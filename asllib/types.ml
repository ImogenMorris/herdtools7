open AST
module IMap = ASTUtils.IMap
module ISet = ASTUtils.ISet

type env = ty IMap.t * identifier IMap.t

let add_pos_from = ASTUtils.add_pos_from

let undefined_identifier pos x =
  Error.fatal_from pos (Error.UndefinedIdentifier x)

let list_equal = ASTUtils.list_equal

let get_structure (env : env) : ty -> ty =
  (* TODO: rethink to have physical equality when structural equality? *)
  (* TODO: memoize? *)
  let rec get ty =
    let () =
      if false then Format.eprintf "@[Getting structure of %a.@]@." PP.pp_ty ty
    in
    let with_pos = add_pos_from ty in
    match ty.desc with
    | T_Named x -> (
        match IMap.find_opt x (fst env) with
        | None -> undefined_identifier ty x
        | Some ty -> get ty)
    | T_Int _ | T_Real | T_String | T_Bool | T_Bits _ | T_Enum _ -> ty
    | T_Tuple subtypes -> T_Tuple (List.map get subtypes) |> with_pos
    | T_Array (e, t) -> T_Array (e, get t) |> with_pos
    | T_Record fields -> T_Record (get_fields fields) |> with_pos
    | T_Exception fields -> T_Exception (get_fields fields) |> with_pos
  and get_fields fields =
    let one_field (name, t) = (name, get t) in
    let fields = List.map one_field fields in
    ASTUtils.canonical_fields fields
  in

  get

(* The builtin singular types are:
   • integer
   • real
   • string
   • boolean
   • bits
   • bit
   • enumeration
*)
let is_builtin_singular ty =
  match ty.desc with
  | T_Real | T_String | T_Bool | T_Bits _ | T_Enum _ | T_Int _ -> true
  | _ -> false

(* The builtin aggregate types are:
   • tuple
   • array
   • record
   • exception
*)
let is_builtin_aggregate ty =
  match ty.desc with
  | T_Tuple _ | T_Array _ | T_Record _ | T_Exception _ -> true
  | _ -> false

let is_builtin ty = is_builtin_singular ty || is_builtin_aggregate ty
let is_named ty = match ty.desc with T_Named _ -> true | _ -> false

(* A named type is singular if it has the structure of a singular type, otherwise it is aggregate. *)
let is_singular env ty =
  is_builtin_singular ty
  || (is_named ty && get_structure env ty |> is_builtin_singular)

(* A named type is singular if it has the structure of a singular type, otherwise it is aggregate. *)
let is_aggregate env ty =
  is_builtin_aggregate ty
  || (is_named ty && get_structure env ty |> is_builtin_aggregate)

let is_anonymous ty = not (is_named ty)

let rec is_non_primitive ty =
  match ty.desc with
  | T_Real | T_String | T_Bool | T_Bits _ | T_Enum _ | T_Int _ -> false
  | T_Named _ -> true
  | T_Tuple li -> List.exists is_non_primitive li
  | T_Array (_, ty) -> is_non_primitive ty
  | T_Record fields | T_Exception fields ->
      List.exists (fun (_, ty) -> is_non_primitive ty) fields

let is_primitive ty = not (is_non_primitive ty)

let eval _env e =
  let v =
    StaticInterpreter.static_eval
      (fun _s ->
        failwith
          "Not yet implemented: environment lookup in static evaluation for \
           typechecking.")
      e
  in
  match v with
  | V_Int i -> i
  | _ ->
      failwith
        "Type error? Cannot use an expression that is not an int in a \
         constraint."

module Domain = struct
  module IntSet = Set.Make (Int)

  (* Pretty inefficient. Use diets instead?
     See https://web.engr.oregonstate.edu/~erwig/papers/Diet_JFP98.pdf
     or https://github.com/mirage/ocaml-diet
  *)
  type int_set = Finite of IntSet.t | Top

  type t =
    | D_Bool
    | D_String
    | D_Real
    | D_Symbols of ISet.t  (** The domain of an enum is a set of symbols *)
    | D_Int of int_set
    | D_Bits of int_set  (** The domain of a bitvector is given by its width. *)

  let rec add_interval_to_intset acc bot top =
    if bot > top then acc
    else add_interval_to_intset (IntSet.add bot acc) (bot + 1) top

  let add_constraint_to_intset env acc = function
    | Constraint_Exact e -> IntSet.add (eval env e) acc
    | Constraint_Range (bot, top) ->
        let bot = eval env bot and top = eval env top in
        add_interval_to_intset acc bot top

  let int_set_of_int_constraints env constraints =
    Finite
      (List.fold_left (add_constraint_to_intset env) IntSet.empty constraints)

  let rec int_set_of_bits_width env = function
    | BitWidth_Determined e -> Finite (IntSet.singleton (eval env e))
    | BitWidth_ConstrainedFormType ty -> (
        match of_type env ty with
        | D_Bits is | D_Int is -> is
        | _ ->
            failwith
              "An bit width cannot be constrained from a type that is neither \
               a bitvector nor an integer.")
    | BitWidth_Constrained constraints ->
        int_set_of_int_constraints env constraints

  and of_type env ty =
    match ty.desc with
    | T_Bool -> D_Bool
    | T_String -> D_String
    | T_Real -> D_Real
    | T_Enum li -> D_Symbols (ISet.of_list li)
    | T_Int None -> D_Int Top
    | T_Int (Some constraints) ->
        D_Int (int_set_of_int_constraints env constraints)
    | T_Bits (width, _) -> D_Bits (int_set_of_bits_width env width)
    | T_Array _ | T_Exception _ | T_Record _ | T_Tuple _ ->
        failwith "Unimplemented: domain of a non singular type."
    | T_Named _ ->
        failwith "Cannot construct a domain of a non-structural type."

  let mem v d =
    match (v, d) with
    | V_Bool _, D_Bool | V_Real _, D_Real -> true
    | V_Bool _, _ | V_Real _, _ | _, D_Bool | _, D_Real -> false
    | V_BitVector _, D_Bits Top -> true
    | V_BitVector bv, D_Bits (Finite intset) ->
        IntSet.mem (Bitvector.length bv) intset
    | V_BitVector _, _ | _, D_Bits _ -> false
    | V_Int _, D_Int Top -> true
    | V_Int i, D_Int (Finite intset) -> IntSet.mem i intset
    | V_Int _, _ | _, D_Int _ -> false
    | V_Tuple _, _ | V_Exception _, _ | V_Record _, _ ->
        failwith "Unimplemented: domain of non-singular type."

  let equal d1 d2 =
    match (d1, d2) with
    | D_Bool, D_Bool | D_String, D_String | D_Real, D_Real -> true
    | D_Symbols s1, D_Symbols s2 -> ISet.equal s1 s2
    | D_Bits Top, D_Bits Top | D_Int Top, D_Int Top -> true
    | D_Int (Finite is1), D_Int (Finite is2)
    | D_Bits (Finite is1), D_Bits (Finite is2) ->
        IntSet.equal is1 is2
    | _ -> false

  let compare _d1 _d2 = assert false

  let is_subset d1 d2 =
    match (d1, d2) with
    | D_Bool, D_Bool | D_String, D_String | D_Real, D_Real -> true
    | D_Symbols s1, D_Symbols s2 -> ISet.subset s1 s2
    | _ -> false
end

let rec subtypes_names env s1 s2 =
  if String.equal s1 s2 then true
  else
    match IMap.find_opt s1 (snd env) with
    | None -> false
    | Some s1' -> subtypes_names env s1' s2

let subtypes env t1 t2 =
  match (t1.desc, t2.desc) with
  | T_Named s1, T_Named s2 -> subtypes_names env s1 s2
  | _ -> false

let rec structural_subtype_satisfies env t s =
  (* A type T subtype-satisfies type S if and only if all of the following conditions hold: *)
  let s_struct = get_structure env s and t_struct = get_structure env t in
  match (s_struct.desc, t_struct.desc) with
  (* If S has the structure of an integer type then T must have the structure
     of an integer type. *)
  | T_Int _, T_Int _ -> true
  | T_Int _, _ -> false
  (* If S has the structure of a real type then T must have the structure of a
     real type. *)
  | T_Real, T_Real -> true
  | T_Real, _ -> false
  (* If S has the structure of a string type then T must have the structure of
     a string type. *)
  | T_String, T_String -> true
  | T_String, _ -> false
  (* If S has the structure of a boolean type then T must have the structure of
     a boolean type. *)
  | T_Bool, T_Bool -> true
  | T_Bool, _ -> false
  (* If S has the structure of an enumeration type then T must have the
     structure of an enumeration type with exactly the same enumeration
     literals. *)
  | T_Enum li_s, T_Enum li_t -> list_equal String.equal li_s li_t
  | T_Enum _, _ -> false
  (*
    • If S has the structure of a bitvector type with determined width then
      either T must have the structure of a bitvector type of the same
      determined width or T must have the structure of a bitvector type with
      undetermined width.
    • If S has the structure of a bitvector type with undetermined width then T
      must have the structure of a bitvector type.
    • If S has the structure of a bitvector type which has bitfields then T
      must have the structure of a bitvector type of the same width and for
      every bitfield in S there must be a bitfield in T of the same name, width
      and offset, whose type type-satisfies the bitfield in S.
  *)
  | T_Bits (w_s, bf_s), T_Bits (w_t, bf_t) -> (
      (match (w_s, w_t) with
      | BitWidth_Determined e_s, BitWidth_Determined e_t ->
          eval env e_s = eval env e_t
      | BitWidth_Determined _, _ -> false
      | BitWidth_Constrained _, _ -> true
      | _ -> true)
      &&
      match (bf_s, bf_t) with
      | Some bfs_s, Some bfs_t ->
          w_s = w_t
          &&
          let bf_equal (name_s, slices_s) (name_t, slices_t) =
            String.equal name_s name_t
            && ASTUtils.slices_equal slices_s slices_t
          in
          let mem_bf bfs_t bf_s = List.exists (bf_equal bf_s) bfs_t in
          List.for_all (mem_bf bfs_t) bfs_s
      | Some _, None -> false
      | None, _ -> true)
  | T_Bits _, _ -> false
  (* If S has the structure of an array type with elements of type E then T
     must have the structure of an array type with elements of type E, and T
     must have the same element indices as S.
     TODO: this is probably wrong, or a bad approximation. *)
  | T_Array (length_s, ty_s), T_Array (length_t, ty_t) ->
      ASTUtils.(expr_equal length_s length_t && type_equal ty_s ty_t)
  | T_Array _, _ -> false
  (* If S has the structure of a tuple type then T must have the structure of
     a tuple type with same number of elements as S, and each element in T
     must type-satisfy the corresponding element in S.*)
  | T_Tuple li_s, T_Tuple li_t ->
      List.compare_lengths li_s li_t = 0
      && List.for_all2 (type_satisfies env) li_t li_s
  | T_Tuple _, _ -> false
  (* If S has the structure of an exception type then T must have the structure
     of an exception type with at least the same fields (each with the same
     type) as S.
     If S has the structure of a record type then T must have the structure of
     a record type with at least the same fields (each with the same type) as
     S.
     TODO: order of fields? *)
  | T_Exception fields_s, T_Exception fields_t
  | T_Record fields_s, T_Record fields_t ->
      List.compare_lengths fields_s fields_t = 0
      && List.for_all2 ( = ) fields_s fields_t
  | T_Exception _, _ | T_Record _, _ -> false (* A structure cannot be a name *)
  | T_Named _, _ -> assert false

and domain_subtype_satisfies env t s =
  let s_struct = get_structure env s in
  match s_struct.desc with
  | T_Named _ ->
      (* Cannot happen *)
      assert false
      (* If S does not have the structure of an aggregate type or bitvector type
         then the domain of T must be a subset of the domain of S. *)
  | T_Tuple _ | T_Array _ | T_Record _ | T_Exception _ -> true
  | T_Real | T_String | T_Bool | T_Enum _ | T_Int _ ->
      Domain.(is_subset (of_type env (get_structure env t)) (of_type env s))
  | T_Bits _ ->
      (* If either S or T have the structure of a bitvector type with
         undetermined width then the domain of T must be a subset of the domain
         of S. *)
      (* TODO *)
      assert false

and subtype_satisfies env t s =
  structural_subtype_satisfies env t s && domain_subtype_satisfies env t s

and type_satisfies env t s =
  (* Type T type-satisfies type S if and only if at least one of the following conditions holds: *)
  (* T is a subtype of S *)
  subtypes env t s
  (* T subtype-satisfies S and at least one of S or T is an anonymous type *)
  || ((is_anonymous t || is_anonymous s) && subtype_satisfies env t s)
  ||
  (* T is an anonymous bitvector with no bitfields and S has the structure of a
     bitvector (with or without bitfields) of the same width as T. *)
  match (t.desc, (get_structure env s).desc) with
  | T_Bits (width_t, None), T_Bits (width_s, _) -> width_t = width_s
  | _ -> true

let rec type_clashes env t s =
  (*
   Definition VPZZ:
   A type T type-clashes with S if any of the following hold:
      • they both have the structure of integers
      • they both have the structure of reals
      • they both have the structure of strings
      • they both have the structure of enumeration types with the same enumeration literals
      • they both have the structure of bit vectors
      • they both have the structure of arrays whose element types type-clash
      • they both have the structure of tuples of the same length whose corresponding element types type-clash
      • S is either a subtype or a supertype of T *)
  (subtypes env s t || subtypes env t s)
  ||
  let s_struct = get_structure env s and t_struct = get_structure env t in
  match (s_struct.desc, t_struct.desc) with
  | T_Int _, T_Int _ | T_Real, T_Real | T_String, T_String | T_Bits _, T_Bits _
    ->
      true
  | T_Enum li_s, T_Enum li_t -> list_equal String.equal li_s li_t
  | T_Array (_, ty_s), T_Array (_, ty_t) -> type_clashes env ty_s ty_t
  | T_Tuple li_s, T_Tuple li_t ->
      List.compare_lengths li_s li_t = 0
      && List.for_all2 (type_clashes env) li_s li_t
  | _ -> false

let subprogram_clashes env f1 f2 =
  (* Two subprograms clash if all of the following hold:
      • they have the same name
      • they are the same kind of subprogram
      • they have the same number of formal arguments
      • every formal argument in one type-clashes with the corresponding formal argument in the other

     TODO: they are the same kind of subprogram
  *)
  String.equal f1.name f2.name
  && List.compare_lengths f1.args f2.args = 0
  && List.for_all2
       (fun (_, t1) (_, t2) -> type_clashes env t1 t2)
       f1.args f2.args
