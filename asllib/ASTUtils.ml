open AST
module ISet = Set.Make (String)

module IMap : sig
  include Map.S with type key = identifier

  val of_list : (key * 'a) list -> 'a t
end = struct
  include Map.Make (String)

  let of_list li =
    List.fold_left (fun acc (key, value) -> add key value acc) empty li
end

let dummy_pos = Lexing.dummy_pos
let annotated desc pos_start pos_end = { desc; pos_start; pos_end }
let add_dummy_pos desc = annotated desc dummy_pos dummy_pos
let dummy_annotated = add_dummy_pos ()
let to_pos pos = { pos with desc = () }

let add_pos_from_st pos desc =
  if pos.desc == desc then pos else { pos with desc }

let with_pos_from_st pos { desc; _ } = add_pos_from_st pos desc
let map_desc_st f thing = f thing |> add_pos_from_st thing
let add_pos_from pos desc = { pos with desc }
let with_pos_from pos { desc; _ } = add_pos_from pos desc
let map_desc f thing = f thing |> add_pos_from thing

let list_equal equal li1 li2 =
  li1 == li2 || (List.compare_lengths li1 li2 = 0 && List.for_all2 equal li1 li2)

let pair_equal f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

let map2_desc f thing1 thing2 =
  {
    desc = f thing1 thing2;
    pos_start = thing1.pos_start;
    pos_end = thing2.pos_end;
  }

let s_pass = add_dummy_pos S_Pass
let s_then = map2_desc (fun s1 s2 -> S_Then (s1, s2))

let stmt_from_list : stmt list -> stmt =
  let is_not_s_pass = function { desc = S_Pass; _ } -> false | _ -> true in
  let rec one_step acc = function
    | [] -> List.rev acc
    | [ x ] -> List.rev (x :: acc)
    | s1 :: s2 :: t -> one_step (s_then s1 s2 :: acc) t
  in
  let rec aux = function
    | [] -> add_dummy_pos S_Pass
    | [ x ] -> x
    | l -> aux @@ one_step [] l
  in
  fun l -> List.filter is_not_s_pass l |> aux

let mask_from_set_bits_positions size pos =
  let buf = Bytes.make size '0' in
  let set i = Bytes.set buf i '1' in
  let () = List.iter set pos in
  Bytes.to_string buf

let inv_mask =
  let one_char = function '0' -> '1' | '1' -> '0' | c -> c in
  String.map one_char

let slices_to_positions as_int =
  let one_slice (start, length) =
    let start = as_int start and length = as_int length in
    (* Reversed interval *)
    List.init length (( - ) (start + length - 1))
  in
  fun positions -> List.map one_slice positions |> List.flatten

let used_identifiers, used_identifiers_stmt =
  let rec use_e acc e =
    match e.desc with
    | E_Literal _ -> acc
    | E_Typed (e, _) -> use_e acc e
    | E_Var x -> ISet.add x acc
    | E_Binop (_op, e1, e2) -> use_e (use_e acc e2) e1
    | E_Unop (_op, e) -> use_e acc e
    | E_Call (x, args, named_args) ->
        let acc = ISet.add x acc in
        let acc = List.fold_left use_field acc named_args in
        List.fold_left use_e acc args
    | E_Slice (e, args) ->
        let acc = use_e acc e in
        List.fold_left use_slice acc args
    | E_Cond (e1, e2, e3) -> use_e (use_e (use_e acc e1) e3) e2
    | E_GetField (e, _, _ta) -> use_e acc e
    | E_GetFields (e, _, _ta) -> use_e acc e
    | E_Record (_ty, li, _ta) -> List.fold_left use_field acc li
    | E_Concat es -> List.fold_left use_e acc es
    | E_Tuple es -> List.fold_left use_e acc es
    | E_Unknown _ -> acc
    | E_Pattern (e, _p) -> use_e acc e
  and use_field acc (_, e) = use_e acc e
  and use_slice acc = function
    | Slice_Single e -> use_e acc e
    | Slice_Length (e1, e2) | Slice_Range (e1, e2) -> use_e (use_e acc e1) e2
  and use_s acc s =
    match s.desc with
    | S_Pass | S_Return None -> acc
    | S_Then (s1, s2) -> use_s (use_s acc s1) s2
    | S_Assert e | S_Return (Some e) -> use_e acc e
    | S_Assign (le, e) -> use_le (use_e acc e) le
    | S_Call (x, args, named_args) ->
        let acc = ISet.add x acc in
        let acc = List.fold_left use_field acc named_args in
        List.fold_left use_e acc args
    | S_Cond (e, s1, s2) -> use_s (use_s (use_e acc e) s2) s1
    | S_Case (e, cases) -> List.fold_left use_case (use_e acc e) cases
    | S_TypeDecl _ -> acc
  and use_case acc { desc = _p, stmt; _ } = use_s acc stmt
  and use_le acc _le = acc
  and use_decl acc = function
    | D_Func { body; _ } -> use_s acc body
    | D_GlobalConst (_name, _ty, e) -> use_e acc e
    | _ -> acc
  in
  (List.fold_left use_decl ISet.empty, use_s ISet.empty)

let canonical_fields li =
  let compare (x, _) (y, _) = String.compare x y in
  List.sort compare li

let rec value_equal v1 v2 =
  match (v1, v2) with
  | V_Bool b1, V_Bool b2 -> b1 = b2
  | V_Int i1, V_Int i2 -> i1 = i2
  | V_Real f1, V_Real f2 -> f1 = f2
  | V_BitVector bv1, V_BitVector bv2 -> Bitvector.equal bv1 bv2
  | V_Exception fs1, V_Exception fs2 | V_Record fs1, V_Record fs2 ->
      List.compare_lengths fs1 fs2 = 0
      &&
      let fs1 = canonical_fields fs1 and fs2 = canonical_fields fs2 in
      let field_equal (x1, v1) (x2, v2) =
        String.equal x1 x2 && value_equal v1 v2
      in
      List.for_all2 field_equal fs1 fs2
  | V_Tuple vs1, V_Tuple vs2 ->
      List.compare_lengths vs1 vs2 = 0 && List.for_all2 value_equal vs1 vs2
  | _ -> false

let rec expr_equal e1 e2 =
  e1 == e2
  ||
  match (e1.desc, e2.desc) with
  | E_Binop (o1, e11, e21), E_Binop (o2, e12, e22) ->
      o1 = o2 && expr_equal e11 e12 && expr_equal e21 e22
  | E_Binop _, _ | _, E_Binop _ -> false
  | E_Call (x1, args1, _), E_Call (x2, args2, _) ->
      String.equal x1 x2 && list_equal expr_equal args1 args2
  | E_Call _, _ | _, E_Call _ -> false
  | E_Concat li1, E_Concat li2 -> list_equal expr_equal li1 li2
  | E_Concat _, _ | _, E_Concat _ -> false
  | E_Cond (e11, e21, e31), E_Cond (e12, e22, e32) ->
      expr_equal e11 e12 && expr_equal e21 e22 && expr_equal e31 e32
  | E_Cond _, _ | _, E_Cond _ -> false
  | E_Slice (e1, slices1), E_Slice (e2, slices2) ->
      expr_equal e1 e2 && slices_equal slices1 slices2
  | E_Slice _, _ | _, E_Slice _ -> false
  | E_GetField _, _ | E_GetFields _, _ | E_Pattern _, _ | E_Record _, _ ->
      assert false
  | E_Literal v1, E_Literal v2 -> value_equal v1 v2
  | E_Literal _, _ | _, E_Literal _ -> false
  | E_Tuple li1, E_Tuple li2 -> list_equal expr_equal li1 li2
  | E_Tuple _, _ | _, E_Tuple _ -> false
  | E_Typed (e1, t1), E_Typed (e2, t2) -> expr_equal e1 e2 && type_equal t1 t2
  | E_Typed _, _ | _, E_Typed _ -> false
  | E_Unop (o1, e1), E_Unop (o2, e2) -> o1 = o2 && expr_equal e1 e2
  | E_Unop _, _ | _, E_Unop _ -> false
  | E_Unknown _, _ | _, E_Unknown _ -> false
  | E_Var s1, E_Var s2 -> String.equal s1 s2
  | E_Var _, _ (* | _, E_Var _ *) -> false

and slices_equal slices1 slices2 = list_equal slice_equal slices1 slices2

and slice_equal slice1 slice2 =
  slice1 == slice2
  ||
  match (slice1, slice2) with
  | Slice_Single e1, Slice_Single e2 -> expr_equal e1 e2
  | Slice_Range (e11, e21), Slice_Range (e12, e22)
  | Slice_Length (e11, e21), Slice_Length (e12, e22) ->
      expr_equal e11 e12 && expr_equal e21 e22
  | _ -> false

and constraint_equal c1 c2 =
  c1 == c2
  ||
  match (c1, c2) with
  | Constraint_Exact e1, Constraint_Exact e2 -> expr_equal e1 e2
  | Constraint_Range (e11, e21), Constraint_Range (e12, e22) ->
      expr_equal e11 e12 && expr_equal e21 e22
  | _ -> false

and constraints_equal cs1 cs2 =
  cs1 == cs2 || list_equal constraint_equal cs1 cs2

and type_equal t1 t2 =
  t1.desc == t2.desc
  ||
  match (t1.desc, t2.desc) with
  | T_Bool, T_Bool
  | T_Real, T_Real
  | T_String, T_String
  | T_Int None, T_Int None ->
      true
  | T_Int (Some c1), T_Int (Some c2) -> constraints_equal c1 c2
  | T_Bits (w1, bf1), T_Bits (w2, bf2) ->
      bitwidth_equal w1 w2 && bitfields_equal bf1 bf2
  | T_Array (l1, t1), T_Array (l2, t2) -> expr_equal l1 l2 && type_equal t1 t2
  | T_Named s1, T_Named s2 -> String.equal s1 s2
  | T_Enum li1, T_Enum li2 ->
      (* TODO: order of fields? *) list_equal String.equal li1 li2
  | T_Exception f1, T_Exception f2 | T_Record f1, T_Record f2 ->
      list_equal
        (pair_equal String.equal type_equal)
        (canonical_fields f1) (canonical_fields f2)
  | T_Tuple ts1, T_Tuple ts2 -> list_equal type_equal ts1 ts2
  | _ -> false

and bitwidth_equal w1 w2 =
  w1 == w2
  ||
  match (w1, w2) with
  | BitWidth_Constrained c1, BitWidth_Constrained c2 -> constraints_equal c1 c2
  | BitWidth_ConstrainedFormType t1, BitWidth_ConstrainedFormType t2 ->
      type_equal t1 t2
  | BitWidth_Determined e1, BitWidth_Determined e2 -> expr_equal e1 e2
  | _ -> false

and bitfields_equal bf1 bf2 =
  bf1 == bf2
  || Option.equal (list_equal (pair_equal String.equal slices_equal)) bf1 bf2

let literal v = E_Literal v |> add_dummy_pos
let var_ x = E_Var x |> add_dummy_pos
let binop op = map2_desc (fun e1 e2 -> E_Binop (op, e1, e2))

let expr_of_lexpr : lexpr -> expr =
  let rec aux le =
    match le.desc with
    | LE_Var x -> E_Var x
    | LE_Typed (le, t) -> E_Typed (map_desc aux le, t)
    | LE_Slice (le, args) -> E_Slice (map_desc aux le, args)
    | LE_SetField (le, x, ta) -> E_GetField (map_desc aux le, x, ta)
    | LE_SetFields (le, x, ta) -> E_GetFields (map_desc aux le, x, ta)
    | LE_Ignore -> E_Var "-"
    | LE_TupleUnpack les -> E_Tuple (List.map (map_desc aux) les)
  in
  map_desc aux

let fresh_var =
  let i = ref 0 in
  fun s ->
    let () = incr i in
    s ^ "-" ^ string_of_int !i

let rec big_union = function
  | [] -> literal (V_Bool true)
  | [ e ] -> e
  | h :: t -> binop BOR h (big_union t)

let case_to_conds : stmt -> stmt =
  let rec cases_to_cond x = function
    | [] -> s_pass
    | case :: t -> map_desc (one_case x t) case
  and one_case x t case =
    let p, s = case.desc in
    S_Cond (E_Pattern (var_ x, p) |> add_pos_from case, s, cases_to_cond x t)
  in
  map_desc @@ fun s ->
  match s.desc with
  | S_Case ({ desc = E_Var y; _ }, cases) -> (cases_to_cond y cases).desc
  | S_Case (e, cases) ->
      let x = fresh_var "case" in
      let assign =
        let pos = e.pos_start in
        let le = annotated (LE_Var x) pos pos in
        annotated (S_Assign (le, e)) pos e.pos_end
      in
      S_Then (assign, cases_to_cond x cases)
  | _ -> raise (Invalid_argument "case_to_conds")

let slice_as_single = function
  | Slice_Single e -> e
  | _ -> raise @@ Invalid_argument "slice_as_single"

let getter_prefix = "getter-"
let setter_prefix = "setter-"
let setter_name = ( ^ ) setter_prefix
let getter_name = ( ^ ) getter_prefix

let num_args = function
  | 0 -> Fun.id
  | n -> fun name -> name ^ "-" ^ string_of_int n

let default_t_bits = T_Bits (BitWidth_Constrained [], None)

let patch ~src ~patches =
  (* Size considerations:
     - [src] is BIG.
     - [patches] is not that little. *)
  let identifier_of_decl = function
    | D_Func { name; _ }
    | D_GlobalConst (name, _, _)
    | D_TypeDecl (name, _)
    | D_Primitive { name; _ } ->
        name
  in
  let to_remove =
    patches |> List.to_seq |> Seq.map identifier_of_decl |> ISet.of_seq
  in
  let filter d = not (ISet.mem (identifier_of_decl d) to_remove) in
  src |> List.filter filter |> List.rev_append patches
