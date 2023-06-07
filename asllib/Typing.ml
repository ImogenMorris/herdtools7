open AST
open ASTUtils

let fatal_from = Error.fatal_from
let not_yet_implemented pos s = fatal_from pos (Error.NotYetImplemented s)
let undefined_identifier pos x = fatal_from pos (Error.UndefinedIdentifier x)
let bad_field pos x ty = fatal_from pos (Error.BadField (x, ty))

let conflict pos expected provided =
  fatal_from pos (Error.ConflictingTypes (expected, provided))

(* Control Warning outputs. *)
let _warn = false

type strictness = [ `Silence | `Warn | `TypeCheck ]

(******************************************************************************)
(*                                                                            *)
(*                               Environments                                 *)
(*                                                                            *)
(******************************************************************************)

type genv = ty IMap.t
(** Type environment for all globally declared identifiers.
    Note that this is shared between named_types and global variables, but not
    functions, getter, setters, and all subprograms.
    In asl-semantics, it is refered to as Γ.T : TypeModel.
*)

type func_sig = (identifier * ty) list * ty option
(** Type signature for functions, some kind of an arrow type. *)

type func_tr = ((identifier * ty) list * AST.identifier) list IMap.t
(** function renaming to get unique identifiers. *)

type tenv = { globals : genv; funcs : func_sig IMap.t; func_tr : func_tr }
(** The global type environment, with types for every globally available
    identifier, i.e. variables, named types or functions .*)

type lenv = ty IMap.t
(** The local type environment, with types for all locally declared variables. *)

let lookup_opt (tenv : tenv) (lenv : lenv) x =
  let open IMap in
  match find_opt x lenv with
  | Some ty -> Some ty
  | None -> (
      match find_opt x tenv.globals with
      | Some ty -> Some ty
      | None -> (
          match find_opt x tenv.funcs with
          | Some ([], Some ty) -> Some ty
          | _ -> None))

let lookup tenv lenv pos x =
  let () = if false then Format.eprintf "@[Looking up var %S.@]@." x in
  match lookup_opt tenv lenv x with
  | Some ty -> ty
  | None -> undefined_identifier pos x

let lookup_return_type (tenv : tenv) pos x =
  let () = if false then Format.eprintf "@[Finding return type of %S@]@." x in
  match IMap.find_opt x tenv.funcs with
  | Some (_, Some ty) -> ty
  | Some (_, None) -> fatal_from pos @@ Error.MismatchedReturnValue x
  | None -> undefined_identifier pos x

let get_structure genv ty = Types.get_structure (genv, IMap.empty) ty

(* --------------------------------------------------------------------------

                              Subtyping

   --------------------------------------------------------------------------*)

(** [subtypes tenv t1 t2] is the set of equations that must be validated for
    [t1] to be a subtype of [t2].

    For example, [integer {3}] is always a subtype of [integer], and thus
    [subtypes] would return [Some []].

    However, for [integer {3}] to be a subset of [integer {N}], [N] needs to be
    equal to [3].
*)
let rec subtypes tenv t1 t2 =
  match (t1.desc, t2.desc) with
  | T_Bits (BitWidth_Determined e1, _), T_Bits (BitWidth_Determined e2, _) ->
      Some [ (e1, e2) ]
  | T_Int _, T_Int None -> Some []
  | T_Int (Some _), T_Int (Some _) ->
      Some [] (* TODO should we add equations here? *)
  | T_Real, T_Real | T_String, T_String | T_Bool, T_Bool -> Some []
  | T_Tuple li1, T_Tuple li2 when List.compare_lengths li1 li2 = 0 ->
      let rec on_tuples acc li1 li2 =
        match (li1, li2) with
        | [], [] -> Some acc
        | st1 :: h1, st2 :: h2 -> (
            match subtypes tenv st1 st2 with
            | None -> None
            | Some eqs -> on_tuples (List.rev_append eqs acc) h1 h2)
        | _ -> assert false
      in
      on_tuples [] li1 li2
  | T_Array (e1, st1), T_Array (e2, st2) -> (
      match subtypes tenv st1 st2 with
      | None -> None
      | Some eqs -> Some ((e1, e2) :: eqs))
  | T_Record li1, T_Record li2 when List.compare_lengths li1 li2 = 0 ->
      let rec on_fields acc li1 li2 =
        match (li1, li2) with
        | [], [] -> Some acc
        | (x1, _) :: _, (x2, _) :: _ when String.compare x1 x2 != 0 -> None
        | (_, st1) :: h1, (_, st2) :: h2 -> (
            match subtypes tenv st1 st2 with
            | None -> None
            | Some eqs -> on_fields (List.rev_append eqs acc) h1 h2)
        | _ -> assert false
      in
      on_fields [] (canonical_fields li1) (canonical_fields li2)
  | T_Named x, T_Named y when String.compare x y = 0 -> Some []
  | T_Named _, _ | _, T_Named _ ->
      subtypes tenv
        (get_structure tenv.globals t1)
        (get_structure tenv.globals t2)
  | T_Enum l1, T_Enum l2 when List.compare_lengths l1 l2 = 0 ->
      if List.for_all2 String.equal l1 l2 then Some [] else None
  | _ -> None

let subtypes =
  if true then subtypes
  else fun tenv t1 t2 ->
    let res = subtypes tenv t1 t2 in
    let () =
      if false then
        Format.eprintf "Subtypes %a :< %a : %B.@," PP.pp_ty t1 PP.pp_ty t2
          (Option.is_some res)
    in
    res

let eqs_as_exprs =
  let one (e1, e2) =
    match e2.desc with
    | E_Var x -> Some (x, e1)
    | _ ->
        if false && e1.desc <> e2.desc then
          Format.eprintf "@[Unsupported type equation:@ %a@ == %a.@]@."
            PP.pp_expr e1 PP.pp_expr e2;
        None
  in
  List.filter_map one

(* -------------------------------------------------------------------------

                        Functionnal polymorphism

   ------------------------------------------------------------------------- *)

module FunctionRenaming = struct
  let has_arg_clash tenv caller callee =
    if List.compare_lengths caller callee != 0 then None
    else
      let rec on_each acc caller callee =
        match (caller, callee) with
        | [], [] -> Some acc
        | t1 :: caller, (_, t2) :: callee -> (
            match subtypes tenv t1 t2 with
            | None -> None
            | Some eqs -> on_each (List.rev_append eqs acc) caller callee)
        | _ -> None
      in
      on_each [] caller callee

  let add_new_func tr_table name arg_types =
    match IMap.find_opt name !tr_table with
    | None ->
        tr_table := IMap.add name [ (arg_types, name) ] !tr_table;
        name
    | Some assoc_list ->
        let name' = name ^ "-" ^ string_of_int (List.length assoc_list) in
        tr_table := IMap.add name ((arg_types, name') :: assoc_list) !tr_table;
        name'

  let find_name_strict loc tenv name caller_arg_types =
    let () =
      if false then Format.eprintf "Trying to rename call to %S@." name
    in
    match IMap.find_opt name tenv.func_tr with
    | None -> undefined_identifier loc name
    | Some assoc_list -> (
        let finder (callee_arg_types, name') =
          match has_arg_clash tenv caller_arg_types callee_arg_types with
          | None -> None
          | Some eqs -> Some (eqs, name', callee_arg_types)
        in
        match List.filter_map finder assoc_list with
        | [] -> fatal_from loc (Error.NoCallCandidate (name, caller_arg_types))
        | [ (eqs, name', callee_arg_types) ] ->
            (eqs_as_exprs eqs, name', callee_arg_types)
        | _ :: _ ->
            fatal_from loc
              (Error.TooManyCallCandidates (name, caller_arg_types)))

  let find_name tenv name caller_arg_types =
    match IMap.find_opt name tenv.func_tr with
    | None ->
        let () =
          if _warn then Format.eprintf "No found function named %s.@." name
        in
        ([], name)
        (* Will trigger runtime exception *)
    | Some assoc_list -> (
        let finder (callee_arg_types, name') =
          match has_arg_clash tenv caller_arg_types callee_arg_types with
          | None -> None
          | Some eqs -> Some (eqs, name')
        in
        match List.filter_map finder assoc_list with
        | [] ->
            let () =
              if _warn then
                Format.eprintf "No found function %s with the right types.@."
                  name
            in
            ([], name)
            (* Will trigger runtime exception *)
        | [ (eqs, name') ] -> (eqs_as_exprs eqs, name')
        | (_, name') :: _ as li ->
            let () =
              if _warn then
                Format.eprintf
                  "Ambiguous call to %s. Many conflicting declared functions.@."
                  name
            in
            (* We select all possible equations, hoping that there are no
               conflicting ones. Args keep precendence over type-equations, so
               there should not be any conflicts with those. *)
            let eqs = li |> List.map fst |> List.concat in
            (eqs_as_exprs eqs, name')
        (* If ambiguous, I don't know what happens *))

  let new_tr_table () = ref IMap.empty
  let to_tr_table tr_table_ref = IMap.map List.rev !tr_table_ref
end

(******************************************************************************)
(*                                                                            *)
(*                         Type manipulation helpers                          *)
(*                                                                            *)
(******************************************************************************)

let expr_of_int i = literal (V_Int i)
let plus = binop PLUS
let t_bits_bitwidth e = T_Bits (BitWidth_Determined e, [])

let reduce_constants =
  (* TODO static reduction. *)
  let exception TrivialReductionFailed in
  let lookup _s = raise_notrace TrivialReductionFailed in
  fun e ->
    try
      let v = StaticInterpreter.static_eval lookup e in
      E_Literal v |> add_pos_from_st e
    with TrivialReductionFailed -> e

let sum = function
  | [] -> expr_of_int 0
  | [ x ] -> x
  | h :: t -> List.fold_left plus h t

let slices_length =
  let minus = binop MINUS in
  let one = expr_of_int 1 in
  let slice_length = function
    | Slice_Single _ -> one
    | Slice_Length (_, e) -> e
    | Slice_Range (e1, e2) -> plus one (minus e1 e2)
  in
  fun li -> List.map slice_length li |> sum |> reduce_constants

let width_plus acc w =
  match (acc, w) with
  | BitWidth_Determined e1, BitWidth_Determined e2 ->
      BitWidth_Determined (plus e1 e2 |> reduce_constants)
  | BitWidth_Constrained cs1, BitWidth_Determined e2 ->
      BitWidth_Constrained (constraint_binop PLUS cs1 [ Constraint_Exact e2 ])
  | BitWidth_Determined e1, BitWidth_Constrained cs2 ->
      BitWidth_Constrained (constraint_binop PLUS [ Constraint_Exact e1 ] cs2)
  | BitWidth_Constrained cs1, BitWidth_Constrained cs2 ->
      BitWidth_Constrained (constraint_binop PLUS cs1 cs2)
  | _ ->
      failwith "Not yet implemented: concatening slices constrained from type."

let field_type pos x ty =
  match ty.desc with
  | T_Record li -> (
      match List.assoc_opt x li with
      | Some ty -> ty
      | None -> bad_field pos x ty)
  | T_Bits (_, fields) -> (
      match List.assoc_opt x fields with
      | Some slices ->
          slices_length slices |> t_bits_bitwidth |> add_pos_from_st ty
      | None -> bad_field pos x ty)
  | _ -> bad_field pos x ty

let fields_type pos xs ty =
  let field_length =
    match ty.desc with
    | T_Bits (_, fields) -> (
        fun x ->
          match List.assoc_opt x fields with
          | None -> bad_field pos x ty
          | Some slices -> slices_length slices)
    | _ -> conflict pos [ default_t_bits ] ty
  in
  List.map field_length xs |> sum |> t_bits_bitwidth |> add_pos_from_st ty

let rename_ty_eqs (eqs : (AST.identifier * AST.expr) list) ty =
  let mapping = IMap.of_list eqs in
  match ty.desc with
  | T_Bits (BitWidth_Determined ({ desc = E_Var callee_var; _ } as e), fields)
    when IMap.mem callee_var mapping ->
      let new_e = IMap.find callee_var mapping |> with_pos_from e in
      T_Bits (BitWidth_Determined new_e, fields) |> add_pos_from_st ty
  | _ -> ty

(******************************************************************************)
(*                                                                            *)
(*                   Inference and type-checking helpers                      *)
(*                                                                            *)
(******************************************************************************)

let infer_value = function
  | V_Int i -> T_Int (Some [ Constraint_Exact (expr_of_int i) ])
  | V_Bool _ -> T_Bool
  | V_Real _ -> T_Real
  | V_BitVector bv -> Bitvector.length bv |> expr_of_int |> t_bits_bitwidth
  | _ -> not_yet_implemented dummy_annotated "static complex values"

let rec infer_lexpr tenv lenv le =
  match le.desc with
  | LE_Var x -> lookup tenv lenv le x
  | LE_Slice ({ desc = LE_Var x; _ }, _) when IMap.mem x tenv.funcs ->
      lookup_return_type tenv le x
  | LE_Slice (le', slices) -> (
      let ty = infer_lexpr tenv lenv le' in
      match ty.desc with
      | T_Bits _ -> slices_length slices |> t_bits_bitwidth |> add_dummy_pos
      | _ -> conflict le [ default_t_bits ] ty)
  | LE_SetField (_, field, TA_InferredStructure ty) -> field_type le field ty
  | LE_SetFields (_, fields, TA_InferredStructure ty) ->
      fields_type le fields ty
  | LE_SetField (le, fields, TA_None) ->
      infer_lexpr tenv lenv le |> field_type le fields
  | LE_SetFields (le, fields, TA_None) ->
      infer_lexpr tenv lenv le |> fields_type le fields
  | LE_Ignore -> not_yet_implemented le "Type inference of '-'"
  | LE_TupleUnpack les ->
      T_Tuple (List.map (infer_lexpr tenv lenv) les) |> add_dummy_pos

(* -------------------------------------------------------------------------

                          Getter/Setter handling

   -------------------------------------------------------------------------- *)

let should_reduce_to_call tenv name args =
  match IMap.find_opt name tenv.funcs with
  | None -> None
  | Some (_arg_types, return_type) -> Some (name, args, return_type)

let should_slices_reduce_to_call tenv name slices =
  let args =
    try Some (List.map slice_as_single slices) with Invalid_argument _ -> None
  in
  match args with
  | None -> None
  | Some args -> should_reduce_to_call tenv name args

let getter_should_reduce_to_call tenv x slices =
  let name = getter_name x in
  match should_slices_reduce_to_call tenv name slices with
  | Some (name, args, Some _) ->
      let () =
        if false then Format.eprintf "Reducing call from %s to %s.@." x name
      in
      Some (name, args)
  | Some (_, _, None) | None -> None

let rec setter_should_reduce_to_call_s tenv le e : stmt option =
  let here d = add_pos_from le d in
  let s_then = s_then in
  let to_expr = expr_of_lexpr in
  let with_temp old_le sub_le =
    let x = fresh_var "setter_setfield" in
    let le_x = LE_Var x |> here in
    match setter_should_reduce_to_call_s tenv sub_le (E_Var x |> here) with
    | None -> None
    | Some s ->
        Some
          (s_then
             (s_then
                (S_Assign (le_x, to_expr sub_le) |> here)
                (S_Assign (old_le le_x, e) |> here))
             s)
  in
  match le.desc with
  | LE_Ignore -> None
  | LE_SetField (sub_le, field, ta) ->
      let old_le le' = LE_SetField (le', field, ta) |> here in
      with_temp old_le sub_le
  | LE_SetFields (sub_le, fields, ta) ->
      let old_le le' = LE_SetFields (le', fields, ta) |> here in
      with_temp old_le sub_le
  | LE_Slice ({ desc = LE_Var x; _ }, slices) -> (
      let name = setter_name x and slices = Slice_Single e :: slices in
      match should_slices_reduce_to_call tenv name slices with
      | None -> None
      | Some (name, args, _) -> Some (S_Call (name, args, []) |> here))
  | LE_Slice (sub_le, slices) ->
      let old_le le' = LE_Slice (le', slices) |> here in
      with_temp old_le sub_le
  | LE_TupleUnpack _ -> None
  | LE_Var x -> (
      match should_reduce_to_call tenv (setter_name x) [ e ] with
      | Some (name, args, _) -> Some (S_Call (name, args, []) |> here)
      | None -> None)

(******************************************************************************)
(*                                                                            *)
(*                               Annotate AST                                 *)
(*                                                                            *)
(******************************************************************************)

module type ANNOTATE_CONFIG = sig
  val check : strictness
end

module Annotate (C : ANNOTATE_CONFIG) = struct
  exception TypingAssumptionFailed

  let _warn =
    match C.check with `Warn | `TypeCheck -> true | `Silence -> false

  let check =
    match C.check with
    | `TypeCheck -> fun f x -> f x
    | `Warn -> (
        fun f x ->
          try f x
          with Error.ASLException e ->
            Error.eprintln e;
            x)
    | `Silence -> fun _f x -> x

  let best_effort =
    match C.check with
    | `TypeCheck -> fun x f -> f x
    | `Warn -> (
        fun x f ->
          try f x
          with Error.ASLException e ->
            Error.eprintln e;
            x)
    | `Silence -> ( fun x f -> try f x with Error.ASLException _ -> x)

  let[@inline] ( let+ ) m f = check m () |> f

  let[@inline] both f1 f2 x =
    let _ = f1 x in
    f2 x

  let either f1 f2 x =
    try f1 x with TypingAssumptionFailed | Error.ASLException _ -> f2 x

  let rec any li x =
    match li with
    | [] -> raise (Invalid_argument "any")
    | [ f ] -> f x
    | f :: li -> either f (any li) x

  let assumption_failed () = raise_notrace TypingAssumptionFailed [@@inline]
  let check_true b fail () = if b then () else fail () [@@inline]
  let check_true' b = check_true b assumption_failed [@@inline]

  let eval' _tenv =
    let lookup _s = assumption_failed () in
    StaticInterpreter.static_eval lookup

  let check_type_satisfies' tenv t1 t2 () =
    if Types.type_satisfies (tenv.globals, IMap.empty) t1 t2 then ()
    else raise_notrace TypingAssumptionFailed

  let get_bitvector_width' tenv t =
    match (get_structure tenv.globals t).desc with
    | T_Bits (n, _) -> n
    | _ -> assumption_failed ()

  let get_bitvector_width loc tenv t =
    try get_bitvector_width' tenv t
    with TypingAssumptionFailed -> conflict loc [ default_t_bits ] t

  let get_record_fields loc tenv t =
    match (get_structure tenv.globals t).desc with
    | T_Record fields -> fields
    | _ -> conflict loc [ T_Record [] ] t

  (** [check_type_satisfies t1 t2] if [t1 <: t2]. *)
  let check_type_satisfies loc tenv t1 t2 () =
    if Types.type_satisfies (tenv.globals, IMap.empty) t1 t2 then ()
    else conflict loc [ t2.desc ] t1

  (** [check_structure_boolean env t1] checks that [t1] has the structure of a boolean. *)
  let check_structure_boolean loc tenv t1 () =
    match (get_structure tenv.globals t1).desc with
    | T_Bool -> ()
    | _ -> conflict loc [ T_Bool ] t1

  let check_structure_bits loc tenv t () =
    match (get_structure tenv.globals t).desc with
    | T_Bits _ -> ()
    | _ -> conflict loc [ default_t_bits ] t

  let check_structure_integer loc tenv t () =
    match (get_structure tenv.globals t).desc with
    | T_Int _ -> ()
    | _ -> conflict loc [ T_Int None ] t

  let check_bv_have_same_determined_bitwidth' tenv t1 t2 () =
    let n = get_bitvector_width' tenv t1 and m = get_bitvector_width' tenv t2 in
    if bitwidth_equal n m then ()
    else
      match (n, m) with
      | BitWidth_Determined e_n, BitWidth_Determined e_m ->
          let v_n = eval' tenv e_n and v_m = eval' tenv e_m in
          check_true' (value_equal v_n v_m) ()
      | _ -> assumption_failed ()

  let has_bitvector_structure tenv t =
    match (get_structure tenv.globals t).desc with
    | T_Bits _ -> true
    | _ -> false

  let t_bool = T_Bool |> add_dummy_pos
  let t_int = T_Int None |> add_dummy_pos

  let check_binop loc tenv op t1 t2 : ty =
    let () =
      if false then
        Format.eprintf "Checking binop %s between %a and %a@."
          (PP.binop_to_string op) PP.pp_ty t1 PP.pp_ty t2
    in
    let with_loc = add_pos_from loc in
    either
      (fun () ->
        match op with
        | BAND | BOR | BEQ | IMPL ->
            let+ () = check_type_satisfies' tenv t1 t_bool in
            let+ () = check_type_satisfies' tenv t2 t_bool in
            T_Bool |> with_loc
        | AND | OR | EOR ->
            (* Rule KXMR: If the operands of a primitive operation are
               bitvectors, the widths of the operands must be equivalent
               statically evaluable expressions. *)
            (* TODO: We cannot perform that at the moment, as it needs a
               symbolic expression solver. *)
            (*
            let+ () = check_bv_have_same_determined_bitwidth' tenv t1 t2 in
            *)
            let n = get_bitvector_width' tenv t1 in
            T_Bits (n, []) |> with_loc
        | (PLUS | MINUS) when has_bitvector_structure tenv t1 ->
            (* Rule KXMR: If the operands of a primitive operation are
               bitvectors, the widths of the operands must be equivalent
               statically evaluable expressions. *)
            let+ () =
              either
                (check_bv_have_same_determined_bitwidth' tenv t1 t2)
                (check_type_satisfies' tenv t2 t_int)
            in
            let n = get_bitvector_width' tenv t1 in
            T_Bits (n, []) |> with_loc
        | EQ_OP | NEQ ->
            (* Wrong! *)
            let+ () =
              any
                [
                  (* Optimisation. *)
                  check_true' (type_equal t1 t2);
                  (* If an argument of a comparison operation is a constrained
                     integer then it is treated as an unconstrained integer. *)
                  both
                    (check_type_satisfies' tenv t1 t_int)
                    (check_type_satisfies' tenv t2 t_int);
                  (* If the arguments of a comparison operation are bitvectors
                     then they must have the same determined width. *)
                  check_bv_have_same_determined_bitwidth' tenv t1 t2;
                  (* The rest are redundancies from the first equal types
                     cases, but provided for completeness. *)
                  both
                    (check_type_satisfies' tenv t1 t_bool)
                    (check_type_satisfies' tenv t2 t_bool);
                  (fun () ->
                    match (t1.desc, t2.desc) with
                    | T_Enum li1, T_Enum li2 ->
                        check_true' (list_equal String.equal li1 li2) ()
                    | _ -> assumption_failed ());
                ]
            in
            T_Bool |> with_loc
        | LEQ | GEQ | GT | LT ->
            let+ () = check_type_satisfies' tenv t1 t_int in
            let+ () = check_type_satisfies' tenv t2 t_int in
            T_Bool |> with_loc
        | MUL | DIV | MOD | SHL | SHR | PLUS | MINUS -> (
            (* TODO: ensure that they mean "has the structure of" instead of
               "is" *)
            let struct1 = get_structure tenv.globals t1
            and struct2 = get_structure tenv.globals t2 in
            match (struct1.desc, struct2.desc) with
            | T_Int None, T_Int _ | T_Int _, T_Int None ->
                (* Rule ZYWY: If both operands of an integer binary primitive
                   operator are integers and at least one of them is an
                   unconstrained integer then the result shall be an
                   unconstrained integer. *)
                (* TODO: check that no other checks are necessary. *)
                T_Int None |> with_loc
            | T_Int (Some []), T_Int (Some _) | T_Int (Some _), T_Int (Some [])
              ->
                (* Rule BZKW: If both operands of an integer binary primitive
                   operator are constrained integers and at least one of them
                   is the under-constrained integer then the result shall be an
                   under-constrained integer. *)
                T_Int (Some []) |> with_loc
            | T_Int (Some cs1), T_Int (Some cs2) ->
                (* Rule KFYS: If both operands of an integer binary primitive
                   operation are well-constrained integers, then it shall
                   return a constrained integer whose constraint is calculated
                   by applying the operation to all possible value pairs. *)
                (* TODO: check for division by zero? cf I YHRP: The calculation
                   of constraints shall cause an error if necessary, for
                   example where a division by zero occurs, etc. *)
                T_Int (Some (constraint_binop op cs1 cs2)) |> with_loc
            | _ -> assumption_failed ())
        | RDIV ->
            let+ () = check_type_satisfies' tenv t1 (T_Real |> add_dummy_pos) in
            T_Real |> with_loc)
      (fun () -> fatal_from loc (Error.BadTypesForBinop (op, t1, t2)))
      ()

  let check_unop loc tenv op t =
    match op with
    | BNOT ->
        let+ () = check_type_satisfies loc tenv t t_bool in
        T_Bool |> add_pos_from loc
    | NEG ->
        let+ () = check_type_satisfies loc tenv t t_int in
        (* TODO: work on constraints. *)
        T_Int None |> add_pos_from loc
    | NOT ->
        (* TODO: make sure that default_t_bits is type-satisfied by all [bits( * )] types *)
        let+ () =
          check_type_satisfies loc tenv t (default_t_bits |> add_dummy_pos)
        in
        t

  let rec try_annotate_expr tenv lenv e =
    best_effort (t_int, e) (fun (_, e) -> annotate_expr tenv lenv e) |> snd

  and annotate_slices tenv lenv =
    (* Rules:
       - Rule WZCS: The width of a bitslice must be any non-negative,
         statically evaluable integer expression (including zero).
       - Rule KTBG: It is an error if any bits selected by a bitslice are not
         in range for the expression being sliced. If the offset of a bitslice
         depends on a statically evaluable expression then this shall be
         checked at compile time. Otherwise a bounds check will occur at
         execution-time and an implementation defined exception shall be thrown
         if it fails.
       TODO: check them
       TODO: there should be a rule that an index inside a slice should have
       the structure of an integer
    *)
    let tr_one = function
      | Slice_Single e ->
          (* First rule trivially true. *)
          (* TODO: try evaluate this at compile time, and check it against sliced
             expression type. *)
          let t_e, e = annotate_expr tenv lenv e in
          let+ () = check_structure_integer e tenv t_e in
          Slice_Single e
      | Slice_Range (e1, e2) ->
          let t_e1, e1 = annotate_expr tenv lenv e1
          and t_e2, e2 = annotate_expr tenv lenv e2 in
          let+ () = check_structure_integer e1 tenv t_e1 in
          let+ () = check_structure_integer e2 tenv t_e2 in
          (* TODO: check that diff is statically evaluable. *)
          Slice_Range (e1, e2)
      | Slice_Length (e1, e2) ->
          let t_e1, e1 = annotate_expr tenv lenv e1
          and t_e2, e2 = annotate_expr tenv lenv e2 in
          let+ () = check_structure_integer e1 tenv t_e1 in
          let+ () = check_structure_integer e2 tenv t_e2 in
          (* TODO: check that length is statically evaluable. *)
          (* TODO: if offset is statically evaluable, check that it is less
             than sliced expression width. *)
          Slice_Length (e1, e2)
    in
    List.map tr_one

  and annotate_pattern loc tenv lenv t = function
    | Pattern_All as p -> p
    | Pattern_Any li ->
        Pattern_Any (List.map (annotate_pattern loc tenv lenv t) li)
    | Pattern_Not p -> Pattern_Not (annotate_pattern loc tenv lenv t p)
    | Pattern_Single e ->
        let t_e, e = annotate_expr tenv lenv e in
        let+ () =
         fun () ->
          let t_struct = get_structure tenv.globals t
          and t_e_struct = get_structure tenv.globals t_e in
          match (t_struct.desc, t_e_struct.desc) with
          | T_Bool, T_Bool | T_Real, T_Real -> ()
          | T_Int _, T_Int _ -> ()
          | T_Bits _, T_Bits _ ->
              check_bv_have_same_determined_bitwidth' tenv t_struct t_e_struct
                ()
          (* TODO: Multiple discriminants can be matched at once by forming
             a tuple of discriminants and a tuple used in the pattern_set.
             Both tuples must have the same number of elements. A
             successful pattern match occurs when each discriminant term
             matches the respective term of the pattern tuple. *)
          | T_Enum li1, T_Enum li2 when list_equal String.equal li1 li2 -> ()
          | _ -> fatal_from loc (Error.BadTypesForBinop (EQ_OP, t, t_e))
        in
        Pattern_Single e
    | Pattern_Geq e ->
        (* TODO: check that e is statically evaluable. *)
        let t_e, e = annotate_expr tenv lenv e in
        let+ () =
          both
            (check_structure_integer loc tenv t)
            (check_structure_integer loc tenv t_e)
        in
        Pattern_Geq e
    | Pattern_Leq e ->
        (* TODO: check that e is statically evaluable. *)
        let t_e, e = annotate_expr tenv lenv e in
        let+ () =
          both
            (check_structure_integer loc tenv t)
            (check_structure_integer loc tenv t_e)
        in
        Pattern_Leq e
    | Pattern_Range (e1, e2) ->
        let t_e1, e1 = annotate_expr tenv lenv e1
        and t_e2, e2 = annotate_expr tenv lenv e2 in
        let+ () =
          both
            (check_structure_integer loc tenv t)
            (both
               (check_structure_integer loc tenv t_e1)
               (check_structure_integer loc tenv t_e2))
        in
        Pattern_Range (e1, e2)
    | Pattern_Mask _ as p ->
        (* TODO. *)
        let+ () =
          fatal_from loc
            (Error.NotYetImplemented "Typing masks in pattern matching.")
        in
        p

  and annotate_expr tenv lenv (e : expr) : ty * expr =
    let () = if false then Format.eprintf "@[Annotating %a@]@." PP.pp_expr e in
    match e.desc with
    | E_Literal v -> (infer_value v |> add_pos_from e, e)
    | E_Typed (e', t) ->
        let t = get_structure tenv.globals t in
        let t_e, e'' = annotate_expr tenv lenv e' in
        (* - If type-checking determines that the expression type-satisfies
             the required type, then no further check is required.
           - If the expression only fails to type-satisfy the required type
             because the domain of its type is not a subset of the domain of
             the required type, an execution-time check that the expression
             evaluates to a value in the domain of the required type is
             required. *)
        best_effort
          (t, E_Typed (e'', t) |> add_pos_from_st e)
          (fun res ->
            let tenv' = (tenv.globals, IMap.empty) in
            if Types.structural_subtype_satisfies tenv' t_e t then
              if Types.domain_subtype_satisfies tenv' t_e t then (t_e, e'')
              else res
            else conflict e [ t_e.desc ] t)
    | E_Var x -> (
        let () = if false then Format.eprintf "Looking at %S.@." x in
        match getter_should_reduce_to_call tenv x [] with
        | Some (name, args) ->
            let () =
              if false then
                Format.eprintf "@[Reducing getter %S@ at %a@]@." x PP.pp_pos e
            in
            E_Call (name, args, [])
            |> add_pos_from_st e |> annotate_expr tenv lenv
        | None ->
            let () =
              if false then
                Format.eprintf "@[Choosing not to reduce var %S@ at @[%a@]@]@."
                  x PP.pp_pos e
            in
            (lookup tenv lenv e x, e))
    | E_Binop (BAND, e1, e2) ->
        E_Cond (e1, e2, E_Literal (V_Bool false) |> add_pos_from_st e)
        |> add_pos_from_st e |> annotate_expr tenv lenv
    | E_Binop (BOR, e1, e2) ->
        E_Cond (e1, E_Literal (V_Bool true) |> add_pos_from_st e, e2)
        |> add_pos_from_st e |> annotate_expr tenv lenv
    | E_Binop (op, e1, e2) ->
        let t1, e1' = annotate_expr tenv lenv e1 in
        let t2, e2' = annotate_expr tenv lenv e2 in
        let t = check_binop e tenv op t1 t2 in
        (t, E_Binop (op, e1', e2') |> add_pos_from_st e)
    | E_Unop (op, e') ->
        let t'', e'' = annotate_expr tenv lenv e' in
        let t = check_unop e tenv op t'' in
        (t, E_Unop (op, e'') |> add_pos_from_st e)
    | E_Call (name, args, eqs) ->
        let caller_arg_types, args =
          List.map (annotate_expr tenv lenv) args |> List.split
        in
        let name, eqs =
          best_effort (name, eqs) (fun _ ->
              let extra_nargs, name, callee_arg_types =
                either
                  (fun () ->
                    FunctionRenaming.find_name_strict e tenv name
                      caller_arg_types)
                  (fun () ->
                    let extra_nargs, name =
                      FunctionRenaming.find_name tenv name caller_arg_types
                    in
                    match IMap.find_opt name tenv.funcs with
                    | None -> undefined_identifier e ("function " ^ name)
                    | Some (_, None) ->
                        fatal_from e @@ Error.MismatchedReturnValue name
                    | Some (callee_arg_types, _return_type) ->
                        (extra_nargs, name, callee_arg_types))
                  ()
              in
              let eqs = List.rev_append eqs extra_nargs in
              let () =
                if List.compare_lengths callee_arg_types args != 0 then
                  fatal_from e
                  @@ Error.BadArity
                       (name, List.length callee_arg_types, List.length args)
              in
              let eqs =
                let folder acc (x, _) e = (x, e) :: acc in
                List.fold_left2 folder eqs callee_arg_types args
              in
              let () =
                if false && not (String.equal name name) then
                  Format.eprintf "Renaming call from %s to %s@ at %a.@." name
                    name PP.pp_pos e
              in
              (name, eqs))
        in
        ( lookup_return_type tenv e name |> rename_ty_eqs eqs,
          E_Call (name, args, eqs) |> add_pos_from_st e )
    | E_Cond (e_cond, e_true, e_false) ->
        let t_cond, e_cond = annotate_expr tenv lenv e_cond in
        let+ () = check_structure_boolean e tenv t_cond in
        let t_true, e_true = annotate_expr tenv lenv e_true
        and t_false, e_false = annotate_expr tenv lenv e_false in
        let t =
          best_effort t_true (fun _ ->
              match
                Types.lowest_common_ancestor (tenv.globals, IMap.empty) t_true
                  t_false
              with
              | None ->
                  fatal_from e
                    (Error.NotYetImplemented "Cannot reconcile the two types.")
              | Some t -> t)
        in
        (t, E_Cond (e_cond, e_true, e_false) |> add_pos_from_st e)
    | E_Tuple li ->
        let ts, es = List.map (annotate_expr tenv lenv) li |> List.split in
        (T_Tuple ts |> add_pos_from e, E_Tuple es |> add_pos_from_st e)
    | E_Concat [] ->
        (T_Bits (BitWidth_Determined (expr_of_int 0), []) |> add_pos_from e, e)
    | E_Concat (_ :: _ as li) ->
        let ts, es = List.map (annotate_expr tenv lenv) li |> List.split in
        let w =
          best_effort (BitWidth_Constrained []) (fun _ ->
              let widths = List.map (get_bitvector_width e tenv) ts in
              let wh = List.hd widths and wts = List.tl widths in
              List.fold_left width_plus wh wts)
        in
        (T_Bits (w, []) |> add_pos_from e, E_Concat es |> add_pos_from_st e)
    | E_Record (t, fields, _ta) ->
        (* Rule WBCQ: The identifier in a record expression must be a named type
           with the structure of a record type, and whose fields have the values
           given in the field_assignment_list. *)
        let+ () =
          check_true (Types.is_named t) (fun () ->
              failwith "Typing error: should be a named type")
        in
        let t_struct = get_structure tenv.globals t in
        let field_types = get_record_fields e tenv t in
        let fields =
          best_effort fields (fun _ ->
              (* Rule DYQZ: A record expression shall assign every field of the record. *)
              if
                List.for_all
                  (fun (name, _) -> List.mem_assoc name fields)
                  field_types
              then ()
              else fatal_from e (Error.BadFields (List.map fst fields, t));
              (* and whose fields have the values given in the field_assignment_list. *)
              List.map
                (fun (name, e') ->
                  let t', e' = annotate_expr tenv lenv e' in
                  let t_spec' =
                    match List.assoc_opt name field_types with
                    | None -> fatal_from e (Error.BadField (name, t))
                    | Some t_spec' -> t_spec'
                  in
                  (* TODO: No type checking rule exists here, I interprete
                     Rule LXQZ: A storage element of type S, where S is any
                     type that does not have the structure of the
                     under-constrained integer type, may only be assigned
                     or initialized with a value of type T if T
                     type-satisfies S. *)
                  let+ () = check_type_satisfies e tenv t' t_spec' in
                  (name, e'))
                fields)
        in
        ( t_struct,
          E_Record (t, fields, TA_InferredStructure t_struct)
          |> add_pos_from_st e )
    | E_Unknown t ->
        let t = get_structure tenv.globals t in
        (t, E_Unknown t |> add_pos_from_st e)
    | E_Slice (e', slices) -> (
        let reduced =
          match e'.desc with
          | E_Var x -> getter_should_reduce_to_call tenv x slices
          | _ -> None
        in
        match reduced with
        | Some (name, args) ->
            E_Call (name, args, [])
            |> add_pos_from_st e |> annotate_expr tenv lenv
        | None ->
            let t_e', e' = annotate_expr tenv lenv e' in
            let+ () =
              either
                (check_structure_bits e tenv t_e')
                (check_structure_integer e tenv t_e')
            in
            let w = slices_length slices in
            (* TODO: check that:
               - Rule SNQJ: An expression or subexpression which may result in
                 a zero-length bitvector must not be side-effecting.
            *)
            let slices = best_effort slices (annotate_slices tenv lenv) in
            ( T_Bits (BitWidth_Determined w, []) |> add_pos_from e,
              E_Slice (e', slices) |> add_pos_from_st e ))
    | E_GetField (e', field, _ta) -> (
        let t_e', e' = annotate_expr tenv lenv e' in
        let t_e'_struct = get_structure tenv.globals t_e' in
        match t_e'_struct.desc with
        | T_Record fields -> (
            match List.assoc_opt field fields with
            | None -> fatal_from e (Error.BadField (field, t_e'_struct))
            | Some t ->
                ( t,
                  E_GetField (e', field, TA_InferredStructure t_e'_struct)
                  |> add_pos_from_st e ))
        | T_Bits (_, bitfields) -> (
            match List.assoc_opt field bitfields with
            | None -> fatal_from e (Error.BadField (field, t_e'_struct))
            | Some slice ->
                let w = slices_length slice in
                (* I think rules KTBG and WZCS (see annotate_slices) do not
                   need to be checked here, but at type declaration. *)
                (* TODO: check that:
                   - Rule SNQJ: An expression or subexpression which may result in
                     a zero-length bitvector must not be side-effecting.
                *)
                ( T_Bits (BitWidth_Determined w, []) |> add_pos_from e,
                  E_GetFields (e', [ field ], TA_InferredStructure t_e'_struct)
                  |> add_pos_from_st e ))
        | _ -> conflict e [ default_t_bits; T_Record [] ] t_e')
    | E_GetFields (e', fields, _ta) ->
        let t_e', e' = annotate_expr tenv lenv e' in
        let t_e'_struct = get_structure tenv.globals t_e' in
        let bitfields =
          match t_e'_struct.desc with
          | T_Bits (_, bitfields) -> bitfields
          | _ -> conflict e [ default_t_bits ] t_e'
        in
        let one_field field =
          match List.assoc_opt field bitfields with
          | None -> fatal_from e (Error.BadField (field, t_e'_struct))
          | Some slices ->
              (* I think rules KTBG and WZCS (see annotate_slices) do not
                 need to be checked here, but at type declaration. *)
              slices_length slices
        in
        let w = List.map one_field fields |> sum |> reduce_constants in
        (* TODO: check that:
           - Rule SNQJ: An expression or subexpression which may result in a
             zero-length bitvector must not be side-effecting.
        *)
        ( T_Bits (BitWidth_Determined w, []) |> add_pos_from e,
          E_GetFields (e', fields, TA_InferredStructure t_e'_struct)
          |> add_pos_from_st e )
    | E_Pattern (e', patterns) ->
        (*
         Rule ZNDL states that

            The IN operator is equivalent to testing its first operand for
            equality against each value in the (possibly infinite) set denoted
            by the second operand, and taking the logical OR of the result.
            Values denoted by a bitmask_lit comprise all bitvectors that could
            match the bit-mask. It is not an error if any or all of the values
            denoted by the first operand can be statically determined to never
            compare equal with the second operand.

          e IN pattern            is sugar for
             "-"                      ->          TRUE
           | e1=expr                  ->          e == e1
           | bitmask_lit              ->          not yet implemented
           | e1=expr ".." e2=expr     ->          e1 <= e && e <= e2
           | "<=" e1=expr             ->          e <= e1
           | ">=" e1=expr             ->          e >= e1
           |  { p0 , ... pN }         ->          e IN p0 || ... e IN pN
           | !{ p0 , ... pN }         ->          not (e IN p0) && ... e IN pN

         We cannot reduce them here (as otherwise e might be evaluated a bad
         number of times), but we will apply the same typing rules as for those
         desugared expressions.
         *)
        let t_e', e' = annotate_expr tenv lenv e' in
        let patterns =
          best_effort patterns (annotate_pattern e tenv lenv t_e')
        in
        (T_Bool |> add_pos_from e, E_Pattern (e', patterns) |> add_pos_from_st e)

  let rec annotate_lexpr_fallback tenv lenv le =
    add_pos_from_st le
    @@
    match le.desc with
    | LE_Var _ -> le.desc
    | LE_Slice (le, slices) ->
        LE_Slice
          ( annotate_lexpr_fallback tenv lenv le,
            annotate_slices tenv lenv slices )
    | LE_SetField (le', field, _ta) -> (
        let le' = annotate_lexpr_fallback tenv lenv le' in
        let ty = infer_lexpr tenv lenv le' in
        match ty.desc with
        | T_Bits _ -> LE_SetFields (le', [ field ], TA_InferredStructure ty)
        | _ -> LE_SetField (le', field, TA_InferredStructure ty))
    | LE_SetFields (le', fields, _ta) ->
        let le' = annotate_lexpr_fallback tenv lenv le' in
        let ty = infer_lexpr tenv lenv le' in
        LE_SetFields (le', fields, TA_InferredStructure ty)
    | LE_Ignore -> LE_Ignore
    | LE_TupleUnpack les ->
        LE_TupleUnpack (List.map (annotate_lexpr_fallback tenv lenv) les)

  let can_assign_to tenv s t =
    (* Rules:
       - GNTS: It is illegal for a storage element whose type has the structure
         of the under-constrained integer to be assigned a value whose type has
         the structure of the under-constrained integer.
       - LXQZ: A storage element of type S, where S is any type that does not have the
         structure of the under-constrained integer type, may only be
         assigned or initialized with a value of type T if T type-satisfies S
    *)
    (* TODO: incomplete. *)
    let s_struct = get_structure tenv.globals s
    and t_struct = get_structure tenv.globals t in
    match (s_struct.desc, t_struct.desc) with
    | T_Int (Some []), T_Int (Some []) -> false
    | _ -> Types.type_satisfies (tenv.globals, IMap.empty) t s

  let rec annotate_lexpr tenv lenv le t_e =
    match le.desc with
    | LE_Var x ->
        (* TODO: Handle setting global var *)
        let ty =
          match IMap.find_opt x lenv with
          | None -> (
              match IMap.find_opt x tenv.globals with
              | Some ty -> ty
              | None -> undefined_identifier le x)
          | Some ty -> ty
        in
        let+ () =
         fun () ->
          if can_assign_to tenv ty t_e then ()
          else
            fatal_from le
              (Error.NotYetImplemented
                 "Cannot assign to variable because bad type.")
        in
        (lenv, le)
    | LE_Ignore -> (lenv, le)
    | LE_TupleUnpack les -> (
        match t_e.desc with
        | T_Tuple sub_tys ->
            if List.compare_lengths sub_tys les != 0 then
              Error.fatal_from le
                (Error.BadArity
                   ("tuple unpacking", List.length sub_tys, List.length les))
            else
              let folder (lenv, sub_les) sub_le sub_ty =
                let lenv, sub_le' = annotate_lexpr tenv lenv sub_le sub_ty in
                (lenv, sub_le' :: sub_les)
              in
              let lenv, les' = List.fold_left2 folder (lenv, []) les sub_tys in
              (lenv, LE_TupleUnpack (List.rev les') |> add_pos_from_st le)
        | _ -> conflict le [ T_Tuple [] ] t_e)
    | _ -> (lenv, annotate_lexpr_fallback tenv lenv le)

  let can_be_initialized_with tenv s t =
    (* Rules:
       - ZCVD: It is illegal for a storage element whose type has the
         structure of the under-constrained integer to be initialized with a
         value whose type has the structure of the under-constrained integer,
         unless the type is omitted from the declaration (and therefore the
         type can be unambiguously inferred) or the initialization expression
         is omitted (and therefore the type is not omitted from the
         declaration).
       - LXQZ: A storage element of type S, where S is any type that does not have the
         structure of the under-constrained integer type, may only be
         assigned or initialized with a value of type T if T type-satisfies
         S)
    *)
    let s_struct = get_structure tenv.globals s in
    match s_struct.desc with
    | T_Int (Some []) -> (* TODO *) assert false
    | _ -> Types.type_satisfies (tenv.globals, IMap.empty) t s

  let check_var_not_in_env loc tenv lenv x () =
    if IMap.mem x tenv.globals || IMap.mem x lenv || IMap.mem x tenv.funcs then
      fatal_from loc (Error.NotYetImplemented "Typing error: ")
    else ()

  let rec annotate_local_decl_item loc tenv lenv ty ldi =
    match ldi with
    | LDI_Ignore None -> (lenv, LE_Ignore |> add_pos_from loc)
    | LDI_Ignore (Some t) ->
        let+ () =
         fun () ->
          if can_be_initialized_with tenv t ty then ()
          else
            fatal_from loc
              (Error.NotYetImplemented
                 "typing error: cannot assign to a type that does not \
                  type-satisfies.")
        in
        (lenv, LE_Ignore |> add_pos_from loc)
    | LDI_Var (x, ty_opt) ->
        let t =
          best_effort ty (fun _ ->
              match ty_opt with
              | Some t ->
                  if can_be_initialized_with tenv t ty then t
                  else
                    fatal_from loc
                      (Error.NotYetImplemented
                         "typing error: cannot assign to a type that does not \
                          type-satisfies.")
              | _ -> ty)
        in
        let+ () =
          (* Rule LCFD: A local declaration shall not declare an identifier
             which is already in scope at the point of declaration. *)
          check_var_not_in_env loc tenv lenv x
        in
        let lenv = IMap.add x t lenv in
        (lenv, LE_Var x |> add_pos_from loc)
    | LDI_Tuple ([ ldi ], None) -> annotate_local_decl_item loc tenv lenv ty ldi
    | LDI_Tuple (ldis, None) ->
        let tys =
          match (get_structure tenv.globals ty).desc with
          | T_Tuple tys when List.compare_lengths tys ldis = 0 -> tys
          | T_Tuple tys ->
              fatal_from loc
                (Error.BadArity
                   ("tuple initialization", List.length tys, List.length ldis))
          | _ ->
              fatal_from loc
                (Error.NotYetImplemented
                   Format.(
                     asprintf
                       "Type Error: cannot unpack a value of type %a into a \
                        tuple of length."
                       PP.pp_ty ty))
        in
        let lenv, les =
          List.fold_left2
            (fun (lenv', les) ty' ldi' ->
              let lenv', le =
                annotate_local_decl_item loc tenv lenv' ty' ldi'
              in
              (lenv', le :: les))
            (lenv, []) tys ldis
        in
        (lenv, LE_TupleUnpack (List.rev les) |> add_pos_from loc)
    | LDI_Tuple (_ldis, Some _t) ->
        (* TODO: I don't know what to do in that case, for me the LRM is ambiguous in this case. *)
        assert false

  let rec annotate_local_decl_item_uninit loc tenv lenv ldi =
    match ldi with
    | LDI_Ignore _ -> (lenv, S_Pass |> add_pos_from_st loc)
    | LDI_Var (_, None) ->
        fatal_from loc
          (Error.NotYetImplemented "Variable declaration needs a type.")
    | LDI_Var (x, Some t) ->
        let+ () = check_var_not_in_env loc tenv lenv x in
        ( IMap.add x t lenv,
          S_Assign (LE_Var x |> add_pos_from loc, E_Unknown t |> add_pos_from t)
          |> add_pos_from loc )
    | LDI_Tuple (ldis, None) ->
        let lenv, ss =
          list_fold_left_map
            (annotate_local_decl_item_uninit loc tenv)
            lenv ldis
        in
        (lenv, stmt_from_list ss)
    | LDI_Tuple (ldis, Some t) ->
        let lenv, les =
          list_fold_left_map
            (fun lenv' -> annotate_local_decl_item loc tenv lenv' t)
            lenv ldis
        in
        let e = E_Unknown t |> add_pos_from t in
        let ss =
          List.map (fun le -> S_Assign (le, e) |> add_pos_from loc) les
        in
        (lenv, stmt_from_list ss)

  let rec annotate_stmt tenv lenv s =
    let () =
      if false then Format.eprintf "@[<3>Annotating@ @[%a@]@]@." PP.pp_stmt s
    in
    let tr_desc d =
      add_pos_from_st s d |> annotate_stmt tenv lenv
      |> fun ({ desc; _ }, lenv) -> (desc, lenv)
    in
    let add_pos (desc, lenv) = (add_pos_from_st s desc, lenv) in
    add_pos
    @@
    match s.desc with
    | S_Pass -> (S_Pass, lenv)
    | S_Then (s1, s2) ->
        let s1, lenv = annotate_stmt tenv lenv s1 in
        let s2, lenv = annotate_stmt tenv lenv s2 in
        (S_Then (s1, s2), lenv)
    | S_Assign (le, e) -> (
        let t_e, e = annotate_expr tenv lenv e in
        let reduced = setter_should_reduce_to_call_s tenv le e in
        match reduced with
        | Some { desc = s; _ } -> tr_desc s
        | None ->
            let lenv, le = annotate_lexpr tenv lenv le t_e in
            (S_Assign (le, e), lenv))
    | S_Call (name, args, named_args) ->
        let arg_types, args =
          List.map (annotate_expr tenv lenv) args |> List.split
        in
        let extra_nargs, name' =
          FunctionRenaming.find_name tenv name arg_types
        in
        (S_Call (name', args, List.rev_append named_args extra_nargs), lenv)
    | S_Return (Some e) ->
        let _t_e', e' = annotate_expr tenv lenv e in
        (* TODO: check that t_e <: return_type *)
        (S_Return (Some e'), lenv)
    | S_Return None ->
        (* TODO: check return type is none *)
        (S_Return None, lenv)
    | S_Cond (e, s1, s2) ->
        let t_cond, e = annotate_expr tenv lenv e in
        let+ () = check_type_satisfies e tenv t_cond t_bool in
        let s1, lenv = try_annotate_stmt tenv lenv s1 in
        let s2, lenv = try_annotate_stmt tenv lenv s2 in
        (S_Cond (e, s1, s2), lenv)
    | S_Case (e, cases) ->
        let e = try_annotate_expr tenv lenv e in
        let annotate_case (acc, lenv) case =
          let p, s = case.desc in
          let s, lenv = try_annotate_stmt tenv lenv s in
          (add_pos_from_st case (p, s) :: acc, lenv)
        in
        let cases, lenv = List.fold_left annotate_case ([], lenv) cases in
        (S_Case (e, List.rev cases), lenv)
    | S_Assert e ->
        let t_e', e' = annotate_expr tenv lenv e in
        let+ () = check_type_satisfies s tenv t_e' t_bool in
        (S_Assert e', lenv)
    | S_Decl (ldk, ldi, e_opt) -> (
        match (ldk, e_opt) with
        | _, Some e ->
            let t_e, e = annotate_expr tenv lenv e in
            let lenv, le = annotate_local_decl_item s tenv lenv t_e ldi in
            (* TODO:
               - The initialization expression in a local constant declaration
                 must be a compile-time-constant expression.
               - A local storage element declared with constant is initialized
                 with the value of its initialization expression during
                 compilation.
               - Initialization expressions in local constant declarations must
                 be non-side-effecting.
            *)
            (S_Assign (le, e), lenv)
        | LDK_Var, None ->
            (* TODO *)
            let lenv, s = annotate_local_decl_item_uninit s tenv lenv ldi in
            (s.desc, lenv)
        | (LDK_Constant | LDK_Let), None ->
            (* by construction in Parser. *)
            assert false)

  and try_annotate_stmt tenv lenv s =
    best_effort (s, lenv) (fun (s, lenv) -> annotate_stmt tenv lenv s)

  let annotate_func (tenv : tenv) (f : AST.func) : AST.func =
    let () = if false then Format.eprintf "Annotating %s.@." f.name in
    (* Build typing local environment. *)
    let lenv =
      let one_arg acc (x, ty) =
        IMap.add x (get_structure tenv.globals ty) acc
      in
      List.fold_left one_arg IMap.empty f.args
    in
    (* Add dependently typed identifiers. *)
    let add_dependently_typed_from_ty lenv ty =
      match ty.desc with
      | T_Bits (BitWidth_Determined { desc = E_Var x; _ }, _) ->
          if IMap.mem x lenv then lenv
          else IMap.add x (T_Int None |> add_dummy_pos) lenv
      | _ -> lenv
    in
    (* Resolve dependently typed identifiers in the arguments. *)
    let lenv =
      let one_arg acc (_, ty) = add_dependently_typed_from_ty acc ty in
      List.fold_left one_arg lenv f.args
    in
    (* Resolve dependently typed identifiers in the result type. *)
    let lenv =
      match f.return_type with
      | None -> lenv
      | Some t -> add_dependently_typed_from_ty lenv t
    in
    (* Annotate body *)
    let body, _lenv = try_annotate_stmt tenv lenv f.body in
    (* Optionnally rename the function if needs be *)
    let one_arg (_x, t) = get_structure tenv.globals t in
    let args = List.map one_arg f.args in
    let _, name = FunctionRenaming.find_name tenv f.name args in
    let () =
      if false then
        Format.eprintf "Renaming decl of %s (%a) to %s.@." f.name
          (Format.pp_print_list PP.pp_ty)
          args name
    in
    { f with body; name }

  let try_annotate_func tenv f = best_effort f (annotate_func tenv)
end

module TypeCheck = Annotate (struct
  let check = `TypeCheck
end)

module TypeInferWarn = Annotate (struct
  let check = `Warn
end)

module TypeInferSilence = Annotate (struct
  let check = `Silence
end)

(******************************************************************************)
(*                                                                            *)
(*                           Global env and funcs                             *)
(*                                                                            *)
(******************************************************************************)

let build_funcs genv : AST.t -> func_sig IMap.t * func_tr =
  let one_func tr_table_ref = function
    | D_Func { name; args; return_type; body = _; parameters = _ } ->
        let args =
          let one_arg (x, ty) = (x, get_structure genv ty) in
          List.map one_arg args
        and return_type =
          match return_type with
          | None -> None
          | Some ty -> Some (get_structure genv ty)
        in
        let name' = FunctionRenaming.add_new_func tr_table_ref name args in
        Some (name', (args, return_type))
    | _ -> None
  in
  let one_func tr_table_ref f =
    match Error.intercept (fun () -> one_func tr_table_ref f) () with
    | Ok res -> res
    | Error e ->
        if _warn then
          Format.eprintf
            "@[<v 2>Ignoring type error:@ %a@;<1 -2>in func:@ @[<v>%a@]@]@."
            Error.pp_error e PP.pp_t [ f ];
        None
  in
  fun ast ->
    let tr_table_ref = FunctionRenaming.new_tr_table () in
    let funcs =
      List.to_seq ast |> Seq.filter_map (one_func tr_table_ref) |> IMap.of_seq
    in
    let tr_table = FunctionRenaming.to_tr_table tr_table_ref in
    let () =
      if false then (
        Format.eprintf "@[<v 2>Function env:@ ";
        IMap.iter
          (fun name li ->
            List.iter
              (fun (arg, name') ->
                Format.eprintf "- @[<hv 2>%s (-> %s):@ @[<hv>%a@]@]@ " name
                  name'
                  (Format.pp_print_list ~pp_sep:Format.pp_print_space
                     (fun f (_, t) -> PP.pp_ty f t))
                  arg)
              li)
          tr_table;
        Format.eprintf "@]@.")
    in
    (funcs, tr_table)

let reduce_genv : genv -> genv =
  let should_reduce genv = function
    | x, ({ desc = T_Named y; _ } as pos) -> (
        let () = if false then Format.eprintf "Reducing genv at %S." x in
        match IMap.find_opt y genv with
        | None -> undefined_identifier pos y
        | Some z -> Some (x, z))
    | _ -> None
  in
  let rec reduce genv =
    let edit_one (genv, _edited) (x, y) = (IMap.add x y genv, true) in
    let genv, edited =
      IMap.to_seq genv
      |> Seq.filter_map (should_reduce genv)
      |> Seq.fold_left edit_one (genv, false)
    in
    if edited then reduce genv else genv
  in
  reduce

let build_genv : AST.t -> genv =
  let one_decl acc = function
    | D_TypeDecl (name, ({ desc = T_Enum ids; _ } as ty)) ->
        let acc = IMap.add name ty acc in
        let id_type = T_Named name |> add_dummy_pos in
        let add_one_id acc x = IMap.add x id_type acc in
        List.fold_left add_one_id acc ids
    | D_TypeDecl (name, ty) | D_GlobalConst (name, ty, _) ->
        IMap.add name ty acc
    | _ -> acc
  in
  List.fold_left one_decl IMap.empty

(******************************************************************************)
(*                                                                            *)
(*                                Entry point                                 *)
(*                                                                            *)
(******************************************************************************)

let annotate_ast ast =
  let globals = build_genv ast |> reduce_genv in
  let funcs, func_tr = build_funcs globals ast in
  let annotate_func =
    TypeInferSilence.try_annotate_func { globals; funcs; func_tr }
  in
  let one_decl = function D_Func f -> D_Func (annotate_func f) | d -> d in
  List.map one_decl ast

let type_check_ast strictness ast =
  let globals = build_genv ast |> reduce_genv in
  let funcs, func_tr = build_funcs globals ast in
  let tenv = { globals; funcs; func_tr } in
  let annotate =
    match strictness with
    | `TypeCheck -> TypeCheck.annotate_func
    | `Warn -> TypeInferWarn.try_annotate_func
    | `Silence -> TypeInferSilence.try_annotate_func
  in
  let one_decl = function D_Func f -> D_Func (annotate tenv f) | d -> d in
  List.map one_decl ast
