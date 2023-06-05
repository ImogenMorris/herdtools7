open Asllib
open ASTUtils
open Types
open AST
open Test_helpers.Helpers
open Test_helpers.Helpers.Infix

let empty_env : env = (IMap.empty, IMap.empty)
let integer = !!(T_Int None)

let builtin_examples () =
  let assert_is_builtin_singular t =
    assert (is_builtin_singular !!t);
    assert (not (is_builtin_aggregate !!t));
    assert (is_builtin !!t);
    assert (is_anonymous !!t);
    ()
  in
  let assert_is_builtin_aggregate t =
    assert (is_builtin_aggregate !!t);
    assert (not (is_builtin_singular !!t));
    assert (is_builtin !!t);
    assert (is_anonymous !!t)
  in

  (* Builtin singulars *)
  List.iter assert_is_builtin_singular
    [
      T_Int None;
      T_Int (Some [ Constraint_Exact !$3 ]);
      T_Real;
      T_String;
      T_Bool;
      T_Enum [];
      T_Enum [ "Something"; "Something Else" ];
      T_Bits (BitWidth_Determined !$0, []);
      T_Bits (BitWidth_Determined !$3, [ ("Something", [ Slice_Single !$0 ]) ]);
    ];

  (* Builtin aggregate *)
  List.iter assert_is_builtin_aggregate
    [
      T_Tuple [];
      T_Tuple [ !!T_Real; !!T_String ];
      T_Record [];
      T_Record [ ("a", !!T_Real); ("B", !!(T_Int None)) ];
      T_Exception [];
      T_Exception [ ("a", !!T_Real); ("B", !!(T_Int None)) ];
    ];

  (* Not builtin *)
  assert (is_named !!(T_Named "type_x"));
  assert (not (is_builtin !!(T_Named "type_x")));
  assert (not (is_anonymous !!(T_Named "type_x")));

  ()

let structure_example () =
  (* type T1 of integer; *)
  let t1 = !!(T_Named "T1") in
  (* type T2 of (integer, T1); *)
  let t2_def = !!(T_Tuple [ integer; t1 ]) in
  let t2 = !!(T_Named "T2") in
  let env =
    ( ASTUtils.IMap.of_list [ ("T1", integer); ("T2", t2_def) ],
      ASTUtils.IMap.empty )
  in
  (* the named type `T1` whose structure is integer *)
  assert (is_named t1);
  assert ((get_structure env t1).desc = integer.desc);
  (* the named type `T2` whose structure is (integer, integer) *)
  assert (is_named t2);
  assert ((get_structure env t2).desc = T_Tuple [ integer; integer ]);
  (* Note that (integer, T1) is non-primitive since it uses T1 *)
  assert (is_non_primitive t2_def);
  (* the named (hence non-primitive) type `T1` *)
  assert (is_non_primitive t1);

  (* anonymous primitive type `integer` *)
  assert (is_primitive integer);
  assert (is_anonymous integer);

  (* the anonymous non-primitive type `(integer, T1)` whose structure is `(integer, integer)` *)
  assert (is_anonymous t2_def);
  assert (is_non_primitive t2_def);
  assert ((get_structure env t2).desc = T_Tuple [ integer; integer ]);

  ()

let subtype_examples () =
  let bits_4 = !!(T_Bits (BitWidth_Determined !$4, [])) in
  let bits_2_4 =
    !!(T_Bits
         ( BitWidth_Constrained [ Constraint_Exact !$2; Constraint_Exact !$4 ],
           [] ))
  in

  assert (not (subtype_satisfies empty_env bits_2_4 bits_4));

  ()

let type_examples () =
  let bits_4 = !!(T_Bits (BitWidth_Determined !$4, [])) in
  let bits_n = !!(T_Bits (BitWidth_Determined !%"N", [])) in
  let bits_n' = !!(T_Bits (BitWidth_Determined !%"N", [])) in

  assert (type_satisfies empty_env bits_n bits_n');

  assert (not (type_satisfies empty_env !!T_Bool integer));
  assert (not (type_satisfies empty_env bits_4 integer));
  assert (type_satisfies empty_env integer integer);
  assert (type_satisfies empty_env bits_4 bits_4);
  assert (type_satisfies empty_env !!T_Bool !!T_Bool);

  ()

let lca_examples () =
  let bits_4 = !!(T_Bits (BitWidth_Determined !$4, [])) in
  let bits_2 = !!(T_Bits (BitWidth_Determined !$2, [])) in

  assert (Types.lowest_common_ancestor empty_env bits_4 bits_2 = None);

  let integer_4 = !!(T_Int (Some [ Constraint_Exact !$4 ])) in
  let integer_2 = !!(T_Int (Some [ Constraint_Exact !$2 ])) in

  let lca = Types.lowest_common_ancestor empty_env integer_4 integer_2 in
  assert (Option.is_some lca);
  let lca = Option.get lca in
  let domain = Domain.of_type empty_env lca in

  assert (Domain.mem (V_Int 2) domain);
  assert (Domain.mem (V_Int 4) domain);

  ()

let () =
  exec_tests
    [
      ("types.builtin_examples", builtin_examples);
      ("types.structure_example", structure_example);
      ("types.subtype_example", subtype_examples);
      ("types.lca_example", lca_examples);
      ("types.types_examples", type_examples);
    ]
