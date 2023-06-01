open Asllib
open Types
open AST
open Test_helpers.Helpers
open Test_helpers.Helpers.Infix

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
      T_Bits (BitWidth_Determined !$0, None);
      T_Bits
        (BitWidth_Determined !$3, Some [ ("Something", [ Slice_Single !$0 ]) ]);
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
  let integer = !!(T_Int None) in
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
  let bits_4 = !!(T_Bits (BitWidth_Determined !$4, None)) in
  let bits_2_4 =
    !!(T_Bits
         ( BitWidth_Constrained [ Constraint_Exact !$2; Constraint_Exact !$4 ],
           None ))
  in

  let env = (ASTUtils.IMap.empty, ASTUtils.IMap.empty) in

  assert (not (subtype_satisfies env bits_2_4 bits_4));

  ()

let () =
  exec_tests
    [
      ("types.builtin_examples", builtin_examples);
      ("types.structure_example", structure_example);
      ("types.subtype_example", subtype_examples);
    ]
