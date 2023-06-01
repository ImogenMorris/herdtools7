open Asllib
open AST
open Test_helpers.Helpers
open Test_helpers.Helpers.Infix

let build_consts () =
  let values =
    [ ("c1", !$3); ("c2", !!(E_Slice (!%"c1", [ Slice_Range (!$3, !$0) ]))) ]
  in
  let consts =
    List.map (fun (name, e) -> D_GlobalConst (name, !!(T_Int None), e)) values
  in
  let main =
    D_Func
      {
        name = "main";
        body = !!S_Pass;
        args = [];
        parameters = [];
        return_type = None;
      }
  in
  let ast = main :: consts in
  let _ = Native.interprete `TypeCheck ast in
  ()

let () = exec_tests [ ("build_consts", build_consts) ]
