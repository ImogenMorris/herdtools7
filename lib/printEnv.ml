open Interpreter

open EV

(*  module rec V : sig

      type v =
        | Empty | Unv
        | Pair of (S.event * S.event)
        | Rel of S.event_rel
        | ClassRel of ClassRel.t
        | Event of S.event
        | Set of S.event_set
        | Clo of  closure
        | Prim of string * int * (v -> v)
        | Proc of  procedure
        | Tag of string * string     (* type  X name *)
        | ValSet of typ *  ValSet.t   (* elt type X set *)
        | Tuple of  v list   
(*type env = {
  vals : v lazy_t StringMap.t;
  enums : tag list StringMap.t;
  tags : tag StringMap.t;
}

 type env =
          { env : V.env ; silent : bool; ks : ks; }*)

    let debug_event chan e =
      fprintf chan
        "(eeid=%s iiid=%s action=%s)" (pp_eiid e) (pp_iiid e) (pp_action e)
*)

(*      type v =
        | Empty | Unv
        | Pair of (S.event * S.event)
        | Rel of S.event_rel
        | ClassRel of ClassRel.t
        | Event of S.event
        | Set of S.event_set
        | Clo of  closure
        | Prim of string * int * (v -> v)
        | Proc of  procedure
        | Tag of string * string     (* type  X name *)
        | ValSet of typ *  ValSet.t   (* elt type X set *)
        | Tuple of  v list  *)

(*let string_of_op2 o =
  match o with
  | Union -> "Union"
  | Inter -> "Inter"
  | Diff -> "Diff"
  | Seq -> "Seq"
  | Cartesian -> "Cartesian"
  | Add -> "Add"
  | Tuple -> "Tuple"*)

let string_of_silent silent = string_of_bool silent

