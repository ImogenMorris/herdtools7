(******************************************************************************)
(*                           the diy toolsuite                                *)
(*                                                                            *)
(* Jade Alglave, University College London, UK.                               *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                            *)
(*                                                                            *)
(* Copyright 2015-present Institut National de Recherche en Informatique et   *)
(* en Automatique and the authors. All rights reserved.                       *)
(*                                                                            *)
(* This software is governed by the CeCILL-B license under French law and     *)
(* abiding by the rules of distribution of free software. You can use,        *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B   *)
(* license as circulated by CEA, CNRS and INRIA at the following URL          *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.              *)
(******************************************************************************)
(* Authors:                                                                   *)
(* Hadrien Renaud, University College London, UK.                             *)
(******************************************************************************)
(* Disclaimer:                                                                *)
(* This material covers both ASLv0 (viz, the existing ASL pseudocode language *)
(* which appears in the Arm Architecture Reference Manual) and ASLv1, a new,  *)
(* experimental, and as yet unreleased version of ASL.                        *)
(* This material is work in progress, more precisely at pre-Alpha quality as  *)
(* per Arm’s quality standards.                                               *)
(* In particular, this means that it would be premature to base any           *)
(* production tool development on this material.                              *)
(* However, any feedback, question, query and feature request would be most   *)
(* welcome; those can be sent to Arm’s Architecture Formal Team Lead          *)
(* Jade Alglave <jade.alglave@arm.com>, or by raising issues or PRs to the    *)
(* herdtools7 github repository.                                              *)
(******************************************************************************)

module A64B = AArch64Base

(*****************************************************************************)
(*                                                                           *)
(*                               ASL preambule                               *)
(*                                                                           *)
(*****************************************************************************)

type scope = Asllib.AST.scope

let pp_scope =
  let open Asllib.AST in
  function
  | Scope_Global -> ""
  | Scope_Local (enclosure, call_nb) ->
      Printf.sprintf "%s.%d." enclosure call_nb

let arch_reg_to_int =
  let rec index_of elt pos li =
    match li with
    | [] -> raise Not_found
    | h :: _ when compare elt h = 0 -> pos
    | _ :: t -> index_of elt (pos + 1) t
  in
  fun r -> index_of r 0 AArch64Base.gprs

(*****************************************************************************)
(*                                                                           *)
(*                             Implem of archBase                            *)
(*                                                                           *)
(*****************************************************************************)

(* Who am I ? *)
let arch = Archs.asl
let base_type = A64B.base_type
let endian = A64B.endian

(***********************************************)
(* Basic arch types and their basic operations *)
(***********************************************)

type reg = ASLLocalId of scope * Asllib.AST.identifier | ArchReg of A64B.reg

let pp_reg = function
  | ASLLocalId (scope, x) -> pp_scope scope ^ x
  | ArchReg r -> A64B.pp_reg r

let is_local = function ASLLocalId _ -> true | _ -> false
let to_arch_reg = function ASLLocalId _ -> assert false | ArchReg r -> r
let to_reg r = ArchReg r
let main_scope = ("main", 0)
let default_scope = Asllib.AST.Scope_Global

let parse_local_id =
  let ( let* ) = Option.bind in
  let ( and* ) o1 o2 =
    match (o1, o2) with Some x1, Some x2 -> Some (x1, x2) | _ -> None
  in
  let find_opt n s =
    try Some (Str.matched_group n s) with Not_found -> None
  in
  let regexp =
    Str.regexp {|\([A-Za-z0-9_-]+\)\.\([0-9]+\)\.\([A-Za-z0-9_-]+\)|}
  in
  fun s ->
    if Str.string_match regexp s 0 then
      let* x1 = find_opt 1 s and* x2 = find_opt 2 s and* x3 = find_opt 3 s in
      Some (ASLLocalId (Asllib.AST.Scope_Local (x1, int_of_string x2), x3))
    else Some (ASLLocalId (default_scope, s))

let parse_reg s =
  match (A64B.parse_reg s, s) with
  | Some r, _ -> Some (ArchReg r)
  | None, "NZCV" -> Some (ArchReg AArch64Base.NZCV)
  | None, _ -> parse_local_id s

(** A list of supported AArch64 registers. *)
let gregs = List.map fst AArch64Base.xregs

let reg_compare r1 r2 =
  match (r1, r2) with
  | ArchReg r1, ArchReg r2 -> A64B.reg_compare r1 r2
  | ASLLocalId (s1, x1), ASLLocalId (s2, x2) ->
      if String.equal x1 x2 then Asllib.ASTUtils.scope_compare s1 s2
      else String.compare x1 x2
  | ArchReg _, ASLLocalId _ -> 1
  | ASLLocalId _, ArchReg _ -> -1

let symb_reg_name = function
  | ASLLocalId _ -> None
  | ArchReg r -> A64B.symb_reg_name r

let symb_reg x = ArchReg (A64B.symb_reg x)
let type_reg _ = assert false

type barrier = A64B.barrier

let pp_barrier = A64B.pp_barrier
let barrier_compare = A64B.barrier_compare

type parsedInstruction = unit Asllib.AST.t
type instruction = unit Asllib.AST.t

let pp_instruction _ppmode ast = Asllib.PP.t_to_string ast
let dump_instruction a = pp_instruction PPMode.Ascii a
let dump_instruction_hash = Asllib.Serialize.t_to_string
let allowed_for_symb = List.map to_reg A64B.allowed_for_symb
let fold_regs _ ab _ = ab
let map_regs _ _ i = i
let fold_addrs _ a _ = a
let map_addrs _ i = i
let norm_ins i = i
let get_next _ = assert false

let is_valid _ = true

include Pseudo.Make (struct
  type ins = instruction
  type pins = parsedInstruction
  type reg_arg = reg

  let parsed_tr ast = ast
  let get_naccesses _ = -1
  let size_of_ins _ = 4
  let fold_labels k _f _i = k
  let map_labels _f i = i
end)

let get_macro _ = assert false
let hash_pteval _ = assert false

(*****************************************************************************)
(*                                                                           *)
(*                                 ASL Utils                                 *)
(*                                                                           *)
(*****************************************************************************)

let memoize f =
  let table = Hashtbl.create 17 in
  fun ?ast_type version s ->
    let k = (ast_type, version, s) in
    match Hashtbl.find_opt table k with
    | Some r -> r
    | None ->
        let r = f ?ast_type version s in
        let () = Hashtbl.add table k r in
        r

let do_build_ast_from_file ?ast_type version fname =
  match Asllib.Builder.from_file_multi_version ?ast_type version fname with
  | Error e -> raise (Misc.Fatal (Asllib.Error.error_to_string e))
  | Ok ast -> ast

let build_ast_from_file = memoize do_build_ast_from_file

let asl_generic_parser version lexer lexbuf =
  match
    Asllib.Builder.from_lexer_lexbuf ~ast_type:`Ast version lexer lexbuf
  with
  | Error e -> raise (Misc.Fatal (Asllib.Error.error_to_string e))
  | Ok ast -> ([ (0, None, MiscParser.Main) ], [ [ Instruction ast ] ], [])

let stmts_from_string s =
  let open Asllib in
  let lexbuf = Lexing.from_string s in
  try Parser.stmts Lexer.token lexbuf
  with e ->
    Warn.fatal
      "Internal parsing of \"%s\" failed with %s" s (Printexc.to_string e)

module Instr = Instr.No (struct
  type instr = instruction
end)
