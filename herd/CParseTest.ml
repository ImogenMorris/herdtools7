(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2023-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

 module Make(Conf:RunTest.Config)(ModelConfig:CMem.Config) = struct
  module LexConfig = struct
    let debug = Conf.debug.Debug_herd.lexer
  end
  module ArchConfig = SemExtra.ConfigToArchConfig(Conf)
  let run =
    if Conf.variant Variant.S128 then
      let module ConfMorello = struct
        include CBase.Instr
      end in
      let module CValue = Int128Value.Make(ConfMorello) in
      let module CS = CSem.Make(Conf)(CValue) in
      let module CM = CMem.Make(ModelConfig)(CS) in
      let module C = CArch_herd.Make(ArchConfig)(CValue) in
      let module CLexParse = struct
        (* Parsing *)
        type pseudo = C.pseudo
        type token = CParser.token
        module Lexer = CLexer.Make(LexConfig)
        let shallow_lexer = Lexer.token false
        let deep_lexer = Lexer.token true
        let shallow_parser = CParser.shallow_main
        let deep_parser = CParser.deep_main

        (* Macros *)
        type macro = C.macro
        let macros_parser = CParser.macros
        let macros_expand = CBase.expand
      end in
      let module P = CGenParser_lib.Make (Conf) (C) (CLexParse) in
      let module X = RunTest.Make (CS) (P) (CM) (Conf) in
      X.run
    else
      let module CValue = Int32Value.Make(CBase.Instr) in
      let module CS = CSem.Make(Conf)(CValue) in
      let module CM = CMem.Make(ModelConfig)(CS) in
      let module C = CArch_herd.Make(ArchConfig)(CValue) in
      let module CLexParse = struct
        (* Parsing *)
        type pseudo = C.pseudo
        type token = CParser.token
        module Lexer = CLexer.Make(LexConfig)
        let shallow_lexer = Lexer.token false
        let deep_lexer = Lexer.token true
        let shallow_parser = CParser.shallow_main
        let deep_parser = CParser.deep_main

        (* Macros *)
        type macro = C.macro
        let macros_parser = CParser.macros
        let macros_expand = CBase.expand
      end in
      let module P = CGenParser_lib.Make (Conf) (C) (CLexParse) in
      let module X = RunTest.Make (CS) (P) (CM) (Conf) in
      X.run
end

