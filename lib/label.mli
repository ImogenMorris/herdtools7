(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2010-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Labels in code *)

type t = string

val pp : t -> string
val compare : t -> t -> int
val reset : unit -> unit
val next_label : string -> t

val last : int -> t

type next = Any | Next | To of t | Disp of int

module Set : MySet.S with type elt = t
module Map : MyMap.S with type key = t

val norm : Set.t -> t option

module Full :
  sig
    type full = Proc.t * t

    val pp : full -> string
    val equal : full -> full -> bool
    val compare : full -> full -> int

    module Set : MySet.S with type elt = full
  end
