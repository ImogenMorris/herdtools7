(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2015-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Signed 128-bit integer types in pure OCaml. *)

module Int128 = struct
  type t = Int64.t * Int64.t

  let num_bits = 128

  let of_int u = Int64.zero, (Int64.of_int u)
  let of_int64 u = Int64.zero, u
  let of_int32 u = of_int64 (Int64.of_int32 u)
  (* Both int8 and int16 are implemented as int in Ocaml stdlib*)
  let of_int8 u = of_int u
  let of_int16 u = of_int u

  let zero = Int64.zero, Int64.zero
  let one = Int64.zero, Int64.one
  let max_int = Int64.max_int, Int64.max_int

  let logand a b = Int64.logand (fst a) (fst b), Int64.logand (snd a) (snd b)
  let logor a b = Int64.logor (fst a) (fst b), Int64.logor (snd a) (snd b)
  let logxor a b = Int64.logxor (fst a) (fst b), Int64.logxor (snd a) (snd b)
  let lognot a = Int64.lognot (fst a), Int64.lognot (snd a)

  let shift_left a by =
    if by < 0 then
      invalid_arg (Printf.sprintf "shift_left by negative: %i" by)
    else if by > num_bits then
      invalid_arg (Printf.sprintf "shift_left by %i" by)
    else if by = 0 then
      a
    else if by < 64 then
      let upper =
        Int64.logor
          (Int64.shift_left (fst a) by)
          (Int64.shift_right_logical (snd a) (64-by))
      in
      upper, Int64.shift_left (snd a) by
    else
      Int64.shift_left (snd a) (by-64), Int64.zero

  let shift_right_logical a by =
    if by < 0 then
      invalid_arg (Printf.sprintf "shift_right by negative: %i" by)
    else if by > num_bits then
      invalid_arg (Printf.sprintf "shift_right_logical %i" by)
    else if by = 0 then
      a
    else if by < 64 then
      let lower =
        Int64.logor
          (Int64.shift_left (fst a) (64-by))
          (Int64.shift_right_logical (snd a) by)
      in
      Int64.shift_right_logical (fst a) by, lower
    else
      Int64.zero, Int64.shift_right_logical (fst a) (by-64)

  let shift_right a by =
    let upper_bit = shift_left one (num_bits - 1) in
    let has_msb = logand a upper_bit = upper_bit in
    let rest = shift_right_logical a by in
    if has_msb then
      let rec upper_bits acc n =
        match n with
        | 0 -> acc
        | n -> upper_bits (logor upper_bit (shift_right_logical acc 1)) (n-1)
      in
      logor rest (upper_bits upper_bit by)
    else
      rest

  (* For signed integers, the top bit is the sign.
   * Thus, we will occasionally need to check if that bit is set,
   * or clear the bit for interaction with Int64.t. *)
  let top_bit = (0x8000000000000000L, 0L)
  let has_top_bit_set a = logand a top_bit <> zero

  let leading_zeros a =
    let rec leading_zeros' i a =
      match a with
      | (0L, a2) -> 64 + (leading_zeros' 0 (a2,0L))
      | a1 ->
          if has_top_bit_set a1 then
            i
          else
            leading_zeros' (i+1) (shift_left a 1)
    in
    leading_zeros' 0 a

  let compare a b =
    match Int64.compare (fst a) (fst b) with
    | 0 -> Int64.compare (snd a) (snd b)
    | n -> n

  let equal a b =
    Int64.equal (snd a) (snd b) && Int64.equal (fst a) (fst b)

  let add a b =
    let carry =
      if Int64.compare (Int64.add (snd a) (snd b)) (snd a) < 0 then
        1L
      else
        0L
    in
    Int64.add (Int64.add (fst a) (fst b)) carry, Int64.add (snd a) (snd b)

  let sub a b =
    let carry =
      if Int64.compare (Int64.sub (snd a) (snd b)) (snd a) > 0 then
        1L
      else
        0L
    in
    Int64.sub (fst a) (Int64.add (fst b) carry), Int64.sub (snd a) (snd b)

  let mul (a1, a2) (b1, b2) =
    (* Multiplication by parts.
     * For example,
     *   25 * 31 =
     *     20*30 + 5*30 + 20*1 + 5*1 =
     *       2*3*100 + 5*3*10 + * 2*1*10 + 5*1. *)
    let upper_bits u =
      Int64.shift_right_logical u 32
    in
    let lower_bits u =
      let bottom_32_bits = Int64.of_int32 Int32.max_int in
      Int64.logand u bottom_32_bits
    in
    let a2_1 = upper_bits a2 in
    let a2_2 = lower_bits a2 in

    let b2_1 = upper_bits b2 in
    let b2_2 = lower_bits b2 in

    let t1 = Int64.mul a2_2 b2_2 in
    let t2 = Int64.add (upper_bits t1) (Int64.mul a2_1 b2_2) in
    let t3 = Int64.add (lower_bits t2) (Int64.mul a2_2 b2_1) in

    let lower = Int64.add (lower_bits t1) (Int64.shift_left t3 32) in
    let upper = Int64.add (upper_bits t2) (upper_bits t3) in

    let upper = Int64.add upper (Int64.mul a2_1 b2_1) in
    let upper = Int64.add upper (Int64.mul a1 b2) in
    let upper = Int64.add upper (Int64.mul a2 b1) in
    upper, lower

  let div_and_rem a b =
    if compare b zero = 0 then
      raise Division_by_zero
    else if compare a b = 0 then
      one, zero
    else if compare a b < 0 then
      zero, a
    else
      (* Binary long division by shift and subtract. *)
      let rec div_and_rem' (i : int) (q : t) (r : t) (b : t) =
        let q, r =
          if compare r b >= 0 then
            logor q one, sub r b
          else
            q, r
        in
        if i = 0 then
          q, r
        else
          div_and_rem' (i - 1) (shift_left q 1) r (shift_right_logical b 1)
      in
      let shift = (leading_zeros b) - (leading_zeros a) in
      div_and_rem' shift zero a (shift_left b shift)

  let div a b =
    let d, _ = div_and_rem a b in d

  let rem a b =
    let _, r = div_and_rem a b in r

  let pred = sub one
  let succ = add one

  let to_int a = Int64.to_int (snd a)

  let of_int i =
    if i < 0 then
      Int64.max_int, Int64.of_int i
    else
      Int64.zero, Int64.of_int i

  let to_int64 (_,lo) = lo

  let of_int64 i =
    let hi =
      if Int64.compare i 0L < 0 then Int64.max_int else Int64.zero in
    hi,i


  let to_string a =
    let ten = of_int 10 in
    let string_of_digit q =
      assert (compare q ten < 0) ;
      Int64.to_string (snd q)
    in
    let rec to_string' total a =
      if compare a ten < 0 then
        (string_of_digit a) :: total
      else
        let q, r = div_and_rem a ten in
        to_string' ((string_of_digit r) :: total) q
    in
    to_string' [] a |> String.concat ""

  let to_string_hex a =
    match a with
    | 0L, a2 -> Printf.sprintf "0x%Lx" a2
    | a1, a2 -> Printf.sprintf "0x%Lx%016Lx" a1 a2

  let of_string raw =
    let of_string_hex raw =
      let len = String.length raw in
      if len <= 16 then
        Int64.zero, Int64.of_string ("0x" ^ raw)
      else if len <= 32 then
        Int64.of_string ("0x" ^ (String.sub raw 0 (len-16))), Int64.of_string ("0x" ^ (String.sub raw (len-16) 16))
      else
        failwith "too many hex digits"
    in
    let of_string_oct _a = failwith "not implemented: of_string_oct" in
    let of_string_bin raw =
      let len = String.length raw in
      if len <= 64 then
        Int64.zero, Int64.of_string ("0b" ^ raw)
      else if len <= 128 then
        Int64.of_string ("0b" ^ (String.sub raw 0 (len-64))), Int64.of_string ("0b" ^ (String.sub raw (len-64) 64))
      else
        failwith "too many bits"
    in
    let of_string_dec a =
      let of_char c =
        match c with
        | '0' -> zero
        | '1' -> one
        | '2' -> of_int 2
        | '3' -> of_int 3
        | '4' -> of_int 4
        | '5' -> of_int 5
        | '6' -> of_int 6
        | '7' -> of_int 7
        | '8' -> of_int 8
        | '9' -> of_int 9
        | _ -> failwith (Printf.sprintf "invalid character: %c" c)
      in
      let ten = of_int 10 in
      let acc = ref zero in
      String.iter (fun c -> acc := add (mul !acc ten) (of_char c)) a ;
      !acc
    in
    let len = String.length raw in
    if len >= 2 then
      match raw.[0], raw.[1] with
      | '0', 'x' -> of_string_hex (String.sub raw 2 (len-2))
      | '0', 'o' -> of_string_oct (String.sub raw 2 (len-2))
      | '0', 'b' -> of_string_bin (String.sub raw 2 (len-2))
      | _ -> of_string_dec raw
    else
      of_string_dec raw
end
