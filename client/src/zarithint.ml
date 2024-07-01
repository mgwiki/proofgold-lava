(* Copyright (c) 2021-2024 The Proofgold Lava developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* This module provides utility functions for working with big integers. *)

(* Define some commonly used big integer constants. *)
let zero_big_int = Z.zero
let unit_big_int = Z.one
let two_big_int = Z.of_int 2

(* Convert a string to a big integer. *)
let big_int_of_string x =
  let r = Z.of_string x in
  r

(* Convert a big integer to a string. *)
let string_of_big_int x =
  let r = Z.to_string x in
  r

(* Convert a big integer to an OCaml int, int32, or int64. *)
let int_of_big_int x = Z.to_int x
let int32_of_big_int x = Z.to_int32 x
let int64_of_big_int x = Z.to_int64 x

(* Convert an OCaml int, int32, or int64 to a big integer. *)
let big_int_of_int x =
  let r = Z.of_int x in
  r

let big_int_of_int32 x =
  let r = Z.of_int32 x in
  r

let big_int_of_int64 x =
  let r = Z.of_int64 x in
  r

(* Compare two big integers for equality, less-than-or-equal, greater-than-or-equal,
   less-than, greater-than, and sign. *)
let eq_big_int x y = Z.equal x y
let le_big_int x y = Z.leq x y
let ge_big_int x y = Z.geq x y
let lt_big_int x y = Z.lt x y
let gt_big_int x y = Z.gt x y
let sign_big_int x = Z.sign x

(* Increment a big integer by one. *)
let succ_big_int x =
  let r = Z.succ x in
  r

(* Add two big integers, or add an OCaml int to a big integer. *)
let add_big_int x y =
  let r = Z.add x y in
  r

let add_int_big_int x y = add_big_int (Z.of_int x) y

(* Subtract two big integers. *)
let sub_big_int x y =
  let r = Z.sub x y in
  r

(* Multiply two big integers, or multiply an OCaml int by a big integer. *)
let mult_big_int x y =
  let r = Z.mul x y in
  r

let mult_int_big_int x y = mult_big_int (Z.of_int x) y

(* Divide two big integers, or compute the modulus of a big integer with respect
   to another big integer. *)
let div_big_int x y =
  let r = Z.div x y in
  r

let mod_big_int x y =
  let r =
    if Z.sign x < 0 then
      Z.add y (Z.rem x y)
    else
      Z.rem x y
  in
  r

(* Compute the quotient and remainder of the division of two big integers. *)
let quomod_big_int x y =
  let r = Z.div_rem x y in
  r

(* Raise a big integer to a positive integer power. *)
let power_big_int_positive_int x y =
  let r = Z.pow x y in
  r

(* Compute the minimum of two big integers. *)
let min_big_int x y =
  let r = Z.min x y in
  r

(* Compute the bitwise AND, OR, and shifts of two big integers. *)
let and_big_int x y =
  let r = Z.logand x y in
  r

let or_big_int x y =
  let r = Z.logor x y in
  r

let shift_left_big_int x y =
  let r = Z.shift_left x y in
  r

let shift_right_towards_zero_big_int x y =
  let r = Z.shift_right_trunc x y in
  r

let rec loclist_to_code l =
  match l with
  | [] -> (0,zero_big_int)
  | None::r ->
     let (n,c) = loclist_to_code r in
     (n+1,c)
  | Some(b)::r ->
     let (n,c) = loclist_to_code r in
     let c2 = shift_left_big_int c 1 in
     (n+1,(if b then or_big_int unit_big_int c2 else c2))
