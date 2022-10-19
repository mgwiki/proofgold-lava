(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint

let hexchar i =
  match i with
  | 0 -> '0'
  | 1 -> '1'
  | 2 -> '2'
  | 3 -> '3'
  | 4 -> '4'
  | 5 -> '5'
  | 6 -> '6'
  | 7 -> '7'
  | 8 -> '8'
  | 9 -> '9'
  | 10 -> 'a'
  | 11 -> 'b'
  | 12 -> 'c'
  | 13 -> 'd'
  | 14 -> 'e'
  | 15 -> 'f'
  | _ -> raise (Failure("Not a hexit"))

let hexchar_inv x =
  match x with
  | '0' -> 0l
  | '1' -> 1l
  | '2' -> 2l
  | '3' -> 3l
  | '4' -> 4l
  | '5' -> 5l
  | '6' -> 6l
  | '7' -> 7l
  | '8' -> 8l
  | '9' -> 9l
  | 'A' -> 10l
  | 'B' -> 11l
  | 'C' -> 12l
  | 'D' -> 13l
  | 'E' -> 14l
  | 'F' -> 15l
  | 'a' -> 10l
  | 'b' -> 11l
  | 'c' -> 12l
  | 'd' -> 13l
  | 'e' -> 14l
  | 'f' -> 15l
  | _ -> raise (Failure("not a hexit: " ^ (string_of_int (Char.code x))))

let hexsubstring_int8 h i =
  Int32.to_int
    (Int32.logor
       (Int32.shift_left (hexchar_inv h.[i]) 4)
       (hexchar_inv h.[i+1]))

let hexstring_string s =
  let l = String.length s in
  let l2 = l/2 in
  let strb = Buffer.create l2 in
  let i = ref 1 in
  while (!i < l) do
    Buffer.add_char strb (Char.chr (hexsubstring_int8 s (!i-1)));
    i := !i + 2;
  done;
  Buffer.contents strb

let string_hexstring s =
  let l = String.length s in
  let l2 = l*2 in
  let strb = Buffer.create l2 in
  for i = 0 to l-1 do
    let x = Char.code s.[i] in
    Buffer.add_char strb (hexchar ((x lsr 4) land 15));
    Buffer.add_char strb (hexchar (x land 15));
  done;
  Buffer.contents strb

let string_bytelist s =
  let l = ref [] in
  for i = (String.length s) - 1 downto 0 do
    l := Char.code (s.[i])::!l
  done;
  !l

let hexsubstring_int32 h i =
  Int32.logor (Int32.shift_left (hexchar_inv h.[i]) 28)
    (Int32.logor (Int32.shift_left (hexchar_inv h.[i+1]) 24)
       (Int32.logor (Int32.shift_left (hexchar_inv h.[i+2]) 20)
	  (Int32.logor (Int32.shift_left (hexchar_inv h.[i+3]) 16)
	     (Int32.logor (Int32.shift_left (hexchar_inv h.[i+4]) 12)
		(Int32.logor (Int32.shift_left (hexchar_inv h.[i+5]) 8)
		   (Int32.logor (Int32.shift_left (hexchar_inv h.[i+6]) 4)
		      (hexchar_inv h.[i+7])))))))
  
let int32_hexstring b x =
  Buffer.add_string b (Bebits.to_hexstring (Bebits.of_int32 x))

let z65535 = big_int_of_int 65535

let big_int_sub_int32 x i =
  Int32.logor
    (Int32.shift_left (int32_of_big_int (and_big_int (shift_right_towards_zero_big_int x (i+16)) z65535)) 16)
    (int32_of_big_int (and_big_int (shift_right_towards_zero_big_int x i) z65535))

let int32_big_int_bits x i =
  or_big_int
    (shift_left_big_int (big_int_of_int32 (Int32.shift_right_logical x 16)) (i+16))
    (shift_left_big_int (big_int_of_int32 (Int32.logand x 65535l)) i)

let int32_rev x =
  Int32.logor
    (Int32.shift_left (Int32.logand x 0xffl) 24)
    (Int32.logor
       (Int32.shift_left (Int32.logand (Int32.shift_right_logical x 8) 0xffl) 16)
       (Int32.logor
	  (Int32.shift_left (Int32.logand (Int32.shift_right_logical x 16) 0xffl) 8)
	  (Int32.logand (Int32.shift_right_logical x 24) 0xffl)))

let hexstring_of_big_int x n =
  let xr = ref x in
  let r = ref "" in
  for i = 1 to n do
    r := Printf.sprintf "%c%s" (hexchar (int_of_big_int (and_big_int !xr (big_int_of_int 15)))) !r;
    xr := shift_right_towards_zero_big_int !xr 4
  done;
  !r

let big_int_of_hexstring s =
  let r = ref zero_big_int in
  for i = 0 to String.length s - 1 do
    r := add_big_int (shift_left_big_int !r 4) (big_int_of_int32 (hexchar_inv (s.[i])));
  done;
  !r

