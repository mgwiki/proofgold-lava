(* Copyright (c) 2021-2024 The Proofgold Lava developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint

(*** Generic serialization code ***)

let z255 = big_int_of_int 255

(*** String Buffer (out) / String (in), partly copied from Egal ***)

(* A type representing a string buffer and an optional "byte I/O" value. *)
type seosbt = Buffer.t * (int * int) option

(* A type representing a string and an optional "byte I/O" value, along with
   the index of the current character and the number of characters remaining. *)
type seist = string * int * int option * int * int

(* Writes a single byte to a string buffer. *)
let output_byte_sb c by =
  Buffer.add_char c (char_of_int by)

(* Serialize a value using a string buffer. *)
let seosbf (c,byio) =
  match byio with
  | Some (by,i) -> output_byte_sb c by
  | None -> ()

(* Serialize a value using a string buffer. *)
let rec seosb n b (c,byio) =
  if n = 0 then
    (c,byio)
  else
    match byio with
    | Some (by,i) -> 
	if (i + n >= 8) then
	  begin
	    output_byte_sb c (((b lsl i) land 255) lor by);
	    seosb (i+n-8) (b lsr (8-i)) (c,None)
	  end
	else
	  (c,Some (((b lsl i) lor by),i+n))
    | None ->
	if n < 8 then
	  (c,Some(b,n))
	else
	  (output_byte_sb c (b land 255); seosb (n-8) (b lsr 8) (c,None))

(* Deserialize a value from a string. *)
let rec seis_old n (s,k,byo,i,j) =
  if n = 0 then
    (0,(s,k,byo,i,j))
  else if (j >= 0 && i >= 0 && i < k) then
    match byo with
    | None ->
	let by = int_of_char (String.get s i) in
	seis_old n (s,k,Some(by),i,j)
    | Some(by) ->
	let b = (by lsr j) in
	if (j + n < 8) then
	  (b mod (1 lsl n),(s,k,Some(by),i,j+n))
	else
	  let l = 8-j in
	  let (br,z) = seis_old (n-l) (s,k,None,i+1,0) in
	  ((b mod (1 lsl l)) lor (br lsl l),z)
  else
    raise Not_found

(* Deserialize a value from a string. *)
let seis n t =
  let rec seis n (s,k,byo,i,j) lorby lslby =
    if n = 0 then
      (lorby,(s,k,byo,i,j))
    else if (j >= 0 && i >= 0 && i < k) then
      let by = int_of_char (s.[i]) in
      let b = (by lsr j) in
      if (j + n < 8) then
        ((lorby lor ((b mod (1 lsl n)) lsl lslby)),(s,k,None,i,j+n))
      else
        let l = 8-j in
        let nlorby = lorby lor ((b mod (1 lsl l)) lsl lslby) in
        seis (n-l) (s,k,None,i+1,0) nlorby (lslby + l)
    else
      raise Not_found
  in seis n t 0 0

(*** Channels ***)

(* A type representing an output channel and an optional "byte I/O" value. *)
type seoct = out_channel * (int * int) option

(* A type representing an input channel and an optional "byte I/O" value. *)
type seict = in_channel * (int * int) option

(* Serialize a value using an output channel. *)
let seocf (ch,byio) =
  match byio with
  | Some (by,i) -> output_byte ch by
  | None -> ()

(* Serialize a value using an output channel. *)
let rec seoc n b (ch,byio) =
  if n = 0 then
    (ch,byio)
  else
    match byio with
    | Some (by,i) -> 
	if (i + n >= 8) then
	  begin
	    output_byte ch (((b lsl i) land 255) lor by);
	    seoc (i+n-8) (b lsr (8-i)) (ch,None)
	  end
	else
	  (ch,Some (((b lsl i) lor by),i+n))
    | None ->
	if n < 8 then
	  (ch,Some(b,n))
	else
	  (output_byte ch (b land 255); seoc (n-8) (b lsr 8) (ch,None))

(* Deserialize a value from an input channel. *)
let rec seic n (ch,byo) =
  if n = 0 then
    (0,(ch,byo))
  else
    match byo with
    | None ->
	let by = input_byte ch in
	seic n (ch,Some(by,0))
    | Some(by,j) ->
	let b = (by lsr j) in
	if (j + n < 8) then
	  (b mod (1 lsl n),(ch,Some(by,j+n)))
	else
	  let l = 8-j in
	  let (br,z) = seic (n-l) (ch,None) in
	  ((b mod (1 lsl l)) lor (br lsl l),z)

(*** serialization of some specific types ***)

(* Serialize a boolean value. *)
let seo_bool o b c = o 1 (if b then 1 else 0) c

(* Deserialize a boolean value. *)
let sei_bool i c =
  let (x,c) = i 1 c in
  (x=1,c)

(* Serialize an 8-bit integer. *)
(*** int8 assumes int is a byte (0 to 255) ***)
let seo_int8 o x c = o 8 x c

(* Deserialize an 8-bit integer. *)
let sei_int8 i c = i 8 c

(*** big endian serialization of int32 and int64 ***)

(* Serialize a 32-bit integer in big-endian byte order. *)
let seo_int32 o x c =
  let c = o 8 (Int32.to_int (Int32.shift_right_logical x 24)) c in
  let c = o 8 (Int32.to_int (Int32.logand (Int32.shift_right_logical x 16) 255l)) c in
  let c = o 8 (Int32.to_int (Int32.logand (Int32.shift_right_logical x 8) 255l)) c in
  let c = o 8 (Int32.to_int (Int32.logand x 255l)) c in
  c

(* Serialize a 32-bit integer in big-endian byte order using a string buffer. *)
let seosb_int32 x c =
  match c with
  | (bu,None) ->
     Buffer.add_string bu (Bebits.of_int32 x);
     (bu,None)
  | _ -> seo_int32 seosb x c

(* Deserialize a 32-bit integer in big-endian byte order. *)
let sei_int32 i c =
  let (m3,c) = i 8 c in
  let (m2,c) = i 8 c in
  let (m1,c) = i 8 c in
  let (m0,c) = i 8 c in
  (Int32.logor (Int32.of_int m0)
     (Int32.logor (Int32.shift_left (Int32.of_int m1) 8)
	(Int32.logor (Int32.shift_left (Int32.of_int m2) 16)
	   (Int32.shift_left (Int32.of_int m3) 24))),c)

(* Serialize a 64-bit integer in big-endian byte order. *)
let seo_int64 o x c =
  let c = o 8 (Int64.to_int (Int64.shift_right_logical x 56)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 48) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 40) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 32) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 24) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 16) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand (Int64.shift_right_logical x 8) 255L)) c in
  let c = o 8 (Int64.to_int (Int64.logand x 255L)) c in
  c

(* Deserialize a 64-bit integer in big-endian byte order. *)
let sei_int64 i c =
  let (m7,c) = i 8 c in
  let (m6,c) = i 8 c in
  let (m5,c) = i 8 c in
  let (m4,c) = i 8 c in
  let (m3,c) = i 8 c in
  let (m2,c) = i 8 c in
  let (m1,c) = i 8 c in
  let (m0,c) = i 8 c in
  (Int64.logor (Int64.of_int m0)
     (Int64.logor (Int64.shift_left (Int64.of_int m1) 8)
	(Int64.logor (Int64.shift_left (Int64.of_int m2) 16)
	   (Int64.logor (Int64.shift_left (Int64.of_int m3) 24)
	      (Int64.logor (Int64.shift_left (Int64.of_int m4) 32)
		 (Int64.logor (Int64.shift_left (Int64.of_int m5) 40)
		    (Int64.logor (Int64.shift_left (Int64.of_int m6) 48)
		       (Int64.shift_left (Int64.of_int m7) 56))))))),c)

(*** big_int, assuming it is positive and < 2^256 ***)

(* Serialize a big integer using 256 bits. *)
let seo_big_int_256 o x c =
  let xr = ref x in
  let cr = ref c in
  for j = 0 to 31 do
    cr := o 8 (int_of_big_int (and_big_int !xr z255)) !cr;
    xr := shift_right_towards_zero_big_int !xr 8
  done;
  !cr

(* Deserialize a big integer using 256 bits. *)
let sei_big_int_256 i c =
  let xr = ref zero_big_int in
  let cr = ref c in
  for j = 0 to 31 do
    let (x,c) = i 8 !cr in
    cr := c;
    xr := or_big_int (shift_left_big_int (big_int_of_int x) (j*8)) !xr
  done;
  (!xr,!cr)


(*** the varint representation used in Bitcoin ***)

(* Serialize a variable-length integer. *)
let seo_varint o x c =
  if x >= 4294967296L then
    let c = o 8 255 c in
    seo_int64 o x c
  else if x >= 65536L then
    let c = o 8 254 c in
    let c = o 8 (Int64.to_int (Int64.logand x 255L)) c in
    let c = o 8 ((Int64.to_int (Int64.logand x 65535L)) lsr 8) c in
    let c = o 8 ((Int64.to_int (Int64.logand x 16777215L)) lsr 16) c in
    o 8 (Int64.to_int (Int64.shift_right_logical x 24)) c
  else
    let x = Int64.to_int x in
    if x < 253 then
      o 8 x c
    else
      let c = o 8 253 c in
      let c = o 16 x c in
      c

(* Deserialize a variable-length integer. *)
let sei_varint i c =
  let (x,c) = i 8 c in
  if x < 253 then
    (Int64.of_int x,c)
  else if x = 253 then
    let (m1,c) = i 8 c in
    let (m2,c) = i 8 c in
    (Int64.of_int (m1 + m2 lsl 8),c)
  else if x = 254 then
    let (m1,c) = i 8 c in
    let (m2,c) = i 8 c in
    let (m3,c) = i 8 c in
    let (m4,c) = i 8 c in
    (Int64.of_int (m1 + m2 lsl 8 + m3 lsl 16 + m4 lsl 24),c)
  else
    sei_int64 i c


(***
 another varint representation that requires only a few bits for small numbers
 and is only intended for numbers < 65536
 ***)

(* Serialize a variable-length integer using fewer bits for small integers. *)
let seo_varintb o x c =
  if x < 4 then
    let c = o 2 0 c in
    o 2 x c
  else if x < 20 then
    let c = o 2 1 c in
    o 4 (x-4) c
  else if x < 276 then
    let c = o 2 2 c in
    o 8 (x-20) c
  else
    let c = o 2 3 c in
    o 16 x c

(* Deserialize a variable-length integer using fewer bits for small integers. *)
let sei_varintb i c =
  let (b,c) = i 2 c in
  if b = 0 then
    i 2 c
  else if b = 1 then
    let (x,c) = i 4 c in
    (x+4,c)
  else if b = 2 then
    let (x,c) = i 8 c in
    (x+20,c)
  else
    i 16 c

(* Serialize a string. *)
let seo_string o x c =
  let l = String.length x in
  let cr = ref (seo_varint o (Int64.of_int l) c) in
  for j = 0 to l-1 do
    cr := seo_int8 o (Char.code x.[j]) !cr
  done;
  !cr

(* Deserialize a string. *)
let sei_string i c =
  let (l,c) = sei_varint i c in
  let l = Int64.to_int l in
  let cr = ref c in
  let sb = Buffer.create l in
  for j = 0 to l-1 do
    let (y,c) = sei_int8 i !cr in
    Buffer.add_char sb (Char.chr y);
    cr := c
  done;
  (Buffer.contents sb,!cr)

(*** operators to build serialization for list and option types ***)

(* Serialize a list using a serialization function for the elements. *)
let rec seo_list s o ml c =
  match ml with
  | [] -> o 1 0 c
  | m::mr ->
      let c = o 1 1 c in
      let c = s o m c in
      let c = seo_list s o mr c in
      c

(* Deserialize a list using a serialization function for the elements. *)
let rec sei_list s i c =
  let (b,c) = i 1 c in
  if b = 0 then
    ([],c)
  else
    let (m,c) = s i c in
    let (mr,c) = sei_list s i c in
    (m::mr,c)

(* Serialize an option using a serialization function for the value. *)
let seo_option s o ml c =
  match ml with
  | None -> o 1 0 c
  | Some(m) ->
      let c = o 1 1 c in
      let c = s o m c in
      c

(* Deserialize an option using a serialization function for the value. *)
let sei_option s i c =
  let (b,c) = i 1 c in
  if b = 0 then
    (None,c)
  else
    let (m,c) = s i c in
    (Some(m),c)

(* Serialize a tuple using serialization functions for the elements. *)
let seo_prod s1 s2 o (m,n) c =
  let c = s1 o m c in
  let c = s2 o n c in
  c

(* Deserialize a tuple using serialization functions for the elements. *)
let sei_prod s1 s2 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  ((m,n),c)

(* Serialize a tuple of three elements using serialization functions for the
   elements. *)
let seo_prod3 s1 s2 s3 o (m,n,k) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  c

(* Deserialize a tuple of three elements using serialization functions for the
   elements. *)
let sei_prod3 s1 s2 s3 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  ((m,n,k),c)

(* Serialize a tuple of a tuple and an element using serialization functions for
   the elements. *)
let seo_prod_prod s1 s2 s3 o ((m,n),k) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  c

(* Deserialize a tuple of a tuple and an element using serialization functions
   for the elements. *)
let sei_prod_prod s1 s2 s3 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  (((m,n),k),c)

(* Serialize a tuple of four elements using serialization functions for the
   elements. *)
let seo_prod4 s1 s2 s3 s4 o (m,n,k,l) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  let c = s4 o l c in
  c

(* Deserialize a tuple of four elements using serialization functions for the
   elements. *)
let sei_prod4 s1 s2 s3 s4 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  let (l,c) = s4 i c in
  ((m,n,k,l),c)

(* Serialize a tuple of five elements using serialization functions for the
   elements. *)
let seo_prod5 s1 s2 s3 s4 s5 o (m,n,k,l,p) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  let c = s4 o l c in
  let c = s5 o p c in
  c

(* Deserialize a tuple of five elements using serialization functions for the
   elements. *)
let sei_prod5 s1 s2 s3 s4 s5 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  let (l,c) = s4 i c in
  let (p,c) = s5 i c in
  ((m,n,k,l,p),c)

(* Serialize a tuple of six elements using serialization functions for the
   elements. *)
let seo_prod6 s1 s2 s3 s4 s5 s6 o (m,n,k,l,p,q) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  let c = s4 o l c in
  let c = s5 o p c in
  let c = s6 o q c in
  c

(* Deserialize a tuple of six elements using serialization functions for the
   elements. *)
let sei_prod6 s1 s2 s3 s4 s5 s6 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  let (l,c) = s4 i c in
  let (p,c) = s5 i c in
  let (q,c) = s6 i c in
  ((m,n,k,l,p,q),c)

(* Serialize a tuple of seven elements using serialization functions for the
   elements. *)
let seo_prod7 s1 s2 s3 s4 s5 s6 s7 o (m,n,k,l,p,q,r) c =
  let c = s1 o m c in
  let c = s2 o n c in
  let c = s3 o k c in
  let c = s4 o l c in
  let c = s5 o p c in
  let c = s6 o q c in
  let c = s7 o r c in
  c

(* Deserialize a tuple of seven elements using serialization functions for the
   elements. *)
let sei_prod7 s1 s2 s3 s4 s5 s6 s7 i c =
  let (m,c) = s1 i c in
  let (n,c) = s2 i c in
  let (k,c) = s3 i c in
  let (l,c) = s4 i c in
  let (p,c) = s5 i c in
  let (q,c) = s6 i c in
  let (r,c) = s7 i c in
  ((m,n,k,l,p,q,r),c)

(* Serialize a 32-bit integer in big-endian byte order directly into a string
   buffer. *)
(** specialized serialization functions for efficiency **)
(** put int32 x as 4 bytes into buffer bu **)
let seo_by_sb_int32 bu x = Buffer.add_string bu (Bebits.of_int32 x)
