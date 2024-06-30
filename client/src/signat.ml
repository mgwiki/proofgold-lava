(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* This code implements digital signatures for Qeditas, a cryptocurrency. *)

open Zarithint
open Ser
open Sha256
open Hash
open Secp256k1
open Cryptocurr

(* Constant representing the value 255 as a big integer. *)
let z255 = big_int_of_int 255

(* Type definition for a signature, consisting of two big integers. *)
type signat = Z.t * Z.t

(* Converts a list of bytes to a big integer. *)
let rec bytelist_to_big_int rst n c =
  if n > 0 then
    match rst with
    | (b::rst2) -> bytelist_to_big_int rst2 (n-1) (or_big_int (shift_left_big_int (big_int_of_int b) ((n-1)*8)) c)
    | [] -> raise (Failure("not enough bytes"))
  else
    (c,rst)

(* Decodes a signature from a base64-encoded string. *)
let decode_signature_real sg =
  match Utils.base64decode sg with
  | (by0::rst) ->
      let (r,rst2) = bytelist_to_big_int rst 32 zero_big_int in
      let (s,rst3) = bytelist_to_big_int rst2 32 zero_big_int in
      if rst3 = [] then
	(by0,(r,s))
      else
	raise (Failure("Signature Too Long"))
  | [] -> raise (Failure("Empty Signature"))

(* Decodes a signature and returns its components. *)
let decode_signature sg =
  let (by0,(r,s)) = decode_signature_real sg in
  let by27 = by0-27 in
  let recid = by27 land 3 in
  let fcomp = by27 land 4 > 0 in
  (recid,fcomp,(r,s))

(* Converts a big integer to a list of bytes. *)
let rec big_int_to_bytelist r l bl =
  if l > 0 then
    big_int_to_bytelist (shift_right_towards_zero_big_int r 8) (l-1) (int_of_big_int (and_big_int r z255)::bl)
  else
    bl

(* Encodes a signature as a base64-encoded string. *)
let encode_signature recid fcomp (r,s) =
  let by0 = 27 + if fcomp then 4 lor recid else recid in
  Utils.base64encode (by0::big_int_to_bytelist r 32 []@big_int_to_bytelist s 32 [])

(* Exception indicating that a value is zero. *)
exception ZeroValue

(* Generates a signature for a given message hash, private key, and random number. *)
let signat_big_int e privk randk =
  match smulp randk _g with
  | Some(xr,yr) ->
      let r = mod_big_int xr _n in
      if r = zero_big_int then raise ZeroValue;
      let s = mod_big_int (mult_big_int (inv_mod_n randk) (add_big_int e (mult_big_int r privk))) _n in
      if s = zero_big_int then raise ZeroValue;
      (r,s)
  | None -> raise ZeroValue

(* Verifies a signature for a given message hash, public key, and signature. *)
let verify_signed_big_int e q (r,s) =
  if lt_big_int r _n && lt_big_int s _n && lt_big_int e _p then
    let sinv = inv_mod_n s in
    let u1 = mod_big_int (mult_big_int e sinv) _n in
    let u2 = mod_big_int (mult_big_int r sinv) _n in
    match addp (smulp u1 _g) (smulp u2 q) with
    | None -> false
    | Some(xr,yr) -> eq_big_int (mod_big_int xr _n) r
  else
    false

(* Generates a signature for a given message hash, private key, and random number. *)
let signat_hashval h privk randk = signat_big_int (hashval_big_int h) privk randk

(* Verifies a signature for a given message hash, public key, and signature. *)
let verify_signed_hashval h q (r,s) = verify_signed_big_int (hashval_big_int h) q (r,s)

(* Constant representing the negative of the generator point on the secp256k1 curve. *)
let _minusg = Some(big_int_of_string "55066263022277343669578718895168534326250603453777594175500187360389116729240",
		 big_int_of_string "83121579216557378445487899878180864668798711284981320763518679672151497189239")

(* Recovers a public key from a signature, message hash, and recovery ID. *)
let recover_key e (r,s) recid =
  let xr = if recid > 1 then mod_big_int (add_big_int r _n) _p else r in
  let yr = curve_y (recid mod 2 = 0) xr in
  let rinv = inv_mod_n r in
  smulp rinv (addp (smulp s (Some(xr,yr))) (smulp e _minusg))

(* Verifies a signature for a given message hash, address, and signature. *)
let verify_p2pkhaddr_signat e alpha (r,s) recid fcomp =
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_be160 q fcomp = alpha
  | None -> false

(* Verifies a signature for a given message, address, and signature. *)
let verifymessage alpha recid fcomp (r,s) m =
  let e = hashval_big_int (sha256dstr m) in
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_be160 q fcomp = alpha
  | None -> false

(* Verifies a signature for a given message, address, and signature, and returns the recovered public key if the signature is valid. *)
let verifymessage_recover alpha recid fcomp (r,s) m =
  let e = hashval_big_int (sha256dstr m) in
  match recover_key e (r,s) recid with
  | Some(q) when pubkey_be160 q fcomp = alpha -> Some(q)
  | _ -> None

(* Calculates the hash value of a Bitcoin message. *)
let hashval_of_bitcoin_message m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  sha256dstr_hashval (Buffer.contents ms)

(* Verifies a signature for a given Bitcoin message, address, and signature. *)
let verifybitcoinmessage alpha recid fcomp (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage alpha recid fcomp (r,s) (Buffer.contents ms)

(* Verifies a signature for a given Bitcoin message, address, and signature, and returns the recovered public key if the signature is valid. *)
let verifybitcoinmessage_recover alpha recid fcomp (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage_recover alpha recid fcomp (r,s) (Buffer.contents ms)

(* Calculates the hash value of a Proofgold message. *)
let hashval_of_proofgold_message m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Proofgold Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  sha256str_hashval (Buffer.contents ms)

(* Verifies a signature for a given Proofgold message and public key. *)
let verifyproofgoldmessage q (r,s) m =
  let mh = hashval_of_proofgold_message m in
  let e = hashval_big_int mh in
  verify_signed_big_int e q (r,s)

(* Generates a signature for a given Proofgold message and private key. *)
let sign_proofgold_message m privk randk =
  let h = hashval_of_proofgold_message m in
  signat_hashval h privk randk

(* Repeatedly calls a function with a randomly generated number until the function returns a non-zero value. *)
let rec repeat_rand f r =
  try
    let randk = r() in
    (randk,f randk)
  with ZeroValue -> repeat_rand f r

(* Serializes a signature to a byte stream. *)
let seo_signat o rs c = seo_prod seo_big_int_256 seo_big_int_256 o rs c

(* Deserializes a signature from a byte stream. *)
let sei_signat i c = sei_prod sei_big_int_256 sei_big_int_256 i c

(* Calculates the hash value of a signature. *)
let hashsignat (r,s) = hashpair (big_int_hashval r) (big_int_hashval s)
