(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Sha256

(* Most of the old ocaml of this code was taken directly from Egal,
   but almost all of it has been replaced. *)

(* Code for the Elliptic Curve secp256k1 *)
(* https://en.bitcoin.it/wiki/Secp256k1 *)

open Zarithint
   
let btc_to_z x = Z.of_bits (S2n.to_lebits x)
let z_to_btc x = S2n.of_lebits (Z.to_bits x)

let evenp k = Z.is_even k

(* _p : the 256 bit int prime in secp256k1 *)
let _p = big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007908834671663"

(* multiplicative inverse mod _n *)
let inv_mod_n x = btc_to_z (S2n.modinv_n (z_to_btc x))

(* multiplicative inverse mod _p *)
let inv_mod_p x = btc_to_z (S2n.modinv_p (z_to_btc x))

(* Intended to be points on the curve y^2 = x^3 + 7 *)
(* None is used for the zero point/point at infinity *)
type pt = (Z.t * Z.t) option

let btc_to_z_p = function
  | None -> None
  | Some (x, y) -> Some (btc_to_z x, btc_to_z y);;

(* Addition for points on the elliptic curve *)
(* p,q : points on the curve *)
(* return point p+q *)
let addp p q =
  match p, q with
  | (None,q) -> q
  | (p,None) -> p
  | (Some (x1,y1), Some(x2,y2)) ->
       let ge1 = Secp256k1btc.pt_of_xy (z_to_btc x1) (z_to_btc y1) in
       let ge2 = Secp256k1btc.pt_of_xy (z_to_btc x2) (z_to_btc y2) in
       btc_to_z_p (Secp256k1btc.pt_to_xyo (Secp256k1btc.add_pt ge1 ge2))

(* Scalar multiplication *)
(* k : Z.t *)
(* p : point p on the curve *)
(* return point k*p as a point *)
let smulp k = function
  | None -> None
  | Some (x, y) ->
     btc_to_z_p (Secp256k1btc.pt_to_xyo (Secp256k1btc.smulp (z_to_btc k) (Secp256k1btc.pt_of_xy (z_to_btc x) (z_to_btc y))))

(* base point _g *)
let _g = Some(big_int_of_string "55066263022277343669578718895168534326250603453777594175500187360389116729240",
	      big_int_of_string "32670510020758816978083085130507043184471273380659243275938904335757337482424")

(* _n : order of _g *)
let _n = big_int_of_string "115792089237316195423570985008687907852837564279074904382605163141518161494337"

let curve_y e x =
  match Secp256k1btc.pt_to_xyo (Secp256k1btc.curve_y (not e) (z_to_btc x)) with
  | None -> failwith "curve_y"
  | Some (_, y) -> btc_to_z y;;


let seo_pt o p c = seo_option (seo_prod seo_big_int_256 seo_big_int_256) o p c
let sei_pt i c = sei_option (sei_prod sei_big_int_256 sei_big_int_256) i c
