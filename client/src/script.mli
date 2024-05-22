(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json
open Sha256
open Hash
open Secp256k1
open Signat

val be160_bytelist : Be160.t -> int list
val be256_bytelist : Be256.t -> int list
val bytelist_string : int list -> string
val hash160_bytelist : int list -> p2shaddr
val sha256_bytelist : int list -> Be256.t

val next_bytes : int -> int list -> int list * int list
val bytelist_to_pt : int list -> pt
val push_bytes : int list -> int list
val pop_bytes : int list -> int list * int list
val blnum_le : Z.t -> int -> int list
val blnum_be : Z.t -> int -> int list

val verify_p2sh : int64 option -> Z.t -> p2shaddr -> int list -> bool * int64 option * int64 option

type gensignat =
  | P2pkhSignat of pt * bool * signat
  | P2shSignat of int list
  | EndP2pkhToP2pkhSignat of pt * bool * pt * bool * signat * signat
  | EndP2pkhToP2shSignat of pt * bool * Be160.t * signat * int list
  | EndP2shToP2pkhSignat of pt * bool * int list * signat
  | EndP2shToP2shSignat of Be160.t * int list * int list

val verify_gensignat : int64 option -> Z.t -> gensignat -> addr -> bool * int64 option * int64 option

val verify_gensignat2 : int64 option -> hashval -> Z.t -> gensignat -> addr -> bool * int64 option * int64 option

val seo_gensignat : (int -> int -> 'a -> 'a) -> gensignat -> 'a -> 'a
val sei_gensignat : (int -> 'a -> int * 'a) -> 'a -> gensignat * 'a

val json_gensignat : gensignat -> jsonval

val inum_be : int list -> Z.t
val inum_le : int list -> Z.t

val createatomicswapcsv : hashval -> Be160.t -> Be160.t -> int32 -> Be160.t * int list
val bountyfundveto : Be160.t -> Be160.t * int list
