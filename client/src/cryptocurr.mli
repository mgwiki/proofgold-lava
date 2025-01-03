(* Copyright (c) 2021-2025 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Most of this code is taken directly from Egal. *)

open Json
open Secp256k1
open Hash

val base58 : Z.t -> string
val frombase58 : string -> Z.t
val pfgwif : Z.t -> bool -> string
val btcwif : Z.t -> bool -> string
val ltcwif : Z.t -> bool -> string
val privkey_from_wif : string -> Z.t * bool
val privkey_from_btcwif : string -> Z.t * bool
val pubkey_hexstring : (Z.t * Z.t) -> bool -> string
val pubkey_bytelist : (Z.t * Z.t) -> bool -> int list
val hexstring_pubkey : string -> (Z.t * Z.t) * bool
val pubkey_hashval : Z.t * Z.t -> bool -> hashval
val pubkey_be160 : Z.t * Z.t -> bool -> Be160.t
val be160_from_addrstr : string -> Be160.t
val be160_btcaddrstr : Be160.t -> string
val payaddr_btcaddrstr : payaddr -> string
val payaddr_ltcaddrstr : payaddr -> string
val addr_pfgaddrstr : addr -> string
val pfgaddrstr_addr : string -> addr
val btcaddrstr_addr : string -> addr
val ltcaddrstr_addr : string -> addr
val bars_of_atoms : int64 -> string
val atoms_of_bars : string -> int64
val ltc_of_litoshis : int64 -> string
val litoshis_of_ltc : string -> int64

val addr_from_json : jsonval -> addr
val payaddr_from_json : jsonval -> payaddr
val atoms_from_json : jsonval -> int64
val bars_from_json : jsonval -> string
val json_bars : string -> jsonval
val json_atoms : int64 -> jsonval

exception InvalidBech32
val ltcbech32_be160 : string -> Be160.t
