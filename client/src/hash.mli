(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold Core developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json
open Sha256

type hashval = Be256.t
val zerohashval : hashval

type addr = int * Be160.t
type p2pkhaddr = Be160.t
type p2shaddr = Be160.t
type payaddr = bool * Be160.t
type termaddr = Be160.t
type pubaddr = Be160.t

val hash160 : string -> Be160.t

val p2pkhaddr_payaddr : p2pkhaddr -> payaddr
val p2shaddr_payaddr : p2shaddr -> payaddr

val p2pkhaddr_addr : p2pkhaddr -> addr
val p2shaddr_addr : p2shaddr -> addr
val payaddr_addr : payaddr -> addr
val termaddr_addr : termaddr -> addr
val pubaddr_addr : pubaddr -> addr

val payaddr_p : addr -> bool
val p2pkhaddr_p : addr -> bool
val p2shaddr_p : addr -> bool
val termaddr_p : addr -> bool
val pubaddr_p : addr -> bool

val hashval_bitseq : hashval -> bool list
val bitseq_hashval : bool list -> hashval
val bytelist_be160 : int list -> Be160.t
val bytelist_be256 : int list -> Be256.t
val be256_bytelist : Be256.t -> int list
val hashval_be160 : hashval -> Be160.t
val hashval_p2pkh_payaddr : hashval -> payaddr
val hashval_p2sh_payaddr : hashval -> payaddr
val be160_p2pkh_addr : Be160.t -> addr
val hashval_p2pkh_addr : hashval -> addr
val be160_p2sh_addr : Be160.t -> addr
val hashval_p2sh_addr : hashval -> addr
val hashval_term_addr : hashval -> addr
val hashval_pub_addr : hashval -> addr

val addr_bitseq : addr -> bool list
val bitseq_addr : bool list -> addr

val addr_bitlist : addr -> Bitlist.t
val bitlist_addr : Bitlist.t -> addr

val hashval_int32p8 : hashval -> int32p8
val int32p8_hashval : int32p8 -> hashval
val hashval_hexstring : hashval -> string
val hexstring_hashval : string -> hashval

val sha256str_hashval : string -> hashval
val sha256dstr_hashval : string -> hashval
  
val printhashval : hashval -> unit
val hashint32 : int32 -> hashval
val hashint64 : int64 -> hashval
val hashaddr : addr -> hashval
val hashpayaddr : payaddr -> hashval
val hashtermaddr : termaddr -> hashval
val hashpubaddr : pubaddr -> hashval
val hashpair : hashval -> hashval -> hashval
val hashpubkey : Be256.t -> Be256.t -> hashval
val hashpubkeyc : int -> Be256.t -> hashval
val hashtag : hashval -> int32 -> hashval
val hashlist : hashval list -> hashval
val ohashlist : hashval list -> hashval option
val hashopair : hashval option -> hashval option -> hashval option
val hashopair1 : hashval -> hashval option -> hashval
val hashopair2 : hashval option -> hashval -> hashval

val be256_big_int : Be256.t -> Z.t
val big_int_be256 : Z.t -> Be256.t
val hashval_big_int : hashval -> Z.t
val big_int_hashval : Z.t -> hashval

val seo_be160 : (int -> int -> 'a -> 'a) -> Be160.t -> 'a -> 'a
val seosb_be160 : Be160.t -> Ser.seosbt -> Ser.seosbt
val sei_be160 : (int -> 'a -> int * 'a) -> 'a -> Be160.t * 'a
val seo_be256 : (int -> int -> 'a -> 'a) -> Be256.t -> 'a -> 'a
val seosb_be256 : Be256.t -> Ser.seosbt -> Ser.seosbt
val seoc_be256 : Be256.t -> Ser.seoct -> Ser.seoct
val sei_be256 : (int -> 'a -> int * 'a) -> 'a -> Be256.t * 'a
val seis_be256 : Ser.seist -> Be256.t * Ser.seist
val seic_be256 : Ser.seict -> Be256.t * Ser.seict
val seo_hashval : (int -> int -> 'a -> 'a) -> hashval -> 'a -> 'a
val seosb_hashval : hashval -> Ser.seosbt -> Ser.seosbt
val seoc_hashval : hashval -> Ser.seoct -> Ser.seoct
val sei_hashval : (int -> 'a -> int * 'a) -> 'a -> hashval * 'a
val seis_hashval : Ser.seist -> hashval * Ser.seist
val seic_hashval : Ser.seict -> hashval * Ser.seict
val seo_addr : (int -> int -> 'a -> 'a) -> addr -> 'a -> 'a
val sei_addr : (int -> 'a -> int * 'a) -> 'a -> addr * 'a
val seo_payaddr : (int -> int -> 'a -> 'a) -> payaddr -> 'a -> 'a
val sei_payaddr : (int -> 'a -> int * 'a) -> 'a -> payaddr * 'a
val seo_termaddr : (int -> int -> 'a -> 'a) -> termaddr -> 'a -> 'a
val sei_termaddr : (int -> 'a -> int * 'a) -> 'a -> termaddr * 'a
val seo_pubaddr : (int -> int -> 'a -> 'a) -> pubaddr -> 'a -> 'a
val sei_pubaddr : (int -> 'a -> int * 'a) -> 'a -> pubaddr * 'a

val merkle_root : hashval list -> hashval option

val hashval_rev : hashval -> hashval

val hashval_from_json : jsonval -> hashval

val bountyfund : p2pkhaddr

val addr_get_bit : addr -> int -> bool

val pow_finalstep : hashval -> Z.t
