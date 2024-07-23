(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json
open Hash
open Db
open Mathdata
open Logic
open Checking

type obligation = (payaddr * int64 * bool) option

type preasset =
  | Currency of int64
  | Bounty of int64
  | OwnsObj of hashval * payaddr * int64 option
  | OwnsProp of hashval * payaddr * int64 option
  | OwnsNegProp
  | RightsObj of hashval * int64
  | RightsProp of hashval * int64
  | Marker
  | TheoryPublication of payaddr * hashval * theoryspec
  | SignaPublication of payaddr * hashval * hashval option * signaspec
  | DocPublication of payaddr * hashval * hashval option * doc

val obligation_string : obligation -> string
val preasset_string : preasset -> string

(*** asset is (assetid,birthday,obligation,preasset) ***)
type asset = hashval * int64 * obligation * preasset

val assetid : asset -> hashval
val assetbday : asset -> int64
val assetobl : asset -> obligation
val assetpre : asset -> preasset

val hashobligation : obligation -> hashval option
val hashpreasset : preasset -> hashval
val hashasset : asset -> hashval

type addr_assetid = addr * hashval
type addr_preasset = addr * (obligation * preasset)
type addr_asset = addr * asset

val hash_addr_assetid : addr_assetid -> hashval
val hash_addr_preasset : addr_preasset -> hashval
val hash_addr_asset : addr_asset -> hashval

val new_assets : int64 -> addr -> addr_preasset list -> hashval -> int32 -> asset list
val remove_assets : asset list -> hashval list -> asset list
val get_spent : addr -> addr_assetid list -> hashval list
val add_vout : int64 -> hashval -> addr_preasset list -> int32 -> addr_asset list
val asset_value : int64 -> asset -> int64 option
val asset_value_sum : int64 -> asset list -> int64
val output_signaspec_uses_objs : addr_preasset list -> (hashval * hashval) list
val output_signaspec_uses_props : addr_preasset list -> (hashval * hashval) list
val output_doc_uses_objs : addr_preasset list -> (hashval * hashval) list
val output_doc_uses_props : addr_preasset list -> (hashval * hashval) list
val output_creates_objs : addr_preasset list -> (hashval option * hashval * hashval) list
val output_creates_props : addr_preasset list -> (hashval option * hashval) list
val output_creates_neg_props : addr_preasset list -> (hashval option * hashval) list
val rights_out_obj : addr_preasset list -> hashval -> int64
val rights_out_prop : addr_preasset list -> hashval -> int64
val count_obj_rights : asset list -> hashval -> int64
val count_prop_rights : asset list -> hashval -> int64
val count_rights_used : (hashval * hashval) list -> hashval -> int
val obj_rights_mentioned : addr_preasset list -> hashval list
val prop_rights_mentioned : addr_preasset list -> hashval list
val rights_mentioned : addr_preasset list -> hashval list
val units_sent_to_addr : addr -> addr_preasset list -> int64
val out_cost : addr_preasset list -> int64

val seo_obligation : (int -> int -> 'a -> 'a) -> obligation -> 'a -> 'a
val sei_obligation : (int -> 'a -> int * 'a) -> 'a -> obligation * 'a

val seo_preasset : (int -> int -> 'a -> 'a) -> preasset -> 'a -> 'a
val sei_preasset : (int -> 'a -> int * 'a) -> 'a -> preasset * 'a

val seo_asset : (int -> int -> 'a -> 'a) -> asset -> 'a -> 'a
val sei_asset : (int -> 'a -> int * 'a) -> 'a -> asset * 'a

val seo_addr_assetid : (int -> int -> 'a -> 'a) -> addr_assetid -> 'a -> 'a
val sei_addr_assetid : (int -> 'a -> int * 'a) -> 'a -> addr_assetid * 'a

val seo_addr_preasset : (int -> int -> 'a -> 'a) -> addr_preasset -> 'a -> 'a
val sei_addr_preasset : (int -> 'a -> int * 'a) -> 'a -> addr_preasset * 'a

val seo_addr_asset : (int -> int -> 'a -> 'a) -> addr_asset -> 'a -> 'a
val sei_addr_asset : (int -> 'a -> int * 'a) -> 'a -> addr_asset * 'a

module DbAsset :
    sig
      val dbinit : unit -> unit
      val dbget : hashval -> asset
      val dbexists : hashval -> bool
      val dbput : hashval -> asset -> unit
      val dbdelete : hashval -> unit
      val dbkeyiter : (hashval -> unit) -> unit
    end

module DbAssetIdAt :
    sig
      val dbinit : unit -> unit
      val dbget : hashval -> addr
      val dbexists : hashval -> bool
      val dbput : hashval -> addr -> unit
      val dbdelete : hashval -> unit
    end

val get_asset : hashval -> asset

val json_obligation : obligation -> jsonval option
val json_preasset : preasset -> jsonval
val json_asset : asset -> jsonval

val obligation_from_json : jsonval option -> obligation
val preasset_from_json : jsonval -> preasset
val asset_from_json : jsonval -> asset

val tx_count_recompute : int ref
val addr_count_recompute : int ref
val tx_count : int ref
val addr_count : int ref
val asset_id_hash_history : (hashval,hashval * hashval * hashval * hashval option) Hashtbl.t
val asset_id_hash_refreshing : bool ref
val asset_id_hash_table_bkp : (hashval,hashval * hashval * hashval option) Hashtbl.t
val asset_id_hash_table : (hashval,hashval * hashval * hashval option) Hashtbl.t
val addr_contents_history_table : (hashval,(addr * hashval)) Hashtbl.t
val addr_contents_table_bkp : (addr, hashval) Hashtbl.t
val addr_contents_table : (addr,hashval) Hashtbl.t
val block_txcount_history_table : (hashval,int) Hashtbl.t
val blockheight_history_table : (hashval,int64) Hashtbl.t
val spent_table_refreshing : bool ref
val spent_table_bkp : (hashval,(hashval * hashval * hashval option * int64)) Hashtbl.t
val spent_table : (hashval,(hashval * hashval * hashval option * int64)) Hashtbl.t
val spent_history_table : (hashval,((hashval * hashval * hashval option) list * hashval option)) Hashtbl.t
val bounty_sorted_refreshing : bool ref
val bounty_sorted_bkp : (int64 * addr * hashval * int64 * hashval * hashval option) list ref
val bounty_sorted : (int64 * addr * hashval * int64 * hashval * hashval option) list ref
val placed_bounty_sorted : (int64 * addr * hashval * int64 * hashval * hashval option) list ref
val collected_bounty_sorted : (int64 * hashval * hashval option * int64 * addr * hashval * int64 * hashval * hashval option) list ref
val sig_table_bkp : (addr, (payaddr * hashval option * hashval)) Hashtbl.t
val doc_table_bkp : (addr, (payaddr * hashval option * hashval)) Hashtbl.t
val sig_table : (addr, (payaddr * hashval option * hashval)) Hashtbl.t
val doc_table : (addr, (payaddr * hashval option * hashval)) Hashtbl.t
val sig_history_table : (hashval, (addr * payaddr * hashval option * hashval)) Hashtbl.t
val doc_history_table : (hashval, (addr * payaddr * hashval option * hashval)) Hashtbl.t
val bounty_sum : int64 ref
val open_bounty_sum : int64 ref
val bounty_history_table : (hashval,(int64 * addr * hashval * int64 * hashval * hashval option)) Hashtbl.t
val theory_history_table : (hashval,(hashval * hashval * addr * payaddr)) Hashtbl.t
val theory_info : (hashval, hashval * addr * payaddr) Hashtbl.t
val theory_info_bkp : (hashval, hashval * addr * payaddr) Hashtbl.t
val term_info_refreshing : bool ref
val term_info_bkp : (hashval,trm * hashval * hashval option * hashval * hashval option * bool * hashval) Hashtbl.t
val term_info : (hashval,trm * hashval * hashval option * hashval * hashval option * bool * hashval) Hashtbl.t
val term_info_hf : (hashval,trm) Hashtbl.t
val obj_info_bkp : (hashval,hashval option * stp * hashval * trm * bool * addr) Hashtbl.t
val obj_info : (hashval,hashval option * stp * hashval * trm * bool * addr) Hashtbl.t
val obj_info_hf : (hashval,stp * hashval * trm) Hashtbl.t
val prop_info_bkp : (hashval,hashval option * hashval * trm * bool * addr) Hashtbl.t
val prop_info : (hashval,hashval option * hashval * trm * bool * addr) Hashtbl.t
val prop_info_hf : (hashval,hashval * trm) Hashtbl.t
val negprop_info_bkp : (hashval,hashval option * hashval * bool) Hashtbl.t
val negprop_info : (hashval,hashval option * hashval * bool) Hashtbl.t
val term_history_table : (hashval,hashval * trm * hashval * hashval option * hashval * hashval option * bool * hashval) Hashtbl.t
val term_history_table : (hashval,hashval * trm * hashval * hashval option * hashval * hashval option * bool * hashval) Hashtbl.t
val obj_history_table : (hashval,hashval * hashval option * stp * hashval * trm * bool * addr) Hashtbl.t
val prop_history_table : (hashval,hashval * hashval option * hashval * trm * bool * addr) Hashtbl.t
val ownsobj_history_table : (hashval,hashval * hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val ownsprop_history_table : (hashval,hashval * hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val ownsnegprop_history_table : (hashval,addr * hashval * int64 * payaddr) Hashtbl.t
val created_obj_info : (hashval, hashval * int64 * payaddr) Hashtbl.t
val created_obj_info_bkp : (hashval, hashval * int64 * payaddr) Hashtbl.t
val owns_obj_info : (hashval, hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val owns_obj_info_bkp : (hashval, hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val created_prop_info : (hashval, hashval * int64 * payaddr) Hashtbl.t
val created_prop_info_bkp : (hashval, hashval * int64 * payaddr) Hashtbl.t
val owns_prop_info : (hashval, hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val owns_prop_info_bkp : (hashval, hashval * int64 * payaddr * payaddr * int64 option) Hashtbl.t
val created_negprop_info : (addr, hashval * int64 * payaddr) Hashtbl.t
val created_negprop_info_bkp : (addr, hashval * int64 * payaddr) Hashtbl.t
val owns_negprop_info : (addr, hashval * int64 * payaddr) Hashtbl.t
val owns_negprop_info_bkp : (addr, hashval * int64 * payaddr) Hashtbl.t
