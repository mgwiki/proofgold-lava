(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Net
open Signat
open Ltcrpc
open Mathdata
open Tx
open Ctre
open Block

type swapmatchoffertype =
  | SimpleSwapMatchOffer of hashval * hashval * Be160.t * hashval * int64 * int64 * Be160.t * Be160.t * Be160.t * int

val swapmatchoffers : (float ref * swapmatchoffertype) list ref

val unconfswapredemptions : (hashval * int64 * stx) list ref

val swapmatchoffer_ltccontracttx : hashval -> Be160.t -> int64 -> string

val localpreferred : (hashval,unit) Hashtbl.t

val stxpoolfee : (hashval,int64) Hashtbl.t
val stxpooltm : (hashval,int64) Hashtbl.t
val stxpool : (hashval,stx) Hashtbl.t
val unconfirmed_spent_assets : (hashval,hashval) Hashtbl.t

val artificialledgerroot : hashval option ref
val artificialbestblock : (hashval * hashval * hashval) option ref

val delayed_headers : (hashval * hashval,Z.t -> unit) Hashtbl.t
val delayed_deltas : (hashval * hashval,hashval option -> hashval option -> Z.t -> unit) Hashtbl.t

val process_header : out_channel -> bool -> bool -> bool
  -> hashval * hashval -> hashval -> blockheader
  -> int64 -> stakemod -> targetinfo -> int64 -> int64 -> hashval -> int32 -> unit

val process_delta : out_channel -> bool -> bool -> bool -> bool
  -> hashval * hashval -> hashval -> block
    -> hashval option -> ttree option -> hashval option -> stree option
    -> int64 -> stakemod -> targetinfo -> int64 -> int64
    -> hashval -> int32
    -> unit

val process_block : out_channel -> bool -> bool -> bool -> bool
  -> hashval * hashval -> hashval -> block
    -> hashval option -> ttree option -> hashval option -> stree option
    -> int64 -> stakemod -> targetinfo -> int64 -> int64
    -> hashval -> int32
    -> unit

val initialize_pfg_from_ltc : out_channel -> hashval -> unit

val print_best_block : unit -> unit

val lookup_thytree : hashval option -> Mathdata.ttree option
val lookup_sigtree : hashval option -> Mathdata.stree option

val update_theories : hashval option -> Mathdata.ttree option -> Mathdata.ttree option -> unit
val update_signatures : hashval option -> Mathdata.stree option -> Mathdata.stree option -> unit

val publish_stx : hashval -> stx -> unit
val publish_block : int64 -> hashval -> block -> unit

val send_inv : int -> out_channel -> connstate -> unit

val dumpblocktreestate : out_channel -> unit

type consensuswarning =
  | ConsensusWarningMissing of hashval * hashval * hashval
  | ConsensusWarningBlacklist of hashval
  | ConsensusWarningInvalid of hashval
  | ConsensusWarningNoBurn of hashval
  | ConsensusWarningTerminal

val print_consensus_warning : out_channel -> consensuswarning -> unit

val get_burn : hashval -> hashval * hashval
val get_bestblock : unit -> (hashval * hashval * hashval) option * consensuswarning list
val get_bestblock2 : unit -> int64 * hashval
val get_bestblock_or_previous : unit -> (hashval * hashval * hashval) option
val get_bestblock_print_warnings : out_channel -> (hashval * hashval * hashval) option
val get_bestblock_cw_exception : exn -> hashval * hashval * hashval

val add_to_txpool : hashval -> Tx.stx -> unit
val remove_from_txpool : hashval -> unit
val savetxtopool_real : hashval -> stx -> unit

val recursively_invalidate_blocks : hashval -> unit
val recursively_revalidate_blocks : hashval -> unit

val reprocessblock : out_channel -> hashval -> hashval -> hashval -> unit

val ensure_sync : unit -> unit

val bestblocklist : (int64 * hashval * Z.t) list ref
