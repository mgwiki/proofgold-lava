(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2021 The Proofgold Core developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash

exception NoBootstrapURL
val dbdir : string ref
val dbconfig : string -> unit

module type dbmtype = functor (M:sig type t val basedir : string val seival : (seist -> t * seist) val seoval : (t -> seosbt -> seosbt) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbget_opt : hashval -> M.t option
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
    val dbkeyiter : (hashval -> unit) -> unit
    val dbbincp : hashval -> Buffer.t -> unit
  end

module Dbmbasic : dbmtype

module DbBlacklist :
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> bool
    val dbexists : hashval -> bool
    val dbput : hashval -> bool -> unit
    val dbdelete : hashval -> unit
  end

module DbArchived :
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> bool
    val dbexists : hashval -> bool
    val dbput : hashval -> bool -> unit
    val dbdelete : hashval -> unit
  end
