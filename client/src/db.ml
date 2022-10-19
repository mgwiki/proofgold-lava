(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash

let dbdir = ref ""

exception NoBootstrapURL

let dbconfig dir =
  dbdir := dir;
  if Sys.file_exists dir then
    if Sys.is_directory dir then
      ()
    else
      raise (Failure (dir ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir dir 0b111111000;
      Utils.forward_from_ltc_block := Some("26c874bca3122a06ec9b6582d4b62f38cfbf9a490da15698fe9a33c7d5a35cde")
    end

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
                            
module Dbmbasic : dbmtype = functor (M:sig type t val basedir : string val seival : (seist -> t * seist) val seoval : (t -> seosbt -> seosbt) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let db1 = ref None
            
    let dbinit () =
      let d2 = Filename.concat !dbdir M.basedir in
      if Sys.file_exists d2 then
        (if not (Sys.is_directory d2) then raise (Failure (d2 ^ " is a file not a directory")))
      else
        Unix.mkdir d2 0b111111000;
      let d2b = Filename.concat d2 "db4" in
      db1 := Some(Mlgdbm.dbopen (d2b ^ ".pag"))

    let dbf () =
      match !db1 with
      | Some(db) ->
         db
      | None ->
         let d2b = Filename.concat (Filename.concat !dbdir M.basedir) "db4" in
         let db = Mlgdbm.dbopen (d2b ^ ".pag") in
         db1 := Some(db);
         db

    let dbexists k =
      let k = Be256.to_string k in
      Mlgdbm.exists (dbf ()) k

    let dbget k =
      let k = Be256.to_string k in
      ((Mlgdbm.find_unmarshal (dbf ()) k) : M.t)

    let dbget_opt k =
      let k = Be256.to_string k in
      ((Mlgdbm.find_unmarshal_opt (dbf ()) k) : M.t option)

    let dbput k v =
      let k = Be256.to_string k in
      withlock
        (fun () ->
          let s = Marshal.to_string v [Marshal.No_sharing;Marshal.Compat_32] in
          Mlgdbm.replace (dbf()) k s)

    let dbdelete k =
      let k = Be256.to_string k in
      withlock
        (fun () -> Mlgdbm.delete (dbf ()) k)

    let dbkeyiter f =
      let db = dbf () in
      let rec walk = function
	| None -> ()
	| Some k ->
           f (Be256.of_substring k 0);
           walk (try Some (Mlgdbm.nextkey db k) with Not_found -> None)
      in
      walk (try Some(Mlgdbm.firstkey db) with Not_found -> None)

    let dbbincp k sb =
      let k = Be256.to_string k in
      let s = Mlgdbm.find (dbf ()) k in
      Buffer.add_string sb s

  end

module DbBlacklist = Dbmbasic (struct type t = bool let basedir = "blacklist" let seival = sei_bool seis let seoval = seo_bool seosb end)

module DbArchived = Dbmbasic (struct type t = bool let basedir = "archived" let seival = sei_bool seis let seoval = seo_bool seosb end)
