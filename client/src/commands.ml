(* Copyright (c) 2021-2023 The Proofgold Lava developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json
open Zarithint
open Config
open Hashaux
open Ser
open Sha256
open Hash
open Net
open Cryptocurr
open Signat
open Ltcrpc
open Script
open Mathdata
open Assets
open Tx
open Ctre
open Block
open Blocktree

let walletkeys_staking = ref []
let walletkeys_nonstaking = ref []
let walletkeys_staking_fresh = ref []
let walletkeys_nonstaking_fresh = ref []
let walletp2shs = ref []
let walletendorsements = ref []
let walletwatchaddrs = ref []
let walletwatchaddrs_offlinekey = ref []
let walletwatchaddrs_offlinekey_fresh = ref []
let stakingassets = ref []

let atoms_balances_in_ledger : (hashval,int64 * int64 * int64 * int64 * int64 * int64 * int64 * int64) Hashtbl.t = Hashtbl.create 100
let spendable_assets_in_ledger : (hashval,(addr * asset * int64) list) Hashtbl.t = Hashtbl.create 100

let load_txpooltm () =
  let fn = Filename.concat (datadir()) "txpooltm" in
  let tmminusweek = Int64.sub (Int64.of_float (Unix.time())) 604800L in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txtm,txid),_) = sei_prod sei_int64 sei_hashval seic (ch,None) in
	if txtm > tmminusweek then
	  Hashtbl.add stxpooltm txid txtm
      done
    with
    | End_of_file -> close_in_noerr ch
    | exc ->
	Printf.printf "Problem in txpooltm file: %s\n" (Printexc.to_string exc);
	close_in_noerr ch;;

let load_txpoolfees () =
  let fn = Filename.concat (datadir()) "txpoolfees" in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txid,fee),_) = sei_prod sei_hashval sei_int64 seic (ch,None) in
        Hashtbl.add stxpoolfee txid fee
      done
    with
    | End_of_file -> close_in_noerr ch
    | exc ->
	Printf.printf "Problem in txpoolfees file: %s\n" (Printexc.to_string exc);
	close_in_noerr ch;;

let load_txpool () =
  load_txpooltm();
  load_txpoolfees();
  let fn = Filename.concat (datadir()) "txpool" in
  if Sys.file_exists fn then
    let ch = open_in_bin fn in
    try
      while true do
	let ((txid,stau),_) = sei_prod sei_hashval Tx.sei_stx seic (ch,None) in
	if Hashtbl.mem stxpooltm txid && not (Hashtbl.mem stxpool txid) then
	  add_to_txpool txid stau
      done
    with
    | End_of_file -> close_in_noerr ch
    | exc ->
	Printf.printf "Problem in txpool file: %s\n" (Printexc.to_string exc);
	close_in_noerr ch;;

let save_txpool () =
  let fn = Filename.concat (datadir()) "txpool" in
  let fn2 = Filename.concat (datadir()) "txpoolfees" in
  let ch = open_out_bin fn in
  let ch2 = open_out_bin fn2 in
  Hashtbl.iter
    (fun txid stau ->
      seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,stau) (ch,None));
      try
        let fee = Hashtbl.find stxpoolfee txid in
        seocf (seo_prod seo_hashval seo_int64 seoc (txid,fee) (ch2,None))
      with Not_found -> ())
    stxpool;
  close_out_noerr ch;
  close_out_noerr ch2;;

let swapselloffers = ref []
let swapredemptions = ref []
                         
let load_swaps () =
  let dup : (hashval,unit) Hashtbl.t = Hashtbl.create 10 in
  let load_swaps_a swapfn =
    if Sys.file_exists swapfn then
      begin
        let s = open_in_bin swapfn in
        try
          while true do
	    let by = input_byte s in
            if by = 0 then
              begin
                let ((h,lbeta,pbeta,atoms,litoshis),_) =
                  sei_prod5 sei_hashval sei_string sei_be160 sei_int64 sei_int64 seic (s,None)
                in
                if not (Hashtbl.mem dup h) then
                  begin
                    Hashtbl.add dup h ();
                    let price = Int64.to_float litoshis *. 1000.0 /. Int64.to_float atoms in
                    let pbeta = (0,pbeta) in
                    swapbuyoffers := List.merge (fun (_,p1,_) (_,p2,_) -> compare p2 p1) [(h,price,SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis))] !swapbuyoffers;
                  end
              end
            else if by = 1 then
              begin
                let ((lalpha,pr64,minatoms,maxatoms),_) =
                  sei_prod4 sei_string sei_int64 sei_int64 sei_int64 seic (s,None)
                in
                let pr = float_of_string (bars_of_atoms pr64) in
                if pr > 0.00001 && List.mem lalpha !Config.ltctradeaddresses && not (List.exists (fun (lalpha2,_,minatoms2,maxatoms2) -> (lalpha2,minatoms2,maxatoms2) = (lalpha,minatoms,maxatoms)) !swapselloffers) then
                  swapselloffers := List.merge (fun (_,p1,_,_) (_,p2,_,_) -> compare p1 p2) [(lalpha,pr,minatoms,maxatoms)] !swapselloffers
              end
            else if by = 2 then
              begin
                let (((pfgtxid,ltctxid,caddr,caid),(atms,litoshis,alphal,alphap,betap,ltcfee)),_) =
                  sei_prod
                    (sei_prod4 sei_hashval sei_hashval sei_be160 sei_hashval)
                    (sei_prod6 sei_int64 sei_int64 sei_be160 sei_be160 sei_be160 sei_varintb)
                    seic (s,None)
                in
                if not (List.exists (fun (_,smo) -> match smo with SimpleSwapMatchOffer(pfgtxid2,_,_,_,_,_,_,_,_,_) -> pfgtxid2 = pfgtxid) !swapmatchoffers) then
                  let ctm = ref (Unix.time()) in
                  swapmatchoffers := (ctm,SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,ltcfee)) :: !swapmatchoffers
              end
            else if by = 3 then
              begin
                let ((ltctxid,caddr,caid,betap,alphap),_) =
                  sei_prod5 sei_hashval sei_be160 sei_hashval sei_be160 sei_be160
                            seic (s,None)
                in
                if not (List.exists (fun (ltctxid2,caddr2,caid2,_,_) -> ltctxid = ltctxid2 && caddr = caddr2 && caid = caid2) !swapredemptions) then
                  swapredemptions := (ltctxid,caddr,caid,betap,alphap)::!swapredemptions
              end
            else if by = 4 then
              begin
                let ((txid,byh,stau),_) = sei_prod3 sei_hashval sei_int64 sei_stx seic (s,None) in
                if not (List.exists (fun (txid2,_,_) -> txid = txid2) !unconfswapredemptions) then
                  unconfswapredemptions := (txid,byh,stau) :: !unconfswapredemptions
              end
          done
        with
        | End_of_file -> close_in_noerr s
        | e ->
	   Printf.printf "Warning: %s\nIgnoring the rest of the wallet file.\n" (Printexc.to_string e); flush stdout;
	   close_in_noerr s
      end
  in
  load_swaps_a (Filename.concat (datadir()) "swaps");
  load_swaps_a (Filename.concat (datadir()) "swapsbkp")

let save_swaps bkp =
  let swapfn = Filename.concat (datadir()) "swaps" in
  if bkp then
    begin
      let bkpswapfn = Filename.concat (datadir()) "swapsbkp" in
      if Sys.file_exists swapfn then Sys.rename swapfn bkpswapfn
    end
  else
    begin
      let bkpswapfn = Filename.concat (datadir()) "swapsbkp" in
      if Sys.file_exists swapfn then Sys.remove swapfn;
      if Sys.file_exists bkpswapfn then Sys.remove bkpswapfn
    end;
  let s = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o600 swapfn in
  try
    List.iter
      (fun (h,_,sbo) ->
        match sbo with
        | SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis) ->
           output_byte s 0;
           let (_,bs) = pbeta in
           seocf (seo_prod5 seo_hashval seo_string seo_be160 seo_int64 seo_int64 seoc (h,lbeta,bs,atoms,litoshis) (s,None)))
      !swapbuyoffers;
    List.iter
      (fun (lalpha,pr,minatoms,maxatoms) ->
        let pr64 = atoms_of_bars (Printf.sprintf "%f" pr) in
        output_byte s 1;
        seocf (seo_prod4 seo_string seo_int64 seo_int64 seo_int64 seoc (lalpha,pr64,minatoms,maxatoms) (s,None)))
      !swapselloffers;
    List.iter
      (fun (_,smo) ->
        match smo with
        | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,ltcfee) ->
           output_byte s 2;
           seocf (seo_prod
                    (seo_prod4 seo_hashval seo_hashval seo_be160 seo_hashval)
                    (seo_prod6 seo_int64 seo_int64 seo_be160 seo_be160 seo_be160 seo_varintb)
                    seoc
                    ((pfgtxid,ltctxid,caddr,caid),(atms,litoshis,alphal,alphap,betap,ltcfee))
                    (s,None)))
      !swapmatchoffers;
    List.iter
      (fun (ltccontracttxid,caddr,caid,betap,alphap) ->
        output_byte s 3;
        seocf (seo_prod5 seo_hashval seo_be160 seo_hashval seo_be160 seo_be160 seoc
                 (ltccontracttxid,caddr,caid,betap,alphap)
                 (s,None)))
      !swapredemptions;
    List.iter
      (fun (txid,byh,stau) ->
        output_byte s 4;
        seocf (seo_prod3 seo_hashval seo_int64 seo_stx seoc
                 (txid,byh,stau)
                 (s,None)))
      !unconfswapredemptions;
    close_out_noerr s
  with _ ->
    close_out_noerr s

let load_wallet () =
  let wallfn = Filename.concat (datadir()) "wallet" in
  if not (Sys.file_exists wallfn) then
    begin
      walletkeys_staking := [];
      walletkeys_nonstaking := [];
      walletkeys_staking_fresh := [];
      walletkeys_nonstaking_fresh := [];
      walletp2shs := [];
      walletendorsements := [];
      walletwatchaddrs := [];
      walletwatchaddrs_offlinekey := [];
      walletwatchaddrs_offlinekey_fresh := []
    end
  else
    let s = open_in_bin wallfn in
    try
      while true do
	let by = input_byte s in
	match by with
	| 0 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_staking :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_staking
	| 4 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_nonstaking :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_nonstaking
	| 5 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_staking_fresh :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_staking_fresh
	| 6 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_nonstaking_fresh :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_nonstaking_fresh
	| 1 ->
	    let (scr,_) = sei_list sei_int8 seic (s,None) in
	    walletp2shs :=
	      (let h = hash160_bytelist scr in
	      let a = addr_pfgaddrstr (p2shaddr_addr h) in
	      (h,a,scr))::!walletp2shs
	| 2 ->
	    let (endors,_) = sei_prod6 sei_payaddr sei_payaddr (sei_prod sei_big_int_256 sei_big_int_256) sei_varintb sei_bool sei_signat seic (s,None) in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
	    walletendorsements := endors::!walletendorsements
	| 3 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs := watchaddr::!walletwatchaddrs
	| 7 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs_offlinekey := watchaddr::!walletwatchaddrs_offlinekey
	| 8 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs_offlinekey_fresh := watchaddr::!walletwatchaddrs_offlinekey_fresh
	| _ ->
	    raise (Failure "Bad entry in wallet file")
      done
    with
    | End_of_file -> close_in_noerr s
    | Failure(x) ->
	Printf.printf "Warning: %s\nIgnoring the rest of the wallet file.\n" x; flush stdout;
	close_in_noerr s

let save_wallet () =
  let bkpwalldir =
    let bkpwalldir = Filename.concat (datadir()) "walletbkps" in
    if Sys.file_exists bkpwalldir then
      if Sys.is_directory bkpwalldir then
	bkpwalldir
      else
	datadir() (** in case a nondirectory is named "walletbkps" just put the backup files in the top level directory **)
    else
      begin
	Unix.mkdir bkpwalldir 0b111111000;
	bkpwalldir
      end
  in
  let currtm = Int64.of_float (Unix.time()) in
  let bkpwallfn = Filename.concat bkpwalldir (Printf.sprintf "walletbkp%Ld" currtm) in
  let wallfn = Filename.concat (datadir()) "wallet" in
  if Sys.file_exists wallfn then Sys.rename wallfn bkpwallfn;
  let s = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o600 wallfn in
  try
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 0;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_staking;
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 4;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_nonstaking;
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 5;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_staking_fresh;
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 6;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_nonstaking_fresh;
    List.iter
      (fun (_,_,scr) ->
	output_byte s 1;
	seocf (seo_list seo_int8 seoc scr (s,None)))
      !walletp2shs;
    List.iter
      (fun endors ->
	output_byte s 2;
	seocf (seo_prod6 seo_payaddr seo_payaddr (seo_prod seo_big_int_256 seo_big_int_256) seo_varintb seo_bool seo_signat seoc endors (s,None)))
      !walletendorsements;
    List.iter
      (fun watchaddr ->
	output_byte s 3;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs;
    List.iter
      (fun watchaddr ->
	output_byte s 7;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs_offlinekey;
    List.iter
      (fun watchaddr ->
	output_byte s 8;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs_offlinekey_fresh;
    close_out_noerr s;
    if not (Int64.logand currtm 127L = 0L) then Sys.remove bkpwallfn (* now that the wallet file has successfully updated, delete the backup, except about 1% of the time *)
  with e ->
    Utils.log_string (Printf.sprintf "exception during save_wallet: %s\n" (Printexc.to_string e));
    close_out_noerr s

let filter_wallet lr =
  let bkpwalldir =
    let bkpwalldir = Filename.concat (datadir()) "walletbkps" in
    if Sys.file_exists bkpwalldir then
      if Sys.is_directory bkpwalldir then
	bkpwalldir
      else
	datadir() (** in case a nondirectory is named "walletbkps" just put the backup files in the top level directory **)
    else
      begin
	Unix.mkdir bkpwalldir 0b111111000;
	bkpwalldir
      end
  in
  let currtm = Int64.of_float (Unix.time()) in
  let bkpwallfn = Filename.concat bkpwalldir (Printf.sprintf "walletbkp%Ld" currtm) in
  let wallfn = Filename.concat (datadir()) "wallet" in
  if Sys.file_exists wallfn then Sys.rename wallfn bkpwallfn;
  let s = open_out_bin wallfn in
  try
    let ws = ref [] in
    let wns = ref [] in
    List.iter
      (fun ((k,b,_,_,alpha1,_) as x) ->
        try
          if not (ctree_lookup_addr_assets true false (CHash(lr)) (0,(p2pkhaddr_addr alpha1)) = HNil) then
            begin
              ws := x::!ws;
	      output_byte s 0;
	      seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None))
            end
        with _ ->
          begin
            ws := x::!ws;
	    output_byte s 0;
	    seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None))
          end)
      !walletkeys_staking;
    walletkeys_staking := !ws;
    List.iter
      (fun ((k,b,_,_,alpha1,_) as x) ->
        try
          if not (ctree_lookup_addr_assets true false (CHash(lr)) (0,(p2pkhaddr_addr alpha1)) = HNil) then
            begin
              wns := x::!wns;
	      output_byte s 4;
	      seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None))
            end
        with _ ->
          begin
            wns := x::!wns;
	    output_byte s 4;
	    seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None))
          end)
      !walletkeys_nonstaking;
    walletkeys_nonstaking := !wns;
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 5;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_staking_fresh;
    List.iter
      (fun (k,b,_,_,_,_) ->
	output_byte s 6;
	seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)))
      !walletkeys_nonstaking_fresh;
    List.iter
      (fun (_,_,scr) ->
	output_byte s 1;
	seocf (seo_list seo_int8 seoc scr (s,None)))
      !walletp2shs;
    List.iter
      (fun endors ->
	output_byte s 2;
	seocf (seo_prod6 seo_payaddr seo_payaddr (seo_prod seo_big_int_256 seo_big_int_256) seo_varintb seo_bool seo_signat seoc endors (s,None)))
      !walletendorsements;
    List.iter
      (fun watchaddr ->
	output_byte s 3;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs;
    List.iter
      (fun watchaddr ->
	output_byte s 7;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs_offlinekey;
    List.iter
      (fun watchaddr ->
	output_byte s 8;
	seocf (seo_addr seoc watchaddr (s,None)))
      !walletwatchaddrs_offlinekey_fresh;
    close_out_noerr s
  with e ->
    Utils.log_string (Printf.sprintf "exception during filter_wallet: %s\n" (Printexc.to_string e));
    close_out_noerr s

let append_wallet f =
  let wallfn = Filename.concat (datadir()) "wallet" in
  let s = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o600 wallfn in
  f s;
  close_out_noerr s

let privkey_in_wallet_p alpha =
  let (p,xs) = alpha in
  if p = 0 then
    begin
      let s kl =
	try
	  ignore (List.find (fun (_,_,_,_,h,_) -> h = xs) kl);
	  true
	with Not_found -> false
      in
      s !walletkeys_staking || s !walletkeys_nonstaking || s !walletkeys_staking_fresh || s !walletkeys_nonstaking_fresh
    end
  else
    false

let endorsement_in_wallet_p alpha =
  let (p,xs) = alpha in
  if p = 0 || p = 1 then
    let b = (p = 1) in
    begin
      try
	ignore (List.find (fun (beta,_,_,_,_,_) -> beta = (b,xs)) !walletendorsements);
	true
      with Not_found -> false
    end
  else
    false

let endorsement_in_wallet_2_p alpha beta =
  let (p,xs) = alpha in
  let (q,ys) = beta in
  if (p = 0 || p = 1) && (q = 0 || q = 1) then
    let b = (p = 1) in
    let c = (q = 1) in
    begin
      try
	ignore (List.find (fun (alpha2,beta2,_,_,_,_) -> alpha2 = (b,xs) && beta2 = (c,ys)) !walletendorsements);
	true
      with Not_found -> false
    end
  else
    false

let watchaddr_in_wallet_p alpha =
  List.mem alpha !walletwatchaddrs || List.mem alpha !walletwatchaddrs_offlinekey || List.mem alpha !walletwatchaddrs_offlinekey_fresh

let hexchar_invi x =
  match x with
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'A' -> 10
  | 'B' -> 11
  | 'C' -> 12
  | 'D' -> 13
  | 'E' -> 14
  | 'F' -> 15
  | 'a' -> 10
  | 'b' -> 11
  | 'c' -> 12
  | 'd' -> 13
  | 'e' -> 14
  | 'f' -> 15
  | _ -> raise (Failure("not a hex: " ^ (string_of_int (Char.code x))))

let hexsubstring_int8 h i =
  (hexchar_invi h.[i]) lsl 4 + (hexchar_invi h.[i+1])

let bytelist_of_hexstring h =
  let l = ref (String.length h) in
  let bl = ref [] in
  l := !l-2;
  while (!l > 0) do
    bl := hexsubstring_int8 h !l::!bl;
    l := !l-2
  done;
  !bl

let btctopfgaddr oc a =
  let alpha = btcaddrstr_addr a in
  let a2 = addr_pfgaddrstr alpha in
  Printf.fprintf oc "Proofgold address %s corresponds to Bitcoin address %s\n" a2 a

let importprivkey_real oc (k,b) cls report =
  match Secp256k1.smulp k Secp256k1._g with
  | Some(x,y) ->
      let h = hashval_be160 (pubkey_hashval (x,y) b) in
      let alpha = p2pkhaddr_addr h in
      let a = addr_pfgaddrstr alpha in
      let replwall = ref false in
      if privkey_in_wallet_p alpha then raise (Failure "Private key already in wallet.");
      let clsn =
	if cls = "nonstaking" then 4 else if cls = "staking_fresh" then 5 else if cls = "nonstaking_fresh" then 6 else 0
      in
      let wr = if clsn = 4 then walletkeys_nonstaking else if clsn = 5 then walletkeys_staking_fresh else if clsn = 6 then walletkeys_nonstaking_fresh else walletkeys_staking in
      wr := (k,b,(x,y),pfgwif k b,h,a)::!wr;
      walletendorsements := (*** remove endorsements if the wallet has the private key for the address, since it can now sign directly ***)
	List.filter
	  (fun (alpha2,beta,(x,y),recid,fcomp,esg) -> if alpha = payaddr_addr alpha2 then (replwall := true; false) else true)
	  !walletendorsements;
      walletwatchaddrs :=
	List.filter
	  (fun alpha2 -> if alpha = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs;
      walletwatchaddrs_offlinekey :=
	List.filter
	  (fun alpha2 -> if alpha = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs_offlinekey;
      walletwatchaddrs_offlinekey_fresh :=
	List.filter
	  (fun alpha2 -> if alpha = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs_offlinekey_fresh;
      if !replwall then
	save_wallet()
      else
	append_wallet
	  (fun s ->
	    output_byte s clsn;
	    seocf (seo_prod seo_big_int_256 seo_bool seoc (k,b) (s,None)));
      if report then Printf.fprintf oc "Imported key for address %s\n" a;
      flush stdout
  | None ->
      raise (Failure "This private key does not give a public key.")

let importprivkey oc w cls =
  let (k,b) = privkey_from_wif w in
  let w2 = pfgwif k b in
  if not (w2 = w) then raise (Failure (w ^ " is not a valid Proofgold wif"));
  importprivkey_real oc (k,b) cls true

let importbtcprivkey oc w cls =
  let (k,b) = privkey_from_btcwif w in
  importprivkey_real oc (k,b) cls true

let importendorsement oc a b s =
  let alpha = pfgaddrstr_addr a in
  let beta = pfgaddrstr_addr b in
  if endorsement_in_wallet_2_p alpha beta then raise (Failure ("An endorsement from " ^ a ^ " to " ^ b ^ " is already in the wallet."));
  let (q,ys) = beta in
  if q = 0 && not (privkey_in_wallet_p beta) then raise (Failure ("The private key for " ^ b ^ " must be in the wallet before an endorsement to it can be added."));
  let betap = (q=1,ys) in
  let (recid,fcomp,esg) = decode_signature s in
  let (p,xs) = alpha in
  if p = 0 then
    begin
      let alphap = (false,xs) in
      if privkey_in_wallet_p alpha then raise (Failure "Not adding endorsement since the wallet already has the private key for this address.");
      match verifybitcoinmessage_recover xs recid fcomp esg ("endorse " ^ b) with
      | None ->
	  if !Config.testnet then
	    begin
	      match verifybitcoinmessage_recover (Be160.of_int32p5 (-916116462l, -1122756662l, 602820575l, 669938289l, 1956032577l)) recid fcomp esg ("fakeendorsement " ^ b ^ " (" ^ (addr_pfgaddrstr alpha) ^ ")") with
	      | None ->
		  raise (Failure "endorsement signature verification failed; not adding endorsement to wallet")
	      | Some(x,y) ->
		  Printf.fprintf oc "Fake endorsement acceptable for testnet; adding to wallet.\n";
		  walletendorsements := (alphap,betap,(x,y),recid,fcomp,esg)::!walletendorsements;
		  save_wallet() (*** overkill, should append if possible ***)
	    end
	  else
	    raise (Failure "endorsement signature verification failed; not adding endorsement to wallet")
      | Some(x,y) ->
(*	  Printf.fprintf oc "just verified endorsement signature:\naddrhex = %s\nrecid = %d\nfcomp = %s\nesgr = %s\nesgs = %s\nendorse %s\n" (hashval_hexstring (x4,x3,x2,x1,x0)) recid (if fcomp then "true" else "false") (let (r,s) = esg in string_of_big_int r) (let (r,s) = esg in string_of_big_int s) b; flush stdout; *)
	  Printf.fprintf oc "Verified endorsement; adding to wallet.\n";
	  walletendorsements := (alphap,betap,(x,y),recid,fcomp,esg)::!walletendorsements;
	  save_wallet() (*** overkill, should append if possible ***)
    end
  else if p = 1 then (*** endorsement by a p2sh address, endorsement can only be checked if the script for alpha is known, so it should have been imported earlier ***)
    begin
      raise (Failure "Code for importing endorsements by a p2sh addresses has not yet been written.")
    end
  else
    raise (Failure (a ^ " expected to be a p2pkh or p2sh Proofgold address."))

let importp2sh oc bl =
  let alpha = Script.hash160_bytelist bl in
  let alpha1 = p2shaddr_addr alpha in
  let alphas = addr_pfgaddrstr alpha1 in
  begin
    try
      ignore (List.find (fun (z,_,_) -> z = alpha) !walletp2shs);
      Printf.fprintf oc "Already have p2sh address %s in wallet.\n" alphas;
    with Not_found ->
      let replwall = ref false in
      walletp2shs := (alpha,alphas,bl)::!walletp2shs;
      (** remove from watch wallet if it is there **)
      walletwatchaddrs :=
	List.filter
	  (fun alpha2 -> if alpha1 = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs;
      walletwatchaddrs_offlinekey :=
	List.filter
	  (fun alpha2 -> if alpha1 = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs_offlinekey;
      walletwatchaddrs_offlinekey_fresh :=
	List.filter
	  (fun alpha2 -> if alpha1 = alpha2 then (replwall := true; false) else true)
	  !walletwatchaddrs_offlinekey_fresh;
      if !replwall then
	save_wallet()
      else
	append_wallet
	  (fun s ->
	    output_byte s 1;
	    seocf (seo_list seo_int8 seoc bl (s,None)));
      Printf.fprintf oc "Imported p2sh address: %s\n" alphas;
  end
  
let importwatchaddr oc a cls =
  let alpha = pfgaddrstr_addr a in
  let a2 = addr_pfgaddrstr alpha in
  if not (a2 = a) then raise (Failure (a ^ " is not a valid Proofgold address"));
  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
  if cls = "offlinekey" then
    walletwatchaddrs_offlinekey := alpha::!walletwatchaddrs_offlinekey
  else if cls = "offlinekey_fresh" then
    walletwatchaddrs_offlinekey_fresh := alpha::!walletwatchaddrs_offlinekey_fresh
  else
    walletwatchaddrs := alpha::!walletwatchaddrs;
  save_wallet() (*** overkill, should append if possible ***)

let importwatchbtcaddr oc a cls =
  let alpha = btcaddrstr_addr a in
  let a2 = addr_pfgaddrstr alpha in
  Printf.fprintf oc "Importing as Proofgold address %s\n" a2;
  if privkey_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has the private key for this address.");
  if endorsement_in_wallet_p alpha then raise (Failure "Not adding as a watch address since the wallet already has an endorsement for this address.");
  if watchaddr_in_wallet_p alpha then raise (Failure "Watch address is already in wallet.");
  if cls = "offlinekey" then
    walletwatchaddrs_offlinekey := alpha::!walletwatchaddrs_offlinekey
  else if cls = "offlinekey_fresh" then
    walletwatchaddrs_offlinekey_fresh := alpha::!walletwatchaddrs_offlinekey_fresh
  else
    walletwatchaddrs := alpha::!walletwatchaddrs;
  save_wallet() (*** overkill, should append if possible ***)

let importwallet oc w =
  if not (Sys.file_exists w) then
    begin
      raise (Failure (Printf.sprintf "file %s does not exist" w))
    end;
  let s = open_in_bin w in
    try
      while true do
	let by = input_byte s in
	match by with
	| 0 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_staking :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_staking
	| 4 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_nonstaking :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_nonstaking
	| 5 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_staking_fresh :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_staking_fresh
	| 6 ->
	    let ((k,b),_) = sei_prod sei_big_int_256 sei_bool seic (s,None) in
	    walletkeys_nonstaking_fresh :=
	      (match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = pubkey_hashval (x,y) b in
		  let alpha1 = hashval_be160 h in
		  let alpha = addr_pfgaddrstr (p2pkhaddr_addr alpha1) in
		  (k,b,(x,y),pfgwif k b,alpha1,alpha)
	      | None ->
		  raise (Failure "A private key in the wallet did not give a public key.")
	      )::!walletkeys_nonstaking_fresh
	| 1 ->
	    let (scr,_) = sei_list sei_int8 seic (s,None) in
	    walletp2shs :=
	      (let h = hash160_bytelist scr in
	      let a = addr_pfgaddrstr (p2shaddr_addr h) in
	      (h,a,scr))::!walletp2shs
	| 2 ->
	    let (endors,_) = sei_prod6 sei_payaddr sei_payaddr (sei_prod sei_big_int_256 sei_big_int_256) sei_varintb sei_bool sei_signat seic (s,None) in (*** For each (alpha,beta,esg) beta can use esg to justify signing for alpha; endorsements can be used for spending/moving, but not for staking. ***)
	    walletendorsements := endors::!walletendorsements
	| 3 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs := watchaddr::!walletwatchaddrs
	| 7 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs_offlinekey := watchaddr::!walletwatchaddrs_offlinekey
	| 8 ->
	    let (watchaddr,_) = sei_addr seic (s,None) in
	    walletwatchaddrs_offlinekey_fresh := watchaddr::!walletwatchaddrs_offlinekey_fresh
	| _ ->
	    raise (Failure "Bad entry in wallet file")
      done
    with
    | End_of_file -> close_in_noerr s; save_wallet()
    | Failure(x) ->
	Printf.printf "Warning: %s\nIgnoring the rest of the wallet file.\n" x; flush stdout;
	close_in_noerr s;
        save_wallet()

(*** make sure we locally know the contents of the address (which should be empty, of course) ***)
let rec randomly_generate_newkeyandaddress ledgerroot cls =
  let giveup = ref 65536 in
  let k = strong_rand_256() in
  let b = true in (*** compressed ***)
  let rec newkeyandaddress_rec k =
    match Secp256k1.smulp k Secp256k1._g with
    | None -> (*** try again, in the very unlikely event this happened ***)
	randomly_generate_newkeyandaddress ledgerroot cls
    | Some(x,y) ->
	let w = pfgwif k true in
	let h = hashval_be160 (pubkey_hashval (x,y) b) in
	let alpha = p2pkhaddr_addr h in
	try
	  ignore (ctree_addr true false alpha (CHash(ledgerroot)) None);
	  let a = addr_pfgaddrstr alpha in
	  Utils.log_string (Printf.sprintf "Importing privkey %s for address %s\n" w a);
	  importprivkey_real !Utils.log (k,b) cls false;
	  (k,h)
	with Not_found ->
	  decr giveup;
	  if !giveup > 0 then
	    newkeyandaddress_rec (succ_big_int k)
	  else
	    raise (Failure "could not generature a new address accessible by the local ledger")
  in
  newkeyandaddress_rec k

let generate_newkeyandaddress ledgerroot cls =
  if cls = "" || cls = "staking" then
    begin
      match !walletkeys_staking_fresh with
      | (k::wr) ->
	  walletkeys_staking_fresh := wr;
	  walletkeys_staking := k::!walletkeys_staking;
	  save_wallet();
	  let (k,_,_,_,h,_) = k in
	  (k,h)
      | [] ->
	  randomly_generate_newkeyandaddress ledgerroot cls
    end
  else
    begin
      match !walletkeys_nonstaking_fresh with
      | (k::wr) ->
	  walletkeys_nonstaking_fresh := wr;
	  walletkeys_nonstaking := k::!walletkeys_nonstaking;
	  save_wallet();
	  let (k,_,_,_,h,_) = k in
	  (k,h)
      | [] ->
	  randomly_generate_newkeyandaddress ledgerroot cls
    end

let get_fresh_offline_address oc =
  match !walletwatchaddrs_offlinekey_fresh with
  | alpha::wr ->
      walletwatchaddrs_offlinekey := alpha::!walletwatchaddrs_offlinekey;
      walletwatchaddrs_offlinekey_fresh := wr;
      save_wallet();
      alpha
  | _ ->
      Printf.fprintf oc "No fresh offline addresses\n";
      raise (Failure("out of fresh offline addresses"))

let reclassify_staking oc alpha b =
  let (p,xs) = pfgaddrstr_addr alpha in
  if not (p = 0) then
    Printf.fprintf oc "%s is not p2pkh\n" alpha
  else if b then
    begin (*** from staking to nonstaking ***)
      try
	let ke = List.find (fun (_,_,_,_,h,_) -> h = xs) !walletkeys_nonstaking in
	let (k,b,(x,y),w,h,a) = ke in
	walletkeys_staking := (k,b,(x,y),w,h,a)::!walletkeys_staking;
	walletkeys_nonstaking := List.filter (fun (_,_,_,_,h,_) -> not (h = xs)) !walletkeys_nonstaking;
	save_wallet()
      with Not_found ->
	Printf.fprintf oc "%s is not among the nonstaking keys in the wallet\n" alpha
    end
  else
    begin (*** from nonstaking to staking ***)
      try
	let ke = List.find (fun (_,_,_,_,h,_) -> h = xs) !walletkeys_staking in
	let (k,b,(x,y),w,h,a) = ke in
	walletkeys_nonstaking := (k,b,(x,y),w,h,a)::!walletkeys_nonstaking;
	walletkeys_staking := List.filter (fun (_,_,_,_,h,_) -> not (h = xs)) !walletkeys_staking;
	save_wallet()
      with Not_found ->
	Printf.fprintf oc "%s is not among the staking keys in the wallet\n" alpha
    end

exception EmptyAddress

let assets_at_address_in_ledger_json raiseempty alpha par ledgerroot blkh =
  let cache : (hashval,nehlist option * int) Hashtbl.t = Hashtbl.create 100 in
  let reported : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
  let alphas = addr_pfgaddrstr alpha in
  let ctr = Ctre.CHash(ledgerroot) in
  let warned = ref false in
  let jwl = ref [] in
  let jal = ref [] in
  let alpha_hl = ref (None,-1) in
  let tot = ref 0L in
  let handler f =
    try
      f()
    with
    | Not_found ->
	jwl := JsonObj([("warning",JsonStr("The complete ledger is not in the local database; some assets in the ledger might not be displayed."))])::!jwl;
	warned := true
    | e ->
      jwl := JsonObj([("warning",JsonStr(Printexc.to_string e))])::!jwl;
      warned := true
  in
  handler (fun () -> alpha_hl := Ctre.ctree_addr_cache cache true false alpha ctr None);
  let sumcurr a =
    match a with
    | (_,_,_,Currency(v)) -> tot := Int64.add !tot v
    | _ -> ()
  in
  let rec hlist_report_assets_json hl =
    match hl with
    | HHash(_,_) -> []
    | HNil -> []
    | HCons(a,hr) ->
	let ah = hashasset a in
	if not (Hashtbl.mem reported ah) then
	  begin
	    Hashtbl.add reported ah ();
	    json_asset a::hlist_report_assets_json hr
	  end
	else
	  hlist_report_assets_json hr
    | HConsH(ah,hr) ->
	hlist_report_assets_json hr
  in
  begin
    let add_previous_assets jpal jpalcnt =
      List.iter
        (fun ah ->
          let ((aid,bday,obl,u) as a) = DbAsset.dbget ah in
          if !jpalcnt < 10 then
            if Hashtbl.mem (if !spent_table_refreshing then spent_table_bkp else spent_table) aid then
              (incr jpalcnt; jpal := json_asset a::!jpal))
        (Hashtbl.find_all (if !asset_id_hash_refreshing then addr_contents_table_bkp else addr_contents_table) alpha);
    in
    match !alpha_hl with
    | (Some(hl),_) ->
       let jhl = hlist_report_assets_json (Ctre.nehlist_hlist hl) in
       let jpal = ref [] in
       let jpalcnt = ref 0 in
       add_previous_assets jpal jpalcnt;
       let s = Buffer.create 100 in
       Ctre.print_hlist_to_buffer_gen s blkh (Ctre.nehlist_hlist hl) sumcurr;
       jal := [("address",JsonStr(alphas));("total",JsonNum(bars_of_atoms !tot));("contents",JsonStr(Buffer.contents s));("currentassets",JsonArr(jhl));("previousassets",JsonArr(!jpal))]
    | (None,z) ->
	if raiseempty then
	  raise EmptyAddress
	else if z < 0 then
	  begin
	    jwl := JsonObj([("warning",JsonStr("Problem obtaining contents of address."))])::!jwl;
	    jal := [("address",JsonStr(alphas))]
	  end
	else
          begin
            let jpal = ref [] in
            let jpalcnt = ref 0 in
            add_previous_assets jpal jpalcnt;
	    jal := [("address",JsonStr(alphas));("contents",JsonStr("empty"));("previousassets",JsonArr(!jpal))]
          end
  end;
  let rec assets_at_address_in_ledger_json_history alpha par =
    match par with
    | None -> []
    | Some(lbk,ltx) ->
	try
	  let (_,_,_,_,par,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	  let (_,_,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	  handler (fun () -> alpha_hl := Ctre.ctree_addr_cache cache true false alpha (Ctre.CHash(ledgerroot)) None);	
	  match !alpha_hl with
	  | (Some(hl),_) ->
	      let jhl =
		List.map (fun j -> JsonObj([("type",JsonStr("spentasset"));
					    ("spentheight",JsonNum(Int64.to_string blkh));
					    ("asset",j)]))
		  (hlist_report_assets_json (Ctre.nehlist_hlist hl))
	      in
	      jhl @ assets_at_address_in_ledger_json_history alpha par
	  | (None,z) ->
	      assets_at_address_in_ledger_json_history alpha par
	with Not_found -> []
  in
(*  let jhl = assets_at_address_in_ledger_json_history alpha par in
  if not (jhl = []) then jal := ("historic",JsonArr(jhl))::!jal; *)
  (!jal,!jwl)

let printassets_in_ledger oc ledgerroot blkhght =
  let ctr = Ctre.CHash(ledgerroot) in
  let warned = ref false in
  let al1 = ref [] in
  let tot1 = ref 0L in
  let tot1u = ref 0L in
  let al2 = ref [] in
  let tot2 = ref 0L in
  let tot2u = ref 0L in
  let al3 = ref [] in
  let tot3 = ref 0L in
  let tot3u = ref 0L in
  let al4 = ref [] in
  let tot4 = ref 0L in
  let tot4u = ref 0L in
  let handler f =
    try
      f();
    with
    | Exit -> ()
    | GettingRemoteData ->
       if not !warned then
	 begin
	   Printf.fprintf oc "Warning: The complete ledger is not in the local database.\n";
	   Printf.fprintf oc "Some assets in the ledger might not be displayed.\n";
	   warned := true
	 end       
  in
  List.iter
    (fun (k,b,(x,y),w,h,z) ->
      handler (fun () -> let alpha = p2pkhaddr_addr h in al1 := (alpha,z,Ctre.ctree_addr true true alpha ctr None)::!al1))
    !walletkeys_staking;
  List.iter
    (fun (k,b,(x,y),w,h,z) ->
      handler (fun () -> let alpha = p2pkhaddr_addr h in al1 := (alpha,z,Ctre.ctree_addr true true alpha ctr None)::!al1))
    !walletkeys_nonstaking;
  List.iter
    (fun (h,z,scr) ->
      handler (fun () -> al2 := (z,Ctre.ctree_addr true true (p2shaddr_addr h) ctr None)::!al2))
    !walletp2shs;
  List.iter
    (fun (alpha,beta,(x,y),recid,fcomp,esg) -> 
      let alpha2 = payaddr_addr alpha in
      handler (fun () -> al3 := (alpha2,Ctre.ctree_addr true true alpha2 ctr None)::!al3))
    !walletendorsements;
  List.iter
    (fun alpha ->
      handler (fun () -> al4 := (alpha,Ctre.ctree_addr true true alpha ctr None)::!al4))
    !walletwatchaddrs;
  List.iter
    (fun alpha ->
      handler (fun () -> al4 := (alpha,Ctre.ctree_addr true true alpha ctr None)::!al4))
    !walletwatchaddrs_offlinekey;
  let sumcurr tot totu a =
    match a with
    | (_,_,Some(_,lh,_),Currency(_)) when lh > blkhght ->
	let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	tot := Int64.add !tot v
    | (_,_,_,Currency(_)) ->
	let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	tot := Int64.add !tot v;
	totu := Int64.add !totu v
    | _ -> ()
  in
  let spendable = ref [] in
  let sumcurr2 alpha tot totu a =
    match a with
    | (_,_,Some(_,lh,_),Currency(_)) when lh > blkhght ->
	let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	tot := Int64.add !tot v
    | (_,_,_,Currency(_)) ->
	let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	tot := Int64.add !tot v;
	totu := Int64.add !totu v;
	spendable := (alpha,a,v)::!spendable
    | _ -> ()
  in
  Printf.fprintf oc "Assets in ledger with root %s:\n" (hashval_hexstring ledgerroot);
  Printf.fprintf oc "Controlled p2pkh assets:\n";
  List.iter
    (fun (alpha,z,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.fprintf oc "%s:\n" z;
	  Ctre.print_hlist_gen oc blkhght (Ctre.nehlist_hlist hl) (sumcurr2 alpha tot1 tot1u)
      | (None,_) ->
	  Printf.fprintf oc "%s: empty\n" z;
    )
    !al1;
  Hashtbl.add spendable_assets_in_ledger ledgerroot !spendable;
  Printf.fprintf oc "Possibly controlled p2sh assets:\n";
  List.iter
    (fun (z,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.fprintf oc "%s:\n" z;
	  Ctre.print_hlist_gen oc blkhght (Ctre.nehlist_hlist hl) (sumcurr tot2 tot2u)
      | (None,_) ->
	  Printf.fprintf oc "%s: empty\n" z;
    )
    !al2;
  Printf.fprintf oc "Assets via endorsement:\n";
  List.iter
    (fun (alpha2,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.fprintf oc "%s:\n" (addr_pfgaddrstr alpha2);
	  Ctre.print_hlist_gen oc blkhght (Ctre.nehlist_hlist hl) (sumcurr tot3 tot3u)
      | (None,_) ->
	  Printf.fprintf oc "%s: empty\n" (addr_pfgaddrstr alpha2);
    )
    !al3;
  Printf.fprintf oc "Watched assets:\n";
  List.iter
    (fun (alpha,x) ->
      match x with
      | (Some(hl),_) ->
	  Printf.fprintf oc "%s:\n" (addr_pfgaddrstr alpha);
	  Ctre.print_hlist_gen oc blkhght (Ctre.nehlist_hlist hl) (sumcurr tot4 tot4u)
      | (None,_) ->
	  Printf.fprintf oc "%s: empty\n" (addr_pfgaddrstr alpha);
    )
    !al4;
  Printf.fprintf oc "Total p2pkh: %s bars (%s unlocked)\n" (bars_of_atoms !tot1) (bars_of_atoms !tot1u);
  Printf.fprintf oc "Total p2sh: %s bars (%s unlocked)\n" (bars_of_atoms !tot2) (bars_of_atoms !tot2u);
  Printf.fprintf oc "Total via endorsement: %s bars (%s unlocked)\n" (bars_of_atoms !tot3) (bars_of_atoms !tot3u);
  Printf.fprintf oc "Total watched: %s bars (%s unlocked)\n" (bars_of_atoms !tot4)  (bars_of_atoms !tot4u);
  Hashtbl.replace atoms_balances_in_ledger ledgerroot (!tot1,!tot1u,!tot2,!tot2u,!tot3,!tot3u,!tot4,!tot4u) (*** preventing recomputation for getting balances if the ledger has not changed ***)

let printassets oc =
  match !artificialledgerroot with
  | Some(ledgerroot) ->
      printassets_in_ledger oc ledgerroot (-1L)
  | None ->
      try
	let (b,cwl) = get_bestblock() in
	match b with
	| Some(_,lbk,ltx) ->
	    let (_,_,_,_,_,_,blkhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let (_,_,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    printassets_in_ledger oc ledgerroot blkhght
	| None -> ()
      with Not_found -> ()

let get_spendable_assets_in_ledger oc ledgerroot blkhght =
  try
    Hashtbl.find spendable_assets_in_ledger ledgerroot
  with Not_found ->
    let ctr = Ctre.CHash(ledgerroot) in
    let warned = ref false in
    let waitprinted = ref false in
    let numtrys = ref 2 in
    let al1 : (bool * addr * (nehlist option * int)) list ref = ref [] in
    let handler f =
      try
	if !numtrys > 1 then decr numtrys;
	for i = 1 to !numtrys do
	  try
	    f();
	    raise Exit
	  with GettingRemoteData ->
	    if !netconns = [] then
	      begin (** ignore if there are no connections **)
		if not !warned then
		  begin
		    Printf.fprintf oc "Warning: The complete ledger is not in the local database and there are no connections to request missing data.\n";
		    warned := true
		  end;
		raise Exit
	      end
	    else
	      begin
		if not !waitprinted then (Printf.fprintf oc "Some data is being requested from remote nodes...please wait a minute or two...\n"; flush oc; waitprinted := true);
		Thread.delay 2.0
	      end
	done;
	if not !warned then
	  begin
	    Printf.fprintf oc "Warning: The complete ledger is not in the local database.\n";
	    Printf.fprintf oc "Remote data is being requested, but is taking too long.\n";
	    warned := true
	  end
      with Exit -> ()
    in
    let havekey : (payaddr,unit) Hashtbl.t = Hashtbl.create 100 in
    List.iter
      (fun (k,b,(x,y),w,h,z) ->
        Hashtbl.add havekey (p2pkhaddr_payaddr h) ();
	handler (fun () -> let alpha = p2pkhaddr_addr h in al1 := (true,alpha,Ctre.ctree_addr true true alpha ctr None)::!al1))
      !walletkeys_staking;
    List.iter
      (fun (k,b,(x,y),w,h,z) ->
        Hashtbl.add havekey (p2pkhaddr_payaddr h) ();
	handler (fun () -> let alpha = p2pkhaddr_addr h in al1 := (true,alpha,Ctre.ctree_addr true true alpha ctr None)::!al1))
      !walletkeys_nonstaking;
    List.iter
      (fun alpha ->
        handler (fun () -> al1 := (false,alpha,Ctre.ctree_addr true true alpha ctr None) :: !al1))
      !walletwatchaddrs;
    List.iter
      (fun alpha ->
        handler (fun () -> al1 := (false,alpha,Ctre.ctree_addr true true alpha ctr None)::!al1))
      !walletwatchaddrs_offlinekey;
    let spendable = ref [] in
    let sumcurr2 haveholdingkey alpha a =
      match a with
      | (_,_,Some(beta,lh,_),_) when not (Hashtbl.mem havekey beta)  || lh > blkhght -> ()
      | (_,_,Some(_,lh,_),_) when lh > blkhght -> ()
      | (_,_,None,_) when not haveholdingkey -> ()
      | (_,_,_,Currency(_)) ->
	 let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	 spendable := (alpha,a,v)::!spendable
      | _ ->
	 spendable := (alpha,a,0L)::!spendable
    in
    List.iter
      (fun (haveholdingkey,alpha,x) ->
	match x with
	| (Some(hl),_) ->
	   Ctre.iter_hlist_gen blkhght (Ctre.nehlist_hlist hl) (sumcurr2 haveholdingkey alpha)
	| (None,_) -> ())
      !al1;
    Hashtbl.add spendable_assets_in_ledger ledgerroot !spendable;
    !spendable

let get_atoms_balances_in_ledger oc ledgerroot blkhght =
  try
    Hashtbl.find atoms_balances_in_ledger ledgerroot
  with Not_found ->
    let ctr = Ctre.CHash(ledgerroot) in
    let warned = ref false in
    let waitprinted = ref false in
    let tot1 = ref 0L in
    let tot1u = ref 0L in
    let tot2 = ref 0L in
    let tot2u = ref 0L in
    let tot3 = ref 0L in
    let tot3u = ref 0L in
    let tot4 = ref 0L in
    let tot4u = ref 0L in
    let numtrys = ref 11 in
    let handler f =
      try
	if !numtrys > 1 then decr numtrys;
	for i = 1 to !numtrys do
	  try
	    f();
	    raise Exit
	  with GettingRemoteData ->
	    if !netconns = [] then
	      begin (** ignore if there are no connections **)
		if not !warned then
		  begin
		    Printf.fprintf oc "Warning: The complete ledger is not in the local database and there are no connections to request missing data.\n";
		    Printf.fprintf oc "Some displayed balances may be too small.\n";
		    warned := true
		  end;
		raise Exit
	      end
	    else
	      begin
		if not !waitprinted then (Printf.fprintf oc "Some data is being requested from remote nodes...please wait a minute or two...\n"; flush oc; waitprinted := true);
                Thread.delay 2.0
	      end
	done;
	if not !warned then
	  begin
	    Printf.fprintf oc "Warning: The complete ledger is not in the local database.\n";
	    Printf.fprintf oc "Remote data is being requested, but is taking too long.\n";
	    Printf.fprintf oc "Some assets in the ledger might not be displayed.\n";
	    warned := true
	  end
      with Exit -> ()
    in
    let asset_sumcurr tot totu a =
      match a with
      | (_,_,Some(_,lh,_),Currency(_)) when lh > blkhght ->
	  let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	  tot := Int64.add !tot v
      | (_,_,_,Currency(_)) ->
	  let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
	  tot := Int64.add !tot v;
	  totu := Int64.add !totu v
      | _ -> ()
    in
    let rec hlist_sumcurr tot totu (hl:hlist) =
      match hl with
      | HNil -> ()
      | HConsH(ah,hr) -> hlist_sumcurr tot totu hr; asset_sumcurr tot totu (get_asset ah)
      | HCons(a,hr) -> hlist_sumcurr tot totu hr; asset_sumcurr tot totu a
      | HHash(hh,_) -> hlist_sumcurr tot totu (get_hlist_element hh)
    in
    let rec nehlist_sumcurr tot totu (hl:nehlist) =
      match hl with
      | NehConsH(ah,hr) -> hlist_sumcurr tot totu hr; asset_sumcurr tot totu (get_asset ah)
      | NehCons(a,hr) -> hlist_sumcurr tot totu hr; asset_sumcurr tot totu a
      | NehHash(hh,_) -> nehlist_sumcurr tot totu (get_nehlist_element hh)
    in
    List.iter
      (fun (k,b,(x,y),w,h,z) ->
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true (p2pkhaddr_addr h) ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot1 tot1u hl
	    | _ -> ()))
      !walletkeys_staking;
    List.iter
      (fun (k,b,(x,y),w,h,z) ->
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true (p2pkhaddr_addr h) ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot1 tot1u hl
	    | _ -> ()))
      !walletkeys_nonstaking;
    List.iter
      (fun (h,z,scr) ->
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true (p2shaddr_addr h) ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot2 tot2u hl
	    | _ -> ()))
      !walletp2shs;
    List.iter
      (fun (alpha,beta,(x,y),recid,fcomp,esg) -> 
	let alpha2 = payaddr_addr alpha in
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true alpha2 ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot3 tot3u hl
	    | _ -> ()))
      !walletendorsements;
    List.iter
      (fun alpha ->
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true alpha ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot4 tot4u hl
	    | _ -> ()))
      !walletwatchaddrs;
    List.iter
      (fun alpha ->
	handler
	  (fun () ->
	    match Ctre.ctree_addr true true alpha ctr None with
	      (Some(hl),_) -> nehlist_sumcurr tot4 tot4u hl
	    | _ -> ()))
      !walletwatchaddrs_offlinekey;
    Hashtbl.add atoms_balances_in_ledger ledgerroot (!tot1,!tot1u,!tot2,!tot2u,!tot3,!tot3u,!tot4,!tot4u);
    (!tot1,!tot1u,!tot2,!tot2u,!tot3,!tot3u,!tot4,!tot4u)

let printasset oc h =
  try
    let (aid,bday,obl,u) = DbAsset.dbget h in
    if bday = 0L then
      begin
	Printf.fprintf oc "%s: %s [initial distribution] %s %s (note: value has been halved at least once)\n" (hashval_hexstring h) (hashval_hexstring aid) (preasset_string u) (obligation_string obl)
      end
    else
      Printf.fprintf oc "%s: %s [%Ld] %s %s\n" (hashval_hexstring h) (hashval_hexstring aid) bday (preasset_string u) (obligation_string obl)
  with Not_found ->
    Printf.fprintf oc "No asset with hash %s found. (Did you give the asset id instead of the asset hash?)\n" (hashval_hexstring h)

let printhconselt oc h =
  try
    let (aid,k) = DbHConsElt.dbget h in
    Printf.fprintf oc "assetid %s\n" (hashval_hexstring aid);
    match k with
    | Some(k,l) -> Printf.fprintf oc "next hcons elt %s[%d]\n" (hashval_hexstring k) l
    | None -> Printf.fprintf oc "last on the list\n"
  with Not_found ->
    Printf.fprintf oc "No hcons elt %s found\n" (hashval_hexstring h)

let printctreeelt oc h =
  try
    let c = DbCTreeElt.dbget h in
    print_ctree oc c
  with Not_found ->
    Printf.fprintf oc "No ctree elt %s found\n" (hashval_hexstring h)

let printctreeatm oc h =
  try
    let c = DbCTreeAtm.dbget h in
    print_ctree oc c
  with Not_found ->
    Printf.fprintf oc "No ctree elt %s found\n" (hashval_hexstring h)

let printctreeinfo oc h =
  try
    let c = expand_ctree_atom_or_element false h in
    let v = ref 0L in
    let b = ref 0L in
    let e = ref 1 in
    let l = ref 0 in
    let a = ref 0 in
    let own = ref 0 in
    let rght = ref 0 in
    let mrk = ref 0 in
    let pub = ref 0 in
    let ah = ref 0 in
    let hh = ref 0 in
    let ch = ref 0 in
    let rec hconseltinfo (aid,k) =
      try
	let (_,_,_,preast) = DbAsset.dbget aid in
	incr a;
	match preast with
	| Currency(u) -> v := Int64.add u !v
	| Bounty(u) -> b := Int64.add u !b
	| OwnsObj(_,_,_) -> incr own
	| OwnsProp(_,_,_) -> incr own
	| OwnsNegProp -> incr own
	| RightsObj(_,_) -> incr rght
	| RightsProp(_,_) -> incr rght
	| Marker -> incr mrk
	| _ -> incr pub
      with Not_found ->
	incr ah;
	match k with
	| None -> ()
	| Some(k,_) ->
	    try
	      hconseltinfo (DbHConsElt.dbget k)
	    with Not_found ->
	      incr hh
    in
    let rec ctreeeltinfo c =
      match c with
      | CHash(h) ->
	  begin
	    try
	      incr e;
	      ctreeeltinfo (expand_ctree_atom_or_element false h)
	    with Not_found -> incr ch
	  end
      | CLeaf(_,NehHash(h,_)) ->
	  begin
	    try
	      incr l;
	      hconseltinfo (DbHConsElt.dbget h)
	    with Not_found -> incr hh
	  end
      | CLeaf(_,_) -> raise (Failure "ctree was not an element")
      | CLeft(c0) -> ctreeeltinfo c0
      | CRight(c1) -> ctreeeltinfo c1
      | CBin(c0,c1) -> ctreeeltinfo c0; ctreeeltinfo c1
    in
    ctreeeltinfo c;
    Printf.fprintf oc "Number of abstract unknown ctrees %d\n" !ch;
    Printf.fprintf oc "Number of abstract unknown hcons elts %d\n" !hh;
    Printf.fprintf oc "Number of abstract unknown assets %d\n" !ah;
    Printf.fprintf oc "Number of known ctree elts %d\n" !e;
    Printf.fprintf oc "Number of known leaves %d\n" !l;
    Printf.fprintf oc "Number of known assets %d\n" !a;
    Printf.fprintf oc "Number of ownership assets %d\n" !own;
    Printf.fprintf oc "Number of rights assets %d\n" !rght;
    Printf.fprintf oc "Number of marker assets %d\n" !mrk;
    Printf.fprintf oc "Number of publication assets %d\n" !pub;
    Printf.fprintf oc "Total atoms in known currency assets %Ld\n" !v;
    Printf.fprintf oc "Total atoms in known bounty assets %Ld\n" !b;
  with Not_found ->
    Printf.fprintf oc "No ctree %s found\n" (hashval_hexstring h)
  
let printtx_a oc (tauin,tauout) =
  let i = ref 0 in
  Printf.fprintf oc "Inputs (%d):\n" (List.length tauin);
  List.iter
    (fun (alpha,aid) ->
      Printf.fprintf oc "Input %d:%s %s\n" !i (addr_pfgaddrstr alpha) (hashval_hexstring aid);
      incr i)
    tauin;      
  i := 0;
  Printf.fprintf oc "Outputs (%d):\n" (List.length tauout);
  List.iter
    (fun (alpha,(obl,u)) ->
      Printf.fprintf oc "Output %d:%s %s %s\n" !i (addr_pfgaddrstr alpha) (preasset_string u) (obligation_string obl);
      incr i)
    tauout

let printtx oc txid =
  try
    let (tau,_) = Hashtbl.find stxpool txid in
    Printf.fprintf oc "Tx %s in pool.\n" (hashval_hexstring txid);
    printtx_a oc tau
  with Not_found ->
    try
      let (tau,_) = DbSTx.dbget txid in
      Printf.fprintf oc "Tx %s in local database.\n" (hashval_hexstring txid);
      printtx_a oc tau
    with Not_found ->
      Printf.fprintf oc "Unknown tx %s.\n" (hashval_hexstring txid)

let createtx inpj outpj =
  match (inpj,outpj) with
  | (JsonArr(inpl),JsonArr(outpl)) ->
      begin
	let tauinl =
	  List.map
	    (fun inp ->
	      match inp with
	      | JsonObj([(alpha,JsonStr(aidhex))]) ->
		  (pfgaddrstr_addr alpha,hexstring_hashval aidhex)
	      | _ -> raise Exit)
	    inpl
	in
	  let tauoutl =
	    List.map
	      (fun outp ->
		match outp with
		| JsonObj(al) ->
		    begin
		      try
			let betaj = List.assoc "addr" al in
			let valj = List.assoc "val" al in
			match (betaj,valj) with
			| (JsonStr(beta),JsonNum(x)) ->
			    begin
			      let beta2 = pfgaddrstr_addr beta in
			      let v = atoms_of_bars x in
			      try
				let lockj = List.assoc "lockheight" al in
				match lockj with
				| JsonNum(lockstr) ->
				    let lock = Int64.of_string lockstr in
				    begin
				      try
					let obladdrj = List.assoc "lockaddr" al in
					match obladdrj with
					| JsonStr(obladdr) ->
					    let gamma2 = pfgaddrstr_addr obladdr in
					    if not (payaddr_p gamma2) then raise (Failure (Printf.sprintf "obligation address %s must be a payaddr (p2pkh or p2sh)" obladdr));
					    let (i,cs) = gamma2 in
					    let gamma_as_payaddr = (i=1,cs) in
					    let obl = Some(gamma_as_payaddr,lock,false) in
					    (beta2,(obl,Currency(v)))
					| _ -> raise Exit
				      with Not_found ->
					if not (payaddr_p beta2) then raise (Failure (Printf.sprintf "since output will be locked, receiving address %s must be a payaddr (p2pkh or p2sh) or a payaddr as obligation address must be given" beta));
					let (i,bs) = beta2 in
					let beta_as_payaddr = (i=1,bs) in
					let obl = Some(beta_as_payaddr,lock,false) in
					(beta2,(obl,Currency(v)))
				    end
				| _ -> raise Exit
			      with Not_found ->
				(beta2,(None,Currency(v)))
			    end
			| _ -> raise Exit
		      with Not_found -> raise Exit
		    end
		| _ -> raise Exit)
	      outpl
	  in
	  (tauinl,tauoutl)
      end
  | _ -> raise Exit

let createsplitlocktx oc ledgerroot blkhght alpha beta gamma aid i lkh fee =
  if i <= 0 then raise (Failure ("Cannot split into " ^ (string_of_int i) ^ " assets"));
  let alpha2 = payaddr_addr alpha in
  let ctr = Ctre.CHash(ledgerroot) in
  match ctree_lookup_asset false true false aid ctr (0,alpha2) with
  | None -> Printf.fprintf oc "Could not find asset %s at %s in ledger %s\n" (hashval_hexstring aid) (addr_pfgaddrstr alpha2) (hashval_hexstring ledgerroot); flush stdout
  | Some((_,bday,obl,Currency(_)) as a) ->
      let v = match asset_value blkhght a with None -> 0L | Some(v) -> v in
      if v > fee then
	begin
	  let rem = ref (Int64.sub v fee) in
	  let u = Int64.div !rem (Int64.of_int i) in
	  if u > 0L then
	    begin
	      let outl = ref [] in
	      for j = 0 to i-2 do
		outl := (gamma,(Some(beta,lkh,false),Currency(u)))::!outl;
		rem := Int64.sub !rem u
	      done;
	      outl := (gamma,(Some(beta,lkh,false),Currency(!rem)))::!outl;
	      let tau : tx = ([(alpha2,aid)],!outl) in
	      printtx_a oc tau;
	      let s = Buffer.create 100 in
	      seosbf (seo_stx seosb (tau,([],[])) (s,None));
	      let hs = string_hexstring (Buffer.contents s) in
	      Printf.fprintf oc "%s\n" hs
	    end
	  else
	    begin
	      Printf.fprintf oc "Asset %s is %s bars, which is smaller than %d atoms after subtracting the fee of %s\n" (hashval_hexstring aid) (bars_of_atoms v) i (bars_of_atoms v); flush stdout
	    end	  
	end
      else
	begin
	  Printf.fprintf oc "Asset %s is %s bars, which is not greater the fee of %s\n" (hashval_hexstring aid) (bars_of_atoms v) (bars_of_atoms v); flush stdout
	end
  | _ -> Printf.fprintf oc "Asset %s is not currency.\n" (hashval_hexstring aid); flush stdout

let simple_checksig_script bl stk =
  let sigssofar =
    List.map
      (fun dl ->
	match dl with
	| (00::rs) when List.length rs = 64 ->
	    let (r,s) = next_bytes 32 rs in
	    (dl,inum_be r,inum_be s)
	| _ -> raise Not_found)
      (List.rev stk)
  in
  let rec simple_checksig_script_2 br =
    let (dl,bs) = pop_bytes br in
    match bs with
    | [0xac] ->
	begin
	  match bytelist_to_pt dl with
	  | None -> raise Not_found
	  | Some(x,y) ->
	      match dl with
	      | (c::_) when c = 4 ->
		  let h = hashval_be160 (pubkey_hashval (x,y) false) in
		  (sigssofar,false,x,y,h)
	      | _ ->
		  let h = hashval_be160 (pubkey_hashval (x,y) true) in
		  (sigssofar,true,x,y,h)
	end
    | (177::117::br) -> (** CLTV;DROP -- skip for signing purposes **)
	simple_checksig_script_2 br
    | (178::117::br) -> (** CSV;DROP -- skip for signing purposes **)
	simple_checksig_script_2 br
    | _ -> raise Not_found
  in
  simple_checksig_script_2 bl

let simple_multisig_script bl stk =
  let rec simple_multisig_script_2 m br pkl =
    match br with
    | [n;174] when n >= 81 && n <= 96 ->
	if n - 80 = List.length pkl then
	  let sigssofar =
	    List.map
	      (fun dl ->
		match dl with
		| (00::rs) when List.length rs = 64 ->
		    let (r,s) = next_bytes 32 rs in
		    (dl,inum_be r,inum_be s)
		| _ -> raise Not_found)
	      (List.rev stk)
	  in
	  (sigssofar,bl,m,n-80,List.rev pkl)
	else
	  raise Not_found
    | _ ->
	let (dl,bs) = pop_bytes br in
	match bytelist_to_pt dl with
	| None -> raise Not_found
	| Some(x,y) ->
	    match dl with
	    | (c::_) when c = 4 ->
		let h = hashval_be160 (pubkey_hashval (x,y) false) in
		simple_multisig_script_2 m bs ((false,x,y,h)::pkl)
	    | _ ->
		let h = hashval_be160 (pubkey_hashval (x,y) true) in
		simple_multisig_script_2 m bs ((true,x,y,h)::pkl)
  in
  match bl with
  | (n::br) when n >= 81 && n <= 96 ->
      simple_multisig_script_2 (n-80) br []
  | _ -> raise Not_found

let simple_atomicswap_script bl stk =
  if not (stk = []) then raise Not_found; (** assume there is no partial signature yet, for simplicity **)
  match bl with
  | (0x63::0x51::0x20::br) ->
      begin
	try
	  let (ltxidl,br) = next_bytes 32 br in
	  match br with
	  | (0xb3::0x76::0xa9::0x14::br) ->
	      begin
		try
		  let (alphabl,br) = next_bytes 20 br in
		  match br with
		  | (0x67::0x04::br) ->
		      begin
			try
			  let (locktmbl,br) = next_bytes 4 br in
			  match br with
			  | (lkop::0x75::0x76::0xa9::0x14::br) when lkop = 0xb1 || lkop = 0xb2 ->
			      begin
				try
				  let (betabl,br) = next_bytes 20 br in
				  if br = [0x68;0x88;0xac] then
				    (bytelist_be160 alphabl,
				     bytelist_be160 betabl,
				     int64_of_big_int (inum_le locktmbl),
                                     bytelist_be256 ltxidl)
				  else
				    raise Not_found
				with _ -> raise Not_found
			      end
			  | _ -> raise Not_found
			with _ -> raise Not_found
		      end
		  | _ -> raise Not_found
		with _ -> raise Not_found
	      end
	  | _ -> raise Not_found
	with _ -> raise Not_found
      end
  | _ -> raise Not_found

let simple_atomicswap_n_script bl stk =
  if not (stk = []) then raise Not_found; (** assume there is no partial signature yet, for simplicity **)
  match bl with
  | (0x63::0x01::n::0x20::br) ->
      begin
	try
	  let (ltxidl,br) = next_bytes 32 br in
	  match br with
	  | (0xb3::0x76::0xa9::0x14::br) ->
	      begin
		try
		  let (alphabl,br) = next_bytes 20 br in
		  match br with
		  | (0x67::0x04::br) ->
		      begin
			try
			  let (locktmbl,br) = next_bytes 4 br in
			  match br with
			  | (lkop::0x75::0x76::0xa9::0x14::br) when lkop = 0xb1 || lkop = 0xb2 ->
			      begin
				try
				  let (betabl,br) = next_bytes 20 br in
				  if br = [0x68;0x88;0xac] then
				    (bytelist_be160 alphabl,
				     bytelist_be160 betabl,
				     int64_of_big_int (inum_le locktmbl),
                                     bytelist_be256 ltxidl,
                                     n,lkop = 0xb1)
				  else
				    raise Not_found
				with _ -> raise Not_found
			      end
			  | _ -> raise Not_found
			with _ -> raise Not_found
		      end
		  | _ -> raise Not_found
		with _ -> raise Not_found
	      end
	  | _ -> raise Not_found
	with _ -> raise Not_found
      end
  | _ -> raise Not_found

let simple_htlc_script bl stk =
  if not (stk = []) then raise Not_found; (** assume there is no partial signature yet, for simplicity **)
  match bl with
  | (0x63::0x82::0x01::0x20::0x88::0xa8::0x20::br) -> (*** 32 bytes ***)
      begin
	try
	  let (secrhbl,br) = next_bytes 32 br in
	  match br with
	  | (0x88::0x76::0xa9::0x14::br) ->
	      begin
		try
		  let (alphabl,br) = next_bytes 20 br in
		  match br with
		  | (0x67::0x04::br) ->
		      begin
			try
			  let (locktmbl,br) = next_bytes 4 br in
			  match br with
			  | (lkop::0x75::0x76::0xa9::0x14::br) when lkop = 0xb1 || lkop = 0xb2 ->
			      begin
				try
				  let (betabl,br) = next_bytes 20 br in
				  if br = [0x68;0x88;0xac] then
				    (bytelist_be160 alphabl,
				     bytelist_be160 betabl,
				     int64_of_big_int (inum_le locktmbl),
				     lkop = 0xb2,
                                     bytelist_be256 secrhbl)
				  else
				    raise Not_found
				with _ -> raise Not_found
			      end
			  | _ -> raise Not_found
			with _ -> raise Not_found
		      end
		  | _ -> raise Not_found
		with _ -> raise Not_found
	      end
	  | _ -> raise Not_found
	with _ -> raise Not_found
      end
  | _ -> raise Not_found

let simple_veto_script bl stk =
  if not (stk = []) then raise Not_found; (** assume there is no partial signature yet, for simplicity **)
  match bl with
  | 0x63::0x76::0xa9::0x14::br ->
     begin
       let (alphabl,br) = next_bytes 20 br in
       begin
         match br with
         | 0x67::0x04::br ->
            let (locktmbl,br) = next_bytes 4 br in
            begin
              match br with
              | lkop::0x75::0x76::0xa9::0x14::br when lkop = 0xb1 || lkop = 0xb2 ->
                 begin
                   let (betabl,br) = next_bytes 20 br in
                   if br = [0x68;0x88;0xac] then
                     (bytelist_be160 alphabl,
                      bytelist_be160 betabl,
                      int64_of_big_int (inum_le locktmbl),
                      lkop = 0xb2)
                   else
                     raise Not_found
                 end
              | _ -> raise Not_found
            end
         | _ -> raise Not_found
       end
     end
  | _ -> raise Not_found

(*** first see if private key for beta is in the wallet; if not check if an endorsement is in the wallet; if not fail ***)
let signtx_p2pkh kl beta taue =
  match kl with
  | Some(kl) ->
     let (k,b,(x,y),_) = List.find (fun (_,_,_,h) -> h = beta) kl in
     let (_,(r,s)) = repeat_rand (signat_big_int taue k) rand_256 in
     P2pkhSignat(Some(x,y),b,(r,s))
  | None ->
      try
	let (k,b,(x,y),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = beta) !walletkeys_staking in
        let (_,(r,s)) = repeat_rand (signat_big_int taue k) rand_256 in
	P2pkhSignat(Some(x,y),b,(r,s))
      with Not_found ->
	try
	  let (k,b,(x,y),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = beta) !walletkeys_nonstaking in
          let (_,(r,s)) = repeat_rand (signat_big_int taue k) rand_256 in
	  P2pkhSignat(Some(x,y),b,(r,s))
	with Not_found ->
	  let (alpha,gamma,(x,y),recid,fcomp,esg) =
	    List.find 
	      (fun (alpha,gam,_,_,_,_) ->
		let (p,av) = alpha in
		not p && av = beta)
	      !walletendorsements
	  in
	  let (p,cv) = gamma in
	  if p then
	    raise (Failure "p2psh signing not yet supported")
	  else
	    try
	      let (k,b2,(x2,y2),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = cv) !walletkeys_staking in
              let (_,s1) = repeat_rand (signat_big_int taue k) rand_256 in
	      let s = EndP2pkhToP2pkhSignat(Some(x,y),fcomp,Some(x2,y2),b2,esg,s1) in
	      s
	    with Not_found ->
	      let (k,b2,(x2,y2),w,h,z) = List.find (fun (_,_,_,_,h,_) -> h = cv) !walletkeys_nonstaking in
              let (_,s1) = repeat_rand (signat_big_int taue k) rand_256 in
	      let s = EndP2pkhToP2pkhSignat(Some(x,y),fcomp,Some(x2,y2),b2,esg,s1) in
	      s

let rec script_stack bl stk =
  let (dl,bs) = pop_bytes bl in
  if bs = [] then
    (dl::stk)
  else
    script_stack bs (dl::stk)

let signtx_p2sh_partialsig_2 secrl kl beta taue psig bl stk =
  try
    let (sigssofar,b,x,y,h) = simple_checksig_script bl stk in
    if not (sigssofar = []) then
      (P2shSignat(psig),true)
    else
      let v = signtx_p2pkh kl h taue in
      match v with
      | P2pkhSignat(_,_,(r,s)) ->
	  let sscr = (*** signature script PUSH (0,r,s) PUSH bl ***)
	    push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ psig
	  in
	  (P2shSignat(sscr),true)
      | _ -> raise (Failure "problem signing p2sh case")
  with Not_found ->
    try
      let (sigssofar,redscr,m,n,pkl) = simple_multisig_script bl stk in
      let sigs2 = ref [] in
      let sc = ref 0 in
      if List.length sigssofar < m then
	begin
	  List.iter
	    (fun (b,x,y,h) ->
	      if !sc < m then
		begin
		  try
		    let (rs,r,s) = List.find (fun (_,r,s) -> verify_signed_big_int taue (Some(x,y)) (r,s)) sigssofar in
		    sigs2 := (rs,r,s)::!sigs2;
		    incr sc
		  with Not_found ->
		    try
		      let v = signtx_p2pkh kl h taue in
		      match v with
		      | P2pkhSignat(_,_,(r,s)) ->
			  let zl = 0::blnum_be r 32 @ blnum_be s 32 in
			  sigs2 := (zl,r,s)::!sigs2;
			  incr sc
		      | _ -> raise Not_found
		    with Not_found -> ()
		end)
	    pkl;
	  let psig2 = ref (push_bytes redscr) in
	  List.iter (fun (rs,_,_) -> psig2 := push_bytes rs @ !psig2) !sigs2;
	  (P2shSignat(!psig2),!sc = m)
	end
      else
	raise Not_found
    with Not_found ->
      try
	let (alpha,beta,locktm,rel,secrh) = simple_htlc_script bl stk in (* two cases: we know the secret and the key for alpha, or the key for beta (allowing signing before locktm is reached) *)
	try
	  let (secr,_) = List.find (fun (secr1,secr1h) -> secrh = secr1h) secrl in
	  let v = signtx_p2pkh kl alpha taue in
	  match v with
	  | P2pkhSignat(Some(x,y),b,(r,s)) ->
	      let pubkeybytes = pubkey_bytelist (x,y) b in
	      let secrbytes = be256_bytelist secr in
	      let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH secret PUSH 1 (for IF) PUSH bl ***)
		push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ push_bytes secrbytes @ 0x51::push_bytes bl
	      in
	      (P2shSignat(sscr),true)
	  | _ -> raise Not_found
	with Not_found ->
	  let v = signtx_p2pkh kl beta taue in
	  match v with
	  | P2pkhSignat(Some(x,y),b,(r,s)) ->
	      let pubkeybytes = pubkey_bytelist (x,y) b in
	      let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 0 (for ELSE) PUSH bl ***)
		push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0::push_bytes bl
	      in
	      (P2shSignat(sscr),true)
	  | _ -> raise Not_found
      with Not_found ->
        try
	  let (alpha,beta,locktm,ltxid) = simple_atomicswap_script bl stk in (* two cases: the ltc tx has confirmed or the timelock has passed. *)
          try
            let confs = ltc_tx_confirmed (hashval_hexstring ltxid) in
            match confs with
            | Some(c) when c > 0 ->
               begin
	         let v = signtx_p2pkh kl alpha taue in
                 match v with
	         | P2pkhSignat(Some(x,y),b,(r,s)) ->
	            let pubkeybytes = pubkey_bytelist (x,y) b in
	            let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 1 (for IF) PUSH bl ***)
		      push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0x51::push_bytes bl
	            in
	            (P2shSignat(sscr),true)
	         | _ -> raise Not_found
               end
            | _ -> raise Not_found
          with _ ->
	        let v = signtx_p2pkh kl beta taue in
	        match v with
	        | P2pkhSignat(Some(x,y),b,(r,s)) ->
	           let pubkeybytes = pubkey_bytelist (x,y) b in
	           let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 0 (for ELSE) PUSH bl ***)
		     push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0::push_bytes bl
	           in
	           (P2shSignat(sscr),true)
	        | _ -> raise Not_found
        with Not_found ->
          try
	    let (alpha,beta,locktm,ltxid,n,cltv) = simple_atomicswap_n_script bl stk in (* two cases: the ltc tx has confirmed or the timelock has passed. *)
            try
              let confs = ltc_tx_confirmed (hashval_hexstring ltxid) in
              match confs with
              | Some(c) when c >= n ->
                 begin
	           let v = signtx_p2pkh kl alpha taue in
                   match v with
	           | P2pkhSignat(Some(x,y),b,(r,s)) ->
	              let pubkeybytes = pubkey_bytelist (x,y) b in
	              let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 1 (for IF) PUSH bl ***)
		        push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0x51::push_bytes bl
	              in
	              (P2shSignat(sscr),true)
	           | _ -> raise Not_found
                 end
              | _ -> raise Not_found
            with _ ->
	          let v = signtx_p2pkh kl beta taue in
	          match v with
	          | P2pkhSignat(Some(x,y),b,(r,s)) ->
	             let pubkeybytes = pubkey_bytelist (x,y) b in
	             let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 0 (for ELSE) PUSH bl ***)
		       push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0::push_bytes bl
	             in
	             (P2shSignat(sscr),true)
	          | _ -> raise Not_found
          with Not_found ->
            try
              let (alpha,beta,n,csv) = simple_veto_script bl stk in (** alpha can spend [veto], or after n beta can spend **)
              try
                let v = signtx_p2pkh kl alpha taue in
                match v with
                | P2pkhSignat(Some(x,y),b,(r,s)) ->
                   let pubkeybytes = pubkey_bytelist (x,y) b in
                   let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 1 (for IF) PUSH bl ***)
                     push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0x51::push_bytes bl
                   in
                   (P2shSignat(sscr),true)
                | _ -> raise Not_found
              with Not_found ->
                    let v = signtx_p2pkh kl beta taue in
                    match v with
                    | P2pkhSignat(Some(x,y),b,(r,s)) ->
                       let pubkeybytes = pubkey_bytelist (x,y) b in
                       let sscr = (*** signature script PUSH (0,r,s) PUSH pubkey PUSH 0 (for ELSE) PUSH bl ***)
                         push_bytes (0::blnum_be r 32 @ blnum_be s 32) @ push_bytes pubkeybytes @ 0::push_bytes bl
                       in
                       (P2shSignat(sscr),true)
                    | _ -> raise Not_found
            with Not_found ->
	      raise (Failure "unhandled signtx_p2sh case")	    

let signtx_p2sh_partialsig secrl kl beta taue psig =
  let stk = script_stack psig [] in
  match stk with
  | (bl::stkr) ->
      let beta2 = Script.hash160_bytelist bl in
      if beta2 = beta then
	begin
	  signtx_p2sh_partialsig_2 secrl kl beta taue psig bl stkr
	end
      else
	raise (Failure "partial signature does not have correct redeem script")
  | [] ->
      raise (Failure "partial signature has no redeem script")

let signtx_p2sh_redeemscr secrl kl beta taue bl =
  signtx_p2sh_partialsig secrl kl beta taue (push_bytes bl)

let signtx_p2sh rdmscrl secrl kl beta taue =
  try
    let (bl,_) = List.find (fun (_,alpha) -> alpha = beta) rdmscrl in
    signtx_p2sh_redeemscr secrl kl beta taue bl
  with Not_found ->
    let (_,_,bl) = List.find (fun (alpha,_,_) -> alpha = beta) !walletp2shs in
    signtx_p2sh_redeemscr secrl kl beta taue bl

let getsig s rl =
  match s with
  | GenSignatReal(s) -> (s,fun gam -> (gam,Some(s))::rl)
  | GenSignatRef(i) -> (*** only allow up to 64K signatures on the list; should be much less than this in practice ***)
      if i < 65535 && i >= 0 then
	match List.nth rl i with
	| (gam,Some(s)) -> (s,fun _ -> rl)
	| (gam,None) ->
	    raise BadOrMissingSignature
      else
	raise BadOrMissingSignature

let rec assoc_pos b l p =
  match l with
  | ((x,v)::r) when x = b -> (v,p)
  | (_::r) -> assoc_pos b r (p+1)
  | [] -> raise Not_found

let rec signtx_ins rdmscrl secrl kl taue inpl al outpl sl rl (rsl:gensignat_or_ref option list) ci propowns =
  match inpl,al with
  | (alpha,k)::inpr,(a::ar) ->
      begin
	if not (assetid a = k) then raise (Failure "Asset mismatch when trying to sign inputs");
	match a with
	| (_,_,_,Marker) -> signtx_ins rdmscrl secrl kl taue inpr ar outpl sl rl rsl ci propowns
	| (_,bday,obl,Bounty(_)) ->
	    begin
	      if List.mem alpha propowns then (*** no signature required, bounty is being collected by owner of prop/negprop ***)
		signtx_ins rdmscrl secrl kl taue inpr ar outpl sl rl rsl ci propowns
	      else
		match obl with
		| None -> (*** Bounty cannot be spent, but can only be collected ***)
		    raise (Failure("bad attempt to spend bounty"))
		| Some(gamma,lkh,_) -> (*** gamma must sign to spend bounty where prop (or neg prop) owner is not part of tx ***)
		    begin
		      match sl with
		      | [] -> signtx_ins rdmscrl secrl kl taue inpl al outpl [None] rl rsl ci propowns
		      | (None::sr) -> (*** missing signature ***)
			  begin
			    try
			      match assoc_pos gamma rl 0 with
			      | (Some(s),p) ->
				  signtx_ins rdmscrl secrl kl taue inpr ar outpl sr rl (Some(GenSignatRef(p))::rsl) ci propowns
			      | (None,p) -> raise Not_found
			    with Not_found ->
			      let (p,bv) = gamma in
			      if p then
				raise (Failure "p2sh signing is not yet supported")
			      else
				begin
				  try
				    let s = signtx_p2pkh kl bv taue in
				    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((gamma,Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci propowns
				  with _ ->
				    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((gamma,None)::rl) (None::rsl) false propowns
				end
			  end
		      | (Some(s)::sr) ->
			  try
			    let obl = assetobl a in
			    let (s1,rl1) = getsig s rl in
			    begin
			      let (b,_,_,_,_) = check_spend_obligation_upto_blkh (Some(bday)) alpha taue s1 obl in (*** allow signing now even if it cannot be confirmed until later ***)
			      if b then
				match obl with
				| None -> 
				    let (p,av) = alpha in
				    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 (p=1,av)) (Some(GenSignatReal(s1))::rsl) ci propowns
				| Some(gam,_,_) ->
				    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 gam) (Some(GenSignatReal(s1))::rsl) ci propowns
			      else
				raise (Failure "bad signature already part of stx")
			    end
			  with BadOrMissingSignature ->
			    raise (Failure "bad signature already part of stx")
		    end
	    end
	| (_,bday,obl,_) ->
	    match sl with
	    | [] -> signtx_ins rdmscrl secrl kl taue inpl al outpl [None] rl rsl ci propowns
	    | (None::sr) -> (*** missing signature ***)
		begin
		  (*** check if one of the existing signatures can be used for this ***)
		  try
		    let beta =
		      match obl with
		      | None ->
			  let (p,av) = alpha in
			  (p=1,av)
		      | Some(beta,_,_) -> beta
		    in
		    match assoc_pos beta rl 0 with
		    | (Some(s),p) ->
			signtx_ins rdmscrl secrl kl taue inpr ar outpl sr rl (Some(GenSignatRef(p))::rsl) ci propowns
		    | (None,p) -> raise Not_found
		  with Not_found ->
		    (*** otherwise, try to sign for this input ***)
		    match obl with
		    | Some(beta,lkh,r) ->
			let (p,bv) = beta in
			if p then
			  begin
			    try
			      let (s,compl) = signtx_p2sh rdmscrl secrl kl bv taue in
			      signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((beta,Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci propowns
			    with _ ->
			      signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((beta,None)::rl) (None::rsl) false propowns
			  end
			else
			  begin
			    try
			      let s = signtx_p2pkh kl bv taue in
			      signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((beta,Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci propowns
			    with _ ->
			      signtx_ins rdmscrl secrl kl taue inpr ar outpl sr ((beta,None)::rl) (None::rsl) false propowns
			  end
		    | None ->
		      let (p,av) = alpha in
		      if p = 0 then
			begin
			  try
			    let s = signtx_p2pkh kl av taue in
			    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (((false,av),Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci propowns
			  with _ ->
			    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (((false,av),None)::rl) (None::rsl) false propowns
			end
		      else if p = 1 then
			begin
			  try
			    let (s,compl) = signtx_p2sh rdmscrl secrl kl av taue in
			    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (((true,av),Some(s))::rl) (Some(GenSignatReal(s))::rsl) (ci && compl) propowns
			  with _ ->
			    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (((true,av),None)::rl) (None::rsl) false propowns
			end
		      else
			raise (Failure "tx attempts to spend a non-Marker and non-Bounty without an explicit obligation from an address other than a pay address")

		end
	    | (Some(s)::sr) ->
		try
		  let (s1,rl1) = getsig s rl in
		  let (p,av) = alpha in
		  let (b,_,_,_,_) =
		    try
		      check_spend_obligation_upto_blkh (Some(bday)) alpha taue s1 obl (*** allow signing now even if it cannot be confirmed until later ***)
		    with BadOrMissingSignature ->
		      (false,None,None,None,[])
		  in
		  if b then
		    begin
		      match obl with
		      | None -> 
			  signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 (p=1,av)) (Some(GenSignatReal(s1))::rsl) ci propowns
		      | Some(gam,_,_) ->
			  signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 gam) (Some(GenSignatReal(s1))::rsl) ci propowns
		    end
		  else if check_move_obligation alpha taue s1 obl (assetpre a) outpl then
		    signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 (p=1,av)) (Some(GenSignatReal(s1))::rsl) ci propowns
		  else
		    begin
		      match s1 with
		      | P2shSignat(pscr) -> (*** p2sh, so might be incomplete sig ***)
			  begin
			    match obl with
			    | None -> 
				let (sgscr,compl) =
				  try
				    if p=1 then
				      signtx_p2sh_partialsig secrl kl av taue pscr
				    else
				      (s1,false)
				  with _ -> (s1,false)
				in
				signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 (p=1,av)) (Some(GenSignatReal(sgscr))::rsl) (ci && compl) propowns
			    | Some(gam,_,_) ->
				let (sgscr,compl) =
				  try
				    let (q,cv) = gam in
				    if q then
				      signtx_p2sh_partialsig secrl kl cv taue pscr
				    else
				      (s1,false)
				  with _ -> (s1,false)
				in
				signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 gam) (Some(GenSignatReal(sgscr))::rsl) (ci && compl) propowns
			  end
		      | _ ->
			  begin
			    match obl with
			    | None -> 
				signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 (p=1,av)) (Some(GenSignatReal(s1))::rsl) ci propowns
			    | Some(gam,_,_) ->
				signtx_ins rdmscrl secrl kl taue inpr ar outpl sr (rl1 gam) (Some(GenSignatReal(s1))::rsl) ci propowns
			  end
		    end
		with BadOrMissingSignature ->
		  raise (Failure "bad signature already part of stx")
      end
  | [],[] -> if sl = [] then (List.rev rsl,ci) else raise (Failure "extra unused signature")
  | _,_ -> raise (Failure "problem signing inputs")

let rec signtx_outs rdmscrl secrl kl taue outpl sl rl rsl co =
  let publication_signtx_out alpha outpr =
      begin
	match sl with
	| [] -> signtx_outs rdmscrl secrl kl taue outpl [None] rl rsl co
	| (None::sr) -> (*** missing signature ***)
	    begin
	      let (p,av) = alpha in
	      if p then
		raise (Failure "p2sh signing is not yet supported")
	      else
		begin
		  try
		    let s = signtx_p2pkh kl av taue in
		    signtx_outs rdmscrl secrl kl taue outpr sr ((alpha,Some(s))::rl) (Some(GenSignatReal(s))::rsl) co
		  with _ ->
		    signtx_outs rdmscrl secrl kl taue outpr sr ((alpha,None)::rl) (None::rsl) false
		end
	    end
	| (Some(s)::sr) ->
	    begin
	      let (s1,rl1) = getsig s rl in
	      let (b,_,_,_,_) = check_spend_obligation_upto_blkh None (payaddr_addr alpha) taue s1 None in
	      if b then
		signtx_outs rdmscrl secrl kl taue outpr sr (rl1 alpha) (Some(GenSignatReal(s1))::rsl) co
	      else
		raise (Failure "bad signature already part of stx")
	    end
      end
  in
  match outpl with
  | (_,(_,TheoryPublication(alpha,n,thy)))::outpr ->
      publication_signtx_out alpha outpr
  | (_,(_,SignaPublication(alpha,n,th,si)))::outpr ->
      publication_signtx_out alpha outpr
  | (_,(_,DocPublication(alpha,n,th,si)))::outpr ->
      publication_signtx_out alpha outpr
  | _::outpr -> signtx_outs rdmscrl secrl kl taue outpr sl rl rsl co
  | [] -> (List.rev rsl,co)

let signtx2 oc lr stau rdmscrl secrl kl =
  let ((tauin,tauout) as tau,(tausgin,tausgout)) = stau in
  let unsupportederror alpha h = Printf.fprintf oc "Could not find asset %s at address %s in ledger %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha) (hashval_hexstring lr) in
  let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin (CHash(lr)) unsupportederror) in
  let rec get_propowns tauin al =
    match tauin,al with
    | ((alpha,aid1)::tauinr),((aid2,_,_,OwnsProp(_,_,_))::ar) when aid1 = aid2 -> alpha::get_propowns tauinr ar
    | ((alpha,aid1)::tauinr),((aid2,_,_,OwnsNegProp)::ar) when aid1 = aid2 -> alpha::get_propowns tauinr ar
    | ((_,aid1)::tauinr),((aid2,_,_,_)::ar) when aid1 = aid2 -> get_propowns tauinr ar
    | [],[] -> []
    | _,_ -> raise BadOrMissingSignature (*** actually this means the asset list does not match the inputs ***)
  in
  let tauh = hashtx tau in
  let tauh2 = if !Config.testnet then hashtag tauh 288l else tauh in
  let taue = hashval_big_int tauh2 in
  let (tausgin1,ci) = signtx_ins rdmscrl secrl kl taue tauin al tauout tausgin [] [] true (get_propowns tauin al) in
  let (tausgout1,co) = signtx_outs rdmscrl secrl kl taue tauout tausgout [] [] true in
  ((tau,(tausgin1,tausgout1)),ci,co)

let signbatchtxsc oc lr staul oc2 rdmscrl secrl kl =
  let i = ref 0 in
  List.iter
    (fun stau ->
      incr i;
      let (stau2,ci,co) = signtx2 oc lr stau rdmscrl secrl kl in
      seocf (seo_stx seoc stau2 (oc2,None));
      if ci && co then
	Printf.fprintf oc "Tx %d Completely signed.\n" !i
      else
	Printf.fprintf oc "Tx %d Partially signed.\n" !i)
    staul

let signtxc oc lr stau oc2 rdmscrl secrl kl =
  let (stau2,ci,co) = signtx2 oc lr stau rdmscrl secrl kl in
  seocf (seo_stx seoc stau2 (oc2,None));
  if ci && co then
    Printf.fprintf oc "Completely signed.\n"
  else
    Printf.fprintf oc "Partially signed.\n"

let signtx oc lr taustr rdmscrl secrl kl =
  let s = hexstring_string taustr in
  let (stau,_) = sei_stx seis (s,String.length s,None,0,0) in (*** may be partially signed ***)
  let (stau2,ci,co) = signtx2 oc lr stau rdmscrl secrl kl in
  let s = Buffer.create 100 in
  seosbf (seo_stx seosb stau2 (s,None));
  let hs = string_hexstring (Buffer.contents s) in
  Printf.fprintf oc "%s\n" hs;
  if ci && co then
    Printf.fprintf oc "Completely signed.\n"
  else
    Printf.fprintf oc "Partially signed.\n"

let rec simplesigntx_ins rdmscrl secrl kl taue inpl sl rl (rsl:gensignat_or_ref option list) ci =
  match inpl with
  | (alpha,k)::inpr ->
      begin
	match sl with
	| [] -> simplesigntx_ins rdmscrl secrl kl taue inpl [None] rl rsl ci
	| (None::sr) -> (*** missing signature ***)
	    begin
	      (*** check if one of the existing signatures can be used for this ***)
	      try
		let beta =
		  let (p,av) = alpha in
		  (p=1,av)
		in
		match assoc_pos beta rl 0 with
		| (Some(s),p) ->
		    simplesigntx_ins rdmscrl secrl kl taue inpr sr rl (Some(GenSignatRef(p))::rsl) ci
		| (None,p) -> raise Not_found
	      with Not_found ->
		(*** otherwise, try to sign for this input ***)
		let (p,av) = alpha in
		if p = 0 then
		  begin
		    try
		      let s = signtx_p2pkh kl av taue in
		      simplesigntx_ins rdmscrl secrl kl taue inpr sr (((false,av),Some(s))::rl) (Some(GenSignatReal(s))::rsl) ci
		    with _ ->
		      simplesigntx_ins rdmscrl secrl kl taue inpr sr (((false,av),None)::rl) (None::rsl) false
		  end
		else if p = 1 then
		  begin
		    try
		      let (s,compl) = signtx_p2sh rdmscrl secrl kl av taue in
		      simplesigntx_ins rdmscrl secrl kl taue inpr sr (((true,av),Some(s))::rl) (Some(GenSignatReal(s))::rsl) (ci && compl)
		    with _ ->
		      simplesigntx_ins rdmscrl secrl kl taue inpr sr (((true,av),None)::rl) (None::rsl) false
		  end
		else
		  raise (Failure "tx attempts to spend from an address other than a pay address")
	    end
	| (Some(s)::sr) ->
	    try
	      let (s1,rl1) = getsig s rl in
	      let (p,av) = alpha in
	      begin
		match s1 with
		| P2shSignat(pscr) -> (*** p2sh, so might be incomplete sig ***)
		    begin
		      let (sgscr,compl) =
			try
			  if p=1 then
			    signtx_p2sh_partialsig secrl kl av taue pscr
			  else
			    (s1,false)
			with _ -> (s1,false)
		      in
		      simplesigntx_ins rdmscrl secrl kl taue inpr sr (rl1 (p=1,av)) (Some(GenSignatReal(sgscr))::rsl) (ci && compl)
		    end
		| _ ->
		    simplesigntx_ins rdmscrl secrl kl taue inpr sr (rl1 (p=1,av)) (Some(GenSignatReal(s1))::rsl) ci
	      end
	    with BadOrMissingSignature ->
	      raise (Failure "bad signature already part of stx")
      end
  | [] -> if sl = [] then (List.rev rsl,ci) else raise (Failure "extra unused signature")

let simplesigntx2 oc stau rdmscrl secrl kl =
  let ((tauin,tauout) as tau,(tausgin,tausgout)) = stau in
  let tauh = hashtx tau in
  let tauh2 = if !Config.testnet then hashtag tauh 288l else tauh in
  let taue = hashval_big_int tauh2 in
  let (tausgin1,ci) = simplesigntx_ins rdmscrl secrl kl taue tauin tausgin [] [] true in
  ((tau,(tausgin1,[])),ci,true)

let simplesigntx oc taustr rdmscrl secrl kl =
  let s = hexstring_string taustr in
  let (stau,_) = sei_stx seis (s,String.length s,None,0,0) in (*** may be partially signed ***)
  let (stau2,ci,co) = simplesigntx2 oc stau rdmscrl secrl kl in
  let s = Buffer.create 100 in
  seosbf (seo_stx seosb stau2 (s,None));
  let hs = string_hexstring (Buffer.contents s) in
  Printf.fprintf oc "%s\n" hs;
  if ci && co then
    Printf.fprintf oc "Completely signed.\n"
  else
    Printf.fprintf oc "Partially signed.\n"

let savetxtopool blkh tm lr staustr =
  let s = hexstring_string staustr in
  let (((tauin,tauout) as tau,tausg),_) = sei_stx seis (s,String.length s,None,0,0) in
  if tx_valid tau then
    let unsupportederror alpha h = Printf.printf "Could not find asset %s at address %s in ledger %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha) (hashval_hexstring lr) in
    let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin (CHash(lr)) unsupportederror) in
    begin
      match tx_signatures_valid blkh tm al (tau,tausg) with
      | Some(provenl) -> (** go ahead and put it in the pool whether or not the props are proven; it can't confirm until they're proven **)
         let txid = hashstx (tau,tausg) in
         savetxtopool_real txid (tau,tausg)
      | None ->
         Printf.printf "Invalid or incomplete signatures\n"
    end
  else
    Printf.printf "Invalid tx\n"

let validatetx4 blkh tm thtr sgtr ltr txbytes stau transform =
  let ((tauin,tauout) as tau,tausg) = stau in
  if tx_valid tau then
    begin
      let unsupportederror alpha h = ()
      in
      let retval () =
	if transform then
	  begin
	    try
	      match tx_octree_trans true false blkh tau (Some(ltr)) with
	      | None -> None
	      | Some(ltr2) -> Some(txout_update_ottree tauout thtr,txout_update_ostree tauout sgtr,ltr2)
	    with exn -> None
	  end
	else
	  None
      in
      let validatetx_report provenl =
	let stxh = hashstx stau in
	begin
	  try
	    verbose_supportedcheck := None;
	    let nfee = ctree_supports_tx (ref 0) true true false thtr sgtr blkh provenl tau ltr in
	    verbose_supportedcheck := None;
	    retval()
	  with
	  | NotSupported ->
	      verbose_supportedcheck := None;
	      None
	  | exn ->
	      verbose_supportedcheck := None;
	      None
	end
      in
      let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin ltr unsupportederror) in
      try
	let (mbha,mbhb,mtm,provenl) = tx_signatures_valid_asof_blkh al (tau,tausg) in
        let mbh = if blkh < Utils.lockingfixsoftforkheight then mbha else mbhb in
        validatetx_report provenl
      with
      | BadOrMissingSignature ->
	  validatetx_report []
      | e ->
	  validatetx_report []
    end
  else
    None

let validatetx3 oc blkh tm thtr sgtr ltr txbytes stau transform =
  let ((tauin,tauout) as tau,tausg) = stau in
  if tx_valid_oc oc tau then
    begin
      let unsupportederror alpha h =
        Printf.fprintf oc "Could not find asset %s at address %s in ledger %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha) (hashval_hexstring (ctree_hashroot ltr))
      in
      let retval () =
	if transform then
	  begin
	    try
	      match tx_octree_trans true false blkh tau (Some(ltr)) with
	      | None -> None
	      | Some(ltr2) -> Some(txout_update_ottree tauout thtr,txout_update_ostree tauout sgtr,ltr2)
	    with exn ->
                  Printf.fprintf oc "Tx transformation problem %s\n" (Printexc.to_string exn); flush oc; None
	  end
	else
	  None
      in
      let validatetx_report provenl =
	let stxh = hashstx stau in
	Printf.fprintf oc "Tx is valid and has id %s\n" (hashval_hexstring stxh);
	begin
	  try
	    verbose_supportedcheck := Some(oc);
	    let nfee = ctree_supports_tx (ref 0) true true false thtr sgtr blkh provenl tau ltr in
	    verbose_supportedcheck := None;
	    let minfee = Int64.mul (Int64.of_int txbytes) !Config.minrelayfee in
	    let fee = Int64.sub 0L nfee in
	    if fee < 0L then
              Printf.fprintf oc "Tx is supported by the current ledger and but requires %s bars more input.\n" (Cryptocurr.bars_of_atoms (Int64.neg fee))
	    else if fee >= minfee then
	      Printf.fprintf oc "Tx is supported by the current ledger and has fee %s bars (above minrelayfee %s bars)\n" (Cryptocurr.bars_of_atoms fee) (Cryptocurr.bars_of_atoms minfee)
            else
	      Printf.fprintf oc "Tx is supported by the current ledger and has fee %s bars (below minrelayfee %s bars)\n" (Cryptocurr.bars_of_atoms fee) (Cryptocurr.bars_of_atoms minfee);
	    flush oc;
	    retval()
	  with
	  | NotSupported ->
	      verbose_supportedcheck := None;
	      Printf.fprintf oc "Tx is not supported by the current ledger\n";
	      flush oc;
	      None
	  | exn ->
	      verbose_supportedcheck := None;
	      Printf.fprintf oc "Tx is not supported by the current ledger: %s\n" (Printexc.to_string exn);
	      flush oc;
	      None
	end
      in
      let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin ltr unsupportederror) in
      try
	let (mbha,mbhb,mtm,provenl) = tx_signatures_valid_asof_blkh al (tau,tausg) in
        let mbh = if blkh < Utils.lockingfixsoftforkheight then mbha else mbhb in
	match (mbh,mtm) with
	| (None,None) -> validatetx_report provenl
	| (Some(bh2),None) ->
	    if bh2 > blkh then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld\n" bh2;
		flush oc
	      end;
	    validatetx_report provenl
	| (None,Some(tm2)) ->
	    if tm2 > tm then
	      begin
		Printf.fprintf oc "Tx is not valid until time %Ld\n" tm2;
		flush oc
	      end;
	    validatetx_report provenl
	| (Some(bh2),Some(tm2)) ->
	    if (bh2 > blkh) && (tm2 > tm) then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld and time %Ld\n" bh2 tm2;
		flush oc
	      end
	    else if bh2 > blkh then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld\n" bh2;
		flush oc
	      end
	    else if tm2 > tm then
	      begin
		Printf.fprintf oc "Tx is not valid until time %Ld\n" tm2;
		flush oc
	      end;
	    validatetx_report provenl
      with
      | BadOrMissingSignature ->
	  Printf.fprintf oc "Invalid or incomplete signatures\n";
	  validatetx_report []
      | e ->
	  Printf.fprintf oc "Exception: %s\n" (Printexc.to_string e);
	  validatetx_report []
    end
  else
    (Printf.fprintf oc "Invalid tx\n"; None)

let validatetx2 oc blkh tm tr sr lr txbytes stau =
  match oc with
  | Some(oc) ->
     ignore (validatetx3 oc blkh tm (lookup_thytree tr) (lookup_sigtree sr) (CHash(lr)) txbytes stau false)
  | None ->
     ignore (validatetx4 blkh tm (lookup_thytree tr) (lookup_sigtree sr) (CHash(lr)) txbytes stau false)

let validatebatchtxs oc blkh tm tr sr lr staul =
  let i = ref 0 in
  let thtr = ref (lookup_thytree tr) in
  let sgtr = ref (lookup_sigtree sr) in
  let ltr = ref (CHash(lr)) in
  try
    List.iter
      (fun stau ->
	incr i;
	Printf.fprintf oc "Validating tx %d\n" !i;
	match validatetx3 oc blkh tm !thtr !sgtr !ltr (stxsize stau) stau true with
	| Some(thtr2,sgtr2,ltr2) ->
	    thtr := thtr2;
	    sgtr := sgtr2;
	    ltr := ltr2
	| None ->
	    Printf.fprintf oc "Cannot continue validating tx.\n";
	    raise Exit)
      staul
  with Exit -> ()

let validatetx oc blkh tm tr sr lr staustr =
  let s = hexstring_string staustr in
  let l = String.length s in
  let (stau,_) = sei_stx seis (s,l,None,0,0) in
  validatetx2 (Some(oc)) blkh tm tr sr lr l stau

let sendtx2 oc blkh tm tr sr lr txbytes stau =
  let ((tauin,tauout) as tau,tausg) = stau in
  if tx_valid tau then
    begin
      let unsupportederror alpha h = Printf.fprintf oc "Could not find asset %s at address %s in ledger %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha) (hashval_hexstring lr) in
      let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin (CHash(lr)) unsupportederror) in
      try
	let (mbha,mbhb,mtm,provenl) = tx_signatures_valid_asof_blkh al (tau,tausg) in
        let mbh = if blkh < Utils.lockingfixsoftforkheight then mbha else mbhb in
	let sendtxreal () =
	  let stxh = hashstx stau in
	  begin
	    try
	      let minfee = Int64.mul (Int64.of_int txbytes) !Config.minrelayfee in
	      let nfee = ctree_supports_tx (ref 0) true true false (lookup_thytree tr) (lookup_sigtree sr) blkh provenl tau (CHash(lr)) in
	      let fee = Int64.sub 0L nfee in
	      if fee >= minfee then
		begin
		  savetxtopool_real stxh stau;
		  publish_stx stxh stau;
		  Printf.fprintf oc "%s\n" (hashval_hexstring stxh);
		end
	      else
		Printf.fprintf oc "Tx is supported by the current ledger, but has too low fee of %s bars (below minrelayfee %s bars)\n" (Cryptocurr.bars_of_atoms fee) (Cryptocurr.bars_of_atoms minfee);
	      flush oc
	    with
	    | NotSupported ->
		Printf.fprintf oc "Tx is not supported by the current ledger\n";
		flush oc;
	    | exn ->
		Printf.fprintf oc "Tx is not supported by the current ledger: %s\n" (Printexc.to_string exn);
		flush oc;
	  end
	in
	match (mbh,mtm) with
	| (None,None) ->
	    let stxh = hashstx stau in
	    savetxtopool_real stxh stau;
	    publish_stx stxh stau;
	    Printf.fprintf oc "%s\n" (hashval_hexstring stxh);
	    flush stdout;
	| (Some(bh2),None) ->
	    if bh2 > blkh then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld\n" bh2;
		flush stdout
	      end
	    else
	      sendtxreal()
	| (None,Some(tm2)) ->
	    if tm2 > tm then
	      begin
		Printf.fprintf oc "Tx is not valid until time %Ld\n" tm2;
		flush stdout
	      end
	    else
	      sendtxreal()
	| (Some(bh2),Some(tm2)) ->
	    if bh2 > blkh && tm2 > tm then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld and time %Ld\n" bh2 tm2;
		flush stdout
	      end
	    else if bh2 > blkh then
	      begin
		Printf.fprintf oc "Tx is not valid until block height %Ld\n" bh2;
		flush stdout
	      end
	    else if tm2 > tm then
	      begin
		Printf.fprintf oc "Tx is not valid until time %Ld\n" tm2;
		flush stdout
	      end
	    else
	      sendtxreal()
      with BadOrMissingSignature ->
	Printf.fprintf oc "Invalid or incomplete signatures\n"
    end
  else
    Printf.fprintf oc "Invalid tx\n"

let sendtx oc blkh tm tr sr lr staustr =
  let s = hexstring_string staustr in
  let l = String.length s in
  if l > 450000 then raise (Failure "refusing to send tx bigger than 450K bytes");
  let (stau,_) = sei_stx seis (s,l,None,0,0) in
  sendtx2 oc blkh tm tr sr lr l stau

(*** should gather historic information as well ***)
let proofgold_addr_jsoninfo raiseempty alpha pbh ledgerroot blkh =
  let (jpbh,par) =
    match pbh with
    | None -> (JsonObj([("block",JsonStr("genesis"))]),None)
    | Some(prevh,Poburn(lblkh,ltxh,lmedtm,burned,txid1,vout1)) ->
	begin
	  let jpbh = JsonObj([("block",JsonStr(hashval_hexstring prevh));
			      ("height",JsonNum(Int64.to_string blkh));
			      ("ltcblock",JsonStr(hashval_hexstring lblkh));
			      ("ltcburntx",JsonStr(hashval_hexstring ltxh));
			      ("ltcmedtm",JsonNum(Int64.to_string lmedtm));
			      ("ltcburned",JsonNum(Int64.to_string burned));
                              ("txid1",JsonStr(hashval_hexstring txid1));
                              ("vout1",JsonNum(Int32.to_string vout1))])
	  in
	  (jpbh,Some(lblkh,ltxh))
	end
  in
  let (jal,jwl) = assets_at_address_in_ledger_json raiseempty alpha par ledgerroot blkh in
  try
    let ph = Hashtbl.find term_addr_hashval alpha in
    try
      let conjpub = Hashtbl.find (if !term_info_refreshing then propid_conj_pub_bkp else propid_conj_pub) ph in
      if jwl = [] then
        JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::("preimagehash",JsonStr(hashval_hexstring ph))::("conjpub",JsonStr(addr_pfgaddrstr conjpub))::jal)
      else
        JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::("warnings",JsonArr(jwl))::("preimagehash",JsonStr(hashval_hexstring ph))::("conjpub",JsonStr(addr_pfgaddrstr conjpub))::jal)
    with Not_found ->
      if jwl = [] then
        JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::("preimagehash",JsonStr(hashval_hexstring ph))::jal)
      else
        JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::("warnings",JsonArr(jwl))::("preimagehash",JsonStr(hashval_hexstring ph))::jal)
  with Not_found ->
    if jwl = [] then
      JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::jal)
    else
      JsonObj(("ledgerroot",JsonStr(hashval_hexstring ledgerroot))::("block",jpbh)::("warnings",JsonArr(jwl))::jal)

let query_at_block q pbh ledgerroot blkh =
  if String.length q = 64 || String.length q = 40 then
    begin
      try
	let q = if String.length q = 64 then q else "000000000000000000000000" ^ q in
	let h = hexstring_hashval q in
	let dbentries = ref [] in
	let blkh = Int64.sub blkh 1L in
	begin
	  try
	    let e = Assets.DbAsset.dbget h in
	    let s = Buffer.create 100 in
	    print_hlist_to_buffer s blkh (HCons(e,HNil));
	    let j = json_asset e in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
	begin
	  try
	    let alpha = Assets.DbAssetIdAt.dbget h in
	    let j = proofgold_addr_jsoninfo true alpha pbh ledgerroot blkh in
	    dbentries := j::!dbentries
	  with
	  | EmptyAddress -> ()
	  | Not_found -> ()
	end;
	begin
	  try
	    let e = Tx.DbSTx.dbget h in
	    let j = json_stx e in
	    dbentries := j::!dbentries
	  with Not_found ->
	    try
	      let e = Hashtbl.find stxpool h in
	      let j = json_stx e in
	      dbentries := j::!dbentries
	    with Not_found ->
	      ()
	end;
	begin
	  try
	    let (k,r) = Ctre.DbHConsElt.dbget h in
	    let j =
	      match r with
	      | None ->
		  JsonObj([("type",JsonStr("hconselt"));("asset",JsonStr(hashval_hexstring k))])
	      | Some(r,l) ->
		  JsonObj([("type",JsonStr("hconselt"));("asset",JsonStr(hashval_hexstring k));("next",JsonStr(hashval_hexstring r));("nextlen",JsonStr(string_of_int l))])
	    in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
	begin
	  try
	    let e = expand_ctree_atom_or_element false h in
	    let j = JsonObj([("type",JsonStr("ctreeelt"));("ctree",json_ctree(e))]) in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
	begin
	  try
	    let (bhd,bhs) = DbBlockHeader.dbget h in
	    let invalid = DbInvalidatedBlocks.dbexists h in
	    let pbh = bhd.prevblockhash in
	    let alpha = bhd.stakeaddr in
	    let aid = bhd.stakeassetid in
	    let timestamp = bhd.timestamp in
	    let deltatime = bhd.deltatime in
	    let tinfo = bhd.tinfo in
	    let bblkh =
	      try
		match pbh with
		| Some(_,Poburn(plbk,pltx,_,_,_,_)) ->
		    let (_,_,_,_,_,_,pblkh) = Db_outlinevals.dbget (hashpair plbk pltx) in
		    Some(Int64.add pblkh 1L)
		| None -> Some(1L)
	      with Not_found ->
		None
	    in
	    let jpb =
	      match pbh with
	      | None -> []
	      | Some(prevh,Poburn(lblkh,ltxh,lmedtm,burned,txid1,vout1)) ->
		  match bblkh with
		  | Some(bblkh) ->
		      [("height",JsonNum(Int64.to_string bblkh));
		        ("prevblock",
			 JsonObj([("block",JsonStr(hashval_hexstring prevh));
				  ("ltcblock",JsonStr(hashval_hexstring lblkh));
				  ("ltcburntx",JsonStr(hashval_hexstring ltxh));
				  ("ltcmedtm",JsonNum(Int64.to_string lmedtm));
				  ("ltcburned",JsonNum(Int64.to_string burned));
                                  ("txid1",JsonStr(hashval_hexstring txid1));
                                  ("vout1",JsonNum(Int32.to_string vout1))]))]
		  | None ->
		      [("prevblock",
			JsonObj([("block",JsonStr(hashval_hexstring prevh));
				 ("ltcblock",JsonStr(hashval_hexstring lblkh));
				 ("ltcburntx",JsonStr(hashval_hexstring ltxh));
				 ("ltcmedtm",JsonNum(Int64.to_string lmedtm));
				 ("ltcburned",JsonNum(Int64.to_string burned));
                                 ("txid1",JsonStr(hashval_hexstring txid1));
                                 ("vout1",JsonNum(Int32.to_string vout1))]))]
	    in
	    let jr =
	      jpb @
	      [("stakeaddress",JsonStr(addr_pfgaddrstr (p2pkhaddr_addr alpha)));
	       ("timestamp",JsonNum(Int64.to_string timestamp));
	       ("deltatime",JsonNum(Int32.to_string deltatime));
	       ("prevledgerroot",JsonStr(hashval_hexstring (ctree_hashroot bhd.prevledger)));
	       ("newledgerroot",JsonStr(hashval_hexstring bhd.newledgerroot));
	       ("target",JsonStr(string_of_big_int tinfo));
	       ("difficulty",JsonStr(string_of_big_int (difficulty tinfo)))]
	    in
            let jr =
              match bhd.pureburn with
              | Some(h,v) -> ("pureburn",JsonObj([("txid1",JsonStr(hashval_hexstring h));("vout1",JsonNum(Int32.to_string v))]))::jr
              | None -> ("stakeassetid",JsonStr(hashval_hexstring aid))::jr
            in
	    let jr =
	      match bhd.newtheoryroot with
	      | Some(r) -> ("newtheoryroot",JsonStr(hashval_hexstring r))::jr
	      | None -> jr
	    in
	    let jr =
	      match bhd.newsignaroot with
	      | Some(r) -> ("newsignaroot",JsonStr(hashval_hexstring r))::jr
	      | None -> jr
	    in
	    let jr =
	      if invalid then
		(("invalid",JsonBool(true))::jr)
	      else
		jr
	    in
	    begin
	      try
		let bd = Block.DbBlockDelta.dbget h in
		let jcoinstk = json_tx(coinstake ((bhd,bhs),bd)) in
		let jtxhl =
		  List.map
		    (fun (tau,stau) -> JsonStr(hashval_hexstring(hashstx (tau,stau))))
		    bd.blockdelta_stxl
		in
		let j = JsonObj(("type",JsonStr("block"))::jr @ [("coinstk",jcoinstk);("txs",JsonArr(jtxhl))]) in
		dbentries := j::!dbentries
	      with Not_found ->
		let j = JsonObj(("type",JsonStr("block"))::jr) in
		dbentries := j::!dbentries
	    end
	  with Not_found -> ()
	end;
(***
	begin
	  try
	    let e = Ltcrpc.DbLtcPfgStatus.dbget h in
	    let j = JsonObj([("type",JsonStr("ltcblock"))]) in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
***)
	begin
	  try
	    let (burned,lprevtx,dnxt,txid1,vout1) = DbLtcBurnTx.dbget h in
	    let j = JsonObj([("type",JsonStr("ltcburntx"));
			     ("burned",JsonNum(Int64.to_string burned));
			     ("previousltcburntx",JsonStr(hashval_hexstring lprevtx));
			     ("pfgblock",JsonStr(hashval_hexstring dnxt));
                             ("txid1",JsonStr(hashval_hexstring txid1));
                             ("vout1",JsonNum(Int32.to_string vout1))]) in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
	begin
	  try
	    let (prevh,tm,hght,txhhs) = DbLtcBlock.dbget h in
	    let j = JsonObj([("type",JsonStr("ltcblock"));
			     ("tm",JsonNum(Int64.to_string tm));
			     ("height",JsonNum(Int64.to_string hght));
			     ("txhhs",JsonArr(List.map (fun txh -> JsonStr(hashval_hexstring txh)) txhhs))]) in
	    dbentries := j::!dbentries
	  with Not_found -> ()
	end;
	begin
	  try
            let d = termaddr_addr (hashval_be160 h) in
            let j = proofgold_addr_jsoninfo true d pbh ledgerroot blkh in
	    dbentries := JsonObj([("type",JsonStr("termid"));("termaddress",JsonStr(addr_pfgaddrstr d));("termaddressinfo",j)])::!dbentries;
	  with EmptyAddress -> ()
	end;
        (* This would give the contents of the address of the publication, but it seems we never query it this way.
	begin
	  try
            let d = pubaddr_addr (hashval_be160 h) in
            let j = proofgold_addr_jsoninfo true d pbh ledgerroot blkh in
	    dbentries := JsonObj([("type",JsonStr("pubid"));("pubaddress",JsonStr(addr_pfgaddrstr d));("contents",j)])::!dbentries;
	  with EmptyAddress -> ()
	end;
         *)
        begin
          try
            let m = Hashtbl.find term_info_hf h in
            match m with
            | Prim(i) ->
               dbentries := JsonObj([("type",JsonStr("termroot"));("hfbuiltin",JsonBool(true));("hfprimnum",JsonNum(Printf.sprintf "%d" i));("primname",JsonStr(Mathdata.hfprimnamesa.(i)))])::!dbentries
            | _ ->
               dbentries := JsonObj([("type",JsonStr("termroot"));("hfbuiltin",JsonBool(true));("trmpres",JsonStr(Mathdata.mghtml_nice_trm (Some(Mathdata.hfthyroot)) m))])::!dbentries;
          with Not_found -> ()
        end;
        begin
          try
            let (a,tmroot,m) = Hashtbl.find obj_info_hf h in
            let names = Hashtbl.find_all mglegend h in
            dbentries := JsonObj([("type",JsonStr("obj"));("hfbuiltin",JsonBool(true));("stppres",JsonStr(Mathdata.mghtml_nice_stp (Some(Mathdata.hfthyroot)) a));("trmpres",JsonStr(Mathdata.mghtml_nice_trm (Some(Mathdata.hfthyroot)) m));("termroot",JsonStr(hashval_hexstring tmroot));("defaultnames",JsonArr(List.map (fun x -> JsonStr(x)) names))])::!dbentries
          with Not_found -> ()
        end;
        begin
          try
            let (tmroot,m) = Hashtbl.find prop_info_hf h in
            let names = Hashtbl.find_all mglegendp h in
            dbentries := JsonObj([("type",JsonStr("prop"));("hfbuiltin",JsonBool(true));("trmpres",JsonStr(Mathdata.mghtml_nice_trm (Some(Mathdata.hfthyroot)) m));("termroot",JsonStr(hashval_hexstring tmroot));("defaultnames",JsonArr(List.map (fun x -> JsonStr(x)) names))])::!dbentries
          with Not_found -> ()
        end;
        begin
          try
            let (ah,pfgbh,otx) = Hashtbl.find (if !asset_id_hash_refreshing then asset_id_hash_table_bkp else asset_id_hash_table) h in
            match otx with
            | None ->
               dbentries := JsonObj([("type",JsonStr("assetid"));("assethash",JsonStr(hashval_hexstring ah));("block",JsonStr(hashval_hexstring pfgbh))])::!dbentries
            | Some(txid) ->
               dbentries := JsonObj([("type",JsonStr("assetid"));("assethash",JsonStr(hashval_hexstring ah));("block",JsonStr(hashval_hexstring pfgbh));("tx",JsonStr(hashval_hexstring txid))])::!dbentries
          with Not_found -> ()
        end;
        List.iter
          (fun (m,aid,thyh,pfgbh,otx,isprop,objorpropid) ->
            let thystr =
              match thyh with
              | Some(h) ->
                 [("theory",JsonStr(hashval_hexstring h));("theorynames",JsonArr(List.map (fun x -> JsonStr(x)) (Hashtbl.find_all Mathdata.mglegendt h)))]
              | None -> []
            in
            let txstr =
              match otx with
              | Some(txid) -> [("tx",JsonStr(hashval_hexstring txid))]
              | None -> [("block",JsonStr(hashval_hexstring pfgbh))]
            in
            let creatorobj =
              try
                let (aid,bday,beta) = Hashtbl.find created_obj_info h in
                [("creatorasobj",JsonObj([("creatoraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let ownerobj =
              try
                let (aid,bday,beta,gamma,r) = Hashtbl.find owns_obj_info h in
                [("ownerasobj",JsonObj([("owneraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let creatorprop =
              try
                let (aid,bday,beta) = Hashtbl.find created_prop_info h in
                [("creatorasprop",JsonObj([("creatoraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let ownerprop =
              try
                let (aid,bday,beta,gamma,r) = Hashtbl.find owns_prop_info h in
                [("ownerasprop",JsonObj([("owneraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let objorpropinfo =
              if isprop then
                [("correspondingprop",JsonStr(hashval_hexstring objorpropid))]
              else
                [("correspondingobj",JsonStr(hashval_hexstring objorpropid))]
            in
            let al = thystr @ txstr @ creatorobj @ ownerobj @ creatorprop @ ownerprop @ objorpropinfo in
            let al =
              match m with
              | Logic.Prim(i) -> ("primnum",JsonNum(string_of_int i))::al
              | _ -> al
            in
            let al = ("trmpres",JsonStr(Mathdata.mghtml_nice_trm thyh m))::al in
            let al = ("type",JsonStr("termroot"))::al in
            dbentries := JsonObj(al)::!dbentries)
          (Hashtbl.find_all (if !term_info_refreshing then term_info_bkp else term_info) h);
        List.iter
          (fun (thyh,a,tmroot,m,prim,alpha) ->
            let creatorobj =
              try
                let (aid,bday,beta) = Hashtbl.find created_obj_info h in
                [("creatorasobj",JsonObj([("creatoraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let ownerobj =
              try
                let (aid,bday,beta,gamma,r) = Hashtbl.find owns_obj_info h in
                [("ownerasobj",JsonObj([("owneraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let thyinfo =
              match thyh with
              | Some(h) ->
                 [("theory",JsonStr(hashval_hexstring h));("theorynames",JsonArr(List.map (fun x -> JsonStr(x)) (Hashtbl.find_all Mathdata.mglegendt h)))]
              | None -> []
            in
            let al = thyinfo @ creatorobj @ ownerobj in
            let al = ("firstpubaddr",JsonStr(addr_pfgaddrstr alpha))::al in
            let al = ("trmpres",JsonStr(Mathdata.mghtml_nice_trm thyh m))::al in
            let al = ("stppres",JsonStr(Mathdata.mghtml_nice_stp thyh a))::al in
            let al =
              match m with
              | Prim(i) -> ("primnum",JsonNum(string_of_int i))::al
              | _ -> al
            in
            let al = ("termroot",JsonStr(hashval_hexstring tmroot))::al in
            let d = termaddr_addr (hashval_be160 h) in
            let al = ("termaddress",JsonStr(addr_pfgaddrstr d))::al in
            let names = Hashtbl.find_all mglegend h in
            let al = ("defaultnames",JsonArr(List.map (fun x -> JsonStr(x)) names))::al in
            let al = ("type",JsonStr("obj"))::al in
            dbentries := JsonObj(al)::!dbentries)
          (Hashtbl.find_all (if !term_info_refreshing then obj_info_bkp else obj_info) h);
        List.iter
          (fun (thyh,tmroot,m,prim,alpha) ->
            let creatorprop =
              try
                let (aid,bday,beta) = Hashtbl.find created_prop_info h in
                [("creatorasprop",JsonObj([("creatoraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let ownerprop =
              try
                let (aid,bday,beta,gamma,r) = Hashtbl.find owns_prop_info h in
                [("ownerasprop",JsonObj([("owneraddr",JsonStr(addr_pfgaddrstr (payaddr_addr beta)));("assetid",JsonStr(hashval_hexstring aid));("bday",JsonNum(Printf.sprintf "%Ld" bday))]))]
              with Not_found -> []
            in
            let thyinfo =
              match thyh with
              | Some(h) ->
                 [("theory",JsonStr(hashval_hexstring h));("theorynames",JsonArr(List.map (fun x -> JsonStr(x)) (Hashtbl.find_all Mathdata.mglegendt h)))]
              | None -> []
            in
            let al = thyinfo @ creatorprop @ ownerprop in
            let al = ("firstpubaddr",JsonStr(addr_pfgaddrstr alpha))::al in
            let al = ("termroot",JsonStr(hashval_hexstring tmroot))::al in
            let al = ("trmpres",JsonStr(Mathdata.mghtml_nice_trm thyh m))::al in
            let al =
              match m with
              | Prim(i) -> ("primnum",JsonNum(string_of_int i))::al
              | _ -> al
            in
            let d = termaddr_addr (hashval_be160 h) in
            let al = ("termaddress",JsonStr(addr_pfgaddrstr d))::al in
            let names = Hashtbl.find_all mglegendp h in
            let al = ("defaultnames",JsonArr(List.map (fun x -> JsonStr(x)) names))::al in
            let al = ("type",JsonStr("prop"))::al in
            dbentries := JsonObj(al)::!dbentries)
          (Hashtbl.find_all (if !term_info_refreshing then prop_info_bkp else prop_info) h);
	if !dbentries = [] then
	  JsonObj([("response",JsonStr("unknown"));("msg",JsonStr("No associated information found"))])
	else
	  JsonObj([("response",JsonStr("known"));("dbdata",JsonArr(!dbentries))])
      with exn ->
	JsonObj([("response",JsonStr("unknown"));("msg",JsonStr("Cannot interpret as hash value" ^ Printexc.to_string exn))])
    end
  else
    begin
      try
	let d = pfgaddrstr_addr q in
	let j = proofgold_addr_jsoninfo false d pbh ledgerroot blkh in
	JsonObj([("response",JsonStr("pfgaddress"));("info",j)])
      with _ ->
	try
	  let b = btcaddrstr_addr q in
	  let j = proofgold_addr_jsoninfo false b pbh ledgerroot blkh in
	  let d = addr_pfgaddrstr b in
	  JsonObj([("response",JsonStr("bitcoin address"));("pfgaddress",JsonStr(d));("info",j)])
	with _ ->
	  JsonObj([("response",JsonStr("unknown"));("msg",JsonStr("Cannot interpret as proofgold value"))])
    end

let query q =
  match !artificialledgerroot with
  | Some(ledgerroot) ->
      query_at_block q None ledgerroot (-1L)
  | None ->
      try
	let (b,cwl) = get_bestblock() in
	match b with
	| Some(_,lbk,ltx) ->
	    let (bh,lmedtm,burned,(txid1,vout1),_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let pbh = Some(bh,Poburn(lbk,ltx,lmedtm,burned,txid1,vout1)) in
	    let (_,_,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    query_at_block q pbh ledgerroot blkh
	| None -> JsonObj([("response",JsonStr("no best block found"))])
      with Not_found -> JsonObj([("response",JsonStr("no best block found"))])

let query_blockheight findblkh =
  if findblkh < 1L then
    JsonObj([("response",JsonStr("no block at height < 1"))])
  else
    let (b,cwl) = get_bestblock() in
    match b with
    | None -> JsonObj([("response",JsonStr("no block at height " ^ (Int64.to_string findblkh)))])
    | Some(_,lbk,ltx) ->
	begin
	  try
	    let rec query_blockheight_search lbk ltx =
	      let (bh,lmedtm,burned,(txid1,vout1),par,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	      if blkh = findblkh then
		let (_,_,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
		query_at_block (hashval_hexstring bh) (Some(bh,Poburn(lbk,ltx,lmedtm,burned,txid1,vout1))) ledgerroot blkh
	      else if blkh < findblkh then
		JsonObj([("response",JsonStr("no block at height " ^ (Int64.to_string findblkh)))])
	      else
		match par with
		| Some(lbk,ltx) ->
		    query_blockheight_search lbk ltx
		| None ->
		    JsonObj([("response",JsonStr("no block at height " ^ (Int64.to_string findblkh)))])
	    in
	    query_blockheight_search lbk ltx
	  with Not_found ->
	    JsonObj([("response",JsonStr("no block at height " ^ (Int64.to_string findblkh)))])
	end

let preassetinfo_report oc u =
  match u with
  | Currency(v) ->
      Printf.fprintf oc "Currency: %s bars (%Ld atoms)\n" (bars_of_atoms v) v
  | Bounty(v) ->
      Printf.fprintf oc "Bounty: %s bars (%Ld atoms)\n" (bars_of_atoms v) v
  | OwnsObj(h,alpha,None) ->
      Printf.fprintf oc "Ownership deed for object with id %s (which must be held at address %s).\n" (hashval_hexstring h) (addr_pfgaddrstr (termaddr_addr (hashval_be160 h)));
      Printf.fprintf oc "Rights to import the object cannot be purchased. It must be redefined in new documents.\n";
  | OwnsObj(h,alpha,Some(r)) ->
      Printf.fprintf oc "Ownership deed for object with id %s (which must be held at address %s).\n" (hashval_hexstring h) (addr_pfgaddrstr (termaddr_addr (hashval_be160 h)));
      if r = 0L then
	Printf.fprintf oc "The object can be freely imported into documents and signatures.\n"
      else
	Printf.fprintf oc "Each right to import the object into a document costs %s bars (%Ld atoms), payable to %s.\n" (bars_of_atoms r) r (addr_pfgaddrstr (payaddr_addr alpha))
  | OwnsProp(h,alpha,r) ->
      Printf.fprintf oc "Ownership deed for proposition with id %s (which must be held at address %s).\n" (hashval_hexstring h) (addr_pfgaddrstr (termaddr_addr (hashval_be160 h)));
      Printf.fprintf oc "Rights to import the proposition cannot be purchased. It must be reproven in new documents.\n";
  | OwnsNegProp ->
      Printf.fprintf oc "Ownership deed for negation of proposition, controlled by whomever proved negation of proposition.\n"
  | RightsObj(h,v) ->
      Printf.fprintf oc "%Ld rights to import object with id %s into documents.\n" v (hashval_hexstring h)
  | RightsProp(h,v) ->
      Printf.fprintf oc "%Ld rights to import proposition with id %s into documents.\n" v (hashval_hexstring h)
  | Marker ->
      Printf.fprintf oc "Marker committing to publish a document, theory or signature with fixed contents.\n"
  | TheoryPublication(alpha,nonce,ts) ->
      Printf.fprintf oc "Theory specification with publisher %s\n" (addr_pfgaddrstr (payaddr_addr alpha));
      begin
	let th = Mathdata.theoryspec_theory ts in
	match Mathdata.hashtheory th with
	| Some(thyh) ->
	    let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr alpha)) (hashpair nonce thyh)) in
	    Printf.fprintf oc "Theory must be published to address %s\n" (addr_pfgaddrstr (hashval_pub_addr thyh));
	    Printf.fprintf oc "and can only be published by spending a Marker at least 4 blocks old held at %s.\n" (addr_pfgaddrstr beta);
	    Printf.fprintf oc "Publishing theory requires burning %s bars.\n" (bars_of_atoms (Mathdata.theory_burncost th))
	| None ->
	    Printf.fprintf oc "Theory seems to be empty and cannot be published.\n"
      end
  | SignaPublication(alpha,nonce,thyid,ss) ->
      Printf.fprintf oc "Signature specification in %s with publisher %s\n"
	(match thyid with None -> "the empty theory" | Some(h) -> "theory " ^ (hashval_hexstring h))
	(addr_pfgaddrstr (payaddr_addr alpha));
      let s = Mathdata.signaspec_signa ss in
      let slh = Mathdata.hashsigna s in
      let tslh = hashopair2 thyid slh in
      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr alpha)) (hashpair nonce tslh)) in
      Printf.fprintf oc "Signature must be published to address %s\n" (addr_pfgaddrstr (hashval_pub_addr tslh));
      Printf.fprintf oc "and can only be published by spending a Marker at least 4 blocks old held at %s.\n" (addr_pfgaddrstr beta);
      Printf.fprintf oc "Publishing signature requires burning %s bars.\n" (bars_of_atoms (Mathdata.signa_burncost s));
      let usesobjs = Mathdata.signaspec_uses_objs ss in
      let usesprops = Mathdata.signaspec_uses_props ss in
      if not (usesobjs = []) then
	begin
	  Printf.fprintf oc "2*%d rights required to use objects must be consumed:\n" (List.length usesprops);
	  List.iter
	    (fun (h,k) ->
	      Printf.fprintf oc "Right to use (pure) object %s (%s)\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid (hashpair h k)) 32l in
	      Printf.fprintf oc "Right to use (theory) object %s (%s)\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    usesobjs
	end;
      if not (usesprops = []) then
	begin
	  Printf.fprintf oc "2*%d rights required to use propositions must be consumed:\n" (List.length usesprops);
	  List.iter
	    (fun h ->
	      Printf.fprintf oc "Right to use (pure) proposition %s (%s)\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid h) 33l in
	      Printf.fprintf oc "Right to use (theory) proposition %s (%s)\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    usesprops
	end
  | DocPublication(alpha,nonce,thyid,dl) ->
      Printf.fprintf oc "Document in %s with publisher %s\n"
	(match thyid with None -> "the empty theory" | Some(h) -> "theory " ^ (hashval_hexstring h))
	(addr_pfgaddrstr (payaddr_addr alpha));
      let dlh = Mathdata.hashdoc dl in
      let tdlh = hashopair2 thyid dlh in
      let beta = hashval_pub_addr (hashpair (hashaddr (payaddr_addr alpha)) (hashpair nonce tdlh)) in
      Printf.fprintf oc "Document must be published to address %s\n" (addr_pfgaddrstr (hashval_pub_addr tdlh));
      Printf.fprintf oc "and can only be published by spending a Marker at least 4 blocks old held at %s.\n" (addr_pfgaddrstr beta);
      let usesobjs = Mathdata.doc_uses_objs dl in
      let usesprops = Mathdata.doc_uses_props dl in
      let createsobjs = Mathdata.doc_creates_objs dl in
      let createsprops = Mathdata.doc_creates_props dl in
      let createsnegprops = Mathdata.doc_creates_neg_props dl in
      if not (usesobjs = []) then
	begin
	  Printf.fprintf oc "2*%d rights required to use objects must be consumed:\n" (List.length usesprops);
	  List.iter
	    (fun (h,k) ->
	      Printf.fprintf oc "Right to use (pure) object %s (%s)\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid (hashpair h k)) 32l in
	      Printf.fprintf oc "Right to use (theory) object %s (%s)\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    usesobjs
	end;
      if not (usesprops = []) then
	begin
	  Printf.fprintf oc "2*%d rights required to use propositions must be consumed:\n" (List.length usesprops);
	  List.iter
	    (fun h ->
	      Printf.fprintf oc "Right to use (pure) proposition %s (%s)\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid h) 33l in
	      Printf.fprintf oc "Right to use (theory) proposition %s (%s)\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    usesprops
	end;
      if not (createsobjs = []) then
	begin
	  Printf.fprintf oc "%d objects possibly created:\n" (List.length createsobjs);
	  List.iter
	    (fun (h,k) ->
	      Printf.fprintf oc "If there is no owner of (pure) object %s (%s), OwnsObj must be declared.\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid (hashpair h k)) 32l in
	      Printf.fprintf oc "If there is no owner of (theory) object %s (%s), OwnsObj must be declared.\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    createsobjs
	end;
      if not (createsprops = []) then
	begin
	  Printf.fprintf oc "%d propositions possibly created:\n" (List.length createsprops);
	  List.iter
	    (fun h ->
	      Printf.fprintf oc "If there is no owner of (pure) proposition %s (%s), OwnsProp must be declared.\n" (hashval_hexstring h) (addr_pfgaddrstr (hashval_term_addr h));
	      let h2 = hashtag (hashopair2 thyid h) 33l in
	      Printf.fprintf oc "If there is no owner of (theory) proposition %s (%s), OwnsProp must be declared.\n" (hashval_hexstring h2) (addr_pfgaddrstr (hashval_term_addr h2)))
	    createsprops
	end;
      if not (createsnegprops = []) then
	begin
	  Printf.fprintf oc "%d negated propositions possibly created:\n" (List.length createsnegprops);
	  List.iter
	    (fun h ->
	      let h2 = hashtag (hashopair2 thyid h) 33l in
	      Printf.fprintf oc "If there is no OwnsNegProp at %s (for id %s), one must be declared.\n" (addr_pfgaddrstr (hashval_term_addr h2)) (hashval_hexstring h2))
	    createsnegprops
	end

let rec ctree_tagged_hashes c par r =
  match c with
  | CHash(h) -> (None,par,h)::r
  | CLeaf((_,beta),NehHash(h,_)) -> (Some(beta),par,h)::r
  | CLeaf(_,_) -> raise (Failure "Bug: Unexpected ctree elt case of nehhlist other than hash")
  | CLeft(c0) -> ctree_tagged_hashes c0 par r
  | CRight(c1) -> ctree_tagged_hashes c1 par r
  | CBin(c0,c1) -> ctree_tagged_hashes c0 par (ctree_tagged_hashes c1 par r)

let verifyfullledger oc h =
  try
    let c = expand_ctree_atom_or_element false h in
    let cl = ctree_tagged_hashes c [h] [] in
    let rec verify_tagged_hashes thl =
      match thl with
      | [] -> ()
      | (None,_,h)::thr ->
	 verifyledger_h h;
	 verify_tagged_hashes thr
      | (Some(beta),_,h)::thr ->
	 verifyhlist_h h beta;
	 verify_tagged_hashes thr
    in
    try
      Printf.fprintf oc "Verifying ledger %s. This may take a while.\n" (hashval_hexstring h);
      flush oc;
      verify_tagged_hashes cl;
      Printf.fprintf oc "Ledger is complete.\n";
      flush oc
    with
    | MissingAsset(h,beta) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. Asset %s is missing.\n" (hashval_hexstring h);
	  Printf.fprintf oc "At address: %s\n" (addr_pfgaddrstr beta);
	  flush oc
	end
    | MissingHConsElt(h,beta) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. HConsElt %s is missing.\n" (hashval_hexstring h);
	  Printf.fprintf oc "At address: %s\n" (addr_pfgaddrstr beta);
	  flush oc
	end
    | MissingCTreeAtm(h) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. CTreeAtm %s is missing.\n" (hashval_hexstring h);
	  flush oc
	end
    | CorruptedAsset(h,beta) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. Asset %s is corrupted.\n" (hashval_hexstring h);
	  Printf.fprintf oc "At address: %s\n" (addr_pfgaddrstr beta);
	  flush oc
	end
    | CorruptedHConsElt(h,beta) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. HConsElt %s is corrupted.\n" (hashval_hexstring h);
	  Printf.fprintf oc "At address: %s\n" (addr_pfgaddrstr beta);
	  flush oc
	end
    | CorruptedCTreeAtm(h) ->
	begin
	  Printf.fprintf oc "Ledger is not complete. CTreeAtm %s is corrupted.\n" (hashval_hexstring h);
	  flush oc
	end
  with Not_found ->
    Printf.fprintf oc "Do not have the root of ledger %s\n" (hashval_hexstring h);
    flush oc

let rec req_par_inv_nbhd par cnt =
  let gini = int_of_msgtype GetInvNbhd in
  let cei = int_of_msgtype CTreeElement in
  match par with
  | [] -> cnt()
  | h::parr ->
      req_par_inv_nbhd parr
	(fun () ->
	  let invrq = ref false in
	  let tm = Unix.time() in
	  List.iter
	    (fun (_,_,(_,_,_,gcs)) ->
	      match !gcs with
	      | Some(cs) ->
		  if not cs.banned && Hashtbl.mem cs.rinv (cei,h) && not (recently_requested (gini,h) tm cs.invreq) && not !invrq then
		    begin
		      Hashtbl.add cs.invreqhooks (cei,h) cnt;
		      let msb = Buffer.create 20 in
		      seosbf (seo_prod seo_int8 seo_hashval seosb (cei,h) (msb,None));
		      let ms = Buffer.contents msb in
		      ignore (queue_msg cs GetInvNbhd ms);
		      Hashtbl.add cs.invreq (gini,h) tm;
		      invrq := true
		    end;
	      | None -> ())
	    !netconns;
	  if not !invrq then cnt())

let dumpwallet fn =
  let f = open_out fn in
  Printf.fprintf f "1. Wallet keys and address:\n";
  List.iter
    (fun (_,_,_,w,_,alpha) ->
      Printf.fprintf f "%s %s (staking)\n" alpha w)
    !walletkeys_staking;
  List.iter
    (fun (_,_,_,w,_,alpha) ->
      Printf.fprintf f "%s %s (nonstaking)\n" alpha w)
    !walletkeys_nonstaking;
  List.iter
    (fun (_,_,_,w,_,alpha) ->
      Printf.fprintf f "%s %s (staking fresh)\n" alpha w)
    !walletkeys_staking_fresh;
  List.iter
    (fun (_,_,_,w,_,alpha) ->
      Printf.fprintf f "%s %s (nonstaking fresh)\n" alpha w)
    !walletkeys_nonstaking_fresh;
  Printf.fprintf f "2. Wallet endorsements:\n";
  List.iter
    (fun (alphap,betap,_,recid,fcomp,esg) ->
      let alpha = addr_pfgaddrstr (payaddr_addr alphap) in
      let beta = addr_pfgaddrstr (payaddr_addr betap) in
      let sgstr = encode_signature recid fcomp esg in
      Printf.fprintf f "%s controls %s via %s\n" beta alpha sgstr)
    !walletendorsements;
  Printf.fprintf f "3. Wallet p2sh:\n";
  List.iter
    (fun (_,alpha,scr) ->
      Printf.fprintf f "%s p2sh with script " alpha;
      List.iter (fun b -> Printf.fprintf f "%0x" b) scr;
      Printf.fprintf f "\n")
    !walletp2shs;
  Printf.fprintf f "4. Wallet watch addresses:\n";
  List.iter
    (fun alpha -> Printf.fprintf f "%s\n" (addr_pfgaddrstr alpha))
    !walletwatchaddrs;
  List.iter
    (fun alpha -> Printf.fprintf f "%s (offlinekey)\n" (addr_pfgaddrstr alpha))
    !walletwatchaddrs_offlinekey;
  List.iter
    (fun alpha -> Printf.fprintf f "%s (offlinekey, fresh)\n" (addr_pfgaddrstr alpha))
    !walletwatchaddrs_offlinekey_fresh;
  close_out_noerr f

let rec pblockchain_r s lbk ltx m =
  if m > 0 then
    begin
      try
	let (dbh,lmedtm,burned,(txid1,vout1),par,csm,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	begin
	  match par with
	  | Some(lbk,ltx) -> pblockchain_r s lbk ltx (m-1)
	  | None -> ()
	end;
	try
	  let (tar,tm,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	  Printf.fprintf s "block %Ld %s (post block ledger %s)\n" blkh (hashval_hexstring dbh) (hashval_hexstring lr);
          Printf.fprintf s "(BLOCK %Ld \"%s\" %s)\n" blkh (hashval_hexstring dbh) (Z.to_string (pow_finalstep dbh));
	  Printf.fprintf s "Timestamp: %Ld\n" tm;
	  Printf.fprintf s "Target: %s\n" (string_of_big_int tar);
	  Printf.fprintf s "Difficulty: %s\n" (string_of_big_int (difficulty tar));
	  Printf.fprintf s "Stake Modifier: %s\n" (hashval_hexstring csm);
	  Printf.fprintf s "Burned %Ld at median time %Ld with ltc tx %s in block %s\n" burned lmedtm (hashval_hexstring ltx) (hashval_hexstring lbk);
	with Not_found ->
	  Printf.fprintf s "block %Ld %s (missing header info)\n" blkh (hashval_hexstring dbh);
	  Printf.fprintf s "Stake Modifier: %s\n" (hashval_hexstring csm);
	  Printf.fprintf s "Burned %Ld at median time %Ld with ltc tx %s in block %s\n" burned lmedtm (hashval_hexstring ltx) (hashval_hexstring lbk);
      with Not_found ->
	Printf.fprintf s "apparent block burned with ltc tx %s in block %s, but missing outline info\n" (hashval_hexstring ltx) (hashval_hexstring lbk);
    end

let pblockchain s n m =
  match n with
  | Some(_,lbk,ltx) -> pblockchain_r s lbk ltx m
  | None -> ()

let rec reprocess_blockchain_r s lbk ltx m cnt =
  try
    let lh = hashpair lbk ltx in
    let (dbh,lmedtm,burned,(txid1,vout1),par,csm,blkh) = Db_outlinevals.dbget lh in
    Db_validheadervals.dbdelete lh;
    Db_validblockvals.dbdelete lh;
    if blkh > m then
      begin
        let cnt2 () =
          (*          Printf.printf "BEGIN reprocessblock %Ld %s\n" blkh (hashval_hexstring dbh); flush stdout; *)
          reprocessblock s dbh lbk ltx;
          (*          Printf.printf "END reprocessblock %Ld %s\n" blkh (hashval_hexstring dbh); flush stdout; *)
          cnt()
        in
	match par with
	| Some(plbk,pltx) -> reprocess_blockchain_r s plbk pltx m cnt2
	| None -> ()
      end
    else
      begin
        (*        Printf.printf "BEGIN reprocessblock %Ld %s\n" blkh (hashval_hexstring dbh); flush stdout; *)
        reprocessblock s dbh lbk ltx;
        (*        Printf.printf "END reprocessblock %Ld %s\n" blkh (hashval_hexstring dbh); flush stdout; *)
        cnt()
      end
  with Not_found ->
    Printf.fprintf s "apparent block burned with ltc tx %s in block %s, but missing outline info\n" (hashval_hexstring ltx) (hashval_hexstring lbk)

let reprocess_blockchain s n m =
  match n with
  | Some(_,lbk,ltx) ->
     let tm = Unix.gettimeofday() in
     reprocess_blockchain_r s lbk ltx (Int64.of_int m) (fun () -> ());
     Printf.fprintf s "Elapsed time: %f\n" (Unix.gettimeofday() -. tm)
  | None -> ()

let dumpstate fa =
  let sa = open_out fa in
  Printf.fprintf sa "=========\nNetwork connections: %d\n" (List.length !netconns);
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
      match !gcs with
      | None -> Printf.fprintf sa "[Dead Connection]\n";
      | Some(cs) ->
	  Printf.fprintf sa "-----------\nConnection: %s %f\n" cs.realaddr cs.conntime;
	  Printf.fprintf sa "peertimeskew %d\nprotvers %ld\nuseragent %s\naddrfrom %s\nbanned %s\nlastmsgtm %f\nfirst_header_height %Ld\nfirst_full_height %Ld\nlast_height %Ld\n" cs.peertimeskew cs.protvers cs.useragent cs.addrfrom (if cs.banned then "true" else "false") cs.lastmsgtm cs.first_header_height cs.first_full_height cs.last_height;
	  Hashtbl.iter
	    (fun (m,h) tm ->
	      Printf.fprintf sa "%d %s %f\n" m (hashval_hexstring h) tm)
	    cs.sentinv;
	  Hashtbl.iter
	    (fun (m,h) () ->
	      Printf.fprintf sa "%d %s\n" m (hashval_hexstring h))
	    cs.rinv;
	  Hashtbl.iter
	    (fun (m,h) tm ->
	      Printf.fprintf sa "%d %s %f\n" m (hashval_hexstring h) tm)
	    cs.invreq;
    )
    !netconns;
  Printf.fprintf sa "=================\nBlock Chain:\n";
  (try pblockchain sa (get_bestblock_print_warnings sa) 10000 with _ -> ());
  dumpblocktreestate sa;
  close_out_noerr sa

let rec ctre_left c =
  match c with
  | CHash(h) -> ctre_left (get_ctree_atom_or_element h)
  | CBin(cl,_) -> cl
  | CLeft(cl) -> cl
  | CLeaf((st,beta),hl) when st < 162 && not (addr_get_bit beta st) -> CLeaf((st+1,beta),hl)
  | _ -> raise Not_found

let rec ctre_right c =
  match c with
  | CHash(h) -> ctre_right (get_ctree_atom_or_element h)
  | CBin(_,cr) -> cr
  | CRight(cr) -> cr
  | CLeaf((st,beta),hl) when st < 162 && addr_get_bit beta st -> CLeaf((st+1,beta),hl)
  | _ -> raise Not_found

let notfound_warning_wrap oc h d f =
  try
    f()
  with Not_found ->
    Printf.fprintf oc "WARNING: missing %s %s. Information likely to be incomplete.\n" d (hashval_hexstring h);
    raise Not_found

let rec report_hlist_a oc (g:asset -> addr -> unit) hl bl =
  match hl with
  | HNil -> ()
  | HCons(a1,hr) ->
      g a1 bl;
      report_hlist_a oc g hr bl
  | HConsH(h1,hr) ->
      begin
	try
	  let a1 = notfound_warning_wrap oc h1 "asset" (fun () -> get_asset h1) in
	  g a1 bl;
	  raise Not_found
	with Not_found ->
	  report_hlist_a oc g hr bl
      end
  | HHash(h,_) ->
      try
	let (h1,ohr) = notfound_warning_wrap oc h "hcons element" (fun () -> get_hcons_element h) in
	try
	  let a1 = notfound_warning_wrap oc h1 "asset" (fun () -> get_asset h1) in
	  g a1 bl;
	  raise Not_found
	with Not_found ->
	  match ohr with
	  | None -> ()
	  | Some(k,l) -> report_hlist_a oc g (HHash(k,l)) bl
      with Not_found -> ()

let report_nehlist_a oc g hl bl =
  match hl with
  | NehCons(a1,hr) ->
      g a1 bl;
      report_hlist_a oc g hr bl
  | NehConsH(h1,hr) ->
      begin
	try
	  let a1 = notfound_warning_wrap oc h1 "asset" (fun () -> get_asset h1) in
	  g a1 bl;
	  raise Not_found
	with Not_found ->
	  report_hlist_a oc g hr bl
      end
  | NehHash(h,_) ->
      try
	let (h1,ohr) = notfound_warning_wrap oc h "hcons element" (fun () -> get_hcons_element h) in
	try
	  let a1 = notfound_warning_wrap oc h1 "asset" (fun () -> get_asset h1) in
	  g a1 bl;
	  raise Not_found
	with Not_found ->
	  match ohr with
	  | None -> ()
	  | Some(k,l) -> report_hlist_a oc g (HHash(k,l)) bl
      with Not_found -> ()

let rec report_a oc g c =
  match c with
  | CBin(cl,cr) ->
      report_a oc g cl;
      report_a oc g cr;
  | CLeft(cl) ->
      report_a oc g cl;
  | CRight(cr) ->
      report_a oc g cr;
  | CLeaf((_,beta),hl) ->
     report_nehlist_a oc g hl beta
  | CHash(h) ->
      begin
	try
	  let c2 = notfound_warning_wrap oc h "ledger element" (fun () -> get_ctree_atom_or_element h) in
	  report_a oc g c2
	with Not_found -> ()
      end

let reportowned oc f lr =
  try
    report_a
      oc
      (fun a bl ->
	match a with
	| (aid,bday,obl,OwnsObj(oid,alpha,r)) ->
	    Printf.fprintf f "Obj %s %Ld %s %s %s %s %s %s\n" (hashval_hexstring aid) bday (hashval_hexstring oid) (addr_pfgaddrstr (hashval_term_addr oid)) (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha)) (match r with Some(rp) -> Printf.sprintf "%Ld" rp | None -> "None") (match obl with Some(beta,lk,_) -> Printf.sprintf "%s %Ld" (addr_pfgaddrstr (payaddr_addr beta)) lk | None -> "None")
	| (aid,bday,obl,OwnsProp(pid,alpha,r)) ->
	    Printf.fprintf f "Prop %s %Ld %s %s %s %s %s %s\n" (hashval_hexstring aid) bday (hashval_hexstring pid) (addr_pfgaddrstr (hashval_term_addr pid)) (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha)) (match r with Some(rp) -> Printf.sprintf "%Ld" rp | None -> "None") (match obl with Some(beta,lk,_) -> Printf.sprintf "%s %Ld" (addr_pfgaddrstr (payaddr_addr beta)) lk | None -> "None")
	| (aid,bday,obl,OwnsNegProp) ->
	    Printf.fprintf f "NegProp %s %Ld %s %s\n" (hashval_hexstring aid) bday (addr_pfgaddrstr bl) (match obl with Some(beta,lk,_) -> Printf.sprintf "%s %Ld" (addr_pfgaddrstr (payaddr_addr beta)) lk | None -> "None")
	| _ -> ())
      (ctre_left (ctre_right (get_ctree_atom_or_element lr)))
  with Not_found ->
    Printf.fprintf oc "There appear to be no owned objects or propositions in the ledger.\n"

let reportbounties oc f lr =
  try
    let ownedproph : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    let ownednegproph : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    let bountyh : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    report_a
      oc
      (fun a bl ->
	match a with
	| (aid,bday,obl,Bounty(v)) ->
	    let alpha = bl in
	    Hashtbl.add bountyh alpha a
	| (aid,bday,obl,OwnsProp(pid,beta,r)) ->
	    let alpha = bl in
	    Hashtbl.add ownedproph alpha a
	| (aid,bday,obl,OwnsNegProp) ->
	    let alpha = bl in
	    Hashtbl.add ownednegproph alpha a
	| _ -> ())
      (ctre_left (ctre_right (get_ctree_atom_or_element lr)));
    Hashtbl.iter
      (fun alpha a ->
	match a with
	| (aid,bday,obl,Bounty(v)) ->
	    begin
	      Printf.fprintf f "%s bars bounty at %s (id %s)" (bars_of_atoms v) (addr_pfgaddrstr alpha) (hashval_hexstring aid);
	      try
		let a2 = Hashtbl.find ownedproph alpha in
		match a2 with
		| (_,_,Some(gamma,_,_),_) ->
		    Printf.fprintf f " ** Prop owned by %s and bounty can be claimed.\n" (addr_pfgaddrstr (payaddr_addr gamma))
		| _ -> Printf.fprintf f "\n"
	      with Not_found ->
		try
		  let a2 = Hashtbl.find ownednegproph alpha in
		  match a2 with
		  | (_,_,Some(gamma,_,_),_) ->
		      Printf.fprintf f " ** Neg prop owned by %s and bounty can be claimed.\n" (addr_pfgaddrstr (payaddr_addr gamma))
		  | _ -> Printf.fprintf f "\n"
		with Not_found -> Printf.fprintf f "\n"
	    end
	| _ -> ())
      bountyh
  with Not_found ->
    Printf.fprintf oc "There appear to be no bounties in the ledger.\n"

let collectable_bounties oc lr =
  try
    let ownedproph : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    let ownednegproph : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    let bountyh : (addr,asset) Hashtbl.t = Hashtbl.create 1000 in
    report_a
      oc
      (fun a bl ->
	match a with
	| (aid,bday,obl,Bounty(v)) ->
	    let alpha = bl in
	    Hashtbl.add bountyh alpha a
	| (aid,bday,Some(beta,_,_),OwnsProp(_,_,_)) when privkey_in_wallet_p (payaddr_addr beta) ->
	    let alpha = bl in
	    Hashtbl.add ownedproph alpha a
	| (aid,bday,Some(beta,_,_),OwnsNegProp) when privkey_in_wallet_p (payaddr_addr beta) ->
	    let alpha = bl in
	    Hashtbl.add ownednegproph alpha a
	| _ -> ())
      (ctre_left (ctre_right (get_ctree_atom_or_element lr)));
    let cbl = ref [] in
    Hashtbl.iter
      (fun alpha a ->
	try
	  let a2 = Hashtbl.find ownedproph alpha in cbl := (alpha,a,a2)::!cbl
	with Not_found ->
	  try
	    let a2 = Hashtbl.find ownednegproph alpha in cbl := (alpha,a,a2)::!cbl
	  with Not_found -> ())
      bountyh;
    !cbl
  with Not_found -> []

let reportpubs oc f lr =
  let rec stp_str a =
    match a with
    | Logic.Base(i) -> Printf.sprintf "$%d" i
    | Logic.TpArr(a,b) -> Printf.sprintf "(%s -> %s)" (stp_str a) (stp_str b)
    | Logic.Prop -> "o"
  in
  let rec trm_str m =
    match m with
    | Logic.DB(i) -> Printf.sprintf "?%d" i
    | Logic.TmH(h) -> hashval_hexstring h
    | Logic.Prim(i) -> Printf.sprintf "'%d" i
    | Logic.Ap(m,n) -> Printf.sprintf "(%s %s)" (trm_str m) (trm_str n)
    | Logic.Lam(a,m) -> Printf.sprintf "(^%s.%s)" (stp_str a) (trm_str m)
    | Logic.Imp(m,n) -> Printf.sprintf "(%s -> %s)" (trm_str m) (trm_str n)
    | Logic.All(a,m) -> Printf.sprintf "(!%s.%s)" (stp_str a) (trm_str m)
    | Logic.Ex(a,m) -> Printf.sprintf "(?%s.%s)" (stp_str a) (trm_str m)
    | Logic.Eq(a,m,n) -> Printf.sprintf "(%s =[%s] %s)" (trm_str m) (stp_str a) (trm_str n)
  in
  try
    report_a
      oc
      (fun a bl ->
	match a with
	| (aid,bday,obl,TheoryPublication(alpha,_,ts)) ->
	    begin
	      match Mathdata.hashtheory (Mathdata.theoryspec_theory ts) with
	      | None ->
		  Printf.fprintf f "Theory %s %Ld %s %s with no content?\n" (hashval_hexstring aid) bday (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha));
	      | Some(thyh) ->
		  Printf.fprintf f "Theory %s %Ld %s %s %s\n" (hashval_hexstring aid) bday (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha)) (hashval_hexstring thyh);
		  List.iter
		    (fun thyi ->
		      match thyi with
		      | Logic.Thyprim(a) -> Printf.fprintf f "Prim %s\n" (stp_str a)
		      | Logic.Thyaxiom(m) -> Printf.fprintf f "Axiom %s (%s) : %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 (Some(thyh)) (Mathdata.tm_hashroot m)) 33l)) (trm_str m)
		      | Logic.Thydef(a,m) -> Printf.fprintf f "Def %s (%s) : %s := %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 (Some(thyh)) (hashpair (Mathdata.tm_hashroot m) (Mathdata.hashtp a))) 32l)) (hashval_hexstring (Mathdata.hashtp a)) (trm_str m))
		    (List.rev ts)
	    end
	| (aid,bday,obl,SignaPublication(alpha,_,thyh,ss)) ->
	    Printf.fprintf f "Signature %s %Ld %s %s %s\n" (hashval_hexstring aid) bday (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha)) (match thyh with Some(thyh) -> hashval_hexstring thyh ^ " " ^ (addr_pfgaddrstr (hashval_pub_addr thyh)) | None -> "None");
	    begin
	      List.iter
		(fun si ->
		  match si with
		  | Logic.Signasigna(h) -> Printf.fprintf f "Require %s\n" (hashval_hexstring h)
		  | Logic.Signaparam(h,a) -> Printf.fprintf f "Param %s (%s) : %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 thyh (hashpair h (Mathdata.hashtp a))) 32l)) (stp_str a)
		  | Logic.Signadef(a,m) -> Printf.fprintf f "Def %s (%s) : %s := %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (hashpair (Mathdata.tm_hashroot m) (Mathdata.hashtp a))) 32l)) (stp_str a) (trm_str m)
		  | Logic.Signaknown(m) -> Printf.fprintf f "Known %s (%s) : %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (Mathdata.tm_hashroot m)) 33l)) (trm_str m))
		(List.rev ss)
	    end
	| (aid,bday,obl,DocPublication(alpha,_,thyh,d)) ->
	    Printf.fprintf f "Document %s %Ld %s %s %s\n" (hashval_hexstring aid) bday (addr_pfgaddrstr bl) (addr_pfgaddrstr (payaddr_addr alpha)) (match thyh with Some(thyh) -> hashval_hexstring thyh ^ " " ^ (addr_pfgaddrstr (hashval_pub_addr thyh)) | None -> "None");
	    begin
	      List.iter
		(fun di ->
		  match di with
		  | Logic.Docsigna(h) -> Printf.fprintf f "Require %s\n" (hashval_hexstring h)
		  | Logic.Docparam(h,a) -> Printf.fprintf f "Param %s (%s) : %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 thyh (hashpair h (Mathdata.hashtp a))) 32l)) (stp_str a)
		  | Logic.Docdef(a,m) -> Printf.fprintf f "Def %s (%s) : %s := %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (hashpair (Mathdata.tm_hashroot m) (Mathdata.hashtp a))) 32l)) (stp_str a) (trm_str m)
		  | Logic.Docknown(m) -> Printf.fprintf f "Known %s (%s) : %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (Mathdata.tm_hashroot m)) 33l)) (trm_str m)
		  | Logic.Docpfof(m,d) ->
                     Printf.fprintf f "Theorem %s (%s) : %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (Mathdata.tm_hashroot m)) 33l)) (trm_str m);
                     Printf.fprintf f "(PID-TRMROOT \"%s\" \"%s\")\n" (hashval_hexstring (hashtag (hashopair2 thyh (Mathdata.tm_hashroot m)) 33l)) (hashval_hexstring (Mathdata.tm_hashroot m));
                     let usesknowns = ref [] in
                     let rec g d =
                       match d with
                       | Logic.Known(h) -> if not (List.mem h !usesknowns) then usesknowns := h :: !usesknowns
                       | Logic.PrAp(d1,d2) -> g d1; g d2
                       | Logic.TmAp(d1,_) -> g d1
                       | Logic.PrLa(_,d1) -> g d1
                       | Logic.TmLa(_,d1) -> g d1
                       | _ -> ()
                     in
                     g d;
                     Printf.fprintf f "(PFUSES \"%s\"" (hashval_hexstring (Mathdata.tm_hashroot m));
                     List.iter (fun h -> Printf.fprintf f " \"%s\"" (hashval_hexstring h)) !usesknowns;
                     Printf.fprintf f ")\n";
		  | Logic.Docconj(m) -> Printf.fprintf f "Conjecture %s (%s) : %s\n" (hashval_hexstring (Mathdata.tm_hashroot m)) (hashval_hexstring (hashtag (hashopair2 thyh (Mathdata.tm_hashroot m)) 33l)) (trm_str m))
		(List.rev d)
	    end
	| _ -> ())
      (ctre_right (ctre_right (get_ctree_atom_or_element lr)))
  with Not_found ->
    Printf.fprintf oc "There are no publications in the ledger.\n"

let createatomicswap ltxid alpha beta tmlock =
  let scrl =
    [0x63; (** OP_IF **)
     0x51; (** PUSH 1 onto the stack, requiring 1 ltc confirmation **)
     0x20] (** PUSH 32 bytes (the ltc tx id) onto the stack **)
    @ be256_bytelist ltxid
    @ [0xb3; (** OP_LTX_VERIFY to ensure the ltc tx has at least 1 confirmation **)
       0x76; (** OP_DUP -- duplicate the given pubkey for alpha **)
       0xa9; (** OP_HASH160 -- hash the given pubkey **)
       0x14] (** PUSH 20 bytes (should be hash of pubkey for alpha) onto the stack **)
    @ be160_bytelist alpha
    @ [0x67; (** OP_ELSE **)
       0x04] (** PUSH 4 bytes onto the stack (lock time) **)
    @ blnum_le (big_int_of_int32 tmlock) 4
    @ [0xb1] (** CLTV to check if this branch is valid yet **)
    @ [0x75; (** OP_DROP, drop the locktime from the stack **)
       0x76; (** OP_DUP -- duplicate the given pubkey for beta **)
       0xa9; (** OP_HASH160 -- hash the given pubkey **)
       0x14] (** PUSH 20 bytes (should be hash of pubkey for beta) onto the stack **)
    @ be160_bytelist beta
    @ [0x68; (** OP_ENDIF **)
       0x88; (** OP_EQUALVERIFY -- to ensure the given pubkey hashes to the right value **)
       0xac] (** OP_CHECKSIG **)
  in
  let gamma = Script.hash160_bytelist scrl in
  (gamma,scrl)

let createhtlc2 alpha beta tmlock rel secrh =
  let scrl =
    [0x63; (** OP_IF **)
     0x82; (** OP_SIZE **)
     0x01;0x20; (** PUSH 0x20 (32) **)
     0x88; (** OP_EQUALVERIFY to make sure the secret is 32 bytes **)
     0xa8; (** OP_SHA256 **)
     0x20] (** PUSH 32 bytes (the hash of the secret) onto the stack **)
    @ be256_bytelist secrh
    @ [0x88; (** OP_EQUALVERIFY to ensure the secret hashes to the expected hash **)
       0x76; (** OP_DUP -- duplicate the given pubkey for alpha **)
       0xa9; (** OP_HASH160 -- hash the given pubkey **)
       0x14] (** PUSH 20 bytes (should be hash of pubkey for alpha) onto the stack **)
    @ be160_bytelist alpha
    @ [0x67; (** OP_ELSE **)
       0x04] (** PUSH 4 bytes onto the stack (lock time) **)
    @ blnum_le (big_int_of_int32 tmlock) 4
    @ [if rel then 0xb2 else 0xb1] (** CSV or CLTV to check if this branch is valid yet **)
    @ [0x75; (** OP_DROP, drop the locktime from the stack **)
       0x76; (** OP_DUP -- duplicate the given pubkey for beta **)
       0xa9; (** OP_HASH160 -- hash the given pubkey **)
       0x14] (** PUSH 20 bytes (should be hash of pubkey for beta) onto the stack **)
    @ be160_bytelist beta
    @ [0x68; (** OP_ENDIF **)
       0x88; (** OP_EQUALVERIFY -- to ensure the given pubkey hashes to the right value **)
       0xac] (** OP_CHECKSIG **)
  in
  let alpha = Script.hash160_bytelist scrl in
  (alpha,scrl,secrh)

let createhtlc alpha beta tmlock rel secr =
  let secrh = sha256_bytelist (be256_bytelist secr) in
  createhtlc2 alpha beta tmlock rel secrh

let createmultisig2 m pubkeys =
  let n = List.length pubkeys in
  if n <= 1 || n > 16 then raise (Failure "n must be > 1 and <= 16");
  if m > n then raise (Failure "m cannot be greater than n");
  let scrl = ref [174] in
  let pushscrnum i =
    if i < 0 then
      raise (Failure "unexpected occurrence")
    else if i = 0 then
      scrl := 0::!scrl
    else if i <= 16 then
      scrl := (80 + i)::!scrl
    else
      raise (Failure "unexpected occurrence")
  in
  pushscrnum n;
  List.iter
    (fun (s,_) ->
      let il = string_bytelist (hexstring_string s) in
      scrl := List.length il::il @ !scrl)
    (List.rev pubkeys);
  pushscrnum m;
  let alpha = Script.hash160_bytelist !scrl in
  (alpha,!scrl)

let createmultisig m jpks =
  match jpks with
  | JsonArr(jpkl) ->
      let pubkeys = List.map (fun j -> match j with JsonStr(s) -> (s,hexstring_pubkey s) | _ -> raise (Failure "expected an array of pubkeys")) jpkl in
      createmultisig2 m pubkeys
  | _ -> raise (Failure "expected an array of pubkeys")

let report_recenttxs_filtered p oc h n =
  let reptxs = ref [] in
  let i = ref 0 in
  let (bhd,_) = DbBlockHeader.dbget h in
  let bd = Block.DbBlockDelta.dbget h in
  let blktm = bhd.timestamp in
  let (par,blkh) =
    match bhd.prevblockhash with
    | Some(_,Poburn(h,k,_,_,_,_)) ->
       let (pbh,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair h k) in
       (Some(pbh,h,k),Int64.add blkh 1L)
    | None -> (None,1L)
  in
  let blkidh = hashval_hexstring h in
  List.iter
    (fun (((_,tauout),_) as stau) ->
      if List.exists p tauout then
        let stxid = hashstx stau in
        reptxs := JsonObj([("stx",JsonStr(hashval_hexstring stxid));("block",JsonStr(blkidh));("height",JsonNum(Int64.to_string blkh));("time",JsonNum(Int64.to_string blktm))])::!reptxs;
        incr i)
    bd.blockdelta_stxl;
  let finish pbh =
    match pbh with
    | None ->
       print_jsonval oc (JsonObj([("recenttxs",JsonArr(!reptxs))]));
       Printf.fprintf oc "\n"
    | Some(pbh) ->
       print_jsonval oc (JsonObj([("recenttxs",JsonArr(!reptxs));("prevblock",JsonStr(hashval_hexstring pbh))]));
       Printf.fprintf oc "\n"
  in
  match par with
  | None -> finish None
  | Some(pbh,plbk,pltx) ->
     if !i < n then
       let rec f lbk ltx =
         let (bh,_,_,_,par,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
         let (bhd,_) = DbBlockHeader.dbget bh in
         let bd = Block.DbBlockDelta.dbget bh in
         let blktm = bhd.timestamp in
         List.iter
           (fun (((_,tauout),_) as stau) ->
             if List.exists p tauout then
               let stxid = hashstx stau in
               reptxs := JsonObj([("stx",JsonStr(hashval_hexstring stxid));("block",JsonStr(blkidh));("height",JsonNum(Int64.to_string blkh));("time",JsonNum(Int64.to_string blktm))])::!reptxs;
               incr i)
           bd.blockdelta_stxl;
         match par with
         | Some(plbk,pltx) ->
            if !i < n then
              f plbk pltx
            else
              let (pbh,_,_,_,_,_,_) = Db_outlinevals.dbget (hashpair plbk pltx) in
              finish (Some(pbh))
         | None ->
            finish None
       in
       f plbk pltx
     else
       finish (Some(pbh))

let report_recenttxs oc h n =
  let p _ = true in
  report_recenttxs_filtered p oc h n

let report_recentdocs oc h n =
  let p (_,(_,u)) =
    match u with
    | DocPublication(_,_,_,_) -> true
    | _ -> false
  in
  report_recenttxs_filtered p oc h n

let report_recentthms oc h n =
  let p (_,(_,u)) =
    match u with
    | DocPublication(_,_,_,dl) ->
       List.exists (fun di -> match di with Logic.Docpfof(_,_) -> true | _ -> false) dl
    | _ -> false
  in
  report_recenttxs_filtered p oc h n

let report_recentobjid_defined oc oid h n =
  let p (_,(_,u)) =
    match u with
    | DocPublication(_,_,th,dl) ->
       List.exists
         (fun di ->
           match di with
             Logic.Docdef(a,m) ->
              let trmroot = Mathdata.tm_hashroot m in
              let objid = hashtag (hashopair2 th (hashpair trmroot (Mathdata.hashtp a))) 32l in
              objid = oid
           | _ -> false)
         dl
    | _ -> false
  in
  report_recenttxs_filtered p oc h n

let report_recenttrmroot_defined oc oid h n =
  let p (_,(_,u)) =
    match u with
    | DocPublication(_,_,th,dl) ->
       List.exists
         (fun di ->
           match di with
             Logic.Docdef(a,m) ->
              let trmroot = Mathdata.tm_hashroot m in
              trmroot = oid
           | Logic.Docpfof(p,_) ->
              let trmroot = Mathdata.tm_hashroot p in
              trmroot = oid
           | Logic.Docconj(p) ->
              let trmroot = Mathdata.tm_hashroot p in
              trmroot = oid
           | _ -> false)
         dl
    | _ -> false
  in
  report_recenttxs_filtered p oc h n

let report_recentpropid_proven oc pid h n =
  let p (_,(_,u)) =
    match u with
    | DocPublication(_,_,th,dl) ->
       List.exists
         (fun di ->
           match di with
             Logic.Docpfof(p,_) ->
              let trmroot = Mathdata.tm_hashroot p in
              let propid = hashtag (hashopair2 th trmroot) 33l in
              propid = pid
           | _ -> false)
         dl
    | _ -> false
  in
  report_recenttxs_filtered p oc h n

let report_bounties_collected oc h =
  let spentfrom : (addr,hashval) Hashtbl.t = Hashtbl.create 1000 in
  let ownsproppid : (addr,hashval) Hashtbl.t = Hashtbl.create 1000 in
  let ownsprop : (addr,hashval) Hashtbl.t = Hashtbl.create 1000 in
  let ownsnegprop : (addr,hashval) Hashtbl.t = Hashtbl.create 1000 in
  let bountyat : (addr,int64) Hashtbl.t = Hashtbl.create 1000 in
  let reptxs = ref [] in
  let (bhd,_) = DbBlockHeader.dbget h in
  let bd = Block.DbBlockDelta.dbget h in
  let blktm = bhd.timestamp in
  let (par,blkh) =
    match bhd.prevblockhash with
    | Some(_,Poburn(h,k,_,_,_,_)) ->
       let (pbh,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair h k) in
       (Some(pbh,h,k),Int64.add blkh 1L)
    | None -> (None,1L)
  in
  let blkidh = hashval_hexstring h in
  List.iter
    (fun (((tauin,tauout),_) as stau) ->
      let stxid = hashstx stau in
      List.iter
        (fun (alpha,_) ->
          Hashtbl.add spentfrom alpha stxid)
        tauin;
      List.iter
        (fun (alpha,(_,u)) ->
          match u with
          | Bounty(v) when v > 0L ->
             (try let v1 = Hashtbl.find bountyat alpha in Hashtbl.replace bountyat alpha (Int64.add v1 v) with Not_found -> Hashtbl.add bountyat alpha v)
          | OwnsProp(pid,_,_) -> Hashtbl.replace ownsproppid alpha pid; Hashtbl.add ownsprop alpha stxid
          | OwnsNegProp -> Hashtbl.add ownsnegprop alpha stxid
          | _ -> ())
        tauout)
    bd.blockdelta_stxl;
  (**  to do: go through everything and then collect which bounties seem to have been spent and by proving which theory. probably need ownsprop and ownsnegprop info too **)
  match par with
  | None -> ()
  | Some(pbh,plbk,pltx) ->
     let rec f lbk ltx =
       let (bh,_,_,_,par,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
       let (bhd,_) = DbBlockHeader.dbget bh in
       let bd = Block.DbBlockDelta.dbget bh in
       let blktm = bhd.timestamp in
       List.iter
         (fun (((tauin,tauout),_) as stau) ->
           let stxid = hashstx stau in
           List.iter
             (fun (alpha,_) ->
               Hashtbl.add spentfrom alpha stxid)
             tauin;
           List.iter
             (fun (alpha,(_,u)) ->
               match u with
               | Bounty(v) when v > 0L ->
                  (try let v1 = Hashtbl.find bountyat alpha in Hashtbl.replace bountyat alpha (Int64.add v1 v) with Not_found -> Hashtbl.add bountyat alpha v)
               | OwnsProp(pid,_,_) -> Hashtbl.replace ownsproppid alpha pid; Hashtbl.add ownsprop alpha stxid
               | OwnsNegProp -> Hashtbl.add ownsnegprop alpha stxid
               | _ -> ())
             tauout)
         bd.blockdelta_stxl;
         match par with
         | Some(plbk,pltx) ->
            f plbk pltx
         | None -> ()
     in
     f plbk pltx;
     Hashtbl.iter
       (fun alpha v ->
         if Hashtbl.mem spentfrom alpha then
           begin
             try
               let pid = Hashtbl.find ownsproppid alpha in
               Printf.fprintf oc "(BOUNTY \"%s\" %Ld (POS \"%s\") (TXS" (addr_pfgaddrstr alpha) v (hashval_hexstring pid);
               List.iter
                 (fun h -> Printf.fprintf oc " \"%s\"" (hashval_hexstring h))
                 (Hashtbl.find_all ownsprop alpha);
               Printf.fprintf oc "))\n"
             with Not_found ->
                   if Hashtbl.mem ownsnegprop alpha then
                     begin
                       Printf.fprintf oc "(BOUNTY \"%s\" %Ld NEG (TXS" (addr_pfgaddrstr alpha) v;
                       List.iter
                         (fun h -> Printf.fprintf oc " \"%s\"" (hashval_hexstring h))
                         (Hashtbl.find_all ownsnegprop alpha);
                       Printf.fprintf oc "))\n"
                     end
           end
       )
       bountyat

