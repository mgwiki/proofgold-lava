(* Copyright (c) 2021-2023 The Proofgold Lava developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2017 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json;;
open Zarithint;;
open Utils;;
open Ser;;
open Sha256;;
open Hashaux;;
open Hash;;
open Net;;
open Db;;
open Secp256k1;;
open Signat;;
open Cryptocurr;;
open Mathdata;;
open Assets;;
open Tx;;
open Ctre;;
open Ctregraft;;
open Block;;
open Blocktree;;
open Ltcrpc;;
open Setconfig;;
open Staking;;
open Inputdraft;;

let ltc_listener_paused = ref false;;

let commitment_maturation_minus_one = 11L;;

exception BadCommandForm;;

let get_ledgerroot b =
  match b with
  | None -> raise Not_found
  | Some(dbh,lbk,ltx) ->
      try
	let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	lr
      with Not_found ->
	let (bhd,_) = DbBlockHeader.dbget dbh in
	bhd.newledgerroot

let get_3roots b =
  match b with
  | None -> raise Not_found
  | Some(dbh,lbk,ltx) ->
      try
	let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
	(lr,tr,sr)
      with Not_found ->
	let (bhd,_) = DbBlockHeader.dbget dbh in
	(bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot)

let lock datadir =
  let lf = Filename.concat datadir "lock" in
  let c = open_out lf in
  close_out_noerr c;
  exitfn := (fun n -> (try Commands.save_txpool(); Sys.remove lf with _ -> ()); exit n);;

let sinceltctime f =
  let snc = Int64.sub (ltc_medtime()) f in
  if snc >= 172800L then
    (Int64.to_string (Int64.div snc 86400L)) ^ " days"
  else if snc >= 7200L then
    (Int64.to_string (Int64.div snc 7200L)) ^ " hours"
  else if snc >= 120L then
    (Int64.to_string (Int64.div snc 60L)) ^ " minutes"
  else if snc = 1L then
    "1 second"
  else
    (Int64.to_string snc) ^ " seconds";;

let sincetime f =
  let snc = Int64.sub (Int64.of_float (Unix.time())) f in
  if snc >= 172800L then
    (Int64.to_string (Int64.div snc 86400L)) ^ " days"
  else if snc >= 7200L then
    (Int64.to_string (Int64.div snc 7200L)) ^ " hours"
  else if snc >= 120L then
    (Int64.to_string (Int64.div snc 60L)) ^ " minutes"
  else if snc = 1L then
    "1 second"
  else
    (Int64.to_string snc) ^ " seconds";;

let fstohash a =
  match a with
  | None -> None
  | Some(h,_) -> Some(h);;

let stkth : Thread.t option ref = ref None;;
let swpth : Thread.t option ref = ref None;;

let ltc_listener_th : Thread.t option ref = ref None;;

let ltc_init sout =
  try
    log_string (Printf.sprintf "syncing with ltc\n");
    begin (** if recentltcblocks file was given, then process the ones listed in the file **)
      match !recent_ltc_blocks with
      | None -> ()
      | Some(f) ->
         try
	   let s = open_in f in
	   try
	     while true do
	       let l = input_line s in
	       ltc_process_block l
	     done
	   with _ -> close_in_noerr s
         with _ -> ()
    end;
    begin (** if forwardfromltcblock was given, then try to sync forward from a given block **)
      match !forward_from_ltc_block with
      | None -> ltc_forward_from_oldest()
      | Some(h) ->
         ltc_forward_from_block h
    end;
    let lbh = ltc_getbestblockhash () in
    log_string (Printf.sprintf "ltc bestblock %s\n" lbh);
    ltc_process_block lbh;
    ltc_bestblock := hexstring_hashval lbh;
    log_string (Printf.sprintf "finished initial syncing with ltc, now checking for new blocks\n");
    let lbh = ltc_getbestblockhash () in
    log_string (Printf.sprintf "ltc bestblock %s\n" lbh);
    ltc_process_block lbh;
    ltc_bestblock := hexstring_hashval lbh;
    log_string (Printf.sprintf "finished syncing with ltc\n");
  with exc ->
    log_string (Printf.sprintf "problem syncing with ltc. %s quitting.\n" (Printexc.to_string exc));
    Printf.fprintf sout "problem syncing with ltc. quitting.\n";
    !exitfn 2

let ltc_listener () =
  log_string (Printf.sprintf "ltc_listener thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let lastensuresync = ref (Unix.time()) in
  let maybe_ensure_sync () =
    let nw = Unix.time() in
    if nw -. !lastensuresync > 3600.0 then
      begin
        lastensuresync := nw;
        ensure_sync()
      end
  in
  while true do
    try
      (*      log_string (Printf.sprintf "ltc_listener thread %d loop %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday())); *)
      if !ltc_listener_paused then raise Exit;
      let lbh = ltc_getbestblockhash () in
      ltc_process_block lbh;
      ltc_bestblock := hexstring_hashval lbh;
      begin
        match !alertcandidatetxs with
        | (altx::altxr) ->
           alertcandidatetxs := altxr;
           ltc_process_alert_tx altx
        | [] -> ()
      end;
      if !netconns = [] then
        (netseeker2 (); Thread.delay 60.0)
      else if !missingheaders = [] && !missingdeltas = [] then
        (maybe_ensure_sync(); Thread.delay 60.0)
      else
        begin
          missingheaders :=
            List.filter
              (fun (_,k) -> not (DbBlockHeader.dbexists k || DbInvalidatedBlocks.dbexists k || DbBlacklist.dbexists k))
              !missingheaders;
          missingdeltas :=
            List.filter
              (fun (_,k) -> not (DbBlockDelta.dbexists k || DbInvalidatedBlocks.dbexists k || DbBlacklist.dbexists k))
              !missingdeltas;
          if !missingheaders = [] && !missingdeltas = [] then
            (maybe_ensure_sync(); Thread.delay 60.0)
          else
            begin
              List.iter
                (fun (_,_,(_,_,_,gcs)) ->
                  match !gcs with
                  | Some(cs) ->
                     if cs.handshakestep = 5 then find_and_send_requestmissingblocks cs
                  | None -> ())
                !netconns;
              Thread.delay 10.0
            end
        end
    with
    | Unix.Unix_error(Unix.ENOMEM,_,_) ->
       log_string (Printf.sprintf "Out of memory. Trying to exit gracefully.\n");
       Printf.printf "Out of memory. Trying to exit gracefully.\n";
       !exitfn 9
    | exn ->
      log_string (Printf.sprintf "ltc_listener thread %d exception %s\n" (Thread.id (Thread.self())) (Printexc.to_string exn));
      Thread.delay 120.0
  done;;

let unconfirmedspentutxo : (hashval * hashval,unit) Hashtbl.t = Hashtbl.create 100;;

exception CouldNotConsolidate;;
            
let consolidate_spendable oc blkh lr amt esttxsize gathered gatheredkeys gatheredassets txinlr =
  try
    List.iter
      (fun (alpha,a,v) ->
	match a with
	| (aid,_,obl,Currency(_)) when not (Hashtbl.mem unconfirmedspentutxo (lr,aid)) ->
	   begin
	     match obl with
	     | None ->
		begin
		  let (p,xs) = alpha in
		  if p = 0 then (** only handling assets controlled by p2pkh addresses for now **)
		    begin
		      let s kl = List.find (fun (_,_,_,_,h,_) -> h = xs) kl in
		      try
			let (k,c,(x,y),_,h,_) = try s !Commands.walletkeys_staking with Not_found -> s !Commands.walletkeys_nonstaking in
			gatheredkeys := (k,c,(x,y),h)::!gatheredkeys;
			gatheredassets := a::!gatheredassets;
			txinlr := (alpha,aid)::!txinlr;
			gathered := Int64.add !gathered v;
			esttxsize := !esttxsize + 300;
			if !gathered >= Int64.add amt (Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee) then raise Exit
		      with Not_found -> ()
		    end
		end
	     | Some(beta,_,_) ->
		begin
		  let (p,xs) = beta in
		  if not p then (** only handling assets controlled by p2pkh addresses for now **)
		    begin
		      let s kl = List.find (fun (_,_,_,_,h,_) -> h = xs) kl in
		      try
			let (k,c,(x,y),_,h,_) = try s !Commands.walletkeys_staking with Not_found -> s !Commands.walletkeys_nonstaking in
			gatheredkeys := (k,c,(x,y),h)::!gatheredkeys;
			gatheredassets := a::!gatheredassets;
			txinlr := (alpha,aid)::!txinlr;
			gathered := Int64.add !gathered v;
			esttxsize := !esttxsize + 300;
			if !gathered >= Int64.add amt (Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee) then raise Exit
		      with Not_found -> ()
		    end
		end
	   end
	| _ -> ())
      (Commands.get_spendable_assets_in_ledger oc lr blkh);
    raise CouldNotConsolidate
  with Exit -> ();;

let swappingthread () =
  log_string (Printf.sprintf "swapping thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let change = ref false in
  while true do
    try
      let (bb,_) = get_bestblock () in
      match bb with
      | None -> raise Not_found
      | Some(dbh,lbk,ltx) ->
	 let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	 let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
         let now = Unix.time() in
         change := false;
         swapbuyoffers :=
           List.filter
             (fun (h,pr,sbo) ->
               match sbo with
               | SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis) ->
                  let hh = hashval_hexstring h in
                  if ltc_unspent hh 1 then
                    true
                  else
                    begin
                      change := true;
                      false
                    end)
             !swapbuyoffers;
         let swapcandidatetxs1 = !swapcandidatetxs in
         List.iter
           (fun h -> ltc_getswaptransactioninfo h)
           swapcandidatetxs1;
         swapmatchoffers :=
           List.filter
             (fun (ltm,smo) ->
               match smo with
               | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,fakeltcfee) ->
                  begin
                    let caddr2 = p2shaddr_addr caddr in
                    match ctree_lookup_asset false true false caid (CHash(lr)) (0,caddr2) with
                    | Some(_,bday,None,_) ->
                       begin
                         ltm := now; (** seems to be current **)
                         try
	                   let s kl = List.find (fun (_,_,_,_,h,_) -> h = alphap) kl in
	                   let (k,b,(x,y),_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                           if Int64.sub blkh bday > 48L then (** expired, reclaim **)
                             begin
                               let tauin = [(caddr2,caid)] in
                               let tauout = [(p2pkhaddr_addr alphap,(None,Currency(Int64.sub atms (Int64.mul 1000L !Config.defaulttxfee)))) ] in
                               let tau = (tauin,tauout) in
                               let realltcfee = Int64.mul 100L (Int64.of_int fakeltcfee) in
                               let litoshisout = Int64.sub litoshis realltcfee in
                               let ltccontracttx = swapmatchoffer_ltccontracttx ltctxid alphal litoshisout in
                               let ltccontracttxid = hashval_rev (sha256dstr_hashval ltccontracttx) in
                               let (caddr3,credscr) = Script.createatomicswapcsv ltccontracttxid betap alphap 48l in
                               if caddr3 = caddr then
                                 begin
                                   log_string (Printf.sprintf "Redeeming expired swap\n");
                                   let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [(credscr,caddr)] [] (Some([(k,b,(x,y),alphap)])) in
                                   if (ci && co) then
                                     begin
                                       log_string (Printf.sprintf "Sending refund tx for expired swap contract\n");
                                       Commands.sendtx2 (!Utils.log) blkh 0L tr sr lr (stxsize stau) stau;
                                       change := true;
                                       false (* remove the match offer now *)
                                     end
                                   else
                                     begin
                                       log_string (Printf.sprintf "SWAPWARNING: could not sign to redeem expired contract.\n");
                                       true (* this is a bug, but keep it so we don't lose it *)
                                     end;
                                 end
                               else
                                 begin
                                   log_string (Printf.sprintf "SWAPWARNING: expired contract address mismatch\n");
                                   true (* this is a bug, but keep it so we don't lose it *)
                                 end
                             end
                           else
                             true
                         with
                         | Not_found -> (* I'm not the seller, delete eagerly, unless I'm the buyer *)
                            if Int64.sub blkh bday > 24L then (** old or expired; delete **)
                              begin
                                change := true;
                                false
                              end
                            else
                              if List.exists (fun (h,_,sbo) -> match sbo with SimpleSwapBuyOffer(lbeta,_,_,_) -> List.mem lbeta !Config.ltctradeaddresses) !swapbuyoffers then (** I'm the buyer; don't delete it so can try to spend it below **)
                                true
                              else (** not involved; if ltc utxo is spent then delete it **)
                                let hh = hashval_hexstring ltctxid in
                                if ltc_unspent hh 1 then
                                  true
                                else
                                  begin
                                    change := true;
                                    false
                                  end
                       end
                    | None ->
                       if now -. !ltm > 86400. then (** seems old, so assume the asset was spent already and not waiting to confirm **)
                         begin
                           change := true;
                           false
                         end
                       else
                         true
                    | _ -> (** nothing else should be possible, but just delete it if so **)
                       change := true;
                       false
                  end)
             !swapmatchoffers;
         Commands.swapredemptions :=
           List.filter
             (fun (ltccontracttxid,caddr,caid,betap,alphap) ->
               match ctree_lookup_asset false true false caid (CHash(lr)) (0,(p2shaddr_addr caddr)) with
               | Some(_,bday,None,Currency(atoms)) ->
                  let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid betap alphap 48l in
                  if caddr = caddr2 then
                    begin
                      match ltc_tx_confirmed (hashval_hexstring ltccontracttxid) with
                      | Some(n) when n >= 3 ->
                         begin
                           let atomsminusfee = Int64.sub atoms (Int64.mul 400L !Config.defaulttxfee) in
                           let txinl = [(p2shaddr_addr caddr,caid)] in
                           let txoutl = [(p2pkhaddr_addr betap,(None,Currency(atomsminusfee)))] in
                           let tau = (txinl,txoutl) in
                           let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [(credscr2,caddr)] [] None in
                           if (ci && co) then
                             begin
                               let redtxid = hashstx stau in
                               log_string (Printf.sprintf "Publishing redemption tx %s for completing swap with contract address %s. Must confirm within %Ld blocks or might lose funds.\n" (hashval_hexstring redtxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (Int64.sub (Int64.add bday 48L) blkh));
                               Commands.sendtx2 !Utils.log blkh 0L tr sr lr (stxsize stau) stau; (** publish tx and remove from redemption list **)
                               unconfswapredemptions := (redtxid,Int64.add bday 48L,stau)::!unconfswapredemptions;
                               false
                             end
                           else
                             begin
                               log_string (Printf.sprintf "SWAPWARNING: Trouble signing redemption for swap with ltc tx %s and contract address %s. In %Ld blocks might lose funds.\n" (hashval_hexstring ltccontracttxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (Int64.sub (Int64.add bday 48L) blkh));
                               true
                             end
                         end
                      | _ -> true (** waiting for enough confirmations of ltc tx **)
                    end
                  else
                    begin
                      log_string (Printf.sprintf "SWAPWARNING: Contract address mismatch: computed %s but expected %s.\nIf this is not resolved quickly, funds may be lost.\n" (addr_pfgaddrstr (p2shaddr_addr caddr2)) (addr_pfgaddrstr (p2shaddr_addr caddr)));
                      true
                    end
               | None -> false (** asset has been spent so either redemption or refund already happened **)
               | _ -> false) (** other cases should be impossible (noncurrency assets or nondefault obligation), but if slips in then delete it **)
             !Commands.swapredemptions;
         List.iter
           (fun (h,pr,sbo) ->
             match sbo with
             | SimpleSwapBuyOffer(lbeta,(zp,zs),atoms,litoshis) when zp = 0 ->
                if List.mem lbeta !Config.ltctradeaddresses then (** check for match offers to accept; could generalize to check for higher bidding matches leading to something like an auction **)
                  begin
                    if ltc_unspent (hashval_hexstring h) 1 then (** if haven't already done it **)
                      begin
                        try
                          List.iter
                            (fun (_,smo) ->
                              match smo with
                              | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atoms2,litoshis2,lalpha160,alphap,betap,fakeltcfee) when ltctxid = h && atoms2 >= atoms && Int64.mul 100L (Int64.of_int fakeltcfee) >= !Config.minltctxfee ->
                                 begin
                                   match ctree_lookup_asset false true false caid (CHash(lr)) (0,(p2shaddr_addr caddr)) with
                                   | Some(_,bday,None,Currency(atoms3)) when atoms2 = atoms3 ->
                                      begin
                                        let n = Int64.sub blkh bday in
                                        if n >= 3L && n <= 24L then (** active range **)
                                          begin
                                            log_string (Printf.sprintf "Accepting swap with contract address %s\n" (addr_pfgaddrstr (p2shaddr_addr caddr)));
                                            let realltcfee = Int64.mul (Int64.of_int fakeltcfee) 100L in
                                            let litoshisout = Int64.sub litoshis realltcfee in
                                            let ltccontracttx = swapmatchoffer_ltccontracttx h lalpha160 litoshisout in
                                            let ltccontracttxid = hashval_rev (sha256dstr_hashval ltccontracttx) in
                                            let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid zs alphap 48l in
                                            if not (caddr = caddr2) then
                                              begin
                                                log_string (Printf.sprintf "SWAPWARNING: Contract address mismatch: computed %s but expected %s.\nNot accepting match, but this must be a bug.\n" (addr_pfgaddrstr (p2shaddr_addr caddr2)) (addr_pfgaddrstr (p2shaddr_addr caddr)));
                                              end
                                            else
                                              begin
                                                let ltccontracttxhex = string_hexstring ltccontracttx in
                                                try
                                                  let ltccontracttxsignedhex = ltc_signrawtransaction ltccontracttxhex in
                                                  try
                                                    let h = ltc_sendrawtransaction ltccontracttxsignedhex in
                                                    if h = hashval_hexstring ltccontracttxid then
                                                      begin
                                                        log_string (Printf.sprintf "Seem to have successfully signed and published ltc swap contract tx %s\n" h);
                                                        Commands.swapredemptions := (ltccontracttxid,caddr,caid,betap,alphap)::!Commands.swapredemptions
                                                      end
                                                    else
                                                      log_string (Printf.sprintf "SWAP WARNING: Signed and published ltc contract tx but txid was %s instead of %s. Debug or funds may be lost!\n" h (hashval_hexstring ltccontracttxid))
                                                  with Not_found ->
                                                    log_string (Printf.sprintf "Failed with accepting swap match since could not send presumably signed ltc tx: %s\n" ltccontracttxsignedhex)
                                                with Not_found ->
                                                  log_string (Printf.sprintf "Failed with accepting swap match since could not sign ltc tx: %s\n" ltccontracttxhex)
                                              end
                                          end
                                      end
                                   | _ -> ()
                                 end
                              | _ -> ())
                            !swapmatchoffers
                        with
                        | Exit -> ()
                      end
                  end
                else if not (List.exists (fun (_,smo) -> match smo with SimpleSwapMatchOffer(_,ltctxid,_,_,_,_,_,_,_,_) -> ltctxid = h) !swapmatchoffers) (** don't make offers if an offer exists; could generalize to outbig existing offers by others **)
                then
                  begin
                    try
                      let (lalpha,prsell,minatoms,maxatoms) as sof =
                        List.find
                          (fun (lalpha,pr2,minatoms,maxatoms) ->
                            pr2 <= pr && minatoms <= atoms && atoms <= maxatoms)
                          !Commands.swapselloffers
                      in
                      (** create a match offer **)
                      let fakeltcfee =
                        if Int64.rem !Config.ltctxfee 100L = 0L then
                          Int64.div !Config.ltctxfee 100L
                        else
                          Int64.add 1L (Int64.div !Config.ltctxfee 100L)
                      in
                      if fakeltcfee <= 4000L then
                        let realltcfee = Int64.mul fakeltcfee 100L in
                        begin
                          try
                            let lalpha160 = ltcbech32_be160 lalpha in
                            let litoshisout = Int64.sub litoshis realltcfee in
                            let ltccontracttx = swapmatchoffer_ltccontracttx h lalpha160 litoshisout in
                            let ltccontracttxid = hashval_rev (sha256dstr_hashval ltccontracttx) in
                            let (k,alphap) =
                              Commands.generate_newkeyandaddress lr "nonstaking"
                            in
                            let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid zs alphap 48l in
	                    let esttxsize = ref 500 in
	                    let gathered = ref 0L in
	                    let gatheredkeys = ref [] in
	                    let gatheredassets = ref [] in
	                    let txinlr = ref [] in
                            consolidate_spendable !Utils.log blkh lr (Int64.add atoms (Int64.mul 450000L !Config.defaulttxfee)) esttxsize gathered gatheredkeys gatheredassets txinlr;
	                    let minfee = Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee in
	                    let change = Int64.sub !gathered (Int64.add atoms minfee) in
                            let lalphap = p2pkhaddr_addr lalpha160 in
                            let txoutl =
                              [(p2shaddr_addr caddr2,(None,Currency(atoms)));
                               (lalphap,(Some(p2pkhaddr_payaddr alphap,fakeltcfee,false),Currency(change)))]
                            in
                            let tau = (!txinlr,txoutl) in
                            let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [] [] (Some(!gatheredkeys)) in
                            if (ci && co) then
                              begin
                                if not (List.mem lalphap !Commands.walletwatchaddrs) then Commands.walletwatchaddrs := lalphap::!Commands.walletwatchaddrs;
                                log_string (Printf.sprintf "Creating Swap Match for Buy Offer with ltc txid %s\nRefund address: %s (key %s)\nContract address: %s\nscript\n" (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr alphap)) (pfgwif k true) (addr_pfgaddrstr (p2shaddr_addr caddr2)));
                                List.iter (fun by -> Printf.fprintf !Utils.log "%02x" by) credscr2;
                                Printf.fprintf !Utils.log "\n";
	                        let s = Buffer.create 100 in
	                        seosbf (seo_stx seosb stau (s,None));
	                        let hs = Hashaux.string_hexstring (Buffer.contents s) in
	                        Printf.fprintf !Utils.log "tx: %s\n" hs;
                                flush !Utils.log;
                                Commands.sendtx2 (!Utils.log) blkh 0L tr sr lr (stxsize stau) stau;
                                let ctm = ref (Unix.time()) in
                                swapmatchoffers := (ctm,SimpleSwapMatchOffer(hashstx stau,h,caddr2,hashpair (hashtx tau) (hashint32 0l),atoms,litoshis,lalpha160,alphap,zs,Int64.to_int fakeltcfee)) :: !swapmatchoffers;
                                let maxatoms2 = Int64.sub maxatoms atoms in
                                if maxatoms2 >= minatoms then
                                  Commands.swapselloffers := List.map (fun sof2 -> if sof = sof2 then (lalpha,prsell,minatoms,maxatoms2) else sof2) !Commands.swapselloffers (* remove some atoms from the sell offer so it does not get used to match twice *)
                                else
                                  Commands.swapselloffers := List.filter (fun sof2 -> not (sof = sof2)) !Commands.swapselloffers; (* remove the sell offer so it does not get used to match twice *)
                                Commands.save_swaps false;
                                List.iter
                                  (fun (alpha,aid) -> Hashtbl.add unconfirmedspentutxo (lr,aid) ())
                                  !txinlr
                              end
                            else
                              log_string (Printf.sprintf "Not able to match buy offer since could not fully sign consolidation tx for %s bars.\n" (bars_of_atoms atoms));
                          with
                          | InvalidBech32 ->
                             log_string (Printf.sprintf "Could not match buy offer since %s is an invalid bech32 address.\n" lalpha);
                          | CouldNotConsolidate ->
                             log_string (Printf.sprintf "Not able to match buy offer since cannot consolidate %s bars.\n" (bars_of_atoms atoms));
                        end
                    with
                    | Not_found -> ()
                  end
             | _ -> ())
           !swapbuyoffers;
         Thread.delay 30.0
    with exn ->
      log_string (Printf.sprintf "swapping thread %d exception %s\n" (Thread.id (Thread.self())) (Printexc.to_string exn));
      Thread.delay 300.0
  done;;

(*** if only one ledger root is in the snapshot, assets, hconselts and ctreeelts will not be revisited, so no need to waste memory by saving them in fin ***)
let snapshot_fin_mem fin h = 
  (List.length !snapshot_ledgerroots > 1) && Hashtbl.mem fin h

let snapshot_fin_add fin h =
  if List.length !snapshot_ledgerroots > 1 then
    Hashtbl.add fin h ()

let dbledgersnapshot_asset assetfile fin h =
  if not (snapshot_fin_mem fin h) then
    begin
      snapshot_fin_add fin h;
      try
        let a = DbAsset.dbget h in
        seocf (seo_asset seoc a (assetfile,None))
      with Not_found ->
        Printf.printf "Could not find %s asset in database\n" (hashval_hexstring h)
    end

let rec dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l =
  if not (snapshot_fin_mem fin h) then
    begin
      snapshot_fin_add fin h;
      try
	let (ah,hr) = DbHConsElt.dbget h in
        seocf (seo_prod seo_hashval (seo_option (seo_prod seo_hashval seo_int8)) seoc (ah,hr) (hconseltfile,None));
	dbledgersnapshot_asset assetfile fin ah;
	match hr with
	| Some(hr,l2) ->
	    if not (l = l2+1) then Printf.printf "Length mismatch in hconselt %s: expected length %d after cons but rest has claimed length %d.\n" (hashval_hexstring h) l l2;
	    dbledgersnapshot_hcons (hconseltfile,assetfile) fin hr l2
	| None ->
	    if not (l = 1) then Printf.printf "Length mismatch in hconselt %s: expected length %d after cons but claimed to have no extra elements.\n" (hashval_hexstring h) l;
	    ()
      with Not_found ->
	Printf.printf "Could not find %s hcons element in database\n" (hashval_hexstring h)
    end

let rec dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h =
  if not (snapshot_fin_mem fin h) && (!snapshot_full || not (supp = [])) then
    begin
      snapshot_fin_add fin h;
      try
	let c = expand_ctree_atom_or_element false h in
	seocf (seo_ctree seoc c (ctreeeltfile,None));
	dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin supp c
      with Not_found ->
	Printf.printf "Could not find %s ctree element in database\n" (hashval_hexstring h)
    end
and dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin supp c =
  match c with
  | CLeaf(bl,NehHash(h,l)) ->
      dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l
  | CLeaf(bl,_) ->
      Printf.printf "non element ctree found in database\n"
  | CHash(h) -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
  | CLeft(c0) -> dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_left0 supp) c0
  | CRight(c1) -> dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_right0 supp) c1
  | CBin(c0,c1) ->
      dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_left0 supp) c0;
      dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_right0 supp) c1

let rec dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin supp c sl =
  if not (sl = []) then
    match c with
    | CLeaf(bl,NehHash(h,l)) ->
	dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l
    | CLeaf(bl,_) ->
	Printf.printf "non element ctree found in database\n"
    | CHash(h) -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
    | CLeft(c0) -> dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_left0 supp) c0 (strip_location_left0 sl)
    | CRight(c1) -> dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_right0 supp) c1 (strip_location_right0 sl)
    | CBin(c0,c1) ->
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_left0 supp) c0 (strip_location_left0 sl);
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_location_right0 supp) c1 (strip_location_right0 sl)

let dbledgersnapshot_shards (ctreeeltfile,hconseltfile,assetfile) fin supp h sl =
  if not (snapshot_fin_mem fin h) && (!snapshot_full || not (supp = [])) then
    begin
      snapshot_fin_add fin h;
      try
	let c = expand_ctree_atom_or_element false h in
	seocf (seo_ctree seoc c (ctreeeltfile,None));
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin supp c sl
      with Not_found ->
	Printf.printf "Could not find %s ctree element in database\n" (hashval_hexstring h)
    end

  (** not sure how fix this so comment it out for now
let dbledgersnapshot_ctree_top (ctreeeltfile,hconseltfile,assetfile) fin supp h s =
  match s with
  | None -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
  | Some(sl) ->
      let bitseq j =
	let r = ref [] in
	for i = 0 to 8 do
	  if ((j lsr i) land 1) = 1 then
	    r := true::!r
	  else
	    r := false::!r
	done;
	Bitlist.of_bools !r
      in
      dbledgersnapshot_shards (ctreeeltfile,hconseltfile,assetfile) fin supp h (List.map (fun x -> (0,x)) sl);;
   **)
  
let parse_json_privkeys kl =
  let (klj,_) = parse_jsonval kl in
  match klj with
  | JsonArr(kla) ->
      List.map
	(fun kj ->
	  match kj with
	  | JsonStr(k) ->
	    begin
	      let (k,b) = 
		try
		  privkey_from_wif k
		with _ ->
		  try
		    privkey_from_btcwif k
		  with _ -> raise (Failure "Bad private key")
	      in
	      match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = hashval_be160 (pubkey_hashval (x,y) b) in
		  (k,b,(x,y),h)
	      | None -> raise (Failure "Bad private key")
	    end
	  | _ -> raise BadCommandForm)
	kla
  | _ -> raise BadCommandForm;;

let parse_json_redeemscripts rl =
  let (rlj,_) = parse_jsonval rl in
  match rlj with
  | JsonArr(rla) ->
      List.map
	(fun rj ->
	  match rj with
	  | JsonStr(r) -> 
	      let il = string_bytelist (hexstring_string r) in
	      (il,Script.hash160_bytelist il)
	  | _ -> raise BadCommandForm)
	rla
  | _ -> raise BadCommandForm;;

let parse_json_secrets sl =
  let (slj,_) = parse_jsonval sl in
  match slj with
  | JsonArr(sla) ->
      List.map
	(fun sj ->
	  match sj with
	  | JsonStr(s) -> 
	      let sh = hexstring_hashval s in
	      let shh = Script.sha256_bytelist (string_bytelist (hexstring_string s)) in
	      (sh,shh)
	  | _ -> raise BadCommandForm)
	sla
  | _ -> raise BadCommandForm;;
	
let commandh : (string,(string * string * (out_channel -> string list -> unit))) Hashtbl.t = Hashtbl.create 100;;
let sortedcommands : string list ref = ref [];;

let local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy =
  try
    Hashtbl.find remgvtpth oidthy
  with Not_found ->
    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
    match hlist_lookup_obj_owner true true true oidthy hl with
    | None -> raise Not_found
    | Some(beta,r) -> (beta,r);;

let local_lookup_prop_thy_owner lr remgvknth pidthy alphathy =
  try
    Hashtbl.find remgvknth pidthy
  with Not_found ->
    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
    match hlist_lookup_prop_owner true true true pidthy hl with
    | None -> raise Not_found
    | Some(beta,r) -> (beta,r);;

let ac c h longhelp f =
  sortedcommands := List.merge compare [c] !sortedcommands;
  Hashtbl.add commandh c (h,longhelp,(fun oc al -> try f oc al with BadCommandForm -> Printf.fprintf oc "%s\n" h));;

let validusername_p u =
  if u = "" || String.length u > 32 then
    false
  else
    begin
      try
        for i = 0 to String.length u - 1 do
          let ci = Char.code u.[i] in
          if not ((ci >= 48 && ci <= 57) || (ci >= 65 && ci <= 90) || (ci >= 97 && ci <= 122) || (ci = 95)) then raise Exit
        done;
        true
      with Exit -> false
    end;;

let identities : (string,bool * Z.t * (Z.t * Z.t) * addr) Hashtbl.t = Hashtbl.create 10;;
let othidentities : (string,bool * (Z.t * Z.t) * addr) Hashtbl.t = Hashtbl.create 10;;

let identities_loaded = ref false;;

let identity_pubkey u =
  try
    let (_,(x,y),_) = Hashtbl.find othidentities u in
    (x,y)
  with
  | Not_found ->
     let (_,_,(x,y),_) = Hashtbl.find identities u in
     (x,y)

let load_identities () =
  if not (!identities_loaded) then
    begin
      identities_loaded := true;
      let idfn = Filename.concat (datadir()) "ids" in
      if Sys.file_exists idfn then
        begin
          let f = open_in idfn in
          try
            while true do
              let u = input_line f in
              let alpha = input_line f in
              let pubkey = input_line f in
              let privkey = input_line f in
              try
                let alpha = Cryptocurr.pfgaddrstr_addr alpha in
                let ((x,y),_) = Cryptocurr.hexstring_pubkey pubkey in
                let (k,b) = Cryptocurr.privkey_from_wif privkey in
                Hashtbl.add identities u (b,k,(x,y),alpha)
              with _ -> ()
            done
          with End_of_file ->
            close_in_noerr f;
        end;
      let idfn = Filename.concat (datadir()) "otherids" in
      if Sys.file_exists idfn then
        begin
          let f = open_in idfn in
          try
            while true do
              let u = input_line f in
              let alpha = input_line f in
              let pubkey = input_line f in
              try
                let alpha = Cryptocurr.pfgaddrstr_addr alpha in
                let ((x,y),b) = Cryptocurr.hexstring_pubkey pubkey in
                Hashtbl.add othidentities u (b,(x,y),alpha)
              with _ -> ()
            done
          with End_of_file ->
            close_in_noerr f
        end
    end;;

let find_spendable_utxo oc lr blkh mv =
  let b = ref None in
  List.iter
    (fun (alpha,a,v) ->
      if v >= mv && (match a with (aid,_,_,Currency(_)) when not (Hashtbl.mem unconfirmedspentutxo (lr,aid)) -> true | _ -> false) then
	match !b with
	| None -> b := Some(alpha,a,v)
	| Some(_,_,u) -> if v < u then b := Some(alpha,a,v))
    (Commands.get_spendable_assets_in_ledger oc lr blkh);
  match !b with
  | None -> raise Not_found
  | Some(alpha,a,v) ->
      Hashtbl.add unconfirmedspentutxo (lr,assetid a) ();
      (alpha,a,v);;

let rec find_marker_in_hlist hl =
  match hl with
  | HNil -> raise Not_found
  | HCons((aid,bday,obl,Marker),_) -> (aid,bday,obl)
  | HCons(_,hr) -> find_marker_in_hlist hr
  | HConsH(h,hr) ->
      let a = get_asset h in
      find_marker_in_hlist (HCons(a,hr))
  | HHash(h,_) ->
      find_marker_in_hlist (get_hlist_element h)

let find_marker_at_address tr beta =
  let hl = ctree_lookup_addr_assets true true tr (0,beta) in
  find_marker_in_hlist hl

let initialize_commands () =
  ac "version" "version" "Print client description and version number"
    (fun oc _ ->
      Printf.fprintf oc "%s %s\n" Version.clientdescr Version.clientversion);
  ac "headerhex" "headerhex" "headerhex" (* delete *)
    (fun oc al ->
      match al with
      | [h] ->
         let h = hexstring_hashval h in
         let bh = DbBlockHeader.dbget h in
         Printf.fprintf oc "id: %s\n" (hashval_hexstring (blockheader_id bh));
         let (bhd,bhs) = bh in
         Printf.fprintf oc "prevledgerroot: %s\n" (hashval_hexstring (ctree_hashroot bhd.prevledger));
         let b = Buffer.create 10 in
         seosbf (seo_blockheader seosb bh (b,None));
         Printf.fprintf oc "%s\n" (string_hexstring (Buffer.contents b));
      | _ -> ());
  ac "retractltcblockandexit" "retractltcblockandexit <ltcblock>" "Purge ltc information back to the given block and exit.\nWhen Proofgold restarts it will resync with ltc back to the retracted block."
    (fun oc al ->
      match al with
      | [h] -> (try ltc_listener_paused := true; retractltcblock h; !exitfn 0 with e -> Printf.fprintf oc "%s\n" (Printexc.to_string e); !exitfn 7)
      | _ -> raise BadCommandForm);
  ac "sendtoaddress" "sendtoaddress <address> <bars> [<lockheight>]" "Consolidate enough spendable utxos to send the given number of bars to the given address.\nIf the address is a term address, then the bars are put as a bounty.\nIf a lockheight is given and the address is a pay address,\n then the new asset is locked until the given height."
    (fun oc al ->
      let (a,v,lh) =
        match al with
        | [a;v] ->
           (a,v,None)
        | [a;v;lh] ->
           (a,v,Some(Int64.of_string lh))
        | _ -> raise BadCommandForm
      in
      let gamma = pfgaddrstr_addr a in
      if pubaddr_p gamma then (Printf.fprintf oc "%s is a publication address, so neither currency nor bounty can be sent there.\n" a; raise BadCommandForm);
      let amt = Cryptocurr.atoms_of_bars v in
      let esttxsize = ref 500 in
      let gathered = ref 0L in
      let gatheredkeys = ref [] in
      let gatheredassets = ref [] in
      let txinlr = ref [] in
      begin
	let (blkh,tm,lr,tr,sr) =
	  match get_bestblock_print_warnings oc with
	  | None -> raise Not_found
	  | Some(dbh,lbk,ltx) ->
	     let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	     let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
	     (blkh,tm,lr,tr,sr)
	in
	try
          consolidate_spendable oc blkh lr amt esttxsize gathered gatheredkeys gatheredassets txinlr;
	  let minfee = Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee in
	  let change = Int64.sub !gathered (Int64.add amt minfee) in
          let newpreasset = if termaddr_p gamma then Bounty(amt) else Currency(amt) in
          let obl =
            if termaddr_p gamma then
              None
            else
              match lh with
              | None -> None
              | Some(lh) ->
                 if lh <= blkh then
                   raise (Failure "lockheight must be greater than current height")
                 else
                   let (p,xs) = gamma in
                   Some((p=1,xs),lh,false)
          in
	  let txoutl =
	    if change >= 10000L then
	      let (_,delta) = Commands.generate_newkeyandaddress lr "" in
	      [(gamma,(obl,newpreasset));(p2pkhaddr_addr delta,(None,Currency(change)))]
	    else
	      [(gamma,(obl,newpreasset))]
	  in
	  let stau = ((!txinlr,txoutl),([],[])) in
	  let (stau,ci,co) = Commands.signtx2 oc lr stau [] [] (Some(!gatheredkeys)) in
	  if (ci && co) then
            begin
	      Commands.sendtx2 oc blkh tm tr sr lr (stxsize stau) stau;
              List.iter
                (fun (alpha,aid) -> Hashtbl.add unconfirmedspentutxo (lr,aid) ())
                !txinlr
            end
	  else
	    Printf.fprintf oc "Transaction was created but only partially signed and so was not sent.\n"
	with CouldNotConsolidate ->
	  Printf.fprintf oc "Could not consolidate enough spendable currency to send %s to address %s\n" v a
      end);
  ac "signmessage" "signmessage <address> <msg>" "Sign a message with the private key for the given address, assuming it is p2pkh and in the wallet."
    (fun oc al ->
      match al with
      | [a;m] ->
	 let alpha = pfgaddrstr_addr a in
	 let (p,xs) = alpha in
	 begin
	   if p = 0 then
	     begin
	       try
		 let s kl = List.find (fun (_,_,_,_,h,_) -> h = xs) kl in
		 let (k,b,_,_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                 let (_,(r,s)) = repeat_rand (sign_proofgold_message m k) rand_256 in
                 Printf.fprintf oc "%s\n" (encode_signature 0 b (r,s)) (** recid is just set to 0 here since pubkey recovery is not supported in proofgold signed messages **)
               with Not_found ->
                 Printf.fprintf oc "The private key for %s is not in your wallet.\n" a
             end
           else
             Printf.fprintf oc "%s is not a p2pkh address.\n" a
         end         
      | _ -> raise BadCommandForm);
  ac "signmessagewithkey" "signmessagewithkey <privkey> <msg>" "Sign a message with the private key (in WIF format)."
    (fun oc al ->
      match al with
      | [k;m] ->
         let (k,b) = privkey_from_wif k in
         let (_,(r,s)) = repeat_rand (sign_proofgold_message m k) rand_256 in
         Printf.fprintf oc "%s\n" (encode_signature 0 b (r,s))
      | _ -> raise BadCommandForm);
  ac "verifymessage" "verifymessage <pubkey> <signature> <msg>" "Verify the signature of the message by the key for the pubkey is valid."
    (fun oc al ->
      match al with
      | [pk;sg;m] ->
         let (q,b) = hexstring_pubkey pk in
         let (_,fcomp,(r,s)) = decode_signature sg in
         if b = fcomp && verifyproofgoldmessage (Some(q)) (r,s) m then
           Printf.fprintf oc "Valid\n"
         else
           Printf.fprintf oc "Invalid\n"
      | _ -> raise BadCommandForm);
  ac "importid" "(deprecated) importid <username> <address>" "(deprecated) Locally associate a username with an address in the local wallet.\nThis identity is assumed to already have been registered with registerid."
    (fun oc al -> Printf.fprintf oc "importid is deprecated");
  ac "registerid" "(deprecated) registerid <username> <address>" "(deprecated) Associate a pubkey (the one for the given address) with a username on proofgold.org.\nThis can then be used to exchange private messages (end-to-end encrypted)\nwith other registered users via the pm command.\nThe address must be a p2pkh address in the wallet.\nThe command newaddress can be used to obtain a fresh p2pkh address.\nThe commands importprivkey and importbtcprivkey can be used if you have a private key for a p2pkh address in WIF Format."
    (fun oc al -> raise (Failure "registerid is deprecated"));
  ac "getid" "(deprecated) getid <username>" "(deprecated) Try to get the pubkey associated with a username registered on proofgold.org."
    (fun oc al -> raise (Failure "getid is deprecated"));
  ac "getmessages" "(deprecated) getmessages <user> [<timestamp>]" "(deprecated) Get all private messages for the user since the given timestamp.\nIf no timestamp is given, all messages from the past week are downloaded."
    (fun oc al -> raise (Failure "getmessages is deprecated"));
  ac "savemessages" "(deprecated) savemessages <user> <file> [<timestamp>]" "(deprecated) Get all private messages for the user since the given timestamp and save them into the given file.\nIf no timestamp is given, all messages from the past week are downloaded."
    (fun oc al -> raise (Failure "savemessages is deprecated"));
  ac "pm" "(deprecated) pm <fromuser> <touser> <text>" "(deprecated) Send the (short) text as a private message."
    (fun oc al -> raise (Failure "pm is deprecated"));
  ac "pmfile" "(deprecated) pmfile <fromuser> <touser> <filename>" "(deprecated) Send the contents of the given text file as a private message."
    (fun oc al -> raise (Failure "pmfile is deprecated"));
  ac "posttop" "(deprecated) posttop <user> <text>" "(deprecated) Post in the top level of the latest anon topic on the proofgold forum.\nThe given username is assumed to be registered with registerid."
    (fun oc al -> raise (Failure "posttop is deprecated"));
  ac "postreply" "(deprecated) postreply <user> <parentid> <text>" "(deprecated) Post reply on the proofgold forum"
    (fun oc al -> raise (Failure "postreply is deprecated"));
  ac "selloffers" "selloffers"
    "Show the current local sell offers of the node."
    (fun oc al ->
      List.iter
        (fun (lalpha,pr,minatoms,maxatoms) ->
          Printf.fprintf oc "%f %s [%s,%s]\n" pr lalpha (bars_of_atoms minatoms) (bars_of_atoms maxatoms))
        !Commands.swapselloffers);
  ac "buyoffers" "buyoffers"
    "Show all active buy offers, indicating which are by the local node."
    (fun oc al ->
      List.iter
        (fun (h,pr,sbo) ->
          match sbo with
          | SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis) ->
             let hh = hashval_hexstring h in
             if List.mem lbeta !Config.ltctradeaddresses then Printf.fprintf oc "[LOCAL] ";
             Printf.fprintf oc "%f %s %s litecoins for %s proofgold bars\n" pr hh (ltc_of_litoshis litoshis) (bars_of_atoms atoms))
        !swapbuyoffers);
  ac "swapredemptions" "swapredemptions"
    "Show all swap redemptions in progress (completing the buying of pfg via a swap with ltc)"
    (fun oc al ->
      List.iter
        (fun (ltctxid,caddr,caid,betap,alphap) ->
          Printf.fprintf oc "* ltctx: %s\ncontract %s: %s\nMy address (buyer): %s\nRefund address (seller): %s\n" (hashval_hexstring ltctxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (hashval_hexstring caid) (addr_pfgaddrstr (p2pkhaddr_addr betap)) (addr_pfgaddrstr (p2pkhaddr_addr alphap)))
        !Commands.swapredemptions);
  ac "matchoffers" "matchoffers"
    "Show all current match offers, indicating which correspond to the local node."
    (fun oc al ->
      List.iter
        (fun (_,smo) ->
          match smo with
          | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,ltcfee) ->
             begin
               try
	         let s kl = List.find (fun (_,_,_,_,h,_) -> h = alphap) kl in
	         let (_,_,_,_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                 Printf.fprintf oc "* [LOCAL] Match offer for ltc buy offer %s\nContract address: %s\n" (hashval_hexstring ltctxid) (addr_pfgaddrstr (p2shaddr_addr caddr))
               with Not_found ->
                 Printf.fprintf oc "* Match offer for ltc buy offer %s\n" (hashval_hexstring ltctxid)
             end)
        !swapmatchoffers);
  ac "createswapselloffer" "createswapselloffer <price> <minamt> <maxamt>"
    "Create a local (not advertised) offer to sell some pfg for ltc via an atomic swap.\nThis will be used to match public buy offers."
    (fun oc al ->
      match !Config.ltctradeaddresses with
      | [] -> Printf.fprintf oc "Cannot set up a sell offer until at least one bech32 litecoin address\nis given via ltctradeaddress in proofgold.conf file.\n";
      | (lalpha::_) ->
         match al with
         | [pr;mi;ma] ->
            let pr = float_of_string pr in
            let minatoms = atoms_of_bars mi in
            let maxatoms = atoms_of_bars ma in
            if minatoms > maxatoms then
              raise (Failure "minamount must be <= to maxamount")
            else
              Commands.swapselloffers := List.merge (fun (_,p1,_,_) (_,p2,_,_) -> compare p1 p2) [(lalpha,pr,minatoms,maxatoms)] !Commands.swapselloffers
         | _ -> raise BadCommandForm);
  ac "cancelswapselloffers" "cancelswapselloffers"
    "Cancels all local swap sell offers.\n"
    (fun oc al -> Commands.swapselloffers := []; Commands.save_swaps false);
  ac "createswapbuyoffer" "createswapbuyoffer <pfgaddr> <price> <pfgamount> <ltcamount>"
    "Create a public offer to buy proofgold bars via an atomic swap.\nThe price is given in LTC:PFG, e.g., 0.01 means 0.01 litecoins per proofgold.\nThe amount is then given in both the amount of proofgold to buy and litecoins to spend.\nIf the ratio does not match the price within a 1% tolerance the swap buy offer is not created.\nLines of the form ltctradeaddress=<address> in proofgold.conf\n give segwit addresses to use for swaps.\nIf successful, this command will create a litecoin tx that makes the terms of the swap\nand the utxo for the swap explicit.\n"
    (fun oc al ->
      match al with
      | [pbetastr;pr;pfgamt;ltcamt] ->
         let pbeta = pfgaddrstr_addr pbetastr in
         if not (p2pkhaddr_p pbeta) then raise (Failure "proofgold address for swap must be p2pkh");
         let prg = float_of_string pr in
         let atoms = atoms_of_bars pfgamt in
         let litoshis = litoshis_of_ltc ltcamt in
         let prc = Int64.to_float litoshis *. 1000.0 /. Int64.to_float atoms in
         let prf = prg /. prc in
         if prf < 0.99 || prf > 1.01 then raise (Failure "Given price is more than 1% off from computed price. Not making offer.");
	 begin
	   try
	     let ltctxid = ltc_createswapoffertx pbeta litoshis atoms in
             Printf.fprintf oc "If you decide to cancel this swap offer, use:\ncancelswapbuyoffer %s\n" ltctxid;
           with InsufficientLtcFunds -> raise (Failure "Insufficient LTC funds to create swap buy offer. (There must be a single utxo in an ltctradeaddress to fund the swap buy offer.)")
         end
      | _ -> raise BadCommandForm);
  ac "cancelswapbuyoffer" "cancelswapbuyoffer <txid>"
    "Cancel an atomic swap by spending the ltc utxo for the swap to a local ltcaddress.\nLines of the form ltctradeaddress=<address> in proofgold.conf\n give segwit addresses to use for swaps.\n"
    (fun oc al ->
      match al with
      | [h] -> ltc_cancelswapbuyoffer h
      | _ -> raise BadCommandForm);
  ac "scanforswapbuyoffers" "scanforswapbuyoffers [<num>]"
    "Scans recent ltc blocks for swap buy offers.\nThe number of blocks can optionally be given with default 1000"
    (fun oc al ->
      let n =
        match al with
        | [] -> 1000
        | [n] -> int_of_string n
        | _ -> raise BadCommandForm
      in
      ltc_scanforswapbuyoffers n);
  ac "getaddressinfo" "getaddressinfo <address>" "Print information about address"
    (fun oc al ->
      match al with
      | [a] ->
	  let alpha = pfgaddrstr_addr a in
	  let (p,xs) = alpha in
	  let jol = ref [] in
	  begin
	    if p = 0 then
	      begin
		jol := ("address",JsonStr("p2pkh"))::!jol;
		try
		  let s kl = List.find (fun (_,_,_,_,h,_) -> h = xs) kl in
		  let (_,b,(x,y),_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
		  if b then
		    if evenp y then
		      jol := ("pubkey",JsonStr(Printf.sprintf "02%s" (Be256.to_hexstring (big_int_be256 x))))::!jol
		    else
		      jol := ("pubkey",JsonStr(Printf.sprintf "03%s" (Be256.to_hexstring (big_int_be256 x))))::!jol
		  else
		    jol := ("pubkey",JsonStr(Printf.sprintf "04%s%s" (Be256.to_hexstring (big_int_be256 x)) (Be256.to_hexstring (big_int_be256 y))))::!jol
		with Not_found -> ()
	      end
	    else if p = 1 then
	      begin
		jol := ("address",JsonStr("p2sh"))::!jol;
		let (_,_,bl) = List.find (fun (beta,_,_) -> xs = beta) !Commands.walletp2shs in
		let bu = Buffer.create 10 in
		List.iter (fun b -> Buffer.add_char bu (Char.chr b)) bl;
		jol := ("script",JsonStr(string_hexstring (Buffer.contents bu)))::!jol
	      end
	    else if p = 2 then
	      begin
		jol := ("address",JsonStr("term"))::!jol;
	      end
	    else if p = 3 then
	      begin
		jol := ("address",JsonStr("pub"))::!jol;
	      end
	    else
	      raise (Failure "apparently not an address");
	  end;
	  if not (!jol = []) then
	    begin
	      print_jsonval oc (JsonObj(List.rev !jol));
	      Printf.fprintf oc "\n";
	    end
      | _ -> raise BadCommandForm);
  ac "addnonce" "addnonce <file>" "Add a nonce to a theory specification file, a signature specification file or a document"
    (fun oc al ->
      match al with
      | [f] ->
	  begin
	    let ch = open_in f in
	    try
	      while true do
		let l = input_token ch in
		if l = "Nonce" then raise Exit
	      done
	    with
	    | Exit -> close_in_noerr ch; Printf.fprintf oc "A nonce was already declared.\nNo change was made.\n"
	    | End_of_file ->
		close_in_noerr ch;
		let ch = open_out_gen [Open_append] 0o600 f in
		let h = big_int_hashval (strong_rand_256()) in
		let nonce = hashval_hexstring h in
		Printf.fprintf ch "\nNonce %s\n" nonce;
		close_out_noerr ch
	    | e -> close_in_noerr ch; raise e
	  end
      | _ -> raise BadCommandForm);
  ac "addpublisher" "addpublisher <file> <payaddr>" "Add a publisher address to a theory specification file, a signature specification file or a document."
    (fun oc al ->
      match al with
      | [f;gammas] ->
	  begin
	    let gamma = Cryptocurr.pfgaddrstr_addr gammas in
	    if not (payaddr_p gamma) then raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." gammas));
	    let ch = open_in f in
	    try
	      while true do
		let l = input_token ch in
		if l = "Publisher" then raise Exit
	      done
	    with
	    | Exit -> close_in_noerr ch; Printf.fprintf oc "A publisher was already declared.\nNo change was made.\n"
	    | End_of_file ->
		close_in_noerr ch;
		let ch = open_out_gen [Open_append] 0o600 f in
		Printf.fprintf ch "\nPublisher %s\n" gammas;
		close_out_noerr ch
	    | e -> close_in_noerr ch; raise e
	  end
      | _ -> raise BadCommandForm);
  ac "readdraft" "readdraft <file>" "Read a theory specification file, signature specification file or document file and give information."
    (fun oc al ->
      match al with
      | [f] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,prophrev,propownsh,proprightsh) = input_theoryspec ch in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_theoryspec seosb thyspec (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Theory is too big: %d bytes. It probably will not fit in a block.\n" p;
              let counter = ref 0 in
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      let b = theoryspec_burncost thyspec in
		      Printf.fprintf oc "Theory is correct and has id %s and address %s.\n%s bars must be burned to publish the theory.\n" (hashval_hexstring thyh) (Cryptocurr.addr_pfgaddrstr (hashval_pub_addr thyh)) (bars_of_atoms b);
		      match nonce with
		      | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		      | Some(h) ->
			  Printf.fprintf oc "Nonce: %s\n" (hashval_hexstring h);
			  match gamma with
			  | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			  | Some(gamma) ->
			      if payaddr_p gamma then
				let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair h thyh)) in
				Printf.fprintf oc "Publisher address: %s\n" (Cryptocurr.addr_pfgaddrstr gamma);
				Printf.fprintf oc "Marker Address: %s\n" (Cryptocurr.addr_pfgaddrstr beta);
				let (_,kl) = thy in
				let pname h =
				  try
				    Hashtbl.find prophrev h
				  with Not_found -> ""
				in
				List.iter
				  (fun pidpure ->
				    let pidthy = hashtag (hashopair2 (Some(thyh)) pidpure) 33l in
				    let alphapure = hashval_term_addr pidpure in
				    let alphathy = hashval_term_addr pidthy in
				    let nm = pname pidpure in
				    begin
				      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
				      match hlist_lookup_prop_owner true true true pidpure hl with
				      | None ->
					  begin
					    let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
					    let rstr =
					      try
						let (delta2,r) = Hashtbl.find proprightsh (false,pidpure) in
						match r with
						| None -> "no rights available (unusable)"
						| Some(0L) -> "free to use"
						| Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
					      with Not_found -> "free to use"
					    in
					    Printf.fprintf oc "Pure proposition '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
					  end;
					  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
					  if not (bl = []) then
					    begin
					      Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the pure prop:\n" (Cryptocurr.addr_pfgaddrstr alphapure);
					      List.iter
						(fun (bid,_,_,b) ->
						  match b with
						  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
						  | _ -> raise (Failure "impossible"))
						bl
					    end
				      | Some(beta,r) ->
					  Printf.fprintf oc "Pure proposition '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
					    (match r with
					    | None -> "No right to use without defining; must leave as theorem in the document"
					    | Some(r) ->
						if r = 0L then
						  "free to use; consider changing to Known without proof"
						else
						  (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
				    end;
				    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
				    begin
				      match hlist_lookup_prop_owner true true true pidthy hl with
				      | None ->
					  begin
					    let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
					    let rstr =
					      try
						let (delta2,r) = Hashtbl.find proprightsh (true,pidpure) in
						match r with
						| None -> "no rights available (unusable)"
						| Some(0L) -> "free to use"
						| Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
					      with Not_found -> "free to use"
					    in
					    Printf.fprintf oc "Proposition '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
					  end;
					  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
					  if not (bl = []) then
					    begin
					      Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the theory prop:\n" (Cryptocurr.addr_pfgaddrstr alphathy);
					      List.iter
						(fun (bid,_,_,b) ->
						  match b with
						  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
						  | _ -> raise (Failure "impossible"))
						bl
					    end
				      | Some(beta,r) ->
					  Printf.fprintf oc "Proposition '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
					    (match r with
					    | None -> "No right to use without defining; must leave as definition in the document"
					    | Some(r) ->
						if r = 0L then
						  "free to use; consider changing Thm to Known"
						else
						  (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
				    end)
				  kl;
			      else
				raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_signaspec seosb signaspec (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Signature is too big: %d bytes. It probably will not fit in a block. Split it into multiple signatures.\n" p;
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  let b = signaspec_burncost signaspec in
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "%s bars must be burned to publish signature.\n" (Cryptocurr.bars_of_atoms b);
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition '%s' %s at %s when checking. Unexpected case.\n"
			  nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n";
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,_,objhrev,_,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh) = input_doc ch th sgt in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_doc seosb dl (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Document is too big: %d bytes. It probably will not fit in a block. Split it into multiple documents.\n" p;
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_doc counter gvtp gvkn th thy sgt dl with
	      | None -> raise (Failure "Document does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashdoc dl) in
		  Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Document imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Document mentions %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),_) -> Printf.fprintf oc " '%s' %s\n" (oname h) (hashval_hexstring h)) tml;
		  Printf.fprintf oc "Document mentions %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = doc_uses_objs dl in
		  let usesprops = doc_uses_props dl in
		  let createsobjs = doc_creates_objs dl in
		  let createsprops = doc_creates_props dl in
		  let createsnegpropsaddrs2 = List.map (fun h -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) (doc_creates_neg_props dl) in
		  Printf.fprintf oc "Document uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | None -> "No right to use; document cannot be published unless this is redefined.\n"
			  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use; document cannot be published unless this is redefined.\n"
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
		      with Not_found ->
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Document uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | None -> "No right to use; document cannot be published unless this is reproven."
			  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use; document cannot be published unless this is reproven."
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
		      with Not_found ->
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  Printf.fprintf oc "Document creates %d objects:\n" (List.length createsobjs);
		  List.iter
		    (fun (h,k) ->
		      let oidpure = h in
		      let oidthy = hashtag (hashopair2 th (hashpair h k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
		      let nm = oname oidpure in
		      begin
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find objownsh oidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find objrightsh (false,oidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Pure object '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <defname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <defname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <defname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end
			| Some(beta,r) ->
			    Printf.fprintf oc "Pure object '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    (Printf.sprintf "free to use; consider changing Def to Param %s if the definition is not needed" (hashval_hexstring oidpure))
				  else
				    (Printf.sprintf "Using the object without defining it would cost %Ld atoms; consider changing Def to Param %s if the definition is not needed" r (hashval_hexstring oidpure)))
		      end;
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
		      begin
			match hlist_lookup_obj_owner true true true oidthy hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find objownsh oidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find objrightsh (true,oidpure) in
				  match r with
				  | None -> "no rights available (unusable)"
				  | Some(0L) -> "free to use"
				  | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Object '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <defname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <defname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <defname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end
			| Some(beta,r) ->
			    Printf.fprintf oc "Object '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    (Printf.sprintf "free to use; consider changing Def to Param %s if the definition is not needed" (hashval_hexstring oidpure))
				  else
				    (Printf.sprintf "Using the object without defining it would cost %Ld atoms; consider changing Def to Param %s if the definition is not needed" r (hashval_hexstring oidpure)))
		      end)
		    createsobjs;
		  Printf.fprintf oc "Document creates %d props:\n" (List.length createsprops);
		  List.iter
		    (fun h ->
		      let pidpure = h in
		      let pidthy = hashtag (hashopair2 th h) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
		      let nm = pname pidpure in
		      begin
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find proprightsh (false,pidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Pure proposition '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end;
			    let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			    if not (bl = []) then
			      begin
				Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the pure prop:\n" (Cryptocurr.addr_pfgaddrstr alphapure);
				List.iter
				  (fun (bid,_,_,b) ->
				    match b with
				    | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				    | _ -> raise (Failure "impossible"))
				  bl
			      end
			| Some(beta,r) ->
			    Printf.fprintf oc "Pure proposition '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as theorem in the document"
			      | Some(r) ->
				  if r = 0L then
				    "free to use; consider changing to Known without proof"
				  else
				    (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
		      end;
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
		      begin
			match hlist_lookup_prop_owner true true true pidthy hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find proprightsh (true,pidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Proposition '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end;
			    let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			    if not (bl = []) then
			      begin
				Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the theory prop:\n" (Cryptocurr.addr_pfgaddrstr alphathy);
				List.iter
				  (fun (bid,_,_,b) ->
				    match b with
				    | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				    | _ -> raise (Failure "impossible"))
				  bl
			      end
			| Some(beta,r) ->
			    Printf.fprintf oc "Proposition '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    "free to use; consider changing Thm to Known"
				  else
				    (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
		      end)
		    createsprops;
		  Printf.fprintf oc "Document creates %d negprops:\n" (List.length createsnegpropsaddrs2);
		  List.iter
		    (fun alphathy ->
		      Printf.fprintf oc "%s\n" (addr_pfgaddrstr alphathy);
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
		      if hlist_lookup_neg_prop_owner true true true hl then
			Printf.fprintf oc "The negated proposition already has an owner.\n"
		      else
			begin
			  Printf.fprintf oc "Negated proposition has no owner.\nThe publisher address will be used to declare ownership of the negated proposition when publishing the document.\n";
			  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			  if not (bl = []) then
			    begin
			      Printf.fprintf oc "There are bounties you can claim by becoming the owner of the negated prop:\n";
			      List.iter
				(fun (bid,_,_,b) ->
				  match b with
				  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				  | _ -> raise (Failure "impossible"))
				bl
			    end
			end)
		    createsnegpropsaddrs2;
                  Printf.fprintf oc "Conjecture theory addresses:\n";
                  Hashtbl.iter
                    (fun nm pureh ->
		      let pid = hashtag (hashopair2 th pureh) 33l in
                      Printf.fprintf oc "%s : %s\n" nm (addr_pfgaddrstr (hashval_term_addr pid)))
                    conjh;
		  let countbounties = ref 0 in
		  let totalbounties = ref 0L in
		  Hashtbl.iter
		    (fun _ (amt,_) ->
		      incr countbounties;
		      totalbounties := Int64.add amt !totalbounties)
		    bountyh;
		  if !countbounties > 0 then Printf.fprintf oc "%d new bounties worth a total of %s bars.\n" !countbounties (bars_of_atoms !totalbounties)
	    end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "commitdraft" "commitdraft <draftfile> <newtxfile>" "Form a transaction to publish a commitment for a draft file."
    (fun oc al ->
      match al with
      | [f;g] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  let mkcommittx blkh lr beta =
	    try
	      let (aid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
	      if Int64.add bday commitment_maturation_minus_one <= blkh then (** this means 12 confirmations **)
		Printf.fprintf oc "A commitment marker for this draft has already been published and matured.\nThe draft can be published with the publishdraft command.\n"
	      else
		Printf.fprintf oc "A commitment marker for this draft has already been published and will mature after %Ld more blocks.\nAfter that the draft can be published with the publishdraft command.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh )
	    with Not_found ->
	      try
		let minfee = Int64.mul 1000L !Config.defaulttxfee in (** very rough overestimate of 1K bytes for commitment tx **)
		let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh minfee in
		let txinl = [(alpha,aid)] in
		let txoutl =
		  if v >= Int64.add 10000L minfee then (** only create change if it is at least 10000 atoms ***)
		    [(alpha,(None,Currency(Int64.sub v minfee)));(beta,(None,Marker))]
		  else
		    [(beta,(None,Marker))]
		in
		let stau = ((txinl,txoutl),([],[])) in
		let c2 = open_out_bin g in
		begin
		  try
		    Commands.signtxc oc lr stau c2 [] [] None;
		    close_out_noerr c2;
		    Printf.fprintf oc "The commitment transaction (to publish the marker) was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
		  with e ->
		    close_out_noerr c2;
		    raise e
		end
	      with Not_found ->
		Printf.fprintf oc "Cannot find a spendable utxo to use to publish the marker.\n"
	  in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,_,_,_) = input_theoryspec ch in
            let counter = ref 0 in
	    begin
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      match get_bestblock_print_warnings oc with
		      | None -> Printf.fprintf oc "No blocks yet\n"
		      | Some(h,lbk,ltx) ->
			  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
			  let (_,_,lr,tr,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			  try
			    let tht = lookup_thytree tr in
			    let _ = ottree_lookup tht (Some(thyh)) in
			    Printf.fprintf oc "Theory %s has already been published.\n" (hashval_hexstring thyh)
			  with Not_found ->
			    match nonce with
			    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			    | Some(nonce) ->
				match gamma with
				| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
				| Some(gamma) ->
				    if payaddr_p gamma then
				      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce thyh)) in
				      mkcommittx blkh lr beta
				    else
				      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then
		    Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n"
		  else
		    match nonce with
		    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		    | Some(nonce) ->
			match gamma with
			| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			| Some(gamma) ->
			    if payaddr_p gamma then
			      let signaspech = hashsigna (signaspec_signa signaspec) in
			      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th signaspech))) in
			      mkcommittx blkh lr beta
			    else
			      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,_,_,_,_,_,_,_,_,_,_) = input_doc ch th sgt in
	    let doch = hashdoc dl in
	    let alphadoc = hashval_pub_addr (hashopair2 th doch) in
	    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphadoc) in
	    match hlist_lookup_asset_gen true true true (fun a -> match a with (_,_,_,DocPublication(_,_,_,_)) -> true | _ -> false) hl with
	    | Some(aid,_,_,_) ->
		Printf.fprintf oc "Document has already been published: address %s asset id %s\n" (Cryptocurr.addr_pfgaddrstr alphadoc) (hashval_hexstring aid)
	    | None ->
		begin
		  let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
		  let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
		  let refusecommit = ref false in
		  let gvtp th1 h1 a =
		    if th1 = th then
		      let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		      let alpha = hashval_term_addr oid in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		      match hlist_lookup_obj_owner true true true oid hl with
		      | None -> false
		      | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		    else
		      false
		  in
		  let gvkn th1 k =
		    if th1 = th then
		      let pid = hashtag (hashopair2 th k) 33l in
		      let alpha = hashval_term_addr pid in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		      match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		      | None -> false
		      | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		    else
		      false
		  in
                  let counter = ref 0 in
		  match Checking.check_doc counter gvtp gvkn th thy sgt dl with
		  | None -> raise (Failure "Document does not check.\n")
		  | Some(_) ->
		      let id = hashopair2 th (hashdoc dl) in
		      Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		      let usesobjs = doc_uses_objs dl in
		      let usesprops = doc_uses_props dl in
		      Printf.fprintf oc "Document uses %d objects:\n" (List.length usesobjs);
		      List.iter
			(fun (oidpure,k) ->
			  let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
			  let alphapure = hashval_term_addr oidpure in
			  let alphathy = hashval_term_addr oidthy in
			  try
			    let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			    Printf.fprintf oc "  Theory Object %s (%s) Owner %s: %s\n" (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> refusecommit := true; "No right to use; document cannot be published unless this is redefined.\n"
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			    match hlist_lookup_obj_owner true true true oidpure hl with
			    | None ->
				Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
				  (hashval_hexstring oidpure)
				  (addr_pfgaddrstr alphapure)
			    | Some(beta,r) ->
				Printf.fprintf oc "  Pure Object %s (%s) Owner %s: %s\n" (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
				  (addr_pfgaddrstr (payaddr_addr beta))
				  (match r with
				  | None -> refusecommit := true; "No right to use; document cannot be published unless this is redefined.\n"
				  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			  with Not_found ->
			    refusecommit := true;
			    Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			      (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
			usesobjs;
		      Printf.fprintf oc "Document uses %d props:\n" (List.length usesprops);
		      List.iter
			(fun pidpure ->
			  let pidthy = hashtag (hashopair2 th pidpure) 33l in
			  let alphapure = hashval_term_addr pidpure in
			  let alphathy = hashval_term_addr pidthy in
			  try
			    let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			    Printf.fprintf oc "  Theory Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> refusecommit := true; "No right to use; document cannot be published unless this is reproven."
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			    match hlist_lookup_prop_owner true true true pidpure hl with
			    | None ->
				Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
				  (hashval_hexstring pidpure)
				  (addr_pfgaddrstr alphapure)
			    | Some(beta,r) ->
				Printf.fprintf oc "  Pure Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
				  (addr_pfgaddrstr (payaddr_addr beta))
				  (match r with
				  | None -> refusecommit := true; "No right to use; document cannot be published unless this is reproven."
				  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			  with Not_found ->
			    refusecommit := true;
			    Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			      (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
			usesprops;
		      if !refusecommit then
			Printf.fprintf oc "Refusing to commit to the draft until the issues above are resolved.\n"
		      else
			match nonce with
			| None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			| Some(nonce) ->
			    match gamma with
			    | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			    | Some(gamma) ->
				if payaddr_p gamma then
				  let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th doch))) in
				  mkcommittx blkh lr beta
				else
				  raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
		end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "publishdraft" "publishdraft <draftfile> <newtxfile>" "Form a transaction to publish a committed draft file."
    (fun oc al ->
      match al with
      | [f;g] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,_,propownsh,proprightsh) = input_theoryspec ch in
	    begin
              let counter = ref 0 in
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      match get_bestblock_print_warnings oc with
		      | None -> Printf.fprintf oc "No blocks yet\n"
		      | Some(h,lbk,ltx) ->
			  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
			  let (_,_,lr,tr,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			  try
			    let tht = lookup_thytree tr in
			    let _ = ottree_lookup tht (Some(thyh)) in
			    Printf.fprintf oc "Theory %s has already been published.\n" (hashval_hexstring thyh)
			  with Not_found ->
			    match nonce with
			    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			    | Some(h) ->
				match gamma with
				| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
				| Some(gamma) ->
				    if payaddr_p gamma then
				      let gammap = let (i,xs) = gamma in (i = 1,xs) in
				      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair h thyh)) in
				      begin
					try
					  let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
					  try
					    if Int64.add bday commitment_maturation_minus_one <= blkh then
					      begin
						let b = theoryspec_burncost thyspec in
						try
						  let delta = hashval_pub_addr thyh in
						  let txoutl = [(delta,(None,TheoryPublication(gammap,h,thyspec)))] in
						  let txoutlr = ref txoutl in
						  let (_,kl) = thy in
						  List.iter
						    (fun h ->
                                                      let pidpure = h in
				                      let pidthy = hashtag (hashopair2 (Some(thyh)) pidpure) 33l in
				                      let alphapure = hashval_term_addr pidpure in
				                      let alphathy = hashval_term_addr pidthy in
						      let gamma1p =
							try
							  Hashtbl.find propownsh h
							with Not_found -> gammap
						      in
						      let (gamma2pp,rpp) =
							try
							  Hashtbl.find proprightsh (false,h)
							with Not_found -> (gamma1p,Some(0L))
						      in
						      let (gamma2tp,rtp) =
							try
							  Hashtbl.find proprightsh (true,h)
							with Not_found -> (gamma1p,Some(0L))
						      in
                                                      begin
				                        let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
				                        match hlist_lookup_prop_owner true true true pidpure hl with
                                                        | Some(_,_) -> () (** pure version already owned **)
				                        | None -> (** pure version not owned yet **)
						           txoutlr := (alphapure,(Some(gamma1p,0L,false),OwnsProp(pidpure,gamma2pp,rpp)))::!txoutlr
                                                      end;
                                                      (** the theory version cannot be previously owned unless the exact theory was already published, in which case the theory should not be republished **)
                                                      txoutlr := (alphathy,(Some(gamma1p,0L,false),OwnsProp(pidthy,gamma2tp,rtp)))::!txoutlr)
						    kl;
						  let esttxbytes = 2000 + stxsize (([],!txoutlr),([],[])) in (** rough overestimate for txin and signatures at 2000 bytes **)
						  let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
						  let minamt = Int64.add b minfee in
						  let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh minamt in
						  let change = Int64.sub v minamt in
						  if change >= 10000L then txoutlr := (alpha,(None,Currency(change)))::!txoutlr;
						  let txinl = [(alpha,aid);(beta,markerid)] in
						  let stau = ((txinl,!txoutlr),([],[])) in
						  let c2 = open_out_bin g in
						  begin
						    try
						      Commands.signtxc oc lr stau c2 [] [] None;
						      let p = pos_out c2 in
						      close_out_noerr c2;
						      if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
						      Printf.fprintf oc "The transaction to publish the theory was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
						    with e ->
						      close_out_noerr c2;
						      raise e
						  end
						with Not_found ->
						  Printf.fprintf oc "Cannot find a spendable utxo to use to publish the marker.\n"
					      end
					    else
					      Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
					  with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
					with Not_found ->
					  Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
				      end
				    else
				      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  let delta = hashval_pub_addr id in
		  let hldelta = ctree_lookup_addr_assets true true (CHash(lr)) (0,delta) in
		  if not (hldelta = HNil) then raise (Failure "Signature already seems to have been published.");
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then
		    Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n"
		  else
		    match nonce with
		    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		    | Some(nonce) ->
			match gamma with
			| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			| Some(gamma) ->
			    if payaddr_p gamma then
			      let gammap = let (i,xs) = gamma in (i = 1,xs) in
			      let signaspech = hashsigna (signaspec_signa signaspec) in
			      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th signaspech))) in
			      begin
				try
				  let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
				  try
				    if Int64.add bday commitment_maturation_minus_one <= blkh then
				      begin
					let b = signaspec_burncost signaspec in
					let txinlr = ref [(beta,markerid)] in
					let txoutlr = ref [(delta,(None,SignaPublication(gammap,nonce,th,signaspec)))] in
					let esttxbytes = 2000 + stxsize (([],!txoutlr),([],[])) in (** rough overestimate for txin, possible change and signatures at 2000 bytes **)
					let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
					let tospend = ref (Int64.add b minfee) in
					try
					  let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
					  let tauin = (alpha,aid)::!txinlr in
					  let tauout = if Int64.sub v !tospend >= 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
					  let stau = ((tauin,tauout),([],[])) in
					  let c2 = open_out_bin g in
					  begin
					    try
					      Commands.signtxc oc lr stau c2 [] [] None;
					      let p = pos_out c2 in
					      close_out_noerr c2;
					      if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
					      Printf.fprintf oc "The transaction to publish the signature was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
					    with e ->
					      close_out_noerr c2;
					      raise e
					  end
					with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
				      end
				    else
				      Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
				  with Not_found -> Printf.fprintf oc "Not_found was raised while trying to construct the publication tx.\n"
				with Not_found ->
				  Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
			      end
			    else
			      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
            let addrh : (payaddr,int64) Hashtbl.t = Hashtbl.create 10 in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,paramh,objhrev,proph,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh) = input_doc ch th sgt in
	    let id = hashopair2 th (hashdoc dl) in
	    let delta = hashval_pub_addr id in
	    let hldelta = ctree_lookup_addr_assets true true (CHash(lr)) (0,delta) in
	    if not (hldelta = HNil) then raise (Failure "Document already seems to have been published.");
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_doc counter gvtp gvkn th thy sgt dl with
	      | None -> raise (Failure "Document does not check.\n")
	      | Some(_) ->
		  Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr delta);
		  match nonce with
		  | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		  | Some(nonce) ->
		      match gamma with
		      | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
		      | Some(gamma) ->
			  if payaddr_p gamma then
			    let gammap = let (i,xs) = gamma in (i = 1,xs) in
			    let doch = hashdoc dl in
			    let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th doch))) in
			    begin
			      try
				let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
				try
				  if Int64.add bday commitment_maturation_minus_one <= blkh then
				    begin
				      let tospend = ref 0L in
				      let al = ref [(markerid,bday,obl,Marker)] in
				      let txinlr = ref [(beta,markerid)] in
				      let txoutlr = ref [(delta,(None,DocPublication(gammap,nonce,th,dl)))] in
                                      let revisituses = ref [] in
				      let usesobjs = doc_uses_objs dl in
				      let usesprops = doc_uses_props dl in
				      let createsobjs = doc_creates_objs dl in
				      let createsprops = doc_creates_props dl in
				      let createsnegpropsaddrs2 = List.map (fun h -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) (doc_creates_neg_props dl) in
				      let objrightsassets : (hashval,addr * asset) Hashtbl.t = Hashtbl.create 10 in
				      let proprightsassets : (hashval,addr * asset) Hashtbl.t = Hashtbl.create 10 in
				      List.iter
					(fun (alpha,a,v) ->
					  match a with
					  | (_,_,_,RightsObj(h,_)) -> Hashtbl.add objrightsassets h (alpha,a)
					  | (_,_,_,RightsProp(h,_)) -> Hashtbl.add proprightsassets h (alpha,a)
					  | _ -> ())
					(Commands.get_spendable_assets_in_ledger oc lr blkh);
				      let oname h =
					try
					  Hashtbl.find objhrev h
					with Not_found -> ""
				      in
				      let pname h =
					try
					  Hashtbl.find prophrev h
					with Not_found -> ""
				      in
				      List.iter
					(fun (oidpure,k) ->
					  let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
					  let alphapure = hashval_term_addr oidpure in
					  let alphathy = hashval_term_addr oidthy in
					  let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
					  begin
					    match r with
					    | None -> raise (Failure (Printf.sprintf "No right to use theory object '%s' %s. It must be redefined." (oname oidpure) (hashval_hexstring oidthy)))
					    | Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
					       begin
                                                 revisituses := (false,oidthy,beta,i)::!revisituses;
                                                 if Hashtbl.mem objrightsassets oidthy then
                                                   begin
                                                     try
                                                       let i2 = Hashtbl.find addrh beta in
                                                       if i > i2 then Hashtbl.replace addrh beta i
                                                     with Not_found ->
                                                       Hashtbl.add addrh beta i
                                                   end
                                               end
					    | _ -> ()
					  end;
					  begin
					    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
					    match hlist_lookup_obj_owner true true true oidpure hl with
					    | None -> raise (Failure (Printf.sprintf "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **" (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)))
					    | Some(beta,r) ->
						match r with
						| None -> raise (Failure (Printf.sprintf "No right to use pure object '%s' %s. It must be redefined." (oname oidpure) (hashval_hexstring oidpure)))
						| Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
					           begin
                                                     revisituses := (false,oidpure,beta,i)::!revisituses;
                                                     if Hashtbl.mem objrightsassets oidpure then
                                                       begin
                                                         try
                                                           let i2 = Hashtbl.find addrh beta in
                                                           if i > i2 then Hashtbl.replace addrh beta i
                                                         with Not_found ->
                                                           Hashtbl.add addrh beta i
                                                       end
                                                   end
						| _ -> ()
					  end)
					usesobjs;
				      List.iter
					(fun pidpure ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphapure = hashval_term_addr pidpure in
					  let alphathy = hashval_term_addr pidthy in
					  let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
					  begin
					    match r with
					    | None -> raise (Failure (Printf.sprintf "No right to use theory proposition '%s' %s. It must be reproven." (pname pidpure) (hashval_hexstring pidthy)))
					    | Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
						begin
                                                  revisituses := (true,pidthy,beta,i)::!revisituses;
                                                  if Hashtbl.mem proprightsassets pidthy then
                                                    begin
						      try
                                                        let i2 = Hashtbl.find addrh beta in
                                                        if i > i2 then Hashtbl.replace addrh beta i
                                                      with Not_found ->
                                                        Hashtbl.add addrh beta i
                                                    end
						end
					    | _ -> ()
					  end;
					  begin
					    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
					    match hlist_lookup_prop_owner true true true pidpure hl with
					    | None -> raise (Failure (Printf.sprintf "** Somehow the theory proposition has an owner but the pure object %s (%s) did not. Invariant failure. **" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)))
					    | Some(beta,r) ->
						match r with
						| None -> raise (Failure (Printf.sprintf "No right to use pure proposition '%s' %s. It must be reproven." (pname pidpure) (hashval_hexstring pidpure)))
						| Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
						   begin
                                                     revisituses := (true,pidpure,beta,i)::!revisituses;
                                                     if Hashtbl.mem proprightsassets pidpure then
                                                       begin
						         try
                                                           let i2 = Hashtbl.find addrh beta in
                                                           if i > i2 then Hashtbl.replace addrh beta i
                                                         with Not_found ->
                                                           Hashtbl.add addrh beta i
                                                       end
						   end
						| _ -> ()
					  end)
					usesprops;
                                      Hashtbl.iter
                                        (fun beta m ->
                                          tospend := Int64.add !tospend m;
                                          txoutlr := (payaddr_addr beta,(None,Currency(m)))::!txoutlr)
                                        addrh;
                                      List.iter
                                        (fun (b1,h1,beta1,i1) ->
                                          try
                                            let i2 = Hashtbl.find addrh beta1 in
                                            if i2 < i1 then raise Not_found;
                                          with Not_found ->
                                            try
                                              let (alpha,a) = Hashtbl.find (if b1 then proprightsassets else objrightsassets) h1 in
					      match a with
					      | (aid,bday,obl,RightsObj(h,r)) when not b1 ->
						 if r > 0L then
						   begin
						     al := a::!al;
						     txinlr := (alpha,aid)::!txinlr;
                                                     if r > 1L then txoutlr := (alpha,(obl,RightsObj(h,Int64.sub r 1L)))::!txoutlr;
                                                   end
                                                 else
                                                   raise Not_found
					      | (aid,bday,obl,RightsProp(h,r)) when b1 ->
						 if r > 0L then
						   begin
						     al := a::!al;
						     txinlr := (alpha,aid)::!txinlr;
                                                     if r > 1L then txoutlr := (alpha,(obl,RightsProp(h,Int64.sub r 1L)))::!txoutlr;
                                                   end
                                                 else
                                                   raise Not_found
                                              | _ ->
                                                 raise Not_found
                                            with Not_found ->
                                              raise (Failure (Printf.sprintf "Problem obtaining rights for %s" (hashval_hexstring h1))))
                                        !revisituses;
				      List.iter
					(fun (h,k) ->
					  let oidpure = h in
					  let oidthy = hashtag (hashopair2 th (hashpair h k)) 32l in
					  let alphapure = hashval_term_addr oidpure in
					  let alphathy = hashval_term_addr oidthy in
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
					  begin
					    match hlist_lookup_obj_owner true true true oidpure hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find objownsh oidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find objrightsh (false,oidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphapure,(Some(delta1,0L,false),OwnsObj(oidpure,delta2,r)))::!txoutlr
					  end;
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
					  begin
					    match hlist_lookup_obj_owner true true true oidthy hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find objownsh oidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find objrightsh (true,oidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphathy,(Some(delta1,0L,false),OwnsObj(oidthy,delta2,r)))::!txoutlr
					  end)
					createsobjs;
				      List.iter
					(fun pidpure ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphapure = hashval_term_addr pidpure in
					  let alphathy = hashval_term_addr pidthy in
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphapure) in
					  begin
					    match hlist_lookup_prop_owner true true true pidpure hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find propownsh pidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find proprightsh (false,pidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphapure,(Some(delta1,0L,false),OwnsProp(pidpure,delta2,r)))::!txoutlr
					  end;
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alphathy) in
					  begin
					    match hlist_lookup_prop_owner true true true pidthy hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find propownsh pidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find proprightsh (true,pidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphathy,(Some(delta1,0L,false),OwnsProp(pidthy,delta2,r)))::!txoutlr
					  end)
					createsprops;
				      List.iter
					(fun alpha -> txoutlr := (alpha,(Some(gammap,0L,false),OwnsNegProp))::!txoutlr)
					createsnegpropsaddrs2;
				      Hashtbl.iter
					(fun pidpure (amt,olkh) ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphathy = hashval_term_addr pidthy in
					  tospend := Int64.add amt !tospend;
					  match olkh with
					  | None -> txoutlr := (alphathy,(None,Bounty(amt)))::!txoutlr
					  | Some(deltap,lkh) -> txoutlr := (alphathy,(Some(deltap,lkh,false),Bounty(amt)))::!txoutlr)
					bountyh;
				      try
					let esttxbytes = 2000 + stxsize ((!txinlr,!txoutlr),([],[])) + 200 * estimate_required_signatures !al (!txinlr,!txoutlr) in (** rough overestimate for funding asset, possible change and signature for the funding asset 2000 bytes; overestimate of 200 bytes per other signature **)
					let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
					tospend := Int64.add !tospend minfee;
					let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
					let tauin = (alpha,aid)::!txinlr in
					let tauout = if Int64.sub v !tospend > 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
					let stau = ((tauin,tauout),([],[])) in
					let c2 = open_out_bin g in
					begin
					  try
					    Commands.signtxc oc lr stau c2 [] [] None;
					    let p = pos_out c2 in
					    close_out_noerr c2;
					    if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
					    Printf.fprintf oc "The transaction to publish the document was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
					  with e ->
					    close_out_noerr c2;
					    raise e
					end
				      with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
				    end
				  else
				    Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
				with Not_found -> Printf.fprintf oc "Not_found was raised while trying to create the publication tx.\n"
			      with Not_found ->
				Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
			    end
			  else
			    raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "createbuyrightstx" "createbuyrightstx <payaddr> <num of rights> <id> ... <id>" "Create tx to buy rights for objects and/or propositions to be held at the given pay address."
    (fun oc al ->
      match al with
      | (beta::n::idl0) ->
         begin
           let beta = pfgaddrstr_addr beta in
           if not (payaddr_p beta) then raise BadCommandForm;
           let addrh : (payaddr,int64) Hashtbl.t = Hashtbl.create 10 in
           let n = Int64.of_string n in
           let idaddrl =
             List.map
               (fun h ->
                 let id1 = hexstring_hashval h in
                 let alpha1 = hashval_term_addr id1 in
                 (id1,alpha1))
               idl0
           in
           match get_bestblock_print_warnings oc with
           | None -> Printf.fprintf oc "No blocks yet\n"
           | Some(h,lbk,ltx) ->
	      let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	      let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
              List.iter
                (fun (id1,alpha1) ->
                  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha1) in
                  let al2 =
                    hlist_filter_assets_gen true true
                      (fun a ->
                        match a with
                        | (_,_,_,OwnsObj(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | (_,_,_,OwnsProp(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | _ -> false)
                      hl
                  in
                  List.iter
                    (fun a ->
                      match a with
                      | (_,_,_,OwnsObj(id2,gamma,Some(r))) ->
                         let rn = Int64.mul r n in
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             if rn > m then Hashtbl.replace addrh gamma rn
                           with Not_found ->
                             Hashtbl.add addrh gamma rn
                         end
                      | (_,_,_,OwnsProp(id2,gamma,Some(r))) ->
                         let rn = Int64.mul r n in
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             if rn > m then Hashtbl.replace addrh gamma rn
                           with Not_found ->
                             Hashtbl.add addrh gamma rn
                         end
                      | _ -> ())
                    al2)
                idaddrl;
              let tospend = ref 0L in
              let txoutlr = ref [] in
              Hashtbl.iter
                (fun gamma m ->
                  tospend := Int64.add !tospend m;
                  txoutlr := (payaddr_addr gamma,(None,Currency(m)))::!txoutlr)
                addrh;
              List.iter
                (fun (id1,alpha1) ->
                  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha1) in
                  let al2 =
                    hlist_filter_assets_gen true true
                      (fun a ->
                        match a with
                        | (_,_,_,OwnsObj(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | (_,_,_,OwnsProp(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | _ -> false)
                      hl
                  in
                  List.iter
                    (fun a ->
                      match a with
                      | (_,_,_,OwnsObj(id2,gamma,Some(r))) ->
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             let n2 = Int64.div m r in
                             txoutlr := (beta,(None,RightsObj(id2,n2)))::!txoutlr
                           with Not_found -> ()
                         end
                      | (_,_,_,OwnsProp(id2,gamma,Some(r))) ->
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             let n2 = Int64.div m r in
                             txoutlr := (beta,(None,RightsProp(id2,n2)))::!txoutlr
                           with Not_found -> ()
                         end
                      | _ -> ())
                    al2)
                idaddrl;
              let esttxbytes = 2000 + 200 * List.length !txoutlr in
              let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
              tospend := Int64.add !tospend minfee;
	      let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
	      let tauin = [(alpha,aid)] in
	      let tauout = if Int64.sub v !tospend > 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
              let stau = ((tauin,tauout),([],[])) in
	      let s = Buffer.create 100 in
	      seosbf (seo_stx seosb stau (s,None));
              let hs = Hashaux.string_hexstring (Buffer.contents s) in
	      Printf.fprintf oc "%s\n" hs
         end
      | _ -> raise BadCommandForm);
  ac "missing" "missing" "Report current list of missing headers/deltas"
    (fun oc al ->
      Printf.fprintf oc "%d missing headers\n" (List.length !missingheaders);
      List.iter
	(fun (i,h) -> Printf.fprintf oc "%Ld %s\n" i (hashval_hexstring h))
	!missingheaders;
      Printf.fprintf oc "%d missing deltas\n" (List.length !missingdeltas);
      List.iter
	(fun (i,h) -> Printf.fprintf oc "%Ld %s\n" i (hashval_hexstring h))
	!missingdeltas;
      );
  ac "reportowned" "reportowned [<outputfile> [<ledgerroot>]]" "Give a report of all owned objects and propositions in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportowned oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportowned oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportowned oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "reportbounties" "reportbounties [<outputfile> [<ledgerroot>]]" "Give a report of all bounties in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportbounties oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportbounties oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportbounties oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "collectbounties" "collectbounties <outputaddress> <txfileout> [<ledgerroot>]" "Create a tx (stored in a file) paying all collectable bounties (if there are any) to the output address."
    (fun oc al ->
      let collb gammas fn lr =
	  let gamma = Cryptocurr.pfgaddrstr_addr gammas in
	  if not (payaddr_p gamma) then raise (Failure (Printf.sprintf "Address %s is not a pay address." gammas));
	  let cbl = Commands.collectable_bounties oc lr in
	  if cbl = [] then
	    Printf.fprintf oc "No bounties can be collected.\n"
	  else
	    let txinl = ref [] in
	    let txoutl = ref [] in
	    let vtot = ref 0L in
            let cnt = ref 0 in
	    List.iter
	      (fun (alpha,a1,a2) ->
		match (a1,a2) with
		| ((aid1,_,_,Bounty(v)),(aid2,_,obl2,pre2)) ->
		    vtot := Int64.add !vtot v;
		    txinl := (alpha,aid1)::!txinl;
		    if (!cnt < 50) && not (List.exists (fun (_,aid2b) -> aid2b = aid2) !txinl) then
		      begin
			txinl := (alpha,aid2)::!txinl;
			txoutl := (alpha,(obl2,pre2))::!txoutl;
                        incr cnt
		      end
		| _ -> ())
	      cbl;
	    let esttxbytes = 2000 + stxsize ((!txinl,!txoutl),([],[])) in
	    let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
	    if !vtot < minfee then
	      Printf.fprintf oc "Total bounties are less than the tx fee, so refusing to make the tx.\n"
	    else
	      begin
		let totminusfee = Int64.sub !vtot minfee in
		txoutl := (gamma,(None,Currency(totminusfee)))::!txoutl;
		let stau = ((!txinl,!txoutl),([],[])) in
		let c2 = open_out_bin fn in
		begin
		  try
		    Commands.signtxc oc lr stau c2 [] [] None;
		    close_out_noerr c2;
		    Printf.fprintf oc "Transaction created to claim %s bars from bounties.\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" (Cryptocurr.bars_of_atoms totminusfee) fn fn
		  with e ->
		    close_out_noerr c2;
		    raise e
		end
	      end
      in
      match al with
      | [gammas;fn] -> let lr = get_ledgerroot (get_bestblock_print_warnings oc) in collb gammas fn lr
      | [gammas;fn;lr] -> collb gammas fn (hexstring_hashval lr)
      | _ -> raise BadCommandForm);
  ac "reportpubs" "reportpubs [<outputfile> [<ledgerroot>]]" "Give a report of all publications in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportpubs oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportpubs oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportpubs oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "setbestblock" "setbestblock <blockid> [<blockheight> <ltcblockid> <ltcburntx>]" "Manually set the current best block. This is mostly useful if -ltcoffline is being used."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      let bh = DbBlockHeader.dbget h in
	      let (bhd,_) = bh in
	      begin
		try
		  let (lbk,ltx) = get_burn h in
		  artificialbestblock := Some(h,lbk,ltx);
		  artificialledgerroot := Some(bhd.newledgerroot)
		with Not_found ->
		  Printf.fprintf oc "Cannot find burn for block.\n"
	      end
	    with Not_found ->
	      Printf.fprintf oc "Unknown block.\n"
	  end
      | [a;lblk;ltx] ->
	  begin
	    let h = hexstring_hashval a in
	    let lblk = hexstring_hashval lblk in
	    let ltx = hexstring_hashval ltx in
	    artificialbestblock := Some(h,lblk,ltx);
	  end
      | [a;_;lblk;ltx] -> (*** ignore blkh (second argument), but leave this format for backwards compatibility ***)
	  begin
	    let h = hexstring_hashval a in
	    let lblk = hexstring_hashval lblk in
	    let ltx = hexstring_hashval ltx in
	    artificialbestblock := Some(h,lblk,ltx);
	  end
      | _ ->
	  raise BadCommandForm);
  ac "setledgerroot" "setledgerroot <ledgerroot or blockhash>" "Manually set the current ledger root, either by giving the ledger root (Merkle root of a ctree)\nor by giving the hash of a block containing the new ledger root."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      let (bhd,_) = DbBlockHeader.dbget h in
	      artificialledgerroot := Some(bhd.newledgerroot)
	    with Not_found ->
	      artificialledgerroot := Some(h)
	  end
      | _ -> raise BadCommandForm);
  ac "verifyfullledger" "verifyfullledger [<ledgerroot>]" "Ensure the node has the full ledger with the given ledger root."
    (fun oc al ->
      match al with
      | [a] ->
	 begin
	   let h = hexstring_hashval a in
           try
             Commands.verifyfullledger oc h
           with
           | MissingAsset(k,_) -> Printf.printf "Missing asset %s\n" (hashval_hexstring k)
           | CorruptedAsset(k,_) -> Printf.printf "Corrupted asset %s\n" (hashval_hexstring k)
           | MissingHConsElt(k,_) -> Printf.printf "Missing hcons element %s\n" (hashval_hexstring k)
           | CorruptedHConsElt(k,_) -> Printf.printf "Corrupted hcons element %s\n" (hashval_hexstring k)
           | MissingCTreeAtm(k) -> Printf.printf "Missing ctree atom %s\n" (hashval_hexstring k)
           | CorruptedCTreeAtm(k) -> Printf.printf "Corrupted ctree atom %s\n" (hashval_hexstring k)
	  end
      | [] ->
	 begin
	   try
	     let ledgerroot = get_ledgerroot (get_bestblock_print_warnings oc) in
	     Commands.verifyfullledger oc ledgerroot
	   with
           | MissingAsset(k,_) -> Printf.printf "Missing asset %s\n" (hashval_hexstring k)
           | CorruptedAsset(k,_) -> Printf.printf "Corrupted asset %s\n" (hashval_hexstring k)
           | MissingHConsElt(k,_) -> Printf.printf "Missing hcons element %s\n" (hashval_hexstring k)
           | CorruptedHConsElt(k,_) -> Printf.printf "Corrupted hcons element %s\n" (hashval_hexstring k)
           | MissingCTreeAtm(k) -> Printf.printf "Missing ctree atom %s\n" (hashval_hexstring k)
           | CorruptedCTreeAtm(k) -> Printf.printf "Corrupted ctree atom %s\n" (hashval_hexstring k)
	 end
      | _ -> raise BadCommandForm);
  ac "requestblock" "requestblock <blockhash>" "Manually request a missing block from peers, if possible.\nThis is mostly useful if -ltcoffline is set.\nUnder normal operations proofgold will request the block when its hash is seen in the ltc burn tx."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      if DbInvalidatedBlocks.dbexists h then DbInvalidatedBlocks.dbdelete h;
	      if DbBlacklist.dbexists h then DbBlacklist.dbdelete h;
	      if DbBlockHeader.dbexists h then
		Printf.fprintf oc "Already have header.\n"
	      else
		begin
		  find_and_send_requestdata GetHeader h;
		  Printf.fprintf oc "Block header requested.\n"
		end;
	      try
		if DbBlockDelta.dbexists h then
		  Printf.fprintf oc "Already have delta.\n"
		else
		  begin
		    find_and_send_requestdata GetBlockdelta h;
		    Printf.fprintf oc "Block delta requested.\n"
		  end
	      with Not_found ->
		Printf.fprintf oc "No peer has delta %s.\n" a
	    with Not_found ->
	      Printf.fprintf oc "No peer has header %s.\n" a
	  end
      | _ -> raise BadCommandForm);
  ac "originalrewardbountyprop" "originalrewardbountyprop <ltcblockid> <ltcburntxid> [format]" "Convert an ltc block id and ltc tx id (where the tx should be a burn tx confirmed in the block),\ncreate the corresponding proposition where a reward bounty would be placed.\nIf the format argument is given, then it can have the following values:\nassembly : give the conjecture in the assembly format proofgold can parse\nfof : try to give the conjecture as a first-order problem in the TPTP fof format\nthf : give the conjecture as a higher-order problem in the TPTP thf format\nThis alternativeversion of rewardbountyprop uses the original (buggy) algorithm\nbefore the emergency hard fork of August 30 2020.\n"
    (fun oc al ->
      let (lbk,ltx,formatval) =
        match al with
        | [lbk;ltx] -> (lbk,ltx,0)
        | [lbk;ltx;f] when f = "assembly" -> (lbk,ltx,1)
        | [lbk;ltx;f] when f = "fof" -> (lbk,ltx,2)
        | [lbk;ltx;f] when f = "thf" -> (lbk,ltx,3)
        | [lbk;ltx;f] when f = "mg" -> (lbk,ltx,256)
        | _ -> raise BadCommandForm
      in
      begin
	let lbk = hexstring_hashval lbk in
	let ltx = hexstring_hashval ltx in
        let h = hashpair lbk ltx in
        let (pc,p,q) = Checking.reward_bounty_prop 2214L h in (** q is the normalized version of p, where the bounty really goes, but p is what we show and can put into the document since it will be normalized anyway **) (** 2214 is a fake block height just to indicate we want the reward bounty prop before the August 30 2020 emergency hard fork **)
        let cls = (try (List.nth ["Random1";"Random2";"Random3";"QBF";"HOSetConstr";"HOUnif";"CombUnif";"AbstrHF";"DiophantineMod";"AIM1";"AIM2";"Diophantine"] pc) with _ -> "Unknown") in
	Printf.fprintf oc "%s\n" cls;
        if formatval = 0 then
          Printf.fprintf oc "%s\n" (if pc = 9 || pc = 10 then Checking.aim_trm_str p [] else if pc = 6 then Checking.comb_trm_str p [] else if pc = 7 then Checking.ahf_trm_str p [] else Checking.hf_trm_str p [])
        else if formatval = 1 then
          begin
            let bh : (int,string) Hashtbl.t = Hashtbl.create 1 in
            let trmh : (hashval,string) Hashtbl.t = Hashtbl.create 1 in
            let leth : (Logic.trm,string) Hashtbl.t = Hashtbl.create 10 in
            if not (cls = "QBF") then
              begin
                Hashtbl.add bh 0 "set";
                Printf.fprintf oc "Base set\n"
              end;
            decl_let_hfprims oc bh leth p;
            Printf.fprintf oc "Conj bountyprop : %s\n" (output_trm p bh trmh leth [])
          end
        else if formatval = 2 then
          begin
            if cls = "AbstrHF" then
              Checking.ahf_fof_prob oc p
            else if cls = "AIM1" then
              Checking.aim1_fof_prob oc p
            else if cls = "AIM2" then
              Checking.aim2_fof_prob oc p
            else if cls = "QBF" then
              Checking.qbf_fof_prob oc p
            else if cls = "CombUnif" then
              Checking.comb_fof_prob oc p
            else
              Printf.fprintf oc "Currently no implementation giving a TPTP fof problem for problems of class %s.\n" cls
          end
        else if formatval = 3 then
          Checking.hf_thf_prob oc p
        else if formatval = 256 then
          Checking.hf_mg_prob oc p;
        let pureid = tm_hashroot q in
        let inthyid = hashtag (hashopair2 (Some(Checking.hfthyid)) pureid) 33l in
        Printf.fprintf oc "Pure Id: %s\nId in Theory: %s\nAddress in Theory: %s\n" (hashval_hexstring pureid) (hashval_hexstring inthyid) (addr_pfgaddrstr (hashval_term_addr inthyid))
      end);
  ac "rewardbountyprop" "rewardbountyprop <ltcblockid> <ltcburntxid> [format]" "Convert an ltc block id and ltc tx id (where the tx should be a burn tx confirmed in the block),\ncreate the corresponding proposition where a reward bounty would be placed.\nIf the format argument is given, then it can have the following values:\nassembly : give the conjecture in the assembly format proofgold can parse\nfof : try to give the conjecture as a first-order problem in the TPTP fof format\nthf : give the conjecture as a higher-order problem in the TPTP thf format\n"
    (fun oc al ->
      let (lbk,ltx,formatval) =
        match al with
        | [lbk;ltx] -> (lbk,ltx,0)
        | [lbk;ltx;f] when f = "assembly" -> (lbk,ltx,1)
        | [lbk;ltx;f] when f = "fof" -> (lbk,ltx,2)
        | [lbk;ltx;f] when f = "thf" -> (lbk,ltx,3)
        | [lbk;ltx;f] when f = "mg" -> (lbk,ltx,256)
        | _ -> raise BadCommandForm
      in
      begin
	let lbk = hexstring_hashval lbk in
	let ltx = hexstring_hashval ltx in
        let h = hashpair lbk ltx in
        let (pc,p,q) = Checking.reward_bounty_prop 2216L h in (** q is the normalized version of p, where the bounty really goes, but p is what we show and can put into the document since it will be normalized anyway **) (** 2216 is a fake block height just to indicate we want the reward bounty prop after the August 30 2020 emergency hard fork **)
        let cls = (try (List.nth ["Random1";"Random2";"Random3";"QBF";"HOSetConstr";"HOUnif";"CombUnif";"AbstrHF";"DiophantineMod";"AIM1";"AIM2";"Diophantine"] pc) with _ -> "Unknown") in
	Printf.fprintf oc "%s\n" cls;
        if formatval = 0 then
          Printf.fprintf oc "%s\n" (if pc = 9 || pc = 10 then Checking.aim_trm_str p [] else if pc = 6 then Checking.comb_trm_str p [] else if pc = 7 then Checking.ahf_trm_str p [] else Checking.hf_trm_str p [])
        else if formatval = 1 then
          begin
            let bh : (int,string) Hashtbl.t = Hashtbl.create 1 in
            let trmh : (hashval,string) Hashtbl.t = Hashtbl.create 1 in
            let leth : (Logic.trm,string) Hashtbl.t = Hashtbl.create 10 in
            if not (cls = "QBF") then
              begin
                Hashtbl.add bh 0 "set";
                Printf.fprintf oc "Base set\n"
              end;
            decl_let_hfprims oc bh leth p;
            Printf.fprintf oc "Conj bountyprop : %s\n" (output_trm p bh trmh leth [])
          end
        else if formatval = 2 then
          begin
            if cls = "AbstrHF" then
              Checking.ahf_fof_prob oc p
            else if cls = "AIM1" then
              Checking.aim1_fof_prob oc p
            else if cls = "AIM2" then
              Checking.aim2_fof_prob oc p
            else if cls = "QBF" then
              Checking.qbf_fof_prob oc p
            else if cls = "CombUnif" then
              Checking.comb_fof_prob oc p
            else
              Printf.fprintf oc "Currently no implementation giving a TPTP fof problem for problems of class %s.\n" cls
          end
        else if formatval = 3 then
          Checking.hf_thf_prob oc p
        else if formatval = 256 then
          Checking.hf_mg_prob oc p;
        let pureid = tm_hashroot q in
        let inthyid = hashtag (hashopair2 (Some(Checking.hfthyid)) pureid) 33l in
        Printf.fprintf oc "Pure Id: %s\nId in Theory: %s\nAddress in Theory: %s\n" (hashval_hexstring pureid) (hashval_hexstring inthyid) (addr_pfgaddrstr (hashval_term_addr inthyid))
      end);
  ac "recenttxs" "recenttxs [<blockid> <num>]" "Report txs included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recenttxs with it to get more."
    (fun oc al ->
      let (blkid,n) =
        match al with
        | [h;ns] -> (hexstring_hashval h,int_of_string ns)
        | [h] -> (hexstring_hashval h,10)
        | (_::_) -> raise BadCommandForm
        | [] ->
           match get_bestblock_print_warnings oc with
           | None -> raise (Failure "No blocks yet?")
           | Some(h,_,_) -> (h,10)
      in
      Commands.report_recenttxs oc blkid n);
  ac "recentdocs" "recentdocs [<blockid> <num>]" "Report txs publishing docs included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recentdocs with it to get more."
    (fun oc al ->
      let (blkid,n) =
        match al with
        | [h;ns] -> (hexstring_hashval h,int_of_string ns)
        | [h] -> (hexstring_hashval h,10)
        | (_::_) -> raise BadCommandForm
        | [] ->
           match get_bestblock_print_warnings oc with
           | None -> raise (Failure "No blocks yet?")
           | Some(h,_,_) -> (h,10)
      in
      Commands.report_recentdocs oc blkid n);
  ac "recentthms" "recentthms [<blockid> <num>]" "Report txs with docs proving at least one thm included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recentthms with it to get more."
    (fun oc al ->
      let (blkid,n) =
        match al with
        | [h;ns] -> (hexstring_hashval h,int_of_string ns)
        | [h] -> (hexstring_hashval h,10)
        | (_::_) -> raise BadCommandForm
        | [] ->
           match get_bestblock_print_warnings oc with
           | None -> raise (Failure "No blocks yet?")
           | Some(h,_,_) -> (h,10)
      in
      Commands.report_recentthms oc blkid n);
  ac "recentobjiddefined" "recentobjiddefined <objid> [<blockid> <num>]" "Report txs with docs defining the given object included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recentobjiddefinedthms with it to get more."
    (fun oc al ->
      match al with
      | [] -> raise BadCommandForm
      | (oid::ar) ->
         let oid = hexstring_hashval oid in
         let (blkid,n) =
           match ar with
           | [h;ns] -> (hexstring_hashval h,int_of_string ns)
           | [h] -> (hexstring_hashval h,10)
           | (_::_) -> raise BadCommandForm
           | [] ->
              match get_bestblock_print_warnings oc with
              | None -> raise (Failure "No blocks yet?")
              | Some(h,_,_) -> (h,10)
         in
         Commands.report_recentobjid_defined oc oid blkid n);
  ac "recentpropidproven" "recentpropidproven <propid> [<blockid> <num>]" "Report txs with docs proving the given proposition included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recentpropidproven with it to get more."
    (fun oc al ->
      match al with
      | [] -> raise BadCommandForm
      | (pid::ar) ->
         let pid = hexstring_hashval pid in
         let (blkid,n) =
           match ar with
           | [h;ns] -> (hexstring_hashval h,int_of_string ns)
           | [h] -> (hexstring_hashval h,10)
           | (_::_) -> raise BadCommandForm
           | [] ->
              match get_bestblock_print_warnings oc with
              | None -> raise (Failure "No blocks yet?")
              | Some(h,_,_) -> (h,10)
         in
         Commands.report_recentpropid_proven oc pid blkid n);
  ac "recentbountiesplaced" "recentbountiesplaced [<blockid> <num>]" "Report txs placing bounties included in blocks up to (and including)\nthe given block (defaults to current best block).\nAfter enough txs (soft bound of <num>, default 10) are reported, the block before the last block\n considered is reported so the user can call recentbountiesplaced with it to get more."
    (fun oc al ->
      let (blkid,n) =
        match al with
        | [h;ns] -> (hexstring_hashval h,int_of_string ns)
        | [h] -> (hexstring_hashval h,10)
        | (_::_) -> raise BadCommandForm
        | [] ->
           match get_bestblock_print_warnings oc with
           | None -> raise (Failure "No blocks yet?")
           | Some(h,_,_) -> (h,10)
      in
      Commands.report_recentbountiesplaced oc blkid n);
  ac "mgdoc" "mgdoc <pubaddr|blockid|txid> <mgoutfile> [<num>]" "Create an approximate Megalodon version of the nth document published at the address or in the block or tx.\n"
    (fun oc al ->
      match al with
      | [hh;fn] ->
         if String.length hh > 60 then (** hashval, not address **)
           begin
             let n = 1 in
             let cnt = ref 0 in
             let h = hexstring_hashval hh in
             try
               let bd = DbBlockDelta.dbget h in
               List.iter
                 (fun ((_,tauout),_) ->
                   List.iter
                     (fun (_,(_,u)) ->
                       match u with
                       | DocPublication(_,_,th,dl) ->
                          incr cnt;
                          if !cnt = n then
                            begin
                              let f = open_out fn in
                              mgdoc_out f th dl;
                              close_out f
                            end
                       | _ -> ())
                     tauout)
                 bd.blockdelta_stxl
             with Not_found ->
               try
                 let ((_,tauout),_) = DbSTx.dbget h in
                 List.iter
                   (fun (_,(_,u)) ->
                     match u with
                     | DocPublication(_,_,th,dl) ->
                        incr cnt;
                        if !cnt = n then
                          begin
                            let f = open_out fn in
                            mgdoc_out f th dl;
                            close_out f
                          end
                     | _ -> ())
                   tauout
               with Not_found ->
                 Printf.fprintf oc "Do not know %s\n" hh
           end
         else
           begin
             let alpha = pfgaddrstr_addr hh in
             if not (pubaddr_p alpha) then raise (Failure "not a pubaddr");
             let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
             let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,alpha) in
             match hl with
             | HCons(a,_) ->
                begin
                  match a with
                  | (_,_,_,DocPublication(_,_,th,dl)) ->
                     let f = open_out fn in
                     mgdoc_out f th dl;
                     close_out f
                  | _ ->
                     raise (Failure "something other than a document at address")
                end
             | HConsH(ah,_) ->
                begin
                  let a = DbAsset.dbget ah in
                  match a with
                  | (_,_,_,DocPublication(_,_,th,dl)) ->
                     let f = open_out fn in
                     mgdoc_out f th dl;
                     close_out f
                  | _ ->
                     raise (Failure "something other than a document at address")
                end
             | HNil -> raise (Failure "no document at address")
             | HHash(hlh,_) ->
                begin
                  let (ah,_) = DbHConsElt.dbget hlh in
                  let a = DbAsset.dbget ah in
                  match a with
                  | (_,_,_,DocPublication(_,_,th,dl)) ->
                     let f = open_out fn in
                     mgdoc_out f th dl;
                     close_out f
                  | _ ->
                     raise (Failure "something other than a document at address")
                end
           end
      | [hh;fn;n] ->
         begin
           let n = int_of_string n in
           let cnt = ref 0 in
           let h = hexstring_hashval hh in
           try
             let bd = DbBlockDelta.dbget h in
             List.iter
               (fun ((_,tauout),_) ->
                 List.iter
                   (fun (_,(_,u)) ->
                     match u with
                     | DocPublication(_,_,th,dl) ->
                        incr cnt;
                        if !cnt = n then
                          begin
                            let f = open_out fn in
                            mgdoc_out f th dl;
                            close_out f
                          end
                     | _ -> ())
                   tauout)
               bd.blockdelta_stxl
           with Not_found ->
             try
               let ((_,tauout),_) = DbSTx.dbget h in
               List.iter
                 (fun (_,(_,u)) ->
                   match u with
                   | DocPublication(_,_,th,dl) ->
                      incr cnt;
                      if !cnt = n then
                        begin
                          let f = open_out fn in
                          mgdoc_out f th dl;
                          close_out f
                        end
                   | _ -> ())
                 tauout
             with Not_found ->
               Printf.fprintf oc "Do not know %s\n" hh
         end
      | _ -> raise BadCommandForm);
  ac "querymg" "querymg <hashval or address or int[block height]> [<blockid or ledgerroot>]" "Get information (in json format) about some item.\nSpecial Notation is used to present types and terms (and proofs are omitted).\nThis is intended to support exporers.\nThe querymg command gives more detailed information if -extraindex is set to true.\n"
    (fun oc al ->
      mgnice := true;
      mgnicestp := true;
      mgnatnotation := true;
      match al with
      | [h] ->
	 begin
	   try
	     let blkh = Int64.of_string h in
	     let j = Commands.query_blockheight blkh in
	     print_jsonval oc j;
	     Printf.fprintf oc "\n"
	   with Failure(_) ->
	     let j = Commands.query h in
	     print_jsonval oc j;
	     Printf.fprintf oc "\n"
	 end
      | [h;kh] ->
	 let k = hexstring_hashval kh in
	 begin
	   try
	     let (lbk,ltx) = get_burn k in
	     let (_,lmedtm,burned,(txid1,vout1),_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	     let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	     let pbh = Some(k,Poburn(lbk,ltx,lmedtm,burned,txid1,vout1)) in
	     let j = Commands.query_at_block h pbh lr blkh in
	     print_jsonval oc j;
	     Printf.fprintf oc "\n"
	   with Not_found ->
             if DbCTreeAtm.dbexists k then
	       begin
		 let j = Commands.query_at_block h None k (-1L) in
		 print_jsonval oc j;
		 Printf.fprintf oc "\n"
	       end
	     else if DbCTreeElt.dbexists k then
	       begin
		 let j = Commands.query_at_block h None k (-1L) in
		 print_jsonval oc j;
		 Printf.fprintf oc "\n"
	       end
	     else
	       raise (Failure ("could not interpret " ^ kh ^ " as a block or ledger root"))
	 end
      | _ -> raise BadCommandForm);
  ac "query" "query <hashval or address or int[block height]> [<blockid or ledgerroot>]" "Get information (in json format) about some item.\nThis is intended to support exporers.\nThe query command gives more detailed information if -extraindex is set to true."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let blkh = Int64.of_string h in
	      let j = Commands.query_blockheight blkh in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	    with Failure(_) ->
	      let j = Commands.query h in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	  end
      | [h;kh] ->
	  let k = hexstring_hashval kh in
	  begin
	    try
	      let (lbk,ltx) = get_burn k in
	      let (_,lmedtm,burned,(txid1,vout1),_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	      let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	      let pbh = Some(k,Poburn(lbk,ltx,lmedtm,burned,txid1,vout1)) in
	      let j = Commands.query_at_block h pbh lr blkh in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	    with Not_found ->
              if DbCTreeAtm.dbexists k then
		begin
		  let j = Commands.query_at_block h None k (-1L) in
		  print_jsonval oc j;
		  Printf.fprintf oc "\n"
		end
	      else if DbCTreeElt.dbexists k then
		begin
		  let j = Commands.query_at_block h None k (-1L) in
		  print_jsonval oc j;
		  Printf.fprintf oc "\n"
		end
	      else
		raise (Failure ("could not interpret " ^ kh ^ " as a block or ledger root"))
	  end
      | _ -> raise BadCommandForm);
  ac "filterwallet" "filterwallet [<ledgerroot>]" "Remove private keys/addresses not classified as fresh if they are empty.\nA backup of the old wallet is kept in the walletbkps directory."
    (fun oc al ->
      let lr =
        match al with
        | [] -> get_ledgerroot (get_bestblock_print_warnings oc)
        | [h] -> hexstring_hashval h
        | _ -> raise BadCommandForm
      in
      Commands.filter_wallet lr);
  ac "dumpwallet" "dumpwallet <filename>" "Dump the current wallet keys, addresses, etc., to a given file."
    (fun oc al ->
      match al with
      | [fn] -> Commands.dumpwallet fn
      | _ -> raise BadCommandForm);
  ac "ltcstatusdump" "ltcstatusdump [<filename> [<ltcblockhash> [<how many ltc blocks back>]]]" "Dump the proofgold information about the current ltc status to a given file."
    (fun oc al ->
      let (fn,blkh,howfarback) =
	match al with
	| [] -> ("ltcstatusdumpfile",hexstring_hashval (Ltcrpc.ltc_getbestblockhash ()),1000)
	| [fn] -> (fn,hexstring_hashval (Ltcrpc.ltc_getbestblockhash ()),1000)
	| [fn;hh] -> (fn,hexstring_hashval hh,1000)
	| [fn;hh;b] -> (fn,hexstring_hashval hh,int_of_string b)
	| _ -> raise BadCommandForm
      in
      let cblkh = ref blkh in
      let f = open_out fn in
      begin
	try
	  for i = 1 to howfarback do
	    Printf.fprintf f "%d. ltc block %s PfgStatus\n" i (hashval_hexstring !cblkh);
	    begin
	      try
		match DbLtcPfgStatus.dbget !cblkh with
		| LtcPfgStatusPrev(h) ->
		    Printf.fprintf f "  PfgStatus unchanged since ltc block %s\n" (hashval_hexstring h)
		| LtcPfgStatusNew(l) ->
		    Printf.fprintf f "  New PfgStatus:\n";
		    let cnt = ref 0 in
		    List.iter
		      (fun (dhght,li) ->
			let i = !cnt in
			incr cnt;
			match li with
			| [] -> Printf.fprintf f "   %d. Empty tip? Should not be possible. Dalilcoin height %Ld\n" i dhght;
			| ((bh,lbh,ltx,ltm,lhght)::r) ->
			    Printf.fprintf f " %Ld (%d) - Proofgold Block: %s\n        Litecoin Block: %s\n        Litecoin Burn Tx: %s\n        Litecoin Time: %Ld\n        Litecoin Height: %Ld\n" dhght i (hashval_hexstring bh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght;
			    List.iter (fun (bh,lbh,ltx,ltm,lhght) ->
			      Printf.fprintf f "       - Proofgold Block: %s\n        Litecoin Block: %s\n        Litecoin Burn Tx: %s\n        Litecoin Time: %Ld\n        Litecoin Height: %Ld\n" (hashval_hexstring bh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght)
			      r)
		      l
	      with Not_found ->
		Printf.fprintf f "  PfgStatus not found\n"
	    end;
	    begin
	      try
		let (prevh,tm,hght,burntxhs) = DbLtcBlock.dbget !cblkh in
		Printf.fprintf f "%d. ltc block %s info\n" i (hashval_hexstring !cblkh);
		Printf.fprintf f "   Previous %s\n   Block Time %Ld\n    Height %Ld\n" (hashval_hexstring prevh) tm hght;
		cblkh := prevh;
		match burntxhs with
		| [] -> ()
		| [x] -> Printf.fprintf f "    Burn Tx: %s\n" (hashval_hexstring x)
		| _ ->
		    Printf.fprintf f "    %d Burn Txs:\n" (List.length burntxhs);
		    List.iter (fun x -> Printf.fprintf f "         %s\n" (hashval_hexstring x)) burntxhs
	      with Not_found ->
		Printf.fprintf f "  LtcBlock not found\n"
	    end
	  done
	with e -> Printf.fprintf f "Exception: %s\n" (Printexc.to_string e)
      end;
      close_out_noerr f);
  ac "ltcstatus" "ltcstatus [<ltcblockhash>]" "Print the proofgold blocks burned into the ltc blockchain from the past week.\nThe topmost is the current best block."
    (fun oc al ->
      let h =
	match al with
	| [hh] -> hexstring_hashval hh
	| [] ->
	    Printf.fprintf oc "ltcbest %s\n" (hashval_hexstring !ltc_bestblock);
	    !ltc_bestblock
	| _ -> raise BadCommandForm
      in
      let (lastchangekey,zll) = ltcpfgstatus_dbget h in
      let tm = ltc_medtime() in
      if zll = [] && tm > Int64.add !Config.genesistimestamp 604800L then
	begin
	  Printf.fprintf oc "No blocks were created in the past week. Proofgold has reached terminal status.\nThe only recovery possible for the network is a hard fork.\nSometimes this message means the node is out of sync with ltc.\n"
	end;
      let i = ref 0 in
      List.iter
	(fun (dhght,zl) ->
	  incr i;
	  Printf.fprintf oc "%d [%Ld].\n" !i dhght;
	  List.iter
	    (fun (dbh,lbh,ltx,ltm,lhght) ->
	      if DbBlacklist.dbexists dbh then
		Printf.fprintf oc "- %s (blacklisted, presumably invalid) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	      else if DbInvalidatedBlocks.dbexists dbh then
		Printf.fprintf oc "- %s (marked invalid) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	      else
                let lh = hashpair lbh ltx in
                if Db_validblockvals.dbexists lh then
		  Printf.fprintf oc "+ %s %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	        else if Db_validheadervals.dbexists lh then
		  if DbBlockDelta.dbexists dbh then
		    Printf.fprintf oc "* %s (have delta, but not fully validated) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		  else
		    Printf.fprintf oc "* %s (missing delta) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	        else
		  if DbBlockHeader.dbexists dbh then
		    if DbBlockDelta.dbexists dbh then
		      Printf.fprintf oc "* %s (have block, but neither header nor delta fully valided) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		    else
		      Printf.fprintf oc "* %s (missing delta, header not fully validated) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		  else
		    Printf.fprintf oc "* %s (missing header) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght)
	    zl)
	zll);
  ac "ltcgettxinfo" "ltcgettxinfo <txid>" "Get proofgold related information about an ltc burn tx."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let (burned,prev,nxt,lblkh,confs,_,_) = Ltcrpc.ltc_getburntransactioninfo h in
	      match lblkh,confs with
	      | Some(lh),Some(confs) ->
		  Printf.fprintf oc "burned %Ld prev %s next %s in ltc block %s, %d confirmations\n" burned (hashval_hexstring prev) (hashval_hexstring nxt) lh confs
	      | _,_ ->
		  Printf.fprintf oc "burned %Ld prev %s next %s\n" burned (hashval_hexstring prev) (hashval_hexstring nxt)
	    with Not_found -> raise (Failure("problem"))
	  end
      | _ -> raise BadCommandForm);
  ac "ltcgetbestblockhash" "ltcgetbestblockhash" "Get the current tip of the ltc blockchain."
    (fun oc al ->
      if al = [] then
	begin
	  try
	    let x = Ltcrpc.ltc_getbestblockhash () in
	    Printf.fprintf oc "best ltc block hash %s\n" x
	  with Not_found ->
	    Printf.fprintf oc "could not find best ltc block hash\n"
	end
      else
	raise BadCommandForm);
  ac "ltcgetblock" "ltcgetblock <blockid>" "Print proofgold related information about the given ltc block."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let (pbh,tm,hght,txl,_) = Ltcrpc.ltc_getblock h in
	      Printf.fprintf oc "ltc block %s time %Ld height %Ld prev %s; %d proofgold candidate txs:\n" h tm hght pbh (List.length txl);
	      List.iter (fun tx -> Printf.fprintf oc "%s\n" tx) txl
	    with Not_found ->
	      Printf.fprintf oc "could not find ltc block %s\n" h
	  end
      | _ -> raise BadCommandForm);
  ac "ltclistunspent" "ltclistunspent" "List the current relevant utxos in the local ltc wallet.\nThese utxos are used to fund ltc burn txs during the creation of proofgold blocks."
    (fun oc al ->
      if al = [] then
	begin
	  try
	    let utxol = Ltcrpc.ltc_listunspent () in
	    Printf.fprintf oc "%d ltc utxos\n" (List.length utxol);
	    List.iter
	      (fun u ->
		match u with
		| LtcP2shSegwit(txid,vout,ltcaddr,_,_,amt) ->
		    Printf.fprintf oc "%s:%d %Ld (%s [p2sh-segwit])\n" txid vout amt ltcaddr
		| LtcBech32(txid,vout,ltcaddr,_,amt) ->
		    Printf.fprintf oc "%s:%d %Ld (%s [bech32])\n" txid vout amt ltcaddr)
	      utxol
	  with Not_found ->
	    Printf.fprintf oc "could not get unspent ltc list\n"
	end
      else
	raise BadCommandForm);
  ac "ltcsigntx" "ltcsigntx <txinhex>" "Use the local ltc wallet to sign an ltc tx."
    (fun oc al ->
      match al with
      | [tx] -> Printf.fprintf oc "%s\n" (Ltcrpc.ltc_signrawtransaction tx)
      | _ -> raise BadCommandForm);
  ac "ltcsendtx" "ltcsendtx <txinhex>" "Use the local ltc wallet to send an ltc tx."
    (fun oc al ->
      match al with
      | [tx] -> Printf.fprintf oc "%s\n" (Ltcrpc.ltc_sendrawtransaction tx)
      | _ -> raise BadCommandForm);
  ac "ltccreateburn" "ltccreateburn <hash1> <hash2> <litoshis to burn>" "Manually create an ltc burn tx to support a newly staked proofgold block."
    (fun oc al ->
      match al with
      | [h1;h2;toburn] ->
	  begin
	    try
	      let txs = Ltcrpc.ltc_createburntx (hexstring_hashval h1) (hexstring_hashval h2) (Int64.of_string toburn) in
	      Printf.fprintf oc "burntx: %s\n" (Hashaux.string_hexstring txs)
	    with
	    | Ltcrpc.InsufficientLtcFunds ->
		Printf.fprintf oc "no ltc utxo has %s litoshis\n" toburn
	    | Not_found ->
		Printf.fprintf oc "trouble creating burn tx\n"
	  end
      | _ -> raise BadCommandForm);
  ac "exit" "exit" "exit or stop kills the proofgold node"
    (fun oc _ -> (*** Could call Thread.kill on netth and stkth, but Thread.kill is not always implemented. ***)
      Printf.fprintf oc "Shutting down threads. Please be patient.\n"; flush oc;
      closelog();
      !exitfn 0);
  ac "stop" "stop" "exit or stop kills the proofgold node"
    (fun oc _ -> (*** Could call Thread.kill on netth and stkth, but Thread.kill is not always implemented. ***)
      Printf.fprintf oc "Shutting down threads. Please be patient.\n"; flush oc;
      closelog();
      !exitfn 0);
  ac "dumpstate" "dumpstate <textfile>" "Dump the current proofgold state to a file for debugging."
    (fun oc al ->
      match al with
      | [fa] -> Commands.dumpstate fa
      | _ -> raise BadCommandForm);
  ac "broadcastbootstrap" "broadcastbootstrap <url>" "Use an ltc alert tx to broadcast a url from which bootstraps are available."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'B' msg in
             Printf.fprintf oc "Alert bootstrap url broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "broadcastbootstrapwarning" "broadcastbootstrapwarning <url>" "Use an ltc alert tx to broadcast a warning about a url from which bootstraps were alleged to be available."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'b' msg in
             Printf.fprintf oc "Alert bootstrap warning url broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "broadcastlistener" "broadcastlistener [<url>]" "Use an ltc alert tx to broadcast an ip or onion address for a listening node.\nIf no url is given, the value of onion or ip is used."
    (fun oc al ->
      let f msg =
        let l = String.length msg in
        if l < 70 then
          begin
            for i = 0 to l-1 do
              if Char.code msg.[i] > 127 then
                raise (Failure "Alert message must only contain ASCII characters")
            done;
            let ltctx = broadcast_alert_via_ltc 'L' msg in
            Printf.fprintf oc "Alert listener msg broadcast as ltc tx %s\n" ltctx
          end
        else
          raise (Failure "Alert message must have fewer than 70 ASCII characters")
      in
      match al with
      | [] ->
         begin
           match !Config.onion with
           | Some(onionaddr) ->
              let msg = Printf.sprintf "%s:%d" onionaddr !Config.onionremoteport in
              f msg
           | None ->
              match !Config.ip with
              | Some(ipaddr) ->
                 let msg = Printf.sprintf "%s:%d" ipaddr !Config.port in
                 f msg
              | None ->
                 raise (Failure "No listening url available")
         end
      | [url] -> f url
      | _ -> raise BadCommandForm);
  ac "broadcastalert" "broadcastalert <string>" "Use an ltc alert tx to broadcast an alert message for nodes. The message must contain fewer than 70 ASCII characters."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'A' msg in
             Printf.fprintf oc "Alert broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "addnode" "addnode <address:port> [add|remove|onetry] [strength (for onetry)]" "Add or remove a peer by giving an address or port number.\nThe address may be an ip or an onion address."
    (fun oc al ->
      let addnode_add n =
	match tryconnectpeer n with
	| None -> raise (Failure "Failed to add node")
	| Some(lth,sth,(fd,sin,sout,gcs)) ->
	   match !gcs with
	   | None -> raise (Failure "Problem adding node")
	   | Some(cs) ->
	      if cs.addrfrom = "" then
                if cs.realaddr = "" then
                  ()
                else
		  addknownpeer (Int64.of_float cs.conntime) cs.realaddr
              else
		addknownpeer (Int64.of_float cs.conntime) cs.addrfrom
      in
      match al with
      | [n] -> addnode_add n
      | [n;"add"] -> addnode_add n
      | [n;"remove"] ->
          removeknownpeer n;
          List.iter
	    (fun (lth,sth,(fd,sin,sout,gcs)) -> if peeraddr !gcs = n then (shutdown_close fd; gcs := None))
	    !netconns
      | [n;"onetry"] ->
	  ignore (tryconnectpeer n)
      | [n;"onetry";str] ->
          reqstrength := Some(int_of_string str);
	  ignore (tryconnectpeer n)
      | _ -> raise BadCommandForm);
  ac "clearbanned" "clearbanned" "Clear the list of banned peers."
    (fun _ _ -> clearbanned());
  ac "listbanned" "listbanned" "List the current banned peers."
    (fun oc _ -> Hashtbl.iter (fun n () -> Printf.fprintf oc "%s\n" n) bannedpeers);
  ac "bannode" "bannode [<address:port>] ... [<address:port>]" "ban the given peers"
    (fun _ al -> List.iter (fun n -> banpeer n) al);
  ac "missingblocks" "missingblocks" "Print info about headers and deltas the node is missing.\nTypically a delta is only listed as missing after the header has been received and validated."
    (fun oc al ->
      Printf.fprintf oc "%d missing headers.\n" (List.length !missingheaders);
      List.iter (fun (h,k) -> Printf.fprintf oc "%Ld. %s\n" h (hashval_hexstring k)) !missingheaders;
      Printf.fprintf oc "%d missing deltas.\n" (List.length !missingdeltas);
      List.iter (fun (h,k) -> Printf.fprintf oc "%Ld. %s\n" h (hashval_hexstring k)) !missingdeltas);
  ac "getledgerroot" "getledgerroot" "Print the current ledger root."
    (fun oc al ->
      let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
      Printf.fprintf oc "Ledger root: %s\n" (hashval_hexstring lr));
  ac "getinfo" "getinfo" "Print a summary of the current proofgold node state including:\nnumber of connections, current best block, current difficulty, current balance."
    (fun oc al ->
      remove_dead_conns();
      let ll = List.length !netconns in
      Printf.fprintf oc "%d connection%s\n" ll (if ll = 1 then "" else "s");
      begin
	try
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "No blocks yet\n"
	    | Some(h,lbk,ltx) ->
		let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		let (tar,tmstmp,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
		let gtm = Unix.gmtime (Int64.to_float tmstmp) in
		Printf.fprintf oc "Best block %s at height %Ld\n" (hashval_hexstring h) blkh;
		Printf.fprintf oc "Ledger root: %s\n" (hashval_hexstring ledgerroot);
		Printf.fprintf oc "Time: %Ld (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		Printf.fprintf oc "Target: %s\n" (string_of_big_int tar);
		Printf.fprintf oc "Difficulty: %s\n" (string_of_big_int (difficulty tar));
		let (bal1,bal1u,bal2,bal2u,bal3,bal3u,bal4,bal4u) = Commands.get_atoms_balances_in_ledger oc ledgerroot blkh in
		Printf.fprintf oc "Total p2pkh: %s bars (%s unlocked)\n" (bars_of_atoms bal1) (bars_of_atoms bal1u);
		Printf.fprintf oc "Total p2sh: %s bars (%s unlocked)\n" (bars_of_atoms bal2) (bars_of_atoms bal2u);
		Printf.fprintf oc "Total via endorsement: %s bars (%s unlocked)\n" (bars_of_atoms bal3) (bars_of_atoms bal3u);
		Printf.fprintf oc "Total watched: %s bars (%s unlocked)\n" (bars_of_atoms bal4)  (bars_of_atoms bal4u);
		Printf.fprintf oc "Sum of all: %s bars (%s unlocked)\n"
		  (bars_of_atoms (Int64.add bal1 (Int64.add bal2 (Int64.add bal3 bal4))))
		  (bars_of_atoms (Int64.add bal1u (Int64.add bal2u (Int64.add bal3u bal4u))))
	  end;
	with e ->
	  Printf.fprintf oc "Exception: %s\n" (Printexc.to_string e)
      end);
  ac "getpeerinfo" "getpeerinfo" "List the current peers and when the last message was received from each."
    (fun oc al ->
      remove_dead_conns();
      let ll = List.length !netconns in
      Printf.fprintf oc "%d connection%s\n" ll (if ll = 1 then "" else "s");
      List.iter
	(fun (_,_,(_,_,_,gcs)) ->
	  match !gcs with
	  | Some(cs) ->
	      Printf.fprintf oc "%s (%s): %s\n" cs.realaddr cs.addrfrom cs.useragent;
	      let snc1 = sincetime (Int64.of_float cs.conntime) in
	      let snc2 = sincetime (Int64.of_float cs.lastmsgtm) in
	      Printf.fprintf oc "Connected for %s; last message %s ago.\n" snc1 snc2;
              begin
                match cs.strength with
                | Some(str) -> Printf.fprintf oc "Strength %d POW target %ld\n" str cs.powtarget
                | None -> ()
              end;
	      if cs.handshakestep < 5 then Printf.fprintf oc "(Still in handshake phase)\n";
              if not (cs.powchallenge = None) then Printf.fprintf oc "(outstanding POW challenge)\n";
	  | None -> (*** This could happen if a connection died after remove_dead_conns above. ***)
	      Printf.fprintf oc "[Dead Connection]\n";
	)
	!netconns;
      flush oc);
  ac "nettime" "nettime" "Print the current network time (median of peers) and skew from local node."
    (fun oc al ->
      let (tm,skew) = network_time() in
      Printf.fprintf oc "network time %Ld (median skew of %d)\n" tm skew;
      flush oc);
  ac "invalidateblock" "invalidateblock <blockhash>" "Manually invalidate a proofgold block\nThis should be used if someone is attacking the network and nodes decide to ignore their blocks."
    (fun oc al ->
      match al with
      | [h] ->
	  let hh = hexstring_hashval h in
	  recursively_invalidate_blocks hh
      | _ -> raise BadCommandForm);
  ac "revalidateblock" "revalidateblock <blockhash>" "Manually mark a previously manually invalidated block as being valid.\nThis will also mark the previous blocks as valid."
    (fun oc al ->
      match al with
      | [h] ->
	  let hh = hexstring_hashval h in
	  recursively_revalidate_blocks hh
      | _ -> raise BadCommandForm);
  ac "rawblockheader" "rawblockheader <blockhash>" "Print the given block header in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bh = DbBlockHeader.dbget h in
	      let sb = Buffer.create 1000 in
	      seosbf (seo_blockheader seosb bh (sb,None));
	      let s = string_hexstring (Buffer.contents sb) in
	      Printf.fprintf oc "%s\n" s;
	    with Not_found ->
	      Printf.fprintf oc "Could not find header %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "rawblockdelta" "rawblockdelta <blockid>" "Print the given block delta in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bd = DbBlockDelta.dbget h in
	      let sb = Buffer.create 1000 in
	      seosbf (seo_blockdelta seosb bd (sb,None));
	      let s = string_hexstring (Buffer.contents sb) in
	      Printf.fprintf oc "%s\n" s;
	    with Not_found ->
	      Printf.fprintf oc "Could not find delta %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "rawblock" "rawblock <blockid>" "Print the block (header and delta) in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bh = DbBlockHeader.dbget h in
	      try
		let bd = DbBlockDelta.dbget h in
		let sb = Buffer.create 1000 in
		seosbf (seo_block seosb (bh,bd) (sb,None));
		let s = string_hexstring (Buffer.contents sb) in
		Printf.fprintf oc "%s\n" s;
	      with Not_found ->
		Printf.fprintf oc "Could not find delta %s\n" hh
	    with Not_found ->
	      Printf.fprintf oc "Could not find header %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "getblock" "getblock <blockhash>" "Print information about the block, or request it from a peer if it is missing."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let (bhd,_) = DbBlockHeader.dbget h in
	      Printf.fprintf oc "Time: %Ld\n" bhd.timestamp;
	      begin
		try
		  let bd = DbBlockDelta.dbget h in
		  Printf.fprintf oc "%d txs\n" (List.length (bd.blockdelta_stxl));
		  List.iter (fun (tx,txs) -> Printf.fprintf oc "%s\n" (hashval_hexstring (hashtx tx))) (bd.blockdelta_stxl);
		with Not_found ->
		  find_and_send_requestdata GetBlockdelta h;
		  Printf.fprintf oc "Missing block delta\n"
	      end
	    with Not_found ->
	      find_and_send_requestdata GetHeader h
	  end
      | _ -> raise BadCommandForm);
  ac "nextstakingchances" "nextstakingchances [<hours> [<max ltc to burn> [<blockid>]]" "Print chances for the node to stake\nincluding chances if the node were to hypothetically burn some ltc (see extraburn).\nBy default nextstakingchances checks for every chance from the time of the previous block to 4 hours in the future."
    (fun oc al ->
      let (scnds,maxburn,n) =
	match al with
	| [] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * 4,100000000L,n)
	| [hrs] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * (int_of_string hrs),100000000L,n)
	| [hrs;maxburn] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * (int_of_string hrs),litoshis_of_ltc maxburn,n)
	| [hrs;maxburn;blockid] ->
	    begin
	      try
		let k = hexstring_hashval blockid in
		let (lbk,ltx) = get_burn k in
		(3600 * (int_of_string hrs),litoshis_of_ltc maxburn,Some(k,lbk,ltx))
	      with Not_found ->
		raise (Failure ("unknown block " ^ blockid))
	    end
	| _ -> raise BadCommandForm
      in
      begin
	let nw = ltc_medtime() in (*** for staking purposes, ltc is the clock to follow ***)
	let fromnow_string i nw =
	  if i <= nw then
	    "now"
	  else
	    let del = Int64.to_int (Int64.sub i nw) in
	    if del < 60 then
	      Printf.sprintf "%d seconds from now" del
	    else if del < 3600 then
	      Printf.sprintf "%d minutes %d seconds from now" (del / 60) (del mod 60)
	    else
	      Printf.sprintf "%d hours %d minutes %d seconds from now" (del / 3600) ((del mod 3600) / 60) (del mod 60)
	in
	match n with
	| None ->
           begin
             if nw > Int64.add !Config.genesistimestamp 86400L then
               raise (Failure ("could not find block"))
             else
               begin
                 compute_genesis_staking_chances !Config.genesistimestamp (min (Int64.add !Config.genesistimestamp 86400L) (Int64.add nw (Int64.of_int scnds)));
                 begin
	           try
		     match !genesisstakechances with
                     | Some(NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_)) ->
                        Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		     | Some(NextStake(_,_,_,_,_,_,_,_,_,_,_,_)) -> () (*** should not happen; ignore **)
		     | Some(NoStakeUpTo(_)) -> Printf.fprintf oc "Found no chance to stake with current wallet and ltc burn limits.\n"
                     | None -> raise Not_found
	           with Not_found -> ()
	         end;
	         List.iter
	           (fun z ->
		     let il = ref [] in
		     match z with
                     | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                        Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		     | NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		        if not (List.mem i !il) then
		          begin
			    il := i::!il; (** while the info should not be on the hash table more than once, sometimes it is, so only report it once **)
			    Printf.fprintf oc "With extraburn %Ld litoshis (%s ltc), could stake at time %Ld (%s) with asset %s at address %s.\n" toburn (ltc_of_litoshis toburn) i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr))
		          end
		     | _ -> ())
	           (List.sort
		      (fun y z ->
                        let tmstkch y =
                          match y with
                          | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> i
		          | NextStake(i,_,_,_,_,_,Some(_),_,_,_,_,_) -> i
		          | _ -> 0L
                        in
                        compare (tmstkch y) (tmstkch z))
		      (List.filter
		         (fun z ->
		           match z with
                           | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> true
		           | _ -> false)
		         !genesisstakechances_hypo))
               end
           end
	| Some(dbh,lbk,ltx) ->
	    let (_,tmstmp,_,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    Printf.fprintf oc "Trying to stake on top of %s with time stamp %Ld ltc block %s ltc burn tx %s\n" (hashval_hexstring dbh) tmstmp (hashval_hexstring lbk) (hashval_hexstring ltx);
	    compute_staking_chances (dbh,lbk,ltx) tmstmp (min (Int64.add tmstmp 604800L) (Int64.add nw (Int64.of_int scnds)));
	    begin
	      try
		match Hashtbl.find nextstakechances (lbk,ltx) with
                | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                   Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		    Printf.fprintf oc "Can stake at time %Ld (%s) with asset %s at address %s burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr)) toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,None,_,_,_,_,_) -> () (*** should not happen; ignore ***)
		| NoStakeUpTo(_) -> Printf.fprintf oc "Found no chance to stake with current wallet and ltc burn limits.\n"
	      with Not_found -> ()
	    end;
	    List.iter
	      (fun z ->
		let il = ref [] in
		match z with
                | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                   Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		    if not (List.mem i !il) then
		      begin
			il := i::!il; (** while the info should not be on the hash table more than once, sometimes it is, so only report it once **)
			Printf.fprintf oc "With extraburn %Ld litoshis (%s ltc), could stake at time %Ld (%s) with asset %s at address %s.\n" toburn (ltc_of_litoshis toburn) i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr))
		      end
		| _ -> ())
	      (List.sort
		 (fun y z ->
                   let tmstkch y =
                     match y with
                     | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> i
		     | NextStake(i,_,_,_,_,_,Some(_),_,_,_,_,_) -> i
		     | _ -> 0L
                   in
                   compare (tmstkch y) (tmstkch z))
		 (List.filter
		    (fun z ->
		      match z with
                      | NextPureBurn(_,_,_,_,_,_,_,_,_,_) -> true
		      | NextStake(_,_,_,_,_,_,Some(_),_,_,_,_,_) -> true
		      | _ -> false)
		    (Hashtbl.find_all nextstakechances_hypo (lbk,ltx))))
       end);
  ac "extraburn" "extraburn <ltc> or extraburn <litoshis> litoshis" "Order the node to burn up to the given amount of ltc given a chance to stake\nby doing the burn (see nextstakingchances)."
    (fun oc al ->
      match al with
      | [a] -> (extraburn := litoshis_of_ltc a; Hashtbl.clear nextstakechances)
      | [a;b] when b = "litoshis" -> (extraburn := Int64.of_string a; Hashtbl.clear nextstakechances)
      | _ -> raise BadCommandForm);
  ac "printassets" "printassets [<ledgerroot>] [<height>]" "Print the assets (in given ledger root assuming given block height).\nBy default the ledger root and height of the current best block is used."
    (fun oc al ->
      match al with
      | [] -> Commands.printassets oc
      | [lr;hght] -> Commands.printassets_in_ledger oc (hexstring_hashval lr) (Int64.of_string hght)
      | [lr] ->
	  begin
	    let n = get_bestblock_print_warnings oc in
	    match n with
	    | None -> raise (Failure ("could not find block"))
	    | Some(_,lbk,ltx) ->
		let (_,_,_,_,_,_,hght) = Db_outlinevals.dbget (hashpair lbk ltx) in
		Commands.printassets_in_ledger oc (hexstring_hashval lr) hght
	  end
      | _ -> raise BadCommandForm);
  ac "printtx" "printtx <txid> [<txid>] ... [<txid>]" "Print info about the given txs."
    (fun oc al -> List.iter (fun h -> Commands.printtx oc (hexstring_hashval h)) al);
  ac "importwallet" "importwallet <walletfile>" "Imports the entries from a wallet file into the current wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importwallet oc w
      | _ -> raise BadCommandForm);
  ac "importprivkey" "importprivkey <WIFkey> [staking|nonstaking|staking_fresh|nonstaking_fresh]" "Import a private key for a p2pkh address into the wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importprivkey oc w "staking"
      | [w;cls] -> Commands.importprivkey oc w cls
      | _ -> raise BadCommandForm);
  ac "importbtcprivkey" "importbtcprivkey <btcWIFkey> [staking|nonstaking|staking_fresh|nonstaking_fresh]" "Import a btc private key for a p2pkh address into the wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importbtcprivkey oc w "staking"
      | [w;cls] -> Commands.importbtcprivkey oc w cls
      | _ -> raise BadCommandForm);
  ac "importwatchaddr" "importwatchaddr <address> [offlinekey|offlinekey_fresh]" "Import a proofgold address to watch.\nofflinekey or offlinekey_fresh indicates that the user has the private key offline.\nofflinekey_fresh tells proofgold to use the address when it needs a fresh address controlled offline (e.g. for staking rewards)"
    (fun oc al ->
      match al with
      | [a] -> Commands.importwatchaddr oc a ""
      | [a;cls] ->
	  if cls = "offlinekey" || cls = "offlinekey_fresh" then
	    Commands.importwatchaddr oc a cls
	  else
	    raise BadCommandForm
      | _ -> raise BadCommandForm);
  ac "importwatchbtcaddr" "importwatchbtcaddr <address> [offlinekey|offlinekey_fresh]" "Import a proofgold address to watch by giving it as a bitcoin address.\nofflinekey or offlinekey_fresh indicates that the user has the private key offline.\nofflinekey_fresh tells proofgold to use the address when it needs a fresh address controlled offline (e.g. for staking rewards)"
    (fun oc al ->
      match al with
      | [a] -> Commands.importwatchbtcaddr oc a ""
      | [a;cls] ->
	  if cls = "offlinekey" || cls = "offlinekey_fresh" then
	    Commands.importwatchbtcaddr oc a cls
	  else
	    raise BadCommandForm
      | _ -> raise BadCommandForm);
  ac "importendorsement" "importendorsement <address> <address> <signature>" "Import a bitcoin signed endorsement message into the proofgold wallet.\nimportendorsement should be given three arguments: a b s where s is a signature made with the private key for address a endorsing to address b"
    (fun oc al ->
      match al with
      | [a;b;s] -> Commands.importendorsement oc a b s
      | _ -> raise BadCommandForm);
  ac "btctopfgaddr" "btctopfgaddr <btcaddress> [<btcaddress>] .. [<btcaddress>]" "Print the proofgold addresses corresponding to the given btc addresses."
    (fun oc al -> List.iter (Commands.btctopfgaddr oc) al);
  ac "printasset" "printasset <assethash>" "print information about the given asset"
    (fun oc al ->
      match al with
      | [h] -> Commands.printasset oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printhconselt" "printhconselt <hashval>" "Print information about the given hconselt, which is an asset possibly followed by a hash referencing more assets."
    (fun oc al ->
      match al with
      | [h] -> Commands.printhconselt oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeatm" "printctreeatm <hashval>" "Print information about a ctree atom with the given Merkle root."
    (fun oc al ->
      match al with
      | [h] -> Commands.printctreeatm oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeelt" "printctreeelt <hashval>" "Print information about a ctree element with the given Merkle root."
    (fun oc al ->
      match al with
      | [h] -> Commands.printctreeelt oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeinfo" "printctreeinfo [ledgerroot]" "Print info about a ctree with the given Merkle root."
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  Commands.printctreeinfo oc currledgerroot
      | [h] -> Commands.printctreeinfo oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "newofflineaddress" "newofflineaddress" "Find an address in the watch wallet that was marked as offlinekey and fresh.\nPrint it and mark it as no longer fresh."
    (fun oc al ->
      let alpha = Commands.get_fresh_offline_address oc in
      Printf.fprintf oc "%s\n" (addr_pfgaddrstr alpha));
  ac "newaddress" "newaddress [ledgerroot]" "If there is a key in the wallet classified as nonstaking_fresh, then print it and mark it as no longer fresh.\nOtherwise randomly generate a key, import the key into the wallet (as nonstaking) and print the correponding address.\nThe ledger root is used to ensure that the address is really empty (or was empty, given an old ledgerroot).\nSee also: newstakingaddress"
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  let (k,h) = Commands.generate_newkeyandaddress currledgerroot "nonstaking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | [clr] ->
	  let (k,h) = Commands.generate_newkeyandaddress (hexstring_hashval clr) "nonstaking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | _ -> raise BadCommandForm);
  ac "newstakingaddress" "newstakingaddress [ledgerroot]" "If there is a key in the wallet classified as staking_fresh, then print it and mark it as no longer fresh.\nOtherwise randomly generate a key, import the key into the wallet (as staking) and print the correponding address.\nThe ledger root is used to ensure that the address is really empty (or was empty, given an old ledgerroot).\nSee also: newaddress"
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  let (k,h) = Commands.generate_newkeyandaddress currledgerroot "staking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | [clr] ->
	  let (k,h) = Commands.generate_newkeyandaddress (hexstring_hashval clr) "staking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | _ -> raise BadCommandForm);
  ac "stakewith" "stakewith <address>" "Move an address in the wallet from nonstaking to staking.\nAttempts to spend assets from staking addresses might fail due to the asset being used to stake instead.\nSee also: donotstakewith"
    (fun oc al ->
      match al with
      | [alpha] -> Commands.reclassify_staking oc alpha true
      | _ -> raise BadCommandForm);
  ac "donotstakewith" "donotstakewith <address>" "Move an address in the wallet from staking to nonstaking.\nYou should mark an address as nonstaking if you want to ensure you can spend assets at the address.\nSee also: stakewith"
    (fun oc al ->
      match al with
      | [alpha] -> Commands.reclassify_staking oc alpha false
      | _ -> raise BadCommandForm);
  ac "createp2sh" "createp2sh <redeem script in hex>" "Create a p2sh address by giving the redeem script in hex"
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let bl = ref [] in
	  for i = (String.length s) - 1 downto 0 do
	    bl := Char.code s.[i]::!bl
	  done;
	  let alpha = Script.hash160_bytelist !bl in
	  Printf.fprintf oc "p2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr alpha));
      | _ -> raise BadCommandForm);
  ac "importp2sh" "importp2sh <redeem script in hex>" "Create a p2sh address by giving the redeem script in hex and import it into wallet"
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let bl = ref [] in
	  for i = (String.length s) - 1 downto 0 do
	    bl := Char.code s.[i]::!bl
	  done;
	  Commands.importp2sh oc !bl
      | _ -> raise BadCommandForm);
  ac "createchannel" "createchannel <alphapubkey> <betapubkey> <alphaassetid> <betaassetid> <alphaamt[bars]> <betaamt[bars]> [json]"
    "Create the initial information for a payment channel,\nincluding the unsigned funding tx, the funding address and funding asset id."
    (fun oc al ->
      let (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,jb) =
	match al with
	| [alphapubkey;betapubkey;alphaaid;betaaid;alphaamt;betaamt] ->
	    (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,false)
	| [alphapubkey;betapubkey;alphaaid;betaaid;alphaamt;betaamt;"json"] ->
	    (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,true)
	| _ -> raise BadCommandForm
      in
      let (alphapk,alphab) = hexstring_pubkey alphapubkey in
      let (betapk,betab) = hexstring_pubkey betapubkey in
      let aaid = hexstring_hashval alphaaid in
      let baid = hexstring_hashval betaaid in
      let aamt = atoms_of_bars alphaamt in
      let bamt = atoms_of_bars betaamt in
      let esttxbytes = 2000 in
      let fee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
      let halffee = Int64.div fee 2L in
      let (blkh,lr) =
	match get_bestblock_print_warnings oc with
	| None -> raise (Failure "trouble finding current ledger")
	| Some(_,lbk,ltx) ->
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    (blkh,lr)
      in
      let alpha = pubkey_be160 alphapk alphab in
      let beta = pubkey_be160 betapk betab in
      let alpha2 = p2pkhaddr_addr alpha in
      let beta2 = p2pkhaddr_addr beta in
      let (fundaddress,fundredscr) = Commands.createmultisig2 2 [(alphapubkey,(alphapk,alphab));(betapubkey,(betapk,betab))] in
      let fundaddress2 = p2shaddr_addr fundaddress in
      let (aa,av) =
	match ctree_lookup_asset false true true aaid (CHash(lr)) (0,alpha2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
      in
      let ach = Int64.sub av (Int64.add aamt halffee) in
      if ach < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" alphaaid));
      let (ba,bv) =
	match ctree_lookup_asset false true true baid (CHash(lr)) (0,beta2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" betaaid (addr_pfgaddrstr beta2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" betaaid (addr_pfgaddrstr beta2)))
      in
      let bch = Int64.sub bv (Int64.add bamt halffee) in
      if bch < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" betaaid));
      let tauin = [(alpha2,aaid);(beta2,baid)] in
      let tauout = ref [] in
      if bch > 0L then tauout := (beta2,(None,Currency(bch)))::!tauout;
      if ach > 0L then tauout := (alpha2,(None,Currency(ach)))::!tauout;
      (* split into two assets so commitment txs replace the two assets with two assets, avoiding full address attack (since addresses can only hold at most 32 assets) *)
      tauout := (fundaddress2,(None,Currency(bamt)))::!tauout;
      tauout := (fundaddress2,(None,Currency(aamt)))::!tauout;
      let tau = (tauin,!tauout) in
      let s = Buffer.create 100 in
      seosbf (seo_stx seosb (tau,([],[])) (s,None));
      let txh = hashtx tau in
      let fundid1 = hashpair txh (hashint32 0l) in
      let fundid2 = hashpair txh (hashint32 1l) in
      let hs = Hashaux.string_hexstring (Buffer.contents s) in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) fundredscr;
	  let jol = [("fundingtx",JsonStr(hs));
		     ("fundaddress",JsonStr(addr_pfgaddrstr (p2shaddr_addr fundaddress)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("fundassetid1",JsonStr(hashval_hexstring fundid1));
		     ("fundassetid2",JsonStr(hashval_hexstring fundid2))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "Funding tx: %s\n" hs;
	  Printf.fprintf oc "Fund 2-of-2 address: %s\n" (addr_pfgaddrstr (p2shaddr_addr fundaddress));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) fundredscr;
	  Printf.fprintf oc "\nFund asset id 1: %s\n" (hashval_hexstring fundid1);
	  Printf.fprintf oc "Fund asset id 2: %s\n" (hashval_hexstring fundid2)
	end);
  ac "createchannelonefunder" "createchannelonefunder <alphapubkey> <betapubkey> <alphaassetid> <alphaamt[bars]> [json]"
    "Create the initial information for a payment channel (with only alpha funding the channel),\nincluding the unsigned funding tx, the funding address and funding asset id."
    (fun oc al ->
      let (alphapubkey,betapubkey,alphaaid,alphaamt,jb) =
	match al with
	| [alphapubkey;betapubkey;alphaaid;alphaamt] ->
	    (alphapubkey,betapubkey,alphaaid,alphaamt,false)
	| [alphapubkey;betapubkey;alphaaid;alphaamt;"json"] ->
	    (alphapubkey,betapubkey,alphaaid,alphaamt,true)
	| _ -> raise BadCommandForm
      in
      let (alphapk,alphab) = hexstring_pubkey alphapubkey in
      let (betapk,betab) = hexstring_pubkey betapubkey in
      let aaid = hexstring_hashval alphaaid in
      let aamt = atoms_of_bars alphaamt in
      let esttxbytes = 2000 in
      let fee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
      let (blkh,lr) =
	match get_bestblock_print_warnings oc with
	| None -> raise (Failure "trouble finding current ledger")
	| Some(_,lbk,ltx) ->
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    (blkh,lr)
      in
      let alpha = pubkey_be160 alphapk alphab in
      let alpha2 = p2pkhaddr_addr alpha in
      let (fundaddress,fundredscr) = Commands.createmultisig2 2 [(alphapubkey,(alphapk,alphab));(betapubkey,(betapk,betab))] in
      let fundaddress2 = p2shaddr_addr fundaddress in
      let (aa,av) =
	match ctree_lookup_asset false true true aaid (CHash(lr)) (0,alpha2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
      in
      let ach = Int64.sub av (Int64.add aamt fee) in
      if ach < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" alphaaid));
      let tauin = [(alpha2,aaid)] in
      let tauout = ref [] in
      if ach > 0L then tauout := (alpha2,(None,Currency(ach)))::!tauout;
      (* split into two assets so commitment txs replace the two assets with two assets, avoiding full address attack (since addresses can only hold at most 32 assets) *)
      let aamthalf = Int64.div aamt 2L in
      tauout := (fundaddress2,(None,Currency(aamthalf)))::!tauout;
      tauout := (fundaddress2,(None,Currency(Int64.sub aamt aamthalf)))::!tauout;
      let tau = (tauin,!tauout) in
      let s = Buffer.create 100 in
      seosbf (seo_stx seosb (tau,([],[])) (s,None));
      let txh = hashtx tau in
      let fundid1 = hashpair txh (hashint32 0l) in
      let fundid2 = hashpair txh (hashint32 1l) in
      let hs = Hashaux.string_hexstring (Buffer.contents s) in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) fundredscr;
	  let jol = [("fundingtx",JsonStr(hs));
		     ("fundaddress",JsonStr(addr_pfgaddrstr (p2shaddr_addr fundaddress)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("fundassetid1",JsonStr(hashval_hexstring fundid1));
		     ("fundassetid2",JsonStr(hashval_hexstring fundid2))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "Funding tx: %s\n" hs;
	  Printf.fprintf oc "Fund 2-of-2 address: %s\n" (addr_pfgaddrstr (p2shaddr_addr fundaddress));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) fundredscr;
	  Printf.fprintf oc "\nFund asset id 1: %s\n" (hashval_hexstring fundid1);
	  Printf.fprintf oc "Fund asset id 2: %s\n" (hashval_hexstring fundid2)
	end);
  ac "createhtlc" "createhtlc <p2pkhaddr:alpha> <p2pkhaddr:beta> <timelock> [relative] [<secret>] [json]"
    "Create hash timelock constract script and address.\nThe controller of address alpha can spend with the secret.\nThe controller of the address beta can spend after the timelock.\nThe controller of address alpha should call this command and the secret will be held in alpha's wallet.\nA hex 32 byte secret can optionally be given, otherwise one will be randomly generated.\nIf 'relative' is given, then relative lock time (CSV) is used. Otherwise absolute lock time (CLTV) is used.\nThe timelock is either in block time (if less than 500000000) or unix time (otherwise).\nOnly block time can be used with relative block time."
    (fun oc al ->
      let (alphas,alpha,betas,beta,tmlock,rel,secr,jb) =
	match al with
	  [alpha;beta;tmlock] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,big_int_hashval (strong_rand_256()),false)
	| [alpha;beta;tmlock;"relative"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,big_int_hashval (strong_rand_256()),false)
	| [alpha;beta;tmlock;"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,big_int_hashval (strong_rand_256()),false)
	| [alpha;beta;tmlock;secr] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,hexstring_hashval secr,false)
	| [alpha;beta;tmlock;"relative";"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,big_int_hashval (strong_rand_256()),true)
	| [alpha;beta;tmlock;"relative";secr] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,hexstring_hashval secr,false)
	| [alpha;beta;tmlock;secr;"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,hexstring_hashval secr,true)
	| [alpha;beta;tmlock;"relative";secr;"true"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,hexstring_hashval secr,true)
	| _ -> raise BadCommandForm
      in
      if not (p2pkhaddr_p alpha) then raise (Failure (Printf.sprintf "%s is not a p2pkh address" alphas));
      if not (p2pkhaddr_p beta) then raise (Failure (Printf.sprintf "%s is not a p2pkh address" betas));
      if tmlock < 1l then raise (Failure ("locktime must be positive"));
      if rel && tmlock >= 500000000l then raise (Failure ("relative lock time must be given in number of blocks"));
      let (_,av) = alpha in
      let (_,bv) = beta in
      let (gamma,scrl,secrh) = Commands.createhtlc av bv tmlock rel secr in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) scrl;
	  let jol = [("address",JsonStr(addr_pfgaddrstr (p2shaddr_addr gamma)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("secret",JsonStr(hashval_hexstring secr));
		     ("hashofsecret",JsonStr(hashval_hexstring secrh))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "P2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr gamma));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	  Printf.fprintf oc "\n";
	  Printf.fprintf oc "Secret: %s\n" (hashval_hexstring secr);
	  Printf.fprintf oc "Hash of secret: %s\n" (hashval_hexstring secrh)
	end);
  ac "verifycommitmenttx" "verifycommitmenttx alpha beta fundaddress fundid1 fundid2 alphaamt betaamt secrethash tx [json]"
    "Verify a commitment tx"
    (fun oc al ->
      let (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,jb) =
	match al with
	| [alphas;betas;gammas;fundid1s;fundid2s;alphaamts;betaamts;secrethashs;txs] ->
	    (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,false)
	| [alphas;betas;gammas;fundid1s;fundid2s;alphaamts;betaamts;secrethashs;txs;"json"] ->
	    (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,true)
	| _ -> raise BadCommandForm
      in
      let alpha = pfgaddrstr_addr alphas in
      let beta = pfgaddrstr_addr betas in
      let gamma = pfgaddrstr_addr gammas in
      let fundid1 = hexstring_hashval fundid1s in
      let fundid2 = hexstring_hashval fundid2s in
      let alphaamt = atoms_of_bars alphaamts in
      let betaamt = atoms_of_bars betaamts in
      let secrethash = hexstring_hashval secrethashs in
      let txs2 = hexstring_string txs in
      let (((tauin,tauout) as tau,(tausigsin,_)),_) = sei_stx seis (txs2,String.length txs2,None,0,0) in
      let inputsok =
	match tauin with
	| [(a1,aid1);(a2,aid2)] when a1 = gamma && a2 = gamma && aid1 = fundid1 && aid2 = fundid2 -> true
	| _ -> false
      in
      let (outputsok,htlcaddr) =
	match tauout with
	| [(a01,(Some(aaddr2,0L,false),Currency(aamt2)));(a02,(Some(baddr2,0L,false),Currency(bamt2)))] when aamt2 = alphaamt && bamt2 = betaamt && a01 = gamma && a02 = gamma ->
	    if payaddr_addr aaddr2 = alpha then (*** this must be a commitment for beta to close the channel ***)
	      (2,Some(payaddr_addr baddr2))
	    else if payaddr_addr baddr2 = beta then (*** this must be a commitment for alpha to close the channel ***)
	      (1,Some(payaddr_addr aaddr2))
	    else
	      (0,None)
	| _ -> (0,None)
      in
      if inputsok then
	if outputsok = 1 then
	  begin
	    let (_,av) = alpha in
	    let (_,bv) = beta in
	    let (delta,scrl,secrh) = Commands.createhtlc2 bv av 28l true secrethash in
	    if Some(p2shaddr_addr delta) = htlcaddr then
	      begin (** it's good, could also check if beta has already signed it -- for now alpha can check the signature by signing with alphas key and ensuring the result is completely signed **)
		if jb then
		  print_jsonval oc (JsonObj([("result",JsonBool(true));("commitmentfor",JsonStr(alphas))]))
		else
		  Printf.fprintf oc "Valid commitment tx for %s\n" alphas
	      end
	    else
	      begin
		if jb then
		  print_jsonval oc (JsonBool(false))
		else
		  begin
		    Printf.fprintf oc "Appears to be a commitment tx for alpha, but htlc address mismatch:\nFound %s\nExpected %s\n"
		      (addr_pfgaddrstr (p2shaddr_addr delta))
		      (match htlcaddr with Some(delta2) -> addr_pfgaddrstr delta2 | None -> "None")
		  end
	      end
	  end
	else if outputsok = 2 then
	  begin
	    let (_,av) = alpha in
	    let (_,bv) = beta in
	    let (delta,scrl,secrh) = Commands.createhtlc2 av bv 28l true secrethash in
	    if Some(p2shaddr_addr delta) = htlcaddr then
	      begin (** it's good, could also check if alpha has already signed it -- for now alpha can check the signature by signing with alphas key and ensuring the result is completely signed **)
		if jb then
		  print_jsonval oc (JsonObj([("result",JsonBool(true));("commitmentfor",JsonStr(betas))]))
		else
		  Printf.fprintf oc "Valid commitment tx for %s\n" betas
	      end
	    else
	      begin
		if jb then
		  print_jsonval oc (JsonBool(false))
		else
		  begin
		    Printf.fprintf oc "Appears to be a commitment tx for beta, but htlc address mismatch:\nFound %s\nExpected %s\n"
		      (addr_pfgaddrstr (p2shaddr_addr delta))
		      (match htlcaddr with Some(delta2) -> addr_pfgaddrstr delta2 | None -> "None")
		  end
	      end
	  end
	else
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Outputs do not match the form of a commitment tx.\n"
	  end
      else
	if not (outputsok = 0) then
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Inputs do not match the form of a commitment tx.\n"
	  end
	else
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Inputs and outputs do not match the form of a commitment tx.\n"
	  end);
  ac "createmultisig" "createmultisig <m> <jsonarrayofpubkeys>" "Create an m-of-n script and address"
    (fun oc al ->
      match al with
      | [ms;pubkeyss] ->
	  let m = int_of_string ms in
	  begin
	    let (jpks,_) = parse_jsonval pubkeyss in
	    let (alpha,scrl) = Commands.createmultisig m jpks in
	    let alphastr = addr_pfgaddrstr (p2shaddr_addr alpha) in
	    Printf.fprintf oc "P2sh address: %s\n" alphastr;
	    Printf.fprintf oc "Redeem script: ";
	    List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	    Printf.fprintf oc "\n";
	  end
      | _ -> raise BadCommandForm);
  ac "addmultisig" "addmultisig <m> <jsonarrayofpubkeys>" "Create an m-of-n script and address and add it to the wallet"
    (fun oc al ->
      match al with
      | [ms;pubkeyss] ->
	  let m = int_of_string ms in
	  begin
	    let (jpks,_) = parse_jsonval pubkeyss in
	    let (alpha,scrl) = Commands.createmultisig m jpks in
	    let alphastr = addr_pfgaddrstr (p2shaddr_addr alpha) in
	    Commands.importp2sh oc scrl;
	    Printf.fprintf oc "P2sh address: %s\n" alphastr;
	    Printf.fprintf oc "Redeem script: ";
	    List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	    Printf.fprintf oc "\n";
	  end
      | _ -> raise BadCommandForm);
  ac "createatomicswap" "createatomicswap <ltctxid> <pfgaddr> <pfgrefundaddr> <timelock> [json]"
    "Create a script and corresponding p2sh address for an atomic swap with ltc.\nThe address will be spendable by <pfgaddr> after the given litecoin tx has at least one confirmation.\nThe address will be spendable by <pfgrefundaddr> after <timelock>.\nIf the keyword 'json' is given then the response is given in json format.\nThe intended use is that Alice has some X Proofgold bars that Bob will pay Y litecoins for.\nBob has his litecoins in a segwit addresses. Bob creates an unsigned litecoin tx sending Y litecoins to Alice.\nAlice verifies Bob's litecoin tx and notes the txid.\nAlice then uses createatomicswap with this litecoin txid, Bob's Proofgold address,\na refund address for Alice and a timelock in case Bob does not sign and publish the litecoin tx.\nAlice sends X Proofgold bars to the created p2sh address.\nIf Bob signs and publishes the litecoin tx and it confirms before the timelock,\n Bob will be able to spend the Proofgold bars to an address only he controls.\nIf the litecoin tx is not confirmed before the timelock,\nAlice can recover the funds by spending from the p2sh address after the timelock passes."
    (fun oc al ->
      let (ltx,alpha,beta,tmlock,jb) =
        match al with
        | (ltx::alpha::beta::tmlock::r) ->
           let ltx = hexstring_hashval ltx in
           let alpha = Cryptocurr.pfgaddrstr_addr alpha in
           let beta = Cryptocurr.pfgaddrstr_addr beta in
           let tmlock = Int32.of_string tmlock in
           let (a0,av) = alpha in
           let (b0,bv) = beta in
           if not (a0 = 0 && b0 = 0) then raise (Failure "The two addresses must be p2pkh.");
           (ltx,av,bv,tmlock,r = ["json"])
        | _ -> raise BadCommandForm
      in
      let (gamma,scrl) = Commands.createatomicswap ltx alpha beta tmlock in
      if jb then
        begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) scrl;
          let jol = [("address",JsonStr(addr_pfgaddrstr (p2shaddr_addr gamma)));
                     ("redeemscript",JsonStr(Buffer.contents redscr))]
          in
          print_jsonval oc (JsonObj(jol))
        end
      else
        begin
	  Printf.fprintf oc "P2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr gamma));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	  Printf.fprintf oc "\n";
        end);
  ac "createtx" "createtx <inputs as json array> <outputs as json array>" "Create a simple tx spending some assets to create new currency assets.\neach input: {\"<addr>\":\"<assetid>\"}\neach output: {\"addr\":\"<addr>\",\"val\":<bars>,\"lockheight\":<height>,\"lockaddr\":\"<addr>\"}\nwhere lock is optional (default null, unlocked output)\nand lockaddr is optional (default null, meaning the holder address is implicitly the lockaddr)\nSee also: creategeneraltx"
    (fun oc al ->
      match al with
      | [inp;outp] ->
	  begin
	    try
	      let (inpj,_) = parse_jsonval inp in
	      begin
		try
		  let (outpj,_) = parse_jsonval outp in
		  let tau = Commands.createtx inpj outpj in
		  let s = Buffer.create 100 in
		  seosbf (seo_stx seosb (tau,([],[])) (s,None));
		  let hs = Hashaux.string_hexstring (Buffer.contents s) in
		  Printf.fprintf oc "%s\n" hs
		with
		| JsonParseFail(i,msg) ->
		    Printf.fprintf oc "Problem parsing json object for tx inputs at position %d %s\n" i msg
	      end
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for tx outputs at position %d %s\n" i msg
	  end
      | _ -> raise BadCommandForm);
  ac "creategeneraltx" "creategeneraltx <tx as json object>" "Create a general tx given as as a json object.\nEvery possible transaction can be represented this way,\nincluding txs publishing mathematical documents and collecting bounties.\nSee also: createtx and createsplitlocktx"
    (fun oc al ->
      try
	match al with
	| [jtxstr] ->
	    let (jtx,_) = parse_jsonval jtxstr in
	    let tau = tx_from_json jtx in
	    let s = Buffer.create 100 in
	    seosbf (seo_stx seosb (tau,([],[])) (s,None));
	    let hs = Hashaux.string_hexstring (Buffer.contents s) in
	    Printf.fprintf oc "%s\n" hs
	| _ -> raise BadCommandForm
      with
      | JsonParseFail(i,msg) ->
	  Printf.fprintf oc "Problem parsing json object for tx at position %d %s\n" i msg);
  ac "createsplitlocktx" "createsplitlocktx <current address> <assetid> <number of outputs> <lockheight> <fee> [<new holding address> [<new obligation address> [<ledger root> <current block height>]]]" "Create a tx to spend an asset into several assets locked until a given height.\nOptionally the new assets can be held at a new address, and may be controlled by a different obligation address."
    (fun oc al ->
      match al with
      | (alp::aid::n::lkh::fee::r) ->
	  begin
	    let alpha2 = pfgaddrstr_addr alp in
	    if not (payaddr_p alpha2) then raise (Failure (alp ^ " is not a pay address"));
	    let (p,av) = alpha2 in
	    let alpha = (p=1,av) in
	    let aid = hexstring_hashval aid in
	    let n = int_of_string n in
	    if n <= 0 then raise (Failure ("Cannot split into " ^ (string_of_int n) ^ " assets"));
	    let lkh = Int64.of_string lkh in
	    let fee = atoms_of_bars fee in
	    if fee < 0L then raise (Failure ("Cannot have a negative fee"));
	    let (blkhght,lr) =
	      match r with
	      | [_;_;lr;blkhght] ->
		  (Int64.of_string blkhght,hexstring_hashval lr)
	      | _ ->
		  try
		    match get_bestblock_print_warnings oc with
		    | None -> raise Not_found
		    | Some(_,lbk,ltx) ->
			let (_,_,_,_,_,_,blkhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
			let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			(blkhght,lr)
		  with Not_found ->
		    raise (Failure("Could not find ledger root"))
	    in
	    match r with
	    | [] ->
		let gamma = alpha2 in
		let beta = alpha in
		Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
	    | (gam::r) ->
		let gamma = pfgaddrstr_addr gam in
		if not (payaddr_p gamma) then raise (Failure (gam ^ " is not a pay address"));
		match r with
		| [] ->
		    let beta = alpha in
		    let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
		    Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
		| (bet::r) ->
		    let beta2 = pfgaddrstr_addr bet in
		    if not (payaddr_p beta2) then raise (Failure (bet ^ " is not a pay address"));
		    let (p,bv) = beta2 in
		    let beta = (p=1,bv) in
		    match r with
		    | [] -> Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
		    | [_;_] -> Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee (** lr and blockheight given, handled above **)
		    | _ -> raise BadCommandForm
	  end
      | _ -> raise BadCommandForm);
  ac "hashsecret" "hashsecret <hashval in hex>"
    "Compute the sha256 hash of a secret (32 bytes given in hex)\nintended to be used to check secrets used in hash time lock contracts (htlc)\nespecially in payment channels."
    (fun oc al ->
      match al with
      | [secr] when String.length secr = 64 ->
	  let secrh = Script.sha256_bytelist (string_bytelist (hexstring_string secr)) in
	  Printf.fprintf oc "%s\n" (hashval_hexstring secrh)
      | _ -> raise BadCommandForm);
  ac "simplesigntx" "simplesigntx <tx in hex> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets>]]]" "Sign a proofgold tx, under the simple assumption that the obligations are defaults\nand all inputs and outputs are currency assets.\nThis command is useful for signing txs that spend assets that are not yet in the ledger,\nfor example when creating a payment channel."
    (fun oc al ->
      match al with
      | [s] -> Commands.simplesigntx oc s [] [] None
      | [s;kl] ->
	  let kl = parse_json_privkeys kl in
	  Commands.simplesigntx oc s [] [] (Some(kl))
      | [s;kl;rl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  Commands.simplesigntx oc s rl [] (Some(kl))
      | [s;kl;rl;sl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.simplesigntx oc s rl sl (Some(kl))
      | _ -> raise BadCommandForm);
  ac "signtx" "signtx <tx in hex> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets> [<ledgerroot>]]]]" "Sign a proofgold tx."
    (fun oc al ->
      match al with
      | [s] -> Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s [] [] None
      | [s;kl] ->
	  let kl = parse_json_privkeys kl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s [] [] (Some(kl))
      | [s;kl;rl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s rl [] (Some(kl))
      | [s;kl;rl;sl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s rl sl (Some(kl))
      | [s;kl;rl;sl;lr] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.signtx oc (hexstring_hashval lr) s rl sl (Some(kl))
      | _ -> raise BadCommandForm);
  ac "signtxfile" "signtxfile <infile> <outfile> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets> [<ledgerroot>]]]]" "Sign a proofgold tx.\n<infile> is an existing binary file with the (possibly partially signed) tx.\n<outfile> is a binary file created with the output tx."
    (fun oc al ->
      let kl =
	match al with
	| (_::_::kl::_) -> Some(parse_json_privkeys kl)
	| _ -> None
      in
      let rl =
	match al with
	| (_::_::_::rl::_) -> parse_json_redeemscripts rl
	| _ -> []
      in
      let sl =
	match al with
	| (_::_::_::_::sl::_) -> parse_json_secrets sl
	| _ -> []
      in
      let lr =
	match al with
	| (_::_::_::_::_::lr::_) -> hexstring_hashval lr
	| _ -> get_ledgerroot (get_bestblock_print_warnings oc)
      in
      match al with
      | (s1::s2::_) ->
	  let c1 = open_in_bin s1 in
	  let (stau,_) = Tx.sei_stx seic (c1,None) in
	  close_in_noerr c1;
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signtxc oc lr stau c2 rl sl kl;
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | _ -> raise BadCommandForm);
  ac "signbatchtxsfiles" "signbatchtxsfiles <infile> <outfile> [<jsonarrayofprivkeys> [<ledgerroot>]]" "Sign a proofgold tx.\n<infile> is an existing binary file with several (possibly partially signed) txs.\n<outfile> is a binary file created with the txs after signing."
    (fun oc al ->
      let read_staul s1 =
	let staur = ref [] in
	let c1 = open_in_bin s1 in
	try
	  while true do
	    let (stau,_) = Tx.sei_stx seic (c1,None) in
	    staur := stau::!staur
	  done;
	  []
	with
	| End_of_file -> close_in_noerr c1; List.rev !staur
	| _ -> close_in_noerr c1; raise BadCommandForm
      in
      match al with
      | [s1;s2] ->
	  let staul = read_staul s1 in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (get_ledgerroot (get_bestblock_print_warnings oc)) staul c2 [] [] None;
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | [s1;s2;kl] ->
	  let staul = read_staul s1 in
	  let kl = parse_json_privkeys kl in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (get_ledgerroot (get_bestblock_print_warnings oc)) staul c2 [] [] (Some(kl));
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | [s1;s2;kl;lr] ->
	  let staul = read_staul s1 in
	  let kl = parse_json_privkeys kl in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (hexstring_hashval lr) staul c2 [] [] (Some(kl));
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | _ -> raise BadCommandForm);
  ac "txpool" "txpool" "Print info about txpool"
    (fun oc al ->
      Hashtbl.iter
        (fun k stau ->
          let sz = stxsize stau in
          Printf.fprintf oc ". %s size %d\n" (hashval_hexstring k) sz;
          if sz < 400 then
            let sb = Buffer.create 400 in
            seosbf (seo_stx seosb stau (sb,None));
            Printf.fprintf oc "%s\n" (string_hexstring (Buffer.contents sb)))
        stxpool);
  ac "savetxtopool" "savetxtopool <tx in hex>" "Save a proofgold tx to the local pool without sending it to the network."
    (fun oc al ->
      match al with
      | [s] ->
	  let b = get_bestblock_print_warnings oc in
	  begin
	    match b with
	    | None -> Printf.fprintf oc "Cannot find best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    Commands.savetxtopool blkh tm lr s
		  with Not_found ->
		    let (bhd,_) = DbBlockHeader.dbget dbh in
		    let lr = bhd.newledgerroot in
		    let tm = bhd.timestamp in
		    Commands.savetxtopool blkh tm lr s
		with Not_found ->
		  Printf.fprintf oc "Trouble finding current block height\n"
	  end
      | _ -> raise BadCommandForm);
  ac "sendtx" "sendtx <tx in hex>" "Send a proofgold tx to other nodes on the network."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "Cannot find best block.\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  Commands.sendtx oc (Int64.add 1L blkh) tm tr sr lr s
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "sendtxfile" "sendtxfile <file with tx in binary>" "Send a proofgold tx to other nodes on the network."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "Cannot find best block.\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  let c = open_in_bin s in
		  let (stau,_) = Tx.sei_stx seic (c,None) in
		  let txbytes = pos_in c in
		  close_in_noerr c;
		  if txbytes > 450000 then
		    Printf.fprintf oc "Refusing to send tx > 450K bytes\n"
		  else
		    Commands.sendtx2 oc (Int64.add 1L blkh) tm tr sr lr txbytes stau
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatetx" "validatetx <tx in hex>" "Print information about the tx and whether or not it is valid.\nIf the tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      Commands.validatetx oc (Int64.add 1L blkh) tm tr sr lr s
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatetxfile" "validatetxfile <file with tx in binary>" "Print information about the tx and whether or not it is valid.\nIf the tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      let c = open_in_bin s in
		      let (stau,_) = Tx.sei_stx seic (c,None) in
		      let txbytes = pos_in c in
		      close_in_noerr c;
		      if txbytes > 450000 then
			Printf.fprintf oc "Tx is > 450K bytes and will be considered too big to include in a block\n"
		      else
			Commands.validatetx2 oc (Int64.add 1L blkh) tm tr sr lr txbytes stau
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatebatchtxsfile" "validatebatchtxsfile <file with several tx in binary>" "Print information about the txs and whether or not it they valid.\nThe txs are considered in sequences with the previous txs modifying the ledger before evaluating the next.\nIf a tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      let c = open_in_bin s in
		      let staur = ref [] in
		      begin
			try
			  while true do
			    let (stau,_) = Tx.sei_stx seic (c,None) in
			    staur := stau::!staur
			  done
			with End_of_file ->
			  close_in_noerr c;
			  Commands.validatebatchtxs oc (Int64.add 1L blkh) tm tr sr lr (List.rev !staur)
		      end
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "theory" "theory <theoryid>" "Print information about a confirmed theory"
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let thyid = hexstring_hashval a in
	    let (_,tr,_) = get_3roots (get_bestblock_print_warnings oc) in
	    try
	      let tht = lookup_thytree tr in
	      let thy = ottree_lookup tht (Some(thyid)) in
	      let (prms,axs) = thy in
	      let i = ref 0 in
	      Printf.fprintf oc "Theory %s %d Prims %d Axioms:\nIds and Types of Prims:\n" a (List.length prms) (List.length axs);
	      List.iter
		(fun a ->
		  let h = tm_hashroot (Logic.Prim(!i)) in
		  incr i;
		  Printf.fprintf oc "%s %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 (Some(thyid)) (hashpair h (hashtp a))) 32l));
		  print_jsonval oc (json_stp a); Printf.fprintf oc "\n")
		prms;
	      Printf.fprintf oc "Ids of Axioms:\n";
	      List.iter
		(fun h -> Printf.fprintf oc "%s %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 (Some(thyid)) h) 33l)))
		axs;
	    with Not_found ->
	      Printf.fprintf oc "Theory not found.\n"
	  end
      | _ -> raise BadCommandForm);
  ac "signature" "signature <signatureid>" "Print information about a confirmed signature"
    (fun oc al ->
      let (a,sgid) =
	match al with
	| [a] -> (a,hexstring_hashval a)
	| _ -> raise BadCommandForm
      in
      let (_,_,sr) = get_3roots (get_bestblock_print_warnings oc) in
      try
	let sgt = lookup_sigtree sr in
	let (th,sg) = ostree_lookup sgt (Some(sgid)) in
	let ths = match th with Some(h) -> hashval_hexstring h | None -> "empty" in
	let (imps,(objs,kns)) = sg in
	Printf.fprintf oc "Signature %s in Theory %s\n%d Imported Signatures %d Objects %d Knowns:\n" a ths (List.length imps) (List.length objs) (List.length kns);
	Printf.fprintf oc "Imports:\n";
	List.iter
	  (fun h -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  imps;
	Printf.fprintf oc "Objects:\n";
	List.iter
	  (fun ((h,_),_) -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  objs;
	Printf.fprintf oc "Knowns:\n";
	List.iter
	  (fun (h,_) -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  kns;
      with Not_found ->
	Printf.fprintf oc "Signature not found.\n");
  ac "preassetinfo" "preassetinfo <preasset as json>" "Print information about a preasset given in json form.\nTypes of assets are currency, bounties,\n ownership of objects, ownership of propositions, ownership of negations of propositions,\nrights to use an object, rights to use a proposition,\ncommitment markers published before publishing a document, theory or signature,\na theories, signatures and documents."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    try
	      let (j,_) = parse_jsonval a in
	      let u = preasset_from_json j in
	      Commands.preassetinfo_report oc u
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for preasset at position %d %s\n" i msg
	  end
      | _ -> raise BadCommandForm);
  ac "terminfo" "terminfo <term as json> [<type as json>, with default 'prop'] [<theoryid, default of empty theory>]" "Print information about a mathematical term given in json format."
    (fun oc al ->
      let (jtm,jtp,thyid) =
	match al with
	| [jtm] -> (jtm,"'\"prop\"'",None)
	| [jtm;jtp] -> (jtm,jtp,None)
	| [jtm;jtp;theoryid] -> (jtm,jtp,Some(hexstring_hashval theoryid))
	| _ -> raise BadCommandForm
      in
      begin
	try
	  let (jtm,_) = parse_jsonval jtm in
	  begin
	    try
	      let (jtp,_) = parse_jsonval jtp in
	      let m =
		match jtm with
		| JsonStr(x) -> Logic.TmH(hexstring_hashval x) (*** treat a string as just the term root abbreviating the term ***)
		| _ -> trm_from_json jtm
	      in
	      let a =
		match jtp with
		| JsonStr(x) when x = "prop" -> Logic.Prop
		| JsonNum(x) -> Logic.Base(int_of_string x)
		| _ -> stp_from_json jtp
	      in (*** not checking if the term has the type; this could depend on the theory ***)
	      let h = tm_hashroot m in
	      let tph = hashtp a in
	      Printf.fprintf oc "term root: %s\n" (hashval_hexstring h);
	      Printf.fprintf oc "pure term address: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_be160 h)));
	      if thyid = None then
		begin
		  let k = hashtag (hashopair2 None (hashpair h tph)) 32l in
		  Printf.fprintf oc "obj id in empty theory: %s\n" (hashval_hexstring k);
		  Printf.fprintf oc "obj address in empty theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_be160 k)))
		end
	      else
		begin
		  let k = hashtag (hashopair2 thyid (hashpair h tph)) 32l in
		  Printf.fprintf oc "obj id in given theory: %s\n" (hashval_hexstring k);
		  Printf.fprintf oc "obj address in given theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_be160 k)))
		end;
	      if a = Logic.Prop then
		begin
		  if thyid = None then
		    begin
		      let k = hashtag (hashopair2 None h) 33l in
		      Printf.fprintf oc "prop id in empty theory: %s\n" (hashval_hexstring k);
		      Printf.fprintf oc "prop address in empty theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_be160 k)))
		    end
		  else
		    begin
		      let k = hashtag (hashopair2 thyid h) 33l in
		      Printf.fprintf oc "prop id in given theory: %s\n" (hashval_hexstring k);
		      Printf.fprintf oc "prop address in given theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_be160 k)))
		    end
		end
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for tp at position %d %s\n" i msg
	  end
	with
	| JsonParseFail(i,msg) ->
	    Printf.fprintf oc "Problem parsing json object for tm at position %d %s\n" i msg
      end);
  ac "decodetx" "decodetx <raw tx in hex>" "Decode a proofgold tx."
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let (stx,_) = sei_stx seis (s,String.length s,None,0,0) in
	  print_jsonval oc (json_stx stx);
	  Printf.fprintf oc "\n"
      | _ -> raise BadCommandForm);
  ac "decodetxfile" "decodetxfile <file with binary tx>" "Decode a proofgold tx from a file."
    (fun oc al ->
      match al with
      | [s1] ->
	  let c1 = open_in_bin s1 in
	  let (stau,_) = Tx.sei_stx seic (c1,None) in
	  close_in_noerr c1;
	  print_jsonval oc (json_stx stau);
	  Printf.fprintf oc "\n"
      | _ -> raise BadCommandForm);
  ac "querybestblock" "querybestblock" "Print the current best block in json format.\nIn case of a tie, only one of the current best blocks is returned.\nThis command is intended to support explorers.\nSee also: bestblock"
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let lr = get_ledgerroot best in
	      print_jsonval oc (JsonObj([("height",JsonNum(Int64.to_string blkh));("block",JsonStr(hashval_hexstring h));("ledgerroot",JsonStr(hashval_hexstring lr))]))
	    with Not_found ->
	      print_jsonval oc (JsonObj([("height",JsonNum(Int64.to_string blkh));("block",JsonStr(hashval_hexstring h))]))
	  with Not_found ->
	    Printf.fprintf oc "Cannot determine height of best block %s\n" (hashval_hexstring h));
  ac "bestblock" "bestblock" "Print the current best block in text format.\nIn case of a tie, only one of the current best blocks is returned.\nSee also: querybestblock"
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let lr = get_ledgerroot best in
	      Printf.fprintf oc "Height: %Ld\nBlock hash: %s\nLedger root: %s\n" (Int64.sub blkh 1L) (hashval_hexstring h) (hashval_hexstring lr)
	    with Not_found ->
	      Printf.fprintf oc "Height: %Ld\nBlock hash: %s\n" (Int64.sub blkh 1L) (hashval_hexstring h)
	  with Not_found ->
	    Printf.fprintf oc "Block hash: %s\n" (hashval_hexstring h));
  ac "difficulty" "difficulty" "Print the current difficulty."
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let (tar,_,_,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	      Printf.fprintf oc "Current target (for block at height %Ld): %s\n" blkh (string_of_big_int tar)
	    with Not_found ->
	      Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring h) blkh
	  with Not_found ->
	    Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring h));
  ac "vetobountyfund" "vetobountyfund <blockid> [<addr>]" "If your node staked the given block, then try to spend the bounty fund part of the block reward.\nThe bounty fund part of the reward can be collected to the bounty fund after 48 blocks,\ngiving the staker (at least) 48 blocks to veto the collection.\nIf you veto the collection, you are expected to place an equal amount of bars (25 per block)\nas a bounty on a proposition of your choice.\nThe address (if given) might be a term address, in which case vetobountyfund directly places the bounty on that address.\nOtherwise the address is a pay address (by default the staking address) and you\nare expected to manually place bounties.\nIf you do not place such a bounty or it is determined the bounties are gamed,\nfuture staked blocks may be orphaned by the network."
    (fun oc al ->
      let (h,blkid,alpha,delta) =
        match al with
        | [h] ->
           let blkid = hexstring_hashval h in
           begin
             try
               let (bhd,bhs) = DbBlockHeader.dbget blkid in
               let alpha = bhd.stakeaddr in
               (h,blkid,alpha,p2pkhaddr_addr alpha)
             with Not_found ->
               raise (Failure (Printf.sprintf "Do not have header %s\n" h));
           end
        | [h;a] ->
           let blkid = hexstring_hashval h in
           let delta = pfgaddrstr_addr a in
           if pubaddr_p delta then raise BadCommandForm;
           begin
             try
               let (bhd,bhs) = DbBlockHeader.dbget blkid in
               let alpha = bhd.stakeaddr in
               (h,blkid,alpha,delta)
             with Not_found ->
               raise (Failure (Printf.sprintf "Do not have header %s\n" h));
           end
       | _ -> raise BadCommandForm
      in
      begin
        try
          let s kl = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) kl in
          let (k,b,(x,y),_,_,_) = s !Commands.walletkeys_staking in
          try
            let bd = DbBlockDelta.dbget blkid in
            let (gamma,scr) = Script.bountyfundveto alpha in
            match get_bestblock_print_warnings oc with
            | None -> Printf.fprintf oc "No blocks yet\n"
            | Some(h,lbk,ltx) ->
               let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
               let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
               if termaddr_p delta then
                 begin
                   let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,delta) in
                   if not (hl = HNil) then
                     raise (Failure (Printf.sprintf "There are already assets at %s.\nPlease choose an unused term address for a bounty.\n" (addr_pfgaddrstr delta)))
                 end;
               let f beta =
                 let hl = ctree_lookup_addr_assets true true (CHash(lr)) (0,beta) in
                 match
                   hlist_lookup_asset_gen true true true
                     (fun a -> match a with (_,_,Some(gamma2,n2,r2),Currency(_)) when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> true | _ -> false)
                     hl
                 with
                 | Some(aid,_,_,Currency(v)) ->
                    let txfee = Int64.mul 2000L !Config.defaulttxfee in
                    if v <= txfee then
                      Printf.fprintf oc "Not enough for txfee. Consider reducing defaulttxfee in proofgold.conf.\n"
                    else
                      let tau = ([(beta,aid)],[delta,(None,if termaddr_p delta then Bounty(Int64.sub v txfee) else Currency(Int64.sub v txfee))]) in
                      let (stau,si,so) = Commands.signtx2 oc lr (tau,([],[])) [(scr,gamma)] [] (Some([(k,b,(x,y),alpha)])) in
                      if (si && so) then
                        begin
                          Commands.sendtx2 oc blkh tm tr sr lr (stxsize stau) stau;
                          Printf.fprintf oc "Sent veto transaction.\n";
                          if payaddr_p delta then
                            Printf.fprintf oc "Make sure to place at least 25 bars worth of bounties on meaningful unproven propositions.\n"
                        end
                      else
                        Printf.fprintf oc "Problem signing veto tx.\n"
                 | _ ->
                    Printf.fprintf oc "Could not find bounty fund reward output in current ledger.\nIt is probably too late to veto.\n"
               in
               match bd.stakeoutput with
               | (beta,(Some(gamma2,n2,r2),Currency(_)))::_ when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> f beta
               | _::(beta,(Some(gamma2,n2,r2),Currency(_)))::_ when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> f beta
               | _ ->
                  Printf.fprintf oc "Could not find bounty fund reward output in coinstake.\n"
          with Not_found ->
            Printf.fprintf oc "Do not have delta %s\n" h
        with Not_found ->
          Printf.fprintf oc "Do not have private key for stake address in wallet.\n"
      end);
  ac "hashinttests" "hashinttests" "hashinttests" (* delete *)
    (fun oc al ->
      let int32l = ref [581869302l;1742863086l;1438850937l;545404204l;2013771743l;-1775435781l;-949333985l;-568478650l;-1323567403l;-418932835l] in
      let int64l = ref [871066256982911172L;3475034101394730335L;9092055236958169831L;9158095014910422873L;8627448804135228577L;-4165993559733355699L;-8874907355532813482L;-2026591599286391832L;-5499082447685365340L;-5479226235522558428L] in
      for i = 0 to 89 do int32l := Int32.of_int i :: !int32l done;
      for i = 0 to 89 do int64l := Int64.of_int i :: !int64l done;
      let tm = Unix.gettimeofday() in
      for i = 1 to 10000 do
        List.iter (fun v -> ignore (hashint32 v)) !int32l
      done;
      let tm2 = Unix.gettimeofday() in
      for i = 1 to 10000 do
        List.iter (fun v -> ignore (hashint64 v)) !int64l
      done;
      Printf.printf "int32s: %f\nint64s: %f\n" (tm2 -. tm) (Unix.gettimeofday() -. tm2));
  ac "bugtest" "bugtest" "bugtest" (* delete *)
    (fun oc al ->
      let k = hexstring_hashval "6160e043be6022fa47c9d615aff05e239d25841c66c0288610ca669afd08a5cf" in
      let a = DbAsset.dbget k in
      let (h,bd,obl,u) = a in
      print_jsonval oc (json_asset a);
      Printf.fprintf oc "\nbd:%Ld %s\n" bd (hashval_hexstring (hashint64 bd));
      Printf.fprintf oc "hpre: %s\n" (hashval_hexstring (hashpreasset u));
      Printf.fprintf oc "hpair: %s\n" (hashval_hexstring (hashpair (hashint64 bd) (hashpreasset u)));
      Printf.fprintf oc "aid: %s\n" (hashval_hexstring h);
      Printf.fprintf oc "htrip: %s\n" (hashval_hexstring (hashpair h (hashpair (hashint64 bd) (hashpreasset u))));
      Printf.fprintf oc "hobl: %s\n" (match hashobligation obl with None -> "None" | Some(k) -> hashval_hexstring k);
      Printf.fprintf oc "ha: %s\n" (hashval_hexstring (hashasset a)));
  ac "dbtest" "dbtest" "dbtest" (* delete *)
    (fun oc al ->
      let keys = ref [] in
      let tm1 = Unix.gettimeofday() in
      DbHConsElt.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbHConsElt %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbHConsElt.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbHConsElt deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let (ah,h) = DbHConsElt.dbget k in
          match h with
          | None ->
             if not (k = hashtag ah 3l) then raise (Failure (Printf.sprintf "HConsElt hash failure: %s" (hashval_hexstring k)))
          | Some(k1,l) ->
             if not (k = hashtag (hashpair ah k1) (Int32.of_int (4096+l))) then raise (Failure (Printf.sprintf "HConsElt hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbHConsElt deserialize and rehash %f\n" (tm4 -. tm3);
      keys := [];
      let tm1 = Unix.gettimeofday() in
      DbAsset.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbAsset %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbAsset.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbAsset deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let a = DbAsset.dbget k in
          if not (k = hashasset a) then raise (Failure (Printf.sprintf "Asset hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbAsset deserialize and rehash %f\n" (tm4 -. tm3);
      keys := [];
      let tm1 = Unix.gettimeofday() in
      DbCTreeAtm.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeAtm %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbCTreeAtm.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeAtm deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let c = DbCTreeAtm.dbget k in
          if not (k = ctree_hashroot c) then raise (Failure (Printf.sprintf "CTreeAtom hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeAtm deserialize and rehash %f\n" (tm4 -. tm3);
      keys := [];
      let tm1 = Unix.gettimeofday() in
      DbCTreeLeaf.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeLeaf %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbCTreeLeaf.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeLeaf deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let c = DbCTreeLeaf.dbget k in
          if not (k = ctree_hashroot c) then raise (Failure (Printf.sprintf "CTreeLeaf hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbCTreeLeaf deserialize and rehash %f\n" (tm4 -. tm3);
      keys := [];
      let tm1 = Unix.gettimeofday() in
      DbSTx.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbSTx %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbSTx.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbSTx deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let stau = DbSTx.dbget k in
          if not (k = hashstx stau) then raise (Failure (Printf.sprintf "STx hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbSTx deserialize and rehash %f\n" (tm4 -. tm3);
      keys := [];
      let tm1 = Unix.gettimeofday() in
      DbBlockHeader.dbkeyiter (fun k -> keys := k :: !keys);
      let tm2 = Unix.gettimeofday() in
      Printf.fprintf oc "DbBlockHeader %d keys %f\n" (List.length !keys) (tm2 -. tm1);
      List.iter
        (fun k -> ignore (DbBlockHeader.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbBlockHeader deserialize %f\n" (tm3 -. tm2);
      List.iter
        (fun k ->
          let bh = DbBlockHeader.dbget k in
          if not (k = blockheader_id bh) then raise (Failure (Printf.sprintf "BlockHeader hash failure: %s" (hashval_hexstring k))))
        !keys;
      let tm4 = Unix.gettimeofday() in
      Printf.fprintf oc "DbBlockHeader deserialize and rehash %f\n" (tm4 -. tm3);
      let tm2 = Unix.gettimeofday() in
      List.iter
        (fun k -> ignore (DbBlockDelta.dbget k))
        !keys;
      let tm3 = Unix.gettimeofday() in
      Printf.fprintf oc "DbBlockDelta deserialize %f\n" (tm3 -. tm2);
      keys := [];
    );
  ac "hashtest160" "hashtest160" "hashtest160" (* delete *)
    (fun oc al ->
      let h1s = "b453567dae66f8c30ca34aaef6d102f03fd3dd34bbfb360b7fe42ac9076a1caf" in
      let h1 = hexstring_hashval h1s in
      let h2s = "c67e78ecf065928e65d7e158ccbac3173e49afef8f7a944c07e54acdcb63b366" in
      let h2 = hexstring_hashval h2s in
      let md_hexstring c =
        let b = Buffer.create 64 in
        let (h0,h1,h2,h3,h4) = Be160.to_int32p5 c in
        int32_hexstring b h0;
        int32_hexstring b h1;
        int32_hexstring b h2;
        int32_hexstring b h3;
        int32_hexstring b h4;
        Buffer.contents b
      in
      let g c x =
        if not (md_hexstring c = x) then
          raise (Failure "hashtest160 failure")
      in
      g (hash160 h1s) "23f979f4d5f4104e0cd06cebb572718e0d012f7e";
      g (hashval_be160 h1) "779d4c88890180fe9fbffcfc32ffb963b9106f3e";
      g (hash160 h2s) "7d7ad877364a79c3468fbc59b527fad8bc6f71f6";
      g (hashval_be160 h2) "12f7a2ccbf8f44c9f29b5b9bb9c9e62f9bb84978";
      Printf.fprintf oc "hashtest160 passed\n");
  ac "hashtest1" "hashtest1" "hashtest1" (* delete *)
    (fun oc al ->
      let h1 = hexstring_hashval "b453567dae66f8c30ca34aaef6d102f03fd3dd34bbfb360b7fe42ac9076a1caf" in
      let h2 = hexstring_hashval "c67e78ecf065928e65d7e158ccbac3173e49afef8f7a944c07e54acdcb63b366" in
      let i32a = 182873996l in
      let i32b = -353996916l in
      let i64a = 198270026362470L in
      let i64b = -46815743024L in
      let privkey = big_int_of_string "89781401347074584135977282480277488620815033066203126710433227224864270366267" in
      let (pubkeyx,pubkeyy) = match Secp256k1.smulp privkey Secp256k1._g with Some(x,y) -> (big_int_be256 x,big_int_be256 y) | None -> raise (Failure "bad key in hashtest1; bug in testing code") in
      let hashint32a = hexstring_hashval "d83dc15e33701927f69d4b6dd44dbbdb8eda8147d173a2ec4c2d65a8d89764b0" in
      let hashint32b = hexstring_hashval "d3c16cc50fcf17adb0dc93f1aefefb427b4073c4473380ab32833cc677c58364" in
      let hashint64a = hexstring_hashval "a72b883e966ad52b12d687e62cdda3bcae78d6c84c9e7895b0ca418cf067d160" in
      let hashint64b = hexstring_hashval "56bcc7330fe974d753e5bec947e94a65559e133f49ce6e1938e159c97649d8e2" in
      let hashpaira = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair1a = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair1b = hexstring_hashval "2b930bf9f2558f4a7a21b4c0c79507d4cb92c0deff8142de2a17e62b941984d2" in
      let hashopair2a = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair2b = hexstring_hashval "ead4295d1c3e845f5559d6111bd2f966bcbdef3387ccedee2f9b7cfb44e13398" in
      let hashopaira = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopairb = hexstring_hashval "ead4295d1c3e845f5559d6111bd2f966bcbdef3387ccedee2f9b7cfb44e13398" in
      let hashopairc = hexstring_hashval "2b930bf9f2558f4a7a21b4c0c79507d4cb92c0deff8142de2a17e62b941984d2" in
      let hashtaga = hexstring_hashval "bdb7f8502049580fa081f253b3f8486535be3978b36714f3a79aba74b956d7b1" in
      let hashtagb = hexstring_hashval "24f318ead86b1f066588dec5d0b4aa318c6d558f9bcc72b47403ff674ac90dbb" in
      let hashlist0 = hexstring_hashval "3ab5c46f74b1fb1d7aad6dd04a45c41c7f0b7e4b5d70001b997272cbd44d6492" in
      let hashlist1 = hexstring_hashval "58a4efefe4a46c936f1f285b6b424c09164dcc790bf92077b09ec8a58066e5af" in
      let hashlist2 = hexstring_hashval "d855ace7582c9699f3d1b6004926c1e8bb47e6c441fe159b2fa6cb4f357a9ab9" in
      let pubkeyh1 = hexstring_hashval "56cd98af43fac7e5ecbf90518964421471926c1689e47e26e34425c9ecab933a" in
      let pubkeyh2 = hexstring_hashval "dfd8222cb2844e399a8f34f1961d1f7b9485a79d5e8f9babfc322bfeaefbbbfc" in
      let pubkeyh3 = hexstring_hashval "0ff6cb677e57eea35624b52cefa603b4530acda450fd4843fc9305c0f9a6f34e" in
      let g str k1 k2 =
        if not (k1 = k2) then
          begin
            Printf.fprintf oc "hashtest1 failed: %s\ncomputed: %s\nexpected: %s\n" str (hashval_hexstring k1) (hashval_hexstring k2);
            raise (Failure "hashtest1 failed")
          end
      in
      let f h = match h with Some(h) -> h | None -> raise (Failure "hashtest failed due to None") in
      g "hashint32a" (hashint32 i32a) hashint32a;
      g "hashint32b" (hashint32 i32b) hashint32b;
      g "hashint64a" (hashint64 i64a) hashint64a;
      g "hashint64b" (hashint64 i64b) hashint64b;
      g "hashpaira" (hashpair h1 h2) hashpaira;
      g "hashopair1a" (hashopair1 h1 (Some(h2))) hashopair1a;
      g "hashopair1b" (hashopair1 h1 None) hashopair1b;
      g "hashopair2a" (hashopair2 (Some(h1)) h2) hashopair2a;
      g "hashopair2b" (hashopair2 None h2) hashopair2b;
      g "hashopaira" (f (hashopair (Some(h1)) (Some(h2)))) hashopaira;
      g "hashopairb" (f (hashopair None (Some(h2)))) hashopairb;
      g "hashopairc" (f (hashopair (Some(h1)) None)) hashopairc;
      g "hashtaga" (hashtag h1 i32a) hashtaga;
      g "hashtagb" (hashtag h2 i32b) hashtagb;
      g "hashlist0" (hashlist []) hashlist0;
      g "hashlist1" (hashlist [h1]) hashlist1;
      g "hashlist2" (hashlist [h1;h2]) hashlist2;
      g "pubkeyh1" (hashpubkey pubkeyx pubkeyy) pubkeyh1;
      g "pubkeyh2" (hashpubkeyc 2 pubkeyx) pubkeyh2;
      g "pubkeyh3" (hashpubkeyc 3 pubkeyx) pubkeyh3;
      Printf.fprintf oc "hashtest1 passed\n"
    );
  ac "hashtest2" "hashtest2" "hashtest2" (* delete *)
    (fun oc al ->
      let h1 = hexstring_hashval "b453567dae66f8c30ca34aaef6d102f03fd3dd34bbfb360b7fe42ac9076a1caf" in
      let h2 = hexstring_hashval "c67e78ecf065928e65d7e158ccbac3173e49afef8f7a944c07e54acdcb63b366" in
      let i32a = 182873996l in
      let i32b = -353996916l in
      let i64a = 198270026362470L in
      let i64b = -46815743024L in
      let privkey = big_int_of_string "89781401347074584135977282480277488620815033066203126710433227224864270366267" in
      let (pubkeyx,pubkeyy) = match Secp256k1.smulp privkey Secp256k1._g with Some(x,y) -> (big_int_be256 x,big_int_be256 y) | None -> raise (Failure "bad key in hashtest1; bug in testing code") in
      let hashint32a = hexstring_hashval "d83dc15e33701927f69d4b6dd44dbbdb8eda8147d173a2ec4c2d65a8d89764b0" in
      let hashint32b = hexstring_hashval "d3c16cc50fcf17adb0dc93f1aefefb427b4073c4473380ab32833cc677c58364" in
      let hashint64a = hexstring_hashval "a72b883e966ad52b12d687e62cdda3bcae78d6c84c9e7895b0ca418cf067d160" in
      let hashint64b = hexstring_hashval "56bcc7330fe974d753e5bec947e94a65559e133f49ce6e1938e159c97649d8e2" in
      let hashpaira = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair1a = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair1b = hexstring_hashval "2b930bf9f2558f4a7a21b4c0c79507d4cb92c0deff8142de2a17e62b941984d2" in
      let hashopair2a = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopair2b = hexstring_hashval "ead4295d1c3e845f5559d6111bd2f966bcbdef3387ccedee2f9b7cfb44e13398" in
      let hashopaira = hexstring_hashval "abb166e7aa178c8180e729ea31c5660683b71b976e7329f4ae429336923bca98" in
      let hashopairb = hexstring_hashval "ead4295d1c3e845f5559d6111bd2f966bcbdef3387ccedee2f9b7cfb44e13398" in
      let hashopairc = hexstring_hashval "2b930bf9f2558f4a7a21b4c0c79507d4cb92c0deff8142de2a17e62b941984d2" in
      let hashtaga = hexstring_hashval "bdb7f8502049580fa081f253b3f8486535be3978b36714f3a79aba74b956d7b1" in
      let hashtagb = hexstring_hashval "24f318ead86b1f066588dec5d0b4aa318c6d558f9bcc72b47403ff674ac90dbb" in
      let hashlist0 = hexstring_hashval "3ab5c46f74b1fb1d7aad6dd04a45c41c7f0b7e4b5d70001b997272cbd44d6492" in
      let hashlist1 = hexstring_hashval "58a4efefe4a46c936f1f285b6b424c09164dcc790bf92077b09ec8a58066e5af" in
      let hashlist2 = hexstring_hashval "d855ace7582c9699f3d1b6004926c1e8bb47e6c441fe159b2fa6cb4f357a9ab9" in
      let pubkeyh1 = hexstring_hashval "56cd98af43fac7e5ecbf90518964421471926c1689e47e26e34425c9ecab933a" in
      let pubkeyh2 = hexstring_hashval "dfd8222cb2844e399a8f34f1961d1f7b9485a79d5e8f9babfc322bfeaefbbbfc" in
      let pubkeyh3 = hexstring_hashval "0ff6cb677e57eea35624b52cefa603b4530acda450fd4843fc9305c0f9a6f34e" in
      let g str k1 k2 =
        if not (k1 = k2) then
          begin
            Printf.fprintf oc "hashtest1 failed: %s\ncomputed: %s\nexpected: %s\n" str (hashval_hexstring k1) (hashval_hexstring k2);
            raise (Failure "hashtest1 failed")
          end
      in
      let f h = match h with Some(h) -> h | None -> raise (Failure "hashtest failed due to None") in
      let tm = Unix.gettimeofday() in
      for i = 1 to 100000 do
        g "hashint32a" (hashint32 i32a) hashint32a;
        g "hashint32b" (hashint32 i32b) hashint32b;
        g "hashint64a" (hashint64 i64a) hashint64a;
        g "hashint64b" (hashint64 i64b) hashint64b;
        g "hashpaira" (hashpair h1 h2) hashpaira;
        g "hashopair1a" (hashopair1 h1 (Some(h2))) hashopair1a;
        g "hashopair1b" (hashopair1 h1 None) hashopair1b;
        g "hashopair2a" (hashopair2 (Some(h1)) h2) hashopair2a;
        g "hashopair2b" (hashopair2 None h2) hashopair2b;
        g "hashopaira" (f (hashopair (Some(h1)) (Some(h2)))) hashopaira;
        g "hashopairb" (f (hashopair None (Some(h2)))) hashopairb;
        g "hashopairc" (f (hashopair (Some(h1)) None)) hashopairc;
        g "hashtaga" (hashtag h1 i32a) hashtaga;
        g "hashtagb" (hashtag h2 i32b) hashtagb;
        g "hashlist0" (hashlist []) hashlist0;
        g "hashlist1" (hashlist [h1]) hashlist1;
        g "hashlist2" (hashlist [h1;h2]) hashlist2;
        g "pubkeyh1" (hashpubkey pubkeyx pubkeyy) pubkeyh1;
        g "pubkeyh2" (hashpubkeyc 2 pubkeyx) pubkeyh2;
        g "pubkeyh3" (hashpubkeyc 3 pubkeyx) pubkeyh3;
     done;
     Printf.fprintf oc "hashtest2 passed %f\n" (Unix.gettimeofday() -. tm));
  ac "sha256strtest1" "sha256strtest1" "sha256strtest1" (* delete *)
    (fun oc al ->
      match al with
      | [s] ->
         Printf.printf "%s\n" (hashval_hexstring (sha256str_hashval s));
         Printf.printf "%s\n" (Be256.to_hexstring (sha256str s));
      | _ -> raise BadCommandForm);
  ac "sha256dstrtest1" "sha256dstrtest1" "sha256dstrtest1" (* delete *)
    (fun oc al ->
      match al with
      | [s] ->
         Printf.printf "%s\n" (hashval_hexstring (sha256dstr_hashval s));
         Printf.printf "%s\n" (Be256.to_hexstring (sha256dstr s));
         Printf.printf "These should be the same. If they're not, something needs to be fixed or use the old sha256dstr.\n";
      | _ -> raise BadCommandForm);
  ac "secp256k1test" "secp256k1test" "secp256k1test" (* delete *)
    (fun oc al ->
      let dl =
        [
         (big_int_of_string "10996098274289172793485020970266713297297319068003711194195298624898156042634",(let (_,xs) = pfgaddrstr_addr "PrGmkcV2gRskATkBdcjJb7QBngsmQqwN5eU" in xs),big_int_of_string "4534256599487250898182114811024986386561920126591604118458116105563197004996",big_int_of_string "98845362050093233615298952818311615880116154137484472252860897670923573217724",1,true);
         (big_int_of_string "101650753039202594837866637839394616736407413322427547802984490283915864348181",(let (_,xs) = pfgaddrstr_addr "Pr8RmLKwowv73hpJb6t7MNTcs9EYbp5F59H" in xs),big_int_of_string "7471028006810276087710429534676827306977078745675273629535560497710904192476",big_int_of_string "115209813530060012472736523293473049103403781870335361741591613424975277677345",1,true);
         (big_int_of_string "66010286458814147841851472620230565323088309274126662439853918254742851540497",(let (_,xs) = pfgaddrstr_addr "PrJBNT3pAEVrHuWWvkdzFTnPWuTgGoYtgnq" in xs),big_int_of_string "20398620936312213130615503809061454867673194851759207649574151044191393143259",big_int_of_string "79618108274953013806829987516299650100873464119808997376459306527369909583441",0,true);
         (big_int_of_string "47534948027168146391442638719193645635181450165017920345438046301380207915706",(let (_,xs) = pfgaddrstr_addr "PrFzFuH391ykHqDyJ2o2Pp5YFJAxtqG8arA" in xs),big_int_of_string "99521125475799576326432090986443202663320542030043266746660707739174650912012",big_int_of_string "61087948247784281327126829832312646405907597736877355964936693745130214946357",1,true);
         (big_int_of_string "75061917695687790007707566800550714141458513938909318847892164225743550846321",(let (_,xs) = pfgaddrstr_addr "PrFGN1bQM22qCwaHB3NTeQqbjE5mUPKbCDG" in xs),big_int_of_string "46018273577275729293280938537418337623893450502641114276873197288663115652382",big_int_of_string "9235760579841229867028390638635911540561238498815103671611871731966908144205",0,true);
         (big_int_of_string "60121394118949338863307677667750400555787471991961787719748305436763117292143",(let (_,xs) = pfgaddrstr_addr "Pr5E9idJPqbhm7SWy8SeGpFspN7LAfSTjGe" in xs),big_int_of_string "1378038247406434333600332295090076766994379371641775531971315051530734440966",big_int_of_string "69749169916764602599240549014708964446824640301351223152614209332296199406206",0,true);
         (big_int_of_string "63789987131945229711210101567447021734290830206612116990379178032398010475379",(let (_,xs) = pfgaddrstr_addr "PrKkTswYu3Aiyrqw41un1uQEab8MXFqH4YB" in xs),big_int_of_string "27900487517584586924899192034961114468601392408795427816923057876606940531094",big_int_of_string "27484693000218434764501824925046857814511907054088508864887150556177807563959",0,true);
         (big_int_of_string "41289779462723365788356909287112394481379648710384553107270833774778055711446",(let (_,xs) = pfgaddrstr_addr "PrH7MgjbAof4Xymhm2stNmadXarnpz1iGsH" in xs),big_int_of_string "94029533423118343936361791170265451906453283080220155549494188319429730753400",big_int_of_string "94236895318190745731067332776720037118041247029902594867685816285516855374094",1,true);
         (big_int_of_string "19847955673544500464094946741152587493004983754441373362048675327438124128488",(let (_,xs) = pfgaddrstr_addr "Pr67PmkkZZkwkW98vaE3oTcNh6KBedKozQ2" in xs),big_int_of_string "109433573825611876315603271096214429598871035032810120337788580986209550320955",big_int_of_string "71135416170399387014222781664260379313753259817643953878663579119130472397459",0,true);
         (big_int_of_string "25305202939638304149069225536543780570969209861295990505612245731826997008912",(let (_,xs) = pfgaddrstr_addr "Pr6Xc7YKYsrgxCcxH9ZY5yfwAFqSqSeVdPS" in xs),big_int_of_string "58079211964873713641962132874369906683684204708294977505385731449313905283744",big_int_of_string "32213606313858655021479846935800071569074176756590293929699586542737149324014",1,true);
         (big_int_of_string "92972553636840715862486694393539507752117474719597058009509301431567341935579",(let (_,xs) = pfgaddrstr_addr "PrS8yZFzqkfzQudMLvQ382X3Pv1oLC4ShHV" in xs),big_int_of_string "66142331100938615971006492415163472896806884627158325561348299580482653330028",big_int_of_string "46774671390257987946381069788860977693290941577152290928504295986171657085001",0,true);
         (big_int_of_string "113239996453934158828842334058313547010027557086883997430454663383336750077412",(let (_,xs) = pfgaddrstr_addr "PrEWaN97FWi6ssXaqoJGQKA6X3AQ4DqtyrE" in xs),big_int_of_string "71149416781784799230882753541512287913698796238854270820788169342850460130552",big_int_of_string "34220045331449394473453892605635422810135732819477420278682276837513522323081",1,true);
         (big_int_of_string "48198222108486518347625732276821861253677326766794562362928796118302753537596",(let (_,xs) = pfgaddrstr_addr "PrBmwYHAWESYuEkPxwTk4YXRDcDHgetnJrQ" in xs),big_int_of_string "19335122235907335594758224980922493316843342559327974299526789753003875510536",big_int_of_string "101073259421136418977926110877821005412782524397307592624211410234089725507387",0,true);
         (big_int_of_string "82877683694856544704959693161537853781693262487859232086266352021799659457491",(let (_,xs) = pfgaddrstr_addr "PrARQSPRzTVJYUi6H5vYezHA5RbdfTrwJKy" in xs),big_int_of_string "78543669407143030611862101178158110710347487922879896680081531550714930703886",big_int_of_string "40367742530813553610887228671738168801328048322184858109515162916049631204712",1,true);
         (big_int_of_string "32798489811387826588638836291863177609881847678706006063180805833338766733713",(let (_,xs) = pfgaddrstr_addr "PrEeJarsGr1fr1bMoc6GYLQpjYRvbYN6auB" in xs),big_int_of_string "80168240492266867690639751594111314299753305967675155410593354645462294346350",big_int_of_string "55922900511472123094582501857648335183637036321451200761058071835370451107560",0,true);
         (big_int_of_string "52276180242907196400170853020087035546683335819675534339107454334092293710652",(let (_,xs) = pfgaddrstr_addr "PrERYjdktucYL9gSQrmrY9eZPbA16cp5hkr" in xs),big_int_of_string "72267856432650445753555052891511829937593432746060710545267765695283615982465",big_int_of_string "10949348582575951051328184136671561016984354034144303479091562385095071220727",1,true);
         (big_int_of_string "76530419955223877577412609958986752514619339509304933093759643358119316748593",(let (_,xs) = pfgaddrstr_addr "PrH7MgjbAof4Xymhm2stNmadXarnpz1iGsH" in xs),big_int_of_string "5006793447044568203062266992239022340389252248587511404333592551149410654928",big_int_of_string "17582496309325443663641348286336620720717325529102250980415814645334132405142",1,true);
         (big_int_of_string "7573638023810218272674786629282792701776460665276830086780702757644809879905",(let (_,xs) = pfgaddrstr_addr "PrG1WmkNPkHTWVXQJnEv2oZKaQp6L4DZu1N" in xs),big_int_of_string "91511212018358143175784780440029752619493420418095293813689962602098166774784",big_int_of_string "78720459546869811761379148888212926632391231603812472031589820785524138107281",0,true);
         (big_int_of_string "12189848152540438877058091823390025896070009516840506993034086410378410281744",(let (_,xs) = pfgaddrstr_addr "PrEjBa27AHzbR246jAumWSv9qkUdEw81hfP" in xs),big_int_of_string "26946325538212973943401176593232141736777600958072501489774426703335148322644",big_int_of_string "15772439186133678206951624305341891998166267081552841516482233662907523118263",0,true);
         (big_int_of_string "20752260874786110299684911345429407094863014478505077309779216014992967916598",(let (_,xs) = pfgaddrstr_addr "Pr3f4ZsqZWargfJshe9kku5NZNTbt7APEGB" in xs),big_int_of_string "108041075086777981288792369608307887935167439222621372954008229596225808033519",big_int_of_string "49015085701020781326422627537508488946610033829294971954033380346079254455509",1,true);
         (big_int_of_string "96000586103627214836233956315710984210135220333152222576908151412467123808564",(let (_,xs) = pfgaddrstr_addr "Pr4N2SUvyXhgFMZxfx7spm8dzPnLQJh5EEa" in xs),big_int_of_string "34344932004443760037020979690426791879829128437479911522865651827098779509364",big_int_of_string "99831840136339179792498117527662308034110375238043990859455405986107349510573",1,true);
         (big_int_of_string "59883686873623213581475495873008605942002618950993492639586382481632740107509",(let (_,xs) = pfgaddrstr_addr "PrLNBxofAEFqAqUro8FfTWagBdDettHjLHE" in xs),big_int_of_string "106059801344243303608001870808473142012929800961572277684774577881908009679751",big_int_of_string "20102757377998600354295940065956458852854189273121861065657901064609508142499",1,true);
         (big_int_of_string "84701216393852469407069392795030273363103177069419227943651393811773125817086",(let (_,xs) = pfgaddrstr_addr "PrLstDumFMHTPCNmWL9HvaVnmzRAtSUdhrP" in xs),big_int_of_string "100921603658116900868315302522027681143828746750171959043916556631622022594298",big_int_of_string "109431618242647805586344512704119196975094731126863132761013000757549970874884",0,true);
         (big_int_of_string "9887319513540848766663660636636099081355734828240213727072396360297778324994",(let (_,xs) = pfgaddrstr_addr "PrQWZh2DkFxDz1EaJ8dSv5udrYeeksU2H3J" in xs),big_int_of_string "75752445557647430129348537287725952566306723062460157510869978397496292249552",big_int_of_string "44876649273271386452068036123428951923617276971764439572702317765165459362286",1,true);
         (big_int_of_string "89806148705814001232543131183776877822836794453978599767677803107094032268759",(let (_,xs) = pfgaddrstr_addr "PrQpLGYc1baZxQsd5mUK4BLSkVAswkvtRrR" in xs),big_int_of_string "73824834788189785294373651207322215445804298771440226371035827605617775907913",big_int_of_string "104497535262314558180616917288045781019382160034813799586663003356089430177079",0,true);
         (big_int_of_string "108739905067322131010277789729371826403706335121959807348457643011046019970123",(let (_,xs) = pfgaddrstr_addr "Pr4JHVSYtXHnDTaxv8mtHAviPKhQKKQ4Fa4" in xs),big_int_of_string "83298912644187275813257846319462908606542157529398920642428315769694761892889",big_int_of_string "24905146657043690502407400478971182064467076059422819577486297189157989596083",0,true);
         (big_int_of_string "65690190431747589939264351004405503427714867824942773574335834962698944731284",(let (_,xs) = pfgaddrstr_addr "Pr9w75NdX5BwQnCi6Po5YoR1ghwW5fFkmaP" in xs),big_int_of_string "29221566128170116899542605602354534513007958521957448231765442577929748387849",big_int_of_string "51341188634658817338334933173702151119438424384468831366341810754328644295",1,true);
         (big_int_of_string "30858726992337497953361073803469993229918238302477483724189367944267135531760",(let (_,xs) = pfgaddrstr_addr "PrNq3cKzRJ51rJTkVpQ2VWcbTtCQFLKXdqu" in xs),big_int_of_string "40131154711417255805816111760618561121073052443826581925679365705835987423167",big_int_of_string "74981215935020290099235465942779633855763180157541890777464243851296956049579",1,true);
         (big_int_of_string "41924584126538543781518899355642083360906545508086144592001406262949749463406",(let (_,xs) = pfgaddrstr_addr "PrNy97NFQWpDe8sE3R3kQTKf5i4j3n6juQi" in xs),big_int_of_string "110639390709509051399239240855130308172067605275964657953667583611092822205710",big_int_of_string "93354390444430283912458161759116308582642541201930600011467045461433812785497",1,true);
         (big_int_of_string "39447355588614185097918778005341035958742585124641852725152402741445805379271",(let (_,xs) = pfgaddrstr_addr "PrJGbczqewN36zxG9V6wdFWq3mYeu3ffrEt" in xs),big_int_of_string "40082219382823145940970880832711753325421715795700361684467118658635007689780",big_int_of_string "68902854903195865847367523517061424720608618674466352929236444263450741661705",0,true);
         (big_int_of_string "27572962953812693100425625103949268116025703424621821776540278700473638331104",(let (_,xs) = pfgaddrstr_addr "Pr68JukivXhTTeqX9Z8tpt73iQ684CcYTB7" in xs),big_int_of_string "47987984182844642273800539153418547732858856623002740242827689996020364568401",big_int_of_string "98119986933243859258500698853656629493078320570929219365295540030259163337535",1,true);
         (big_int_of_string "7815226372214775161667726331966826983766632370569485333526318292276235514614",(let (_,xs) = pfgaddrstr_addr "PrEhJkwQykPavVmXiaH4vuXT5qHgzsMNzxj" in xs),big_int_of_string "67770389265310601703170279482429415010947811413818794731264123466573583392508",big_int_of_string "78105326533564113473802265127935995106954157662565054582247436989367928442163",1,true);
         (big_int_of_string "4359764362092116380769374955425443034935102287846134199422084829313283960094",(let (_,xs) = pfgaddrstr_addr "PrEyDEQiRGHr3J6YT9vwgs2RAoLHWnXwbYJ" in xs),big_int_of_string "6603631810137614447049416445005675553555349877714251936098471929859858264348",big_int_of_string "87923832867942603133869782981278406752675099696999525832543364629760629372360",1,true);
         (big_int_of_string "99937275466029631854748747631300137989826953500659204439234460755281127199966",(let (_,xs) = pfgaddrstr_addr "PrAoFWcuPaxrfvqPpmFg4zxoKi3x63D2GhH" in xs),big_int_of_string "47298743550555019094594475513360064157001572549786912417412958914033765630170",big_int_of_string "86756344582125598303470918191732509456012262222397841463139516695623639560172",1,true);
         (big_int_of_string "65328403200719866316586480018027456256941079196993414049976165305836865097420",(let (_,xs) = pfgaddrstr_addr "PrJ8ufsxH5Wa8kG3dXheaf3kYgQt5Dj7ihQ" in xs),big_int_of_string "9815535090469394871897474916259924410933696600136285966838034536387704163568",big_int_of_string "13437479145511145876623963049306510256126712404986032597275754999470354551086",1,true);
         (big_int_of_string "86175817799617817530346643778271501425349994169058725634608076576974925623786",(let (_,xs) = pfgaddrstr_addr "Pr8WZEWHb5FuFfiDP6sALrNX4kJeomMYYQk" in xs),big_int_of_string "32612174543054371390980101180969965515490668502438452588909183719867014250104",big_int_of_string "74491028698366479565382522490845907124618213612174330286825001766195975816875",1,true);
         (big_int_of_string "38058687407308628893995093301486145264447840530864357569753327009823986482811",(let (_,xs) = pfgaddrstr_addr "PrM1MoYY8ZheMF6ge3s6hnV77Fij1BNvk4t" in xs),big_int_of_string "94014162489193190635752835383151119781627885173021520847004264113474140371493",big_int_of_string "31518398306744151962737822762352532205520949423978112001570082826553195843084",1,true);
         (big_int_of_string "25280761480094319889067917233648894977820929927635682489500715339628593497188",(let (_,xs) = pfgaddrstr_addr "PrDTmn4d7zJCUcaHyAfabs9VKp48UUyd6BP" in xs),big_int_of_string "20577158807262376094601206603368533008992498738510040062362111252843526821650",big_int_of_string "56445797547210113783025216919964231175020218634523092956133387313741496189746",1,true);
         (big_int_of_string "9247122322053168064115522057507580444650325157487790921278129303182799047266",(let (_,xs) = pfgaddrstr_addr "Pr5T8z6LUt7dm8i9hZ6D9Vsw7tAoFHe6yoA" in xs),big_int_of_string "64578234626105067569917753440754088299313483071921451896562968246873069071945",big_int_of_string "65170087928577586805435786654410890945062944066541428339774331964381905686937",1,true);
         (big_int_of_string "73116313727210978159391700922618185450613280756282193021718754324015265647637",(let (_,xs) = pfgaddrstr_addr "PrDAkQUmY7vjXwMooaNGF2MGZAVeReV9GDj" in xs),big_int_of_string "79925533193972493563807430934062553286069361998825144033692337255522859016503",big_int_of_string "61096172095369323165748625628934519126329334565089456028696691515012753187277",0,true);
         (big_int_of_string "94205221859279687083865134999193810142400701216245823237831601316989510392459",(let (_,xs) = pfgaddrstr_addr "PrJMjVF8vQjyeuCqi8TS5LaEbA1fg5jgozj" in xs),big_int_of_string "100409299502942454966935695192320712046500050994515495917171689026367914180791",big_int_of_string "32007767130562050391665783821792081849285016049213134506401141061540743776819",1,true);
         (big_int_of_string "104912362459669265231815481902681768684714737563103831069981931228982351903571",(let (_,xs) = pfgaddrstr_addr "PrBzmJT1kqNhHbkoSSxh3w54t3HxUyd5Ssp" in xs),big_int_of_string "105346394936956832915050715735934449341541804956254035378425262884599779008345",big_int_of_string "104570334745223537142146915451805194956746850699716195954704967457464229198833",1,true);
         (big_int_of_string "33238624408048012283296394817083233040687012767381324006387774649447625647728",(let (_,xs) = pfgaddrstr_addr "PrARXjGjMGoshcw8E9ENjjftTDei1AatrJk" in xs),big_int_of_string "11211179299764158668167448669425924424153183242965318351197790968910446313861",big_int_of_string "113469705043202878114578555327954633009939230539782442984031912422042583521125",0,true);
         (big_int_of_string "50657249951605788032721012319148168181859569225738556171508178944723849296806",(let (_,xs) = pfgaddrstr_addr "PrHfm1k8t142mYzG2PpSd7CB1W6vBEqFkgK" in xs),big_int_of_string "48357902367850172866952437826158621761708772030865100496458246330298061418868",big_int_of_string "15388916386276923830399982096866048035188519874691744541615290003405928662849",0,true);
         (big_int_of_string "70384376201214548341084800392382475950601634739397614078677700501155328855188",(let (_,xs) = pfgaddrstr_addr "Pr3tAR8UNSpoUYwRQkweKy495i2mchQD4eP" in xs),big_int_of_string "64030788599332377000393319677867766924046001578908242237488752302409348844235",big_int_of_string "98263109038247906466508720906518077923178983950299768144053620740567369541456",1,true);
         (big_int_of_string "21642367931055711665788434640098496565725357063445322470608433448214506355302",(let (_,xs) = pfgaddrstr_addr "PrBfJQbiobm7nVYYnXuPM5AipjMtDewpBH1" in xs),big_int_of_string "95826346487509847143922125279192268319792948230168625602084248601093838010785",big_int_of_string "93686996690306353832068614378848241767800957153298310125676572813763592704318",0,true);
         (big_int_of_string "106912129425121550967343367449247606116171929069360801847482384055950623622387",(let (_,xs) = pfgaddrstr_addr "PrEMicZgM4WvRicRBjVAVD1V8cZdTEn55GZ" in xs),big_int_of_string "22071787206055064635760110656138132691193066678876947080219224374333790469143",big_int_of_string "60900782318364570351783929034757429854182740200264616215684431674614694718723",1,true);
         (big_int_of_string "56511762133768519194482147781924159077796652839663070820556282262726186120041",(let (_,xs) = pfgaddrstr_addr "PrNvAjJrumPJJ9YC3d4EnHx3A4khZmm7X9v" in xs),big_int_of_string "31048352363553627676739621160087865265581316320459318130945229639392811509415",big_int_of_string "60902457677530533440242122910268986406500595284695332580125957967814039352694",0,true);
         (big_int_of_string "51703268200107284939059026647614254004513844097915227853054177562506935773059",(let (_,xs) = pfgaddrstr_addr "Pr3v3nvLjFDLnnhYQ8K3aN29nhV6fWCh8ej" in xs),big_int_of_string "81650508821186590030136926401890560373765977341544988370362952846498466439137",big_int_of_string "103311950440846513130951785872844963257300135880513718687165699278260622331846",0,true);
         (big_int_of_string "77470445760292499874443428853787723374202647402715904392002351831276727503406",(let (_,xs) = pfgaddrstr_addr "Pr5tuWNs9xE7jhhCZThg2P5pksFxGV5fQY1" in xs),big_int_of_string "38361018904992422678255879368436405761909111057806688046231980258374108697293",big_int_of_string "47518985787036251279333697143209040364695611214779105286491310602330898020074",1,true);
         (big_int_of_string "46143926136606841249633397618327265244493429793169583280276206674507799198459",(let (_,xs) = pfgaddrstr_addr "PrLCWCcQ6DYgRd2nQSaAc43FURn69e9tA8x" in xs),big_int_of_string "51265027116188306103439313347373945451897905625133786736490283167939271705557",big_int_of_string "43075958560697134490106226982989888438992791556065412419949191188857092445252",0,true);
         (big_int_of_string "43090157220130762104607573997133126064427599683760667494680219040001595119293",(let (_,xs) = pfgaddrstr_addr "PrDA4m5X9kvpjpCbQiKk9t1DcERcW79QGor" in xs),big_int_of_string "80415461246811507675443346045708024059831305697076984577637753358677038804258",big_int_of_string "110277849284370114491201150508976295349041877089695928510996561735077698155440",0,true);
         (big_int_of_string "111461911527193497948149122417389037661930669761669477016730927095980349050187",(let (_,xs) = pfgaddrstr_addr "Pr9nF7S34ZWK3U5Ztwe75TWjcSz7qEWw7H4" in xs),big_int_of_string "51634922689234155051112456750891998760955243696164786365741363373568404106792",big_int_of_string "23367173317187610859603783838375785828254483645130495992781144769892638721727",1,true);
         (big_int_of_string "103771735850939590581691146369923898648830421368967176212898810215294417525106",(let (_,xs) = pfgaddrstr_addr "Pr9bWmnG66XTWEAQckm5X5sm9AiZ7LDPGqo" in xs),big_int_of_string "42729682964400008832726659783402619028593843209874548628903828680067740709758",big_int_of_string "6499415169810329893770556219199776855899639262057602543058481821080304672723",0,true);
         (big_int_of_string "49163530351917716333794600024853635498061048339903193957915703611898711476213",(let (_,xs) = pfgaddrstr_addr "PrLWrxFW35nhYsPnSvNJUUsabHo6NSvXKMT" in xs),big_int_of_string "62739116548912957333567384875687427399459381929953689755796463829611211247847",big_int_of_string "99737122815859318965833907912231495821176414823908825326202860102768370261503",1,true);
         (big_int_of_string "20112006784029092810704093468210120784653327412631693300845211120178836270918",(let (_,xs) = pfgaddrstr_addr "PrJsszUUXvzeASfkot3mXmVZGcAUD9G5xCJ" in xs),big_int_of_string "92909462685353008996386569822802210506028646093872439393134409191259954591039",big_int_of_string "101786347413167816420124303332357485741630016375306228075184225711967562666380",1,true);
         (big_int_of_string "2458817202123774689058335445957143007896921052517788976591965985842594088400",(let (_,xs) = pfgaddrstr_addr "PrHra58UK47ijwBe79romjckixoskyjdyxH" in xs),big_int_of_string "80715583153428731742875477321262867202394879048588333353789644458815113845387",big_int_of_string "90750925758778367338676991180723636818107197187121392398283740998100875505596",1,true);
         (big_int_of_string "89104253142963455133193867868298571851745316488419498192886329514822004124346",(let (_,xs) = pfgaddrstr_addr "PrB1QBjVC4CvpfeUxnHZbSAwNVUNrebm8UY" in xs),big_int_of_string "68768706839230590032067949752223773400151479422199376280906900291035781887414",big_int_of_string "35120714282285683728692722237692033090398975736967370257426904780192598963704",1,true);
         (big_int_of_string "47284201726200199586438710314740543560801968278905081204744269827456659633218",(let (_,xs) = pfgaddrstr_addr "PrEqZmHxvRNGQ1ZnJc7yZ5dJBqAj5FSGYMu" in xs),big_int_of_string "10280363345430762337812631495972830943516008667739069140197997246988177162439",big_int_of_string "95611683814497844898775120954752831047843101033029042966661007352124046132817",1,true);
         (big_int_of_string "107842549982600384329285908160415363364996580592517125745975678813628222635046",(let (_,xs) = pfgaddrstr_addr "PrHhSDJB2jN41n3naHk1C5s5crRTxF4f5ws" in xs),big_int_of_string "99912099794972502416778894245170771595094627254238421488755000554398704775359",big_int_of_string "3125682374517529581375043661702681473289111718390902756089300147287113299906",0,false);
         (big_int_of_string "10555872557329183003643650335424420523194664157711231631263873799519723727789",(let (_,xs) = pfgaddrstr_addr "PrR6yhSEKCewTS48NFyVMcPdcouodccNxq1" in xs),big_int_of_string "59193434489575029285582901897901157544922931161346818382797733935098911580509",big_int_of_string "103330586760487635207218018847534300337271675961178153228520857930955192238869",0,true);
         (big_int_of_string "39010772735660229489992452756459528447682759143092761080852421957412798955430",(let (_,xs) = pfgaddrstr_addr "Pr7yxbGC9N9sFfDxKyXNQ7XWgWgUpH34zWz" in xs),big_int_of_string "110378063603343639076512499374103644473125247522401993267716106475311641842981",big_int_of_string "224317586784266055257056733270013123967965401009542647186583764193274696593",0,true);
         (big_int_of_string "13679698320303378268072346286098516753915487162571426573935807717616003726549",(let (_,xs) = pfgaddrstr_addr "Pr6ZsQEhukAsgYoV6GeLHYwZehYuJNgNkTy" in xs),big_int_of_string "64778372786934258486509049177585368064814542867301452733445590566230236100753",big_int_of_string "78059496042014676555499881556498223283542733850702815491424279320261243151514",1,true);
         (big_int_of_string "97012678441064093277292170332589375313159821949015974959682007282304922754203",(let (_,xs) = pfgaddrstr_addr "PrRt7VJuNm7zG7P1usCMpGNW6NFN9DqYCh9" in xs),big_int_of_string "26463887923441753840175865286929386743440282883406222206944376521838218464336",big_int_of_string "42571386599126560714831228386995807801083637384071978388214090772562480709275",0,true);
         (big_int_of_string "24794880397165966903012902156070955498348256007048544615558702589667298730941",(let (_,xs) = pfgaddrstr_addr "PrKbASYVwpRzfvMEgdEWqBHGZE6GL1MPCr7" in xs),big_int_of_string "88077385120443581242093269169228143897499586552373759268848017581960782243708",big_int_of_string "92546149858400602963393821904440908340885414236689885352121319519135317955837",1,true);
         (big_int_of_string "107852570354125729033611253562884397944364416347949879852944173180846299895476",(let (_,xs) = pfgaddrstr_addr "PrRs4BHe8ruz1h6JiNBPX9Hjetf2q5zztH9" in xs),big_int_of_string "55207444055840490797370729530998989639114643341640521548342523164384542694513",big_int_of_string "40698536193550604900987406742679061710876564923936288706634558501530969545300",0,true);
         (big_int_of_string "38074531946422695156651023129521409413103546867505970766004627758340608835507",(let (_,xs) = pfgaddrstr_addr "Pr8muno28zq9xEGdZ1auNvLn7o6XUPnc1ov" in xs),big_int_of_string "75483111323166292656143763072604394593414814852521587771401488974986128557807",big_int_of_string "75522279013730846893264761861279590545688999867609485829361052658770198850599",0,true);
         (big_int_of_string "78399766552727053237801338674647504715304604674855686557081565256306647797511",(let (_,xs) = pfgaddrstr_addr "PrJ4fFFFWXe2xVEyZiZWarDVhnqMLUj68et" in xs),big_int_of_string "59825710768703321907063206293735448198380386446458847454873022430431649670263",big_int_of_string "11932559103886652585407096189406810770408981616316909547512193085215435082204",1,true);
         (big_int_of_string "54324761074855063599801597060510956379987128115676013454788410632416022097979",(let (_,xs) = pfgaddrstr_addr "Pr5oiTAkhFrbqmHjBVVg2WrzDgKgG2xjZ6K" in xs),big_int_of_string "99935059450479061365763934663535887461854694291702767281579223044614771764497",big_int_of_string "4760948996590996811855962836856466466407641528100086499639656550038523176909",0,true);
         (big_int_of_string "54187097806912609914966567793066684936615128044763319156278940385307195595529",(let (_,xs) = pfgaddrstr_addr "PrGFuuqmq1ocRJ164G1GHMdwSvR5P3z3tzj" in xs),big_int_of_string "50455416797702096866222350076799012450690198328842345898297347646076073511985",big_int_of_string "50634110668016570664178973320389076786140069732316868282073354122220805320575",1,true);
         (big_int_of_string "84265676530432744400104443175353507763808938655182300189729766103893098808763",(let (_,xs) = pfgaddrstr_addr "PrPjoAVZxdUXm2vd7HKBYs6RNVzoVqWXpTL" in xs),big_int_of_string "34610709983547076288254656118999376165401129947156092741694171549863880369516",big_int_of_string "16483557474493964481862120059097185106175682319986233720741877920872807359445",0,true);
         (big_int_of_string "112240629029225632964303433821770732700232946928114168606721150551041191575715",(let (_,xs) = pfgaddrstr_addr "Pr5kuRPCHmXtWdALjUCVQvqZyxtS5AB4jE7" in xs),big_int_of_string "104203657449964756773107041502326117732388151522932310008592187220160886222664",big_int_of_string "86071402663119974283058415602996257584858120789619785038876934401719693312520",0,true);
         (big_int_of_string "88010163644202579399608381923726977042675061553563904356288737729811802896498",(let (_,xs) = pfgaddrstr_addr "PrR41gavcaEVSJSTGiJcAz2LdJ5xuzkJiED" in xs),big_int_of_string "96486527022722359373717435376445662327747145885393162521608932750493955888674",big_int_of_string "88729452128427207104337807453761983632510279823649268747713187289866417751073",0,true);
         (big_int_of_string "9375340658027427262403902166459742407027501239775280230352213292342367580445",(let (_,xs) = pfgaddrstr_addr "PrBFo679JUTu32BoprZsRZ4VYSuFqPpfxH6" in xs),big_int_of_string "103149477303001057826616991520396617068840753486571828988671648849144404708304",big_int_of_string "107039605028699784521542451210884245314541464974651630520194190778380290935686",0,true);
         (big_int_of_string "17935009338869252632479324209890451094451887662800293750581131751594546944981",(let (_,xs) = pfgaddrstr_addr "PrRbGVcTDcmPhskv4oTUrJeXMvMV2hQ29Nh" in xs),big_int_of_string "111858531142688835912606186341173505017452674638075976169504768725562225565010",big_int_of_string "78462453671662201159826908875017322003529937231277661025124320819144061263198",0,true);
         (big_int_of_string "107743741938075273535041526987013950987556238878818087273869164134667228414516",(let (_,xs) = pfgaddrstr_addr "Pr9w8MdZZ9J2wPozZDXWjKMFux6Wa8VmLrf" in xs),big_int_of_string "50689012367280670203480434659698656986023926709147999934585932616881889273754",big_int_of_string "22166617649890011031226208550705023615724870144651473960378887349004168741579",0,true);
         (big_int_of_string "104186005169946727999324391402996334571944060085145125268051350701314234481012",(let (_,xs) = pfgaddrstr_addr "Pr38XKYSRaXsbLM48ZAjkzYcKbHCzyNjBTQ" in xs),big_int_of_string "48623328124962736399257587087429076648497981476209261870534152326902869556226",big_int_of_string "37221549397822225987896384909420244555385854729618583525689233102953826740609",1,true);
         (big_int_of_string "64013938347325317753869606768253051590323441698656506928368620764260165159136",(let (_,xs) = pfgaddrstr_addr "PrCz4Ss1ofYEfAv3w2eV79zHVtXpJznZ67Y" in xs),big_int_of_string "29390566929462747746841254594274612930079081150105884706845887981753782878594",big_int_of_string "24185963932870683003523945955133450456881092997831553425391119741286044555732",1,true);
         (big_int_of_string "91450789641080308467874391078721872792852753159706390022980229179623126132318",(let (_,xs) = pfgaddrstr_addr "PrN5sasvMneGffwg1F6TzbtoA2AshLyLi9g" in xs),big_int_of_string "56763834216060708714600904081092005335738523719515120043488733118861475442244",big_int_of_string "6418928900403766659859165181884064872219758082426641710458492834311478072860",0,true);
         (big_int_of_string "21753180883382750592750460528052493955531472690025665102149704146070795179924",(let (_,xs) = pfgaddrstr_addr "PrAmWhiTLDQkQ9fwkKCmkyRmRtFN4NYQbtH" in xs),big_int_of_string "103618308688145545639798901028097165387500276741594932349297690295164592034128",big_int_of_string "31124164376388350224827163777881384319069015745763648995708976205855378915091",0,true);
         (big_int_of_string "47546546749621398904638859651073037044178001750476129465189161857897540739214",(let (_,xs) = pfgaddrstr_addr "PrBe9tei5JUd6s2Gmg5Z5s6PQnAWdDTu4Mc" in xs),big_int_of_string "40043670331734130963546159713758097890948821707036883607947448163001736686389",big_int_of_string "55812024956389683764553844376036186388001216869028989296193651244166311804174",1,true);
         (big_int_of_string "58956648700103560990419294008993058339707503148922761656732652679191785541078",(let (_,xs) = pfgaddrstr_addr "PrSDDSESZryjumdxiBAo5EptBKvFMd7DhzL" in xs),big_int_of_string "77350088095221339417991740770368795332950832030470502598099978325202979804799",big_int_of_string "46710220215585475197964103281431792507724990366391344790734567969385023683821",0,true);
         (big_int_of_string "95902527160610183476576603503618103538023940834605334561123104768769287086020",(let (_,xs) = pfgaddrstr_addr "PrMq6gBzJYrHXspqJWJBqdw8u9YUtwDNwKZ" in xs),big_int_of_string "88900335761832455089817379720669093342149467571816817627406177519690283580858",big_int_of_string "98806261098122432948364518118909554435663286549328953316162058996459419802960",1,true);
         (big_int_of_string "80816045129401180139381484617261195475221784176569358632467177923720730789532",(let (_,xs) = pfgaddrstr_addr "Pr8eF3MRg7B7MGt6d5fzb1Eo6QRcAQeA5gf" in xs),big_int_of_string "41853991522070641254754218712837439587373841830578561292466662107957987657643",big_int_of_string "114046194585943110459189023690698175772053609555158670663318701648611611770693",1,true);
         (big_int_of_string "58043794887844283431220697186749957412494591326211150285192181791285627582888",(let (_,xs) = pfgaddrstr_addr "PrSFN4syfmLGd1RdNwhoyE2yH5EKD17roRq" in xs),big_int_of_string "18556182671655670689666277288724306931864826747545805411113881113914026485248",big_int_of_string "68856617413946497515758455292156220357605778972044643858427398168669768007435",0,true);
         (big_int_of_string "51476200128190389580376289843663996818326147712663728752788412179863059223776",(let (_,xs) = pfgaddrstr_addr "Pr7TN58p65ke2jVidHHw6gEeHspyZuB4UxM" in xs),big_int_of_string "78360330379748931502140534735932520670264349888165970995513049936256263786937",big_int_of_string "89192332264347334125095324272901230965308829986786909673704580786691702804983",1,true);
         (big_int_of_string "87729800213250060665771778642734829798016300685375749331096895536172183240153",(let (_,xs) = pfgaddrstr_addr "PrG4K8rB7zsmSMX4eqojvKFHYxHvnd8ayNt" in xs),big_int_of_string "31213893269525330899376851919616378973794937762781160321688127517404426802729",big_int_of_string "45301539357558636746991223088423397271618268344138157506350800444519584378956",1,true);
         (big_int_of_string "86310865129983332352455157388552217315770905593556507328962839730437227083952",(let (_,xs) = pfgaddrstr_addr "Pr9psV7KZZFNS2FcwwdD2WpcTqygpMiYAAM" in xs),big_int_of_string "115740789725634976503109628050067786884863016511093297701806545010376977202871",big_int_of_string "20262197932014157145029550010779574622845511690816536522932890260455633911624",0,true);
         (big_int_of_string "9418939514493617425161517931229021543728845657286926820350059915350526791645",(let (_,xs) = pfgaddrstr_addr "PrS5oU8EaEMUzyFPpBSTUENbFjExT4F947d" in xs),big_int_of_string "70588736301912308747988560585407371081580256503451495386009999159715629805896",big_int_of_string "65330920928895553604026723584007649126980787903703559504338208063253841078078",0,true);
         (big_int_of_string "94252119166872917111985140614348925064030458743088338169801062315254622411795",(let (_,xs) = pfgaddrstr_addr "PrRgLfYPa1CtDy8jB4tajfuyvGiUJAAgdcr" in xs),big_int_of_string "54720509606231009589609950766055275769326964804135849952313179105174964932467",big_int_of_string "16904252253066820648392650995233400140669945027458638532935055203574418843456",1,true);
         (big_int_of_string "2945572391104910051000878029563369956566455045792857895193082466082156586626",(let (_,xs) = pfgaddrstr_addr "PrP4p2UuthLmDGzEiuCctSYugPBAFiXLFK7" in xs),big_int_of_string "25846827075808437391520774916090464036121147755706229039604519734773986781480",big_int_of_string "64384291056209229301716042311830581725256936148920504120393061322257403347903",1,true);
         (big_int_of_string "13248701382719574572460908154684189881504335908459165690216949468157983064233",(let (_,xs) = pfgaddrstr_addr "Pr8a4W7Vao4pR1E6d9yMYqUpav8KH8bmETj" in xs),big_int_of_string "89953479704692970630745993455622286963614516887667884431394836281238600782578",big_int_of_string "656411605390680048662699143745324472714889086506919607178648234938161510978",1,true);
         (big_int_of_string "39420537632916502992034748157690519623378162434411414484977004038094297316163",(let (_,xs) = pfgaddrstr_addr "PrMQ27RaUfbXd6vW97CP9gn35FE2qZPRBYk" in xs),big_int_of_string "96237365533544104334917136545357789689994330481542348292355171911839268997246",big_int_of_string "53186159230672321498005463987168424613914714639900530975824543033120924499578",1,true);
         (big_int_of_string "14074466784990805344149216140467170159267278282696826503842786750577380797389",(let (_,xs) = pfgaddrstr_addr "PrLdMKmcEDXhq3kjJ8hQZS7FafYRzrxedGo" in xs),big_int_of_string "92289084498473123734461486733126665926798521108481353881255163663541189137570",big_int_of_string "44649593083243173489098419771619847981208343057472134321173436947682528525851",1,true);
         (big_int_of_string "8717213038504346209461164787395809898907703123486990837047457088378476091912",(let (_,xs) = pfgaddrstr_addr "Pr3Lni5AfUHugzXCuxrz8YhCfgh6YGHRdog" in xs),big_int_of_string "80090538919931902573217193485742414635953927550487541338100931673267955726158",big_int_of_string "68051690789538604107953466118251386619969511040591465491575034237288421850239",1,true);
         (big_int_of_string "34345438670216908814706259479968609323547875115645908242448657019220556621317",(let (_,xs) = pfgaddrstr_addr "PrGvKXUvaGzPsrsZWk16ZmqvzAiVbgPzCra" in xs),big_int_of_string "76029590691313292045321792162928028250757466087751472372587352755912337392148",big_int_of_string "67616808292513332998088282316977757086664101676168351555277450072774734797691",0,true);
         (big_int_of_string "14357359443897748776540411009158052060662492773435611811604546326639651488098",(let (_,xs) = pfgaddrstr_addr "PrFkdnxcukfRtiQ3MWE4PBs4T7FdQrFnw2Y" in xs),big_int_of_string "90788783891515387654238568805435060863240573083757904703769002540230550908361",big_int_of_string "22047228390870116366804993838083554121708463000755023656456540491197672824657",0,true);
         (big_int_of_string "29333623424559215373649573308197889033220286373997088662466430404729126739602",(let (_,xs) = pfgaddrstr_addr "PrFdMHZHuFS4NJa7qUd3mJyg9pdM2xfKp3f" in xs),big_int_of_string "69582253912400239778108602807880502425313987220437567757505924165353142259300",big_int_of_string "81536457747359240864302925827097077596244715019200579260316952304985431515551",0,true);
         (big_int_of_string "15796386932371899199520497579538811098657075472599336477136380465415131863161",(let (_,xs) = pfgaddrstr_addr "PrCWXQST7oYzwPyUM7aD1Jhbow8dEyMnpZV" in xs),big_int_of_string "67115338677175297718784536144282676464273197138329731851146813481277466830366",big_int_of_string "40771703970664952461254555844633890058558952446879640514349888824593901006493",1,true);
         (big_int_of_string "101928902123813030315252368396121652059862761482159489487711777494677874860470",(let (_,xs) = pfgaddrstr_addr "PrHUovtxUEtaDWdzjyPMicTXqRMJm3vpHS6" in xs),big_int_of_string "34692426553659006473190396044973479697252535976889812102497162666918539060993",big_int_of_string "103234478929154657953738824301674546414351832665060756541774954036174718875766",0,true);
         (big_int_of_string "35502660998044749108160349804426831340900027487206345088433793301213487885639",(let (_,xs) = pfgaddrstr_addr "PrMnctzUk9rjWrreMgLdkJEWDGRugyLTUnK" in xs),big_int_of_string "83140512858906167724155269044175290655262326591108696863669797157333003166099",big_int_of_string "1661432769304554649377474722316814508277369691107378055360787165924595405911",1,true);
         (big_int_of_string "49856352104692394707199607049969721993997783799507085434062208203605265279626",(let (_,xs) = pfgaddrstr_addr "PrMq6gBzJYrHXspqJWJBqdw8u9YUtwDNwKZ" in xs),big_int_of_string "8701051746893909045084811092297441491273699114855061015608718603546749471204",big_int_of_string "66625567529808588874931304631303627140958519389297414581934398504548241501522",0,true);
         (big_int_of_string "27536170073659396972659672920327197698428528044730048763806027849239480385698",(let (_,xs) = pfgaddrstr_addr "PrDTZn4pw9GVxCqwUdJkgmz5acnbNwetcLT" in xs),big_int_of_string "50608533081821447698970223626962451790256823439089781843286821512188848328005",big_int_of_string "114415725400918535094562515940423468020159654748354169892157938613162151383542",1,true);
         (big_int_of_string "115403291499085131236562616270084598229646266280683021800513003429275506334810",(let (_,xs) = pfgaddrstr_addr "Pr67mC9V5vJmzcKR5xsiSVEp2czpEPy8zop" in xs),big_int_of_string "69774567354584135227798611202246281649363035621945068374591228543924808994164",big_int_of_string "104618633948690971820073529579210992346912422174906653189749995564393895695806",1,true);
         (big_int_of_string "46957787364019507334036865419597887168759391544447232151619783184834999117027",(let (_,xs) = pfgaddrstr_addr "PrQAUCvKSVF32LSBVEHmv5vRgAdYQDPUQs4" in xs),big_int_of_string "7312203019452704556253836564760966354024489737486683396727534162183937123578",big_int_of_string "114011054012502147251398110393698691035202330808177504359888984321126936714770",1,true);
         (big_int_of_string "9050249831710186054012264430094626795629787121528836501027818040252012599527",(let (_,xs) = pfgaddrstr_addr "PrB9ZtCKGgn3QAa8dgPUqcfNtNVi3UfFS8h" in xs),big_int_of_string "98876852038209685342506244151185943920004955649668961503080940719774405595947",big_int_of_string "21928617624267593563637847996269804036718003456925434628432242381239692525082",1,true);
         (big_int_of_string "27221981982288448509706964451019343841030531966840186596342872956238504761881",(let (_,xs) = pfgaddrstr_addr "Pr8kErjPhLvXN86UQJJEipr9fyZ7JmGpSDo" in xs),big_int_of_string "66644109977877582052349934147582084456516731225211532550157975125731108970023",big_int_of_string "32880185721938051275485779481004722967602702738954338954868751655160813185185",1,true);
         (big_int_of_string "84818775369055641858561859817740587734182635807693970866563574441180356778014",(let (_,xs) = pfgaddrstr_addr "PrFa7W7GXVbCswiQ6uBMUc4WbmSxTLPBaze" in xs),big_int_of_string "85043340836726563734484368993380308921509745259832663193901094458961297390276",big_int_of_string "46531472333555366324093144498455581860917497679350946564402585923354374595905",0,true);
         (big_int_of_string "19075727197114237718637785318648187051970106328350502678685062450174640282359",(let (_,xs) = pfgaddrstr_addr "PrJNMiwQ22L2N8EJsyXDdA7LCoF5MzqYKyk" in xs),big_int_of_string "65229919225627581734375796010298753417349004567851575847573414459474965109726",big_int_of_string "45107952368499133446551763360609910551782832621940488165215189255446357946105",0,true);
         (big_int_of_string "114094529511741613611193259139221768255539552561155786355359885988853089054117",(let (_,xs) = pfgaddrstr_addr "PrB28WT3PHfDkQtpUBeWbt9Z2935d91p8vo" in xs),big_int_of_string "82543441166201735478688948529639295802876435377367753811253516232880251205604",big_int_of_string "96654946936913812966709107625591665546133599114299939898294385538739979566492",1,true);
         (big_int_of_string "78532505542890966431978965774698713871953249243560222509445397390817805541871",(let (_,xs) = pfgaddrstr_addr "PrDM7Do7iHSMpGvsrBFk2k7XNxH497N6eLg" in xs),big_int_of_string "88591100461176046002850584144285817285709811814236496922668685385471135815494",big_int_of_string "111649814959117018848850497412585479139218041313461429222374357381410126951588",1,true);
         (big_int_of_string "6503078206790916133682339368409625538569423314426071264706892197483912446819",(let (_,xs) = pfgaddrstr_addr "PrGT2oDfsyWkDuWEkVWK7PTHcHBuejwm446" in xs),big_int_of_string "54747470663752165844116728435274248512508899979776225136900115225638728587936",big_int_of_string "86695798042728770052014884612182612708593309141087437386838393380739363820223",1,true);
         (big_int_of_string "32130165615684703606700697041161818176196570227676769301713370074859517583364",(let (_,xs) = pfgaddrstr_addr "PrLTJNhDEwW7pvgiHJzmdHDYX3SDWek2sqb" in xs),big_int_of_string "103276584959012896111685024242203190473352179124659076243220439567038088113923",big_int_of_string "98427436120660504925592914722689395719323199044249774293547325278440320890621",1,true);
         (big_int_of_string "70099312021623434445044356424205439481939570649474111680627889212001524845576",(let (_,xs) = pfgaddrstr_addr "PrLTyp8qkDYCEc3rMv3UrcXwufG5GaVhHvF" in xs),big_int_of_string "80883788280196070217683739725188279039685640626867127151514269111395854650387",big_int_of_string "14889963612332895559771270821302504592516149995804024130965697398627857056657",1,true);
         (big_int_of_string "104274780076528905438435887006147682054893396841278446363810086321964200483607",(let (_,xs) = pfgaddrstr_addr "PrCazD7XeWJoFn3JzLDriZvossDq36V99Ec" in xs),big_int_of_string "76006980022996524375680616909428046971651624591053324710919908148115175969728",big_int_of_string "62212698784773035409214711585781053889803239373100724474399404921046764800726",1,true);
         (big_int_of_string "92830678436077983482318226688730045835623621084513745342455831523770736330959",(let (_,xs) = pfgaddrstr_addr "Pr9sZFuitk2D63WiG7MFcyD6Du64xXQyoMg" in xs),big_int_of_string "11341366807834361569313768329038665491390616175007735080935972050487984473777",big_int_of_string "63700799284894345069347235964147303505334218512496039795952271340249916799310",1,true);
         (big_int_of_string "66196652010653545529441336386487165580279433756856289281931668101492452217897",(let (_,xs) = pfgaddrstr_addr "PrE84fYJC7H4R9M8LeygGLYMor2wmuQuJZi" in xs),big_int_of_string "107097878214181432970743875381992516601988472924271181249862315233525195193780",big_int_of_string "17037020492052548036441962352573105741618871488319606042547510485218155898950",1,true);
         (big_int_of_string "92224623394576695864361203594484684273980180803486619417621306885057195754655",(let (_,xs) = pfgaddrstr_addr "Pr6ZFiFNg3UUp57kg8F1KjSYU1YAcuDM8zb" in xs),big_int_of_string "115247318839863156451432373825928994136023618006938918754317208367300571972366",big_int_of_string "26326842507022313822379020970979103454778128833317980259888307455421392036274",1,true);
         (big_int_of_string "114399644832551645530182921723233562638125057958481006150022140019344304614600",(let (_,xs) = pfgaddrstr_addr "Pr7nyvvuVu4avbrqW4URKc2ktCGEG2W6fet" in xs),big_int_of_string "37224958240013437103723095453877298156794867705391261440234842372652585155258",big_int_of_string "73020301094135577407996035678785302342856821609195510208102008398083565691434",1,true);
         (big_int_of_string "61362082613204940464949590808785421169962161819639341834556644472321715111771",(let (_,xs) = pfgaddrstr_addr "PrPfoX7Vdwx8g6QLjK5GPudquhG3VPhGjYX" in xs),big_int_of_string "24352228750596134534580216076050809903767184214962643120881616964229998320505",big_int_of_string "56981188541335843077383766173333863042520333976582045240502163853092621757224",1,true);
         (big_int_of_string "81034947950591444238175438636959800006655021230568826326573065186840784666961",(let (_,xs) = pfgaddrstr_addr "PrGGGehVtP24Bi6EthZzs6arJMmPtA7qb7p" in xs),big_int_of_string "55905117385019224224380974089396588029956353212033286402776584855488743143736",big_int_of_string "67772591514262207741734886215994892648390770245879370989443398234432566626294",1,true);
         (big_int_of_string "106682177309442003205315265334298016197894536914973327060228450770875308260581",(let (_,xs) = pfgaddrstr_addr "Pr5RAtyEar2ExmuqNikMGdvRB26mzX6CMAo" in xs),big_int_of_string "24921962823827379283661870274736351723516531012337140721723358203920178392597",big_int_of_string "90803374113774808953454550403005674964393917661645477589533005793414360883461",1,true);
         (big_int_of_string "56709402761743030577267132789982078094825274841945667393138412540910742982214",(let (_,xs) = pfgaddrstr_addr "PrMyKaNkaAhrxs7JyiwFgUgHZ6UekuQpZGN" in xs),big_int_of_string "47222778692445379525345119758938170763205805148738213255040971144471690308578",big_int_of_string "12633340528132552797364221110014911852394795071945957185550763791081538554893",0,true);
         (big_int_of_string "63264558460380620945076634457470220102393304576139843902827616470780433434499",(let (_,xs) = pfgaddrstr_addr "PrReEdqwEBrwjShCqTy1D7brfpAAfjmY25H" in xs),big_int_of_string "85816616848576568218550709305032618319726643450044057280047607544128490878188",big_int_of_string "47804467299877925320309122579161058517632983513573450472864495105151622856509",1,true);
         (big_int_of_string "57129568730434197059775598391747053282028495869693050430763439211681157489405",(let (_,xs) = pfgaddrstr_addr "Pr6ZFiFNg3UUp57kg8F1KjSYU1YAcuDM8zb" in xs),big_int_of_string "18291838324554663634074843487060446699324365719293418027794956745673241476323",big_int_of_string "41678430636271100647080535348850093746622819762207361612958116073806592132268",1,true);
         (big_int_of_string "69252970027351068334541663347233153067054797147372150750702855797090737665499",(let (_,xs) = pfgaddrstr_addr "PrHAJ3k15jTnWSqjGkEoUCuLdBmwgrR8dmc" in xs),big_int_of_string "47309732174435054223520629707058398478573083619288390638695971272975021615276",big_int_of_string "76882072093927654277607150772113223292054994221069978267483358350040819523128",1,true);
         (big_int_of_string "30936642886558708517572509417717278193407765553606700373110777942680588745268",(let (_,xs) = pfgaddrstr_addr "PrBe9tei5JUd6s2Gmg5Z5s6PQnAWdDTu4Mc" in xs),big_int_of_string "100497172894068906820107709593278733733257000955437193169515253803740613495756",big_int_of_string "61692774539027002779126615065465918600437827047318683347952939076095123449202",1,true);
         (big_int_of_string "61364567803804256501925722147490555093853241566859711833575862541883571887714",(let (_,xs) = pfgaddrstr_addr "Pr5pWLKo6TzTk3imPAvRkU6G9CGcmdZw9q4" in xs),big_int_of_string "6369111510665090062811267169431245486116077121028799617193035636404924154069",big_int_of_string "39279178061404668263141287023003721757914144650393320590193350118869499508074",0,true);
         (big_int_of_string "109805976818327192788621463981150143568155981843472015463253793998834143297204",(let (_,xs) = pfgaddrstr_addr "PrHaxseN1c5dZ44mGc4uVrWVwgPAmncCn1i" in xs),big_int_of_string "30380123169739105158436731905528691880918419589892791440864883883571212111885",big_int_of_string "52664271339096714786330576224395163825089717123216905629258069228062911324859",0,true);
         (big_int_of_string "102540825626245388447321099029282852596051566180415393009789962458689693250432",(let (_,xs) = pfgaddrstr_addr "PrBQtyjwv1AbqfRYBQ1kpE4hYktjrpG4YpK" in xs),big_int_of_string "3092452421144220111128721041085485629721482678925581428486861984544920527485",big_int_of_string "27237924930204183651321025924999926502060118218655422896715871678121545701483",0,true);
         (big_int_of_string "15235489404688287381465161611484548251665635335612555245873437452924537707640",(let (_,xs) = pfgaddrstr_addr "PrNRt93MJLKKZ6pLgfRt2rxVV39w1s9YTzf" in xs),big_int_of_string "73521415343796367413328195421532994897916079640903081248907714623434237542030",big_int_of_string "50760576974474891950126120544329271143592926165295191578549086121973677964939",0,true);
         (big_int_of_string "112397031094057254269184512222034063475719360181427594454272379821370988040241",(let (_,xs) = pfgaddrstr_addr "PrDndQNTQFBnfpnBmJw1FLJT9GMMQLEiHdJ" in xs),big_int_of_string "72811168955685137762453002660054722183009569260585576728699311814374504554572",big_int_of_string "18552781373933420104257162922661872000093916961233888925103984190559458208036",0,true);
         (big_int_of_string "98165579535122188837451562290450729377971943575608203983566662928958779333989",(let (_,xs) = pfgaddrstr_addr "PrGpGKr4c7tCXJ6BvzaMJYc7FDMZtWhqcf4" in xs),big_int_of_string "83250437623144689504430010840352415923985493704830392813230742302074895395839",big_int_of_string "5604140552314990468602830408365003979496566469824207875336475517650494501426",1,true);
         (big_int_of_string "57702772304265637708722873172874473948525495530223060875560891309040964628655",(let (_,xs) = pfgaddrstr_addr "PrLKg28FAyWLanbWuerkg8fLaQWL5gkhgXt" in xs),big_int_of_string "9452467567058271704905754720906086292491500381532201010569914613267749470638",big_int_of_string "17599141497898592285222092200849719847857432599945172056542265528818450326819",0,true);
         (big_int_of_string "41922837682770875546171735580126928883084879761222371184905018330523073488914",(let (_,xs) = pfgaddrstr_addr "PrLxyPK3a3Mg474bURtk8udFB8DsDDVQNux" in xs),big_int_of_string "76226003805480961997254382404892150899310278914666278127657490718104750981614",big_int_of_string "69307374460698231855929493279838800466860396237375432562053537744437760966101",1,true);
         (big_int_of_string "70925211096276680759084213717970489870998538858073456722308710323286484874151",(let (_,xs) = pfgaddrstr_addr "PrEPh6tqgChwrK2Tr2YvyE3rV8UXuBtx2Ad" in xs),big_int_of_string "78378401026180871107329910878869184489910247818087223455620204617553497190351",big_int_of_string "62235884715371802087474005261570681864713330734669764444784301761412930249390",1,true);
         (big_int_of_string "8469873468082506417596597330712313949809574265335041166988849273381587326409",(let (_,xs) = pfgaddrstr_addr "PrL7Li3o4BXuf2odPoQk9VgeFTrAiBsoam3" in xs),big_int_of_string "85354787921591126118164638573977029061472141275607976274724691954767725899930",big_int_of_string "60629202358623092956195836433915050184158304655106297039824496944272240300945",0,true);
         (big_int_of_string "109611501455661627558779524393332543195776542994131356440612045982060614984149",(let (_,xs) = pfgaddrstr_addr "PrB5TXn8b37fWGw1CLQuTXVFa8ZJWDUcdvw" in xs),big_int_of_string "32077889095587777799982811042675622711861953083597840256556419130699785912051",big_int_of_string "60764493830709694217192059373013353887062478028646148290946290366880728386309",0,true);
         (big_int_of_string "92300386046578088856505760860996729062495864026149650791322321457336999600692",(let (_,xs) = pfgaddrstr_addr "PrPVJumdg8mQKJaCAFquZh77Fd4UsJZwdgM" in xs),big_int_of_string "34515314018053131796350105089895230831805634137329026918349833528764877102512",big_int_of_string "92334494329869603308007612250775969336782837835870631600071022000083357550421",1,true);
         (big_int_of_string "63670350494254264497951507744541712865798706862116493189547968513241441205460",(let (_,xs) = pfgaddrstr_addr "PrHHwUnoVeyMeF3zoc4UBWjTNfrci3WF8mi" in xs),big_int_of_string "34187400301453349465329531993409494159261724916150276756862839967032204181119",big_int_of_string "53998153637866605981577830273357446734892726274342636561347459394072529834698",0,true);
         (big_int_of_string "52515992610529942486290054579276811356996910657840410172201647661562316511695",(let (_,xs) = pfgaddrstr_addr "PrBMYeNMNSyappcEeydcmFpPCK8wB9V7ATb" in xs),big_int_of_string "16066686010952173369594466922020638405032415035579982339936673730762531339161",big_int_of_string "82573802277094772928150133490866601278951141136130578857235464568649861945212",1,true);
         (big_int_of_string "71287020532131103734359330844352670117912523189182012387641654350885783398190",(let (_,xs) = pfgaddrstr_addr "Pr9jVU8tEJyLmNj2YaBoRPyLJatEyndb3aY" in xs),big_int_of_string "26977659430624276880400031504199641008142492022940121772941923592975526380746",big_int_of_string "52669550147278325313961086497550532666025417098394807825893128561781575469191",0,true);
         (big_int_of_string "54994785272540343977681138635311196849876606541008675537959092553394631145637",(let (_,xs) = pfgaddrstr_addr "Pr3vCmg6orKCMXFcvE8acgKuipJFbWRZ6Z1" in xs),big_int_of_string "34486625087070382471640216587506074637663747905245962154540005001574677020652",big_int_of_string "87641341441553759185250917657996867928207590572245549921918216515429078276236",1,true);
         (big_int_of_string "97002590337993155768594539213217816976626109702385662988596176552259437854357",(let (_,xs) = pfgaddrstr_addr "PrKoJEyyH5cejeZfuV7XaU64rAgqJnTnzov" in xs),big_int_of_string "85996275872134222525492216148390165962459656001584078749898953889453110062807",big_int_of_string "37308404569238762053217902646255372897375422530592042679015629204560553000257",0,true);
         (big_int_of_string "38641968352134315613999237412502891269296371464349715440109174086948515518889",(let (_,xs) = pfgaddrstr_addr "PrJRE4P1HhnxmpvrqB7BtRyfCeCDTQDJ2Pd" in xs),big_int_of_string "36833903064851130539002124816907728450639959231065490538589290658637168895766",big_int_of_string "45626527622815774064970345261570793017454411518669047557657342020683113212042",1,true);
         (big_int_of_string "90303247996462776675164479663294693340995436134988252673396902116304191946836",(let (_,xs) = pfgaddrstr_addr "Pr5NUwEaz4yfouhL5ASGZ6p3z2VxbBS5PUF" in xs),big_int_of_string "110198462838613895469001544132618099744646708463891976997749001836136083364947",big_int_of_string "19753881503540826804667160544109354880163077451164624659178231126071918294677",1,true);
         (big_int_of_string "44428848330408487667078967247681401505377851623503911601186564810647181291366",(let (_,xs) = pfgaddrstr_addr "Pr3au6aMcPVPobHDkSG6CZVeto2G5kEERd4" in xs),big_int_of_string "85934508161642200316247931110829294766270432627769617308015044932051944163174",big_int_of_string "6078065127337071378745306068565270321715350290519497229552671141099762976221",0,true);
         (big_int_of_string "5016325282350521498906181751839328862773570665885968081733554691751756491806",(let (_,xs) = pfgaddrstr_addr "PrQ6DJiW9SkEAtKAVTNYoXw2YEXpSsmNwjT" in xs),big_int_of_string "31218460927733180090429704977513389191152675328536631642244469028334301177895",big_int_of_string "26902897441343169979703364088253382287553679041481701630535312179150916316191",0,true);
         (big_int_of_string "21248357442520914205567931992675590379733225336311955836981264943505669919588",(let (_,xs) = pfgaddrstr_addr "PrP7pD8a7aucihoxPYirHB9uPHJMspWjFGR" in xs),big_int_of_string "67843100747305773273347242183085492415767850407068170483466704228715954311198",big_int_of_string "55270316536074042011050454093719364565400716033794741687462442867378981941939",0,true);
         (big_int_of_string "75325485156011858553453123905555410612258178089502437356424191682343250569480",(let (_,xs) = pfgaddrstr_addr "PrHxuTEFteQ9eZX4jZCiEAj48nfoiaPrxRS" in xs),big_int_of_string "35933722366669267900469652269897820010009678067485022589011894629037325269626",big_int_of_string "7101646594230767247626855333480041575033552188660323367352282998484407670601",1,true);
         (big_int_of_string "3893645724734085805351116757520018949717637799932919344020738111557323591646",(let (_,xs) = pfgaddrstr_addr "Pr4N2SUvyXhgFMZxfx7spm8dzPnLQJh5EEa" in xs),big_int_of_string "28831808487697651201865844465845350477652768236573645378482506230871666341039",big_int_of_string "76997732678655921511745005034385118161657065570954007945034111516395861467926",0,true);
         (big_int_of_string "67377780385724393887136753330657531796145203922113127210292821639649404739008",(let (_,xs) = pfgaddrstr_addr "PrGXTWtbkgM5dRH8U88WGvtuxNwvSbSztsF" in xs),big_int_of_string "24930032084042669942206441143901236336305113878973283613024569369308048238170",big_int_of_string "87358279777350836982052546520951028713870537191915178941538353682545823297893",1,true);
         (big_int_of_string "44588867654372486953622766468482654925991507440557058931776011104362271837265",(let (_,xs) = pfgaddrstr_addr "Pr8MBNgcF6mczhfhkXanUkzN2T2Foeknyvk" in xs),big_int_of_string "8764165145548784716956570741743915872563376151828542811428843586150037322693",big_int_of_string "42767229359295755260103018894129551815519263390316986002587878014748755170269",0,true);
         (big_int_of_string "107492427214770355392681085497640822014054700658137275793439625595203046924435",(let (_,xs) = pfgaddrstr_addr "PrPfoX7Vdwx8g6QLjK5GPudquhG3VPhGjYX" in xs),big_int_of_string "37195361238895694317686614153716949085113859968522488687758674350247125118255",big_int_of_string "68496919449155672773329145549342288056271380445103503654169466624189293715904",1,true);
         (big_int_of_string "50370519545427502945074295413198894263425579944915125765352344640835925362031",(let (_,xs) = pfgaddrstr_addr "PrSFarDpAQS6nfczM4uAShJ2vhyCY7sgjhT" in xs),big_int_of_string "6566132519314133211532238649192288799424116407562150727502299827673040313234",big_int_of_string "71677781533718212820118895251079691235111830681682656492998816164167642623115",1,true);
         (big_int_of_string "103750994824201610924712978995705200843824810964700086907941919677797360633131",(let (_,xs) = pfgaddrstr_addr "PrAfyrmJ1VVBAqfLK6hu2RBbwFjpDqSGC9D" in xs),big_int_of_string "4261509550299807201181542899242094721333376809589442695389339202131728848730",big_int_of_string "33667440770562450448226280611203249724400446326091865705080872603573466440829",1,true);
         (big_int_of_string "72907680139851678588081967006328603510255097924349583054976969765062791423124",(let (_,xs) = pfgaddrstr_addr "PrCyF9NbHmk8qWyNZLG6fSmcQSF6goYHEJg" in xs),big_int_of_string "111501513501496797268846988109660516967014434712084504054474837021091848017324",big_int_of_string "43202866402052181390628800192983405136792139713839611773658180886851137264586",0,true);
         (big_int_of_string "11464917877208103264005512051984631292722798431975335680587031331711931922947",(let (_,xs) = pfgaddrstr_addr "Pr6ZP1r5NT1npWQyoJJFfKs5xd1ULznpSn6" in xs),big_int_of_string "43726447717558910485715074429926293156377241893752674976691517226437190749530",big_int_of_string "105178237955110882889502570558523364365483191612785277298190368427830000424193",1,true);
         (big_int_of_string "91157909298119271436479636850896211654247718860587088048625477134427918916531",(let (_,xs) = pfgaddrstr_addr "PrGWwrXBfcxczNisoBY16pfZJ15mUeAV2ey" in xs),big_int_of_string "60988438392597239913099852396518666876103288278904232654744567119661678665763",big_int_of_string "52542840336427658892155102874893116655358807927280406607312469825388902189467",1,true);
         (big_int_of_string "19204799987988086015770030134962716907285411064732967633885356987238601104045",(let (_,xs) = pfgaddrstr_addr "Pr5oqBoj8UEhG8NqVWU9B62G2PVn897cpFq" in xs),big_int_of_string "37010904886241325425558028509207732176819054017313714528886140200695536905377",big_int_of_string "51282927930198799565500503526130422469712582712277601061060288610187783089145",1,true);
         (big_int_of_string "32534309550392975063523037781584606854903165764688618232868422539411815407097",(let (_,xs) = pfgaddrstr_addr "PrDgYVRdQE8Wi7dERUH1Lmi7GP7B7NGpQzZ" in xs),big_int_of_string "88019307190930758556949121611190703441200072858972731973658662558606178797978",big_int_of_string "44908503093097658500802439153450946714012459797528073928859704130032820068291",0,true);
         (big_int_of_string "27319606130884794716786844815497470668946227176682422407042942517243432232553",(let (_,xs) = pfgaddrstr_addr "PrRJkvepiADUCwHGAv7K4kCwgx8TVt3aced" in xs),big_int_of_string "12327887389981443603591884306763442754991836033587473078795614251760617344468",big_int_of_string "68671368254677955638093028394067476216042154054858304887905415737236121028028",1,true);
         (big_int_of_string "71000476982374504680081230190711085783793447101916013495277685845160868934385",(let (_,xs) = pfgaddrstr_addr "PrDPTT5dVAqPWo6PtqhPDMBv63Lg1GNPzhe" in xs),big_int_of_string "30944262802958550927022662990190486619560874347834862266182566807770113526541",big_int_of_string "7268309188785141003217048814764926086972334633570208358330044407053587396865",0,true);
         (big_int_of_string "8298933501389901691157924594086585260407063739209989692038010101015752835808",(let (_,xs) = pfgaddrstr_addr "Pr5D17EC32rW85vbiB8rwJfG5nu1YA3aZGi" in xs),big_int_of_string "24442724776487539570378106655687683178646995850395440771946753787811664043059",big_int_of_string "8813612294494951012910118080470560197089453850481698427356953789822096576707",0,true);
         (big_int_of_string "94604971188555141755449811045696245783433150942043312817881204211924894515916",(let (_,xs) = pfgaddrstr_addr "Pr6pUctFi1B3cnN3qho3EMzrtUrswCduq1j" in xs),big_int_of_string "38940154016339003417298873781723066684354640970937549772025539959481594384348",big_int_of_string "50552551128147654049529581494443754829582330728931371279619663763761217983811",1,true);
         (big_int_of_string "66090765924879911823323430001900261734187750196098195165463010108683675560378",(let (_,xs) = pfgaddrstr_addr "PrCFQw8qJpjvzdpq768x5sJqGRJqDRwjQgE" in xs),big_int_of_string "51874621695876661315766778986849411153072776784040805239839400638530022050135",big_int_of_string "8822482284813324424593965412034018600164101361708172274146437977204574599184",0,true);
         (big_int_of_string "29467471280673454923325361423543565914022629774844042947205863142879276653441",(let (_,xs) = pfgaddrstr_addr "PrCz4Ss1ofYEfAv3w2eV79zHVtXpJznZ67Y" in xs),big_int_of_string "114176300139760512115884983507376473654057379172551238288704593332155475523892",big_int_of_string "13833630664089335690838403393136680132634067267376203638463378623820890526509",0,true);
         (big_int_of_string "2034617085232411048031959658395343543459950068482016484185187825886185899734",(let (_,xs) = pfgaddrstr_addr "Pr3t1XBoPUsQfHTLP6cM4CtrxteLLrPZWyo" in xs),big_int_of_string "91975815205443951967061940702834712073158007613858632549568482267481575018661",big_int_of_string "110013408868494679773782453916219615454674102779322213483851709683166381223127",1,true);
         (big_int_of_string "43419901486822505728929925022292828661516405714979645634383775289176277636301",(let (_,xs) = pfgaddrstr_addr "PrHaxseN1c5dZ44mGc4uVrWVwgPAmncCn1i" in xs),big_int_of_string "23392133145077500534187855626363033451234218031832274857862785829667472665506",big_int_of_string "48657917916202923655663719344988877138352295696810672137063892034519182934799",0,true);
         (big_int_of_string "21602714461211959775831344795599232574795756614990470853158914419485566839521",(let (_,xs) = pfgaddrstr_addr "PrBSXauppq6u6FLk5Ym4MspHMvzLk7mQcnC" in xs),big_int_of_string "52342307607102641802273389320262866352719633034428032471602954629793688382847",big_int_of_string "47064379154900807632133057518526147738656736127003607101900362601836264401864",0,true);
         (big_int_of_string "34961443577437806091254452517035716409967130122790395895700363333652552743647",(let (_,xs) = pfgaddrstr_addr "PrFFJh7ecJRRc7376Bo1cp1FA4a8a5YSpzJ" in xs),big_int_of_string "114177794098751370225956745703820894814216385259811411283807341502752267573735",big_int_of_string "27398158425386584221206274448197540083343042419227095439129110878194821605570",1,true);
         (big_int_of_string "17204142405616750143855618121134405794544188883604999821090612549881737200559",(let (_,xs) = pfgaddrstr_addr "PrLYZTj9vVSSJ9XmQpDEX8YNEdzJcaY95gN" in xs),big_int_of_string "109004156448008952141813921115240505102898222893422419515469737397367326974007",big_int_of_string "113880370637370000160011337097418753962415649147822344004282915200204141874470",1,true);
         (big_int_of_string "31169685086298953803233620126245397167998201318594645754490171868887905588518",(let (_,xs) = pfgaddrstr_addr "PrS8CMatgZcXCkpskhDbrYqKYZnECbDzYRh" in xs),big_int_of_string "2320731111500505900923176353499929988074292029305430207697284849061825466133",big_int_of_string "76342232274154706361629179240089959155602299148958261720105097144696272225825",1,true);
         (big_int_of_string "34986713025667184120532447637229866517131515651332082400845899732806798790296",(let (_,xs) = pfgaddrstr_addr "PrFZoYJKBy6FH71qVNDWCtoSAgGDpariHiH" in xs),big_int_of_string "42006855532235758383930069272038938105736222708745521974275375261961609420700",big_int_of_string "70649793495504896469342087667906621699827058707844344844328332350357675305837",0,true);
         (big_int_of_string "44931778372093927832350588425947533964902095662661248089699343554345241037792",(let (_,xs) = pfgaddrstr_addr "Pr5uzVn1kRpCeevDykQeCjEasMDRVFTHQVb" in xs),big_int_of_string "73852156843760139365324918607494984239125331748606862457461351891395037103359",big_int_of_string "53728651899984791361259506552767666833376880796659907193944626118076020174467",0,true);
         (big_int_of_string "33979784389932803380523253083554871363153006119435859841266034378932230185672",(let (_,xs) = pfgaddrstr_addr "PrQq3LBc3uyRUb8FLrCr8rZJbszsV8t5jUQ" in xs),big_int_of_string "109921300472832876884108744783670570348992949925586620868131802000665127046395",big_int_of_string "98257567310030265582946610099998257881472898036614683711144070256276113656767",1,true);
         (big_int_of_string "37546146904411339538195439433266361544168394874560417294785771780182136929958",(let (_,xs) = pfgaddrstr_addr "PrKqYmTDTxdhtEutkE4Buqu35odqWDhY2eT" in xs),big_int_of_string "5689915825946860135016577866626858531107070421221003207511591712073671177055",big_int_of_string "16993122123858426119625807853485025435199052504561015757814628776349089444529",0,true);
         (big_int_of_string "68418628403136516243660650988340262692401437420568998142902529923475142596482",(let (_,xs) = pfgaddrstr_addr "Pr5nvuSm8D51YoDtJ3BRwoUBJ1tS15oY5L4" in xs),big_int_of_string "62389570565519676158599865049685147649871081040802776508125368000688046776530",big_int_of_string "65346255623049846489067675089637134663403351435437750592613718643071104968656",1,true);
         (big_int_of_string "110864722912673675199619930576181847990391835143030369990664720769675446639308",(let (_,xs) = pfgaddrstr_addr "PrL6HpshJL4jy89TF8TiGytS5rrnrJtwxDt" in xs),big_int_of_string "77963571774010053106513703453874452318768250357759490349272827718863358697389",big_int_of_string "107929868092839018617472948682383659159789764302784773567093564007276051848607",1,true);
         (big_int_of_string "107070768042633414948291162213209980862314866103243897039709638616565928051060",(let (_,xs) = pfgaddrstr_addr "Pr5tKwbTRutysWm1AkWXULWiK8er18PRXA6" in xs),big_int_of_string "73146108312170178277674356727040506030008606798577311708510271129675995107553",big_int_of_string "27889069385406588739550459619494957086305167092127610510411172614094335270415",0,true);
         (big_int_of_string "37274847126228984454492024786133421422374438287349319153298736198886017017603",(let (_,xs) = pfgaddrstr_addr "Pr5SKwLrTdnYh1BiGp5CbKuE7t8N1dJ32qY" in xs),big_int_of_string "87902211488565173151358909084045665346590889519398456924745842216262690102673",big_int_of_string "63612205768889690233632807516806092786200920139748749974064114829361013002789",1,true);
         (big_int_of_string "79487718762395055357370920897431835763057697552107757202289992063101799208500",(let (_,xs) = pfgaddrstr_addr "PrP1QbwnyzWLq5GVXCLHEafzTrnBG4Y3Lfw" in xs),big_int_of_string "64861046464751938675110435878290705565099609090301746395281168837564566159776",big_int_of_string "93961593690087722260458599405247649916278126650774708152083767186707835308374",0,true);
         (big_int_of_string "31844036840834666914941568588854492957434763150133722948669558952352877321562",(let (_,xs) = pfgaddrstr_addr "PrNW6skS3MzDR3xVivC6CHTwG2tikseHvxZ" in xs),big_int_of_string "42545824364360914198406441099583453089102033766208954612920314639235827536575",big_int_of_string "114141404423002430645298492532492295761140350794283560854937723153683773501720",1,true);
         (big_int_of_string "41784196732913001829993089833059379624692648237718121354050887925657520115195",(let (_,xs) = pfgaddrstr_addr "PrPEQc7rdD6saKC9e6xTMzbwVxqaMF1zJNE" in xs),big_int_of_string "76146464344057799134628320228293687928945071300164508970153064006878670269724",big_int_of_string "61494813072866266315454764471738492744894541332362519497119248415917171800933",1,true);
         (big_int_of_string "48313741559603961114276415121661400738839113334066817367181762591168077017646",(let (_,xs) = pfgaddrstr_addr "PrDbj2y9v481zrApttf2vNzNURb9tR6C8xx" in xs),big_int_of_string "64765054649875724516935138052865825067381531522795318319619172302010139854023",big_int_of_string "105566335590260896999480950035526056806045613106120929766207693285340139240733",1,true);
         (big_int_of_string "75163073114030218211632529810269048651268976788712970762291107243087377858043",(let (_,xs) = pfgaddrstr_addr "Pr6ctg88A3bhd2fjHC6srPzytm9wtWS5ZPn" in xs),big_int_of_string "19804266180439279125920833341220800666871749243160534881917393069653540051416",big_int_of_string "11269179994724913371336278131785888689627742377141188768469047852028564033176",0,true);
         (big_int_of_string "52428610651564793440221611142334134820590743268861554581160621660231690323771",(let (_,xs) = pfgaddrstr_addr "PrJEC2npknasiwCSYcMr2QyczPYgNSJc7Yv" in xs),big_int_of_string "75256816945837400849093697403992290128941433837655351057923302798552617553377",big_int_of_string "90285467034345719128663252628829167284454171550991575942060066626292444718328",0,true);
         (big_int_of_string "27791264951912234159047755562725305839329462525294574478482623292807866229321",(let (_,xs) = pfgaddrstr_addr "Pr63ExLC4GwjqEp5RdU4uTPfqbuKUczU7jc" in xs),big_int_of_string "45405758202473947467634151032918937281721981832261824529740656558723524061337",big_int_of_string "60950118964823993610816273735263159935997841648994343875697537106940062793100",1,true);
         (big_int_of_string "3546791946872061251345151297801110303740443106783295086826424828059934726012",(let (_,xs) = pfgaddrstr_addr "PrKy8759Pn2XM8keBoDrrxrxPPXfaQPAfJW" in xs),big_int_of_string "29103131809093001715629074669362554671220320943718505832396937625423777794554",big_int_of_string "63100810776033284982624691723238956231868032883243576231940276276696763361174",1,true);
         (big_int_of_string "4303110764302887755164141017640120478083110557780902647028195213831394758808",(let (_,xs) = pfgaddrstr_addr "PrLG3UPAJRJn8B82PrQzG4GjCM1zZdiMrPH" in xs),big_int_of_string "33848649142621321268666406998068928249285956284309585658421674806515490637695",big_int_of_string "69964813149258101287080271871251004831253201869525388329795113013492169548225",0,true);
         (big_int_of_string "20896829910246112726684626747912202956989630887557871069059079307460545796590",(let (_,xs) = pfgaddrstr_addr "Pr5viGpTUSqomCrPd9MVLksiv5uzShJcwbC" in xs),big_int_of_string "100811581864590479244455237113007707312084757220661184469406043433327348310006",big_int_of_string "51820279325650812429266132755737159969751163437999537207249782061066596085991",0,true);
         (big_int_of_string "99491204173344481819442264483267380532619461552951566039891611603172737817662",(let (_,xs) = pfgaddrstr_addr "PrHYwmSZMdWVSkkDjAAZui31sYmKVw7JeBF" in xs),big_int_of_string "21647702795355850617155486006202742416847325946079558955147982043412195148712",big_int_of_string "31130493343157269427967199251435971621219797685918214211113936743008015630084",0,true);
         (big_int_of_string "65157440514071368100979003565867444351095371499349778070149456505865845544036",(let (_,xs) = pfgaddrstr_addr "PrPX6PdxvgygnwLQdAeJnXoihwLHLUY3vgg" in xs),big_int_of_string "21495451841299144621849796139324696365250201966514979755616650912352684577139",big_int_of_string "23668839427940588232419676181341386185029046253852582824172295644773188295856",1,true);
         (big_int_of_string "89561736414348660934745787329785708105264912270328411759049276241004508157962",(let (_,xs) = pfgaddrstr_addr "PrKy8759Pn2XM8keBoDrrxrxPPXfaQPAfJW" in xs),big_int_of_string "14621919875996745719175784819224788465415523559653057953723483490853963868415",big_int_of_string "25368834144196268237873097101184280602611582283712982842061410611325790176888",0,true);
         (big_int_of_string "114681972453174165317348262290935175684304814346466996891478511440461893367835",(let (_,xs) = pfgaddrstr_addr "PrMq6gBzJYrHXspqJWJBqdw8u9YUtwDNwKZ" in xs),big_int_of_string "35472136224095563546797599913664416381266166528505865043846593580582506647845",big_int_of_string "109908832534155131519037069116903065067770630527726902630078767051831044185899",1,true);
         (big_int_of_string "80242361401658551238851976498293755648055283223673359411281139432710990895915",(let (_,xs) = pfgaddrstr_addr "PrAiV6AYAgMSVueHAtUMphUvEPZSQscrdv1" in xs),big_int_of_string "32360561987460114681722890334340473835756027716005508927438312073562360008888",big_int_of_string "36404884152104823127332438475253358172344781206896850854688862524690849821158",0,true);
         (big_int_of_string "99895433531700865968831894279858515652589109254994924204308688433314516516547",(let (_,xs) = pfgaddrstr_addr "Pr9nPjXJM7rfV1orMTVgJ8U3ZvBdwWteNiK" in xs),big_int_of_string "30806447881038050694965637212939395763689895722788454630485403520557605064137",big_int_of_string "111601477522337583442060945582316905339302206989848721744934345837330347316533",0,true);
         (big_int_of_string "45418689967911996017223163995192935702828396062562916428635250855100440689178",(let (_,xs) = pfgaddrstr_addr "PrCp2cr95TcTw7ZmvntqY5ZYd2qUibP9BnJ" in xs),big_int_of_string "115157237730786730371180771345554532501810324227309940883730723760856309980257",big_int_of_string "20046984027228315315096769388171242621829590402072618529785478728843919417749",0,true);
         (big_int_of_string "44187428840172468701403136428834731342971808053764169814560763219414550225737",(let (_,xs) = pfgaddrstr_addr "Pr52k5uSwaxHgtpnBpxFrZDQf3bqu2RwKTc" in xs),big_int_of_string "15759479885939773621364572227214527841209063058438685062376030356823265017452",big_int_of_string "67574005856885808251420029937223373033098763322877719683815365353043734737933",1,true);
         (big_int_of_string "38843693040448293452653751077224629883574134422367440791273358437726228385848",(let (_,xs) = pfgaddrstr_addr "PrHMzBGnDmCZC8dkkjAxGzKSFKfDjtdPD2j" in xs),big_int_of_string "74048262728311952221766470638170167725422564474128740775615103620911570933103",big_int_of_string "86463815707693741477870555172760094327026166099771832869213385861533586762685",1,true);
         (big_int_of_string "92262300135460871982117799480521353937625784947635990606981257142513062662799",(let (_,xs) = pfgaddrstr_addr "Pr7yxbGC9N9sFfDxKyXNQ7XWgWgUpH34zWz" in xs),big_int_of_string "59740054402830171167356134682904757000908932577344860387537144839201686135577",big_int_of_string "1808349848207082533055857144459791150364430496793253838348471609344837286170",1,true);
         (big_int_of_string "104971292835188364053351369759537079630540686370451082480463282276698092358676",(let (_,xs) = pfgaddrstr_addr "PrFsXKE6Cqf3MxjpavEZ3HpvBfnpnWCwD79" in xs),big_int_of_string "26305211189660245319464317257011100416201047156682602764296125234212864759507",big_int_of_string "96404666641104838439462310249324821746365968545390053187876143682329564508753",0,true);
         (big_int_of_string "111169308600971653336398979669963865679004864352176232490954536753686295588960",(let (_,xs) = pfgaddrstr_addr "Pr8gPDb22vKSWm4wyFSnnzUiJ4M8aBv4aBA" in xs),big_int_of_string "106247719976987410330859754097085855951164618896828311749565476536746861871405",big_int_of_string "72137103868948878615918612214944659431496286874670180880249806454884206049366",1,true);
         (big_int_of_string "73918579917606148662016182604001931494225640538920748990178643552506175748469",(let (_,xs) = pfgaddrstr_addr "PrFY7neshTVxDHLTQbuVfMmJMdQtCZQNPQx" in xs),big_int_of_string "9504265914955588710003230040053845853811874534196916216236672647819070149737",big_int_of_string "50130687449681805956151728225209284918326539031726722253748149271611242397181",0,true);
         (big_int_of_string "20004140704306356241203225462853840025798724809821911213605392815938361756242",(let (_,xs) = pfgaddrstr_addr "Pr5JxpmqfnjvepqNc1fXfws427D2nju5Wwd" in xs),big_int_of_string "93183705156996515481142416632674325523699635731393048472265340667977025902859",big_int_of_string "21015076713280490653820803974678757739119931301184954682137430570211765804336",1,true);
         (big_int_of_string "84558023036650360674061335047182684459938590567609254492008730380067519082776",(let (_,xs) = pfgaddrstr_addr "PrLXUc3xKAB1rh9qz9yUfnRmxrgkbJyzbQe" in xs),big_int_of_string "111383817865377641966162743838276176278663161741424913571065463712828532992542",big_int_of_string "40695210914814606309742186521600168630137659842949638273330657941213039232134",0,true);
         (big_int_of_string "38451209258311540366868835877517915522696104341470929637730830235273167975262",(let (_,xs) = pfgaddrstr_addr "PrFLefWM8uN9AMEounqujVy8UGWY7j99RVT" in xs),big_int_of_string "92905953503181434569748383519432686085912337116680381028313483147479150599387",big_int_of_string "103522224092740964659169600835242123588553766822011402494729528995730101903858",1,true);
         (big_int_of_string "27480266820163933286937074409875133613141071762156180529832992714396099083809",(let (_,xs) = pfgaddrstr_addr "PrLxuLKKpjELEfcSMnnTJXNwAA9Ah2vQzxo" in xs),big_int_of_string "6988582319684956411572361725034778664346676719537389234284870981363441038279",big_int_of_string "20226487651442622978555475731628621003818096744107935082792897781406377571344",0,true);
         (big_int_of_string "33401711969100018678961769474402169557045143282804094097331494351683486261193",(let (_,xs) = pfgaddrstr_addr "Pr5j3xdJAu7PVvHDumod9eHFtKb7vwZs57H" in xs),big_int_of_string "30444884493586117885208546346057124278498519625080029606593936361705673096724",big_int_of_string "62635841419762365505422978145363233338256806035131524619544478382140645057200",0,true);
         (big_int_of_string "6796178726263014763557349990497306351423237429103152061820769467676496950361",(let (_,xs) = pfgaddrstr_addr "Pr6ZFiFNg3UUp57kg8F1KjSYU1YAcuDM8zb" in xs),big_int_of_string "16051185140309424687384993241168577764172980002935430136052748777500525410068",big_int_of_string "32301356017243927088646152157855032444827346609230228612324335088910698952015",1,true);
         (big_int_of_string "111533347861187350926655461319428430034766866414955315946446926453968158389259",(let (_,xs) = pfgaddrstr_addr "Pr551cqjYwQKoQs59LrQR128S6T987xw9Xh" in xs),big_int_of_string "70179988891500569327435606366812388170013861283562622984027945493391941156267",big_int_of_string "2477368041699832918026321280369892157385923828626523576418468138282211604353",0,true);
         (big_int_of_string "29411387023952088512070179105388876418112572707060595320447854371362945284945",(let (_,xs) = pfgaddrstr_addr "PrQiFgg3wx2RhUXeQxLic71Xnz7TZxJmSxt" in xs),big_int_of_string "99864951648131342574746356064168791813619236294381616067373507547829357393852",big_int_of_string "28701592082560694896155097964533406724811934919907032011874526088886927927631",1,true);
         (big_int_of_string "62767582377024962927991625819137934520393959080664076744136610004230638843489",(let (_,xs) = pfgaddrstr_addr "PrBMxpg95xeHcMY4sLm9k6DohmjayQEm51Q" in xs),big_int_of_string "16011698959586363419486698707525002107021974866623707499314634651935571494118",big_int_of_string "89897554320130488761307064802410145523384222476689190987720807361873284088668",0,true);
         (big_int_of_string "46855696678877109936656077485863445215045738316937050842666133893042849432590",(let (_,xs) = pfgaddrstr_addr "PrE4L4e9M7NqzUQki1NhSeXunXyj87TZ1xY" in xs),big_int_of_string "31008124383714330114540049488383556198798503987660483171541065697064445205042",big_int_of_string "100007219351587624682825068143791879114945993578714992567304165095037510362869",1,true);
         (big_int_of_string "76871296404977738144528949521853051380653456153109075848716242577425106708637",(let (_,xs) = pfgaddrstr_addr "PrDhvvbxcwU6okps3uVF6fPGfYQ9s4oy5pJ" in xs),big_int_of_string "32635792847383428641269540222254724644495218324787107667806076628801053884446",big_int_of_string "63071798301378511588596409349480555612107692624921800124257137137065747815002",0,true);
         (big_int_of_string "18362176323827080980496758590428791146846731391903206318291415704350901259080",(let (_,xs) = pfgaddrstr_addr "PrDoLAB6Z7EnHkbkaxjSzgohbmtkVwTjQ33" in xs),big_int_of_string "55463401413193276683116870376373785906882542700243170043306222136875420340619",big_int_of_string "66157163844511060386802176824724050777317636765588902893407571626377300585255",0,true);
         (big_int_of_string "95426538181644592577032990146620174187400319400092266294337070917315022402788",(let (_,xs) = pfgaddrstr_addr "PrDkkfpyn6W7gvBr2Wyk2UKVJ8jVgcBNPro" in xs),big_int_of_string "115012402459013407069172037306669900785077700101182247156282596076592838662280",big_int_of_string "93818368528731891268210489355154048218353950348849107541402783451987416276857",1,true);
         (big_int_of_string "94538780473973863342013455088339037262336467174347198051675438573892672171282",(let (_,xs) = pfgaddrstr_addr "PrCD2ST5gKD8SXAmSkazckmsqbEawVLTXwo" in xs),big_int_of_string "29624191983616348979930396720683728008985285320845607377559009267175875930135",big_int_of_string "32034572289567945875203579299870951128284204716538555190338852106365606068329",0,true);
         (big_int_of_string "27878500577914448394246746914108431643140163246171010604796706846369581286823",(let (_,xs) = pfgaddrstr_addr "PrDpx56xMqcmCrg5Mja5BnTcMtjWAaNEy24" in xs),big_int_of_string "67064046451841276582186104994510488404268402308390024357166203842190353366379",big_int_of_string "54899679661276110435405426781646959032375506455367341655059719041584450704239",0,true);
         (big_int_of_string "29632910948262406116542274549756112197932772644266466888136031360546521347405",(let (_,xs) = pfgaddrstr_addr "PrQLusJGt3McEoTfgdc7KEndhY4YcKLxNDy" in xs),big_int_of_string "105639872941490514972995034929957566572486123100369068400478947111852416539223",big_int_of_string "86984132568658656287664069876372606641747534631203240796753423363887792085434",1,true);
         (big_int_of_string "84298161423873976334352303295246864827479653172933105120007159752989491243240",(let (_,xs) = pfgaddrstr_addr "Pr8DuXCnefFf6S7k918ML5GmvCRJZtUDARH" in xs),big_int_of_string "50901559156137244250903873623387077219619731083949633066434677239553064149702",big_int_of_string "7793308413555364525447093774869900740423615027980291221523453824693901730319",1,true);
         (big_int_of_string "28187830545440654004874979036063717871945176599115845373656694040744285021128",(let (_,xs) = pfgaddrstr_addr "Pr8pkFksKzNXSSZn8AkPWPLTXzgpFFMpTnD" in xs),big_int_of_string "31728661751399972903801852014191760544289051857463385497185473170628828234779",big_int_of_string "93933248817246339908339107204049116527959451633983968505575229040568717964306",1,true);
         (big_int_of_string "52552097928004863863103493682220122757038067395313157443399958141144742610141",(let (_,xs) = pfgaddrstr_addr "Pr6GK52a7Z8dLLngbc9rJu3yMnuTNeUVsMx" in xs),big_int_of_string "60541866931910725667361189716582288316463312603886905938966203436538293784134",big_int_of_string "16296891841184388758746005346422722655317108921224420507081563411698853205436",1,true);
         (big_int_of_string "19357000526761146112831373492127000502789819772204554263108203641621024027663",(let (_,xs) = pfgaddrstr_addr "PrDir3CrFppMr3f3BY1uVHrdX9L54gVmvNq" in xs),big_int_of_string "47583991231418532493092133282942179627053641822890092574221231168988555657359",big_int_of_string "93579264588998937952783241703791466683642601802282059212770537882320262483228",1,true);
         (big_int_of_string "100598692334014829267989500210555402217398070882070888190843408776452496913548",(let (_,xs) = pfgaddrstr_addr "PrDmgp5JYpHtmx6DcKUHXizJAsKMPMfFqx3" in xs),big_int_of_string "22308247711338059802166307896353815882576065414461513197505413422358105670805",big_int_of_string "17556775273521898320025535069690377527573867047637495621184893175516690213693",0,true);
         (big_int_of_string "82001324963259054604338824947065478789334714473645351223447356004642657655220",(let (_,xs) = pfgaddrstr_addr "PrAfx3jUPNY44GnE7gHx1BnKsLMg7egfd2G" in xs),big_int_of_string "11890524096593855432580935787306406802224439817120969297378860358769712361029",big_int_of_string "12509545194506626633936367778904577044754556977979415941788006144192065345253",1,true);
         (big_int_of_string "5192360077335494436873702939999999393033800962821960351385067890671869307755",(let (_,xs) = pfgaddrstr_addr "Pr6jsyPpQScvSqT5YX9ABXWUQ4W8V3D69uY" in xs),big_int_of_string "87110787097767709997464389667779801423483080634032376704375806066209500557766",big_int_of_string "30261123426213982680179276466383779360096147910989648572069981476928890233998",0,true);
         (big_int_of_string "114069442582640503556365962634095984720087081729066455651149996279504103649347",(let (_,xs) = pfgaddrstr_addr "PrQK9bGDUSiVh2syb9CdTEmqmS3t7t1ouDG" in xs),big_int_of_string "8365571562518314086629067638160009899271802350745247155437146855111368265392",big_int_of_string "34203243768970099700647024024764340831297140869619513937438751751719464542673",0,true);
         (big_int_of_string "103842844169008417481277021492488638858946056518444487046326274054843357918147",(let (_,xs) = pfgaddrstr_addr "PrBfqZgebdhegyCMZ5R7XG9q8fnHHj9grJk" in xs),big_int_of_string "32020936547846654811490628918807642273366796632578849880002619712722658599601",big_int_of_string "22310626290679158885088091509583924800332298062937445390757986001990232307501",0,true);
         (big_int_of_string "113097416457398415242914410389858326071919574082518338958673990928312486763613",(let (_,xs) = pfgaddrstr_addr "Pr6orWHxixDfEuRVka6RQB9eHQfrP6ypvjy" in xs),big_int_of_string "28205608706159517673517902151003058821697683184879622640120042008315348180962",big_int_of_string "10594898612624233216133108734997336216347777309023251686136213020767672145950",0,true);
         (big_int_of_string "24045619521560229705288588962897519875095833406392650275962985741090636535832",(let (_,xs) = pfgaddrstr_addr "PrRRBurQTikfcCgcjfzkwary72QdBtShEgf" in xs),big_int_of_string "12803867937925596113291318092471262613550289664165871874149433475325615810871",big_int_of_string "107081972455772863365825037618135260717384705445425024518486941313505405524621",1,true);
         (big_int_of_string "91275382296534106526792318648844786777232635851753646665714857940447774964547",(let (_,xs) = pfgaddrstr_addr "PrJ4fFFFWXe2xVEyZiZWarDVhnqMLUj68et" in xs),big_int_of_string "99066357883301000727695955894030506219583890411497071993870991272720787555937",big_int_of_string "102544651276212894426513615714441177393873622201858793294525439398665044365888",0,true);
         (big_int_of_string "4128818130522402662002227326259377096047228153340364913705112179914019330548",(let (_,xs) = pfgaddrstr_addr "Pr5X6PVhL8PLyAka4axS2QFZC55xfJcVfSe" in xs),big_int_of_string "38362271341368908172289654168886889362730195753836127946714734785604462376876",big_int_of_string "16212008127337498511307459324115976940004397743899901465930878206898592470148",0,true);
         (big_int_of_string "85656840865815958315315447935611253025830807169082740627329931807764528724321",(let (_,xs) = pfgaddrstr_addr "PrQudydz7W6pwRxAEJcvj1aFDhajK6koBuV" in xs),big_int_of_string "20839127916935170450212642530735362771063889789665239921572870313107883555098",big_int_of_string "95141964371576321123891780529085527060454765377256889827882829953828895453799",0,true);
         (big_int_of_string "84618716214971154528046354150240041939972999238465634662327279567931370812009",(let (_,xs) = pfgaddrstr_addr "PrDFe3PdWMq4DUmiBcCqsPkgMcN3T4UjuGY" in xs),big_int_of_string "111632100209725276752203941427904263413438140483954289374240531491740946621723",big_int_of_string "89095986244199484128271895222264282259703898718370660564371910683524688678465",1,true);
         (big_int_of_string "24785580900660765538289902617846467971244579935551507939836423902487918676313",(let (_,xs) = pfgaddrstr_addr "Pr3raQFhW3ANeMxLJcsv8hXrSB2o3ZwQYTP" in xs),big_int_of_string "24623054506788392761785480541261973914834630213206354552313456589355728047718",big_int_of_string "35644564668837306836414017095822210964440012785761630611263064260330711909576",1,true);
         (big_int_of_string "49060796272457054269145552068759760645265085920855528803972158371067189044774",(let (_,xs) = pfgaddrstr_addr "PrAbH4aDstqHy8vX2gSXvWbszTv9crb5mp9" in xs),big_int_of_string "18860541078097665066375678800501775700776702485915562176007095698001284741072",big_int_of_string "36815962688346695672115885502729602420492305978223090343706295402730862933495",0,true);
         (big_int_of_string "96476243981133133449846745828568882870148956101210396165937216048299825536709",(let (_,xs) = pfgaddrstr_addr "PrPb4ci7VSB4zomgZPRaDQphx2B7HTUDosS" in xs),big_int_of_string "7396476710438346152039362029049984768644050156664537034572001704704757619841",big_int_of_string "53304675122318636530626095606283054002394358218264292122264577846628638951694",1,true);
         (big_int_of_string "30807792594079069575504119517752357149392391512591600882756741781372323337878",(let (_,xs) = pfgaddrstr_addr "Pr5Tmnb5R54w5ZXGbaNRbZUZTL3ahb1PpoL" in xs),big_int_of_string "50083122431526701597903155447418711621907960394396893498404975794880439210542",big_int_of_string "68714407877741141491869036691300078777162060818587743166738248239831172789432",1,true);
         (big_int_of_string "24954093715249298338868238214102445430321999341883824152360514690810372710617",(let (_,xs) = pfgaddrstr_addr "PrE64CqyYPXpb7vESMjFfvmeeHnBbDFmkSm" in xs),big_int_of_string "16661016500524705034293380580482533449746843234768949482176402613261996096760",big_int_of_string "1816223022322357397241276008296900736992659073816146119752203333829739470606",0,true);
         (big_int_of_string "14084823002336028925349918574850504104989377645094624571142429318166855505801",(let (_,xs) = pfgaddrstr_addr "Pr6KmA2rhqbD4Po7EHpLWv1HFn9enuDC5Fa" in xs),big_int_of_string "92153818302253108712877673649854172545384045084141995685272830513441194607415",big_int_of_string "67958663544358957974626859437247564439010413593574862978213998226239949380689",0,true);
         (big_int_of_string "68505357876530572972616137600870544340760386141122606384861333286393697576450",(let (_,xs) = pfgaddrstr_addr "PrEJLkq8Gp73DWaRKirgxX77sEoFBrih8ns" in xs),big_int_of_string "15807653973181776964977342834201643544770135115487889231791288262138070254595",big_int_of_string "73022746025816449311741584869869706116236055978142019115382160934609506901800",1,true);
         (big_int_of_string "56074485432798888563673703474239726577730662326940992885522753098919184330697",(let (_,xs) = pfgaddrstr_addr "Pr4Uy5pkjLV3CdoUTq6uBXhFE8Cg7q822Th" in xs),big_int_of_string "66774568082125487684976851220522318486619033706990026252048501575612917814326",big_int_of_string "49107197009504761892029141085248893107442648086343966176861672658153439905026",0,true);
         (big_int_of_string "7888553621630818371678339111855585873715775148799452476246152883228134982184",(let (_,xs) = pfgaddrstr_addr "PrG8ugZqTmnZB8JskCFameK1dpwR9WvJgGr" in xs),big_int_of_string "3076320505762728498425211140480057507750182105464866634400780383679216025581",big_int_of_string "92778639648629003467664786105695234386733166112183426501402029736614047622025",0,true);
         (big_int_of_string "18317765447702683659584681744924253520731563523636010055044407380075552688186",(let (_,xs) = pfgaddrstr_addr "Pr6Az1Z2bmiMw7zrGbjTzzyWXiEV6txrAK9" in xs),big_int_of_string "76487785717207293547882570466846389630189119072961910420808000620985904412106",big_int_of_string "21956560553231719722477559283054034057675795278553450837123970717723773037261",0,true);
         (big_int_of_string "93023133289628717190378788356290775589834784460720474509445439160701259386140",(let (_,xs) = pfgaddrstr_addr "Pr3a2P9Fk4HzktiJBvJut5azH47c2oz8oEi" in xs),big_int_of_string "41831409964851520653587395607915660446059916005584399921482656492652842814714",big_int_of_string "9326968982578627720173566065943834462920768827886992446144898623952078498301",0,true);
         (big_int_of_string "34388281098180262579719792548121773845637138678212505191612695778176480547843",(let (_,xs) = pfgaddrstr_addr "PrPKdFdxDA3sRY5a8XAuPDWNAvreNg6CmXj" in xs),big_int_of_string "76559334004743750627388988603982513862303304958049857653056102778659704999728",big_int_of_string "44328356531376798257053235880645268417922591534866317702798637265193409759509",0,true);
         (big_int_of_string "70145504161182936756250022802651765585864011308714361682877028390926832799958",(let (_,xs) = pfgaddrstr_addr "PrCpNeMpYxkZAKddvgfpVni9eec8niKrDZw" in xs),big_int_of_string "12760550384839440589526890095396491174966990804048237804250370621686066047263",big_int_of_string "37010102318603506452332472961878190685100920646216336612098157661144589363693",1,true);
         (big_int_of_string "12587826255259821147145282534089244100538607998702985920446527172948541712789",(let (_,xs) = pfgaddrstr_addr "PrDdDnqpd2VNvofmsBjrgvdj2em6j35X7QP" in xs),big_int_of_string "2758293769447053288777953769339746270035383315490727712645216670524267466501",big_int_of_string "94308696790618197290053639496257806125458024490513203336525473004421225331582",0,true);
         (big_int_of_string "6997009566224980298879658504179120254789039552837479660375809072700849151864",(let (_,xs) = pfgaddrstr_addr "PrPof3ComU8paMGYA8zFdVfCyXdCQ5BnxtU" in xs),big_int_of_string "114417475148345925707344077071743930094175284103457268469728218419976013116325",big_int_of_string "14892483277312036903498348900320789471589158035060775391174386834628699457209",0,true);
         (big_int_of_string "71166293413883939814383246215192353288318401890889399490346738689861034498795",(let (_,xs) = pfgaddrstr_addr "PrAofod6gXo9H6LHSrjU9oJ4sn6CwM1QmXs" in xs),big_int_of_string "74718659067803201527174086537786887837959169426620363976864538206713154529323",big_int_of_string "15877085481118036608155558084034803471940030146461747468767493715276327915770",0,true);
         (big_int_of_string "113376713162903959397374387951473031356781784543984156959041605062180470574173",(let (_,xs) = pfgaddrstr_addr "PrLsEygB1EotK51RmY3pMn9SHRPDMcFj6GW" in xs),big_int_of_string "38496230106509784351296834948986560846902855620187321770639585578836016287612",big_int_of_string "93053567669942999355343951156267706363944351613448955743429774316688898746392",1,true);
         (big_int_of_string "113405767874927105523637977853098008341092574809654998805922343400656033957602",(let (_,xs) = pfgaddrstr_addr "Pr7pMYjWarv3NEkGcPyFtvQsZ9srwtG1W9T" in xs),big_int_of_string "50819414137409820612564365547333294663943077369589051319360504779217685933460",big_int_of_string "106547503420948744167809102964370973857751409517721039453415570730408117505516",1,true);
         (big_int_of_string "80304002900369560549122698206689565608899639334090206058053860971265313763028",(let (_,xs) = pfgaddrstr_addr "Pr6ZG5PNSXwEuLuvtrCqWy7q2wkeiUjCVLG" in xs),big_int_of_string "99226142759151187666032623813198866769097938984423084473262881427012594514204",big_int_of_string "81319823645714034449906442783416817591480069726543384230085346078444625108070",0,true);
         (big_int_of_string "26690367311628432789241203671610246387484370752759979776143526509728789966603",(let (_,xs) = pfgaddrstr_addr "PrLvjw7JVD6x5ju7VHcFZ7DuzbXKodiCTjU" in xs),big_int_of_string "82327067723771121001259204651967905918847543050824744427906666128707950485712",big_int_of_string "9362254731478599231120071541681120262939245000059555243557600748431789298937",0,true);
         (big_int_of_string "73846873887510291484300639589260807233013160960770367164091063438620663254360",(let (_,xs) = pfgaddrstr_addr "PrHBZs4TCY5qBbhPsUX9FeM2DDRH5Eo2w8y" in xs),big_int_of_string "60402011250692771769887753818080594437798354804949349610988832029880239997046",big_int_of_string "36446811845375375537189509831993525592354022760430555067414655044185649084326",1,true);
         (big_int_of_string "24961582023042661228427310114128453144172902677689288323191053305799640758553",(let (_,xs) = pfgaddrstr_addr "PrPscHqnJQDcbtiAxCAsxkafYB3u3Rrn99w" in xs),big_int_of_string "44083087351952676385542007384480655174019712064511590168806513747807470455685",big_int_of_string "29064897611780519786492913968579157591086695394734689924740040112891223049658",0,true);
         (big_int_of_string "48103956603608950718758249021382394194033173078892295627134228146650077262911",(let (_,xs) = pfgaddrstr_addr "PrB5TXn8b37fWGw1CLQuTXVFa8ZJWDUcdvw" in xs),big_int_of_string "27732426051376989283738938835808995199970349725746519925599619840210849783128",big_int_of_string "109622890249575166300046782508341101633732454735929561455310236225417761251788",0,true);
         (big_int_of_string "33197094530473779972278077176382354950560185315789025636718584444573041363035",(let (_,xs) = pfgaddrstr_addr "PrAcoQs23pnPZY2bP5iAPSeVbcQ1fZCYJ5o" in xs),big_int_of_string "16782583285391382626212098436466735300639930058839250813714239042941725163233",big_int_of_string "110455773394094577863240383159811432575925196586572806178209337456743440607127",1,true);
         (big_int_of_string "58893253833179741007725880863944539434979000903445567470989167186738679085100",(let (_,xs) = pfgaddrstr_addr "Pr3SaDHe2yanUsyFyNMESLxWx696UJsMErL" in xs),big_int_of_string "44457077141353253322433186901827907377070579014799691309231088893176625371232",big_int_of_string "51070339318753957052310357960445931237276607221003566972822289940755260725590",0,true);
         (big_int_of_string "15617294489813186898133474961700966177702505468165304836325328627656658255876",(let (_,xs) = pfgaddrstr_addr "PrJ1vNLPMtWAUHk3kcj24RWEVo1xnDdgALC" in xs),big_int_of_string "69624437094952889524405370860066513786813568820447364748579983343640203483253",big_int_of_string "107333178036492556181000538945541816611357809414465203744737979092910545539394",0,true);
         (big_int_of_string "101135946450461245787109878317118718305373308011363768269796326048050660200537",(let (_,xs) = pfgaddrstr_addr "PrEnexWDLvFg3xwkXWTDgBt3qXnBwfESJJc" in xs),big_int_of_string "90699216874937545361918544431446637949067785838736343265127948222119157024508",big_int_of_string "37631516749071059528578315946142234336833527087414833120343591779978216541478",1,true);
         (big_int_of_string "11305901522606381241595533531298113410270009370143740379401721888370714213154",(let (_,xs) = pfgaddrstr_addr "PrGw4yAPkHqdJBQzk4ou37PPJAM5f9UgDyo" in xs),big_int_of_string "22161003589604257223883556955640486792994543504983659514997938610489795453464",big_int_of_string "54555546719331815239936758416969763392534923553058995961178456281277462163555",0,true);
         (big_int_of_string "59200402904336324216812285503411537214988322125978944473756194202482925519832",(let (_,xs) = pfgaddrstr_addr "PrEG9rv1fXv53F3zqkZoHUkXbt8dg8hWhb1" in xs),big_int_of_string "58653870028072002930755046190811648739602552683684381072623461342849981005921",big_int_of_string "75591100222246316188703835251436349126121212725491531222459973608569952282557",0,true);
         (big_int_of_string "104128807302747927240398777987942828506174409005028252437792377463930879845422",(let (_,xs) = pfgaddrstr_addr "PrMS8VJH5gwCrYYtA9aTgqfVvhUxyhMHtyh" in xs),big_int_of_string "75237170755107077393672068068568142534897456450642306486554342334321662852628",big_int_of_string "96784643111891712057592569200164688062406524572134962589183671602984792069305",0,true);
         (big_int_of_string "91298994627220400658847386601914684761879449948421985258962466592380980489814",(let (_,xs) = pfgaddrstr_addr "Pr4v8QThgJK11aZ92MiN8H2MWAFrhRQrECj" in xs),big_int_of_string "107390062576131792778146298487435224489458686124313142904292212494857175800562",big_int_of_string "73842376380276004323401258651914093192086719624369663555690734694906704594741",0,true);
         (big_int_of_string "50101661983563943914410939287671918713563590512000982012623035791790242139181",(let (_,xs) = pfgaddrstr_addr "PrBjk32e1zmnbpFw8mpov3MZgU5gTrydsZR" in xs),big_int_of_string "11083658051452190113213591039311088730569610505572307507695358939508155158213",big_int_of_string "56934554270387520746485721026378795921375229446883675380492480455650885563104",1,true);
         (big_int_of_string "92918161450544843128484434423149157378342685597900874980930508625539165468423",(let (_,xs) = pfgaddrstr_addr "Pr86LSGwsHJY2QNaA5CA4fKvzRu1dZxdKEZ" in xs),big_int_of_string "49308660223207913550824964108080592954504405355916052125924684582671446796089",big_int_of_string "44721021735969038771881164735607895244474221656594276630227503768928767157929",0,true);
         (big_int_of_string "58531402281049727450705335435458153579506428171258810624043559204419437413039",(let (_,xs) = pfgaddrstr_addr "PrQ7xbStMxKnudAMnCARqBSSVQKpr4EHMo8" in xs),big_int_of_string "19042864428737333711911846522571387714700936991975041968415075536540458905317",big_int_of_string "2112216491683221100313437293376721557703970132628914021599304133644593217907",0,true);
         (big_int_of_string "88639064074851138414955190784830990052544237616011916147233340144406770890163",(let (_,xs) = pfgaddrstr_addr "PrMeRcQZVEhm3kFSQzzpCRDVPPCTZmKFG3j" in xs),big_int_of_string "60538807276678116482709698056752087240083479284669092449593784215094359220278",big_int_of_string "59714766938082224714214828802719403512666997992986308020456897086444678806422",1,true);
         (big_int_of_string "27904295066835879697915954607978884791524241433988751813795225319314814847148",(let (_,xs) = pfgaddrstr_addr "PrRPttCCYUAt92FcrdDc15XLNjLcPYj7SWb" in xs),big_int_of_string "90624058634867993710137935319906756474638321160452484014841396872959878521727",big_int_of_string "36041359829998681549267466672127294292475303060157670943615364702727472953833",1,true);
         (big_int_of_string "61310051485012798860689181459815024401385689920023228090266948518557786985258",(let (_,xs) = pfgaddrstr_addr "PrEBzRDHhXf2JHXeKvaHUbMX6oRAyLmHyJk" in xs),big_int_of_string "1821746744425967619094144364061786634407254205571125654724443747018490901222",big_int_of_string "81473439614841200045541229672184783831735276693163976494947379473541701103323",0,true);
         (big_int_of_string "57435872594574610162390706049115362389855053702027209182626064100698436450816",(let (_,xs) = pfgaddrstr_addr "PrMTDqYTjBckYXkuWwCod6wM7ivxhGK2k9G" in xs),big_int_of_string "12997078598509733362908703925995143676189564866976892639947314332611609677204",big_int_of_string "106400488543630476679548054466451320157185930452116273669968673008826742094541",0,true);
         (big_int_of_string "48783825808911561164152767776740223608549975620651657811191323707064927993449",(let (_,xs) = pfgaddrstr_addr "PrMnnVF75wu8extdM5R9PYZQwrTVahJNA64" in xs),big_int_of_string "19940851360281361853562558695758929628348316661602913255607823379165904245306",big_int_of_string "24779282028354663467869147181776948001935964283024857705249419949678395641567",1,true);
         (big_int_of_string "19509172015737788416746780555459437151938543690387436271880314677190767754746",(let (_,xs) = pfgaddrstr_addr "PrRGyGDiEJ7XyjPSFfqFEFbzo86W6Vq2N7X" in xs),big_int_of_string "62946289983044011230339456307337626756605438447817407668065587067348740332748",big_int_of_string "100876461960930065878976494436866206307230132429242696369367252608061591806209",1,true);
         (big_int_of_string "13015217513439634607886519386502599784520241150111785768223148724001888167072",(let (_,xs) = pfgaddrstr_addr "PrE64CqyYPXpb7vESMjFfvmeeHnBbDFmkSm" in xs),big_int_of_string "89875103409400183971123798632006053664759549665715307633974502480877229744175",big_int_of_string "16220153103072929805695308548897129589798758145567200762725913481502883672168",0,true);
         (big_int_of_string "10786099413863340057340711725275371976832999665953041379600037661176059418189",(let (_,xs) = pfgaddrstr_addr "PrBwSq9PNaa2yx8s9N5as5nybCd227QKdyc" in xs),big_int_of_string "100399919119387868849458901912053297941529383280895420851221671143595371684549",big_int_of_string "46519945110490546175882538661214697735579727837907982905371663123675038358482",0,true);
         (big_int_of_string "69179911562380197285002808220923408914605486184850306517827906399620840276606",(let (_,xs) = pfgaddrstr_addr "PrCmvGi1xigWFFE8jTyVuQMojNzo3C1Qzim" in xs),big_int_of_string "61364317225244988974577708809270236068590656956401517317618766283986338464759",big_int_of_string "49831475882262970254034086649018544390118386647664852365196162032970322294376",0,true);
         (big_int_of_string "29085059513948977937505922711150487168382508377547921718044841235950511032772",(let (_,xs) = pfgaddrstr_addr "PrFZ7cY8bpcMDuf4MNqcEin84WEGZQnDMyB" in xs),big_int_of_string "59106269188121772320333535557599606860573531565694423729447336458720642281781",big_int_of_string "20981555798399085304882572022972765370158601125330470818342172324491446436585",0,true);
         (big_int_of_string "66036832968706057480687791270133666427122437139569582523323326439901470293140",(let (_,xs) = pfgaddrstr_addr "PrRMqXSCk7jNyKCcCYe75xqUww9phwCLhyv" in xs),big_int_of_string "92694033747295430434217210656407724709436010689171860554385989023007049273468",big_int_of_string "54295996030741519086407445582025776109719846300730014792730262732384671976454",0,true);
         (big_int_of_string "5767883043196027537253445822983587085762386913233266768653660651312051559568",(let (_,xs) = pfgaddrstr_addr "Pr8uzb4DZtYs9GnLYPH141eHSN939eRLPYb" in xs),big_int_of_string "3453578157546390744176140157672987124905774598891403523265374210801697250302",big_int_of_string "46575285915593423908881471459620952304777461378146131203025489769908980012444",1,true);
         (big_int_of_string "55665706071318470350929899909910440973777302193061829447339523362299235171579",(let (_,xs) = pfgaddrstr_addr "PrEzSnFZxAzRbmDtdedFHPJQ8kJ7V1eKs55" in xs),big_int_of_string "7928379485728786774420944107618965322173280629614590090920980353010094989746",big_int_of_string "82007943197278701585024634218678870548266029131990510939676591699389464919581",0,true);
         (big_int_of_string "37588283978620948984751555022014750037147142551774688744166067538312890372290",(let (_,xs) = pfgaddrstr_addr "PrQ396pFFhNK9H6kiopSNvH4HeDYsj7TWRU" in xs),big_int_of_string "66122765521926715894673932086659204627416517149413084022980236925051466226197",big_int_of_string "77775281894218082326929574501583675063939198834932968453566157990180460322740",0,true);
         (big_int_of_string "115204809142159727989320734458147668687470614716411448959521786331673333541166",(let (_,xs) = pfgaddrstr_addr "Pr45mjJGGN1gUvbDWXf2kHaNmKPjEdFj1P9" in xs),big_int_of_string "11535326666926475970464074139191243561042810396328138665365683248853366510171",big_int_of_string "37236565047597769308208411040067544364389298882535274370038479020164593829683",1,true);
         (big_int_of_string "97724074461714612854613802994909462994489581763121046399478681335651926780757",(let (_,xs) = pfgaddrstr_addr "Pr8vyL3uxpUBMZ1sWBpijKE6aAAeRJMjjAq" in xs),big_int_of_string "3090426149983179556597392480637290063428786284773858472095611468967096716844",big_int_of_string "115704492645677397806795590703546041836583739207494107057541771860092182787575",1,true);
         (big_int_of_string "43658607714765867994029986055892432913789139079965315207489139649254861697794",(let (_,xs) = pfgaddrstr_addr "PrDn4PM6SDEQsDPZnVrd6hX7Qs4iRfVGBTd" in xs),big_int_of_string "83852474992011212450803442061464319357993290234112884480257949827821543011950",big_int_of_string "65858717256046694939827573774888670299243442762869939975740103272000332034854",0,true);
         (big_int_of_string "52821888713628485715664169516761583049985475821586890593250625928529932325161",(let (_,xs) = pfgaddrstr_addr "PrMBc75sBu4giMksM5x3BodoFn3zkEymu9M" in xs),big_int_of_string "79711882901301993787990463059004964630074622869291449663241996899490131151868",big_int_of_string "44853262316680623935488429489724006935577958191363100988567019935319569208034",0,true);
         (big_int_of_string "105855845638140601507646718121809305315902468425559916685067433329085407844006",(let (_,xs) = pfgaddrstr_addr "PrC82RYz6gc4sJV8hajXbHQPGAbZUnx94by" in xs),big_int_of_string "48566694648892526896482190792301681508291291064413360106979618404259435565680",big_int_of_string "109942474798860753579212359910060407278906714683094267262212531354780052478446",1,true);
         (big_int_of_string "7095800513427290479837719298440686924649287957632589956793982045087385935458",(let (_,xs) = pfgaddrstr_addr "PrM3zpuR1nw3gexrb89gMJ3aNgAgfJW5WrL" in xs),big_int_of_string "50452771282451810495552702871053047273230025512413550492837180024438852165699",big_int_of_string "64772000415920836049833694410071348344424446147013074122015727049702549386509",1,true);
         (big_int_of_string "53741132036468597544315833336135792871051054541166952886553481990074915513978",(let (_,xs) = pfgaddrstr_addr "PrJGcs3ARwMMZ9SMGymXVPuHYzsBuXCBRUn" in xs),big_int_of_string "42137159457354903772760530538036895086708686206751821480561986295810994394534",big_int_of_string "59579659435566907159372815190104239828809535192718615304566532548232019936446",0,true);
         (big_int_of_string "37038288653049854235031871844673458938427888475943030319179364346052864604958",(let (_,xs) = pfgaddrstr_addr "PrHDC2tozq3EqfkPjqpN6AcJzsD7Q4vRtLE" in xs),big_int_of_string "55908656564879074106630362953643899332710410794569585628140855748294465864025",big_int_of_string "16442902690874057971132320516277822592024617265218565453210889497660571958996",1,true);
         (big_int_of_string "38003718878366360640813210547402381817959815010575434737964383884841470348739",(let (_,xs) = pfgaddrstr_addr "Pr6vuNfxKu7gWamW3WfBEMjTQQUmTtHVaiE" in xs),big_int_of_string "71135658137742267347662846836496609592720903509535738660191145026863204711131",big_int_of_string "109939282854170133447242372858189228400959092375733848087256867742946795628012",0,true);
         (big_int_of_string "2520488533029361530411471411061231407078333982554684512383531946490751158986",(let (_,xs) = pfgaddrstr_addr "Pr4eqmWHZYwCMWjiCKGMjnpzpLB48uwaGTF" in xs),big_int_of_string "59799297177470377276980384935444719749173382961437674536901910206445449672689",big_int_of_string "37684739789094210006096781730528256585099586685272595238130450752707062932225",0,true);
         (big_int_of_string "63822829565135891216847521724427648530264182322842504698890034323305092180504",(let (_,xs) = pfgaddrstr_addr "PrPEwJMCK6hVSfhGwGFhNAdAJeGRFGMyFyx" in xs),big_int_of_string "87936873574674678020645458365761513291472970889225852428178240960507095678041",big_int_of_string "24898715346675515498003344197134772079612605216993255498310971859910358307396",0,true);
         (big_int_of_string "11702741944934351223130905559615109230258174877166314040577622670838452332909",(let (_,xs) = pfgaddrstr_addr "PrMnGiieLjL719nGtySoDryQbBW2R6rFr1N" in xs),big_int_of_string "872442993173318629072093350583892420970673121224932764191320933998855502605",big_int_of_string "1871739305032077588582701787577902758107550221965085910800771363635953767462",0,true);
         (big_int_of_string "106413554664915341443653324753544853636668720724537307546172257699121405479182",(let (_,xs) = pfgaddrstr_addr "PrAhi31mpebZMtpGAjKzbpVKC9LpuVMVNJT" in xs),big_int_of_string "68245972397272842679701260125785179494226981831632960797784184752023547947699",big_int_of_string "104779941479267248174865654082498023533798668059318699815782279671858036567891",1,true);
         (big_int_of_string "95221181885445971379496836025859182547469527861290469571935235527198652627406",(let (_,xs) = pfgaddrstr_addr "Pr9jVU8tEJyLmNj2YaBoRPyLJatEyndb3aY" in xs),big_int_of_string "33030918595516961560019122981231442751425907825710510758261521236774286855844",big_int_of_string "42786601515758478964821003165132014591197860939395120119114009500461165300173",0,true);
         (big_int_of_string "71003759791795769115086427346004399269085237028990038838909542338672880032072",(let (_,xs) = pfgaddrstr_addr "PrC51qfC7E7BawdASucBP8eBXSxmbH5p6vC" in xs),big_int_of_string "62732694372096949593149317314637360807888668785276489495646460217630796623425",big_int_of_string "81568062936613330656364538139506692292080071026510699117945218001193182662522",0,true);
         (big_int_of_string "27112042101879824990815762383091618156288377814007660317441120645351798661164",(let (_,xs) = pfgaddrstr_addr "PrCxPB8zwyu8XDf3fAR68M2pVBPiBpDc6gF" in xs),big_int_of_string "28951011475402640040978591721664941685037969241405398887820418439794274561890",big_int_of_string "91003325433567282161279240443593304104657662299781596762385045392792749109702",1,true);
         (big_int_of_string "36716031879998943281926946569259988820107361065151350940431523488566186231488",(let (_,xs) = pfgaddrstr_addr "PrP4Sna2dBBCE7m9m6TUXFQQfo4FH6EWPyr" in xs),big_int_of_string "95237416348887409138267407970160570024432704360748793147282141474096671539202",big_int_of_string "30084749311515827429117576053821771623032864671257419643254933084976075684325",1,true);
         (big_int_of_string "56051456673996516221713515325167361387165200515399380507654742037097792704326",(let (_,xs) = pfgaddrstr_addr "Pr6o9GnYkkAkYvwTG61aiX9TQtsZp9cmkDu" in xs),big_int_of_string "78637737564072582727674665331244521221250915075094406803288012783449734048698",big_int_of_string "35482358121717014749521828260667304027305869053924377688530131224470363365599",0,true);
         (big_int_of_string "101695736368839979465058995052214460812136104066172489762734886284122762183096",(let (_,xs) = pfgaddrstr_addr "Pr6wSVRF8bNYq4Nz8JLu2SPEqGWfLoXJn3c" in xs),big_int_of_string "45881317817060088011941023885916572512680849451702988420690714050788389656",big_int_of_string "68051216055798899699980239111296619470943888107911655564811523644563891718998",0,true);
         (big_int_of_string "43852040969097563927482002782928091556571881905274512003045474708630911261647",(let (_,xs) = pfgaddrstr_addr "PrGXBCLZCr35VqTGSJqF9A5anrZUPUczWLZ" in xs),big_int_of_string "104583388713667028687568133495543581941419743166849754448607435356461636150375",big_int_of_string "19497025271473669051891581806052874150200722943820588720034255896872575338592",0,true);
         (big_int_of_string "81505797083650202623385958262467451448421355297703399475611506985966401320637",(let (_,xs) = pfgaddrstr_addr "PrCpNeMpYxkZAKddvgfpVni9eec8niKrDZw" in xs),big_int_of_string "57983385768484858796350974435407696751131746969418541225602399831804626277582",big_int_of_string "74799213701152980731304428966153284236631304574963553219571974597198896526499",1,true);
         (big_int_of_string "87076044836172900834430841593287924600453403984286769097997777384664692821528",(let (_,xs) = pfgaddrstr_addr "PrPX6PdxvgygnwLQdAeJnXoihwLHLUY3vgg" in xs),big_int_of_string "105381527896492606038820690298951563756790106466992234853558887781586084051407",big_int_of_string "101331268701777738079552041776486286075805361555766047113899856170859052495666",1,true);
         (big_int_of_string "36564862394400178953817589849837542631005598288947247501492761451480293283186",(let (_,xs) = pfgaddrstr_addr "PrHSLM5LFaPiQnSxgiXpc22Mz6qye9tFCSN" in xs),big_int_of_string "68031017082239293751925266512326914192846952017152064145191663876059378588458",big_int_of_string "6975706345321657179951427719103236584897154180953600207729727771840276147282",0,true);
         (big_int_of_string "81178323297122259327971220521800269180472301069065218806855711855826687034355",(let (_,xs) = pfgaddrstr_addr "Pr4AJUWeyiYBaoynpxRWhgkmySjtHcjH9xk" in xs),big_int_of_string "25602003104541247950121396564569112032817283096972084934189265287481676280408",big_int_of_string "28592154369164616926357696622388960433618439436425535403332927772146929860779",0,true);
         (big_int_of_string "91571408415768754246256250542419419945535078366176814081168502028742881435023",(let (_,xs) = pfgaddrstr_addr "Pr5fYf5JyCXEaFyVH5fdqaHELCL2XW8ccVp" in xs),big_int_of_string "2817761204030180586207164684605736474347454706821061162946365824703365402453",big_int_of_string "20586300991793681071359179986513747155595461047089193607657470353264159041708",0,true);
         (big_int_of_string "8846373280856618402055875429333325123273826074703975508986466668480633901040",(let (_,xs) = pfgaddrstr_addr "PrNLEbear4ouPoL7oCsntDmn5eWq1VhUkAa" in xs),big_int_of_string "57727291935409905176908929301531652677966794911609215012324125990456769814151",big_int_of_string "81948042720766186250948012673780866671867623880365431669098325965399747780410",0,true);
         (big_int_of_string "26817303579560704148682638236463004409006710753759016979998079149526135776233",(let (_,xs) = pfgaddrstr_addr "Pr6wSVRF8bNYq4Nz8JLu2SPEqGWfLoXJn3c" in xs),big_int_of_string "76743707099960257846279576334203667534181706993689192311066781776861022826823",big_int_of_string "79144499226474984262435644262945724021622462927565514306795746910576341093874",0,true);
         (big_int_of_string "49220792911876712338395712602566582448378690376460154027897689376164484351645",(let (_,xs) = pfgaddrstr_addr "PrQLVJgBG5BdmtLtLwjFDELBKCaxsfztBev" in xs),big_int_of_string "115096693114691594574336864908826892918626905481680842349375141506691081446565",big_int_of_string "37649790015683059190090273402419571981734108417899903585733421888925822216911",0,true);
         (big_int_of_string "77512019351436251330876618181829060768169388920707917724507386653120893790050",(let (_,xs) = pfgaddrstr_addr "PrFJBDGC7TCePg53MAbcNydMPiVUYFGcbrj" in xs),big_int_of_string "21389782750854248365384469261191837090136865287617474243637352086009374549857",big_int_of_string "109809577422415613983608241933745067223395651990229612641616212420864823480668",0,true);
         (big_int_of_string "75023620223887019396080149289054905162944583941215226747089344650069366858682",(let (_,xs) = pfgaddrstr_addr "PrRkbw5fyy7KAqr5KpUGxZVd9ArhESf1ted" in xs),big_int_of_string "108534474248048754181979758604319938743299607877724579996915087033484448982786",big_int_of_string "1767012850568908953367418847333475013344508471461799035466608084266144843747",1,true);
         (big_int_of_string "45107676242436083952657251699411769573448008825265509500122176893127432669258",(let (_,xs) = pfgaddrstr_addr "Pr6HNzX11GyupN1fb1kPq2BWCroNibTAbmY" in xs),big_int_of_string "114895714965138219782606094234694160514993604807679082091443581389394156995321",big_int_of_string "29191505430429937070865278148956999884692973343394091597509595120071456538810",0,true);
         (big_int_of_string "64320327303425854136954822587746857985759722957264829759606524964469295522304",(let (_,xs) = pfgaddrstr_addr "PrKCFqr2ghgVdPjYmJ3RUDea8b5T45K1fo2" in xs),big_int_of_string "70081817170871072229825811646462641774705936684211736266347029525107768407319",big_int_of_string "73432696473208593668257562074832808691988391523086409430206917339154201416009",0,true);
         (big_int_of_string "112160094700827448125347224461083024214071822584666499634637141540084597335974",(let (_,xs) = pfgaddrstr_addr "Pr3dss1QsopMbBZmuXkJdjdGtcxVRgqxHs3" in xs),big_int_of_string "57329547956122911958942737906634228501454326974237054380316674652702436734891",big_int_of_string "29024250322989704560426966216644853625348905445587639127456772968323483904400",0,true);
         (big_int_of_string "84433628321901967370795563123695156609112457321211608711543486923357809991392",(let (_,xs) = pfgaddrstr_addr "PrEG9rv1fXv53F3zqkZoHUkXbt8dg8hWhb1" in xs),big_int_of_string "9666550858032783404543889693645166336085159738193121412923700672617433093921",big_int_of_string "66754122174986811192809445980722350462378719436021264258092483409152845333690",0,true);
         (big_int_of_string "42675596059229131571689206301428939030370274985546317754019280111876444425583",(let (_,xs) = pfgaddrstr_addr "PrEnVdhacebL5Qd86fD2hBsKuYjxmt4zpxF" in xs),big_int_of_string "69512174442463525055811101538339097081364560341684613581972357134858591983974",big_int_of_string "15974977343336526878340036889752747140752414263160057002178499263886563561062",1,true);
         (big_int_of_string "109595433602674963481202647787301569142709211917579058061844361285562321394007",(let (_,xs) = pfgaddrstr_addr "PrJMKu7y9pGz59PbHHh8R3g1KCWV6LyUuG6" in xs),big_int_of_string "95684594174699462978729325042447657303151556788288447961674831953780714945645",big_int_of_string "31848387074483707143717434510920497539224561232344494986371092915673102187366",0,true);
         (big_int_of_string "106329027480575971532326381287260623845239685573169417664850657982579265079555",(let (_,xs) = pfgaddrstr_addr "PrKVNssEf3kc8ZRheGE7aCSd4PgY1f7VzMv" in xs),big_int_of_string "46004142163144743435214625578240438330663890742339120710969689167147875656981",big_int_of_string "17816279997920842773834237167663575787440410110835970427056578695567738518360",1,true);
         (big_int_of_string "115003560658832916494988875789470786331064941618939778167673986010031877000450",(let (_,xs) = pfgaddrstr_addr "PrFrcststKpdQP8YUguS5Ysts5gWq4JLNxn" in xs),big_int_of_string "70823507703664091031890767044679165640374831836478651710880661037666410134716",big_int_of_string "36336252425077949156829232889358166641868054715062794309095503277129157065308",0,true);
         (big_int_of_string "38392861343350427791526189317593791043358378898726764883066504986477445409889",(let (_,xs) = pfgaddrstr_addr "PrMiqBYFTuxAcXznbP4QLewxzfZwF113grd" in xs),big_int_of_string "98404853313242183065244637704784463366649216274824661644161776467254310139800",big_int_of_string "65254462132800474561659711580849112473135102089904564792896959310229486137878",1,true);
         (big_int_of_string "21101421930491647484836864361181059450936769202012378779814246987109243208111",(let (_,xs) = pfgaddrstr_addr "Pr63ExLC4GwjqEp5RdU4uTPfqbuKUczU7jc" in xs),big_int_of_string "7372177671422215832905250873030220891449541152818343358702311229931567389707",big_int_of_string "40360211416835423830848320466128581885324019089172485605347387830540664575319",0,true);
         (big_int_of_string "51543240957059655984024145807888596367480128225774677453038565714351860367729",(let (_,xs) = pfgaddrstr_addr "PrCnHvYyyHahnQyAA3q6Sn4M2oAu46b5f3d" in xs),big_int_of_string "6425532983118239126240069500736339456665650171688924592809263523614222830426",big_int_of_string "17742607774600151242853721389328069876281990694560381971034078937425283431735",0,true);
         (big_int_of_string "85063755525063890045542673933736987861619499959139830242714457979941353424937",(let (_,xs) = pfgaddrstr_addr "Pr6jB3ZcNxGFSWRex9jEbUBKxPeQvWVJpFH" in xs),big_int_of_string "47800219258768896376562954853121783223944925846559847103278638130984292214007",big_int_of_string "28291406647796992356927443167547628000514517818673250346053424606626616462504",1,true);
         (big_int_of_string "72912944075006926393110537068301775821918566951695404509954141874953660970934",(let (_,xs) = pfgaddrstr_addr "PrQ6e9moBciC4HuUcBFoVvfH7NzGTimbRHc" in xs),big_int_of_string "32035371115990947786627586618921154462220437684952099541037279498872269546562",big_int_of_string "100498665725579118696957143665268843559623718136577114159497285795846245804782",1,true);
         (big_int_of_string "56155631483069887210175720062374968021771022663232013270580413870094762819130",(let (_,xs) = pfgaddrstr_addr "Pr73ioYKxyAwNg5jLFe3QxMY3e55vE7Hb1E" in xs),big_int_of_string "1605306277824406178660653281710185735212502746756897283043503787791030697026",big_int_of_string "95031353898251938975655177944570550822445174275367517616176800156999623081189",1,true);
         (big_int_of_string "61894977551497686377182375019437091838273526452779419744918255292649119507529",(let (_,xs) = pfgaddrstr_addr "PrM9vakTwC4Z6gCt15Eev5Bzsm23GHDN7E5" in xs),big_int_of_string "95821573153440763958355053218073455213843752953517707080207108162631094219555",big_int_of_string "114300163675374319222288273583291472293117366533588255118093312107753064297885",0,true);
         (big_int_of_string "48544131333654653758542048138280160418456829837083270118626683516787250594447",(let (_,xs) = pfgaddrstr_addr "PrMG3Rp8hre2g1rdTte4iN7XofUWiF4arpn" in xs),big_int_of_string "41800644303127014692598411275967132539825317125932349586124809744766298812556",big_int_of_string "32816855605583064900706508757760065582216258969721200278469586503150008274387",0,true);
         (big_int_of_string "35479377315165271984362720325375103036009415542721483285134253088930942909798",(let (_,xs) = pfgaddrstr_addr "PrH7MgjbAof4Xymhm2stNmadXarnpz1iGsH" in xs),big_int_of_string "95483142929345204647222297592218085867093346724892356520661573311885762557105",big_int_of_string "20785550263786229484688582164275285226543993062416848110194785311393558187423",1,true);
         (big_int_of_string "95294548123761886022559772337024158013184902890121527885919165545709176235406",(let (_,xs) = pfgaddrstr_addr "PrS3MZCatmnqf7Ff3czACsX7xWASeq1rfJx" in xs),big_int_of_string "103586280579464251835814658317715085485798929640060447879123599469787505881108",big_int_of_string "55911862366593290383515257005143280717666242001315718116988832439411073391360",1,true);
         (big_int_of_string "64913286750491506590300420367897205701684529958966943027184134085234793392631",(let (_,xs) = pfgaddrstr_addr "Pr6KhCyBaHcoC7JmwaxCgCLg8RsvQAorpwG" in xs),big_int_of_string "113378020475656027915156350433927634816623164468171259072238898080267071941086",big_int_of_string "10627700551059432698992708449412992366369280008339596761023678475034725151573",0,true);
         (big_int_of_string "88086749739609428421948504922345750967617411188518611223979619805339961674124",(let (_,xs) = pfgaddrstr_addr "PrECYFV5TAcDgBcyoibsB9kxUf7EVf8jfZQ" in xs),big_int_of_string "82197948008242692849683368899559293932543341354653264541557548568924051196415",big_int_of_string "95948755629998828054775829934805217300839023177968449858310359704263691384065",0,true);
         (big_int_of_string "51377712549336081294061374244278176461353440920789306429155019857292250999342",(let (_,xs) = pfgaddrstr_addr "PrLd3Rtq4XatFvNNSc9D1QvoRtL8qjb9WqY" in xs),big_int_of_string "59595741088054051493345502688278678777918633351936762995244591624970700403257",big_int_of_string "28760993852193776196881513253692093352942720341297659361163838879398474811447",0,true);
         (big_int_of_string "55482138406973857627597470715138755451289253568969638926109576796157826466196",(let (_,xs) = pfgaddrstr_addr "PrEDD6nS1VQDJdzkegxDf2xNCzzcDJSyxa2" in xs),big_int_of_string "106389387298592105909388827215532253666058158843306138264326506711627923816514",big_int_of_string "46401980400009885395699574849093159637757545542321526796744705223319340587191",0,true);
         (big_int_of_string "34019433130840004612662852766508227626203736337063619814025501412298454199515",(let (_,xs) = pfgaddrstr_addr "PrFRpnSKUYoMxBwquMfSKtP4ehXNbnfx2vN" in xs),big_int_of_string "65445251295475364467674826264917500691253993630160676535754023724197235675211",big_int_of_string "41909425682464044222370610894642311725241077322388993990303230449984281536616",0,true);
         (big_int_of_string "69261841324055289102657514995555428271851622020169915397075561805197173853640",(let (_,xs) = pfgaddrstr_addr "Pr7Uy8eZEb7TYxgkT4kJK6vhznMZND7bBFq" in xs),big_int_of_string "18677089351097105326825285928445588650430660728095410249272338505844736484965",big_int_of_string "48615952584794694467907287405946521937914751643333091240531782777539738579154",1,true);
         (big_int_of_string "20088782642845517072390481577286979206639499277355811475357483315428293593140",(let (_,xs) = pfgaddrstr_addr "Pr45mjJGGN1gUvbDWXf2kHaNmKPjEdFj1P9" in xs),big_int_of_string "18220139012304411039776500061439611084624268986586193893971450070528234427693",big_int_of_string "110947833257352500741470207022963194521850608843368660552745388064221890837561",0,true);
         (big_int_of_string "1884791495519292245634676426606251508730160412187019027161187628316654656069",(let (_,xs) = pfgaddrstr_addr "PrKVNssEf3kc8ZRheGE7aCSd4PgY1f7VzMv" in xs),big_int_of_string "22427928308390390770242113700176784361001654359247771941526742397819558230706",big_int_of_string "100075454452979547593406608821204321882778783743640459540029955633118429799802",0,true);
         (big_int_of_string "28137000734936737394593020877544939650432876552142586495847585731662029532542",(let (_,xs) = pfgaddrstr_addr "PrJJ5fn5AacJLcJkxNvzveH8C6jbK8UeGrF" in xs),big_int_of_string "101259066532621248631445448818153705960868243521790215015606119719350294393022",big_int_of_string "48148609639103450393329326813286167945484511289491310781326094151932603417216",0,true);
         (big_int_of_string "28218510981003238749108750159103236517093197165723891731485633940506125799466",(let (_,xs) = pfgaddrstr_addr "PrQ976UYS2Z5ryuLQ5xkkmQVGsf2xTfsVmp" in xs),big_int_of_string "70040233205025768471535629554749602164278795874968805878130139300441805705532",big_int_of_string "53958378212609131679584210614234114898522669849023166463706423887367032217794",0,true);
         (big_int_of_string "2335858928901950548254805569947845309608213685621196639837216428523398188395",(let (_,xs) = pfgaddrstr_addr "Pr6RBDP4AcUV1CheSEsHHCHuhdJYpa2U5WF" in xs),big_int_of_string "54824330876069538036240448143752090520810422354631204728463671852204915882861",big_int_of_string "56738511658090218892264278462051405656064297102548360419405697560520235647280",0,true);
         (big_int_of_string "35962682028665152027314654280331380920717918210911034561748909827806128679798",(let (_,xs) = pfgaddrstr_addr "PrCciPS7LeEaEQkTLrBm8NLStUPKZ792TrS" in xs),big_int_of_string "46943225323069757093268887109133322412418253987674738138947128037886635305376",big_int_of_string "7214404811661704669805086894982892343425716175297885420366160716718489392409",1,true);
         (big_int_of_string "53278532176227066042245229481499867244082097557799124297264856202871251387972",(let (_,xs) = pfgaddrstr_addr "PrPs1cXbzXSBBTfk6KmCqYjRTD6cb6zSfvs" in xs),big_int_of_string "112217069400717331435531361226046347433240025941056735516172510367171592256412",big_int_of_string "34758967049725136681918646151749948426113828503956965302027109819247237853560",1,true);
         (big_int_of_string "33096768758947644706514935401417012498000125836736543258402623411462525788190",(let (_,xs) = pfgaddrstr_addr "Pr7PpJdFnV1hLChN7bTfUVCE9vXju3133Pw" in xs),big_int_of_string "41641022173946429754577516572195824911214729955420573055702897277390253856646",big_int_of_string "103041149958599345997419886082567415098892207701865896068639569363149171520157",1,true);
         (big_int_of_string "27801424157276704978687425741943204607244378801941285014272913306000825311329",(let (_,xs) = pfgaddrstr_addr "Pr7xJZT8PVxwvrx7vpzLBQwoZ2QkaUuUo8f" in xs),big_int_of_string "22048299702809092458661234140948724071171311057302517525155114260355258845608",big_int_of_string "39996680429713256993890178215030796887762770207187967554453843803303597006792",1,true);
         (big_int_of_string "80963478427191069173784327550900301091799280355644913340453249907292172377216",(let (_,xs) = pfgaddrstr_addr "PrGGf4YTzeHwDSgmrDAgV3nSHtYWiQ9TWQ1" in xs),big_int_of_string "91781096515350779073769230827753524120247450449331336514158551355626933925071",big_int_of_string "74660393563384267075176995619577787678040233569996543048509601695663875087804",0,true);
         (big_int_of_string "21509700589423623157419352052251819196261287264996206438432250554393724358908",(let (_,xs) = pfgaddrstr_addr "PrPjeHDw5u7i39dxK3M4zi84aaHBzgHDVts" in xs),big_int_of_string "107960767605301790442468571144154919630527279206089177101587925979972596556173",big_int_of_string "108665202448264672830413192337165482713310317832640276632836416958724382622643",0,true);
         (big_int_of_string "112430028737433440234895262393365484351472978728743985026913474072793752836348",(let (_,xs) = pfgaddrstr_addr "Pr9uVYX1TL59bh4k9g2HKW1ejvcH9kiyzVn" in xs),big_int_of_string "29767020435124339790865514451592745165004780323443266122672096883845941536823",big_int_of_string "36671517180947885304697605955930645740099995738787522171647562453690408395841",0,true);
         (big_int_of_string "17960053068983066994340011481782472107884070247006894466341792171438011120031",(let (_,xs) = pfgaddrstr_addr "Pr5RAtyEar2ExmuqNikMGdvRB26mzX6CMAo" in xs),big_int_of_string "34598451248965115040336585909526194943685850610597931647553417219230919381004",big_int_of_string "12204723147500764265401463254701883182836329312264229440203732438310615639572",1,true);
         (big_int_of_string "81941123360218186147315065993915359826408773654321475829811747540236235223291",(let (_,xs) = pfgaddrstr_addr "PrKWGipD6SN327WvVsXU6mDALE4MbnGhtSA" in xs),big_int_of_string "10250388875910070984408090087993254682662722050545321133431342439219764361589",big_int_of_string "93750316221490830885214633169399488740144199002081846992196648179200958252190",0,true);
         (big_int_of_string "108253406766234156949555645056667933850899839403631218293031348848094200174007",(let (_,xs) = pfgaddrstr_addr "PrMdsXp5utptJfpor829mtJ1qfRgZacqodF" in xs),big_int_of_string "19184998729661126085255851686408653265096315982435247727541527952870240128441",big_int_of_string "47266567674194698461600348404679965518384901590907616803526877823448673854069",1,true);
         (big_int_of_string "20548743895444890082297090141152234661625382105459842950697604998834195166205",(let (_,xs) = pfgaddrstr_addr "PrAeosCaAbRxbUxiqY9euGQXvHLXpX4GA3s" in xs),big_int_of_string "19986706078978615524102427639798140236779483882462263201045882465471211338933",big_int_of_string "68564449919652065370130329897289694107072651120066086297727664006386637862354",1,true);
         (big_int_of_string "112152250601670836486118774556984445704068121781930706543252353932342727317536",(let (_,xs) = pfgaddrstr_addr "Pr7ytaWVYr9ic8VCmg1KrWRF8dHZuBJKqwk" in xs),big_int_of_string "917877336890725099380056497297804273837771532630289151086405446306263012128",big_int_of_string "18519991103597706972545638937510214606343792779546486409969352924200812843549",0,true);
         (big_int_of_string "59874903192543825297870280309105150912581288850252640001795317743606912557524",(let (_,xs) = pfgaddrstr_addr "PrK27MEdw93wV4QcmFBJ2kyeaQ8wvaPWFMa" in xs),big_int_of_string "107979995984666471481178820015033587878913324622898741824069229632486440748344",big_int_of_string "113554552537934412162447347270470974212203436253036865990289623530616455780566",1,true);
         (big_int_of_string "109522607807933635774995153333926965249076584728528383928918650494735161204013",(let (_,xs) = pfgaddrstr_addr "Pr59h8D4k9dRqRE3sabtCpo8LqFDVh2Gbot" in xs),big_int_of_string "18621000480664523936607137377097532146959190110930296000092341129407718460205",big_int_of_string "63031182481164123378586112320218589338513130954203663720822858704976560351061",0,true);
         (big_int_of_string "109719428928243735795162711317394901741541835615818893742213720037523049148961",(let (_,xs) = pfgaddrstr_addr "PrEUcoSX7Mb2xMyBgJdimToM5TjzdALsx1N" in xs),big_int_of_string "108661336861079141678315753393902994705249362653635203867025776534460791474828",big_int_of_string "104336951650208714432301351109915745332875196885340599942395990616251993183551",1,true);
         (big_int_of_string "50318465621691403465494990676623340509674363179144912364375006036970948190156",(let (_,xs) = pfgaddrstr_addr "PrBgq1uGA5psBbKQdwUKV6ALQcSDdPaMYNU" in xs),big_int_of_string "34126387591511958341210865140674868228118462747359861564670201355693173712600",big_int_of_string "104965048078086776396746016138226544657598783018482100544370496961375407367526",0,true);
         (big_int_of_string "115483008168925529863480350691180797298844147873838585560516475202461875426711",(let (_,xs) = pfgaddrstr_addr "PrFUZatC5ZE4iAm4BzzEYyG3iUsNf1S2rnG" in xs),big_int_of_string "86757114595783125384154067570788755119560242812935384360575449175553969197778",big_int_of_string "36694119051224358545857486672684149358612004106211060048093681028879007592465",1,true);
         (big_int_of_string "97166385506398612153366050439008477022503199827161239551656206279850025391854",(let (_,xs) = pfgaddrstr_addr "PrPJL7L8GUHHfS2ecXfVbop2af641fZfB6G" in xs),big_int_of_string "84102029096268466834972796519397036525820223382907915438462336804515712616090",big_int_of_string "57870345484006428634888885644477415087925294783842845058764612421416886246322",0,true);
         (big_int_of_string "78655884152743883701574293859422309773590058735210578123045919257470731781697",(let (_,xs) = pfgaddrstr_addr "PrB621cFJsHFmPhyaMcYD9khrhGdxFQDy2p" in xs),big_int_of_string "36316273034719558389864872616205746562226894428236251610395554982162779612419",big_int_of_string "109109254888599355654908454112516994960885623393308034711189325342632869240232",1,true);
         (big_int_of_string "34180817851284715264686399220584438168082105155029774892437065556718090948984",(let (_,xs) = pfgaddrstr_addr "PrHZSRj6RcrbYybQCJXD2wGSYF2uccp7oF9" in xs),big_int_of_string "101608145988455133152045601961514846328921604496816041855545403882980004242673",big_int_of_string "30054546715477949892688587533042691213801049658947441184018933282085197693145",1,true);
         (big_int_of_string "38959294662196261139513375769365814042366446881663694958003547269751718508272",(let (_,xs) = pfgaddrstr_addr "PrPo4VvvzAB3gAiG5U1yeyaLTLWiQMDdh1g" in xs),big_int_of_string "40565921181473524426668640377776543593734036838226921422185154963786791519653",big_int_of_string "86544832148038407785166338945510659481711429374944911223836070775507533544446",1,true);
         (big_int_of_string "38496330554845576761034312666920037070611257762475876267257360576756312225879",(let (_,xs) = pfgaddrstr_addr "PrRbXLKVUtJHzaEZVNpjuqsFvgcc48effLF" in xs),big_int_of_string "22389098567893496959586289164355732976522165565541558889528433603250682659735",big_int_of_string "76135816403932764038192912003525188461471447566896305204482501000753213788655",0,true);
         (big_int_of_string "71928461860958158143799501925598088487926328981008578060099000210318098184844",(let (_,xs) = pfgaddrstr_addr "PrCNPbupzKdRzryHdoVTU4S8QncywJkp5fe" in xs),big_int_of_string "43813072580103377715529953297880629714910693010264136020899202936210782822746",big_int_of_string "73051326132669971847975890108219878709507935630135475754043378462381501368094",1,true);
         (big_int_of_string "3928253082518553852703475431896584646701670613524543650769883624215944505438",(let (_,xs) = pfgaddrstr_addr "PrPgvBhyZhWFB4CPKGS9zRHRM4fxmN8iVUZ" in xs),big_int_of_string "68880311490675734722515117549564383894650491942646585131950377382550622059446",big_int_of_string "25162042443867238524512804512670169185324914343390577618431674464205083882436",0,true);
         (big_int_of_string "99480302772751281369880529470909475290212075554583702472296975471523783206108",(let (_,xs) = pfgaddrstr_addr "Pr4C7FjZsL53UnANkZRamVQsbfuJojD8cdE" in xs),big_int_of_string "21246687433838351376919773779184971418630822869518199508311691350521491283297",big_int_of_string "16923638498219897602483682172497545595229181724320634646801070018106820798365",1,true);
         (big_int_of_string "78286732141100883820358832725363508588680791922338221513292476927374427527304",(let (_,xs) = pfgaddrstr_addr "Pr6HsJVGfiXnFF2fVdWVVVBwqAsPW8hrQTX" in xs),big_int_of_string "92962874221234801387225182879877259743326190634832801137330342881260852083516",big_int_of_string "15859800358745162475532763887786889380961211602960204418656148362828306620233",1,true);
         (big_int_of_string "7365091516326621493978326669572869698944944748900435000690816314345550606017",(let (_,xs) = pfgaddrstr_addr "Pr6qT4xWsuvKQVRHAid1w9iZNwTrpuD1Nyj" in xs),big_int_of_string "4197574492148422594748427595618543066834041893824148970085439551107574597340",big_int_of_string "70905730629254412225098263269698648621228470387832886422911429662047055056372",1,true);
         (big_int_of_string "54809191308329668827732192278848237086244314631675780538999542031990327714660",(let (_,xs) = pfgaddrstr_addr "PrD2vipRbKenwhkCZNuDUkD252BwY7fZps4" in xs),big_int_of_string "5529670979130829230056902960858625036682842307429478084406217505607063089065",big_int_of_string "13443091568304534462128693157305619718311814324776897210213343316992201838776",1,true);
         (big_int_of_string "10744726796484359735100814002515632496284066381285471356486274471247098177889",(let (_,xs) = pfgaddrstr_addr "PrD8GhXzCTN9h2VedjabiuLZzxDUbcEcEtR" in xs),big_int_of_string "40593006379696401048938683975709580335696601777021323748125129746056443561734",big_int_of_string "50073609192667088494507742254081075891840465547419621745155928261168507907610",1,true);
         (big_int_of_string "101155336934686959201556505856240479812030915436071995416508684995973579465768",(let (_,xs) = pfgaddrstr_addr "PrPLHtgEzPYnCgP2yJzhNUuczbiED8Lq5Ax" in xs),big_int_of_string "71025476068935108560652068060640285664256801920141321768375717794979917194605",big_int_of_string "22238357280046481193437686907346633717832199554885469020022428220998050180120",0,true);
         (big_int_of_string "27151029157807861114609413600833722025357252176379811596223408448789307519337",(let (_,xs) = pfgaddrstr_addr "PrNjEJRAZACCMSWXaRKSH8LTA13fL8Jqt6t" in xs),big_int_of_string "90170096539516247866910431551922553224084945494072571191967922503317479061820",big_int_of_string "20431787408974621028657496336449488596705516954637394674144614322902475831299",0,true);
         (big_int_of_string "28649934327240218503091004015452663782528322150216141176214863603655040746293",(let (_,xs) = pfgaddrstr_addr "Pr3svewFtTcS3ZRMFKEc14CyWw7kmx7rL8r" in xs),big_int_of_string "92252982257791716118373585162573971249044514852486173384303327045587420619641",big_int_of_string "87022540071009153679918293051237607891117265962876024048206824083931558067262",1,true);
         (big_int_of_string "45291338171823064332328125905915704565747477756016060439954342954145129721549",(let (_,xs) = pfgaddrstr_addr "PrBeay6JE4g1tkJmpCkpepkMW7NkfZcjYmX" in xs),big_int_of_string "114675300722385620772084391143865913168702593369731048723826487309265737193531",big_int_of_string "14108336861122436714462057239724729164778719771388610149866790613773162887462",1,true);
         (big_int_of_string "49993458114115161246162602661548855447021853320422234484126886152921933014566",(let (_,xs) = pfgaddrstr_addr "PrPmiSMjwsjetJgYK3Pr76YSYf47anvxqGJ" in xs),big_int_of_string "60157593807129799513592409594447565982411869386644080049563405666736427812041",big_int_of_string "29296365272964020158037953806859907746142897668708432413515183192283368896408",1,true);
         (big_int_of_string "4422648103817609342073959445917991367770286454930203315439632816248872678861",(let (_,xs) = pfgaddrstr_addr "PrRzAPU19Bnnkfs7FTG9QYLYGXSk1rjbHh8" in xs),big_int_of_string "64078095215551057591990132322359335557481758931352519670634420213381005685620",big_int_of_string "27966906318828143190392975076528902841568519568206928370953207458464954008853",1,true);
         (big_int_of_string "88025930821239123908586627452048284120002037601435665698405133994474571079616",(let (_,xs) = pfgaddrstr_addr "PrBne1pC6SfAxggZRVT5LkN9b7RPstyC51S" in xs),big_int_of_string "25818149695269828473328984209722022293774701204480215235134642488587176141683",big_int_of_string "8422890194944644112890797154523449989566063777114183991022197109702109798971",0,true);
         (big_int_of_string "95478648784149974976478381035082296154822299585730647876963879908320767596388",(let (_,xs) = pfgaddrstr_addr "PrPFv2SnhsRrr8c8C7rboDayVPNXL72g5Z7" in xs),big_int_of_string "59651003772871339047587761045753031445790140658810280350201517178032138994511",big_int_of_string "112511983106738565237087181373814193989066495778866959834204013254030891699217",1,true);
         (big_int_of_string "76442846244292646069399941930490538408838809880969325975083276754679588085254",(let (_,xs) = pfgaddrstr_addr "Pr9hx2zD8DGDKUPH2LLBSSTReCtV8arLETa" in xs),big_int_of_string "107677199899314715802712258532508146747116226288872852458910324235919952144718",big_int_of_string "24094562089117018806240527631405100590981438898723934470251826774550843945314",1,true);
         (big_int_of_string "8833758387980025277839861767475051402907839971278198959535093821139347533251",(let (_,xs) = pfgaddrstr_addr "Pr9RZSwz4JzoJ6EARERE6nak8BEtFPo7orK" in xs),big_int_of_string "99213869124479031349729288548823892156451669337007056650647064471109380917102",big_int_of_string "69289291986974950362629399888487015371707637214317871402868891697565383108958",1,true);
         (big_int_of_string "75141111708820978050274413719662732410933655749521574427750440329700510837509",(let (_,xs) = pfgaddrstr_addr "PrM8pdSAWPAUR8Mc65REaPnH8RjV3S8v7tg" in xs),big_int_of_string "66758616443380266295941693904838745088124806974113781557741940839178799179694",big_int_of_string "47693309534662690339813621159727337921563242493928635605385938203364759442232",1,true);
         (big_int_of_string "50581698419975536938379244940653665922471341095621954434528249221225832730831",(let (_,xs) = pfgaddrstr_addr "PrBj6pVvjYe4c7VH3gYFktJUhfJL5Rk4PEW" in xs),big_int_of_string "74164282001754471200078565201498580261286717150532365623404835446261706588563",big_int_of_string "96954447428057560941259089955565330764306969948073794347981847472021692834490",0,true);
         (big_int_of_string "61438424347261157220515474353164423966306940979769336934672231090655780416035",(let (_,xs) = pfgaddrstr_addr "PrR2psXLV7GgQU83jgw3oMFtyMc29abtbK3" in xs),big_int_of_string "86285555621936976038952786823861034507384229257359449626418881166852688339323",big_int_of_string "85456986951433536382580289733703943607288167902922331755737578795850840465161",0,true);
         (big_int_of_string "22731900107841041510244500505537732775414497641589998284181421158309097705661",(let (_,xs) = pfgaddrstr_addr "PrDsKafTuxTKy4RhpAc6NxvwtYJw8VjLdmg" in xs),big_int_of_string "61935728808058651669775824475071053922857410697100940714158382570409737856788",big_int_of_string "72515872351719914564406456233641775754045566486116163061356252500991482894128",1,true);
         (big_int_of_string "8180639738527741832601995942991266389269477745296581891400009582566373310372",(let (_,xs) = pfgaddrstr_addr "Pr9peRGa3M29NicBoyQm4noD2ywbhuyeore" in xs),big_int_of_string "24527429819170897649106235136707176792303290842539142311468577082174344480386",big_int_of_string "83593011986212746843933226057667419051743054954571359886160371111017587585555",0,true);
         (big_int_of_string "12519860112821552252644292788508594314267792328737883913750391791677251310356",(let (_,xs) = pfgaddrstr_addr "PrM1q2gaFwBDiWKHPPDR8x5oaavUqLFKaFh" in xs),big_int_of_string "79682799010929783341367666784180210540949865471003000496538372958228519736582",big_int_of_string "87185790704910761414200124466684693782916755174553438950926994828853484375948",0,true);
         (big_int_of_string "74717373580334907818622694898203094240682515634266867217690817832903475821907",(let (_,xs) = pfgaddrstr_addr "PrEgf864dKiBUhT2fnKdFi7SKtJCVBCT5gQ" in xs),big_int_of_string "109846178759283411681676401721990459492748957876847525117934773569275378882442",big_int_of_string "39669288638183091733814558978398214234741923369782404926145309701120263237193",0,true);
         (big_int_of_string "104209566650813360301132908031148519422192541946041581226619165449259169684967",(let (_,xs) = pfgaddrstr_addr "PrK12ew5ddozpEyTtBKF2vmCGKF9ZdgRtbK" in xs),big_int_of_string "107338616514722471528282263135522918820475318427558502180234863376578594529473",big_int_of_string "77868522516531975166463520467059311562092616684306435004004378218439594303394",0,true);
         (big_int_of_string "16474498913920023767897727235706363849477508616083272401324788373739951110713",(let (_,xs) = pfgaddrstr_addr "PrDHmWZ5WVzaDYoDbyA5WnREGz5gPaLtWfN" in xs),big_int_of_string "32655439790949526400732183433054079404036096799412373342538496929477808746795",big_int_of_string "103643885316795407119759426946667375463506057256514343862871679508232792966046",0,true);
         (big_int_of_string "62200388432797849274002462148760882655617171947667723778253974185328609335322",(let (_,xs) = pfgaddrstr_addr "PrKHj31pHFrtD8tAovFMpWmpVghxWjKDNdv" in xs),big_int_of_string "73675161969578284923858949915406951802349574708144502070859505781369118056057",big_int_of_string "65873877630042602846126932030481854636659471290808938986834271382569331522299",1,true);
         (big_int_of_string "27201592067813645077261452760084280793641759025985951247221506625778100255435",(let (_,xs) = pfgaddrstr_addr "Pr7kZShErzWDykgdLj3mxk4NVmQ55T5tfsn" in xs),big_int_of_string "80676422884736656247616818455591438119333185539788945184501289771589655614624",big_int_of_string "104349978927566945996837275280909129033574686870205069824422789956543833587737",0,true);
         (big_int_of_string "20262151666528713097275331482075504556249624751581092024806384268358836587385",(let (_,xs) = pfgaddrstr_addr "PrPd52ZkXPmjwqxwpCwhtjiX4R1rhf2Ebcq" in xs),big_int_of_string "14549058707304025813503198288821752598261844379401279196242918781963805641985",big_int_of_string "7541740830780371707978884151010528361552076238863729459387118295831931142354",0,true);
         (big_int_of_string "52910668158083117937206741416592755219522262208018671740161355454745632993779",(let (_,xs) = pfgaddrstr_addr "PrS94MNByLQrxKKVXZog5WmUzZuQzTGWf7G" in xs),big_int_of_string "97145268218711271748671566118155116510801186764429403625762255774756809164613",big_int_of_string "36078317443697061337740470568457519921127877974547421855407918154553140111382",0,true);
         (big_int_of_string "90501299417612127512772741270658595819675799373299476470712479596611246595751",(let (_,xs) = pfgaddrstr_addr "PrHJvPRhiTQ336nWoZNh33g5HouPyxURDDr" in xs),big_int_of_string "4471250626629739560931065989702483845417004423062115210947575762803851710146",big_int_of_string "48457209370815584304682567428682348461645384399819608014412884170607837135006",0,true);
         (big_int_of_string "81045955531008717745312462003018712621825484376279263750894898057241515787465",(let (_,xs) = pfgaddrstr_addr "Pr8e5LFSzHVXYntigsjDNjngDvHeCBtp9cd" in xs),big_int_of_string "36873230214600095824677874156377372481097170096615943109039018998594120547719",big_int_of_string "4702844344211525205783462113834041475477426638902673459770291985029818220065",0,true);
         (big_int_of_string "49469133745111849959121203373095520285724833238978185544447656837007755335206",(let (_,xs) = pfgaddrstr_addr "PrQAHs9tabFiJ4xxZLmxmdpdWD46qnVBcU4" in xs),big_int_of_string "34491089069388718618075111603727135842546614153320432096650696879651590949339",big_int_of_string "66689233802861833077260630689026803259949249370960348163778945716167155505075",1,true);
         (big_int_of_string "14975578301934552346272731841676939718656715269576867850665857919030049401826",(let (_,xs) = pfgaddrstr_addr "PrJwrDwrWtJsWLy6cbSdbSufUf2ccMAmMsh" in xs),big_int_of_string "11338103960938969025468118265853797275195942481002293831482068335876048594184",big_int_of_string "61250188099786702604296599216386702945852707145457266535944500034096358326319",0,true);
         (big_int_of_string "114087715323117014203184124695316800434079889184637801366998717208589925097647",(let (_,xs) = pfgaddrstr_addr "Pr3TBy4ErN9iU4iBaQdTQQM4P3xqGzsJ4mq" in xs),big_int_of_string "21453048446680947450554228097874781880496977530175518517296118229603149739454",big_int_of_string "7260690544065958583477407135480942010377798041174894065399529611478931639009",0,true);
         (big_int_of_string "85285164420827509333076177187505596633943691643304658094002519152894883106300",(let (_,xs) = pfgaddrstr_addr "PrFRv7Wxw5wATW18rSjE53LaUng9Df3WA8d" in xs),big_int_of_string "60836877993939449382233658580116664847180172419267258564488396556143188952850",big_int_of_string "109964912513743772133928034120498423558067136171534979222928924393860807790265",0,true);
         (big_int_of_string "22935269237951118108358795804194427413140768806201852946229093238568178166019",(let (_,xs) = pfgaddrstr_addr "PrQmyM5ocLhtG1CmTvoJV2RMcAJP2odcn8X" in xs),big_int_of_string "15342984830010220095133233642673997127909343713038805377417959451013651931966",big_int_of_string "19639861667619896311873373185048343364261462167960740217810145684143055160515",0,true);
         (big_int_of_string "79543776851324476489238960139016068582708514706136509988717940807346161821769",(let (_,xs) = pfgaddrstr_addr "PrCd5g1ZiZzZ6PdwvYGZShsipWqK7SLjpqR" in xs),big_int_of_string "39290773001474325874101410989283210383062190991518378274098248698194995572006",big_int_of_string "4328687669827785781405908100753931243487329423770283765282247470405196104580",0,true);
         (big_int_of_string "88271446902848052812119634927656637782367577197351595788460030284482998726275",(let (_,xs) = pfgaddrstr_addr "Pr7fVoDDLirSZC4CMfkUg3T1nuiFqAk4QF5" in xs),big_int_of_string "10123636925192295966971648735167669888580481928502589634483607466502811885711",big_int_of_string "38958380380805230161808015143631262259059569916751642580836214926785155949866",0,true);
         (big_int_of_string "93481231508914789215876432414938926155239242530700202383011305273053181852701",(let (_,xs) = pfgaddrstr_addr "PrBPg9z4sFLNZuCMhpqU3kSyssQgVmWCTpG" in xs),big_int_of_string "113378267067015592308808498874554844001944339438892948423646164527581762768033",big_int_of_string "91885713117716457040414813101669808748887763627717426901727322350288685037341",1,true);
         (big_int_of_string "45129997433439291011276559756138799885689975364570723610400182958728122583265",(let (_,xs) = pfgaddrstr_addr "PrHJbaZKRZfSFQML9hCgLLFyZv8ziiuWR8D" in xs),big_int_of_string "75771251007313168925177772461704670165858144664269363930052057496552911407148",big_int_of_string "30557621088944131418105594406317407342876591311039945450033953795705496691849",1,true);
         (big_int_of_string "46085219346626555165842576609900303475999848402843075406348753626417371589051",(let (_,xs) = pfgaddrstr_addr "PrMKzdxmggSdZSmimHo3gh3GinwNB56R5jH" in xs),big_int_of_string "100449302306615632451833317086826062135946639839208019284538663222594599776646",big_int_of_string "84619058805862294639546309162993568294358037680553521213443195105864438105662",1,true);
         (big_int_of_string "16713774488577849247343295151346114452242850579838689522354739718594640514959",(let (_,xs) = pfgaddrstr_addr "PrMXEp8NGr3MCzGop1uqND6fZq9joZe423e" in xs),big_int_of_string "106267760871849866897559075940710502610812209660715163100492175970068218709645",big_int_of_string "40461882114942320019221184924111046548196434731889709001799349654284288710321",0,true);
         (big_int_of_string "20905822294642143063462110756962654523060889884229952705227837157819279904275",(let (_,xs) = pfgaddrstr_addr "PrH4sJdg5KUFbv7S8yCUwGdKtFoZ7wDVjfe" in xs),big_int_of_string "73190501384467189449703880243317022966688396256303579445022855968945325863538",big_int_of_string "66991466728432769775976567529276596355590203576711112313227774058342788432785",0,true);
         (big_int_of_string "2669948391481571364654967020496694258403022751206564451824001926021129244894",(let (_,xs) = pfgaddrstr_addr "PrJZAFrbHhdWQeGMPsNMzgfYxktCMvvVyew" in xs),big_int_of_string "53254192471982566893490574423847814382106171567020849692662610494084113756971",big_int_of_string "54938788159600074747513783928926452206073219814263430717892622692174476167535",1,true);
         (big_int_of_string "80258049264620064352679872090565121416758926968285017255805382131944990003510",(let (_,xs) = pfgaddrstr_addr "PrDiWvKvPJXJejZcsm6Eu9JeCWCiTzN23HD" in xs),big_int_of_string "24335406903576196121452680905213257609004291279513818006386599029203807721570",big_int_of_string "98726840825339625380814183369787238746697925768115877141494367525436792082882",0,true);
         (big_int_of_string "22047216239153389306656526558480166377858020832233620155058167734273448089379",(let (_,xs) = pfgaddrstr_addr "Pr73hgYbEzv25EWiVK3CS3Ghh7vMGu6ZJ93" in xs),big_int_of_string "50378740185693749050269431206935841227507752831526589704367006016113920133058",big_int_of_string "84584342923518822252391152105357377614754223650056630721344485542706136900042",1,true);
         (big_int_of_string "71844172768790147672688932355474068119642321137158961289458081072410649276270",(let (_,xs) = pfgaddrstr_addr "PrQ6ob7aQhaub1A2AcPArjnwd3EbFGUpsCm" in xs),big_int_of_string "43866403913573317355422867566704610397983106150223027039625954727266322890123",big_int_of_string "47390316507502454967214366748930755690493495060820123526891965658443234670834",0,true);
         (big_int_of_string "87086883067112094123992832412815169014976990337060395631128107453022577321748",(let (_,xs) = pfgaddrstr_addr "PrEoFpTPegpggHv4ymqk1sejwBz8FBo3eh8" in xs),big_int_of_string "9847886368026457226819514380289539784186253129001764945096740684704365629662",big_int_of_string "85322825773942788740051216430041608512956961370085607770513467824622861619318",1,true);
         (big_int_of_string "85277262938148456341036471616218206913632651468843452381395024058033960059675",(let (_,xs) = pfgaddrstr_addr "Pr3V4p8DAmKkjhrwyuZgTNVoi5pz5PKPr78" in xs),big_int_of_string "65672843329341298030495709918320589793360198003493886435598385366966981580789",big_int_of_string "38421739190057725069694751916589860857055331828640908294391649648952416731746",1,true);
         (big_int_of_string "103761917477752624168637993796722209507180711324893482428050824795150213810305",(let (_,xs) = pfgaddrstr_addr "PrHpit984YV8Z3VCk1ytBbxDA21Urp1sXQ8" in xs),big_int_of_string "3953329533635817528917663450647327095923159421762736619107323113401466393084",big_int_of_string "43208774117857692245660649050787891653223504218005582956264023772214474689998",0,true);
         (big_int_of_string "41870583146834778149789977235177667664493481374715382389233033564704944224536",(let (_,xs) = pfgaddrstr_addr "Pr3BswVUJkzg7g1NG5eYnfwou9Km2UQjwbk" in xs),big_int_of_string "61551115129549751876265667147732568879746227573411227338510175099478649184285",big_int_of_string "71520478395745847728117405023073559623506753797698821864614254231152364078695",1,true);
         (big_int_of_string "48285735485633433598550579722689900851232278918454738134408701371125699668661",(let (_,xs) = pfgaddrstr_addr "Pr5s2NugAXDAYM8hPjnEGhocbGwUK2s5SsF" in xs),big_int_of_string "77043309465510338500753699381499412194700350429071549983498978419799149625368",big_int_of_string "65013508214973463595920170742944864918146778214432774025396114791080470472474",0,true);
         (big_int_of_string "62809109645840710820410785113416102588574226281261241619610030441062585166997",(let (_,xs) = pfgaddrstr_addr "PrFxJK7qKjize5S261zeopmFTSRymmVbQrm" in xs),big_int_of_string "103296937032359472520022683576241245164164528103167624830679117779642818802541",big_int_of_string "67452242443893552323586473434995198708533642345407941343201981266563212173382",0,true);
         (big_int_of_string "24436298340590050836810160187281859837054238772934385409929427803501575130683",(let (_,xs) = pfgaddrstr_addr "Pr9FwcFLah6ddBumR99YaTN6sBwHFJcZ5UU" in xs),big_int_of_string "20017969539308647238581794759591985544880289603616188151489553890762308315278",big_int_of_string "27092425615253837712916887702364459160615093176654583834119903734660337640211",1,true);
         (big_int_of_string "60748222578939864804741063056589477470411055380427310010890674086168444224904",(let (_,xs) = pfgaddrstr_addr "PrLgLtUJzkJieYiJ5tcm1Ay6GKDH8iVHJdo" in xs),big_int_of_string "928834788338307142265018905074633217843866058588402906058663564067516909840",big_int_of_string "20550557436604528197811648763118229293140783048255740612436012579199311067553",1,true);
         (big_int_of_string "23960958574938095122229746684751834494297409675506859502279644263107686725661",(let (_,xs) = pfgaddrstr_addr "PrKWbNA4zFc73kigtjYu6wrzsghBp31QcYd" in xs),big_int_of_string "84286192555757775033507732648609496803620709099490758217012200395204644660730",big_int_of_string "16001454549426150336464893386737779292282595759819321611873610611021990354468",1,true);
         (big_int_of_string "74947018651311526617357146385985726993556023774723186590667261829757732359762",(let (_,xs) = pfgaddrstr_addr "Pr735WGqJhmCkHXje6uD8mfHXW2qzJP6abJ" in xs),big_int_of_string "44547876980293278384978852054706254868201769158058223741861737782381952473646",big_int_of_string "42488473406757850941544745366482767295445752713326089602990745032287595097193",1,true);
         (big_int_of_string "40725732841985984468401761517672618837860840279636765067695637555435932313322",(let (_,xs) = pfgaddrstr_addr "Pr4U28AzuSwip5qQ58MQ2mAeW8v3gtaTsMc" in xs),big_int_of_string "27707270666289991695165720970792313594647215812628781818241035036785638963788",big_int_of_string "88411345707531434993546422408466596034555792443949306487519197431665735314712",1,false);
         (big_int_of_string "25611494335174211150255904690951873153780546691995035008223443526482732333866",(let (_,xs) = pfgaddrstr_addr "Pr9sMth75v6sAk5U68CcUwmYi51fwrvAwZD" in xs),big_int_of_string "106918846573999701774726098217127933402894770933166336020242256400247502836636",big_int_of_string "1373793211207902844494749796867348365280406043798427812805766467974378963057",0,true);
         (big_int_of_string "85669864732241865673028395118516657447744749703479102290858402127327916985405",(let (_,xs) = pfgaddrstr_addr "Pr6GNf7aWTgWuv3PY4WQiHX4HLbAWu6mjnh" in xs),big_int_of_string "64625654177754116974541120445384549990477821005954331261398742144782460802806",big_int_of_string "80450673119662329590208066420388901929548370810126297401703014321117961950442",1,true);
         (big_int_of_string "83504840497435974966076284478025744614220766564937674810633117955384830655180",(let (_,xs) = pfgaddrstr_addr "PrPzcqgcBep5FL5fc5JaitkxUkkhFNPnpnt" in xs),big_int_of_string "3779488049896632364460746541004013103268997045723693103089324345182547111439",big_int_of_string "84882924820308273875488565695095210972419638076387964011991892668607872464385",0,true);
         (big_int_of_string "13251202938613921671359922375760297761849499796797447831753021620963823838364",(let (_,xs) = pfgaddrstr_addr "PrHDjSd2hMQX12EscBxr7HRdvSW3SsPJnXa" in xs),big_int_of_string "75572832566249290641378469978726658081568907252940348983961277343367329635901",big_int_of_string "43484751715924530992319354970139883687934891787379062259808428886148586167513",0,true);
         (big_int_of_string "47247021087029237767694211195817621065368797625647112422909167860436125826444",(let (_,xs) = pfgaddrstr_addr "Pr4TDwKhXsPWiGiuNVggwwg3rFnig2Na94b" in xs),big_int_of_string "101623062447828219916246047867296478978082432861881302188265430013065780449679",big_int_of_string "84898578806752950195038231516123020612946463579463343877005891235252624346107",1,true);
         (big_int_of_string "1116954631115120260565057403169655643178508100467224903629054155410376117633",(let (_,xs) = pfgaddrstr_addr "PrMB7ibB4nfzdEFVk6yT8sy75mRhnk8dzLt" in xs),big_int_of_string "17479327205482861244761388644108511947824951895497523689477356655916848127220",big_int_of_string "70015796128950632195959422486204964474368240309017555700806878981978136810648",0,true);
         (big_int_of_string "73720869685921485469188683770792771485919795464365726396699738665413449164815",(let (_,xs) = pfgaddrstr_addr "Pr7ZyAT1bW4JBayi854hGz7aC75KFrTZZnT" in xs),big_int_of_string "47281810353387752561568497448620713633725752941446624267195892588543463158424",big_int_of_string "68984236974104994560334974012619893630547668542299554353284999728703098005081",0,true);
         (big_int_of_string "21417019189461236621994798726972051444060762511485780902001912597392813925564",(let (_,xs) = pfgaddrstr_addr "PrMtANTdo8yaMDksiGNJYve5v8W3DMQaR6H" in xs),big_int_of_string "14879637851596645108831566088636915720009820439757032173961010086200021376217",big_int_of_string "52257423400543339682051256251985583769241146007511595889272366238545606638619",1,true);
         (big_int_of_string "82643363791329177564426575290590630273681250041088009270881385403321472406545",(let (_,xs) = pfgaddrstr_addr "PrGZ4Vcmw7bVKKfAjrGZtHmxJNAvjZXx42A" in xs),big_int_of_string "54714099775990058812951365863825578721201409124521992113661199868452380385869",big_int_of_string "103617625553144066978583559807306294866721335451683228569259737054476732338563",1,true);
         (big_int_of_string "9079224124469043341069498601566277403045417676873087337009071333133640663071",(let (_,xs) = pfgaddrstr_addr "PrKoGVbvdvY2eJCD3SdX82Gr77rnCRs9YWR" in xs),big_int_of_string "100954940203394854417720709827902802837386437251460917159021956507585019303659",big_int_of_string "42325376846064018595444790035578019385904024447907593998786739812520235797506",0,true);
         (big_int_of_string "79067549051081878904532890248706245608467689584735362708381167845358945829177",(let (_,xs) = pfgaddrstr_addr "PrPVJumdg8mQKJaCAFquZh77Fd4UsJZwdgM" in xs),big_int_of_string "45376207022494357909188112281797515089403928616697403025908966019620613104723",big_int_of_string "48872128975531057824071663218017027407696933121202533446995934976462799433847",0,true);
         (big_int_of_string "48580272064191618588824253862998412529876804928924668047011347735170518918874",(let (_,xs) = pfgaddrstr_addr "Pr3yGna2kvmyhdLdUx9Foag8yvb65UJTkzr" in xs),big_int_of_string "79896237300885973733446867992804994346670001519002306467477038721167137194040",big_int_of_string "43303692893456034452161998344367802418659471316858712389947039953674109812040",1,true);
         (big_int_of_string "14493231664483710380054605397833725319957803108700226661543826964508282694077",(let (_,xs) = pfgaddrstr_addr "PrGpGKr4c7tCXJ6BvzaMJYc7FDMZtWhqcf4" in xs),big_int_of_string "81572667281307570673516465458599680880166876797491063156543713409503391135078",big_int_of_string "17080672014443546225641456058957399094633862822945772000322411676133743802357",1,true);
         (big_int_of_string "62567196317775225559233374826983523921777747857957067151446581373958699442308",(let (_,xs) = pfgaddrstr_addr "PrMoYRicVwZ3zGW3TvRie3hUPgn35BNZgZ7" in xs),big_int_of_string "38399164832383636620890608747268189577829820793809282548243748304400262516008",big_int_of_string "100781249488359510418409208555867221685307384624950147452906942154715418170963",1,true);
         (big_int_of_string "27155532357935584196455676179513777166487595073183989551257221497987413124099",(let (_,xs) = pfgaddrstr_addr "PrJP3eaWKZeMcyzizQgdDbk7HnqzWDE5fku" in xs),big_int_of_string "87691629094413829379329573933887752179355725236162867725396187457856715752544",big_int_of_string "67679683045768895372214519220450906457363318240654885653669669081184555518430",1,true);
         (big_int_of_string "63190831732654668286461159106597023087243488642267873595298112954832981278135",(let (_,xs) = pfgaddrstr_addr "PrPvwVJyyiA5NsRHD2CEekPYsL82RM2SAN4" in xs),big_int_of_string "17225644454617844326834817658324999217991565930015714729813492943383907229232",big_int_of_string "72973867146308628972011469998319435835528970989856989019744913421811629465688",1,true);
         (big_int_of_string "93968888790574530663153781823901727484483755105433965968080964279153530800505",(let (_,xs) = pfgaddrstr_addr "PrA6yzmLDFKdabHkSKzSEC3jvSBHXLS7XrM" in xs),big_int_of_string "34213946072747844034797726126299734428251412577029136769328689446456325818819",big_int_of_string "46520273759258793411804868595263364921063989017373730234380779654918392015567",1,true);
         (big_int_of_string "65892274817499128879415256366367768761773639285302437681892799229976406459347",(let (_,xs) = pfgaddrstr_addr "PrPcYqusSSWcdvpZDWcef4Ht2bVBXXvfozN" in xs),big_int_of_string "18339523668605697647494326210943094813783474467719550066908391569308578454059",big_int_of_string "113342039626257439367274317746746093353575965671387231889001242619006125363235",0,true);
         (big_int_of_string "28057547831803639030277884399987401955278447285454770809511167247188181526499",(let (_,xs) = pfgaddrstr_addr "PrMyABrTiV2xuLJY6x8qutR2f99pd9SoK38" in xs),big_int_of_string "79379164370254875976416474377653726743188137391670920984757443179187402049108",big_int_of_string "91977100428578456091983221169480360029378881375605218717649256207840235318166",0,true);
         (big_int_of_string "89004056914647886146844338785639643785955812334152456006873987506753483424110",(let (_,xs) = pfgaddrstr_addr "PrLEjEnVRATkWTrUA3RngEv6Cu8aeTuzzoK" in xs),big_int_of_string "11523962643802693111714891898940266482355710822376402857087991464560862892541",big_int_of_string "100998997251696287959995059766586702042539753849363760568813001635639000882861",1,true);
         (big_int_of_string "31516783830244022068430511608862457497095782662869504225426127056766450968295",(let (_,xs) = pfgaddrstr_addr "PrJyZSHbweCtY6bXoFpYQNFyH6SNWAYBhJc" in xs),big_int_of_string "27859684109268080832858202037237438276905049239614267587335330069247183605765",big_int_of_string "97787128374701133772191983334160733549417598548046389813070059331165349826969",0,true);
         (big_int_of_string "80918897907309846571018430727962363524262790987924759032034461141303114005519",(let (_,xs) = pfgaddrstr_addr "Pr9JSM3hYhjBmVBzrHoR22eEmnTCav7kqy2" in xs),big_int_of_string "38743083654175867059106183261931026205566880072144711952277752156834380810576",big_int_of_string "56022963093876434276986839375974222146274245745106536682746082140847878246712",1,true);
         (big_int_of_string "104709652035979854028735972811121001340149001657826170526557557106488190629339",(let (_,xs) = pfgaddrstr_addr "Pr8JGo2r1WAZDBrTiVbhkm7AZqKz2Jwha66" in xs),big_int_of_string "59636418283932200521709701061780892176557367898636707855188667949208503411973",big_int_of_string "48274202992776113205651666854452836305601224235258288056152656244216677749677",1,true);
         (big_int_of_string "27869578733175759140725276519008425597563145229990240319161174562154669850688",(let (_,xs) = pfgaddrstr_addr "PrHMLeMQzeegc5D6tYD2KLX8qLrYxiXioZQ" in xs),big_int_of_string "93650818790913278621453209167920872767784735966607823914734031673446598694321",big_int_of_string "83440328875278369232180865778167203777667062384752848903245727143459325111175",1,true);
         (big_int_of_string "70380150255455053478103187009132116999059675507886874635469687585938419131227",(let (_,xs) = pfgaddrstr_addr "PrNqarSnQ2VDYvXLheH4xcuqkVVrwGZ3j4i" in xs),big_int_of_string "23488723839837035436290955338686541917416585163427828251060159667537194495434",big_int_of_string "47813718262336872116842440988804430006257803363775173630249216583591409017563",0,true);
         (big_int_of_string "114811044681570462522877434630415887689860884130996721151377190834056818904007",(let (_,xs) = pfgaddrstr_addr "PrBSHmhRbjUftLeBo7fLkALCHiKCm9Ntskm" in xs),big_int_of_string "11487791485358756864686098610588452225854612327126442212450164502212977958876",big_int_of_string "71815457892191718132245015919613908007277978262618915033512513888359227052889",1,true);
         (big_int_of_string "45617714925330787123407731032895322981835281902392570021523728419020506243057",(let (_,xs) = pfgaddrstr_addr "Pr4L9VgVuyeBvc2cdxGMNe94B7pocQsapTD" in xs),big_int_of_string "68316677553293610542277519142008017501871875593495146344383596971554732684964",big_int_of_string "112748613386677357221666056061791140031018165559925619993498198737371784719186",0,true);
         (big_int_of_string "47478224663226669127310317088952175871068644957634197101697463132777088805827",(let (_,xs) = pfgaddrstr_addr "PrC65mn7u7XiTx7HSrFupkA9WAu8iYc2jBD" in xs),big_int_of_string "8354298404828554981031276801972102603553566441548542921374722222703427898679",big_int_of_string "18736589641759927894434555670757040216008647399143189955714940340651896165367",0,true);
         (big_int_of_string "52945360043364607442716138749538523580618226052186901214649861730516458574799",(let (_,xs) = pfgaddrstr_addr "PrMLskFubEu7FrzwwdFGB8Na3xwjv4MShuv" in xs),big_int_of_string "58159413155689409957206067561892755596196344283173664907324406743585728575828",big_int_of_string "9877615739810642132518959541428704585056497894983046735871982886204216009360",0,true);
         (big_int_of_string "31412146365062357189850497493965340919882318566417212892017319317099798932780",(let (_,xs) = pfgaddrstr_addr "PrNrLYuhC3T1V3vwJqAfHFke7AcRMQFZk5g" in xs),big_int_of_string "78691390396834139579282270372874541237333067748253338333158306271392131278321",big_int_of_string "66650043318805404786717288799105184942861945023825359077717350872991097551952",1,true);
         (big_int_of_string "64517828621357780104800144685995710876438640687953827472650760215345515371338",(let (_,xs) = pfgaddrstr_addr "PrRpzwPf38u6hduKcnFnfwMjhf25NWtj8MP" in xs),big_int_of_string "21758910969102566568885677300486730628790805180612452228903544619192543150502",big_int_of_string "8933914946016823214904696113231199097803605170387315571898917581163489106909",1,false);
         (big_int_of_string "75198795521501814158911739471483558264049985521405764841960623543239961214256",(let (_,xs) = pfgaddrstr_addr "PrLPBXxxibJH63zo7RAFWAC3fqCEuN8gjKw" in xs),big_int_of_string "35678548840231076746861400689008189302233519218833037073823539487270160765132",big_int_of_string "84492235677835626011581954891381842141047891759934954590440679621065397914695",1,false);
         (big_int_of_string "15597400623847624862146599004105761975335628009018890030717646705771710623397",(let (_,xs) = pfgaddrstr_addr "Pr58Wx8mpHSXm33Nfky76TUBaUXYzr6Wcc6" in xs),big_int_of_string "13760273259055200247308969818295092311651360582528511296591521017767313717369",big_int_of_string "103729944523843761654132005568892802573766746092315358207319397201467847163157",1,true);
         (big_int_of_string "25875368354230877197409498859485249457775841039305551462989806546644621988885",(let (_,xs) = pfgaddrstr_addr "PrJH5qVVQGYRzEfTo2ZFM4Uya1RNbd2FiSc" in xs),big_int_of_string "75555663579235359220575825968855272344800367508649599137014738471308792174166",big_int_of_string "92508497802511493932423087769867467213263310861041502866620621289309534633104",0,true);
         (big_int_of_string "107454102208413092594651622549238819776596798521598973319728326684743414728993",(let (_,xs) = pfgaddrstr_addr "PrPjQPUXuLk1QD1SAC1nPtVBvSeoC5d9pTK" in xs),big_int_of_string "3862959266582935524594184995724154463505983916778479413699916653171031100452",big_int_of_string "108737705175396505406084911264440899823817338927604197251683603770828327696114",0,true);
         (big_int_of_string "64962404316541528641738072126000776195797105318395559597944717358901816508267",(let (_,xs) = pfgaddrstr_addr "PrS1BSSpmsejNNVGuaAbRg1gUvViM1j9H3W" in xs),big_int_of_string "61210145040960833384602625269902636924080808290848522248961827498773421189001",big_int_of_string "20002787945795700885066813446077218274717880522911258703560858061411778074779",1,true);
         (big_int_of_string "65751415040553551557033174299817913263833402474033992378038174538400184008645",(let (_,xs) = pfgaddrstr_addr "PrBkMHcS4MuGZVAzp4yoAfTotsUEVQSLc2N" in xs),big_int_of_string "47384988161298955098307542383340604830466954802963209903200815379929169220852",big_int_of_string "14775814247452203538562408065172937205193665795444356326663322743043372121263",1,true);
         (big_int_of_string "115171659793662089315230825051631438160926396132000033795786377048769095107593",(let (_,xs) = pfgaddrstr_addr "Pr46xioriD92pmCh2t2RKY753Srw4QK9wgf" in xs),big_int_of_string "94468287475891917410177243371468270882127894975679638396708891039707178876840",big_int_of_string "23736568634346412549027301342985680913640828764382266856064572006430712535997",1,true);
         (big_int_of_string "104966715398188606519847663671470550601872984001228091500115162668117867834869",(let (_,xs) = pfgaddrstr_addr "PrAAaHmruqSrW6CUmhiLrtopd5Ex9xviBLz" in xs),big_int_of_string "98508548371959294670933916591103791258278245322050845154891857566629015791441",big_int_of_string "102924670247995691082813444941855702846334854795055526362532753389077773404640",1,true);
         (big_int_of_string "9746848924458524739535041052463198928697286555909251298992131502063861603940",(let (_,xs) = pfgaddrstr_addr "PrAKn5rm6TXqeqkehsT8HWSC7kKNev8HQve" in xs),big_int_of_string "39832095180203107992465693428423747103092184013847416570016382339391046406626",big_int_of_string "40999569117193222277583343848528343074108697569583944060917478760383521354808",1,true);
         (big_int_of_string "18174126429804808670346157805190850116880129214621692597968802151225044007180",(let (_,xs) = pfgaddrstr_addr "PrN78MMTAzGpczMhsNh8WJJwuDFs8cMRCNy" in xs),big_int_of_string "95925336854098344071608136174606015975419587995493078665618094531733077757691",big_int_of_string "76240221726474810377265231950392858225500828952765051794026591003735607114275",0,true);
         (big_int_of_string "99812931819502795679444686527580355408436145350951454920875471797159901152887",(let (_,xs) = pfgaddrstr_addr "PrRBzB2hxF4jM4MSFB36dn24ahaRRV9QdUA" in xs),big_int_of_string "25130355064241576448856679368824201241949804311908338594096654541161863281492",big_int_of_string "83104716306806115183568120116277545798686941884097679229513949899846474568201",0,true);
         (big_int_of_string "70077811158657622016874409742416091579179888114312251451452343827821842803169",(let (_,xs) = pfgaddrstr_addr "Pr7gHSdLFtEJJ6e6Cq9VJHzq95PM3ytSNkL" in xs),big_int_of_string "82586773118243836048064224538713653038300373125430114881778272015067269318566",big_int_of_string "35485816502605421624189158818715308964588008654446866393712443867795608964248",0,true);
         (big_int_of_string "38656513923726107022487425380752501510964724618743803884261845048132594138295",(let (_,xs) = pfgaddrstr_addr "Pr5i9Uu2DBNmhTULa2KX4rxCp4snYry946x" in xs),big_int_of_string "36358644558590567194165010474686946097654702928840124730301496573788269698465",big_int_of_string "44303138671336508013476482301932743127569408163408693106563411933286504545732",1,true);
         (big_int_of_string "76702429972123846643860600182596158052954505286937575587861346824075313499972",(let (_,xs) = pfgaddrstr_addr "Pr6y3mLgM8bz8TD83svPTwdkNQgoY87dwkF" in xs),big_int_of_string "949838554978530587679730832365801021448556406228376577813863898935182949067",big_int_of_string "19306892239176088738129380327862913414735456916825846021224125981070306722722",0,true);
         (big_int_of_string "90687664790945678723415569618290205803055151549197006930201407193695795727329",(let (_,xs) = pfgaddrstr_addr "PrNRRgv7kGvbor3WELYaYRUXW4WhTboTEFz" in xs),big_int_of_string "72885752993732241276252465737440425800259218585553704615584025403525815246405",big_int_of_string "17533840530295510927111907099163410576449396322369138682370575645247172218832",0,true);
         (big_int_of_string "32389791561858459549389806502759253196578678895360500638796778169335970760289",(let (_,xs) = pfgaddrstr_addr "Pr7fzque3YpmRmh121pKgeMzVeCEVp5GZmW" in xs),big_int_of_string "32580883474698961149230345541099823807018720980799195922463410260608823224831",big_int_of_string "100242435660317178465786428420959722023237571122359193713079861747399428338876",1,true);
         (big_int_of_string "48054592588459377072887354597545910135078758188603625035292308828971249948645",(let (_,xs) = pfgaddrstr_addr "PrMQ7to7CjyyT2V5QiorYZK5bsZLdQmc95Q" in xs),big_int_of_string "63079238877106842808315146889828630636391995502714811297796602575573999140644",big_int_of_string "8850193681279710211513001752574241066901011323128578415716315470415594411998",0,true);
         (big_int_of_string "10781380329007404404389232894656124786421707411056837674338503373271894315095",(let (_,xs) = pfgaddrstr_addr "Pr6KJMLDYv8EtV8ss5LbLGk7qhRzBr1HPFp" in xs),big_int_of_string "56790567401840582481801574217657710416027384632385424221157026400929447573834",big_int_of_string "83024402626403663922308407140949032749398458808565951739114954640684226928056",0,true);
         (big_int_of_string "98721024553434172163692928950536860976270945061849826821748926058747490615512",(let (_,xs) = pfgaddrstr_addr "Pr91aNnRYjyTkksDzCqyWbe2Hr6duqWKCeq" in xs),big_int_of_string "46202380911393508794846901620502587584848628981883367263743247734855958572672",big_int_of_string "103066181644518433151629415020998162393361742444044119396595084736268660829410",0,true);
         (big_int_of_string "79209098070403840352825281175306412193933162212077415238374421878758461497218",(let (_,xs) = pfgaddrstr_addr "PrNdp3QsxMcWQrTBGZXaTxY5JmDVMSujg8e" in xs),big_int_of_string "101701175755829918740606344198336633075644712337964602950977684498015439593411",big_int_of_string "113618098252894924075916744830852527987587376554184357630142995038309728662951",1,true);
         (big_int_of_string "73547570011319799288444644253132112421462152465731247703834766517738826157243",(let (_,xs) = pfgaddrstr_addr "Pr8CtNJwPm6ehgJe9vjxVKDx6JwG9i7tNhe" in xs),big_int_of_string "14228364562864995160201166608133107393442681493391066663722972119824570609820",big_int_of_string "68800077642651818695721028324468741932738955215341511311952435843208469369700",0,true);
         (big_int_of_string "75881807344535364039028457321039879902514751727298523420578051080273329977994",(let (_,xs) = pfgaddrstr_addr "Pr39CZajQqWv7UxPWsvqrYqS5ZKdtnoeRLZ" in xs),big_int_of_string "39371516897599431921821805317059295488217513504005026789556747701338572197054",big_int_of_string "42332372555639082815099954778466360787681389842986368196836807054244268119181",0,true);
         (big_int_of_string "29461197766871389150408199251437881417506033276957672644070827163261291135479",(let (_,xs) = pfgaddrstr_addr "PrLhrBT8P53aeTzxMkj9Djqx9GeEfP2UEJz" in xs),big_int_of_string "728775151641030355060056087036234401600150088230740826343135937156226443367",big_int_of_string "22533954611666700518136646963801061473984497190085929680949402195025331964413",0,true);
         (big_int_of_string "48257096700454372808515842669722746209214450079246588942794606101662118659580",(let (_,xs) = pfgaddrstr_addr "PrBEvJkhatETdKTAuuNH6i4XCyz6azEiFHJ" in xs),big_int_of_string "66046806776530006315610955429171428364629451259758684880863078160428466849815",big_int_of_string "37054134601643126859134241282529770890021328397085203850964833617644034297228",0,true);
         (big_int_of_string "105891358624729868703203809058282728171463105643466802730625062743091862736424",(let (_,xs) = pfgaddrstr_addr "PrNY9ChTzyc5Dm3jAQdYJFtmTHVQYHW9fov" in xs),big_int_of_string "43569724102028188680418938021928074741495958178716554359725360341756306714487",big_int_of_string "105499292788565776441210574870852605516632951787417230039388834482761117579245",0,true);
         (big_int_of_string "75486826805580933912040028711742480283754047110877953415946351442680390568046",(let (_,xs) = pfgaddrstr_addr "PrC82NtqEFnXdU87c3wKyxn3yf9QbmkJFjm" in xs),big_int_of_string "107952190896336639489163555779296972214348842464416865065325689291413733770650",big_int_of_string "89477899306416713965632761980186071476813858018415060562276419244981217806176",1,true);
         (big_int_of_string "78818992902464730963714120633548800784908108272514756639225682549505995355509",(let (_,xs) = pfgaddrstr_addr "PrHWotygRyc43myfcunHYemSJYNNiqQnNgJ" in xs),big_int_of_string "113725238729091591094846367140245363460833766496285345129641964457403733268682",big_int_of_string "105396428075551479757387007945001959980648610675297972573374877600841071823641",0,true);
         (big_int_of_string "43417899954809808002821780390854204131263318388159772044363917211244256692121",(let (_,xs) = pfgaddrstr_addr "PrRT5XABhbPQajrh52zQ8MSeU3dqoSqvS6j" in xs),big_int_of_string "73800957545918969263217633553349471500740100744331082218021025881438603823847",big_int_of_string "43821384678470696496159725893542863621187663704061902152053091793789277765477",1,true);
         (big_int_of_string "19315836537849280250225541575265997478454412620338599375847394740339653085847",(let (_,xs) = pfgaddrstr_addr "PrKd1ug4333TwJJtfm7FEWrPiB5Qkq9S8we" in xs),big_int_of_string "106661033582152052340731615816508421755713670480218268296184048297056586215761",big_int_of_string "103150895752890853536690961548987125926470905688094454664883843155928939377380",0,true);
         (big_int_of_string "2983999154872418878456625732769748613281759909177628530292070509428168038149",(let (_,xs) = pfgaddrstr_addr "Pr982vMqGZ6kytVLGY97iV2yebLMJecDCCj" in xs),big_int_of_string "95845402626932544122087039049987670681662725006693271748195759782070576543479",big_int_of_string "22655110845652985082735682112128552168552039683252878873662568898944803523910",0,true);
         (big_int_of_string "39937949184346146240294636421850273414025595180894287181919294037945589482611",(let (_,xs) = pfgaddrstr_addr "PrJHEyhsLGzQVajcS8BZ1eWj75NSLyNCaxA" in xs),big_int_of_string "110315811408482511194510522221865439983122243005636063790098780337214146777361",big_int_of_string "22886783230826536005828358966138151064895594580104082409811709352237736673173",0,true);
         (big_int_of_string "42500718794132496545888746363520342781530795372948481969051633285082721836312",(let (_,xs) = pfgaddrstr_addr "PrNJbFPsMc6t2Gau1aAMsbLJtJtRFAvQZ76" in xs),big_int_of_string "78136684777075393272513920666369046490559008439743067169878820087733143984643",big_int_of_string "37413153635013153910888686886668877453797985821545049641739611345745909000302",1,true);
         (big_int_of_string "8120974865735464884398705793202679652704086861451805920629987049216679674553",(let (_,xs) = pfgaddrstr_addr "PrPTAioNaGCDUVxqyVYZNEPf1etjEkYND1o" in xs),big_int_of_string "51020820634449123872007807494759771152078029853533956435940486473898727765239",big_int_of_string "101059666345232979267513445968235420747799129180506221153219581434877043779904",1,true);
         (big_int_of_string "56057442971098088177807249652077361704062411490934642930827337435741406209589",(let (_,xs) = pfgaddrstr_addr "PrEY5q5H5VTbrtb3Hyui91gj99AJsJGDBuV" in xs),big_int_of_string "4468628733725023168971488962929690338461885835884521957175235732370454467542",big_int_of_string "101880862992777727639225991370348569157365783715206853954545798947792499140443",0,true);
         (big_int_of_string "16110749079647678779295059268813955306002978161719860408587880685037343475246",(let (_,xs) = pfgaddrstr_addr "PrEkuQw7uNkZ6G3qSxV319ZFXRvbjKAp5ar" in xs),big_int_of_string "5054500861658845874204982310720590914691492730984946691233160105500916158695",big_int_of_string "70403841657082756346871519254651044040464318608610941585949876687452028726305",1,true);
         (big_int_of_string "36496745264023685385639669362289871947770605193203472417808913941465678318064",(let (_,xs) = pfgaddrstr_addr "PrEjctN9zKyXEkPpyMXDXUbgT7RaB6mn4hZ" in xs),big_int_of_string "19675720884775127009998745119128106394112714734722396307582071578955142779269",big_int_of_string "75524250224757926358952727161973981631772695819880454666377308782124391991488",0,true);
         (big_int_of_string "21835371530205780115223208515737896247394761608581427503630385461461832790945",(let (_,xs) = pfgaddrstr_addr "PrMmQkMs9TSJBo8nBk5FhBnLnZfD6KTCLuK" in xs),big_int_of_string "68602756039875236918552754422704846824622942027527239177569728386391459763935",big_int_of_string "95712662071592006026470769872006534503594929006807190156444934034409448357895",1,true);
         (big_int_of_string "112687550334141569644684448386499012974638345011103493937426790137079155865312",(let (_,xs) = pfgaddrstr_addr "PrLWbmj6efTMvXEXyViYJU6kHzU8yLyfQv9" in xs),big_int_of_string "85081792963432724606272048616245278828721161551031681173478179334294478230578",big_int_of_string "99209952777782204913315442977439985580591865630615906781788719712021939111080",0,true);
         (big_int_of_string "57161972023241352573753034104025312282462939777343465346579468936529141111084",(let (_,xs) = pfgaddrstr_addr "PrKTxCpivZLJZNPtoUmjZrP3mmdYweHg9rL" in xs),big_int_of_string "104940123760248105720779621603466661327402280827297085486793733187168838207080",big_int_of_string "93148010547449982119690962208205380416162768785766524565285928986108224759686",0,true);
         (big_int_of_string "107376143808106080444832468620651589197115057413476668989823088355655947648850",(let (_,xs) = pfgaddrstr_addr "PrN5sasvMneGffwg1F6TzbtoA2AshLyLi9g" in xs),big_int_of_string "29096160457653173197151368465702896867602485300804084073826969445092934812303",big_int_of_string "24195401824148079804045757951787834186484438539059436838725925100599128254550",1,true);
         (big_int_of_string "31368220310174668806162479271273245920619947245516461120644561459992082855508",(let (_,xs) = pfgaddrstr_addr "PrCUWXgCqZtTdvBQpCnh7KGA2KKoXSmb5ug" in xs),big_int_of_string "86506659257689993527840141149086249960378505102640001218620533311482091768817",big_int_of_string "73413356849782412239273016894711576574583247377805984264783751196502586743783",0,true);
         (big_int_of_string "43997616406895866938397085014051211768190406920369811688451795996173077565878",(let (_,xs) = pfgaddrstr_addr "Pr89fAP8K793G71Hq7xfZ7k75vGVuH2Wxh9" in xs),big_int_of_string "109443440103716750043297358867500291471552151663639518351472742098750206506597",big_int_of_string "56333872699930196624908936519077470423340207248556849016999260812593275147430",0,true);
         (big_int_of_string "14673577501614104792842598554122480345256821179019970584867478764671569209917",(let (_,xs) = pfgaddrstr_addr "Pr8mQCoRsNZLzjhC9Ek8E33YZ53HYw1xK7D" in xs),big_int_of_string "53733709581617988002541196312891374478944890892300399285421768342998228967131",big_int_of_string "108428339682403034933588306761225771124643910801370855496971442075260670186861",1,true);
         (big_int_of_string "61521757737214852310282847798897728637794935915756274065624921608014750526779",(let (_,xs) = pfgaddrstr_addr "PrLug2dMc56MMmezRG8tJSX2FqH29B5utpZ" in xs),big_int_of_string "45968951985603175189830144806810544044653614550214266658117986599747877840681",big_int_of_string "87494424708879454791286500746927245245193506626513644396031275663617688165637",0,true);
         (big_int_of_string "73140348514678589414168788318958935656663190964039164891468759542448288430499",(let (_,xs) = pfgaddrstr_addr "PrG3SfddY7CDPeAJP4DramdJx8iM1YrLccP" in xs),big_int_of_string "38577628391009013918760960271054160354639554757009367915056878429070628936440",big_int_of_string "88479285783683464000866842057737439734271328083897346223901287348516758397178",0,true);
         (big_int_of_string "30332619446685403845512423980155927399666012928269186100051229721439641845605",(let (_,xs) = pfgaddrstr_addr "PrHMzBGnDmCZC8dkkjAxGzKSFKfDjtdPD2j" in xs),big_int_of_string "93303315733990890714838647907692538930277468465880245115750126230027554970046",big_int_of_string "39625881110553983482442866970467737194697821212030983742138376472955805706985",0,true);
         (big_int_of_string "67248657608027369083642920146694538475027316538309438616559327724836026088924",(let (_,xs) = pfgaddrstr_addr "PrLoRQTK3QP55Ma7GXSjiVS1DPmR85c2N86" in xs),big_int_of_string "100644643362694163099408133302809343024163782334970304061438458437121124161821",big_int_of_string "3884307431179122959685673989315392228508797218466793417859019155828849647771",0,true);
         (big_int_of_string "114546595605974438451561892817207054224102010150124095422550960825858656093570",(let (_,xs) = pfgaddrstr_addr "PrHVvfiRjfDeC2kmc7rkEmyTXaDnjsGvPph" in xs),big_int_of_string "63020815040198753684454069113119461856592159981572471087051194203293096367277",big_int_of_string "47362099006230047048938907546304710796307015770653994874652817757427363614990",0,true);
         (big_int_of_string "81031186399784710028214216308426409440364435833233469562928121475490774992000",(let (_,xs) = pfgaddrstr_addr "PrB1Sz6znYvHpwFmkYoEJ6xU2DP669kZBXa" in xs),big_int_of_string "69935712960585172424384115100964517616876400109765030353251564098657116669653",big_int_of_string "9150764426397601904217150948913279304775508469887664131473074061524378181881",0,true);
         (big_int_of_string "114749958537120735303645511330318824539203917191793591595709566834107349322459",(let (_,xs) = pfgaddrstr_addr "PrHoTYHdEL1zDjsoYWsTTFjbfoS6RKTptCN" in xs),big_int_of_string "125323647455729754453993652821860813315590705652381981270863556048295682056",big_int_of_string "43424093995644040128607928303433426602904406837848147794255034893904077527166",1,true);
         (big_int_of_string "67521150967029540951741582125090910049035376822430277667044769033414941667262",(let (_,xs) = pfgaddrstr_addr "PrDM6drw9DQEJsaMZ9iz6jKHNw99okhEzzi" in xs),big_int_of_string "27867565267094609571080769407149419554190681118108114189563103270420414185587",big_int_of_string "26861004362953532161612836750136267940950722489402084101297926868391815307270",1,true);
         (big_int_of_string "53763202785127806591200993484528431516009122178370121508384206446597328174610",(let (_,xs) = pfgaddrstr_addr "PrHDC2tozq3EqfkPjqpN6AcJzsD7Q4vRtLE" in xs),big_int_of_string "75747376417658003458533903727659698123918359902461843487220256170089426064773",big_int_of_string "84283362390569809059865300083015849992561142172308779036695045925252550615563",1,true);
         (big_int_of_string "106851446409234195378244430705226219440714279739227409074970208502583419289242",(let (_,xs) = pfgaddrstr_addr "PrJLVFXaxyMsJFnKKo7PoB97WRA64MnUYWE" in xs),big_int_of_string "111060355835486746466630936595634488852687963679837137440683333359545912443861",big_int_of_string "86417483476571344542614711311287849696376211102354545813745268856351536705283",0,true);
         (big_int_of_string "8857498553981556646203885967508188656240874859905985731824348727313300420963",(let (_,xs) = pfgaddrstr_addr "Pr3tvEr17B5hAaJY46FkiriHBoRFG1gq6Kc" in xs),big_int_of_string "5590935657616943305655648760260054647601696983802310722274477906760551179712",big_int_of_string "98939074238446555216061569299034342438602010987761158626503143785838914206493",1,true);
         (big_int_of_string "58967021340670927676739495231436247680337548304908070023515886499985549179373",(let (_,xs) = pfgaddrstr_addr "PrAzLFPQa5ZVEfg22Ly96jK7KoZS9kjThWq" in xs),big_int_of_string "69868485549598657373554334604312622544686819820614547895579363971249034307157",big_int_of_string "20336204717137950891552093120005541404884028714188634056557454245994034737894",1,true);
         (big_int_of_string "73927401879483650845917358428507174871018362931186879717582590993967054069416",(let (_,xs) = pfgaddrstr_addr "PrRUVPSaiNfUQZ2ozfYvJzF4TtbvSsGjnb9" in xs),big_int_of_string "3329686012822235392361263578174052427211416423923501735405518020131144239038",big_int_of_string "31023098540089121755073292613759710895566560445683449872050564065806932958922",0,true);
         (big_int_of_string "6780587487976436281114156321956466890546191560440059985130313538065859342356",(let (_,xs) = pfgaddrstr_addr "Pr5WkDjjo8EGQmNECo8QG1mqitHPms2S1ms" in xs),big_int_of_string "23111577361402395857467134515546217165031129711548647544820223118555289481121",big_int_of_string "14162868558764195017767434461901626072307534159946951673500217562644242944245",1,true);
         (big_int_of_string "20246084098504185133822577454946216791029371470144318035751359192474876340960",(let (_,xs) = pfgaddrstr_addr "Pr31zqPywu2ACX9SGawD5yYh5YcCtaGFnB8" in xs),big_int_of_string "89022343923348608650887744776206950728958718614414028990358059550580294744205",big_int_of_string "87465879359479631801499268876916908162601023710527508171260463575663209496543",1,true);
         (big_int_of_string "102081811484289886590282461572059171906805119586571044066213195567102193641168",(let (_,xs) = pfgaddrstr_addr "PrMGvVjttC9ghzWfkXFNUskhAHS6v68Bgc1" in xs),big_int_of_string "22011491852720312090221320577184855220758312728585645636029915781985047420649",big_int_of_string "16366672918990096814941349634815908147207634557924497045196120363653638729167",1,true);
         (big_int_of_string "108710590996971583657719339073345299695611247472226642880639159141680940837934",(let (_,xs) = pfgaddrstr_addr "PrS99doGMXDmHsxCRV4zA7eLKP1wMP6jmbS" in xs),big_int_of_string "115277640588343773440463450277441479900382422369327561433540978678846619380911",big_int_of_string "62394016228598555918760130743094995941748406307962975247464476948476966447770",1,true);
         (big_int_of_string "67001998958668952901350084920300228355858856907245889058391693983259227441984",(let (_,xs) = pfgaddrstr_addr "PrGWEWMWJmkjXcCCoSQs5KQKww3JLrXZE1E" in xs),big_int_of_string "68190729160364899484371735387899512679456104981050132440704076639565845224246",big_int_of_string "46454275464051412613041170617912349935430000362549217389480169085170305580336",0,true);
         (big_int_of_string "6742842228259500507834638420931752033590886984130334161954276511572349857114",(let (_,xs) = pfgaddrstr_addr "PrBoBwkVNqQr2E1fm9UTdPmbD22TY88AyKT" in xs),big_int_of_string "24454371727912218509692222886947359774296632770520333638998584427404230444535",big_int_of_string "95818370054560557070569723911499157573016562258500413347448195950234366064929",0,true);
         (big_int_of_string "13570985707150115408823600227134684232983388313878337413427792744331738962099",(let (_,xs) = pfgaddrstr_addr "PrPwtiJGoqhdhQXk7qmPJ15p4kd5v88Y377" in xs),big_int_of_string "97086561533110155134941707077046817869561173840794202417394252271105118848964",big_int_of_string "26496131501136615542575647274650614646424060546722083863083863666818855980032",0,true);
         (big_int_of_string "68261985211451330363772698908319324628776790731923669895498050431276206856622",(let (_,xs) = pfgaddrstr_addr "PrARqjzkN48V8Q35VNQ3wvkUjfX3Cz9FLkh" in xs),big_int_of_string "39811650888823410441531302603024597605644849831210582099554781760822675051313",big_int_of_string "22606281582125520400045305415297055128461022315853513989202003254775197784905",0,true);
         (big_int_of_string "2242068770021798735236756368196467190338640488619429988433716789989748402011",(let (_,xs) = pfgaddrstr_addr "PrKErFLBJcxtmdEom1gYB1Ss3nmpAJmrfS3" in xs),big_int_of_string "31015396752516358197396526059473277213762863466869077696328927195576546110294",big_int_of_string "112626309941319030992731206278486190896787407679832234242889075608101813456324",0,true);
         (big_int_of_string "43929856595683254288355036327812815112418047024417773081624722408508368333718",(let (_,xs) = pfgaddrstr_addr "PrG247qHihhvfW7hvdrQYyiAFxiZuRa2abU" in xs),big_int_of_string "3995208336410468484228087894261736492650185389569887882812447002537719032170",big_int_of_string "110700270077417211086738596011618374213108844936610589078380172730332118213898",1,true);
         (big_int_of_string "80620761683992455942793647248798188181406931263854839008556581473260975121056",(let (_,xs) = pfgaddrstr_addr "PrMTwB2NTHF9stQ25WJhPzyXmwVzt2Jxi7A" in xs),big_int_of_string "44075272331864838062069468663843070518469113571418473810062488740934206968327",big_int_of_string "101303569083731638211849291726359953693038545225778677785563472110913780315039",1,true);
         (big_int_of_string "15336859363596785772543188721766890859813440596206016485748953886577050362504",(let (_,xs) = pfgaddrstr_addr "PrGS12i4fRJijgXfZ5B6fDMjj9ZMkGsRVa9" in xs),big_int_of_string "76501226907037748644813169939487516469853786056795577413799373484846350139547",big_int_of_string "67875956581303172295834133187654534740983244519168993107659564915799119749781",0,true);
         (big_int_of_string "21030874737004750665315924584507307061999053828000473140212559769961014842728",(let (_,xs) = pfgaddrstr_addr "PrDFe3PdWMq4DUmiBcCqsPkgMcN3T4UjuGY" in xs),big_int_of_string "90976754838490118482766066737750597502515772699773845686945832865495275438293",big_int_of_string "95783967650123645222435031794599809706260376777425864974109473962588984122661",0,true);
         (big_int_of_string "22501621661742563016263672631969046740784831369334556516482257906617024144592",(let (_,xs) = pfgaddrstr_addr "Pr73zqCqY3Q5bofCziXCGk39X4S4ekLNAm9" in xs),big_int_of_string "36386720365559101958561234871295189237674679035697011030392893816121746545491",big_int_of_string "96066054728234778251154437309938656932291396579383656003188512232684035856498",1,true);
         (big_int_of_string "114781614156219976086840662648546618974588497247051761911517513986219731936123",(let (_,xs) = pfgaddrstr_addr "Pr651i1f7P8C9KeA3M3GErSszhEkE93RkeX" in xs),big_int_of_string "98293965076639771499934887916828891659755841245686505993447745619244070742705",big_int_of_string "90985763662722645812443495488729202068167434922570510181345654903146491724798",1,true);
         (big_int_of_string "58925774638193771880876767788198819663398158875652083578779311848446487884874",(let (_,xs) = pfgaddrstr_addr "PrDMEFWcsSU6y28LcTjqofvbmu9zepx4u93" in xs),big_int_of_string "113088308242851045523135284251299658018608089403258983191256474111860567755443",big_int_of_string "5553028328769343081308321939362293978508184720453414018192605773134758382799",1,true);
         (big_int_of_string "64169714749615073209720275747231648333431852187086779930349075212093747789839",(let (_,xs) = pfgaddrstr_addr "PrBVcQ56qitQDtztYsL99Qnu8phdF2hfqz2" in xs),big_int_of_string "6265361091348290682389700221569391758654312064772727103118531420257681895090",big_int_of_string "69262506194922813333498513189201564818056378120923432941958074981465841109106",1,true);
         (big_int_of_string "26368948464564316682433947825380703116348720727227769303710508355823514202294",(let (_,xs) = pfgaddrstr_addr "Pr3b7GHWeCzahqSxzizPJusqeJbjzbcTGhq" in xs),big_int_of_string "79460006259710860909938732713013541758847664081942102158767990405459106582351",big_int_of_string "94658252218383580921637313314228698057049681007754940095328445416298564798045",0,true);
         (big_int_of_string "95229914137840163190726681278939070364191806570979529047848494737969013437163",(let (_,xs) = pfgaddrstr_addr "PrNm3Zw4K5ChjDGhqJoWykBcokJ9AxoS5WP" in xs),big_int_of_string "61918767162630314404179411854479652982980994116171222146832783216347781634619",big_int_of_string "35814176438728773874567944937362214324900233744122266040458835488417035891182",0,true);
         (big_int_of_string "52496111615313730174076001136106003235403455735671523004994120593416470374763",(let (_,xs) = pfgaddrstr_addr "PrKLaVikf4qqeRVQpDo8JPMpragnYMnknBK" in xs),big_int_of_string "11289540925172996601150111714597584491991642190419525316124861556455222005325",big_int_of_string "55128189175026448395353632893415687616042785276016226329138504099678899471029",0,true);
         (big_int_of_string "51955315448839224549823279162685007285908605155278832733469480112305574143447",(let (_,xs) = pfgaddrstr_addr "Pr4ZZQiSNqFvi6pFySe6i1PfWf7WheHWnjQ" in xs),big_int_of_string "92556918681667324831115441957161211105575147595310318749815653620576156795050",big_int_of_string "38019131018369010815348348379428034187867464033693861237513155512764988568212",1,true);
         (big_int_of_string "49617092935622364459185603537788398554682817231458935856004662227491301867901",(let (_,xs) = pfgaddrstr_addr "Pr9WrAodmAcMyaLJgpfnubE7bHgyjPouNJZ" in xs),big_int_of_string "17710124719610552087243444178424765495469863719578860358487050856596005724025",big_int_of_string "47695968229113635551525059756489586139621552594208142060657013606646110143812",0,true);
         (big_int_of_string "100523733654831882394158755828517092699270527265101705755236757525288083278836",(let (_,xs) = pfgaddrstr_addr "PrFnHkD9FNFfHHjhYjA5Fs2b9ZYgFGRwxiv" in xs),big_int_of_string "103156645915783134871681445898482752282253850888478165180326819988694118099943",big_int_of_string "108968276741458700130643972090961802022997983366615488754260646441879173117235",0,true);
         (big_int_of_string "103504748151997857640199815856992206660023371332498126111655245724802629279996",(let (_,xs) = pfgaddrstr_addr "PrCdoyMHH8R4xpNYD8zkGy7FFzsp8H6BCkC" in xs),big_int_of_string "95893410452520620224108698030434629437899617086697192690503999735439202571823",big_int_of_string "11549357916531620444999304040967472560120370199840588482051508892461947650197",1,true);
         (big_int_of_string "57812923249109564458795053427793076058136176620147662616503107070584595970411",(let (_,xs) = pfgaddrstr_addr "PrS4kTzkykUsE6YFEyAqfrnMGmLeNXgFUFQ" in xs),big_int_of_string "24556177729079986954382477715782118809442419632078508699056133469251096966338",big_int_of_string "83030932418254804905411629323230212398026498081972284859976912796509458211358",1,true);
         (big_int_of_string "97798686496761948668663202926271028956609617413864452752702045228842903459458",(let (_,xs) = pfgaddrstr_addr "PrFyfVsNS6QbmBTB5e5b2sTmSGXHamRwpQA" in xs),big_int_of_string "109242554320999865669735242466661758018663013141899339725283781447114088828296",big_int_of_string "36416552395734389843925352248231041237364261209926517798544630688844055196471",1,true);
         (big_int_of_string "112271220610616963071076709127143691921731466914093628184099284401507954176454",(let (_,xs) = pfgaddrstr_addr "PrCgywwdgvceiPptNam5LWCdkvw56LBh6wE" in xs),big_int_of_string "16639005726318856241339823213115199319840885897685604662686007230306900703365",big_int_of_string "106495755863487201416914703326932437442282321654725507241398842733360649972645",0,true);
         (big_int_of_string "64620969239899437553508392129097251907747205848857962287662184502969559360707",(let (_,xs) = pfgaddrstr_addr "Pr5LXGnaCpveTQY8XBF1zNJCri6A5Au5u7x" in xs),big_int_of_string "17821204642489691354531778893867671565626349886640513208600290397082706843072",big_int_of_string "73571398591624202573728100687285187590616745816759157973317551360237608374063",1,true);
         (big_int_of_string "114349805917763961439340417966317241897933613363900944008110877276409477909418",(let (_,xs) = pfgaddrstr_addr "PrDJniD31GdzxSwq3YDoofzqe3Nq74iAamD" in xs),big_int_of_string "59030731512410114076754231316887800429950619322437436497765616931412339284925",big_int_of_string "18728322385725639823366172355951797402433708141519074819320231004387494304566",1,true);
         (big_int_of_string "100716856847842096188240496465271661464321751819356172907684292435379023419948",(let (_,xs) = pfgaddrstr_addr "Pr88F1WAENH62BrPm8yCuRK3dNp2R8gaXnr" in xs),big_int_of_string "19753967700253372298445731064935194659999139502257563699985158593347095705875",big_int_of_string "79828176049500576593931516542267167091804273078920575727056252840645769434312",0,true);
         (big_int_of_string "70813925979221138940955589423958343455785239402128953408040890003742604446661",(let (_,xs) = pfgaddrstr_addr "PrKA7uPoP25BE3u5C2Weykub9B44HP4a2vZ" in xs),big_int_of_string "73755688596025099437319705826753321564573508065954057450711227018121063401904",big_int_of_string "54285014659076100894811326791137328525000453150825998099364152486680298645541",0,true);
         (big_int_of_string "93882628820929647426643101384174105299482711341471104955136156459382701416235",(let (_,xs) = pfgaddrstr_addr "PrNDifM78r6ZMwEcQVR2AW8ThpocPAnjY9d" in xs),big_int_of_string "76751546958035123013241293300292153484494092156920325519626372525395522559106",big_int_of_string "29340083072978781478964505643939084729379119205179387761816939857864881096971",0,true);
         (big_int_of_string "110860568940685393771281440881213910877675560230356635901999262933338091512438",(let (_,xs) = pfgaddrstr_addr "Pr9UxDpbEgoQUzbMEx2RECCi1Sb51ufDNd8" in xs),big_int_of_string "40369413138754029818614145800726591813174862976034339851375074409505941503076",big_int_of_string "25719118881411543625589700800038787175388559404602755857430192028822807668170",0,true);
         (big_int_of_string "42725823068276472836327153872950594968312518656555645262700815803194051970311",(let (_,xs) = pfgaddrstr_addr "PrCMjRDPkQ2D9HboHZbdHXdKYUgULesqJCz" in xs),big_int_of_string "95423472457925061144011322256197420274549179473927354315240796654991677114629",big_int_of_string "59404640846267921529524216662969397554995817747594200420681565394664197986183",0,true);
         (big_int_of_string "50978770881659922525085493415338038698864854993863479280540834451767149966531",(let (_,xs) = pfgaddrstr_addr "PrHWRU5zorjDsLd1EGv3TC7xJ2tYoSR8hqk" in xs),big_int_of_string "37636029541152087202353517167509889477817596443970053263817984065406381308444",big_int_of_string "6533594618195866148025237599631306265822232497177726405529282175644146623790",1,true);
         (big_int_of_string "40302556281490109758097568873164668926590206648762480118175964754695179925931",(let (_,xs) = pfgaddrstr_addr "Pr9VfyR63rZEbmyLM7Sb3ks2cxMnLWwYzJp" in xs),big_int_of_string "113285442248781885918365540901913209903673034870267356833282230924550408711358",big_int_of_string "38381763309818130993918163617453686675477543133582477801330506157480949152211",0,true);
         (big_int_of_string "61285362461341166173713661203874923493551189110096767783781109652942033854318",(let (_,xs) = pfgaddrstr_addr "Pr93P3TmVciRuaChSWcD3m45CQ7gMp7P8RX" in xs),big_int_of_string "69972255750917004242084305540941844940545722213747554387092437777151953450490",big_int_of_string "55954993570789618552003998184879636725993167610486243628625935206962879768937",0,true);
         (big_int_of_string "68012706837059048536721800407080451560829117596346166057723804521308972497179",(let (_,xs) = pfgaddrstr_addr "PrDrbFb3hNXgSKkeWKcXMhvjjTHRsAwZyyw" in xs),big_int_of_string "82100036583927838944141495664860813270982275038985781556042345664870391804999",big_int_of_string "106723979193159100522018940481994076284250625307097853537326071484449850265327",1,true);
         (big_int_of_string "35663478573882622190031932921066000813351791555147246931224035704174844297789",(let (_,xs) = pfgaddrstr_addr "PrMgBA8WUvZ169vjWuXaRYx2KEGnryc7tR9" in xs),big_int_of_string "17422381020883715363223014090350897835033700359233479531261650644261062204019",big_int_of_string "50372595986686315486059187510479906868906015592782671415012461053344102962418",1,true);
         (big_int_of_string "66529209983056334178887530535314899028427612661335702205911822387206427896018",(let (_,xs) = pfgaddrstr_addr "PrKHFHS5dDo3XXkNPi9bbtHsHB6Averc8eC" in xs),big_int_of_string "99098810629920394146658762131207280624562303273519107679141262428663445604557",big_int_of_string "105738573392817385058422447577937501925931334424063854424744626631689168666883",1,true);
         (big_int_of_string "68446504902463515606950116687312863187036325629844523308219169934605853120239",(let (_,xs) = pfgaddrstr_addr "Pr64oBZzAoM7sjyLu28am7hrb1ShmdBvj8c" in xs),big_int_of_string "23080418618288637767554846623109060637867165539150603912504953534050256162250",big_int_of_string "12843015858376122908779233735055590563809092337805402915158390430794761648396",0,true);
         (big_int_of_string "29247295150318547709090738571784341111430234683585839417970080179006669822455",(let (_,xs) = pfgaddrstr_addr "Pr9XV7H6DTJatTyH1HWxvELWrcxUnYntA1v" in xs),big_int_of_string "20477313558597505470668128313004151466941267198130832350059900792494418783861",big_int_of_string "66737494164764099399944573991673043107454316128932344277051264887556075973426",1,true);
         (big_int_of_string "52841196744960963117720992253760777975846078520453501413052266823487296296557",(let (_,xs) = pfgaddrstr_addr "PrLXVyQHfAKTMc1UkiseFJB32wZEAHmSPmk" in xs),big_int_of_string "111252087710581356098577808032162972889638126651619959906645679124669700386254",big_int_of_string "89848166137650194127868649657799954219985454492272338618273522436718927769042",1,true);
         (big_int_of_string "73001686407430312859999932168245879414184789132432953892293207581865198997119",(let (_,xs) = pfgaddrstr_addr "PrEJn4PVP8uvwd5LZXEJLQUqcm4SUGgTE7a" in xs),big_int_of_string "61395513926908046340699625556956767309004378423094006617029542963934087274276",big_int_of_string "41121199727455225558207496837817877051560365785122245342613703608991924616595",0,true);
         (big_int_of_string "39904939519821766981815948950125802418661852654557603789622935169319771897645",(let (_,xs) = pfgaddrstr_addr "PrQhE2SniX7QYGKn3ZN5uvx2WCNKmWjWDRK" in xs),big_int_of_string "12309118484402076581716447255887678268887221263824637348965645430615093412897",big_int_of_string "100197219034593651901315211617151912843499080757441062561200138215558343801976",0,true);
         (big_int_of_string "10986461274866501227457055810436174500469580486343007515749650667513929747865",(let (_,xs) = pfgaddrstr_addr "Pr5upAVE6mvxGUdTtwduFNGrsV3PyQSZnkz" in xs),big_int_of_string "25910375645008579650211649291305047907210616386228133836404773451332511859629",big_int_of_string "111415662360482794866823652156691613135023144120610656559676622591367425456316",0,true);
         (big_int_of_string "31177652671724933710089403162446904506122750527719240740465524201194959349488",(let (_,xs) = pfgaddrstr_addr "Pr57MAK1juXYtbbYArRKJNaVsmFkVDEc6ka" in xs),big_int_of_string "80282093105431055266132951948322275773101986720198138791559465426265800693149",big_int_of_string "13948793370562801026354230332552772727296262029050794820175941233381319863688",0,true);
         (big_int_of_string "47571810450022244361195867288744457165061894697815110356604463139397082633323",(let (_,xs) = pfgaddrstr_addr "Pr65vwG3EGKzhHWa9grtiSdRhKNiXrxt87V" in xs),big_int_of_string "13926795733980594386496122075410030385408377638176131300504079356867344190808",big_int_of_string "36373410071971862841251232826150417407708210180940639399967605253237069791686",1,true);
         (big_int_of_string "104689325967714132314552495484614189642884813926037695979443926767358155779524",(let (_,xs) = pfgaddrstr_addr "Pr3RKiZ48EAdBVvXePdiGndvb3sVXjQd1sG" in xs),big_int_of_string "113374556613501251135954864419347275969366636385277779979305150248681393353437",big_int_of_string "84670693966687253617978312066913871846140641179024303072137909674523072431863",0,true);
         (big_int_of_string "1267258598164167346666143511671161311499863194467944115776411878697441814203",(let (_,xs) = pfgaddrstr_addr "Pr6r46R9xN6YkFMm2cLfH9hB3WRgikqXA6z" in xs),big_int_of_string "40355579770931517759728194532654157079814282678830236560454176749603815088737",big_int_of_string "76934998582308728707965257428190629836433659865733548076270009543950463426537",0,true);
         (big_int_of_string "99540830406883502221004644414261216753327729808926877263076919507973451396801",(let (_,xs) = pfgaddrstr_addr "Pr5aCiuDGvQunjhsyeEBcPCDXdH5rVhPKU1" in xs),big_int_of_string "32185728508718535812578639661869357071135104117027687431430619587508826206247",big_int_of_string "59410876827789453871552740172817069960342590453020297484788225057070909428209",0,true);
         (big_int_of_string "54588254225423201131613398641911216868701699316031644231130949387674446236651",(let (_,xs) = pfgaddrstr_addr "PrLXCo66bTBiWV7Vb4UKbTrBUib1azLZb1j" in xs),big_int_of_string "92274050335591131393237909240005716106206408647683248468546444723148470789447",big_int_of_string "12811317258946481363851258474181710842448915271843726702442388271048773183927",1,true);
         (big_int_of_string "9324529780910386410944919309629234245146340102286950900180846365071682360482",(let (_,xs) = pfgaddrstr_addr "PrBJ3cz7Ukr6q42NkxTECescqiXUrbRvv79" in xs),big_int_of_string "85167651781374487148286340909561412674164300412938100527740953293159067942320",big_int_of_string "504699635002645361652148575886966036384261499681032811347727676947817915543",0,true);
         (big_int_of_string "33483968734896008671651480106400672141095077509215501487654855700502548918520",(let (_,xs) = pfgaddrstr_addr "Pr5uhJLtdYDhqcPFVidEAZnipjc4PwDxDqb" in xs),big_int_of_string "99778539102156771284717795839319283711810776487270914775330713239825917284464",big_int_of_string "11987887252248981547719922371482428250775123386604950389056823082621462056747",0,true);
         (big_int_of_string "75937833502075539034738891770295593175091064492214893425095203294576777436500",(let (_,xs) = pfgaddrstr_addr "PrDdE61FGpsjQFVGKUzKRAQmCAANwBQsgmd" in xs),big_int_of_string "83263402357186440105236688267233505552143268473570653717855381731063890550634",big_int_of_string "105997328050542884583682011606932594150860291154387465700421165308110781498675",1,true);
         (big_int_of_string "45287058386136761329454367766132800653260260073215002904337872072706690798272",(let (_,xs) = pfgaddrstr_addr "Pr9hx2zD8DGDKUPH2LLBSSTReCtV8arLETa" in xs),big_int_of_string "66004189168718554552845246558687777332143040487335588119415625973732698894489",big_int_of_string "27779635835670552134520181357912759401370454066833538996800580817724432867672",0,true);
         (big_int_of_string "9496571436790884385515821387003847462158297646663934464988466340772341245251",(let (_,xs) = pfgaddrstr_addr "PrLJqsHmV4w95WDUobYHDLvssVEgGb1Qd2D" in xs),big_int_of_string "94293168981466147440341678849741840545718858906214816782058190614589097985642",big_int_of_string "53576255379522852506829589494834008896602565199490907399257376847752490064295",1,true);
         (big_int_of_string "7666369178777258274739978908012282441535716272312621748220214561625414708327",(let (_,xs) = pfgaddrstr_addr "Pr6TX3HHNB28UdzWNT2uL53RSsshJtweX9V" in xs),big_int_of_string "65860278894599468290382005667742938711075532290246875579318749468214673631513",big_int_of_string "52448333075967662924127307601011631514840557165272975342188168845390690299386",1,true);
         (big_int_of_string "19134094496329613859170920392165312677804054624935844512713105694974665540708",(let (_,xs) = pfgaddrstr_addr "PrRCnu8N6YNXJ6yVavfbMoFAKgJyLnyD6vn" in xs),big_int_of_string "36086113825923028694018317420528917324153016541603738239834704021384414529729",big_int_of_string "40319063548745708623801044498271144660420463307842560585958969020502957846909",1,true);
         (big_int_of_string "78264671135556398955143651005284697441027059407265807633792816186440677537837",(let (_,xs) = pfgaddrstr_addr "PrPifJKLJFBfyDZEqV6sbLnzGad1cS2Jzem" in xs),big_int_of_string "88381515673711571056331299341541804780568407580171947895684765672533999012608",big_int_of_string "114876358918747484056534396570930936383587512569469938259801904195727683381780",0,true);
         (big_int_of_string "47447348007233474363648530012430874782895812300224447038698740042062032264447",(let (_,xs) = pfgaddrstr_addr "PrQbygbtGi2bpdauYhbApam1sAd1KKcjEfA" in xs),big_int_of_string "94474465571146090483685794828845612552257616210070266138060139822064304321617",big_int_of_string "18220693783687111763267455054238156013141843359254244866027429334924289771869",0,true);
         (big_int_of_string "85817423095324138290671168154569133376691519450960195127781183526448824751652",(let (_,xs) = pfgaddrstr_addr "PrPBSVLvj6z6Fr8yRy48FnGSf9iVPJ6D9k4" in xs),big_int_of_string "17988221755828414337384110485254454076350244531924916490516719058218370724978",big_int_of_string "76419901207451900799383067510108516174230280950592568265896446188532688965014",1,true);
         (big_int_of_string "22889691429141198584844903218832583162480292050300726251147846658568720277875",(let (_,xs) = pfgaddrstr_addr "Pr6aWkmHdzk2F1gsUMgqUKufqW1amUJ2anY" in xs),big_int_of_string "72157019132655074352075467564246545323920000069948658207003162820041554977440",big_int_of_string "70046969255970375205342213612847798426351213066721339151659241768416024874342",0,true);
         (big_int_of_string "67499427704168941114663513354751160114709364369466027530234536043322182449316",(let (_,xs) = pfgaddrstr_addr "Pr9HW7QMEkrGyPHmFgF855fbyX4XZNGrryc" in xs),big_int_of_string "29569295515258999363818443035820326154398229039773958467123005065046845467452",big_int_of_string "71680478679091408977060663671103248331657869293892930952815047185923174474255",0,true);
         (big_int_of_string "65387162815983824678573633728603669890186079114600511604703733502873456731420",(let (_,xs) = pfgaddrstr_addr "Pr92dq8PSGnxCa6jeNLUPQWJBuVv36wbX6W" in xs),big_int_of_string "95983206348590551545789045233585820508347467389368393214380077640663592101571",big_int_of_string "73670323958684603801162278992666178788890531488986937564829773287154637254572",0,true);
         (big_int_of_string "91807692050687810295477740292425177150990602722213730517337915188107686235140",(let (_,xs) = pfgaddrstr_addr "Pr4TeMKvFGYQns1dVen85N9teP8ZZVXQKHR" in xs),big_int_of_string "87714461980085894388978964403048901050025099831123110274324463120992707985000",big_int_of_string "38805109192958678561436970254084832641616982290740823453192446650532357748393",0,true);
         (big_int_of_string "90613525450168270719634272293407564896660791777867623830677042571717943120222",(let (_,xs) = pfgaddrstr_addr "PrLuiTrbkW79YgiDeaN6pqxvPbQ8y8nPMUh" in xs),big_int_of_string "9739356874300465634377988938219064919540984984996196241956488850132061314502",big_int_of_string "38424241938998797038991146628072769571126006981062031790306697106655772836843",1,true);
         (big_int_of_string "62825931083997257952343289814445600517014144314936420522575730494653350076619",(let (_,xs) = pfgaddrstr_addr "PrCxrFsyTrZN8gcebiGr2iggwvoRVKERzZE" in xs),big_int_of_string "16602729891784657106247882859500463467841031039926865499532769192400746404301",big_int_of_string "102797369899794344470562042241787908505363699449508675696840991398331704539699",1,true);
         (big_int_of_string "36604229000616413491231895426364545607357468178676694833083866830529953951144",(let (_,xs) = pfgaddrstr_addr "PrEkkRe69UnWVSQ73e4ecEh7TD757rDPHaB" in xs),big_int_of_string "112461944617692746505809872989049612339661693780053140312789785704777359614251",big_int_of_string "91043321374359705155100281241060346142587813588804365188964737213117157896116",0,true);
         (big_int_of_string "29009720374192850653641570416614302866650543213955258642041784701031672109455",(let (_,xs) = pfgaddrstr_addr "PrNRrL5gKE8k2x3P7CWQFFn99aaP1HdwvcA" in xs),big_int_of_string "18424159217264162408814318930022887897403341475926899024958768300912143590164",big_int_of_string "28750243274176015046003901096137762114772543073596251123550505593040048433028",1,true);
         (big_int_of_string "27099125514733951733175502024881576170749743593184467061221895402236391810009",(let (_,xs) = pfgaddrstr_addr "Pr5zPpfrkGogoZEn4vQKzYaWuyXLEfRyxfq" in xs),big_int_of_string "77784864940899885971249895386959770067420355763342039488118467869167945656590",big_int_of_string "28211489024745366377985792375660667377929703427174491574095601572001742529570",0,true);
         (big_int_of_string "25628270507233811206047752155889870270146735890577879954206447014634744703296",(let (_,xs) = pfgaddrstr_addr "PrJ3jeDPSVvy6XHGi8VyAvAFuj51pSHAQc4" in xs),big_int_of_string "95146516808729284908557476846715770537579266030352778618624471231363340068351",big_int_of_string "42309507626964475523534386338453911606397347903494730542072887805975716296309",0,true);
         (big_int_of_string "79125627099012547654466870770157008048221202295873388200487588224304904337065",(let (_,xs) = pfgaddrstr_addr "Pr8EQvsWwbWg7JxBmk1HYrZgS8NDvihUQfo" in xs),big_int_of_string "79072788496299952591129054834380979465138619782621738144404123552664221511001",big_int_of_string "30951426189735071273460174664790312317383089865928509862019555367347006797856",1,true);
         (big_int_of_string "45925955745292081518954341877614754641627014570863725643969343834351840751756",(let (_,xs) = pfgaddrstr_addr "PrAxXhvYn9Z9uysegALUM5AxWuLe5cCGb9T" in xs),big_int_of_string "68409624381463809264677006449378326152382398388589659737334089428517438083611",big_int_of_string "82031936609688703419298629057829216855162600686047738091682200022180942182432",0,true);
         (big_int_of_string "78819153802966412921650126396837224841217747111397266852399720596919098012025",(let (_,xs) = pfgaddrstr_addr "PrDLFoJF4j3wFb85Eu46ZKKvcKkPiXaYfr2" in xs),big_int_of_string "69746699661853345742557131913661113963844851929902498844295333494954300888601",big_int_of_string "5740510550666903925025069334276305769433854091334400511999276199821893422884",1,true);
         (big_int_of_string "21905348109363877089814816377884727916235767836620859988561513504926275063325",(let (_,xs) = pfgaddrstr_addr "PrGpCzik7gF4jZQPEkd6ruk4gY7Yq153rkE" in xs),big_int_of_string "77340132969157224676821046194344101766006062476021654964557079453928444663669",big_int_of_string "22722802735507932199894303859024405853612990973382711935632905928596613040859",0,true);
         (big_int_of_string "54737455036983729154548415941224640893208388799092469846158952369833766787124",(let (_,xs) = pfgaddrstr_addr "PrA5BKmZ4bUwA6UzNknHLP9KjUwTVTXpKfL" in xs),big_int_of_string "108130644199731814532985980074714419929135814280646569278647858967585341888679",big_int_of_string "15920814614905593923581738777666011747730805823531584022893203415797238180674",0,true);
         (big_int_of_string "52630680623383214919994131486382106839177744080505716565019158765276883480979",(let (_,xs) = pfgaddrstr_addr "PrCNEVJ3M4zsXGceAyCBQxPSihirBtTTBFK" in xs),big_int_of_string "11297846611695638409786406493267433092184082700289843920145680446781993573379",big_int_of_string "44698027324277821280530111804489833121436321237520460221493116253513315562066",1,true);
         (big_int_of_string "42850775772955379940354637695900599586996400747573885560267774388255890994794",(let (_,xs) = pfgaddrstr_addr "PrJ9kx6wbfxbPcfWCbRXNW6KM3Rr3BYppcZ" in xs),big_int_of_string "84140175491832936413515346231691296887819951010114515871017134674673884049707",big_int_of_string "92814837128176266533884524992199619524892991230049097081257686667215687826649",1,true);
         (big_int_of_string "73662755854577875986088719884149908500861349167230961242672376575270611384845",(let (_,xs) = pfgaddrstr_addr "PrDeqv4FEvPAueRVdEjPandbNbwzvBU5RKa" in xs),big_int_of_string "78381899099351274968839653062900311538971016356195682548182040800204093522332",big_int_of_string "65165179977163225364960984702414653652433890452251715106373638019922708874764",1,true);
         (big_int_of_string "49025685549779930225171585067489423315642140942886839849511782384995406791290",(let (_,xs) = pfgaddrstr_addr "Pr72Yz4wEfFcNFnKaTzMmvXTew3wzbzN5a3" in xs),big_int_of_string "70691595417682535108216560027545193638916218922687818468702537088013767204836",big_int_of_string "32784584143406944871238215267925661682737262550975494824653279339071863055257",1,true);
         (big_int_of_string "55955828372496539404224080537762451908765931741340012169752855141604259706227",(let (_,xs) = pfgaddrstr_addr "PrGd46Mu5kDgTN8rs4MWoX9BbdNuwWKYHUz" in xs),big_int_of_string "46832311059275005724175654052724901076004576416832469252430809864526590019681",big_int_of_string "96853523304891112039334478437831200757637015997161719838569825188476934200013",1,true);
         (big_int_of_string "24106927100861321939549034247376497750030853970803105642368418273490995874430",(let (_,xs) = pfgaddrstr_addr "PrEQADJ9c9B7PfQTFNJEGJpG2XxYMqXeHUo" in xs),big_int_of_string "96019257498575622028951008629928550611155452121822974377906839089900763148329",big_int_of_string "8093829349986694187580062693027598695567124364819194366983192193873853040032",0,true);
         (big_int_of_string "35076436120136865205479839241446274011455785906680956550890703910941737447952",(let (_,xs) = pfgaddrstr_addr "Pr4XwSpYGrbnLyLtiwWhSq5o3BoCorfp95x" in xs),big_int_of_string "105583238538160056236603806070750121313902429982453986357731200984385016841744",big_int_of_string "86407091397580466802059225260360444120472340701595344784070732499542127572694",0,true);
         (big_int_of_string "37418373952050992326672143812482512095649023712227997217679411501002531537562",(let (_,xs) = pfgaddrstr_addr "PrNoia1kbPPTZf7j5hgVYCvYSLyAtxP2Ncn" in xs),big_int_of_string "24569254671699547656936442571891699251030974061741112423096005256301885808460",big_int_of_string "38731866744549207808275255706163937179363479986731704867413340792000902308376",0,true);
         (big_int_of_string "12984801780898187014208658138782795157387004470493499726441176726152763772386",(let (_,xs) = pfgaddrstr_addr "PrByGHNyupvjdJipnxiGVFCwBExKzrpdrXw" in xs),big_int_of_string "86551304312059533395875483381238959119930376838953672655653055343537806253264",big_int_of_string "61034392310373002759310626276231964161125313095123241759843990210721954997404",1,true);
         (big_int_of_string "81372174908795194411407860503109849026086654330656812172542910245946189848575",(let (_,xs) = pfgaddrstr_addr "PrDWnsooufKCFG6eWiUDc1U5ScUFfUrR3ee" in xs),big_int_of_string "111585855660253406037206506935598815547919055387677707123272602776395291636587",big_int_of_string "41346757725351081668901855414806894027057162215629503422213964098372330804681",0,true);
         (big_int_of_string "114855305993159512433283218587466003284324794337663009539261139647124002927742",(let (_,xs) = pfgaddrstr_addr "Pr3hshdSrDRGPF8LLDj5i9Yjfn2GXPu2fFr" in xs),big_int_of_string "94930654797885807374019333712626505785406200036323838915294588133991929483477",big_int_of_string "39432087752923925382028512142797527353620386189141318772552813216813799889543",1,true);
         (big_int_of_string "19384779942624050110594416746882782958601187318672523605782872963977605451123",(let (_,xs) = pfgaddrstr_addr "PrJ2yYYx1FFXf5ok8tBrW6bjUStUAuaP2nH" in xs),big_int_of_string "96247799607767966922604138482700852815976882790996384520847229900983825032258",big_int_of_string "17079943991892972120707583380432356654976966703535541645288212039629055777663",0,true);
         (big_int_of_string "80159072986678736819234011096597913469322557434966453279439172923183106353535",(let (_,xs) = pfgaddrstr_addr "Pr8MwUNwyv8iQ8qwqcFFzxXXiu14R2QC2wL" in xs),big_int_of_string "65802252645215447168559643192461312601819775194622733755203882520001130417614",big_int_of_string "69540695002161871085970248068042672645290885813297838578203388670699363484605",1,true);
         (big_int_of_string "10517564831657863753570397638672833721055480293499713234149147124518584550091",(let (_,xs) = pfgaddrstr_addr "PrRvrzdbZXTkViZpTj4ktqgJBsH9LNo8NJ1" in xs),big_int_of_string "27471535911548308400451458819152027424054490837681305280471962537509464784467",big_int_of_string "93509115193457956670433579078975962614952744403267585885147103542251151119775",1,true);
         (big_int_of_string "19207401746290889076293516023908590036962912626649585116467437159764616182907",(let (_,xs) = pfgaddrstr_addr "PrKw6b9K4vxzDRNRJL8Wh3k1uMcYCVjTLJe" in xs),big_int_of_string "68383200688440897038774399341289671507296747812123189635496742516089085068577",big_int_of_string "21786425330334573353519810860160862408087548664343653012208543752296226762535",1,true);
         (big_int_of_string "60410316856015181266914895570855887247160477964666905702687494436568907280110",(let (_,xs) = pfgaddrstr_addr "PrH4EZzFubfBJJa5nxw3m6qHu5QEnF6JbNf" in xs),big_int_of_string "42842086896516366610168612947209396878803916424886134441319283541628561380781",big_int_of_string "108764431590997016085115981006005770002672980318011017077626619507143736806799",0,true);
         (big_int_of_string "35203392490301938718858645062957545428955545676943444102909762345519835761017",(let (_,xs) = pfgaddrstr_addr "PrMseQmiGpGSA3WzXfwF6rLG1PpBykGahEW" in xs),big_int_of_string "4159622392637329545734889174520095479172042255253561788559504561105061669511",big_int_of_string "37099995592877355176041282956019789504955324777371724464439790101340273026303",1,true);
         (big_int_of_string "94380862701377353855409221767603077020649686372913230270400379693986724616831",(let (_,xs) = pfgaddrstr_addr "Pr4442wBNVvbfhkmrGmNAzZVXvC2TgzqvQ5" in xs),big_int_of_string "70902757220319640869806080713822492823784432664207218563617453225122801201605",big_int_of_string "108694463606480700304972965840457450423645212962689448459197959260828962381204",0,true);
         (big_int_of_string "51259130726901418068359764701399821624925567220546446777464401290741527257359",(let (_,xs) = pfgaddrstr_addr "Pr9y2PZdnyW4JWZ2Bk2nE7ustK6MBysGoX4" in xs),big_int_of_string "45531679932017383079851014385240243700325358064978409198574087095511241599170",big_int_of_string "727207255566665116906960846646742923145078277812715532259713080209956369461",1,true);
         (big_int_of_string "33197474524435707966656074685318845392468261404476523318593004198116516179571",(let (_,xs) = pfgaddrstr_addr "Pr3v75ZpGwmSCFHWoy1DEkHhv9x88JcqzKu" in xs),big_int_of_string "74413752562303132176337074930094913480566716112306600025645978508157112930692",big_int_of_string "94024200996594472656293676189750589328443533496502084036616822424773533762332",0,true);
         (big_int_of_string "83335724129056488314143480767976869223606231067463671071010219568948749419311",(let (_,xs) = pfgaddrstr_addr "Pr8HNgMtk5yfCGgw1qwgix1bUg7wK9Tc6tk" in xs),big_int_of_string "71102550543454447986640393813228859604102749066830783697045990518218424457791",big_int_of_string "68997605989665995179326970850602149112856951137708437106442881662996231862943",1,true);
         (big_int_of_string "107336964568533813687825275299806181666337362059941041694388633505181119193247",(let (_,xs) = pfgaddrstr_addr "Pr66PEQ63L4SZs8w9FB7pcwYZHFX1CedP2X" in xs),big_int_of_string "41759208662600709835497920280292183994958048379035763714144531381654883949613",big_int_of_string "88064216475012738763266480550823346657522228670474961317625890723970385909070",1,true);
         (big_int_of_string "9397669652492543668413265948298188377982990730735769680389714586986177623532",(let (_,xs) = pfgaddrstr_addr "PrFLe76xuXwpo5YVhKpyAVchxPtynDEQDTt" in xs),big_int_of_string "62564178631625664172470704131831518564522149162563856230313080018441722636871",big_int_of_string "110958176325016618885500614566712490952423410269017849204670457015749567994622",0,true);
         (big_int_of_string "95072443915647737191326656378095031238354920656688556521044785192381060989487",(let (_,xs) = pfgaddrstr_addr "PrCmQhka58HXwat1n5VSp6xuE1RGSBsihN1" in xs),big_int_of_string "62478038872229913351307443958385058565586832087318854032455323412984542049619",big_int_of_string "74148415450280250416068541362418820435374621061938976520144782200982398559149",0,true);
         (big_int_of_string "8991679010161887570288010338232581802436764348432933313001625297012398151203",(let (_,xs) = pfgaddrstr_addr "PrLj9iA7AXrWS6RucjbP3PdQenUcFZycoSF" in xs),big_int_of_string "66203816131169756368147564393613018249118813049479690573900312516424114164063",big_int_of_string "63057102336491803783710787571028507990085784930717440427184068703114866774356",0,true);
         (big_int_of_string "96564084032037388261465804063510309069348529632947426077975808509818636176333",(let (_,xs) = pfgaddrstr_addr "Pr3PyhTXryTATexECApcuBeeJTjwNiU5CN8" in xs),big_int_of_string "38636966133377539018536849797627588072754718676342771298590906696643077463418",big_int_of_string "91131709345352780433193722888612160801383068370658340856476015698773224742764",1,true);
         (big_int_of_string "15697713390546467101198171813600782826079000204588299124042679271852921058187",(let (_,xs) = pfgaddrstr_addr "PrMwTsRhsnYqCbq3m6miBC9D9AXyG6HuNrE" in xs),big_int_of_string "84934472205274402736462695908263368979242804609895234543665154396913236333165",big_int_of_string "67935349173408645052193675071204095066804344100215605979581883632034272447387",1,true);
         (big_int_of_string "47275927021529290543983853449561352799043123416026889362726354452039122875656",(let (_,xs) = pfgaddrstr_addr "PrBSLcEomv7ZJAgBLNNsVXQ5yeaQ8nygJ1v" in xs),big_int_of_string "9670456693147581333170778089578255691883443006071691311865009033645259013238",big_int_of_string "44606178387741809969994612180276322957959315522140297153513786778208278005009",1,true);
         (big_int_of_string "80288031125265559951442759471673073449345250667545012820339278038536518906552",(let (_,xs) = pfgaddrstr_addr "Pr4Jq292oCD4NCkRkvNnKZH21ynQKnwtESh" in xs),big_int_of_string "51269468042363071514007380255963044995739527423967436202239747581806056592115",big_int_of_string "27719819515452577695832997383486686485970598949479879515766319127054881748384",1,true);
         (big_int_of_string "90088644673272028119688760105779043857408051886359391876653940739743353207036",(let (_,xs) = pfgaddrstr_addr "Pr3dGbjMB6eML5g36j9SsVLcxMf2j7urJzs" in xs),big_int_of_string "16138095654532306344815745796599034941275553814161714950071823572637408295304",big_int_of_string "24242924535917199023288562276796408569850738805782724351613400997425507380365",0,true);
         (big_int_of_string "39845812473842281601255097518844340382778288506929376108713691546215585763838",(let (_,xs) = pfgaddrstr_addr "Pr3JW83tYxWtcvR3LWo8v6pAUsztCXKwCpR" in xs),big_int_of_string "45222269623903032718381756965104199524816281956248169148362886602950613591141",big_int_of_string "93982117370188923422141334157564588517514950103616986086305322191202273686570",1,true);
         (big_int_of_string "27777015675180019151037624693582250769588484844970170693199436861637700556457",(let (_,xs) = pfgaddrstr_addr "PrA7uz9juup5kSQpPhjbP485of5T4Eh7M85" in xs),big_int_of_string "9592286525522382719719481226874513735856671860751203959344256808193888153327",big_int_of_string "72389219479435961648180228760610869127681199609658113782358181573664322689777",1,true);
         (big_int_of_string "100844670990773986487328778091706993930743708000907687537446312746104131064443",(let (_,xs) = pfgaddrstr_addr "PrF9xg3A8qvGrM25VBo6D98LudwaHiWJe2r" in xs),big_int_of_string "96130534375569774016719203111982697405791674724240930663193448895694030999688",big_int_of_string "63984328888741821760485536882765460510175261592974962213024830034193288417467",1,true);
         (big_int_of_string "111154288358389218284773886278408848796362881733739679876535494907557100702470",(let (_,xs) = pfgaddrstr_addr "PrGcSvfw4RqAC5XtPHVq8XB8Xyq4G8fvPea" in xs),big_int_of_string "101223864450807864874165322807724639645653447150722674300764042808737297798720",big_int_of_string "38124577099702842127699044925463839494460003241434709966820645628255091705021",1,true);
         (big_int_of_string "78860748323443265346949576364746815914692538478390148470939311314621465140411",(let (_,xs) = pfgaddrstr_addr "Pr9HV4HzDNjMnuGrTGeV6u1vDUYpnLGhkH4" in xs),big_int_of_string "45757137142877342810470236607290521052630410163373950946491353478142975324715",big_int_of_string "55139669301136911952229775317660990905319312550637950228290931000840764642520",0,true);
         (big_int_of_string "107712722065791868857271687560992354685335909221658474825285905314674392899589",(let (_,xs) = pfgaddrstr_addr "PrL8XB8J3QM6mPPCCunohZhQzbNNhTnzWrC" in xs),big_int_of_string "11954200906626817772819501038350416702778306143340425099228596917242984896307",big_int_of_string "19554473218209389716553723363299042410519014406442810757317254801511047388892",1,true);
         (big_int_of_string "66598920420827900475312328301539843988535337243251114460092966019234327201012",(let (_,xs) = pfgaddrstr_addr "Pr8QPLeSMVMUMNT2WPkvEUDhuEcsbdizF2U" in xs),big_int_of_string "37054109482881820142702384587972676318814572191866973453613637930095281004385",big_int_of_string "23983052636437279892860140149154899517417738356871937607832989782823898387589",0,true);
         (big_int_of_string "23277368738462871157834335227682591559379918807575349469656992061174596265186",(let (_,xs) = pfgaddrstr_addr "PrG4ubRfJ7k14Ce1hpqTRDW6QQz2NiDBpVg" in xs),big_int_of_string "26856151228850430081811945400569203415580010402511825393639695017569529627045",big_int_of_string "9520216424590398126020178862609762997954585915785502987802662432306148780408",0,true);
         (big_int_of_string "14227363468708984142682652361311849814554839581458758776387265370715327407231",(let (_,xs) = pfgaddrstr_addr "PrFb9Nn6RMYcaPRKm19Lzf8s5X8mrhn4oYL" in xs),big_int_of_string "80755096442553696452370134234793205234904091532560722680374701361809619283930",big_int_of_string "82664057072235835031498248896104848241896328450878638547584161511789305764414",1,true);
         (big_int_of_string "115471543621348736072422318859324074266209622100521178381052667363676468986957",(let (_,xs) = pfgaddrstr_addr "PrQunXhm8jeWHZ8nnaZRKikWrBQUZNvTDMh" in xs),big_int_of_string "57678990041449734127649869897071812408220384466603086579157703175154126351081",big_int_of_string "49807772883760125861834709504923641973672014229582043391615115790612569136320",0,true);
         (big_int_of_string "1232861947888897664827386365924035295160430840776588529757125071670032116976",(let (_,xs) = pfgaddrstr_addr "PrFs3ziA9G92prcHRFekaKRELpQxsJYTR84" in xs),big_int_of_string "82442139076767068929444800455518129182190378364535286795377079426606152484933",big_int_of_string "2990114711323142043887563033244565088281376115576179474604916558340309482636",0,true);
         (big_int_of_string "13301672953332572406465548567305706219704043441618466173637563246076642892378",(let (_,xs) = pfgaddrstr_addr "PrGcAwxjTy8KCeBWY7XuYJkxTmhekiyV2nT" in xs),big_int_of_string "86033330404162981586394918632620779983998380784766338014755112858682058984490",big_int_of_string "86576446926999611612341392217658397230571020179835167247799890695571851624105",1,true);
         (big_int_of_string "96446257022886914043882289909828924653750713621596997926728166181295734788427",(let (_,xs) = pfgaddrstr_addr "PrQQrXjDQpCqAYAeyaLrPkMK2zadNUB5zb4" in xs),big_int_of_string "84872077241555613190388846662557707008506220464878612225587693110363827908491",big_int_of_string "17528460690641083798200838243219936843605837386540494482042167975081100623841",1,true);
         (big_int_of_string "93233416210616593823899558987781826353383476451041750316401931136886493776028",(let (_,xs) = pfgaddrstr_addr "PrK3GzL9NZew1K5BjJkQ7kAev7z7etssge5" in xs),big_int_of_string "71708818405771386870457309227848055421277746403044836162177924995636230439457",big_int_of_string "108960176979398470514547849629017942192642164752894489867619203857956534669031",0,true);
         (big_int_of_string "53256789083467068878437355869973734252422320993298908134946157824473011624190",(let (_,xs) = pfgaddrstr_addr "PrNE4hbXXncbbRqfyKMMz6cYertF4yjzFCx" in xs),big_int_of_string "55303203945536548274835052463411557080482436761045290423389794076220350858149",big_int_of_string "111295539391692111406143144184865748945626176672815330442384919422466239237756",0,true);
         (big_int_of_string "62875150383336695785756555443824656041699041653306119668500912644886136234784",(let (_,xs) = pfgaddrstr_addr "Pr8FhK7HRLLnckr7tMwu3RJTPzFw7w6wDDo" in xs),big_int_of_string "67108663521492936880874114642301055578815334671354211601221532018799187986202",big_int_of_string "67168339873144884543188477978843993812243945870050037245846307871995857717112",0,true);
         (big_int_of_string "91961272709592626606807645758135234945168946721559528805925166712778086772826",(let (_,xs) = pfgaddrstr_addr "Pr62f2RwVx9ANZw4WgPm21iGQK2EzDh142Q" in xs),big_int_of_string "98598297291358291381561028219002750286128544988357614594439721952322355805",big_int_of_string "24114509998416197245014939298121723596900234178625631128786545853295011068501",0,true);
         (big_int_of_string "102656054925282222791533512399762453284957493396429738869062347973500126793075",(let (_,xs) = pfgaddrstr_addr "PrNbwAxScnBf9wkXA9LSNa97H95o7S8UG3e" in xs),big_int_of_string "52536276186063363498261756816000172256079155107863171291114022741300668066991",big_int_of_string "68980874583931658207778078557559424830205614022232233291601280851951699718376",1,true);
         (big_int_of_string "19450828471977066795911497076148037123300094806041618689514205952579223523170",(let (_,xs) = pfgaddrstr_addr "PrFjGqaqNrxKVanPWVtNeRycm36ywnwdtJ7" in xs),big_int_of_string "94756982607927099812087702572419479823327974893385287878763831542213267514420",big_int_of_string "49494036352207813157186964058551525058047462662670460335389235590423844788300",1,true);
         (big_int_of_string "49318251321826600933430288517275573797035551773355889441207314330754167510140",(let (_,xs) = pfgaddrstr_addr "PrD4qpopEXMdrPew56HqZu4CHgou6xkmkeg" in xs),big_int_of_string "7670463600665281914275493608640062763879503789338384589995592515907770863705",big_int_of_string "31055428320745798742234954534557241010641855761670172907077459566239979740854",1,true);
         (big_int_of_string "60244421114850431880696066399460607636620722572397434951741339954311698438779",(let (_,xs) = pfgaddrstr_addr "Pr5BFWZo9W1MYZbiwz92Yg4KpzMhUupNnZe" in xs),big_int_of_string "67352212498481022996801415819617953683185637123692908110832502934432236737420",big_int_of_string "374453795961198568942618250109247443764569632421868123189482123130092330670",0,true);
         (big_int_of_string "98174185454887152131468325325158932041705829699756560350232239856608794487269",(let (_,xs) = pfgaddrstr_addr "PrEeXDNTLyGTPtvKh9nDot7yNAqZb19kuyn" in xs),big_int_of_string "14293467136254537198634330373871897800657274837928926146816837344599660053010",big_int_of_string "113507745850686807444272409148933596429554789878864034265941129094563699137547",1,true);
         (big_int_of_string "27174199074699805762778138131641502017777575941304142227386672506278122778686",(let (_,xs) = pfgaddrstr_addr "PrLxPZFRsyruhA6uCDQHWo2ktsWZM4UinVg" in xs),big_int_of_string "41559711518396378768159669953376094077692746057242578337629973583798976042449",big_int_of_string "44758568735281130769162690653309709389658110615917385432889374747738903916738",0,true);
         (big_int_of_string "87679571525768900269942986326036134806057466728182417413491468650474773760640",(let (_,xs) = pfgaddrstr_addr "PrEeLrXAUxtsnD2YyLmpnaGEUW5Xg2KC522" in xs),big_int_of_string "114241229921883756215703023400234119740830382797317943207358672836254435062015",big_int_of_string "64259639009925176391427807875949014501568567706132702479105151863031991618999",1,true);
         (big_int_of_string "22134817824536066882548345392427709313624214756951212570310068484318117415811",(let (_,xs) = pfgaddrstr_addr "Pr5NUwEaz4yfouhL5ASGZ6p3z2VxbBS5PUF" in xs),big_int_of_string "21521940548288497515725285133702154689300966689408452540874483892035071622574",big_int_of_string "109969004070810233732927061478850669281594211693179660905259475588445990854183",1,true);
         (big_int_of_string "103660011245543913437761687617396120739653784320800871191812690811187230179195",(let (_,xs) = pfgaddrstr_addr "PrMnnVF75wu8extdM5R9PYZQwrTVahJNA64" in xs),big_int_of_string "33964479606632767824099415717440511844273113732803719045051923676481879627533",big_int_of_string "17185866626976921727943006143735831553270935512476647604022855046622858082293",1,true);
         (big_int_of_string "8930486151494797991331120835827874181012697641441679439988958138375599115629",(let (_,xs) = pfgaddrstr_addr "PrHaxseN1c5dZ44mGc4uVrWVwgPAmncCn1i" in xs),big_int_of_string "41538860420818325041042317216769457007406034081374449921975674685803106493221",big_int_of_string "113213456886372755643594597998282989839044899884056222259288379311827617386744",1,true);
         (big_int_of_string "74019617122999306812548133126875881047756739943764436067788583192308882854941",(let (_,xs) = pfgaddrstr_addr "Pr8or9Q51vnpZuEoCxyBcMuGZQ77WeLnbLS" in xs),big_int_of_string "1362145639955228753792482649462628352583000988429166927802543566378692135720",big_int_of_string "91943528795196090956222962139009632687415179856008306718075954116662241538751",0,true);
         (big_int_of_string "68480540865412878154476587309638749353602759214837347692416889437385387721517",(let (_,xs) = pfgaddrstr_addr "PrC4rc8yzbmKBKEc2Cyxr5oLj5w7cDJAmAZ" in xs),big_int_of_string "72066217850231607216441311591479833763175103555523965335944309999274994252679",big_int_of_string "46628820501392518244930974809574473875382055652108313838021277022053082074343",0,true);
         (big_int_of_string "80489550722065770607396601037132146145271736413632272058946644388939906274573",(let (_,xs) = pfgaddrstr_addr "PrJw5hDZFUip6VQxvYLbhPNS9DPagjUMjne" in xs),big_int_of_string "44082036919257560889459230704262498032355239266590088221983661605831888983856",big_int_of_string "61724321405009485727899320937155666096063047181703626200586726475940877439257",1,true);
         (big_int_of_string "59658641037374471484232601989616208846085310095424504986615038170074071689546",(let (_,xs) = pfgaddrstr_addr "Pr3hEP5pcz3C6CoggyTBqnFV3taBxB7fDPf" in xs),big_int_of_string "31040587946118954561074145621300398731276598089517640089729709885260291853888",big_int_of_string "115599120742295977324059205302284231655308648772798433023421766585928864030018",0,true);
         (big_int_of_string "11293108220440343316701959854007505419415573323037567656060741017767185759770",(let (_,xs) = pfgaddrstr_addr "PrQygviYS5q985y7UeUZdaWafEVPdt9nUA2" in xs),big_int_of_string "18219815234292116677704621100932174855106997413748458412596184942917677583224",big_int_of_string "76385579763893157646634788026302868836922809562407885064957766072271650346135",1,true);
         (big_int_of_string "38715717934942082513159957762925433309601560961465608875023814809688016450694",(let (_,xs) = pfgaddrstr_addr "PrLWrxFW35nhYsPnSvNJUUsabHo6NSvXKMT" in xs),big_int_of_string "40962017979894252920883019731959026990461876193622451641958315906925375047975",big_int_of_string "4609247310766840524402128054426404539536426288331467125907427859351300629633",0,true);
         (big_int_of_string "81402051991482897408853163972553340416352448109377897302059156057100086636879",(let (_,xs) = pfgaddrstr_addr "Pr6AYA8DG4GuLH6bAt2GzRSXS3d2nvtvFr1" in xs),big_int_of_string "31085740972987776511956066819240841734298034336966275613607173130816803362148",big_int_of_string "74660213479202582073933212328142488083809205411732610420122960656510996491995",1,true);
         (big_int_of_string "50996902978633178451894287686859512450102108034622765107177782283988573137314",(let (_,xs) = pfgaddrstr_addr "PrK8HsGYo7LsPuYk6wGKqDL9N1FP9xTb3K4" in xs),big_int_of_string "16844509056701323717850592266419551335202625066836166176029749879617650925082",big_int_of_string "73040252998240529650663197137428550992331043773030167454633028718777764991481",0,true);
         (big_int_of_string "7120863795975844403434777698545754580422079057286731194560085802477471918399",(let (_,xs) = pfgaddrstr_addr "Pr3rWdpMEeQzm8TxtJ3kZa8MkYEQYVC23LA" in xs),big_int_of_string "16309914796078580760194395439019842964083093037399367804583742797689648922503",big_int_of_string "77129738837017095284773680717899831609397954343568032945402955886602610741343",0,true);
         (big_int_of_string "34704529868551197179993803823221577887227756041284126715530532410346884080242",(let (_,xs) = pfgaddrstr_addr "PrHu2SF6BrNX7XwLVEFaTWXXScq9rsCjDJP" in xs),big_int_of_string "57441167210199461406849907085743191848178607331110491217929275005606286886091",big_int_of_string "37306738671080007588231153092343679620313194971300265927797860683937027521107",1,true);
         (big_int_of_string "88021788977347591196067148344884872231628824849496100537374510552923048030617",(let (_,xs) = pfgaddrstr_addr "PrGvp4gXbYfjgpJb1VKpxvhAi3oQULM3Quq" in xs),big_int_of_string "86358465369127862024082218180947764269734460977241080547835931102117067239093",big_int_of_string "40443927896914602343205241914082509054466254232389593340414873516667399914078",1,true);
         (big_int_of_string "96504714580269712857903040099568765234745779776924553401327469935064202568934",(let (_,xs) = pfgaddrstr_addr "PrAUdsp5xAafD3xCFxS7RwbjQrMxsRmTcui" in xs),big_int_of_string "23508229065656826426780403703170232637039839122519751293834934807815642228185",big_int_of_string "24660917212079882714068985084774051046438570843554576790061150495219633571350",1,true);
         (big_int_of_string "19846398329659761271129588676468568134906819686391710801965027579051679883076",(let (_,xs) = pfgaddrstr_addr "PrFUkdDxVX5sFS3pe7Xbwm3pbcgSNjhHwTB" in xs),big_int_of_string "43709871984058000541870336557395286106235063799026979236831929675236817604947",big_int_of_string "47134595408563597377312838804581248838171091645680222987864287493481286503166",1,true);
         (big_int_of_string "113978615747138526616010626753112241395273051654092508909349636633866412121404",(let (_,xs) = pfgaddrstr_addr "Pr59kMQgNbjfMbD9rp7VS4e2gPFVqS5N8xV" in xs),big_int_of_string "60534684590053497037053037202170050944573419654357897298601883116878385868594",big_int_of_string "115703595755122252046779271867015896623291297106002758672964315991201421922538",0,true);
         (big_int_of_string "80046840259570654937567439644256026445275185548979029485337560608876050732819",(let (_,xs) = pfgaddrstr_addr "PrNRcrB7CKPb7hN3muWHCXckKXS9Vtw3mxy" in xs),big_int_of_string "67077864439472591665704723203416171300925439125214665853280921732249278368913",big_int_of_string "6547116979619460007125916970776718738219443609958466456953013396905897637733",0,true);
         (big_int_of_string "55682335636696745172758601973177518548114504164179723476064200509153169496839",(let (_,xs) = pfgaddrstr_addr "Pr598noaiMfX9KCK1Lkao8n8fgDjD4gCUFR" in xs),big_int_of_string "12252136990924717079795707184932305058797580250576507378365105927517728839458",big_int_of_string "45345135465665281059866403032748265401553068533444496504921837475403736020100",0,true);
         (big_int_of_string "101920801604405350568995754111855805165680093388238474694556947053599907276794",(let (_,xs) = pfgaddrstr_addr "Pr3ZnZi6N9A9Kqmi9KvXmXP67kui9fj5bVh" in xs),big_int_of_string "83753628458989626634768809133172592851107132111070671506663118804567139628496",big_int_of_string "110579274051030236567901333327609501399808595104542461526003962419654406295010",0,true);
         (big_int_of_string "103976802284122498773103914174637800444908314222119994469869947439232367163980",(let (_,xs) = pfgaddrstr_addr "PrHSu7xZFAjuBLvjaCvXTKzVE8BgNtfigVN" in xs),big_int_of_string "19142503073745869706037132618653638389170601393980348240685661216745967301408",big_int_of_string "32525902036069276518866436334294985934406674631054605718188724108585674084255",0,true);
         (big_int_of_string "37000618664459874254617445278487670086602362701794768468929664255692737626042",(let (_,xs) = pfgaddrstr_addr "PrG3DJZhvZTBh9pmHpHbudeM5hMfGG7VNx8" in xs),big_int_of_string "38410937897845718223126603353450247237399651510391047264519420212022458353395",big_int_of_string "10953126663449046155857543499770793942803544862706616396282923124598084235325",1,true);
         (big_int_of_string "94450874797799336083498224439189933744372195062942195612851767412170323965858",(let (_,xs) = pfgaddrstr_addr "Pr6ns16zHebMpueb8CCKjYyVJzfawT96NSK" in xs),big_int_of_string "26200376296222982187099368732407447810646750387795601077862649863578040906626",big_int_of_string "79190847441287217270501842515199223172902185099971750979081421095007637501019",1,true);
         (big_int_of_string "25665731755821061851369547647496018866661465370395069573642162693931032639672",(let (_,xs) = pfgaddrstr_addr "PrSBiqHx6CntgAJqvHqWKbVJb2iwoBbMz8h" in xs),big_int_of_string "1115072826324093397561075829678202262580706774045129009385155259898940175562",big_int_of_string "52888258345595553982761353930314702226714602739139315695820946687760147391817",1,true);
         (big_int_of_string "101333847778555976522506207615016779870301302227851967580166336979337505152060",(let (_,xs) = pfgaddrstr_addr "PrPTfv5X1DYbfn6iaMaJ4UrddZvxsczLhBC" in xs),big_int_of_string "49031438882275217843728990624318109843214066958798524321201793959897322534378",big_int_of_string "50186366354954703169482624165685475598334830957100752867724007503355199781887",1,true);
         (big_int_of_string "112638983036401785321254246132810554671109777487102043949142933971521757264808",(let (_,xs) = pfgaddrstr_addr "Pr3vVcGECwkrWy6GEQh7F9SsHCRukYoKz2v" in xs),big_int_of_string "1512499776022892546077584481360649066499698227879442208989216023483374623652",big_int_of_string "1014842731648866495918958851523328361596484053841701498501476773603189107096",0,true);
         (big_int_of_string "104450668821226735499963961180155590546993296360172940417012714206209228406466",(let (_,xs) = pfgaddrstr_addr "Pr9hx2zD8DGDKUPH2LLBSSTReCtV8arLETa" in xs),big_int_of_string "32528032258750370745720947246250022812256035967274906101043493231041500911174",big_int_of_string "70946737032701019187803322089144047485566772295978883396739457045372223176990",1,true);
         (big_int_of_string "70613732518800341924150993712210005230981274074122295390357898955964899311037",(let (_,xs) = pfgaddrstr_addr "PrNKc9RVKKsp71yDHqm3TqH917n65vUaEdx" in xs),big_int_of_string "15245069827406991435831946382264852432089241802802073388990904794811389319069",big_int_of_string "46999729442319391168944283206804870499230598614736210121778632988312242553431",1,true);
         (big_int_of_string "95444252675809312201349547130091825307902147612076529767229392341143354843459",(let (_,xs) = pfgaddrstr_addr "PrCFEGdVA6vQ9jrDd4bLNp2qogzRh1H39W3" in xs),big_int_of_string "33969483889828793386933634966250366514206312528837773765748577671206154104622",big_int_of_string "90838116783917647886360423014465301059280650773048522338897408048196663045053",1,true);
         (big_int_of_string "54598436930119580506537494550299570311891201622370964799415822611572432367136",(let (_,xs) = pfgaddrstr_addr "Pr551cqjYwQKoQs59LrQR128S6T987xw9Xh" in xs),big_int_of_string "110054226272117261980129881853744519952594251835122699866601065578897304258449",big_int_of_string "39058557727641232812489075536789243843109096941486084279945214513706037542133",1,true);
         (big_int_of_string "71947774867562390249137729399276337372200716300458234821162668560841644629721",(let (_,xs) = pfgaddrstr_addr "PrQpLGYc1baZxQsd5mUK4BLSkVAswkvtRrR" in xs),big_int_of_string "37677870080708694549029678079114828183727877213246404819595160774773775119881",big_int_of_string "99123236118937669042925415125966509139743677946517705336533224591571009234207",0,true);
         (big_int_of_string "8791857512645669574851298250829856671648342598121958074221441060039551820692",(let (_,xs) = pfgaddrstr_addr "PrGerhLKeLH1N8G5HDHsWSEFeWRgAgrH2qz" in xs),big_int_of_string "112796775462723931811241814235505549177955033262792127221136321989346612836921",big_int_of_string "85390297827397741482546708867993396028220327099237174025368871414664241748607",1,true);
         (big_int_of_string "48524146000738690018429672000038384521006290814738178623899471171355941058915",(let (_,xs) = pfgaddrstr_addr "Pr4icqceb5QVCPbuNnegoGxFxf5sHfYokc4" in xs),big_int_of_string "28430511991097039386278797080834616229954002201959342559032413128870820269570",big_int_of_string "98741028674157148877906884521095344613495917523465187877952957165024587102240",1,true);
         (big_int_of_string "3381137031761852778841693946691136128671860991866578397044541325222238264478",(let (_,xs) = pfgaddrstr_addr "PrP8QPZsJQm2jDz14fE5UudfjvAhS47QvJ2" in xs),big_int_of_string "57079416351656902882914579888938110638732649719318020990167899582826034468379",big_int_of_string "56660257354536819751251638970644847668282353854526046133455505364789524017628",1,true);
         (big_int_of_string "51148517193806844213904466773092838655846202488857153862094554782776678511574",(let (_,xs) = pfgaddrstr_addr "Pr5X97BsDMegqyExGhCB2MRSqahJfGg1y45" in xs),big_int_of_string "107076486286525551010494264388496877756932054580104904416205864365185657872936",big_int_of_string "48423932642138678039428484703924037047410902192715040101756400172010199536627",0,true);
         (big_int_of_string "107041060551885377455085375531148412679007082845766894143002967109049961683947",(let (_,xs) = pfgaddrstr_addr "PrE4anhdrsVEqAP47sBnHC1S9Qf2PnfLrWS" in xs),big_int_of_string "28960836008544882438014909881298229815126362686453664961616097174750408871475",big_int_of_string "76399351198227968706633940768410026637887275892074714487097627003092435072940",1,true);
         (big_int_of_string "388018705890952440179283100338571622287012034851944124181558223502728880182",(let (_,xs) = pfgaddrstr_addr "PrCKPrevibZaGNmM8NWwgV32BTvouDK5XZ6" in xs),big_int_of_string "81285954180947045030587010987457731604506672895860026319292344038652610005755",big_int_of_string "42578887714520375367598798311424949495838158533012956734106230460178872607477",0,true);
         (big_int_of_string "77973082445520174156648773918979970199445829926755266601982220494054066578755",(let (_,xs) = pfgaddrstr_addr "PrBqTaHY35UJRG1LpjPMDEEWD8cS7xJK71k" in xs),big_int_of_string "90358046622053885187652149303343884533135065572181268128814127736813469284161",big_int_of_string "35179559078431657175924567607541028435864150489397932251316786382644638425629",0,true);
         (big_int_of_string "105520560008651350708415599775456956430291437745660157939092872238504128266887",(let (_,xs) = pfgaddrstr_addr "Pr4oqVBjutXERPDALcMgFSrZ665Mezenbdc" in xs),big_int_of_string "52340646818606546445554387823252153515028258916337678814456803040431217911898",big_int_of_string "109055814066026093306229989674984889510731332928235252295660778519771402672359",1,true);
         (big_int_of_string "96226808835995171089519481586577859715540388825329642729344193577408230501934",(let (_,xs) = pfgaddrstr_addr "Pr9hV6t4d2DUqLzRxTqmuPSNb9DVDhTYPWJ" in xs),big_int_of_string "44782597377347232381982333603489917395466966558612867698053250901700592963727",big_int_of_string "83175843167777138578671026641696858697603433426188375933513522515869755918202",1,true);
         (big_int_of_string "82332501461159824686279002012116912862819526353345331441145652860080833344145",(let (_,xs) = pfgaddrstr_addr "PrAPn5TRpwUZPmBbRwokQGWzseWXyteCvUJ" in xs),big_int_of_string "109537990708466991069815533494202519846443851554318382028581231592258603434546",big_int_of_string "74120552991756472415424370696987371915090113560354986215738631623900682326900",1,true);
         (big_int_of_string "47597284094075243624315420224211488791564846268646130950717831771659132476250",(let (_,xs) = pfgaddrstr_addr "Pr9TmDy5KwtRHrKo1tEcF7qsujTUnA2q83n" in xs),big_int_of_string "3718590363664140431487654831072092879916551791441222291441015774316505991487",big_int_of_string "301632265814209843701660068200865527807636752992842539085851523561297937488",1,true);
         (big_int_of_string "64589781269445453549711791797491905981805040845861915034677739645379012373535",(let (_,xs) = pfgaddrstr_addr "PrS4vuuDep1qvjABUi5nr44e6FrEkpAdzcm" in xs),big_int_of_string "78420308625597634531476130965781667775075452678196609209803292592410441887045",big_int_of_string "657697221985469528474145018976866816698614301275946613301898845583728271531",1,true);
         (big_int_of_string "66915984143266641909647876883311466064083499964827338708462740111192341646806",(let (_,xs) = pfgaddrstr_addr "PrPzDdDCvJGPY1scKZG7iYM5PRqsBAmHeRj" in xs),big_int_of_string "110270121194897528131576232651316289763110039878202965571170959444920156553067",big_int_of_string "94469327327172650379361691844250693981622062260626839942620068956514774301178",0,true);
         (big_int_of_string "80857452930411372667884658082231184762693922104338239492505682547747377679067",(let (_,xs) = pfgaddrstr_addr "PrLd3Rtq4XatFvNNSc9D1QvoRtL8qjb9WqY" in xs),big_int_of_string "1152178552252974374936983681836780536914885574522751918963773672698956745304",big_int_of_string "21851382809669211165823519129771006297189735661242405636227917998027331122538",0,true);
         (big_int_of_string "90215631659275979834455043585514760765344478177569112367937353161713549069576",(let (_,xs) = pfgaddrstr_addr "PrEjRuSM2zSsR3SJXtxhU8WKZohmQegwjHv" in xs),big_int_of_string "53499470453142646291400694687011969377748373506417110174963113001235735269116",big_int_of_string "74983663633627566215872488914089597688094358761849060127459865233495390396114",0,true);
         (big_int_of_string "108728316338827849608093739284098154275653617990717434428874698605399969040956",(let (_,xs) = pfgaddrstr_addr "PrKS89s39McYrFX2Ztaew9ogqGd4MBhCYYG" in xs),big_int_of_string "64672364452000739384242883906136283801734932644794925419440666477913598625128",big_int_of_string "1938709799123777491752708256518299523945626567569716974714738032913421628998",0,true);
         (big_int_of_string "75849924127921873177132634648858717686220685635677064703456385214845709916630",(let (_,xs) = pfgaddrstr_addr "Pr5xPAXGJkEpr5FHR7cQYy2RWbVCBj49QHM" in xs),big_int_of_string "1361036979135089682878540623066136205201452339812069120426313251997418371774",big_int_of_string "87329377830167942502146472703603222510815257230607616534532852307978431221880",1,true);
         (big_int_of_string "44147679851104604806664179168669081272007504301817222411668066150000210456756",(let (_,xs) = pfgaddrstr_addr "PrHPiRf273idrikD2p5L9kc3HJcJZPinJpn" in xs),big_int_of_string "44013528707482217213313917281637367311991172888815960878355850570906798276131",big_int_of_string "93239873814621667257381649148781164276879801977148944204621388281246554947688",1,true);
         (big_int_of_string "48576693782862178854978228002875256310153021502804844002334670360217404413434",(let (_,xs) = pfgaddrstr_addr "PrP7gNuRnMsEL2MpGK3VvxbQpVLZXpyjHLj" in xs),big_int_of_string "57986385085398882592346518693689351774531530504544148621862103544861118549579",big_int_of_string "19624011656694386896793546304321436097551103241960152098654544871794260511862",0,true);
         (big_int_of_string "45199344302963963826930970933504355347315726010943978111660099825569528526365",(let (_,xs) = pfgaddrstr_addr "PrCLSoQExb2tk7seQocV7RNafHC6RQReAGD" in xs),big_int_of_string "66341549797373155365334086784290082284820409835124897281392873730893291119602",big_int_of_string "108776470089272693824386191878174701351640912415910238378715639958162064690114",1,true);
         (big_int_of_string "80313543153507750161437565148646499599735186718248814765351655231726592832709",(let (_,xs) = pfgaddrstr_addr "PrNqQd8GLTwg2TGKZ8UyRGUhpycLGr9y6wy" in xs),big_int_of_string "21267546143887812105372930864077103458879306364163707008465083827899880307573",big_int_of_string "54266331028421495849468518528384590756885334579473756415632385693808973694346",1,true);
         (big_int_of_string "20921142294645923602772353092154551345960536134148623083685599390523435012205",(let (_,xs) = pfgaddrstr_addr "PrC7SV6KXFgUEhw7jD4rkAXLE4LnPVkheE1" in xs),big_int_of_string "42547804186408590743117773008827876845993187438381603733596322107487180084129",big_int_of_string "67786062396210008629320295494271475865297503657405836021845612090171486016960",1,true);
         (big_int_of_string "45534775777770665365865759571376927664985758024174634095340905056120531759049",(let (_,xs) = pfgaddrstr_addr "PrKTxSFPkFiEqEZdGheWQr5hSxUUPSFSuNo" in xs),big_int_of_string "31314423601512377419574384744968285646644203538188184741937813258068798514938",big_int_of_string "105619280909460872183808759823633788025222649173690203730218779378413875514583",1,true);
         (big_int_of_string "35442669566057827431848544789244000508539176500871172065642356286407930652644",(let (_,xs) = pfgaddrstr_addr "PrRt5i9AYjEh2H8ugbD2L9ZoaEwZvmMxAhX" in xs),big_int_of_string "86635589936310071519519786500198633375790037904045932913999290566293902052115",big_int_of_string "41442874562461578169999065150355084797224224064338370781504374992691768127399",0,true);
         (big_int_of_string "71233418161689085304957906379991873258014042502966503033728832912400615532300",(let (_,xs) = pfgaddrstr_addr "PrNRuJccLVNAAntYkN8jk7wEwbJ2gNZNsex" in xs),big_int_of_string "106535012540455459495413849183845761498318763875856007762097982885933544101582",big_int_of_string "99898650655770828781501755853428291323690499274433627027535570337865539277031",1,true);
         (big_int_of_string "57724971824877546148389667618293002021925272190504287684075422899309439659081",(let (_,xs) = pfgaddrstr_addr "Pr3PhhYmKzpLixGRX4idbG4pGqXtLT8F9TY" in xs),big_int_of_string "46455363899608102273488971493292154437996067988514641149481672456005704051004",big_int_of_string "88901155721646738277277588003213216722312603984568781329879444175786846860077",0,true);
         (big_int_of_string "67887868384647846885099220968321080588413917570641247951235098286459027421347",(let (_,xs) = pfgaddrstr_addr "Pr8cDNzETcih9yMJsDgAPxiHvtwpjSH1Tpr" in xs),big_int_of_string "10277481493238139282185458018936151588058995493159084653339301548596625688545",big_int_of_string "21661417994672203354615647856999220784777702516357822818862200146648712012281",0,true);
         (big_int_of_string "44378835364282337893256286927135537278287356229205744890011896992994889146251",(let (_,xs) = pfgaddrstr_addr "PrMCwZAJd9UCnkJuAZpzFmHkwwyhfgEKcfE" in xs),big_int_of_string "32928956993120124100532925425351987579406651560952770912639563132898245861553",big_int_of_string "112197014155267789143189670903092110668739455059014660234184874781806365483199",1,true);
         (big_int_of_string "33453490626019157750361077530208687953677849248739978089646387682122785313324",(let (_,xs) = pfgaddrstr_addr "PrE7nt8omuz2yTBErbQ26H5xE9Lkkuwdf3M" in xs),big_int_of_string "14768003355648993938082748916007353971558825091128986086262682146675966675641",big_int_of_string "53869223781418323962519322244330067853101677972266122538780092731159052755428",0,true);
         (big_int_of_string "1073363383513171537255851131969498090912942794344225844950919721588762056635",(let (_,xs) = pfgaddrstr_addr "PrQ2tWPrWoxpnBcchEYtWZ19nYVsh1gvjkm" in xs),big_int_of_string "7828061219092455513952686920976797168023060810714995420021624195713057424714",big_int_of_string "34608898914184529115718409318672633212255407904751224548631547703719829727007",0,true);
         (big_int_of_string "111500813666713474353377667874372396612077878141207195905140419917683456757430",(let (_,xs) = pfgaddrstr_addr "Pr9sZFuitk2D63WiG7MFcyD6Du64xXQyoMg" in xs),big_int_of_string "12748619029715845415144921696428282422426473926777062505645743549184887863266",big_int_of_string "10495163096131917683237923390383599876768779557687242366154192877797423921240",0,true);
         (big_int_of_string "72633602703135705642279123579576656428442020617999615865776284142707664960775",(let (_,xs) = pfgaddrstr_addr "PrKVNssEf3kc8ZRheGE7aCSd4PgY1f7VzMv" in xs),big_int_of_string "98027376642183086297421035469947162699631187093149578765120853627677978451737",big_int_of_string "1665490040352896921006348036773513878144431278160534965331479093137649819400",0,true);
         (big_int_of_string "112546664720990226495706598441619190192831164214885667475142796278818840545117",(let (_,xs) = pfgaddrstr_addr "PrKm2DmVzibVACp5N6hKFBCH45rzWCJg6uW" in xs),big_int_of_string "84853883203069539757880435816430307057200431528502012537819798795188611141788",big_int_of_string "34602740248995073505506138880684266283324664973633660956128821366745138986365",1,true);
         (big_int_of_string "107448696570815093819463377243555255989358926690988778980879122140494998139206",(let (_,xs) = pfgaddrstr_addr "Pr38XKYSRaXsbLM48ZAjkzYcKbHCzyNjBTQ" in xs),big_int_of_string "19871991040461745917430707149356867567189975509290069322956237924516892802156",big_int_of_string "28907912843897412181068928320956788313829305415980606225326630170414050657132",0,true);
         (big_int_of_string "234293686352047821333498076135324776536557107593593089741469539898079532952",(let (_,xs) = pfgaddrstr_addr "Pr61aW4kav2s9Ue6dnumjfTqMvzqMBxaKMa" in xs),big_int_of_string "50169020810654920328607863264599480201268951542936255360203227464981031326247",big_int_of_string "100305500984851410777100816340825051365449351776259166015288005263580461606313",0,true);
         (big_int_of_string "104762563873557869714287131927074561909445875677481363862851136275336325025383",(let (_,xs) = pfgaddrstr_addr "PrEgazE6Jauxfd4tfjLseKCnWkNYhag47JY" in xs),big_int_of_string "49966866809575781634896483989511807412745117775957457061271474821890716924250",big_int_of_string "23976162320892113723652079551346981494310985633018379883405439323049253555169",1,true);
         (big_int_of_string "63889605247532558952314062545207323792836402318980094243406325942394114890603",(let (_,xs) = pfgaddrstr_addr "PrEWaN97FWi6ssXaqoJGQKA6X3AQ4DqtyrE" in xs),big_int_of_string "61177010700914711224064475749516457869310534342070283349520652263851188606186",big_int_of_string "90841949546228667229644180115615848770996936536932559847340157873820990806827",0,true);
         (big_int_of_string "43145823154482055856351091851357522602362917733658804821420204356670147204009",(let (_,xs) = pfgaddrstr_addr "PrFiHAnK1NpcChP4djLTcwaAwdGQLpPEWuL" in xs),big_int_of_string "97805464417271174445029581557338270345978283180127478972700900365723575540523",big_int_of_string "107365274632074292698827226162344737750002778077313785317524386121380673681071",0,false);
         (big_int_of_string "13049024139168883021257605102530335359811400255747451103515692823573293142038",(let (_,xs) = pfgaddrstr_addr "PrR2FZn15b5FaY9UeMKyyKD27p5dytNgAYv" in xs),big_int_of_string "7987123465204002720654092953337712335149693295868840037624783683053747900065",big_int_of_string "104548036260048717383616079650606382339754408417629882456274580716406686503892",1,false);
         (big_int_of_string "34019549159701833363314880665541622848672203951692969591324260871020551704865",(let (_,xs) = pfgaddrstr_addr "PrQPdaw2G7KF28grxEPvmvifv5oMfvyrMuE" in xs),big_int_of_string "12282059733779529834858452937397510685369165017809210949394212391343947845593",big_int_of_string "54417347662167682205506340096905669578773307216109450034036229381936764481757",0,true);
         (big_int_of_string "38925095339689623911871385687388223939854591516878326934911884994892170660851",(let (_,xs) = pfgaddrstr_addr "PrMTwB2NTHF9stQ25WJhPzyXmwVzt2Jxi7A" in xs),big_int_of_string "45171201923105304178462164279748340489404192160799087627953491197699395724084",big_int_of_string "37312763687172315297274103214715611297001930488872596690681319150614437481804",0,true);
         (big_int_of_string "28506503488066344691501535541700371772554972958640780778468152904382337201789",(let (_,xs) = pfgaddrstr_addr "PrEX5t64pbZpfUsDNaLjRrQmCEarX4Fq8mR" in xs),big_int_of_string "75807594651150778736856494447560409384422350209511157641010298651298151051768",big_int_of_string "3240644361841632128763331666436065423085710193677274302591536694504313186895",1,true);
         (big_int_of_string "70903611813126525066151568333854177540812063473740554177069544756685098938371",(let (_,xs) = pfgaddrstr_addr "PrNSVzcxF2BT4q8nFtmEgpcnVaWhUV4fYH9" in xs),big_int_of_string "1624121344370880825547076001972962723591348574080876827143659057047089916639",big_int_of_string "8213218070389334554789869320701575616407402272742144045899568126544192933110",1,true);
         (big_int_of_string "34678314551046014743375781634354505722742709540940051952454540674279761352829",(let (_,xs) = pfgaddrstr_addr "PrFvuuhdmH777yL3HP9kdYpxHg5spb2bP2a" in xs),big_int_of_string "100433381714338172434383321868566146304560741154095988895852328537442012280158",big_int_of_string "13240736749921337750202399150666809665103210062914086306418316151854904375343",0,true);
         (big_int_of_string "9211809503454947692016514266670787205790114549435663974164164327177930642367",(let (_,xs) = pfgaddrstr_addr "PrPyaK8KfBzcTC4NXdg7woZbjhrmUuxfTVP" in xs),big_int_of_string "46117974368816886080681399138768790071654205044308023642117904837009104080926",big_int_of_string "115086565031355092575080889647100362668719650992012814817368803367072838878047",1,true);
         (big_int_of_string "76421248598144090693275678320153556516809240216597846643826251972983480429125",(let (_,xs) = pfgaddrstr_addr "PrJx4ohZYCqC55k68v6tGDgyC5cx87toNgX" in xs),big_int_of_string "48711494752172534545050781259490198120995341024765795426422060292577202602917",big_int_of_string "82686403933527956354436303668324707734189876664186018394167498315947862352305",1,true);
         (big_int_of_string "63240451400565266057527785817401691009299397997678591580988527906293492388212",(let (_,xs) = pfgaddrstr_addr "PrHvh3ggNJx3jfigEzCuQQydKEQYAyobZdG" in xs),big_int_of_string "115167018044142081810259953914454908955849180985435827164531008253065955678935",big_int_of_string "55591469347470377107154821609682903851267908901623490406506074337759047893890",1,true);
         (big_int_of_string "84411926952129440415276722259928876424609629136003072007821653768547862452954",(let (_,xs) = pfgaddrstr_addr "Pr7DG3EFjwLnGXkJHo6bE8ZFkV2LFiDsRXL" in xs),big_int_of_string "21782486807010156872913856341299411901622636103970135205211747531593961550779",big_int_of_string "4569102528725094664168305555032979534550035045451299777325766280822863547366",0,true);
         (big_int_of_string "47493739035426115279275681941569732494311053069991392184294653738892673244829",(let (_,xs) = pfgaddrstr_addr "PrD3iSZg2CYSLpTGrQEi6L5RFtCUHz2MHBg" in xs),big_int_of_string "110430986879931663170941495763670045932608140495690610588688570401786625181678",big_int_of_string "107031317472078802889398857068250930104653386564127198514408515254806279137655",1,true);
         (big_int_of_string "30986491677121201308308822348595763474570332842615236380110145124726105912050",(let (_,xs) = pfgaddrstr_addr "Pr69tEKCfEp1P8FL8ESBRxmsEovois7819s" in xs),big_int_of_string "73123765664325895616761308509359242709308589365196962771648356334702899514514",big_int_of_string "112258970891079951979235922489507009273826052189912560196144760231995466791900",1,false);
         (big_int_of_string "43004763827692159388155151071983366063376619286161129211760439058003490941648",(let (_,xs) = pfgaddrstr_addr "Pr52k5uSwaxHgtpnBpxFrZDQf3bqu2RwKTc" in xs),big_int_of_string "3106343232858476959510533499056087329150038237044575832171511170862155287198",big_int_of_string "23514701383516589071385720517741311943233231518015421839154772884419343432735",1,true);
         (big_int_of_string "34032127410952748013332093513142523491473127170305852280572399941004741465325",(let (_,xs) = pfgaddrstr_addr "Pr5S6yaZL75hSVQVqXvsw8TM41Pfuxycg75" in xs),big_int_of_string "114231661144839867990683309966534542724228318214272365365976953290634878557216",big_int_of_string "22113449693707164901233077689559510657937326238147527179958009326229687284942",1,true);
         (big_int_of_string "69493169502594101707927745701304245558143104379960716898519735697988713323435",(let (_,xs) = pfgaddrstr_addr "PrFEZ7rmM4DciXSMWXTic3kt9BVg28c64Ym" in xs),big_int_of_string "114762606174055108966221592754566360642922892181481672033251897063999404269353",big_int_of_string "2275976394005130155089539059049788291689615524898884425900621419384867485507",1,true);
         (big_int_of_string "95746126956682942452358864710346115394861676720095458028484117871630097608757",(let (_,xs) = pfgaddrstr_addr "PrMWWQtgmvGn7NfjexCNtQUXuWMZGEH66nH" in xs),big_int_of_string "30432988030065730411034584722229213273730082988968139365733823716849158049263",big_int_of_string "37868991122779665500941009361771497695260209184554855004870485223726618116218",0,true);
         (big_int_of_string "27330399414261231802366356647731569530733499503008654903904888692674437916972",(let (_,xs) = pfgaddrstr_addr "Pr86bGBXpB5Djg7Pj9jgYHYDkJPAMunjedX" in xs),big_int_of_string "95345066111248657001962978626961580019857788995148563167881164194644926487379",big_int_of_string "105894993559668275999302096457200550118098602038521893590676539980175137681974",0,true);
         (big_int_of_string "43346064141479097998124205913029889813454082166830897566538018312195428706959",(let (_,xs) = pfgaddrstr_addr "PrDFGmpdb1x1C5gzGUAAk1XWDcS77axBcgR" in xs),big_int_of_string "104453436204299181701901831224464291016188277123041585203750915578418199103307",big_int_of_string "101142878943969010606971674384211033933404732921027658311660689442748774151983",1,true);
         (big_int_of_string "13437001066170076227242676507921520706232086319935287152649221489385799726354",(let (_,xs) = pfgaddrstr_addr "Pr3qoE7TW2uadaA5r4esucYNk6LdMSJ6t9S" in xs),big_int_of_string "9988966584838484242855100082504871826379846993362268564076960704751476366347",big_int_of_string "14295261142342623175490313416922694247227203554864314316030339037753248826353",1,true);
         (big_int_of_string "103753713891269174877630455976070642077677714211167021045590757725482475450167",(let (_,xs) = pfgaddrstr_addr "PrBCA6Mhu7itwDortV5fAJRP34FS4WxPMtn" in xs),big_int_of_string "72306501023296417008841409372550949585281575341764863165076775153283824328812",big_int_of_string "64982836477906276736189397295611357771912961119889287593496597226732207222611",0,true);
         (big_int_of_string "86434526932778364982965054725069039880706827167860637294926794433025678473420",(let (_,xs) = pfgaddrstr_addr "PrRWQpKviDop2ncNpEqQGGTRbyQoxMoi3gQ" in xs),big_int_of_string "32370361759229663737424200891666077734101608078278061235466019233866640977904",big_int_of_string "20775351147056446825796319859435129406305410949809114585565110730880441260033",1,true);
         (big_int_of_string "78323865991246649691974199107641208256008771553589347480981458333990918841425",(let (_,xs) = pfgaddrstr_addr "PrNsSoBB9EovvGEj9UmVj52WaReuMzbYYKZ" in xs),big_int_of_string "40473487114144415462967317503635711807543873651386592397085696047041759457147",big_int_of_string "80755078971110007432672245028087219280075963315629931786633216878479988682677",0,true);
         (big_int_of_string "32803450590705323026360215165596998719468398009540753673981494489549777990682",(let (_,xs) = pfgaddrstr_addr "Pr7726bT11VtdFrk6hzkfwkF6ctnVTY335V" in xs),big_int_of_string "71658862921016524751579372307610749948306636198653764294710963725688593516793",big_int_of_string "61658929189167257283005984730997682071816000021130782310788183745100573108517",0,true);
         (big_int_of_string "12293258164536807089429689119244006343540401993529342745364721347616581048666",(let (_,xs) = pfgaddrstr_addr "PrJPhWe7MxMpnBU5P52cy2m8SzvNQe2SVsQ" in xs),big_int_of_string "48408902480096716420564966090522799091862193188714919981830654668376511508337",big_int_of_string "36776268837473650723949299532523000358513062921611210478063323316340309050679",1,true);
         (big_int_of_string "106167759181895144864562289568042409523086298537644711716596573920733951215502",(let (_,xs) = pfgaddrstr_addr "PrH1CJDiwvDb3Ea2MojtRUFFweDmUYm7qtX" in xs),big_int_of_string "37700988926703901658848179574665145443694374043291226886609179499254803408992",big_int_of_string "74340717041337102148793589318483067091957622022615241401552522797922235428529",1,true);
         (big_int_of_string "37555165967291281581003005620282824224882417342064569588884576712436076804357",(let (_,xs) = pfgaddrstr_addr "Pr7uhSVSSCLDJHuYXTA32M8ZutBSr417NWp" in xs),big_int_of_string "93101593251867322710755088750510412939353259802282551697205433457469541040420",big_int_of_string "74944812306402653686305654087125555097029591678173337483530534833135050034096",0,true);
         (big_int_of_string "9116580304645255798883112958692588573558783059337110664200136087188882829457",(let (_,xs) = pfgaddrstr_addr "PrQp3NkWjuDZD8iVt41ibXvPieEuK1Go2cZ" in xs),big_int_of_string "26085399108311084528339798330738102255191120090745440075465648892459690335685",big_int_of_string "62935326362138760567666102711881158896389944919494800917513570617470788339365",0,true);
         (big_int_of_string "396052236172640228132465014463761936488376728418911260732697450385890446387",(let (_,xs) = pfgaddrstr_addr "Pr4VFmJr4KU9J2tZEdyMFf6jhGTB36euv5Z" in xs),big_int_of_string "82344749751687632045753062185238428580957938683060800988859506254086600815182",big_int_of_string "56728687510967971217537050644250253489763640536209477159129117857151321424382",1,true);
         (big_int_of_string "12281000358800696178391409197536387280913366747073168020325290782388343488220",(let (_,xs) = pfgaddrstr_addr "PrJJ5fn5AacJLcJkxNvzveH8C6jbK8UeGrF" in xs),big_int_of_string "878801857405073991201584852863786779995316402244132541386264365650882020448",big_int_of_string "93969996419326063933402320551023068138032061724361739911983487593679621470923",1,true);
         (big_int_of_string "107741728453910986698367450760304554530927939412674577839162375953599787613372",(let (_,xs) = pfgaddrstr_addr "PrBzmJT1kqNhHbkoSSxh3w54t3HxUyd5Ssp" in xs),big_int_of_string "96746215874213693992677324845445165226354034024916602033778775931104501300288",big_int_of_string "55485620425338305876644606938946228545231376344664032940708561661363671624995",0,true);
         (big_int_of_string "58354201602013258174705233803449396227235693282038971204234417063672007926803",(let (_,xs) = pfgaddrstr_addr "Pr57wLwamTLPKAbDKKNiDRjo53hdzpyDH4A" in xs),big_int_of_string "54225255513833114498864939726666782475165640163855288009155828580317665153998",big_int_of_string "79631195513799701546554659770316134459816930010586617764696846746333206750256",0,true);
         (big_int_of_string "67612154314164710098862499248094735082489079350265339886574671411168925661251",(let (_,xs) = pfgaddrstr_addr "PrPqvtdhzgtzEV7mQg8UWDtdt7C2qWrag84" in xs),big_int_of_string "11541426487385184150343778287582291920402229106320880212388803603887352257135",big_int_of_string "90343052554067942840357755778485071992772605519115595341674233314354629202781",0,false);
         (big_int_of_string "91140552303483292088391535858011545477975330087885394246972484282103521292146",(let (_,xs) = pfgaddrstr_addr "PrPB79PkjKdZ5VFTFvMa42o8qDQBhVuaFtz" in xs),big_int_of_string "63303806419556975452571463025121565019258722579294233819966941885938842490970",big_int_of_string "30863187258662377014362099703102037460121093114027729126585196263358948234415",1,true);
         (big_int_of_string "112983002792067311271918144284143869157040136684817801537854179789560020916765",(let (_,xs) = pfgaddrstr_addr "PrNvaHwVEuxxrhQAsUTHMnTjQ9YEuBkFs9W" in xs),big_int_of_string "47543778737230709879975088857554948171907166255517185761249354295750132561326",big_int_of_string "47435701220476758087143715747420225098477494387323410863710632704912526936650",0,false);
         (big_int_of_string "113354092235210589393160275629557251039884860960114572075893862851360180235760",(let (_,xs) = pfgaddrstr_addr "PrQm1QLLnnFECoUATHzp13ug6sknWZh5Uhy" in xs),big_int_of_string "42165126891674463562383435146847140338055602960693952507245077675140132371522",big_int_of_string "99675110581305405847619306306396962924947697199268126442781442162961272968981",0,true);
         (big_int_of_string "91873428633615872490181860693258581899652179399428279445701222966650242399786",(let (_,xs) = pfgaddrstr_addr "PrQpLGYc1baZxQsd5mUK4BLSkVAswkvtRrR" in xs),big_int_of_string "18084598056942132607853357630020375900299564096442031483843648843991982744792",big_int_of_string "29666483979402028998675399967664709333207493027362832818453399817810085555125",0,true);
         (big_int_of_string "102986713923778429946261539712617784311027804875261896619789030397668819692481",(let (_,xs) = pfgaddrstr_addr "Pr3au6aMcPVPobHDkSG6CZVeto2G5kEERd4" in xs),big_int_of_string "108366983432540869296849850591533706316162686847615136408363552219008444845937",big_int_of_string "99199776260263691895292534021821377325940486935731589935232427362445353764004",0,true);
         (big_int_of_string "102070731707263261160123969383579465465537485762088970323941858383291818723563",(let (_,xs) = pfgaddrstr_addr "PrERvuYb9pRA7cVocqhLFigFaGdR6mnMNWi" in xs),big_int_of_string "84643141927349051163458976448982667891191871492512274459484277145809070503381",big_int_of_string "87960284504859509244467067669847010773827916637189398149273680863601149938268",0,false);
         (big_int_of_string "44658504258501174232577328285351853400980323293757025739548781515230217503284",(let (_,xs) = pfgaddrstr_addr "PrFodoELTcE8iLvFQTnvMecsz74ufCkRUFX" in xs),big_int_of_string "67140526465941174301049289743658233902919441952127960493743789821834411128525",big_int_of_string "41106254203050347000201515997724643477497744842525421909209205459630474666167",1,true);
         (big_int_of_string "73677302284335183944783950955387110847182238118558697339574107223918272342541",(let (_,xs) = pfgaddrstr_addr "PrE24bgjKhW7VRWtbjm4eenCTyirFAjj85x" in xs),big_int_of_string "106451288664279452642696202282109423211887391037577117863568942070077021976005",big_int_of_string "71007044708444802801346475864900209770183971798419669186524158634169239856837",0,true);
         (big_int_of_string "31200441463401189188180951571412147587996874654894444478174884831922747929928",(let (_,xs) = pfgaddrstr_addr "PrDR5RPusCX4i9EhUiS3bZaZoo3xFyPxde7" in xs),big_int_of_string "11867765546883345039451034105834572489656360614209710130416834649107923725251",big_int_of_string "105734146966135700709772781437160139627480385329758237032724894026697235895487",0,true);
         (big_int_of_string "111034119228031272937863207530531683982542080810471022678801790513727813656498",(let (_,xs) = pfgaddrstr_addr "PrHSWje45ZzoX6ipBrsepojNnQqovpHfnoM" in xs),big_int_of_string "44185780584192176990420538185910209949718887058855208620119893745748490627774",big_int_of_string "32490623226868920361879169823213877412920035688408087669265570836794939707810",0,true);
         (big_int_of_string "83243537654411473561050778644641064054889976956589435289969639566211215849989",(let (_,xs) = pfgaddrstr_addr "PrGaZGNsQ3HxMpq9QGrPKasJYHSZGg22CuS" in xs),big_int_of_string "51625083260638195847428369270700542534978659033955807197287631268193075103343",big_int_of_string "75138275328908690881641727609184958686896480805974366284431843065860330282008",0,true);
         (big_int_of_string "113908527329447288522577982450287848434573809066139441520468154437414255680383",(let (_,xs) = pfgaddrstr_addr "PrCRvLYumPyfXE3yv3HDyWt6DXb8SqGomWK" in xs),big_int_of_string "103604813351100103728058799167994441406282710249702625098095694183482696728450",big_int_of_string "69451776182496119611961187488601867117161965732028407820683466916967147046566",1,true);
         (big_int_of_string "8192856088020789883509124598761037749584531507388173698621706183105129823714",(let (_,xs) = pfgaddrstr_addr "PrPpykoyQ3e4WGwLkuS52cf4SK1ofkpW6s5" in xs),big_int_of_string "82402881069782330909844847847708185023590475871352284137376769618201078357875",big_int_of_string "100597619247620270646992089937123911390136067305269556959895458445652625605021",1,true);
         (big_int_of_string "107296667379738440507825128329653516604947066644052559365999858953472516054562",(let (_,xs) = pfgaddrstr_addr "PrKaPD8BpYWJzga73UZmfxMSKq2WbprnPfp" in xs),big_int_of_string "13001164118427983636603976380230047802973747812311818679551466850453784117959",big_int_of_string "109959833356696625006837188825596258524081907392028263456040950652842284318251",1,true);
         (big_int_of_string "80151225911156139587646956204471613677261644148561639575729497101823553731442",(let (_,xs) = pfgaddrstr_addr "PrJPEFuwAvieUxbTbqN4B5LkrNszyKHQMwb" in xs),big_int_of_string "59479853249073171403958154859796080527943498712671802657950962733300172707148",big_int_of_string "47639921181133717509691185225603986539411266782997454933933240030006455315239",0,true);
         (big_int_of_string "103213881744068416023260957229870709606867714278213265646188866392743866337023",(let (_,xs) = pfgaddrstr_addr "PrLdMKmcEDXhq3kjJ8hQZS7FafYRzrxedGo" in xs),big_int_of_string "55052667009868424037153142394876864976074588747360558621252587633660736777044",big_int_of_string "102372799798654013611441274351352162350986610657293759924923982192760035283518",0,true);
         (big_int_of_string "27857485221680953627724363919901004887683403298112096460497984913899431297149",(let (_,xs) = pfgaddrstr_addr "PrQ2d3UZPgUhZGgNbqLAU9ckyvdBTu7sA4k" in xs),big_int_of_string "109661744443409844588726138919798615299536215852130978660099133540195883686789",big_int_of_string "63564799780534932649759179511148114500731973016239099627559809092624308433915",1,true);
         (big_int_of_string "103806929205737849888062564311214075671896068835588064574522546552318860812520",(let (_,xs) = pfgaddrstr_addr "PrRE3yNSAbzUkzbVN6Be2KkBRqbzEwfGM2z" in xs),big_int_of_string "43891670784683039255895792916092978974716491725037155077119721958858519950752",big_int_of_string "66023280207408871970426645212589384823728326840143979237265643839204172875669",0,true);
         (big_int_of_string "106805794338937405282193841785203044285562157654087827337734944248887439269776",(let (_,xs) = pfgaddrstr_addr "PrLTyp8qkDYCEc3rMv3UrcXwufG5GaVhHvF" in xs),big_int_of_string "49803359161269042384363151316358784431004713754846155919409826910779227817851",big_int_of_string "40516675551047890394616290723817706637618302969245343791355252512790525925783",0,true);
         (big_int_of_string "56998709692248886646701585086793862963863628543324189985202140527772888629392",(let (_,xs) = pfgaddrstr_addr "Pr7GnzdhbdTA4rXRpvMj9tFsc6vaxV3eafw" in xs),big_int_of_string "51756241822296811805976783226325080499485581597535413178103183821696574086983",big_int_of_string "33133292298665867640377728259981259864134629947007197399888846250066688494946",0,true);
         (big_int_of_string "74865907703228420221823968110681376488936549827627893326971160034459366449175",(let (_,xs) = pfgaddrstr_addr "PrPpDq1eThQGF5n1iNk5s7hxhGQUYmEUuej" in xs),big_int_of_string "73603949390786246435891202529106401204497490608466254244782700823982207938311",big_int_of_string "72147167509404339573060676045447385868202566383170021572769360621597319367420",1,true);
         (big_int_of_string "83571426392909904634554894933726236452069195398929104936680887955900272223921",(let (_,xs) = pfgaddrstr_addr "PrKcpaiqkor2ViZFiiC1Pjpwwv2faRZRFMw" in xs),big_int_of_string "47936781433575518237082752025596483495611138344551923536579950867273211945374",big_int_of_string "67528806814022614471872768541270962036957548756453611078438278871310551349244",1,false);
         (big_int_of_string "84212405717016110884408832367059835079642709300617626147842497268265642314637",(let (_,xs) = pfgaddrstr_addr "PrCs1nUkEgzt42rprud23FEBakYKQTEAwJP" in xs),big_int_of_string "21485163383070574394305937156974833888913034247110082822898895605526951079152",big_int_of_string "51486141050309990526730015979054284783941593918553715075204933257534671390334",0,false);
         (big_int_of_string "106788103988844612790810817718481324465602732200590535287770491835233613797225",(let (_,xs) = pfgaddrstr_addr "PrFKpMeioNCbFdFBVA9xWMqEZWKvBS4MGEu" in xs),big_int_of_string "5824873326811811741895876388351284665798327165384880531277146025930567265351",big_int_of_string "89236388807973333802394893108189295565033548196806691939638415689274918295384",1,true);
         (big_int_of_string "19631873037376128752769376952129533189389849232270757611295481621256847579959",(let (_,xs) = pfgaddrstr_addr "PrGJmQV3aZSN9HS4D9d3XrcWH48nsMbu3zD" in xs),big_int_of_string "73157842780120951929006235004373926527933519592215224045317724113874901189137",big_int_of_string "52390283067942753607359832283433817741316217064071887759574342339904233520396",0,false);
         (big_int_of_string "99452694302833681568614899163095851195121845841490353613450184015870350059683",(let (_,xs) = pfgaddrstr_addr "PrRUVPSaiNfUQZ2ozfYvJzF4TtbvSsGjnb9" in xs),big_int_of_string "2711253870917565978084909730712472035916445236710800206318708451439816147497",big_int_of_string "45945838372989209983802734184663354283535858799775009961384705311177208324196",0,true);
         (big_int_of_string "15499092915473128057814756502462010336374945010709353007142684759776877235760",(let (_,xs) = pfgaddrstr_addr "Pr3hS2qabUeWgAhHs4os9qS8kz4ohyxdwp3" in xs),big_int_of_string "37782881459193541497423028098853390422332850514615768739954612052077862164434",big_int_of_string "21121674812949283434410171696477225041206575377475871357630472440882790197495",1,true);
         (big_int_of_string "107908312689718441655258393325339482124354972712875850169065662365754887877806",(let (_,xs) = pfgaddrstr_addr "PrPvdV2PSYsS3mTawizzVfA1yvSr1BPeyLG" in xs),big_int_of_string "39384971256976439590073636342284699452692962061126547954509885941822845940606",big_int_of_string "84132834246566188268602621711743445349868751253058266239935153380720399508609",0,true);
         (big_int_of_string "82934051606822377462713030324260312564401457914762897726887246026823055387698",(let (_,xs) = pfgaddrstr_addr "Pr6BnR526HgSLMJR6PKBCT8jH2LJU48RAqz" in xs),big_int_of_string "67971797001224995487140321701168081829592343605850809542081901054101206488068",big_int_of_string "97726895138298379217221620212182479521318141112590048869826665501869635608453",1,true);
         (big_int_of_string "3982622876544337535694724480170800945260813881866309247636125831264537277651",(let (_,xs) = pfgaddrstr_addr "PrJr7oFiANxHVBA9cdypabkCCxwJBomEQNk" in xs),big_int_of_string "7387099742432333099249590996152557505852686572170542764891610036863271341257",big_int_of_string "38657114026150266815557949607758660176968975310530797407842395778985971287266",0,true);
         (big_int_of_string "53385368555707516686361085906429538978315307600295606964644583123967419973434",(let (_,xs) = pfgaddrstr_addr "PrJeAj4dpK3eNkLyf7GiVDqo2KY6enGQAzP" in xs),big_int_of_string "47058152382545640340630910646955085348983687264634808370127438178875555281496",big_int_of_string "58938717301491387853222198354322165309151539468880438052091049443262971886964",0,true);
         (big_int_of_string "13264421510101452752576060229372075391629292558173633810843187163454822576706",(let (_,xs) = pfgaddrstr_addr "PrAdPPhCehjEwPkRXcwFUTeTDEq8wqq7RNx" in xs),big_int_of_string "40467303594050687492433168244615066733820245901347975507003680269753376488456",big_int_of_string "81757078023163206607363532286458036001940858322670321739170226507835084784697",1,true);
         (big_int_of_string "88112026127279683910562188458310057462294944401108023515937266594428733303336",(let (_,xs) = pfgaddrstr_addr "PrJBYyakq3cMrv7S4TXCx24uYfLttrtXFQz" in xs),big_int_of_string "108931287966197581800182178337907867734299238602909681988904765884464599016299",big_int_of_string "47339959735474770282306979153407986724359172033933128888663721211300624691854",1,true);
         (big_int_of_string "16051364840778330302674760687568633534049088861740184183675762729973009200456",(let (_,xs) = pfgaddrstr_addr "Pr9qwTjVqQ4h1xpJy98yJe2Jh6UWNS9uv9a" in xs),big_int_of_string "8410133790634330961036563430159354508969173948810360066403873412769933890220",big_int_of_string "7802215421551361639300383030086935163571190031841977325154682713659099507638",1,true);
         (big_int_of_string "45802237384680146979851215684484174488090074809499424179175769176271766993081",(let (_,xs) = pfgaddrstr_addr "PrKD2jE7YzA5aBmzMBCcDU6bdkye8E785aF" in xs),big_int_of_string "76977781583896485527773168160428150259585367054202846847829055173563901715389",big_int_of_string "2206592124568272542465889707157883429466291991205256775173400146162217192627",1,true);
         (big_int_of_string "90981472873871024792832515673753031369185373603375165289092113432597315722313",(let (_,xs) = pfgaddrstr_addr "PrR2pTvMZ7JdfWK6idrPFs2QUzDUmMR6H1d" in xs),big_int_of_string "97759347853926517461762640830497322513868614317826161404114265751468447904216",big_int_of_string "109798446741720199154289923639513449254744297859210124169263046989572405635270",1,true);
         (big_int_of_string "63858676488897553711638631965674326033331015028747650290182991358243240906962",(let (_,xs) = pfgaddrstr_addr "PrE2sbkYfizbTqrRfxtSHrdB25wPPYG5p8p" in xs),big_int_of_string "103298757278275757848705237759321564535685605844311185549118514126553346402147",big_int_of_string "115760094077576072102673605505583454581667142968822977221957257937775997218520",0,true);
         (big_int_of_string "34717758756996616037607190172616917462433893985952090950474626374014954893561",(let (_,xs) = pfgaddrstr_addr "PrBn5FHnyyjWeERgB8geCiXZtNrPoLKXuW2" in xs),big_int_of_string "70043344821114496897409266032123685204888076838522252694598793763597356526258",big_int_of_string "15511079581402901622544217565443667666380954844324296539219192008908438807567",1,true);
         (big_int_of_string "92348130080071314197215034632855263239169262377133531908496427893103043415463",(let (_,xs) = pfgaddrstr_addr "PrGJ1KkgJqU2fRLek11x5xyzQxbedEcNuNs" in xs),big_int_of_string "77233332616119362387701775568546356371903504085274408644713257800038318398499",big_int_of_string "4892000343970486901611599151731929545987033595226922261948754400974035450667",0,true);
         (big_int_of_string "10812063487663924661517578894065036155471272095932108589990755403536247901548",(let (_,xs) = pfgaddrstr_addr "PrLGo6zfrBpqN2K6dMeBGzPhr6YzKFbHits" in xs),big_int_of_string "62696874724003759789023317542475687129325935450941401762947900628313605364449",big_int_of_string "25462716872136078260510466801491047690748981052363739168417557767367594219411",0,true);
         (big_int_of_string "80509804646582593984624926939559476110116534199965758874686159241444001670477",(let (_,xs) = pfgaddrstr_addr "Pr9XVBPHLtdzovoPqfXvbD1YUFtc6aw2HS4" in xs),big_int_of_string "55142807401785250374129484278214341765427092561295166310972528392523870409124",big_int_of_string "7822912197960026976410058674427854540998714799399344039826788916619432132299",1,true);
         (big_int_of_string "37893278480755375332181348362686850949231882266271899029758065766330872102155",(let (_,xs) = pfgaddrstr_addr "Pr6i4nckz7zVNUHYnEUR8hUuoaQ1yXPpHhV" in xs),big_int_of_string "43162531478231879862895700056020117988320977991796897400770442137501702103181",big_int_of_string "16499182084100741390210343912600385387919138097990809150608621093089859162816",1,true);
         (big_int_of_string "45101267638945538159269350456557085763502042798874052760154068683222562462972",(let (_,xs) = pfgaddrstr_addr "Pr7SxbZTqtwpgQfHpUiY4Zm6v51xPaCk3ch" in xs),big_int_of_string "6897660485453554214695506114658814917021114673571600904283963406056318354840",big_int_of_string "96797553475717602883744456350552470003123540633856180451038726101691353105928",0,true);
         (big_int_of_string "49453249418144783430315703144802469279626377245999200483945105366471458892310",(let (_,xs) = pfgaddrstr_addr "PrCbP5Mgrs1We5c8Ng4vSnvXrDuqRNMm8tt" in xs),big_int_of_string "93439428640933637749809689124494803896665011296310812682004690993637735409402",big_int_of_string "108389058243400237256293309792425856162279865065456450802990002281474645631516",1,true);
         (big_int_of_string "91537196177458815572227703514444080515215744745116083089758889250185000660388",(let (_,xs) = pfgaddrstr_addr "PrF9U2QzJrtgCEtxMtzdQCmFJakcfhAyVrW" in xs),big_int_of_string "60825959708312791531833509331262714181187208345589294814955012516887936862828",big_int_of_string "34370733887535186065314473081632727718598140984049609180852074492313903752958",1,true);
         (big_int_of_string "36886174608297170216032590586090089415169008046447143140092844166826213097318",(let (_,xs) = pfgaddrstr_addr "PrK5CM79LNNxrCqTPbxF325ehb1WtgFsdoD" in xs),big_int_of_string "61408036251481149799199484475122352561472873454135400342205295108268618403643",big_int_of_string "101626010449673122919602749823659804474342510262127537237101533535291193028351",1,true);
         (big_int_of_string "79587536691372455601900573709470119693414357840606107559430869628547542401123",(let (_,xs) = pfgaddrstr_addr "PrMMYaJ5jA5fijk1hoTPdWLbA7vpJhANxUK" in xs),big_int_of_string "48977948675639849716919253940884390703576783777190907481262663654290785300131",big_int_of_string "32104185287750782921845372889730715149136271709073455124445286644054123130366",1,true);
         (big_int_of_string "22288592645435173925702690384005589976802347274481483240293734578132604215831",(let (_,xs) = pfgaddrstr_addr "Pr5grXTkRB21DfDWianyJ4VovFZdT9z4543" in xs),big_int_of_string "76123589253887003030288856732158968198143719218860573201285433177884322208280",big_int_of_string "42234698627278388884521092086776644981730683711916922883773214263717939594125",1,true);
         (big_int_of_string "91779809679319591901352082758417527125693649473840380820147888446807658512376",(let (_,xs) = pfgaddrstr_addr "PrBfJQbiobm7nVYYnXuPM5AipjMtDewpBH1" in xs),big_int_of_string "106401037612041933600625109099837892360024493318144358072595032025273647073449",big_int_of_string "50112335824306346669845484156598248075985542619089584544629459991939594466798",1,true);
         (big_int_of_string "67877108864631188389255554241615006707842415838263725007710518429841009803313",(let (_,xs) = pfgaddrstr_addr "PrQcejSFa52z2btdQmVTfg7iCAQmXT94LXD" in xs),big_int_of_string "87041822516961864988427491152348289166891249233526530876787438508422854752244",big_int_of_string "31573943107037315667285609672323268385291591187133481848793837177739037314481",0,true);
         (big_int_of_string "9558013719341671840605586099040420527443337038776798405615898551416378944182",(let (_,xs) = pfgaddrstr_addr "Pr35C2UfLy6SsQtzPjf8qpQrjSDUpLprZxN" in xs),big_int_of_string "25866102234209554870034150893755641416645642526159947322265347969930445359081",big_int_of_string "69389739127045607851360667956832458783607363346328815838280762116627829346296",1,true);
         (big_int_of_string "105547268982253112084368913491760729960859578055575697495342048335032936855362",(let (_,xs) = pfgaddrstr_addr "PrLH6VFYKa1dvoAB4nziHJjG9kUwJ1JV939" in xs),big_int_of_string "1094609987785189132637097645921754052660514762415598794316940655980651974516",big_int_of_string "25747833489461192805146470184391814366633440507827364655363885283857772471911",0,true);
         (big_int_of_string "16882048378794252286944772473540027818544305041064871251427360154126538352809",(let (_,xs) = pfgaddrstr_addr "PrCtEGxK1D6ma9R63k7fir9G9iCDkX8ydPu" in xs),big_int_of_string "34673295439883911093700745543561569531466313103699888256681889424762031422220",big_int_of_string "6831335212655688446874637488757188718556615019449961247118574382933404216909",0,true);
         (big_int_of_string "67441249035602197971879372349980001018040533795856838227904535464778230766289",(let (_,xs) = pfgaddrstr_addr "Pr8kjDJUuKcb6kbeA1sVWt6gB8yGVuYL2Lv" in xs),big_int_of_string "98525881230091485925137505331914445621420875872130011147303478328037866951950",big_int_of_string "38509172982936224750169506182331870955137765531181765480950119868279788879897",1,true);
         (big_int_of_string "63290728682056449888414275209163895041705068934777168797920064151143674306243",(let (_,xs) = pfgaddrstr_addr "Pr4WzqbmgCXzPin12ZyNWJWLq9hwDs41sj3" in xs),big_int_of_string "64535582447934027758661085468364620575902968490826983008069965301353686107429",big_int_of_string "61079267208579899785109706285860596081882024655945073096836917697345341969759",0,true);
         (big_int_of_string "5493294074661611629184927678557727814087685033767578059302295550665346508085",(let (_,xs) = pfgaddrstr_addr "PrK4iZ97kTMkWJiDERYZUyPHXBvwmw1nbu3" in xs),big_int_of_string "37707212809167726255444818649168400470841757771422582565682201545087391546758",big_int_of_string "52736071651176615482368010740401593134334568135395909880580541550127173767613",0,true);
         (big_int_of_string "21376016243038917972621395756897959811331619211942426969670144103540752498263",(let (_,xs) = pfgaddrstr_addr "Pr836qUCfBWvwM4dZ8kg14Wr3J7oHA3QYjK" in xs),big_int_of_string "44814978612045735526867918853127244564198626528119645431342144494934730024452",big_int_of_string "35485048095114637988148475234269967798085524964214035058407870328658550071326",0,true);
         (big_int_of_string "26053711741262381078912660123547824857342072158596769360095768504209046428277",(let (_,xs) = pfgaddrstr_addr "PrEcY2CVnQMyWHnwusGtrm2CdanRG818Dfx" in xs),big_int_of_string "112807755704769846534651438252309173420983012951564391192321218847201380990239",big_int_of_string "84600322174928263569333847272137426706548202011088044398672120111291262351967",0,true);
         (big_int_of_string "96520921248543856721313433458573893296856080605499946293524645737684439541208",(let (_,xs) = pfgaddrstr_addr "Pr4EYJEhMYKPnodZLiSqR4rHxz7cWaarFGj" in xs),big_int_of_string "94841523158635082487133340177372839460670701917324757817592107090494177610751",big_int_of_string "99212912952900280692839355458510933948684424183803143975851925054397152668310",0,true);
         (big_int_of_string "18846097207052450901242319149525668230792180563321874665865697525065777854922",(let (_,xs) = pfgaddrstr_addr "PrBr7TzLPbSGhfSekEQ36h4AyrmatvpWAx5" in xs),big_int_of_string "77239963850493501062523440590185465988027966811164441540778610290899792286874",big_int_of_string "61180054521331763733089462151926986208005489859544055317104485884739525115433",1,true);
         (big_int_of_string "108595350359005533688536496160105000255302717476249510987174140882087954316576",(let (_,xs) = pfgaddrstr_addr "PrK36t7oasP1bsRwffDvThnCjanuHEYJ51s" in xs),big_int_of_string "39222617037929618609456476991584382820516865463477719307081382518401261296308",big_int_of_string "5712913992822733094855397844509388790599198319631664402461776809392233984391",1,true);
         (big_int_of_string "61303994960176962528823189156271843086327746240344893233823143333800128347647",(let (_,xs) = pfgaddrstr_addr "PrPhjB554zy4b6BaxSKhZ9morSQEi98xdd6" in xs),big_int_of_string "64704502444505360018561330602131937138106401186147283326778620570160574637979",big_int_of_string "60971268156505410893963606789678607615227997039309300327489106641671527937566",1,true);
         (big_int_of_string "5925858817769881542630140196359766960690209343110577991416260566886111158368",(let (_,xs) = pfgaddrstr_addr "PrBDSHmXVPmf3cJq3FNeLgynqccvtBmod2s" in xs),big_int_of_string "64570470764017564129502389326163371695060088683137059225555001179445466552827",big_int_of_string "103897542469520291330788184937822176981112554516983247111647434251094828393059",1,true);
         (big_int_of_string "103087520110184478382886427368553162917608650384996279299925599445159702655349",(let (_,xs) = pfgaddrstr_addr "PrNbnEh2eokmVP3RRwZXnR9hB7g9EnkNGRV" in xs),big_int_of_string "68341500053814730977080582850587738543062567022557677260997962932424105494309",big_int_of_string "80282034618220980455533979255091797730887639366289181517521826606971963960146",0,true);
         (big_int_of_string "57962000633428553106925547331919677331598515680321018179919696024391862900368",(let (_,xs) = pfgaddrstr_addr "PrMJsKnMAzVJvcXXgfLNuBpHrmT9CnLEQGC" in xs),big_int_of_string "74153554289304633205423311863556278984327347928468219862120702965827416145853",big_int_of_string "91175856453042573602651271440405881537592015115025978176020434678779994003744",1,true);
         (big_int_of_string "88786618006912743852103089834491281819294735737915296183212879311222388540522",(let (_,xs) = pfgaddrstr_addr "PrDcUabX2d5nfLerTWn45eBerqeYjKM9vRb" in xs),big_int_of_string "40698863114170190102280060707110075158436804872363104976499433036802956700773",big_int_of_string "98507408709405035968624887265445100252202777635508388810700579498514061917936",0,true);
         (big_int_of_string "68179151187950031417758446109567406475877027600622363775617998834437456816686",(let (_,xs) = pfgaddrstr_addr "Pr8SMTQMKB92T7yk4Fq8e3yKdCzgEWLEkVv" in xs),big_int_of_string "51477389708770352254140490512814328531372864014151043474617382317483854027291",big_int_of_string "95590983604472477230056703446408089987738112483005144081129618962904774947046",1,true);
         (big_int_of_string "69706742720840949357803282956190113086299784826152658462336924976595470663421",(let (_,xs) = pfgaddrstr_addr "PrPXz54fFQer6gkXoK6BxiFPbHPhSQAEAMx" in xs),big_int_of_string "88594848150762908973817831535023303324838081973938246835514296613496848630793",big_int_of_string "51551770545302204229252380681012542916971507052727238316053963168977107520941",1,true);
         (big_int_of_string "51921500185136933435555415460557139625101227307712467104766787422701031954362",(let (_,xs) = pfgaddrstr_addr "PrNAq87XP7vBW8Y4WJFd6Cy6BFibMvsawZm" in xs),big_int_of_string "55785857517516567744470553365268251395978860252308134507839706231054615163318",big_int_of_string "100686091320191174803118720782581505722197326781658500827192765110282676448286",1,true);
         (big_int_of_string "26520973957088751951892174839546146395213354045697477452635551897363872894227",(let (_,xs) = pfgaddrstr_addr "PrBjk32e1zmnbpFw8mpov3MZgU5gTrydsZR" in xs),big_int_of_string "36627685770000578869923839078832119771098067182216148959697681575789265223477",big_int_of_string "3432075910002280309309710014484272905797691095257251686685676274867501377623",0,true);
         (big_int_of_string "18160208097170317880209574777058427364517207131180115872048305736463966897586",(let (_,xs) = pfgaddrstr_addr "PrDwTrum7RXFNND6aQV4aVySaB86wYVezXB" in xs),big_int_of_string "83442309983708338142252447567423475872143331499858839762881956546744768484197",big_int_of_string "50400734639315935316860336885633412880352643203735273084491414829752587412749",1,true);
         (big_int_of_string "33559059954627232012469183132956296610432558129733603371766850605155761044905",(let (_,xs) = pfgaddrstr_addr "PrGT2oDfsyWkDuWEkVWK7PTHcHBuejwm446" in xs),big_int_of_string "114553689130406309449887570164638244670796950354928412104699041905489009519875",big_int_of_string "73718848909637588502840111509065854696985950951904168055432692360776375265601",0,true);
         (big_int_of_string "34931521657572369651332502279489925171671674404153352857197022475502420299356",(let (_,xs) = pfgaddrstr_addr "PrNy5a76QftEnft1xpvyk7KmhqUCeMQtwij" in xs),big_int_of_string "80025758184469139678461336922962253425934213804756357978521646393106183433772",big_int_of_string "23047469031912969668532847667475909862494634273059597884831596549542720009646",0,true);
         (big_int_of_string "30932066392559338047487850378374740010446025391637328115287991799622066836950",(let (_,xs) = pfgaddrstr_addr "Pr7auCVN7B7A3ouGSYb4AFKYUtfLueqr8aP" in xs),big_int_of_string "52008191735687619312567887274878823668175142128954065398279310365011611613363",big_int_of_string "50045312889616103982718672301221214979412687317046860599712452178356126048989",1,true);
         (big_int_of_string "54242194653428626142078909073374595661906430867822738000627807155458316232521",(let (_,xs) = pfgaddrstr_addr "Pr5FVbL1YmcawyWLU8pfobuxnivYVrUji2i" in xs),big_int_of_string "103878338024087809636999469998355325764418126603783204246776603533417653895463",big_int_of_string "69698543968041251024536235662012498832656773819787228910313287673362793506146",1,true);
         (big_int_of_string "83423092573848869907077562805564169267149168468037186172428292724544759366114",(let (_,xs) = pfgaddrstr_addr "PrG8rhp8Lcfwhhdtca1WideV2eYneAvRgNm" in xs),big_int_of_string "72092265090963851770315070989504186607194382788060973187808582643712373235653",big_int_of_string "43679292681169463389604012840215506061073516209567861921747071572923076601508",0,true);
         (big_int_of_string "33120706796825233839395688979924101635068282221368560823478292546893637841870",(let (_,xs) = pfgaddrstr_addr "PrLdMKmcEDXhq3kjJ8hQZS7FafYRzrxedGo" in xs),big_int_of_string "68484885880021597923890131347144913707584864516567263185956089043321285161739",big_int_of_string "11159756411387743840909672140754312904147395049570121434590860868727724054679",0,true);
         (big_int_of_string "439419303590033650896584336354186238984403369892682423486113374517632609703",(let (_,xs) = pfgaddrstr_addr "PrAvNMJZs638u7MCU28FNk3zmsLNMgoNcJt" in xs),big_int_of_string "108619057069420418757630212445246798904749314704372094096020178003398221156364",big_int_of_string "8003664253222320248691698823547222352702707975146727553149037756352570759382",0,true);
         (big_int_of_string "29630782356652718104683768209172786765996520954121956916714688977032241727451",(let (_,xs) = pfgaddrstr_addr "PrD6hGDjk1G4ewtuyrRZrWpCNRVB2msHBaB" in xs),big_int_of_string "2702104198843406056588669748648091913405596459986812442513755477544437611392",big_int_of_string "18665292437406075548322111039482041145877447601765981260405754368241988597087",0,true);
         (big_int_of_string "57836470244975789637372942102437826952379202340947109316959967188360112004621",(let (_,xs) = pfgaddrstr_addr "PrEXtPQuXmX8W7ARvtFF1dqEPRgCjj9yDH1" in xs),big_int_of_string "103050147607864145073466630496754080842903039205941421709788214242875887406563",big_int_of_string "3948982971112313217939229517713205190243146620203362963787318407021194525700",1,true);
         (big_int_of_string "35593616882803399783790885829897204530633770111514958494726679208007768485698",(let (_,xs) = pfgaddrstr_addr "PrEaMuHpVNpAk2FqYvv1V8JeBtEBYEREUX6" in xs),big_int_of_string "60476125624250120190328466646027593277637082660808026406005636953437995249139",big_int_of_string "3127636513229695664521464959166548201602491573221404574197425887808593747117",1,true);
         (big_int_of_string "32958192906799897947083719223026569117497042908169263954630179647754723100751",(let (_,xs) = pfgaddrstr_addr "Pr8j3pb6Xtujm7n4EtSojPRiTP9RJiXXLFJ" in xs),big_int_of_string "4494071240697541003516064872805677469964390227757092829836314598243862830813",big_int_of_string "16855262577413959655398308912508310319946063176010917404906340539997240840652",1,true);
         (big_int_of_string "85813118101910862105153867304540191907126680094491175668402755973245361296657",(let (_,xs) = pfgaddrstr_addr "Pr7CNzMQ4yxRyNM1nrMhC56BDgeb1iwV4Fq" in xs),big_int_of_string "61435072583474943327051821177907459568978993698320842024082180645326945489103",big_int_of_string "28241608637636655764806651523875652672972269295916797375208470090159194088203",0,false);
         (big_int_of_string "108191984622378963160705715944701106631168933021893115079209916417031785824548",(let (_,xs) = pfgaddrstr_addr "PrHaX9GBqcbdnzJP2VftcrrcRCegVq5Y2Y5" in xs),big_int_of_string "79688889454713691785163913599899053077521852197647831261124413215238735148448",big_int_of_string "103137737954791042825747991525908158457060283967401325519385402538627114762308",1,true);
         (big_int_of_string "18929883153008802015411042608062270784364068180880847764422522447050127112126",(let (_,xs) = pfgaddrstr_addr "PrBpvoJx1eJ5DTJU6fz3t7DFqvWFg5kYqpv" in xs),big_int_of_string "80745368193482148983052527245088980829092057394324429730346506294307591540003",big_int_of_string "94774836138487397914750151429158146653155669786196705628179268700917878112145",1,true);
         (big_int_of_string "35666417204786094709087790457101037159993867502611556704853015226586839586320",(let (_,xs) = pfgaddrstr_addr "Pr3KFA83JkEkgra3961mQpZhCJWP3MVCJ8u" in xs),big_int_of_string "34234972487814544572994932780497435905762935651989897232633201861919875429848",big_int_of_string "43704268167925330446000889982897601726468379787630494781756878695017679257822",0,true);
         (big_int_of_string "2447214592642715269455113754079525397006014369292878471108276613689172975365",(let (_,xs) = pfgaddrstr_addr "PrAmVFqFs2qvmwqqpoVcbuEc7WUJekbGkNr" in xs),big_int_of_string "72765262538942194349650939145915635762146056844487306896651194117150219159359",big_int_of_string "88703218622720778458476732132864257678133311666031546900174010510926260068411",1,true);
         (big_int_of_string "110334399246214128576856909952787378825766923897148821553384660894369977560732",(let (_,xs) = pfgaddrstr_addr "PrMBc75sBu4giMksM5x3BodoFn3zkEymu9M" in xs),big_int_of_string "29698089263266868661065279131530288096611284902962006885764761148568988189022",big_int_of_string "58891096079998576763557000026070142165913268612603814352127967253497010240154",0,true);
         (big_int_of_string "35639335929895445518365579165187129008866251350157204642173281042404433321646",(let (_,xs) = pfgaddrstr_addr "PrQPTPPDgpBBsBnPSarcacWe6F18VkpJm2B" in xs),big_int_of_string "56964963130465580725603606390295461807808845201842270191391032440874404182283",big_int_of_string "29924067090164556178477718415658620349794013351297555943748201437362067335713",1,true);
         (big_int_of_string "32645669562785595950121379687151039158785316142477938433857738212043136847740",(let (_,xs) = pfgaddrstr_addr "PrG3J3SCgRt7dCGiyXR82RsCpCbRARNAJtv" in xs),big_int_of_string "109955848262694215406116942304928929577193983527975235380188895303229574663875",big_int_of_string "75486142009767993142826169391847296130436505207349825857806934534670160122346",1,true);
         (big_int_of_string "78111086752317220686560570784488991260510570064362529883434091784352629746095",(let (_,xs) = pfgaddrstr_addr "Pr5FBtVjWpryNcxH3tfCeTxyxMu7bFN9XGa" in xs),big_int_of_string "18054159905892823988456798372285356754459991777880112755221023746788782442249",big_int_of_string "57440854615500977742596480507004724558958114490861337511058114067705619406021",0,true);
         (big_int_of_string "30556200200494710753629415694089390399194243855701216081812778097453361901943",(let (_,xs) = pfgaddrstr_addr "Pr5tmrok4VB4VXr5HXNkDGLNaoFFzhyFosB" in xs),big_int_of_string "76295257295031346492344989394671716670753469901456262787389875843145402133573",big_int_of_string "89092867057948254679535967916249207782552735707550500682089539630400141605163",1,true);
         (big_int_of_string "13720133302111273692413240817683207035989750015252913138486924177358054152352",(let (_,xs) = pfgaddrstr_addr "PrFyDhzC65LVFUDgGHbXVgrPYSLuszHE1iD" in xs),big_int_of_string "69804611812441471382160711880894027782760669424414905660737482170350105033119",big_int_of_string "110269816981494151492628373419143835536406661445870219284133280822375490133635",0,true);
         (big_int_of_string "51423273197705475433246163906439238547647219098894482300775602732442728986699",(let (_,xs) = pfgaddrstr_addr "PrGoCbopBqFyhQo8ktAvxPQDpoTs3jvvwiP" in xs),big_int_of_string "5708487461344125842701646591686918583105538561052507412604749807480081775836",big_int_of_string "101029741809788047024339099495339942468069908493899739715777374360471465561987",0,true);
         (big_int_of_string "105258099399796733812761416767018062965138493944396744982511407956285399768878",(let (_,xs) = pfgaddrstr_addr "Pr3qoE7TW2uadaA5r4esucYNk6LdMSJ6t9S" in xs),big_int_of_string "58035234703314350593335630729394191855318761852755153067428996992251612905547",big_int_of_string "107836804756956012520013303223952488286776082694522296688107450274941005858598",0,true);
         (big_int_of_string "43065265444300677065992056052520980727803821579657978405720065522134851232964",(let (_,xs) = pfgaddrstr_addr "PrEWkFNrPLpGTLc9ahysF1qAJDXhqMPcmGo" in xs),big_int_of_string "20560782795854527847967344501211237014556306356911245303419248727529290536618",big_int_of_string "29074202344969903397245973923703534927581248298528437589866151889400370872276",0,true);
         (big_int_of_string "100517475743140011126956131801236980850617866537402570814092411937255957071687",(let (_,xs) = pfgaddrstr_addr "PrR41gavcaEVSJSTGiJcAz2LdJ5xuzkJiED" in xs),big_int_of_string "18296827686898675303376737426512991347444842887170527384721126955495567762747",big_int_of_string "94995900079787287119586085340481418559018683228835204374467626250063114126000",1,true);
         (big_int_of_string "55511511597861452488409803111591982255249649138638593994423271593527416610401",(let (_,xs) = pfgaddrstr_addr "PrHvgFB34XmExcuhiZ1xhgDDgFXCVVCCzno" in xs),big_int_of_string "107980726708755633556054953163249979147953748980083411098840642268166590142674",big_int_of_string "82003467307451304278508736784337067899561655509640194177444702541730938035185",0,true);
         (big_int_of_string "33163782733115090831890811286044341103393303097907836026337764807104962146571",(let (_,xs) = pfgaddrstr_addr "Pr8eTJ3vYE4tNgftRvqJHVXpJoKCEGtDhV6" in xs),big_int_of_string "8910812294239066318186948007025052131852423005804667145889355107336301656761",big_int_of_string "83647763826440552885230368080193380602526144378848207442767861576839013488652",0,true);
         (big_int_of_string "107518527183417524283076305592051912115290429507569052528518538593362882066437",(let (_,xs) = pfgaddrstr_addr "PrHkYp8fTPnzAQqN3zXBM3gh81e4SjaepKt" in xs),big_int_of_string "100399928509123177846603414211155319412417873450845046890096139527881849273129",big_int_of_string "97016430114389248703904863241637386390716635360733781036340504311004327380804",0,true);
         (big_int_of_string "87587694067303826337675593048706640778341286867899523167931159209705237715379",(let (_,xs) = pfgaddrstr_addr "PrJvBacgx7MG9d2JgYZVQSaBQFrGcNWL2D6" in xs),big_int_of_string "95858134214646753554753950311752991285782880010383092280499065215328138530580",big_int_of_string "47459484527437735206476012842908220055089098086731384879302489456800194532830",1,true);
         (big_int_of_string "69106777475973486572208151202588888455983998290494865495711073087499921098875",(let (_,xs) = pfgaddrstr_addr "PrL3qamidnF2kr2gXZhAx4zFGHmfPki1VTv" in xs),big_int_of_string "114251666005168642479539240012379991994096341367648028627787778669323425349571",big_int_of_string "70482036062605943452382674902781972764136892323937991997670686533225570629048",1,true);
         (big_int_of_string "91091309991508795985857102940030686169022987271390567842960103547858726145339",(let (_,xs) = pfgaddrstr_addr "PrRH2R4fgwN5a7E8ibjjbhiVrtZwdrxXF2c" in xs),big_int_of_string "52534542758362293896649757089083062327788681548124546563558052888706860359321",big_int_of_string "58184586800572366269113960453085132476271002276486379265810623077750883082891",1,true);
         (big_int_of_string "59341898288169730054320382853293979213983823732533803943263850698994170243489",(let (_,xs) = pfgaddrstr_addr "PrDEr4a4DxapqirfgHn1YYgPiX9Q2g5QFJR" in xs),big_int_of_string "51105956136709727846913339721506173455820945916290364231216192145872546092471",big_int_of_string "93565356215199437087592313024423943329158130389361859948675744231725098981017",0,true);
         (big_int_of_string "62492550150680797925817789915773907844928019317747821499832148719488801601595",(let (_,xs) = pfgaddrstr_addr "PrKb29ibcrowfK1DjXjinz25NzLSdasUVcJ" in xs),big_int_of_string "73923133817465210891167791096796575250875511401606274341109783854234986340592",big_int_of_string "99910021372366476429599031000946310492182043933186016603328653809168372285283",1,true);
         (big_int_of_string "37597152587962933915481098609090999241268825597391847567612810928544797588839",(let (_,xs) = pfgaddrstr_addr "PrCQYyfqtuqtS9MUsP9HEjHgSPMVU7eJ5ho" in xs),big_int_of_string "52401870114039982969294974060665118176229408456873671094597495360759970258738",big_int_of_string "15368261012972015201666181039600165963795584768953747174573110732452445410081",0,true);
         (big_int_of_string "69875114320503783427874218474138204137434794323550270757374403052617053615702",(let (_,xs) = pfgaddrstr_addr "Pr7tArDCrbzd476hdPNhEcujU9ZVKoCCik7" in xs),big_int_of_string "103395909700691048486875011337511239952909835760318969654843827207080054871958",big_int_of_string "94364927686175013128755663688248464802156395893864697397091137581344801915163",1,true);
         (big_int_of_string "56024714925788321100972519475558882431476850807759094951505791770177913460073",(let (_,xs) = pfgaddrstr_addr "PrPMrfa4PA3GzE68R1YXb4YWqTYKoYRB65h" in xs),big_int_of_string "62465057608345013312654210702578864136652608246319866259860722559655210701461",big_int_of_string "25261729178714341642072384024386634120220991546978403064610553365977492701444",1,true);
         (big_int_of_string "72314634133543767169534144451038593723554962492829447093654034254112951216208",(let (_,xs) = pfgaddrstr_addr "PrPmPA7dJA6iKM2PVqnsvS9L2aj55dES1am" in xs),big_int_of_string "71297336618123131806333680336811063392149752174510587509240376287534354493376",big_int_of_string "97463903961896412484403857630861141081606503240373010159462983852305459400212",0,true);
         (big_int_of_string "105950939660954558189928187561949045610866462481665190913792269058743016662926",(let (_,xs) = pfgaddrstr_addr "PrRkD7org34u2zGMu1yP7VeYK9pYoYo6dbB" in xs),big_int_of_string "70926420514126589274634020096925853156555788669552539069880501310104270268541",big_int_of_string "110181474007564475551701080767134542443812607356263969558817555911082319156815",0,true);
         (big_int_of_string "90010570290702699160331140853000345820773730240470861255514429823103198653545",(let (_,xs) = pfgaddrstr_addr "PrH1AeWxR5fkZeYcCYQ8vXXD3G5fhAKVfSa" in xs),big_int_of_string "350378467035508710560468695879870529671845194616308471839040273847623982078",big_int_of_string "43687394175340904604884661287415537571768798979200908329241800494621685401677",1,true);
         (big_int_of_string "68594657710651388283335887326264537321011821789238159004899514365865884526884",(let (_,xs) = pfgaddrstr_addr "PrDmgp5JYpHtmx6DcKUHXizJAsKMPMfFqx3" in xs),big_int_of_string "37998406577301727985647092611387215972686163589328438379562634829928028000886",big_int_of_string "20884480007710867971164997094984430521794958807844029785889642789372726629815",0,true);
         (big_int_of_string "6797967757571251116829074519200702591497517984467122768052850439339163920683",(let (_,xs) = pfgaddrstr_addr "Pr8z6nraPjetSUsuXAdnjyzYGo32jmSg2w5" in xs),big_int_of_string "58921950745073595220541018745496032146945306977706701956661567187631699131991",big_int_of_string "28584030346445342363989308812420110291551544240564439004882680370275650743242",0,true);
         (big_int_of_string "67002246646894115890820446897371693861077801984336348861328987985200861569950",(let (_,xs) = pfgaddrstr_addr "PrNMCJSYkTw4KyHKjjaERAo367nBs1fUKi8" in xs),big_int_of_string "32753528056073538956468384922627603189672896038544523444041076920255517280341",big_int_of_string "94204640942543766749148280842513146347806414803830616340865059708542307564922",1,true);
         (big_int_of_string "35016204899508229107615642651419163541183054628736327641125291363796737191937",(let (_,xs) = pfgaddrstr_addr "Pr6g9a18ePFgEYftGwAJ7oW9rAvTgXZpaUc" in xs),big_int_of_string "306403071456391471701175766814496362131909318708396997656999393050494598050",big_int_of_string "26370824544718684072424209538898718198568792387628111460023046798614842450758",1,true);
         (big_int_of_string "108639664667582342137811605321338404036806376111478949095230715612624941521299",(let (_,xs) = pfgaddrstr_addr "PrBFQZRJihPCKiGwSMd3v8NcDShSa1Z1bJY" in xs),big_int_of_string "15835679715905798530976955990082068142540554877532945837060531043164259339801",big_int_of_string "4310700144806448077440108260578853672474758350916426293306733642524032658861",1,true);
         (big_int_of_string "13874982251383016415817278594918880186778501151244430555995521865749995345659",(let (_,xs) = pfgaddrstr_addr "Pr5ZBM7u42H8rYMMsFtaQbeZepwGByUyVTw" in xs),big_int_of_string "108185792046862554023614650355890839475060977849371002035470948349609894600428",big_int_of_string "50646286435085402649375070945840669859452114112715666042415611947222751382378",1,true);
         (big_int_of_string "64533895708513038047962105304237424857822068448412955163474598256224550504721",(let (_,xs) = pfgaddrstr_addr "Pr7UPnZm2Uuoqi3r2raWmfgCu4fSk6MqxLz" in xs),big_int_of_string "35029930383848760913753250433057326409283246228705280985595075762734196277864",big_int_of_string "28987992990762122647549834164572873482943324039944461421128752784359753000968",0,true);
         (big_int_of_string "88809393543386210634608111314954005150251842987022272861019308481886081786220",(let (_,xs) = pfgaddrstr_addr "PrKhJ8nCdNL93uZLqoAi2HHt6XC6fAq2FHj" in xs),big_int_of_string "83224265187802504266520391250915856742925174928054743979370523386266724346334",big_int_of_string "112143277607263384846289957140448433383351420308479548904789937338010757107460",0,true);
         (big_int_of_string "68855312449187188234332521495821860338413635263165879206091823454523512879513",(let (_,xs) = pfgaddrstr_addr "PrD9xnufhGgNXKmtqihF1yHjJ4YrcXZFuae" in xs),big_int_of_string "68478258909424512675277760386969793198202326194313032257999788644049470449187",big_int_of_string "42191628850497538223153249644440347632574177362884418505204584705481082395282",0,true);
         (big_int_of_string "85265780777415884010727634367125469356475883618318552064829901649604745195622",(let (_,xs) = pfgaddrstr_addr "Pr7Xwf2GKSmiiYARCYhBQbifTeL7H9wjNTf" in xs),big_int_of_string "93096149267981761798291494483639423922628864206825691942668929782472844420300",big_int_of_string "99225429050438526757572967175991765135873930283392344151956345917384555167943",1,true);
         (big_int_of_string "83588921958494725443366054085070987529970789551449371271411266237568560387304",(let (_,xs) = pfgaddrstr_addr "Pr61aW4kav2s9Ue6dnumjfTqMvzqMBxaKMa" in xs),big_int_of_string "114590240383401722935054039343734989695104805096678372947751014364528900360658",big_int_of_string "90454993948049548879006778116887201443676977508939657464644442259284459933183",0,true);
         (big_int_of_string "35303397899753231325407665702452014139835228256424494477696151752236033621125",(let (_,xs) = pfgaddrstr_addr "Pr6wEwL6E1VAs5PJZzfwRiHFnizKVzhmH5w" in xs),big_int_of_string "15110707721796107944870328167755667785874966332095886655781466443587239437705",big_int_of_string "82276496502218670634258891731629112988495527715161270404034296820470944087558",0,true);
         (big_int_of_string "28370583792790855772158775939069123067696657653486722623422764467559557801748",(let (_,xs) = pfgaddrstr_addr "Pr5pxCQEBFKisN3PKvmYd244cT5GqxjDxdu" in xs),big_int_of_string "72479602952063844388787341388913042230886518545664204692865573568793020543697",big_int_of_string "54306424693277893486642340400753584881118445004747368245961734831013134246642",1,true);
         (big_int_of_string "57807810290108300666766130350242893738745824765245348682765164162541469606803",(let (_,xs) = pfgaddrstr_addr "PrLU9ots9WDJBvrbjen7XwcFn9KkXLeKz7J" in xs),big_int_of_string "78798921903618908095797894294442376830359452252674482994185287695673219843168",big_int_of_string "82058902211037683157164513370533421166566742994847245682548056886463015160563",0,true);
         (big_int_of_string "46612679668121926098300143804902005056779628641451185021726303077825165241364",(let (_,xs) = pfgaddrstr_addr "Pr5RAtyEar2ExmuqNikMGdvRB26mzX6CMAo" in xs),big_int_of_string "16653920493962468701175528384943266252718905858380543782084748617097630398654",big_int_of_string "14423690478366406955947086304864048216710304067182616270452274808019447936295",1,true);
         (big_int_of_string "59203856999257883978195591461527816745212366917988551747621154897930919209219",(let (_,xs) = pfgaddrstr_addr "PrDd2Km5adhZv6BSR6xFEgd1SrW3mz2r5J6" in xs),big_int_of_string "111015240317971289457748172778717526594753075001217053302409726448530635512946",big_int_of_string "37144244273181613396555318946629957043123764693903325358611799778209876072383",0,true);
         (big_int_of_string "67834703138885895566297652889132838774042723652496278198140852437770022270724",(let (_,xs) = pfgaddrstr_addr "Pr38TkxYJS6Wx6HrxVKt4jqgn5p6gMnppTm" in xs),big_int_of_string "58692382996781953730233585993694391715692854275195156415410377179110101473958",big_int_of_string "63911639360422839283457438935242706026300694408286398375673723563792628346017",0,true);
         (big_int_of_string "26314077905350322957328592508265940519564788872884321735929633890790111533519",(let (_,xs) = pfgaddrstr_addr "PrBJ64YzysUBettZDrV6Gi6UJk6y2f4S52A" in xs),big_int_of_string "2963453715660777481880837533979168338515118037099220285394453628568063284537",big_int_of_string "106255905237542848947097825135098350376010093260785400710033367402902468433119",0,true);
         (big_int_of_string "139150074720316745795684629656548848041436569380666428158283456484860674374",(let (_,xs) = pfgaddrstr_addr "PrBzmJT1kqNhHbkoSSxh3w54t3HxUyd5Ssp" in xs),big_int_of_string "15239961680880829741229643432717324930592934526223509314766323120923122494301",big_int_of_string "112448369864012134113887774717161908638660565357283662652546528103731810077050",1,true);
         (big_int_of_string "104855205463843491982367059515924839423524818438679745669621555195561508859310",(let (_,xs) = pfgaddrstr_addr "PrQqqd3ZcdGLc9BA3smcpKhvccMvzxHfrgu" in xs),big_int_of_string "87397580909619472404236237839394092766553844534955069250664344813218392395487",big_int_of_string "29107057923066181449690620106652611740855143377085796488315058388732616830552",1,true);
         (big_int_of_string "114772142264420922354082318211640256497836002919900184863761878829508824717365",(let (_,xs) = pfgaddrstr_addr "PrGEq32w7LKMKwX9gBdEcUzTqgjYyTnHxo3" in xs),big_int_of_string "23836911260527599823227232184389215810830826427234333625537201894521603351467",big_int_of_string "44537043456079546768703764181572117658160901341591650342635056403333136826601",1,true);
         (big_int_of_string "100146681127041332205744202188232555267791761700395350250337577556747689908198",(let (_,xs) = pfgaddrstr_addr "Pr32cdvgQNJi52n2jG9fTgyqvvfFjgSQgGN" in xs),big_int_of_string "103934338657985694682040417253157452146802259883145948209489586421269843513748",big_int_of_string "113844890315909126887527902311108952645972861146071047889571256161810847969225",0,true);
         (big_int_of_string "2636196568733706133585654489638193974619101388110986911892189683811038316840",(let (_,xs) = pfgaddrstr_addr "Pr7inMHuTpMks1dk37iHFEKUCD9nyZP7mdV" in xs),big_int_of_string "77612311340260284598099292422787260829776705847017295072051785337581109215010",big_int_of_string "40139184735603943025753395275102331706397250297776794841667756224222427317793",0,true);
         (big_int_of_string "113267945450201790632591904636926852869910368455996294713847788329337255662895",(let (_,xs) = pfgaddrstr_addr "PrKSyvRF6XzVTjt43HF3JabwHyJMehk1rCU" in xs),big_int_of_string "107051535051427678407651561982053801125898815732033403670726366893996255145737",big_int_of_string "103778222075419065266105719911293639292081421328286285477766162620177029881064",1,true);
         (big_int_of_string "64972721662782962563179252010946486812989107491565782617234435871420618637700",(let (_,xs) = pfgaddrstr_addr "PrG3J3SCgRt7dCGiyXR82RsCpCbRARNAJtv" in xs),big_int_of_string "70350047081868318623573931022767665287012789025864956543899671248296628643285",big_int_of_string "89800740859690697528262962608057767452642464036425147767872739431392720427597",0,true);
         (big_int_of_string "114528594289668670222931639329731104300121505289476080573259523204494553405570",(let (_,xs) = pfgaddrstr_addr "PrQ127Wt8oCAfdnvw695awTY9ZBfJnnKEDa" in xs),big_int_of_string "35496774103061378231026797382478932652712084444600906476389529878453880104675",big_int_of_string "9652035675978946868810875824639734926041459786294516145442139463895069245114",1,true);
         (big_int_of_string "59864775467661469445060537692999647946412980780055940124663345959633051555648",(let (_,xs) = pfgaddrstr_addr "PrPXoiDKz7RdcragZLNUXSeqVSKNvfKzJpT" in xs),big_int_of_string "2907788999020899611065501306380206857560430124956557598292596948592399384053",big_int_of_string "97624308625168398882311738482121184844669876718123317594692592228242773185986",0,true);
         (big_int_of_string "85873312044460239417921185801195413857460086613518121142947606766352785374459",(let (_,xs) = pfgaddrstr_addr "PrE2XtrJ1NgKzqWSkoJyNAFuEw2sX7fq5z4" in xs),big_int_of_string "63282978811454531758811032930000325829262737320472977596477155780117535149944",big_int_of_string "17150438752228066033136873619822148236036401541658498055139401792230498824736",1,true);
         (big_int_of_string "15482759930330046314327755146808668368402565573105462096670495609496140725171",(let (_,xs) = pfgaddrstr_addr "PrFdMHZHuFS4NJa7qUd3mJyg9pdM2xfKp3f" in xs),big_int_of_string "64726636556205884773686696704535771045097087360808743488052339368760642699792",big_int_of_string "17083474706841721683854103062255015477751067395215066166301260813435485261264",0,true);
         (big_int_of_string "44376660858347458610134390835287229111958601827634059465176972664346170229752",(let (_,xs) = pfgaddrstr_addr "PrFLgRfv3T18egvydezp86Q7i1HbETQTcat" in xs),big_int_of_string "113708856093405859349428416534273895443800721770638401365493131974895409639242",big_int_of_string "34400717843315618015393928674461973255707962528638128773949607172776977290152",1,true);
         (big_int_of_string "62445745507079092072747738721476957166245788504556264533822678231082414117724",(let (_,xs) = pfgaddrstr_addr "PrKHMRh9uPMGh28URBbHwZhJN5Pov8jNb9p" in xs),big_int_of_string "47296388205628412989445118454680069160196854661512697370813283209852125870421",big_int_of_string "104150669672739384680156678709843298461972016859077062248884200589601277556942",1,true);
         (big_int_of_string "86733973843691947759351538412557890624462955919221994697523156280222946846657",(let (_,xs) = pfgaddrstr_addr "PrNk4YWL4TGFXKqarTAEkPoLwmgDNLDG5zm" in xs),big_int_of_string "76567455282679806011973320489347849906977510907734575568709220196075853899472",big_int_of_string "5183244241088311043818138862297195221896782122471788669780779516256643021563",0,true);
         (big_int_of_string "12789041804487066700660491261239240206684398907878123342800109304538231914773",(let (_,xs) = pfgaddrstr_addr "PrL1M9YdTLmEteNYmayRVqpq4REvp4zMD5x" in xs),big_int_of_string "48353987641822029914052428760330758534537103289595084118856239251876681377022",big_int_of_string "68243599920432401294508292504880763737221982068766910345400209108740289179948",0,true);
         (big_int_of_string "56896731446426627262023400177365004173805260963117359982742882369769972913155",(let (_,xs) = pfgaddrstr_addr "PrFSETkdB5DAVfGFaVeBBjKhyQQacWveiZv" in xs),big_int_of_string "79933274765426564498886800961550578375957584454296314162754600225409368924412",big_int_of_string "46339022102366291556112351474250627318892247226547870781970700471824791374394",1,true);
         (big_int_of_string "70595759206826847804418747624648027270403744354905998366350612756861622933947",(let (_,xs) = pfgaddrstr_addr "Pr9w75NdX5BwQnCi6Po5YoR1ghwW5fFkmaP" in xs),big_int_of_string "105617959953329845481376255621977635004172176594844579659550129089805174881157",big_int_of_string "22761941539280616527618347215857691980281265185442584216216210300798965361561",1,true);
         (big_int_of_string "64165007649476100097226195164777757650685530238807846359803569709651394148457",(let (_,xs) = pfgaddrstr_addr "PrNddZLqGx8DrYBVbyQewnGL3XpjeyEn9sf" in xs),big_int_of_string "56314696299959568096016449972466611157199090067716141486267762606160597415690",big_int_of_string "43588188742412265640459754279440072581807873644379936097971814577195120978298",0,true);
         (big_int_of_string "45470216587034665681389782195226848812876280239530887977387574103540098486602",(let (_,xs) = pfgaddrstr_addr "PrMmLSgrQZZ84MU6zLZUTSKadJ2njjkZRrp" in xs),big_int_of_string "87363623081134426405511736278892101914070513519712754129422384490050283520464",big_int_of_string "93491120793614442101825957383494365824313338933261875872713755993425068785454",1,true);
         (big_int_of_string "62521129002445300551651307083702060286430022769429614584824446102659900327505",(let (_,xs) = pfgaddrstr_addr "PrKeaBsgSPrSoFj8s2xqwWmZNsT63aD53Aa" in xs),big_int_of_string "101319553037501939155441545559108963113412299534367430528203413385261477364943",big_int_of_string "62712674868877855797094026653947818546028204376392124122385250385030251672623",1,true);
         (big_int_of_string "97419154360990059991233311828470707594523760198512605084575946215028358564927",(let (_,xs) = pfgaddrstr_addr "PrPhJWS3ZooAxiAGuN9Ft3Rn4FVHsEgSThw" in xs),big_int_of_string "60016226031210035512470278082981010573024774450851901745364612956147774016191",big_int_of_string "51709986509038709039996523170525403377585708316864516120712642047993093459799",1,true);
         (big_int_of_string "89552124892281178411005616968905663295843486009437722763153630320443828437016",(let (_,xs) = pfgaddrstr_addr "PrBciN4r8LPF72rRM4kWtbgAQs7rFX59zUB" in xs),big_int_of_string "71838342936411073447822725951885115764300007227754245401591870035292169057240",big_int_of_string "31551385340353017551292801474230895150696313299087123932285773083414021832734",1,true);
         (big_int_of_string "75058249724079415841759381730553344818417780629875358157155309358366179464103",(let (_,xs) = pfgaddrstr_addr "PrPwHXpNw678U3TgFibM4tVm48h8E5xgx37" in xs),big_int_of_string "12974178031430759250672828620773900126104021037899586324031951959992388092094",big_int_of_string "114940910654294942927857572311069311383275234409705996869518971741306106703552",0,true);
         (big_int_of_string "67439492453613792646832145465821469871809644019751152815990807093047974679447",(let (_,xs) = pfgaddrstr_addr "PrDmx8UWHxAY5v8EdmS9DzbSfox1TmtMEvH" in xs),big_int_of_string "76357732321250427129709659694259531402523407617398433278164197787766138649087",big_int_of_string "96575656732935881875349196589414884511147744062852691691582142298558261575393",1,true);
         (big_int_of_string "81292779103920844349907496338518962708330511499711417808953118026890631616839",(let (_,xs) = pfgaddrstr_addr "PrFvuuhdmH777yL3HP9kdYpxHg5spb2bP2a" in xs),big_int_of_string "101672442111417357593654000303439717460942622566012896136693114072625165954744",big_int_of_string "36882458615006320540723232616066932796144473572212309179706397091156126210707",1,true);
         (big_int_of_string "91689536235933164137273208777577564687562082950308640969600728061137771697696",(let (_,xs) = pfgaddrstr_addr "Pr3YmMnXP9muACB67cgLfpMWrAVcY1Kb57V" in xs),big_int_of_string "1075567311477369815945534875285183795489593262972009780395767998390982784649",big_int_of_string "43831125005101855385881803697426671880945154378414963426350116488244378032616",0,true);
         (big_int_of_string "69667423158251213193173410009310663862127275644067763609152569957921951012997",(let (_,xs) = pfgaddrstr_addr "PrLTJNhDEwW7pvgiHJzmdHDYX3SDWek2sqb" in xs),big_int_of_string "115565797094114982640894376376722457360965447124252566296718413468275662693681",big_int_of_string "24429099343007517904671068376743296089382680613576986095015120495349816931491",1,true);
         (big_int_of_string "63027842149217619916298209636014012715647707990222203098826920931754493586479",(let (_,xs) = pfgaddrstr_addr "PrMHLLzvJmLeos7aJQZNXhCP7PrwpGfKtm4" in xs),big_int_of_string "61246028207894613968605884073726072662280385321698435206879926310438805019250",big_int_of_string "71704493484691499107268889172000351715277411672631058495375602266402326625618",1,true);
         (big_int_of_string "42354217527087415717799768839671451501046329432704506830079622501811243326085",(let (_,xs) = pfgaddrstr_addr "PrLd7XiGctBmHi87TFeAdwkrjuJCiEG2F92" in xs),big_int_of_string "52937729728996463497649869327888525302494309608754913360997932646889991472018",big_int_of_string "58146689079562860082993947914520488620969032275288692783636646268992457402206",0,true);
         (big_int_of_string "30506425595965021278149103669225645297993229835991346181613921607663401395843",(let (_,xs) = pfgaddrstr_addr "PrQUMGt3dUPGA45ESrsPUiBprQf8sWHRWkV" in xs),big_int_of_string "25966625167789672055218266929872302178263181334682591818946585331467830159902",big_int_of_string "107463519768056660569452238839368421089979921436910299509136618147383413249486",1,false);
         (big_int_of_string "35015134862741721354647627921484590690149408342374718235076033645859784574260",(let (_,xs) = pfgaddrstr_addr "PrMFEp4oh6qyvw8HYUvNPw2i6sti5RwvJP3" in xs),big_int_of_string "115486316797602356442126972083654138675156185238480061840460594087947085331072",big_int_of_string "109477136301500571146325308663875442276840832815352675825851220146034712313341",0,true);
         (big_int_of_string "111563811357608980949304240064744740370551360560597861781327968652359109061407",(let (_,xs) = pfgaddrstr_addr "PrFZHyfU9Uav8VTR17tor3YBkj5Vy2j19CF" in xs),big_int_of_string "9665478917237041125284870663410261553059971428443542005486388083410235390596",big_int_of_string "30472078498934971042925971165486091794824662429606319646298407283389189610654",1,true);
         (big_int_of_string "85121269044135996750312927533188369918107837621416578590225170399982703370127",(let (_,xs) = pfgaddrstr_addr "Pr9LtYvupHKyJhugseAnNh3ee4ZjmpEkusV" in xs),big_int_of_string "14245970947417695114797187001821744636081155189023771385362141456113143117614",big_int_of_string "2865509799499241348193151307475260502503852064782603544073702591417626972201",1,true);
         (big_int_of_string "103660257899491374350070083241218926686384804808701023114412346979293723585190",(let (_,xs) = pfgaddrstr_addr "PrB6nvhdSpdhfMC89uiPSkjKvKXyeiKMEYY" in xs),big_int_of_string "23322240189157616003586986727799299058183469273417132450613673707795552544983",big_int_of_string "33042237526758651900344120441576430655345891148707516268978085104691647795513",0,true);
         (big_int_of_string "93232921518681972797645491557719154125231486057163312703584375164300946950550",(let (_,xs) = pfgaddrstr_addr "PrBmirnyWD9F5Zh12GZhvHWDmevaq1Y8v4f" in xs),big_int_of_string "82129476283589477891174574746991022265348548896262831014829666583643868190213",big_int_of_string "47044224639470211834865132026800386071658690847147649226676549405617473802709",1,true);
         (big_int_of_string "90686106520763690586860758274340038300458894337416571253291979380206131814189",(let (_,xs) = pfgaddrstr_addr "Pr7tD8GgKB3RXkTv6iHJZWb83jGLQrNkK2c" in xs),big_int_of_string "104686569514584090413770406827137770845478771892631994661305108444824017448463",big_int_of_string "26539022347347288643821997664476095138392936346513335395531069323147955307391",1,true);
         (big_int_of_string "82227769412427095918389865212528254204988635414214271544549084224591411450537",(let (_,xs) = pfgaddrstr_addr "Pr6YySyj36MdEzteU2HCfzvzGELMhJ2kNCH" in xs),big_int_of_string "56896080887728333740725856051364646175306721722250719387678864718750357407820",big_int_of_string "25604895096534607311455900688441619740135202784389927510004302794806574894219",0,true);
         (big_int_of_string "97867312900424470079057941401702592351552557150812999640598482630363735652621",(let (_,xs) = pfgaddrstr_addr "PrPzzUkNRGrcHnyyZpiGuc3nGThaSf5BJZT" in xs),big_int_of_string "57544328187504091628752451621616067980320531227323248949875350448429844701870",big_int_of_string "52569654198292884965990161866967187051158363333293145997723536452412526876990",1,true);
         (big_int_of_string "7197967618442441534839950203376015854887465206557735764150103259034527374338",(let (_,xs) = pfgaddrstr_addr "PrLBWHYeBoE5MH6kLNWzWkCiGpJ1d8en6AZ" in xs),big_int_of_string "95857495048648263442466174131750400430935772614709260920051267551156461416175",big_int_of_string "39902970448501456831948724681739528908135141607057014379625944272456798120063",0,true);
         (big_int_of_string "17958388744677541219575010227629181715663204679490384114646612083134600777393",(let (_,xs) = pfgaddrstr_addr "PrR9EujsBWx9nw3puDbdJ96FpxwFZC8a1wd" in xs),big_int_of_string "2843640477578290456766453530736395482675790514963835270253236832575672968331",big_int_of_string "113868251776843583471537494078618302898093678459997204945567979215372263373620",0,true);
         (big_int_of_string "20698189017473411480415132269651382262265079650293377285423512153625915617780",(let (_,xs) = pfgaddrstr_addr "PrGW26gUR3hymRfC6YiCsuopjcjd99w5RgL" in xs),big_int_of_string "7979289893842613264318221552136615820449804313828573170173455298355586168420",big_int_of_string "63380494056680843892475681571138008648536630475775552972304372441170320011478",1,true);
         (big_int_of_string "93513152150292521521076721218104912277199317147598497329416367661784008618197",(let (_,xs) = pfgaddrstr_addr "PrD6hGDjk1G4ewtuyrRZrWpCNRVB2msHBaB" in xs),big_int_of_string "53578573756406633429329375294406542880367713354611983438171449879891553820562",big_int_of_string "45633520631041314388061094929542550386056713408984685866587205978406313334363",0,true);
         (big_int_of_string "14873486709761352572833040599172267547888783826448789883325110604408920390777",(let (_,xs) = pfgaddrstr_addr "Pr3RKiZ48EAdBVvXePdiGndvb3sVXjQd1sG" in xs),big_int_of_string "109710605106795571332039656787993503262620664974544566800006157390034019353653",big_int_of_string "40767492004793314508581278439676693052462622484555129046742677526486401872836",0,true);
         (big_int_of_string "73660162295006838324627293251235062750718032514656298159110293723534822703591",(let (_,xs) = pfgaddrstr_addr "PrNsSoBB9EovvGEj9UmVj52WaReuMzbYYKZ" in xs),big_int_of_string "67667017274450367172975773289060104629904812292068549427453385421224425664427",big_int_of_string "96506537576222384358192847175560677895328788516593962221048079386920518070607",0,true);
         (big_int_of_string "9048806994212331638115497960370673752363962950877920793309576966281678822499",(let (_,xs) = pfgaddrstr_addr "Pr3SuXuwBXsx8F3kAJ5Zoz3Ym7cVDFMgp6d" in xs),big_int_of_string "45694048046424806489709184211860663926923572247204587524802521700356443017603",big_int_of_string "61972786145640695521272471020741840854959355788373128486147753546968686998045",1,true);
         (big_int_of_string "79033359287717008330676025899812528716725548020412241828150793117045418258508",(let (_,xs) = pfgaddrstr_addr "Pr7rW41EmHjCFrQRXBBp6kemfSp2zwWfg9V" in xs),big_int_of_string "46678500375413751101803017390830664048139425248121018723297753909058286168905",big_int_of_string "56571648077601290533588746058079239656733246143227658335530637884040888554138",1,true);
         (big_int_of_string "3455675121406919644230542731210423110160986261518217889926153338526544091555",(let (_,xs) = pfgaddrstr_addr "PrEh8FcqZHyxj7GdJPKxDPXDF3Y3qNNJehw" in xs),big_int_of_string "15052426487100666587149462769873784581651865291181893905596047011975447822416",big_int_of_string "57273167057410442136256717054129659032733620926002658679426796103559728314717",0,true);
         (big_int_of_string "47067549054642189335029083420518320514874921455230736206463209452237334281802",(let (_,xs) = pfgaddrstr_addr "PrNPbUpEtuQ1c6tbfnuZAbVTsCn8MtZWGGZ" in xs),big_int_of_string "22391233352672195378424827771119810905744986286039697085225957515479673220475",big_int_of_string "81969944301301531668125148478452419714851843302688614676398394193759040849213",1,true);
         (big_int_of_string "84810284258748120875353715483451266416594405459445161840536017108147277565117",(let (_,xs) = pfgaddrstr_addr "Pr67PmkkZZkwkW98vaE3oTcNh6KBedKozQ2" in xs),big_int_of_string "72553346458372689231527363784842072104324701752885280485568085916852292055950",big_int_of_string "890789977147702851554043555433088093620327800980613642027322267479993072122",0,true);
         (big_int_of_string "105295838690373172559833868804502998276180724456679822343149873206673187146607",(let (_,xs) = pfgaddrstr_addr "PrE1v4hkuigthUWmrGi1gxnNtvNksVTLp3x" in xs),big_int_of_string "112715005094785196572400504416489325044654879283353266892256529164349149700860",big_int_of_string "98819445274633189958056944453524756423742928870915946247076148526269102304565",0,true);
         (big_int_of_string "67668239479348145393793326757614206699223655758955309088115533185983028294436",(let (_,xs) = pfgaddrstr_addr "Pr37S4Kt15P4hFyS27iZEjrbkhn1YjSqybS" in xs),big_int_of_string "42111559611970618714149806401003251332684250744556445390120833399587243637328",big_int_of_string "111882536687891837154765661486986808073230207038531589367551980223771792629775",1,true);
         (big_int_of_string "90759086540348247431984982241508775555131142972444749417721473994561218554912",(let (_,xs) = pfgaddrstr_addr "PrPPSeaEguxUCWNriktsrD29CQUhDFqR8h9" in xs),big_int_of_string "32882522869213656624276094497285870183894998108378607489495788390526642638035",big_int_of_string "100575769408947730168040492926541523978157437522189545787100160949082651363260",0,true);
         (big_int_of_string "87450116538127586239796563389215668471995222546565281514229168230730023669761",(let (_,xs) = pfgaddrstr_addr "PrMqyZ13L7Y9wdAzxGsCRBfvLkZcnqR5LAo" in xs),big_int_of_string "55199235061143706378644920190695391646300801099032165780183011431169532470288",big_int_of_string "92622478562182109051973562623560982696657751078733025560748081159380041308161",1,true);
         (big_int_of_string "44122550447487199865342132110745123590525014864958199941005211029681121017493",(let (_,xs) = pfgaddrstr_addr "PrHZ5bYm6poHujJdWfV3b77aWP3Jb68Qc6i" in xs),big_int_of_string "40271406880682732247444628769713893531058849574338422630125286321665234661686",big_int_of_string "12871451914487612275123833586446365672357570960242360286785640784861472132569",1,true);
         (big_int_of_string "81266679486896495875594878789743300929250153030978830058143421082191179580455",(let (_,xs) = pfgaddrstr_addr "PrEyDEQiRGHr3J6YT9vwgs2RAoLHWnXwbYJ" in xs),big_int_of_string "50049683938425286710377305049092387162947997626100626886804637347022397436847",big_int_of_string "50829597058501559345260627235586882116258433529915173264412225189340928582370",0,true);
         (big_int_of_string "70201616512737405020263091810135428054200204617831642508478895726986811202945",(let (_,xs) = pfgaddrstr_addr "PrFU5CTPTBmz8MQfd2JQyEijp2uQ9hcT7Bp" in xs),big_int_of_string "61140616715183365765018522155931073203610814369824275582442328091098547565645",big_int_of_string "33012639437665618989838849621513548320829898345711447119742857185200636876934",0,true);
         (big_int_of_string "19062001824281253135496054959612265023860571880224097714988303441342551983391",(let (_,xs) = pfgaddrstr_addr "PrEyDEQiRGHr3J6YT9vwgs2RAoLHWnXwbYJ" in xs),big_int_of_string "80029047212175518067948577618180151019663667156166086895889154630618233414115",big_int_of_string "69310172236426638219456395720495057870303988586036038677028902605464714963940",0,true);
         (big_int_of_string "26765059332394090524171033314060317905963733081685187415837186528112524117332",(let (_,xs) = pfgaddrstr_addr "Pr4vpXcEXpj31uTbRoGUa2JY7Zk6N8MrUTa" in xs),big_int_of_string "8814366075770868777353285811927367865419717563664370363720014280204595748284",big_int_of_string "9240837682657070329882959709912891082404930902663191790555181867623890234003",1,true);
         (big_int_of_string "59371002772325380382854665737493685375985627465357064693137649860028766664635",(let (_,xs) = pfgaddrstr_addr "Pr3t1kFhiAKVTDwoBAfo5eg9gpvusz8La6w" in xs),big_int_of_string "78955951789123481611124245232035495959979873302739647055434834898216627375082",big_int_of_string "25684451977630002330870767703539779211050264639078352021246718554155101552451",1,false);
         (big_int_of_string "93644464319180185274793781032639590692715212688674110777399775076215472115138",(let (_,xs) = pfgaddrstr_addr "PrNxyCVK9MBrHViWu65SQyqDB3yayoiK1QD" in xs),big_int_of_string "53057015231064074800967374304273865874216320091462398842971893199253250542249",big_int_of_string "78931192714705080504662466338955870971754357857655754869442422933918452540509",0,false);
         (big_int_of_string "33956093044644714114369873210784869026439077399238910935184288537094746912601",(let (_,xs) = pfgaddrstr_addr "PrGmHHtA96sWrQWnXMxTtFm89S51xtjheeF" in xs),big_int_of_string "105965366070645737957117647039860698344269077668242445389082510908368394330472",big_int_of_string "73954436527537687372618600262611371572841309974745472135097104639222613618242",1,true);
         (big_int_of_string "13732087914929791529404149304837919899895200661617594448793085745231006426832",(let (_,xs) = pfgaddrstr_addr "PrFe4cCePjAZTosVspvyZ8XkBzb8TrxVvkz" in xs),big_int_of_string "60307212785174945433873428245075182725512257590757221552469385469941646857560",big_int_of_string "25507845735797279734227293914402065696947628284658721147023017950203192488667",1,true);
         (big_int_of_string "95245613540275579965787670528794052431523650432814007056943667198039585136714",(let (_,xs) = pfgaddrstr_addr "PrHZ5bYm6poHujJdWfV3b77aWP3Jb68Qc6i" in xs),big_int_of_string "115593519990682585160316441891444387820802909872538915214247494883081735412951",big_int_of_string "83166258530702831015922730581298023955939873750218717567209640413347379173588",1,true);
         (big_int_of_string "114066696960042106683717540770017481339665926579571774610533286778285626587696",(let (_,xs) = pfgaddrstr_addr "Pr7eRjXbtL5pdYvJmJ7vMJ4B2NgJiMhaAxD" in xs),big_int_of_string "108247603610846297857391424930371866753800963013207110571851461052555879398098",big_int_of_string "73451730685677363704440871023588418589498193726819954218811764694469403959428",1,false);
         (big_int_of_string "34872407083938933048213322423127676379512763292432630459809960354468714127315",(let (_,xs) = pfgaddrstr_addr "PrQJRSjhQmknVaUywtrKeEVUBrpQsLxHDRX" in xs),big_int_of_string "65571289224887607237291349847132112891919862665232855554403738298370354602225",big_int_of_string "96141805327652043305650191079035428178711069983314558089903093442204122670193",1,true);
         (big_int_of_string "100116718885209772006321943256840028631768022237794997987499840047520402115883",(let (_,xs) = pfgaddrstr_addr "Pr71bGuF8PkJXXaFdief3HpGbKqd8jbNFA6" in xs),big_int_of_string "92592154149688542434815688285513590113198889734656115423572440367043246899702",big_int_of_string "34171686310946942015762666516461268465034211481277876331094366973464626510546",1,false);
         (big_int_of_string "86794443624172806131123300700648574205905834594274743804672719050651709741688",(let (_,xs) = pfgaddrstr_addr "PrRWBP9rmU3LXsieMUBGVFYKRVGkCLoSQKD" in xs),big_int_of_string "53754225549597869058210288395577702278639437159068455992087232215006930344686",big_int_of_string "114157936115390578140651194532395808478300809207820848447589698707063884244262",0,true);
         (big_int_of_string "41807808043895383406553127533940718808783157892173629286672768929632900866869",(let (_,xs) = pfgaddrstr_addr "PrDb6t1rDYxERitujasKPsw3FFanVM2H5Jf" in xs),big_int_of_string "92551664694882080054367696991100487886506700811824625566191957257947357841251",big_int_of_string "87161974294111465932109518401153198730698724009208693891976710734651184636981",0,true);
         (big_int_of_string "20806861403466846404421955009012082295879682325574903661946391535492816424903",(let (_,xs) = pfgaddrstr_addr "PrFLNYab8mYagu8bVuyjE5VCxgUT9GKi7KX" in xs),big_int_of_string "81468603165012683209639521959504416501675763985640021272672607517378211574873",big_int_of_string "33558943203517788096118636809886857265286523084417025024846843114851932854372",1,true);
         (big_int_of_string "79555533595989921482979521935806806749515291680724569776169014161406678866068",(let (_,xs) = pfgaddrstr_addr "PrBaPQupTuySrngh5XqwRRVXeNfLwKJk79T" in xs),big_int_of_string "43621759781539806064839787419855667906503155629655215804367498543944101180381",big_int_of_string "75975692224561864306509009295195873295261456990530933635669170143575669085339",0,false);
         (big_int_of_string "70672965069125823881586397654200775125677094999417292791361262823691410995891",(let (_,xs) = pfgaddrstr_addr "PrLo8HVMhmjtoJtddqSY6fkqKrqHqmaGbaM" in xs),big_int_of_string "103824491049264494842479554623281976410365632428361976377271555781049128713960",big_int_of_string "67692281832059680517393859320393639537067464655875393298940257889894259000321",1,false);
         (big_int_of_string "5342419863936718410629711659848184134891169849683192462574136066645601598472",(let (_,xs) = pfgaddrstr_addr "PrEywkN6yWvvfpp5tmktpLHEPJga7XAgidD" in xs),big_int_of_string "39999254233911207494323302261792047022836613655567796098011691784455836659490",big_int_of_string "85689877546302197702699739933067218127748056043727293332734452368365313304510",1,true);
         (big_int_of_string "70199021891045831541326891463885461992024355013810783997313736175481526166921",(let (_,xs) = pfgaddrstr_addr "PrECKoqgAAaPW55txcyQYcBkaWfDNYqRfHB" in xs),big_int_of_string "101674820665341877665846323708230393006258107053500828213415651150965489636735",big_int_of_string "32134209748068747950808284202290014749968126503391613529907058331598662098314",0,true);
         (big_int_of_string "76056068042364332511776775539298117446401342547667242317194894323922622241080",(let (_,xs) = pfgaddrstr_addr "Pr6UX7vhhUnJM1xYgsoAfqNfP7tG3mkx93x" in xs),big_int_of_string "70686832360504163542943362837102667335029860662040070151475206057382486560595",big_int_of_string "14188402539232734565801073815726860872247077777958185606965497961295456322109",1,true);
         (big_int_of_string "6389092667002797921809538066966101231144032154035160986416368219924332812617",(let (_,xs) = pfgaddrstr_addr "PrBJNbhbrZT3ufa45YvNc9TKQdDQuF6rRu3" in xs),big_int_of_string "69561073434261546708086616370916491627777036557685452405306566816475864507240",big_int_of_string "109123219905426905005740984653082341856359220574988104446021118667661660440056",1,true);
         (big_int_of_string "72984138439627557876193618608726041236354671939438767067742885151003900563745",(let (_,xs) = pfgaddrstr_addr "PrHLHALE6YFRb42K8kxkwnk8xPZ1qTp8K13" in xs),big_int_of_string "92791867472707199636255343326293567830033752193030813765877485674049140250603",big_int_of_string "75662930207950186461766088744887519995561484410973954539084619723088726144116",0,true);
         (big_int_of_string "246061591238077180779866696549597069610286452507125845775284743317149437959",(let (_,xs) = pfgaddrstr_addr "PrL7N62RHdNUvLQt5sMDsC53xr7WvXVDQ3U" in xs),big_int_of_string "24122571351369208461040483804499471754559885088133001780468468572359271685436",big_int_of_string "107665619798952429113395268805826772973802441201603767803251626085367357235670",1,false);
         (big_int_of_string "112979752695945101815882636890241197256558198370335589498278027855851942513546",(let (_,xs) = pfgaddrstr_addr "PrA1P17YqujAJamfXDKbQEEmdFeZNP5mU5D" in xs),big_int_of_string "27201882629158843696178416800421721311563228607271735838759942722392067253866",big_int_of_string "35143274432282627826009732032174133991039467402266870034927222280409916124528",0,true);
         (big_int_of_string "113247480415226870020625082127702862902185679870863721213811180973837615922356",(let (_,xs) = pfgaddrstr_addr "Pr6aw5ciaqed3a1qScvfLbpWA19HsCoahiu" in xs),big_int_of_string "56469806480654869421525230031144336672974955672084774143798765077434675089670",big_int_of_string "104784135195863133301459891797347051960252095681653433161337392402502548588357",1,false);
         (big_int_of_string "78085205666427914501987627812495680786703935404141275210175373425295045077928",(let (_,xs) = pfgaddrstr_addr "PrLHA5nf66GG62ZeMowiHVYYiMTSq2Z194h" in xs),big_int_of_string "46850070869079902688790578982703316048485436019674809865155135746732566950301",big_int_of_string "2446177594058641502041080491711342702832267160607621623227841184098310853822",1,true);
         (big_int_of_string "75374685082912805773387669377859989750927303586282607142187569138626248260836",(let (_,xs) = pfgaddrstr_addr "PrHDC2tozq3EqfkPjqpN6AcJzsD7Q4vRtLE" in xs),big_int_of_string "32736969781095257108230662685835332329620817898851821713876601749411922257965",big_int_of_string "14375529613801782695999545703591053631251443218198052156826945420974910146166",1,true);
         (big_int_of_string "99293012279350652353160252715967871911171829917746501805765012020095764380111",(let (_,xs) = pfgaddrstr_addr "PrDdDnqpd2VNvofmsBjrgvdj2em6j35X7QP" in xs),big_int_of_string "98772014813004334701452550186903872109675414370118103242323904937934827176211",big_int_of_string "81597115762083810595833172395011998409320224700967087438243471983423993704882",1,true);
         (big_int_of_string "108307842504193490873045705876634127799359575161022718087204759697389082909785",(let (_,xs) = pfgaddrstr_addr "Pr97sji7NMpbVDpeMbGoNKNYyMkkbj2ho7Q" in xs),big_int_of_string "79591888664570151398225705020922332175635720725472080460608507236844166917888",big_int_of_string "56600059999755031134969299549933011051998229647702630671834122039265687908141",0,false);
         (big_int_of_string "36663433654316715754851730507987943228563432006087770954235825016163893199773",(let (_,xs) = pfgaddrstr_addr "Pr8TVtSJ2vp1CYfghEQspFXZELXGkySmukA" in xs),big_int_of_string "93625212333722561943976950575226149831143185592898064266300969393283989983287",big_int_of_string "104081337763327771972034004639118972637135966089238705297361601840490589629496",0,true);
         (big_int_of_string "17199197650275081568624087645846736725995626437448685869539154581485264571915",(let (_,xs) = pfgaddrstr_addr "PrPCqB2i175j6xUszRwqHMLTCTUtBknS4KC" in xs),big_int_of_string "64272578708045129576661363036562199323376003172961201530015383902842483348757",big_int_of_string "61158467169013300614594375611683064976181674552985127936269574424526971025706",1,true);
         (big_int_of_string "19513661576031212006438126991741388421995828263040800611934544002971287744239",(let (_,xs) = pfgaddrstr_addr "Pr7YYpPXkoVmFcboc4Rx7Ys4d7LDWnw8FJH" in xs),big_int_of_string "106225810214439181178734761250875907349402329995081623383490329611166242819871",big_int_of_string "60419302454768326125270529745875505874341576525303916020850087036610325637791",1,true);
         (big_int_of_string "86929535872138543964779396433629277497984157071588654050889852835243683700758",(let (_,xs) = pfgaddrstr_addr "Pr3N6mCj7iZWjAFPYJFmAcfq4xUMjwx68Ee" in xs),big_int_of_string "26753410138796142651939791799646718711564911949405882401751752916571386277748",big_int_of_string "5191691621231476673653751902980885116589379830459256170474546429556297371852",1,true);
         (big_int_of_string "23459028207189890132727325789250828107530216632004396003605638980856042670728",(let (_,xs) = pfgaddrstr_addr "PrPZRuLcEmijyJTXwNJxqfB2BGFCyBpJuE1" in xs),big_int_of_string "48970394442108890440108852274783888235630731769723677111953565050724218817358",big_int_of_string "112832267385762595099812880430667401860412006563995532405724654671798606403233",0,true);
         (big_int_of_string "105391544667565878990851541468111754011474325285761998175943976536794539501030",(let (_,xs) = pfgaddrstr_addr "PrD2XsiPMAXuGjFkJnQq1cQ51ebGpA6uA2x" in xs),big_int_of_string "5602498606639504302984375524106994363004984062850625321949817861425166030677",big_int_of_string "95561404555293425233584578651782253003111036665143699024191327984414501027116",0,false);
         (big_int_of_string "4976327831036437974746278790893675450425965604968598771801401302006827536518",(let (_,xs) = pfgaddrstr_addr "PrFsEyVhLAypg2cqah16dMSd8MoYR5YyQjP" in xs),big_int_of_string "54994923606273232860066914359145976904323034129143663487010345054522685329259",big_int_of_string "41449578649008856412849840487878234958237913819536317252261866994272812661234",0,true);
         (big_int_of_string "13295043719613747913120113695629267937457687438006858729396851001244239790176",(let (_,xs) = pfgaddrstr_addr "Pr4vJBbsdCHEULmUnfSBy6NqYd6j7j3hQBm" in xs),big_int_of_string "50462081069810129441895339322480338835217426970345091411913583976173758065065",big_int_of_string "52200776778519544895366386058038970560629601012298304555783031944932400731278",1,true);
         (big_int_of_string "23165984864275274080345436796706092583609033773800574266378529666328504108020",(let (_,xs) = pfgaddrstr_addr "PrMVs7TxPGPz5uU4GdJZQ2TmDBaUjokkkoZ" in xs),big_int_of_string "29577084910681553320864338354324078931725930735425505716483504803774567426468",big_int_of_string "69407249064808252498807338709679560344855057332118484852171497852859292850729",1,true);
         (big_int_of_string "3434199086825088869918452427770860968993600369192283012372617056281782955883",(let (_,xs) = pfgaddrstr_addr "PrF56SRe5q51GP9MDadFWgDKaSxe3jrfjBf" in xs),big_int_of_string "48235405024329853274372961837327824053065032569361085218766505606692535368211",big_int_of_string "45389643690205364356000729185077635485661343571951554633153400625025364655488",0,false);
         (big_int_of_string "1461548097731903373873674300284787274896815773240555824346473155629282141245",(let (_,xs) = pfgaddrstr_addr "Pr5ZoUgo413rzzgeV7XcLmFpMJ65Spaiqks" in xs),big_int_of_string "77475183616556445172298965489214288584943556383587905927543480199672085457646",big_int_of_string "92041139681664568147051513687101617404083224032573435929963320563255467559157",0,true);
         (big_int_of_string "78990501364641585060838826404664929205452369969675001756696967820286293190247",(let (_,xs) = pfgaddrstr_addr "PrQco3skydJDZtfaJVbpF5sJaeTrhHWV2vC" in xs),big_int_of_string "5578089881612120604897574007526279018365656557234139041807650571473649161504",big_int_of_string "77886442951637364659982036390565259741243991037553848257806955047587769930010",1,true);
         (big_int_of_string "34137174147557077419257331786267350959099968234412257726621874928762411697870",(let (_,xs) = pfgaddrstr_addr "Pr6zkqtAhZbFw6BvuB5BAPGiKbiaezTP4pv" in xs),big_int_of_string "12215862912148549237757415195791001577484337044475749018175371912901769894801",big_int_of_string "67779082260580856408706467069037263859840308241734692503830779261387146757661",1,true);
         (big_int_of_string "37529181915331755147482935146865213396811548330129230189033008448017073833174",(let (_,xs) = pfgaddrstr_addr "PrH6dv3w2iWpnfRFLPuPC1NitgMTSaqJK2L" in xs),big_int_of_string "34619476862784880892508432586015151671405913419479600299960699669559503774840",big_int_of_string "57240846304468738371738602506887285410790645567683689402436295142234356091903",1,true);
         (big_int_of_string "54224381111392269181585328607437470708602756465936175733004884825356531162603",(let (_,xs) = pfgaddrstr_addr "PrDALjmVHjtdbJtQVnGPhMQhtHF8urUEhzJ" in xs),big_int_of_string "101250757350360446571746207102547834900523193419686097423571475125341574806212",big_int_of_string "44230840251803675954736091643344603858069471001287641358639334884119708895467",0,true);
         (big_int_of_string "12177070847165779891913451390065646321156824401132752018822385022106542963262",(let (_,xs) = pfgaddrstr_addr "PrEzeYBPCThuA75pVJ8ubAatTundDDD87rY" in xs),big_int_of_string "93355528033853090157171137737151849404376192674225762521490345071624278869198",big_int_of_string "8079677363972193934879810353747113239637015155712734846796351079124059930698",0,true);
         (big_int_of_string "49638520963990750429633377176275665055903885171832851789942732343871958022226",(let (_,xs) = pfgaddrstr_addr "PrKGpmsqQREsDZhWs7bhQYiaxzJ3eWvuwCL" in xs),big_int_of_string "26064057743098672582567410876517306408053497192636223934391146154888553720833",big_int_of_string "83210731161235383562298596052633970425708705830126092537050852410958034457561",1,true);
         (big_int_of_string "68689369249245599637758214756527469235499024593199407556722582460303370835931",(let (_,xs) = pfgaddrstr_addr "Pr8mLBHhp98rSj44AhT146c5w6tL3bn9QgG" in xs),big_int_of_string "25356446045129348189759716333749532124335795469545872295852931289142125364892",big_int_of_string "34299398805095898065034349474900087125164016730387622131646769237732457429979",1,true);
         (big_int_of_string "82588607938427862528889137885440351054065888327307506174712933802320571884981",(let (_,xs) = pfgaddrstr_addr "PrQVW2ibeNZ1aiRZy4uqwzt47UiqLyYPHN7" in xs),big_int_of_string "3422542868775059070282840611614614452189501528181346593644402156164148234606",big_int_of_string "82194733274866081629107206616299888925079912885401653446711389248402918551656",1,true);
         (big_int_of_string "906150012377140731835779773794168338450228140363999779851732053831391329777",(let (_,xs) = pfgaddrstr_addr "Pr7VGJ8vA6zBNCERv9tbE3umJjZ2qKVVBL3" in xs),big_int_of_string "105317714716730803982021149042316772758660108105929776614133321277598574921880",big_int_of_string "76207053720313713767208533059121651147525334970708084966114541041112534619751",0,true);
         (big_int_of_string "35447311806510948671336219699640312695821321229860104596134327803101121544915",(let (_,xs) = pfgaddrstr_addr "PrK64YgN8tTjJNFLLkxSYBr5opjVBYbMaZV" in xs),big_int_of_string "108743038940157051254995171408958672552147742246075286213514354194000176361507",big_int_of_string "91350861727398997778627600570544672120500437481690393709627179492169405532278",1,true);
         (big_int_of_string "7817827695689981402251239253222939246451523688603060720601499126133022777770",(let (_,xs) = pfgaddrstr_addr "PrCGeoCndutnQoSSzCYvkiZHk5w8fMvZoHu" in xs),big_int_of_string "67104671224257243264525045603377829229852275419591726832831117392354133803372",big_int_of_string "28054586560237146372076869971613151988339658332011531621425116110518713729915",1,true);
         (big_int_of_string "14623663930472059627338185836899293147621829862200793208868139955959342170287",(let (_,xs) = pfgaddrstr_addr "Pr9SVUZbjEQsrXHpkHJtTrmgpLnW7WwEmS8" in xs),big_int_of_string "25736895125329029135610751359289753516032149376933224907075670894082839614273",big_int_of_string "37116299627937630608810264499465714721441527820213216194288045645925858130853",1,true);
         (big_int_of_string "72601536981239127204486389412030270471358883171052370833677166679220010339991",(let (_,xs) = pfgaddrstr_addr "PrFrXb7kVJ644vThoNaMAygBCWuxqpcTaZH" in xs),big_int_of_string "59861714635790755436375547219462849456543982915064209929874714385804981227199",big_int_of_string "88624088093075233312367328505243365624744415490365460356410400135965365960573",0,true);
         (big_int_of_string "66677248750488309519125943341227447380163307819172573004274935790534772898150",(let (_,xs) = pfgaddrstr_addr "PrG2fY6pgtysri6KLScNwvbVZb9tXXewPuc" in xs),big_int_of_string "38042329955402777816550383584690164142913859226170419120439240452438895759467",big_int_of_string "40355318770424079823547221629550813078144996275398291074146500514730892723336",0,false);
         (big_int_of_string "18797153456520908231536844988443703932762228478544777026350784993685372641582",(let (_,xs) = pfgaddrstr_addr "PrMSY3HYnZ21QvKRifAF7BZAe1TEWTcYkUc" in xs),big_int_of_string "87973065817756790597675450719427066835949306225232181814971055267379466907013",big_int_of_string "57465337732869178492417031071089199372467824926949768146411782017729436035736",1,true);
         (big_int_of_string "105950558581671647251301782308739957126076265353824976768894276172748070870157",(let (_,xs) = pfgaddrstr_addr "Pr6hGv3H7nsfv9Aa1RoMk5KmFexSarS1e9v" in xs),big_int_of_string "36104041074683098674316446658582716251897969936464257624846395631996668586762",big_int_of_string "104925032491690679145860196057786697538025453338106833899734519692941429596113",1,true);
         (big_int_of_string "29014170003292753239102073990157357941110696294028154917863297132426041240856",(let (_,xs) = pfgaddrstr_addr "PrDUHeH5juNGYY29fcgEHrSpVTjRMS3GtJ3" in xs),big_int_of_string "71356446197129610063503955051154473717602006928852237538763367017486185630138",big_int_of_string "48345516684604136501235755317838560739365686281509866100982248523517778926377",1,true);
         (big_int_of_string "82515607382996241940639445089274867154541737582978316286297762490931064680306",(let (_,xs) = pfgaddrstr_addr "PrQaYjPzehgjChmWs1XowXCzn2yAVE8B5C6" in xs),big_int_of_string "51971753687017182435468353198093097889448117671925288608497116578293315373823",big_int_of_string "103124833592269408228486832318408480168202484537466996603522265790735300199685",0,true);
         (big_int_of_string "39619508448360026996065095600810091368527402980933164409951350619319449864187",(let (_,xs) = pfgaddrstr_addr "PrEnQfzA6jdcCHobK8fTJL45PfAgrhnKLiQ" in xs),big_int_of_string "79004488301598290202039778391917843845620670442668663367031212474814032421199",big_int_of_string "87906340657759307804585148861146921713802038609792718567358068114696959486225",0,true);
         (big_int_of_string "36220499738132308061515363756109573967208691519028420635270637898135601546568",(let (_,xs) = pfgaddrstr_addr "Pr8Dh4CBjRXTHTGyb8ogmL1SXdKjqG6ryJW" in xs),big_int_of_string "27319693189174915163982440622276173397680742252795754557095102062077728669118",big_int_of_string "7818639388573790983767169496532608336669449283288092299283346030393619713016",1,true);
         (big_int_of_string "111133700590887201120009881445147494332577674090741561678154495090480973118868",(let (_,xs) = pfgaddrstr_addr "PrRgGSuKD7YrV8aZfsJDBv8HP9chji1ft8v" in xs),big_int_of_string "66154246183832529722175676368945646937435697308998048764705050455051296283328",big_int_of_string "75305822553109679685759065532180401892546408322973553293369580042272601541752",1,true);
         (big_int_of_string "87350086028931236515670360540008666148256960771519859944139042288461379388894",(let (_,xs) = pfgaddrstr_addr "PrQP6TDZgTtsdkbEHU6UhvKERYcBrA8K7ak" in xs),big_int_of_string "29748943722540436346070886284165528167316421349215848613903962389284039687621",big_int_of_string "40093568343175028582142669527473948103407181694360465315755838488249619814034",1,true);
         (big_int_of_string "104711379263281263467859459975277352701500543506774296875557464059458836807032",(let (_,xs) = pfgaddrstr_addr "PrHgW5gpvR91pVdxQxZsQqBuCndFZcAL5Lc" in xs),big_int_of_string "20717230484827050524224894947607961396909573323579747779019290332620372991892",big_int_of_string "11908743292433909030842334367204376548439461965547766752838572709263792049789",1,true);
         (big_int_of_string "103019069957933565171377588397433433802229446309263301873063248721245667741555",(let (_,xs) = pfgaddrstr_addr "Pr5vkjBjqNJr5MDDU6NWVS9kcwjH2U3gq7g" in xs),big_int_of_string "36170379664194776978197874359828641201212753492314783891882704617549356723257",big_int_of_string "100242447255228210217967697249500088049522063045571006072311230567334393867185",1,true);
         (big_int_of_string "103684849565925515669385577716042810877263545759612217324816720550185106182773",(let (_,xs) = pfgaddrstr_addr "PrLgfruyuoCkgpoPBPT3gTLccqeUpPGRuuK" in xs),big_int_of_string "91603695690917851483728388688945076047734462002684883345566597456701935834211",big_int_of_string "99069457354694211416587830286678475747406010678517911049177234700869045334830",1,true);
         (big_int_of_string "4455826725166052533252303367880003715637170668327154120246707585379164698619",(let (_,xs) = pfgaddrstr_addr "PrMuhBCmC1RahziVBs1WwkCrKQxGQiQHtSV" in xs),big_int_of_string "101691607330747007730206976807715105251777412870198251050145169420769598101239",big_int_of_string "110329227129122126412180106396541725401222166640871367852924401581577142968514",0,true);
         (big_int_of_string "41719338947589515312318721263025743281724792709805482694350234642489399056461",(let (_,xs) = pfgaddrstr_addr "PrM9ixa2xFhrbQTkr6Ct3Le9EQCHacWyjoc" in xs),big_int_of_string "103800663662496355379269421057111330813183128961179133556583203875954660277495",big_int_of_string "11878235257879400441667295807028211134355719203696426190856281150237063645687",1,true);
         (big_int_of_string "72048874365911295979876070839107028886387096964692411711428390417091776113951",(let (_,xs) = pfgaddrstr_addr "PrDqzd9gt1kgWV4xjUwUnKbReR8dZrt2fCC" in xs),big_int_of_string "4005523250049697009253640345953121972045652172245379726194596962437001202819",big_int_of_string "67402994559910911677911943768718441933950932217662307534183539330208185520263",0,true);
         (big_int_of_string "55741791289612436265904838543286977654915383589056729300872546212259626760202",(let (_,xs) = pfgaddrstr_addr "PrGSt6YCH7TQkgyn8B9iGKpn5ctJVQnjiHf" in xs),big_int_of_string "87254591259590959163314684047626320747319943936153572333719945004176974571106",big_int_of_string "13836848968566771839657452157184787727322788556316234495992153031114871705414",0,true);
         (big_int_of_string "49555961894239538085182842026884971598037946042120873557331456405705215753659",(let (_,xs) = pfgaddrstr_addr "PrCFkcncX1HZCzTbRrHmUyczewUafuErYxV" in xs),big_int_of_string "101713489790069024321841994788304179840679640529940894869874780948922099396597",big_int_of_string "56917829419364052850384429452008060854930737168218201653752613562865669559446",0,true);
         (big_int_of_string "42792397560948727302608062720563110638347535345997682282818230701030399113355",(let (_,xs) = pfgaddrstr_addr "Pr7nzGYh8nGGLue1czrnFrCPxyL2xieDGaS" in xs),big_int_of_string "44341260207524026147048550049486122778195398535985563126506010789039838018803",big_int_of_string "102940879035548620081911157800649712565798832898128215995490041721352656012705",1,true);
         (big_int_of_string "89369793884272311404419648533880636451323029452132747535704559709789464986177",(let (_,xs) = pfgaddrstr_addr "PrLVNxP7s4vuTDB9zDscWaYBhgmDsdNr9FL" in xs),big_int_of_string "60957856569061172577548063562991513811838763725500902218584354416274759803915",big_int_of_string "16468123574600318460463246063803919236813158233830928000179424265481219959070",1,true);
         (big_int_of_string "41540002911168071397701160520105949827896782004465683521393565962152346670925",(let (_,xs) = pfgaddrstr_addr "Pr93fwVdxC9Zugh6X4Z3fQsZo4xmCGAcjLB" in xs),big_int_of_string "1390347579544793529694361365088392597571223948971610003341734761245333178747",big_int_of_string "80613413389953735745186945533605136452541669235502485601881301715683341309642",0,false);
         (big_int_of_string "6915836558368859589333345796200574645259791279757831700701980384497413052834",(let (_,xs) = pfgaddrstr_addr "PrPmCdwreQ78XZiSipsZg5NSoZhupXAwfLr" in xs),big_int_of_string "34656926416220716121342178735339276474472696480700517149201358364505253171256",big_int_of_string "7277415392181446444810006248403199708217581045136629703963437877153594402599",1,true);
         (big_int_of_string "44781390513337303008158756217697998258825861187863025311332216062357111903671",(let (_,xs) = pfgaddrstr_addr "PrKMgPuSyuN2p3C5VAqgoU3exckQiX7enuQ" in xs),big_int_of_string "84204551915112433772256045965920686952202101447340884200008407315573742293899",big_int_of_string "113607299198848956209065418453818148192883410355406669557315895695652140572650",0,true);
        ]
      in
      let tm = Unix.gettimeofday() in
      List.iter
        (fun (e,alpha,r,s,recid,fcomp) ->
          if not (verify_p2pkhaddr_signat e alpha (r,s) recid fcomp) then
            raise (Failure "error"))
        dl;
      Printf.fprintf oc "time: %f\n" (Unix.gettimeofday() -. tm));
  ac "blockchain" "blockchain [<n>]" "Print the blockchain up to the most recent <n> blocks, with a default of 1000 blocks."
    (fun oc al ->
      match al with
      | [] -> Commands.pblockchain oc (get_bestblock_print_warnings oc) 1000
      | [n] ->
         let n = int_of_string n in
         Commands.pblockchain oc (get_bestblock_print_warnings oc) n;
      | _ -> raise BadCommandForm);
  ac "reprocessblockchain" "reprocessblockchain [<n>]" "reprocess the block chain from the block at height n up to the current block, where by default n=1 (the genesis block)"
    (fun oc al ->
      match al with
      | [] -> Commands.reprocess_blockchain oc (get_bestblock_print_warnings oc) 1
      | [n] -> let n = int_of_string n in Commands.reprocess_blockchain oc (get_bestblock_print_warnings oc) n
      | _ -> raise BadCommandForm);
  ac "reprocessblock" "reprocessblock <blockid> <ltcblock> <ltcburntx>" "Manually reprocess a given block.\nThis is useful if either -ltcoffline is set or if part of the current ledger seems to be missing from the local node.\nIf the current node has the full ledger from before the block,\nthen processing the block should ensure the node has the resulting full ledger."
    (fun oc al ->
      match al with
      | [h;lbk;ltx] ->
         let h = hexstring_hashval h in
         let lbk = hexstring_hashval lbk in
         let ltx = hexstring_hashval ltx in
         let lh = hashpair lbk ltx in
         Db_validheadervals.dbdelete lh;
         Db_validblockvals.dbdelete lh;
         DbInvalidatedBlocks.dbdelete h;
         reprocessblock oc h lbk ltx
      | _ -> raise (Failure "reprocessblock <blockid> <ltcblock> <ltcburntx>"));;

let rec parse_command_r l i n =
  if i < n then
    let j = ref i in
    while !j < n && l.[!j] = ' ' do
      incr j
    done;
    let b = Buffer.create 20 in
    while !j < n && not (List.mem l.[!j] [' ';'"';'\'']) do
      Buffer.add_char b l.[!j];
      incr j
    done;
    let a = Buffer.contents b in
    let c d = if a = "" then d else a::d in
    if !j < n && l.[!j] = '"' then
      c (parse_command_r_q l (!j+1) n)
    else if !j < n && l.[!j] = '\'' then
      c (parse_command_r_sq l (!j+1) n)
    else
      c (parse_command_r l (!j+1) n)
  else
    []
and parse_command_r_q l i n =
  let b = Buffer.create 20 in
  let j = ref i in
  while !j < n && not (l.[!j] = '"') do
    Buffer.add_char b l.[!j];
    incr j
  done;
  if !j < n then
    Buffer.contents b::parse_command_r l (!j+1) n
  else
    raise (Failure("missing \""))
and parse_command_r_sq l i n =
  let b = Buffer.create 20 in
  let j = ref i in
  while !j < n && not (l.[!j] = '\'') do
    Buffer.add_char b l.[!j];
    incr j
  done;
  if !j < n then
    Buffer.contents b::parse_command_r l (!j+1) n
  else
    raise (Failure("missing '"))

let parse_command l =
  let ll = parse_command_r l 0 (String.length l) in
  match ll with
  | [] -> raise Exit (*** empty command, silently ignore ***)
  | (c::al) -> (c,al)

let do_command oc l =
  let (c,al) = parse_command l in
  if c = "help" then
    begin
      match al with
      | [a] ->
	  begin
	    try
	      let (h,longhelp,_) = Hashtbl.find commandh a in
	      Printf.fprintf oc "%s\n" h;
	      if not (longhelp = "") then Printf.fprintf oc "%s\n" longhelp
	    with Not_found ->
	      Printf.fprintf oc "Unknown command %s\n" a;
	  end
      | _ ->
	  Printf.fprintf oc "Available Commands:\n";
	  List.iter
	    (fun c -> Printf.fprintf oc "%s\n" c)
	    !sortedcommands;
	  Printf.fprintf oc "\nFor more specific information: help <command>\n";
    end
  else
    try
      let (_,_,f) = Hashtbl.find commandh c in
      try
        f oc al;
        flush oc
      with Not_found -> raise (Failure "Not_found raised by command")
    with Not_found ->
      Printf.fprintf oc "Unknown command %s\n" c;;

let init_ledger () =
  let inith = !genesisledgerroot in
  if not (DbCTreeAtm.dbexists inith) then
    begin
      let hfthy = Checking.hfthy in
      let hfthyid = Checking.hfthyid in
      log_string (Printf.sprintf "Creating initial hf theory with id %s\n" (hashval_hexstring hfthyid));
      DbTheory.dbput hfthyid hfthy;
      let hfalpha = hashval_pub_addr hfthyid in
      let nonce = zerohashval in
      let burnpayaddr = (false,Be160.of_int32p5 (0l,0l,0l,0l,0l)) in
      let inittauout = ref [(hfalpha,(None,TheoryPublication(burnpayaddr,nonce,Checking.hfthyspec)))] in
      let (_,hfaxhs) = Checking.hfthy in
      List.iter
        (fun axh ->
          inittauout := (hashval_term_addr axh,(Some(burnpayaddr,0L,false),OwnsProp(axh,burnpayaddr,Some(0L))))::!inittauout; (* ownership of pure prop of hf ax; free to use forever *)
          let axhthyid = hashtag (hashopair2 (Some(hfthyid)) axh) 33l in
          inittauout := (hashval_term_addr axhthyid,(Some(burnpayaddr,0L,false),OwnsProp(axhthyid,burnpayaddr,Some(0L))))::!inittauout) (* ownership of theory prop of hf ax; free to use forever *)
        hfaxhs;
      flush stdout;
      let inittau : tx = ([],!inittauout) in
      match tx_octree_trans false false 0L inittau None with
      | None -> Printf.printf "Something is terribly wrong.\n"; flush stdout; !exitfn 1
      | Some(initc) ->
         let inith2 = save_ctree_atoms initc in
         if not (inith = inith2) then
           (Printf.printf "Initial ledger hash root mismatch.\nExpected %s\nFound %s\n" (hashval_hexstring inith) (hashval_hexstring inith2); flush stdout; !exitfn 1);
         match txout_update_ottree !inittauout None with
         | None -> Printf.printf "Something is terribly wrong.\n"; flush stdout; !exitfn 1
         | Some(initthytree) ->
            match ottree_hashroot (Some(initthytree)) with
            | Some(initthytreeroot) when initthytreeroot = Checking.initthytreeroot ->
               DbTheoryTree.dbput initthytreeroot (None,[hfthyid])
            | _ -> Printf.printf "Init thy tree root mismatch."; flush stdout; !exitfn 1
    end;;

let set_signal_handlers () =
(*  let generic_signal_handler str sg =
    Utils.log_string (Printf.sprintf "thread %d got signal %d (%s) - terminating\n" (Thread.id (Thread.self ())) sg str);
    !exitfn 1;
  in *)
(*  Sys.set_signal Sys.sigvtalrm Sys.Signal_ignore; (* these might make sense, but not sure *)
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
  Sys.set_signal Sys.sigprof Sys.Signal_ignore;
  Sys.set_signal Sys.sigchld Sys.Signal_ignore; *)
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle
       (fun sg ->
         Printf.printf "got sigint signal. Terminating.\n";
         !exitfn 1));
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  ();;

let initialize () =
  begin
    let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
    if !Config.testnet then
      begin
	if !Config.ltcrpcport = 9332 then Config.ltcrpcport := 19332;
        ltctestnet();
        max_target := shift_left_big_int unit_big_int 208;
        genesistarget := shift_left_big_int unit_big_int 207;
      end;
    genesisstakemod := !ltc_oldest_to_consider; (** use the oldest ltc block hash as the initial stake modifier **)
    Config.genesistimestamp := Int64.add 3600L !ltc_oldest_to_consider_time; (** genesis time is 1 hour after the oldest ltc block to consider **)
    Gc.set { (Gc.get ()) with Gc.stack_limit = !Config.gc_stack_limit; Gc.space_overhead = !Config.gc_space_overhead; };
    if Sys.file_exists (Filename.concat datadir "lock") then
      begin
	if not !Config.daemon then
	  begin
	    Printf.printf "Cannot start Proofgold. Do you already have Proofgold running? If not, remove: %s\n" (Filename.concat datadir "lock");
	    flush stdout;
	    exit 1;
	  end;
      end;
    lock datadir;
    if not !Config.daemon then (Printf.printf "Initializing the database...\n"; flush stdout);
    let dbdir = Filename.concat datadir "dbm" in
    begin
      try
        dbconfig dbdir; (*** configure the database ***)
      with
      | NoBootstrapURL ->
         if not !Config.daemon then
           (Printf.printf "Searching the ltc chain for a bootstrap URL\n"; flush stdout);
         search_ltc_bootstrap_url ();
         if !Config.bootstrapurl = "" then
           begin
             Printf.printf "No bootstrap url found.\n";
             !exitfn 1;
           end
         else
           dbconfig dbdir
    end;
    DbBlacklist.dbinit();
    DbArchived.dbinit();
    DbTheory.dbinit();
    DbTheoryTree.dbinit();
    DbSigna.dbinit();
    DbSignaTree.dbinit();
    DbAsset.dbinit();
    DbAssetIdAt.dbinit();
    DbSTx.dbinit();
    DbHConsElt.dbinit();
    DbHConsEltAt.dbinit();
    DbCTreeLeaf.dbinit();
    DbCTreeLeafAt.dbinit();
    DbCTreeAtm.dbinit();
    DbCTreeAtmAt.dbinit();
    DbCTreeElt.dbinit();
    DbCTreeEltAt.dbinit();
    DbBlockHeader.dbinit();
    DbBlockDelta.dbinit();
    DbInvalidatedBlocks.dbinit();
    DbLtcPfgStatus.dbinit();
    DbLtcBurnTx.dbinit();
    DbLtcBlock.dbinit();
    Db_outlinevals.dbinit();
    Db_validheadervals.dbinit();
    Db_validblockvals.dbinit();
    Db_outlinesucc.dbinit();
    Db_blockburns.dbinit();
    openlog(); (*** Don't open the log until the config vars are set, so if we know whether or not it's testnet. ***)
    init_ledger();
    if not !Config.daemon then (Printf.printf "Initialized.\n"; flush stdout);
    let sout = if !Config.daemon then !Utils.log else stdout in
    begin
      match !check_ledger with
      | None -> ()
      | Some(lr) ->
	  let totatoms = ref 0L in
	  let totbounties = ref 0L in
	  let rec check_asset h =
	    try
	      let a = DbAsset.dbget h in
	      match a with
	      | (_,_,_,Currency(v)) -> totatoms := Int64.add v !totatoms
	      | (_,_,_,Bounty(v)) -> totbounties := Int64.add v !totbounties
	      | _ -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: asset %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec check_hconselt h =
	    try
	      let (ah,hr) = DbHConsElt.dbget h in
	      check_asset ah;
	      match hr with
	      | Some(h,_) -> check_hconselt h
	      | None -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: hconselt %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec check_ledger_rec h =
	    try
	      let c = DbCTreeElt.dbget h in
	      check_ctree_rec c 9
	    with Not_found ->
	      Printf.fprintf sout "WARNING: ctreeelt %s is not in database\n" (hashval_hexstring h)
	  and check_ctree_rec c i =
	    match c with
	    | CHash(h) -> check_ledger_rec h
	    | CLeaf(_,NehHash(h,_)) -> check_hconselt h
	    | CLeft(c0) -> check_ctree_rec c0 (i-1)
	    | CRight(c1) -> check_ctree_rec c1 (i-1)
	    | CBin(c0,c1) ->
		check_ctree_rec c0 (i-1);
		check_ctree_rec c1 (i-1)
	    | _ ->
		Printf.fprintf sout "WARNING: unexpected non-element ctree at level %d:\n" i;
		print_ctree sout c
	  in
	  check_ledger_rec lr;
	  Printf.fprintf sout "Total Currency Assets: %Ld atoms (%s bars)\n" !totatoms (bars_of_atoms !totatoms);
	  Printf.fprintf sout "Total Bounties: %Ld atoms (%s bars)\n" !totbounties (bars_of_atoms !totbounties);
	  !exitfn 0
    end;
    begin
      match !build_extraindex with
      | None -> ()
      | Some(lr) ->
	  let rec extraindex_asset h alpha =
	    try
	      let a = DbAsset.dbget h in
	      DbAssetIdAt.dbput (assetid a) alpha
	    with Not_found ->
	      Printf.fprintf sout "WARNING: asset %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec extraindex_hconselt h alpha =
	    try
	      let (ah,hr) = DbHConsElt.dbget h in
	      DbHConsEltAt.dbput ah alpha;
	      extraindex_asset ah alpha;
	      match hr with
	      | Some(h,_) -> extraindex_hconselt h alpha
	      | None -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: hconselt %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec extraindex_ledger_rec h =
	    try
	      let c = DbCTreeElt.dbget h in
	      extraindex_ctree_rec c 9
	    with Not_found ->
	      Printf.fprintf sout "WARNING: ctreeelt %s is not in database\n" (hashval_hexstring h)
	  and extraindex_ctree_rec c i =
	    match c with
	    | CHash(h) -> extraindex_ledger_rec h
	    | CLeaf((_,beta),NehHash(h,_)) -> extraindex_hconselt h beta
	    | CLeft(c0) -> extraindex_ctree_rec c0 (i-1)
	    | CRight(c1) -> extraindex_ctree_rec c1 (i-1)
	    | CBin(c0,c1) ->
		extraindex_ctree_rec c0 (i-1);
		extraindex_ctree_rec c1 (i-1)
	    | _ ->
		Printf.fprintf sout "WARNING: unexpected non-element ctree at level %d:\n" i;
		print_ctree sout c
	  in
	  extraindex_ledger_rec lr;
	  !exitfn 0
    end;
    begin
      match !netlogreport with
      | None -> ()
      | Some([]) ->
	  Printf.fprintf sout "Expected -netlogreport <sentlogfile> [<reclogfile>*]\n";
	  !exitfn 1
      | Some(sentf::recfl) ->
	  let extra_log_info mt ms = (*** for certain types of messages, give more information ***)
	    match mt with
	    | Inv ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int32 seis !c in
		  Printf.fprintf sout "Inv msg %ld entries\n" n;
		  c := cn;
		  for j = 1 to Int32.to_int n do
		    let ((i,h),cn) = sei_prod sei_int8 sei_hashval seis !c in
		    c := cn;
		    Printf.fprintf sout "Inv %d %s\n" i (hashval_hexstring h);
		  done
		end
	    | GetHeader ->
		begin
		  let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
		  Printf.fprintf sout "GetHeader %s\n" (hashval_hexstring h)
		end
	    | GetHeaders ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
		  c := cn;
		  Printf.fprintf sout "GetHeaders requesting these %d headers:\n" n;
		  for j = 1 to n do
		    let (h,cn) = sei_hashval seis !c in
		    c := cn;
		    Printf.fprintf sout "%d. %s\n" j (hashval_hexstring h);
		  done
		end
	    | Headers ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
		  Printf.fprintf sout "Got %d Headers\n" n;
		  c := cn;
		  for j = 1 to n do
		    let (h,cn) = sei_hashval seis !c in
		    let (bh,cn) = sei_blockheader seis cn in
		    c := cn;
		    Printf.fprintf sout "%d. %s\n" j (hashval_hexstring h)
		  done
		end
	    | _ -> ()
	  in
	  Printf.fprintf sout "++++++++++++++++++++++++\nReport of all sent messages:\n";
	  let f = open_in_bin sentf in
	  begin
	    try
	      while true do
		let (tmstmp,_) = sei_int64 seic (f,None) in
		let gtm = Unix.gmtime (Int64.to_float tmstmp) in
		Printf.fprintf sout "Sending At Time: %Ld (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		let (magic,_) = sei_int32 seic (f,None) in
		if magic = 0x44616c54l then Printf.fprintf sout "Testnet message\n" else if magic = 0x44616c4dl then Printf.fprintf sout "Mainnet message\n" else Printf.fprintf sout "Bad Magic Number %08lx\n" magic;
		let rby = input_byte f in
		if rby = 0 then
		  Printf.fprintf sout "Not a reply\n"
		else if rby = 1 then
		  begin
		    let (h,_) = sei_hashval seic (f,None) in
		    Printf.fprintf sout "Reply to %s\n" (hashval_hexstring h)
		  end
		else
		  Printf.fprintf sout "Bad Reply Byte %d\n" rby;
		let mti = input_byte f in
		Printf.fprintf sout "Message type %d: %s\n" mti (try string_of_msgtype (msgtype_of_int mti) with Not_found -> "no such message type");
		let (msl,_) = sei_int32 seic (f,None) in
		Printf.fprintf sout "Message contents length %ld bytes\n" msl;
		let (mh,_) = sei_hashval seic (f,None) in
		Printf.fprintf sout "Message contents hash %s\n" (hashval_hexstring mh);
		let sb = Buffer.create 100 in
		for i = 1 to (Int32.to_int msl) do
		  let x = input_byte f in
		  Buffer.add_char sb (Char.chr x)
		done;
		let s = Buffer.contents sb in
		Printf.fprintf sout "Message contents: %s\n" (string_hexstring s);
		try let mt = msgtype_of_int mti in extra_log_info mt s with Not_found -> ()
	      done
	    with
	    | End_of_file -> ()
	    | e -> Printf.fprintf sout "Exception: %s\n" (Printexc.to_string e)
	  end;
	  close_in_noerr f;
	  List.iter
	    (fun fn ->
	      Printf.fprintf sout "++++++++++++++++++++++++\nReport of all messages received via %s:\n" fn;
	      let f = open_in_bin fn in
	      begin
		try
		  while true do
		    let tmstmp : float = input_value f in
		    let gtm = Unix.gmtime tmstmp in
		    Printf.fprintf sout "Received At Time: %f (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		    let rmmm : hashval option * hashval * msgtype * string = input_value f in
		    let (replyto,mh,mt,m) = rmmm in
		    begin
		      match replyto with
		      | None -> Printf.fprintf sout "Not a reply\n"
		      | Some(h) -> Printf.fprintf sout "Reply to %s\n" (hashval_hexstring h)
		    end;
		    Printf.fprintf sout "Message type %d: %s\n" (int_of_msgtype mt) (string_of_msgtype mt);
		    Printf.fprintf sout "Message contents hash %s\n" (hashval_hexstring mh);
		    Printf.fprintf sout "Message contents: %s\n" (string_hexstring m);
		    extra_log_info mt m
		  done
		with
		| End_of_file -> ()
		| e -> Printf.fprintf sout "Exception: %s\n" (Printexc.to_string e)
	      end;
	      close_in_noerr f)
	    recfl;
	  !exitfn 0
    end;
    if not !Config.offline && not !Config.ltcoffline then
      begin
	if not !Config.daemon then (Printf.fprintf sout "Syncing with ltc.\n"; flush sout);
	ltc_init sout;
	if not !Config.daemon then (Printf.fprintf sout "Building block tree.\n"; flush sout);
	initialize_pfg_from_ltc sout !ltc_bestblock;
      end;
    Printf.fprintf sout "Loading wallet\n"; flush sout;
    Commands.load_wallet();
    let efn = !exitfn in
    exitfn := (fun n -> (try Commands.save_wallet() with _ -> ()); efn n);
    if !Config.swapping then
      begin
        Commands.load_swaps();
        let efn = !exitfn in
        exitfn := (fun n -> (try Commands.save_swaps true with _ -> ()); efn n);
      end;
    Printf.fprintf sout "Loading txpool\n"; flush sout;
    Commands.load_txpool();
    (*** We next compute a nonce for the node to prevent self conns; it doesn't need to be cryptographically secure ***)
    if not !random_initialized then initialize_random_seed();
    let n = rand_int64() in
    this_nodes_nonce := n;
    log_string (Printf.sprintf "Nonce: %Ld\n" n);
  end;;

exception Skip

let main () =
  initialize_commands();
  datadir_from_command_line(); (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
  process_config_file();
  process_config_args(); (*** settings on the command line shadow those in the config file ***)
  let last_failure = ref None in
  let failure_count = ref 0 in
  let failure_delay() =
    let tm = ltc_medtime() in
    match !last_failure with
    | Some(tm0) ->
	let d = Int64.sub tm tm0 in
	if d > 21600L then (** first failure in 6 hours, reset failure count to 1 and only delay 1 second **)
	  begin
	    failure_count := 1;
	    last_failure := Some(tm);
	    Thread.delay 1.0
	  end
	else if !failure_count > 100 then (** after 100 regular failures, just exit **)
	  begin
	    closelog();
	    !exitfn 1
	  end
	else
	  begin
	    incr failure_count;
	    last_failure := Some(tm);
	    Thread.delay (float_of_int !failure_count) (** with each new failure, delay for longer **)
	  end
    | None ->
	incr failure_count;
	last_failure := Some(tm);
	Thread.delay 1.0
  in
  let readevalloop () =
    while true do
      try
	Printf.printf "%s" !Config.prompt; flush stdout;
	let l = read_line() in
	do_command stdout l
      with
      | GettingRemoteData -> Printf.printf "Requested some remote data; try again.\n"
      | Exit -> () (*** silently ignore ***)
      | End_of_file ->
	  closelog();
	  Printf.printf "Shutting down threads. Please be patient.\n"; flush stdout;
	  !exitfn 0
      | Failure(x) ->
	  Printf.fprintf stdout "Ignoring Uncaught Failure: %s\n" x; flush stdout;
	  failure_delay()
      | BannedPeer -> Printf.fprintf stdout "Banned Peer"
      | exn -> (*** unexpected ***)
	  Printf.fprintf stdout "Ignoring Uncaught Exception: %s\n" (Printexc.to_string exn); flush stdout;
	  failure_delay()
    done
  in
  let daemon_readevalloop () =
    let lst = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let ia = Unix.inet_addr_of_string "127.0.0.1" in
    begin
      try
	Unix.bind lst (Unix.ADDR_INET(ia,!Config.rpcport));
      with _ ->
	Printf.fprintf !Utils.log "Cannot bind to rpcport. Quitting.\n";
	!exitfn 1
    end;
    let efn = !exitfn in
    exitfn := (fun n -> shutdown_close lst; efn n);
    set_signal_handlers();
    Unix.listen lst 1;
    while true do
      try
	let (s,a) = Unix.accept lst in
	let sin = Unix.in_channel_of_descr s in
	let sout = Unix.out_channel_of_descr s in
	try
	  let l = input_line sin in
	  if not (l = !Config.rpcuser) then raise (Failure "bad rpcuser");
	  let l = input_line sin in
	  if not (l = !Config.rpcpass) then raise (Failure "bad rpcpass");
	  let l = input_line sin in
	  do_command sout l;
	  flush sout;
	  shutdown_close s
	with
	| exn ->
	    flush sout;
	    Unix.close s;
	    raise exn
      with
      | Exit -> () (*** silently ignore ***)
      | End_of_file ->
	  closelog();
	  !exitfn 0
      | Failure(x) ->
	  log_string (Printf.sprintf "Ignoring Uncaught Failure: %s\n" x);
	  failure_delay()
      | exn -> (*** unexpected ***)
	  log_string (Printf.sprintf "Ignoring Uncaught Exception: %s\n" (Printexc.to_string exn));
	  failure_delay()
    done
  in
  if !Config.daemon then
    begin
      if !Config.rpcpass = "changeme" then
        begin
          Printf.printf "Refusing to run as a daemon until rpcpass is set\n";
          Printf.printf "Add the following lines to your proofgold.conf file:\n";
          Printf.printf "rpcuser='...'\nrpcpass='...'\nwhere the pass is a secure password.\n";
          !Utils.exitfn 1;
        end;
      match Unix.fork() with
      | 0 ->
	  initialize();
	  if not !Config.offline then
	    begin
	      initnetwork !Utils.log;
	      if !Config.staking then stkth := Some(Thread.create stakingthread ());
	      if !Config.swapping then swpth := Some(Thread.create swappingthread ());
	      if not !Config.ltcoffline then ltc_listener_th := Some(Thread.create ltc_listener ());
	    end;
	  daemon_readevalloop ()
      | pid -> Printf.printf "Proofgold daemon process %d started.\n" pid
    end
  else
    begin
      initialize();
      set_signal_handlers();
      if not !Config.offline then
	begin
	  initnetwork stdout;
	  if !Config.staking then stkth := Some(Thread.create stakingthread ());
	  if !Config.swapping then swpth := Some(Thread.create swappingthread ());
	  if not !Config.ltcoffline then ltc_listener_th := Some(Thread.create ltc_listener ());
	end;
      readevalloop()
    end;;

main();;

