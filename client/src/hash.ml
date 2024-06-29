(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold Core developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint
open Json
open Hashaux
open Sha256
open Ser

(* A hash value is a 256-bit number represented in big-endian byte order. *)
type hashval = Be256.t

(* Convert a hash value to a hexadecimal string. *)
let hashval_hexstring h = Be256.to_hexstring h

(* Convert a hexadecimal string to a hash value. *)
let hexstring_hashval h = Be256.of_hexstring h

(* Convert a hash value to a list of 32-bit integers in big-endian byte order. *)
let hashval_int32p8 h = Be256.to_int32p8 h

(* Convert a list of 32-bit integers in big-endian byte order to a hash value. *)
let int32p8_hashval h = Be256.of_int32p8 h

(* Compute the SHA-256 hash of a string. *)
let sha256str_hashval = sha256str

(* Compute the double SHA-256 hash of a string. *)
let sha256dstr_hashval = sha256dstr

(* An address is a pair of an integer prefix and a 160-bit hash value in big-endian byte order. *)
type addr = int * Be160.t

(* A pay-to-public-key-hash address is a 160-bit hash value in big-endian byte order. *)
type p2pkhaddr = Be160.t

(* A pay-to-script-hash address is a 160-bit hash value in big-endian byte order. *)
type p2shaddr = Be160.t

(* A payment address is a pair of a boolean flag and a 160-bit hash value in big-endian byte order. *)
type payaddr = bool * Be160.t

(* A term address is a 160-bit hash value in big-endian byte order. *)
type termaddr = Be160.t

(* A public key address is a 160-bit hash value in big-endian byte order. *)
type pubaddr = Be160.t

(* Cache for the hashes of 32-bit integers. *)
let hashcache_int32 : (int32,hashval) Hashtbl.t = Hashtbl.create 100 (** always on **)

(* Cache for the hashes of 64-bit integers. *)
let hashcache_int64 : (int64,hashval) Hashtbl.t = Hashtbl.create 100 (** always on **)

(* The zero hash value. *)
let zerohashval : hashval = Be256.of_int32p8 (0l,0l,0l,0l,0l,0l,0l,0l)

(* Compute the RIPEMD-160 hash of a string. *)
let hash160 s = Hashbtc.ripemd160 (sha256str s)

(* Compute the SHA-256 hash of a 32-bit integer. *)
let hashint32 x =
  try
    Hashtbl.find hashcache_int32 x
  with Not_found ->
    let h = Hashbtc.sha256l ["\000\000\000\001"; Bebits.of_int32 x] in
    Hashtbl.add hashcache_int32 x h;
    h

(* Compute the SHA-256 hash of a 64-bit integer. *)
(*** x:int64 ***)
let hashint64 x =
  try
    Hashtbl.find hashcache_int64 x
  with Not_found ->
    let h = Hashbtc.sha256l ["\000\000\000\002"; Bebits.of_int32 (Int64.to_int32 (Int64.shift_right_logical x 32)); Bebits.of_int32 (Int64.to_int32 x)] in
    Hashtbl.add hashcache_int64 x h;
    h

(* Convert a pay-to-public-key-hash address to a payment address. *)
let p2pkhaddr_payaddr x =
  (false,x)

(* Convert a pay-to-script-hash address to a payment address. *)
let p2shaddr_payaddr x =
  (true,x)

(* Convert a pay-to-public-key-hash address to an address. *)
let p2pkhaddr_addr x =
  (0,x)

(* Convert a pay-to-script-hash address to an address. *)
let p2shaddr_addr x =
  (1,x)

(* Convert a payment address to an address. *)
let payaddr_addr x =
  let (b,xs) = x in
  if b then
    (1,xs)
  else
    (0,xs)

(* Convert a term address to an address. *)
let termaddr_addr x =
  (2,x)

(* Convert a public key address to an address. *)
let pubaddr_addr x =
  (3,x)

(* Check if an address is a pay-to-public-key or pay-to-script-hash address. *)
let payaddr_p x =
  let (p,_) = x in
  p = 0 || p = 1

(* Check if an address is a pay-to-public-key address. *)
let p2pkhaddr_p x =
  let (p,_) = x in
  p = 0

(* Check if an address is a pay-to-script-hash address. *)
let p2shaddr_p x =
  let (p,_) = x in
  p = 1

(* Check if an address is a term address. *)
let termaddr_p x =
  let (p,_) = x in
  p = 2

(* Check if an address is a public key address. *)
let pubaddr_p x =
  let (p,_) = x in
  p = 3

(* Convert a 160-bit hash value to a list of booleans representing its bits in big-endian order. *)
let be160_bitseq x =
  let (x0,x1,x2,x3,x4) = Be160.to_int32p5 x in
  let r = ref [] in
  let aux xj =
    for i = 0 to 31 do
      if Int32.logand (Int32.shift_right_logical xj i) 1l = 1l then
	r := true::!r
      else
	r := false::!r
    done
  in
  aux x4; aux x3; aux x2; aux x1; aux x0;
  !r

(* Convert a 256-bit hash value to a list of booleans representing its bits in big-endian order. *)
let hashval_bitseq x =
  let (x0,x1,x2,x3,x4,x5,x6,x7) = Be256.to_int32p8 x in
  let r = ref [] in
  let aux xj =
    for i = 0 to 31 do
      if Int32.logand (Int32.shift_right_logical xj i) 1l = 1l then
	r := true::!r
      else
	r := false::!r
    done
  in
  aux x7; aux x6; aux x5; aux x4; aux x3; aux x2; aux x1; aux x0;
  !r

(* Compute the RIPEMD-160 hash of a 256-bit hash value. *)
let hashval_be160 x = Hashbtc.ripemd160 x

(* Convert a 256-bit hash value to a pay-to-public-key-hash payment address. *)
let hashval_p2pkh_payaddr x =
  let xs = Hashbtc.ripemd160 x in
  (false,xs)

(* Convert a 256-bit hash value to a pay-to-script-hash payment address. *)
let hashval_p2sh_payaddr x =
  let xs = Hashbtc.ripemd160 x in
  (true,xs)

(* Convert a 160-bit hash value to a pay-to-public-key-hash address. *)
let be160_p2pkh_addr x =
  (0,x)

(* Convert a 256-bit hash value to a pay-to-public-key-hash address. *)
let hashval_p2pkh_addr x =
  let xs = Hashbtc.ripemd160 x in
  (0,xs)

(* Convert a 160-bit hash value to a pay-to-script-hash address. *)
let be160_p2sh_addr x =
  (1,x)

(* Convert a 256-bit hash value to a pay-to-script-hash address. *)
let hashval_p2sh_addr x =
  let xs = Hashbtc.ripemd160 x in
  (1,xs)

(* Convert a 256-bit hash value to a term address. *)
let hashval_term_addr x =
  let xs = Hashbtc.ripemd160 x in
  (2,xs)

(* Convert a 256-bit hash value to a public key address. *)
let hashval_pub_addr x =
  let xs = Hashbtc.ripemd160 x in
  (3,xs)

(* Convert an address to a list of booleans representing its bits in big-endian order. *)
let addr_bitseq x =
  let (p,xs) = x in
  let r = be160_bitseq xs in
  if p = 0 then
    (false::false::r)
  else if p = 1 then
    (false::true::r)
  else if p = 2 then
    (true::false::r)
  else
    (true::true::r)

(* Convert an address to a bit list. *)
let addr_bitlist x =
  let (p,xs) = x in
  let xl = Bitlist.of_string (Be160.to_string xs,0,160) in
  match p with
  | 0 -> Bitlist.cons false (Bitlist.cons false xl)
  | 1 -> Bitlist.cons false (Bitlist.cons true xl)
  | 2 -> Bitlist.cons true (Bitlist.cons false xl)
  | 3 -> Bitlist.cons true (Bitlist.cons true xl)
  | _ -> raise (Failure "nonaddress given to addr_bitlist")


(* Convert a list of booleans to a 32-bit integer. *)
let rec bitseq_int32 bl r i =
  if i < 0 then
    (r,bl)
  else
    match bl with
    | (true::br) ->
	bitseq_int32 br (Int32.logor (Int32.shift_left 1l i) r) (i-1)
    | (false::br) ->
	bitseq_int32 br r (i-1)
    | _ -> raise (Failure "bitseq_int32 called with bitseq of insufficient length")

(* Convert a list of booleans to an address. *)
let bitseq_addr bs =
  let (p,bl) =
    match bs with
    | (false::false::bl) -> (0,bl)
    | (false::true::bl) -> (1,bl)
    | (true::false::bl) -> (2,bl)
    | (true::true::bl) -> (3,bl)
    | _ -> raise (Failure "bitseq too short")
  in
  let (x0,bl) = bitseq_int32 bl 0l 31 in
  let (x1,bl) = bitseq_int32 bl 0l 31 in
  let (x2,bl) = bitseq_int32 bl 0l 31 in
  let (x3,bl) = bitseq_int32 bl 0l 31 in
  let (x4,bl) = bitseq_int32 bl 0l 31 in
  (p,Be160.of_int32p5 (x0,x1,x2,x3,x4))

(* Convert a bit list to an address. *)
let bitlist_addr x =
  let (xs,i,j) = Bitlist.to_string x in
  if i = 6 && j = 162 then (** if this is always true we can delete this if, but playing it safe for now **)
    begin
      Utils.log_string (Printf.sprintf "bitlist_addr 1 %d %d\n" i j);
      let xa = Be160.of_substring xs 1 in
      Utils.log_string (Printf.sprintf "bitlist_addr 2 %d %d\n" i j);
      if Bitlist.get x 0 then
        if Bitlist.get x 1 then
          (3,xa)
        else
          (2,xa)
      else
        if Bitlist.get x 1 then
          (1,xa)
        else
          (0,xa)
    end
  else
    begin
      Utils.log_string (Printf.sprintf "bitlist_addr to_bools case %d %d\n" i j);
      bitseq_addr (Bitlist.to_bools x)
    end

(* Convert a list of booleans to a 256-bit hash value. *)
let bitseq_hashval bl =
  let (x0,bl) = bitseq_int32 bl 0l 31 in
  let (x1,bl) = bitseq_int32 bl 0l 31 in
  let (x2,bl) = bitseq_int32 bl 0l 31 in
  let (x3,bl) = bitseq_int32 bl 0l 31 in
  let (x4,bl) = bitseq_int32 bl 0l 31 in
  let (x5,bl) = bitseq_int32 bl 0l 31 in
  let (x6,bl) = bitseq_int32 bl 0l 31 in
  let (x7,bl) = bitseq_int32 bl 0l 31 in
  Be256.of_int32p8 (x0,x1,x2,x3,x4,x5,x6,x7)

(* Convert a byte list to a 32-bit integer. *)
let bytelist_int32 bl =
  match bl with
  | (m3::m2::m1::m0::br) ->
     (* copied from sei_int32 in ser *)
     (Int32.logor (Int32.of_int m0)
        (Int32.logor (Int32.shift_left (Int32.of_int m1) 8)
	   (Int32.logor (Int32.shift_left (Int32.of_int m2) 16)
	      (Int32.shift_left (Int32.of_int m3) 24))),br)
  | _ -> raise (Failure "bytelist_int32 given too short of a list")

(* Convert a byte list to a 160-bit hash value. *)
let bytelist_be160 bl =
  let (x0,bl) = bytelist_int32 bl in
  let (x1,bl) = bytelist_int32 bl in
  let (x2,bl) = bytelist_int32 bl in
  let (x3,bl) = bytelist_int32 bl in
  let (x4,bl) = bytelist_int32 bl in
  Be160.of_int32p5 (x0,x1,x2,x3,x4)

(* Convert a byte list to a 256-bit hash value. *)
let bytelist_be256 bl =
  let (x0,bl) = bytelist_int32 bl in
  let (x1,bl) = bytelist_int32 bl in
  let (x2,bl) = bytelist_int32 bl in
  let (x3,bl) = bytelist_int32 bl in
  let (x4,bl) = bytelist_int32 bl in
  let (x5,bl) = bytelist_int32 bl in
  let (x6,bl) = bytelist_int32 bl in
  let (x7,bl) = bytelist_int32 bl in
  Be256.of_int32p8 (x0,x1,x2,x3,x4,x5,x6,x7)

(* Convert a 256-bit hash value to a byte list. *)
let be256_bytelist h =
  let s = Be256.to_string h in
  let bl = ref [] in
  for i = 31 downto 0 do
    bl := Char.code (s.[i])::!bl
  done;
  !bl

(* Compute the SHA-256 hash of an address. *)
(*** x is an address, 162 bits ***)
let hashaddr x =
  let (p,xs) = x in
  let p1 =
    match p with
    | 0 -> "\000\000\000\003"
    | 1 -> "\000\000\000\004"
    | 2 -> "\000\000\000\005"
    | 3 -> "\000\000\000\006"
    | _ -> raise (Failure "illegal prefix for address")
  in
  Hashbtc.sha256l [p1; Be160.to_string xs]

(* Compute the SHA-256 hash of a payment address. *)
let hashpayaddr x =
  let (b,xs) = x in
  Hashbtc.sha256l [(if b then "\000\000\000\004" else "\000\000\000\003"); Be160.to_string xs]

(* Compute the SHA-256 hash of a term address. *)
let hashtermaddr x =
  Hashbtc.sha256l ["\000\000\000\005"; Be160.to_string x]

(* Compute the SHA-256 hash of a public key address. *)
let hashpubaddr x =
  Hashbtc.sha256l ["\000\000\000\006"; Be160.to_string x]

(* Compute the SHA-256 hash of a pair of 256-bit hash values. *)
(*** x and y are hashvals ***)
let hashpair x y =
  Hashbtc.sha256l ["\000\000\000\007" ; Be256.to_string x ; Be256.to_string y]

(* Compute the SHA-256 hash of a tagged 256-bit hash value. *)
let hashtag x tg =
  Hashbtc.sha256l ["\000\000\000\008" ; Bebits.of_int32 tg ; Be256.to_string x]

(* Compute the SHA-256 hash of a pair of public keys. *)
let hashpubkey x y =
  Hashbtc.sha256l ["\004" ; Be256.to_string x ; Be256.to_string y]

(* Compute the SHA-256 hash of a compressed public key. *)
let hashpubkeyc p x =
  Hashbtc.sha256l [(if p = 2 then "\002" else "\003") ; Be256.to_string x]

(* Compute the SHA-256 hash of a list of 256-bit hash values. *)
(* due to a length error bug we still need to use sha256round here *)
let hashlist hl =
  let currhashval : int32 array = [| 0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al; 0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l |] in
  let currblock : int32 array = [| 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l |] in
  let sha256round () =
    Hashbtc.sha256_round_arrays currhashval currblock
  in
  let l = List.length hl in
  if l >= 8388576 then raise (Failure "hashlist overflow");
  let bl = Int32.of_int (l * 160 + 64) in (* bit length calculation error making it not really sha256; should have been l * 256 + 64 *)
  currblock.(0) <- 9l;
  currblock.(1) <- Int32.of_int l;
  let i = ref 2 in
  List.iter
    (fun x ->
      let (x0,x1,x2,x3,x4,x5,x6,x7) = Be256.to_int32p8 x in (* simplify when hashval = string *)
      currblock.(!i) <- x0;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x1;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x2;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x3;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x4;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x5;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x6;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x7;
      incr i;
      if !i = 16 then (i := 0; sha256round());
    ) hl;
  if !i < 15 then
    begin
      currblock.(!i) <- 0x80000000l;
      incr i;
      while !i < 15 do
	currblock.(!i) <- 0l;
	incr i;
      done
    end
  else
    begin
      currblock.(15) <- 0x80000000l;
      sha256round();
      for j = 0 to 14 do
	currblock.(j) <- 0l;
      done
    end;
  currblock.(15) <- bl;
  sha256round();
  Be256.of_int32p8 (currhashval.(0),currhashval.(1),currhashval.(2),currhashval.(3),currhashval.(4),currhashval.(5),currhashval.(6),currhashval.(7))

(* Compute the optional SHA-256 hash of a list of 256-bit hash values. *)
let rec ohashlist hl =
  begin
    match hl with
    | [] -> None
    | h::hr ->
	begin
	  match ohashlist hr with
	  | None -> Some(hashtag h 3l)
	  | Some(k) -> Some(hashtag (hashpair h k) 4l)
	end
  end

(* Compute the optional SHA-256 hash of a pair of optional 256-bit hash values. *)
(*** hashopair, x and y are hashval options ***)
let hashopair x y =
  match x,y with
  | Some x,Some y -> Some(hashpair x y)
  | Some x,None -> Some(hashtag x 0l)
  | None,Some y -> Some(hashtag y 1l)
  | None,None -> None

(* Compute the SHA-256 hash of a pair of a 256-bit hash value and an optional 256-bit hash value. *)
let hashopair1 x y =
  match y with
  | Some y -> hashpair x y
  | None -> hashtag x 0l

(* Compute the SHA-256 hash of a pair of an optional 256-bit hash value and a 256-bit hash value. *)
let hashopair2 x y =
  match x with
  | Some x -> hashpair x y
  | None -> hashtag y 1l

(* Compute the SHA-256 hash of a bit sequence. *)
let rec hashbitseq_r bl i =
  if i >= 32 then
    let (x,bl) = bitseq_int32 bl 0l 31 in
    hashpair (hashint32 x) (hashbitseq_r bl (i-32))
  else
    let (x,_) = bitseq_int32 bl 0l (i-1) in
    hashint32 x

(* Compute the SHA-256 hash of a bit sequence. *)
let hashbitseq bl = hashtag (hashbitseq_r bl (List.length bl)) 140l

(* Print a 256-bit hash value in hexadecimal format. *)
let printhashval h =
  Printf.printf "%s\n" (Be256.to_hexstring h)

(* Convert a 256-bit hash value to a big integer. *)
let be256_big_int h =
  int32p8_big_int (Be256.to_int32p8 h)

(* Convert a 256-bit hash value to a big integer. *)
let hashval_big_int = be256_big_int

(* Convert a big integer to a 256-bit hash value. *)
let big_int_be256 x =
  let h0 = big_int_sub_int32 x 224 in
  let h1 = big_int_sub_int32 x 192 in
  let h2 = big_int_sub_int32 x 160 in
  let h3 = big_int_sub_int32 x 128 in
  let h4 = big_int_sub_int32 x 96 in
  let h5 = big_int_sub_int32 x 64 in
  let h6 = big_int_sub_int32 x 32 in
  let h7 = big_int_sub_int32 x 0 in
  Be256.of_int32p8 (h0,h1,h2,h3,h4,h5,h6,h7)

(* Convert a big integer to a 256-bit hash value. *)
let big_int_hashval = big_int_be256

(* Serialize a 256-bit hash value. *)
let seo_be256 o h c =
  let (h0,h1,h2,h3,h4,h5,h6,h7) = Be256.to_int32p8 h in
  let c = seo_int32 o h0 c in
  let c = seo_int32 o h1 c in
  let c = seo_int32 o h2 c in
  let c = seo_int32 o h3 c in
  let c = seo_int32 o h4 c in
  let c = seo_int32 o h5 c in
  let c = seo_int32 o h6 c in
  let c = seo_int32 o h7 c in
  c

(* Serialize a 256-bit hash value to a string buffer. *)
let seosb_be256 h c =
  match c with
  | (bu,None) ->
     Buffer.add_string bu (Be256.to_string h);
     (bu,None)
  | _ -> seo_be256 seosb h c

(* Serialize a 256-bit hash value to a channel. *)
let seoc_be256 h c =
  match c with
  | (ch,None) ->
     output_string ch (Be256.to_string h);
     (ch,None)
  | _ -> seo_be256 seoc h c

(* Deserialize a 256-bit hash value. *)
let rec sei_be256 i c =
  let (h0,c) = sei_int32 i c in
  let (h1,c) = sei_int32 i c in
  let (h2,c) = sei_int32 i c in
  let (h3,c) = sei_int32 i c in
  let (h4,c) = sei_int32 i c in
  let (h5,c) = sei_int32 i c in
  let (h6,c) = sei_int32 i c in
  let (h7,c) = sei_int32 i c in
  (Be256.of_int32p8 (h0,h1,h2,h3,h4,h5,h6,h7),c)

(* Deserialize a 256-bit hash value from a string. *)
let seis_be256 c =
  match c with
  | (s,k,None,i,j) when j = 0 ->
     let h = Be256.of_substring s i in
     (h,(s,k,None,i+32,j))
  | _ -> sei_be256 seis c

(* Deserialize a 256-bit hash value from a channel. *)
let seic_be256 c =
  match c with
  | (ch,None) ->
     let h = Be256.of_channel ch in
     (h,(ch,None))
  | _ -> sei_be256 seic c

(* Serialize a 256-bit hash value. *)
let seo_hashval = seo_be256

(* Serialize a 256-bit hash value to a string buffer. *)
let seosb_hashval = seosb_be256

(* Serialize a 256-bit hash value to a channel. *)
let seoc_hashval = seoc_be256

(* Deserialize a 256-bit hash value. *)
let sei_hashval = sei_be256

(* Deserialize a 256-bit hash value from a string. *)
let seis_hashval = seis_be256

(* Deserialize a 256-bit hash value from a channel. *)
let seic_hashval = seic_be256

(* Serialize a 160-bit hash value. *)
let seo_be160 o h c =
  let (h0,h1,h2,h3,h4) = Be160.to_int32p5 h in
  let c = seo_int32 o h0 c in
  let c = seo_int32 o h1 c in
  let c = seo_int32 o h2 c in
  let c = seo_int32 o h3 c in
  let c = seo_int32 o h4 c in
  c

(* Serialize a 160-bit hash value to a string buffer. *)
let seosb_be160 h c =
  match c with
  | (bu,None) ->
     Buffer.add_string bu (Be160.to_string h);
     (bu,None)
  | _ -> seo_be160 seosb h c

(* Deserialize a 160-bit hash value. *)
let sei_be160 i c =
  let (h0,c) = sei_int32 i c in
  let (h1,c) = sei_int32 i c in
  let (h2,c) = sei_int32 i c in
  let (h3,c) = sei_int32 i c in
  let (h4,c) = sei_int32 i c in
  (Be160.of_int32p5 (h0,h1,h2,h3,h4),c)

(* Serialize an address. *)
let seo_addr o (p,xs) c =
  let c = o 2 p c in (*** 2 bit prefix indicating which kind of address ***)
  seo_be160 o xs c

(* Deserialize an address. *)
let sei_addr i c =
  let (p,c) = i 2 c in
  let (xs,c) = sei_be160 i c in
  ((p,xs),c)

(* Serialize a payment address. *)
let seo_payaddr o (b,xs) c =
  let c = o 1 (if b then 1 else 0) c in (*** 1 bit prefix indicating whether its p2pkh or p2sh ***)
  seo_be160 o xs c

(* Deserialize a payment address. *)
let sei_payaddr i c =
  let (b,c) = i 1 c in
  let (xs,c) = sei_be160 i c in
  ((b = 1,xs),c)

(* Serialize a term address. *)
let seo_termaddr o alpha c = seo_be160 o alpha c

(* Deserialize a term address. *)
let sei_termaddr i c = sei_be160 i c

(* Serialize a public key address. *)
let seo_pubaddr o alpha c = seo_be160 o alpha c

(* Deserialize a public key address. *)
let sei_pubaddr i c = sei_be160 i c

(* Compute the Merkle root of a list of 256-bit hash values. *)
let merkle_root (l:hashval list) : hashval option =
  match l with
  | [] -> None
  | (h::r) ->
      let rec merkle_root_a h r =
	match r with
	| [] -> [hashpair h h]
	| [h2] -> [hashpair h h2]
	| (h2::h3::r2) -> (hashpair h h2)::merkle_root_a h3 r2
      in
      let rec merkle_root_b h r =
	match merkle_root_a h r with
	| [] -> raise (Failure "impossible")
	| [h2] -> h2
	| (h2::r2) -> merkle_root_b h2 r2
      in
      Some (merkle_root_b h r)

(* Parse a 256-bit hash value from a JSON string. *)
let hashval_from_json j =
  match j with
  | JsonStr(h) -> hexstring_hashval h
  | _ -> raise (Failure("not a hashval"))

(* Reverse the bytes of a 256-bit hash value. *)
let hashval_rev h = Be256.rev h

(* The bounty fund address. *)
let bountyfund = Be160.of_int32p5 (861509328l, 1659223912l, -1848099664l, -1155860081l, 1514376423l)

(* Get a bit of an address. *)
let addr_get_bit (p,xs) i =
  match i with
  | 0 -> p lsr 1 = 1
  | 1 -> p land 1 = 1
  | _ -> Be160.get_bit xs (i-2)
