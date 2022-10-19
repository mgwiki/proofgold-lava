type stp =
| Base of int
| TpArr of stp * stp
| Prop;;

type trm =
| DB of int
| TmH of string
| Prim of int
| Ap of trm * trm
| Lam of stp * trm
| Imp of trm * trm
| All of stp * trm
| Ex of stp * trm
| Eq of stp * trm * trm;;

type utm = int;;
type utp = int;;

external init : unit -> unit = "c_utm_init";;
init ();;

external mk_tpbase : int -> utp = "c_utm_mk_tpbase" [@@noalloc];;
external mk_tparr : utp -> utp -> utp = "c_utm_mk_tparr" [@@noalloc];;

external mk_db : int -> utm = "c_utm_mk_db" [@@noalloc];;
external mk_tmh : int -> utm = "c_utm_mk_tmh" [@@noalloc];;
external mk_prim : int -> utm = "c_utm_mk_prim" [@@noalloc];;
external mk_ap : utm -> utm -> utm = "c_utm_mk_ap" [@@noalloc];;
external mk_imp : utm -> utm -> utm = "c_utm_mk_imp" [@@noalloc];;
external mk_lam : utp -> utm -> utm = "c_utm_mk_lam" [@@noalloc];;
external mk_all : utp -> utm -> utm = "c_utm_mk_all" [@@noalloc];;
external mk_ex : utp -> utm -> utm = "c_utm_mk_ex" [@@noalloc];;
external mk_eq : utp -> utm -> utm -> utm = "c_utm_mk_eq" [@@noalloc];;

let hh=(Hashtbl.create 1000 : (string, int) Hashtbl.t);;
let hh_num=ref 0;;

external hash_clear : unit -> unit = "c_utm_hash_clear" [@@noalloc];;
let hash_clear () =
  hash_clear (); Hashtbl.clear hh; hh_num := 0;;

let hh_no s =
  try Hashtbl.find hh s
  with Not_found ->
    incr hh_num;
    Hashtbl.add hh s !hh_num;
    !hh_num
;;

let rec trm_no = function
  | TmH(h) -> mk_tmh (hh_no h)
  | DB(i) -> mk_db i
  | Prim(i) -> mk_prim i
  | Ap(m1,m2) -> mk_ap (trm_no m1) (trm_no m2)
  | Lam(a,m1) -> mk_lam (ty_no a) (trm_no m1)
  | Imp(m1,m2) -> mk_imp (trm_no m1) (trm_no m2)
  | All(a,m1) -> mk_all (ty_no a) (trm_no m1)
  | Ex(a,m1) -> mk_ex (ty_no a) (trm_no m1)
  | Eq(a,m1,m2) -> mk_eq (ty_no a) (trm_no m1) (trm_no m2)
and ty_no = function
  | Prop -> mk_tpbase 0
  | Base n -> mk_tpbase (n + 1)
  | TpArr (l, r) -> mk_tparr (ty_no l) (ty_no r);;

let rec fold_id f t =
  match t with
  | TmH(h) -> let n = mk_tmh (hh_no h) in n, f [] n t
  | DB(i) -> let n = mk_db i in n, f [] n t
  | Prim(i) -> let n = mk_prim i in n, f [] n t
  | Ap(m1,m2) ->
      let n1, sf1 = fold_id f m1 in
      let n2, sf2 = fold_id f m2 in
      let n = mk_ap n1 n2 in
      n, f [sf1;sf2] n t
  | Imp(m1,m2) ->
      let n1, sf1 = fold_id f m1 in
      let n2, sf2 = fold_id f m2 in
      let n = mk_imp n1 n2 in
      n, f [sf1;sf2] n t
  | Eq(a,m1,m2) ->
      let n1, sf1 = fold_id f m1 in
      let n2, sf2 = fold_id f m2 in
      let n = mk_eq (ty_no a) n1 n2 in
      n, f [sf1;sf2] n t
  | All(a,m1) ->
      let n1, sf1 = fold_id f m1 in
      let n = mk_all (ty_no a) n1 in
      n, f [sf1] n t
  | Ex(a,m1) ->
      let n1, sf1 = fold_id f m1 in
      let n = mk_ex (ty_no a) n1 in
      n, f [sf1] n t
  | Lam(a,m1) ->
      let n1, sf1 = fold_id f m1 in
      let n = mk_lam (ty_no a) n1 in
      n, f [sf1] n t;;

(* fold_id : ('a list -> int -> trm -> 'a) -> trm -> 'a *)
let fold_id (f : ('a list -> int -> trm -> 'a)) t = snd (fold_id f t);;
