external sha256 : string -> Be256.t = "c_sha256_bebits";;
external sha256l : string list -> Be256.t = "c_sha256_list_bebits";;

external sha256_round :
  (int32*int32*int32*int32*int32*int32*int32*int32) ->
  (int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32*int32) ->
  (int32*int32*int32*int32*int32*int32*int32*int32) = "c_sha256_round";;

(* given the arrays currhashval currblock updates the former *)
let sha256_round_arrays chv cb =
  let a1 = chv.(0),chv.(1),chv.(2),chv.(3),chv.(4),chv.(5),chv.(6),chv.(7) in
  let a2 = cb.(0),cb.(1),cb.(2),cb.(3),cb.(4),cb.(5),cb.(6),cb.(7),
           cb.(8),cb.(9),cb.(10),cb.(11),cb.(12),cb.(13),cb.(14),cb.(15) in
  let (a,b,c,d,e,f,g,h) = sha256_round a1 a2 in
  chv.(0) <- a; chv.(1) <- b; chv.(2) <- c; chv.(3) <- d;
  chv.(4) <- e; chv.(5) <- f; chv.(6) <- g; chv.(7) <- h
;;

type sha256buf;;
external mk_sha256buf : unit -> sha256buf = "c_sha256_buffer";;
external sha256_add_s1 : sha256buf -> string -> unit = "c_sha256_add_s1" [@@noalloc];;
external sha256_add_s4 : sha256buf -> string -> unit = "c_sha256_add_s4" [@@noalloc];;
external sha256_add_s32 : sha256buf -> string -> unit = "c_sha256_add_s32" [@@noalloc];;
external sha256_add_be256 : sha256buf -> Be256.t -> unit = "c_sha256_add_s32" [@@noalloc];;
external sha256_add_i32 : sha256buf -> int32 -> unit = "c_sha256_add_i32" [@@noalloc];;
external sha256buf_finalize : sha256buf -> Be256.t = "c_sha256_finalize";;

external ripemd160 : Be256.t -> Be160.t = "c_ripemd160_be_be";;
