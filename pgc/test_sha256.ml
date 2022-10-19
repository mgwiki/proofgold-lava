open Hashbtc;;

let be = sha256 "asdfasdf";;

let t1 = sha256 (Bebits.of_int32 7l ^ Be256.to_string be);;

let b = mk_sha256buf ();;
sha256_add_s4 b "\000\000\000\007";;
sha256_add_be256 b be;;
let t2 = sha256buf_finalize b;;

Printf.printf "%b\n" (t1 = t2);;
let s = Bebits.of_int32 (Int32.of_int (65 + 66 * 256));;
let t3 = sha256 (Bebits.of_int32 8l ^ Bebits.of_int32 (Int32.of_int (65 + 66 * 256)) ^ Be256.to_string be)

let b = mk_sha256buf ();;
sha256_add_s4 b "\000\000\000\008";;
sha256_add_i32 b (Int32.of_int (65 + 66 * 256));;
sha256_add_be256 b be;;
let t4 = sha256buf_finalize b;;

Printf.printf "%b\n" (t3 = t4);;
