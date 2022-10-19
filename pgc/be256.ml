type t = string;;
let to_int32p8 = Bebits.to_int32p8;;
let of_int32p8 = Bebits.of_int32p8;;
let to_hexstring = Bebits.to_hexstring;;
let of_hexstring = Bebits.of_hexstring;;

let to_string x = x;;
let of_substring s p = String.sub s p 32;;
let of_channel ic = really_input_string ic 32;;

let get_bit = Bebits.get_bit;;

let rev = Bebits.rev;;

let hash = Bebits.hash;;

let seo o x c =
  let rec seo_iter i c =
    if i = 32 then c else seo_iter (i + 1) (o 8 (Bebits.get_byte x i) c) in
  seo_iter 0 c;;

let sei i c =
  let x = Bebits.zero 32 in
  let rec sei_iter j c =
    if j = 32 then x, c else
    let v, nc = i 8 c in
    Bebits.set_byte x j v;
    sei_iter (j + 1) nc
  in
  sei_iter 0 c;;
