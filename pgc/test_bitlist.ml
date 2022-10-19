open Bitlist;;
let print2 bl =
  print2 Format.std_formatter bl; Format.pp_print_char Format.std_formatter '\n';
  Format.pp_print_flush Format.std_formatter ();;

let bl = of_bools [false;false;false;false;false;false];;
Printf.printf "6 falses: "; print2 bl;;
set bl 2 true;;
let (s,_,_) = to_string bl;;

Bebits.blit_bools [true;true;true;true] s 4 (-1);;
Printf.printf "4 blits   "; print2 bl;;

let bl2 = cut_prefix bl 2;;
Printf.printf "2 cuts    "; print2 bl2;;

let bl3 = rev_append [false;true;true] bl2;;
Printf.printf "3 "; print2 bl3;;

let bl4 = of_bools [true; true; true; true; true; true; true; true; true; true];;
let (s, _, _) = to_string bl in
Printf.printf "Str <%s>\n" (Bebits.to_hexstring s);;

let bl1a = of_bools [true; true];;
let bl1 = of_bools [true; true; true];;
let bl2 = of_bools [true; true];;
let bl1c = cut_prefix bl1 1;;

Printf.printf "Fast compare if bit-aligned: %b\n" (eq_when_zeroed bl1a bl2);;
Printf.printf "Slow-compare if non-aligned: %b\n" (eq_by_bits bl1c bl2);;


let a = of_string ("\255\255\255", 8, 12);;
print2 a;;
let (s, _, _) = to_string a;;
print2 a;;
Printf.printf "Actual contents: <%s>\n" s;;
