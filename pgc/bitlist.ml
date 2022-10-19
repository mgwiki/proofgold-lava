(* Keeps a string together with first-bit and length *)
type t = (string * int * int);;

let zeros n = (String.make ((n + 7) / 8) '\000'), 0, n;;
let length (_, st, len) = len;;

let to_bools_rev (s, st, len) = Bebits.to_bools s st (st + len) 1;;
let to_bools (s, st, len) = Bebits.to_bools s (st + len - 1) (st - 1) (-1);;

let of_bools l =
  let len = List.length l in
  let ((s, _, _) as ret) = zeros len in
  Bebits.blit_bools l s 0 1;
  ret;;

let cut_prefix (s, st, len) j =
  if j > len || j < 0 then failwith "Bitlist.cut_prefix cannot extend";
  (s, st + j, len - j);;

let cut_prefix_zero (s, st, len) j =
  Bebits.zero_bits s st j;
  cut_prefix (s, st, len) j;;

let get (s,st,_) i = Bebits.get_bit s (st+i);;
let set (s,st,_) i v = Bebits.set_bit s (st+i) v;;

let rev_append l (s, st, oldlen) =
  let addlen = List.length l in
  let ns, nst =
    if addlen <= st then s, st else begin
      let willadd = ((addlen - st) + 7) / 8 in
      let slen = String.length s in
      let ns = String.make (slen + willadd) '\000' in
      String.blit s 0 (Obj.magic ns) willadd slen;
      ns, (st + willadd * 8)
    end in
  Bebits.blit_bools l ns (nst - 1) (-1);
  (ns, nst - addlen, oldlen + addlen);;

let cons b t = rev_append [b] t;;

let zero_outside (s, st, len) =
  Bebits.zero_bits s 0 st;
  Bebits.zero_bits s (st + len) (8 * (String.length s) - st - len)
;;

let to_string t = t;;
let of_string t = t;;

let print1 b = Printf.printf "%s\n" (String.concat "" (List.map (fun b -> if b then "1" else "0") (to_bools b)));;

let print2 f ((s,st,len) as b) =
  let print_underlying b i = Format.pp_print_char f (if get b (i - st) then '1' else '0') in
  for i = 0 to st - 1 do print_underlying b i done; Format.pp_print_char f '{';
  for i = st to (st + len) - 1 do print_underlying b i done; Format.pp_print_char f '}';
  for i = (st + len) to (String.length s) * 8 - 1 do print_underlying b i done;;

let hd b = get b 0;;
let tl b = cut_prefix b 1;;

let eq_by_bits (s1, st1, l1) (s2, st2, l2) =
  l1 = l2 && Bebits.bit_eq s1 st1 s2 st2 l1

let eq_when_zeroed (s1, st1, l1) (s2, st2, l2) =
  l1 = l2 && (if st1 = st2 then s1 = s2 else Bebits.bit_eq s1 st1 s2 st2 l1);;

let copy (s, st, len) = (String.copy s, st, len);;
