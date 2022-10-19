(* Big endian strings of bits, internally stored as strings *)
let zero n = String.make n '\000';;

external of_int32   : int32 -> string = "c_int32_bebits";;
external of_int32p5 : int32 * int32 * int32 * int32 * int32 -> string = "c_int32pow5_bebits";;
external of_int32p8 : int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 -> string = "c_int32pow8_bebits";;

external to_int32   : string -> int32 = "c_bebits_int32";;
external to_int32p5 : string -> int32 * int32 * int32 * int32 * int32 = "c_bebits_int32pow5";;
external to_int32p8 : string -> int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 = "c_bebits_int32pow8";;

external to_hexstring : string -> string = "c_bebits_hexstring";;
(* if input length is odd, last character is ignored as we cannot put it in a single be character *)
external of_hexstring : string -> string = "c_hexstring_bebits";;

external rev : string -> string = "c_bebits_rev";;

external get_bit : string -> int -> bool = "c_bebits_get_bit" [@@noalloc];;
external set_bit : string -> int -> bool -> unit = "c_bebits_set_bit" [@@noalloc];;
external get_byte : string -> int -> int = "c_bebits_get_byte" [@@noalloc];;
external set_byte : string -> int -> int -> unit = "c_bebits_set_byte" [@@noalloc];;

external blit_bools : bool list -> string -> int -> int -> unit = "c_bools_blit_bebits" [@@noalloc];;
(* [to_bools s start end step] where [step] is +-1 and [end] is the first invalid position *)
external to_bools : string -> int -> int -> int -> bool list = "c_bebits_to_bools";;
external zero_bits : string -> int -> int -> unit = "c_bebits_zero_bits" [@@noalloc];;
external bit_eq : string -> int -> string -> int -> int -> bool = "c_bebits_bit_eq" [@@noalloc];;

(* Assumes the string is already a hash longer than an int, returns its first sizeof(int) bytes *)
external hash : string -> int = "c_bebits_hash" [@@noalloc];;
