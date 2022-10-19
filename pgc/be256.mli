type t;;
val to_int32p8 : t -> int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32;;
val of_int32p8 : int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 -> t;;
val to_hexstring : t -> string;;
val of_hexstring : string -> t;;

(* For adding to buffer or writing to channel *)
val to_string : t -> string;;
val of_substring : string -> int -> t;;
val of_channel : in_channel -> t;;

val get_bit : t -> int -> bool;;

val rev : t -> t;;

val hash : t -> int;;

val seo : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
val sei : (int -> 'a -> int * 'a) -> 'a -> t * 'a
