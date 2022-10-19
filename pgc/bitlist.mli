type t;;

val zeros : int -> t;;
val length : t -> int;;

val of_bools : bool list -> t;;

val to_bools : t -> bool list;;
val to_bools_rev : t -> bool list;;

val cut_prefix : t -> int -> t;;
val cut_prefix_zero : t -> int -> t;;

val get : t -> int -> bool;;
val set : t -> int -> bool -> unit;;

val hd : t -> bool;;
val tl : t -> t;;

val cons : bool -> t -> t;;
val rev_append : bool list -> t -> t;;

val zero_outside : t -> unit;;

val to_string : t -> (string * int * int);;
val of_string : (string * int * int) -> t;;

val print1 : t -> unit;;
val print2 : Format.formatter -> t -> unit;;

val eq_by_bits : t -> t -> bool;;
val eq_when_zeroed : t -> t -> bool;;

val copy : t -> t;;
