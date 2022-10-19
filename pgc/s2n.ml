(* 256 bit long sequences of bytes modulo sec256k1 p *)

type t;;

(* Functions used to convert to and from Z._strings *)
external of_lebits : string -> t = "c_s2n_of_le_string";;
external to_lebits : t -> string = "c_s2n_to_le_string";;

external of_int32p8 : int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 -> t = "c_s2n_of_int32p8";;
external to_int32p8 : t -> int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 = "c_s2n_to_int32p8";;

external of_int : int -> t = "c_s2n_of_int";;

external modinv_n : t -> t = "c_s2n_modinv_n";;
external modinv_p : t -> t = "c_s2n_modinv_p";;

external iseven : t -> bool = "c_s2n_iseven";;
external iszero : t -> bool = "c_s2n_iszero";;
external eq : t -> t -> bool = "c_s2n_eq";;
external gt : t -> t -> bool = "c_s2n_gt";;

