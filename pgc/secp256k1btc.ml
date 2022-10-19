type pt;;
external curve_y : bool -> S2n.t -> pt = "c_secp256_curve_y";;
external pt_of_xy : S2n.t -> S2n.t -> pt = "c_secp256_pt_of_xy";;
external pt_to_xyo : pt -> (S2n.t * S2n.t) option = "c_secp256_pt_to_xyo";;
external smulp : S2n.t -> pt -> pt = "c_secp256_smulp";;
external add_pt : pt -> pt -> pt = "c_secp256_add_pt";;
