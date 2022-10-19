open Mlgdbm;;

let db = dbopen "bin/testdatabase.pag";;

replace db "a" "aaaaaaa";;
replace db "b" "b";;
Printf.printf "find a = %s\n" (find db "a");;
Printf.printf "find c? %b\n" ((find_opt db "c") = None);;
Printf.printf "exists b = %b\n" (exists db "b");;
sync db;;
replace db "a" "aaaaaaaaaaaaaaa";;
Printf.printf "find a = %s\n" (find db "a");;

let fk = firstkey db;;
Printf.printf "firstkey=%s\n" fk;;
let nk = nextkey db fk;;
Printf.printf "nextkey=%s\n" nk;;
try ignore (nextkey db nk); failwith "!" with Not_found -> Printf.printf "nextkey Not_Found\n";;

replace db "c" (Marshal.to_string (Int32.of_int 3) [Marshal.No_sharing;Marshal.Compat_32])
let i = (find_unmarshal db "c" : int32);;
Printf.printf "find c->3 : %ld\n" i;;
