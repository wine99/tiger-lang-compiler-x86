(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)


(** This module contains some auxiliary functions used for pretty 
    printing. *)

let string_of_symbol = Symbol.name 
let concat = String.concat ""

let indent i = concat @@ List.init i (fun x -> if x mod 2 = 1 then "| " else "  ")
