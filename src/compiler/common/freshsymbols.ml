(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

module S = Symbol 

type freshsymenv = {fresh_counter: int ref } 

let gensym {fresh_counter} s = 
  let c = !fresh_counter in 
    fresh_counter := c + 1 ;
    S.symbol @@ s ^ "_$_" ^ string_of_int c  

let empty = { fresh_counter = ref 0}    