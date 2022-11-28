(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type unique = int 
let unique_state = ref 0 

type ty = 
  | RECORD of (Symbol.symbol * ty) list * unique 
  | NIL 
  | INT 
  | STRING 
  | ARRAY of (ty * unique)
  | NAME of Symbol.symbol * ty option ref 
  | VOID
  | ERROR 

let mkUnique () = 
    let current = !unique_state in  
        unique_state := current + 1; 
        current 

let string_of_unique = string_of_int