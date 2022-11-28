(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type unique
type ty = 
    | RECORD of (Symbol.symbol * ty) list * unique 
    | NIL 
    | INT 
    | STRING 
    | ARRAY of (ty * unique)
    | NAME of Symbol.symbol * ty option ref 
    | VOID (* obs: this is called UNIT in the textbook *)
    | ERROR  

val mkUnique: unit -> unique
val string_of_unique : unique -> string 