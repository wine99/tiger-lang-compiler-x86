(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type symbol 
val symbol: string -> symbol
val name: symbol -> string
type 'a table
val empty: 'a table
val enter: 'a table * symbol * 'a -> 'a table
val look: 'a table * symbol -> 'a option
val numItems: 'a table -> int
