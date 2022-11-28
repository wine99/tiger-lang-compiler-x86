(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Error environment interface *)

type errenv 
exception CompilerError of string 

val error: errenv -> Lexing.position -> string -> unit 
val impossible: string -> 'a
val any_errors: errenv -> bool 
val initial_env: errenv