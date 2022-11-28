(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Types pretty printing interface *)

val string_of_type : ?max_unfolds:int -> Types.ty -> string 
val print_type : out_channel * Types.ty -> unit