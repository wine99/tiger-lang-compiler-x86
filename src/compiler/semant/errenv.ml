(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Error environment implementation *)

type errenv = { mutable anyerrors: bool  }
exception CompilerError of string 

let pos_col_relative (pos:Lexing.position) = pos.pos_cnum - pos.pos_bol + 1

let error errenv (pos:Lexing.position) s =   
  errenv.anyerrors <- true;
  Printf.fprintf stderr "%s:%d:%d: %s\n"
    pos.pos_fname pos.pos_lnum (pos_col_relative pos) s
  (* failwith "FATAL?" *)


let impossible s = 
  Printf.fprintf stderr "Compiler error: %s" s; 
  raise (CompilerError s)

let any_errors errenv = errenv.anyerrors  

let initial_env = { anyerrors = false }

