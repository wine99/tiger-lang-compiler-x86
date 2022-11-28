(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon 
module S = Symbol 
module Ty = Types

type enventry 
  = VarEntry of Types.ty 
  | FunEntry of { formals: Types.ty list; result: Types.ty }



let baseVenv = S.empty 
