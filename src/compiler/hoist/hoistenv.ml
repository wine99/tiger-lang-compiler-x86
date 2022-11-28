(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

open Tigercommon
module Ty = Types
module S = Symbol


let from_string_list ls =
  List.fold_left
    (fun t (k, v) -> S.enter (t, S.symbol k, v)) S.empty ls 
  
let baseTenv = from_string_list 
    [ ("int", Ty.INT); ("string", Ty.STRING)]

let baseVenv = List.fold_left 
    (fun t k -> 
        S.enter (t, S.symbol k, 0)) 
    S.empty 
    [ "print"
    ; "flush"
    ; "getChar"
    ; "ord"
    ; "chr"
    ; "size"
    ; "substring"
    ; "concat"
    ; "not"
    ; "tigerexit"
    ]