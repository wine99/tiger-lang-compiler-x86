(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Types pretty printing implementation *)
open Ppcommon
module T = Types 


(* a set of symbols *)
module SS = Set.Make(struct 
                      type t = Symbol.symbol 
                      let compare = compare 
                    end) 

let rec asStringI unfolds max_unfolds seen ty =
  let asStringI' = asStringI (unfolds + 1) max_unfolds in (* increment of unfolds *)
  match ty with 
    T.RECORD (fields, _) -> 
     let fieldString (s, ty) = 
        concat [ string_of_symbol s; ": "; asStringI' seen ty] in 
     let fieldsString = String.concat ", " (List.map fieldString fields) 
     in concat [ "RECORD {"; fieldsString; "}" ]
  | T.NIL -> "NIL" 
  | T.INT -> "INT"
  | T.STRING -> "STRING" 
  | T.ARRAY (ty1, _) -> concat [ "ARRAY of "; asStringI'  seen ty1]
  | T.NAME (s, tyor) -> 
    let hasBeenSeen = SS.mem s seen in 
    if hasBeenSeen then concat ["NAME " ; string_of_symbol s ] 
    else if unfolds <= max_unfolds then 
           let tyAsStringI = match  !tyor with 
                               Some ty -> asStringI' (SS.add s seen) ty 
                             | None -> "(NONE)"
           in concat ["NAME "; string_of_symbol s; " = "; tyAsStringI] 
         else concat ["NAME "; string_of_symbol s] 
  | T.VOID -> "VOID"
  | T.ERROR -> "ERROR"


let string_of_type ?(max_unfolds=0) ty = asStringI 0 max_unfolds SS.empty ty 

let print_type (outchan, ty) = 
  Printf.fprintf outchan "%s\n" (string_of_type ty)
   