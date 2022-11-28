(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type oper 
  = EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp | PlusOp 
  | MinusOp | TimesOp | DivideOp | ExponentOp 

let opname = function 
  EqOp  -> "EqOp"
| NeqOp -> "NeqOp"
| LtOp  -> "LtOp"
| LeOp  -> "LeOp"
| GtOp  -> "GtOp"
| GeOp  -> "GeOp"
| PlusOp  -> "PlusOp"
| MinusOp -> "MinusOp"
| TimesOp -> "TimesOp"
| DivideOp -> "DivideOp"
| ExponentOp -> "ExponentOp"

