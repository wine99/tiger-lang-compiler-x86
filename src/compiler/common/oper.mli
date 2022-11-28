(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

type oper 
  = EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp | PlusOp 
  | MinusOp | TimesOp | DivideOp | ExponentOp 

val opname: oper -> string 
