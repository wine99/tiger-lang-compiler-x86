(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

open Tigercommon
type pos = Lexing.position 
type symbol = Symbol.symbol 
type ty = Types.ty 

include Oper 

type var_base 
  = AccessVar of int * symbol
  | FieldVar of var * symbol
  | SubscriptVar of var * exp
and var = Var of { var_base : var_base; pos : pos; ty : ty }   
and exp = Exp of { exp_base : exp_base; pos : pos; ty : ty }
and exp_base 
  = VarExp of var 
  | NilExp
  | IntExp of int
  | StringExp of string
  | CallExp of { func: symbol; lvl_diff: int; args: exp list }   
  | OpExp of { left: exp; oper: oper; right: exp  }  
  | RecordExp of { fields: (symbol * exp) list } 
  | SeqExp of exp list 
  | AssignExp of { var: var; exp: exp }  
  | IfExp of { test: exp; thn: exp; els: exp option }  
  | WhileExp of { test: exp; body: exp }
  | BreakExp
  | LetExp of { vardecl: vardecl; body: exp }
  | ArrayExp of { size: exp; init :exp } 

and vardecl 
  = VarDec of 
    { name: symbol
    ; escape: bool ref
    ; typ: Types.ty
    ; init: exp
    ; pos: pos 
    }

type tydecldata = Tdecl of { name: symbol; ty: ty ; pos: pos }
   
type argdata = 
    Arg of { name: symbol; escape: bool ref; ty: ty; pos: pos } 

type fundecldata = Fdecl of   
      { name: symbol
      ; args: argdata list
      ; result: ty      
      ; body: exp 
      ; pos: pos 
      ; parent_opt: symbol option
      ; locals: (symbol * ty) list
      }

type program = 
  Program of 
  { tdecls : tydecldata list 
  ; fdecls : fundecldata list 
  }

(* for debugging purposes *)
let string_of_parents p = List.map Symbol.name p |> String.concat " | "
