(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)
open Tigercommon
type pos = Lexing.position 
type symbol = Symbol.symbol

module T=Types 

include Oper (* note that this re-exports the definitions of operations *)


type var_base 
  = SimpleVar of symbol 
  | FieldVar of var * symbol
  | SubscriptVar of var * exp
and var = Var of { var_base: var_base; pos: pos; ty: T.ty }
and exp = Exp of { exp_base: exp_base; pos: pos; ty: T.ty } 
and exp_base
  = VarExp of var
  | NilExp
  | IntExp of int
  | StringExp of string 
  | CallExp of { func: symbol; args: exp list }   
  | OpExp of { left: exp; oper: oper; right: exp }  
  | RecordExp of { fields: (symbol * exp) list } 
  | SeqExp of exp list 
  | AssignExp of { var: var; exp: exp }  
  | IfExp of { test: exp; thn: exp; els: exp option }  
  | WhileExp of { test: exp; body: exp  }
  | ForExp of { var: symbol; escape: bool ref; lo: exp; hi: exp
              ; body: exp  } 
  | BreakExp
  | LetExp of { decls:decl list; body: exp }
  | ArrayExp of { size: exp; init :exp } 
and decl 
  = FunctionDec of fundecldata list 
  | VarDec of 
      { name: symbol
      ; escape: bool ref
      ; typ: Types.ty
      ; init: exp
      ; pos: pos 
      }
  | TypeDec of tydecldata list
and tydecldata = Tdecl of { name: symbol; ty: Types.ty ; pos: pos }
and fundecldata = Fdecl of   
      { name: symbol
      ; args: argdata list
      ; result: Types.ty 
      ; body: exp 
      ; pos: pos 
      }
and argdata = 
    Arg of { name: symbol; escape: bool ref; ty: Types.ty ; pos: pos } 
