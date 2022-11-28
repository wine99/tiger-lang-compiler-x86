(**************************************************************************)
(* AU Compilation. This file needs no modifications                       *)
(**************************************************************************)

type pos = Lexing.position 
type symbol = Symbol.symbol
include Oper (* note that this re-exports the definitions of operations *)


(* Note the use of Ocaml inline records in our AST declaration 
  https://caml.inria.fr/pub/docs/manual-ocaml/manual040.html *)

type var_base
  = SimpleVar of symbol
  | FieldVar of var * symbol
  | SubscriptVar of var * exp
and var = Var of { var_base: var_base; pos: pos }
and exp = Exp of { exp_base: exp_base; pos: pos }
and exp_base
  = VarExp of var
  | NilExp
  | IntExp of int
  | StringExp of string 
  | CallExp of { func: symbol; args: exp list }   
  | OpExp of { left: exp; oper: oper; right: exp  }  
  | RecordExp of { fields: (symbol * exp) list; typ: symbol } 
  | SeqExp of exp list 
  | AssignExp of { var: var; exp: exp }  
  | IfExp of { test: exp; thn: exp; els: exp option }  
  | WhileExp of { test: exp; body: exp  }
  | ForExp of { var: symbol; escape: bool ref; lo: exp; hi: exp
              ; body: exp  } 
  | BreakExp
  | LetExp of { decls:decl list; body: exp }
  | ArrayExp of { typ: symbol; size: exp; init: exp } 
and decl 
  = FunctionDec of fundecldata list 
  | VarDec of 
      { name: symbol
      ; escape: bool ref
      ; typ: (symbol * pos) option
      ; init: exp
      ; pos: pos
      }
  | TypeDec of tydecldata list
and tydecldata = Tdecl of { name: symbol; ty: ty ; pos: pos }
and fundecldata = Fdecl of   
      { name: symbol
      ; params: fielddata list
      ; result: (symbol * pos) option
      ; body: exp 
      ; pos: pos 
      }
and fielddata = 
    Field of { name: symbol; escape: bool ref; typ: symbol * pos; pos: pos } 
and ty
  = NameTy of symbol  * pos 
  | RecordTy of fielddata list 
  | ArrayTy of symbol * pos
