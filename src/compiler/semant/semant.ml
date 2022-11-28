(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)
open Tigercommon
module S = Symbol
module A = Absyn
module E = Semenv
module Err = Errenv
module EFmt = ErrorFormatter
module Ty = Types
module PT = Prtypes
module TA = Tabsyn

(** Context record contains the environments we use in our translation *)

type context =
  { venv: E.enventry S.table (* Γ from our formal typing rules *)
  ; err: Err.errenv (* error environment *) }

exception NotImplemented
(* the final code should work without this exception *)

exception NotSem0 (* for handling AST cases outside of Sem 0 feature set *)

open Ty
let rec transExp ({err; venv} : context) e =
  let rec trexp (A.Exp {exp_base; pos}) =
    let (^!) exp_base ty = TA.Exp {exp_base;pos;ty} in
    match exp_base with
    | A.IntExp n ->  TA.IntExp n ^! INT 
    | A.StringExp s -> TA.StringExp s ^! STRING 
    (* the above cases have been implemented in class *)
    | A.OpExp {left; oper; right} -> raise NotImplemented
    | A.CallExp _ -> raise NotImplemented
    | A.SeqExp _ -> raise NotImplemented
    | A.IfExp {test; thn; els= Some _} -> raise NotImplemented
    | A.WhileExp _ -> raise NotImplemented
    | A.LetExp _ -> raise NotImplemented
    | A.VarExp _ -> raise NotImplemented
    | A.AssignExp _ -> raise NotImplemented
    (* the rest of the cases do not need handling in Sem0 / Assignment 3 *)
    | _ -> raise NotSem0
  and trvar (A.Var{var_base;_}) = 
    match var_base with 
    | A.SimpleVar _ -> raise NotImplemented 
    | _ -> raise NotSem0
  in
  trexp e

and transDecl ({err; venv} : context) dec =
  match dec with
  | A.VarDec _ -> raise NotImplemented (* implement this *)
  (* the rest of the cases do not nede handling in Sem 0 / Assignment 3 *)
  | _ -> raise NotSem0

(* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  try (transExp {venv= E.baseVenv; err} e, err)
  with NotSem0 ->
    Err.error err Lexing.dummy_pos
      "found language feature that is not part of sem0" ;
    ( TA.Exp
        { exp_base= TA.IntExp 0 (* dummy value *)
        ; pos= Lexing.dummy_pos
        ; ty= Ty.ERROR }
    , err )
