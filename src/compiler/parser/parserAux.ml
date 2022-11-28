(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** This module implements auxiliary functions for the parser. *)

open Tigercommon
open Absyn

let (^!) exp_base pos = Exp {exp_base;pos}
let (^@) var_base pos = Var {var_base;pos}

(* --- On parsing l-values -------------------------------------------------

Recall the definition of l-values from Appel's textbook, page 515:

    lvalue -> id
           -> lvalue . id
           -> lvalue [ exp ]

Note that the definition of l-value is inductive. Here, the (id) on the first
line is the base case, and the two inductive cases correspond to records and
arrays. Observe also how in each of the inductive cases, (lvalue) occurs
exactly once.

We may use these observations when parsing l-values. For this, we define an
auxiliary type lvaluePartSpec that specifies the "information part" of the two
inductive cases.
*)

type lvaluePartSpec
  = FieldPart of symbol
  | SubscriptPart of exp

;;

(* Consider, for example, a complex l-value such as

    x.foo[42].bar[i]

With the type lvaluePartSpec above, the inductive parts of this l-value can be
represented in a reversed list as follows (obs: mild abuse w.r.t. pos and
symbols in the AST).

    [ SubscriptPart (VarExp (SimpleVar "i"))
    ; FieldPart "bar"
    ; SubscriptPart (IntExp 42)
    ; FieldPart "foo"]

Given this list, we only need the information about the base case -- that is
the identifier "x" -- to construct an AST node corresponding to the l-value.


The following function implements the AST construction for l-values. The first
argument corresponds to the already constructed part -- hence its type is
Absyn.var; and the third argument is an lvaluePartSpec list. Note how the
recursive nature of this function corresponds to the inductive definition of
l-value.

*)

let rec makeLvaluePartSpec (v:Absyn.var) pos (ls:lvaluePartSpec list) =
  match ls with
  | l::r -> (
      match l with
        | FieldPart idsym ->
            makeLvaluePartSpec (FieldVar (v, idsym) ^@ pos) pos r
        | SubscriptPart exp ->
            makeLvaluePartSpec (SubscriptVar (v, exp) ^@ pos) pos r
      )
  | _ -> v

(* You may use the above helper definitions in the semantic actions of
   your parser when dealing with l-values *)

