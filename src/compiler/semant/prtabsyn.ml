(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Typed AST pretty printer implementation *)

open Tigercommon
module S = Symbol

open Tabsyn
open Prtypes
open Ppcommon

let field (Arg { name; escape; _}, d) = 
    concat [ indent d; "("; string_of_symbol name; ","
                     ; string_of_bool !escape; ")"]   

(* uses buffer to get quasi-linear time string concatenation (compared to quadratic time) *)
let as_string max_unfolds e0 = 
  let buf = Buffer.create 100 in
  let add = Buffer.add_string buf in

  let rec dolist d f ls: unit = match ls with
    |  [a] -> add "\n"; f (a, d + 1)
    |  a::r -> add "\n"; f (a, d + 1); add ","; dolist d f r
    |  []  -> () in

  let rec exp (Exp{exp_base;ty;_}, d): unit =
    add @@ concat [indent d; "("; string_of_type ~max_unfolds ty; ",\n"]; exp_desc (exp_base, d+1); add ")"
  and exp_desc (e,d) = add @@ indent d; match e with
    | VarExp v -> add "VarExp(\n"; var (v, d+1); add ")"
    | IntExp i -> add @@ concat ["IntExp("; string_of_int i; ")"]
    | NilExp -> add "NilExp"
    | StringExp s -> add @@ concat ["StringExp(\""; String.escaped s ; "\")"]
    | CallExp { func; args; _ } -> 
        add @@ concat [ "CallExp("; string_of_symbol func; ",[" ];
        dolist d exp args;
        add "])"
    | OpExp {left; oper; right} -> 
        add @@ concat [ "OpExp("; opname oper; ",\n" ];
        exp (left, d+1); add ",\n"; exp (right, d + 1); add ")"
    | RecordExp { fields } ->
       let f ((name, e), d) = 
         add @@ concat [indent d; "("; string_of_symbol name; ",\n"]; exp (e, d + 1); add ")"
       in add "RecordExp(["; dolist d f fields; add "])"
    | SeqExp l -> 
        add "SeqExp["; dolist d exp l; add "]"
    | AssignExp { var = v; exp = e } -> 
        add "AssignExp(\n"; var (v, d + 1); add ",\n"; exp (e, d + 1 ); add ")"
    | IfExp { test; thn; els }    -> 
        add "IfExp(\n"; exp (test, d + 1); add ",\n"; exp (thn, d + 1);
        (match els with None -> () | Some e -> add ",\n"; exp (e, d + 1)); add ")"
    | WhileExp {test; body} -> 
        add "WhileExp(\n"; exp (test, d + 1); add ",\n"; exp (body, d + 1); add ")"
    | ForExp { var = v; escape = b; lo; hi; body } -> 
        add @@ concat [ "ForExp("; string_of_symbol v; ","; string_of_bool (!b); ",\n" ];
        exp (lo, d + 1); add ",\n";
        exp (hi, d + 1); add ",\n";
        exp (body, d + 1); add ")"
    | BreakExp -> add "BreakExp"
    | LetExp {decls; body } -> 
        add "LetExp(["; dolist d dec decls; add "],\n"; exp (body, d + 1); add ")"
    | ArrayExp {size;init} -> 
        add "ArrayExp(\n"; exp (size, d + 1); add ",\n"; exp (init, d + 1); add ")"
    | ErrorExp -> add "ErrorExp"

  and dec (theDec,d) = add @@ indent d; match theDec with
    | FunctionDec l -> 
        let f ( Fdecl {name; args; result; body; _}, d ) =
          add @@ concat [ indent d; "("; string_of_symbol name; ",[" ]; dolist d (fun x -> add @@ field x) args;
          add @@ concat [ "],\n"; indent (d + 1); string_of_type ~max_unfolds result; ",\n" ];
          exp (body, d + 1); add ")" in
        add "FunctionDec["; dolist d f l; add "]"
    | VarDec { name; escape; typ; init; _ } ->
        add @@ concat [ "VarDec("; string_of_symbol name; ","; string_of_bool !escape; ","
              ; string_of_type ~max_unfolds typ; ",\n" ];
        exp (init, d + 1); add ")"
    | TypeDec l -> 
        let tdec ( Tdecl {name; ty=t; _}, d ) =
          add @@ concat [ indent d; "("; string_of_symbol name; ",\n"; ty (t, d + 1); ")"] in
        add "TypeDec["; dolist d tdec l; add "]"
  and ty (theType_, d) = concat [indent d; string_of_type ~max_unfolds theType_]
  
  and var (Var{var_base;ty;_}, d) = 
    add @@ concat [indent d; "("; string_of_type ~max_unfolds ty; ",\n"]; var_desc (var_base, d+1); add ")"
  and var_desc (e, d) = add @@ indent d; match e with
    | SimpleVar s -> 
        add @@ concat ["SimpleVar("; string_of_symbol s; ")"]
    | FieldVar (v,s) -> 
        add "FieldVar(\n" ; var (v, d + 1 ); add ",\n";
        add @@ concat [indent (d + 1); string_of_symbol s; ")"]
    | SubscriptVar (v, e) -> 
        add "SubscriptVar(\n"; var (v, d + 1); add ",\n";
        exp (e, d + 1); add ")"
  in (exp (e0, 0); Buffer.contents buf)

let string_of_exp = as_string  
let print_exp max_unfolds out e = Format.fprintf out "%s\n" (as_string max_unfolds e)
