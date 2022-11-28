(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** AST pretty printer implementation *)

module S = Symbol

open Absyn 
open Ppcommon


(* observe that merlin does not handle this function definition properly; aa; 2019-08-07; *)  
let field (Field { name; escape; typ; _}, d) = 
    concat [ indent d; "("; string_of_symbol name; ","
                     ; string_of_bool !escape; ","; string_of_symbol @@ fst typ; ")"]  


(* uses buffer to get quasi-linear time string concatenation (compared to quadratic time) *)
let as_string e0 = 
  let buf = Buffer.create 100 in
  let add = Buffer.add_string buf in

  let rec dolist d f ls: unit = match ls with
    |  [a] -> add "\n"; f (a, d + 1)
    |  a::r -> add "\n"; f (a, d + 1); add ","; dolist d f r
    |  []  -> () in

  let rec exp (Exp{exp_base;_}, d): unit = add @@ indent d; match exp_base with
    | VarExp v -> add "VarExp(\n"; var (v, d+1); add ")"
    | IntExp i -> add @@ concat ["IntExp("; string_of_int i; ")"]
    | NilExp -> add "NilExp"
    | StringExp s -> add @@ concat ["StringExp(\""; String.escaped s ; "\")"]
    | CallExp { func; args; _ } -> 
        add @@ concat [ "CallExp("; string_of_symbol func; ",[" ];
        dolist d exp args; add "])"
    | OpExp {left; oper; right; _} -> 
        add @@ concat [ "OpExp("; opname oper; ",\n" ];
        exp (left, d+1); add ",\n"; exp (right, d + 1); add ")"
    | RecordExp { fields; typ; _ } -> 
       let f ((name, e), d) = 
         add @@ concat [indent d; "("; string_of_symbol name; ",\n"]; exp (e, d + 1); add ")"
       in add @@ concat [ "RecordExp("; string_of_symbol typ; ",[" ]; dolist d f fields; add "])"
    | SeqExp l -> 
        add "SeqExp["; dolist d exp l; add "]"
    | AssignExp { var = v; exp = e; _} -> 
        add "AssignExp(\n"; var (v, d + 1); add ",\n"; exp (e, d + 1 ); add ")"
    | IfExp { test; thn; els; _ }    -> 
        add "IfExp(\n"; exp (test, d + 1); add ",\n"; exp (thn, d + 1);
        (match els with None -> () | Some e -> add ",\n"; exp (e, d + 1)); add ")"
    | WhileExp {test; body; _} -> 
        add "WhileExp(\n"; exp (test, d + 1); add ",\n"; exp (body, d + 1); add ")"
    | ForExp { var = v; escape = b; lo; hi; body; _} -> 
        add @@ concat [ "ForExp("
                      ; string_of_symbol v
                      ; ","; string_of_bool (!b) ];
        add ",\n"; exp (lo, d + 1);
        add ",\n"; exp (hi, d + 1);
        add ",\n"; exp (body, d + 1);
        add ")"
    | BreakExp -> add "BreakExp"
    | LetExp {decls; body; _} -> 
        add "LetExp(["; dolist d dec decls; add "],\n"; exp (body, d + 1); add ")"
    | ArrayExp {typ; size; init; _} -> 
        add @@ concat [ "ArrayExp("; string_of_symbol typ; ",\n" ];
        exp (size, d + 1); add ",\n"; exp (init, d + 1); add ")"


  and dec (theDec,d): unit = add @@ indent d; match theDec with
    | FunctionDec l -> 
       
       let f ( Fdecl {name; params; result; body; _}, d ) = 
         add @@ concat [ indent d; "("; string_of_symbol name; ",[" ];
         dolist d (fun x -> add @@ field x) params;
         add @@ concat [ "],\n"
                       ; indent (d + 1)
                       ; (match result with | None -> "NONE" | Some (s,_) -> "SOME(" ^ string_of_symbol s ^ ")" )
                       ; ",\n" ];
         exp (body, d + 1); add ")" in
       add "FunctionDec["; dolist d f l; add "]"

    | VarDec { name; escape; typ; init; _ } -> 
        add @@ concat [ "VarDec("; string_of_symbol name; ","; string_of_bool !escape; ","
                      ; (match typ with | None -> "NONE" | Some (s,_) -> "SOME(" ^ string_of_symbol s ^ ")" )
                      ; ",\n" ];
        exp (init, d + 1); add ")"
        
    | TypeDec l -> 
         let tdec ( Tdecl {name; ty=t; _}, d ) = 
           add @@ concat [ indent d; "("; string_of_symbol name; ",\n" ];
           ty (t, d + 1); add ")" in
         add "TypeDec["; dolist d tdec l; add "]"

  and ty (theType_, d): unit = add @@ indent d; match theType_ with
    | NameTy (s, _) -> add @@ concat ["NameTy("; string_of_symbol s; ")"]
    | RecordTy l -> add "RecordTy["; dolist d (fun x -> add @@ field x) l; add "]"
    | ArrayTy (s, _) -> add @@ concat ["ArrayTy("; string_of_symbol s; ")"]
  

  and var (Var{var_base;_}, d): unit = add @@ indent d; match var_base with
    | SimpleVar s -> 
        add @@ concat ["SimpleVar("; string_of_symbol s; ")"]
    | FieldVar (v,s) -> 
        add "FieldVar(\n"; var (v, d + 1 );
        add @@ concat [",\n"; indent (d + 1); string_of_symbol s; ")"]
    | SubscriptVar (v, e) -> 
        add "SubscriptVar(\n"; var (v, d + 1); add ",\n";
        exp (e, d + 1); add ")"
  in (exp (e0, 0); Buffer.contents buf)


let string_of_exp = as_string  
let print_exp out e = Format.fprintf out "%s\n" (as_string e)
