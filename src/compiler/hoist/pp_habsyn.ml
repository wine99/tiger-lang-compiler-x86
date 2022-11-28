open Tigercommon
open Habsyn


let binop_to_str = function 
  EqOp  -> "="
| NeqOp -> "<>"
| LtOp  -> "<"
| LeOp  -> "<="
| GtOp  -> ">"
| GeOp  -> ">="
| PlusOp  -> "+"
| MinusOp -> "-"
| TimesOp -> "*"
| DivideOp -> "/"
| ExponentOp -> "^"


let str_ s = fun ppy _ -> Fmt.string ppy s 
let sym_ s = str_ (Symbol.name s )
let int_ i = fun fmt _ -> Fmt.int fmt i




let colon: unit Fmt.t  = str_ ":" 
exception NotImplemented 
exception Impossible
let rec pp_ty ?(unfold=false) ty = let open Types in let open Fmt in   
  match ty with 
    NIL -> str_ "nil"
  | INT -> str_ "int"
  | STRING -> str_ "string"
  | NAME (s, rt) -> if unfold then !rt |> Option.get |> pp_ty else sym_ s   
  | RECORD (fields, _) ->      
      let f (s,ty) = sym_ s ++ colon ++ pp_ty ty in 
      let fs = List.map f fields in 
      fs |> concat ~sep:comma |> braces |> hvbox 
  | ARRAY (t,_) -> str_ "array of " ++ pp_ty t 
  | VOID -> str_ "void"
  | ERROR -> raise Impossible
              

let rec pp_exp' ?(inlet=false) (Exp{exp_base;ty;_}) = let open Fmt in 
  match exp_base with 
    | IntExp x -> int_ x 
    | NilExp -> str_ "nil"
    | VarExp x -> pp_var x
    | StringExp x -> x|> String.escaped |> str_ |> quote  
    | OpExp {left; right; oper; _ }->
      [pp_exp' left; binop_to_str oper |> str_;  pp_exp' right] 
          |> concat ~sep:sp |> hvbox ~indent:2 

    | LetExp {vardecl = VarDec{name;typ;init;_}; body; _} ->  
      [ [ str_ "let var"; (sym_ name ++ colon ++ pp_ty typ); str_ ":="; pp_exp' init; str_ "in" ] 
        |> concat ~sep:sp |> hvbox ~indent:2
      ;  pp_exp' ~inlet:true body
      ] |> concat |> vbox ~indent:0             
      
    | IfExp {test; thn; els;_} -> 
      let pp_els = match els with Some els -> concat ~sep:sp [str_ "else"; pp_exp' els ]| None -> nop in 
      let box1 =  [str_ "if";  pp_exp' test] |> concat~sep:sp |> hvbox ~indent:2 in 
      let box2 =  [str_ "then"; pp_exp' thn] |> concat~sep:sp |> hvbox ~indent:2 in 
      let box3 = pp_els |> hvbox ~indent:2 in 
      concat ~sep:sp [box1;box2;box3]  |> hvbox 

    | CallExp{func;lvl_diff;args;_} -> 
      let args = List.map pp_exp' args |> concat ~sep:comma |> parens in 
      [ sym_ func; str_ "@" ++ int_ lvl_diff ; args]  |> concat |> hvbox 

    | ArrayExp{size;init;_} -> 
      let pp_t = pp_ty ty in 
      [pp_t ; brackets (pp_exp' size) ; str_ " of " ; pp_exp' init ] |> concat |> hvbox 

    | RecordExp {fields;_} -> 
      let f (s, e) = [sym_ s; str_ "="; pp_exp' e] |> concat in 
      List.map f fields |> concat ~sep:comma |> braces |> hvbox 
    | BreakExp -> str_ "break"
    
    | AssignExp {var;exp;_} ->
      hbox @@ pp_var var ++ str_ " := " ++ pp_exp' exp 
    | SeqExp exps -> 
      List.map pp_exp' exps 
      |> concat ~sep:semi 
      |> hvbox |> (if inlet then id else parens )
    
    | WhileExp {test;body;_} -> 
      [ [str_ "while"; pp_exp' test; str_ "do"] |> concat ~sep:sp |> hvbox 
      ; pp_exp' body 
      ] |> concat |> hvbox ~indent:2
         

and pp_var (Var{var_base;_}) = let open Fmt in 
  match var_base with 
     AccessVar (0, s) -> sym_ s
   | AccessVar (i, s) -> sym_ s ++ str_ "<" ++ int_ i ++ str_ ">"

   | FieldVar (v,s) -> pp_var v ++ str_ "." ++ sym_ s 
   | SubscriptVar (v, e) -> pp_var v ++ (brackets (pp_exp' e)) 
   

let pp_exp = pp_exp'     


let pp_fdecl (Fdecl{name; args; result=r; body;_}) = 
  let open Fmt in 
  let pp_arg (Arg{name;ty;_}) = 
       hbox @@ sym_ name ++ colon ++  pp_ty ty in 
  let args = List.map pp_arg args |> concat ~sep:comma |> parens in 
  let ty' = if r = Types.VOID then nop else colon ++ pp_ty r in 
  concat
     [  [str_ "function "; sym_ name ; args ; ty'; str_ " =" ] |> concat ~sep:nop |> hvbox  
     ;  pp_exp body 
     ] |> vbox ~indent:2

let pp_tdecl (Tdecl{name; ty;_}) = let open Fmt in 
   [str_ "type"; sym_ name; str_ "="; pp_ty ~unfold:true ty] 
   |> concat ~sep:sp |> hvbox 
  
let pp_program (Program{tdecls; fdecls}) = 
  let open Fmt in 
  let ff = fdecls |> List.map pp_fdecl in 
  let tt = tdecls |> List.map pp_tdecl in 
  tt @ ff |> concat |> vbox 

let print_program out p = 
  pp_program p out ();
  Format.pp_print_newline out ();
