(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

open Tigercommon 
open Habsyn
(* open Fmt  *)
module S = Symbol

exception Impossible

let fresh_counter = ref 0

let genname s = 
  let c = !fresh_counter in 
    fresh_counter := c + 1 ;
    "_" ^ s ^ "_" ^ string_of_int c

let _locals = "$locals"
let _sl = "$sl"

let oper_to_string = function 
  EqOp  -> "=="
| NeqOp -> "!="
| LtOp  -> "<"
| LeOp  -> "<="
| GtOp  -> ">"
| GeOp  -> ">="
| PlusOp  -> "+"
| MinusOp -> "-"
| TimesOp -> "*"
| DivideOp -> "/"
| ExponentOp -> raise Impossible

let pp_str s = fun pp _ -> Fmt.string pp s
let pp_sym s = pp_str (S.name s)
let pp_local s = pp_str @@ _locals ^ "." ^ (S.name s)

let pp_pos (pos:Lexing.position) = 
  let pos_col_relative (pos:Lexing.position) = pos.pos_cnum - pos.pos_bol + 1 in 
  Format.asprintf  "%s:%d:%d"
    pos.pos_fname pos.pos_lnum (pos_col_relative pos) 
  

let rec sl_chain = function 
    0 -> pp_str _locals
  | n when n > 0 -> let open Fmt in 
    sl_chain (n-1) ++ (pp_str ".") ++ (pp_str _sl)
  | _ -> raise Impossible
let pp_via_sl depth s = let open Fmt in 
   sl_chain depth ++ pp_str "." ++ pp_sym s

let ret x = let open Fmt in 
  hvbox (concat [
    hvbox ~indent:2 (pp_str "return (" ++ cut ++ x)
  ; pp_str ");"
  ])

let store v x = let open Fmt in 
  hvbox (concat [
    hvbox ~indent:2 (pp_str (v ^ " = ") ++ x ++ pp_str ";")
  ])

let arrow x = 
  let open Fmt in 
  concat [
    parens @@ 
      vbox @@ concat 
        [ vbox ~indent:2 @@ concat 
              [ hbox @@ concat [ parens nop ; pp_str " => { " ]
              ; x 
              ]
        ; pp_str "}"      
        ]
  ; pp_str "()"]

let id = Fun.id

let js_encode s = 
  let explode s = String.to_seq s |> List.of_seq in 
  let implode s = List.to_seq s |> String.of_seq in   
  let rec ase ls = match ls with     
      []  -> []
    | ('\\'::cs) -> '\\' :: '\\' :: (ase cs)
    | ('\"'::cs) -> 
        let charsc = "x" ^ Format.asprintf "%02X" (Char.code('\"')) in 
        '\\' :: (explode charsc) @ (ase cs)
    | (c::cs) -> 
        let ordc = Char.code c in 
        let charsc = "x" ^ Format.asprintf "%02X" ordc in 
        if 32 <= ordc && ordc < 128 then c :: (ase cs) 
        else '\\':: (explode charsc) @ (ase cs) in    
  s |> explode |> ase |> implode 

let rec exp_to_js (k:'a Fmt.t -> 'a Fmt.t) pfy (Exp{exp_base;pos;ty}) =   
  let k' arg = k arg pfy () in (* applying k *)
  match exp_base with 
  | VarExp v -> (pp_var k v) pfy ()
  | NilExp -> k' @@ pp_str "null"
  | IntExp n -> k' @@ fun pfy _ -> Fmt.int pfy n
  | StringExp s -> k' @@ Fmt.quote (pp_str (js_encode s))
  | OpExp{left; oper=ExponentOp; right} ->
      let left_let = genname "left" in
      let right_let = genname "right" in
      let open Fmt in
      vbox (concat
        [ pp_str @@ "let " ^ left_let ^ ", " ^ right_let ^";"
        ; pp_exp (store left_let) left
        ; pp_exp (store right_let) right
        ; k @@ parens(
          pp_str "Math.pow" ++
          parens(
          pp_str left_let ++ 
          pp_str "," ++ 
          pp_str right_let
          )
        )
        ]) pfy ()
  | OpExp{left; oper; right} ->
      let left_let = genname "left" in
      let right_let = genname "right" in
      let open Fmt in
      vbox (concat
        [ pp_str @@ "let " ^ left_let ^ ", " ^ right_let ^";"
        ; pp_exp (store left_let) left
        ; pp_exp (store right_let) right
        ; k @@ parens(
          pp_str left_let ++ 
          pp_str (oper_to_string oper) ++ 
          pp_str right_let
          ++ pp_str begin match oper with
          | DivideOp | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp -> "|0"
          | _ -> ""
          end
        )
        ]) pfy ()
  | LetExp{vardecl = (VarDec{name;init;_});body} ->   
    let open Fmt in 
    vbox (concat [        
        pp_exp (bindsym name) init
      ; pp_exp k body 
    ]) pfy ()
  | SeqExp [] -> k' Fmt.nop 
  | SeqExp [e] -> exp_to_js k pfy e
  | SeqExp (e::exps) ->
      exp_to_js id pfy e; 
      Fmt.semi pfy ();
      (exp_to_js k pfy (Exp{exp_base = SeqExp exps;pos; ty}))
  | IfExp{test;thn;els=Some els} when ty != VOID  ->
      let name = genname "cnd" in
      let open Fmt in
        (vbox (concat [
        vbox ~indent:2 @@ concat 
        [ vbox @@
          concat ~sep:sp
          [ pp_str @@ "let " ^ name ^";"
          ; pp_exp (store name) test
          ; pp_str @@ "if (" ^ name ^ ") {" ]
        ; pp_exp k thn
        ]
      ; vbox ~indent:2 @@ concat 
        [ hbox @@ concat [ pp_str "} else {" ]
        ; pp_exp k els 
        ]
      ; pp_str "} "
      ])) pfy ()
  | IfExp{test;thn;els = Some els} -> 
      let name = genname "cnd" in
      let open Fmt in 
      (vbox (concat [
        vbox ~indent:2 @@ concat 
        [ vbox @@
          concat ~sep:sp
          [ pp_str @@ "let " ^ name ^";"
          ; pp_exp (store name) test
          ; pp_str @@ "if (" ^ name ^ ") {" ]
        ; pp_exp id thn
        ]
      ; vbox ~indent:2 @@ concat 
        [ hbox @@ concat [ pp_str "} else {" ]
        ; pp_exp id els 
        ]
      ; pp_str "}"
      ])) pfy ()
  | IfExp{test;thn;els = None} -> 
      let name = genname "cnd" in
      let open Fmt in 
      (vbox (concat [
        vbox ~indent:2 @@ concat 
        [ vbox @@
          concat ~sep:sp
          [ pp_str @@ "let " ^ name ^";"
          ; pp_exp (store name) test
          ; pp_str @@ "if (" ^ name ^ ") {" ]
        ; pp_exp id thn
        ]
      ;  pp_str "}" 
      ])) pfy ()

  | CallExp{func;lvl_diff;args} -> let open Fmt in 
    let sl = sl_chain lvl_diff in 
    let arg_lets =
      List.init (List.length args) (fun i -> genname ("arg" ^ string_of_int i)) in
    let pp_args_lets =
      pp_str @@ "let " ^ String.concat ", " arg_lets in
    let pp_store_args =
      concat @@ List.mapi (fun i exp -> pp_exp (store @@ List.nth arg_lets i) exp) args in
    let pp_args =
      List.map (fun s -> pp_str s) arg_lets in
    let pp_arg_exps = sl :: pp_args in

    (concat ~sep:semi
    [ if List.length args = 0
      then nop
      else concat ~sep:semi[pp_args_lets; pp_store_args]
    ; concat ~sep:semi
      [ k @@ parens @@ hbox @@ concat
        [ pp_str "await" ; sp ; pp_sym func
        ; parens @@ concat ~sep:comma pp_arg_exps    
        ]
      ]
    ]) pfy ()
  
  | AssignExp{var;exp} -> 
      (pp_exp (setvar var) exp) pfy ()

  | RecordExp{fields} -> let open Fmt in 
    let field_lets =
      List.init (List.length fields) (fun i -> genname ("field" ^ string_of_int i)) in
    let pp_field_lets =
      pp_str @@ "let " ^ String.concat ", " field_lets in
    let pp_store_field i (_,e) =
      pp_exp (store @@ List.nth field_lets i) e in
    let pp_store_fields = concat @@ List.mapi pp_store_field fields in
    let pp_fields =
      List.map (fun s -> pp_str s) field_lets in
    let field_to_js i (s, _) = 
        hvbox @@ concat [pp_sym s ; pp_str ":" ; List.nth pp_fields i] in 
    let fields = List.mapi field_to_js fields  in 
    (concat ~sep:semi @@
    [ if List.length fields = 0
      then nop
      else concat ~sep:semi[pp_field_lets; pp_store_fields]
    ; k @@ braces @@ hbox @@ concat ~sep:comma fields
    ]) pfy ()
    
 
  | ArrayExp{size;init} -> let open Fmt in 
      let size_let = genname "size" in
      let init_let = genname "init" in
      (concat 
        [ pp_str @@ "let " ^ size_let ^";"
        ; pp_exp (store size_let) size
        ; pp_str @@ "let " ^ init_let ^";"
        ; pp_exp (store init_let) init
        ; k @@ concat
          [ pp_str "Array("
          ; pp_str size_let
          ; pp_str ").fill("
          ; pp_str init_let
          ; pp_str ")" ]
        ]) pfy ()

  | WhileExp{test=Exp{exp_base=SeqExp test_exps;pos;_};body} when List.length test_exps > 1 ->
    let (test_intro,test_res) = 
      test_exps 
      |> List.rev 
      |> (fun ls -> (List.rev @@ List.tl ls, List.hd ls)) in
    let name = genname "cnd" in
    let open Fmt in 
      (vbox @@ concat 
      [ vbox ~indent:2 @@ concat 
        [ vbox @@ concat
          [ pp_exp id (Exp{exp_base=SeqExp test_intro;pos;ty=VOID})
          ; pp_str @@ "let " ^ name ^ ";"
          ; pp_exp (store name) test_res
          ; pp_str @@ "while (" ^ name ^ ") {" ]
        ; pp_exp id body
        ; pp_exp id @@ Exp{exp_base=SeqExp test_intro;pos;ty=VOID}
        ; pp_exp (store name) test_res
        ]
      ; pp_str "}"
      ]) pfy ()

  | WhileExp{test;body} -> (
      let name = genname "cnd" in
      let open Fmt in 
      vbox @@ concat 
      [ vbox ~indent:2 @@ concat 
        [ vbox @@ concat
          [ pp_str @@ "let " ^ name ^";"
          ; pp_exp (store name) test
          ; pp_str @@ "while (" ^ name ^ ") {" ]
        ; vbox @@ concat ~sep:semi
          [ pp_exp id body
          ; pp_exp (store name) test ]
        ]
      ; pp_str "}"  
      ]) pfy ()
  
  | BreakExp -> pp_str "break;"  pfy ()



and pp_exp k e = (fun pfy _ -> exp_to_js k pfy e)

and var_to_js k (pfy:Format.formatter) (Var{var_base;pos;_}): unit = 
  match var_base with 
  | AccessVar(0, s) -> k (pp_local s) pfy ()
  | AccessVar (depth, s) -> 
      k (pp_via_sl depth s) pfy ()
  | SubscriptVar (var,exp) -> let open Fmt in 
      let index = genname "index" in
      let svar = genname "svar" in
      (vbox @@ concat
      [ pp_str @@ "let " ^ index ^ ", " ^ svar ^ ";"
      ; pp_exp (store index) exp
      ; pp_var (store svar) var
      ; vbox ~indent:2 @@ concat ~sep:sp
        [ pp_str @@ "if (" ^ index ^ " < 0 || " ^ svar ^ ".length <= " ^ index ^ ")"
        ; pp_str "throw new TigerIndexOutOfRange();" ]
      ; k @@ pp_str svar ++ pp_str "[" ++ pp_str index  ++ pp_str "]"
      ]) pfy ()
  | FieldVar (var, s) -> let open Fmt in 
      let fvar = genname "fvar" in
      (vbox @@ concat
      [ pp_str @@ "let " ^ fvar ^";"
      ; pp_var (store fvar) var
      ; vbox ~indent:2 @@ concat ~sep:sp
        [ pp_str @@ "if (" ^ fvar ^ " == null)"
        ; pp_str "throw new TigerNilLookup";  
                pp_pos pos|> pp_str |> Fmt.quote |> Fmt.parens  ]
      ; k @@ pp_str fvar ++ pp_str "." ++ pp_sym s
      ]) pfy ()
  
and pp_var (k:'a Fmt.t -> 'a Fmt.t) (v:var) = (fun pfy _ -> var_to_js k pfy v)

and bindsym s x = let open Fmt in 
  hbox @@ concat [pp_local s ; sp;  pp_str "="; sp; x; pp_str ";" ]

and setvar (var:var) x = let open Fmt in 
  hbox @@ concat [ pp_var id var ; sp;  pp_str "="; sp; x; pp_str ";" ]

let fdecl_to_js (ppf:Format.formatter) (Fdecl{name;body;args;result=res_ty;_}) =  
  let pp_arg_names = 
    pp_str _sl :: 
    List.map (fun (Arg{name;_}) -> pp_sym name) args in 
  let open Fmt in   
  Fmt.concat [
    vbox ~indent:2 (
      Fmt.concat ([( 
          Fmt.hbox (Fmt.concat [
            pp_str "async function" ++ sp ++pp_str (S.name name)
          ; Fmt.parens (Fmt.concat ~sep:Fmt.comma (pp_arg_names))
          ; pp_str "{"
          ]             
        ))
      ; pp_str ("let " ^ _locals ^ " = {};") ]
      @ List.map ( fun a -> pp_str 
                          (_locals ^ ".")  ++ a ++ pp_str " = " ++ a ++ pp_str ";"
                          ) pp_arg_names 
      @ match res_ty with
      | Types.VOID -> [ pp_exp id body ]
      | _-> [ pp_exp ret body ]))
  ; pp_str "}"  
  ; nop 
  ] ppf ()

let to_js' (fmt:Format.formatter) (Program{fdecls;_}) =     
    List.iter (fdecl_to_js fmt) fdecls

let to_js file = 
  let open Fmt in
  let header = Stdio.In_channel.read_all "src/compiler/hoist/html/header.html" in 
  let footer = Stdio.In_channel.read_all "src/compiler/hoist/html/footer.html" in 
  let title = String.concat "" ["<script>document.title = 'TigerJS: "; file; "';</script>"] in

  vbox ~indent:0 @@ concat [pp_str header; to_js'; pp_str footer; pp_str title]

