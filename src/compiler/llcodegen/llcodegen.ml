(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon 
open Tigerhoist

module H = Habsyn
module Ty = Types
module S = Symbol
module B = Cfgbuilder

module SymbolMap = Map.Make 
    (struct type t = S.symbol let compare = compare end)
module UniqueMap = Map.Make 
    (struct type t = Ty.unique let compare = compare end)

type unique_env = Ll.tid UniqueMap.t  
type fdecl_summary =
  { parent_opt: Ll.gid option
  ; locals_uid: Ll.uid
  ; locals_tid: Ll.tid 
  ; offset_of_symbol: S.symbol -> int 
  }

type summary_env = fdecl_summary SymbolMap.t
exception NotImplemented
exception CodeGenerationBug 

let ty_to_llty = function 
| Ty.INT -> Ll.I64 
| _ -> raise NotImplemented

type context 
  = { break_lbl: Ll.lbl option     
    ; summary: fdecl_summary
    ; uenv: unique_env
    ; senv: summary_env
    ; gdecls: (Ll.gid * Ll.gdecl) list ref
    }

(* Obs: this is a rather tricky piece of code; 2019-10-12 *)
let cg_tydecl (_ :unique_env ref) (H.Tdecl{name; ty ; _}) = 
   match ty with 
     Ty.INT  -> Some (name, Ll.I64 )
  | _ -> raise NotImplemented


let fresh = let open Freshsymbols in let env = empty in gensym env

let ptr_i8 = Ll.Ptr Ll.I8 
let (<$>) f g x = f (g x)
let id = Fun.id
let ($>) b1 b2 = b2 <$> b1 (* buildlet composition *)
let (@>) (b,op) k = b $> k op
let ty_of_exp (H.Exp{ty;_}) = ty 
let ty_of_var (H.Var{ty;_}) = ty
let ty_of_arg (H.Arg{ty;_}) = ty
let name_of_arg (H.Arg{name;_}) = name 

let default_sl_name = S.symbol "$sl" 
let locals_type_name name = (S.symbol @@ "$locals_" ^ (S.name name))
let ty_dec_name name = (S.symbol @@ "t_$" ^ (S.name name)) 

(* add instruction with fresh symbol *)
let aiwf s i = 
  let t = fresh s in 
  B.add_insn (Some t, i), Ll.Id t 

(* --- monadic interface;) ----------------------------- *)

(* Notes on the monadic interface:

1) Monadic interface is not necessary at all, and one could just 
   program with buildlets as before; it's just a little bit more 
   concise, but one _really_ needs to know what they are doing.

2) Some useful info on the OCmal let* notation here
   http://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html 

3) Observe that the new OCaml notation conflicts with JaneStreet 
   pre-processors, so we don't have any pre-processing in this library.
*)

type 'a m = B.buildlet * 'a
let bind ((builder, op):'a m) (f:'a -> 'b m):'b m =
  let ( builder', op') = f op in 
  (builder $> builder', op')
let return x = (B.id_buildlet, x)  
let (let*) = bind
(* --- end of monadic interface ------------------------ *)

let unit b = (b, ())    
let build_store t o1 o2 = B.add_insn (None, Ll.Store (t,o1,o2))
let gep_0 ty op i = Ll.Gep (ty, op, [Const 0; Const i])

let rec cgExp ctxt (Exp{exp_base;_}:H.exp) : B.buildlet * Ll.operand (* Alternatively: Ll.operand m *) = 
  let cgE_ = cgExp ctxt in

  match exp_base with 
  | IntExp i -> (id, (Const i))

  | H.OpExp {left; right; oper; _}  -> 
    let (build_right, op_right) = cgE_ right in 
    let (build_left, op_left)  = cgE_ left  in 
    let bop = match oper with 
                  PlusOp -> Ll.Add 
                | MinusOp -> Ll.Sub
                | TimesOp -> Ll.Mul 
                |_ -> raise NotImplemented
              in
    let i = Ll.Binop (bop, Ll.I64, op_left, op_right ) in 
    let newid = fresh "temp"  in
    let builder = Cfgbuilder.add_insn (Some newid, i) in 
    let builder' = Cfgbuilder.seq_buildlets [ build_left; build_right; builder ]  in 
    (builder', Ll.Id newid)

    (* the above can be rewritten using the monadic interface and aux functions 
     as follows *)
    (*
    | H.OpExp {left; right; oper; _} ->
      let* op_left  = cgE_ left  in
      let* op_right = cgE_ right in 
      let bop = match oper with 
                    PlusOp -> Ll.Add 
                  | MinusOp -> Ll.Sub
                  | TimesOp -> Ll.Mul 
                  |_ -> raise NotImplemented
                in
      let i = Ll.Binop (bop, Ll.I64, op_left, op_right ) in 
      aiwf "temp" i
      *)

| _ -> raise NotImplemented

and cgVar (_ : context) (H.Var _) =
  raise NotImplemented

(* --- From this point on the code requires no changes --- *)

(* Creates summary of a function declaration; relies on the alpha conversion *)
let cg_fdecl_summary senv_ref ( H.Fdecl{name; parent_opt; locals; _}) = 
  let locals_uid = fresh "locals" in
  let locals_tid = locals_type_name name in 
  let offset_of_symbol = 
    let locals_map = default_sl_name :: (List.map fst locals) 
                     |> List.mapi (fun i x -> (x,i)) 
                     |> List.to_seq 
                     |> SymbolMap.of_seq in 
    fun sym -> SymbolMap.find sym locals_map in 
  senv_ref := SymbolMap.add name 
      {parent_opt; locals_uid; locals_tid; offset_of_symbol} !senv_ref;
  let sl_type = 
    match parent_opt with 
    | Some p -> Ll.Ptr (Ll.Namedt (p |> locals_type_name))
    | None -> Ll.Ptr I8 in  
  let locals_ty =
    Ll.Struct (sl_type:: List.map (fun (_, t) -> ty_to_llty t ) locals) in
  (locals_tid, locals_ty)

(* --- Code genartion of function bodies --- *)
let cg_fdecl senv uenv gdecls (H.Fdecl{name; args; result; body; _}) =
  (*  Function bodies are generated in 5 steps
      1. Creating the translation context
      2. Allocating the locals structure with all the variables
      3. Copying the arguments to the locals
      4. Generating the code for the function body
      5. Terminate the function

      Because we use buildlets, the order in which we take steps 2-4 does not 
      matter as long as we compose the resulting buildlets correctly in the
      end.
  *)

  let open Ll in (* locally open the Ll module; for convenience *)

  (* Extract the necessary information from the function summary environment *)
  let {parent_opt;locals_uid;locals_tid;offset_of_symbol;_} as summary = 
    SymbolMap.find name senv in

  (* Get the name of the static link
     - either from the lookup in the summary, if the function is not main
     - a dummy i8*, for the main function
  *) 
  let sl_type  = 
    match parent_opt with 
    | Some p -> Ll.Ptr (Ll.Namedt (SymbolMap.find p senv).locals_tid)
    | None -> Ll.Ptr I8 in

  (* A tuple that contains all sl-related information  *)
  let sl_info = (default_sl_name, sl_type) in 

  (* Step 1 -- this is our context *)
  let ctxt = {  summary; 
                break_lbl = None; 
                uenv;
                senv;
                gdecls                
             } in
  
  (* A buildlet for allocating the locals structure *)
  let build_alloca = B.add_alloca (locals_uid, Namedt locals_tid) in

  (* Aux list of arguments with SL added in the beginning *)
  let args' = sl_info:: List.map 
                (fun (H.Arg{name;ty;_}) -> (name,ty_to_llty ty)) args in 
  
  let copy_one_arg (name,ty) = (* A buildlet for copying one argument *)
    let (build_gep,op_gep) = aiwf "arg" 
      (gep_0 (* Use GEP to find where to store the argument *)
        (Namedt locals_tid)
        (Id locals_uid)
        (offset_of_symbol name)) in
    (* Observe how we return the composition of two buildlets *)
    build_gep $> build_store ty (Id name) op_gep in

  let copy_args = (* A buildlet that copies all of the arguments *)
        List.rev args' |> List.map copy_one_arg |> B.seq_buildlets in 

  let ret_ty, tr = match result with 
      Ty.VOID -> Void, fun _ -> Ret (Void, None)
    | t -> let llty = ty_to_llty t in 
      llty, fun op -> Ret (llty, Some op) in 

  let build_body, op = (* Get the builder for the body and the operand with 
                          the result; observe that we pass the context.  *)
    cgExp ctxt body in

  let build_function  (* Putting it all together *)
      = build_alloca                                          (* Step 2 *)
        $> copy_args                                          (* Step 3 *) 
        $> build_body                                         (* Step 4 *)
        $> B.term_block (tr op) in                            (* Step 5 *)

  let cfg_builder = (* Apply the buildlet; we get a cfg_builder *)
      build_function B.empty_cfg_builder in

  name,
  { fty = sl_type::List.map (ty_to_llty<$>ty_of_arg) args, ret_ty
  ; param = default_sl_name :: List.map name_of_arg args 
  ; cfg = B.get_cfg cfg_builder 
  }

let codegen_prog (H.Program{tdecls; fdecls})  : Ll.prog = 
  let tenv = ref UniqueMap.empty in
  let senv = ref SymbolMap.empty in 
  let gdecls = ref [] in 
  let tdecls1 = List.filter_map (cg_tydecl tenv) tdecls in 
  let tdecls2 = List.map (cg_fdecl_summary senv) fdecls in 
  let fdecls = List.map (cg_fdecl !senv !tenv gdecls) fdecls in 
  let tdecls = tdecls1 @ tdecls2 in 
  let gdecls = !gdecls in let open Ll in
  {tdecls; gdecls; fdecls}

let runtime_fns = 
  let fns =
    [ "i8* @allocRecord(i64)"   (* runtime functions *)
    ; "i8* @initArray (i64, i64, i8*)"
    ; "i64 @arrInxError (i64)"
    ; "i64 @recFieldError()"
    ; "i64 @divisionByZero()"
    ; "i64 @stringEqual (i8*, i8*)"
    ; "i64 @stringNotEq (i8*, i8*)"
    ; "i64 @stringLess (i8*, i8*)"
    ; "i64 @stringLessEq (i8*, i8*)"
    ; "i64 @stringGreater (i8*, i8*)"
    ; "i64 @stringGreaterEq (i8*, i8*)"
    ; "i64 @exponent(i64, i64)"

    (* user visible functions; note SL argument *)

    ; "void @print      (i8*, i8*)"   
    ; "void @flush      (i8*)"
    ; "i8*  @getChar    (i8*)"
    ; "i64  @ord        (i8*, i8*)"
    ; "i8*  @chr        (i8*, i64)"
    ; "i64  @size       (i8*, i8*)"
    ; "i8*  @substring  (i8*, i8*, i64, i64)"
    ; "i8*  @concat     (i8*, i8*, i8*)"
    ; "i64  @not        (i8*, i64)"
    ; "void @tigerexit  (i8*, i64)"
    ] in 
  let mkDeclare s = "declare " ^ s ^ "\n"
  in String.concat "" (List.map mkDeclare fns)

let ll_target_triple:string = 
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with 
    "Darwin" -> "target triple = \"x86_64-apple-macosx10.15.0\""
  | "Linux"  -> "target triple = \"x86_64-pc-linux-gnu\""
  | _ -> ""
