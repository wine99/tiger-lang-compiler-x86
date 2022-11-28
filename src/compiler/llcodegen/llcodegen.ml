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

module SymbolMap = Map.Make (struct
  type t = S.symbol

  let compare = compare
end)

module UniqueMap = Map.Make (struct
  type t = Ty.unique

  let compare = compare
end)

type unique_env = Ll.tid UniqueMap.t

type fdecl_summary =
  { parent_opt: Ll.gid option (* optional symbol 'parent' in locals.parent *)
  ; locals_uid: Ll.uid (* symbol 'locals' in locals.field *)
  ; locals_tid: Ll.tid
        (* type of the struct of 'locals'. Each 'locals' struct is a distinct type *)
  ; offset_of_symbol: S.symbol -> int
        (* the offset of the symbol in 'locals', used for gep instruction *)
  }

type summary_env = fdecl_summary SymbolMap.t

exception NotImplemented

exception CodeGenerationBug

let ty_of_exp = function H.Exp {ty; _} -> ty

let rec sym_of_var = function
  | H.Var {var_base= AccessVar (_, s); _} -> s
  | H.Var {var_base= FieldVar (v, _); _} -> sym_of_var v
  | H.Var {var_base= SubscriptVar (v, _); _} -> sym_of_var v

let string_literal_llty str =
  let len = String.length str in
  Ll.Struct [Ll.I64; Ll.Array (len, Ll.I8)]

let string_literal_llstr str =
  let len = String.length str in
  Ll.GStruct [(Ll.I64, Ll.GInt len); (Ll.Array (len, Ll.I8), Ll.GString str)]

let rec actual_type = function
  | Types.NAME (_, opt_ty_ref) -> (
    match !opt_ty_ref with
    | None -> raise CodeGenerationBug
    | Some a -> actual_type a )
  | t -> t

let rec ty_to_llty ty =
  match ty with
  | Ty.INT -> Ll.I64
  | Ty.NIL -> Ll.Ptr I8
  | Ty.STRING | Ty.RECORD _ | Ty.ARRAY _ -> Ll.Ptr I8
  (* The given code for generating types of locals (SL) used ty_to_llty,
     if type a = {...} type b = a, and we have a var v of type b, v should
     also be a pointer in locals *)
  | Ty.NAME _ -> ty_to_llty @@ actual_type ty
  | Ty.VOID -> Ll.Void
  | Ty.ERROR -> raise CodeGenerationBug

type context =
  { break_lbl: Ll.lbl option
  ; summary: fdecl_summary
  ; uenv: unique_env
  ; senv: summary_env
  ; gdecls: (Ll.gid * Ll.gdecl) list ref }

let get_rec_or_arr_back (uenv : unique_env) ty =
  match actual_type ty with
  | Ty.RECORD (_, u) -> Ll.Namedt (UniqueMap.find u uenv)
  | Ty.ARRAY (_, u) -> Ll.Namedt (UniqueMap.find u uenv)
  | _ -> raise CodeGenerationBug

(* Obs: this is a rather tricky piece of code; 2019-10-12 *)
let cg_tydecl (uenv : unique_env ref) (H.Tdecl {name; ty; _}) =
  (* [ty] has a named type arround it, seems like a weird design choice *)
  let ty = actual_type ty in
  let llvm_type = ty_to_llty ty in
  match ty with
  | Ty.INT -> Some (name, llvm_type) (* type a = int *)
  | Ty.STRING -> Some (name, llvm_type) (* type a = string *)
  | Ty.NAME (_, _) -> Some (name, llvm_type) (* type a = b *)
  | Ty.VOID -> Some (name, llvm_type)
  | Ty.RECORD (ts, u) -> (
    match UniqueMap.find_opt u !uenv with
    | None ->
        uenv := UniqueMap.add u name !uenv ;
        Some (name, Ll.Struct (List.map (fun (_, t) -> ty_to_llty t) ts))
    | Some _ -> None )
  | Ty.ARRAY (_, u) -> (
    match UniqueMap.find_opt u !uenv with
    | None ->
        uenv := UniqueMap.add u name !uenv ;
        Some (name, llvm_type)
    | Some _ -> None )
  | Ty.NIL -> None
  | Ty.ERROR -> None

let fresh =
  let open Freshsymbols in
  let env = empty in
  gensym env

let cmp_to_ll_cmp = function
  | H.EqOp -> Ll.Eq
  | H.NeqOp -> Ll.Ne
  | H.LtOp -> Ll.Slt
  | H.LeOp -> Ll.Sle
  | H.GtOp -> Ll.Sgt
  | H.GeOp -> Ll.Sge
  | _ -> raise NotImplemented

let ptr_i8 = Ll.Ptr Ll.I8

let ( <$> ) f g x = f (g x)

let id = Fun.id

let ( $> ) b1 b2 = b2 <$> b1 (* buildlet composition *)

let ( @> ) (b, op) k = b $> k op

let ty_of_exp (H.Exp {ty; _}) = ty

let ty_of_var (H.Var {ty; _}) = ty

let ty_of_arg (H.Arg {ty; _}) = ty

let name_of_arg (H.Arg {name; _}) = name

let default_sl_name = S.symbol "$sl"

let locals_type_name name = S.symbol @@ "$locals_" ^ S.name name

let ty_dec_name name = S.symbol @@ "t_$" ^ S.name name

(* add instruction with fresh symbol *)
let aiwf s i =
  let t = fresh s in
  (B.add_insn (Some t, i), Ll.Id t)

let biwf t i = (B.add_insn (Some t, i), Ll.Id t)

let no_res_inst i = (B.add_insn (None, i), Ll.Null)

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

let bind ((builder, op) : 'a m) (f : 'a -> 'b m) : 'b m =
  let builder', op' = f op in
  (builder $> builder', op')

let return x = (B.id_buildlet, x)

let ( let* ) = bind
(* --- end of monadic interface ------------------------ *)

let unit b = (b, ())

let build_store t o1 o2 = B.add_insn (None, Ll.Store (t, o1, o2))

let gep_0 ty op i = Ll.Gep (ty, op, [Const 0; Const i])

let arith_oper =
  [Oper.PlusOp; Oper.MinusOp; Oper.TimesOp; Oper.DivideOp; Oper.ExponentOp]

let cmp_oper =
  [Oper.EqOp; Oper.NeqOp; Oper.LtOp; Oper.LeOp; Oper.GtOp; Oper.GeOp]

let global_functions =
  [ ("print", Ll.Void)
  ; ("flush", Ll.Void)
  ; ("getChar", ptr_i8)
  ; ("ord", Ll.I64)
  ; ("chr", ptr_i8)
  ; ("size", Ll.I64)
  ; ("substring", ptr_i8)
  ; ("concat", ptr_i8)
  ; ("not", Ll.I64)
  ; ("tigerexit", Ll.Void) ]

let cg_ai_ op left right =
  aiwf "arith_tmp" @@ Ll.Binop (op, Ll.I64, left, right)

let cg_ai_div left right =
  let zero_lbl = fresh "zero_lbl" in
  let non_zero_lbl = fresh "non_zero_lbl" in
  let* cmp = aiwf "zero_cmp" @@ Ll.Icmp (Ll.Eq, Ll.I64, right, Ll.Const 0) in
  let* _ = (B.term_block @@ Ll.Cbr (cmp, zero_lbl, non_zero_lbl), Ll.Null) in
  (* Division by zero branch *)
  let* _ = (B.start_block @@ zero_lbl, Ll.Null) in
  let* _ =
    no_res_inst @@ Ll.Call (Ll.I64, Ll.Gid (S.symbol "divisionByZero"), [])
  in
  let* _ = (B.term_block @@ Ll.Br non_zero_lbl, Ll.Null) in
  (* Non-zero division branch *)
  let* _ = (B.start_block @@ non_zero_lbl, Ll.Null) in
  aiwf "arith_tmp" @@ Ll.Binop (Ll.SDiv, Ll.I64, left, right)
  

let cg_arith_instr left right = function
  | Oper.PlusOp -> cg_ai_ Ll.Add left right
  | Oper.MinusOp -> cg_ai_ Ll.Sub left right
  | Oper.TimesOp -> cg_ai_ Ll.Mul left right
  | Oper.DivideOp -> cg_ai_div left right (* special case to handle division by zero *)
  | Oper.ExponentOp ->
      aiwf "ret"
        (Ll.Call
           ( Ll.I64
           , Ll.Gid (S.symbol "exponent")
           , [(Ll.I64, left); (Ll.I64, right)] ) )
  | _ -> raise CodeGenerationBug

let cg_cmp_instr ty left right op =
  match ty with
  | Ty.STRING ->
      let cnd =
        match op with
        | Oper.EqOp -> "stringEqual"
        | Oper.NeqOp -> "stringNotEq"
        | Oper.LtOp -> "stringLess"
        | Oper.LeOp -> "stringLessEq"
        | Oper.GtOp -> "stringGreater"
        | Oper.GeOp -> "stringGreaterEq"
        | _ -> raise CodeGenerationBug
      in
      let func = Ll.Gid (S.symbol cnd) in
      aiwf "ret" (Ll.Call (Ll.I64, func, [(ptr_i8, left); (ptr_i8, right)]))
  | _ ->
      let cnd = cmp_to_ll_cmp op in
      let* tmp =
        aiwf "cmp_tmp" @@ Ll.Icmp (cnd, ty_to_llty ty, left, right)
      in
      aiwf "cmp_tmp" @@ Ll.Zext (Ll.I1, tmp, Ll.I64)

let rec cgExp ctxt (Exp {exp_base; ty; _} : H.exp) :
    B.buildlet * Ll.operand (* Alternatively: Ll.operand m *) =
  let cgE_ = cgExp ctxt in
  match exp_base with
  | IntExp i -> (id, Const i)
  | H.OpExp {left; right; oper; _} when List.exists (( = ) oper) arith_oper
    ->
      let* op_left = cgE_ left in
      let* op_right = cgE_ right in
      cg_arith_instr op_left op_right oper
  | H.OpExp {left= H.Exp {ty; _} as left; right; oper; _}
    when List.exists (( = ) oper) cmp_oper ->
      let* op_left = cgE_ left in
      let* op_right = cgE_ right in
      cg_cmp_instr ty op_left op_right oper
  | H.AssignExp {var; exp} ->
      let ty = ty_of_var var in
      let* e = cgE_ exp in
      let* dest = cgVar ~load:false ctxt var in
      no_res_inst @@ Ll.Store (ty_to_llty ty, e, dest)
  | H.LetExp {vardecl; body} -> (
    match vardecl with
    | VarDec {name; typ; init; _} ->
        let* e = cgE_ init in
        let* dest =
          cgVarLookup ctxt ctxt.summary (Ll.Id ctxt.summary.locals_uid) name
            0
        in
        let* _ = (build_store (ty_to_llty typ) e dest, Ll.Null) in
        cgE_ body )
  | H.SeqExp exps ->
      let rec loop = function
        | [] -> (B.id_buildlet, Ll.Null)
        | [e] -> cgE_ e
        | e :: es ->
            let* _ = cgE_ e in
            loop es
      in
      loop exps
  | H.VarExp var -> cgVar ctxt var
  | H.IfExp {test; thn; els= Some els} -> cgIfThenElse ctxt test thn els ty
  | H.IfExp {test; thn; els= None} ->
      let thn_lbl = fresh "then" in
      let merge_lbl = fresh "merge" in
      let* test_res_i64 = cgE_ test in
      let* test_res =
        aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
      in
      let* _ =
        (B.term_block @@ Ll.Cbr (test_res, thn_lbl, merge_lbl), Ll.Null)
      in
      let* _ = (B.start_block thn_lbl, Ll.Null) in
      let* _ = cgE_ thn in
      let* _ = (B.term_block @@ Ll.Br merge_lbl, Ll.Null) in
      (B.start_block merge_lbl, Ll.Null)
  | H.StringExp str ->
      let str_id = fresh "string_lit" in
      let str_ty = string_literal_llty str in
      let ll_str = string_literal_llstr str in
      ctxt.gdecls := (str_id, (str_ty, ll_str)) :: !(ctxt.gdecls) ;
      aiwf "string" @@ Ll.Bitcast (Ll.Ptr str_ty, Ll.Gid str_id, ptr_i8)
  | H.CallExp {func; lvl_diff; args} -> (
      let rec loop args =
        match args with
        | [] -> (id, [])
        | (H.Exp {ty= ty_a; _} as a) :: args -> (
            let build, op = cgE_ a in
            match loop args with
            | builds, ops -> (build $> builds, (ty_to_llty ty_a, op) :: ops)
            )
      in
      let* ops = loop args in
      let is_global =
        List.find_opt
          (fun x ->
            let name, _ = x in
            name = S.name func )
          global_functions
      in
      let func = Ll.Gid func in
      let locals = Ll.Id ctxt.summary.locals_uid in
      match is_global with
      | Some (_, ret_ty) ->
          let locals_type = ctxt.summary.locals_tid in
          let* sl =
            aiwf "SL"
            @@ Ll.Bitcast (Ll.Ptr (Ll.Namedt locals_type), locals, ptr_i8)
          in
          if ret_ty = Ll.Void then
            ( B.add_insn (None, Ll.Call (ret_ty, func, (ptr_i8, sl) :: ops))
            , Ll.Null )
          else aiwf "ret" @@ Ll.Call (ret_ty, func, (ptr_i8, sl) :: ops)
      | None ->
          let* sl_ptr = cgSlLookup ctxt ctxt.summary locals lvl_diff in
          let sl_ptr_ty = Ll.Ptr (getSlType ctxt ctxt.summary lvl_diff) in
          let ret_ty = ty_to_llty ty in
          if ret_ty = Ll.Void then
            ( B.add_insn
                (None, Ll.Call (ret_ty, func, (sl_ptr_ty, sl_ptr) :: ops))
            , Ll.Null )
          else
            aiwf "ret" @@ Ll.Call (ret_ty, func, (sl_ptr_ty, sl_ptr) :: ops)
      )
  | H.WhileExp {test; body} ->
      let test_lbl = fresh "test" in
      let body_lbl = fresh "body" in
      let merge_lbl = fresh "merge" in
      (* Test block *)
      let* _ = (B.term_block @@ Ll.Br test_lbl, Ll.Null) in
      let* _ = (B.start_block test_lbl, Ll.Null) in
      let* test_res_i64 = cgE_ test in
      let* test_res =
        aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
      in
      let* _ =
        (B.term_block @@ Ll.Cbr (test_res, body_lbl, merge_lbl), Ll.Null)
      in
      (* Body block *)
      let* _ = (B.start_block body_lbl, Ll.Null) in
      let* _ = cgExp {ctxt with break_lbl= Some merge_lbl} body in
      let* _ = (B.term_block @@ Ll.Br test_lbl, Ll.Null) in
      (* Merge block *)
      (B.start_block merge_lbl, Ll.Null)
  | H.BreakExp -> (
    match ctxt.break_lbl with
    | None -> raise NotImplemented (* Should not be allowed *)
    | Some merge_lbl ->
        let dummy = fresh "dummy" in
        let* _ = (B.term_block @@ Ll.Br merge_lbl, Ll.Null) in
        (B.start_block dummy, Ll.Null) )
  | RecordExp {fields= fields_inits} ->
      let rec cgFieldsInit rec_ptr rec_ptr_i8 fields_inits rec_ty fields_tys
          rec_llty =
        match fields_inits with
        | [] -> return rec_ptr_i8
        | (field, init) :: fields_inits ->
            let ty = List.assoc field fields_tys in
            let llty = ty_to_llty ty in
            let* op_init = cgE_ init in
            let* field_ptr =
              aiwf "field_ptr" @@ gep_0 rec_llty rec_ptr
              @@ field_offset field rec_ty
            in
            let* _ = (build_store llty op_init field_ptr, Ll.Null) in
            cgFieldsInit rec_ptr rec_ptr_i8 fields_inits rec_ty fields_tys
              rec_llty
      in
      let fields_tys =
        match actual_type ty with
        | Types.RECORD (fields_tys, _) -> fields_tys
        | _ -> raise CodeGenerationBug
      in
      let rec_llty = get_rec_or_arr_back ctxt.uenv ty in
      let* size_ptr =
        aiwf "size_ptr" @@ Ll.Gep (rec_llty, Ll.Null, [Ll.Const 1])
      in
      let* size = aiwf "size" @@ Ll.Ptrtoint (rec_llty, size_ptr, Ll.I64) in
      let* rec_ptr_i8 =
        aiwf "rec_ptr_i8"
        @@ Ll.Call (ptr_i8, Ll.Gid (S.symbol "allocRecord"), [(Ll.I64, size)])
      in
      let* rec_ptr =
        aiwf "rec_ptr" @@ Ll.Bitcast (ptr_i8, rec_ptr_i8, Ll.Ptr rec_llty)
      in
      cgFieldsInit rec_ptr rec_ptr_i8 fields_inits ty fields_tys rec_llty
  | ArrayExp {size; init} ->
      let elem_llty =
        ty_to_llty
          ( match actual_type ty with
          | Ty.ARRAY (ty, _) -> ty
          | _ -> raise CodeGenerationBug )
      in
      let* size = cgE_ size in
      let* init = cgE_ init in
      let* init_ptr = aiwf "arr_init_ptr" @@ Ll.Alloca elem_llty in
      let* _ = (build_store elem_llty init init_ptr, Ll.Null) in
      let* init_ptr =
        aiwf "array_init" @@ Ll.Bitcast (Ptr elem_llty, init_ptr, ptr_i8)
      in
      let* elem_size_ptr =
        aiwf "elem_size_ptr" @@ Ll.Gep (elem_llty, Ll.Null, [Ll.Const 1])
      in
      let* elem_size =
        aiwf "elem_size" @@ Ll.Ptrtoint (elem_llty, elem_size_ptr, Ll.I64)
      in
      aiwf "arr_ptr_i8"
      @@ Ll.Call
           ( ptr_i8
           , Ll.Gid (S.symbol "initArray")
           , [(Ll.I64, size); (Ll.I64, elem_size); (ptr_i8, init_ptr)] )
  | NilExp -> return Ll.Null
  | _ -> raise CodeGenerationBug

and cgIfThenElse ctxt test thn els ty =
  let cgE_ = cgExp ctxt in
  let thn_lbl = fresh "then" in
  let els_lbl = fresh "else" in
  let merge_lbl = fresh "merge" in
  let res_ty = ty_to_llty ty in
  let* res_ptr =
    if res_ty = Ll.Void then return Ll.Null
    else
      let res = fresh "local_ifs" in
      (B.add_alloca (res, res_ty), Ll.Id res)
  in
  let* test_res_i64 = cgE_ test in
  let* test_res =
    aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
  in
  let* _ = (B.term_block @@ Ll.Cbr (test_res, thn_lbl, els_lbl), Ll.Null) in
  let* _ = (B.start_block thn_lbl, Ll.Null) in
  let* thn_op = cgE_ thn in
  let* _ =
    if res_ty = Ll.Void then return Ll.Null
    else (build_store res_ty thn_op res_ptr, Ll.Null)
  in
  let* _ = (B.term_block @@ Ll.Br merge_lbl, Ll.Null) in
  let* _ = (B.start_block els_lbl, Ll.Null) in
  let* els_op = cgE_ els in
  let* _ =
    if res_ty = Ll.Void then return Ll.Null
    else (build_store res_ty els_op res_ptr, Ll.Null)
  in
  let* _ = (B.term_block @@ Ll.Br merge_lbl, Ll.Null) in
  let* _ = (B.start_block merge_lbl, Ll.Null) in
  if res_ty = Ll.Void then return Ll.Null
  else aiwf "if_res" @@ Ll.Load (res_ty, res_ptr)

and cgVar ?(load = true) (ctxt : context) (H.Var {var_base; ty; _}) =
  let return_llty = ty_to_llty ty in
  match var_base with
  | AccessVar (i, sym) ->
      let locals = Ll.Id ctxt.summary.locals_uid in
      let* var_ptr = cgVarLookup ctxt ctxt.summary locals sym i in
      if load then mk_var_load_inst ctxt return_llty var_ptr
      else return var_ptr
  | FieldVar (var, sym) ->
      let rec_ty = ty_of_var var in
      let rec_llty = get_rec_or_arr_back ctxt.uenv @@ rec_ty in
      let* rec_ptr = cgVar ctxt var in
      let* rec_ptr =
        aiwf "rec_ptr" @@ Bitcast (ptr_i8, rec_ptr, Ptr rec_llty)
      in
      let* field_ptr =
        aiwf "field_ptr" @@ gep_0 rec_llty rec_ptr @@ field_offset sym rec_ty
      in
      if load then aiwf "field" @@ Ll.Load (return_llty, field_ptr)
      else return field_ptr
  | SubscriptVar (var, exp) ->
      let inbound_lbl = fresh "inbound_lbl" in
      let inbound2_lbl = fresh "inbound2_lbl" in
      let outbound_lbl = fresh "outbound_lbl" in
      let* arrptr = cgVar ctxt var in
      let* index = cgExp ctxt exp in
      let* arr_ptr = aiwf "arr_ptr" @@ Bitcast (ptr_i8, arrptr, Ptr I64) in
      let* arr_size_ptr_raw =
        aiwf "arr_size_ptr_raw" @@ Gep (I64, arr_ptr, [Ll.Const (-1)])
      in
      let* arr_size =
        aiwf "arr_size" @@ Ll.Load (Ll.I64, arr_size_ptr_raw)
      in
      let* cmp =
        aiwf "bounds_check" @@ Ll.Icmp (Ll.Slt, Ll.I64, index, arr_size)
      in
      let* _ =
        (B.term_block @@ Ll.Cbr (cmp, inbound_lbl, outbound_lbl), Ll.Null)
      in
      (* Outbound branch *)
      let* _ = (B.start_block @@ outbound_lbl, Ll.Null) in
      let* _ =
        aiwf "arr_outbound"
        @@ Ll.Call
             (Ll.I64, Ll.Gid (S.symbol "arrInxError"), [(Ll.I64, index)])
      in
      let* _ = (B.term_block @@ Ll.Br inbound2_lbl, Ll.Null) in
      (* Inbound branch *)
      let* _ = (B.start_block @@ inbound_lbl, Ll.Null) in
      let* cmp2 =
        aiwf "bounds_check2" @@ Ll.Icmp (Ll.Sle, Ll.I64, Ll.Const 0, index)
      in
      let* _ =
        (B.term_block @@ Ll.Cbr (cmp2, inbound2_lbl, outbound_lbl), Ll.Null)
      in
      (* Inbound 2 branch *)
      let* _ = (B.start_block @@ inbound2_lbl, Ll.Null) in
      let* arr_ptr =
        aiwf "arr_ptr" @@ Bitcast (ptr_i8, arrptr, Ptr return_llty)
      in
      let* elem_ptr =
        aiwf "elem_ptr" @@ Gep (return_llty, arr_ptr, [index])
      in
      if load then aiwf "elem" @@ Ll.Load (return_llty, elem_ptr)
      else return elem_ptr

and field_offset field (ty : Types.ty) =
  match actual_type ty with
  | Types.RECORD (fields, _) -> assoc_index field fields
  | _ -> raise CodeGenerationBug

and assoc_index a l =
  let rec loop l i =
    match l with
    | [] -> raise CodeGenerationBug
    | (a', _) :: l' -> if a = a' then i else loop l' (i + 1)
  in
  loop l 0

and mk_var_load_inst ctxt ty var_ptr =
  let null_lbl = fresh "null_lbl" in
  let not_null_lbl = fresh "not_null_lbl" in
  let* cmp =
    aiwf "var_cmp" @@ Ll.Icmp (Ll.Eq, Ll.Ptr ty, Ll.Null, var_ptr)
  in
  let* _ = (B.term_block @@ Ll.Cbr (cmp, null_lbl, not_null_lbl), Ll.Null) in
  (* Null branch *)
  let* _ = (B.start_block @@ null_lbl, Ll.Null) in
  let locals = Ll.Id ctxt.summary.locals_uid in
  let locals_type = ctxt.summary.locals_tid in
  let* sl =
    aiwf "SL" @@ Ll.Bitcast (Ll.Ptr (Ll.Namedt locals_type), locals, ptr_i8)
  in
  let* _ =
    match ty with
    | Ll.Struct _ ->
        aiwf "rec_field_error_ret"
        @@ Ll.Call (Ll.I64, Ll.Gid (S.symbol "recFieldError"), [])
    | _ ->
        no_res_inst
        @@ Ll.Call
             ( Ll.Void
             , Ll.Gid (S.symbol "tigerexit")
             , [(ptr_i8, sl); (Ll.I64, Ll.Const (-1))] )
  in
  let* _ = (B.term_block @@ Ll.Br not_null_lbl, Ll.Null) in
  (* Not-null branch *)
  let* _ = (B.start_block @@ not_null_lbl, Ll.Null) in
  aiwf "var" @@ Ll.Load (ty, var_ptr)

(* Usage: pass locals to parent_ptr *)
and cgVarLookup ctxt summary (parent_ptr : Ll.operand) sym n =
  cgSlOrVarLookup ctxt summary parent_ptr (Some sym) n

(* Usage: pass locals to parent_ptr *)
and cgSlLookup ctxt summary (parent_ptr : Ll.operand) n =
  cgSlOrVarLookup ctxt summary parent_ptr None n

(* This function either return a variable pointer or a SL pointer *)
and cgSlOrVarLookup ctxt summary (parent_ptr : Ll.operand)
    (sym : S.symbol option) = function
  | 0 -> (
    match sym with
    | None -> return parent_ptr
    | Some sym ->
        aiwf
          (S.name sym ^ "_ptr")
          (gep_0 (Namedt summary.locals_tid) parent_ptr
             (summary.offset_of_symbol sym) ) )
  | n ->
      let parent_sym =
        match summary.parent_opt with
        | Some sym -> sym
        | None -> raise CodeGenerationBug
      in
      let parent_summary = SymbolMap.find parent_sym ctxt.senv in
      let* parent_parent_ptrptr =
        aiwf
          (S.name parent_sym ^ "_ptrptr")
          (gep_0 (Namedt summary.locals_tid) parent_ptr 0)
      in
      let* parent_parent_ptr =
        aiwf
          (S.name parent_sym ^ "_ptr")
          (Ll.Load
             (Ptr (Namedt parent_summary.locals_tid), parent_parent_ptrptr)
          )
      in
      cgSlOrVarLookup ctxt parent_summary parent_parent_ptr sym (n - 1)

and getSlType ctxt summary = function
  | 0 -> Ll.Namedt summary.locals_tid
  | n ->
      let parent_sym =
        match summary.parent_opt with
        | Some sym -> sym
        | None -> raise CodeGenerationBug
      in
      let parent_summary = SymbolMap.find parent_sym ctxt.senv in
      getSlType ctxt parent_summary (n - 1)

(* --- From this point on the code requires no changes --- *)

(* Creates summary of a function declaration; relies on the alpha conversion *)
let cg_fdecl_summary senv_ref (H.Fdecl {name; parent_opt; locals; _}) =
  let locals_uid = fresh "locals" in
  let locals_tid = locals_type_name name in
  let offset_of_symbol =
    let locals_map =
      default_sl_name :: List.map fst locals
      |> List.mapi (fun i x -> (x, i))
      |> List.to_seq |> SymbolMap.of_seq
    in
    fun sym -> SymbolMap.find sym locals_map
  in
  senv_ref :=
    SymbolMap.add name
      {parent_opt; locals_uid; locals_tid; offset_of_symbol}
      !senv_ref ;
  let sl_type =
    match parent_opt with
    | Some p -> Ll.Ptr (Ll.Namedt (p |> locals_type_name))
    | None -> Ll.Ptr I8
  in
  let locals_ty =
    Ll.Struct (sl_type :: List.map (fun (_, t) -> ty_to_llty t) locals)
  in
  (locals_tid, locals_ty)

(* --- Code genartion of function bodies --- *)
let cg_fdecl senv uenv gdecls (H.Fdecl {name; args; result; body; _}) =
  (* Function bodies are generated in 5 steps
     1. Creating the translation context
     2. Allocating the locals structure with all the variables
     3. Copying the arguments to the locals
     4. Generating the code for the function body
     5. Terminate the function

     Because we use buildlets, the order in which we take steps 2-4 does not
     matter as long as we compose the resulting buildlets correctly in the
     end.
  *)
  let open Ll in
  (* locally open the Ll module; for convenience *)

  (* Extract the necessary information from the function summary environment *)
  let ({parent_opt; locals_uid; locals_tid; offset_of_symbol; _} as summary)
      =
    SymbolMap.find name senv
  in
  (* Get the name of the static link
     - either from the lookup in the summary, if the function is not main
     - a dummy i8*, for the main function
  *)
  let sl_type =
    match parent_opt with
    | Some p -> Ll.Ptr (Ll.Namedt (SymbolMap.find p senv).locals_tid)
    | None -> Ll.Ptr I8
  in
  (* A tuple that contains all sl-related information  *)
  let sl_info = (default_sl_name, sl_type) in
  (* Step 1 -- this is our context *)
  let ctxt = {summary; break_lbl= None; uenv; senv; gdecls} in
  (* A buildlet for allocating the locals structure *)
  let build_alloca = B.add_alloca (locals_uid, Namedt locals_tid) in
  (* Aux list of arguments with SL added in the beginning *)
  let args' =
    sl_info
    :: List.map (fun (H.Arg {name; ty; _}) -> (name, ty_to_llty ty)) args
  in
  let copy_one_arg (name, ty) =
    (* A buildlet for copying one argument *)
    let build_gep, op_gep =
      aiwf "arg"
        (gep_0 (* Use GEP to find where to store the argument *)
           (Namedt locals_tid) (Id locals_uid) (offset_of_symbol name) )
    in
    (* Observe how we return the composition of two buildlets *)
    build_gep $> build_store ty (Id name) op_gep
  in
  let copy_args =
    (* A buildlet that copies all of the arguments *)
    List.rev args' |> List.map copy_one_arg |> B.seq_buildlets
  in
  let ret_ty, tr =
    match result with
    | Ty.VOID -> (Void, fun _ -> Ret (Void, None))
    | t ->
        let llty = ty_to_llty t in
        (llty, fun op -> Ret (llty, Some op))
  in
  let build_body, op =
    (* Get the builder for the body and the operand with
       the result; observe that we pass the context. *)
    cgExp ctxt body
  in
  let build_function (* Putting it all together *) =
    build_alloca (* Step 2 *) $> copy_args (* Step 3 *)
    $> build_body (* Step 4 *)
    $> B.term_block (tr op)
  in
  (* Step 5 *)
  let cfg_builder =
    (* Apply the buildlet; we get a cfg_builder *)
    build_function B.empty_cfg_builder
  in
  ( name
  , { fty= (sl_type :: List.map (ty_to_llty <$> ty_of_arg) args, ret_ty)
    ; param= default_sl_name :: List.map name_of_arg args
    ; cfg= B.get_cfg cfg_builder } )

let codegen_prog (H.Program {tdecls; fdecls}) : Ll.prog =
  let tenv = ref UniqueMap.empty in
  let senv = ref SymbolMap.empty in
  let gdecls = ref [] in
  let tdecls1 = List.filter_map (cg_tydecl tenv) tdecls in
  let tdecls2 = List.map (cg_fdecl_summary senv) fdecls in
  let fdecls = List.map (cg_fdecl !senv !tenv gdecls) fdecls in
  let tdecls = tdecls1 @ tdecls2 in
  let gdecls = !gdecls in
  let open Ll in
  {tdecls; gdecls; fdecls}

let runtime_fns =
  let fns =
    [ "i8* @allocRecord(i64)" (* runtime functions *)
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
    ; "void @tigerexit  (i8*, i64)" ]
  in
  let mkDeclare s = "declare " ^ s ^ "\n" in
  String.concat "" (List.map mkDeclare fns)

let ll_target_triple : string =
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with
  | "Darwin" -> "target triple = \"x86_64-apple-macosx10.15.0\""
  | "Linux" -> "target triple = \"x86_64-pc-linux-gnu\""
  | _ -> ""
