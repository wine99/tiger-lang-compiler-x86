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
  ; tenv: Ty.ty S.table (* Δ from our formal typing rules *)
  ; break: bool (* β from our formal typing rules *)
  ; err: Err.errenv (* error environment *) }

open Ty
open Oper

let arithOps = [PlusOp; MinusOp; TimesOp; DivideOp; ExponentOp]

let compOps = [LtOp; LeOp; GtOp; GeOp]

let rec dup_elem names positions =
  match (names, positions) with
  | [], [] -> None
  | h1 :: t1, h2 :: t2 ->
      if List.mem h1 t1 then Some (h1, h2) else dup_elem t1 t2
  | _ -> failwith "wrong usage of dup_elem"

let rec transExp ({err; venv; tenv; break} as ctx : context) e =
  let rec trexp (A.Exp {exp_base; pos}) : TA.exp =
    match exp_base with
    | A.IntExp i -> TA.Exp {exp_base= TA.IntExp i; pos; ty= Ty.INT}
    | A.StringExp s -> TA.Exp {exp_base= TA.StringExp s; pos; ty= Ty.STRING}
    | A.NilExp -> TA.Exp {exp_base= TA.NilExp; pos; ty= Ty.NIL}
    | VarExp var -> (
        let tvar = trvar var in
        match tvar with
        | TA.Var {ty; _} -> TA.Exp {exp_base= VarExp tvar; pos; ty} )
    | A.CallExp {func; args} -> (
      (* Lookup the function in the variable environment *)
      match S.look (venv, func) with
      | None ->
          Err.error err pos (EFmt.errorFunctionUndefined func) ;
          err_exp pos
      | Some tFunc -> call_exp func tFunc args pos )
    | A.OpExp {left; oper; right}
      when List.exists (fun op -> op = oper) arithOps -> (
        let (Exp {ty= ty_left; pos= pos_left; _} as t_left) = trexp left in
        let (Exp {ty= ty_right; pos= pos_right; _} as t_right) =
          trexp right
        in
        match
          ( actual_type err pos_left ty_left
          , actual_type err pos_right ty_right )
        with
        | INT, INT ->
            TA.Exp
              { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
              ; pos
              ; ty= INT }
        | _ ->
            Err.error err pos EFmt.errorArith ;
            err_exp pos )
    | A.OpExp {left; oper; right}
      when List.exists (fun op -> op = oper) compOps -> (
        let (Exp {ty= ty_left; pos= pos_left; _} as t_left) = trexp left in
        let (Exp {ty= ty_right; pos= pos_right; _} as t_right) =
          trexp right
        in
        match
          ( actual_type err pos_left ty_left
          , actual_type err pos_right ty_right )
        with
        | INT, INT | STRING, STRING ->
            TA.Exp
              { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
              ; pos
              ; ty= INT }
        | _ ->
            Err.error err pos (EFmt.errorOtherComparison ty_left ty_right) ;
            err_exp pos )
    | A.OpExp {left; oper; right} ->
        let (Exp {ty= ty_left; pos= pos_left; _} as t_left) = trexp left in
        let (Exp {ty= ty_right; pos= pos_right; _} as t_right) =
          trexp right
        in
        if
          are_comparable err ty_left pos_left ty_right pos_right
          && (ty_left != NIL || ty_right != NIL)
        then
          TA.Exp
            { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
            ; pos
            ; ty= INT }
        else (
          Err.error err pos (EFmt.errorOtherComparison ty_left ty_right) ;
          err_exp pos )
    | A.ArrayExp {size= size_exp; init= init_exp; typ} -> (
      match S.look (tenv, typ) with
      | None ->
          Err.error err pos (EFmt.errorTypeDoesNotExist typ) ;
          err_exp pos
      | Some type_arr -> (
        match actual_type err pos type_arr with
        | ARRAY (ty, _) -> (
            let (Exp {ty= ty_size; pos= pos_size; _} as t_size_exp) =
              trexp size_exp
            in
            let (Exp {ty= ty_init; pos= pos_init; _} as t_init_exp) =
              trexp init_exp
            in
            match (actual_type err pos_size ty_size, ty_init) with
            | INT, _ when is_subtype err ty_init pos_init ty pos_init ->
                (* TODO double check this and recordExp *)
                TA.Exp
                  { exp_base= TA.ArrayExp {size= t_size_exp; init= t_init_exp}
                  ; pos
                  ; ty= type_arr }
            | INT, _ ->
                Err.error err pos_init (EFmt.errorArrayInitType ty_init ty) ;
                err_exp pos
            | _ ->
                Err.error err pos_size (EFmt.errorIntRequired ty_size) ;
                err_exp pos )
        | _ ->
            Err.error err pos (EFmt.errorArrayType type_arr) ;
            err_exp pos ) )
    | A.RecordExp {fields= fields_given; typ} -> (
      match S.look (tenv, typ) with
      | None ->
          Err.error err pos (EFmt.errorTypeDoesNotExist typ) ;
          err_exp pos
      | Some type_rec -> (
        match actual_type err pos type_rec with
        | RECORD (fields, _) ->
            let fields_expec = fields in
            if List.length fields_given != List.length fields_expec then (
              Err.error err pos EFmt.errorRecordFields ;
              err_exp pos )
            else
              let t_fields =
                List.map2
                  (fun filed_given filed_expec ->
                    match (filed_given, filed_expec) with
                    | (name_given, val_given), (name_expec, val_ty_expec) ->
                        if name_given <> name_expec then (
                          Err.error err pos
                            (EFmt.errorRecordFieldName name_given name_expec) ;
                          (name_given, err_exp pos) )
                        else
                          let (TA.Exp {ty= val_ty; pos= val_pos; _} as t_val)
                              =
                            trexp val_given
                          in
                          if
                            is_subtype err val_ty val_pos val_ty_expec
                              val_pos
                          then (name_given, t_val)
                          else (
                            Err.error err pos
                              (EFmt.errorRecordFieldType name_given
                                 val_ty_expec val_ty ) ;
                            (name_given, err_exp pos) ) )
                  fields_given fields_expec
              in
              TA.Exp
                {exp_base= TA.RecordExp {fields= t_fields}; pos; ty= type_rec}
        | _ ->
            Err.error err pos (EFmt.errorRecordType type_rec) ;
            err_exp pos ) )
    | A.SeqExp [] -> TA.Exp {exp_base= TA.SeqExp []; pos; ty= Ty.VOID}
    | A.SeqExp [(A.Exp _ as e)] -> trexp e
    | A.SeqExp exps ->
        let rec t_exp = function
          | [] -> ([], Ty.VOID)
          | [exp] ->
              let (TA.Exp {ty; _} as t_exp) = trexp exp in
              ([t_exp], ty)
          | exp :: exps ->
              let (TA.Exp {ty= ty_hd; pos= pos_hd; _} as hd) = trexp exp in
              let t_exps, ty = t_exp exps in
              if ty_hd = NIL then (
                Err.error err pos_hd EFmt.errorInferNilType ;
                (err_exp pos_hd :: t_exps, ty) )
              else (hd :: t_exps, ty)
        in
        let t_exps, ty = t_exp exps in
        TA.Exp {exp_base= TA.SeqExp t_exps; pos; ty}
    | A.AssignExp {var; exp} ->
        let (TA.Var {var_base; ty= varTy; pos= varPos} as t_var) =
          trvar var
        in
        let (Exp {ty= expTy; pos= expPos; _} as t_exp) = trexp exp in
        if
          is_subtype err expTy expPos varTy varPos && assignable_var var_base
        then
          TA.Exp
            { exp_base= TA.AssignExp {var= t_var; exp= t_exp}
            ; pos
            ; ty= Ty.VOID }
        else (
          Err.error err pos (EFmt.errorCoercible varTy expTy) ;
          (*Not sure if correct err_msg*)
          err_exp pos )
    | A.IfExp {test; thn; els} -> if_exp test thn els pos
    | A.WhileExp {test; body} -> (
        let (TA.Exp {ty= testTy; _} as t_test) = trexp test in
        let (TA.Exp {ty= bodyTy; _} as t_body) =
          transExp {err; venv; tenv; break= true} body
        in
        match (testTy, bodyTy) with
        | Ty.INT, Ty.VOID ->
            TA.Exp
              { exp_base= TA.WhileExp {test= t_test; body= t_body}
              ; pos
              ; ty= bodyTy }
            (* ---------- TODO : break = true ----------- *)
        | Ty.INT, _ ->
            Err.error err pos (EFmt.errorWhileShouldBeVoid bodyTy) ;
            err_exp pos
        | _ ->
            Err.error err pos (EFmt.errorIntRequired testTy) ;
            err_exp pos )
    | A.ForExp {var; escape; lo; hi; body} -> (
        let (TA.Exp {ty= loTy; _} as t_lo) = trexp lo in
        let (TA.Exp {ty= hiTy; _} as t_hi) = trexp hi in
        match (loTy, hiTy) with
        | Ty.INT, Ty.INT ->
            let (TA.Exp {ty= bodyTy; _} as t_body) =
              transExp
                { err
                ; venv=
                    S.enter
                      (venv, var, E.VarEntry {assignable= false; ty= Ty.INT})
                ; tenv
                ; break= true }
                body
            in
            if bodyTy == Ty.VOID then
              TA.Exp
                { exp_base=
                    ForExp {var; escape; lo= t_lo; hi= t_hi; body= t_body}
                ; pos
                ; ty= bodyTy }
            else (
              Err.error err pos (EFmt.errorForShouldBeVoid bodyTy) ;
              err_exp pos )
        | Ty.INT, _ ->
            Err.error err pos (EFmt.errorIntRequired hiTy) ;
            err_exp pos
        | _ ->
            Err.error err pos (EFmt.errorIntRequired loTy) ;
            err_exp pos )
    | A.BreakExp ->
        if break then TA.Exp {exp_base= BreakExp; pos; ty= Ty.VOID}
        else (
          Err.error err pos EFmt.errorBreak ;
          err_exp pos )
    | A.LetExp {decls; body} ->
        (*Is LetEmpty not just a part of this?*)
        let t_decl_func acc decl =
          let t_decls, ctx0 = acc in
          let t_decl, ctx1 = transDecl ctx0 decl in
          (t_decl :: t_decls, ctx1)
        in
        let rev_t_decls, ctx_new =
          List.fold_left t_decl_func ([], ctx) decls
        in
        let t_decls = List.rev rev_t_decls in
        let (TA.Exp {ty; _} as t_body) = transExp ctx_new body in
        TA.Exp {exp_base= TA.LetExp {decls= t_decls; body= t_body}; pos; ty}
  (* Compute an error expression. *)
  and err_exp pos = TA.Exp {exp_base= TA.ErrorExp; pos; ty= Ty.ERROR}
  (* Helper function for call expression. *)
  and call_exp func tFunc args pos =
    (* Match the types of the function. *)
    match tFunc with
    | FunEntry {formals; result} ->
        if List.length args != List.length formals then (
          Err.error err pos (EFmt.errorFunctionArguments func) ;
          err_exp pos )
        else
          (* Check if arguments have correct type *)
          (* Check types of arguments are the same as specified for function. *)
          let t_args =
            List.map2
              (fun arg formal ->
                let (TA.Exp {ty= arg_ty; pos= arg_pos; _} as t_arg) =
                  trexp arg
                in
                if is_subtype err arg_ty arg_pos formal arg_pos then t_arg
                else (
                  Err.error err arg_pos (EFmt.errorCoercible arg_ty formal) ;
                  err_exp pos ) )
              args formals
          in
          TA.Exp {exp_base= TA.CallExp {func; args= t_args}; pos; ty= result}
    | _ ->
        Err.error err pos (EFmt.errorUsingVariableAsFunction func) ;
        err_exp pos
  and assignable_var var =
    match var with
    | TA.SimpleVar s -> (
      match S.look (venv, s) with
      | Some (E.VarEntry {assignable; _}) -> assignable
      | _ -> false (* TODO double check this *) )
    | _ -> true (* TODO double check this *)
  and if_exp test thn els pos =
    (* Type check test and then. *)
    let (TA.Exp {ty= testTy; pos= testPos; _} as t_test) = trexp test in
    let (TA.Exp {ty= thnTy; pos= thnPos; _} as t_thn) = trexp thn in
    (* Check for else. *)
    match els with
    | None -> (
      (* No else statement *)
      match (actual_type err testPos testTy, thnTy) with
      | Ty.INT, Ty.VOID ->
          TA.Exp
            { exp_base= TA.IfExp {test= t_test; thn= t_thn; els= None}
            ; pos
            ; ty= thnTy }
      | Ty.INT, _ ->
          Err.error err pos (EFmt.errorIfThenShouldBeVoid thnTy) ;
          err_exp pos
      | _ ->
          Err.error err pos (EFmt.errorIntRequired testTy) ;
          err_exp pos )
    | Some elsSt -> (
        (* With else statement *)
        let (TA.Exp {ty= elsTy; pos= elsPos; _} as t_els) = trexp elsSt in
        match (actual_type err testPos testTy, thnTy, elsTy) with
        | Ty.INT, _, _ when is_subtype err elsTy elsPos thnTy thnPos ->
            (* TODO double check this *)
            TA.Exp
              { exp_base= TA.IfExp {test= t_test; thn= t_thn; els= Some t_els}
              ; pos
              ; ty= thnTy }
        | Ty.INT, _, _ when is_subtype err thnTy thnPos elsTy elsPos ->
            TA.Exp
              { exp_base= TA.IfExp {test= t_test; thn= t_thn; els= Some t_els}
              ; pos
              ; ty= elsTy }
        | Ty.INT, _, _ ->
            Err.error err pos (EFmt.errorIfBranchesNotSameType thnTy elsTy) ;
            err_exp pos
        | _ ->
            Err.error err pos (EFmt.errorIntRequired testTy) ;
            err_exp pos )
  and trvar (A.Var {var_base; pos}) : TA.var =
    match var_base with
    (* Simple var i.e. `x` *)
    | A.SimpleVar s -> (
      match S.look (venv, s) with
      (* Look up the symbol s in venv *)
      | None ->
          (* Error, it does not exists *)
          Err.error err pos (EFmt.errorVariableUndefined s) ;
          TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR}
      | Some ent -> (
        match ent with
        | VarEntry {ty; _} -> TA.Var {var_base= TA.SimpleVar s; pos; ty}
        | FunEntry _ ->
            Err.error err pos (EFmt.errorUsingFunctionAsVariable s) ;
            TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR} ) )
    (* FieldVar, i.e. `record.field` *)
    | A.FieldVar (v, s) -> (
        (* Type check the base variable v *)
        let (TA.Var {pos= p; ty= tpe; _} as tv) = trvar v in
        match actual_type err p tpe with
        | RECORD (fields, _) -> (
          (* Check that symbol s exists in record fields *)
          match List.assoc_opt s fields with
          | Some t -> TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= t}
          | None ->
              Err.error err p (EFmt.errorRecordNonExistingField s tpe) ;
              TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= Ty.ERROR} )
        | t ->
            (* Actual type of the variable v was not a record *)
            Err.error err pos (EFmt.errorRecordType t) ;
            TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= Ty.ERROR} )
    (* SubscriptVar i.e. `arr[i]` *)
    | A.SubscriptVar (v, e) -> (
        (* Type check the base variable v *)
        let (TA.Var {pos= p; ty= tpe; _} as tv) = trvar v in
        let (TA.Exp {pos= ep; ty= etyp; _} as texp) = trexp e in
        (* Check that the actualy type is an array *)
        match (actual_type err p tpe, etyp) with
        | ARRAY (t, _), INT ->
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= t}
        | t, INT ->
            (* Error, actual type of var was not an array *)
            Err.error err p (EFmt.errorArrayType t) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        | ARRAY (_, _), et ->
            (* Error, actual type of exp was not an int *)
            Err.error err ep (EFmt.errorIntRequired et) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        | t, et ->
            (* Error, actual type of var was not array and actual type of exp was not int (combination of both) *)
            Err.error err p (EFmt.errorArrayType t) ;
            Err.error err ep (EFmt.errorIntRequired et) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        )
  in
  trexp e

and transDecl ({err; venv; tenv; break} as ctx : context) dec :
    TA.decl * context =
  match dec with
  | A.VarDec {name; escape; typ= None; init; pos} -> (
      let (TA.Exp {pos= p; ty= etyp; _} as texp) = transExp ctx init in
      match etyp with
      | Ty.NIL ->
          Err.error err p EFmt.errorInferNilType ;
          (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx)
      | Ty.VOID ->
          Err.error err p EFmt.errorVoid ;
          (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx)
      | t ->
          ( TA.VarDec {name; escape; typ= t; init= texp; pos}
          , { err
            ; venv= S.enter (venv, name, E.VarEntry {assignable= true; ty= t})
            ; tenv
            ; break } ) )
  | A.VarDec {name; escape; typ= Some (t, tp); init; pos} -> (
      let opt_expected_typ = S.look (tenv, t) in
      let (TA.Exp {pos= p; ty= actual_typ; _} as texp) = transExp ctx init in
      match opt_expected_typ with
      | Some expected_typ ->
          if is_subtype err actual_typ p expected_typ tp then
            ( TA.VarDec {name; escape; typ= expected_typ; init= texp; pos}
            , { err
              ; venv=
                  S.enter
                    ( venv
                    , name
                    , E.VarEntry {assignable= true; ty= expected_typ} )
              ; tenv
              ; break } )
          else (
            Err.error err p @@ EFmt.errorCoercible actual_typ expected_typ ;
            (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx) )
      | None ->
          Err.error err tp @@ EFmt.errorTypeDoesNotExist t ;
          (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx) )
  | A.FunctionDec funcdecls ->
      (* Helper functions *)
      (* Convert field data entry to typed field data entry *)
      let t_arg = function
        | A.Field {name; escape; typ= sym, _; pos} -> (
          match S.look (tenv, sym) with
          | Some ty -> TA.Arg {name; escape; ty; pos}
          | None ->
              Err.error err pos (EFmt.errorTypeDoesNotExist sym) ;
              TA.Arg {name; escape; ty= Ty.ERROR; pos}
              (* type of argument not defined *) )
      in
      (* Convert list of parameters to list of typed parameters *)
      let t_args params =
        List.fold_right (fun arg acc -> t_arg arg :: acc) params []
      in
      (* Look up given return type of function *)
      let t_result = function
        | Some (sym, pos) -> (
          match S.look (tenv, sym) with
          | Some ty -> ty
          | None ->
              Err.error err pos (EFmt.errorTypeDoesNotExist sym) ;
              Ty.ERROR (* result type not defined *) )
        | None -> Ty.VOID (* no annotation => void return type *)
      in
      (* Extend venv with given funcdecl *)
      let venv_func venv = function
        | A.Fdecl {name; params; result; _} ->
            let t_args =
              List.map
                (fun arg ->
                  let (TA.Arg {ty; _}) = arg in
                  ty )
                (t_args params)
            in
            S.enter
              ( venv
              , name
              , E.FunEntry {formals= t_args; result= t_result result} )
      in
      (* Extend venv with funcdecls *)
      let venv_funcs = List.fold_left venv_func venv funcdecls in
      (* Extend venv with argument *)
      let venv_arg venv_args arg =
        let (TA.Arg {name; ty; _}) = t_arg arg in
        S.enter (venv_args, name, E.VarEntry {assignable= true; ty})
      in
      (* Extend venv with arguments *)
      let venv_args args =
        List.fold_left (fun acc arg -> venv_arg acc arg) venv_funcs args
      in
      (* Type check the function *)
      let t_func = function
        | A.Fdecl {name; params; result; body; pos} ->
            (* extend venv with the argument types for the function *)
            let venv_w_args = venv_args params in
            (* type check the body *)
            let (TA.Exp {ty; pos= pos_body; _} as t_body) =
              transExp {err; venv= venv_w_args; tenv; break= false} body
            in
            let t_res = t_result result in
            if is_subtype err ty pos_body t_res pos_body then
              TA.Fdecl
                {name; args= t_args params; result= t_res; body= t_body; pos}
            else (
              Err.error err pos (EFmt.errorFunctionReturn ty t_res) ;
              TA.Fdecl
                { name
                ; args= t_args params
                ; result= Ty.ERROR
                ; body= t_body
                ; pos } )
      in
      let dup_names name pos acc =
        let acc_names =
          List.map
            (fun x ->
              let (TA.Fdecl {name; _}) = x in
              S.name name )
            acc
        in
        if List.exists (fun x -> String.equal x (S.name name)) acc_names then
          Err.error err pos (EFmt.errorDuplicate name)
      in
      let t_funcs =
        TA.FunctionDec
          (List.rev
             (List.fold_left
                (fun acc func ->
                  let (TA.Fdecl {name; pos; _} as typed_func) =
                    t_func func
                  in
                  dup_names name pos acc ; typed_func :: acc )
                [] funcdecls ) )
      in
      (t_funcs, {err; venv= venv_funcs; tenv; break})
  | A.TypeDec tydecs -> (
      let names, poses =
        List.split
          (List.map (fun (A.Tdecl {name; pos; _}) -> (name, pos)) tydecs)
      in
      let t_tydecs =
        List.map2
          (fun name pos -> TA.Tdecl {name; pos; ty= ERROR})
          names poses
      in
      match dup_elem names poses with
      | Some (name, pos) ->
          Err.error err pos (EFmt.errorDuplicate name) ;
          (TA.TypeDec t_tydecs, {err; venv; tenv; break})
      | None ->
          let tenv', name_ptrs =
            List.fold_right
              (fun name (acc_tenv, acc_refs) ->
                let nameptr = Ty.NAME (name, ref None) in
                (S.enter (acc_tenv, name, nameptr), nameptr :: acc_refs) )
              names (tenv, [])
          in
          List.iter2
            (fun [@warning "-8"] (Ty.NAME (_, tyref)) (A.Tdecl {ty; _}) ->
              tyref := mk_type err tenv' ty )
            name_ptrs tydecs ;
          if no_cycles name_ptrs then
            let t_tydecs =
              List.map2
                (fun name_ptr (A.Tdecl {name; pos; _}) ->
                  TA.Tdecl {name; pos; ty= name_ptr} )
                name_ptrs tydecs
            in
            (TA.TypeDec t_tydecs, {err; venv; tenv= tenv'; break})
          else
            let (A.Tdecl {pos; _}) = List.hd tydecs in
            Err.error err pos
              (EFmt.errorTypeDeclLoop
                 (List.map (fun (A.Tdecl {name; _}) -> name) tydecs) ) ;
            (TA.TypeDec t_tydecs, {err; venv; tenv; break}) )

and no_cycles name_ptrs =
  let eq_own_type self =
    let rec eq_self acc =
      match acc with
      | NAME (_, opt_ty_ref) -> (
        match !opt_ty_ref with
        | None -> false
        | Some a -> (
          match (self, a) with
          | NAME (sym_self, _), NAME (sym_a, _) ->
              if sym_self = sym_a then true else eq_self a
          | _ -> false ) )
      | _ -> false
    in
    eq_self self
  in
  let rec has_cycles ls =
    match ls with
    | [] -> false
    | hd_ptr :: tl_ptrs ->
        let cycle = eq_own_type hd_ptr in
        if cycle then true else has_cycles tl_ptrs
  in
  not (has_cycles name_ptrs)

and mk_type err tenv = function
  | A.NameTy (ty, pos) -> (
    match S.look (tenv, ty) with
    | None ->
        Err.error err pos (EFmt.errorTypeDoesNotExist ty) ;
        None
    | Some ty -> Some ty )
  | A.RecordTy fields -> (
      let names, poses =
        List.split
          (List.map (fun (A.Field {name; pos; _}) -> (name, pos)) fields)
      in
      match dup_elem names poses with
      | Some (name, pos) ->
          Err.error err pos (EFmt.errorDuplicate name) ;
          None
      | None ->
          let t_fields =
            List.map
              (fun (A.Field {name; typ= ty, pos; _}) ->
                match S.look (tenv, ty) with
                | None ->
                    Err.error err pos (EFmt.errorTypeDoesNotExist ty) ;
                    (name, ERROR)
                | Some ty -> (name, ty) )
              fields
          in
          if List.exists (fun (_, ty) -> ty = ERROR) t_fields then None
          else Some (RECORD (t_fields, mkUnique ())) )
  | A.ArrayTy (ty, pos) -> (
    match S.look (tenv, ty) with
    | None ->
        Err.error err pos (EFmt.errorTypeDoesNotExist ty) ;
        None
    | Some ty -> Some (ARRAY (ty, mkUnique ())) )

and actual_type err pos = function
  | NAME (sym, opt_ty_ref) -> (
    match !opt_ty_ref with
    | None ->
        Err.error err pos (EFmt.errorTypeDoesNotExist sym) ;
        Ty.ERROR
    | Some a -> actual_type err pos a )
  | t -> t

(** Checks if t1 is a subtype of t2 *)
and is_subtype err t1 pos1 t2 pos2 =
  let t1 = actual_type err pos1 t1 in
  let t2 = actual_type err pos2 t2 in
  match (t1, t2) with Ty.NIL, Ty.RECORD _ -> true | _ -> t1 == t2

and are_comparable err t1 pos1 t2 pos2 =
  t1 != Ty.VOID
  && (is_subtype err t1 pos1 t2 pos2 || is_subtype err t2 pos2 t1 pos1)

(* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  let (TA.Exp {ty; pos; _} as t_exp) =
    transExp {venv= E.baseVenv; tenv= E.baseTenv; err; break= false} e
  in
  if ty = NIL then Err.error err pos EFmt.errorInferNilType ;
  (t_exp, err)
