(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Tigerc compiler main *)


open Tigercommon
open Tigerlexer
open Tigerparser
open Tigersemant
open Tigerhoist
open Tigerll
open Tigerx86
open Phases
open ExitCodes

module A = Absyn
module A' = Tabsyn
module S = Symbol

type config = {file: string; phase: phase; norm_cnd: phase_relation; unfold: int; out: Format.formatter}

exception ExitMain of phase

(** Open the file and initialize the lexer buffer. Observe that the input
    buffer must be closed by the caller. *)

let initLexer filename =
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  (* obs that we need to initialize the pos_fname field ourselves *)
  filebuf.lex_curr_p <- { filebuf.lex_curr_p with pos_fname = filename };
  (input, filebuf)

let lexonly file out =
  let input, filebuf = initLexer file in
  let lexRes =
    try
      let tokens = Parser.lexdriver Lexer.token filebuf in
      let printToken ((t,p):string * Lexing.position) =
        Format.fprintf out "%d:%d:%s\n"
          p.pos_lnum (p.pos_cnum - p.pos_bol + 1) t
      in
      List.iter printToken tokens
    with
    | Lexer.Error msg ->
      Printf.eprintf "%s%!" msg;
      raise (ExitMain LEX)
  in
  close_in input; lexRes

let parse file =
  let input, filebuf = initLexer file in
  let parseRes =
    try  Parser.program Lexer.token filebuf
    with
    | Lexer.Error msg -> Printf.eprintf "%s%!" msg; raise (ExitMain LEX)
    | Parser.Error ->
      let pos1 = Lexing.lexeme_start_p filebuf in
      let pos2 = Lexing.lexeme_end_p filebuf in
      let lexeme = Lexing.lexeme filebuf in
      Printf.fprintf stderr "%s:%d:%d - %d:%d: syntax error '%s'\n"
        pos1.pos_fname pos1.pos_lnum (pos1.pos_cnum - pos1.pos_bol)
        pos2.pos_lnum (pos2.pos_cnum - pos2.pos_bol + 1)
        lexeme;
      raise (ExitMain PAR)
  in
  close_in input;
  parseRes

let semant exp =
  let texp, err = Semant.transProg exp
  in if Errenv.any_errors err
  then raise (ExitMain SEM);
  texp

let hoist texp =
  let aexp = Alphaconversion.alpha_convert texp in
  Hoisting.hoist aexp

let js file out hexp =
  HoistedToJs.to_js file out hexp

let llvm p = Llcodegen.codegen_prog p

let x86 p = Backend.compile_prog p

let llvmparse file =
  let open Llvmparser in
  let input, filebuf = initLexer file in
  let parseRes =
    try Llparser.prog Lllexer.token filebuf
    with
    | Lllexer.Error msg -> Printf.eprintf "%s%!" msg; raise (ExitMain LEX)
    | Llparser.Error ->
      let pos1 = Lexing.lexeme_start_p filebuf in
      let pos2 = Lexing.lexeme_end_p filebuf in
      let lexeme = Lexing.lexeme filebuf in
      Printf.fprintf stderr "%s:%d:%d - %d:%d: syntax error '%s'\n"
        pos1.pos_fname pos1.pos_lnum (pos1.pos_cnum - pos1.pos_bol)
        pos2.pos_lnum (pos2.pos_cnum - pos2.pos_bol + 1)
        lexeme;
      raise (ExitMain PAR)
  in
  close_in input;
  parseRes

(* Our reference compiler should allow for stopping at different phases
   in the compilation and allow us to pick the right backend. We implement
   this using a straightforward command-line parsing/checking *)


(* --- command-line checking; dispatching to the right phase --- *)

(* observe that we make sure that exit flags are raised upon
   invalid return from each phase *)
let tiger {file;phase;unfold;out; _} =
  let exitCode = ref 0 in

  begin
    try
      match phase with
      | LEX ->
        lexonly file out
      | PAR ->
        file |> parse
        |> Prabsyn.print_exp out
      | SEM ->
        file |> parse
        |> semant
        |> Prtabsyn.print_exp unfold out
      | HOIST ->
        file |> parse
        |> semant
        |> hoist
        |> Pp_habsyn.print_program out
      | JS ->
        file |> parse
        |> semant
        |> hoist
        |> js file out
      | LLVM ->
        file |> parse
        |> semant
        |> hoist
        |> llvm |> Ll.string_of_prog
        |> (fun ll_s1 -> let open Llextra in
             let ll_s2 = Format.sprintf
                 "%s\n\n%s\n%s" ll_target_triple runtime_fns ll_s1 in
             Format.fprintf out "%s" ll_s2
           )
      | X86 ->
        file |> parse
        |> semant
        |> hoist
        |> llvm
        |> x86
        |> X86.string_of_prog
        |> Format.fprintf out "%s\n"
    with
      ExitMain p -> exitCode := (error_code p)
  end;
  Format.pp_print_flush out ();
  flush_all();
  exit (!exitCode) (* obs: exits the program *)

let llvm file out =
  let exitCode = ref 0 in
  begin
    try
      file |> llvmparse
      |> x86
      |> X86.string_of_prog
      |> Format.fprintf out "%s\n"
    with
      ExitMain p -> exitCode := (error_code p)
  end;
  Format.pp_print_flush out ();
  flush_all();
  exit (!exitCode) (* obs: exits the program *)

(* --- program entry point: prep work wrt command line args --- *)

open Cmdliner

type language = TIG | LL

let src_arg =
  let doc = "Source file $(docv)." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let dst_arg =
  let doc = "Output to $(docv)." in
  Arg.(value & opt (some string) None & info ["o";"out"] ~docv:"FILE" ~doc)

type norm_cnd =
  | NONE | PREVIOUS | ALL
let norm_arg =
  let ls = [("none", NONE); ("previous", PREVIOUS); ("all", ALL)] in
  let doc = "Select $(docv) phases to normalize. The value $(docv) must be " ^
            Arg.doc_alts_enum ls ^ "." in
  Arg.(value & opt (enum ls) PREVIOUS & info ["n";"normalize"] ~docv:"WHICH" ~doc)

let phase_arg =
  let ls = [("lex", LEX); ("par", PAR); ("sem", SEM); ("hoist", HOIST); ("js", JS); ("llvm", LLVM); ("x86", X86)] in
  let doc =
    "Compile to $(docv). The value $(docv) must be " ^
    Arg.doc_alts_enum ls ^ ". Ignored if $(b,language) is $(b,llvm)." in
  Arg.(value & opt (enum ls) X86 & info ["p";"phase"] ~docv:"PHASE" ~doc)

let unfold_arg =
  let doc = "Unfold name-types $(docv) levels when pretty-printing." in
  Arg.(value & opt int 0 & info ["u";"unfold"] ~docv:"N" ~doc)

let language_arg =
  let ls = [("tiger", TIG); ("llvm", LL)] in
  let doc = "Source $(docv). The value $(docv) must be " ^
            Arg.doc_alts_enum ls ^ "." in
  Arg.(value & opt (enum ls) TIG & info ["l";"language"] ~docv:"LANG" ~doc)

let check file out_opt phase norm unfold language =
  let out =
    match out_opt with
    | None -> Format.std_formatter
    | Some s -> Format.formatter_of_out_channel (Stdio.Out_channel.create s) in

  let norm_cnd =
    match norm with
    | NONE -> (fun _ _ -> false)
    | PREVIOUS -> isBefore
    | ALL -> (fun _ _ -> true) in

  if unfold < 0
  then (Printf.eprintf "Unfold argument must be non-negative.\n%!"; exit 1);

  match language with
  | TIG ->
    tiger {file;out;phase;norm_cnd;unfold}
  | LL ->
    llvm file out

let main_t =
  Term.(const check $ src_arg $ dst_arg $ phase_arg $ norm_arg $ unfold_arg $ language_arg)

let info =
  let doc = "Tiger AU reference compiler." in
  let success = Cmd.Exit.info 0 ~doc:"on success" in
  let lex_exit = Cmd.Exit.info 10 ~doc:"on lexing error" in
  let par_exit = Cmd.Exit.info 20 ~doc:"on parsing error" in
  let sem_exit = Cmd.Exit.info 30 ~doc:"on semant error" in
  let hoist_exit = Cmd.Exit.info 32 ~doc:"on hoisting error" in
  let llvm_exit = Cmd.Exit.info 40 ~doc:"on llcodegen error" in
  let x86_exit = Cmd.Exit.info 50 ~doc:"on backend error" in
  Cmd.info "tigerc" ~version:"v0.2" ~doc
    ~exits:[success;lex_exit;par_exit;sem_exit;hoist_exit;llvm_exit;x86_exit]

let main () = Cmd.v info main_t |> Cmd.eval |> exit
