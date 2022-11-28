(**************************************************************************)
(* AU Compilation.                                                        *)
(**************************************************************************)

(* See comments in runtests.ml *)
open TestPhases
let runWithStatus cmd =
  let inp,outp,errp = Unix.open_process_full cmd @@ Unix.environment() in
  let i = Stdio.In_channel.input_all inp in
  let e = Stdio.In_channel.input_all errp in
  Stdio.In_channel.close inp;
  Stdio.Out_channel.close outp;
  Stdio.In_channel.close errp;
  let s = match e with
  | "" -> i
  | _ -> String.concat "\n" [i;"\n--- StdErr ---";e;] in
  (Unix.close_process_full (inp,outp,errp), s)

exception TestingFatal 
(* we only call this for positive test cases *)
let goldenFrontEnd phase code out file overwrite =
  let golden_ext = match phase with 
    LEX -> ".expected-lex"
  | PAR -> ".expected-par" 
  | SEM -> ".expected-sem"
  | _ ->  raise TestingFatal in
  let golden_file = file ^ golden_ext in
  match code, Sys.file_exists golden_file, overwrite with
  | 0, false, _ | 0, true, true ->
    (* succeeded, either no expected file or overwriting: write expected file *)
    Stdio.Out_channel.write_all golden_file ~data:out;
  | 0, true, false | _, true, _ -> 
    (* expected file found: check against it
       if compilation failed, it is still useful to see what we should have gotten *)
    let golden = Stdio.In_channel.read_all golden_file in
    if not (String.equal golden out)
    then DiffWriter.logDiff (Filename.basename file) (phaseName phase) golden_file out;
    Alcotest.(check string) ("matching output for " ^ file) golden out
  | _ ->
    (* error and no expected file: we can only fail the test *)
    Alcotest.fail out
 
let phaseFlag phase = "-p " ^ 
  match phase with 
   LEX -> "lex"|PAR ->"par"|SEM->"sem"| HOIST -> "hoist" | LL _ ->"llvm" |X86 _ ->"x86"
   

(* observe that if the exit code is non-zero we make no further checks *)  
let goldenWithExitCode expectedExitCode phase overwrite file () = 
  let flag = " " ^ phaseFlag phase in     
  let status,out = runWithStatus @@"./tigerc.sh " ^ file ^ flag in 
  match status with 
  | Unix.WEXITED 0 when expectedExitCode = 0  ->
      goldenFrontEnd phase 0 out file overwrite   (* only check the output on 0-exit *)
  | Unix.WEXITED code when expectedExitCode = 0 -> 
      goldenFrontEnd phase code
      out (*("<<runtests: test target finished with exit code " ^ (string_of_int code) ^ ". Output suppressed>>")*)
      file false
  | Unix.WEXITED 1 when expectedExitCode != 0 ->
      Printf.printf "%s\n" out; 
      Alcotest.fail "Uncaught exception during compilation"
  | Unix.WEXITED code ->
      Alcotest.(check int) ("matching exit codes") expectedExitCode code;
  | _ -> Alcotest.fail ("Exit via an interrupt or a signal")
 
(* exception NotImplemented  *)
let goldenBackend phase overwrite file () = 
  let tmpfile = Filename.temp_file (Filename.basename file) "" in 
  let ext = match phase with X86 _ -> ".s" | _ -> ".ll" in 
  let ll_or_asm_file = tmpfile ^ ext  in  
  let outfile = ll_or_asm_file ^ ".out" in 
  let flag = " " ^ phaseFlag phase ^ " --out=" ^ ll_or_asm_file in     
  let cmd = "./tigerc.sh " ^ file ^ flag in   
  let status,out = runWithStatus cmd in 
  match status with 
  | Unix.WEXITED 0 ->       
      if phase = HOIST then () else 
      let golden_file = file ^ ".expected-out" in   
      let runtime_c = "src/compiler/llcodegen/runtime.c" in 
      let cmd, runmode =
          match phase with 
            LL r -> 
              Printf.sprintf "clang %s %s -o %s" runtime_c ll_or_asm_file outfile, r 
          | X86 r -> 
              Printf.sprintf "clang %s %s -o %s" runtime_c ll_or_asm_file outfile, r 
          | _  -> raise TestingFatal in       
      let status, out = runWithStatus cmd in (
      match status with 
      | Unix.WEXITED 0 -> 
         if runmode = Batch then          
            let status, out = runWithStatus outfile in (
            match status with 
            Unix.WEXITED code  ->                
                let out_to_compare = 
                    if Sys.file_exists (file ^ ".ignore-code") 
                    then out 
                    else 
                      let sep = if out <> "" then "\n" else "" in 
                      out ^ sep ^ (string_of_int code) in 
                if (not (Sys.file_exists golden_file)) || overwrite 
                then Stdio.Out_channel.write_all golden_file ~data:out_to_compare
                else 
                  let golden = Stdio.In_channel.read_all golden_file in 
                  if not (String.equal golden out_to_compare)
                  then DiffWriter.logDiff (Filename.basename file) (phaseName phase) golden_file out_to_compare;
                  Alcotest.(check string) ("Matching program output") golden out_to_compare
            | _ -> Alcotest.fail ("Exit via an interrupt or a signal is not supported. This is probably a bug")
            )
      | _ -> 
        Alcotest.(check string) ("Matching compiler output") "" out; 
        Alcotest.fail ("Compiler error")

      )
  | _ -> Alcotest.(check string) ("Matching compiler output") "" out; 
         Alcotest.fail ("Compiler error")

let testFileWithTester nameFormatter tester name  = 
  (* let base = name |> Filename.basename |> Filename.remove_extension in  *)
  let open Alcotest in 
  test_case (nameFormatter name) `Quick (tester name) 
