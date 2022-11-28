(**************************************************************************)
(* AU Compilation.                                                        *)
(**************************************************************************)

(**  Golden testing for Tiger *)

(* This file implements a golden test harness for Tiger compiler. As such it is
complete but student submissions are welcome to modify it in any way 
they fit. *)



(**************************************************************************)
(*               MAIN OPTION TO CHANGE BETWEEN ASSIGNMENTS                *)   


let defaultPhasesToCheck = 
  let open TestPhases in 
    [ 
     X86 Batch; X86 Interactive
    ]
        
          
(* obs: for student code the above list must correspond to only one phase *)

(**************************************************************************)


open Cmdliner

let only_flag =   
  let doc = "Only pick filenames matching the regular expression $(i,REGEXP)." in
  Arg.(value & opt (some string) None & info ["only"] ~doc ~docv:"REGEXP")


let overwrite_flag =
  let doc = "Overwrite expected files." in
  Arg.(value & flag & info ["overwrite-expected"] ~doc)
 
let featureset_exclusive_flag =
  let doc = "Choose feature sets by comma separated $(docv)." in
  Arg.(value & opt (some (list string)) None & info ["fs-list";"feature-sets-list"] ~doc ~docv:"LIST")

let featuresetregexp_flag =
  let doc = "Choose feature sets matching the regular expression $(i,REGEXP)." in
  Arg.(value & opt (some string) None & info ["fs";"feature-sets"] ~doc ~docv:"REGEXP")

let init_testsets featureSetMap only overwrite fs_exclusive fs_regexp =
  DefaultTesting.defaultTestsForPhases
     { use_filter = Option.map Str.regexp only
     ; overwrite 
     ; feature_map = featureSetMap
     ; fs_exclusive
     ; fs_regexp = Option.map (fun s -> Str.regexp s ) fs_regexp
     } 
     defaultPhasesToCheck 

let init_testsets_t fs = Term.(const (init_testsets fs)
    $ only_flag $ overwrite_flag $featureset_exclusive_flag $featuresetregexp_flag)

let dummy_testsets_t = Term.(const (fun _ _ _ _-> ()) 
    $ only_flag $ overwrite_flag $featureset_exclusive_flag $featuresetregexp_flag)  

let () = 
  Printexc.record_backtrace false;  
      (* Dear Jane Street folks, please stop messing with other people's global state *) 
      (* https://github.com/janestreet/base/issues/77 *)

  FeatureSets.checkJsonPath();
  let featureSetMap = FeatureSets.readJson () in 
  match Cmd.eval_peek_opts (init_testsets_t featureSetMap) with 
    (* 2020-08-20; a gentle hack; AA 
       We abuse the eval_peek_opts function to process our custom optional 
       arguments to the tool and create the dataset based on them
       *)
    Some tests, _ ->
      ( try
          Alcotest.run_with_args 
            "TigerCompiler" dummy_testsets_t tests ~and_exit:false
            (* Use dummy_testsets to ensure that we show the flags in 
               the --help option, etc *)
        with | _  -> ()
      );
      let diff_file= "_build/_tests/diff-recent.html" in
      DiffWriter.writeResults diff_file;
      Printf.printf 
          " The diff of the most recent test run is available in %s\n" 
          diff_file 
    | _ -> Alcotest.run_with_args "Tiger compiler" dummy_testsets_t []  (* let the tool show the exception *)
   

