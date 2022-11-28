
let json_file = "testcases/feature_sets.json"

let checkJsonPath () = 
  if not (Sys.file_exists json_file) 
  then failwith @@ "cannot find json file " ^ json_file

open TestPhases

let normalize_feature_string s' =
  let s = String.trim s' in  
  let n = String.length s in 
  let last_char = s.[n-1] in
  let s'' = if last_char = '+' || last_char = '-' then 
            String.sub s' 0 (n-1)  else s' in 
  String.uppercase_ascii s''


let string_to_featureset s = 
  let s_norm = normalize_feature_string s in 
  let asgmt = 
    match s_norm with 
      "LEX0" | "LEX1" | "LEX2" -> Lex
    | "PAR0" | "PAR1" | "PAR2" | "PAR3" -> Par 
    | "SEM0" | "SEM1" | "SEM2" | "SEM3" -> Sem 
    | "LLVM0" | "LLVM1" | "LLVM2" | "LLVM3" | "LLVM4" -> LL
    | "XASM1" | "XASM2" | "XASM3" | "XASM4"  -> XAsm 
    (* 2020-08-23; AA; TODO: better error reporting *)
    | _ -> failwith @@ "Unrecognized featureset " ^ s in 
  let j = String.sub s_norm (String.length s_norm - 1) 1 |> int_of_string in 
  (asgmt, j)

let string_list_to_featursets = 
  let f m (asgmt, i) = 
    let s = match AssignmentMap.find_opt asgmt m  with 
              Some s' -> s' 
            | None -> IntSet.empty in 
    let s' = if IntSet.mem i s 
               then failwith @@ "repeat featureset" ^ (string_of_featureset (asgmt, i))
               else IntSet.add i s in 
    AssignmentMap.add asgmt s' m in 
 List.fold_left f AssignmentMap.empty

let readJson (): featursets StringMap.t =
    let compose f g x = f (g x) in
    let json = Yojson.Basic.from_file json_file in 
    let open Yojson.Basic.Util in 
    let entries = json |> to_list in 
    let process_entry json = 
      let file0 = json |> member "file" |> to_string in 
      let file = "testcases/"^file0 in 
      let fs0 = json 
                |> member "feature-sets" 
                |> to_list 
                |> List.map (compose string_to_featureset to_string) 
                |> string_list_to_featursets in
      (file, fs0)
      in    
    let entries' = List.map process_entry entries in  
    StringMap.of_seq (Stdlib.List.to_seq entries')

