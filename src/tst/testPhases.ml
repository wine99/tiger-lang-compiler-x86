module StringMap = Map.Make (String)

type assignment = Lex | Par | Sem | LL | XAsm 
module AssignmentMap = Map.Make (
    struct type t = assignment let compare = compare end)
module IntSet = Set.Make (Int)
type featursets = IntSet.t AssignmentMap.t


type runmode = Batch | Interactive (* the interactive mode is not yet supported *)

type testphase 
  = LEX | PAR | SEM | HOIST | LL of runmode | X86 of runmode 

type featureset = assignment * int 

let phaseName = function 
    LEX -> "Lexer" 
  | PAR -> "Parser"
  | SEM -> "Semant"
  | HOIST -> "Hoist"
  | LL Batch -> "LLBatch"
  | LL Interactive -> "LLInter"
  | X86 Batch -> "x86Batch"
  | X86 Interactive -> "x86Inter"

type options = { use_filter: Str.regexp option 
; overwrite: bool
; feature_map: featursets StringMap.t 
; fs_exclusive: string list option
; fs_regexp: Str.regexp option }  

let phase_assignment_agreement p a = 
  match p,a with 
    LEX, Lex
  | PAR, Par
  | SEM, Sem 
  | LL _, LL 
  | X86 _ , XAsm -> true 
  | _ -> false 

let assignment_of_phase p = match p with 
    LEX -> Some Lex
  | PAR -> Some Par
  | SEM -> Some Sem 
  | LL _ -> Some LL 
  | X86 _ -> Some XAsm 
  | HOIST -> None 
  

let string_of_assignment a = 
  match a with
     Lex -> "lex" 
  |  Par -> "par" 
  |  Sem -> "sem"
  |  LL -> "llvm"
  |  XAsm -> "xasm"  


let string_of_featureset (a,j) = 
  (string_of_assignment a) ^ (string_of_int j)
