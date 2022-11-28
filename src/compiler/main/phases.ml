
type phase = LEX | PAR | SEM | HOIST | JS | LLVM | X86
type phase_relation = phase -> phase -> bool

let toHandle = function
| LEX   -> "lex"
| PAR   -> "par"
| SEM   -> "sem"
| HOIST -> "hoist"
| JS    -> "js"
| LLVM  -> "llvm"
| X86   -> "x86"

let fromHandleOpt = function
| "lex"   -> Some LEX
| "par"   -> Some PAR
| "sem"   -> Some SEM
| "hoist" -> Some HOIST 
| "js"    -> Some JS
| "llvm"  -> Some LLVM
| "x86"   -> Some X86
| _       -> None

let toCode = function
| LEX   -> 1.0
| PAR   -> 2.0
| SEM   -> 3.0
| HOIST -> 3.25
| JS    -> 3.5
| LLVM  -> 4.0
| X86   -> 5.0

let isBefore a b =
  toCode a < toCode b

let isBeforeOrNow a b =
  toCode a <= toCode b
