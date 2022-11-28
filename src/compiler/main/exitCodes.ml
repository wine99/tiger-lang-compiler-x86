open Phases

let success_code _ = 0

let error_code = function
| LEX   -> 10
| PAR   -> 20
| SEM   -> 30
| HOIST -> 32
| JS    -> 35
| LLVM  -> 40
| X86   -> 50