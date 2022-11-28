
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
    "Darwin" -> "target triple = \"x86_64-apple-macosx11.0.0\""
  | "Linux"  -> "target triple = \"x86_64-pc-linux-gnu\""
  | _ -> ""
