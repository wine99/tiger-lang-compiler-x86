{
  open Llparser
  module S = Tigercommon.Symbol
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
  let hex2str hex =
    "0x" ^ hex |> int_of_string
               |> Char.chr
               |> Printf.sprintf "%c"
}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let hex = letter | digit
let idchar = letter | digit | ['.' '_' '-' '$']

rule token = parse
  | eof                { EOF }
  | ['\t' ' ']+        { token lexbuf }
  | '\n'               { Lexing.new_line lexbuf; token lexbuf }
  | '*'                { STAR }
  | ','                { COMMA }
  | ':'                { COLON }
  | '='                { EQUALS }
  | '('                { LPAREN }
  | ')'                { RPAREN }
  | '{'                { LBRACE }
  | '}'                { RBRACE }
  | '['                { LBRACKET }
  | ']'                { RBRACKET }
  | "i1"               { I1 }
  | "i8"               { I8 }
  | "i32"              { I32 }
  | "i64"              { I64 }
  | "to"               { TO }
  | "br"               { BR }
  | "eq"               { EQ }
  | "ne"               { NE }
  | "or"               { OR }
  | "and"              { AND }
  | "add"              { ADD }
  | "sub"              { SUB }
  | "mul"              { MUL }
  | "sdiv"             { SDIV }
  | "xor"              { XOR }
  | "slt"              { SLT }
  | "sle"              { SLE }
  | "sgt"              { SGT }
  | "sge"              { SGE }
  | "shl"              { SHL }
  | "ret"              { RET }
  | "getelementptr"    { GEP }
  | "zext"             { ZEXT }
  | "ptrtoint"         { PTRTOINT }
  | "type"             { TYPE }
  | "null"             { NULL }
  | "lshr"             { LSHR }
  | "ashr"             { ASHR }
  | "call"             { CALL }
  | "icmp"             { ICMP }
  | "void"             { VOID }
  | "load"             { LOAD }
  | "entry"            { ENTRY }
  | "store"            { STORE }
  | "label"            { LABEL }
  | "global"           { GLOBAL }
  | "define"           { DEFINE }
  | "alloca"           { ALLOCA }
  | "bitcast"          { BITCAST }
  | '%' (idchar+ as i) { UID (S.symbol i) }
  | '@' (idchar+ as i) { GID (S.symbol i) }
  | "x"                           { CROSS } (* for Array types *)
  | '-'? digit+ as d              { INT (int_of_string d) }
  | idchar+ as i                  { LBL (S.symbol i) }
  | ";" ([^'\n']*) '\n'           { token lexbuf } (* ignored *)
  | "declare" [^'\n']* '\n'       { token lexbuf } (* ignored *)
  | "target"  [^'\n']* '\n'       { token lexbuf } (* ignored *)
  | "c\""                         { string "" lexbuf }
  | _ as c                        { error lexbuf @@ "Unexpected character: " ^ Char.escaped c }

and string current = parse
  | '\"'                { STRING current }
  | '\n'                { error lexbuf "Illegal newline in string" }
  | '\\' ['\\' '\"'] as e
                        { string (current^(Scanf.unescaped e)) lexbuf }
  | '\\' (hex hex as h)
                        { string (current^(hex2str h)) lexbuf }
  | [' '-'~']           { string (current^(Lexing.lexeme lexbuf)) lexbuf }
  | eof                 { error lexbuf "Unclosed string at end of file" }
  | _ as c              { error lexbuf @@ "Illegal character '" ^ (String.make 1 c) ^ "'" }
