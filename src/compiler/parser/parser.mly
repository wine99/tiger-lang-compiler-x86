(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

%{
  open Tigercommon.Absyn   
  open ParserAux 
%}

%token EOF
%token <string> ID
%token <int> INT 
%token <string> STRING 
%token COMMA COLON SEMICOLON 
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE 
%token DOT PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE 
%token AND OR ASSIGN ARRAY IF THEN ELSE WHILE FOR TO DO
%token LET IN END OF BREAK NIL FUNCTION VAR TYPE CARET 


%start <Tigercommon.Absyn.exp> program  
(* Observe that we need to use fully qualified types for the start symbol *)

%%
(* Expressions *)
exp_base:
| NIL  { NilExp}
| i=INT  { IntExp i }
| s=STRING { StringExp s }

(* Top-level *)
program: e = exp EOF { e }


exp:
| e=exp_base  { e ^! $startpos }
