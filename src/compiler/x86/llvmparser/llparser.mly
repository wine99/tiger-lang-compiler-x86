%{
  open Tigercommon
  open Tigercommon.Ll
  module S = Symbol
%}

%token STAR COMMA COLON EQUALS EOF
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET 
%token TYPE CROSS I1 I8 I32 I64 VOID
%token ADD SUB MUL SDIV
%token EQ NE SLT SLE SGT SGE
%token AND OR XOR SHL LSHR ASHR
%token RET BR TO NULL LABEL ENTRY GLOBAL DEFINE
%token CALL ICMP LOAD STORE ALLOCA BITCAST GEP ZEXT PTRTOINT

%token <int> INT        (* int64 values *)
%token <Tigercommon.Symbol.symbol> LBL   (* labels *)
%token <Tigercommon.Symbol.symbol> GID   (* global identifier *)
%token <Tigercommon.Symbol.symbol> UID   (* local identifier *)
%token <string> STRING  (* string literals *)

%start <Tigercommon.Ll.prog> prog
%%

%inline typed(X): t=ty x=X { (t,x) }

prog:
  | ds=decls EOF
    { ds }

decls:
  | ds = decls_rev
    { { tdecls = List.rev ds.tdecls
      ; gdecls = List.rev ds.gdecls
      ; fdecls = List.rev ds.fdecls
    } }

decls_rev:
  | (* empty *)
    { { tdecls = [] ; gdecls = [] ; fdecls = [] } }
  | ds=decls_rev f=fdecl
    { { ds with fdecls = f :: ds.fdecls }  }
  | ds=decls_rev g=gdecl
    { { ds with gdecls = g :: ds.gdecls }  }
  | ds=decls_rev t=tdecl
    { { ds with tdecls = t :: ds.tdecls }  }

fdecl:
  | DEFINE t=ty l=GID
    LPAREN params=separated_list(COMMA,typed(UID)) RPAREN
    LBRACE eb=entry_block bs=list(labeled_block) RBRACE
    { (l, { fty = (List.map fst params, t)
          ; param = List.map snd params
          ; cfg = (eb, bs)
          }
    ) }

gdecl:
  | g=GID EQUALS GLOBAL tgi=typed(ginit)
    { (g, tgi) }

tdecl:
  | tid=UID EQUALS TYPE t=ty
    { (tid, t) }

entry_block:
  | ENTRY COLON b=block     { b }
  | b=block                 { b }

block:
  | is=list(named_insn) t=terminator
    { { insns = is; terminator=t }  }

labeled_block:
  | l=LBL COLON b=block 
    { (l,b) }

terminator:
  | RET t=ty o=operand?
    { Ret (t, o) }
  | BR LABEL l=UID
    { Br l }
  | BR I1 o=operand COMMA LABEL l1=UID COMMA LABEL l2=UID
    { Cbr (o, l1, l2) }

operand:
  | NULL            { Null }
  | i=INT           { Const i }
  | g=GID           { Gid g }
  | u=UID           { Id u }

ty:
  | t=ty STAR       { Ptr t }
  | VOID            { Void }
  | I1              { I1 }
  | I8              { I8 }
  | I32             { I64 }
  | I64             { I64 }
  | LBRACE ts=ty_list RBRACE
    { Struct ts }
  | LBRACKET i=INT CROSS t=ty RBRACKET
    { Array (i,t) }
  | rt=ty LPAREN ts=ty_list RPAREN
    { Fun (ts, rt) }
  | t=UID           { Namedt t }

ty_list:
  | ts=separated_list(COMMA,ty)
    { ts }

gep_path:
  | path=separated_nonempty_list(COMMA,typed(operand))
    { List.map snd path }

bop:
  | OR { Or }
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mul }
  | SDIV { SDiv }
  | SHL { Shl }
  | XOR { Xor }      
  | AND { And }
  | LSHR { Lshr }
  | ASHR { Ashr }

cnd:
  | EQ { Eq }
  | NE { Ne }
  | SLT { Slt }
  | SLE { Sle }
  | SGT { Sgt }
  | SGE { Sge }

named_insn:
| u_opt=terminated(UID,EQUALS)? i=insn
  { u_opt, i }

insn:
  | b=bop t=ty o1=operand COMMA o2=operand
    { Binop (b,t,o1,o2) }
  | ALLOCA t=ty
    { Alloca t }
  | LOAD t=ty COMMA ty o=operand
    { Load (t,o) }
  | STORE t1=ty o1=operand COMMA ty o2=operand
    { Store (t1,o1,o2) }
  | ICMP c=cnd t=ty o1=operand COMMA o2=operand
    { Icmp (c,t,o1,o2) }
  | CALL t=ty o=operand LPAREN args=separated_list(COMMA,typed(operand)) RPAREN
    { Call (t, o, args) }
  | BITCAST t1=ty o=operand TO t2=ty
    { Bitcast (t1,o,t2) }
  | GEP t=ty COMMA path=gep_path
    { Gep (t, List.hd path, List.tl path) }
  | ZEXT t1=ty o=operand TO t2=ty
    { Zext (t1,o,t2) }
  | PTRTOINT t1=ty STAR o=operand TO t2=ty
    { Ptrtoint (t1,o,t2) }

ty_ginit_list:
  | gs=separated_list(COMMA,typed(ginit))
    { gs }

ginit:
  | NULL          { GNull }
  | g=GID         { GGid g }
  | i=INT         { GInt i }
  | s=STRING      { GString s }
  | LBRACKET gs=ty_ginit_list RBRACKET
    { GArray gs }
  | LBRACE gs=ty_ginit_list RBRACE
    { GStruct gs }
