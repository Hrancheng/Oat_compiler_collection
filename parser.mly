%{
open Ast
open Lexing

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token TWO_EQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */



(*Add more tokens, bool related three for new binop*)
%token TBOOL
%token TRUE
%token FALSE /* false */
%token FOR
%token NEW
%token LEFT_SHIFT
%token RIGHT_SHIFT
%token LT
%token GT
%token LTEQ
%token GTEQ
%token ARITH_RSHIFT
%token NOTEQ
%token MYAND
%token MYOR
%token BIT_AND
%token BIT_OR


%left BIT_OR
%left BIT_AND
%left MYOR
%left MYAND
%left TWO_EQ NOTEQ
%left LT LTEQ GT GTEQ
%left LEFT_SHIFT RIGHT_SHIFT ARITH_RSHIFT
%left PLUS DASH
%left STAR

%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | r=rtyp { TRef r } 
  | TBOOL   { TBool }


%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | TWO_EQ   { Eq }
  | NOTEQ { Neq }
  | BIT_AND { IAnd }
  | BIT_OR { IOr }
  | LEFT_SHIFT { Shl }
  | RIGHT_SHIFT { Shr }
  | ARITH_RSHIFT { Sar }
  | GT { Gt }
  | GTEQ { Gte }
  | LT { Lt }
  | LTEQ { Lte }
  | MYAND { And }
  | MYOR { Or }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=ty LBRACKET RBRACKET NULL { loc $startpos $endpos @@ CNull (RArray t) }
  | NEW t=ty LBRACKET RBRACKET LBRACE l=separated_list(COMMA, gexp) RBRACE 
      { loc $startpos $endpos @@ CArr (t, l) }
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT        { loc $startpos $endpos @@ CInt i }
  | s=STRING     { loc $startpos $endpos @@ CStr s }
  | t=TRUE       { loc $startpos $endpos @@ CBool true }
  | f=FALSE      { loc $startpos $endpos @@ CBool false }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | NEW t=ty LBRACKET RBRACKET LBRACE l=separated_list(COMMA, exp) RBRACE 
      { loc $startpos $endpos @@ CArr (t, l) }
  | NEW t=ty LBRACKET i=exp RBRACKET    
      { loc $startpos $endpos @@ NewArr (t, i) }
  | i=INT        { loc $startpos $endpos @@ CInt i }
  | s=STRING     { loc $startpos $endpos @@ CStr s }
  | id=IDENT     { loc $startpos $endpos @@ Id id }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp  { loc $startpos $endpos @@ Uop (u, e) }
  | t=TRUE       { loc $startpos $endpos @@ CBool true }
  | f=FALSE      { loc $startpos $endpos @@ CBool false }
  | e=exp LBRACKET i=exp RBRACKET
      { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
      { loc $startpos $endpos @@ Call (e, es) }
  | LPAREN e=exp RPAREN { e }

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

(*vdecls ::= | vdecl1, vdecl2, ...., vdecln*)
vdecls:
  | l=separated_list(COMMA, vdecl) { l }

exp_opt:
  | { None }
  | e=exp { Some e }

stmt_opt:
  | { None }
  | s=stmt { Some s }
(*lhs, vdecl, return exp, return, id(exp1...), if_stmt, for(vdecl; exp-opt, stmt-opt)block), 
while(exp)block*)

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 
  | FOR LPAREN v=vdecls SEMI e=exp_opt SEMI s=stmt_opt RPAREN b=block
                        { loc $startpos $endpos @@ For(v, e, s, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
