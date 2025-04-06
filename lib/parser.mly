%{
  open Ast
  open Location
%} 

/* Token declarations */
%token EOF
%token ASSIGN /* '=' */
%token OR
%token AND
%token EQ NEQ GT LT GEQ LEQ
%token PLUS MINUS TIMES DIV MOD
%token ASSIGN_PLUS ASSIGN_MINUS ASSIGN_TIMES ASSIGN_DIV ASSIGN_MOD
%token PLUSPLUS MINUSMINUS
%token REF NOT /* '&', '!' */
%token L_BRACKET R_BRACKET LS_BRACKET RS_BRACKET LR_BRACKET RR_BRACKET /* '{', '}', '['. ']', '(', ')' */
%token DOT COMMA COLON SEMICOLON
%token ARROW /* '<-' */
%token <string>ID
%token <int>INT
%token <char>CHAR
%token <bool>BOOL
/* Key word tokens */
%token IF ELSE WHILE DO FOR
%token VAR DEF
%token KW_INT KW_CHAR KW_VOID KW_BOOL
%token INTERFACE USES PROVIDES COMPONENT CONNECT RETURN

/* Precedence and associativity specification */
%nonassoc THEN
%nonassoc ELSE
%right ASSIGN_PLUS ASSIGN_MINUS ASSIGN_TIMES ASSIGN_DIV ASSIGN_MOD
%right ASSIGN
%left OR
%left AND
%left EQ NEQ
%nonassoc GT LT GEQ LEQ
%left PLUS MINUS
%left TIMES DIV MOD
%right MINUSMINUS
%nonassoc UMINUS
%nonassoc NOT

/* Start symbol */
%start compilation_unit
%type <Ast.located_compilation_unit> compilation_unit 

%% 


/* Grammar Specification */

compilation_unit:
  | td = list(top_decl) EOF       
    { 
      let rec make_compilation_unit _interfaces _components _connections = function
        | [] -> (CompilationUnit({ interfaces = _interfaces; components = _components; connections = _connections; }))
        | x::xs -> 
          match x with
            | Interface(i) -> (make_compilation_unit (i::_interfaces) _components _connections xs)
            | Component(c) -> (make_compilation_unit _interfaces (c::_components) _connections xs)
            | Connection(c) -> (make_compilation_unit _interfaces _components (c::_connections) xs)
            | ConnectionList(cl) -> (make_compilation_unit _interfaces _components (cl@_connections) xs)
        in make_compilation_unit [] [] [] td
    }                   
;

top_decl:
  | i = interface
    { Interface(i) }
  | c = component
    { Component(c) }
  | c = connection
    { Connection(c) }
  | cl = connection_list
    { ConnectionList(cl) }
;

interface:
  | INTERFACE id = ID L_BRACKET imd = nonempty_list(i_member_decl) R_BRACKET
    { make_node (InterfaceDecl({ iname = id; declarations = imd})) (to_code_position $loc) }
;

component:
  | COMPONENT id = ID pc = option(provide_clause) uc = option(use_clause) L_BRACKET cmd=nonempty_list(c_member_decl) R_BRACKET
    {
      let optlist_to_list = function
        | None -> []
        | Some l -> l
      in
        (make_node (ComponentDecl({ cname = id; uses = (optlist_to_list uc); provides = (optlist_to_list pc); definitions = cmd; })) (to_code_position $loc)) 
    }
;

connection:
  | CONNECT l = link option(SEMICOLON)
    { l }
;

connection_list:
  | CONNECT L_BRACKET ll = list(connect) R_BRACKET
    { ll }
;

connect:
  l = link SEMICOLON
    { l }
;

link:
  | id1 = ID DOT id2 = ID ARROW id3 = ID DOT id4 = ID
    { Link(id1, id2, id3, id4) }
;

i_member_decl:
  | VAR v = var_sign SEMICOLON
    { make_node (VarDecl(v)) (to_code_position $loc) }
  | fp = fun_proto SEMICOLON
    { make_node (FunDecl(fp)) (to_code_position $loc) }
;

provide_clause:
  | PROVIDES l = separated_nonempty_list(COMMA, ID)
    { l }
;

use_clause:
  | USES l = separated_nonempty_list(COMMA, ID)
    { l }
;

var_sign:
  | id = ID COLON t = l_type
    { (id, t) }
;

fun_proto:
  | DEF id = ID LR_BRACKET RR_BRACKET
    { { rtype = TVoid; fname = id; formals = []; body = None; } }
  | DEF id = ID LR_BRACKET l = separated_nonempty_list(COMMA, var_sign) RR_BRACKET
    { { rtype = TVoid; fname = id; formals = l; body = None; } }
  | DEF id = ID LR_BRACKET RR_BRACKET COLON bt = basic_type
    { { rtype = bt; fname = id; formals = []; body = None; } }
  | DEF id = ID LR_BRACKET l = separated_nonempty_list(COMMA, var_sign) RR_BRACKET COLON bt = basic_type
    { { rtype = bt; fname = id; formals = l; body = None; } }
;

c_member_decl:
  | VAR v = var_sign SEMICOLON
    { make_node (VarDecl(v)) (to_code_position $loc) }
  | fd = fun_decl
    { make_node (FunDecl(fd)) (to_code_position $loc) }
;

fun_decl:
  | fp = fun_proto b = block
    { { fp with body = Some b } }
;

block:
  | L_BRACKET ba = list(block_aux) R_BRACKET
    { make_node (Block(ba)) (to_code_position $loc) }
;

block_aux:
  | s = stmt
    { make_node (Stmt(s)) (to_code_position $loc) }
  | VAR vs = var_sign SEMICOLON
    { make_node (LocalDecl(vs)) (to_code_position $loc) }
;

l_type:
  | bt = basic_type
    { bt }
  | t = l_type LS_BRACKET RS_BRACKET
    { TArray(t, None) }
  | t = l_type LS_BRACKET i = INT RS_BRACKET
    { TArray(t, Some i) }
  | REF bt = basic_type
    { TRef(bt) } 
;

basic_type:
  | KW_INT
    { TInt }
  | KW_CHAR
    { TChar }
  | KW_BOOL
    { TBool }
  | KW_VOID
    { TVoid }
;

stmt:
  | SEMICOLON
    { make_node (Skip) (to_code_position $loc) }
  | RETURN e = option(expr) SEMICOLON
    { make_node (Return(e)) (to_code_position $loc) }
  | e = expr SEMICOLON
    { make_node (Expr(e)) (to_code_position $loc) } 
  | b = block
    { b }
  | WHILE LR_BRACKET e = expr RR_BRACKET s = stmt
    { make_node (While(e, s)) (to_code_position $loc) }
  | DO s = stmt WHILE LR_BRACKET e = expr RR_BRACKET SEMICOLON
    { make_node (DoWhile(e, s)) (to_code_position $loc) }
  | FOR LR_BRACKET e1 = option(expr) SEMICOLON e2 = option(expr) SEMICOLON e3 = option(expr) RR_BRACKET s = stmt
    { make_node (For(e1, e2, e3, s)) (to_code_position $loc) }
  | IF LR_BRACKET e = expr RR_BRACKET s1 = stmt ELSE s2 = stmt
    { make_node (If(e, s1, s2)) (to_code_position $loc) }
  | IF LR_BRACKET e = expr RR_BRACKET s1 = stmt %prec THEN
    { make_node (If(e, s1, (make_node (Skip) (to_code_position $loc)))) (to_code_position $loc) }
;

expr:
  | i = INT
    { make_node (ILiteral(i)) (to_code_position $loc) }
  | c = CHAR
    { make_node (CLiteral(c)) (to_code_position $loc) }
  | b = BOOL
    { make_node (BLiteral(b)) (to_code_position $loc) }
  | LR_BRACKET e = expr RR_BRACKET
    { e }
  | REF lv = l_value
    { make_node (Address(lv)) (to_code_position $loc) }
  | lv = l_value ASSIGN e = expr
    { make_node (Assign(lv, e)) (to_code_position $loc) }
  | NOT e = expr
    { make_node (UnaryOp(Not, e)) (to_code_position $loc) }
  | id = ID LR_BRACKET ls = option(separated_nonempty_list(COMMA, expr)) RR_BRACKET
    {
      let optlist_to_list = function
        | None -> []
        | Some l -> l
      in
        make_node (Call(None, id, (optlist_to_list ls))) (to_code_position $loc) 
      }
  | lv = l_value 
    { make_node (LV(lv)) (to_code_position $loc) }
  | MINUS e = expr %prec UMINUS
    { make_node (UnaryOp(Neg, e)) (to_code_position $loc) }
  | e1 = expr o = bin_op e2 = expr
    { make_node (BinaryOp(o, e1, e2)) (to_code_position $loc) }
  | PLUSPLUS lv = l_value 
    { make_node (IncDec(lv, PreInc)) (to_code_position $loc) }
  | lv = l_value  PLUSPLUS 
    { make_node (IncDec(lv, PostInc)) (to_code_position $loc) }
  | MINUSMINUS e = expr 
    { match (e.Ast.node) with 
      | LV(lv) -> make_node (IncDec(lv, PreDec)) (to_code_position $loc) 
      | _ -> make_node (UnaryOp(Neg, (make_node (UnaryOp(Neg, e)) (to_code_position $loc)))) (to_code_position $loc)
    }
  | lv = l_value MINUSMINUS 
    { make_node (IncDec(lv, PostDec)) (to_code_position $loc) }
  | lv = l_value o = bin_op_ass e = expr
    { make_node (Assign(lv, (make_node (BinaryOp(o, (make_node (LV(lv)) (to_code_position $loc)), e)) (to_code_position $loc)))) (to_code_position $loc) } 
;

l_value:
  | id = ID
    { make_node (AccVar(None, id)) (to_code_position $loc) }
  | id = ID LS_BRACKET e = expr RS_BRACKET
    { let lv = make_node (AccVar(None, id)) (to_code_position $loc) in
        make_node (AccIndex(lv, e)) (to_code_position $loc)
    }
;

%inline bin_op:
  | PLUS
    { Add }
  | MINUS
    { Sub }
  | TIMES
    { Mult }
  | DIV
    { Div }
  | MOD
    { Mod }
  | EQ
    { Equal }
  | NEQ
    { Neq }
  | LT
    { Less }
  | LEQ
    { Leq }
  | GT
    { Greater }
  | GEQ
    { Geq }
  | AND
    { And }
  | OR
    { Or }
;

%inline bin_op_ass:
  | ASSIGN_PLUS
    { Add }
  | ASSIGN_MINUS
    { Sub }
  | ASSIGN_TIMES
    { Mult }
  | ASSIGN_DIV
    { Div }
  | ASSIGN_MOD
    { Mod }
;