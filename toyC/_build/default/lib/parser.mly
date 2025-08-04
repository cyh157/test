%{
open Ast  (* 导入 AST 结构，用于构造节点 *)
%}

(* 声明 Token 类型（与 lexer.mll 输出严格一致） *)
%token <string> ID
%token <int> NUMBER
%token INT VOID IF ELSE WHILE BREAK CONTINUE RETURN
%token EQ NEQ LEQ GEQ AND OR ASSIGN PLUS MINUS MUL DIV MOD NOT LT GT
%token SEMI COMMA LPAREN RPAREN LBRACE RBRACE
%token EOF

(* 语法分析入口：编译单元（CompUnit），输出 AST 根节点 *)
%start comp_unit
%type <comp_unit> comp_unit

(* 非终结符类型声明（对应 AST 子结构） *)
%type <func_def> func_def
%type <param list> param_list
%type <param> param
%type <block> block
%type <stmt> stmt
%type <stmt list> stmt_list
%type <expr> expr lor_expr land_expr rel_expr add_expr mul_expr unary_expr primary_expr

%%  (* 分隔“声明段”与“规则段” *)

(* --------------------- 编译单元与函数定义 --------------------- *)
comp_unit:
  | funcs = list(func_def) EOF { funcs }  (* CompUnit → FuncDef⁺ *)
  ;

func_def:
  (* FuncDef → (“int”|“void”) ID “(” (Param (“,” Param))? “)” Block *)
  | INT name = ID LPAREN params = param_list RPAREN body = block
    { { ret_type = Int; name; params; body } }
  | VOID name = ID LPAREN params = param_list RPAREN body = block
    { { ret_type = Void; name; params; body } }
  ;

param_list:
| params = separated_nonempty_list(COMMA, param) { params }
| /* 空 */ { [] }

param:
  (* Param → “int” ID *)
  | INT name = ID { { typ = Int; name } }
  ;


(* --------------------- 语句与语句块 --------------------- *)
block:
  (* Block → “{” Stmt* “}” *)
  | LBRACE stmts = stmt_list RBRACE { { stmts } }
  ;

stmt_list:
  (* Stmt* → 多个语句 *)
  | stmts = list(stmt) { stmts }
  ;

stmt:
  (* Stmt 的多分支：Block | “;” | Expr “;” | ID “=” Expr “;” | “int” ID “=” Expr “;” | if/while/break/continue/return *)
  | block = block { BlockStmt block }                  (* 语句块 *)
  | SEMI { EmptyStmt }                                (* 空语句 *)
  | expr = expr SEMI { ExprStmt expr }                (* 表达式语句 *)
  | name = ID ASSIGN expr = expr SEMI { AssignStmt (name, expr) } (* 赋值语句 *)
  | INT name = ID ASSIGN expr = expr SEMI { DeclStmt (Int, name, Some expr) } (* 变量声明+赋值 *)
  | IF LPAREN cond = expr RPAREN then_stmt = stmt
    { IfStmt (cond, then_stmt, None) }           (* if 语句，无 else *)
  | IF LPAREN cond = expr RPAREN then_stmt = stmt ELSE else_stmt = stmt
    { IfStmt (cond, then_stmt, Some else_stmt) } (* if-else 语句 *)
  | WHILE LPAREN cond = expr RPAREN stmt = stmt { WhileStmt (cond, stmt) } (* while 语句 *)
  | BREAK SEMI { BreakStmt }                          (* break 语句 *)
  | CONTINUE SEMI { ContinueStmt }                    (* continue 语句 *)
  | RETURN SEMI { ReturnStmt None }                   (* return 语句（无返回值） *)
  | RETURN e=expr SEMI {ReturnStmt(Some e)}
  ;


(* --------------------- 表达式层级（从低到高） --------------------- *)
expr:
  (* Expr → LOrExpr *)
  | e = lor_expr { e }
  ;

lor_expr:
  (* LOrExpr → LAndExpr | LOrExpr “||” LAndExpr *)
  | e = land_expr { e }
  | e1 = lor_expr OR e2 = land_expr { Binary (Or, e1, e2) }
  ;

land_expr:
  (* LAndExpr → RelExpr | LAndExpr “&&” RelExpr *)
  | e = rel_expr { e }
  | e1 = land_expr AND e2 = rel_expr { Binary (And, e1, e2) }
  ;

rel_expr:
  (* RelExpr → AddExpr | RelExpr (“<”|“>”|“<=”|“>=”|“==”|“!=”) AddExpr *)
  | e = add_expr { e }
  | e1 = rel_expr op = rel_op e2 = add_expr { Binary (op, e1, e2) }
  ;

rel_op:  (* 关系运算符规则（无 %inline，独立规则） *)
  | LT { Lt }
  | GT { Gt }
  | LEQ { Leq }
  | GEQ { Geq }
  | EQ { Eq }
  | NEQ { Neq }
  ;

add_expr:
  (* AddExpr → MulExpr | AddExpr (“+”|“-”) MulExpr *)
  | e = mul_expr { e }
  | e1 = add_expr op = add_op e2 = mul_expr { Binary (op, e1, e2) }
  ;

add_op:  (* 加减运算符规则（无 %inline，独立规则） *)
  | PLUS { Add }
  | MINUS { Sub }
  ;

mul_expr:
  (* MulExpr → UnaryExpr | MulExpr (“*”|“/”|“%”) UnaryExpr *)
  | e = unary_expr { e }
  | e1 = mul_expr op = mul_op e2 = unary_expr { Binary (op, e1, e2) }
  ;

mul_op:  (* 乘除模运算符规则（无 %inline，独立规则） *)
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  ;

unary_expr:
  (* UnaryExpr → PrimaryExpr | (“+”|“-”|“!”) UnaryExpr *)
  | e = primary_expr { e }
  | op = unary_op e = unary_expr { Unary (op, e) }
  ;

unary_op:  (* 一元运算符规则（无 %inline，独立规则） *)
  | PLUS { Plus }
  | MINUS { Minus }
  | NOT { Not }
  ;

primary_expr:
  (* PrimaryExpr → ID | NUMBER | “(” Expr “)” | ID “(” (Expr (“,” Expr))? “)” *)
  | name = ID { Var name }                                (* 变量引用 *)
  | num = NUMBER { Num num }                              (* 数字常量 *)
  | LPAREN e = expr RPAREN { e }                          (* 括号表达式 *)
  | name = ID LPAREN args = expr_list RPAREN { Call (name, args) } (* 函数调用 *)
  ;

expr_list:
  (* (Expr (“,” Expr))? → 允许空列表 *)
  | args = separated_nonempty_list(COMMA, expr) { args }
  | /* 空 */ { [] }
  ;