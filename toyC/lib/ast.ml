(* Ast.ml *)
type typ = Int | Void

type param = {
  typ : typ;
  name : string;
}

type bin_op =
  | Add | Sub | Mul | Div | Mod        (* 算术运算 *)
  | Lt | Gt | Leq | Geq | Eq | Neq    (* 关系运算 *)
  | And | Or                          (* 逻辑运算 *)

type unary_op = Plus | Minus | Not    (* 一元运算 *)

type expr =
  | Num of int                        (* 数字常量，如 10 *)
  | Var of string                     (* 变量，如 a *)
  | Call of string * expr list        (* 函数调用，如 f(1, 2) *)
  | Unary of unary_op * expr          (* 一元表达式，如 !a、-b *)
  | Binary of bin_op * expr * expr    (* 二元表达式，如 a + b、a > 5 *)

type stmt =
  | BlockStmt of block                (* 语句块，如 { ... } *)
  | EmptyStmt                         (* 空语句，如 ; *)
  | ExprStmt of expr                  (* 表达式语句，如 a = 5; *)
  | DeclStmt of typ * string * expr option (* 变量声明，如 int a = 10; *)
  | AssignStmt of string * expr       (* 赋值语句，如 a = 5; *)
  | IfStmt of expr * stmt * stmt option (* if 语句，如 if (a>5) { ... } else { ... } *)
  | WhileStmt of expr * stmt          (* while 语句，如 while (a>0) { ... } *)
  | BreakStmt                         (* break 语句 *)
  | ContinueStmt                      (* continue 语句 *)
  | ReturnStmt of expr option         (* return 语句，如 return a; 或 return; *)

and block = {
  stmts : stmt list;                  (* 语句块内的语句列表 *)
}

type func_def = {
  ret_type : typ;                     (* 函数返回类型：int/void *)
  name : string;                      (* 函数名，如 main *)
  params : param list;                (* 形参列表 *)
  body : block;                       (* 函数体（语句块） *)
}

type comp_unit = func_def list        (* 编译单元：多个函数定义 *)