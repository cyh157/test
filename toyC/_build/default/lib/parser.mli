
(* The type of tokens. *)

type token = 
  | WHILE
  | VOID
  | SEMI
  | RPAREN
  | RETURN
  | RBRACE
  | PLUS
  | OR
  | NUMBER of (int)
  | NOT
  | NEQ
  | MUL
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LEQ
  | LBRACE
  | INT
  | IF
  | ID of (string)
  | GT
  | GEQ
  | EQ
  | EOF
  | ELSE
  | DIV
  | CONTINUE
  | COMMA
  | BREAK
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val comp_unit: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.comp_unit)
