{
open Parser  (* 导入语法分析器的Token类型 *)
exception LexicalError of string
}

(* 定义空白字符 *)
let whitespace = [' ' '\t' '\r']

(* 定义换行符 *)
let newline = '\n'

rule token = parse
  (* 关键字：必须在标识符前匹配 *)
  | "int"       { INT }
  | "void"      { VOID }
  | "if"        { IF }
  | "else"      { ELSE }
  | "while"     { WHILE }
  | "break"     { BREAK }
  | "continue"  { CONTINUE }
  | "return"    { RETURN }

  (* 运算符与标点：严格匹配ToyC文法 *)
  | "=="        { EQ }
  | "!="        { NEQ }
  | "<="        { LEQ }
  | ">="        { GEQ }
  | "&&"        { AND }
  | "||"        { OR }   (* ToyC是||，对应OR Token *)
  | "="         { ASSIGN }
  | "+"         { PLUS }
  | "-"         { MINUS }
  | "*"         { MUL }
  | "/"         { DIV }
  | "%"         { MOD }
  | "!"         { NOT }
  | "<"         { LT }
  | ">"         { GT }
  | ";"         { SEMI }
  | ","         { COMMA }
  | "("         { LPAREN }
  | ")"         { RPAREN }
  | "{"         { LBRACE }
  | "}"         { RBRACE }

  (* 标识符：变量名/函数名 *)
  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as id { ID id }

  (* 数字常量 *)
  | ['0'-'9']+ as n { NUMBER (int_of_string n) }

  (* 空白：跳过 *)
  | [' ' '\t' '\n' '\r']+  { token lexbuf }  (* 递归调用继续分词 *)

  (* 块注释：/* ... */ *)
  | "/*"        { block_comment lexbuf }

  (* 行注释：// ... *)
  | "//"        { line_comment lexbuf }

  (* 文件结束 *)
  | eof         { EOF }

  (* 未知字符：抛词法错误 *)
  | _ as c      { raise (LexicalError (Printf.sprintf "Unexpected character: %c" c)) }

  (* 块注释处理规则 *)
and block_comment = parse
  | "*/"        { token lexbuf }  (* 块注释结束，继续解析 *)
  | newline     { block_comment lexbuf }  (* 换行继续解析注释 *)
  | _           { block_comment lexbuf }  (* 其他字符，跳过 *)
  | eof         { raise (LexicalError "Unterminated block comment") } (* 未结束的块注释 *)

(* 行注释处理规则 *)
and line_comment = parse
  | newline     { token lexbuf }  (* 行注释到换行结束 *)
  | eof         { EOF }           (* 行注释到文件末尾 *)
  | _           { line_comment lexbuf }  (* 其他字符，跳过 *)