exception LexicalError of string [@@warning "-38"]
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

module StringMap = Map.Make(String)

(* ==================== IR 定义 ==================== *)
type reg = 
  | RiscvReg of string  (* RISC-V寄存器如x1-x31 *)
  | Temp of int         (* 临时变量 *)

type ir_instr =
  | Li of reg * int                (* 加载立即数 *)
  | Mv of reg * reg                (* 寄存器间移动 *)
  | BinaryOp of string * reg * reg * reg (* 二元运算 *)
  | Branch of string * reg * reg * string (* 条件分支 *)
  | Jmp of string                  (* 无条件跳转 *)
  | Label of string                (* 标签 *)
  | Call of string                 (* 函数调用 *)
  | Ret                           (* 返回 *)
  | Store of reg * reg * int       (* 存储到内存 *)
  | Load of reg * reg * int        (* 从内存加载 *)

type ir_func = {
  name: string;
  params: string list;
  body: ir_instr list;
}

(* ==================== 代码生成状态 ==================== *)
type codegen_state = {
  temp_counter: int;
  label_counter: int;
  var_offset: (string, int) Hashtbl.t; (* 变量在栈帧中的偏移量 *)
  stack_size: int; (* 当前栈帧大小 *)
  loop_labels: (string * string) list;  (* (end_label, loop_label) 的栈 *)
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
}

(* ==================== 辅助函数 ==================== *)
let fresh_temp state = 
  let temp = state.temp_counter in
  (Temp temp, {state with temp_counter = temp + 1})

let fresh_label state prefix =
  let label = Printf.sprintf "%s%d" prefix state.label_counter in
  (label, {state with label_counter = state.label_counter + 1})

let get_var_offset state var =
  try 
    (Hashtbl.find state.var_offset var, state)  (* 找到时返回偏移量和原状态 *)
  with Not_found -> 
    let offset = state.stack_size in
    Hashtbl.add state.var_offset var offset;
    let new_state = {state with stack_size = offset + 8} in
    (offset, new_state)  (* 未找到时返回新偏移量和更新后的状态 *)

(* 将表达式转换为字符串 *)
let rec string_of_expr = function
  | Num n -> string_of_int n
  | Var s -> s
  | Call (name, args) -> name ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Unary (op, e) -> (match op with Plus -> "+" | Minus -> "-" | Not -> "!") ^ string_of_expr e
  | Binary (op, e1, e2) -> (match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%" | Lt -> "<" | Gt -> ">" | Leq -> "<=" | Geq -> ">=" | Eq -> "==" | Neq -> "!=" | And -> "&&" | Or -> "||") ^ "(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"

(* 将语句转换为字符串 *)
let rec string_of_stmt = function
  | BlockStmt b -> "Block(" ^ String.concat "; " (List.map string_of_stmt b.stmts) ^ ")"
  | EmptyStmt -> ";"
  | ExprStmt e -> string_of_expr e ^ ";"
  | DeclStmt (t, name, Some e) -> (match t with Int -> "int" | Void -> "void") ^ " " ^ name ^ " = " ^ string_of_expr e ^ ";"
  | DeclStmt (t, name, None) -> (match t with Int -> "int" | Void -> "void") ^ " " ^ name ^ ";"
  | AssignStmt (name, e) -> name ^ " = " ^ string_of_expr e ^ ";"
  | IfStmt (cond, then_stmt, Some else_stmt) -> "if (" ^ string_of_expr cond ^ ") " ^ string_of_stmt then_stmt ^ " else " ^ string_of_stmt else_stmt
  | IfStmt (cond, then_stmt, None) -> "if (" ^ string_of_expr cond ^ ") " ^ string_of_stmt then_stmt
  | WhileStmt (cond, s) -> "while (" ^ string_of_expr cond ^ ") " ^ string_of_stmt s
  | BreakStmt -> "break;"
  | ContinueStmt -> "continue;"
  | ReturnStmt (Some e) -> "return " ^ string_of_expr e ^ ";"
  | ReturnStmt None -> "return;"

(* 将函数定义转换为字符串 *)
let string_of_func_def fd =
  (match fd.ret_type with Int -> "int" | Void -> "void") ^ " " ^ fd.name ^ "(" ^ String.concat ", " (List.map (fun p -> (match p.typ with Int -> "int" | Void -> "void") ^ " " ^ p.name) fd.params) ^ ")" ^ " {\n" ^ string_of_stmt (BlockStmt fd.body) ^ "\n}"

(* 将 AST 转换为字符串 *)
let string_of_ast ast =
  String.concat "\n" (List.map string_of_func_def ast)

(* 辅助函数：检查函数是否在全局作用域 *)
let is_global_scope = function
  | BlockStmt _ -> false
  | _ -> true

(* 辅助函数：检查 return 语句覆盖所有路径 *)
let rec check_return_coverage stmt =
  match stmt with
  | BlockStmt b ->  (* 检查块中所有语句，直到找到返回或确定没有返回 *)
  let rec check_block stmts =
    match stmts with
    | [] -> false
    | s::rest ->
        if check_return_coverage s 
        then true  (* 当前语句返回，整个块返回 *)
        else check_block rest  (* 继续检查后续语句 *)
  in
  check_block b.stmts
  | IfStmt (cond, then_stmt, Some else_stmt) ->
      check_return_coverage then_stmt && check_return_coverage else_stmt
  | IfStmt (cond, then_stmt, None) -> false
  | WhileStmt (cond, s) -> false
  | ReturnStmt _ -> true
  | _ -> false

  type func_signature = { ret_type: typ; params: param list } 
  let func_table = Hashtbl.create 30
  
  let collect_functions ast =
    List.iter (fun (fd : Ast.func_def) ->
      Hashtbl.add func_table fd.name { ret_type = fd.ret_type; params = fd.params }
    ) ast
  (*检查函数调用*)
  let rec check_expr_calls (expr : Ast.expr) =
    match expr with
    | Call (name, args) ->
        if not (Hashtbl.mem func_table name) then
          raise (SemanticError ("function " ^ name ^ " called but not defined"));
        List.iter check_expr_calls args
    | Unary (_, e) -> check_expr_calls e
    | Binary (_, e1, e2) -> check_expr_calls e1; check_expr_calls e2
    | _ -> ()
(* 语义分析主函数 *)
let semantic_analysis ast =
  collect_functions ast;
  let has_main = ref false in
  (* Symbol table stack, initialized with global scope *)
  let scope_stack = ref [StringMap.empty] in
  (* Enter a new scope *)
  let enter_scope () =
    scope_stack := StringMap.empty :: !scope_stack
  in
  (* Exit the current scope *)
  let leave_scope () =
    scope_stack := List.tl !scope_stack
  in
  (* Add a variable to the current scope *)
  let add_var name typ =
    match !scope_stack with
    | current :: rest ->
        if StringMap.mem name current then
          raise (SemanticError ("variable " ^ name ^ " redeclared"));
        scope_stack := StringMap.add name typ current :: rest
    | [] -> failwith "scope stack empty"
  in
  (* Look up variable type *)
  let rec find_var name = function
    | [] -> None
    | scope :: rest ->
        match StringMap.find_opt name scope with
        | Some t -> Some t
        | None -> find_var name rest
  in
  (* Infer expression type *)
  let rec infer_expr_type expr =
    match expr with
    | Num _ -> Int
    | Var v ->
        (match find_var v !scope_stack with
         | Some t -> t
         | None -> raise (SemanticError ("variable " ^ v ^ " used before declaration")))
    | Call (name, args) ->
        let { ret_type; params } = Hashtbl.find func_table name in
        if List.length args <> List.length params then
          raise (SemanticError ("function " ^ name ^ " called with wrong number of arguments"));
        List.iter2 (fun arg param ->
          let arg_type = infer_expr_type arg in
          if arg_type <> param.typ then
            raise (SemanticError ("type mismatch in argument of function " ^ name))
        ) args params;
        ret_type
    | Unary (op, e) ->
        (match op with
         | Plus | Minus -> infer_expr_type e
         | Not -> Int)
    | Binary (op, e1, e2) ->
        let t1 = infer_expr_type e1 in
        let t2 = infer_expr_type e2 in
        if t1 <> Int || t2 <> Int then
          raise (SemanticError "binary operation only supports int types");
        Int
  in
  (* Check statement types, variable declarations, uses, and function calls *)
  let rec check_stmt stmt expected_ret_type in_loop =
    match stmt with
    | DeclStmt (t, name, e_opt) ->
        add_var name t; (* Add variable to scope before checking expression *)
        (match e_opt with
         | Some e ->
             let expr_type = infer_expr_type e in
             if expr_type <> t then
               raise (SemanticError ("type mismatch in declaration of " ^ name))
         | None -> ())
    | AssignStmt (name, e) ->
        (match find_var name !scope_stack with
         | None -> raise (SemanticError ("variable " ^ name ^ " used before declaration"))
         | Some t ->
             let expr_type = infer_expr_type e in
             if expr_type <> t then
               raise (SemanticError ("type mismatch in assignment to " ^ name)))
    | ExprStmt e -> ignore (infer_expr_type e); check_expr_calls e
    | ReturnStmt (Some e) ->
        let expr_type = infer_expr_type e in
        if expr_type <> expected_ret_type then
          raise (SemanticError "return type mismatch")
    | ReturnStmt None ->
        if expected_ret_type <> Void then
          raise (SemanticError "missing return value in non-void function")
    | BlockStmt b ->
        enter_scope ();
        List.iter (fun s -> check_stmt s expected_ret_type in_loop) b.stmts;
        leave_scope ()
    | IfStmt (cond, then_stmt, else_stmt_opt) ->
        ignore (infer_expr_type cond);
        check_stmt then_stmt expected_ret_type in_loop;
        Option.iter (fun s -> check_stmt s expected_ret_type in_loop) else_stmt_opt
    | WhileStmt (cond, s) ->
        ignore (infer_expr_type cond);
        check_stmt s expected_ret_type true
    | BreakStmt | ContinueStmt ->
        if not in_loop then raise (SemanticError "break/continue must be inside a loop")
  and check_expr_calls expr =
    match expr with
    | Call (name, args) ->
        if not (Hashtbl.mem func_table name) then
          raise (SemanticError ("function " ^ name ^ " called but not defined"));
        List.iter check_expr_calls args
    | Unary (_, e) -> check_expr_calls e
    | Binary (_, e1, e2) -> check_expr_calls e1; check_expr_calls e2
    | _ -> ()
  in
  List.iter (fun (fd : ToyC_riscv_lib.Ast.func_def) ->
    if fd.name = "main" then (
      has_main := true;
      if fd.params <> [] then raise (SemanticError "main function must have an empty parameter list");
      if fd.ret_type <> Int then raise (SemanticError "main function must return int");
      if not (check_return_coverage (BlockStmt fd.body)) then
        raise (SemanticError "main function must return a value on all paths")
    ) else if fd.ret_type = Int && not (check_return_coverage (BlockStmt fd.body)) then
      raise (SemanticError (fd.name ^ " function with int return type must return a value on all paths"));
    let param_names = List.map (fun (p : ToyC_riscv_lib.Ast.param) -> p.name) fd.params in
    let initial_scope = List.fold_left (fun acc name -> StringMap.add name Int acc) StringMap.empty param_names in
    scope_stack := initial_scope :: !scope_stack;
    check_stmt (BlockStmt fd.body) fd.ret_type false;
    scope_stack := List.tl !scope_stack
  ) ast;
  if not !has_main then raise (SemanticError "program must contain a main function");
  print_endline "Semantic analysis passed!"

let parse_channel ch =
  let lex = Lexing.from_channel ch in
  try
    Parser.comp_unit Lexer.token lex
  with
  | LexicalError msg ->
      Printf.eprintf "Lexical error: %s\n" msg;
      exit 1
  | Parser.Error ->
      let pos = lex.Lexing.lex_curr_p in
      Printf.eprintf "Syntax error at line %d, column %d\n"
        pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1);
      exit 1

(* ==================== AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  match expr with
  | Num n -> 
      let (temp, state') = fresh_temp state in
      (temp, [Li (temp, n)], state')
  | Var x -> 
      let offset, state' = get_var_offset state x in
      let (temp, state'') = fresh_temp state' in
      (temp, [Load (temp, RiscvReg "sp", offset)], state'')
  | Binary (op, e1, e2) ->
      let (e1_reg, e1_code, state') = expr_to_ir state e1 in
      let (e2_reg, e2_code, state'') = expr_to_ir state' e2 in
      let (temp, state''') = fresh_temp state'' in
      let op_str = match op with
        | Add -> "add" | Sub -> "sub" | Mul -> "mul" 
        | Div -> "div" | Mod -> "rem" | Lt -> "slt"
        | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
        | Eq -> "seq" | Neq -> "sne" | And -> "and"
        | Or -> "or" in
      (temp, e1_code @ e2_code @ [BinaryOp (op_str, temp, e1_reg, e2_reg)], state''')
  | _ -> failwith "Unsupported expression"

let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> block_to_ir state b
  | DeclStmt (_, name, Some expr) -> (* 带初始化的声明 *)
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset state' name in
      (expr_code @ [Store (expr_reg, RiscvReg "sp", offset)], state'')
  | DeclStmt (_, name, None) -> (* 不带初始化的声明 *)
      let offset, state' = get_var_offset state name in
      ([], state')
  | AssignStmt (name, expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset state' name in
      (expr_code @ [Store (expr_reg, RiscvReg "sp", offset)], state'')
  | IfStmt (cond, then_stmt, else_stmt) ->
      let (cond_reg, cond_code, state') = expr_to_ir state cond in
      let (then_label, state'') = fresh_label state' "then" in
      let (else_label, state''') = fresh_label state'' "else" in
      let (merge_label, state'''') = fresh_label state''' "merge" in
      let (then_code, state''''') = stmt_to_ir state'''' then_stmt in
      let (else_code, state'''''') = 
        match else_stmt with
        | Some s -> stmt_to_ir state''''' s
        | None -> ([], state''''') in
      (cond_code @ 
       [Branch ("bnez", cond_reg, RiscvReg "zero", then_label);
        Jmp else_label;
        Label then_label] @
       then_code @
       [Jmp merge_label;
        Label else_label] @
       else_code @
       [Label merge_label], state'''''')
  | ReturnStmt (Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      (expr_code @ [Mv (RiscvReg "a0", expr_reg); Ret], state')
  | ReturnStmt None ->
      ([Ret], state)
  | ExprStmt expr ->
      let (_, expr_code, state') = expr_to_ir state expr in
      (expr_code, state')
  | WhileStmt (cond, body) ->
      let (loop_label, state') = fresh_label state "loop" in
      let (end_label, state'') = fresh_label state' "end" in
      
      let state_with_loop = { state'' with loop_labels = (end_label, loop_label) :: state''.loop_labels } in
      
      let (cond_reg, cond_code, state''') = expr_to_ir state_with_loop cond in
      let (body_code, state'''') = stmt_to_ir state''' body in
      
      ( [Label loop_label] @
        cond_code @
        [Branch ("beqz", cond_reg, RiscvReg "zero", end_label)] @
        body_code @
        [Jmp loop_label;
         Label end_label],
        { state'''' with loop_labels = List.tl state''''.loop_labels } )
  
  | BreakStmt ->
      (match state.loop_labels with
       | (end_label, _) :: _ -> ([Jmp end_label], state)
       | [] -> failwith "break statement outside loop")
  | ContinueStmt ->
      (match state.loop_labels with
       | (_, loop_label) :: _ -> ([Jmp loop_label], state)
       | [] -> failwith "continue statement outside loop")
  | EmptyStmt ->
      ([], state)

and block_to_ir state block =
  List.fold_left (fun (code_acc, st) stmt ->
    let (code, st') = stmt_to_ir st stmt in
    (code_acc @ code, st')
  ) ([], state) block.stmts

let func_to_ir (func : Ast.func_def) : ir_func =
  let state = { 
    initial_state with 
    var_offset = Hashtbl.create (List.length func.params);
  } in
    let state' = 
    List.fold_left (fun st (param : Ast.param) ->
      let offset, st' = get_var_offset st param.name in
      st'
    ) state func.params
  in
  let (body_code, final_state) = block_to_ir state' func.body in
  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = body_code;
  }


let () =
  let ch = open_in "test/04_while_break.tc" in
  let ast = parse_channel ch in
  close_in ch;
  semantic_analysis ast;
  let ast_str = string_of_ast ast in
  let out_ch = open_out "ast.txt" in
  Printf.fprintf out_ch "%s\n" ast_str;
  close_out out_ch;
   let ir = List.map func_to_ir ast in  (* 转换整个AST为IR *)
  
  let string_of_ir ir_func =
    let buf = Buffer.create 256 in
    Buffer.add_string buf (Printf.sprintf "Function: %s\n" ir_func.name);
    Buffer.add_string buf "Params: ";
    List.iter (fun p -> Buffer.add_string buf (p ^ " ")) ir_func.params;
    Buffer.add_string buf "\nBody:\n";
    List.iter (fun instr ->
      let instr_str = match instr with
        | Li (r, n) -> Printf.sprintf "  li %s, %d" 
                        (match r with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n) 
                        n
        | Mv (rd, rs) -> Printf.sprintf "  mv %s, %s" 
                          (match rd with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
                          (match rs with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
        | BinaryOp (op, rd, rs1, rs2) ->
            Printf.sprintf "  %s %s, %s, %s" op
              (match rd with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              (match rs1 with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              (match rs2 with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
        | Branch (cond, rs1, rs2, label) ->
            Printf.sprintf "  %s %s, %s, %s" cond
              (match rs1 with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              (match rs2 with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              label
        | Jmp label ->
            Printf.sprintf "  j %s" label
        | Label label ->
            label ^ ":"
        | Call func ->
            Printf.sprintf "  call %s" func
        | Ret ->
            "  ret"
        | Store (rs, base, offset) ->
            Printf.sprintf "  sd %s, %d(%s)"
              (match rs with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              offset
              (match base with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
        | Load (rd, base, offset) ->
            Printf.sprintf "  ld %s, %d(%s)"
              (match rd with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
              offset
              (match base with RiscvReg s -> s | Temp n -> "t" ^ string_of_int n)
      in
      Buffer.add_string buf (instr_str ^ "\n")
    ) ir_func.body;
    Buffer.contents buf
  in
  
  (* 6. 输出IR到文件 *)
  let ir_out = open_out "risc-V.txt" in
  List.iter (fun f -> 
    Printf.fprintf ir_out "%s\n" (string_of_ir f)
  ) ir;
  close_out ir_out;
  

  print_endline "Compilation successful!";
  print_endline ("AST written to ast.txt");
  print_endline ("RISC-V written to risc-V.txt")