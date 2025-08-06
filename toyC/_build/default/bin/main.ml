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
  | BinaryOp of string * reg * reg * reg (* 二元运算：操作符, 目标寄存器, 源寄存器1, 源寄存器2 *)
  | BinaryOpImm of string * reg * reg * int (* 带立即数的二元运算：操作符, 目标寄存器, 源寄存器, 立即数 *)
  | Branch of string * reg * reg * string (* 条件分支 *)
  | Jmp of string                  (* 无条件跳转 *)
  | Label of string                (* 标签 *)
  | Call of string                 (* 函数调用 *)
  | Ret                           (* 返回 *)
  | Store of reg * reg * int       (* 存储到内存 *)
  | Load of reg * reg * int        (* 从内存加载 *)
  | ReloadVar of reg * string      (* 在函数调用后重新加载变量 *)
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
  scope_stack: (string, int) Hashtbl.t list; (* 作用域栈 *)
  free_temps: int list; (* 可重用的临时寄存器列表 *)
  current_function: string; (* 当前函数名 *)
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
  scope_stack = [];
  free_temps = [];
  current_function = "";
}

(* ==================== 辅助函数 ==================== *)
let fresh_temp state = 
  if state.temp_counter < 26 then  (* 限制在26个寄存器内 *)
    let temp = state.temp_counter in
    (Temp temp, {state with temp_counter = temp + 1})
  else
    let stack_var = state.stack_size + 1 in
    (Temp stack_var, {state with stack_size = state.stack_size + 4})

let free_temp state temp_reg = 
  match temp_reg with
  | Temp n when n < 26 -> {state with free_temps = n :: state.free_temps}
  | _ -> state

let fresh_label state prefix =
  let label = Printf.sprintf "%s_%s%d" state.current_function prefix state.label_counter in
  (label, {state with label_counter = state.label_counter + 1})

let get_var_offset_for_use state var =
  let rec lookup scopes =
    match scopes with
    | [] -> None
    | scope :: remaining_scopes ->
        (try
           Some (Hashtbl.find scope var)
         with Not_found ->
           lookup remaining_scopes)
  in
  match lookup state.scope_stack with
  | Some offset -> 
      (offset, state)
  | None ->
      failwith ("Variable " ^ var ^ " not found in local scopes")

let get_var_offset_for_declaration state var =
  match state.scope_stack with
  | current_scope :: _ ->
      let offset = -(500  + state.stack_size) in
      Hashtbl.add current_scope var offset;
      let new_state = {state with stack_size = state.stack_size + 4} in
      (offset, new_state)
  | [] ->
      let new_scope = Hashtbl.create 10 in
      let offset = -(500  + state.stack_size) in
      Hashtbl.add new_scope var offset;
      let new_state = {state with 
                       scope_stack = new_scope :: state.scope_stack;
                       stack_size = state.stack_size + 4} in
      (offset, new_state)

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
  | BlockStmt b ->  
  let rec check_block stmts =
    match stmts with
    | [] -> false
    | s::rest ->
        if check_return_coverage s 
        then true  
        else check_block rest  
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
  let scope_stack = ref [StringMap.empty] in
  let enter_scope () =
    scope_stack := StringMap.empty :: !scope_stack
  in
  let leave_scope () =
    scope_stack := List.tl !scope_stack
  in
  let add_var name typ =
    match !scope_stack with
    | current :: rest ->
        if StringMap.mem name current then
          raise (SemanticError ("variable " ^ name ^ " redeclared"));
        scope_stack := StringMap.add name typ current :: rest
    | [] -> failwith "scope stack empty"
  in
  let rec find_var name = function
    | [] -> None
    | scope :: rest ->
        match StringMap.find_opt name scope with
        | Some t -> Some t
        | None -> find_var name rest
  in
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
  let rec check_stmt stmt expected_ret_type in_loop =
    match stmt with
    | DeclStmt (t, name, e_opt) ->
        add_var name t;
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
    | EmptyStmt -> ()
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
  if not !has_main then raise (SemanticError "program must contain a main function")

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
      let offset, state' = get_var_offset_for_use state x in
      let (temp, state'') = fresh_temp state' in
      (temp, [Load (temp, RiscvReg "s0", offset)], state'')
  | Call (name, args) ->
    let indexed_args = List.mapi (fun i arg -> (i, arg)) args in
    let (processed_args, final_state) = List.fold_left (
      fun (acc_results, acc_state) (i, arg_expr) ->
        let (reg, code, new_state) = expr_to_ir acc_state arg_expr in
        let process_code = 
          if i < 8 then
            code @ [Mv (RiscvReg ("a" ^ string_of_int i), reg)]
          else
             let stack_offset = ((i - 8) * 4) in
          code @ [Store (reg, RiscvReg "sp", stack_offset)]
        in
        let free_state = free_temp new_state reg in
        (acc_results @ process_code, free_state)
    ) ([], state) indexed_args in
    let is_void_func = 
      try
        let func_info = Hashtbl.find func_table name in
        func_info.ret_type = Void
      with Not_found -> false
    in
    if is_void_func then
      let (temp, state') = fresh_temp final_state in
      (temp, processed_args @ [Call name; Li (temp, 0)], state')
    else
      let (result_reg, state') = fresh_temp final_state in
      (result_reg, processed_args @ [Call name; Mv (result_reg, RiscvReg "a0")], state')
  | Unary (op, e) ->
      let (e_reg, e_code, state') = expr_to_ir state e in
      let (temp, state'') = fresh_temp state' in
      let state''' = free_temp state'' e_reg in
      (match op with
       | Plus -> (e_reg, e_code, state')
       | Minus -> (temp, e_code @ [BinaryOp ("sub", temp, RiscvReg "zero", e_reg)], state''')
       | Not -> 
           let (ne_temp, state'''') = fresh_temp state''' in
           let state_final = free_temp state'''' ne_temp in
           (temp, e_code @ [BinaryOp ("sltu", ne_temp, RiscvReg "zero", e_reg);
                            BinaryOpImm ("xori", temp, ne_temp, 1)], state_final))
  | Binary (op, e1, e2) ->
      let (e1_reg, e1_code, state') = expr_to_ir state e1 in        
      let protected_state = 
        match e1_reg with
        | Temp n -> {state' with free_temps = List.filter (fun x -> x <> n) state'.free_temps}
        | RiscvReg _ -> state'
      in
      let (e2_reg, e2_code, state'') = expr_to_ir protected_state e2 in
      let (temp, state''') = fresh_temp state'' in
      let state_final = free_temp (free_temp state''' e1_reg) e2_reg in
    
        match op with
        | And -> 
            let (false_label, state_false) = fresh_label state''' "and_false" in
            let (merge_label, state_merge) = fresh_label state_false "and_merge" in
            let state_final = free_temp state_merge temp in
            (temp, 
            e1_code @ 
            [Branch ("beqz", e1_reg, RiscvReg "zero", false_label)] @
            e2_code @
            [Mv (temp, e2_reg);
              Jmp merge_label;
              Label false_label;
              Li (temp, 0);
              Label merge_label], 
            state_final)
        | Or -> 
            let (true_label, state_true) = fresh_label state''' "or_true" in
            let (merge_label, state_merge) = fresh_label state_true "or_merge" in
            let state_final = free_temp state_merge temp in
            (temp, 
            e1_code @ 
            [Branch ("bnez", e1_reg, RiscvReg "zero", true_label)] @
            e2_code @
            [Mv (temp, e2_reg);
              Jmp merge_label;
              Label true_label;
              Li (temp, 1);
              Label merge_label], 
            state_final)
        | Add -> 
            (temp, e1_code @ e2_code @ [BinaryOp ("add", temp, e1_reg, e2_reg)], state_final)
        | Sub -> 
          (match e2 with
          | Num n -> 
              (temp, e1_code @ [BinaryOpImm ("addi", temp, e1_reg, -n)], state_final) 
          | _ -> 
              (temp, e1_code @ e2_code @ [BinaryOp ("sub", temp, e1_reg, e2_reg)], state_final))
        | Mul -> 
            (temp, e1_code @ e2_code @ [BinaryOp ("mul", temp, e1_reg, e2_reg)], state_final)
        | Div -> 
            (temp, e1_code @ e2_code @ [BinaryOp ("div", temp, e1_reg, e2_reg)], state_final)
        | Mod -> 
            (temp, e1_code @ e2_code @ [BinaryOp ("rem", temp, e1_reg, e2_reg)], state_final)
        | Lt -> 
            (temp, e1_code @ e2_code @ [BinaryOp ("slt", temp, e1_reg, e2_reg)], state_final)
        | Gt -> 
            let code = e1_code @ e2_code @ [BinaryOp ("slt", temp, e2_reg, e1_reg)] in
            (temp, code, state_final)
        | Leq ->
        let (lt_temp, state'''') = fresh_temp state_final in
        let state_final' = free_temp state'''' lt_temp in
        let code = e1_code @ e2_code @
          [BinaryOp ("slt", lt_temp, e2_reg, e1_reg);
          BinaryOpImm ("xori", temp, lt_temp, 1)] in
        (temp, code, state_final')
        | Geq ->
            let (lt_temp, state'''') = fresh_temp state_final in
            let state_final' = free_temp state'''' lt_temp in
            let code = e1_code @ e2_code @
              [BinaryOp ("slt", lt_temp, e1_reg, e2_reg);
              BinaryOpImm ("xori", temp, lt_temp, 1)] in
            (temp, code, state_final')
        | Eq ->
            let (xor_temp, state'''') = fresh_temp state_final in
            let (sltu_temp, state''''') = fresh_temp state'''' in
            let state_final'' = free_temp (free_temp state''''' xor_temp) sltu_temp in
            let code = e1_code @ e2_code @
              [BinaryOp ("xor", xor_temp, e1_reg, e2_reg);
              BinaryOp ("sltu", sltu_temp, RiscvReg "zero", xor_temp);
              BinaryOpImm ("xori", temp, sltu_temp, 1)] in
            (temp, code, state_final'')
        | Neq ->
            let (xor_temp, state'''') = fresh_temp state_final in
            let (sltu_temp, state''''') = fresh_temp state'''' in
            let state_final'' = free_temp (free_temp state''''' xor_temp) sltu_temp in
            let code = e1_code @ e2_code @
              [BinaryOp ("xor", xor_temp, e1_reg, e2_reg);
              BinaryOp ("sltu", sltu_temp, RiscvReg "zero", xor_temp)] in
            (temp, code, state_final'')

let enter_scope state =
  let new_scope = Hashtbl.create 10 in
  {state with scope_stack = new_scope :: state.scope_stack}

let leave_scope state =
  match state.scope_stack with
  | [] -> state
  | _ :: rest -> {state with scope_stack = rest}

let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> block_to_ir state b
  | DeclStmt (_, name, Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset_for_declaration state' name in
      let state''' = free_temp state'' expr_reg in
      (expr_code @ [Store (expr_reg, RiscvReg "s0", offset)], state''')
  | DeclStmt (_, name, None) ->
      let offset, state' = get_var_offset_for_declaration state name in
      ([], state')
  | AssignStmt (name, expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset_for_use state' name in
      let state''' = free_temp state'' expr_reg in
      (expr_code @ [Store (expr_reg, RiscvReg "s0", offset)], state''')
  | IfStmt (cond, then_stmt, else_stmt_opt) ->
      let (cond_reg, cond_code, state') = expr_to_ir state cond in
      let (then_label, state'') = fresh_label state' "then" in
      let (else_label, state''') = fresh_label state'' "else" in
      let (merge_label, state'''') = fresh_label state''' "merge" in
      let (then_code, state''''') = stmt_to_ir state'''' then_stmt in
      let (else_code, state'''''') = 
        match else_stmt_opt with
        | Some s -> stmt_to_ir state''''' s
        | None -> ([], state''''') in
      let state_final = free_temp state'''''' cond_reg in
      (cond_code @ 
       [Branch ("bnez", cond_reg, RiscvReg "zero", then_label);
        Jmp else_label;
        Label then_label] @
       then_code @
       [Jmp merge_label;
        Label else_label] @
       else_code @
       [Label merge_label], state_final)
  | ReturnStmt (Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let state'' = free_temp state' expr_reg in
      (expr_code @ [Mv (RiscvReg "a0", expr_reg); Ret], state'')
  | ReturnStmt None ->
      ([Ret], state)
  | ExprStmt expr ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let state'' = free_temp state' expr_reg in
      (expr_code, state'')
  | WhileStmt (cond, body) ->
      let (loop_label, state') = fresh_label state "loop" in
      let (end_label, state'') = fresh_label state' "end" in
      let state_with_loop = { state'' with loop_labels = (end_label, loop_label) :: state''.loop_labels } in
      let (cond_reg, cond_code, state''') = expr_to_ir state_with_loop cond in
      let (body_code, state'''') = stmt_to_ir state''' body in
      let state_final = free_temp state'''' cond_reg in
      ( [Label loop_label] @
        cond_code @
        [Branch ("beqz", cond_reg, RiscvReg "zero", end_label)] @
        body_code @
        [Jmp loop_label;
         Label end_label],
        { state_final with loop_labels = List.tl state_final.loop_labels } )
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
  let state_with_scope = enter_scope state in
  let (code, final_state) = List.fold_left (fun (code_acc, st) stmt ->
    let (code, st') = stmt_to_ir st stmt in
    (code_acc @ code, st')
  ) ([], state_with_scope) block.stmts in
  let exited_state = leave_scope final_state in
  (code, exited_state)

let func_to_ir (func : Ast.func_def) : (ir_func * (string, int) Hashtbl.t) =
  let state = { 
    initial_state with 
    var_offset = Hashtbl.create (List.length func.params);
    stack_size = 0;
    label_counter = 0;
    current_function = func.name;
  } in
  let param_scope = Hashtbl.create (List.length func.params) in
  let state_with_scope = { state with scope_stack = [param_scope] } in
  let state' = 
    List.fold_left (fun st (i, (param : Ast.param)) ->
      let offset = -(68 + i * 4) in
      Hashtbl.add param_scope param.name offset;
      Hashtbl.add st.var_offset param.name offset;
      st
    ) state_with_scope (List.mapi (fun i x -> (i, x)) func.params)
  in
  let (body_code, final_state) = block_to_ir state' func.body in
  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = body_code;
  }, final_state.var_offset

(* ==================== IR到RISC-V汇编转换（无伪指令） ==================== *)
module IRToRiscV = struct
  let reg_names = [|
    "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";
    "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"
  |]
  
  let reg_map reg =
    match reg with
    | RiscvReg s -> s
    | Temp n when n < Array.length reg_names -> reg_names.(n)
    | Temp n -> 
        let stack_offset = -(68 + (n - Array.length reg_names) * 4) in
        Printf.sprintf "%d(s0)" stack_offset

  let instr_to_asm var_offsets frame_size instrs =
    let rec convert_instrs acc_index acc_code instr_list =
      match instr_list with
      | [] -> List.rev acc_code
      | instr :: rest ->
          let handle_reg r =
            match r with
            | Temp n when n >= Array.length reg_names -> 
                let offset = -(68 + (n - Array.length reg_names) * 4) in
                let temp_reg = "t0" in
                ([Printf.sprintf "  lw %s, %d(s0)" temp_reg offset], temp_reg)
            | _ -> ([], reg_map r)
          in
          
          let handle_store_reg r value_reg =
            match r with
            | Temp n when n >= Array.length reg_names -> 
                let offset = -(68 + (n - Array.length reg_names) * 4) in
                [Printf.sprintf "  sw %s, %d(s0)" value_reg offset]
            | _ -> []
          in
          
          let (pre_code, post_code, asm_code) = 
            match instr with
            | Li (r, n) -> 
                let (pre, rd) = handle_reg r in
                if n >= -2048 && n <= 2047 then
                  (pre, [], Printf.sprintf "  addi %s, x0, %d" rd n)
                else
                  let signed_lower = n land 0xFFF in
                  let upper_20 = (n asr 12) land 0xFFFFF in
                  let signed_lower = if signed_lower >= 2048 then signed_lower - 4096 else signed_lower in
                  let adjusted_upper = if signed_lower < 0 then upper_20 + 1 else upper_20 in
                  (pre, [], Printf.sprintf "  lui %s, %d\n  addi %s, %s, %d" 
                     rd adjusted_upper rd rd signed_lower)
                     
            | Mv (rd, rs) ->
                let (pre_rs, rs_reg) = handle_reg rs in
                let (pre_rd, rd_reg) = handle_reg rd in
                let post = handle_store_reg rd rs_reg in
                (pre_rs @ pre_rd, post, Printf.sprintf "  add %s, %s, x0" rd_reg rs_reg)
                
            | BinaryOp (op, rd, rs1, rs2) ->
                let (pre1, rs1_reg) = handle_reg rs1 in
                let (pre2, rs2_reg) = handle_reg rs2 in
                let (pre3, rd_reg) = handle_reg rd in
                let post = handle_store_reg rd rd_reg in
                (pre1 @ pre2 @ pre3, post, Printf.sprintf "  %s %s, %s, %s" op rd_reg rs1_reg rs2_reg)
                
            | BinaryOpImm (op, rd, rs, imm) ->
                let (pre_rs, rs_reg) = handle_reg rs in
                let (pre_rd, rd_reg) = handle_reg rd in
                let post = handle_store_reg rd rd_reg in
                (match op with
                 | "addi" | "slti" | "xori" ->  (* 这些指令需要立即数 *)
                     if imm >= -2048 && imm <= 2047 then
                       (pre_rs @ pre_rd, post, Printf.sprintf "  %s %s, %s, %d" op rd_reg rs_reg imm)
                     else
                       let temp_reg = "t0" in
                       let signed_lower = imm land 0xFFF in
                       let upper_20 = (imm asr 12) land 0xFFFFF in
                       let signed_lower = if signed_lower >= 2048 then signed_lower - 4096 else signed_lower in
                       let adjusted_upper = if signed_lower < 0 then upper_20 + 1 else upper_20 in
                       let load_imm = 
                         Printf.sprintf "  lui %s, %d\n  addi %s, %s, %d" 
                           temp_reg adjusted_upper temp_reg temp_reg signed_lower
                       in
                       (pre_rs @ pre_rd @ [load_imm], post, 
                        Printf.sprintf "  %s %s, %s, %s" op rd_reg rs_reg temp_reg)
                 | _ -> 
                     (pre_rs @ pre_rd, post, Printf.sprintf "  %s %s, %s, %d" op rd_reg rs_reg imm))
                     
            | Branch (cond, rs1, rs2, label) ->
                let (pre1, rs1_reg) = handle_reg rs1 in
                let (pre2, rs2_reg) = handle_reg rs2 in
                (match cond with
                 | "beqz" -> (pre1 @ pre2, [], Printf.sprintf "  beq %s, x0, %s" rs1_reg label)
                 | "bnez" -> (pre1 @ pre2, [], Printf.sprintf "  bne %s, x0, %s" rs1_reg label)
                 | _ -> (pre1 @ pre2, [], Printf.sprintf "  %s %s, %s, %s" cond rs1_reg rs2_reg label))
                 
            | Jmp label -> 
                ([], [], Printf.sprintf "  j %s" label)
                
            | Label label -> 
                ([], [], Printf.sprintf "%s:" label)
                
            | Call func -> 
                ([], [], Printf.sprintf "  jal ra, %s" func)
                
            | Ret -> 
                ([], [], "  jalr x0, ra, 0")
                
            | Store (rs, base, offset) ->
                let (pre_rs, rs_reg) = handle_reg rs in
                let (pre_base, base_reg) = handle_reg base in
                (pre_rs @ pre_base, [], Printf.sprintf "  sw %s, %d(%s)" rs_reg offset base_reg)
                
            | Load (rd, base, offset) ->
                let (pre_base, base_reg) = handle_reg base in
                let (pre_rd, rd_reg) = handle_reg rd in
                let post = handle_store_reg rd rd_reg in
                (pre_base @ pre_rd, post, Printf.sprintf "  lw %s, %d(%s)" rd_reg offset base_reg)
                
            | ReloadVar (rd, var_name) ->
                try
                  let offset = Hashtbl.find var_offsets var_name in
                  let (pre_rd, rd_reg) = handle_reg rd in
                  let post = handle_store_reg rd rd_reg in
                  (pre_rd, post, Printf.sprintf "  lw %s, %d(s0)" rd_reg offset)
                with Not_found ->
                  failwith ("Variable " ^ var_name ^ " not found during code generation")
          in
          
          let full_code = 
            (List.map (fun s -> s ^ "\n") pre_code) @ 
            [asm_code] @ 
            (List.map (fun s -> s ^ "\n") post_code)
          in
          convert_instrs (acc_index + 1) (full_code @ acc_code) rest
    in
    convert_instrs 0 [] instrs

  let calculate_frame_size (ir_func : ir_func) =
    let base_size = 16 in
    let rec analyze_instrs = function
      | [] -> 0
      | instr :: rest ->
          let extra = 
            match instr with
            | Store (_, RiscvReg "sp", offset) when offset > 0 -> offset + 4
            | Load (Temp n, _, _) | Li (Temp n, _) | Mv (Temp n, _) 
            | BinaryOp (_, Temp n, _, _) | BinaryOpImm (_, Temp n, _, _) ->
                if n >= Array.length reg_names then (n - Array.length reg_names + 1) * 4 else 0
            | _ -> 0
          in
          max extra (analyze_instrs rest)
    in
    let call_stack = analyze_instrs ir_func.body in
    let aligned = ((base_size + call_stack + 15) / 16) * 16 in
    max aligned 32

  let save_callee_saved frame_size =
    let s_regs = ["s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"] in
    List.mapi (fun i reg ->
      Printf.sprintf "  sw %s, %d(sp)\n" reg (frame_size - 12 - i * 4)
    ) s_regs
    |> String.concat ""

  let restore_callee_saved frame_size =
    let s_regs = ["s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"] in
    List.mapi (fun i reg ->
      Printf.sprintf "  lw %s, %d(sp)\n" reg (frame_size - 12 - i * 4)
    ) s_regs
    |> String.concat ""

  let function_prologue name frame_size =
    let ra_offset = frame_size - 4 in
    let s0_offset = frame_size - 8 in
    let save_code = save_callee_saved frame_size in
    Printf.sprintf "%s:\n" name ^
    Printf.sprintf "  addi sp, sp, -%d\n" frame_size ^
    Printf.sprintf "  sw ra, %d(sp)\n" ra_offset ^
    Printf.sprintf "  sw s0, %d(sp)\n" s0_offset ^
    save_code ^
    Printf.sprintf "  addi s0, sp, %d\n" frame_size

  let function_epilogue frame_size =
    let ra_offset = frame_size - 4 in 
    let s0_offset = frame_size - 8 in 
    let restore_code = restore_callee_saved frame_size in
    restore_code ^
    Printf.sprintf "  lw ra, %d(sp)\n" ra_offset ^
    Printf.sprintf "  lw s0, %d(sp)\n" s0_offset ^
    Printf.sprintf "  addi sp, sp, %d\n" frame_size ^
    "  jalr x0, ra, 0\n"

  let func_to_asm var_offsets (ir_func : ir_func) =
    let frame_size = calculate_frame_size ir_func in
    let buf = Buffer.create 256 in
    Buffer.add_string buf (function_prologue ir_func.name frame_size);
    
    List.iteri (fun i param ->
      let offset = -(68 + i * 4) in
      if i < 8 then
        Buffer.add_string buf (Printf.sprintf "  sw a%d, %d(s0)\n" i offset)
      else
        let param_stack_offset = (i - 8) * 4 in
        Buffer.add_string buf (Printf.sprintf "  lw t0, %d(s0)\n  sw t0, %d(s0)\n" param_stack_offset offset)
    ) ir_func.params;
    
    let asm_code = instr_to_asm var_offsets frame_size ir_func.body in
    List.iter (fun line -> Buffer.add_string buf line) asm_code;
    
    let has_explicit_ret = List.exists (function Ret -> true | _ -> false) ir_func.body in
    if not has_explicit_ret then
      Buffer.add_string buf (function_epilogue frame_size);
    
    Buffer.contents buf
end

(* ==================== 主程序：生成标准RISC-V汇编 ==================== *)
let () =
  let ast = parse_channel stdin in
  semantic_analysis ast;
  
  let ir_with_offsets = List.map func_to_ir ast in
  let (ir_funcs, var_offsets_list) = List.split ir_with_offsets in
  
  let combined_var_offsets = Hashtbl.create 50 in
  List.iter (fun vo -> Hashtbl.iter (fun k v -> Hashtbl.add combined_var_offsets k v) vo) var_offsets_list;
  
  Printf.printf ".global main\n";
  List.iter (fun func -> Printf.printf "%s\n" (IRToRiscV.func_to_asm combined_var_offsets func)) ir_funcs;
  
  prerr_endline "Compilation successful! Output is standard RISC-V 32-bit assembly (no pseudoinstructions).";