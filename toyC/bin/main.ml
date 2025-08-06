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
  | BinaryOpImm of string * reg * reg * int (* 带立即数的二元运算 *)
  | Branch of string * reg * reg * string (* 条件分支 *)
  | Jmp of string                  (* 无条件跳转 *)
  | Label of string                (* 标签 *)
  | Call of string * int           (* 函数调用，附带参数数量 *)
  | Ret                           (* 返回 *)
  | Store of reg * reg * int       (* 存储到内存 *)
  | Load of reg * reg * int        (* 从内存加载 *)
  | ReloadVar of reg * string      (* 在函数调用后重新加载变量 *)
  | Addi of reg * reg * int        (* 寄存器加立即数，用于调整栈指针 *)

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
  match state.free_temps with
  | temp :: rest -> 
      (Temp temp, {state with free_temps = rest})
  | [] -> 
      let temp = state.temp_counter in
      (Temp temp, {state with temp_counter = temp + 1})

let free_temp state temp_reg = 
  match temp_reg with
  | Temp n -> {state with free_temps = n :: state.free_temps}
  | RiscvReg _ -> state

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

(* 修复：使用动态计算的偏移量，避免与参数冲突 *)
let get_var_offset_for_declaration state var =
  match state.scope_stack with
  | current_scope :: _ ->
      (* 从-16开始（避开ra和s0的保存位置），而不是固定的-500 *)
      let offset = -(16 + state.stack_size) in
      Hashtbl.add current_scope var offset;
      let new_state = {state with stack_size = state.stack_size + 4} in
      (offset, new_state)
  | [] ->
      let new_scope = Hashtbl.create 10 in
      let offset = -(16 + state.stack_size) in
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
      let num_args = List.length args in
      let indexed_args = List.mapi (fun i arg -> (i, arg)) args in
      
      (* 计算需要在栈上传递的参数数量 *)
      let num_stack_args = max 0 (num_args - 8) in
      let stack_arg_size = num_stack_args * 4 in
      
      (* 为栈上参数分配空间 *)
      let stack_alloc_code = 
        if stack_arg_size > 0 then
          [Addi (RiscvReg "sp", RiscvReg "sp", -stack_arg_size)]
        else
          []
      in
      
      (* 处理参数 *)
      let (processed_args, final_state) = List.fold_left (
        fun (acc_results, acc_state) (i, arg_expr) ->
          let (reg, code, new_state) = expr_to_ir acc_state arg_expr in
          let process_code = 
            if i < 8 then
              code @ [Mv (RiscvReg ("a" ^ string_of_int i), reg)]
            else
              let stack_offset = ((i - 8) * 4) + stack_arg_size in
              code @ [Store (reg, RiscvReg "sp", stack_offset)]
          in
          let free_state = free_temp new_state reg in
          (acc_results @ process_code, free_state)
      ) ([], state) indexed_args in
      
      (* 调用函数 *)
      let is_void_func = 
        try
          let func_info = Hashtbl.find func_table name in
          func_info.ret_type = Void
        with Not_found -> false
      in
      
      (* 恢复栈指针的代码 *)
      let stack_restore_code = 
        if stack_arg_size > 0 then
          [Addi (RiscvReg "sp", RiscvReg "sp", stack_arg_size)]
        else
          []
      in
      
      if is_void_func then
        let (temp, state') = fresh_temp final_state in
        (temp, stack_alloc_code @ processed_args @ [Call (name, num_args)] @ stack_restore_code @ [Li (temp, 0)], state')
      else
        let (result_reg, state') = fresh_temp final_state in
        (result_reg, stack_alloc_code @ processed_args @ [Call (name, num_args)] @ stack_restore_code @ [Mv (result_reg, RiscvReg "a0")], state')
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
            let e1_has_call = List.exists (function Call _ -> true | _ -> false) e1_code in
            let e2_has_call = List.exists (function Call _ -> true | _ -> false) e2_code in
            
            (match (e1, e2) with
            | (Var x1, _) when e2_has_call -> 
                (temp, e1_code @ e2_code @ [ReloadVar (e1_reg, x1); BinaryOp ("mul", temp, e1_reg, e2_reg)], state_final)
            | (_, Var x2) when e1_has_call -> 
                (temp, e1_code @ e2_code @ [ReloadVar (e2_reg, x2); BinaryOp ("mul", temp, e1_reg, e2_reg)], state_final)
            | _ -> 
                (temp, e1_code @ e2_code @ [BinaryOp ("mul", temp, e1_reg, e2_reg)], state_final))
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
        | None -> ([], state'''') in
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
      let offset = -(16 + i * 4) in  (* 从-16开始，避开ra和s0的保存位置 *)
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

(* ==================== IR到RISC-V汇编转换 ==================== *)
module LivenessAnalysis = struct
  module RegSet = Set.Make(struct
    type t = reg
    let compare = compare
  end)
  
  let regs_used = function
    | Li _ -> RegSet.empty
    | Mv (_, rs) -> RegSet.singleton rs
    | BinaryOp (_, _, rs1, rs2) -> RegSet.add rs1 (RegSet.singleton rs2)
    | BinaryOpImm (_, _, rs, _) -> RegSet.singleton rs
    | Branch (_, rs1, rs2, _) -> RegSet.add rs1 (RegSet.singleton rs2)
    | Store (rs, _, _) -> RegSet.singleton rs
    | Load (_, _, _) -> RegSet.empty
    | ReloadVar (_, _) -> RegSet.empty
    | Call _ -> 
        let params = List.init 8 (fun i -> RiscvReg ("a" ^ string_of_int i)) in
        List.fold_left (fun set reg -> RegSet.add reg set) RegSet.empty params
    | Addi (_, rs, _) -> RegSet.singleton rs
    | _ -> RegSet.empty
  
  let regs_defined = function
    | Li (rd, _) -> RegSet.singleton rd
    | Mv (rd, _) -> RegSet.singleton rd
    | BinaryOp (_, rd, _, _) -> RegSet.singleton rd
    | BinaryOpImm (_, rd, _, _) -> RegSet.singleton rd
    | Load (rd, _, _) -> RegSet.singleton rd
    | ReloadVar (rd, _) -> RegSet.singleton rd
    | Call _ -> RegSet.singleton (RiscvReg "a0")
    | Addi (rd, _, _) -> RegSet.singleton rd
    | _ -> RegSet.empty
  
  type liveness_info = {
    live_in: RegSet.t array;
    live_out: RegSet.t array;
  }[@@warning "-69"]
  
  let analyze_liveness (instrs: ir_instr list) : liveness_info =
    let n = List.length instrs in
    if n = 0 then
      { live_in = [||]; live_out = [||] }
    else
      let live_in = Array.make n RegSet.empty in
      let live_out = Array.make n RegSet.empty in
      let instr_array = Array.of_list instrs in
      
      for i = 0 to n - 1 do
        live_in.(i) <- RegSet.empty;
        live_out.(i) <- RegSet.empty;
      done;
      
      let changed = ref true in
      while !changed do
        changed := false;
        
        for i = n - 1 downto 0 do
          let used = regs_used instr_array.(i) in
          let defined = regs_defined instr_array.(i) in
          
          let new_out = 
            if i < n - 1 then
              live_in.(i + 1)
            else
              RegSet.empty
          in
          
          let new_in = RegSet.union used (RegSet.diff new_out defined) in
          
          if not (RegSet.equal live_in.(i) new_in) || 
             not (RegSet.equal live_out.(i) new_out) then
            (
              live_in.(i) <- new_in;
              live_out.(i) <- new_out;
              changed := true
            )
        done
      done;
      
      { live_in; live_out }
  
  let get_live_regs info instr_index =
    if instr_index >= 0 && instr_index < Array.length info.live_in then
      info.live_in.(instr_index)
    else
      RegSet.empty
      
  let is_live info instr_index reg =
    RegSet.mem reg (get_live_regs info instr_index)
end

module IRToRiscV = struct
  (* 修复：调整临时寄存器的栈偏移，避免与ra和s0冲突 *)
  let reg_map var_offsets frame_size = function
    | RiscvReg s -> s
    | Temp n -> 
        if n < 7 then 
          Printf.sprintf "t%d" n
        else if n < 15 then 
          Printf.sprintf "a%d" (n - 7)
        else
          (* 从-20开始，确保避开ra(-4)和s0(-8)的保存位置 *)
          let stack_offset = -(20 + (n - 15) * 4) in
          Printf.sprintf "%d(s0)" stack_offset
  
  let instr_to_asm var_offsets frame_size instrs =
    let liveness_info = LivenessAnalysis.analyze_liveness instrs in
    
    let rec convert_instrs acc_index acc_code instr_list =
      match instr_list with
      | [] -> acc_code
      | instr :: rest ->
          let code = 
            match instr with
                      | Li (r, n) -> 
                let process_imm_value n =
                 if n >= -2048 && n <= 2047 then
                    string_of_int n
                  else
                    let hi = (n asr 12) + (if n land 0x800 != 0 then 1 else 0) in
                    let lo = n - (hi lsl 12) in
                    Printf.sprintf "  lui t1, %d\n  addi t1, t1, %d" hi lo
                in
                
                let imm_str = process_imm_value n in
                
                (match r with
                | Temp temp_reg when temp_reg >= 15 -> 
                    let stack_offset = -(20 + (temp_reg - 15) * 4) in
                    if String.contains imm_str '\n' then
                      Printf.sprintf "%s\n  sw t1, %d(s0)" imm_str stack_offset
                    else if n = 0 then
                      Printf.sprintf "  sw zero, %d(s0)" stack_offset
                    else
                      Printf.sprintf "  li t0, %s\n  sw t0, %d(s0)" imm_str stack_offset
                | _ -> 
                    let target_reg = reg_map var_offsets frame_size r in
                    if String.contains imm_str '\n' then
                      Printf.sprintf "%s\n  mv %s, t1" imm_str target_reg
                    else if n = 0 then
                      Printf.sprintf "  mv %s, zero" target_reg
                    else
                      Printf.sprintf "  li %s, %s" target_reg imm_str)
          | Mv (rd, rs) ->
              (match (rd, rs) with
              | (Temp n, _) when n >= 15 -> 
                  let stack_offset = -(20 + (n - 15) * 4) in
                  Printf.sprintf "  mv t0, %s\n  sw t0, %d(s0)" (reg_map var_offsets frame_size rs) stack_offset
              | (_, Temp n) when n >= 15 -> 
                  let stack_offset = -(20 + (n - 15) * 4) in
                  Printf.sprintf "  lw t0, %d(s0)\n  mv %s, t0" stack_offset (reg_map var_offsets frame_size rd)
              | _ -> 
                  Printf.sprintf "  mv %s, %s" (reg_map var_offsets frame_size rd) (reg_map var_offsets frame_size rs))
          | BinaryOp (op, rd, rs1, rs2) ->
              (match (rd, rs1, rs2) with
              | (Temp n, _, _) when n >= 15 -> 
                  let stack_offset = -(20 + (n - 15) * 4) in
                  let src1 = reg_map var_offsets frame_size rs1 in
                  let src2 = reg_map var_offsets frame_size rs2 in
                  let (reg1, load1) = 
                    match rs1 with
                    | Temp m when m >= 15 -> 
                        let offset = -(20 + (m - 15) * 4) in
                        ("t1", Printf.sprintf "  lw t1, %d(s0)\n" offset)
                    | _ -> (src1, "")
                  in
                  let (reg2, load2) = 
                    match rs2 with
                    | Temp m when m >= 15 -> 
                        let offset = -(20 + (m - 15) * 4) in
                        ("t2", Printf.sprintf "  lw t2, %d(s0)\n" offset)
                    | _ -> (src2, "")
                  in
                  load1 ^ load2 ^ 
                  Printf.sprintf "  %s t0, %s, %s\n  sw t0, %d(s0)" op reg1 reg2 stack_offset
              | _ ->
                  let dest = reg_map var_offsets frame_size rd in
                  let (reg1, load1) = 
                    match rs1 with
                    | Temp m when m >= 15 -> 
                        let offset = -(20 + (m - 15) * 4) in
                        ("t1", Printf.sprintf "  lw t1, %d(s0)\n" offset)
                    | _ -> (reg_map var_offsets frame_size rs1, "")
                  in
                  let (reg2, load2) = 
                    match rs2 with
                    | Temp m when m >= 15 -> 
                        let offset = -(20 + (m - 15) * 4) in
                        ("t2", Printf.sprintf "  lw t2, %d(s0)\n" offset)
                    | _ -> (reg_map var_offsets frame_size rs2, "")
                  in
                  let dest_reg = 
                    match rd with
                    | Temp m when m >= 15 -> "t0"
                    | _ -> dest
                  in
                  load1 ^ load2 ^ 
                  Printf.sprintf "  %s %s, %s, %s" op dest_reg reg1 reg2 ^
                  (match rd with
                    | Temp m when m >= 15 -> 
                        let stack_offset = -(20 + (m - 15) * 4) in
                        Printf.sprintf "\n  sw t0, %d(s0)" stack_offset
                    | _ -> ""))
                     | BinaryOpImm (op, rd, rs, imm) ->
                let process_imm_value n =
      if n >= -2048 && n <= 2047 then
      string_of_int n
    else
      let hi = (n + 0x800) asr 12 in
      let lo = n - (hi lsl 12) in
      
      let unsigned_hi = 
        if hi < 0 then
          hi + (1 lsl 20)
        else
          hi
      in
      
      assert (lo >= -2048 && lo <= 2047);
      assert (unsigned_hi >= 0 && unsigned_hi <= 1048575);
      
      Printf.sprintf "  lui t1, %d\n  addi t1, t1, %d" unsigned_hi lo
                in
                
                let imm_str = process_imm_value imm in
                
                let actual_op = 
                  if String.contains imm_str '\n' then
                    match op with
                    | "addi" -> "add"
                    | "sub" -> "sub"
                    | "andi" -> "and"
                    | "ori" -> "or"
                    | "xori" -> "xor"
                    | _ -> op
                  else
                    op
                in
                
                (match (rd, rs) with
                | (Temp n, _) when n >= 15 -> 
                    let stack_offset = -(20 + (n - 15) * 4) in
                    let src = reg_map var_offsets frame_size rs in
                    let (reg, load) = 
                      match rs with
                      | Temp m when m >= 15 -> 
                          let offset = -(20 + (m - 15) * 4) in
                          ("t2", Printf.sprintf "  lw t2, %d(s0)\n" offset)
                      | _ -> (src, "")
                    in
                    
                    if String.contains imm_str '\n' then
                      load ^ imm_str ^ 
                      Printf.sprintf "\n  %s t0, t2, t1\n  sw t0, %d(s0)" actual_op stack_offset
                    else
                      load ^ 
                      Printf.sprintf "  %s t0, t2, %s\n  sw t0, %d(s0)" actual_op imm_str stack_offset
                | _ -> 
                    let dest = reg_map var_offsets frame_size rd in
                    let (reg, load) = 
                      match rs with
                      | Temp m when m >= 15 -> 
                          let offset = -(20 + (m - 15) * 4) in
                          ("t2", Printf.sprintf "  lw t2, %d(s0)\n" offset)
                      | _ -> (reg_map var_offsets frame_size rs, "")
                    in
                    let dest_reg = 
                      match rd with
                      | Temp m when m >= 15 -> "t0"
                      | _ -> dest
                    in
                    
                    if String.contains imm_str '\n' then
                      load ^ imm_str ^ 
                      Printf.sprintf "\n  %s %s, %s, t1" actual_op dest_reg reg
                    else
                      load ^ Printf.sprintf "  %s %s, %s, %s" actual_op dest_reg reg imm_str)
          | Branch (cond, rs1, rs2, label) ->
              let (reg1, load1) = 
                match rs1 with
                | Temp m when m >= 15 -> 
                    let offset = -(20 + (m - 15) * 4) in
                    ("t1", Printf.sprintf "  lw t1, %d(s0)\n" offset)
                | _ -> (reg_map var_offsets frame_size rs1, "")
              in
              let (reg2, load2) = 
                match rs2 with
                | Temp m when m >= 15 -> 
                    let offset = -(20 + (m - 15) * 4) in
                    ("t2", Printf.sprintf "  lw t2, %d(s0)\n" offset)
                | _ -> (reg_map var_offsets frame_size rs2, "")
              in
              load1 ^ load2 ^
              (match cond with
              | "beqz" -> Printf.sprintf "  beq %s, zero, %s" reg1 label
              | "bnez" -> Printf.sprintf "  bne %s, zero, %s" reg1 label
              | _ -> Printf.sprintf "  %s %s, %s, %s" cond reg1 reg2 label)
          | Store (rs, base, offset) ->
              let (reg, load) = 
                match rs with
                | Temp m when m >= 15 -> 
                    let stack_offset = -(20 + (m - 15) * 4) in
                    ("t0", Printf.sprintf "  lw t0, %d(s0)\n" stack_offset)
                | _ -> (reg_map var_offsets frame_size rs, "")
              in
              load ^ Printf.sprintf "  sw %s, %d(%s)" reg offset (reg_map var_offsets frame_size base)
          | Load (rd, base, offset) ->
              (match rd with
              | Temp n when n >= 15 -> 
                  let stack_offset = -(20 + (n - 15) * 4) in
                  Printf.sprintf "  lw t0, %d(%s)\n  sw t0, %d(s0)" 
                    offset (reg_map var_offsets frame_size base) stack_offset
              | _ -> 
                  Printf.sprintf "  lw %s, %d(%s)" 
                    (reg_map var_offsets frame_size rd) offset (reg_map var_offsets frame_size base))
          | ReloadVar (reg, var_name) ->
              (try
                let offset = Hashtbl.find var_offsets var_name in
                (match reg with
                | Temp n when n >= 15 -> 
                    let temp_offset = -(20 + (n - 15) * 4) in
                    Printf.sprintf "  lw t0, %d(s0)\n  sw t0, %d(s0)" offset temp_offset
                | _ -> 
                    Printf.sprintf "  lw %s, %d(s0)" (reg_map var_offsets frame_size reg) offset)
              with Not_found ->
                failwith ("Variable " ^ var_name ^ " not found during code generation"))
          | Call (func, num_args) -> 
              (* 修复：保存所有调用者保存寄存器 *)
              let caller_saved = ["t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"; 
                                 "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7"] in
              
              (* 保存寄存器 *)
              let save_code = 
                List.mapi (fun i reg_name ->
                  Printf.sprintf "  sw %s, -%d(s0)" reg_name (20 + i * 4)
                ) caller_saved
              in
              
              (* 函数调用 *)
              let call_code = "  call " ^ func in
              
              (* 恢复寄存器 - 按逆序恢复 *)
              let restore_code = 
                List.rev (List.mapi (fun i reg_name ->
                  Printf.sprintf "  lw %s, -%d(s0)" reg_name (20 + i * 4)
                ) caller_saved)
              in
              
              String.concat "\n" (save_code @ [call_code] @ restore_code)
          | Addi (rd, rs, imm) ->
              Printf.sprintf "  addi %s, %s, %d" 
                (reg_map var_offsets frame_size rd)
                (reg_map var_offsets frame_size rs)
                imm
          | instr -> 
              match instr with
              | Jmp label -> "  j " ^ label
              | Label label -> label ^ ":"
              | Ret ->
                  let ra_offset = frame_size - 4 in      
                  let s0_offset = frame_size - 8 in      
                  Printf.sprintf "  lw ra, %d(sp)\n" ra_offset ^
                  Printf.sprintf "  lw s0, %d(sp)\n" s0_offset ^
                  Printf.sprintf "  addi sp, sp, %d\n" frame_size ^
                  "  jr ra"
              | _ -> failwith "Unhandled instruction"
          in
          convert_instrs (acc_index + 1) (acc_code ^ code ^ "\n") rest
    in
    convert_instrs 0 "" instrs
        
  let calculate_frame_size (ir_func : ir_func) =
    let base_size = 16 in (* 基础保存空间：ra(4) + s0(4) + 额外8字节对齐 *)
    
    let extra_param_space = 
      if List.length ir_func.params > 8 then
        (List.length ir_func.params - 8) * 4
      else 
        0 
    in

    let call_stack_space = ref 0 in
    let analyze_call_stack instr = 
      match instr with
      | Store (_, RiscvReg "sp", offset) when offset >= 0 ->
          call_stack_space := max !call_stack_space (offset + 4)
      | _ -> ()
    in
    List.iter analyze_call_stack ir_func.body;

    let used_offsets = ref [] in
    
    List.iteri (fun i _ ->
      if i < 8 then used_offsets := -(16 + i * 4) :: !used_offsets
    ) ir_func.params;
    
    List.iteri (fun i _ ->
      if i >= 8 then used_offsets := -(16 + i * 4) :: !used_offsets
    ) ir_func.params;

    let max_temp = ref (-1) in
    let min_offset = ref 0 in

    let analyze_instr = function
      | Store (_, RiscvReg "s0", offset) when offset < 0 ->
          used_offsets := offset :: !used_offsets;
          if offset < !min_offset then min_offset := offset
      | Load (Temp n, RiscvReg "s0", offset) when offset < 0 ->
          used_offsets := offset :: !used_offsets;
          if offset < !min_offset then min_offset := offset;
          max_temp := max !max_temp n
      | Li (Temp n, _) | Mv (Temp n, _) | BinaryOp (_, Temp n, _, _)
      | BinaryOpImm (_, Temp n, _, _) | ReloadVar (Temp n, _) ->
          max_temp := max !max_temp n
      | _ -> ()
    in
    List.iter analyze_instr ir_func.body;

    let local_var_size = 
      if !used_offsets <> [] then
        let min_used = !min_offset in
        -min_used
        -min_used
      else 0 in

    let temp_stack_size = 
      if !max_temp >= 15 then (20 + (!max_temp - 15) * 4) else 0 in

    let required_space = base_size + local_var_size + temp_stack_size + extra_param_space + !call_stack_space in

    let aligned_size = ((required_space + 15) / 16) * 16 in

    max aligned_size 32

  let function_prologue name frame_size =
    let ra_offset = frame_size - 4 in      
    let s0_offset = frame_size - 8 in      
    Printf.sprintf "%s:\n" name ^
    Printf.sprintf "  addi sp, sp, -%d\n" frame_size ^
    Printf.sprintf "  sw ra, %d(sp)\n" ra_offset ^
    Printf.sprintf "  sw s0, %d(sp)\n" s0_offset ^
    Printf.sprintf "  addi s0, sp, %d\n" frame_size

  let function_epilogue frame_size =
    let ra_offset = frame_size - 4 in 
    let s0_offset = frame_size - 8 in 
    Printf.sprintf "  lw ra, %d(sp)\n" ra_offset ^
    Printf.sprintf "  lw s0, %d(sp)\n" s0_offset ^
    Printf.sprintf "  addi sp, sp, %d\n" frame_size ^
    "  ret\n"

  let func_to_asm var_offsets (ir_func : ir_func) =
    let buf = Buffer.create 256 in
    let frame_size = calculate_frame_size ir_func in
    
    Buffer.add_string buf (function_prologue ir_func.name frame_size);
      
    (* 保存参数到栈帧 *)
    List.iteri (fun i param ->
      let offset = -(16 + i * 4) in
      if i < 8 then
        Buffer.add_string buf (Printf.sprintf "  sw a%d, %d(s0)\n" i offset)
      else
         let param_stack_offset = (i - 8) * 4 in
         Buffer.add_string buf (Printf.sprintf "  lw t0, %d(sp)\n  sw t0, %d(s0)\n" param_stack_offset offset)
    ) ir_func.params;
    
    let asm_code = instr_to_asm var_offsets frame_size ir_func.body in
    Buffer.add_string buf asm_code;
    
    let has_explicit_return = List.exists (function Ret -> true | _ -> false) ir_func.body in
    
    if not has_explicit_return then (
      Buffer.add_string buf (function_epilogue frame_size);
    );
    
    Buffer.contents buf
end

let () =
  let ast = parse_channel stdin in
  semantic_analysis ast;
  
  let ir_with_offsets = List.map func_to_ir ast in
  
  let (ir_funcs, var_offsets_list) = List.split ir_with_offsets in
  
  let combined_var_offsets = Hashtbl.create 50 in
  List.iter (fun var_offsets ->
    Hashtbl.iter (fun name offset ->
      Hashtbl.add combined_var_offsets name offset
    ) var_offsets
  ) var_offsets_list;
  
  let riscv_asm = List.map (IRToRiscV.func_to_asm combined_var_offsets) ir_funcs in
  
  let oc = open_out "riscv-V.txt" in
  
  Printf.fprintf oc ".global main\n";
  Printf.printf ".global main\n";
  
  List.iter (fun f -> 
    Printf.fprintf oc "%s\n" f;
    Printf.printf "%s\n" f
  ) riscv_asm;
  
  close_out oc;
  
  prerr_endline "Compilation successful! Output also written to riscv-V.txt";
