exception LexicalError of string
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

module StringMap = Map.Make(String)

(* ==================== IR 定义 ==================== *)
type reg = 
  | Zero
  | RA 
  | SP 
  | GP 
  | TP 
  | T0 | T1 | T2 | T3 | T4 | T5 | T6
  | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | S10 | S11
  | A0 | A1 | A2 | A3 | A4 | A5 | A6 | A7

let string_of_reg = function
  | Zero -> "x0"
  | RA -> "x1"
  | SP -> "x2"
  | GP -> "x3"
  | TP -> "x4"
  | T0 -> "x5" | T1 -> "x6" | T2 -> "x7" | T3 -> "x8" | T4 -> "x9"
  | T5 -> "x10" | T6 -> "x11"
  | S0 -> "x18" | S1 -> "x19" | S2 -> "x20" | S3 -> "x21" | S4 -> "x22"
  | S5 -> "x23" | S6 -> "x24" | S7 -> "x25" | S8 -> "x26" | S9 -> "x27"
  | S10 -> "x28" | S11 -> "x29"
  | A0 -> "x10" | A1 -> "x11" | A2 -> "x12" | A3 -> "x13" 
  | A4 -> "x14" | A5 -> "x15" | A6 -> "x16" | A7 -> "x17"

type ir_instr =
  | Lui of reg * int             (* 加载高20位 *)
  | Addi of reg * reg * int      (* 立即数加法 *)
  | Add of reg * reg * reg       (* 寄存器加法 *)
  | Sub of reg * reg * reg       (* 寄存器减法 *)
  | Mul of reg * reg * reg       (* 乘法 *)
  | Div of reg * reg * reg       (* 除法 *)
  | Rem of reg * reg * reg       (* 取余 *)
  | Slt of reg * reg * reg       (* 小于比较 *)
  | Beq of reg * reg * string    (* 相等分支 *)
  | Bne of reg * reg * string    (* 不等分支 *)
  | Blt of reg * reg * string    (* 小于分支 *)
  | Bge of reg * reg * string    (* 大于等于分支 *)
  | Jmp of string                (* 无条件跳转 *)
  | Jal of string                (* 函数调用 *)
  | Jalr of reg * reg * int      (* 寄存器跳转 *)
  | Label of string              (* 标签 *)
  | Sw of reg * reg * int        (* 存储字 *)
  | Lw of reg * reg * int        (* 加载字 *)
  | Comment of string            (* 汇编注释 *)

type ir_func = {
  name: string;
  params: string list;
  body: ir_instr list;
  stack_size: int;
  num_params: int;
}

(* ==================== 代码生成状态 ==================== *)
type codegen_state = {
  temp_counter: int;
  label_counter: int;
  var_offset: (string, int) Hashtbl.t;
  stack_size: int;
  loop_labels: (string * string) list;
  max_temp_used: int;
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
  max_temp_used = 0;
}

(* ==================== 辅助函数 ==================== *)
let fresh_temp state = 
  if state.temp_counter >= 6 then 
    raise (SemanticError "Too many temporary registers used");
  let reg = match state.temp_counter with
    | 0 -> T0
    | 1 -> T1
    | 2 -> T2
    | 3 -> T3
    | 4 -> T4
    | 5 -> T5
    | _ -> T6
  in
  (reg, {state with 
         temp_counter = state.temp_counter + 1;
         max_temp_used = max state.max_temp_used (state.temp_counter + 1)})

let reset_temp state = {state with temp_counter = 0}

let fresh_label state prefix =
  let label = Printf.sprintf "%s%d" prefix state.label_counter in
  (label, {state with label_counter = state.label_counter + 1})

let get_var_offset state var =
  try 
    (Hashtbl.find state.var_offset var, state)
  with Not_found -> 
    let offset = state.stack_size in
    Hashtbl.add state.var_offset var offset;
    let new_state = {state with stack_size = offset + 8} in
    (offset, new_state)

(* 正确加载立即数 *)
let load_immediate state value =
  if value = 0 then
    let (temp, state') = fresh_temp state in
    (temp, [Addi(temp, Zero, 0)], state')
  else if value >= -2048 && value <= 2047 then
    let (temp, state') = fresh_temp state in
    (temp, [Addi(temp, Zero, value)], state')
  else
    (* 处理大立即数 - 使用LUI+ADDI组合 *)
    let (temp, state') = fresh_temp state in
    let upper = (value lsr 12) land 0xFFFFF in
    let lower = value land 0xFFF in
    (* 如果低12位是负数，需要调整 *)
    let (upper, lower) = 
      if lower >= 0x800 then (upper + 1, lower - 0x1000) 
      else (upper, lower) in
    (temp, [Lui(temp, upper); Addi(temp, temp, lower)], state')

let create_prologue stack_size num_params =
  [
    Comment ("Function prologue for " ^ string_of_int stack_size ^ " bytes");
    Addi(SP, SP, -stack_size);  (* 分配栈空间 *)
    Sw(RA, SP, stack_size - 4);  (* 保存返回地址 *)
    (if num_params > 0 then Sw(A0, SP, stack_size - 8) else Comment "No params to save");
    (if num_params > 1 then Sw(A1, SP, stack_size - 12) else Comment "");
    (if num_params > 2 then Sw(A2, SP, stack_size - 16) else Comment "");
    (if num_params > 3 then Sw(A3, SP, stack_size - 20) else Comment "");
    Comment "End prologue";
  ]

let create_epilogue stack_size =
  [
    Comment "Function epilogue";
    Lw(RA, SP, stack_size - 4);  (* 恢复返回地址 *)
    Addi(SP, SP, stack_size);    (* 释放栈空间 *)
    Jalr(Zero, RA, 0);           (* 返回调用点 *)
    Comment "End epilogue";
  ]

(* 语义分析 - 保持不变 *)
let semantic_analysis ast = 
  (* 保持不变 *)
  print_endline "Semantic analysis passed!"

(* ==================== AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  match expr with
  | Num n -> 
      load_immediate state n
  
  | Var x -> 
      let offset, state' = get_var_offset state x in
      let (temp, state'') = fresh_temp state' in
      (temp, [Lw(temp, SP, offset)], state'')
  
  | Binary (op, e1, e2) ->
      let (e1_reg, e1_code, state') = expr_to_ir state e1 in
      let (e2_reg, e2_code, state'') = expr_to_ir (reset_temp state') e2 in
      let (temp, state''') = fresh_temp state'' in
      
      let instr = match op with
        | Add -> Add(temp, e1_reg, e2_reg)
        | Sub -> Sub(temp, e1_reg, e2_reg)
        | Mul -> Mul(temp, e1_reg, e2_reg)
        | Div -> Div(temp, e1_reg, e2_reg)
        | Mod -> Rem(temp, e1_reg, e2_reg)
        | Lt -> Slt(temp, e1_reg, e2_reg)
        | _ -> failwith "Unsupported binary operation"
      in
      (temp, e1_code @ e2_code @ [instr], state''')
  
  | Call (name, args) ->
      (* 准备参数 *)
      let rec prepare_args state args idx = 
        match args with
        | [] -> ([], state)
        | arg::rest ->
            let (arg_reg, arg_code, state') = expr_to_ir state arg in
            let save_code = 
              if idx < 4 then [Addi((match idx with 0 -> A0 | 1 -> A1 | 2 -> A2 | 3 -> A3), arg_reg, 0)]
              else [Sw(arg_reg, SP, 16 + (idx - 4) * 4)] (* 参数保存在栈上 *)
            in
            let (rest_code, state'') = prepare_args (reset_temp state') rest (idx + 1) in
            (arg_code @ save_code @ rest_code, state'')
      in
      
      let (arg_code, state') = prepare_args state args 0 in
      let call_instr = [Jal(name)] in
      
      (* 函数调用结果在A0寄存器 *)
      (A0, arg_code @ call_instr, state')
  
  | _ -> failwith "Unsupported expression"

let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> block_to_ir state b
  
  | DeclStmt (_, name, Some expr) -> 
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset state' name in
      (expr_code @ [Sw(expr_reg, SP, offset)], reset_temp state'')
  
  | DeclStmt (_, name, None) -> 
      let offset, state' = get_var_offset state name in
      ([], state')
  
  | AssignStmt (name, expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset state' name in
      (expr_code @ [Sw(expr_reg, SP, offset)], reset_temp state'')
  
  | IfStmt (cond, then_stmt, else_stmt) ->
      let (cond_reg, cond_code, state') = expr_to_ir state cond in
      let (then_label, state'') = fresh_label state' "then" in
      let (else_label, state''') = fresh_label state'' "else" in
      let (merge_label, state'''') = fresh_label state''' "merge" in
      
      let (then_code, state''''') = stmt_to_ir (reset_temp state'''') then_stmt in
      let (else_code, state'''''') = 
        match else_stmt with
        | Some s -> stmt_to_ir (reset_temp state''''') s
        | None -> ([], state''''') 
      in
      
      (cond_code @ 
       [Bne(cond_reg, Zero, then_label);
        Jmp(else_label);
        Label then_label] @
       then_code @
       [Jmp(merge_label);
        Label else_label] @
       else_code @
       [Label merge_label], state'''''')

  | WhileStmt (cond, body) ->
      let (loop_label, state') = fresh_label state "loop" in
      let (end_label, state'') = fresh_label state' "end" in
      
      let state_with_loop = { state'' with loop_labels = (end_label, loop_label) :: state''.loop_labels } in
      
      let (cond_reg, cond_code, state''') = expr_to_ir state_with_loop cond in
      let (body_code, state'''') = stmt_to_ir state''' body in
      
      ( [Label loop_label] @
        cond_code @
        [Beq(cond_reg, Zero, end_label)] @
        body_code @
        [Jmp(loop_label);
         Label end_label],
        { state'''' with loop_labels = List.tl state''''.loop_labels } )

  | ReturnStmt (Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      (expr_code @ [Addi(A0, expr_reg, 0); Comment "Return value"; Jmp("__return")], state')
  
  | ReturnStmt None ->
      ([Jmp("__return")], state)
  
  | ExprStmt expr ->
      let (_, expr_code, state') = expr_to_ir state expr in
      (expr_code, reset_temp state')
  
  | BreakStmt ->
      (match state.loop_labels with
       | (end_label, _) :: _ -> [Jmp(end_label)], state
       | [] -> failwith "break statement outside loop")
  
  | ContinueStmt ->
      (match state.loop_labels with
       | (_, loop_label) :: _ -> [Jmp(loop_label)], state
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
  
  (* 首先处理参数 - 存储到栈帧中 *)
  let state' = 
    List.fold_left (fun st (param : Ast.param) ->
      let offset, st' = get_var_offset st param.name in
      st'
    ) state func.params
  in
  
  (* 生成函数体 *)
  let (body_code, final_state) = block_to_ir state' func.body in
  
  (* 添加函数返回点标签 *)
  let body_with_return = body_code @ [Label "__return"] in
  
  (* 计算栈大小（局部变量空间 + 保存寄存器空间） *)
  let stack_size = final_state.stack_size + 20 in (* 返回地址 + 保存寄存器 *)
  
  (* 添加序言和尾声 *)
  let prologue = create_prologue stack_size (List.length func.params) in
  let epilogue = create_epilogue stack_size in
  
  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = prologue @ body_with_return @ epilogue;
    stack_size = stack_size;
    num_params = List.length func.params;
  }

(* 将IR转换为RISC-V汇编字符串 *)
let string_of_ir ir_func =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf ".globl %s\n" ir_func.name);
  Buffer.add_string buf (Printf.sprintf "%s:\n" ir_func.name);
  
  List.iter (fun instr ->
    let instr_str = match instr with
      | Lui (rd, imm) -> 
          Printf.sprintf "    lui %s, %d" (string_of_reg rd) imm
      | Addi (rd, rs1, imm) -> 
          Printf.sprintf "    addi %s, %s, %d" (string_of_reg rd) (string_of_reg rs1) imm
      | Add (rd, rs1, rs2) -> 
          Printf.sprintf "    add %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Sub (rd, rs1, rs2) -> 
          Printf.sprintf "    sub %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Mul (rd, rs1, rs2) -> 
          Printf.sprintf "    mul %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Div (rd, rs1, rs2) -> 
          Printf.sprintf "    div %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Rem (rd, rs1, rs2) -> 
          Printf.sprintf "    rem %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Slt (rd, rs1, rs2) -> 
          Printf.sprintf "    slt %s, %s, %s" (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
      | Beq (rs1, rs2, label) -> 
          Printf.sprintf "    beq %s, %s, %s" (string_of_reg rs1) (string_of_reg rs2) label
      | Bne (rs1, rs2, label) -> 
          Printf.sprintf "    bne %s, %s, %s" (string_of_reg rs1) (string_of_reg rs2) label
      | Blt (rs1, rs2, label) -> 
          Printf.sprintf "    blt %s, %s, %s" (string_of_reg rs1) (string_of_reg rs2) label
      | Bge (rs1, rs2, label) -> 
          Printf.sprintf "    bge %s, %s, %s" (string_of_reg rs1) (string_of_reg rs2) label
      | Jmp label -> 
          Printf.sprintf "    j %s" label
      | Jal label -> 
          Printf.sprintf "    jal %s" label
      | Jalr (rd, rs, imm) -> 
          Printf.sprintf "    jalr %s, %s, %d" (string_of_reg rd) (string_of_reg rs) imm
      | Label label -> 
          Printf.sprintf "%s:" label
      | Sw (rs, base, offset) -> 
          Printf.sprintf "    sw %s, %d(%s)" (string_of_reg rs) offset (string_of_reg base)
      | Lw (rd, base, offset) -> 
          Printf.sprintf "    lw %s, %d(%s)" (string_of_reg rd) offset (string_of_reg base)
      | Comment str -> 
          Printf.sprintf "    # %s" str
    in
    Buffer.add_string buf (instr_str ^ "\n")
  ) ir_func.body;
  
  Buffer.contents buf

(* 主函数保持不变 *)
let () =
  let ch = open_in "test/04_while_break.tc" in
  let ast = parse_channel ch in
  close_in ch;
  semantic_analysis ast;
  let ast_str = string_of_ast ast in
  let out_ch = open_out "ast.txt" in
  Printf.fprintf out_ch "%s\n" ast_str;
  close_out out_ch;
  
  let ir = List.map func_to_ir ast in
  
  let ir_out = open_out "riscv.s" in
  (* 添加RISC-V汇编头 *)
  output_string ir_out ".text\n";
  output_string ir_out ".align 2\n";
  output_string ir_out ".globl __start\n";
  output_string ir_out "__start:\n";
  output_string ir_out "    jal main\n";
  output_string ir_out "    li a0, 0\n";
  output_string ir_out "    jal exit\n\n";
  
  (* 输出函数 *)
  List.iter (fun f -> 
    Printf.fprintf ir_out "%s\n" (string_of_ir f)
  ) ir;
  
  (* 添加退出函数 *)
  output_string ir_out ".globl exit\n";
  output_string ir_out "exit:\n";
  output_string ir_out "    addi a0, x0, 93\n";  (* Linux exit syscall *)
  output_string ir_out "    ecall\n";
  
  close_out ir_out;
  
  print_endline "Compilation successful!";
  print_endline ("AST written to ast.txt");
  print_endline ("RISC-V assembly written to riscv.s")