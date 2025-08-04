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
  | Lui of reg * int               (* 加载高位立即数 *)
  | Addi of reg * reg * int        (* 加立即数 *)
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

(* ==================== 高效立即数处理 ==================== *)
let handle_large_imm reg n =
  let upper = (n asr 12) land 0xFFFFF in
  let lower = n land 0xFFF in
  
  (* 处理低位部分的符号问题 - 这是核心优化 *)
  if lower >= 0x800 then
    let upper = upper + 1 in
    let lower = lower - 0x1000 in
    [Lui (reg, upper); Addi (reg, reg, lower)]
  else
    [Lui (reg, upper); Addi (reg, reg, lower)]

let load_imm reg n state =
  if n >= -2048 && n <= 2047 then
    ([Li (reg, n)], state)
  else
    let (temp, state') = fresh_temp state in
    (handle_large_imm temp n, state')

(* ==================== AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  match expr with
  | Num n -> 
      let (temp, state') = fresh_temp state in
      let (code, state'') = load_imm temp n state' in
      (temp, code, state'')
  
  | Var x -> 
      let offset, state' = get_var_offset state x in
      (* 优化：尝试重用已有寄存器而不是创建新临时寄存器 *)
      if offset >= -2048 && offset <= 2047 then
        (RiscvReg "t0", [Load (RiscvReg "t0", RiscvReg "sp", offset)], state')
      else
        let (temp, state'') = fresh_temp state' in
        (temp, [Load (temp, RiscvReg "sp", offset)], state'')
  
  | Binary (op, e1, e2) ->
      (* 性能优化：常量折叠 *)
      match (op, e1, e2) with
      | (Add, Num n1, Num n2) -> expr_to_ir state (Num (n1 + n2))
      | (Sub, Num n1, Num n2) -> expr_to_ir state (Num (n1 - n2))
      | (Mul, Num n1, Num n2) -> expr_to_ir state (Num (n1 * n2))
      | (Div, Num n1, Num n2) when n2 <> 0 -> expr_to_ir state (Num (n1 / n2))
      | _ ->
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
  
  | DeclStmt (_, name, Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr in
      let offset, state'' = get_var_offset state' name in
      (expr_code @ [Store (expr_reg, RiscvReg "sp", offset)], state'')
  
  | DeclStmt (_, name, None) ->
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
        | None -> ([], state''''') 
      in
      
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
      let (cond_label, state''') = fresh_label state'' "cond" in
      
      let state_with_loop = { state''' with loop_labels = (end_label, cond_label) :: state'''.loop_labels } in
      
      let (cond_reg, cond_code, state'''') = expr_to_ir state_with_loop cond in
      let (body_code, state''''') = stmt_to_ir state'''' body in
      
      (* 优化控制流结构 *)
      ([Label cond_label] @
        cond_code @
        [Branch ("beqz", cond_reg, RiscvReg "zero", end_label)] @
        body_code @
        [Jmp cond_label;
         Label end_label],
        { state''''' with loop_labels = List.tl state'''''.loop_labels } )
  
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

(* ==================== 输出优化 ==================== *)
let string_of_reg = function
  | RiscvReg s -> s
  | Temp n -> "t" ^ string_of_int n

let string_of_ir ir_func =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "Function: %s\n" ir_func.name);
  Buffer.add_string buf "Params: ";
  List.iter (fun p -> Buffer.add_string buf (p ^ " ")) ir_func.params;
  Buffer.add_string buf "\nBody:\n";
  List.iter (fun instr ->
    let instr_str = match instr with
      | Li (r, n) -> Printf.sprintf "  li %s, %d" (string_of_reg r) n
      | Lui (r, imm) -> Printf.sprintf "  lui %s, %d" (string_of_reg r) imm
      | Addi (rd, rs, imm) -> Printf.sprintf "  addi %s, %s, %d" (string_of_reg rd) (string_of_reg rs) imm
      | Mv (rd, rs) -> Printf.sprintf "  mv %s, %s" (string_of_reg rd) (string_of_reg rs)
      | BinaryOp (op, rd, rs1, rs2) ->
          Printf.sprintf "  %s %s, %s, %s" op
            (string_of_reg rd)
            (string_of_reg rs1)
            (string_of_reg rs2)
      | Branch (cond, rs1, rs2, label) ->
          Printf.sprintf "  %s %s, %s, %s" cond
            (string_of_reg rs1)
            (string_of_reg rs2)
            label
      | Jmp label -> Printf.sprintf "  j %s" label
      | Label label -> label ^ ":"
      | Call func -> Printf.sprintf "  call %s" func
      | Ret -> "  ret"
      | Store (rs, base, offset) ->
          Printf.sprintf "  sd %s, %d(%s)"
            (string_of_reg rs)
            offset
            (string_of_reg base)
      | Load (rd, base, offset) ->
          Printf.sprintf "  ld %s, %d(%s)"
            (string_of_reg rd)
            offset
            (string_of_reg base)
    in
    Buffer.add_string buf (instr_str ^ "\n")
  ) ir_func.body;
  Buffer.contents buf

(* ==================== 主函数 ==================== *)
let () =
  let ch = open_in "test/04_while_break.tc" in
  let ast = parse_channel ch in
  close_in ch;
  semantic_analysis ast;
  
  (* 输出AST *)
  let ast_str = string_of_ast ast in
  let out_ch = open_out "ast.txt" in
  Printf.fprintf out_ch "%s\n" ast_str;
  close_out out_ch;
  
  (* 生成IR *)
  let ir = List.map func_to_ir ast in
  
  (* 输出IR *)
  let ir_out = open_out "risc-V.txt" in
  List.iter (fun f -> 
    Printf.fprintf ir_out "%s\n" (string_of_ir f)
  ) ir;
  close_out ir_out;
  
  print_endline "Compilation successful!";
  print_endline "AST written to ast.txt";
  print_endline "RISC-V assembly written to risc-V.txt"