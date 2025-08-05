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
  | Lui of reg * int               (* 加载高20位 *)
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

(* 处理大立即数（核心修复） *)
let handle_large_immediate state reg n =
  (* 正确拆分大立即数（包括负数） *)
  let high_bits = (n asr 12) in
  let low_bits = n - (high_bits lsl 12) in
  
  (* 确保低位在[-2048, 2047]范围内 *)
  let (adjusted_high, adjusted_low) = 
    if low_bits < -2048 then
      (high_bits - 1, n - ((high_bits - 1) lsl 12))
    else if low_bits > 2047 then
      (high_bits + 1, n - ((high_bits + 1) lsl 12))
    else
      (high_bits, low_bits)
  in
  
  (reg, [
      Lui (reg, adjusted_high);   (* 加载高20位 *)
      Addi (reg, reg, adjusted_low)   (* 添加低12位 *)
    ], {state with temp_counter = state.temp_counter + 1})

(* ==================== 表达式转换 ==================== *)
let rec expr_to_ir state expr =
  match expr with
  | Num n -> 
      (* 核心修复：处理大立即数 *)
      if n >= -2048 && n <= 2047 then
        let (temp, state') = fresh_temp state in
        (temp, [Li (temp, n)], state')
      else
        let (temp, state') = fresh_temp state in
        handle_large_immediate state' temp n
        
  | Var x -> 
      let offset, state' = get_var_offset state x in
      let (temp, state'') = fresh_temp state' in
      (temp, [Load (temp, RiscvReg "sp", offset)], state'')
  
  | Binary (op, e1, e2) ->
      let op_str = match op with
        | Add -> "add" | Sub -> "sub" | Mul -> "mul" 
        | Div -> "div" | Mod -> "rem" | Lt -> "slt"
        | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
        | Eq -> "seq" | Neq -> "sne" | And -> "and"
        | Or -> "or" | ShiftL -> "sll" | ShiftR -> "srl" in
      let (e1_reg, e1_code, state') = expr_to_ir state e1 in
      let (e2_reg, e2_code, state'') = expr_to_ir state' e2 in
      let (temp, state''') = fresh_temp state'' in
      (temp, e1_code @ e2_code @ [BinaryOp (op_str, temp, e1_reg, e2_reg)], state''')
  
  | _ -> failwith "Unsupported expression"

(* ==================== 语句转换 ==================== *)
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
      ( cond_code @ 
        [Branch ("bnez", cond_reg, RiscvReg "zero", then_label);
         Jmp else_label;
         Label then_label] @ 
        then_code @ 
        [Jmp merge_label;
         Label else_label] @ 
        else_code @ 
        [Label merge_label], 
        state'''''' )
  
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

(* ==================== 函数转换 ==================== *)
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

(* ==================== 主程序 ==================== *)
let () =
  let ch = open_in "test/04_while_break.tc" in
  let lexbuf = Lexing.from_channel ch in
  let ast = 
    try ToyC_riscv_lib.Parser.prog ToyC_riscv_lib.Lexer.token lexbuf 
    with e -> close_in ch; raise e
  in
  close_in ch;
  
  semantic_analysis ast;
  
  let ir = List.map func_to_ir ast in
  
  (* 输出优化后的汇编 *)
  let oc = open_out "optimized_riscv.s" in
  List.iter (fun func ->
    output_string oc (Printf.sprintf ".globl %s\n" func.name);
    output_string oc (Printf.sprintf "%s:\n" func.name);
    
    List.iter (fun instr ->
      let reg_to_str = function
        | RiscvReg s -> s
        | Temp i -> "t" ^ string_of_int i
      in
      
      let instr_str = match instr with
        | Lui (rd, n) ->
            Printf.sprintf "  lui %s, %d" (reg_to_str rd) n
            
        | Addi (rd, rs, n) ->
            Printf.sprintf "  addi %s, %s, %d" 
              (reg_to_str rd) (reg_to_str rs) n
              
        | Mv (rd, rs) -> 
            Printf.sprintf "  mv %s, %s" 
              (reg_to_str rd) (reg_to_str rs)
            
        | BinaryOp (op, rd, rs1, rs2) -> 
            Printf.sprintf "  %s %s, %s, %s" op
              (reg_to_str rd) (reg_to_str rs1) (reg_to_str rs2)
            
        | Branch (cond, rs1, rs2, label) -> 
            Printf.sprintf "  %s %s, %s, %s" cond
              (reg_to_str rs1) (reg_to_str rs2) label
            
        | Jmp label -> "  j " ^ label
        | Label label -> label ^ ":"
        | Call func -> "  call " ^ func
        | Ret -> "  ret"
        
        | Store (rs, base, off) when off >= -2048 && off <= 2047 -> 
            Printf.sprintf "  sd %s, %d(%s)"
              (reg_to_str rs) off (reg_to_str base)
              
        | Store (rs, base, off) -> 
            (* 大偏移量需要单独处理 *)
            let (temp, _) = fresh_temp initial_state in
            Printf.sprintf "  lui %s, %%hi(%d)\n  addi %s, %s, %%lo(%d)\n  add %s, %s, %s\n  sd %s, 0(%s)" 
              (reg_to_str temp) off 
              (reg_to_str temp) (reg_to_str temp) off
              (reg_to_str temp) (reg_to_str base) (reg_to_str temp)
              (reg_to_str rs) (reg_to_str temp)
              
        | Load (rd, base, off) when off >= -2048 && off <= 2047 -> 
            Printf.sprintf "  ld %s, %d(%s)"
              (reg_to_str rd) off (reg_to_str base)
              
        | Load (rd, base, off) -> 
            (* 大偏移量需要单独处理 *)
            let (temp, _) = fresh_temp initial_state in
            Printf.sprintf "  lui %s, %%hi(%d)\n  addi %s, %s, %%lo(%d)\n  add %s, %s, %s\n  ld %s, 0(%s)" 
              (reg_to_str temp) off 
              (reg_to_str temp) (reg_to_str temp) off
              (reg_to_str temp) (reg_to_str base) (reg_to_str temp)
              (reg_to_str rd) (reg_to_str temp)
      in
      output_string oc (instr_str ^ "\n")
    ) func.body;
    
    output_string oc "\n"
  ) ir;
  
  close_out oc;
  
  print_endline "Optimized assembly written to optimized_riscv.s"