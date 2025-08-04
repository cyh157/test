exception LexicalError of string [@@warning "-38"]
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

module StringMap = Map.Make(String)

(* ==================== 优化的IR定义 ==================== *)
type reg =
  | RiscvReg of string
  | Temp of int

type ir_instr =
  | Li of reg * int
  | Lui of reg * int
  | Addi of reg * reg * int
  | BinaryOp of string * reg * reg * reg
  | Branch of string * reg * reg * string
  | Jmp of string
  | Label of string
  | Call of string
  | Ret
  | Store of reg * reg * int
  | Load of reg * reg * int
  | Mv of reg * reg

type ir_func = {
  name: string;
  params: string list;
  body: ir_instr list;
  stack_size: int;
}

(* ==================== 高性能代码生成状态 ==================== *)
type codegen_state = {
  mutable temp_counter: int;
  mutable label_counter: int;
  var_offset: (string, int) Hashtbl.t;
  mutable stack_size: int;
  mutable loop_labels: (string * string) list;
  mutable current_code: ir_instr list;
  const_values: (int, reg) Hashtbl.t; (* 仅缓存整数常量 *)
}

let initial_state () = 
  {
    temp_counter = 0;
    label_counter = 0;
    var_offset = Hashtbl.create 32;
    stack_size = 0;
    loop_labels = [];
    current_code = [];
    const_values = Hashtbl.create 32;
  }

(* ==================== 高效辅助函数 ==================== *)
let fresh_temp state =
  let temp = state.temp_counter in
  state.temp_counter <- temp + 1;
  Temp temp

let fresh_label state prefix =
  let label = Printf.sprintf "%s%d" prefix state.label_counter in
  state.label_counter <- state.label_counter + 1;
  label

let get_var_offset state var =
  try Hashtbl.find state.var_offset var
  with Not_found ->
    let offset = (state.stack_size + 7) land (lnot 7) in
    Hashtbl.add state.var_offset var offset;
    state.stack_size <- offset + 8;
    offset

let emit state instr = 
  state.current_code <- instr :: state.current_code

(* ==================== 立即数范围问题终极解决方案 ==================== *)
let emit_imm_load state reg n =
  (* 检查是否在有效范围内 [-2048, 2047] *)
  if n >= -2048 && n <= 2047 then
    emit state (Li (reg, n))
  else 
    (* 处理大立即数的标准RISC-V方法 *)
    let high_bits = (n + 0x800) lsr 12 in
    let low_bits = n - (high_bits lsl 12) in
    
    emit state (Lui (reg, high_bits));
    if low_bits <> 0 then
      emit state (Addi (reg, reg, low_bits))

(* ==================== 优化的AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  match expr with
  | Num n ->
      (* 使用常量缓存优化 *)
      begin
        try Hashtbl.find state.const_values n
        with Not_found ->
          let temp = fresh_temp state in
          if n = 0 then
            emit state (Mv (temp, RiscvReg "x0"))
          else
            emit_imm_load state temp n;
          Hashtbl.add state.const_values n temp;
          temp
      end
      
  | Var x ->
      let offset = get_var_offset state x in
      let temp = fresh_temp state in
      (* 对于在范围内的偏移量，直接使用load指令 *)
      if offset >= -2048 && offset <= 2047 then
        emit state (Load (temp, RiscvReg "sp", offset))
      else
        (* 对于大偏移量，使用临时寄存器计算地址 *)
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset;
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
        emit state (Load (temp, addr_reg, 0));
      temp
      
  | Binary (op, e1, e2) ->
      let e1_reg = expr_to_ir state e1 in
      let e2_reg = expr_to_ir state e2 in
      let temp = fresh_temp state in
      let op_str = match op with
        | Add -> "add" | Sub -> "sub" | Mul -> "mul"
        | Div -> "div" | Mod -> "rem" | Lt -> "slt"
        | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
        | Eq -> "seq" | Neq -> "sne" | And -> "and"
        | Or -> "or" | _ -> "add"  (* 默认使用add *)
      in
      emit state (BinaryOp (op_str, temp, e1_reg, e2_reg));
      temp
      
  | _ -> 
      (* 默认返回0寄存器 *)
      RiscvReg "x0"

(* ==================== 语句处理优化 ==================== *)
let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> List.iter (fun s -> stmt_to_ir state s) b.stmts
  
  | DeclStmt (_, name, Some expr) ->
      let expr_reg = expr_to_ir state expr in
      let offset = get_var_offset state name in
      if offset >= -2048 && offset <= 2047 then
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      else
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset;
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
        emit state (Store (expr_reg, addr_reg, 0))
  
  | DeclStmt (_, name, None) ->
      ignore (get_var_offset state name)  (* 只是分配空间 *)
  
  | AssignStmt (name, expr) ->
      let expr_reg = expr_to_ir state expr in
      let offset = 
        try Hashtbl.find state.var_offset name 
        with Not_found -> get_var_offset state name
      in
      if offset >= -2048 && offset <= 2047 then
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      else
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset;
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
        emit state (Store (expr_reg, addr_reg, 0))
  
  | IfStmt (cond, then_stmt, else_stmt) ->
      let cond_reg = expr_to_ir state cond in
      let else_label = fresh_label state "else" in
      let merge_label = fresh_label state "merge" in
      
      emit state (Branch ("beqz", cond_reg, RiscvReg "zero", else_label));
      stmt_to_ir state then_stmt;
      emit state (Jmp merge_label);
      
      emit state (Label else_label);
      Option.iter (fun s -> stmt_to_ir state s) else_stmt;
      
      emit state (Label merge_label)
  
  | ReturnStmt (Some expr) ->
      let expr_reg = expr_to_ir state expr in
      emit state (Mv (RiscvReg "a0", expr_reg));
      emit state Ret
  
  | ReturnStmt None ->
      emit state Ret
  
  | ExprStmt expr ->
      ignore (expr_to_ir state expr)  (* 生成表达式代码但忽略结果 *)
  
  | WhileStmt (cond, body) ->
      let start_label = fresh_label state "while_start" in
      let cond_label = fresh_label state "while_cond" in
      let end_label = fresh_label state "while_end" in
      
      state.loop_labels <- (end_label, cond_label) :: state.loop_labels;
      
      emit state (Jmp cond_label);
      emit state (Label start_label);
      stmt_to_ir state body;
      
      emit state (Label cond_label);
      let cond_reg = expr_to_ir state cond in
      emit state (Branch ("bnez", cond_reg, RiscvReg "zero", start_label));
      
      emit state (Label end_label);
      state.loop_labels <- List.tl state.loop_labels
  
  | BreakStmt ->
      (match state.loop_labels with
      | (end_label, _) :: _ -> emit state (Jmp end_label)
      | [] -> ())  (* 忽略函数外的break *)
  
  | ContinueStmt ->
      (match state.loop_labels with
      | (_, loop_label) :: _ -> emit state (Jmp loop_label)
      | [] -> ())  (* 忽略函数外的continue *)
  
  | EmptyStmt -> ()  (* 忽略空语句 *)

(* ==================== 函数处理优化 ==================== *)
let func_to_ir (func : Ast.func_def) : ir_func =
  let state = initial_state () in
  
  (* 预分配参数偏移量 - 避免多次查找 *)
  List.iteri (fun i (p : Ast.param) ->
    let offset = i * 8 in
    Hashtbl.add state.var_offset p.name offset;
  ) func.params;
  
  state.stack_size <- List.length func.params * 8;
  
  block_to_ir state func.body;
  
  (* 16字节栈对齐 *)
  let aligned_stack_size = 
    if state.stack_size > 0 then
      ((state.stack_size + 15) / 16) * 16
    else 0
  in
  
  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = List.rev state.current_code;  (* 反转以获得正确指令顺序 *)
    stack_size = aligned_stack_size;
  }

and block_to_ir state block =
  List.iter (fun stmt -> stmt_to_ir state stmt) block.stmts

(* ==================== 高效的IR输出 ==================== *)
let string_of_reg = function
  | RiscvReg s -> s
  | Temp i -> Printf.sprintf "t%d" i

let string_of_ir_instr = function
  | Li (r, n) -> 
      if n >= -2048 && n <= 2047 then
        Printf.sprintf "li %s, %d" (string_of_reg r) n
      else
        Printf.sprintf "# LARGE IMM: %d\n  lui %s, %d\n  addi %s, %s, %d" 
          n (string_of_reg r) (n lsr 12) (string_of_reg r) (string_of_reg r) (n land 0xFFF)
        
  | Lui (r, n) -> Printf.sprintf "lui %s, %d" (string_of_reg r) n
  | Addi (rd, rs1, imm) when imm >= -2048 && imm <= 2047 ->
      Printf.sprintf "addi %s, %s, %d" (string_of_reg rd) (string_of_reg rs1) imm
  | Addi (rd, rs1, imm) ->
      Printf.sprintf "# INVALID ADDI: %d\n  lui %s, %d\n  addi %s, %s, %d" 
        imm (string_of_reg rd) (imm lsr 12) (string_of_reg rd) (string_of_reg rd) (imm land 0xFFF)
        
  | BinaryOp (op, rd, rs1, rs2) -> 
      Printf.sprintf "%s %s, %s, %s" op (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
  | Branch (op, r1, r2, label) -> 
      Printf.sprintf "%s %s, %s, %s" op (string_of_reg r1) (string_of_reg r2) label
  | Jmp label -> "j " ^ label
  | Label s -> s ^ ":"
  | Call f -> "call " ^ f
  | Ret -> "ret"
  | Store (r, base, off) when off >= -2048 && off <= 2047 ->
      Printf.sprintf "sd %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Store (r, base, off) ->
      let temp = "t" ^ string_of_int (off land 0xFFFF) in
      Printf.sprintf "# LARGE OFFSET: %d\n  lui %s, %d\n  addi %s, %s, %d\n  sd %s, 0(%s)" 
        off temp (off lsr 12) temp temp (off land 0xFFF) (string_of_reg r) temp
        
  | Load (r, base, off) when off >= -2048 && off <= 2047 ->
      Printf.sprintf "ld %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Load (r, base, off) ->
      let temp = "t" ^ string_of_int (off land 0xFFFF) in
      Printf.sprintf "# LARGE OFFSET: %d\n  lui %s, %d\n  addi %s, %s, %d\n  ld %s, 0(%s)" 
        off temp (off lsr 12) temp temp (off land 0xFFF) (string_of_reg r) temp
        
  | Mv (rd, rs) -> Printf.sprintf "mv %s, %s" (string_of_reg rd) (string_of_reg rs)

let string_of_ir_func f =
  let buffer = Buffer.create 1024 in
  Buffer.add_string buffer (Printf.sprintf ".global %s\n" f.name);
  Buffer.add_string buffer (Printf.sprintf "%s:\n" f.name);
  
  if f.stack_size > 0 then
    Buffer.add_string buffer (Printf.sprintf "  addi sp, sp, -%d\n" f.stack_size);
  
  List.iter (fun instr ->
    Buffer.add_string buffer "  ";
    Buffer.add_string buffer (string_of_ir_instr instr);
    Buffer.add_char buffer '\n'
  ) f.body;
  
  if f.stack_size > 0 then
    Buffer.add_string buffer (Printf.sprintf "  addi sp, sp, %d\n" f.stack_size);
  
  Buffer.add_string buffer "  ret\n";
  Buffer.contents buffer

(* ==================== 主编译流程 ==================== *)
let () =
  let ch = open_in "test/04_while_break.tc" in
  let lexbuf = Lexing.from_channel ch in
  let ast = 
    try ToyC_riscv_lib.Parser.prog ToyC_riscv_lib.Lexer.token lexbuf 
    with e -> close_in ch; raise e
  in
  close_in ch;
  
  (* 语义分析 *)
  ToyC_riscv_lib.Semantic_analysis.semantic_analysis ast;
  
  (* 生成IR *)
  let ir = List.map func_to_ir ast in
  
  (* 输出IR *)
  let out_ch = open_out "risc-V.s" in
  List.iter (fun f ->
    output_string out_ch (string_of_ir_instr (Label f.name));
    output_string out_ch "\n";
    output_string out_ch (string_of_ir_func f);
    output_string out_ch "\n"
  ) ir;
  close_out out_ch;
  
  print_endline "Compilation successful!";
  print_endline "Optimized RISC-V assembly written to risc-V.txt"