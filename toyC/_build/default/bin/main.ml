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
  | Li of reg * int         (* 加载立即数 *)
  | Lui of reg * int        (* 加载高位立即数 *)
  | Addi of reg * reg * int (* 加立即数 *)
  | BinaryOp of string * reg * reg * reg (* 二元运算 (只适用于两个寄存器) *)
  | Branch of string * reg * reg * string (* 条件分支 *)
  | Jmp of string           (* 无条件跳转 *)
  | Label of string         (* 标签 *)
  | Call of string          (* 函数调用 *)
  | Ret                     (* 返回 *)
  | Store of reg * reg * int (* 存储到内存 *)
  | Load of reg * reg * int  (* 从内存加载 *)
  | Mv of reg * reg          (* 寄存器移动 *)

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
  mutable var_offset: (string, int) Hashtbl.t; (* 变量名 -> 栈偏移 *)
  mutable stack_size: int;                     (* 当前栈大小 *)
  mutable loop_labels: (string * string) list; (* 循环标签栈 *)
  mutable reg_cache: (string, reg) Hashtbl.t;  (* 变量名 -> 寄存器，用于缓存变量值 *)
  mutable const_expr_cache: (Ast.expr, reg) Hashtbl.t; (* 表达式 -> 寄存器，用于缓存常量表达式 *)
  mutable current_code: ir_instr list;         (* 累积IR指令 (逆序) *)
}

let initial_state () =
  {
    temp_counter = 0;
    label_counter = 0;
    var_offset = Hashtbl.create 32;
    stack_size = 0;
    loop_labels = [];
    reg_cache = Hashtbl.create 32;
    const_expr_cache = Hashtbl.create 32;
    current_code = [];
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

(* 获取变量在栈上的偏移量，并确保8字节对齐 *)
let get_var_offset state var =
  try Hashtbl.find state.var_offset var
  with Not_found ->
    (* 变量分配时，8字节对齐 *)
    let offset = (state.stack_size + 7) land (lnot 7) in
    Hashtbl.add state.var_offset var offset;
    state.stack_size <- offset + 8;
    offset

(* O(1) 指令添加 *)
let emit state instr =
  state.current_code <- instr :: state.current_code

(* ==================== 立即数范围处理和常量折叠 ==================== *)

(* emit_imm_load 确保立即数加载指令的正确性 *)
let emit_imm_load state reg n =
  (* RISC-V的addi立即数范围是[-2048, 2047] *)
  if n >= -2048 && n <= 2047 then
    emit state (Li (reg, n))
  else
    (* 处理大立即数：使用LUI加载高20位，ADDImm加载低12位。
       LUI指令加载高20位到寄存器，并清零低12位。
       ADDI指令将寄存器内容与一个符号扩展的12位立即数相加。
       为了正确处理，我们需要根据低12位是否为负数来调整LUI的高20位。
       (n + 0x800) lsr 12 的目的是当n的低12位是负数时，给高位“进1”，使得低12位可以被正确表示为负数。
    *)
    let high_bits = (n + 0x800) lsr 12 in (* 计算高20位，考虑ADDI的符号扩展 *)
    let low_bits = n - (high_bits lsl 12) in (* 重新计算精确的低12位 *)

    emit state (Lui (reg, high_bits));
    if low_bits <> 0 then (* 只有低12位不为0才需要addi *)
      emit state (Addi (reg, reg, low_bits))

(* 表达式值范围分析（用于常量折叠） *)
type value_range =
  | Unknown
  | Constant of int
  | Bounded of int * int  (* min, max *)

let rec expr_range expr =
  match expr with
  | Num n -> Constant n
  | Var _ -> Unknown (* 变量值在编译时通常未知 *)
  | Binary (op, e1, e2) ->
      let r1 = expr_range e1 in
      let r2 = expr_range e2 in

      (* 常量折叠优化 *)
      (match (r1, r2) with
      | (Constant n1, Constant n2) ->
          (match op with
            | Add -> Constant (n1 + n2)
            | Sub -> Constant (n1 - n2)
            | Mul -> Constant (n1 * n2)
            | Div when n2 <> 0 -> Constant (n1 / n2)
            | Mod when n2 <> 0 -> Constant (n1 mod n2)
            | Lt -> Constant (if n1 < n2 then 1 else 0)
            | Gt -> Constant (if n1 > n2 then 1 else 0)
            | Leq -> Constant (if n1 <= n2 then 1 else 0)
            | Geq -> Constant (if n1 >= n2 then 1 else 0)
            | Eq -> Constant (if n1 = n2 then 1 else 0)
            | Neq -> Constant (if n1 <> n2 then 1 else 0)
            | And -> Constant (if n1 <> 0 && n2 <> 0 then 1 else 0)
            | Or -> Constant (if n1 <> 0 || n2 <> 0 then 1 else 0)
            | _ -> Unknown) (* 无法折叠的运算符 *)
      | _ -> Unknown) (* 至少一个不是常量，无法常量折叠 *)
  | _ -> Unknown (* 其他表达式类型，如函数调用等，值范围未知 *)


(* ==================== 优化的AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  (* 尝试从常量表达式缓存中获取 *)
  match Hashtbl.find_opt state.const_expr_cache expr with
  | Some reg -> reg
  | None ->
      let result_reg =
        match expr with
        | Num n ->
            let temp = fresh_temp state in
            if n = 0 then
              emit state (Mv (temp, RiscvReg "x0")) (* x0是硬编码的零寄存器 *)
            else
              emit_imm_load state temp n;
            temp

        | Var x ->
            (* 尝试从寄存器缓存中获取变量值 *)
            (match Hashtbl.find_opt state.reg_cache x with
            | Some reg -> reg
            | None ->
                let offset = get_var_offset state x in
                let temp = fresh_temp state in
                (* 内存访问：考虑大偏移量 *)
                if offset >= -2048 && offset <= 2047 then
                  emit state (Load (temp, RiscvReg "sp", offset))
                else begin
                  let offset_reg = fresh_temp state in
                  emit_imm_load state offset_reg offset; (* 加载完整的偏移量 *)
                  let addr_reg = fresh_temp state in
                  emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg)); (* sp + offset_reg *)
                  emit state (Load (temp, addr_reg, 0)); (* 从计算出的地址加载，偏移量为0 *)
                end;
                Hashtbl.add state.reg_cache x temp; (* 缓存变量值到寄存器 *)
                temp)

        | Binary (op, e1, e2) ->
            (* 尝试常量折叠 *)
            (match expr_range expr with
            | Constant n ->
                expr_to_ir state (Num n) (* 折叠后重新处理为Num *)
            | _ ->
                (* 未折叠，按常规处理 *)
                let e1_reg = expr_to_ir state e1 in
                let e2_reg = expr_to_ir state e2 in
                let temp = fresh_temp state in
                let op_str = match op with
                  | Add -> "add" | Sub -> "sub" | Mul -> "mul"
                  | Div -> "div" | Mod -> "rem" | Lt -> "slt"
                  | Gt -> "sgt" | Leq -> "sle" (* slt + xor + xori *)
                  | Geq -> "sge" (* slt + xor + xori *)
                  | Eq -> "seq" (* xor + sltu + xori *)
                  | Neq -> "sne" (* xor + sltu *)
                  | And -> "and"
                  | Or -> "or"
                in
                emit state (BinaryOp (op_str, temp, e1_reg, e2_reg));
                temp)
        | _ -> failwith "Unsupported expression type"
      in
      Hashtbl.add state.const_expr_cache expr result_reg; (* 缓存表达式结果 *)
      result_reg

(* ==================== 语句处理优化 ==================== *)
let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b ->
      (* 进入新块时，清空变量寄存器缓存，因为寄存器可能被复用，或者块内的声明会改变语义 *)
      Hashtbl.clear state.reg_cache;
      List.iter (fun s -> stmt_to_ir state s) b.stmts
      (* 离开块时，不需要恢复旧的reg_cache，因为新块的生命周期结束了 *)

  | DeclStmt (_, name, Some expr) ->
      let expr_reg = expr_to_ir state expr in
      let offset = get_var_offset state name in
      if offset >= -2048 && offset <= 2047 then
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      else begin
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset;
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
        emit state (Store (expr_reg, addr_reg, 0))
      end;
      Hashtbl.remove state.reg_cache name (* 变量被重新赋值，其在寄存器中的旧值可能失效 *)

  | DeclStmt (_, name, None) ->
      ignore (get_var_offset state name) (* 只是分配空间 *)

  | AssignStmt (name, expr) ->
      let expr_reg = expr_to_ir state expr in
      (* 确保变量已分配空间 *)
      let offset = get_var_offset state name in
      if offset >= -2048 && offset <= 2047 then
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      else begin
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset;
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
        emit state (Store (expr_reg, addr_reg, 0))
      end;
      Hashtbl.remove state.reg_cache name (* 变量被重新赋值，其在寄存器中的旧值失效 *)

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
      ignore (expr_to_ir state expr) (* 生成表达式代码但忽略结果 *)

  | WhileStmt (cond, body) ->
      let start_label = fresh_label state "while_start" in
      let cond_label = fresh_label state "while_cond" in
      let end_label = fresh_label state "while_end" in

      state.loop_labels <- (end_label, cond_label) :: state.loop_labels;

      emit state (Jmp cond_label); (* 首次跳转到条件检查 *)
      emit state (Label start_label);
      stmt_to_ir state body;

      emit state (Label cond_label);
      let cond_reg = expr_to_ir state cond in
      emit state (Branch ("bnez", cond_reg, RiscvReg "zero", start_label)); (* 如果条件为真，跳转回循环体 *)

      emit state (Label end_label);
      state.loop_labels <- List.tl state.loop_labels

  | BreakStmt ->
      (match state.loop_labels with
      | (end_label, _) :: _ -> emit state (Jmp end_label)
      | [] -> ()) (* 忽略函数外的break，或者可以抛出错误 *)

  | ContinueStmt ->
      (match state.loop_labels with
      | (_, loop_label) :: _ -> emit state (Jmp loop_label)
      | [] -> ()) (* 忽略函数外的continue，或者可以抛出错误 *)

  | EmptyStmt -> () (* 忽略空语句 *)

(* ==================== 函数级别的优化（Peephole） ==================== *)
let optimize_basic_block (instrs: ir_instr list) =
  let rec peephole_pass acc = function
    | (Mv (r_dest, r_src)) :: rest when r_dest = r_src ->
        peephole_pass acc rest (* 消除 mv t0, t0 *)
    | (Addi (r_dest, r_src, 0)) :: rest when r_dest = r_src ->
        peephole_pass acc rest (* 消除 addi x, x, 0 *)
    | (Load (r1, base1, off1)) :: (Store (r2, base2, off2)) :: rest
      when r1 = r2 && base1 = base2 && off1 = off2 ->
        peephole_pass acc rest (* 消除冗余的Load-Store对，如果值没有被使用 *)
    (* 可以添加更多peephole规则 *)
    | i :: rest -> peephole_pass (i :: acc) rest
    | [] -> List.rev acc
  in
  peephole_pass [] instrs

(* ==================== 函数处理优化 ==================== *)
let func_to_ir (func : Ast.func_def) : ir_func =
  let state = initial_state () in

  (* 参数在栈上的空间分配。注意：RISC-V通常前8个参数在寄存器中。
     这里简单地假设它们在栈上，或者后续通过Load/Store进行spill/restore。
     为了简化，我们为参数分配栈空间，并将其视为局部变量。
     实际编译器会有更复杂的参数传递约定处理。
  *)
  List.iteri (fun i (p : Ast.param) ->
    (* 在RISC-V中，参数通常从a0-a7寄存器传入。如果参数多于8个或需要存储，才会放到栈上。
       此处简化处理，假设所有参数都可能需要栈空间。
       一个更完整的编译器会在函数入口处，将a0-a7的值存储到栈上对应的位置。
       但由于目前没有实现寄存器分配，我们只是为它们预留栈空间。
       参数的偏移量应该从sp + 栈帧大小开始，而不是从0开始。
       这里 `get_var_offset` 适用于局部变量和需要栈空间的参数。
       后续可以考虑如何处理 `a0-a7` 的参数传入。
    *)
    ignore (get_var_offset state p.name);
  ) func.params;

  (* 生成函数体IR *)
  stmt_to_ir state (Ast.BlockStmt func.body); (* 传递整个block *)

  (* 16字节栈对齐 *)
  let aligned_stack_size =
    if state.stack_size > 0 then
      ((state.stack_size + 15) / 16) * 16
    else 0
  in

  let ir_body = List.rev state.current_code in (* 反转以获得正确指令顺序 *)
  let optimized_body = optimize_basic_block ir_body in (* 应用基本块优化 *)

  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = optimized_body;
    stack_size = aligned_stack_size;
  }

(* ==================== 高效的IR输出 ==================== *)
let string_of_reg = function
  | RiscvReg s -> s
  | Temp i -> Printf.sprintf "t%d" i

(* 确保 string_of_ir_instr 只格式化单条IR指令 *)
let string_of_ir_instr = function
  | Li (r, n) -> Printf.sprintf "li %s, %d" (string_of_reg r) n
  | Lui (r, n) -> Printf.sprintf "lui %s, %d" (string_of_reg r) n
  | Addi (rd, rs1, imm) -> Printf.sprintf "addi %s, %s, %d" (string_of_reg rd) (string_of_reg rs1) imm
  | BinaryOp (op, rd, rs1, rs2) -> Printf.sprintf "%s %s, %s, %s" op (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
  | Branch (op, r1, r2, label) -> Printf.sprintf "%s %s, %s, %s" op (string_of_reg r1) (string_of_reg r2) label
  | Jmp label -> Printf.sprintf "j %s" label
  | Label s -> s ^ ":"
  | Call f -> Printf.sprintf "call %s" f
  | Ret -> "ret"
  | Store (r, base, off) -> Printf.sprintf "sd %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Load (r, base, off) -> Printf.sprintf "ld %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Mv (rd, rs) -> Printf.sprintf "mv %s, %s" (string_of_reg rd) (string_of_reg rs)


let string_of_ir_func f =
  let buffer = Buffer.create 1024 in
  Buffer.add_string buffer (Printf.sprintf ".global %s\n" f.name);
  Buffer.add_string buffer (Printf.sprintf "%s:\n" f.name);

  (* Function Prologue *)
  (* Save ra (return address) and s0 (frame pointer) if used *)
  (* For simplicity, we just adjust sp for stack_size *)
  if f.stack_size > 0 then begin
    Buffer.add_string buffer (Printf.sprintf "  addi sp, sp, -%d\n" f.stack_size);
    (* 可以根据需要在这里添加 ra 和 s0 的保存/恢复逻辑，例如：
       Buffer.add_string buffer (Printf.sprintf "  sd ra, %d(sp)\n" (f.stack_size - 8));
       Buffer.add_string buffer (Printf.sprintf "  sd s0, %d(sp)\n" (f.stack_size - 16));
       Buffer.add_string buffer "  addi s0, sp, 0\n";
    *)
  end;

  (* Function Body *)
  List.iter (fun instr ->
    Buffer.add_string buffer "  "; (* 缩进 *)
    Buffer.add_string buffer (string_of_ir_instr instr);
    Buffer.add_char buffer '\n'
  ) f.body;

  (* Function Epilogue *)
  if f.stack_size > 0 then begin
    (* 可以根据需要在这里添加 ra 和 s0 的保存/恢复逻辑，例如：
       Buffer.add_string buffer (Printf.sprintf "  ld ra, %d(sp)\n" (f.stack_size - 8));
       Buffer.add_string buffer (Printf.sprintf "  ld s0, %d(sp)\n" (f.stack_size - 16));
    *)
    Buffer.add_string buffer (Printf.sprintf "  addi sp, sp, %d\n" f.stack_size);
  end;

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
    (* string_of_ir_func 已经包含了函数名Label，这里不再重复输出 *)
    output_string out_ch (string_of_ir_func f);
    output_string out_ch "\n" (* 在函数之间添加一个空行，增加可读性 *)
  ) ir;
  close_out out_ch;

  print_endline "Compilation successful!";
  print_endline "Optimized RISC-V assembly written to risc-V.s"