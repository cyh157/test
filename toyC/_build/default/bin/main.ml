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
  stack_size: int; (* Added stack_size to ir_func for easier access in string_of_ir_func *)
}

(* ==================== 代码生成状态 ==================== *)
type codegen_state = {
  mutable temp_counter: int;
  mutable label_counter: int;
  mutable var_offset: (string, int) Hashtbl.t; (* Mutable for efficiency *)
  mutable stack_size: int;                     (* Mutable for efficiency *)
  mutable loop_labels: (string * string) list; (* Mutable for efficiency *)
  mutable reg_cache: (string, reg) Hashtbl.t;  (* Mutable for efficiency *)
  mutable const_values: (expr, reg) Hashtbl.t; (* Mutable for efficiency *)
  mutable current_code: ir_instr list;         (* Accumulate code incrementally (in reverse order) *)
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
  reg_cache = Hashtbl.create 10;
  const_values = Hashtbl.create 10;
  current_code = [];
}

(* ==================== 辅助函数 ==================== *)
let fresh_temp state =
  let temp = state.temp_counter in
  state.temp_counter <- temp + 1;
  Temp temp

let fresh_label state prefix =
  let label = Printf.sprintf "%s%d" prefix state.label_counter in
  state.label_counter <- state.label_counter + 1;
  label

let get_var_offset state var =
  try
    Hashtbl.find state.var_offset var
  with Not_found ->
    let offset = state.stack_size in
    Hashtbl.add state.var_offset var offset;
    state.stack_size <- offset + 8; (* Assuming 8 bytes per variable *)
    offset

(* 优化：使用 cons 操作符在列表头部添加，最后反转 *)
let emit state instr =
  state.current_code <- instr :: state.current_code

let emit_many state instrs =
  state.current_code <- (List.rev instrs) @ state.current_code

(* ==================== 立即数处理终极解决方案 ==================== *)
let emit_imm_load state reg n =
  if n >= -2048 && n <= 2047 then
    emit state (Li (reg, n))
  else
    (* RISC-V的LUI加载高20位，ADDImm加载低12位，ADDImm有符号扩展。
       因此，如果低12位是负数，我们需要对高20位进行调整。 *)
    let high = (n lsr 12) in
    let low = n land 0xFFF in
    if low >= 0x800 then begin (* 如果低12位表示的是负数，例如 0xFFF = -1 *)
      emit state (Lui (reg, high + 1));
      emit state (Addi (reg, reg, low - 0x1000)); (* 将低12位调整为负数 *)
    end else begin
      emit state (Lui (reg, high));
      emit state (Addi (reg, reg, low));
    end

(* ==================== 表达式值范围分析 ==================== *)
type value_range =
  | Unknown
  | Constant of int
  | Bounded of int * int  (* min, max *)

let rec expr_range expr env =
  match expr with
  | Num n -> Constant n
  | Var x ->
      (try Hashtbl.find env x
        with Not_found -> Unknown)
  | Binary (op, e1, e2) ->
      let r1 = expr_range e1 env in
      let r2 = expr_range e2 env in

      (* 常量折叠优化 *)
      (match (r1, r2) with
      | (Constant n1, Constant n2) ->
          (match op with
            | Add -> Constant (n1 + n2)
            | Sub -> Constant (n1 - n2)
            | Mul -> Constant (n1 * n2)
            | Div when n2 <> 0 -> Constant (n1 / n2)
            | Mod when n2 <> 0 -> Constant (n1 mod n2)
            | _ -> Unknown)
      | (Bounded (min1, max1), Bounded (min2, max2)) ->
          (match op with
            | Add -> Bounded (min1 + min2, max1 + max2)
            | Sub -> Bounded (min1 - max2, max1 - min2)
            | Mul ->
                let vals = [min1*min2; min1*max2; max1*min2; max1*max2] in
                Bounded (List.fold_left min (List.hd vals) vals,
                         List.fold_left max (List.hd vals) vals)
            | _ -> Unknown)
      | _ -> Unknown)
  | _ -> Unknown

(* ==================== AST到IR转换（最终优化版） ==================== *)
let rec expr_to_ir state expr env =
  (* 尝试从常量缓存中获取 *)
  match Hashtbl.find_opt state.const_values expr with
  | Some reg -> reg
  | None ->
      match expr with
      | Num n ->
          let temp = fresh_temp state in
          emit_imm_load state temp n;
          Hashtbl.add state.const_values expr temp; (* 缓存常量值 *)
          temp

      | Var x ->
          (* 尝试从寄存器缓存中获取 *)
          (match Hashtbl.find_opt state.reg_cache x with
          | Some reg -> reg
          | None ->
              let offset = get_var_offset state x in
              let temp = fresh_temp state in
              (* 如果偏移量超出 addi 的立即数范围，需要多条指令来计算地址 *)
              if offset >= -2048 && offset <= 2047 then begin
                emit state (Load (temp, RiscvReg "sp", offset))
              end else begin
                let offset_reg = fresh_temp state in
                emit_imm_load state offset_reg offset; (* 加载完整的偏移量 *)
                let addr_reg = fresh_temp state in
                emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg)); (* sp + offset_reg *)
                emit state (Load (temp, addr_reg, 0)); (* 从计算出的地址加载，偏移量为0 *)
              end;
              Hashtbl.add state.reg_cache x temp;
              temp)

      | Binary (op, e1, e2) ->
          (* 值范围分析 *)
          let range = expr_range expr env in

          (* 基于范围分析进行优化 *)
          (match range with
          | Constant n ->
              expr_to_ir state (Num n) env (* 常量折叠后直接处理为 Num *)
          | _ -> (* Bounded 或 Unknown, 按通用方式处理 *)
              let e1_reg = expr_to_ir state e1 env in
              let e2_reg = expr_to_ir state e2 env in
              let temp = fresh_temp state in
              let op_str = match op with
                | Add -> "add" | Sub -> "sub" | Mul -> "mul"
                | Div -> "div" | Mod -> "rem" | Lt -> "slt"
                | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
                | Eq -> "seq" | Neq -> "sne" | And -> "and"
                | Or -> "or" in
              emit state (BinaryOp (op_str, temp, e1_reg, e2_reg));
              temp)

      | _ -> failwith "Unsupported expression"

(* ==================== 基本块优化 ==================== *)
let optimize_basic_block (instrs: ir_instr list) =
  let rec merge_imm_loads acc = function
    | (Li (r1, n1))::(Li (r2, n2))::rest when n1 = n2 ->
        merge_imm_loads (Mv (r2, r1)::acc) rest
    | i::rest -> merge_imm_loads (i::acc) rest
    | [] -> List.rev acc
  in

  let rec remove_redundant_stores acc = function
    | (Store (r1, base, off1))::(Load (r2, base2, off2))::rest
        when r1 = r2 && base = base2 && off1 = off2 ->
        remove_redundant_stores acc rest
    | i::rest -> remove_redundant_stores (i::acc) rest
    | [] -> List.rev acc
  in

  let rec remove_redundant_moves acc = function
    | (Mv (r1, r2))::(Mv (r3, r4))::rest when r1 = r4 && r2 = r3 ->
        (* 消除冗余的交换操作，例如 mv a, b; mv b, a *)
        remove_redundant_moves acc rest
    | (Mv (r_dest, r_src)) :: rest when r_dest = r_src ->
        (* 消除自身移动，例如 mv t0, t0 *)
        remove_redundant_moves acc rest
    | i :: rest -> remove_redundant_moves (i :: acc) rest
    | [] -> List.rev acc
  in

  let rec peephole_optimize acc = function
    | (Addi (r_dest, r_src, 0)) :: rest when r_dest = r_src ->
        peephole_optimize acc rest (* 移除 addi x, x, 0 *)
    | i :: rest -> peephole_optimize (i :: acc) rest
    | [] -> List.rev acc
  in
  instrs
  |> merge_imm_loads []
  |> remove_redundant_stores []
  |> remove_redundant_moves []
  |> peephole_optimize []

let rec stmt_to_ir state stmt env =
  match stmt with
  | BlockStmt b -> block_to_ir state b env

  | DeclStmt (_, name, Some expr) ->
      let expr_reg = expr_to_ir state expr env in
      let offset = get_var_offset state name in
      (* 如果偏移量超出 addi 的立即数范围，需要多条指令来计算地址 *)
      if offset >= -2048 && offset <= 2047 then begin
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      end else begin
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset; (* 加载完整的偏移量 *)
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg)); (* sp + offset_reg *)
        emit state (Store (expr_reg, addr_reg, 0)); (* 存储到计算出的地址，偏移量为0 *)
      end

  | DeclStmt (_, name, None) ->
      let _ = get_var_offset state name in (* Just ensure offset is allocated *)
      ()

  | AssignStmt (name, expr) ->
      let expr_reg = expr_to_ir state expr env in
      let offset = get_var_offset state name in
      (* 如果偏移量超出 addi 的立即数范围，需要多条指令来计算地址 *)
      if offset >= -2048 && offset <= 2047 then begin
        emit state (Store (expr_reg, RiscvReg "sp", offset))
      end else begin
        let offset_reg = fresh_temp state in
        emit_imm_load state offset_reg offset; (* 加载完整的偏移量 *)
        let addr_reg = fresh_temp state in
        emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg)); (* sp + offset_reg *)
        emit state (Store (expr_reg, addr_reg, 0)); (* 存储到计算出的地址，偏移量为0 *)
      end

  | IfStmt (cond, then_stmt, else_stmt) ->
      let cond_reg = expr_to_ir state cond env in
      let then_label = fresh_label state "then" in
      let else_label = fresh_label state "else" in
      let merge_label = fresh_label state "merge" in

      emit state (Branch ("bnez", cond_reg, RiscvReg "zero", then_label));
      emit state (Jmp else_label);
      emit state (Label then_label);
      stmt_to_ir state then_stmt env;
      emit state (Jmp merge_label);
      emit state (Label else_label);
      (match else_stmt with
      | Some s -> stmt_to_ir state s env
      | None -> ());
      emit state (Label merge_label)

  | ReturnStmt (Some expr) ->
      let expr_reg = expr_to_ir state expr env in
      emit state (Mv (RiscvReg "a0", expr_reg));
      emit state Ret

  | ReturnStmt None ->
      emit state Ret

  | ExprStmt expr ->
      let _ = expr_to_ir state expr env in
      () (* The IR instructions are already emitted *)

  | WhileStmt (cond, body) ->
      let loop_label = fresh_label state "loop" in
      let end_label = fresh_label state "end" in
      let cond_label = fresh_label state "cond" in

      state.loop_labels <- (end_label, cond_label) :: state.loop_labels;

      emit state (Label cond_label);
      let cond_reg = expr_to_ir state cond env in
      emit state (Branch ("beqz", cond_reg, RiscvReg "zero", end_label));
      stmt_to_ir state body env;
      emit state (Jmp cond_label);
      emit state (Label end_label);

      state.loop_labels <- List.tl state.loop_labels

  | BreakStmt ->
      (match state.loop_labels with
      | (end_label, _) :: _ -> emit state (Jmp end_label)
      | [] -> failwith "break statement outside loop")

  | ContinueStmt ->
      (match state.loop_labels with
      | (_, loop_label) :: _ -> emit state (Jmp loop_label)
      | [] -> failwith "continue statement outside loop")

  | EmptyStmt ->
      ()

and block_to_ir state block env =
  let new_env = Hashtbl.copy env in
  List.iter (fun stmt -> stmt_to_ir state stmt new_env) block.stmts

(* ==================== 函数级别的优化 ==================== *)
let optimize_function ir_func =
  let optimized_body = optimize_basic_block ir_func.body in
  { ir_func with body = optimized_body }

let func_to_ir (func : Ast.func_def) : ir_func =
  let state = {
    initial_state with
    var_offset = Hashtbl.create (List.length func.params * 2); (* Better initial size *)
    reg_cache = Hashtbl.create (List.length func.params);
    const_values = Hashtbl.create 10;
    temp_counter = 0; (* Reset for each function *)
    label_counter = 0; (* Reset for each function *)
    stack_size = 0; (* Reset for each function *)
    current_code = []; (* Reset for each function *)
    loop_labels = []; (* Reset for each function *)
  } in
  let env = Hashtbl.create 10 in

  (* Add parameters to environment and allocate stack space *)
  List.iteri (fun i (p : Ast.param) ->
    Hashtbl.add env p.name (Bounded (-2147483648, 2147483647));
    (* Call get_var_offset to ensure stack space is allocated for parameters *)
    let _ = get_var_offset state p.name in
    ()
  ) func.params;

  block_to_ir state func.body env;

  (* 确保栈大小是 16 字节对齐 *)
  let aligned_stack_size =
    let align = 16 in
    ((state.stack_size + align - 1) / align) * align
  in

  let result = {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = List.rev state.current_code; (* 反转列表以获得正确的指令顺序 *)
    stack_size = aligned_stack_size; (* Get the final aligned stack size *)
  } in
  optimize_function result

(* ==================== 其他保持不变的部分 ==================== *)

let string_of_reg = function
  | RiscvReg s -> s
  | Temp i -> Printf.sprintf "t%d" i (* Temporary registers mapped to RISC-V t0-t6, s0-s11 etc. *)

let string_of_ir_instr = function
  | Li (r, n) -> Printf.sprintf "li %s, %d" (string_of_reg r) n
  | Lui (r, n) -> Printf.sprintf "lui %s, %d" (string_of_reg r) n
  | Addi (rd, rs1, imm) -> Printf.sprintf "addi %s, %s, %d" (string_of_reg rd) (string_of_reg rs1) imm
  | BinaryOp (op, rd, rs1, rs2) -> Printf.sprintf "%s %s, %s, %s" op (string_of_reg rd) (string_of_reg rs1) (string_of_reg rs2)
  | Branch (op, r1, r2, label) -> Printf.sprintf "%s %s, %s, %s" op (string_of_reg r1) (string_of_reg r2) label
  | Jmp label -> Printf.sprintf "j %s" label
  | Label s -> Printf.sprintf "%s:" s
  | Call f -> Printf.sprintf "call %s" f
  | Ret -> "ret"
  | Store (r, base, off) -> Printf.sprintf "sd %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Load (r, base, off) -> Printf.sprintf "ld %s, %d(%s)" (string_of_reg r) off (string_of_reg base)
  | Mv (rd, rs) -> Printf.sprintf "mv %s, %s" (string_of_reg rd) (string_of_reg rs)


let string_of_ir_func f =
  let body_str = String.concat "\n  " (List.map string_of_ir_instr f.body) in
  (* Adjust stack pointer only if stack_size is positive *)
  let prologue = if f.stack_size > 0 then Printf.sprintf "  addi sp, sp, -%d" f.stack_size else "" in
  let epilogue = if f.stack_size > 0 then Printf.sprintf "  addi sp, sp, %d" f.stack_size else "" in
  Printf.sprintf ".global %s\n%s:\n%s\n%s\n%s"
    f.name f.name prologue body_str epilogue


let () =
  let ch = open_in "test/04_while_break.tc" in
  let ast = ToyC_riscv_lib.Parser.prog ToyC_riscv_lib.Lexer.token (Lexing.from_channel ch) in
  close_in ch;
  ToyC_riscv_lib.Semantic_analysis.semantic_analysis ast;

  (* Output AST *)
  let ast_str = ToyC_riscv_lib.Ast_printer.string_of_ast ast in
  let out_ch = open_out "ast.txt" in
  Printf.fprintf out_ch "%s\n" ast_str;
  close_out out_ch;

  (* Generate IR and optimize *)
  let ir = List.map func_to_ir ast in

  (* Output IR *)
  let ir_out = open_out "risc-V.txt" in
  List.iter (fun f ->
    let s = string_of_ir_func f in
    Printf.fprintf ir_out "%s\n" s;
  ) ir;
  close_out ir_out;

  print_endline "Compilation successful!";
  print_endline "AST written to ast.txt";
  print_endline "Optimized RISC-V assembly written to risc-V.txt"