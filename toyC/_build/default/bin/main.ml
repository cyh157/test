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
type value_range =
  | Unknown
  | Constant of int
  | Bounded of int * int

type env_frame = {
  vr_map: (string, value_range) Hashtbl.t;
  next_frame: env_frame option;
}

type codegen_state = {
  temp_counter: int ref;
  label_counter: int ref;
  var_offset: (string, int) Hashtbl.t;
  stack_size: int ref;
  loop_labels: (string * string) list ref;
  const_values: (expr, reg) Hashtbl.t;
  current_code: ir_instr list ref;
  current_frame: env_frame ref;
}

(* ==================== 高效辅助函数 ==================== *)
let create_frame parent = {
  vr_map = Hashtbl.create 8;
  next_frame = parent;
}

let rec lookup_var frame name =
  try Hashtbl.find frame.vr_map name
  with Not_found ->
    match frame.next_frame with
    | Some parent -> lookup_var parent name
    | None -> Unknown

let initial_state () = 
  let root_frame = create_frame None in
  {
    temp_counter = ref 0;
    label_counter = ref 0;
    var_offset = Hashtbl.create 16;
    stack_size = ref 0;
    loop_labels = ref [];
    const_values = Hashtbl.create 16;
    current_code = ref [];
    current_frame = ref root_frame;
  }

let fresh_temp state =
  let counter = !(state.temp_counter) in
  state.temp_counter := counter + 1;
  Temp counter

let fresh_label state prefix =
  let counter = !(state.label_counter) in
  state.label_counter := counter + 1;
  Printf.sprintf "%s%d" prefix counter

let get_var_offset state var =
  try Hashtbl.find state.var_offset var
  with Not_found ->
    (* 直接对齐到8字节边界 *)
    let offset = (!(state.stack_size) + 7) land (lnot 7) in
    state.stack_size := offset + 8;
    Hashtbl.replace state.var_offset var offset;
    offset

let emit state instr =
  state.current_code := instr :: !(state.current_code)

(* 高效立即数处理 *)
let emit_imm_load state reg n =
  match n with
  | 0 -> emit state (Mv (reg, RiscvReg "x0"))
  | _ when n >= -2048 && n <= 2047 -> emit state (Li (reg, n))
  | _ -> 
      let low12 = n land 0xFFF in
      let adjusted_low = 
        if low12 >= 0x800 then low12 - 0x1000 
        else low12 in
      let high20 = (n - adjusted_low) lsr 12 in
      emit state (Lui (reg, high20));
      if adjusted_low <> 0 then
        emit state (Addi (reg, reg, adjusted_low))

(* ==================== 优化的AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  match Hashtbl.find_opt state.const_values expr with
  | Some reg -> reg
  | None ->
      match expr with
      | Num n ->
          let temp = fresh_temp state in
          if n = 0 then
            emit state (Mv (temp, RiscvReg "x0"))
          else
            emit_imm_load state temp n;
          Hashtbl.add state.const_values expr temp;
          temp

      | Var x ->
          let offset = get_var_offset state x in
          let temp = fresh_temp state in
          emit state (Load (temp, RiscvReg "sp", offset));
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
            | Or -> "or" | _ -> failwith "Unsupported operator" in
          emit state (BinaryOp (op_str, temp, e1_reg, e2_reg));
          temp

      | _ -> failwith "Unsupported expression"

let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> block_to_ir state b

  | DeclStmt (_, name, Some expr) ->
      let expr_reg = expr_to_ir state expr in
      let offset = get_var_offset state name in
      emit state (Store (expr_reg, RiscvReg "sp", offset))

  | DeclStmt (_, name, None) ->
      (* 仅分配空间，不生成代码 *)
      ignore (get_var_offset state name)

  | AssignStmt (name, expr) ->
      let expr_reg = expr_to_ir state expr in
      let offset = 
        try Hashtbl.find state.var_offset name 
        with Not_found -> get_var_offset state name in
      emit state (Store (expr_reg, RiscvReg "sp", offset))

  | IfStmt (cond, then_stmt, else_stmt) ->
      let cond_reg = expr_to_ir state cond in
      let else_label = fresh_label state "else" in
      let merge_label = fresh_label state "merge" in

      emit state (Branch ("beqz", cond_reg, RiscvReg "zero", else_label));
      stmt_to_ir state then_stmt;
      emit state (Jmp merge_label);
      
      emit state (Label else_label);
      (match else_stmt with
      | Some s -> stmt_to_ir state s
      | None -> ());
      
      emit state (Label merge_label)

  | ReturnStmt (Some expr) ->
      let expr_reg = expr_to_ir state expr in
      emit state (Mv (RiscvReg "a0", expr_reg));
      emit state Ret

  | ReturnStmt None ->
      emit state Ret

  | ExprStmt expr ->
      ignore (expr_to_ir state expr) (* 生成代码但忽略结果 *)

  | WhileStmt (cond, body) ->
      let cond_label = fresh_label state "cond" in
      let body_label = fresh_label state "body" in
      let end_label = fresh_label state "end" in

      state.loop_labels := (end_label, cond_label) :: !(state.loop_labels);
      
      emit state (Jmp cond_label);
      emit state (Label body_label);
      stmt_to_ir state body;
      
      emit state (Label cond_label);
      let cond_reg = expr_to_ir state cond in
      emit state (Branch ("bnez", cond_reg, RiscvReg "zero", body_label));
      
      emit state (Label end_label);
      state.loop_labels := List.tl !(state.loop_labels)

  | BreakStmt ->
      match !(state.loop_labels) with
      | (end_label, _) :: _ -> emit state (Jmp end_label)
      | [] -> failwith "break statement outside loop"

  | ContinueStmt ->
      match !(state.loop_labels) with
      | (_, loop_label) :: _ -> emit state (Jmp loop_label)
      | [] -> failwith "continue statement outside loop"

  | EmptyStmt -> ()

and block_to_ir state block =
  (* 创建新作用域帧 *)
  let new_frame = create_frame (Some !(state.current_frame)) in
  let old_frame = !(state.current_frame) in
  state.current_frame := new_frame;
  
  List.iter (fun stmt -> stmt_to_ir state stmt) block.stmts;
  
  (* 恢复作用域 *)
  state.current_frame := old_frame

(* ==================== 函数处理 ==================== *)
let func_to_ir (func : Ast.func_def) : ir_func =
  let state = initial_state () in
  
  (* 预分配参数偏移量 *)
  let param_offset i = i * 8 in
  List.iteri (fun i (p : Ast.param) ->
    let offset = param_offset i in
    Hashtbl.replace state.var_offset p.name offset;
    Hashtbl.replace (!(state.current_frame)).vr_map p.name Unknown;
  ) func.params;
  
  state.stack_size := List.length func.params * 8;
  
  block_to_ir state func.body;
  
  (* 16字节栈对齐 *)
  let aligned_stack_size = 
    if !(state.stack_size) = 0 then 0
    else ((!(state.stack_size) + 15) / 16) * 16 
  in
  
  {
    name = func.name;
    params = List.map (fun p -> p.name) func.params;
    body = List.rev !(state.current_code);
    stack_size = aligned_stack_size;
  }

(* ==================== 高效的IR输出 ==================== *)
let string_of_reg = function
  | RiscvReg s -> s
  | Temp i -> Printf.sprintf "t%d" i

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
  let buffer = Buffer.create 256 in
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
let compile ast =
  let state = initial_state () in
  List.map func_to_ir ast

let () =
  (* 示例用法 - 需要实际实现文件读取和解析 *)
  let ast = [] (* 这里应该是实际的AST *) in
  let ir = compile ast in
  
  (* 输出RISC-V汇编 *)
  let out = open_out "output.s" in
  List.iter (fun func ->
    Printf.fprintf out "%s\n" (string_of_ir_func func)
  ) ir;
  close_out out

  print_endline "Compilation successful!";
  print_endline "AST written to ast.txt";
  print_endline "Optimized RISC-V assembly written to risc-V.txt"