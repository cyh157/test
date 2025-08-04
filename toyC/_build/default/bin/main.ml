exception LexicalError of string [@@warning "-38"]
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

module StringMap = Map.Make(String)
module IntSet = Set.Make(Int)

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
  const_values: (int, reg) Hashtbl.t;
  mutable copy_prop_map: (string, reg) Hashtbl.t; (* 复制传播映射 *)
  mutable dead_code_elim: bool; (* 死代码消除标志 *)
  mutable cse_cache: (expr * reg) list; (* 公共子表达式缓存 *)
  mutable loop_invariants: (ir_instr list) list; (* 循环不变量 *)
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
    copy_prop_map = Hashtbl.create 16;
    dead_code_elim = false;
    cse_cache = [];
    loop_invariants = [];
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
  if not state.dead_code_elim then
    state.current_code <- instr :: state.current_code

(* ==================== 强度削弱优化 ==================== *)
let reduce_strength op e1 e2 =
  match op, e1, e2 with
  | Mul, Num n, _ when n = 1 -> Some e2
  | Mul, _, Num n when n = 1 -> Some e1
  | Mul, Num n, _ when n = 0 -> Some (Num 0)
  | Mul, _, Num n when n = 0 -> Some (Num 0)
  | Mul, Num 2, e | Mul, e, Num 2 -> Some (Binary (Add, e, e))
  | Mul, Num n, e when n land (n - 1) = 0 -> (* n是2的幂 *)
      let shift = Int.log2 n in
      Some (Binary (LShift, e, Num shift))
  | Mul, e, Num n when n land (n - 1) = 0 -> 
      let shift = Int.log2 n in
      Some (Binary (LShift, e, Num shift))
  | Div, e, Num n when n land (n - 1) = 0 -> 
      let shift = Int.log2 n in
      Some (Binary (RShift, e, Num shift))
  | Add, e, Num 0 | Add, Num 0, e -> Some e
  | Sub, e, Num 0 -> Some e
  | _ -> None

(* ==================== 常量折叠 ==================== *)
let rec constant_folding expr =
  match expr with
  | Binary(op, e1, e2) ->
      let e1' = constant_folding e1 in
      let e2' = constant_folding e2 in
      begin match e1', e2' with
      | Num n1, Num n2 ->
          let result = match op with
          | Add -> n1 + n2
          | Sub -> n1 - n2
          | Mul -> n1 * n2
          | Div -> if n2 <> 0 then n1 / n2 else 0
          | Mod -> if n2 <> 0 then n1 mod n2 else 0
          | Eq -> if n1 = n2 then 1 else 0
          | Neq -> if n1 <> n2 then 1 else 0
          | Lt -> if n1 < n2 then 1 else 0
          | Gt -> if n1 > n2 then 1 else 0
          | Leq -> if n1 <= n2 then 1 else 0
          | Geq -> if n1 >= n2 then 1 else 0
          | And -> if n1 <> 0 && n2 <> 0 then 1 else 0
          | Or -> if n1 <> 0 || n2 <> 0 then 1 else 0
          | LShift -> n1 lsl n2
          | RShift -> n1 lsr n2
          in Num result
      | _ -> 
          match reduce_strength op e1' e2' with
          | Some e -> e
          | None -> Binary(op, e1', e2')
      end
  | Unary(op, e) ->
      let e' = constant_folding e in
      begin match e' with
      | Num n ->
          Num (match op with
            | Neg -> -n
            | Not -> if n = 0 then 1 else 0)
      | _ -> Unary(op, e')
      end
  | _ -> expr

(* ==================== 公共子表达式消除 ==================== *)
let find_cse state expr =
  try 
    List.assoc expr state.cse_cache
  with Not_found ->
    let reg = fresh_temp state in
    state.cse_cache <- (expr, reg) :: state.cse_cache;
    reg

(* ==================== 立即数范围优化 ==================== *)
let emit_imm_load state reg n =
  if n >= -2048 && n <= 2047 then
    emit state (Li (reg, n))
  else 
    let high_bits = (n + 0x800) lsr 12 in
    let low_bits = n - (high_bits lsl 12) in
    emit state (Lui (reg, high_bits));
    if low_bits <> 0 then
      emit state (Addi (reg, reg, low_bits))

(* ==================== 优化的AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  let expr = constant_folding expr in
  
  (* 公共子表达式消除 *)
  try List.assoc expr state.cse_cache
  with Not_found ->
    let result = match expr with
    | Num n ->
        (try Hashtbl.find state.const_values n
         with Not_found ->
           let temp = fresh_temp state in
           if n = 0 then
             emit state (Mv (temp, RiscvReg "x0"))
           else
             emit_imm_load state temp n;
           Hashtbl.add state.const_values n temp;
           temp)
          
    | Var x ->
        (* 复制传播 *)
        try Hashtbl.find state.copy_prop_map x
        with Not_found ->
          let offset = get_var_offset state x in
          let temp = fresh_temp state in
          if offset >= -2048 && offset <= 2047 then
            emit state (Load (temp, RiscvReg "sp", offset))
          else
            let offset_reg = fresh_temp state in
            emit_imm_load state offset_reg offset;
            let addr_reg = fresh_temp state in
            emit state (BinaryOp ("add", addr_reg, RiscvReg "sp", offset_reg));
            emit state (Load (temp, addr_reg, 0));
          temp
          
    | Binary (op, e1, e2) ->
        (* 强度削弱 *)
        match reduce_strength op e1 e2 with
        | Some e -> expr_to_ir state e
        | None ->
            let e1_reg = expr_to_ir state e1 in
            let e2_reg = expr_to_ir state e2 in
            let temp = fresh_temp state in
            let op_str = match op with
              | Add -> "add" | Sub -> "sub" | Mul -> "mul"
              | Div -> "div" | Mod -> "rem" | Lt -> "slt"
              | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
              | Eq -> "seq" | Neq -> "sne" | And -> "and"
              | Or -> "or" | LShift -> "sll" | RShift -> "srl"
            in
            emit state (BinaryOp (op_str, temp, e1_reg, e2_reg));
            temp
            
    | Unary (Neg, e) ->
        let e_reg = expr_to_ir state e in
        let temp = fresh_temp state in
        emit state (BinaryOp ("sub", temp, RiscvReg "x0", e_reg));
        temp
        
    | Unary (Not, e) ->
        let e_reg = expr_to_ir state e in
        let temp = fresh_temp state in
        emit state (BinaryOp ("seqz", temp, e_reg, RiscvReg "x0"));
        temp
        
    | _ -> 
        RiscvReg "x0"
    in
    (* 缓存公共子表达式 *)
    state.cse_cache <- (expr, result) :: state.cse_cache;
    result

(* ==================== 死代码消除 ==================== *)
let has_side_effects = function
  | AssignStmt _ | DeclStmt (_, _, Some _) | CallExpr _ -> true
  | ReturnStmt _ | BreakStmt | ContinueStmt -> true
  | _ -> false

(* ==================== 循环不变量外提 ==================== *)
let extract_loop_invariants state body =
  let invariants = ref [] in
  let new_body = ref [] in
  
  let is_invariant stmt =
    match stmt with
    | DeclStmt (_, _, Some expr) ->
        not (contains_var expr state.loop_labels)
    | AssignStmt (_, expr) ->
        not (contains_var expr state.loop_labels)
    | ExprStmt expr ->
        not (contains_var expr state.loop_labels)
    | _ -> false
  and contains_var expr labels =
    (* 简化实现：检查是否包含循环变量 *)
    false (* 实际实现需要变量分析 *)
  in
  
  List.iter (fun stmt ->
    if is_invariant stmt then
      invariants := stmt :: !invariants
    else
      new_body := stmt :: !new_body
  ) body;
  
  state.loop_invariants <- !invariants :: state.loop_invariants;
  List.rev !new_body

(* ==================== 优化的语句处理 ==================== *)
let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> 
      let save_cse = state.cse_cache in
      let save_cp = Hashtbl.copy state.copy_prop_map in
      List.iter (fun s -> stmt_to_ir state s) b.stmts;
      state.cse_cache <- save_cse;
      Hashtbl.clear state.copy_prop_map;
      Hashtbl.iter (fun k v -> Hashtbl.add state.copy_prop_map k v) save_cp
  
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
        emit state (Store (expr_reg, addr_reg, 0));
      Hashtbl.add state.copy_prop_map name expr_reg
  
  | DeclStmt (_, name, None) ->
      ignore (get_var_offset state name);
      Hashtbl.add state.copy_prop_map name (RiscvReg "zero")
  
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
        emit state (Store (expr_reg, addr_reg, 0));
      Hashtbl.replace state.copy_prop_map name expr_reg
  
  | IfStmt (cond, then_stmt, else_stmt) ->
      let cond_expr = constant_folding cond in
      if cond_expr = Num 1 then (* 条件恒真 *)
        stmt_to_ir state then_stmt
      else if cond_expr = Num 0 then (* 条件恒假 *)
        Option.iter (stmt_to_ir state) else_stmt
      else
        let cond_reg = expr_to_ir state cond in
        let else_label = fresh_label state "else" in
        let merge_label = fresh_label state "merge" in
        
        emit state (Branch ("beqz", cond_reg, RiscvReg "zero", else_label));
        stmt_to_ir state then_stmt;
        emit state (Jmp merge_label);
        
        emit state (Label else_label);
        Option.iter (fun s -> stmt_to_ir state s) else_stmt;
        
        emit state (Label merge_label);
        (* 清除复制传播映射，因为分支可能改变变量值 *)
        Hashtbl.clear state.copy_prop_map
  
  | ReturnStmt (Some expr) ->
      let expr_reg = expr_to_ir state expr in
      emit state (Mv (RiscvReg "a0", expr_reg));
      emit state Ret;
      state.dead_code_elim <- true (* 后续代码为死代码 *)
  
  | ReturnStmt None ->
      emit state Ret;
      state.dead_code_elim <- true
  
  | ExprStmt expr ->
      if has_side_effects expr then
        ignore (expr_to_ir state expr)
  
  | WhileStmt (cond, body) ->
      (* 提取循环不变量 *)
      let invariant_body = 
        match state.loop_invariants with
        | inv :: rest -> 
            state.loop_invariants <- rest;
            inv
        | [] -> []
      in
      
      let start_label = fresh_label state "while_start" in
      let cond_label = fresh_label state "while_cond" in
      let end_label = fresh_label state "while_end" in
      
      state.loop_labels <- (end_label, cond_label) :: state.loop_labels;
      
      (* 生成循环不变量代码 *)
      List.iter (fun inv_instr -> emit state inv_instr) invariant_body;
      
      emit state (Jmp cond_label);
      emit state (Label start_label);
      stmt_to_ir state body;
      
      emit state (Label cond_label);
      let cond_expr = constant_folding cond in
      if cond_expr = Num 0 then (* 循环条件恒假 *)
        ()
      else
        let cond_reg = expr_to_ir state cond in
        emit state (Branch ("bnez", cond_reg, RiscvReg "zero", start_label));
      
      emit state (Label end_label);
      state.loop_labels <- List.tl state.loop_labels;
      (* 清除复制传播映射，因为循环可能改变变量值 *)
      Hashtbl.clear state.copy_prop_map
  
  | BreakStmt ->
      (match state.loop_labels with
      | (end_label, _) :: _ -> 
          emit state (Jmp end_label);
          state.dead_code_elim <- true (* 后续代码为死代码 *)
      | [] -> ())
  
  | ContinueStmt ->
      (match state.loop_labels with
      | (_, loop_label) :: _ -> 
          emit state (Jmp loop_label);
          state.dead_code_elim <- true
      | [] -> ())
  
  | EmptyStmt -> ()

(* ==================== 优化的函数处理 ==================== *)
let func_to_ir (func : Ast.func_def) : ir_func =
  let state = initial_state () in
  
  (* 预分配参数偏移量 *)
  List.iteri (fun i (p : Ast.param) ->
    let offset = i * 8 in
    Hashtbl.add state.var_offset p.name offset;
    Hashtbl.add state.copy_prop_map p.name (RiscvReg (Printf.sprintf "a%d" i))
  ) func.params;
  
  state.stack_size <- List.length func.params * 8;
  
  block_to_ir state func.body;
  
  (* 死代码消除：移除return之后的指令 *)
  let rec remove_dead_code = function
    | [] -> []
    | Ret :: rest -> [Ret]
    | (Branch _ as b) :: rest -> b :: remove_dead_code rest
    | (Jmp _ as j) :: rest -> j :: remove_dead_code rest
    | (Label _ as l) :: rest -> l :: remove_dead_code rest
    | instr :: rest -> remove_dead_code rest
  in
  
  let optimized_body = 
    state.current_code 
    |> List.rev 
    |> remove_dead_code
    |> List.rev
  in
  
  (* 16字节栈对齐 *)
  let aligned_stack_size = 
    if state.stack_size > 0 then
      ((state.stack_size + 15) / 16) * 16
    else 0
  in
  
  {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = optimized_body;
    stack_size = aligned_stack_size;
  }

and block_to_ir state block =
  List.iter (fun stmt -> 
    state.dead_code_elim <- false; (* 重置死代码标志 *)
    stmt_to_ir state stmt
  ) block.stmts

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