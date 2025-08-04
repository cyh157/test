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
  | Mv of reg * reg               (* 寄存器间移动 *)

type ir_func = {
  name: string;
  params: string list;
  body: ir_instr list;
}

(* ==================== 代码生成状态 ==================== *)
type codegen_state = {
  temp_counter: int;
  label_counter: int;
  var_offset: (string, int) Hashtbl.t; 
  stack_size: int;
  loop_labels: (string * string) list;
  reg_cache: (string, reg) Hashtbl.t; (* 寄存器分配缓存 *)
  const_cache: (int, reg) Hashtbl.t;   (* 常量值缓存 *)
  current_block: ir_instr list ref;    (* 当前基本块 *)
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
  reg_cache = Hashtbl.create 10;
  const_cache = Hashtbl.create 10;
  current_block = ref [];
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
    (Hashtbl.find state.var_offset var, state)
  with Not_found -> 
    let offset = state.stack_size in
    Hashtbl.add state.var_offset var offset;
    let new_state = {state with stack_size = offset + 8} in
    (offset, new_state)

(* ==================== 立即数处理终极解决方案 ==================== *)
let emit_imm_load reg n =
  if n >= -2048 && n <= 2047 then
    [Li (reg, n)]  (* 小立即数直接加载 *)
  else
    (* 完全正确的算法：处理所有边界情况 *)
    let high = (n asr 12) + (if (n land 0x800) <> 0 then 1 else 0) in
    let low = n - (high lsl 12) in
    [Lui (reg, high land 0xFFFFF); Addi (reg, reg, low)]

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
      match (r1, r2) with
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
      | _ -> Unknown
  | _ -> Unknown

(* ==================== AST到IR转换（最终优化版） ==================== *)
let rec expr_to_ir state expr env =
  (* 尝试从常量缓存中获取 *)
  match expr with
  | Num n -> 
      (try 
         let reg = Hashtbl.find state.const_cache n in
         (reg, [], state)
       with Not_found ->
         let (temp, state') = fresh_temp state in
         let code = emit_imm_load temp n in
         Hashtbl.add state'.const_cache n temp;
         (temp, code, state'))
  
  | Var x -> 
      (* 尝试从寄存器缓存中获取 *)
      (try 
         let reg = Hashtbl.find state.reg_cache x in
         (reg, [], state)
       with Not_found ->
         let offset, state' = get_var_offset state x in
         let (temp, state'') = fresh_temp state' in
         let code = [Load (temp, RiscvReg "sp", offset)] in
         Hashtbl.add state''.reg_cache x temp;
         (temp, code, state''))
  
  | Binary (op, e1, e2) ->
      (* 值范围分析 *)
      let range = expr_range expr env in
      
      (* 基于范围分析进行优化 *)
      match range with
      | Constant n -> 
          expr_to_ir state (Num n) env
      | Bounded (min, max) when max - min < 2048 && min >= -2048 && max <= 2047 ->
          (* 如果值范围在可预测的小范围内，使用临时寄存器 *)
          let (temp, state') = fresh_temp state in
          let (_, e1_code, state'') = expr_to_ir state' e1 env in
          let (_, e2_code, state''') = expr_to_ir state'' e2 env in
          let op_str = match op with
            | Add -> "add" | Sub -> "sub" | Mul -> "mul" 
            | Div -> "div" | Mod -> "rem" | Lt -> "slt"
            | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
            | Eq -> "seq" | Neq -> "sne" | And -> "and"
            | Or -> "or" in
          let code = e1_code @ e2_code @ [BinaryOp (op_str, temp, 
              (match e1 with Num _ -> RiscvReg "t0" | _ -> Temp (state.temp_counter - 2)), 
              (match e2 with Num _ -> RiscvReg "t1" | _ -> Temp (state.temp_counter - 1)))] in
          (temp, code, state''')
      
      | _ ->
          (* 通用情况 *)
          let (e1_reg, e1_code, state') = expr_to_ir state e1 env in
          let (e2_reg, e2_code, state'') = expr_to_ir state' e2 env in
          let (temp, state''') = fresh_temp state'' in
          let op_str = match op with
            | Add -> "add" | Sub -> "sub" | Mul -> "mul" 
            | Div -> "div" | Mod -> "rem" | Lt -> "slt"
            | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
            | Eq -> "seq" | Neq -> "sne" | And -> "and"
            | Or -> "or" in
          (temp, e1_code @ e2_code @ [BinaryOp (op_str, temp, e1_reg, e2_reg)], state''')
  
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
  
  instrs
  |> merge_imm_loads []
  |> remove_redundant_stores []

let rec stmt_to_ir state stmt env =
  match stmt with
  | BlockStmt b -> block_to_ir state b env
  
  | DeclStmt (_, name, Some expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr env in
      let offset, state'' = get_var_offset state' name in
      let code = expr_code @ [Store (expr_reg, RiscvReg "sp", offset)] in
      let optimized_code = optimize_basic_block code in
      (optimized_code, state'')
  
  | DeclStmt (_, name, None) ->
      let offset, state' = get_var_offset state name in
      ([], state')
  
  | AssignStmt (name, expr) ->
      let (expr_reg, expr_code, state') = expr_to_ir state expr env in
      let offset, state'' = get_var_offset state' name in
      let code = expr_code @ [Store (expr_reg, RiscvReg "sp", offset)] in
      let optimized_code = optimize_basic_block code in
      (optimized_code, state'')
  
  | IfStmt (cond, then_stmt, else_stmt) ->
      let (cond_reg, cond_code, state') = expr_to_ir state cond env in
      let (then_label, state'') = fresh_label state' "then" in
      let (else_label, state''') = fresh_label state'' "else" in
      let (merge_label, state'''') = fresh_label state''' "merge" in
      
      let (then_code, state''''') = stmt_to_ir state'''' then_stmt env in
      let (else_code, state'''''') = 
        match else_stmt with
        | Some s -> stmt_to_ir state''''' s env
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
      let (expr_reg, expr_code, state') = expr_to_ir state expr env in
      (expr_code @ [Mv (RiscvReg "a0", expr_reg); Ret], state')
  
  | ReturnStmt None ->
      ([Ret], state)
  
  | ExprStmt expr ->
      let (_, expr_code, state') = expr_to_ir state expr env in
      (optimize_basic_block expr_code, state')
  
  | WhileStmt (cond, body) ->
      let (loop_label, state') = fresh_label state "loop" in
      let (end_label, state'') = fresh_label state' "end" in
      let (cond_label, state''') = fresh_label state'' "cond" in
      
      let state_with_loop = { state''' with loop_labels = (end_label, cond_label) :: state'''.loop_labels } in
      
      let (cond_reg, cond_code, state'''') = expr_to_ir state_with_loop cond env in
      let (body_code, state''''') = stmt_to_ir state'''' body env in
      
      (* 优化控制流 *)
      let code = [Label cond_label] @
                cond_code @
                [Branch ("beqz", cond_reg, RiscvReg "zero", end_label)] @
                body_code @
                [Jmp cond_label;
                 Label end_label]
      in
      (optimize_basic_block code, 
       { state''''' with loop_labels = List.tl state'''''.loop_labels })
  
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

and block_to_ir state block env =
  let new_env = Hashtbl.copy env in
  List.fold_left (fun (code_acc, st) stmt ->
    let (code, st') = stmt_to_ir st stmt new_env in
    (code_acc @ code, st')
  ) ([], state) block.stmts

(* ==================== 函数级别的优化 ==================== *)
let optimize_function ir_func =
  let optimized_body = optimize_basic_block ir_func.body in
  { ir_func with body = optimized_body }

let func_to_ir (func : Ast.func_def) : ir_func =
  let state = { 
    initial_state with 
    var_offset = Hashtbl.create (List.length func.params);
  } in
  let env = Hashtbl.create 10 in
  
  (* 添加参数到环境 *)
  List.iter (fun (p : Ast.param) -> 
    Hashtbl.add env p.name (Bounded (-2147483648, 2147483647))) func.params;
  
  let state' = 
    List.fold_left (fun st (param : Ast.param) ->
      let offset, st' = get_var_offset st param.name in
      st'
    ) state func.params
  in
  let (body_code, final_state) = block_to_ir state' func.body env in
  let result = {
    name = func.name;
    params = List.map (fun (p : Ast.param) -> p.name) func.params;
    body = body_code;
  } in
  optimize_function result

(* ==================== 语义分析（保持不变） ==================== *)
(* ... [语义分析代码保持不变] ... *)

(* ==================== 输出函数 ==================== *)
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
  
  (* 生成IR并进行优化 *)
  let ir = List.map func_to_ir ast in
  
  (* 输出IR *)
  let ir_out = open_out "risc-V.txt" in
  List.iter (fun f -> 
    let s = string_of_ir f in
    Printf.fprintf ir_out "%s\n" s;
  ) ir;
  close_out ir_out;
  
  print_endline "Compilation successful!";
  print_endline "AST written to ast.txt";
  print_endline "Optimized RISC-V assembly written to risc-V.txt"