exception LexicalError of string [@@warning "-38"]
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

module StringMap = Map.Make(String)

(* ==================== IR 定义 ==================== *)
type reg = 
  | RiscvReg of string
  | Temp of int

type ir_instr =
  | Li of reg * int
  | Mv of reg * reg
  | BinaryOp of string * reg * reg * reg
  | Branch of string * reg * reg * string
  | Jmp of string
  | Label of string
  | Call of string
  | Ret
  | Store of reg * reg * int
  | Load of reg * reg * int

type ir_func = {
  name: string;
  params: string list;
  body: ir_instr list;
}

(* ==================== 优化后的代码生成状态 ==================== *)
type codegen_state = {
  temp_counter: int;
  label_counter: int;
  var_offset: (string, int) Hashtbl.t;
  stack_size: int;
  loop_labels: (string * string) list;
  const_env: (reg, int) Hashtbl.t;
  copy_env: (reg, reg) Hashtbl.t;
}

let initial_state = {
  temp_counter = 0;
  label_counter = 0;
  var_offset = Hashtbl.create 10;
  stack_size = 0;
  loop_labels = [];
  const_env = Hashtbl.create 10;
  copy_env = Hashtbl.create 10;
}

(* ==================== 优化后的辅助函数 ==================== *)
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

(* 常量折叠优化 *)
let optimize_const_folding expr =
  match expr with
  | Binary (Add, Num n1, Num n2) -> Some (Num (n1 + n2))
  | Binary (Sub, Num n1, Num n2) -> Some (Num (n1 - n2))
  | Binary (Mul, Num n1, Num n2) -> Some (Num (n1 * n2))
  | Binary (Div, Num n1, Num n2) when n2 <> 0 -> Some (Num (n1 / n2))
  | Binary (Mod, Num n1, Num n2) when n2 <> 0 -> Some (Num (n1 mod n2))
  | Unary (Minus, Num n) -> Some (Num (-n))
  | Binary (Lt, Num n1, Num n2) -> Some (Num (if n1 < n2 then 1 else 0))
  | Binary (Gt, Num n1, Num n2) -> Some (Num (if n1 > n2 then 1 else 0))
  | Binary (Leq, Num n1, Num n2) -> Some (Num (if n1 <= n2 then 1 else 0))
  | Binary (Geq, Num n1, Num n2) -> Some (Num (if n1 >= n2 then 1 else 0))
  | Binary (Eq, Num n1, Num n2) -> Some (Num (if n1 = n2 then 1 else 0))
  | Binary (Neq, Num n1, Num n2) -> Some (Num (if n1 <> n2 then 1 else 0))
  | Binary (And, Num n1, Num n2) -> Some (Num (if n1 <> 0 && n2 <> 0 then 1 else 0))
  | Binary (Or, Num n1, Num n2) -> Some (Num (if n1 <> 0 || n2 <> 0 then 1 else 0))
  | _ -> None

(* 强度削弱优化 *)
let optimize_strength_reduction expr =
  match expr with
  | Binary (Mul, e, Num n) when n > 0 && n land (n - 1) = 0 -> (* 幂为2 *)
      let shift = int_of_float (log (float n) /. log 2. +. 0.5) in
      Binary (ShiftL, e, Num shift)
  | Binary (Mul, e, Num n) when n = 3 -> 
      Binary (Add, e, Binary (ShiftL, e, Num 1))
  | Binary (Mul, e, Num n) when n = 5 -> 
      Binary (Add, e, Binary (ShiftL, e, Num 2))
  | Binary (Mul, e, Num n) when n = 9 -> 
      Binary (Add, e, Binary (ShiftL, e, Num 3))
  | Binary (Div, e, Num n) when n > 0 && n land (n - 1) = 0 ->
      let shift = int_of_float (log (float n) /. log 2. +. 0.5) in
      Binary (ShiftR, e, Num shift)
  | _ -> expr

(* 解决大立即数问题 *)
let handle_large_immediate state reg n =
  let code = ref [] in
  if n >= -2048 && n <= 2047 then
    code := [Li (reg, n)]
  else (
    (* 正确处理大负立即数 *)
    let high_bits = (n asr 12) in  (* 使用算术右移处理负数 *)
    let low_bits = n - (high_bits lsl 12) in
    code := [
      Li (reg, high_bits);
      Li (Temp (state.temp_counter + 1), low_bits);
      BinaryOp ("add", reg, reg, Temp (state.temp_counter + 1))
    ]
  );
  (reg, !code, {state with temp_counter = state.temp_counter + 2})

(* ==================== 优化后的表达式转换 ==================== *)
let rec expr_to_ir state expr =
  (* 应用优化 *)
  let expr = match optimize_const_folding expr with
    | Some e -> e
    | None -> expr
  in
  let expr = optimize_strength_reduction expr in
  
  match expr with
  | Num n -> 
      handle_large_immediate state (Temp state.temp_counter) n
      
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

(* ==================== 优化后的语句转换 ==================== *)
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

(* ==================== 优化后的函数转换 ==================== *)
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
      let instr_str = match instr with
        | Li (r, n) when n >= -2048 && n <= 2047 -> 
            Printf.sprintf "  li %s, %d" 
              (match r with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              n
        | Li (r, n) -> (* 大立即数处理 *)
            Printf.sprintf "  lui %s, %%hi(%d)\n  addi %s, %s, %%lo(%d)" 
              (match r with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i) n
              (match r with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match r with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i) 
              n
        | Mv (rd, rs) -> 
            Printf.sprintf "  mv %s, %s" 
              (match rd with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rs with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
        | BinaryOp (op, rd, rs1, rs2) -> 
            Printf.sprintf "  %s %s, %s, %s" op
              (match rd with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rs1 with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rs2 with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
        | Branch (cond, rs1, rs2, label) -> 
            Printf.sprintf "  %s %s, %s, %s" cond
              (match rs1 with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rs2 with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              label
        | Jmp label -> "  j " ^ label
        | Label label -> label ^ ":"
        | Call func -> "  call " ^ func
        | Ret -> "  ret"
        | Store (rs, base, off) when off >= -2048 && off <= 2047 -> 
            Printf.sprintf "  sd %s, %d(%s)"
              (match rs with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              off
              (match base with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
        | Store (rs, base, off) -> 
            Printf.sprintf "  lui t0, %%hi(%d)\n  addi t0, t0, %%lo(%d)\n  add t0, %s, t0\n  sd %s, 0(t0)"
              off off 
              (match base with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rs with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
        | Load (rd, base, off) when off >= -2048 && off <= 2047 -> 
            Printf.sprintf "  ld %s, %d(%s)"
              (match rd with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              off
              (match base with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
        | Load (rd, base, off) -> 
            Printf.sprintf "  lui t0, %%hi(%d)\n  addi t0, t0, %%lo(%d)\n  add t0, %s, t0\n  ld %s, 0(t0)"
              off off 
              (match base with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
              (match rd with RiscvReg s -> s | Temp i -> "t" ^ string_of_int i)
      in
      output_string oc (instr_str ^ "\n")
    ) func.body;
    
    output_string oc "\n"
  ) ir;
  
  close_out oc;
  
  print_endline "Optimized assembly written to optimized_riscv.s"