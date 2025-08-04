exception LexicalError of string [@@warning "-38"]
exception SemanticError of string

open ToyC_riscv_lib.Ast
open ToyC_riscv_lib

(* 使用更轻量级的Hashtbl替代方案 *)
module FastMap = struct
  type 'a t = {
    keys: string array;
    values: 'a array;
    mutable size: int;
  }
  
  let create capacity = {
    keys = Array.make capacity "";
    values = Array.make capacity (Obj.magic 0);
    size = 0;
  }
  
  let find map key =
    let rec loop i =
      if i >= map.size then None
      else if map.keys.(i) = key then Some map.values.(i)
      else loop (i + 1)
    in
    loop 0
  
  let add map key value =
    if map.size >= Array.length map.keys then
      (* 需要扩容时创建新数组 *)
      let new_cap = (Array.length map.keys * 2) in
      let new_keys = Array.make new_cap "" in
      let new_values = Array.make new_cap (Obj.magic 0) in
      Array.blit map.keys 0 new_keys 0 map.size;
      Array.blit map.values 0 new_values 0 map.size;
      new_keys.(map.size) <- key;
      new_values.(map.size) <- value;
      { keys = new_keys; values = new_values; size = map.size + 1 }
    else (
      map.keys.(map.size) <- key;
      map.values.(map.size) <- value;
      map.size <- map.size + 1;
      map
    )
  
  let replace map key value =
    let rec loop i =
      if i >= map.size then add map key value
      else if map.keys.(i) = key then (
        map.values.(i) <- value;
        map
      )
      else loop (i + 1)
    in
    loop 0
end

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
  temp_counter: int;
  label_counter: int;
  var_offset: (string, int) FastMap.t;
  stack_size: int;
  loop_labels: (string * string) list;
  current_code: ir_instr list;
  (* 使用数组存储常量表达式 *)
  const_cache: (expr * reg) array ref;
  const_cache_size: int ref;
}

let initial_state () = 
  {
    temp_counter = 0;
    label_counter = 0;
    var_offset = FastMap.create 16;
    stack_size = 0;
    loop_labels = [];
    current_code = [];
    const_cache = ref [||];
    const_cache_size = ref 0;
  }

(* ==================== 高效辅助函数 ==================== *)
let fresh_temp state =
  ({ state with temp_counter = state.temp_counter + 1 }, 
   Temp state.temp_counter)

let fresh_label state prefix =
  ({ state with label_counter = state.label_counter + 1 },
   Printf.sprintf "%s%d" prefix state.label_counter)

let get_var_offset state var =
  match FastMap.find state.var_offset var with
  | Some offset -> (state, offset)
  | None ->
      (* 直接对齐到8字节边界 *)
      let offset = (state.stack_size + 7) land (lnot 7) in
      let new_state = {
        state with 
        stack_size = offset + 8;
        var_offset = FastMap.add state.var_offset var offset
      } in
      (new_state, offset)

(* 使用尾递归优化指令生成 *)
let rec emit_imm_load state reg n =
  if n = 0 then
    let state' = { state with current_code = Mv (reg, RiscvReg "x0") :: state.current_code } in
    state'
  else if n >= -2048 && n <= 2047 then
    { state with current_code = Li (reg, n) :: state.current_code }
  else
    let low12 = n land 0xFFF in
    let adjusted_low = 
      if low12 >= 0x800 then low12 - 0x1000 
      else low12 in
    let high20 = (n - adjusted_low) lsr 12 in
    let state' = { 
      state with 
      current_code = Lui (reg, high20) :: state.current_code 
    } in
    if adjusted_low <> 0 then
      { state' with current_code = Addi (reg, reg, adjusted_low) :: state'.current_code }
    else state'

let emit state instr = 
  { state with current_code = instr :: state.current_code }

(* ==================== 优化的AST到IR转换 ==================== *)
let rec expr_to_ir state expr =
  (* 优化常量表达式查找 *)
  let rec find_in_cache expr cache i =
    if i >= Array.length cache then None
    else 
      let (e, r) = cache.(i) in
      if e = expr then Some r
      else find_in_cache expr cache (i + 1)
  in
  
  match find_in_cache expr !(state.const_cache) 0 with
  | Some reg -> (state, reg)
  | None ->
      match expr with
      | Num n ->
          let (state', temp) = fresh_temp state in
          let state'' = emit_imm_load state' temp n in
          (* 更新缓存 *)
          if !(state.const_cache_size) >= Array.length !(state.const_cache) then
            let new_size = max 4 (!(state.const_cache_size) * 2) in
            let new_cache = Array.make new_size (Num 0, Temp 0) in
            Array.blit !(state.const_cache) 0 new_cache 0 !(state.const_cache_size);
            state.const_cache := new_cache;
            new_cache.(!(state.const_cache_size)) <- (expr, temp);
            state.const_cache_size := !(state.const_cache_size) + 1;
            (state'', temp)
          else (
            !(state.const_cache).(!(state.const_cache_size)) <- (expr, temp);
            state.const_cache_size := !(state.const_cache_size) + 1;
            (state'', temp)
          )

      | Var x ->
          let (state', offset) = get_var_offset state x in
          let (state'', temp) = fresh_temp state' in
          let state''' = { 
            state'' with 
            current_code = Load (temp, RiscvReg "sp", offset) :: state''.current_code 
          } in
          (state''', temp)

      | Binary (op, e1, e2) ->
          let (state', e1_reg) = expr_to_ir state e1 in
          let (state'', e2_reg) = expr_to_ir state' e2 in
          let (state''', temp) = fresh_temp state'' in
          let op_str = match op with
            | Add -> "add" | Sub -> "sub" | Mul -> "mul"
            | Div -> "div" | Mod -> "rem" | Lt -> "slt"
            | Gt -> "sgt" | Leq -> "sle" | Geq -> "sge"
            | Eq -> "seq" | Neq -> "sne" | And -> "and"
            | Or -> "or" | _ -> failwith "Unsupported operator" 
          in
          let state'''' = { 
            state''' with 
            current_code = BinaryOp (op_str, temp, e1_reg, e2_reg) :: state'''.current_code 
          } in
          (state'''', temp)

      | _ -> failwith "Unsupported expression"

(* 优化控制流：减少标签数量 *)
let rec stmt_to_ir state stmt =
  match stmt with
  | BlockStmt b -> block_to_ir state b.stmts

  | DeclStmt (_, name, Some expr) ->
      let (state', expr_reg) = expr_to_ir state expr in
      let (state'', offset) = get_var_offset state' name in
      let state''' = { 
        state'' with 
        current_code = Store (expr_reg, RiscvReg "sp", offset) :: state''.current_code 
      } in
      state'''

  | DeclStmt (_, name, None) ->
      let (state', _) = get_var_offset state name in
      state'

  | AssignStmt (name, expr) ->
      let (state', expr_reg) = expr_to_ir state expr in
      let offset = 
        match FastMap.find state.var_offset name with
        | Some off -> off
        | None -> 
            (* 变量尚未声明，分配新位置 *)
            let (state'', off) = get_var_offset state' name in
            off
      in
      let state''' = { 
        state' with 
        current_code = Store (expr_reg, RiscvReg "sp", offset) :: state'.current_code 
      } in
      state'''

  | IfStmt (cond, then_stmt, else_stmt) ->
      let (state', cond_reg) = expr_to_ir state cond in
      let (state'', else_label) = fresh_label state' "else" in
      let (state''', merge_label) = fresh_label state'' "merge" in
      let state4 = { 
        state''' with 
        current_code = Branch ("beqz", cond_reg, RiscvReg "zero", else_label) :: state'''.current_code 
      } in
      let state5 = stmt_to_ir state4 then_stmt in
      let state6 = { 
        state5 with 
        current_code = Jmp merge_label :: Label else_label :: state5.current_code 
      } in
      let state7 = match else_stmt with
        | Some s -> stmt_to_ir state6 s
        | None -> state6
      in
      { state7 with current_code = Label merge_label :: state7.current_code }

  | ReturnStmt (Some expr) ->
      let (state', expr_reg) = expr_to_ir state expr in
      let state'' = { 
        state' with 
        current_code = Mv (RiscvReg "a0", expr_reg) :: state'.current_code 
      } in
      { state'' with current_code = Ret :: state''.current_code }

  | ReturnStmt None ->
      { state with current_code = Ret :: state.current_code }

  | ExprStmt expr ->
      let (state', _) = expr_to_ir state expr in
      state'  (* 忽略结果 *)

  | WhileStmt (cond, body) ->
      let (state', loop_label) = fresh_label state "loop" in
      let (state'', end_label) = fresh_label state' "end" in
      let state1 = { 
        state'' with 
        current_code = Label loop_label :: state''.current_code 
      } in
      let (state2, cond_reg) = expr_to_ir state1 cond in
      let state3 = { 
        state2 with 
        current_code = Branch ("beqz", cond_reg, RiscvReg "zero", end_label) :: state2.current_code 
      } in
      let state4 = stmt_to_ir state3 body in
      let state5 = { 
        state4 with 
        current_code = Jmp loop_label :: state4.current_code 
      } in
      { state5 with current_code = Label end_label :: state5.current_code }

  | BreakStmt ->
      (match state.loop_labels with
      | (end_label, _) :: _ -> 
          { state with current_code = Jmp end_label :: state.current_code }
      | [] -> failwith "break statement outside loop")

  | ContinueStmt ->
      (match state.loop_labels with
      | (_, loop_label) :: _ -> 
          { state with current_code = Jmp loop_label :: state.current_code }
      | [] -> failwith "continue statement outside loop")

  | EmptyStmt -> state

and block_to_ir state stmts =
  List.fold_left stmt_to_ir state stmts

(* ==================== 函数处理 ==================== *)
let func_to_ir (func : Ast.func_def) : ir_func =
  let init_state = initial_state () in
  
  (* 预分配参数偏移量 - 避免多次查找 *)
  let (state, _) = 
    List.fold_left (fun (state, offset) (p : Ast.param) ->
      let new_state = { 
        state with 
        var_offset = FastMap.add state.var_offset p.name offset;
        stack_size = state.stack_size + 8;
      } in
      (new_state, offset + 8)
    ) (init_state, 0) func.params
  in
  
  let state' = block_to_ir state func.body.stmts in
  
  (* 16字节栈对齐 *)
  let aligned_stack_size = 
    if state'.stack_size = 0 then 0
    else ((state'.stack_size + 15) land (lnot 15)) 
  in
  
  {
    name = func.name;
    params = List.map (fun p -> p.name) func.params;
    body = List.rev state'.current_code;
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
  let b = Buffer.create 1024 in
  Buffer.add_string b (Printf.sprintf ".global %s\n" f.name);
  Buffer.add_string b (Printf.sprintf "%s:\n" f.name);
  
  if f.stack_size > 0 then
    Buffer.add_string b (Printf.sprintf "  addi sp, sp, -%d\n" f.stack_size);
  
  List.iter (fun instr ->
    Buffer.add_string b "  ";
    Buffer.add_string b (string_of_ir_instr instr);
    Buffer.add_char b '\n'
  ) f.body;
  
  if f.stack_size > 0 then
    Buffer.add_string b (Printf.sprintf "  addi sp, sp, %d\n" f.stack_size);
  
  Buffer.add_string b "  ret\n";
  Buffer.contents b

(* ==================== 主编译流程 ==================== *)
let () =
  let ch = open_in "test/04_while_break.tc" in
  let ast = ToyC_riscv_lib.Parser.prog ToyC_riscv_lib.Lexer.token (Lexing.from_channel ch) in
  close_in ch;
  ToyC_riscv_lib.Semantic_analysis.semantic_analysis ast;
  
  (* 生成IR *)
  let ir = List.map func_to_ir ast in
  
  (* 输出IR *)
  let out_ch = open_out "risc-V.txt" in
  List.iter (fun f ->
    output_string out_ch (string_of_ir_func f);
    output_char out_ch '\n'
  ) ir;
  close_out out_ch;
  
  print_endline "Compilation successful!";
  print_endline "Optimized RISC-V assembly written to risc-V.txt"