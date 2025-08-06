
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | WHILE
    | VOID
    | SEMI
    | RPAREN
    | RETURN
    | RBRACE
    | PLUS
    | OR
    | NUMBER of (
# 7 "lib/parser.mly"
       (int)
# 23 "lib/parser.ml"
  )
    | NOT
    | NEQ
    | MUL
    | MOD
    | MINUS
    | LT
    | LPAREN
    | LEQ
    | LBRACE
    | INT
    | IF
    | ID of (
# 6 "lib/parser.mly"
       (string)
# 39 "lib/parser.ml"
  )
    | GT
    | GEQ
    | EQ
    | EOF
    | ELSE
    | DIV
    | CONTINUE
    | COMMA
    | BREAK
    | ASSIGN
    | AND
  
end

include MenhirBasics

# 1 "lib/parser.mly"
  
open Ast  (* 导入 AST 结构，用于构造节点 *)

# 61 "lib/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_comp_unit) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: comp_unit. *)

  | MenhirState003 : (('s, _menhir_box_comp_unit) _menhir_cell1_VOID _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_state
    (** State 003.
        Stack shape : VOID ID.
        Start symbol: comp_unit. *)

  | MenhirState008 : ((('s, _menhir_box_comp_unit) _menhir_cell1_VOID _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_cell1_param_list, _menhir_box_comp_unit) _menhir_state
    (** State 008.
        Stack shape : VOID ID param_list.
        Start symbol: comp_unit. *)

  | MenhirState009 : (('s, _menhir_box_comp_unit) _menhir_cell1_LBRACE, _menhir_box_comp_unit) _menhir_state
    (** State 009.
        Stack shape : LBRACE.
        Start symbol: comp_unit. *)

  | MenhirState011 : (('s, _menhir_box_comp_unit) _menhir_cell1_WHILE, _menhir_box_comp_unit) _menhir_state
    (** State 011.
        Stack shape : WHILE.
        Start symbol: comp_unit. *)

  | MenhirState016 : (('s, _menhir_box_comp_unit) _menhir_cell1_LPAREN, _menhir_box_comp_unit) _menhir_state
    (** State 016.
        Stack shape : LPAREN.
        Start symbol: comp_unit. *)

  | MenhirState018 : (('s, _menhir_box_comp_unit) _menhir_cell1_ID, _menhir_box_comp_unit) _menhir_state
    (** State 018.
        Stack shape : ID.
        Start symbol: comp_unit. *)

  | MenhirState019 : (('s, _menhir_box_comp_unit) _menhir_cell1_unary_op, _menhir_box_comp_unit) _menhir_state
    (** State 019.
        Stack shape : unary_op.
        Start symbol: comp_unit. *)

  | MenhirState031 : (('s, _menhir_box_comp_unit) _menhir_cell1_rel_expr _menhir_cell0_rel_op, _menhir_box_comp_unit) _menhir_state
    (** State 031.
        Stack shape : rel_expr rel_op.
        Start symbol: comp_unit. *)

  | MenhirState036 : (('s, _menhir_box_comp_unit) _menhir_cell1_mul_expr _menhir_cell0_mul_op, _menhir_box_comp_unit) _menhir_state
    (** State 036.
        Stack shape : mul_expr mul_op.
        Start symbol: comp_unit. *)

  | MenhirState041 : (('s, _menhir_box_comp_unit) _menhir_cell1_add_expr _menhir_cell0_add_op, _menhir_box_comp_unit) _menhir_state
    (** State 041.
        Stack shape : add_expr add_op.
        Start symbol: comp_unit. *)

  | MenhirState044 : (('s, _menhir_box_comp_unit) _menhir_cell1_lor_expr, _menhir_box_comp_unit) _menhir_state
    (** State 044.
        Stack shape : lor_expr.
        Start symbol: comp_unit. *)

  | MenhirState046 : (('s, _menhir_box_comp_unit) _menhir_cell1_land_expr, _menhir_box_comp_unit) _menhir_state
    (** State 046.
        Stack shape : land_expr.
        Start symbol: comp_unit. *)

  | MenhirState053 : (('s, _menhir_box_comp_unit) _menhir_cell1_expr, _menhir_box_comp_unit) _menhir_state
    (** State 053.
        Stack shape : expr.
        Start symbol: comp_unit. *)

  | MenhirState058 : ((('s, _menhir_box_comp_unit) _menhir_cell1_WHILE, _menhir_box_comp_unit) _menhir_cell1_expr, _menhir_box_comp_unit) _menhir_state
    (** State 058.
        Stack shape : WHILE expr.
        Start symbol: comp_unit. *)

  | MenhirState060 : (('s, _menhir_box_comp_unit) _menhir_cell1_RETURN, _menhir_box_comp_unit) _menhir_state
    (** State 060.
        Stack shape : RETURN.
        Start symbol: comp_unit. *)

  | MenhirState066 : (('s, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_state
    (** State 066.
        Stack shape : INT ID.
        Start symbol: comp_unit. *)

  | MenhirState070 : (('s, _menhir_box_comp_unit) _menhir_cell1_IF, _menhir_box_comp_unit) _menhir_state
    (** State 070.
        Stack shape : IF.
        Start symbol: comp_unit. *)

  | MenhirState072 : ((('s, _menhir_box_comp_unit) _menhir_cell1_IF, _menhir_box_comp_unit) _menhir_cell1_expr, _menhir_box_comp_unit) _menhir_state
    (** State 072.
        Stack shape : IF expr.
        Start symbol: comp_unit. *)

  | MenhirState074 : (('s, _menhir_box_comp_unit) _menhir_cell1_ID, _menhir_box_comp_unit) _menhir_state
    (** State 074.
        Stack shape : ID.
        Start symbol: comp_unit. *)

  | MenhirState082 : (((('s, _menhir_box_comp_unit) _menhir_cell1_IF, _menhir_box_comp_unit) _menhir_cell1_expr, _menhir_box_comp_unit) _menhir_cell1_stmt, _menhir_box_comp_unit) _menhir_state
    (** State 082.
        Stack shape : IF expr stmt.
        Start symbol: comp_unit. *)

  | MenhirState090 : (('s, _menhir_box_comp_unit) _menhir_cell1_stmt, _menhir_box_comp_unit) _menhir_state
    (** State 090.
        Stack shape : stmt.
        Start symbol: comp_unit. *)

  | MenhirState095 : (('s, _menhir_box_comp_unit) _menhir_cell1_param, _menhir_box_comp_unit) _menhir_state
    (** State 095.
        Stack shape : param.
        Start symbol: comp_unit. *)

  | MenhirState099 : (('s, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_state
    (** State 099.
        Stack shape : INT ID.
        Start symbol: comp_unit. *)

  | MenhirState101 : ((('s, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_cell1_param_list, _menhir_box_comp_unit) _menhir_state
    (** State 101.
        Stack shape : INT ID param_list.
        Start symbol: comp_unit. *)

  | MenhirState105 : (('s, _menhir_box_comp_unit) _menhir_cell1_func_def, _menhir_box_comp_unit) _menhir_state
    (** State 105.
        Stack shape : func_def.
        Start symbol: comp_unit. *)


and ('s, 'r) _menhir_cell1_add_expr = 
  | MenhirCell1_add_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and 's _menhir_cell0_add_op = 
  | MenhirCell0_add_op of 's * (Ast.bin_op)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_func_def = 
  | MenhirCell1_func_def of 's * ('s, 'r) _menhir_state * (Ast.func_def)

and ('s, 'r) _menhir_cell1_land_expr = 
  | MenhirCell1_land_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_lor_expr = 
  | MenhirCell1_lor_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_mul_expr = 
  | MenhirCell1_mul_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and 's _menhir_cell0_mul_op = 
  | MenhirCell0_mul_op of 's * (Ast.bin_op)

and ('s, 'r) _menhir_cell1_param = 
  | MenhirCell1_param of 's * ('s, 'r) _menhir_state * (Ast.param)

and ('s, 'r) _menhir_cell1_param_list = 
  | MenhirCell1_param_list of 's * ('s, 'r) _menhir_state * (Ast.param list)

and ('s, 'r) _menhir_cell1_rel_expr = 
  | MenhirCell1_rel_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and 's _menhir_cell0_rel_op = 
  | MenhirCell0_rel_op of 's * (Ast.bin_op)

and ('s, 'r) _menhir_cell1_stmt = 
  | MenhirCell1_stmt of 's * ('s, 'r) _menhir_state * (Ast.stmt)

and ('s, 'r) _menhir_cell1_unary_op = 
  | MenhirCell1_unary_op of 's * ('s, 'r) _menhir_state * (Ast.unary_op)

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 6 "lib/parser.mly"
       (string)
# 241 "lib/parser.ml"
)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 6 "lib/parser.mly"
       (string)
# 248 "lib/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_INT = 
  | MenhirCell1_INT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_VOID = 
  | MenhirCell1_VOID of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_WHILE = 
  | MenhirCell1_WHILE of 's * ('s, 'r) _menhir_state

and _menhir_box_comp_unit = 
  | MenhirBox_comp_unit of (Ast.comp_unit) [@@unboxed]

let _menhir_action_01 =
  fun e ->
    (
# 116 "lib/parser.mly"
                 ( e )
# 280 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_02 =
  fun e1 e2 op ->
    (
# 117 "lib/parser.mly"
                                            ( Binary (op, e1, e2) )
# 288 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_03 =
  fun () ->
    (
# 121 "lib/parser.mly"
         ( Add )
# 296 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_04 =
  fun () ->
    (
# 122 "lib/parser.mly"
          ( Sub )
# 304 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_05 =
  fun stmts ->
    (
# 54 "lib/parser.mly"
                                    ( { stmts } )
# 312 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_06 =
  fun funcs ->
    (
# 30 "lib/parser.mly"
                               ( funcs )
# 320 "lib/parser.ml"
     : (Ast.comp_unit))

let _menhir_action_07 =
  fun e ->
    (
# 84 "lib/parser.mly"
                 ( e )
# 328 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_08 =
  fun args ->
    (
# 159 "lib/parser.mly"
                                                ( args )
# 336 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_09 =
  fun () ->
    (
# 160 "lib/parser.mly"
              ( [] )
# 344 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_10 =
  fun body name params ->
    (
# 36 "lib/parser.mly"
    ( { ret_type = Int; name; params; body } )
# 352 "lib/parser.ml"
     : (Ast.func_def))

let _menhir_action_11 =
  fun body name params ->
    (
# 38 "lib/parser.mly"
    ( { ret_type = Void; name; params; body } )
# 360 "lib/parser.ml"
     : (Ast.func_def))

let _menhir_action_12 =
  fun e ->
    (
# 95 "lib/parser.mly"
                 ( e )
# 368 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_13 =
  fun e1 e2 ->
    (
# 96 "lib/parser.mly"
                                     ( Binary (And, e1, e2) )
# 376 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_14 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 384 "lib/parser.ml"
     : (Ast.comp_unit))

let _menhir_action_15 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 392 "lib/parser.ml"
     : (Ast.comp_unit))

let _menhir_action_16 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 400 "lib/parser.ml"
     : (Ast.stmt list))

let _menhir_action_17 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 408 "lib/parser.ml"
     : (Ast.stmt list))

let _menhir_action_18 =
  fun e ->
    (
# 89 "lib/parser.mly"
                  ( e )
# 416 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_19 =
  fun e1 e2 ->
    (
# 90 "lib/parser.mly"
                                    ( Binary (Or, e1, e2) )
# 424 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_20 =
  fun e ->
    (
# 127 "lib/parser.mly"
                   ( e )
# 432 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_21 =
  fun e1 e2 op ->
    (
# 128 "lib/parser.mly"
                                              ( Binary (op, e1, e2) )
# 440 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_22 =
  fun () ->
    (
# 132 "lib/parser.mly"
        ( Mul )
# 448 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_23 =
  fun () ->
    (
# 133 "lib/parser.mly"
        ( Div )
# 456 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_24 =
  fun () ->
    (
# 134 "lib/parser.mly"
        ( Mod )
# 464 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_25 =
  fun name ->
    (
# 47 "lib/parser.mly"
                  ( { typ = Int; name } )
# 472 "lib/parser.ml"
     : (Ast.param))

let _menhir_action_26 =
  fun params ->
    (
# 42 "lib/parser.mly"
                                                 ( params )
# 480 "lib/parser.ml"
     : (Ast.param list))

let _menhir_action_27 =
  fun () ->
    (
# 43 "lib/parser.mly"
            ( [] )
# 488 "lib/parser.ml"
     : (Ast.param list))

let _menhir_action_28 =
  fun name ->
    (
# 151 "lib/parser.mly"
              ( Var name )
# 496 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_29 =
  fun num ->
    (
# 152 "lib/parser.mly"
                 ( Num num )
# 504 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_30 =
  fun e ->
    (
# 153 "lib/parser.mly"
                           ( e )
# 512 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_31 =
  fun args name ->
    (
# 154 "lib/parser.mly"
                                             ( Call (name, args) )
# 520 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_32 =
  fun e ->
    (
# 101 "lib/parser.mly"
                 ( e )
# 528 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_33 =
  fun e1 e2 op ->
    (
# 102 "lib/parser.mly"
                                            ( Binary (op, e1, e2) )
# 536 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_34 =
  fun () ->
    (
# 106 "lib/parser.mly"
       ( Lt )
# 544 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_35 =
  fun () ->
    (
# 107 "lib/parser.mly"
       ( Gt )
# 552 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_36 =
  fun () ->
    (
# 108 "lib/parser.mly"
        ( Leq )
# 560 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_37 =
  fun () ->
    (
# 109 "lib/parser.mly"
        ( Geq )
# 568 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_38 =
  fun () ->
    (
# 110 "lib/parser.mly"
       ( Eq )
# 576 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_39 =
  fun () ->
    (
# 111 "lib/parser.mly"
        ( Neq )
# 584 "lib/parser.ml"
     : (Ast.bin_op))

let _menhir_action_40 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 592 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_41 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 600 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_42 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 608 "lib/parser.ml"
     : (Ast.param list))

let _menhir_action_43 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 616 "lib/parser.ml"
     : (Ast.param list))

let _menhir_action_44 =
  fun block ->
    (
# 64 "lib/parser.mly"
                  ( BlockStmt block )
# 624 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_45 =
  fun () ->
    (
# 65 "lib/parser.mly"
         ( EmptyStmt )
# 632 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_46 =
  fun expr ->
    (
# 66 "lib/parser.mly"
                     ( ExprStmt expr )
# 640 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_47 =
  fun expr name ->
    (
# 67 "lib/parser.mly"
                                      ( AssignStmt (name, expr) )
# 648 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_48 =
  fun expr name ->
    (
# 68 "lib/parser.mly"
                                          ( DeclStmt (Int, name, Some expr) )
# 656 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_49 =
  fun cond then_stmt ->
    (
# 70 "lib/parser.mly"
    ( IfStmt (cond, then_stmt, None) )
# 664 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_50 =
  fun cond else_stmt then_stmt ->
    (
# 72 "lib/parser.mly"
    ( IfStmt (cond, then_stmt, Some else_stmt) )
# 672 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_51 =
  fun cond stmt ->
    (
# 73 "lib/parser.mly"
                                                ( WhileStmt (cond, stmt) )
# 680 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_52 =
  fun () ->
    (
# 74 "lib/parser.mly"
               ( BreakStmt )
# 688 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_53 =
  fun () ->
    (
# 75 "lib/parser.mly"
                  ( ContinueStmt )
# 696 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_54 =
  fun () ->
    (
# 76 "lib/parser.mly"
                ( ReturnStmt None )
# 704 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_55 =
  fun e ->
    (
# 77 "lib/parser.mly"
                       (ReturnStmt(Some e))
# 712 "lib/parser.ml"
     : (Ast.stmt))

let _menhir_action_56 =
  fun stmts ->
    (
# 59 "lib/parser.mly"
                       ( stmts )
# 720 "lib/parser.ml"
     : (Ast.stmt list))

let _menhir_action_57 =
  fun e ->
    (
# 139 "lib/parser.mly"
                     ( e )
# 728 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_58 =
  fun e op ->
    (
# 140 "lib/parser.mly"
                                 ( Unary (op, e) )
# 736 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_59 =
  fun () ->
    (
# 144 "lib/parser.mly"
         ( Plus )
# 744 "lib/parser.ml"
     : (Ast.unary_op))

let _menhir_action_60 =
  fun () ->
    (
# 145 "lib/parser.mly"
          ( Minus )
# 752 "lib/parser.ml"
     : (Ast.unary_op))

let _menhir_action_61 =
  fun () ->
    (
# 146 "lib/parser.mly"
        ( Not )
# 760 "lib/parser.ml"
     : (Ast.unary_op))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AND ->
        "AND"
    | ASSIGN ->
        "ASSIGN"
    | BREAK ->
        "BREAK"
    | COMMA ->
        "COMMA"
    | CONTINUE ->
        "CONTINUE"
    | DIV ->
        "DIV"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | GEQ ->
        "GEQ"
    | GT ->
        "GT"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | INT ->
        "INT"
    | LBRACE ->
        "LBRACE"
    | LEQ ->
        "LEQ"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MINUS ->
        "MINUS"
    | MOD ->
        "MOD"
    | MUL ->
        "MUL"
    | NEQ ->
        "NEQ"
    | NOT ->
        "NOT"
    | NUMBER _ ->
        "NUMBER"
    | OR ->
        "OR"
    | PLUS ->
        "PLUS"
    | RBRACE ->
        "RBRACE"
    | RETURN ->
        "RETURN"
    | RPAREN ->
        "RPAREN"
    | SEMI ->
        "SEMI"
    | VOID ->
        "VOID"
    | WHILE ->
        "WHILE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_103 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _v ->
      let funcs = _v in
      let _v = _menhir_action_06 funcs in
      MenhirBox_comp_unit _v
  
  let rec _menhir_run_106 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_func_def -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _v ->
      let MenhirCell1_func_def (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_15 x xs in
      _menhir_goto_list_func_def_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_func_def_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState105 ->
          _menhir_run_106 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_103 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_VOID (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INT ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState003
              | RPAREN ->
                  let _v_0 = _menhir_action_27 () in
                  _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState003
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let name = _v in
          let _v = _menhir_action_25 name in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_param (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState095 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INT ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_42 x in
              _menhir_goto_separated_nonempty_list_COMMA_param_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_param_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState095 ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState099 ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState003 ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_096 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_param -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_param (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_43 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_param_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_006 : type  ttv_stack. (ttv_stack _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let params = _v in
      let _v = _menhir_action_26 params in
      _menhir_goto_param_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_param_list : type  ttv_stack. (ttv_stack _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState099 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState003 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_100 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_param_list (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState101 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_009 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | SEMI ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | RETURN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | NUMBER _v ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState009
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | LBRACE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | INT ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | IF ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | ID _v ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState009
      | CONTINUE ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | BREAK ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | RBRACE ->
          let _v = _menhir_action_16 () in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState011 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_012 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_59 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_unary_op : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_unary_op (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState019
      | NUMBER _v_0 ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState019
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState019
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState019
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState019
      | ID _v_1 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState019
      | _ ->
          _eRR ()
  
  and _menhir_run_013 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let num = _v in
      let _v = _menhir_action_29 num in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_primary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_57 e in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_unary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState036 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState090 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState009 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState011 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState041 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState031 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_037 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_mul_expr _menhir_cell0_mul_op -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_mul_op (_menhir_stack, op) = _menhir_stack in
      let MenhirCell1_mul_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_21 e1 e2 op in
      _menhir_goto_mul_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_mul_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState041 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState009 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState011 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState031 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_042 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_add_expr _menhir_cell0_add_op as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | EQ | GEQ | GT | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | SEMI ->
          let MenhirCell0_add_op (_menhir_stack, op) = _menhir_stack in
          let MenhirCell1_add_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_02 e1 e2 op in
          _menhir_goto_add_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_033 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_mul_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_22 () in
      _menhir_goto_mul_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_mul_op : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_mul_expr -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_mul_op (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | NUMBER _v_0 ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState036
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState036
      | ID _v_1 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState036
      | _ ->
          _eRR ()
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_61 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_60 () in
      _menhir_goto_unary_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState016 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NUMBER _v ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | DIV | EQ | GEQ | GT | LEQ | LT | MINUS | MOD | MUL | NEQ | OR | PLUS | RPAREN | SEMI ->
          let name = _v in
          let _v = _menhir_action_28 name in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_018 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_ID -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState018 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NUMBER _v ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RPAREN ->
          let _v = _menhir_action_09 () in
          _menhir_goto_expr_list _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr_list : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_ID (_menhir_stack, _menhir_s, name) = _menhir_stack in
      let args = _v in
      let _v = _menhir_action_31 args name in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_034 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_mul_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_24 () in
      _menhir_goto_mul_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_035 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_mul_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_23 () in
      _menhir_goto_mul_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_add_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState009 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState011 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState031 ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_048 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_add_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_add_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | EQ | GEQ | GT | LEQ | LT | NEQ | OR | RPAREN | SEMI ->
          let e = _v in
          let _v = _menhir_action_32 e in
          _menhir_goto_rel_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_039 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_add_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_03 () in
      _menhir_goto_add_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_add_op : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_add_expr -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_add_op (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState041
      | NUMBER _v_0 ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState041
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState041
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState041
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState041
      | ID _v_1 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState041
      | _ ->
          _eRR ()
  
  and _menhir_run_040 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_add_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_04 () in
      _menhir_goto_add_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_rel_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState009 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState011 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_047 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_land_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | NEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | OR | RPAREN | SEMI ->
          let MenhirCell1_land_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_13 e1 e2 in
          _menhir_goto_land_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_025 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_39 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_rel_op : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_rel_op (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | NUMBER _v_0 ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState031
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState031
      | ID _v_1 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState031
      | _ ->
          _eRR ()
  
  and _menhir_run_026 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_34 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_027 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_36 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_028 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_35 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_029 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_37 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_030 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_38 () in
      _menhir_goto_rel_op _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_land_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState009 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState011 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_049 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_land_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | OR | RPAREN | SEMI ->
          let e = _v in
          let _v = _menhir_action_18 e in
          _menhir_goto_lor_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_046 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_land_expr -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState046 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NUMBER _v ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_lor_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_lor_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState044 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | COMMA | RPAREN | SEMI ->
          let e = _v in
          let _v = _menhir_action_07 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState009 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState070 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState060 ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState011 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState016 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState053 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState018 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_084 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let expr = _v in
          let _v = _menhir_action_46 expr in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState090 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState009 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState082 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState072 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_090 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | SEMI ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | RETURN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | PLUS ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | NUMBER _v_0 ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState090
      | NOT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | MINUS ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | LPAREN ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | LBRACE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | INT ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | IF ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | ID _v_1 ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState090
      | CONTINUE ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | BREAK ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | RBRACE ->
          let _v_2 = _menhir_action_16 () in
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2
      | _ ->
          _eRR ()
  
  and _menhir_run_059 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_45 () in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_060 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_54 () in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | NUMBER _v ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState060
      | NOT ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | MINUS ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | LPAREN ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | ID _v ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState060
      | _ ->
          _eRR ()
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_INT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ASSIGN ->
              let _menhir_s = MenhirState066 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | PLUS ->
                  _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | NUMBER _v ->
                  _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | NOT ->
                  _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ID _v ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_069 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState070 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_073 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ASSIGN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState074 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND | DIV | EQ | GEQ | GT | LEQ | LT | MINUS | MOD | MUL | NEQ | OR | PLUS | SEMI ->
          let name = _v in
          let _v = _menhir_action_28 name in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_077 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_53 () in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_079 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_52 () in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_091 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_stmt -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_stmt (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_17 x xs in
      _menhir_goto_list_stmt_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_stmt_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState009 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState090 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_092 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let stmts = _v in
      let _v = _menhir_action_56 stmts in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
      let stmts = _v in
      let _v = _menhir_action_05 stmts in
      _menhir_goto_block _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_block : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState101 ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState008 ->
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState009 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_102 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_cell1_param_list -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_param_list (_menhir_stack, _, params) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, name) = _menhir_stack in
      let MenhirCell1_INT (_menhir_stack, _menhir_s) = _menhir_stack in
      let body = _v in
      let _v = _menhir_action_10 body name params in
      _menhir_goto_func_def _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_func_def : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_func_def (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOID ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState105
      | INT ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState105
      | EOF ->
          let _v_0 = _menhir_action_14 () in
          _menhir_run_106 _menhir_stack _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_097 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_INT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | INT ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
              | RPAREN ->
                  let _v_0 = _menhir_action_27 () in
                  _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState099
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_093 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_VOID _menhir_cell0_ID, _menhir_box_comp_unit) _menhir_cell1_param_list -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_param_list (_menhir_stack, _, params) = _menhir_stack in
      let MenhirCell0_ID (_menhir_stack, name) = _menhir_stack in
      let MenhirCell1_VOID (_menhir_stack, _menhir_s) = _menhir_stack in
      let body = _v in
      let _v = _menhir_action_11 body name params in
      _menhir_goto_func_def _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_086 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let block = _v in
      let _v = _menhir_action_44 block in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_087 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_WHILE, _menhir_box_comp_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, cond) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s) = _menhir_stack in
      let stmt = _v in
      let _v = _menhir_action_51 cond stmt in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_083 : type  ttv_stack. (((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_IF, _menhir_box_comp_unit) _menhir_cell1_expr, _menhir_box_comp_unit) _menhir_cell1_stmt -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_stmt (_menhir_stack, _, then_stmt) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, cond) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let else_stmt = _v in
      let _v = _menhir_action_50 cond else_stmt then_stmt in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_081 : type  ttv_stack. (((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_IF, _menhir_box_comp_unit) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState082 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | BREAK | CONTINUE | ID _ | IF | INT | LBRACE | LPAREN | MINUS | NOT | NUMBER _ | PLUS | RBRACE | RETURN | SEMI | WHILE ->
          let MenhirCell1_expr (_menhir_stack, _, cond) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let then_stmt = _v in
          let _v = _menhir_action_49 cond then_stmt in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_ID -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_ID (_menhir_stack, _menhir_s, name) = _menhir_stack in
          let expr = _v in
          let _v = _menhir_action_47 expr name in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_071 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState072 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_067 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_INT _menhir_cell0_ID -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_ID (_menhir_stack, name) = _menhir_stack in
          let MenhirCell1_INT (_menhir_stack, _menhir_s) = _menhir_stack in
          let expr = _v in
          let _v = _menhir_action_48 expr name in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_062 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_RETURN -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_RETURN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_55 e in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_057 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState058 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONTINUE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_055 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_30 e in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState053 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PLUS ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NUMBER _v ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | NOT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_40 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState053 ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState018 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_054 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_41 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_023 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let args = _v in
      let _v = _menhir_action_08 args in
      _menhir_goto_expr_list _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_run_045 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_lor_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_land_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | OR | RPAREN | SEMI ->
          let MenhirCell1_lor_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_19 e1 e2 in
          _menhir_goto_lor_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | NEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GEQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_rel_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | OR | RPAREN | SEMI ->
          let e = _v in
          let _v = _menhir_action_12 e in
          _menhir_goto_land_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_038 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_rel_expr _menhir_cell0_rel_op as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_add_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_add_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | EQ | GEQ | GT | LEQ | LT | NEQ | OR | RPAREN | SEMI ->
          let MenhirCell0_rel_op (_menhir_stack, op) = _menhir_stack in
          let MenhirCell1_rel_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_33 e1 e2 op in
          _menhir_goto_rel_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_032 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_mul_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | EQ | GEQ | GT | LEQ | LT | MINUS | NEQ | OR | PLUS | RPAREN | SEMI ->
          let e = _v in
          let _v = _menhir_action_01 e in
          _menhir_goto_add_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_comp_unit) _menhir_state -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_20 e in
      _menhir_goto_mul_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_020 : type  ttv_stack. (ttv_stack, _menhir_box_comp_unit) _menhir_cell1_unary_op -> _ -> _ -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_op (_menhir_stack, _menhir_s, op) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_58 e op in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_007 : type  ttv_stack. ((ttv_stack, _menhir_box_comp_unit) _menhir_cell1_VOID _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_comp_unit) _menhir_state -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_param_list (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState008 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_comp_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOID ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | INT ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | EOF ->
          let _v = _menhir_action_14 () in
          _menhir_run_103 _menhir_stack _v
      | _ ->
          _eRR ()
  
end

let comp_unit =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_comp_unit v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
