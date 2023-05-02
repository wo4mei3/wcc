
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | XOR_EQ
    | WHILE
    | VOLATILE
    | UNION
    | ULINT of (
# 260 "src/parser.mly"
       (int)
# 19 "src/parser.ml"
  )
    | UINT of (
# 260 "src/parser.mly"
       (int)
# 24 "src/parser.ml"
  )
    | TYPE_ID of (
# 263 "src/parser.mly"
      (string)
# 29 "src/parser.ml"
  )
    | TYPEDEF
    | TVOID
    | TUNSIGNED
    | TSIGNED
    | TSHORT
    | TLONG
    | TINT
    | TFLOAT
    | TDOUBLE
    | TCHAR
    | SWITCH
    | SUB_EQ
    | STRUCT
    | STR of (
# 262 "src/parser.mly"
      (int list)
# 47 "src/parser.ml"
  )
    | STATIC_ASSERT
    | STATIC
    | STAR
    | SIZEOF
    | SEMI
    | RSHIFT_EQ
    | RSHIFT
    | RPAREN
    | RETURN
    | REGISTER
    | RBRACKET
    | RBRACE
    | QUESTION
    | PLUS
    | OR_EQ
    | OROR
    | OR
    | NOT
    | NORETURN
    | NE
    | MUL_EQ
    | MOD_EQ
    | MOD
    | MINUS
    | LT
    | LSHIFT_EQ
    | LSHIFT
    | LPAREN
    | LINT of (
# 260 "src/parser.mly"
       (int)
# 80 "src/parser.ml"
  )
    | LE
    | LBRACKET
    | LBRACE
    | INT of (
# 260 "src/parser.mly"
       (int)
# 88 "src/parser.ml"
  )
    | INLINE
    | INC
    | IF
    | ID of (
# 263 "src/parser.mly"
      (string)
# 96 "src/parser.ml"
  )
    | HAT
    | GT
    | GOTO
    | GE
    | FOR
    | FLOAT of (
# 261 "src/parser.mly"
       (float)
# 106 "src/parser.ml"
  )
    | EXTERN
    | EQEQ
    | EQ
    | EOF
    | ENUM
    | ELSE
    | ELLIPSIS
    | DOUBLE of (
# 261 "src/parser.mly"
       (float)
# 118 "src/parser.ml"
  )
    | DOT
    | DO
    | DIV_EQ
    | DIV
    | DEFAULT
    | DEC
    | CONTINUE
    | CONST
    | COMMA
    | COLON
    | CASE
    | BREAK
    | BANG
    | AUTO
    | ARROW
    | AND_EQ
    | ANDAND
    | AND
    | ALIGNAS
    | ADD_EQ
  
end

include MenhirBasics

# 1 "src/parser.mly"
  
    open Ast 
    open Env 
    open Ctype
    
    

    type declarator =
    | DeclPtr of declarator
    | DeclIdent of string
    | DeclArr of declarator * int
    | DeclFun of declarator * decl list

    exception ParserError of string
    exception NotImpl of string


    let make_decl ty d = 
      let name = ref "" in
      let rec aux ty = function
      | DeclPtr d -> aux (TPtr ty) d 
      | DeclIdent n -> name := n; ty 
      | DeclArr(d,sz) -> aux (TArr(ty,sz)) d 
      | DeclFun(d,dl) -> aux (TFun(ty,dl)) d
      in (!name, aux ty d)

    let make_decls ty dl =
      List.map (fun d -> make_decl ty d) dl

    let make_decls_with_init_opts ty d_with_init_opt_l =
      List.map (fun (d,init_opt) -> (make_decl ty d,init_opt)) d_with_init_opt_l

    let item_id = ref 0
    let gen_id () =
      item_id := !item_id + 1;
      !item_id

    let append_ds_list a b =
      let pred a b c = 
      match (a,b,c) with
      | (TDeclSpec x,TDeclSpec y,TDeclSpec z) -> TDeclSpec(x@y@z) 
      | _ -> raise (ParserError "decl_spec")
      in
      List.fold_left2 pred (TDeclSpec []) a b

    let struct_pred name =function
    | (_,Struct(n,_)) when n = name ->
      true
    | _ -> false

    let lookup_struct_in_scope name =
      try 
        let (id,_) = List.find (struct_pred name) !curr_scope 
      in
        Some id
      with Not_found ->
        None

    let lookup_struct_in_stack name =
      let rec aux stack =
      match stack with
      | hd::tl ->
      begin
        try 
          let (id,_) = List.find (struct_pred name) hd
        in
          Some id
        with Not_found ->
          aux tl
      end
      | [] -> None
      in aux !stack

    let make_struct name_opt dl =
      let name = ref "" in
      let (id,def_opt) =
      match name_opt with
      | Some n -> 
        begin
          name := n;
          match lookup_struct_in_scope n with
          | Some id -> 
            begin
              match dl with
              | Some _ -> raise (ParserError "redifinition")
              | None -> (id,None)
            end
          | None -> 
            begin
              match lookup_struct_in_stack n with
              | Some id -> (id,None)
              | None -> let id = gen_id () in 
                        (id,Some (id,Struct(!name,dl)))
            end
        end 
      | None -> let id = gen_id () in 
                (id,Some (id,Struct(!name,dl)))
      in
      (def_opt, TsStruct id)

    let union_pred name =function
    | (_,Union(n,_)) when n = name ->
      true
    | _ -> false

    let lookup_union_in_scope name =
      try 
        let (id,_) = List.find (union_pred name) !curr_scope 
      in
        Some id
      with Not_found ->
        None

    let lookup_union_in_stack name =
      let rec aux stack =
      match stack with
      | hd::tl ->
      begin
        try 
          let (id,_) = List.find (union_pred name) hd
        in
          Some id
        with Not_found ->
          aux tl
      end
      | [] -> None
      in aux !stack

    let make_union name_opt dl =
      let name = ref "" in
      let (id,def_opt) =
      match name_opt with
      | Some n -> 
        begin
          name := n;
          match lookup_union_in_scope n with
          | Some id -> 
            begin
              match dl with
              | Some _ -> raise (ParserError "redifinition")
              | None -> (id,None)
            end
          | None -> 
            begin
              match lookup_union_in_stack n with
              | Some id -> (id,None)
              | None -> let id = gen_id () in 
                        (id,Some (id,Union(!name,dl)))
            end
        end 
      | None -> let id = gen_id () in 
                (id,Some (id,Union(!name,dl)))
      in
      (def_opt, TsUnion id)

    let lookup_var_in_scope name =
      let aux = function
      | (_,Var((n,_),_)) when n = name -> true
      | _ -> false
      in
      List.exists aux !curr_scope  

    let lookup_typedef_in_scope name =
      let aux = function
      | (_,Typedef(n,_)) when n = name -> true
      | _ -> false
      in
      List.exists aux !curr_scope 

    let rec is_typedef_definition ty =
      match ty with
      | TFun(t,_) -> is_typedef_definition t 
      | TPtr t -> is_typedef_definition t 
      | TArr(t,_) -> is_typedef_definition t 
      | TDeclSpec dsl -> List.mem (Scs ScsTypedef) dsl
    
    let make_typedef (name, ty) =
      if not (lookup_var_in_scope name || lookup_typedef_in_scope name) then
        (gen_id (),Typedef (name,ty))
      else 
        raise (NotImpl "redifinition")

    let make_var (name,ty) init_opt =
      if lookup_var_in_scope name then
        raise (NotImpl "redifinition")
      else
        (gen_id (), Var((name,ty),init_opt))

    let make_var_or_typedef ((name,ty),init_opt) =
      if is_typedef_definition ty then
        begin
          match init_opt with
          | Some _ -> raise (ParserError "typedef has init")
          | None -> make_typedef (name,ty)
        end
      else
        make_var (name,ty) init_opt

    let get_params = function
    | TFun(_,dl) -> List.map (fun d-> (gen_id () ,Param d)) dl
    | _ -> raise (ParserError "not a function declarator given")

    let def_stack:def list ref = ref []

    let def_stack_in_params:def list ref = ref []
    
    let flush_stack () = 
      def_stack := []  

    let get_stack () =
      let ret = List.rev !def_stack in
      flush_stack ();
      ret

    let in_params = ref false
    
    let enter_params () =
      in_params := true

    let leave_params () =
      in_params := false

    let add_def2 def =
      def_stack_in_params := def::!def_stack_in_params
    
    let add_def def =
      if !in_params then
        add_def2 def
      else
        def_stack := def::!def_stack


    let flush_stack2 () = 
      def_stack_in_params := []  

    let get_stack2 () =
      let ret = List.rev !def_stack_in_params in
      flush_stack2 ();
      ret

    let expr_conv = function
    | Some e -> SExpr e 
    | None -> SStmts []



# 392 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_translation_unit) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: translation_unit. *)

  | MenhirState002 : (('s, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_state
    (** State 002.
        Stack shape : UNION.
        Start symbol: translation_unit. *)

  | MenhirState006 : ((('s, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_state
    (** State 006.
        Stack shape : UNION option(ident).
        Start symbol: translation_unit. *)

  | MenhirState017 : (('s, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_state
    (** State 017.
        Stack shape : STRUCT.
        Start symbol: translation_unit. *)

  | MenhirState019 : ((('s, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_state
    (** State 019.
        Stack shape : STRUCT option(ident).
        Start symbol: translation_unit. *)

  | MenhirState021 : (('s, _menhir_box_translation_unit) _menhir_cell1_STATIC_ASSERT, _menhir_box_translation_unit) _menhir_state
    (** State 021.
        Stack shape : STATIC_ASSERT.
        Start symbol: translation_unit. *)

  | MenhirState025 : (('s, _menhir_box_translation_unit) _menhir_cell1_STAR, _menhir_box_translation_unit) _menhir_state
    (** State 025.
        Stack shape : STAR.
        Start symbol: translation_unit. *)

  | MenhirState026 : (('s, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_state
    (** State 026.
        Stack shape : SIZEOF.
        Start symbol: translation_unit. *)

  | MenhirState027 : (('s, _menhir_box_translation_unit) _menhir_cell1_PLUS, _menhir_box_translation_unit) _menhir_state
    (** State 027.
        Stack shape : PLUS.
        Start symbol: translation_unit. *)

  | MenhirState028 : (('s, _menhir_box_translation_unit) _menhir_cell1_NOT, _menhir_box_translation_unit) _menhir_state
    (** State 028.
        Stack shape : NOT.
        Start symbol: translation_unit. *)

  | MenhirState029 : (('s, _menhir_box_translation_unit) _menhir_cell1_MINUS, _menhir_box_translation_unit) _menhir_state
    (** State 029.
        Stack shape : MINUS.
        Start symbol: translation_unit. *)

  | MenhirState030 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 030.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState033 : (('s, _menhir_box_translation_unit) _menhir_cell1_INC, _menhir_box_translation_unit) _menhir_state
    (** State 033.
        Stack shape : INC.
        Start symbol: translation_unit. *)

  | MenhirState034 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 034.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState037 : (('s, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_state
    (** State 037.
        Stack shape : ENUM.
        Start symbol: translation_unit. *)

  | MenhirState039 : ((('s, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_state
    (** State 039.
        Stack shape : ENUM option(ident).
        Start symbol: translation_unit. *)

  | MenhirState041 : (((('s, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list, _menhir_box_translation_unit) _menhir_state
    (** State 041.
        Stack shape : ENUM option(ident) enum_list.
        Start symbol: translation_unit. *)

  | MenhirState042 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list, _menhir_box_translation_unit) _menhir_cell1_COMMA, _menhir_box_translation_unit) _menhir_state
    (** State 042.
        Stack shape : ENUM option(ident) enum_list COMMA.
        Start symbol: translation_unit. *)

  | MenhirState044 : (('s, _menhir_box_translation_unit) _menhir_cell1_enum_const, _menhir_box_translation_unit) _menhir_state
    (** State 044.
        Stack shape : enum_const.
        Start symbol: translation_unit. *)

  | MenhirState046 : (('s, _menhir_box_translation_unit) _menhir_cell1_DEC, _menhir_box_translation_unit) _menhir_state
    (** State 046.
        Stack shape : DEC.
        Start symbol: translation_unit. *)

  | MenhirState047 : (('s, _menhir_box_translation_unit) _menhir_cell1_BANG, _menhir_box_translation_unit) _menhir_state
    (** State 047.
        Stack shape : BANG.
        Start symbol: translation_unit. *)

  | MenhirState048 : (('s, _menhir_box_translation_unit) _menhir_cell1_AND, _menhir_box_translation_unit) _menhir_state
    (** State 048.
        Stack shape : AND.
        Start symbol: translation_unit. *)

  | MenhirState052 : (('s, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_state
    (** State 052.
        Stack shape : postfix_expr.
        Start symbol: translation_unit. *)

  | MenhirState054 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 054.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState056 : (('s, _menhir_box_translation_unit) _menhir_cell1_shift_expr, _menhir_box_translation_unit) _menhir_state
    (** State 056.
        Stack shape : shift_expr.
        Start symbol: translation_unit. *)

  | MenhirState058 : (('s, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr, _menhir_box_translation_unit) _menhir_state
    (** State 058.
        Stack shape : multiplicative_expr.
        Start symbol: translation_unit. *)

  | MenhirState060 : (('s, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr, _menhir_box_translation_unit) _menhir_state
    (** State 060.
        Stack shape : multiplicative_expr.
        Start symbol: translation_unit. *)

  | MenhirState062 : (('s, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr, _menhir_box_translation_unit) _menhir_state
    (** State 062.
        Stack shape : multiplicative_expr.
        Start symbol: translation_unit. *)

  | MenhirState066 : (('s, _menhir_box_translation_unit) _menhir_cell1_additive_expr, _menhir_box_translation_unit) _menhir_state
    (** State 066.
        Stack shape : additive_expr.
        Start symbol: translation_unit. *)

  | MenhirState068 : (('s, _menhir_box_translation_unit) _menhir_cell1_additive_expr, _menhir_box_translation_unit) _menhir_state
    (** State 068.
        Stack shape : additive_expr.
        Start symbol: translation_unit. *)

  | MenhirState070 : (('s, _menhir_box_translation_unit) _menhir_cell1_shift_expr, _menhir_box_translation_unit) _menhir_state
    (** State 070.
        Stack shape : shift_expr.
        Start symbol: translation_unit. *)

  | MenhirState073 : (('s, _menhir_box_translation_unit) _menhir_cell1_relational_expr, _menhir_box_translation_unit) _menhir_state
    (** State 073.
        Stack shape : relational_expr.
        Start symbol: translation_unit. *)

  | MenhirState076 : (('s, _menhir_box_translation_unit) _menhir_cell1_relational_expr, _menhir_box_translation_unit) _menhir_state
    (** State 076.
        Stack shape : relational_expr.
        Start symbol: translation_unit. *)

  | MenhirState078 : (('s, _menhir_box_translation_unit) _menhir_cell1_relational_expr, _menhir_box_translation_unit) _menhir_state
    (** State 078.
        Stack shape : relational_expr.
        Start symbol: translation_unit. *)

  | MenhirState080 : (('s, _menhir_box_translation_unit) _menhir_cell1_relational_expr, _menhir_box_translation_unit) _menhir_state
    (** State 080.
        Stack shape : relational_expr.
        Start symbol: translation_unit. *)

  | MenhirState083 : (('s, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr, _menhir_box_translation_unit) _menhir_state
    (** State 083.
        Stack shape : logical_or_expr.
        Start symbol: translation_unit. *)

  | MenhirState085 : (('s, _menhir_box_translation_unit) _menhir_cell1_logical_and_expr, _menhir_box_translation_unit) _menhir_state
    (** State 085.
        Stack shape : logical_and_expr.
        Start symbol: translation_unit. *)

  | MenhirState087 : (('s, _menhir_box_translation_unit) _menhir_cell1_inclusive_or_expr, _menhir_box_translation_unit) _menhir_state
    (** State 087.
        Stack shape : inclusive_or_expr.
        Start symbol: translation_unit. *)

  | MenhirState089 : (('s, _menhir_box_translation_unit) _menhir_cell1_exclusive_or_expr, _menhir_box_translation_unit) _menhir_state
    (** State 089.
        Stack shape : exclusive_or_expr.
        Start symbol: translation_unit. *)

  | MenhirState091 : (('s, _menhir_box_translation_unit) _menhir_cell1_equality_expr, _menhir_box_translation_unit) _menhir_state
    (** State 091.
        Stack shape : equality_expr.
        Start symbol: translation_unit. *)

  | MenhirState093 : (('s, _menhir_box_translation_unit) _menhir_cell1_equality_expr, _menhir_box_translation_unit) _menhir_state
    (** State 093.
        Stack shape : equality_expr.
        Start symbol: translation_unit. *)

  | MenhirState096 : (('s, _menhir_box_translation_unit) _menhir_cell1_and_expr, _menhir_box_translation_unit) _menhir_state
    (** State 096.
        Stack shape : and_expr.
        Start symbol: translation_unit. *)

  | MenhirState102 : (('s, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 102.
        Stack shape : expr.
        Start symbol: translation_unit. *)

  | MenhirState105 : ((('s, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 105.
        Stack shape : logical_or_expr expr.
        Start symbol: translation_unit. *)

  | MenhirState108 : (('s, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr, _menhir_box_translation_unit) _menhir_state
    (** State 108.
        Stack shape : logical_or_expr.
        Start symbol: translation_unit. *)

  | MenhirState111 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 111.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState113 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 113.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState115 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 115.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState117 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 117.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState119 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 119.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState121 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 121.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState123 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 123.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState125 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 125.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState127 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 127.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState129 : (('s, _menhir_box_translation_unit) _menhir_cell1_unary_expr, _menhir_box_translation_unit) _menhir_state
    (** State 129.
        Stack shape : unary_expr.
        Start symbol: translation_unit. *)

  | MenhirState135 : ((('s, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_cell1_argument_expr_list, _menhir_box_translation_unit) _menhir_state
    (** State 135.
        Stack shape : postfix_expr argument_expr_list.
        Start symbol: translation_unit. *)

  | MenhirState137 : (('s, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_state
    (** State 137.
        Stack shape : postfix_expr.
        Start symbol: translation_unit. *)

  | MenhirState141 : (('s, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_state
    (** State 141.
        Stack shape : postfix_expr.
        Start symbol: translation_unit. *)

  | MenhirState144 : (('s, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_state
    (** State 144.
        Stack shape : postfix_expr.
        Start symbol: translation_unit. *)

  | MenhirState157 : (('s, _menhir_box_translation_unit) _menhir_cell1_type_spec, _menhir_box_translation_unit) _menhir_state
    (** State 157.
        Stack shape : type_spec.
        Start symbol: translation_unit. *)

  | MenhirState158 : (('s, _menhir_box_translation_unit) _menhir_cell1_type_qual, _menhir_box_translation_unit) _menhir_state
    (** State 158.
        Stack shape : type_qual.
        Start symbol: translation_unit. *)

  | MenhirState164 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_state
    (** State 164.
        Stack shape : LPAREN type_name.
        Start symbol: translation_unit. *)

  | MenhirState165 : (((('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_state
    (** State 165.
        Stack shape : LPAREN type_name LBRACE.
        Start symbol: translation_unit. *)

  | MenhirState166 : (('s, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_state
    (** State 166.
        Stack shape : LBRACKET.
        Start symbol: translation_unit. *)

  | MenhirState168 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_cell1_constant_expr, _menhir_box_translation_unit) _menhir_state
    (** State 168.
        Stack shape : LBRACKET constant_expr.
        Start symbol: translation_unit. *)

  | MenhirState169 : (('s, _menhir_box_translation_unit) _menhir_cell1_DOT, _menhir_box_translation_unit) _menhir_state
    (** State 169.
        Stack shape : DOT.
        Start symbol: translation_unit. *)

  | MenhirState170 : ((('s, _menhir_box_translation_unit) _menhir_cell1_DOT, _menhir_box_translation_unit) _menhir_cell1_ident, _menhir_box_translation_unit) _menhir_state
    (** State 170.
        Stack shape : DOT ident.
        Start symbol: translation_unit. *)

  | MenhirState173 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_option_desig_, _menhir_box_translation_unit) _menhir_state
    (** State 173.
        Stack shape : LBRACE option(desig).
        Start symbol: translation_unit. *)

  | MenhirState174 : (('s, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_state
    (** State 174.
        Stack shape : LBRACE.
        Start symbol: translation_unit. *)

  | MenhirState175 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_state
    (** State 175.
        Stack shape : LBRACE init_list.
        Start symbol: translation_unit. *)

  | MenhirState176 : (((('s, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_cell1_COMMA, _menhir_box_translation_unit) _menhir_state
    (** State 176.
        Stack shape : LBRACE init_list COMMA.
        Start symbol: translation_unit. *)

  | MenhirState177 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_cell1_COMMA, _menhir_box_translation_unit) _menhir_cell1_option_desig_, _menhir_box_translation_unit) _menhir_state
    (** State 177.
        Stack shape : LBRACE init_list COMMA option(desig).
        Start symbol: translation_unit. *)

  | MenhirState186 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_state
    (** State 186.
        Stack shape : LPAREN type_name LBRACE init_list.
        Start symbol: translation_unit. *)

  | MenhirState189 : (('s, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_state
    (** State 189.
        Stack shape : spec_qual_list.
        Start symbol: translation_unit. *)

  | MenhirState190 : (('s, _menhir_box_translation_unit) _menhir_cell1_STAR, _menhir_box_translation_unit) _menhir_state
    (** State 190.
        Stack shape : STAR.
        Start symbol: translation_unit. *)

  | MenhirState191 : (('s, _menhir_box_translation_unit) _menhir_cell1_type_qual, _menhir_box_translation_unit) _menhir_state
    (** State 191.
        Stack shape : type_qual.
        Start symbol: translation_unit. *)

  | MenhirState194 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 194.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState195 : (('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_state
    (** State 195.
        Stack shape : pointer.
        Start symbol: translation_unit. *)

  | MenhirState196 : ((('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 196.
        Stack shape : pointer direct_abstract_declarator.
        Start symbol: translation_unit. *)

  | MenhirState198 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_state
    (** State 198.
        Stack shape : direct_abstract_declarator LBRACKET.
        Start symbol: translation_unit. *)

  | MenhirState201 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_state
    (** State 201.
        Stack shape : direct_abstract_declarator lp.
        Start symbol: translation_unit. *)

  | MenhirState210 : (('s, _menhir_box_translation_unit) _menhir_cell1_ALIGNAS, _menhir_box_translation_unit) _menhir_state
    (** State 210.
        Stack shape : ALIGNAS.
        Start symbol: translation_unit. *)

  | MenhirState218 : (((('s, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list, _menhir_box_translation_unit) _menhir_state
    (** State 218.
        Stack shape : direct_abstract_declarator lp parameter_type_list.
        Start symbol: translation_unit. *)

  | MenhirState222 : ((('s, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_list, _menhir_box_translation_unit) _menhir_state
    (** State 222.
        Stack shape : lp parameter_list.
        Start symbol: translation_unit. *)

  | MenhirState225 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 225.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)

  | MenhirState226 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 226.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState227 : (('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_state
    (** State 227.
        Stack shape : pointer.
        Start symbol: translation_unit. *)

  | MenhirState231 : ((('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 231.
        Stack shape : pointer direct_declarator.
        Start symbol: translation_unit. *)

  | MenhirState232 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_state
    (** State 232.
        Stack shape : direct_declarator LBRACKET.
        Start symbol: translation_unit. *)

  | MenhirState235 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_state
    (** State 235.
        Stack shape : direct_declarator lp.
        Start symbol: translation_unit. *)

  | MenhirState236 : (((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list, _menhir_box_translation_unit) _menhir_state
    (** State 236.
        Stack shape : direct_declarator lp parameter_type_list.
        Start symbol: translation_unit. *)

  | MenhirState241 : (('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 241.
        Stack shape : direct_declarator.
        Start symbol: translation_unit. *)

  | MenhirState242 : (('s, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 242.
        Stack shape : direct_abstract_declarator.
        Start symbol: translation_unit. *)

  | MenhirState259 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_state
    (** State 259.
        Stack shape : LPAREN type_name.
        Start symbol: translation_unit. *)

  | MenhirState264 : ((('s, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 264.
        Stack shape : SIZEOF LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState266 : (((('s, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_state
    (** State 266.
        Stack shape : SIZEOF LPAREN type_name.
        Start symbol: translation_unit. *)

  | MenhirState274 : (((('s, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list, _menhir_box_translation_unit) _menhir_state
    (** State 274.
        Stack shape : STRUCT option(ident) struct_decl_list.
        Start symbol: translation_unit. *)

  | MenhirState278 : (('s, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_state
    (** State 278.
        Stack shape : spec_qual_list.
        Start symbol: translation_unit. *)

  | MenhirState279 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 279.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState280 : (('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_state
    (** State 280.
        Stack shape : pointer.
        Start symbol: translation_unit. *)

  | MenhirState282 : ((('s, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_cell1_struct_declarator_list, _menhir_box_translation_unit) _menhir_state
    (** State 282.
        Stack shape : spec_qual_list struct_declarator_list.
        Start symbol: translation_unit. *)

  | MenhirState285 : (('s, _menhir_box_translation_unit) _menhir_cell1_option_declarator_, _menhir_box_translation_unit) _menhir_state
    (** State 285.
        Stack shape : option(declarator).
        Start symbol: translation_unit. *)

  | MenhirState293 : (((('s, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list, _menhir_box_translation_unit) _menhir_state
    (** State 293.
        Stack shape : UNION option(ident) struct_decl_list.
        Start symbol: translation_unit. *)

  | MenhirState301 : (('s, _menhir_box_translation_unit) _menhir_cell1_external_decl, _menhir_box_translation_unit) _menhir_state
    (** State 301.
        Stack shape : external_decl.
        Start symbol: translation_unit. *)

  | MenhirState303 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 303.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)

  | MenhirState307 : ((('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_init_declarator_list, _menhir_box_translation_unit) _menhir_state
    (** State 307.
        Stack shape : decl_specs init_declarator_list.
        Start symbol: translation_unit. *)

  | MenhirState309 : (('s, _menhir_box_translation_unit) _menhir_cell1_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 309.
        Stack shape : declarator.
        Start symbol: translation_unit. *)

  | MenhirState310 : ((('s, _menhir_box_translation_unit) _menhir_cell1_declarator, _menhir_box_translation_unit) _menhir_cell1_EQ, _menhir_box_translation_unit) _menhir_state
    (** State 310.
        Stack shape : declarator EQ.
        Start symbol: translation_unit. *)

  | MenhirState313 : ((('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 313.
        Stack shape : decl_specs declarator.
        Start symbol: translation_unit. *)

  | MenhirState315 : (('s, _menhir_box_translation_unit) _menhir_cell1_enter_scope, _menhir_box_translation_unit) _menhir_state
    (** State 315.
        Stack shape : enter_scope.
        Start symbol: translation_unit. *)

  | MenhirState317 : (('s, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_state
    (** State 317.
        Stack shape : WHILE.
        Start symbol: translation_unit. *)

  | MenhirState319 : ((('s, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 319.
        Stack shape : WHILE expr.
        Start symbol: translation_unit. *)

  | MenhirState321 : (('s, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_state
    (** State 321.
        Stack shape : SWITCH.
        Start symbol: translation_unit. *)

  | MenhirState323 : ((('s, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 323.
        Stack shape : SWITCH expr.
        Start symbol: translation_unit. *)

  | MenhirState325 : (('s, _menhir_box_translation_unit) _menhir_cell1_RETURN, _menhir_box_translation_unit) _menhir_state
    (** State 325.
        Stack shape : RETURN.
        Start symbol: translation_unit. *)

  | MenhirState330 : (('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_state
    (** State 330.
        Stack shape : IF.
        Start symbol: translation_unit. *)

  | MenhirState332 : ((('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 332.
        Stack shape : IF expr.
        Start symbol: translation_unit. *)

  | MenhirState334 : (('s, _menhir_box_translation_unit) _menhir_cell1_GOTO, _menhir_box_translation_unit) _menhir_state
    (** State 334.
        Stack shape : GOTO.
        Start symbol: translation_unit. *)

  | MenhirState338 : (('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_state
    (** State 338.
        Stack shape : FOR.
        Start symbol: translation_unit. *)

  | MenhirState339 : ((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 339.
        Stack shape : FOR expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState340 : (((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 340.
        Stack shape : FOR expr_stmt expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState342 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 342.
        Stack shape : FOR expr_stmt expr_stmt expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState343 : (('s, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_state
    (** State 343.
        Stack shape : DO.
        Start symbol: translation_unit. *)

  | MenhirState348 : (('s, _menhir_box_translation_unit) _menhir_cell1_CASE, _menhir_box_translation_unit) _menhir_state
    (** State 348.
        Stack shape : CASE.
        Start symbol: translation_unit. *)

  | MenhirState355 : ((('s, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 355.
        Stack shape : DO stmt.
        Start symbol: translation_unit. *)

  | MenhirState363 : (('s, _menhir_box_translation_unit) _menhir_cell1_ident, _menhir_box_translation_unit) _menhir_state
    (** State 363.
        Stack shape : ident.
        Start symbol: translation_unit. *)

  | MenhirState368 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 368.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)

  | MenhirState369 : ((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl, _menhir_box_translation_unit) _menhir_state
    (** State 369.
        Stack shape : FOR decl.
        Start symbol: translation_unit. *)

  | MenhirState370 : (((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 370.
        Stack shape : FOR decl expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState372 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 372.
        Stack shape : FOR decl expr_stmt expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState375 : (((('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 375.
        Stack shape : IF expr stmt.
        Start symbol: translation_unit. *)

  | MenhirState384 : (('s, _menhir_box_translation_unit) _menhir_cell1_item, _menhir_box_translation_unit) _menhir_state
    (** State 384.
        Stack shape : item.
        Start symbol: translation_unit. *)


and ('s, 'r) _menhir_cell1_additive_expr = 
  | MenhirCell1_additive_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_and_expr = 
  | MenhirCell1_and_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_argument_expr_list = 
  | MenhirCell1_argument_expr_list of 's * ('s, 'r) _menhir_state * (Ast.expr list)

and ('s, 'r) _menhir_cell1_constant_expr = 
  | MenhirCell1_constant_expr of 's * ('s, 'r) _menhir_state * (int)

and ('s, 'r) _menhir_cell1_decl = 
  | MenhirCell1_decl of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_decl_specs = 
  | MenhirCell1_decl_specs of 's * ('s, 'r) _menhir_state * (Ctype.ty)

and ('s, 'r) _menhir_cell1_declarator = 
  | MenhirCell1_declarator of 's * ('s, 'r) _menhir_state * (declarator)

and ('s, 'r) _menhir_cell1_direct_abstract_declarator = 
  | MenhirCell1_direct_abstract_declarator of 's * ('s, 'r) _menhir_state * (declarator)

and ('s, 'r) _menhir_cell1_direct_declarator = 
  | MenhirCell1_direct_declarator of 's * ('s, 'r) _menhir_state * (declarator)

and ('s, 'r) _menhir_cell1_enter_declarator = 
  | MenhirCell1_enter_declarator of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_enter_scope = 
  | MenhirCell1_enter_scope of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_enum_const = 
  | MenhirCell1_enum_const of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_enum_list = 
  | MenhirCell1_enum_list of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_equality_expr = 
  | MenhirCell1_equality_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_exclusive_or_expr = 
  | MenhirCell1_exclusive_or_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_expr_stmt = 
  | MenhirCell1_expr_stmt of 's * ('s, 'r) _menhir_state * (Ast.expr option)

and ('s, 'r) _menhir_cell1_external_decl = 
  | MenhirCell1_external_decl of 's * ('s, 'r) _menhir_state * (Ast.def list)

and ('s, 'r) _menhir_cell1_ident = 
  | MenhirCell1_ident of 's * ('s, 'r) _menhir_state * (string)

and ('s, 'r) _menhir_cell1_inclusive_or_expr = 
  | MenhirCell1_inclusive_or_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_init_declarator_list = 
  | MenhirCell1_init_declarator_list of 's * ('s, 'r) _menhir_state * ((declarator * Ast.init option) list)

and ('s, 'r) _menhir_cell1_init_list = 
  | MenhirCell1_init_list of 's * ('s, 'r) _menhir_state * ((Ast.desig option * Ast.init) list)

and ('s, 'r) _menhir_cell1_item = 
  | MenhirCell1_item of 's * ('s, 'r) _menhir_state * (Ast.stmt list)

and ('s, 'r) _menhir_cell1_list_item_ = 
  | MenhirCell1_list_item_ of 's * ('s, 'r) _menhir_state * (Ast.stmt list list)

and ('s, 'r) _menhir_cell1_logical_and_expr = 
  | MenhirCell1_logical_and_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_logical_or_expr = 
  | MenhirCell1_logical_or_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_lp = 
  | MenhirCell1_lp of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_multiplicative_expr = 
  | MenhirCell1_multiplicative_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_option_declarator_ = 
  | MenhirCell1_option_declarator_ of 's * ('s, 'r) _menhir_state * (declarator option)

and ('s, 'r) _menhir_cell1_option_desig_ = 
  | MenhirCell1_option_desig_ of 's * ('s, 'r) _menhir_state * (Ast.desig option)

and ('s, 'r) _menhir_cell1_option_ident_ = 
  | MenhirCell1_option_ident_ of 's * ('s, 'r) _menhir_state * (string option)

and ('s, 'r) _menhir_cell1_parameter_list = 
  | MenhirCell1_parameter_list of 's * ('s, 'r) _menhir_state * (Ctype.decl list)

and ('s, 'r) _menhir_cell1_parameter_type_list = 
  | MenhirCell1_parameter_type_list of 's * ('s, 'r) _menhir_state * (Ctype.decl list)

and ('s, 'r) _menhir_cell1_pointer = 
  | MenhirCell1_pointer of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_postfix_expr = 
  | MenhirCell1_postfix_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_relational_expr = 
  | MenhirCell1_relational_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_shift_expr = 
  | MenhirCell1_shift_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_spec_qual_list = 
  | MenhirCell1_spec_qual_list of 's * ('s, 'r) _menhir_state * (Ctype.ds list)

and ('s, 'r) _menhir_cell1_stmt = 
  | MenhirCell1_stmt of 's * ('s, 'r) _menhir_state * (Ast.stmt)

and ('s, 'r) _menhir_cell1_struct_decl_list = 
  | MenhirCell1_struct_decl_list of 's * ('s, 'r) _menhir_state * (Ctype.decl list)

and ('s, 'r) _menhir_cell1_struct_declarator_list = 
  | MenhirCell1_struct_declarator_list of 's * ('s, 'r) _menhir_state * (declarator list)

and ('s, 'r) _menhir_cell1_type_name = 
  | MenhirCell1_type_name of 's * ('s, 'r) _menhir_state * (Ctype.ty)

and ('s, 'r) _menhir_cell1_type_qual = 
  | MenhirCell1_type_qual of 's * ('s, 'r) _menhir_state * (Ctype.tq)

and ('s, 'r) _menhir_cell1_type_spec = 
  | MenhirCell1_type_spec of 's * ('s, 'r) _menhir_state * (Ctype.ts)

and ('s, 'r) _menhir_cell1_unary_expr = 
  | MenhirCell1_unary_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_ALIGNAS = 
  | MenhirCell1_ALIGNAS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_AND = 
  | MenhirCell1_AND of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_BANG = 
  | MenhirCell1_BANG of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_CASE = 
  | MenhirCell1_CASE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_COMMA = 
  | MenhirCell1_COMMA of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DEC = 
  | MenhirCell1_DEC of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DO = 
  | MenhirCell1_DO of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DOT = 
  | MenhirCell1_DOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ENUM = 
  | MenhirCell1_ENUM of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_EQ = 
  | MenhirCell1_EQ of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FOR = 
  | MenhirCell1_FOR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_GOTO = 
  | MenhirCell1_GOTO of 's * ('s, 'r) _menhir_state

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 263 "src/parser.mly"
      (string)
# 1231 "src/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_INC = 
  | MenhirCell1_INC of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACKET = 
  | MenhirCell1_LBRACKET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PLUS = 
  | MenhirCell1_PLUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SIZEOF = 
  | MenhirCell1_SIZEOF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_STAR = 
  | MenhirCell1_STAR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_STATIC_ASSERT = 
  | MenhirCell1_STATIC_ASSERT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_STRUCT = 
  | MenhirCell1_STRUCT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SWITCH = 
  | MenhirCell1_SWITCH of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_UNION = 
  | MenhirCell1_UNION of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_WHILE = 
  | MenhirCell1_WHILE of 's * ('s, 'r) _menhir_state

and _menhir_box_translation_unit = 
  | MenhirBox_translation_unit of (Ast.program) [@@unboxed]

let _menhir_action_001 =
  fun () ->
    (
# 589 "src/parser.mly"
          ( DeclPtr (DeclIdent "") )
# 1290 "src/parser.ml"
     : (declarator))

let _menhir_action_002 =
  fun _2 ->
    (
# 590 "src/parser.mly"
                                     ( DeclPtr _2 )
# 1298 "src/parser.ml"
     : (declarator))

let _menhir_action_003 =
  fun _1 ->
    (
# 591 "src/parser.mly"
                             ( _1 )
# 1306 "src/parser.ml"
     : (declarator))

let _menhir_action_004 =
  fun _1 ->
    (
# 338 "src/parser.mly"
                      ( _1 )
# 1314 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_005 =
  fun _1 _3 ->
    (
# 339 "src/parser.mly"
                                         ( EBinary(Add,_1,_3) )
# 1322 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_006 =
  fun _1 _3 ->
    (
# 340 "src/parser.mly"
                                          ( EBinary(Sub,_1,_3) )
# 1330 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_007 =
  fun () ->
    (
# 478 "src/parser.mly"
  ( raise (NotImpl "ALIGNAS") )
# 1338 "src/parser.ml"
     : ('tv_alignment_spec))

let _menhir_action_008 =
  fun () ->
    (
# 478 "src/parser.mly"
  ( raise (NotImpl "ALIGNAS") )
# 1346 "src/parser.ml"
     : ('tv_alignment_spec))

let _menhir_action_009 =
  fun _1 ->
    (
# 360 "src/parser.mly"
                ( _1 )
# 1354 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_010 =
  fun _1 _3 ->
    (
# 361 "src/parser.mly"
                             ( EBinary(BitAnd,_1,_3) )
# 1362 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_011 =
  fun _1 ->
    (
# 310 "src/parser.mly"
                  ( [_1] )
# 1370 "src/parser.ml"
     : (Ast.expr list))

let _menhir_action_012 =
  fun _1 _3 ->
    (
# 311 "src/parser.mly"
                                           ( _1@[_3] )
# 1378 "src/parser.ml"
     : (Ast.expr list))

let _menhir_action_013 =
  fun _1 ->
    (
# 384 "src/parser.mly"
                   ( _1 )
# 1386 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_014 =
  fun _1 _3 ->
    (
# 385 "src/parser.mly"
                                ( EAssign(None, _1,_3) )
# 1394 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_015 =
  fun _1 _3 ->
    (
# 386 "src/parser.mly"
                                    ( EAssign(Some Mul, _1,_3) )
# 1402 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_016 =
  fun _1 _3 ->
    (
# 387 "src/parser.mly"
                                    ( EAssign(Some Div, _1,_3) )
# 1410 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_017 =
  fun _1 _3 ->
    (
# 388 "src/parser.mly"
                                    ( EAssign(Some Mod, _1,_3) )
# 1418 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_018 =
  fun _1 _3 ->
    (
# 389 "src/parser.mly"
                                    ( EAssign(Some Add, _1,_3) )
# 1426 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_019 =
  fun _1 _3 ->
    (
# 390 "src/parser.mly"
                                    ( EAssign(Some Sub, _1,_3) )
# 1434 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_020 =
  fun _1 _3 ->
    (
# 391 "src/parser.mly"
                                       ( EAssign(Some LShift, _1,_3) )
# 1442 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_021 =
  fun _1 _3 ->
    (
# 392 "src/parser.mly"
                                       ( EAssign(Some RShift, _1,_3) )
# 1450 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_022 =
  fun _1 _3 ->
    (
# 393 "src/parser.mly"
                                    ( EAssign(Some BitAnd, _1,_3) )
# 1458 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_023 =
  fun _1 _3 ->
    (
# 394 "src/parser.mly"
                                    ( EAssign(Some BitXor, _1,_3) )
# 1466 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_024 =
  fun _1 _3 ->
    (
# 395 "src/parser.mly"
                                   ( EAssign(Some BitOr, _1,_3) )
# 1474 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_025 =
  fun _1 ->
    (
# 328 "src/parser.mly"
             ( _1 )
# 1482 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_026 =
  fun _2 _4 ->
    (
# 329 "src/parser.mly"
                                    ( ECast(_2,_4) )
# 1490 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_027 =
  fun _3 ->
    (
# 654 "src/parser.mly"
 (
    SStmts(List.flatten _3)
  )
# 1500 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_028 =
  fun _1 ->
    (
# 380 "src/parser.mly"
                  ( _1 )
# 1508 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_029 =
  fun _1 _3 _5 ->
    (
# 381 "src/parser.mly"
                                                       ( ECond(_1,_3,_5) )
# 1516 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_030 =
  fun () ->
    (
# 403 "src/parser.mly"
  ( 0 )
# 1524 "src/parser.ml"
     : (int))

let _menhir_action_031 =
  fun () ->
    (
# 406 "src/parser.mly"
                  ( () )
# 1532 "src/parser.ml"
     : (unit))

let _menhir_action_032 =
  fun _1 _2 ->
    (
# 408 "src/parser.mly"
  ( 
    let defs = List.map make_var_or_typedef (make_decls_with_init_opts _1 _2) in
    List.iter add_def defs
  )
# 1543 "src/parser.ml"
     : (unit))

let _menhir_action_033 =
  fun () ->
    (
# 412 "src/parser.mly"
                      ( raise (NotImpl "Static_assert") )
# 1551 "src/parser.ml"
     : (unit))

let _menhir_action_034 =
  fun _1 ->
    (
# 415 "src/parser.mly"
                     ( TDeclSpec [Scs _1] )
# 1559 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_035 =
  fun _1 ->
    (
# 416 "src/parser.mly"
            ( TDeclSpec [Tq _1] )
# 1567 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_036 =
  fun _1 ->
    (
# 417 "src/parser.mly"
                ( TDeclSpec [Fs _1] )
# 1575 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_037 =
  fun () ->
    (
# 418 "src/parser.mly"
                 ( raise (NotImpl "not implemented") )
# 1583 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_038 =
  fun _1 ->
    (
# 419 "src/parser.mly"
            ( TDeclSpec [Ts _1] )
# 1591 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_039 =
  fun _1 ->
    (
# 422 "src/parser.mly"
            ( _1 )
# 1599 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_040 =
  fun _1 _2 ->
    (
# 424 "src/parser.mly"
  ( append_ds_list [_1] [_2] )
# 1607 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_041 =
  fun _2 ->
    (
# 530 "src/parser.mly"
                            ( DeclPtr _2 )
# 1615 "src/parser.ml"
     : (declarator))

let _menhir_action_042 =
  fun _1 ->
    (
# 531 "src/parser.mly"
                    ( _1 )
# 1623 "src/parser.ml"
     : (declarator))

let _menhir_action_043 =
  fun _1 ->
    (
# 613 "src/parser.mly"
  ( _1 )
# 1631 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_044 =
  fun _2 ->
    (
# 616 "src/parser.mly"
                                  ( DIdx(_2,None) )
# 1639 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_045 =
  fun _2 ->
    (
# 617 "src/parser.mly"
            ( DField(_2,None) )
# 1647 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_046 =
  fun _2 _4 ->
    (
# 618 "src/parser.mly"
                                                  (DIdx(_2,Some _4) )
# 1655 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_047 =
  fun _2 _3 ->
    (
# 619 "src/parser.mly"
                            ( DField(_2,Some _3) )
# 1663 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_048 =
  fun _2 ->
    (
# 594 "src/parser.mly"
                                    ( _2 )
# 1671 "src/parser.ml"
     : (declarator))

let _menhir_action_049 =
  fun _1 _3 ->
    (
# 595 "src/parser.mly"
                                                             ( DeclArr(_1,_3) )
# 1679 "src/parser.ml"
     : (declarator))

let _menhir_action_050 =
  fun _1 _3 ->
    (
# 596 "src/parser.mly"
                                                       ( DeclFun(_1,_3) )
# 1687 "src/parser.ml"
     : (declarator))

let _menhir_action_051 =
  fun _2 ->
    (
# 547 "src/parser.mly"
                                       ( DeclIdent _2 )
# 1695 "src/parser.ml"
     : (declarator))

let _menhir_action_052 =
  fun _2 ->
    (
# 548 "src/parser.mly"
                           ( _2 )
# 1703 "src/parser.ml"
     : (declarator))

let _menhir_action_053 =
  fun _1 _3 ->
    (
# 549 "src/parser.mly"
                                                    ( DeclArr(_1, _3) )
# 1711 "src/parser.ml"
     : (declarator))

let _menhir_action_054 =
  fun _1 _3 ->
    (
# 550 "src/parser.mly"
                                              ( DeclFun(_1,_3) )
# 1719 "src/parser.ml"
     : (declarator))

let _menhir_action_055 =
  fun () ->
    (
# 536 "src/parser.mly"
  (
    in_declarator := true
  )
# 1729 "src/parser.ml"
     : (unit))

let _menhir_action_056 =
  fun () ->
    (
# 626 "src/parser.mly"
  (
    stack := !curr_scope::!stack
  )
# 1739 "src/parser.ml"
     : (unit))

let _menhir_action_057 =
  fun () ->
    (
# 523 "src/parser.mly"
    (  )
# 1747 "src/parser.ml"
     : (unit))

let _menhir_action_058 =
  fun () ->
    (
# 523 "src/parser.mly"
    (  )
# 1755 "src/parser.ml"
     : (unit))

let _menhir_action_059 =
  fun () ->
    (
# 527 "src/parser.mly"
    (  )
# 1763 "src/parser.ml"
     : (unit))

let _menhir_action_060 =
  fun () ->
    (
# 518 "src/parser.mly"
    ()
# 1771 "src/parser.ml"
     : (unit))

let _menhir_action_061 =
  fun () ->
    (
# 518 "src/parser.mly"
    ()
# 1779 "src/parser.ml"
     : (unit))

let _menhir_action_062 =
  fun () ->
    (
# 513 "src/parser.mly"
    ( raise (NotImpl "enum_spec") )
# 1787 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_063 =
  fun () ->
    (
# 513 "src/parser.mly"
    ( raise (NotImpl "enum_spec") )
# 1795 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_064 =
  fun _1 ->
    (
# 355 "src/parser.mly"
                  ( _1 )
# 1803 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_065 =
  fun _1 _3 ->
    (
# 356 "src/parser.mly"
                                     ( EBinary(Eq,_1,_3) )
# 1811 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_066 =
  fun _1 _3 ->
    (
# 357 "src/parser.mly"
                                   ( EBinary(Ne,_1,_3) )
# 1819 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_067 =
  fun _1 ->
    (
# 364 "src/parser.mly"
           ( _1 )
# 1827 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_068 =
  fun _1 _3 ->
    (
# 365 "src/parser.mly"
                                 ( EBinary(BitXor,_1,_3) )
# 1835 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_069 =
  fun _1 ->
    (
# 398 "src/parser.mly"
                  ( _1 )
# 1843 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_070 =
  fun _1 _3 ->
    (
# 399 "src/parser.mly"
                             ( EBinary(Comma,_1,_3) )
# 1851 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_071 =
  fun () ->
    (
# 659 "src/parser.mly"
       ( None )
# 1859 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_072 =
  fun _1 ->
    (
# 660 "src/parser.mly"
            ( Some _1 )
# 1867 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_073 =
  fun _1 ->
    (
# 684 "src/parser.mly"
               ( _1 )
# 1875 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_074 =
  fun () ->
    (
# 686 "src/parser.mly"
  ( get_stack () )
# 1883 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_075 =
  fun _1 _2 _3 ->
    (
# 692 "src/parser.mly"
  (
    let decl = make_decl _1 _2 in
    get_stack ()@[(gen_id (),Function(get_stack2 ()@get_params (snd decl),decl,Some _3))]
  )
# 1894 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_076 =
  fun () ->
    (
# 472 "src/parser.mly"
         ( FsInline )
# 1902 "src/parser.ml"
     : (Ctype.fs))

let _menhir_action_077 =
  fun () ->
    (
# 473 "src/parser.mly"
           ( FsNoreturn )
# 1910 "src/parser.ml"
     : (Ctype.fs))

let _menhir_action_078 =
  fun _1 ->
    (
# 279 "src/parser.mly"
     ( _1 )
# 1918 "src/parser.ml"
     : (string))

let _menhir_action_079 =
  fun _1 ->
    (
# 280 "src/parser.mly"
          ( _1 )
# 1926 "src/parser.ml"
     : (string))

let _menhir_action_080 =
  fun _1 ->
    (
# 368 "src/parser.mly"
                    ( _1 )
# 1934 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_081 =
  fun _1 _3 ->
    (
# 369 "src/parser.mly"
                                         ( EBinary(BitOr,_1,_3) )
# 1942 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_082 =
  fun _1 ->
    (
# 604 "src/parser.mly"
                  ( IScal _1 )
# 1950 "src/parser.ml"
     : (Ast.init))

let _menhir_action_083 =
  fun _2 ->
    (
# 605 "src/parser.mly"
                                 ( IVect _2 )
# 1958 "src/parser.ml"
     : (Ast.init))

let _menhir_action_084 =
  fun _1 ->
    (
# 433 "src/parser.mly"
             ( (_1,None) )
# 1966 "src/parser.ml"
     : (declarator * Ast.init option))

let _menhir_action_085 =
  fun _1 _3 ->
    (
# 435 "src/parser.mly"
  ( (_1,Some _3) )
# 1974 "src/parser.ml"
     : (declarator * Ast.init option))

let _menhir_action_086 =
  fun _1 ->
    (
# 428 "src/parser.mly"
  ( [_1] )
# 1982 "src/parser.ml"
     : ((declarator * Ast.init option) list))

let _menhir_action_087 =
  fun _1 _3 ->
    (
# 430 "src/parser.mly"
  ( _1@[_3] )
# 1990 "src/parser.ml"
     : ((declarator * Ast.init option) list))

let _menhir_action_088 =
  fun _1 _2 ->
    (
# 608 "src/parser.mly"
              ( [(_1,_2)] )
# 1998 "src/parser.ml"
     : ((Ast.desig option * Ast.init) list))

let _menhir_action_089 =
  fun _1 _3 _4 ->
    (
# 609 "src/parser.mly"
                              ( _1@[(_3,_4)] )
# 2006 "src/parser.ml"
     : ((Ast.desig option * Ast.init) list))

let _menhir_action_090 =
  fun () ->
    (
# 636 "src/parser.mly"
       ( List.map (fun def -> SDef def) (get_stack ()) )
# 2014 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_091 =
  fun _1 ->
    (
# 637 "src/parser.mly"
       ( [_1] )
# 2022 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_092 =
  fun _3 _5 ->
    (
# 668 "src/parser.mly"
                                ( SWhile(_3,_5) )
# 2030 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_093 =
  fun _2 _5 ->
    (
# 669 "src/parser.mly"
                                   (  SDoWhile(_2,_5) )
# 2038 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_094 =
  fun _3 _4 _5 _7 ->
    (
# 670 "src/parser.mly"
                                                       ( SFor(expr_conv _3,_4,_5,_7) )
# 2046 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_095 =
  fun _4 _5 _7 ->
    (
# 672 "src/parser.mly"
  ( 
    let stmt = SStmts(List.map (fun def -> SDef def) (get_stack ())) in
    SFor(stmt,_4,_5,_7)
  )
# 2057 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_096 =
  fun _2 ->
    (
# 678 "src/parser.mly"
                  ( SGoto _2)
# 2065 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_097 =
  fun () ->
    (
# 679 "src/parser.mly"
                ( SContinue )
# 2073 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_098 =
  fun () ->
    (
# 680 "src/parser.mly"
             ( SBreak )
# 2081 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_099 =
  fun _2 ->
    (
# 681 "src/parser.mly"
                   ( SReturn _2 )
# 2089 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_100 =
  fun _1 _3 ->
    (
# 648 "src/parser.mly"
                   ( SLabel(_1,_3) )
# 2097 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_101 =
  fun _2 ->
    (
# 649 "src/parser.mly"
                              ( SCase _2 )
# 2105 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_102 =
  fun () ->
    (
# 650 "src/parser.mly"
                ( SDefault )
# 2113 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_103 =
  fun () ->
    (
# 542 "src/parser.mly"
  (
    in_declarator := false
  )
# 2123 "src/parser.ml"
     : (unit))

let _menhir_action_104 =
  fun () ->
    (
# 631 "src/parser.mly"
  (
    stack := List.tl !stack
  )
# 2133 "src/parser.ml"
     : (unit))

let _menhir_action_105 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2141 "src/parser.ml"
     : (Ast.def list list))

let _menhir_action_106 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2149 "src/parser.ml"
     : (Ast.def list list))

let _menhir_action_107 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2157 "src/parser.ml"
     : (Ast.stmt list list))

let _menhir_action_108 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2165 "src/parser.ml"
     : (Ast.stmt list list))

let _menhir_action_109 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2173 "src/parser.ml"
     : (Ctype.tq list))

let _menhir_action_110 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2181 "src/parser.ml"
     : (Ctype.tq list))

let _menhir_action_111 =
  fun _1 ->
    (
# 372 "src/parser.mly"
                    ( _1 )
# 2189 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_112 =
  fun _1 _3 ->
    (
# 373 "src/parser.mly"
                                            ( EBinary(LogAnd,_1,_3) )
# 2197 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_113 =
  fun _1 ->
    (
# 376 "src/parser.mly"
                   ( _1 )
# 2205 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_114 =
  fun _1 _3 ->
    (
# 377 "src/parser.mly"
                                        ( EBinary(LogOr,_1,_3) )
# 2213 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_115 =
  fun () ->
    (
# 558 "src/parser.mly"
  ( enter_params () )
# 2221 "src/parser.ml"
     : (unit))

let _menhir_action_116 =
  fun _1 ->
    (
# 332 "src/parser.mly"
            ( _1 )
# 2229 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_117 =
  fun _1 _3 ->
    (
# 333 "src/parser.mly"
                                     ( EBinary(Mul,_1,_3) )
# 2237 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_118 =
  fun _1 _3 ->
    (
# 334 "src/parser.mly"
                                    ( EBinary(Div,_1,_3) )
# 2245 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_119 =
  fun _1 _3 ->
    (
# 335 "src/parser.mly"
                                    ( EBinary(Mod,_1,_3) )
# 2253 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_120 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2261 "src/parser.ml"
     : (unit option))

let _menhir_action_121 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2269 "src/parser.ml"
     : (unit option))

let _menhir_action_122 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2277 "src/parser.ml"
     : (unit option))

let _menhir_action_123 =
  fun () ->
    let x = 
# 567 "src/parser.mly"
                                       ()
# 2285 "src/parser.ml"
     in
    (
# 113 "<standard.mly>"
    ( Some x )
# 2290 "src/parser.ml"
     : (unit option))

let _menhir_action_124 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2298 "src/parser.ml"
     : (declarator option))

let _menhir_action_125 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2306 "src/parser.ml"
     : (declarator option))

let _menhir_action_126 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2314 "src/parser.ml"
     : (Ast.expr list option))

let _menhir_action_127 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2322 "src/parser.ml"
     : (Ast.expr list option))

let _menhir_action_128 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2330 "src/parser.ml"
     : (declarator option))

let _menhir_action_129 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2338 "src/parser.ml"
     : (declarator option))

let _menhir_action_130 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2346 "src/parser.ml"
     : (Ast.desig option))

let _menhir_action_131 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2354 "src/parser.ml"
     : (Ast.desig option))

let _menhir_action_132 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2362 "src/parser.ml"
     : (string option))

let _menhir_action_133 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2370 "src/parser.ml"
     : (string option))

let _menhir_action_134 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2378 "src/parser.ml"
     : (declarator list option))

let _menhir_action_135 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2386 "src/parser.ml"
     : (declarator list option))

let _menhir_action_136 =
  fun _1 _2 ->
    (
# 578 "src/parser.mly"
  ( 
    [make_decl _1 _2]
  )
# 2396 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_137 =
  fun _1 _2 ->
    (
# 582 "src/parser.mly"
  (
    match _2 with
    | Some d -> [make_decl _1 d]
    | None -> [make_decl _1 (DeclIdent "")]
  )
# 2408 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_138 =
  fun _1 ->
    (
# 572 "src/parser.mly"
  ( _1 )
# 2416 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_139 =
  fun _1 _3 ->
    (
# 574 "src/parser.mly"
  ( _1@_3 )
# 2424 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_140 =
  fun () ->
    (
# 566 "src/parser.mly"
  ( [] )
# 2432 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_141 =
  fun _1 ->
    (
# 568 "src/parser.mly"
  ( _1 )
# 2440 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_142 =
  fun () ->
    (
# 554 "src/parser.mly"
  (  )
# 2448 "src/parser.ml"
     : (unit))

let _menhir_action_143 =
  fun _1 ->
    (
# 295 "src/parser.mly"
               ( _1 )
# 2456 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_144 =
  fun _1 _3 ->
    (
# 296 "src/parser.mly"
                                      ( EPostfix(_1,Nth _3) )
# 2464 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_145 =
  fun _1 _3 ->
    (
# 298 "src/parser.mly"
  ( 
    match _3 with
    | Some l -> EPostfix(_1,Call l)
    | None -> EPostfix(_1,Call [])
  )
# 2476 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_146 =
  fun _1 _3 ->
    (
# 303 "src/parser.mly"
                         ( EPostfix(_1,Member _3) )
# 2484 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_147 =
  fun _1 _3 ->
    (
# 304 "src/parser.mly"
                           ( EPostfix(EUnary(Deref,_1),Member _3) )
# 2492 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_148 =
  fun _1 ->
    (
# 305 "src/parser.mly"
                   ( EPostfix(_1,Inc) )
# 2500 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_149 =
  fun _1 ->
    (
# 306 "src/parser.mly"
                   ( EPostfix(_1,Dec) )
# 2508 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_150 =
  fun _2 _5 ->
    (
# 307 "src/parser.mly"
                                                         ( ECompoundLit(_2,IVect _5) )
# 2516 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_151 =
  fun _1 ->
    (
# 283 "src/parser.mly"
     ( EVar (get_var _1) )
# 2524 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_152 =
  fun _1 ->
    (
# 284 "src/parser.mly"
      ( EConst (VInt _1) )
# 2532 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_153 =
  fun _1 ->
    (
# 285 "src/parser.mly"
       ( ECast(TDeclSpec[(Ts TsUInt)],EConst(VInt _1)) )
# 2540 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_154 =
  fun _1 ->
    (
# 286 "src/parser.mly"
       ( ECast(TDeclSpec[(Ts TsLong)],EConst(VInt _1)) )
# 2548 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_155 =
  fun _1 ->
    (
# 287 "src/parser.mly"
        ( ECast(TDeclSpec[(Ts TsULong)],EConst(VInt _1)) )
# 2556 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_156 =
  fun _1 ->
    (
# 288 "src/parser.mly"
        ( EConst (VFloat _1) )
# 2564 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_157 =
  fun _1 ->
    (
# 289 "src/parser.mly"
         ( ECast(TDeclSpec[(Ts TsDouble)],EConst(VFloat _1)) )
# 2572 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_158 =
  fun _1 ->
    (
# 290 "src/parser.mly"
      ( EConst (VStr _1) )
# 2580 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_159 =
  fun _2 ->
    (
# 292 "src/parser.mly"
   ( _2 )
# 2588 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_160 =
  fun _1 ->
    (
# 348 "src/parser.mly"
             ( _1 )
# 2596 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_161 =
  fun _1 _3 ->
    (
# 349 "src/parser.mly"
                                ( EBinary(Lt,_1,_3) )
# 2604 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_162 =
  fun _1 _3 ->
    (
# 350 "src/parser.mly"
                                ( EBinary(Gt,_1,_3) )
# 2612 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_163 =
  fun _1 _3 ->
    (
# 351 "src/parser.mly"
                                ( EBinary(Le,_1,_3) )
# 2620 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_164 =
  fun _1 _3 ->
    (
# 352 "src/parser.mly"
                                ( EBinary(Ge,_1,_3) )
# 2628 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_165 =
  fun () ->
    (
# 562 "src/parser.mly"
  ( leave_params () )
# 2636 "src/parser.ml"
     : (unit))

let _menhir_action_166 =
  fun _3 _5 ->
    (
# 663 "src/parser.mly"
                                              ( SIfElse(_3,_5,SStmts []) )
# 2644 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_167 =
  fun _3 _5 _7 ->
    (
# 664 "src/parser.mly"
                                       ( SIfElse(_3,_5,_7) )
# 2652 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_168 =
  fun _3 _5 ->
    (
# 665 "src/parser.mly"
                                 ( SSwitch(_3,_5) )
# 2660 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_169 =
  fun _1 ->
    (
# 343 "src/parser.mly"
                ( _1 )
# 2668 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_170 =
  fun _1 _3 ->
    (
# 344 "src/parser.mly"
                                  ( EBinary(LShift,_1,_3) )
# 2676 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_171 =
  fun _1 _3 ->
    (
# 345 "src/parser.mly"
                                  ( EBinary(RShift,_1,_3) )
# 2684 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_172 =
  fun _1 ->
    (
# 463 "src/parser.mly"
            ( [Ts _1] )
# 2692 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_173 =
  fun _1 _2 ->
    (
# 464 "src/parser.mly"
                           ( (Ts _1)::_2 )
# 2700 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_174 =
  fun _1 _2 ->
    (
# 465 "src/parser.mly"
                           ( (Tq _1)::_2 )
# 2708 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_175 =
  fun () ->
    (
# 623 "src/parser.mly"
  ( raise (NotImpl "_Static_assert") )
# 2716 "src/parser.ml"
     : ('tv_static_assert_decl))

let _menhir_action_176 =
  fun _1 ->
    (
# 640 "src/parser.mly"
               ( _1 )
# 2724 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_177 =
  fun _1 ->
    (
# 641 "src/parser.mly"
                ( _1 )
# 2732 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_178 =
  fun _1 ->
    (
# 642 "src/parser.mly"
            ( expr_conv _1 )
# 2740 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_179 =
  fun _1 ->
    (
# 643 "src/parser.mly"
                 ( _1 )
# 2748 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_180 =
  fun _1 ->
    (
# 644 "src/parser.mly"
                 ( _1 )
# 2756 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_181 =
  fun _1 ->
    (
# 645 "src/parser.mly"
            ( _1 )
# 2764 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_182 =
  fun () ->
    (
# 438 "src/parser.mly"
          ( ScsTypedef )
# 2772 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_183 =
  fun () ->
    (
# 439 "src/parser.mly"
         ( ScsExtern )
# 2780 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_184 =
  fun () ->
    (
# 440 "src/parser.mly"
         ( ScsStatic )
# 2788 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_185 =
  fun () ->
    (
# 441 "src/parser.mly"
       ( ScsAuto )
# 2796 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_186 =
  fun () ->
    (
# 442 "src/parser.mly"
           ( ScsRegister )
# 2804 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_187 =
  fun _1 _2 ->
    (
# 493 "src/parser.mly"
  (
    match _2 with
    | Some dl -> make_decls (TDeclSpec _1) dl
    | None -> raise (NotImpl "struct_decl")
  )
# 2816 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_188 =
  fun () ->
    (
# 499 "src/parser.mly"
  ( raise (NotImpl "Static_assert") )
# 2824 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_189 =
  fun _1 ->
    (
# 488 "src/parser.mly"
              ( _1 )
# 2832 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_190 =
  fun _1 _2 ->
    (
# 489 "src/parser.mly"
                               ( _1@_2 )
# 2840 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_191 =
  fun _1 ->
    (
# 506 "src/parser.mly"
             ( _1 )
# 2848 "src/parser.ml"
     : (declarator))

let _menhir_action_192 =
  fun () ->
    (
# 508 "src/parser.mly"
  ( raise (NotImpl "Bitfield") )
# 2856 "src/parser.ml"
     : (declarator))

let _menhir_action_193 =
  fun _1 ->
    (
# 502 "src/parser.mly"
                    ( [_1] )
# 2864 "src/parser.ml"
     : (declarator list))

let _menhir_action_194 =
  fun _1 _3 ->
    (
# 503 "src/parser.mly"
                                                 ( _1@[_3] )
# 2872 "src/parser.ml"
     : (declarator list))

let _menhir_action_195 =
  fun _2 _4 ->
    (
# 481 "src/parser.mly"
                                               ( make_struct _2 (Some _4) )
# 2880 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_196 =
  fun _2 ->
    (
# 482 "src/parser.mly"
               ( make_struct (Some _2) None )
# 2888 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_197 =
  fun _2 _4 ->
    (
# 483 "src/parser.mly"
                                              ( make_union _2 (Some _4) )
# 2896 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_198 =
  fun _2 ->
    (
# 484 "src/parser.mly"
              ( make_union (Some _2) None )
# 2904 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_199 =
  fun _1 ->
    (
# 276 "src/parser.mly"
  ( Program (List.flatten _1) )
# 2912 "src/parser.ml"
     : (Ast.program))

let _menhir_action_200 =
  fun _1 ->
    (
# 599 "src/parser.mly"
                 ( TDeclSpec _1 )
# 2920 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_201 =
  fun _1 _2 ->
    (
# 601 "src/parser.mly"
  ( snd (make_decl (TDeclSpec _1) _2) )
# 2928 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_202 =
  fun () ->
    (
# 468 "src/parser.mly"
        ( TqConst )
# 2936 "src/parser.ml"
     : (Ctype.tq))

let _menhir_action_203 =
  fun () ->
    (
# 469 "src/parser.mly"
           ( TqVolatile )
# 2944 "src/parser.ml"
     : (Ctype.tq))

let _menhir_action_204 =
  fun () ->
    (
# 445 "src/parser.mly"
        ( TsVoid )
# 2952 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_205 =
  fun () ->
    (
# 446 "src/parser.mly"
        ( TsChar )
# 2960 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_206 =
  fun () ->
    (
# 447 "src/parser.mly"
         ( TsShort)
# 2968 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_207 =
  fun () ->
    (
# 448 "src/parser.mly"
       ( TsInt )
# 2976 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_208 =
  fun () ->
    (
# 449 "src/parser.mly"
        ( TsLong )
# 2984 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_209 =
  fun () ->
    (
# 450 "src/parser.mly"
         ( TsFloat )
# 2992 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_210 =
  fun () ->
    (
# 451 "src/parser.mly"
          ( TsDouble )
# 3000 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_211 =
  fun () ->
    (
# 452 "src/parser.mly"
          ( TsSigned )
# 3008 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_212 =
  fun () ->
    (
# 453 "src/parser.mly"
            ( TsUnsigned )
# 3016 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_213 =
  fun _1 ->
    (
# 454 "src/parser.mly"
                       ( 
  match _1 with
  | (Some def,ts) -> add_def def;ts
  | (None,ts) -> ts
  )
# 3028 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_214 =
  fun _1 ->
    (
# 459 "src/parser.mly"
            ( _1 )
# 3036 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_215 =
  fun _1 ->
    (
# 460 "src/parser.mly"
          ( TsTypedef (get_typedef _1) )
# 3044 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_216 =
  fun _1 ->
    (
# 314 "src/parser.mly"
               ( _1 )
# 3052 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_217 =
  fun _2 ->
    (
# 315 "src/parser.mly"
                 ( EUnary(PreInc, _2) )
# 3060 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_218 =
  fun _2 ->
    (
# 316 "src/parser.mly"
                 ( EUnary(PreDec, _2) )
# 3068 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_219 =
  fun _2 ->
    (
# 317 "src/parser.mly"
                 ( EUnary(Ref, _2) )
# 3076 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_220 =
  fun _2 ->
    (
# 318 "src/parser.mly"
                 ( EUnary(Deref, _2) )
# 3084 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_221 =
  fun _2 ->
    (
# 319 "src/parser.mly"
                 ( EUnary(Plus, _2) )
# 3092 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_222 =
  fun _2 ->
    (
# 320 "src/parser.mly"
                  ( EUnary(Minus, _2) )
# 3100 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_223 =
  fun _2 ->
    (
# 321 "src/parser.mly"
                ( EUnary(BitNot, _2) )
# 3108 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_224 =
  fun _2 ->
    (
# 322 "src/parser.mly"
                 ( EUnary(LogNot, _2) )
# 3116 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_225 =
  fun _2 ->
    (
# 323 "src/parser.mly"
                    ( EUnary(Sizeof, _2) )
# 3124 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_226 =
  fun _3 ->
    (
# 324 "src/parser.mly"
                                 ( ETyUnary(Sizeof,_3) )
# 3132 "src/parser.ml"
     : (Ast.expr))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ADD_EQ ->
        "ADD_EQ"
    | ALIGNAS ->
        "ALIGNAS"
    | AND ->
        "AND"
    | ANDAND ->
        "ANDAND"
    | AND_EQ ->
        "AND_EQ"
    | ARROW ->
        "ARROW"
    | AUTO ->
        "AUTO"
    | BANG ->
        "BANG"
    | BREAK ->
        "BREAK"
    | CASE ->
        "CASE"
    | COLON ->
        "COLON"
    | COMMA ->
        "COMMA"
    | CONST ->
        "CONST"
    | CONTINUE ->
        "CONTINUE"
    | DEC ->
        "DEC"
    | DEFAULT ->
        "DEFAULT"
    | DIV ->
        "DIV"
    | DIV_EQ ->
        "DIV_EQ"
    | DO ->
        "DO"
    | DOT ->
        "DOT"
    | DOUBLE _ ->
        "DOUBLE"
    | ELLIPSIS ->
        "ELLIPSIS"
    | ELSE ->
        "ELSE"
    | ENUM ->
        "ENUM"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | EQEQ ->
        "EQEQ"
    | EXTERN ->
        "EXTERN"
    | FLOAT _ ->
        "FLOAT"
    | FOR ->
        "FOR"
    | GE ->
        "GE"
    | GOTO ->
        "GOTO"
    | GT ->
        "GT"
    | HAT ->
        "HAT"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | INC ->
        "INC"
    | INLINE ->
        "INLINE"
    | INT _ ->
        "INT"
    | LBRACE ->
        "LBRACE"
    | LBRACKET ->
        "LBRACKET"
    | LE ->
        "LE"
    | LINT _ ->
        "LINT"
    | LPAREN ->
        "LPAREN"
    | LSHIFT ->
        "LSHIFT"
    | LSHIFT_EQ ->
        "LSHIFT_EQ"
    | LT ->
        "LT"
    | MINUS ->
        "MINUS"
    | MOD ->
        "MOD"
    | MOD_EQ ->
        "MOD_EQ"
    | MUL_EQ ->
        "MUL_EQ"
    | NE ->
        "NE"
    | NORETURN ->
        "NORETURN"
    | NOT ->
        "NOT"
    | OR ->
        "OR"
    | OROR ->
        "OROR"
    | OR_EQ ->
        "OR_EQ"
    | PLUS ->
        "PLUS"
    | QUESTION ->
        "QUESTION"
    | RBRACE ->
        "RBRACE"
    | RBRACKET ->
        "RBRACKET"
    | REGISTER ->
        "REGISTER"
    | RETURN ->
        "RETURN"
    | RPAREN ->
        "RPAREN"
    | RSHIFT ->
        "RSHIFT"
    | RSHIFT_EQ ->
        "RSHIFT_EQ"
    | SEMI ->
        "SEMI"
    | SIZEOF ->
        "SIZEOF"
    | STAR ->
        "STAR"
    | STATIC ->
        "STATIC"
    | STATIC_ASSERT ->
        "STATIC_ASSERT"
    | STR _ ->
        "STR"
    | STRUCT ->
        "STRUCT"
    | SUB_EQ ->
        "SUB_EQ"
    | SWITCH ->
        "SWITCH"
    | TCHAR ->
        "TCHAR"
    | TDOUBLE ->
        "TDOUBLE"
    | TFLOAT ->
        "TFLOAT"
    | TINT ->
        "TINT"
    | TLONG ->
        "TLONG"
    | TSHORT ->
        "TSHORT"
    | TSIGNED ->
        "TSIGNED"
    | TUNSIGNED ->
        "TUNSIGNED"
    | TVOID ->
        "TVOID"
    | TYPEDEF ->
        "TYPEDEF"
    | TYPE_ID _ ->
        "TYPE_ID"
    | UINT _ ->
        "UINT"
    | ULINT _ ->
        "ULINT"
    | UNION ->
        "UNION"
    | VOLATILE ->
        "VOLATILE"
    | WHILE ->
        "WHILE"
    | XOR_EQ ->
        "XOR_EQ"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_298 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _v ->
      let _1 = _v in
      let _v = _menhir_action_199 _1 in
      MenhirBox_translation_unit _v
  
  let rec _menhir_run_302 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_external_decl -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _v ->
      let MenhirCell1_external_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_106 x xs in
      _menhir_goto_list_external_decl_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_external_decl_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState301 ->
          _menhir_run_302 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_298 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_203 () in
      _menhir_goto_type_qual _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_qual : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState384 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState191 ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState190 ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState293 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState274 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState157 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_216 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_035 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState303 ->
          _menhir_run_249 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState368 ->
          _menhir_run_249 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState225 ->
          _menhir_run_249 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState000 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_249 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_040 _1 _2 in
      _menhir_goto_decl_specs _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl_specs : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_303 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_303 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_368 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState368
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | SEMI ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | LPAREN ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | ID _ ->
          let _menhir_s = MenhirState368 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_002 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_UNION (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState002
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState002
      | LBRACE ->
          let _v = _menhir_action_132 () in
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState002
      | _ ->
          _eRR ()
  
  and _menhir_run_003 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_079 _1 in
      _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_ident : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_362 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_335 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState002 ->
          _menhir_run_295 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_292 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState169 ->
          _menhir_run_170 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState037 ->
          _menhir_run_155 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState144 ->
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState141 ->
          _menhir_run_142 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState042 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState039 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_362 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState363 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_316 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState317 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_155 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_primary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_143 _1 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_postfix_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState052 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RPAREN ->
              let _v = _menhir_action_126 () in
              _menhir_goto_option_argument_expr_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
          | _ ->
              _eRR ())
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState137 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | INC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_148 _1 in
          _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | DOT ->
          let _menhir_stack = MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState141 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | ID _v ->
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | DEC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_149 _1 in
          _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ARROW ->
          let _menhir_stack = MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState144 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | ID _v ->
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | ADD_EQ | AND | ANDAND | AND_EQ | COLON | COMMA | DIV | DIV_EQ | EQ | EQEQ | GE | GT | HAT | LE | LSHIFT | LSHIFT_EQ | LT | MINUS | MOD | MOD_EQ | MUL_EQ | NE | OR | OROR | OR_EQ | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | RSHIFT_EQ | SEMI | STAR | SUB_EQ | XOR_EQ ->
          let _1 = _v in
          let _v = _menhir_action_216 _1 in
          _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_023 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_153 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_158 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_025 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState025 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_026 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SIZEOF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState026 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
          let _menhir_s = MenhirState264 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_027 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PLUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState027 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_028 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState028 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_029 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState029 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_030 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState030 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TYPE_ID _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_007 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_215 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState384 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState293 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState274 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState157 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_215 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_038 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_157 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | UNION ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TYPE_ID _v_0 ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState157
      | TVOID ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TUNSIGNED ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TSIGNED ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TSHORT ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TLONG ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TINT ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TFLOAT ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TDOUBLE ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | TCHAR ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | STRUCT ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | ENUM ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | CONST ->
          let _menhir_stack = MenhirCell1_type_spec (_menhir_stack, _menhir_s, _v) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | COLON | ID _ | LPAREN | RPAREN | SEMI | STAR ->
          let _1 = _v in
          let _v = _menhir_action_172 _1 in
          _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_008 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_204 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_009 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_212 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_211 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_011 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_206 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_012 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_208 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_013 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_207 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_209 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_210 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_205 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState017
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState017
      | LBRACE ->
          let _v = _menhir_action_132 () in
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState017
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_078 _1 in
      _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_018 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STRUCT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_ident_ (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState019 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYPE_ID _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_020 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STATIC_ASSERT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState021 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_031 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_154 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_032 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_152 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_033 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_INC (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState033 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_034 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState034 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TYPE_ID _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_035 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_151 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_036 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_156 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_037 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ENUM (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | LBRACE ->
          let _v = _menhir_action_132 () in
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | _ ->
          _eRR ()
  
  and _menhir_run_038 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_ident_ (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState039 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_045 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_157 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DEC (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState046 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_034 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_047 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_BANG (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState047 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_048 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_AND (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState048 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_156 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_202 () in
      _menhir_goto_type_qual _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_spec_qual_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState293 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState274 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState157 ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState158 ->
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_278 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState278
      | LPAREN ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState278
      | ID _ ->
          let _menhir_s = MenhirState278 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COLON ->
          let _menhir_s = MenhirState278 in
          let _v = _menhir_action_128 () in
          _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | SEMI ->
          let _v = _menhir_action_134 () in
          _menhir_goto_option_struct_declarator_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_190 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState190
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState190
      | COLON | COMMA | ID _ | LPAREN | RPAREN ->
          let _ = _menhir_action_109 () in
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_193 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STAR -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_STAR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_142 () in
      _menhir_goto_pointer _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_pointer : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState368 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState307 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState278 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState282 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState279 ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState189 ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState194 ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_280 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState280
      | ID _ ->
          let _menhir_s = MenhirState280 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_279 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState279 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _ ->
          _menhir_reduce_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_reduce_055 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_055 () in
      _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_enter_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_enter_declarator (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ID _v_0 ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _ = _menhir_action_103 () in
          let MenhirCell0_ID (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_enter_declarator (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let _v = _menhir_action_051 _2 in
          _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_direct_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState368 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState307 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState278 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState282 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState279 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState280 ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_241 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState241
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState241
      | COLON | COMMA | EQ | LBRACE | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_042 _1 in
          _menhir_goto_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_197 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_115 () in
      _menhir_goto_lp _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_lp : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState241 ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState231 ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState242 ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState196 ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_235 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lp (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState235
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState235
      | RPAREN ->
          let _v_1 = _menhir_action_140 () in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState235 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_202 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_182 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_storage_class_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_034 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_203 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_184 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_204 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_186 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_205 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_077 () in
      _menhir_goto_function_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_function_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_036 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_206 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_076 () in
      _menhir_goto_function_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_207 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_183 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_208 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_185 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_209 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ALIGNAS (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState210 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_236 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_parameter_type_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState236
      | _ ->
          _eRR ()
  
  and _menhir_run_219 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _ = _menhir_action_165 () in
      _menhir_goto_rp _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
  
  and _menhir_goto_rp : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      match _menhir_s with
      | MenhirState236 ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState218 ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_237 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_type_list (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_lp (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_054 _1 _3 in
      _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_220 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_type_list (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_lp (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_050 _1 _3 in
      _menhir_goto_direct_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_direct_abstract_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState189 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState194 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState195 ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_242 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState242
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState242
      | COLON | COMMA | RPAREN ->
          let _1 = _v in
          let _v = _menhir_action_003 _1 in
          _menhir_goto_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_198 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState198 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_abstract_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState189 ->
          _menhir_run_254 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState225 ->
          _menhir_run_250 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState194 ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState226 ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_254 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_201 _1 _2 in
      _menhir_goto_type_name _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_name : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState264 ->
          _menhir_run_265 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_258 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState034 ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_265 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACE ->
              let _menhir_stack = MenhirCell1_type_name (_menhir_stack, _menhir_s, _v) in
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState266
          | ADD_EQ | AND | ANDAND | AND_EQ | COLON | COMMA | DIV | DIV_EQ | EQ | EQEQ | GE | GT | HAT | LE | LSHIFT | LSHIFT_EQ | LT | MINUS | MOD | MOD_EQ | MUL_EQ | NE | OR | OROR | OR_EQ | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | RSHIFT_EQ | SEMI | STAR | SUB_EQ | XOR_EQ ->
              let MenhirCell1_LPAREN (_menhir_stack, _) = _menhir_stack in
              let MenhirCell1_SIZEOF (_menhir_stack, _menhir_s) = _menhir_stack in
              let _3 = _v in
              let _v = _menhir_action_226 _3 in
              _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_165 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | DOT ->
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | AND | BANG | DEC | DOUBLE _ | FLOAT _ | ID _ | INC | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NOT | PLUS | SIZEOF | STAR | STR _ | UINT _ | ULINT _ ->
          let _v = _menhir_action_130 () in
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState165 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_166 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState166 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_169 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DOT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState169 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_173 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_option_desig_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState173
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState173
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState173
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState173
      | LBRACE ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState173
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState173
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState173
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState173
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState173
      | _ ->
          _eRR ()
  
  and _menhir_run_174 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | DOT ->
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | AND | BANG | DEC | DOUBLE _ | FLOAT _ | ID _ | INC | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NOT | PLUS | SIZEOF | STAR | STR _ | UINT _ | ULINT _ ->
          let _v = _menhir_action_130 () in
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState174 _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_unary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState026 ->
          _menhir_run_267 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState033 ->
          _menhir_run_257 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState046 ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState384 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState027 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState028 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState029 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState259 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState047 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState093 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState068 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState048 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_267 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SIZEOF -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SIZEOF (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_225 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_257 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_INC -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_INC (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_217 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_148 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DEC -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_DEC (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_218 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_053 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState054 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | SUB_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState111 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RSHIFT_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState113 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | OR_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState115 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | MUL_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState117 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | MOD_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState119 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LSHIFT_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState121 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState123 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | DIV_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState125 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AND_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState127 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | ADD_EQ ->
          let _menhir_stack = MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState129 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AND | ANDAND | COLON | COMMA | DIV | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | MINUS | MOD | NE | OR | OROR | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI | STAR ->
          let _1 = _v in
          let _v = _menhir_action_025 _1 in
          _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_cast_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState025 ->
          _menhir_run_268 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState027 ->
          _menhir_run_263 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState028 ->
          _menhir_run_262 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState029 ->
          _menhir_run_261 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState259 ->
          _menhir_run_260 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState047 ->
          _menhir_run_147 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState048 ->
          _menhir_run_146 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState315 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState093 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState068 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState060 ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState058 ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_268 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STAR -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_STAR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_220 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_263 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_PLUS -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_PLUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_221 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_262 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_223 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_261 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_MINUS -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_222 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_260 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_name (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_026 _2 _4 in
      _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_147 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_BANG -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_BANG (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_224 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_146 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_AND -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AND (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_219 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_116 _1 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_multiplicative_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState068 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState093 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_069 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_additive_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | MINUS | NE | OR | OROR | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_006 _1 _3 in
          _menhir_goto_additive_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_058 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState058 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_060 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState060 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_062 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState062 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_additive_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState093 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_075 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_169 _1 in
          _menhir_goto_shift_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_066 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_additive_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState066 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_068 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_additive_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState068 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_shift_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState080 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState093 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_081 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_164 _1 _3 in
          _menhir_goto_relational_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_056 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_shift_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState056 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_070 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_shift_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState070 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_relational_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState093 ->
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState091 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_094 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_equality_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | HAT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_065 _1 _3 in
          _menhir_goto_equality_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_073 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState073 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_076 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState076 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_078 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState078 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_080 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState080 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_equality_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState096 ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_097 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_and_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | NE ->
          let _menhir_stack = MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | HAT | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_and_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_010 _1 _3 in
          _menhir_goto_and_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_091 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_equality_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState091 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_093 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_equality_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState093 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_and_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState089 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_098 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_and_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | HAT | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_067 _1 in
          _menhir_goto_exclusive_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_096 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_and_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState096 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_exclusive_or_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_099 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | HAT ->
          let _menhir_stack = MenhirCell1_exclusive_or_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_080 _1 in
          _menhir_goto_inclusive_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_089 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_exclusive_or_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState089 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_inclusive_or_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState315 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_100 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_inclusive_or_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_111 _1 in
          _menhir_goto_logical_and_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_087 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_inclusive_or_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState087 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_logical_and_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState108 ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState348 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState285 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_109 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ANDAND ->
          let _menhir_stack = MenhirCell1_logical_and_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COLON | COMMA | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_logical_or_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_114 _1 _3 in
          _menhir_goto_logical_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_085 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_and_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState085 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_logical_or_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | QUESTION ->
          let _menhir_stack = MenhirCell1_logical_or_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState083 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | OROR ->
          let _menhir_stack = MenhirCell1_logical_or_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState108 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COLON | COMMA | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_028 _1 in
          _menhir_goto_conditional_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_conditional_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState348 ->
          _menhir_run_349 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState285 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState315 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState127 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState125 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState123 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState117 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState111 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_349 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_CASE -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_CASE (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_101 _2 in
          _menhir_goto_labeled_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_labeled_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_176 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState384 ->
          _menhir_run_380 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_380 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState323 ->
          _menhir_run_377 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState375 ->
          _menhir_run_376 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState332 ->
          _menhir_run_374 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_373 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState342 ->
          _menhir_run_367 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState363 ->
          _menhir_run_364 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState343 ->
          _menhir_run_353 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_380 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_091 _1 in
      _menhir_goto_item _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_item : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_item (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState384
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState384
      | TYPE_ID _v_2 ->
          _menhir_run_379 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState384
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | SWITCH ->
          _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState384
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | RETURN ->
          _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState384
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState384
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | IF ->
          _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | ID _v_6 ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState384
      | GOTO ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | FOR ->
          _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState384
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState384
      | DO ->
          _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | DEFAULT ->
          _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | CONTINUE ->
          _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | CASE ->
          _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | BREAK ->
          _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState384
      | LBRACE ->
          let _menhir_s = MenhirState384 in
          let _v = _menhir_action_056 () in
          _menhir_goto_enter_scope _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RBRACE ->
          let _v_10 = _menhir_action_107 () in
          _menhir_run_385 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10
      | _ ->
          _eRR ()
  
  and _menhir_run_379 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _1 = _v in
          let _v = _menhir_action_079 _1 in
          _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ALIGNAS | AUTO | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let _1 = _v in
          let _v = _menhir_action_215 _1 in
          _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_320 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SWITCH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState321 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_324 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_071 () in
      _menhir_goto_expr_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState370 ->
          _menhir_run_371 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_370 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_365 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_341 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_339 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_326 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_371 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState372 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_325 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState325 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_329 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState330 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_333 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _1 = _v in
          let _v = _menhir_action_078 _1 in
          _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ADD_EQ | AND | ANDAND | AND_EQ | ARROW | COMMA | DEC | DIV | DIV_EQ | DOT | EQ | EQEQ | GE | GT | HAT | INC | LBRACKET | LE | LPAREN | LSHIFT | LSHIFT_EQ | LT | MINUS | MOD | MOD_EQ | MUL_EQ | NE | OR | OROR | OR_EQ | PLUS | QUESTION | RSHIFT | RSHIFT_EQ | SEMI | STAR | SUB_EQ | XOR_EQ ->
          let _1 = _v in
          let _v = _menhir_action_151 _1 in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_334 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_GOTO (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState334 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_337 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState338 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STATIC_ASSERT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_343 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DO (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState343 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | SWITCH ->
          _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | GOTO ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DO ->
          _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEFAULT ->
          _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONTINUE ->
          _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CASE ->
          _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BREAK ->
          _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACE ->
          _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_344 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_102 () in
          _menhir_goto_labeled_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_346 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_097 () in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_jump_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_181 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_348 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_CASE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState348 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_351 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_098 () in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_reduce_056 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _v = _menhir_action_056 () in
      _menhir_goto_enter_scope _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_enter_scope : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_enter_scope (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState315
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState315
      | TYPE_ID _v_2 ->
          _menhir_run_379 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState315
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | SWITCH ->
          _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState315
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | RETURN ->
          _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState315
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState315
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | IF ->
          _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | ID _v_6 ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState315
      | GOTO ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | FOR ->
          _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState315
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState315
      | DO ->
          _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | DEFAULT ->
          _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | CONTINUE ->
          _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | CASE ->
          _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | BREAK ->
          _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState315
      | LBRACE ->
          let _menhir_s = MenhirState315 in
          let _v = _menhir_action_056 () in
          _menhir_goto_enter_scope _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RBRACE ->
          let _v_10 = _menhir_action_107 () in
          _menhir_run_381 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10 MenhirState315
      | _ ->
          _eRR ()
  
  and _menhir_run_381 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_enter_scope as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_list_item_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _ = _menhir_action_104 () in
      let MenhirCell1_list_item_ (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_enter_scope (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_027 _3 in
      _menhir_goto_compound_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_compound_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState313 ->
          _menhir_run_387 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState315 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_387 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_declarator -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_declarator (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_075 _1 _2 _3 in
      let _1 = _v in
      let _v = _menhir_action_073 _1 in
      _menhir_goto_external_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_external_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_external_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState301
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState301
      | EOF ->
          let _v_1 = _menhir_action_105 () in
          _menhir_run_302 _menhir_stack _v_1
      | _ ->
          _eRR ()
  
  and _menhir_run_366 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_177 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_370 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState370
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState370
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState370
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState370
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState370
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState370
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState370
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState370
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState370
      | _ ->
          _eRR ()
  
  and _menhir_run_365 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_178 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_341 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState342 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_340 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState340
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState340
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState340
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState340
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState340
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState340
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState340
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState340
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState340
      | _ ->
          _eRR ()
  
  and _menhir_run_339 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState339
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState339
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState339
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState339
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState339
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState339
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState339
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState339
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | _ ->
          _eRR ()
  
  and _menhir_run_326 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_RETURN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_RETURN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_099 _2 in
      _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_385 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_item -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_item (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_108 x xs in
      _menhir_goto_list_item_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_item_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState384 ->
          _menhir_run_385 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState315 ->
          _menhir_run_381 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_378 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _5 = _v in
      let _v = _menhir_action_092 _3 _5 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_iteration_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_180 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_377 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_SWITCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let _5 = _v in
      let _v = _menhir_action_168 _3 _5 in
      _menhir_goto_selection_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_selection_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_179 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_376 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_stmt -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_stmt (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let _7 = _v in
      let _v = _menhir_action_167 _3 _5 _7 in
      _menhir_goto_selection_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_374 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState375 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | ALIGNAS | AND | AUTO | BANG | BREAK | CASE | CONST | CONTINUE | DEC | DEFAULT | DO | DOUBLE _ | ENUM | EXTERN | FLOAT _ | FOR | GOTO | ID _ | IF | INC | INLINE | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NORETURN | NOT | PLUS | RBRACE | REGISTER | RETURN | SEMI | SIZEOF | STAR | STATIC | STATIC_ASSERT | STR _ | STRUCT | SWITCH | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UINT _ | ULINT _ | UNION | VOLATILE | WHILE ->
          let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let _5 = _v in
          let _v = _menhir_action_166 _3 _5 in
          _menhir_goto_selection_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_373 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_stmt (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _4) = _menhir_stack in
      let MenhirCell1_decl (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _7 = _v in
      let _v = _menhir_action_095 _4 _5 _7 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_367 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_stmt (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _4) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _7 = _v in
      let _v = _menhir_action_094 _3 _4 _5 _7 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_364 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_100 _1 _3 in
      _menhir_goto_labeled_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_353 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DO as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _menhir_s = MenhirState355 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ULINT _v ->
                  _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | UINT _v ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | STR _v ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | STAR ->
                  _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | SIZEOF ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | PLUS ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | NOT ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LINT _v ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT _v ->
                  _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INC ->
                  _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ID _v ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FLOAT _v ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | DOUBLE _v ->
                  _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | DEC ->
                  _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BANG ->
                  _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | AND ->
                  _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_150 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_030 () in
      _menhir_goto_constant_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_constant_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState285 ->
          _menhir_run_286 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState021 ->
          _menhir_run_269 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState232 ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState210 ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState198 ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState166 ->
          _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState044 ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_286 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_declarator_ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_option_declarator_ (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_192 () in
      _menhir_goto_struct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState278 ->
          _menhir_run_288 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState282 ->
          _menhir_run_283 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_288 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_193 _1 in
      _menhir_goto_struct_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_declarator_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_struct_declarator_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState282 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _ ->
              _menhir_reduce_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
          | COLON ->
              let _v = _menhir_action_128 () in
              _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | SEMI ->
          let x = _v in
          let _v = _menhir_action_135 x in
          _menhir_goto_option_struct_declarator_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_declarator_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_declarator_ (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState285 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_struct_declarator_list_ : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_187 _1 _2 in
      _menhir_goto_struct_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_291 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_291 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState293 ->
          _menhir_run_276 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState274 ->
          _menhir_run_276 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_291 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_189 _1 in
      _menhir_goto_struct_decl_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_decl_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_293 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_274 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_293 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | UNION ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TYPE_ID _v_0 ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState293
      | TVOID ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TUNSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TSHORT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TLONG ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TINT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TFLOAT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TDOUBLE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | TCHAR ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | STRUCT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | STATIC_ASSERT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_option_ident_ (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_UNION (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_197 _2 _4 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ENUM ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | CONST ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState293
      | _ ->
          _eRR ()
  
  and _menhir_goto_struct_or_union_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_213 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_274 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | UNION ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TYPE_ID _v_0 ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState274
      | TVOID ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TUNSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TSHORT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TLONG ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TINT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TFLOAT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TDOUBLE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | TCHAR ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | STRUCT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | STATIC_ASSERT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_option_ident_ (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_195 _2 _4 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ENUM ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | CONST ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState274
      | _ ->
          _eRR ()
  
  and _menhir_run_276 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_190 _1 _2 in
      _menhir_goto_struct_decl_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_283 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_cell1_struct_declarator_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_struct_declarator_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_194 _1 _3 in
      _menhir_goto_struct_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_269 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STATIC_ASSERT -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STR _ ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RPAREN ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | SEMI ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let MenhirCell1_STATIC_ASSERT (_menhir_stack, _menhir_s) = _menhir_stack in
                      let _ = _menhir_action_175 () in
                      _menhir_goto_static_assert_decl _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_static_assert_decl : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      match _menhir_s with
      | MenhirState384 ->
          _menhir_run_297 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_297 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_297 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_297 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_297 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState293 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState274 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_297 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_033 () in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_388 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_388 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_386 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_386 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_369 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_388 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_074 () in
      _menhir_goto_external_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_386 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_090 () in
      _menhir_goto_item _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_369 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState369
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState369
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState369
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | SEMI ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState369
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState369
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState369
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState369
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState369
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState369
      | _ ->
          _eRR ()
  
  and _menhir_run_277 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_188 () in
      _menhir_goto_struct_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_233 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACKET (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_053 _1 _3 in
          _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_213 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ALIGNAS -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_ALIGNAS (_menhir_stack, _menhir_s) = _menhir_stack in
          let _ = _menhir_action_008 () in
          _menhir_goto_alignment_spec _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_alignment_spec : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_037 () in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_199 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACKET (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_049 _1 _3 in
          _menhir_goto_direct_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_167 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACKET as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACKET ->
              let _menhir_stack = MenhirCell1_constant_expr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState168
          | DOT ->
              let _menhir_stack = MenhirCell1_constant_expr (_menhir_stack, _menhir_s, _v) in
              _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState168
          | EQ ->
              let MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) = _menhir_stack in
              let _2 = _v in
              let _v = _menhir_action_044 _2 in
              _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_designator_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState165 ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState174 ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState176 ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState168 ->
          _menhir_run_172 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState170 ->
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_180 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_043 _1 in
      let x = _v in
      let _v = _menhir_action_131 x in
      _menhir_goto_option_desig_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_option_desig_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState176 ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState174 ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState165 ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_177 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_cell1_COMMA as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_option_desig_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState177
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState177
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState177
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState177
      | LBRACE ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState177
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState177
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState177
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState177
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState177
      | _ ->
          _eRR ()
  
  and _menhir_run_172 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_cell1_constant_expr -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_constant_expr (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_046 _2 _4 in
      _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_171 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DOT, _menhir_box_translation_unit) _menhir_cell1_ident -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_ident (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_DOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_047 _2 _3 in
      _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_149 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_enum_const -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_enum_const (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _ = _menhir_action_058 () in
      _menhir_goto_enum _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
  
  and _menhir_goto_enum : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      match _menhir_s with
      | MenhirState039 ->
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState042 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_154 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_060 () in
      _menhir_goto_enum_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_enum_list : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_enum_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TYPE_ID _v_0 ->
              let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, MenhirState041) in
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState042
          | ID _v_1 ->
              let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, MenhirState041) in
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState042
          | RBRACE ->
              let _ =
                let x = () in
                _menhir_action_121 x
              in
              _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | RBRACE ->
          let _ = _menhir_action_120 () in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_152 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_enum_list (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_option_ident_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_ENUM (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_062 () in
      _menhir_goto_enum_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_enum_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_214 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_151 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list, _menhir_box_translation_unit) _menhir_cell1_COMMA -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_enum_list (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_061 () in
      _menhir_goto_enum_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_106 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_logical_or_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _5 = _v in
      let _v = _menhir_action_029 _1 _3 _5 in
      _menhir_goto_conditional_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_103 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_013 _1 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_assignment_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState310 ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState052 ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState129 ->
          _menhir_run_130 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState127 ->
          _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState125 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState123 ->
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState121 ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState119 ->
          _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState117 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState115 ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState113 ->
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState111 ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState054 ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState315 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState355 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_179 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_082 _1 in
      _menhir_goto_init _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState310 ->
          _menhir_run_311 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState173 ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState177 ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_311 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_declarator, _menhir_box_translation_unit) _menhir_cell1_EQ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_EQ (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_085 _1 _3 in
      _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState368 ->
          _menhir_run_312 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_312 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState307 ->
          _menhir_run_308 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_312 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_086 _1 in
      _menhir_goto_init_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init_declarator_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_032 _1 _2 in
          _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_init_declarator_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState307 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _ ->
              _menhir_reduce_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_308 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_init_declarator_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_init_declarator_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_087 _1 _3 in
      _menhir_goto_init_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_185 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_option_desig_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_option_desig_ (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_088 _1 _2 in
      _menhir_goto_init_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState165 ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState174 ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_186 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_cell1_LBRACE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_init_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState186
      | RBRACE ->
          let _ = _menhir_action_120 () in
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_176 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, _menhir_s) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | DOT ->
          let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, _menhir_s) in
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | RBRACE ->
          let x = () in
          let _ = _menhir_action_121 x in
          _menhir_goto_option_COMMA_ _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND | BANG | DEC | DOUBLE _ | FLOAT _ | ID _ | INC | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NOT | PLUS | SIZEOF | STAR | STR _ | UINT _ | ULINT _ ->
          let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, _menhir_s) in
          let _v = _menhir_action_130 () in
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState176 _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_COMMA_ : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      match _menhir_s with
      | MenhirState186 ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MenhirState175 ->
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MenhirState041 ->
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_187 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_init_list (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_LBRACE (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_type_name (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_150 _2 _5 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_183 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_init_list (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_083 _2 in
      _menhir_goto_init _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_175 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_init_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState175
      | RBRACE ->
          let _ = _menhir_action_120 () in
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_178 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_cell1_COMMA, _menhir_box_translation_unit) _menhir_cell1_option_desig_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_option_desig_ (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_init_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_089 _1 _3 _4 in
      _menhir_goto_init_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_136 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr, _menhir_box_translation_unit) _menhir_cell1_argument_expr_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_argument_expr_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_012 _1 _3 in
      _menhir_goto_argument_expr_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_argument_expr_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_argument_expr_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState135 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_127 x in
          _menhir_goto_option_argument_expr_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_argument_expr_list_ : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_145 _1 _3 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_133 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_011 _1 in
      _menhir_goto_argument_expr_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_130 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_018 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_128 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_022 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_126 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_016 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_124 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_014 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_122 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_020 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_120 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_017 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_118 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_015 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_116 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_024 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_114 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_021 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_112 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_019 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_110 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_unary_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_unary_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_023 _1 _3 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_107 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_069 _1 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState355 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState330 ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState315 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState384 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState323 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState369 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState370 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState338 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState340 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState342 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState343 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState363 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState325 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_322 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState317 ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState264 ->
          _menhir_run_255 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_255 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_255 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_356 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_stmt (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_DO (_menhir_stack, _menhir_s) = _menhir_stack in
          let _5 = _v in
          let _v = _menhir_action_093 _2 _5 in
          _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_102 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState102 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_331 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState332 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_327 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_072 _1 in
          _menhir_goto_expr_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_322 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SWITCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState323 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_318 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState319 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPE_ID _v ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SWITCH ->
              _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEMI ->
              _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | GOTO ->
              _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FOR ->
              _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DO ->
              _menhir_run_343 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEFAULT ->
              _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONTINUE ->
              _menhir_run_346 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CASE ->
              _menhir_run_348 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BREAK ->
              _menhir_run_351 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              _menhir_reduce_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_255 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_159 _2 in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_138 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_144 _1 _3 in
          _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_101 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COLON ->
          let _menhir_s = MenhirState105 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_104 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_070 _1 _3 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_084 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ANDAND ->
          let _menhir_stack = MenhirCell1_logical_and_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COLON | COMMA | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_113 _1 in
          _menhir_goto_logical_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_086 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_and_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_inclusive_or_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_logical_and_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_112 _1 _3 in
          _menhir_goto_logical_and_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_088 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_inclusive_or_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | HAT ->
          let _menhir_stack = MenhirCell1_exclusive_or_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_inclusive_or_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_081 _1 _3 in
          _menhir_goto_inclusive_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_095 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_exclusive_or_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_and_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ANDAND | COLON | COMMA | HAT | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_exclusive_or_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_068 _1 _3 in
          _menhir_goto_exclusive_or_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_090 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | NE ->
          let _menhir_stack = MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | HAT | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_009 _1 in
          _menhir_goto_and_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_092 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_equality_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | HAT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_equality_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_066 _1 _3 in
          _menhir_goto_equality_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_072 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | HAT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_064 _1 in
          _menhir_goto_equality_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_079 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_162 _1 _3 in
          _menhir_goto_relational_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_077 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_163 _1 _3 in
          _menhir_goto_relational_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_074 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_relational_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let MenhirCell1_relational_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_161 _1 _3 in
          _menhir_goto_relational_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_055 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LSHIFT ->
          let _menhir_stack = MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_160 _1 in
          _menhir_goto_relational_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_071 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_shift_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_170 _1 _3 in
          _menhir_goto_shift_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_065 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_shift_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | NE | OR | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let MenhirCell1_shift_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_171 _1 _3 in
          _menhir_goto_shift_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_067 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_additive_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | MINUS | NE | OR | OROR | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let MenhirCell1_additive_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_005 _1 _3 in
          _menhir_goto_additive_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_057 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | ANDAND | COLON | COMMA | EQEQ | GE | GT | HAT | LE | LSHIFT | LT | MINUS | NE | OR | OROR | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_004 _1 in
          _menhir_goto_additive_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_063 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_118 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_061 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_119 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_059 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_117 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_049 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_025 _1 in
      _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_258 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_name (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState259 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | LBRACE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_211 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ALIGNAS -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_ALIGNAS (_menhir_stack, _menhir_s) = _menhir_stack in
          let _ = _menhir_action_007 () in
          _menhir_goto_alignment_spec _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_163 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_name (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState164 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_250 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_125 x in
      _menhir_goto_option_abstract_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_option_abstract_declarator_ : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_137 _1 _2 in
      _menhir_goto_parameter_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState201 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_238 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_138 _1 in
      _menhir_goto_parameter_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState222 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TYPE_ID _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ELLIPSIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _ = _menhir_action_123 () in
              _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _tok
          | _ ->
              _eRR ())
      | RPAREN ->
          let _ = _menhir_action_122 () in
          _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_option___anonymous_0_ : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_141 _1 in
      _menhir_goto_parameter_type_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_type_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState235 ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_218 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_parameter_type_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState218
      | _ ->
          _eRR ()
  
  and _menhir_run_223 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_139 _1 _3 in
      _menhir_goto_parameter_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_245 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_048 _2 in
          _menhir_goto_direct_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_196 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_pointer as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState196
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState196
      | COLON | COMMA | RPAREN ->
          let MenhirCell1_pointer (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_002 _2 in
          _menhir_goto_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_201 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lp (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState201
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState201
      | RPAREN ->
          let _v_1 = _menhir_action_140 () in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState201 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_232 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState232 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState303 ->
          _menhir_run_313 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState307 ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState278 ->
          _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState282 ->
          _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_248 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState279 ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState226 ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_313 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_stack = MenhirCell1_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_310 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState313
      | LBRACE ->
          let _menhir_stack = MenhirCell1_declarator (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState313 in
          let _v = _menhir_action_056 () in
          _menhir_goto_enter_scope _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_084 _1 in
          _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_310 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_declarator as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_EQ (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState310 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ULINT _v ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | UINT _v ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STR _v ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LINT _v ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | LBRACE ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _v ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FLOAT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DOUBLE _v ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_309 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_stack = MenhirCell1_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_310 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState309
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_084 _1 in
          _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_287 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let x = _v in
          let _v = _menhir_action_129 x in
          _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_191 _1 in
          _menhir_goto_struct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_248 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_136 _1 _2 in
      _menhir_goto_parameter_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_243 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_052 _2 in
          _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_231 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_pointer as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState231
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState231
      | COLON | COMMA | EQ | LBRACE | RPAREN | SEMI ->
          let MenhirCell1_pointer (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_041 _2 in
          _menhir_goto_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_227 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState227
      | COLON | COMMA | RPAREN ->
          let _v = _menhir_action_001 () in
          _menhir_goto_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ID _ ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState227 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_226 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState226 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _ ->
          _menhir_reduce_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_195 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | RPAREN ->
          let _v = _menhir_action_001 () in
          _menhir_goto_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_194 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState194 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_189 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState189
      | LPAREN ->
          let _menhir_stack = MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState189
      | RPAREN ->
          let _1 = _v in
          let _v = _menhir_action_200 _1 in
          _menhir_goto_type_name _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_162 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_spec -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_spec (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_173 _1 _2 in
      _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_160 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_qual -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_qual (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_174 _1 _2 in
      _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_335 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_GOTO -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_GOTO (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_096 _2 in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_295 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_UNION as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_133 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_UNION (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_198 _2 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_ident_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState037 ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState017 ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState002 ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_005 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_UNION as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_ident_ (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState006 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYPE_ID _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_292 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STRUCT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_133 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_196 _2 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_170 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DOT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | DOT ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v) in
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | EQ ->
          let MenhirCell1_DOT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_045 _2 in
          _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_155 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_ENUM (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v = _menhir_action_063 () in
          _menhir_goto_enum_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_133 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_145 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_147 _1 _3 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_142 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_146 _1 _3 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_040 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_059 () in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_stack = MenhirCell1_enum_const (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState044 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _v ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COMMA | RBRACE ->
          let _ = _menhir_action_057 () in
          _menhir_goto_enum _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_304 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_031 () in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_303 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState303
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | SEMI ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | LPAREN ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
      | ID _ ->
          let _menhir_s = MenhirState303 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_225 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState225
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | LPAREN ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState225
      | ID _ ->
          let _menhir_s = MenhirState225 in
          let _v = _menhir_action_055 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COLON | COMMA | RPAREN ->
          let _v = _menhir_action_124 () in
          _menhir_goto_option_abstract_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_239 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_039 _1 in
      _menhir_goto_decl_specs _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_191 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_qual (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState191
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState191
      | COLON | COMMA | ID _ | LPAREN | RPAREN ->
          let _v_0 = _menhir_action_109 () in
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_192 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_qual -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_qual (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_110 x xs in
      _menhir_goto_list_type_qual_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_list_type_qual_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState190 ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState191 ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_158 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_qual (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState158
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState158
      | _ ->
          _eRR ()
  
  let rec _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TYPE_ID _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | EOF ->
          let _v = _menhir_action_105 () in
          _menhir_run_298 _menhir_stack _v
      | _ ->
          _eRR ()
  
end

let translation_unit =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_translation_unit v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

# 696 "src/parser.mly"
  
# 12952 "src/parser.ml"
