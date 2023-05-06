
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
# 335 "src/parser.mly"
       (int)
# 19 "src/parser.ml"
  )
    | UINT of (
# 335 "src/parser.mly"
       (int)
# 24 "src/parser.ml"
  )
    | TYPE_ID of (
# 338 "src/parser.mly"
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
# 337 "src/parser.mly"
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
# 335 "src/parser.mly"
       (int)
# 80 "src/parser.ml"
  )
    | LE
    | LBRACKET
    | LBRACE
    | INT of (
# 335 "src/parser.mly"
       (int)
# 88 "src/parser.ml"
  )
    | INLINE
    | INC
    | IF
    | ID of (
# 338 "src/parser.mly"
      (string)
# 96 "src/parser.ml"
  )
    | HAT
    | GT
    | GOTO
    | GE
    | FOR
    | FLOAT of (
# 336 "src/parser.mly"
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
# 336 "src/parser.mly"
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

    let raise exn =
    match exn with
    | ParserError msg -> Printf.printf "%s\n" msg;raise exn
    | _ -> raise exn

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

    type is_incomplete =
    | Complete
    | Incomplete 
    | DontCare 

    let struct_pred name =function
    | (_,Struct(n,_)) when n = name ->
      true
    | _ -> false

    let lookup_struct_in_scope name =
      try 
        let (id,item) = List.find (struct_pred name) !curr_scope 
      in
      match item with
      | Struct(_,Some _) -> (Some id,Complete)
      | Struct(_,None) -> (Some id,Incomplete)
      | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)

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
          | (Some id,Complete) -> 
            begin
              match dl with
              | Some _ -> raise (ParserError "redifinition")
              | None -> (id,None)
            end
          | (Some id,Incomplete) ->
            begin
              match dl with
              | Some _ -> (id,Some (id,Struct(!name,dl)))
              | None -> (id,None)
            end
          | _ -> 
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
        let (id,item) = List.find (union_pred name) !curr_scope 
      in
      match item with
      | Union(_,Some _) -> (Some id,Complete)
      | Union(_,None) -> (Some id,Incomplete)
      | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)

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
          | (Some id,Complete) -> 
            begin
              match dl with
              | Some _ -> raise (ParserError "redifinition")
              | None -> (id,None)
            end
          | (Some id,Incomplete) ->
            begin
              match dl with
              | Some _ -> (id,Some (id,Union(!name,dl)))
              | None -> (id,None)
            end
          | _ -> 
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
        begin
          push_def def;
          def_stack := def::!def_stack
        end


    let flush_stack2 () = 
      def_stack_in_params := []  

    let get_stack2 () =
      let ret = List.rev !def_stack_in_params in
      flush_stack2 ();
      ret

    let expr_conv = function
    | Some e -> SExpr e 
    | None -> SStmts []

    let label_list = ref []
    
    let goto_list = ref []

    let push_label l =
      label_list := l::!label_list

    let push_goto g =
      goto_list := g::!goto_list

    let all_labels_exist () =
      let missing_label = ref "" in
      let pred goto =
        if List.mem goto !label_list then
          true
        else
          begin
            missing_label := goto;
            false
          end
      in
      if List.for_all (fun goto -> pred goto) !goto_list then
        begin
          label_list := [];
          goto_list := []
        end
      else
        raise (ParserError (Printf.sprintf "label %s is missing" !missing_label))

    let label_id = ref 0

    let gen_new_label () =
      label_id := !label_id + 1;
      let label = "label" ^ (string_of_int !label_id) in
      push_label label;
      label
    
    let brk = ref ""

    let cont = ref ""

    let curr_brk = ref ""

    let curr_cont = ref ""



# 466 "src/parser.ml"

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

  | MenhirState226 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 226.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)

  | MenhirState227 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 227.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState228 : (('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_state
    (** State 228.
        Stack shape : pointer.
        Start symbol: translation_unit. *)

  | MenhirState229 : (('s, _menhir_box_translation_unit) _menhir_cell1_pointer, _menhir_box_translation_unit) _menhir_state
    (** State 229.
        Stack shape : pointer.
        Start symbol: translation_unit. *)

  | MenhirState230 : (('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 230.
        Stack shape : LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState234 : (('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 234.
        Stack shape : direct_declarator.
        Start symbol: translation_unit. *)

  | MenhirState235 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET, _menhir_box_translation_unit) _menhir_state
    (** State 235.
        Stack shape : direct_declarator LBRACKET.
        Start symbol: translation_unit. *)

  | MenhirState238 : ((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_state
    (** State 238.
        Stack shape : direct_declarator lp.
        Start symbol: translation_unit. *)

  | MenhirState239 : (((('s, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list, _menhir_box_translation_unit) _menhir_state
    (** State 239.
        Stack shape : direct_declarator lp parameter_type_list.
        Start symbol: translation_unit. *)

  | MenhirState247 : (('s, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 247.
        Stack shape : direct_abstract_declarator.
        Start symbol: translation_unit. *)

  | MenhirState260 : ((('s, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_state
    (** State 260.
        Stack shape : LPAREN type_name.
        Start symbol: translation_unit. *)

  | MenhirState265 : ((('s, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_state
    (** State 265.
        Stack shape : SIZEOF LPAREN.
        Start symbol: translation_unit. *)

  | MenhirState267 : (((('s, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name, _menhir_box_translation_unit) _menhir_state
    (** State 267.
        Stack shape : SIZEOF LPAREN type_name.
        Start symbol: translation_unit. *)

  | MenhirState275 : (((('s, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list, _menhir_box_translation_unit) _menhir_state
    (** State 275.
        Stack shape : STRUCT option(ident) struct_decl_list.
        Start symbol: translation_unit. *)

  | MenhirState279 : (('s, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_state
    (** State 279.
        Stack shape : spec_qual_list.
        Start symbol: translation_unit. *)

  | MenhirState281 : ((('s, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_cell1_struct_declarator_list, _menhir_box_translation_unit) _menhir_state
    (** State 281.
        Stack shape : spec_qual_list struct_declarator_list.
        Start symbol: translation_unit. *)

  | MenhirState284 : (('s, _menhir_box_translation_unit) _menhir_cell1_option_declarator_, _menhir_box_translation_unit) _menhir_state
    (** State 284.
        Stack shape : option(declarator).
        Start symbol: translation_unit. *)

  | MenhirState292 : (((('s, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list, _menhir_box_translation_unit) _menhir_state
    (** State 292.
        Stack shape : UNION option(ident) struct_decl_list.
        Start symbol: translation_unit. *)

  | MenhirState300 : (('s, _menhir_box_translation_unit) _menhir_cell1_function_decl, _menhir_box_translation_unit) _menhir_state
    (** State 300.
        Stack shape : function_decl.
        Start symbol: translation_unit. *)

  | MenhirState303 : ((('s, _menhir_box_translation_unit) _menhir_cell1_function_decl, _menhir_box_translation_unit) _menhir_cell1_enter_scope, _menhir_box_translation_unit) _menhir_state
    (** State 303.
        Stack shape : function_decl enter_scope.
        Start symbol: translation_unit. *)

  | MenhirState305 : (('s, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_state
    (** State 305.
        Stack shape : WHILE.
        Start symbol: translation_unit. *)

  | MenhirState307 : ((('s, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 307.
        Stack shape : WHILE expr.
        Start symbol: translation_unit. *)

  | MenhirState308 : (((('s, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_state
    (** State 308.
        Stack shape : WHILE expr begin_.
        Start symbol: translation_unit. *)

  | MenhirState310 : (('s, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_state
    (** State 310.
        Stack shape : SWITCH.
        Start symbol: translation_unit. *)

  | MenhirState312 : ((('s, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 312.
        Stack shape : SWITCH expr.
        Start symbol: translation_unit. *)

  | MenhirState314 : (((('s, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_state
    (** State 314.
        Stack shape : SWITCH expr begin_.
        Start symbol: translation_unit. *)

  | MenhirState316 : (('s, _menhir_box_translation_unit) _menhir_cell1_DEFAULT, _menhir_box_translation_unit) _menhir_state
    (** State 316.
        Stack shape : DEFAULT.
        Start symbol: translation_unit. *)

  | MenhirState319 : (('s, _menhir_box_translation_unit) _menhir_cell1_RETURN, _menhir_box_translation_unit) _menhir_state
    (** State 319.
        Stack shape : RETURN.
        Start symbol: translation_unit. *)

  | MenhirState324 : (('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_state
    (** State 324.
        Stack shape : IF.
        Start symbol: translation_unit. *)

  | MenhirState326 : ((('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_state
    (** State 326.
        Stack shape : IF expr.
        Start symbol: translation_unit. *)

  | MenhirState328 : (('s, _menhir_box_translation_unit) _menhir_cell1_GOTO, _menhir_box_translation_unit) _menhir_state
    (** State 328.
        Stack shape : GOTO.
        Start symbol: translation_unit. *)

  | MenhirState332 : (('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_state
    (** State 332.
        Stack shape : FOR.
        Start symbol: translation_unit. *)

  | MenhirState333 : ((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 333.
        Stack shape : FOR expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState334 : (((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 334.
        Stack shape : FOR expr_stmt expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState336 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_state
    (** State 336.
        Stack shape : FOR expr_stmt expr_stmt option(expr).
        Start symbol: translation_unit. *)

  | MenhirState337 : (((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_state
    (** State 337.
        Stack shape : FOR expr_stmt expr_stmt option(expr) begin_.
        Start symbol: translation_unit. *)

  | MenhirState338 : (('s, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_state
    (** State 338.
        Stack shape : DO.
        Start symbol: translation_unit. *)

  | MenhirState339 : ((('s, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_state
    (** State 339.
        Stack shape : DO begin_.
        Start symbol: translation_unit. *)

  | MenhirState346 : (((('s, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_cell1_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 346.
        Stack shape : DO begin_ stmt.
        Start symbol: translation_unit. *)

  | MenhirState349 : (('s, _menhir_box_translation_unit) _menhir_cell1_selection_stmt_2, _menhir_box_translation_unit) _menhir_state
    (** State 349.
        Stack shape : selection_stmt_2.
        Start symbol: translation_unit. *)

  | MenhirState354 : (('s, _menhir_box_translation_unit) _menhir_cell1_iteration_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 354.
        Stack shape : iteration_stmt.
        Start symbol: translation_unit. *)

  | MenhirState357 : (('s, _menhir_box_translation_unit) _menhir_cell1_ident, _menhir_box_translation_unit) _menhir_state
    (** State 357.
        Stack shape : ident.
        Start symbol: translation_unit. *)

  | MenhirState362 : (('s, _menhir_box_translation_unit) _menhir_cell1_enter_scope, _menhir_box_translation_unit) _menhir_state
    (** State 362.
        Stack shape : enter_scope.
        Start symbol: translation_unit. *)

  | MenhirState364 : ((('s, _menhir_box_translation_unit) _menhir_cell1_enter_scope, _menhir_box_translation_unit) _menhir_cell1_list_item_, _menhir_box_translation_unit) _menhir_state
    (** State 364.
        Stack shape : enter_scope list(item).
        Start symbol: translation_unit. *)

  | MenhirState366 : (('s, _menhir_box_translation_unit) _menhir_cell1_item, _menhir_box_translation_unit) _menhir_state
    (** State 366.
        Stack shape : item.
        Start symbol: translation_unit. *)

  | MenhirState368 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 368.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)

  | MenhirState372 : ((('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_init_declarator_list, _menhir_box_translation_unit) _menhir_state
    (** State 372.
        Stack shape : decl_specs init_declarator_list.
        Start symbol: translation_unit. *)

  | MenhirState375 : (('s, _menhir_box_translation_unit) _menhir_cell1_declarator, _menhir_box_translation_unit) _menhir_state
    (** State 375.
        Stack shape : declarator.
        Start symbol: translation_unit. *)

  | MenhirState382 : ((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 382.
        Stack shape : FOR decl_for_for_stmt.
        Start symbol: translation_unit. *)

  | MenhirState383 : (((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 383.
        Stack shape : FOR decl_for_for_stmt expr_stmt.
        Start symbol: translation_unit. *)

  | MenhirState385 : ((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_state
    (** State 385.
        Stack shape : FOR decl_for_for_stmt expr_stmt option(expr).
        Start symbol: translation_unit. *)

  | MenhirState386 : (((((('s, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_state
    (** State 386.
        Stack shape : FOR decl_for_for_stmt expr_stmt option(expr) begin_.
        Start symbol: translation_unit. *)

  | MenhirState390 : (((('s, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_stmt, _menhir_box_translation_unit) _menhir_state
    (** State 390.
        Stack shape : IF expr stmt.
        Start symbol: translation_unit. *)

  | MenhirState393 : (('s, _menhir_box_translation_unit) _menhir_cell1_CASE, _menhir_box_translation_unit) _menhir_state
    (** State 393.
        Stack shape : CASE.
        Start symbol: translation_unit. *)

  | MenhirState395 : ((('s, _menhir_box_translation_unit) _menhir_cell1_CASE, _menhir_box_translation_unit) _menhir_cell1_conditional_expr, _menhir_box_translation_unit) _menhir_state
    (** State 395.
        Stack shape : CASE conditional_expr.
        Start symbol: translation_unit. *)

  | MenhirState399 : (('s, _menhir_box_translation_unit) _menhir_cell1_case_or_default, _menhir_box_translation_unit) _menhir_state
    (** State 399.
        Stack shape : case_or_default.
        Start symbol: translation_unit. *)

  | MenhirState403 : (((('s, _menhir_box_translation_unit) _menhir_cell1_function_decl, _menhir_box_translation_unit) _menhir_cell1_enter_scope, _menhir_box_translation_unit) _menhir_cell1_list_item_, _menhir_box_translation_unit) _menhir_state
    (** State 403.
        Stack shape : function_decl enter_scope list(item).
        Start symbol: translation_unit. *)

  | MenhirState405 : (('s, _menhir_box_translation_unit) _menhir_cell1_external_decl, _menhir_box_translation_unit) _menhir_state
    (** State 405.
        Stack shape : external_decl.
        Start symbol: translation_unit. *)

  | MenhirState407 : (('s, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_state
    (** State 407.
        Stack shape : decl_specs.
        Start symbol: translation_unit. *)


and ('s, 'r) _menhir_cell1_additive_expr = 
  | MenhirCell1_additive_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_and_expr = 
  | MenhirCell1_and_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_argument_expr_list = 
  | MenhirCell1_argument_expr_list of 's * ('s, 'r) _menhir_state * (Ast.expr list)

and ('s, 'r) _menhir_cell1_begin_ = 
  | MenhirCell1_begin_ of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_case_or_default = 
  | MenhirCell1_case_or_default of 's * ('s, 'r) _menhir_state * (Ast.stmt)

and ('s, 'r) _menhir_cell1_conditional_expr = 
  | MenhirCell1_conditional_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_constant_expr = 
  | MenhirCell1_constant_expr of 's * ('s, 'r) _menhir_state * (int)

and ('s, 'r) _menhir_cell1_decl_for_for_stmt = 
  | MenhirCell1_decl_for_for_stmt of 's * ('s, 'r) _menhir_state * (Ast.def)

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

and ('s, 'r) _menhir_cell1_function_decl = 
  | MenhirCell1_function_decl of 's * ('s, 'r) _menhir_state * (Ctype.decl * Ast.def list)

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

and ('s, 'r) _menhir_cell1_iteration_stmt = 
  | MenhirCell1_iteration_stmt of 's * ('s, 'r) _menhir_state * (Ast.stmt)

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

and ('s, 'r) _menhir_cell1_option_expr_ = 
  | MenhirCell1_option_expr_ of 's * ('s, 'r) _menhir_state * (Ast.expr option)

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

and ('s, 'r) _menhir_cell1_selection_stmt_2 = 
  | MenhirCell1_selection_stmt_2 of 's * ('s, 'r) _menhir_state * (Ast.stmt)

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

and ('s, 'r) _menhir_cell1_DEFAULT = 
  | MenhirCell1_DEFAULT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DO = 
  | MenhirCell1_DO of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DOT = 
  | MenhirCell1_DOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ENUM = 
  | MenhirCell1_ENUM of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FOR = 
  | MenhirCell1_FOR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_GOTO = 
  | MenhirCell1_GOTO of 's * ('s, 'r) _menhir_state

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 338 "src/parser.mly"
      (string)
# 1381 "src/parser.ml"
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
# 664 "src/parser.mly"
          ( DeclPtr (DeclIdent "") )
# 1440 "src/parser.ml"
     : (declarator))

let _menhir_action_002 =
  fun _2 ->
    (
# 665 "src/parser.mly"
                                     ( DeclPtr _2 )
# 1448 "src/parser.ml"
     : (declarator))

let _menhir_action_003 =
  fun _1 ->
    (
# 666 "src/parser.mly"
                             ( _1 )
# 1456 "src/parser.ml"
     : (declarator))

let _menhir_action_004 =
  fun _1 ->
    (
# 413 "src/parser.mly"
                      ( _1 )
# 1464 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_005 =
  fun _1 _3 ->
    (
# 414 "src/parser.mly"
                                         ( EBinary(Add,_1,_3) )
# 1472 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_006 =
  fun _1 _3 ->
    (
# 415 "src/parser.mly"
                                          ( EBinary(Sub,_1,_3) )
# 1480 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_007 =
  fun () ->
    (
# 553 "src/parser.mly"
  ( raise (NotImpl "ALIGNAS") )
# 1488 "src/parser.ml"
     : ('tv_alignment_spec))

let _menhir_action_008 =
  fun () ->
    (
# 553 "src/parser.mly"
  ( raise (NotImpl "ALIGNAS") )
# 1496 "src/parser.ml"
     : ('tv_alignment_spec))

let _menhir_action_009 =
  fun _1 ->
    (
# 435 "src/parser.mly"
                ( _1 )
# 1504 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_010 =
  fun _1 _3 ->
    (
# 436 "src/parser.mly"
                             ( EBinary(BitAnd,_1,_3) )
# 1512 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_011 =
  fun _1 ->
    (
# 385 "src/parser.mly"
                  ( [_1] )
# 1520 "src/parser.ml"
     : (Ast.expr list))

let _menhir_action_012 =
  fun _1 _3 ->
    (
# 386 "src/parser.mly"
                                           ( _1@[_3] )
# 1528 "src/parser.ml"
     : (Ast.expr list))

let _menhir_action_013 =
  fun _1 ->
    (
# 459 "src/parser.mly"
                   ( _1 )
# 1536 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_014 =
  fun _1 _3 ->
    (
# 460 "src/parser.mly"
                                ( EAssign(None, _1,_3) )
# 1544 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_015 =
  fun _1 _3 ->
    (
# 461 "src/parser.mly"
                                    ( EAssign(Some Mul, _1,_3) )
# 1552 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_016 =
  fun _1 _3 ->
    (
# 462 "src/parser.mly"
                                    ( EAssign(Some Div, _1,_3) )
# 1560 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_017 =
  fun _1 _3 ->
    (
# 463 "src/parser.mly"
                                    ( EAssign(Some Mod, _1,_3) )
# 1568 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_018 =
  fun _1 _3 ->
    (
# 464 "src/parser.mly"
                                    ( EAssign(Some Add, _1,_3) )
# 1576 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_019 =
  fun _1 _3 ->
    (
# 465 "src/parser.mly"
                                    ( EAssign(Some Sub, _1,_3) )
# 1584 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_020 =
  fun _1 _3 ->
    (
# 466 "src/parser.mly"
                                       ( EAssign(Some LShift, _1,_3) )
# 1592 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_021 =
  fun _1 _3 ->
    (
# 467 "src/parser.mly"
                                       ( EAssign(Some RShift, _1,_3) )
# 1600 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_022 =
  fun _1 _3 ->
    (
# 468 "src/parser.mly"
                                    ( EAssign(Some BitAnd, _1,_3) )
# 1608 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_023 =
  fun _1 _3 ->
    (
# 469 "src/parser.mly"
                                    ( EAssign(Some BitXor, _1,_3) )
# 1616 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_024 =
  fun _1 _3 ->
    (
# 470 "src/parser.mly"
                                   ( EAssign(Some BitOr, _1,_3) )
# 1624 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_025 =
  fun () ->
    (
# 783 "src/parser.mly"
  (
    brk := !curr_brk;
    cont := !curr_cont;
    curr_brk := gen_new_label ();
    curr_cont := gen_new_label ();
  )
# 1637 "src/parser.ml"
     : (unit))

let _menhir_action_026 =
  fun _2 _4 ->
    (
# 731 "src/parser.mly"
                                         ( SCase (_2,List.flatten _4) )
# 1645 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_027 =
  fun _3 ->
    (
# 732 "src/parser.mly"
                           ( SDefault (List.flatten _3) )
# 1653 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_028 =
  fun _1 ->
    (
# 403 "src/parser.mly"
             ( _1 )
# 1661 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_029 =
  fun _2 _4 ->
    (
# 404 "src/parser.mly"
                                    ( ECast(_2,_4) )
# 1669 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_030 =
  fun _3 ->
    (
# 737 "src/parser.mly"
 (
    SStmts(List.flatten _3)
  )
# 1679 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_031 =
  fun _1 ->
    (
# 455 "src/parser.mly"
                  ( _1 )
# 1687 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_032 =
  fun _1 _3 _5 ->
    (
# 456 "src/parser.mly"
                                                       ( ECond(_1,_3,_5) )
# 1695 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_033 =
  fun () ->
    (
# 478 "src/parser.mly"
  ( 0 )
# 1703 "src/parser.ml"
     : (int))

let _menhir_action_034 =
  fun () ->
    (
# 481 "src/parser.mly"
                  ( () )
# 1711 "src/parser.ml"
     : (unit))

let _menhir_action_035 =
  fun _1 _2 ->
    (
# 483 "src/parser.mly"
  ( 
    let defs = List.map make_var_or_typedef (make_decls_with_init_opts _1 _2) in
    List.iter add_def defs
  )
# 1722 "src/parser.ml"
     : (unit))

let _menhir_action_036 =
  fun () ->
    (
# 487 "src/parser.mly"
                      ( raise (NotImpl "Static_assert") )
# 1730 "src/parser.ml"
     : (unit))

let _menhir_action_037 =
  fun () ->
    (
# 758 "src/parser.mly"
  ( peek_curr_scope () )
# 1738 "src/parser.ml"
     : (Ast.def))

let _menhir_action_038 =
  fun _1 ->
    (
# 490 "src/parser.mly"
                     ( TDeclSpec [Scs _1] )
# 1746 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_039 =
  fun _1 ->
    (
# 491 "src/parser.mly"
            ( TDeclSpec [Tq _1] )
# 1754 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_040 =
  fun _1 ->
    (
# 492 "src/parser.mly"
                ( TDeclSpec [Fs _1] )
# 1762 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_041 =
  fun () ->
    (
# 493 "src/parser.mly"
                 ( raise (NotImpl "not implemented") )
# 1770 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_042 =
  fun _1 ->
    (
# 494 "src/parser.mly"
            ( TDeclSpec [Ts _1] )
# 1778 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_043 =
  fun _1 ->
    (
# 497 "src/parser.mly"
            ( _1 )
# 1786 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_044 =
  fun _1 _2 ->
    (
# 499 "src/parser.mly"
  ( append_ds_list [_1] [_2] )
# 1794 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_045 =
  fun _2 ->
    (
# 605 "src/parser.mly"
                     ( DeclPtr _2 )
# 1802 "src/parser.ml"
     : (declarator))

let _menhir_action_046 =
  fun _1 ->
    (
# 606 "src/parser.mly"
                    ( _1 )
# 1810 "src/parser.ml"
     : (declarator))

let _menhir_action_047 =
  fun _1 ->
    (
# 688 "src/parser.mly"
  ( _1 )
# 1818 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_048 =
  fun _2 ->
    (
# 691 "src/parser.mly"
                                  ( DIdx(_2,None) )
# 1826 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_049 =
  fun _2 ->
    (
# 692 "src/parser.mly"
            ( DField(_2,None) )
# 1834 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_050 =
  fun _2 _4 ->
    (
# 693 "src/parser.mly"
                                                  (DIdx(_2,Some _4) )
# 1842 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_051 =
  fun _2 _3 ->
    (
# 694 "src/parser.mly"
                            ( DField(_2,Some _3) )
# 1850 "src/parser.ml"
     : (Ast.desig))

let _menhir_action_052 =
  fun _2 ->
    (
# 669 "src/parser.mly"
                                    ( _2 )
# 1858 "src/parser.ml"
     : (declarator))

let _menhir_action_053 =
  fun _1 _3 ->
    (
# 670 "src/parser.mly"
                                                             ( DeclArr(_1,_3) )
# 1866 "src/parser.ml"
     : (declarator))

let _menhir_action_054 =
  fun _1 _3 ->
    (
# 671 "src/parser.mly"
                                                       ( DeclFun(_1,_3) )
# 1874 "src/parser.ml"
     : (declarator))

let _menhir_action_055 =
  fun _2 ->
    (
# 622 "src/parser.mly"
                                       ( DeclIdent _2 )
# 1882 "src/parser.ml"
     : (declarator))

let _menhir_action_056 =
  fun _2 ->
    (
# 623 "src/parser.mly"
                           ( _2 )
# 1890 "src/parser.ml"
     : (declarator))

let _menhir_action_057 =
  fun _1 _3 ->
    (
# 624 "src/parser.mly"
                                                    ( DeclArr(_1, _3) )
# 1898 "src/parser.ml"
     : (declarator))

let _menhir_action_058 =
  fun _1 _3 ->
    (
# 625 "src/parser.mly"
                                              ( DeclFun(_1,_3) )
# 1906 "src/parser.ml"
     : (declarator))

let _menhir_action_059 =
  fun () ->
    (
# 792 "src/parser.mly"
  (
    curr_brk := !brk;
    curr_cont := !cont;
  )
# 1917 "src/parser.ml"
     : (unit))

let _menhir_action_060 =
  fun () ->
    (
# 611 "src/parser.mly"
  (
    in_declarator := true
  )
# 1927 "src/parser.ml"
     : (unit))

let _menhir_action_061 =
  fun () ->
    (
# 701 "src/parser.mly"
  (
    stack := !curr_scope::!stack
  )
# 1937 "src/parser.ml"
     : (unit))

let _menhir_action_062 =
  fun () ->
    (
# 598 "src/parser.mly"
    (  )
# 1945 "src/parser.ml"
     : (unit))

let _menhir_action_063 =
  fun () ->
    (
# 598 "src/parser.mly"
    (  )
# 1953 "src/parser.ml"
     : (unit))

let _menhir_action_064 =
  fun () ->
    (
# 602 "src/parser.mly"
    (  )
# 1961 "src/parser.ml"
     : (unit))

let _menhir_action_065 =
  fun () ->
    (
# 593 "src/parser.mly"
    ()
# 1969 "src/parser.ml"
     : (unit))

let _menhir_action_066 =
  fun () ->
    (
# 593 "src/parser.mly"
    ()
# 1977 "src/parser.ml"
     : (unit))

let _menhir_action_067 =
  fun () ->
    (
# 588 "src/parser.mly"
    ( raise (NotImpl "enum_spec") )
# 1985 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_068 =
  fun () ->
    (
# 588 "src/parser.mly"
    ( raise (NotImpl "enum_spec") )
# 1993 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_069 =
  fun _1 ->
    (
# 430 "src/parser.mly"
                  ( _1 )
# 2001 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_070 =
  fun _1 _3 ->
    (
# 431 "src/parser.mly"
                                     ( EBinary(Eq,_1,_3) )
# 2009 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_071 =
  fun _1 _3 ->
    (
# 432 "src/parser.mly"
                                   ( EBinary(Ne,_1,_3) )
# 2017 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_072 =
  fun _1 ->
    (
# 439 "src/parser.mly"
           ( _1 )
# 2025 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_073 =
  fun _1 _3 ->
    (
# 440 "src/parser.mly"
                                 ( EBinary(BitXor,_1,_3) )
# 2033 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_074 =
  fun _1 ->
    (
# 473 "src/parser.mly"
                  ( _1 )
# 2041 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_075 =
  fun _1 _3 ->
    (
# 474 "src/parser.mly"
                             ( EBinary(Comma,_1,_3) )
# 2049 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_076 =
  fun () ->
    (
# 742 "src/parser.mly"
       ( None )
# 2057 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_077 =
  fun _1 ->
    (
# 743 "src/parser.mly"
            ( Some _1 )
# 2065 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_078 =
  fun _1 ->
    (
# 808 "src/parser.mly"
               ( _1 )
# 2073 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_079 =
  fun () ->
    (
# 810 "src/parser.mly"
  ( get_stack () )
# 2081 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_080 =
  fun _1 _2 ->
    (
# 814 "src/parser.mly"
  (
    let decl = make_decl _1 _2 in
    (decl,get_stack ())
  )
# 2092 "src/parser.ml"
     : (Ctype.decl * Ast.def list))

let _menhir_action_081 =
  fun _1 _2 ->
    (
# 828 "src/parser.mly"
  (
    let (decl,def_list) = _1 in
    let def2_list = get_stack2 () in
    let get_stmts = function 
    | SStmts l -> l 
    | _ -> raise (ParserError "function_def") in
    let def2_list = SStmts ((List.map (fun def -> SDef def) def2_list)@(get_stmts _2)) in
    def_list@[(gen_id (),Function(get_stack2 ()@get_params (snd decl),decl,Some def2_list))]
  )
# 2108 "src/parser.ml"
     : (Ast.def list))

let _menhir_action_082 =
  fun () ->
    (
# 547 "src/parser.mly"
         ( FsInline )
# 2116 "src/parser.ml"
     : (Ctype.fs))

let _menhir_action_083 =
  fun () ->
    (
# 548 "src/parser.mly"
           ( FsNoreturn )
# 2124 "src/parser.ml"
     : (Ctype.fs))

let _menhir_action_084 =
  fun _1 ->
    (
# 354 "src/parser.mly"
     ( _1 )
# 2132 "src/parser.ml"
     : (string))

let _menhir_action_085 =
  fun _1 ->
    (
# 355 "src/parser.mly"
          ( _1 )
# 2140 "src/parser.ml"
     : (string))

let _menhir_action_086 =
  fun _1 ->
    (
# 443 "src/parser.mly"
                    ( _1 )
# 2148 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_087 =
  fun _1 _3 ->
    (
# 444 "src/parser.mly"
                                         ( EBinary(BitOr,_1,_3) )
# 2156 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_088 =
  fun _1 ->
    (
# 679 "src/parser.mly"
                  ( IScal _1 )
# 2164 "src/parser.ml"
     : (Ast.init))

let _menhir_action_089 =
  fun _2 ->
    (
# 680 "src/parser.mly"
                                 ( IVect _2 )
# 2172 "src/parser.ml"
     : (Ast.init))

let _menhir_action_090 =
  fun _1 ->
    (
# 508 "src/parser.mly"
             ( (_1,None) )
# 2180 "src/parser.ml"
     : (declarator * Ast.init option))

let _menhir_action_091 =
  fun _1 _3 ->
    (
# 510 "src/parser.mly"
  ( (_1,Some _3) )
# 2188 "src/parser.ml"
     : (declarator * Ast.init option))

let _menhir_action_092 =
  fun _1 ->
    (
# 503 "src/parser.mly"
  ( [_1] )
# 2196 "src/parser.ml"
     : ((declarator * Ast.init option) list))

let _menhir_action_093 =
  fun _1 _3 ->
    (
# 505 "src/parser.mly"
  ( _1@[_3] )
# 2204 "src/parser.ml"
     : ((declarator * Ast.init option) list))

let _menhir_action_094 =
  fun _1 _2 ->
    (
# 683 "src/parser.mly"
              ( [(_1,_2)] )
# 2212 "src/parser.ml"
     : ((Ast.desig option * Ast.init) list))

let _menhir_action_095 =
  fun _1 _3 _4 ->
    (
# 684 "src/parser.mly"
                              ( _1@[(_3,_4)] )
# 2220 "src/parser.ml"
     : ((Ast.desig option * Ast.init) list))

let _menhir_action_096 =
  fun () ->
    (
# 711 "src/parser.mly"
       ( List.map (fun def -> SDef def) (get_stack ()) )
# 2228 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_097 =
  fun _1 ->
    (
# 712 "src/parser.mly"
       ( [_1] )
# 2236 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_098 =
  fun _3 _6 ->
    (
# 762 "src/parser.mly"
  ( 
    SWhile(_3,_6,!curr_brk,!curr_cont)
  )
# 2246 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_099 =
  fun _3 _6 ->
    (
# 766 "src/parser.mly"
  ( 
    SDoWhile(_3,_6,!curr_brk,!curr_cont)
  )
# 2256 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_100 =
  fun _3 _4 _5 _8 ->
    (
# 770 "src/parser.mly"
  ( 
    SFor(None,_3,_4,_5,_8,!curr_brk,!curr_cont)
  )
# 2266 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_101 =
  fun _3 _4 _5 _8 ->
    (
# 775 "src/parser.mly"
  ( 
    let ret = SFor(Some _3, None,_4,_5,_8,!curr_brk,!curr_cont) in
    pop_curr_scope ();
    ret
  )
# 2278 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_102 =
  fun _2 ->
    (
# 799 "src/parser.mly"
  ( 
    push_goto _2;
    SGoto _2
  )
# 2289 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_103 =
  fun () ->
    (
# 803 "src/parser.mly"
                ( SGoto !curr_cont )
# 2297 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_104 =
  fun () ->
    (
# 804 "src/parser.mly"
             ( SGoto !curr_brk )
# 2305 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_105 =
  fun _2 ->
    (
# 805 "src/parser.mly"
                   ( SReturn _2 )
# 2313 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_106 =
  fun _1 _3 ->
    (
# 725 "src/parser.mly"
  ( 
    push_label _1;
    SLabel(_1,SStmts _3)
  )
# 2324 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_107 =
  fun () ->
    (
# 617 "src/parser.mly"
  (
    in_declarator := false
  )
# 2334 "src/parser.ml"
     : (unit))

let _menhir_action_108 =
  fun () ->
    (
# 706 "src/parser.mly"
  (
    stack := List.tl !stack
  )
# 2344 "src/parser.ml"
     : (unit))

let _menhir_action_109 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2352 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_110 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2360 "src/parser.ml"
     : (Ast.stmt list))

let _menhir_action_111 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2368 "src/parser.ml"
     : (Ast.def list list))

let _menhir_action_112 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2376 "src/parser.ml"
     : (Ast.def list list))

let _menhir_action_113 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2384 "src/parser.ml"
     : (Ast.stmt list list))

let _menhir_action_114 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2392 "src/parser.ml"
     : (Ast.stmt list list))

let _menhir_action_115 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 2400 "src/parser.ml"
     : (Ctype.tq list))

let _menhir_action_116 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 2408 "src/parser.ml"
     : (Ctype.tq list))

let _menhir_action_117 =
  fun _1 ->
    (
# 447 "src/parser.mly"
                    ( _1 )
# 2416 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_118 =
  fun _1 _3 ->
    (
# 448 "src/parser.mly"
                                            ( EBinary(LogAnd,_1,_3) )
# 2424 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_119 =
  fun _1 ->
    (
# 451 "src/parser.mly"
                   ( _1 )
# 2432 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_120 =
  fun _1 _3 ->
    (
# 452 "src/parser.mly"
                                        ( EBinary(LogOr,_1,_3) )
# 2440 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_121 =
  fun () ->
    (
# 633 "src/parser.mly"
  ( enter_params () )
# 2448 "src/parser.ml"
     : (unit))

let _menhir_action_122 =
  fun _1 ->
    (
# 407 "src/parser.mly"
            ( _1 )
# 2456 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_123 =
  fun _1 _3 ->
    (
# 408 "src/parser.mly"
                                     ( EBinary(Mul,_1,_3) )
# 2464 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_124 =
  fun _1 _3 ->
    (
# 409 "src/parser.mly"
                                    ( EBinary(Div,_1,_3) )
# 2472 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_125 =
  fun _1 _3 ->
    (
# 410 "src/parser.mly"
                                    ( EBinary(Mod,_1,_3) )
# 2480 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_126 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2488 "src/parser.ml"
     : (unit option))

let _menhir_action_127 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2496 "src/parser.ml"
     : (unit option))

let _menhir_action_128 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2504 "src/parser.ml"
     : (unit option))

let _menhir_action_129 =
  fun () ->
    let x = 
# 642 "src/parser.mly"
                                       ()
# 2512 "src/parser.ml"
     in
    (
# 113 "<standard.mly>"
    ( Some x )
# 2517 "src/parser.ml"
     : (unit option))

let _menhir_action_130 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2525 "src/parser.ml"
     : (declarator option))

let _menhir_action_131 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2533 "src/parser.ml"
     : (declarator option))

let _menhir_action_132 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2541 "src/parser.ml"
     : (Ast.expr list option))

let _menhir_action_133 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2549 "src/parser.ml"
     : (Ast.expr list option))

let _menhir_action_134 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2557 "src/parser.ml"
     : (declarator option))

let _menhir_action_135 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2565 "src/parser.ml"
     : (declarator option))

let _menhir_action_136 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2573 "src/parser.ml"
     : (Ast.desig option))

let _menhir_action_137 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2581 "src/parser.ml"
     : (Ast.desig option))

let _menhir_action_138 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2589 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_139 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2597 "src/parser.ml"
     : (Ast.expr option))

let _menhir_action_140 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2605 "src/parser.ml"
     : (string option))

let _menhir_action_141 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2613 "src/parser.ml"
     : (string option))

let _menhir_action_142 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2621 "src/parser.ml"
     : (declarator list option))

let _menhir_action_143 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 2629 "src/parser.ml"
     : (declarator list option))

let _menhir_action_144 =
  fun _1 _2 ->
    (
# 653 "src/parser.mly"
  ( 
    [make_decl _1 _2]
  )
# 2639 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_145 =
  fun _1 _2 ->
    (
# 657 "src/parser.mly"
  (
    match _2 with
    | Some d -> [make_decl _1 d]
    | None -> [make_decl _1 (DeclIdent "")]
  )
# 2651 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_146 =
  fun _1 ->
    (
# 647 "src/parser.mly"
  ( _1 )
# 2659 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_147 =
  fun _1 _3 ->
    (
# 649 "src/parser.mly"
  ( _1@_3 )
# 2667 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_148 =
  fun () ->
    (
# 641 "src/parser.mly"
  ( [] )
# 2675 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_149 =
  fun _1 ->
    (
# 643 "src/parser.mly"
  ( _1 )
# 2683 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_150 =
  fun () ->
    (
# 629 "src/parser.mly"
  (  )
# 2691 "src/parser.ml"
     : (unit))

let _menhir_action_151 =
  fun _1 ->
    (
# 370 "src/parser.mly"
               ( _1 )
# 2699 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_152 =
  fun _1 _3 ->
    (
# 371 "src/parser.mly"
                                      ( EPostfix(_1,Nth _3) )
# 2707 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_153 =
  fun _1 _3 ->
    (
# 373 "src/parser.mly"
  ( 
    match _3 with
    | Some l -> EPostfix(_1,Call l)
    | None -> EPostfix(_1,Call [])
  )
# 2719 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_154 =
  fun _1 _3 ->
    (
# 378 "src/parser.mly"
                         ( EPostfix(_1,Member _3) )
# 2727 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_155 =
  fun _1 _3 ->
    (
# 379 "src/parser.mly"
                           ( EPostfix(EUnary(Deref,_1),Member _3) )
# 2735 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_156 =
  fun _1 ->
    (
# 380 "src/parser.mly"
                   ( EPostfix(_1,Inc) )
# 2743 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_157 =
  fun _1 ->
    (
# 381 "src/parser.mly"
                   ( EPostfix(_1,Dec) )
# 2751 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_158 =
  fun _2 _5 ->
    (
# 382 "src/parser.mly"
                                                         ( ECompoundLit(_2,IVect _5) )
# 2759 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_159 =
  fun _1 ->
    (
# 358 "src/parser.mly"
     ( EVar (get_var _1) )
# 2767 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_160 =
  fun _1 ->
    (
# 359 "src/parser.mly"
      ( EConst (VInt _1) )
# 2775 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_161 =
  fun _1 ->
    (
# 360 "src/parser.mly"
       ( ECast(TDeclSpec[(Ts TsUInt)],EConst(VInt _1)) )
# 2783 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_162 =
  fun _1 ->
    (
# 361 "src/parser.mly"
       ( ECast(TDeclSpec[(Ts TsLong)],EConst(VInt _1)) )
# 2791 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_163 =
  fun _1 ->
    (
# 362 "src/parser.mly"
        ( ECast(TDeclSpec[(Ts TsULong)],EConst(VInt _1)) )
# 2799 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_164 =
  fun _1 ->
    (
# 363 "src/parser.mly"
        ( EConst (VFloat _1) )
# 2807 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_165 =
  fun _1 ->
    (
# 364 "src/parser.mly"
         ( ECast(TDeclSpec[(Ts TsDouble)],EConst(VFloat _1)) )
# 2815 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_166 =
  fun _1 ->
    (
# 365 "src/parser.mly"
      ( EConst (VStr _1) )
# 2823 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_167 =
  fun _2 ->
    (
# 367 "src/parser.mly"
   ( _2 )
# 2831 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_168 =
  fun _1 ->
    (
# 423 "src/parser.mly"
             ( _1 )
# 2839 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_169 =
  fun _1 _3 ->
    (
# 424 "src/parser.mly"
                                ( EBinary(Lt,_1,_3) )
# 2847 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_170 =
  fun _1 _3 ->
    (
# 425 "src/parser.mly"
                                ( EBinary(Gt,_1,_3) )
# 2855 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_171 =
  fun _1 _3 ->
    (
# 426 "src/parser.mly"
                                ( EBinary(Le,_1,_3) )
# 2863 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_172 =
  fun _1 _3 ->
    (
# 427 "src/parser.mly"
                                ( EBinary(Ge,_1,_3) )
# 2871 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_173 =
  fun () ->
    (
# 637 "src/parser.mly"
  ( leave_params () )
# 2879 "src/parser.ml"
     : (unit))

let _menhir_action_174 =
  fun _3 _5 ->
    (
# 746 "src/parser.mly"
                                              ( SIfElse(_3,_5,SStmts []) )
# 2887 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_175 =
  fun _3 _5 _7 ->
    (
# 747 "src/parser.mly"
                                       ( SIfElse(_3,_5,_7) )
# 2895 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_176 =
  fun _3 _7 ->
    (
# 751 "src/parser.mly"
  ( 
    let ret = SSwitch(_3,_7,!curr_brk) in
    ret
  )
# 2906 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_177 =
  fun _1 ->
    (
# 418 "src/parser.mly"
                ( _1 )
# 2914 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_178 =
  fun _1 _3 ->
    (
# 419 "src/parser.mly"
                                  ( EBinary(LShift,_1,_3) )
# 2922 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_179 =
  fun _1 _3 ->
    (
# 420 "src/parser.mly"
                                  ( EBinary(RShift,_1,_3) )
# 2930 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_180 =
  fun _1 ->
    (
# 538 "src/parser.mly"
            ( [Ts _1] )
# 2938 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_181 =
  fun _1 _2 ->
    (
# 539 "src/parser.mly"
                           ( (Ts _1)::_2 )
# 2946 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_182 =
  fun _1 _2 ->
    (
# 540 "src/parser.mly"
                           ( (Tq _1)::_2 )
# 2954 "src/parser.ml"
     : (Ctype.ds list))

let _menhir_action_183 =
  fun () ->
    (
# 698 "src/parser.mly"
  ( raise (NotImpl "_Static_assert") )
# 2962 "src/parser.ml"
     : ('tv_static_assert_decl))

let _menhir_action_184 =
  fun _1 ->
    (
# 715 "src/parser.mly"
               ( _1 )
# 2970 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_185 =
  fun _1 ->
    (
# 716 "src/parser.mly"
                ( _1 )
# 2978 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_186 =
  fun _1 ->
    (
# 717 "src/parser.mly"
            ( expr_conv _1 )
# 2986 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_187 =
  fun _1 ->
    (
# 718 "src/parser.mly"
                   ( _1 )
# 2994 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_188 =
  fun _1 ->
    (
# 719 "src/parser.mly"
                        ( _1 )
# 3002 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_189 =
  fun _1 ->
    (
# 720 "src/parser.mly"
                      ( _1 )
# 3010 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_190 =
  fun _1 ->
    (
# 721 "src/parser.mly"
            ( _1 )
# 3018 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_191 =
  fun () ->
    (
# 513 "src/parser.mly"
          ( ScsTypedef )
# 3026 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_192 =
  fun () ->
    (
# 514 "src/parser.mly"
         ( ScsExtern )
# 3034 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_193 =
  fun () ->
    (
# 515 "src/parser.mly"
         ( ScsStatic )
# 3042 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_194 =
  fun () ->
    (
# 516 "src/parser.mly"
       ( ScsAuto )
# 3050 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_195 =
  fun () ->
    (
# 517 "src/parser.mly"
           ( ScsRegister )
# 3058 "src/parser.ml"
     : (Ctype.scs))

let _menhir_action_196 =
  fun _1 _2 ->
    (
# 568 "src/parser.mly"
  (
    match _2 with
    | Some dl -> make_decls (TDeclSpec _1) dl
    | None -> raise (NotImpl "struct_decl")
  )
# 3070 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_197 =
  fun () ->
    (
# 574 "src/parser.mly"
  ( raise (NotImpl "Static_assert") )
# 3078 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_198 =
  fun _1 ->
    (
# 563 "src/parser.mly"
              ( _1 )
# 3086 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_199 =
  fun _1 _2 ->
    (
# 564 "src/parser.mly"
                               ( _1@_2 )
# 3094 "src/parser.ml"
     : (Ctype.decl list))

let _menhir_action_200 =
  fun _1 ->
    (
# 581 "src/parser.mly"
             ( _1 )
# 3102 "src/parser.ml"
     : (declarator))

let _menhir_action_201 =
  fun () ->
    (
# 583 "src/parser.mly"
  ( raise (NotImpl "Bitfield") )
# 3110 "src/parser.ml"
     : (declarator))

let _menhir_action_202 =
  fun _1 ->
    (
# 577 "src/parser.mly"
                    ( [_1] )
# 3118 "src/parser.ml"
     : (declarator list))

let _menhir_action_203 =
  fun _1 _3 ->
    (
# 578 "src/parser.mly"
                                                 ( _1@[_3] )
# 3126 "src/parser.ml"
     : (declarator list))

let _menhir_action_204 =
  fun _2 _4 ->
    (
# 556 "src/parser.mly"
                                               ( make_struct _2 (Some _4) )
# 3134 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_205 =
  fun _2 ->
    (
# 557 "src/parser.mly"
               ( make_struct (Some _2) None )
# 3142 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_206 =
  fun _2 _4 ->
    (
# 558 "src/parser.mly"
                                              ( make_union _2 (Some _4) )
# 3150 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_207 =
  fun _2 ->
    (
# 559 "src/parser.mly"
              ( make_union (Some _2) None )
# 3158 "src/parser.ml"
     : (Ast.def option * Ctype.ts))

let _menhir_action_208 =
  fun _3 ->
    (
# 821 "src/parser.mly"
 (
    all_labels_exist ();
    SStmts(List.flatten _3)
  )
# 3169 "src/parser.ml"
     : (Ast.stmt))

let _menhir_action_209 =
  fun _1 ->
    (
# 351 "src/parser.mly"
  ( Program (List.flatten _1) )
# 3177 "src/parser.ml"
     : (Ast.program))

let _menhir_action_210 =
  fun _1 ->
    (
# 674 "src/parser.mly"
                 ( TDeclSpec _1 )
# 3185 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_211 =
  fun _1 _2 ->
    (
# 676 "src/parser.mly"
  ( snd (make_decl (TDeclSpec _1) _2) )
# 3193 "src/parser.ml"
     : (Ctype.ty))

let _menhir_action_212 =
  fun () ->
    (
# 543 "src/parser.mly"
        ( TqConst )
# 3201 "src/parser.ml"
     : (Ctype.tq))

let _menhir_action_213 =
  fun () ->
    (
# 544 "src/parser.mly"
           ( TqVolatile )
# 3209 "src/parser.ml"
     : (Ctype.tq))

let _menhir_action_214 =
  fun () ->
    (
# 520 "src/parser.mly"
        ( TsVoid )
# 3217 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_215 =
  fun () ->
    (
# 521 "src/parser.mly"
        ( TsChar )
# 3225 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_216 =
  fun () ->
    (
# 522 "src/parser.mly"
         ( TsShort)
# 3233 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_217 =
  fun () ->
    (
# 523 "src/parser.mly"
       ( TsInt )
# 3241 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_218 =
  fun () ->
    (
# 524 "src/parser.mly"
        ( TsLong )
# 3249 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_219 =
  fun () ->
    (
# 525 "src/parser.mly"
         ( TsFloat )
# 3257 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_220 =
  fun () ->
    (
# 526 "src/parser.mly"
          ( TsDouble )
# 3265 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_221 =
  fun () ->
    (
# 527 "src/parser.mly"
          ( TsSigned )
# 3273 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_222 =
  fun () ->
    (
# 528 "src/parser.mly"
            ( TsUnsigned )
# 3281 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_223 =
  fun _1 ->
    (
# 529 "src/parser.mly"
                       ( 
  match _1 with
  | (Some def,ts) -> add_def def;ts
  | (None,ts) -> ts
  )
# 3293 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_224 =
  fun _1 ->
    (
# 534 "src/parser.mly"
            ( _1 )
# 3301 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_225 =
  fun _1 ->
    (
# 535 "src/parser.mly"
          ( TsTypedef (get_typedef _1) )
# 3309 "src/parser.ml"
     : (Ctype.ts))

let _menhir_action_226 =
  fun _1 ->
    (
# 389 "src/parser.mly"
               ( _1 )
# 3317 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_227 =
  fun _2 ->
    (
# 390 "src/parser.mly"
                 ( EUnary(PreInc, _2) )
# 3325 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_228 =
  fun _2 ->
    (
# 391 "src/parser.mly"
                 ( EUnary(PreDec, _2) )
# 3333 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_229 =
  fun _2 ->
    (
# 392 "src/parser.mly"
                 ( EUnary(Ref, _2) )
# 3341 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_230 =
  fun _2 ->
    (
# 393 "src/parser.mly"
                 ( EUnary(Deref, _2) )
# 3349 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_231 =
  fun _2 ->
    (
# 394 "src/parser.mly"
                 ( EUnary(Plus, _2) )
# 3357 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_232 =
  fun _2 ->
    (
# 395 "src/parser.mly"
                  ( EUnary(Minus, _2) )
# 3365 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_233 =
  fun _2 ->
    (
# 396 "src/parser.mly"
                ( EUnary(BitNot, _2) )
# 3373 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_234 =
  fun _2 ->
    (
# 397 "src/parser.mly"
                 ( EUnary(LogNot, _2) )
# 3381 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_235 =
  fun _2 ->
    (
# 398 "src/parser.mly"
                    ( EUnary(Sizeof, _2) )
# 3389 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_236 =
  fun _3 ->
    (
# 399 "src/parser.mly"
                                 ( ETyUnary(Sizeof,_3) )
# 3397 "src/parser.ml"
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
  
  let rec _menhir_run_297 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _v ->
      let _1 = _v in
      let _v = _menhir_action_209 _1 in
      MenhirBox_translation_unit _v
  
  let rec _menhir_run_406 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_external_decl -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _v ->
      let MenhirCell1_external_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_112 x xs in
      _menhir_goto_list_external_decl_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_external_decl_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState405 ->
          _menhir_run_406 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_297 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_213 () in
      _menhir_goto_type_qual _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_qual : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState405 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState191 ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState190 ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState292 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState275 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
      let _v = _menhir_action_039 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_252 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState368 ->
          _menhir_run_252 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState226 ->
          _menhir_run_252 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState000 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState405 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_252 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_044 _1 _2 in
      _menhir_goto_decl_specs _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl_specs : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_407 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState405 ->
          _menhir_run_407 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_368 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_407 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState407
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | SEMI ->
          _menhir_run_369 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | LPAREN ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState407
      | ID _ ->
          let _menhir_s = MenhirState407 in
          let _v = _menhir_action_060 () in
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
          let _v = _menhir_action_140 () in
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState002
      | _ ->
          _eRR ()
  
  and _menhir_run_003 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_085 _1 in
      _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_ident : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState303 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_356 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState328 ->
          _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState002 ->
          _menhir_run_294 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_291 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
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
  
  and _menhir_run_356 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState357
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState357
          | TYPE_ID _v_2 ->
              _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState357
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState357
          | STATIC_ASSERT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState357
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState357
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState357
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState357
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState357
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState357
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState357
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_304 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState305 in
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
      let _v = _menhir_action_163 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_primary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_151 _1 in
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
              let _v = _menhir_action_132 () in
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
          let _v = _menhir_action_156 _1 in
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
          let _v = _menhir_action_157 _1 in
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
          let _v = _menhir_action_226 _1 in
          _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_023 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_161 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_166 _1 in
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
          let _menhir_s = MenhirState265 in
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
      let _v = _menhir_action_225 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState405 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState292 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState275 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
      let _v = _menhir_action_042 _1 in
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
          let _v = _menhir_action_180 _1 in
          _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_008 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_214 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_009 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_222 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_221 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_011 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_216 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_012 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_218 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_013 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_217 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_219 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_220 () in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_215 () in
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
          let _v = _menhir_action_140 () in
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState017
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_084 _1 in
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
      let _v = _menhir_action_162 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_032 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_160 _1 in
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
      let _v = _menhir_action_159 _1 in
      _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_036 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _1 = _v in
      let _v = _menhir_action_164 _1 in
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
          let _v = _menhir_action_140 () in
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
      let _v = _menhir_action_165 _1 in
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
      let _v = _menhir_action_212 () in
      _menhir_goto_type_qual _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_spec_qual_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState292 ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState275 ->
          _menhir_run_279 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
  
  and _menhir_run_279 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState279
      | LPAREN ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState279
      | ID _ ->
          let _menhir_s = MenhirState279 in
          let _v = _menhir_action_060 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COLON ->
          let _menhir_s = MenhirState279 in
          let _v = _menhir_action_134 () in
          _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | SEMI ->
          let _v = _menhir_action_142 () in
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
      | COMMA | ID _ | LPAREN | RPAREN | STAR ->
          let _ = _menhir_action_115 () in
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_193 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STAR -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_STAR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_150 () in
      _menhir_goto_pointer _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_pointer : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState279 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState281 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState229 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState230 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState228 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState189 ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState194 ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_229 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState229
      | LPAREN ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState229
      | ID _ ->
          let _menhir_s = MenhirState229 in
          let _v = _menhir_action_060 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_230 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState230 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _ ->
          _menhir_reduce_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_reduce_060 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_060 () in
      _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_enter_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_enter_declarator (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ID _v_0 ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _ = _menhir_action_107 () in
          let MenhirCell0_ID (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_enter_declarator (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let _v = _menhir_action_055 _2 in
          _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_direct_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState234
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _v) in
          let _menhir_stack = MenhirCell1_LBRACKET (_menhir_stack, MenhirState234) in
          let _menhir_s = MenhirState235 in
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
      | COLON | COMMA | EQ | LBRACE | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_046 _1 in
          _menhir_goto_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_197 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_121 () in
      _menhir_goto_lp _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_lp : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState234 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState247 ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState196 ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_238 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lp (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState238
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | RPAREN ->
          let _v_1 = _menhir_action_148 () in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState238 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_202 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_191 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_storage_class_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_038 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_203 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_193 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_204 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_195 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_205 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_083 () in
      _menhir_goto_function_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_function_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_040 _1 in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_206 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_082 () in
      _menhir_goto_function_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_207 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_192 () in
      _menhir_goto_storage_class_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_208 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_194 () in
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
  
  and _menhir_run_239 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_parameter_type_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState239
      | _ ->
          _eRR ()
  
  and _menhir_run_219 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _ = _menhir_action_173 () in
      _menhir_goto_rp _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
  
  and _menhir_goto_rp : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      match _menhir_s with
      | MenhirState239 ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState218 ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_240 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_type_list (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_lp (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_058 _1 _3 in
      _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_220 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_type_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_type_list (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_lp (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_054 _1 _3 in
      _menhir_goto_direct_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_direct_abstract_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState189 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState194 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState228 ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState195 ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_247 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState247
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState247
      | COMMA | RPAREN ->
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
          _menhir_run_255 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState226 ->
          _menhir_run_253 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState194 ->
          _menhir_run_248 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState227 ->
          _menhir_run_248 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_255 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_spec_qual_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_211 _1 _2 in
      _menhir_goto_type_name _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_type_name : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState265 ->
          _menhir_run_266 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_259 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState034 ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_266 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SIZEOF, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACE ->
              let _menhir_stack = MenhirCell1_type_name (_menhir_stack, _menhir_s, _v) in
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState267
          | ADD_EQ | AND | ANDAND | AND_EQ | COLON | COMMA | DIV | DIV_EQ | EQ | EQEQ | GE | GT | HAT | LE | LSHIFT | LSHIFT_EQ | LT | MINUS | MOD | MOD_EQ | MUL_EQ | NE | OR | OROR | OR_EQ | PLUS | QUESTION | RBRACE | RBRACKET | RPAREN | RSHIFT | RSHIFT_EQ | SEMI | STAR | SUB_EQ | XOR_EQ ->
              let MenhirCell1_LPAREN (_menhir_stack, _) = _menhir_stack in
              let MenhirCell1_SIZEOF (_menhir_stack, _menhir_s) = _menhir_stack in
              let _3 = _v in
              let _v = _menhir_action_236 _3 in
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
          let _v = _menhir_action_136 () in
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
          let _v = _menhir_action_136 () in
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState174 _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_unary_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState026 ->
          _menhir_run_268 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState033 ->
          _menhir_run_258 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState046 ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState303 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
      | MenhirState393 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
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
      | MenhirState260 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
  
  and _menhir_run_268 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SIZEOF -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SIZEOF (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_235 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_258 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_INC -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_INC (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_227 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_148 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DEC -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_DEC (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_228 _2 in
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
          let _v = _menhir_action_028 _1 in
          _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_cast_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState025 ->
          _menhir_run_269 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState027 ->
          _menhir_run_264 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState028 ->
          _menhir_run_263 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState029 ->
          _menhir_run_262 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState260 ->
          _menhir_run_261 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState047 ->
          _menhir_run_147 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState048 ->
          _menhir_run_146 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState303 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
  
  and _menhir_run_269 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STAR -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_STAR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_230 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_264 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_PLUS -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_PLUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_231 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_263 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_233 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_262 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_MINUS -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_232 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_261 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN, _menhir_box_translation_unit) _menhir_cell1_type_name -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_name (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_029 _2 _4 in
      _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_147 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_BANG -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_BANG (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_234 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_146 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_AND -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_AND (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_229 _2 in
      _menhir_goto_unary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_122 _1 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_multiplicative_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState068 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
      | MenhirState303 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_177 _1 in
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
      | MenhirState303 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_172 _1 _3 in
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
      | MenhirState303 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_070 _1 _3 in
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
      | MenhirState303 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
      | MenhirState303 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_072 _1 in
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
      | MenhirState303 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_086 _1 in
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
      | MenhirState303 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_117 _1 in
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
      | MenhirState303 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState393 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
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
          let _v = _menhir_action_120 _1 _3 in
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
          let _v = _menhir_action_031 _1 in
          _menhir_goto_conditional_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_conditional_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState393 ->
          _menhir_run_394 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState021 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState235 ->
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
      | MenhirState303 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState375 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
  
  and _menhir_run_394 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_CASE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_conditional_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState395
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState395
          | TYPE_ID _v_2 ->
              _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState395
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState395
          | STATIC_ASSERT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState395
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState395
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState395
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState395
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState395
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState395
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState395
          | CASE | DEFAULT | RBRACE ->
              let _v_10 = _menhir_action_113 () in
              _menhir_run_396 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_317 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _1 = _v in
          let _v = _menhir_action_085 _1 in
          _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ALIGNAS | AUTO | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let _1 = _v in
          let _v = _menhir_action_225 _1 in
          _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_309 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SWITCH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState310 in
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
  
  and _menhir_run_318 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_076 () in
      _menhir_goto_expr_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState382 ->
          _menhir_run_383 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_360 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_320 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_383 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState383
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState383
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState383
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState383
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState383
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState383
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState383
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState383
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState383
      | RPAREN ->
          let _v_8 = _menhir_action_138 () in
          _menhir_run_384 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState383
      | _ ->
          _eRR ()
  
  and _menhir_run_384 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_expr_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v_0 = _menhir_action_025 () in
      let (_v, _menhir_s) = (_v_0, MenhirState385) in
      let _menhir_stack = MenhirCell1_begin_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState386
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState386
      | TYPE_ID _v_2 ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState386
      | SWITCH ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState386
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | RETURN ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState386
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState386
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | IF ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | ID _v_6 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState386
      | GOTO ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | FOR ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState386
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState386
      | DO ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | CONTINUE ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | BREAK ->
          _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState386
      | LBRACE ->
          let _v_9 = _menhir_action_061 () in
          _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState386
      | _ ->
          _eRR ()
  
  and _menhir_run_319 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState319 in
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
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
  
  and _menhir_run_323 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState324 in
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
  
  and _menhir_run_327 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _1 = _v in
          let _v = _menhir_action_084 _1 in
          _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ADD_EQ | AND | ANDAND | AND_EQ | ARROW | COMMA | DEC | DIV | DIV_EQ | DOT | EQ | EQEQ | GE | GT | HAT | INC | LBRACKET | LE | LPAREN | LSHIFT | LSHIFT_EQ | LT | MINUS | MOD | MOD_EQ | MUL_EQ | NE | OR | OROR | OR_EQ | PLUS | QUESTION | RSHIFT | RSHIFT_EQ | SEMI | STAR | SUB_EQ | XOR_EQ ->
          let _1 = _v in
          let _v = _menhir_action_159 _1 in
          _menhir_goto_primary_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_328 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_GOTO (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState328 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYPE_ID _v ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ID _v ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_331 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState332 in
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
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
  
  and _menhir_run_338 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DO (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_025 () in
      let _menhir_s = MenhirState338 in
      let _menhir_stack = MenhirCell1_begin_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState339
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState339
      | TYPE_ID _v_2 ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState339
      | SWITCH ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState339
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | RETURN ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState339
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState339
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | IF ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | ID _v_6 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState339
      | GOTO ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | FOR ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState339
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState339
      | DO ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | CONTINUE ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | BREAK ->
          _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState339
      | LBRACE ->
          let _v_9 = _menhir_action_061 () in
          _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState339
      | _ ->
          _eRR ()
  
  and _menhir_run_340 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_103 () in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_jump_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_190 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState308 ->
          _menhir_run_401 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState390 ->
          _menhir_run_391 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState326 ->
          _menhir_run_389 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_387 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState337 ->
          _menhir_run_380 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState303 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_358 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_344 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_401 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_WHILE, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_begin_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_begin_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _6 = _v in
      let _v = _menhir_action_098 _3 _6 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_iteration_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_iteration_stmt (_menhir_stack, _menhir_s, _v) in
      let _ = _menhir_action_059 () in
      let MenhirCell1_iteration_stmt (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_189 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_391 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_stmt -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_stmt (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let _7 = _v in
      let _v = _menhir_action_175 _3 _5 _7 in
      _menhir_goto_selection_stmt_1 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_selection_stmt_1 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_187 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_389 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF, _menhir_box_translation_unit) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState390
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState390
          | TYPE_ID _v_2 ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState390
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState390
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState390
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState390
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState390
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState390
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState390
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState390
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState390
          | _ ->
              _eRR ())
      | ALIGNAS | AND | AUTO | BANG | BREAK | CASE | CONST | CONTINUE | DEC | DEFAULT | DO | DOUBLE _ | ENUM | EXTERN | FLOAT _ | FOR | GOTO | ID _ | IF | INC | INLINE | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NORETURN | NOT | PLUS | RBRACE | REGISTER | RETURN | SEMI | SIZEOF | STAR | STATIC | STATIC_ASSERT | STR _ | STRUCT | SWITCH | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UINT _ | ULINT _ | UNION | VOLATILE | WHILE ->
          let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let _5 = _v in
          let _v = _menhir_action_174 _3 _5 in
          _menhir_goto_selection_stmt_1 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_342 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_104 () in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_361 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_enter_scope (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState362
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState362
      | TYPE_ID _v_2 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState362
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | SWITCH ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState362
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | RETURN ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState362
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState362
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | IF ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | ID _v_6 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState362
      | GOTO ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | FOR ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState362
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState362
      | DO ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | CONTINUE ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | BREAK ->
          _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState362
      | LBRACE ->
          let _v_9 = _menhir_action_061 () in
          _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState362
      | RBRACE ->
          let _v_10 = _menhir_action_113 () in
          _menhir_run_363 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10 MenhirState362 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_363 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_enter_scope as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_list_item_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _ = _menhir_action_108 () in
          let MenhirCell1_list_item_ (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_enter_scope (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let _v = _menhir_action_030 _3 in
          let _1 = _v in
          let _v = _menhir_action_185 _1 in
          _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_387 : type  ttv_stack. (((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_decl_for_for_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_cell1_begin_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_begin_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_option_expr_ (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _4) = _menhir_stack in
      let MenhirCell1_decl_for_for_stmt (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _8 = _v in
      let _v = _menhir_action_101 _3 _4 _5 _8 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_380 : type  ttv_stack. (((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_option_expr_, _menhir_box_translation_unit) _menhir_cell1_begin_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_begin_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_option_expr_ (_menhir_stack, _, _5) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _4) = _menhir_stack in
      let MenhirCell1_expr_stmt (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
      let _8 = _v in
      let _v = _menhir_action_100 _3 _4 _5 _8 in
      _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_358 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_097 _1 in
      _menhir_goto_item _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_item : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState303 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_366 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_359 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_366 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_item (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState366
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState366
      | TYPE_ID _v_2 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState366
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | SWITCH ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState366
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | RETURN ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState366
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState366
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | IF ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | ID _v_6 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState366
      | GOTO ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | FOR ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState366
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState366
      | DO ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | CONTINUE ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | BREAK ->
          _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState366
      | LBRACE ->
          let _v_9 = _menhir_action_061 () in
          _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState366
      | CASE | DEFAULT | RBRACE ->
          let _v_10 = _menhir_action_113 () in
          _menhir_run_367 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_367 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_item -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_item (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_114 x xs in
      _menhir_goto_list_item_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_list_item_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState303 ->
          _menhir_run_402 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_396 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState316 ->
          _menhir_run_392 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState366 ->
          _menhir_run_367 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState362 ->
          _menhir_run_363 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_402 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_function_decl, _menhir_box_translation_unit) _menhir_cell1_enter_scope as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_list_item_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _ = _menhir_action_108 () in
          let MenhirCell1_list_item_ (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_enter_scope (_menhir_stack, _, _) = _menhir_stack in
          let _v = _menhir_action_208 _3 in
          let MenhirCell1_function_decl (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_081 _1 _2 in
          let _1 = _v in
          let _v = _menhir_action_078 _1 in
          _menhir_goto_external_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_external_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_external_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState405
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | STATIC_ASSERT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState405
      | EOF ->
          let _v_1 = _menhir_action_111 () in
          _menhir_run_406 _menhir_stack _v_1
      | _ ->
          _eRR ()
  
  and _menhir_run_396 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_CASE, _menhir_box_translation_unit) _menhir_cell1_conditional_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_conditional_expr (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_CASE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_026 _2 _4 in
      _menhir_goto_case_or_default _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_case_or_default : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_case_or_default (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | DEFAULT ->
          _menhir_run_315 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState399
      | CASE ->
          _menhir_run_393 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState399
      | RBRACE ->
          let _v_0 = _menhir_action_109 () in
          _menhir_run_400 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_315 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DEFAULT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | ULINT _v ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | UINT _v ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | TYPE_ID _v ->
              _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | STR _v ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | STATIC_ASSERT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | LINT _v ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | INT _v ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | ID _v ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | FLOAT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | DOUBLE _v ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState316
          | LBRACE ->
              let _v = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState316
          | CASE | DEFAULT | RBRACE ->
              let _v = _menhir_action_113 () in
              _menhir_run_392 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_392 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DEFAULT -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_DEFAULT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_027 _3 in
      _menhir_goto_case_or_default _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_393 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_CASE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState393 in
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
  
  and _menhir_run_400 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_case_or_default -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_case_or_default (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_110 x xs in
      _menhir_goto_list_case_or_default_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_case_or_default_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState399 ->
          _menhir_run_400 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState314 ->
          _menhir_run_397 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_397 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SWITCH, _menhir_box_translation_unit) _menhir_cell1_expr, _menhir_box_translation_unit) _menhir_cell1_begin_ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_begin_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_SWITCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let _7 = _v in
      let _v = _menhir_action_176 _3 _7 in
      let _menhir_stack = MenhirCell1_selection_stmt_2 (_menhir_stack, _menhir_s, _v) in
      let _ = _menhir_action_059 () in
      let MenhirCell1_selection_stmt_2 (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_188 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_359 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_106 _1 _3 in
      let _1 = _v in
      let _v = _menhir_action_184 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_344 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_begin_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _menhir_s = MenhirState346 in
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
  
  and _menhir_run_360 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_186 _1 in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_334 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState334
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState334
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState334
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState334
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState334
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState334
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState334
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState334
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState334
      | RPAREN ->
          let _v_8 = _menhir_action_138 () in
          _menhir_run_335 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState334
      | _ ->
          _eRR ()
  
  and _menhir_run_335 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR, _menhir_box_translation_unit) _menhir_cell1_expr_stmt, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_expr_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v_0 = _menhir_action_025 () in
      let (_v, _menhir_s) = (_v_0, MenhirState336) in
      let _menhir_stack = MenhirCell1_begin_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState337
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState337
      | TYPE_ID _v_2 ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState337
      | SWITCH ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | STR _v_3 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState337
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | RETURN ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | LINT _v_4 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState337
      | INT _v_5 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState337
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | IF ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | ID _v_6 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState337
      | GOTO ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | FOR ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | FLOAT _v_7 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState337
      | DOUBLE _v_8 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState337
      | DO ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | CONTINUE ->
          _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | BREAK ->
          _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState337
      | LBRACE ->
          let _v_9 = _menhir_action_061 () in
          _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState337
      | _ ->
          _eRR ()
  
  and _menhir_run_333 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState333
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState333
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState333
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState333
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState333
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState333
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState333
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState333
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState333
      | _ ->
          _eRR ()
  
  and _menhir_run_320 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_RETURN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_RETURN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_105 _2 in
      _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_150 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_033 () in
      _menhir_goto_constant_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_constant_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState284 ->
          _menhir_run_285 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState021 ->
          _menhir_run_270 _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | MenhirState235 ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
  
  and _menhir_run_285 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_declarator_ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_option_declarator_ (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_201 () in
      _menhir_goto_struct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState279 ->
          _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState281 ->
          _menhir_run_282 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_287 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_202 _1 in
      _menhir_goto_struct_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_declarator_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_struct_declarator_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState281 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _ ->
              _menhir_reduce_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
          | COLON ->
              let _v = _menhir_action_134 () in
              _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | SEMI ->
          let x = _v in
          let _v = _menhir_action_143 x in
          _menhir_goto_option_struct_declarator_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_declarator_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_option_declarator_ (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState284 in
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
      let _v = _menhir_action_196 _1 _2 in
      _menhir_goto_struct_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_290 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_290 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState292 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState275 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_290 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_198 _1 in
      _menhir_goto_struct_decl_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_struct_decl_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState006 ->
          _menhir_run_292 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_275 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_292 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_UNION, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | UNION ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TYPE_ID _v_0 ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState292
      | TVOID ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TUNSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TSHORT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TLONG ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TINT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TFLOAT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TDOUBLE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | TCHAR ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | STRUCT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | STATIC_ASSERT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_option_ident_ (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_UNION (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_206 _2 _4 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ENUM ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | CONST ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState292
      | _ ->
          _eRR ()
  
  and _menhir_goto_struct_or_union_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_223 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_275 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STRUCT, _menhir_box_translation_unit) _menhir_cell1_option_ident_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | UNION ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TYPE_ID _v_0 ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState275
      | TVOID ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TUNSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TSIGNED ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TSHORT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TLONG ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TINT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TFLOAT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TDOUBLE ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | TCHAR ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | STRUCT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | STATIC_ASSERT ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_option_ident_ (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_204 _2 _4 in
          _menhir_goto_struct_or_union_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ENUM ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | CONST ->
          let _menhir_stack = MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _v) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState275
      | _ ->
          _eRR ()
  
  and _menhir_run_277 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_struct_decl_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_struct_decl_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_199 _1 _2 in
      _menhir_goto_struct_decl_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_282 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_spec_qual_list, _menhir_box_translation_unit) _menhir_cell1_struct_declarator_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_struct_declarator_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_203 _1 _3 in
      _menhir_goto_struct_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_270 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STATIC_ASSERT -> _ -> _ -> _ -> _menhir_box_translation_unit =
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
                      let _ = _menhir_action_183 () in
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
      | MenhirState405 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState292 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState275 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_296 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _ = _menhir_action_036 () in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_409 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState405 ->
          _menhir_run_409 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_388 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_378 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_409 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_079 () in
      _menhir_goto_external_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_388 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_FOR as 'stack) -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_037 () in
      let _menhir_stack = MenhirCell1_decl_for_for_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ULINT _v_0 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState382
      | UINT _v_1 ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState382
      | STR _v_2 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState382
      | STAR ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | SIZEOF ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | SEMI ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | PLUS ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | NOT ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | MINUS ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | LPAREN ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | LINT _v_3 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState382
      | INT _v_4 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState382
      | INC ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | ID _v_5 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState382
      | FLOAT _v_6 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState382
      | DOUBLE _v_7 ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState382
      | DEC ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | BANG ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | AND ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState382
      | _ ->
          _eRR ()
  
  and _menhir_run_378 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_096 () in
      _menhir_goto_item _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_278 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_197 () in
      _menhir_goto_struct_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_236 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACKET (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_direct_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_057 _1 _3 in
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
      let _v = _menhir_action_041 () in
      _menhir_goto_decl_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_199 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_direct_abstract_declarator, _menhir_box_translation_unit) _menhir_cell1_LBRACKET -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACKET (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_direct_abstract_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_053 _1 _3 in
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
              let _v = _menhir_action_048 _2 in
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
      let _v = _menhir_action_047 _1 in
      let x = _v in
      let _v = _menhir_action_137 x in
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
      let _v = _menhir_action_050 _2 _4 in
      _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_171 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DOT, _menhir_box_translation_unit) _menhir_cell1_ident -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_ident (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_DOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_051 _2 _3 in
      _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_149 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_enum_const -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_enum_const (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _ = _menhir_action_063 () in
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
      let _v = _menhir_action_065 () in
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
                _menhir_action_127 x
              in
              _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | RBRACE ->
          let _ = _menhir_action_126 () in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_152 : type  ttv_stack. (((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_enum_list (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_option_ident_ (_menhir_stack, _, _) = _menhir_stack in
      let MenhirCell1_ENUM (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_067 () in
      _menhir_goto_enum_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_enum_spec : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_224 _1 in
      _menhir_goto_type_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_151 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM, _menhir_box_translation_unit) _menhir_cell1_option_ident_, _menhir_box_translation_unit) _menhir_cell1_enum_list, _menhir_box_translation_unit) _menhir_cell1_COMMA -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_enum_list (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _v = _menhir_action_066 () in
      _menhir_goto_enum_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_106 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_logical_or_expr, _menhir_box_translation_unit) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_logical_or_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _5 = _v in
      let _v = _menhir_action_032 _1 _3 _5 in
      _menhir_goto_conditional_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_103 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_013 _1 in
      _menhir_goto_assignment_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_assignment_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState375 ->
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
      | MenhirState303 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState383 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
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
      let _v = _menhir_action_088 _1 in
      _menhir_goto_init _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState375 ->
          _menhir_run_376 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState173 ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState177 ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_376 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_declarator -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_declarator (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_091 _1 _3 in
      _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_377 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_377 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_373 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_377 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_092 _1 in
      _menhir_goto_init_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_init_declarator_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _ = _menhir_action_035 _1 _2 in
          _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_init_declarator_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState372 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ID _ ->
              _menhir_reduce_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_373 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs, _menhir_box_translation_unit) _menhir_cell1_init_declarator_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_init_declarator_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_093 _1 _3 in
      _menhir_goto_init_declarator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_185 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_option_desig_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_option_desig_ (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_094 _1 _2 in
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
          let _ = _menhir_action_126 () in
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
          let _ = _menhir_action_127 x in
          _menhir_goto_option_COMMA_ _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AND | BANG | DEC | DOUBLE _ | FLOAT _ | ID _ | INC | INT _ | LBRACE | LINT _ | LPAREN | MINUS | NOT | PLUS | SIZEOF | STAR | STR _ | UINT _ | ULINT _ ->
          let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, _menhir_s) in
          let _v = _menhir_action_136 () in
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
      let _v = _menhir_action_158 _2 _5 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_183 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_init_list (_menhir_stack, _, _2) = _menhir_stack in
      let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_089 _2 in
      _menhir_goto_init _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_175 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_init_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState175
      | RBRACE ->
          let _ = _menhir_action_126 () in
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_178 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LBRACE, _menhir_box_translation_unit) _menhir_cell1_init_list, _menhir_box_translation_unit) _menhir_cell1_COMMA, _menhir_box_translation_unit) _menhir_cell1_option_desig_ -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_option_desig_ (_menhir_stack, _, _3) = _menhir_stack in
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_init_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_095 _1 _3 _4 in
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
          let _v = _menhir_action_133 x in
          _menhir_goto_option_argument_expr_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_argument_expr_list_ : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_153 _1 _3 in
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
      let _v = _menhir_action_074 _1 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState383 ->
          _menhir_run_381 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState334 ->
          _menhir_run_381 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState346 ->
          _menhir_run_347 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState324 ->
          _menhir_run_325 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState308 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState395 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState326 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState390 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState382 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState386 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState339 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState362 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState366 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState357 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState319 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState310 ->
          _menhir_run_311 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_306 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState265 ->
          _menhir_run_256 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_256 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_256 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState083 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_381 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_139 x in
          _menhir_goto_option_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
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
  
  and _menhir_goto_option_expr_ : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_expr_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState383 ->
          _menhir_run_384 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState334 ->
          _menhir_run_335 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_347 : type  ttv_stack. ((((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_DO, _menhir_box_translation_unit) _menhir_cell1_begin_, _menhir_box_translation_unit) _menhir_cell1_stmt as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_stmt (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_begin_ (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_DO (_menhir_stack, _menhir_s) = _menhir_stack in
          let _6 = _v in
          let _v = _menhir_action_099 _3 _6 in
          _menhir_goto_iteration_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_325 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState326
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState326
          | TYPE_ID _v_2 ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState326
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState326
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState326
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState326
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState326
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState326
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState326
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState326
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState326
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_321 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_077 _1 in
          _menhir_goto_expr_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_311 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_SWITCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v_0 = _menhir_action_025 () in
          let (_v, _menhir_s) = (_v_0, MenhirState312) in
          let _menhir_stack = MenhirCell1_begin_ (_menhir_stack, _menhir_s, _v) in
          (match (_tok : MenhirBasics.token) with
          | LBRACE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | DEFAULT ->
                  _menhir_run_315 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState314
              | CASE ->
                  _menhir_run_393 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState314
              | RBRACE ->
                  let _v_0 = _menhir_action_109 () in
                  _menhir_run_397 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_306 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v_0 = _menhir_action_025 () in
          let (_v, _menhir_s) = (_v_0, MenhirState307) in
          let _menhir_stack = MenhirCell1_begin_ (_menhir_stack, _menhir_s, _v) in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState308
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState308
          | TYPE_ID _v_2 ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState308
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState308
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState308
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState308
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState308
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState308
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState308
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState308
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState308
          | _ ->
              _eRR ())
      | COMMA ->
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_256 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_167 _2 in
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
          let _v = _menhir_action_152 _1 _3 in
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
      let _v = _menhir_action_075 _1 _3 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_084 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ANDAND ->
          let _menhir_stack = MenhirCell1_logical_and_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COLON | COMMA | OROR | QUESTION | RBRACE | RBRACKET | RPAREN | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_119 _1 in
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
          let _v = _menhir_action_118 _1 _3 in
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
          let _v = _menhir_action_087 _1 _3 in
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
          let _v = _menhir_action_073 _1 _3 in
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
          let _v = _menhir_action_071 _1 _3 in
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
          let _v = _menhir_action_069 _1 in
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
          let _v = _menhir_action_170 _1 _3 in
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
          let _v = _menhir_action_171 _1 _3 in
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
          let _v = _menhir_action_169 _1 _3 in
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
          let _v = _menhir_action_168 _1 in
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
          let _v = _menhir_action_178 _1 _3 in
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
          let _v = _menhir_action_179 _1 _3 in
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
      let _v = _menhir_action_124 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_061 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_125 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_059 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_multiplicative_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_multiplicative_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_123 _1 _3 in
      _menhir_goto_multiplicative_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_049 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_028 _1 in
      _menhir_goto_cast_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_259 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_name (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState260 in
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
  
  and _menhir_run_253 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_131 x in
      _menhir_goto_option_abstract_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_option_abstract_declarator_ : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_145 _1 _2 in
      _menhir_goto_parameter_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState201 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_241 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_146 _1 in
      _menhir_goto_parameter_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TYPE_ID _v_0 ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState222
          | TYPEDEF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TVOID ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TUNSIGNED ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TSIGNED ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TSHORT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TLONG ->
              _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TINT ->
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TFLOAT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TDOUBLE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | TCHAR ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | ELLIPSIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _ = _menhir_action_129 () in
              _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _tok
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState222
          | _ ->
              _eRR ())
      | RPAREN ->
          let _ = _menhir_action_128 () in
          _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_option___anonymous_0_ : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_list -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _tok ->
      let MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v = _menhir_action_149 _1 in
      _menhir_goto_parameter_type_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_parameter_type_list : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState238 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
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
  
  and _menhir_run_224 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_lp, _menhir_box_translation_unit) _menhir_cell1_parameter_list -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_parameter_list (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_147 _1 _3 in
      _menhir_goto_parameter_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_248 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_052 _2 in
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
      | COMMA | RPAREN ->
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
          let _v_1 = _menhir_action_148 () in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState201 _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_declarator : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState407 ->
          _menhir_run_408 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState368 ->
          _menhir_run_374 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState372 ->
          _menhir_run_374 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState279 ->
          _menhir_run_286 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState281 ->
          _menhir_run_286 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_251 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState228 ->
          _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState229 ->
          _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState227 ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState230 ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_408 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_stack = MenhirCell1_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_375 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACE ->
          let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_080 _1 _2 in
          let _menhir_stack = MenhirCell1_function_decl (_menhir_stack, _menhir_s, _v) in
          let _v_0 = _menhir_action_061 () in
          let (_v, _menhir_s) = (_v_0, MenhirState300) in
          let _menhir_stack = MenhirCell1_enter_scope (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | VOLATILE ->
              _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | UNION ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | ULINT _v_0 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState303
          | UINT _v_1 ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState303
          | TYPE_ID _v_2 ->
              _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState303
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
          | SWITCH ->
              _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | STRUCT ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | STR _v_3 ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState303
          | STATIC_ASSERT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | STATIC ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | STAR ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | SIZEOF ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | SEMI ->
              _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | RETURN ->
              _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | REGISTER ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | PLUS ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | NOT ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | NORETURN ->
              _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | MINUS ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | LPAREN ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | LINT _v_4 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState303
          | INT _v_5 ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState303
          | INLINE ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | INC ->
              _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | IF ->
              _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | ID _v_6 ->
              _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6 MenhirState303
          | GOTO ->
              _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | FOR ->
              _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | FLOAT _v_7 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_7 MenhirState303
          | EXTERN ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | ENUM ->
              _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | DOUBLE _v_8 ->
              _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer _v_8 MenhirState303
          | DO ->
              _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | DEC ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | CONTINUE ->
              _menhir_run_340 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | CONST ->
              _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | BREAK ->
              _menhir_run_342 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | BANG ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | AUTO ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | AND ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | ALIGNAS ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState303
          | LBRACE ->
              let _v_9 = _menhir_action_061 () in
              _menhir_run_361 _menhir_stack _menhir_lexbuf _menhir_lexer _v_9 MenhirState303
          | RBRACE ->
              let _v_10 = _menhir_action_113 () in
              _menhir_run_402 _menhir_stack _menhir_lexbuf _menhir_lexer _v_10 MenhirState303 _tok
          | _ ->
              _eRR ())
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_090 _1 in
          _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_375 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_declarator -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState375 in
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
  
  and _menhir_run_374 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_stack = MenhirCell1_declarator (_menhir_stack, _menhir_s, _v) in
          _menhir_run_375 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_090 _1 in
          _menhir_goto_init_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_286 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let x = _v in
          let _v = _menhir_action_135 x in
          _menhir_goto_option_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | COMMA | SEMI ->
          let _1 = _v in
          let _v = _menhir_action_200 _1 in
          _menhir_goto_struct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_251 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_144 _1 _2 in
      _menhir_goto_parameter_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_246 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_pointer -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_pointer (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_045 _2 in
      _menhir_goto_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_244 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_056 _2 in
          _menhir_goto_direct_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_228 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState228
      | LPAREN ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState228
      | COMMA | RPAREN ->
          let _v = _menhir_action_001 () in
          _menhir_goto_abstract_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | ID _ ->
          let _menhir_stack = MenhirCell1_pointer (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState228 in
          let _v = _menhir_action_060 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_227 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState227 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ID _ ->
          _menhir_reduce_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
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
          let _v = _menhir_action_210 _1 in
          _menhir_goto_type_name _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_162 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_spec -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_spec (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_181 _1 _2 in
      _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_160 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_qual -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_qual (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_182 _1 _2 in
      _menhir_goto_spec_qual_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_329 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_GOTO -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_GOTO (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_102 _2 in
          _menhir_goto_jump_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_294 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_UNION as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_141 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_UNION (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_207 _2 in
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
  
  and _menhir_run_291 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_STRUCT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_141 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_205 _2 in
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
          let _v = _menhir_action_049 _2 in
          _menhir_goto_designator_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_155 : type  ttv_stack. ((ttv_stack, _menhir_box_translation_unit) _menhir_cell1_ENUM as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ALIGNAS | AUTO | COLON | COMMA | CONST | ENUM | EXTERN | ID _ | INLINE | LPAREN | NORETURN | REGISTER | RPAREN | SEMI | STAR | STATIC | STRUCT | TCHAR | TDOUBLE | TFLOAT | TINT | TLONG | TSHORT | TSIGNED | TUNSIGNED | TVOID | TYPEDEF | TYPE_ID _ | UNION | VOLATILE ->
          let MenhirCell1_ENUM (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v = _menhir_action_068 () in
          _menhir_goto_enum_spec _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_141 x in
          _menhir_goto_option_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_145 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_155 _1 _3 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_142 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_postfix_expr -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_postfix_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_154 _1 _3 in
      _menhir_goto_postfix_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_040 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok ->
      let _v = _menhir_action_064 () in
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
          let _ = _menhir_action_062 () in
          _menhir_goto_enum _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_369 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_decl_specs -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let _ = _menhir_action_034 () in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s _tok
  
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
          _menhir_run_369 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
      | LPAREN ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState368
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
          let _v = _menhir_action_060 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_226 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl_specs (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | UNION ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TYPE_ID _v_0 ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState226
      | TYPEDEF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TVOID ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TUNSIGNED ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TSIGNED ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TSHORT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TLONG ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TINT ->
          _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TFLOAT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TDOUBLE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | TCHAR ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | STRUCT ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | STATIC ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | STAR ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | REGISTER ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | NORETURN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | LPAREN ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | INLINE ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | EXTERN ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | ENUM ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | AUTO ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | ALIGNAS ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | ID _ ->
          let _menhir_s = MenhirState226 in
          let _v = _menhir_action_060 () in
          _menhir_goto_enter_declarator _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COMMA | RPAREN ->
          let _v = _menhir_action_130 () in
          _menhir_goto_option_abstract_declarator_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_242 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_043 _1 in
      _menhir_goto_decl_specs _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_191 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_translation_unit) _menhir_state -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_qual (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VOLATILE ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState191
      | CONST ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState191
      | COMMA | ID _ | LPAREN | RPAREN | STAR ->
          let _v_0 = _menhir_action_115 () in
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_192 : type  ttv_stack. (ttv_stack, _menhir_box_translation_unit) _menhir_cell1_type_qual -> _ -> _ -> _ -> _ -> _menhir_box_translation_unit =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_type_qual (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_116 x xs in
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
          let _v = _menhir_action_111 () in
          _menhir_run_297 _menhir_stack _v
      | _ ->
          _eRR ()
  
end

let translation_unit =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_translation_unit v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

# 837 "src/parser.mly"
  
# 13673 "src/parser.ml"
