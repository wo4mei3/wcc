%{
    open Ast 
    open Env 
    open Ctype
    open Middle
    open Typing
    open Parser_helper

    type declarator =
    | DeclPtr of declarator
    | DeclIdent of string
    | DeclArr of declarator * int
    | DeclFun of declarator * decl list

    let make_decl ty d = 
      let name = ref "" in
      let rec aux ty = function
      | DeclPtr d -> aux (TPtr ty) d 
      | DeclIdent n -> name := n; ty 
      | DeclArr(d,sz) -> aux (TArr(ty,sz)) d 
      | DeclFun(d,dl) -> aux (TFun(ty,dl)) d
      in (!name, aux ty d, None)

    let make_decls ty dl =
      List.map (fun d -> make_decl ty d) dl

    let make_decls_with_init_opts ty d_with_init_opt_l =
      List.map (fun (d,init_opt) -> (make_decl ty d,init_opt)) d_with_init_opt_l

    let item_id = ref 0

    let gen_id () =
      item_id := !item_id + 1;
      !item_id

    let unsigned_flag = ref false

    let get_declspecs = function
    | Some (TDeclSpec x) when !unsigned_flag  ->
      TDeclSpec ( 
        List.map (
        function
        | Ts TsChar -> Ts TsUChar
        | Ts TsInt -> Ts TsUInt
        | Ts TsShort -> Ts TsUShort
        | Ts TsLong -> Ts TsULong
        | _ as ds -> ds
      ) x )
    | Some ty -> ty
    | None when !unsigned_flag -> TDeclSpec ([Ts TsUInt])
    | None -> TDeclSpec ([Ts TsInt])


    let append_ds_list a b =
      let pred a b c = 
      match (a,b,c) with
      | (None,None,None) -> None
      | (Some (TDeclSpec x),None,None) -> Some (TDeclSpec(x))
      | (None,Some (TDeclSpec y),None) -> Some (TDeclSpec(y))
      | (None,None,Some (TDeclSpec z)) -> Some (TDeclSpec(z))
      | (Some (TDeclSpec x),Some (TDeclSpec y),None) -> Some (TDeclSpec(x@y))
      | (Some (TDeclSpec x),None,Some (TDeclSpec z)) -> Some (TDeclSpec(x@z))
      | (None,Some (TDeclSpec y),Some (TDeclSpec z)) -> Some (TDeclSpec(y@z))
      | (Some (TDeclSpec x),Some (TDeclSpec y),Some (TDeclSpec z)) -> Some (TDeclSpec(x@y@z))
      | _ -> raise (ParserError "decl_spec")
      in
      List.fold_left2 pred None a b

    let check_member_redifinition decls =
      let rec aux l = function
      | [] -> false
      | (name,_,_) as x::xs -> mem_assoc name (l@xs) || aux (x::l) xs
      in
      if aux [] decls then raise (ParserError "member redefiniton")

    type is_incomplete =
    | Complete
    | Incomplete 
    | DontCare 

    let struct_pred name =function
    | (_,Struct(n,_)) when n = name ->
      true
    | _ -> false

    let lookup_struct_definition name scope =
      try 
        let (id,item) = List.find (struct_pred name) scope 
        in
        match item with
        | Struct(_,Some _) -> (Some id,Complete)
        | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)

    let lookup_struct_in_scope name =
      try 
        let (id,item) = List.find (struct_pred name) !curr_scope 
        in
        match item with
        | Struct(_,Some _) -> (Some id,Complete)
        | Struct(_,None) ->
        begin
        match lookup_struct_definition name !curr_scope with
        | (Some id,Complete) -> (Some id,Complete)
        | _ -> (Some id,Incomplete)
        end
        | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)

    let lookup_struct_in_stack name =
      let rec aux stack =
      match stack with
      | hd::tl ->
      begin
        try 
          let (id,item) = List.find (struct_pred name) hd
        in
        match item with
        | Struct(_,Some _) -> (Some id,Complete)
        | Struct(_,None) -> 
        begin
          match lookup_struct_definition name hd with
          | (Some id,Complete) -> (Some id,Complete)
          | _ -> 
          begin 
          match aux tl with
          | (Some id,Complete) -> (Some id,Complete)
          | _ -> (Some id,Incomplete)
          end
        end
        | _ -> (None,DontCare)
        with Not_found ->
          aux tl
      end
      | [] -> (None,DontCare)
      in aux !stack

    let make_struct name_opt dl =
      let name = ref "" in
      let (def_opt,id,status) =
      match name_opt with
      | Some n -> 
        begin
          name := n;
          match lookup_struct_in_scope n with
          | (Some id,Complete) -> 
            begin
              match dl with
              | Some _ -> raise (ParserError (Printf.sprintf "redifinition of %s \n" !name))
              | None -> (None,id,Complete)
            end
          | (Some id,Incomplete) ->
            begin
              match dl with
              | Some decls -> check_member_redifinition decls; (Some (id,Struct(!name,dl)),id,Complete)
              | None -> (None,id,Incomplete)
            end
          | _ -> 
            begin
              match lookup_struct_in_stack n with
              | (Some id,Complete) -> 
                begin
                  match dl with
                  | Some decls -> check_member_redifinition decls; check_member_redifinition decls; (Some (id,Struct(!name,dl)),id,Complete)
                  | None -> (None,id,Complete)
                end
              | (Some id,Incomplete) ->
                begin
                  match dl with
                  | Some decls -> check_member_redifinition decls; (Some (id,Struct(!name,dl)),id,Complete)
                  | None -> (None,id,Incomplete)
                end
              | _ -> 
                let id = gen_id () in
                match dl with
                | Some decls -> check_member_redifinition decls; (Some (id,Struct(!name,dl)),id,Complete)
                | None -> (Some (id,Struct(!name,dl)),id,Incomplete)
            end
        end 
      | None -> let id = gen_id () in
                match dl with 
                | Some decls -> check_member_redifinition decls; 
                  (Some (id,Struct(!name,dl)),id,Complete)
                | None ->
                  raise (ParserError "anonymous struct with no definition.")
      in
      (def_opt, TsStruct id,status)

    let union_pred name =function
    | (_,Union(n,_)) when n = name ->
      true
    | _ -> false

    let lookup_union_definition name scope =
      try 
        let (id,item) = List.find (union_pred name) scope 
        in
        match item with
        | Union(_,Some _) -> (Some id,Complete)
        | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)

    let lookup_union_in_scope name=
      try 
        let (id,item) = List.find (union_pred name) !curr_scope 
      in
      match item with
      | Union(_,Some _) -> (Some id,Complete)
      | Union(_,None) -> 
        begin
        match lookup_union_definition name !curr_scope with
        | (Some id,Complete) -> (Some id,Complete)
        | _ -> (Some id,Incomplete)
        end
      | _ -> (None,DontCare)
      with Not_found ->
        (None,DontCare)


    let lookup_union_in_stack name =
      let rec aux stack =
      match stack with
      | hd::tl ->
      begin
        try 
          let (id,item) = List.find (union_pred name) hd
        in
        match item with
        | Union(_,Some _) -> (Some id,Complete)
        | Union(_,None) ->       
        begin
          match lookup_union_definition name hd with
          | (Some id,Complete) -> (Some id,Complete)
          | _ -> 
          begin 
          match aux tl with
          | (Some id,Complete) -> (Some id,Complete)
          | _ -> (Some id,Incomplete)
          end
        end
        | _ -> (None,DontCare)
        with Not_found ->
          aux tl
      end
      | [] -> (None,DontCare)
      in aux !stack

    let make_union name_opt dl =
      let name = ref "" in
      let (def_opt,id,status) =
      match name_opt with
      | Some n -> 
        begin
          name := n;
          match lookup_union_in_scope n with
          | (Some id,Complete) -> 
            begin
              match dl with
              | Some decls -> check_member_redifinition decls; raise (ParserError (Printf.sprintf "redifinition of %s \n" !name))
              | None -> (None,id,Complete)
            end
          | (Some id,Incomplete) ->
            begin
              match dl with
              | Some decls -> check_member_redifinition decls; (Some (id,Union(!name,dl)),id,Complete)
              | None -> (None,id,Incomplete)
            end
          | _ -> 
            begin
              match lookup_union_in_stack n with
              | (Some id,Complete) -> 
                begin
                  match dl with
                  | Some decls -> check_member_redifinition decls; (Some (id,Union(!name,dl)),id,Complete)
                  | None -> (None,id,Complete)
                end
              | (Some id,Incomplete) ->
                begin
                  match dl with
                  | Some decls -> check_member_redifinition decls; (Some (id,Union(!name,dl)),id,Complete)
                  | None -> (None,id,Incomplete)
                end
              | _ -> 
                let id = gen_id () in
                match dl with
                | Some decls -> check_member_redifinition decls; (Some (id,Union(!name,dl)),id,Complete)
                | None -> (Some (id,Union(!name,dl)),id,Incomplete)
            end
        end 
      | None -> let id = gen_id () in
                match dl with 
                | Some decls -> check_member_redifinition decls; 
                  (Some (id,Union(!name,dl)),id,Complete)
                | None ->
                  raise (ParserError "anonymous union with no definition.")
      in
      (def_opt, TsUnion id,status)

    let lookup_var_in_scope name =
      let aux = function
      | (_,Var((n,_,_),_)) when n = name -> true
      | _ -> false
      in
      List.exists aux !curr_scope  

    let lookup_typedef_in_scope name =
      let aux = function
      | (_,Typedef(n,_,_)) when n = name -> true
      | _ -> false
      in
      List.exists aux !curr_scope 


    let rec is_typedef_definition ty =
      match ty with
      | TFun(t,_) -> is_typedef_definition t 
      | TPtr t -> is_typedef_definition t 
      | TArr(t,_) -> is_typedef_definition t 
      | TDeclSpec dsl -> List.mem (Scs ScsTypedef) dsl
    
    let make_typedef (name, ty,offset) =
      if not (lookup_var_in_scope name || lookup_typedef_in_scope name) then
        (gen_id (),Typedef (name,ty,offset))
      else 
        raise (ParserError "redifinition")

    let make_var (name,ty,offset) init_opt =
      if lookup_var_in_scope name then
        raise (ParserError "redifinition")
      else
        (gen_id (), Var((name,ty,offset),init_opt))

    let make_var_or_typedef ((name,ty,offset),init_opt) =
      if is_typedef_definition ty then
        begin
          match init_opt with
          | Some _ -> raise (ParserError "typedef has init")
          | None -> make_typedef (name,ty,offset)
        end
      else
        make_var (name,ty,offset) init_opt

    let def_buf:def list ref = ref []

    let flush_stack () = 
      def_buf := [] 

    let get_def_buf () =
      let ret = List.rev !def_buf in
      flush_stack ();
      ret

    let curr_params = ref []

    let params_stack = ref []
    
    let enter_params () =
      params_stack := !curr_params::!params_stack;
      curr_params := []

    let leave_params () =
      curr_params := List.hd !params_stack;
      params_stack := List.tl !params_stack

    let is_in_params () =
      match !curr_params with
      | [] -> false
      | _ -> true

    let add_def2 def =
      curr_params := def::!curr_params
    
    let add_def def =
      if is_in_params () then
        add_def2 def
      else
        begin
          push_def def;
          def_buf := def::!def_buf
        end


    let get_params_buf () =
      List.rev !curr_params

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


%}

%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE DOT COMMA
%token AND STAR PLUS MINUS NOT BANG DIV MOD LT GT HAT OR 
%token COLON QUESTION SEMI EQ INLINE NORETURN ALIGNAS
%token SIZEOF EOF STATIC_ASSERT
%token ARROW INC DEC LSHIFT RSHIFT LE GE EQEQ NE ELLIPSIS
%token ANDAND OROR MUL_EQ DIV_EQ MOD_EQ ADD_EQ
%token SUB_EQ LSHIFT_EQ RSHIFT_EQ AND_EQ
%token XOR_EQ OR_EQ
%token TYPEDEF EXTERN STATIC AUTO REGISTER
%token TCHAR TSHORT TINT TLONG TSIGNED TUNSIGNED TFLOAT TDOUBLE CONST VOLATILE TVOID
%token STRUCT UNION ENUM 
%token CASE DEFAULT IF ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN

%token <int> CHAR INT UINT LINT ULINT
%token <float> FLOAT DOUBLE
%token<int list> STR
%token<string> ID TYPE_ID

%nonassoc NO_ELSE
%nonassoc  ELSE 

%type<program> translation_unit
%start translation_unit


%%

translation_unit:
| list(external_decl) EOF
  { Program (List.flatten $1) }

ident:
| ID { $1 }
| TYPE_ID { $1 }


primary_expr:
| ID { EVar (None, get_var $1) }
| CHAR { EConst (Some (TDeclSpec[(Ts TsChar)]), VInt $1) }
| INT { EConst (Some (TDeclSpec[(Ts TsInt)]), VInt $1) }
| UINT { EConst(Some (TDeclSpec[(Ts TsUInt)]), VInt $1) }
| LINT { EConst(Some (TDeclSpec[(Ts TsLong)]), VInt $1) }
| ULINT { EConst(Some (TDeclSpec[(Ts TsULong)]), VInt $1) }
| FLOAT { EConst (Some (TDeclSpec[(Ts TsFloat)]), VFloat $1) }
| DOUBLE { EConst(Some (TDeclSpec[(Ts TsDouble)]), VFloat $1) }
| STR { EConst (Some (TArr(TDeclSpec[(Ts TsChar)],List.length $1)), VStr $1) }
| LPAREN expr RPAREN
   { $2 }

postfix_expr:
| primary_expr { $1 }
| postfix_expr LBRACKET expr RBRACKET { EUnary(None, Deref, EBinary(None, Add,$1,$3)) }
| postfix_expr LPAREN argument_expr_list? RPAREN
  { 
    match $3 with
    | Some l -> EPostfix(None, $1,Call l)
    | None -> EPostfix(None, $1,Call [])
  }
| postfix_expr DOT ident { EPostfix(None, $1,Member $3) }
| postfix_expr ARROW ident { EPostfix(None, EUnary(None, Deref,$1),Member $3) }
| postfix_expr INC 
  { 
  EBinary(None, Sub,
  EAssign(None, $1,EBinary(None, Add,$1,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1)))
  ,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1)) 
  }
| postfix_expr DEC
  { 
  EBinary(None, Add,
  EAssign(None, $1,EBinary(None, Sub,$1,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1)))
  ,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1)) 
  }
| LPAREN type_name RPAREN LBRACE init_list COMMA? RBRACE { ECompoundLit(None, $2,IVect $5) }

argument_expr_list:
| assignment_expr { [$1] }
| argument_expr_list COMMA assignment_expr { $1@[$3] }

unary_expr:
| postfix_expr { $1 }
| INC unary_expr { EAssign(None, $2,EBinary(None, Add,$2,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1)))  }
| DEC unary_expr { EAssign(None, $2,EBinary(None, Sub,$2,EConst (Some (TDeclSpec[(Ts TsInt)]), VInt 1))) }
| AND cast_expr  { EUnary(None, Ref, $2) }
| STAR cast_expr { EUnary(None, Deref, $2) }
| PLUS cast_expr { EUnary(None, Plus, $2) }
| MINUS cast_expr { EUnary(None, Minus, $2) }
| NOT cast_expr { EUnary(None, BitNot, $2) }
| BANG cast_expr { EUnary(None, LogNot, $2) }
| SIZEOF unary_expr { EUnary(None, Sizeof, $2) }
| SIZEOF LPAREN type_name RPAREN { ETyUnary(None, Sizeof,$3) }


cast_expr:
| unary_expr { $1 }
| LPAREN type_name RPAREN cast_expr { ECast(None, $2,$4) }

multiplicative_expr:
| cast_expr { $1 }
| multiplicative_expr STAR cast_expr { EBinary(None, Mul,$1,$3) }
| multiplicative_expr DIV cast_expr { EBinary(None, Div,$1,$3) }
| multiplicative_expr MOD cast_expr { EBinary(None, Mod,$1,$3) }

additive_expr:
| multiplicative_expr { $1 }
| additive_expr PLUS multiplicative_expr { EBinary(None, Add,$1,$3) }
| additive_expr MINUS multiplicative_expr { EBinary(None, Sub,$1,$3) }

shift_expr:
| additive_expr { $1 }
| shift_expr LSHIFT additive_expr { EBinary(None, LShift,$1,$3) }
| shift_expr RSHIFT additive_expr { EBinary(None, RShift,$1,$3) }

relational_expr:
| shift_expr { $1 }
| relational_expr LT shift_expr { EBinary(None, Lt,$1,$3) }
| relational_expr GT shift_expr { EBinary(None, Gt,$1,$3) }
| relational_expr LE shift_expr { EBinary(None, Le,$1,$3) }
| relational_expr GE shift_expr { EBinary(None, Ge,$1,$3) }

equality_expr:
| relational_expr { $1 }
| equality_expr EQEQ relational_expr { EBinary(None, Eq,$1,$3) }
| equality_expr NE relational_expr { EBinary(None, Ne,$1,$3) }

and_expr:
| equality_expr { $1 }
| and_expr AND equality_expr { EBinary(None, BitAnd,$1,$3) }

exclusive_or_expr:
| and_expr { $1 }
| exclusive_or_expr HAT and_expr { EBinary(None, BitXor,$1,$3) }

inclusive_or_expr:
| exclusive_or_expr { $1 }
| inclusive_or_expr OR exclusive_or_expr { EBinary(None, BitOr,$1,$3) }

logical_and_expr:
| inclusive_or_expr { $1 }
| logical_and_expr ANDAND inclusive_or_expr { EBinary(None, LogAnd,$1,$3) }

logical_or_expr:
| logical_and_expr { $1 }
| logical_or_expr OROR logical_and_expr { EBinary(None, LogOr,$1,$3) }

conditional_expr:
| logical_or_expr { $1 }
| logical_or_expr QUESTION expr COLON conditional_expr { ECond(None, $1,$3,$5) }

assignment_expr:
| conditional_expr { $1 }
| unary_expr EQ assignment_expr { EAssign(None, $1,$3) }
| unary_expr MUL_EQ assignment_expr { EAssign(None, $1,EBinary(None, Mul,$1,$3)) }
| unary_expr DIV_EQ assignment_expr { EAssign(None, $1,EBinary(None, Div,$1,$3)) }
| unary_expr MOD_EQ assignment_expr { EAssign(None, $1,EBinary(None, Mod,$1,$3)) }
| unary_expr ADD_EQ assignment_expr { EAssign(None, $1,EBinary(None, Add,$1,$3)) }
| unary_expr SUB_EQ assignment_expr { EAssign(None, $1,EBinary(None, Sub,$1,$3)) }
| unary_expr LSHIFT_EQ assignment_expr { EAssign(None, $1,EBinary(None, LShift,$1,$3)) }
| unary_expr RSHIFT_EQ assignment_expr { EAssign(None, $1,EBinary(None, RShift,$1,$3)) }
| unary_expr AND_EQ assignment_expr { EAssign(None, $1,EBinary(None, BitAnd,$1,$3)) }
| unary_expr XOR_EQ assignment_expr { EAssign(None, $1,EBinary(None, BitXor,$1,$3)) }
| unary_expr OR_EQ assignment_expr { EAssign(None, $1,EBinary(None, BitOr,$1,$3)) }

expr:
| assignment_expr { $1 }
| expr COMMA assignment_expr { EBinary(None, Comma,$1,$3) }

constant_expr:
| conditional_expr
  { eval (ty_expr $1) } 


decl:
| decl_specs SEMI { () }
| decl_specs init_declarator_list SEMI 
  { 
    let defs = List.map make_var_or_typedef (make_decls_with_init_opts $1 $2) in
    List.iter add_def defs
  }
| static_assert_decl  { raise (NotImpl "Static_assert") }

decl_spec:
| storage_class_spec { Some (TDeclSpec [Scs $1]) }
| type_qual { Some (TDeclSpec [Tq $1]) }
| function_spec { Some (TDeclSpec [Fs $1]) }
| alignment_spec { raise (NotImpl "not implemented") }
| type_spec 
  { 
    match $1 with
    | Some ts -> Some (TDeclSpec [Ts ts])
    | None -> None
  }

decl_specs:
| decl_specs_sub
  {
    let ret = get_declspecs $1 in
    unsigned_flag := false;
    ret
  }

decl_specs_sub:
| decl_spec { $1 }
| decl_specs_sub decl_spec
  { append_ds_list [$1] [$2] }

init_declarator_list:
| init_declarator
  { [$1] }
| init_declarator_list COMMA init_declarator
  { $1@[$3] }

init_declarator:
| declarator { ($1,None) }
| declarator EQ init
  { ($1,Some $3) }

storage_class_spec:
| TYPEDEF { ScsTypedef }
| EXTERN { ScsExtern }
| STATIC { ScsStatic }
| AUTO { ScsAuto }
| REGISTER { ScsRegister }

type_spec:
| TVOID { Some TsVoid }
| TCHAR { Some TsChar }
| TSHORT { Some TsShort}
| TINT { Some TsInt }
| TLONG { Some TsLong }
| TFLOAT { Some TsFloat }
| TDOUBLE { Some TsDouble }
| TSIGNED { None }
| TUNSIGNED { unsigned_flag := true ; None }
| struct_or_union_spec { 
  match $1 with
  | (Some def,ts,_) -> add_def def;Some ts
  | (_,ts,_) ->Some ts
  }
| enum_spec { Some $1 }
| TYPE_ID { Some (TsTypedef (get_typedef $1)) }

spec_qual_list:
| spec_qual_list_sub
  {
    let ret =
    match $1 with
    | [] when !unsigned_flag -> [Ts TsUInt]
    | [] -> [Ts TsInt]
    | _ ->
    begin
      if !unsigned_flag then
        List.map (
          function
          | Ts TsChar -> Ts TsUChar
          | Ts TsInt -> Ts TsUInt
          | Ts TsShort -> Ts TsUShort
          | Ts TsLong -> Ts TsULong
          | _ as ds -> ds
        ) $1
      else 
        $1
    end
    in 
    unsigned_flag := false;
    ret
  }

spec_qual_list_sub:
| type_spec
  {
    match $1 with
    | Some ts -> [Ts ts]
    | None -> [] 
  }
| type_spec spec_qual_list_sub
  { 
    match $1 with
    | Some ts -> (Ts ts)::$2
    | None -> $2
  }
| type_qual spec_qual_list_sub { (Tq $1)::$2 }

type_qual:
| CONST { TqConst }
| VOLATILE { TqVolatile }

function_spec:
| INLINE { FsInline }
| NORETURN { FsNoreturn }

alignment_spec:
| ALIGNAS LPAREN type_name RPAREN
| ALIGNAS LPAREN constant_expr RPAREN
  { raise (NotImpl "ALIGNAS") }

struct_or_union_spec:
| STRUCT ident? LBRACE list(struct_decl) RBRACE { make_struct $2 (Some (List.flatten $4)) }
| STRUCT ident { make_struct (Some $2) None } 
| UNION ident? LBRACE list(struct_decl) RBRACE { make_union $2 (Some (List.flatten $4)) }
| UNION ident { make_union (Some $2) None }

struct_decl:
| spec_qual_list struct_declarator_list? SEMI
  {
    match $2 with
    | Some dl -> make_decls (TDeclSpec $1) dl
    | None -> raise (NotImpl "struct_decl")
  }
| static_assert_decl
  { raise (NotImpl "Static_assert") }

struct_declarator_list:
| struct_declarator { [$1] }
| struct_declarator_list COMMA struct_declarator { $1@[$3] }

struct_declarator:
| declarator { $1 }
| declarator? COLON constant_expr
  { raise (NotImpl "Bitfield") }

enum_spec:
| ENUM ident? LBRACE enum_list COMMA? RBRACE
| ENUM ident
    { raise (NotImpl "enum_spec") }

enum_list:
| enum
| enum_list COMMA enum
    {}

enum:
| enum_const
| enum_const EQ constant_expr
    {  }

enum_const:
| ident
    {  }

declarator:
| pointer declarator { DeclPtr $2 }
| direct_declarator { $1 }


enter_declarator:
|
  {
    in_declarator := true
  }

leave_declarator:
|
  {
    in_declarator := false
  }

direct_declarator:
| enter_declarator ID leave_declarator { DeclIdent $2 }
| LPAREN declarator RPAREN { $2 }

| direct_declarator LBRACKET constant_expr RBRACKET { DeclArr($1, $3) }
| direct_declarator lp parameter_type_list rp { DeclFun($1,$3) }

pointer:
| STAR list(type_qual)
  {  }

lp:
| LPAREN 
  { enter_params () }

rp:
| RPAREN
  { leave_params () }

parameter_type_list:
| 
  { [] }
| parameter_list option(COMMA ELLIPSIS {})
  { $1 }

parameter_list:
| parameter_decl
  { $1 }
| parameter_list COMMA parameter_decl
  { $1@$3 }

parameter_decl:
| decl_specs declarator
  { 
    [make_decl $1 $2]
  }
| decl_specs abstract_declarator?
  {
    match $2 with
    | Some d -> [make_decl $1 d]
    | None -> [make_decl $1 (DeclIdent "")]
  }

abstract_declarator:
| pointer { DeclPtr(DeclIdent "") }
| pointer abstract_declarator { DeclPtr $2 }
| direct_abstract_declarator { $1 }

direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN { $2 }
| LBRACKET constant_expr RBRACKET { DeclArr(DeclIdent "",$2) }
| lp parameter_type_list rp { DeclFun(DeclIdent "",$2) }
| direct_abstract_declarator LBRACKET constant_expr RBRACKET { DeclArr($1,$3) }
| direct_abstract_declarator lp parameter_type_list rp { DeclFun($1,$3) }



type_name:
| spec_qual_list { TDeclSpec $1 }
| spec_qual_list abstract_declarator
  { snd_ (make_decl (TDeclSpec $1) $2) }

init:
| assignment_expr { IScal $1 }
| LBRACE init_list COMMA? RBRACE { IVect $2 }

init_list:
| desig? init { [($1,$2)] }
| init_list COMMA desig? init { $1@[($3,$4)] }

desig:
| designator_list  EQ
  { $1 }

designator_list:
| LBRACKET constant_expr RBRACKET { DIdx($2,None) }
| DOT ident { DField($2,None) }
| LBRACKET constant_expr RBRACKET designator_list {DIdx($2,Some $4) } 
| DOT ident designator_list { DField($2,Some $3) }

static_assert_decl:
| STATIC_ASSERT LPAREN constant_expr COMMA STR RPAREN SEMI
  { raise (NotImpl "_Static_assert") }

enter_scope:
  {
    enter_scope ()
  }

leave_scope:
  {
    leave_scope ()
  }

item:
| decl { List.map (fun def -> SDef def) (get_def_buf ()) }
(*
| decl 
  { 
    List.map (fun def -> SDef def) (!curr_scope)
  }
*)
| stmt { [$1] }

stmt:
| labeled_stmt { $1 }
| compound_stmt { $1 }
| expr_stmt { expr_conv $1 }
| selection_stmt_1 { $1 }
| selection_stmt_2 end_ { $1 }
| iteration_stmt end_ { $1 }
| jump_stmt { $1 }

labeled_stmt:
| ident COLON item
  { 
    push_label $1;
    SLabel($1,SStmts $3)
  }

case_or_default:
| CASE conditional_expr COLON list(item) { SCase ($2,List.flatten $4) }
| DEFAULT COLON list(item) { SDefault (List.flatten $3) }


compound_stmt:
| enter_scope LBRACE list(item) RBRACE leave_scope
  {
    SStmts(List.flatten $3)
  }

expr_stmt:
| SEMI { None }
| expr SEMI { Some $1 }

selection_stmt_1:
| IF LPAREN expr RPAREN stmt    %prec NO_ELSE { SIfElse($3,$5,SStmts []) }
| IF LPAREN expr RPAREN stmt ELSE stmt { SIfElse($3,$5,$7) }

selection_stmt_2:
| SWITCH LPAREN expr RPAREN begin_ LBRACE list(case_or_default) RBRACE
  { 
    let ret = SSwitch($3,$7,!curr_brk) in
    ret
  }

decl_for_for_stmt:
| decl
  { peek_curr_scope () }

stmt_for_for_stmt:
| labeled_stmt leave_scope { $1 }
| LBRACE list(item) RBRACE leave_scope
  {
    SStmts(List.flatten $2)
  }
| expr_stmt leave_scope { expr_conv $1 }
| selection_stmt_1 leave_scope { $1 }
| selection_stmt_2 end_ leave_scope { $1 }
| iteration_stmt end_ leave_scope { $1 }
| jump_stmt leave_scope { $1 }

iteration_stmt:
| WHILE LPAREN expr RPAREN begin_ stmt
  { 
    SWhile($3,$6,!curr_brk,!curr_cont)
  }
| DO begin_ stmt WHILE LPAREN expr RPAREN
  { 
    SDoWhile($3,$6,!curr_brk,!curr_cont)
  }
| FOR LPAREN expr_stmt expr_stmt expr? RPAREN begin_ stmt
  { 
    SFor(None,$3,$4,$5,$8,!curr_brk,!curr_cont)
  }

| FOR LPAREN enter_scope decl_for_for_stmt expr_stmt expr? RPAREN begin_ stmt_for_for_stmt
  { 
    let ret = SFor(Some $4, None,$5,$6,$9,!curr_brk,!curr_cont) in
    ret
  }

begin_:
|  
  {
    brk := !curr_brk;
    cont := !curr_cont;
    curr_brk := gen_new_label ();
    curr_cont := gen_new_label ();
  }

end_:
| 
  {
    curr_brk := !brk;
    curr_cont := !cont;
  }

jump_stmt:
| GOTO ident SEMI
  { 
    push_goto $2;
    SGoto $2
  }
| CONTINUE SEMI { SGoto !curr_cont }
| BREAK SEMI { SGoto !curr_brk }
| RETURN expr_stmt { SReturn $2 }

external_decl:
| function_def
  { get_def_buf () }
| decl
  { get_def_buf () }

function_decl:
| decl_specs declarator
  {
    make_decl $1 $2
  }

top_compound_stmt:
| enter_scope LBRACE list(item) RBRACE leave_scope
  {
    all_labels_exist ();
    SStmts(List.flatten $3)
  }

function_def:
| function_decl top_compound_stmt
  {
    let decl = $1 in
    let def2_list = get_params_buf () in
    let def_list =
    [(gen_id (),Function(def2_list,decl,Some $2,None))] in
    List.iter add_def def_list
  }
%%
