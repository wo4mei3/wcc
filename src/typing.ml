open Ctype
open Ast

exception TypingError of string

let raise exn =
  match exn with
  (*| TypeError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

let rec declspecs attr is_encountered dsl =
  let is_typedef = ref false
  and is_static = ref false
  and is_extern = ref false
  and is_inline = ref false
  in
  let is_const = ref false
  and is_volatile = ref false
  in
  let pred ds = 
  if attr then
  match ds with
  | Scs ScsTypedef -> is_typedef := true
  | Scs ScsStatic -> is_static := true
  | Scs ScsExtern -> is_extern := true
  | Fs FsInline -> is_inline := true
  | Tq TqConst -> is_const := true
  | Tq TqVolatile -> is_volatile := true
  | _ -> ()
  else
    match ds with
  | Scs ScsTypedef
  | Scs ScsStatic
  | Scs ScsExtern
  | Fs FsInline
  | Tq TqConst
  | Tq TqVolatile -> raise (TypeError ( 
  "storage class specifiers not allowed in this contexts."))
  | _ -> ()
  in
  List.iter pred dsl;
  if (!is_typedef && !is_static || !is_typedef && !is_extern || !is_typedef && !is_inline) then
  raise (TypeError ( 
  "typedef may not be used together with static, extern, inline"))
  else ()
  ;
  let is_char_or_int = ref false
  and is_int = ref false
  and is_int_or_double = ref false
  and is_short = ref false
  and is_long = ref false
  in
  let pred = function 
  | Ts TsVoid -> is_encountered := true
  | Ts TsChar -> is_encountered := true; is_char_or_int := true
  | Ts TsInt -> is_encountered := true; is_char_or_int := true;
                is_int := true;  is_int_or_double := true;
  | Ts TsFloat -> is_encountered := true
  | Ts TsDouble -> is_encountered := true; is_int_or_double := true
  | Ts (TsStruct _)
  | Ts (TsUnion _) -> is_encountered := true
  | Ts (TsTypedef i) -> is_encountered := true;
  begin 
    match get_def_from_ast i with
    | Some  (_,Typedef(decl)) -> 
    begin
      let ty = snd decl in
      let dsl = get_declspecs ty in
      declspecs attr is_encountered dsl
    end
    | _ -> raise (ASTError (spr "typedef not found with id %d" i))
  end
  | _ -> ()
  in
  List.iter pred dsl;
  if !is_short && !is_long then
     raise (TypeError ( 
  "both short and long are appear"))
  else if !is_short then
  begin
    if not !is_int && !is_encountered then
        raise (TypeError ( 
  "short with other than int is not allowed"))
    else ()
  end
  else if !is_long then
  begin
    if not !is_int_or_double && !is_encountered then
        raise (TypeError ( 
  "long with other than int or double is not allowed"))
    else ()
  end


let rec alignof ty =
  if is_typedef ty then
    match get_typedef_from_ast (get_typedef_id ty) with
    | Some decl -> alignof (snd decl)
    | None -> raise (TypingError (spr "alignof error: %s" (show_ty ty)))
  else begin
  match ty with
  | TDeclSpec dsl ->
    if List.mem (Ts TsVoid) dsl then
      raise (TypingError (spr "alignof error: %s" (show_ty ty)))
    else if List.mem (Ts TsChar) dsl || List.mem (Ts TsUChar) dsl then
      1
    else if List.mem (Ts TsShort) dsl || List.mem (Ts TsUShort) dsl then
      2
    else if List.mem (Ts TsInt) dsl || List.mem (Ts TsUInt) dsl || List.mem (Ts TsFloat) dsl then
      4
    else if List.mem (Ts TsLong) dsl || List.mem (Ts TsULong) dsl || List.mem (Ts TsDouble) dsl then
      8
    else if is_struct ty then
      let id = get_struct_id ty in
      let mems = get_struct_members id in
      let aux init decl = 
        let ty = snd decl in
        let align = alignof ty in
        if init < align then
          align
        else
          init
      in
      List.fold_left aux 0 mems
    else if is_union ty then
      let id = get_union_id ty in
      let mems = get_union_members id in
      let aux init decl = 
        let ty = snd decl in
        let align = alignof ty in
        if init < align then
          align
        else
          init
      in
      List.fold_left aux 0 mems
    else raise (TypingError (spr "alignof error: %s" (show_ty ty)))
  | TArr(ty, _) -> alignof ty
  | TPtr _ -> 8
  | TFun _ -> raise (TypingError (spr "alignof error: %s" (show_ty ty)))
  end

and aligned ty n =
  let a = alignof ty in
  (n + a - 1) / a * a

and sizeof ty = 
  if is_typedef ty then
    match get_typedef_from_ast (get_typedef_id ty) with
    | Some decl -> sizeof (snd decl)
    | None -> raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
  else begin
  match ty with
  | TDeclSpec dsl ->
    if List.mem (Ts TsVoid) dsl then
      raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
    else if List.mem (Ts TsChar) dsl || List.mem (Ts TsUChar) dsl then
      1
    else if List.mem (Ts TsShort) dsl || List.mem (Ts TsUShort) dsl then
      2
    else if List.mem (Ts TsInt) dsl || List.mem (Ts TsUInt) dsl || List.mem (Ts TsFloat) dsl then
      4
    else if List.mem (Ts TsLong) dsl || List.mem (Ts TsULong) dsl || List.mem (Ts TsDouble) dsl then
      8
    else if is_struct ty then
      let id = get_struct_id ty in
      let mems = get_struct_members id in
      let aux n decl = 
        let ty = snd decl in
        aligned ty n + sizeof ty
      in
      aligned ty (List.fold_left aux 0 mems)
    else if is_union ty then
      let id = get_union_id ty in
      let mems = get_union_members id in
      let aux init decl = 
        let ty = snd decl in
        let size = sizeof ty in
        if init < size then
          size
        else
          init
      in
      List.fold_left aux 0 mems
    else raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
  | TArr(ty, sz) -> (sizeof ty) * sz
  | TPtr _ -> 8
  | TFun _ -> raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
  end

let rec is_compatible lty rty =
  if is_struct lty  && is_struct rty then
    get_struct_id lty = get_struct_id rty
  else if is_union lty  && is_union rty then
    get_union_id lty = get_union_id rty
  else if is_typedef lty then
    let origin = match get_typedef_from_ast (get_typedef_id lty) with
    | Some decl -> snd decl
    | None -> raise (TypingError (spr "is_compatible error: %s" (show_ty lty)))
    in
    is_compatible origin rty
  else if is_typedef rty then
    let origin = match get_typedef_from_ast (get_typedef_id rty) with
    | Some decl -> snd decl
    | None -> raise (TypingError (spr "is_compatible error: %s" (show_ty rty)))
    in
    is_compatible lty origin
  else if is_numeric lty && is_numeric rty then
    true
  else
    begin
    let map l = List.map (fun x -> snd x) l in
    match (lty, rty) with
    | (TPtr(TFun(lty,ll)),TFun(rty,rl)) 
    | (TFun(lty,ll),TPtr(TFun(rty,rl))) 
    | (TFun(lty,ll),TFun(rty,rl)) -> is_compatible lty rty && List.for_all2 is_compatible (map ll) (map rl)
    | (TPtr lty,TPtr rty)
    | (TPtr lty,TArr(rty,_))
    | (TArr(lty,_),TPtr rty)
    | (TArr(lty,_),TArr(rty,_)) -> is_compatible lty rty
    | _ -> raise (TypingError (spr "is_compatible error: %s and %s is not compatible" (show_ty lty) (show_ty rty)))
    end

let get_common_type lty rty =
    let ty = match (lty, rty) with
    | (TArr(lty,_),_) -> TPtr lty
    | (_,TArr(rty,_)) -> TPtr rty
    | (TFun(_,_),_) -> TPtr lty
    | (_,TFun(_,_)) -> TPtr rty
    | (TPtr _,_) -> lty
    | (_,TPtr _) -> rty
    | (TDeclSpec _,_) when is_numeric lty && sizeof lty = 4 -> TDeclSpec [Ts TsFloat]
    | (_,TDeclSpec _) when is_numeric rty && sizeof rty = 4 -> TDeclSpec [Ts TsFloat]
    | (TDeclSpec _,_) when is_numeric lty && sizeof lty = 8 -> TDeclSpec [Ts TsDouble]
    | (_,TDeclSpec _) when is_numeric rty && sizeof rty = 8 -> TDeclSpec [Ts TsDouble]
    | (TDeclSpec _,_) when is_unsigned lty -> lty
    | (_,TDeclSpec _) when is_unsigned rty -> rty
    | _ -> if sizeof lty < sizeof rty then rty else lty 
    in
    if is_compatible ty lty && is_compatible ty rty then ty
    else raise (TypingError (spr "get_common_type error: %s is not the common type" (show_ty ty)))


let usual_arith_conv lhs rhs =
  let lty = typeof lhs in
  let rty = typeof rhs in
  let ty = get_common_type lty rty in
  (ty,ECast(Some ty,ty,lhs), ECast(Some ty,ty,rhs))


let rec ty_expr expr =
match expr with
| EConst(_,_)
| EVar(_,_) -> expr
| EBinary(_,bin,lhs,rhs) ->
  let (lhs,rhs) = (ty_expr lhs,ty_expr rhs) in
  begin
    match bin with
    | Add | Sub | Mul | Div | Mod
    | BitAnd | BitOr | BitXor ->
    let (ty,lhs,rhs) = usual_arith_conv lhs rhs in
    EBinary(Some ty,bin,lhs,rhs)
    | LShift | RShift ->
    EBinary(Some (typeof lhs),bin,lhs,rhs)
    | LogAnd | LogOr ->
    EBinary(Some (TDeclSpec [Ts TsInt]),bin,lhs,rhs)
    | Lt | Le | Gt | Ge | Eq | Ne ->
    let (_,lhs,rhs) = usual_arith_conv lhs rhs in
    EBinary(Some (TDeclSpec [Ts TsInt]),bin,lhs,rhs)
    | Comma -> EBinary(Some (typeof rhs),bin,lhs,rhs)
  end
| EAssign(_,lhs,rhs) ->
  let (lhs,rhs) = (ty_expr lhs,ty_expr rhs) in
  let ty = typeof lhs in
  begin
  match ty with
  | TArr(_,_) -> raise (TypingError (spr "ty_expr error: array is not a lvalue %s" (show_ty ty)))
  | _ when is_struct ty -> raise (TypingError (spr "ty_expr error: struct cannot be a lvalue %s" (show_ty ty)))
  | _ -> let rhs = ECast(Some ty,ty,rhs) in EAssign(Some ty,lhs,rhs)
  end
| EUnary(_,unary,expr) ->
  let expr = ty_expr expr in
  let ty = typeof expr in
  begin
    match unary with
    | Plus -> EUnary(Some ty,unary,expr)
    | Minus -> let ty = get_common_type (TDeclSpec [Ts TsInt]) ty in ECast(Some ty,ty,expr)
    | BitNot -> EUnary(Some ty,unary,expr)
    | LogNot -> EUnary(Some (TDeclSpec [Ts TsInt]),unary,expr)
    | Ref ->
    begin
    let ty =
    match ty with
    | TArr(ty,_) -> TPtr ty
    | _ -> TPtr ty
    in EUnary(Some ty,unary,expr)
    end
    | Deref ->
    begin
    match ty with
    | TPtr ty when is_void ty -> raise (TypingError (spr "ty_expr error: dereference a void pointer %s" (show_ty ty)))
    | TPtr ty -> EUnary(Some ty,unary,expr)
    | _ -> raise (TypingError (spr "ty_expr error: invalid value dereference %s" (show_ty ty)))
    end
    | Sizeof -> EUnary(Some (TDeclSpec [Ts TsUInt]),unary,expr)
  end
| ETyUnary(_,unary,ty) -> ETyUnary(Some (TDeclSpec [Ts TsUInt]),unary,ty)
| EPostfix(_,expr,postfix) as e-> 
  let expr = ty_expr expr in
  let ty = typeof expr in
  let ret_ty = TDeclSpec (get_declspecs ty) in
  begin
  match postfix with
  | Call l -> 
    let l = List.map ty_expr l in
    let tys = List.map (fun x -> ("",typeof x)) l in
    let ty = get_common_type ty (TFun(ret_ty,tys)) in
    let ret_ty = TDeclSpec (get_declspecs ty) in
    EPostfix(Some ret_ty,expr,Call l)
  | Member name when is_struct ty ->
    let members = get_struct_members (get_struct_id ty) in
    let ty = List.assoc name members in
    EPostfix(Some ty,expr,postfix)
  | _ -> raise (TypingError (spr "ty_expr error: invalid postfix expr %s" (show_expr e)))
  end
| ECond(_,flag,then_,else_) ->
  let (then_,else_) = (ty_expr then_,ty_expr else_) in
  if is_void (typeof then_) || is_void (typeof else_) then
    ECond(Some (TDeclSpec [Ts TsVoid]),flag,then_,else_)
  else
    let (ty,then_,else_) = usual_arith_conv then_ else_ in
    ECond(Some ty,flag,then_,else_)
| ECast(_,ty,expr) -> ECast(Some ty,ty,ty_expr expr)
| ECompoundLit(_,ty,init) -> ECompoundLit(Some ty,ty,ty_init ty init)

and ty_init ty init =
match init with
| IScal expr -> 
  let expr = ty_expr expr in
  let ty = (typeof expr) in
  IScal  (ECast (Some ty,ty, expr))
| IVect l ->
  begin
    let loc = ref 0 in
    match ty with
    | TArr(ty,sz) ->
      let rec aux loc = function
      | [] when !loc < sz -> []
      | (desig_opt,init)::xs -> 
        let x = (desig_opt, ty_init (ty_desig ty desig_opt loc) init) in
        loc := !loc + 1;
        x::aux loc xs
      | _ -> raise (TypingError (spr "ty_init error: excess elements %d" !loc))
      in 
      IVect (aux loc l)
    | ty when is_struct ty ->
      let members = get_struct_members (get_struct_id ty) in
      let rec aux loc mems l =
        match (mems, l) with
        | (_,[]) -> []
        | ([],_) -> raise (TypingError (spr "ty_init error: excess elements %d" !loc))
        | ((_,memty)::_,(desig_opt,init)::xs) -> 
          let elem_ty = match desig_opt with
          | Some _ -> ty_desig ty desig_opt loc
          | None -> memty
          in
          loc := !loc + 1;
          let rec get_remain_members members x =
            match (members, x) with
            | (members,0) -> members
            | ([],x) -> raise (TypingError (spr "ty_init error: excess elements %d" x))
            | (_::members,x) -> get_remain_members members (x - 1)
          in
          (desig_opt, ty_init elem_ty init)::aux loc (get_remain_members members !loc) xs
      in IVect (aux loc members l)
    | _ -> raise (TypingError (spr "ty_init error: invalid ty or init %s, %s" (show_ty ty) (show_init init)))
  end

and ty_desig ty desig_opt loc =
match (ty,desig_opt) with
| (TArr(ty,n),Some (DIdx(i,desig_opt))) when i < n -> loc := i; ty_desig ty desig_opt (ref 0)
| (TArr(_,n),Some (DIdx(i,_))) when i >= n -> raise (TypingError (spr "ty_desig error: invalid index %d" i))
| (ty,Some (DField(name,desig_opt))) when is_struct ty ->
  let members = get_struct_members (get_struct_id ty) in
  let rec aux i = function
  | [] -> raise (TypingError (spr "ty_desig error: no such member %s" name))
  | (n,ty)::_ when n = name -> loc := i; ty
  | _::xs -> aux (i + 1) xs
  in
  ty_desig (aux 0 members) desig_opt (ref 0)
| (_,None) -> ty
| _ -> raise (TypingError (spr "ty_desig error: invalid desig %s" (show_desig_opt desig_opt))) 

and ty_stmt stmt =
match stmt with
| SDef def -> SDef def
| SStmts stmts -> SStmts (List.map ty_stmt stmts)
| SWhile(expr,stmt,s1,s2) -> SWhile(ty_expr expr,ty_stmt stmt,s1,s2)
| SDoWhile(stmt,expr,s1,s2) -> SDoWhile(ty_stmt stmt,ty_expr expr,s1,s2)
| SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,stmt,s1,s2) ->
  let def_opt = match def_opt with
  | Some def -> Some (def)
  | None -> None in
  let expr_opt1 = match expr_opt1 with
  | Some expr -> Some (ty_expr expr)
  | None -> None in
  let expr_opt2 = match expr_opt2 with
  | Some expr -> Some (ty_expr expr)
  | None -> None in
  let expr_opt3 = match expr_opt3 with
  | Some expr -> Some (ty_expr expr)
  | None -> None in
  SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,ty_stmt stmt,s1,s2)
| SIfElse(expr,stmt1,stmt2) -> SIfElse(ty_expr expr,ty_stmt stmt1,ty_stmt stmt2)
| SReturn expr_opt ->
  let expr_opt = match expr_opt with
  | Some expr -> Some (ty_expr expr)
  | None -> None in
  SReturn expr_opt
| SLabel(s,stmt) -> SLabel(s,ty_stmt stmt)
| SGoto s -> SGoto s
| SSwitch(expr,stmts,s) -> SSwitch(ty_expr expr,List.map ty_stmt stmts,s)
| SCase(expr,stmts) -> SCase(ty_expr expr,List.map ty_stmt stmts)
| SDefault stmts -> SDefault(List.map ty_stmt stmts)
| SExpr expr -> SExpr(ty_expr expr)