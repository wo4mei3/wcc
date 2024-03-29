open Ctype
open Ast
open Typing

exception MiddleError of string

let gp_max = 6
let fp_max = 8

let raise exn =
  match exn with
  (*| MiddleError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

let uint_of_int i =
  if i < 0 then
    Int64.sub (Int64.of_int i) (Int64.shift_left 1L 62) |> Int64.to_int
  else 
    i

let bool_of_int x =
  if x = 0 then
    false
  else
    true

let bool_to_int b =
  if b then
    1
  else
    0

let rec eval_expr expr name_ref =
  let ty = typeof expr in
  if is_flonum ty then
    VFloat(eval_double expr)
  else
    VInt(eval2 expr name_ref)

and eval expr =
  eval2 expr (ref "")

and eval2 expr name_ref =
  let ty = typeof expr in
  if is_flonum ty then
    int_of_float(eval_double expr)
  else
    match expr with
    | EConst(_,v) ->
      begin match v with
      | VInt i -> i
      | _ -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))
      end
    | EVar(_,i) ->
      begin match get_var_from_ast i with
      | Some decl -> 
        name_ref := fst_ decl
      | _ -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))
      end;
      0
    | EBinary(_,bin,lhs,rhs) ->
      begin match bin with
      | Add -> (eval2 lhs name_ref) + (eval rhs)
      | Sub -> (eval2 lhs name_ref) - (eval rhs)
      | Mul -> (eval lhs) * (eval rhs)
      | Div -> 
        if is_unsigned ty then
          (uint_of_int (eval lhs)) / (uint_of_int (eval rhs))
        else
          (eval lhs) / (eval rhs)
      | Mod -> 
        if is_unsigned ty then
          (uint_of_int (eval lhs)) mod (uint_of_int (eval rhs))
        else
          (eval lhs) mod (eval rhs)
      | LShift -> (eval lhs) lsl (eval rhs)
      | RShift ->
        if is_unsigned ty then
          (uint_of_int (eval lhs)) lsr (eval rhs)
        else
          (eval lhs) asr (eval rhs)
      | BitAnd -> (eval lhs) land (eval rhs)
      | BitXor -> (eval lhs) lxor (eval rhs)
      | BitOr -> (eval lhs) lor (eval rhs)
      | LogAnd -> ((bool_of_int (eval lhs)) && (bool_of_int (eval rhs))) |> bool_to_int
      | LogOr -> ((bool_of_int (eval lhs)) || (bool_of_int (eval rhs))) |> bool_to_int
      | Lt -> ((eval lhs) < (eval rhs)) |> bool_to_int
      | Le -> ((eval lhs) <= (eval rhs)) |> bool_to_int
      | Gt -> ((eval lhs) > (eval rhs)) |> bool_to_int
      | Ge -> ((eval lhs) >= (eval rhs)) |> bool_to_int
      | Eq -> ((eval lhs) = (eval rhs)) |> bool_to_int
      | Ne -> ((eval lhs) <> (eval rhs)) |> bool_to_int
      | Comma -> eval rhs
      end
    | EUnary(_,un,expr) ->
      begin match un with
      | Plus -> eval expr
      | Minus -> -(eval expr)
      | BitNot -> lnot (eval expr)
      | LogNot -> (not (bool_of_int (eval expr))) |> bool_to_int
      | Ref -> eval_rval expr name_ref
      | _ -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))
      end
    | EPostfix(_,expr,Member(name)) when is_struct ty ->
      let decls = get_struct_id ty |> get_struct_members in
      let offset = match assoc3 name decls with
      | Some offset -> offset
      | None -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))
      in 
      (eval_rval expr name_ref) + offset
    | ECond(_,flag,lhs,rhs) ->
      if bool_of_int (eval flag) then
        eval lhs
      else 
        eval rhs
    | ECast(_,_,expr) ->
      if is_unsigned ty then
        uint_of_int (eval2 expr name_ref)
      else
        eval2 expr name_ref
    | _ -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))

and eval_rval expr name_ref =
  let ty = typeof expr in
  match expr with
  | EVar(_,i) ->
      begin match get_var_from_ast i with
      | Some decl -> 
        name_ref := fst_ decl
      | _ -> raise (MiddleError (spr "eval_rval error: %s" (show_expr expr)))
      end;
      0
  | EUnary(_,Deref,expr) -> eval2 expr name_ref
  | EPostfix(_,expr,Member(name)) when is_struct ty ->
    let decls = get_struct_id ty |> get_struct_members in
    let offset = match assoc3 name decls with
    | Some offset -> offset
    | None -> raise (MiddleError (spr "eval_rval error: %s" (show_expr expr)))
    in 
    (eval_rval expr name_ref) + offset
  | _ -> raise (MiddleError (spr "eval_rval error: %s" (show_expr expr)))

and eval_double expr =
  let ty = typeof expr in
  if is_integer ty && is_unsigned ty then
    float_of_int(eval expr |> uint_of_int)
  else if is_integer ty then
    float_of_int(eval expr)
  else
    match expr with
    | EConst(_,v) ->
      begin match v with
      | VFloat f -> f
      | _ -> raise (MiddleError (spr "eval_double error: %s" (show_expr expr)))
      end
    | EBinary(_,bin,lhs,rhs) ->
      begin match bin with
      | Add -> (eval_double lhs) +. (eval_double rhs)
      | Sub -> (eval_double lhs) -. (eval_double rhs)
      | Mul -> (eval_double lhs) *. (eval_double rhs)
      | Div -> (eval_double lhs) /. (eval_double rhs)
      | Comma -> eval_double rhs
      | _ -> raise (MiddleError (spr "eval_double error: %s" (show_expr expr)))
      end
    | EUnary(_,un,expr) ->
      begin match un with
      | Plus -> eval_double expr
      | Minus -> -.(eval_double expr)
      | _ -> raise (MiddleError (spr "eval_double error: %s" (show_expr expr)))
      end
    | ECond(_,flag,lhs,rhs) ->
      if bool_of_int (flag |> eval_double |> int_of_float) then
        eval_double lhs
      else 
        eval_double rhs
    | ECast(_,_,expr) ->
      eval_double expr
    | _ -> raise (MiddleError (spr "eval2 error: %s" (show_expr expr)))

let rec has_flonum ty lo hi offset =
  if offset < lo || hi <= offset then
    true
  else
    match ty with
    | _ when is_flonum ty -> true
    | _ when is_struct ty || is_union ty ->
        let decls = get_struct_id ty |> get_struct_members in
        let flag = ref true in
        List.iter 
        (
          function
          | (_,ty,Some x) when !flag -> flag :=  has_flonum ty lo hi (offset + x)
          | _ as decl -> raise (MiddleError (spr "has_flonum error: %s" (show_decl decl)))
        ) decls;
        !flag
    | _ -> false

let assign_params_offsets' decls =
  let gp = ref 0 in
  let fp = ref 0 in
  let aux top decl =
    let top = align_to top 8 in
    let ty = snd_ !decl in
    begin
      match ty with
      | _ when (is_struct ty || is_union ty) && sizeof ty <= 16 ->
        let fp1 = has_flonum ty 0 8 0 in
        let fp2 = has_flonum ty 8 16 8 in
        if !fp + (bool_to_int fp1) + (bool_to_int fp2) < fp_max
        && !gp + (bool_to_int (not fp1)) + (bool_to_int (not fp2)) < gp_max then
        begin
          fp := !fp + (bool_to_int fp1) + (bool_to_int fp2);
          gp := !gp + (bool_to_int (not fp1)) + (bool_to_int (not fp2));
          top
        end
        else
        begin
          decl :=  (fst_ !decl,ty,Some top);
          top + sizeof ty
        end
      | _ when is_flonum ty ->
        if !fp < fp_max then
        begin
          fp := !fp + 1;
          top
        end
        else
        begin
          decl := (fst_ !decl,ty,Some top);
          top + sizeof ty
        end
      | _ ->
        if !gp < gp_max then
        begin
          gp := !gp + 1;
          top
        end
        else
        begin
          decl := (fst_ !decl,ty,Some top);
          top + sizeof ty
        end
    end
  in
  let decls = List.map (fun x-> ref x) decls in
  ignore (List.fold_left aux 16 decls);
  List.map (fun x-> !x) decls

let assign_params_offsets item =
let aux decl =
match decl with
| (n,TFun(ret,decls),offset)-> 
  (n,TFun(ret,assign_params_offsets' decls),offset)
| _ -> decl
in
match item with
| Var(decl,init) -> Var(aux decl,init)
| Struct(n,Some decls) -> Struct(n,Some (List.map aux decls))
| Union(n,Some decls) -> Union(n,Some (List.map aux decls))
| Typedef decl -> Typedef(aux decl)
| Function(l,decl,stmts,sz) -> Function(l,aux decl,stmts,sz)
| _ -> item

let rec assign_lvars_offsets stmt =
  let bottom = ref 0 in
  let aux = function
  | (i,Var((name,ty,None),init_opt)) ->
    let align = 
      match ty with
      | TArr _ when sizeof ty >= 16 ->
        16
      | _ -> alignof ty
    in
    bottom := !bottom + sizeof ty;
    bottom := align_to !bottom align;
    (i,Var((name,ty,Some (-(!bottom))),init_opt))
  | _ as def -> def
  in
  let rec assign_lvars_offsets' stmt =
  match stmt with
  | SDef def -> SDef (aux def)
  | SStmts stmts -> SStmts (List.map assign_lvars_offsets' stmts)
  | SWhile(expr,stmt,s1,s2) -> SWhile(expr,assign_lvars_offsets' stmt,s1,s2)
  | SDoWhile(stmt,expr,s1,s2) -> SDoWhile(assign_lvars_offsets' stmt,expr,s1,s2)
  | SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,stmt,s1,s2) ->
    let def_opt = match def_opt with
    | Some def -> Some (aux def)
    | None -> None in
    SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,assign_lvars_offsets' stmt,s1,s2)
  | SIfElse(expr,stmt1,stmt2) -> SIfElse(expr,assign_lvars_offsets' stmt1,assign_lvars_offsets' stmt2)
  | SReturn expr_opt ->
    SReturn expr_opt
  | SLabel(s,stmt) -> SLabel(s,assign_lvars_offsets' stmt)
  | SGoto s -> SGoto s
  | SSwitch(expr,stmts,s) -> SSwitch(expr,List.map assign_lvars_offsets' stmts,s)
  | SCase(expr,stmts) -> SCase(expr,List.map assign_lvars_offsets' stmts)
  | SDefault stmts -> SDefault(List.map assign_lvars_offsets' stmts)
  | SExpr expr -> SExpr expr
  in
  (assign_lvars_offsets' stmt,!bottom)

and middle_item item =
let item = assign_params_offsets item in
match item with
| Var(decl,init_opt) ->
  Var(decl,init_opt)
| Function(l,decl,stmt_opt,_) ->
  let size = ref 0 in
  let stmt_opt = match stmt_opt with
  | Some stmt -> 
      let (stmt, sz) = assign_lvars_offsets stmt in
      size := sz;
      Some stmt
  | None -> None
  in
  Function(l,decl,stmt_opt,Some !size)
| _ -> item

and middle_def def =
let (i,item) = def in
(i,middle_item item)


and middle_program program =
match program with
| Program l -> Program(List.map middle_def l)

let pass program = middle_program program