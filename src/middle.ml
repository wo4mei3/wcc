open Ctype
open Ast
open Typing

exception MiddleError of string

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
          | _ -> raise (MiddleError (spr "has_flonum error: %s" (show_ty ty)))
        ) decls;
        !flag
    | _ -> false

let assign_mems_offsets ty =
  let mems = get_struct_id ty |> get_struct_members in
  let aux offset decl =
    let ty = snd_ !decl in
    decl := (fst_ !decl, snd_ !decl, Some offset);
    aligned ty offset + sizeof ty
  in
  let mems = List.map (fun x-> ref x) mems
  in
  ignore (List.fold_left aux 0  mems);
  List.map (fun x-> !x) mems



let rec middle_stmt stmt =
match stmt with
| SDef def -> SDef (middle_def def)
| SStmts stmts -> SStmts (List.map middle_stmt stmts)
| SWhile(expr,stmt,s1,s2) -> SWhile(expr,middle_stmt stmt,s1,s2)
| SDoWhile(stmt,expr,s1,s2) -> SDoWhile(middle_stmt stmt,expr,s1,s2)
| SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,stmt,s1,s2) ->
  let def_opt = match def_opt with
  | Some def -> Some (middle_def def)
  | None -> None in
  SFor(def_opt,expr_opt1,expr_opt2,expr_opt3,middle_stmt stmt,s1,s2)
| SIfElse(expr,stmt1,stmt2) -> SIfElse(expr,middle_stmt stmt1,middle_stmt stmt2)
| SReturn expr_opt ->
  SReturn expr_opt
| SLabel(s,stmt) -> SLabel(s,middle_stmt stmt)
| SGoto s -> SGoto s
| SSwitch(expr,stmts,s) -> SSwitch(expr,List.map middle_stmt stmts,s)
| SCase(expr,stmts) -> SCase(expr,List.map middle_stmt stmts)
| SDefault stmts -> SDefault(List.map middle_stmt stmts)
| SExpr expr -> SExpr expr


and middle_item item =
match item with
| Var(decl,init_opt) ->
  Var(decl,init_opt)
| Function(l,decl,stmt_opt,stack_size) ->
  let stmt_opt = match stmt_opt with
  | Some stmt -> Some (middle_stmt stmt)
  | None -> None in
  Function(l,decl,stmt_opt,stack_size)
| _ -> item

and middle_def def =
let (i,item) = def in
(i,middle_item item)

and middle_program program =
match program with
| Program l -> Program(List.map middle_def l)

let middle_pass program = middle_program program