open Ctype
open Ast

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
