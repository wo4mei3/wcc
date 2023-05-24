open Ctype
open Ast

exception TypingError of string

let raise exn =
  match exn with
  (*| TypeError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

let rec declspecs attr is_encountered dsl program =
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
    match get_def_from_ast i program with
    | Some  (_,Typedef(decl)) -> 
    begin
      let ty = snd decl in
      let dsl = get_declspecs ty in
      declspecs attr is_encountered dsl program
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

let rec sizeof ty = 
  match ty with
  | TDeclSpec dsl ->
    if List.mem (Ts TsVoid) dsl then
      raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
    else if List.mem (Ts TsChar) dsl then
      1
    else if List.mem (Ts TsShort) dsl then
      2
    else if List.mem (Ts TsLong) dsl then
      8
    else if List.mem (Ts TsInt) dsl then
      4
    else if List.mem (Ts TsSigned) dsl || List.mem (Ts TsUnsigned) dsl then
      4
    else raise (TypingError (spr "sizeof error: %s" (show_ty ty)))
  | TArr(ty, sz) -> (sizeof ty) * sz
  | TPtr _ -> 8
  | _ -> 0

let is_integer = function
| TDeclSpec dsl ->
  let l = [Ts TsInt; Ts TsShort; Ts TsLong; Ts TsChar] in
    let aux init f = init || List.mem f dsl in
    List.fold_left aux false l
| _ -> false

let is_flonum = function
| TDeclSpec dsl ->
  let l = [Ts TsFloat; Ts TsDouble] in
    let aux init f = init || List.mem f dsl in
    List.fold_left aux false l
| _ -> false

let is_numeric ty =
  is_integer ty || is_flonum ty

let is_unsigned ty = 
match ty with
| TDeclSpec dsl -> List.mem (Ts TsUnsigned) dsl && is_numeric ty
| _ -> false

let is_signed ty =
  is_numeric ty && not (is_unsigned ty)