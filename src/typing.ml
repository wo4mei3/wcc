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

and aligned ty n =
  let a = alignof ty in
  (n + a - 1) / a * a

and sizeof ty = 
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
  | TFun _ -> raise (TypingError (spr "alignof error: %s" (show_ty ty)))
