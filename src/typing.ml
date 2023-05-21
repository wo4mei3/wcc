open Ctype

let declspecs dsl attr =
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
  let is_encountered = ref false
  and is_char_or_int = ref false
  and is_int = ref false
  and is_int_or_double = ref false
  and is_short = ref false
  and is_long = ref false
  and is_signed = ref false
  and is_unsigned = ref false
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
  | Ts (TsTypedef _)
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
  end;
  if !is_signed && !is_unsigned then
       raise (TypeError ( 
  "both signed and unsigned are appear"))
  else if !is_signed || !is_unsigned then
  begin
    if not !is_char_or_int && !is_encountered then
            raise (TypeError ( 
  "signed or unsigned with other than char or int is not allowed"))
    else ()
  end