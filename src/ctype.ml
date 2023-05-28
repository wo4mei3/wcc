exception TypeError of string

let raise exn =
  match exn with
  (*| TypeError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

type ty =
| TFun of ty * decl list
| TPtr of ty 
| TArr of ty * int
| TDeclSpec of ds list
[@@deriving show]

and decl = (string * ty)
[@@deriving show]

and ds = 
| Ts of ts
| Scs of scs
| Tq of tq
| Fs of fs
[@@deriving show]

and ts =
| TsInt  | TsShort  | TsLong  | TsChar
| TsUInt  | TsUShort  | TsULong  | TsUChar
| TsFloat | TsDouble 
| TsVoid
| TsStruct of int
| TsUnion of int
| TsTypedef of int
[@@deriving show]

and scs =
| ScsTypedef
| ScsExtern
| ScsStatic
| ScsAuto
| ScsRegister
[@@deriving show]

and tq =
| TqConst
| TqVolatile
[@@deriving show]

and fs =
| FsInline
| FsNoreturn
[@@deriving show]

let rec get_declspecs ty =
  match ty with
  | TFun(t,_) -> get_declspecs t 
  | TPtr t -> get_declspecs t 
  | TArr(t,_) -> get_declspecs t 
  | TDeclSpec dsl -> dsl


let is_integer = function
| TDeclSpec dsl ->
  let l = [Ts TsInt; Ts TsShort; Ts TsLong; Ts TsChar;Ts TsUInt; Ts TsUShort; Ts TsULong; Ts TsUChar] in
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

let is_signed = function
| TDeclSpec dsl ->
  let l = [Ts TsInt; Ts TsShort; Ts TsLong; Ts TsChar] in
    let aux init f = init || List.mem f dsl in
    List.fold_left aux false l
| _ -> false

let is_unsigned = function
| TDeclSpec dsl -> 
  let l = [Ts TsUInt; Ts TsUShort; Ts TsULong; Ts TsUChar] in
    let aux init f = init || List.mem f dsl in
    List.fold_left aux false l
| _ -> false

let is_struct = function
| TDeclSpec dsl -> 
  let aux = function
  | Ts (TsStruct _) -> true 
  | _ -> false
  in
  List.exists aux dsl
| _ -> false

let get_struct_id = function
| TDeclSpec dsl -> 
  let rec aux = function
  | [] -> raise (TypeError "get_struct_id")
  | Ts (TsStruct id)::_ -> id 
  | _::xs -> aux xs
  in
  aux dsl
| _ -> raise (TypeError "get_struct_id")

let is_union = function
| TDeclSpec dsl -> 
  let aux = function
  | Ts (TsUnion _) -> true 
  | _ -> false
  in
  List.exists aux dsl
| _ -> false

let get_union_id = function
| TDeclSpec dsl -> 
  let rec aux = function
  | [] -> raise (TypeError "get_union_id")
  | Ts (TsUnion id)::_ -> id 
  | _::xs -> aux xs
  in
  aux dsl
| _ -> raise (TypeError "get_union_id")