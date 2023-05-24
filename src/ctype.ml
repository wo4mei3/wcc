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