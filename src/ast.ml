open Ctype

exception ASTError of string

let raise exn =
  match exn with
  (*| ASTError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

type value =
| VInt   of int
| VFloat of float
| VStr   of int list
[@@deriving show]

type binary =
| Add | Sub
| Mul | Div | Mod
| LShift | RShift
| BitAnd | BitXor | BitOr
| LogAnd | LogOr
| Lt | Le | Gt | Ge
| Eq | Ne
| Comma 
[@@deriving show]

type unary = 
| Plus | Minus | BitNot | LogNot | PreInc 
| PreDec | Ref | Deref | Sizeof
[@@deriving show]

type item =
| Var of decl * init option
| Param of decl
| Struct of string * decl list option
| Union of string * decl list option
| Enum of string * (string * int) list option
| Typedef of decl
| Function of def list * decl * stmt option
| Static_assert
[@@deriving show]

and def = int * item
[@@deriving show]

and def_list = def list
[@@deriving show]

and def_ll = def_list list
[@@deriving show]

and expr =
| EConst  of ty option * value
| EVar    of ty option * int
| EBinary  of ty option * binary * expr * expr
| EAssign of ty option * binary option * expr * expr
| EUnary  of ty option * unary * expr
| ETyUnary of ty option * unary * ty
| EPostfix of ty option * expr * postfix
| ECond   of ty option * expr * expr * expr
| ECast   of ty option * ty * expr
| ECompoundLit of ty option * ty * init
[@@deriving show]

and postfix =
| Nth of expr
| Call of expr list
| Member of string
| Inc | Dec
[@@deriving show]

and init =
| IScal of expr
| IVect of (desig option * init)  list
[@@deriving show]

and desig =
| DIdx of int * desig option
| DField of string * desig option
[@@deriving show]

and stmt =
| SDef of def
| SStmts of stmt list
| SWhile of expr * stmt * string * string
| SDoWhile of stmt * expr * string * string
| SFor of (def option) * (expr option) * (expr option) 
* (expr option) * stmt * string * string
| SIfElse of expr * stmt * stmt
| SReturn of expr option
| SLabel of string * stmt
| SGoto of string
| SSwitch of expr * stmt list * string
| SCase of expr * stmt list
| SDefault of stmt list
| SExpr of expr
[@@deriving show]

type program =
| Program of def list
[@@deriving show]

let rec get_def_from_ast id program =
  match program with
  | Program l ->
    get_def_from_def_list id l 

and get_def_from_def_list id l =
  match l with
  | [] -> None
  | x::xs ->
  match get_def_from_def id x with
  | Some x -> Some x
  | None -> get_def_from_def_list id xs

and get_def_from_def id def =
  match def with
  | (i, Var(_,_)) when id = i -> Some def
  | (i, Param(_)) when id = i -> Some def
  | (i, Struct(_,Some _)) when id = i -> Some def
  | (i, Union(_,Some _)) when id = i -> Some def
  | (i, Enum(_,Some _)) when id = i -> Some def
  | (i, Typedef(_)) when id = i -> Some def
  | (i, Function(_,_,_)) when id = i -> Some def
  | (_, Function(def_list,_,stmt_opt)) ->
  begin
        let rec get_def_from_stmts id stmts =
        match stmts with
        | [] -> None
        | x::xs ->
        begin
          match get_def_from_stmt id x with
          | Some _ as def -> def
          | None -> get_def_from_stmts id xs
        end
        and get_def_from_stmt id stmt = 
          match stmt with
          | SDef def -> get_def_from_def id def
          | SStmts l -> get_def_from_stmts id l 
          | SWhile(_,stmt,_,_) -> get_def_from_stmt id stmt
          | SDoWhile(stmt,_,_,_) -> get_def_from_stmt id stmt
          | SFor(def_opt,_,_,_,stmt,_,_) ->
          begin
            match def_opt with
            | Some def -> 
            begin 
              match get_def_from_def id def with
              | Some _ as def -> def
              | None -> get_def_from_stmt id stmt
            end
            | None -> get_def_from_stmt id stmt
          end
          | SIfElse(_,s1,s2) ->
          begin
            match get_def_from_stmt id s1 with
            | Some _ as def -> def
            | None -> get_def_from_stmt id s2
          end
          | SSwitch(_,stmts,_) -> get_def_from_stmts id stmts
          | SCase(_,stmts) -> get_def_from_stmts id stmts
          | SDefault(stmts) -> get_def_from_stmts id stmts
          | _ -> None
        in
    match get_def_from_def_list id def_list with
    | Some _ as def -> def
    | None ->
    begin
      match stmt_opt with
      | Some stmt -> get_def_from_stmt id stmt
      | None -> None
    end
  end
  | _ -> None

let get_typedef_from_ast id program =
  match get_def_from_ast id program with
  | Some  (_,Typedef(_) as def) -> def
  | _ -> raise (ASTError (spr "typedef not found with id %d" id))