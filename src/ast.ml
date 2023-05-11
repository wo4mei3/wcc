open Ctype

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
| EConst  of value
| EVar    of int
| EBinary  of binary * expr * expr
| EAssign of binary option * expr * expr
| EUnary  of unary * expr
| ETyUnary of unary * ty
| EPostfix of expr * postfix
| ECond   of expr * expr * expr
| ECast   of ty * expr
| ECompoundLit of ty * init
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