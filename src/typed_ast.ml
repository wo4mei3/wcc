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
| Label of string
| Struct of string * decl list option
| Union of string * decl list option
| Enum of string * (string * int) list option
| Typedef of decl
| Function of def list * decl * stmt option
| Static_assert
[@@deriving show]

and def = int * item
[@@deriving show]

and expr =
| EConst  of ty * value
| EVar    of ty * int
| EBinary  of ty * binary * expr * expr
| EAssign of ty * binary option * expr * expr
| EUnary  of ty * unary * expr
| ETyUnary of ty * unary * ty
| EPostfix of ty * expr * postfix
| ECond   of ty * expr * expr * expr
| ECast   of ty * ty * expr
| ECompoundLit of ty * ty * init
[@@deriving show]

and postfix =
| Nth of expr
| Call of expr list
| Member of string
| Inc | Dec
[@@deriving show]
and init =
| IScal of expr
| IVect of init list
[@@deriving show]

and stmt =
| SDef of def
| SStmts of stmt list
| SWhile of expr * stmt
| SDoWhile of stmt * expr
| SFor of (def option) * (expr option) * (expr option) * (expr option) * stmt
| SIfElse of expr * stmt * stmt
| SReturn of expr option
| SContinue
| SBreak
| SLabel of string * stmt
| SGoto of int
| SSwitch of expr * stmt
| SCase of expr
| SDefault
| SExpr of expr
[@@deriving show]

type program =
| Program of def list
[@@deriving show]