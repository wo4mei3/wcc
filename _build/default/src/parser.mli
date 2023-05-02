
(* The type of tokens. *)

type token = 
  | XOR_EQ
  | WHILE
  | VOLATILE
  | UNION
  | ULINT of (int)
  | UINT of (int)
  | TYPE_ID of (string)
  | TYPEDEF
  | TVOID
  | TUNSIGNED
  | TSIGNED
  | TSHORT
  | TLONG
  | TINT
  | TFLOAT
  | TDOUBLE
  | TCHAR
  | SWITCH
  | SUB_EQ
  | STRUCT
  | STR of (int list)
  | STATIC_ASSERT
  | STATIC
  | STAR
  | SIZEOF
  | SEMI
  | RSHIFT_EQ
  | RSHIFT
  | RPAREN
  | RETURN
  | REGISTER
  | RBRACKET
  | RBRACE
  | QUESTION
  | PLUS
  | OR_EQ
  | OROR
  | OR
  | NOT
  | NORETURN
  | NE
  | MUL_EQ
  | MOD_EQ
  | MOD
  | MINUS
  | LT
  | LSHIFT_EQ
  | LSHIFT
  | LPAREN
  | LINT of (int)
  | LE
  | LBRACKET
  | LBRACE
  | INT of (int)
  | INLINE
  | INC
  | IF
  | ID of (string)
  | HAT
  | GT
  | GOTO
  | GE
  | FOR
  | FLOAT of (float)
  | EXTERN
  | EQEQ
  | EQ
  | EOF
  | ENUM
  | ELSE
  | ELLIPSIS
  | DOUBLE of (float)
  | DOT
  | DO
  | DIV_EQ
  | DIV
  | DEFAULT
  | DEC
  | CONTINUE
  | CONST
  | COMMA
  | COLON
  | CASE
  | BREAK
  | BANG
  | AUTO
  | ARROW
  | AND_EQ
  | ANDAND
  | AND
  | ALIGNAS
  | ADD_EQ

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val translation_unit: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.program)
