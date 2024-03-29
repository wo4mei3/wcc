let print_tok pos token = 
  let open Lexing in
  Printf.printf "(%d, %d):\"%s\"" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) token

let curr_token = ref ""

let curr_pos = 
  let open Lexing in
  ref {pos_fname="";pos_lnum=0;pos_bol=0;pos_cnum=0}

let conv lexer =
  fun lexbuf ->
    curr_token := Lexing.lexeme lexbuf;
    curr_pos := Lexing.lexeme_start_p lexbuf;
    lexer lexbuf 


let () =
  let argc = Array.length Sys.argv in
  if argc != 2 then 
    begin
      Format.printf "Usage: ./cc [filename]\n";exit (-1)
    end
  else
  let fname = Sys.argv.(1) in
  let inchan = open_in fname in
  let filebuf = Lexing.from_channel inchan in
  begin
  try
    Ast.program := Parser.translation_unit (conv Lexer.token) filebuf;
    Ast.program := Typing.typing !Ast.program;
    Ast.program := Middle.pass !Ast.program
  with
  | Dune__exe__Parser_helper.ParserError _
  | Dune__exe__Parser_helper.NotImpl _
  | Dune__exe__Ctype.TypeError _ 
  | Dune__exe__Ast.ASTError _
  | Dune__exe__Typing.TypingError _ -> print_tok !curr_pos !curr_token; print_endline "something went wrong while parsing"
  end;
  Printf.printf "%s\n" (Ast.show_program !Ast.program)