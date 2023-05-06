
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
  try
    let program = Parser.translation_unit Lexer.token filebuf in
    Printf.printf "%s\n" (Ast.show_program program)
  with
  | Lexer.LexerError msg -> Printf.printf "%s" msg
  | _ -> print_endline "something went wrong"