let read_whole_file filename =
    (* open_in_bin works correctly on Unix and Windows *)
    let ch = open_in_bin filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let p s = Printf.printf "%s\n" s

let () = p "hjgf"
let () =
  p "a";
  let argc = Array.length Sys.argv in
  Printf.printf "%d" argc;
  if argc != 2 then 
    begin
      Format.printf "Usage: ./cc [filename]\n";exit (-1)
    end
  else
  let fname = Sys.argv.(1) in
  p fname;
  let src = read_whole_file fname in
  let _ = Lexing.from_string src in p src (*
  try
    let program = Parser.translation_unit Lexer.token filebuf in
    Printf.printf "%s" (Ast.show_program program);
    p "b"
  with
  | Invalid_argument _ -> p "dsa"
  | Lexer.LexerError msg -> p msg
  | _ -> print_endline "something went wrong"*)