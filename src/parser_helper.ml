    exception ParserError of string
    exception NotImpl of string

    let raise exn =
    match exn with
    | ParserError msg -> Printf.printf "ParserError: %s\n" msg;raise exn
    | NotImpl msg -> Printf.printf "NotImpl: %s\n" msg;raise exn
    | _ -> raise exn