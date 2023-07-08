open Ast

exception EnvError of string

let raise exn =
  match exn with
  (*| EnvError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)

let in_declarator = ref false

let global_scope:def list ref = ref []

let curr_scope: def list ref = global_scope

let stack:def list list ref = ref []

let peek_curr_scope () =
  List.hd !curr_scope

let pop_curr_scope () =
  curr_scope := List.rev (List.tl (List.rev !curr_scope))


let push_def def =
  curr_scope := def :: !curr_scope

let enter_scope () =
  stack := !curr_scope :: !stack;
  curr_scope := []

let leave_scope () =
  curr_scope := List.hd !stack;
  stack := List.tl !stack

let get_var name =
  let pred (_,item) =
  match item with
  | Var((n,_,_),_) when n = name -> true
  | Function(_,(n,_,_),_,_) when n = name -> true
  | _ -> false
  in
  let (id,_) = try 
    List.find pred !curr_scope
  with Not_found ->
    let rec aux = function
    | hd::tl ->
      begin
      try
        List.find pred hd
      with Not_found ->
        aux tl
      end
    | [] ->
    begin
      (*Printf.printf "%s" (show_def_ll !stack);*)
      raise (EnvError  (spr "var not found: %s\n" name))
    end
    in aux !stack
  in id

let get_typedef name =
  let pred (_,item) =
  match item with
  | Typedef(n,_,_) when n = name -> true
  | _ -> false
  in
  let (id,_) = try 
    List.find pred !curr_scope
  with Not_found ->
    let rec aux = function
    | hd::tl ->
      begin
      try
        List.find pred hd
      with Not_found ->
        aux tl
      end
    | [] ->
      raise (EnvError  (spr "typedef not found: %s\n" name))
    in aux !stack
  in id