open Ast

exception EnvError of string

let in_declarator = ref false

let curr_scope: def list ref = ref []
let stack:def list list ref = ref []

let push_def def =
  curr_scope := def :: !curr_scope

let enter_scope () =
  stack := !curr_scope :: !stack

let leave_scope () =
  stack := List.tl !stack

let get_var name =
  let pred (_,item) =
  match item with
  | Var((n,_),_) when n = name -> true
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
      raise (EnvError "var not found")
    in aux !stack
  in id

let get_typedef name =
  let pred (_,item) =
  match item with
  | Typedef(n,_) when n = name -> true
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
      raise (EnvError "var not found")
    in aux !stack
  in id