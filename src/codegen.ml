open Ctype
open Ast
open Typing
open Middle 

exception CodegenError of string

let raise exn =
  match exn with
  (*| CodegenError msg -> Printf.printf "%s\n" msg;raise exn*)
  | _ -> raise exn

let spr fmt s = (Printf.sprintf  fmt s)