open Interpreter
open Utils

let read_file file =
  let ch =
    try open_in_bin file
    with Sys_error s ->
      Printf.eprintf "%s\n" s;
      exit 1
  in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let file = Sys.argv.(1)
let source = read_file file
let program = Utils.parse_from_string source

let _ = print_endline (expr_to_string program)
let _ = print_endline "\n---->>>>\n"
let _ = print_endline (Eval.normalize program |> expr_to_string)

