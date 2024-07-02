open Syntax

let rec value_to_string (v : value) (d : int) : string = 
  match v with
  | VVar x -> x
  | VLam(x, e) -> Printf.sprintf "fn %s =>\n%s" x (expr_to_string e d)
  | VInt n -> string_of_int n

and expr_to_string (e : expr) (d : int) : string = 
  let space = String.make d ' ' in
  match e with
  | EAdd(v1, v2) -> Printf.sprintf "%s%s + %s" space (value_to_string v1 d) (value_to_string v2 d)
  | EApp(v1, v2) -> Printf.sprintf "%s(%s %s)" space (value_to_string v1 d) (value_to_string v2 d)
  | ERet v -> Printf.sprintf "%sreturn %s" space (value_to_string v d)
  | ELet(x, e1, e2) -> Printf.sprintf "%slet %s =\n%s\n%sin\n%s" space x (expr_to_string e1 (d + 1)) space (expr_to_string e2 d)
  | EDo(l, v) -> Printf.sprintf "%sdo %s %s" space l (value_to_string v d)
  | EHandle(h, e) -> Printf.sprintf "%shandle\n%s\n%swith\n%s" space (expr_to_string e (d + 1)) space (handler_to_string h (d + 1))

and handler_to_string (h : handler) (d : int) : string = 
  let space = String.make d ' ' in
  match h with
  | Handler(RetClause(l, e), h_ops) ->
      let ret = Printf.sprintf "%s{ %s =>\n%s }\n" space l (expr_to_string e (d + 2)) in
      let op_fn (OpClause(l, x, r, e)) = Printf.sprintf "%s{ %s %s %s =>\n%s }\n" space l x r (expr_to_string e (d + 2)) in
      ret ^ String.concat "" (List.map op_fn h_ops)

let expr_to_string (e : expr) : string = 
  expr_to_string e 0

let parse_from_string (source : string) : expr =
  let lexbuf = Lexing.from_string source in
  try Parser.file Lexer.token lexbuf
  with Parser.Error ->
    Printf.fprintf stderr "At offset %d: syntax error.\n%!"
      (Lexing.lexeme_start lexbuf);
    failwith ""
