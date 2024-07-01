open Syntax

let rec value_to_string (v : value) : string = 
  match v with
  | VVar x -> x
  | VLam(_, _) -> "<fn>"
  | VInt n -> string_of_int n

and expr_to_string (e : expr) (d : int) : string = 
  let space = String.make d ' ' in
  match e with
  | EAdd(v1, v2) -> Printf.sprintf "%s%s + %s" space (value_to_string v1) (value_to_string v2)
  | EApp(v1, v2) -> Printf.sprintf "%s(%s %s)" space (value_to_string v1) (value_to_string v2)
  | ERet v -> Printf.sprintf "%sReturn %s" space (value_to_string v)
  | ELet(x, e1, e2) -> Printf.sprintf "%slet %s =\n%s\n%sin\n%s" space x (expr_to_string e1 (d + 1)) space (expr_to_string e2 d)
  | EDo(l, v) -> Printf.sprintf "%sdo %s %s" space l (value_to_string v)
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
