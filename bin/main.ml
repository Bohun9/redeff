open Interpreter
open Syntax
open Utils

let expr = ELet("x", EDo("tell", VInt 101), ERet(VVar "x"))

let prog = EHandle(Handler(RetClause("x", ERet(VVar "x")),
                           [OpClause("tell", "y", "r", ELet("x1", EApp(VVar "r", VInt 1), 
                                                       ELet("x2", EApp(VVar "r", VInt 2),
                                                       ELet("s",  EAdd(VVar "x1", VVar "x2"),
                                                       EAdd(VVar "s", VVar "y"))))
                           )])
                  , expr)

let _ = print_endline (prog |> expr_to_string)
let _ = print_endline (Eval.iterate prog |> expr_to_string)
