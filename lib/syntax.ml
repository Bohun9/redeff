(* Terms are divided into the expressions and values *)

type var = string
type label = string

type value = 
  | VVar of var
  | VLam of var * expr
  | VInt of int

and expr = 
  | EAdd of value * value
  | EApp of value * value  
  | ERet of value
  | ELet of var * expr * expr
  | EDo of label * value
  | EHandle of handler * expr

and handler = Handler of return_clause * op_clause list

and return_clause = RetClause of var * expr
and op_clause = OpClause of label * var * var * expr

let op_clauses (Handler(_, ops)) = ops
let ret_clause (Handler(ret, _)) = ret
