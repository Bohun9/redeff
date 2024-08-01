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

(* Evaluation contexts *)

type context = 
  | CSquare
  | CLet of var * context * expr
  | CHandle of handler * context

(* Redexes *)

type redex = 
  | RAdd of int * int
  | RBeta of var * expr * value
  | RLet of var * value * expr
  | RHandleRet of var * expr * value
  | RHandleDo of handler * context * label * value

(* Decomposition *)

type decomp = context * redex

let op_clauses (Handler(_, ops)) = ops
