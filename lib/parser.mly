%{
  open Syntax
%}

%type <Syntax.expr> file
%start file

%token EOF
%token <string> IDENTIFIER
%token <int> INT

%token FN
%token LET IN RET DO HANDLE WITH
%token PLUS EQ ARROW
%token L_BRACE R_BRACE L_PAREN R_PAREN

%%

expr
  : LET IDENTIFIER EQ expr IN expr { ELet($2, $4, $6) }
  | HANDLE expr WITH handler { EHandle($4, $2) }
  | expr_simpl { $1 }

expr_simpl
  : RET value { ERet($2) }
  | DO IDENTIFIER value { EDo($2, $3) }
  | value PLUS value { EAdd($1, $3) }
  | value value { EApp($1, $2) }
  | L_PAREN expr R_PAREN { $2 }

value 
  : FN IDENTIFIER ARROW expr { VLam($2, $4) }
  | INT { VInt $1 }
  | IDENTIFIER { VVar $1 }
  | L_PAREN value R_PAREN { $2 }

handler
  : ret_clause op_clauses { Handler($1, $2) }

ret_clause
  : L_BRACE RET IDENTIFIER ARROW expr R_BRACE { RetClause($3, $5) }

op_clause
  : L_BRACE IDENTIFIER IDENTIFIER IDENTIFIER ARROW expr R_BRACE { OpClause($2, $3, $4, $6) }

op_clauses
  : { [] }
  | op_clause op_clauses { $1 :: $2 }

file : expr EOF { $1 }

%%
