open Syntax

let rec subst_expr (e : expr) (x : var) (w : value) : expr = 
  match e with
  | EAdd(v1, v2) -> EAdd(subst_val v1 x w, subst_val v2 x w)
  | EApp(v1, v2) -> EApp(subst_val v1 x w, subst_val v2 x w)
  | ERet v -> ERet(subst_val v x w)
  | ELet(y, e1, e2) ->
      let e1 = if x = y then e1 else subst_expr e1 x w in
      ELet(y, e1, subst_expr e2 x w)
  | EDo(l, v) -> EDo(l, subst_val v x w)
  | EHandle(Handler(h_ret, h_ops), e) ->
      let subst_ret_clause (RetClause(y, e1) as h_ret) = 
        if x = y then h_ret else RetClause(y, subst_expr e1 x w)
      in
      let subst_op_clause (OpClause(l, y, r, e1) as h_op) = 
        if x = y || x = r then h_op else (OpClause(l, y, r, subst_expr e1 x w))
      in
      EHandle(Handler(subst_ret_clause h_ret, List.map subst_op_clause h_ops), subst_expr e x w)

and subst_val (v : value) (x : var) (w : value) : value = 
  match v with
  | VVar y -> if x = y then w else v
  | VLam(y, body) -> if x = y then v else VLam(y, subst_expr body x w) (* name capture? *)
  | VInt _ -> v

let fresh = 
  let r = ref 0 in
  fun () -> incr r; "f" ^ string_of_int !r

let rec contract (r : redex) : expr = 
  match r with
  | RAdd(n1, n2) -> ERet (VInt (n1 + n2))
  | RBeta(x, b, v) -> subst_expr b x v
  | RLet(x, v, e) -> subst_expr e x v
  | RHandleRet(x, e, v) -> subst_expr e x v
  | RHandleDo(h, c, l, v) ->
      let (OpClause(_, y, k, e)) = List.find (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) in
      let e = subst_expr e y v in
      let x = fresh () in
      let e = subst_expr e k (VLam(x, EHandle(h, plug c (ERet (VVar x))))) in
      e

and plug (c : context) (e : expr) : expr = 
  match c with
  | CSquare -> e
  | CLet(x, c', e') -> plug c' (ELet(x, e, e'))
  | CHandle(h, c') -> plug c' (EHandle(h, e))

let rec find_handler (l : label) (c : context) : (handler * context * context) option = 
  match c with
  | CSquare -> None (* uncaught operation *)
  | CLet(x, c', e) ->
      begin match find_handler l c' with
      | None -> None
      | Some(h, c, k) -> Some(h, c, CLet(x, k, e))
      end
  | CHandle(h, c') ->
      begin match List.find_opt (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) with
      | Some _ -> Some(h, c', CSquare)
      | None ->
          begin match find_handler l c' with
          | None -> None
          | Some(h, c, k) -> Some(h, c, CHandle(h, k))
          end
      end

let rec decompose (e : expr) (c : context) : decomp option = 
  match e with
  | EAdd(VInt n1, VInt n2) -> Some(c, RAdd(n1, n2))
  | EAdd(_, _) -> None
  | EApp(VLam(x, e1), v) -> Some(c, RBeta(x, e1, v))
  | EApp(_, _) -> None
  | ERet _ -> None
  | ELet(x, (ERet v), e2) -> Some(c, RLet(x, v, e2))
  | ELet(x, e1, e2) -> decompose e1 (CLet(x, c, e2))
  | EDo(l, v) -> 
      begin match find_handler l c with
      | None -> None
      | Some(h, c, k) -> Some(c, RHandleDo(h, k, l, v))
      end
  | EHandle(Handler(RetClause(x, e), _), (ERet v)) -> Some(c, RHandleRet(x, e, v))
  | EHandle(h, e1) -> decompose e1 (CHandle(h, c))

let decompose (e : expr) : decomp option = 
  decompose e CSquare

let rec iterate (e : expr) : expr = 
  match decompose e with
  | None -> e
  | Some(c, r) -> iterate (plug c (contract r))

