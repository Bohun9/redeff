open Syntax

module type ENV = sig
  type 'a t
  val empty : 'a t
  val extend : var -> 'a -> 'a t -> 'a t
  val lookup : var -> 'a t -> 'a option
  val to_string : ('a -> string) -> 'a t -> string
end

module Env : ENV = struct
  module VarMap = Map.Make(struct
    type t = var
    let compare = compare
  end)

  type 'a t = 'a VarMap.t
  let empty = VarMap.empty
  let extend = VarMap.add
  let lookup = VarMap.find_opt
  let to_string val_to_string env = VarMap.fold (fun x v acc -> Printf.sprintf "%s%s ↦  %s\n" acc x (val_to_string v)) env ""
end

(* Evaluation contexts *)

type context = 
  | CSquare
  | CLet of (var * expr * env) * context
  | CHandle of (handler * env) * context

(* Redexes *)

and redex = 
  | RAdd of int * int
  | RBeta of var * expr * env * walue
  | RLet of var * expr * env * walue
  | RHandleRet of var * expr * env * walue
  | RHandleDo of handler * context * label * env * walue
  | RContApp of context * walue

and walue = 
  | WInt of int
  | WClosure of env * var * expr
  | WCont of context

and env = walue Env.t

type vm_state = context * expr * env

let walue_to_string (w : walue) : string = 
  match w with
  | WInt n -> string_of_int n
  | WClosure _ -> "<closure>"
  | WCont _ -> "<cont>"

(* Just for printing result *)
let rec plug (c : context) (e : expr) : expr = 
  match c with
  | CSquare -> e
  | CLet((x, e', _), c') -> plug c' (ELet(x, e, e'))
  | CHandle((h, _), c') -> plug c' (EHandle(h, e))

let vm_state_to_string ((c, e, env) : vm_state) : string = 
  Env.to_string walue_to_string env ^ (plug c e |> Utils.expr_to_string)

let rec connect_contexts (c_up : context) (c_down : context) : context = 
  match c_down with
  | CSquare -> c_up
  | CLet(frame, c') -> CLet(frame, connect_contexts c_up c')
  | CHandle(frame, c') -> CHandle(frame, connect_contexts c_up c')

let contract (c : context) (r : redex) : vm_state = 
  match r with
  | RAdd(n1, n2) -> c, ERet (VInt (n1 + n2)), Env.empty
  | RBeta(x, e, env, w) | RLet(x, e, env, w) | RHandleRet(x, e, env, w) -> c, e, Env.extend x w env
  | RContApp(c', w) -> connect_contexts c c', (ERet (VVar "cont_arg")), Env.empty |> Env.extend "cont_arg" w
  | RHandleDo(h, c_local, l, env, w) ->
      let (OpClause(_, y, k, e)) = List.find (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) in
      let c' = connect_contexts (CHandle((h, env), CSquare)) c_local in
      c, e, env |> Env.extend y w |> Env.extend k (WCont c')

let rec find_handler (l : label) (c : context) : (handler * context * context * env) option = 
  match c with
  | CSquare -> None (* uncaught operation *)
  | CLet((x, e, let_env), c') ->
      begin match find_handler l c' with
      | None -> None
      | Some(h, c, k, env) -> Some(h, c, CLet((x, e, let_env), k), env)
      end
  | CHandle((h, hdlr_env), c') ->
      begin match List.find_opt (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) with
      | Some _ -> Some(h, c', CSquare, hdlr_env)
      | None ->
          begin match find_handler l c' with
          | None -> None
          | Some(h, c, k, env) -> Some(h, c, CHandle((h, hdlr_env), k), env)
          end
      end

type decomp =
  | Decomp of context * redex
  | Normal of vm_state

let value_to_walue (v : value) (env : env) : walue option = 
  match v with
  | VInt n -> Some (WInt n)
  | VLam(x, e) -> Some (WClosure(env, x, e))
  | VVar x -> Env.lookup x env

let rec refocus (c : context) (e : expr) (env : env) : (context * redex) option =
  match e with
  | EAdd(v1, v2) ->
      begin match value_to_walue v1 env, value_to_walue v2 env with
      | Some(WInt n1), Some(WInt n2) -> Some(c, RAdd(n1, n2))
      | _, _ -> None
      end
  | EApp(v1, v2) -> 
      begin match value_to_walue v1 env, value_to_walue v2 env with
      | Some(WClosure(clo_env, x, e)), Some(w) -> Some(c, RBeta(x, e, clo_env, w))
      | Some(WCont(c')), Some(w) -> Some(c, RContApp(c', w))
      | _, _ -> None
      end
  | ERet v -> 
      begin match c with
      | CSquare -> None
      | CLet((x, e, env'), c') ->
          begin match value_to_walue v env with
          | Some w -> Some(c', RLet(x, e, env', w))
          | None -> None
          end
      | CHandle((h, env'), c') ->
          begin match value_to_walue v env with
          | Some w ->
              let RetClause(x, e) = ret_clause h in
              Some(c', RHandleRet(x, e, env', w))
          | None -> None
          end
      end
  | ELet(x, e1, e2) -> refocus (CLet((x, e2, env), c)) e1 env
  | EDo(l, v) -> 
      begin match value_to_walue v env with
      | Some w ->
          begin match find_handler l c with
          | None -> None
          | Some(h, c, k, hdlr_env) -> Some(c, RHandleDo(h, k, l, hdlr_env, w))
          end
      | None -> None
      end
  | EHandle(h, e1) -> refocus (CHandle((h, env), c)) e1 env

let refocus ((c, e, env) : vm_state) : decomp = 
  (* print_endline (vm_state_to_string (c, e, env)); *)
  (* print_endline ""; *)
  match refocus c e env with
  | Some(c, r) -> Decomp(c, r)
  | None -> Normal(c, e, env)

let rec iterate (d : decomp) : vm_state = 
  match d with
  | Normal s -> s
  | Decomp(c, r) ->
      let (c', e, env) = contract c r in
      iterate (refocus (c', e, env))

let normalize (e : expr) : vm_state = 
  iterate (refocus (CSquare, e, Env.empty))
