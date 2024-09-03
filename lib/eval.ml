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
  | CLet of var * context * expr * env
  | CHandle of handler * context * env

(* Redexes *)

and redex = 
  | RAdd of int * int
  | RBeta of env * var * context * expr * walue
  | RLet of var * walue * expr
  | RHandleRet of var * expr * walue
  | RHandleDo of handler * context * label * walue * env

and walue = 
  | WInt of int
  | WClosure of env * var * context * expr

and env = walue Env.t

type vm_state = context * expr * env

let walue_to_string (w : walue) : string = 
  match w with
  | WInt n -> string_of_int n
  | WClosure _ -> "<closure>"

(* Just for printing result *)
let rec plug (c : context) (e : expr) : expr = 
  match c with
  | CSquare -> e
  | CLet(x, c', e', _) -> plug c' (ELet(x, e, e'))
  | CHandle(h, c', _) -> plug c' (EHandle(h, e))

let vm_state_to_string ((c, e, env) : vm_state) : string = 
  Env.to_string walue_to_string env ^ (plug c e |> Utils.expr_to_string)

let fresh = 
  let r = ref 0 in
  fun () -> incr r; "f" ^ string_of_int !r

let rec connect_contexts (c_up : context) (c_down : context) : context = 
  match c_down with
  | CSquare -> c_up
  | CLet(x, c', e, env) -> CLet(x, connect_contexts c_up c', e, env)
  | CHandle(h, c', env) -> CHandle(h, connect_contexts c_up c', env)

let contract (c : context) (r : redex) (env : env) : vm_state = 
  match r with
  | RAdd(n1, n2) -> c, ERet (VInt (n1 + n2)), env
  | RBeta(env', x, c', e, w) -> connect_contexts c c', e, Env.extend x w env'
  | RLet(x, w, e) -> c, e, Env.extend x w env
  | RHandleRet(x, e, w) -> c, e, Env.extend x w env
  | RHandleDo(h, c_local, l, w, env') ->
      let (OpClause(_, y, k, e)) = List.find (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) in
      let x = fresh () in
      let c' = connect_contexts (CHandle(h, CSquare, env)) c_local in
      c, e, env |> Env.extend y w |> Env.extend k (WClosure(env', x, c', (ERet (VVar x))))

let rec find_handler (l : label) (c : context) : (handler * context * context * env) option = 
  match c with
  | CSquare -> None (* uncaught operation *)
  | CLet(x, c', e, let_env) ->
      begin match find_handler l c' with
      | None -> None
      | Some(h, c, k, env) -> Some(h, c, CLet(x, k, e, let_env), env)
      end
  | CHandle(h, c', hdlr_env) ->
      begin match List.find_opt (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) with
      | Some _ -> Some(h, c', CSquare, hdlr_env)
      | None ->
          begin match find_handler l c' with
          | None -> None
          | Some(h, c, k, env) -> Some(h, c, CHandle(h, k, hdlr_env), env)
          end
      end

type decomp =
  | Decomp of context * redex * env
  | Normal of vm_state

let value_to_walue (v : value) (env : env) : walue option = 
  match v with
  | VInt n -> Some (WInt n)
  | VLam(x, e) -> Some (WClosure(env, x, CSquare, e))
  | VVar x -> 
      begin match Env.lookup x env with
      | Some w -> Some w
      | None -> None
      end

let value_to_int (v : value) (env : env) : int option = 
  match value_to_walue v env with
  | Some w ->
      begin match w with
      | WInt n -> Some n
      | WClosure _ -> None
      end
  | None -> None

let value_to_closure (v : value) (env : env) : (env * var * context * expr) option = 
  match value_to_walue v env with
  | Some w ->
      begin match w with
      | WInt _ -> None
      | WClosure(clo_env, x, c, e) -> Some(clo_env, x, c, e)
      end
  | None -> None

let rec refocus (c : context) (e : expr) (env : env) : (context * redex * env) option =
  match e with
  | EAdd(v1, v2) ->
      begin match value_to_int v1 env, value_to_int v2 env with
      | Some(n1), Some(n2) -> Some(c, RAdd(n1, n2), env)
      | _, _ -> None
      end
  | EApp(v1, v2) -> 
      begin match value_to_closure v1 env, value_to_walue v2 env with
      | Some(clo_env, x, clo_c, e), Some(w) -> Some(c, RBeta(clo_env, x, clo_c, e, w), env)
      | _, _ -> None
      end
  | ERet v -> 
      begin match c with
      | CSquare -> None
      | CLet(x, c', e, env') ->
          begin match value_to_walue v env with
          | Some w -> Some(c', RLet(x, w, e), env')
          | None -> None
          end
      | CHandle(h, c', env') ->
          begin match value_to_walue v env with
          | Some w ->
              let RetClause(x, e) = ret_clause h in
              Some(c', RHandleRet(x, e, w), env')
          | None -> None
          end
      end
  | ELet(x, e1, e2) -> refocus (CLet(x, c, e2, env)) e1 env
  | EDo(l, v) -> 
      begin match value_to_walue v env with
      | Some w ->
          begin match find_handler l c with
          | None -> None
          | Some(h, c, k, hdlr_env) -> Some(c, RHandleDo(h, k, l, w, env), hdlr_env)
          end
      | None -> None
      end
  | EHandle(h, e1) -> refocus (CHandle(h, c, env)) e1 env

let refocus ((c, e, env) : vm_state) : decomp = 
  (* print_endline (vm_state_to_string (c, e, env)); *)
  (* print_endline ""; *)
  match refocus c e env with
  | Some(c, r, env) -> Decomp(c, r, env)
  | None -> Normal(c, e, env)

let rec iterate (d : decomp) : vm_state = 
  match d with
  | Normal s -> s
  | Decomp(c, r, env) ->
      let (c', e, env') = contract c r env in
      iterate (refocus (c', e, env'))

let normalize (e : expr) : vm_state = 
  iterate (refocus (CSquare, e, Env.empty))
