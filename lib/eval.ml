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

type pure_frame = FLet of var * expr * env
and pure_context = pure_frame list

and handle_frame = FHandle of handler * env

and eff_frame = handle_frame * pure_context
and context = eff_frame list

(* Redexes *)

and redex = 
  | RAdd of int * int
  | RBeta of var * expr * env * walue
  | RLet of var * expr * env * walue
  | RHandleRet of var * expr * env * walue
  | RHandleDo of handler * context * label * env * walue (* context is reversed to have easy access to the active handler *)
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
let rec plug_pure (c : pure_context) (e : expr) : expr = 
  match c with
  | [] -> e
  | FLet(x, e', _) :: c' -> plug_pure c' (ELet(x, e, e'))

let rec plug (c : context) (e : expr) : expr = 
  match c with
  | [] -> e
  | (FHandle(h, _), pure_c) :: c' -> plug c' (EHandle(h, (plug_pure pure_c e)))

let vm_state_to_string ((c, e, env) : vm_state) : string = 
  Env.to_string walue_to_string env ^ (plug c e |> Utils.expr_to_string)

let contract (c : context) (r : redex) : vm_state = 
  match r with
  | RAdd(n1, n2) -> c, ERet (VInt (n1 + n2)), Env.empty
  | RBeta(x, e, env, w) | RLet(x, e, env, w) | RHandleRet(x, e, env, w) -> c, e, Env.extend x w env
  | RContApp(c', w) -> c' @ c, (ERet (VVar "cont_arg")), Env.empty |> Env.extend "cont_arg" w
  | RHandleDo(h, c_local, l, env, w) ->
      let (OpClause(_, y, k, e)) = List.find (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) in
      c, e, env |> Env.extend y w |> Env.extend k (WCont (List.rev c_local))

let rec find_handler (l : label) (c : context) (res_c : context) : (handler * context * context * env) option = 
  match c with
  | [] -> None
  | ((FHandle(h, env), _) as eff_frame) :: c' -> 
      begin match List.find_opt (fun (OpClause(l', _, _, _)) -> l = l') (op_clauses h) with
      | Some _ -> Some(h, c', eff_frame :: res_c, env)
      | None -> find_handler l c' (eff_frame :: res_c)
      end

let find_handler (l : label) (c : context) : (handler * context * context * env) option = 
  find_handler l c []

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
      | [] -> None
      | (FHandle(h, env'), []) :: c' -> 
          let RetClause(x, e) = ret_clause h in
          begin match value_to_walue v env with
          | Some w -> Some(c', RHandleRet(x, e, env', w))
          | None -> None
          end
      | (handle_f, FLet(x, e, env') :: pure_c) :: c' ->
          begin match value_to_walue v env with
          | Some w -> Some((handle_f, pure_c) :: c', RLet(x, e, env', w))
          | None -> None
          end
      end
  | ELet(x, e1, e2) ->
      begin match c with
      | [] -> failwith "top handler should guard us"
      | (handle_f, pure_c) :: c' ->
          refocus ((handle_f, FLet(x, e2, env) :: pure_c) :: c') e1 env
      end
  | EDo(l, v) -> 
      begin match value_to_walue v env with
      | Some w ->
          begin match find_handler l c with
          | None -> None
          | Some(h, c, k, hdlr_env) -> Some(c, RHandleDo(h, k, l, hdlr_env, w))
          end
      | None -> None
      end
  | EHandle(h, e1) -> refocus ((FHandle(h, env), []) :: c) e1 env

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

let init_context = [FHandle(Handler(RetClause("x", ERet(VVar "x")), []), Env.empty), []]

let normalize (e : expr) : vm_state = 
  iterate (refocus (init_context, e, Env.empty))
