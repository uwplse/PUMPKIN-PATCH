open Term
open Coqterms

type tactic = unit Proofview.tactic

(* The domain of a tactic is described by a list of type families, such that the
 * conclusion (innermost codomain) of a matching goal type must be an instance of
 * one of the given type families.
 *)
type pattern = types list

let rec applicable env typ pat =
  match kind_of_term typ with
  | Cast (trm, knd, typ) -> applicable env typ pat
  | Prod (var, dom, cod) -> applicable env cod pat
  | App (head, tail) -> applicable env head pat
  | _ -> List.exists (convertible env typ) pat

exception Register_collision
exception Tactic_failure

let registered : (string, tactic * pattern) Hashtbl.t = Hashtbl.create 16

(* Register the tactic under the given name, raising Register_collision if the
 * name is already in use.
 *)
let register_tactic name tac pat =
  if Hashtbl.mem registered name
  then raise Register_collision
  else Hashtbl.add registered name (tac, pat)

(* Remove the named tactic from the registration table, if present. *)
let unregister_tactic = Hashtbl.remove registered

(* Find the tactic registered under the given name, raising Not_found if no
 * tactic is registered under that name.
 *)
let lookup_tactic name : tactic * pattern =
  Hashtbl.find registered name

(* Find all tactics that support the given type. *)
let applicable_tactics env typ : tactic list =
  let supports _ (tac, pat) tacs =
    if applicable env typ pat then tac :: tacs else tacs
  in
  Hashtbl.fold supports registered []

(* Evaluate a tactic to solve the given goal. *)
let eval_tactic env evm typ tac : constr =
  let (ent, pv) = Proofview.init evm [(env, typ)] in
  try
    let ((), pv, (true, [], []), _) = Proofview.apply env tac pv in
    let [pf] = Proofview.partial_proof ent pv in
    assert (Proofview.finished pv);
    pf
  with _ -> raise Tactic_failure

(* Call a registered tactic to solve the given goal. *)
let call_tactic env evm typ name : constr =
  let (tac, _) = lookup_tactic name in
  eval_tactic env evm typ tac

(* Try all applicable tactics to solve the goal *)
let try_tactics env evm typ : constr option =
  let next res tac =
    match res with
    | Some _ -> res
    | None ->
      try
        Some (eval_tactic env evm typ tac)
      with Tactic_failure -> None
  in
  List.fold_left next None (applicable_tactics env typ)
