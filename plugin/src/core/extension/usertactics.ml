open Term
open Coqterms

type tactic = unit Proofview.tactic

(* A tactic entry is the pair of a tactic and the list of supported conclusion
 * type families, such that a supported goal is one with a conclusion that is an
 * application of a form in this list.
 *)
type tactic_entry = tactic * types list

exception Tactic_failure

(* NOTE: This still isn't a robust approach, really.
 * TODO: Check conclusion term from the inside out, to support
 * partially applied forms like [(@eq Z)] in a tactic entry's
 * support conclusions.
 *)
let rec matches env typ typ0 =
  match kind_of_term typ with
  | Cast (trm, knd, typ) -> matches env typ typ0
  | Prod (var, dom, cod) -> matches env cod typ0
  | App (head, tail) -> matches env head typ0
  | _ -> convertible env typ typ0

let registry : tactic_entry Registry.registry = Registry.create ()

let register_tactic key tac typs =
  Registry.register registry key (tac, typs)

let unregister_tactic = Registry.unregister registry

let lookup_tactic = Registry.lookup registry

(* Find all tactics that support the given type. *)
let find_tactics env typ : tactic list =
  let pred (_, typs) = List.exists (matches env typ) typs in
  List.map (fun (tac, _) -> tac) (Registry.filter registry pred)

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
  List.fold_left next None (find_tactics env typ)
