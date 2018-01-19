(* --- Type definitions for tactic-based automation --- *)

open Term

type tactic = unit Proofview.tactic

(* The domain of a tactic is described by a list of types, such that a matching
 * goal type must be constructed only with types given in this list.
 *
 * TODO: We should probably distinguish between tactics that tolerate/require
 *       introduction of all hypotheses and those that are sensitive to it.
 * TODO: We really need a more sophisticated pattern language that can express
 *       restrictions such as a list of an arbitrary type.
 *)
type pattern = types list

(* TODO: This is currently dummy code. *)
let applicable pat typ =
  match kind_of_term typ with
  | Cast (trm, knd, typ) -> true
  | Prod (var, dom, cod) -> true
  | Lambda (var, typ, trm) -> true
  | LetIn (var, trm, typ, body) -> true
  | App (func, arg) -> true
  | Const con -> true
  | Ind ind -> true
  | Construct con -> true
  | Case (info, dis, ret, brs) -> true
  | Fix (trm, typ) -> true
  | CoFix (trm, typ) -> true
  | Proj (pr, trm) -> true
  | _ -> true

exception Name_collision

let registered : (string, tactic * pattern) Hashtbl.t = Hashtbl.create 16

(* Register the tactic under the given name, raising Name_collision if the name
 * is already in use.
 *)
let register_tactic name tac pat =
  if Hashtbl.mem registered name
  then raise Name_collision
  else Hashtbl.add registered name (tac, pat)

(* Find the tactic registered under the given name, raising Not_found if no
 * tactic is registered under that name.
 *)
let lookup_tactic name : tactic * pattern =
  Hashtbl.find registered name

(* Find all tactics that support the given type. *)
let applicable_tactics typ : tactic list =
  let supports _ (tac, pat) tacs =
    if applicable pat typ then tac :: tacs else tacs
  in
  Hashtbl.fold supports registered []
