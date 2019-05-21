(*
 * Auxiliary functions for printing.
 *
 * Some of these implementations are incomplete right now.
 * Those pieces will show the wrong environments, so indexes will
 * appear to be incorrect.
 *)

open Format
open Names
open Univ
open Constr
open Environ
open Printer
open Utilities
open Goptions
open Declarations
open Coqterms

module CRD = Context.Rel.Declaration

(* --- Strings --- *)

(*
 * Using pp, prints directly to a string
 * TODO use this in category for as_string, to avoid extraneous envs
 *)
let print_to_string (pp : formatter -> 'a -> unit) (trm : 'a) : string =
  Format.asprintf "%a" pp trm

(* --- Coq terms --- *)

(* Gets n as a string *)
let name_as_string (n : Name.t) : string =
  match n with
  | Name id -> Id.to_string id
  | Anonymous -> "_"

(* Pretty prints a universe level *)
let print_univ_level (fmt : formatter) (l : Level.t) =
  Pp.pp_with fmt (Level.pr l)

(* Prints a universe *)
let universe_as_string u =
  match Universe.level u with
  | Some l -> print_to_string print_univ_level l
  | None -> Printf.sprintf "Max{%s}" (String.concat ", " (List.map (print_to_string print_univ_level) (LSet.elements (Universe.levels u))))

(* Gets a sort as a string *)
let sort_as_string s =
  match s with
  | Term.Prop _ -> if s = Sorts.prop then "Prop" else "Set"
  | Term.Type u -> Printf.sprintf "Type %s" (universe_as_string u)

(* Prints a term *)
let rec term_as_string (env : env) (trm : types) =
  match kind trm with
  | Rel i ->
     (try
       let (n, _, _) = CRD.to_tuple @@ lookup_rel i env in
       Printf.sprintf "(%s [Rel %d])" (name_as_string n) i
     with
       Not_found -> Printf.sprintf "(Unbound_Rel %d)" i)
  | Var v ->
     Id.to_string v
  | Meta mv ->
     failwith "Metavariables are not yet supported"
  | Evar (k, cs) ->
     Printf.sprintf "??"
  | Sort s ->
     sort_as_string s
  | Cast (c, k, t) ->
     Printf.sprintf "(%s : %s)" (term_as_string env c) (term_as_string env t)
  | Prod (n, t, b) ->
     Printf.sprintf "(Π (%s : %s) . %s)" (name_as_string n) (term_as_string env t) (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | Lambda (n, t, b) ->
     Printf.sprintf "(λ (%s : %s) . %s)" (name_as_string n) (term_as_string env t) (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | LetIn (n, trm, typ, e) ->
     Printf.sprintf "(let (%s : %s) := %s in %s)" (name_as_string n) (term_as_string env typ) (term_as_string env typ) (term_as_string (push_rel CRD.(LocalDef(n, e, typ)) env) e)
  | App (f, xs) ->
     Printf.sprintf "(%s %s)" (term_as_string env f) (String.concat " " (List.map (term_as_string env) (Array.to_list xs)))
  | Const (c, u) ->
     let ker_name = Constant.canonical c in
     KerName.to_string ker_name
  | Construct (((i, i_index), c_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     let constr_name_id = ind_body.mind_consnames.(c_index - 1) in
     Id.to_string constr_name_id
  | Ind ((i, i_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_bodies = mutind_body.mind_packets in
     let name_id = (ind_bodies.(i_index)).mind_typename in
     Id.to_string name_id
  | Case (ci, ct, m, bs) ->
     let (i, i_index) = ci.ci_ind in
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     Printf.sprintf
       "(match %s : %s with %s)"
       (term_as_string env m)
       (term_as_string env ct)
       (String.concat
          " "
          (Array.to_list
             (Array.mapi
                (fun c_i b ->
                  Printf.sprintf
                    "(case %s => %s)"
                    (Id.to_string (ind_body.mind_consnames.(c_i)))
                    (term_as_string env b))
                bs)))
  | Fix ((is, i), (ns, ts, ds)) ->
     let env_fix = push_rel_context (bindings_for_fix ns ds) env in
     String.concat
       " with "
       (map3
          (fun n t d ->
            Printf.sprintf
             "(Fix %s : %s := %s)"
             (name_as_string n)
             (term_as_string env t)
             (term_as_string env_fix d))
          (Array.to_list ns)
          (Array.to_list ts)
          (Array.to_list ds))
  | CoFix (i, (ns, ts, ds)) ->
     Printf.sprintf "TODO" (* TODO *)
  | Proj (p, c) ->
     Printf.sprintf "TODO" (* TODO *)

(* --- Coq environments --- *)

(* Gets env as a string *)
let env_as_string (env : env) : string =
  let all_relis = all_rel_indexes env in
  String.concat
    ",\n"
    (List.map
       (fun i ->
         let (n, b, t) = CRD.to_tuple @@ lookup_rel i env in
         Printf.sprintf "%s (Rel %d): %s" (name_as_string n) i (term_as_string (pop_rel_context i env) t))
       all_relis)

(* --- Debugging --- *)

(* Print a separator string *)
let print_separator unit : unit =
  Printf.printf "%s\n\n" "-----------------"

(* Debug a term *)
let debug_term (env : env) (trm : types) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (term_as_string env trm)

(* Debug a list of terms *)
let debug_terms (env : env) (trms : types list) (descriptor : string) : unit =
  List.iter (fun t -> debug_term env t descriptor) trms

(* Debug an environment *)
let debug_env (env : env) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (env_as_string env)

(* Print a patch to stdout in the standard Coq format *)
let print_patch env evm patch_id patch : unit =
  let opts = get_tables () in
  let print_all =
    match (OptionMap.find ["Printing"; "All"] opts).opt_value with
    | BoolValue b -> b
    | _ -> true
  in
  let _ = set_bool_option_value ["Printing"; "All"] true in
  Pp.pp_with
    Format.std_formatter
    (Pp.pr_sequence
       id
       [(Pp.str "\nBEGIN PATCH");
        (Pp.str patch_id);
        (Pp.str "\nDefinition");
        (Pp.str patch_id);
        (Pp.str ":=");
        (pr_lconstr_env env evm patch);
        (Pp.str ".\nEND PATCH");
        (Pp.str "\n")]);
  set_bool_option_value ["Printing"; "All"] print_all
