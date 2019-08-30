(* A representation for small categories with state *)
(* Will go away at some point soon (not bothering to clean!) *)

open Utilities
open Stateutils
open Evd

module type Opaque =
sig
  type t
  val as_string : t -> string
  val equal : t -> t -> evar_map -> bool state
end

module type CatT =
sig
  type obj
  type morph
  type cat
  type arrow = (obj * morph * obj)

  val objects : cat -> evar_map -> (obj list) state
  val morphisms : cat -> arrow list
  val make : obj list -> arrow list -> obj option -> obj option -> evar_map -> cat state
  val initial : cat -> obj option
  val terminal : cat -> obj option
end

module Category (Object : Opaque) (Morphism : Opaque) =
struct
  type obj = Object.t
  type morph = Morphism.t

  (* Reimplementation of adjacency list for primitive morphisms *)
  type cat_list = (obj * (morph * obj) list) list

  (* A category has an optional initial and terminal object,
     which we don't explicitly represent with morphisms for obvious reasons *)
  type cat = Category of cat_list * obj option * obj option

  type arrow = (obj * morph * obj)
  type arr =
  | Identity of obj
  | Composite of arr * arr
  | Primitive of arrow

  let make (objects : Object.t list) morphisms i t =
    let aux obj l (dom, mor, cod) =
      branch_state
        (Object.equal obj)
        (fun _ -> ret ((mor, cod) :: l))
        (fun _ -> ret l)
        dom
    in
    bind
      (map_state
        (fun obj ->
          bind
            (fold_left_state (aux obj) [] morphisms)
            (fun ms -> ret (obj, ms)))
        objects)
      (fun cs -> ret (Category (cs, i, t)))

  (* Operations about morphisms *)
  let rec domain f =
    match f with
    | Identity a -> a
    | Composite (g, _) -> domain g
    | Primitive (a, _, _) -> a

  let rec codomain f =
    match f with
    | Identity a -> a
    | Composite (_, h) -> codomain h
    | Primitive (_, _, b) -> b

  let compose f g = (* f o g *)
    if domain f <> codomain g
    then None
    else
      match (f, g) with (* NOTE: Should we reduce away identity morphisms...? *)
      | (_, Identity _) -> Some f
      | (Identity _, _) -> Some g
      | (_, _) -> Some (Composite (f, g))

  let identity a =
    Identity a

  let between (Category (cl, _, _)) dom cod =
    bind
      (find_state (fun adj -> Object.equal (fst adj) dom) cl)
      (fun adj ->
        bind
          (filter_state (fun (_, obj) -> Object.equal obj cod) (snd adj))
          (map_state (fun (mor, _) -> ret (dom, mor, cod))))

  let objects c =
    match c with
      Category (cl, i, t) ->
        let os = List.map fst cl in
        let append_initial_terminal it os =
          if Option.has_some it then
            let ito = Option.get it in
            branch_state
              (exists_state (fun o -> Object.equal o ito))
              ret
              (fun os -> ret (ito :: os))
              os
          else
            ret os
        in bind (append_initial_terminal i os) (append_initial_terminal t)

  let morphisms (Category (cs, _, _)) =
    flat_map (fun (s, adjs) -> (List.map (fun (m, d) -> (s, m, d)) adjs)) cs

  let initial (Category (_, i, _)) = i

  let terminal (Category (_, _, t)) = t

  let morphism_as_string (src, m, dst) =
    Printf.sprintf "(%s, %s, %s)" (Object.as_string src) (Morphism.as_string m) (Object.as_string dst)

  let as_string cat sigma =
    (* For now, string representation for debugging *)
    (*failwith "TODO: repurpose graphviz serialization"*)
    let initial_terminal_as_string it =
      if Option.has_some it then
        Printf.sprintf "Some %s" (Object.as_string (Option.get it))
      else
        "None"
    in
    Printf.sprintf
      "Objects:\n%s\n\nMorphisms:\n%s\n\nInitial:\n%s\n\nTerminal:\n%s\n"
      (String.concat ",\n" (List.map Object.as_string (snd (objects cat sigma))))
      (String.concat ",\n" (List.map morphism_as_string (morphisms cat)))
      (initial_terminal_as_string (initial cat))
      (initial_terminal_as_string (terminal cat))
end


module Functor (Dom : CatT) (Cod : CatT) =
struct
  type f_obj = Dom.obj -> evar_map -> Cod.obj state
  type f_arr = Dom.arrow -> evar_map -> Cod.arrow state
  type f_iterm = Dom.obj option -> evar_map -> (Cod.obj option) state
  type t = Fun of f_obj * f_arr * f_iterm * f_iterm

  let make (f_o : f_obj) (f_a : f_arr) =
    let f_it : f_iterm =
      fun o sigma ->
      match Option.map (fun o -> f_o o sigma) o with
      | Some (sigma, o') ->
         ret (Some o') sigma
      | None ->
         ret None sigma
    in ret (Fun (f_o, f_a, f_it, f_it))

  let make_with_it (f_o : f_obj) (f_a : f_arr) (f_i : f_iterm) (f_t : f_iterm) =
    Fun (f_o, f_a, f_i, f_t)

  let f_O (f : t) = match f with
    Fun (f_o, _, _, _) -> f_o

  let f_A (f : t) = match f with
    Fun (_, f_a, _, _) -> f_a

  let f_I (f : t) = match f with
    Fun (_, _, f_i, _) -> f_i

  let f_T (f : t) = match f with
    Fun (_, _, _, f_t) -> f_t

  let apply (f : t) (c : Dom.cat) sigma =
    let f_o = f_O f in
    let f_a = f_A f in
    let sigma, os = bind (Dom.objects c) (map_state f_o) sigma in
    let sigma, ms = map_state f_a (Dom.morphisms c) sigma in
    let sigma, i = (f_I f) (Dom.initial c) sigma in
    let sigma, t = (f_T f) (Dom.terminal c) sigma in
    Cod.make os ms i t sigma

  let as_string (f : t) =
    failwith "TODO"
end


