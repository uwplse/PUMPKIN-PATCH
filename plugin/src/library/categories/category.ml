(* A super simple representation for small categories. *)

open Collections

module type Opaque =
sig
  type t
  val as_string : t -> string
  val equal : t -> t -> bool
end

module type CatT =
sig
  type obj
  type morph
  type cat
  type arrow = (obj * morph * obj)

  val objects : cat -> obj list
  val morphisms : cat -> arrow list
  val make : obj list -> arrow list -> obj option -> obj option -> cat
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
    Identity of obj
  | Composite of arr * arr
  | Primitive of arrow

  let make objects morphisms i t =
    let aux obj l (dom, mor, cod) =
      if Object.equal obj dom then ((mor, cod) :: l) else l
    in
    let cs =
      List.map
        (fun obj -> (obj, List.fold_left (aux obj) [] morphisms))
        objects
    in Category (cs, i, t)

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
    List.map (fun (mor, _) -> (dom, mor, cod))
      (List.filter (fun (_, obj) -> Object.equal obj cod)
        (snd (List.find (fun adj -> Object.equal (fst adj) dom) cl)))

  let objects c =
    match c with
      Category (cl, i, t) ->
        let os = List.map fst cl in
        let append_initial_terminal it os =
          if Option.has_some it then
            let ito = Option.get it in
            if List.exists (fun o -> Object.equal o ito) os then os else ito :: os
          else os
        in append_initial_terminal t (append_initial_terminal i os)

  let morphisms (Category (cs, _, _)) =
    flat_map (fun (s, adjs) -> (List.map (fun (m, d) -> (s, m, d)) adjs)) cs

  let initial (Category (_, i, _)) = i

  let terminal (Category (_, _, t)) = t

  let morphism_as_string (src, m, dst) =
    Printf.sprintf "(%s, %s, %s)" (Object.as_string src) (Morphism.as_string m) (Object.as_string dst)

  let as_string cat =
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
      (String.concat ",\n" (List.map Object.as_string (objects cat)))
      (String.concat ",\n" (List.map morphism_as_string (morphisms cat)))
      (initial_terminal_as_string (initial cat))
      (initial_terminal_as_string (terminal cat))
end


module Functor (Dom : CatT) (Cod : CatT) =
struct
  type f_obj = Dom.obj -> Cod.obj
  type f_arr = Dom.arrow -> Cod.arrow
  type f_iterm = Dom.obj option -> Cod.obj option
  type t = Fun of f_obj * f_arr * f_iterm * f_iterm

  let make (f_o : f_obj) (f_a : f_arr) =
    let f_it = Option.map f_o in
    Fun (f_o, f_a, f_it, f_it)

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

  let apply (f : t) (c : Dom.cat) =
    let f_o = f_O f in
    let f_a = f_A f in
    let os = List.map f_o (Dom.objects c) in
    let ms = List.map f_a (Dom.morphisms c) in
    let i = (f_I f) (Dom.initial c) in
    let t = (f_T f) (Dom.terminal c) in
    Cod.make os ms i t

  let as_string (f : t) =
    failwith "TODO"
end


