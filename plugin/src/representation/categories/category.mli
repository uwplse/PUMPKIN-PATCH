(* An interface for small categories with state *)
(* Will go away at some point soon (not bothering to clean!) *)

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

module Category (Object : Opaque) (Morphism : Opaque):
sig
  type cat

  type obj = Object.t
  type morph = Morphism.t

  val make : obj list -> (obj * morph * obj) list -> obj option -> obj option -> evar_map -> cat state

  type arrow = (obj * morph * obj)
  type arr =
    Identity of obj
  | Composite of arr * arr
  | Primitive of arrow

  val domain : arr -> obj
  val codomain : arr -> obj
  val compose : arr -> arr -> arr option
  val identity : obj -> arr
  val between : cat -> obj -> obj -> evar_map -> (arrow list) state (* primitive morphisms only *)
  val objects : cat -> evar_map -> (obj list) state
  val morphisms : cat -> arrow list (* primitive morpshism only *)
  val initial : cat -> obj option
  val terminal : cat -> obj option

  val as_string : cat -> evar_map -> string
end

module Functor (Dom : CatT) (Cod : CatT):
sig
  type f_obj = Dom.obj -> evar_map -> Cod.obj state
  type f_arr = Dom.arrow -> evar_map -> Cod.arrow state
  type f_iterm = Dom.obj option -> evar_map -> (Cod.obj option) state
  type t = Fun of f_obj * f_arr * f_iterm * f_iterm

  val make : f_obj -> f_arr -> evar_map -> t state
  val make_with_it : f_obj -> f_arr -> f_iterm -> f_iterm -> t
  val f_O : t -> f_obj
  val f_A : t -> f_arr
  val f_I : t -> f_iterm
  val f_T : t -> f_iterm
  val apply : t -> Dom.cat -> evar_map -> Cod.cat state
  val as_string : t -> string
end

