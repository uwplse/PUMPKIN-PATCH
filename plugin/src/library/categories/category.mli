(* A super simple interface for small categories. *)
(* TODO clean, given additions of functor and so on *)

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

module Category (Object : Opaque) (Morphism : Opaque):
sig
  type cat

  type obj = Object.t
  type morph = Morphism.t

  val make : obj list -> (obj * morph * obj) list -> obj option -> obj option -> cat

  type arrow = (obj * morph * obj)
  type arr =
    Identity of obj
  | Composite of arr * arr
  | Primitive of arrow

  val domain : arr -> obj
  val codomain : arr -> obj
  val compose : arr -> arr -> arr option
  val identity : obj -> arr
  val between : cat -> obj -> obj -> arrow list (* primitive morphisms only *)
  val objects : cat -> obj list
  val morphisms : cat -> arrow list (* primitive morpshism only *)
  val initial : cat -> obj option
  val terminal : cat -> obj option

  val as_string : cat -> string
end

module Functor (Dom : CatT) (Cod : CatT):
sig
  type f_obj = Dom.obj -> Cod.obj
  type f_arr = Dom.arrow -> Cod.arrow
  type f_iterm = Dom.obj option -> Cod.obj option
  type t = Fun of f_obj * f_arr * f_iterm * f_iterm

  val make : f_obj -> f_arr -> t
  val make_with_it : f_obj -> f_arr -> f_iterm -> f_iterm -> t
  val f_O : t -> f_obj
  val f_A : t -> f_arr
  val f_I : t -> f_iterm
  val f_T : t -> f_iterm
  val apply : t -> Dom.cat -> Cod.cat
  val as_string : t -> string
end

