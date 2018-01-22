(* --- Common wrapper for Hash tables --- *)

type 'a registry = (string, 'a) Hashtbl.t

exception Registry_collision

(* Create a new extension registry with an initial capacity. *)
let create ?size:(size=16) () : 'a registry =
  Hashtbl.create size

(* Register the item under the given key, raising Registry_collision if the
 * name is already in use.
 *)
let register reg key item =
  if Hashtbl.mem reg key
  then raise Registry_collision
  else Hashtbl.add reg key item

(* Remove the key from the registration table, if present. *)
let unregister = Hashtbl.remove

(* Find the item registered under the given key, raising Not_found if no
 * item is registered under that name.
 *)
let lookup = Hashtbl.find

(* Find all items in the registry that satisfy a predicate. *)
let filter reg pred =
  let check key obj items =
    if pred obj then obj :: items else items
  in
  Hashtbl.fold check reg []
