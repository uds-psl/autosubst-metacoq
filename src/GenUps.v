Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
From ASUB Require Import Language Utils Flags.

(** * Generate all the liftings (\fatarrow^y_x) for all pairs of sorts in the current component.
 ** So that we can later build the lifting functions
 ** e.g. "X_ty_ty", "X_ty_vl" etc. *)
Definition getUps (component: list tId) (remove: list (tId * tId)) (sc: scope_type) : list (tId * tId) * list (Binder * tId) :=
  let cart := cartesian_product component component in
  let cart := list_diff_prod cart remove in
  let singles := map (fun '(x, y) => (Single x, y)) cart in
  let blists := map (fun '(x, y) => (BinderList "p" x, y)) cart in
  match sc with
  | Unscoped => (cart, singles)
  | Wellscoped => (cart, List.app singles blists)
  end.

