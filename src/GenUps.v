Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
From ASUB Require Import Language Utils Flags.

(** * Generate all the liftings (\fatarrow^y_x) for all pairs of sorts in the given substitution vector.
 ** So that we can later build the lifting functions
 ** e.g. "X_ty_ty", "X_ty_vl" etc. *)
Definition getUps (substSorts: list tId) (remove: list (tId * tId)) (sc: scope_type) : list (tId * tId) * list (Binder * tId) :=
  let cart := cartesian_product substSorts substSorts in
  let cart := list_diff_prod cart remove in
  let singles := map (fun '(x, y) => (Single x, y)) cart in
  let blists := map (fun '(x, y) => (BinderList "p" x, y)) cart in
  match sc with
  | Unscoped => (cart, singles)
  | Wellscoped => (cart, List.app singles blists)
  end.

From ASUB Require Import GenM.
Import GenM.Notations GenM.

Definition getUps' (_: unit) : GenM.t (list (list (Binder * tId))) :=
  sc <- get_scope_type;;
  components <- asks (fun x => x.(R_sig).(sigComponents));;
  substSortsByComponent <- a_map (fun c => substOf (NEList.hd c)) components;;
  let '(_, upsByComponent) :=
    List.fold_left (fun '(doneUps, ups) substSorts =>
                      let '(newDoneUps, newUps) := getUps substSorts doneUps sc in
                      (List.app doneUps newDoneUps, List.app ups [newUps]))
                   substSortsByComponent
                   ([], []) in
  pure upsByComponent.

Definition getUpsPure (_: unit) : GenM.t (list (list (tId * tId))) :=
  components <- asks (fun x => x.(R_sig).(sigComponents));;
  substSortsByComponent <- a_map (fun c => substOf (NEList.hd c)) components;;
  let '(_, upsByComponent) :=
    List.fold_left (fun '(doneUps, ups) substSorts =>
                      let '(newDoneUps, _) := getUps substSorts doneUps Unscoped in
                      (List.app doneUps newDoneUps, List.app ups [newDoneUps]))
                   substSortsByComponent
                   ([], []) in
  pure upsByComponent.
