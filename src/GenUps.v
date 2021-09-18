Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
From ASUB Require Import GenM Language Utils.
Import GenM.Notations GenM.

(** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the current component.
 ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
Definition getUps (component: list tId) (remove: list (tId * tId)) : (list (tId * tId) * list (Binder * tId)) :=
  let cart := cartesian_product component component in
  let cart := list_diff_prod cart remove in
  let singles := map (fun '(x, y) => (Single x, y)) cart in
  (* let blists := map (fun '(x, y) => (BinderList ("p", x), y)) cart in *)
  (* TODO scoped append blists *)
  (cart, singles).

Module GenUpsExample_fcbv.
  Definition upList_ty :=
    let m := substSorts <- substOf "ty";;
             let '(_, upList) := getUps substSorts [] in
             pure upList in
    match testrun m with
    | inl _ => []
    | inr (_, _, x) => x
    end.

  Definition upList_tm :=
    let m := substSorts_ty <- substOf "ty";;
             substSorts <- substOf "tm";;
             let '(combinations, _) := getUps substSorts_ty [] in
             let '(_, upList) := getUps substSorts combinations in
             pure upList in
    match testrun m with
    | inr (_, _, x) => x
    | _ => []
    end.
End GenUpsExample_fcbv.
