
Require Import Structures.OrderedTypeEx List String.
Import ListNotations.
Require Export FSets.FMapList.

Module M := FMapList.Make String_as_OT.

(* a.d. todo, no guarantees about overwriting but I think I only use it for constructing test data *)
Fixpoint fromList {elt : Type} (A: list (string * elt)) : M.t elt :=
  match A with
  | [] => M.empty _
  | (k, v) :: A => M.add k v (fromList A)
  end.
