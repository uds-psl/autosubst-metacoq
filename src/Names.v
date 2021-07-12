Require Import String List.
Import ListNotations.
Open Scope string.

Definition separator := "_".
Definition sep x y := x ++ separator ++ y.
Fixpoint sepd xs :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: xs => sep x (sepd xs)
  end.

Definition varConstrName x := sep "var" x.
