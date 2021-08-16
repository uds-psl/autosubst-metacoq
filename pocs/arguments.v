Require Import List.
Import ListNotations.

Inductive A := A0 : A.
Inductive B := B0 : B.
Inductive C := cA :> A -> C | cB :> B -> C.

Definition foo (l: list C) : unit := tt.

Check (A0 : C).

Fail Check foo [A0; B0].

Arguments cons {_} & _ _.

Check foo [A0; B0].

Arguments cons : clear bidirectionality hint.

Fail Check foo [A0; B0].
