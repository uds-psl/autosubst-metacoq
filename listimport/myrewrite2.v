
Require List.

From ASUB Require Import myrewrite1.

(* it also changes semantics of a rewrite inside another tactic imported from another module. *)
Goal forall P Q, P <-> Q -> P -> Q.
Proof.
  intros P Q H. rewrite H. easy.
  Restart.
  intros P Q H. myrewrite H. easy.
Qed.
