Goal forall P Q, P <-> Q -> P -> Q.
Proof.
  intros P Q H. Fail rewrite H.
Abort.

Require Import List.

Goal forall P Q, P <-> Q -> P -> Q.
Proof.
  intros P Q H. rewrite H. easy.
Qed.
