From ASUB Require Import importfile1.

(* ssreflect rewrite due to List import is transitive *)
Goal forall P Q, P <-> Q -> P -> Q.
Proof.
  intros P Q H. rewrite H. easy.
Qed.
