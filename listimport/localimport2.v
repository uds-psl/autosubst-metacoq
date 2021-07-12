
Check list.
Fail Check List.map.

From ASUB Require localimport1.

(* just a require without import already changes the behavior of rewrite *)
Goal forall P Q, P <-> Q -> P -> Q.
Proof.
  intros P Q H. rewrite H. easy.
Qed.

