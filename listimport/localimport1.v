Require List. 

Module proofs.

  Goal forall P Q, P <-> Q -> P -> Q.
    intros P Q H. rewrite H. easy.
  Qed.

End proofs.
