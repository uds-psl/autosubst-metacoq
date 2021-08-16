Module test.
  Parameter R2 : Type -> Type -> Type.
  Parameter R3 : Type -> Type -> Type -> Type.
  
  Notation "A /|\ B" := (R2 A B) (at level 85, right associativity, only parsing).
  Notation "A \|/ B" := (R2 A B) (at level 90, right associativity, only parsing).

  Notation "A <|> B <*> C" := (R3 A B C) (at level 96). 
  Notation "A >> B <+> C" := (R3 A B C) (at level 96). 

  Notation "A <<> B <<> C" := (R3 A B C) (at level 97, B at next level, right associativity).
  Notation "A <<>> B <<>> C" := (R3 A B C) (at level 97, right associativity).

  Unset Printing Notations.
  Parameter A B C : Prop.
  
  Check (A \|/ B /|\ B).
  Check (B \|/ B <|> A /|\ A <*> A).
  Check (A <|> B <*> A <|> B <*> B).
  Check (A >> B <+> C).
  Check (A >> B <+> B >> C <+> A).
  Check (A <|> A <|> B <*> C <*> C).

  (* does not work when B is not next level, why? *)
  Check (A <<> B <<> C <<> A <<> B).
  (* Check (A <<>> B <<>> C <<>> A <<>> B). *)













