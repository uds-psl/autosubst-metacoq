Require Import String List.
From ASUB Require Import GallinaGen Language GenM.


Inductive SubstTy : Type :=
| SubstScope : list string -> list nterm -> SubstTy
| SubstRen : list nterm -> SubstTy
| SubstSubst : list nterm -> SubstTy
| SubstEq : list nterm -> (string -> Binder -> nterm -> GenM.t nterm) -> SubstTy.

Definition sty_terms (st: SubstTy) :=
  match st with
  | SubstScope _ nts => nts
  | SubstRen nts => nts
  | SubstSubst nts => nts
  | SubstEq nts _ => nts
  end.
