Require Import String List.
Import ListNotations.

From ASUB Require Import Nterm Language GenM Utils Names.


Inductive substScope := SubstScope : list string -> list nterm -> substScope.
Inductive substTy : Type :=
| SubstRen : list nterm -> substTy
| SubstSubst : list nterm -> substTy
| SubstEq : list nterm -> (string -> Binder -> nterm -> GenM.t nterm) -> substTy.

Definition ss_terms (is_wellscoped: bool) (ss: substScope) :=
  if is_wellscoped
  then match ss with SubstScope _ xs => xs end
  else [].

Definition ss_terms_all (ss: substScope) :=
  match ss with SubstScope _ xs => xs end.

Definition ss_names (ss: substScope) :=
  match ss with SubstScope names _ => names end.
                                    
  
Definition sty_terms (st: substTy) :=
  match st with
  | SubstRen nts => nts
  | SubstSubst nts => nts
  | SubstEq nts _ => nts
  end.


