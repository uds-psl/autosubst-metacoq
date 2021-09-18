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


Import GenM.Notations GenM.

Definition up (sort: tId) (f: tId -> Binder -> nterm -> nterm) (n: list nterm) (b: Binder) : t (list nterm) :=
  substSorts <- substOf sort;;
  pure (map2 (fun p n_i => f p b n_i) substSorts n).

Definition ups (sort: tId) (f: string -> Binder -> nterm -> nterm) := m_fold_left (up sort f).

Definition succ_ (n: nterm) (z: string) (b: Binder) :=
  match b with
  | Single x => if eqb z x
               then nApp (nRef "S") [n] else n
  end.

Definition upScope (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (n: nterm) => succ_ n z b) terms binders.

Definition upRen (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (xi: nterm) => nApp (nRef (upRenName z b)) [ xi ]) terms binders.

(* TODO rename *)
Definition upSubstS (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (sigma: nterm) => nApp (nRef (upName z b)) [ sigma ]) terms binders.

Definition up' (x: string) (f: tId -> Binder -> nterm -> t nterm) (n: list nterm) (b: Binder) : t (list nterm) :=
  substSorts <- substOf x;;
  a_map (fun '(p, n_i) => f p b n_i) (combine substSorts n).

Definition upEq (sort: tId) (binders: list Binder) (terms: list nterm) (f: tId -> Binder -> nterm -> t nterm) :=
  m_fold_left (up' sort f) terms binders.

Definition upSubstScope (sort: tId) (binders: list Binder) (ss: substScope) :=
  match ss with
  | SubstScope ns nts => fmap (fun nts => SubstScope ns nts) (upScope sort binders nts)
  end.
Definition upSubst (sort: tId) (binders: list Binder) (st: substTy) :=
  match st with
  | SubstRen nts => fmap (fun nts => SubstRen nts) (upRen sort binders nts)
  | SubstSubst nts => fmap (fun nts => SubstSubst nts) (upSubstS sort binders nts)
  | SubstEq nts f => fmap (fun nts => SubstEq nts f) (upEq sort binders nts f)
  end.

Definition cast (sort sort': tId) (nts: list nterm) :=
  substSorts <- substOf sort;;
  substSorts' <- substOf sort';;
  pure (List.fold_right (fun '(x, v) ws => if list_mem x substSorts' then v :: ws else ws)
                        [] (combine substSorts nts)).

Definition castSubstScope (sort sort': tId) (ss: substScope) :=
  match ss with
  | SubstScope ns nts => fmap (fun nts => SubstScope ns nts) (cast sort sort' nts)
  end.
Definition castSubst (sort sort': tId) (st: substTy) :=
  match st with
  | SubstRen nts => fmap (fun nts => SubstRen nts) (cast sort sort' nts)
  | SubstSubst nts => fmap (fun nts => SubstSubst nts) (cast sort sort' nts)
  | SubstEq nts f => fmap (fun nts => SubstEq nts f) (cast sort sort' nts)
  end.

Definition castUpSubstScope (sort: tId) (binders: list Binder) (sort': tId) (ss: substScope) : t substScope :=
  ss' <- castSubstScope sort sort' ss;;
  upSubstScope sort' binders ss'.
Definition castUpSubst (sort: tId) (binders: list Binder) (sort': tId) (st: substTy) : t substTy :=
  st' <- castSubst sort sort' st;;
  upSubst sort' binders st'.
