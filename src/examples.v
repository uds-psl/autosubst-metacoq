Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.

From ASUB Require Import Autosubst ErrorM CustomEntryParser Language Flags TemplateMonadUtils.
From ASUB Require Import core fintype.
Import SyntaxNotation.


Definition utlc : autosubstLanguage :=
  {| al_sorts := <{ tm : Type }>;
     al_ctors := {{ app : tm -> tm -> tm;
                    lam : (bind tm in tm) -> tm }} |}.

Module utlc_fintype.
  MetaCoq Run Autosubst Wellscoped for utlc.
End utlc_fintype.

Module utlc_unscoped.
  MetaCoq Run Autosubst Unscoped for utlc.
End utlc_unscoped.

Definition stlc : autosubstLanguage :=
  {| al_sorts := <{ ty : Type;
                    tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    app : tm -> tm -> tm;
                    lam : ty -> (bind tm in tm) -> tm }} |}.

Module stlc_fintype.
  MetaCoq Run Autosubst Wellscoped for stlc.
End stlc_fintype.

Module stlc_unscoped.
  MetaCoq Run Autosubst Unscoped for stlc.
End stlc_unscoped.


Definition fcbv : autosubstLanguage :=
  {| al_sorts := <{ ty : Type;
                    tm : Type;
                    vl : Type }>;
    al_ctors := {{ arr : ty -> ty -> ty;
                   all : (bind ty in ty) -> ty;
                   app : tm -> tm -> tm;
                   tapp : tm -> ty -> tm;
                   vt : vl -> tm;
                   lam : ty -> (bind vl in tm) -> vl;
                   tlam : (bind ty in tm) -> vl }} |}.

Module fcbv_fintype.
  (* TODO somehow takes 3 minutes *)
  Time MetaCoq Run Autosubst Wellscoped for fcbv.
End fcbv_fintype.

Module fcbv_unscoped.
  Time MetaCoq Run Autosubst Unscoped for fcbv.
End fcbv_unscoped.

Definition pi : autosubstLanguage :=
  {| al_sorts := <{ chan : Type;
                    proc : Type }>;
     al_ctors := {{ Nil : proc;
                    Bang : proc -> proc;
                    Res : (bind chan in proc) -> proc;
                    Par : proc -> proc -> proc;
                    In : chan -> (bind chan in proc) -> proc;
                    Out : chan -> chan -> proc -> proc }} |}.

Module pi_fintype.
  MetaCoq Run Autosubst Wellscoped for pi.
End pi_fintype.

Module pi_unscoped.
  MetaCoq Run Autosubst Unscoped for pi.
End pi_unscoped.

Definition num : autosubstLanguage :=
  {| al_sorts := <{ tm : Type;
                    nat : Type }>;
     al_ctors := {{ const : nat -> tm;
                    Plus : tm -> tm -> tm;
                    app : tm -> tm -> tm;
                    lam : (bind tm in tm) -> tm }} |}.

Module num_fintype.
  MetaCoq Run Autosubst Wellscoped for num.
End num_fintype.

Module num_unscoped.
  MetaCoq Run Autosubst Unscoped for num.
End num_unscoped.

Definition fol : autosubstLanguage :=
  {| al_sorts := <{ term : Type;
                    form : Type }>;
     al_ctors := {{ Func (f : nat) : codF (fin f) (term) -> term;
                    Fal : form;
                    Pred (p : nat) : codF (fin p) (term) -> form;
                    Impl : form -> form -> form;
                    Conj : form -> form -> form;
                    Disj : form -> form -> form;
                    All : (bind term in form) -> form;
                    Ex : (bind term in form) -> form }} |}.

Module fol_fintype.
  (* From ASUB Require Import core fintype. *)
  Import TemplateMonadNotations.

  Inductive term (n_term : nat) : Type :=
  | var_term : fin n_term -> term n_term
  | Func : forall (f : nat), (cod (fin f) (term n_term)) -> term n_term.
  Inductive form (n_term : nat) : Type :=
  | Fal : form n_term
  | Pred : forall p : nat, cod (fin p) (term n_term) -> form n_term
  | Impl : form n_term -> form n_term -> form n_term
  | Conj : form n_term -> form n_term -> form n_term
  | Disj : form n_term -> form n_term -> form n_term
  | All : form (S n_term) -> form n_term
  | Ex : form (S n_term) -> form n_term.

  MetaCoq Run (translate_signature fol >>= fun sig => tmPrint (getIndCtorNames sig)).

  MetaCoq Run AutosubstNoInd Wellscoped for fol.
End fol_fintype.
      
Definition variadic : autosubstLanguage :=
  {| al_sorts := <{ tm : Type  }>;
     al_ctors := {{ app : tm -> listF (tm) -> tm;
                    lam (p: nat) : (bind <p, tm> in tm) -> tm }} |}.

Module variadic_fintype.

  Inductive tm (n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_tm
  | app : tm n_tm -> list (tm n_tm) -> tm n_tm
  | lam : forall p : nat, tm (plus p n_tm) -> tm n_tm.

  (* TODO method not implemented *)
  (* MetaCoq Run AutosubstNoInd Wellscoped for variadic. *)
End variadic_fintype.

Module variadic_unscoped.

  (* TODO still uses some _list_ lemma *)
  (* MetaCoq Run Autosubst Unscoped for variadic. *)
End variadic_unscoped.

(* XXX lower-case lambda does not work as a Coq identifier. But apparently this approach works with all identifiers, e.g. upper-case lambda *)
Definition unicode : autosubstLanguage :=
  {| al_sorts := <{ ty : Type; tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    アップ : tm -> tm -> tm;
                    Λ : ty -> (bind tm in tm) -> tm }} |}.

Module unicode_fintype.
  MetaCoq Run Autosubst Wellscoped for unicode.
End unicode_fintype.

Module unicode_unscoped.
  MetaCoq Run Autosubst Unscoped for unicode.
End unicode_unscoped.
