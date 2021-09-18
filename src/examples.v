Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From ASUB Require Import Autosubst.

Definition utlc : autosubstLanguage :=
  {| al_sorts := <{ tm : Type }>;
     al_ctors := {{ app : tm -> tm -> tm;
                    lam : (bind tm in tm) -> tm }} |}.

Module m1.
  MetaCoq Run Autosubst Wellscoped for utlc.
End m1.

Definition stlc : autosubstLanguage :=
  {| al_sorts := <{ ty : Type;
                    tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    app : tm -> tm -> tm;
                    lam : ty -> (bind tm in tm) -> tm }} |}.

Module m2.
  MetaCoq Run Autosubst Wellscoped for stlc.
End m2.

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

From ASUB Require Import ErrorM.
Module m3.
  Compute (ErrorM.run (translate_signature fcbv) tt tt).
  Time MetaCoq Run Autosubst Wellscoped for fcbv.
End m3.

Definition pi : autosubstLanguage :=
  {| al_sorts := <{ chan : Type;
                    proc : Type }>;
     al_ctors := {{ Nil : proc;
                    Bang : proc -> proc;
                    Res : (bind chan in proc) -> proc;
                    Par : proc -> proc -> proc;
                    In : chan -> (bind chan in proc) -> proc;
                    Out : chan -> chan -> proc -> proc }} |}.

Module m4.
  Compute (ErrorM.run (translate_signature pi) tt tt).
  MetaCoq Run Autosubst Wellscoped for pi.
End m4.

Definition num : autosubstLanguage :=
  {| al_sorts := <{ tm : Type;
                    nat : Type }>;
     al_ctors := {{ const : nat -> tm; 
                    Plus : tm -> tm -> tm }} |}.

Definition fol : autosubstLanguage :=
  {| al_sorts := <{ term : Type;
                    form : Type }>;
     al_ctors := {{ Func (f : nat) : cod (fin f) (term) -> term;
                    Fal : form;
                    Pred (p : nat) : cod (fin p) (term) -> form;
                    Impl : form -> form -> form;
                    Conj : form -> form -> form;
                    Disj : form -> form -> form;
                    All : (bind term in form) -> form;
                    Ex : (bind term in form) -> form }} |}.

Module m6.
  Compute (ErrorM.run (translate_signature fol) tt tt).
  (* MetaCoq Run Autosubst Wellscoped for fol. *)
End m6.

Definition variadic : autosubstLanguage :=
  {| al_sorts := <{ tm : Type  }>;
     al_ctors := {{ app : tm -> list (tm) -> tm;
                    lam (p: nat) : (bind <p, tm> in tm) -> tm }} |}.

(* XXX lower-case lambda does not work as a Coq identifier. But apparently this approach works with all identifiers, e.g. upper-case lambda *)
Definition unicode : autosubstLanguage :=
  {| al_sorts := <{ ty : Type; tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    アップ : tm -> tm -> tm;
                    Λ : ty -> (bind tm in tm) -> tm }} |}.
