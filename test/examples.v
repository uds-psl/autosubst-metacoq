Require Import String.
(* Import ListNotations. *)
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.

From ASUB Require Import Autosubst ErrorM CustomEntryParser Language Flags TemplateMonadUtils.
Import SyntaxNotation.


(* The untyped lambda calculus. *)
Definition utlc : autosubstLanguage :=
  {| al_sorts := <{ tm : Type }>;
     al_ctors := {{ app : tm -> tm -> tm;
                    lam : (bind tm in tm) -> tm }} |}.

Module utlc_fintype.
  (* In VSCoq, the automation is printed to the "Info" channel. *)
  MetaCoq Run Autosubst Wellscoped for utlc.
  Print tm.
End utlc_fintype.

Module utlc_unscoped.
  MetaCoq Run Autosubst Unscoped for utlc.
  Print tm.
  From ASUB Require Import core core_axioms unscoped unscoped_axioms.

  (* We can solve one of the normal substitution goals. 
   * Unfortunately we do not generate the versions of lemmas with functional extensionality. 
   * So we assert them in the proof. 
   * If Autosubst MetaCoq generates these lemmas, it can at least use the normal asimpl tactic. 
   * But at the moment that is not possible. *)
  Goal forall (f: nat -> tm) (s t: tm), 
      subst_tm f (subst_tm (scons t var_tm) s) = subst_tm (scons (subst_tm f t) var_tm) (subst_tm (up_tm_tm f) s).
  Proof.
    assert (varL_fext_tm : 
            forall (sigma_tm : nat -> tm),
              funcomp (subst_tm sigma_tm) var_tm = sigma_tm).
              { intros *. fext. apply varL_tm. }
    assert (renSubst_fext_tm : 
            forall (xi_tm : nat -> nat) (tau_tm : nat -> tm),
              funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm)).
              { intros *. fext. apply renSubst_tm. }
    assert (instId_fext_tm : subst_tm var_tm = id). { fext. apply instId_tm. }
    (* Start the real proof. *)
    intros *.
    rewrite ?substSubst_tm.
    unfold up_tm_tm.
    fsimpl_fext.
    rewrite ?varL_fext_tm.
    fsimpl_fext.
    rewrite ?renSubst_fext_tm.
    fsimpl_fext.
    rewrite ?instId_fext_tm.
    fsimpl_fext.
    cbn.
    reflexivity.
  Qed.

End utlc_unscoped.

(* The simply typed lambda calculus. *)
Definition stlc : autosubstLanguage :=
  {| al_sorts := <{ ty : Type;
                    tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    app : tm -> tm -> tm;
                    lam : ty -> (bind tm in tm) -> tm }} |}.

Module stlc_fintype.
  MetaCoq Run Autosubst Wellscoped for stlc.
  Print ty.
  Print tm.
  (* Autosubst logs which lemmas are generated. 
   * In VSCoq this is also printed to the "Info" channel. 
   * Unfortunately, this makes the generated code a lot less discoverable. 
   * But here's one of the generated lemmas. *)
  Print compSubstSubst_tm. (* composition of substitutions *)
End stlc_fintype.

Module stlc_unscoped.
  MetaCoq Run Autosubst Unscoped for stlc.
  Print ty.
  Print tm.
End stlc_unscoped.

(* call-by-value SystemF *)
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
  (* SysF_cbv already takes pretty long on my laptop. *)
  Time MetaCoq Run Autosubst Wellscoped for fcbv.
  (* tm and vl are generated mutually recursive *)
  Print tm.
End fcbv_fintype.

Module fcbv_unscoped.
  Time MetaCoq Run Autosubst Unscoped for fcbv.
  Print tm.
End fcbv_unscoped.

(* The pi-calculus *)
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
  
  (* chan is only a variable *)
  Print chan.
  Print proc.
End pi_fintype.

Module pi_unscoped.
  MetaCoq Run Autosubst Unscoped for pi.
  
  Print proc.
End pi_unscoped.

(* The simply typed lambda calculus with addition and constants. *)
Definition num : autosubstLanguage :=
  {| al_sorts := <{ tm : Type;
                    nat : Type }>;
     al_ctors := {{ const : nat -> tm;
                    Plus : tm -> tm -> tm;
                    app : tm -> tm -> tm;
                    lam : (bind tm in tm) -> tm }} |}.

Module num_fintype.
  MetaCoq Run Autosubst Wellscoped for num.
  
  (* The interesting thing here is that nat is declared as a sort but we do not generate code for it 
   * because it has no declared constructors and also is not open, i.e. no variable constructor. *)
  Print tm.
End num_fintype.

Module num_unscoped.
  MetaCoq Run Autosubst Unscoped for num.

  Print tm.
End num_unscoped.

(* First-order logic with functions and predicates that are parameterized by their arity *)
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

Module fol.
  (* The codF functor is just a function 
   * codF (fin f) (term) = fin f -> term *)
  (* At the moment I cannot create inductive types that contain functors 
   * This is due to universe constraint errors. Inferring the universe constraints might be possible 
   * in a future version of MetaCoq. But for now the user must create the exact 
   * inductive type that Autosubst _would_ have  generated. 
   *)
   From ASUB Require Import core fintype.

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
End fol.

Module fol_fintype.
  Include fol.

  (* Import TemplateMonadNotations. *)
  (* MetaCoq Run (translate_signature fol >>= fun sig => tmPrint (getIndCtorNames sig)). *)

  (* AutosubstNoInd just skips the creation of the inductive type. So it just generates all the lemmas.
   * If the inductive type that the user writes is not correct, this command will fail. *)
  MetaCoq Run AutosubstNoInd Wellscoped for fol.
End fol_fintype.

Module fol_unscoped.
  Include fol.

  (* Autosubst MetaCoq does not check for unsupported syntax combinations yet *)
  (* TODO should signal not supported *)
  Fail MetaCoq Run AutosubstNoInd Unscoped for fol.
End fol_unscoped.
      
(* Untyped lambda calculus with variadic binder uses the list functor. 
 * This means the user also has to generate the inductive type. *)
Definition variadic : autosubstLanguage :=
  {| al_sorts := <{ tm : Type  }>;
     al_ctors := {{ app : tm -> listF (tm) -> tm;
                    lam (p: nat) : (bind <p, tm> in tm) -> tm }} |}.

Module variadic_fintype.
  From ASUB Require Import core fintype.
  
  Inductive tm (n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_tm
  | app : tm n_tm -> list (tm n_tm) -> tm n_tm
  | lam : forall p : nat, tm (plus p n_tm) -> tm n_tm.

  MetaCoq Run AutosubstNoInd Wellscoped for variadic.
  Print compSubstSubst_tm.
End variadic_fintype.

Module variadic_unscoped.

  (* TODO should signal not supported *)
  (* MetaCoq Run Autosubst Unscoped for variadic. *)
End variadic_unscoped.

(* We can use unicode identifiers in our definitions. *)
(* lower-case lambda does not work as a Coq identifier. But apparently this approach works with all identifiers, e.g. upper-case lambda *)
Definition unicode : autosubstLanguage :=
  {| al_sorts := <{ ty : Type; tm : Type }>;
     al_ctors := {{ Base : ty;
                    Fun : ty -> ty -> ty;
                    アップ : tm -> tm -> tm;
                    Λ : ty -> (bind tm in tm) -> tm }} |}.

Module unicode_fintype.
  MetaCoq Run Autosubst Wellscoped for unicode.
  Print tm.
End unicode_fintype.

Module unicode_unscoped.
  MetaCoq Run Autosubst Unscoped for unicode.
  Print tm.
End unicode_unscoped.