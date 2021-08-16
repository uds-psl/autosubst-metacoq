From MetaCoq.Template Require Import All.
Require Import String.
Import MonadNotation Ast BasicAst.

Definition bar {X:Type} (a:X) := a.
(* MetaCoq Quote Definition bar_source := Eval compute in bar. *)
Definition baz {s t: nat} (H: s = t) := H.
Eval compute in baz.
(* = fun H : ?s = ?t => H *)
(* : ?s = ?t -> ?s = ?t *)

Compute (baz eq_refl).


MetaCoq Quote Definition eq_q := @eq.
MetaCoq Quote Definition nat_q := nat.
MetaCoq Quote Definition one_q := 1.
Definition evar1 := hole.
Definition evar2 := hole.
Definition one_eq := tApp eq_q [nat_q; one_q; one_q].
Definition evar_eq := tApp eq_q [nat_q; evar1; evar2].
MetaCoq Test Unquote evar_eq.

Definition tmFunWithImplicits : TemplateMonad unit :=
  let lname := {| binder_name:=nNamed "H"%string; binder_relevance:=Relevant |} in
  let evar1 := hole in
  let evar2 := hole in
  let ty := tApp eq_q [nat_q; evar1; evar2] in
  let tm := tRel 0 in
  let fn := tLambda lname ty tm in
  unq <- tmUnquote fn;;
  tmPrint unq.

MetaCoq Run tmFunWithImplicits.
 
