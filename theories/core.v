(* Here I define the spec like that holds all the data for the code we want to generate *)
Require Import String List.
Import ListNotations.


Notation tId := string.
Notation vId := string.
Notation fId := string.
Notation cId := string.

Inductive Binder :=
| Single : tId -> Binder
| BinderList : string -> tId -> Binder.

Inductive ArgumentHead :=
| Atom : tId -> ArgumentHead
| FunApp : fId -> (* ast term option *) list ArgumentHead -> ArgumentHead.

Definition getBinders b :=
  match b with
  | Single x => [x]
  | BinderList _ x => [x]
  end.

(* a.d. todo recursion! *)
Fixpoint getArgSorts a :=
  match a with
  | Atom x => [x]
  | FunApp _ xs => flat_map getArgSorts xs
  end.

Set Primitive Projections.
Record Position := mkPosition
                     { binders : list Binder;
                       head : ArgumentHead }.
Record Constructor := mkConstructor
                        { cparameters : list (string * tId);
                          cname : cId;
                          cpositions : list Position }.
Unset Primitive Projections.

(* a.d. todo, recursion! *)
Definition getArgs c :=
  flat_map (fun p => getArgSorts p.(head)) c.(cpositions).

(* Require Import Coq.FSets.FMapList Coq.Structures.OrderedTypeEx. *)
(* Module M := FMapList.Make (String_as_OT). *)
(* Check M.empty . *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
(* nat_choiceType *)
(* Definition string_choiceType := Choice.Pack {| Choice.base := Equality.class string_eqType} *)
(* Set Printing All. *)
(* Check [fmap]. *)
(* Fact string_choiceMixin : choiceMixin *)
(* Fact nat_choiceMixin : choiceMixin nat. *)
(* Proof. *)
(* pose f := [fun (P : pred nat) n => if P n then Some n else None]. *)
(* exists f => [P n m | P [n Pn] | P Q eqPQ n] /=; last by rewrite eqPQ. *)
(*   by case: ifP => // Pn [<-]. *)
(* by exists n; rewrite Pn. *)
(* Qed. *)
(* Canonical nat_choiceType := Eval hnf in ChoiceType nat nat_choiceMixin. *)

(* Definition scope := {fmap string -> Constructor}. *)
Require Import Coq.Strings.Ascii Coq.Strings.String.


Notation string := string.

Definition tuple_of_ascii c :=
  let: Ascii x1 x2 x3 x4 x5 x6 x7 x8 := c in
  (x1, x2, x3, x4, x5, x6, x7, x8).

Definition ascii_of_tuple t :=
  let: (x1, x2, x3, x4, x5, x6, x7, x8) := t in
  Ascii x1 x2 x3 x4 x5 x6 x7 x8.

Lemma tuple_of_asciiK : cancel tuple_of_ascii ascii_of_tuple.
Proof. by case. Qed.

Definition ascii_eqMixin := CanEqMixin tuple_of_asciiK.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin := CanChoiceMixin tuple_of_asciiK.
Canonical ascii_choiceType := Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin := CanCountMixin tuple_of_asciiK.
Canonical ascii_countType := Eval hnf in CountType ascii ascii_countMixin.

Fixpoint seq_of_string s :=
  if s is String c s' then c :: seq_of_string s'
  else [::].

Fixpoint string_of_seq s :=
  if s is c :: s' then String c (string_of_seq s')
  else EmptyString.

Lemma seq_of_stringK : cancel seq_of_string string_of_seq.
Proof. by elim=> [|c s /= ->]. Qed.

Definition string_eqMixin := CanEqMixin seq_of_stringK.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin := CanChoiceMixin seq_of_stringK.
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin := CanCountMixin seq_of_stringK.
Canonical string_countType := Eval hnf in CountType string string_countMixin.

Section f.
  Open Scope fmap.
  Check ([fmap] : {fmap string -> nat}).
  Check [fmap].

  Definition test := [fmap]
                     .["ty"%string <- 1]
                     .["tm"%string <- 2].

  Definition test2 := [fmap]
                     .[2 <- 1]
                     .[3 <- 2].

  Print test2.
  (* It appears you cannot compute with these finmaps -.-* *)
  Compute test2.[? 2].
                       
