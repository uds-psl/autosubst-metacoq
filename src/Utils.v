From MetaCoq.Template Require Import All.
Require Import List.
Import ListNotations Nat.

Fixpoint mkArr t1 ts2 :=
  match ts2 with
  | [] => t1
  | t2 :: ts2 => tProd {| binder_name := BasicAst.nAnon; binder_relevance := BasicAst.Relevant |}
                     t1
                     (mkArr t2 ts2)
  end.

Fixpoint mkArrRev ts1 t2 :=
  match ts1 with
  | [] => t2
  | t1 :: ts1 => tProd {| binder_name := BasicAst.nAnon;
                        binder_relevance := BasicAst.Relevant |}
                     t1
                     (mkArrRev ts1 t2)
  end.

Definition ref_ name := tVar name. 

Definition sortType sort :=
  (* also take substs as an argument *)
  ref_ sort.

Definition app_ s t := tApp s [t].

Definition appRef_ name t :=
  app_ (ref_ name) t.

Require Import List.
Import ListNotations.

Fixpoint mapi' {A B: Type} (f: nat -> A -> B) (l: list A) (n: nat): list B :=
  match l with
  | [] => []
  | a :: l =>
    (f n a) :: mapi' f l (S n)
  end.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A): list B :=
  mapi' f l 0.

(* map over two lists. No errors! we never call it with lists of different lengths anyways
 a.d. TODO, certifying function *)
Fixpoint map2 {A B C: Type} (f: A -> B -> C) (l0: list A) (l1: list B) :=
  match l0, l1 with
  | [], _ => []
  | _, [] => []
  | a :: l0, b :: l1 => (f a b) :: map2 f l0 l1
  end.

Fixpoint enumerate' {A: Type} (l: list A) (n: nat) : list (nat * A) :=
  match l with
  | [] => []
  | a :: l => (n, a) :: (enumerate' l (S n))
  end.
Definition enumerate {A: Type} (l: list A) : list (nat * A) := enumerate' l 0.

Definition findi {A: Type} (f: nat -> A -> bool) (l: list A ): option (nat * A) :=
  find (uncurry f) (enumerate l).

Lemma nth_error_Some_x :
  forall (A: Type) (l : list A) (n: nat),
    n < length l -> { x & nth_error l n = Some x }.
Proof.
  refine (fun A l n H => _).
  refine (match nth_error l n as p return (nth_error l n = p -> {x & p = Some x }) with
          | None => fun H' => _
          | Some x => fun _ => _
          end eq_refl).
  - exists x. reflexivity.
  - exfalso. apply (nth_error_Some l n); assumption.
Defined.
  
Fixpoint list_nonef {A: Type} (f: A -> bool) (l: list A) : bool :=
  match l with
  | [] => true
  | a :: l =>
    negb (f a) && list_nonef f l
  end.

Fixpoint list_anyf {A: Type} (f: A -> bool) (l: list A) : bool :=
  match l with
  | [] => false
  | a :: l =>
    (f a) || list_anyf f l
  end.

Fixpoint list_none (l: list bool) : bool :=
  match l with
  | [] => true
  | b :: l =>
    (negb b) || list_none l
  end.

Fixpoint list_any (l: list bool) : bool :=
  match l with
  | [] => false
  | b :: l =>
    b || list_any l
  end.

Definition list_empty {A: Type} (l: list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

Require Import String.

Fixpoint list_mem (s: string) (l: list string) : bool :=
  match l with
  | [] => false
  | s' :: l' =>
    if eqb s s'
    then true
    else list_mem s l'
  end.

Definition list_intersection (l0 l1: list string) : list string :=
  filter (fun s0 => list_mem s0 l1) l0.

Definition list_diff (l0 l1: list string) : list string :=
  filter (fun s0 => negb (list_mem s0 l1)) l0.

(* TODO put all the list helper functions into a module so I don't have to duplicate that here *)
Fixpoint list_mem_prod (s: string * string) (l: list (string * string)) : bool :=
  let '(s0, s1) := s in
  match l with
  | [] => false 
  | (s0', s1') :: l' =>
    if andb (eqb s0 s0') (eqb s1 s1')
    then true
    else list_mem_prod s l'
  end.
    
Definition list_diff_prod (l0 l1: list (string * string)) : list (string * string) :=
  filter (fun s => negb (list_mem_prod s l1)) l0.

Fixpoint list_filter_map {A B: Type} (f: A -> option B) (l: list A) : list B :=
  match l with
  | [] => []
  | a :: l =>
    let fa := f a in
    match fa with
    | None => list_filter_map f l
    | Some b => b :: (list_filter_map f l)
    end
  end.

Definition cartesian_product {A: Type} (xs ys: list A) : list (A * A) :=
  fold_left (fun c x =>
               let pairs := map (fun y => (x, y)) ys in
               app c pairs)
            xs [].

Fixpoint list_fill {A: Type} (a: A) (n: nat) : list A :=
  match n with
  | O => []
  | S n => a :: list_fill a n
  end.

Definition const {A B} (a: A) (b: B) : A := a.

(* Require Import Structures.OrderedTypeEx FSets.  *)
(* (* a.d. TODO I would rather use MSets instead of FSets since they are recommended but MSets uses a different OrderedType module and there is no String_as_OT for it *) *)
(* (* Module A : Structures.Orders.OrderedType := String_as_OT. *) *)

(* (* module for sets of strings *) *)
(* Module SSet := FSetList.Make String_as_OT. *)

(* copied from MetaCoq.Template.utils.MCString *)
Require DecimalString.
Definition string_of_nat :=
  fun n : nat =>
    DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Require Import Arith.

(* Has to be defined because I use in in AssocList to compute the union of a set *)
Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Type) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction (f x).
  - intros y. intros []%Nat.nlt_0_r.
  - intros y Hy. apply H.
    intros z Hz. apply IHn.
    apply (Nat.lt_le_trans (f z) (f y) n).
    + apply Hz.
    + apply lt_n_Sm_le, Hy.
Defined.

(** * hole to use in incomplete definitions *)
Axiom undefined : forall {A:Type}, A.
