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

Fixpoint mapi' {A B: Type} (f: nat -> A -> B) (as_: list A) (n: nat): list B :=
  match as_ with
  | [] => []
  | a :: as_ =>
    (f n a) :: (mapi' f as_ (S n))
  end.

Definition mapi {A B: Type} (f: nat -> A -> B) (as_: list A): list B :=
  mapi' f as_ 0.

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
  
Fixpoint list_none {A: Type} (f: A -> bool) (l: list A) : bool :=
  match l with
  | [] => true
  | a :: l =>
    negb (f a) && list_none f l
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

Module NEList.
  Definition t (A: Type) := (A * list A)%type.

  Definition to_list {A: Type} (ne: t A) :=
    let '(v, l) := ne in
    v :: l.
End NEList.

(* Require Import Structures.OrderedTypeEx FSets.  *)
(* (* a.d. TODO I would rather use MSets instead of FSets since they are recommended but MSets uses a different OrderedType module and there is no String_as_OT for it *) *)
(* (* Module A : Structures.Orders.OrderedType := String_as_OT. *) *)

(* (* module for sets of strings *) *)
(* Module SSet := FSetList.Make String_as_OT. *)

