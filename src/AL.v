Require Import Structures.OrderedType Structures.OrderedTypeEx List String.
Import ListNotations.
Require Import FSets.FMapList.

Module FMap (X: OrderedType).
  (* Include FMapList.Make X.  *)

  Definition key := X.t.
  Definition t (elt: Type) := list (key * elt)%type.

  Definition empty (elt: Type) : t elt := [].
  Fixpoint add {elt: Type} (k: key) (v: elt) (s: t elt) :=
    match s with
    | [] => [(k, v)]
    | (k', v') :: s' =>
      match X.compare k k' with
      | LT _ => (k, v) :: s
      | EQ _ => (k, v) :: s'
      | GT _ => (k', v') :: add k v s'
      end
    end.
  Fixpoint mem {elt: Type} (k: key) (s: t elt) :=
    match s with
    | [] => false
    | (k', _) :: s' =>
      match X.compare k k' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem k s'
      end
    end.
  Fixpoint find {elt: Type} (k: key) (s: t elt) : option elt :=
    match s with
    | [] => None
    | (k', v) :: s' =>
      match X.compare k k' with
      | LT _ => None
      | EQ _ => Some v
      | GT _ => find k s'
      end
    end.

  Fixpoint fold {elt A: Type} (f: key -> elt -> A -> A) (s: t elt) (state: A) : A :=
    match s with
    | [] => state
    | (k, v) :: s' => fold f s' (f k v state)
    end.

  Fixpoint map {elt elt': Type} (f: elt -> elt') (s: t elt) : t elt' :=
    match s with
    | [] => []
    | (k, v) :: s' => (k, f v) :: map f s'
    end.

  Fixpoint mapi {elt elt': Type} (f: key -> elt -> elt') (s: t elt) : t elt' :=
    match s with
    | [] => []
    | (k, v) :: s' => (k, f k v) :: mapi f s'
    end.
    
  (* a.d. todo, no guarantees about overwriting. I'm using elements -> List.map -> fromList to replace mapi since mapi seems bugged *)
  Fixpoint fromList {elt : Type} (A: list (key * elt)) : t elt :=
    match A with
    | [] => empty _
    | (k, v) :: A => add k v (fromList A)
    end.
End FMap. 

Module SFMap := FMap String_as_OT.

Require Import Arith.

Module FSet (X: OrderedType).

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := [].

  Definition elements (s: t) : list elt := s.

  Definition singleton (v: elt) : t := [v].

  Fixpoint add (v: elt) (s: t) :=
    match s with
    | [] => [v]
    | v' :: s' =>
      match X.compare v v' with
      | LT _ => v :: s
      | EQ _ => s
      | GT _ => v' :: add v s'
      end
    end.

  Fixpoint mem (v: elt) (s: t) :=
    match s with
    | [] => false
    | v' :: s' =>
      match X.compare v v' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem v s'
      end
    end.

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

  Fixpoint card (s: t) : nat :=
    match s with
    | [] => 0
    | _ :: s' => S (card s')
    end.

  Lemma union (s0 s1: t) : t.
    refine (size_ind (fun '(s0, s1) => card s0 + card s1) (fun _ => t) _ (s0, s1)).
    clear s0 s1.
    intros [s0 s1] IH.
    destruct s0 as [|v0 s0'] eqn:H0.
    - exact s1.
    - destruct s1 as [|v1 s1'] eqn:H1.
      + exact s0.
      + refine (match X.compare v0 v1 (* as p return (X.compare v0 v1 = p -> t) *) with
                | LT _ => _ 
                | EQ _ => _ 
                | GT _ => _ 
                end (* eq_refl *)).
        * refine (v0 :: IH (s0', v1 :: s1') _).
          cbn. apply Nat.lt_succ_diag_r.
        * refine (v0 :: IH (s0', s1') _).
          cbn. rewrite Nat.add_succ_r.
          apply (Nat.lt_trans (card s0' + card s1') (S (card s0' + card s1')) (S (S (card s0' + card s1')))).
          apply Nat.lt_succ_diag_r. apply Nat.lt_succ_diag_r.
        * refine (v1 :: IH (v0 :: s0', s1') _).
          cbn. rewrite Nat.add_succ_r.
          apply Nat.lt_succ_diag_r.
  Defined.

  Lemma intersection (s0 s1: t) : t.
    refine (size_ind (fun '(s0, s1) => card s0 + card s1) (fun _ => t) _ (s0, s1)).
    clear s0 s1.
    intros [s0 s1] IH.
    destruct s0 as [|v0 s0'] eqn:H0.
    - exact [].
    - destruct s1 as [|v1 s1'] eqn:H1.
      + exact [].
      + refine (match X.compare v0 v1 with
                | LT _ => _
                | EQ _ => _
                | GT _ => _
                end).
        * refine (IH (s0', v1 :: s1') _).
          cbn. apply Nat.lt_succ_diag_r.
        * refine (v0 :: IH (s0', s1') _).
          cbn. rewrite Nat.add_succ_r.
          apply (Nat.lt_trans (card s0' + card s1') (S (card s0' + card s1')) (S (S (card s0' + card s1')))).
          apply Nat.lt_succ_diag_r. apply Nat.lt_succ_diag_r.
        * refine (IH (v0 :: s0', s1') _).
          cbn. rewrite Nat.add_succ_r.
          apply Nat.lt_succ_diag_r.
  Defined.
End FSet.

Module SSet := FSet String_as_OT.
  












           
