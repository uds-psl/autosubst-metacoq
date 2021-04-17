Require Import Structures.OrderedType Structures.OrderedTypeEx List String.
Import ListNotations.
Require Import FSets.FMapList Arith.
From ASUB Require Import utils.

Module FMap (X: OrderedType).
  (* Finite maps.
   a.d. TODO remove the ordered constraint because map/fold destroys the sorted invariant anyways and I don't want to run into bugs in the future where I work with unsorted maps *)

  Definition key := X.t.
  Definition t (elt: Type) := list (key * elt)%type.

  Definition empty {elt: Type} : t elt := [].

  Fixpoint add {elt: Type} (s: t elt) (k: key) (v: elt) : t elt :=
    match s with
    | [] => [(k, v)]
    | (k', v') :: s' =>
      match X.compare k k' with
      | LT _ => (k, v) :: s
      | EQ _ => (k, v) :: s'
      | GT _ => (k', v') :: add s' k v
      end
    end.

  Definition union {elt: Type} (s s': t elt) : t elt :=
    app s s'.
  
  Fixpoint mem {elt: Type} (s: t elt) (k: key) : bool :=
    match s with
    | [] => false
    | (k', _) :: s' =>
      match X.compare k k' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem s' k
      end
    end.

  Fixpoint find {elt: Type} (s: t elt) (k: key) : option elt :=
    match s with
    | [] => None
    | (k', v) :: s' =>
      match X.compare k k' with
      | LT _ => None
      | EQ _ => Some v
      | GT _ => find s' k
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
    | [] => empty
    | (k, v) :: A => add (fromList A) k v 
    end.
End FMap. 

Module SFMap := FMap String_as_OT.

Module FSet (X: OrderedType).

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := [].

  Definition elements (s: t) : list elt := s.

  Definition singleton (v: elt) : t := [v].

  Fixpoint add (s: t) (v: elt) :=
    match s with
    | [] => [v]
    | v' :: s' =>
      match X.compare v v' with
      | LT _ => v :: s
      | EQ _ => s
      | GT _ => v' :: add s' v
      end
    end.

  Fixpoint mem (s: t) (v: elt) :=
    match s with
    | [] => false
    | v' :: s' =>
      match X.compare v v' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem s' v
      end
    end.

  Fixpoint fromList (l: list elt) :=
    match l with
    | [] => empty
    | v :: l =>
      add (fromList l) v
    end.

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
  












           
