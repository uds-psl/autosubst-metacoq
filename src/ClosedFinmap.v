(* This module implements closed finite maps. They are like finite maps except that to retrieve an
 element you need to provide a proof that the key is in the map. Then you will get a value of the
 result type (not an option like with normal finmaps)
 At first I planned to use sort of an "opaque" proof of membership but then I naturally used it
 as a path to the object.
 So to use this with e.g. strings, in the internal datastructures like Spec I want to pair each
 occurrence of a string I want to look up with its path in the map *)
Require Import String List.
Import ListNotations.
Require Import Structures.OrderedType Structures.OrderedTypeEx.

Module Type CFmap_params.
  Parameter t: Type.
End CFmap_params.

Module CFmap (X: CFmap_params).
  
  Fixpoint InD (s:X.t) (l: list X.t) : Type :=
    match l with
    | [] => False
    | s' :: l =>
      (s = s') + InD s l
    end.

  Definition inclD (l l': list X.t) := forall s, InD s l -> InD s l'.

  Lemma inclD_cons (s: X.t) (l l': list X.t) :
    inclD (s :: l) l' -> inclD l l' * InD s l'.
  Proof.
    unfold inclD. intros H. split.
    - intros s' Hs'. apply H. right. apply Hs'.
    - apply H. left. reflexivity.
  Defined.

  Lemma inclD_refl {l: list X.t} :
    inclD l l.
  Proof.
    intros s. trivial.
  Defined.

  Inductive CFmap {T: Type}: list X.t -> Type :=
  | CNil : CFmap []
  | CCons : forall (s: X.t) (t: T) (l: list X.t) (d: CFmap l), CFmap (s :: l).
  Arguments CFmap T : clear implicits.
  Arguments CCons {T} s t {l} d.

  Lemma CFmap_inv {T: Type}: forall s l (d: CFmap T (s :: l)), { t & { d' | d = CCons s t d' } }.
  Proof.
    intros *.
    (* a.d. DONE, using eliminator like in ACT *)
    enough (H: forall l (d: CFmap T l), match l as l0 return CFmap T l0 -> Type with
                                 | [] => fun _ => unit
                                 | s :: l' => fun d => { t & { d' | d = CCons s t d' } }
                                 end d).
    - apply (H (s :: l) d).
    - clear s l d. intros *.
      destruct d as [|s t l' d'].
      + exact tt.
      + exists t, d'. reflexivity.
  Defined.

  Lemma get {T: Type} (s: X.t) {l: list X.t} (H: InD s l) (d: CFmap T l) : T.
  Proof.
    induction l.
    - destruct H.
    - destruct (CFmap_inv a l d) as (t & d' & _).
      (* If I just destruct H then get depends on the form of H which means I don't even need the type to be discrete. All get does is take a path through l which is dictated by H *)
      destruct H as [H | H].
      + (* a.d. TODO if I want to to prove correctness of this function I will probably need to do something with the proof of s = a here. And maybe also do higher order recursion in CCons so that I can only recurse when s <> a *)
        exact t.
      + apply (IHl H d').
  Defined.

  Lemma fold_left' {A: Type} (l lorig: list X.t) (H: inclD l lorig) (f: forall (s: X.t) , InD s lorig -> A -> A) (state: A) : A.
    induction l as [|s l' IH].
    - exact state.
    - apply inclD_cons in H as [H0 H1].
      exact (f s H1 (IH H0)).
  Defined.

  Definition fold_left {A: Type} (l: list X.t) (f: forall (s:X.t), InD s l -> A -> A) (state: A) : A :=
    fold_left' l l inclD_refl f state.
End CFmap.

Module Example.
  Module mm.
    Definition t := string.
  End mm.

  Module M := (CFmap mm).
  Import M.
  
  Open Scope string.
  Definition sorts :=  ["tm"; "vl"; "ty"].
  Definition ty := "ty".
  Lemma tyIn : InD ty sorts.
  Proof.
    unfold InD. right. right. left.
    reflexivity.
  Defined.

  Definition myCFmap := CCons "tm" 11 (CCons "vl" 22 (CCons "ty" 33 CNil)).
  Definition myCFmap2 := CCons "tm" 0 (CCons "vl" 1 (CCons "ty" 0 CNil)).

  Compute get "ty" tyIn myCFmap.

  Compute (fold_left sorts (fun s H sum => (get s H myCFmap * get s H myCFmap2) + sum) 0).
End Example.

Module Type DecType.
  Parameter t: Type.
  Parameter eq_dec: forall x y: t, {x = y} + { x <> y }.
End DecType.

Module CFmap_dec (X: DecType).
  Module mm <: CFmap_params.
    Definition t := X.t.
  End mm.
  
  Module M := CFmap mm.
  Import M.
  
  Lemma InD_dec (s: mm.t) (l: list mm.t) :
    InD s l + (InD s l -> False).
  Proof.
    induction l as [|s' l' [IH|IH]].
    - right. intros [].
    - left. right. apply IH.
    - destruct (X.eq_dec s s') as [H|H].
      + left. left. apply H.
      + right. intros [H0 | H0].
        * contradiction.
        * apply IH, H0.
  Defined.
End CFmap_dec.

Module StringDec : DecType.
  Definition t := string.
  Definition eq_dec := String_as_OT.eq_dec.
End StringDec.

Module M := CFmap_dec StringDec.

