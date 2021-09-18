Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

Require Import Arith.
From ASUB Require Import Utils.

Module Type Discrete.
  Parameter t : Set.
  Parameter eqb : t -> t -> bool.
End Discrete.

Module String_Discrete.
  Definition t := string.
  Definition eqb := String.eqb.
End String_Discrete.

(* Module bla : Discrete := String_Discrete.  *)

(* My own implementation of string as ordered type. Mainly tried it to improve performance when
 the example in Graph.v did not run anymore. Turns out that was because I changed size_ind in Utils.v to
 Qed. instead of Defined.
 But keeping it now since it's probably faster than the stdlib implementation that first converts
 the ascii to binary nats *)
(* Module MyStringOT. *)
(*   Definition t := string. *)
(*   (* Definition cmp := String_as_OT.cmp. *) *)
  
(*   Compute (match " ", "#" with *)
(*            | String a_head _, String b_head _ => *)
(*              Ascii_as_OT.cmp a_head b_head *)
(*            | _, _ => Eq *)
(*            end). *)
  
(*   Definition Ascii_cmp (a b : Ascii.ascii) : comparison := *)
(*     match a, b with *)
(*       (* least significant bit is on the left *) *)
(*     | Ascii.Ascii a0 a1 a2 a3 a4 a5 a6 a7, Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 => *)
(*       match Bool.compare a7 b7 with *)
(*       | Eq => *)
(*         match Bool.compare a6 b6 with *)
(*         | Eq => *)
(*           match Bool.compare a5 b5 with *)
(*           | Eq => *)
(*             match Bool.compare a4 b4 with *)
(*             | Eq => *)
(*               match Bool.compare a3 b3 with *)
(*               | Eq => *)
(*                 match Bool.compare a2 b2 with *)
(*                 | Eq => *)
(*                   match Bool.compare a1 b1 with *)
(*                   | Eq => *)
(*                     Bool.compare a0 b0 *)
(*                   | x => x *)
(*                   end *)
(*                 | x => x *)
(*                 end *)
(*               | x => x *)
(*               end *)
(*             | x => x *)
(*             end *)
(*           | x => x *)
(*           end *)
(*         | x => x *)
(*         end *)
(*       | x => x *)
(*       end *)
(*     end. *)

(*   (* Compute (match " " with *) *)
(*   (*          | String head _ => *) *)
(*   (*            head *) *)
(*   (*          | "" => Ascii.Ascii false false false false false false false false *) *)
(*   (*          end). *) *)
(*   (* Compute (match "c", "b" with *) *)
(*   (*          | String a_head _, String b_head _ => *) *)
(*   (*            Ascii_cmp a_head b_head *) *)
(*   (*          | _, _ => Eq *) *)
(*   (*          end). *) *)
  
(*   Fixpoint cmp (a b : t) : comparison := *)
(*     match a with *)
(*     | "" => match b with *)
(*            | "" => Eq *)
(*            | String _ _ => Lt *)
(*            end *)
(*     | String a_head a_tail => *)
(*       match b with *)
(*       | "" => Gt *)
(*       | String b_head b_tail => *)
(*         match Ascii_cmp a_head b_head with *)
(*         | Eq => cmp a_tail b_tail *)
(*         | Lt => Lt *)
(*         | Gt => Gt *)
(*         end *)
(*       end *)
(*     end. *)

(*   (* Compute (cmp "Hello" "Hella"). *) *)

(* End MyStringOT.  *)


(* DONE use more naive implementation that does not have ordering invariant
 * surprisingly this might even have better performance because our lists are very small in most cases *)
Module FMap (X: Discrete).
  (* Finite maps represented as association lists.
   * Invariant: keys are unique *)

  Definition key := X.t.
  Definition t (elt: Type) := list (key * elt)%type.

  Definition empty {elt: Type} : t elt := [].

  Fixpoint add {elt: Type} (s: t elt) (k: key) (v: elt) : t elt :=
    match s with
    | [] => [(k, v)]
    | (k', v') :: s' =>
      if X.eqb k k'
      then (k, v) :: s'
      else (k', v') :: (add s' k v)
    end.

  Fixpoint addCollect {elt: Type} (s: t (list elt)) (k: key) (v: elt) : t (list elt) :=
    match s with
    | [] => [(k, [v])]
    | (k', vs) :: s' =>
      if X.eqb k k'
      then (k, List.app vs [v]) :: s'
      else (k', vs) :: (addCollect s' k v)
    end.

  Fixpoint union {elt: Type} (s0 s1: t elt) : t elt :=
    match s0 with
    | [] => s1
    | (k, v) :: s0' =>
      union s0' (add s1 k v)
    end.
  
  Fixpoint mem {elt: Type} (s: t elt) (k: key) : bool :=
    match s with
    | [] => false
    | (k', _) :: s' =>
      if X.eqb k k'
      then true
      else mem s' k
    end.

  Fixpoint find {elt: Type} (s: t elt) (k: key) : option elt :=
    match s with
    | [] => None
    | (k', v) :: s' =>
      if X.eqb k k'
      then Some v
      else find s' k
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
    | [] => []
    | (k, v) :: A' => add (fromList A') k v
    end.

  Fixpoint fromListCollect {elt : Type} (A: list (key * elt)) : t (list elt) :=
    match A with
    | [] => []
    | (k, v) :: A' => addCollect (fromListCollect A') k v
    end.
  
End FMap. 

(* Module SFMap := FMap MyStringOT. *)
Module SFMap := FMap String_Discrete.


(* TODO tried using the balanced search tree from the library
 * for the implicit-map. It should balance itself and I expected it
 * to be fast.
 * However, it was unusably slow *)
(* Require FSets.FMapAVL. *)
(* Require Import Structures.OrderedTypeEx. *)

(* Module SFMapfast := FMapAVL.Make String_as_OT. *)


Module FSet (X: Discrete).

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := [].

  Definition elements (s: t) : list elt := s.

  Definition singleton (v: elt) : t := [v].

  Fixpoint mem (s: t) (v: elt) :=
    match s with
    | [] => false
    | v' :: s' =>
      if X.eqb v v'
      then true
      else mem s' v
    end.

  Fixpoint add (s: t) (v: elt) :=
    match s with
    | [] => [v]
    | v' :: s' =>
      if X.eqb v v'
      then v' :: s'
      else v' :: (add s' v)
    end.

  Fixpoint fromList (l: list elt) :=
    match l with
    | [] => empty
    | v :: l =>
      add (fromList l) v
    end.

  Fixpoint union (s0 s1: t) : t :=
    match s0 with
    | [] => s1
    | v :: s0' =>
      union s0' (add s1 v)
    end.

  Fixpoint filter (s: t) (f : elt -> bool) : t :=
    match s with
    | [] => []
    | v :: s' =>
      if f v
      then v :: (filter s' f)
      else filter s' f
    end.

  (* Lemma intersection (s0 s1: t) : t. *)
End FSet.

(* Module SSet := FSet MyStringOT. *)
Module SSet := FSet String_Discrete.
  









           
