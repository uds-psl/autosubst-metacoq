From ASUB Require Import util.
Require Import List.
Import ListNotations.

Module Type RWSE_params.
  Parameter R W S E : Type.
  Parameter empty : W.
  Parameter append : W -> W -> W.
End RWSE_params.

(* Module Type RWSE_T. *)
(*   Parameter M : Type -> Type. *)
(*   Parameter bind : forall A B, M A -> (A -> M B) -> M B. *)

(* End RWSE_T. *)

Module RWSE (T: RWSE_params).
  Definition t (A: Type) := T.R -> T.S -> T.E + (T.W * T.S * A).

  Definition join {A: Type} : t (t A) -> t A :=
    fun mma => fun r s =>
              match mma r s with
              | inl e => inl e
              | inr (w, s', ma) =>
                match ma r s' with
                | inl e => inl e
                | inr (w', s'', a) => inr (T.append w w', s'', a)
                end
              end.
  Definition bind {A B: Type} : t A -> (A -> t B) -> t B :=
    fun ma f => fun r s =>
               match ma r s with
               | inl e => inl e
               | inr (w, s', a) => f a r s'
               end.
  Definition pure {A: Type} : A -> t A :=
    fun a r s => inr (T.empty, s, a).
  Definition run {A: Type} : t A -> T.R -> T.S -> T.E + (T.W * T.S * A) := fun ma => ma.

  Module Notations.
    Declare Scope rwse_scope.
    
    Notation "x <- c1 ;; c2" := (bind  c1 (fun x => c2))
                               (at level 100, c1 at next level, right associativity) : rwse_scope.
    Notation "c1 ;; c2" := (bind  c1 (fun _ => c2))
                          (at level 100, right associativity) : rwse_scope.

    (* Bind Scope rwse_scope with M. *)
    (* automatically put scope on top of the stack when this module is imported. *)
    #[ global ]
    Open Scope rwse_scope.
  End Notations.

  Import Notations.
  Definition ask {A: Type} : t T.R :=
    fun r s => inr (T.empty, s, r).
  Definition asks {A B: Type} : (T.R -> B) -> t B :=
    fun f r s => inr (T.empty, s, f r).

  Definition get {A: Type} : t T.S :=
    fun _ s => inr (T.empty, s, s).
  Definition put {A: Type} : T.S -> t unit :=
    fun s _ _ => inr (T.empty, s, tt).

  Definition tell {A: Type} : T.W -> t unit :=
    fun w _ s => inr (w, s, tt).

  Definition error {A: Type} : T.E -> t A :=
    fun e _ _ => inl e.

  Definition fmap {A B: Type} : (A -> B) -> t A -> t B :=
    fun f ma r s => match ma r s with
                 | inl e => inl e
                 | inr (w, s', a) => inr (w, s', f a)
                 end.

  Definition fmap2 {A B C: Type} : (A -> B -> C) -> t A -> t B -> t C :=
    fun f ma mb =>
   f' <- (fmap f ma);;
   fmap f' mb.

  Fixpoint sequence {A: Type} (ms: list (t A)) : t (list A) :=
    match ms with
    | [] => pure []
    | ma :: ms =>
      a <- ma;;
      as_ <- sequence ms;;
      pure (a :: as_)
    end.
  
  Definition amap {A B: Type} : (A -> t B) -> list A -> t (list B) :=
    fun f as_ => sequence (map f as_).

  Definition a_mapi {A B: Type} : (nat -> A -> t B) -> list A -> t (list B) :=
    fun f as_ => sequence (mapi f as_).
  
  Fixpoint m_fold_left {A B: Type} (f: A -> B -> t A) (init: A) (bs: list B) : t A :=
    match bs with
    | [] => pure init
    | b :: bs =>
      init' <- f init b;;
      m_fold_left f init' bs
    end.
           
  Fixpoint m_fold_right {A B: Type} (f: B -> A -> t A) (init: A) (bs: list B) : t A :=
    match bs with
    | [] => pure init
    | b :: bs =>
      a <- m_fold_right f init bs;;
      f b a
    end.
End RWSE.

Require Import String.
(* a.d. TODO, only really need error monad here. Write other monad variants. *)
Module EParams. 
  Definition R := unit.
  Definition W := unit.
  Definition S := unit.
  Definition E := string.

  Definition append := fun (_ _: unit) => tt.
  Definition empty := tt.
End EParams.

Module E := RWSE EParams.
