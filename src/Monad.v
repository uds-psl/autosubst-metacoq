Require Import List.
Import ListNotations.

From ASUB Require Import Utils.

Module Type RWSEParams.
  Parameter R W S E : Type.
  Parameter empty : W.
  Parameter append : W -> W -> W.
End RWSEParams.

(* Module Type RWSE_T. *)
(*   Parameter M : Type -> Type. *)
(*   Parameter bind : forall A B, M A -> (A -> M B) -> M B. *)

(* End RWSE_T. *)

Module RWSE (T: RWSEParams).
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
  
  Definition pure {A: Type} : A -> t A := fun a r s => inr (T.empty, s, a).

  Definition run {A: Type} : t A -> T.R -> T.S -> T.E + (T.W * T.S * A) := fun ma => ma.

  (* taken form the notations of the TemplateMonad *)
  Module Notations.
    Declare Scope rwse_scope.
    
    Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                               (at level 100, c1 at next level, right associativity) : rwse_scope.

    Notation "' pat <- c1 ;; c2" := (bind c1 (fun x => match x with pat => c2 end))
                                   (at level 100, pat pattern, c1 at next level, right associativity) : rwse_scope.
    
    Notation "c1 ;; c2" := (bind c1 (fun _ => c2))
                          (at level 100, right associativity) : rwse_scope.

    (* automatically put scope on top of the stack when this module is imported. *)
    #[ global ]
    Open Scope rwse_scope.
  End Notations.

  Import Notations.

  Definition ask : t T.R :=
    fun r s => inr (T.empty, s, r).
  Definition asks {A: Type} : (T.R -> A) -> t A :=
    fun f r s => inr (T.empty, s, f r).

  Definition get : t T.S :=
    fun _ s => inr (T.empty, s, s).
  Definition gets {A: Type} : (T.S -> A) -> t A :=
    fun f _ s => inr (T.empty, s, f s).
  
  Definition put : T.S -> t unit :=
    fun s _ _ => inr (T.empty, s, tt).
  Definition puts : (T.S -> T.S) -> t unit :=
    fun f _ s => inr (T.empty, f s, tt).

  Definition tell : T.W -> t unit :=
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
  
  Definition a_map {A B: Type} : (A -> t B) -> list A -> t (list B) :=
    fun f as_ => sequence (map f as_).

  Fixpoint a_map2 {A B C: Type} (f: A -> B -> t C) (l0: list A) (l1: list B) : t (list C) :=
    match l0, l1 with
    | a::l0, b::l1 =>
      c <- f a b;;
      cs <- a_map2 f l0 l1;;
      pure (c::cs)
    | [], _ => pure []
    | _, [] => pure []
    end.

  Definition a_mapi {A B: Type} : (nat -> A -> t B) -> list A -> t (list B) :=
    fun f as_ => sequence (mapi f as_).

  Fixpoint a_filter {A: Type} (f: A -> t bool) (xs: list A) : t (list A) :=
    match xs with
    | [] => pure []
    | x :: xs =>
      b <- f x;;
      fxs <- a_filter f xs;;
      if b then pure (x :: fxs) else pure fxs
    end.
  
  Definition a_concat_map {A B: Type} : (A -> t (list B)) -> list A -> t (list B) :=
    fun f as_ => fmap (@List.concat B) (a_map f as_).
  
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

