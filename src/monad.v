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
  Definition M (A: Type) := T.R -> T.S -> T.E + (T.W * T.S * A).

  Definition join {A: Type} : M (M A) -> M A :=
    fun mma => fun r s =>
              match mma r s with
              | inl e => inl e
              | inr (w, s', ma) =>
                match ma r s' with
                | inl e => inl e
                | inr (w', s'', a) => inr (T.append w w', s'', a)
                end
              end.
  Definition bind {A B: Type} : M A -> (A -> M B) -> M B :=
    fun ma f => fun r s =>
               match ma r s with
               | inl e => inl e
               | inr (w, s', a) => f a r s'
               end.
  Definition ret {A: Type} : A -> M A :=
    fun a r s => inr (T.empty, s, a).
  Definition run {A: Type} : M A -> T.R -> T.S -> T.E + (T.W * T.S * A) := fun ma => ma.

  Module Notations.
    Declare Scope rwse_scope.
    
    Notation "x <- c1 ;; c2" := (bind  c1 (fun x => c2))
                               (at level 100, c1 at next level, right associativity) : rwse_scope.
    Notation "c1 ;; c2" := (bind  c1 (fun _ => c2))
                          (at level 100, right associativity) : rwse_scope.
    Print Grammar constr.

    (* Bind Scope rwse_scope with M. *)
    (* automatically put scope on top of the stack when this module is imported. *)
    #[ global ]
    Open Scope rwse_scope.
  End Notations.

  Import Notations.
  Definition ask {A: Type} : M T.R :=
    fun r s => inr (T.empty, s, r).
  Definition asks {A B: Type} : (T.R -> B) -> M B :=
    fun f r s => inr (T.empty, s, f r).

  Definition get {A: Type} : M T.S :=
    fun _ s => inr (T.empty, s, s).
  Definition put {A: Type} : T.S -> M unit :=
    fun s _ _ => inr (T.empty, s, tt).

  Definition tell {A: Type} : T.W -> M unit :=
    fun w _ s => inr (w, s, tt).

  Definition error {A: Type} : T.E -> M A :=
    fun e _ _ => inl e.

  Definition fmap {A B: Type} : (A -> B) -> M A -> M B :=
    fun f ma r s => match ma r s with
                 | inl e => inl e
                 | inr (w, s', a) => inr (w, s', f a)
                 end.

  Definition fmap2 {A B C: Type} : (A -> B -> C) -> M A -> M B -> M C :=
    fun f ma mb =>
   f' <- (fmap f ma);;
   fmap f' mb.

  Fixpoint sequence {A: Type} (ms: list (M A)) : M (list A) :=
    match ms with
    | [] => ret []
    | ma :: ms =>
      a <- ma;;
      as_ <- sequence ms;;
      ret (a :: as_)
    end.
  
  Definition amap {A B: Type} : (A -> M B) -> list A -> M (list B) :=
    fun f as_ => sequence (map f as_).

  Definition a_mapi {A B: Type} : (nat -> A -> M B) -> list A -> M (list B) :=
    fun f as_ => sequence (mapi f as_).
  
  Fixpoint m_fold_left {A B: Type} (f: A -> B -> M A) (init: A) (bs: list B) : M A :=
    match bs with
    | [] => ret init
    | b :: bs =>
      init' <- f init b;;
      m_fold_left f init' bs
    end.
           
  Fixpoint m_fold_right {A B: Type} (f: B -> A -> M A) (init: A) (bs: list B) : M A :=
    match bs with
    | [] => ret init
    | b :: bs =>
      a <- m_fold_right f init bs;;
      f b a
    end.
End RWSE.
