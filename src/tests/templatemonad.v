From MetaCoq.Template Require Import All.

Require Import Arith.
Import MonadNotation.

Definition foo (n: nat) : TemplateMonad nat :=
  tmReturn (S n).

Definition test (n:nat) : TemplateMonad bool :=
  m <- foo n;;
  m2 <- foo m;;
  if le_lt_dec m 10
  then tmReturn true
  else tmReturn false.

Definition bar {X:Type} (a:X) := a.
(* MetaCoq Quote Definition bar_source := Eval compute in bar. *)

Definition
