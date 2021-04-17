From MetaCoq.Template Require Import All.
Require Import List.
Import ListNotations MonadNotation.

Fixpoint tm_sequence {A: Type} (mvals: list (TemplateMonad A)) : TemplateMonad (list A) :=
  match mvals with
  | [] => tmReturn []
  | mval :: mvals =>
    val <- mval;;
    vals <- tm_sequence mvals;;
    tmReturn (val :: vals)
  end.

Fixpoint tm_mapM {A B: Type} (f: A -> TemplateMonad B) (l: list A) : TemplateMonad (list B) :=
  match l with
  | [] => tmReturn []
  | a :: l =>
    b <- f a;;
    bs <- tm_mapM f l;;
    tmReturn (b :: bs)
  end.
          
