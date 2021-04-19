From MetaCoq.Template Require Import Ast.
Require Import String List.
Import ListNotations.

Definition dbmap_empty : string -> nat := fun _ => 666.

Definition dbmap_add (s: string) (dbmap: string -> nat) :=
  fun s' =>
    if eqb s s' then 0
    else S (dbmap s').

Fixpoint dbmap_adds (ss: list string) (dbmap: string -> nat) :=
  match ss with
  | [] => dbmap
  | s :: ss =>
    dbmap_adds ss (dbmap_add s dbmap)
  end.

Definition dbmap_get (dbmap: string -> nat) (s: string) : term :=
  tRel (dbmap s).

