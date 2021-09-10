Require Import List.
Import ListNotations.

From ASUB Require Import Utils.

Definition t (A: Type) := (A * list A)%type.

Definition hd {A: Type} (ne: t A) : A :=
  let '(v, l) := ne in v.

Definition tl {A: Type} (ne: t A) : list A :=
  let '(v, l) := ne in l.

Definition to_list {A: Type} (ne: t A) : list A :=
  let '(v, l) := ne in
  v :: l.

Definition from_list {A: Type} (l: list A) : option (t A) :=
  match l with
  | [] => None
  | a :: l => Some (a, l)
  end.

Definition from_list' {A: Type} (l: list A) : match l with [] => list A | _ :: _ => (t A) end :=
  match l with
  | [] => []
  | a :: l => (a, l)
  end.

Definition map {A B: Type} (f: A -> B) (ne: t A) : t B :=
  let '(x, l) := ne in
  (f x, List.map f l).

Definition fold_left {A B: Type} (f: A -> B -> A) (ne: t B) (init: A) : A :=
  List.fold_left f (to_list ne) init.

Definition anyf {A: Type} (f: A -> bool) (ne: t A) : bool :=
  list_anyf f (to_list ne).
