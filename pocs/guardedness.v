(* I wanted to test if the guardedness checker can specifically deal with functions on list or also user-defined types. Seems like it's exclusive to lists as the definition of getArgSorts2 fails *)
Require Import String.

Inductive mylist (A:Type) : Type :=
| MNil : mylist A
| MCons : A -> mylist A -> mylist A.
Arguments MCons {A}.
Arguments MNil {A}.

Inductive ArgumentHead2 :=
| Atom2 : string -> ArgumentHead2
| FunApp2 : string ->  mylist ArgumentHead2 -> ArgumentHead2.

Fixpoint concat2 {A: Type} (l0 l1 : mylist A) : mylist A :=
  match l0 with
  | MNil => l1 
  | MCons x l0 => MCons x (concat2 l0 l1)
  end.

Fixpoint flat_map2 {A B:Type} (f: A -> mylist B) (l : mylist A) : mylist B :=
  match l with
  | MNil => MNil
  | MCons x l => concat2 (f x) (flat_map2 f l)
  end.

Fail Fixpoint getArgSorts2 (a: ArgumentHead2) : mylist string :=
  match a with
  | Atom2 x => MCons x MNil
  | FunApp2 _  xs => flat_map2 getArgSorts2 xs
  end.

