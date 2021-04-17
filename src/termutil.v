Require Import String Arith.

From ASUB Require Import hsig utils.

Open Scope string.

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.
