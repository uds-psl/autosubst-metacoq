Require Import String Arith List.
Import ListNotations.

From ASUB Require Import hsig utils quotes.
From MetaCoq.Template Require Import Ast.

Open Scope string.

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.

Definition eq_ ty t0 t1 := tApp eq_q [ty; t0; t1].

Definition lambda_ (bname: string) (ty body: term) :=
  tLambda {| binder_name := nNamed bname; binder_relevance := Relevant |} ty body.

Fixpoint add_binders (bs: list (string * term)): term -> term :=
  match bs with
  | [] => fun t => t
  | (bname, btype) :: bs =>
    fun t => lambda_ bname btype (add_binders bs t)
  end.
