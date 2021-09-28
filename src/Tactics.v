Require Import List String Ascii.
Import ListNotations.
#[ local ]
 Open Scope string.

Inductive tactic : Set :=
  t_idtac : string -> tactic
| t_setoid_rewrite : bool -> string -> tactic
| t_rewrite : bool -> bool -> bool -> string -> tactic
| t_call : string -> list string -> tactic
| t_call_tac : string -> tactic -> tactic
| t_cbn : list string -> tactic
| t_intros : list string -> tactic
| t_unfold : list string -> tactic
(* combinators *)
| t_repeat : tactic -> tactic
| t_first : list tactic -> tactic
| t_progress : tactic -> tactic
| t_try : tactic -> tactic
| t_then : list tactic -> tactic.

Definition newline := string_of_list_ascii [ascii_of_nat 10].
Definition quote := string_of_list_ascii [ascii_of_nat 34].

Fixpoint pr_tactic (tac: tactic) : string :=
  let s := match tac with
           | t_idtac msg => "idtac """ ++ msg ++ """"
           | t_setoid_rewrite lr lemma =>
             if lr
             then "setoid_rewrite <- " ++ lemma
             else "setoid_rewrite " ++ lemma
           | t_rewrite rep ev lr lemma =>
             let cmd := if ev then "erewrite" else "rewrite" in
             let lemma := if rep then "?" ++ lemma else lemma in
             if lr
             then cmd ++ " <- " ++ lemma
             else cmd ++ " " ++ lemma
           | t_call operator args => operator ++ " " ++ concat " " args
           | t_call_tac operator tac => operator ++ " " ++ pr_tactic tac
           | t_cbn consts => "cbn [ " ++ concat " " consts ++ " ]"
           | t_intros pats => "intros " ++ concat " " pats
           | t_unfold consts => "unfold " ++ concat ", " consts
           | t_repeat tac => "repeat " ++ pr_tactic tac
           | t_first tacs => "first [ " ++ concat (" |" ++ newline) (map pr_tactic tacs) ++ " ]"
           | t_progress tac => "progress " ++ pr_tactic tac
           | t_try tac => "try " ++ pr_tactic tac
           | t_then tacs => concat (";" ++ newline) (map (fun t => "(" ++ pr_tactic t ++ ")") tacs)
           end in
  s.

Definition pr_tactic_cmd (tac: tactic) : string :=
  pr_tactic tac ++ ".".

Definition pr_tactic_ltac (name: string) (tac: tactic) : string :=
  let s := "Ltac " ++ name ++ " := " ++ pr_tactic_cmd tac in
  s.
Definition pr_tactic_notation (not: string) (tac: tactic) : string :=
  "Tactic Notation """ ++ not ++ """ := " ++ pr_tactic_cmd tac. 


Definition exampletac :=
  t_then [ t_intros [ "a"; "b"; "*" ];
         t_first [ t_try (t_progress (t_unfold ["a"]));
                 t_try (t_rewrite false false false "b");
                 t_call "auto" []] ].
                  
Compute pr_tactic_ltac "exampletac2" exampletac.
Compute pr_tactic_notation "exampletac3" exampletac.

