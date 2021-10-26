Require Import List String Ascii.
Import ListNotations.
#[ local ]
 Open Scope string.

Inductive tactic : Set :=
  t_idtac : string -> tactic
| t_setoid_rewrite_lr : bool -> string -> tactic
| t_rewrite' : bool -> bool -> bool -> string -> tactic
| t_call_args : string -> list string -> tactic
| t_call_tac : string -> tactic -> tactic
| t_cbn : list string -> tactic
| t_intros : list string -> tactic
| t_unfold_loc : bool -> list string -> tactic
(* combinators *)
| t_repeat : tactic -> tactic
| t_first : list tactic -> tactic
| t_progress : tactic -> tactic
| t_try : tactic -> tactic
| t_then : list tactic -> tactic.

(** * Default setoid rewrite is left-to-right *)
Definition t_setoid_rewrite (name: string) : tactic :=
  t_setoid_rewrite_lr false name.
Definition t_unfold (names: list string) : tactic :=
  t_unfold_loc false names.
Definition t_call (name: string) : tactic :=
  t_call_args name [].
Definition t_rewrite (lemma: string) : tactic :=
  t_rewrite' false false false lemma.
Definition t_erewrite (lemma: string) : tactic :=
  t_rewrite' false true false lemma.

Inductive automationCommand : Set :=
| a_ltac : string -> tactic -> automationCommand
| a_ltacNotation : string -> tactic -> automationCommand
| a_classUp : string -> automationCommand
| a_instance : string -> string -> string -> automationCommand
| a_properInstance : string -> list string -> list string -> string -> string -> automationCommand
| a_notSubstFun : list string -> string -> automationCommand
| a_notSubst : list string -> string -> automationCommand
| a_notRenFun : list string -> string -> automationCommand
| a_notRen : list string -> string -> automationCommand
| a_notVar : string -> automationCommand
(* | a_notVarInst : string -> automationCommand *)
| a_notVarConstr : string -> automationCommand
| a_notUp : string -> string -> automationCommand
| a_notUp2 : string -> automationCommand.

Definition newline := string_of_list_ascii [ascii_of_nat 10].
Definition quote := string_of_list_ascii [ascii_of_nat 34].

Fixpoint pr_tactic (tac: tactic) : string :=
  let s := match tac with
           | t_idtac msg => "idtac """ ++ msg ++ """"
           | t_setoid_rewrite_lr lr lemma =>
             if lr
             then "setoid_rewrite <- " ++ lemma
             else "setoid_rewrite " ++ lemma
           | t_rewrite' rep ev lr lemma =>
             let cmd := if ev then "erewrite" else "rewrite" in
             let lemma := if rep then "?" ++ lemma else lemma in
             if lr
             then cmd ++ " <- " ++ lemma
             else cmd ++ " " ++ lemma
           | t_call_args operator args =>
             match args with
             | [] => operator
             | _ => operator ++ " " ++ String.concat " " args
             end
           | t_call_tac operator tac => operator ++ " " ++ pr_tactic tac
           | t_cbn consts => 
             match consts with 
             | [] => "cbn"
             | _ => "cbn [ " ++ String.concat " " consts ++ " ]"
             end
           | t_intros pats => "intros " ++ String.concat " " pats
           | t_unfold_loc star consts => 
             if star 
             then "unfold " ++ String.concat ", " consts ++ " in *"
             else "unfold " ++ String.concat ", " consts
           | t_repeat tac => "repeat " ++ pr_tactic tac
           | t_first tacs => "first [ " ++ String.concat (newline ++ "| ") (map pr_tactic tacs) ++ " ]"
           | t_progress tac => "progress " ++ pr_tactic tac
           | t_try tac => "try " ++ pr_tactic tac
           | t_then tacs => concat (";" ++ newline) (map (fun t => "(" ++ pr_tactic t ++ ")") tacs)
           end in
  s.

  Definition pr_tactic_cmd (tac: tactic) : string :=
    pr_tactic tac ++ ".".

  Definition pr_automation_command (ac: automationCommand) : string :=
  match ac with
  | a_ltac name tac =>
    "Ltac " ++ name ++ " := " ++ pr_tactic_cmd tac
  | a_ltacNotation name tac =>
    "Tactic Notation " ++ name ++ " := " ++ pr_tactic_cmd tac
  | a_classUp sort => 
    "Class Up_" ++ sort ++ " X Y :=" ++ newline 
    ++ "  up_" ++ sort ++ " : X -> Y."
  | a_instance name type body =>
    "Instance " ++ name ++ " : (" ++ type ++ ") := " ++ body ++ "."
  | a_properInstance name ss substSorts opName extName =>
    let introNames := List.concat (List.map (fun substSort => [
                                               "f_" ++ substSort;
                                               "g_" ++ substSort;
                                               "Eq_" ++ substSort 
                                             ])
                                            substSorts) in
    let tac := t_then [ t_intros (List.app introNames ["s"; "?"; "<-"]);
                        t_call_args "apply" [extName];
                        t_call "assumption" ] in
    let binders := match ss with [] => "" | _ => " {" ++ (String.concat " " ss) ++ " : nat }" end in
    let op := match ss with [] => opName | _ => " (" ++ opName ++ " " ++ (String.concat " " ss) ++ ")" end in
    let proper := "(Proper (" 
      ++ (List.fold_left (fun p _ => "pointwise_relation _ eq ==> " ++ p)
                        substSorts "eq ==> eq")
      ++ ")" ++ op ++ ")." in
    "Instance " ++ name ++ binders ++ ":" ++ newline
    ++ proper ++ newline 
    ++ "Proof." ++ newline 
    ++ pr_tactic tac ++ newline 
    ++ "Qed."
  | a_notSubstFun substSorts sort =>
    let sigmas := List.map (fun substSort => "sigma_" ++ substSort) substSorts in
    "Notation ""[ " ++ (String.concat " ; " sigmas) ++ " ]"" := (subst_" ++ sort ++ " " ++ (String.concat " " sigmas) ++ ")" ++ newline
    ++ "  (at level 1, left associativity, only printing) : fscope."
  | a_notSubst substSorts sort => 
    let sigmas := List.map (fun substSort => "sigma_" ++ substSort) substSorts in
    "Notation ""s [ " ++ (String.concat " ; " sigmas) ++ " ]"" := (subst_" ++ sort ++ " " ++ (String.concat " " sigmas) ++ ")" ++ newline
    ++ "  (at level 7, left associativity, only printing) : subst_scope."
  | a_notRenFun substSorts sort =>
    let xis := List.map (fun substSort => "xi_" ++ substSort) substSorts in
    "Notation ""⟨ " ++ (String.concat " ; " xis) ++ " ⟩"" := (ren_" ++ sort ++ " " ++ (String.concat " " xis) ++ ")" ++ newline
    ++ "  (at level 1, left associativity, only printing) : fscope."
  | a_notRen substSorts sort => 
    let xis := List.map (fun substSort => "xi_" ++ substSort) substSorts in
    "Notation ""s ⟨ " ++ (String.concat " ; " xis) ++ " ⟩"" := (ren_" ++ sort ++ " " ++ (String.concat " " xis) ++ ")" ++ newline
    ++ "  (at level 7, left associativity, only printing) : subst_scope."
  | a_notVar sort => 
    "Notation ""'var'"" := var_" ++ sort ++ " (at level 1, only printing) : subst_scope."
  (* | a_notVarInst sort =>
    "Notation ""x '__" ++ sort ++ "'"" := (@ids _ _ VarInstance_" ++ sort ++ " x)" ++ newline 
    ++ "  (at level 5, format ""x __" ++ sort ++ """, only printing) : subst_scope." *)
  | a_notVarConstr sort =>
    "Notation ""x '__" ++ sort ++ "'"" := (var_" ++ sort ++ " x)" ++ newline 
    ++ "  (at level 5, format ""x __" ++ sort ++ """) : subst_scope."
  | a_notUp boundSort sort =>
    "Notation ""↑__" ++ sort ++ """ := up_" ++ boundSort ++ "_" ++ sort ++ " (only printing) : subst_scope."
  | a_notUp2 sort =>
    "Notation ""↑__" ++ sort ++ """ := up_" ++ sort ++ " (only printing) : subst_scope."
  end.

Definition pr_automation (acs: list automationCommand) : string :=
  let nn := newline ++ newline in
  concat nn (List.map pr_automation_command acs).

Definition exampletac :=
  t_then [ t_intros [ "a"; "b"; "*" ];
           t_first [ t_try (t_progress (t_unfold ["a"]));
                     t_try (t_rewrite "b");
                     t_call "auto" ] ].

Definition exampleautomation :=
  [ a_ltac "exampletac2" exampletac;
    a_ltacNotation """exampletac3""" exampletac ].
                  
Compute pr_automation exampleautomation. 

