Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From ASUB Require Import AssocList Language Tactics GenM Utils.
Import GenM.Notations GenM.

From ASUB Require Import Names.
From ASUB Require Import GenUps.

(** * Generate the Up_x_y typeclasses *)
Definition generateTypeclasses (_: unit) : GenM.t (list automationCommand) :=
  (* TODO check has substs *)
  sorts <- allSorts;;
  pure (List.map a_classUp sorts).


Definition generateNotations (_: unit) : GenM.t (list automationCommand) :=
  (* TODO check has substs *)
  sorts <- allSorts;;
  substSorts_by_sort <- a_map (fun sort => 
                                 substSorts <- substOf sort;;
                                 pure (substSorts, sort))
                              sorts;;
  let notSubstFuns := List.map (fun '(substSorts, sort) => a_notSubstFun substSorts sort) substSorts_by_sort in
  let notSubsts := List.map (fun '(substSorts, sort) => a_notSubst substSorts sort) substSorts_by_sort in
  let notRenFuns := List.map (fun '(substSorts, sort) => a_notRenFun substSorts sort) substSorts_by_sort in
  let notRens := List.map (fun '(substSorts, sort) => a_notRen substSorts sort) substSorts_by_sort in
  (* for all open sorts *)
  upsByComponent <- getUpsPure tt;;
  let notUps := List.map (fun '(boundSort, sort) => a_notUp boundSort sort) (List.concat upsByComponent) in
  openSorts <- a_filter isOpen sorts;;
  let notUps2 := List.map a_notUp2 openSorts in
  let notVars := List.map a_notVar openSorts in
  (* let notVarInsts := List.map a_notVarInst openSorts in *)
  let notVarConstrs := List.map a_notVarConstr openSorts in
  pure (List.concat [
    notSubstFuns; notSubsts; notRenFuns; notRens;
    notUps; notUps2; notVars; notVarConstrs
  ]).

(* TODO *)
Definition generateInstances (_: unit) : GenM.t (list automationCommand) :=
  pure [].

From ASUB Require Import Termutil Flags SubstTy.

Definition generateProperInstancesForSort (sort: tId) : GenM.t (list automationCommand) :=
  (* TODO assuming subst and ren for all sorts *)
  substSorts <- substOf sort;;
  sc <- get_scope_type;;
  let iw := is_wellscoped sc in
  let ss := List.concat [
    List.map (sep "m") substSorts;
    List.map (sep "n") substSorts
  ] in
  pure [
    a_properInstance (sepd ["ren"; sort; "morphism"]) 
                     ss
                     substSorts 
                     (renName sort)
                     (extRenName sort);
    a_properInstance (sepd ["subst"; sort; "morphism"]) 
                     ss
                     substSorts 
                     (substName sort)
                     (extName sort)
  ].

Definition generateProperInstances (_: unit) : GenM.t (list automationCommand) :=
  sorts <- allSorts;;
  a_concat_map generateProperInstancesForSort sorts.

Definition genRewrites (sort: tId) : GenM.t (list tactic) :=
  hasRen <- hasRenaming sort;;
  let lemmaNames :=
    if hasRen
    then [ substSubstName sort;
           renSubstName sort;
           substRenName sort;
           renRenName sort;
           varLRenName sort;
           varLName sort;
           rinstIdName sort;
           instIdName sort
      ]
    else [ substSubstName sort;
           varLName sort;
           instIdName sort
      ]
  in
  let lemmas := List.map
                  (fun n => t_setoid_rewrite n)
                  lemmaNames in
  pure lemmas.


(* check again which things to unfold  *)
Definition genUnfold (_: unit) : GenM.t tactic :=
  ups <- getUps' tt;;
  pure (t_unfold []).

(* same as rewrites  *)
Definition genCbn (sorts: list tId) : GenM.t tactic :=
  opNames <- a_concat_map
              (fun sort => 
                 hasRen <- hasRenaming sort;;
                 if hasRen
                 then pure [ substName sort; renName sort ]
                 else pure [ substName sort ])
              sorts;;
  pure (t_cbn opNames).


Definition genAsimpl' (_: unit) : GenM.t (automationCommand) :=
  sorts <- allSorts;;
  asimplRewrites <- a_concat_map genRewrites sorts;;
  asimplCbn <- genCbn sorts;;
  asimplUnfold <- genUnfold tt;;
  let firstArgs := List.app asimplRewrites
                            [asimplUnfold; asimplCbn; t_call "fsimpl" ] in
  let tac := t_repeat (t_first (List.map t_progress firstArgs)) in
  pure (a_ltac "asimpl'" tac).

Definition genAutoUnfoldFunctions (_: unit) : GenM.t (list string) :=
  pure [].

Definition genAutoUnfold (_: unit) : GenM.t (automationCommand) :=
  autoUnfoldFunctions <- genAutoUnfoldFunctions tt;;
  let tac := t_repeat (t_unfold autoUnfoldFunctions) in
  pure (a_ltac "auto_unfold" tac).

 Definition genAutoUnfoldStar (_: unit) : GenM.t (automationCommand) :=
  autoUnfoldFunctions <- genAutoUnfoldFunctions tt;;
  let tac := t_repeat (t_unfold_loc true autoUnfoldFunctions) in
  pure (a_ltacNotation """auto_unfold"" ""in"" ""*""" tac).
  
Definition genAsimpl (_: unit) : GenM.t (automationCommand) :=
  let tac := t_then [ t_call "check_no_evars";
                      t_call "auto_unfold in *";
                      t_call "asimpl'";
                      t_call "minimize" ] in
  pure (a_ltac "asimpl" tac).

Definition genAsimplHyp (_: unit) : GenM.t (automationCommand) :=
  let tac := t_then [ t_call_args "revert" ["J"];
                      t_call "asimpl";
                      t_intros ["J"] ] in
  pure (a_ltacNotation """asimpl"" ""in"" hyp(J)" tac).

Definition genAutoCase (_: unit) : GenM.t (automationCommand) :=
  let innerTac := t_then [ t_call "asimpl"; 
                           t_cbn [];
                           t_call "eauto" ] in
  let tac := t_call_tac "auto_case" innerTac in 
  pure (a_ltacNotation """auto_case""" tac).

Definition genSubstify (_: unit) : GenM.t (automationCommand) :=
  sorts <- allSorts;;
  renSorts <- a_filter hasRenaming sorts;;
  let substifyLemmas := List.map (fun sort => "rinstInst_" ++ sort) renSorts in
  let rewrites := List.map (fun t => t_try (t_repeat (t_setoid_rewrite t))) substifyLemmas in
  let tac := t_then (t_call "auto_unfold" :: rewrites) in 
  pure (a_ltac "substify" tac).

Definition genRenamify (_: unit) : GenM.t (automationCommand) :=
  sorts <- allSorts;;
  renSorts <- a_filter hasRenaming sorts;;
  let renamifyLemmas := List.map (fun sort => "rinstInst_" ++ sort) renSorts in
  let rewrites := List.map (fun t => t_try (t_setoid_rewrite_lr true t)) renamifyLemmas in
  let tac := t_then (t_call "auto_unfold" :: rewrites) in 
  pure (a_ltac "renamify" tac).

Definition generateTactics (_: unit) : GenM.t (list automationCommand) :=
  let tactic_funs := [
    genAutoUnfold;
    genAutoUnfoldStar;
    genAsimpl';
    genAsimpl;
    genAsimplHyp;
    genAutoCase;
    genSubstify;
    genRenamify
  ] in
  a_map (fun f => f tt) tactic_funs.

(** * Generate all of the automation (typeclasses, notation, tactics, ...) for the rewriting system. *)
Definition generateAutomationM (_: unit) : GenM.t string :=
  let automation_funs := [
    generateTypeclasses;
    generateInstances;
    generateNotations;
    generateProperInstances;
    generateTactics
  ] in
  automation <- a_concat_map (fun f => f tt) automation_funs;;
  pure (pr_automation automation).

From MetaCoq.Template Require Import All.
From ASUB Require Import TemplateMonadUtils.
Import TemplateMonadNotations.

Definition generateAutomation (info: genInfo): TemplateMonadSet unit :=
  match GenM.runInfo (generateAutomationM tt) info with
  | inl e => tmFail ("Failed generating automation: " ++ e)
  | inr (_, _, automation) =>
    automation <- tmEval all automation;;
    (* this generates a Coq message that is displayed to the user *)
    tmMsg "Please copy the following output into your Coq buffer. It is the automation generated by Autosubst MetaCoq.";;
    tmMsg automation
  end.


