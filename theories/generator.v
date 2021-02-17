
From ASUB Require Import AL core quotes util.
From MetaCoq.Template Require Import utils All.
Import ListNotations MonadNotation Nat.

Axiom fls : False.

Module S := Hsig_example.

(* The following definitions are just hardcoded for System F ty *)
Definition isOpen (sort: string) : bool := true.
Definition genVarArg (sort: string) : term := nat_q.
Definition constructors (sort: string) : TemplateMonad (list constructor) :=
  match AL.M.find sort S.mySigSpec with
  | Some cs => tmReturn cs
  | None => tmFail "not found"
  end.

Definition genVar (sort: string) (db: nat) : term :=
  let s := genVarArg sort in
  let typ := mkArr nat_q [tRel (S db)] in
  typ.

Definition genConstructor (sort: string) (db: nat) (c: constructor) : term :=
  tRel db. 

(* Set Printing  *)
Definition genOneInductive sort (db: nat) : TemplateMonad one_inductive_entry :=
  cs <- constructors sort;;
  (* introScopeVar *)
  let restNames : list cId := map cname cs in
  let restTypes := map (genConstructor sort db) cs in
  let '(cnames, ctypes) := if isOpen sort
                           then ("var_"^sort :: restNames, genVar sort db :: restTypes)
                           else (restNames, restTypes) in
  tmReturn {|
    mind_entry_typename := sort;
    mind_entry_arity := tSort Universe.type0;
    mind_entry_consnames := cnames;
    mind_entry_lc := ctypes 
  |}.
  
Definition genMInductive (component: list cId) : mutual_inductive_entry :=
  (* debruijn indices are counted backwards *)
  let component := rev component in
  let entries := rev (map (fun n s => genOneInductive s n) component) in
  {|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := entries;
    mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
    mind_entry_template := false;
    mind_entry_variance := None;
    mind_entry_private := None;
  |}.

Definition mkInductive (component: list cId) : TemplateMonad unit :=
  let mind := genInductive component in
  tmMkInductive mind.

MetaCoq Run (mkInductive ["ty"]).


Definition tmGenUpS (binder: Binder) (sort: tId) :=
  let '(m, bm) = introScopeVarS "m" in
  let '(ns, bns) = introScopeVar "n" sort in
  let '(sigma, bsigma) = genSubstS "sigma" m ns sort in
  (* let sigma = upSubstT binder sort ns sigma in *)
  let '(_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = upSubst sort [binder] ns in
  tmDefinition (up_ sort binder) tm.

MetaCoq Run (tmGenUpS (Single "") "").
