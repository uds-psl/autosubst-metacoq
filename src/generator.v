
From ASUB Require Import AL hsig quotes util monad.
From MetaCoq.Template Require Import All.
Require Import List String.
Import ListNotations.

Axiom fls : False.

Module S := Hsig_example.
Module RWSE_params.
  Definition R := signature.
  Definition W := string.
  Definition S := unit.
  Definition E := string.

  Definition append := String.append.
  Definition empty := ""%string.
End RWSE_params.

Module M := RWSE RWSE_params.
Import M.

(* The following definitions are just hardcoded for System F ty *)
Definition isOpen (sort: string) : bool := true.
Definition genVarArg (sort: string) : term := nat_q.

(* Returns the constructors of a sort in the spec *)
Definition constructors (sort: string) : M (list Constructor) :=
  match AL.M.find sort S.mySigSpec with
  | Some cs => ret cs
  | None => error "not found"%string
  end.

(* Generates the type of a variable constructor for a sort
 db : base deBruijn index, should move into a reader monad *)
Definition genVar (sort: string) (db: nat) : term :=
  let s := genVarArg sort in
  let typ := mkArr nat_q [tRel (S db)] in
  typ.

(* generates the type of a single argument of a constructor *)
Definition genArg (sort: string) (db: nat) (pos : Position) :=
  let '{| pos_binders := pos_binders; pos_head := pos_head |} := pos in
  match pos_head with
  | Atom argSort =>
    (* todo lift scopes *)
    if eqb sort argSort then tRel db else ref_ argSort
  end.

(* Generates the type of a given constructor for a sort
 db: base deBruijn index, should move into a reader monad *)
Definition genConstructor (sort: string) (db: nat) (c: Constructor) : term :=
  let '{| con_parameters := con_parameters; con_name := _; con_positions := con_positions |} := c in
  let up_n_x := mapi (fun n => genArg sort (n + db)) con_positions in
  (* todo take care of parameters *)
  let targetType := tRel (List.length up_n_x) in
  mkArrRev up_n_x targetType.
  
(* Generates a one_inductive_entry which holds the information for a single inductive type for a given sort based on the spec *)
Definition genOneInductive sort (db: nat) : M one_inductive_entry :=
  bind (constructors sort) (fun cs =>
        (* introScopeVar *)
        let restNames : list cId := map con_name cs in
        let restTypes := map (genConstructor sort db) cs in
        let '(cnames, ctypes) := if isOpen sort
                                 then (("var_" ++ sort)%string :: restNames, genVar sort db :: restTypes)
                                 else (restNames, restTypes) in
        ret {|
            mind_entry_typename := sort;
            mind_entry_arity := tSort Universe.type0;
            mind_entry_consnames := cnames;
            mind_entry_lc := ctypes 
          |}).

Compute genOneInductive "ty"%string 0.

(* Generates a mutual_inductive_entry which combines multiple one_inductive_entry's into a mutual inductive type definition.
 For each sort in the component, a one_inductive_entry is generated *)
Definition genMutualInductive (component: list cId) : M mutual_inductive_entry :=
  (* debruijn indices are counted backwards *)
  let rcomponent := rev component in
  bind (a_mapi (fun n s => genOneInductive s n) rcomponent) (fun entries =>
      ret {|
          mind_entry_record := None;
          mind_entry_finite := Finite;
          mind_entry_params := [];
          mind_entry_inds := rev entries;
          mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
          mind_entry_template := false;
          mind_entry_variance := None;
          mind_entry_private := None;
        |}).

Definition mkInductive (component: list cId) : TemplateMonad unit :=
  match run (genMutualInductive component) S.mySig tt with
  | inr mind =>
    (tmPrint "hello"%string;;
    tmMkInductive mind;;
    tmReturn tt)
  | inl s =>
    (tmPrint s;;
    tmReturn tt)
  end.

MetaCoq Run (mkInductive ["ty"%string]).


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
