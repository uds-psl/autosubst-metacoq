
From ASUB Require Import AL hsig quotes utils termutil monad tmUtils.
From MetaCoq.Template Require Import All.
Require Import List String.
Import ListNotations MonadNotation.
Open Scope string.


Record State := { st_names : list string;
                  st_env : SFMap.t term }.

Definition empty_state := {| st_names := []; st_env := SFMap.empty |}.
Definition env_state env := {| st_names := []; st_env := env |}.

Definition update_env (env env' : SFMap.t term) : SFMap.t term :=
  SFMap.union env env'.

Definition locate_name (name: string) : TemplateMonad (string * term) :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind => tmReturn (name, tInd ind [])
  | ConstructRef ind n => tmReturn (name, tConstruct ind n [])
  | ConstRef kn => tmReturn (name, tConst kn [])
  | _ => tmFail (String.append "unknown name or name is not an inductive/constructor/constant: " name)
  end.

Definition tm_update_env '{| st_names := names; st_env := env |} : TemplateMonad (SFMap.t term) :=
  env_list' <- tm_mapM locate_name names;;
  let env' := SFMap.fromList env_list' in
  tmReturn (update_env env' env). 
  
Module GenM.

  (* The RWSE monad that we use to generate the lemmas *)
  Module RWSE_params.
    Definition R := Signature.
    Definition W := string.
    Definition S := State.
    Definition E := string.

    Definition append := String.append.
    Definition empty := ""%string.
  End RWSE_params.

  Module M := RWSE RWSE_params.
  Include M.
  Import Notations.

  Definition register_name (name: string) : t unit :=
    '{| st_names := names; st_env := env |} <- get;;
    put {| st_names := name :: names; st_env := env |}.

  Definition register_names (names': list string) : t unit :=
    '{| st_names := names; st_env := env |} <- get;;
    put {| st_names := app names' names; st_env := env |}.

  Definition env_get (s: string) : t term :=
    env <- gets st_env;;
    match SFMap.find env s with
    | None => error (String.append "Not found: " s)
    | Some t => pure t
    end.
End GenM.
  
Module inductives.
  Import GenM GenM.Notations.
  
  (* The following definitions are just hardcoded for System F ty *)
  Definition isOpen (sort: string) : bool := true.
  Definition genVarArg (sort: string) : term := nat_q.

  (* Returns the constructors of a sort in the spec *)
  Definition constructors (sort: string) : t (list Constructor) :=
    spec <- asks sigSpec;;
    (* let spec := ltac:(native_compute in spec; exact spec) in *)
    match SFMap.find spec sort with
    (* match SFMap.find Hsig_example.mySigSpec sort with *)
    | Some cs => M.pure cs
    | None => M.error "not found"%string
    end.

  Eval hnf in (constructors "ty").
  
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
    let '{| con_parameters := con_parameters;
            con_name := _;
            con_positions := con_positions |} := c in
    let up_n_x := mapi (fun n => genArg sort (n + db)) con_positions in
    (* todo take care of parameters *)
    let targetType := tRel (List.length up_n_x) in
    mkArrRev up_n_x targetType.

  (* Generates a one_inductive_entry which holds the information for a single inductive type for a given sort based on the spec *)
  Definition genOneInductive sort (db: nat) : t one_inductive_entry :=
    ctors <- constructors sort;;
    (* introScopeVar *)
    let ctor_names : list cId := map con_name ctors in
    let ctor_types := map (genConstructor sort db) ctors in
    let '(ctor_names, ctor_types) :=
        if isOpen sort
        then (("var_" ++ sort) :: ctor_names, genVar sort db :: ctor_types)
        else (ctor_names, ctor_types) in
    (* register the type & ctor names to be put in the environment later *)
    register_names (sort :: ctor_names);;
    pure {|
        mind_entry_typename := sort;
        mind_entry_arity := tSort Universe.type0;
        mind_entry_consnames := ctor_names;
        mind_entry_lc := ctor_types 
      |}.

  (* Compute genOneInductive "ty"%string 0. *)

  (* Generates a mutual_inductive_entry which combines multiple one_inductive_entry's into a mutual inductive type definition.
 For each sort in the component, a one_inductive_entry is generated *)
  Definition genMutualInductive (component: list cId) : t mutual_inductive_entry :=
    (* debruijn indices are counted backwards so we revert the list before mapping over it *)
    let rcomponent := rev component in
    entries <- a_mapi (fun n s => genOneInductive s n) rcomponent;;
    pure {|
        mind_entry_record := None;
        mind_entry_finite := Finite;
        mind_entry_params := [];
        mind_entry_inds := rev entries; (* need to revert again *)
        mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
        mind_entry_template := false;
        mind_entry_variance := None;
        mind_entry_private := None;
      |}.

End inductives.

Import inductives.

Definition mkInductive (component: list cId) : TemplateMonad (SFMap.t term) :=
  match GenM.run (genMutualInductive component) Hsig_example.mySig empty_state with
  | inr (_, state, mind) =>
    (tmMkInductive mind;;
     tm_update_env state)
  | inl e => tmFail e
  end.

(* MetaCoq Run (mkInductive ["ty"%string] >>= tmEval TemplateMonad.Common.all >>= tmPrint). *)

Module congruences.
  Import GenM GenM.Notations.

  Definition eq_ ty t0 t1 := tApp eq_q [ty; t0; t1].
  
  Definition lambda_ (bname: string) (ty body: term) :=
    tLambda {| binder_name := nNamed bname; binder_relevance := Relevant |} ty body.
  
  Fixpoint add_binders (bs: list (string * term)): term -> term :=
    match bs with
    | [] => fun t => t
    | (bname, btype) :: bs =>
      fun t => lambda_ bname btype (add_binders bs t)
    end.

  Definition dbmap_empty : tId -> nat := fun _ => 666.
  Definition dbmap_add (s: tId) (dbmap: tId -> nat) :=
    fun s' =>
      if eqb s s' then 0
      else S (dbmap s').
  Fixpoint dbmap_adds (ss: list tId) (dbmap: tId -> nat) :=
    match ss with
    | [] => dbmap
    | s :: ss =>
      dbmap_adds ss (dbmap_add s dbmap)
    end.
  Definition dbmap_get (dbmap: tId -> nat) (s: tId) : term := tRel (dbmap s).

  Definition getArgType (p: Position) : t term :=
    let '{| pos_binders := _;
            pos_head := Atom sort |} := p in
    env_get sort.
        
  (* generates the terms for the congruence lemmas for a constructor of an inductive type
   Instead of sort I should get ty_q as an argument *)
  Definition genCongruence (sort: tId) (ctor: Constructor) : t (string * term) :=
    let '{| con_parameters := con_parameters;
            con_name := con_name;
            con_positions := con_positions |} := ctor in
    let dbmap := dbmap_empty in
    sort_tm <- env_get sort;;
    ctor_tm <- env_get con_name;;
    (* arguments to the lemma *)
    let ss := getPattern "s" con_positions in
    let ts := getPattern "t" con_positions in
    let dbmap := dbmap_adds (ss ++ ts) dbmap in
    (* but this works also to reference the s and t when generating the H's because for each H, the corresponding s and t are bound at the same distance. *)
    let t_deBruijn := (List.length ts) - 1 in
    let s_deBruijn := (List.length ss) + t_deBruijn in
    arg_tys <- amap getArgType con_positions;;
    let eqs := map (fun arg_ty => eq_ arg_ty (tRel s_deBruijn) (tRel t_deBruijn)) arg_tys in
    let Hs := getPattern "H" con_positions in
    let dbmap := dbmap_adds Hs dbmap in
    (* building the binders of the lemma *)
    let bss := combine ss arg_tys in
    let bts := combine ts arg_tys in
    let beqs := combine Hs eqs in
    let proof := add_binders (bss ++ bts ++ beqs) in
    (* body of the lemma *)
    (* the last implicit argument to eq_trans will always be the same *)
    let impl2 := tApp ctor_tm (map (dbmap_get dbmap) ts) in
    let (_, proof') := fold_right (fun '(s, t, H) '(i, tm) =>
                                    let impl0 := tApp ctor_tm (map (dbmap_get dbmap) (firstn (i - 1) ts ++ skipn (i - 1) ss)) in
                                    let impl1 := tApp ctor_tm (map (dbmap_get dbmap) (firstn i ts ++ skipn i ss)) in
                                    let feq_dbmap := dbmap_add "x" dbmap in
                                    let feq_args := (map (dbmap_get feq_dbmap) (firstn (i - 1) ts ++ ["x"] ++ skipn i ss)) in
                                    let feq_lam := lambda_ "x" hole (tApp ctor_tm feq_args) in
                                    let feq := tApp f_equal_q [sort_tm; sort_tm; feq_lam; dbmap_get dbmap s; dbmap_get dbmap t; dbmap_get dbmap H] in
                                    (i - 1, tApp eq_trans_q [sort_tm; impl0; impl1; impl2; feq; tm])
                                 )
                                 (List.length con_positions, tApp eq_refl_q [sort_tm; impl2]) (combine (combine ss ts) Hs) in
    (* generate and register lemma name *)
    let lemma_name := String.append "congr_" con_name in
    register_name lemma_name;;
    pure (lemma_name, proof proof').

  Definition myctor := {| con_parameters := [];
                          con_name := "arr";
                          con_positions := [ {| pos_binders := []; pos_head := Atom "ty" |};
                                           {| pos_binders := []; pos_head := Atom "ty" |} ] |}.

  (* generates the terms for the congruence lemmas of the
     constructors of an inductive type *)
  (* Definition genCongruences (env: string -> t term) (sort: tId) : t (list (string * term)) := *)
  (*   ctors <- constructors sort;; *)
  (*   amap (genCongruence env sort) ctors. *)

End congruences.

Import congruences.

Definition mkCongruences (env: SFMap.t term) (sort: tId) : TemplateMonad (SFMap.t term) :=
  match GenM.run (genCongruence sort myctor) Hsig_example.mySig (env_state env) with
  | inl e => tmFail e
  | inr (_, state, (lname, t)) =>
    body <- tmUnquote t;;
    body <- tmEval lazy (my_projT2 body);;
    tmDefinitionRed lname (Some TemplateMonad.Common.all) body;;
    tm_update_env state
  end. 


Definition generate (component: list tId) : TemplateMonad (SFMap.t term) :=
  env <- mkInductive component;;
  env <- mkCongruences env "ty";;
  tmReturn env.

MetaCoq Run (generate ["ty"] >>= tmEval lazy >>= tmPrint).

MetaCoq Run (tmLocate1 "congr_arr" >>= tmPrint).
  

(* Definition tmGenUpS (binder: Binder) (sort: tId) := *)
(*   let '(m, bm) = introScopeVarS "m" in *)
(*   let '(ns, bns) = introScopeVar "n" sort in *)
(*   let '(sigma, bsigma) = genSubstS "sigma" m ns sort in *)
(*   (* let sigma = upSubstT binder sort ns sigma in *) *)
(*   let '(_, bpms) = bparameters binder in *)
(*   let m' = succ_ m sort binder in *)
(*   let n' = upSubst sort [binder] ns in *)
(*   tmDefinition (up_ sort binder) tm. *)

(* MetaCoq Run (tmGenUpS (Single "") ""). *)
