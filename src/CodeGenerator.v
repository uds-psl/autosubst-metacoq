Require Import List String.
Import ListNotations.

#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
Import MonadNotation.
From ASUB Require Import AssocList Language Quotes Utils DeBruijnMap Monad TemplateMonadUtils Names GallinaGen GenM Termutil SubstTy.

Module genCode.
  Import GenM.Notations GenM.

  (** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the current component.
   ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
  Definition getUps (component: list tId) (remove: list (tId * tId)) : (list (tId * tId) * list (Binder * tId)) :=
    let cart := cartesian_product component component in
    let cart := list_diff_prod cart remove in
    let singles := map (fun '(x, y) => (Single x, y)) cart in
    (* let blists := map (fun '(x, y) => (BinderList ("p", x), y)) cart in *)
    (* TODO scoped append blists *)
    (cart, singles).
  
  Definition upList_ty :=
    let m := substSorts <- substOf "ty";;
             let '(_, upList) := getUps substSorts [] in
             pure upList in
    match testrun m with
    | inl _ => []
    | inr (_, _, x) => x
    end.

  Definition upList_tm :=
    let m := substSorts_ty <- substOf "ty";;
             substSorts <- substOf "tm";;
             let '(combinations, _) := getUps substSorts_ty [] in
             let '(_, upList) := getUps substSorts combinations in
             pure upList in
    match testrun m with
    | inr (_, _, x) => x
    | _ => []
    end.

End genCode.
Import genCode.


Module helpers.
  Record genInfo := { in_env : SFMap.t term; in_implicits : SFMap.t nat }.

  (** * TemplateMonad function to generate and unquote inductive types.
   ** * It returns an updated environment that contains the new types and their constructors. *)
  Definition mkInductive (m: GenM.t mutual_inductive_entry) (fl: Flags) (s: Signature) (info : genInfo) : TemplateMonad genInfo :=
    let env := info.(in_env) in
    match GenM.run m {| R_flags := fl; R_sig := s; R_env := env |} (initial_state info.(in_implicits)) with
    | inl e => tmFail e
    | inr (_, {| st_names := names; st_implicits := implicits |}, mind) =>
      tmMkInductive mind;;
      env' <- tm_update_env names env;;
      tmReturn {| in_env := env'; in_implicits := implicits |}
    end.

  Definition mkLemmasTyped (m: GenM.t (list lemma)) (fl: Flags) (s: Signature) (info: genInfo) : TemplateMonad genInfo :=
    let env := info.(in_env) in
    match GenM.run m {| R_flags := fl; R_sig := s; R_env := env |} (initial_state info.(in_implicits)) with
    | inl e => tmFail e
    | inr (_, {| st_names := names; st_implicits := implicits |}, lemmas) =>
      tm_mapM tmTypedDefinition lemmas;; 
      env' <- tm_update_env names env;;
      tmReturn {| in_env := env'; in_implicits := implicits |}
    end. 

  (* give a name to the persistent information between code generation calls
   * Necessary because for testing we do code generation incrementally with several commands. *)
  Definition composeGeneration (infoName: string) (info: genInfo) : TemplateMonad unit :=
    info <- tmEval TemplateMonad.Common.all info;;
    tmDefinition infoName info;;
    tmReturn tt.

  Import GenM.Notations GenM.
  Definition genFixpoint (genF : tId -> t (def nterm)) (component: NEList.t tId) : t (list lemma) :=
    let componentL := NEList.to_list component in
    isRec <- isRecursive component;;
    fexprs <- a_map genF componentL;;
    buildFixpoint fexprs isRec.

End helpers.
Import helpers.


Module inductives.
  Import GenM GenM.Notations.
  
  (* Generates the type of a variable constructor for a sort
 db : base deBruijn index, should move into a reader monad *)
  Definition genVarConstrType (sort: tId) (ns: substScope) : t nterm :=
    s <- genVarArg sort ns;;
    scope_type <- get_scope_type;;
    pure (mknArrRev [s] (app_sort sort scope_type ns)).

  (* generates the type of a single argument of a constructor *)
  Definition genArg (sort: string) (ns: substScope) (pos : Position) : t nterm :=
    let '{| pos_binders := pos_binders; pos_head := pos_head |} := pos in
    match pos_head with
    | Atom argSort =>
      upScopes <- castUpSubstScope sort pos_binders argSort ns;;
      scope_type <- get_scope_type;;
      pure (app_sort argSort scope_type upScopes)
    (* TODO implement funapp case *)
    | FunApp _ _ _ => pure nat_
    end.

  (** * Generates the type of a given constructor for a sort *)
  Definition genConstructor (sort: tId) (ns: substScope) (c: Constructor) : t nterm :=
    let '{| con_parameters := con_parameters;
            con_name := _;
            con_positions := con_positions |} := c in
    up_n_x <- a_map (genArg sort ns) con_positions;;
    scope_type <- get_scope_type;;
    (* TODO take care of parameters *)
    let targetType := app_sort sort scope_type ns in
    pure (mknArrRev up_n_x targetType).

  (** * Generates a one_inductive_entry which holds the information for a single inductive type for a given sort based on the spec *)
  Definition genOneInductive (dbmap: DB.t) (ns: substScope) (bns: list gallinaArg) (sort: tId) : t one_inductive_entry :=
    ctors <- constructors sort;;
    sortIsOpen <- isOpen sort;;
    let ctor_names := map con_name ctors in
    ctor_ntypes <- a_map (genConstructor sort ns) ctors;;
    (* maybe we also add a variable constructor *)
    '(ctor_names, ctor_ntypes) <-
        (if sortIsOpen
        then
          (* process_implicits (varConstrName sort) bns;; *)
          varConstrType <- genVarConstrType sort ns;;
          pure (varConstrName sort :: ctor_names, varConstrType :: ctor_ntypes)
        else pure (ctor_names, ctor_ntypes));;
    (* register the type & ctor names to be put in the environment later *)
    register_names (sort :: ctor_names);;
    (* translate into TemplateCoq terms *)
    ctor_types <- a_map (translate' dbmap) ctor_ntypes;;
    (* compute arity. Depends on if we are wellscoped *)
    scope_type <- get_scope_type;;
    let arity := if is_wellscoped scope_type
                 then scoped_arity
                 else unscoped_arity in
    pure {|
        mind_entry_typename := sort;
        mind_entry_arity := arity;
        mind_entry_consnames := ctor_names;
        mind_entry_lc := ctor_types 
      |}.

  (** * Convert my binder representation to the parameter representation in a mutual_inductive_entry *)
  Definition binder_to_param '{| g_name := bname; g_type := btype |} : t context_decl :=
    type <- translate' DB.empty btype;;
    pure {| decl_name := {| binder_name := nNamed bname; binder_relevance := Relevant |};
            decl_body := None;
            decl_type := type |}.

  (** * Generates a mutual_inductive_entry which combines multiple one_inductive_entry's into a mutual inductive type definition.
   ** * For each sort in the component, a one_inductive_entry is generated *)
  Definition genMutualInductive (component: NEList.t tId) : t mutual_inductive_entry :=
    (* the entries already use deBruin numbers as if they were sequentially bound.
     * i.e. the last entry has index 0. Therefore we can just add the component *)
    (* only generate the definable sorts *)
    let head_sort := NEList.hd component in
    '(ns, bns) <- introScopeVar "n" head_sort;;
    params <- a_map binder_to_param bns;;
    let componentL := NEList.to_list component in
    def_sorts <- a_filter isDefinable componentL;;
    let dbmap := DB.adds def_sorts DB.empty in
    scope_type <- get_scope_type;;
    let dbmap := if is_wellscoped scope_type
                 then DB.adds (ss_names ns) dbmap
                 else dbmap in
    entries <- a_map (genOneInductive dbmap ns bns) def_sorts;;
    pure {|
        mind_entry_record := None;
        mind_entry_finite := Finite;
        mind_entry_params := params;
        mind_entry_inds := entries;
        mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
        mind_entry_template := false;
        mind_entry_variance := None;
        mind_entry_private := None;
      |}.

  (* Eval cbv in (run (genMutualInductive ["ty"]) Hsig_example.mySig empty_state). *)
End inductives.
Import inductives.

(* Definition default_flags := {| fl_scope_type := Wellscoped |}. *)
MetaCoq Run (mkInductive (genMutualInductive (NEList.from_list' ["ty"%string])) default_flags Hsig_example.mySig {| in_env := GenM.initial_env; in_implicits := SFMap.empty |}
                         >>= tmEval TemplateMonad.Common.all
                         >>= mkInductive (genMutualInductive (NEList.from_list' ["tm"; "vl"])) default_flags Hsig_example.mySig
                         >>= composeGeneration "env0").


Module congruences.
  Import GenM GenM.Notations.

  (** get the quoted type of an argument *)
  Definition getArgType (p: Position) : t nterm :=
    let '{| pos_binders := _;
            pos_head := hd |} := p in
    let sort := match hd with
                | Atom sort => sort
                (* TODO funapp *)
                | FunApp _ _ _ => ""
                end in
    pure (nRef sort).

  (** * generates the terms for the congruence lemmas for a constructor of an inductive type *)
  Definition genCongruence (sort: tId) (ctor: Constructor) : t nlemma :=
    let '{| con_parameters := con_parameters;
            con_name := con_name;
            con_positions := con_positions |} := ctor in
    '(ms, bms) <- introScopeVar "m" sort;;
    scope_type <- get_scope_type;;
    (* arguments to the lemma *)
    let ss := getPattern "s" con_positions in
    let ts := getPattern "t" con_positions in
    arg_tys <- a_map (genArg sort ms) con_positions;;
    let Hs := getPattern "H" con_positions in
    (* building the binders of the lemma *)
    let bss := map2 explArg ss arg_tys in
    let bts := map2 explArg ts arg_tys in
    let eqs := map2 (fun s t => eq_ (nRef s) (nRef t)) ss ts in
    let beqs := map2 explArg Hs eqs in
    (* generate the type of the lemma *)
    let innerType := eq_ (app_constr con_name scope_type ms (List.map nRef ss))
                         (app_constr con_name scope_type ms (List.map nRef ts)) in
    (* body of the lemma *)
    let (_, innerProof) := fold_left
                         (fun '(i, t) H =>
                            let feq_args := map nRef (firstn i ts ++ ["x"] ++ skipn (S i) ss) in
                            let feq_lam := abs_ref "x" (app_constr con_name scope_type ms feq_args) in
                            let feq := f_equal_ feq_lam nHole nHole (nRef H) in
                            (S i, eq_trans_ t feq))
                         Hs
                         (0, eq_refl_) in
    (* generate and register lemma name *)
    let name := congrName con_name in
    process_lemma name (bms ++ bss ++ bts ++ beqs) innerType innerProof.


  (** * generates the terms for the congruence lemmas of the constructors of an inductive type *)
  Definition genCongruences (sort: tId) : t (list lemma) :=
    ctors <- constructors sort;;
    a_map (fun ctor => translate_lemma (genCongruence sort ctor)) ctors.
End congruences.
Import congruences.

MetaCoq Run (mkLemmasTyped (genCongruences "ty") default_flags Hsig_example.mySig env0
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genCongruences "tm") default_flags Hsig_example.mySig
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genCongruences "vl") default_flags Hsig_example.mySig
                           >>= composeGeneration "env1").

Module traversal.
  Import GenM.Notations GenM.
  
  (* TODO implement *)
  (* Definition mk_underscore_pattern (scope: tId) := []. *)

  Definition hasArgs (sort: tId) : t bool :=
    substSorts <- substOf sort;;
    match substSorts with
    | [] => pure false
    | _ => pure true
    end.

  Definition branch_ (underscoreNum: nat) (binderNames: list string) (body: nterm) : (nat * nterm) :=
    let paramNum := underscoreNum + List.length binderNames in
    let binders := List.map (fun name => explArg name nHole) binderNames in
    let body := add_binders binders body in
    (paramNum, body).
  
  Definition mk_var_pattern (sort: tId) (var_case_body: nterm -> t nterm) : t (list (nat * nterm)) :=
    sortIsOpen <- isOpen sort;;
    if sortIsOpen
    then
      let s0 := "s0" in
      var_body <- var_case_body (nRef s0);;
      pure [ branch_ 0 [s0] var_body ]
    else pure [].

  Fixpoint arg_map (sort: tId) (args: list substTy) (nameF: string -> string) (no_args: nterm -> nterm) (funsem: string -> list nterm -> nterm) (bs: list Binder) (arg: ArgumentHead) :=
    match arg with
    | Atom y =>
      b <- hasArgs y;;
      args <- a_map (castUpSubst sort bs y) args;;
      pure (if b
                 (* TODO can these two holes also be handled in GallinaGen?
                  * In theory it should because we have an nApp with an nRef
                  * but (nameF y) should be in the environment *)
            then nApp (nRef (nameF y)) (flat_map sty_terms args)
            else abs_ref "x" (no_args (nRef "x")))
    | FunApp f p xs =>
      res <- a_map (arg_map sort args nameF no_args funsem bs) xs;;
      pure (funsem f res)
    end.

  
  Definition mk_constr_pattern (s: string) (sort: tId) (args: list substTy) (nameF: string -> string) (no_args: nterm -> nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: string -> list nterm -> nterm) (ctor: Constructor) : t (nat * nterm) :=
    let '{| con_parameters := cparameters; con_name := cname; con_positions := cpositions |} := ctor in
    let ss := getPattern "s" cpositions in
    positions <- a_map (fun '(s, {| pos_binders := binders; pos_head := head |}) =>
                         fmap2 nApp (arg_map sort args nameF no_args funsem binders head) (pure [ nRef s ]))
                      (combine ss cpositions);;
    let paramNames := List.map fst cparameters in
    pure (branch_ 0 (List.app paramNames ss) (sem paramNames cname positions)).
  
  Definition traversal (sort: tId) (ms: substScope) (nameF: string -> string) (no_args: nterm -> nterm) (ret: nterm -> nterm) (bargs: list gallinaArg) (args: list substTy) (var_case_body: nterm -> t nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: string -> list nterm -> nterm) : t (def nterm) :=
    ctors <- constructors sort;;
    scope_type <- get_scope_type;;
    let sort_t := app_sort sort scope_type ms in
    let s := "s" in
    let lambdas := List.app bargs [explArg s (sort_t)] in
    (** * the structural argument
     * it's always the last one so it's the length of all outermost binders
     * TODO can we move all other binders outside and have the mutual fixpoint bodies only take this argument?
     * FIX: only set to length of bargs since we start counting at 0
     *)
    let argNum := List.length bargs in
    (** * the type of the fixpoint *)
    let innerType := ret (nRef s) in
    let type := add_tbinders lambdas innerType in
    (** * the body of the fixpoint *)
    var_pattern <- mk_var_pattern sort var_case_body;;
    constr_patterns <- a_map (mk_constr_pattern s sort args nameF no_args sem funsem) ctors;;
    (* TODO calculate number of parameters *)
    (* DONE fix elemination predicate. I tried putting a hole as the return type but Coq is not smart enough to infer it. But we can use the return type function we already have available. *)
    let innerBody := nCase sort 0 (nLambda s sort_t innerType) (nRef s) (List.app var_pattern constr_patterns) in
    let body := add_binders lambdas innerBody in
    let name := nameF sort in
    process_implicits name lambdas;;
    pure {| dname := aname_ name; dtype := type; dbody := body; rarg := argNum |}.

  Definition no_args_default := fun s => nApp eq_refl_ [ s ].

  (* TODO bettenr way to find out length of implicit arguments to congr.
   * It would probably be best to save that information also in the environment.
   * Like a list of all arguments where I mark which ones should be implicit *)
  Definition sem_default := (fun (paramNames: list string) cname positions =>
                               nApp (nRef (congrName cname)) (List.app (list_fill nHole (2 * List.length positions)) positions)).
    
End traversal.
Import traversal.

Module renamings.
  Import GenM.Notations GenM.

  Definition genUpRen (bs: Binder * tId) : t (string * nterm * nterm) :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(m, bm) <- introScopeVarS "m";;
    '(n, bn) <- introScopeVarS "n";;
    let '(xi, bxi) := genRenS "xi" scope_type m n in
    (* let '(_, bpms) := bparameters binder in *)
    let m_succ := succ_ m sort binder in
    let n_succ := succ_ n sort binder in
    let innerType := renT scope_type m_succ n_succ in
    let innerProof := definitionBody sort binder (up_ren_ xi) xi in
    let name := upRenName sort binder in
    process_lemma name (List.concat [bm; bn; [bxi]]) innerType innerProof.

  Definition genUpRens (bss: list (Binder * tId)) : t (list (string * term * term)) :=
    a_map (fun bs => translate_lemma (genUpRen bs)) bss.


  Definition genRenaming (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    substSorts <- substOf sort;;
    (* DONE would have to register eveything in the current component *)
    (* register_implicits (renName "ty") 2;; *)
    (* register_implicits (renName "tm") 4;; *)
    (* register_implicits (renName "vl") 4;; *)
    scope_type <- get_scope_type;;
    let ret _ := app_sort sort scope_type ns in
    traversal sort ms renName Datatypes.id ret (List.concat [bms; bns; bxis]) [ xis ]
              (fun s => toVarT <- toVar sort xis;;
                     pure (nApp (app_constr (varConstrName sort) scope_type ns []) [ nApp toVarT [ s ] ]))
              (fun paramNames cname positions => app_constr cname scope_type ns (List.app (List.map nRef paramNames) positions))
              map_.

  Definition genRenamings := genFixpoint genRenaming.
End renamings.
Import renamings.

MetaCoq Run (mkLemmasTyped (genUpRens upList_ty) default_flags Hsig_example.mySig env1
                           >>= composeGeneration "env2").

MetaCoq Run (mkLemmasTyped (genRenamings ("ty", [])) default_flags Hsig_example.mySig env2
                           >>= composeGeneration "env3").

MetaCoq Run (mkLemmasTyped (genUpRens upList_tm) default_flags Hsig_example.mySig env3
                           >>= composeGeneration "env4").

MetaCoq Run (mkLemmasTyped (genRenamings ("tm", ["vl"])) default_flags Hsig_example.mySig env4
                           >>= composeGeneration "env5").


Module substitutions.
  Import GenM.Notations GenM.

  Definition genUpSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(m, bm) <- introScopeVarS "m";;
    '(ns, bns) <- introScopeVar "n" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type m ns sort in
    (* let '(_, bpms) := bparameters binder in *)
    let m' := succ_ m sort binder in
    ns' <- upSubstScope sort [binder] ns;;
    let innerType := substT scope_type m' ns' sort in
    innerProof <- upSubstT binder sort sigma ns;;
    let name := upName sort binder in
    process_lemma name (List.concat [bm; bns; [ bsigma ]]) innerType innerProof.

  Definition genUpSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubst bs)) bss.

  (** Generate the substitution function
   ** e.g. subst_ty *)
  Definition genSubstitution (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ms ns;;
    scope_type <- get_scope_type;;
    traversal sort ms substName Datatypes.id (fun _ => app_sort sort scope_type ns) (List.concat [bms; bns; bsigmas]) [ sigmas ]
              (fun s =>
                 toVarT <- toVar sort sigmas;;
                 pure (nApp toVarT [ s ]))
              (fun paramNames cname positions => app_constr cname scope_type ns (List.app (List.map nRef paramNames) positions))
              map_.

  Definition genSubstitutions := genFixpoint genSubstitution.
    
End substitutions.
Import substitutions.

MetaCoq Run (mkLemmasTyped (genUpSubsts upList_ty) default_flags Hsig_example.mySig env5
                           >>= composeGeneration "env6").

MetaCoq Run (mkLemmasTyped (genSubstitutions ("ty", [])) default_flags Hsig_example.mySig env6
                           >>= composeGeneration "env7").

MetaCoq Run (mkLemmasTyped (genUpSubsts upList_tm) default_flags Hsig_example.mySig env7
                           >>= composeGeneration "env8").

MetaCoq Run (mkLemmasTyped (genSubstitutions ("tm", ["vl"])) default_flags Hsig_example.mySig env8
                           >>= composeGeneration "env9").

Module idsubsts.
  Import GenM.Notations GenM.

  (* TODO bit hacky but it works. the problem is that I sometimes need to quanitfy over some nat/fin
   * and I need to give it an explicit type (in OCaml it was possible to leave the type unspecified)
   * Since they are used with the lifting functions we can use upSubstScope to lift our given scope variables and then project the one we need out with toVarScope 
   *)
  Definition selectUpScopeVar (name: string) (sort: tId) (binder: Binder) (ms: substScope) : t (nterm * gallinaArg) :=
  scope_type <- get_scope_type;;
  match scope_type with
  | Unscoped => pure (nRef name, explArg name nat_)
  | Wellscoped =>
    m_var <- toVarScope sort ms;;
    pure (nRef name, explArg name (fin_ (succ_ m_var sort binder)))
  end.

  Definition genUpId (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(ms, bms) <- introScopeVar "m" sort;;
    m_var <- toVarScope sort ms;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type m_var ms sort in
    '(x, bx) <- selectUpScopeVar "x" sort binder ms;;
    let '(eq, beq) := genEqS "Eq" bx sigma (app_constr (varConstrName sort) scope_type ms []) in
    ms' <- upSubstScope sort [binder] ms;;
    (** * type *)
    let innerType := equiv_ x
                       (app_ref (upName sort binder) [ sigma ])
                       (app_constr (varConstrName sort) scope_type ms' []) in
    (** * body *)
    shift <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let t := fun (n: nterm) =>
               ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) shift)
                   (nApp eq [ n ]) in
    matchFin <- matchFin_ bx innerType x t eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (t x) in
    (** * name *)
    let name := upIdName sort binder in
    process_lemma name (List.concat [bms; [ bsigma; beq; bx ]]) innerType innerBody.
  
  Definition genUpIds (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpId bs)) bss.

  Definition genIdLemma (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ms ms;;
    substSorts <- substOf sort;;
    eqs' <- mk_var_apps sort ms;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms sigmas) eqs'
                         (fun x y s => pure (nApp (nRef (upIdName x y)) [nHole; s]));;
    let ret := fun s =>
                 eq_ (nApp (nRef (substName sort)) (List.app (sty_terms sigmas) [ s ])) s in
    traversal sort ms idSubstName no_args_default ret (List.concat [bms; bsigmas; beqs]) [ sigmas; eqs ]
              (fun s =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [ s ]))
              sem_default
              mapId_.

  Definition genIdLemmas := genFixpoint genIdLemma.

End idsubsts.
Import idsubsts.

MetaCoq Run (mkLemmasTyped (genUpIds upList_ty) default_flags Hsig_example.mySig env9 >>= composeGeneration "env10").

MetaCoq Run (mkLemmasTyped (genIdLemmas ("ty", [])) default_flags Hsig_example.mySig env10 >>= composeGeneration "env11").

MetaCoq Run (mkLemmasTyped (genUpIds upList_tm) default_flags Hsig_example.mySig env11 >>= composeGeneration "env12").

MetaCoq Run (mkLemmasTyped (genIdLemmas ("tm", ["vl"])) default_flags Hsig_example.mySig env12 >>= composeGeneration "env13").

Module extensionality.
  Import GenM.Notations GenM.

  (* TODO merge with genVar? *)
  Definition genUpVar (name: string) (sort: tId) (binder: Binder) (m: nterm) : t (nterm * gallinaArg) :=
    scope_type <- get_scope_type;;
    match scope_type with
    | Unscoped => pure (nRef name, explArg name nat_)
    | Wellscoped => pure (nRef name, explArg name (fin_ (succ_ m sort binder)))
    end.

  Definition genUpExtRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(m, bms) <- introScopeVarS "m";;
    '(n, bns) <- introScopeVarS "n";;
    let '(xi, bxi) := genRenS "xi" scope_type m n in
    let '(zeta, bzeta) := genRenS "zeta" scope_type m n in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx xi zeta in
    (* type *)
    let innerType := equiv_ x (nApp (nRef (upRenName sort binder)) [ xi ]) (nApp (nRef (upRenName sort binder)) [ zeta ]) in
    (* body *)
    matchFin <- matchFin_ bx innerType x (fun n => ap_ shift_ (nApp eq [n])) eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (nApp eq [x]) in
    (* name *)
    let name := upExtRenName sort binder in
    process_lemma name (List.concat [bms; bns; [bxi; bzeta; beq; bx ]]) innerType innerBody.
  
  Definition genUpExtRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpExtRen bs)) bss.

  
  Definition genExtRen (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    '(zetas, bzetas) <- genRen "zeta" sort ms ns;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms xis) (sty_terms zetas)
                         (fun x y s => pure (nApp (nRef (upExtRenName x y)) [nHole; nHole; s]));;
    (* type *)
    let ret := fun s => eq_ (nApp (nRef (renName sort)) (List.app (sty_terms xis) [s]))
                         (nApp (nRef (renName sort)) (List.app (sty_terms zetas) [s])) in
    traversal sort ms extRenName no_args_default ret (List.concat [bms; bns; bxis; bzetas; beqs]) [xis; zetas; eqs]
              (fun z =>
                 toVarT <- toVar sort eqs;;
                 scope_type <- get_scope_type;;
                 pure (ap_ (app_constr (varConstrName sort) scope_type ns []) (nApp toVarT [z])))
              sem_default
              mapExt_.

  Definition genExtRens (component: NEList.t tId) : t (list lemma) :=
    let componentL := NEList.to_list component in
    isRec <- isRecursive component;;
    fexprs <- a_map genExtRen componentL;;
    buildFixpoint fexprs isRec.

  
  Definition genUpExt (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(m, bms) <- introScopeVarS "m";;
    '(ns, bns) <- introScopeVar "n" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type m ns sort in
    let '(tau, btau) := genSubstS "tau" scope_type m ns sort in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx sigma tau in
    (* type *)
    let innerType := equiv_ x (nApp (nRef (upName sort binder)) [ sigma ]) (nApp (nRef (upName sort binder)) [ tau ]) in
    (* body *)
    shift <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let innerBodyHelper := fun n => ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) shift)
                                     (nApp eq [n]) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (innerBodyHelper x) in
    (* name *)
    let name := upExtName sort binder in
    process_lemma name (List.concat [bms; bns; [ bsigma; btau; beq; bx ]]) innerType innerBody.
    
  Definition genUpExts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpExt bs)) bss.

  Definition genExt (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ms ns;;
    '(taus, btaus) <- genSubst "tau" sort ms ns;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms sigmas) (sty_terms taus)
                         (fun x y s => pure (nApp (nRef (upExtName x y)) [nHole; nHole; s]));;
    let ret := fun s => eq_ (nApp (nRef (substName sort)) (List.app (sty_terms sigmas) [s]))
                         (nApp (nRef (substName sort)) (List.app (sty_terms taus) [s])) in
    traversal sort ms extName no_args_default ret (List.concat [bms; bns; bsigmas; btaus; beqs]) [sigmas; taus; eqs]
              (fun z =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [z]))
              sem_default
              mapExt_.

  Definition genExts := genFixpoint genExt.

End extensionality.
Import extensionality.

MetaCoq Run (mkLemmasTyped (genUpExtRens upList_ty) default_flags Hsig_example.mySig env13
                           >>= tmEval TemplateMonad.Common.all >>=
                           mkLemmasTyped (genUpExts upList_ty) default_flags Hsig_example.mySig
                           >>= composeGeneration "env14").

MetaCoq Run (mkLemmasTyped (genUpExtRens upList_tm) default_flags Hsig_example.mySig env14
                           >>= tmEval TemplateMonad.Common.all >>=
                           mkLemmasTyped (genUpExts upList_tm) default_flags Hsig_example.mySig
                           >>= composeGeneration "env15").

MetaCoq Run (mkLemmasTyped (genExtRens ("ty", [])) default_flags Hsig_example.mySig env15
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genExts ("ty", [])) default_flags Hsig_example.mySig
                           >>= composeGeneration "env16").

MetaCoq Run (mkLemmasTyped (genExtRens ("tm", ["vl"])) default_flags Hsig_example.mySig env16
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genExts ("tm", ["vl"])) default_flags Hsig_example.mySig
                           >>= composeGeneration "env17").

Module renRen.
  Import GenM.Notations GenM.
  
  Definition genUpRenRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(k, bks) <- introScopeVarS "k";;
    '(l, bls) <- introScopeVarS "l";;
    '(m, bms) <- introScopeVarS "m";;
    let '(xi, bxi) := genRenS "xi" scope_type k l in
    let '(zeta, bzeta) := genRenS "zeta" scope_type l m in
    let '(rho, brho) := genRenS "rho" scope_type k m in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> zeta) rho in
    (* type *)
    let innerType := equiv_ x ((nApp (nRef (upRenName sort binder)) [xi])
                                 >>> (nApp (nRef (upRenName sort binder)) [zeta]))
                            (nApp (nRef (upRenName sort binder)) [rho]) in
    (* body *)
    (* a.d. here I have to take care to also pass x to up_ren_ren and to eq in the second case of definitionBody *)
    let innerBody := definitionBody sort binder (nApp (up_ren_ren_ xi zeta rho eq) [x]) (nApp eq [x]) in
    (* name *)
    let name := upRenRenName sort binder in
    process_lemma name (List.concat [bks; bls; bms; [bxi; bzeta; brho; beq; bx]]) innerType innerBody.

  Definition genUpRenRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRenRen bs)) bss.


  Definition genCompRenRen (sort: tId) : t (def nterm) :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(xis, bxis) <- genRen "xi" sort ks ls;;
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    '(rhos, brhos) <- genRen "rho" sort ks ms;;
    '(eqs, beqs) <- genEq "Eq" sort
                         (map2 funcomp_ (sty_terms zetas) (sty_terms xis))
                         (sty_terms rhos)
                         (fun x y s => match y with
                                    | Single z => if eqb z x
                                                        (* DONE do I need an x to pass to up_ren_ren here
                                                         * No, because it needs to be forall quantified.
                                                         * Had to change up_ren_ren_ for it to work. Before, it required an x argument. Now, in genUpRenRen we make an additional application of x to the result of up_ren_ren_
                                                         * *)
                                                 then pure (up_ren_ren_ nHole nHole nHole s)
                                                 else pure s
                                    end);;
    let ret := fun s => eq_ (nApp (nRef (renName sort)) (List.app (sty_terms zetas)
                                                        [ nApp (nRef (renName sort)) (List.app (sty_terms xis) [s]) ]))
                         (nApp (nRef (renName sort)) (List.app (sty_terms rhos) [s])) in
    traversal sort ks compRenRenName no_args_default ret (List.concat [bks; bls; bms; bxis; bzetas; brhos; beqs]) [xis; zetas; rhos; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 scope_type <- get_scope_type;;
                 pure (ap_ (app_constr (varConstrName sort) scope_type ms []) (nApp toVarT [n])))
              sem_default
              mapComp_.
              
  Definition genCompRenRens := genFixpoint genCompRenRen.
End renRen.
Import renRen.

MetaCoq Run (mkLemmasTyped (genUpRenRens upList_ty) default_flags Hsig_example.mySig env17
                           >>= composeGeneration "env18").

MetaCoq Run (mkLemmasTyped (genUpRenRens upList_tm) default_flags Hsig_example.mySig env18
                           >>= composeGeneration "env19").

MetaCoq Run (mkLemmasTyped (genCompRenRens ("ty", [])) default_flags Hsig_example.mySig env19
                           >>= composeGeneration "env20").

MetaCoq Run (mkLemmasTyped (genCompRenRens ("tm", ["vl"])) default_flags Hsig_example.mySig env20
                           >>= composeGeneration "env21").

Module renSubst.
  Import GenM.Notations GenM.
  

  Definition genUpRenSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(k, bks) <- introScopeVarS "k";;
    '(l, bls) <- introScopeVarS "l";;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(xi, bxi) := genRenS "xi" scope_type k l in
    let '(tau, btau) := genSubstS "tau" scope_type l ms sort in
    let '(theta, btheta) := genSubstS "theta" scope_type k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> tau) theta in
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) [xi])
                                 >>> (app_ref (upName sort binder) [tau]))
                            (app_ref (upName sort binder) [theta]) in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper := fun n => ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (innerBodyHelper x) in
    (* name *)
    let name := upRenSubstName sort binder in
    process_lemma name (List.concat [bks; bls; bms; [bxi; btau; btheta; beq; bx]]) innerType innerBody.

  Definition genUpRenSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRenSubst bs)) bss.
  
  Definition genCompRenSubst (sort: tId) : t (def nterm) :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(xis, bxis) <- genRen "xi" sort ks ls;;
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    '(thetas, bthetas) <- genSubst "theta" sort ks ms;;
    '(eqs, beqs) <- genEq "Eq" sort
                         (map2 funcomp_ (sty_terms taus) (sty_terms xis))
                         (sty_terms thetas)
                         (fun x y s => pure (app_ref (upRenSubstName x y) [nHole; nHole; nHole; s]));;
    (* type *)
    let ret := fun s => eq_ (app_ref (substName sort) (List.app (sty_terms taus)
                                                             [app_ref (renName sort) (List.app (sty_terms xis) [s])]))
                         (app_ref (substName sort) (List.app (sty_terms thetas) [s])) in
    traversal sort ks compRenSubstName no_args_default ret (List.concat [bks; bls; bms; bxis; btaus; bthetas; beqs]) [xis; taus; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genCompRenSubsts := genFixpoint genCompRenSubst.
End renSubst.
Import renSubst.

MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_ty) default_flags Hsig_example.mySig env21
                           >>= composeGeneration "env22").

(* From ASUB Require Import core. *)

(* Lemma up_ren_subst'_ty_ty (xi : nat -> nat) (tau : nat -> ty) *)
(*   (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) : *)
(*   forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x. *)
(* Proof. *)
(* exact (up_ren_subst_ty_ty xi tau theta Eq). *)
(* Qed. *)

(* MetaCoq Run (tm_update_env {| st_names := ["up_ren_subst'_ty_ty"] |} env22 >>= tmDefinition "env22'"). *)

(* DONE the type of up_ren_subst_ty_ty is evaluated too much so this fails. If I define a lemma with the correct type I can use the same proof (see above) and then it works.
 * It worked when I used the hnf reduction strategy in my unquoteTyped helper function *)
MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_tm) default_flags Hsig_example.mySig env22
                           >>= composeGeneration "env23").

MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("ty", [])) default_flags Hsig_example.mySig env23
                           >>= composeGeneration "env24").

MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("tm", ["vl"])) default_flags Hsig_example.mySig env24
                           >>= composeGeneration "env25").

Module substRen.
  Import GenM.Notations GenM.
  

  Definition genUpSubstRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(k, bks) <- introScopeVarS "k";;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type k ls sort in
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    let '(theta, btheta) := genSubstS "theta" scope_type k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    (* sigma >> <zeta> =1 theta *)
    let '(eq, beq) := genEqS "Eq" bx (sigma >>> (app_ref (renName sort) (sty_terms zetas))) theta in
    zetas' <- upSubst sort [binder] zetas;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) [sigma])
                                 >>> (app_ref (renName sort) (sty_terms zetas')))
                            (app_ref (upName sort binder) [theta]) in
    (* body *)
    let compRenRenArgs := fun n => List.concat [map2 funcomp_ pat (sty_terms zetas);
                                            List.map (const (abs_ref "x" eq_refl_)) pat;
                                            [ nApp sigma [n] ]] in
    let innerBodyHelper n :=
        eq_trans_ (app_ref (compRenRenName sort)
                           (List.concat [pat; sty_terms zetas'; compRenRenArgs n]))
                  (eq_trans_ (eq_sym_ (app_ref (compRenRenName sort)
                                               (List.concat [sty_terms zetas; pat; compRenRenArgs n])))
                             (ap_ (app_ref (renName sort) pat)
                                  (nApp eq [n]))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (innerBodyHelper x) in
    (* name *)
    let name := upSubstRenName sort binder in
    process_lemma name (List.concat [bks; bls; bms; [bsigma]; bzetas; [btheta]; [beq]; [bx]]) innerType innerBody.

  Definition genUpSubstRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstRen bs)) bss.

  
  Definition genCompSubstRen (sort: tId) : t (def nterm) :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ks ls;;
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    '(thetas, bthetas) <- genSubst "theta" sort ks ms;;
    sigmazeta <- comp_ren_or_subst sort zetas sigmas;;
    '(eqs, beqs) <- genEq "Eq" sort sigmazeta (sty_terms thetas)
                         (fun x y s =>
                            zetas' <- castSubst sort x zetas;;
                            pure (app_ref (upSubstRenName x y)
                                          (List.concat [[nHole];
                                                       List.map (const nHole) (sty_terms zetas');
                                                       [nHole; s]])));;
    (* type *)
    let ret s := eq_ (app_ref (renName sort)
                              (List.app (sty_terms zetas)
                                        [app_ref (substName sort) (List.app (sty_terms sigmas) [s])]))
                     (app_ref (substName sort) (List.app (sty_terms thetas) [s])) in
    traversal sort ks compSubstRenName no_args_default ret (List.concat [bks; bls; bms; bsigmas; bzetas; bthetas; beqs]) [sigmas; zetas; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.

  Definition genCompSubstRens := genFixpoint genCompSubstRen.
End substRen.
Import substRen.

MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_ty) default_flags Hsig_example.mySig env25
                           >>= composeGeneration "env26").

MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_tm) default_flags Hsig_example.mySig env26
                           >>= composeGeneration "env27").

MetaCoq Run (mkLemmasTyped (genCompSubstRens ("ty", [])) default_flags Hsig_example.mySig env27
                           >>= composeGeneration "env28").

MetaCoq Run (mkLemmasTyped (genCompSubstRens ("tm", ["vl"])) default_flags Hsig_example.mySig env28
                           >>= composeGeneration "env29").

Module substSubst.
  Import GenM.Notations GenM.
  
  Definition genUpSubstSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(k, bks) <- introScopeVarS "k";;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type k ls sort in
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    let '(theta, btheta) := genSubstS "theta" scope_type k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx
                             (sigma >>> app_ref (substName sort) (sty_terms taus))
                             theta in
    taus' <- upSubst sort [binder] taus;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) [sigma])
                                 >>> (app_ref (substName sort) (sty_terms taus')))
                            (app_ref (upName sort binder) [theta]) in
    (* body *)
    pat' <- comp_ren_or_subst sort (SubstRen pat) taus;;
    let compRenSubstArgs n := List.concat [ List.map (const (abs_ref "x" eq_refl_)) pat;
                                          [ nApp sigma [n] ] ] in
    let innerBodyHelper :=
        fun n => eq_trans_ (app_ref (compRenSubstName sort) (List.concat [pat; sty_terms taus';
                                                                      map2 funcomp_ (sty_terms taus') pat;
                                                                      compRenSubstArgs n]))
                        (eq_trans_ (eq_sym_ (app_ref (compSubstRenName sort)
                                                     (List.concat [sty_terms taus; pat; pat';
                                                                  compRenSubstArgs n])))
                                   (ap_ (app_ref (renName sort) pat) (nApp eq [n]))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (innerBodyHelper x) in
    (* name *)
    let name := upSubstSubstName sort binder in
    process_lemma name (List.concat [bks; bls; bms; [bsigma]; btaus; [btheta; beq; bx]]) innerType innerBody.

  Definition genUpSubstSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstSubst bs)) bss.

  Definition genCompSubstSubst (sort: tId) : t (def nterm) :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ks ls;;
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    '(thetas, bthetas) <- genSubst "theta" sort ks ms;;
    sigmatau <- comp_ren_or_subst sort taus sigmas;;
    '(eqs, beqs) <- genEq "Eq" sort sigmatau (sty_terms thetas)
                         (fun x y s =>
                            taus' <- castSubst sort x taus;;
                            pure (app_ref (upSubstSubstName x y)
                                          (List.concat [[nHole];
                                                       List.map (const nHole) (sty_terms taus');
                                                       [nHole; s]])));;
    (* type *)
    let ret s := eq_ (app_ref (substName sort) (List.app (sty_terms taus)
                                                         [app_ref (substName sort) (List.app (sty_terms sigmas)
                                                                                             [s])]))
                     (app_ref (substName sort) (List.app (sty_terms thetas) [s])) in
    traversal sort ks compSubstSubstName no_args_default ret (List.concat [bks; bls; bms; bsigmas; btaus; bthetas; beqs]) [sigmas; taus; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genCompSubstSubsts := genFixpoint genCompSubstSubst.
End substSubst.
Import substSubst.

MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_ty) default_flags Hsig_example.mySig env29
                           >>= composeGeneration "env30").

MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_tm) default_flags Hsig_example.mySig env30
                           >>= composeGeneration "env31").

MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("ty", [])) default_flags Hsig_example.mySig env31
                           >>= composeGeneration "env32").

MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("tm", ["vl"])) default_flags Hsig_example.mySig env32
                           >>= composeGeneration "env33").

Module rinstInst.
  Import GenM.Notations GenM.
  
  Definition genUpRinstInst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    '(m, bms) <- introScopeVarS "m";;
    '(ns, bns) <- introScopeVar "n" sort;;
    n_var <- toVarScope sort ns;;
    let '(xi, bxi) := genRenS "xi" scope_type m n_var in
    let '(sigma, bsigma) := genSubstS "sigma" scope_type m ns sort in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> app_constr (varConstrName sort) scope_type ns []) sigma in
    ns' <- upSubstScope sort [binder] ns;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) [xi])
                                 >>> (app_constr (varConstrName sort) scope_type ns' []))
                            (app_ref (upName sort binder) [sigma]) in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper n := ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder matchFin (innerBodyHelper x) in
    (* name *)
    let name := upRinstInstName sort binder in
    process_lemma name (List.concat [bms; bns; [bxi; bsigma; beq; bx]]) innerType innerBody.
    
  Definition genUpRinstInsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRinstInst bs)) bss.


  Definition genRinstInst (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ms ns;;
    xis' <- substify sort ns xis;;
    '(eqs, beqs) <- genEq "Eq" sort xis' (sty_terms sigmas)
                         (fun x y s => pure (app_ref (upRinstInstName x y) [nHole; nHole; s]));;
    let ret s := eq_ (app_ref (renName sort) (List.app (sty_terms xis) [s]))
                     (app_ref (substName sort) (List.app (sty_terms sigmas) [s])) in
    traversal sort ms rinstInstName no_args_default ret (List.concat [bms; bns; bxis; bsigmas; beqs]) [xis; sigmas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genRinstInsts := genFixpoint genRinstInst.


  Definition genLemmaRinstInst (sort: tId) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    xis_subst <- substify sort ns xis;;
    '(x, bx) <- introSortVar "x" ms sort;;
    (* type *)
    let innerType := eq_ (app_ref (renName sort) (List.app (sty_terms xis) [x]))
                         (app_ref (substName sort) (List.app xis_subst [x])) in
    (* body *)
    substSorts <- substOf sort;;
    let innerBody := app_ref (rinstInstName sort)
                             (List.concat [sty_terms xis;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [ x ]]) in
    (* name *)
    let name := rinstInstRewriteName sort in
    process_lemma name (List.concat [bms; bns; bxis; [bx]]) innerType innerBody.
                
  Definition genLemmaRinstInsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaRinstInst sort)) sorts.

End rinstInst.
Import rinstInst.

MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_ty) default_flags Hsig_example.mySig env33
                           >>= composeGeneration "env34").

MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_tm) default_flags Hsig_example.mySig env34
                           >>= composeGeneration "env35").

MetaCoq Run (mkLemmasTyped (genRinstInsts ("ty", [])) default_flags Hsig_example.mySig env35 >>= composeGeneration "env36").

MetaCoq Run (mkLemmasTyped (genRinstInsts ("tm", ["vl"])) default_flags Hsig_example.mySig env36 >>= composeGeneration "env37").

MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["ty"]) default_flags Hsig_example.mySig env37 >>= composeGeneration "env38").

MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["tm"; "vl"]) default_flags Hsig_example.mySig env38 >>= composeGeneration "env39").

Module instId.
  Import GenM.Notations GenM.
  
  Definition genLemmaInstId (sort: tId) : t nlemma :=
    substSorts <- substOf sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    vars <- mk_var_apps sort ms;;
    '(s, bs) <- introSortVar "s" ms sort;;
    (* type *)
    let innerType := eq_ (app_ref (substName sort) (List.app vars [s])) s in
    (* body *)
    let innerBody := app_ref (idSubstName sort)
                             (List.concat [vars;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [s]]) in
    (* name *)
    let name := instIdName sort in
    process_lemma name (List.concat [bms; [bs]]) innerType innerBody.

  Definition genLemmaInstIds (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaInstId sort)) sorts.

  
  Definition genLemmaRinstId (sort: tId) : t nlemma :=
    substSorts <- substOf sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    vars <- mk_var_apps sort ms;;
    let ids := List.map (const id_) substSorts in
    '(s, bs) <- introSortVar "s" ms sort;;
    (* type *)
    let innerType := eq_ (app_ref (renName sort) (List.app ids [s])) s in
    (* body *)
    let innerBody := eq_ind_r_ (abs_ref "t" (eq_ (nRef "t") s))
                               (app_ref (instIdName sort) [s])
                               (app_ref (rinstInstRewriteName sort) (List.app ids [s])) in
    (* name *)
    let name := rinstIdName sort in
    process_lemma name (List.concat [bms; [bs]]) innerType innerBody.
                         
  Definition genLemmaRinstIds (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaRinstId sort)) sorts.
  
End instId.
Import instId.

MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["ty"]) default_flags Hsig_example.mySig env39 >>= composeGeneration "env40").

MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["tm"; "vl"]) default_flags Hsig_example.mySig env40 >>= composeGeneration "env41").

MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["ty"]) default_flags Hsig_example.mySig env41 >>= composeGeneration "env42").

MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["tm"; "vl"]) default_flags Hsig_example.mySig env42 >>= composeGeneration "env43").


Module varL.
  Import GenM.Notations GenM.

  Definition genVar (name: string) (m: nterm) : t (nterm * gallinaArg) :=
    scope_type <- get_scope_type;;
    match scope_type with
    | Unscoped => pure (nRef name, explArg name nat_)
    | Wellscoped => pure (nRef name, explArg name (fin_ m))
    end.

  Definition genVarL (sort: tId) :=
    scope_type <- get_scope_type;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ms ns;;
    sigma_var <- toVar sort sigmas;;
    m_var <- toVarScope sort ms;;
    '(x, bx) <- genVar "x" m_var;;
    (* type *)
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms sigmas)
                                            [ app_constr (varConstrName sort) scope_type ms [x] ]))
                         (nApp sigma_var [x]) in
    (* body *)
    let innerBody := eq_refl_ in
    (* name *)
    let name := varLName sort in
    process_lemma name (List.concat [bms; bns; bsigmas; [bx]]) innerType innerBody.

  Definition genVarLs (sorts: list tId) : t (list lemma) :=
    varSorts <- a_filter isOpen sorts;;
    a_map (fun sort => translate_lemma (genVarL sort)) varSorts.
  

  Definition genVarLRen (sort: tId) :=
    scope_type <- get_scope_type;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    xi_var <- toVar sort xis;;
    m_var <- toVarScope sort ms;;
    '(x, bx) <- genVar "x" m_var;;
    (* type *)
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms xis)
                                            [ app_constr (varConstrName sort) scope_type ms [x] ]))
                         (app_constr (varConstrName sort) scope_type ns [nApp xi_var [x] ]) in
    (* body *)
    let innerBody := eq_refl_ in
    (* name *)
    let name := varLRenName sort in
    process_lemma name (List.concat [bms; bns; bxis; [bx]]) innerType innerBody.

  Definition genVarLRens (sorts: list tId) : t (list lemma) :=
    varSorts <- a_filter isOpen sorts;;
    a_map (fun sort => translate_lemma (genVarLRen sort)) varSorts.
  
End varL.
Import varL.

MetaCoq Run (mkLemmasTyped (genVarLs ["ty"]) default_flags Hsig_example.mySig env43 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env44").

MetaCoq Run (mkLemmasTyped (genVarLs ["tm"; "vl"]) default_flags Hsig_example.mySig env44 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env45").

MetaCoq Run (mkLemmasTyped (genVarLRens ["ty"]) default_flags Hsig_example.mySig env45 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env46").

MetaCoq Run (mkLemmasTyped (genVarLRens ["tm"; "vl"]) default_flags Hsig_example.mySig env46 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env47").


Module comps.
  Import GenM.Notations GenM.

  Definition genLemmaCompRenRen (sort: tId) : t nlemma :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(xis, bxis) <- genRen "xi" sort ks ls;;
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    let sigmazeta := xis <<>> zetas in
    substSorts <- substOf sort;;
    '(s, bs) <- introSortVar "s" ks sort;;
    (* type *)
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms zetas)
                                            [ app_ref (renName sort) (List.app (sty_terms xis) [s]) ]))
                         (app_ref (renName sort)
                                  (List.app sigmazeta [s])) in
    (* body *)
    let innerBody := app_ref (compRenRenName sort)
                             (List.concat [ sty_terms xis;
                                          sty_terms zetas;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [s]]) in
    (* name *)
    let name := renRenName sort in
    process_lemma name (List.concat [bks; bls; bms; bxis; bzetas; [bs]]) innerType innerBody.

  Definition genLemmaCompRenRens (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompRenRen sort)) sorts.
  

  Definition genLemmaCompRenSubst (sort: tId) : t nlemma :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(xis, bxis) <- genRen "xi" sort ks ls;;
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    substSorts <- substOf sort;;
    '(s, bs) <- introSortVar "s" ks sort;;
    (* type *)
    let xitaus := xis <<>> taus in
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms taus)
                                            [ app_ref (renName sort)
                                                      (List.app (sty_terms xis) [s]) ]))
                         (app_ref (substName sort)
                                  (List.app xitaus [s])) in
    (* body *)
    let innerBody := app_ref (compRenSubstName sort)
                             (List.concat [ sty_terms xis;
                                          sty_terms taus;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    (* name *)
    let name := renSubstName sort in
    process_lemma name (List.concat [bks; bls; bms; bxis; btaus; [bs]]) innerType innerBody.

  Definition genLemmaCompRenSubsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompRenSubst  sort)) sorts.


  Definition genLemmaCompSubstRen (sort: tId) : t nlemma :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ks ls;;
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    substSorts <- substOf sort;;
    '(s, bs) <- introSortVar "s" ks sort;;
    (* type *)
    sigmazetas <- comp_ren_or_subst sort zetas sigmas;;
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms zetas)
                                            [ app_ref (substName sort)
                                                      (List.app (sty_terms sigmas) [s]) ]))
                         (app_ref (substName sort) (List.app sigmazetas [s])) in
    (* body *)
    let innerBody := app_ref (compSubstRenName sort)
                             (List.concat [ sty_terms sigmas;
                                          sty_terms zetas;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    (* name *)
    let name := substRenName sort in
    process_lemma name (List.concat [bks; bls; bms; bsigmas; bzetas; [bs]]) innerType innerBody.

  Definition genLemmaCompSubstRens (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompSubstRen  sort)) sorts.


  Definition genLemmaCompSubstSubst (sort: tId) : t nlemma :=
    '(ks, bks) <- introScopeVar "k" sort;;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort ks ls;;
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    substSorts <- substOf sort;;
    '(s, bs) <- introSortVar "s" ks sort;;
    (* type *)
    sigmataus <- comp_ren_or_subst sort taus sigmas;;
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms taus)
                                            [ app_ref (substName sort)
                                                      (List.app (sty_terms sigmas) [s]) ]))
                         (app_ref (substName sort) (List.app sigmataus [s])) in
    (* body *)
    let innerBody := app_ref (compSubstSubstName sort)
                             (List.concat [sty_terms sigmas;
                                          sty_terms taus;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    (* name *)
    let name := substSubstName sort in
    process_lemma name (List.concat [bks; bls; bms; bsigmas; btaus; [bs]]) innerType innerBody.

  
  Definition genLemmaCompSubstSubsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompSubstSubst  sort)) sorts.

End comps.
Import comps.

MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["ty"]) default_flags Hsig_example.mySig env47 >>= composeGeneration "env48").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["tm"; "vl"]) default_flags Hsig_example.mySig env48 >>= composeGeneration "env49").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["ty"]) default_flags Hsig_example.mySig env49 >>= composeGeneration "env50").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["tm"; "vl"]) default_flags Hsig_example.mySig env50 >>= composeGeneration "env51").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["ty"]) default_flags Hsig_example.mySig env51 >>= composeGeneration "env52").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["tm"; "vl"]) default_flags Hsig_example.mySig env52 >>= composeGeneration "env53").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["ty"]) default_flags Hsig_example.mySig env53 >>= composeGeneration "env54").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["tm"; "vl"]) default_flags Hsig_example.mySig env54 >>= composeGeneration "env55").

(* MetaCoq Run (match GenM.run (genUpExts upList_ty) (Hsig_example.mySig, env13) empty_state with *)
(*              | inr (_, _, x) => *)
(*                tmEval TemplateMonad.Common.all x >>= tmPrint *)
(*              | _ => tmFail "fail" *)
(*              end). *)

(* TODO better document the way to debug this.
 * you can set everything opaque except the thing you want to see the AST of *)
(*
Module foo.
  From ASUB Require Import unscoped.
  Opaque ren_ty.
  Opaque ap.
  Opaque shift.
  Opaque up_ty_ty.
  
 Lemma upId_ty_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall n, up_ty_ty sigma n = var_ty n.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

MetaCoq Quote Definition foo_source := Eval compute in upId_ty_ty.
End foo.
 *)

Definition generate (component: NEList.t tId) (upList: list (Binder * tId)) (info: genInfo) : TemplateMonad genInfo :=
  let fl := default_flags in
  let s := Hsig_example.mySig in
  let componentL := NEList.to_list component in
  (** * Inductive Types *)
  (* generate the inductive types *)
  info <- mkInductive (genMutualInductive component) fl s info;;
  (** * Congruence Lemmas *)
  (* if we generate multiple lemmas we need to keep updating the infoironment in a fold *)
  info <- tm_foldM (fun info sort => mkLemmasTyped (genCongruences sort) fl s info) componentL info;;
  (* TODO check if component has binders
   * should probably use a nonempty list for the component then *)
  (** * Renamings *)
  info <- mkLemmasTyped (genUpRens upList) fl s info;;
  info <- mkLemmasTyped (genRenamings component) fl s info;;
  (** * Substitutions *)
  info <- mkLemmasTyped (genUpSubsts upList) fl s info;;
  info <- mkLemmasTyped (genSubstitutions component) fl s info;;
  (** * idSubst *)
  info <- mkLemmasTyped (genUpIds upList) fl s info;;
  info <- mkLemmasTyped (genIdLemmas component) fl s info;;
  (** * Extensionality *)
  info <- mkLemmasTyped (genUpExtRens upList) fl s info;;
  info <- mkLemmasTyped (genExtRens component) fl s info;;
  info <- mkLemmasTyped (genUpExts upList) fl s info;;
  info <- mkLemmasTyped (genExts component) fl s info;;
  (** * Combinations *)
  info <- mkLemmasTyped (genUpRenRens upList) fl s info;;
  info <- mkLemmasTyped (genCompRenRens component) fl s info;;
  info <- mkLemmasTyped (genUpRenSubsts upList) fl s info;;
  info <- mkLemmasTyped (genCompRenSubsts component) fl s info;;
  info <- mkLemmasTyped (genUpSubstRens upList) fl s info;;
  info <- mkLemmasTyped (genCompSubstRens component) fl s info;;
  info <- mkLemmasTyped (genUpSubstSubsts upList) fl s info;;
  info <- mkLemmasTyped (genCompSubstSubsts component) fl s info;;
  (** * rinstInst *)
  info <- mkLemmasTyped (genUpRinstInsts upList) fl s info;;
  info <- mkLemmasTyped (genRinstInsts component) fl s info;;
  info <- mkLemmasTyped (genLemmaRinstInsts componentL) fl s info;;
  (** * rinstId/instId *)
  info <- mkLemmasTyped (genLemmaInstIds componentL) fl s info;;
  info <- mkLemmasTyped (genLemmaRinstIds componentL) fl s info;;
  (** * varL *)
  info <- mkLemmasTyped (genVarLs componentL) fl s info;;
  info <- mkLemmasTyped (genVarLRens componentL) fl s info;;
  (** * Combinations *)
  info <- mkLemmasTyped (genLemmaCompRenRens componentL) fl s info;;
  info <- mkLemmasTyped (genLemmaCompRenSubsts componentL) fl s info;;
  info <- mkLemmasTyped (genLemmaCompSubstRens componentL) fl s info;;
  info <- mkLemmasTyped (genLemmaCompSubstSubsts componentL) fl s info;;
  tmReturn info.

From ASUB Require unscoped core.
Require Setoid Morphisms.

Module generation.
  Import Setoid Morphisms.
  (* Compute (GenM.run (genUpRens upList_ty) Hsig_example.mySig empty_state). *)
  Time MetaCoq Run (generate ("ty",[]) upList_ty {| in_env := initial_env; in_implicits := SFMap.empty |}
                             >>= tmEval TemplateMonad.Common.all
                             >>= generate ("tm", ["vl"]) upList_tm
                             >>= tmEval TemplateMonad.Common.all
                             >>= tmDefinition "env1").
  (* SFMap.t : 7 *)

  Import unscoped core UnscopedNotations.
  (* TODO the morphisms must still be generated *)
  Instance subst_ty_morphism :
    (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
            (@subst_ty)).
  Proof.
    exact (fun f_ty g_ty Eq_ty s t Eq_st =>
             eq_ind s (fun t' => subst_ty f_ty s = subst_ty g_ty t')
                    (ext_ty f_ty g_ty Eq_ty s) t Eq_st).
  Qed.

  Instance ren_ty_morphism :
    (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty)).
  Proof.
    exact (fun f_ty g_ty Eq_ty s t Eq_st =>
             eq_ind s (fun t' => ren_ty f_ty s = ren_ty g_ty t')
                    (extRen_ty f_ty g_ty Eq_ty s) t Eq_st).
  Qed.


  (* DONE prove the default lemma. If this works we're on the right track *)
  Goal forall (f: nat -> ty) (s t: ty),
      subst_ty f (subst_ty (scons t var_ty) s) = subst_ty (scons (subst_ty f t) var_ty) (subst_ty (up_ty_ty f) s).
  Proof.
    intros *.
    rewrite ?substSubst_ty.
    unfold up_ty_ty, funcomp.
    fsimpl.
    setoid_rewrite varL_ty.
    setoid_rewrite renSubst_ty.
    setoid_rewrite instId_ty.
    fsimpl. minimize.
    reflexivity.
  Qed.
End generation.


(* Module generation. *)
(*   Import Setoid Morphisms. *)
(*   (* Compute (GenM.run (genUpRens upList_ty) Hsig_example.mySig empty_state). *) *)
(*   Time MetaCoq Run (generate ("ty",[]) upList_ty {| in_env := initial_env; in_implicits := SFMap.empty |} *)
(*                              >>= tmEval TemplateMonad.Common.all *)
(*                              >>= generate ("tm", ["vl"]) upList_tm *)
(*                              >>= tmEval TemplateMonad.Common.all *)
(*                              >>= tmDefinition "env1"). *)
(*   (* implicit lookup in nRef translation: 18s *) *)
(*   (* implicit lookup in nApp translation: 15s *) *)

(*   Import fintype core ScopedNotations. *)
(*   (* TODO the morphisms must still be generated *) *)
(*   Instance subst_ty_morphism {m_ty n_ty : nat} : *)
(*     (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) *)
(*             (@subst_ty m_ty n_ty)). *)
(*   Proof. *)
(*     exact (fun f_ty g_ty Eq_ty s t Eq_st => *)
(*              eq_ind s (fun t' => subst_ty _ _ f_ty s = subst_ty _ _ g_ty t') *)
(*                     (ext_ty _ _ f_ty g_ty Eq_ty s) t Eq_st). *)
(*   Qed. *)

(*   Instance ren_ty_morphism {m_ty n_ty : nat} : *)
(*     (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty m_ty n_ty)). *)
(*   Proof. *)
(*     exact (fun f_ty g_ty Eq_ty s t Eq_st => *)
(*              eq_ind s (fun t' => ren_ty _ _ f_ty s = ren_ty _ _ g_ty t') *)
(*                     (extRen_ty _ _ f_ty g_ty Eq_ty s) t Eq_st). *)
(*   Qed. *)


(*   (* DONE prove the default lemma. If this works we're on the right track *) *)
(*   Goal forall {m n: nat} (f : fin m -> ty n) (s : ty (S m)) (t : ty m), *)
(*       subst_ty _ _ f (subst_ty _ _ (scons t (var_ty _)) s) = subst_ty _ _ (scons (subst_ty _ _ f t) (var_ty _)) (subst_ty _ _ (up_ty_ty _ _ f) s). *)
(*   Proof. *)
(*     intros *. *)
(*     rewrite ?substSubst_ty. *)
(*     unfold up_ty_ty, funcomp. *)
(*     fsimpl. *)
(*     setoid_rewrite varL_ty. *)
(*     setoid_rewrite renSubst_ty. *)
(*     setoid_rewrite instId_ty. *)
(*     fsimpl. minimize. *)
(*     reflexivity. *)
(*   Qed.  *)
(* End generation. *)
