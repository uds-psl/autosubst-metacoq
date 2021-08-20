Require Import List String.
Import ListNotations.
Open Scope string.

From MetaCoq.Template Require Import All.
Import MonadNotation.
From ASUB Require Import AssocList Language Quotes Utils DeBruijnMap Monad TemplateMonadUtils Names GallinaGen GenM VariableDSL Termutil SubstTy.

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
    match run m (Hsig_example.mySig, initial_env) empty_state with
    | inl _ => []
    | inr (_, _, x) => x
    end.

  Definition upList_tm :=
    let m := substSorts_ty <- substOf "ty";;
             substSorts <- substOf "tm";;
             let '(combinations, _) := getUps substSorts_ty [] in
             let '(_, upList) := getUps substSorts combinations in
             pure upList in
    match run m (Hsig_example.mySig, initial_env) empty_state with
    | inr (_, _, x) => x
    | _ => []
    end.

End genCode.
Import genCode.


Module helpers.
  (** * TemplateMonad function to generate and unquote inductive types.
   ** * It returns an updated environment that contains the new types and their constructors. *)
  Definition mkInductive (m: GenM.t mutual_inductive_entry) (s: Signature) (env: SFMap.t term) : TemplateMonad (SFMap.t term) :=
    match GenM.run m (s, env) empty_state with
    | inl e => tmFail e
    | inr (_, state, mind) =>
      tmMkInductive mind;;
      tm_update_env state env
    end.

  Definition mkLemmasTyped (m: GenM.t (list lemma)) (s: Signature) (env: SFMap.t term): TemplateMonad (SFMap.t term) :=
    match GenM.run m (s, env) empty_state with
    | inl e => tmFail e
    | inr (_, state, lemmas) =>
      tm_mapM tmTypedDefinition lemmas;; 
      tm_update_env state env
    end. 

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

  (* Generates the type of a variable constructor for a sort
 db : base deBruijn index, should move into a reader monad *)
  Definition genVarConstrType (sort: tId) : nterm :=
    let s := genVarArg sort in
    let typ := mknArr s [nRef sort] in
    typ.

  (* generates the type of a single argument of a constructor *)
  Definition genArg (sort: string) (pos : Position) : t nterm :=
    let '{| pos_binders := pos_binders; pos_head := pos_head |} := pos in
    match pos_head with
    | Atom argSort =>
      (* TODO lift scopes *)
      (* have to differentiate between sorts in the current component and sorts that are already in the environment *)
      pure (nRef argSort)
    (* TODO implement funapp case *)
    | FunApp _ _ _ => pure nat_
    end.

  (** * Generates the type of a given constructor for a sort *)
  Definition genConstructor (sort: tId) (c: Constructor) : t nterm :=
    let '{| con_parameters := con_parameters;
            con_name := _;
            con_positions := con_positions |} := c in
    (* need to fold over the positions to update the dbmap.
     * Also remember that arg needs to be appended to the list because it's a left fold *)
    up_n_x <- a_map (genArg sort) con_positions;;
    (* todo take care of parameters *)
    let targetType := nRef sort in
    pure (mknArrRev up_n_x targetType).

  (** * Generates a one_inductive_entry which holds the information for a single inductive type for a given sort based on the spec *)
  Definition genOneInductive (dbmap: DB.t) (sort: tId) : t one_inductive_entry :=
    ctors <- constructors sort;;
    sortIsOpen <- isOpen sort;;
    (* introScopeVar *)
    let ctor_names := map con_name ctors in
    ctor_ntypes <- a_map (genConstructor sort) ctors;;
    (* maybe we also add a variable constructor *)
    let '(ctor_names, ctor_ntypes) :=
        if sortIsOpen
        then (varConstrName sort :: ctor_names, genVarConstrType sort :: ctor_ntypes)
        else (ctor_names, ctor_ntypes) in
    (* register the type & ctor names to be put in the environment later *)
    register_names (sort :: ctor_names);;
    (* translate into TemplateCoq terms *)
    ctor_types <- a_map (translate dbmap) ctor_ntypes;;
    pure {|
        mind_entry_typename := sort;
        mind_entry_arity := tSort Universe.type0;
        mind_entry_consnames := ctor_names;
        mind_entry_lc := ctor_types 
      |}.

  (** * Generates a mutual_inductive_entry which combines multiple one_inductive_entry's into a mutual inductive type definition.
   ** * For each sort in the component, a one_inductive_entry is generated *)
  Definition genMutualInductive (component: list tId) : t mutual_inductive_entry :=
    (* the entries already use deBruin numbers as if they were sequentially bound.
     * i.e. the last entry has index 0. Therefore we can just add the component *)
    (* only generate the definable sorts *)
    def_sorts <- a_filter isDefinable component;;
    let dbmap := DB.adds def_sorts DB.empty in
    (* component also would contain predefined types like nat so we pass in def_sorts all the way down to genVarConstrType so that we also get nat out of the environment *)
    entries <- a_map (genOneInductive dbmap) def_sorts;;
    pure {|
        mind_entry_record := None;
        mind_entry_finite := Finite;
        mind_entry_params := [];
        mind_entry_inds := entries;
        mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
        mind_entry_template := false;
        mind_entry_variance := None;
        mind_entry_private := None;
      |}.

  (* Eval cbv in (run (genMutualInductive ["ty"]) Hsig_example.mySig empty_state). *)
End inductives.
Import inductives.

MetaCoq Run (mkInductive (genMutualInductive ["ty"%string]) Hsig_example.mySig GenM.initial_env >>= tmEval TemplateMonad.Common.all >>= mkInductive (genMutualInductive ["tm"; "vl"]) Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env0").


Module congruences.
  Import GenM GenM.Notations.

  (** * generates the terms for the congruence lemmas for a constructor of an inductive type *)
  Definition genCongruence (sort: tId) (ctor: Constructor) : t nlemma :=
    let '{| con_parameters := con_parameters;
            con_name := con_name;
            con_positions := con_positions |} := ctor in
    let ctor_tm := nRef con_name in
    (* arguments to the lemma *)
    let ss := getPattern "s" con_positions in
    let ts := getPattern "t" con_positions in
    arg_tys <- a_map getArgType con_positions;;
    let eqs := map2 (fun s t => eq_ (nRef s) (nRef t)) ss ts in
    let Hs := getPattern "H" con_positions in
    (* building the binders of the lemma *)
    let bss := combine ss arg_tys in
    let bts := combine ts arg_tys in
    let beqs := combine Hs eqs in
    let proof := add_binders (bss ++ bts ++ beqs) in
    (* body of the lemma *)
    let (_, proof') := fold_left
                         (fun '(i, tm) '(arg_typ, s, t, H) =>
                            let feq_args := map nRef (firstn i ts ++ ["x"] ++ skipn (S i) ss) in
                            let feq_lam := nLambda "x" nHole (nApp ctor_tm feq_args) in
                            let feq := f_equal_ feq_lam (nRef s) (nRef t) (nRef H) in
                            (S i, eq_trans_ tm feq))
                         (combine (combine (combine arg_tys ss) ts) Hs)
                         (0, eq_refl_) in
    (* generate and register lemma name *)
    let name := congrName con_name in
    register_name name;;
    (* generate the type of the lemma *)
    let type := add_tbinders (bss ++ bts ++ beqs) in
    let type' := eq_ (nApp ctor_tm (map nRef ss)) (nApp ctor_tm (map nRef ts)) in
    pure (name, type type', proof proof').


  (** * generates the terms for the congruence lemmas of the constructors of an inductive type *)
  Definition genCongruences (sort: tId) : t (list lemma) :=
    ctors <- constructors sort;;
    a_map (fun ctor => translate_lemma (genCongruence sort ctor)) ctors.
End congruences.
Import congruences.


(* Definition bind' := @bind TemplateMonad TemplateMonad_Monad. *)
(* Arguments bind' {t u}. *)

(* TODO seems like I still can't use implicit arguments.
 * The problem is now that to use tmUnquoteTyped I would need a Coq type (not in the MetaCoq AST) but when I unquote it, the typechecker does not know it's actually a type.
 * But in theory this should be possible to resolve by defining something like tmUnquoteType (no d) that gives me back a type (in this case the typed_term is not interesting because the first element will always be "Type") *)
(* Definition mkLemma '(lname, lbody, ltype) : TemplateMonad unit := *)
(*   bind' (tmUnquote ltype) *)
(*        (fun type : typed_term => *)
(*           bind' (tmEval lazy (my_projT2 type)) *)
(*                (fun type0 : _ => *)
(*                   bind' (tmUnquoteTyped type0 lbody) *)
(*                        (fun body : _ => *)
(*                           bind' (tmDefinitionRed lname (Some TemplateMonad.Common.all) body) *)
(*                                (fun _ => tmReturn tt)))). *)

(** * Helper function that does the actual unquoting to define alemma *)
(* Definition mkLemma' '(lname, lbody) : TemplateMonad unit := *)
(*   body <- tmUnquote lbody;; *)
(*   body <- tmEval lazy (my_projT2 body);; *)
(*   (* TODO In System F the all constructor shadowed the reductionStrategy. Is there a better way to avoid redefined names? I could put all unquoted definitions into their own module *) *)
(*   tmDefinitionRed lname (Some TemplateMonad.Common.all) body;; *)
(*   tmReturn tt. *)

(* (** * TemplateMonad function to generate and unquote lemmas. *) *)
(* Definition mkLemma (m: GenM.t (list (string * term))) (s: Signature) (env: SFMap.t term): TemplateMonad (SFMap.t term) := *)
(*   match GenM.run m s empty_state with *)
(*   | inl e => tmFail e *)
(*   | inr (_, state, lemmas) => *)
(*     tm_mapM mkLemma' lemmas;;  *)
(*     tm_update_env state *)
(*   end.  *)


MetaCoq Run (mkLemmasTyped (genCongruences "ty") Hsig_example.mySig env0 >>= tmEval TemplateMonad.Common.all >>=
                          mkLemmasTyped (genCongruences "tm") Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>= mkLemmasTyped (genCongruences "vl") Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>=
                          tmDefinition "env1").

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

  Definition branch_ (underscoreNum: nat) (binders: list string) (body: nterm) : (nat * nterm) :=
    let paramNum := underscoreNum + List.length binders in
    let binders := List.map (fun n => (n, nHole)) binders in
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

  Fixpoint arg_map (sort: tId) (args: list SubstTy) (name: string -> string) (no_args: nterm -> nterm) (funsem: string -> list nterm -> nterm) (bs: list Binder) (arg: ArgumentHead) :=
    match arg with
    | Atom y =>
      b <- hasArgs y;;
      args <- a_map (castUpSubst sort bs y) args;;
      pure (if b
            then nApp (nRef (name y)) (flat_map sty_terms args)
            else abs_ref "x" (no_args (nRef "x")))
    | FunApp f p xs =>
      res <- a_map (arg_map sort args name no_args funsem bs) xs;;
      pure (funsem f res)
    end.

  
  Definition mk_constr_pattern (s: string) (sort: tId) (args: list SubstTy) (name: string -> string) (no_args: nterm -> nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: string -> list nterm -> nterm) (ctor: Constructor) : t (nat * nterm) :=
    let '{| con_parameters := cparameters; con_name := cname; con_positions := cpositions |} := ctor in
    let ss := getPattern "s" cpositions in
    positions <- a_map (fun '(s, {| pos_binders := binders; pos_head := head |}) =>
                         fmap2 nApp (arg_map sort args name no_args funsem binders head) (pure [ nRef s ]))
                      (combine ss cpositions);;
    let paramNames := List.map fst cparameters in
    pure (branch_ 0 (List.app paramNames ss) (sem paramNames cname positions)).
  
  Definition traversal (sort: tId) (name: string -> string) (no_args: nterm -> nterm) (ret: nterm -> nterm) (bargs: list (string * nterm)) (args: list SubstTy) (var_case_body: nterm -> t nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: string -> list nterm -> nterm) : t (def nterm) :=
    ctors <- constructors sort;;
    let s := "s" in
    let lambdas := List.app bargs [(s, nRef sort)] in
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
    constr_patterns <- a_map (mk_constr_pattern s sort args name no_args sem funsem) ctors;;
    (* TODO calculate number of parameters *)
    (* DONE fix elemination predicate. I tried putting a hole as the return type but Coq is not smart enough to infer it. But we can use the return type function we already have available. *)
    let innerBody := nCase sort 0 (nLambda s (nRef sort) innerType) (nRef s) (List.app var_pattern constr_patterns) in
    let body := add_binders lambdas innerBody in
    pure {| dname := aname_ (name sort); dtype := type; dbody := body; rarg := argNum |}.

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
    let '(xi, bxi) := genRenS "xi" in
    (* let '(_, bpms) := bparameters binder in *)
    let preProof := definitionBody sort binder (up_ren_ xi) xi in
    let proof := add_binders [ bxi ] preProof in
    let preType := nArr nat_ nat_ in
    let type := add_tbinders [bxi] preType in
    let name := upRenName sort binder in
    register_name name;;
    pure (name, type, proof).

  Definition genUpRens (bss: list (Binder * tId)) : t (list (string * term * term)) :=
    a_map (fun bs => translate_lemma (genUpRen bs)) bss.


  Definition genRenaming (sort: tId) : t (def nterm) :=
    '(xis, bxis) <- genRen "xi" sort;;
    substSorts <- substOf sort;;
    let ret := fun _ => nRef sort in
    traversal sort renName Datatypes.id ret bxis [ xis ]
              (fun s => toVarT <- toVar sort xis;;
                     pure (nApp (nRef (varConstrName sort)) [ nApp toVarT [ s ] ]))
              (fun paramNames cname positions => app_constr cname (List.app (List.map nRef paramNames) positions))
              map_.

  Definition genRenamings := genFixpoint genRenaming.
End renamings.
Import renamings.

MetaCoq Run (mkLemmasTyped (genUpRens upList_ty) Hsig_example.mySig env1 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env2").

MetaCoq Run (mkLemmasTyped (genRenamings ("ty", [])) Hsig_example.mySig env2 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env3").

MetaCoq Run (mkLemmasTyped (genUpRens upList_tm) Hsig_example.mySig env3 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env4").

MetaCoq Run (mkLemmasTyped (genRenamings ("tm", ["vl"])) Hsig_example.mySig env4 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env5").


Module substitutions.
  Import GenM.Notations GenM.

  Definition genUpSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    (* let '(_, bpms) := bparameters binder in *)
    innerBody <- upSubstT binder sort sigma;;
    let body := add_binders [ bsigma ] innerBody in
    let innerType := nArr nat_ (nRef sort) in
    let type := add_tbinders [ bsigma ] innerType in
    let name := upName sort binder in
    register_name name;;
    pure (name, type, body).

  Definition genUpSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubst bs)) bss.

  (** Generate the substitution function
   ** e.g. subst_ty *)
  Definition genSubstitution (sort: tId) : t (def nterm) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    traversal sort substName Datatypes.id (fun _ => nRef sort) bsigmas [ sigmas ]
              (fun s =>
                 toVarT <- toVar sort sigmas;;
                 pure (nApp toVarT [ s ]))
              (fun paramNames cname positions => app_constr cname (List.app (List.map nRef paramNames) positions))
              map_.

  Definition genSubstitutions := genFixpoint genSubstitution.
    
End substitutions.
Import substitutions.

MetaCoq Run (mkLemmasTyped (genUpSubsts upList_ty) Hsig_example.mySig env5 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env6").

MetaCoq Run (mkLemmasTyped (genSubstitutions ("ty", [])) Hsig_example.mySig env6 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env7").

MetaCoq Run (mkLemmasTyped (genUpSubsts upList_tm) Hsig_example.mySig env7 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env8").

MetaCoq Run (mkLemmasTyped (genSubstitutions ("tm", ["vl"])) Hsig_example.mySig env8 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env9").

Module idsubsts.
  Import GenM.Notations GenM.

  Definition genUpId (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    let '(n, bn) := introDBVar "n" in
    let '(eq, beq) := genEqS "Eq" bn sigma (nRef (varConstrName sort)) in
    (** * type *)
    let innerType := equiv_ n
                       (nApp (nRef (upName sort binder)) [ sigma ])
                       (nRef (varConstrName sort)) in
    let type := add_tbinders [ bsigma; beq; bn ] innerType in
    (** * body *)
    shift <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let t := fun (n: nterm) =>
               ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) shift)
                   (nApp eq [ n ]) in
    let innerBody := definitionBody sort binder
                                    (matchFin_ bn innerType n t eq_refl_) (t n) in
    let body := add_binders [ bsigma; beq; bn ] innerBody in
    (** * name *)
    let name := upIdName sort binder in
    register_name name;;
    pure (name, type, body).
  
  Definition genUpIds (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpId bs)) bss.

  Definition genIdLemma (sort: tId) : t (def nterm) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    substSorts <- substOf sort;;
    eqs' <- mk_var_apps sort;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms sigmas) eqs'
                         (fun x y s => pure (nApp (nRef (upIdName x y)) [nHole; s]));;
    let ret := fun s =>
                 eq_ (nApp (nRef (substName sort)) (List.app (sty_terms sigmas) [ s ])) s in
    traversal sort idSubstName no_args_default ret (List.app bsigmas beqs) [ sigmas; eqs ]
              (fun s =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [ s ]))
              sem_default
              mapId_.

  Definition genIdLemmas := genFixpoint genIdLemma.

End idsubsts.
Import idsubsts.

MetaCoq Run (mkLemmasTyped (genUpIds upList_ty) Hsig_example.mySig env9 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env10").

MetaCoq Run (mkLemmasTyped (genIdLemmas ("ty", [])) Hsig_example.mySig env10 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env11").

MetaCoq Run (mkLemmasTyped (genUpIds upList_tm) Hsig_example.mySig env11 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env12").

MetaCoq Run (mkLemmasTyped (genIdLemmas ("tm", ["vl"])) Hsig_example.mySig env12 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env13").

Module extensionality.
  Import GenM.Notations GenM.

  Definition genUpExtRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(xi, bxi) := genRenS "xi" in
    let '(zeta, bzeta) := genRenS "zeta" in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx xi zeta in
    (* type *)
    let innerType := equiv_ x (nApp (nRef (upRenName sort binder)) [ xi ]) (nApp (nRef (upRenName sort binder)) [ zeta ]) in
    let type := add_tbinders [ bxi; bzeta; beq; bx ] innerType in
    (* body *)
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x (fun n => ap_ shift_ (nApp eq [n])) eq_refl_)
                                    (nApp eq [x]) in
    let body := add_binders [ bxi; bzeta; beq; bx ] innerBody in
    (* name *)
    let name := upExtRenName sort binder in
    register_name name;;
    pure (name, type, body).
  
  Definition genUpExtRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpExtRen bs)) bss.

  
  Definition genExtRen (sort: tId) : t (def nterm) :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(zetas, bzetas) <- genRen "zeta" sort;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms xis) (sty_terms zetas)
                         (fun x y s => pure (nApp (nRef (upExtRenName x y)) [nHole; nHole; s]));;
    (* type *)
    let ret := fun s => eq_ (nApp (nRef (renName sort)) (List.app (sty_terms xis) [s]))
                         (nApp (nRef (renName sort)) (List.app (sty_terms zetas) [s])) in
    traversal sort extRenName no_args_default ret (List.concat [bxis; bzetas; beqs]) [xis; zetas; eqs]
              (fun z =>
                 toVarT <- toVar sort eqs;;
                 pure (ap_ (nRef (varConstrName sort)) (nApp toVarT [z])))
              sem_default
              mapExt_.

  Definition genExtRens (component: NEList.t tId) : t (list lemma) :=
    let componentL := NEList.to_list component in
    isRec <- isRecursive component;;
    fexprs <- a_map genExtRen componentL;;
    buildFixpoint fexprs isRec.

  
  Definition genUpExt (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    let '(tau, btau) := genSubstS "tau" sort in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx sigma tau in
    (* type *)
    let innerType := equiv_ x (nApp (nRef (upName sort binder)) [ sigma ]) (nApp (nRef (upName sort binder)) [ tau ]) in
    let type := add_tbinders [ bsigma; btau; beq; bx ] innerType in
    (* body *)
    shift <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let innerBodyHelper := fun n => ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) shift)
                                     (nApp eq [n]) in
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x innerBodyHelper eq_refl_)
                                    (innerBodyHelper x) in
    let body := add_binders [ bsigma; btau; beq; bx ] innerBody in
    (* name *)
    let name := upExtName sort binder in
    register_name name;;
    pure (name, type, body).
    
  Definition genUpExts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpExt bs)) bss.

  Definition genExt (sort: tId) : t (def nterm) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    '(taus, btaus) <- genSubst "tau" sort;;
    '(eqs, beqs) <- genEq "Eq" sort (sty_terms sigmas) (sty_terms taus)
                         (fun x y s => pure (nApp (nRef (upExtName x y)) [nHole; nHole; s]));;
    let ret := fun s => eq_ (nApp (nRef (substName sort)) (List.app (sty_terms sigmas) [s]))
                         (nApp (nRef (substName sort)) (List.app (sty_terms taus) [s])) in
    traversal sort extName no_args_default ret (List.concat [bsigmas; btaus; beqs]) [sigmas; taus; eqs]
              (fun z =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [z]))
              sem_default
              mapExt_.

  Definition genExts := genFixpoint genExt.

End extensionality.
Import extensionality.

MetaCoq Run (mkLemmasTyped (genUpExtRens upList_ty) Hsig_example.mySig env13 >>= tmEval TemplateMonad.Common.all >>=
             mkLemmasTyped (genUpExts upList_ty) Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>=
             tmDefinition "env14").

MetaCoq Run (mkLemmasTyped (genUpExtRens upList_tm) Hsig_example.mySig env14 >>= tmEval TemplateMonad.Common.all >>=
             mkLemmasTyped (genUpExts upList_tm) Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>=
             tmDefinition "env15").

MetaCoq Run (mkLemmasTyped (genExtRens ("ty", [])) Hsig_example.mySig env15 >>= tmEval TemplateMonad.Common.all >>=
             mkLemmasTyped (genExts ("ty", [])) Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>=
                           tmDefinition "env16").

MetaCoq Run (mkLemmasTyped (genExtRens ("tm", ["vl"])) Hsig_example.mySig env16 >>= tmEval TemplateMonad.Common.all >>=
             mkLemmasTyped (genExts ("tm", ["vl"])) Hsig_example.mySig >>= tmEval TemplateMonad.Common.all >>=
                           tmDefinition "env17").

Module renRen.
  Import GenM.Notations GenM.
  
  Definition genUpRenRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(xi, bxi) := genRenS "xi" in
    let '(zeta, bzeta) := genRenS "zeta" in
    let '(rho, brho) := genRenS "rho" in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx (xi >>> zeta) rho in
    (* type *)
    let innerType := equiv_ x ((nApp (nRef (upRenName sort binder)) [xi])
                                 >>> (nApp (nRef (upRenName sort binder)) [zeta]))
                            (nApp (nRef (upRenName sort binder)) [rho]) in
    let type := add_tbinders [bxi; bzeta; brho; beq; bx] innerType in
    (* body *)
    (* a.d. here I have to take care to also pass x to up_ren_ren and to eq in the second case of definitionBody *)
    let innerBody := definitionBody sort binder (nApp up_ren_ren_ [xi; zeta; rho; eq; x]) (nApp eq [x]) in
    let body := add_binders [bxi; bzeta; brho; beq; bx] innerBody in 
    (* name *)
    let name := upRenRenName sort binder in
    register_name name;;
    pure (name, type, body).

  Definition genUpRenRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRenRen bs)) bss.


  Definition genCompRenRen (sort: tId) : t (def nterm) :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(zetas, bzetas) <- genRen "zeta" sort;;
    '(rhos, brhos) <- genRen "rho" sort;;
    '(eqs, beqs) <- genEq "Eq" sort
                         (map2 funcomp_ (sty_terms zetas) (sty_terms xis))
                         (sty_terms rhos)
                         (fun x y s => match y with
                                    | Single z => if eqb z x
                                                        (* TODO do I need an x to pass to up_ren_ren here *)
                                                 then pure (nApp up_ren_ren_ [nHole; nHole; nHole; s])
                                                 else pure s
                                    end);;
    let ret := fun s => eq_ (nApp (nRef (renName sort)) (List.app (sty_terms zetas)
                                                        [ nApp (nRef (renName sort)) (List.app (sty_terms xis) [s]) ]))
                         (nApp (nRef (renName sort)) (List.app (sty_terms rhos) [s])) in
    traversal sort compRenRenName no_args_default ret (List.concat [bxis; bzetas; brhos; beqs]) [xis; zetas; rhos; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (ap_ (nRef (varConstrName sort)) (nApp toVarT [n])))
              sem_default
              mapComp_.
              
  Definition genCompRenRens := genFixpoint genCompRenRen.
End renRen.
Import renRen.

MetaCoq Run (mkLemmasTyped (genUpRenRens upList_ty) Hsig_example.mySig env17 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env18").

MetaCoq Run (mkLemmasTyped (genUpRenRens upList_tm) Hsig_example.mySig env18 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env19").

MetaCoq Run (mkLemmasTyped (genCompRenRens ("ty", [])) Hsig_example.mySig env19 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env20").

MetaCoq Run (mkLemmasTyped (genCompRenRens ("tm", ["vl"])) Hsig_example.mySig env20 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env21").

Module renSubst.
  Import GenM.Notations GenM.
  

  Definition genUpRenSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(xi, bxi) := genRenS "xi" in
    let '(tau, btau) := genSubstS "tau" sort in
    let '(theta, btheta) := genSubstS "theta" sort in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx (xi >>> tau) theta in
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) [xi])
                                 >>> (app_ref (upName sort binder) [tau]))
                            (app_ref (upName sort binder) [theta]) in
    let type := add_tbinders [bxi; btau; btheta; beq; bx] innerType in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper := fun n => ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x innerBodyHelper eq_refl_)
                                    (innerBodyHelper x) in
    let body := add_binders [bxi; btau; btheta; beq; bx] innerBody in
    (* name *)
    let name := upRenSubstName sort binder in
    register_name name;;
    pure (name, type, body).

  Definition genUpRenSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRenSubst bs)) bss.
  
  Definition genCompRenSubst (sort: tId) : t (def nterm) :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(taus, btaus) <- genSubst "tau" sort;;
    '(thetas, bthetas) <- genSubst "theta" sort;;
    '(eqs, beqs) <- genEq "Eq" sort
                         (map2 funcomp_ (sty_terms taus) (sty_terms xis))
                         (sty_terms thetas)
                         (fun x y s => pure (app_ref (upRenSubstName x y) [nHole; nHole; nHole; s]));;
    (* type *)
    let ret := fun s => eq_ (app_ref (substName sort) (List.app (sty_terms taus)
                                                             [app_ref (renName sort) (List.app (sty_terms xis) [s])]))
                         (app_ref (substName sort) (List.app (sty_terms thetas) [s])) in
    traversal sort compRenSubstName no_args_default ret (List.concat [bxis; btaus; bthetas; beqs]) [xis; taus; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genCompRenSubsts := genFixpoint genCompRenSubst.
End renSubst.
Import renSubst.

MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_ty) Hsig_example.mySig env21 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env22").

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
MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_tm) Hsig_example.mySig env22 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env23").

MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("ty", [])) Hsig_example.mySig env23 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env24").

MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("tm", ["vl"])) Hsig_example.mySig env24 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env25").

Module substRen.
  Import GenM.Notations GenM.
  

  Definition genUpSubstRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    '(zetas, bzetas) <- genRen "zeta" sort;;
    let '(theta, btheta) := genSubstS "theta" sort in
    let '(x, bx) := introDBVar "x" in
    (* sigma >> <zeta> =1 theta *)
    let '(eq, beq) := genEqS "Eq" bx (sigma >>> (app_ref (renName sort) (sty_terms zetas))) theta in
    zetas' <- upSubst sort [binder] zetas;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) [sigma])
                                 >>> (app_ref (renName sort) (sty_terms zetas')))
                            (app_ref (upName sort binder) [theta]) in
    let type := add_tbinders (List.concat [[bsigma]; bzetas; [btheta]; [beq]; [bx]]) innerType in
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
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x innerBodyHelper eq_refl_)
                                    (innerBodyHelper x) in
    let body := add_binders (List.concat [[bsigma]; bzetas; [btheta]; [beq]; [bx]]) innerBody in
    (* name *)
    let name := upSubstRenName sort binder in
    register_name name;;
    pure (name, type, body).

  Definition genUpSubstRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstRen bs)) bss.

  
  Definition genCompSubstRen (sort: tId) : t (def nterm) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    '(zetas, bzetas) <- genRen "zeta" sort;;
    '(thetas, bthetas) <- genSubst "theta" sort;;
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
    traversal sort compSubstRenName no_args_default ret (List.concat [bsigmas; bzetas; bthetas; beqs]) [sigmas; zetas; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.

  Definition genCompSubstRens := genFixpoint genCompSubstRen.
End substRen.
Import substRen.

MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_ty) Hsig_example.mySig env25 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env26").

MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_tm) Hsig_example.mySig env26 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env27").

MetaCoq Run (mkLemmasTyped (genCompSubstRens ("ty", [])) Hsig_example.mySig env27 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env28").

MetaCoq Run (mkLemmasTyped (genCompSubstRens ("tm", ["vl"])) Hsig_example.mySig env28 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env29").

Module substSubst.
  Import GenM.Notations GenM.
  
  Definition genUpSubstSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    '(taus, btaus) <- genSubst "tau" sort;;
    let '(theta, btheta) := genSubstS "theta" sort in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx
                             (sigma >>> app_ref (substName sort) (sty_terms taus))
                             theta in
    taus' <- upSubst sort [binder] taus;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) [sigma])
                                 >>> (app_ref (substName sort) (sty_terms taus')))
                            (app_ref (upName sort binder) [theta]) in
    let type := add_tbinders (List.concat [[bsigma]; btaus; [btheta; beq; bx]]) innerType in
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
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x innerBodyHelper eq_refl_)
                                    (innerBodyHelper x) in
    let body := add_binders (List.concat [[bsigma]; btaus; [btheta; beq; bx]]) innerBody in
    (* name *)
    let name := upSubstSubstName sort binder in
    register_name name;;
    pure (name, type, body).

  Definition genUpSubstSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstSubst bs)) bss.

  Definition genCompSubstSubst (sort: tId) : t (def nterm) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    '(taus, btaus) <- genSubst "tau" sort;;
    '(thetas, bthetas) <- genSubst "theta" sort;;
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
    traversal sort compSubstSubstName no_args_default ret (List.concat [bsigmas; btaus; bthetas; beqs]) [sigmas; taus; thetas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genCompSubstSubsts := genFixpoint genCompSubstSubst.
End substSubst.
Import substSubst.

MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_ty) Hsig_example.mySig env29 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env30").

MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_tm) Hsig_example.mySig env30 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env31").

MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("ty", [])) Hsig_example.mySig env31 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env32").

MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("tm", ["vl"])) Hsig_example.mySig env32 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env33").

Module rinstInst.
  Import GenM.Notations GenM.
  
  Definition genUpRinstInst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(xi, bxi) := genRenS "xi" in
    let '(sigma, bsigma) := genSubstS "sigma" sort in
    let '(x, bx) := introDBVar "x" in
    let '(eq, beq) := genEqS "Eq" bx (xi >>> app_ref (varConstrName sort) []) sigma in
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) [xi])
                                 >>> (app_ref (varConstrName sort) []))
                            (app_ref (upName sort binder) [sigma]) in
    let type := add_tbinders [bxi; bsigma; beq; bx] innerType in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper n := ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    let innerBody := definitionBody sort binder
                                    (matchFin_ bx innerType x innerBodyHelper eq_refl_)
                                    (innerBodyHelper x) in
    let body := add_binders [bxi; bsigma; beq; bx] innerBody in
    (* name *)
    let name := upRinstInstName sort binder in
    register_name name;;
    pure (name, type, body).
    
  Definition genUpRinstInsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRinstInst bs)) bss.


  Definition genRinstInst (sort: tId) : t (def nterm) :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    xis' <- substify sort xis;;
    '(eqs, beqs) <- genEq "Eq" sort xis' (sty_terms sigmas)
                         (fun x y s => pure (app_ref (upRinstInstName x y) [nHole; nHole; s]));;
    let ret s := eq_ (app_ref (renName sort) (List.app (sty_terms xis) [s]))
                     (app_ref (substName sort) (List.app (sty_terms sigmas) [s])) in
    traversal sort rinstInstName no_args_default ret (List.concat [bxis; bsigmas; beqs]) [xis; sigmas; eqs]
              (fun n =>
                 toVarT <- toVar sort eqs;;
                 pure (nApp toVarT [n]))
              sem_default
              mapComp_.
    
  Definition genRinstInsts := genFixpoint genRinstInst.


  Definition genLemmaRinstInst (sort: tId) :=
    '(xis, bxis) <- genRen "xi" sort;;
    xis_subst <- substify sort xis;;
    let '(x, bx) := introSortVar "x" sort in
    (* type *)
    let innerType := eq_ (app_ref (renName sort) (List.app (sty_terms xis) [x]))
                         (app_ref (substName sort) (List.app xis_subst [x])) in
    let type := add_tbinders (List.app bxis [bx]) innerType in
    (* body *)
    substSorts <- substOf sort;;
    let innerBody := app_ref (rinstInstName sort)
                             (List.concat [sty_terms xis;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [ x ]]) in
    let body := add_binders (List.app bxis [bx]) innerBody in
    (* name *)
    let name := rinstInstRewriteName sort in
    register_name name;;
    pure (name, type, body).
                
  Definition genLemmaRinstInsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaRinstInst sort)) sorts.

End rinstInst.
Import rinstInst.

MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_ty) Hsig_example.mySig env33 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env34").

MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_tm) Hsig_example.mySig env34 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env35").

MetaCoq Run (mkLemmasTyped (genRinstInsts ("ty", [])) Hsig_example.mySig env35 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env36").

MetaCoq Run (mkLemmasTyped (genRinstInsts ("tm", ["vl"])) Hsig_example.mySig env36 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env37").

MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["ty"]) Hsig_example.mySig env37 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env38").

MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["tm"; "vl"]) Hsig_example.mySig env38 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env39").

Module instId.
  Import GenM.Notations GenM.
  
  Definition genLemmaInstId (sort: tId) : t nlemma :=
    substSorts <- substOf sort;;
    vars <- mk_var_apps sort;;
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    let innerType := eq_ (app_ref (substName sort) (List.app vars [s])) s in
    let type := add_tbinders [bs] innerType in
    (* body *)
    let innerBody := app_ref (idSubstName sort)
                             (List.concat [vars;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [s]]) in
    let body := add_binders [bs] innerBody in
    (* name *)
    let name := instIdName sort in
    register_name name;;
    pure (name, type, body).

  Definition genLemmaInstIds (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaInstId sort)) sorts.

  
  Definition genLemmaRinstId (sort: tId) : t nlemma :=
    substSorts <- substOf sort;;
    vars <- mk_var_apps sort;;
    let ids := List.map (const id_) substSorts in
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    let innerType := eq_ (app_ref (renName sort) (List.app ids [s])) s in
    let type := add_tbinders [bs] innerType in
    (* body *)
    let innerBody := eq_ind_r_ (abs_ref "t" (eq_ (nRef "t") s))
                               (app_ref (instIdName sort) [s])
                               (app_ref (rinstInstRewriteName sort) (List.app ids [s])) in
    let body := add_binders [bs] innerBody in
    (* name *)
    let name := rinstIdName sort in
    register_name name;;
    pure (name, type, body).
                         
  Definition genLemmaRinstIds (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaRinstId sort)) sorts.
  
End instId.
Import instId.

MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["ty"]) Hsig_example.mySig env39 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env40").

MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["tm"; "vl"]) Hsig_example.mySig env40 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env41").

MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["ty"]) Hsig_example.mySig env41 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env42").

MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["tm"; "vl"]) Hsig_example.mySig env42 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env43").


Module varL.
  Import GenM.Notations GenM.

  Definition genVarL (sort: tId) :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    sigma <- toVar sort sigmas;;
    let '(x, bx) := introDBVar "x" in
    (* type *)
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms sigmas)
                                            [ app_constr (varConstrName sort) [x] ]))
                         (nApp sigma [x]) in
    let type := add_tbinders (List.app bsigmas [bx]) innerType in
    (* body *)
    let innerBody := eq_refl_ in
    let body := add_binders (List.app bsigmas [bx]) innerBody in
    (* name *)
    let name := varLName sort in
    pure (name, type, body).

  Definition genVarLs (sorts: list tId) : t (list lemma) :=
    varSorts <- a_filter isOpen sorts;;
    a_map (fun sort => translate_lemma (genVarL sort)) varSorts.
  

  Definition genVarLRen (sort: tId) :=
    '(xis, bxis) <- genRen "subst" sort;;
    xi <- toVar sort xis;;
    let '(x, bx) := introDBVar "x" in
    (* type *)
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms xis)
                                            [ app_constr (varConstrName sort) [x] ]))
                         (app_constr (varConstrName sort) [nApp xi [x] ]) in
    let type := add_tbinders (List.app bxis [bx]) innerType in
    (* body *)
    let innerBody := eq_refl_ in
    let body := add_binders (List.app bxis [bx]) innerBody in
    (* name *)
    let name := varLRenName sort in
    pure (name, type, body).

  Definition genVarLRens (sorts: list tId) : t (list lemma) :=
    varSorts <- a_filter isOpen sorts;;
    a_map (fun sort => translate_lemma (genVarLRen sort)) varSorts.
  
End varL.
Import varL.

MetaCoq Run (mkLemmasTyped (genVarLs ["ty"]) Hsig_example.mySig env43 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env44").

MetaCoq Run (mkLemmasTyped (genVarLs ["tm"; "vl"]) Hsig_example.mySig env44 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env45").

MetaCoq Run (mkLemmasTyped (genVarLRens ["ty"]) Hsig_example.mySig env45 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env46").

MetaCoq Run (mkLemmasTyped (genVarLRens ["tm"; "vl"]) Hsig_example.mySig env46 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env47").


Module comps.
  Import GenM.Notations GenM.

  Definition genLemmaCompRenRen (sort: tId) : t nlemma :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(zetas, bzetas) <- genRen "zeta" sort;;
    let sigmazeta := xis <<>> zetas in
    substSorts <- substOf sort;;
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms zetas)
                                            [ app_ref (renName sort) (List.app (sty_terms xis) [s]) ]))
                         (app_ref (renName sort)
                                  (List.app sigmazeta [s])) in
    let type := add_tbinders (List.concat [bxis; bzetas; [bs]]) innerType in
    (* body *)
    let innerBody := app_ref (compRenRenName sort)
                             (List.concat [ sty_terms xis;
                                          sty_terms zetas;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "x" eq_refl_)) substSorts;
                                          [s]]) in
    let body := add_binders (List.concat [bxis; bzetas; [bs]]) innerBody in
    (* name *)
    let name := renRenName sort in
    pure (name, type, body).

  Definition genLemmaCompRenRens (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompRenRen sort)) sorts.
  

  Definition genLemmaCompRenSubst (sort: tId) : t nlemma :=
    '(xis, bxis) <- genRen "xi" sort;;
    '(taus, btaus) <- genSubst "tau" sort;;
    substSorts <- substOf sort;;
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    let xitaus := xis <<>> taus in
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms taus)
                                            [ app_ref (renName sort)
                                                      (List.app (sty_terms xis) [s]) ]))
                         (app_ref (substName sort)
                                  (List.app xitaus [s])) in
    let type := add_tbinders (List.concat [bxis; btaus; [bs]]) innerType in
    (* body *)
    let innerBody := app_ref (compRenSubstName sort)
                             (List.concat [ sty_terms xis;
                                          sty_terms taus;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    let body := add_binders (List.concat [bxis; btaus; [bs]]) innerBody in
    (* name *)
    let name := renSubstName sort in
    pure (name, type, body).

  Definition genLemmaCompRenSubsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompRenSubst  sort)) sorts.


  Definition genLemmaCompSubstRen (sort: tId) : t nlemma :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    '(zetas, bzetas) <- genRen "zeta" sort;;
    substSorts <- substOf sort;;
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    sigmazetas <- comp_ren_or_subst sort zetas sigmas;;
    let innerType := eq_ (app_ref (renName sort)
                                  (List.app (sty_terms zetas)
                                            [ app_ref (substName sort)
                                                      (List.app (sty_terms sigmas) [s]) ]))
                         (app_ref (substName sort) (List.app sigmazetas [s])) in
    let type := add_tbinders (List.concat [bsigmas; bzetas; [bs]]) innerType in
    (* body *)
    let innerBody := app_ref (compSubstRenName sort)
                             (List.concat [ sty_terms sigmas;
                                          sty_terms zetas;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    let body := add_binders (List.concat [bsigmas; bzetas; [bs]]) innerBody in
    (* name *)
    let name := substRenName sort in
    pure (name, type, body).

  Definition genLemmaCompSubstRens (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompSubstRen  sort)) sorts.


  Definition genLemmaCompSubstSubst (sort: tId) : t nlemma :=
    '(sigmas, bsigmas) <- genSubst "sigma" sort;;
    '(taus, btaus) <- genSubst "tau" sort;;
    substSorts <- substOf sort;;
    let '(s, bs) := introSortVar "s" sort in
    (* type *)
    sigmataus <- comp_ren_or_subst sort taus sigmas;;
    let innerType := eq_ (app_ref (substName sort)
                                  (List.app (sty_terms taus)
                                            [ app_ref (substName sort)
                                                      (List.app (sty_terms sigmas) [s]) ]))
                         (app_ref (substName sort) (List.app sigmataus [s])) in
    let type := add_tbinders (List.concat [bsigmas; btaus; [bs]]) innerType in
    (* body *)
    let innerBody := app_ref (compSubstSubstName sort)
                             (List.concat [sty_terms sigmas;
                                          sty_terms taus;
                                          List.map (const nHole) substSorts;
                                          List.map (const (abs_ref "n" eq_refl_)) substSorts;
                                          [s] ]) in
    let body := add_binders (List.concat [bsigmas; btaus; [bs]]) innerBody in
    (* name *)
    let name := substSubstName sort in
    pure (name, type, body).

  
  Definition genLemmaCompSubstSubsts (sorts: list tId) : t (list lemma) :=
    a_map (fun sort => translate_lemma (genLemmaCompSubstSubst  sort)) sorts.

End comps.
Import comps.

MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["ty"]) Hsig_example.mySig env47 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env48").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["tm"; "vl"]) Hsig_example.mySig env48 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env49").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["ty"]) Hsig_example.mySig env49 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env50").

MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["tm"; "vl"]) Hsig_example.mySig env50 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env51").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["ty"]) Hsig_example.mySig env51 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env52").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["tm"; "vl"]) Hsig_example.mySig env52 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env53").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["ty"]) Hsig_example.mySig env53 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env54").

MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["tm"; "vl"]) Hsig_example.mySig env54 >>= tmEval TemplateMonad.Common.all >>= tmDefinition "env55").

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

Definition generate (env: SFMap.t term) (component: NEList.t tId) (upList: list (Binder * tId)) : TemplateMonad (SFMap.t term) :=
  let s := Hsig_example.mySig in
  let componentL := NEList.to_list component in
  (** * Inductive Types *)
  (* generate the inductive types *)
  env <- mkInductive (genMutualInductive componentL) s env;;
  (** * Congruence Lemmas *)
  (* if we generate multiple lemmas we need to keep updating the environment in a fold *)
  env <- tm_foldM (fun env sort => mkLemmasTyped (genCongruences sort) s env) componentL env;;
  (* TODO check if component has binders
   * should probably use a nonempty list for the component then *)
  (** * Renamings *)
  env <- mkLemmasTyped (genUpRens upList) s env;;
  env <- mkLemmasTyped (genRenamings component) s env;;
  (** * Substitutions *)
  env <- mkLemmasTyped (genUpSubsts upList) s env;;
  env <- mkLemmasTyped (genSubstitutions component) s env;;
  (** * idSubst *)
  env <- mkLemmasTyped (genUpIds upList) s env;;
  env <- mkLemmasTyped (genIdLemmas component) s env;;
  (** * Extensionality *)
  env <- mkLemmasTyped (genUpExtRens upList) s env;;
  env <- mkLemmasTyped (genExtRens component) s env;;
  env <- mkLemmasTyped (genUpExts upList) s env;;
  env <- mkLemmasTyped (genExts component) s env;;
  (** * Combinations *)
  env <- mkLemmasTyped (genUpRenRens upList) s env;;
  env <- mkLemmasTyped (genCompRenRens component) s env;;
  env <- mkLemmasTyped (genUpRenSubsts upList) s env;;
  env <- mkLemmasTyped (genCompRenSubsts component) s env;;
  env <- mkLemmasTyped (genUpSubstRens upList) s env;;
  env <- mkLemmasTyped (genCompSubstRens component) s env;;
  env <- mkLemmasTyped (genUpSubstSubsts upList) s env;;
  env <- mkLemmasTyped (genCompSubstSubsts component) s env;;
  (** * rinstInst *)
  env <- mkLemmasTyped (genUpRinstInsts upList) s env;;
  env <- mkLemmasTyped (genRinstInsts component) s env;;
  env <- mkLemmasTyped (genLemmaRinstInsts componentL) s env;;
  (** * rinstId/instId *)
  env <- mkLemmasTyped (genLemmaInstIds componentL) s env;;
  env <- mkLemmasTyped (genLemmaRinstIds componentL) s env;;
  (** * varL *)
  env <- mkLemmasTyped (genVarLs componentL) s env;;
  env <- mkLemmasTyped (genVarLRens componentL) s env;;
  (** * Combinations *)
  env <- mkLemmasTyped (genLemmaCompRenRens componentL) s env;;
  env <- mkLemmasTyped (genLemmaCompRenSubsts componentL) s env;;
  env <- mkLemmasTyped (genLemmaCompSubstRens componentL) s env;;
  env <- mkLemmasTyped (genLemmaCompSubstSubsts componentL) s env;;
  tmReturn env.

Compute upList_tm.

From ASUB Require unscoped core.
Require Setoid Morphisms.

Module generation.
  Import Setoid Morphisms.
  (* Compute (GenM.run (genUpRens upList_ty) Hsig_example.mySig empty_state). *)
  Time MetaCoq Run (generate initial_env ("ty",[]) upList_ty >>= tmEval TemplateMonad.Common.all >>=
                             fun env => generate env ("tm", ["vl"]) upList_tm >>= tmEval TemplateMonad.Common.all >>=
                                              tmDefinition "env1").

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


