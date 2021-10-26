Require Import String Arith List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import Ast.
From ASUB Require Import Language Utils Quotes Nterm GallinaGen SubstTy Names GenM DeBruijnMap AssocList Flags.
Import GenM.Notations GenM.


Definition nat_ := nTerm nat_q.
Definition S_ (n: nterm) := nApp (nTerm S_q) [n].
Definition plus_ (s t: nterm) := nApp (nTerm plus_q) [s; t].
Definition fin_ (n: nterm) := nApp (nTerm fin_q) [n].
Definition eq_ (s t: nterm) := nApp (nTerm eq_q) [nHole; s; t].
Definition eq_refl'_ (sO: option nterm) :=
  match sO with
  | None => nApp (nTerm eq_refl_q) [nHole; nHole]
  | Some s => nApp (nTerm eq_refl_q) [nHole; s]
  end.
Definition eq_refl_ := eq_refl'_ None.
Definition ap_ (s t: nterm) := nApp (nTerm ap_q) [ nHole; nHole; s; nHole; nHole; t ].
Definition eq_trans_ (s t: nterm) := nApp (nTerm eq_trans_q) [nHole; nHole; nHole; nHole; s; t].
Definition eq_sym_ (s: nterm) := nApp (nTerm eq_sym_q) [nHole; nHole; nHole; s].
Definition eq_ind_r_ p px eqyx := nApp (nTerm eq_ind_r_q) [nHole; nHole; p; px; nHole; eqyx ].
Definition f_equal_ (feq_lam s t H: nterm) := nApp (nTerm f_equal_q) [nHole; nHole; feq_lam; s; t; H].
Definition funcomp_ (f g: nterm) : nterm := nApp (nTerm funcomp_q) [nHole; nHole; nHole; f; g].
Definition id_ := nApp (nTerm id_q) [nHole].
Definition funcomps_ ss ts := map2 funcomp_ (sty_terms ss) (sty_terms ts).

(* binderlist *)
Definition var_zero_p_ (p: nterm) := nApp (nTerm fintype_var_zero_p_q) [p; nHole].
Definition scons_p_ (p s t: nterm) := nApp (nTerm fintype_scons_p_q) [nHole; p; nHole; s; t].
Definition shift_p_ (p: nterm) := nApp (nTerm fintype_shift_p_q) [p; nHole].
Definition upRen_p_ (p s: nterm) := nApp (nTerm fintype_upRen_p_q) [p; nHole; nHole; s].
Definition scons_p_eta_ (s t u: nterm) := nApp (nTerm fintype_scons_p_eta_q) [nHole; nHole; nHole; nHole; nHole; s; nHole; t; u].
Definition scons_p_congr_ (s t: nterm) := nApp (nTerm fintype_scons_p_congr_q) [nHole; nHole; nHole; nHole; nHole; nHole; nHole; nHole; t; s].
Definition scons_p_comp_ (s t u v: nterm) := nApp (nTerm fintype_scons_p_comp'_q) [nHole; nHole; nHole; nHole; s; t; u; v].
Definition scons_p_head_ (s t u: nterm) := nApp (nTerm fintype_scons_p_head'_q) [nHole; nHole; nHole; s; t; u].
Definition scons_p_tail_ (s t u: nterm) := nApp (nTerm fintype_scons_p_tail'_q) [nHole; nHole; nHole; s; t; u].
Definition up_ren_ren_p_ (s: nterm) := nApp (nTerm fintype_up_ren_ren_p_q) [nHole; nHole; nHole; nHole; nHole; nHole; nHole; s].


Notation "g >>> f" := (funcomp_ f g) (at level 70, no associativity).
Notation "tt <<>> ss" := (funcomps_ ss tt) (at level 70, no associativity).


(** * Helper functions based on scope type *)
Definition scons_ (sc: scope_type) (s t: nterm) :=
  match sc with
  | Unscoped => nApp (nTerm unscoped_scons_q) [nHole; s; t]
  | Wellscoped => nApp (nTerm fintype_scons_q) [nHole; nHole; s; t]
  end.
Definition var_zero_ (sc: scope_type) :=
  match sc with
  | Unscoped => nTerm unscoped_var_zero_q
  | Wellscoped => nApp (nTerm fintype_var_zero_q) [nHole]
  end.
Definition shift_ (sc: scope_type) :=
  match sc with
  | Unscoped => nTerm unscoped_shift_q
  | Wellscoped => nApp (nTerm fintype_shift_q) [nHole]
  end.
Definition up_ren_ (sc: scope_type) (s: nterm) :=
  match sc with
  | Unscoped => nApp (nTerm unscoped_up_ren_q) [s]
  | Wellscoped => nApp (nTerm fintype_up_ren_q) [nHole; nHole; s]
  end.
Definition up_ren_ren_ (sc: scope_type) (xi zeta rho eq : nterm) :=
  match sc with
  | Unscoped => nApp (nTerm unscoped_up_ren_ren_q) [xi; zeta; rho; eq]
  | Wellscoped => nApp (nTerm fintype_up_ren_ren_q) [nHole; nHole; nHole; xi; zeta; rho; eq]
  end.

(*** Functors *)
(* TODO add other functors *)
Definition functorMap_ f ts :=
  match f with
  | AFCod => nApp (nTerm cod_map_q) (List.app [nHole; nHole; nHole] ts)
  | AFList => nApp (nTerm list_map_q) (List.app [nHole; nHole] ts)
  end.
Definition functorId_ f ts :=
  match f with
  | AFCod => nApp (nTerm cod_id_q) (List.app [nHole; nHole; nHole] ts)
  | AFList => nApp (nTerm list_id_q) (List.app [nHole; nHole] ts)
  end.
Definition functorExt_ f ts :=
  match f with
  | AFCod => nApp (nTerm cod_ext_q) (List.app [nHole; nHole; nHole; nHole; nHole] ts)
  | AFList => nApp (nTerm list_ext_q) (List.app [nHole; nHole; nHole; nHole] ts)
  end.
Definition functorComp_ f ts :=
  match f with
  | AFCod => nApp (nTerm cod_comp_q) (List.app [nHole; nHole; nHole; nHole; nHole; nHole; nHole] ts)
  | AFList => nApp (nTerm list_comp_q) (List.app [nHole; nHole; nHole; nHole; nHole; nHole] ts)
  end.
Definition appFunctor_ f ts :=
  match f with
  | AFCod => nApp (nTerm cod_q) ts
  | AFList => nApp (nTerm list_q) ts
  end.

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.


Definition process_implicits (name: string) (args: list gallinaArg) : t unit :=
  let implicits := List.map g_implicit args in
  register_implicits name implicits.

Definition add_binders (args: list gallinaArg) (innerProof: nterm) : nterm :=
  List.fold_right (fun '{| g_name := name; g_type := argType |} proof => nLambda name argType proof)
                  innerProof args.

Definition add_tbinders (args: list gallinaArg) (innerType: nterm) : nterm :=
  List.fold_right (fun '{| g_name := name; g_type := argType |} type => nProd name argType type)
                  innerType args.

Definition process_lemma (name: string) (args: list gallinaArg) (innerType innerProof: nterm) : t nlemma :=
  let type := add_tbinders args innerType in
  let proof := add_binders args innerProof in
  process_implicits name args;;
  pure (name, type, proof).



(** * Construct the body of a definition depending on if the given sort matches the one in the binder *)
Definition definitionBody (sort: tId) (binder: Binder) (singleMatch singleNoMatch: nterm) (listMatch listNoMatch: string -> tId -> nterm) : nterm :=
  match binder with
  | Single boundSort => if eqb sort boundSort
                       then singleMatch
                       else singleNoMatch
  | BinderList p boundSort => if eqb sort boundSort
                             then listMatch p boundSort
                             else listNoMatch p boundSort
  end.

(** Extract the extra shifting argument from a BinderList.
 ** In MetaCoq all binders are explicit so we don't even have the binvparameters function *)
Definition binvparameters (binder: Binder) : list nterm * list gallinaArg :=
  match binder with
  | Single x => ([], [])
  | BinderList m _ => ([nRef m], [implArg m nat_])
  end.

Definition bparameters (binder: Binder) : list nterm * list gallinaArg :=
  let '(terms, binders) := binvparameters binder in
  (terms, List.map makeExplicitArg binders).

Definition abs_ref x t := nLambda x nHole t.
Definition app_ref n ts := nApp (nRef n) ts.
(* Definition app_const n ts := nApp (nConst n) ts. *)
Definition app_sort (sort: tId) (st: scope_type) (scope: substScope) := app_ref sort (ss_terms (is_wellscoped st) scope).
Definition app_constr (cname: string) (st: scope_type) (scope: substScope) (rest: list nterm) : nterm :=
  app_ref cname (List.app (ss_terms (is_wellscoped st) scope) rest).

Definition var_constr (sort: tId) := nRef (varConstrName sort).


Definition toVarHelper (sort: tId) (assoc: SFMap.t nterm) : t nterm :=
  match SFMap.find assoc sort with
  | None => error "toVar was called with incompatible sort and substitution vector. The substitution vector must contain the sort!"
  | Some t => pure t
  end.

Definition toVar (sort: tId) (st: substTy) : t nterm :=
  substSorts <- substOf sort;;
  toVarHelper sort (SFMap.fromList (List.combine substSorts (sty_terms st))).
Definition toVarScope (sort: tId) (ss: substScope) : t nterm :=
  substSorts <- substOf sort;;
  toVarHelper sort (SFMap.fromList (List.combine substSorts (ss_terms_all ss))).

(** Create the argument type for the variable constructor of the given sort.
 ** If we create well scoped code fin will be indexed by the element of the scope indices
 ** corresponding to the sort.
 ** For sort vl and ns = [nty; nvl], create fin nvl *)
Definition genVarArg (sort: string) (ns: substScope) : t nterm :=
  scope_type <- get_scope_type;;
  match scope_type with
  | Unscoped => pure nat_
  | Wellscoped => fmap fin_ (toVarScope sort ns)
  end.

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
Definition equiv_ (n: nterm) (s t: nterm) : nterm :=
  let equality := eq_ (nApp s [ n ]) (nApp t [ n ]) in
  equality.

Definition succ_ (n: nterm) (sort: tId) (b: Binder) :=
  match b with
  | Single boundSort => if eqb sort boundSort
                       then S_ n
                       else n
  | BinderList m boundSort => if eqb sort boundSort
                             then plus_ (nRef m) n
                             else n
  end.


Definition up (sort: tId) (f: tId -> Binder -> nterm -> nterm) (n: list nterm) (b: Binder) : t (list nterm) :=
  substSorts <- substOf sort;;
  pure (map2 (fun p n_i => f p b n_i) substSorts n).

Definition ups (sort: tId) (f: string -> Binder -> nterm -> nterm) := m_fold_left (up sort f).

Definition upScope (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (n: nterm) => succ_ n z b) terms binders.

Definition upRen (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (xi: nterm) => nApp (nRef (upRenName z b)) (List.app (fst (bparameters b)) [ xi ])) terms binders.

(* TODO rename *)
Definition upSubstS (sort: tId) (binders: list Binder) (terms: list nterm) := ups sort (fun (z: string) (b: Binder) (sigma: nterm) => nApp (nRef (upName z b)) (List.app (fst (bparameters b)) [ sigma ])) terms binders.

Definition up' (x: string) (f: tId -> Binder -> nterm -> t nterm) (n: list nterm) (b: Binder) : t (list nterm) :=
  substSorts <- substOf x;;
  a_map (fun '(p, n_i) => f p b n_i) (combine substSorts n).

Definition upEq (sort: tId) (binders: list Binder) (terms: list nterm) (f: tId -> Binder -> nterm -> t nterm) :=
  m_fold_left (up' sort f) terms binders.

Definition upSubstScope (sort: tId) (binders: list Binder) (ss: substScope) :=
  match ss with
  | SubstScope ns nts => fmap (fun nts => SubstScope ns nts) (upScope sort binders nts)
  end.
Definition upSubst (sort: tId) (binders: list Binder) (st: substTy) :=
  match st with
  | SubstRen nts => fmap (fun nts => SubstRen nts) (upRen sort binders nts)
  | SubstSubst nts => fmap (fun nts => SubstSubst nts) (upSubstS sort binders nts)
  | SubstEq nts f => fmap (fun nts => SubstEq nts f) (upEq sort binders nts f)
  end.

Definition cast (sort sort': tId) (nts: list nterm) :=
  substSorts <- substOf sort;;
  substSorts' <- substOf sort';;
  pure (List.fold_right (fun '(x, v) ws => if list_mem x substSorts' then v :: ws else ws)
                        [] (combine substSorts nts)).

Definition castSubstScope (sort sort': tId) (ss: substScope) :=
  match ss with
  | SubstScope ns nts => fmap (fun nts => SubstScope ns nts) (cast sort sort' nts)
  end.
Definition castSubst (sort sort': tId) (st: substTy) :=
  match st with
  | SubstRen nts => fmap (fun nts => SubstRen nts) (cast sort sort' nts)
  | SubstSubst nts => fmap (fun nts => SubstSubst nts) (cast sort sort' nts)
  | SubstEq nts f => fmap (fun nts => SubstEq nts f) (cast sort sort' nts)
  end.

Definition castUpSubstScope (sort: tId) (binders: list Binder) (sort': tId) (ss: substScope) : t substScope :=
  ss' <- castSubstScope sort sort' ss;;
  upSubstScope sort' binders ss'.
Definition castUpSubst (sort: tId) (binders: list Binder) (sort': tId) (st: substTy) : t substTy :=
  st' <- castSubst sort sort' st;;
  upSubst sort' binders st'.
(** * Create an application of the var constructor for each element of the substitition vector
 ** * of the given sort
 ** * e.g. [ var_ty m_ty; var_vl m_ty m_vl ] *)
Definition mk_var_apps (sort: tId) (ms: substScope) : t (list nterm) :=
  substSorts <- substOf sort;;
  scope_type <- get_scope_type;;
  a_map (fun substSort =>
ms' <- castSubstScope sort substSort ms;;
pure (app_constr (varConstrName substSort) scope_type ms' []))
        substSorts.

(** * Convert a renaming to a substitution by postcomposing it with the variable constructor
 ** * of the given sort. The domain of xis is the given ns *)
Definition substify (sort: tId) (ns: substScope) (xis: substTy) :=
  substSorts <- substOf sort;;
  scope_type <- get_scope_type;;
  a_map2 (fun substSort xi =>
ns' <- castSubstScope sort substSort ns;;
pure (xi >>> app_constr (varConstrName substSort) scope_type ns' []))
         substSorts (sty_terms xis).

(* TODO if I want to actually use isRec I would need to change the dbody of all the fexprs so I probably won't use it. *)
(* convert a list of fixpoint bodies into as many fixpoint definitions. Each fixpoint definitions references all the fixpoint bodies but has a different index into the list of bodies. *)
Definition buildFixpoint (fixBodies: list (def nterm)) (isRec: bool) : t (list nlemma) :=
  a_mapi (fun n d => name <- get_fix_name d;;
                  let body := nFix fixBodies n in (* each definition contains the whole fixpoint *)
                  pure (name, d.(dtype), body))
         fixBodies.

Definition genFixpoint (genF : tId -> t (def nterm)) (component: NEList.t tId) : t (list nlemma) :=
  let componentL := NEList.to_list component in
  isRec <- isRecursive component;;
  fexprs <- a_map genF componentL;;
  buildFixpoint fexprs isRec.

Definition renT (st: scope_type) (m n: nterm) :=
  match st with
  | Unscoped => nArr nat_ nat_
  | Wellscoped => nArr (fin_ m) (fin_ n)
  end.

Definition substT (st: scope_type) (m : nterm) (ns: substScope) (sort: tId) :=
  match st with
  | Unscoped => nArr nat_ (nRef sort)
  | Wellscoped => nArr (fin_ m) (app_sort sort st ns)
  end.

Definition introScopeVarS (name: string) : t (nterm * list gallinaArg) :=
  scope_type <- get_scope_type;;
  match scope_type with
  | Unscoped =>
    pure (nRef name, [])
  | Wellscoped =>
    pure (nRef name, [implArg name nat_])
  end.

Definition introScopeVar (name: string) (sort: tId) : t (substScope * list gallinaArg) :=
  substSorts <- substOf sort;;
  let names := List.map (sep name) substSorts in
  scope_type <- get_scope_type;;
  let binders := guard (is_wellscoped scope_type) (List.map (fun name => implArg name nat_) names) in
  pure (SubstScope names (List.map nRef names), binders).
                      
(* TODO make genRenS and genSubstS return a list of binders *)
Definition genRenS (name: string) (st: scope_type) (m n: nterm) : nterm * gallinaArg :=
  (nRef name, explArg name (renT st m n)).

Definition genRen (name: string) (sort: tId) (ms ns: substScope) : t (substTy * list gallinaArg) :=
  substSorts <- substOf sort;;
  scope_type <- get_scope_type;;
  let names := List.map (sep name) substSorts in
  let types := map2 (renT scope_type) (ss_terms_all ms) (ss_terms_all ns) in
  pure (SubstRen (List.map nRef names), map2 explArg names types).

(* Definition genRen2 (name: string) (sort: tId) (substSorts: list tId) : substTy * list (string * nterm) := *)
(*   let names := List.map (sep name) substSorts in *)
(*   let binders := List.map (fun name => (name, nArr nat_ nat_)) names in *)
(*   (SubstRen (List.map nRef names), binders). *)

(* TODO first component should be nterm directly? *)
Definition genSubstS (name: string) (st: scope_type) (m: nterm) (ns: substScope) (sort: tId) : nterm * gallinaArg :=
  (nRef name, explArg name (substT st m ns sort)).

Definition genSubst (name: string) (sort: tId) (ms ns: substScope) : t (substTy * list gallinaArg) :=
  substSorts <- substOf sort;;
  scope_type <- get_scope_type;;
  let names := List.map (sep name) substSorts in
  types <- a_map2 (fun substSort m => ns' <- castSubstScope sort substSort ns;;
                                 pure (substT scope_type m ns' substSort))
                substSorts (ss_terms_all ms);;
  pure (SubstSubst (List.map nRef names), map2 explArg names types).

Definition genEqS (name: string) '{| g_name := bname; g_type := btype |} (sigma tau: nterm) : nterm * gallinaArg :=
  (nRef name, explArg name (nProd bname nHole (equiv_ (nRef bname) sigma tau))).

Definition genEq (name: string) (sort: tId) (sigmas taus: list nterm) (f: string -> Binder -> nterm -> t nterm) : t (substTy * list gallinaArg) :=
  substSorts <- substOf sort;;
  let names := List.map (sep name) substSorts in
  (* TODO hole could be filled  *)
  let binders := map2 (fun name '(s, t) => explArg name (nProd "x" nHole (equiv_ (nRef "x") s t))) names (combine sigmas taus) in
  pure (SubstEq (List.map nRef names) f, binders).

Definition introUpVar (name: string) (idx: nterm): t (nterm * gallinaArg) :=
  scope_type <- get_scope_type;;
  match scope_type with
  | Unscoped => pure (nRef name, explArg name nat_)
  | Wellscoped => pure (nRef name, explArg name (fin_ (S_ idx)))
  end.

Definition introSortVar (name: string) (ms: substScope) (sort: tId) : t (nterm * gallinaArg) :=
  scope_type <- get_scope_type;;
  pure (nRef name, explArg name (app_sort sort scope_type ms)).


Definition patternSId (sort: tId) (binder: Binder) :=
  substSorts <- substOf sort;;
  hasRen <- hasRenaming sort;;
  sc <- get_scope_type;;
  let ss := SubstScope (List.map (const "_") substSorts)
                       (List.map (const nHole) substSorts) in
  let shift shiftSort :=
      if hasRen
      then shift_ sc
      else shift_ sc
                  >>> app_constr (varConstrName shiftSort) sc ss [] in
  let shiftp p shiftSort :=
      if hasRen
      then shift_p_ (nRef p)
      else shift_p_ (nRef p)
                  >>> app_constr (varConstrName shiftSort) sc ss [] in
  up sort (fun substSort b _ => match b with
                             | Single boundSort =>
                               if eqb substSort boundSort
                               then shift substSort
                               else id_
                             | BinderList p boundSort =>
                               if eqb substSort boundSort
                               then shiftp p substSort
                               else id_
                             end)
     (List.map nRef substSorts) binder.

Definition patternSIdNoRen (sort: tId) (binder: Binder) :=
  substSorts <- substOf sort;;
  sc <- get_scope_type;;
  let shift _ := shift_ sc in
  let shiftp p _ := shift_p_ (nRef p) in
  up sort (fun substSort b _ => match b with
                             | Single boundSort =>
                               if eqb substSort boundSort
                               then shift substSort
                               else nApp id_ [nHole]
                             | BinderList p boundSort =>
                               if eqb substSort boundSort
                               then shiftp p substSort
                               else nApp id_ [nHole]
                             end)
     (List.map nRef substSorts) binder.


Definition mk_scons (sort: tId) (binder: Binder) (sigma: nterm) (ms: substScope) : t nterm :=
  scope_type <- get_scope_type;;
  match binder with
  | Single boundSort =>
    if eqb sort boundSort
    then let zero := app_constr (varConstrName sort) scope_type ms [var_zero_ scope_type] in
         pure (scons_ scope_type zero sigma)
    else pure sigma
  | BinderList p boundSort =>
    if eqb sort boundSort
    then let zero := var_zero_p_ (nRef p)
                             >>> app_constr (varConstrName sort) scope_type ms [] in
         pure (scons_p_ (nRef p) zero sigma)
    else pure sigma
  end.

Definition upSubstT (binder: Binder) (sort: tId) (sigma: nterm) (ms: substScope) : t nterm :=
  hasRen <- hasRenaming sort;;
  pat <- patternSId sort binder;;
  ms' <- upSubstScope sort [binder] ms;;
  let f := if hasRen
           then nRef (renName sort)
           else nRef (substName sort) in
  let sigma' := sigma >>> (nApp f pat) in
  mk_scons sort binder sigma' ms'.

(* TODO f does not really need to be a function? *)
Definition matchFin_ '{| g_name := bname; g_type := btype |} (equality: nterm) (s: nterm) (f: nterm -> nterm) (b: nterm) : t nterm :=
  scope_type <- get_scope_type;;
  match scope_type with
  | Unscoped =>
    let branches := [ (0, b); (1, nLambda "n'" nat_ (f (nRef "n'"))) ] in
    let elimPred := nLambda bname btype equality in
    pure (nCase "nat" 0 elimPred s branches)
  | Wellscoped =>
    let branches := [ (1, nLambda "fin_n" nHole (f (nRef "fin_n"))); (0, b) ] in
    let elimPred := nLambda bname btype equality in
    pure (nCase "option" 1 elimPred s branches)
  end.

Definition comp_ren_or_subst (sort: tId) (stys1 stys2: substTy) :=
  substSorts <- substOf sort;;
  renOrSubstName <- match stys1 with
                   | SubstRen _ => pure renName
                   | SubstSubst _ => pure substName
                   | _ => error "comp_ren_or_subst called with wrong subst_ty"
                   end;;
  a_map2 (fun substSort sty2 =>
stys1' <- castSubst sort substSort stys1;;
pure (sty2 >>> app_ref (renOrSubstName substSort) (sty_terms stys1')))
         substSorts (sty_terms stys2).                         


(** * The arity argument to a one_inductive_entry
 ** * TODO the universe of fintype might change between Coq versions or due to other reasons. Can we do it differently? *)
Definition scoped_arity : term :=
  tSort (Universe.from_kernel_repr (Level.lSet, false)
                                   [(Level.Level "ASUB.src.static.fintype.9", false)
                                   
        ]).

Definition unscoped_arity : term :=
  tSort Universe.type0.

