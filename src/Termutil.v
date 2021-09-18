Require Import String Arith List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import Ast.
From ASUB Require Import Language Utils Quotes Nterm GallinaGen SubstTy Names GenM DeBruijnMap AssocList Flags.
Import GenM.Notations GenM.


Definition nat_ := nTerm nat_q.
Definition S_ (n: nterm) := nApp (nTerm S_q) [n].
Definition fin_ (n: nterm) := nApp (nTerm fin_q) [n].
Definition eq_ (s t: nterm) := nApp (nTerm eq_q) [nHole; s; t].
Definition eq_refl_ := nApp (nTerm eq_refl_q) [nHole; nHole].
Definition ap_ (s t: nterm) := nApp (nTerm ap_q) [ nHole; nHole; s; nHole; nHole; t ].
Definition eq_trans_ (s t: nterm) := nApp (nTerm eq_trans_q) [nHole; nHole; nHole; nHole; s; t].
Definition eq_sym_ (s: nterm) := nApp (nTerm eq_sym_q) [nHole; nHole; nHole; s].
Definition eq_ind_r_ p px eqyx := nApp (nTerm eq_ind_r_q) [nHole; nHole; p; px; nHole; eqyx ].
Definition f_equal_ (feq_lam s t H: nterm) := nApp (nTerm f_equal_q) [nHole; nHole; feq_lam; s; t; H].
(* Definition up_ren_ (s: nterm) := nApp (nTerm up_ren_q) [nHole; nHole; s]. *)
Definition up_ren_ (s: nterm) := nApp (nTerm up_ren_q) [s].
(* Definition scons_ (s t: nterm) := nApp (nTerm scons_q) [nHole; nHole; s; t]. *)
Definition scons_ (s t: nterm) := nApp (nTerm scons_q) [nHole; s; t].
(* Definition var_zero_ := nApp (nTerm var_zero_q) [nHole]. *)
Definition var_zero_ := nTerm var_zero_q.
Definition funcomp_ (f g: nterm) : nterm := nApp (nTerm funcomp_q) [nHole; nHole; nHole; f; g].
(* Definition shift_ := nApp (nTerm shift_q) [nHole]. *)
Definition shift_ := nTerm shift_q.
Definition id_ := nApp (nTerm id_q) [nHole].
(* Definition up_ren_ren_ (xi zeta rho eq : nterm) := nApp (nTerm up_ren_ren_q) [nHole; nHole; nHole; xi; zeta; rho; eq]. *)
Definition up_ren_ren_ (xi zeta rho eq : nterm) := nApp (nTerm up_ren_ren_q) [xi; zeta; rho; eq].

Definition funcomps_ ss ts := map2 funcomp_ (sty_terms ss) (sty_terms ts).

Notation "g >>> f" := (funcomp_ f g) (at level 70, no associativity).
Notation "tt <<>> ss" := (funcomps_ ss tt) (at level 70, no associativity).


(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.


(** * A representation of arguments that resembles to one from the Coq implementation.
 ** * When we build an application to some named constant, during translation to the
 ** * MetaCoq AST we pass a number of holes corresponding to how many arguments were
 ** * marked implicit in the call to `add_binders`

 ** * TODO atm we always prepend these holes to the given argument list. This has the
 ** * assumption that there are no implicit arguments after some non-implicit argument.
 ** * To fix this we would have to merge left-nested applications during the translation
 ** * and save the list of implicit positions instead of only their number.
 *)
Record gallinaArg := { g_name : string; g_implicit : bool; g_type : nterm }.
Definition implArg (name: string) (type: nterm) := {| g_name := name; g_implicit := true; g_type := type |}.
Definition explArg (name: string) (type: nterm) := {| g_name := name; g_implicit := false; g_type := type |}.

Definition process_implicits (name: string) (args: list gallinaArg) : t unit :=
  let implicitNum := List.length (list_filter_map (fun '{| g_implicit := implicit |} =>
                                 if implicit then Some tt else None) args) in
  register_implicits name implicitNum.

Definition add_binders (args: list gallinaArg) (innerProof: nterm) : nterm :=
  List.fold_right (fun '{| g_name := name; g_type := argType |} proof => nLambda name argType proof)
                  innerProof args.

Definition add_tbinders (args: list gallinaArg) (innerType: nterm) : nterm :=
  List.fold_right (fun '{| g_name := name; g_type := argType |} type => nProd name argType type)
                  innerType args.

Definition process_lemma (name: string) (args: list gallinaArg) (innerType innerProof: nterm) : t nlemma :=
  let type := add_tbinders args innerType in
  let proof := add_binders args innerProof in
  register_name name;;
  process_implicits name args;;
  pure (name, type, proof).


(** * The following definitions are just hardcoded for System F ty *)


(** Construct the body of a definition depending on if the given sort matches the one in the binder *)
Definition definitionBody (sort: tId) (binder: Binder) (singleMatch singleNoMatch: nterm) (* (f_listMatch: string -> tId -> term)  *) : nterm :=
  match binder with
  | Single sort' => if eqb sort sort'
                   then singleMatch
                   else singleNoMatch
  (* TODO binder list case *)
  (* | L.BinderList (p, sort') -> *)
  (*   let (listMatch, listNoMatch) = f_listMatch p sort' in *)
  (*   if sort = sort' then listMatch else listNoMatch *)
  end.

(** Extract the extra shifting argument from a BinderList.
 ** In MetaCoq all binders are explicit so we don't even have the binvparameters function *)
Definition bparameters (binder: Binder) : list term * list (term -> term) :=
  match binder with
  | Single x => ([], [])
(* | BinderList (m, _) -> ([ref_ m], [binder1_ ~implicit:true ~btype:nat_ m]) *)
  end.

Definition abs_ref x t := nLambda x nHole t.
Definition app_ref n ts := nApp (nRef n) ts.
Definition app_sort (sort: tId) (st: scope_type) (scope: substScope) := app_ref sort (ss_terms (is_wellscoped st) scope).

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

Definition app_constr (cname: string) (st: scope_type) (scope: substScope) (rest: list nterm) : nterm :=
  app_ref cname (List.app (ss_terms (is_wellscoped st) scope) rest).

Definition map_ f ts := nApp (nRef (sep f "map")) ts.
Definition var_constr (sort: tId) := nRef (varConstrName sort).

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
Definition equiv_ (n: nterm) (s t: nterm) : nterm :=
  let equality := eq_ (nApp s [ n ]) (nApp t [ n ]) in
  equality.

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

Definition mapId_ f ts := nApp (nRef (sep f "id")) ts.
Definition mapExt_ f ts := nApp (nRef (sep f "ext")) ts.
Definition mapComp_ f ts := nApp (nRef (sep f "comp")) ts.

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
Definition buildFixpoint (fixBodies: list (def nterm)) (isRec: bool) : t (list lemma) :=
  fixNames <- a_map get_fix_name fixBodies;;
  register_names fixNames;;
  let fixExprs :=  mapi (fun n _ => nFix fixBodies n) fixBodies in
  fixExprs <- a_map translate fixExprs;;
  types <- a_map translate (List.map dtype fixBodies);;
  pure (map2 (fun name '(t, typ) => (name, typ, t)) fixNames (List.combine fixExprs types)).

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


Definition shift (hasRen: bool) (sc: scope_type) (substSorts: list tId) (sort: tId) :=
  if hasRen
  then shift_
  else funcomp_ (app_constr (varConstrName sort) sc (SubstScope (List.map (const "_") substSorts) (List.map (fun _ => nHole) substSorts)) []) shift_.

Definition patternSId (sort: tId) (binder: Binder) :=
  substSorts <- substOf sort;;
  hasRen <- hasRenaming sort;;
  scope_type <- get_scope_type;;
  up sort (fun substSort b _ => match b with
                             | Single bsort =>
                               if eqb substSort bsort then shift hasRen scope_type substSorts substSort else id_
                             end)
     (List.map nRef substSorts) binder.


(* TODO borken indentation *)
Definition mk_scons (sort: tId) (binder: Binder) (sigma: nterm) (ms: substScope) : t nterm :=
  scope_type <- get_scope_type;;
  match binder with
  | Single sort' => if eqb sort sort'
                   then
let zero := app_constr (varConstrName sort) scope_type ms [var_zero_] in
pure (scons_ zero sigma)
                   else pure (sigma)
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

(* Definition testmatchfin : t term := *)
(*   '(n, bns) <- introScopeVarS "n";; *)
(*   '(x, bx) <- introUpVar "x" n;; *)
(*   let innerType := eq_ (nRef "nat") (nRef "nat") in *)
(*   let t := fun (n: nterm) => eq_refl_ in *)
(*   matchFin <- matchFin_ bx innerType x t eq_refl_;; *)
(*   let proof := add_binders (List.app bns [bx]) matchFin in *)
(*   translate proof. *)

(* Definition testfin : t term := *)
(*   '(n, bns) <- introScopeVarS "n";; *)
(*   '(x, bx) <- introUpVar "x" n;; *)
(*   let innerType := nHole in *)
(*   let proof := add_binders (List.app bns [bx]) x in *)
(*   translate proof. *)

(* From ASUB Require Import core unscoped fintype. *)

(* Definition asb : forall n (x: fin (S n)), nat = nat := *)
(*   (fun (n:nat) (x: fin (S n)) => *)
(* match x with *)
(* | None => eq_refl *)
(* | Some fin_n => eq_refl *)
(* end). *)


(* MetaCoq Quote Definition abs_source := Eval hnf in asb. *)

(*


tLambda {| binder_name := nNamed "n"; binder_relevance := Relevant |}
  (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [])
  (tLambda {| binder_name := nNamed "x"; binder_relevance := Relevant |}
     (tApp (tConst (MPfile ["fintype"; "static"; "src"; "ASUB"], "fin") [])
        [tApp
           (tConstruct
              {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1 [])
           [tRel 0]])
     (tCase
        ({| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "option"); inductive_ind := 0 |}, 1,
        Relevant)
        (tLambda {| binder_name := nNamed "x"; binder_relevance := Relevant |}
           (tApp
              (tInd
                 {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "option"); inductive_ind := 0 |}
                 [])
              [tApp
                 (tFix
                    [{|
                       dname := {| binder_name := nNamed "fin"; binder_relevance := Relevant |};
                       dtype :=
                         tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                           (tInd
                              {|
                                inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                inductive_ind := 0
                              |} [])
                           (tSort (Universe.of_levels (inr (Level.Level "ASUB.src.static.fintype.9"))));
                       dbody :=
                         tLambda {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                           (tInd
                              {|
                                inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                inductive_ind := 0
                              |} [])
                           (tCase
                              ({|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                 inductive_ind := 0
                               |}, 0, Relevant)
                              (tLambda {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                                 (tInd
                                    {|
                                      inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                      inductive_ind := 0
                                    |} [])
                                 (tSort (Universe.of_levels (inr (Level.Level "ASUB.src.static.fintype.9")))))
                              (tRel 0)
                              [(0,
                               tInd
                                 {|
                                   inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "False");
                                   inductive_ind := 0
                                 |} []);
                              (1,
                              tLambda {| binder_name := nNamed "m"; binder_relevance := Relevant |}
                                (tInd
                                   {|
                                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                     inductive_ind := 0
                                   |} [])
                                (tApp
                                   (tInd
                                      {|
                                        inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "option");
                                        inductive_ind := 0
                                      |} []) [tApp (tRel 2) [tRel 0]]))]);
                       rarg := 0
                     |}] 0) [tRel 1]])
           (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
              [tSort (Universe.of_levels (inr Level.lSet));
              tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
              tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []]))
        (tRel 0)
        [(1,
         tLambda {| binder_name := nNamed "fin_n"; binder_relevance := Relevant |}
           (tApp
              (tFix
                 [{|
                    dname := {| binder_name := nNamed "fin"; binder_relevance := Relevant |};
                    dtype :=
                      tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                        (tInd
                           {|
                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                             inductive_ind := 0
                           |} []) (tSort (Universe.of_levels (inr (Level.Level "ASUB.src.static.fintype.9"))));
                    dbody :=
                      tLambda {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                        (tInd
                           {|
                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                             inductive_ind := 0
                           |} [])
                        (tCase
                           ({|
                              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |}, 0, Relevant)
                           (tLambda {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                              (tInd
                                 {|
                                   inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                   inductive_ind := 0
                                 |} [])
                              (tSort (Universe.of_levels (inr (Level.Level "ASUB.src.static.fintype.9")))))
                           (tRel 0)
                           [(0,
                            tInd
                              {|
                                inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "False");
                                inductive_ind := 0
                              |} []);
                           (1,
                           tLambda {| binder_name := nNamed "m"; binder_relevance := Relevant |}
                             (tInd
                                {|
                                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                  inductive_ind := 0
                                |} [])
                             (tApp
                                (tInd
                                   {|
                                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "option");
                                     inductive_ind := 0
                                   |} []) [tApp (tRel 2) [tRel 0]]))]);
                    rarg := 0
                  |}] 0) [tRel 1])
           (tApp
              (tConstruct {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |}
                 0 [])
              [tSort (Universe.of_levels (inr Level.lSet));
              tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []]));
        (0,
        tApp
          (tConstruct {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} 0 [])
          [tSort (Universe.of_levels (inr Level.lSet));
          tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []])]))

 *)
(* Eval cbv in (run testfin {| R_flags := {| fl_scope_type := Wellscoped |}; R_sig := Hsig_example.mySig; R_env := initial_env |} empty_state). *)
(* Eval cbv in (run testmatchfin {| R_flags := {| fl_scope_type := Wellscoped |}; R_sig := Hsig_example.mySig; R_env := initial_env |} empty_state). *)

(* From MetaCoq.Template Require Import All. *)

(* MetaCoq Run *)
(*         (match (run testmatchfin {| R_flags := {| fl_scope_type := Wellscoped |}; R_sig := Hsig_example.mySig; R_env := initial_env |} empty_state) with *)
(*          | inl e => tmPrint e *)
(*          | inr (_, _, x) => *)
(*            tmBind (tmUnquoteTyped (forall (n: nat) (x: fin (S n)), nat = nat) x) (fun _ => tmReturn tt) *)
(*          end). *)

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
                                   [(Level.Level "ASUB.src.static.fintype.9", false)]).

Definition unscoped_arity : term :=
  tSort Universe.type0.

Definition succ_ (n: nterm) (sort: tId) (binder: Binder) :=
  match binder with
  | Single boundSort => if eqb sort boundSort
                       then S_ n
                       else n
  end.

Definition genFixpoint (genF : tId -> t (def nterm)) (component: NEList.t tId) : t (list lemma) :=
  let componentL := NEList.to_list component in
  isRec <- isRecursive component;;
  fexprs <- a_map genF componentL;;
  buildFixpoint fexprs isRec.
