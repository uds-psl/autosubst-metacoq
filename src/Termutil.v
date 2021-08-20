Require Import String Arith List.
Import ListNotations.
Open Scope string.

From MetaCoq.Template Require Import Ast.
From ASUB Require Import Language Utils Quotes GallinaGen SubstTy Names GenM DeBruijnMap.
Import GenM.Notations GenM.


Definition nat_ := nTerm nat_q.
Definition eq_ (s t: nterm) := nApp (nTerm eq_q) [nHole; s; t].
Definition eq_refl_ := nApp (nTerm eq_refl_q) [nHole; nHole].
Definition ap_ (s t: nterm) := nApp (nTerm ap_q) [ nHole; nHole; s; nHole; nHole; t ].
Definition eq_trans_ (s t: nterm) := nApp (nTerm eq_trans_q) [nHole; nHole; nHole; nHole; s; t].
Definition eq_sym_ (s: nterm) := nApp (nTerm eq_sym_q) [nHole; nHole; nHole; s].
Definition eq_ind_r_ p px eqyx := nApp (nTerm eq_ind_r_q) [nHole; nHole; p; px; nHole; eqyx ].
Definition f_equal_ (feq_lam s t H: nterm) := nApp (nTerm f_equal_q) [nHole; nHole; feq_lam; s; t; H].
Definition up_ren_ (s: nterm) := nApp (nTerm up_ren_q) [s].
Definition scons_ (s t: nterm) := nApp (nTerm scons_q) [nHole; s; t].
Definition var_zero_ := nTerm var_zero_q.
Definition funcomp_ (f g: nterm) : nterm := nApp (nTerm funcomp_q) [nHole; nHole; nHole; f; g].
Definition shift_ := nTerm shift_q.
Definition id_ := nApp (nTerm id_q) [nHole].
Definition up_ren_ren_ := nTerm up_ren_ren_q.
Definition funcomps_ ss ts := map2 funcomp_ (sty_terms ss) (sty_terms ts).

Notation "g >>> f" := (funcomp_ f g) (at level 70, no associativity).
Notation "tt <<>> ss" := (funcomps_ ss tt) (at level 70, no associativity).


(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.


(* Definition lambda_ (bname: string) (ty body: term) := *)
(*   tLambda {| binder_name := nNamed bname; binder_relevance := Relevant |} ty body. *)

Definition add_binders (bs: list (string * nterm)) (body: nterm) :=
  List.fold_right (fun '(bname, btype) body => nLambda bname btype body) body bs.

Definition add_tbinders (bs: list (string * nterm)) (body: nterm) :=
  List.fold_right (fun '(bname, btype) body => nProd bname btype body) body bs.

(** * The following definitions are just hardcoded for System F ty *)

(** Create the argument type for the variable constructor of the given sort.
 ** If we create well scoped code fin will be indexed by the element of the scope indices
 ** corresponding to the sort.
 ** For sort vl and ns = [nty; nvl], create fin nvl *)

(* TODO make general *)
Definition genVarArg (sort: string) : nterm := nat_.

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

Definition toVar (sort: tId) (ts: SubstTy) : t nterm :=
  substSorts <- substOf sort;;
  let zs := List.filter (fun '(substSort, _) => eqb sort substSort) (combine substSorts (sty_terms ts)) in
  match zs with
  | [] => error "toVar was called with incompatible sort and substitution vector."
  | z::_ => pure (snd z)
  end.

Definition app_constr (cname: string) (rest: list nterm) : nterm :=
  match rest with
  | [] => nRef cname
  | _ => nApp (nRef cname) rest
  end.

Definition map_ f ts := nApp (nRef (sep f "map")) ts.
Definition var_constr (sort: tId) := nRef (varConstrName sort).

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
Definition equiv_ (n: nterm) (s t: nterm) : nterm :=
  let equality := eq_ (nApp s [ n ]) (nApp t [ n ]) in
  equality.

Definition mk_var_apps (sort: tId) : t (list nterm) :=
  substSorts <- substOf sort;;
  a_map (fun substSort => pure (nRef (varConstrName substSort))) substSorts.

Definition mapId_ f ts := nApp (nRef (sep f "id")) ts.
Definition mapExt_ f ts := nApp (nRef (sep f "ext")) ts.
Definition mapComp_ f ts := nApp (nRef (sep f "comp")) ts.


Definition substify (sort: tId) (xis: SubstTy) :=
  substSorts <- substOf sort;;
  a_map2 (fun substSort xi =>
pure (xi >>> app_ref (varConstrName substSort) []))
         substSorts (sty_terms xis).

(* TODO if I want to actually use isRec I would need to change the dbody of all the fexprs so I probably won't use it. *)
(* convert a list of fixpoint bodies into as many fixpoint definitions. Each fixpoint definitions references all the fixpoint bodies but has a different index into the list of bodies. *)
Definition buildFixpoint (fixBodies: list (def nterm)) (isRec: bool) : t (list lemma) :=
  fixNames <- a_map get_fix_name fixBodies;;
  register_names fixNames;;
  let fixExprs :=  mapi (fun n _ => nFix fixBodies n) fixBodies in
  fixExprs <- a_map (translate DB.empty) fixExprs;;
  pure (map2 (fun name t => (name, hole, t)) fixNames fixExprs).

(* TODO make genRenS and genSubstS return a list of binders *)
Definition genRenS (name: string) : nterm * (string * nterm) :=
  (nRef name, (name, nArr nat_ nat_)).

Definition genRen (name: string) (sort: tId) : t (SubstTy * list (string * nterm)) :=
  substSorts <- substOf sort;;
  let names := List.map (sep name) substSorts in
  let binders := List.map (fun name => (name, nArr nat_ nat_)) names in
  pure (SubstRen (List.map nRef names), binders).

Definition genRen2 (name: string) (sort: tId) (substSorts: list tId) : SubstTy * list (string * nterm) :=
  let names := List.map (sep name) substSorts in
  let binders := List.map (fun name => (name, nArr nat_ nat_)) names in
  (SubstRen (List.map nRef names), binders).


(* TODO first component should be nterm directly? *)
Definition genSubstS (name: string) (sort: tId) : nterm * (string * nterm) :=
  (nRef name, (name, nArr nat_ (nRef sort))).

Definition genSubst (name: string) (sort: tId) :=
  substSorts <- substOf sort;;
  let names := List.map (sep name) substSorts in
  let binders := map2 (fun name substSort => (name, nArr nat_ (nRef substSort))) names substSorts in
  pure (SubstSubst (List.map nRef names), binders).

Definition genEqS (name: string) (bn: string * nterm) (sigma tau: nterm) : nterm * (string * nterm) :=
  let '(n, nt) := bn in
  (nRef name, (name, nProd n nt (equiv_ (nRef n) sigma tau))).

Definition genEq (name: string) (sort: tId) (sigmas taus: list nterm) (f: string -> Binder -> nterm -> t nterm) :=
  substSorts <- substOf sort;;
  let names := List.map (sep name) substSorts in
  let binders := map2 (fun n '(s, t) => (n, nProd "x" nHole (equiv_ (nRef "x") s t))) names (combine sigmas taus) in
  pure (SubstEq (List.map nRef names) f, binders).


Definition introDBVar (name: string) : nterm * (string * nterm) :=
  (nRef name, (name, nat_)).
Definition introSortVar (name: string) (sort: tId) : nterm * (string * nterm) :=
  (nRef name, (name, app_ref sort [])).


Definition shift (hasRen: bool) (substSorts: list tId) (sort: tId) :=
  if hasRen
  then shift_
  else funcomp_ shift_ (nApp (var_constr sort) (List.map (fun _ => nHole) substSorts)).

Definition patternSId (sort: tId) (binder: Binder) :=
  substSorts <- substOf sort;;
  hasRen <- hasRenaming sort;;
  up sort (fun substSort b _ => match b with
                             | Single bsort =>
                               if eqb substSort bsort then shift hasRen substSorts substSort else id_
                             end)
     (List.map nRef substSorts) binder.


Definition mk_scons (sort: tId) (binder: Binder) (sigma: nterm) :=
  match binder with
  | Single sort' => if eqb sort sort'
                   then
let zero := nApp (nRef (varConstrName sort)) [var_zero_] in
scons_ zero sigma
                   else sigma
  end.

Definition upSubstT (binder: Binder) (sort: tId) (sigma: nterm) : t nterm :=
  hasRen <- hasRenaming sort;;
  pat <- patternSId sort binder;;
  let f := if hasRen
           then nRef (renName sort)
           else nRef (substName sort) in
  let sigma' := sigma >>> (nApp f pat) in
  pure (mk_scons sort binder sigma').                   

(* TODO f does not really need to be a function? *)
Definition matchFin_ (bn: string * nterm) (equality: nterm) (s: nterm) (f: nterm -> nterm) (b: nterm) :=
  let '(n, nt) := bn in
  let branches := [ (0, b); (1, nLambda "n'" nat_ (f (nRef "n'"))) ] in
  let elimPred := nLambda n nt equality in
  nCase "nat" 0 elimPred s branches.

Definition comp_ren_or_subst (sort: tId) (stys1 stys2: SubstTy) :=
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

