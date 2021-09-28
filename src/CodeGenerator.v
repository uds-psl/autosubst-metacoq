Require Import List String.
Import ListNotations.

#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
(* Import MonadNotation. *)
From ASUB Require Import AssocList Language Quotes Utils DeBruijnMap Monad TemplateMonadUtils Names Nterm GallinaGen GenM Termutil SubstTy GenUps Flags.
Import TemplateMonadNotations.

Module fcbv.
  
  From ASUB Require Import CustomEntryParser.
  Import SyntaxNotation Syntax SyntaxTranslation.
Definition fcbv : autosubstLanguage :=
  {| al_sorts := <{ ty : Type;
                    tm : Type;
                    vl : Type }>;
    al_ctors := {{ arr : ty -> ty -> ty;
                   all : (bind ty in ty) -> ty;
                   app : tm -> tm -> tm;
                   tapp : tm -> ty -> tm;
                   vt : vl -> tm;
                   lam : ty -> (bind vl in tm) -> vl;
                   tlam : (bind ty in tm) -> vl }} |}.

  From ASUB Require Import SigAnalyzer ErrorM.

  MetaCoq Run (translate_signature fcbv >>= tmDefinition "fcbv_sig").
  Compute fcbv_sig.

  Definition fcbv_info := {| in_flags := {| fl_scope_type := Wellscoped |};
                             in_implicits := SFMap.empty;
                             in_sig := fcbv_sig;
                             in_env := initial_env |}.
End fcbv.
Import fcbv.

Module GenUpsExample_fcbv.
  Import GenM.Notations GenM.
  
  Definition upList_ty :=
    let m := substSorts <- substOf "ty";;
             sc <- get_scope_type;;
             let '(_, upList) := getUps substSorts [] sc in
             pure upList in
    match runInfo m fcbv_info with
    | inl _ => []
    | inr (_, _, x) => x
    end.
  Compute upList_ty.

  Definition upList_tm :=
    let m := substSorts_ty <- substOf "ty";;
             substSorts <- substOf "tm";;
             sc <- get_scope_type;;
             let '(combinations, _) := getUps substSorts_ty [] sc in
             let '(_, upList) := getUps substSorts combinations sc in
             pure upList in
    match runInfo m fcbv_info with
    | inr (_, _, x) => x
    | _ => []
    end.

  Compute upList_tm.
End GenUpsExample_fcbv.
Import GenUpsExample_fcbv.

(* Module stlc. *)
(*   From ASUB Require Import CustomEntryParser. *)
(*   Import HOASNotation2. *)
(*   Definition stlc : autosubstLanguage := *)
(*     {| al_sorts := <{ ty : Type; *)
(*                       tm : Type }>;  *)
(*                                  al_ctors := {{ Base : - ty; *)
(*                                                 Fun : ty -> ty - ty; *)
(*                                                 app : tm -> tm - tm; *)
(*                                                 lam : ty -> (bind tm in tm) - tm }} |}. *)

(*   From ASUB Require Import SigAnalyzer ErrorM. *)

(*   Definition stlc_sig := *)
(*     match ErrorM.run (translate_signature stlc) tt tt with *)
(*     | inl _ => Hsig_example.mySig *)
(*     | inr (_, _, sig) => sig *)
(*     end. *)

(*   Compute stlc_sig. *)
(*   Definition stlcinfo := {| in_flags := {| fl_scope_type := Unscoped |}; *)
(*                             in_implicits := SFMap.empty; *)
(*                             in_sig := stlc_sig; *)
(*                             in_env := initial_env |}. *)
(* End stlc. *)
(* Import stlc. *)

(* Module GenUpsExample_stlc. *)
(*   Import GenM.Notations GenM. *)

(*   Definition upList_tm := *)
(*     let m := substSorts <- substOf "tm";; *)
(*              let '(_, upList) := getUps substSorts [] in *)
(*              pure upList in *)
(*     match GenM.run m {| R_flags := stlcinfo.(in_flags); R_sig := stlcinfo.(in_sig); R_env := stlcinfo.(in_env) |} (initial_state stlcinfo.(in_implicits)) with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)

(*   Compute upList_tm. *)
(* End GenUpsExample_stlc. *)
(* Import GenUpsExample_stlc. *)

(* Module pi. *)
(*   From ASUB Require Import CustomEntryParser. *)
(*   Import SyntaxNotation SyntaxTranslation Syntax. *)

(* Definition pi : autosubstLanguage := *)
(*   {| al_sorts := <{ chan : Type; *)
(*                     proc : Type }>; *)
(*      al_ctors := {{ Nil : proc; *)
(*                     Bang : proc -> proc; *)
(*                     Res : (bind chan in proc) -> proc; *)
(*                     Par : proc -> proc -> proc; *)
(*                     In : chan -> (bind chan in proc) -> proc; *)
(*                     Out : chan -> chan -> proc -> proc }} |}. *)

(*   From ASUB Require Import SigAnalyzer ErrorM. *)

(*   MetaCoq Run (translate_signature pi >>= tmDefinition "pi_sig"). *)
(*   Compute pi_sig. *)

(*   Definition piinfo := {| in_flags := {| fl_scope_type := Wellscoped |}; *)
(*                             in_implicits := SFMap.empty; *)
(*                             in_sig := pi_sig; *)
(*                             in_env := initial_env |}. *)
(* End pi. *)
(* Import pi. *)

(* Module GenUpsExample_pi. *)
(*   Import GenM.Notations GenM. *)

(*   Definition upList_chan := *)
(*     let m := substSorts <- substOf "chan";; *)
(*              let '(_, upList) := getUps substSorts [] in *)
(*              pure upList in *)
(*     match GenM.runInfo m piinfo with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)
(*   Compute upList_chan. *)

(*   Definition upList_proc := *)
(*     let m := substSortsChan <- substOf "chan";; *)
(*              substSorts <- substOf "proc";; *)
(*              let '(combinations, _) := getUps substSortsChan [] in *)
(*              let '(_, upList) := getUps substSorts combinations in *)
(*              pure upList in *)
(*     match GenM.runInfo m piinfo with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)
(*   Compute upList_proc. *)

(* End GenUpsExample_pi. *)
(* Import GenUpsExample_pi. *)

(* Module fol. *)
(*   From ASUB Require Import CustomEntryParser. *)
(*   Import SyntaxNotation SyntaxTranslation Syntax. *)

(* Definition fol : autosubstLanguage := *)
(*   {| al_sorts := <{ folterm : Type; *)
(*                     form : Type }>; *)
(*      al_ctors := {{ Func (f : nat) : codF (fin f) (folterm) -> folterm; *)
(*                     Fal : form; *)
(*                     Pred (p : nat) : codF (fin p) (folterm) -> form; *)
(*                     Impl : form -> form -> form; *)
(*                     Conj : form -> form -> form; *)
(*                     Disj : form -> form -> form; *)
(*                     All : (bind folterm in form) -> form; *)
(*                     Ex : (bind folterm in form) -> form }} |}. *)

(*   From ASUB Require Import SigAnalyzer. *)

(*   MetaCoq Run (translate_signature fol >>= tmDefinition "fol_sig"). *)

(*   Compute fol_sig. *)
(*   Definition fol_info := {| in_flags := {| fl_scope_type := Wellscoped |}; *)
(*                             in_implicits := SFMap.empty; *)
(*                             in_sig := fol_sig; *)
(*                             in_env := initial_env |}. *)
(* End fol. *)
(* Import fol. *)

(* Module GenUpsExample_fol. *)
(*   Import GenM.Notations GenM. *)

(*   Definition upList_term := *)
(*     let m := substSorts <- substOf "folterm";; *)
(*              let '(_, upList) := getUps substSorts [] in *)
(*              pure upList in *)
(*     match GenM.runInfo m fol_info with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)
(*   Compute upList_term. *)

(*   Definition upList_form := *)
(*     let m := substSortsTerm <- substOf "folterm";; *)
(*              substSorts <- substOf "form";; *)
(*              let '(combinations, _) := getUps substSortsTerm [] in *)
(*              let '(_, upList) := getUps substSorts combinations in *)
(*              pure upList in *)
(*     match GenM.runInfo m fol_info with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)
(*   Compute upList_form. *)

(* End GenUpsExample_fol. *)
(* Import GenUpsExample_fol. *)

(* Module variadic. *)
  
(*   From ASUB Require Import CustomEntryParser SigAnalyzer. *)
(*   Import SyntaxNotation SyntaxTranslation Syntax. *)

(* Definition variadic : autosubstLanguage := *)
(*   {| al_sorts := <{ tm : Type  }>; *)
(*      al_ctors := {{ app : tm -> listF (tm) -> tm; *)
(*                     lam (p: nat) : (bind <p, tm> in tm) -> tm }} |}. *)

(*   MetaCoq Run (translate_signature variadic >>= tmDefinition "variadic_sig"). *)

(*   Compute variadic_sig. *)
(*   Definition variadic_info := {| in_flags := {| fl_scope_type := Wellscoped |}; *)
(*                                  in_implicits := SFMap.empty; *)
(*                                  in_sig := variadic_sig; *)
(*                                  in_env := initial_env |}. *)
(* End variadic. *)
(* Import variadic. *)

(* Module GenUpsExample_variadic. *)
(*   Import GenM.Notations GenM. *)

(*   Definition upList_tm := *)
(*     let m := substSorts <- substOf "tm";; *)
(*              let '(_, upList) := getUps substSorts [] in *)
(*              pure upList in *)
(*     match GenM.runInfo m variadic_info with *)
(*     | inr (_, _, x) => x *)
(*     | _ => [] *)
(*     end. *)
(*   Compute upList_tm. *)

(* End GenUpsExample_variadic. *)
(* Import GenUpsExample_variadic. *)

Module TemplateMonadInterface.

  (** * TemplateMonad function to generate and unquote inductive types.
   ** * It returns an updated environment that contains the new types and their constructors. *)
  Definition mkInductive (m: GenM.t mutual_inductive_entry) (info : genInfo) : TemplateMonad@{_ Set} genInfo :=
    let flags := info.(in_flags) in
    let sig := info.(in_sig) in
    let env := info.(in_env) in
    match GenM.run m {| R_flags := flags; R_sig := sig; R_env := env |} (initial_state info.(in_implicits)) with
    | inl e => tmFail e
    | inr (_, {| st_names := names; st_implicits := implicits |}, mind) =>
      mind_eval <- tmEval TemplateMonad.Common.all mind;;
      tmMkInductive mind_eval;;
      env' <- tm_update_env names env;;
      tmReturn {| in_env := env';
                  in_implicits := implicits;
                  in_flags := flags;
                  in_sig := sig |}
    end.
  
  Definition mkLemmasTyped (m: GenM.t (list lemma)) (info: genInfo) : TemplateMonad@{_ Set} genInfo :=
    let flags := info.(in_flags) in
    let sig := info.(in_sig) in
    let env := info.(in_env) in
    match GenM.run m {| R_flags := flags; R_sig := sig; R_env := env |} (initial_state info.(in_implicits)) with
    | inl e => tmFail e
    | inr (_, {| st_names := names; st_implicits := implicits |}, lemmas) =>
      lemmas_eval <- tmEval TemplateMonad.Common.all lemmas;;
      monad_map tmTypedDefinition lemmas_eval;; 
      env' <- tm_update_env names env;;
      tmReturn {| in_env := env';
                  in_implicits := implicits;
                  in_flags := flags;
                  in_sig := sig |}
    end. 

  (* give a name to the persistent information between code generation calls
   * Necessary because for testing we do code generation incrementally with several commands. *)
  Definition composeGeneration (infoName: string) (info: genInfo) : TemplateMonad@{_ Set} unit :=
    info <- tmEval TemplateMonad.Common.all info;;
    tmDefinition infoName info;;
    tmReturn tt.

  Definition tm_liftGenM {A} (m: GenM.t A) (info: genInfo) : @TemplateMonad@{_ Set} A :=
    match GenM.run m {| R_flags := info.(in_flags); R_sig := info.(in_sig); R_env := info.(in_env) |} (initial_state info.(in_implicits)) with
    | inl e => tmFail e
    | inr (_, _, a) => tmReturn a
    end.

End TemplateMonadInterface.
Import TemplateMonadInterface.


Module inductives.
  Import GenM GenM.Notations.

  (* Generates the type of a variable constructor for a sort
 db : base deBruijn index, should move into a reader monad *)
  Definition genVarConstrType (sort: tId) (ns: substScope) : t nterm :=
    s <- genVarArg sort ns;;
    scope_type <- get_scope_type;;
    pure (mknArrRev [s] (app_sort sort scope_type ns)).

  (* generates the type of a single argument of a constructor *)
  Fixpoint genArg (sort: string) (ns: substScope) (bs: list Binder) (head: ArgumentHead) : t nterm :=
    match head with
    | Atom argSort =>
      upScopes <- castUpSubstScope sort bs argSort ns;;
      scope_type <- get_scope_type;;
      pure (app_sort argSort scope_type upScopes)
    (* DONE implement funapp case *)
    | FunApp fname staticArgs args => 
      args' <- a_map (genArg sort ns bs) args;;
      pure (appFunctor_ fname (staticArgs ++ args'))
    end.

  (** * Generates the type of a given constructor for a sort *)
  Definition genConstructor (sort: tId) (ns: substScope) (ctor: Constructor) : t nterm :=
    up_n_x <- a_map (fun '{| pos_binders := bs; pos_head := head |} => genArg sort ns bs head) ctor.(con_positions);;
    scope_type <- get_scope_type;;
    (* DONE take care of parameters *)
    let targetType := app_sort sort scope_type ns in
    let innerType := mknArrRev up_n_x targetType in
    let ctorType := add_tbinders ctor.(con_parameters) innerType in
    pure ctorType.

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

Definition default_flags := {| fl_scope_type := Wellscoped |}.
MetaCoq Run (mkInductive (genMutualInductive ("ty", [])) {| in_env := GenM.initial_env; in_implicits := SFMap.empty; in_flags := default_flags; in_sig := Hsig_example.mySig |}
                         >>= tmEval TemplateMonad.Common.all
                         >>= mkInductive (genMutualInductive ("tm", ["vl"]))
                         >>= composeGeneration "env0").

(** * stlc *)
(* MetaCoq Run (mkInductive (genMutualInductive ("ty", [])) stlcinfo *)
(*                          >>= tmEval TemplateMonad.Common.all *)
(*                          >>= mkInductive (genMutualInductive ("tm", []))  *)
(*                          >>= composeGeneration "env0"). *)

(** * pi *)
(* MetaCoq Run (mkInductive (genMutualInductive ("chan", [])) piinfo *)
(*                          >>= tmEval TemplateMonad.Common.all *)
(*                          >>= mkInductive (genMutualInductive ("proc", [])) *)
(*                          >>= composeGeneration "env0"). *)

(** * fol *)
(* From ASUB Require Import fintype core. *)
(* Inductive folterm (n_term : nat) : Type := *)
(*   | var_folterm : fin n_term -> folterm n_term *)
(*   | Func : forall f : nat, cod (fin f) (folterm n_term) -> folterm n_term. *)
(* Inductive form (n_term : nat) : Type := *)
(*   | Fal : form n_term *)
(*   | Pred : forall p : nat, cod (fin p) (folterm n_term) -> form n_term *)
(*   | Impl : form n_term -> form n_term -> form n_term *)
(*   | Conj : form n_term -> form n_term -> form n_term *)
(*   | Disj : form n_term -> form n_term -> form n_term *)
(*   | All : form (S n_term) -> form n_term *)
(*   | Ex : form (S n_term) -> form n_term. *)

(* MetaCoq Run (locate_mind "term" >>= tmPrint). *)

(* Definition myterm := *)
(* {| *)
(*   mind_entry_record := None; *)
(*   mind_entry_finite := Finite; *)
(*   mind_entry_params := *)
(*     [{| *)
(*        decl_name := {| binder_name := nNamed "n_term"; binder_relevance := Relevant |}; *)
(*        decl_body := None; *)
(*        decl_type := *)
(*          tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [] *)
(*      |}]; *)
(*   mind_entry_inds := *)
(*     [{| *)
(*        mind_entry_typename := "term"; *)
(*        mind_entry_arity := *)
(*          tSort *)
(*            {| *)
(*              Universe.t_set := *)
(*                {| *)
(*                  UnivExprSet.this := *)
(*                    [(Level.lSet, 0); (Level.Level "ASUB.src.static.fintype.1", 0); *)
(*                    (Level.Level "ASUB.src.static.core.101", 0)]; *)
(*                  UnivExprSet.is_ok := *)
(*                    UnivExprSet.Raw.add_ok (s:=[(Level.lSet, 0); (Level.Level "ASUB.src.static.fintype.1", 0)]) *)
(*                      (Level.Level "ASUB.src.static.core.101", 0) *)
(*                      (UnivExprSet.Raw.add_ok (s:=[(Level.lSet, 0)]) *)
(*                         (Level.Level "ASUB.src.static.fintype.1", 0) *)
(*                         (UnivExprSet.Raw.singleton_ok (Level.lSet, 0))) *)
(*                |}; *)
(*              Universe.t_ne := *)
(*                Universes.Universe.add_obligation_1 (Level.Level "ASUB.src.static.core.101", 0) *)
(*                  {| *)
(*                    Universe.t_set := *)
(*                      {| *)
(*                        UnivExprSet.this := [(Level.lSet, 0); (Level.Level "ASUB.src.static.fintype.1", 0)]; *)
(*                        UnivExprSet.is_ok := *)
(*                          UnivExprSet.Raw.add_ok (s:=[(Level.lSet, 0)]) *)
(*                            (Level.Level "ASUB.src.static.fintype.1", 0) *)
(*                            (UnivExprSet.Raw.singleton_ok (Level.lSet, 0)) *)
(*                      |}; *)
(*                    Universe.t_ne := *)
(*                      Universes.Universe.add_obligation_1 (Level.Level "ASUB.src.static.fintype.1", 0) *)
(*                        {| *)
(*                          Universe.t_set := *)
(*                            {| *)
(*                              UnivExprSet.this := [(Level.lSet, 0)]; *)
(*                              UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok (Level.lSet, 0) *)
(*                            |}; *)
(*                          Universe.t_ne := eq_refl *)
(*                        |} *)
(*                  |} *)
(*            |}; *)
(*        mind_entry_consnames := ["var_term"; "Func"]; *)
(*        mind_entry_lc := *)
(*          [tProd {| binder_name := nAnon; binder_relevance := Relevant |} *)
(*             (tApp (tConst (MPfile ["fintype"; "static"; "src"; "ASUB"], "fin") []) [tRel 0]) *)
(*             (tApp (tRel 2) [tRel 1]); *)
(*          tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |} *)
(*            (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []) *)
(*            (tProd {| binder_name := nAnon; binder_relevance := Relevant |} *)
(*               (tApp (tConst (MPfile ["core"; "static"; "src"; "ASUB"], "cod") []) *)
(*                  [tApp (tConst (MPfile ["fintype"; "static"; "src"; "ASUB"], "fin") []) [tRel 0]; *)
(*                  tApp (tRel 2) [tRel 1]]) (tApp (tRel 3) [tRel 2]))] *)
(*      |}]; *)
(*   mind_entry_universes :=(* Monomorphic_entry (LevelSet.empty, ConstraintSet.empty); *) *)
(*     Monomorphic_entry *)
(*       ({| VSet.this := []; VSet.is_ok := LevelSet.Raw.empty_ok |}, *)
(*       {| *)
(*         CS.this := *)
(*           [(Level.lSet, ConstraintType.Le BinNums.Z0, Level.Level "ASUB.src.static.core.103"); *)
(*           (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*           Level.Level "ASUB.src.static.core.102"); *)
(*           (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*           Level.Level "ASUB.src.static.core.103"); *)
(*           (Level.Level "ASUB.src.static.core.101", ConstraintType.Le BinNums.Z0, *)
(*           Level.Level "ASUB.src.static.core.103")]; *)
(*         CS.is_ok := *)
(*           ConstraintSet.Raw.add_ok *)
(*             (s:=[(Level.lSet, ConstraintType.Le BinNums.Z0, Level.Level "ASUB.src.static.core.103"); *)
(*                 (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*                 Level.Level "ASUB.src.static.core.102"); *)
(*                 (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*                 Level.Level "ASUB.src.static.core.103")]) *)
(*             (Level.Level "ASUB.src.static.core.101", ConstraintType.Le BinNums.Z0, *)
(*             Level.Level "ASUB.src.static.core.103") *)
(*             (ConstraintSet.Raw.add_ok *)
(*                (s:=[(Level.lSet, ConstraintType.Le BinNums.Z0, Level.Level "ASUB.src.static.core.103"); *)
(*                    (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*                    Level.Level "ASUB.src.static.core.102")]) *)
(*                (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*                Level.Level "ASUB.src.static.core.103") *)
(*                (ConstraintSet.Raw.add_ok *)
(*                   (s:=[(Level.lSet, ConstraintType.Le BinNums.Z0, Level.Level "ASUB.src.static.core.103")]) *)
(*                   (Level.Level "ASUB.src.static.fintype.1", ConstraintType.Le BinNums.Z0, *)
(*                   Level.Level "ASUB.src.static.core.102") *)
(*                   (ConstraintSet.Raw.add_ok (s:=[]) *)
(*                      (Level.lSet, ConstraintType.Le BinNums.Z0, Level.Level "ASUB.src.static.core.103") *)
(*                      ConstraintSet.Raw.empty_ok))) *)
(*       |}); *)
(*   mind_entry_template := false; *)
(*   mind_entry_variance := None; *)
(*   mind_entry_private := None *)
(* |}. *)

(* Print mutual_inductive_entry. *)
(* Search universes_entry. *)
(* Search ContextSet.t. *)
(* (* TemplateLookup.monomorphic_udecl_decl: TemplateEnvironment.global_decl -> ContextSet.t *) *)
(* Search global_decl. *)
(* Search constant_body. *)
(* (* tmQuoteConstant *) *)


(* Definition locate_kername (name: string) : TemplateMonad@{_ Set} kername := *)
(*   loc <- tmLocate1 name;; *)
(*   match loc with *)
(*   | ConstRef kn => tmReturn kn *)
(*   | _ => tmFail (String.append "unknown name or name is not an inductive/constructor/constant: " name) *)
(*   end. *)
(* From ASUB Require Import fintype core. *)

(* MetaCoq Run (locate_kername "fin" >>= fun kn => tmQuoteConstant kn true >>= tmDefinition "finbody" >>= fun body => tmDefinition "findecl" (ConstantDecl body) >>= fun decl => tmDefinition "finctx" (monomorphic_udecl_decl decl) >>= fun ctx => tmDefinition "finuniv" (Monomorphic_entry ctx)). *)
(* MetaCoq Run (locate_kername "cod" >>= fun kn => tmQuoteConstant kn true >>= tmEval all >>= tmDefinition "codbody"). *)

(* MetaCoq Run (tmQuoteRecTransp fin true >>= tmEval all >>= tmPrint). *)

      
(* MetaCoq Run (tmMkInductive myterm). *)


(* MetaCoq Run (mkInductive (genMutualInductive ("term", [])) fol_info *)
(*                          >>= tmEval TemplateMonad.Common.all *)
(*                          >>= mkInductive (genMutualInductive ("form", [])) *)
(*                          >>= composeGeneration "env0"). *)

(** * variadic *)
(* DONE in app constructor the arguments seem to be swapped
 was because I reverse the positions in the parser *)
(* DONE and in lam constructor a apparently applies S and not plus
 was because I parsed everything as a Single *)

(* Compute (GenM.runInfo (genMutualInductive ("tm", [])) variadic_info). *)

(* also universe constraint errors *)
(* MetaCoq Run (mkInductive (genMutualInductive ("tm", [])) variadic_info *)
(*                          >>= composeGeneration "env0"). *)


Module congruences.
  Import GenM GenM.Notations.

  Definition createImpBinders (params: list gallinaArg) : list gallinaArg :=
    List.map (fun g => let '{| g_name := p_name;
                            g_implicit := _;
                            g_type := p_type |} := g in
                    {| g_name := p_name; g_implicit := true; g_type := p_type |})
             params.

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
    arg_tys <- a_map (fun '{| pos_binders := bs; pos_head := head |} => genArg sort ms bs head) con_positions;;
    let Hs := getPattern "H" con_positions in
    (* building the binders of the lemma *)
    let bss := map2 explArg ss arg_tys in
    let bts := map2 explArg ts arg_tys in
    let bparameters := createImpBinders con_parameters in
    let parameters' := List.map (fun arg => nRef arg.(g_name)) con_parameters in
    let eqs := map2 (fun s t => eq_ (nRef s) (nRef t)) ss ts in
    let beqs := map2 explArg Hs eqs in
    (* generate the type of the lemma *)
    let innerType := eq_ (app_constr con_name scope_type ms (List.app parameters' (List.map nRef ss)))
                         (app_constr con_name scope_type ms (List.app parameters' (List.map nRef ts))) in
    (* body of the lemma *)
    let (_, innerProof) := fold_left
                         (fun '(i, t) H =>
                            let feq_args := map nRef (firstn i ts ++ ["x"] ++ skipn (S i) ss) in
                            let feq_lam := abs_ref "x" (app_constr con_name scope_type ms (List.app parameters' feq_args)) in
                            let feq := f_equal_ feq_lam nHole nHole (nRef H) in
                            (S i, eq_trans_ t feq))
                         Hs
                         (0, eq_refl_) in
    (* generate and register lemma name *)
    let name := congrName con_name in
    process_lemma name (bparameters ++ bms ++ bss ++ bts ++ beqs) innerType innerProof.


  (** * generates the terms for the congruence lemmas of the constructors of an inductive type *)
  Definition genCongruences (sort: tId) : t (list lemma) :=
    ctors <- constructors sort;;
    a_map (fun ctor => translate_lemma (genCongruence sort ctor)) ctors.
End congruences.
Import congruences.

MetaCoq Run (mkLemmasTyped (genCongruences "ty") env0
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genCongruences "tm")
                           >>= tmEval TemplateMonad.Common.all
                           >>= mkLemmasTyped (genCongruences "vl")
                           >>= composeGeneration "env1").

(** * stlc *)
(* MetaCoq Run (mkLemmasTyped (genCongruences "ty") env0 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genCongruences "tm")  *)
(*                            >>= composeGeneration "env1"). *)

(** * pi *)
(* MetaCoq Run (mkLemmasTyped (genCongruences "chan") env0 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genCongruences "proc") *)
(*                            >>= composeGeneration "env1"). *)

(** * fol *)
(* we had to write the inductive types so we put them into the environment explicitly *)


(* MetaCoq Run (env <- tm_update_env ["folterm"; "var_folterm"; "Func"; "form"; "Fal"; "Pred"; "Impl"; "Conj"; "Disj"; "All"; "Ex"] initial_env;; *)
(*              let info := {| in_flags := {| fl_scope_type := Wellscoped |}; *)
(*                             in_implicits := SFMap.empty; *)
(*                             in_sig := fol_sig; *)
(*                             in_env := env |} in *)
(*              info <- tmEval all info;; *)
(*              tmDefinition "env0" info). *)
(* MetaCoq Run (mkLemmasTyped (genCongruences "folterm") env0 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genCongruences "form") *)
(*                            >>= composeGeneration "env1"). *)

Module traversal.
  Import GenM.Notations GenM.
  
  (* TODO implement
   * but I think I already do it in sem_default *)
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

  Definition extra_arg_list (extra_arg: option nterm) : list nterm :=
    match extra_arg with
    | None => []
    | Some e => [e]
    end.

  Fixpoint arg_map (sort: tId) (args: list substTy) (nameF: string -> string) (no_args: nterm -> nterm) (funsem: AutosubstFunctor -> list nterm -> nterm) (bs: list Binder) (extra_arg : option nterm) (arg: ArgumentHead) :=
    match arg with
    | Atom y =>
      b <- hasArgs y;;
      args <- a_map (castUpSubst sort bs y) args;;
      pure (if b
                 (* TODO can these two holes also be handled in GallinaGen?
                  * In theory it should because we have an nApp with an nRef
                  * but (nameF y) should be in the environment *)
            then nApp (nRef (nameF y))
                      (List.app (flat_map sty_terms args)
                                (extra_arg_list extra_arg))
            else
              match extra_arg with
              | None => abs_ref "x" (no_args (nRef "x"))
              | Some s => no_args s
              end)
    | FunApp f p xs =>
      res <- a_map (arg_map sort args nameF no_args funsem bs None) xs;;
      pure (funsem f (List.app res (extra_arg_list extra_arg)))
    end.

  
  Definition mk_constr_pattern (s: string) (sort: tId) (args: list substTy) (nameF: string -> string) (no_args: nterm -> nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: AutosubstFunctor -> list nterm -> nterm) (ctor: Constructor) : t (nat * nterm) :=
    let ss := getPattern "s" ctor.(con_positions) in
    positions <- a_map (fun '(s, {| pos_binders := binders; pos_head := head |}) =>
                         arg_map sort args nameF no_args funsem binders (Some (nRef s)) head)
                      (combine ss ctor.(con_positions));;
    let paramNames := List.map g_name ctor.(con_parameters) in
    pure (branch_ 0 (List.app paramNames ss) (sem paramNames ctor.(con_name) positions)).
  
  Definition traversal (sort: tId) (ms: substScope) (nameF: string -> string) (no_args: nterm -> nterm) (ret: nterm -> nterm) (bargs: list gallinaArg) (args: list substTy) (var_case_body: nterm -> t nterm) (sem: list string -> string -> list nterm -> nterm) (funsem: AutosubstFunctor -> list nterm -> nterm) : t (def nterm) :=
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

  Definition no_args_default := fun s => eq_refl'_ (Some s).

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
    let '(_, bpms) := bparameters binder in
    scope_type <- get_scope_type;;
    '(m, bm) <- introScopeVarS "m";;
    '(n, bn) <- introScopeVarS "n";;
    let '(xi, bxi) := genRenS "xi" scope_type m n in
    (* let '(_, bpms) := bparameters binder in *)
    let m_succ := succ_ m sort binder in
    let n_succ := succ_ n sort binder in
    let innerType := renT scope_type m_succ n_succ in
    let innerProof := definitionBody sort binder
                                     (up_ren_ scope_type xi) xi
                                     (fun p _ => upRen_p_ (nRef p) xi) (fun _ _ => xi) in
    let name := upRenName sort binder in
    process_lemma name (List.concat [bpms; bm; bn; [bxi]]) innerType innerProof.

  Definition genUpRens (bss: list (Binder * tId)) : t (list (string * term * term)) :=
    a_map (fun bs => translate_lemma (genUpRen bs)) bss.


  (* TODO fcbv hangs here atm *)
  Definition genRenaming (sort: tId) : t (def nterm) :=
    '(ms, bms) <- introScopeVar "m" sort;;
    '(ns, bns) <- introScopeVar "n" sort;;
    '(xis, bxis) <- genRen "xi" sort ms ns;;
    substSorts <- substOf sort;;
    scope_type <- get_scope_type;;
    let ret _ := app_sort sort scope_type ns in
    traversal sort ms renName Datatypes.id ret (List.concat [bms; bns; bxis]) [ xis ]
              (fun s => toVarT <- toVar sort xis;;
                     pure (nApp (app_constr (varConstrName sort) scope_type ns []) [ nApp toVarT [ s ] ]))
              (fun paramNames cname positions => app_constr cname scope_type ns (List.app (List.map nRef paramNames) positions))
              functorMap_.

  Definition genRenamings := genFixpoint genRenaming.
End renamings.
Import renamings.


MetaCoq Run (mkLemmasTyped (genUpRens upList_ty) env1 >>= composeGeneration "env2").
MetaCoq Run (mkLemmasTyped (genRenamings ("ty", [])) env2 >>= composeGeneration "env3").
MetaCoq Run (mkLemmasTyped (genUpRens upList_tm) env3 >>= composeGeneration "env4").
MetaCoq Run (mkLemmasTyped (genRenamings ("tm", ["vl"])) env4 >>= composeGeneration "env5").

(** * stlc *)
(* MetaCoq Run (mkLemmasTyped (genUpRens upList_tm) env1 >>= composeGeneration "env4"). *)
(* MetaCoq Run (mkLemmasTyped (genRenamings ("tm", [])) env4 >>= composeGeneration "env5"). *)



Module substitutions.
  Import GenM.Notations GenM.

  Definition genUpSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(_, bpms) := bparameters binder in
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
    process_lemma name (List.concat [bpms; bm; bns; [ bsigma ]]) innerType innerProof.

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
              functorMap_.

  Definition genSubstitutions := genFixpoint genSubstitution.
    
End substitutions.
Import substitutions.

(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_ty) env5 >>= composeGeneration "env6"). *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("ty", [])) env6 >>= composeGeneration "env7"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_tm) env7 >>= composeGeneration "env8"). *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("tm", ["vl"])) env8 >>= composeGeneration "env9"). *)

(** * pi *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("chan", [])) env1 >>= composeGeneration "env5"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_chan) env5 >>= composeGeneration "env6"). *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("proc", [])) env6 >>= composeGeneration "env7"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_proc) env7 >>= composeGeneration "env8"). *)

(** * fol *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("folterm", [])) env1 >>= composeGeneration "env5"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_term) env5 >>= composeGeneration "env6"). *)
(* MetaCoq Run (mkLemmasTyped (genSubstitutions ("form", [])) env6 >>= composeGeneration "env7"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubsts upList_form) env7 >>= composeGeneration "env8"). *)

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
    let '(pms, bpms) := binvparameters binder in
    sc <- get_scope_type;;
    '(ms, bms) <- introScopeVar "m" sort;;
    m_var <- toVarScope sort ms;;
    let '(sigma, bsigma) := genSubstS "sigma" sc m_var ms sort in
    '(x, bx) <- selectUpScopeVar "x" sort binder ms;;
    let '(eq, beq) := genEqS "Eq" bx sigma (app_constr (varConstrName sort) sc ms []) in
    ms_up <- upSubstScope sort [binder] ms;;
    (** * type *)
    let innerType := equiv_ x
                       (app_ref (upName sort binder) (List.app pms [ sigma ]))
                       (app_constr (varConstrName sort) sc ms_up []) in
    (** * body *)
    shift <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let t n := ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) shift)
                   (nApp eq [ n ]) in
    matchFin <- matchFin_ bx innerType x t eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (t x)
                                    (fun _ _ => scons_p_eta_ (app_constr (varConstrName sort) sc ms_up [])
                                                          (abs_ref "n" (t (nRef "n"))) (abs_ref "n" eq_refl_))
                                    (fun _ _ => t x)
    in
    (** * name *)
    let name := upIdName sort binder in
    process_lemma name (List.concat [bpms; bms; [ bsigma; beq; bx ]]) innerType innerBody.
  
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
              functorId_.

  Definition genIdLemmas := genFixpoint genIdLemma.

End idsubsts.
Import idsubsts.

(* MetaCoq Run (mkLemmasTyped (genUpIds upList_ty) env9 >>= composeGeneration "env10"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("ty", [])) env10 >>= composeGeneration "env11"). *)
(* MetaCoq Run (mkLemmasTyped (genUpIds upList_tm) env11 >>= composeGeneration "env12"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("tm", ["vl"])) env12 >>= composeGeneration "env13"). *)

(** * pi *)
(* MetaCoq Run (mkLemmasTyped (genUpIds upList_chan) env8 >>= composeGeneration "env10"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("chan", [])) env10 >>= composeGeneration "env11"). *)
(* MetaCoq Run (mkLemmasTyped (genUpIds upList_proc) env11 >>= composeGeneration "env12"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("proc", [])) env12 >>= composeGeneration "env13"). *)

(** * fol *)
(* MetaCoq Run (mkLemmasTyped (genUpIds upList_term) env8 >>= composeGeneration "env10"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("folterm", [])) env10 >>= composeGeneration "env11"). *)
(* MetaCoq Run (mkLemmasTyped (genUpIds upList_form) env11 >>= composeGeneration "env12"). *)
(* MetaCoq Run (mkLemmasTyped (genIdLemmas ("form", [])) env12 >>= composeGeneration "env13"). *)

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
    let '(pms, bpms) := binvparameters binder in
    scope_type <- get_scope_type;;
    '(m, bms) <- introScopeVarS "m";;
    '(n, bns) <- introScopeVarS "n";;
    let '(xi, bxi) := genRenS "xi" scope_type m n in
    let '(zeta, bzeta) := genRenS "zeta" scope_type m n in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx xi zeta in
    (* type *)
    let innerType := equiv_ x
                            (nApp (nRef (upRenName sort binder)) (List.app pms [ xi ]))
                            (nApp (nRef (upRenName sort binder)) (List.app pms [ zeta ])) in
    (* body *)
    let innerBodyHelper n := nApp eq [n] in
    matchFin <- matchFin_ bx innerType x (fun n => ap_ (shift_ scope_type) (nApp eq [n])) eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun p _ => scons_p_congr_ (abs_ref "n" (ap_ (shift_p_ (nRef p))
                                                                              (innerBodyHelper (nRef "n"))))
                                                            (abs_ref "n" eq_refl_))
                                    (fun _ _ => innerBodyHelper x)
    in
    (* name *)
    let name := upExtRenName sort binder in
    process_lemma name (List.concat [bpms; bms; bns; [bxi; bzeta; beq; bx ]]) innerType innerBody.
  
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
              functorExt_.

  Definition genExtRens (component: NEList.t tId) : t (list lemma) :=
    let componentL := NEList.to_list component in
    isRec <- isRecursive component;;
    fexprs <- a_map genExtRen componentL;;
    buildFixpoint fexprs isRec.

  
  Definition genUpExt (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    let '(pms, bpms) := binvparameters binder in
    scope_type <- get_scope_type;;
    '(m, bms) <- introScopeVarS "m";;
    '(ns, bns) <- introScopeVar "n" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" scope_type m ns sort in
    let '(tau, btau) := genSubstS "tau" scope_type m ns sort in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx sigma tau in
    (* type *)
    let innerType := equiv_ x
                            (nApp (nRef (upName sort binder)) (List.app pms [ sigma ]))
                            (nApp (nRef (upName sort binder)) (List.app pms [ tau ])) in
    (* body *)
    pat <- patternSId sort binder;;
    hasRen <- hasRenaming sort;;
    let innerBodyHelper n := ap_ (nApp (nRef (if hasRen then renName sort else substName sort)) pat)
                                 (nApp eq [n]) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun _ _ => scons_p_congr_ (abs_ref "n" (innerBodyHelper (nRef "n")))
                                                            (abs_ref "n" eq_refl_))
                                    (fun _ _ => innerBodyHelper x)
    in
    (* name *)
    let name := upExtName sort binder in
    process_lemma name (List.concat [bpms; bms; bns; [ bsigma; btau; beq; bx ]]) innerType innerBody.
    
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
              functorExt_.

  Definition genExts := genFixpoint genExt.

End extensionality.
Import extensionality.

(* MetaCoq Run (mkLemmasTyped (genUpExtRens upList_ty) env13 *)
(*                            >>= tmEval TemplateMonad.Common.all >>= *)
(*                            mkLemmasTyped (genUpExts upList_ty)  *)
(*                            >>= composeGeneration "env14"). *)

(* MetaCoq Run (mkLemmasTyped (genUpExtRens upList_tm) env14 *)
(*                            >>= tmEval TemplateMonad.Common.all >>= *)
(*                            mkLemmasTyped (genUpExts upList_tm)  *)
(*                            >>= composeGeneration "env15"). *)

(* MetaCoq Run (mkLemmasTyped (genExtRens ("ty", [])) env15 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genExts ("ty", []))  *)
(*                            >>= composeGeneration "env16"). *)

(* MetaCoq Run (mkLemmasTyped (genExtRens ("tm", ["vl"])) env16 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genExts ("tm", ["vl"]))  *)
(*                            >>= composeGeneration "env17"). *)


(** * pi *)

(* MetaCoq Run (mkLemmasTyped (genUpExts upList_chan) env13 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genUpExts upList_proc) *)
(*                            >>= composeGeneration "env14"). *)

(* MetaCoq Run (mkLemmasTyped (genExts ("chan", [])) env14 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genExts ("proc", [])) *)
(*                            >>= composeGeneration "env17"). *)

(* fol *)

(* MetaCoq Run (mkLemmasTyped (genUpExts upList_term) env13 *)
(*                            >>= tmEval TemplateMonad.Common.all  *)
(*                            >>= mkLemmasTyped (genUpExts upList_form)  *)
(*                            >>= composeGeneration "env14"). *)

(* MetaCoq Run (mkLemmasTyped (genExts ("folterm", [])) env14 *)
(*                            >>= tmEval TemplateMonad.Common.all *)
(*                            >>= mkLemmasTyped (genExts ("form", [])) *)
(*                            >>= composeGeneration "env17"). *)

Module renRen.
  Import GenM.Notations GenM.
  
  Definition genUpRenRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    sc <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(k, bks) <- introScopeVarS "k";;
    '(l, bls) <- introScopeVarS "l";;
    '(m, bms) <- introScopeVarS "m";;
    let '(xi, bxi) := genRenS "xi" sc k l in
    let '(zeta, bzeta) := genRenS "zeta" sc l m in
    let '(rho, brho) := genRenS "rho" sc k m in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> zeta) rho in
    (* type *)
    let innerType := equiv_ x (app_ref (upRenName sort binder) (List.app pms [xi])
                                 >>> app_ref (upRenName sort binder) (List.app pms [zeta]))
                            (app_ref (upRenName sort binder) (List.app pms [rho])) in
    (* body *)
    (* a.d. here I have to take care to also pass x to up_ren_ren and to eq in the second case of definitionBody *)
    let innerBody := definitionBody sort binder
                                    (nApp (up_ren_ren_ sc xi zeta rho eq) [x]) (nApp eq [x])
                                    (* TODO had to add x argument because in OCaml it was inferred *)
                                    (fun _ _ => nApp (up_ren_ren_p_ eq) [x])
                                    (* TODO here I also had to add the x. Why don't I need to add it elsewhere.
                                     Also this is a nice tidbit to complain that Coq's exact still does inference *)
                                    (fun _ _ => nApp eq [x])
    in
    (* name *)
    let name := upRenRenName sort binder in
    process_lemma name (List.concat [bpms; bks; bls; bms; [bxi; bzeta; brho; beq; bx]]) innerType innerBody.

  Definition genUpRenRens (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpRenRen bs)) bss.


  Definition genCompRenRen (sort: tId) : t (def nterm) :=
    scope_type <- get_scope_type;;
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
                                                 then pure (up_ren_ren_ scope_type nHole nHole nHole s)
                                                 else pure s
                                    | BinderList _ _ => pure (up_ren_ren_p_ s)
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
              functorComp_.
              
  Definition genCompRenRens := genFixpoint genCompRenRen.
End renRen.
Import renRen.

(* MetaCoq Run (mkLemmasTyped (genUpRenRens upList_ty) env17 >>= composeGeneration "env18"). *)
(* MetaCoq Run (mkLemmasTyped (genUpRenRens upList_tm) env18 >>= composeGeneration "env19"). *)
(* MetaCoq Run (mkLemmasTyped (genCompRenRens ("ty", [])) env19 >>= composeGeneration "env20"). *)
(* MetaCoq Run (mkLemmasTyped (genCompRenRens ("tm", ["vl"])) env20 >>= composeGeneration "env21"). *)

Module renSubst.
  Import GenM.Notations GenM.
  

  Definition genUpRenSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    scope_type <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(k, bks) <- introScopeVarS "k";;
    '(l, bls) <- introScopeVarS "l";;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(xi, bxi) := genRenS "xi" scope_type k l in
    let '(tau, btau) := genSubstS "tau" scope_type l ms sort in
    let '(theta, btheta) := genSubstS "theta" scope_type k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> tau) theta in
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) (List.app pms [xi]))
                                 >>> (app_ref (upName sort binder) (List.app pms [tau])))
                            (app_ref (upName sort binder) (List.app pms [theta])) in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper n := ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    let innerBodyHelper2 := eq_trans_ (scons_p_comp_ nHole nHole nHole x)
                                      (scons_p_congr_ (abs_ref "z"
                                                               (eq_trans_ (scons_p_tail_ nHole nHole (nApp xi [nRef "z"]))
                                                                          (innerBodyHelper (nRef "z"))))
                                                      (abs_ref "z" (scons_p_head_ nHole nHole (nRef "z")))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun _ _ => innerBodyHelper2)
                                    (fun _ _ => innerBodyHelper x)
    in
    (* name *)
    let name := upRenSubstName sort binder in
    process_lemma name (List.concat [bpms; bks; bls; bms; [bxi; btau; btheta; beq; bx]]) innerType innerBody.

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
              functorComp_.
    
  Definition genCompRenSubsts := genFixpoint genCompRenSubst.
End renSubst.
Import renSubst.

(* MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_ty) env21 >>= composeGeneration "env22"). *)
(* MetaCoq Run (mkLemmasTyped (genUpRenSubsts upList_tm) env22 >>= composeGeneration "env23"). *)
(* MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("ty", [])) env23 >>= composeGeneration "env24"). *)
(* MetaCoq Run (mkLemmasTyped (genCompRenSubsts ("tm", ["vl"])) env24 >>= composeGeneration "env25"). *)

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
Module substRen.
  Import GenM.Notations GenM.
  

  Definition genUpSubstRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    substSorts <- substOf sort;;
    sc <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(k, bks) <- introScopeVarS "k";;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" sc k ls sort in
    '(zetas, bzetas) <- genRen "zeta" sort ls ms;;
    let '(theta, btheta) := genSubstS "theta" sc k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    (* sigma >> <zeta> =1 theta *)
    let '(eq, beq) := genEqS "Eq" bx (sigma >>> app_ref (renName sort) (sty_terms zetas)) theta in
    ms_up <- upSubstScope sort [binder] ms;;
    zetas_up <- upSubst sort [binder] zetas;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) (List.app pms [sigma]))
                                 >>> (app_ref (renName sort) (sty_terms zetas_up)))
                            (app_ref (upName sort binder) (List.app pms [theta])) in
    (* body *)
    let compRenRenArgs n := List.concat [map2 funcomp_ pat (sty_terms zetas);
                                        List.map (const (abs_ref "x" eq_refl_)) pat;
                                        [ nApp sigma [n] ]] in
    let innerBodyHelper n :=
        eq_trans_ (app_ref (compRenRenName sort)
                           (List.concat [pat; sty_terms zetas_up; compRenRenArgs n]))
                  (eq_trans_ (eq_sym_ (app_ref (compRenRenName sort)
                                               (List.concat [sty_terms zetas; pat; compRenRenArgs n])))
                             (ap_ (app_ref (renName sort) pat)
                                  (nApp eq [n]))) in
    let innerBodyHelper2 n boundSort :=
        eq_trans_ (app_ref (compRenRenName sort)
                           (List.concat [pat; sty_terms zetas_up;
                                        map2 funcomp_ pat (sty_terms zetas);
                                        List.map (fun x => abs_ref "x" (if eqb x boundSort
                                                                     then scons_p_tail_ nHole nHole (nRef "x")
                                                                     else eq_refl_)) substSorts;
                                        [ nApp sigma [n] ]]))
                  (eq_trans_ (eq_sym_ (app_ref (compRenRenName sort)
                                               (List.concat [sty_terms zetas; pat;
                                                            map2 funcomp_ pat (sty_terms zetas);
                                                            List.map (const (abs_ref "x" eq_refl_)) pat;
                                                            [ nApp sigma [n] ]])))
                             (ap_ (app_ref (renName sort) pat)
                                  (nApp eq [n]))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun _ boundSort => eq_trans_ (scons_p_comp_ nHole nHole nHole x)
                                                               (scons_p_congr_ (abs_ref "n" (innerBodyHelper2 (nRef "n") boundSort))
                                                                               (abs_ref "x" (ap_ (app_constr (varConstrName sort) sc ms_up [])
                                                                                                 (scons_p_head_ nHole nHole (nRef "x"))))))
                                    (fun _ boundSort => innerBodyHelper2 x boundSort)
    in
    (* name *)
    let name := upSubstRenName sort binder in
    process_lemma name (List.concat [bpms; bks; bls; bms; [bsigma]; bzetas; [btheta]; [beq]; [bx]]) innerType innerBody.

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
              functorComp_.

  Definition genCompSubstRens := genFixpoint genCompSubstRen.
End substRen.
Import substRen.

(* MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_ty) env25 >>= composeGeneration "env26"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubstRens upList_tm) env26 >>= composeGeneration "env27"). *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstRens ("ty", [])) env27 >>= composeGeneration "env28"). *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstRens ("tm", ["vl"])) env28 >>= composeGeneration "env29"). *)

Module substSubst.
  Import GenM.Notations GenM.
  
  Definition genUpSubstSubst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    substSorts <- substOf sort;;
    sc <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(k, bks) <- introScopeVarS "k";;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" sc k ls sort in
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    let '(theta, btheta) := genSubstS "theta" sc k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx
                             (sigma >>> app_ref (substName sort) (sty_terms taus))
                             theta in
    ls_up <- upSubstScope sort [binder] ls;;
    taus_up <- upSubst sort [binder] taus;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) (List.app pms [sigma]))
                                 >>> (app_ref (substName sort) (sty_terms taus_up)))
                            (app_ref (upName sort binder) (List.app pms [theta])) in
    (* body *)
    pat' <- comp_ren_or_subst sort (SubstRen pat) taus;;
    let compRenSubstArgs n := List.concat [ List.map (const (abs_ref "x" eq_refl_)) pat;
                                          [ nApp sigma [n] ] ] in
    let innerBodyHelper n :=
        eq_trans_ (app_ref (compRenSubstName sort)
                           (List.concat [pat; sty_terms taus_up;
                                        map2 funcomp_ (sty_terms taus_up) pat;
                                        compRenSubstArgs n]))
                  (eq_trans_ (eq_sym_ (app_ref (compSubstRenName sort)
                                               (List.concat [sty_terms taus; pat; pat';
                                                            compRenSubstArgs n])))
                             (ap_ (app_ref (renName sort) pat) (nApp eq [n]))) in
    let innerBodyHelper2 n boundSort :=
        eq_trans_ (app_ref (compRenSubstName sort)
                           (List.concat [pat; sty_terms taus_up;
                                        map2 funcomp_ (sty_terms taus_up) pat;
                                        compRenSubstArgs n]))
                  (eq_trans_ (eq_sym_ (app_ref (compSubstRenName sort)
                                               (List.concat [sty_terms taus; pat;
                                                            List.map (const nHole) pat';
                                                            List.map (fun substSort =>
                                                                        abs_ref "x" (eq_sym_ (if eqb substSort boundSort
                                                                                              then scons_p_tail_ nHole nHole (nRef "x")
                                                                                              else eq_refl_))) substSorts;
                                                            [ nApp sigma [n] ]])))
                             (ap_ (app_ref (renName sort) pat)
                                  (nApp eq [n]))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun p boundSort =>
                                       eq_trans_ (scons_p_comp_ (var_zero_p_ (nRef p)
                                                                             >>> app_constr (varConstrName sort) sc ls_up [])
                                                                nHole nHole x)
                                                 (scons_p_congr_ (abs_ref "n" (innerBodyHelper2 (nRef "n") boundSort))
                                                                 (abs_ref "x" (scons_p_head_ nHole
                                                                                             (abs_ref "z" (app_ref (renName sort) (List.app pat [nHole])))
                                                                                             (nRef "x")))))
                                    (fun _ boundSort => innerBodyHelper2 x boundSort)
    in
    (* name *)
    let name := upSubstSubstName sort binder in
    process_lemma name (List.concat [bpms; bks; bls; bms; [bsigma]; btaus; [btheta; beq; bx]]) innerType innerBody.

  Definition genUpSubstSubsts (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstSubst bs)) bss.


  Definition genUpSubstSubstNoRen (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    substSorts <- substOf sort;;
    sc <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(k, bks) <- introScopeVarS "k";;
    '(ls, bls) <- introScopeVar "l" sort;;
    '(ms, bms) <- introScopeVar "m" sort;;
    let '(sigma, bsigma) := genSubstS "sigma" sc k ls sort in
    '(taus, btaus) <- genSubst "tau" sort ls ms;;
    let '(theta, btheta) := genSubstS "theta" sc k ms sort in
    '(x, bx) <- genUpVar "x" sort binder k;;
    let '(eq, beq) := genEqS "Eq" bx
                             (sigma >>> app_ref (substName sort) (sty_terms taus))
                             theta in
    ms_up <- upSubstScope sort [binder] ms;;
    ls_up <- upSubstScope sort [binder] ls;;
    taus_up <- upSubst sort [binder] taus;;
    pat <- patternSId sort binder;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upName sort binder) (List.app pms [sigma]))
                                 >>> (app_ref (substName sort) (sty_terms taus_up)))
                            (app_ref (upName sort binder) (List.app pms [theta])) in
    (* body *)
    patNoRen <- patternSIdNoRen sort binder;;
    pat' <- comp_ren_or_subst sort (SubstSubst pat) taus;;
    let compSubstSubstArgs n := List.concat [ List.map (const (abs_ref "x" eq_refl_)) pat;
                                            [ nApp sigma [n] ] ] in
    let innerBodyHelper n :=
        eq_trans_ (app_ref (compSubstSubstName sort) (List.concat [pat; sty_terms taus_up;
                                                                map2 funcomp_ (sty_terms taus_up) patNoRen;
                                                                compSubstSubstArgs n]))
                  (eq_trans_ (eq_sym_ (app_ref (compSubstSubstName sort)
                                               (List.concat [sty_terms taus; pat; pat';
                                                            compSubstSubstArgs n])))
                             (ap_ (app_ref (substName sort) pat) (nApp eq [n]))) in
    let innerBodyHelper2 p boundSort :=
        eq_trans_ (app_ref (compSubstSubstName sort)
                           (List.concat [pat; sty_terms taus_up;
                                        map2 funcomp_ (sty_terms taus_up) patNoRen;
                                        compSubstSubstArgs p]))
                  (eq_trans_ (eq_sym_ (app_ref (compSubstSubstName sort)
                                               (List.concat [sty_terms taus; pat;
                                                            List.map (const nHole) pat';
                                                            List.map (fun substSort =>
                                                                        abs_ref "x" (eq_sym_ (if eqb substSort boundSort
                                                                                              then scons_p_tail_ nHole nHole (nRef "x")
                                                                                              else eq_refl_))) substSorts;
                                                            [ nApp sigma [p] ]])))
                             (ap_ (app_ref (substName sort) pat) (nApp eq [p]))) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun p boundSort =>
                                       eq_trans_ (scons_p_comp_ (var_zero_p_ (nRef p) >>> app_constr (varConstrName sort) sc ls_up [])
                                                                nHole nHole x)
                                                 (scons_p_congr_ (abs_ref "n" (innerBodyHelper2 (nRef "n") boundSort))
                                                                 (abs_ref "x" (scons_p_head_ nHole
                                                                                             (abs_ref "z" (app_ref (substName sort) (List.app pat [nHole])))
                                                                                             (nRef "x")))))
                                    (fun _ boundSort => innerBodyHelper2 x boundSort)
    in
    (* name *)
    let name := upSubstSubstName sort binder in
    process_lemma name (List.concat [bpms; bks; bls; bms; [bsigma]; btaus; [btheta; beq; bx]]) innerType innerBody.

  Definition genUpSubstSubstsNoRen (bss: list (Binder * tId)) : t (list lemma) :=
    a_map (fun bs => translate_lemma (genUpSubstSubstNoRen bs)) bss.


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
              functorComp_.
    
  Definition genCompSubstSubsts := genFixpoint genCompSubstSubst.
End substSubst.
Import substSubst.

(* MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_ty) env29 >>= composeGeneration "env30"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubstSubsts upList_tm) env30 >>= composeGeneration "env31"). *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("ty", [])) env31 >>= composeGeneration "env32"). *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("tm", ["vl"])) env32 >>= composeGeneration "env33"). *)

(** * pi *)

(* Module m. *)
(*   Import GenM.Notations GenM. *)
  
(*   Definition testup : GenM.t substTy := *)
(*         let bs := (BinderList "p" "chan", "chan") in *)
(*         let '(binder, sort) := bs in *)
(*         '(ms, bms) <- introScopeVar "m" sort;; *)
(*         '(ls, bls) <- introScopeVar "l" sort;; *)
(*         '(taus, btaus) <- genSubst "tau" sort ls ms;; *)
(*         taus_up <- upSubst sort [binder] taus;; *)
(*         pure taus_up. *)
(* End m. *)

(* MetaCoq Run ( *)
(*       match GenM.runInfo m.testup env17 with *)
(*       | inl e => tmFail e *)
(*       | inr (_, _, x) => *)
(*         x <- tmEval all x;; *)
(*         tmPrint x *)
(*       end). *)
(* From ASUB Require Import core fintype. *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("chan", [])) env17 >>= composeGeneration "env32"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubstSubstsNoRen upList_chan) env32 >>= composeGeneration "env30"). *)
(* MetaCoq Run (mkLemmasTyped (genCompSubstSubsts ("proc", [])) env30 >>= composeGeneration "env33"). *)
(* MetaCoq Run (mkLemmasTyped (genUpSubstSubstsNoRen upList_proc) env33 >>= composeGeneration "env31"). *)

Module rinstInst.
  Import GenM.Notations GenM.
  
  Definition genUpRinstInst (bs: Binder * tId) : t nlemma :=
    let '(binder, sort) := bs in
    sc <- get_scope_type;;
    let '(pms, bpms) := binvparameters binder in
    '(m, bms) <- introScopeVarS "m";;
    '(ns, bns) <- introScopeVar "n" sort;;
    n_var <- toVarScope sort ns;;
    let '(xi, bxi) := genRenS "xi" sc m n_var in
    let '(sigma, bsigma) := genSubstS "sigma" sc m ns sort in
    '(x, bx) <- genUpVar "x" sort binder m;;
    let '(eq, beq) := genEqS "Eq" bx (xi >>> app_constr (varConstrName sort) sc ns []) sigma in
    ns' <- upSubstScope sort [binder] ns;;
    (* type *)
    let innerType := equiv_ x ((app_ref (upRenName sort binder) (List.app pms [xi]))
                                 >>> (app_constr (varConstrName sort) sc ns' []))
                            (app_ref (upName sort binder) (List.app pms [sigma])) in
    (* body *)
    shift <- patternSId sort binder;;
    let innerBodyHelper n := ap_ (app_ref (renName sort) shift) (nApp eq [n]) in
    matchFin <- matchFin_ bx innerType x innerBodyHelper eq_refl_;;
    let innerBody := definitionBody sort binder
                                    matchFin (innerBodyHelper x)
                                    (fun _ _ =>
                                       eq_trans_ (scons_p_comp_ nHole nHole
                                                                (app_constr (varConstrName sort) sc ns' [])
                                                                x)
                                                 (scons_p_congr_ (abs_ref "n" (innerBodyHelper (nRef "n")))
                                                                 (abs_ref "z" eq_refl_)))
                                    (fun _ _ => innerBodyHelper x)
    in
    (* name *)
    let name := upRinstInstName sort binder in
    process_lemma name (List.concat [bpms; bms; bns; [bxi; bsigma; beq; bx]]) innerType innerBody.
    
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
              functorExt_.
    
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

(* MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_ty) env33 >>= composeGeneration "env34"). *)
(* MetaCoq Run (mkLemmasTyped (genUpRinstInsts upList_tm) env34 >>= composeGeneration "env35"). *)
(* MetaCoq Run (mkLemmasTyped (genRinstInsts ("ty", [])) env35 >>= composeGeneration "env36"). *)
(* MetaCoq Run (mkLemmasTyped (genRinstInsts ("tm", ["vl"])) env36 >>= composeGeneration "env37"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["ty"]) env37 >>= composeGeneration "env38"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaRinstInsts ["tm"; "vl"]) env38 >>= composeGeneration "env39"). *)

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

(* MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["ty"]) env39 >>= composeGeneration "env40"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaInstIds ["tm"; "vl"]) env40 >>= composeGeneration "env41"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["ty"]) env41 >>= composeGeneration "env42"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaRinstIds ["tm"; "vl"]) env42 >>= composeGeneration "env43"). *)


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

(* MetaCoq Run (mkLemmasTyped (genVarLs ["ty"]) env43 >>= composeGeneration "env44"). *)
(* MetaCoq Run (mkLemmasTyped (genVarLs ["tm"; "vl"]) env44 >>= composeGeneration "env45"). *)
(* MetaCoq Run (mkLemmasTyped (genVarLRens ["ty"]) env45 >>= composeGeneration "env46"). *)
(* MetaCoq Run (mkLemmasTyped (genVarLRens ["tm"; "vl"]) env46 >>= composeGeneration "env47"). *)


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

(* MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["ty"]) env47 >>= composeGeneration "env48"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompRenRens ["tm"; "vl"]) env48 >>= composeGeneration "env49"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["ty"]) env49 >>= composeGeneration "env50"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompRenSubsts ["tm"; "vl"]) env50 >>= composeGeneration "env51"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["ty"]) env51 >>= composeGeneration "env52"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompSubstRens ["tm"; "vl"]) env52 >>= composeGeneration "env53"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["ty"]) env53 >>= composeGeneration "env54"). *)
(* MetaCoq Run (mkLemmasTyped (genLemmaCompSubstSubsts ["tm"; "vl"]) env54 >>= composeGeneration "env55"). *)

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

(** * Inductive Types *)
Definition generateInductives (component: NEList.t tId) (info: genInfo) : TemplateMonad genInfo :=
  (** TODO the component already only includes definable sorts *)
  info <- mkInductive (genMutualInductive component) info;;
  tmPrint "Defined Inductive Types";;
  tmReturn info. 
          
Definition generateLemmas (component: NEList.t tId) (upList: list (Binder * tId)) (info: genInfo) : TemplateMonad genInfo :=
  let componentL := NEList.to_list component in
  (** * Congruence Lemmas *)
  (* if we generate multiple lemmas we need to keep updating the infoironment in a fold *)
  info <- monad_fold_left (fun info sort => mkLemmasTyped (genCongruences sort) info) componentL info;;
  tmPrint "Defined Congruence Lemmas";;
  hasSubsts <- tm_liftGenM (GenM.hasSubsts (NEList.hd component)) info;;
  if negb hasSubsts 
  then tmReturn info
  else 
    let isRen := SSet.mem info.(in_sig).(sigRenamings) (NEList.hd component) in
    if isRen
    then
      tmPrint "Has Renamings";;
      (** * Renamings *)
      info <- mkLemmasTyped (genUpRens upList) info;;
      info <- mkLemmasTyped (genRenamings component) info;;
      (** * Substitutions *)
      info <- mkLemmasTyped (genUpSubsts upList) info;;
      info <- mkLemmasTyped (genSubstitutions component) info;;
      (** * idSubst *)
      info <- mkLemmasTyped (genUpIds upList) info;;
      info <- mkLemmasTyped (genIdLemmas component) info;;
      (** * Extensionality *)
      info <- mkLemmasTyped (genUpExtRens upList) info;;
      info <- mkLemmasTyped (genExtRens component) info;;
      info <- mkLemmasTyped (genUpExts upList) info;;
      info <- mkLemmasTyped (genExts component) info;;
      (** * Combinations *)
      info <- mkLemmasTyped (genUpRenRens upList) info;;
      info <- mkLemmasTyped (genCompRenRens component) info;;
      info <- mkLemmasTyped (genUpRenSubsts upList) info;;
      info <- mkLemmasTyped (genCompRenSubsts component) info;;
      info <- mkLemmasTyped (genUpSubstRens upList) info;;
      info <- mkLemmasTyped (genCompSubstRens component) info;;
      info <- mkLemmasTyped (genUpSubstSubsts upList) info;;
      info <- mkLemmasTyped (genCompSubstSubsts component) info;;
      (** * rinstInst *)
      info <- mkLemmasTyped (genUpRinstInsts upList) info;;
      info <- mkLemmasTyped (genRinstInsts component) info;;
      info <- mkLemmasTyped (genLemmaRinstInsts componentL) info;;
      (** * rinstId/instId *)
      info <- mkLemmasTyped (genLemmaInstIds componentL) info;;
      info <- mkLemmasTyped (genLemmaRinstIds componentL) info;;
      (** * varL *)
      info <- mkLemmasTyped (genVarLs componentL) info;;
      info <- mkLemmasTyped (genVarLRens componentL) info;;
      (** * Combinations *)
      info <- mkLemmasTyped (genLemmaCompRenRens componentL) info;;
      info <- mkLemmasTyped (genLemmaCompRenSubsts componentL) info;;
      info <- mkLemmasTyped (genLemmaCompSubstRens componentL) info;;
      info <- mkLemmasTyped (genLemmaCompSubstSubsts componentL) info;;
      tmReturn info
    else
      tmPrint "Has No Renamings";;
      (** * Substitutions *)
      info <- mkLemmasTyped (genSubstitutions component) info;;
      info <- mkLemmasTyped (genUpSubsts upList) info;;
      (** * idSubst *)
      info <- mkLemmasTyped (genUpIds upList) info;;
      info <- mkLemmasTyped (genIdLemmas component) info;;
      (** * Extensionality *)
      info <- mkLemmasTyped (genUpExts upList) info;;
      info <- mkLemmasTyped (genExts component) info;;
      (** * Combinations *)
      info <- mkLemmasTyped (genCompSubstSubsts component) info;;
      info <- mkLemmasTyped (genUpSubstSubstsNoRen upList) info;;
      (** * instId *)
      info <- mkLemmasTyped (genLemmaInstIds componentL) info;;
      (** * varL *)
      info <- mkLemmasTyped (genVarLs componentL) info;;
      (** * Combinations *)
      info <- mkLemmasTyped (genLemmaCompSubstSubsts componentL) info;;
      tmReturn info.
               

From ASUB Require unscoped core.
Require Setoid Morphisms.

Module generation_pi.
  (* Time MetaCoq Run (generate ("chan",[]) upList_chan {| in_env := initial_env; in_implicits := SFMap.empty; in_flags := {| fl_scope_type := Wellscoped |}; in_sig := pi_sig |} *)
  (*                            >>= tmEval TemplateMonad.Common.all *)
  (*                            >>= generate ("proc", []) upList_proc *)
  (*                            >>= tmEval TemplateMonad.Common.all *)
  (*                            >>= tmDefinition "env1"). *)
End generation_pi.

(* Module generation. *)

(*   Import GenUpsExample_fcbv. *)

(*   Import Setoid Morphisms. *)
(*   (* Compute (GenM.run (genUpRens upList_ty) Hsig_example.mySig empty_state). *) *)
(*   Time MetaCoq Run (generate ("ty",[]) upList_ty {| in_env := initial_env; in_implicits := SFMap.empty; in_flags := default_flags; in_sig := Hsig_example.mySig |} *)
(*                              >>= tmEval TemplateMonad.Common.all *)
(*                              >>= generate ("tm", ["vl"]) upList_tm *)
(*                              >>= tmEval TemplateMonad.Common.all *)
(*                              >>= tmDefinition "env1"). *)
(*   (* SFMap.t : 7 *) *)

(*   Import unscoped core UnscopedNotations. *)
(*   Instance subst_ty_morphism : *)
(*     (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) *)
(*             (@subst_ty)). *)
(*   Proof. *)
(*     exact (fun f_ty g_ty Eq_ty s t Eq_st => *)
(*              eq_ind s (fun t' => subst_ty f_ty s = subst_ty g_ty t') *)
(*                     (ext_ty f_ty g_ty Eq_ty s) t Eq_st). *)
(*   Qed. *)

(*   Instance ren_ty_morphism : *)
(*     (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty)). *)
(*   Proof. *)
(*     exact (fun f_ty g_ty Eq_ty s t Eq_st => *)
(*              eq_ind s (fun t' => ren_ty f_ty s = ren_ty g_ty t') *)
(*                     (extRen_ty f_ty g_ty Eq_ty s) t Eq_st). *)
(*   Qed. *)


(*   (* DONE prove the default lemma. If this works we're on the right track *) *)
(*   Goal forall (f: nat -> ty) (s t: ty), *)
(*       subst_ty f (subst_ty (scons t var_ty) s) = subst_ty (scons (subst_ty f t) var_ty) (subst_ty (up_ty_ty f) s). *)
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
(*   Qed. *)
(* End generation. *)


(* Module generation. *)
  
(*   Import GenUpsExample_fcbv. *)
(*   Import core fintype. *)
(*   Import Setoid Morphisms. *)
(*   Compute upList_ty. *)
(*   Compute upList_tm. *)
(*   (* Compute (GenM.run (genUpRens upList_ty) Hsig_example.mySig empty_state). *) *)
(*   MetaCoq Run (generateInductives ("ty", []) fcbv_info *)
(*                                  >>= composeGeneration "env0"). *)
(*   MetaCoq Run (generateInductives ("tm", ["vl"]) env0 *)
(*                                  >>= composeGeneration "env1"). *)
(*   MetaCoq Run (generateLemmas ("ty",[]) upList_ty env1  *)
(*                               >>= composeGeneration "env2"). *)
(*   (* TODO takes way too long with over 2 minutes! *) *)
(*   MetaCoq Run (generateLemmas ("tm", ["vl"]) upList_tm env2 *)
(*                               >>= composeGeneration "env3"). *)
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
(*     unfold up_ty_ty. *)
(*     (* TODO apparently fsimpl got weaker. Also I need to generate the lemmas with pointwise *) *)
(*     fsimpl. *)
(*     setoid_rewrite varL_ty. *)
(*     (* setoid_rewrite renSubst_ty. *) *)
(*     (* setoid_rewrite instId_ty. *) *)
(*     (* fsimpl. minimize. *) *)
(*     (* reflexivity. *) *)
(*   Admitted. *)
(* End generation. *)
