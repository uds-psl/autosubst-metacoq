(** * Module to parse HOAS by quoting inductive types with MetaCoq *)
From MetaCoq.Template Require Import All.
Require Import String List Arith.
Import ListNotations MonadNotation.
Open Scope string.
From ASUB Require Import hsig monad AL sigAnalyzer.

Module m3.
  Parameter V W : Type.
  
  Inductive ty :=
  | arr : ty -> ty -> ty
  | all : (V -> ty) -> ty.

  Inductive tm :=
  | app : tm -> tm -> tm 
  | tapp : tm -> ty -> tm 
  | vt : vl -> tm 
  with vl :=
  | lam : ty -> (W -> tm) -> vl
  | tlam : (V -> tm) -> vl.

  Definition Autosubst_map := [(V, ty); (W, vl)].
  Definition Autosubst_sorts := [ty; tm].
End m3.

(* chain several actions in the templatemonad *)
Fixpoint chain (actions: list (TemplateMonad unit)) : TemplateMonad unit :=
  match actions with
  | [] => tmReturn tt
  | a :: actions =>
    a;;
    chain actions
  end.

(* standard sequencing to swap order of list and monad *)
Fixpoint sequence {A:Type} (ms: list (TemplateMonad A)) : TemplateMonad (list A) :=
  match ms with
  | [] => tmReturn []
  | m :: ms =>
    a <- m;;
    as_ <- sequence ms;;
    tmReturn (a :: as_)
  end.

(* map a function with monadic return type over a list *)
Definition tm_a_map {A B: Type} (f: A -> TemplateMonad B) (ms: list A) : TemplateMonad (list B) :=
  sequence (map f ms).

(* Return just the quoted terms for a list of types *)
Definition get_quoted_terms (slist: list Type) : TemplateMonad (list term) :=
  inductives <- tm_a_map tmQuote slist;;
  tmReturn inductives.

MetaCoq Run (get_quoted_terms m3.Autosubst_sorts >>= tmPrint).

(* Return the kernel names for the tInds *)
Definition get_inductive_kernames (slist: list Type) : TemplateMonad (list kername) :=
  qterms <- get_quoted_terms slist;;
  kernames <- tm_a_map (fun t: term =>
                        match t return TemplateMonad kername with
                        | tInd {| inductive_mind := inductive_mind; inductive_ind := _ |} _ => tmReturn inductive_mind
                        | _ => tmFail "not an inductive in get_inductive_kernames"
                        end) qterms;;
  tmReturn kernames.

(* Return the list of mutual_inductive_body for a list of inductive types. *)
Definition get_inductive_mbodies (slist: list Type) : TemplateMonad (list mutual_inductive_body) :=
  kernames <- get_inductive_kernames slist;;
  mutual_bodies <- tm_a_map tmQuoteInductive kernames;;
  tmReturn mutual_bodies.

MetaCoq Run (get_inductive_mbodies m3.Autosubst_sorts >>= tmPrint).

(* Quotes a list of pairs of types for the variable map so that they can be used during translation. *)
Definition get_variable_map (vlist: list (Type * Type)) : TemplateMonad (list (string * inductive)) :=
  (* a.d. TODO, can we use split_combine here to map over the vars and sorts separately? *)
  qvlist <- tm_a_map (fun '(v, s) =>
                    qvar <- tmQuote v;;
                    qsort <- tmQuote s;;
                    match qvar, qsort with
                    | tConst (_, name) _, tInd ind _ => tmReturn (name, ind)
                    | tConst _ _, _ => tmFail "not an inductive in get_variable_map"
                    | _, _ => tmFail "not a const in get_variable_map"
                    end)
                    vlist;;
  tmReturn qvlist.

Import E.

Module translation.

Import E.Notations.
  
(* the following functions should be in the RWSE Monad instead of the TemplateMonad *)

(* Lift our maps when we traverse a binder. Since MetaCoq uses deBruijn indices in inductive type definitions. *)
Definition scons {A:Type} (a:A) (A_map: nat -> A) (n: nat) : A :=
  match n with
  | 0 => a
  | S n => A_map n
  end.

(* in the translations functions we have three mappings from coq terms to our internal datatypes
 * sort is just a string we use to identify syntactic sorts.
 * 
 * name_map: maps deBruijn indices of the current mutual inductive type definition to their sort
 * 
 * var_map: maps names of module variables used for weak HOAS to the sort they are supposed to represent.
 * 
 * ind_map: maps a string and an index for a previously defined inductive type to a sort.
 *** The string is the first inductive type of the mutual inductive type definition
 *** The index is the number of the inductive type definition in the mutual inductive type definition
 *** These arguments are chosen because a MetaCoq `inductive` also identifies an inductive type by them and we often work with objects of type `inductive`.
 *)

(* translate a type expression to a Binder instance.
 * The type expression should only contain
 * - tConst for negative occurences of inductive types
 * - tApp for variadic binders
 *
 * e.g. all: ([V] -> tRel n) -> tRel m
 *)
Definition translate_binder (var_map: string -> E.t tId) (t: term) : E.t Binder :=
  match t with
  | tConst (_, var_name) _ => fmap Single (var_map var_name)
  (* TODO app with variadic should result in BinderList *)
  | _ => error "inexhaustive pattern match in translate binder"
  end.

(* translate a type to a Position instance.
 * The type should only contain
 * - tRel for references to one of the current mutual inductive types
 * - tInd for references to previously defined inductive types
 * - tProd for binders
 *
 * e.g. all: [(V -> tRel n)] -> tRel m
 *)
Fixpoint translate_position (name_map: nat -> E.t tId) (var_map: string -> E.t tId) (ind_map: (string * nat) -> E.t tId) (t: term) : E.t Position :=
  match t with
  | tRel n =>
    sort <- name_map n;;
    pure {| pos_binders := []; pos_head := Atom sort |}
  | tInd {| inductive_mind := (_, tname); inductive_ind := n |} _ =>
    sort <- ind_map (tname, n);;
    pure {| pos_binders := []; pos_head := Atom sort |}
  | tProd {| binder_name := nAnon; binder_relevance := _ |} t1 t2 =>
    binder <- translate_binder var_map t1;;
    (* for the right part of the product we update the name map because we have traversed the binder *)
    let name_map := scons (error "should not appear") name_map in
    (* TODO add patterns to monad notations *)
    result2 <- translate_position name_map var_map ind_map t2;;
    let '{| pos_binders := binders; pos_head := head |} := result2 in
    pure {| pos_binders := binder :: binders; pos_head := head |}
  | _ => error "inexhaustive pattern match in translate_position"
  end.

(* translate a type to a list of Position instances.
 * The type should only contain products or deBruijn indices
 *
 * every left child of a product is dispatched to translate_position
 * this function only takes care of the rightward spine
 *
 * e.g. all: [(V -> tRel n) -> tRel m]
 *)
Fixpoint translate_positions (name_map: nat -> E.t tId) (var_map: string -> E.t tId) (ind_map: (string * nat) -> E.t tId) (t: term) : E.t (list Position) :=
  match t with
  (* base case content of tRel can be ignored since all constructors must end with a reference to their inductive type *)
  | tRel _ => pure []
  | tProd {| binder_name := nAnon; binder_relevance := _ |} t1 t2 =>
    pos <- translate_position name_map var_map ind_map t1;;
    (* for the right part of the product we update the name map *)
    let name_map := scons (error "should not appear") name_map in
    result2 <- translate_positions name_map var_map ind_map t2;;
    pure (pos :: result2)
  (* should really use error monad here *)
  | _ => error "inexhaustive pattern match in translate_positions"
  end.

(* translate the MetaCoq representation of a constructor to an instance of Constructor
 * e.g. ("app", tm -> tm -> tm)
 *)
Definition translate_constructor (name_map: nat -> E.t tId) (var_map: string -> E.t tId) (ind_map: (string * nat) -> E.t tId) (ctor: (string * term) * nat) : E.t Constructor :=
  let '((cname, ctype), _) := ctor in
  positions <- translate_positions name_map var_map ind_map ctype;;
  pure {| con_parameters := []; con_name := cname; con_positions := positions |}.

(* translate a single inductive type definition into a list of constructors paired with the name of the inductive. *)
Definition translate_inductive_body (name_map: nat -> E.t tId) (var_map: string -> E.t tId) (ind_map: (string * nat) -> E.t tId) (b: one_inductive_body) : E.t (tId * list Constructor) :=
  ctors <- amap (translate_constructor name_map var_map ind_map) (ind_ctors b);;
  pure (ind_name b, ctors).

(* build a name_map by using a list of inductive definitions to map deBruijn indices to the name of the inductive. Modified by scons. *)
Fixpoint mk_name_map (bodies: list one_inductive_body) : nat -> E.t tId :=
  fun n => 
  match bodies with
  | [] => error "deBruijn index out of bounds in mk_name_map"
  | b :: bodies =>
    match n with
    | O => pure (ind_name b)
    | S n => mk_name_map bodies n
    end
  end.

(* translate a mutual inductive type definition into a list of its sorts together with their lists of their constructors *)
Definition translate_mutual_inductive_body (var_map: string -> E.t tId) (ind_map: (string * nat) -> E.t tId) (mbody: mutual_inductive_body) : E.t (list (tId * list Constructor)) :=
  (* a.d. DONE do deBruijn indices count from the front or back? From the back, so we need to reverse the list. *)
  let name_map := mk_name_map (rev (ind_bodies mbody)) in
  amap (translate_inductive_body name_map var_map ind_map) (ind_bodies mbody).

(* build a var_map by using an association list of (variable_name, sort_name) to map variable names to their associated sort name. *)
Definition mk_var_map (mvar_sorts: E.t (list (string * string))) : string -> E.t tId :=
  fun key =>
  var_sorts <- mvar_sorts;;
  match find (fun '(var, _) => eqb key var) var_sorts with
  | None => error (String.concat " " ["unknown variable in mk_var_map"; key])
  | Some (_, sort) => pure sort
  end.

(* A basic ind_map which just errors out.
 * We use another function to iteratively update the ind_map because each update adds one mutual inductive type definition. *)
Definition mk_ind_map : (string * nat) -> E.t tId := fun '(ind_name, n) => error (String.concat " " ["unknown inductive in mk_ind_map"; ind_name; string_of_nat n]).

(* Update the ind map using one mutual inductive type definition.
 * A correct key consists of a name that matches the name of the first inductive type definition, and an index which does not exceed the number of inductive type definitions.
 * If the name does not match we delegate to the next ind_map.
 * The definition uses some of the power of dependent types to prove that if the index is in bounds we can retrieve a but unfortunately this is still unhandy. *)
Definition update_ind_map (inds: list one_inductive_body) (ind_map: (string * nat) -> E.t tId): (string * nat) -> E.t tId.
  refine (fun key =>
          let (key_name, n) := key in
          match inds with
          | [] => error "False: Inductive definitions always have at least one body."
          | head_ind :: _ =>
            (* if we are looking for an inductive in the current block *)
            if eqb (ind_name head_ind) key_name
            then _
            else ind_map key (* ask the next mapping *)
         end).
  refine (match lt_dec n (length inds) with
          | right _ => error (String.concat " " ["False: queried ind_map with index out of bounds for mutual inductive type"; key_name; (string_of_nat n)])
          | left H => _
          end).
  (* a.d. TODO, when I used this code instead of the rest below the MetaCoq Run at the end crashed *)
  (* specialize (nth_error_Some' inds n) as [_ H']. *)
  (* destruct (H' H) as [ind _]. *)
  (* exact (ret (ind_name ind)). *)
  refine (match nth_error inds n as p return (nth_error inds n = p -> E.t cId) with
          | None => fun H' => _
          | Some ind => fun H' => pure (ind_name ind)
          end eq_refl).
  - exfalso. destruct (nth_error_Some inds n) as [_ H_is_not_None].
    apply H_is_not_None; [ exact H | exact H' ].
Defined.

(* build a var_map by using an ind_map to translate the inductive's to their sort name.
 * e.g. ("V", (... "tm", 1)) ~~> ("V", "vl")
 *)
Definition quote_var_map (qvlist: list (string * inductive)) (ind_map: (string * nat) -> E.t tId): E.t (list (string * tId)) :=
  amap (fun '(var, ind) =>
        let '{| inductive_mind := (_, ind_name); inductive_ind := n |} := ind in
        sort <- ind_map (ind_name, n);;
        pure (var, sort))
       qvlist.

(* entry point for the translation which is used by the wrapper in the TemplateMonad *)
Definition translate_inductives (mbodies: list mutual_inductive_body) (qvlist: list (string * inductive)) : E.t (list (list tId) * list tId * Spec) :=
  (* the canonical_order is simply the order in which the inductive datatypes are defined in the program. *)
  let components := map (fun mbody => map ind_name (ind_bodies mbody)) mbodies in
  let canonical_order := concat components in
  (* build the ind_map out of all the mutual inductive definitions *)
  let ind_map :=
      fold_left (fun ind_map mbody => update_ind_map (ind_bodies mbody) ind_map)
                mbodies mk_ind_map in
  let var_map := mk_var_map (quote_var_map qvlist ind_map) in
  (* fold over the mutual inductive definitions and translate all contained inductive definitions at once, then collect all inductive definitions of all mutual inductive definitions in a single list *)
  translation <-
      m_fold_left (fun proto_spec mbody =>
                     bind (translate_mutual_inductive_body var_map ind_map mbody)
                            (fun l => pure (app proto_spec l)))
                    [] mbodies;;
  pure (components, canonical_order, SFMap.fromList translation).
End translation.

(* a.d. TODO, RSWE and TemplateMonad don't play nicely together right now so I put all the RWSE functions into module to import them again *)
Import translation.

(* main function that translates some given inductive types and a mapping of variables to their associated inductive types to a Spec, our internal datatype, to represent a language.
 * This function only quotes its arguments and then delegates to the "pure" translate_inductives function *)
Definition tmTranslateInductives (slist: list Type) (vlist: list (Type * Type)) : TemplateMonad (list (list tId) * list tId * Spec) :=
  mbodies <- get_inductive_mbodies slist;;
  qvlist <- get_variable_map vlist;;
  let mtranslation := translate_inductives mbodies qvlist in
  (* run the translation *)
  match run mtranslation tt tt with
  | inl e => tmFail e
  | inr (_, _, (components, canonical_order, spec)) =>
    spec <- tmEval all spec;;
    canonical_order <- tmEval all canonical_order;;
    components <- tmEval all components;;
    tmReturn (components, canonical_order, spec)
  end.

MetaCoq Run (tmTranslateInductives m3.Autosubst_sorts m3.Autosubst_map >>= tmPrint).

From ASUB Require Import sigAnalyzer.

Definition tmInternalizeInductives (slist: list Type) (vlist: list (Type * Type)) : TemplateMonad Signature :=
  '(components, canonical_order, spec) <- tmTranslateInductives slist vlist;;
  (* canonical_order <- tmEval all canonical_order;; *)
  (* spec <- tmEval all spec;; *)
  let x := run (build_signature (Some components) canonical_order spec) tt tt in
  x <- tmEval all x;;
  match x with
  | inl e => tmFail e
  | inr (_, _, sig) =>
    tmReturn sig
  end.

MetaCoq Run (tmInternalizeInductives m3.Autosubst_sorts m3.Autosubst_map >>= tmPrint).


Definition HOASArrow (A:Type) (B: Type) := (A * B)%type.

Notation "A ~> B" := (HOASArrow A B) (at level 80, right associativity).

Inductive tm :=
  | app : tm -> tm -> tm
  | lam : (tm ~> tm) -> tm.

Definition foo :=
  fun a b:nat => a = b.

MetaCoq Quote Definition foo_source :=  Eval cbv in foo.

MetaCoq Run (get_inductive_mbodies [tm] >>= tmPrint).

(*   [{|
        ind_name := "tm";
        ind_type :=
          tSort
            (Universe.from_kernel_repr (Level.lSet, false)
               [(Level.Level "ASUB.src.phoas.533", false);
               (Level.Level "ASUB.src.phoas.534", false)]);
        ind_kelim := IntoAny;
        ind_ctors :=
          [("app",
           tProd
             {| binder_name := nAnon; binder_relevance := Relevant |}
             (tRel 0)
             (tProd
                {| binder_name := nAnon; binder_relevance := Relevant |}
                (tRel 1) (tRel 2)), 2);
          ("lam",
          tProd {| binder_name := nAnon; binder_relevance := Relevant |}
            (tApp
               (tConst (MPfile ["phoas"; "src"; "ASUB"], "HOASArrow") [])
               [tRel 0; tRel 0]) (tRel 1), 1)];
        ind_projs := [];
        ind_relevance := Relevant
      |}];
*)
