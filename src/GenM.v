Require Import String List.
Import ListNotations.
Open Scope string.

From MetaCoq.Template Require Import All.
Import MonadNotation.
From ASUB Require Import Monad Language AssocList Utils TemplateMonadUtils Quotes.

Record State := { st_names : list string }.

Definition empty_state := {| st_names := [] |}.
(* Definition initial_env := SFMap.fromList [("nat", nat_q); ("eq", eq_q); ("f_equal", f_equal_q); ("eq_refl", eq_refl_q); ("eq_trans", eq_trans_q); ("up_ren", up_ren_q); ("funcomp", funcomp_q); ("var_zero", var_zero_q); ("scons", scons_q); ("id", id_q); ("shift", shift_q); ("ap", ap_q); ("up_ren_ren", up_ren_ren_q)]. *)
Definition initial_env := SFMap.fromList [("nat", nat_q)].

Definition update_env (env env' : SFMap.t term) : SFMap.t term :=
  SFMap.union env env'.

Definition tm_update_env '{| st_names := names; |} (env: SFMap.t term) : TemplateMonad (SFMap.t term) :=
  env_list' <- tm_mapM locate_name names;;
  let env' := SFMap.fromList env_list' in
  tmReturn (update_env env' env). 
  

(* The RWSE monad that we use to generate the lemmas *)
Module GenMArgs.
  Definition R := (Signature * (SFMap.t term))%type.
  Definition W := string.
  Definition S := State.
  Definition E := string.

  Definition append := String.append.
  Definition empty := ""%string.
End GenMArgs.

Module GenM.
  Module GenM := RWSE GenMArgs.
  Include GenM.

  Import Notations.

  Definition register_name (name: string) : t unit :=
    '{| st_names := names |} <- get;;
    put {| st_names := name :: names |}.

  Definition register_names (names': list string) : t unit :=
    '{| st_names := names |} <- get;;
    put {| st_names := app names' names |}.

  (* Definition env_get (s: string) : t term := *)
  (*   env <- gets st_env;; *)
  (*   match SFMap.find env s with *)
  (*   | None => error (String.append "Not found: " s) *)
  (*   | Some t => pure t *)
  (*   end. *)

  Definition testrun {A} (mv: t A) :=
    run mv (Hsig_example.mySig, initial_env) empty_state.

  (** * Additional functions used during code generation *)

  (** get the constructors of a sort *)
  Definition constructors (sort: tId) : t (list Constructor) :=
    spec <- asks (fun x => sigSpec (fst x));;
    match SFMap.find spec sort with
    | Some cs => pure cs
    | None => error ("constructors called with unknown sort")
    end.

  (** get the arguments of a sort *)
  Definition getArguments (sort: tId) : t (list tId) :=
    args <- asks (fun x => sigArguments (fst x));;
    match SFMap.find args sort with
    | Some sorts => pure sorts
    | None => error ("getArguments called with unknown sort")
    end.

  (** check if a sort has renamings *)
  Definition hasRenaming (sort: tId) : t bool :=
    rens <- asks (fun x => sigRenamings (fst x));;
    pure (SSet.mem rens sort).

  (** return the substitution vector for a sort *)
  Definition substOf (sort: tId) : t (list tId) :=
    substs <- asks (fun x => sigSubstOf (fst x));;
    match SFMap.find substs sort with
    | Some sorts => pure sorts
    | None => error ("substOf called with unknown sort")
    end.

  (** check if a sort is open (has a variable constructor) *)
  Definition isOpen (sort: tId) : t bool :=
    isOpen <- asks (fun x => sigIsOpen (fst x));;
    pure (SSet.mem isOpen sort).

  (** A sort is definable if it has any constructor *)
  Definition isDefinable (sort: tId) : t bool :=
    b <- isOpen sort;;
    ctors <- constructors sort;;
    pure (orb b (negb (list_empty ctors))).

  (** Check if the arguments of the first sort of a component and the component itself overlaps
   ** We can only check the first element of the component because they all have the same
   ** substitution vector. *)
  Definition isRecursive (component: NEList.t tId) : t bool :=
    let '(sort, _) := component in
    args <- getArguments sort;;
    pure (negb (list_empty (list_intersection (NEList.to_list component) args))).
  
End GenM.
