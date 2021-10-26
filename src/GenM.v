Require Import String List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
From ASUB Require Import Monad Language AssocList Utils Quotes Flags.

Record State := { st_names : list string; st_implicits : SFMap.t (list bool) }.

Definition empty_state := {| st_names := []; st_implicits := SFMap.empty |}.
Definition initial_state (implicits: SFMap.t (list bool)) := {| st_names := []; st_implicits := implicits |}.

(** * Put constants for wellscoped syntax in the initial environment. *)
Definition initial_env := SFMap.fromList [("nat", nat_q); ("option", option_q); ("S", S_q)].
Definition update_env (env env' : SFMap.t term) : SFMap.t term :=
  SFMap.union env env'.


(** * Record of information that is carried by the TemplateMonad in between evaluations of the GenM monad. Used to fill R' and State. *)
Record genInfo := { in_env : SFMap.t term;
                    in_implicits : SFMap.t (list bool);
                    in_flags : Flags;
                    in_sig : Signature;
                    in_modpath : modpath }.


Record R' := { R_flags : Flags; R_sig: Signature; R_env : SFMap.t term; R_modpath : modpath }.

(* The RWSEM monad that we use to generate the lemmas *)
Module GenMArgs.
  (* module parameters cannot be records yet. So define outside and put definition here *)
  Definition R := R'.
  Definition W := string.
  Definition S := State.
  Definition E := string.

  Definition append := String.append.
  Definition empty := ""%string.
End GenMArgs.

Module GenM.
  Module GenM := RWSEM GenMArgs.
  Include GenM.

  Import Notations.

  Definition runInfo {A: Type} (m: t A) (info: genInfo) :=
    run m {| R_flags := info.(in_flags);
             R_sig := info.(in_sig);
             R_env := info.(in_env);
             R_modpath := info.(in_modpath) |}
        (initial_state info.(in_implicits)).

  Definition register_name (name: string) : t unit :=
    state <- get;;
    put {| st_names := name :: state.(st_names); st_implicits := state.(st_implicits) |}.

  Definition register_names (names': list string) : t unit :=
    state <- get;;
    put {| st_names := app names' state.(st_names); st_implicits := state.(st_implicits) |}.

  Definition register_implicits (name: string) (implicits: list bool) : t unit :=
    state <- get;;
    put {| st_names := state.(st_names); st_implicits := SFMap.add state.(st_implicits) name implicits |}.

  Definition get_implicits (name: string) : t (list bool) :=
    state <- get;;
    match SFMap.find state.(st_implicits) name with
    | None => pure []
    | Some l => pure l
    end.
  
  (* Definition env_get (s: string) : t term := *)
  (*   env <- gets st_env;; *)
  (*   match SFMap.find env s with *)
  (*   | None => error (String.append "Not found: " s) *)
  (*   | Some t => pure t *)
  (*   end. *)

  (** * Additional functions used during code generation *)

  (** get the constructors of a sort *)
  Definition constructors (sort: tId) : t (list Constructor) :=
    spec <- asks (fun x => sigSpec x.(R_sig));;
    match SFMap.find spec sort with
    | Some cs => pure cs
    | None => error (String.append "constructors called with unknown sort: " sort)
    end.

  (** get the arguments of a sort *)
  Definition getArguments (sort: tId) : t (list tId) :=
    args <- asks (fun x => sigArguments x.(R_sig));;
    match SFMap.find args sort with
    | Some sorts => pure sorts
    | None => error (String.append "getArguments called with unknown sort: " sort)
    end.

  (** check if a sort has renamings *)
  Definition hasRenaming (sort: tId) : t bool :=
    rens <- asks (fun x => sigRenamings x.(R_sig));;
    pure (SSet.mem rens sort).

  (** return the substitution vector for a sort *)
  Definition substOf (sort: tId) : t (list tId) :=
    substs <- asks (fun x => sigSubstOf x.(R_sig));;
    match SFMap.find substs sort with
    | Some sorts => pure sorts
    | None => error (String.append "substOf called with unknown sort: " sort)
    end.

  (** check if a sort has a substitution vector *)
  Definition hasSubsts (sort: tId) : t bool :=
    substSorts <- substOf sort;;
    pure (negb (list_empty substSorts)).

  (** check if a sort is open (has a variable constructor) *)
  Definition isOpen (sort: tId) : t bool :=
    isOpen <- asks (fun x => sigIsOpen x.(R_sig));;
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

  Definition get_scope_type : t scope_type :=
    fl <- asks R_flags;;
    pure fl.(fl_scope_type).

  Definition allSorts : t (list tId) :=
    components <- asks (fun x => x.(R_sig).(sigComponents));;
    let sorts := List.concat (List.map NEList.to_list components) in
    pure sorts.

End GenM.
