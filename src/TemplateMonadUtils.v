Require Import List String.
Import ListNotations.

From MetaCoq.Template Require Import All Pretty.
From ASUB Require Import AssocList GenM.
Import MonadNotation.

(** * Shorthand for the TemplateMonad with fixed universe argument *)
Definition TemplateMonadSet := TemplateMonad@{_ Set}.
  
Module TemplateMonadNotations.
  Declare Scope tm_scope.

  (* TODO if I declare it with tmBind the tm_update_env function fails to typecheck *)
  Notation "x <- c1 ;; c2" := (tmBind c1 (fun x => c2))
                                (at level 100, c1 at next level, right associativity) : tm_scope.

  Notation "' pat <- c1 ;; c2" := (tmBind c1 (fun x => match x with pat => c2 end))
                                    (at level 100, pat pattern, c1 at next level, right associativity) : tm_scope.
  
  Notation "c1 ;; c2" := (tmBind c1 (fun _ => c2))
                           (at level 100, right associativity) : tm_scope.

  Notation "c >>= f" := (tmBind c f) (at level 50, f at next level, left associativity) : tm_scope.

  (* automatically put scope on top of the stack when this module is imported. *)
  #[ global ]
   Open Scope tm_scope.
End TemplateMonadNotations.
Import TemplateMonadNotations.

(** * Evaluate monadic actions in sequence and collect results. *)
Fixpoint tm_sequence {A: Type} (mvals: list (TemplateMonadSet A)) : TemplateMonadSet (list A) :=
  match mvals with
  | [] => tmReturn []
  | mval :: mvals =>
    val <- mval;;
    vals <- tm_sequence mvals;;
    tmReturn (val :: vals)
  end.

(*   (* TODO find out why guard checker does not like the this tm_mapM *)
(*    does not accept src/parsers/CustomEntryParser.v::translate_head *) *)
(* (** * Map a monadic action over a list. *) *)
(* Fixpoint tm_mapM {A B: Type} (f: A -> TemplateMonadSet B) (l: list A) : TemplateMonadSet (list B) := *)
(*   match l with *)
(*   | [] => tmReturn [] *)
(*   | a :: l => *)
(*     b <- f a;; *)
(*     bs <- tm_mapM f l;; *)
(*     tmReturn (b :: bs) *)
(*   end. *)

(* Section MonadMap. *)
(*   Context {A B} (f : A -> TemplateMonadSet B). *)
(* (** * Map a monadic action over a list. *) *)
(*   Fixpoint tm_mapM2 (l: list A) : TemplateMonadSet (list B) := *)
(*     match l with *)
(*     | [] => tmReturn [] *)
(*     | a :: l => *)
(*       b <- f a;; *)
(*       bs <- tm_mapM2 l;; *)
(*       tmReturn (b :: bs) *)
(*     end. *)
(* End MonadMap. *)


(** * Lift a GenM computation into the TemplateMonad *)
Definition tm_liftGenM {A} (m: GenM.t A) (info: genInfo) : TemplateMonadSet A :=
  match GenM.run m {| R_flags := info.(in_flags);
                      R_sig := info.(in_sig);
                      R_env := info.(in_env) |}
                 (initial_state info.(in_implicits)) with
  | inl e => tmFail e
  | inr (_, _, x) =>
    x_eval <- tmEval all x;;
    tmReturn x_eval
  end.

(** * Register a definition in the Coq environment given the quoted representation of its type and term.
 ** * This works with terms that contain holes (but the types must not, else Coq cannot infer all holes) *)
Definition tmTypedDefinition (lem: string * term * term) : TemplateMonadSet unit :=
  let '(name, typ_q, t_q) := lem in
  typ <- tmUnquoteTyped Type typ_q;;
  (* TODO tried casting here but it still cannot infer some arguments *)
  (* t <- tmUnquoteTyped typ (tCast t_q NativeCast typ_q);; *)
  t <- tmUnquoteTyped typ t_q;;
  @tmDefinitionRed name (Some TemplateMonad.Common.hnf) typ t;;
  tmReturn tt.

(* MetaCoq Run (tmTypedDefinition "mynatnil" <% list nat %> (tApp <% @nil %> [hole])). *)

(** * Get a reference to an inductive type, constructor or defined constant.
 ** * Used to update the translation environment in our code generation functions. *)
Definition locate_name (name: string) : TemplateMonadSet (string * term) :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind => tmReturn (name, tInd ind [])
  | ConstructRef ind n => tmReturn (name, tConstruct ind n [])
  | ConstRef kn => tmReturn (name, tConst kn [])
  | _ => tmFail (String.append "unknown name or name is not an inductive/constructor/constant: " name)
  end.


(** * Get information about an inductive type given its name. *)
Definition locate_mind (name: string) : TemplateMonadSet mutual_inductive_entry :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind =>
    body <- tmQuoteInductive ind.(inductive_mind);;
    entry <- tmEval all (mind_body_to_entry body);;
    tmReturn entry
  | _ => tmFail (String.append "unknown name or name is not an inductive: " name)
  end.

(* kind of works but it's not completely evaluated *)
(** * Print a term using MetaCoq's printing functionality.
 ** * Might be used to serialize our generated code. *)
Definition my_print_term (t: term) : TemplateMonadSet unit :=
  let s := print_term ([], Monomorphic_ctx (LevelSet.Mkt [], ConstraintSet.Mkt [])) [] false t in
  tmEval TemplateMonad.Common.all s >>= tmPrint.

Definition tm_update_env (names: list string) (env: SFMap.t term) : TemplateMonadSet (SFMap.t term) :=
  env_list' <- monad_map locate_name names;;
  let env' := SFMap.fromList env_list' in
  tmReturn (update_env env' env). 
