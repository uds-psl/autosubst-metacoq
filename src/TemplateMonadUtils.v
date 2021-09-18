Require Import List String.
Import ListNotations.

From MetaCoq.Template Require Import All Pretty.
From ASUB Require Import AssocList.
Import MonadNotation.

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

(* TODO some of these functions should already be in monad_utils.v of the TemplateMonad library *)
(** * Evaluate monadic actions in sequence and collect results. *)
Fixpoint tm_sequence {A: Type} (mvals: list (TemplateMonad A)) : TemplateMonad@{_ Set} (list A) :=
  match mvals with
  | [] => tmReturn []
  | mval :: mvals =>
    val <- mval;;
    vals <- tm_sequence mvals;;
    tmReturn (val :: vals)
  end.

(** * Map a monadic action over a list. *)
Fixpoint tm_mapM {A B: Type} (f: A -> TemplateMonad B) (l: list A) : TemplateMonad@{_ Set} (list B) :=
  match l with
  | [] => tmReturn []
  | a :: l =>
    b <- f a;;
    bs <- tm_mapM f l;;
    tmReturn (b :: bs)
  end.

(** * Left-fold a monadic action over a list. *)
Fixpoint tm_foldM {A B: Type} (f: A -> B -> TemplateMonad A) (l: list B) (init: A) : TemplateMonad@{_ Set} A :=
  match l with
  | [] => tmReturn init
  | b :: l =>
    init <- f init b;;
    tm_foldM f l init
  end.

(** * Register a definition in the Coq environment given the quoted representation of its type and term.
 ** * This works with terms that contain holes (but the types must not, else Coq cannot infer all holes) *)
Definition tmTypedDefinition (lem: string * term * term) : TemplateMonad@{_ Set} unit :=
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
Definition locate_name (name: string) : TemplateMonad@{_ Set} (string * term) :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind => tmReturn (name, tInd ind [])
  | ConstructRef ind n => tmReturn (name, tConstruct ind n [])
  | ConstRef kn => tmReturn (name, tConst kn [])
  | _ => tmFail (String.append "unknown name or name is not an inductive/constructor/constant: " name)
  end.

(* TODO find out how to construct reference so that I don't have to take the detour through TemplateMonad *)
(* Inductive bla := foo : bla. *)
(* (* module name + inductive name + inductive index *) *)
(* MetaCoq Run (locate_name "bla" >>= tmPrint). *)
(* (* module name + inductive name + inductive index + ctor index *) *)
(* MetaCoq Run (locate_name "foo" >>= tmPrint). *)
(* Lemma ta : True. *)
(* Proof. *)
(*   exact I. *)
(* Qed. *)

(* (* module name + lemma name *) *)
(* MetaCoq Run (locate_name "ta" >>= tmPrint). *)


(** * Get information about an inductive type given its name. *)
Definition locate_mind (name: string) : TemplateMonad@{_ Set} mutual_inductive_entry :=
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
Definition my_print_term (t: term) : TemplateMonad@{_ Set} unit :=
  let s := print_term ([], Monomorphic_ctx (LevelSet.Mkt [], ConstraintSet.Mkt [])) [] false t in
  tmEval TemplateMonad.Common.all s >>= tmPrint.

Definition update_env (env env' : SFMap.t term) : SFMap.t term :=
  SFMap.union env env'.

Definition tm_update_env (names: list string) (env: SFMap.t term) : TemplateMonad@{_ Set} (SFMap.t term) :=
  env_list' <- (tm_mapM locate_name names);;
  let env' := SFMap.fromList env_list' in
  tmReturn (update_env env' env). 
