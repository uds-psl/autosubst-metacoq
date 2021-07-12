From MetaCoq.Template Require Import All Pretty.
Require Import List String.
Import ListNotations MonadNotation.

Fixpoint tm_sequence {A: Type} (mvals: list (TemplateMonad A)) : TemplateMonad (list A) :=
  match mvals with
  | [] => tmReturn []
  | mval :: mvals =>
    val <- mval;;
    vals <- tm_sequence mvals;;
    tmReturn (val :: vals)
  end.

Fixpoint tm_mapM {A B: Type} (f: A -> TemplateMonad B) (l: list A) : TemplateMonad (list B) :=
  match l with
  | [] => tmReturn []
  | a :: l =>
    b <- f a;;
    bs <- tm_mapM f l;;
    tmReturn (b :: bs)
  end.

Fixpoint tm_foldM {A B: Type} (f: A -> B -> TemplateMonad A) (l: list B) (init: A) : TemplateMonad A :=
  match l with
  | [] => tmReturn init
  | b :: l =>
    init <- f init b;;
    tm_foldM f l init
  end.

(** * Register a definition in the Coq environment given the quoted representation of its type and term.
 ** * This works with terms that contain holes (but the types must not, else Coq cannot infer all holes) *)
Definition tmTypedDefinition (lem: string * term * term) : TemplateMonad unit :=
  let '(name, typ_q, t_q) := lem in
  typ <- tmUnquoteTyped Type typ_q;;
  t <- tmUnquoteTyped typ t_q;;
  @tmDefinitionRed name (Some TemplateMonad.Common.hnf) typ t;;
  tmReturn tt.

(* MetaCoq Run (tmTypedDefinition "mynatnil" <% list nat %> (tApp <% @nil %> [hole])). *)
          
Definition locate_name (name: string) : TemplateMonad (string * term) :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind => tmReturn (name, tInd ind [])
  | ConstructRef ind n => tmReturn (name, tConstruct ind n [])
  | ConstRef kn => tmReturn (name, tConst kn [])
  | _ => tmFail (String.append "unknown name or name is not an inductive/constructor/constant: " name)
  end.

(* kind of works but it's not completely evaluated *)
Definition my_print_term (t: term) : TemplateMonad unit :=
  let s := print_term ([], Monomorphic_ctx (LevelSet.Mkt [], ConstraintSet.Mkt [])) [] false t in
  tmEval TemplateMonad.Common.all s >>= tmPrint.
