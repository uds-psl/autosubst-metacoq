From MetaCoq.Template Require Import All.
From ASUB Require Import CodeGenDispatch Language ErrorM GenM.
From ASUB Require Export CustomEntryParser Flags.

(** * Open the notations *)
Export SyntaxNotation SyntaxTranslation.

Definition runAutosubst (lang: autosubstLanguage) (flags : Flags): TemplateMonad unit :=
  match ErrorM.run (translate_signature lang) tt tt with
  | inl e => tmFail e
  | inr (_, _, sig) => genCode sig flags 
  end.

Module AutosubstNotations.
  Notation "'Autosubst' scope 'for' lang" := (runAutosubst lang {| fl_scope_type := scope |}) (at level 8).

End AutosubstNotations.
Export AutosubstNotations.

(* MetaCoq Run Autosubst Unscoped for fcbv. *)

