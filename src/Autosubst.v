Require Import List String.

Import ListNotations.


From MetaCoq.Template Require Import All.
From ASUB Require Import CodeGenDispatch Language ErrorM GenM CustomEntryParser Flags AssocList TemplateMonadUtils.
Import TemplateMonadNotations.

(** * Open the notations *)
Export SyntaxTranslation Syntax.

Definition runAutosubst (lang: autosubstLanguage) (flags : Flags): TemplateMonad unit :=
  sig <- translate_signature lang;;
  genCode sig flags.

(** * return names of all sorts and constructors of the given language *)
Definition getIndCtorNames (sig: Signature) : list string :=
  let sortNames := List.concat (List.map (fun nel => NEList.to_list nel) sig.(sigComponents)) in
  let ctorNames := List.map (fun ctor => con_name ctor) (List.concat (SFMap.values sig.(sigSpec))) in
  let varCtorNames := List.map (fun sort => String.append "var_" sort) (SSet.toList sig.(sigIsOpen)) in
  List.concat [sortNames; varCtorNames; ctorNames].
  
Definition runAutosubstNoInd (lang: autosubstLanguage) (flags : Flags): TemplateMonad unit :=
  sig <- translate_signature lang;;
  (** get all names of the inductive types and their constructors *)
  let names := getIndCtorNames sig in 
  env <- tm_update_env names initial_env;;
  genCode2 sig flags env.

Module AutosubstNotations.
  Notation "'Autosubst' scope 'for' lang" := (runAutosubst lang {| fl_scope_type := scope |}) (at level 8).
  Notation "'AutosubstNoInd' scope 'for' lang" := (runAutosubstNoInd lang {| fl_scope_type := scope |}) (at level 8).
  

End AutosubstNotations.
Export AutosubstNotations.


