(** Take a signature and go through the components and call generate on each of them
 * also generate uplists for each component *)

Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.
Import MonadNotation.
From ASUB Require Import Language Utils CodeGenerator GenUps TemplateMonadUtils AssocList GenM Flags.
Import TemplateMonadInterface.

Definition genCode (sig : Signature) (flags : Flags): TemplateMonad unit :=
  let info := {| in_env := initial_env;
                 in_implicits := SFMap.empty;
                 in_flags := flags;
                 in_sig := sig |} in
  let components := sig.(sigComponents) in
  monad_fold_left (fun '(doneUps, info) component =>
                     let hd_sort := NEList.hd component in
                     substSorts <- tm_liftGenM (GenM.substOf hd_sort) info;;
                     let '(newUps, ups) := getUps substSorts doneUps info.(in_flags).(fl_scope_type) in
                     ups <- tmEval (TemplateMonad.Common.all) ups;;
                     info <- generateInductives component info;;
                     info <- generateLemmas component ups info;;
                     tmReturn (List.app doneUps newUps, info))
                  components
                  ([], info);;
  tmReturn tt.

Definition genCode2 (sig: Signature) (flags: Flags) (env: SFMap.t term): TemplateMonad unit :=
  let info := {| in_env := env;
                 in_implicits := SFMap.empty;
                 in_flags := flags;
                 in_sig := sig |} in
  let components := sig.(sigComponents) in
  monad_fold_left (fun '(doneUps, info) component =>
                     let hd_sort := NEList.hd component in
                     substSorts <- tm_liftGenM (GenM.substOf hd_sort) info;;
                     let '(newUps, ups) := getUps substSorts doneUps info.(in_flags).(fl_scope_type) in
                     ups <- tmEval (TemplateMonad.Common.all) ups;;
                     info <- generateLemmas component ups info;;
                     tmReturn (List.app doneUps newUps, info))
                  components
                  ([], info);;
  tmReturn tt.


    

