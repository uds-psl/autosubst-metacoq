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
  let components := sig.(sigComponents) in
  let substOfs := sig.(sigSubstOf) in
  tm_foldM (fun '(doneUps, info) component =>
              (* TODO pretty ugly since I can't use GenM bind here. Would have to buggle up the nlemma and nmutual_ind_entry from generate to do it here *)
              let hd_sort := NEList.hd component in
              let substSorts := SFMap.find substOfs hd_sort in
              match substSorts with
              | None => tmFail (String.append "unknown sort: " hd_sort)
              | Some substSorts =>
                let '(newUps, ups) := getUps substSorts doneUps in
                ups <- tmEval (TemplateMonad.Common.all) ups;;
                info <- generate component ups info;;
                tmReturn (List.app doneUps newUps, info)
              end)
           components
           ([], {| in_env := initial_env;
                   in_implicits := SFMap.empty;
                   in_flags := flags;
                   in_sig := sig |});;
  tmReturn tt.

(* MetaCoq Run (genCode Hsig_example.mySig default_flags). *)

    

