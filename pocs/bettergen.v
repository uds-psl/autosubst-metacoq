(** TODO code generation should happen purely in the GenM monad.
 * The only hurdle is making valid references.
 * 1. if we keep using the environment we want to fill it after every generated lemma.
 *    but we don't use locate_name from TemplateMonad, rather we build the references ourself which is not too hard. The most problematic thing is finding out the curent module.
 *    idea: the user should specify the module anyways because of shadowing issues
 *)

Definition mkLemmaTyped (m: GenM.t lemma) (info: genInfo) : TemplateMonad genInfo :=
  mkLemmasTyped (GenM.fmap (fun l => [l]) m) info.

Module lemmagen.
  Import GenM.Notations GenM.

  Definition genlemmas2 (component: NEList.t tId) (upList: list (Binder * tId)) : t (list lemma) :=
    let componentL := NEList.to_list component in
    let lemmas := [
          (* TODO check if component has binders *)
          (*  * should probably use a nonempty list for the component then *)
          (** * Renamings *)
          (genUpRens upList);
        (genRenamings component);
        (** * Substitutions *)
        (genUpSubsts upList);
        (genSubstitutions component);
        (** * idSubst *)
        (genUpIds upList);
        (genIdLemmas component);
        (** * Extensionality *)
        (genUpExtRens upList);
        (genExtRens component);
        (genUpExts upList);
        (genExts component);
        (** * Combinations *)
        (genUpRenRens upList);
        (genCompRenRens component);
        (genUpRenSubsts upList);
        (genCompRenSubsts component);
        (genUpSubstRens upList);
        (genCompSubstRens component);
        (genUpSubstSubsts upList);
        (genCompSubstSubsts component);
        (** * rinstInst *)
        (genUpRinstInsts upList);
        (genRinstInsts component);
        (genLemmaRinstInsts componentL);
        (** * rinstId/instId *)
        (genLemmaInstIds componentL);
        (genLemmaRinstIds componentL);
        (** * varL *)
        (genVarLs componentL);
        (genVarLRens componentL);
        (** * Combinations *)
        (genLemmaCompRenRens componentL);
        (genLemmaCompRenSubsts componentL);
        (genLemmaCompSubstRens componentL);
        (genLemmaCompSubstSubsts componentL) ] in
    fmap (@List.concat _) (sequence lemmas).

  Definition genlemmas3 : t (list lemma) := pure [].

  Definition lemmagen (component: NEList.t tId) (upList: list (Binder * tId)) : t (list lemma) :=
    let componentL := NEList.to_list component in
    congruences <- fmap (@List.concat _) (sequence (List.map genCongruences componentL));;
    hasSubsts <- hasSubsts (NEList.hd component);;
    if hasSubsts
    then lemmas <- genlemmas2 component upList;;
         pure (List.app congruences lemmas)
    else lemmas <- genlemmas3;;
         pure (List.app congruences lemmas).
End lemmagen.

Definition generate2 (component: NEList.t tId) (upList: list (Binder * tId)) (info: genInfo) : TemplateMonad genInfo :=
  let componentL := NEList.to_list component in
  (** * Inductive Types *)
  (* generate the inductive types *)
  (** TODO the component already only includes definable sorts *)
  info <- mkInductive (genMutualInductive component) info;;
  let lemmas := lemmagen.lemmagen component upList in
  (** * Congruence Lemmas *)
  (* if we generate multiple lemmas we need to keep updating the infoironment in a fold *)
  info <- mkLemmasTyped lemmas info;;
  tmReturn info.
