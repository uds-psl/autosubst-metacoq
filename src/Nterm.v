Require Import String List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import All.

(* TODO add another node for embedded terms. This should be a bit more performant when we use predefined terms like "eq" since we don't really need to look them up in the environment. *)
Inductive nterm : Type :=
| nRef : string -> nterm (* turns into tRel, tInd, tConstruct from the normal term type. This needs to looked up in the environment during translation *)
| nConst : string -> nterm (* turns into tConst from the normal term type. We use the modpath from GenM to build the correct kername *)
| nHole : nterm
| nTerm : term -> nterm
| nProd : string -> nterm -> nterm -> nterm
| nArr : nterm -> nterm -> nterm
| nLambda : string -> nterm -> nterm -> nterm
| nApp : nterm -> list nterm -> nterm
| nFix : mfixpoint nterm -> nat -> nterm
| nCase : string -> nat -> nterm -> nterm -> list (nat * nterm) -> nterm.

Definition nlemma : Type := string * nterm * nterm.
Definition lemma : Type := string * term * term.

Fixpoint mknArr (nt0: nterm) (nts: list nterm) :=
  match nts with
  | [] => nt0
  | nt :: nts =>
    nArr nt0 (mknArr nt nts)
  end.

Fixpoint mknArrRev (nts: list nterm) (nt0: nterm) :=
  match nts with
  | [] => nt0
  | nt :: nts => nArr nt (mknArrRev nts nt0)
  end.
