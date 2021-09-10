Require Import String List.

From MetaCoq.Template Require Import All.
From ASUB Require Import GenM AssocList DeBruijnMap Language TemplateMonadUtils Utils.

(* TODO add another node for embedded terms. This should be a bit more performant when we use predefined terms like "eq" since we don't really need to look them up in the environment. *)
Inductive nterm : Type :=
| nRef : string -> nterm (* turns into tRel, tConst, tInd, tConstruct from the normal term type *)
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

Import GenM.Notations GenM.

(* TODO maybe make it option string but then I don't have error handling.
 * Just a possible performance improvement *)
Definition get_fix_name (d: def nterm) : GenM.t string :=
  match binder_name (dname d) with
  | nAnon => error "Fixpoint without a name."
  | nNamed s => pure s
  end.

(* TODO already defined somewhere? *)
Definition get_inductive (s: string) : GenM.t inductive :=
  env <- asks R_env;;
  match SFMap.find env s with
  | None => error (append "get_inductive: not found: " s)
  | Some t => match t with
             | tInd ind _ => pure ind
             | _ => error "wrong kind of term"
             end
  end.
    
Fixpoint translate' (dbmap: DB.t) (t: nterm) : GenM.t term :=
  match t with
  | nRef s =>
    (* check dbmap and environment *)
    x <- (match dbmap s with
         | Some n => pure (tRel n)
         | None =>
           env <- asks R_env;;
           match SFMap.find env s with
           | Some t => pure t
           | None => error (append "Unknown Identifier during Gallina Translation: " s)
           end
        end);;
    implicitNum <- get_implicits s;;
    match implicitNum with
    | O => pure x
    | S _ => pure (tApp x (list_fill hole implicitNum))
    end
  | nHole => pure hole
  | nTerm t => pure t
  | nProd s nt0 nt1 =>
    let n := {| binder_name := nNamed s; binder_relevance := Relevant |} in
    t0 <- translate' dbmap nt0;;
    (* add the newly bound variable when translating nt1 *)
    let dbmap' := DB.add s dbmap in
    t1 <- translate' dbmap' nt1;;
    pure (tProd n t0 t1)
  | nArr nt0 nt1 =>
    let n := {| binder_name := nAnon; binder_relevance := Relevant |} in
    t0 <- translate' dbmap nt0;;
    (* just shift the dbmap when translating nt1 *)
    let dbmap' := DB.shift dbmap in
    t1 <- translate' dbmap' nt1;;
    pure (tProd n t0 t1)
  | nLambda s nt0 nt1 =>
    let n := {| binder_name := nNamed s; binder_relevance := Relevant |} in
    t0 <- translate' dbmap nt0;;
    (* add the newly bound variable when translating nt1 *)
    let dbmap' := DB.add s dbmap in
    t1 <- translate' dbmap' nt1;;
    pure (tLambda n t0 t1)
  | nApp nt nts =>
    t <- translate' dbmap nt;;
    ts <- a_map (translate' dbmap) nts;;
    pure (tApp t ts)
  | nFix mfixs n =>
    fixNames <- a_map get_fix_name mfixs;;
    let dbmap' := DB.adds fixNames dbmap in
    mfixs <- a_map (fun '{| dname := nname; dtype := ntype; dbody := nbody; rarg := nrarg |} =>
                     ttype <- translate' dbmap ntype;;
                     (* the fixpoint names are only bound in the bodies *)
                     tbody <- translate' dbmap' nbody;;
                     pure {| dname := nname; dtype := ttype; dbody := tbody; rarg := nrarg |})
                  mfixs;;
    pure (tFix mfixs n)
  | nCase indName paramNum nelimPred ndiscr nbranches =>
    telimPred <- translate' dbmap nelimPred;;
    tdiscr <- translate' dbmap ndiscr;;
    tbranches <- a_map (fun '(n, nt) =>
                         t <- translate' dbmap nt;;
                         pure (n, t))
                      nbranches;;
    ind <- get_inductive indName;;
    pure (tCase (ind, paramNum, Relevant) telimPred tdiscr tbranches)
  end.

(* TODO merge left-nested applications
 * We want to save information in the envionment about implicit arguments of certain functions.
 * Therefore we want to have an analysis step where if we have an nApp of an nRef we check if this reference should have any implicit arguments and add them to the argument list *)
Definition translate (t: nterm) : GenM.t term :=
  translate' DB.empty t.
  
Definition translate_lemma (l: t nlemma) : GenM.t lemma :=
  '(lname, ntype, nbody) <- l;;
  ttype <- translate ntype;;
  tbody <- translate nbody;;
  pure (lname, ttype, tbody).
