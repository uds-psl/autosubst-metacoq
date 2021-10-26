Require Import String List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import Ast.
From ASUB Require Import GenM AssocList DeBruijnMap TemplateMonadUtils Utils Nterm.

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

Fixpoint zipImplicits (implicits: list bool) (ts: list term) : GenM.t (list term) :=
  match implicits with
  | [] => pure ts
  | i :: implicits =>
    if i
    then
     res <- zipImplicits implicits ts;;
     pure (hole :: res)
    else match ts with
         | [] => pure []
         | t :: ts =>
           res <- zipImplicits implicits ts;;
           pure (t :: res)
         end
  end.

(** Translates our custom AST to the MetaCoq AST,
 ** the debruijn map is updated when translation goes beneath a binder. *)
Fixpoint translate' (dbmap: DB.t) (t: nterm) : GenM.t term :=
  match t with
  | nRef s =>
    (* We first check if the reference is a local variable in the dbmap *)
    x <- (match dbmap s with
         | Some n => pure (tRel n)
         | None =>
           (* if it's not local we check if it's defined in the environment *)
           env <- asks R_env;;
           match SFMap.find env s with
           | Some t => pure t
           | None =>
             (* otherwise we assume it is a definition from the current module (e.g. if one of our lemmas references another)
              * so we make a fully qualified name by prepending the module path *)
             mp <- asks R_modpath;;
             pure (tConst (mp, s) [])
           end
        end);;
    pure x
  | nConst s =>
    (* constants are always assumed to be from the current module *)
    mp <- asks R_modpath;;
    pure (tConst (mp, s) [])
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
    (* have to translate ts beforehand and call zipImplicits with ts because of guard checker *)
    match nt with
    | nRef s =>
      implicits <- get_implicits s;;
      tsImplicits <- zipImplicits implicits ts;;
      pure (tApp t tsImplicits)
    | _ => pure (tApp t ts)
    end
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

(** Translates our custom AST to the MetaCoq AST *)
Definition translate (t: nterm) : GenM.t term :=
  translate' DB.empty t.
  
Definition translate_lemma (l: nlemma) : GenM.t lemma :=
  let '(lname, ntype, nbody) := l in
  ttype <- translate ntype;;
  tbody <- translate nbody;;
  pure (lname, ttype, tbody).
