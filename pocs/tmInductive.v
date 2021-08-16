
From ASUB Require Import core util.
From MetaCoq.Template Require Import utils All.
Import ListNotations MonadNotation Nat.


(* Inductive ty : Type := *)
(* | var_ty : nat -> ty *)
(* | arr : ty -> ty -> ty *)
(* | allt : ty -> ty.  *)

MetaCoq Quote Definition nat_q := nat.

Definition ty_i : one_inductive_entry :=
{|
  mind_entry_typename := "ty";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_consnames := ["var_ty"; "att"; "allt"];
  mind_entry_lc := [mkArr nat_q [tRel 1]; mkArr (tRel 0) [tRel 1; tRel 2]; mkArr (tRel 0) [tRel 1]];
|}.

Definition ty_mi : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [];
  mind_entry_inds := [ty_i];
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

(* MetaCoq Unquote Inductive ty_mi. *)
(* MetaCoq Quote Definition ty_q := ty. *)

(* Inductive tm : Type := *)
(*   | app : tm -> tm -> tm *)
(*   | tapp : tm -> ty -> tm *)
(*   | vt : vl -> tm *)
(* with vl : Type := *)
(*   | var_vl : nat -> vl *)
(*   | lam : ty -> tm -> vl *)
(*   | tlam : tm -> vl. *)

Definition tm_i (ty_q: term): one_inductive_entry :=
{|
  mind_entry_typename := "tm";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_consnames := ["app"; "tapp"; "vt"];
  mind_entry_lc := [mkArr (tRel 1) [tRel 2; tRel 3]; mkArr (tRel 1) [ty_q; tRel 3]; mkArr (tRel 0) [tRel 2]];
|}.

Definition vl_i (ty_q: term): one_inductive_entry :=
{|
  mind_entry_typename := "vl";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_consnames := ["var_vl"; "lam"; "tlam"];
  mind_entry_lc := [mkArr nat_q [tRel 1]; mkArr ty_q [tRel 2; tRel 2]; mkArr (tRel 1) [tRel 1]];
|}.

Definition tmvl_mi (ty_q: term) : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [];
  mind_entry_inds := [tm_i ty_q; vl_i ty_q];
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

(* MetaCoq Unquote Inductive tmvl_mi. *)

(* MetaCoq Quote Definition tm_q := tm. *)
(* MetaCoq Quote Definition vl_q := vl. *)

Definition getInductiveRef (q:qualid) :=
  kn <- tmLocate1 q;;
  match kn with
  | IndRef ind => tmReturn (tInd ind [])
  | _ => tmFail "not an inductive"
  end.

Definition mkInds : TemplateMonad unit :=
  tmMkInductive ty_mi;;
  ty_q <- getInductiveRef "ty";;
  tmMkInductive (tmvl_mi ty_q);;
  tmReturn tt.

MetaCoq Run mkInds.

From MetaCoq.PCUIC Require PCUICAst.

Module dominate.
  
  Definition test_i : one_inductive_entry :=
    {|
    mind_entry_typename := "T";
    mind_entry_arity := tSort Universe.type0;
    mind_entry_consnames := ["C"];
    mind_entry_lc := [tProd {| binder_name := BasicAst.nNamed "X"; binder_relevance:= BasicAst.Relevant |} (tSort Universe.type0) (tRel 0) ];
    |}.

  Definition test_mi : mutual_inductive_entry :=
    {|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := [test_i];
    mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
    mind_entry_template := false;
    mind_entry_variance := None;
    mind_entry_private := None;
    |}.

  Fail MetaCoq Unquote Inductive test_mi.
End dominate.
