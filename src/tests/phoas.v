Fail Inductive tm :=
| app : tm -> tm -> tm
| abs : (tm -> tm) -> tm.

Module m1.
Inductive tm (V:Type) :=
| app : tm V -> tm V -> tm V
| abs : (V -> tm V) -> tm V.
End m1.

Module m2.
Inductive ty (V:Type) :=
| arr : ty V -> ty V -> ty V
| all : (V -> ty V) -> ty V.

Inductive tm (V W:Type) :=
| app : tm V W -> tm V W -> tm V W
| tapp : tm V W -> ty V -> tm V W
| vt : vl V W -> tm V W
with vl (V W:Type) :=
| lam : ty V -> (W -> tm V W) -> vl V W
| tlam : (V -> tm V W) -> vl V W.
End m2.

Module m3.
  Variables V W : Type.
  
  Inductive ty_V :=
  | arr : ty_V -> ty_V -> ty_V
  | all : (V -> ty_V) -> ty_V.

  Inductive tm :=
  | app : tm -> tm -> tm 
  | tapp : tm -> ty_V -> tm 
  | vt : vl_W -> tm 
  with vl_W :=
  | lam : ty_V -> (W -> tm) -> vl_W 
  | tlam : (V -> tm) -> vl_W.
End m3.

Module autosubst.
Inductive ty : Type :=
  | var_ty : forall _ : nat, ty
  | arr : forall _ : ty, forall _ : ty, ty
  | all : forall _ : ty, ty.

Inductive tm : Type :=
  | app : forall _ : tm, forall _ : tm, tm
  | tapp : forall _ : tm, forall _ : ty, tm
  | vt : forall _ : vl, tm
with vl : Type :=
  | var_vl : forall _ : nat, vl
  | lam : forall _ : ty, forall _ : tm, vl
  | tlam : forall _ : tm, vl.
End autosubst.

From MetaCoq.Template Require Import utils All.

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

MetaCoq Run (printInductive "m3.tm").

(* Bei parametric HOAS wird der inductive datatype durch einen typen V parametrisiert, der fuer die Variablen steht *)
(* Da kann man auch direkt den inductive type schreiben. *)
