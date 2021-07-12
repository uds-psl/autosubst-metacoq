Require Import String Arith List.
Import ListNotations.

From ASUB Require Import Language Utils Quotes GallinaGen.
From MetaCoq.Template Require Import Ast.

Open Scope string.

Definition nat_ := nTerm nat_q.
Definition eq_ (s t: nterm) := nApp (nTerm eq_q) [nHole; s; t].
Definition eq_refl_ := nApp (nTerm eq_refl_q) [nHole; nHole].
Definition ap_ (s t: nterm) := nApp (nTerm ap_q) [ nHole; nHole; s; nHole; nHole; t ].
Definition eq_trans_ (s t: nterm) := nApp (nTerm eq_trans_q) [nHole; nHole; nHole; nHole; s; t].
Definition eq_sym_ (s: nterm) := nApp (nTerm eq_sym_q) [nHole; nHole; nHole; s].
Definition f_equal_ (feq_lam s t H: nterm) := nApp (nTerm f_equal_q) [nHole; nHole; feq_lam; s; t; H].
Definition up_ren_ (s: nterm) := nApp (nTerm up_ren_q) [s].
Definition scons_ (s t: nterm) := nApp (nTerm scons_q) [nHole; s; t].
Definition var_zero_ := nTerm var_zero_q.
Definition funcomp_ (f g: nterm) : nterm := nApp (nTerm funcomp_q) [nHole; nHole; nHole; f; g].
Definition shift_ := nTerm shift_q.
Definition id_ := nApp (nTerm id_q) [nHole].
Definition up_ren_ren_ := nTerm up_ren_ren_q.

Notation "g >>> f" := (funcomp_ f g) (at level 70, no associativity).


(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
Definition getPattern {A: Type} (name: string) (l: list A) :=
  mapi (fun i _ => name ++ string_of_nat i) l.


(* Definition lambda_ (bname: string) (ty body: term) := *)
(*   tLambda {| binder_name := nNamed bname; binder_relevance := Relevant |} ty body. *)

Definition add_binders (bs: list (string * nterm)) (body: nterm) :=
  List.fold_right (fun '(bname, btype) body => nLambda bname btype body) body bs.

Definition add_tbinders (bs: list (string * nterm)) (body: nterm) :=
  List.fold_right (fun '(bname, btype) body => nProd bname btype body) body bs.

(** * The following definitions are just hardcoded for System F ty *)

(** Create the argument type for the variable constructor of the given sort.
 ** If we create well scoped code fin will be indexed by the element of the scope indices
 ** corresponding to the sort.
 ** For sort vl and ns = [nty; nvl], create fin nvl *)

(* TODO make general *)
Definition genVarArg (sort: string) : nterm := nat_.

(** Construct the body of a definition depending on if the given sort matches the one in the binder *)
Definition definitionBody (sort: tId) (binder: Binder) (singleMatch singleNoMatch: nterm) (* (f_listMatch: string -> tId -> term)  *) : nterm :=
  match binder with
  | Single sort' => if eqb sort sort'
                   then singleMatch
                   else singleNoMatch
  (* TODO binder list case *)
  (* | L.BinderList (p, sort') -> *)
  (*   let (listMatch, listNoMatch) = f_listMatch p sort' in *)
  (*   if sort = sort' then listMatch else listNoMatch *)
  end.

(** Extract the extra shifting argument from a BinderList.
 ** In MetaCoq all binders are explicit so we don't even have the binvparameters function *)
Definition bparameters (binder: Binder) : list term * list (term -> term) :=
  match binder with
  | Single x => ([], [])
  (* | BinderList (m, _) -> ([ref_ m], [binder1_ ~implicit:true ~btype:nat_ m]) *)
  end.

