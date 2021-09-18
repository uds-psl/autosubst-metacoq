Require Import String List.
Import ListNotations.
#[ local ]
 Open Scope string.

From MetaCoq.Template Require Import Ast.
From ASUB Require Import Language.

Definition separator := "_".
Definition sep x y := x ++ separator ++ y.
Fixpoint sepd xs :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: xs => sep x (sepd xs)
  end.


Definition aname_ (name: string) : aname := {| binder_name := nNamed name; binder_relevance := Relevant |}.

Definition varConstrName x := sep "var" x.


Definition congrName (sort: string) := sep "congr" sort.

Definition renName (x: string) := sep "ren" x.

Definition substName (x: string) := sep "subst" x.
Definition idSubstName (sort: tId) := sep "idSubst" sort.
Definition extRenName sort := sep "extRen" sort.
Definition extName sort := sep "ext" sort.
Definition compRenRenName x := sep "compRenRen" x.
Definition compRenSubstName x := sep "compRenSubst" x.
Definition compSubstRenName x := sep "compSubstRen" x.
Definition compSubstSubstName x := sep "compSubstSubst" x.
Definition rinstInstName x := sep "rinst_inst" x.
Definition rinstInstRewriteName x := sep "rinstInst" x.
Definition rinstIdName x := sep "rinstId" x.
Definition instIdName x := sep "instId" x.
Definition varLRenName x := sep "varLRen" x.
Definition varLName x := sep "varL" x.
Definition renRenName x := sep "renRen" x.
Definition renSubstName x := sep "renSubst" x.
Definition substRenName x := sep "substRen" x.
Definition substSubstName x := sep "substSubst" x.


Definition upNameGen (name: string) (sort: tId) (binder: Binder) :=
  match binder with
  | Single sort' => sepd [name; sort'; sort]
  end.
Definition upRenName := upNameGen "upRen".
Definition upName := upNameGen "up". 
Definition upIdName := upNameGen "upId". 
Definition upExtRenName := upNameGen "upExtRen".
Definition upExtName := upNameGen "upExt".
Definition upRenRenName := upNameGen "up_ren_ren".
Definition upRenSubstName := upNameGen "up_ren_subst".
Definition upSubstRenName := upNameGen "up_subst_ren".
Definition upSubstSubstName := upNameGen "up_subst_subst".
Definition upRinstInstName := upNameGen "up_rinst_inst".







