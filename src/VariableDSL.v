Require Import String.
Require Import List.
Import ListNotations.
From ASUB Require Import Utils GallinaGen Termutil SubstTy.

Inductive ScopeVar : Set := K | L | M.
Inductive ScopeVars : Set := KS | LS | MS.
Inductive RenVar : Set :=
| XI : ScopeVar -> ScopeVar -> RenVar
| ZETA : ScopeVar -> ScopeVar -> RenVar
| RHO : ScopeVar -> ScopeVar -> RenVar.
Inductive RenVars : Set :=
| XIS : ScopeVars -> ScopeVars -> RenVars
| ZETAS : ScopeVars -> ScopeVars -> RenVars
| RHOS : ScopeVars -> ScopeVars -> RenVars.
Inductive VarSpec : Set :=
| scopeVar :> ScopeVar -> VarSpec
| scopeVars :> ScopeVars -> VarSpec
| renVar :> RenVar -> VarSpec
| renVars :> RenVars -> VarSpec.

(* Coercions functionieren nicht da man die Liste nicht zusammenbauen kann.
 * Doch tatsaechlich funktioniert es wenn man bidirectionlity hints einbaut.
 * Wie hier auf Zulip beschrieben https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Coercions.20inside.20tuples *)
(* mit Typklassen geht es gut wie hier beschrieben https://stackoverflow.com/questions/26755507/coq-notation-for-multi-type-list
 * Leider muss ich dann die Listnotation veraendern um mein CONS zu benutzen *)
(* Ich koennte es auch mit einem custom parser versuchen, aber dann brauche ich auch meine eigene Listensyntax und es waere mehr brittle.
 zb wenn ich eine neue Variable shinzufuege, muesste ich den Parser veraendern. Mit Typklassen nur den Induktive Type selbst + ggf eine neue Instanz *)
(* Class ConsVarSpec (A:Set) := *)
(*   { CONS: A -> list VarSpec -> list VarSpec }. *)

(* Instance ConsScopeVar : ConsVarSpec ScopeVar := *)
(*   { CONS := fun a => cons (scopeVar a) }. *)
(* Instance ConsScopeVars : ConsVarSpec ScopeVars := *)
(*   { CONS := fun a => cons (scopeVars a) }. *)
(* Instance ConsRenVar : ConsVarSpec RenVar := *)
(*   { CONS := fun a => cons (renVar a) }. *)
(* Instance ConsRenVars : ConsVarSpec RenVars := *)
(*   { CONS := fun a => cons (renVars a) }. *)

(* #[ local ] *)
(*  Notation "[< x ; .. ; y >]" := (CONS x .. (CONS y nil) .. ). *)

(* Check [<K; LS; XI K L; XIS KS LS>]. *)


(* Arguments pair {_ _} & _ _. *)

(* here we define the bidirectionality hint so that our coercions work in a list *)
Arguments cons {_} & _ _.
Check ([ K; XI K L; XIS KS LS ] : list VarSpec).

Definition genVariableShape (var_spec: VarSpec) : Type :=
  match var_spec with
  | scopeVar _ | renVar _ => nterm 
  | scopeVars _ | renVars _ => SubstTy
  end.

#[ local ]
 Open Scope type.
Definition boundVariable := string * nterm.

(* TODO should use NEList.t instead of list so that I don't get the default argument in fold_list *)
(* TODO since I don't think I can use fold_left for the definitions, I would have to use normal lists. But can I define my own pair type that is right associative to make it easier? *)
Fixpoint genVariableShapes (var_specs: list VarSpec) : Type :=
  match var_specs with
  | [] => unit
  | v :: var_specs =>
    let t := genVariableShapes var_specs in
    let t' := genVariableShape v in
    t' * t
  end.

Definition genVariableShapesFold (init: Type) (var_specs: list VarSpec): Type :=
  fold_left (fun t v => t * genVariableShape v)
            var_specs init.

(* in the short version we don't want the unit at the end.
 * The unit appears in genVaraibleShapesFold because the first value of init is tt.
 * That's why we define another wrapper around it to catch that case and set init to the shape of the first variable *)
Fixpoint genVariableShapesShort' (init: Type) (var_specs: list VarSpec): Type :=
  match var_specs with
  | [] => init
  | v :: var_specs =>
    let t := genVariableShape v in
    genVariableShapesShort' (init * t) var_specs
  end.

Definition genVariableShapesShort (var_specs: list VarSpec) : Type :=
  match var_specs with
  | [] => unit
  | v :: var_specs =>
    genVariableShapesShort' (genVariableShape v) var_specs
  end.

(* schachtelung anders rum durch akkumulierendes Argument. wie beihttps://github.com/mit-plv/engine-bench/pull/4 *)
(* Funktion die aus einer Liste von Typen einen links- und recchtsassoziierten Tupeltypen baut und sie uebersetzen kann. *)

(* so kann man ein dependent left fold schreiben, habe ich aber am Ende nicht gebraucht *)
Fixpoint fold_left_dep' {A} (fT: list A -> Type) (f: forall (l_acc: list A) (b: fT l_acc) (a: A), fT (List.app l_acc [a])) (l_acc: list A) (l: list A) (init: fT l_acc) (l_max: list A) (Hl: List.app l_acc l = l_max) : fT l_max.
Proof.
  destruct l as [|a l'].
  - subst l_max. rewrite app_nil_r. exact init.
  - refine (fold_left_dep' A fT f (List.app l_acc [a]) l' (f l_acc init a) l_max _).
    rewrite <- app_assoc. exact Hl.
Defined.

Definition fold_left_dep {A} (fT: list A -> Type) (f: forall (l_acc: list A) (b: fT l_acc) (a: A), fT (List.app l_acc [a])) (l: list A) (init: fT []) : fT l.
Proof.
  refine (fold_left_dep' fT f [] l init l eq_refl).
Defined.


Definition genVariable (sort: string) (var_spec: VarSpec) : (genVariableShape var_spec * list boundVariable) :=
  match var_spec with
  | scopeVar _ => (nRef "scope", [])
  | scopeVars _ => (SubstScope ["m_ty"; "m_vl"] [nRef "m_ty"; nRef "m_vl"], [])
  | renVar _ => (nRef "ren", [])
  | renVars _ => genRen2 "xi" "tm" ["ty"; "vl"]
  end.

(* TODO probably not a good idea to match on single element list b/c of code duplication *)
Fixpoint genVariables (sort: string) (var_specs: list VarSpec) {struct var_specs}: (genVariableShapes var_specs * list boundVariable) :=
  match var_specs with
  | [] => (tt, [])
  | v :: var_specs' =>
    let '(ts, bs) := genVariables sort var_specs' in
    let '(t', bs') := genVariable sort v in
    ((t', ts), List.app bs bs')
  end.

Definition genVariablesFold (sort: string) (var_specs: list VarSpec) : (genVariableShapesFold unit var_specs).
  refine (fold_left_dep (genVariableShapesFold unit) _ var_specs tt).
  intros l_acc acc a. unfold genVariableShapesFold in *.
  rewrite fold_left_app.
  destruct a; cbn.
  (* here I have the acc which is a tuple of type generated by the fold left and I need to construct tuples also generated by fold_left with different initial value.
   * so I would need to deconstruct the tuple and build it up again in every step. My lists are mostly of length <= 8 but still that seems like a bad way
   *
   * I think the reason for the problem is the append in fold_left_dep. So what if I use a fold_right here? *)
Abort.

(* ok so if I understand this right this constructs a tuple of a type constructed by
 * genVariablesShapeFold (i.e. left-associated) still by doing a left-fold which is inlined and
 * we update the accumulator every time.
 * this should be performant enough
 *
 * so where exactly is the difference with the prevous definition that used fold_left_dep explicitly?
 *)
(* Definition genVariablesFold (sort: string) (var_specs: list VarSpec) : (genVariableShapesFold unit var_specs) * list boundVariable. *)
(* Proof. *)
(*   revert var_specs. *)
(*   enough (H: forall A : Type, A -> forall var_specs : list VarSpec, (genVariableShapesFold A var_specs) * list boundVariable) by (apply (H unit tt)). *)
(*   fix F 3. *)
(*   intros A init var_specs. *)
(*   destruct var_specs. *)
(*   - split. exact init. exact []. *)
(*   - cbn. *)
(*     destruct (genVariable sort v) as [t bs']. *)
(*     destruct (F (A * genVariableShape v) (init, t) var_specs) as [ts bs]. *)
(*     refine ((ts, List.app bs bs')). *)
(* Defined. *)


Fixpoint genVariablesFold' {A:Type} (sort: string) (init: A) (var_specs: list VarSpec) {struct var_specs} : (genVariableShapesFold A var_specs) * list boundVariable :=
  match var_specs with
  | [] => (init, [])
  | v :: var_specs =>
    let '(t, bs') := genVariable sort v in
    let '(ts, bs) := genVariablesFold' sort (init, t) var_specs in
    (ts, List.app bs bs')
  end.

Definition genVariablesFold (sort: string) (var_specs: list VarSpec) : (genVariableShapesFold unit var_specs) * list boundVariable :=
  @genVariablesFold' unit sort tt var_specs.

Fixpoint genVariablesShort' {A:Type} (sort: string) (init: A) (var_specs: list VarSpec) {struct var_specs} : (genVariableShapesShort' A var_specs) * list boundVariable.
Proof.
  refine (match var_specs with
          | [] => (init, [])
          | v :: var_specs0 => _
         end).
  refine (
    let '(t, bs) := genVariable sort v in
    let '(ts, bs') := genVariablesShort' (A * genVariableShape v) sort (init, t) var_specs0 in
    _).
  split.
  2: exact (List.app bs bs').
  exact ts.
Defined.

Definition genVariablesShort (sort: string) (var_specs: list VarSpec) : (genVariableShapesShort var_specs) * list boundVariable.
Proof.
  refine (match var_specs with
          | [] => (tt, [])
          | v :: var_specs => _
         end).
  refine (
  let '(t, bs) := genVariable sort v in
  let '(ts, bs') := genVariablesShort' sort t var_specs in
  _).
  exact (ts, List.app bs bs').
Defined.

Check ZETA K L.


#[ local ]
Notation "( x ; .. ; y ; z )" := (pair x .. (pair y z) ..) : core_scope.
(** * works so far but the matchin in the end is a bit awkward because I need to nest muy pairs to the right.
 * 
 * I tried to define my functions using a fold_left first but ran into a problem
 * genVariablesShape -> works fine
 * genVariables -> can't use normal fold_left because of dependent type since I need to give the default argument right at the beginning.
 * And I don't think I can write a dependent fold_left 
 *
 * However it works by inlining a right_fold (did not try with an actual right fold yet because that also would need to be dependent but it's probably easier)
 * But then my return pairs are nested to the right so I should redefine pair syntax to make it easier 
 *)
Arguments concat [_] & _.
Definition testGen (_: unit) :=
  (* DONE define notations so that I can write my expressions easier *)
  (* let '((k; l; ks; ls; xi; zeta; xis; zetas; _), scopeBinders) := genVariables "asd" [ scopeVar K; scopeVar L; scopeVars KS; scopeVars LS; renVar (XI K L); renVar (ZETA K L); renVars (XIS KS LS); renVars (ZETAS KS LS) ] in *)
  let x := genVariables "asd" (List.concat [
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];        
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ]
                                   ]) in
  x.


Definition testGenFold (_: unit) :=
  (* let '(_, k, l, ks, ls, xi, zeta, xis, zetas) := genVariablesFold "asd" tt [ scopeVar K; scopeVar L; scopeVars KS; scopeVars LS; renVar (XI K L); renVar (ZETA K L); renVars (XIS KS LS); renVars (ZETAS KS LS) ] in *)
  let x := genVariablesFold "asd" (List.concat [
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];        
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ]
                                   ]) in
  (* nApp k (List.concat [l]; sty_terms ks; sty_terms ls; [xi]; [zeta]; sty_terms xis; sty_terms zetas]). *)
  x.

Definition testGenShort (_: unit) :=
  (* let '(_, k, l, ks, ls, xi, zeta, xis, zetas) := genVariablesFold "asd" tt [ scopeVar K; scopeVar L; scopeVars KS; scopeVars LS; renVar (XI K L); renVar (ZETA K L); renVars (XIS KS LS); renVars (ZETAS KS LS) ] in *)
  let x := genVariablesShort "asd" (List.concat [
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];        
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ];         
                                   [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ]
                                   ]) in
  (* nApp k (List.concat [l]; sty_terms ks; sty_terms ls; [xi]; [zeta]; sty_terms xis; sty_terms zetas]). *)
  x.

Time Compute testGen tt.
(* this is a bit faster since I switched to a definition with fix in testGenFold
 * TODO is fix generally faster than Fixpoint? *)
Time Compute testGenFold tt.
Time Compute testGenShort tt.

Compute genVariableShapesShort [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ].

(* DONE now it finally works.  *)
Definition genTestMatchShort (_: unit) : nterm :=
  let '(k, l, ks, ls, xi, zeta, xis, zetas, bs) :=
      genVariablesShort "asd" [ K; L; KS; LS; XI K L; ZETA K L; XIS KS LS; ZETAS KS LS ] in
  nApp k (List.concat [ [l]; sty_terms ks; sty_terms ls; [xi]; [zeta]; sty_terms xis; sty_terms zetas]).

Time Compute genTestMatchShort tt.

(* From ASUB Require NEList. *)
(* #[ local ] *)
(*  Notation "[~ z ; x ; .. ; y ~]" := (z, (CONS x .. (CONS y nil) .. )). *)

