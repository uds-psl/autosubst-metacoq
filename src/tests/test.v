From Coq Require Import String List.
From MetaCoq.Template Require Import All.
MetaCoq Quote Definition nat_q := @eq.

Require Import FunctionalExtensionality.
Goal forall (x y: nat), x = y -> (fun z => z + x) = (fun z => z + y).
Proof.
  intros * H.
  rewrite H.
  reflexivity.
Qed.

Import ListNotations.
Definition bAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Goal True.
  evar (n : nat).
  match goal with
    H := ?t |- _ => quote_term t (fun x => pose (qn:=x))
  end.
  match goal with
    qn := Ast.tEvar _ nil |- _ => idtac
  end.
  exact I.
  Unshelve. exact 0.
Qed.

(** Evars *)
MetaCoq Quote Definition lnil := @nil.
MetaCoq Quote Definition listnat := (list nat).
MetaCoq Quote Definition eq_q := @eq.
MetaCoq Quote Definition zero_q := 0.
MetaCoq Unquote Definition foo := (tCast (tApp lnil [hole]) Cast listnat).

Local Open Scope string_scope.

Goal list nat.
  (* Back and forth *)
  (* Set Printing All. *)
  let x := idtac in idtac x.
  let x := open_constr:(cons 0 []) in quote_term x (fun qt =>
    ltac:(idtac qt; (denote_term qt (fun unqt => idtac unqt; (set (e := eq_refl : unqt = x :> list _));
                                    idtac unqt; idtac x));
          idtac 0)).
    (* Creation of evars by denotation of 'hole' *)
  Unset Printing Notations.
  Set Printing All.
  let x := eval cbv in (tApp lnil [hole]) in
  denote_term x (fun k => idtac k; exact k).
Defined.

Lemma bla: Prop.
  let x := constr:(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) [tEvar fresh_evar_id []; (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0 []); (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0 [])])
  in idtac x; (denote_term x (fun unqt => idtac unqt; 
                                       idtac x; exact unqt)).
  
  Unshelve.
  (* the second seems to be the evar that is placed in eq but why do I even get the first? *)
  exact Type. exact nat.
Defined.

(* ok so it does not really work above since I always get the shelved evars which I have to explicitly instantiate and below does not work either so I don't pursue this further. It would be an ugly hack anyways.

 foo2 uses an Gallina-let and when I use x as an argument to denote_term it does not seem to reduce it (different semantics to ltac-let) which means that denote_term just sees x. No idea how to reduce it though *)
Fail Definition foo2 : term :=
  let x := (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) [tEvar fresh_evar_id []; (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0 []); (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0 [])])
  in ltac:(denote_term x (fun unqt => idtac unqt; 
                                    idtac unqt; exact unqt)).
    
Goal True.
  let x := eval cbv in (tLambda bAnon listnat hole) in
  (* We check that created evars are in the right context *)
  denote_term x (fun k => set (ev := k); revert ev).
  instantiate (1 := list nat).
  instantiate (1 := l).
  exact I.
Qed.


