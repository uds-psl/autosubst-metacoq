
(* From ASUB Require Import core. *)

Definition foo := (fun {A:Type} (x: A) => x).
Compute foo 1.

(* while the above with foo works, below does not.
 So even though we can specify implicit variables in constr_expr, Coq seems to just use this info
 if we are in a Definition. The kernel AST econstr does not carry this information anymore.
 Depending on what tmUnquote does (run_template_monad.ml suggests that it is translated to econstr) we could not even add
 implicit arguments to metacoq lambdas *)
Fail Compute ((fun {A:Type} (x: A) => x) 1).

From MetaCoq.Template Require Import utils All.
Import ListNotations MonadNotation Nat.


Module tests.
  Definition congr_test :=
    tmLemma "congr_arr" True.

  MetaCoq Run congr_test.

  Inductive ty : Type :=
    var_ty : nat -> ty
  | arr : ty -> ty -> ty
  | allt : ty -> ty. 

  Definition congr_test2 : TemplateMonad unit :=
    ty_q <- tmQuote ty ;;
    tm <- tmUnquote (Ast.tLambda {| binder_name := BasicAst.nNamed "s"; binder_relevance := BasicAst.Relevant |} ty_q ty_q);;
    z <- tmEval lazy (tm.(my_projT2));;
    tmDefinitionRed "congr_arr2" (Some lazy) z;;
    tmReturn tt.

  MetaCoq Run congr_test2.

  Definition oneisone : forall X (x:X), x = x := fun _ x => @Logic.eq_refl _ x.

  (* Just a definition triggered by MetaCoq using an original Coq term *)
  Definition oneisonetest : TemplateMonad unit :=
    (* one_q <- tmQuote 1;; *)
    (* eq_q <- tmQuote eq;; *)
    (* typ <- tmUnquote (Ast.tApp eq_q [one_q; one_q]);; *)
    (* typ' <- tmEval lazy (typ.(my_projT2));; *)
    (* a.d. todo, we can't explicitly give types to our definitions? *)
    obj <- tmDefinitionRed "oneisone_q" (Some lazy)  (@Logic.eq_refl _ 1);;
    tmReturn tt.
                 
  MetaCoq Run oneisonetest.
  Check oneisone_q.

  MetaCoq Quote Definition eq_refl_q := @Coq.Init.Logic.eq_refl.

  (* Same definition but with a term unquoted by MetaCoq *)
  Definition oneisonetest2 : TemplateMonad unit :=
    (* one_q <- tmQuote 1;; *)
    (* eq_refl_q <- tmQuote eq_refl;; *)
    (* tm <- tmUnquote (Ast.tApp eq_refl_q [Ast.hole; one_q]);; *)
    tm <- tmUnquote eq_refl_q;;
    tm <- tmEval lazy (tm.(my_projT2));;
    (* tmPrint tm;; *)
    obj <- tmDefinitionRed "oneisone_q2" (Some lazy) tm;;
    tmPrint obj;;
    tmReturn tt.
                 
  MetaCoq Run oneisonetest2.
  Check oneisone_q2.

  (* a.d. todo, why does inference fail when return type is not unit? *)
  Fail Definition oneisonetest3 : TemplateMonad (forall (A:Type) (x :A), x = x) :=
    tm <- tmUnquote eq_refl_q;;
    tm <- tmEval lazy (tm.(my_projT2));;
    obj <- tmDefinitionRed "oneisone_q3" (Some lazy) tm;;
    tmReturn obj.

  MetaCoq Quote Definition zero_q := 0.
  (* this fails when I use hole instead of nat because MetaCoq apparently cannot unquote evars? *)
  Definition oneisonetest3 : TemplateMonad unit.
  Proof.
    refine (
    one_q <- tmQuote 1;;
    nat_q <- tmQuote nat;; _).
    (* a.d. ok so apparently I can use holes when I state beforehand the gallina term to which it should conform. But that is probably not usable in my code. *)
    assert (H: 0 = 0). {
    let x := eval cbv in (Ast.tApp eq_refl_q [Ast.hole; zero_q ]) in
        denote_term x (fun k => exact k).
    }
    refine (
    tm <- tmUnquote (Ast.tApp eq_refl_q [nat_q; one_q]);;
    tm <- tmEval lazy (my_projT2 tm);;
    obj <- tmDefinitionRed "oneisone_q3" (Some lazy) tm;;
    tmReturn tt).
  Defined.

  MetaCoq Run oneisonetest3.
  Check oneisone_q3.
  
  MetaCoq Quote Definition tru := True.
  MetaCoq Quote Definition i := I.

  (* Set Printing All. *)
  (* wenn ich nach dem (fun ty: Type) versuche es in dem bind oder tmEval zu benutzen funktioniert es leider nicht, da statisch keine Verbindung zwischen my_projT1 t und ty existiert. *)
  Definition oneisonetest4 : TemplateMonad unit :=
  (@bind TemplateMonad TemplateMonad_Monad typed_term unit (tmUnquote i)
     (fun t : typed_term =>
      @bind TemplateMonad TemplateMonad_Monad Type unit (@tmEval all Type (my_projT1 t))
            (fun ty : Type =>
             @bind TemplateMonad TemplateMonad_Monad (my_projT1 t) unit (@tmEval all (my_projT1 t) (my_projT2 t))
                   (fun tm : (my_projT1 t) =>
                    @bind TemplateMonad TemplateMonad_Monad (my_projT1 t) unit
                          (@tmDefinitionRed "oneisone4" (Some lazy) (my_projT1 t) tm)
                          (fun _ : _ => @tmReturn unit tt))))).
                 
  MetaCoq Run oneisonetest4.
  Check oneisone4.

  (*** Finally this works. Just use tmUnquoteTyped to assign the type of the proof then we can use the same type in tmDefinition *)
  (* MetaCoq Quote Definition id_q := (fun x:Set => x). *)
  
  Definition oneisonetest5 : TemplateMonad unit :=
    (* let tru' := tApp id_q [tru] in *)
    ty <- tmUnquoteTyped Type tru;;
    proof <- tmUnquoteTyped ty i;;
    @tmDefinitionRed "oneisone5" (Some lazy) ty proof;;
    tmReturn tt.

  MetaCoq Run oneisonetest5.
  Print oneisone5.
  (* Unset Printing All. *)

  Definition oneisonetest6: TemplateMonad unit :=
    proof <- tmUnquote i;;
    ty <- tmEval all (my_projT1 proof);;
    tm <- tmEval all (my_projT2 proof);;
    tmPrint ty;;
    tmPrint (my_projT1 proof);;
    obj <- @tmDefinitionRed "oneisone_q6" (Some (unfold (Common_kn "my_projT1"))) (my_projT1 proof) tm;;
    (* obj <- tmDefinitionRed "oneisone_q6" None tm;; *)
    (* obj <- tmEval all obj;; *)
    tmReturn tt.

  MetaCoq Run oneisonetest6.
  (* Compute (my_projT1 (existT_typed_term True I)). *)
  Check oneisone_q6.

  (* a.d. todo, quote definition with implicits *)
  Definition myid {A:Type} (a:A) := a.
  (* Fail MetaCoq Quote Definition myid_source := Eval compute in myid. *)
  (* Print myid_source. *)

  (* define a fixpoint *)
  Fixpoint add (n m : nat) :=
    match n return _ with
    | O => m
    | S n => S (add n m)
    end.


  MetaCoq Quote Definition add_source := Eval compute in add.
  Print add_source.
  MetaCoq Test Quote add.

  Fixpoint even (n:nat) :=
    match n with
    | O => true
    | S n => odd n
    end
  with odd n :=
    match n with
    | O => false
    | S n => even n
    end.

  Compute even 4.
  Compute even 5.
  Compute odd 4.
  Compute odd 5.

  Inductive foo : nat -> Type :=
  | foo0 : forall n, foo n
  | foo1 : nat -> foo 0.
   Fixpoint bla (n: nat) (d: foo n) :=
    match d with
    | foo0 _ => false
    | foo1 _ => true
    end.

  MetaCoq Test Quote odd.

  MetaCoq Quote Definition even_source := Eval compute in even.
  MetaCoq Quote Definition odd_source := Eval compute in odd.
  MetaCoq Quote Definition bla_source := Eval compute in bla.
  Print even_source.
  (* the second argument to tFix is an index into the list of mutual fixpoint definitions *)
  Print odd_source.
  Print bla_source.

  Definition tmTypedDefinition (lem: string * term * term) : TemplateMonad unit :=
    let '(name, typ_q, t_q) := lem in
    typ <- tmUnquoteTyped Type typ_q;;
    t <- tmUnquoteTyped typ t_q;;
    @tmDefinitionRed name (Some TemplateMonad.Common.all) typ t;;
    tmReturn tt.

  (* ok so I can just use a hole for the type here *)
  MetaCoq Run (tmTypedDefinition ("even2", hole, even_source)).
  MetaCoq Run (tmTypedDefinition ("odd2", hole, odd_source)).

  Compute even2 4.
  Compute even2 5.
  Compute odd2 4.
  Compute odd2 5.



  MetaCoq Quote Definition nat_q := nat.
  
 Definition myfix : term := tFix
  [{|
     dname :=
       {| binder_name := nNamed "myadd"; binder_relevance := Relevant |};
     dtype :=
       tProd
         {| binder_name := nNamed "n"; binder_relevance := Relevant |}
         nat_q
         (tProd
          {| binder_name := nNamed "m"; binder_relevance := Relevant |}
          nat_q
          nat_q);
     dbody :=
       tLambda
         {| binder_name := nNamed "n"; binder_relevance := Relevant |}
         nat_q
         (tLambda
            {| binder_name := nNamed "m"; binder_relevance := Relevant |}
            nat_q
            (tCase
               ({|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0
                 |}, 0, Relevant)
               (tLambda
                  {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                  nat_q
                  nat_q)
               (tRel 1)
               (* the first component of the pair seems to be the number of arguments of the constructor *)
               [(0, (tRel 0));
               (1,
                tLambda
                  {|
                    binder_name := nNamed "n"; binder_relevance := Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} []) (tApp <% S %> [tApp (tRel 3) [tRel 0; tRel 1]]))]));
     rarg := 0
   |}] 0.

 MetaCoq Unquote Definition myfix' := myfix.
 Compute (myfix' 4 5).

 MetaCoq Run (tmUnquoteTyped (list nat) (tApp <% @nil %> [hole]) >>= tmPrint).
 Definition foo2 X (x y:X) := x.

 (* wow so it actually works if we specify the type with tmUnquoteTyped
  * but since we also compute the type for the tmUnquoteTyped call we actually need another tmUnquoteTyped before *)
 MetaCoq Run (
           tmUnquoteTyped Type <% bool %> >>= fun nat_uq =>
           tmUnquoteTyped nat_uq (tApp <% foo2 %> [hole; <% true %>; <% false %>]) >>= tmPrint).
