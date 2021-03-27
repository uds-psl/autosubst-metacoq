
(* From ASUB Require Import core. *)

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
    (* eq_refl_q <- tmQuote Logic.eq_refl;; *)
    (* typ <- tmUnquote (Ast.tApp eq_q [one_q; one_q]);; *)
    (* typ' <- tmEval lazy (typ.(my_projT2));; *)
    (* a.d. todo, we can't explicitly give types to our definitions? *)
    obj <- tmDefinitionRed "oneisone_q" (Some lazy) (@Logic.eq_refl _ 1);;
    tmReturn tt.
                 
  MetaCoq Run oneisonetest.
  Check oneisone_q.

  MetaCoq Quote Definition eq_refl_q := @Coq.Init.Logic.eq_refl.

  (* Same definition but with a term unquoted by MetaCoq *)
  Definition oneisonetest2 : TemplateMonad unit :=
    one_q <- tmQuote 1;;
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

  (* this fails when I use hole instead of nat because MetaCoq apparently cannot unquote evars? *)
  Definition oneisonetest3 : TemplateMonad unit :=
    one_q <- tmQuote 1;;
    nat_q <- tmQuote nat;;
    (* tm <- tmUnquote (Ast.tApp eq_refl_q [Ast.hole; one_q]);; *)
    tm <- tmUnquote (Ast.tApp eq_refl_q [nat_q; one_q]);;
    tm <- tmEval lazy (my_projT2 tm);;
    obj <- tmDefinitionRed "oneisone_q3" (Some lazy) tm;;
    tmReturn tt.

  MetaCoq Run oneisonetest3.
  Check oneisone_q3.
  
  MetaCoq Quote Definition tru := True.
  MetaCoq Quote Definition i := I.

  Set Printing All.
  Fail Definition oneisonetest3 : TemplateMonad unit :=
  (@bind TemplateMonad TemplateMonad_Monad typed_term unit (tmUnquote tru)
     (fun typ : typed_term =>
      @bind TemplateMonad TemplateMonad_Monad (my_projT1 typ) unit (@tmEval all (my_projT1 typ) (my_projT2 typ))
        (fun typ0 : (my_projT1 typ) =>
         @bind TemplateMonad TemplateMonad_Monad typed_term unit (tmUnquote i)
           (fun proof : typed_term =>
            @bind TemplateMonad TemplateMonad_Monad (my_projT1 proof) unit
              (@tmEval all (my_projT1 proof) (my_projT2 proof))
              (fun proof0 : (my_projT1 proof) =>
               @bind TemplateMonad TemplateMonad_Monad (my_projT1 typ) unit
                 (@tmDefinitionRed "oneisone4" (Some lazy) typ0 proof0)
                 (fun _ : _ => @tmReturn unit tt)))))).
                 
  Definition oneisonetest4 : TemplateMonad unit :=
    proof <- tmUnquote i;;
    t <- tmEval lazy (my_projT1 proof);;
    t' <- tmEval lazy (my_projT2 proof);;
    tmPrint t;;
    tmPrint t';;
    tmReturn tt.

  MetaCoq Run oneisonetest4.

  (* a.d. todo, quote definition with implicits *)
  Definition myid {A:Type} (a:A) := a.
  Fail MetaCoq Quote Definition myid_source := Eval compute in myid.
  (* Print myid_source. *)

