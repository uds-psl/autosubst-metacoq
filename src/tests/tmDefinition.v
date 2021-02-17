
From ASUB Require Import core.
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

  Definition oneisonetest : TemplateMonad unit :=
    (* one_q <- tmQuote 1;; *)
    (* eq_q <- tmQuote eq;; *)
    (* eq_refl_q <- tmQuote Logic.eq_refl;; *)
    (* typ <- tmUnquote (Ast.tApp eq_q [one_q; one_q]);; *)
    (* typ' <- tmEval lazy (typ.(my_projT2));; *)
    obj <- tmDefinitionRed "oneisone2" (Some lazy) (@Logic.eq_refl _ 1);;
    tmReturn tt.
                 
  MetaCoq Run oneisonetest.
  Check oneisone2.

  MetaCoq Quote Definition eq_refl_q := eq_refl.
  
  Definition oneisonetest2 : TemplateMonad unit :=
    one_q <- tmQuote 1;;
    (* tm <- tmUnquote (Ast.tApp eq_refl_q [Ast.hole; one_q]);; *)
    tm <- tmUnquote eq_refl_q;;
    tm <- tmEval lazy (tm.(my_projT2));;
    tmPrint tm;;
    obj <- tmDefinitionRed "oneisone3" (Some lazy) tm;;
    tmReturn tt.
                 
  MetaCoq Run oneisonetest2.
  Check oneisone3.
  
  MetaCoq Quote Definition tru := True.
  MetaCoq Quote Definition i := I.

  Set Printing All.
  Fail Definition oneisonetest3 : TemplateMonad unit :=
  (@bind TemplateMonad TemplateMonad_Monad typed_term unit (tmUnquote tru)
     (fun typ : typed_term =>
      @bind TemplateMonad TemplateMonad_Monad (my_projT1 typ) unit (@tmEval lazy (my_projT1 typ) (my_projT2 typ))
        (fun typ0 : (my_projT1 typ) =>
         @bind TemplateMonad TemplateMonad_Monad typed_term unit (tmUnquote i)
           (fun proof : typed_term =>
            @bind TemplateMonad TemplateMonad_Monad (my_projT1 proof) unit
              (@tmEval lazy (my_projT1 proof) (my_projT2 proof))
              (fun proof0 : (my_projT1 proof) =>
               @bind TemplateMonad TemplateMonad_Monad (my_projT1 typ) unit
                 (@tmDefinitionRed "oneisone4" (Some lazy) typ0 proof0)
                 (fun _ : _ => @tmReturn unit tt)))))).
                 
  Definition oneisonetest3 : TemplateMonad unit :=
    proof <- tmUnquote i;;
    t <- tmEval lazy (my_projT1 proof);;
    t' <- tmEval lazy (my_projT2 proof);;
    tmPrint t;;
    tmPrint t';;
    tmReturn tt.

  MetaCoq Run oneisonetest3.
