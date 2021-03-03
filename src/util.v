
Require Import MetaCoq.Template.All.
Require Import List.
Import ListNotations Nat.

Fixpoint mkArr t1 ts2 :=
  match ts2 with
  | [] => t1
  | t2 :: ts2 => tProd {| binder_name := BasicAst.nAnon; binder_relevance := BasicAst.Relevant |}
                     t1
                     (mkArr t2 ts2)
  end.

Fixpoint mkArrRev ts1 t2 :=
  match ts1 with
  | [] => t2
  | t1 :: ts1 => tProd {| binder_name := BasicAst.nAnon;
                        binder_relevance := BasicAst.Relevant |}
                     t1
                     (mkArrRev ts1 t2)
  end.

Definition ref_ name := tVar name. 

Definition sortType sort :=
  (* also take substs as an argument *)
  ref_ sort.

Definition app_ s t := tApp s [t].

Definition appRef_ name t :=
  app_ (ref_ name) t.

Require Import List.
Import ListNotations.

Fixpoint mapi' {A B: Type} (f: nat -> A -> B) (as_: list A) (n: nat): list B :=
  match as_ with
  | [] => []
  | a :: as_ =>
    (f n a) :: (mapi' f as_ (S n))
  end.

Definition mapi {A B: Type} (f: nat -> A -> B) (as_: list A): list B :=
  mapi' f as_ 0.
