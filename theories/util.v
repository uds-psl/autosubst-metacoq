
From MetaCoq.Template Require Import utils All.

Fixpoint mkArr t1 ts2 :=
  match ts2 with
  | [] => t1
  | t2 :: ts2 => tProd {| binder_name := BasicAst.nAnon; binder_relevance := BasicAst.Relevant |}
                     t1
                     (mkArr t2 ts2)
  end.
