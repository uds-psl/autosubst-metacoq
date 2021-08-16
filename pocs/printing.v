(* Does MetaCoq already have facilities to pretty-print terms? *)
From MetaCoq.Template Require Import All Pretty.
Import String List.
Import ListNotations.

Check print_term.

Definition foo := <% forall X:Type, X -> X %>.
Print foo.

(* yes it's possible. But it seems that if I want to use things from the environment like "eq" I need to set up the environment which is cumbersome *)
Compute print_term ([], Monomorphic_ctx (LevelSet.Mkt [], ConstraintSet.Mkt [])) [] false foo.


Definition bar := <% 0 = 0 %>.
Compute print_term ([], Monomorphic_ctx (LevelSet.Mkt [], ConstraintSet.Mkt [])) [] false bar.



