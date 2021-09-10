Require Import String List.
Open Scope string.

From MetaCoq.Template Require Import All.
Import MonadNotation.

From ASUB Require Import TemplateMonadUtils fintype.

(* TODO in Termutil.scoped_arity we compute the universe constraints for an inductive type that uses "fin".
 * Is there any way we can compute the implicit universes created by fin? Atm we have a hardcoded string. *)

Definition locate_mind' (name: string) : TemplateMonad mutual_inductive_body :=
  loc <- tmLocate1 name;;
  match loc with
  | IndRef ind =>
    body <- tmQuoteInductive ind.(inductive_mind);;
    tmReturn body
  | _ => tmFail (String.append "unknown name or name is not an inductive: " name)
  end.

From ASUB Require Import fintype.
Inductive tm (n m:nat) :=
| var_tm : fin n -> tm n m
| app : tm n m -> tm n m -> tm n m.

MetaCoq Run (locate_mind "tm" >>= tmPrint).
MetaCoq Run (locate_mind' "tm" >>= tmPrint).

Module m.
  Definition mytm :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params :=
    [{|
       decl_name := {| binder_name := nNamed "n"%string; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tInd
           {|
             inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
             inductive_ind := 0
           |} []
     |}];
  mind_entry_inds :=
    [{|
       mind_entry_typename := "tm"%string;
       mind_entry_arity := 
         (* this computes the commented out thing below *)
         tSort
              (Universe.from_kernel_repr (Level.lSet, false)
                 [(Level.Level "ASUB.src.static.fintype.9", false)]);
         (* tSort *)
         (*   {| *)
         (*     Universe.t_set := *)
         (*       {| *)
         (*         UnivExprSet.this := [(Level.lSet, 0); (Level.Level "ASUB.src.static.fintype.9", 0)]; *)
         (*         UnivExprSet.is_ok := *)
         (*           UnivExprSet.Raw.add_ok (s:=[(Level.lSet, 0)]) (Level.Level "ASUB.src.static.fintype.9", 0) *)
         (*             (UnivExprSet.Raw.singleton_ok (Level.lSet, 0)) *)
         (*       |}; *)
         (*     Universe.t_ne := *)
         (*       Universes.Universe.add_obligation_1 (Level.Level "ASUB.src.static.fintype.9", 0) *)
         (*         {| *)
         (*           Universe.t_set := *)
         (*             {| *)
         (*               UnivExprSet.this := [(Level.lSet, 0)]; *)
         (*               UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok (Level.lSet, 0) *)
         (*             |}; *)
         (*           Universe.t_ne := eq_refl *)
         (*         |} *)
         (*   |}; *)
       mind_entry_consnames := ["var_tm"%string; "app"%string];
       mind_entry_lc :=
         [tProd {| binder_name := nAnon; binder_relevance := Relevant |}
            (tApp
               (tConst (MPfile ["fintype"%string; "static"%string; "src"%string; "ASUB"%string], "fin"%string)
                  []) [tRel 0]) (tApp (tRel 2) [tRel 1]);
         tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp (tRel 1) [tRel 0])
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp (tRel 2) [tRel 1])
              (tApp (tRel 3) [tRel 2]))]
     |}];
  mind_entry_universes :=
    Monomorphic_entry
      ({| VSet.this := []; VSet.is_ok := LevelSet.Raw.empty_ok |},
      {| CS.this := []; CS.is_ok := ConstraintSet.Raw.empty_ok |});
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None
|}.

  MetaCoq Run (tmMkInductive mytm).

  MetaCoq Run (tmLocate1 "fin" >>= tmPrint).

Search global_decl.
Search UnivExprSet.t.
Search UnivExpr.t.
Search Universe.t0.
Search Universe.t.


(*
  TODO how to get to Universe.t?

 univExpr.get_level : UnivExpr.t -> Level.t
 Universe.from_kernel_repr : Level.t -> Universe.t
 *)

  Compute 
(tSort
              (Universe.from_kernel_repr (Level.lSet, true)
                 [(Level.Level "ASUB.src.static.fintype.9", false)])).

  Compute 
(tSort
              (Universe.from_kernel_repr (Level.lSet, false)
                 [(Level.Level "ASUB.src.static.fintype.9", false)])).

