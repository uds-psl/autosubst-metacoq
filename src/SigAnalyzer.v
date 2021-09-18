Require Import List String.
Import ListNotations.
#[ local ]
 Open Scope string.

From ASUB Require Import Language Graph AssocList Monad Utils ErrorM.
From ASUB Require NEList.
Import ErrorM.Notations ErrorM.

Module G := Digraph.

(** * Build a graph where the vertices are all the sorts from the spec and there
 ** * is an edge u->v iff v occurs directly in u (i.e. if there is some constructor
 ** * of u where v is an argument head. ) *)
Definition build_graph (spec: Spec) :=
  SFMap.fold (fun sort ctors g0 =>
                let args := flat_map getArgs ctors in
                fold_left (fun g1 arg => G.add_edge g1 sort arg)
                          args g0)
             spec G.empty.


Definition binder_analysis (spec: Spec) (occurs_in: G.vertex -> G.vertex -> bool) : ErrorM.t SSet.t :=
  SFMap.fold (fun sort ctors mbs0 =>
                let positions := flat_map con_positions ctors in
                fold_left (fun mbs1 '{| pos_binders := pos_binders; pos_head := pos_head |} =>
                             let binders := flat_map getBinders pos_binders in
                             fold_left (fun mbs2 bound_sort =>
                                          bs <- mbs2;;
                                          let vacuous := list_nonef (fun arg => occurs_in arg bound_sort) (getArgSorts pos_head) in
                                          if vacuous
                                          then error "vacuous!"
                                          else pure (SSet.add bs bound_sort))
                                       binders mbs1
                          )
                          positions mbs0)
             spec (ErrorM.pure SSet.empty).


(** * A sort needs renamings
 ** * either if it appears in a constructor in the same component
 ** * or if it occurs in a sort that needs renamings *)
Definition renaming_analysis (spec: Spec) (g_trans: G.t) (components: list (NEList.t tId)) : SSet.t :=
  let renamings := SSet.empty in
  (* add all sorts to the set that appear in their component *)
  let renamings := fold_left (fun ren0 (component: NEList.t tId) =>
                                let boundSorts := getBoundSorts spec component in
                                let has_bound := NEList.anyf (fun sort => list_mem sort boundSorts) component in
                                if has_bound
                                then SSet.union ren0 (SSet.fromList (NEList.to_list component))
                                else ren0)
                             components renamings in
  (* then go through all sorts and add those that occur in sorts already in the set *)
  let renamings := G.fold g_trans (fun sort adj ren0 =>
                                     if SSet.mem ren0 sort 
                                     then SSet.union ren0 adj
                                     else ren0)
                          renamings in
  renamings.
                   

(** * The substitution vector of a sort consist of the open sorts that occur in it. *)
Definition subordination (g: G.t) (canonical_order: list tId) (open_sorts: SSet.t) : tId -> list tId :=
  fun sort => filter (fun subst_sort =>
                     (SSet.mem open_sorts subst_sort
                      && G.mem_edge g sort subst_sort)%bool)
                  canonical_order.

(** Calculate the strongly connected components *)
(* TODO using a hack here to convert the non-empty list to a normal list temporarily
 * but it should be possible to implement the sorting if if I have a proof that the canonical_order list contains all sorts. (maybe even declare a finite string type indexed by this canonical_order) *)
(** We also filter out the non-definable sorts *)
Definition topological_sort g (open_sorts : SSet.t) (spec: Spec) (canonical_order: list tId) : list (NEList.t tId) :=
  list_filter_map (fun component =>
                     let componentL := NEList.to_list component in
                     let componentL := List.filter (fun sort =>
                                                      orb (SSet.mem open_sorts sort)
                                                          (match SFMap.find spec sort with
                                                           | None => false
                                                           | Some l => negb (list_empty l)
                                                           end)
                                                   ) componentL in
                     let componentOrdered := list_intersection canonical_order componentL in
                     NEList.from_list componentOrdered) (G.scc_list g).

Definition build_signature (componentsO: option (list (NEList.t tId))) (canonical_order: list tId) (spec: Spec) : ErrorM.t Signature :=
  let g := build_graph spec in
  open_sorts <- binder_analysis spec (G.mem_edge (G.transitive_closure g false));;
  let substs := subordination (G.transitive_closure g true) canonical_order open_sorts in
  let subst_of := SFMap.mapi (fun sort _ => substs sort) spec in
  let components := match componentsO with None => topological_sort g open_sorts spec canonical_order | Some c => c end in
  let arguments := SFMap.mapi (fun sort _ => match G.succ g sort with None => [] | Some x => x end) spec in
  (* let arguments := SFMap.fromList (map (fun '(sort, _) => (sort, match G.succ g sort with None => [] | Some x => x end)) (SFMap.elements spec)) in *)
  let renamings := renaming_analysis spec (G.transitive_closure g false) components in
  pure {| sigSpec := spec;
          sigSubstOf := subst_of;
          sigComponents := components;
          sigIsOpen := open_sorts;
          sigArguments := arguments;
          sigRenamings := renamings
       |}.


Module Ex.
  Definition spec := Hsig_example.mySigSpec.
  Definition g := build_graph spec.
  Open Scope string.

  Compute g.
  Compute (G.invert g).

  (* test occurs_in relation *)
  Compute bool_beq (G.mem_edge g "ty" "ty") true.
  Compute bool_beq (G.mem_edge g "ty" "tm") false.
  Compute bool_beq (G.mem_edge g "ty" "vl") false.
  Compute bool_beq (G.mem_edge g "tm" "ty") true.
  Compute bool_beq (G.mem_edge g "tm" "tm") true.
  Compute bool_beq (G.mem_edge g "tm" "vl") true.
  Compute bool_beq (G.mem_edge g "vl" "ty") true.
  Compute bool_beq (G.mem_edge g "vl" "tm") true.
  Compute bool_beq (G.mem_edge g "vl" "vl") false.

  (* test open sorts *)
  Definition open_sorts := (match run (binder_analysis spec (G.mem_edge (G.transitive_closure g false))) tt tt with
                            | inl _ => SSet.empty
                            | inr (_, _, x) => x
                            end).
  Compute open_sorts.

  Definition substs := subordination (G.transitive_closure g true) ["ty"; "tm"; "vl"] open_sorts.
  (* While it does not diverge it takes a very long time to compute. This and the trouble with the actually diverging function call above indicates that I should write my own finmaps *)
  Compute (SFMap.mapi (fun sort _ => substs sort) spec).
  (* Compute (SFMap.fromList (map (fun '(sort, _) => (sort, substs sort)) (SFMap.elements spec))). *)

  Compute (run (build_signature (Some [("ty", []); ("tm", ["vl"])]) ["ty"; "tm"; "vl"] spec) tt tt).
  Compute (run (build_signature None ["ty"; "tm"; "vl"] spec) tt tt).
  Compute (G.succ g "ty").
  Compute (G.succ g "tm").
  Compute (G.succ g "vl").

  Definition components := [("tm", ["vl"]); ("ty", [])].
  Compute (renaming_analysis spec (G.transitive_closure (G.invert g) false) components).

End Ex.

Module Ex2.
  Definition spec := Hsig_fol.mySigSpec.
  Definition g := build_graph spec.
  Open Scope string.

  Compute g.

  Definition open_sorts := (match run (binder_analysis spec (G.mem_edge (G.transitive_closure g false))) tt tt with
                            | inl _ => SSet.empty
                            | inr (_, _, x) => x
                            end).
  Compute open_sorts.
  Definition components : list (NEList.t tId) := [("form", []); ("term", [])].
  (* as expected this is the empty list *)
  Compute (renaming_analysis spec (G.transitive_closure (G.invert g) false) components).

  Compute (run (build_signature None ["term"; "form"] spec) tt tt).
End Ex2.
