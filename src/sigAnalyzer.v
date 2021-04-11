From ASUB Require Import hsig graph AL monad util.
Require Import List String.
Import ListNotations.
Open Scope string.

Module G := Digraph.
Import E.Notations E.

(** Build a graph where the vertices are all the sort from the spec and there
 ** is an edge u->v if v occurs directly in u (i.e. if there is some constructor
 ** of u where v is an argument head. ) *)
Definition build_graph (spec: Spec) :=
  SFMap.fold (fun sort ctors g0 =>
            let args := flat_map getArgs ctors in
            fold_left (fun g1 arg => G.add_edge g1 sort arg)
                      args g0)
         spec G.empty.


Definition binder_analysis (spec: Spec) (occurs_in: G.vertex -> G.vertex -> bool) : E.t SSet.t :=
  SFMap.fold (fun sort ctors mbs0 =>
            let positions := flat_map con_positions ctors in
            fold_left (fun mbs1 '{| pos_binders := pos_binders; pos_head := pos_head |} =>
                         let binders := flat_map getBinders pos_binders in
                         fold_left (fun mbs2 bound_sort =>
                                      bs <- mbs2;;
                                      let vacuous := list_none (fun arg => occurs_in arg bound_sort) (getArgSorts pos_head) in
                                      if vacuous
                                      then error "vacuous!"
                                      else pure (SSet.add bound_sort bs))
                                   binders mbs1
                      )
                      positions mbs0)
         spec (pure SSet.empty).

Definition subordination (g: G.t) (canonical_order: list tId) (open_sorts: SSet.t) : tId -> list tId :=
  fun sort => filter (fun subst_sort =>
                     (SSet.mem subst_sort open_sorts
                     && G.mem_edge g sort subst_sort)%bool)
                  canonical_order.

Definition topological_sort g canonical_order : list (list tId) :=
  map (fun component => list_intersection canonical_order (NEList.to_list component)) (G.scc_list g).

Definition build_signature (componentsO: option (list (list tId))) (canonical_order: list tId) (spec: Spec) : E.t Signature :=
  let g := build_graph spec in
  open_sorts <- binder_analysis spec (G.mem_edge (G.transitive_closure g false));;
  let substs := subordination (G.transitive_closure g true) canonical_order open_sorts in
  let subst_of := SFMap.mapi (fun sort _ => substs sort) spec in
  let components := match componentsO with None => topological_sort g canonical_order | Some c => c end in
  let arguments := SFMap.mapi (fun sort _ => match G.succ g sort with None => [] | Some x => x end) spec in
  (* let arguments := SFMap.fromList (map (fun '(sort, _) => (sort, match G.succ g sort with None => [] | Some x => x end)) (SFMap.elements spec)) in *)
  pure {| sigSpec := spec;
         sigSubstOf := subst_of;
         sigComponents := components;
         sigIsOpen := open_sorts;
         sigArguments := arguments
      |}.



Module Ex.
  Definition spec := Hsig_example.mySigSpec.
  Definition g := build_graph spec.
  Open Scope string.

  (* test occurs_in relation *)
  Compute (G.mem_edge g "ty" "ty").
  Compute (G.mem_edge g "ty" "tm").
  Compute (G.mem_edge g "ty" "vl").
  Compute (G.mem_edge g "tm" "ty").
  Compute (G.mem_edge g "tm" "tm").
  Compute (G.mem_edge g "tm" "vl").
  Compute (G.mem_edge g "vl" "ty").
  Compute (G.mem_edge g "vl" "tm").
  Compute (G.mem_edge g "vl" "vl").

  (* test open sorts *)
  Definition open_sorts := (match E.run (binder_analysis spec (G.mem_edge (G.transitive_closure g false))) tt tt with
                            | inl _ => SSet.empty
                            | inr (_, _, x) => x
                            end).
  Compute open_sorts.

  Definition substs := subordination (G.transitive_closure g true) ["ty"; "tm"; "vl"] open_sorts.
  (* While it does not diverge it takes a very long time to compute. This and the trouble with the actually diverging function call above indicates that I should write my own finmaps *)
  Compute (SFMap.mapi (fun sort _ => substs sort) spec).
  (* Compute (SFMap.fromList (map (fun '(sort, _) => (sort, substs sort)) (SFMap.elements spec))). *)

  Compute (E.run (build_signature (Some [["ty"]; ["tm"; "vl"]]) ["ty"; "tm"; "vl"] spec) tt tt).
  Compute (E.run (build_signature None ["ty"; "tm"; "vl"] spec) tt tt).
  Compute (G.succ g "ty").
End Ex. 
