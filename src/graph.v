Require Import Structures.OrderedTypeEx List Arith String.
Import ListNotations.
From ASUB Require Import util AL.
Require Import Structures.OrderedTypeEx.
Require FSets.FMapList.


Module Digraph.
  Definition vertex := string.
  Definition edge := (vertex * vertex)%type.
  (* at the moment we only label our trees by their adjancent vertices *)
  Definition elt := SSet.t.
  Definition t := SFMap.t elt.

  Definition adj_In_dec := List.In_dec String_as_OT.eq_dec.

  (* a.d. TODO can we *)
  Definition empty : t := SFMap.empty elt.

  Definition get (g: t) (v: vertex) : option elt := SFMap.find v g.
  Definition succ (g: t) (v: vertex) : option (list vertex) :=
    match get g v with
    | None => None
    | Some vs => Some (SSet.elements vs)
    end.

  Definition add_vertex (g: t) (v: vertex) (adj: SSet.t) : t :=
    match SFMap.find v g with
    | None => SFMap.add v adj g
    (* a.d. DONE, uniquify lists since vertex is dec. But this should not introduce errors.
     It did introduce errors in sigAnalyzer.v when building the argument mapping *)
    | Some adj' => SFMap.add v (SSet.union adj adj') g
    end.

  Definition add_edge (g: t) (v w: vertex) : t :=
    let g0 := add_vertex g v (SSet.singleton w) in
    let g1 := add_vertex g0 w SSet.empty in
    g1.

  Definition mem_edge (g: t) (v w: vertex) : bool :=
    match get g v with
    | None => false
    | Some adj => SSet.mem w adj
    end.

  Definition fold {A: Type} (g: t) (f: vertex -> elt -> A -> A) (state: A) :=
    SFMap.fold f g state.
  Definition fold_vertex {A: Type} (g: t) (f: vertex -> A -> A) (state: A) :=
    SFMap.fold (fun v _ a => f v a) g state.
  
  Definition fold_succ {A: Type} (g: t) (f: vertex -> A -> A) (v: vertex) (init: A) :=
    match succ g v with
    | None => init (* a.d. TODO rather error *)
    | Some adj => fold_left (fun a v => f v a) adj init
    end.

  Definition fold_pred {A: Type} (g: t) (f: vertex -> A -> A) (v: vertex) (init: A) :=
    SFMap.fold (fun v_pred adj a =>
               if SSet.mem v adj
               then (* v_pred is a predecessor of v *)
                 f v_pred a
               else
                 a)
            g init.

  (* like in the ocamlgrpah library. seems to correspond to Roy-Warshall's algorithm *)
  Definition transitive_closure' (refl: bool) (v: vertex) (g: t) :=
    let g0 := if refl then add_edge g v v else g in
    fold_succ g0 (fun v_succ g1 =>
                    fold_pred g1 (fun v_pred g2 => add_edge g2 v_pred v_succ)
                              v g1)
              v g0.
    
  Definition transitive_closure (g: t) (refl: bool) := fold_vertex g (transitive_closure' refl) g.

  Definition scc_list (g: t) :=
    let gt := transitive_closure g false in
    let sccs := fold_vertex gt (fun v sccs =>
                                  let '(added, sccs) :=
                                      fold_left (fun (state: bool * list (NEList.t vertex)) scc =>
                                                   let '(added, sccs) := state in
                                                   if added then (added, sccs ++ [scc])
                                                   else
                                                     let '(scc_head, scc_rest) := scc in
                                                     if andb (mem_edge gt v scc_head) (mem_edge gt scc_head v)
                                                     then (true, sccs ++ [(scc_head, v :: scc_rest)])
                                                     else (false, sccs ++ [scc]))
                                                sccs (false, []) in
                                  if added
                                  then sccs else (v, []) :: sccs)
                     [] in
    sccs.
End Digraph.

Module Ex.
  Module G := Digraph.
  Open Scope string.

  Definition g0 := G.add_edge G.empty "a" "b".
  Definition g := G.add_edge
                    (G.add_edge G.empty
                                "a" "b")
                    "b" "c".
  Definition gt := G.transitive_closure g true.
  
  Compute (G.mem_edge gt "a" "c").
End Ex.

