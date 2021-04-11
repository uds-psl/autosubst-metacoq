Require Import Structures.OrderedTypeEx List Arith String.
Import ListNotations.
From ASUB Require Import util monad.

Module RWSE_params. 
  Definition R := unit.
  Definition W := unit.
  Definition S := unit.
  Definition E := string.

  Definition append := fun (_ _: unit) => tt.
  Definition empty := tt.
End RWSE_params.

Module M := RWSE RWSE_params.
Import M.Notations M.

Require Import Structures.OrderedTypeEx ListDec.
Require FSets.FMapList.



Module Type Digraph_param.
  Parameter (A: Type).
  (* Parameter In_dec : forall (a: A) (la: list (A * list nat)), { In a (map fst la) } + { ~ In a (map fst la) }. *)
  Parameter A_eqb: A -> A -> bool. 
End Digraph_param.

Module Digraph.

  Module FS := FMapList.Make String_as_OT.
  Definition vertex := string.
  Definition edge := (vertex * vertex)%type.
  (* at the moment we only label our trees by their adjancent vertices *)
  Definition elt := list vertex.
  Definition t := FS.t elt.

  Definition adj_In_dec := List.In_dec String_as_OT.eq_dec.

  (* a.d. TODO can we *)
  Definition empty : t := FS.empty elt.

  Definition get (g: t) (v: vertex) : option elt := FS.find v g.
  Definition succ (g: t) (v: vertex) : option (list vertex) := get g v.

  Definition add_vertex (g: t) (v: vertex) (adj: list vertex) : t :=
    match FS.find v g with
    | None => FS.add v adj g
    (* a.d. TODO, uniquify lists since vertex is dec. But this should not introduce errors *)
    | Some adj' => FS.add v (adj ++ adj') g
    end.

  Definition add_edge (g: t) (v w: vertex) : t :=
    let g0 := add_vertex g v [w] in
    let g1 := add_vertex g0 w [] in
    g1.

  Definition mem_edge (g: t) (v w: vertex) : bool :=
    match get g v with
    | None => false
    | Some adj => if adj_In_dec w adj then true else false
    end.

  Definition fold_vertex {A: Type} (g: t) (f: vertex -> A -> A) (init: A) :=
    FS.fold (fun v _ a => f v a) g init.
  
  Definition fold_succ {A: Type} (g: t) (f: vertex -> A -> A) (v: vertex) (init: A) :=
    match succ g v with
    | None => init (* a.d. TODO rather error *)
    | Some adj => fold_left (fun a v => f v a) adj init
    end.

  Definition fold_pred {A: Type} (g: t) (f: vertex -> A -> A) (v: vertex) (init: A) :=
    FS.fold (fun v_pred adj a =>
               if adj_In_dec v adj
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

(* Module Digraph_list (T: Digraph_param). *)
(*   Definition get (g: t) (v: vertex) : option (T.A * list vertex) := nth_error g v. *)

  (* Fixpoint extend_g (n: nat) (a: T.A) (adj: list vertex) := *)
  (*   match n with *)
  (*   | O => [(a, adj)] *)
  (*   | S n => [() *)

  (* Lemma In_nth_error: *)
  (*   forall (A: Type) (l: list A) (x: A), *)
  (*     In x l -> { n | nth_error l n = Some x }. *)
  (* Proof. *)
  (*   intros * H. induction l as [|a l' IH ]. *)
  (*   - destruct H. *)
  (*   - destruct H as [H|H].nth *)

  (* Definition add_vertex_if (g: t) (a: T.A) (adj: list vertex) : M t. *)
  (*   refine (match findi (fun _ '(a', _) => T.A_eqb a a') g with *)
  (*           | None => ret (g ++ [(a, adj)]) *)
  (*           | Some (n, (a', adj')) => _ *)
  (*           end). *)
  (*   clear p p0. *)
  (*   refine ( f) *)
    

  (* Definition add_edge (g: t) (a a': T.A) : t := *)
  (*   let g' := add_vertex g a'  in *)
  (*   let g'' := add_vertex g' w in *)
    
