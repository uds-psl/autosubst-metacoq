(* tldr the finmap module from the coq stdlib constructs very large terms that will crash coq if you don't fully evaluate something like a G.mem_edge *)
From ASUB Require Import hsig AL sigAnalyzer.
Module diverge.
  From MetaCoq.Template Require Import All.
  Import MonadNotation.
  Inductive Id {A:Type} := IdC : A -> Id.
  Require Import Arith List String.
  Open Scope string.
  Import ListNotations.

  Definition mySigSpec : Spec := SFMap.fromList
                                   [  ("ty", [ {| con_parameters := [];
                                                   con_name := "arr";
                                                   con_positions := [ {| pos_binders := []; pos_head := Atom "ty" |}
                                                                   ; {| pos_binders := []; pos_head := Atom "ty" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "all";
                                                     con_positions := [ {| pos_binders := [ Single "ty" ]; pos_head := Atom "ty" |} ] |} ]) 

  (* Definition mySigSpec2 : Spec := SFMap.fromList *)
                                   ;  ("tm", [ {| con_parameters := [];
                                                   con_name := "app";
                                                   con_positions := [ {| pos_binders := []; pos_head := Atom "tm" |}
                                                                   ; {| pos_binders := []; pos_head := Atom "tm" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "tapp";
                                                     con_positions := [ {| pos_binders := []; pos_head := Atom "tm" |}
                                                                     ; {| pos_binders := []; pos_head := Atom "tm" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "vt";
                                                     con_positions := [ {| pos_binders := []; pos_head := Atom "tm" |} ] |} ])
                                      ].
  Definition diverge :=
    (* Minimum working example for diverging behaviour so far.
     * Build graph, then check if edge exists two times while one expression is packed in some inductive type
     * WTF is happening here?
     * Feels like somehow state is handled wrongly since it works when I use a "fresh" copy of the graph for the second call to mem_edge *)
    let spec := mySigSpec in
    let g := build_graph spec in
    (* let g' := build_graph spec in *)
    let x1 := if G.mem_edge g "ty" "ty" then IdC (G.mem_edge g "ty" "ty") else IdC true in
    (* let x1 := if Nat.eq_dec 100 100 then IdC (if Nat.eq_dec 100000 100000 then true else false) else IdC false in *)
    (* let x1 := if Nat.eq_dec 100 100 then IdC (if G.mem_edge g "ty" "ty" then true else false) else IdC false in *)
    (* let x1 := if G.mem_edge g "ty" "ty" then IdC (if Nat.eq_dec 100000 100000 then true else false) else IdC false in *)
    (* let x1 := if Nat.eq_dec (1000 * 1000) (1000 * 1000) then IdC (if Nat.eq_dec 10 10 then true else false) else IdC false in *)
    (* let x1 := if G.mem_edge g "ty" "ty" then IdC (if G.mem_edge g "ty" "ty" then true else false) else IdC true in *)
    (* let x1 := if G.mem_edge g "vl" "vl" then IdC (g) else IdC g in *)
    (* Yannick: sollte man immer mal wieder tmeval all machen? *)
    (* x2 <- tmEval all x1;; *)
    match x1 with
    | IdC x => tmReturn x
    end.

  (* Compute (build_graph Hsig_example.mySigSpec). *)
  MetaCoq Run (diverge >>= tmPrint).
  (* Coq intern mehrere evaluationstrategien
   * man kann anscheinend auch in Coq die evaluation erzwingen, phne die TemplateMonade
   *)
End diverge.
