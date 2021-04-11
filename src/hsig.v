(* Here I define the spec like that holds all the data for the code we want to generate *)
Require Import String List.
Import ListNotations.
From ASUB Require Import AL util.


Notation tId := string.
Notation vId := string.
Notation fId := string.
Notation cId := string.

Inductive Binder :=
| Single : tId -> Binder
| BinderList : string -> tId -> Binder.

(* no funapp until I know how to deal with arguments *)
Inductive ArgumentHead :=
| Atom : tId -> ArgumentHead.
(* | FunApp : fId -> (* ast term option *) list ArgumentHead -> ArgumentHead. *)

Definition getBinders b :=
  match b with
  | Single x => [x]
  | BinderList _ x => [x]
  end.

(* a.d. todo recursion! *)
Definition getArgSorts a :=
  match a with
  | Atom x => [x]
  (* | FunApp _ xs => flat_map getArgSorts xs *)
  end.

Set Primitive Projections.
Record Position := { pos_binders : list Binder;
                     pos_head : ArgumentHead }.
Record Constructor := { con_parameters : list (string * tId);
                        con_name : cId;
                        con_positions : list Position }.
Unset Primitive Projections.

Definition getArgs c :=
  flat_map (fun p => getArgSorts p.(pos_head)) c.(con_positions).

Notation tIdMap elt := (SFMap.t elt).
Definition Spec := tIdMap (list Constructor).

Record Signature := { sigSpec : Spec;
                      sigSubstOf : tIdMap (list tId);
                      sigComponents : list (list tId);
                      sigIsOpen : SSet.t;
                      sigArguments: tIdMap (list tId);
                    }.

Definition t := Signature.

Scheme Equality for string.
Scheme Equality for Binder.
Scheme Equality for ArgumentHead.
(* a.d. TODO, scheme equality issues im bugtracker, ggf neues Issue *)
(* Scheme Equality for Position. *)

Notation eq_dec A := (forall x y:A, { x = y } + { x <> y }).
Lemma Position_eq_dec : eq_dec Position.
Proof.
  repeat (decide equality).
Qed.


Lemma Constructor_eq_dec : eq_dec Constructor.
Proof.
  repeat (decide equality).
Qed.


Module Hsig_example.
  #[ local ]
   Open Scope string.
  
  Definition mySigSpec : Spec := SFMap.fromList
                                   [ ("vl", [ {| con_parameters := [];
                                                 con_name := "lam";
                                                 con_positions := [ {| pos_binders := []; pos_head := Atom "ty" |}
                                                                 ; {| pos_binders := [ Single "vl" ]; pos_head := Atom "tm" |} ] |}
                                              ; {| con_parameters := [];
                                                   con_name := "tlam";
                                                   con_positions := [ {| pos_binders := [ Single "ty" ]; pos_head := Atom "tm" |} ] |} ])
                                     ; ("tm", [ {| con_parameters := [];
                                                   con_name := "app";
                                                   con_positions := [ {| pos_binders := []; pos_head := Atom "tm" |}
                                                                   ; {| pos_binders := []; pos_head := Atom "tm" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "tapp";
                                                     con_positions := [ {| pos_binders := []; pos_head := Atom "tm" |}
                                                                     ; {| pos_binders := []; pos_head := Atom "ty" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "vt";
                                                     con_positions := [ {| pos_binders := []; pos_head := Atom "vl" |} ] |} ])
                                     ; ("ty", [ {| con_parameters := [];
                                                   con_name := "arr";
                                                   con_positions := [ {| pos_binders := []; pos_head := Atom "ty" |}
                                                                   ; {| pos_binders := []; pos_head := Atom "ty" |} ] |}
                                                ; {| con_parameters := [];
                                                     con_name := "all";
                                                     con_positions := [ {| pos_binders := [ Single "ty" ]; pos_head := Atom "ty" |} ] |} ]) ].

  (* Compute M.find "ty"%string (M.empty _). *)
  (* Compute M.find "ty"%string mySigSpec. *)

  Definition mySig : Signature := {|
    sigSpec := mySigSpec;
    sigSubstOf := SFMap.fromList [ ("tm", ["ty"; "vl"])
                                ; ("ty", ["ty"])
                                ; ("vl", ["ty"; "vl"]) ];
    sigComponents := [ [ "ty" ]; [ "tm"; "vl" ] ];
    sigIsOpen := SSet.add "ty" (SSet.add "vl" SSet.empty);
    sigArguments := SFMap.fromList [ ("tm", [ "tm"; "ty"; "vl" ])
                                  ; ("ty", [ "ty" ])
                                  ; ("vl", [ "ty"; "tm" ]) ];
    |}.
End Hsig_example.


