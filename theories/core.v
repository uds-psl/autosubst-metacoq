(* Here I define the spec like that holds all the data for the code we want to generate *)
Require Import String List.
Import ListNotations.


Notation tId := string.
Notation vId := string.
Notation fId := string.
Notation cId := string.

Inductive Binder :=
| Single : tId -> Binder
| BinderList : string -> tId -> Binder.

Inductive ArgumentHead :=
| Atom : tId -> ArgumentHead
| FunApp : fId -> (* ast term option *) list ArgumentHead -> ArgumentHead.

Definition getBinders b :=
  match b with
  | Single x => [x]
  | BinderList _ x => [x]
  end.

(* a.d. todo recursion! *)
Fixpoint getArgSorts a :=
  match a with
  | Atom x => [x]
  | FunApp _ xs => flat_map getArgSorts xs
  end.

Set Primitive Projections.
Record position := mkPosition
                     { binders : list Binder;
                       head : ArgumentHead }.
Record constructor := mkConstructor
                        { cparameters : list (string * tId);
                          cname : cId;
                          cpositions : list position }.
Unset Primitive Projections.

(* a.d. todo, recursion! *)
Definition getArgs c :=
  flat_map (fun p => getArgSorts p.(head)) c.(cpositions).

From ASUB Require Import AL.

Notation tIdMap elt := (M.t elt).
Definition spec := tIdMap (list constructor).

Record signature := mkSig {
                        sigSpec : spec;
                        sigSubstOf : tIdMap (list tId);
                        sigComponents : list (list tId);
                        sigIsOpen : list tId;
                        sigArguments: tIdMap (list tId);
                      }.

Definition t := signature.

Module Hsig_example.
  #[ local ]
   Open Scope string.
  
  Definition mySigSpec : spec := AL.fromList
                                   [ ("vl", [ {| cparameters := [];
                                                 cname := "lam";
                                                 cpositions := [ {| binders := []; head := Atom "ty" |}
                                                                 ; {| binders := [ Single "vl" ]; head := Atom "tm" |} ] |}
                                              ; {| cparameters := [];
                                                   cname := "tlam";
                                                   cpositions := [ {| binders := [ Single "ty" ]; head := Atom "tm" |} ] |} ])
                                     ; ("tm", [ {| cparameters := [];
                                                   cname := "app";
                                                   cpositions := [ {| binders := []; head := Atom "tm" |}
                                                                   ; {| binders := []; head := Atom "tm" |} ] |}
                                                ; {| cparameters := [];
                                                     cname := "tapp";
                                                     cpositions := [ {| binders := []; head := Atom "tm" |}
                                                                     ; {| binders := []; head := Atom "ty" |} ] |}
                                                ; {| cparameters := [];
                                                     cname := "vt";
                                                     cpositions := [ {| binders := []; head := Atom "vl" |} ] |} ])
                                     ; ("ty", [ {| cparameters := [];
                                                   cname := "arr";
                                                   cpositions := [ {| binders := []; head := Atom "ty" |}
                                                                   ; {| binders := []; head := Atom "ty" |} ] |}
                                                ; {| cparameters := [];
                                                     cname := "all";
                                                     cpositions := [ {| binders := [ Single "ty" ]; head := Atom "ty" |} ] |} ]) ].

  Compute M.find "ty"%string (M.empty _).
  Compute M.find "ty"%string mySigSpec.

  Definition mySig : signature := {|
    sigSpec := mySigSpec;
    sigSubstOf := AL.fromList [ ("tm", ["ty"; "vl"])
                                ; ("ty", ["ty"])
                                ; ("vl", ["ty"; "vl"]) ];
    sigComponents := [ [ "ty" ]; [ "tm"; "vl" ] ];
    sigIsOpen := [ "ty"; "vl" ];
    sigArguments := AL.fromList [ ("tm", [ "tm"; "ty"; "vl" ])
                                  ; ("ty", [ "ty" ])
                                  ; ("vl", [ "ty"; "tm" ]) ];
    |}.
End Hsig_example.


