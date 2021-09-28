(* Here I define the spec like that holds all the data for the code we want to generate *)
Require Import String List.
Import ListNotations.
From ASUB Require Import AssocList Utils NEList Nterm Quotes.
From MetaCoq.Template Require Import All.

Notation tId := string.
Notation vId := string.
Notation fId := string.
Notation cId := string.

(** * A representation of arguments that resembles to one from the Coq implementation.
 ** * When we build an application to some named constant, during translation to the
 ** * MetaCoq AST we pass a number of holes corresponding to how many arguments were
 ** * marked implicit in the call to `add_binders`

 ** * DONE atm we always prepend these holes to the given argument list. This has the
 ** * assumption that there are no implicit arguments after some non-implicit argument.
 ** * To fix this we would have to merge left-nested applications during the translation
 ** * and save the list of implicit positions instead of only their number.
 *)
Record gallinaArg := { g_name : string; g_implicit : bool; g_type : nterm }.
Definition implArg (name: string) (type: nterm) := {| g_name := name; g_implicit := true; g_type := type |}.
Definition explArg (name: string) (type: nterm) := {| g_name := name; g_implicit := false; g_type := type |}.
Definition makeExplicitArg (g: gallinaArg) := {| g_name := g.(g_name); g_implicit := false; g_type := g.(g_type) |}.

Inductive AutosubstFunctor : Set := AFCod | AFList.

Inductive Binder :=
| Single : tId -> Binder
| BinderList : string -> tId -> Binder.

Inductive ArgumentHead :=
| Atom : tId -> ArgumentHead
| FunApp : AutosubstFunctor -> list nterm -> list ArgumentHead -> ArgumentHead.
  
Definition getBinders b :=
  match b with
  | Single x => [x]
  | BinderList _ x => [x]
  end.

Fixpoint getArgSorts (a: ArgumentHead) : list tId :=
  match a with
  | Atom x => [x]
  | FunApp _ _ xs => flat_map getArgSorts xs
  end.

Record Position := { pos_binders : list Binder;
                     pos_head : ArgumentHead }.
Record Constructor := { con_parameters : list gallinaArg;
                        con_name : cId;
                        con_positions : list Position }.

Definition getArgs c :=
  flat_map (fun p => getArgSorts p.(pos_head)) c.(con_positions).

Definition Spec := SFMap.t (list Constructor).

(* Return all sorts that are bound in a constructor of a sort in the given component *)
Definition getBoundSorts (spec: Spec) (component: NEList.t tId) : list tId :=
  let constructors := flat_map (fun sort => match SFMap.find spec sort with
                                         | None => []
                                         | Some ctors => ctors
                                         end) (NEList.to_list component) in
  let binders := flat_map (fun ctor =>
                             flat_map (fun position =>
                                         flat_map getBinders position.(pos_binders))
                                      ctor.(con_positions))
                          constructors in
  binders.

Record Signature := { sigSpec : Spec;
                      sigSubstOf : SFMap.t (list tId);
                      sigComponents : list (NEList.t tId);
                      sigIsOpen : SSet.t;
                      sigArguments: SFMap.t (list tId);
                      sigRenamings : SSet.t;
                    }.

Definition t := Signature.

Scheme Equality for string.
Scheme Equality for Binder.
(* Scheme Equality for ArgumentHead. *)


(* a.d. DONE, scheme equality issues im bugtracker, ggf neues Issue
 * originally did not work b/c Position was declared with primitive projections.
 * but even without them Scheme Equality does not like list Binder
 * Jason Gross hat dafuer schon ein Issue erstellt *)
(* Scheme Equality for Position. *)

Notation eq_dec A := (forall x y:A, { x = y } + { x <> y }).
(* TODO I think for this I would need the stronger induction lemma *)
(* Lemma ArgumenHead_eq_dec : eq_dec ArgumentHead. *)
(* Proof. *)
(* Admitted. *)

(* Lemma Position_eq_dec : eq_dec Position. *)
(* Proof. *)
(*   repeat (decide equality). *)
(* Qed. *)


(* Lemma Constructor_eq_dec : eq_dec Constructor. *)
(* Proof. *)
(*   repeat (decide equality). *)
(* Qed. *)

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
    sigComponents := [ ("ty", []); ("tm", [ "vl" ]) ];
    sigIsOpen := SSet.fromList ["ty"; "vl"];
    sigArguments := SFMap.fromList [ ("tm", [ "tm"; "ty"; "vl" ])
                                  ; ("ty", [ "ty" ])
                                  ; ("vl", [ "ty"; "tm" ]) ];
    sigRenamings := SSet.fromList ["ty"; "tm"; "vl"];
    |}.
End Hsig_example.

Module Hsig_fol.
  #[ local ]
   Open Scope string.
  
  Definition mySigSpec : Spec := SFMap.fromList [
                                    ("form", [ {|
                                                 con_parameters := [];
                                                 con_name := "Fal";
                                                 con_positions := []
                                               |}; {|
                                               con_parameters := [explArg "p" (nTerm nat_q)];
                                               con_name := "Pred";
                                               con_positions := [ {| pos_binders := []; pos_head := FunApp AFCod [nApp (nRef "fin") [nRef "p"]] [ Atom "term" ] |} ]
                                               (* con_positions := [ {| pos_binders := []; pos_head := Atom "term" |}] *)
                                             |}; {|
                                               con_parameters := [];
                                               con_name := "Impl";
                                               con_positions := [ {| pos_binders := []; pos_head := Atom "form"; |};
                                                            {| pos_binders := []; pos_head := Atom "form"; |} ];
                                             |}; {|
                                               con_parameters := [];
                                               con_name := "Conj";
                                               con_positions := [ {| pos_binders := []; pos_head := Atom "form" |};
                                                            {| pos_binders := []; pos_head := Atom "form" |} ];
                                             |}; {|
                                               con_parameters := [];
                                               con_name := "Disj";
                                               con_positions := [ {| pos_binders := []; pos_head := Atom "form" |};
                                                            {| pos_binders := []; pos_head := Atom "form" |} ];
                                             |}; {|
                                               con_parameters := [];
                                               con_name := "All";
                                               con_positions := [ {| pos_binders := [Single "term"];
                                                                pos_head := Atom "form" |} ];
                                             |}; {|
                                               con_parameters := [];
                                               con_name := "Ex";
                                               con_positions := [ {| pos_binders := [Single "term"]; pos_head := Atom "form"; |} ]
                                             |}
                                             ]
                                    ); ("term", [ {|
                                                    con_parameters := [explArg "f" (nTerm nat_q)];
                                                    con_name := "Func";
                                                    con_positions := [ {|pos_binders := []; pos_head := FunApp AFCod [nApp (nRef "fin") [nRef "f"]] [Atom "term"] |} ]
                                                    (* con_positions := [ {|pos_binders := []; pos_head := Atom "term" |} ] *)
                                       |} ] )
                                  ].

  Definition mySig : Signature := {|
    sigSpec := mySigSpec;
    sigSubstOf := SFMap.fromList [ ("form",["term"]); ("term",["term"])];
    sigComponents := [("term", []); ("form", [])];
    sigIsOpen := SSet.fromList ["term"];
    sigArguments := SFMap.fromList [ ("form",["term";"form"])
                                   ; ("term",["term"])];
    sigRenamings := SSet.fromList [];
                                 |}.
End Hsig_fol.
