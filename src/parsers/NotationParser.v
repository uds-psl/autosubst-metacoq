(** * Module to parse HOAS using normal Notation commands *)
Require Import List String.
Import ListNotations.
From ASUB Require Import hsig AL monad sigAnalyzer.


Notation HOASSort := string.

(* Inductive types that are built by Coq notations and then translated to the internal datatypes in hsig *)
Inductive HOASBinder :=
| HSingle : tId -> HOASBinder
| HBinderList : string -> tId -> HOASBinder.

Record HOASPosition := { hpos_binders : list HOASBinder;
                         hpos_head : string }.
Record HOASParameter := { hpar_name : string; hpar_sort : string }.
Record HOASConstructor := { hcon_parameters : list HOASParameter;
                            hcon_name : string;
                            hcon_positions : list HOASPosition;
                            hcon_target : string }.

(* coercions for positions and binder so that the repetition pattern '..' automatically turns them into the correct datatype. *)
Definition str_to_position (s: string) : HOASPosition :=
  {| hpos_binders := []; hpos_head := s |}.
Coercion str_to_position : string >-> HOASPosition.

Definition consP : HOASPosition -> list HOASPosition -> list HOASPosition := cons.
Definition nilP : list HOASPosition := nil.

Definition str_to_binder (s: string) : HOASBinder := HSingle s.
Coercion str_to_binder : string >-> HOASBinder.

Definition consB : HOASBinder -> list HOASBinder -> list HOASBinder := cons.
Definition nilB : list HOASBinder := nil.

Module HOASNotation.
  Declare Scope hoas_scope.
  Notation " x := 'Sort' " := (x) (at level 70, only parsing) : hoas_scope.
  Notation " x := 'Functor' " := (x) (at level 70, only parsing) : hoas_scope.

  Notation " x := y " :=
    ({| hcon_parameters := [];
        hcon_name:= x;
        hcon_positions:=[];
        hcon_target:= y |}) (at level 70, only parsing) : hoas_scope.
  Notation " x <+ p1 <+ .. <+ pn := y " :=
    ({| hcon_parameters := (cons p1 .. (cons pn nil) ..);
        hcon_name:= x;
        hcon_positions:=[];
        hcon_target:= y |}) (at level 70, only parsing) : hoas_scope.
  (* a.d. TODO, why do I need the "at next level" modifiers here? *)
  Notation " x := y -> .. -> z -> w " :=
    ({| hcon_parameters := [];
        hcon_name:=x;
        hcon_positions:= (consP y .. (consP z nilP) ..);
        hcon_target:=w |}) (at level 70, y at next level, z at next level, w at next level, only parsing) : hoas_scope.
  Notation " x <+ p1 <+ .. <+ pn := y -> .. -> z -> w " :=
    ({| hcon_parameters := (cons p1 .. (cons pn nil) ..);
        hcon_name:=x;
        hcon_positions:= (consP y .. (consP z nilP) ..);
        hcon_target:=w |}) (at level 70, p1 at next level, pn at next level, y at next level, z at next level, w at next level, only parsing) : hoas_scope.
  Notation " {{ p : t }} " := ({| hpar_name:=p; hpar_sort:=t|}) (p at next level, t at level 100, only parsing) : hoas_scope.
  Notation " {{ x -> .. -> y -> z }} " :=
    ({| hpos_binders:= (consB x .. (consB y nilB) ..);
        hpos_head:=z |}) (y at next level, z at next level, only parsing) : hoas_scope.
  Notation " << p , n >> " :=
    (HBinderList p n) (only parsing) : hoas_scope.
End HOASNotation.

Definition translate_binder (hb: HOASBinder) : Binder :=
  match hb with
  | HSingle x => Single x
  | HBinderList p x => BinderList p x
  end.
Definition translate_position (hp: HOASPosition) : Position :=
  let '{| hpos_binders := hpos_binders; hpos_head := hpos_head |} := hp in
  {| pos_binders := map translate_binder hpos_binders
     ; pos_head := Atom hpos_head |}.

Definition translate_constructor (hc: HOASConstructor) : (tId * Constructor) :=
  let '{| hcon_name := hcon_name; hcon_positions := hcon_positions; hcon_target := hcon_target |} := hc in
  let c := {| con_parameters := []
              ; con_name := hcon_name
              ; con_positions := map translate_position hcon_positions |} in
  (hcon_target, c).

Scheme Equality for string.
Definition translate_spec (ss: list HOASSort) (hcs: list HOASConstructor) : Spec :=
  let cs := map translate_constructor hcs in
  let cs_by_sort := map (fun s => (s, map snd (filter (fun '(s', _) => string_beq s s') cs))) ss in
  SFMap.fromList cs_by_sort.



Definition translate_signature (ss: list HOASSort) (hcs: list HOASConstructor) : E.t Signature :=
  let spec := translate_spec ss hcs in
  let canonical_order := ss in
  build_signature None canonical_order spec.
    
(* The problems from the tests/phoasnotation.v are mostly solved.
 variadic binders and parameters also work now but parameter notation is pretty ugly since I don't know how to remove the extra symbols *)
Module Example.
  Import HOASNotation.
  Open Scope hoas_scope.
  Open Scope string.

  Definition fcbv_sorts :=
    [ "ty" := Sort
      ; "tm" := Sort
      ; "vl" := Sort ].

  Definition fcbv_constrs (ty tm vl: string) :=
    [ "arr" := ty -> ty -> ty
      ; "all" := {{ ty -> ty }} -> ty
      ; "app" := tm -> tm -> tm
      ; "tapp" := tm -> ty -> tm
      ; "vt" := vl -> tm
      ; "lam" := ty -> {{ vl -> tm }} -> vl
      ; "tlam" := {{ ty -> tm }} -> vl ].
  Compute (fcbv_constrs "ty" "tm" "vl").
  
  (* Compute translate_spec fcbv_sorts fcbv_constrs. *)
  Compute translate_spec fcbv_sorts (fcbv_constrs "ty" "tm" "vl").
  Compute E.run (translate_signature fcbv_sorts (fcbv_constrs "ty" "tm" "vl")) tt tt.

  Definition variadic_sorts := [ "tm" := Sort ].
  Definition variadic_functors := [ "list" := Functor ].
  Definition variadic_constrs :=
    [ "lam" <+ {{ "p" : "tm" }} := {{ << "p", "tm" >> -> "tm" }} -> "tm" ].

  Compute translate_spec variadic_sorts variadic_constrs.
End Example.

