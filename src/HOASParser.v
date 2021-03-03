
Require Import List String.
Import ListNotations.
(* From ASUB Require Import hsig. *)


Notation HOASSort := string.

Record HOASPosition := { hpos_binders : list string;
                         hpos_head : string }.
Record HOASConstructor := { hcon_name : string;
                            hcon_positions : list HOASPosition;
                            hcon_target : string }.

Definition str_to_binder (s: string) : HOASPosition :=
  {| hpos_binders:= []; hpos_head := s |}.
Coercion str_to_binder : string >-> HOASPosition.

Definition consP : HOASPosition -> list HOASPosition -> list HOASPosition := cons.
Definition nilP : list HOASPosition := nil.

Module HOASNotation.
  Declare Scope hoas_scope.
  Notation " x := 'Sort' " := (x) (at level 70, only parsing) : hoas_scope.

  Notation " x := y " :=
    ({| hcon_name:= x;
        hcon_positions:=[];
        hcon_target:= y |}) (at level 70, only parsing) : hoas_scope.
  (* a.d. todo, why do I need the "at next level" modifiers here? *)
  Notation " x := y -> .. -> z -> w " :=
    ({| hcon_name:=x;
        hcon_positions:= (consP y .. (consP z nilP) ..);
        hcon_target:=w |}) (at level 70, y at next level, z at next level, w at next level, only parsing) : hoas_scope.

  Notation " {{ x -> .. -> y -> z }} " :=
    ({| hpos_binders:= (cons x .. (cons y nil) ..);
        hpos_head:=z |}) (y at next level, z at next level, only parsing) : hoas_scope.
End HOASNotation.

Require Import hsig AL.

Definition translate_position (hp: HOASPosition) : Position :=
  let '{| hpos_binders := hpos_binders; hpos_head := hpos_head |} := hp in
  {| pos_binders := map Single hpos_binders
     ; pos_head := Atom hpos_head |}.

Definition translate_constructor (hc: HOASConstructor) : (tId * Constructor) :=
  let '{| hcon_name := hcon_name; hcon_positions := hcon_positions; hcon_target := hcon_target |} := hc in
  let c := {| con_parameters := []
              ; con_name := hcon_name
              ; con_positions := map translate_position hcon_positions |} in
  (hcon_target, c).

Scheme Equality for string.
Definition translate_spec (ss: list HOASSort) (hcs: list HOASConstructor) : spec :=
  let cs := map translate_constructor hcs in
  let cs_by_sort := map (fun s => (s, map snd (filter (fun '(s', _) => string_beq s s') cs))) ss in
  AL.fromList cs_by_sort.
          
Module Example.
  Import HOASNotation.
  Open Scope hoas_scope.
  Open Scope string.

  Definition fcbv_sorts :=
    [ "ty" := Sort
      ; "tm" := Sort
      ; "vl" := Sort ].

  Definition fcbv_constrs :=
    [ "arr" := "ty" -> "ty" -> "ty"
      ; "all" := {{ "ty" -> "ty" }} -> "ty"
      ; "app" := "tm" -> "tm" -> "tm"
      ; "tapp" := "tm" -> "ty" -> "tm"
      ; "vt" := "vl" -> "tm"
      ; "lam" := "ty" -> {{ "vl" -> "tm" }} -> "vl"
      ; "tlam" := {{ "ty" -> "tm" }} -> "vl" ].

  Compute translate_spec fcbv_sorts fcbv_constrs.
End Example.
