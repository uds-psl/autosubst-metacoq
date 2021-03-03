Require Import List String.
Import ListNotations.
(* From ASUB Require Import hsig. *)


Record hoas_type := { PT: string }.

Record Position := { pos_binders : list string;
                     pos_head : string }.
Record Constructor := { con_name : string;
                        con_positions : list Position;
                        con_target : string }.

Module hoas1.
Declare Scope phoas_scope.

Notation " x := 'Type' " := ({| PT:=x |}) (at level 70, only parsing) : phoas_scope.
Notation " x := y ~> .. ~> z ~> w " :=
  ({| con_name:=x;
      con_positions:= (cons y .. (cons z nil) ..);
      con_target:=w |}) (at level 70, y at next level, z at next level, w at next level, only parsing) : phoas_scope.
Notation " x := y " :=
  ({| con_name:= x;
      con_positions:=[];
      con_target:= y |}) (at level 70, only parsing) : phoas_scope.
Notation " {{ x ~> .. ~> y ~> z }} " :=
  ({| pos_binders:= (cons x .. (cons y nil) ..);
      pos_head:=z |}) (y at next level, z at next level, only parsing) : phoas_scope.
Notation " ! x "  := ({| pos_binders:=[]
                     ; pos_head:= x |}) (at level 65, only parsing) : phoas_scope.

Print Grammar constr.
Open Scope phoas_scope.
Open Scope string.

Definition fcbv_types := [ "tm" := Type
                           ; "ty" := Type
                           ; "vl" := Type ].

(* can parse HOAS with some caveats.
 the "x ~> .. ~> y" allows me to parse multiple arrows but I don't know how to make them optional.
 That's why for a position with just a head I use ! as a distinguishing symbol *)
(* Also, this does not include parameters and variadic binders. *)
Definition fcbv_constrs :=
  [ "arr" := !"ty" ~> !"ty" ~> "ty"
    ; "all" := {{ "ty" ~> "ty" }} ~> "ty"
    ; "app" := !"tm" ~> !"tm" ~> "tm"
    ; "tapp" := !"tm" ~> !"ty" ~> "tm"
    ; "vt" := !"vl" ~> "tm"
    ; "lam" := !"ty" ~> {{ "vl" ~> "tm" }} ~> "vl"
    ; "tlam" := {{ "ty" ~> "tm" }} ~> "vl"
    ; "const" := "tm" ].

Print Grammar constr.
End hoas1.

Module hoas2.
  (* We can actually remove the caveat of a position with no binders
     by defining a coercion from string to position and in the ~> .. ~> notation using specialized versions of cons and nil that trigger the coercion.
     *)
  Definition str_to_binder (s: string) : Position :=
    {| pos_binders:= []; pos_head := s |}.
  Coercion str_to_binder : string >-> Position.
  Check ("hello"%string : Position).
  
  Definition consP : Position -> list Position -> list Position := cons.
  Definition nilP : list Position := nil.

  Declare Scope hoas_scope2.
  Notation " x := 'Type' " := ({| PT:=x |}) (at level 70, only parsing) : hoas_scope2.

  Notation " x := y " :=
    ({| con_name:= x;
        con_positions:=[];
        con_target:= y |}) (at level 70, only parsing) : hoas_scope2.
  Notation " x := y ~> .. ~> z ~> w " :=
    ({| con_name:=x;
        con_positions:= (consP y .. (consP z nilP) ..);
        con_target:=w |}) (at level 70, y at next level, z at next level, w at next level, only parsing) : hoas_scope2.

  Notation " {{ x ~> .. ~> y ~> z }} " :=
    ({| pos_binders:= (cons x .. (cons y nil) ..);
        pos_head:=z |}) (y at next level, z at next level, only parsing) : hoas_scope2.


  Open Scope hoas_scope2.
  Open Scope string.

  (* still no parameters and variadic binders though *)
  Definition fcbv_constrs :=
    [ "arr" := "ty" ~> "ty" ~> "ty"
      ; "all" := {{ "ty" ~> "ty" }} ~> "ty"
      ; "app" := "tm" ~> "tm" ~> "tm"
      ; "tapp" := "tm" ~> "ty" ~> "tm"
      ; "vt" := "vl" ~> "tm"
      ; "lam" := "ty" ~> {{ "vl" ~> "tm" }} ~> "vl"
      ; "tlam" := {{ "ty" ~> "tm" }} ~> "vl"
      ; "const" := "tm" ].
