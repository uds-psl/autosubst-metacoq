(** * Module to parse HOAS using custom entry notations *)
From ASUB Require Import hsig.
Require Import List String.
(* Import ListNotations. *)
Open Scope string.

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

Definition str_to_position (s: string) : HOASPosition :=
  {| hpos_binders := nil; hpos_head := s |}.
Coercion str_to_position : string >-> HOASPosition.

Definition str_to_binder (s: string) : HOASBinder := HSingle s.
Coercion str_to_binder : string >-> HOASBinder.

From ASUB Require Import IdentParsing.

Module HOASNotation.
  Declare Custom Entry hoas_sorts.
  Declare Custom Entry hoas_ctors.
  Declare Custom Entry hoas_params.

  Notation "'<{' e '}>'" := (e) (e custom hoas_sorts).

  Notation " x : 'Type' " := (x) (in custom hoas_sorts at level 60, only parsing).
  Notation " x ; y ; .. ; z " := (cons x (cons y .. (cons z nil) .. )) (in custom hoas_sorts at level 70, only parsing).

  (* Notation "a" := (UVar (ident_to_string a)) (in custom koika at level 1, a constr at level 0, only parsing). *)
  Notation "a" := (ident_to_string a) (in custom hoas_sorts at level 1, a constr at level 0, only parsing).

  Notation "'{{' e '}}'" := (e) (e custom hoas_ctors).
  Notation " x p : y -> .. -> z -> w " :=
    ({| hcon_parameters := p;
        hcon_name:=x;
        hcon_positions:= (@cons HOASPosition y .. (@cons HOASPosition z (@nil HOASPosition)) ..);
        hcon_target:=w |}) (in custom hoas_ctors at level 70, p at level 0, y at next level, z at next level, w at next level, only parsing).
  Notation " x : y -> .. -> z -> w " :=
    ({| hcon_parameters := nil;
        hcon_name:=x;
        hcon_positions:= (@cons HOASPosition y .. (@cons HOASPosition z (@nil HOASPosition)) ..);
        hcon_target:=w |}) (in custom hoas_ctors at level 70, y at next level, z at next level, w at next level, only parsing).

  Notation " '(|' p0 , .. , p1 '|)' " := (@cons HOASParameter p0 .. (@cons HOASParameter p1 nil) .. ) (in custom hoas_ctors, p0 custom hoas_params at level 2, p1 custom hoas_params at level 2).
  Notation " p : t  " := ({| hpar_name:=p; hpar_sort:=t|}) (in custom hoas_params at level 2, only parsing).
  Notation "a" := (ident_to_string a) (in custom hoas_params at level 1, a constr at level 0, only parsing).

  Notation " ( x -> .. -> y -> z ) " :=
    ({| hpos_binders:= (@cons HOASBinder x .. (@cons HOASBinder y (@nil HOASBinder)) ..);
        hpos_head:=z |}) (in custom hoas_ctors at level 50, y at next level, z at next level, only parsing).
  
  Notation " x ; y ; .. ; z " := (@cons HOASConstructor x (@cons HOASConstructor y .. (@cons HOASConstructor z (@nil HOASConstructor)) .. )) (in custom hoas_ctors at level 100, y at next level, z at next level, only parsing).
  Notation "a" := (ident_to_string a) (in custom hoas_ctors at level 1, a constr at level 0, only parsing).

  Definition bla_sorts := <{ ty : Type;
                             tm : Type }>.
  Check bla_sorts.
  Definition bla_ctors := {{ arr (| p : nat, k : nat |) : ty -> ty -> ty;
                             all : ty -> ty -> ty;
                             app : tm -> tm -> tm;
                             lam : (tm -> tm) -> tm }}.
  Check bla_ctors.
End HOASNotation. 

