Require Import String List.
Import ListNotations.

Module DB.
  Definition t := string -> option nat.
  
  Definition empty : t := fun _ => None.

  Definition shift (dbmap: t) : t :=
    fun s' =>
      match dbmap s' with
      | None => None
      | Some n => Some (S n)
      end.

  Definition add (s: string) (dbmap: t) : t :=
    fun s' =>
      if eqb s s' then Some 0
      else shift dbmap s'.

  Fixpoint adds (ss: list string) (dbmap: t) : t :=
    match ss with
    | [] => dbmap
    | s :: ss =>
      adds ss (add s dbmap)
    end.
End DB.
