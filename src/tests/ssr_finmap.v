From mathcomp Require Import all_ssreflect finmap.

Section t.
  Open Scope fmap.

  Definition empty := [fmap of bool_choiceType -> nat].
  Check empty.
  (* 11 sec on my laptop *)
  Time Compute (empty.[? true]).

  Definition mymap := [fmap].[true <- 1].
  Check mymap.
  (* OOM after a while *)
  Time Compute (mymap.[? true]).

  
