From mathcomp Require Import all_ssreflect finmap.

Section t.
  Open Scope fmap.
  
  Time Compute ([fmap].[? 1]).

  Definition test := [fmap].[1 <- true].[2 <- false].
  Time Compute test.[? 1].
