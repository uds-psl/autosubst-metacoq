
Require Import String List.
Import ListNotations.

From ASUB Require Import HOASParser monad.
Import HOASNotation.
Open Scope string.
Open Scope hoas_scope.

Definition test_5_3_sorts :=
  [ "sort0" := Sort
; "sort1" := Sort
; "sort2" := Sort
; "sort3" := Sort
; "sort4" := Sort
; "sort5" := Sort
; "sort6" := Sort
; "sort7" := Sort
; "sort8" := Sort
; "sort9" := Sort
; "sort10" := Sort
; "sort11" := Sort
; "sort12" := Sort
; "sort13" := Sort
; "sort14" := Sort ].
              
Definition test_5_3_ctors :=
  [ "cmix0" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort0"
; "cmix1" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort1"
; "cmix2" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort2"
; "cmix3" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort3"
; "cmix4" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort4"
; "cmix5" := "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort5"
; "cmix6" := "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort6"
; "cmix7" := "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort7"
; "cmix8" := "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort8"
; "cmix9" := "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort9"
; "cmix10" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort10"
; "cmix11" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort11"
; "cmix12" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort12"
; "cmix13" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort13"
; "cmix14" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort14"
; "clam5" := {{"sort2" -> "sort3"}} -> "sort1"
; "clam10" := {{"sort9" -> "sort6"}} -> "sort7"
; "clam15" := {{"sort10" -> "sort11"}} -> "sort12" ].
