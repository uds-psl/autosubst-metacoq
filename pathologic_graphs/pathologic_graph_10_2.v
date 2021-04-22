Require Import String List.
Import ListNotations.

From ASUB Require Import HOASParser monad.
Import HOASNotation.
Open Scope string.
Open Scope hoas_scope.

Definition test_10_2_sorts :=
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
; "sort14" := Sort
; "sort15" := Sort
; "sort16" := Sort
; "sort17" := Sort
; "sort18" := Sort
; "sort19" := Sort ].

Definition test_10_2_ctors :=
  [ "cmix0" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort0"
; "cmix1" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort1"
; "cmix2" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort2"
; "cmix3" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort3"
; "cmix4" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort4"
; "cmix5" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort5"
; "cmix6" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort6"
; "cmix7" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort7"
; "cmix8" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort8"
; "cmix9" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort9"
; "cmix10" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort10"
; "cmix11" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort11"
; "cmix12" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort12"
; "cmix13" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort13"
; "cmix14" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort14"
; "cmix15" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort15"
; "cmix16" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort16"
; "cmix17" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort17"
; "cmix18" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort18"
; "cmix19" := "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort19"
; "clam10" := {{"sort8" -> "sort7"}} -> "sort7"
; "clam20" := {{"sort11" -> "sort10"}} -> "sort11" ].
