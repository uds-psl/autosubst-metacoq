
Require Import String List.
Import ListNotations.

From ASUB Require Import HOASParser monad.
Import HOASNotation.
Open Scope string.
Open Scope hoas_scope.

Definition test_10_4_sorts :=
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
; "sort19" := Sort
; "sort20" := Sort
; "sort21" := Sort
; "sort22" := Sort
; "sort23" := Sort
; "sort24" := Sort
; "sort25" := Sort
; "sort26" := Sort
; "sort27" := Sort
; "sort28" := Sort
; "sort29" := Sort
; "sort30" := Sort
; "sort31" := Sort
; "sort32" := Sort
; "sort33" := Sort
; "sort34" := Sort
; "sort35" := Sort
; "sort36" := Sort
; "sort37" := Sort
; "sort38" := Sort
; "sort39" := Sort ].

Definition test_10_4_ctors :=
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
; "cmix20" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort20"
; "cmix21" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort21"
; "cmix22" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort22"
; "cmix23" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort23"
; "cmix24" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort24"
; "cmix25" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort25"
; "cmix26" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort26"
; "cmix27" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort27"
; "cmix28" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort28"
; "cmix29" := "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort28" -> "sort29" -> "sort29"
; "cmix30" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort30"
; "cmix31" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort31"
; "cmix32" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort32"
; "cmix33" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort33"
; "cmix34" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort34"
; "cmix35" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort35"
; "cmix36" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort36"
; "cmix37" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort37"
; "cmix38" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort38"
; "cmix39" := "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort39"
; "clam10" := {{"sort2" -> "sort0"}} -> "sort9"
; "clam20" := {{"sort13" -> "sort14"}} -> "sort13"
; "clam30" := {{"sort28" -> "sort22"}} -> "sort21"
    ; "clam40" := {{"sort36" -> "sort37"}} -> "sort37" ].
                                              
