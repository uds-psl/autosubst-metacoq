Require Import String List.
Import ListNotations.

From ASUB Require Import HOASParser monad.
Import HOASNotation.
Open Scope string.
Open Scope hoas_scope.

Definition test_14_3_sorts :=
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
; "sort39" := Sort
; "sort40" := Sort
; "sort41" := Sort ].

Definition test_14_3_ctors :=
  [ "cmix0" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort0"
; "cmix1" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort1"
; "cmix2" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort2"
; "cmix3" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort3"
; "cmix4" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort4"
; "cmix5" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort5"
; "cmix6" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort6"
; "cmix7" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort7"
; "cmix8" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort8"
; "cmix9" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort9"
; "cmix10" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort10"
; "cmix11" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort11"
; "cmix12" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort12"
; "cmix13" := "sort0" -> "sort1" -> "sort2" -> "sort3" -> "sort4" -> "sort5" -> "sort6" -> "sort7" -> "sort8" -> "sort9" -> "sort10" -> "sort11" -> "sort12" -> "sort13" -> "sort13"
; "cmix14" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort14"
; "cmix15" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort15"
; "cmix16" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort16"
; "cmix17" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort17"
; "cmix18" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort18"
; "cmix19" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort19"
; "cmix20" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort20"
; "cmix21" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort21"
; "cmix22" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort22"
; "cmix23" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort23"
; "cmix24" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort24"
; "cmix25" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort25"
; "cmix26" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort26"
; "cmix27" := "sort14" -> "sort15" -> "sort16" -> "sort17" -> "sort18" -> "sort19" -> "sort20" -> "sort21" -> "sort22" -> "sort23" -> "sort24" -> "sort25" -> "sort26" -> "sort27" -> "sort27"
; "cmix28" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort28"
; "cmix29" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort29"
; "cmix30" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort30"
; "cmix31" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort31"
; "cmix32" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort32"
; "cmix33" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort33"
; "cmix34" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort34"
; "cmix35" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort35"
; "cmix36" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort36"
; "cmix37" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort37"
; "cmix38" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort38"
; "cmix39" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort39"
; "cmix40" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort40"
; "cmix41" := "sort28" -> "sort29" -> "sort30" -> "sort31" -> "sort32" -> "sort33" -> "sort34" -> "sort35" -> "sort36" -> "sort37" -> "sort38" -> "sort39" -> "sort40" -> "sort41" -> "sort41"
; "clam14" := {{"sort5" -> "sort2"}} -> "sort5"
; "clam28" := {{"sort15" -> "sort19"}} -> "sort27"
; "clam42" := {{"sort32" -> "sort39"}} -> "sort32" ].
