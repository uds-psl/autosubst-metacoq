Require Import List.
Import ListNotations.
From ASUB Require Import arguments.

Check C.

(* ok I can reset the bidirectionlity hint so it's no problem *)
Fail Check foo [A0; B0].
