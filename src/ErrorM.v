Require Import String.
#[ local ]
 Open Scope string.

From ASUB Require Import Monad.

(* a.d. TODO maybe write the error monad directly. *)

(* Adding the module type annotation breaks other modules because then E is not transparent *)
Module EArgs (* : RWSEParams *).
  Definition R := unit.
  Definition W := unit.
  Definition S := unit.
  Definition E := string.

  Definition append := fun (_ _: unit) => tt.
  Definition empty := tt.
End EArgs.

Module ErrorM := RWSEM EArgs.
