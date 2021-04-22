Require Import String List.
Import ListNotations.

From ASUB Require Import HOASParser monad.
Import HOASNotation.
Open Scope string.
Open Scope hoas_scope.

From ASUB Require Import pathologic_graph_5_3 pathologic_graph_10_3 pathologic_graph_10_2 pathologic_graph_10_4  pathologic_graph_12_3 pathologic_graph_14_3.

Definition test_5_3_sig := translate_signature test_5_3_sorts test_5_3_ctors.
Definition test_10_2_sig := translate_signature test_10_2_sorts test_10_2_ctors.
Definition test_10_3_sig := translate_signature test_10_3_sorts test_10_3_ctors.
Definition test_10_4_sig := translate_signature test_10_4_sorts test_10_4_ctors.
Definition test_12_3_sig := translate_signature test_12_3_sorts test_12_3_ctors.
Definition test_14_3_sig := translate_signature test_14_3_sorts test_14_3_ctors.

(* 1.1 seconds *)
Time Compute (E.run test_5_3_sig tt tt).

(* 8 seconds *)
Time Compute (E.run test_10_2_sig tt tt).

(* 10 seconds *)
(* Time Compute (E.run test_10_3_sig tt tt). *)

(* 28 seconds *)
Time Compute (E.run test_10_4_sig tt tt).

(* 20 seconds *)
(* Time Compute (E.run test_12_3_sig tt tt). *)

(* 36 seconds *)
Time Compute (E.run test_14_3_sig tt tt).
