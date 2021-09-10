Require Import String.
From MetaCoq.Template Require Import All.
From ASUB Require Import core unscoped.

(* TODO make definition based on scope_type. There are things both in unscoped and fintype *)
MetaCoq Quote Definition nat_q := nat.
MetaCoq Quote Definition S_q := @S.
MetaCoq Quote Definition option_q := @option.
MetaCoq Quote Definition eq_q := @eq.
MetaCoq Quote Definition eq_trans_q := @eq_trans.
MetaCoq Quote Definition eq_sym_q := @eq_sym.
MetaCoq Quote Definition eq_refl_q := @eq_refl.
MetaCoq Quote Definition eq_ind_r_q := @eq_ind_r.
MetaCoq Quote Definition f_equal_q := @f_equal.
(* MetaCoq Quote Definition up_ren_q := up_ren. *)
MetaCoq Quote Definition funcomp_q := @funcomp.
MetaCoq Quote Definition var_zero_q := @var_zero.
MetaCoq Quote Definition scons_q := @scons.
MetaCoq Quote Definition id_q := @id.
MetaCoq Quote Definition ap_q := @ap.
MetaCoq Quote Definition up_ren_q := @up_ren.
(* not adding the @ quotes it with an implicit argument (i.e. an evar)
 THen using this term to generate code triggers an exception when unquoting because the contained evar has not been declared *)
MetaCoq Quote Definition shift_q := @shift.
MetaCoq Quote Definition up_ren_ren_q := @up_ren_ren.


From ASUB Require Import fintype.
MetaCoq Quote Definition fin_q := @fin.

