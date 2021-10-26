Require Import String.
From MetaCoq.Template Require Import All.
From ASUB Require Import core.

From ASUB Require unscoped fintype.

(* We quote common terms that are used in the proof generation. *)
MetaCoq Quote Definition nat_q := nat.
MetaCoq Quote Definition S_q := @S.
MetaCoq Quote Definition plus_q := @Nat.add.
MetaCoq Quote Definition option_q := @option.
MetaCoq Quote Definition eq_q := @eq.
MetaCoq Quote Definition eq_trans_q := @eq_trans.
MetaCoq Quote Definition eq_sym_q := @eq_sym.
MetaCoq Quote Definition eq_refl_q := @eq_refl.
MetaCoq Quote Definition eq_ind_r_q := @eq_ind_r.
MetaCoq Quote Definition f_equal_q := @f_equal.
MetaCoq Quote Definition funcomp_q := @funcomp.
MetaCoq Quote Definition id_q := @id.
MetaCoq Quote Definition ap_q := @ap.
MetaCoq Quote Definition fin_q := @fintype.fin.

(* Constants defined in both unscoped and fintype
 * We quote both definitions each and then decide in Termutil.v which we use based on the scope_type *)
MetaCoq Quote Definition unscoped_scons_q := @unscoped.scons.
MetaCoq Quote Definition unscoped_var_zero_q := @unscoped.var_zero.
MetaCoq Quote Definition unscoped_shift_q := @unscoped.shift.
MetaCoq Quote Definition unscoped_up_ren_q := @unscoped.up_ren.
MetaCoq Quote Definition unscoped_up_ren_ren_q := @unscoped.up_ren_ren.

MetaCoq Quote Definition fintype_scons_q := @fintype.scons.
MetaCoq Quote Definition fintype_var_zero_q := @fintype.var_zero.
MetaCoq Quote Definition fintype_shift_q := @fintype.shift.
MetaCoq Quote Definition fintype_up_ren_q := @fintype.up_ren.
MetaCoq Quote Definition fintype_up_ren_ren_q := @fintype.up_ren_ren.
MetaCoq Quote Definition fintype_scons_p_q := @fintype.scons_p.
MetaCoq Quote Definition fintype_var_zero_p_q := @fintype.zero_p.
MetaCoq Quote Definition fintype_shift_p_q := @fintype.shift_p.
MetaCoq Quote Definition fintype_upRen_p_q := @fintype.upRen_p.
MetaCoq Quote Definition fintype_up_ren_ren_p_q := @fintype.up_ren_ren_p.
MetaCoq Quote Definition fintype_scons_p_eta_q := @fintype.scons_p_eta.
MetaCoq Quote Definition fintype_scons_p_congr_q := @fintype.scons_p_congr.
MetaCoq Quote Definition fintype_scons_p_comp'_q := @fintype.scons_p_comp'.
MetaCoq Quote Definition fintype_scons_p_head'_q := @fintype.scons_p_head'.
MetaCoq Quote Definition fintype_scons_p_tail'_q := @fintype.scons_p_tail'.


(*** Functors *)
MetaCoq Quote Definition cod_q := @cod.
MetaCoq Quote Definition cod_map_q := @cod_map.
MetaCoq Quote Definition cod_id_q := @cod_id.
MetaCoq Quote Definition cod_ext_q := @cod_ext.
MetaCoq Quote Definition cod_comp_q := @cod_comp.

MetaCoq Quote Definition list_q := @list.
MetaCoq Quote Definition list_map_q := @list_map.
MetaCoq Quote Definition list_id_q := @list_id.
MetaCoq Quote Definition list_ext_q := @list_ext.
MetaCoq Quote Definition list_comp_q := @list_comp.
