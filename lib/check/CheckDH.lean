/- This file prints the axioms of the final theorems of the `lib/dh` layer: the Davenport–Heilbronn function `dh`, a
combination of the Dirichlet `L`-functions of a character mod 5 that has the functional equation of `ζ` and zeros off
the critical line, and its columns of the library's criteria for RH (each statement with `dh` in place of `ζ`, refuted
or proved). `CheckAll.lean` does not import the layer, so that its build leaves out the layer's numerical
certificates. It is not built by default (`scripts/check_axioms.py --dh`). Every line it prints must be
`[propext, Classical.choice, Quot.sound]`, a subset of them, or none. -/
import DHInert
import ChiFirstFailure
import DHBohrSphere
import DHColumnRest
import DHBallKernel

/- The function: `dh ≢ 0`, its functional equation, the conjugation symmetry of its zeros, the coefficients of
`−dh′/dh`, the sum over its zeros and the Euler–Maclaurin bound. -/
#print axioms PsiOmega.dh_ne_zero
#print axioms PsiOmega.dh_functional_equation
#print axioms PsiOmega.dh_conj_zero
#print axioms PsiOmega.cDH_chi5_eq_of_dvd
#print axioms PsiOmega.hasSum_logDeriv_dh
#print axioms PsiOmega.norm_dh_sub_EM_le
#print axioms PsiOmega.dh_div_a1_real_ge

/- Its zeros off the critical line: a negative value of the Weil form certifies one, the certificate's zero, which is
not real and may be taken right of the line, four zeros located in boxes, and GRH and RH for `dh` refuted. -/
#print axioms PsiOmega.exists_offline_dh_of_neg
#print axioms PsiOmega.dh_offline_zero
#print axioms PsiOmega.dh_offline_nonreal_zero
#print axioms PsiOmega.dh_offline_zero_right
#print axioms PsiOmega.dh_offcross_zero
#print axioms PsiOmega.Locate.dh_zeros_located_four_box
#print axioms PsiOmega.not_GRH_dh
#print axioms PsiOmega.dhRH_iff_cross
#print axioms PsiOmega.dh_zero_pair_off_sphere

/- On the critical line: the channels of `χ₅`, and the zero condition as one real equation. -/
#print axioms PsiOmega.chi5_channel_fe
#print axioms PsiOmega.chi5_phase_lock
#print axioms PsiOmega.chi5_channel_ratio_real
#print axioms PsiOmega.chi5_channel_ratio
#print axioms PsiOmega.dh_line_zero_iff

/- The Weil form of `dh`: negative somewhere, negative definite on a plane and on spaces of dimension `4` and `5`, and
its ground energy `λ_dh`, negative from `12/5` on, failing exponentially, with a first failure. -/
#print axioms PsiOmega.exists_lamDH_neg
#print axioms PsiOmega.QDHu_packet_plane_neg
#print axioms DHNegIndex.negIndex_ge_four
#print axioms DHNegIndex.negIndex_ge_five
#print axioms PsiOmega.finrank_le_quadruples_dh
#print axioms PsiOmega.lamDH_fails_exponentially
#print axioms PsiOmega.not_lamDH_subexp
#print axioms PsiOmega.continuousOn_lamDH
#print axioms PsiOmega.first_failureDH

/- The dh column of the library's criteria for RH: each criterion with `dh` in place of `ζ`, whose hypotheses `dh`
cannot satisfy, since its RH fails. -/
#print axioms PsiOmega.weil_criterion_dh
#print axioms PsiOmega.QDHu_nonneg_of_DHRHcross
#print axioms PsiOmega.not_D_dh
#print axioms PsiOmega.not_twins_nonneg_dh
#print axioms PsiOmega.not_twins_subexp_dh
#print axioms PsiOmega.not_posDef_dh
#print axioms PsiOmega.not_realization_dh
#print axioms PsiOmega.not_posDefH_dh
#print axioms PsiOmega.not_odd_lower_dh
#print axioms PsiOmega.not_lamODH_lower
#print axioms PsiOmega.theoremDDH
#print axioms PsiOmega.bilDH_polar
#print axioms PsiOmega.euler_lagrangeDH
#print axioms PsiOmega.dhRHcross_of_eventually_simple
#print axioms PsiOmega.dhRHcross_of_hypConv_top
#print axioms PsiOmega.not_simple_hypConvDH
#print axioms PsiOmega.not_hypConvDH_top
#print axioms PsiOmega.not_ground_states_dh
#print axioms PsiOmega.not_groundStates_dodging_dh
#print axioms PsiOmega.not_D_and_realRooted_hadamard
#print axioms PsiOmega.not_hypConvStripDH_top
#print axioms PsiOmega.not_XiDH_params
#print axioms PsiOmega.not_dodging_hadamard
#print axioms PsiOmega.not_pairing_and_realRooted

/- The χ column: the same criteria for the `L`-function of a Dirichlet character `χ`, and GRH for `χ₋₃`, `χ₋₄`, `χ₋₇`
and `χ₋₈` from them. -/
#print axioms PsiOmega.exists_groundStateC
#print axioms PsiOmega.euler_lagrangeC_mem
#print axioms PsiOmega.theoremDC
#print axioms PsiOmega.grh_of_eventually_simpleC
#print axioms PsiOmega.grh_chi3_of_hypConvC_top
#print axioms PsiOmega.grh_chi4_of_hypConvC_top
#print axioms PsiOmega.grh_chi7_of_hypConvC_top
#print axioms PsiOmega.grh_chi8_of_hypConvC_top
#print axioms PsiOmega.continuousOn_lamC
#print axioms PsiOmega.lamC_pos_small
#print axioms PsiOmega.first_failureC
#print axioms PsiOmega.lamC_nonneg_of_GRH
#print axioms PsiOmega.grh_iff_lamC_eventually_nonneg
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi3
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi4
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi7
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi8
