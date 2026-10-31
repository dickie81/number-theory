/- This file prints the axioms of every final theorem of the library. It is not built by default. Every line it
prints must be `[propext, Classical.choice, Quot.sound]`, a subset of them, or none. -/
import PrimeNumberTheoremAnd.Consequences
import PNTKV
import KaiserKV
import TwinKV
import DetectEM
import WeilIndexInfinite
import StripConv
import PhiDExp
import LogDerivDisc
import HalfPlanePNT
import BohrKV
import HalfPlaneFinal
import PsiExponent
import HalfPlaneLindelof
import SmoothPerron
import MertensExponent
import HalfPlaneJoinsPNT
import DivisorExponent
import ChiPNT
import PNTProgressions
import ChiUniform
import Littlewood
import LeastNonresidue
import SquarefreeCount
import ExplicitSmooth
import ExplicitConstants
import QuadRing
import QuadSplit
import QuadKronecker
import QuadClassNumber
import Subconvexity
import SubconvexityCrit
import InghamDetect
import InghamDensity
import LinnikChar
import LinnikDeduction
import LinnikHybrid
import LinnikDetect
import LinnikDensity
import LinnikHalf
import LinnikFE
import LinnikLindelof
import LinnikSubconvex
import MertensChi
import ShortCharSums
import LinnikAFE
import LinnikFourth
import LinnikIngham
import LinnikPower
import LinnikOffDiag
import LinnikHuxley
import LinnikGammaRatio
import LinnikReflect
import LinnikWeighted
import LinnikDual
import LinnikBuckets
import LinnikLargeValues
import LinnikTwelveBins
import LinnikTwelveSizes
import LinnikTwelve
import LinnikMoment
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import LinnikPoints
import SieveSmooth
import LinnikStep
import SieveLemma1
import SieveWeight
import SieveTypeII
import SieveRoute
import SieveCert
import SieveRough
import SieveSep
import SieveFamily
import SieveTypeIB
import SieveSpline
import SieveBrun
import SieveCount
import SieveRanges
import SieveLeaf
import SieveTree
import SieveDyadic
import SieveTypeIIU
import SieveRoughTuple
import SieveTypeIIR
import SieveDiff
import SieveStops1
import SieveCmp
import SieveStops2
import SieveProp6
import SieveChain
import SieveDecomp
import SieveBuch
import SieveLeaves
import SieveQ
import SieveDrop
import SieveMain
import LinnikCGL
import LinnikHuxStep
import SieveTypeIIGen
import LinnikInghamC
import SieveCurveGlue
import LinnikWeyl
import LinnikHuxStepY
import LinnikStairs7
import SieveHMBin
import SieveHMBins
import SieveHMWindow
import SieveTypeIIHM
import LinnikCGLLV
import LinnikCGLStep
import LinnikCGLMat
import LinnikCGLS23
import LinnikCGLMellin
import LinnikCGLReflect
import LinnikCGLPair
import LinnikCGLFrob
import LinnikCGLS2
import LinnikCGLFourier
import LinnikCGLPoisson
import LinnikCGLTrace
import LinnikCGLDiag
import LinnikCGLTrunc
import LinnikCGLProd
import LinnikCGLRFact
import LinnikCGLRam
import LinnikCGLP71
import LinnikCGLSym
import LinnikCGLRt
import LinnikCGLP72
import LinnikCGLMom
import LinnikCGLMom4
import LinnikCGLCS
import LinnikCGLJ
import LinnikCGLFb
import LinnikCGLPhi
import LinnikCGLDecay
import LinnikCGLBlock
import LinnikCGL112
import LinnikCGLLoc
import LinnikCGLL105
import LinnikCGLT101
import LinnikCGLL107
import LinnikCGLSep
import LinnikCGLL109
import LinnikCGLL1010
import LinnikCGLCase
import LinnikCGLEps
import LinnikCGLS3
import LinnikCGLG
import LinnikCGLPois8
import LinnikCGLCount
import LinnikCGLAsum
import LinnikCGLNsum
import LinnikCGLN0
import LinnikCGLCov
import LinnikCGLSig2
import LinnikCGLFtil
import LinnikCGLJtil
import LinnikCGLTail
import LinnikCGLL82
import LinnikCGLConst
import LinnikCGLForm
import LinnikCGLFtilP
import LinnikCGLP81
import LinnikCGLHBPos
import LinnikCGLHBLen
import LinnikCGLRefl0
import LinnikCGLHBRefl
import LinnikCGLHBIter
import LinnikCGLHB101
import LinnikCGLDensity
import SieveMain2
import LinnikCGLSteps
import SieveCurve7D
import SieveBuch8
import SieveQ8
import SieveDeep
import SieveDeepCost
import SieveBox
import SieveDrop8
import SieveMain8
import SieveDeepCert
import SieveTypeIIU22000D
import SieveGrid22000E
import SieveCert22000E
import Linnik22000E
import LinnikG7
import LinnikGRH
import ShortPrimesHalfPlane
import LinnikWeylBridge
import ZetaHuxley
import AlmostAllPrimes
import ZetaGMDensity
import BohrLandauCore
#print axioms Landau.zeroFree_of_growth
#print axioms Landau.logDerivBnd_of_growth
#print axioms Landau.rung3_of_growth
#print axioms KVBridge.polylogGrowth_kv
#print axioms KVBridge.polylogGrowth_sharp
#print axioms KVBridge.zeroFree_kv
#print axioms KVBridge.rung3_kv
#print axioms LandauKV.zeroFree_KV
#print axioms LogDerivKV.logDerivBnd_KV
#print axioms MediumPNTW.GenPNTW
#print axioms MediumPNTW.GenPNTW'
#print axioms MediumPNTW.GenPNTWNoEps
#print axioms PNTKV.PNT_KV
#print axioms KaiserKV.lam_prefactor_KV
#print axioms TwinLandau.Q_ge_of_rates
#print axioms TwinKV.twins_lower_KV
#print axioms TwinKV.twins_lower_KV'
#print axioms TwinKV.twins_lower_cut
#print axioms TwinKV.twins_lower_KV_sharp
#print axioms ShortKV.zeroFreeXi_KV
#print axioms DetectEM.density_unconditional
#print axioms HalfPlanePNT.logDeriv_le_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_zeroFree
#print axioms BohrKV.shell_of_KV
#print axioms HalfPlanePNT.psi_isBigO_eleven_twelfths
#print axioms PsiExponent.Theta_le
#print axioms PsiExponent.half_le_Theta
#print axioms Eis.ne_zero_of_re_gt_eleven_twelfths
#print axioms HalfPlaneJoins.zeta_band_eleven_twelfths
#print axioms BohrLandauCore.tendsto_NX_div_of_lower
#print axioms PsiExponent.zeta_ne_zero_of_Theta_lt
#print axioms PsiExponent.psi_isBigO_Theta
#print axioms PsiExponent.psi_omega_Theta
#print axioms PsiExponent.limsup_expo
#print axioms HalfPlaneLindelof.norm_le_interp
#print axioms HalfPlaneLindelof.hasDerivAt_log_norm
#print axioms HalfPlaneLindelof.logDeriv_le_interp
#print axioms HalfPlaneLindelof.zeta_bound_of_zeroFree
#print axioms HalfPlaneLindelof.zeta_bound_eleven_twelfths
#print axioms HalfPlaneLindelof.zeta_bound_Theta
#print axioms SmoothPerron.verticalIntegral_eq_smoothedSum
#print axioms SmoothPerron.verticalIntegral_shift
#print axioms SmoothPerron.mellin_le_geom
#print axioms SmoothPerron.norm_smoothedSum_sub_le
#print axioms SmoothPerron.verticalIntegral_integrand_shift
#print axioms SmoothPerron.smoothedSum_eq_verticalIntegral_left
#print axioms MertensExponent.mertens_isBigO_of_zeroFree
#print axioms MertensExponent.mertens_isBigO_eleven_twelfths
#print axioms MertensExponent.mertens_isBigO_Theta
#print axioms MertensExponent.mertens_omega_Theta
#print axioms MertensExponent.rh_iff_Theta_eq_half
#print axioms MertensExponent.rh_iff_mertens
#print axioms MertensExponent.limsup_mexpo
#print axioms MertensExponent.moebius_tendsto_of_Theta_lt
#print axioms MertensExponent.moebius_not_tendsto_of_lt_Theta
#print axioms MertensExponent.moebiusAbscissa_eq_Theta
#print axioms HalfPlaneJoinsPNT.weil_twins_rate_Theta
#print axioms HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH
#print axioms DivisorExponent.integral_pow_mul_cexp
#print axioms DivisorExponent.inv_sub_one_pow_eq_integral
#print axioms DivisorExponent.LSeries_dk
#print axioms DivisorExponent.zeta_pow_eq
#print axioms DivisorExponent.verticalIntegral_inv_sub_one_pow
#print axioms DivisorExponent.smoothedSum_dk_eq
#print axioms DivisorExponent.norm_remainder_le
#print axioms DivisorExponent.coeff_Pk
#print axioms DivisorExponent.natDegree_Pk_eq
#print axioms DivisorExponent.divisor_isBigO_of_zeroFree
#print axioms DivisorExponent.divisor_isBigO_eleven_twelfths
#print axioms DivisorExponent.divisor_isBigO_Theta
#print axioms ChiPNT.sum_isBigO_of_zeroFree
#print axioms ChiPNT.psiChi_isBigO_of_zeroFree
#print axioms ChiPNT.psiChi_isBigO_eleven_twelfths
#print axioms PNTProgressions.sum_dvd_le_log
#print axioms PNTProgressions.sum_not_coprime_le
#print axioms PNTProgressions.psiChi_one
#print axioms PNTProgressions.psiAP_eq_sum
#print axioms PNTProgressions.psiAP_isBigO
#print axioms ChiPNT.sum_le_uniform
#print axioms ChiUniform.psiChi_le_uniform
#print axioms Littlewood.norm_LSeries_le_of_sum_le
#print axioms Littlewood.logDeriv_le_loglog
#print axioms Littlewood.norm_LFunction_le_real
#print axioms Littlewood.abs_log_norm_LFunction_one_le
#print axioms Littlewood.norm_LFunction_one_le
#print axioms Littlewood.norm_LFunction_one_ge
#print axioms Littlewood.norm_logDeriv_one_le
#print axioms LeastNonresidue.re_psiChi_ge
#print axioms LeastNonresidue.rpow_le_of_forall_eq
#print axioms LeastNonresidue.exists_prime_eq
#print axioms LeastNonresidue.exists_prime_ne_one
#print axioms LeastNonresidue.exists_nonsquare_le
#print axioms LeastNonresidue.exists_nonsquare_le_rpow
#print axioms SquarefreeCount.sum_sqf_eq
#print axioms SquarefreeCount.hasSum_moebius_div_sq
#print axioms SquarefreeCount.abs_sub_sum_le
#print axioms SquarefreeCount.abs_sum_sqf_sub_le
#print axioms SquarefreeCount.squarefree_isBigO_of_zeroFree
#print axioms SquarefreeCount.squarefree_isBigO_twelve_25ths
#print axioms SquarefreeCount.squarefree_isBigO_Theta
#print axioms SmoothPerron.mellin_le_geom_of
#print axioms ExplicitSmooth.contDiff_ν₀
#print axioms ExplicitSmooth.mass_ν₀
#print axioms ExplicitSmooth.mellin_ν₀_le_geom
#print axioms LogDerivDisc.logDeriv_le_uniform_of
#print axioms ChiPNT.sum_le_uniform_of
#print axioms ChiUniform.psiChi_le_uniform_of
#print axioms Littlewood.logDeriv_le_loglog_of
#print axioms Littlewood.abs_log_norm_LFunction_one_le_of
#print axioms LeastNonresidue.exists_nonsquare_le_of
#print axioms LeastNonresidue.exists_nonsquare_le_rpow_of
#print axioms ExplicitConstants.psiChi_le_explicit
#print axioms ExplicitConstants.logDeriv_le_explicit
#print axioms ExplicitConstants.norm_LFunction_one_le_explicit
#print axioms ExplicitConstants.norm_LFunction_one_ge_explicit
#print axioms ExplicitConstants.norm_logDeriv_one_le_explicit
#print axioms ExplicitConstants.exists_prime_eq_explicit
#print axioms ExplicitConstants.exists_prime_eq_13
#print axioms ExplicitConstants.exists_nonsquare_le_explicit
#print axioms ExplicitConstants.exists_nonsquare_le_13
#print axioms ExplicitConstants.exists_nonsquare_le_rpow_explicit
#print axioms QuadRing.int_of_mul_sq
#print axioms QuadRing.exists_eq
#print axioms QuadRing.minpoly_eq
#print axioms QuadRing.isIntegral_iff
#print axioms QuadRing.discr_eq_of_basis
#print axioms QuadRing.span_θ₁
#print axioms QuadRing.adjoin_θ₁
#print axioms QuadRing.discr_θ₁
#print axioms QuadRing.minpoly_θ₁
#print axioms QuadRing.span_θ₂
#print axioms QuadRing.adjoin_θ₂
#print axioms QuadRing.discr_θ₂
#print axioms QuadRing.minpoly_θ₂
#print axioms QuadRing.exists_sqrt
#print axioms QuadSplit.split_of_factors
#print axioms QuadSplit.ramified_of_factors
#print axioms QuadSplit.inert_of_factors
#print axioms QuadSplit.split_of_root
#print axioms QuadSplit.ramified_of_root
#print axioms QuadSplit.inert_of_no_root
#print axioms QuadSplit.ramified_of_dvd₂
#print axioms QuadSplit.ramified_two₂
#print axioms QuadSplit.split₂
#print axioms QuadSplit.inert₂
#print axioms QuadSplit.ramified_of_dvd₁
#print axioms QuadSplit.split₁
#print axioms QuadSplit.inert₁
#print axioms QuadSplit.split_two₁
#print axioms QuadSplit.inert_two₁
#print axioms QuadKronecker.jacBot_natCast
#print axioms QuadKronecker.jacTop_natCast
#print axioms QuadKronecker.jacobiSym_natAbs
#print axioms QuadKronecker.jacobiSym_two_natAbs
#print axioms QuadKronecker.type_one
#print axioms QuadKronecker.type_two_three
#print axioms QuadKronecker.dedekindZeta_eq
#print axioms QuadKronecker.ne_one_of_eq
#print axioms QuadKronecker.exists_kronecker
#print axioms QuadKronecker.classNumber_formula
#print axioms QuadClassNumber.classNumber_ge
#print axioms QuadClassNumber.classNumber_le
#print axioms QuadClassNumber.classNumber_ge_sqrt
#print axioms QuadClassNumber.regulator_mul_classNumber_ge
#print axioms QuadClassNumber.regulator_mul_classNumber_le
#print axioms QuadClassNumber.regulator_mul_classNumber_ge_sqrt
#print axioms QuadClassNumber.classNumber_ge_loglog
#print axioms QuadClassNumber.regulator_mul_classNumber_ge_loglog
#print axioms QuadClassNumber.exists_inert_le
#print axioms QuadClassNumber.exists_split_le
#print axioms QuadClassNumber.exists_inert_le_13
#print axioms QuadClassNumber.exists_split_le_13
#print axioms QuadClassNumber.eulerKronecker
#print axioms Subconvexity.zeta_strip_of_zeroFree
#print axioms Subconvexity.zeta_strip_eleven_twelfths
#print axioms Subconvexity.zetaCritBound_of_zeroFree
#print axioms Subconvexity.zetaCritBound_five_24
#print axioms Subconvexity.convexityBound
#print axioms Subconvexity.zetaCritBound_Theta
#print axioms Subconvexity.lindelof_of_RH
#print axioms Subconvexity.zeta_strip_of_crit
#print axioms Subconvexity.zeta_strip_eleven_twelfths_of_crit
#print axioms Subconvexity.zeta_strip_eleven_twelfths_of_weyl
#print axioms InghamDensity.detect_identity
#print axioms InghamDensity.trichotomy
#print axioms InghamDensity.densityXi_of_zetaCrit
#print axioms InghamDensity.inghamFromC
#print axioms InghamDensity.densityXi_17_6
#print axioms InghamDensity.densityXi_Theta
#print axioms InghamDensity.densityHypothesis_of_lindelof
#print axioms InghamDensity.short_primes_Theta
#print axioms ZetaFourth.afe_xi
#print axioms ZetaFourth.zeta_fourth_moment
#print axioms ZetaIngham.nx_ingham
#print axioms ZetaKernel.hm_duality_pts
#print axioms ZetaKernel.norm_kz_le
#print axioms ZetaKernel.power_count_pts
#print axioms ZetaHuxley.nx_huxley
#print axioms ZetaHuxley.densityXi_twelve_fifths
#print axioms ZetaHuxley.short_primes_seven_twelfths
#print axioms AlmostAll.arch_far
#print axioms AlmostAll.head_mean_square
#print axioms AlmostAll.almost_all_of_density
#print axioms AlmostAll.almost_all_short_primes
#print axioms ZetaGMLV.gm_prop31_one
#print axioms ZetaGMLV.gm_large_values
#print axioms ZetaGMWin.nx_gm
#print axioms ZetaGMIngham.nx_ingham13
#print axioms ZetaGMHux.nx_gmh
#print axioms ZetaGMDensity.densityXi_thirty_thirteenths
#print axioms ZetaGMDensity.short_primes_seventeen_thirtieths
#print axioms ZetaGMDensity.almost_all_short_primes_two_fifteenths
#print axioms LogDerivDisc.disc_point_ball
#print axioms LogDerivDisc.logDeriv_le_ball
#print axioms InghamDensity.norm_Gamma_exp_le
#print axioms ChiUniform.LFunction_ctr_inv_le
#print axioms ChiUniform.logDeriv_LFunction_right
#print axioms Linnik.perron_exp
#print axioms Linnik.logDeriv_LFunction_le
#print axioms Linnik.norm_Sx_le
#print axioms Linnik.totient_mul_SAP
#print axioms Linnik.re_Sx_one_ge
#print axioms Linnik.SAP_le_of_noPrime
#print axioms Linnik.error_le
#print axioms Linnik.total_le
#print axioms Linnik.prime_in_class
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.charDensity_twelve
#print axioms Linnik.linnik_twelve
#print axioms LinnikHybrid.mean_value_row
#print axioms LinnikHybrid.sum_chars_norm_sq_le
#print axioms LinnikHybrid.mean_value_chars
#print axioms LinnikHybrid.large_values_chars
#print axioms LinnikHybrid.large_values_chars_off
#print axioms LinnikPoints.large_values_points
#print axioms SieveSmooth.indicator_sub_G
#print axioms SieveSmooth.pow_mul_norm_fourier_GC_le
#print axioms SieveSmooth.integrable_fourier_GC
#print axioms LinnikStep.class1_step
#print axioms LinnikStep.count_step
#print axioms LinnikStep.charDensity_step
#print axioms SieveLemma1.perron_weight
#print axioms SieveLemma1.norm_Sw_le
#print axioms SieveWeight.exists_mellin_bound
#print axioms SieveWeight.norm_Sw_wy_le
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveRough.psi_le
#print axioms SieveRough.share2
#print axioms SieveRough.share2_of_cand
#print axioms SieveOmegaB.log_le_half_sub_inv
#print axioms SieveOmegaB.omB_le_w1
#print axioms SieveOmegaB.omB_mono
#print axioms SieveOmegaB.omB_anti
#print axioms SieveOmegaB.lnT_ge
#print axioms SieveOmegaB.omF_ge
#print axioms SieveCert.omegaC_le_w
#print axioms SieveCert.bound2_ge
#print axioms SieveRough.super_M
#print axioms SieveRough.evLe_cell_tr
#print axioms SieveRough.evLe_cell_ex
#print axioms SieveSep.sum_sep
#print axioms SieveSep.sep_bound
#print axioms SieveFamily.family_bound
#print axioms SieveFamily.Dsum_sharp_le
#print axioms SieveFamily.typeII_sharp_explicit
#print axioms SieveFamily.typeII_sharp
#print axioms SieveTypeIB.sum_bilinear
#print axioms SieveTypeIB.typeIB_bound
#print axioms SieveSpline.what_spl
#print axioms SieveSpline.norm_what_spl_tail
#print axioms SieveSpline.norm_Ew_spl_le
#print axioms SieveSpline.typeIB_spline
#print axioms SieveBrun.bonferroni
#print axioms SieveBrun.fundamental
#print axioms SieveBrun.gap_le
#print axioms SieveCount.card_A
#print axioms SieveCount.card_B
#print axioms SieveRanges.rng_sum_le
#print axioms SieveLeaf.leaf_A
#print axioms SieveLeaf.leaf_B
#print axioms SieveLeaf.leaf_gap
#print axioms SieveLeaf.prod_T_le
#print axioms SieveLeaf.prod_primesBelow_le
#print axioms SieveDyadic.sum_bump
#print axioms SieveTypeIIU.typeII_unw
#print axioms SieveRoughTuple.sum_rough_eq
#print axioms SieveStops2.typeII_cmp
#print axioms SieveStops2.stops2_bound
#print axioms SieveProp6.prop6
#print axioms SieveChain.typeII_gcmp'
#print axioms SieveChain.chainTU_bound
#print axioms SieveChain.chainTL_bound
#print axioms SieveChainR.chainTR_bound
#print axioms SieveDecomp.buchstab_fam
#print axioms SieveDecomp.famI_cells
#print axioms SieveDecomp.famI_vanish
#print axioms SieveLeaves.TL_spec
#print axioms SieveLeaves.TU_spec
#print axioms SieveLeaves.P6_spec
#print axioms SieveP6ib.prop6ib
#print axioms SieveLeaves.TR_spec
#print axioms SieveLeaves.P6IB_spec
#print axioms SieveQ.good_of_large
#print axioms SieveQ.P6IB_boxes
#print axioms SieveMain.TB_ev
#print axioms LinnikHuxStep.class1_gen
#print axioms LinnikHuxStep.count_gen
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikHuxStep.charDensity_step'
#print axioms SieveTypeIIGen.card_bin_gen
#print axioms SieveTypeIIGen.prod_MB_le_gen
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikWeyl.class2_empty
#print axioms LinnikHuxStepY.charDensity_genY
#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_hy_0
#print axioms LinnikStairs7.charDensity_hy_top
#print axioms SieveTypeIIHM.dp_eq_pv
#print axioms SieveTypeIIHM.sum_bin_hm
#print axioms SieveTypeIIHM.sum_typeII_bins_hm
#print axioms SieveTypeIIHM.offK_bound
#print axioms SieveCurveGlue.affine_corner_bound
#print axioms SieveCurveGlue.windowPieceHM_affine_split
#print axioms SieveCurveGlue.windowPieceHM_const_split
#print axioms SieveTypeIIHM.bin_bound_pt
#print axioms SieveTypeIIHM.bin_bound_gen_hm
#print axioms SieveTypeIIHM.typeII_gen_hm
#print axioms LinnikCGLLV.lv_range
#print axioms LinnikCGLLV.cgl_all
#print axioms LinnikCGLLV.taylor_pick
#print axioms LinnikCGLLV.cgl_shift
#print axioms LinnikCGLStep.block_bin_cgl
#print axioms LinnikCGLStep.class1_cgl
#print axioms LinnikCGLStep.count_cgl
#print axioms LinnikCGLMat.refined_moment_points
#print axioms LinnikCGLMat.prop46
#print axioms LinnikCGLMat.mvt_case
#print axioms LinnikCGLMat.alg112
#print axioms LinnikCGLMat.prop31_of_third
#print axioms LinnikCGLS23.third_of_s23
#print axioms LinnikCGLMellin.exists_H_bound
#print axioms LinnikCGLMellin.differentiable_H
#print axioms LinnikCGLMellin.perron_Wt
#print axioms LinnikCGLMellin.perron_gram
#print axioms LinnikCGLReflect.norm_Phi_le_far
#print axioms LinnikCGLReflect.LFunction_reflected
#print axioms LinnikCGLReflect.shift_of_bound
#print axioms LinnikCGLReflect.reflect_gram
#print axioms LinnikCGLReflect.gram_reflect
#print axioms LinnikCGLPair.norm_Eu_mul_le
#print axioms LinnikCGLPair.norm_dualT_le
#print axioms LinnikCGLPair.norm_integral_Mn_le
#print axioms LinnikCGLPair.norm_integral_Tl_le
#print axioms LinnikCGLPair.norm_gram_le
#print axioms LinnikCGLFrob.ls_points
#print axioms LinnikCGLFrob.prod_trick_points
#print axioms LinnikCGLFrob.sum_Dp_sq_le
#print axioms LinnikCGLFrob.gram_sq_le
#print axioms LinnikCGLFrob.frobOff_le
#print axioms LinnikCGLS2.LSX_le
#print axioms LinnikCGLS2.Bmax_le
#print axioms LinnikCGLS2.s2_main
#print axioms LinnikCGLS2.cgls2
#print axioms LinnikCGLFourier.hasDerivAt_F
#print axioms LinnikCGLFourier.fourier_F
#print axioms LinnikCGLFourier.lemma43
#print axioms LinnikCGLPoisson.poisson_scaled
#print axioms LinnikCGLPoisson.sum_colsP_residue
#print axioms LinnikCGLPoisson.gram_poisson
#print axioms LinnikCGLTrace.S3_eq_cube
#print axioms LinnikCGLTrace.Em_eq
#print axioms LinnikCGLTrace.S3_eq_Fm
#print axioms LinnikCGLDiag.muP_sub_mu0_le
#print axioms LinnikCGLDiag.muP_sub_mu0_le_rpow
#print axioms LinnikCGLDiag.S3_eq_all
#print axioms LinnikCGLTrunc.sum_FmT_cube
#print axioms LinnikCGLTrunc.norm_Fm_sub_FmT_le
#print axioms LinnikCGLTrunc.S3_trunc
#print axioms LinnikCGLProd.prod_eq_iter
#print axioms LinnikCGLProd.iter_swap
#print axioms LinnikCGLProd.hhat_prod
#print axioms LinnikCGLRFact.S2_triple
#print axioms LinnikCGLRFact.sum_Qk
#print axioms LinnikCGLRFact.Ip_eq
#print axioms LinnikCGLRam.norm_Cq_le
#print axioms LinnikCGLRam.Jk_decay
#print axioms LinnikCGLRam.Jk_eq_zero_of
#print axioms LinnikCGLP71.norm_Psi_le
#print axioms LinnikCGLP71.prop71
#print axioms LinnikCGLSym.prop71r
#print axioms LinnikCGLSym.Ip_cyc
#print axioms LinnikCGLSym.sum_le_three_mul
#print axioms LinnikCGLRt.local_le_Rt_sq
#print axioms LinnikCGLRt.inner_le
#print axioms LinnikCGLRt.Vr_inner_le
#print axioms LinnikCGLP72.Ip_le_It
#print axioms LinnikCGLP72.sum_Ak_regroup
#print axioms LinnikCGLP72.prop72
#print axioms LinnikCGLMom.lemma91
#print axioms LinnikCGLMom.lemma91_Rt
#print axioms LinnikCGLMom4.lemma92
#print axioms LinnikCGLMom4.lemma92_Rt
#print axioms LinnikCGLCS.sum_It_sq_le
#print axioms LinnikCGLCS.S32_le
#print axioms LinnikCGLJ.S34_le_Jint
#print axioms LinnikCGLJ.S33_le_S34
#print axioms LinnikCGLFb.contDiff_fb
#print axioms LinnikCGLFb.fb_one_ge
#print axioms LinnikCGLFb.S34_le_fb
#print axioms LinnikCGLPhi.integral_abs_iteratedDeriv_phi_le
#print axioms LinnikCGLPhi.fourier_phi_le
#print axioms LinnikCGLDecay.fb_decay
#print axioms LinnikCGLDecay.fb_decay_all
#print axioms LinnikCGLBlock.S34_le_P81
#print axioms LinnikCGLBlock.block_le
#print axioms LinnikCGL112.S3_le_blocks
#print axioms LinnikCGL112.S3_le_112
#print axioms LinnikCGLLoc.norm_esum_le_integral
#print axioms LinnikCGLLoc.norm_sq_esum_le
#print axioms LinnikCGLLoc.norm_cube_esum_le
#print axioms LinnikCGLL105.sum_triple_le
#print axioms LinnikCGLL105.lemma105
#print axioms LinnikCGLT101.sum_sq_R2_eq
#print axioms LinnikCGLT101.lemma106
#print axioms LinnikCGLL107.group_le
#print axioms LinnikCGLL107.lemma107
#print axioms LinnikCGLSep.log_sep
#print axioms LinnikCGLSep.sum_cube_le
#print axioms LinnikCGLL109.sum_cube_moment_le
#print axioms LinnikCGLL109.lemma109
#print axioms LinnikCGLL1010.lemma106'
#print axioms LinnikCGLL1010.lemma1010
#print axioms LinnikCGLCase.case_le
#print axioms LinnikCGLCase.remark103
#print axioms LinnikCGLCase.lemma1010_case
#print axioms LinnikCGLEps.lemma109_eps
#print axioms LinnikCGLEps.lemma1010_eps
#print axioms LinnikCGLEps.prop102
#print axioms LinnikCGLS3.cgls3
#print axioms LinnikCGLS3.prop31_pt
#print axioms LinnikCGLG.Jint_le_ga
#print axioms LinnikCGLG.integral_sq_ga
#print axioms LinnikCGLG.fourier_ga
#print axioms LinnikCGLPois8.poisson_S
#print axioms LinnikCGLPois8.fourier_ga_poisson
#print axioms LinnikCGLCount.count_le
#print axioms LinnikCGLAsum.sum_a_finite_le
#print axioms LinnikCGLNsum.fourier_ga_split
#print axioms LinnikCGLNsum.sum_a_fourier_ga_le
#print axioms LinnikCGLN0.sum_integral_g0_le
#print axioms LinnikCGLCov.integral_r_eq
#print axioms LinnikCGLCov.integral_gstar_le
#print axioms LinnikCGLSig2.sum_psi_norm_Phi_sq_le
#print axioms LinnikCGLSig2.norm_S2_le
#print axioms LinnikCGLFtil.integral_S2_le
#print axioms LinnikCGLFtil.sum_psi_norm_Phi_sq_le_ftil
#print axioms LinnikCGLJtil.sum_psi_norm_Phi_sq_le_J
#print axioms LinnikCGLJtil.sum_integral_Phi_le
#print axioms LinnikCGLTail.sum_integral_Phi_tail_le
#print axioms LinnikCGLTail.setIntegral_ga_tail_le
#print axioms LinnikCGLL82.lemma82_explicit
#print axioms LinnikCGLConst.sum_gw_le
#print axioms LinnikCGLConst.KX_le
#print axioms LinnikCGLForm.term2_parts
#print axioms LinnikCGLForm.lemma82_form
#print axioms LinnikCGLFtilP.integral_ftil_sq_le
#print axioms LinnikCGLFtilP.Lam_le
#print axioms LinnikCGLP81.cglp81
#print axioms LinnikCGLHBPos.dsum_le
#print axioms LinnikCGLHBPos.shat_sq_le
#print axioms LinnikCGLHBLen.cqU_mul_sig_le
#print axioms LinnikCGLHBLen.sig_le_lengthen
#print axioms LinnikCGLRefl0.reflect_gram0
#print axioms LinnikCGLRefl0.norm_gram_le0
#print axioms LinnikCGLHBRefl.sum_gram_sq_le
#print axioms LinnikCGLHBRefl.sig_le_refl
#print axioms LinnikCGLHBIter.caseB
#print axioms LinnikCGLHBIter.sig_bound
#print axioms LinnikCGLHB101.cglt101
#print axioms LinnikCGLHB101.cgls3
#print axioms LinnikCGLHB101.prop31
#print axioms LinnikCGLDensity.cglDensity
#print axioms LinnikCGLSteps.charDensity_s0
#print axioms LinnikCGLSteps.charDensity_s29
#print axioms LinnikCGLSteps.charDensity_inT
#print axioms SieveCurve7D.counts_7d
#print axioms SieveBuch.Par.decomp8
#print axioms SieveQ8.leaves_ev8
#print axioms SieveDeep.okIB_of_okD
#print axioms SieveDeep.Ch3_le
#print axioms SieveRough.shareBox
#print axioms SieveDrop8.share8D
#print axioms SieveDrop8.E1_le
#print axioms SieveDrop8.dT_le_cost
#print axioms SieveDrop8.drop_ev8
#print axioms SieveMain8.linnik_route_lt8
#print axioms SieveDeep.totalD_eq_rowsJD
#print axioms SieveTypeIIU22000D.window_22000d
#print axioms SieveTypeIIU22000D.typeII_22000d
#print axioms SieveCert.gridOK22000E
#print axioms SieveCert.gridOKC22000E
#print axioms SieveDeep.totalD_lt_22000E
#print axioms Linnik22000E.fits22000E
#print axioms Linnik22000E.deepGrid22000E
#print axioms Linnik22000E.linnik_22000e
#print axioms SieveCurve7D.g7d_le_lin
#print axioms LinnikG7.charDensity_g7d
#print axioms LinnikG7.linnik_g7d
#print axioms LinnikDetect.LSeries_aXχ
#print axioms LinnikDetect.detect_identityχ
#print axioms LinnikDetect.dichotomy
#print axioms LinnikDensity.class1_count
#print axioms LinnikDensity.class2_count
#print axioms LinnikDensity.count_nontrivial
#print axioms LinnikDensity.charDensity_of_LBound
#print axioms LinnikDensity.charDensity_of_critBound
#print axioms LinnikDensity.linnik_of_critBound
#print axioms LinnikDensity.LFunction_split
#print axioms LinnikDensity.norm_LFunction_half_le
#print axioms LinnikDensity.critBoundχ_half
#print axioms LinnikDensity.linnik_four
#print axioms LinnikFE.rootNumber_inv
#print axioms LinnikFE.rootNumber_mul_inv
#print axioms LinnikFE.norm_rootNumber
#print axioms LinnikFE.norm_Gamma_mul_sin_le
#print axioms LinnikFE.norm_LFunction_one_sub_le
#print axioms LinnikLindelof.norm_LFunction_le_zeta32
#print axioms LinnikLindelof.inv_norm_LFunction_le_zeta32
#print axioms LinnikLindelof.logDeriv_le_interp
#print axioms LinnikLindelof.lindelof
#print axioms LinnikSubconvex.primitive_bound
#print axioms LinnikSubconvex.prod_primeFactors_le
#print axioms LinnikSubconvex.critBoundχ
#print axioms LinnikSubconvex.linnik_seventeen_sixths
#print axioms MertensChi.LSeries_fχμ
#print axioms MertensChi.norm_sum_le_of
#print axioms MertensChi.norm_sum_le
#print axioms MertensChi.isBigO
#print axioms ShortCharSums.norm_sum_le
#print axioms ShortCharSums.norm_sum_le_rpow
#print axioms ShortCharSums.norm_sum_le_mul
#print axioms ShortCharSums.card_squares_sub_le
#print axioms LinnikGamma.norm_gammaFactor_ratio_le
#print axioms LinnikGamma.verticalIntegral_sub_eq
#print axioms LinnikGamma.afe
#print axioms LinnikFourth.norm_LFunction_four_le
#print axioms LinnikFourth.sum_norm_Pd_sq_le
#print axioms LinnikFourth.afeJ_split
#print axioms LinnikFourth.sum_norm_afeD_sq_le
#print axioms LinnikFourth.fourth_moment_primitive
#print axioms LinnikFourth.fourth_moment
#print axioms LinnikIngham.class2_count_ingham
#print axioms LinnikIngham.count_nontrivial_ingham
#print axioms LinnikIngham.charDensity_ingham
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikPower.card_divisors_le
#print axioms LinnikPower.pv_pow
#print axioms LinnikPower.hm_duality
#print axioms LinnikOffDiag.left_line
#print axioms LinnikOffDiag.norm_offK_le
#print axioms LinnikHuxley.power_count
#print axioms LinnikHuxley.class2_count_small
#print axioms LinnikHuxley.class1_huxley
#print axioms LinnikHuxley.count_huxley
#print axioms LinnikHuxley.charDensity_huxley
#print axioms LinnikHuxley.linnik_eighty_seven_thirty_fifths
#print axioms LinnikReflect.LFunction_eq_reflect
#print axioms LinnikReflect.hm_duality_W
#print axioms LinnikReflect.norm_hTerm_le_reflect
#print axioms LinnikReflect.huxley_core
#print axioms LinnikReflect.pair_kernel_one
#print axioms LinnikReflect.pair_kernel_two
#print axioms LinnikReflect.pair_sum_pointwise
#print axioms LinnikReflect.kernel_sum_le
#print axioms LinnikReflect.huxley_large_values
#print axioms LinnikTwelve.block_bin_hux
#print axioms LinnikTwelve.count_middle_c10
#print axioms LinnikTwelve.term1_le
#print axioms LinnikTwelve.term2_le
#print axioms LinnikTwelve.class1_twelve
#print axioms LinnikTwelve.count_twelve_fifths
#print axioms LinnikTwelve.charDensity_twelve_fifths
#print axioms LinnikTwelve.linnik_twelve_fifths
#print axioms LinnikMoment.moment_three
#print axioms LinnikMoment.moment_three_chars
#print axioms LinnikMoment.refined_moment
#print axioms LinnikMoment.refined_moment_cube
#print axioms LinnikMoment.refined_moment_chars
#print axioms LinnikGRH.charDensity_two_of_GRH
#print axioms LinnikGRH.linnik_two_of_GRH
#print axioms ShortPrimesHalfPlane.zeroFreeXi_of_halfplane
#print axioms LinnikWeylBridge.weylBound_of_PYWeyl

/- Results that no paper uses and nothing else printed here uses, kept for their own sake: each is named in
`formalisations/` (`scripts/dead_code.py`). -/
#print axioms BallTower.ballVol_lt_five
#print axioms BallTower.sphereArea_lt_seven
#print axioms BallTower.completing_factor_unique
#print axioms BohrJoins.completed_eq_sphereArea_bohr
#print axioms BohrJoins.shell_radii_tendsto
#print axioms BohrJoins.shell_unconditional
#print axioms BohrJoins.zero_pair_of_not_RH
#print axioms BohrJoins.shell_eleven_twelfths
#print axioms CubeBall.cube_distortion
#print axioms CubeBall.exists_unit_seq_tendsto_inner
#print axioms CubeBall.isEmpty_homeomorph_ball_hilbertCube
#print axioms CubeBall.line_inside_cube_not_in_ell2
#print axioms CubeBall.no_isometry_cube
#print axioms CubeBall.norm_zCube_eq_one_iff
#print axioms CubeBall.tendsto_ball_div_cube
#print axioms CubeBall.tendsto_inner_ellUnit
#print axioms CubeBall.vLp_mem_sphere_iff
#print axioms Orthogonality.pythagoras_lpGauge_iff
#print axioms Orthogonality.tendsto_mean_sq_norm_primeSum
#print axioms Eis.quadR_neg_one
#print axioms Eis.quad_recip
#print axioms Eis.kub_int
#print axioms Eis.kub2_mul
#print axioms Eis.summable_eisTerm
#print axioms Eis.eis1_slAct
#print axioms QuadIdeals.trichotomy
#print axioms VinoRec.vmvt_weak
#print axioms WeilForm.rh_of_relgap
#print axioms HalfPlaneJoins.QK3_rate_eleven_twelfths
#print axioms HalfPlaneJoins.chi3_rate_eleven_twelfths

/- Criteria for RH and GRH: Weil's for `ζ` and its forms, the library's own, those for Dirichlet and Dedekind
`L`-functions, Pólya's, and the sphere of the Bohr vectors. -/
#print axioms AngularFamily.rh_of_member_zero
#print axioms CrossCriteria.rh_of_liouville_theta
#print axioms Dedekind4.rh_grh_iff_QK_subexp
#print axioms Dedekind4.rh_grh_iff_QK_twins
#print axioms Dedekind4.rh_grh_of_member_zero
#print axioms PsiOmega.grh_iff_QC_subexp
#print axioms PsiOmega.grh_iff_QC_subexp_all
#print axioms PsiOmega.grh_iff_QC_subexp_chi4
#print axioms PsiOmega.grh_iff_twins_chi3
#print axioms PsiOmega.grh_iff_twins_chi4
#print axioms PsiOmega.grh_iff_twins_chi8
#print axioms PsiOmega.rh_of_liouville_bound
#print axioms PsiOmega.rh_of_polya
#print axioms WeilForm.line_of_RH
#print axioms WeilForm.line_of_weil_twins
#print axioms WeilForm.rh_iff_lam_subexp
#print axioms WeilForm.rh_iff_twins_subexp
#print axioms WeilForm.rh_of_D_and_realRooted
#print axioms WeilForm.rh_of_D_and_realRooted_final
#print axioms WeilForm.rh_of_D_and_realRooted_proved
#print axioms WeilForm.rh_of_Xi_params
#print axioms WeilForm.rh_of_dodging
#print axioms WeilForm.rh_of_dodging_final
#print axioms WeilForm.rh_of_eventually_simple
#print axioms WeilForm.rh_of_groundStates_dodging
#print axioms WeilForm.rh_of_ground_states
#print axioms WeilForm.rh_of_hypConv_top
#print axioms WeilForm.rh_of_no_crossing
#print axioms WeilForm.rh_of_pairing_and_realRooted
#print axioms WeilForm.rh_of_parity_gap
#print axioms WeilForm.rh_of_prime_side
#print axioms WeilForm.rh_of_prime_side_cross
#print axioms WeilForm.rh_of_realRooted_limit
#print axioms WeilForm.rh_of_simple_ground_states
#print axioms WeilForm.rh_of_simple_ground_states'
#print axioms WeilForm.rh_of_weil
#print axioms WeilForm.rh_of_weil_twins
#print axioms WeilForm.weil_criterion_finite
#print axioms WeilForm.weil_criterion_zeta
#print axioms WeilTwinGeneral.grh_iff_twins_chi7
#print axioms WeilTwinGeneral.line_of_twins_g
#print axioms WeilTwinGeneral.rh_grh_iff_QKχ_twins
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q3
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q4
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q7
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q8
#print axioms WeilTwinGeneral.rh_iff_twins_box
#print axioms WeilTwinGeneral.rh_iff_twins_concave
#print axioms WeilTwinGeneral.rh_iff_twins_realRooted
#print axioms BohrSphere.riemannHypothesis_iff_mem_sphere
#print axioms BohrSphere.riemannHypothesis_iff_tendsto

/- The Weil form of `ζ`: the bounds for its ground energies, the uniqueness of its ground state at small supports,
its negative index, and the structure of its ground states. -/
#print axioms WeilForm.first_failure
#print axioms WeilForm.lam_fails_exponentially
#print axioms WeilForm.lam_decay_uncond
#print axioms WeilForm.lamO_decay_uncond
#print axioms WeilForm.lam2_decay_uncond
#print axioms WeilForm.lam_dexp
#print axioms WeilForm.lamO_dexp
#print axioms WeilForm.lam2_dexp
#print axioms Kaiser.lam_kaiser
#print axioms HalfPlaneJoins.lam_prefactor_eleven_twelfths
#print axioms HalfPlaneJoins.weil_rate_eleven_twelfths
#print axioms WeilForm.groundState_energy_ge
#print axioms WeilForm.groundState_unique_035
#print axioms WeilForm.groundState_unique_below_log2
#print axioms WeilForm.groundState_unique_of_gap
#print axioms WeilForm.simpleGround_of_gap
#print axioms WeilForm.simple_of_pole_overlap
#print axioms WeilForm.pole_overlap_identity
#print axioms WeilForm.weilQg_ge_twentieth_all
#print axioms WeilForm.weilQ0_abs_le
#print axioms WeilForm.weilQ_symbol
#print axioms WeilForm.bil_zero_sum
#print axioms WeilForm.negIndex_eq_quadruples
#print axioms WeilForm.negDirections_unbounded
#print axioms WeilForm.exists_offline_of_neg_C2
#print axioms WeilForm.finrank_le_offline_zeta
#print axioms WeilForm.finrank_le_quadruples_C2
#print axioms WeilForm.theoremD
#print axioms WeilForm.chain_top_zeros
#print axioms WeilForm.zeros_real_or_imag'
#print axioms WeilForm.simple_iff_no_flat
#print axioms WeilForm.simple_not_flat
#print axioms WeilForm.simple_iff_no_green_pair
#print axioms WeilForm.degenerate_flat_fourier
#print axioms WeilForm.not_simple_iff_secular
#print axioms WeilForm.first_degeneracy_036
#print axioms WeilForm.hypConv_of_D
#print axioms WeilForm.pinned_zeta
#print axioms WeilForm.pinned_unconditional_zero
#print axioms WeilForm.realRooted_of_ae_concaveOn
#print axioms WeilForm.ghat_curvature
#print axioms WeilForm.exists_groundStates
#print axioms PsiOmega.QC_fails_rate
#print axioms PsiOmega.twins_rate_chi4
#print axioms WeilTwinGeneral.twins_rate_realRooted
#print axioms Dedekind4.QC_chi4_littleO
#print axioms Dedekind4.QK_littleO
#print axioms Dedekind4.QK_nonneg_of_member_zero

/- `ψ(x) − x` and `M(x)` are `Ω±(x^θ)` for every `θ < 1/2`, and the prime races mod 3, 4, 7 and 8; the Hadamard
product of `L(s, χ₋₄)`, and `ζ·L(χ₋₄)` as the radial member of the angular family. -/
#print axioms PsiOmega.psi_omega_half
#print axioms PsiOmega.mertens_omega_half
#print axioms PsiOmega.race_three_half
#print axioms PsiOmega.race_four_half
#print axioms PsiOmega.race_eight_half
#print axioms WeilTwinGeneral.race_seven_half
#print axioms PsiOmega.hadamard_chi4
#print axioms AngularFamily.member_zero_eq

/- The ideals of `ℤ[ω]` of prime-power norm; Heath-Brown's Lemmas 2 and 10 in general form; Kubota's `θ` is
nonzero and automorphic on `Γ_2`. -/
#print axioms Eis.card_ofNorm_inert
#print axioms Eis.card_ofNorm_split
#print axioms Eis.card_ofNorm_three
#print axioms Eis.fBound_gcd
#print axioms Eis.fBound_sep
#print axioms Eis.thetaL_ne_zero
#print axioms Eis.isAut_thS_Gam2
