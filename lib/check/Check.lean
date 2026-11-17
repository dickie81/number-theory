/- The axioms of the papers' theorems, the repository's default build target. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py`). -/
import Linnik21500
import LinnikG7
import PivotSharp
import BallFlat
import BallGap
import BallUpperEta
import OrbitWindow

/- Linnik's theorem with exponent `L = 43/20` (`2150/1000`), with no hypothesis: Theorem 1.2 of the Linnik paper
(`papers/linnik-exponent/main.tex`). Harman's sieve with the Type II estimate in two variables, whose density curve is
the trivial count below `7789/10000` and Huxley's estimate above (`SieveCurveHx`), a decomposition by trees of
Buchstab steps with the reversal of a term through its largest prime, and its certificate, the plan of a search that
the kernel follows by hints. Its one input that has not been refereed is the zero-free half-plane `Re s > 11/12`,
OpenAI's result, proved here along their companion preprint (`formalisations/openai-half-plane.md`); no estimate of
Ingham's or of Chen, Gupta and Li's is in its proof: its tests are those of the namespace `SieveAd.Plain`, with the
paper's conditions on the leaves of a comparison alone. The theorems of the first block of the paper's claims table
(Appendix A), in its order: its own steps by section (Sections 2 to 7), then the results of the literature it uses,
each with a note in `formalisations/`, then the classical deduction it compares with. The paper's Theorem 1.1, at
`21/10` (`Linnik21000.linnik_21000`), and the theorems of its Sections 8 to 10 are printed by `CheckAll.lean`: its
certificate is too heavy for the default build. -/
#print axioms Linnik21500.linnik_21500
#print axioms SieveTypeIIGen.CurveCounts
#print axioms SieveCurveHx.counts_hx
#print axioms SieveCurveHx.ghx_le_one
#print axioms SieveCurveHx.ghx_half
#print axioms SieveCurveHx.charDensity_hxT
#print axioms SieveTwoZone7D.Zone7d
#print axioms SieveFamilyTwo.typeIITwoAt_hx
#print axioms SieveTwoZone7D.typeII_two_hx
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeIIHM.sum_bin_hm_sq
#print axioms SieveTypeIIHM.hm_duality_wt
#print axioms SieveTypeIIHM.sum_typeII_two_bins
#print axioms SieveTypeIIHM.offK_bound
#print axioms LinnikOffDiag.norm_offK_le
#print axioms LinnikLindelof.lindelof
#print axioms SieveTypeIIHM.ZoneOK
#print axioms SieveTypeIIHM.twoBound
#print axioms SieveTypeIIHM.SqExp
#print axioms SieveTypeIIHM.sum_bin_two
#print axioms SieveTypeIIHM.bin_bound_two
#print axioms SieveTypeIIHM.typeII_two_gen
#print axioms SieveTwoZone7D.zone_hx
#print axioms SieveTwoZone7D.zone7d_orth
#print axioms SieveTypeIIHM.zonePiece_HH
#print axioms SieveTypeIIHM.zonePiece_of_ends
#print axioms SieveCount.card_A
#print axioms SieveCount.card_B
#print axioms SieveTypeIB.typeIB_bound_wide
#print axioms SieveSpline.typeIB_spline_wide
#print axioms SieveP6LeavesWide.leaves_chain_wide
#print axioms SieveP6LeavesWide.leavesOK_wide
#print axioms SieveTypeIBAsymWide.leaves_ib_wide
#print axioms SieveTypeIBPairWide.pair_le_wide
#print axioms SieveTypeIBSumWide.bdPW_le
#print axioms SieveFamilyTwo.typeII_sharp_two
#print axioms SieveFamilyTwo.pair_sum_eq
#print axioms SieveFamilyTwo.box_two
#print axioms SieveFamilyGen.sharp_gen
#print axioms SieveUnwTwo.typeII_unw_two
#print axioms SieveUnwGen.unw_gen
#print axioms SieveTwoCross.BilBd.cmp_list
#print axioms SieveTwoChain.chain_two
#print axioms SieveTwoTerm.chain2_bound
#print axioms SieveTwoComp.prop6_two_at
#print axioms SieveTwoComp.prop6_two
#print axioms SieveTreeStop.tree_weighted_stop
#print axioms SieveP6Tree.tree_chains
#print axioms SieveTwoP6.stops_bound2
#print axioms SieveTwoTerm.chainOK2_of_zone
#print axioms SieveP6TreeLeaves.tree_leaves_le
#print axioms SieveProp6.leaf_bound
#print axioms SieveBrun.fundamental
#print axioms SieveLeaf.prod_T_le
#print axioms SieveLeaf.prod_primesBelow_le
#print axioms SieveFillComp.prop6_fill_at
#print axioms SieveFillComp.prop6_fill
#print axioms SieveFillTree.tree_last
#print axioms SieveFill.stops_last_le
#print axioms SieveAd.famI_cut
#print axioms SieveAd.famI_buch
#print axioms SieveAd.famI_vanish_box
#print axioms SieveAd.Ttop_eq
#print axioms SieveDecomp.buchstab_pt
#print axioms SieveAd.Tree
#print axioms SieveAd.ok
#print axioms SieveAd.cost
#print axioms SieveAd.okI2
#print axioms SieveAd.Plain.okJ2
#print axioms SieveAd.Plain.okJ3
#print axioms SieveAd.Plain.fillTests_sound
#print axioms SieveAd.Plain.evJ_fill_core
#print axioms SieveAd.Plain.evJ_two_core
#print axioms SieveAd.Plain.evI_twoE
#print axioms SieveRough.psi_le
#print axioms SieveRough.Psi_le_buchstab
#print axioms SieveRough.super_M
#print axioms SieveOmegaB.omB_le_w1
#print axioms SieveCert.omegaC_le_w
#print axioms SieveOmegaB.omF_ge
#print axioms SieveOmegaB.lnT_ge
#print axioms SieveOmegaB.omB_mono
#print axioms SieveOmegaB.omB_anti
#print axioms SieveAd.dropCost_ge
#print axioms SieveAd.dropBCost_ge
#print axioms SieveAd.drop_bound
#print axioms SieveAd.dropB_bound
#print axioms SieveRough.shareBox
#print axioms SieveAd.shareBd
#print axioms SieveRough.evLe_box_tr
#print axioms SieveRough.evLe_box_ex
#print axioms SieveAd.famIR_eq
#print axioms SieveAd.famJR_eq
#print axioms SieveAd.dJF_level
#print axioms SieveAd.flip_cover
#print axioms SieveAd.flip_inject
#print axioms SieveAd.froz_weight_le
#print axioms SieveAd.Plain.frozTests_sound
#print axioms SieveAd.opsK
#print axioms SieveAd.Plain.frozTests
#print axioms SieveAd.frozRules
#print axioms SieveAd.flipOK
#print axioms SieveAd.Plain.flipCostD
#print axioms SieveAd.bd_flip_neg
#print axioms SieveAd.Plain.bd_flip_core
#print axioms SieveAd.Plain.bd_flipCostD
#print axioms SieveAd.sound
#print axioms SieveAd.Plain.altFD_sound
#print axioms SieveAd.linnik_pr
#print axioms SieveAd.linnik_bd
#print axioms SieveAd.Ttop_gB_ge
#print axioms SieveAd.solveG_sound
#print axioms SieveAd.Plain.solveD_sound
#print axioms SieveAd.Plain.pr_of_partD
#print axioms Linnik21500.tree21500
#print axioms Linnik21500.part21500
#print axioms Linnik21500.sound21500
#print axioms Linnik21500.soundF21500
#print axioms SieveAd.Plain.fillTestsF_eq
#print axioms SieveAd.Plain.frozTestsC_okI
#print axioms SieveAd.Plain.frozTestsC_okJ
#print axioms SieveAd.Plain.rules_frozC
#print axioms HalfPlanePNT.psi_isBigO_eleven_twelfths
#print axioms Eis.LFunction_ne_zero_of_re_gt
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikStairs7.charDensity_hx7_5
#print axioms LinnikStairs7.charDensity_hx7_19
#print axioms LinnikStep.charDensity_step
#print axioms LinnikReflect.hm_duality_W
#print axioms LinnikHybrid.mean_value_chars
#print axioms LinnikHybrid.large_values_chars
#print axioms LinnikFourth.fourth_moment
#print axioms Eis.kubotaTheta
#print axioms Eis.quadLargeSieve
#print axioms Eis.cub_recip
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.linnik_twelve
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikTwelve.linnik_twelve_fifths

/- Further theorems of the Linnik paper's claims table: the literature that the two theorems use (Chen, Gupta and
Li's Proposition 3.1 and the steps of the curve `g7d`, the Halász–Montgomery inequality, the bilinear Type I
estimate) and the classical deduction. -/
#print axioms LinnikCGLSteps.charDensity_s0
#print axioms LinnikCGLSteps.charDensity_inT
#print axioms LinnikCGLHB101.prop31
#print axioms LinnikCGLSteps.charDensity_s29
#print axioms SieveCurve7D.counts_7d
#print axioms SieveCurve7D.g7d_le_one
#print axioms SieveCurve7D.g7d_half
#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_in7_18
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikCGLMat.prop46
#print axioms LinnikCGLS2.cgls2
#print axioms LinnikCGLP81.cglp81
#print axioms LinnikCGLHB101.cgls3
#print axioms LinnikCGLHB101.cglt101
#print axioms LinnikCGLLV.cgl_all
#print axioms LinnikCGLStep.charDensity_cglGen
#print axioms LinnikG7.linnik_g7d

/- The orbit-lattice paper (`papers/orbit-lattice/main.tex`): under RH every pivot of the orbit with Gram matrix
`√(mn)·K_H(m/n)`, computed from the primes, is at least `0.0577` after the first (`formalisations/ball-rate.md`, "The
pivot inequality for every `k`"); hence RH holds if and only if every pivot is at least the first, and if and only if
the form is at least `K_H(1)` at every nonzero integer vector, which under RH makes `w_1` a shortest vector of the
lattice the orbit spans. The theorems of the paper's claims table (Appendix A): the
equivalences and the margin, the kernel and the positivity layer, the flat model, the window, and the steps of the
proof of the margin. -/
#print axioms PivotSharp.rh_iff_orbitLattice
#print axioms BallWeil.rh_of_pivots
#print axioms PivotSharp.orbitLattice_of_rh
#print axioms PivotSharp.rh_iff_shortest
#print axioms PivotSharp.shortest_of_rh
#print axioms PivotSharp.pivot_ge_rh
#print axioms PivotSharp.lattice_gap
#print axioms PivotSharp.shortest_unique
#print axioms PivotSharp.lattice_second
#print axioms BallHadamard.kerH_one
#print axioms BallHadamard.summable_hw
#print axioms BallHadamard.kerH_inv
#print axioms BallPsi.kerH_explicit
#print axioms BallWeil.rh_iff_form
#print axioms BallWeil.rh_iff_weil_bound
#print axioms BallHadamard.rh_iff_realizationH
#print axioms BallWeil.form_eq_norm_sq
#print axioms BallFlat.gram_flat
#print axioms BallFlat.kerFlat_eq_integral
#print axioms BallFlat.flat_pivot
#print axioms BallFlat.inner_increments
#print axioms WeilForm.weilExplicit_zeta
#print axioms PivotPhi.integral_phi_cos
#print axioms PivotPhi.phi_nonneg
#print axioms PivotPhi.phi_mul_le
#print axioms PivotPhi.phi_le_sq
#print axioms PivotPhi.phiE_strip
#print axioms PivotPhi.norm_phiE_I_le
#print axioms PivotPhi.differentiable_phiE
#print axioms PivotPhi.phiE_ofReal
#print axioms PivotSharp.prime_eq
#print axioms PivotMinorFT.integral_mu_cos_eq_zero
#print axioms PivotMinorFT.integral_mu_ge
#print axioms PivotCert.mu_le
#print axioms PivotSharp.pole_ge
#print axioms PivotSharp.form_ge
#print axioms PivotSharp.muLe
#print axioms PivotTop.mertens_le_uniform
#print axioms PivotTop.mertens_le_small
#print axioms PivotTop.top_bound
#print axioms OrbitWindow.form_eq_weilQg
#print axioms OrbitWindow.weilQg_hasSum
#print axioms OrbitWindow.weilQg_step_int_ge
