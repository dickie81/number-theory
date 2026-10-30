/- The axioms of the papers' theorems, the repository's default build target. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py`). -/
import Linnik22000E
import LinnikG7

/- Linnik's theorem with exponent `L = 11/5`, with no hypothesis: the sieve route with the density curve `g7d`
(Chen–Gupta–Li's Proposition 3.1 on `[5/7, 131/168]`, `LinnikCGLSteps`), the bilinear Type I estimate and the
decomposition to depth 8, its certificate and the Type II estimate on its window. The theorem at `278/125` with the
refined certificate (`Linnik22240R.linnik_22240r`) is printed by `CheckAll`. Earlier theorems, at weaker exponents and
with their own certificates, are no longer in the tree: see the git history. -/
#print axioms Linnik22000E.linnik_22000e
#print axioms SieveMain8.linnik_route_lt8
#print axioms SieveMain8.linnik_large8
#print axioms SieveDeep.totalD_lt_22000E
#print axioms SieveCert.gridOK22000E
#print axioms SieveCert.gridOKC22000E
#print axioms Linnik22000E.routeOK22000D
#print axioms Linnik22000E.fits22000E
#print axioms Linnik22000E.deepGrid22000E
#print axioms SieveTypeIIU22000D.typeII_22000d
#print axioms LinnikCGLSteps.charDensity_s0
#print axioms LinnikCGLSteps.charDensity_inT
#print axioms LinnikCGLHB101.prop31
#print axioms LinnikCGLSteps.charDensity_s29
#print axioms SieveTypeIIU22240D.counts_7d
#print axioms SieveTypeIIU22240D.g7d_le_one
#print axioms SieveTypeIIU22240D.g7d_half
#print axioms SieveTypeIIU22000D.window_22000d

/- Two results of the literature that it uses (`formalisations/`): the zero-free half-plane `Re s > 11/12` for
every Dirichlet L-function, OpenAI's result, proved here along their companion preprint
(`formalisations/openai-half-plane.md`), printed here, and Chen–Gupta–Li's density estimate, whose steps and
Proposition 3.1 are printed above (`cglDensity`, their estimate with the exponent `7/3 + ε` on `[5/7, 16/21]`, is not
used by `Linnik22000E` or `Linnik22240R` and is printed by `CheckAll`). -/
#print axioms Eis.LFunction_ne_zero_of_re_gt

/- The other theorems of the Linnik paper's claims table (`papers/linnik-exponent/main.tex`, Appendix A): its own steps
by section, then the results of the literature it uses, each with a note in `formalisations/`. -/
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeIIHM.sum_bin_hm
#print axioms SieveTypeIIHM.sum_typeII_bins_hm
#print axioms SieveTypeIIHM.offK_bound
#print axioms LinnikOffDiag.norm_offK_le
#print axioms LinnikLindelof.lindelof
#print axioms SieveTypeIIHM.bin_bound_gen_hm
#print axioms SieveTypeIIHM.typeII_gen_hm
#print axioms SieveCount.card_A
#print axioms SieveCount.card_B
#print axioms SieveFamily.typeII_sharp
#print axioms SieveTypeIIU.typeII_unw
#print axioms SieveChain.chainTU_bound
#print axioms SieveChain.chainTL_bound
#print axioms SieveExact.chainT0_bound
#print axioms SieveChain.sum_rough_tuples
#print axioms SieveProp6.prop6
#print axioms SieveTree.tree_pt
#print axioms SieveStops2.stops2_bound
#print axioms SieveProp6.leaf_bound
#print axioms SieveLeaf.leaf_gap
#print axioms SieveBrun.fundamental
#print axioms SieveLeaf.prod_T_le
#print axioms SieveLeaf.prod_primesBelow_le
#print axioms SieveDecomp.buchstab_fam
#print axioms SieveBuch.Par.T_eq
#print axioms SieveBuch.Par.I_S1
#print axioms SieveBuch.Par.I_S2
#print axioms SieveBuch.Par.I_S3
#print axioms SieveBuch.Par.I_S4
#print axioms SieveBuch.Par.I_S5
#print axioms SieveBuch.Par.I_S6
#print axioms SieveBuch.Par.lvl1k
#print axioms SieveBuch.Par.I_S3c_vanish
#print axioms SieveBuch.Par.I_S4c_vanish_lt
#print axioms SieveBuch.Par.I_S4c_vanish_reg
#print axioms SieveBuch.Par.I_S5c_vanish_lt
#print axioms SieveBuch.Par.I_S5c_vanish_reg
#print axioms SieveBuch.Par.I_S6c_vanish_lt
#print axioms SieveBuch.Par.I_S6c_vanish_reg
#print axioms SieveQ.leaves_ev
#print axioms SieveRough.psi_le
#print axioms SieveRough.Psi_le_buchstab
#print axioms SieveRough.super_M
#print axioms SieveOmegaB.omB_le_w1
#print axioms SieveCert.omegaC_le_w
#print axioms SieveOmegaB.omF_ge
#print axioms SieveOmegaB.lnT_ge
#print axioms SieveOmegaB.omB_mono
#print axioms SieveOmegaB.omB_anti
#print axioms SieveRough.evLe_cell_tr
#print axioms SieveRough.evLe_cell_ex
#print axioms SieveOmegaB.log_le_half_sub_inv
#print axioms SieveCert.bound2_ge
#print axioms SieveCert.bound4_ge
#print axioms SieveCert.bound6_ge
#print axioms SieveDrop.drop2_le
#print axioms SieveDrop.drop4_le
#print axioms SieveDrop.drop6_le
#print axioms SieveDrop.shares_ev
#print axioms SieveDrop.corner_le
#print axioms SieveDrop.corner_ev
#print axioms SieveBuch.Par.Kp2_le
#print axioms SieveBuch.Par.Kk_eq
#print axioms SieveKeptLeaf.lf_Kk
#print axioms SieveKeptB.Kk_gB_ge
#print axioms SieveRoughLo.evGe_cell_tr
#print axioms SieveOmegaB.two_mul_div_le_log
#print axioms SieveBuch.Par.decompk
#print axioms SieveKeptLeaf.leaves_ev2
#print axioms SieveDrop2.drop_ev2
#print axioms HalfPlanePNT.psi_isBigO_eleven_twelfths
#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_in7_18
#print axioms LinnikStairs7.charDensity_hx7_5
#print axioms LinnikStairs7.charDensity_hx7_19
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikStep.charDensity_step
#print axioms LinnikPower.hm_duality
#print axioms LinnikHybrid.mean_value_chars
#print axioms LinnikHybrid.large_values_chars
#print axioms LinnikFourth.fourth_moment
#print axioms LinnikCGLMat.prop46
#print axioms LinnikCGLS2.cgls2
#print axioms LinnikCGLP81.cglp81
#print axioms LinnikCGLHB101.cgls3
#print axioms LinnikCGLHB101.cglt101
#print axioms Eis.kubotaTheta
#print axioms Eis.quadLargeSieve
#print axioms Eis.cub_recip
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.linnik_twelve
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikTwelve.linnik_twelve_fifths
#print axioms SieveTypeIIU22240D.g7d_le_lin
#print axioms LinnikG7.charDensity_g7d
#print axioms LinnikG7.linnik_g7d
