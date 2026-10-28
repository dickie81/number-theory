/- The axioms of the papers' theorems, the repository's default build target. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py`). -/
import Linnik22250R
import LinnikG7

/- The Linnik paper: its theorem with the density curve `g7d` (Chen–Gupta–Li's Proposition 3.1 on `[5/7, 131/168]`,
`LinnikCGLSteps`) at `L = 89/40`, with no hypothesis, the sieve route, its certificate and the Type II estimate on its
window. Earlier theorems, at weaker exponents and with their own certificates, are no longer in the tree: see the git
history. -/
#print axioms Linnik22250R.linnik_22250r
#print axioms SieveMain2.linnik_route_lt2
#print axioms SieveMain2.linnik_large2
#print axioms SieveCert.total2_lt_22250R
#print axioms SieveCert.gridOK22250R
#print axioms SieveCert.gridOKC22250R
#print axioms SieveTypeIIU22250D.typeII_22250d
#print axioms LinnikCGLSteps.charDensity_s0
#print axioms LinnikCGLSteps.charDensity_inT
#print axioms LinnikCGLHB101.prop31
#print axioms LinnikCGLSteps.charDensity_s109
#print axioms SieveTypeIIU22250D.counts_7d
#print axioms SieveTypeIIU22250D.g7d_le_one
#print axioms SieveTypeIIU22250D.g7d_half
#print axioms SieveTypeIIU22250D.window_22250d

/- Two results of the literature that it uses (`formalisations/`): the zero-free half-plane `Re s > 11/12` for
every Dirichlet L-function, from OpenAI's release (`formalisations/openai-half-plane.md`), printed here, and
Chen–Gupta–Li's density estimate, whose steps and Proposition 3.1 are printed above (`cglDensity`, the same estimate on
`[5/7, 16/21]`, is not used by `Linnik22250R` and is printed by `CheckAll`). -/
#print axioms Eis.LFunction_ne_zero_of_re_gt

/- The other theorems of the Linnik paper's claims table (`papers/linnik-exponent/main.tex`, Section 7): its own steps
by section, then the results of the literature it uses, each with a note in `formalisations/`. -/
#print axioms HalfPlanePNT.psi_isBigO_eleven_twelfths
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeIIHM.sum_bin_hm
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
#print axioms SieveRoughTuple.sum_rough_eq
#print axioms SieveRough.psi_le
#print axioms SieveProp6.prop6
#print axioms SieveTree.tree_pt
#print axioms SieveBrun.fundamental
#print axioms SieveDecomp.buchstab_fam
#print axioms SieveBuch.Par.decomp
#print axioms SieveQ.leaves_ev
#print axioms SieveDrop.drop_ev_of
#print axioms SieveBuch.Par.Kp2_le
#print axioms SieveBuch.Par.Kk_eq
#print axioms SieveKeptLeaf.lf_Kk
#print axioms SieveKeptB.Kk_gB_ge
#print axioms SieveBuch.Par.decompk
#print axioms SieveKeptLeaf.leaves_ev2
#print axioms SieveDrop2.drop_ev2
#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_in7_18
#print axioms LinnikStairs7.charDensity_hx7_5
#print axioms LinnikStairs7.charDensity_hx7_19
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikStep.charDensity_step
#print axioms LinnikPower.hm_duality
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.linnik_twelve
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikTwelve.linnik_twelve_fifths
#print axioms LinnikG7.charDensity_g7d
#print axioms LinnikG7.linnik_g7d
