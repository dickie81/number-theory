/- The axioms of the papers' theorems, the repository's default build target. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py`). -/
import Linnik22475R
import Linnik22325R

/- The Linnik paper: its theorem, the theorem under the density hypothesis, the route, the certificate and the
Type II estimate on its window. -/
#print axioms Linnik22475R.linnik_22475r
#print axioms Linnik22475R.linnik_22475r_of
#print axioms SieveMain2.linnik_route_lt2
#print axioms SieveCert.total2_lt_22475R
#print axioms SieveTypeIIU22475C.typeII_22475c

/- The same route with the density curve `g7d` (Chen–Gupta–Li's Proposition 3.1 at every point of `[5/7, 131/168]`,
`LinnikCGLSteps`) at `L = 893/400`: its theorem, with no hypothesis, its certificate and the Type II estimate on its
window. `Linnik22475R` above is unchanged. -/
#print axioms Linnik22325R.linnik_22325r
#print axioms SieveCert.total2_lt_22325R
#print axioms SieveTypeIIU22325D.typeII_22325d
#print axioms LinnikCGLSteps.charDensity_s0

/- Two results of the literature that it uses (`formalisations/`): the zero-free half-plane `Re s > 11/12` for
every Dirichlet L-function, from OpenAI's release (`formalisations/openai-half-plane.md`), and Chen–Gupta–Li's
density estimate on `[5/7, 16/21]`. -/
#print axioms Eis.LFunction_ne_zero_of_re_gt
#print axioms LinnikCGLDensity.cglDensity

/- The other theorems of the Linnik paper's claims table (`papers/linnik-exponent/main.tex`, Section 7): its own steps
by section, then the results of the literature it uses, each with a note in `formalisations/`. -/
#print axioms SieveTypeIIU226C.counts_7c
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeIIHM.typeII_gen_hm
#print axioms SieveTypeIIU22475C.window_22475c
#print axioms SieveCount.card_A
#print axioms SieveCount.card_B
#print axioms SieveFamily.typeII_sharp
#print axioms SieveRough.psi_le
#print axioms SieveBuch.Par.decomp
#print axioms SieveDrop.drop_ev_of
#print axioms SieveBuch.Par.Kp2_le
#print axioms SieveBuch.Par.Kk_eq
#print axioms SieveKeptB.Kk_gB_ge
#print axioms SieveBuch.Par.decompk
#print axioms SieveDrop2.drop_ev2
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikStep.charDensity_step
#print axioms LinnikPower.hm_duality
#print axioms SieveProp6.prop6
#print axioms SieveBrun.fundamental
#print axioms SieveDecomp.buchstab_fam
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.linnik_twelve
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikTwelve.linnik_twelve_fifths
