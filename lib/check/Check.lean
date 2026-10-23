/- The axioms of the papers' theorems, the repository's default build target. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py`). -/
import Linnik22475R

/- The Linnik paper: its theorem, the theorem under the density hypothesis, the route, the certificate and the
Type II estimate on its window. -/
#print axioms Linnik22475R.linnik_22475r
#print axioms Linnik22475R.linnik_22475r_of
#print axioms SieveMain2.linnik_route_lt2
#print axioms SieveCert.total2_lt_22475R
#print axioms SieveTypeIIU22475C.typeII_22475c

/- Two results of the literature that it uses (`formalisations/`): the zero-free half-plane `Re s > 11/12` for
every Dirichlet L-function, from OpenAI's release (`formalisations/openai-half-plane.md`), and Chen–Gupta–Li's
density estimate on `[5/7, 16/21]`. -/
#print axioms Eis.LFunction_ne_zero_of_re_gt
#print axioms LinnikCGLDensity.cglDensity
