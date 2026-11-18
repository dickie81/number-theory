/-
# The route at `x = q^L`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `L` is a route's exponent (`SieveRoute.Route`).

* `IBFits`: the exponent `Lnum/Lden` of the bilinear Type I rule (`SieveCert.IBPar`) is the route's `L`.
* `xq q = q^L`, and `xpow`: `(q^L)^s = q^{Ls}`.
* `ev_rpow`: for `c > 0` and any `B`, eventually `B ≤ q^c`.

The file imports `SieveLeaves.lean`.
-/
import SieveLeaves

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveLeaves SieveRoute
open SieveCert (DEN U1 U2)

namespace SieveQ

open Classical

/-- **The bilinear Type I rule's exponent is the route's**: `Lnum/Lden = L`. -/
class IBFits [Route] [SieveCert.IBPar] : Prop where
  L_eq : (SieveCert.IBPar.Lnum : ℝ) / SieveCert.IBPar.Lden = L

variable [Route] [RouteOK] [SieveCert.Grid]

omit [RouteOK] [SieveCert.Grid] in
theorem xpow (q : ℕ) (s : ℝ) : ((q : ℝ) ^ L) ^ s = (q : ℝ) ^ (L * s) :=
  (Real.rpow_mul (Nat.cast_nonneg q) _ _).symm

omit [Route] [RouteOK] [SieveCert.Grid] in
theorem ev_rpow {c : ℝ} (hc : 0 < c) (B : ℝ) : ∀ᶠ q : ℕ in atTop, B ≤ (q : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- `x = q^L`. -/
noncomputable abbrev xq (q : ℕ) : ℝ := (q : ℝ) ^ L

end SieveQ
