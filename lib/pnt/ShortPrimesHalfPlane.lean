/-
# Primes in short intervals for every `θ > 11/17`, from the zero-free half-plane instead of Korobov–Vinogradov

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`short_primes_11_17_noKV`). For every `θ > 11/17`, every large `y` has a prime in `(y, y + y^θ]`. This is
the statement of `InghamDensity.short_primes_11_17`; only the zero-free input differs.

`ShortWeil.short_primes_of_density` (`lib/core/ShortPrimes.lean`) takes a density estimate `DensityXi A B` and a
zero-free region `ZeroFreeXi α` of width `(log T)^{−α}`, `α < 1`. `InghamDensity.short_primes_11_17` gets the second
from the Korobov–Vinogradov region (`ShortKV.zeroFreeXi_KV`, `α = 3/4`). Here the second comes from the zero-free
half-plane: the half-plane is `|Im τ| ≤ 5/12` for the zeros `τ` of Ξ in the library's normalisation
(`HalfPlaneJoins.abs_im_tau_le_five_twelfths`, `lib/core/HalfPlaneJoinsFinal.lean`), a region of constant width `1/12`,
which gives `ZeroFreeXi α` for every `α ≥ 0` with `T₀ = e` (`zeroFreeXi_of_halfplane`).

This is a second proof of the same result, not a stronger one: the density `DensityXi (17/6 + ε) 12` is the same
(`InghamDensity.densityXi_17_6`) and `11/17 = 1 − 1/(17/6)` is fixed by it. It removes the Korobov–Vinogradov dependency and
leaves the zero-free half-plane (`Re s > 11/12`) as the only analytic input; it is not independent of the half-plane
(the density `InghamDensity.densityXi_17_6` itself goes through `Subconvexity.zetaCritBound_five_24`, which uses it). The
library keeps `InghamDensity.short_primes_11_17` (half-plane and Korobov–Vinogradov) and `DetectEM.short_primes` (the
unconditional `θ > 3/4`, Korobov–Vinogradov and no half-plane) as they are.

* `zeroFreeXi_of_halfplane`: `0 ≤ α → ZeroFreeXi α`.
* `short_primes_11_17_noKV`: `11/17 < θ → ∀ᶠ y, ∃ p prime, y < p ∧ p ≤ y + y^θ`, by `short_primes_of_density` with
  `A = 17/6 + ε`, `B = 12` and `ε = (1/(1 − θ') − 17/6)/2` for `θ' = min θ (3/4)`; `y^{θ'} ≤ y^θ` for `y ≥ 1`.
-/
import ShortPrimes
import HalfPlaneJoinsFinal
import InghamDensity

open ShortWeil

namespace ShortPrimesHalfPlane

/-- The zero-free half-plane gives `ZeroFreeXi α` for every `α` (here `α < 1` is what `short_primes_of_density` takes),
with no Korobov–Vinogradov input. -/
theorem zeroFreeXi_of_halfplane {α : ℝ} (hα : 0 ≤ α) : ZeroFreeXi α := by
  refine ⟨1 / 12, Real.exp 1, by norm_num, fun T hT i _ => ?_⟩
  have h5 := HalfPlaneJoins.abs_im_tau_le_five_twelfths i
  have hlog : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    simpa using this
  have hpow : 1 ≤ Real.log T ^ α := Real.one_le_rpow hlog hα
  have : (1 / 12 : ℝ) / Real.log T ^ α ≤ 1 / 12 := div_le_self (by norm_num) hpow
  linarith

end ShortPrimesHalfPlane

#print axioms ShortPrimesHalfPlane.zeroFreeXi_of_halfplane
