/-
# The zero-free region `ZeroFreeXi α` from the zero-free half-plane instead of Korobov–Vinogradov

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`ShortWeil.short_primes_of_density` (`lib/core/ShortPrimes.lean`) takes a density estimate `DensityXi A B` and a
zero-free region `ZeroFreeXi α` of width `(log T)^{−α}`, `α < 1`. The Korobov–Vinogradov region gives the second
with `α = 3/4` (`ShortKV.zeroFreeXi_KV`). Here the second comes from the zero-free half-plane: the half-plane is
`|Im τ| ≤ 5/12` for the zeros `τ` of Ξ in the library's normalisation (`HalfPlaneJoins.abs_im_tau_le_five_twelfths`,
`lib/core/HalfPlaneJoinsFinal.lean`), a region of constant width `1/12`, which gives `ZeroFreeXi α` for every `α ≥ 0`
with `T₀ = e` (`zeroFreeXi_of_halfplane`).

* `zeroFreeXi_of_halfplane`: `0 ≤ α → ZeroFreeXi α`.
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
