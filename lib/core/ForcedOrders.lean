import Mathlib
import CMHost

/-!
# The forced orders

Part of layer L7 of the sharp frontier for the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`):
the forced orders `Fo(𝒫_u)`, an explicit function of the parameters that the frontier pins (spec L7.4). They are
defined from the parameters only: the ranks `(k, m, t)` and the Harish-Chandra family `hc` of L0, the two split
primes `g₀, g₁` and the cut `X″` of L7.1, which are inputs here.

For `1 ≤ j ≤ m` the weight is `w_j = e_{j−1}`; here `j` is `J + 1` for `J : Fin m`, so `w_j = wj hc J`.
* **At `p ∈ {g₀, g₁}`** (`FTypeG`): `−½·Σ_τ (Σ_{i<k+j−1} |a⁺_{j,τ,i}| + Σ_{c<m−j} |a⁻_{j,τ,c}|)`, with
  `a⁺ = σ_i + e_{j−1} − (nV − 1 − 2i)/2 − ((k + j − 1) − (m − j))/2`, `σ_i = v_i` for `i < k − 1` and `−b_{i−k+1}`
  beyond, and `a⁻ = b_{j+c} − e_{j−1} − (t + 1 + 2c)/2`.
* **At `p = d`** (`FRamD`): `−((k − 1)/2)·Σ_{t∈A} min(w_j(1, t), w_j(−1, t))`.
* **At inert or signal `p ≤ X″`** (`FInert`): `Σ_ρ (k − 1)w_j(ρ)/(p² − 1)` if `p` is inert with `hP(p) = 1`, and
  otherwise `nP(p)⁻¹·Σ_{z∈Φ} lpF(p, nP(p), s ↦ (k − 1)·w_j(pos_p(z; s)))`, where (`lpF`)
  `lpF(ℓ, n, D) = ℓ/(ℓ² − 1)·Σ_s D(s) − max{Σ x_{s,i} : x ≥ 0, x_{s,i} = 0 unless i odd < n,
  Σ_i ℓ^i x_{s,i} + Σ_i x_{s−i,i} ≤ D(s)}`.

Then `Fo = 2·Σ_j [FTypeG(j)·log(g₀g₁) + FRamD(j)·log d + Σ_{p ≤ X″ inert/signal} FInert(j, p)·log p]` (`Fo`), and
in the library's units, which halve the archive's (`KLattice`, "The factor 2"), it is `FoLib = Fo/2`.

**Checks.** `0 ≤ lpF(ℓ, n, D) ≤ ℓ/(ℓ² − 1)·Σ D` for `ℓ > 1` and `D ≥ 0` (`lpF_nonneg_le`, the archive's
`FactLpF`); `FTypeG ≤ 0` (`FTypeG_nonpos`); and `FInert ≥ 0` for nonnegative weights (`FInert_nonneg`).
`Fo`, `FoLib`, `FRamD` and `inertPrimes` are meant for the frontier `SharpBound` (L7.5).

**Choices.**
* The LP's maximum is the `sSup` in `ℝ` of `Σ x` over the feasible real `x ≥ 0`; the feasible set is bounded for
  `ℓ ≥ 1`, closed and, for `D ≥ 0`, contains `0`, so the `sSup` is the maximum. (For an infeasible `D` it is `0`.)
* The orbit index `s` runs over `Fin n`, read cyclically: `s − i` is `Fin`'s subtraction mod `n`. So `D` is a
  function on `Fin n`, and the positions `pos_p(z; s)` have period `nP(p)`.
* The sum over primes is over `p ≤ ⌊X″⌋` with `p ∤ N` and `cls p` inert or signal; `p ∤ N` keeps `p = d` (handled
  by `FRamD`) out, as `cls` is meant for `p ∤ N` only. "`hP(p) = 0`" of the spec is `hP(p) = 1` in `A`'s
  multiplicative notation.
* Everything is real-valued. `σ_i` is `0` past `i ≥ r`, which the sums never reach.
-/

open Finset

namespace ZetaBalance.Setting

/-! ## The linear program -/

/-- The feasible set of the LP of `lpF(ℓ, n, D)`: `x ≥ 0`, `x_{s,i} = 0` unless `i` is odd, and
`Σ_i ℓ^i x_{s,i} + Σ_i x_{s−i,i} ≤ D(s)` for every `s`, with `s − i` taken mod `n`. -/
def LpFeasible (ℓ : ℝ) (n : ℕ) (D : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ s i, 0 ≤ x s i) ∧ (∀ s i, ¬ Odd i.val → x s i = 0) ∧
    ∀ s, ∑ i, ℓ ^ i.val * x s i + ∑ i, x (s - i) i ≤ D s

/-- `lpF(ℓ, n, D) = ℓ/(ℓ² − 1)·Σ_s D(s) − max_x Σ x_{s,i}`, the maximum being the `sSup` over `LpFeasible`. -/
noncomputable def lpF (ℓ : ℝ) (n : ℕ) (D : Fin n → ℝ) : ℝ :=
  ℓ / (ℓ ^ 2 - 1) * ∑ s, D s - sSup {y | ∃ x, LpFeasible ℓ n D x ∧ y = ∑ s, ∑ i, x s i}

variable {S : Setting} (R : S.Ranks) (hc : R.HCFamily)

namespace Ranks

/-! ## The local forced orders -/

/-- `σ_i = v_i` for `i < k − 1` and `−b_{i−k+1}` beyond (and `0` from `r` on). -/
def sig (H : R.HC) (i : ℕ) : ℤ :=
  if h : i < R.k - 1 then H.v ⟨i, h⟩ else if h' : i - (R.k - 1) < R.m then -H.b ⟨i - (R.k - 1), h'⟩ else 0

/-- `a⁺_{j,i} = σ_i + e_{j−1} − (nV − 1 − 2i)/2 − ((k + j − 1) − (m − j))/2`, for `j = J + 1`. -/
noncomputable def aPlus (H : R.HC) (J : Fin R.m) (i : ℕ) : ℝ :=
  R.sig H i + H.e J - ((R.nV : ℝ) - 1 - 2 * i) / 2 - (((R.k : ℝ) + J) - ((R.m : ℝ) - J - 1)) / 2

/-- `a⁻_{j,c} = b_{j+c} − e_{j−1} − (t + 1 + 2c)/2`, for `j = J + 1` and `c < m − j` (`b` is 0-based). -/
noncomputable def aMinus (H : R.HC) (J : Fin R.m) (c : Fin (R.m - J - 1)) : ℝ :=
  H.b ⟨J + 1 + c, by have := c.2; omega⟩ - H.e J - ((R.t : ℝ) + 1 + 2 * c) / 2

/-- The forced order at `p ∈ {g₀, g₁}`:
`FTypeG(j) = −½·Σ_τ (Σ_{i<k+j−1} |a⁺_{j,τ,i}| + Σ_{c<m−j} |a⁻_{j,τ,c}|)`, for `j = J + 1`. -/
noncomputable def FTypeG (J : Fin R.m) : ℝ :=
  -(1 / 2) * ∑ τ, (∑ i : Fin (R.k + J), |R.aPlus (hc τ) J i| + ∑ c, |R.aMinus (hc τ) J c|)

/-- The forced order at `p = d`: `FRamD(j) = −((k − 1)/2)·Σ_{t∈A} min(w_j(1, t), w_j(−1, t))`. -/
noncomputable def FRamD (J : Fin R.m) : ℝ :=
  -(((R.k : ℝ) - 1) / 2) * ∑ t : S.A, (min (R.wj hc J (1, t)) (R.wj hc J (-1, t)) : ℝ)

/-- The forced order at an inert or signal `p`: `Σ_ρ (k − 1)w_j(ρ)/(p² − 1)` if `p` is inert with `hP(p) = 1`,
and `nP(p)⁻¹·Σ_z lpF(p, nP(p), s ↦ (k − 1)·w_j(pos_p(z; s)))` otherwise. -/
noncomputable def FInert (J : Fin R.m) (p : ℕ) : ℝ :=
  if S.cls p = .inert ∧ S.hP p = 1 then ∑ ρ, ((R.k : ℝ) - 1) * R.wj hc J ρ / ((p : ℝ) ^ 2 - 1)
  else (S.nP p : ℝ)⁻¹ * ∑ z, lpF p (S.nP p) fun s => ((R.k : ℝ) - 1) * R.wj hc J (S.pos p z s)

/-! ## The forced orders -/

/-- The primes `p ≤ X″` with `p ∤ N` that are inert or signal. -/
noncomputable def inertPrimes (X'' : ℝ) : Finset ℕ :=
  (range (⌊X''⌋₊ + 1)).filter fun p => p.Prime ∧ ¬ p ∣ S.N ∧ S.cls p ≠ .split

/-- The forced orders in the library's units:
`Σ_j [FTypeG(j)·log(g₀g₁) + FRamD(j)·log d + Σ_{p ≤ X″ inert/signal} FInert(j, p)·log p]`. -/
noncomputable def FoLib (g₀ g₁ : ℕ) (X'' : ℝ) : ℝ :=
  ∑ J, (R.FTypeG hc J * Real.log (g₀ * g₁) + R.FRamD hc J * Real.log S.d +
    ∑ p ∈ inertPrimes (S := S) X'', R.FInert hc J p * Real.log p)

/-- The forced orders `Fo(𝒫_u)` in the archive's units, twice `FoLib`. -/
noncomputable def Fo (g₀ g₁ : ℕ) (X'' : ℝ) : ℝ := 2 * R.FoLib hc g₀ g₁ X''

end Ranks

/-! ## Checks -/

/-- Shifting the orbit index: `Σ_s Σ_i x_{s−i,i} = Σ_s Σ_i x_{s,i}`. -/
theorem sum_sum_sub {n : ℕ} (x : Fin n → Fin n → ℝ) : ∑ s, ∑ i, x (s - i) i = ∑ s, ∑ i, x s i := by
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  cases n with
  | zero => exact i.elim0
  | succ n => exact Fintype.sum_equiv (Equiv.subRight i) _ _ fun s => rfl

/-- Summing the constraints: a feasible `x` has `(ℓ + 1)·Σ x ≤ Σ D`, for `ℓ ≥ 1`. -/
theorem LpFeasible.sum_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) {n : ℕ} {D : Fin n → ℝ} {x : Fin n → Fin n → ℝ}
    (hx : LpFeasible ℓ n D x) : (ℓ + 1) * ∑ s, ∑ i, x s i ≤ ∑ s, D s := by
  obtain ⟨h0, hodd, hD⟩ := hx
  have h1 : ℓ * ∑ s, ∑ i, x s i ≤ ∑ s, ∑ i, ℓ ^ i.val * x s i := by
    rw [mul_sum]
    refine sum_le_sum fun s _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    by_cases hi : Odd i.val
    · refine mul_le_mul_of_nonneg_right (le_self_pow₀ hℓ ?_) (h0 s i)
      rintro h
      obtain ⟨c, hc⟩ := hi
      omega
    · simp [hodd s i hi]
  have h2 := sum_le_sum fun s (_ : s ∈ univ) => hD s
  rw [sum_add_distrib, sum_sum_sub] at h2
  linarith

/-- `0 ≤ lpF(ℓ, n, D) ≤ ℓ/(ℓ² − 1)·Σ D` for `ℓ > 1` and `D ≥ 0` (the archive's `FactLpF`). -/
theorem lpF_nonneg_le {ℓ : ℝ} (hℓ : 1 < ℓ) {n : ℕ} {D : Fin n → ℝ} (hD : 0 ≤ D) :
    0 ≤ lpF ℓ n D ∧ lpF ℓ n D ≤ ℓ / (ℓ ^ 2 - 1) * ∑ s, D s := by
  set T := {y | ∃ x, LpFeasible ℓ n D x ∧ y = ∑ s, ∑ i, x s i}
  have hsum : 0 ≤ ∑ s, D s := sum_nonneg fun s _ => hD s
  have hmem : (0 : ℝ) ∈ T := ⟨0, ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun s => by simpa using hD s⟩, by simp⟩
  have hub : ∀ y ∈ T, y ≤ (∑ s, D s) / (ℓ + 1) := by
    rintro y ⟨x, hx, rfl⟩
    rw [le_div_iff₀ (by linarith)]
    linarith [hx.sum_le hℓ.le]
  have hle : sSup T ≤ (∑ s, D s) / (ℓ + 1) := csSup_le ⟨0, hmem⟩ hub
  have hge : 0 ≤ sSup T := le_csSup ⟨_, hub⟩ hmem
  have hsq : 0 < ℓ ^ 2 - 1 := by nlinarith
  have heq : ℓ / (ℓ ^ 2 - 1) = 1 / (ℓ + 1) + 1 / (ℓ ^ 2 - 1) := by
    field_simp
    ring
  have key : (∑ s, D s) / (ℓ + 1) ≤ ℓ / (ℓ ^ 2 - 1) * ∑ s, D s := by
    have h3 : 0 ≤ 1 / (ℓ ^ 2 - 1) * ∑ s, D s := mul_nonneg (by positivity) hsum
    rw [heq, add_mul, show (∑ s, D s) / (ℓ + 1) = 1 / (ℓ + 1) * ∑ s, D s by ring]
    exact le_add_of_nonneg_right h3
  unfold lpF
  constructor <;> linarith

namespace Ranks

/-- The forced order at `g₀, g₁` is at most `0`. -/
theorem FTypeG_nonpos (J : Fin R.m) : R.FTypeG hc J ≤ 0 := by
  have : 0 ≤ ∑ τ, (∑ i : Fin (R.k + J), |R.aPlus (hc τ) J i| + ∑ c, |R.aMinus (hc τ) J c|) :=
    sum_nonneg fun τ _ => add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
  unfold FTypeG
  linarith

/-- The forced order at an inert or signal prime is nonnegative when the weights are. -/
theorem FInert_nonneg (J : Fin R.m) {p : ℕ} (hp : p.Prime) (hw : ∀ ρ, 0 ≤ R.wj hc J ρ) :
    0 ≤ R.FInert hc J p := by
  have hk : (1 : ℝ) ≤ R.k := by have := R.m_add_three_le; exact_mod_cast (by omega : 1 ≤ R.k)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold FInert
  split_ifs
  · exact sum_nonneg fun ρ _ => div_nonneg (mul_nonneg (by linarith) (by exact_mod_cast hw ρ)) (by nlinarith)
  · refine mul_nonneg (by positivity) (sum_nonneg fun z _ => (lpF_nonneg_le hp1 fun s => ?_).1)
    have := hw (S.pos p z s)
    simp only [Pi.zero_apply]
    exact mul_nonneg (by linarith) (by exact_mod_cast this)

end Ranks

end ZetaBalance.Setting
