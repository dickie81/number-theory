/-
# The lonely primes joined to the library: their half has the error exponent `Θ`, and they fill short windows

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. At stage `N` the lonely primes are the primes in `(N/2, N]`, those with no other multiple up to
`N` (`LonelyPrimes.lonely_iff`). Weighted by `log p`, as the explicit formula weights them, they carry
`θ(x) − θ(x/2)`, which is `x/2 + o(x)` by the prime number theorem.
* **The error has the exponent `Θ`** (`lonely_weight_isBigO_iff`): for `a ≥ ½`, `θ(x) − θ(x/2) − x/2 = O(x^{a+ε})`
  for every `ε > 0` if and only if `Θ ≤ a`, where `Θ` is the supremum of the real parts of the nontrivial zeros of
  `ζ` (`PsiExponent.Theta`). So **RH holds exactly when the lonely primes carry half of `x` to within `x^{½+ε}`**
  (`rh_iff_lonely_weight`).
* **They fill every short window** (`lonely_in_window`): for `θ > 17/30` and every large `y`, every interval
  `(y, y + y^θ]` inside `[N/2, N]` holds a lonely prime of stage `N`, by the short-primes theorem from Guth and
  Maynard's density estimate (`ZetaGMDensity.short_primes_seventeen_thirtieths`).

The first is proved by a telescoping (`isBigO_of_sub_half`): if `f(x) − f(x/2) = O(x^b)` with `b > 0`, and `f` is
bounded on bounded sets, then `f(x) = O(x^b)`, since the bounds at `x, x/2, x/4, …` form a geometric series. For
`f(x) = ψ(x) − x` and `a < Θ` this contradicts `ψ(x) − x = Ω±(x^{Θ−ε})` (`PsiExponent.psi_omega_Theta`). The
other direction subtracts two copies of `ψ(x) − x = O(x^{Θ+ε})` (`PsiExponent.psi_isBigO_Theta`). Both pass
between `ψ` and `θ` by `|ψ(x) − θ(x)| ≤ 2√x log x` (Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).
-/
import LonelyPrimes
import MertensExponent
import ZetaGMDensity

open Asymptotics Filter Topology
open scoped Chebyshev

noncomputable section

namespace LonelyJoins

open PsiExponent

/-- The log-weight of the primes in `(x/2, x]`, less `x/2`. -/
def lonelyDev (x : ℝ) : ℝ := θ x - θ (x / 2) - x / 2

/-- **Telescoping.** If `f(x) − f(x/2) = O(x^b)` with `b > 0`, and `f` is bounded on every `[0, X]`, then
`f(x) = O(x^b)`. -/
theorem isBigO_of_sub_half {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hD : (fun x => f x - f (x / 2)) =O[atTop] fun x => x ^ b)
    (hbdd : ∀ X, ∃ B, ∀ x, 0 ≤ x → x ≤ X → |f x| ≤ B) :
    f =O[atTop] fun x => x ^ b := by
  obtain ⟨C, hC, hCw⟩ := hD.exists_pos
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hCw.bound
  set X₀ := max X₁ 1 with hX₀
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  obtain ⟨B, hB⟩ := hbdd X₀
  have h2b : (2 : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K := C / (1 - 2 ^ (-b)) with hK
  have hK0 : 0 ≤ K := div_nonneg hC.le (by linarith)
  have hKeq : C + K * 2 ^ (-b) = K := by
    have h1 : (1 - (2 : ℝ) ^ (-b)) ≠ 0 := by linarith
    rw [hK]
    field_simp
    ring
  have claim : ∀ n : ℕ, ∀ x, 0 ≤ x → x < 2 ^ n * X₀ → |f x| ≤ K * x ^ b + B := by
    intro n
    induction n with
    | zero =>
      intro x hx0 hx
      have h1 : |f x| ≤ B := hB x hx0 (by simpa using hx.le)
      have h2 : 0 ≤ K * x ^ b := mul_nonneg hK0 (Real.rpow_nonneg hx0 _)
      linarith
    | succ n ih =>
      intro x hx0 hx
      by_cases hxX : x < X₀
      · have h1 : |f x| ≤ B := hB x hx0 hxX.le
        have h2 : 0 ≤ K * x ^ b := mul_nonneg hK0 (Real.rpow_nonneg hx0 _)
        linarith
      · have hstep := hX₁ x (le_trans (le_max_left _ _) (not_lt.1 hxX))
        have hxb : 0 ≤ x ^ b := Real.rpow_nonneg hx0 _
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxb] at hstep
        have h2n : (2 : ℝ) ^ (n + 1) * X₀ = 2 * (2 ^ n * X₀) := by ring
        rw [h2n] at hx
        have hhalf := ih (x / 2) (by linarith) (by linarith)
        have hdiv : (x / 2) ^ b = 2 ^ (-b) * x ^ b := by
          rw [Real.div_rpow hx0 (by norm_num), Real.rpow_neg (by norm_num)]
          ring
        rw [hdiv] at hhalf
        calc |f x| = |(f x - f (x / 2)) + f (x / 2)| := by ring_nf
          _ ≤ |f x - f (x / 2)| + |f (x / 2)| := abs_add_le _ _
          _ ≤ C * x ^ b + (K * (2 ^ (-b) * x ^ b) + B) := add_le_add hstep hhalf
          _ = (C + K * 2 ^ (-b)) * x ^ b + B := by ring
          _ = K * x ^ b + B := by rw [hKeq]
  have hall : ∀ x, 0 ≤ x → |f x| ≤ K * x ^ b + B := by
    intro x hx0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / X₀) (by norm_num : (1 : ℝ) < 2)
    have hX₀pos : 0 < X₀ := by linarith
    rw [div_lt_iff₀ hX₀pos] at hn
    exact claim n x hx0 hn
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 le_rfl (by linarith))
  refine IsBigO.of_bound (K + B) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hxb1 : 1 ≤ x ^ b := Real.one_le_rpow hx hb.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
  have h1 := hall x hx0
  have h2 : B ≤ B * x ^ b := le_mul_of_one_le_right hB0 hxb1
  nlinarith

lemma rpow_isBigO_rpow {c d : ℝ} (hcd : c ≤ d) : (fun x : ℝ => x ^ c) =O[atTop] fun x => x ^ d := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _),
    abs_of_nonneg (Real.rpow_nonneg hx0 _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx hcd

lemma comp_half {g : ℝ → ℝ} {c : ℝ} (h : g =O[atTop] fun x => x ^ c) :
    (fun x => g (x / 2)) =O[atTop] fun x => x ^ c := by
  have ht : Tendsto (fun x : ℝ => x / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  refine (h.comp_tendsto ht).trans (IsBigO.of_bound ((2 : ℝ) ^ c)⁻¹ ?_)
  filter_upwards [eventually_ge_atTop 0] with x hx
  simp only [Function.comp_apply]
  rw [Real.div_rpow hx (by norm_num), Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg (by norm_num) _)),
    abs_of_nonneg (Real.rpow_nonneg hx _), div_eq_inv_mul]

lemma psi_sub_theta_isBigO {ε : ℝ} (hε : 0 < ε) :
    (fun x => ψ x - θ x) =O[atTop] fun x => x ^ ((1 : ℝ) / 2 + ε) := by
  have h0 : (fun x => ψ x - θ x) =O[atTop] fun x => 2 * Real.sqrt x * Real.log x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt x * Real.log x)]
    exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hs : (fun x : ℝ => 2 * Real.sqrt x) =O[atTop] fun x => x ^ ((1 : ℝ) / 2) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hx _)]
    norm_num
  have h1 : (fun x : ℝ => 2 * Real.sqrt x * Real.log x) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 2) * x ^ ε := hs.mul (isLittleO_log_rpow_atTop hε).isBigO
  refine (h0.trans h1).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [← Real.rpow_add hx]

/-- `ψ(x) − ψ(x/2) − x/2` and `θ(x) − θ(x/2) − x/2` differ by `O(x^{½+ε})`. -/
lemma psi_dev_sub_lonelyDev {ε : ℝ} (hε : 0 < ε) :
    (fun x => (ψ x - ψ (x / 2) - x / 2) - lonelyDev x) =O[atTop] fun x => x ^ ((1 : ℝ) / 2 + ε) := by
  have h := psi_sub_theta_isBigO hε
  refine (h.sub (comp_half h)).congr_left fun x => ?_
  simp only [lonelyDev]
  ring

lemma psi_bdd (X : ℝ) : ∃ B, ∀ x, 0 ≤ x → x ≤ X → |ψ x - x| ≤ B := by
  refine ⟨ψ X + X, fun x hx0 hxX => abs_le.2 ⟨?_, ?_⟩⟩
  · linarith [Chebyshev.psi_nonneg x, Chebyshev.psi_nonneg X]
  · linarith [Chebyshev.psi_mono hxX, Chebyshev.psi_nonneg x]

/-- **The error of the lonely primes' half has the exponent `Θ`**: for `a ≥ ½`, `θ(x) − θ(x/2) = x/2 + O(x^{a+ε})`
for every `ε > 0` if and only if `Θ ≤ a`. -/
theorem lonely_weight_isBigO_iff {a : ℝ} (ha : 1 / 2 ≤ a) :
    (∀ ε > 0, lonelyDev =O[atTop] fun x => x ^ (a + ε)) ↔ Theta ≤ a := by
  have hΘ := half_le_Theta
  constructor
  · intro h
    by_contra hlt
    have hlt : a < Theta := not_le.1 hlt
    set d := Theta - a with hd
    have hd0 : 0 < d := by linarith
    have hD : (fun x => (ψ x - x) - (ψ (x / 2) - x / 2)) =O[atTop] fun x => x ^ (a + d / 4) := by
      have h1 := h (d / 4) (by linarith)
      have h2 : (fun x => (ψ x - ψ (x / 2) - x / 2) - lonelyDev x) =O[atTop] fun x => x ^ (a + d / 4) :=
        (psi_dev_sub_lonelyDev (ε := d / 4) (by linarith)).trans (rpow_isBigO_rpow (by linarith))
      refine (h2.add h1).congr_left fun x => ?_
      ring
    have hf : (fun x => ψ x - x) =O[atTop] fun x => x ^ (a + d / 4) :=
      isBigO_of_sub_half (f := fun x => ψ x - x) (by linarith) hD psi_bdd
    obtain ⟨C, hC, hCw⟩ := hf.exists_pos
    obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hCw.bound
    obtain ⟨⟨x, hxX, hx⟩, -⟩ := psi_omega_Theta (ε := d / 2) (by linarith) (by linarith) C (max X₁ 1)
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hxX.le
    have hb := hX₁ x (le_trans (le_max_left _ _) hxX.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
    have hexp : x ^ (a + d / 4) ≤ x ^ (Theta - d / 2) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h3 := mul_le_mul_of_nonneg_left hexp hC.le
    have h4 : ψ x - x ≤ |ψ x - x| := le_abs_self _
    linarith
  · intro hle ε hε
    have h1 : (fun x => ψ x - x) =O[atTop] fun x => x ^ (a + ε) :=
      (psi_isBigO_Theta hε).trans (rpow_isBigO_rpow (by linarith))
    have h3 : (fun x => (ψ x - ψ (x / 2) - x / 2) - lonelyDev x) =O[atTop] fun x => x ^ (a + ε) :=
      (psi_dev_sub_lonelyDev hε).trans (rpow_isBigO_rpow (by linarith))
    refine ((h1.sub (comp_half h1)).sub h3).congr_left fun x => ?_
    ring

/-- **RH holds exactly when the lonely primes carry half of `x` to within `x^{½+ε}`**:
`θ(x) − θ(x/2) = x/2 + O(x^{½+ε})` for every `ε > 0`. -/
theorem rh_iff_lonely_weight :
    RiemannHypothesis ↔ ∀ ε > 0, lonelyDev =O[atTop] fun x => x ^ ((1 : ℝ) / 2 + ε) := by
  rw [lonely_weight_isBigO_iff le_rfl, MertensExponent.rh_iff_Theta_eq_half]
  exact ⟨fun h => h.le, fun h => le_antisymm h half_le_Theta⟩

/-- **A lonely prime in every short window**: for `θ > 17/30` and large `y`, every interval `(y, y + y^θ]` inside
`[N/2, N]` holds a prime `p` with no other multiple up to `N`. -/
theorem lonely_in_window {θ' : ℝ} (hθ : 17 / 30 < θ') :
    ∃ X : ℝ, ∀ (N : ℕ) (y : ℝ), X ≤ y → (N : ℝ) / 2 ≤ y → y + y ^ θ' ≤ N →
      ∃ p : ℕ, p.Prime ∧ (∀ k : ℕ, 2 ≤ k → N < k * p) ∧ p ≤ N ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ' := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 (ZetaGMDensity.short_primes_seventeen_thirtieths hθ)
  refine ⟨X, fun N y hXy hNy hyN => ?_⟩
  obtain ⟨p, hp, hyp, hpy⟩ := hX y hXy
  have hpN : p ≤ N := by exact_mod_cast hpy.trans hyN
  have h2p : N < 2 * p := by
    have h : (N : ℝ) < 2 * p := by linarith
    exact_mod_cast h
  exact ⟨p, hp, LonelyPrimes.lonely_iff.2 (by omega), hpN, hyp, hpy⟩

end LonelyJoins

#print axioms LonelyJoins.isBigO_of_sub_half
#print axioms LonelyJoins.lonely_weight_isBigO_iff
#print axioms LonelyJoins.rh_iff_lonely_weight
#print axioms LonelyJoins.lonely_in_window
