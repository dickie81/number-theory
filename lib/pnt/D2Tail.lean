import Mathlib
import Littlewood
import D2Prim

/-!
# The tail identity for `L′/L(1, χ_D)` — CONDITIONAL on the half-plane

* `GSTail.tail_le_of_sum_le`, unconditional: let `L(a, σ)` converge absolutely to `F(σ)` for `σ > 1`, with `F`
  continuous at `1`, and let the partial sums of `a` be at most `K t^θ`. Then
  `‖F(1) − Σ_{n ≤ y} a(n)/n‖ ≤ (4K/η) y^{θ+η−1}` when `θ + η < 1`. The partial sums of the tail `n > y` are at most
  `2K y^{θ+η−1} t^{1−η}`, so partial summation (`Littlewood.norm_LSeries_le_of_sum_le`) bounds its `L`-series on
  `1 < σ ≤ 2`, and continuity carries the bound to `σ = 1`.

**CONDITIONAL.** Every other result here uses `ChiUniform.psiChi_le_uniform`, hence the half-plane `Re s > 11/12` for
every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`, the companion preprint's result formalised in the
library; see `formalisations/openai-half-plane.md`). Lean checks it with the standard axioms only, but it is only as good
as that input, and must be cited as conditional on it.

* `GSTail.logDeriv_one_tail`: for `0 < η < 1/24`, `‖L′/L(1, χ) + Σ_{n ≤ y} χ(n)Λ(n)/n‖ ≤ C log(N + 2) y^{2η − 1/12}`
  for every `χ ≠ 1` mod `N` and `y > 1`: `tail_le_of_sum_le` with `a = χΛ`, `F = −L′/L(·, χ)` and `θ = 11/12 + η`.
* `GSTail.tail_pos`, `GSTail.tail_neg`: the same for the primitive `χ_D` of `GSPrim` with `χ_D(n) = (D|n)`.

See `formalisations/d2-density.md`.
-/

namespace GSTail
open Complex Filter Topology ArithmeticFunction Finset

/-- **The value of an `L`-series at `s = 1`, from its partial sums** (unconditional). Let `L(a, σ)` converge absolutely
to `F(σ)` for `σ > 1`, with `F` continuous at `1`, and let `‖Σ_{n ≤ t} a(n)‖ ≤ K t^θ` for `t > 1`, with `θ ≥ 0`. Then
`‖F(1) − Σ_{n ≤ y} a(n)/n‖ ≤ (4K/η) y^{θ+η−1}` for every `y > 1` and `η > 0` with `θ + η < 1`. -/
theorem tail_le_of_sum_le {a : ℕ → ℂ} {F : ℂ → ℂ} {θ η K : ℝ} (hθ : 0 ≤ θ) (hη : 0 < η) (hθη : θ + η < 1)
    (hS : ∀ σ : ℝ, 1 < σ → LSeriesSummable a σ) (hF : ∀ σ : ℝ, 1 < σ → LSeries a σ = F σ)
    (hc : ContinuousAt F 1) (hb : ∀ t : ℝ, 1 < t → ‖∑ n ∈ Icc 1 ⌊t⌋₊, a n‖ ≤ K * t ^ θ) {y : ℝ} (hy : 1 < y) :
    ‖F 1 - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / n‖ ≤ 4 * K / η * y ^ (θ + η - 1) := by
  set Y := ⌊y⌋₊
  have hy0 : 0 < y := by linarith
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hb y hy)) (by positivity)
  set K' := 2 * K * y ^ (θ + η - 1) with hK'
  -- the head `n ≤ Y`; the tail is `a − hd`
  set hd : ℕ → ℂ := fun n => if n ≤ Y then a n else 0 with hhd
  have hsum : ∀ T : ℕ, ∑ k ∈ Icc 1 T, hd k = ∑ k ∈ Icc 1 (min T Y), a k := fun T => by
    rw [hhd, ← sum_filter]
    congr 1
    ext k
    simp only [mem_filter, mem_Icc]
    omega
  -- the partial sums of the tail
  have hb' : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Icc 1 ⌊t⌋₊, (a - hd) k‖ ≤ K' * t ^ (1 - η) := by
    intro t ht
    simp only [Pi.sub_apply, sum_sub_distrib, hsum]
    rcases le_or_gt ⌊t⌋₊ Y with hT | hT
    · rw [min_eq_left hT, sub_self, norm_zero]
      positivity
    rw [min_eq_right hT.le]
    have hty : y < t := (Nat.lt_floor_add_one y).trans_le
      ((by exact_mod_cast hT : (Y : ℝ) + 1 ≤ ⌊t⌋₊).trans (Nat.floor_le (by linarith)))
    calc _ ≤ K * t ^ θ + K * y ^ θ := (norm_sub_le _ _).trans (add_le_add (hb t (hy.trans hty)) (hb y hy))
      _ ≤ 2 * K * t ^ θ := by nlinarith [mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le hty.le hθ) hK]
      _ = 2 * K * t ^ (θ + η - 1) * t ^ (1 - η) := by
          rw [mul_assoc (2 * K), ← Real.rpow_add (by linarith), show θ + η - 1 + (1 - η) = θ by ring]
      _ ≤ K' * t ^ (1 - η) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hy0 hty.le (by linarith)) (by positivity)) (by positivity)
  -- for `1 < σ ≤ 2`, `F(σ) − P(σ)` is the `L`-series of the tail, with `P(σ) = Σ_{n ≤ Y} a(n) n^{−σ}`
  set P : ℝ → ℂ := fun σ => ∑ n ∈ Icc 1 Y, a n / (n : ℂ) ^ (σ : ℂ) with hP
  have hσ : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖F σ - P σ‖ ≤ 2 * K' / η := by
    intro σ h1 h2
    have hH : HasSum (LSeries.term hd σ) (P σ) := by
      have e : P σ = ∑ n ∈ Icc 1 Y, LSeries.term hd σ n := by
        rw [hP]
        refine sum_congr rfl fun n hn => ?_
        rw [mem_Icc] at hn
        simp only [LSeries.term_of_ne_zero (show n ≠ 0 by omega), hhd, hn.2, ↓reduceIte]
      rw [e]
      refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
      rw [mem_Icc] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact LSeries.term_zero _ _
      · simp only [LSeries.term_of_ne_zero hn0.ne', hhd, show ¬n ≤ Y by omega, ↓reduceIte, zero_div]
    rw [← hF σ h1, ← hH.tsum_eq, ← LSeries, ← LSeries_sub (hS σ h1) hH.summable]
    calc _ ≤ σ * K' / (σ - (1 - η)) :=
          Littlewood.norm_LSeries_le_of_sum_le (by linarith) (by linarith) ((hS σ h1).sub hH.summable) hb'
      _ ≤ 2 * K' / η := by
          have hK'0 : 0 ≤ K' := by rw [hK']; positivity
          rw [div_le_div_iff₀ (by linarith) hη]
          nlinarith [mul_nonneg hK'0 hη.le]
  -- `σ → 1⁺`
  have hcont : ContinuousAt (fun σ : ℝ => F σ - P σ) 1 := by
    refine (hc.comp_of_eq Complex.continuous_ofReal.continuousAt Complex.ofReal_one).sub
      (continuous_finsetSum _ fun n hn => ?_).continuousAt
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [mem_Icc] at hn; omega)
    exact continuous_const.div (Complex.continuous_ofReal.const_cpow (Or.inl hn0))
      fun σ => Complex.cpow_ne_zero_iff.2 (Or.inl hn0)
  have hle : ‖F 1 - P 1‖ ≤ 2 * K' / η := by
    have ht := (hcont.norm.tendsto.mono_left nhdsWithin_le_nhds : Tendsto (fun σ : ℝ => ‖F σ - P σ‖) (𝓝[>] 1) _)
    rw [Complex.ofReal_one] at ht
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hs
    exact hσ σ hs.1 hs.2.le
  have hP1 : P 1 = ∑ n ∈ Icc 1 Y, a n / n := by simp [hP]
  rw [← hP1]
  refine hle.trans (le_of_eq ?_)
  rw [hK']
  ring

/-- **CONDITIONAL. Tail identity for `L′/L(1, χ)`** (conditional on the half-plane `Re s > 11/12`, through
`ChiUniform.psiChi_le_uniform`): for `0 < η < 1/24` there is `C` with
`‖L′/L(1, χ) + Σ_{n ≤ y} χ(n)Λ(n)/n‖ ≤ C log(N + 2) y^{2η − 1/12}` for every `χ ≠ 1` mod `N` and `y > 1`. -/
theorem logDeriv_one_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y : ℝ, 1 < y →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
          ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (vonMangoldt n : ℂ) / n‖ ≤
        C * Real.log (N + 2) * y ^ (2 * η - 1 / 12) := by
  obtain ⟨C, hC, hψ⟩ := ChiUniform.psiChi_le_uniform hη
  refine ⟨4 * C / η, by positivity, fun N _ χ hχ y hy => ?_⟩
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have h := tail_le_of_sum_le (a := fun n => χ n * (vonMangoldt n : ℂ))
    (F := fun s => -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s))
    (by linarith) hη (by linarith)
    (fun σ hσ => DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hσ))
    (fun σ hσ => ChiPNT.LSeries_twist_vonMangoldt_eq_LFunction χ (by simpa using hσ))
    (((hL.analyticAt 1).deriv.continuousAt.div hL.continuous.continuousAt
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)).neg) (hψ N χ hχ) hy
  rw [← norm_neg, neg_sub', neg_neg, sub_neg_eq_add] at h
  refine h.trans (le_of_eq ?_)
  rw [show 11 / 12 + η + η - 1 = 2 * η - 1 / 12 by ring]
  ring

/-- A primitive character of level `d > 1` is not trivial. -/
theorem ne_one_of_primitive {d : ℕ} [NeZero d] (hd : 1 < d) {χ : DirichletCharacter ℂ d}
    (hp : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  have := hp
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
  omega

/-- The tail identity of `logDeriv_one_tail` for a primitive `χ` mod `d > 1` that agrees with the Kronecker symbol
`(D|·)` on `n ≠ 0`, with `(D|n)` in the sum. -/
theorem tail_of {η C : ℝ} {d : ℕ} [NeZero d] (hd : 1 < d) (D : ℤ) (χ : DirichletCharacter ℂ d)
    (hp : χ.IsPrimitive) (hv : ∀ n : ℕ, n ≠ 0 → χ n = GSEven.kron D n)
    (hC : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y : ℝ, 1 < y →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
          ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (vonMangoldt n : ℂ) / n‖ ≤
        C * Real.log (N + 2) * y ^ (2 * η - 1 / 12)) (y : ℝ) (hy : 1 < y) :
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
        ∑ n ∈ Icc 1 ⌊y⌋₊, GSEven.kron D n * (vonMangoldt n : ℂ) / n‖ ≤
      C * Real.log (d + 2) * y ^ (2 * η - 1 / 12) := by
  have h := hC d χ (ne_one_of_primitive hd hp) y hy
  rwa [sum_congr rfl fun n hn => by rw [hv n (by simp at hn; omega)]] at h

/-- **CONDITIONAL. Tail identity for positive fundamental discriminants** (conditional on the half-plane `Re s > 11/12`):
`L′/L(1, χ_d) = −Σ_{n ≤ y} Λ(n)(d|n)/n + O(log d · y^{2η − 1/12})`, uniformly in `d`. -/
theorem tail_pos {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d], GSFund.fundPos d → (hd : 1 < d) →
      ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ (∀ n : ℕ, n ≠ 0 → χ n = GSEven.kron d n) ∧
        ∀ y : ℝ, 1 < y →
          ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
              ∑ n ∈ Icc 1 ⌊y⌋₊, GSEven.kron d n * (vonMangoldt n : ℂ) / n‖ ≤
            C * Real.log (d + 2) * y ^ (2 * η - 1 / 12) := by
  obtain ⟨C, hC0, hC⟩ := logDeriv_one_tail hη hη'
  refine ⟨C, hC0, fun d _ hf hd => ?_⟩
  obtain ⟨χ, hp, hv⟩ := GSPrim.primitive_pos hf hd
  exact ⟨χ, hp, hv, tail_of hd _ χ hp hv hC⟩

/-- **CONDITIONAL. Tail identity for negative fundamental discriminants** (conditional on the half-plane `Re s > 11/12`). -/
theorem tail_neg {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d], GSFund.fundNeg d →
      ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ (∀ n : ℕ, n ≠ 0 → χ n = GSEven.kron (-d) n) ∧
        ∀ y : ℝ, 1 < y →
          ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
              ∑ n ∈ Icc 1 ⌊y⌋₊, GSEven.kron (-d) n * (vonMangoldt n : ℂ) / n‖ ≤
            C * Real.log (d + 2) * y ^ (2 * η - 1 / 12) := by
  obtain ⟨C, hC0, hC⟩ := logDeriv_one_tail hη hη'
  refine ⟨C, hC0, fun d _ hf => ?_⟩
  have hd : 1 < d := by
    rcases hf with ⟨-, h4⟩ | ⟨⟨j, rfl⟩, hs, -⟩
    · omega
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp at hs
      · omega
  obtain ⟨χ, hp, hv⟩ := GSPrim.primitive_neg hf
  exact ⟨χ, hp, hv, tail_of hd _ χ hp hv hC⟩

end GSTail

#print axioms GSTail.tail_le_of_sum_le
#print axioms GSTail.logDeriv_one_tail
