import Mathlib
import Littlewood
import D2Prim

/-!
# The tail identity for `L′/L(1, χ_D)` — CONDITIONAL on the half-plane

**CONDITIONAL.** Every result here uses `ChiUniform.psiChi_le_uniform`, hence the half-plane `Re s > 11/12` for every
Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`, the companion preprint's result formalised in the library;
see `formalisations/openai-half-plane.md`). Lean checks it with the standard axioms only, but it is only as good as that
input, and must be cited as conditional on it.

* `GSTail.logDeriv_one_tail`: for `0 < η < 1/24`, `‖L′/L(1, χ) + Σ_{n ≤ y} χ(n)Λ(n)/n‖ ≤ C log(N + 2) y^{2η − 1/12}`
  for every `χ ≠ 1` mod `N` and `y > 1`.
* `GSTail.tail_pos`, `GSTail.tail_neg`: the same for the primitive `χ_D` of `GSPrim` with `χ_D(n) = (D|n)`.

See `formalisations/d2-density.md`.
-/

namespace GSTail
open Complex Filter Topology ArithmeticFunction Finset

/-- `χ(n)Λ(n)`. -/
noncomputable def a {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := χ n * (vonMangoldt n : ℂ)

theorem norm_a_le {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖a χ n‖ ≤ vonMangoldt n := by
  unfold a
  rw [norm_mul, Complex.norm_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)

/-- The tail `n > Y`. -/
noncomputable def tl {N : ℕ} (χ : DirichletCharacter ℂ N) (Y n : ℕ) : ℂ := if Y < n then a χ n else 0

/-- The head `n ≤ Y`. -/
noncomputable def hd {N : ℕ} (χ : DirichletCharacter ℂ N) (Y n : ℕ) : ℂ := if n ≤ Y then a χ n else 0

theorem sum_split {N : ℕ} (χ : DirichletCharacter ℂ N) (Y T : ℕ) :
    ∑ k ∈ Icc 1 T, a χ k = ∑ k ∈ Icc 1 T, tl χ Y k + ∑ k ∈ Icc 1 (min T Y), a χ k := by
  have h : ∑ k ∈ Icc 1 (min T Y), a χ k = ∑ k ∈ Icc 1 T, hd χ Y k := by
    unfold hd; rw [← sum_filter]; congr 1; ext k; simp only [mem_Icc, mem_filter]; omega
  rw [h, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  unfold tl hd; split_ifs <;> first | omega | simp

theorem psiChi_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) :
    ChiPNT.psiChi χ x = ∑ k ∈ Icc 1 ⌊x⌋₊, a χ k := rfl

/-- **CONDITIONAL. Tail identity for `L′/L(1, χ)`** (conditional on the half-plane `Re s > 11/12`, through
`ChiUniform.psiChi_le_uniform`): for `0 < η < 1/24` there is `C` with
`‖L′/L(1, χ) + Σ_{n ≤ y} χ(n)Λ(n)/n‖ ≤ C log(N + 2) y^{2η − 1/12}` for every `χ ≠ 1` mod `N` and `y > 1`. -/
theorem logDeriv_one_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y : ℝ, 1 < y →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
          ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (vonMangoldt n : ℂ) / n‖ ≤
        C * Real.log (N + 2) * y ^ (2 * η - 1 / 12) := by
  obtain ⟨C, hC, hψ⟩ := ChiUniform.psiChi_le_uniform hη
  refine ⟨4 * C / η, by positivity, ?_⟩
  intro N _ χ hχ y hy
  set Y := ⌊y⌋₊ with hYdef
  set L := Real.log (N + 2)
  have hL : 0 ≤ L := Real.log_nonneg (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  set δ : ℝ := 1 / 12 - 2 * η
  have hδ : 0 < δ := by simp only [δ]; linarith
  set K := 2 * C * L * y ^ (-δ)
  have hy0 : 0 < y := by linarith
  -- partial sums of the tail
  have hb : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Icc 1 ⌊t⌋₊, tl χ Y k‖ ≤ K * t ^ (1 - η) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hK : 0 ≤ K := by positivity
    have hsplit := sum_split χ Y ⌊t⌋₊
    by_cases hT : ⌊t⌋₊ ≤ Y
    · rw [min_eq_left hT] at hsplit
      have h0 : ∑ k ∈ Icc 1 ⌊t⌋₊, tl χ Y k = 0 := by linear_combination -hsplit
      rw [h0, norm_zero]; positivity
    · push Not at hT
      rw [min_eq_right hT.le] at hsplit
      have hty : y < t := by
        have h1 := Nat.lt_floor_add_one y
        have h2 : ((Y + 1 : ℕ) : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hT
        have h3 := Nat.floor_le ht0.le
        push_cast at h2; linarith
      have e : ∑ k ∈ Icc 1 ⌊t⌋₊, tl χ Y k = ChiPNT.psiChi χ t - ChiPNT.psiChi χ y := by
        rw [psiChi_eq, psiChi_eq, hsplit]; ring
      rw [e]
      have h1 := hψ N χ hχ t (by linarith)
      have h2 := hψ N χ hχ y hy
      have hyt : y ^ (11 / 12 + η) ≤ t ^ (11 / 12 + η) :=
        Real.rpow_le_rpow hy0.le hty.le (by linarith)
      have htd : t ^ (-δ) ≤ y ^ (-δ) := Real.rpow_le_rpow_of_nonpos hy0 hty.le (by linarith)
      have hsplitpow : t ^ (11 / 12 + η) = t ^ (1 - η) * t ^ (-δ) := by
        rw [← Real.rpow_add ht0]; congr 1; simp only [δ]; ring
      calc ‖ChiPNT.psiChi χ t - ChiPNT.psiChi χ y‖
          ≤ ‖ChiPNT.psiChi χ t‖ + ‖ChiPNT.psiChi χ y‖ := norm_sub_le _ _
        _ ≤ C * L * t ^ (11 / 12 + η) + C * L * y ^ (11 / 12 + η) := add_le_add h1 h2
        _ ≤ 2 * C * L * t ^ (11 / 12 + η) := by
            have := mul_le_mul_of_nonneg_left hyt (by positivity : 0 ≤ C * L); linarith
        _ = 2 * C * L * t ^ (-δ) * t ^ (1 - η) := by rw [hsplitpow]; ring
        _ ≤ K * t ^ (1 - η) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left htd (by positivity)
  -- the bound for `σ ∈ (1, 2]`
  set P : ℝ → ℂ := fun σ => ∑ n ∈ Icc 1 Y, a χ n / (n : ℂ) ^ (σ : ℂ)
  set g : ℝ → ℂ := fun σ => deriv (DirichletCharacter.LFunction χ) σ /
    DirichletCharacter.LFunction χ σ + P σ
  have hσ : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖g σ‖ ≤ 2 * K / η := by
    intro σ h1 h2
    have hre : 1 < (σ : ℂ).re := by simpa using h1
    have hsT : LSeriesSummable (tl χ Y) σ := ChiPNT.LSeriesSummable_of_le_vonMangoldt
      (fun n => by unfold tl; split_ifs; exact norm_a_le χ n; simp [vonMangoldt_nonneg]) hre
    have hsH : LSeriesSummable (hd χ Y) σ := ChiPNT.LSeriesSummable_of_le_vonMangoldt
      (fun n => by unfold hd; split_ifs; exact norm_a_le χ n; simp [vonMangoldt_nonneg]) hre
    have hadd : a χ = hd χ Y + tl χ Y := by
      funext n; simp only [Pi.add_apply, hd, tl]; split_ifs <;> first | omega | simp
    have hH : LSeries (hd χ Y) σ = P σ := by
      rw [LSeries, tsum_eq_sum (s := Icc 1 Y)]
      · refine sum_congr rfl fun n hn => ?_
        have hn1 : n ≠ 0 := by simp at hn; omega
        have hnY : n ≤ Y := by simp at hn; omega
        rw [LSeries.term_def, if_neg hn1, hd, if_pos hnY]
      · intro n hn
        rw [LSeries.term_def]
        split_ifs with h0
        · rfl
        · simp only [mem_Icc, not_and, not_le] at hn
          rw [hd, if_neg (by omega), zero_div]
    have hL1 := ChiPNT.LSeries_twist_vonMangoldt_eq_LFunction χ hre
    have hg : g σ = -LSeries (tl χ Y) σ := by
      have : LSeries (a χ) σ = P σ + LSeries (tl χ Y) σ := by
        rw [hadd, LSeries_add hsH hsT, hH]
      simp only [g]
      unfold a at this
      rw [hL1] at this
      linear_combination -this
    rw [hg, norm_neg]
    have hbound := Littlewood.norm_LSeries_le_of_sum_le (by linarith) (by linarith : 1 - η < σ) hsT hb
    have hK : 0 ≤ K := by positivity
    calc ‖LSeries (tl χ Y) σ‖ ≤ σ * K / (σ - (1 - η)) := hbound
      _ ≤ 2 * K / η := by
        rw [div_le_div_iff₀ (by linarith) hη]
        nlinarith [mul_nonneg hK hη.le]
  -- `σ → 1⁺`
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have h10 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hcont : ContinuousAt g 1 := by
    have hc1 : ContinuousAt (fun σ : ℝ => (σ : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    apply ContinuousAt.add
    · apply ContinuousAt.div
      · exact ((hF.analyticAt _).deriv.continuousAt).comp (f := fun σ : ℝ => (σ : ℂ)) (by simpa using hc1)
      · exact (hF.continuous.continuousAt).comp (f := fun σ : ℝ => (σ : ℂ)) hc1
      · simpa using h10
    · apply Continuous.continuousAt
      refine continuous_finset_sum _ fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by simp at hn; exact_mod_cast (show n ≠ 0 by omega)
      exact continuous_const.div (Complex.continuous_ofReal.const_cpow (Or.inl hn0))
        fun σ => Complex.cpow_ne_zero_iff.2 (Or.inl hn0)
  have ht : Tendsto (fun σ => ‖g σ‖) (𝓝[>] 1) (𝓝 ‖g 1‖) :=
    hcont.norm.tendsto.mono_left nhdsWithin_le_nhds
  have hle : ‖g 1‖ ≤ 2 * K / η := by
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with σ hs
    exact hσ σ hs.1 hs.2.le
  have hg1 : g 1 = deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
      ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (vonMangoldt n : ℂ) / n := by
    simp only [g, P, a, Complex.ofReal_one, Complex.cpow_one]
    rfl
  rw [← hg1]
  refine hle.trans (le_of_eq ?_)
  have e : -δ = 2 * η - 1 / 12 := by simp only [δ]; ring
  simp only [K, e]
  field_simp
  ring

theorem ne_one_of_primitive {d : ℕ} [NeZero d] (hd : 1 < d) {χ : DirichletCharacter ℂ d}
    (hp : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  have := hp
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
  omega

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

