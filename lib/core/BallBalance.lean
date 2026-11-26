import Mathlib
import ZetaGap

/-!
# The balance identity at a constant weight, and the ball's Gram entries

Lemma B of the rebuild (`ZetaBalance.Setting.balance`) at the constant weight `W ≡ w`.

* **The collapse** (`ZetaBalance.Setting.balance_const`): with `W ≡ w > 0`, the coefficients
  `Σ_{ρ ∈ Φ} conj χ(γ_t(ρ))` leave only `χ = 1` and `χ = (1, 0, 1)` (`ZetaBalance.sum_conj_eval_γ`), and Lemma B is
  `ASK(a, t, w) − MAIN(a, w) = w·(G(a/w) − Re g_{χ_d}(a/w))`, where `G` is the ramp error of `ζ`
  (`WindowGRH.zetaFamily.G`) and `g_{χ_d}` that of the primitive character of `χ_d` (`ZetaBalance.Setting.g` at
  `(1, 0, 1)`). The ramp error of the trivial character of the setting is `G` (`ZetaBalance.Setting.g_one_re`,
  of `ZetaGap`).
* **The ball's prime part** (`ZetaBalance.Setting.gram_primePart`): the prime part
  `m·Σ_{k ≤ m/n} Λ(k)/k − n·ψ(m/n)` of the ball's Gram entry (`BallPsi.gram_explicit`) is
  `Σ_{k ≤ m/n} Λ(k)(m/k − n)`, and at the constant weight `n` the sum `ASK(m, t, n)` has the same terms, each weighted
  by `1[(k, QS·q) = 1]·(1 − χ_d(k))`, which vanishes off the prime powers inert in `ℚ(√−d)`
  (`ZetaBalance.Setting.ASK_const`).
-/

open Complex ComplexConjugate DirichletCharacter
open scoped ArithmeticFunction.vonMangoldt

namespace ZetaBalance

namespace Setting

variable (S : Setting)

/-- **Lemma B at a constant weight**: for `w > 0`,
`ASK(a, t, w) − MAIN(a, w) = w·(G(a/w) − Re g_{χ_d}(a/w))`, with `G` the ramp error of `ζ` and `g_{χ_d}` that of
the primitive character of `χ_d`. -/
theorem balance_const (a : ℝ) (t : S.A) {w : ℝ} (hw : 0 < w) :
    S.ASK a t (fun _ => w) - S.MAIN a (fun _ => w) =
      w * (WindowGRH.zetaFamily.G (a / w) - (S.g (true, false, 1) (a / w)).re) := by
  rw [S.balance a t _ fun _ => hw]
  have hsum : ∑ ρ : Φ S.A, ((w : ℝ) : ℂ) * ∑ χ : Dual S.A, conj (eval χ (γ t ρ)) * S.g χ (a / w) =
      (w : ℂ) * ∑ χ : Dual S.A, (∑ ρ : Φ S.A, conj (eval χ (γ t ρ))) * S.g χ (a / w) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun χ _ => by rw [Finset.sum_mul]
  rw [hsum]
  simp only [sum_conj_eval_γ]
  set c : ℂ := (Fintype.card (Φ S.A) : ℂ)
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have htwo : ∑ χ : Dual S.A, (if χ.2.1 = false ∧ χ.2.2 = 1 then sgnPow χ.1 (-1) * c else 0) * S.g χ (a / w) =
      c * (S.g (false, false, 1) (a / w) - S.g (true, false, 1) (a / w)) := by
    rw [Fintype.sum_eq_add (false, false, 1) (true, false, 1) (by simp)]
    · simp only [and_self, ite_true, sgnPow]
      push_cast
      ring
    · rintro ⟨α, β, ξ⟩ ⟨h1, h2⟩
      split_ifs with h
      · obtain ⟨hβ, hξ⟩ := h
        simp only at hβ hξ
        subst hβ hξ
        cases α
        · exact absurd rfl h1
        · exact absurd rfl h2
      · exact zero_mul _
  rw [htwo, mul_left_comm, ← mul_assoc c⁻¹ c, inv_mul_cancel₀ hc0, one_mul, re_ofReal_mul, sub_re, S.g_one_re,
    WindowGRH.zetaFamily_G]

/-- **The prime part of the ball's Gram entry**: for `n > 0`,
`m·Σ_{k ≤ m/n} Λ(k)/k − n·ψ(m/n) = Σ_{k ≤ m/n} Λ(k)(m/k − n)`, the prime part of `BallPsi.gram_explicit`. -/
theorem gram_primePart (m : ℝ) (n : ℝ) :
    m * ∑ k ∈ Finset.Ioc 0 ⌊m / n⌋₊, Λ k / k - n * Chebyshev.psi (m / n) =
      ∑ k ∈ Finset.Icc 1 ⌊m / n⌋₊, Λ k * (m / k - n) := by
  have e : Finset.Icc 1 ⌊m / n⌋₊ = Finset.Ioc 0 ⌊m / n⌋₊ := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e, Chebyshev.psi, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **`ASK` at a constant weight is the ball's prime part, filtered**: for `w > 0`,
`ASK(a, t, w) = Σ_{k ≤ a/w} 1[(k, QS·q) = 1](1 − χ_d(k))·Λ(k)(a/k − w)`: the terms of `gram_primePart` at
`a = m`, `w = n`, each weighted by the indicator of the prime powers inert in `ℚ(√−d)`. -/
theorem ASK_const (a : ℝ) (t : S.A) {w : ℝ} (hw : 0 < w) :
    S.ASK a t (fun _ => w) = ∑ k ∈ Finset.Icc 1 ⌊a / w⌋₊,
      (if k.Coprime (S.QS * S.q) then (1 - (legendreSym S.d k : ℝ)) else 0) * (Λ k * (a / k - w)) := by
  unfold ASK
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊a / w⌋₊) fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkf⟩ := Finset.mem_Icc.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkw : (k : ℝ) ≤ a / w := (Nat.le_floor_iff' (by omega)).1 hkf
    have hnn : 0 ≤ a / k - w := by
      rw [le_div_iff₀ hw] at hkw
      rw [sub_nonneg, le_div_iff₀ hk0]
      linarith
    rw [max_eq_left hnn]
    split_ifs
    · ring
    · ring
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · have hlt : ⌊a / w⌋₊ < k := by
        by_contra hle
        exact hk (Finset.mem_Icc.2 ⟨hpos, not_lt.1 hle⟩)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hpos
      have hx : a / w < k := Nat.lt_of_floor_lt hlt
      have hneg : a / k - w ≤ 0 := by
        rw [div_lt_iff₀ hw] at hx
        rw [sub_nonpos, div_le_iff₀ hk0]
        linarith
      rw [max_eq_right hneg]
      simp

end Setting

end ZetaBalance

#print axioms ZetaBalance.Setting.balance_const
#print axioms ZetaBalance.Setting.gram_primePart
#print axioms ZetaBalance.Setting.ASK_const
