import Mathlib

/-! # The d₂ < d₁ density for real characters: analytic assembly

What is proved here, and what is assumed (as explicit hypotheses, never `sorry`):

* `re_inv_pos` / `K1_pos`: proved. Every zero with `0 < Re ρ < 1` gives `Re (1/(ρ(1-ρ))) > 0`, so a summable zero
  sum `K₁ = Σ 1/(ρ(1-ρ))` over a nonempty zero set has positive real part.
* `density_of_dist`: proved. Suppose the empirical proportions of `ℓ_D > t` tend to `μ (Ioi t)` for every `t`, which is
  the hypothesis `hdist`. The "lower failures" `ℓ_D < low D` only happen for `low D → -∞`, which is the hypothesis `hlow`.
  Then the proportion of `D` with `ℓ_D > t₀ ∨ ℓ_D < low D` tends to `μ (Ioi t₀)`.

Assumed inputs (not formalised; cited):
* `hdist`: weak convergence per sign of the law of `L'/L(1,χ_D)` to the random model, at every `t`. This rests on
  Lamzouri (arXiv:1410.1603, §2) per sign, Granville–Soundararajan Lemma 4.1 (Pólya–Vinogradov; not in Mathlib),
  Carleman's moment theorem (not in Mathlib), and the random model having no atoms (Lévy).
* Theorem B (the closed form of `K(2)`), from the explicit formula for `L(s,χ)` (not in Mathlib).
-/

open Filter Topology MeasureTheory Set

namespace D2Density

/-- For `0 < Re ρ < 1`, `Re (1/(ρ(1-ρ))) > 0`. -/
theorem re_inv_pos (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : 0 < (1 / (ρ * (1 - ρ))).re := by
  have hne : ρ * (1 - ρ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h; rw [h] at h0; simp at h0
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [one_div, Complex.inv_re]
  apply div_pos _ (Complex.normSq_pos.2 hne)
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith [sq_nonneg ρ.im, mul_pos h0 (sub_pos.2 h1)]

/-- `K₁ > 0`: a summable zero sum over a nonempty set of zeros in the open strip has positive real part. -/
theorem K1_pos {ι : Type*} (ρ : ι → ℂ) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1)
    (hs : Summable fun i => 1 / (ρ i * (1 - ρ i))) [Nonempty ι] :
    0 < (∑' i, 1 / (ρ i * (1 - ρ i))).re := by
  rw [Complex.re_tsum hs]
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (Complex.reCLM.summable hs).tsum_pos (fun j => (re_inv_pos _ (h0 j) (h1 j)).le) i
    (re_inv_pos _ (h0 i) (h1 i))

/-- Proportion of a finset satisfying a predicate. -/
noncomputable def prop (S : Finset ℤ) (P : ℤ → Prop) [DecidablePred P] : ℝ :=
  ((S.filter P).card : ℝ) / (S.card : ℝ)

theorem prop_le_prop {S : Finset ℤ} {P Q : ℤ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ D ∈ S, P D → Q D) : prop S P ≤ prop S Q := by
  unfold prop
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun D hD => by
    simp only [Finset.mem_filter] at hD ⊢; exact ⟨hD.1, h D hD.1 hD.2⟩)

theorem prop_or_le {S : Finset ℤ} (P Q : ℤ → Prop) [DecidablePred P] [DecidablePred Q] :
    prop S (fun D => P D ∨ Q D) ≤ prop S P + prop S Q := by
  unfold prop; rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Finset.filter_or]; exact_mod_cast Finset.card_union_le _ _

theorem prop_not {S : Finset ℤ} (P : ℤ → Prop) [DecidablePred P] (hS : S.Nonempty) :
    prop S (fun D => ¬ P D) = 1 - prop S P := by
  unfold prop
  have hc : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hc.ne']
  have := Finset.card_filter_add_card_filter_not (s := S) (p := P)
  rw [add_comm]; exact_mod_cast this

theorem prop_finite_le {S : Finset ℤ} (B : Finset ℤ) (P : ℤ → Prop) [DecidablePred P]
    (hB : ∀ D, P D → D ∈ B) : prop S P ≤ (B.card : ℝ) / S.card := by
  unfold prop
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun D hD => hB D (Finset.mem_filter.1 hD).2)

/-- **Assembly.** Let `S x` be the discriminants up to `x`, of one sign, with `#S x → ∞`, and `ℓ D = L'/L(1,χ_D)`.
Suppose:
* `hdist`: for every `t` the proportion with `ℓ > t` tends to `μ (Ioi t)` (a probability measure);
* `hlow`: for each `M` only finitely many `D` (the finset `B M`) have `low D ≥ -M`.
Then the proportion of `D` with `ℓ D > t₀ ∨ ℓ D < low D` tends to `μ (Ioi t₀)`. -/
theorem density_of_dist (S : ℕ → Finset ℤ) (hS : Tendsto (fun x => ((S x).card : ℝ)) atTop atTop)
    (ℓ low : ℤ → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hdist : ∀ t, Tendsto (fun x => prop (S x) (fun D => t < ℓ D)) atTop (𝓝 (μ (Ioi t)).toReal))
    (B : ℝ → Finset ℤ) (hlow : ∀ M D, -M ≤ low D → D ∈ B M) (t₀ : ℝ) :
    Tendsto (fun x => prop (S x) (fun D => t₀ < ℓ D ∨ ℓ D < low D)) atTop (𝓝 (μ (Ioi t₀)).toReal) := by
  classical
  -- μ (Ioi (-M)) → 1 as M → ∞
  have htail : Tendsto (fun M : ℕ => (μ (Ioi (-(M:ℝ)))).toReal) atTop (𝓝 1) := by
    have hmono : Monotone (fun M : ℕ => Ioi (-(M:ℝ))) := fun a b h => Ioi_subset_Ioi (by
      simp only [neg_le_neg_iff]; exact_mod_cast h)
    have hU : (⋃ M : ℕ, Ioi (-(M:ℝ))) = univ := by
      ext y; simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y); exact ⟨n, by linarith⟩
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU, measure_univ] at this
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
    exact h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 htail) (ε/4) (by linarith)
  have hM' := hM M le_rfl; rw [Real.dist_eq] at hM'
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 (hdist t₀)) (ε/4) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 (hdist (-(M:ℝ)))) (ε/4) (by linarith)
  have hB : Tendsto (fun x => ((B M).card : ℝ) / (S x).card) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hS
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.1 hB) (ε/4) (by linarith)
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 ((tendsto_atTop.1 hS) 1)
  refine ⟨max (max N1 N2) (max N3 N4), fun x hx => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  have e1 := hN1 x hx.1.1; have e2 := hN2 x hx.1.2; have e3 := hN3 x hx.2.1
  rw [Real.dist_eq] at e1 e2 e3
  have hne : (S x).Nonempty := by
    rw [← Finset.card_pos]; have := hN4 x hx.2.2; exact_mod_cast (by linarith : (0:ℝ) < (S x).card)
  -- lower bound
  have lo : prop (S x) (fun D => t₀ < ℓ D) ≤ prop (S x) (fun D => t₀ < ℓ D ∨ ℓ D < low D) :=
    prop_le_prop (fun D _ h => Or.inl h)
  -- upper bound
  have up1 : prop (S x) (fun D => t₀ < ℓ D ∨ ℓ D < low D) ≤
      prop (S x) (fun D => t₀ < ℓ D) + prop (S x) (fun D => ¬ (-(M:ℝ)) < ℓ D ∨ -(M:ℝ) ≤ low D) :=
    (prop_le_prop (Q := fun D => t₀ < ℓ D ∨ (¬ (-(M:ℝ)) < ℓ D ∨ -(M:ℝ) ≤ low D)) (fun D _ h => by
      rcases h with h | h
      · exact Or.inl h
      · right; by_cases hl : -(M:ℝ) ≤ low D
        · exact Or.inr hl
        · left; push_neg at hl ⊢; linarith)).trans (prop_or_le _ _)
  have up2 := prop_or_le (S := S x) (fun D => ¬ (-(M:ℝ)) < ℓ D) (fun D => -(M:ℝ) ≤ low D)
  have up3 := prop_not (S := S x) (fun D => (-(M:ℝ)) < ℓ D) hne
  have up4 := prop_finite_le (S := S x) (B M) (fun D => -(M:ℝ) ≤ low D) (fun D h => hlow M D h)
  have hμ : (μ (Ioi t₀)).toReal ≤ 1 := by
    have := prob_le_one (μ := μ) (s := Ioi t₀); exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using this)
  rw [Real.dist_eq, abs_lt]
  have hpos3 : 0 ≤ ((B M).card : ℝ) / (S x).card := by positivity
  constructor
  · linarith [abs_lt.1 e1]
  · have := abs_lt.1 e1; have := abs_lt.1 e2; have := abs_lt.1 e3; have := abs_lt.1 hM'
    linarith

theorem criterion' (K1 c l : ℝ) (hK : 0 < K1) :
    1 ≤ 2 * (1 - (√2 * (K1/2 + c + l/2))^2 / K1^2) ↔ -2*K1 - 2*c ≤ l ∧ l ≤ -2*c := by
  have hs : (√2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [mul_pow, hs]
  have hK2 : 0 < K1^2 := by positivity
  constructor
  · intro h
    have : 2 * (K1/2 + c + l/2)^2 ≤ K1^2 / 2 := by
      have := h; rw [show 2 * (1 - 2 * (K1/2+c+l/2)^2 / K1^2)
        = 2 - 4 * (K1/2+c+l/2)^2 / K1^2 by ring] at this
      have h' : 4 * (K1/2+c+l/2)^2 / K1^2 ≤ 1 := by linarith
      rw [div_le_one hK2] at h'; linarith
    have hsq : (K1 + 2*c + l)^2 ≤ K1^2 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (K1 + 2*c + l - K1), sq_nonneg (K1+2*c+l+K1)]
  · rintro ⟨h1, h2⟩
    have hsq : (K1 + 2*c + l)^2 ≤ K1^2 := by nlinarith
    rw [show 2 * (1 - 2 * (K1/2+c+l/2)^2 / K1^2)
        = 2 - (K1 + 2*c + l)^2 / K1^2 by field_simp]
    have : (K1 + 2*c + l)^2 / K1^2 ≤ 1 := (div_le_one hK2).2 hsq
    linarith


/-- **The d₂ < d₁ density, one sign.** Per discriminant: `K1 D = L0 D + 2 ℓ D > 0` (I2; `K1_pos`), and Theorem B
`K2 D = √2 (K1 D/2 + c + ℓ D/2)` (hypothesis `hB`, paper proof). Assume the distributional input `hdist`, and
that `L0 D → ∞` in the sense `hL0` (only finitely many `D` with `L0 D ≤ R`; true as `L0 = log(|D|/π) + ψ_a`).
Then the proportion of `D` with `d₂/d₁ = 2(1 - K2²/K1²) < 1` tends to `μ (Ioi (-2c))`. -/
theorem d2_density (S : ℕ → Finset ℤ) (hS : Tendsto (fun x => ((S x).card : ℝ)) atTop atTop)
    (ℓ L0 K1 K2 : ℤ → ℝ) (c : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK1 : ∀ D, K1 D = L0 D + 2 * ℓ D) (hpos : ∀ D, 0 < K1 D)
    (hB : ∀ D, K2 D = √2 * (K1 D / 2 + c + ℓ D / 2))
    (hdist : ∀ t, Tendsto (fun x => prop (S x) (fun D => t < ℓ D)) atTop (𝓝 (μ (Ioi t)).toReal))
    (Bf : ℝ → Finset ℤ) (hL0 : ∀ R D, L0 D ≤ R → D ∈ Bf R) :
    Tendsto (fun x => prop (S x) (fun D => 2 * (1 - K2 D ^ 2 / K1 D ^ 2) < 1)) atTop
      (𝓝 (μ (Ioi (-2 * c))).toReal) := by
  classical
  have key : ∀ D, 2 * (1 - K2 D ^ 2 / K1 D ^ 2) < 1 ↔ (-2 * c < ℓ D ∨ ℓ D < -(2/5) * (L0 D + c)) := by
    intro D
    have h := criterion' (K1 D) c (ℓ D) (hpos D)
    rw [← hB D] at h
    rw [← not_le, h, hK1 D]; constructor
    · intro hn; by_contra hc; push_neg at hc; exact hn ⟨by linarith [hc.2], by linarith [hc.1]⟩
    · rintro (h1 | h1) ⟨h2, h3⟩ <;> linarith
  have hfun : (fun x => prop (S x) (fun D => 2 * (1 - K2 D ^ 2 / K1 D ^ 2) < 1)) =
      fun x => prop (S x) (fun D => -2 * c < ℓ D ∨ ℓ D < -(2/5) * (L0 D + c)) := by
    funext x; unfold prop; congr 3; ext D; simp only [Finset.mem_filter, key D]
  rw [hfun]
  refine density_of_dist S hS ℓ (fun D => -(2/5) * (L0 D + c)) μ hdist (fun M => Bf (5/2 * M - c)) ?_ (-2 * c)
  intro M D h; apply hL0; linarith

end D2Density

#print axioms D2Density.K1_pos
#print axioms D2Density.density_of_dist
#print axioms D2Density.d2_density
