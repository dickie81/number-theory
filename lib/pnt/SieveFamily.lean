/-
# Type II families

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `L`, `w₁` and `w₂` are a route's parameters (`SieveRoute.Route`), and `family_bound`,
`typeII_sharp_explicit` and `typeII_sharp` assume the route's Type II estimate (`hII : SieveRoute.TypeIIAt`). Let `f0`
be smooth and real with support in `[1/2, 2]`, `K₀ ≥ 0` and `e₁ > 0`. A *family* has: a large `q`; `P` with
`q^{w₁L} ≤ P ≤ q^{w₂L}`; `S ⊆ (P, 2P]` with coefficients `a_m`; `K ≤ K₀` primes `x_i` of `Sp`'s ranges at the scales
`Q_i ≥ q^{e₁}` (`primesTo Q_i`, the primes up to `2Q_i`), with the weights `f0(x_i/Q_i)` and `∏_i Q_i ≤ 2^{K₀}q^L/P`;
and `J` forms `ℓ_j(m, x) = φ_j(m) + Σ_i e_{ji} log x_i`. For a unit `a` mod `q`, its `A − B/φ(q)` is `Dsum`: the sum of
its weights times `1[n ≡ a] − 1[(n, q) = 1]/φ(q)` at `n = m∏_i x_i`.

* `family_bound` (Lemma 4′ with Proposition 3′): let `J` continuous integrable `g_j` with integrable `𝓕g_j` be applied
  to the forms, with `2π(Σ_j |e_{ji}|)T₀ ≤ q^η` for each `i` and `0 < η ≤ 10⁻⁵`. The sum over `χ ≠ 1` of the family's
  twisted sums is at most `q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2} ∏_j ‖𝓕g_j‖₁`, plus the number of characters `χ ≠ 1` times
  `Σ_m |a_m| ∏_i Σ_p |f0(p/Q_i)|` times `Σ_j (∫_{|t|>T₀} |𝓕g_j(t)| dt) ∏_{i≠j} ‖𝓕g_i‖₁`.
* `typeII_sharp_explicit` (Lemma 4″): let also `0 ≤ f0 ≤ F₀`, and cut a family with at least one prime by `J` sharp
  comparisons `P_j`, where `P_j` holds when `ℓ_j > 0` and implies `ℓ_j ≥ 0`. If `0 < θ ≤ 1 ≤ Λ`, `ℓ_j ≤ Λ` on the
  family, each comparison has a pivot prime with coefficient `±1`, `T₀ ≥ 1`, `k ≥ 2` and
  `2π(Σ_j |e_{ji}|)T₀ ≤ q^{1/100000}` for each `i`, then `|A − B/φ(q)|` is at most an explicit bound in the cut-off's
  masses and tails (`massB`, `tailB`) and the pivots' counts.
* `typeII_sharp`: fix also `J₀`, `E₀ ≥ 0`, `Λ₀ ≥ 0` and `A₀ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀`,
  every such family with `|a_m| ≤ A₀` for every `m`, `J ≤ J₀`, `|e_{ji}| ≤ E₀`, `ℓ_j ≤ Λ₀ log q` on the family and
  pivots as above has `|A − B/φ(q)| ≤ A₀q^{L−δ}/φ(q)`.

The proof:

* `sum_twist_eq`, `inner_factor`: a separated family sum factors into the twisted `m`-sum and the twisted prime sums,
  which are `SieveWeight.Sp` at the heights `−2πΣ_j ξ_je_{ji}`.
* `family_bound`: `SieveSep.sum_sep` writes each character's sum as an integral over `ℝ^J`. On the box `|ξ_j| ≤ T₀` the
  heights are at most `q^η`, and `hII` bounds the sum over `χ ≠ 1`; everywhere the trivial bound holds;
  `SieveSep.sep_bound` combines the two.
* `integral_norm_GC_le`, `mass_GC_le`, `tail_GC_le`: for `SieveSmooth`'s cut-off `G` with `0 < θ ≤ 2Λ`,
  `‖G‖₁ ≤ 2Λ + θ` and `‖𝓕G‖₁ ≤ π(2Λ + θ) + c₂/(2πθ)`, and for `θ > 0`, `Λ ≥ 0`, `k ≥ 2` and `T₀ ≥ 1`,
  `∫_{|ξ|>T₀} |𝓕G| ≤ 2π·2θ^{1−k}c_k(2π)^{−k}T₀^{2−k}`, with `c_k = ‖g^{(k)}‖₁`.
* `dw`, `dw_eq`, `Dsum`, `norm_Dsum_le`: orthogonality, `1[n ≡ a] − 1[(n, q) = 1]/φ(q) = φ(q)⁻¹Σ_{χ≠1} χ(a⁻¹)χ(n)` for
  a unit `a`.
* `abs_prod_sub_prod_le`, `norm_Dsum_sharp_le`: sharp against smooth, from `|∏_j I_j − ∏_j G_j| ≤ Σ_j |I_j − G_j|` for
  values in `[0, 1]`.
* `abs_ind_sub_G_le`, `card_short_le`, `pivot_sum_le`, `pivot_term_le`: near the boundary `|1[P_j] − G| ≤ G̃`, with
  `G̃(u) = G_{θ,θ}(u + θ)`, and over the pivot prime `Σ_y f0(y/Q)G̃(…) ≤ F₀((e^{3θ} − 1)2Q + 1)`.
* `Dsum_sharp_le`, `typeII_sharp_explicit`: the smoothed family and the `J` near-boundary families by `family_bound`,
  and the pivots' counts by `pivot_sum_le`.
* `typeII_sharp`: `θ = q^{−ε₂}` with `ε₂ = 1/(400000(J₀ + 1))`, `Λ = Λ₀ log q + 1`, `T₀ = q^{1/200000}` and
  `k = 1200003`. The masses are at most `Cq^{ε₂}` (`massB_le`) and the tails at most `c′q^{−3}` (`tailB_le`). The box
  and the pivots' counts are at most constants times `A₀q^L` (`box_le`, `pivot_le`). So the bound is at most
  `A₀q^L/φ(q)` times `a₁q^{−7/400000} + a₂q^{−1} + a₃(12q^{−ε₂} + q^{−e₁})`, which is at most `q^{−δ}` for large `q`,
  with `δ = min(ε₂, e₁)/2` (`bracket_le`).

The file imports `SieveSep.lean` and `SieveRoute.lean`.
-/
import SieveSep
import SieveRoute

open MeasureTheory Real Complex FourierTransform Finset SieveRoute

namespace SieveFamily

variable {q : ℕ} [NeZero q]

/-- The primes of `Sp`'s range at scale `Q`. -/
noncomputable def primesTo (Q : ℝ) : Finset ℕ := (Finset.range (⌊2 * Q⌋₊ + 1)).filter Nat.Prime

omit [NeZero q] in
/-- For `Q > 0`, a prime sum with the twist `p^{2πiH}` is `Q^{2πiH}` times `Sp` at the height `−2πH`. -/
theorem sum_twist_eq (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) {Q : ℝ} (hQ : 0 < Q) (H : ℝ) :
    ∑ p ∈ primesTo Q, χ p * (f0 (p / Q) : ℂ) * Complex.exp (2 * π * I * H * Real.log p) =
      Complex.exp (2 * π * I * H * Real.log Q) * SieveWeight.Sp χ f0 Q (-(2 * π * H)) := by
  rw [SieveWeight.Sp, primesTo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hz : (0 : ℝ) < (p : ℝ) / Q := div_pos hp0 hQ
  have hcpow : ((((p : ℝ) / Q : ℝ)) : ℂ) ^ (-((-(2 * π * H) : ℝ) : ℂ) * I) =
      Complex.exp (2 * π * I * H * Real.log p) * Complex.exp (-(2 * π * I * H * Real.log Q)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'), ← Complex.ofReal_log hz.le,
      Real.log_div hp0.ne' hQ.ne', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcpow]
  have hinv : Complex.exp (2 * π * I * H * Real.log Q) * Complex.exp (-(2 * π * I * H * Real.log Q)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(χ p * (f0 (p / Q) : ℂ) * Complex.exp (2 * π * I * H * Real.log p))) * hinv

/-! ### The cut-off's Fourier transform: mass and tails -/

section Cutoff

open SieveSmooth

variable {θ Λ : ℝ}

/-- `‖G‖₁ ≤ 2Λ + θ` for `0 < θ ≤ 2Λ`. -/
theorem integral_norm_GC_le (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) : ∫ u, ‖GC θ Λ u‖ ≤ 2 * Λ + θ := by
  have hΛ : 0 ≤ Λ := by linarith
  have hpt : ∀ u, ‖GC θ Λ u‖ ≤ Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ)) u := by
    intro u
    rw [GC_eq_G, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G_nonneg hθ hθΛ u)]
    by_cases hu : u ∈ Set.Icc 0 (2 * Λ + θ)
    · rw [Set.indicator_of_mem hu]; exact G_le_one u
    · rw [Set.indicator_of_notMem hu, G_eq_zero hθ hΛ hu]
  have hi : Integrable (Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  calc ∫ u, ‖GC θ Λ u‖ ≤ ∫ u, Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ)) u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
          (Filter.Eventually.of_forall hpt)
    _ = 2 * Λ + θ := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, Measure.real,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

/-- The mass of `𝓕G`: `‖𝓕G‖₁ ≤ π(2Λ + θ) + c₂/(2πθ)` for `0 < θ ≤ 2Λ`, with `c₂ = ‖g″‖₁`. -/
theorem mass_GC_le (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) :
    ∫ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ π * (2 * Λ + θ) + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ) := by
  have hΛ : 0 ≤ Λ := by linarith
  set c₂ := ∫ v, ‖iteratedDeriv 2 gc v‖ with hc₂
  have hc₂0 : 0 ≤ c₂ := integral_nonneg fun _ => norm_nonneg _
  set N := (2 * Λ + θ) + c₂ / (2 * π ^ 2 * θ) with hN
  have hpt : ∀ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ N * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have h0 := (norm_fourier_GC_le (θ := θ) (Λ := Λ) ξ).trans (integral_norm_GC_le hθ hθΛ)
    have h2 := pow_mul_norm_fourier_GC_le hθ hΛ (K := 2) (by norm_num) ξ
    rw [← hc₂] at h2
    have hsq : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
    rw [hsq] at h2
    have hpi : 0 < 4 * π ^ 2 := by positivity
    have hF := norm_nonneg (𝓕 (GC θ Λ) ξ)
    have h2' : ξ ^ 2 * ‖𝓕 (GC θ Λ) ξ‖ ≤ c₂ / (2 * π ^ 2 * θ) := by
      have e : 2 * (θ⁻¹ ^ 2 * θ) * c₂ = 4 * π ^ 2 * (c₂ / (2 * π ^ 2 * θ)) := by
        field_simp
        ring
      rw [e] at h2
      nlinarith
    have hpos : 0 < 1 + ξ ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    nlinarith
  have hint : Integrable fun ξ : ℝ => N * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul N
  calc ∫ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ ∫ ξ : ℝ, N * (1 + ξ ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = π * (2 * Λ + θ) + c₂ / (2 * π * θ) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hN]
        field_simp

/-- The tail of `𝓕G` beyond `T₀ ≥ 1`: at most `2π·2θ^{1−k}c_k(2π)^{−k}T₀^{2−k}` for `θ > 0`, `Λ ≥ 0` and `k ≥ 2`,
with `c_k = ‖g^{(k)}‖₁`. -/
theorem tail_GC_le (hθ : 0 < θ) (hΛ : 0 ≤ Λ) {k : ℕ} (hk : 2 ≤ k) {T₀ : ℝ} (hT₀ : 1 ≤ T₀) :
    ∫ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ ≤
      2 * π * ((2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ := by
  set N := 2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖ with hN
  have hN0 : 0 ≤ N := by
    rw [hN]
    have := integral_nonneg (μ := volume) (f := fun v : ℝ => ‖iteratedDeriv k gc v‖) (fun v => norm_nonneg _)
    positivity
  set C := 2 * (N / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ with hC
  have hpt : ∀ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ ≤ C * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    by_cases hξ : ξ ∈ {t : ℝ | T₀ < |t|}
    · rw [Set.indicator_of_mem hξ]
      have hξ1 : T₀ < |ξ| := hξ
      have hξ0 : 0 < |ξ| := by linarith
      have h := pow_mul_norm_fourier_GC_le hθ hΛ (K := k) (by omega) ξ
      rw [← hN] at h
      have hpk : 0 < (2 * π * |ξ|) ^ k := by positivity
      have hF : ‖𝓕 (GC θ Λ) ξ‖ ≤ N / (2 * π * |ξ|) ^ k := by rw [le_div_iff₀ hpk]; linarith
      -- `|ξ|^k ≥ T₀^{k−2}ξ²` and `ξ² ≥ (1 + ξ²)/2`
      have hk2 : |ξ| ^ k = |ξ| ^ (k - 2) * ξ ^ 2 := by
        rw [← sq_abs ξ, ← pow_add]; congr 1; omega
      have hT : T₀ ^ (k - 2) ≤ |ξ| ^ (k - 2) := pow_le_pow_left₀ (by linarith) hξ1.le _
      have hTpos : 0 < T₀ ^ (k - 2) := by positivity
      have hsq : (1 + ξ ^ 2) / 2 ≤ ξ ^ 2 := by
        have : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith
        linarith
      have hden : T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k ≤ (2 * π * |ξ|) ^ k := by
        rw [mul_pow (2 * π) |ξ| k, hk2]
        have h2pk : 0 < (2 * π) ^ k := by positivity
        have : T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) ≤ |ξ| ^ (k - 2) * ξ ^ 2 :=
          mul_le_mul hT hsq (by positivity) (by positivity)
        nlinarith
      have hdpos : 0 < T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k := by positivity
      calc ‖𝓕 (GC θ Λ) ξ‖ ≤ N / (2 * π * |ξ|) ^ k := hF
        _ ≤ N / (T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k) :=
          div_le_div_of_nonneg_left hN0 hdpos hden
        _ = C * (1 + ξ ^ 2)⁻¹ := by rw [hC]; field_simp
    · rw [Set.indicator_of_notMem hξ]; positivity
  have hint : Integrable fun ξ : ℝ => C * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul C
  calc ∫ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ
      ≤ ∫ ξ : ℝ, C * (1 + ξ ^ 2)⁻¹ := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _) hint
          (Filter.Eventually.of_forall hpt)
    _ = 2 * π * (N / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hC]; ring

end Cutoff

/-! ### Orthogonality -/

section Orth

open Classical

/-- The weight of `A − B/φ(q)` at `n`: `1[n ≡ a] − 1[(n, q) = 1]/φ(q)`. -/
noncomputable def dw (q : ℕ) (a : ZMod q) (n : ℕ) : ℂ :=
  (if (n : ZMod q) = a then 1 else 0) - (if IsUnit (n : ZMod q) then 1 else 0) / q.totient

/-- **Orthogonality**: `1[n ≡ a] − 1[(n, q) = 1]/φ(q) = φ(q)⁻¹ Σ_{χ≠1} χ(a⁻¹)χ(n)` for `a` a unit. -/
theorem dw_eq {a : ZMod q} (ha : IsUnit a) (n : ℕ) :
    dw q a n = (q.totient : ℂ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * χ n := by
  have htot : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  have hsplit : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n =
      (1 : DirichletCharacter ℂ q) a⁻¹ * (1 : DirichletCharacter ℂ q) n +
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * χ n := by
    rw [Finset.filter_ne']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ * (1 : DirichletCharacter ℂ q) n =
      if IsUnit (n : ZMod q) then 1 else 0 := by
    rw [MulChar.one_apply (IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit a ha)), one_mul]
    by_cases hu : IsUnit (n : ZMod q)
    · simp [MulChar.one_apply hu, hu]
    · simp [MulChar.map_nonunit _ hu, hu]
  rw [hsplit, hone] at horth
  rw [dw]
  field_simp
  have hcase : (if a = (n : ZMod q) then (q.totient : ℂ) else 0) =
      q.totient * (if (n : ZMod q) = a then 1 else 0) := by
    by_cases h : (n : ZMod q) = a
    · simp [h]
    · have h' : ¬ a = (n : ZMod q) := fun h' => h h'.symm
      simp [h, h']
  rw [hcase] at horth
  rcases Classical.em (IsUnit (n : ZMod q)) with hu | hu
  · simp only [hu, ↓reduceIte] at horth ⊢
    linear_combination -horth
  · simp only [hu, ↓reduceIte] at horth ⊢
    linear_combination -horth

/-- The difference `D(w) = Σ_x w(x)(1[n(x) ≡ a] − 1[(n(x), q) = 1]/φ(q))` of a weighted finite family. -/
noncomputable def Dsum {X : Type*} (q : ℕ) (a : ZMod q) (T : Finset X) (n : X → ℕ) (w : X → ℂ) : ℂ :=
  ∑ x ∈ T, w x * dw q a (n x)

/-- For `a` a unit, `|D(w)| ≤ φ(q)⁻¹ Σ_{χ≠1} |Σ_x w(x)χ(n(x))|`. -/
theorem norm_Dsum_le {X : Type*} {a : ZMod q} (ha : IsUnit a) (T : Finset X) (n : X → ℕ) (w : X → ℂ) :
    ‖Dsum q a T n w‖ ≤ (q.totient : ℝ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ x ∈ T, w x * χ (n x)‖ := by
  have heq : Dsum q a T n w = (q.totient : ℂ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * ∑ x ∈ T, w x * χ (n x) := by
    rw [Dsum]
    simp_rw [dw_eq ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)) (by positivity)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

end Orth

/-- For `a_j, b_j ∈ [0, 1]`: `|∏ a_j − ∏ b_j| ≤ Σ |a_j − b_j|`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1) : |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hih := ih ha' hb'
    have haj := ha j (Finset.mem_insert_self j s)
    have hbs : 0 ≤ ∏ i ∈ s, b i ∧ ∏ i ∈ s, b i ≤ 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hb' i hi).1, Finset.prod_le_one₀ (fun i hi => (hb' i hi).1)
        fun i hi => (hb' i hi).2⟩
    have heq : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [heq]
    calc |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i|
        ≤ |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| := abs_add_le _ _
      _ = |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 := by
          gcongr
          · rw [abs_of_nonneg haj.1]; exact haj.2
          · rw [abs_of_nonneg hbs.1]; exact hbs.2
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

section Sharp

open Classical

/-- **Sharp against smooth.** Let the comparisons `I_j ∈ [0, 1]` be
replaced by `G_j ∈ [0, 1]`, with `|I_j − G_j| ≤ M_j`. Then
`|D(wΠI)| ≤ |D(wΠG)| + Σ_j (2φ(q)⁻¹ Σ_x |w(x)|M_j(x) + |D(|w|M_j)|)`. -/
theorem norm_Dsum_sharp_le {X : Type*} {a : ZMod q} (T : Finset X) (n : X → ℕ) (w : X → ℂ) {J : ℕ}
    (I G M : Fin J → X → ℝ) (hI : ∀ j x, 0 ≤ I j x ∧ I j x ≤ 1) (hG : ∀ j x, 0 ≤ G j x ∧ G j x ≤ 1)
    (hM : ∀ j x, |I j x - G j x| ≤ M j x) :
    ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ))‖ ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
      ∑ j, (2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x +
        ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖) := by
  set φq : ℝ := (q.totient : ℝ) with hφq
  have hφ0 : 0 < φq := by rw [hφq]; exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  -- the indicator weights
  set A : ℕ → ℝ := fun m => if (m : ZMod q) = a then 1 else 0 with hA
  set U : ℕ → ℝ := fun m => if IsUnit (m : ZMod q) then 1 else 0 with hU
  have hdw : ∀ m, dw q a m = ((A m - U m / φq : ℝ) : ℂ) := fun m => by
    rw [dw, hA, hU]; push_cast; split_ifs <;> simp [hφq]
  have hA0 : ∀ m, 0 ≤ A m := fun m => by simp only [hA]; split_ifs <;> norm_num
  have hU0 : ∀ m, 0 ≤ U m ∧ U m ≤ 1 := fun m => by simp only [hU]; split_ifs <;> norm_num
  have hdwn : ∀ m, ‖dw q a m‖ ≤ A m + U m / φq := fun m => by
    rw [hdw, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hA0 m), abs_of_nonneg (div_nonneg (hU0 m).1 hφ0.le)]
  -- the difference of the two sums
  have hdiff : ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)) - Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ ≤
      ∑ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) := by
    rw [Dsum, Dsum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x ∈ T, ‖w x * (∏ j, (I j x : ℂ)) * dw q a (n x) - w x * (∏ j, (G j x : ℂ)) * dw q a (n x)‖
        ≤ ∑ x ∈ T, ‖w x‖ * (∑ j, M j x) * (A (n x) + U (n x) / φq) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hprod : ‖(∏ j, (I j x : ℂ)) - ∏ j, (G j x : ℂ)‖ ≤ ∑ j, M j x := by
            rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            exact (abs_prod_sub_prod_le _ _ _ (fun j _ => hI j x) fun j _ => hG j x).trans
              (Finset.sum_le_sum fun j _ => hM j x)
          have e : w x * (∏ j, (I j x : ℂ)) * dw q a (n x) - w x * (∏ j, (G j x : ℂ)) * dw q a (n x) =
              w x * ((∏ j, (I j x : ℂ)) - ∏ j, (G j x : ℂ)) * dw q a (n x) := by ring
          rw [e, norm_mul, norm_mul]
          have hd := hdwn (n x)
          have hw := norm_nonneg (w x)
          have hMs : 0 ≤ ∑ j, M j x := Finset.sum_nonneg fun j _ => le_trans (abs_nonneg _) (hM j x)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hprod hw) hd (norm_nonneg _) (mul_nonneg hw hMs)
      _ = ∑ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
  -- the `A`-part of each near-boundary sum
  have hpart : ∀ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) ≤
      2 * φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x + ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖ := by
    intro j
    have hD : (Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))) =
        ((∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) : ℝ) : ℂ) := by
      rw [Dsum]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hdw]; push_cast; ring
    have hre : ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) ≤
        ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖ := by
      rw [hD, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    have hM0 : ∀ x, 0 ≤ M j x := fun x => le_trans (abs_nonneg _) (hM j x)
    have hU1 : ∑ x ∈ T, ‖w x‖ * M j x * (U (n x) / φq) ≤ φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 : U (n x) / φq ≤ φq⁻¹ := by
        rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (inv_nonneg.2 hφ0.le) (hU0 (n x)).2
      have h0 : 0 ≤ ‖w x‖ * M j x := mul_nonneg (norm_nonneg _) (hM0 x)
      nlinarith
    have hsplit : ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) =
        ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) + 2 * ∑ x ∈ T, ‖w x‖ * M j x * (U (n x) / φq) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hsplit]
    nlinarith
  calc ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ))‖
      ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
        ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)) - Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ := by
        have := norm_sub_norm_le (Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)))
          (Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ)))
        linarith
    _ ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
        ∑ j, (2 * φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x + ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖) := by
        gcongr
        exact hdiff.trans (Finset.sum_le_sum fun j _ => hpart j)

end Sharp

/-! ### The pivot -/

/-- Splitting a sum over a box at the coordinate `p`. -/
theorem sum_piFinset_pivot {n : ℕ} {α : Type*} (t : Fin (n + 1) → Finset α) (p : Fin (n + 1))
    (F : (Fin (n + 1) → α) → ℝ) :
    ∑ x ∈ Fintype.piFinset t, F x =
      ∑ y ∈ t p, ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), F (p.insertNth y z) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x p, p.removeNth x)) (fun yz => p.insertNth yz.1 yz.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Fin.mem_piFinset_iff_pivot_removeNth p] at hx
    exact Finset.mem_product.2 ⟨hx.1, hx.2⟩
  · intro yz hyz
    rw [Finset.mem_product] at hyz
    rw [Fin.mem_piFinset_iff_pivot_removeNth p]
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
    exact hyz
  · intro x _
    simp
  · intro yz _
    simp
  · intro x _
    simp

/-- **The pivot count.** Let `u_i ≥ 0`. If for every choice `z` of the other coordinates, the pivot's sum
`Σ_{y ∈ t p} u_p(y)v(insertNth p y z)` is at most `C`, then the box sum of `∏_i u_i(x_i)·v(x)` is at most `C` times
the product of the other coordinates' sums. -/
theorem pivot_sum_le {n : ℕ} {α : Type*} (t : Fin (n + 1) → Finset α) (p : Fin (n + 1)) (u : Fin (n + 1) → α → ℝ)
    (hu : ∀ i y, 0 ≤ u i y) (v : (Fin (n + 1) → α) → ℝ) {C : ℝ}
    (hC : ∀ z : Fin n → α, ∑ y ∈ t p, u p y * v (p.insertNth y z) ≤ C) :
    ∑ x ∈ Fintype.piFinset t, (∏ i, u i (x i)) * v x ≤
      C * ∏ i : Fin n, ∑ y ∈ t (p.succAbove i), u (p.succAbove i) y := by
  rw [sum_piFinset_pivot t p, Finset.sum_comm]
  have hfac : ∀ y (z : Fin n → α), (∏ i, u i ((p.insertNth y z : Fin (n + 1) → α) i)) =
      u p y * ∏ i : Fin n, u (p.succAbove i) (z i) := by
    intro y z
    rw [Fin.prod_univ_succAbove _ p]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  calc ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), ∑ y ∈ t p,
        (∏ i, u i ((p.insertNth y z : Fin (n + 1) → α) i)) * v (p.insertNth y z)
      = ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)),
          (∏ i : Fin n, u (p.succAbove i) (z i)) * ∑ y ∈ t p, u p y * v (p.insertNth y z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfac]; ring
    _ ≤ ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), (∏ i : Fin n, u (p.succAbove i) (z i)) * C :=
        Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hC z) (Finset.prod_nonneg fun i _ => hu _ _)
    _ = C * ∏ i : Fin n, ∑ y ∈ t (p.succAbove i), u (p.succAbove i) y := by
        rw [← Finset.sum_mul, mul_comm, Finset.prod_univ_sum]

/-- At most `(ρ − 1)R + 1` integers `y ≤ R` lie in `[Y, ρY]`, for `Y > 0`, `ρ ≥ 1` and `R ≥ 0`. -/
theorem card_short_le {Y ρ R : ℝ} (hY : 0 < Y) (hρ : 1 ≤ ρ) (hR : 0 ≤ R) (s : Finset ℕ)
    (hs : ∀ y ∈ s, Y ≤ y ∧ (y : ℝ) ≤ ρ * Y ∧ (y : ℝ) ≤ R) : (s.card : ℝ) ≤ (ρ - 1) * R + 1 := by
  set b : ℝ := min (ρ * Y) R with hb
  have hsub : s ⊆ Finset.Icc ⌈Y⌉₊ ⌊b⌋₊ := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hs y hy
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.2 h1, Nat.le_floor (le_min h2 h3)⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcard' : (s.card : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  have hb0 : 0 ≤ b := le_min (by positivity) hR
  by_cases hle : ⌈Y⌉₊ ≤ ⌊b⌋₊ + 1
  · rw [Nat.cast_sub hle] at hcard'
    push_cast at hcard'
    have hfl : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb0
    have hce : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    -- `b − Y ≤ (ρ − 1)R`, or else nothing is counted
    by_cases hYR : Y ≤ R
    · have : b - Y ≤ (ρ - 1) * R := by
        have h1 : b ≤ ρ * Y := min_le_left _ _
        nlinarith
      linarith
    · push Not at hYR
      have : b ≤ R := min_le_right _ _
      have hneg : (s.card : ℝ) < 1 := by linarith
      have h0 : s.card = 0 := by
        have : s.card < 1 := by exact_mod_cast hneg
        omega
      rw [h0, Nat.cast_zero]
      nlinarith
  · push Not at hle
    rw [Nat.sub_eq_zero_of_le hle.le, Nat.cast_zero] at hcard'
    nlinarith

open SieveSmooth in
/-- Let `θ > 0`, `Λ ≥ 0` and `u ≤ Λ`, and let `P` hold when `u > 0` and imply `u ≥ 0`. Then the narrow cut-off
`G̃(u) = G_{θ,θ}(u + θ)` majorizes `|1[P] − G_{θ,Λ}(u)|`. -/
theorem abs_ind_sub_G_le {θ Λ u : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ) (hu : u ≤ Λ) (P : Prop) [Decidable P]
    (hP : (0 < u → P) ∧ (P → 0 ≤ u)) :
    |(if P then (1 : ℝ) else 0) - G θ Λ u| ≤ G θ θ (u + θ) := by
  obtain ⟨h0, h1, h2⟩ := indicator_sub_G hθ hΛ hu P hP
  rw [abs_of_nonneg h0]
  by_cases hin : 0 ≤ u ∧ u < θ
  · have hG : G θ θ (u + θ) = 1 := by
      rw [G, Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hθ]; linarith),
        Real.smoothTransition.zero_of_nonpos (by
          apply div_nonpos_of_nonpos_of_nonneg _ hθ.le; linarith)]
      norm_num
    rw [hG]; exact h1
  · have hout : u < 0 ∨ θ ≤ u := by
      by_contra hc; push Not at hc; exact hin ⟨hc.1, hc.2⟩
    rw [h2 hout]
    exact G_nonneg hθ (by linarith) _

open SieveSmooth in
/-- **The pivot's sum.** If the form is `c + σ log y` in the pivot `y`, with `σ = ±1`, then for `θ > 0`, `Q > 0`
and `0 ≤ f0 ≤ F₀` the primes `y` of `Sp`'s range at scale `Q` give
`Σ_y f0(y/Q) G̃(c + σ log y) ≤ F₀((e^{3θ} − 1)2Q + 1)`. -/
theorem pivot_term_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {θ Q c σ : ℝ}
    (hθ : 0 < θ) (hQ : 0 < Q) (hσ : σ = 1 ∨ σ = -1) :
    ∑ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤
      F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q) + 1) := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  -- the pivots that count lie in `[Y, e^{3θ}Y]`
  obtain ⟨Y, hY, hYb⟩ : ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, 0 < y → -θ ≤ c + σ * Real.log y →
      c + σ * Real.log y ≤ 2 * θ → Y ≤ y ∧ y ≤ Real.exp (3 * θ) * Y := by
    rcases hσ with rfl | rfl
    · refine ⟨Real.exp (-θ - c), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    · refine ⟨Real.exp (c - 2 * θ), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  set s := (primesTo Q).filter (fun y : ℕ => -θ ≤ c + σ * Real.log y ∧ c + σ * Real.log y ≤ 2 * θ) with hs
  have hterm : ∀ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤
      if y ∈ s then F₀ else 0 := by
    intro y hy
    have hG1 := G_le_one (θ := θ) (Λ := θ) (c + σ * Real.log y + θ)
    have hG0 := G_nonneg hθ (by linarith : θ ≤ 2 * θ) (c + σ * Real.log y + θ)
    split_ifs with hys
    · calc f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤ F₀ * 1 :=
            mul_le_mul (hF₀ _) hG1 hG0 hF0
        _ = F₀ := mul_one _
    · rw [hs, Finset.mem_filter] at hys
      push Not at hys
      have hout : c + σ * Real.log y + θ ∉ Set.Icc 0 (2 * θ + θ) := by
        rintro ⟨h1, h2⟩
        exact absurd (by linarith : c + σ * Real.log y ≤ 2 * θ) (not_le.2 (hys hy (by linarith)))
      rw [G_eq_zero hθ hθ.le hout, mul_zero]
  calc ∑ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ)
      ≤ ∑ y ∈ primesTo Q, (if y ∈ s then F₀ else 0) := Finset.sum_le_sum hterm
    _ = F₀ * s.card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hfs : (primesTo Q).filter (fun y => y ∈ s) = s := by
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        rw [hfs]
    _ ≤ F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hF0
        refine card_short_le hY (by
          have := Real.add_one_le_exp (3 * θ); linarith) (by positivity) s fun y hy => ?_
        rw [hs, Finset.mem_filter] at hy
        obtain ⟨hyp, h1, h2⟩ := hy
        rw [primesTo, Finset.mem_filter, Finset.mem_range] at hyp
        have hy0 : (0 : ℝ) < y := by exact_mod_cast hyp.2.pos
        obtain ⟨hl, hr⟩ := hYb y hy0 h1 h2
        refine ⟨hl, hr, ?_⟩
        have hyle : y ≤ ⌊2 * Q⌋₊ := Nat.lt_succ_iff.1 hyp.1
        exact le_trans (by exact_mod_cast hyle) (Nat.floor_le (by positivity))

section SharpFamily

open SieveSmooth Classical

end SharpFamily

/-- There are at most `φ(q)` characters `χ ≠ 1`. -/
theorem card_chars_le : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
  have h : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h2 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q)) (fun χ => χ ≠ 1)
  rw [Finset.card_univ, h] at h2
  exact_mod_cast h2

/-- Products of masses: if `0 ≤ m_j ≤ M` then `∏ m_j ≤ M^J`. -/
theorem prod_masses_le {J : ℕ} (m : Fin J → ℝ) {M : ℝ} (hm0 : ∀ j, 0 ≤ m j) (hm : ∀ j, m j ≤ M) :
    ∏ j, m j ≤ M ^ J := by
  calc ∏ j, m j ≤ ∏ _j : Fin J, M := Finset.prod_le_prod₀ (fun j _ => hm0 j) fun j _ => hm j
    _ = M ^ J := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `Σ_j t_j ∏_{i≠j} m_i ≤ JτM^J` for `0 ≤ m_j ≤ M`, `0 ≤ t_j ≤ τ` and `M ≥ 1`. -/
theorem sum_tails_le {J : ℕ} [DecidableEq (Fin J)] (m t : Fin J → ℝ) {M τ : ℝ} (hM : 1 ≤ M) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m j ≤ M) (ht0 : ∀ j, 0 ≤ t j) (ht : ∀ j, t j ≤ τ) :
    ∑ j, t j * ∏ i ∈ Finset.univ.erase j, m i ≤ J * τ * M ^ J := by
  calc ∑ j, t j * ∏ i ∈ Finset.univ.erase j, m i ≤ ∑ _j : Fin J, τ * M ^ J := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hτ : 0 ≤ τ := le_trans (ht0 j) (ht j)
        have hp : ∏ i ∈ Finset.univ.erase j, m i ≤ M ^ J := by
          calc ∏ i ∈ Finset.univ.erase j, m i ≤ ∏ _i ∈ Finset.univ.erase j, M :=
                Finset.prod_le_prod₀ (fun i _ => hm0 i) fun i _ => hm i
            _ = M ^ (J - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
                  Fintype.card_fin]
            _ ≤ M ^ J := pow_le_pow_right₀ hM (Nat.sub_le J 1)
        exact mul_le_mul (ht j) hp (Finset.prod_nonneg fun i _ => hm0 i) hτ
    _ = J * τ * M ^ J := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

section Explicit

open SieveSmooth Classical
open scoped ContDiff

/-- The mass bound `M(θ, Λ) = π(2Λ + θ) + c₂/(2πθ)` of `mass_GC_le`. -/
noncomputable def massB (θ Λ : ℝ) : ℝ := π * (2 * Λ + θ) + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ)

/-- The tail bound of `tail_GC_le`. -/
noncomputable def tailB (θ T₀ : ℝ) (k : ℕ) : ℝ :=
  2 * π * ((2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹

end Explicit

/-! ### Elementary bounds for the asymptotic form -/

/-- For `Q ≥ 1`, `#primesTo Q ≤ 3Q`. -/
theorem card_primesTo_le {Q : ℝ} (hQ : 1 ≤ Q) : ((primesTo Q).card : ℝ) ≤ 3 * Q := by
  have h1 : (primesTo Q).card ≤ ⌊2 * Q⌋₊ + 1 := by
    rw [primesTo]; exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
  have h2 : ((⌊2 * Q⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Q + 1 := by
    push_cast; linarith [Nat.floor_le (show (0 : ℝ) ≤ 2 * Q by linarith)]
  calc ((primesTo Q).card : ℝ) ≤ ((⌊2 * Q⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ 2 * Q + 1 := h2
    _ ≤ 3 * Q := by linarith

/-- For `0 ≤ f0 ≤ F₀` and `Q ≥ 1`, `Σ_{p ∈ primesTo Q} |f0(p/Q)| ≤ 3F₀Q`. -/
theorem sum_f0_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ p ∈ primesTo Q, |f0 (p / Q)| ≤ 3 * F₀ * Q := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  calc ∑ p ∈ primesTo Q, |f0 (p / Q)| ≤ ∑ _p ∈ primesTo Q, F₀ :=
        Finset.sum_le_sum fun p _ => by rw [abs_of_nonneg (hf0 _)]; exact hF₀ _
    _ = (primesTo Q).card * F₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * Q * F₀ := mul_le_mul_of_nonneg_right (card_primesTo_le hQ) hF0
    _ = 3 * F₀ * Q := by ring

/-- For `S ⊆ (P, 2P]` and `|a_m| ≤ A₀` for every `m`, `Σ_{m∈S} |a_m| ≤ PA₀`. -/
theorem sum_norm_le {S : Finset ℕ} {P : ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ} {A₀ : ℝ}
    (hA : ∀ m, ‖acoef m‖ ≤ A₀) : ∑ m ∈ S, ‖acoef m‖ ≤ P * A₀ := by
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hcard : (S.card : ℝ) ≤ P := by
    have := Finset.card_le_card hS
    rw [Nat.card_Ioc] at this
    have h2 : 2 * P - P = P := by omega
    rw [h2] at this
    exact_mod_cast this
  calc ∑ m ∈ S, ‖acoef m‖ ≤ ∑ _m ∈ S, A₀ := Finset.sum_le_sum fun m _ => hA m
    _ = S.card * A₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * A₀ := mul_le_mul_of_nonneg_right hcard hA0

/-- For `P > 0`, `S ⊆ (P, 2P]` and `|a_m| ≤ A₀` for every `m`, `(Σ_{m∈S} |a_m|²/P)^{1/2} ≤ A₀`. -/
theorem sqrt_sum_sq_le {S : Finset ℕ} {P : ℕ} (hP : 0 < P) (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ}
    {A₀ : ℝ} (hA : ∀ m, ‖acoef m‖ ≤ A₀) : Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) ≤ A₀ := by
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hcard : (S.card : ℝ) ≤ P := by
    have := Finset.card_le_card hS
    rw [Nat.card_Ioc] at this
    have h2 : 2 * P - P = P := by omega
    rw [h2] at this
    exact_mod_cast this
  rw [Real.sqrt_le_left hA0, div_le_iff₀ hP']
  calc ∑ m ∈ S, ‖acoef m‖ ^ 2 ≤ ∑ _m ∈ S, A₀ ^ 2 :=
        Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (hA m) 2
    _ = S.card * A₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * A₀ ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = A₀ ^ 2 * P := by ring

/-- `e^{3θ} − 1 ≤ 6θ` for `0 ≤ θ ≤ 1/3`. -/
theorem exp_three_sub_one_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 3) : Real.exp (3 * θ) - 1 ≤ 6 * θ := by
  have hx : |3 * θ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.exp_bound hx (n := 1) (by norm_num)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  have h' := (abs_le.1 h).2
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * θ)] at h'
  norm_num at h'
  linarith

/-! ### The asymptotic form -/

section Helpers

open SieveSmooth Filter Asymptotics

/-- For `r > 0` and `Λ₀ ≥ 0`, eventually in `x`: `π(2Λ₀ log x + 3) ≤ x^r`. -/
theorem ev_pi_log_le {r Λ₀ : ℝ} (hr : 0 < r) (hΛ₀ : 0 ≤ Λ₀) :
    ∀ᶠ x : ℝ in atTop, π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ r := by
  have hpi := Real.pi_pos
  have hc : (0 : ℝ) < 1 / (4 * π * Λ₀ + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).def hc
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (6 * π)
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx3
  have hxr : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hxr] at hx1
  have h4 : 2 * π * Λ₀ * Real.log x ≤ 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) :=
    mul_le_mul_of_nonneg_left hx1 (by positivity)
  have h6 : 2 * π * Λ₀ / (4 * π * Λ₀ + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hpi.le hΛ₀]
  have h5 : 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) ≤ x ^ r / 2 := by
    rw [show 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) = (2 * π * Λ₀ / (4 * π * Λ₀ + 1)) * x ^ r by ring]
    nlinarith
  nlinarith

/-- The masses at `θ = x^{−ε}` and `Λ = Λ₀ log x + 1`: for `x ≥ 1`, `Λ₀ ≥ 0` and `π(2Λ₀ log x + 3) ≤ x^ε`, both
`massB θ Λ` and `massB θ θ` are at most `Cx^ε`, `C = 1 + c₂/(2π)`. -/
theorem massB_le {x ε Λ₀ : ℝ} (hx : 1 ≤ x) (hΛ₀ : 0 ≤ Λ₀) (hlog : π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ ε) :
    massB (x ^ (-ε)) (Λ₀ * Real.log x + 1) ≤ (1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π)) * x ^ ε ∧
      massB (x ^ (-ε)) (x ^ (-ε)) ≤ (1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π)) * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_pos
  have hinv : (x ^ (-ε))⁻¹ = x ^ ε := by rw [Real.rpow_neg hx0.le, inv_inv]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxε : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hθ1 : x ^ (-ε) ≤ 1 := by
    have h3 : 3 * π ≤ x ^ ε := by nlinarith [mul_nonneg hΛ₀ hl]
    rw [Real.rpow_neg hx0.le]
    exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have htail : (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * x ^ (-ε)) =
      (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) * x ^ ε := by
    rw [← hinv]; field_simp
  constructor
  · rw [massB, htail]
    have : π * (2 * (Λ₀ * Real.log x + 1) + x ^ (-ε)) ≤ π * (2 * Λ₀ * Real.log x + 3) := by
      apply mul_le_mul_of_nonneg_left _ hpi.le; linarith
    linarith
  · rw [massB, htail]
    have : π * (2 * x ^ (-ε) + x ^ (-ε)) ≤ π * (2 * Λ₀ * Real.log x + 3) := by
      apply mul_le_mul_of_nonneg_left _ hpi.le; nlinarith [mul_nonneg hΛ₀ hl]
    linarith

/-- The tail at `θ = x^{−ε}` and `T₀ = x^{1/200000}`: for `x ≥ 1`, `k ≥ 2` and `εk − ε − (k − 2)/200000 ≤ −3`,
`tailB θ T₀ k ≤ 2π(2c_k/(2π)^k)x^{−3}`. -/
theorem tailB_le {x ε : ℝ} {k : ℕ} (hx : 1 ≤ x) (hk : 2 ≤ k)
    (hexp : ε * k - ε - ((k : ℝ) - 2) / 200000 ≤ -3) :
    tailB (x ^ (-ε)) (x ^ (1 / 200000 : ℝ)) k ≤
      2 * π * ((2 * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * x ^ (-3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hinv : (x ^ (-ε))⁻¹ = x ^ ε := by rw [Real.rpow_neg hx0.le, inv_inv]
  have h1 : (x ^ (-ε))⁻¹ ^ k * x ^ (-ε) = x ^ (ε * k - ε) := by
    rw [hinv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, sub_eq_add_neg]
  have h2 : ((x ^ (1 / 200000 : ℝ)) ^ (k - 2))⁻¹ = x ^ (-(((k : ℝ) - 2) / 200000)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le, Nat.cast_sub hk]
    congr 1; push_cast; ring
  rw [tailB, h1, h2]
  have hck : 0 ≤ ∫ v, ‖iteratedDeriv k gc v‖ := integral_nonneg fun _ => norm_nonneg _
  have h3 : x ^ (ε * k - ε) * x ^ (-(((k : ℝ) - 2) / 200000)) ≤ x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hpi := Real.pi_pos
  calc 2 * π * ((2 * x ^ (ε * k - ε) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) *
        x ^ (-(((k : ℝ) - 2) / 200000)) =
      2 * π * ((2 * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) *
        (x ^ (ε * k - ε) * x ^ (-(((k : ℝ) - 2) / 200000))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The bracket: `a₁x^{−7/400000} + a₂x^{−1} + a₃(12x^{−ε} + x^{−e}) ≤ x^{−δ}` when `x ≥ 1`, `a₁, a₂, a₃ ≥ 0`,
`δ > 0`, `2δ ≤ ε ≤ 1/400000`, `2δ ≤ e` and `a₁ + a₂ + 13a₃ ≤ x^δ`. -/
theorem bracket_le {x a₁ a₂ a₃ ε e δ : ℝ} (hx : 1 ≤ x) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃)
    (hδ : 0 < δ) (hδε : 2 * δ ≤ ε) (hε : ε ≤ 1 / 400000) (hδe : 2 * δ ≤ e)
    (hsum : a₁ + a₂ + 13 * a₃ ≤ x ^ δ) :
    a₁ * x ^ (-(7 / 400000) : ℝ) + a₂ * x ^ (-1 : ℝ) + a₃ * (12 * x ^ (-ε) + x ^ (-e)) ≤ x ^ (-δ) := by
  have hx0 : 0 < x := by linarith
  have hle : ∀ s : ℝ, 2 * δ ≤ s → x ^ (-s) ≤ x ^ (-(2 * δ)) := fun s hs =>
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e1 := hle (7 / 400000) (by linarith)
  have e2 := hle 1 (by linarith)
  have e3 := hle ε hδε
  have e4 := hle e hδe
  have hsplit : x ^ (-(2 * δ)) = x ^ (-δ) * x ^ (-δ) := by rw [← Real.rpow_add hx0]; ring_nf
  have hdd : x ^ δ * x ^ (-δ) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hpos : 0 ≤ x ^ (-δ) := by positivity
  calc a₁ * x ^ (-(7 / 400000) : ℝ) + a₂ * x ^ (-1 : ℝ) + a₃ * (12 * x ^ (-ε) + x ^ (-e))
      ≤ (a₁ + a₂ + 13 * a₃) * x ^ (-(2 * δ)) := by nlinarith
    _ ≤ x ^ δ * x ^ (-(2 * δ)) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = x ^ (-δ) := by rw [hsplit, ← mul_assoc, hdd, one_mul]

end Helpers

section Asym

open SieveSmooth Classical Filter Asymptotics
open scoped ContDiff

end Asym

end SieveFamily
