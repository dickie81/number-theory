/-
# Reflection across vertical lines: RH as a family of inequalities for `|ξ|`, and Lagarias's positivity

Plain statement. Hadamard's product of Riemann's `ξ` over its zeros (`WeilForm.hadamardW_Xi`) compares `|ξ|` at a point
and at its mirror image across a vertical line one zero at a time: a zero on the mirror's side of the line is nearer
the mirror point, so its factor is smaller there (`norm_Xi_lt`).
* **Reflection** (`reflect_lt`, `reflect_xi`): if every zero `ρ` of `ξ` has `|Re ρ − ½| < c − ½`, then
  `|ξ(2c − s̄)| < |ξ(s)|` for every `s` with `Re s > c`. In Riemann's `Ξ(t) = ξ(½ + it)`, with `κ = c − ½`: if every
  zero `τ` of `Ξ` has `|Im τ| < κ`, then `‖Ξ(t̄ − 2κi)‖ < ‖Ξ(t)‖` for `Im t < −κ`.
* **Across `Re s = 1`, with no hypothesis** (`reflect_one`, `reflect_xi_one`): every zero has `0 < Re ρ < 1`.
* **RH is the reflection inequality across every line `Re s = c > ½`** (`rh_iff_reflect`, `rh_iff_reflect_xi`), and
  the inequality across one line `Re s = ½ + κ` confines the zeros to `|Re ρ − ½| ≤ κ` (`abs_im_le_of_reflect`): a
  zero-free strip and the reflection inequality across its edge each give the other, up to the edge itself.
* **Monotonicity** (`rh_iff_monotone`; J. Sondow and C. Dumitrescu, Period. Math. Hungar. 60 (2010)): RH holds if and
  only if `|ξ(σ + iT)|` is strictly increasing in `σ ≥ ½` for every `T`.
* **Positivity** (`rh_iff_logDeriv_pos`; J. C. Lagarias, Acta Arith. 89 (1999)): RH holds if and only if
  `Re ξ′/ξ(s) > 0` wherever `Re s > ½` and `ξ(s) ≠ 0`. Under RH each zero `ρ` adds `Re 1/(s − ρ) > 0` to Hadamard's
  sum (`WeilForm.hasSum_logDeriv_Xi`); a zero `ρ₀` off the line would end a horizontal segment along which `|ξ|`
  increases, to `|ξ(ρ₀)| = 0`.
* **Conjugation** (`xi_conj`, `Xi_conj`): `ξ(s̄) = conj ξ(s)`, by the identity theorem from `ξ`'s reality on `(1, ∞)`.
The calibration: across `Re s = 1` the inequality holds with no hypothesis, and Weng's rank-2 zeta function of `ℚ`
lives there (`WengRankTwo`); RH is the same inequality across every line `Re s = c` with `½ < c < 1`. These are
equivalences: no bearing on RH.
-/
import Mathlib
import WeilAssemble
import PsiOmega

open Complex ComplexConjugate Filter Topology Set

noncomputable section

namespace XiReflection

open WeilForm WeilTest

/-! ## Conjugation -/

/-- `ξ` is real on `(1, ∞)`. -/
lemma conj_xi_ofReal {x : ℝ} (hx : 1 < x) : conj (xi x) = xi x := by
  have h0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith)
  have h1 : (x : ℂ) ≠ 1 := fun h => by
    have := congrArg re h
    simp at this
    linarith
  have hG0 : Gammaℝ (x : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : completedRiemannZeta x = riemannZeta x * Gammaℝ x := by
    rw [riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hG0]
  have hζ : conj (riemannZeta x) = riemannZeta x := by rw [← riemannZeta_conj, conj_ofReal]
  have hπ : conj ((Real.pi : ℂ) ^ (-(x : ℂ) / 2)) = (Real.pi : ℂ) ^ (-(x : ℂ) / 2) := by
    rw [show -(x : ℂ) / 2 = ((-x / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow Real.pi_pos.le, conj_ofReal]
  have hΓ : conj (Gamma ((x : ℂ) / 2)) = Gamma ((x : ℂ) / 2) := by
    rw [← Gamma_conj, map_div₀, conj_ofReal, map_ofNat]
  have hG : conj (Gammaℝ x) = Gammaℝ x := by rw [Gammaℝ_def, map_mul, hπ, hΓ]
  rw [xi_eq h0 h1, hΛ]
  simp only [map_div₀, map_mul, map_sub, map_one, map_ofNat, conj_ofReal, hζ, hG]

/-- **`ξ(s̄) = conj ξ(s)`**: `conj ∘ ξ ∘ conj` is entire and equals `ξ` on `(1, ∞)`. -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  have hg : Differentiable ℂ (fun z => conj (xi (conj z))) := fun z => by
    have h := (differentiable_xi (conj z)).conj_conj
    rw [conj_conj] at h
    exact h
  have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (continuous_ofReal.tendsto (2 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {(2 : ℝ)}ᶜ))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      exact_mod_cast hx
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2 : ℝ), 1 < x :=
    (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), conj (xi (conj z)) = xi z :=
    hmap.frequently (hev.frequently.mono fun x hx => by rw [conj_ofReal, conj_xi_ofReal hx])
  have heq := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hg.analyticAt z)
    (fun z _ => differentiable_xi.analyticAt z) hfreq
  have h := congrFun heq (conj s)
  simp only [conj_conj] at h
  exact h.symm

/-- **`Ξ(t̄) = conj Ξ(t)`**, from `ξ(s̄) = conj ξ(s)` and `ξ(1 − s) = ξ(s)`. -/
theorem Xi_conj (t : ℂ) : Xi (conj t) = conj (Xi t) := by
  unfold Xi
  rw [← xi_conj, ← xi_one_sub (conj (1 / 2 + I * t))]
  congr 1
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, conj_I]
  ring

/-! ## The zeros -/

/-- Under RH every zero of `Ξ` is real. -/
theorem im_eq_zero_of_rh (hRH : RiemannHypothesis) {t : ℂ} (ht : Xi t = 0) : t.im = 0 := by
  have hb := abs_lt.1 (Xi_zero_im ht)
  have hre : (1 / 2 + I * t).re = 1 / 2 - t.im := by simp; ring
  have h0 : 1 / 2 + I * t ≠ 0 := fun h => by
    rw [h] at hre
    simp at hre
    linarith [hb.2]
  have h1 : 1 / 2 + I * t ≠ 1 := fun h => by
    rw [h] at hre
    simp at hre
    linarith [hb.1]
  have hxi : xi (1 / 2 + I * t) = 0 := ht
  rw [xi_eq h0 h1, div_eq_zero_iff] at hxi
  have hΛ : completedRiemannZeta (1 / 2 + I * t) = 0 := by
    rcases hxi with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (mul_ne_zero h0 (sub_ne_zero.2 h1))
      · exact h
    · exact absurd h two_ne_zero
  have hζ : riemannZeta (1 / 2 + I * t) = 0 := by rw [riemannZeta_def_of_ne_zero h0, hΛ, zero_div]
  have htriv : ¬∃ n : ℕ, 1 / 2 + I * t = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have h2 := congrArg re hn
    rw [hre] at h2
    simp at h2
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith [hb.2]
  have h3 := hRH _ hζ htriv h1
  rw [hre] at h3
  linarith

/-- If every zero of `Ξ` is real, RH holds. -/
theorem rh_of_real (h : ∀ t : ℂ, Xi t = 0 → t.im = 0) : RiemannHypothesis := by
  intro s hz htriv _
  apply re_eq_half_of_Xi_real
  apply h
  rw [Xi_at_ordinate]
  exact xi_eq_zero_of_nontrivial ⟨hz, htriv⟩

/-- Without RH, `Ξ` has a zero below the real axis (`Ξ` is even). -/
theorem exists_zero_of_not_rh (h : ¬RiemannHypothesis) : ∃ t : ℂ, Xi t = 0 ∧ t.im < 0 := by
  by_contra hc
  push Not at hc
  exact h (rh_of_real fun t ht => by
    have h1 := hc t ht
    have h2 := hc (-t) (by rw [Xi_even]; exact ht)
    rw [neg_im] at h2
    linarith)

/-- A zero `t` of `Ξ` is `±τ_i` for an index `i` of Hadamard's zero family. -/
theorem exists_index {t : ℂ} (ht : Xi t = 0) : ∃ i : ZeroIdx (sqF Xi), tau i = t ∨ tau i = -t := by
  have hF := sqF_differentiable differentiable_Xi Xi_even
  have hF0 : sqF Xi 0 ≠ 0 := by rw [sqF_zero]; exact Xi_zero_ne_zero
  have hpm : (t ^ 2) ^ ((2 : ℂ)⁻¹) = t ∨ (t ^ 2) ^ ((2 : ℂ)⁻¹) = -t := by
    have h2 := sqrt_sq' (t ^ 2)
    have hm : ((t ^ 2) ^ ((2 : ℂ)⁻¹) - t) * ((t ^ 2) ^ ((2 : ℂ)⁻¹) + t) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hm with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  have hz : sqF Xi (t ^ 2) = 0 := by
    show Xi ((t ^ 2) ^ ((2 : ℂ)⁻¹)) = 0
    rcases hpm with h | h
    · rw [h]; exact ht
    · rw [h, Xi_even]; exact ht
  exact ⟨⟨t ^ 2, ⟨0, Nat.pos_of_ne_zero ((ordN_ne_zero_iff hF hF0 _).2 hz)⟩⟩, hpm⟩

/-- Hadamard's zero family of `Ξ` is nonempty (`ζ` has a nontrivial zero). -/
theorem nonempty_zeroIdx : Nonempty (ZeroIdx (sqF Xi)) := by
  obtain ⟨ρ, hρ, hre⟩ := PsiOmega.exists_zero_re_ge_half
  have hs : IsNontrivialZero ρ := ⟨hρ, by
    rintro ⟨n, rfl⟩
    simp at hre
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith⟩
  obtain ⟨i, -⟩ := exists_index (t := (ρ - 1 / 2) / I) (by
    rw [Xi_at_ordinate]
    exact xi_eq_zero_of_nontrivial hs)
  exact ⟨i⟩

/-! ## Hadamard's product, factor by factor -/

/-- Termwise comparison of norms passes to products. -/
lemma norm_le_of_hasProd {ι : Type*} {a b : ι → ℂ} {A B : ℂ} (ha : HasProd a A) (hb : HasProd b B)
    (h : ∀ i, ‖a i‖ ≤ ‖b i‖) : ‖A‖ ≤ ‖B‖ :=
  le_of_tendsto_of_tendsto' ((continuous_norm.tendsto A).comp ha) ((continuous_norm.tendsto B).comp hb)
    fun s => by
      simp only [Function.comp_apply, norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => h i

/-- The factor of `Ξ(z)/Ξ(0)` at the zero pair `±τ_i`: `‖1 − z²/τ_i²‖ = ‖τ_i − z‖‖τ_i + z‖/‖τ_i‖²`. -/
lemma norm_factor (i : ZeroIdx (sqF Xi)) (z : ℂ) :
    ‖1 - z ^ 2 * i.1⁻¹‖ = ‖tau i - z‖ * ‖tau i + z‖ / ‖tau i‖ ^ 2 := by
  have hu := ZeroIdx_ne_zero i
  rw [← tau_sq i] at hu ⊢
  have hτ : tau i ≠ 0 := fun h => hu (by rw [h]; ring)
  rw [show 1 - z ^ 2 * (tau i ^ 2)⁻¹ = (tau i - z) * (tau i + z) / tau i ^ 2 by field_simp; ring,
    norm_div, norm_mul, norm_pow]

/-- **Hadamard's product compares `‖Ξ‖` at two points**: if `z₂` is nearer than `z₁` to every zero `τ` of `Ξ` and
to `−τ`, then `‖Ξ(z₂)‖ < ‖Ξ(z₁)‖`. -/
theorem norm_Xi_lt {z₁ z₂ : ℂ} (h1 : Xi z₁ ≠ 0)
    (h : ∀ i : ZeroIdx (sqF Xi), ‖tau i - z₂‖ < ‖tau i - z₁‖ ∧ ‖tau i + z₂‖ < ‖tau i + z₁‖) :
    ‖Xi z₂‖ < ‖Xi z₁‖ := by
  classical
  have H := hadamardW_Xi xiGrowth Xi_zero_ne_zero
  set f : ℂ → ZeroIdx (sqF Xi) → ℂ := fun z i => 1 - z ^ 2 * i.1⁻¹ with hf
  have hlt : ∀ i, ‖f z₂ i‖ < ‖f z₁ i‖ := by
    intro i
    simp only [hf, norm_factor]
    have hτ : tau i ≠ 0 := by
      intro h0
      apply ZeroIdx_ne_zero i
      rw [← tau_sq i, h0]
      ring
    exact div_lt_div_of_pos_right (mul_lt_mul'' (h i).1 (h i).2 (norm_nonneg _) (norm_nonneg _))
      (by positivity)
  obtain ⟨j⟩ := nonempty_zeroIdx
  have hmul : ∀ z, Multipliable (Function.update (f z) j 1) := by
    intro z
    have hs : Summable fun i =>
        ‖Function.update (fun i : ZeroIdx (sqF Xi) => -(z ^ 2 * i.1⁻¹)) j 0 i‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (summable_scaled H.summ z)
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self, norm_zero]
        positivity
      · rw [Function.update_of_ne hij]
    refine (multipliable_one_add_of_summable hs).congr fun i => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Function.update_of_ne hij, hf, sub_eq_add_neg]
  obtain ⟨P₁, hP₁⟩ := hmul z₁
  obtain ⟨P₂, hP₂⟩ := hmul z₂
  have hprod : ∀ z, HasProd (f z) (Xi z / Xi 0) := fun z => H.prod z
  have e₁ := (hprod z₁).update' j 1 hP₁
  have e₂ := (hprod z₂).update' j 1 hP₂
  rw [mul_one] at e₁ e₂
  have hle : ‖P₂‖ ≤ ‖P₁‖ := norm_le_of_hasProd hP₂ hP₁ fun i => by
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Function.update_of_ne hij, Function.update_of_ne hij]
      exact (hlt i).le
  have hP₁0 : P₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, div_eq_zero_iff] at e₁
    exact e₁.elim h1 Xi_zero_ne_zero
  have key : ‖Xi z₂ / Xi 0‖ < ‖Xi z₁ / Xi 0‖ := by
    rw [e₁, e₂, norm_mul, norm_mul]
    calc ‖P₂‖ * ‖f z₂ j‖ ≤ ‖P₁‖ * ‖f z₂ j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ < ‖P₁‖ * ‖f z₁ j‖ := mul_lt_mul_of_pos_left (hlt j) (norm_pos_iff.2 hP₁0)
  rw [norm_div, norm_div] at key
  exact (div_lt_div_iff_of_pos_right (norm_pos_iff.2 Xi_zero_ne_zero)).1 key

/-! ## Reflection -/

/-- Across the line `Im = −κ`, a point above it is nearer the mirror image `t̄ − 2κi` of a point `t` below it. -/
lemma norm_sub_mirror_lt {κ : ℝ} {p t : ℂ} (hp : -κ < p.im) (ht : t.im < -κ) :
    ‖p - (conj t - 2 * κ * I)‖ < ‖p - t‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp only [sub_re, sub_im, conj_re, conj_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, re_ofNat,
    im_ofNat]
  nlinarith [mul_pos (by linarith : (0 : ℝ) < p.im + κ) (by linarith : (0 : ℝ) < -(t.im + κ))]

/-- **Reflection across `Re s = ½ + κ`**: if every zero `τ` of `Ξ` has `|Im τ| < κ`, then `‖Ξ(t̄ − 2κi)‖ < ‖Ξ(t)‖`
for `Im t < −κ`. -/
theorem reflect_lt {κ : ℝ} (hz : ∀ i : ZeroIdx (sqF Xi), |(tau i).im| < κ) {t : ℂ} (ht : t.im < -κ) :
    ‖Xi (conj t - 2 * κ * I)‖ < ‖Xi t‖ := by
  have hXi : Xi t ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := exists_index h0
    have hb := abs_lt.1 (hz i)
    rcases hi with hi | hi
    · rw [hi] at hb
      linarith [hb.1]
    · rw [hi, neg_im] at hb
      linarith [hb.2]
  refine norm_Xi_lt hXi fun i => ⟨norm_sub_mirror_lt (by linarith [(abs_lt.1 (hz i)).1]) ht, ?_⟩
  have e : ∀ z : ℂ, ‖tau i + z‖ = ‖-tau i - z‖ := fun z => by
    rw [← norm_neg]
    congr 1
    ring
  rw [e, e]
  exact norm_sub_mirror_lt (by rw [neg_im]; linarith [(abs_lt.1 (hz i)).2]) ht

/-- **Across `Re s = 1`, with no hypothesis**: `‖Ξ(t̄ − i)‖ < ‖Ξ(t)‖` for `Im t < −½`. -/
theorem reflect_one {t : ℂ} (ht : t.im < -(1 / 2)) : ‖Xi (conj t - I)‖ < ‖Xi t‖ := by
  have h := reflect_lt (κ := 1 / 2) (fun i => tau_im i) ht
  rwa [show (2 : ℂ) * ((1 / 2 : ℝ) : ℂ) * I = I by push_cast; ring] at h

/-- The mirror point: at `t = (s − ½)/i`, `Ξ(t̄ − 2κi) = ξ(1 + 2κ − s̄)`. -/
lemma Xi_mirror (s : ℂ) (κ : ℝ) : Xi (conj ((s - 1 / 2) / I) - 2 * κ * I) = xi (1 + 2 * κ - conj s) := by
  unfold Xi
  congr 1
  apply Complex.ext <;> simp [div_I]
  ring

/-- **Reflection across `Re s = c`**: if every zero `ρ` of `ξ` has `|Re ρ − ½| < c − ½`, then
`‖ξ(2c − s̄)‖ < ‖ξ(s)‖` for `Re s > c`. -/
theorem reflect_xi {c : ℝ} (hz : ∀ i : ZeroIdx (sqF Xi), |(tau i).im| < c - 1 / 2) {s : ℂ} (hs : c < s.re) :
    ‖xi (2 * c - conj s)‖ < ‖xi s‖ := by
  have h := reflect_lt hz (t := (s - 1 / 2) / I) (by rw [im_ordinate]; linarith)
  rw [Xi_mirror, Xi_at_ordinate] at h
  convert h using 4
  push_cast
  ring

/-- **Across `Re s = 1`, with no hypothesis**: `‖ξ(2 − s̄)‖ < ‖ξ(s)‖` for `Re s > 1`. -/
theorem reflect_xi_one {s : ℂ} (hs : 1 < s.re) : ‖xi (2 - conj s)‖ < ‖xi s‖ := by
  have h := reflect_xi (c := 1) (fun i => by linarith [tau_im i]) hs
  convert h using 4
  push_cast
  ring

/-- **The reflection inequality across `Re s = ½ + κ` confines the zeros to `|Re ρ − ½| ≤ κ`**: in `Ξ`, every zero
has `|Im t| ≤ κ`. -/
theorem abs_im_le_of_reflect {κ : ℝ} (h : ∀ t : ℂ, t.im < -κ → ‖Xi (conj t - 2 * κ * I)‖ < ‖Xi t‖) {t : ℂ}
    (ht : Xi t = 0) : |t.im| ≤ κ := by
  have key : ∀ u : ℂ, Xi u = 0 → -κ ≤ u.im := fun u hu => by
    by_contra hlt
    push Not at hlt
    have h' := h u hlt
    rw [hu, norm_zero] at h'
    exact (norm_nonneg _).not_gt h'
  have h1 := key t ht
  have h2 := key (-t) (by rw [Xi_even]; exact ht)
  rw [neg_im] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **RH is the reflection inequality across every line `Re s = ½ + κ`, `κ > 0`**, in `Ξ`. -/
theorem rh_iff_reflect : RiemannHypothesis ↔
    ∀ κ : ℝ, 0 < κ → ∀ t : ℂ, t.im < -κ → ‖Xi (conj t - 2 * κ * I)‖ < ‖Xi t‖ := by
  constructor
  · intro hRH κ hκ t ht
    exact reflect_lt (fun i => by rw [im_eq_zero_of_rh hRH (Xi_tau i), abs_zero]; exact hκ) ht
  · intro h
    refine rh_of_real fun t ht => ?_
    by_contra hne
    have hpos : 0 < |t.im| := abs_pos.2 hne
    have h' := abs_im_le_of_reflect (h (|t.im| / 2) (by linarith)) ht
    linarith

/-- **RH is the reflection inequality across every line `Re s = c > ½`**: `‖ξ(2c − s̄)‖ < ‖ξ(s)‖` for `Re s > c`. -/
theorem rh_iff_reflect_xi : RiemannHypothesis ↔
    ∀ c : ℝ, 1 / 2 < c → ∀ s : ℂ, c < s.re → ‖xi (2 * c - conj s)‖ < ‖xi s‖ := by
  constructor
  · intro hRH c hc s hs
    exact reflect_xi (fun i => by rw [im_eq_zero_of_rh hRH (Xi_tau i), abs_zero]; linarith) hs
  · intro h
    refine rh_iff_reflect.2 fun κ hκ t ht => ?_
    have hs : 1 / 2 + κ < (1 / 2 + I * t).re := by simp; linarith
    have h' := h (1 / 2 + κ) (by linarith) (1 / 2 + I * t) hs
    have e : xi (2 * ((1 / 2 + κ : ℝ) : ℂ) - conj (1 / 2 + I * t)) = Xi (conj t - 2 * κ * I) := by
      unfold Xi
      congr 1
      apply Complex.ext <;> simp
      ring
    rw [e] at h'
    exact h'

/-! ## Monotonicity -/

/-- A point of the real axis is nearer `x + iy'` than `x + iy` when `y < y' ≤ 0`. -/
lemma norm_sub_lt_of_im {p : ℂ} (hp : p.im = 0) {x y y' : ℝ} (hy : y < y') (hy' : y' ≤ 0) :
    ‖p - (x + y' * I)‖ < ‖p - (x + y * I)‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, hp]
  nlinarith [mul_pos (sub_pos.2 hy) (by linarith : (0 : ℝ) < -(y + y'))]

/-- Under RH, `‖Ξ(x + iy)‖` strictly decreases as `y` increases to `0`. -/
lemma norm_Xi_lt_of_rh (hRH : RiemannHypothesis) {x y y' : ℝ} (hy : y < y') (hy' : y' ≤ 0) :
    ‖Xi (x + y' * I)‖ < ‖Xi (x + y * I)‖ := by
  have hne : Xi (x + y * I) ≠ 0 := fun h0 => by
    have h' := im_eq_zero_of_rh hRH h0
    simp at h'
    linarith
  refine norm_Xi_lt hne fun i => ⟨norm_sub_lt_of_im (im_eq_zero_of_rh hRH (Xi_tau i)) hy hy', ?_⟩
  have e : ∀ z : ℂ, ‖tau i + z‖ = ‖-tau i - z‖ := fun z => by
    rw [← norm_neg]
    congr 1
    ring
  rw [e, e]
  exact norm_sub_lt_of_im (by rw [neg_im, im_eq_zero_of_rh hRH (Xi_tau i), neg_zero]) hy hy'

/-- **Monotonicity** (Sondow–Dumitrescu): RH holds if and only if `|ξ(σ + iT)|` is strictly increasing in `σ ≥ ½`
for every `T`. -/
theorem rh_iff_monotone : RiemannHypothesis ↔
    ∀ T σ σ' : ℝ, 1 / 2 ≤ σ → σ < σ' → ‖xi (σ + T * I)‖ < ‖xi (σ' + T * I)‖ := by
  have e : ∀ T a : ℝ, xi (a + T * I) = Xi (T + ((1 / 2 - a : ℝ) : ℂ) * I) := fun T a => by
    unfold Xi
    congr 1
    apply Complex.ext <;> simp
  constructor
  · intro hRH T σ σ' hσ hσσ'
    rw [e, e]
    exact norm_Xi_lt_of_rh hRH (by linarith) (by linarith)
  · intro h
    by_contra hRH
    obtain ⟨t, ht, him⟩ := exists_zero_of_not_rh hRH
    have h' := h t.re (1 / 2) (1 / 2 - t.im) le_rfl (by linarith)
    rw [e, e] at h'
    have et : (t.re : ℂ) + ((1 / 2 - (1 / 2 - t.im) : ℝ) : ℂ) * I = t := by
      apply Complex.ext <;> simp
    rw [et, ht, norm_zero] at h'
    exact (norm_nonneg _).not_gt h'

/-! ## Positivity -/

/-- `ξ′/ξ(s) = Ξ′/Ξ((s − ½)/i)·(−i)`. -/
lemma logDeriv_xi (s : ℂ) : logDeriv xi s = logDeriv Xi ((s - 1 / 2) / I) * -I := by
  have hfun : xi = Xi ∘ fun z => (z - 1 / 2) / I := by
    funext z
    simp only [Function.comp_apply, Xi_at_ordinate]
  have hg : HasDerivAt (fun z : ℂ => (z - 1 / 2) / I) (1 / I) s :=
    ((hasDerivAt_id s).sub_const (1 / 2)).div_const I
  rw [hfun, logDeriv_comp (differentiable_Xi _) hg.differentiableAt, hg.deriv, one_div I, inv_I]

/-- Under RH, `Im Ξ′/Ξ(t) > 0` for `Im t < 0`: each zero pair `±τ` adds `Im(1/(t − τ) + 1/(t + τ)) > 0`. -/
lemma im_logDeriv_pos (hRH : RiemannHypothesis) {t : ℂ} (ht : t.im < 0) : 0 < (logDeriv Xi t).im := by
  have hne : Xi t ≠ 0 := fun h0 => by
    have h' := im_eq_zero_of_rh hRH h0
    linarith
  have hs := hasSum_im (hasSum_logDeriv_Xi hne)
  have hpos : ∀ i : ZeroIdx (sqF Xi), 0 < (2 * t / (t ^ 2 - i.1)).im := by
    intro i
    have hτ : (tau i).im = 0 := im_eq_zero_of_rh hRH (Xi_tau i)
    have h1 : t - tau i ≠ 0 := fun h0 => by
      have h' := congrArg im h0
      simp [hτ] at h'
      linarith
    have h2 : t + tau i ≠ 0 := fun h0 => by
      have h' := congrArg im h0
      simp [hτ] at h'
      linarith
    have h3 : t ^ 2 - tau i ^ 2 ≠ 0 := by
      rw [show t ^ 2 - tau i ^ 2 = (t - tau i) * (t + tau i) by ring]
      exact mul_ne_zero h1 h2
    rw [← tau_sq i, show 2 * t / (t ^ 2 - tau i ^ 2) = (t - tau i)⁻¹ + (t + tau i)⁻¹ by
      field_simp
      ring]
    rw [add_im, inv_im, inv_im]
    simp only [sub_im, add_im, hτ, sub_zero, add_zero]
    have hneg : 0 < -t.im := by linarith
    exact add_pos (div_pos hneg (normSq_pos.2 h1)) (div_pos hneg (normSq_pos.2 h2))
  obtain ⟨j⟩ := nonempty_zeroIdx
  exact hasSum_lt (fun i => (hpos i).le) (hpos j) hasSum_zero hs

/-- `Re(a b̄) = |b|²·Re(a/b)`. -/
lemma re_mul_conj (a b : ℂ) (hb : b ≠ 0) : (a * conj b).re = normSq b * (a / b).re := by
  have hn : normSq b ≠ 0 := normSq_eq_zero.not.2 hb
  rw [div_eq_mul_inv, inv_def, ← mul_assoc, re_mul_ofReal]
  field_simp

/-- The derivative of `σ ↦ ‖ξ(σ + iT)‖²` is `2 Re(ξ′ ξ̄)`. -/
lemma hasDerivAt_normSq (T σ : ℝ) :
    HasDerivAt (fun x : ℝ => ‖xi (x + T * I)‖ ^ 2)
      (2 * (deriv xi (σ + T * I) * conj (xi (σ + T * I))).re) σ := by
  have h1 : HasDerivAt (fun z : ℂ => xi (z + T * I)) (deriv xi (σ + T * I)) σ :=
    HasDerivAt.comp_add_const (σ : ℂ) (T * I) (differentiable_xi _).hasDerivAt
  have h2 := h1.comp_ofReal.norm_sq
  rwa [Complex.inner] at h2

/-- **Positivity implies RH**: a zero `ρ₀ = σ₀ + iT` with `σ₀ > ½` is isolated, and on a horizontal segment ending at
it `‖ξ‖²` has derivative `2‖ξ‖² Re ξ′/ξ > 0`, so it increases to `‖ξ(ρ₀)‖² = 0`. -/
theorem rh_of_logDeriv_pos (h : ∀ s : ℂ, 1 / 2 < s.re → xi s ≠ 0 → 0 < (logDeriv xi s).re) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨t, ht, him⟩ := exists_zero_of_not_rh hRH
  set σ₀ : ℝ := 1 / 2 - t.im with hσ₀
  set T : ℝ := t.re with hT
  have hpt : (σ₀ : ℂ) + T * I = 1 / 2 + I * t := by
    apply Complex.ext <;> simp [hσ₀, hT]
    ring
  have hz : xi (σ₀ + T * I) = 0 := by rw [hpt]; exact ht
  have hiso : ∀ᶠ z in 𝓝[≠] ((σ₀ : ℂ) + T * I), xi z ≠ 0 := by
    rcases (differentiable_xi.analyticAt ((σ₀ : ℂ) + T * I)).eventually_eq_zero_or_eventually_ne_zero
      with h0 | h0
    · exfalso
      have hA : AnalyticOnNhd ℂ xi univ := fun z _ => differentiable_xi.analyticAt z
      exact xi_two_ne_zero (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ _) h0 (mem_univ 2))
    · exact h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
  set a : ℝ := max (σ₀ - ε / 2) ((1 / 2 + σ₀) / 2) with ha
  have ha1 : a < σ₀ := max_lt (by linarith) (by linarith)
  have ha2 : 1 / 2 < a := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hcont : Continuous fun x : ℝ => ‖xi (x + T * I)‖ ^ 2 :=
    ((differentiable_xi.continuous.comp (continuous_ofReal.add continuous_const)).norm).pow 2
  have hmono : StrictMonoOn (fun x : ℝ => ‖xi (x + T * I)‖ ^ 2) (Icc a σ₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a σ₀) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    have hne : xi (x + T * I) ≠ 0 := by
      apply hball
      · rw [dist_eq_norm, show (x : ℂ) + T * I - (σ₀ + T * I) = ((x - σ₀ : ℝ) : ℂ) by push_cast; ring,
          norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith [hx.2])]
        linarith [hx.1, le_max_left (σ₀ - ε / 2) ((1 / 2 + σ₀) / 2)]
      · intro h0
        have h' := congrArg re (mem_singleton_iff.1 h0)
        simp at h'
        linarith [hx.2]
    rw [(hasDerivAt_normSq T x).deriv, re_mul_conj _ _ hne]
    have hl := h (x + T * I) (by simp; linarith [hx.1]) hne
    rw [logDeriv_apply] at hl
    have hn : 0 < normSq (xi (x + T * I)) := normSq_pos.2 hne
    have := mul_pos hn hl
    linarith
  have hlt := hmono ⟨le_rfl, ha1.le⟩ ⟨ha1.le, le_rfl⟩ ha1
  simp only [hz, norm_zero] at hlt
  nlinarith [norm_nonneg (xi (a + T * I))]

/-- **Positivity** (Lagarias): RH holds if and only if `Re ξ′/ξ(s) > 0` wherever `Re s > ½` and `ξ(s) ≠ 0`. -/
theorem rh_iff_logDeriv_pos :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → xi s ≠ 0 → 0 < (logDeriv xi s).re := by
  refine ⟨fun hRH s hs _ => ?_, rh_of_logDeriv_pos⟩
  rw [logDeriv_xi]
  have him : ((s - 1 / 2) / I).im < 0 := by rw [im_ordinate]; linarith
  have h := im_logDeriv_pos hRH him
  simpa using h

end XiReflection

#print axioms XiReflection.xi_conj
#print axioms XiReflection.Xi_conj
#print axioms XiReflection.reflect_lt
#print axioms XiReflection.reflect_one
#print axioms XiReflection.reflect_xi
#print axioms XiReflection.reflect_xi_one
#print axioms XiReflection.abs_im_le_of_reflect
#print axioms XiReflection.rh_iff_reflect
#print axioms XiReflection.rh_iff_reflect_xi
#print axioms XiReflection.rh_iff_monotone
#print axioms XiReflection.rh_iff_logDeriv_pos
