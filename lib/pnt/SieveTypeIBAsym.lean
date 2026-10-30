/-
# The leaves by the bilinear estimate: the asymptotic form

Plain statements. `G θ Λ` is `SieveSmooth`'s cut-off and `massB θ Λ = π(2Λ + θ) + c₂/(2πθ)` its Fourier mass bound
(`SieveFamily.massB`); `bdU` is `SieveTypeIBSum`'s uniform bound of a block pair.

* `norm_fourier_comp_add`: a translate has the same `|𝓕|`: `|𝓕(f(· + c))(w)| = |𝓕f(w)|`.
* `cutoffs`: for `0 < θ ≤ 2Λ`, the cut-off `G θ Λ` and the narrow cut-off `u ↦ G θ θ (u + θ)` are continuous and
  integrable with integrable Fourier transforms, of masses at most `massB θ Λ` and `massB θ θ`.
* `pivot_inv_le`, `pivot_box`, `pivot_two_le`: **the pivots.** For `0 < θ ≤ 1/9` and integers at least `Y₀ > 0`:
  `Σ_p G θ θ (c ± log p + θ)/p ≤ 12θ + 1/Y₀`; so for families `Y₁`, `Y₂` in boxes with `Σ_{p∈t_i} 1/p ≤ B` on every
  coordinate and a form `c + Σ e₁ log y₁ + Σ e₂ log y₂` with a coefficient `±1`,
  `Σ_{y₁,y₂} G θ θ (form + θ)/(∏y₁∏y₂) ≤ (12θ + 1/Y₀)B^{K₁+K₂−1}`.
* `sum_box_inv`, `prod_le_pow`, `box_weight_le`: `Σ_{x∈box} 1/∏x = ∏_i Σ_{p∈t_i} 1/p`, so
  `Σ_{y₁,y₂} c/(∏y₁∏y₂) ≤ B^{K₁+K₂}` for `c ≤ 1`.
* `nb_regroup`: the near-boundary masses of a sieve, regrouped:
  `Σ_{(y₁,σ),y₂} C|λ_σ|M/(π₁f_σπ₂) = C(Σ_σ |λ_σ|/f_σ)Σ_{y₁,y₂} M/(π₁π₂)`.
* `half_le_log_one_add`, `blk_floor_le`: for `x ≥ 3`, `ρ = 1 + x^{−s}` and `1 ≤ X ≤ x^L`: `blk⌊X⌋ + 1 ≤ 3Lx^s log x`.
* `bdU_le_pow`: **the uniform bound as powers of `q`.** With `x = q`, `η = x^{−s}`, `ρ = 1 + η`, `N₁ = ⌊x^L⌋`,
  `N₂ = ⌊2x^L⌋`, `X₁ = x^{L−1−a}`, `X₂ = x^{L−b}`, `X₃ = x^{L−1−δ'}`, `r ≥ 4/b` and `F, d(q) ≤ C_dx^s`:
  `bdU ≤ √(816C_d)x^{L−1−(a−δ'−s)/2} + 16(16r)^r x^{L−2} + 4C_dx^{L−1/2+s}/φ(q)`.
* `ev_log_sq_le`: for `α < β`, eventually `C(log x)²x^α ≤ x^β`.
* `sIB`, `sIB_spec`: the exponent `s = min((a − δ')/(2(J₀ + 6)), b/2, e₀, 1/(4(J₀ + 6)))` of `η = θ = q^{−s}`.
* `masses_le`, `rpow_mul_le_div`, `bil_le`: the Fourier masses of `J ≤ J₀` cut-offs, each at most `M ≥ 1`, give
  `∏_j m_j + Σ_j m'_j ≤ (J₀ + 1)M^{J₀}`; and the bilinear part `4k₁k₂·FN·M_fM₂U` is at most
  `36L²(J₀ + 1)C_m^{J₀}(√(816C_d) + r' + 4C_d)(log x)²x^{L−3s/4}/φ(q)` when `k_i ≤ 3Lx^s log x`,
  `FN ≤ (J₀ + 1)(C_mx^s)^{J₀}`, `M_f, M₂ ≤ x^{c₁}`, `U` is at most `bdU_le_pow`'s bound and the exponents allow.
* `split_main`: the leaves' main errors, regrouped into the main term, the transition `(VΘ/x)Σ_y c/d` and
  `(4W/x + 2W·d(q)/φ(q))Σ_y c`, `V = Σ|λ|/f` and `W = Σ|λ|`.
* `leaves_ib`: **the leaves by the bilinear estimate, asymptotically.** Fix `L > 2`, margins `0 ≤ δ' < a ≤ L − 2` and
  `0 < b ≤ L`, `e₀ > 0`, `Λ₀ ≥ 0`, `B ≥ 1`, sizes `K₁`, `K₂`, `J₀`, and `0 ≤ c₁ < s/4` with `s = sIB a b δ' e₀ J₀`.
  For large `q`: let families `Y₁`, `Y₂` of tuples lie in boxes of integers at least `q^{e₀}` with `Σ 1/p ≤ B` on
  each coordinate, `J ≤ J₀` sharp comparisons `Pr_j` of forms at most `Λ₀ log q` each have a coefficient `±1`, and
  sieve weights `S₁` above and `S₂` below sandwich `R`, with fibres and `Σ|λ|/f` at most `q^{c₁}` and `Σ|λ|` at
  most `q^{1/4}`; and let every leaf have `∏y₁·f_max ≤ q^{L−1−a}`, `∏y₁·f_max(∏y₂)² ≤ q^{L−b}` and
  `∏y₁∏y₂ ≥ q^{L−1−δ'}`. Then `|Σ_y c Σ_m rng(d, m)R(m)dw(dm)| ≤ (N₂ − N₁)/q·|Γ|·Σ_y c/d + q^{L−s/4}/φ(q)`,
  `c = ∏_j 1[Pr_j]`, `d = ∏y₁∏y₂`, `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋`, `Γ` the sieve's gap.

The proof of `leaves_ib`: `SieveTypeIBSum.leaves_family` at `θ = η = q^{−s}`, `Λ = Λ₀ log q + 1`, `r = ⌈4/b⌉` and
`F = ⌊C_dq^s⌋` (`LinnikPower.card_divisors_le`), with each comparison replaced off the family by its cut-off, so that
`|I_j − G θ Λ| ≤ G θ θ (· + θ)` everywhere (`SieveFamily.abs_ind_sub_G_le`). The transition is bounded by
`Θ ≤ 11q^{L−s}` and `Σ_y c ≤ q^{L−1/2}B^{K₁+K₂}` (in the region, `(∏y₁∏y₂)² ≤ X₁X₂`), the bilinear part by `bil_le`,
and the near-boundary masses by `nb_regroup` and `pivot_two_le`. Their total is at most `C(log q)²q^{L−3s/4}/φ(q)`,
and `ev_log_sq_le` absorbs the constant.

The file imports `SieveTypeIBSum.lean` and `LinnikPower.lean`.
-/
import SieveTypeIBSum
import LinnikPower

open Finset MeasureTheory
open scoped FourierTransform

namespace SieveTypeIBAsym

open SieveTypeIB SieveSpline SieveTypeIBLeaf SieveTypeIBEv SieveTypeIBSum SieveSmooth

/-! ### The cut-offs -/

/-- A translate has the same `|𝓕|`. -/
theorem norm_fourier_comp_add (f : ℝ → ℂ) (c w : ℝ) : ‖𝓕 (fun u => f (u + c)) w‖ = ‖𝓕 f w‖ := by
  have h := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ ℝ) f c
  have e : 𝓕 (fun u => f (u + c)) w =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) (f ∘ fun v => v + c) w := rfl
  rw [e, h, Circle.norm_smul]
  rfl

/-- **The cut-offs.** For `0 < θ ≤ 2Λ`: `G θ Λ` and `u ↦ G θ θ (u + θ)`, as complex functions, are continuous and
integrable, with integrable Fourier transforms of masses at most `massB θ Λ` and `massB θ θ`. -/
theorem cutoffs {θ Λ : ℝ} (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) :
    Continuous (fun u => ((G θ Λ u : ℝ) : ℂ)) ∧ Integrable (fun u => ((G θ Λ u : ℝ) : ℂ)) ∧
      Integrable (𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ))) ∧
      ∫ t, ‖𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ)) t‖ ≤ SieveFamily.massB θ Λ ∧
    Continuous (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) ∧ Integrable (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) ∧
      Integrable (𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ))) ∧
      ∫ t, ‖𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) t‖ ≤ SieveFamily.massB θ θ := by
  have hΛ : 0 ≤ Λ := by linarith
  have eG : (fun u => ((G θ Λ u : ℝ) : ℂ)) = GC θ Λ := funext fun u => (GC_eq_G θ Λ u).symm
  have eM : (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) = fun u => GC θ θ (u + θ) :=
    funext fun u => (GC_eq_G θ θ (u + θ)).symm
  have hMi : Integrable (fun u => GC θ θ (u + θ)) := (integrable_GC hθ hθ.le).comp_add_right θ
  have hMc : Continuous (fun u => GC θ θ (u + θ)) :=
    (contDiff_GC (n := 0)).continuous.comp (continuous_id.add continuous_const)
  have hnorm : ∀ t, ‖𝓕 (fun u => GC θ θ (u + θ)) t‖ = ‖𝓕 (GC θ θ) t‖ := fun t =>
    norm_fourier_comp_add (GC θ θ) θ t
  have hMf : Integrable (𝓕 (fun u => GC θ θ (u + θ))) := by
    have hcont : Continuous (𝓕 (fun u => GC θ θ (u + θ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hMi
    refine Integrable.mono' (integrable_fourier_GC hθ hθ.le).norm hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => le_of_eq (hnorm t))
  rw [eG, eM]
  refine ⟨(contDiff_GC (n := 0)).continuous, integrable_GC hθ hΛ, integrable_fourier_GC hθ hΛ,
    SieveFamily.mass_GC_le hθ hθΛ, hMc, hMi, hMf, ?_⟩
  rw [show (fun t => ‖𝓕 (fun u => GC θ θ (u + θ)) t‖) = fun t => ‖𝓕 (GC θ θ) t‖ from funext hnorm]
  exact SieveFamily.mass_GC_le hθ (by linarith)

/-! ### The pivots -/

/-- **The pivot's sum, weighted by `1/p`.** For `0 < θ ≤ 1/9`, `Y₀ > 0`, `σ = ±1` and a set `t` of integers at least
`Y₀`: `Σ_{p∈t} G θ θ (c + σ log p + θ)/p ≤ 12θ + 1/Y₀`. -/
theorem pivot_inv_le {θ Y₀ c σ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 9) (hY₀ : 0 < Y₀) (hσ : σ = 1 ∨ σ = -1)
    (t : Finset ℕ) (ht : ∀ p ∈ t, Y₀ ≤ p) :
    ∑ p ∈ t, G θ θ (c + σ * Real.log p + θ) / p ≤ 12 * θ + 1 / Y₀ := by
  -- the terms vanish off `[Y, e^{3θ}Y]`
  obtain ⟨Y, hY, hYb⟩ : ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, 0 < y → -θ ≤ c + σ * Real.log y →
      c + σ * Real.log y ≤ 2 * θ → Y ≤ y ∧ y ≤ Real.exp (3 * θ) * Y := by
    rcases hσ with rfl | rfl
    · refine ⟨Real.exp (-θ - c), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    · refine ⟨Real.exp (c - 2 * θ), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  set Y' := max Y Y₀ with hY'
  have hY'0 : 0 < Y' := lt_of_lt_of_le hY₀ (le_max_right _ _)
  set ρ := Real.exp (3 * θ) with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_exp (by linarith)
  have hρ2 : ρ ≤ 2 := by
    have h := SieveFamily.exp_three_sub_one_le hθ.le (by linarith)
    linarith
  set s := t.filter (fun p : ℕ => -θ ≤ c + σ * Real.log p ∧ c + σ * Real.log p ≤ 2 * θ) with hs
  have hterm : ∀ p ∈ t, G θ θ (c + σ * Real.log p + θ) / p ≤ if p ∈ s then 1 / Y' else 0 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hY₀ (ht p hp)
    have hG1 := G_le_one (θ := θ) (Λ := θ) (c + σ * Real.log p + θ)
    have hG0 := G_nonneg hθ (by linarith : θ ≤ 2 * θ) (c + σ * Real.log p + θ)
    split_ifs with hps
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hps
      have hYp : Y' ≤ p := max_le (hYb p hp0 h1 h2).1 (ht p hp)
      calc G θ θ (c + σ * Real.log p + θ) / p ≤ 1 / p := div_le_div_of_nonneg_right hG1 hp0.le
        _ ≤ 1 / Y' := one_div_le_one_div_of_le hY'0 hYp
    · have hout : c + σ * Real.log p + θ ∉ Set.Icc 0 (2 * θ + θ) := by
        rintro ⟨h1, h2⟩
        exact hps (Finset.mem_filter.2 ⟨hp, by linarith, by linarith⟩)
      rw [G_eq_zero hθ hθ.le hout, zero_div]
  have hcard : (s.card : ℝ) ≤ (ρ - 1) * (ρ * Y') + 1 := by
    refine SieveFamily.card_short_le hY'0 hρ1 (by positivity) s fun y hy => ?_
    obtain ⟨hyt, h1, h2⟩ := Finset.mem_filter.1 hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hY₀ (ht y hyt)
    obtain ⟨hl, hr⟩ := hYb y hy0 h1 h2
    have hYY : ρ * Y ≤ ρ * Y' := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    exact ⟨max_le hl (ht y hyt), hr.trans hYY, hr.trans hYY⟩
  calc ∑ p ∈ t, G θ θ (c + σ * Real.log p + θ) / p ≤ ∑ p ∈ t, (if p ∈ s then 1 / Y' else 0) :=
        Finset.sum_le_sum hterm
    _ = s.card * (1 / Y') := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 2
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
    _ ≤ ((ρ - 1) * (ρ * Y') + 1) * (1 / Y') := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (ρ - 1) * ρ + 1 / Y' := by field_simp
    _ ≤ 12 * θ + 1 / Y₀ := by
        have h1 := SieveFamily.exp_three_sub_one_le hθ.le (by linarith)
        have h2 : 1 / Y' ≤ 1 / Y₀ := one_div_le_one_div_of_le hY₀ (le_max_right _ _)
        have h3 : (ρ - 1) * ρ ≤ 6 * θ * 2 := mul_le_mul h1 hρ2 (by positivity) (by positivity)
        linarith

/-- **The pivot over a box.** For `0 < θ ≤ 1/9`, a box `t` of integers at least `Y₀ > 0` and a form
`c + Σ_i e_i log x_i` with `e_{i₀} = ±1`: `Σ_{x∈box} G θ θ (form + θ)/∏x ≤ (12θ + 1/Y₀)∏_{i≠i₀} Σ_{p∈t_i} 1/p`. -/
theorem pivot_box {n : ℕ} (t : Fin (n + 1) → Finset ℕ) {Y₀ : ℝ} (hY₀ : 0 < Y₀) (ht : ∀ i, ∀ p ∈ t i, Y₀ ≤ p)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 9) (c : ℝ) (e : Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (hi₀ : e i₀ = 1 ∨ e i₀ = -1) :
    ∑ x ∈ Fintype.piFinset t, G θ θ (c + ∑ i, e i * Real.log (x i) + θ) / (∏ i, x i : ℕ) ≤
      (12 * θ + 1 / Y₀) * ∏ i : Fin n, ∑ p ∈ t (i₀.succAbove i), 1 / (p : ℝ) := by
  have h := SieveFamily.pivot_sum_le t i₀ (fun _ y => 1 / (y : ℝ)) (fun _ y => by positivity)
    (fun x => G θ θ (c + ∑ i, e i * Real.log (x i) + θ)) (C := 12 * θ + 1 / Y₀) (fun z => by
      have e1 : ∀ y : ℕ, c + ∑ i, e i * Real.log ((i₀.insertNth y z : Fin (n + 1) → ℕ) i) + θ =
          (c + ∑ i : Fin n, e (i₀.succAbove i) * Real.log (z i)) + e i₀ * Real.log y + θ := by
        intro y
        rw [Fin.sum_univ_succAbove _ i₀]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        ring
      simp only [e1]
      refine le_trans (le_of_eq ?_) (pivot_inv_le (c := c + ∑ i : Fin n, e (i₀.succAbove i) * Real.log (z i))
        hθ hθ1 hY₀ hi₀ (t i₀) (ht i₀))
      exact Finset.sum_congr rfl fun y _ => by rw [one_div_mul_eq_div])
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one, one_div_mul_eq_div]

/-- `Σ_{x∈box} 1/∏x = ∏_i Σ_{p∈t_i} 1/p`. -/
theorem sum_box_inv {K : ℕ} (t : Fin K → Finset ℕ) :
    ∑ x ∈ Fintype.piFinset t, 1 / ((∏ i, x i : ℕ) : ℝ) = ∏ i, ∑ p ∈ t i, 1 / (p : ℝ) := by
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- A product of `n` factors in `[0, B]` is at most `B^n`. -/
theorem prod_le_pow {n : ℕ} (g : Fin n → ℝ) {B : ℝ} (h0 : ∀ i, 0 ≤ g i) (hB : ∀ i, g i ≤ B) :
    ∏ i, g i ≤ B ^ n := by
  calc ∏ i, g i ≤ ∏ _i : Fin n, B := Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => hB i
    _ = B ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The pivot over two groups.** For `0 < θ ≤ 1/9`, families `Y₁`, `Y₂` in boxes of integers at least `Y₀ > 0`,
with `Σ_{p∈t_i} 1/p ≤ B` on every coordinate, and a form `c + Σ e₁ log y₁ + Σ e₂ log y₂` with a coefficient `±1`:
`Σ_{y₁,y₂} G θ θ (form + θ)/(∏y₁∏y₂) ≤ (12θ + 1/Y₀)B^{K₁+K₂−1}`. -/
theorem pivot_two_le {K₁ K₂ : ℕ} (t₁ : Fin K₁ → Finset ℕ) (t₂ : Fin K₂ → Finset ℕ)
    (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)) (hY₁ : Y₁ ⊆ Fintype.piFinset t₁)
    (hY₂ : Y₂ ⊆ Fintype.piFinset t₂) {Y₀ : ℝ} (hY₀ : 0 < Y₀) (ht₁ : ∀ i, ∀ p ∈ t₁ i, Y₀ ≤ p)
    (ht₂ : ∀ i, ∀ p ∈ t₂ i, Y₀ ≤ p) {B : ℝ} (hB : 0 ≤ B) (hB₁ : ∀ i, ∑ p ∈ t₁ i, 1 / (p : ℝ) ≤ B)
    (hB₂ : ∀ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) ≤ B) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 9) (c : ℝ)
    (e₁ : Fin K₁ → ℝ) (e₂ : Fin K₂ → ℝ) (hpiv : (∃ i, e₁ i = 1 ∨ e₁ i = -1) ∨ ∃ i, e₂ i = 1 ∨ e₂ i = -1) :
    ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, G θ θ (c + ∑ i, e₁ i * Real.log (y₁ i) + ∑ i, e₂ i * Real.log (y₂ i) + θ) /
        (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ (12 * θ + 1 / Y₀) * B ^ (K₁ + K₂ - 1) := by
  set F : (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → ℝ := fun y₁ y₂ =>
    G θ θ (c + ∑ i, e₁ i * Real.log (y₁ i) + ∑ i, e₂ i * Real.log (y₂ i) + θ) /
      (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) with hF
  have hF0 : ∀ y₁ y₂, 0 ≤ F y₁ y₂ := fun y₁ y₂ =>
    div_nonneg (G_nonneg hθ (by linarith) _) (Nat.cast_nonneg _)
  have hs0 : ∀ {K : ℕ} (t : Fin K → Finset ℕ), (∀ i, ∀ p ∈ t i, Y₀ ≤ p) → ∀ i, 0 ≤ ∑ p ∈ t i, 1 / (p : ℝ) :=
    fun t _ i => Finset.sum_nonneg fun p _ => by positivity
  -- to the boxes
  have hbox : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, F y₁ y₂ ≤
      ∑ y₁ ∈ Fintype.piFinset t₁, ∑ y₂ ∈ Fintype.piFinset t₂, F y₁ y₂ := by
    refine (Finset.sum_le_sum fun y₁ _ => Finset.sum_le_sum_of_subset_of_nonneg hY₂
      fun y₂ _ _ => hF0 y₁ y₂).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hY₁ fun y₁ _ _ => Finset.sum_nonneg fun y₂ _ => hF0 y₁ y₂
  refine hbox.trans ?_
  have hsplit : ∀ y₁ y₂, F y₁ y₂ = 1 / ((∏ i, y₂ i : ℕ) : ℝ) *
      (G θ θ ((c + ∑ i, e₂ i * Real.log (y₂ i)) + ∑ i, e₁ i * Real.log (y₁ i) + θ) / ((∏ i, y₁ i : ℕ) : ℝ)) ∧
      F y₁ y₂ = 1 / ((∏ i, y₁ i : ℕ) : ℝ) *
      (G θ θ ((c + ∑ i, e₁ i * Real.log (y₁ i)) + ∑ i, e₂ i * Real.log (y₂ i) + θ) / ((∏ i, y₂ i : ℕ) : ℝ)) := by
    intro y₁ y₂
    simp only [hF]
    constructor
    · rw [show c + ∑ i, e₁ i * Real.log (y₁ i) + ∑ i, e₂ i * Real.log (y₂ i) + θ =
        (c + ∑ i, e₂ i * Real.log (y₂ i)) + ∑ i, e₁ i * Real.log (y₁ i) + θ by ring]
      push_cast
      ring
    · push_cast
      ring
  rcases hpiv with ⟨i₀, hi₀⟩ | ⟨i₀, hi₀⟩
  · -- the pivot in the first group
    obtain ⟨n, rfl⟩ : ∃ n, K₁ = n + 1 := ⟨K₁ - 1, by have := i₀.isLt; omega⟩
    rw [Finset.sum_comm]
    calc ∑ y₂ ∈ Fintype.piFinset t₂, ∑ y₁ ∈ Fintype.piFinset t₁, F y₁ y₂
        ≤ ∑ y₂ ∈ Fintype.piFinset t₂, 1 / ((∏ i, y₂ i : ℕ) : ℝ) * ((12 * θ + 1 / Y₀) * B ^ n) := by
          refine Finset.sum_le_sum fun y₂ _ => ?_
          simp only [fun y₁ => (hsplit y₁ y₂).1]
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (pivot_box t₁ hY₀ ht₁ hθ hθ1 _ e₁ i₀ hi₀).trans ?_
          exact mul_le_mul_of_nonneg_left (prod_le_pow _ (fun i => hs0 t₁ ht₁ _) fun i => hB₁ _)
            (by positivity)
      _ = (12 * θ + 1 / Y₀) * B ^ n * ∏ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) := by
          rw [← sum_box_inv, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y₂ _ => by ring
      _ ≤ (12 * θ + 1 / Y₀) * B ^ n * B ^ K₂ :=
          mul_le_mul_of_nonneg_left (prod_le_pow _ (fun i => hs0 t₂ ht₂ i) hB₂) (by positivity)
      _ = (12 * θ + 1 / Y₀) * B ^ (n + 1 + K₂ - 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
  · -- the pivot in the second group
    obtain ⟨n, rfl⟩ : ∃ n, K₂ = n + 1 := ⟨K₂ - 1, by have := i₀.isLt; omega⟩
    calc ∑ y₁ ∈ Fintype.piFinset t₁, ∑ y₂ ∈ Fintype.piFinset t₂, F y₁ y₂
        ≤ ∑ y₁ ∈ Fintype.piFinset t₁, 1 / ((∏ i, y₁ i : ℕ) : ℝ) * ((12 * θ + 1 / Y₀) * B ^ n) := by
          refine Finset.sum_le_sum fun y₁ _ => ?_
          simp only [fun y₂ => (hsplit y₁ y₂).2]
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (pivot_box t₂ hY₀ ht₂ hθ hθ1 _ e₂ i₀ hi₀).trans ?_
          exact mul_le_mul_of_nonneg_left (prod_le_pow _ (fun i => hs0 t₂ ht₂ _) fun i => hB₂ _)
            (by positivity)
      _ = (12 * θ + 1 / Y₀) * B ^ n * ∏ i, ∑ p ∈ t₁ i, 1 / (p : ℝ) := by
          rw [← sum_box_inv, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y₁ _ => by ring
      _ ≤ (12 * θ + 1 / Y₀) * B ^ n * B ^ K₁ :=
          mul_le_mul_of_nonneg_left (prod_le_pow _ (fun i => hs0 t₁ ht₁ i) hB₁) (by positivity)
      _ = (12 * θ + 1 / Y₀) * B ^ (K₁ + (n + 1) - 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega

/-- The near-boundary masses of a sieve, regrouped:
`Σ_{(y₁,σ),y₂} C|λ_σ|M/(π₁f_σπ₂) = C(Σ_σ |λ_σ|/f_σ)Σ_{y₁,y₂} M/(π₁π₂)`. -/
theorem nb_regroup {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (S : Finset κ) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (f : κ → ℕ) (l : κ → ℝ) (C : ℝ) (M : ι₁ → ι₂ → ℝ) :
    ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, C * |l x.2| * M x.1 y₂ / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) =
      C * (∑ σ ∈ S, |l σ| / f σ) * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, M y₁ y₂ / (π₁ y₁ * π₂ y₂ : ℕ) := by
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  dsimp only
  push_cast
  ring

/-! ### The parameters as powers of `q` -/

/-- `t/2 ≤ log(1 + t)` for `0 ≤ t ≤ 1`. -/
theorem half_le_log_one_add {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t / 2 ≤ Real.log (1 + t) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + t by linarith)
  have e : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
  rw [e] at h
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-- **The number of blocks.** For `x ≥ 3`, `s > 0`, `L ≥ 2`, `ρ = 1 + x^{−s}` and `1 ≤ X ≤ x^L`:
`blk(⌊X⌋) + 1 ≤ 3Lx^s log x`. -/
theorem blk_floor_le {x s L : ℝ} (hx : 3 ≤ x) (hs : 0 < s) (hL : 2 ≤ L) {X : ℝ} (hX1 : 1 ≤ X) (hXL : X ≤ x ^ L) :
    (blk (1 + x ^ (-s)) ⌊X⌋₊ : ℝ) + 1 ≤ 3 * L * x ^ s * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hη0 : 0 < x ^ (-s) := Real.rpow_pos_of_pos hx0 _
  have hη1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hρ : 1 < 1 + x ^ (-s) := by linarith
  have hlogρ : x ^ (-s) / 2 ≤ Real.log (1 + x ^ (-s)) := half_le_log_one_add hη0.le hη1
  have hlogρ0 : 0 < Real.log (1 + x ^ (-s)) := Real.log_pos hρ
  have hlx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hxs : 1 ≤ x ^ s := Real.one_le_rpow (by linarith) hs.le
  have hfl1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX1)
  have hlogX : Real.log ⌊X⌋₊ ≤ L * Real.log x := by
    calc Real.log ⌊X⌋₊ ≤ Real.log X := Real.log_le_log (by exact_mod_cast hfl1) (Nat.floor_le (by linarith))
      _ ≤ Real.log (x ^ L) := Real.log_le_log (by linarith) hXL
      _ = L * Real.log x := Real.log_rpow hx0 L
  have hb : (blk (1 + x ^ (-s)) ⌊X⌋₊ : ℝ) ≤ Real.log ⌊X⌋₊ / Real.log (1 + x ^ (-s)) := by
    unfold blk
    exact Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hfl1)) hlogρ0.le)
  have hb2 : Real.log ⌊X⌋₊ / Real.log (1 + x ^ (-s)) ≤ 2 * L * x ^ s * Real.log x := by
    rw [div_le_iff₀ hlogρ0]
    have hinv : x ^ s * x ^ (-s) = 1 := by rw [← Real.rpow_add hx0]; simp
    have hL0 : 0 ≤ L * Real.log x := by positivity
    calc Real.log ⌊X⌋₊ ≤ L * Real.log x := hlogX
      _ = 2 * L * x ^ s * Real.log x * (x ^ (-s) / 2) := by
          rw [show 2 * L * x ^ s * Real.log x * (x ^ (-s) / 2) = L * Real.log x * (x ^ s * x ^ (-s)) by ring,
            hinv, mul_one]
      _ ≤ 2 * L * x ^ s * Real.log x * Real.log (1 + x ^ (-s)) :=
          mul_le_mul_of_nonneg_left hlogρ (by positivity)
  have h1 : (1 : ℝ) ≤ L * x ^ s * Real.log x := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ L * x ^ s * Real.log x := by gcongr; linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **The uniform bound as powers of `q`.** Let `x = q ≥ 3`, `L > 2`, `0 ≤ δ'`, `0 ≤ a ≤ L − 2`, `0 < s ≤ b/2`,
`r ≥ 4/b`, `F ≤ C_dx^s` and `d(q) ≤ C_dx^s`. With `η = x^{−s}`, `ρ = 1 + η`, `N₁ = ⌊x^L⌋`, `N₂ = ⌊2x^L⌋`,
`X₁ = x^{L−1−a}`, `X₂ = x^{L−b}` and `X₃ = x^{L−1−δ'}`:
`bdU ≤ √(816C_d)x^{L−1−(a−δ'−s)/2} + 16(16r)^r x^{L−2} + 4C_dx^{L−1/2+s}/φ(q)`. -/
theorem bdU_le_pow (q : ℕ) [NeZero q] {L s a b δ' Cd : ℝ} (hq3 : (3 : ℝ) ≤ q) (hL : 2 < L) (hδ' : 0 ≤ δ')
    (ha : 0 ≤ a) (haL : a ≤ L - 2) (hb : 0 < b) (hs : 0 < s) (hsb : s ≤ b / 2) {r : ℕ}
    (hr : 4 / b ≤ r) {F : ℕ} (hF : (F : ℝ) ≤ Cd * (q : ℝ) ^ s)
    (hdq : (q.divisors.card : ℝ) ≤ Cd * (q : ℝ) ^ s) :
    bdU q (1 + (q : ℝ) ^ (-s)) ((q : ℝ) ^ (-s)) ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊ r F ((q : ℝ) ^ (L - 1 - a))
        ((q : ℝ) ^ (L - b)) ((q : ℝ) ^ (L - 1 - δ')) ≤
      √(816 * Cd) * (q : ℝ) ^ (L - 1 - (a - δ' - s) / 2) + 16 * (16 * r) ^ r * (q : ℝ) ^ (L - 2) +
        4 * Cd * (q : ℝ) ^ (L - 1 / 2 + s) / q.totient := by
  set x : ℝ := (q : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set η : ℝ := x ^ (-s) with hηdef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hρ1 : 1 + η ≤ 2 := by linarith
  have hxL : 2 ≤ x ^ L := by
    calc (2 : ℝ) ≤ x ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
      _ ≤ x ^ L := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  set N₁ := ⌊x ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * x ^ L⌋₊ with hN₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
  have hN₁ge : x ^ L / 2 ≤ (N₁ : ℝ) := by
    have := Nat.sub_one_lt_floor (x ^ L)
    linarith
  have hN₂0 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
  have hdq0 : 0 ≤ Cd * x ^ s := le_trans (Nat.cast_nonneg _) hdq
  have hxs1 : 1 ≤ x ^ s := Real.one_le_rpow hx1 hs.le
  have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (by positivity)).1 hdq0
  clear_value N₁ N₂
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  rw [bdU]
  -- the first term
  have hA : √((1 + η) ^ 2 * (1 + η) * N₂ * ((1 + η) * x ^ (L - 1 - a) / q + 1) * F *
        ((1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1)) ≤
      √(816 * Cd) * x ^ (L - 1 - (a - δ' - s) / 2) := by
    have e1 : (1 + η) ^ 2 * (1 + η) * N₂ ≤ 16 * x ^ L := by
      have : (1 + η) ^ 2 * (1 + η) ≤ 8 := by
        have h0 : 0 ≤ 1 + η := by linarith
        calc (1 + η) ^ 2 * (1 + η) ≤ 2 ^ 2 * 2 := by gcongr
          _ = 8 := by norm_num
      nlinarith
    have hxa : 1 ≤ x ^ (L - 2 - a) := Real.one_le_rpow hx1 (by linarith)
    have e2 : (1 + η) * x ^ (L - 1 - a) / q + 1 ≤ 3 * x ^ (L - 2 - a) := by
      have : x ^ (L - 1 - a) / x = x ^ (L - 2 - a) := by
        rw [div_eq_iff hx0.ne', ← Real.rpow_add_one hx0.ne']; ring_nf
      have h2 : (1 + η) * x ^ (L - 1 - a) / q = (1 + η) * x ^ (L - 2 - a) := by
        rw [mul_div_assoc, ← hxdef, this]
      rw [h2]
      nlinarith
    have hxδ : 1 ≤ x ^ δ' := Real.one_le_rpow hx1 hδ'
    have e3 : (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1 ≤ 17 * x ^ δ' := by
      have hden : x ^ (L - 1 - δ') * q = x ^ L / x ^ δ' := by
        rw [← hxdef, eq_div_iff (by positivity)]
        calc x ^ (L - 1 - δ') * x * x ^ δ' = x ^ (L - 1 - δ') * x ^ (1 : ℝ) * x ^ δ' := by rw [Real.rpow_one]
          _ = x ^ (L - 1 - δ' + 1 + δ') := by rw [Real.rpow_add hx0, Real.rpow_add hx0]
          _ = x ^ L := by ring_nf
      rw [hden]
      have h8 : (1 + η) * (1 + η) ^ 2 * N₂ ≤ 16 * x ^ L := by nlinarith
      have hpos : 0 < x ^ L / x ^ δ' := by positivity
      have : (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ L / x ^ δ') ≤ 16 * x ^ δ' := by
        rw [div_le_iff₀ hpos]
        rw [show 16 * x ^ δ' * (x ^ L / x ^ δ') = 16 * x ^ L by field_simp]
        exact h8
      linarith
    have hprod : (1 + η) ^ 2 * (1 + η) * N₂ * ((1 + η) * x ^ (L - 1 - a) / q + 1) * F *
        ((1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1) ≤
        (16 * x ^ L) * (3 * x ^ (L - 2 - a)) * (Cd * x ^ s) * (17 * x ^ δ') := by
      have h0a : 0 ≤ (1 + η) ^ 2 * (1 + η) * N₂ := by positivity
      have h0b : 0 ≤ (1 + η) * x ^ (L - 1 - a) / q + 1 := by positivity
      have h0c : (0 : ℝ) ≤ F := Nat.cast_nonneg _
      have h0d : 0 ≤ (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1 := by positivity
      gcongr
    have hsq : (16 * x ^ L) * (3 * x ^ (L - 2 - a)) * (Cd * x ^ s) * (17 * x ^ δ') =
        816 * Cd * (x ^ (L - 1 - (a - δ' - s) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      have : x ^ L * x ^ (L - 2 - a) * x ^ s * x ^ δ' = x ^ ((L - 1 - (a - δ' - s) / 2) * ((2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1; push_cast; ring
      rw [← this]; ring
    calc _ ≤ √(816 * Cd * (x ^ (L - 1 - (a - δ' - s) / 2)) ^ 2) := Real.sqrt_le_sqrt (hprod.trans (le_of_eq hsq))
      _ = √(816 * Cd) * x ^ (L - 1 - (a - δ' - s) / 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the tail
  have hB : (1 + η) ^ 2 * (1 + η) * N₂ * (r * (1 + η) ^ 3 * x ^ (L - b) / (η * N₁)) ^ r ≤
      16 * (16 * r) ^ r * x ^ (L - 2) := by
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
    have hbase : r * (1 + η) ^ 3 * x ^ (L - b) / (η * N₁) ≤ 16 * r * x ^ (s - b) := by
      have hN₁0 : 0 < (N₁ : ℝ) := lt_of_lt_of_le (by positivity) hN₁ge
      rw [div_le_iff₀ (by positivity)]
      have h3 : (1 + η) ^ 3 ≤ 8 := by
        calc (1 + η) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) hρ1 3
          _ = 8 := by norm_num
      have hsb' : x ^ (s - b) * η * x ^ L = x ^ (L - b) := by
        rw [hηdef, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
      calc r * (1 + η) ^ 3 * x ^ (L - b) ≤ r * 8 * x ^ (L - b) := by gcongr
        _ = 16 * r * x ^ (s - b) * (η * (x ^ L / 2)) := by rw [← hsb']; ring
        _ ≤ 16 * r * x ^ (s - b) * (η * N₁) := by gcongr
    have hpow : (r * (1 + η) ^ 3 * x ^ (L - b) / (η * N₁)) ^ r ≤ (16 * r) ^ r * x ^ (-2 : ℝ) := by
      have hb0 : 0 ≤ r * (1 + η) ^ 3 * x ^ (L - b) / (η * N₁) := by positivity
      refine (pow_le_pow_left₀ hb0 hbase r).trans ?_
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      have : (s - b) * r ≤ -(b / 2) * r := by nlinarith
      have : (b / 2) * r ≥ 2 := by
        have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ b / 2)
        rw [show b / 2 * (4 / b) = 2 by field_simp; ring] at this
        linarith
      linarith
    have e1 : (1 + η) ^ 2 * (1 + η) * N₂ ≤ 16 * x ^ L := by
      have : (1 + η) ^ 2 * (1 + η) ≤ 8 := by
        have h0 : 0 ≤ 1 + η := by linarith
        calc (1 + η) ^ 2 * (1 + η) ≤ 2 ^ 2 * 2 := by gcongr
          _ = 8 := by norm_num
      nlinarith
    calc (1 + η) ^ 2 * (1 + η) * N₂ * (r * (1 + η) ^ 3 * x ^ (L - b) / (η * N₁)) ^ r
        ≤ (16 * x ^ L) * ((16 * r) ^ r * x ^ (-2 : ℝ)) := mul_le_mul e1 hpow (by positivity) (by positivity)
      _ = 16 * (16 * r) ^ r * (x ^ L * x ^ (-2 : ℝ)) := by ring
      _ = 16 * (16 * r) ^ r * x ^ (L - 2) := by rw [← Real.rpow_add hx0]; ring_nf
  -- the last term
  have hC : (1 + η) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L - b)) * ((q.divisors.card : ℝ) / q.totient) ≤
      4 * Cd * x ^ (L - 1 / 2 + s) / q.totient := by
    have hsq : √(x ^ (L - 1 - a) * x ^ (L - b)) ≤ x ^ (L - 1 / 2) := by
      rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : (1 + η) ^ 2 ≤ 4 := by nlinarith
    calc (1 + η) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L - b)) * ((q.divisors.card : ℝ) / q.totient)
        ≤ 4 * x ^ (L - 1 / 2) * (Cd * x ^ s / q.totient) := by
          gcongr
      _ = 4 * Cd * x ^ (L - 1 / 2 + s) / q.totient := by
          rw [Real.rpow_add hx0]; ring
  linarith

open Filter in
/-- For `α < β` and any `C`: eventually `C(log x)²x^α ≤ x^β`. -/
theorem ev_log_sq_le (C : ℝ) {α β : ℝ} (h : α < β) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ 2 * x ^ α ≤ x ^ β := by
  set g := (β - α) / 4 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have h1 := (isLittleO_log_rpow_atTop hg0).def one_pos
  have h2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 2 * g)).eventually_ge_atTop (|C|)
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
    one_mul] at hx1
  have hl2 : Real.log x ^ 2 ≤ x ^ (2 * g) := by
    rw [show 2 * g = g + g by ring, Real.rpow_add hx0, sq]
    exact mul_le_mul hx1 hx1 hl (Real.rpow_nonneg hx0.le _)
  have hxa : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le _
  calc C * Real.log x ^ 2 * x ^ α ≤ |C| * Real.log x ^ 2 * x ^ α := by
        gcongr
        exact le_abs_self C
    _ ≤ x ^ (2 * g) * x ^ (2 * g) * x ^ α := by
        gcongr
    _ = x ^ β := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hg]; ring_nf

/-! ### The asymptotic form -/

/-- The exponent `s` of the parameters `η = θ = q^{−s}`:
`s = min((a − δ')/(2(J₀ + 6)), b/2, e₀, 1/(4(J₀ + 6)))`. -/
noncomputable def sIB (a b δ' e₀ : ℝ) (J₀ : ℕ) : ℝ :=
  min (min ((a - δ') / (2 * (J₀ + 6))) (b / 2)) (min e₀ (1 / (4 * (J₀ + 6))))

theorem sIB_spec {a b δ' e₀ : ℝ} (hab : δ' < a) (hb : 0 < b) (he₀ : 0 < e₀) (J₀ : ℕ) :
    0 < sIB a b δ' e₀ J₀ ∧ sIB a b δ' e₀ J₀ ≤ (a - δ') / (2 * (J₀ + 6)) ∧ sIB a b δ' e₀ J₀ ≤ b / 2 ∧
      sIB a b δ' e₀ J₀ ≤ e₀ ∧ sIB a b δ' e₀ J₀ ≤ 1 / (4 * (J₀ + 6)) := by
  unfold sIB
  have h1 : 0 < (a - δ') / (2 * (J₀ + 6)) := by apply div_pos <;> [linarith; positivity]
  refine ⟨lt_min (lt_min h1 (by linarith)) (lt_min he₀ (by positivity)), ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The leaves' weights over boxes: `Σ_{y₁,y₂} c/(∏y₁∏y₂) ≤ B^{K₁+K₂}` for `0 ≤ c ≤ 1`, families in boxes with
`Σ_{p∈t_i} 1/p ≤ B` and `B ≥ 0`. -/
theorem box_weight_le {K₁ K₂ : ℕ} (t₁ : Fin K₁ → Finset ℕ) (t₂ : Fin K₂ → Finset ℕ)
    (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)) (hY₁ : Y₁ ⊆ Fintype.piFinset t₁)
    (hY₂ : Y₂ ⊆ Fintype.piFinset t₂) {B : ℝ} (hB : 0 ≤ B) (hB₁ : ∀ i, ∑ p ∈ t₁ i, 1 / (p : ℝ) ≤ B)
    (hB₂ : ∀ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) ≤ B) (c : (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → ℝ)
    (hc1 : ∀ y₁ y₂, c y₁ y₂ ≤ 1) :
    ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ / (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ B ^ (K₁ + K₂) := by
  have hs0 : ∀ {K : ℕ} (t : Fin K → Finset ℕ) (i : Fin K), 0 ≤ ∑ p ∈ t i, 1 / (p : ℝ) :=
    fun t i => Finset.sum_nonneg fun p _ => by positivity
  calc ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ / (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ)
      ≤ ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, 1 / ((∏ i, y₁ i : ℕ) : ℝ) * (1 / ((∏ i, y₂ i : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun y₁ _ => Finset.sum_le_sum fun y₂ _ => ?_
        rw [one_div_mul_one_div, ← Nat.cast_mul]
        exact div_le_div_of_nonneg_right (hc1 y₁ y₂) (Nat.cast_nonneg _)
    _ ≤ ∑ y₁ ∈ Fintype.piFinset t₁, ∑ y₂ ∈ Fintype.piFinset t₂,
          1 / ((∏ i, y₁ i : ℕ) : ℝ) * (1 / ((∏ i, y₂ i : ℕ) : ℝ)) := by
        refine (Finset.sum_le_sum fun y₁ _ => Finset.sum_le_sum_of_subset_of_nonneg hY₂
          fun y₂ _ _ => by positivity).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hY₁ fun y₁ _ _ => Finset.sum_nonneg fun y₂ _ => by positivity
    _ = (∏ i, ∑ p ∈ t₁ i, 1 / (p : ℝ)) * ∏ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) := by
        rw [← sum_box_inv, ← sum_box_inv, Finset.sum_mul_sum]
    _ ≤ B ^ K₁ * B ^ K₂ := mul_le_mul (prod_le_pow _ (fun i => hs0 t₁ i) hB₁)
        (prod_le_pow _ (fun i => hs0 t₂ i) hB₂) (Finset.prod_nonneg fun i _ => hs0 t₂ i) (by positivity)
    _ = B ^ (K₁ + K₂) := (pow_add B K₁ K₂).symm

/-- The Fourier masses of `J ≤ J₀` cut-offs, each at most `M ≥ 1`: `∏_j m_j + Σ_j m'_j ≤ (J₀ + 1)M^{J₀}`. -/
theorem masses_le {J J₀ : ℕ} (hJ : J ≤ J₀) (m m' : Fin J → ℝ) {M : ℝ} (hM : 1 ≤ M) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m j ≤ M) (hm' : ∀ j, m' j ≤ M) : (∏ j, m j) + ∑ j, m' j ≤ (J₀ + 1) * M ^ J₀ := by
  have h1 : ∏ j, m j ≤ M ^ J₀ :=
    (prod_le_pow m hm0 hm).trans (pow_le_pow_right₀ hM hJ)
  have h2 : ∑ j, m' j ≤ J₀ * M ^ J₀ := by
    calc ∑ j, m' j ≤ ∑ _j : Fin J, M := Finset.sum_le_sum fun j _ => hm' j
      _ = J * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ J₀ * M ^ J₀ := by
          have hMJ : M ≤ M ^ J₀ ∨ J = 0 := by
            rcases Nat.eq_zero_or_pos J with h | h
            · exact Or.inr h
            · exact Or.inl (le_self_pow₀ hM (by omega))
          rcases hMJ with h | h
          · have hJ' : (J : ℝ) ≤ J₀ := by exact_mod_cast hJ
            exact mul_le_mul hJ' h (by linarith) (by positivity)
          · rw [h, Nat.cast_zero, zero_mul]; positivity
  linarith

/-- `x^α·x^β ≤ x^γ/φ` when `α + β ≤ γ − 1`, `x ≥ 1` and `0 < φ ≤ x`. -/
theorem rpow_mul_le_div {x φ α β γ : ℝ} (hx : 1 ≤ x) (hφ0 : 0 < φ) (hφx : φ ≤ x) (h : α + β ≤ γ - 1) :
    x ^ α * x ^ β ≤ x ^ γ / φ := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_add hx0, le_div_iff₀ hφ0]
  calc x ^ (α + β) * φ ≤ x ^ (γ - 1) * x :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx h) hφx hφ0.le (by positivity)
    _ = x ^ γ := by rw [Real.rpow_sub_one hx0.ne']; field_simp

/-- **The bilinear part, as a power of `q`.** With `k_i ≤ 3Lx^s log x`, `FN ≤ (J₀ + 1)(C_mx^s)^{J₀}`,
`M_f, M₂ ≤ x^{c₁}` and `U` at most `bdU_le_pow`'s bound (with `r' = 16(16r)^r`), and the exponents below:
`4k₁k₂·FN·M_fM₂U ≤ 36L²(J₀ + 1)C_m^{J₀}(√(816C_d) + r' + 4C_d)(log x)²x^{L−3s/4}/φ`. -/
theorem bil_le {x φ L s c₁ a δ' Cm Cd r' FN Mf M₂ U k₁ k₂ : ℝ} {J₀ : ℕ} (hx : 3 ≤ x) (hφ0 : 0 < φ) (hφx : φ ≤ x)
    (hL : 0 ≤ L) (hk₁0 : 0 ≤ k₁) (hk₁ : k₁ ≤ 3 * L * x ^ s * Real.log x) (hk₂0 : 0 ≤ k₂)
    (hk₂ : k₂ ≤ 3 * L * x ^ s * Real.log x) (hFN0 : 0 ≤ FN) (hFN : FN ≤ (J₀ + 1) * (Cm * x ^ s) ^ J₀)
    (hMf0 : 0 ≤ Mf) (hMf : Mf ≤ x ^ c₁) (hM₂0 : 0 ≤ M₂) (hM₂ : M₂ ≤ x ^ c₁) (hU0 : 0 ≤ U)
    (hU : U ≤ √(816 * Cd) * x ^ (L - 1 - (a - δ' - s) / 2) + r' * x ^ (L - 2) + 4 * Cd * x ^ (L - 1 / 2 + s) / φ)
    (hCd : 0 ≤ Cd) (hr' : 0 ≤ r') (hCm : 0 ≤ Cm)
    (e1 : (J₀ + 2) * s + 2 * c₁ + (L - 1 - (a - δ' - s) / 2) ≤ L - 3 * s / 4 - 1)
    (e2 : (J₀ + 2) * s + 2 * c₁ + (L - 2) ≤ L - 3 * s / 4 - 1)
    (e3 : (J₀ + 2) * s + 2 * c₁ + (L - 1 / 2 + s) ≤ L - 3 * s / 4) :
    4 * (k₁ * k₂) * (FN * (Mf * M₂ * U)) ≤
      36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * (√(816 * Cd) + r' + 4 * Cd) * Real.log x ^ 2 * x ^ (L - 3 * s / 4) / φ := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  set E := x ^ ((J₀ + 2) * s + 2 * c₁) with hE
  have hE0 : 0 ≤ E := by positivity
  -- the product of the counts, masses and fibres
  have hprod : 4 * (k₁ * k₂) * (FN * (Mf * M₂)) ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 * E := by
    have h1 : k₁ * k₂ ≤ (3 * L * x ^ s * Real.log x) * (3 * L * x ^ s * Real.log x) :=
      mul_le_mul hk₁ hk₂ hk₂0 (le_trans hk₁0 hk₁)
    have h2 : Mf * M₂ ≤ x ^ c₁ * x ^ c₁ := mul_le_mul hMf hM₂ hM₂0 (le_trans hMf0 hMf)
    have h3 : FN * (Mf * M₂) ≤ (J₀ + 1) * (Cm * x ^ s) ^ J₀ * (x ^ c₁ * x ^ c₁) :=
      mul_le_mul hFN h2 (mul_nonneg hMf0 hM₂0) (by positivity)
    have hEq : (3 * L * x ^ s * Real.log x) * (3 * L * x ^ s * Real.log x) *
        ((J₀ + 1) * (Cm * x ^ s) ^ J₀ * (x ^ c₁ * x ^ c₁)) =
        9 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 * E := by
      rw [hE, mul_pow, ← Real.rpow_natCast (x ^ s), ← Real.rpow_mul hx0.le]
      have : x ^ s * x ^ s * x ^ (s * (J₀ : ℝ)) * (x ^ c₁ * x ^ c₁) = x ^ ((J₀ + 2) * s + 2 * c₁) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1; ring
      rw [← this]; ring
    calc 4 * (k₁ * k₂) * (FN * (Mf * M₂))
        ≤ 4 * ((3 * L * x ^ s * Real.log x) * (3 * L * x ^ s * Real.log x)) *
            ((J₀ + 1) * (Cm * x ^ s) ^ J₀ * (x ^ c₁ * x ^ c₁)) := by
          gcongr
      _ = 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 * E := by rw [mul_assoc 4, hEq]; ring
  -- `E·U` against `x^{L−3s/4}/φ`
  have hEU : E * U ≤ (√(816 * Cd) + r' + 4 * Cd) * (x ^ (L - 3 * s / 4) / φ) := by
    have k1 : E * x ^ (L - 1 - (a - δ' - s) / 2) ≤ x ^ (L - 3 * s / 4) / φ :=
      rpow_mul_le_div hx1 hφ0 hφx (by linarith)
    have k2 : E * x ^ (L - 2) ≤ x ^ (L - 3 * s / 4) / φ := rpow_mul_le_div hx1 hφ0 hφx (by linarith)
    have k3 : E * x ^ (L - 1 / 2 + s) ≤ x ^ (L - 3 * s / 4) := by
      rw [hE, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 e3
    calc E * U ≤ E * (√(816 * Cd) * x ^ (L - 1 - (a - δ' - s) / 2) + r' * x ^ (L - 2) +
          4 * Cd * x ^ (L - 1 / 2 + s) / φ) := mul_le_mul_of_nonneg_left hU hE0
      _ = √(816 * Cd) * (E * x ^ (L - 1 - (a - δ' - s) / 2)) + r' * (E * x ^ (L - 2)) +
          4 * Cd * (E * x ^ (L - 1 / 2 + s)) / φ := by ring
      _ ≤ √(816 * Cd) * (x ^ (L - 3 * s / 4) / φ) + r' * (x ^ (L - 3 * s / 4) / φ) +
          4 * Cd * x ^ (L - 3 * s / 4) / φ := by
          gcongr
      _ = (√(816 * Cd) + r' + 4 * Cd) * (x ^ (L - 3 * s / 4) / φ) := by ring
  have hc0 : 0 ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 := by positivity
  calc 4 * (k₁ * k₂) * (FN * (Mf * M₂ * U)) = 4 * (k₁ * k₂) * (FN * (Mf * M₂)) * U := by ring
    _ ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 * E * U :=
        mul_le_mul_of_nonneg_right hprod hU0
    _ = 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 * (E * U) := by ring
    _ ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * Real.log x ^ 2 *
          ((√(816 * Cd) + r' + 4 * Cd) * (x ^ (L - 3 * s / 4) / φ)) := mul_le_mul_of_nonneg_left hEU hc0
    _ = _ := by ring

/-- The leaves' explicit bound, regrouped: `Σ_y c(α·Γ/d + (V·Θ/d + 4W)/x + 2W·D/φ) =
αΓ·Σ_y c/d + (VΘ/x)·Σ_y c/d + (4W/x + 2W·D/φ)·Σ_y c`. -/
theorem split_main {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (c d : ι₁ → ι₂ → ℝ)
    (α Γ V W Θ x D φ : ℝ) :
    ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * (α * (Γ / d y₁ y₂) + (V * (Θ / d y₁ y₂) + 4 * W) / x + 2 * W * (D / φ)) =
      α * Γ * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ / d y₁ y₂ + V * Θ / x * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ / d y₁ y₂ +
        (4 * W / x + 2 * W * (D / φ)) * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

set_option maxHeartbeats 4000000 in
open Classical Filter in
/-- **The leaves by the bilinear estimate, asymptotically.** Fix `L > 2`, margins `0 ≤ δ' < a ≤ L − 2` and
`0 < b ≤ L`, `e₀ > 0`, `Λ₀ ≥ 0`, `B ≥ 1`, sizes `K₁`, `K₂`, `J₀`, and `0 ≤ c₁ < s/4` with `s = sIB a b δ' e₀ J₀`.
There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a'`: let families `Y₁`, `Y₂` of tuples lie in boxes of
integers at least `q^{e₀}` with `Σ 1/p ≤ B` on each coordinate, with fibres of `∏y₂` at most `q^{c₁}`; let
`J ≤ J₀` sharp comparisons `Pr_j` of forms `c_j + Σ e₁ log y₁ + Σ e₂ log y₂ ≤ Λ₀ log q`, each with a coefficient
`±1`; let sieve weights `S₁` above and `S₂` below sandwich `R`, with divisors in `[1, f_max]`, fibres and
`Σ|λ|/f` at most `q^{c₁}` and `Σ|λ|` at most `q^{1/4}`; and let every leaf have `∏y₁·f_max ≤ q^{L−1−a}`,
`∏y₁·f_max(∏y₂)² ≤ q^{L−b}` and `∏y₁∏y₂ ≥ q^{L−1−δ'}`. Then the leaves' sum
`Σ_{y₁,y₂} c Σ_m rng(d, m)R(m)dw(dm)`, `c = ∏_j 1[Pr_j]`, `d = ∏y₁∏y₂`, `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋`, is at most
`(N₂ − N₁)/q·|Γ|·Σ_y c/d + q^{L−δ}/φ(q)` in absolute value, `Γ` the sieve's gap. -/
theorem leaves_ib {L : ℝ} (hL : 2 < L) {a b δ' e₀ c₁ Λ₀ B : ℝ} (hδ' : 0 ≤ δ') (hab : δ' < a) (haL : a ≤ L - 2)
    (hb : 0 < b) (hbL : b ≤ L) (he₀ : 0 < e₀) (hΛ₀ : 0 ≤ Λ₀) (hB : 1 ≤ B) (K₁ K₂ J₀ : ℕ) (hc₁0 : 0 ≤ c₁)
    (hc₁ : c₁ < sIB a b δ' e₀ J₀ / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
    ∀ (t₁ : Fin K₁ → Finset ℕ) (t₂ : Fin K₂ → Finset ℕ),
      (∀ i, ∀ p ∈ t₁ i, (q : ℝ) ^ e₀ ≤ p) → (∀ i, ∀ p ∈ t₂ i, (q : ℝ) ^ e₀ ≤ p) →
      (∀ i, ∑ p ∈ t₁ i, 1 / (p : ℝ) ≤ B) → (∀ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) ≤ B) →
    ∀ (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)), Y₁ ⊆ Fintype.piFinset t₁ →
      Y₂ ⊆ Fintype.piFinset t₂ → (∀ d, (#(Y₂.filter (fun y => ∏ i, y i = d)) : ℝ) ≤ (q : ℝ) ^ c₁) →
    ∀ {J : ℕ}, J ≤ J₀ → ∀ (cc : Fin J → ℝ) (e₁ : Fin J → Fin K₁ → ℝ) (e₂ : Fin J → Fin K₂ → ℝ)
      (Pr : Fin J → (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → Prop),
      (∀ j y₁ y₂, (0 < cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) → Pr j y₁ y₂) ∧
        (Pr j y₁ y₂ → 0 ≤ cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) →
      (∀ j, ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
        cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ₀ * Real.log q) →
      (∀ j, (∃ i, e₁ j i = 1 ∨ e₁ j i = -1) ∨ ∃ i, e₂ j i = 1 ∨ e₂ j i = -1) →
    ∀ (R : ℕ → ℝ) {κ₁ κ₂ : Type} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (S₂ : Finset κ₂)
      (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ), (∀ σ ∈ S₁, 1 ≤ f₁ σ) → (∀ τ ∈ S₂, 1 ≤ f₂ τ) →
      (∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m) → (∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m) →
    ∀ fmax : ℝ, 1 ≤ fmax → (∀ σ ∈ S₁, (f₁ σ : ℝ) ≤ fmax) → (∀ τ ∈ S₂, (f₂ τ : ℝ) ≤ fmax) →
      (∀ d, ∑ x ∈ (Y₁ ×ˢ S₁).filter (fun x => (∏ i, x.1 i) * f₁ x.2 = d), |l₁ x.2| ≤ (q : ℝ) ^ c₁) →
      (∀ d, ∑ x ∈ (Y₁ ×ˢ S₂).filter (fun x => (∏ i, x.1 i) * f₂ x.2 = d), |l₂ x.2| ≤ (q : ℝ) ^ c₁) →
      ∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ| ≤ (q : ℝ) ^ (1 / 4 : ℝ) →
      ∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ ≤ (q : ℝ) ^ c₁ →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
        (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) →
      |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) *
          ∑ m ∈ range (⌊2 * (q : ℝ) ^ L⌋₊ + 1),
            rng ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊ ((∏ i, y₁ i) * ∏ i, y₂ i) m * R m *
              dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m)| ≤
        ((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) / q *
            |∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| *
            ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
              (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨hs0, hsa, hsb, hse, hs1⟩ := sIB_spec hab hb he₀ J₀
  set s := sIB a b δ' e₀ J₀ with hsdef
  have hs1' : s ≤ 1 := hs1.trans (by rw [div_le_one (by positivity)]; linarith)
  set r : ℕ := ⌈4 / b⌉₊ with hrdef
  have hr4 : 4 / b ≤ r := Nat.le_ceil _
  have hr1 : 1 ≤ r := by
    have h4 : (0 : ℝ) < 4 / b := by positivity
    have : (0 : ℝ) < r := lt_of_lt_of_le h4 hr4
    have : 0 < r := by exact_mod_cast this
    omega
  set Cd := LinnikPower.Cdiv s with hCddef
  have hCd1 : 1 ≤ Cd := LinnikPower.one_le_Cdiv hs0 hs1'
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖ := integral_nonneg fun _ => norm_nonneg _
  set Cm := 1 + (∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖) / (2 * Real.pi) with hCmdef
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ (∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖) / (2 * Real.pi) := by positivity
    linarith
  set r' : ℝ := 16 * (16 * r) ^ r with hr'def
  have hr'0 : 0 ≤ r' := by positivity
  set Ctot : ℝ := (15 + 2 * Cd) * B ^ (K₁ + K₂) +
    36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * (√(816 * Cd) + r' + 4 * Cd) + 416 * J₀ * B ^ (K₁ + K₂) with hCtot
  refine ⟨s / 4, by positivity, ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ Real.pi * (2 * Λ₀ * Real.log x + 3) ≤ x ^ s ∧
      Ctot * Real.log x ^ 2 * x ^ (L - 3 * s / 4) ≤ x ^ (L - s / 4) :=
    (eventually_ge_atTop 3).and ((SieveFamily.ev_pi_log_le hs0 hΛ₀).and (ev_log_sq_le Ctot (by linarith)))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨q₀, ?_⟩
  intro q _ hq a' ha' t₁ t₂ ht₁ ht₂ hB₁ hB₂ Y₁ Y₂ hY₁ hY₂ hM₂ J hJ cc e₁ e₂ Pr hPr hΛ hpiv R κ₁ κ₂ S₁ f₁ l₁ S₂ f₂
    l₂ hf₁ hf₂ hR₁ hR₂ fmax hfmax hfm₁ hfm₂ hMf₁ hMf₂ hW hV hreg
  obtain ⟨hx3, hmassc, hfin⟩ := hq₀ q hq
  set x : ℝ := (q : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφx : (q.totient : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast Nat.totient_le q
  -- the parameters
  have hxs9 : 9 ≤ x ^ s := by
    have := Real.pi_gt_three
    have : 0 ≤ Real.pi * (2 * Λ₀ * Real.log x) := by positivity
    nlinarith
  set θ : ℝ := x ^ (-s) with hθdef
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hx0 _
  have hθxs : θ * x ^ s = 1 := by rw [hθdef, ← Real.rpow_add hx0]; simp
  have hθ9 : θ ≤ 1 / 9 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  set Λ : ℝ := Λ₀ * Real.log x + 1 with hΛdef
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef]; nlinarith [mul_nonneg hΛ₀ hlx]
  have hθΛ : θ ≤ 2 * Λ := by linarith
  obtain ⟨hGc, hGi, hGf, hGm, hMc, hMi, hMfr, hMm⟩ := cutoffs hθ0 hθΛ
  obtain ⟨hmB1, hmB2⟩ := SieveFamily.massB_le hx1 hΛ₀ hmassc
  set N₁ : ℕ := ⌊x ^ L⌋₊ with hN₁def
  set N₂ : ℕ := ⌊2 * x ^ L⌋₊ with hN₂def
  have hxL1 : 1 ≤ x ^ L := Real.one_le_rpow hx1 (by linarith)
  have hN : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₁ : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hxL1)
  have hN₁le : (N₁ : ℝ) ≤ x ^ L := Nat.floor_le (by positivity)
  have hN₂le : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
  -- the divisor bound
  set F : ℕ := ⌊Cd * x ^ s⌋₊ with hFdef
  have hF : ∀ n, 0 < n → n < q → n.divisors.card ≤ F := by
    intro n hn hnq
    apply Nat.le_floor
    refine (LinnikPower.card_divisors_le hs0 hs1' n).trans ?_
    have : (n : ℝ) ^ s ≤ x ^ s :=
      Real.rpow_le_rpow (by positivity) (by rw [hxdef]; exact_mod_cast hnq.le) hs0.le
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hFR : (F : ℝ) ≤ Cd * x ^ s := Nat.floor_le (by positivity)
  have hdq : (q.divisors.card : ℝ) ≤ Cd * x ^ s := by
    refine (LinnikPower.card_divisors_le hs0 hs1' q).trans (le_of_eq ?_)
    rfl
  -- the products
  have hY₀ : 0 < x ^ e₀ := Real.rpow_pos_of_pos hx0 _
  have hpos₁ : ∀ y ∈ Y₁, 1 ≤ ∏ i, y i := by
    intro y hy
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have h := ht₁ i (y i) (Fintype.mem_piFinset.1 (hY₁ hy) i)
    intro h0; rw [h0, Nat.cast_zero] at h; linarith
  have hpos₂ : ∀ y ∈ Y₂, 1 ≤ ∏ i, y i := by
    intro y hy
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have h := ht₂ i (y i) (Fintype.mem_piFinset.1 (hY₂ hy) i)
    intro h0; rw [h0, Nat.cast_zero] at h; linarith
  -- the comparisons, with the cut-off itself off the family
  have hIb : ∀ j y₁ y₂, 0 ≤ (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) ∧
      (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) ≤ 1 := by
    intro j y₁ y₂
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨G_nonneg hθ0 hθΛ _, G_le_one _⟩
  have hIGb : ∀ j y₁ y₂, |(if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) -
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))| ≤
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) := by
    intro j y₁ y₂
    by_cases hy : y₁ ∈ Y₁ ∧ y₂ ∈ Y₂
    · rw [ite_eq_left hy]
      have hu : cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ :=
        (hΛ j y₁ hy.1 y₂ hy.2).trans (by rw [hΛdef]; linarith)
      exact SieveFamily.abs_ind_sub_G_le hθ0 (by linarith) hu (Pr j y₁ y₂) (hPr j y₁ y₂)
    · rw [ite_eq_right hy, sub_self, abs_zero]
      exact G_nonneg hθ0 (by linarith) _
  have hreg' : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) ≠ 0 →
      ((∏ i, y₁ i : ℕ) : ℝ) * fmax ≤ x ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ x ^ (L - b) ∧
        x ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) := by
    intro y₁ hy₁ y₂ hy₂ hne
    refine hreg y₁ hy₁ y₂ hy₂ fun j => ?_
    by_contra hj
    apply hne
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [ite_eq_left ⟨hy₁, hy₂⟩, ite_eq_right hj]
  have hη1 : θ ≤ 1 := by linarith
  have hfam := leaves_family (q := q) a' ha' (N₁ := N₁) (N₂ := N₂) hN hN₁ Y₁ Y₂ (fun y => ∏ i, y i)
    (fun y => ∏ i, y i) hpos₁ hpos₂
    (fun j y₁ y₂ => if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))
    (fun _ => G θ Λ) (fun _ u => G θ θ (u + θ)) (fun _ => hGc) (fun _ => hGi) (fun _ => hGf) (fun _ => hMc)
    (fun _ => hMi) (fun _ => hMfr) (fun j y₁ => cc j + ∑ i, e₁ j i * Real.log (y₁ i))
    (fun j y₂ => ∑ i, e₂ j i * Real.log (y₂ i)) hIb (fun _ u => ⟨G_nonneg hθ0 hθΛ u, G_le_one u⟩) hIGb
    R S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂ hfm₁ hfm₂ (Mf := x ^ c₁) (M₂ := x ^ c₁) (by positivity) hMf₁ hMf₂ hM₂
    hF (ρ := 1 + θ) (η := θ) (by linarith) hθ0 hη1 hr1 (X₁ := x ^ (L - 1 - a)) (X₂ := x ^ (L - b))
    (X₃ := x ^ (L - 1 - δ')) (by positivity) (by positivity) hreg'
  beta_reduce at hfam
  rw [← hxdef] at hfam
  -- on the family, the weights are the comparisons'
  have hcI : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) =
      ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) :=
    fun y₁ hy₁ y₂ hy₂ => Finset.prod_congr rfl fun j _ => ite_eq_left ⟨hy₁, hy₂⟩
  have hc0 : ∀ y₁ y₂, 0 ≤ ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) := fun y₁ y₂ =>
    Finset.prod_nonneg fun j _ => by split_ifs <;> norm_num
  have hc1 : ∀ y₁ y₂, ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) ≤ 1 := fun y₁ y₂ =>
    Finset.prod_le_one₀ (fun j _ => by split_ifs <;> norm_num) fun j _ => by split_ifs <;> norm_num
  set K := K₁ + K₂ with hKdef
  have hB0 : 0 ≤ B := by linarith
  have hBK : 1 ≤ B ^ K := one_le_pow₀ hB
  have hCd0 : 0 ≤ Cd := by linarith
  -- the exponents
  have hsa' : s * (2 * (J₀ + 6)) ≤ a - δ' := (le_div_iff₀ (by positivity)).1 hsa
  have hs1'' : s * (4 * (J₀ + 6)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hs1
  have hJs : 0 ≤ (J₀ : ℝ) * s := by positivity
  have hs24 : s ≤ 1 / 24 := by linarith
  -- the leaves' weights: `Σ c/d ≤ B^K` and `Σ c ≤ x^{L−1/2}B^K`
  have hSd : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
      (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ B ^ K :=
    box_weight_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hB0 hB₁ hB₂ _ hc1
  have hSc : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) ≤ x ^ (L - 1 / 2) * B ^ K := by
    calc ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0))
        ≤ ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, x ^ (L - 1 / 2) * ((∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun y₁ hy₁ => Finset.sum_le_sum fun y₂ hy₂ => ?_
          have hd0 : (0 : ℝ) < (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) := by
            have := hpos₁ y₁ hy₁; have := hpos₂ y₂ hy₂; positivity
          by_cases hall : ∀ j, Pr j y₁ y₂
          · obtain ⟨h1, h2, -⟩ := hreg y₁ hy₁ y₂ hy₂ hall
            have hd : (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ x ^ (L - 1 / 2) := by
              have hp₁ : (1 : ℝ) ≤ ((∏ i, y₁ i : ℕ) : ℝ) := by exact_mod_cast hpos₁ y₁ hy₁
              have h1' : ((∏ i, y₁ i : ℕ) : ℝ) ≤ x ^ (L - 1 - a) :=
                le_trans (le_mul_of_one_le_right (by positivity) hfmax) h1
              have h2' : ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ x ^ (L - b) :=
                le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hfmax)
                  (by positivity)) h2
              have hsq : ((((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ)) ^ 2 ≤ (x ^ (L - 1 / 2)) ^ 2 := by
                rw [Nat.cast_mul]
                calc (((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) ^ 2 =
                    ((∏ i, y₁ i : ℕ) : ℝ) * (((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2) := by ring
                  _ ≤ x ^ (L - 1 - a) * x ^ (L - b) := mul_le_mul h1' h2' (by positivity) (by positivity)
                  _ ≤ (x ^ (L - 1 / 2)) ^ 2 := by
                      rw [← Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
                      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
              exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
            rw [mul_div_assoc', le_div_iff₀ hd0]
            exact (mul_le_mul_of_nonneg_left hd (hc0 y₁ y₂)).trans_eq (mul_comm _ _)
          · have : (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) = 0 := by
              obtain ⟨j, hj⟩ := not_forall.1 hall
              exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
            rw [this, zero_div, mul_zero]
      _ = x ^ (L - 1 / 2) * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y₁ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ x ^ (L - 1 / 2) * B ^ K := mul_le_mul_of_nonneg_left hSd (by positivity)
  -- the target power `P = x^{L−3s/4}/φ(q)`
  set P : ℝ := x ^ (L - 3 * s / 4) / (q.totient : ℝ) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hPa : ∀ α β : ℝ, α + β ≤ L - 3 * s / 4 → x ^ α * x ^ β / (q.totient : ℝ) ≤ P := by
    intro α β h
    rw [hP, ← Real.rpow_add hx0]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 h) hφ0.le
  have hPb : ∀ α β : ℝ, α + β ≤ L - 3 * s / 4 → x ^ α * x ^ β / x ≤ P := fun α β h =>
    (div_le_div_of_nonneg_left (by positivity) hφ0 hφx).trans (hPa α β h)
  have hlg : 1 ≤ Real.log x ^ 2 := by
    have : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    exact one_le_pow₀ this
  -- the three parts against `x^{L−s/4}/φ(q)`
  have key : ∀ A₀ Bb Cc M₀ : ℝ, A₀ ≤ M₀ + (15 + 2 * Cd) * B ^ K * P →
      Bb ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * (√(816 * Cd) + r' + 4 * Cd) * Real.log x ^ 2 * P →
      Cc ≤ 416 * J₀ * B ^ K * P → A₀ + Bb + Cc ≤ M₀ + (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by
    intro A₀ Bb Cc M₀ hA hBb hCc
    have hfin' : Ctot * Real.log x ^ 2 * P ≤ (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by
      calc Ctot * Real.log x ^ 2 * P = Ctot * Real.log x ^ 2 * x ^ (L - 3 * s / 4) / q.totient := by
            rw [hP]; ring
        _ ≤ x ^ (L - s / 4) / q.totient := div_le_div_of_nonneg_right hfin hφ0.le
        _ = (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by ring
    rw [hCtot] at hfin'
    have h1 := mul_le_mul_of_nonneg_left hlg (by positivity : (0 : ℝ) ≤ (15 + 2 * Cd) * B ^ K * P)
    have h3 := mul_le_mul_of_nonneg_left hlg (by positivity : (0 : ℝ) ≤ 416 * J₀ * B ^ K * P)
    linarith only [hA, hBb, hCc, hfin', h1, h3]
  -- the near-boundary pieces, per comparison
  have hj₁ : ∀ j : Fin J, ∑ z ∈ Y₁ ×ˢ S₁, ∑ y₂ ∈ Y₂, (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) * |l₁ z.2| *
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (z.1 i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) /
      (((∏ i, z.1 i) * f₁ z.2 * ∏ i, y₂ i : ℕ) : ℝ) ≤
      (1 + θ) * (1 + θ) ^ 2 * N₂ * (∑ σ ∈ S₁, |l₁ σ| / f₁ σ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)) := by
    intro j
    refine (le_of_eq (nb_regroup Y₁ Y₂ S₁ (fun y => ∏ i, y i) (fun y => ∏ i, y i) f₁ l₁
      ((1 + θ) * (1 + θ) ^ 2 * N₂)
      (fun y₁ y₂ => G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ)))).trans ?_
    exact mul_le_mul_of_nonneg_left (pivot_two_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hY₀ ht₁ ht₂ hB0 hB₁ hB₂ hθ0 hθ9 (cc j)
      (e₁ j) (e₂ j) (hpiv j)) (by positivity)
  have hj₂ : ∀ j : Fin J, ∑ z ∈ Y₁ ×ˢ S₂, ∑ y₂ ∈ Y₂, (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) * |l₂ z.2| *
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (z.1 i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) /
      (((∏ i, z.1 i) * f₂ z.2 * ∏ i, y₂ i : ℕ) : ℝ) ≤
      (1 + θ) * (1 + θ) ^ 2 * N₂ * (∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)) := by
    intro j
    refine (le_of_eq (nb_regroup Y₁ Y₂ S₂ (fun y => ∏ i, y i) (fun y => ∏ i, y i) f₂ l₂
      ((1 + θ) * (1 + θ) ^ 2 * N₂)
      (fun y₁ y₂ => G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ)))).trans ?_
    exact mul_le_mul_of_nonneg_left (pivot_two_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hY₀ ht₁ ht₂ hB0 hB₁ hB₂ hθ0 hθ9 (cc j)
      (e₁ j) (e₂ j) (hpiv j)) (by positivity)
  have hCθ : (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) ≤ 16 * x ^ L := by
    calc (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) ≤ 2 * 2 ^ 2 * (2 * x ^ L) := by gcongr <;> linarith
      _ = 16 * x ^ L := by ring
  have hPv : (12 * θ + 1 / x ^ e₀) * B ^ (K - 1) ≤ 13 * θ * B ^ K := by
    have h1 : 1 / x ^ e₀ ≤ θ := by
      calc 1 / x ^ e₀ ≤ 1 / x ^ s := one_div_le_one_div_of_le (by positivity)
            (Real.rpow_le_rpow_of_exponent_le hx1 hse)
        _ = θ := by rw [hθdef, Real.rpow_neg hx0.le, one_div]
    exact mul_le_mul (by linarith) (pow_le_pow_right₀ hB (Nat.sub_le K 1)) (by positivity) (by positivity)
  have hLcθ : x ^ L * x ^ c₁ * θ / (q.totient : ℝ) ≤ P := by
    rw [← Real.rpow_add hx0]
    exact hPa (L + c₁) (-s) (by linarith)
  have hJ' : (J : ℝ) ≤ J₀ := by exact_mod_cast hJ
  -- the transition term `Θ`
  have h30 : 0 ≤ (1 + θ) ^ 2 - 1 := by nlinarith
  have hΘ0 : 0 ≤ ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) + 2 * θ * N₁ :=
    add_nonneg (mul_nonneg (by positivity) h30) (by positivity)
  have hΘ : ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) + 2 * θ * N₁ ≤ 11 * x ^ (L - s) := by
    have h3 : (1 + θ) ^ 2 - 1 ≤ 3 * θ := by nlinarith
    have h4 : ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) ≤ 3 * x ^ L * (3 * θ) :=
      mul_le_mul (by linarith) h3 h30 (by positivity)
    have h5 : 2 * θ * (N₁ : ℝ) ≤ 2 * θ * x ^ L := by gcongr
    have hθL : θ * x ^ L = x ^ (L - s) := by
      rw [hθdef, ← Real.rpow_add hx0]; congr 1; ring
    linarith
  -- the bilinear part's ingredients
  have hk₁ : ((blk (1 + θ) ⌊x ^ (L - 1 - a)⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L * x ^ s * Real.log x := by
    push_cast
    exact blk_floor_le hx3 hs0 hL.le (Real.one_le_rpow hx1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hk₂ : ((blk (1 + θ) ⌊√(x ^ (L - b))⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L * x ^ s * Real.log x := by
    push_cast
    have h1 : 1 ≤ x ^ (L - b) := Real.one_le_rpow hx1 (by linarith)
    exact blk_floor_le hx3 hs0 hL.le (Real.one_le_sqrt.2 h1)
      ((Real.sqrt_le_self_iff.2 (Or.inr h1)).trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)))
  have hMx1 : 1 ≤ Cm * x ^ s := by nlinarith
  have hFN : (∏ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ)) t‖) +
      ∑ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) t‖ ≤ (J₀ + 1) * (Cm * x ^ s) ^ J₀ :=
    masses_le hJ _ _ hMx1 (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => hGm.trans hmB1)
      (fun j => hMm.trans hmB2)
  have hFN0 : 0 ≤ (∏ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ)) t‖) +
      ∑ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) t‖ :=
    add_nonneg (Finset.prod_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _)
  have hU : bdU q (1 + θ) θ N₁ N₂ r F (x ^ (L - 1 - a)) (x ^ (L - b)) (x ^ (L - 1 - δ')) ≤
      √(816 * Cd) * x ^ (L - 1 - (a - δ' - s) / 2) + r' * x ^ (L - 2) +
        4 * Cd * x ^ (L - 1 / 2 + s) / (q.totient : ℝ) :=
    bdU_le_pow q hx3 hL hδ' (by linarith) haL hb hs0 hsb hr4 hFR hdq
  have hU0 : 0 ≤ bdU q (1 + θ) θ N₁ N₂ r F (x ^ (L - 1 - a)) (x ^ (L - b)) (x ^ (L - 1 - δ')) :=
    bdU_nonneg q (by positivity) hθ0 N₁ N₂ r F (by positivity)
  have e1 : (J₀ + 2) * s + 2 * c₁ + (L - 1 - (a - δ' - s) / 2) ≤ L - 3 * s / 4 - 1 := by linarith
  have e2 : (J₀ + 2) * s + 2 * c₁ + (L - 2) ≤ L - 3 * s / 4 - 1 := by linarith
  have e3 : (J₀ + 2) * s + 2 * c₁ + (L - 1 / 2 + s) ≤ L - 3 * s / 4 := by linarith
  -- assemble
  have hcI' : ∀ g : (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → ℝ,
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
        G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) * g y₁ y₂ =
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) * g y₁ y₂ :=
    fun g => Finset.sum_congr rfl fun y₁ hy₁ => Finset.sum_congr rfl fun y₂ hy₂ => by rw [hcI y₁ hy₁ y₂ hy₂]
  rw [hcI', hcI'] at hfam
  refine hfam.trans (key _ _ _ _ ?_ ?_ ?_)
  · -- the main term and the transition
    rw [split_main, add_assoc]
    refine add_le_add le_rfl ((add_le_add ?_ ?_).trans (le_of_eq (by ring :
      11 * B ^ K * P + (4 + 2 * Cd) * B ^ K * P = (15 + 2 * Cd) * B ^ K * P)))
    · calc _ ≤ x ^ c₁ * (11 * x ^ (L - s)) / x * B ^ K := by gcongr
        _ = 11 * B ^ K * (x ^ c₁ * x ^ (L - s) / x) := by ring
        _ ≤ 11 * B ^ K * P := mul_le_mul_of_nonneg_left (hPb _ _ (by linarith)) (by positivity)
    · calc _ ≤ (4 * x ^ (1 / 4 : ℝ) / x + 2 * x ^ (1 / 4 : ℝ) * (Cd * x ^ s / q.totient)) *
              (x ^ (L - 1 / 2) * B ^ K) := by
            gcongr
        _ = 4 * B ^ K * (x ^ (1 / 4 : ℝ) * x ^ (L - 1 / 2) / x) +
            2 * Cd * B ^ K * (x ^ ((1 / 4 : ℝ) + s) * x ^ (L - 1 / 2) / q.totient) := by
            rw [Real.rpow_add hx0]; ring
        _ ≤ 4 * B ^ K * P + 2 * Cd * B ^ K * P :=
            add_le_add (mul_le_mul_of_nonneg_left (hPb _ _ (by linarith)) (by positivity))
              (mul_le_mul_of_nonneg_left (hPa _ _ (by linarith)) (by positivity))
        _ = (4 + 2 * Cd) * B ^ K * P := by ring
  · -- the bilinear part
    rw [Nat.cast_mul]
    refine (bil_le hx3 hφ0 hφx (by linarith) (by positivity) hk₁ (by positivity) hk₂ hFN0 hFN (by positivity)
      le_rfl (by positivity) le_rfl hU0 hU hCd0 hr'0 (by linarith) e1 e2 e3).trans (le_of_eq ?_)
    rw [hP]; ring
  · -- the near-boundary masses
    refine le_trans (add_le_add
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj₁ j) (by positivity))
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj₂ j) (by positivity))) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hprod : (J : ℝ) * ((1 + θ) * (1 + θ) ^ 2 * N₂ * ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) *
        ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)))) ≤ J₀ * (16 * x ^ L * (x ^ c₁ * (13 * θ * B ^ K))) :=
      mul_le_mul hJ' (mul_le_mul hCθ (mul_le_mul hV hPv (by positivity) (by positivity)) (by positivity)
        (by positivity)) (by positivity) (by positivity)
    calc _ = 2 * (q.totient : ℝ)⁻¹ * ((J : ℝ) * ((1 + θ) * (1 + θ) ^ 2 * N₂ *
          ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1))))) := by
          ring
      _ ≤ 2 * (q.totient : ℝ)⁻¹ * (J₀ * (16 * x ^ L * (x ^ c₁ * (13 * θ * B ^ K)))) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 416 * J₀ * B ^ K * (x ^ L * x ^ c₁ * θ / q.totient) := by ring
      _ ≤ 416 * J₀ * B ^ K * P := mul_le_mul_of_nonneg_left hLcθ (by positivity)

end SieveTypeIBAsym
