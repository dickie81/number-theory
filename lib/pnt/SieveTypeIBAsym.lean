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

end SieveTypeIBAsym
