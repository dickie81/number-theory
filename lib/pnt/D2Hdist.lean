import Mathlib
import D2Dist
import NoAtoms
import D2Density

/-!
# `hdist` at every `t`, and the d₂ < d₁ density — CONDITIONAL on the half-plane

**CONDITIONAL.** Everything here uses `D2Dist.dist_pos` / `D2Dist.dist_neg`, hence the tail identity
`GSTail.logDeriv_one_tail` and the half-plane `Re s > 11/12` (see `formalisations/openai-half-plane.md`). Lean checks it
with the standard axioms only, but it must be cited as conditional on that input.

* `D2Hdist.hdist_pos`, `D2Hdist.hdist_neg` (CONDITIONAL): for every `t`, the proportion of fundamental discriminants
  `1 < ±D ≤ x` with `Re L′/L(1, χ_D) > t` tends to `ν (Ioi t)`, `ν` the law of the random model. Weak convergence
  plus `NoAtoms.ν_singleton` (the frontier `{t}` of `Ioi t` is `ν`-null).
* `D2Hdist.d2_density_pos`, `D2Hdist.d2_density_neg` (CONDITIONAL): `D2Density.d2_density_log` with `hdist`
  discharged; the hypotheses `hK1`, `hpos`, `hB` remain.

See `formalisations/d2-density.md`.
-/

namespace D2Hdist
open Finset Filter Topology MeasureTheory D2Dist D2Density GSFund
open scoped ENNReal

section Gen
variable (F : ℕ → Prop) [DecidablePred F] (ℓ : ℕ → ℝ) (ι : ℕ → ℤ) (back : ℤ → ℕ) (hb : ∀ d, back (ι d) = d)

/-- The discriminants up to `x`, as integers. -/
noncomputable def Sx (x : ℕ) : Finset ℤ := (St F x).image ι

include hb in
theorem card_Sx (x : ℕ) : (Sx F ι x).card = (St F x).card :=
  card_image_of_injective _ fun a b (h : ι a = ι b) => by have := congrArg back h; rwa [hb, hb] at this

include hb in
theorem prop_eq {x : ℕ} (h : (St F x).Nonempty) (t : ℝ) :
    prop (Sx F ι x) (fun D => t < ℓ (back D)) = ((emp F ℓ x : Measure ℝ) (Set.Ioi t)).toReal := by
  rw [coe_emp, ite_eq_left_of_eq_true _ _ (eq_true h), empM, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ measurableSet_Ioi, smul_eq_mul]
  have hfil : ((Sx F ι x).filter fun D => t < ℓ (back D)).card = ((St F x).filter fun d => t < ℓ d).card := by
    rw [Sx, filter_image]
    simp only [hb]
    refine card_image_of_injective _ fun a b (h : ι a = ι b) => by have := congrArg back h; rwa [hb, hb] at this
  have hind : ∑ d ∈ St F x, (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) (ℓ d) = ((St F x).filter fun d => t < ℓ d).card := by
    rw [← sum_boole]; exact sum_congr rfl fun d _ => by simp [Set.indicator]
  rw [hind, prop, hfil, card_Sx F ι back hb, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_inv_mul]

include hb in
/-- **`hdist` from weak convergence and no atoms.** -/
theorem hdist_of (κ : ℝ) (hκ : 0 < κ)
    (hmom0 : Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ 0 else 0)) / x) atTop (𝓝 κ))
    (hw : Tendsto (emp F ℓ) atTop (𝓝 RandModel.ν)) (t : ℝ) :
    Tendsto (fun x => prop (Sx F ι x) (fun D => t < ℓ (back D))) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi t)).toReal) := by
  have hfr : RandModel.ν (frontier (Set.Ioi t)) = 0 := by
    rw [frontier_Ioi]
    have := NoAtoms.ν_singleton t
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
    exact_mod_cast this
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hw hfr
  have h' := (NNReal.continuous_coe.tendsto _).comp h
  simp only [Function.comp_def] at h'
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  refine h'.congr' ?_
  have hcard : Tendsto (fun x : ℕ => ((St F x).card : ℝ) / x) atTop (𝓝 κ) := by
    refine hmom0.congr fun x => ?_
    simp only [pow_zero]; rw [St, sum_boole]
  filter_upwards [hcard.eventually (lt_mem_nhds hκ)] with x hx
  have hne : (St F x).Nonempty := by
    rw [← Finset.card_pos]; by_contra hc; simp_all
  rw [prop_eq F ℓ ι back hb hne, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]

include hb in
theorem card_tendsto (κ : ℝ) (hκ : 0 < κ)
    (hmom0 : Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ 0 else 0)) / x) atTop (𝓝 κ)) :
    Tendsto (fun x => ((Sx F ι x).card : ℝ)) atTop atTop := by
  have hcard : Tendsto (fun x : ℕ => ((St F x).card : ℝ) / x) atTop (𝓝 κ) := by
    refine hmom0.congr fun x => ?_
    simp only [pow_zero]; rw [St, sum_boole]
  refine (hcard.pos_mul_atTop hκ tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [card_Sx F ι back hb]; field_simp

end Gen

theorem mν_zero : mν 0 = 1 := by simp [mν]

theorem mom0_pos : Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if fundPos d ∧ 1 < d then lpos d ^ 0 else 0)) / x)
    atTop (𝓝 D2Dist.κ) := by simpa [mν_zero] using moments_pos 0

theorem mom0_neg : Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if fundNeg d ∧ 1 < d then lneg d ^ 0 else 0)) / x)
    atTop (𝓝 D2Dist.κ) := by simpa [mν_zero] using moments_neg 0

/-- The positive fundamental discriminants `1 < D ≤ x`. -/
noncomputable def Spos (x : ℕ) : Finset ℤ := Sx fundPos (fun d : ℕ => (d : ℤ)) x

/-- The negative fundamental discriminants `-x ≤ D < -1`. -/
noncomputable def Sneg (x : ℕ) : Finset ℤ := Sx fundNeg (fun d : ℕ => -(d : ℤ)) x

/-- The positive fundamental discriminants `D > 1`. -/
def Apos (D : ℤ) : Prop := 1 < D ∧ fundPos D.toNat

/-- The negative fundamental discriminants `D < -1`. -/
def Aneg (D : ℤ) : Prop := D < -1 ∧ fundNeg (-D).toNat

theorem Spos_sub (x : ℕ) : ∀ D ∈ Spos x, Apos D := by
  intro D hD
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hD
  obtain ⟨-, hF, h1⟩ := Finset.mem_filter.1 hd
  exact ⟨by exact_mod_cast h1, by simpa using hF⟩

theorem Sneg_sub (x : ℕ) : ∀ D ∈ Sneg x, Aneg D := by
  intro D hD
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hD
  obtain ⟨-, hF, h1⟩ := Finset.mem_filter.1 hd
  exact ⟨by omega, by simpa using hF⟩

/-- `Re L′/L(1, χ_D)` for `D > 1` fundamental. -/
noncomputable def ℓpos (D : ℤ) : ℝ := lpos D.toNat

/-- `Re L′/L(1, χ_D)` for `D < -1` fundamental. -/
noncomputable def ℓneg (D : ℤ) : ℝ := lneg (-D).toNat

/-- **CONDITIONAL (half-plane). `hdist` for `D > 0`, at every `t`.** -/
theorem hdist_pos (t : ℝ) : Tendsto (fun x => prop (Spos x) (fun D => t < ℓpos D)) atTop
    (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi t)).toReal) :=
  hdist_of fundPos lpos _ Int.toNat (fun d => by simp) D2Dist.κ κ_pos mom0_pos D2Dist.dist_pos t

/-- **CONDITIONAL (half-plane). `hdist` for `D < 0`, at every `t`.** -/
theorem hdist_neg (t : ℝ) : Tendsto (fun x => prop (Sneg x) (fun D => t < ℓneg D)) atTop
    (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi t)).toReal) :=
  hdist_of fundNeg lneg _ (fun D => (-D).toNat) (fun d => by simp) D2Dist.κ κ_pos mom0_neg D2Dist.dist_neg t

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D > 0`.** `D2Density.d2_density_log` with `hdist`
discharged: the proportion of `D` with `d₂/d₁ < 1` tends to `ν (Ioi (-2c))`. -/
theorem d2_density_pos (K1 K2 : ℤ → ℝ) (c κ : ℝ)
    (hK1 : ∀ D, Apos D → K1 D = (Real.log (|(D:ℝ)| / Real.pi) + κ) + 2 * ℓpos D)
    (hpos : ∀ D, Apos D → 0 < K1 D) (hB : ∀ D, Apos D → K2 D = √2 * (K1 D / 2 + c + ℓpos D / 2)) :
    Tendsto (fun x => prop (Spos x) (fun D => 2 * (1 - K2 D ^ 2 / K1 D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * c))).toReal) :=
  d2_density_log Spos (card_tendsto fundPos lpos _ Int.toNat (fun d => by simp) D2Dist.κ κ_pos mom0_pos)
    Apos Spos_sub ℓpos K1 K2 c κ _ hK1 hpos hB hdist_pos

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D < 0`.** -/
theorem d2_density_neg (K1 K2 : ℤ → ℝ) (c κ : ℝ)
    (hK1 : ∀ D, Aneg D → K1 D = (Real.log (|(D:ℝ)| / Real.pi) + κ) + 2 * ℓneg D)
    (hpos : ∀ D, Aneg D → 0 < K1 D) (hB : ∀ D, Aneg D → K2 D = √2 * (K1 D / 2 + c + ℓneg D / 2)) :
    Tendsto (fun x => prop (Sneg x) (fun D => 2 * (1 - K2 D ^ 2 / K1 D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * c))).toReal) :=
  d2_density_log Sneg (card_tendsto fundNeg lneg _ (fun D => (-D).toNat) (fun d => by simp) D2Dist.κ κ_pos mom0_neg)
    Aneg Sneg_sub ℓneg K1 K2 c κ _ hK1 hpos hB hdist_neg

end D2Hdist
