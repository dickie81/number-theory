/-
# The density exponent `30/13` for `ζ`, and primes in short intervals for `θ > 17/30`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `ε > 0`, `N(σ, T) ≪ T^{(30/13 + ε)(1−σ)}(log T)^{12}` for `1/2 ≤ σ ≤ 1` and `T ≥ 2`
(`densityXi_thirty_thirteenths`), Guth and Maynard's exponent. For every `θ > 17/30` every interval `(y, y + y^θ]`
with `y` large holds a prime (`short_primes_seventeen_thirtieths`), and for every `θ > 2/15` there is `δ > 0` such
that the `y ∈ [X, 2X]` with no prime in `(y, y + y^θ]` have measure at most `X^{1−δ}`
(`almost_all_short_primes_two_fifteenths`).

* `densityXi_thirty_thirteenths`: the trivial count below `σ = 17/30`, where `(30/13)(1 − σ) ≥ 1`;
  `ZetaGMIngham.nx_ingham13` on `[17/30, 7/10 + η]`; Guth and Maynard's large values (`ZetaGMWin.nx_gm`) on
  `[7/10 + η, 4/5]`; `ZetaGMHux.nx_gmh` on `[4/5, 11/12]`; and no zero above `11/12`
  (`Eis.ne_zero_of_re_gt_eleven_twelfths`), at `η = min(ε, 1)/100`.
* `short_primes_seventeen_thirtieths`: `ZetaHuxley.short_primes_of_density_eps_hp`, `1 − 13/30 = 17/30`.
* `almost_all_short_primes_two_fifteenths`: `AlmostAll.almost_all_of_density`, `1 − 2/(30/13) = 2/15`.

The file imports `ZetaGMWin.lean`, `ZetaGMIngham.lean`, `ZetaGMHux.lean` and `AlmostAllPrimes.lean`.
-/
import ZetaGMWin
import ZetaGMIngham
import ZetaGMHux
import AlmostAllPrimes

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace ZetaGMDensity

open ShortWeil PsiOmega WeilForm WeilTest DirMean Finset InghamDensity ZetaIngham ZetaHuxley

/-- **Zero density at Guth and Maynard's exponent `30/13`**: `N(σ, T) ≪ T^{(30/13 + ε)(1−σ)}(log T)^{12}` for every
`ε > 0`: the trivial count below `σ = 17/30`, `ZetaGMIngham.nx_ingham13` on `[17/30, 7/10 + η]`, `ZetaGMWin.nx_gm`
on `[7/10 + η, 4/5]`, `ZetaGMHux.nx_gmh` on `[4/5, 11/12]`, and no zero above `11/12`, at `η = min(ε, 1)/100`. -/
theorem densityXi_thirty_thirteenths {ε : ℝ} (hε : 0 < ε) : DensityXi (30 / 13 + ε) 12 := by
  classical
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set η := ε₁ / 100 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 100 := by rw [hη]; linarith
  set ε₂ := min ε (1 / 200) / 156 with hε₂
  have hm0 : 0 < min ε (1 / 200) := lt_min hε (by norm_num)
  have hm1 : min ε (1 / 200) ≤ 1 / 200 := min_le_right _ _
  have hmε : min ε (1 / 200) ≤ ε := min_le_left _ _
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂1 : ε₂ ≤ 1 / 200 := by rw [hε₂]; linarith
  have hε₂ε : 156 * ε₂ ≤ ε := by rw [hε₂]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := ZetaGMIngham.nx_ingham13 hε₁0 hε₁1 hη0.le (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := ZetaGMWin.nx_gm hη0 hη1
  obtain ⟨C₃, hC₃0, hC₃⟩ := ZetaGMHux.nx_gmh hε₂0 hε₂1
  set Ca : ℝ := 2 * Kc * 2 ^ 11 with hCa
  have hKc := Kc_nonneg
  have hCa0 : 0 ≤ Ca := by positivity
  refine ⟨Ca + C₁ + C₂ + C₃, by positivity, fun T hT w hw0 hw1 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set e := (30 / 13 + ε) * (1 / 2 - w) with he
  have he0 : 0 ≤ e := by rw [he]; nlinarith
  have hTe : 1 ≤ T ^ e := Real.one_le_rpow hT1 he0
  have hlog12 : 0 ≤ Real.log T ^ 12 := by have := Real.log_nonneg hT1; positivity
  have e12 : Real.log T ^ (12 : ℝ) = Real.log T ^ (12 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [e12]
  have hw' : w = 1 / 2 + w - 1 / 2 := by ring
  have he' : e = (30 / 13 + ε) * (1 - (1 / 2 + w)) := by rw [he]; ring
  have hTeC : ∀ C : ℝ, 0 ≤ C → C ≤ Ca + C₁ + C₂ + C₃ → C * T ^ e * Real.log T ^ 12 ≤
      (Ca + C₁ + C₂ + C₃) * T ^ e * Real.log T ^ 12 := fun C _ hC => by gcongr
  rcases lt_or_ge w (1 / 15) with hw | hw
  · -- `σ < 17/30`: the trivial count
    rw [NX_eq_card]
    have h1 : (((finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im|).card : ℝ) ≤ (T + 1) * Kloc T :=
      (Nat.cast_le.2 (card_filter_le _ _)).trans (card_re_le hT0.le)
    have h2 : Kloc T ≤ Kc * Real.log T :=
      (Kloc_mono (by linarith) (by linarith : T ≤ 2 * T + 1)).trans (Kloc_le hT)
    have h3 : T ≤ T ^ e := by
      calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ e := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [he]; nlinarith)
    have h4 := log_le_pow12 hT
    have h5 : 0 ≤ Kc * Real.log T := mul_nonneg hKc (Real.log_nonneg hT1)
    calc (((finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im|).card : ℝ) ≤ (T + 1) * Kloc T := h1
      _ ≤ (2 * T) * (Kc * Real.log T) := by
          gcongr
          · exact Kloc_nonneg hT0.le
          · linarith
      _ ≤ (2 * T ^ e) * (Kc * (2 ^ 11 * Real.log T ^ 12)) := by gcongr
      _ = Ca * T ^ e * Real.log T ^ 12 := by rw [hCa]; ring
      _ ≤ (Ca + C₁ + C₂ + C₃) * T ^ e * Real.log T ^ 12 := hTeC Ca hCa0 (by linarith)
  rcases le_or_gt w (1 / 5 + η) with hw2 | hw2
  · -- `17/30 ≤ σ ≤ 7/10 + η`: Ingham at `c = 1/13`
    have h := hC₁ T hT (1 / 2 + w) (by linarith) (by linarith)
    rw [← hw'] at h
    have hexp : 30 / 13 * (1 - (1 / 2 + w)) + η + ε₁ / 4 ≤ e := by
      rw [he']
      have hσ : 29 / 100 ≤ 1 - (1 / 2 + w) := by linarith
      have h1 := mul_le_mul_of_nonneg_left hσ hε.le
      nlinarith
    calc (NX w T : ℝ) ≤ C₁ * T ^ (30 / 13 * (1 - (1 / 2 + w)) + η + ε₁ / 4) * Real.log T ^ 12 := h
      _ ≤ C₁ * T ^ e * Real.log T ^ 12 := by gcongr
      _ ≤ (Ca + C₁ + C₂ + C₃) * T ^ e * Real.log T ^ 12 := hTeC C₁ hC₁0 (by linarith)
  rcases le_or_gt w (3 / 10) with hw3 | hw3
  · -- `7/10 + η ≤ σ ≤ 4/5`: Guth and Maynard
    have h := hC₂ T hT (1 / 2 + w) (by linarith) (by linarith)
    rw [← hw'] at h
    have hexp : 30 / 13 * (1 - (1 / 2 + w)) + 9 * η ≤ e := by
      rw [he']
      have hσ : 1 / 5 ≤ 1 - (1 / 2 + w) := by linarith
      have h1 := mul_le_mul_of_nonneg_left hσ hε.le
      nlinarith
    calc (NX w T : ℝ) ≤ C₂ * T ^ (30 / 13 * (1 - (1 / 2 + w)) + 9 * η) * Real.log T ^ 12 := h
      _ ≤ C₂ * T ^ e * Real.log T ^ 12 := by gcongr
      _ ≤ (Ca + C₁ + C₂ + C₃) * T ^ e * Real.log T ^ 12 := hTeC C₂ hC₂0 (by linarith)
  rcases le_or_gt w (5 / 12) with hw4 | hw4
  · -- `4/5 ≤ σ ≤ 11/12`: Huxley's argument at the exponent `30/13`
    have h := hC₃ T hT (1 / 2 + w) (by linarith) (by linarith)
    rw [← hw'] at h
    have hexp : (30 / 13 + 156 * ε₂) * (1 - (1 / 2 + w)) ≤ e := by rw [he']; nlinarith
    calc (NX w T : ℝ) ≤ C₃ * T ^ ((30 / 13 + 156 * ε₂) * (1 - (1 / 2 + w))) * Real.log T ^ 12 := h
      _ ≤ C₃ * T ^ e * Real.log T ^ 12 := by gcongr
      _ ≤ (Ca + C₁ + C₂ + C₃) * T ^ e * Real.log T ^ 12 := hTeC C₃ hC₃0 (by linarith)
  · -- `σ > 11/12`: no zeros
    have hempty : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hwi
      have hβ : 11 / 12 < ((βs i : ℂ) + (γs i : ℝ) * I).re := by simp [βs]; linarith
      exact (Eis.ne_zero_of_re_gt_eleven_twelfths hβ).1 (DetectCore.zeta_βsγs i)
    have hzero : NX w T = 0 := by unfold NX; rw [hempty, Set.ncard_empty]
    rw [hzero, Nat.cast_zero]
    positivity

/-- **Primes in short intervals for every `θ > 17/30`**: from `densityXi_thirty_thirteenths` (`1 − 13/30 = 17/30`),
with the zero-free region of the half-plane (`ZetaHuxley.short_primes_of_density_eps_hp`). -/
theorem short_primes_seventeen_thirtieths {θ : ℝ} (hθ : 17 / 30 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ :=
  short_primes_of_density_eps_hp (A₀ := 30 / 13) (by norm_num)
    (fun ε hε => ⟨12, densityXi_thirty_thirteenths hε⟩) (by linarith) (by norm_num; linarith)

/-- **Primes in almost all short intervals for every `θ > 2/15`**: `AlmostAll.almost_all_of_density` with
`densityXi_thirty_thirteenths`, `1 − 2/(30/13) = 2/15`. -/
theorem almost_all_short_primes_two_fifteenths {θ : ℝ} (hθ : 2 / 15 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      volume {y | y ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
        ≤ ENNReal.ofReal (X ^ (1 - δ)) := by
  set θ₁ := min θ 1 with hθ₁
  have hθ₁0 : 0 < θ₁ := lt_min (by linarith) one_pos
  have hθ₁2 : 1 - 2 / (30 / 13 : ℝ) < θ₁ := lt_min (by norm_num; linarith) (by norm_num)
  obtain ⟨δ, hδ, h⟩ := AlmostAll.almost_all_of_density (A₀ := 30 / 13) (by norm_num)
    (fun ε hε => ⟨12, densityXi_thirty_thirteenths hε⟩) hθ₁0 (min_le_right _ _) hθ₁2
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  refine le_trans (measure_mono ?_) hX
  rintro y ⟨hy, hno⟩
  refine ⟨hy, fun ⟨p, hp, h1, h2⟩ => hno ⟨p, hp, h1, h2.trans ?_⟩⟩
  have hy1 : 1 ≤ y := le_trans hX1 hy.1
  have := Real.rpow_le_rpow_of_exponent_le hy1 (min_le_left θ 1)
  linarith

end ZetaGMDensity

#print axioms ZetaGMDensity.densityXi_thirty_thirteenths
#print axioms ZetaGMDensity.short_primes_seventeen_thirtieths
#print axioms ZetaGMDensity.almost_all_short_primes_two_fifteenths
