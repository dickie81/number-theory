/-
# The strip bound for `ζ` from a critical-line bound and a zero-free half-plane

Plain statement. If `ζ(s) ≠ 0` on `Re s > θ`, with `1/2 < θ < 1`, and `|ζ(1/2 + it)| ≤ C|t|^c` for `|t| ≥ 2`
(`CrossCriteria.ZetaCritBound c`, `c ≥ 0`), then for `1/2 ≤ σ ≤ θ` and every `ε > 0` there is `C'` with
`|ζ(σ + it)| ≤ C'|t|^{c(θ − σ)/(θ − 1/2) + ε}` for `|t| ≥ 2` (`zeta_strip_of_crit`): the exponent falls linearly from
`c` on the critical line to `0` at `θ`. At `θ = 11/12`, from the half-plane: `|ζ(σ + it)| = O(|t|^{(12/5)c(11/12 − σ)
+ ε})` (`zeta_strip_eleven_twelfths_of_crit`), and under Weyl's bound (`CrossCriteria.WeylBound`, `c = 1/6 + ε`),
`O(|t|^{(2/5)(11/12 − σ) + ε})` (`zeta_strip_eleven_twelfths_of_weyl`).

`Subconvexity.zeta_strip_of_zeroFree` gives the exponent `(θ − σ)/2` on `1 − θ ≤ σ ≤ θ`. On `1/2 ≤ σ ≤ θ` that is
this exponent at `c = (2θ − 1)/4`, the critical-line exponent it gives itself (`Subconvexity.zetaCritBound_of_zeroFree`).
A smaller `c` lowers the slope there: Weyl's `1/6`, or J. Bourgain's `13/84` (J. Amer. Math. Soc. 30 (2017)), which
gives `(13/35)(11/12 − σ)`. This library proves neither.

The proof is that of `Subconvexity.zeta_strip_of_zeroFree` with the critical line as the left edge: Hadamard's three
lines (`Subconvexity.norm_le_interp_strip`) between `Re s = 1/2`, where the hypothesis bounds `ζ`, and `Re s = θ + δ`,
where the half-plane does (`HalfPlaneLindelof.zeta_bound_of_zeroFree`), with `δ` small enough that moving the right
edge off `θ` costs at most `ε/2` in the exponent. The bound uses only the two lines, and it is linear in `σ` at `θ`.
-/
import Subconvexity

open Complex Set

namespace Subconvexity

/-- **The strip bound from a critical-line bound.** If `ζ(s) ≠ 0` on `Re s > θ`, `1/2 < θ < 1`, and
`CrossCriteria.ZetaCritBound c` with `c ≥ 0`, then for `1/2 ≤ σ ≤ θ` and `ε > 0` there is `C` with
`|ζ(σ + it)| ≤ C|t|^{c(θ − σ)/(θ − 1/2) + ε}` for `|t| ≥ 2`. -/
theorem zeta_strip_of_crit {θ c σ ε : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ < 1) (hc : 0 ≤ c) (hσ1 : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ θ) (hε : 0 < ε) (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    (hcrit : CrossCriteria.ZetaCritBound c) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (c * (θ - σ) / (θ - 1 / 2) + ε) := by
  have hθh : 0 < θ - 1 / 2 := by linarith
  have hX : 0 ≤ ε / 2 * (θ - 1 / 2) := by positivity
  -- the right edge `Re s = u = θ + δ`, with `cδ ≤ (ε/2)(θ − 1/2)`
  obtain ⟨δ, hδ0, hδc, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ c * δ ≤ ε / 2 * (θ - 1 / 2) ∧ δ ≤ (1 - θ) / 2 := by
    refine ⟨min (ε / 2 * (θ - 1 / 2) / (c + 1)) ((1 - θ) / 2), lt_min (by positivity) (by linarith), ?_,
      min_le_right _ _⟩
    calc c * min (ε / 2 * (θ - 1 / 2) / (c + 1)) ((1 - θ) / 2) ≤ c * (ε / 2 * (θ - 1 / 2) / (c + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ = ε / 2 * (θ - 1 / 2) * (c / (c + 1)) := by ring
      _ ≤ ε / 2 * (θ - 1 / 2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by linarith)).2 (by linarith)) hX
      _ = ε / 2 * (θ - 1 / 2) := mul_one _
  set u : ℝ := θ + δ with hu
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 1 / 2 := ⟨_, rfl⟩
  have hu1 : u < 1 := by linarith
  have hl0 : 0 < l := by rw [hl]; norm_num
  have hlu : l < u := by rw [hl]; linarith
  have hε' : 0 < ε / 2 := by positivity
  -- the bound `zeta_bound_of_zeroFree` on `Re s ≥ u`
  obtain ⟨T, C₀, hL⟩ := HalfPlaneLindelof.zeta_bound_of_zeroFree (by linarith) hθ1
    (by linarith : θ < u) hε' hzf
  -- polynomial growth in the strip `l ≤ Re s ≤ u`
  set K : ℝ := 1 / 2 + 1 / (1 - u) + 1 / l with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ 1 / (1 - u) := one_div_nonneg.2 (by linarith)
    have h2 : 0 ≤ 1 / l := one_div_nonneg.2 hl0.le
    linarith
  have hgr : ∀ z : ℂ, z.re ∈ Icc l u → ‖riemannZeta z‖ ≤ K * (1 + |z.im|) ^ (1 : ℝ) := by
    intro z hz
    rw [Real.rpow_one]
    have hz0 : 0 < z.re := hl0.trans_le hz.1
    have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; linarith [hz.2]
    refine (HalfPlanePNT.norm_riemannZeta_le_of_re_pos hz0 hz1).trans ?_
    have h1 : 1 / ‖1 - z‖ ≤ 1 / (1 - u) := by
      have hre : 1 - u ≤ ‖1 - z‖ := by
        have := Complex.re_le_norm (1 - z)
        rw [Complex.sub_re, Complex.one_re] at this
        linarith [hz.2]
      exact one_div_le_one_div_of_le (by linarith) hre
    have h2 : ‖z‖ / z.re ≤ (1 + |z.im|) / l := by
      have hn : ‖z‖ ≤ 1 + |z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos hz0] at this
        linarith [hz.2]
      calc ‖z‖ / z.re ≤ (1 + |z.im|) / z.re := by gcongr
        _ ≤ (1 + |z.im|) / l := by gcongr; exact hz.1
    have hy : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    have hc' : 0 ≤ 1 / (1 - u) := one_div_nonneg.2 (by linarith)
    calc 1 / 2 + 1 / ‖1 - z‖ + ‖z‖ / z.re ≤ 1 / 2 + 1 / (1 - u) + (1 + |z.im|) / l := by linarith
      _ ≤ (1 / 2 + 1 / (1 - u)) * (1 + |z.im|) + (1 + |z.im|) / l := by
          have := mul_le_mul_of_nonneg_left hy (by linarith : (0 : ℝ) ≤ 1 / 2 + 1 / (1 - u))
          linarith
      _ = K * (1 + |z.im|) := by rw [hK]; ring
  -- the right edge: `|ζ(u + it)| ≤ B(1 + |t|)^{ε/2}`
  set B : ℝ := max (max C₀ 0) (K * (1 + |T|)) with hB
  have hB0 : 0 ≤ B := (le_max_right C₀ 0).trans (le_max_left _ _)
  have hright : ∀ t : ℝ, ‖riemannZeta (u + t * I)‖ ≤ B * (1 + |t|) ^ (ε / 2) := by
    intro t
    have hT1 : (1 : ℝ) ≤ (1 + |t|) ^ (ε / 2) :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hε'.le
    rcases le_or_gt T |t| with ht | ht
    · have h := (hL u t le_rfl ht).1
      calc ‖riemannZeta (u + t * I)‖ ≤ C₀ * |t| ^ (ε / 2) := h
        _ ≤ max C₀ 0 * |t| ^ (ε / 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ max C₀ 0 * (1 + |t|) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hε'.le)
              (le_max_right _ _)
        _ ≤ B * (1 + |t|) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    · have hre : ((u : ℂ) + t * I).re ∈ Icc l u := by
        rw [show ((u : ℂ) + t * I).re = u by simp]
        exact ⟨hlu.le, le_rfl⟩
      have h := hgr _ hre
      have him : ((u : ℂ) + t * I).im = t := by simp
      rw [him, Real.rpow_one] at h
      calc ‖riemannZeta (u + t * I)‖ ≤ K * (1 + |t|) := h
        _ ≤ K * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self T]) hK0
        _ ≤ B := le_max_right _ _
        _ ≤ B * (1 + |t|) ^ (ε / 2) := le_mul_of_one_le_right hB0 hT1
  -- the left edge, the critical line: `|ζ(1/2 + it)| ≤ A(1 + |t|)^c`
  obtain ⟨C₁, hC₁⟩ := hcrit
  set A : ℝ := max (max C₁ 0) (3 * K) with hA
  have hleft : ∀ t : ℝ, ‖riemannZeta (l + t * I)‖ ≤ A * (1 + |t|) ^ c := by
    intro t
    have hT1 : (1 : ℝ) ≤ (1 + |t|) ^ c := Real.one_le_rpow (by linarith [abs_nonneg t]) hc
    have hA0 : 0 ≤ A := (le_max_right C₁ 0).trans (le_max_left _ _)
    have hlc : ((l : ℝ) : ℂ) = 1 / 2 := by rw [hl]; push_cast; ring
    rcases le_or_gt 2 |t| with ht | ht
    · have h := hC₁ t ht
      rw [hlc]
      calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ C₁ * |t| ^ c := h
        _ ≤ max C₁ 0 * |t| ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ max C₁ 0 * (1 + |t|) ^ c :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hc)
              (le_max_right _ _)
        _ ≤ A * (1 + |t|) ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    · have hre : ((l : ℂ) + t * I).re ∈ Icc l u := by
        rw [show ((l : ℂ) + t * I).re = l by simp]
        exact ⟨le_rfl, hlu.le⟩
      have h := hgr _ hre
      have him : ((l : ℂ) + t * I).im = t := by simp
      rw [him, Real.rpow_one] at h
      have ht3 : 1 + |t| ≤ 3 := by linarith
      calc ‖riemannZeta (l + t * I)‖ ≤ K * (1 + |t|) := h
        _ ≤ K * 3 := mul_le_mul_of_nonneg_left ht3 hK0
        _ = 3 * K := mul_comm _ _
        _ ≤ A := le_max_right _ _
        _ ≤ A * (1 + |t|) ^ c := le_mul_of_one_le_right hA0 hT1
  -- interpolate
  have hdiff : DifferentiableOn ℂ riemannZeta (re ⁻¹' Icc l u) := fun z hz =>
    (differentiableAt_riemannZeta (fun h => by
      have : z.re ∈ Icc l u := hz
      rw [h, Complex.one_re] at this
      linarith [this.2])).differentiableWithinAt
  have hσ : σ ∈ Icc l u := ⟨by rw [hl]; exact hσ1, by linarith⟩
  set D : ℝ := (A * Real.exp (l ^ 2 + c ^ 2 / 4)) ^ (1 - (σ - l) / (u - l)) *
      (B * Real.exp (u ^ 2 + (ε / 2) ^ 2 / 4)) ^ ((σ - l) / (u - l)) with hD
  have hD0 : 0 ≤ D := by
    have hA0 : 0 ≤ A := (le_max_right C₁ 0).trans (le_max_left _ _)
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  -- the interpolated exponent is at most the stated one: with `d = u − l = (θ − 1/2) + δ`, the weight
  -- `(u − σ)/d` of `c` is `(θ − σ)/d + δ/d`, the first part at most `(θ − σ)/(θ − 1/2)` and `cδ/d ≤ ε/2`
  have hul : 0 < u - l := by linarith
  have hk1 : (σ - l) / (u - l) ≤ 1 := (div_le_one hul).2 (by linarith)
  have h1k : 1 - (σ - l) / (u - l) = (u - σ) / (u - l) := by
    rw [eq_div_iff hul.ne', sub_mul, one_mul, div_mul_cancel₀ _ hul.ne']
    ring
  have hd : u - l = θ - 1 / 2 + δ := by rw [hu, hl]; ring
  have hus : u - σ = θ - σ + δ := by rw [hu]; ring
  have hpos : 0 < θ - 1 / 2 + δ := by linarith
  have hfirst : (u - σ) / (u - l) * c ≤ c * (θ - σ) / (θ - 1 / 2) + ε / 2 := by
    rw [hus, hd]
    have e1 : (θ - σ + δ) / (θ - 1 / 2 + δ) * c =
        c * (θ - σ) / (θ - 1 / 2 + δ) + c * δ / (θ - 1 / 2 + δ) := by
      rw [div_mul_eq_mul_div, ← add_div]
      congr 1
      ring
    rw [e1]
    have t1 : c * (θ - σ) / (θ - 1 / 2 + δ) ≤ c * (θ - σ) / (θ - 1 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hc (by linarith)) hθh (by linarith)
    have t2 : c * δ / (θ - 1 / 2 + δ) ≤ ε / 2 := by
      rw [div_le_iff₀ hpos]
      have : 0 ≤ ε / 2 * δ := mul_nonneg hε'.le hδ0.le
      linarith
    linarith
  have hexp : (1 - (σ - l) / (u - l)) * c + (σ - l) / (u - l) * (ε / 2) ≤
      c * (θ - σ) / (θ - 1 / 2) + ε := by
    rw [h1k]
    have : (σ - l) / (u - l) * (ε / 2) ≤ ε / 2 := by
      calc (σ - l) / (u - l) * (ε / 2) ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right hk1 hε'.le
        _ = ε / 2 := one_mul _
    linarith
  have he : 0 ≤ c * (θ - σ) / (θ - 1 / 2) + ε := by
    have : 0 ≤ c * (θ - σ) / (θ - 1 / 2) := div_nonneg (mul_nonneg hc (by linarith)) hθh.le
    linarith
  refine ⟨D * 2 ^ (c * (θ - σ) / (θ - 1 / 2) + ε), fun t ht => ?_⟩
  have key := norm_le_interp_strip hlu hc hε'.le zero_le_one hdiff hleft hright hgr hσ t
  have ht1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc ‖riemannZeta (σ + t * I)‖
      ≤ D * (1 + |t|) ^ ((1 - (σ - l) / (u - l)) * c + (σ - l) / (u - l) * (ε / 2)) := key
    _ ≤ D * (1 + |t|) ^ (c * (θ - σ) / (θ - 1 / 2) + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 hexp) hD0
    _ ≤ D * (2 * |t|) ^ (c * (θ - σ) / (θ - 1 / 2) + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) he) hD0
    _ = D * 2 ^ (c * (θ - σ) / (θ - 1 / 2) + ε) * |t| ^ (c * (θ - σ) / (θ - 1 / 2) + ε) := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg t)]; ring

/-- **At `11/12`, from the half-plane**: `CrossCriteria.ZetaCritBound c` with `c ≥ 0` gives
`|ζ(σ + it)| = O(|t|^{(12/5)c(11/12 − σ) + ε})` on `1/2 ≤ σ ≤ 11/12`. -/
theorem zeta_strip_eleven_twelfths_of_crit {c σ ε : ℝ} (hc : 0 ≤ c) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 11 / 12)
    (hε : 0 < ε) (hcrit : CrossCriteria.ZetaCritBound c) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (12 / 5 * c * (11 / 12 - σ) + ε) := by
  have h := zeta_strip_of_crit (θ := 11 / 12) (by norm_num) (by norm_num) hc hσ1 hσ2 hε
    (fun _ hs => (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1) hcrit
  have e : c * (11 / 12 - σ) / (11 / 12 - 1 / 2) + ε = 12 / 5 * c * (11 / 12 - σ) + ε := by ring
  rwa [e] at h

/-- **At `11/12`, under Weyl's bound**: `|ζ(σ + it)| = O(|t|^{(2/5)(11/12 − σ) + ε})` on `1/2 ≤ σ ≤ 11/12`, against
the `(11/12 − σ)/2` of `Subconvexity.zeta_strip_eleven_twelfths`. -/
theorem zeta_strip_eleven_twelfths_of_weyl (hW : CrossCriteria.WeylBound) {σ ε : ℝ} (hσ1 : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ 11 / 12) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (2 / 5 * (11 / 12 - σ) + ε) := by
  obtain ⟨C, hC⟩ := zeta_strip_eleven_twelfths_of_crit (c := 1 / 6 + ε / 4) (by positivity) hσ1 hσ2
    (half_pos hε) (hW _ (by positivity))
  refine ⟨max C 0, fun t ht => (hC t ht).trans ?_⟩
  have h1 : (1 : ℝ) ≤ |t| := by linarith
  have hexp : 12 / 5 * (1 / 6 + ε / 4) * (11 / 12 - σ) + ε / 2 ≤ 2 / 5 * (11 / 12 - σ) + ε := by
    have h := mul_le_mul_of_nonneg_left (show 11 / 12 - σ ≤ 5 / 12 by linarith) hε.le
    linarith
  calc C * |t| ^ (12 / 5 * (1 / 6 + ε / 4) * (11 / 12 - σ) + ε / 2)
      ≤ max C 0 * |t| ^ (12 / 5 * (1 / 6 + ε / 4) * (11 / 12 - σ) + ε / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ max C 0 * |t| ^ (2 / 5 * (11 / 12 - σ) + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hexp) (le_max_right _ _)

end Subconvexity

#print axioms Subconvexity.zeta_strip_of_crit
#print axioms Subconvexity.zeta_strip_eleven_twelfths_of_crit
#print axioms Subconvexity.zeta_strip_eleven_twelfths_of_weyl
