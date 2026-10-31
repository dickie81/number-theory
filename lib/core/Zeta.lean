import Mathlib
import T1bt
import Split
import Exterior

/-! # The zero family of 1ca, linked to Mathlib's `riemannZeta`

`T1bt.lean` defines the nontrivial zeros of `riemannZeta` counted with multiplicity
(`zetaZeroFamily`). Here the positive-ordinate part of that family becomes the family `γ` of
1ca(i)–(iii), and its local finiteness (`{γ < T}` finite, the hypothesis `hfin` of `split` and
`wall_law_zeros`) is proved from Mathlib: the zeros are isolated (identity theorem on the connected
set `ℂ ∖ {1}`, with `ζ(2) ≠ 0`), they cannot accumulate at the pole (`(s − 1)ζ(s) → 1`), and the
strip bounds them, so only finitely many lie below any height. -/

open Real Filter Topology

noncomputable section

namespace WeilForm

open WeilTest

/-- `ζ` has no zeros in a punctured neighbourhood of its pole. -/
theorem zeta_ne_zero_near_one : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 :=
  riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds

/-- **Finitely many nontrivial zeros of `ζ` have `0 < Im ρ < T`.** -/
theorem finite_zeros_below (T : ℝ) :
    {s : ℂ | IsNontrivialZero s ∧ 0 < s.im ∧ s.im < T}.Finite := by
  by_contra hinf
  have hsub : {s : ℂ | IsNontrivialZero s ∧ 0 < s.im ∧ s.im < T}
      ⊆ Metric.closedBall 0 (1 + |T|) := by
    rintro s ⟨hs, h0, hT⟩
    obtain ⟨hr0, hr1⟩ := hs.mem_strip
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |T| := by
        rw [abs_of_pos hr0, abs_of_pos h0]; linarith [le_abs_self T]
  obtain ⟨z, -, hz⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall 0 _) hsub
  rw [accPt_iff_frequently_nhdsNE] at hz
  have hfz : ∃ᶠ s in 𝓝[≠] z, riemannZeta s = 0 := hz.mono fun s hs => hs.1.1
  by_cases h1 : z = 1
  · subst h1
    exact hfz zeta_ne_zero_near_one
  · have h := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
      (by simpa using h1) hfz
    have h2 := h (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num) (by simpa using h2)

/-- The index of `zetaZeroFamily`: a nontrivial zero with a copy number below its multiplicity. -/
abbrev ZIdx : Type := Σ z : NontrivialZero, Fin (zeroMult z)

/-- The zeros in the upper half-plane, with multiplicity. -/
def PosZeroIdx : Type := {p : ZIdx // 0 < (zetaZeroFamily p).im}

/-- **The ordinate family of 1ca**: `γ_p = Im ρ_p` over the nontrivial zeros of `riemannZeta`
with `Im ρ > 0`, each repeated by its multiplicity. -/
def zetaOrd (p : PosZeroIdx) : ℝ := (zetaZeroFamily p.1).im

/-- **Local finiteness of the zeta ordinates**: `{p | γ_p < T}` is finite for every `T`. -/
theorem zetaOrd_finite (T : ℝ) : ({p : PosZeroIdx | zetaOrd p < T}).Finite := by
  have hZ := finite_zeros_below T
  -- the zeros themselves
  have hA : ({z : NontrivialZero | 0 < z.1.im ∧ z.1.im < T}).Finite := by
    refine (hZ.preimage (f := fun z : NontrivialZero => z.1) Subtype.val_injective.injOn).subset ?_
    intro z hz
    exact ⟨z.2, hz.1, hz.2⟩
  -- with multiplicity: each fibre of `Sigma.fst` is a `Fin`
  have hB : ((Sigma.fst : ZIdx → NontrivialZero) ⁻¹'
      {z : NontrivialZero | 0 < z.1.im ∧ z.1.im < T}).Finite := by
    refine hA.preimage' (fun z _ => (Set.finite_range (Sigma.mk z)).subset ?_)
    rintro ⟨a, b⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
    subst h
    exact ⟨b, rfl⟩
  refine (hB.preimage (f := fun p : PosZeroIdx => p.1) Subtype.val_injective.injOn).subset ?_
  intro p hp
  exact ⟨p.2, hp⟩

/-- **1ca(i)–(iii) assembled for the zeros of `riemannZeta`.** The family is no longer a
hypothesis: `γ` is the positive ordinates of Mathlib's `riemannZeta` with multiplicity, locally
finite by `zetaOrd_finite`. The named inputs left are the first-zero height (`G ≤ γ` for every
zero, `G ∈ [14, 2πe]`) and von Mangoldt's and Littlewood's bounds on ζ's own `S = N − N₀ − 7/8`. -/
theorem wall_law_zeta {G a L Δ C lo hi Ts Tu : ℝ} {H : Finset ℝ}
    (h_height : ∀ p, G ≤ zetaOrd p)
    (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hSlog : ∀ t, G ≤ t → |Sz zetaOrd t| ≤ C * Real.log t)
    (hS1log : ∀ t, G ≤ t → |S1 (Sz zetaOrd) G t| ≤ C * Real.log t)
    (hlo : L < lo) (hloΔ : G + 2 * Δ ≤ lo) (hTG : TG G H lo < 1)
    (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hcrit : Fp G (2 * π * Real.exp (2 * a)) H Ts = 0)
    (hminu : ∀ T ∈ Set.Icc lo hi, Fk zetaOrd a H Tu ≤ Fk zetaOrd a H T) :
    ∃ OscInf : ℝ, Tendsto (fun X => ∫ r in G..X, Sz zetaOrd r * (4 / r)) atTop (𝓝 OscInf) ∧
      |Fk zetaOrd a H Tu - (Fs G a H Ts + OscInf)|
        ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log hi / Real.sqrt lo) ∧
      (Tu - Ts) ^ 2 ≤ 4 * ((8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C)
        * (Real.log hi / Real.sqrt lo)) * hi / (1 - TG G H lo) :=
  wall_law_zeros zetaOrd_finite h_height hG14 hGe hLG hH hΔ hC hSlog hS1log hlo hloΔ hTG hTs hTu
    hcrit hminu

end WeilForm

#print axioms WeilForm.finite_zeros_below
#print axioms WeilForm.zetaOrd_finite
#print axioms WeilForm.wall_law_zeta
