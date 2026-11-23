import Mathlib

/-!
# The pole nearest to a vertical line

Geometry for Landau's theorem on windows (`LandauWindow.lean`). `Z` is a set of points with no accumulation
point in the right half-plane (the zeros of finitely many `L`-functions), all left of the line `Re s = σ`. If
one of them lies right of `θ`, with `0 < θ < σ`, then either

* (a) some point `σ + iγ` of the line has a unique nearest point `p` of `Z`, nearer to it than every point of
  `Z` is to `σ`, and nearer than `σ − θ`; or
* (b) a real point `β > θ` of `Z` is the only one in a disc about `σ` of radius greater than `σ − β`.

Let `D` be the distance from `σ` to `Z`, at most `σ − Re ρ₀`. If some point of `Z` is horizontally nearer to the
line than `D`, the vertical line through it meets case (a), after a small move of `γ` that breaks ties: two
points left of the line are equidistant from `σ + iγ` for at most one `γ`. Otherwise the nearest points to `σ`
satisfy `σ − Re p ≥ D = |σ − p|`, so they are the one real point `σ − D`: case (b).

* `finite_inter_closedBall`: `Z` meets each closed disc in the open right half-plane in a finite set.
* `nearest_pole`: the dichotomy.
-/

open Complex Filter Topology Metric

namespace LandauWindow

/-- A set with no accumulation point in the right half-plane meets each closed disc there in a finite set. -/
theorem finite_inter_closedBall {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {z : ℂ} {r : ℝ} (hr : r < z.re) : (Z ∩ closedBall z r).Finite := by
  by_contra h
  obtain ⟨x, hx, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact h (isCompact_closedBall z r) Set.inter_subset_right
  have hx0 : 0 < x.re := by linarith [sub_re z x, (re_le_norm (z - x)).trans (mem_closedBall_iff_norm'.1 hx)]
  exact not_frequently.2 (hiso x hx0) ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun _ hy => hy.1)

/-- Two distinct points left of the line `Re s = σ` are equidistant from `σ + iγ` for at most one `γ`. -/
theorem equidistant_subsingleton {σ : ℝ} {u v : ℂ} (hu : u.re < σ) (hv : v.re < σ) :
    {γ : ℝ | u ≠ v ∧ ‖(σ + γ * I : ℂ) - u‖ = ‖(σ + γ * I : ℂ) - v‖}.Subsingleton := by
  have key (γ : ℝ) (w : ℂ) : ‖(σ + γ * I : ℂ) - w‖ ^ 2 = (σ - w.re) ^ 2 + (γ - w.im) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  rintro γ ⟨huv, h⟩ γ' ⟨-, h'⟩
  have h1 := congrArg (· ^ 2) h
  have h2 := congrArg (· ^ 2) h'
  simp only [key] at h1 h2
  rcases mul_eq_zero.1 (by linear_combination (h1 - h2) / 2 : (γ - γ') * (v.im - u.im) = 0) with h | h
  · linarith
  · have him : u.im = v.im := by linarith
    rw [him] at h1
    exact absurd (Complex.ext (by nlinarith) him) huv

/-- A point `w` no farther from `σ` than its horizontal distance `σ - Re w` is the real point
`σ - ‖σ - w‖`. -/
theorem eq_ofReal_of_norm_le {σ : ℝ} {w : ℂ} (h : ‖(σ : ℂ) - w‖ ≤ σ - w.re) :
    w = ((σ - ‖(σ : ℂ) - w‖ : ℝ) : ℂ) := by
  have he : ‖(σ : ℂ) - w‖ = σ - w.re := le_antisymm h (by simpa using re_le_norm ((σ : ℂ) - w))
  have h2 := sq_norm_sub_sq_re ((σ : ℂ) - w)
  rw [he] at h2
  simp at h2
  exact Complex.ext (by simp [he]) (by simpa using (pow_eq_zero_iff two_ne_zero).1 h2.symm)

/-- If `p` is the only point of `Z` with `f w ≤ f p`, where `f p < D` and only finitely many points of `Z` have
`f w < D`, then `p` is the only point of `Z` with `f w < r`, for some `r` with `f p < r ≤ D`. -/
theorem exists_radius {Z : Set ℂ} {f : ℂ → ℝ} {D : ℝ} (hfin : {w ∈ Z | f w < D}.Finite) {p : ℂ}
    (hpD : f p < D) (hp : ∀ w ∈ Z, f w ≤ f p → w = p) :
    ∃ r, f p < r ∧ r ≤ D ∧ ∀ w ∈ Z, f w < r → w = p := by
  have hS : {w ∈ Z | f w < D ∧ w ≠ p}.Finite := hfin.subset fun w hw => ⟨hw.1, hw.2.1⟩
  have h : ∀ᶠ r in 𝓝 (f p), r < D ∧ ∀ w ∈ {w ∈ Z | f w < D ∧ w ≠ p}, r < f w :=
    (eventually_lt_nhds hpD).and <| hS.eventually_all.2 fun w hw =>
      eventually_lt_nhds <| lt_of_not_ge fun h => hw.2.2 (hp w hw.1 h)
  obtain ⟨r, hpr, hrD, hr⟩ := h.exists_gt
  exact ⟨r, hpr, hrD.le, fun w hw hwr => by_contra fun hne => lt_asymm hwr (hr w ⟨hw, hwr.trans hrD, hne⟩)⟩

/-- **Case (a)**: if a point `ρ₁` of `Z` is horizontally nearer than `D < σ` to the line `Re s = σ`, some point
`σ + iγ` of the line has a nearest point `p` of `Z` that is the only point of `Z` in a disc about `σ + iγ` of
radius at most `D`. Take `γ` near `Im ρ₁`, off the finitely many heights where two points of `Z` near `ρ₁` are
equidistant from `σ + iγ`. -/
theorem exists_isolated_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ D : ℝ}
    (hD : D < σ) (hZ : ∀ ρ ∈ Z, ρ.re < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ p ∈ Z, ∃ r : ℝ, ‖(σ + γ * I : ℂ) - p‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, ‖(σ + γ * I : ℂ) - w‖ < r → w = p := by
  obtain ⟨ε, hε, hεm⟩ := exists_between (lt_min (sub_pos.2 hρ₁) (sub_pos.2 hD))
  obtain ⟨hε₁, hε₂⟩ := lt_min_iff.1 hεm
  -- `G` holds every point of `Z` within `D` of `σ + iγ` for `|γ - Im ρ₁| < ε`
  set z₁ : ℂ := σ + ρ₁.im * I
  set G := Z ∩ closedBall z₁ (D + ε)
  have hG : G.Finite := finite_inter_closedBall hiso (by simp [z₁]; linarith)
  -- off finitely many heights `γ`, no two points of `G` are equidistant from `σ + iγ`
  have hB := hG.biUnion fun u hu => hG.biUnion fun v hv => (equidistant_subsingleton (hZ u hu.1) (hZ v hv.1)).finite
  obtain ⟨γ, ⟨hγ₁, hγ₂⟩, hγB⟩ := ((Set.Ioo_infinite (by linarith : ρ₁.im - ε < ρ₁.im + ε)).sdiff hB).nonempty
  set z : ℂ := σ + γ * I
  have hz : ‖z - z₁‖ < ε := by
    rw [← dist_eq_norm, dist_of_re_eq (by simp [z, z₁])]
    simp [z, z₁, Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith
  have hsub : ∀ w ∈ Z, ‖z - w‖ < D → w ∈ G := fun w hw h => ⟨hw, by
    rw [mem_closedBall_iff_norm]
    linarith [norm_sub_le_norm_sub_add_norm_sub w z z₁, norm_sub_rev w z]⟩
  have hρ : ‖z - ρ₁‖ < D := by
    have : ‖z₁ - ρ₁‖ = σ - ρ₁.re := by
      rw [← dist_eq_norm, dist_of_im_eq (by simp [z₁]), Real.dist_eq, abs_of_pos] <;> simp [z₁, hZ ρ₁ h₁]
    linarith [norm_sub_le_norm_sub_add_norm_sub z z₁ ρ₁]
  -- the nearest point `p` of `G` to `σ + iγ` is the only nearest point of `Z`
  obtain ⟨p, hpG, hpmin⟩ := Set.exists_min_image G (fun w => ‖z - w‖) hG ⟨ρ₁, hsub ρ₁ h₁ hρ⟩
  have hpD : ‖z - p‖ < D := (hpmin ρ₁ (hsub ρ₁ h₁ hρ)).trans_lt hρ
  refine ⟨γ, p, hpG.1, exists_radius (hG.subset fun w hw => hsub w hw.1 hw.2) hpD fun w hw h => ?_⟩
  have hwG := hsub w hw (h.trans_lt hpD)
  by_contra hne
  exact hγB (Set.mem_biUnion hwG (Set.mem_biUnion hpG ⟨hne, le_antisymm h (hpmin w hwG)⟩))

/-- **The nearest pole**: the dichotomy above. -/
theorem nearest_pole {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ θ : ℝ}
    (hθ : 0 < θ) (hZ : ∀ ρ ∈ Z, ρ.re < σ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, D ≤ ‖(σ : ℂ) - w‖) ∧ ∃ γ : ℝ, ∃ p ∈ Z, ∃ r : ℝ,
        ‖(σ + γ * I : ℂ) - p‖ < r ∧ r ≤ D ∧ ∀ w ∈ Z, ‖(σ + γ * I : ℂ) - w‖ < r → w = p) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
        ∀ w ∈ Z, ‖(σ : ℂ) - w‖ < r → w = β) := by
  by_cases hA : ∃ D ≤ σ - θ, (∀ w ∈ Z, D ≤ ‖(σ : ℂ) - w‖) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D
  · obtain ⟨D, hD, hDZ, ρ₁, h₁, hρ₁⟩ := hA
    exact .inl ⟨D, hD, hDZ, exists_isolated_nearest hiso (by linarith) hZ h₁ hρ₁⟩
  -- (b): no point of `Z` is horizontally nearer to the line than the nearest point `p` is to `σ`, so `p` is real
  push Not at hA
  have hF : {w ∈ Z | ‖(σ : ℂ) - w‖ < σ - θ}.Finite :=
    (finite_inter_closedBall hiso (z := σ) (r := σ - θ) (by rw [ofReal_re]; linarith)).subset
      fun w hw => ⟨hw.1, mem_closedBall_iff_norm'.2 hw.2.le⟩
  obtain ⟨p, ⟨hpZ, hpθ⟩, hpmin⟩ := Set.exists_min_image _ (fun w => ‖(σ : ℂ) - w‖) hF <| by
    by_contra hne
    linarith [hA (σ - θ) le_rfl (fun w hw => not_lt.1 fun h => hne ⟨w, hw, h⟩) ρ₀ h₀]
  have hlow : ∀ w ∈ Z, ‖(σ : ℂ) - p‖ ≤ ‖(σ : ℂ) - w‖ := fun w hw =>
    (lt_or_ge ‖(σ : ℂ) - w‖ (σ - θ)).elim (fun h => hpmin w ⟨hw, h⟩) hpθ.le.trans
  have hreal : ∀ w ∈ Z, ‖(σ : ℂ) - w‖ ≤ ‖(σ : ℂ) - p‖ → w = ((σ - ‖(σ : ℂ) - p‖ : ℝ) : ℂ) := by
    intro w hw h
    rw [← le_antisymm h (hlow w hw)]
    exact eq_ofReal_of_norm_le (h.trans (hA _ hpθ.le hlow w hw))
  have hp := hreal p hpZ le_rfl
  obtain ⟨r, hpr, hrθ, hr⟩ := exists_radius hF hpθ fun w hw h => (hreal w hw h).trans hp.symm
  exact .inr ⟨σ - ‖(σ : ℂ) - p‖, by rwa [← hp], by linarith, r, by linarith, hrθ,
    fun w hw h => (hr w hw h).trans hp⟩

end LandauWindow

#print axioms LandauWindow.nearest_pole
