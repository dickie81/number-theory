import SharpBound

/-!
# The frame inequality for one word

For the frame loss of the sharp frontier (`SharpData.frame_le`): a hermitian frame with one word `ω`, whose map `B_ω`
is onto `K^κ`, meets the frame inequality's conclusion exactly, with no frame condition, range or depth. With
`e = dim ker B_ω/dim V_ω`, the mean `s = μ(N_ω) − h_ω` and `μ_max(N_ω) ≤ λ`, in the archive's units,

  `(1 − e)·(s − μ(C)) ≤ e·(λ − h_ω − s)` (`KFrame.one_word_le`).

With `λ = μ(N_ω) + U` (the range (R′)) this is the frame loss `s − μ(C) ≤ (dim ker B_ω/rk B_ω)·U`
(`KFrame.frame_le_of_one_word`), whatever the heights: `λ − h_ω − s = U`.

**The kernel sublattice** (`KLattice.exists_ker_sublattice`). Let `φ` be the map of `B` between the hermitian lattices
(`KLattice.hom`), and `N₀ = N ∩ φ⁻¹(0)` (`EuclidLattice.preimg` of `0`), an `O_K`-stable saturated sublattice.
* `φ` is onto: it carries `ψ(M)` onto `ψ(B M)`, and `B M` is an `O_K`-lattice in `K^κ`, as `B` is onto, so it spans
  (`KLattice.span_lattice`). So the image of `N` is saturated of full rank, that is all of `C`.
* `N₀` spans `ker φ` (rationality of kernels, `EuclidLattice.span_inf_ker`), so `rk N = rk N₀ + rk C` by rank–nullity.
* Bost's inequality at the one quotient `N/N₀` (`EuclidLattice.bost_le`) gives `deg N − deg N₀ − h̄·rk C ≤ deg C`.
  Its proof is the degree additivity `covol N = covol N₀·vol(π ∘ x)` for a basis `(k, x)` of `N` adapted to `N₀`, with
  `π` the projection onto the orthogonal complement of `N₀` (`GramVolume.vol_sumElim`), and Hadamard on that complement,
  place by place (`PlaceLattice.Balanced.volLe`), as the complement is balanced across the places.

**The bookkeeping** (`SlopeFrame.Frame.one_word_le_of_ker`). With `deg N₀ ≤ λ·rk N₀` (`SlopeLe`), dividing by `rk N`
gives the inequality with `e = rk N₀/rk N`. Both hypotheses survive the rescaling to the archive's units
(`Frame.one_word_le_rescale`), and `rk N₀/rk N = dim ker B/dim V`, as `rk = [K:ℚ]·dim` (`KLattice.rk_top`).
-/

open NumberField SlopeFrame HermitianLattice

namespace SlopeFrame

/-- **The mean of one word** is its slope less its height: `s = μ(N_ω) − h_ω`. -/
theorem Frame.mean_one_word (F : Frame) (ω : F.ι) (hω : ∀ ω' : F.ι, ω' = ω) (hrk : (0 : ℝ) < (F.N ω).rk ⊤) :
    F.mean = (F.N ω).deg ⊤ / (F.N ω).rk ⊤ - F.h ω := by
  have hs (f : F.ι → ℝ) : ∑ ω', f ω' = f ω := Finset.sum_eq_single ω (fun b _ hb => absurd (hω b) hb) (by simp)
  rw [Frame.mean, hs, hs]
  field_simp

/-- **The frame inequality for one word, from a kernel**: if a sublattice `k` of the one source `N` (the kernel) has
`rk N = rk k + rk C` and `deg N − deg k − h·rk C ≤ deg C` (Bost at the quotient `N/k`), and `μ_max(N) ≤ λ`, then
`(1 − e)·(s − μ(C)) ≤ e·(λ − h − s)` with `e = rk k/rk N`: add `deg k ≤ λ·rk k` and divide by `rk N`. -/
theorem Frame.one_word_le_of_ker (F : Frame) (ω : F.ι) (hω : ∀ ω' : F.ι, ω' = ω) (k : F.L ω)
    (hrk : (F.N ω).rk ⊤ = (F.N ω).rk k + F.C.rk ⊤)
    (hdeg : (F.N ω).deg ⊤ - (F.N ω).deg k - F.h ω * F.C.rk ⊤ ≤ F.C.deg ⊤) {lam : ℝ}
    (hN : (F.N ω).SlopeLe lam) :
    (1 - ((F.N ω).rk k : ℝ) / (F.N ω).rk ⊤) * (F.mean - F.C.deg ⊤ / F.C.rk ⊤) ≤
      ((F.N ω).rk k : ℝ) / (F.N ω).rk ⊤ * (lam - F.h ω - F.mean) := by
  have hc : (0 : ℝ) < F.C.rk ⊤ := Nat.cast_pos.2 F.rk_pos
  have hr : (0 : ℝ) ≤ (F.N ω).rk k := Nat.cast_nonneg _
  have hR : ((F.N ω).rk ⊤ : ℝ) = (F.N ω).rk k + F.C.rk ⊤ := by exact_mod_cast hrk
  have hk := hN k
  rw [F.mean_one_word ω hω (by linarith), hR]
  set r : ℝ := ((F.N ω).rk k : ℝ)
  set c : ℝ := (F.C.rk ⊤ : ℝ)
  have key : r / (r + c) * (lam - F.h ω - ((F.N ω).deg ⊤ / (r + c) - F.h ω)) -
      (1 - r / (r + c)) * ((F.N ω).deg ⊤ / (r + c) - F.h ω - F.C.deg ⊤ / c) =
      (r * lam + F.C.deg ⊤ + F.h ω * c - (F.N ω).deg ⊤) / (r + c) := by
    field_simp
    ring
  have : 0 ≤ (r * lam + F.C.deg ⊤ + F.h ω * c - (F.N ω).deg ⊤) / (r + c) :=
    div_nonneg (by linarith) (by linarith)
  linarith

/-- **The rescaled frame for one word**: the hypotheses of `one_word_le_of_ker` for a frame give its conclusion for
the frame rescaled by `c`, as `rk N − rk k = rk C` carries the shift `c·rk`. -/
theorem Frame.one_word_le_rescale (F : Frame) (c : ℝ) (ω : F.ι) (hω : ∀ ω' : F.ι, ω' = ω) (k : F.L ω)
    (hrk : (F.N ω).rk ⊤ = (F.N ω).rk k + F.C.rk ⊤)
    (hdeg : (F.N ω).deg ⊤ - (F.N ω).deg k - F.h ω * F.C.rk ⊤ ≤ F.C.deg ⊤) {lam : ℝ}
    (hN : ((F.N ω).rescale c).SlopeLe lam) :
    (1 - ((F.N ω).rk k : ℝ) / (F.N ω).rk ⊤) *
        ((F.rescale c).mean - (F.rescale c).C.deg ⊤ / (F.rescale c).C.rk ⊤) ≤
      ((F.N ω).rk k : ℝ) / (F.N ω).rk ⊤ * (lam - (F.rescale c).h ω - (F.rescale c).mean) := by
  refine (F.rescale c).one_word_le_of_ker ω hω k hrk ?_ hN
  have hR : ((F.N ω).rk ⊤ : ℝ) = (F.N ω).rk k + F.C.rk ⊤ := by exact_mod_cast hrk
  show 2 * (F.N ω).deg ⊤ + c * (F.N ω).rk ⊤ - (2 * (F.N ω).deg k + c * (F.N ω).rk k) - 2 * F.h ω * F.C.rk ⊤ ≤
    2 * F.C.deg ⊤ + c * F.C.rk ⊤
  rw [hR]
  linarith

end SlopeFrame

namespace KLattice

open Module Submodule EuclidLattice

attribute [local instance] InnerProductSpace.complexToReal

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι κ : Type} [Fintype ι] [Fintype κ]
  [Nonempty κ]

/-- **The kernel sublattice**: for a `K`-linear `B` onto `K^κ` that maps `X` into `Y`, with norm at most `e^{h v}` at
each complex place `v`, the kernel sublattice `k = N ∩ φ⁻¹(0)` of `N = ψ(M_X)` has `rk N = rk k + rk C` and
`deg N − deg k − h̄·rk C ≤ deg C`, with `C = ψ(M_Y)` and `h̄` the mean of the `h v`. -/
theorem exists_ker_sublattice (X : KLattice K ι) (Y : KLattice K κ) (B : (ι → K) →ₗ[K] (κ → K))
    (hB : ∀ x ∈ X.M, B x ∈ Y.M) (hsurj : LinearMap.range B = ⊤) (h : Pl K → ℝ)
    (hφ : ∀ v, ∀ x ∈ (part v : Submodule ℂ (Space K ι)), ‖X.hom Y B x‖ ≤ Real.exp (h v) * ‖x‖) :
    ∃ k : X.toPlaceLattice.S, X.toPlaceLattice.slopeLattice.rk ⊤ =
        X.toPlaceLattice.slopeLattice.rk k + Y.toPlaceLattice.slopeLattice.rk ⊤ ∧
      X.toPlaceLattice.slopeLattice.deg ⊤ - X.toPlaceLattice.slopeLattice.deg k -
        (Fintype.card X.toPlaceLattice.P : ℝ)⁻¹ * (∑ v : X.toPlaceLattice.P, h v) *
          Y.toPlaceLattice.slopeLattice.rk ⊤ ≤ Y.toPlaceLattice.slopeLattice.deg ⊤ := by
  set P := X.toPlaceLattice
  set Q := Y.toPlaceLattice
  set φ : Space K ι →L[ℝ] Space K κ := (X.hom Y B).restrictScalars ℝ
  have hφΛ : ∀ x ∈ X.lattice, φ x ∈ Y.lattice := X.hom_mem Y hB
  have hpre : preimg (Λ := X.lattice) φ (⊥ : Sat Y.lattice) ∈ P.S :=
    X.stable.preimg (X.hom_act Y B) Q.bot_mem
  -- `φ` is onto: its image of `ψ(M)` is `ψ(B M)`, and `B M` is an `O_K`-lattice, as `B` is onto.
  have hlat : (X.M.map (B.restrictScalars (𝓞 K))).IsLattice K :=
    ⟨(IsLattice.fg (A := K) (M := X.M)).map _, by
      rw [map_coe, LinearMap.coe_restrictScalars, span_image, IsLattice.span_eq_top, Submodule.map_top, hsurj]⟩
  have hspan : span ℝ (φ '' (X.lattice : Set (Space K ι))) = ⊤ := by
    refine eq_top_iff.2 ((Y.withLattice (X.M.map (B.restrictScalars (𝓞 K)))).span_lattice.ge.trans (span_mono ?_))
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨X.ψ x, ⟨x, hx, rfl⟩, X.hom_ψ Y B x⟩
  have hrange : LinearMap.range (φ : Space K ι →ₗ[ℝ] Space K κ) = ⊤ :=
    eq_top_iff.2 (hspan.ge.trans (span_le.2 (by rintro _ ⟨y, -, rfl⟩; exact ⟨y, rfl⟩)))
  -- So the image of `⊤` is `⊤`.
  have hrkQ : Q.slopeLattice.rk ⊤ = finrank ℝ (Space K κ) := by
    show finrank ℝ (span ℝ (Y.lattice : Set (Space K κ))) = _
    rw [Y.span_lattice, finrank_top]
  have himg : img (Λ' := Y.lattice) φ (⊤ : Sat X.lattice) = ⊤ := by
    refine eq_of_le_of_not_lt le_top fun hlt => (slopeLattice Y.lattice).rk_strictMono hlt |>.ne ?_
    show finrank ℝ (span ℝ (sat Y.lattice (φ '' (X.lattice : Set (Space K ι))) : Set (Space K κ))) = _
    rw [span_sat (by rintro _ ⟨x, hx, rfl⟩; exact hφΛ x hx), hspan, finrank_top]
    exact hrkQ.symm
  -- The kernel sublattice spans `ker φ` (rationality of kernels), so ranks add up (rank–nullity).
  have h0 : span ℝ (((⊥ : Sat Y.lattice).1 : Submodule ℤ (Space K κ)) : Set (Space K κ)) = ⊥ := by
    rw [Sat.coe_bot, Submodule.bot_coe, span_zero_singleton]
  have hker : span ℝ ((preimg (Λ := X.lattice) φ (⊥ : Sat Y.lattice)).1 : Set (Space K ι)) =
      LinearMap.ker (φ : Space K ι →ₗ[ℝ] Space K κ) := by
    refine le_antisymm ((span_sat_le _).trans ?_) ?_
    · rw [span_eq, h0]
      rfl
    · have := span_inf_ker (A := X.lattice) (Λ' := Y.lattice) (φ : Space K ι →ₗ[ℝ] Space K κ) hφΛ
      rw [X.span_lattice, top_inf_eq] at this
      rw [← this]
      refine span_mono ?_
      rintro x ⟨hx, hx0⟩
      refine ⟨hx, subset_span ?_⟩
      show φ x ∈ span ℝ _
      rw [h0]
      simpa using hx0
  have hrn := LinearMap.finrank_range_add_finrank_ker (φ : Space K ι →ₗ[ℝ] Space K κ)
  rw [hrange, finrank_top] at hrn
  have hrk : P.slopeLattice.rk ⊤ = P.slopeLattice.rk ⟨_, hpre⟩ + Q.slopeLattice.rk ⊤ := by
    show finrank ℝ (span ℝ (X.lattice : Set (Space K ι))) =
      finrank ℝ (span ℝ ((preimg (Λ := X.lattice) φ (⊥ : Sat Y.lattice)).1 : Set (Space K ι))) + _
    rw [X.span_lattice, finrank_top, hker, hrkQ]
    omega
  refine ⟨⟨_, hpre⟩, hrk, ?_⟩
  -- Bost at the quotient by the kernel sublattice, with the volume bound of the places on its complement.
  have hK : (⊤ : Sat X.lattice) ⊓ preimg φ ⊥ ∈ P.S := P.S.inf_mem P.top_mem hpre
  have hvol := (PlaceLattice.Balanced.orthogonal_inf P.orth (P.balanced _ P.top_mem) (P.balanced _ hK)
    (span_mono (show (((⊤ : Sat X.lattice) ⊓ preimg φ ⊥).1 : Set (Space K ι)) ⊆ (⊤ : Sat X.lattice).1 from
      inf_le_left))).volLe P.orth (φ := φ) (h := h) fun v x hx => hφ v x hx
  have hQ : (0 : ℝ) < Q.slopeLattice.rk ⊤ := by
    rw [Y.rk_top]
    exact_mod_cast Nat.mul_pos Module.finrank_pos Fintype.card_pos
  have hr : ((P.slopeLattice.rk ⊤ : ℕ) : ℝ) = P.slopeLattice.rk ⟨_, hpre⟩ + Q.slopeLattice.rk ⊤ := by
    exact_mod_cast hrk
  have hb := bost_le φ hφΛ (a := ⊤) (b := ⊥) bot_le hvol
    (θ := (P.slopeLattice.deg ⊤ - P.slopeLattice.deg ⟨_, hpre⟩) / Q.slopeLattice.rk ⊤) (by
      rw [top_inf_eq]
      change _ * ((P.slopeLattice.rk ⊤ : ℝ) - P.slopeLattice.rk ⟨_, hpre⟩) ≤
        P.slopeLattice.deg ⊤ - P.slopeLattice.deg ⟨_, hpre⟩
      rw [hr, add_sub_cancel_left, div_mul_cancel₀ _ hQ.ne'])
  rw [himg, (slopeLattice Y.lattice).rk_bot, (slopeLattice Y.lattice).deg_bot] at hb
  simp only [Nat.cast_zero, sub_zero] at hb
  change (_ / (Q.slopeLattice.rk ⊤ : ℝ) - _) * (Q.slopeLattice.rk ⊤ : ℝ) ≤ Q.slopeLattice.deg ⊤ at hb
  rw [sub_mul, div_mul_cancel₀ _ hQ.ne'] at hb
  linarith

end KLattice

namespace ZetaBalance

namespace KFrame

attribute [local instance] InnerProductSpace.complexToReal

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/-- **The frame inequality for one word**: for a hermitian frame with one word `ω` whose map `B_ω` is onto `K^κ`,
with `e = dim ker B_ω/dim V_ω` and `μ_max(N_ω) ≤ λ`, `(1 − e)·(s − μ(C)) ≤ e·(λ − h_ω − s)` at the mean
`s = μ(N_ω) − h_ω`, in the archive's units (`KFrame.frame`). -/
theorem one_word_le (F : KFrame K) (ω : F.frame.ι) (hω : ∀ ω' : F.frame.ι, ω' = ω)
    (hsurj : LinearMap.range (F.B ω) = ⊤) {lam : ℝ} (hN : (F.frame.N ω).SlopeLe lam) :
    let e : ℝ := (Module.finrank K (LinearMap.ker (F.B ω)) : ℝ) / Module.finrank K (F.n ω → K)
    (1 - e) * (F.frame.mean - F.frame.C.deg ⊤ / F.frame.C.rk ⊤) ≤ e * (lam - F.frame.h ω - F.frame.mean) := by
  intro e
  let : Fintype (F.n ω) := F.fintypeN ω
  obtain ⟨k, hrk, hdeg⟩ := KLattice.exists_ker_sublattice (F.src ω) F.tgt (F.B ω) (F.hB ω) hsurj (F.ht ω) (F.hφ ω)
  have he : e = ((F.src ω).toPlaceLattice.slopeLattice.rk k : ℝ) / (F.src ω).toPlaceLattice.slopeLattice.rk ⊤ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (F.B ω)
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrn
    rw [KLattice.rk_top, KLattice.rk_top, ← hrn, mul_add] at hrk
    have hr : (F.src ω).toPlaceLattice.slopeLattice.rk k =
        Module.finrank ℚ K * Module.finrank K (LinearMap.ker (F.B ω)) := by omega
    have hq : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    show (Module.finrank K (LinearMap.ker (F.B ω)) : ℝ) / Module.finrank K (F.n ω → K) = _
    rw [Module.finrank_fintype_fun_eq_card, hr, KLattice.rk_top, ← hrn]
    push_cast
    rw [mul_div_mul_left _ _ hq.ne']
  rw [he]
  exact Frame.one_word_le_rescale (KLattice.frame F.tgt F.src F.B F.hB F.ht F.hφ) (archShift K) ω hω k hrk hdeg hN

/-- **The frame loss of one word**: for a hermitian frame with one word `ω` whose map `B_ω` is onto, the range
`μ_max(N_ω) ≤ μ(N_ω) + U` gives `s − μ(C) ≤ (dim ker B_ω/rk B_ω)·U`, a frame loss for `SharpData.frame_le`
(`one_word_le` with `λ = μ(N_ω) + U`, so `λ − h_ω − s = U`). -/
theorem frame_le_of_one_word (F : KFrame K) (ω : F.frame.ι) (hω : ∀ ω' : F.frame.ι, ω' = ω)
    (hsurj : LinearMap.range (F.B ω) = ⊤) {U : ℝ}
    (hN : (F.frame.N ω).SlopeLe ((F.frame.N ω).deg ⊤ / (F.frame.N ω).rk ⊤ + U)) :
    F.frame.mean - F.frame.C.deg ⊤ / F.frame.C.rk ⊤ ≤
      (Module.finrank K (LinearMap.ker (F.B ω)) : ℝ) / Module.finrank K (LinearMap.range (F.B ω)) * U := by
  let : Fintype (F.n ω) := F.fintypeN ω
  have h := F.one_word_le ω hω hsurj hN
  dsimp only at h
  have hrn := LinearMap.finrank_range_add_finrank_ker (F.B ω)
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hrB : (0 : ℝ) < Module.finrank K (LinearMap.range (F.B ω)) := by
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card]
    exact_mod_cast Fintype.card_pos
  have ha : ((Fintype.card (F.n ω) : ℕ) : ℝ) = Module.finrank K (LinearMap.range (F.B ω)) +
      Module.finrank K (LinearMap.ker (F.B ω)) := by exact_mod_cast hrn.symm
  have hrk : (0 : ℝ) < (F.frame.N ω).rk ⊤ := by
    show (0 : ℝ) < (F.src ω).toPlaceLattice.slopeLattice.rk ⊤
    rw [KLattice.rk_top]
    push_cast
    rw [ha]
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    positivity
  have hmean := F.frame.mean_one_word ω hω hrk
  rw [Module.finrank_fintype_fun_eq_card, ha, hmean,
    show (F.frame.N ω).deg ⊤ / (F.frame.N ω).rk ⊤ + U - F.frame.h ω -
      ((F.frame.N ω).deg ⊤ / (F.frame.N ω).rk ⊤ - F.frame.h ω) = U by ring] at h
  rw [hmean]
  set d : ℝ := (Module.finrank K (LinearMap.ker (F.B ω)) : ℝ)
  set r : ℝ := (Module.finrank K (LinearMap.range (F.B ω)) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have e1 : 1 - d / (r + d) = r / (r + d) := by
    field_simp
    ring
  rw [e1, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by linarith)] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hrB]
  linarith

end KFrame

end ZetaBalance
