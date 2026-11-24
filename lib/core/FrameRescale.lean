import Mathlib
import SlopeFrame

/-!
# Rescaled frames, extreme slopes, duals and saturation

Layer L1 of the sharp frontier (with `KLattice`): what a frontier needs to be stated in the archive's units.

**Rescaling** (`SlopeFrame.Frame.rescale`). The archive's degrees are `2·deg + c·rk` in the library's, with
`c = −log 2 + log|d_K|/[K:ℚ]`, and its heights are `2h` (`KLattice`, "The factor 2"). The rescaled frame has the same
words, sublattices, images and ranks, degrees `deg ↦ 2·deg + c·rk` on every source and on the target, and heights
`h ↦ 2h`. Then, with `s, U, H ↦ 2s + c, 2U, 2H` and the same `α`, `β`:

* every hypothesis of `Frame.Spread` holds for the rescaled frame iff it holds for the frame (`Frame.spread_rescale`):
  minimal and maximal slopes go `θ ↦ 2θ + c` (`SlopeLattice.slopeGe_rescale`, `SlopeLattice.slopeLe_rescale`),
  Bost's inequality and `SupClosed` are preserved, the mean sum goes `Σ ↦ 2Σ + c·Σ rk` (`Frame.sum_rescale`), and
  rank spreading involves only ranks and images, so it is unchanged;
* the conclusion of the frame inequality holds for the rescaled frame iff it holds for the frame
  (`Frame.loss_le_rescale_iff`): the slope of the target goes `μ ↦ 2μ + c` (`Frame.slope_rescale`), and so does the
  bound `s − αH − βU·log(1 + H/U)`, since `2H/2U = H/U`.

So the spec's claim of invariance (L1.2) holds exactly, with two provisos: the same `c` must shift every source and
the target (otherwise the shift goes into the heights), and the factor is `2` throughout. The rescaled frame inequality
(`Frame.Spread.loss_le_rescale`) is a corollary of `Frame.Spread.loss_le` for the rescaled frame.

**Extreme slopes** (`SlopeLattice.muMax`, `SlopeLattice.muMin`): the supremum of the slopes of the nonzero
sublattices, and the infimum of the slopes of the nonzero quotients of `a`. They are characterised by `SlopeLe` and
`SlopeGe` once the slopes are bounded (`slopeLe_iff_muMax_le`, `slopeGe_iff_le_muMin`), which is how (R) of the
frontier (spec L7.5) turns into `Frame.Spread.range` and `Frame.Spread.depth`. Without that bound the suprema are
junk, so a frontier should state (R) with `SlopeLe`/`SlopeGe`, or carry the bound.

**Duals and saturation** (`HermitianLattice.dual`, `HermitianLattice.saturation`) of an `𝓞 K`-lattice `M ⊆ K^ι`:
`M^∨ = {f ∈ (K^ι)^* : f(M) ⊆ 𝓞 K}` and `M ∩ W` for a subspace `W`, for L6–L7.
-/

namespace SlopeFrame

namespace SlopeLattice

variable {L : Type*} [Lattice L] [BoundedOrder L] (X : SlopeLattice L)

/-- **Rescaling** to the archive's units: `deg ↦ 2·deg + c·rk`, so that slopes go `μ ↦ 2μ + c`. -/
def rescale (c : ℝ) : SlopeLattice L where
  rk := X.rk
  deg a := 2 * X.deg a + c * X.rk a
  rk_bot := X.rk_bot
  deg_bot := by simp [X.deg_bot, X.rk_bot]
  rk_strictMono := X.rk_strictMono

variable {X}

/-- Minimal slopes rescale: `μ_min(a) ≥ θ` after rescaling iff `μ_min(a) ≥ (θ − c)/2` before. -/
theorem slopeGe_rescale {c θ : ℝ} {a : L} : (X.rescale c).SlopeGe a θ ↔ X.SlopeGe a ((θ - c) / 2) :=
  forall₂_congr fun b _ => by
    simp only [rescale]
    constructor <;> intro h <;> linarith

/-- Maximal slopes rescale: `μ_max ≤ λ` after rescaling iff `μ_max ≤ (λ − c)/2` before. -/
theorem slopeLe_rescale {c lam : ℝ} : (X.rescale c).SlopeLe lam ↔ X.SlopeLe ((lam - c) / 2) :=
  forall_congr' fun b => by
    simp only [rescale]
    constructor <;> intro h <;> linarith

/-- `SupClosed` is invariant under rescaling. -/
theorem supClosed_rescale {c : ℝ} : (X.rescale c).SupClosed ↔ X.SupClosed := by
  simp only [SupClosed, slopeGe_rescale]
  refine ⟨fun h a b θ ha hb => ?_, fun h a b θ => h a b _⟩
  have := h a b (2 * θ + c)
  rw [show (2 * θ + c - c) / 2 = θ by ring] at this
  exact this ha hb

end SlopeLattice

open SlopeLattice

/-- **The rescaled frame**, in the archive's units: the same words, sublattices and images, degrees
`deg ↦ 2·deg + c·rk` on every source and on the target, and heights `h ↦ 2h`. Used by L7 (spec L7.6). -/
def Frame.rescale (F : Frame) (c : ℝ) : Frame where
  ι := F.ι
  L := F.L
  N ω := (F.N ω).rescale c
  M := F.M
  C := F.C.rescale c
  img := F.img
  h ω := 2 * F.h ω
  bost ω a θ ha := by
    rw [slopeGe_rescale] at ha ⊢
    exact (F.bost ω a _ ha).anti (by linarith)
  supClosed := supClosed_rescale.2 F.supClosed
  rk_pos := F.rk_pos

variable {F : Frame} {c s U H α β : ℝ}

/-- The mean sum rescales: `Σ (deg N_ω − h_ω·rk N_ω) ↦ 2·Σ (deg N_ω − h_ω·rk N_ω) + c·Σ rk N_ω`. -/
theorem Frame.sum_rescale (F : Frame) (c : ℝ) :
    ∑ ω, (((F.rescale c).N ω).deg ⊤ - (F.rescale c).h ω * ((F.rescale c).N ω).rk ⊤) =
      2 * ∑ ω, ((F.N ω).deg ⊤ - F.h ω * (F.N ω).rk ⊤) + c * ∑ ω, ((F.N ω).rk ⊤ : ℝ) := by
  show ∑ ω, (2 * (F.N ω).deg ⊤ + c * (F.N ω).rk ⊤ - 2 * F.h ω * (F.N ω).rk ⊤) = _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- The slope of the target rescales: `μ(C) ↦ 2·μ(C) + c`. -/
theorem Frame.slope_rescale (F : Frame) (c : ℝ) :
    (F.rescale c).C.deg ⊤ / (F.rescale c).C.rk ⊤ = 2 * (F.C.deg ⊤ / F.C.rk ⊤) + c := by
  have : (F.C.rk ⊤ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 F.rk_pos.ne'
  show (2 * F.C.deg ⊤ + c * F.C.rk ⊤) / F.C.rk ⊤ = _
  field_simp

/-- **Invariance of the hypotheses**: the rescaled frame meets the hypotheses of the frame inequality with
`2s + c, 2U, 2H, α, β` iff the frame meets them with `s, U, H, α, β`. -/
theorem Frame.spread_rescale :
    (F.rescale c).Spread (2 * s + c) (2 * U) (2 * H) α β ↔ F.Spread s U H α β := by
  have hr : ∑ ω, (((F.rescale c).N ω).rk ⊤ : ℝ) = ∑ ω, ((F.N ω).rk ⊤ : ℝ) := rfl
  have hs := F.sum_rescale c
  have hle (ω : F.ι) : ((F.N ω).rescale c).SlopeLe (2 * s + c + 2 * U + 2 * F.h ω) ↔
      (F.N ω).SlopeLe (s + U + F.h ω) :=
    slopeLe_rescale.trans (by convert Iff.rfl using 2; ring)
  have hge : (F.C.rescale c).SlopeGe ⊤ (2 * s + c - 2 * H) ↔ F.C.SlopeGe ⊤ (s - H) :=
    slopeGe_rescale.trans (by convert Iff.rfl using 2; ring)
  constructor
  · rintro ⟨hU, hH, hβ, hmean, hrange, hdepth, hspread⟩
    exact ⟨by linarith, by linarith, hβ, by rw [hr] at hmean; linarith, fun ω => (hle ω).1 (hrange ω),
      hge.1 hdepth, hspread⟩
  · rintro ⟨hU, hH, hβ, hmean, hrange, hdepth, hspread⟩
    exact ⟨by linarith, by linarith, hβ, by rw [hr]; linarith, fun ω => (hle ω).2 (hrange ω), hge.2 hdepth,
      hspread⟩

/-- **Invariance of the conclusion**: the frame inequality for the rescaled frame, with `2s + c, 2U, 2H`, is
equivalent to the frame inequality for the frame, with `s, U, H`. -/
theorem Frame.loss_le_rescale_iff :
    2 * s + c - α * (2 * H) - β * (2 * U) * Real.log (1 + 2 * H / (2 * U)) ≤
        (F.rescale c).C.deg ⊤ / (F.rescale c).C.rk ⊤ ↔
      s - α * H - β * U * Real.log (1 + H / U) ≤ F.C.deg ⊤ / F.C.rk ⊤ := by
  rw [F.slope_rescale c, mul_div_mul_left _ _ two_ne_zero]
  constructor <;> intro h <;> linarith

/-- **The frame inequality in the archive's units**, a corollary of `Frame.Spread.loss_le` for the rescaled frame:
`μ'(C) ≥ s' − α·H' − β·U'·log(1 + H'/U')` with `μ' = 2μ + c`, `s' = 2s + c`, `U' = 2U`, `H' = 2H`. -/
theorem Frame.Spread.loss_le_rescale (h : F.Spread s U H α β) (c : ℝ) :
    2 * s + c - α * (2 * H) - β * (2 * U) * Real.log (1 + 2 * H / (2 * U)) ≤
      (F.rescale c).C.deg ⊤ / (F.rescale c).C.rk ⊤ :=
  (Frame.spread_rescale.2 h).loss_le

namespace SlopeLattice

variable {L : Type*} [Lattice L] [BoundedOrder L] (X : SlopeLattice L)

/-- The maximal slope `μ_max`: the supremum of the slopes `deg b/rk b` of the nonzero sublattices `b`. For (R),
spec L7.5. -/
noncomputable def muMax : ℝ :=
  ⨆ b : {b : L // b ≠ ⊥}, X.deg b / X.rk b

/-- The minimal slope `μ_min(a)`: the infimum of the slopes `(deg a − deg b)/(rk a − rk b)` of the nonzero quotients
`a/b`. For (R), spec L7.5. -/
noncomputable def muMin (a : L) : ℝ :=
  ⨅ b : {b : L // b < a}, (X.deg a - X.deg b) / ((X.rk a : ℝ) - X.rk b)

variable {X}

/-- A nonzero sublattice has positive rank. -/
theorem rk_pos {b : L} (hb : b ≠ ⊥) : (0 : ℝ) < X.rk b := by
  have := X.rk_strictMono (bot_lt_iff_ne_bot.2 hb)
  rw [X.rk_bot] at this
  exact_mod_cast this

/-- A nonzero quotient has positive rank. -/
theorem rk_sub_pos {a b : L} (hb : b < a) : (0 : ℝ) < (X.rk a : ℝ) - X.rk b :=
  sub_pos.2 (Nat.cast_lt.2 (X.rk_strictMono hb))

/-- **`μ_max` is the least `λ` with `SlopeLe λ`**, for a nonzero lattice whose slopes are bounded above. -/
theorem slopeLe_iff_muMax_le (hne : (⊥ : L) ≠ ⊤) (hB : ∃ lam₀, X.SlopeLe lam₀) {lam : ℝ} :
    X.SlopeLe lam ↔ X.muMax ≤ lam := by
  have : Nonempty {b : L // b ≠ ⊥} := ⟨⟨⊤, hne.symm⟩⟩
  have key (μ : ℝ) : X.SlopeLe μ ↔ ∀ b : {b : L // b ≠ ⊥}, X.deg b / X.rk b ≤ μ := by
    refine ⟨fun h b => (div_le_iff₀ (rk_pos b.2)).2 (h b), fun h b => ?_⟩
    obtain rfl | hb := eq_or_ne b ⊥
    · simp [X.rk_bot, X.deg_bot]
    · exact (div_le_iff₀ (rk_pos hb)).1 (h ⟨b, hb⟩)
  obtain ⟨lam₀, h₀⟩ := hB
  rw [key, muMax, ciSup_le_iff ⟨lam₀, Set.forall_mem_range.2 ((key lam₀).1 h₀)⟩]

/-- **`μ_min(a)` is the greatest `θ` with `SlopeGe a θ`**, for `a ≠ ⊥` whose quotient slopes are bounded below. -/
theorem slopeGe_iff_le_muMin {a : L} (ha : ⊥ < a) (hB : ∃ θ₀, X.SlopeGe a θ₀) {θ : ℝ} :
    X.SlopeGe a θ ↔ θ ≤ X.muMin a := by
  have : Nonempty {b : L // b < a} := ⟨⟨⊥, ha⟩⟩
  have key (θ : ℝ) : X.SlopeGe a θ ↔
      ∀ b : {b : L // b < a}, θ ≤ (X.deg a - X.deg b) / ((X.rk a : ℝ) - X.rk b) := by
    refine ⟨fun h b => (le_div_iff₀ (rk_sub_pos b.2)).2 (h b b.2.le), fun h b hb => ?_⟩
    obtain rfl | hb := hb.eq_or_lt
    · simp
    · exact (le_div_iff₀ (rk_sub_pos hb)).1 (h ⟨b, hb⟩)
  obtain ⟨θ₀, h₀⟩ := hB
  rw [key, muMin, le_ciInf_iff ⟨θ₀, Set.forall_mem_range.2 ((key θ₀).1 h₀)⟩]

/-- **`μ_min ≤ μ ≤ μ_max`** for a nonzero lattice with bounded slopes. -/
theorem muMin_le_slope_le_muMax (hne : (⊥ : L) ≠ ⊤) (hge : ∃ θ₀, X.SlopeGe ⊤ θ₀) (hle : ∃ lam₀, X.SlopeLe lam₀) :
    X.muMin ⊤ ≤ X.deg ⊤ / X.rk ⊤ ∧ X.deg ⊤ / X.rk ⊤ ≤ X.muMax := by
  have h1 := (slopeGe_iff_le_muMin (bot_lt_iff_ne_bot.2 hne.symm) hge).2 le_rfl ⊥ bot_le
  simp only [X.rk_bot, X.deg_bot, Nat.cast_zero, sub_zero] at h1
  exact ⟨(le_div_iff₀ (rk_pos hne.symm)).2 h1,
    (div_le_iff₀ (rk_pos hne.symm)).2 ((slopeLe_iff_muMax_le hne hle).2 le_rfl ⊤)⟩

/-- **`μ_max` rescales** as slopes do, `μ_max ↦ 2·μ_max + c`: a sanity check of `rescale` against `muMax`. -/
theorem muMax_rescale (hne : (⊥ : L) ≠ ⊤) (hB : ∃ lam₀, X.SlopeLe lam₀) (c : ℝ) :
    (X.rescale c).muMax = 2 * X.muMax + c := by
  obtain ⟨lam₀, h₀⟩ := hB
  have e (lam : ℝ) : (X.rescale c).SlopeLe (2 * lam + c) ↔ X.SlopeLe lam :=
    slopeLe_rescale.trans (by convert Iff.rfl using 2; ring)
  have hB' : ∃ lam₀, (X.rescale c).SlopeLe lam₀ := ⟨_, (e lam₀).2 h₀⟩
  refine le_antisymm ((slopeLe_iff_muMax_le hne hB').1 ((e _).2 ((slopeLe_iff_muMax_le hne ⟨_, h₀⟩).2 le_rfl))) ?_
  have h := (slopeLe_iff_muMax_le hne hB').2 le_rfl
  rw [slopeLe_rescale] at h
  linarith [(slopeLe_iff_muMax_le hne ⟨_, h₀⟩).1 h]

end SlopeLattice

end SlopeFrame

namespace HermitianLattice

open NumberField

variable {K ι : Type*} [Field K]

/-- The **dual** of an `𝓞 K`-lattice `M ⊆ K^ι`: `M^∨ = {f ∈ (K^ι)^* : f(M) ⊆ 𝓞 K}` (spec L1.3; for L6–L7). -/
def dual (M : Submodule (𝓞 K) (ι → K)) : Submodule (𝓞 K) (Module.Dual K (ι → K)) :=
  ⨅ x ∈ M, (1 : Submodule (𝓞 K) K).comap ((Module.Dual.eval K (ι → K) x).restrictScalars (𝓞 K))

/-- Membership in the dual. -/
theorem mem_dual {M : Submodule (𝓞 K) (ι → K)} {f : Module.Dual K (ι → K)} :
    f ∈ dual M ↔ ∀ x ∈ M, f x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [dual, Submodule.mem_iInf]

/-- Duality reverses inclusion: a sanity check of `dual`. -/
theorem dual_anti {M M' : Submodule (𝓞 K) (ι → K)} (h : M ≤ M') : dual M' ≤ dual M := fun _ hf =>
  mem_dual.2 fun x hx => mem_dual.1 hf x (h hx)

/-- The **saturation** of an `𝓞 K`-lattice `M ⊆ K^ι` in a subspace `W`: `M ∩ W`, the largest sublattice of `M` in
`W` (spec L1.3; for L6–L7). -/
def saturation (M : Submodule (𝓞 K) (ι → K)) (W : Submodule K (ι → K)) : Submodule (𝓞 K) (ι → K) :=
  M ⊓ W.restrictScalars (𝓞 K)

/-- Saturating in the whole space changes nothing: a sanity check of `saturation`. -/
theorem saturation_top (M : Submodule (𝓞 K) (ι → K)) : saturation M ⊤ = M := by
  simp [saturation]

end HermitianLattice
