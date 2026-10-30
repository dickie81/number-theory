import Mathlib

/-!
# Moments from counts of large values

Harman's moment lemma bounds `∫ |L|^δ` for a Dirichlet polynomial `L` through the number of well-spaced points at
which `|L|` is large. This module proves the two steps that turn such counts into a moment, for any function
`f : ℝ → ℝ≥0∞`:

* `volume_le_of_sep`: if every `1`-separated finite subset of `L ⊆ [a, b]` has at most `K` points, then `L` has
  measure at most `2K` (pick a point of `L` in each unit cell `[a + k, a + k + 1)` that meets it; the points of the
  even cells are `1`-separated, and so are those of the odd ones);
* `lintegral_rpow_le_levels`: for `f ≤ M` on `s`, `∫_s f^δ ≤ (M/2^J)^δ |s| + Σ_{j<J} (M/2^j)^δ |{f ≥ M/2^{j+1}} ∩ s|`;
* `lintegral_rpow_le_of_counts`: the two together on `[a, b]`, with a count `K j` of the `1`-separated points
  at which `f ≥ M/2^{j+1}`.
-/

open MeasureTheory Set Finset ENNReal

namespace ShortSieveLevel

/-- A finite set of reals is `1`-separated. -/
def Sep (R : Finset ℝ) : Prop := ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 1 ≤ |x - y|

/-- **The measure of a set from counts of separated points.** If every `1`-separated finite subset of
`L ⊆ [a, b]` has at most `K` points, then `L` has measure at most `2K`. -/
theorem volume_le_of_sep {a b : ℝ} {L : Set ℝ} (hL : L ⊆ Icc a b) {K : ℕ}
    (hK : ∀ R : Finset ℝ, (R : Set ℝ) ⊆ L → Sep R → R.card ≤ K) :
    volume L ≤ 2 * K := by
  classical
  set E : Finset ℕ := (range (⌊b - a⌋₊ + 1)).filter (fun k => ∃ t ∈ L, ⌊t - a⌋₊ = k) with hE
  have hex : ∀ k ∈ E, ∃ t ∈ L, ⌊t - a⌋₊ = k := fun k hk => (mem_filter.1 hk).2
  choose! pt hptL hptk using hex
  -- `L` lies in the union of the unit cells of `E`
  have hcover : L ⊆ ⋃ k ∈ E, Ico (a + k) (a + k + 1) := by
    intro t ht
    have hta : 0 ≤ t - a := sub_nonneg.2 (hL ht).1
    have htb : t - a ≤ b - a := sub_le_sub_right (hL ht).2 a
    refine mem_iUnion₂.2 ⟨⌊t - a⌋₊, mem_filter.2 ⟨mem_range.2 ?_, t, ht, rfl⟩, ?_⟩
    · have := Nat.floor_le_floor htb
      omega
    · have h1 := Nat.floor_le hta
      have h2 := Nat.lt_floor_add_one (t - a)
      constructor <;> linarith
  have hvol : volume L ≤ E.card := by
    calc volume L ≤ volume (⋃ k ∈ E, Ico (a + (k : ℝ)) (a + k + 1)) := measure_mono hcover
      _ ≤ ∑ k ∈ E, volume (Ico (a + (k : ℝ)) (a + k + 1)) := measure_biUnion_finset_le _ _
      _ = E.card := by simp [Real.volume_Ico]
  -- the chosen point of a cell lies in it
  have hcell : ∀ k ∈ E, (k : ℝ) ≤ pt k - a ∧ pt k - a < k + 1 := fun k hk => by
    have hta : 0 ≤ pt k - a := sub_nonneg.2 (hL (hptL k hk)).1
    have h1 := Nat.floor_le hta
    have h2 := Nat.lt_floor_add_one (pt k - a)
    rw [hptk k hk] at h1 h2
    exact ⟨h1, h2⟩
  have hinj : Set.InjOn pt E := fun k hk k' hk' h => by
    rw [← hptk k hk, ← hptk k' hk', h]
  -- cells two apart give `1`-separated points
  have hpar : ∀ (p : ℕ → Prop) [DecidablePred p],
      (∀ k k', p k → p k' → k < k' → k + 2 ≤ k') → (E.filter p).card ≤ K := by
    intro p _ hp
    have hsub : (((E.filter p).image pt : Finset ℝ) : Set ℝ) ⊆ L := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      exact hptL k (mem_filter.1 hk).1
    have hsep : Sep ((E.filter p).image pt) := by
      intro x hx y hy hxy
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
      obtain ⟨k', hk', rfl⟩ := mem_image.1 hy
      have hkk' : k ≠ k' := fun h => hxy (h ▸ rfl)
      obtain ⟨hk1, hk2⟩ := hcell k (mem_filter.1 hk).1
      obtain ⟨hk1', hk2'⟩ := hcell k' (mem_filter.1 hk').1
      rcases lt_or_gt_of_ne hkk' with h | h
      · have h2 : (k : ℝ) + 2 ≤ k' := by
          exact_mod_cast hp k k' (mem_filter.1 hk).2 (mem_filter.1 hk').2 h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have h2 : (k' : ℝ) + 2 ≤ k := by
          exact_mod_cast hp k' k (mem_filter.1 hk').2 (mem_filter.1 hk).2 h
        rw [abs_of_nonneg (by linarith)]
        linarith
    calc (E.filter p).card = ((E.filter p).image pt).card :=
          (card_image_of_injOn (hinj.mono (filter_subset _ _))).symm
      _ ≤ K := hK _ hsub hsep
  have heven := hpar (fun k => Even k) (fun k k' hk hk' h => by
    obtain ⟨i, rfl⟩ := hk
    obtain ⟨j, rfl⟩ := hk'
    omega)
  have hodd := hpar (fun k => ¬ Even k) (fun k k' hk hk' h => by
    rw [Nat.not_even_iff_odd] at hk hk'
    obtain ⟨i, rfl⟩ := hk
    obtain ⟨j, rfl⟩ := hk'
    omega)
  have hcard : E.card ≤ 2 * K := by
    have := card_filter_add_card_filter_not (s := E) (fun k => Even k)
    omega
  calc volume L ≤ E.card := hvol
    _ ≤ ((2 * K : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard
    _ = 2 * K := by push_cast; ring

/-- The pointwise form of the dyadic decomposition: for `x ≤ M`,
`x^δ ≤ (M/2^J)^δ + Σ_{j<J} (M/2^j)^δ·[x ≥ M/2^{j+1}]`. -/
theorem rpow_le_levels {x M : ℝ≥0∞} (hxM : x ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) :
    x ^ δ ≤ (M / 2 ^ J) ^ δ +
      ∑ j ∈ range J, {y : ℝ≥0∞ | M / 2 ^ (j + 1) ≤ y}.indicator (fun _ => (M / 2 ^ j) ^ δ) x := by
  induction J with
  | zero => simpa using ENNReal.rpow_le_rpow hxM hδ
  | succ J ih =>
    rw [sum_range_succ]
    by_cases hx : M / 2 ^ (J + 1) ≤ x
    · rw [indicator_of_mem (show x ∈ {y : ℝ≥0∞ | M / 2 ^ (J + 1) ≤ y} from hx)]
      calc x ^ δ ≤ (M / 2 ^ J) ^ δ + ∑ j ∈ range J,
            {y : ℝ≥0∞ | M / 2 ^ (j + 1) ≤ y}.indicator (fun _ => (M / 2 ^ j) ^ δ) x := ih
        _ ≤ _ := by
          rw [add_comm ((M / 2 ^ J) ^ δ)]
          exact le_add_left le_rfl
    · have hlt : x ≤ M / 2 ^ (J + 1) := (not_le.1 hx).le
      calc x ^ δ ≤ (M / 2 ^ (J + 1)) ^ δ := ENNReal.rpow_le_rpow hlt hδ
        _ ≤ _ := le_self_add

/-- **Moments from the measures of level sets.** For `f ≤ M` on a measurable set `s`,
`∫_s f^δ ≤ (M/2^J)^δ |s| + Σ_{j<J} (M/2^j)^δ |{f ≥ M/2^{j+1}} ∩ s|`. -/
theorem lintegral_rpow_le_levels {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {M : ℝ≥0∞} (hfM : ∀ t ∈ s, f t ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) :
    ∫⁻ t in s, f t ^ δ ≤ (M / 2 ^ J) ^ δ * volume s +
      ∑ j ∈ range J, (M / 2 ^ j) ^ δ * volume ({t | M / 2 ^ (j + 1) ≤ f t} ∩ s) := by
  have hE : ∀ j : ℕ, MeasurableSet {t | M / 2 ^ (j + 1) ≤ f t} := fun j =>
    measurableSet_le measurable_const hf
  calc ∫⁻ t in s, f t ^ δ ≤ ∫⁻ t in s, ((M / 2 ^ J) ^ δ +
        ∑ j ∈ range J, {t | M / 2 ^ (j + 1) ≤ f t}.indicator (fun _ => (M / 2 ^ j) ^ δ) t) :=
        setLIntegral_mono' hs fun t ht => rpow_le_levels (hfM t ht) hδ J
    _ = (M / 2 ^ J) ^ δ * volume s +
        ∑ j ∈ range J, (M / 2 ^ j) ^ δ * volume ({t | M / 2 ^ (j + 1) ≤ f t} ∩ s) := by
      rw [lintegral_add_left measurable_const, setLIntegral_const,
        lintegral_finsetSum _ fun j _ => measurable_const.indicator (hE j)]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [lintegral_indicator_const (hE j), Measure.restrict_apply (hE j)]

/-- **Moments from counts of large values.** For `f ≤ M` on `[a, b]`, if at most `K j` points `1`-separated in
`[a, b]` have `f ≥ M/2^{j+1}`, then `∫_a^b f^δ ≤ (M/2^J)^δ (b − a) + Σ_{j<J} (M/2^j)^δ · 2K j`. -/
theorem lintegral_rpow_le_of_counts {a b : ℝ} {f : ℝ → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞}
    (hfM : ∀ t ∈ Icc a b, f t ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) (K : ℕ → ℕ)
    (hK : ∀ j < J, ∀ R : Finset ℝ, (R : Set ℝ) ⊆ Icc a b → Sep R → (∀ x ∈ R, M / 2 ^ (j + 1) ≤ f x) →
      R.card ≤ K j) :
    ∫⁻ t in Icc a b, f t ^ δ ≤ (M / 2 ^ J) ^ δ * ENNReal.ofReal (b - a) +
      ∑ j ∈ range J, (M / 2 ^ j) ^ δ * (2 * K j) := by
  refine (lintegral_rpow_le_levels measurableSet_Icc hf hfM hδ J).trans ?_
  rw [Real.volume_Icc]
  gcongr with j hj
  refine volume_le_of_sep inter_subset_right fun R hR hsep => hK j (mem_range.1 hj) R
    (hR.trans inter_subset_right) hsep fun x hx => (hR (mem_coe.2 hx)).1

end ShortSieveLevel
