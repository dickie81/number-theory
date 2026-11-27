import ProdWeights
import DesignTiles

/-!
# The tile condition under independent selection

A step of the proof of the sharp frontier (`SharpInputs`, the design's Stage 2): the probability that a forced top
lies on a bad orbit, when the tops are drawn independently (`ProdWeights`) with probabilities `q ∈ [3δ/4, δ]`. Generic:
an orbit is a map `e : ℕ → α` injective on `[0, n′)`, and the positions of `T` on it are
`orbPos n′ e T = {i < n′ : e i ∈ T}` (for the design, `TopsSelect` takes `e i = t₀σ^i`, where this is `topPositions`).

**A marked block** (`pexp_marked_ge`) has probability at least `μ = 10^{−(6r+1)}`. The block holds `6r + 1` cells of
`u` positions with disjoint point sets (`cellSet`), and the block is marked when every cell meets its event
(`cellInd`): an odd cell holds no point of `T`, an even cell exactly one, at an even position. The events are local to
their cells, so independent (`pexp_prod_local`). An odd cell is empty with probability `∏(1 − q) ≥ (1 − δ)^u`; an even
cell holds exactly the point at an even position `j` with probability `q_{e j}·∏_{others}(1 − q) ≥ (3δ/4)(1 − δ)^{u−1}`,
and there are at least `⌊u/2⌋ ≥ (u − 1)/2` such `j` (`card_even_Ico`). With `1/δ ≤ u ≤ 1/δ + 1` both are at least
`(3/8)(1 − δ)^u ≥ 1/8`, as `(1 − δ)^u ≥ e^{−uδ/(1−δ)} ≥ e^{−1.03} ≥ 1/3` for `δ ≤ 1/100` (`one_third_le_pow`).

**A forced top on a bad orbit** (`pexp_forced_bad_le`): `P(e i₀ ∈ T, P not good) ≤ δn′((A) + (T) + (I))`, a union
bound over the three parts of `TilePar.IsGood`.
* (A): a window of `L₂ ≤ n′` positions holds `L₂` distinct points (`winCard_le`), so more than `K` tops in it is
  `|T ∩ W| ≥ K + 1`, of probability `≤ δ(C(L₂, K)δ^K + C(L₂, K+1)δ^{K+1}) ≤ δC(L₂ + 1, K + 1)δ^K` with the forced point
  (`pexp_forced_window_le`, Pascal); `n′` windows.
* (I): the same with `G′ ≤ n′` and `N₁ + 1`.
* (T): a run of `M₀ + 1 ≤ B = ⌊n′/((6r + 1)u)⌋` blocks holds `M₀ + 1` distinct blocks; dropping the block of `i₀`,
  the forced point and the `≥ M₀` unmarked blocks are local to disjoint sets, so the probability is at most
  `δ(1 − μ)^{M₀}`; `B ≤ n′` runs.
-/

open Finset

namespace ZetaBalance

namespace ProdWeights

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The positions of `T` on an orbit `e` of length `n′`: `{i < n′ : e i ∈ T}`. -/
def orbPos (n' : ℕ) (e : ℕ → α) (T : Finset α) : Finset ℕ := (range n').filter fun i => e i ∈ T

/-! ## Small facts -/

/-- **`(1 − δ)^n ≥ 1/3`** for `0 < δ ≤ 1/100` and `nδ ≤ 1 + δ`: `1 − δ ≥ e^{−y}` with `y = δ/(1 − δ)`
(`Real.add_one_le_exp`), `ny ≤ 1.03`, and `e^{−1.03} ≥ 0.97/e ≥ 1/3` (`Real.exp_one_lt_d9`). -/
theorem one_third_le_pow {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 100) {n : ℕ} (hn : n * δ ≤ 1 + δ) :
    1 / 3 ≤ (1 - δ) ^ n := by
  have h1δ : 0 < 1 - δ := by linarith
  have hexp : Real.exp (-(δ / (1 - δ))) ≤ 1 - δ := by
    have h := Real.add_one_le_exp (δ / (1 - δ))
    have e : δ / (1 - δ) + 1 = (1 - δ)⁻¹ := by field_simp; ring
    rw [e] at h
    rw [Real.exp_neg]
    calc (Real.exp (δ / (1 - δ)))⁻¹ ≤ ((1 - δ)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 h1δ) h
      _ = 1 - δ := inv_inv _
  have hny : n * (δ / (1 - δ)) ≤ 103 / 100 := by
    rw [← mul_div_assoc, div_le_iff₀ h1δ]
    nlinarith
  have he1 : 1 / 2.7182818286 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) Real.exp_one_lt_d9.le
  have he2 : 1 - 3 / 100 ≤ Real.exp (-(3 / 100)) := by linarith [Real.add_one_le_exp (-(3 / 100 : ℝ))]
  calc (1 : ℝ) / 3 ≤ 1 / 2.7182818286 * (1 - 3 / 100) := by norm_num
    _ ≤ Real.exp (-1) * Real.exp (-(3 / 100)) := mul_le_mul he1 he2 (by norm_num) (Real.exp_pos _).le
    _ = Real.exp (-(103 / 100)) := by rw [← Real.exp_add]; norm_num
    _ ≤ Real.exp (-(n * (δ / (1 - δ)))) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-(δ / (1 - δ))) ^ n := by rw [← Real.exp_nat_mul, mul_neg]
    _ ≤ (1 - δ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hexp n

/-- The mean of `1 − F`. -/
theorem pexp_one_sub (q : α → ℝ) (F : Finset α → ℝ) : pexp q (fun T => 1 - F T) = 1 - pexp q F := by
  have e : (fun T => 1 - F T) = fun T => 1 + (-1) * F T := by
    funext T
    ring
  rw [e, pexp_add, pexp_const_mul, pexp_const]
  ring

omit [Fintype α] in
/-- A function local to `S` is local to every `S′ ⊇ S`. -/
theorem IsLocal.mono {S S' : Finset α} {F : Finset α → ℝ} (hF : IsLocal S F) (h : S ⊆ S') : IsLocal S' F :=
  fun T => by rw [hF T, hF (T ∩ S'), inter_assoc, inter_eq_right.2 h]

omit [Fintype α] in
/-- `1 − F` is local where `F` is. -/
theorem IsLocal.one_sub {S : Finset α} {F : Finset α → ℝ} (hF : IsLocal S F) : IsLocal S (fun T => 1 - F T) :=
  fun T => by
    show 1 - F T = 1 - F (T ∩ S)
    rw [hF T]

/-- **At least `⌊u/2⌋` even numbers** in `[s, s + u)`: `s + (s mod 2) + 2k` for `k < ⌊u/2⌋`. -/
theorem card_even_Ico (s u : ℕ) : u / 2 ≤ ((Ico s (s + u)).filter Even).card := by
  have hmap : ((range (u / 2)).image fun k => s + s % 2 + 2 * k) ⊆ (Ico s (s + u)).filter Even := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hj
    rw [mem_range] at hk
    rw [mem_filter, mem_Ico]
    exact ⟨⟨by omega, by omega⟩, Nat.even_iff.2 (by omega)⟩
  calc u / 2 = ((range (u / 2)).image fun k => s + s % 2 + 2 * k).card := by
        rw [card_image_of_injective _ (fun k₁ k₂ h => by omega), card_range]
    _ ≤ _ := card_le_card hmap

omit [Fintype α] in
/-- **Images of disjoint position sets are disjoint** under a map injective on `[0, n′)`. -/
theorem disjoint_image_of_lt {e : ℕ → α} {n' : ℕ} (he : Set.InjOn e (Set.Iio n')) {s t : Finset ℕ}
    (hs : ∀ j ∈ s, j < n') (ht : ∀ j ∈ t, j < n') (hd : Disjoint s t) : Disjoint (s.image e) (t.image e) := by
  rw [disjoint_left]
  intro a ha ha'
  obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
  obtain ⟨j', hj', hjj⟩ := mem_image.1 ha'
  have h : j' = j := he (Set.mem_Iio.2 (ht j' hj')) (Set.mem_Iio.2 (hs j hj)) hjj
  exact disjoint_left.1 hd hj (h ▸ hj')

/-! ## Cells and blocks -/

section Cells

variable (Tp : TilePar) (e : ℕ → α)

/-- The positions of the cell `i` of the block `b` (those of `TilePar.cellPts`). -/
def cellIco (b i : ℕ) : Finset ℕ := Ico (b * Tp.blockLen + i * Tp.u) (b * Tp.blockLen + (i + 1) * Tp.u)

/-- The points of the cell `i` of the block `b`. -/
def cellSet (b i : ℕ) : Finset α := (cellIco Tp b i).image e

/-- The positions of the block `b`. -/
def blockIco (b : ℕ) : Finset ℕ := Ico (b * Tp.blockLen) (b * Tp.blockLen + Tp.blockLen)

/-- The points of the block `b`. -/
def blockSet (b : ℕ) : Finset α := (blockIco Tp b).image e

/-- **The cell event**: an odd cell holds no point of `T`; an even cell holds exactly one, `e j` with `j` even. -/
def cellInd (b i : ℕ) (T : Finset α) : ℝ :=
  if Odd i then (if T ∩ cellSet Tp e b i = ∅ then 1 else 0)
  else ∑ j ∈ (cellIco Tp b i).filter Even, if T ∩ cellSet Tp e b i = {e j} then 1 else 0

/-- **The block event**: every cell of the block meets its event. -/
def blockInd (b : ℕ) (T : Finset α) : ℝ := ∏ i ∈ range (6 * Tp.r + 1), cellInd Tp e b i T

variable {Tp e}

/-- A block below `B = ⌊n′/((6r + 1)u)⌋` lies in `[0, n′)`. -/
theorem lt_of_mem_blockIco {n' b j : ℕ} (hb : b < n' / Tp.blockLen) (hj : j ∈ blockIco Tp b) : j < n' := by
  have hb' : b + 1 ≤ n' / Tp.blockLen := hb
  have h2 : (b + 1) * Tp.blockLen ≤ n' := (Nat.mul_le_mul_right _ hb').trans (Nat.div_mul_le_self _ _)
  rw [add_mul, one_mul] at h2
  have := (mem_Ico.1 hj).2
  omega

/-- The cells of a block lie in it. -/
theorem cellIco_subset {b i : ℕ} (hi : i < 6 * Tp.r + 1) : cellIco Tp b i ⊆ blockIco Tp b := by
  intro j hj
  have h1 : (i + 1) * Tp.u ≤ Tp.blockLen := Nat.mul_le_mul_right _ (by omega)
  rw [cellIco, mem_Ico] at hj
  rw [blockIco, mem_Ico]
  exact ⟨by omega, by omega⟩

/-- Distinct cells of a block are disjoint. -/
theorem disjoint_cellIco {b i i' : ℕ} (h : i ≠ i') : Disjoint (cellIco Tp b i) (cellIco Tp b i') := by
  rw [disjoint_left]
  intro j hj hj'
  rw [cellIco, mem_Ico] at hj hj'
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (i + 1) * Tp.u ≤ i' * Tp.u := Nat.mul_le_mul_right _ h'
    omega
  · have : (i' + 1) * Tp.u ≤ i * Tp.u := Nat.mul_le_mul_right _ h'
    omega

/-- Distinct blocks are disjoint. -/
theorem disjoint_blockIco {b b' : ℕ} (h : b ≠ b') : Disjoint (blockIco Tp b) (blockIco Tp b') := by
  rw [disjoint_left]
  intro j hj hj'
  rw [blockIco, mem_Ico] at hj hj'
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (b + 1) * Tp.blockLen ≤ b' * Tp.blockLen := Nat.mul_le_mul_right _ h'
    rw [add_mul, one_mul] at this
    omega
  · have : (b' + 1) * Tp.blockLen ≤ b * Tp.blockLen := Nat.mul_le_mul_right _ h'
    rw [add_mul, one_mul] at this
    omega

/-- A position of the block `b` determines `b`. -/
theorem div_eq_of_mem_blockIco {b j : ℕ} (hj : j ∈ blockIco Tp b) : j / Tp.blockLen = b := by
  rw [blockIco, mem_Ico] at hj
  have hpos : 0 < Tp.blockLen := by omega
  refine le_antisymm ?_ ((Nat.le_div_iff_mul_le hpos).2 hj.1)
  have : j < (b + 1) * Tp.blockLen := by rw [add_mul, one_mul]; exact hj.2
  exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hpos).2 this)

omit [Fintype α] in
/-- The cell has `u` points. -/
theorem card_cellSet {n' b i : ℕ} (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen)
    (hi : i < 6 * Tp.r + 1) : (cellSet Tp e b i).card = Tp.u := by
  rw [cellSet, card_image_of_injOn (he.mono fun j hj => Set.mem_Iio.2 (lt_of_mem_blockIco hb
    (cellIco_subset hi hj))), cellIco, Nat.card_Ico]
  rw [add_mul, one_mul]
  omega

omit [Fintype α] in
/-- The cell event depends only on the cell. -/
theorem isLocal_cellInd (b i : ℕ) : IsLocal (cellSet Tp e b i) (cellInd Tp e b i) := fun T => by
  unfold cellInd
  rw [inter_assoc, inter_self]

omit [Fintype α] in
/-- The cell event is nonnegative. -/
theorem cellInd_nonneg (b i : ℕ) (T : Finset α) : 0 ≤ cellInd Tp e b i T := by
  unfold cellInd
  split_ifs
  · norm_num
  · norm_num
  · exact sum_nonneg fun j _ => by split_ifs <;> norm_num

omit [Fintype α] in
/-- **The cell event is an indicator**: at most one `e j` can be the only point of the cell. -/
theorem cellInd_le_one {n' b i : ℕ} (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen)
    (hi : i < 6 * Tp.r + 1) (T : Finset α) : cellInd Tp e b i T ≤ 1 := by
  unfold cellInd
  split_ifs
  · norm_num
  · norm_num
  · by_cases h : ∃ j ∈ (cellIco Tp b i).filter Even, T ∩ cellSet Tp e b i = {e j}
    · obtain ⟨j₀, hj₀, hT⟩ := h
      rw [sum_eq_single_of_mem j₀ hj₀ fun j hj hne => ?_]
      · rw [ite_eq_left hT]
      · rw [ite_eq_right]
        intro hT'
        have hlt : ∀ j ∈ (cellIco Tp b i).filter Even, j ∈ Set.Iio n' := fun j hj =>
          Set.mem_Iio.2 (lt_of_mem_blockIco hb (cellIco_subset hi (mem_filter.1 hj).1))
        exact hne (he (hlt j hj) (hlt j₀ hj₀) (singleton_injective (hT'.symm.trans hT)))
    · push Not at h
      rw [sum_eq_zero fun j hj => ite_eq_right (h j hj)]
      norm_num

omit [Fintype α] in
/-- **A nonzero cell event gives the cell's clause of `TilePar.Marked`** on the positions of `T`. -/
theorem cellInd_ne_zero {n' b i : ℕ} (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen)
    (hi : i < 6 * Tp.r + 1) {T : Finset α} (h : cellInd Tp e b i T ≠ 0) :
    (Odd i → Tp.cellPts (orbPos n' e T) b i = ∅) ∧
      (Even i → ∃ q, Even q ∧ Tp.cellPts (orbPos n' e T) b i = {q}) := by
  have hlt : ∀ j ∈ cellIco Tp b i, j < n' := fun j hj => lt_of_mem_blockIco hb (cellIco_subset hi hj)
  have hcp : Tp.cellPts (orbPos n' e T) b i = (cellIco Tp b i).filter fun j => e j ∈ T :=
    filter_congr fun j hj => by simp [orbPos, hlt j hj]
  unfold cellInd at h
  constructor
  · intro hodd
    rw [ite_eq_left hodd] at h
    have hT : T ∩ cellSet Tp e b i = ∅ := by
      by_contra hc
      exact h (ite_eq_right hc)
    rw [hcp, filter_eq_empty_iff]
    intro j hj hjT
    have hm : e j ∈ T ∩ cellSet Tp e b i := mem_inter.2 ⟨hjT, mem_image_of_mem e hj⟩
    rw [hT] at hm
    exact notMem_empty _ hm
  · intro hev
    rw [ite_eq_right (Nat.not_odd_iff_even.2 hev)] at h
    obtain ⟨j₀, hj₀, hne⟩ := exists_ne_zero_of_sum_ne_zero h
    have hT : T ∩ cellSet Tp e b i = {e j₀} := by
      by_contra hc
      exact hne (ite_eq_right hc)
    obtain ⟨hj₀I, hj₀e⟩ := mem_filter.1 hj₀
    refine ⟨j₀, hj₀e, ?_⟩
    rw [hcp]
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hj, hjT⟩
      have hm : e j ∈ T ∩ cellSet Tp e b i := mem_inter.2 ⟨hjT, mem_image_of_mem e hj⟩
      rw [hT, mem_singleton] at hm
      exact he (Set.mem_Iio.2 (hlt j hj)) (Set.mem_Iio.2 (hlt j₀ hj₀I)) hm
    · rintro rfl
      have hm : e j ∈ T ∩ cellSet Tp e b i := by
        rw [hT]
        exact mem_singleton_self _
      exact ⟨hj₀I, (mem_inter.1 hm).1⟩

omit [Fintype α] in
/-- **A nonzero block event marks the block.** -/
theorem marked_of_blockInd_ne_zero {n' b : ℕ} (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen)
    {T : Finset α} (h : blockInd Tp e b T ≠ 0) : Tp.Marked (orbPos n' e T) b := fun i hi =>
  cellInd_ne_zero he hb hi (prod_ne_zero_iff.1 h i (mem_range.2 hi))

omit [Fintype α] in
/-- The block event is nonnegative. -/
theorem blockInd_nonneg (b : ℕ) (T : Finset α) : 0 ≤ blockInd Tp e b T :=
  prod_nonneg fun i _ => cellInd_nonneg b i T

omit [Fintype α] in
/-- The block event is at most `1`. -/
theorem blockInd_le_one {n' b : ℕ} (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen) (T : Finset α) :
    blockInd Tp e b T ≤ 1 :=
  prod_le_one₀ (fun i _ => cellInd_nonneg b i T) fun _ hi => cellInd_le_one he hb (mem_range.1 hi) T

omit [Fintype α] in
/-- The block event depends only on the block. -/
theorem isLocal_blockInd (b : ℕ) : IsLocal (blockSet Tp e b) (blockInd Tp e b) := by
  have h := IsLocal.prod (range (6 * Tp.r + 1)) (cellSet Tp e b) (cellInd Tp e b) fun i _ => isLocal_cellInd b i
  refine h.mono ?_
  intro a ha
  obtain ⟨i, hi, ha⟩ := mem_biUnion.1 ha
  obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
  exact mem_image_of_mem e (cellIco_subset (mem_range.1 hi) hj)

/-- **A cell event has probability at least `1/8`**: an odd cell is empty with probability `≥ (1 − δ)^u ≥ 1/3`; an
even cell holds exactly `e j` for one of its `≥ ⌊u/2⌋` even `j`, each with probability `≥ (3δ/4)(1 − δ)^{u−1}`, in
all `≥ (3/8)(1 − δ)^u`. -/
theorem pexp_cellInd_ge {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' b i : ℕ}
    (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen) (hi : i < 6 * Tp.r + 1) :
    1 / 8 ≤ pexp q (cellInd Tp e b i) := by
  have h1δ : 1 / δ * δ = 1 := one_div_mul_cancel hδ.ne'
  have hu0' : (1 : ℝ) ≤ Tp.u := le_trans (by rw [le_div_iff₀ hδ]; linarith) hu1
  have hu0 : 1 ≤ Tp.u := by exact_mod_cast hu0'
  have huδ : 1 ≤ Tp.u * δ := by nlinarith
  have huδ' : Tp.u * δ ≤ 1 + δ := by nlinarith
  have hpow : 1 / 3 ≤ (1 - δ) ^ Tp.u := one_third_le_pow hδ hδ' huδ'
  have hC := card_cellSet he hb hi
  have hprod : ∀ U : Finset α, (1 - δ) ^ U.card ≤ ∏ a ∈ U, (1 - q a) := fun U => by
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => by linarith) (fun a _ => by linarith [(hq a).2])
  by_cases hodd : Odd i
  · have e1 : cellInd Tp e b i = fun T => if T ∩ cellSet Tp e b i = ∅ then 1 else 0 := by
      funext T
      simp [cellInd, hodd]
    rw [e1, pexp_inter_eq q (empty_subset _), prod_empty, one_mul, sdiff_empty]
    calc (1 : ℝ) / 8 ≤ (1 - δ) ^ Tp.u := by linarith
      _ = (1 - δ) ^ (cellSet Tp e b i).card := by rw [hC]
      _ ≤ _ := hprod _
  · have e1 : cellInd Tp e b i = fun T => ∑ j ∈ (cellIco Tp b i).filter Even,
        if T ∩ cellSet Tp e b i = {e j} then 1 else 0 := by
      funext T
      simp [cellInd, hodd]
    rw [e1, pexp_sum]
    have hX0 : 0 ≤ (1 - δ) ^ (Tp.u - 1) := pow_nonneg (by linarith) _
    have hterm : ∀ j ∈ (cellIco Tp b i).filter Even, 3 * δ / 4 * (1 - δ) ^ (Tp.u - 1) ≤
        pexp q (fun T => if T ∩ cellSet Tp e b i = {e j} then 1 else 0) := by
      intro j hj
      have hjC : e j ∈ cellSet Tp e b i := mem_image_of_mem e (mem_filter.1 hj).1
      rw [pexp_inter_eq q (singleton_subset_iff.2 hjC), prod_singleton]
      have hcard : (cellSet Tp e b i \ {e j}).card = Tp.u - 1 := by
        rw [card_sdiff_of_subset (singleton_subset_iff.2 hjC), hC, card_singleton]
      refine mul_le_mul (hq _).1 ?_ hX0 (by linarith [(hq (e j)).1])
      rw [← hcard]
      exact hprod _
    have hsplit : (1 - δ) ^ Tp.u = (1 - δ) * (1 - δ) ^ (Tp.u - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hu0]
    have hdiv : ((Tp.u : ℝ) - 1) / 2 ≤ ((Tp.u / 2 : ℕ) : ℝ) := by
      have h1 := Nat.div_add_mod Tp.u 2
      have h2 := Nat.mod_lt Tp.u (show 0 < 2 by norm_num)
      have h3 : (Tp.u : ℝ) = 2 * (Tp.u / 2 : ℕ) + (Tp.u % 2 : ℕ) := by exact_mod_cast h1.symm
      have h4 : ((Tp.u % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 h2
      linarith
    have hev : Tp.u / 2 ≤ ((cellIco Tp b i).filter Even).card := by
      have e2 : cellIco Tp b i = Ico (b * Tp.blockLen + i * Tp.u) (b * Tp.blockLen + i * Tp.u + Tp.u) := by
        rw [cellIco, add_mul, one_mul, add_assoc]
      rw [e2]
      exact card_even_Ico _ _
    have hev' : ((Tp.u / 2 : ℕ) : ℝ) ≤ (((cellIco Tp b i).filter Even).card : ℝ) := by exact_mod_cast hev
    calc (1 : ℝ) / 8 ≤ 3 / 8 * (1 - δ) ^ Tp.u := by linarith
      _ = 3 / 8 * (1 - δ) * (1 - δ) ^ (Tp.u - 1) := by rw [hsplit]; ring
      _ ≤ ((Tp.u : ℝ) - 1) / 2 * (3 * δ / 4) * (1 - δ) ^ (Tp.u - 1) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hX0
      _ ≤ (((cellIco Tp b i).filter Even).card : ℝ) * (3 * δ / 4 * (1 - δ) ^ (Tp.u - 1)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hdiv.trans hev') (mul_nonneg (by positivity) hX0)
      _ = ∑ _j ∈ (cellIco Tp b i).filter Even, 3 * δ / 4 * (1 - δ) ^ (Tp.u - 1) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hterm

/-- **A block event has probability at least `10^{−(6r+1)}`**: its cells are independent (`pexp_prod_local`). -/
theorem pexp_blockInd_ge {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' b : ℕ}
    (he : Set.InjOn e (Set.Iio n')) (hb : b < n' / Tp.blockLen) :
    (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) ≤ pexp q (blockInd Tp e b) := by
  have hdisj : ((range (6 * Tp.r + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (cellSet Tp e b) := by
    intro i hi i' hi' hne
    exact disjoint_image_of_lt he (fun j hj => lt_of_mem_blockIco hb (cellIco_subset (mem_range.1 hi) hj))
      (fun j hj => lt_of_mem_blockIco hb (cellIco_subset (mem_range.1 hi') hj)) (disjoint_cellIco hne)
  rw [show blockInd Tp e b = fun T => ∏ i ∈ range (6 * Tp.r + 1), cellInd Tp e b i T from rfl,
    pexp_prod_local q _ _ hdisj _ fun i _ => isLocal_cellInd b i]
  calc (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) = ∏ _i ∈ range (6 * Tp.r + 1), (10 : ℝ)⁻¹ := by rw [prod_const, card_range]
    _ ≤ _ := prod_le_prod₀ (fun _ _ => by norm_num) fun i hi =>
        (by norm_num : (10 : ℝ)⁻¹ ≤ 1 / 8).trans (pexp_cellInd_ge hq hδ hδ' hu1 hu2 he hb (mem_range.1 hi))

end Cells

open scoped Classical in
/-- **A marked block** has probability `≥ 10^{−(6r+1)}`: each cell `≥ 1/10` (odd: empty, `≥ (1 − δ)^u`; even: one
point at an even position, `≥ ⌊u/2⌋(3δ/4)(1 − δ)^{u−1}`), cells independent. -/
theorem pexp_marked_ge {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (Tp : TilePar) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' : ℕ}
    {e : ℕ → α} (he : Set.InjOn e (Set.Iio n')) {b : ℕ} (hb : b < n' / Tp.blockLen) :
    (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) ≤ pexp q (fun T => if Tp.Marked (orbPos n' e T) b then 1 else 0) := by
  have hq' : IsProb q := fun a => ⟨by linarith [(hq a).1], by linarith [(hq a).2]⟩
  refine (pexp_blockInd_ge hq hδ hδ' hu1 hu2 he hb).trans (pexp_mono hq' fun T => ?_)
  split_ifs with h
  · exact blockInd_le_one he hb T
  · refine le_of_not_gt fun hc => h (marked_of_blockInd_ne_zero he hb (ne_of_gt hc))

/-! ## A forced top on a bad orbit -/

/-- The points of the cyclic window of `L` positions from `s`. -/
def winSet (e : ℕ → α) (n' s L : ℕ) : Finset α := (range L).image fun j => e ((s + j) % n')

/-- The blocks of the run of `M₀ + 1` blocks from `b₀`, cyclically among the `B = ⌊n′/((6r + 1)u)⌋`, without the
block of `i₀`. -/
def runSet (Tp : TilePar) (n' i₀ b₀ : ℕ) : Finset ℕ :=
  ((range (Tp.M₀ + 1)).image fun j => (b₀ + j) % (n' / Tp.blockLen)).erase (i₀ / Tp.blockLen)

/-- **The union bound** of a forced top on a bad orbit: the windows (A), the runs (T), the windows (I). -/
def badBound (Tp : TilePar) (e : ℕ → α) (n' i₀ : ℕ) (T : Finset α) : ℝ :=
  ∑ s ∈ range n', (if e i₀ ∈ T ∧ Tp.K + 1 ≤ (T ∩ winSet e n' s Tp.L₂).card then 1 else 0) +
    (∑ b₀ ∈ range (n' / Tp.blockLen),
        (if e i₀ ∈ T then 1 else 0) * ∏ b ∈ runSet Tp n' i₀ b₀, (1 - blockInd Tp e b T) +
      ∑ s ∈ range n', (if e i₀ ∈ T ∧ Tp.N₁ + 1 ≤ (T ∩ winSet e n' s Tp.G').card then 1 else 0))

omit [Fintype α] in
/-- **A window holds distinct points**: for `L ≤ n′`, the points of `orbPos n′ e T` in the cyclic window of `L`
positions from `s` number at most `|T ∩ winSet e n′ s L|`. -/
theorem winCard_le {n' : ℕ} {e : ℕ → α} (he : Set.InjOn e (Set.Iio n')) {s L : ℕ} (hL : L ≤ n')
    (T : Finset α) : winCard n' (orbPos n' e T) s L ≤ (T ∩ winSet e n' s L).card := by
  rcases Nat.eq_zero_or_pos n' with hn | hn
  · subst hn
    obtain rfl : L = 0 := by omega
    simp [winCard]
  refine card_le_card_of_injOn (fun j => e ((s + j) % n')) (fun j hj => ?_) (fun j₁ hj₁ j₂ hj₂ h => ?_)
  · obtain ⟨hjL, hjP⟩ := mem_filter.1 hj
    simp only [orbPos, mem_filter] at hjP
    exact mem_inter.2 ⟨hjP.2, mem_image_of_mem _ hjL⟩
  · have h1 := mem_range.1 (mem_filter.1 hj₁).1
    have h2 := mem_range.1 (mem_filter.1 hj₂).1
    have hm : (s + j₁) % n' = (s + j₂) % n' :=
      he (Set.mem_Iio.2 (Nat.mod_lt _ hn)) (Set.mem_Iio.2 (Nat.mod_lt _ hn)) h
    have := Nat.ModEq.add_left_cancel' s hm
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

variable {Tp : TilePar} {e : ℕ → α}

omit [Fintype α] in
/-- The blocks of a run lie below `B`. -/
theorem lt_of_mem_runSet {n' i₀ b₀ b : ℕ} (hb₀ : b₀ < n' / Tp.blockLen) (hb : b ∈ runSet Tp n' i₀ b₀) :
    b < n' / Tp.blockLen := by
  obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
  exact Nat.mod_lt _ (by omega)

omit [Fintype α] in
/-- A run holds `M₀ + 1` distinct blocks, so at least `M₀` without the block of `i₀`. -/
theorem le_card_runSet {n' i₀ b₀ : ℕ} (hMB : Tp.M₀ + 1 ≤ n' / Tp.blockLen) : Tp.M₀ ≤ (runSet Tp n' i₀ b₀).card := by
  have hinj : Set.InjOn (fun j => (b₀ + j) % (n' / Tp.blockLen)) (range (Tp.M₀ + 1) : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ h
    have h1 := mem_range.1 hj₁
    have h2 := mem_range.1 hj₂
    have := Nat.ModEq.add_left_cancel' b₀ h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have h := pred_card_le_card_erase (s := (range (Tp.M₀ + 1)).image fun j => (b₀ + j) % (n' / Tp.blockLen))
    (a := i₀ / Tp.blockLen)
  rw [card_image_of_injOn hinj, card_range, Nat.add_sub_cancel] at h
  exact h

/-- **A run without a marked block**: `E[1_{e i₀ ∈ T}·∏_{b ∈ run}(1 − [b marked])] ≤ δ(1 − μ)^{M₀}`, `μ = 10^{−(6r+1)}`.
The forced point and the blocks of the run (without the block of `i₀`) are local to disjoint sets. -/
theorem pexp_run_le {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' : ℕ}
    (he : Set.InjOn e (Set.Iio n')) {i₀ : ℕ} (hi₀ : i₀ < n') (hMB : Tp.M₀ + 1 ≤ n' / Tp.blockLen) {b₀ : ℕ}
    (hb₀ : b₀ < n' / Tp.blockLen) :
    pexp q (fun T => (if e i₀ ∈ T then 1 else 0) * ∏ b ∈ runSet Tp n' i₀ b₀, (1 - blockInd Tp e b T)) ≤
      δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀ := by
  have hq' : IsProb q := fun a => ⟨by linarith [(hq a).1], by linarith [(hq a).2]⟩
  have hRB := fun b (hb : b ∈ runSet Tp n' i₀ b₀) => lt_of_mem_runSet hb₀ hb
  have hlt : ∀ b ∈ runSet Tp n' i₀ b₀, ∀ j ∈ blockIco Tp b, j < n' := fun b hb j hj =>
    lt_of_mem_blockIco (hRB b hb) hj
  have hloc0 : IsLocal {e i₀} (fun T => if e i₀ ∈ T then 1 else 0) := fun T => by
    simp only [mem_inter, mem_singleton_self, and_true]
  have hloc : ∀ b ∈ runSet Tp n' i₀ b₀, IsLocal (blockSet Tp e b) (fun T => 1 - blockInd Tp e b T) :=
    fun b _ => (isLocal_blockInd b).one_sub
  have hdisj : ((runSet Tp n' i₀ b₀ : Finset ℕ) : Set ℕ).PairwiseDisjoint (blockSet Tp e) := by
    intro b hb b' hb' hne
    exact disjoint_image_of_lt he (hlt b hb) (hlt b' hb') (disjoint_blockIco hne)
  have hd : Disjoint {e i₀} ((runSet Tp n' i₀ b₀).biUnion (blockSet Tp e)) := by
    rw [disjoint_biUnion_right]
    intro b hb
    rw [disjoint_singleton_left]
    intro hm
    obtain ⟨j, hj, hjj⟩ := mem_image.1 hm
    have h1 : j = i₀ := he (Set.mem_Iio.2 (hlt b hb j hj)) (Set.mem_Iio.2 hi₀) hjj
    exact (mem_erase.1 hb).1 (by rw [← div_eq_of_mem_blockIco hj, h1])
  rw [pexp_mul_local q hd hloc0 (IsLocal.prod _ _ _ hloc), pexp_ind,
    pexp_prod_local q _ _ hdisj _ hloc]
  have hfac : ∀ b ∈ runSet Tp n' i₀ b₀, 0 ≤ pexp q (fun T => 1 - blockInd Tp e b T) ∧
      pexp q (fun T => 1 - blockInd Tp e b T) ≤ 1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) := by
    intro b hb
    rw [pexp_one_sub]
    have h1 : pexp q (blockInd Tp e b) ≤ 1 := by
      calc pexp q (blockInd Tp e b) ≤ pexp q (fun _ => 1) := pexp_mono hq' fun T => blockInd_le_one he (hRB b hb) T
        _ = 1 := pexp_const q 1
    have h2 := pexp_blockInd_ge hq hδ hδ' hu1 hu2 he (hRB b hb)
    constructor <;> linarith
  have hμ0 : 0 ≤ 1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) := by
    have : (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hμ1 : 1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) ≤ 1 := by
    have : 0 ≤ (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) := by positivity
    linarith
  calc q (e i₀) * ∏ b ∈ runSet Tp n' i₀ b₀, pexp q (fun T => 1 - blockInd Tp e b T) ≤
      δ * ∏ _b ∈ runSet Tp n' i₀ b₀, (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) :=
        mul_le_mul (hq _).2 (prod_le_prod₀ (fun b hb => (hfac b hb).1) fun b hb => (hfac b hb).2)
          (prod_nonneg fun b hb => (hfac b hb).1) hδ.le
    _ = δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ (runSet Tp n' i₀ b₀).card := by rw [prod_const]
    _ ≤ δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hμ0 hμ1 (le_card_runSet hMB)) hδ.le

omit [Fintype α] in
/-- `1 ≤ Σ f` from one term, the others nonnegative. -/
theorem one_le_sum_of_mem {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i) {i : ι} (hi : i ∈ s)
    (h1 : 1 ≤ f i) : 1 ≤ ∑ j ∈ s, f j :=
  h1.trans (single_le_sum h0 hi)

omit [Fintype α] in
/-- The parts of the union bound are nonnegative. -/
theorem badBound_parts_nonneg {n' i₀ : ℕ} (he : Set.InjOn e (Set.Iio n')) (T : Finset α) :
    (∀ s, (0 : ℝ) ≤ if e i₀ ∈ T ∧ Tp.K + 1 ≤ (T ∩ winSet e n' s Tp.L₂).card then 1 else 0) ∧
    (∀ b₀ ∈ range (n' / Tp.blockLen),
      (0 : ℝ) ≤ (if e i₀ ∈ T then 1 else 0) * ∏ b ∈ runSet Tp n' i₀ b₀, (1 - blockInd Tp e b T)) ∧
    (∀ s, (0 : ℝ) ≤ if e i₀ ∈ T ∧ Tp.N₁ + 1 ≤ (T ∩ winSet e n' s Tp.G').card then 1 else 0) :=
  ⟨fun s => by split_ifs <;> norm_num,
    fun b₀ hb₀ => mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun b hb =>
      sub_nonneg.2 (blockInd_le_one he (lt_of_mem_runSet (mem_range.1 hb₀) hb) T)),
    fun s => by split_ifs <;> norm_num⟩

omit [Fintype α] in
/-- The union bound is nonnegative. -/
theorem badBound_nonneg {n' i₀ : ℕ} (he : Set.InjOn e (Set.Iio n')) (T : Finset α) :
    0 ≤ badBound Tp e n' i₀ T := by
  obtain ⟨h1, h2, h3⟩ := badBound_parts_nonneg (Tp := Tp) (i₀ := i₀) he T
  exact add_nonneg (sum_nonneg fun s _ => h1 s) (add_nonneg (sum_nonneg h2) (sum_nonneg fun s _ => h3 s))

omit [Fintype α] in
/-- **The union bound holds**: a forced top on a bad orbit makes one term of `badBound` equal to `1`. -/
theorem one_le_badBound {n' i₀ : ℕ} (he : Set.InjOn e (Set.Iio n')) (hL : Tp.L₂ ≤ n') (hG : Tp.G' ≤ n')
    {T : Finset α} (hT : e i₀ ∈ T) (hbad : ¬ Tp.IsGood n' (orbPos n' e T)) : 1 ≤ badBound Tp e n' i₀ T := by
  obtain ⟨h1, h2, h3⟩ := badBound_parts_nonneg (Tp := Tp) (i₀ := i₀) he T
  have s1 := sum_nonneg fun s (_ : s ∈ range n') => h1 s
  have s2 := sum_nonneg h2
  have s3 := sum_nonneg fun s (_ : s ∈ range n') => h3 s
  unfold badBound
  by_cases hw : ∀ s < n', winCard n' (orbPos n' e T) s Tp.L₂ ≤ Tp.K
  · by_cases hd : ∀ s < n', winCard n' (orbPos n' e T) s Tp.G' ≤ Tp.N₁
    · have ht : ¬ ∀ b₀ < n' / Tp.blockLen, ∃ j ≤ Tp.M₀, Tp.Marked (orbPos n' e T) ((b₀ + j) % (n' / Tp.blockLen)) :=
        fun ht => hbad ⟨hw, ht, hd⟩
      push Not at ht
      obtain ⟨b₀, hb₀, hnm⟩ := ht
      have hU : 1 ≤ (if e i₀ ∈ T then (1 : ℝ) else 0) * ∏ b ∈ runSet Tp n' i₀ b₀, (1 - blockInd Tp e b T) := by
        rw [ite_eq_left hT, one_mul]
        refine le_of_eq (prod_eq_one fun b hb => ?_).symm
        obtain ⟨j, hj, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
        have hz : blockInd Tp e ((b₀ + j) % (n' / Tp.blockLen)) T = 0 := by
          by_contra hne
          exact hnm j (Nat.lt_succ_iff.1 (mem_range.1 hj))
            (marked_of_blockInd_ne_zero he (Nat.mod_lt _ (by omega)) hne)
        rw [hz, sub_zero]
      have := one_le_sum_of_mem h2 (mem_range.2 hb₀) hU
      linarith
    · push Not at hd
      obtain ⟨s, hs, hlt⟩ := hd
      have hc : e i₀ ∈ T ∧ Tp.N₁ + 1 ≤ (T ∩ winSet e n' s Tp.G').card := ⟨hT, hlt.trans_le (winCard_le he hG T)⟩
      have := one_le_sum_of_mem (fun s _ => h3 s) (mem_range.2 hs) (le_of_eq (ite_eq_left hc).symm)
      linarith
  · push Not at hw
    obtain ⟨s, hs, hlt⟩ := hw
    have hc : e i₀ ∈ T ∧ Tp.K + 1 ≤ (T ∩ winSet e n' s Tp.L₂).card := ⟨hT, hlt.trans_le (winCard_le he hL T)⟩
    have := one_le_sum_of_mem (fun s _ => h1 s) (mem_range.2 hs) (le_of_eq (ite_eq_left hc).symm)
    linarith

/-- **The mean of the union bound**: `≤ δn′(C(L₂ + 1, K + 1)δ^K + (1 − μ)^{M₀} + C(G′, N₁)δ^{N₁} +
C(G′, N₁ + 1)δ^{N₁+1})`, from `pexp_forced_window_le` (with Pascal for (A)) and `pexp_run_le`. -/
theorem pexp_badBound_le {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' : ℕ}
    (he : Set.InjOn e (Set.Iio n')) {i₀ : ℕ} (hi₀ : i₀ < n') (hB : (Tp.M₀ + 1) * Tp.blockLen ≤ n') :
    pexp q (fun T => badBound Tp e n' i₀ T) ≤
      δ * n' * (((Tp.L₂ + 1).choose (Tp.K + 1) : ℝ) * δ ^ Tp.K + (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀ +
        ((Tp.G'.choose Tp.N₁ : ℝ) * δ ^ Tp.N₁ + (Tp.G'.choose (Tp.N₁ + 1) : ℝ) * δ ^ (Tp.N₁ + 1))) := by
  have hq0 : ∀ a, 0 ≤ q a ∧ q a ≤ δ := fun a => ⟨by linarith [(hq a).1], (hq a).2⟩
  have hδ1 : δ ≤ 1 := by linarith
  have hu0' : (1 : ℝ) ≤ Tp.u := le_trans (by rw [le_div_iff₀ hδ]; linarith) hu1
  have hu0 : 1 ≤ Tp.u := by exact_mod_cast hu0'
  have hbl : 0 < Tp.blockLen := Nat.mul_pos (by omega) (by omega)
  have hMB : Tp.M₀ + 1 ≤ n' / Tp.blockLen := (Nat.le_div_iff_mul_le hbl).2 hB
  have hBn : ((n' / Tp.blockLen : ℕ) : ℝ) ≤ n' := by exact_mod_cast Nat.div_le_self _ _
  have hA : ∀ s, pexp q (fun T => if e i₀ ∈ T ∧ Tp.K + 1 ≤ (T ∩ winSet e n' s Tp.L₂).card then 1 else 0) ≤
      δ * (((Tp.L₂ + 1).choose (Tp.K + 1) : ℝ) * δ ^ Tp.K) := by
    intro s
    have hW : (winSet e n' s Tp.L₂).card ≤ Tp.L₂ := card_image_le.trans (card_range _).le
    refine (pexp_forced_window_le hq0 hδ1 (e i₀) _ (Nat.le_add_left 1 Tp.K)).trans ?_
    rw [Nat.add_sub_cancel]
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    have hc1 : ((winSet e n' s Tp.L₂).card.choose Tp.K : ℝ) ≤ Tp.L₂.choose Tp.K := by
      exact_mod_cast Nat.choose_le_choose _ hW
    have hc2 : ((winSet e n' s Tp.L₂).card.choose (Tp.K + 1) : ℝ) ≤ Tp.L₂.choose (Tp.K + 1) := by
      exact_mod_cast Nat.choose_le_choose _ hW
    have hp : δ ^ (Tp.K + 1) ≤ δ ^ Tp.K := pow_le_pow_of_le_one hδ.le hδ1 (Nat.le_succ _)
    have hpas : ((Tp.L₂ + 1).choose (Tp.K + 1) : ℝ) = Tp.L₂.choose Tp.K + Tp.L₂.choose (Tp.K + 1) := by
      exact_mod_cast Nat.choose_succ_succ' _ _
    have t1 := mul_le_mul_of_nonneg_right hc1 (pow_nonneg hδ.le Tp.K)
    have t2 := mul_le_mul hc2 hp (pow_nonneg hδ.le _) (Nat.cast_nonneg _)
    rw [hpas, add_mul]
    linarith
  have hI : ∀ s, pexp q (fun T => if e i₀ ∈ T ∧ Tp.N₁ + 1 ≤ (T ∩ winSet e n' s Tp.G').card then 1 else 0) ≤
      δ * ((Tp.G'.choose Tp.N₁ : ℝ) * δ ^ Tp.N₁ + (Tp.G'.choose (Tp.N₁ + 1) : ℝ) * δ ^ (Tp.N₁ + 1)) := by
    intro s
    have hV : (winSet e n' s Tp.G').card ≤ Tp.G' := card_image_le.trans (card_range _).le
    refine (pexp_forced_window_le hq0 hδ1 (e i₀) _ (Nat.le_add_left 1 Tp.N₁)).trans ?_
    rw [Nat.add_sub_cancel]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hδ.le
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose _ hV) (pow_nonneg hδ.le _)
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose _ hV) (pow_nonneg hδ.le _)
  have hμ0 : 0 ≤ (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀ := by
    have : (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact pow_nonneg (by linarith) _
  simp only [badBound]
  rw [pexp_add, pexp_add, pexp_sum, pexp_sum, pexp_sum]
  have sA := (sum_le_sum fun s (_ : s ∈ range n') => hA s).trans_eq
    (by rw [sum_const, card_range, nsmul_eq_mul])
  have sI := (sum_le_sum fun s (_ : s ∈ range n') => hI s).trans_eq
    (by rw [sum_const, card_range, nsmul_eq_mul])
  have sT := (sum_le_sum fun b₀ (hb₀ : b₀ ∈ range (n' / Tp.blockLen)) =>
    pexp_run_le hq hδ hδ' hu1 hu2 he hi₀ hMB (mem_range.1 hb₀)).trans_eq
      (by rw [sum_const, card_range, nsmul_eq_mul])
  have sT' : ((n' / Tp.blockLen : ℕ) : ℝ) * (δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀) ≤
      n' * (δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀) :=
    mul_le_mul_of_nonneg_right hBn (mul_nonneg hδ.le hμ0)
  calc _ ≤ n' * (δ * (((Tp.L₂ + 1).choose (Tp.K + 1) : ℝ) * δ ^ Tp.K)) +
        (n' * (δ * (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀) +
          n' * (δ * ((Tp.G'.choose Tp.N₁ : ℝ) * δ ^ Tp.N₁ + (Tp.G'.choose (Tp.N₁ + 1) : ℝ) * δ ^ (Tp.N₁ + 1)))) :=
        add_le_add sA (add_le_add (sT.trans sT') sI)
    _ = _ := by ring

open scoped Classical in
/-- **A forced top on a bad orbit**: `P(e i₀ ∈ T, orbit not good) ≤ δn′((A) + (T) + (I))`. -/
theorem pexp_forced_bad_le {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 3 * δ / 4 ≤ q a ∧ q a ≤ δ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 100) (Tp : TilePar) (hu1 : 1 / δ ≤ Tp.u) (hu2 : (Tp.u : ℝ) ≤ 1 / δ + 1) {n' : ℕ}
    {e : ℕ → α} (he : Set.InjOn e (Set.Iio n')) {i₀ : ℕ} (hi₀ : i₀ < n') (hL : Tp.L₂ ≤ n') (hG : Tp.G' ≤ n')
    (hB : (Tp.M₀ + 1) * Tp.blockLen ≤ n') :
    pexp q (fun T => if e i₀ ∈ T ∧ ¬ Tp.IsGood n' (orbPos n' e T) then 1 else 0) ≤
      δ * n' * (((Tp.L₂ + 1).choose (Tp.K + 1) : ℝ) * δ ^ Tp.K + (1 - (10 : ℝ)⁻¹ ^ (6 * Tp.r + 1)) ^ Tp.M₀ +
        ((Tp.G'.choose Tp.N₁ : ℝ) * δ ^ Tp.N₁ + (Tp.G'.choose (Tp.N₁ + 1) : ℝ) * δ ^ (Tp.N₁ + 1))) := by
  have hq' : IsProb q := fun a => ⟨by linarith [(hq a).1], by linarith [(hq a).2]⟩
  calc _ ≤ pexp q (fun T => badBound Tp e n' i₀ T) := pexp_mono hq' fun T => by
        split_ifs with h
        · exact one_le_badBound he hL hG h.1 h.2
        · exact badBound_nonneg he T
    _ ≤ _ := pexp_badBound_le hq hδ hδ' hu1 hu2 he hi₀ hB

end ProdWeights

end ZetaBalance
