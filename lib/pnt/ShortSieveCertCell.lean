import ShortSieveCertTwo
import ShortSieveThree

/-!
# The certificate's root cells

Li's third sum is the counts of the root cells `ShortSieveThree.cell k j r` (`ShortSieveThree.bigThree_eq_cells`).
Each cell is a standard node with two primes (`cell_eq_std`), and the certificate starts it with the box
`[k DEN/40, (k + 1) DEN/40] × [j DEN/40, (j + 1) DEN/40)` of `(X₀, X₁)` (the upper end of `X₀` widened by a unit,
since the cell is closed there) and the constraints `X₁ < X₀`, `q ≤ ρ`, the level and the region (`Sound.cell`).

* `StdInv.cell`, `CondsOK.cell`: the cell's conditions keep the standard nodes' invariants.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveThree

/-- `DEN/40`. -/
def D40 : ℤ := 5 * 2 ^ 29

theorem D40_eq : (D40 : ℝ) = DEN / 40 := by norm_num [D40, DEN]

theorem cell_eq_std (k j : ℕ) (r : Bool) : cell k j r = std 1 (cellConds k j r) := rfl

theorem vec_two (v : (Fin 2 → ℕ) × (Fin 1 → ℕ)) : v.1 = ![v.1 0, v.1 1] ∧ v.2 = ![v.2 0] := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · fin_cases i <;> rfl
  · fin_cases i; rfl

/-- The cell's conditions at a pair, in logarithms. -/
theorem cell_logs {k j : ℕ} {r : Bool} {x : ℝ} {v : (Fin 2 → ℕ) × (Fin 1 → ℕ)}
    (hc : ∀ C ∈ cellConds k j r, C.Holds x v.1 v.2) :
    k * Real.log x < 40 * Real.log (v.1 0) ∧ 40 * Real.log (v.1 0) ≤ (k + 1) * Real.log x ∧
      j * Real.log x ≤ 40 * Real.log (v.1 1) ∧ 40 * Real.log (v.1 1) < (j + 1) * Real.log x ∧
      Real.log (v.1 1) < Real.log (v.1 0) ∧ Real.log (v.1 1) ≤ Real.log (v.2 0) ∧
      (nuCond k).Holds x v.1 v.2 ∧ (if r then regCond k else (regCond k).neg).Holds x v.1 v.2 := by
  obtain ⟨e1, e2⟩ := vec_two v
  simp only [cellConds, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at hc
  obtain ⟨a1, a2, a3, a4, -, a6, -, a8, a9, a10⟩ := hc
  rw [e1, e2] at a1 a2 a3 a4 a6 a10
  rw [holds_lc_lt] at a1 a4 a6
  rw [holds_lc_le] at a2 a3 a10
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, a8, a9⟩

/-- **The cell keeps the standard nodes' invariant** (for `2 ≤ j`): its primes are at least `x^{1/20}`, and the rough
item at least `q`. -/
theorem StdInv.cell {k j : ℕ} (r : Bool) (hj : 2 ≤ j) (hk : 2 ≤ k) : StdInv 1 (cellConds k j r) := by
  intro x hx v hv1 hv2 hc
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  obtain ⟨a1, -, a3, -, a6, a10, -, -⟩ := cell_logs hc
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : (0 : ℝ) < v.1 0 := by exact_mod_cast hv1 0
  have hq0 : (0 : ℝ) < v.1 1 := by exact_mod_cast hv1 1
  have hr0 : (0 : ℝ) < v.2 0 := by exact_mod_cast hv2 0
  refine ⟨fun a => ?_, ?_⟩
  · rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 _), Real.log_rpow hx0, ← Real.exp_log (show (0 : ℝ) < v.1 a by
      exact_mod_cast hv1 a)]
    refine Real.exp_le_exp.2 ?_
    fin_cases a
    · show 1 / 20 * Real.log x ≤ Real.log (v.1 0)
      nlinarith
    · show 1 / 20 * Real.log x ≤ Real.log (v.1 1)
      nlinarith
  · exact_mod_cast (Real.log_le_log_iff hq0 hr0).1 a10

theorem condsOK_lc {e₀ e₁ f c : ℝ} {strict : Bool} (h : e₀ ≠ f ∨ e₁ ≠ f) : CondsOK [lc e₀ e₁ f c strict] := by
  intro C hC
  simp only [List.mem_singleton] at hC
  subst hC
  rcases h with h | h
  · exact ⟨Sum.inl 0, Sum.inr 0, by simpa [lc] using h⟩
  · exact ⟨Sum.inl 1, Sum.inr 0, by simpa [lc] using h⟩

/-- **The cell's conditions are not functions of the product alone.** -/
theorem CondsOK.cell (k j : ℕ) (r : Bool) : CondsOK (cellConds k j r) := by
  have hneg : ∀ C : Cond 2 1, CondsOK [C] → CondsOK [C.neg] := fun C h C' hC' => by
    simp only [List.mem_singleton] at hC'
    subst hC'
    obtain ⟨u, w, huw⟩ := h C List.mem_cons_self
    refine ⟨u, w, fun he => huw ?_⟩
    rcases u with a | i <;> rcases w with b | j' <;> simpa [Cond.neg] using he
  have hnu : CondsOK [nuCond k] := by
    unfold nuCond
    split_ifs
    · exact condsOK_lc (Or.inr (by norm_num))
    · exact condsOK_lc (Or.inr (by norm_num))
    · exact condsOK_lc (Or.inl (by norm_num))
  have hreg : CondsOK [regCond k] := by
    unfold regCond
    split_ifs
    · exact condsOK_lc (Or.inl (by norm_num))
    · exact condsOK_lc (Or.inl (by norm_num))
  have hr : CondsOK [if r then regCond k else (regCond k).neg] := by
    cases r
    · exact hneg _ hreg
    · exact hreg
  intro C hC
  simp only [cellConds, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact condsOK_lc (Or.inl (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inl (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inr (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inr (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inl (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inl (by norm_num)) _ List.mem_cons_self
  · exact condsOK_lc (Or.inl (by norm_num)) _ List.mem_cons_self
  · exact hnu _ List.mem_cons_self
  · exact hr _ List.mem_cons_self
  · exact condsOK_lc (Or.inr (by norm_num)) _ List.mem_cons_self

/-! ### The cell's box and constraints -/

/-- The level as a constraint: `X₁ ≥ DEN/20` on the cell `k = 2`, where it is held at `2θ − 1`; `X₁ ≥ DEN/10` on the
cell `k = 18`, where Li's level is `γ`; and `2X₀ + (2h − 1)X₁ ≥ (21/20)DEN`, `h = ⌊(21 − k)/2⌋`, on the others. -/
def levelCon (k : ℕ) : Con :=
  if k = 2 then ⟨⟨5 * 2 ^ 30, [0, -1], 0⟩, false⟩
  else if k = 18 then ⟨⟨10 * 2 ^ 30, [0, -1], 0⟩, false⟩
  else ⟨⟨105 * 2 ^ 30, [-2, 1 - 2 * (((21 - k) / 2 : ℕ) : ℤ)], 0⟩, false⟩

/-- The region as a constraint: `X₀ + 3X₁ < DEN` for `k ≤ 15`, `2X₁ < X₀` above. -/
def regionCon (k : ℕ) : Con := if k ≤ 15 then ⟨⟨-DEN, [1, 3], 0⟩, true⟩ else ⟨⟨0, [-1, 2], 0⟩, true⟩

/-- The cell's box `[k DEN/40, (k + 1) DEN/40 + 1) × [j DEN/40, (j + 1) DEN/40)`. -/
def cellBox (k j : ℕ) : Box := [(k * D40, (k + 1) * D40 + 1), (j * D40, (j + 1) * D40)]

/-- The cell's constraints: `X₁ < X₀`, `q ≤ ρ`, the level and the region (or its complement). -/
def cellCons (k : ℕ) (r : Bool) : List Con :=
  [⟨⟨0, [-1, 1], 0⟩, true⟩, geCon 1, levelCon k, if r then regionCon k else (regionCon k).neg]

/-- A form in the two coordinates at a cell's pair. -/
theorem val_cell (c0 a b ce : ℤ) (x : ℝ) (v : (Fin 2 → ℕ) × (Fin 1 → ℕ)) :
    (⟨c0, [a, b], ce⟩ : LF).val (coords (stdRows 2) x v) (slack x v) =
      c0 + a * (DEN * (Real.log (v.1 0) / Real.log x)) + b * (DEN * (Real.log (v.1 1) / Real.log x)) +
        ce * (DEN * (1 - (Real.log (v.1 0) / Real.log x + Real.log (v.1 1) / Real.log x +
          Real.log (v.2 0) / Real.log x))) := by
  have e0 : coords (stdRows 2) x v 0 = DEN * (Real.log (v.1 0) / Real.log x) := coords_std x v 0
  have e1 : coords (stdRows 2) x v 1 = DEN * (Real.log (v.1 1) / Real.log x) := coords_std x v 1
  unfold LF.val slack
  simp only [dotR, zero_add, e0, e1]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  simp only [expo, Sum.elim_inl, Sum.elim_inr]
  ring

/-- The cell's region constraint is its region condition. -/
theorem holds_regionCon {k : ℕ} {x : ℝ} (hx : 1 < x) (v : (Fin 2 → ℕ) × (Fin 1 → ℕ)) :
    (regionCon k).Holds (coords (stdRows 2) x v) (slack x v) ↔ (regCond k).Holds x v.1 v.2 := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD := DEN_pos
  obtain ⟨e1, e2⟩ := vec_two v
  conv_rhs => rw [e1, e2]
  unfold regionCon regCond
  split_ifs
  · rw [holds_lc_lt]
    unfold Con.Holds
    simp only [↓reduceIte]
    rw [val_cell]
    push_cast
    constructor <;> intro h
    · have h' : DEN * ((Real.log (v.1 0) + 3 * Real.log (v.1 1) - Real.log x) / Real.log x) < 0 := by
        have e : DEN * ((Real.log (v.1 0) + 3 * Real.log (v.1 1) - Real.log x) / Real.log x) =
            -DEN + 1 * (DEN * (Real.log (v.1 0) / Real.log x)) + 3 * (DEN * (Real.log (v.1 1) / Real.log x)) := by
          field_simp
          ring
        rw [e]
        linarith
      have := (div_neg_iff.1 (neg_of_mul_neg_right h' hD.le))
      rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    · have e : -(DEN : ℝ) + 1 * (DEN * (Real.log (v.1 0) / Real.log x)) +
          3 * (DEN * (Real.log (v.1 1) / Real.log x)) + 0 * (DEN * (1 - (Real.log (v.1 0) / Real.log x +
            Real.log (v.1 1) / Real.log x + Real.log (v.2 0) / Real.log x))) =
          DEN * ((Real.log (v.1 0) + 3 * Real.log (v.1 1) - Real.log x) / Real.log x) := by
        field_simp
        ring
      rw [e]
      exact mul_neg_of_pos_of_neg hD (div_neg_of_neg_of_pos (by linarith) hlx)
  · rw [holds_lc_lt]
    unfold Con.Holds
    simp only [↓reduceIte]
    rw [val_cell]
    push_cast
    have e : (0 : ℝ) + -1 * (DEN * (Real.log (v.1 0) / Real.log x)) + 2 * (DEN * (Real.log (v.1 1) / Real.log x)) +
        0 * (DEN * (1 - (Real.log (v.1 0) / Real.log x + Real.log (v.1 1) / Real.log x +
          Real.log (v.2 0) / Real.log x))) =
        DEN * ((-Real.log (v.1 0) + 2 * Real.log (v.1 1)) / Real.log x) := by
      field_simp
      ring
    rw [e]
    constructor <;> intro h
    · have := (div_neg_iff.1 (neg_of_mul_neg_right h hD.le))
      rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    · exact mul_neg_of_pos_of_neg hD (div_neg_of_neg_of_pos (by linarith) hlx)

/-- **The cell is sound** with its box and constraints. -/
theorem Sound.cell {k j : ℕ} (r : Bool) (E : ℤ) :
    Sound (std 1 (cellConds k j r)) (stdRows 2) E (cellCons k r) (cellBox k j) := by
  intro x hx v hv1 hv2 hc hH
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD := DEN_pos
  obtain ⟨a1, a2, a3, a4, a6, a10, a8, a9⟩ := cell_logs hc
  have e0 : coords (stdRows 2) x v 0 = DEN * (Real.log (v.1 0) / Real.log x) := coords_std x v 0
  have e1 : coords (stdRows 2) x v 1 = DEN * (Real.log (v.1 1) / Real.log x) := coords_std x v 1
  -- `DEN log p/log x` against multiples of `DEN/40`
  have key : ∀ (c : ℝ) (P : ℕ), (c * Real.log x ≤ 40 * Real.log P → c * (DEN / 40) ≤ DEN * (Real.log P / Real.log x)) ∧
      (40 * Real.log P < c * Real.log x → DEN * (Real.log P / Real.log x) < c * (DEN / 40)) ∧
      (40 * Real.log P ≤ c * Real.log x → DEN * (Real.log P / Real.log x) ≤ c * (DEN / 40)) := by
    intro c P
    have e : DEN * (Real.log P / Real.log x) = (DEN / 40) * (40 * Real.log P) / Real.log x := by
      field_simp
    rw [e]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [le_div_iff₀ hlx]; nlinarith
    · rw [div_lt_iff₀ hlx]; nlinarith
    · rw [div_le_iff₀ hlx]; nlinarith
  refine ⟨?_, fun c hc' => ?_⟩
  · -- the box
    simp only [cellBox, InBox, e0, e1, zero_add]
    have k1 := (key k (v.1 0)).1 a1.le
    have k2 := (key (k + 1) (v.1 0)).2.2 a2
    have k3 := (key j (v.1 1)).1 a3
    have k4 := (key (j + 1) (v.1 1)).2.1 a4
    push_cast
    rw [D40_eq]
    refine ⟨k1, by linarith, k3, k4, trivial⟩
  simp only [cellCons, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl
  · -- `X₁ < X₀`
    unfold Con.Holds
    simp only [↓reduceIte]
    rw [val_cell]
    push_cast
    have : Real.log (v.1 1) / Real.log x < Real.log (v.1 0) / Real.log x := div_lt_div_of_pos_right a6 hlx
    nlinarith
  · -- `q ≤ ρ`
    unfold Con.Holds geCon
    simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_one, List.cons_append, List.nil_append]
    rw [val_cell]
    push_cast
    have : Real.log (v.1 1) / Real.log x ≤ Real.log (v.2 0) / Real.log x := div_le_div_of_nonneg_right a10 hlx.le
    nlinarith
  · -- the level
    obtain ⟨f1, f2⟩ := vec_two v
    rw [f1, f2] at a8
    -- the cases `X₁ ≥ c DEN`
    have hlow : ∀ (c : ℝ) (n : ℕ), (n : ℝ) = c * DEN → Real.log x * c ≤ Real.log (v.1 1) →
        (⟨⟨(n : ℤ), [0, -1], 0⟩, false⟩ : Con).Holds (coords (stdRows 2) x v) (slack x v) := by
      intro c n hn hl
      unfold Con.Holds
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [val_cell]
      have h2 : c ≤ Real.log (v.1 1) / Real.log x := by rw [le_div_iff₀ hlx]; linarith
      push_cast
      rw [hn]
      nlinarith
    by_cases hk2 : k = 2
    · have a8' : Real.log x * (1 / 20) ≤ Real.log (v.1 1) := by
        have := a8
        rw [nuCond, ite_eq_left hk2, holds_lc_le] at this
        linarith
      have hc : levelCon k = ⟨⟨((5 * 2 ^ 30 : ℕ) : ℤ), [0, -1], 0⟩, false⟩ := by simp [levelCon, hk2]
      rw [hc]
      exact hlow (1 / 20) _ (by norm_num [DEN]) a8'
    by_cases hk18 : k = 18
    · have a8' : Real.log x * (1 / 10) ≤ Real.log (v.1 1) := by
        have := a8
        rw [nuCond, ite_eq_right hk2, ite_eq_left hk18, holds_lc_le] at this
        linarith
      have hc : levelCon k = ⟨⟨((10 * 2 ^ 30 : ℕ) : ℤ), [0, -1], 0⟩, false⟩ := by simp [levelCon, hk18]
      rw [hc]
      exact hlow (1 / 10) _ (by norm_num [DEN]) a8'
    have a8' : -2 * Real.log (v.1 0) + (1 - 2 * (((21 - k) / 2 : ℕ) : ℝ)) * Real.log (v.1 1) ≤
        -(21 / 20) * Real.log x := by
      have := a8
      rw [nuCond, ite_eq_right hk2, ite_eq_right hk18, holds_lc_le] at this
      linarith
    have hc : levelCon k = ⟨⟨105 * 2 ^ 30, [-2, 1 - 2 * (((21 - k) / 2 : ℕ) : ℤ)], 0⟩, false⟩ := by
      simp [levelCon, hk2, hk18]
    rw [hc]
    unfold Con.Holds
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [val_cell, show ((105 * 2 ^ 30 : ℤ) : ℝ) = 21 / 20 * DEN by norm_num [DEN]]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat, Int.cast_natCast, Int.cast_neg,
      Int.cast_zero]
    set h := (((21 - k) / 2 : ℕ) : ℝ) with hh
    have h2 : (21 / 20 : ℝ) ≤ 2 * (Real.log (v.1 0) / Real.log x) +
        (2 * h - 1) * (Real.log (v.1 1) / Real.log x) := by
      have e : 2 * (Real.log (v.1 0) / Real.log x) + (2 * h - 1) * (Real.log (v.1 1) / Real.log x) =
          (2 * Real.log (v.1 0) + (2 * h - 1) * Real.log (v.1 1)) / Real.log x := by field_simp
      rw [e, le_div_iff₀ hlx]
      linarith
    nlinarith
  · -- the region
    cases r
    · simp only [Bool.false_eq_true, ↓reduceIte] at a9 ⊢
      rw [Con.holds_neg, holds_regionCon hx]
      rwa [ShortSieveTree.holds_neg] at a9
    · simp only [↓reduceIte] at a9 ⊢
      exact (holds_regionCon hx v).2 a9

end ShortSieveCert

#print axioms ShortSieveCert.Sound.cell
#print axioms ShortSieveCert.StdInv.cell
#print axioms ShortSieveCert.CondsOK.cell
