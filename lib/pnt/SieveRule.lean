/-
# The certificate under a decomposition rule, in the reals and over `Finset`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements about `SieveRuleDefs.lean`'s definitions, as `SieveCert.lean` and `SieveCert2.lean` state them for the
certificate's own.

* `allowedR_lim`, `allowed4R_lim`, `decR_lim`, `dec4R_lim`, `costR_lim`, `totalR_lim`, `cost2R_lim`, `total2R_lim`:
  under `limRule` the definitions are the certificate's own.
* `totalR_eq`, `total2R_eq`, `rows2R_eq`, `rowsJ2R_eq`, `refcostR_eq`: the sums as `Finset` sums.
* `rows2R_eq_rowsJ2R`, `rowsJ2R_split`, `rows2R_split`, `total2R_eq_rows2R_full`, `rows2R_le_of_split`,
  `rowsJ2R_le_of_split`, `rows2R_le_of_rowsJ2R`: the steps that assemble a bound on `total2R` from its parts' bounds.
* `totalR_div_le`, `total2R_div_lt`: the totals' bounds in the reals.
* `allowedR_of_decR`, `allowed4R_of_dec4R`, `costR_of_decR`, `costR_of_not_decR`, `cost4R_of_dec4R`,
  `cost4R_of_not_dec4R`, `cost4R_of_not_counted4`, `cost2R_of_decR`, `cost2R_of_not_decR`, `cost2R_of_not_cand`,
  `cost2R_ge`: the costs by cases.

The file imports `SieveCert2.lean` and `SieveRuleDefs.lean`.
-/
import SieveCert2
import SieveRuleDefs

namespace SieveCert

/-! ### The certificate's own rule -/

section Lim

variable [Grid]

theorem limRule_ok (xs : List (ℕ × ℕ)) : @Rule.ok limRule xs = limOK xs := rfl

theorem limOK_cells2 (i j : ℕ) : limOK [cell i, cell j] = decide (e i + H + (e j + H) < lim) := rfl

theorem limOK_cells3 (i j k : ℕ) :
    limOK [cell i, cell j, cell k] = decide (e i + H + (e j + H) + (e k + H) < lim) := by
  simp only [limOK, hiSum, cell, Nat.add_zero, Nat.add_assoc]

theorem limOK_cells4 (i j k l : ℕ) :
    limOK [cell i, cell j, cell k, cell l] = decide (e i + H + (e j + H) + (e k + H) + (e l + H) < lim) := by
  simp only [limOK, hiSum, cell, Nat.add_zero, Nat.add_assoc]

theorem limOK_cells5 (i j k l b : ℕ) :
    limOK [cell i, cell j, cell k, cell l, cellC b] =
      decide (e i + H + (e j + H) + (e k + H) + (e l + H) + (eC b + HC) < lim) := by
  simp only [limOK, hiSum, cell, cellC, Nat.add_zero, Nat.add_assoc]

/-- Under `limRule`, `allowedR` is the certificate's `allowed`. -/
theorem allowedR_lim (i j : ℕ) : @allowedR _ limRule i j = allowed i j := by
  simp only [allowedR, allowed, limRule_ok, limOK_cells2, limOK_cells3]

/-- Under `limRule`, `allowed4R` is the certificate's `allowed4`. -/
theorem allowed4R_lim (i j k l : ℕ) : @allowed4R _ limRule i j k l = allowed4 i j k l := by
  simp only [allowed4R, allowed4, limRule_ok, limOK_cells4, limOK_cells5]

theorem dec4R_lim (i j k l : ℕ) : @dec4R _ limRule i j k l = dec4 i j k l := by
  simp only [dec4R, dec4, allowed4R_lim]

theorem cost4R_lim (i j k l : ℕ) : @cost4R _ limRule i j k l = cost4 i j k l := by
  simp only [cost4R, cost4, dec4R_lim]

theorem rowR_lim (i j k : ℕ) : @rowR _ limRule i j k = row i j k := by
  simp only [rowR, row, cost4R_lim]

theorem refcostR_lim (i j : ℕ) : @refcostR _ limRule i j = refcost i j := by
  simp only [refcostR, refcost, rowR_lim]

theorem decR_lim (i j : ℕ) : @decR _ limRule i j = dec i j := by
  simp only [decR, dec, allowedR_lim, refcostR_lim]

theorem costR_lim (i j : ℕ) : @costR _ limRule i j = cost i j := by
  simp only [costR, cost, decR_lim, refcostR_lim]

/-- Under `limRule`, `totalR` is the certificate's `total`. -/
theorem totalR_lim : @totalR _ limRule = total := by
  simp only [totalR, total, costR_lim]

theorem cost2R_lim (i j : ℕ) : @cost2R _ limRule i j = cost2 i j := by
  simp only [cost2R, cost2, decR_lim, refcostR_lim]

/-- Under `limRule`, `total2R` is the refined certificate's `total2`. -/
theorem total2R_lim : @total2R _ limRule = total2 := by
  simp only [total2R, total2, cost2R_lim]

end Lim

/-! ### Sums, under any rule -/

section Sums

variable [Grid] [Rule]

theorem totalR_eq : totalR = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, costR i j := by
  simp [totalR, sumTo_eq]

theorem total2R_eq : total2R = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cost2R i j := by
  simp [total2R, sumTo_eq]

theorem rows2R_eq (a b : ℕ) : rows2R a b = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.range n, cost2R i j := by
  rw [rows2R, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  simp only [sumTo_eq]

theorem rowsJ2R_eq (a b j₀ j₁ : ℕ) :
    rowsJ2R a b j₀ j₁ = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico j₀ j₁, cost2R i j := by
  rw [rowsJ2R, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumTo_eq, Finset.sum_Ico_eq_sum_range]

theorem rows2R_eq_rowsJ2R (a b : ℕ) : rows2R a b = rowsJ2R a b 0 n := by
  rw [rows2R_eq, rowsJ2R_eq, Finset.range_eq_Ico]

theorem rowsJ2R_split (a b : ℕ) {j₀ j₁ j₂ : ℕ} (h₁ : j₀ ≤ j₁) (h₂ : j₁ ≤ j₂) :
    rowsJ2R a b j₀ j₂ = rowsJ2R a b j₀ j₁ + rowsJ2R a b j₁ j₂ := by
  simp only [rowsJ2R_eq, ← Finset.sum_add_distrib, Finset.sum_Ico_consecutive _ h₁ h₂]

theorem rows2R_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : rows2R a c = rows2R a b + rows2R b c := by
  simp only [rows2R_eq, Finset.sum_Ico_consecutive _ hab hbc]

theorem total2R_eq_rows2R_full : total2R = rows2R 0 n := by
  rw [total2R_eq, rows2R_eq, Finset.range_eq_Ico]

/-- A bound on `rows2R a c` from bounds on `rows2R a b` and `rows2R b c`, for `a ≤ b ≤ c`. -/
theorem rows2R_le_of_split {a b c B₁ B₂ B : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (h₁ : rows2R a b ≤ B₁)
    (h₂ : rows2R b c ≤ B₂) (hB : B₁ + B₂ ≤ B) : rows2R a c ≤ B := by
  rw [rows2R_split hab hbc]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rowsJ2R a b j₀ j₂` from bounds on `rowsJ2R a b j₀ j₁` and `rowsJ2R a b j₁ j₂`, for `j₀ ≤ j₁ ≤ j₂`. -/
theorem rowsJ2R_le_of_split (a b : ℕ) {j₀ j₁ j₂ B₁ B₂ B : ℕ} (h₀₁ : j₀ ≤ j₁) (h₁₂ : j₁ ≤ j₂)
    (h₁ : rowsJ2R a b j₀ j₁ ≤ B₁) (h₂ : rowsJ2R a b j₁ j₂ ≤ B₂) (hB : B₁ + B₂ ≤ B) : rowsJ2R a b j₀ j₂ ≤ B := by
  rw [rowsJ2R_split a b h₀₁ h₁₂]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rows2R a b` from one on `rowsJ2R a b 0 n`. -/
theorem rows2R_le_of_rowsJ2R (a b : ℕ) {B : ℕ} (h : rowsJ2R a b 0 n ≤ B) : rows2R a b ≤ B := by
  rw [rows2R_eq_rowsJ2R]; exact h

theorem totalR_div_le (htot : totalR ≤ 88 * K / 100) : (totalR : ℝ) / K ≤ 88 / 100 := by
  have hK := K_pos'
  rw [div_le_iff₀ hK]
  have h1 : ((88 * K / 100 : ℕ) : ℝ) ≤ (88 * K : ℕ) / 100 := Nat.cast_div_le
  have h2 : (totalR : ℝ) ≤ ((88 * K / 100 : ℕ) : ℝ) := by exact_mod_cast htot
  push_cast at h1
  linarith

theorem total2R_div_lt (htot : total2R < K) : (total2R : ℝ) / K < 1 := by
  rw [div_lt_one K_pos']
  exact_mod_cast htot

/-! ### The costs by cases -/

theorem allowedR_of_decR {i j : ℕ} (h : decR i j = true) : allowedR i j = true := by
  simp only [decR, Bool.and_eq_true] at h
  exact h.1

theorem allowed4R_of_dec4R {i j k l : ℕ} (h : dec4R i j k l = true) : allowed4R i j k l = true := by
  simp only [dec4R, Bool.and_eq_true] at h
  exact h.1

theorem costR_of_decR {i j : ℕ} (hc : cand i j = true) (hd : decR i j = true) : costR i j = refcostR i j := by
  simp [costR, hc, hd]

theorem costR_of_not_decR {i j : ℕ} (hc : cand i j = true) (hd : decR i j = false) :
    costR i j = bound2 (e i) (e j) := by
  simp [costR, hc, hd]

theorem cost4R_of_dec4R {i j k l : ℕ} (hc : counted4 i j k l = true) (hd : dec4R i j k l = true) :
    cost4R i j k l = refcost5 i j k l := by
  simp [cost4R, hc, hd]

theorem cost4R_of_not_dec4R {i j k l : ℕ} (hc : counted4 i j k l = true) (hd : dec4R i j k l = false) :
    cost4R i j k l = bound4 (e i) (e j) (e k) (e l) := by
  simp [cost4R, hc, hd]

theorem cost4R_of_not_counted4 {i j k l : ℕ} (hc : counted4 i j k l = false) : cost4R i j k l = 0 := by
  simp [cost4R, hc]

theorem refcostR_eq (i j : ℕ) : refcostR i j = ∑ k ∈ Finset.range n, if inKK i j k && ne3 i j k then
    ∑ l ∈ Finset.range (k + 1), cost4R i j k l else 0 := by
  simp only [refcostR, rowR, sumTo_eq]

theorem cost2R_of_decR {i j : ℕ} (hc : cand i j = true) (hd : decR i j = true) : cost2R i j = refcostR i j := by
  simp [cost2R, hc, hd]

theorem cost2R_of_not_decR {i j : ℕ} (hc : cand i j = true) (hd : decR i j = false) :
    cost2R i j = bound2 (e i) (e j) - sub2 i j := by
  simp [cost2R, hc, hd]

theorem cost2R_of_not_cand {i j : ℕ} (hc : cand i j = false) : cost2R i j = 0 := by
  simp [cost2R, hc]

/-- A dropped candidate cell's refined cost is at least its bound less `sub2`, in the reals. -/
theorem cost2R_ge {i j : ℕ} (hc : cand i j = true) (hd : decR i j = false) :
    (bound2 (e i) (e j) : ℝ) - sub2 i j ≤ cost2R i j := by
  rw [cost2R_of_not_decR hc hd]
  have h : bound2 (e i) (e j) ≤ bound2 (e i) (e j) - sub2 i j + sub2 i j := by omega
  have h' : ((bound2 (e i) (e j) : ℕ) : ℝ) ≤ ((bound2 (e i) (e j) - sub2 i j : ℕ) : ℝ) + sub2 i j := by
    exact_mod_cast h
  linarith

end Sums

/-! ### The bilinear Type I rule's witnesses -/

section Witness

/-- Each subset-sum range of a box is the sum over a set of its cells. -/
theorem subsetSums_ofFn {k : ℕ} (f : Fin k → ℕ × ℕ) :
    ∀ s ∈ subsetSums (List.ofFn f), ∃ T : Finset (Fin k), s = (∑ t ∈ T, (f t).1, ∑ t ∈ T, (f t).2) := by
  induction k with
  | zero =>
    intro s hs
    simp only [List.ofFn_zero, subsetSums, List.mem_singleton] at hs
    exact ⟨∅, by simp [hs]⟩
  | succ k ih =>
    intro s hs
    simp only [List.ofFn_succ, subsetSums, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨s', hs', rfl⟩
    · obtain ⟨T, rfl⟩ := ih (fun t => f t.succ) s hs
      exact ⟨T.map (Fin.succEmb k), by simp [Finset.sum_map]⟩
    · obtain ⟨T, rfl⟩ := ih (fun t => f t.succ) s' hs'
      refine ⟨insert 0 (T.map (Fin.succEmb k)), ?_⟩
      have h0 : (0 : Fin (k + 1)) ∉ T.map (Fin.succEmb k) := by simp [Fin.succ_ne_zero]
      rw [Finset.sum_insert h0, Finset.sum_insert h0]
      simp [Finset.sum_map, add_comm]

/-- The upper sum of a box is the sum of its cells' upper ends. -/
theorem hiSum_ofFn {k : ℕ} (f : Fin k → ℕ × ℕ) : hiSum (List.ofFn f) = ∑ t, (f t).2 := by
  induction k with
  | zero => simp [hiSum]
  | succ k ih => rw [List.ofFn_succ, hiSum, ih, Fin.sum_univ_succ]

/-- The last cell's upper end of a box of `k + 1` cells. -/
theorem lastHi_ofFn {k : ℕ} (f : Fin (k + 1) → ℕ × ℕ) : lastHi (List.ofFn f) = (f (Fin.last k)).2 := by
  induction k with
  | zero => simp [lastHi]
  | succ k ih =>
    rw [List.ofFn_succ]
    have h := ih (fun t => f t.succ)
    rw [List.ofFn_succ] at h ⊢
    simp only [lastHi] at h ⊢
    rw [h, Fin.succ_last]

/-- A fold that keeps the least value of `f` over the entries that pass `P` is one of those values, or its start. -/
theorem foldl_min_mem {α : Type*} (P : α → Bool) (f : α → ℕ) :
    ∀ (l : List α) (acc : Option ℕ) (T : ℕ),
      l.foldl (fun acc s => if P s then some (optMin acc (f s)) else acc) acc = some T →
        acc = some T ∨ ∃ s ∈ l, P s = true ∧ f s = T := by
  intro l
  induction l with
  | nil => intro acc T h; exact Or.inl h
  | cons s l ih =>
    intro acc T h
    rcases ih _ T h with h' | ⟨s', hs', hP, hf⟩
    · dsimp only at h'
      by_cases hP : P s = true
      · rw [ite_eq_left hP] at h'
        cases acc with
        | none =>
          simp only [optMin, Option.some.injEq] at h'
          exact Or.inr ⟨s, List.mem_cons_self, hP, h'⟩
        | some a =>
          simp only [optMin, Option.some.injEq] at h'
          rcases min_choice a (f s) with hm | hm
          · rw [hm] at h'; exact Or.inl (by rw [h'])
          · rw [hm] at h'; exact Or.inr ⟨s, List.mem_cons_self, hP, h'⟩
      · rw [ite_eq_right hP] at h'
        exact Or.inl h'
    · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', hP, hf⟩

variable [Grid]

/-- `tstar` is `cIB` at some subset sum whose upper end is below `DEN − U1`. -/
theorem tstar_mem {xs : List (ℕ × ℕ)} {T : ℕ} (h : tstar xs = some T) :
    ∃ s ∈ subsetSums xs, s.2 < DEN - U1 ∧ cIB s = T := by
  rcases foldl_min_mem (fun s => decide (s.2 < DEN - U1)) cIB (subsetSums xs) none T (by
      simpa only [tstar, decide_eq_true_eq] using h) with h' | ⟨s, hs, hP, hf⟩
  · exact absurd h' (by simp)
  · exact ⟨s, hs, by simpa using hP, hf⟩

variable [IBPar]

/-- **The bilinear Type I rule's witnesses.** If `ibOK` passes a box of cells `f`, there are a set `S₀` of its cells
with upper sum below `DEN − U1` and the value `T` of `cIB` there (`U1 − Σ_{S₀} lo ≤ T`, and
`(DEN − U2) − max(Σ_{S₀} lo, U2) ≤ T` when `U2 ≤ Σ_{S₀} hi`), and a split `(S₁, eIn₁)` with `a₁ = Σ_{S₁} hi + T·[eIn₁]`
and `a₂ = Σ_{S₁ᶜ} hi + T·[¬eIn₁]` satisfying `a₁·Lnum < (Lnum − Lden)·DEN` and `a₁ + 2a₂ < DEN`. -/
theorem ibOK_sound {k : ℕ} (f : Fin k → ℕ × ℕ) (h : ibOK (List.ofFn f) = true) :
    ∃ (S₀ : Finset (Fin k)) (T : ℕ), ∑ t ∈ S₀, (f t).2 < DEN - U1 ∧ U1 - ∑ t ∈ S₀, (f t).1 ≤ T ∧
      (U2 ≤ ∑ t ∈ S₀, (f t).2 → (DEN - U2) - max (∑ t ∈ S₀, (f t).1) U2 ≤ T) ∧
      ∃ (S₁ : Finset (Fin k)) (eIn₁ : Bool),
        (∑ t ∈ S₁, (f t).2 + (if eIn₁ then T else 0)) * IBPar.Lnum < (IBPar.Lnum - IBPar.Lden) * DEN ∧
        (∑ t ∈ S₁, (f t).2 + (if eIn₁ then T else 0)) +
          2 * (∑ t ∈ S₁ᶜ, (f t).2 + (if eIn₁ then 0 else T)) < DEN := by
  unfold ibOK at h
  rcases ht : tstar (List.ofFn f) with _ | T
  · rw [ht] at h; exact absurd h (by simp)
  rw [ht] at h
  obtain ⟨s, hs, hlt, hc⟩ := tstar_mem ht
  obtain ⟨S₀, rfl⟩ := subsetSums_ofFn f s hs
  refine ⟨S₀, T, hlt, ?_, fun hU => ?_, ?_⟩
  · rw [← hc]; exact le_max_left _ _
  · rw [← hc]; unfold cIB; rw [ite_eq_left hU]; exact le_max_right _ _
  · simp only [leafIB, List.any_eq_true, Bool.or_eq_true] at h
    obtain ⟨s₁, hs₁, hcond⟩ := h
    obtain ⟨S₁, rfl⟩ := subsetSums_ofFn f s₁ hs₁
    have hsplit : hiSum (List.ofFn f) - ∑ t ∈ S₁, (f t).2 = ∑ t ∈ S₁ᶜ, (f t).2 := by
      rw [hiSum_ofFn, ← Finset.sum_add_sum_compl S₁ (fun t => (f t).2)]
      omega
    rw [hsplit] at hcond
    rcases hcond with hcond | hcond
    · refine ⟨S₁, true, ?_⟩
      simp only [condIB, Bool.and_eq_true, decide_eq_true_eq] at hcond
      simpa using hcond
    · refine ⟨S₁, false, ?_⟩
      simp only [condIB, Bool.and_eq_true, decide_eq_true_eq] at hcond
      simpa using hcond

/-- `okIB` passes a box only when `limOK` does, or `ibOK` and `nbOK` do. -/
theorem okIB_cases {xs : List (ℕ × ℕ)} (h : okIB xs = true) :
    limOK xs = true ∨ (ibOK xs = true ∧ nbOK xs = true) := by
  simpa [okIB] using h

end Witness

end SieveCert
