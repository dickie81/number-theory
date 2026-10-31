/-
# The certificate under a decomposition rule, over `Finset`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements about `SieveRuleDefs.lean`'s definitions, as `SieveCert.lean` states them for the certificate's own.

* `limOK_cells2` … `limOK_cells5`, `nbOK_cells2` … `nbOK_cells5`: the tests on a box of cells, as inequalities.
* `subsetSums_ofFn`, `hiSum_ofFn`, `tstar_mem`: a box's subset sums are its sums over the `Finset`s of its cells, and
  `tstar` is attained.
* `ibOK_sound`: `ibOK`'s witnesses, a set `S₀` of the box's cells with `T = cIB` there and a split `(S₁, eIn₁)` of its
  leaves, as sums over `Finset`s; `okIB_cases`: `okIB` is `limOK`, or `ibOK` and `nbOK`.
* `RuleNB`, `RuleIB`: what a rule guarantees of the boxes it passes (`limOK`, or no boundary term; `limOK`, or `ibOK`
  with no boundary term), for `ibRule` (`ibRule_ib`).

The file imports `SieveCert.lean` and `SieveRuleDefs.lean`.
-/
import SieveCert
import SieveRuleDefs

namespace SieveCert

/-! ### The certificate's own rule -/

section Lim

variable [Grid]

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

end Lim

/-! ### Sums, under any rule -/

section Sums

variable [Grid] [Rule]

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

/-! ### The boxes of the decomposed cells -/

section Boxes

variable [Grid]

theorem nbOK_cells2 (i j : ℕ) : nbOK [cell i, cell j] = decide (e i + H + (e j + H) + (e j + H) < DEN) := by
  simp only [nbOK, hiSum, lastHi, cell, Nat.add_zero, Nat.add_assoc]

theorem nbOK_cells3 (i j k : ℕ) :
    nbOK [cell i, cell j, cell k] = decide (e i + H + (e j + H) + (e k + H) + (e k + H) < DEN) := by
  simp only [nbOK, hiSum, lastHi, cell, Nat.add_zero, Nat.add_assoc]

theorem nbOK_cells4 (i j k l : ℕ) :
    nbOK [cell i, cell j, cell k, cell l] =
      decide (e i + H + (e j + H) + (e k + H) + (e l + H) + (e l + H) < DEN) := by
  simp only [nbOK, hiSum, lastHi, cell, Nat.add_zero, Nat.add_assoc]

theorem nbOK_cells5 (i j k l b : ℕ) :
    nbOK [cell i, cell j, cell k, cell l, cellC b] =
      decide (e i + H + (e j + H) + (e k + H) + (e l + H) + (eC b + HC) + (eC b + HC) < DEN) := by
  simp only [nbOK, hiSum, lastHi, cell, cellC, Nat.add_zero, Nat.add_assoc]

variable [Rule]

end Boxes

/-! ### What a rule guarantees -/

/-- **A rule with no boundary term**: a box it passes passes `limOK`, or has no boundary term (`nbOK`). The
decomposition's cells that vanish outside the region use it (`SieveBuch`). -/
class RuleNB [Grid] [Rule] : Prop where
  nb : ∀ xs, Rule.ok xs = true → limOK xs = true ∨ nbOK xs = true

/-- **A rule of the bilinear Type I estimate**: a box it passes passes `limOK`, or passes `ibOK` with no boundary
term. The leaves use it (`SieveQ`). -/
class RuleIB [Grid] [Rule] [IBPar] : Prop where
  ib : ∀ xs, Rule.ok xs = true → limOK xs = true ∨ (ibOK xs = true ∧ nbOK xs = true)

theorem RuleIB.toRuleNB [Grid] [Rule] [IBPar] [RuleIB] : RuleNB :=
  ⟨fun xs h => (RuleIB.ib xs h).imp id fun h' => h'.2⟩

theorem ibRule_ib [Grid] [IBPar] : @RuleIB _ ibRule _ := @RuleIB.mk _ ibRule _ fun _ h => okIB_cases h

end SieveCert
