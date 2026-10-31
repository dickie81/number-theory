import Mathlib

/-!
# Exact boxes and linear forms for the certificate of Li's region `C`

The certificate's coordinates are real numbers `X_j = α_j · DEN`, `α_j` the exponents of a term's primes (or products
of its items). Boxes, linear forms and every check of the certificate are integers.

A linear form `L = c₀ + Σ_j c_j X_j + c_η H` also involves the slack `H = η · DEN`, `η = 1 − log n/log x`, by which
the exponents of a term's items fall short of summing to `1`; a check uses only `|H| ≤ E`.

* `LF.min_le`: the least value of a form on a box (`lo_j ≤ X_j < hi_j`) bounds it there.
* `tightenOne_sound`, `tighten_sound`: shrinking a box by a constraint `L < 0` or `L ≤ 0` keeps every point of the box
  that satisfies it, and an empty result means there is no such point.
-/

open Finset

namespace ShortSieveCert

/-! ### Linear forms and boxes -/

/-- A linear form `c₀ + Σ_j c_j X_j + c_η H` in the coordinates and the slack. -/
structure LF where
  c0 : ℤ
  c : List ℤ
  ce : ℤ

/-- `Σ_j c_j X_j`. -/
noncomputable def dotR : List ℤ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | a :: l, X => a * X 0 + dotR l fun j => X (j + 1)

/-- The value of a form at the coordinates `X` and the slack `H`. -/
noncomputable def LF.val (L : LF) (X : ℕ → ℝ) (H : ℝ) : ℝ := L.c0 + dotR L.c X + L.ce * H

/-- A box `lo_j ≤ X_j < hi_j`, as the list of the pairs `(lo_j, hi_j)`. -/
abbrev Box := List (ℤ × ℤ)

/-- The point `X` lies in the box. -/
def InBox : Box → (ℕ → ℝ) → Prop
  | [], _ => True
  | b :: B, X => (b.1 : ℝ) ≤ X 0 ∧ X 0 < b.2 ∧ InBox B fun j => X (j + 1)

/-- The point `X` lies in the closed box `lo_j ≤ X_j ≤ hi_j`. -/
def InBoxC : Box → (ℕ → ℝ) → Prop
  | [], _ => True
  | b :: B, X => (b.1 : ℝ) ≤ X 0 ∧ X 0 ≤ b.2 ∧ InBoxC B fun j => X (j + 1)

theorem inBoxC_of_inBox : ∀ {B : Box} {X : ℕ → ℝ}, InBox B X → InBoxC B X
  | [], _, _ => trivial
  | _ :: _, _, ⟨h1, h2, hB⟩ => ⟨h1, h2.le, inBoxC_of_inBox hB⟩

/-- `Σ_j min(c_j lo_j, c_j hi_j)`, the least value of `Σ_j c_j X_j` on the box. -/
def minDot : List ℤ → Box → ℤ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: l, b :: B => (if 0 ≤ a then a * b.1 else a * b.2) + minDot l B

theorem minDot_le : ∀ (c : List ℤ) (B : Box), c.length ≤ B.length → ∀ X, InBoxC B X →
    (minDot c B : ℝ) ≤ dotR c X
  | [], _, _, _, _ => by simp [minDot, dotR]
  | a :: l, [], h, _, _ => by simp at h
  | a :: l, b :: B, h, X, hX => by
    obtain ⟨h1, h2, hB⟩ := hX
    have ih := minDot_le l B (by simpa using h) _ hB
    simp only [minDot, dotR, Int.cast_add]
    have : ((if 0 ≤ a then a * b.1 else a * b.2 : ℤ) : ℝ) ≤ a * X 0 := by
      split_ifs with ha
      · push_cast
        exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast ha)
      · push_cast
        have ha' : (a : ℝ) < 0 := by exact_mod_cast not_le.1 ha
        nlinarith
    linarith

/-- The least value of a form on the box with `|H| ≤ E`. -/
def LF.min (L : LF) (B : Box) (E : ℤ) : ℤ := L.c0 + minDot L.c B - |L.ce| * E

theorem abs_mul_le {c : ℤ} {E : ℤ} {H : ℝ} (hH : |H| ≤ E) : |(c : ℝ) * H| ≤ |(c : ℝ)| * E := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)

theorem LF.min_leC (L : LF) {B : Box} (hlen : L.c.length ≤ B.length) {E : ℤ} {X : ℕ → ℝ} (hX : InBoxC B X)
    {H : ℝ} (hH : |H| ≤ E) : (L.min B E : ℝ) ≤ L.val X H := by
  have h1 := minDot_le L.c B hlen X hX
  have h2 := abs_mul_le (c := L.ce) hH
  have h3 := neg_abs_le ((L.ce : ℝ) * H)
  unfold LF.min LF.val
  push_cast
  linarith

theorem LF.min_le (L : LF) {B : Box} (hlen : L.c.length ≤ B.length) {E : ℤ} {X : ℕ → ℝ} (hX : InBox B X)
    {H : ℝ} (hH : |H| ≤ E) : (L.min B E : ℝ) ≤ L.val X H := L.min_leC hlen (inBoxC_of_inBox hX) hH

/-! ### Constraints -/

/-- A constraint `L < 0` (`strict`) or `L ≤ 0`. -/
structure Con where
  L : LF
  strict : Bool

/-- The constraint holds at `(X, H)`. -/
def Con.Holds (C : Con) (X : ℕ → ℝ) (H : ℝ) : Prop := if C.strict then C.L.val X H < 0 else C.L.val X H ≤ 0

theorem Con.val_le {C : Con} {X : ℕ → ℝ} {H : ℝ} (h : C.Holds X H) : C.L.val X H ≤ 0 := by
  unfold Con.Holds at h
  split_ifs at h
  · exact h.le
  · exact h

/-- A constraint fails on the whole box: its least value is positive, or nonnegative for a strict one. -/
def Con.fails (C : Con) (B : Box) (E : ℤ) : Bool :=
  C.L.c.length ≤ B.length && (if C.strict then decide (0 ≤ C.L.min B E) else decide (0 < C.L.min B E))

theorem Con.not_holds_of_fails {C : Con} {B : Box} {E : ℤ} (hf : C.fails B E = true) {X : ℕ → ℝ} (hX : InBox B X)
    {H : ℝ} (hH : |H| ≤ E) : ¬C.Holds X H := by
  unfold Con.fails at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨hlen, hm⟩ := hf
  have hle := C.L.min_le (of_decide_eq_true hlen) hX hH
  unfold Con.Holds
  split_ifs at hm ⊢ with hs
  · have : (0 : ℝ) ≤ C.L.min B E := by exact_mod_cast of_decide_eq_true hm
    intro h; linarith
  · have : (0 : ℝ) < C.L.min B E := by exact_mod_cast of_decide_eq_true hm
    intro h; linarith

/-! ### Tightening a box -/

theorem dotR_set : ∀ (c : List ℤ) (X : ℕ → ℝ) (j : ℕ), j < c.length →
    dotR c X = dotR (c.set j 0) X + (c.getD j 0 : ℝ) * X j
  | [], _, _, h => by simp at h
  | a :: l, X, 0, _ => by simp [dotR]; ring
  | a :: l, X, j + 1, h => by
    have ih := dotR_set l (fun i => X (i + 1)) j (by simpa using h)
    simp only [List.set_cons_succ, dotR, List.getD_cons_succ]
    rw [ih]
    ring

theorem inBox_set : ∀ (B : Box) (X : ℕ → ℝ) (j : ℕ) (b : ℤ × ℤ), InBox B X → (b.1 : ℝ) ≤ X j → X j < b.2 →
    InBox (B.set j b) X
  | [], _, _, _, h, _, _ => by simpa using h
  | _ :: B, X, 0, b, ⟨_, _, hB⟩, h1, h2 => ⟨h1, h2, hB⟩
  | c :: B, X, j + 1, b, ⟨h1, h2, hB⟩, h3, h4 => ⟨h1, h2, inBox_set B _ j b hB h3 h4⟩

theorem inBox_getD : ∀ (B : Box) (X : ℕ → ℝ) (j : ℕ), InBox B X → j < B.length →
    ((B.getD j (0, 0)).1 : ℝ) ≤ X j ∧ X j < (B.getD j (0, 0)).2
  | [], _, _, _, h => by simp at h
  | _ :: _, _, 0, ⟨h1, h2, _⟩, _ => ⟨h1, h2⟩
  | _ :: B, X, j + 1, ⟨_, _, hB⟩, h => inBox_getD B _ j hB (by simpa using h)

/-- The form without the coordinate `j`. -/
def LF.drop (L : LF) (j : ℕ) : LF := ⟨L.c0, L.c.set j 0, L.ce⟩

theorem LF.val_drop (L : LF) {j : ℕ} (hj : j < L.c.length) (X : ℕ → ℝ) (H : ℝ) :
    L.val X H = (L.drop j).val X H + (L.c.getD j 0 : ℝ) * X j := by
  unfold LF.val LF.drop
  rw [dotR_set L.c X j hj]
  ring

/-- Shrinking the range of the coordinate `j` by the constraint: with `r` the least value of the rest of the form,
`c_j X_j < −r` (or `≤`) gives `X_j < ⌈−r/c_j⌉` (or `X_j < ⌊−r/c_j⌋ + 1`) for `c_j > 0`, and `X_j ≥ ⌊r/|c_j|⌋` for
`c_j < 0`. -/
def tightenOne (C : Con) (E : ℤ) (B : Box) (j : ℕ) : Box :=
  let cj := C.L.c.getD j 0
  let b := B.getD j (0, 0)
  let r := (C.L.drop j).min B E
  if 0 < cj then B.set j (b.1, min b.2 (if C.strict then -(r / cj) else -r / cj + 1))
  else if cj < 0 then B.set j (max b.1 (r / -cj), b.2)
  else B

theorem length_tightenOne (C : Con) (E : ℤ) (B : Box) (j : ℕ) : (tightenOne C E B j).length = B.length := by
  simp only [tightenOne]
  split_ifs <;> simp

theorem tightenOne_sound (C : Con) {E : ℤ} {B : Box} (hlen : C.L.c.length ≤ B.length) (j : ℕ) {X : ℕ → ℝ}
    (hX : InBox B X) {H : ℝ} (hH : |H| ≤ E) (hC : C.Holds X H) : InBox (tightenOne C E B j) X := by
  unfold tightenOne
  by_cases hj : j < C.L.c.length
  · have hjB : j < B.length := lt_of_lt_of_le hj hlen
    have hval := C.L.val_drop hj X H
    have hr := (C.L.drop j).min_le (by simpa [LF.drop] using hlen) hX hH
    obtain ⟨hb1, hb2⟩ := inBox_getD B X j hX hjB
    set cj := C.L.c.getD j 0 with hcj
    set r := (C.L.drop j).min B E with hrdef
    have hle := Con.val_le hC
    by_cases h1 : 0 < cj
    · rw [ite_eq_left h1]
      have hc : (0 : ℝ) < cj := by exact_mod_cast h1
      refine inBox_set B X j _ hX hb1 ?_
      simp only [Int.cast_min]
      refine lt_min hb2 ?_
      by_cases h2 : C.strict = true
      · -- strict: `c_j X_j < −r`
        rw [ite_eq_left h2]
        have hC' : C.L.val X H < 0 := by unfold Con.Holds at hC; rwa [ite_eq_left h2] at hC
        have key : (cj : ℝ) * X j < -r := by linarith
        have hd := Int.ediv_mul_le r h1.ne'
        have hd' : ((r / cj : ℤ) : ℝ) * cj ≤ r := by exact_mod_cast hd
        push_cast
        nlinarith
      · -- `c_j X_j ≤ −r`
        rw [ite_eq_right h2]
        have key : (cj : ℝ) * X j ≤ -r := by linarith
        have hd := Int.lt_ediv_add_one_mul_self (-r) h1
        have hd' : (-(r : ℝ)) < (((-r) / cj : ℤ) + 1) * cj := by exact_mod_cast hd
        push_cast
        nlinarith
    · rw [ite_eq_right h1]
      by_cases h3 : cj < 0
      · -- `c_j < 0`: `X_j ≥ r/|c_j|`
        rw [ite_eq_left h3]
        refine inBox_set B X j _ hX ?_ hb2
        simp only [Int.cast_max]
        refine max_le hb1 ?_
        have hc : (0 : ℝ) < -cj := by exact_mod_cast neg_pos.2 h3
        have key : (cj : ℝ) * X j ≤ -r := by linarith
        have hd := Int.ediv_mul_le r (neg_ne_zero.2 (ne_of_lt h3))
        have hd' : ((r / -cj : ℤ) : ℝ) * (-cj) ≤ r := by exact_mod_cast hd
        nlinarith
      · rw [ite_eq_right h3]
        exact hX
  · -- the coefficient `c_j` is `0`
    have : C.L.c.getD j 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hj)]
    simp only [this, lt_irrefl, ↓reduceIte]
    exact hX

/-- Tightening every coordinate by the constraint, in order. -/
def tightenCon (E : ℤ) (B : Box) (C : Con) : Box := (List.range B.length).foldl (tightenOne C E) B

theorem foldl_tightenOne_sound (C : Con) {E : ℤ} {X : ℕ → ℝ} {H : ℝ} (hH : |H| ≤ E) (hC : C.Holds X H) :
    ∀ (js : List ℕ) (B : Box), C.L.c.length ≤ B.length → InBox B X →
      InBox (js.foldl (tightenOne C E) B) X ∧ (js.foldl (tightenOne C E) B).length = B.length
  | [], _, _, hX => ⟨hX, rfl⟩
  | j :: js, B, hlen, hX => by
    have h1 := tightenOne_sound C hlen j hX hH hC
    have hl := length_tightenOne C E B j
    obtain ⟨h2, h3⟩ := foldl_tightenOne_sound C hH hC js (tightenOne C E B j) (by rw [hl]; exact hlen) h1
    exact ⟨h2, h3.trans hl⟩

theorem tightenCon_sound {C : Con} {E : ℤ} {B : Box} (hlen : C.L.c.length ≤ B.length) {X : ℕ → ℝ}
    (hX : InBox B X) {H : ℝ} (hH : |H| ≤ E) (hC : C.Holds X H) :
    InBox (tightenCon E B C) X ∧ (tightenCon E B C).length = B.length :=
  foldl_tightenOne_sound C hH hC _ B hlen hX

/-- The constraints all mention only coordinates of the box. -/
def fits (cs : List Con) (n : ℕ) : Bool := cs.all fun C => decide (C.L.c.length ≤ n)

/-- Tightening by a list of constraints, in order. -/
def tightenList (E : ℤ) (cs : List Con) (B : Box) : Box := cs.foldl (tightenCon E) B

theorem tightenList_sound {E : ℤ} {X : ℕ → ℝ} {H : ℝ} (hH : |H| ≤ E) :
    ∀ (cs : List Con) (B : Box), fits cs B.length = true → InBox B X → (∀ C ∈ cs, C.Holds X H) →
      InBox (tightenList E cs B) X ∧ (tightenList E cs B).length = B.length
  | [], _, _, hX, _ => ⟨hX, rfl⟩
  | C :: cs, B, hf, hX, hC => by
    simp only [fits, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨h1, h2⟩ := tightenCon_sound hf.1 hX hH (hC C (List.mem_cons_self))
    have hf' : fits cs (tightenCon E B C).length = true := by
      rw [h2]; simpa [fits] using hf.2
    obtain ⟨h3, h4⟩ :=
      tightenList_sound hH cs (tightenCon E B C) hf' h1 fun C' hC' => hC C' (List.mem_cons_of_mem _ hC')
    exact ⟨h3, h4.trans h2⟩

/-- A box with an empty range. -/
def Box.isEmpty (B : Box) : Bool := B.any fun b => decide (b.2 ≤ b.1)

theorem not_isEmpty : ∀ {B : Box} {X : ℕ → ℝ}, InBox B X → B.isEmpty = false
  | [], _, _ => rfl
  | b :: B, X, ⟨h1, h2, hB⟩ => by
    have ih := not_isEmpty hB
    simp only [Box.isEmpty, List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le] at ih ⊢
    refine ⟨?_, ih⟩
    have : (b.1 : ℝ) < b.2 := lt_of_le_of_lt h1 h2
    exact_mod_cast this

/-! ### Domain-aware least values -/

theorem dotR_map_mul (a : ℤ) : ∀ (c : List ℤ) (X : ℕ → ℝ), dotR (c.map (a * ·)) X = a * dotR c X
  | [], _ => by simp [dotR]
  | b :: l, X => by
    simp only [List.map_cons, dotR, dotR_map_mul a l]
    push_cast
    ring

theorem dotR_replicate_zero : ∀ (n : ℕ) (X : ℕ → ℝ), dotR (List.replicate n 0) X = 0
  | 0, _ => by simp [dotR]
  | n + 1, X => by simp [List.replicate_succ, dotR, dotR_replicate_zero n]

theorem dotR_append : ∀ (c d : List ℤ) (X : ℕ → ℝ), dotR (c ++ d) X = dotR c X + dotR d fun j => X (j + c.length)
  | [], d, X => by simp [dotR]
  | a :: l, d, X => by
    simp only [List.cons_append, dotR, dotR_append l d]
    have : (fun j => X (j + l.length + 1)) = fun j => X (j + (a :: l).length) := by
      funext j; rw [List.length_cons, Nat.add_assoc]
    rw [this]
    ring

end ShortSieveCert

#print axioms ShortSieveCert.LF.min_le
#print axioms ShortSieveCert.Con.not_holds_of_fails
#print axioms ShortSieveCert.tightenList_sound
#print axioms ShortSieveCert.not_isEmpty
