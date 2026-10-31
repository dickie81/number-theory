import ShortSieveCertSem

/-!
# Buchstab's step on a certificate node

A Buchstab step on the rough item `i₀` of a node adds a prime `p_{last} ∈ [x^a ∏ p_j^{−b_j}, p_{s(i₀)})` dividing
it (`ShortSieveNode.Node.buch`). The certificate's child keeps the parent's coordinates, the new prime taking the
coefficients of the item it divides (`buchRows`), and adds a coordinate: the new prime's exponent.

* `coords_buch`, `slack_buch`: a child pair's coordinates below the new one, and its slack, are those of the parent
  pair it comes from (`ρ_{i₀} = p_{last} ρ'_{i₀}`).
* `Sound.buch`: the parent's constraints hold at the child's pairs; with the new coordinate's range and the child's
  new constraints, the child is sound.
-/

open Finset Real

namespace ShortSieveCert

open ShortSieveNode ShortSieveBuch

open Classical

/-- The rows of a Buchstab child at the item `i₀`: below the coordinate `d` the new prime (the last) has the
coefficients of the item `i₀` it divides; the coordinate `d` is the new prime's exponent. -/
def buchRows {k m : ℕ} (A : Rows k m) (i₀ : Fin m) (d : ℕ) : Rows (k + 1) m := fun j t =>
  if j = d then Sum.elim (fun a => if a = Fin.last k then 1 else 0) (fun _ => 0) t
  else Sum.elim (Fin.lastCases (A j (Sum.inr i₀)) fun a => A j (Sum.inl a)) (fun i => A j (Sum.inr i)) t

/-- The parent pair of a child pair: `ρ_{i₀} = p_{last} ρ'_{i₀}`. -/
def merge {k m : ℕ} (i₀ : Fin m) (v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)) : (Fin k → ℕ) × (Fin m → ℕ) :=
  (Fin.init v.1, Function.update v.2 i₀ (v.1 (Fin.last k) * v.2 i₀))

theorem expo_merge {k m : ℕ} (i₀ : Fin m) (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)}
    (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) (t : Fin k ⊕ Fin m) :
    expo x (merge i₀ v) t = Sum.elim (fun a => expo x v (Sum.inl a.castSucc))
      (fun i => if i = i₀ then expo x v (Sum.inl (Fin.last k)) + expo x v (Sum.inr i) else expo x v (Sum.inr i)) t := by
  rcases t with a | i
  · simp [expo, merge, Fin.init]
  · simp only [expo, merge, Sum.elim_inr]
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self, ite_eq_left rfl, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast (hv1 _).ne') (by exact_mod_cast (hv2 _).ne'), add_div]
      rfl
    · rw [Function.update_of_ne hi, ite_eq_right hi]

/-- **The coordinates of a child pair** below the new one are those of its parent pair. -/
theorem coords_buch {k m : ℕ} (A : Rows k m) (i₀ : Fin m) {d : ℕ} (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)}
    (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) {j : ℕ} (hj : j ≠ d) :
    coords (buchRows A i₀ d) x v j = coords A x (merge i₀ v) j := by
  unfold coords
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [buchRows, ite_eq_right hj, Sum.elim_inl, Sum.elim_inr, Fin.lastCases_castSucc, Fin.lastCases_last,
    expo_merge i₀ x hv1 hv2]
  have e : ∀ i : Fin m, (A j (Sum.inr i) : ℝ) * (if i = i₀ then expo x v (Sum.inl (Fin.last k)) +
      expo x v (Sum.inr i) else expo x v (Sum.inr i)) = (A j (Sum.inr i) : ℝ) * expo x v (Sum.inr i) +
        if i = i₀ then (A j (Sum.inr i₀) : ℝ) * expo x v (Sum.inl (Fin.last k)) else 0 := fun i => by
    split_ifs with h
    · subst h; ring
    · ring
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq' univ i₀, ite_eq_left (mem_univ i₀)]
  ring

/-- **The slack of a child pair** is its parent pair's. -/
theorem slack_buch {k m : ℕ} (i₀ : Fin m) (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) : slack x v = slack x (merge i₀ v) := by
  unfold slack
  congr 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [expo_merge i₀ x hv1 hv2, Sum.elim_inl, Sum.elim_inr]
  have e : ∀ i : Fin m, (if i = i₀ then expo x v (Sum.inl (Fin.last k)) + expo x v (Sum.inr i)
      else expo x v (Sum.inr i)) = expo x v (Sum.inr i) +
        if i = i₀ then expo x v (Sum.inl (Fin.last k)) else 0 := fun i => by
    split_ifs <;> ring
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq' univ i₀, ite_eq_left (mem_univ i₀)]
  ring

end ShortSieveCert

namespace ShortSieveCert

open ShortSieveNode ShortSieveBuch ShortSieveExpand

open Classical

/-! ### The child's invariant -/

theorem dotR_congr : ∀ (c : List ℤ) {X Y : ℕ → ℝ}, (∀ j < c.length, X j = Y j) → dotR c X = dotR c Y
  | [], _, _, _ => rfl
  | a :: l, X, Y, h => by
    simp only [dotR]
    rw [h 0 (by simp), dotR_congr l fun j hj => h (j + 1) (by simp; omega)]

theorem Con.holds_congr (C : Con) {n : ℕ} (hlen : C.L.c.length ≤ n) {X Y : ℕ → ℝ} (h : ∀ j < n, X j = Y j)
    (H : ℝ) : C.Holds X H ↔ C.Holds Y H := by
  have e : C.L.val X H = C.L.val Y H := by
    unfold LF.val
    rw [dotR_congr C.L.c fun j hj => h j (lt_of_lt_of_le hj hlen)]
  unfold Con.Holds
  rw [e]

theorem inBox_congr : ∀ (B : Box) {X Y : ℕ → ℝ}, (∀ j < B.length, X j = Y j) → InBox B X → InBox B Y
  | [], _, _, _, h => h
  | b :: B, X, Y, h, ⟨h1, h2, hB⟩ => by
    refine ⟨by rw [← h 0 (by simp)]; exact h1, by rw [← h 0 (by simp)]; exact h2,
      inBox_congr B (fun j hj => h (j + 1) (by simp; omega)) hB⟩

theorem inBox_append : ∀ (B : Box) (X : ℕ → ℝ) (b : ℤ × ℤ), InBox B X → (b.1 : ℝ) ≤ X B.length →
    X B.length < b.2 → InBox (B ++ [b]) X
  | [], _, _, _, h1, h2 => ⟨h1, h2, trivial⟩
  | _ :: B, _, b, ⟨h1, h2, hB⟩, h3, h4 => ⟨h1, h2, inBox_append B _ b hB h3 h4⟩

/-- A child pair's parent satisfies the parent's conditions. -/
theorem holds_merge {k m : ℕ} (C : Cond k m) (i₀ : Fin m) (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)}
    (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) (h : (C.split i₀).Holds x v.1 v.2) :
    C.Holds x (merge i₀ v).1 (merge i₀ v).2 := by
  have e1 : v.1 = Fin.snoc (Fin.init v.1) (v.1 (Fin.last k)) := (Fin.snoc_init_self v.1).symm
  have e2 : v.2 = Function.update (Function.update v.2 i₀ (v.1 (Fin.last k) * v.2 i₀)) i₀ (v.2 i₀) := by
    rw [Function.update_idem, Function.update_eq_self]
  rw [e1, e2] at h
  exact (holds_split C i₀ x _ _ (hv1 _) (hv2 i₀) (Function.update_self ..)).1 h

/-- **The Buchstab child is sound.** The parent's constraints hold at the child's pairs, at the same coordinates;
with the range of the new coordinate and the child's new constraints, the child is sound with the parent's box
extended by that range. -/
theorem Sound.buch {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hf : fits Γ B.length = true) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) (lo hi : ℤ) (Γ' : List Con)
    (hnew : ∀ x : ℝ, 1 < x → ∀ v : (Fin (N.k + 1) → ℕ) × (Fin N.m → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
      (∀ C ∈ (N.buch i₀ a b).conds, C.Holds x v.1 v.2) → |slack x v| ≤ E →
        (lo : ℝ) ≤ coords (buchRows A i₀ B.length) x v B.length ∧
          coords (buchRows A i₀ B.length) x v B.length < hi ∧
          ∀ c ∈ Γ', c.Holds (coords (buchRows A i₀ B.length) x v) (slack x v)) :
    Sound (N.buch i₀ a b) (buchRows A i₀ B.length) E (Γ ++ Γ') (B ++ [(lo, hi)]) := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨h1, h2, hΓ'⟩ := hnew x hx v hv1 hv2 hc hH
  have hw1 : ∀ a, 0 < (merge i₀ v).1 a := fun a => hv1 _
  have hw2 : ∀ i, 0 < (merge i₀ v).2 i := fun i => by
    simp only [merge]
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      exact Nat.mul_pos (hv1 _) (hv2 _)
    · rw [Function.update_of_ne hi]
      exact hv2 i
  have hcw : ∀ C ∈ N.conds, C.Holds x (merge i₀ v).1 (merge i₀ v).2 := fun C hC =>
    holds_merge C i₀ x hv1 hv2 (hc (C.split i₀) (List.mem_append_left _ (List.mem_map_of_mem hC)))
  have hsl : slack x v = slack x (merge i₀ v) := slack_buch i₀ x hv1 hv2
  obtain ⟨hB, hΓ⟩ := h x hx (merge i₀ v) hw1 hw2 hcw (hsl ▸ hH)
  have hagree : ∀ j < B.length, coords A x (merge i₀ v) j = coords (buchRows A i₀ B.length) x v j :=
    fun j hj => (coords_buch A i₀ x hv1 hv2 (Nat.ne_of_lt hj)).symm
  refine ⟨inBox_append B _ _ (inBox_congr B hagree hB) h1 h2, fun c hc' => ?_⟩
  rcases List.mem_append.1 hc' with hcΓ | hcΓ'
  · have hlen : c.L.c.length ≤ B.length := by
      simp only [fits, List.all_eq_true, decide_eq_true_eq] at hf
      exact hf c hcΓ
    rw [hsl]
    exact (c.holds_congr hlen hagree _).1 (hΓ c hcΓ)
  · exact hΓ' c hcΓ'

/-- **An implied condition** leaves a node's count unchanged: if every term in `(x − y, x]` satisfies `C`, adding
`C` to the conditions keeps the count. The certificate adds, this way, conditions that follow from the rough items'
roughness, such as `ρ' ≥ p_{last}` after a Buchstab step. -/
theorem count_cons_of_implied (N : Node) (C : Cond N.k N.m) (x y : ℝ)
    (h : ∀ v ∈ pairs N.k N.m ⌊x⌋₊, (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) → N.InI x y v.1 v.2 →
      C.Holds x v.1 v.2) :
    (⟨N.k, N.m, N.s, C :: N.conds⟩ : Node).count x y = N.count x y := by
  unfold Node.count
  congr 1
  ext v
  rw [ShortSieveBuch.mem_filter_inst, ShortSieveBuch.mem_filter_inst]
  constructor
  · rintro ⟨hv, hr, hc, h1, h2⟩
    exact ⟨hv, hr, fun C' hC' => hc C' (List.mem_cons_of_mem _ hC'), h1, h2⟩
  · rintro ⟨hv, hr, hc, h1, h2⟩
    refine ⟨hv, hr, fun C' hC' => ?_, h1, h2⟩
    rcases List.mem_cons.1 hC' with h' | hC'
    · rw [h']
      exact h v hv hr ⟨hc, h1, h2⟩
    · exact hc C' hC'

end ShortSieveCert

#print axioms ShortSieveCert.coords_buch
#print axioms ShortSieveCert.slack_buch
#print axioms ShortSieveCert.Sound.buch
#print axioms ShortSieveCert.count_cons_of_implied
