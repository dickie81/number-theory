import ShortSieveDrop

/-!
# The certificate's tree: what each decision proves

The certificate bounds a sum of sieve terms by a tree. Each node is a term that enters Li's identity with a sign
`σ = ±1`. A `+` node needs a lower bound in `A = (x − y, x]` and a `−` node an upper one, both against `y/x^{1−ρ}`
times the term in the comparison interval `B = (x − x^{1−ρ}, x]`. A term is `OK` with loss `L` when, for every
`ε > 0`, large `x` and `y ∈ [x^θ, x^{1−ρ}]`, `σ(F(A) − (y/x^{1−ρ}) F(B)) ≥ −(L + ε) y/log x`.

* `OK_of_asym`: an asymptotic term (`Asym`) is `OK` with no loss, either sign.
* `OK_of_drop`: a `+` term whose count in `B` is at most `(L + δ) x^{1−ρ}/log x` for every `δ > 0` is `OK` with
  loss `L` (its count in `A` is at least `0`).
* `OK_add`, `OK_sum`: the losses of a split add up.
* `OK_sub`: Buchstab's step, `F = J − G` with `J` asymptotic and `G` `OK` with the opposite sign and loss `L`.
* `OK_congr`, `OK_mono`, `OK_zero`: equal terms, larger losses, and terms that vanish.
* `Cond.neg`, `count_split`: a node's count is the sum of its counts with a condition and with its complement, the
  certificate's split of a box.
-/

open Finset Real Filter

namespace ShortSieveTree

open ShortSieveNode

/-- An asymptotic term: `|F(A) − (y/x^{1−ρ}) F(B)| ≤ ε y/log x` for every `ε > 0`, large `x` and
`y ∈ [x^θ, x^{1−ρ}]`. -/
def Asym (θ ρ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
    |F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))| ≤ ε * y / Real.log x

/-- A term bounded with loss `L` for the sign `σ`: `σ(F(A) − (y/x^{1−ρ}) F(B)) ≥ −(L + ε) y/log x` for every
`ε > 0`, large `x` and `y ∈ [x^θ, x^{1−ρ}]`. -/
def OK (θ ρ σ : ℝ) (F : ℝ → ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
    -((L + ε) * y / Real.log x) ≤ σ * (F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ)))

/-- `y/log x ≥ 0` for `x > 1` and `y ≥ x^θ`. -/
theorem div_log_nonneg {θ x y : ℝ} (hx : 1 < x) (hy : x ^ θ ≤ y) : 0 ≤ y / Real.log x :=
  div_nonneg (le_trans (Real.rpow_nonneg (by linarith) _) hy) (Real.log_nonneg hx.le)

/-- **An asymptotic term has no loss**, for either sign. -/
theorem OK_of_asym {θ ρ σ : ℝ} {F : ℝ → ℝ → ℝ} (hσ : |σ| ≤ 1) (h : Asym θ ρ F) : OK θ ρ σ F 0 := by
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop 1] with x hx hx1 y hy1 hy2
  have hu := div_log_nonneg hx1 hy1
  have h1 := hx y hy1 hy2
  have h2 : |σ * (F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ)))| ≤ ε * y / Real.log x := by
    rw [abs_mul]
    calc |σ| * |F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))| ≤ 1 * (ε * y / Real.log x) :=
          mul_le_mul hσ h1 (abs_nonneg _) zero_le_one
      _ = ε * y / Real.log x := one_mul _
  have h3 := (abs_le.1 h2).1
  rw [zero_add]
  exact h3

/-- **A dropped term.** If `F ≥ 0` and, for every `δ > 0`, eventually `F(B) ≤ (L + δ) x^{1−ρ}/log x`, then `F` is
`OK` for `σ = 1` with loss `L`. -/
theorem OK_of_drop {θ ρ L : ℝ} {F : ℝ → ℝ → ℝ} (hF : ∀ x y, 0 ≤ F x y)
    (hB : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop, F x (x ^ (1 - ρ)) ≤ (L + δ) * (x ^ (1 - ρ) / Real.log x)) :
    OK θ ρ 1 F L := by
  intro ε hε
  filter_upwards [hB ε hε, eventually_gt_atTop 1] with x hx hx1 y hy1 _
  have hx0 : 0 < x := by linarith
  have hy₁ : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx0 _
  have hc : 0 ≤ y / x ^ (1 - ρ) := div_nonneg (le_trans (Real.rpow_nonneg hx0.le _) hy1) hy₁.le
  have h1 : y / x ^ (1 - ρ) * F x (x ^ (1 - ρ)) ≤ (L + ε) * y / Real.log x := by
    calc y / x ^ (1 - ρ) * F x (x ^ (1 - ρ)) ≤ y / x ^ (1 - ρ) * ((L + ε) * (x ^ (1 - ρ) / Real.log x)) :=
          mul_le_mul_of_nonneg_left hx hc
      _ = (L + ε) * y / Real.log x := by field_simp
  have := hF x y
  rw [one_mul]
  linarith

/-- **The losses of a split add up.** -/
theorem OK_add {θ ρ σ L₁ L₂ : ℝ} {F G : ℝ → ℝ → ℝ} (h₁ : OK θ ρ σ F L₁) (h₂ : OK θ ρ σ G L₂) :
    OK θ ρ σ (fun x y => F x y + G x y) (L₁ + L₂) := by
  intro ε hε
  filter_upwards [h₁ (ε / 2) (by linarith), h₂ (ε / 2) (by linarith)] with x hx₁ hx₂ y hy1 hy2
  have e1 := hx₁ y hy1 hy2
  have e2 := hx₂ y hy1 hy2
  have e : (L₁ + L₂ + ε) * y / Real.log x = (L₁ + ε / 2) * y / Real.log x + (L₂ + ε / 2) * y / Real.log x := by
    ring
  rw [e]
  have e' : σ * (F x y + G x y - y / x ^ (1 - ρ) * (F x (x ^ (1 - ρ)) + G x (x ^ (1 - ρ)))) =
      σ * (F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))) + σ * (G x y - y / x ^ (1 - ρ) * G x (x ^ (1 - ρ))) := by
    ring
  rw [e']
  linarith

/-- **Buchstab's step.** If `F = J − G` with `J` asymptotic and `G` `OK` for `−σ` with loss `L` (`|σ| ≤ 1`), then
`F` is `OK` for `σ` with loss `L`. -/
theorem OK_sub {θ ρ σ L : ℝ} {J G : ℝ → ℝ → ℝ} (hσ : |σ| ≤ 1) (hJ : Asym θ ρ J) (hG : OK θ ρ (-σ) G L) :
    OK θ ρ σ (fun x y => J x y - G x y) L := by
  have hJ' := OK_of_asym hσ hJ
  intro ε hε
  filter_upwards [hJ' (ε / 2) (by linarith), hG (ε / 2) (by linarith)] with x hx₁ hx₂ y hy1 hy2
  have e1 := hx₁ y hy1 hy2
  have e2 := hx₂ y hy1 hy2
  have e : σ * (J x y - G x y - y / x ^ (1 - ρ) * (J x (x ^ (1 - ρ)) - G x (x ^ (1 - ρ)))) =
      σ * (J x y - y / x ^ (1 - ρ) * J x (x ^ (1 - ρ))) +
        -σ * (G x y - y / x ^ (1 - ρ) * G x (x ^ (1 - ρ))) := by ring
  rw [e]
  have e' : (L + ε) * y / Real.log x = (0 + ε / 2) * y / Real.log x + (L + ε / 2) * y / Real.log x := by ring
  rw [e']
  linarith

/-- Terms equal for large `x` and all `y ∈ [x^θ, x^{1−ρ}]` (and at `y = x^{1−ρ}`) are `OK` together. -/
theorem OK_congr {θ ρ σ L : ℝ} {F G : ℝ → ℝ → ℝ}
    (hFG : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → F x y = G x y)
    (hθρ : θ ≤ 1 - ρ) (h : OK θ ρ σ F L) : OK θ ρ σ G L := by
  intro ε hε
  filter_upwards [h ε hε, hFG, eventually_ge_atTop 1] with x hx hxe hx1 y hy1 hy2
  have hB := hxe (x ^ (1 - ρ)) (Real.rpow_le_rpow_of_exponent_le hx1 hθρ) le_rfl
  rw [← hxe y hy1 hy2, ← hB]
  exact hx y hy1 hy2

/-- A larger loss. -/
theorem OK_mono {θ ρ σ L L' : ℝ} {F : ℝ → ℝ → ℝ} (hL : L ≤ L') (h : OK θ ρ σ F L) : OK θ ρ σ F L' := by
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop 1] with x hx hx1 y hy1 hy2
  have hu := div_log_nonneg hx1 hy1
  have := hx y hy1 hy2
  have h1 : (L + ε) * y / Real.log x ≤ (L' + ε) * y / Real.log x := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hu
  linarith

/-- A term that vanishes for large `x` has no loss. -/
theorem OK_zero {θ ρ σ : ℝ} {F : ℝ → ℝ → ℝ} (hθρ : θ ≤ 1 - ρ)
    (h : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → F x y = 0) : OK θ ρ σ F 0 := by
  intro ε hε
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1 y hy1 hy2
  have hu := div_log_nonneg hx1 hy1
  have hB := hx (x ^ (1 - ρ)) (Real.rpow_le_rpow_of_exponent_le hx1.le hθρ) le_rfl
  rw [hx y hy1 hy2, hB]
  have : 0 ≤ (0 + ε) * y / Real.log x := by rw [zero_add, mul_div_assoc]; exact mul_nonneg hε.le hu
  simp only [mul_zero, sub_zero]
  linarith

/-- **The losses of a finite split add up.** -/
theorem OK_sum {ι : Type*} (s : Finset ι) {θ ρ σ : ℝ} (F : ι → ℝ → ℝ → ℝ) (L : ι → ℝ) (hθρ : θ ≤ 1 - ρ)
    (h : ∀ i ∈ s, OK θ ρ σ (F i) (L i)) :
    OK θ ρ σ (fun x y => ∑ i ∈ s, F i x y) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact OK_zero hθρ (Filter.Eventually.of_forall fun _ _ _ _ => rfl)
  | insert a s has ih =>
    have h1 := h a (mem_insert_self a s)
    have h2 := ih fun i hi => h i (mem_insert_of_mem hi)
    have h3 := OK_add h1 h2
    simp only [sum_insert has]
    exact h3

/-! ### Splitting a node by a condition -/

/-- The complement of a condition: `Σ ≤ b` becomes `−Σ < −b`, and `Σ < b` becomes `−Σ ≤ −b`. -/
def _root_.ShortSieveNode.Cond.neg {k m : ℕ} (C : Cond k m) : Cond k m := ⟨-C.e, -C.f, fun x => -C.b x, !C.strict⟩

theorem holds_neg {k m : ℕ} (C : Cond k m) (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) :
    C.neg.Holds x p ρ ↔ ¬ C.Holds x p ρ := by
  have hv : C.neg.val p ρ = -C.val p ρ := by
    unfold Cond.val Cond.neg
    simp only [Pi.neg_apply, neg_mul, sum_neg_distrib, neg_add]
  unfold Cond.Holds
  rw [hv]
  cases hs : C.strict <;> simp [Cond.neg, hs, not_lt, not_le, neg_lt_neg_iff, neg_le_neg_iff]

open Classical in
/-- **Splitting a node by a condition.** The node's count is the sum of its counts with the condition `C` and with
its complement. -/
theorem count_split (N : Node) (C : Cond N.k N.m) (x y : ℝ) :
    N.count x y = (⟨N.k, N.m, N.s, C :: N.conds⟩ : Node).count x y +
      (⟨N.k, N.m, N.s, C.neg :: N.conds⟩ : Node).count x y := by
  unfold Node.count
  rw [← card_union_of_disjoint]
  · congr 1
    ext v
    rw [mem_union, ShortSieveBuch.mem_filter_inst, ShortSieveBuch.mem_filter_inst, ShortSieveBuch.mem_filter_inst]
    simp only [Node.InI, List.mem_cons, forall_eq_or_imp]
    rw [holds_neg]
    tauto
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [ShortSieveBuch.mem_filter_inst] at hv hv'
    obtain ⟨-, -, h1, -⟩ := hv
    obtain ⟨-, -, h2, -⟩ := hv'
    simp only [List.mem_cons, forall_eq_or_imp] at h1 h2
    exact (holds_neg C x v.1 v.2).1 h2.1 h1.1

end ShortSieveTree

#print axioms ShortSieveTree.OK_of_asym
#print axioms ShortSieveTree.OK_of_drop
#print axioms ShortSieveTree.OK_sub
#print axioms ShortSieveTree.OK_sum
#print axioms ShortSieveTree.count_split
