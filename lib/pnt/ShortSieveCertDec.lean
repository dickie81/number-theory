import ShortSieveCertStd
import ShortSieveTypeI

/-!
# The certificate's decompositions of standard nodes

A standard node (`std`) has `k + 1` primes and one rough item, sifted by the last prime: Li's
`S(A_{p₁⋯p_{k+1}}, p_{k+1})`. Its conditions keep two invariants: its primes are at least `x^{1/25}` and the rough
item at least the last prime (`StdInv`), and no condition is a function of the product alone (`CondsOK`).

* A split writes the node as the sum of the nodes with a condition and with its negation (`OK_of_split`), and keeps the
  invariants (`StdInv.cons`, `CondsOK.split`).
* A decomposition writes the node as a Type I term minus its child, by Buchstab's identity at the level `x^{1/25}`
  (`ShortSieveBuch.count_buchstab`): `N = J − G`. When the box lies in Li's regions `D′₀`, `D′₁` or `D′₂` for a grouping
  of the primes (`typeICheck`), the Type I term is asymptotic by Li's Lemmas 3.1 and 3.2, so the node's loss is the
  child's, for the opposite sign: `Sound.OK_of_dec`. The child's coordinates and invariants: `Sound.std_child`,
  `StdInv.child`, `CondsOK.child`.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree ShortSieveTypeI

open Classical

/-- **Buchstab's decision.** If the level is at most the sifting prime at the node's pairs, the Type I term
`N.toJ i₀ a b` is asymptotic and the Buchstab child is `OK` for `−σ` with loss `L`, then the node is `OK` for `σ` with
loss `L`. -/
theorem OK_of_buch (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ)
    (hlvl : ∀ᶠ x in atTop, ∀ v ∈ pairs N.k N.m ⌊x⌋₊, (∀ C ∈ N.conds, C.Holds x v.1 v.2) →
      lvlOf a b x v.1 ≤ v.1 (N.s i₀))
    {θ ρ σ L : ℝ} (hθρ : θ ≤ 1 - ρ) (hσ : |σ| ≤ 1) (hJ : Asym θ ρ (fun x y => ((N.toJ i₀ a b).count x y : ℝ)))
    (hG : OK θ ρ (-σ) (fun x y => ((N.buch i₀ a b).count x y : ℝ)) L) :
    OK θ ρ σ (fun x y => (N.count x y : ℝ)) L := by
  refine OK_congr ?_ hθρ (OK_sub hσ hJ hG)
  filter_upwards [hlvl, eventually_gt_atTop 0] with x hx hx0 y _ _
  rw [count_buchstab N i₀ a b hx0 y fun v hv hc => hx v hv hc]
  push_cast
  ring

/-- **A relative error is asymptotic** when the count in the comparison interval is `O(x^{1−ρ}/log x)`: Li's
Lemmas 3.1 and 3.2 give `|F(A) − (y/x^{1−ρ})F(B)| ≤ ε (y/x^{1−ρ}) F(B) + C y/log² x`. -/
theorem asym_of_rel {θ ρ : ℝ} {F : ℝ → ℝ → ℝ}
    (hrel : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))| ≤ ε * (y / x ^ (1 - ρ)) * F x (x ^ (1 - ρ)) +
        C * y / Real.log x ^ 2)
    (hB : ∃ CB : ℝ, 0 ≤ CB ∧ ∀ᶠ x : ℝ in atTop, F x (x ^ (1 - ρ)) ≤ CB * x ^ (1 - ρ) / Real.log x) :
    Asym θ ρ F := by
  obtain ⟨C, hC⟩ := hrel
  obtain ⟨CB, hCB0, hCB⟩ := hB
  intro ε hε
  set ε' : ℝ := min 1 (ε / (2 * (CB + 1))) with hε'
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'C : ε' * CB ≤ ε / 2 := by
    have h1 : ε' ≤ ε / (2 * (CB + 1)) := min_le_right _ _
    calc ε' * CB ≤ ε / (2 * (CB + 1)) * CB := mul_le_mul_of_nonneg_right h1 hCB0
      _ ≤ ε / (2 * (CB + 1)) * (CB + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
  have hev : ∀ᶠ x : ℝ in atTop, |C| ≤ ε / 2 * Real.log x :=
    (Real.tendsto_log_atTop.const_mul_atTop (by positivity : 0 < ε / 2)).eventually_ge_atTop _
  filter_upwards [hC ε' hε'0 hε'1, hCB, hev, eventually_gt_atTop (1 : ℝ)] with x hx hxB hxl hx1 y hy1 hy2
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hx0.le _) hy1
  have hx1ρ : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx0 _
  have h1 : ε' * (y / x ^ (1 - ρ)) * F x (x ^ (1 - ρ)) ≤ ε / 2 * y / Real.log x := by
    calc ε' * (y / x ^ (1 - ρ)) * F x (x ^ (1 - ρ)) ≤ ε' * (y / x ^ (1 - ρ)) * (CB * x ^ (1 - ρ) / Real.log x) :=
          mul_le_mul_of_nonneg_left hxB (by positivity)
      _ = ε' * CB * y / Real.log x := by field_simp
      _ ≤ ε / 2 * y / Real.log x := by
          apply div_le_div_of_nonneg_right _ hlx.le
          exact mul_le_mul_of_nonneg_right hε'C hy0
  have h2 : C * y / Real.log x ^ 2 ≤ ε / 2 * y / Real.log x := by
    have e : ε / 2 * y / Real.log x = ε / 2 * Real.log x * y / Real.log x ^ 2 := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans hxl) hy0
  calc |F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))| ≤ _ := hx y hy1 hy2
    _ ≤ ε / 2 * y / Real.log x + ε / 2 * y / Real.log x := add_le_add h1 h2
    _ = ε * y / Real.log x := by ring


/-! ### Standard nodes -/

/-- A standard node: `k + 1` primes and one rough item, sifted by the last prime. -/
@[reducible] def std (k : ℕ) (conds : List (Cond (k + 1) 1)) : Node := ⟨k + 1, 1, fun _ => Fin.last k, conds⟩

/-- The invariant of a standard node's conditions: its primes are at least `x^{1/25}`, and the rough item at least the
last prime. -/
def StdInv (k : ℕ) (conds : List (Cond (k + 1) 1)) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ v : (Fin (k + 1) → ℕ) × (Fin 1 → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
    (∀ C ∈ conds, C.Holds x v.1 v.2) → (∀ a, x ^ (1 / 25 : ℝ) ≤ v.1 a) ∧ v.1 (Fin.last k) ≤ v.2 0

/-- Conditions that are not functions of the product alone. -/
def CondsOK {k m : ℕ} (conds : List (Cond k m)) : Prop :=
  ∀ C ∈ conds, ∃ u w : Fin k ⊕ Fin m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w

/-- A standard node's terms have primes above `x^c`, for `c < 1/25`, and rough items above `1`. -/
theorem StdInv.big {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : StdInv k conds) {c : ℝ} (hc1 : c < 1 / 25) :
    ∀ᶠ x in atTop, ∀ v ∈ (std k conds).terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i := by
  filter_upwards [eventually_gt_atTop 1] with x hx v hv
  obtain ⟨hvp, -, hcv⟩ := mem_filter.1 hv
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hvp
  obtain ⟨h1, h3⟩ := h x hx v (fun a => (hp a).2.pos) (fun i => (hρ i).1) hcv
  refine ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le (h1 a), fun i => ?_⟩
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  have hxc : (1 : ℝ) < x ^ (1 / 25 : ℝ) := Real.one_lt_rpow hx (by norm_num)
  have := (h1 (Fin.last k)).trans (Nat.cast_le.2 h3)
  exact_mod_cast hxc.trans_le this

/-! ### The Type I term -/

/-- The Type I term of a standard node's Buchstab step at the level `x^{1/25}`. -/
@[reducible] noncomputable def stdT (k : ℕ) (conds : List (Cond (k + 1) 1)) : TNode :=
  ⟨k + 1, 0, Fin.elim0, 1 / 25, conds⟩

theorem stdT_toJ (k : ℕ) (conds : List (Cond (k + 1) 1)) :
    (stdT k conds).toJ = (std k conds).toJ 0 (1 / 25) (fun _ => 0) := by
  simp only [TNode.toJ, Node.toJ, stdT, std]
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  rfl


/-! ### Splits -/

theorem wt_std_inl (K : ℕ) (L : LF) (a : Fin K) : wt (stdRows K) L (Sum.inl a) = L.c.getD a 0 - L.ce := by
  unfold wt stdRows
  simp only [Sum.elim_inl, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp

theorem wt_std_inr (K : ℕ) (L : LF) (i : Fin 1) : wt (stdRows K) L (Sum.inr i) = -L.ce := by
  simp [wt, stdRows]


/-- A constraint with a nonzero coefficient on a prime of a standard node's `k + 1`: its condition is not a function of
the product alone. -/
def nonDeg (k : ℕ) (C : Con) : Bool := (List.range (k + 1)).any fun a => C.L.c.getD a 0 ≠ 0

/-- More conditions keep the invariant. -/
theorem StdInv.cons {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : StdInv k conds) (C : Cond (k + 1) 1) :
    StdInv k (C :: conds) := fun x hx v hv1 hv2 hc => h x hx v hv1 hv2 fun C' h' => hc C' (List.mem_cons_of_mem _ h')

/-- **A split keeps the conditions not functions of the product alone**: a nondegenerate constraint's condition and its
negation. -/
theorem CondsOK.split {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : CondsOK conds) {C : Con} (hC : nonDeg k C = true) :
    CondsOK (toCond (stdRows (k + 1)) C :: conds) ∧ CondsOK ((toCond (stdRows (k + 1)) C).neg :: conds) := by
  simp only [nonDeg, List.any_eq_true, List.mem_range, decide_eq_true_eq] at hC
  obtain ⟨a, ha, hca⟩ := hC
  have hne : wt (stdRows (k + 1)) C.L (Sum.inl ⟨a, ha⟩) ≠ wt (stdRows (k + 1)) C.L (Sum.inr 0) := by
    rw [wt_std_inl, wt_std_inr]
    intro he
    exact hca (by exact_mod_cast (show ((C.L.c.getD a 0 : ℤ) : ℝ) = 0 by linarith))
  refine ⟨fun C' hC' => ?_, fun C' hC' => ?_⟩
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · exact ⟨Sum.inl ⟨a, ha⟩, Sum.inr 0, hne⟩
    · exact h C' hC'
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · refine ⟨Sum.inl ⟨a, ha⟩, Sum.inr 0, fun he => hne ?_⟩
      simp only [Cond.neg, toCond, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_inj] at he
      exact he
    · exact h C' hC'

/-- **A split's losses add up.** -/
theorem OK_of_split {k : ℕ} {conds : List (Cond (k + 1) 1)} (C : Cond (k + 1) 1) {θ ρ σ L₁ L₂ : ℝ}
    (h₁ : OK θ ρ σ (fun x y => ((std k (C :: conds)).count x y : ℝ)) L₁)
    (h₂ : OK θ ρ σ (fun x y => ((std k (C.neg :: conds)).count x y : ℝ)) L₂) :
    OK θ ρ σ (fun x y => ((std k conds).count x y : ℝ)) (L₁ + L₂) := by
  have e : (fun x y => ((std k conds).count x y : ℝ)) =
      fun x y => ((std k (C :: conds)).count x y : ℝ) + ((std k (C.neg :: conds)).count x y : ℝ) := by
    funext x y
    rw [count_split (std k conds) C x y]
    push_cast
    rfl
  rw [e]
  exact OK_add h₁ h₂

/-! ### The Buchstab child -/

/-- The rough item is at least the prime `k`: `X_k ≤ DEN − Σ_{j ≤ k} X_j − H`. -/
def geCon (k : ℕ) : Con := ⟨⟨-DEN, List.replicate k 1 ++ [2], 1⟩, false⟩

/-- The order `X_{k+1} < X_k` of the last two primes. -/
def ordCon (k : ℕ) : Con := ⟨⟨0, List.replicate k 0 ++ [-1, 1], 0⟩, true⟩

/-- The level's coordinate `DEN/25`. -/
def NU0 : ℤ := 4 * 2 ^ 30

theorem NU0_eq : (NU0 : ℝ) = DEN / 25 := by norm_num [NU0, DEN]

/-- The conditions of the Buchstab child: the node's, split, with the level `x^{1/25} ≤ p_{k+1}` and the order
`p_{k+1} < p_k`. -/
noncomputable def buchConds (k : ℕ) (conds : List (Cond (k + 1) 1)) : List (Cond (k + 2) 1) :=
  conds.map (Cond.split · 0) ++ [lvlCond (1 / 25) (fun _ => 0), ltCond (Fin.last k)]

/-- The child's conditions: with the rough item at least the new prime, which the child's terms satisfy. -/
noncomputable def stdChild (k : ℕ) (conds : List (Cond (k + 1) 1)) : List (Cond (k + 2) 1) :=
  toCond (stdRows (k + 2)) (geCon (k + 1)) :: buchConds k conds

theorem buch_std (k : ℕ) (conds : List (Cond (k + 1) 1)) :
    (std k conds).buch 0 (1 / 25) (fun _ => 0) = std (k + 1) (buchConds k conds) := by
  simp only [Node.buch, std, buchConds]
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  simp

/-- The child's added condition is `p_{k+1} ≤ ρ`. -/
theorem holds_geCon {k : ℕ} (x : ℝ) {v : (Fin (k + 2) → ℕ) × (Fin 1 → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) :
    (toCond (stdRows (k + 2)) (geCon (k + 1))).Holds x v.1 v.2 ↔ v.1 (Fin.last (k + 1)) ≤ v.2 0 := by
  have he : ∀ a : Fin (k + 2), wt (stdRows (k + 2)) (geCon (k + 1)).L (Sum.inl a) =
      if a = Fin.last (k + 1) then 1 else 0 := by
    intro a
    rw [wt_std_inl]
    induction a using Fin.lastCases with
    | last => norm_num [geCon]
    | cast j =>
      rw [ite_eq_right (Fin.castSucc_ne_last j)]
      have hj : (j.castSucc : ℕ) < (List.replicate (k + 1) (1 : ℤ)).length := by
        rw [List.length_replicate, Fin.val_castSucc]
        exact j.isLt
      simp only [geCon]
      rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj, List.getElem_replicate]
      simp
  have hf : wt (stdRows (k + 2)) (geCon (k + 1)).L (Sum.inr 0) = -1 := by
    rw [wt_std_inr]
    simp [geCon]
  have hval : (toCond (stdRows (k + 2)) (geCon (k + 1))).val v.1 v.2 =
      Real.log (v.1 (Fin.last (k + 1))) - Real.log (v.2 0) := by
    unfold Cond.val toCond
    simp only [he, hf, Fin.sum_univ_one, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
    ring
  have hb : (toCond (stdRows (k + 2)) (geCon (k + 1))).b x = 0 := by
    simp [toCond, geCon]
  have hs : (toCond (stdRows (k + 2)) (geCon (k + 1))).strict = false := rfl
  unfold Cond.Holds
  rw [hval, hb, hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [sub_nonpos, Real.log_le_log_iff (by exact_mod_cast hv1 _) (by exact_mod_cast hv2 _), Nat.cast_le]

theorem merge_pos {k : ℕ} {v : (Fin (k + 1) → ℕ) × (Fin 1 → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) :
    (∀ a, 0 < (merge 0 v).1 a) ∧ ∀ i, 0 < (merge 0 v).2 i := by
  refine ⟨fun a => hv1 _, fun i => ?_⟩
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  simp only [merge, Function.update_self]
  exact Nat.mul_pos (hv1 _) (hv2 _)

/-- The child's conditions at a pair: the node's at the merged pair, the level and the order. -/
theorem buchConds_facts {k : ℕ} {conds : List (Cond (k + 1) 1)} {x : ℝ} (hx : 0 < x)
    {v : (Fin (k + 2) → ℕ) × (Fin 1 → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i)
    (hc : ∀ C ∈ buchConds k conds, C.Holds x v.1 v.2) :
    (∀ C ∈ conds, C.Holds x (merge 0 v).1 (merge 0 v).2) ∧ x ^ (1 / 25 : ℝ) ≤ v.1 (Fin.last (k + 1)) ∧
      v.1 (Fin.last (k + 1)) < v.1 (Fin.last k).castSucc := by
  have e1 : v.1 = Fin.snoc (Fin.init v.1) (v.1 (Fin.last (k + 1))) := (Fin.snoc_init_self v.1).symm
  refine ⟨fun C hC => holds_merge C 0 x hv1 hv2 (hc _ (List.mem_append_left _ (List.mem_map_of_mem hC))), ?_, ?_⟩
  · have h := hc (lvlCond (1 / 25) (fun _ => 0)) (List.mem_append_right _ (by simp))
    rw [e1, holds_lvlCond (p := Fin.init v.1) _ _ hx (fun j => hv1 _) (hv1 _), lvlOf_zero, Nat.ceil_le] at h
    exact h
  · have h := hc (ltCond (Fin.last k)) (List.mem_append_right _ (by simp))
    rw [e1, holds_ltCond (p := Fin.init v.1) _ _ (fun j => hv1 _) (hv1 _)] at h
    exact h

/-- **The child's terms satisfy the added condition**, so the child's count is the Buchstab child's. -/
theorem count_buch_std {k : ℕ} {conds : List (Cond (k + 1) 1)} (hinv : StdInv k conds) {x : ℝ}
    (hx : 1 < x) (y : ℝ) :
    ((std k conds).buch 0 (1 / 25) (fun _ => 0)).count x y = (std (k + 1) (stdChild k conds)).count x y := by
  rw [buch_std]
  symm
  refine count_cons_of_implied (std (k + 1) (buchConds k conds)) _ x y fun v hv hr hI => ?_
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hv
  have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
  have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ i).1
  rw [holds_geCon x hv1 hv2]
  obtain ⟨hcm, -, hlt⟩ := buchConds_facts (by linarith) hv1 hv2 hI.1
  obtain ⟨hw1, hw2⟩ := merge_pos hv1 hv2
  obtain ⟨-, hge⟩ := hinv x hx (merge 0 v) hw1 hw2 hcm
  simp only [merge, Function.update_self, Fin.init] at hge
  -- the rough item is not `1`, so its least prime factor is at least the new prime
  have hρ2 : 2 ≤ v.2 0 := by
    by_contra h
    have h1 : v.2 0 = 1 := by have := (hρ 0).1; omega
    rw [h1, mul_one] at hge
    omega
  exact ((SieveStops2.rough_iff_le_minFac hρ2).1 (hr 0)).trans (Nat.minFac_le (by omega))

/-- **The child keeps the invariant.** -/
theorem StdInv.child {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : StdInv k conds) :
    StdInv (k + 1) (stdChild k conds) := by
  intro x hx v hv1 hv2 hcv
  have hge := (holds_geCon x hv1 hv2).1 (hcv _ List.mem_cons_self)
  obtain ⟨hcm, hlvl, -⟩ :=
    buchConds_facts (by linarith) hv1 hv2 fun C hC => hcv C (List.mem_cons_of_mem _ hC)
  obtain ⟨hw1, hw2⟩ := merge_pos hv1 hv2
  obtain ⟨h1, -⟩ := h x hx (merge 0 v) hw1 hw2 hcm
  refine ⟨fun a => ?_, hge⟩
  induction a using Fin.lastCases with
  | last => exact hlvl
  | cast j => exact h1 j

/-- **The child's conditions are not functions of the product alone.** -/
theorem CondsOK.child {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : CondsOK conds) : CondsOK (stdChild k conds) := by
  intro C hC
  rcases List.mem_cons.1 hC with rfl | hC
  · refine ⟨Sum.inl (Fin.last (k + 1)), Sum.inr 0, ?_⟩
    simp only [toCond, Sum.elim_inl, Sum.elim_inr, wt_std_inl, wt_std_inr, geCon, Fin.val_last]
    simp
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨u, w, huw⟩ := h C' hC'
    refine ⟨u.map Fin.castSucc id, w.map Fin.castSucc id, ?_⟩
    rcases u with a | i <;> rcases w with b | j <;> simpa [Cond.split] using huw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact ⟨Sum.inl (Fin.last (k + 1)), Sum.inr 0, by simp [lvlCond]⟩
    · exact ⟨Sum.inl (Fin.last (k + 1)), Sum.inr 0, by simp [ltCond, (Fin.castSucc_ne_last (Fin.last k)).symm]⟩


/-! ### The child's coordinates -/

theorem coords_std {K : ℕ} (x : ℝ) (v : (Fin K → ℕ) × (Fin 1 → ℕ)) (a : Fin K) :
    coords (stdRows K) x v a = DEN * (Real.log (v.1 a) / Real.log x) := by
  rw [coords_eq, cX_std]
  rfl

theorem holds_ordCon (k : ℕ) (X : ℕ → ℝ) (H : ℝ) : (ordCon k).Holds X H ↔ X (k + 1) < X k := by
  unfold ordCon Con.Holds LF.val
  simp only [↓reduceIte, dotR_append, dotR_replicate_zero, List.length_replicate, dotR, zero_add,
    Nat.add_comm 1 k]
  push_cast
  constructor <;> intro h <;> linarith

/-- **The child's coordinates**: the node's, the new prime's in `[DEN/25, hi_k)` with the order of the last two
primes, and the added condition. -/
theorem Sound.std_child {k : ℕ} {conds : List (Cond (k + 1) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std k conds) (stdRows (k + 1)) E Γ B) (hlen : B.length = k + 1)
    (hf : fits Γ B.length = true) :
    Sound (std (k + 1) (stdChild k conds)) (stdRows (k + 2)) E (geCon (k + 1) :: (Γ ++ [ordCon k]))
      (B ++ [(NU0, (B.getD k (0, 0)).2)]) := by
  have h1 := h.buch hf 0 (1 / 25) (fun _ => 0) NU0 (B.getD k (0, 0)).2 [ordCon k] ?_
  · rw [hlen, buchRows_std] at h1
    have h2 : Sound (std (k + 1) (buchConds k conds)) (stdRows (k + 2)) E (Γ ++ [ordCon k])
        (B ++ [(NU0, (B.getD k (0, 0)).2)]) := h1
    exact h2.split (geCon (k + 1))
  intro x hx v hv1 hv2 hc hH
  rw [hlen, buchRows_std]
  obtain ⟨hcm, hlvl, hlt⟩ := buchConds_facts (by linarith) hv1 hv2 hc
  obtain ⟨hw1, hw2⟩ := merge_pos hv1 hv2
  have hHm : |slack x (merge 0 v)| ≤ E := by rwa [← slack_buch 0 x hv1 hv2]
  obtain ⟨hB, -⟩ := h x hx (merge 0 v) hw1 hw2 hcm hHm
  have hk := (inBox_getD B _ k hB (by omega)).2
  have hD := DEN_pos
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have eN := coords_std x v (Fin.last (k + 1))
  have eK := coords_std x v (Fin.last k).castSucc
  have eM := coords_std x (merge 0 v) (Fin.last k)
  simp only [Fin.val_last, Fin.val_castSucc] at eN eK eM
  have eMK : (merge 0 v).1 (Fin.last k) = v.1 (Fin.last k).castSucc := rfl
  rw [eMK] at eM
  -- the order of the last two primes
  have hlog : Real.log (v.1 (Fin.last (k + 1))) < Real.log (v.1 (Fin.last k).castSucc) :=
    Real.log_lt_log (by exact_mod_cast hv1 _) (by exact_mod_cast hlt)
  have hord : coords (stdRows (k + 2)) x v (k + 1) < coords (stdRows (k + 2)) x v k := by
    rw [eN, eK]
    exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hlog hlx) hD
  refine ⟨?_, ?_, fun c hc' => ?_⟩
  · -- the level
    rw [eN, NU0_eq]
    have h2 : Real.log x / 25 ≤ Real.log (v.1 (Fin.last (k + 1))) := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlvl
      rw [Real.log_rpow hx0] at this
      linarith
    calc (DEN : ℝ) / 25 = DEN * ((Real.log x / 25) / Real.log x) := by field_simp
      _ ≤ DEN * (Real.log (v.1 (Fin.last (k + 1))) / Real.log x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hlx.le) hD.le
  · calc coords (stdRows (k + 2)) x v (k + 1) < coords (stdRows (k + 2)) x v k := hord
      _ = coords (stdRows (k + 1)) x (merge 0 v) k := by rw [eK, eM]
      _ < _ := hk
  · simp only [List.mem_singleton] at hc'
    subst hc'
    exact (holds_ordCon k _ _).2 hord


/-! ### Li's Type I regions on a box -/

/-- The largest value of a form on the box, within the active constraints. -/
def LF.maxD (L : LF) (B : Box) (E : ℤ) (acts : List LF) : ℤ := -((L.smul (-1)).minD B E acts)

theorem LF.le_maxD (L : LF) {B : Box} {E : ℤ} (acts : List LF) {X : ℕ → ℝ} (hX : InBoxC B X) {H : ℝ}
    (hH : |H| ≤ E) (hacts : ∀ g ∈ acts, g.val X H ≤ 0) (hfit : L.c.length ≤ B.length)
    (hfit' : ∀ g ∈ acts, g.c.length ≤ B.length) : L.val X H ≤ L.maxD B E acts := by
  have h := (L.smul (-1)).minD_le acts hX hH hacts (length_smul_le _ hfit) hfit'
  rw [LF.val_smul] at h
  unfold LF.maxD
  push_cast at h ⊢
  linarith

/-- Li's Type I regions at `θ = 13/25` for the groups `0, 1, 2` of a standard node's items, the item `c0` (the Type I
term's cofactor) in group `3`: `kind = 1` is his `D′₀` (Lemma 3.1, no group `2`), `kind = 2` and `kind = 3` his `D′₁`
and `D′₂` (Lemma 3.2), with the groups' total exponent below `1`. -/
def typeICheck (k c0 : ℕ) (E : ℤ) (B : Box) (acts : List LF) (labels : List ℕ) (kind : ℕ) : Bool :=
  let g0 := grpLF (stdItems (k + 1)) labels 0
  let g1 := grpLF (stdItems (k + 1)) labels 1
  let g2 := grpLF (stdItems (k + 1)) labels 2
  let mx := fun L : LF => L.maxD B E acts
  decide (labels.length = k + 2) && decide (labels.getD c0 0 = 3) &&
    ((List.range (k + 2)).all fun a => decide (a = c0 ∨ labels.getD a 0 < if kind = 1 then 2 else 3)) &&
    decide (2 * mx g0 ≤ DEN) && decide (mx ((g0.add g1).add g2) < DEN) &&
    match kind with
    | 1 => decide (25 * mx g1 < 7 * DEN)
    | 2 => decide (50 * mx g2 < 7 * DEN) && decide (25 * mx ((g1.smul 2).add g2) < 13 * DEN) &&
        decide (25 * mx ((g1.smul 2).add (g2.smul 3)) < 19 * DEN)
    | 3 => decide (25 * mx g1 < 6 * DEN) && decide (100 * mx g2 < 7 * DEN)
    | _ => false

/-- The labels of a passing check: `k + 2` of them, the cofactor's `3`, the others below `3`, and below `2` for
`kind = 1`. -/
theorem labels_of_check {k c0 : ℕ} {E : ℤ} {B : Box} {acts : List LF} {labels : List ℕ} {kind : ℕ}
    (hcheck : typeICheck k c0 E B acts labels kind = true) :
    labels.length = k + 2 ∧ labels.getD c0 0 = 3 ∧
      ∀ a < k + 2, a ≠ c0 → labels.getD a 0 < if kind = 1 then 2 else 3 := by
  unfold typeICheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcheck
  obtain ⟨⟨⟨⟨⟨hl, h3⟩, hall⟩, -⟩, -⟩, -⟩ := hcheck
  exact ⟨hl, h3, fun a ha hac => (hall a ha).resolve_left hac⟩

/-- A strict integer check leaves the margin `1/(a DEN)`. -/
theorem le_of_check {M : ℤ} {a b : ℕ} (ha : 0 < a) (h : (a : ℤ) * M < b * DEN) {t : ℝ} (ht : DEN * t ≤ M) :
    t ≤ b / a - 1 / (a * DEN) := by
  have hD := DEN_pos
  have h1 : (a : ℤ) * M ≤ b * DEN - 1 := by omega
  -- `exact_mod_cast` unfolds `DEN`; cast explicitly
  have h2 := Int.cast_le (R := ℝ) |>.2 h1
  push_cast at h2
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : a * (DEN * t) ≤ b * DEN - 1 := le_trans (mul_le_mul_of_nonneg_left ht ha'.le) h2
  have e : (b : ℝ) / a - 1 / (a * DEN) = (b * DEN - 1) / (a * DEN) := by field_simp
  rw [e, le_div_iff₀ (mul_pos ha' hD)]
  have e2 : t * (a * DEN) = a * (DEN * t) := by ring
  linarith


/-- The items' forms of a standard node have at most `K` coordinates. -/
theorem stdItems_length_le (K : ℕ) : ∀ L ∈ stdItems K, L.c.length ≤ K := by
  intro L hL
  simp only [stdItems, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hL
  rcases hL with ⟨j, hj, rfl⟩ | rfl
  · simp [unitLF]; omega
  · simp

/-- The roles of a standard node's primes in its Type I term. -/
def stdRole {k : ℕ} (labels : List ℕ) (hlt3 : ∀ a : Fin (k + 1), labels.getD a 0 < 3) :
    Fin (k + 1) ⊕ Fin 0 → Fin 3 :=
  Sum.elim (fun a => ⟨labels.getD a 0, hlt3 a⟩) fun i => i.elim0

/-- The Type I term's group exponents are the node's, the rough item in group `3`. -/
theorem tExp_std {k : ℕ} (conds : List (Cond (k + 1) 1)) {labels : List ℕ}
    (hlt4 : ∀ t : Fin (k + 1) ⊕ Fin 1, labels.getD (canon t) 0 < 4) (h3 : labels.getD (k + 1) 0 = 3)
    (hlt3 : ∀ a : Fin (k + 1), labels.getD a 0 < 3) (x : ℝ) (w : (Fin (k + 1) → ℕ) × (Fin 1 → ℕ)) (i : Fin 3) :
    tExp (stdT k conds) (stdRole labels hlt3) x w i = grpExp (grpOf labels 4 hlt4) ⟨i, by omega⟩ (expo x w) := by
  unfold tExp grpExp
  rw [sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [univ_eq_empty, sum_empty, add_zero, Fin.sum_univ_one]
  have hr : (grpOf labels 4 hlt4 (Sum.inr 0) = ⟨i, by omega⟩) ↔ False := by
    simp only [grpOf, canon, Sum.elim_inr, Fin.val_zero, add_zero, h3, Fin.mk.injEq, iff_false]
    omega
  rw [ite_eq_right (hr.1 ·), add_zero]
  refine sum_congr rfl fun a _ => ?_
  simp only [stdRole, grpOf, canon, Sum.elim_inl, Fin.ext_iff, expo]


/-- **The regions from the check**, at a point of the box: group values `t_i` whose multiples `DEN t_i` are the
groups' forms lie in Li's regions, with the margin `1/(100 DEN)`. -/
theorem typeIReg_core {k c0 : ℕ} {E : ℤ} {B : Box} (hlen : k + 1 ≤ B.length) {acts : List LF}
    (hfa : ∀ g ∈ acts, g.c.length ≤ B.length) {labels : List ℕ} {kind : ℕ}
    (hcheck : typeICheck k c0 E B acts labels kind = true) {X : ℕ → ℝ} {H : ℝ} (hB : InBoxC B X) (hH : |H| ≤ E)
    (hacts : ∀ g ∈ acts, g.val X H ≤ 0) {t : Fin 3 → ℝ}
    (ht : ∀ i : Fin 3, (grpLF (stdItems (k + 1)) labels i).val X H = DEN * t i) :
    TypeIReg (13 / 25) (1 / (100 * DEN)) (decide (kind ≠ 1)) t ∧ t 0 + t 1 + t 2 ≤ 1 - 1 / (100 * DEN) := by
  unfold typeICheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcheck
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hm0⟩, hsum⟩, hk⟩ := hcheck
  have hfit : ∀ L ∈ stdItems (k + 1), L.c.length ≤ B.length := fun L hL =>
    (stdItems_length_le _ L hL).trans hlen
  have mxle : ∀ L : LF, L.c.length ≤ B.length → L.val X H ≤ L.maxD B E acts := fun L hL =>
    L.le_maxD acts hB hH hacts hL hfa
  set g0 := grpLF (stdItems (k + 1)) labels 0 with hg0
  set g1 := grpLF (stdItems (k + 1)) labels 1 with hg1
  set g2 := grpLF (stdItems (k + 1)) labels 2 with hg2
  have hf0 : g0.c.length ≤ B.length := length_grpLF hfit labels 0
  have hf1 : g1.c.length ≤ B.length := length_grpLF hfit labels 1
  have hf2 : g2.c.length ≤ B.length := length_grpLF hfit labels 2
  have v0 : g0.val X H = DEN * t 0 := ht 0
  have v1 : g1.val X H = DEN * t 1 := ht 1
  have v2 : g2.val X H = DEN * t 2 := ht 2
  have hD := DEN_pos
  have hη : (1 : ℝ) / (100 * DEN) ≤ 1 / DEN := one_div_le_one_div_of_le hD (by linarith)
  -- the largest group exponent and the total
  have e0 : DEN * t 0 ≤ g0.maxD B E acts := v0 ▸ mxle g0 hf0
  have b0 : t 0 ≤ 1 / 2 := by
    have := Int.cast_le (R := ℝ) |>.2 hm0
    push_cast at this
    exact le_of_mul_le_mul_left (by linarith : (DEN : ℝ) * t 0 ≤ DEN * (1 / 2)) hD
  have eS : DEN * (t 0 + t 1 + t 2) ≤ ((g0.add g1).add g2).maxD B E acts := by
    have := mxle _ (length_add_le (length_add_le hf0 hf1) hf2)
    rw [LF.val_add, LF.val_add, v0, v1, v2] at this
    linarith
  have bS := le_of_check (a := 1) (b := 1) one_pos (by simpa using hsum) eS
  push_cast at bS
  rw [div_one, one_mul] at bS
  refine ⟨⟨b0, ?_⟩, by linarith⟩
  rcases kind with _ | _ | _ | _ | n
  · simp at hk
  · -- `D′₀`
    simp only [decide_eq_true_eq] at hk
    have e1 : DEN * t 1 ≤ g1.maxD B E acts := v1 ▸ mxle g1 hf1
    have b1 := le_of_check (a := 25) (b := 7) (by norm_num) (by simpa using hk) e1
    have hmin : min ((3 * (13 / 25 : ℝ) - 1) / 2) ((1 + 13 / 25) / 5) = 7 / 25 := by norm_num
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hmin]
    push_cast at b1
    have : (1 : ℝ) / (100 * DEN) ≤ 1 / (25 * DEN) := one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  · -- `D′₁`
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨k1, k2⟩, k3⟩ := hk
    have e2 : DEN * t 2 ≤ g2.maxD B E acts := v2 ▸ mxle g2 hf2
    have e12 : DEN * (2 * t 1 + t 2) ≤ ((g1.smul 2).add g2).maxD B E acts := by
      have := mxle ((g1.smul 2).add g2) (length_add_le (length_smul_le 2 hf1) hf2)
      rw [LF.val_add, LF.val_smul, v1, v2] at this
      push_cast at this
      linarith
    have e13 : DEN * (2 * t 1 + 3 * t 2) ≤ ((g1.smul 2).add (g2.smul 3)).maxD B E acts := by
      have := mxle ((g1.smul 2).add (g2.smul 3))
        (length_add_le (length_smul_le 2 hf1) (length_smul_le 3 hf2))
      rw [LF.val_add, LF.val_smul, LF.val_smul, v1, v2] at this
      push_cast at this
      linarith
    have b2 := le_of_check (a := 50) (b := 7) (by norm_num) (by simpa using k1) e2
    have b12 := le_of_check (a := 25) (b := 13) (by norm_num) (by simpa using k2) e12
    have b13 := le_of_check (a := 25) (b := 19) (by norm_num) (by simpa using k3) e13
    push_cast at b2 b12 b13
    simp only [ne_eq]
    have i1 : (1 : ℝ) / (100 * DEN) ≤ 1 / (50 * DEN) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have i2 : (1 : ℝ) / (100 * DEN) ≤ 1 / (25 * DEN) := one_div_le_one_div_of_le (by linarith) (by linarith)
    left
    refine ⟨by linarith, by linarith, by linarith⟩
  · -- `D′₂`
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨k1, k2⟩ := hk
    have e1 : DEN * t 1 ≤ g1.maxD B E acts := v1 ▸ mxle g1 hf1
    have e2 : DEN * t 2 ≤ g2.maxD B E acts := v2 ▸ mxle g2 hf2
    have b1 := le_of_check (a := 25) (b := 6) (by norm_num) (by simpa using k1) e1
    have b2 := le_of_check (a := 100) (b := 7) (by norm_num) (by simpa using k2) e2
    push_cast at b1 b2
    simp only [ne_eq]
    have : (0 : ℝ) ≤ 1 / (25 * DEN) := by positivity
    right
    refine ⟨by linarith, by linarith⟩
  · simp at hk

/-- **A box passing the Type I check lies in Li's regions**: at the Type I term's pairs near `x`, with the margin
`1/(100 DEN)`. -/
theorem typeIReg_of_check {k : ℕ} {conds : List (Cond (k + 1) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std k conds) (stdRows (k + 1)) E Γ B) (hE : 0 < E) (hlen : k + 1 ≤ B.length)
    {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    {labels : List ℕ} {kind : ℕ} (hcheck : typeICheck k (k + 1) E B acts labels kind = true) :
    ∃ (role : Fin (k + 1) ⊕ Fin 0 → Fin 3) (kd : Bool), (kd = false → ∀ t, role t ≠ 2) ∧
      ∀ᶠ x in atTop, ∀ w ∈ (stdT k conds).terms x, x / 2 < (prodP w : ℝ) → (prodP w : ℝ) ≤ x →
        TypeIReg (13 / 25) (1 / (100 * DEN)) kd (tExp (stdT k conds) role x w) ∧
          tExp (stdT k conds) role x w 0 + tExp (stdT k conds) role x w 1 + tExp (stdT k conds) role x w 2 ≤
            1 - 1 / (100 * DEN) := by
  obtain ⟨hl, h3, hall⟩ := labels_of_check hcheck
  have hlt3 : ∀ a : Fin (k + 1), labels.getD a 0 < 3 := fun a =>
    lt_of_lt_of_le (hall a (by omega) (by omega)) (by split_ifs <;> norm_num)
  have hlt4 : ∀ t : Fin (k + 1) ⊕ Fin 1, labels.getD (canon t) 0 < 4 := by
    rintro (a | i)
    · exact (hlt3 a).trans (by norm_num)
    · have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      simp only [canon, Sum.elim_inr, Fin.val_zero, add_zero]
      rw [h3]
      norm_num
  refine ⟨stdRole labels hlt3, decide (kind ≠ 1), fun hkd t => ?_, ?_⟩
  · have hk1 : kind = 1 := by simpa using hkd
    rcases t with a | i
    · have := hall a (by omega) (by omega)
      rw [ite_eq_left hk1] at this
      simp only [stdRole, Sum.elim_inl, ne_eq, Fin.ext_iff, Fin.val_two]
      omega
    · exact i.elim0
  filter_upwards [abs_slack_le hE (k + 1) 1, eventually_gt_atTop 1] with x hsl hx1 w hw h1 h2
  obtain ⟨hwp, -, hc⟩ := mem_filter.1 hw
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
  have hw1 : ∀ a, 0 < w.1 a := fun a => (hp a).2.pos
  have hw2 : ∀ i, 0 < w.2 i := fun i => (hρ i).1
  have hH := hsl w hw1 hw2 (by linarith) (by linarith)
  obtain ⟨hB, hΓ⟩ := h x hx1 w hw1 hw2 hc hH
  refine typeIReg_core hlen hfa hcheck (inBoxC_of_inBox hB) hH (fun g hg => ?_) fun i => ?_
  · obtain ⟨c, hc', rfl⟩ := hacts g hg
    exact Con.val_le (hΓ c hc')
  · rw [tExp_std conds hlt4 h3 hlt3]
    exact val_grpLF_eq (itemsOK_std (k + 1)) hl hlt4 ⟨i, by omega⟩ (expo x w)

/-! ### The decision -/

/-- **The decomposition of a standard node.** On a sound standard node whose box passes the Type I check, Buchstab's
identity at the level `x^{1/25}` leaves a Type I term, asymptotic by Li's Lemmas 3.1 and 3.2, and the child: the node
is `OK` for `σ` with the child's loss for `−σ`. -/
theorem Sound.OK_of_dec {k : ℕ} {conds : List (Cond (k + 1) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std k conds) (stdRows (k + 1)) E Γ B) (hE : 0 < E) (hinv : StdInv k conds)
    (hcond : CondsOK conds) (hlen : k + 1 ≤ B.length) {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g)
    (hfa : ∀ g ∈ acts, g.c.length ≤ B.length) {labels : List ℕ} {kind : ℕ}
    (hcheck : typeICheck k (k + 1) E B acts labels kind = true) {c ρ σ L : ℝ} (hc : 0 < c) (hc1 : c < 1 / 25)
    (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hσ : |σ| ≤ 1) (hLi31 : ShortSieveLi.LiLemma31 (13 / 25) (2 / 25) ρ)
    (hLi32 : ShortSieveLi.LiLemma32 (13 / 25) (2 / 25) ρ)
    (hG : OK (13 / 25) ρ (-σ) (fun x y => ((std (k + 1) (stdChild k conds)).count x y : ℝ)) L) :
    OK (13 / 25) ρ σ (fun x y => ((std k conds).count x y : ℝ)) L := by
  have hθρ : (13 / 25 : ℝ) ≤ 1 - ρ := by linarith
  -- the level is at most the last prime
  have hlvl : ∀ x : ℝ, 1 < x → ∀ v ∈ pairs (k + 1) 1 ⌊x⌋₊, (∀ C ∈ conds, C.Holds x v.1 v.2) →
      lvlOf (1 / 25) (fun _ => 0) x v.1 ≤ v.1 (Fin.last k) := by
    intro x hx v hv hcv
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hv
    obtain ⟨h2, -⟩ := hinv x hx v (fun a => (hp a).2.pos) (fun i => (hρ' i).1) hcv
    rw [lvlOf_zero, Nat.ceil_le]
    exact h2 (Fin.last k)
  -- the child
  have hG' : OK (13 / 25) ρ (-σ) (fun x y => (((std k conds).buch 0 (1 / 25) (fun _ => 0)).count x y : ℝ)) L := by
    refine OK_congr ?_ hθρ hG
    filter_upwards [eventually_gt_atTop 1] with x hx y _ _
    rw [count_buch_std hinv hx y]
  -- the Type I term
  have hJ : Asym (13 / 25) ρ (fun x y => (((std k conds).toJ 0 (1 / 25) (fun _ => 0)).count x y : ℝ)) := by
    obtain ⟨role, kd, hrole, hreg⟩ := typeIReg_of_check h hE hlen hacts hfa hcheck
    have hbigT : ∀ᶠ x in atTop, ∀ w ∈ (stdT k conds).terms x, (∀ a, x ^ c < w.1 a) ∧
        ∀ i : Fin (stdT k conds).m, 1 < w.2 i.castSucc := by
      filter_upwards [eventually_gt_atTop 1] with x hx w hw
      obtain ⟨hwp, -, hcw⟩ := mem_filter.1 hw
      obtain ⟨hp, hρ'⟩ := mem_pairs.1 hwp
      exact ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le
        ((hinv x hx w (fun a => (hp a).2.pos) (fun i => (hρ' i).1) hcw).1 a), fun i => i.elim0⟩
    have hrel := abs_count_sub_le_typeI (stdT k conds) (Nat.succ_pos k) hc (by linarith) hρ hρc
      (show (0 : ℝ) < 1 / 25 by norm_num) (show 12 * ρ < (1 / 25 : ℝ) by linarith)
      (show (1 / 25 : ℝ) ≤ 2 * (13 / 25) - 1 by norm_num) (by norm_num) (by norm_num)
      (div_pos one_pos (mul_pos (by norm_num) DEN_pos)) hLi31 hLi32 hcond hbigT role kd hrole hreg
    rw [stdT_toJ] at hrel
    refine asym_of_rel hrel ?_
    -- the comparison interval: the node's count plus the child's
    obtain ⟨CN, hCN0, hCN⟩ := ShortSieveLi.count_B_le (std k conds) hc (by linarith) hρ hρc (hinv.big hc1)
    obtain ⟨CG, hCG0, hCG⟩ := ShortSieveLi.count_B_le (std (k + 1) (stdChild k conds)) hc (by linarith) hρ hρc
      (hinv.child.big hc1)
    refine ⟨CN + CG, by positivity, ?_⟩
    filter_upwards [hCN, hCG, eventually_gt_atTop 1] with x h1 h2 hx
    rw [count_buchstab _ 0 _ _ (by linarith) _ (hlvl x hx), count_buch_std hinv hx]
    push_cast
    have e : (CN + CG) * x ^ (1 - ρ) / Real.log x =
        CN * x ^ (1 - ρ) / Real.log x + CG * x ^ (1 - ρ) / Real.log x := by ring
    rw [e]
    exact add_le_add h1 h2
  exact OK_of_buch _ 0 _ _ ((eventually_gt_atTop 1).mono fun x hx => hlvl x hx) hθρ hσ hJ hG'

end ShortSieveCert

#print axioms ShortSieveCert.Sound.OK_of_dec
#print axioms ShortSieveCert.Sound.std_child
#print axioms ShortSieveCert.StdInv.child
#print axioms ShortSieveCert.CondsOK.child
#print axioms ShortSieveCert.OK_of_split
#print axioms ShortSieveCert.CondsOK.split
