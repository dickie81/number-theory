import ShortSieveCertTII
import ShortSieveLi

/-!
# The certificate's Type II decision on a node

A box of a node is asymptotic when the integer check of `ShortSieveCertTII` passes on it: the node's terms with
product in `(x/4, 2x]` have exponents in the compact set `K` of points whose coordinates lie in the closed box and
satisfy the constraints with `|H| ≤ E` (`mem_K`), and at every point of `K` the check gives Harman's test, so
`ShortSieveNode.abs_count_sub_le_of_test` applies.

The certificate lists the items in canonical order, the primes first (`canon`), with their forms in the coordinates
(`ItemsOK`: the form of item `t` is `DEN α_t` at the coordinates and slack of any `α`), and labels them by group.

* `Sound.asym_of_tii`: the node's count is asymptotic, hence `OK` with no loss.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveTree ShortSieveWit

open Classical

/-! ### Coordinates of exponent vectors -/

/-- The coordinates of an exponent vector `α`: `X_j = DEN Σ_t A_{jt} α_t`. -/
noncomputable def cX {k m : ℕ} (A : Rows k m) (α : Fin k ⊕ Fin m → ℝ) : ℕ → ℝ :=
  fun j => DEN * ∑ t, (A j t : ℝ) * α t

/-- The slack of an exponent vector: `DEN(1 − Σ_t α_t)`. -/
noncomputable def cH {k m : ℕ} (α : Fin k ⊕ Fin m → ℝ) : ℝ := DEN * (1 - ∑ t, α t)

theorem coords_eq {k m : ℕ} (A : Rows k m) (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    coords A x v = cX A (expo x v) := rfl

theorem slack_eq {k m : ℕ} (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) : slack x v = cH (expo x v) := rfl

/-- A form at the coordinates and slack of `α`: `c₀ + c_η DEN + DEN Σ_t w_t α_t`. -/
theorem LF.val_cX {k m : ℕ} (A : Rows k m) (L : LF) (α : Fin k ⊕ Fin m → ℝ) :
    L.val (cX A α) (cH α) = (L.c0 + L.ce * DEN) + DEN * ∑ t, wt A L t * α t := by
  unfold LF.val cX cH wt
  rw [dotR_eq_sum]
  have h1 : ∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * (DEN * ∑ t, (A j t : ℝ) * α t) =
      DEN * ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * α t := by
    calc ∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * (DEN * ∑ t, (A j t : ℝ) * α t)
        = ∑ j ∈ range L.c.length, ∑ t, (DEN : ℝ) * ((L.c.getD j 0 : ℝ) * A j t * α t) := by
          refine sum_congr rfl fun j _ => ?_
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun t _ => by ring
      _ = ∑ t, ∑ j ∈ range L.c.length, (DEN : ℝ) * ((L.c.getD j 0 : ℝ) * A j t * α t) := sum_comm
      _ = DEN * ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * α t := by
          rw [mul_sum]
          refine sum_congr rfl fun t _ => ?_
          rw [sum_mul, mul_sum]
  have h2 : ∑ t, ((∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) - L.ce) * α t =
      ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * α t - L.ce * ∑ t, α t := by
    simp_rw [sub_mul]
    rw [sum_sub_distrib, mul_sum]
  rw [h1, h2]
  ring

theorem continuous_dotR {k m : ℕ} : ∀ (c : List ℤ) (R : ℕ → Fin k ⊕ Fin m → ℤ),
    Continuous fun α : Fin k ⊕ Fin m → ℝ => dotR c (cX R α)
  | [], _ => by simp only [dotR]; exact continuous_const
  | a :: l, R => by
    simp only [dotR]
    have h1 : Continuous fun α : Fin k ⊕ Fin m → ℝ => (a : ℝ) * cX R α 0 := by
      unfold cX
      exact continuous_const.mul (continuous_const.mul
        (continuous_finsetSum _ fun t _ => continuous_const.mul (continuous_apply t)))
    have h2 := continuous_dotR l (fun j => R (j + 1))
    exact h1.add h2

theorem continuous_val {k m : ℕ} (A : Rows k m) (L : LF) :
    Continuous fun α : Fin k ⊕ Fin m → ℝ => L.val (cX A α) (cH α) := by
  unfold LF.val cH
  exact (continuous_const.add (continuous_dotR L.c A)).add (continuous_const.mul
    (continuous_const.mul (continuous_const.sub (continuous_finsetSum _ fun t _ => continuous_apply t))))

theorem isClosed_inBoxC {k m : ℕ} : ∀ (B : Box) (R : ℕ → Fin k ⊕ Fin m → ℤ),
    IsClosed {α : Fin k ⊕ Fin m → ℝ | InBoxC B (cX R α)}
  | [], _ => by simp only [InBoxC, Set.ofPred_true]; exact isClosed_univ
  | b :: B, R => by
    have hc : Continuous fun α : Fin k ⊕ Fin m → ℝ => cX R α 0 := by
      unfold cX
      exact continuous_const.mul (continuous_finsetSum _ fun t _ => continuous_const.mul (continuous_apply t))
    have h3 := isClosed_inBoxC B (fun j => R (j + 1))
    have e : {α : Fin k ⊕ Fin m → ℝ | InBoxC (b :: B) (cX R α)} =
        {α | (b.1 : ℝ) ≤ cX R α 0} ∩ {α | cX R α 0 ≤ b.2} ∩ {α | InBoxC B (cX (fun j => R (j + 1)) α)} := by
      ext α
      simp only [InBoxC, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
      rfl
    rw [e]
    exact ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)).inter h3

/-! ### The compact set of exponent vectors -/

/-- The exponent vectors in `[0, 2]` whose coordinates lie in the closed box and satisfy the constraints (as `≤ 0`),
with slack at most `E`. -/
def KSet {k m : ℕ} (A : Rows k m) (E : ℤ) (Γ : List Con) (B : Box) : Set (Fin k ⊕ Fin m → ℝ) :=
  {α | (∀ t, 0 ≤ α t ∧ α t ≤ 2) ∧ InBoxC B (cX A α) ∧ |cH α| ≤ E ∧ ∀ c ∈ Γ, c.L.val (cX A α) (cH α) ≤ 0}

theorem isCompact_KSet {k m : ℕ} (A : Rows k m) (E : ℤ) (Γ : List Con) (B : Box) : IsCompact (KSet A E Γ B) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : Fin k ⊕ Fin m => Set.Icc (0 : ℝ) 2) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hcube.of_isClosed_subset ?_ fun α hα => ?_
  · have hH : Continuous fun α : Fin k ⊕ Fin m → ℝ => cH α := by
      unfold cH
      exact continuous_const.mul (continuous_const.sub (continuous_finsetSum _ fun t _ => continuous_apply t))
    have e : KSet A E Γ B = (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 2) ∩
        {α | InBoxC B (cX A α)} ∩ {α | |cH α| ≤ E} ∩ ⋂ c ∈ Γ, {α | c.L.val (cX A α) (cH α) ≤ 0} := by
      ext α
      simp only [KSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
        Set.mem_iInter]
      tauto
    rw [e]
    refine (((isClosed_set_pi fun _ _ => isClosed_Icc).inter (isClosed_inBoxC B A)).inter
      (isClosed_le (continuous_abs.comp hH) continuous_const)).inter ?_
    exact isClosed_biInter fun c _ => isClosed_le (continuous_val A c.L) continuous_const
  · exact fun t _ => hα.1 t

/-- **The terms' exponents lie in `K`**: for large `x`, at the terms with product in `(x/4, 2x]`. -/
theorem Sound.mem_K {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hE : 0 < E) : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x →
      expo x v ∈ KSet A E Γ B := by
  filter_upwards [abs_slack_le hE N.k N.m, eventually_ge_atTop 2] with x hsl hx2 v hv h1 h2
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  obtain ⟨hvp, hr, hc⟩ := mem_filter.1 hv
  obtain ⟨hp, hρ⟩ := ShortSieveBuch.mem_pairs.1 hvp
  have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
  have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ i).1
  have hH := hsl v hv1 hv2 h1 h2
  obtain ⟨hB, hΓ⟩ := h x hx1 v hv1 hv2 hc hH
  -- the exponents lie in `[0, 2]`: `1 ≤ item ≤ n ≤ 2x ≤ x²`
  have hle : ∀ t, 1 ≤ Sum.elim (fun a => (v.1 a : ℝ)) (fun i => (v.2 i : ℝ)) t ∧
      Sum.elim (fun a => (v.1 a : ℝ)) (fun i => (v.2 i : ℝ)) t ≤ prodP v := fun t => by
    rcases t with a | i
    · simp only [Sum.elim_inl]
      refine ⟨Nat.one_le_cast.2 (hv1 a), ?_⟩
      have : v.1 a ≤ prodP v := by
        unfold prodP
        exact le_trans (single_le_prod (f := v.1) (fun j _ => hv1 j) (mem_univ a))
          (Nat.le_mul_of_pos_right _ (prod_pos fun i _ => hv2 i))
      exact_mod_cast this
    · simp only [Sum.elim_inr]
      refine ⟨Nat.one_le_cast.2 (hv2 i), ?_⟩
      have : v.2 i ≤ prodP v := by
        unfold prodP
        exact le_trans (single_le_prod (f := v.2) (fun j _ => hv2 j) (mem_univ i))
          (Nat.le_mul_of_pos_left _ (prod_pos fun a _ => hv1 a))
      exact_mod_cast this
  refine ⟨fun t => ?_, inBoxC_of_inBox hB, hH, fun c hc' => Con.val_le (hΓ c hc')⟩
  obtain ⟨h1t, h2t⟩ := hle t
  have hexp : expo x v t = Real.log (Sum.elim (fun a => (v.1 a : ℝ)) (fun i => (v.2 i : ℝ)) t) / Real.log x := by
    rcases t with a | i <;> rfl
  rw [hexp]
  refine ⟨div_nonneg (Real.log_nonneg h1t) hlx.le, ?_⟩
  rw [div_le_iff₀ hlx]
  calc Real.log (Sum.elim (fun a => (v.1 a : ℝ)) (fun i => (v.2 i : ℝ)) t) ≤ Real.log (x * x) :=
        Real.log_le_log (by linarith) (by nlinarith)
    _ = 2 * Real.log x := by rw [Real.log_mul hx0.ne' hx0.ne']; ring

/-! ### Groups of items in canonical order -/

/-- The canonical position of an item: the primes first, then the rough items. -/
def canon {k m : ℕ} : Fin k ⊕ Fin m → ℕ := Sum.elim (fun a => a.val) fun i => k + i.val

theorem canon_lt {k m : ℕ} (t : Fin k ⊕ Fin m) : canon t < k + m := by
  rcases t with a | i
  · simp only [canon, Sum.elim_inl]; omega
  · simp only [canon, Sum.elim_inr]; omega

/-- A sum over the positions `0, …, k + m − 1` is a sum over the items. -/
theorem sum_range_canon {k m : ℕ} (f : ℕ → ℝ) : ∑ p ∈ range (k + m), f p = ∑ t : Fin k ⊕ Fin m, f (canon t) := by
  rw [sum_range_add, Fintype.sum_sum_type, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun i => f (k + i))]
  rfl

/-- The value of a group's form: the items with its label. -/
theorem val_grpLF (g : ℕ) (X : ℕ → ℝ) (H : ℝ) : ∀ (items : List LF) (labels : List ℕ),
    items.length = labels.length → (grpLF items labels g).val X H =
      ∑ p ∈ range items.length, if labels.getD p 0 = g then (items.getD p LF.zero).val X H else 0
  | [], [], _ => by simp [grpLF, sumLF, LF.val_zero]
  | L :: items, l :: labels, h => by
    have ih := val_grpLF g X H items labels (by simpa using h)
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    unfold grpLF at ih ⊢
    rw [List.zip_cons_cons, List.filter_cons]
    by_cases hl : l = g
    · simp only [hl, decide_true, ↓reduceIte]
      show (L.add (sumLF Prod.fst (List.filter (fun p => decide (p.2 = g)) (items.zip labels)))).val X H = _
      rw [LF.val_add, ih]
      ring
    · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The items' forms in canonical order: the form of item `t` is `DEN α_t` at the coordinates and slack of any `α`. -/
def ItemsOK {k m : ℕ} (A : Rows k m) (items : List LF) : Prop :=
  items.length = k + m ∧ ∀ (t : Fin k ⊕ Fin m) (α : Fin k ⊕ Fin m → ℝ),
    (items.getD (canon t) LF.zero).val (cX A α) (cH α) = DEN * α t

/-- The groups of a labelling, as a map to `Fin ng`. -/
def grpOf {k m : ℕ} (labels : List ℕ) (ng : ℕ) (hlt : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < ng)
    (t : Fin k ⊕ Fin m) : Fin ng := ⟨labels.getD (canon t) 0, hlt t⟩

/-- **A group's form is `DEN` times its exponent.** -/
theorem val_grpLF_eq {k m : ℕ} {A : Rows k m} {items : List LF} (hI : ItemsOK A items) {labels : List ℕ}
    (hlab : labels.length = k + m) {ng : ℕ} (hlt : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < ng)
    (g : Fin ng) (α : Fin k ⊕ Fin m → ℝ) :
    (grpLF items labels g).val (cX A α) (cH α) = DEN * grpExp (grpOf labels ng hlt) g α := by
  rw [val_grpLF g _ _ items labels (by rw [hI.1, hlab]), hI.1, sum_range_canon, grpExp, mul_sum, sum_filter]
  refine sum_congr rfl fun t _ => ?_
  simp only [grpOf, Fin.ext_iff]
  split_ifs
  · exact hI.2 t α
  · rfl

/-! ### The decision -/

/-- An error `C y/log² x` is asymptotic. -/
theorem asym_of_log_sq {θ ρ : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |F x y - y / x ^ (1 - ρ) * F x (x ^ (1 - ρ))| ≤ C * y / Real.log x ^ 2) : Asym θ ρ F := by
  obtain ⟨C, hC⟩ := h
  intro ε hε
  filter_upwards [hC, eventually_gt_atTop 1, tendsto_log_atTop.eventually_ge_atTop (|C| / ε)]
    with x hx hx1 hlx y hy1 hy2
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg (by linarith) _) hy1
  refine (hx y hy1 hy2).trans ?_
  have h1 : |C| ≤ ε * Real.log x := by rwa [div_le_iff₀ hε, mul_comm] at hlx
  have e1 : C * y / Real.log x ^ 2 ≤ |C| * y / Real.log x ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hy0) (by positivity)
  have e2 : |C| * y / Real.log x ^ 2 ≤ ε * Real.log x * y / Real.log x ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hy0) (by positivity)
  have e3 : ε * Real.log x * y / Real.log x ^ 2 = ε * y / Real.log x := by field_simp
  linarith

/-- **The Type II decision.** On a sound node whose box passes the check, with the items' forms and labels in
canonical order and the active constraints among the node's constraints, the node's count is asymptotic: the terms'
exponents lie in `K` (`Sound.mem_K`), where the check gives Harman's test. -/
theorem Sound.asym_of_tii {N : Node} (hk : 0 < N.k) (hm : 0 < N.m) {A : Rows N.k N.m} {E : ℤ} (hE : 0 < E)
    {Γ : List Con} {B : Box} (h : Sound N A E Γ B) {items : List LF} (hI : ItemsOK A items)
    {labels : List ℕ} (hlab : labels.length = N.k + N.m) {ng : ℕ}
    (hlt : ∀ t : Fin N.k ⊕ Fin N.m, labels.getD (canon t) 0 < ng)
    {P K : ℤ} (hP : 0 < P) (hK : 0 < K) {θ κ : ℝ} (hPθ : (P : ℝ) = (1 - θ + κ) * DEN) (hKκ : (K : ℝ) = κ * DEN)
    (acts : List LF) (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g)
    (hcheck : tiiCheck P K E B acts items labels ng = true)
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    {c ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hθ : 0 < θ) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hθρ : θ + ρ ≤ 1)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i) :
    Asym θ ρ (fun x y => (N.count x y : ℝ)) := by
  have hD := DEN_pos
  have hκ : 0 < κ := by
    have h0 : (0 : ℝ) < K := by exact_mod_cast hK
    rw [hKκ] at h0
    exact pos_of_mul_pos_left h0 hD.le
  set grp := grpOf labels ng hlt with hgrp
  -- the check at every point of `K`
  have hpt : ∀ α ∈ KSet A E Γ B, (∀ g : Fin ng, κ < grpExp grp g α) ∧
      1 < ∑ g : Fin ng, 1 / dreq ((1 - θ + κ) / (grpExp grp g α - κ)) := by
    intro α hα
    obtain ⟨-, hB, hH, hΓ⟩ := hα
    have hacts' : ∀ g ∈ acts, g.val (cX A α) (cH α) ≤ 0 := fun g hg => by
      obtain ⟨c, hc, rfl⟩ := hacts g hg
      exact hΓ c hc
    obtain ⟨h1, h2⟩ := lt_sum_of_tiiCheck hP hcheck hfit hfa hB hH hacts'
    have e : ∀ g : Fin ng, (grpLF items labels g).val (cX A α) (cH α) = DEN * grpExp grp g α :=
      fun g => val_grpLF_eq hI hlab hlt g α
    have hlt' : ∀ g : Fin ng, κ < grpExp grp g α := fun g => by
      have h3 := h1 g g.2
      rw [e g, hKκ] at h3
      have h4 : κ * DEN < grpExp grp g α * DEN := by linarith
      exact lt_of_mul_lt_mul_right h4 hD.le
    refine ⟨hlt', ?_⟩
    rw [Finset.sum_range] at h2
    refine lt_of_lt_of_le h2 (le_of_eq (sum_congr rfl fun g _ => ?_))
    rw [e g, hPθ, hKκ, show (DEN : ℝ) * grpExp grp g α - κ * DEN = (grpExp grp g α - κ) * DEN by ring,
      mul_div_mul_right _ _ hD.ne']
  have htest : ∀ α ∈ KSet A E Γ B, ∃ δ : Fin ng → ℝ, (∀ g, 0 < δ g) ∧ ∑ g, 1 / δ g = 1 ∧
      ∀ g, ShortSieveTypeII.MomentOK ((1 - θ + κ) / (grpExp grp g α - κ)) (δ g) := by
    intro α hα
    obtain ⟨-, hS⟩ := hpt α hα
    set S := ∑ g : Fin ng, 1 / dreq ((1 - θ + κ) / (grpExp grp g α - κ)) with hSdef
    have hS0 : 0 < S := lt_trans one_pos hS
    have hdq : ∀ g : Fin ng, 0 < dreq ((1 - θ + κ) / (grpExp grp g α - κ)) := fun g =>
      lt_of_lt_of_le two_pos (two_le_dreq _)
    refine ⟨fun g => dreq ((1 - θ + κ) / (grpExp grp g α - κ)) * S, fun g => mul_pos (hdq g) hS0, ?_,
      fun g => momentOK_of_dreq_lt ?_⟩
    · have e : ∀ g : Fin ng, 1 / (dreq ((1 - θ + κ) / (grpExp grp g α - κ)) * S) =
          1 / dreq ((1 - θ + κ) / (grpExp grp g α - κ)) / S := fun g => (div_div _ _ _).symm
      rw [sum_congr rfl fun g _ => e g, ← sum_div, ← hSdef, div_self hS0.ne']
    · have := hdq g
      nlinarith
  have hpos : ∀ α ∈ KSet A E Γ B, ∀ g, κ < grpExp grp g α := fun α hα => (hpt α hα).1
  exact asym_of_log_sq (abs_count_sub_le_of_test N hk hm hc hc1 hθ hκ hρ hρc hθρ hcond hbig
    (isCompact_KSet A E Γ B) grp hpos htest (h.mem_K hE))

/-! ### The decision by Li's Lemma 4.1 -/

/-- **Li's Lemma 4.1 on a box** (the generator's `checkG2`, with the slack in the forms): the groups `M` (label `0`)
and `N` (label `1`) have `|a_M − a_N| < D₁` and `a_M + a_N > D₂` (in units of `1/DEN`) at every point of the box,
by the domain-aware extremes. -/
def g2Check (D1 D2 E : ℤ) (B : Box) (acts : List LF) (items : List LF) (labels : List ℕ) : Bool :=
  let LM := grpLF items labels 0
  let LN := grpLF items labels 1
  decide (-(LN.add (LM.smul (-1))).minD B E acts < D1) && decide (-(LM.add (LN.smul (-1))).minD B E acts < D1) &&
    decide (D2 < (LM.add LN).minD B E acts)

theorem length_add_le {L M : LF} {n : ℕ} (hL : L.c.length ≤ n) (hM : M.c.length ≤ n) : (L.add M).c.length ≤ n := by
  simp only [LF.add, length_addC]; omega

theorem length_smul_le {L : LF} {n : ℕ} (μ : ℤ) (hL : L.c.length ≤ n) : (L.smul μ).c.length ≤ n := by
  simpa [LF.smul] using hL

/-- **The decision by Li's Lemma 4.1.** On a sound node whose box passes `g2Check` with `D₁ = (2θ − 1) DEN` and
`D₂ = (1 − γ) DEN`, groups `0`, `1` and the rest `2` in canonical order, the node's count is asymptotic. -/
theorem Sound.asym_of_g2 {N : Node} (hk : 0 < N.k) (hm : 0 < N.m) {A : Rows N.k N.m} {E : ℤ} (hE : 0 < E)
    {Γ : List Con} {B : Box} (h : Sound N A E Γ B) {items : List LF} (hI : ItemsOK A items)
    {labels : List ℕ} (hlab : labels.length = N.k + N.m)
    (hlt : ∀ t : Fin N.k ⊕ Fin N.m, labels.getD (canon t) 0 < 3)
    {θ γ : ℝ} {D1 D2 : ℤ} (hD1 : (D1 : ℝ) = (2 * θ - 1) * DEN) (hD2 : (D2 : ℝ) = (1 - γ) * DEN)
    (acts : List LF) (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hcheck : g2Check D1 D2 E B acts items labels = true)
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    {c ρ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hLi : ShortSieveLi.LiLemma41 θ γ ρ)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i) :
    Asym θ ρ (fun x y => (N.count x y : ℝ)) := by
  have hD := DEN_pos
  unfold g2Check at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck
  set grp := grpOf labels 3 hlt with hgrp
  set LM := grpLF items labels 0
  set LN := grpLF items labels 1
  have hfM : LM.c.length ≤ B.length := length_grpLF hfit labels 0
  have hfN : LN.c.length ≤ B.length := length_grpLF hfit labels 1
  have hreg : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x →
      |grpExp grp 0 (expo x v) - grpExp grp 1 (expo x v)| ≤ 2 * θ - 1 - 1 / DEN ∧
        1 - γ + 1 / DEN ≤ grpExp grp 0 (expo x v) + grpExp grp 1 (expo x v) := by
    filter_upwards [h.mem_K hE] with x hx v hv h4 h5
    obtain ⟨-, hB, hH, hΓ⟩ := hx v hv h4 h5
    have hacts' : ∀ g ∈ acts, g.val (cX A (expo x v)) (cH (expo x v)) ≤ 0 := fun g hg => by
      obtain ⟨c, hc, rfl⟩ := hacts g hg
      exact hΓ c hc
    have eM : LM.val (cX A (expo x v)) (cH (expo x v)) = DEN * grpExp grp 0 (expo x v) :=
      val_grpLF_eq hI hlab hlt 0 (expo x v)
    have eN : LN.val (cX A (expo x v)) (cH (expo x v)) = DEN * grpExp grp 1 (expo x v) :=
      val_grpLF_eq hI hlab hlt 1 (expo x v)
    -- the three extremes at the point
    have k1 := (LN.add (LM.smul (-1))).minD_le acts hB hH hacts'
      (length_add_le hfN (length_smul_le _ hfM)) hfa
    have k2 := (LM.add (LN.smul (-1))).minD_le acts hB hH hacts'
      (length_add_le hfM (length_smul_le _ hfN)) hfa
    have k3 := (LM.add LN).minD_le acts hB hH hacts' (length_add_le hfM hfN) hfa
    simp only [LF.val_add, LF.val_smul] at k1 k2 k3
    rw [eM, eN] at k1 k2 k3
    -- strict integer checks leave a unit of margin
    have i1 : -(LN.add (LM.smul (-1))).minD B E acts ≤ D1 - 1 := by omega
    have i2 : -(LM.add (LN.smul (-1))).minD B E acts ≤ D1 - 1 := by omega
    have i3 : D2 + 1 ≤ (LM.add LN).minD B E acts := by omega
    have r1 : (-((LN.add (LM.smul (-1))).minD B E acts : ℝ)) ≤ D1 - 1 := by exact_mod_cast i1
    have r2 : (-((LM.add (LN.smul (-1))).minD B E acts : ℝ)) ≤ D1 - 1 := by exact_mod_cast i2
    have r3 : (D2 : ℝ) + 1 ≤ (LM.add LN).minD B E acts := by exact_mod_cast i3
    rw [hD1] at r1 r2
    rw [hD2] at r3
    push_cast at k1 k2 k3
    have e1 : 1 / (DEN : ℝ) * DEN = 1 := by field_simp
    constructor
    · rw [abs_le]
      constructor
      · have : (grpExp grp 1 (expo x v) - grpExp grp 0 (expo x v)) * DEN ≤ (2 * θ - 1 - 1 / DEN) * DEN := by
          nlinarith
        have := le_of_mul_le_mul_right this hD
        linarith
      · have : (grpExp grp 0 (expo x v) - grpExp grp 1 (expo x v)) * DEN ≤ (2 * θ - 1 - 1 / DEN) * DEN := by
          nlinarith
        exact le_of_mul_le_mul_right this hD
    · have : (1 - γ + 1 / DEN) * DEN ≤ (grpExp grp 0 (expo x v) + grpExp grp 1 (expo x v)) * DEN := by
        nlinarith
      exact le_of_mul_le_mul_right this hD
  exact ShortSieveLi.abs_count_sub_le_G2_eps N hk hm hc hc1 hρ hρc (one_div_pos.2 hD) hLi hcond hbig grp hreg

end ShortSieveCert

#print axioms ShortSieveCert.isCompact_KSet
#print axioms ShortSieveCert.Sound.mem_K
#print axioms ShortSieveCert.val_grpLF_eq
#print axioms ShortSieveCert.Sound.asym_of_tii
#print axioms ShortSieveCert.Sound.asym_of_g2
