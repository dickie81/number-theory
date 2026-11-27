import FirstCloudPair

/-!
# The dimensions of the cloud step (L5, A-N15, the Weyl count)

The dimension half of Annex I N15 (module 11, `FirstCloud`): for a weight `λ` of the cloud shape with top extremes
`(A_s + c, B_s + c)`, `A_s, B_s ≥ b′/3 > 0`, middle entries in `[−c, c]`, the flat weights `H = fl(A, B)`,
`H⁺ = fl(A + 2c, B + 2c)` and the number `m = ∏_{s ∈ TT} ∏_{i<j} midFac(λ_s)_{ij}` of cloud vectors:
`m·d(H) ≤ d(λ) ≤ e^ε·m·d(H)` and `d(H⁺) ≤ e^ε·d(H)`, `ε = 12Nkc/b′` (`cloud_dims`), given the Weyl dimension formula
for the repo's `∇` (`WeylDim`, an input; its combinatorial side is `WeylCount.dimW_eq_prod`).

**The route.** In the product formula `dimW(w) = ∏_{i<j} (w_i − w_j + j − i)/(j − i)` each factor is the middle factor
(`midFac`, the pairs inside `[1, k − 2]`) times the outer factor (`outFac`, the pairs through `0` or `k − 1`)
(`dimW_eq_mid_out`); a flat weight has middle factors `1`. The outer factors of `λ_s` and of `H⁺_s` exceed those of
`H_s` by at most `2c`, resp. `4c`, over denominators `≥ b′/3`, resp. `≥ 2b′/3`, so by a factor in `[1, 1 + 6c/b′]`
(`outer_bounds`); the exponents `[i = 0] + [j = k − 1]` add up to at most `2k` (`sum_outExp_le`), so each block costs
at most `(1 + 6c/b′)^{2k}` (`dimW_bounds`), and `(1 + 6c/b′)^{2kN} ≤ e^{12Nkc/b′}`.
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly WeylCount Finset

noncomputable section

/-- **The Weyl dimension formula for `∇`** (Annex I's I8, an input): for a dominant weight `λ` on one orbit,
`dim V(λ) = ∏_s dimW_k(λ_s)` (the block of an odd position carries the dual weight, of the same Weyl dimension,
`WeylCount.dimW_dual`). `FirstAssembly.FlatDim` is the case of the flat weights (`WeylCount.dimW_flatW`). -/
def WeylDim (Kf : Type) [Field Kf] (n' k : ℕ) : Prop :=
  ∀ lam0 : Fin n' → Fin k → ℤ, (∀ s, Antitone (lam0 s)) → dimV Kf lam0 = ∏ s, dimW k (lam0 s)

/-! ## Middle and outer factors of the Weyl product -/

section Factors

variable {k : ℕ}

/-- **The outer Weyl factor** of `w` at `i < j`: `(w_i − w_j + j − i)/(j − i)` when the pair meets `0` or `k − 1`,
`1` for the pairs inside `[1, k − 2]` (the complement of `midFac`). -/
def outFac (w : Fin k → ℤ) (i j : Fin k) : ℚ :=
  if 0 < i.val ∧ j.val + 1 < k then 1
  else ((w i - w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℚ) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))

/-- **The exponent of an outer pair**: `[i = 0] + [j = k − 1]`. -/
def outExp (i j : Fin k) : ℕ := (if i.val = 0 then 1 else 0) + (if j.val + 1 = k then 1 else 0)

/-- **The Weyl dimension splits** into the middle and the outer factors. -/
theorem dimW_eq_mid_out {w : Fin k → ℤ} (hw : Antitone w) :
    (dimW k w : ℚ) = (∏ i, ∏ j ∈ Ioi i, midFac w i j) * ∏ i, ∏ j ∈ Ioi i, outFac w i j := by
  rw [dimW_eq_prod hw, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  unfold midFac outFac
  split_ifs <;> ring

/-- **The middle factors of a weight vanishing in the middle** are `1`. -/
theorem prod_midFac_eq_one {h : Fin k → ℤ} (hh : ∀ i : Fin k, 0 < i.val → i.val + 1 < k → h i = 0) :
    ∏ i, ∏ j ∈ Ioi i, midFac h i j = 1 := by
  refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
  have hij : i.val < j.val := Fin.lt_def.1 (mem_Ioi.1 hj)
  unfold midFac
  split_ifs with hm
  · rw [hh i hm.1 (by omega), hh j (by omega) hm.2]
    have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
      have : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
      linarith
    push_cast
    field_simp
    ring
  · rfl

/-- **The exponents of the outer pairs add up to at most `2k`.** -/
theorem sum_outExp_le : ∑ i : Fin k, ∑ j ∈ Ioi i, outExp i j ≤ 2 * k := by
  have h1 : ∀ i : Fin k, ∑ j ∈ Ioi i, outExp i j ≤ k * (if i.val = 0 then 1 else 0) + 1 := by
    intro i
    calc ∑ j ∈ Ioi i, outExp i j ≤ ∑ j : Fin k, outExp i j :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
      _ = k * (if i.val = 0 then 1 else 0) + (univ.filter fun j : Fin k => j.val + 1 = k).card := by
          simp only [outExp, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_boole,
            Nat.cast_id]
      _ ≤ _ := by
          gcongr
          exact card_le_one.2 fun a ha b hb => Fin.ext (by simp at ha hb; omega)
  calc ∑ i : Fin k, ∑ j ∈ Ioi i, outExp i j ≤ ∑ i : Fin k, (k * (if i.val = 0 then 1 else 0) + 1) :=
        sum_le_sum fun i _ => h1 i
    _ = k * (univ.filter fun i : Fin k => i.val = 0).card + k := by
        simp only [sum_add_distrib, ← mul_sum, sum_boole, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
          Nat.cast_id]
    _ ≤ k * 1 + k := by
        gcongr
        exact card_le_one.2 fun a ha b hb => Fin.ext (by simp at ha hb; omega)
    _ = 2 * k := by ring

/-- **The block bounds**: for antitone `w`, `h` with `h` vanishing in the middle, if on every outer pair `i < j` the
numerators satisfy `0 < N_h ≤ N_w ≤ (1 + δ)·N_h` (`N_w = w_i − w_j + j − i`), then
`0 ≤ m_w` and `m_w·dimW(h) ≤ dimW(w) ≤ (1 + δ)^{2k}·m_w·dimW(h)`, `m_w = ∏ midFac w`. -/
theorem dimW_bounds {w h : Fin k → ℤ} (hw : Antitone w) (hh : Antitone h)
    (hmid : ∀ i : Fin k, 0 < i.val → i.val + 1 < k → h i = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpair : ∀ i j : Fin k, i < j → ¬ (0 < i.val ∧ j.val + 1 < k) →
      0 < ((h i - h j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ) ∧
      ((h i - h j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((w i - w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ) ∧
      ((w i - w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ) ≤
        (1 + δ) * ((h i - h j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ)) :
    0 ≤ ((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) ∧
      (((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ)) * dimW k h ≤ dimW k w ∧
      (dimW k w : ℝ) ≤ (1 + δ) ^ (2 * k) * (((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) * dimW k h) := by
  -- the outer factors, pair by pair
  have hout : ∀ i j : Fin k, i < j → 0 < (outFac h i j : ℝ) ∧ (outFac h i j : ℝ) ≤ outFac w i j ∧
      (outFac w i j : ℝ) ≤ (1 + δ) ^ outExp i j * outFac h i j := by
    intro i j hij
    have hji : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      linarith
    unfold outFac
    split_ifs with hm
    · have he : outExp i j = 0 := by simp [outExp]; omega
      simp [he]
    · obtain ⟨h0, h1, h2⟩ := hpair i j hij hm
      have he : 1 ≤ outExp i j := by simp only [outExp]; split_ifs <;> omega
      have hρ : (1 + δ) ≤ (1 + δ) ^ outExp i j := le_self_pow₀ (by linarith) (by omega)
      push_cast at h0 h1 h2 ⊢
      refine ⟨div_pos h0 hji, div_le_div_of_nonneg_right h1 hji.le, ?_⟩
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right (h2.trans ?_) hji.le
      exact mul_le_mul_of_nonneg_right hρ h0.le
  have hM : (0 : ℝ) ≤ ((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) := by
    push_cast
    refine prod_nonneg fun i _ => prod_nonneg fun j hj => ?_
    have hij : i.val < j.val := Fin.lt_def.1 (mem_Ioi.1 hj)
    unfold midFac
    split_ifs
    · have : w j ≤ w i := hw (Fin.le_def.2 hij.le)
      have h2 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      push_cast
      exact div_nonneg (by linarith [show (w j : ℝ) ≤ w i by exact_mod_cast this]) (by linarith)
    · norm_num
  have ew : (dimW k w : ℝ) = ((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) * ∏ i, ∏ j ∈ Ioi i, (outFac w i j : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (dimW_eq_mid_out hw)
    push_cast at this ⊢
    exact this
  have eh : (dimW k h : ℝ) = ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (dimW_eq_mid_out hh)
    rw [prod_midFac_eq_one hmid, one_mul] at this
    push_cast at this ⊢
    exact this
  have hlow : ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ) ≤ ∏ i, ∏ j ∈ Ioi i, (outFac w i j : ℝ) :=
    prod_le_prod₀ (fun i _ => prod_nonneg fun j hj => (hout i j (mem_Ioi.1 hj)).1.le)
      fun i _ => prod_le_prod₀ (fun j hj => (hout i j (mem_Ioi.1 hj)).1.le) fun j hj => (hout i j (mem_Ioi.1 hj)).2.1
  have hup : ∏ i, ∏ j ∈ Ioi i, (outFac w i j : ℝ) ≤
      (1 + δ) ^ (2 * k) * ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ) := by
    calc ∏ i, ∏ j ∈ Ioi i, (outFac w i j : ℝ) ≤ ∏ i, ∏ j ∈ Ioi i, ((1 + δ) ^ outExp i j * outFac h i j) :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun j hj => (hout i j (mem_Ioi.1 hj)).1.le.trans
            (hout i j (mem_Ioi.1 hj)).2.1)
            fun i _ => prod_le_prod₀ (fun j hj => (hout i j (mem_Ioi.1 hj)).1.le.trans (hout i j (mem_Ioi.1 hj)).2.1)
              fun j hj => (hout i j (mem_Ioi.1 hj)).2.2
      _ = (1 + δ) ^ (∑ i : Fin k, ∑ j ∈ Ioi i, outExp i j) * ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ) := by
          simp only [prod_mul_distrib, prod_pow_eq_pow_sum]
      _ ≤ (1 + δ) ^ (2 * k) * ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) sum_outExp_le)
            (prod_nonneg fun i _ => prod_nonneg fun j hj => (hout i j (mem_Ioi.1 hj)).1.le)
  rw [ew, eh]
  refine ⟨hM, mul_le_mul_of_nonneg_left hlow hM, ?_⟩
  calc ((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) * ∏ i, ∏ j ∈ Ioi i, (outFac w i j : ℝ)
      ≤ ((∏ i, ∏ j ∈ Ioi i, midFac w i j : ℚ) : ℝ) * ((1 + δ) ^ (2 * k) * ∏ i, ∏ j ∈ Ioi i, (outFac h i j : ℝ)) :=
        mul_le_mul_of_nonneg_left hup hM
    _ = _ := by ring

end Factors


/-! ## The outer pairs of the cloud shape -/

section Cloud

variable {n' k : ℕ}

/-- **The outer numerators of the cloud shape**: at a top `s` and an outer pair `i < j` (through `0` or `k − 1`), the
numerators `N(w) = w_i − w_j + j − i` of `H_s`, `λ_s`, `H⁺_s` satisfy `0 < N(H) ≤ N(λ) ≤ (1 + 6c/b′)·N(H)` and
`N(H) ≤ N(H⁺) ≤ (1 + 6c/b′)·N(H)`: the differences are at most `2c` (resp. `4c` on the pair `(0, k − 1)`) over
`N(H) ≥ b′/3` (resp. `≥ 2b′/3`). -/
theorem cloud_pairs {TT : Finset (Fin n')} {c : ℕ} {b' : ℝ} (hb' : 0 < b') {A B : TT → ℤ}
    (hA : ∀ s, b' / 3 ≤ (A s : ℝ)) (hB : ∀ s, b' / 3 ≤ (B s : ℝ)) {lam0 : Fin n' → Fin k → ℤ}
    (hsh : IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0) {s : Fin n'}
    (hs : s ∈ TT) (i j : Fin k) (hij : i < j) (hm : ¬ (0 < i.val ∧ j.val + 1 < k)) :
    let N : (Fin k → ℤ) → ℝ := fun w => ((w i - w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℝ)
    0 < N (flatWt TT A B s) ∧ N (flatWt TT A B s) ≤ N (lam0 s) ∧
      N (lam0 s) ≤ (1 + 6 * c / b') * N (flatWt TT A B s) ∧
      N (flatWt TT A B s) ≤ N (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ)) s) ∧
      N (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ)) s) ≤
        (1 + 6 * c / b') * N (flatWt TT A B s) := by
  intro N
  have hij' : i.val < j.val := Fin.lt_def.1 hij
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set a := A ⟨s, hs⟩ with ha
  set b := B ⟨s, hs⟩ with hb
  have ha3 : b' / 3 ≤ (a : ℝ) := hA _
  have hb3 : b' / 3 ≤ (b : ℝ) := hB _
  have key2 : ∀ x : ℝ, b' / 3 ≤ x → 2 * c ≤ 6 * c / b' * x := fun x hx => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb']
    nlinarith
  have key4 : ∀ x : ℝ, 2 * b' / 3 ≤ x → 4 * c ≤ 6 * c / b' * x := fun x hx => by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb']
    nlinarith
  have hsh' := fun l : Fin k => (hsh.2 s l).1 hs
  have e0 : ∀ l : Fin k, l.val = 0 → lam0 s l = a + c := fun l hl => by
    rw [(hsh' l).1 hl, ext_add, ext_of_mem _ hs, ext_of_mem _ hs]
  have e1 : ∀ l : Fin k, l.val + 1 = k → lam0 s l = -(b + c) := fun l hl => by
    rw [(hsh' l).2.1 hl, ext_add, ext_of_mem _ hs, ext_of_mem _ hs]
  have em : ∀ l : Fin k, 0 < l.val → l.val + 1 < k → |lam0 s l| ≤ c := fun l h1 h2 => (hsh' l).2.2 h1 h2
  have fH : ∀ (α β : TT → ℤ) (l : Fin k), flatWt (k := k) TT α β s l =
      if l.val = 0 then α ⟨s, hs⟩ else if l.val + 1 = k then -β ⟨s, hs⟩ else 0 := fun α β l => by
    simp only [flatWt, ext_of_mem _ hs]
  simp only [N, fH, Pi.add_apply]
  have hj0 : j.val ≠ 0 := by omega
  have hi1 : i.val + 1 ≠ k := by omega
  simp only [hj0, hi1, ite_false]
  have hjr : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij'
    linarith
  by_cases hi : i.val = 0
  · by_cases hj : j.val + 1 = k
    · -- the pair `(0, k − 1)`
      rw [e0 i hi, e1 j hj]
      simp only [hi, hj, ite_true]
      push_cast
      have h4 := key4 ((a : ℝ) + b + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) (by linarith)
      refine ⟨by linarith, by linarith, by nlinarith, by linarith, by nlinarith⟩
    · -- the pairs `(0, j)`, `j` in the middle
      have hjm := abs_le.1 (em j (by omega) (by omega))
      rw [e0 i hi]
      simp only [hi, hj, ite_true, ite_false]
      push_cast
      have hjm' : -(c : ℝ) ≤ lam0 s j ∧ (lam0 s j : ℝ) ≤ c := by exact_mod_cast hjm
      have h2 := key2 ((a : ℝ) - 0 + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) (by linarith)
      refine ⟨by linarith, by linarith, by nlinarith, by linarith, by nlinarith⟩
  · -- the pairs `(i, k − 1)`, `i` in the middle
    have hj : j.val + 1 = k := by omega
    have him := abs_le.1 (em i (by omega) (by omega))
    rw [e1 j hj]
    simp only [hi, hj, ite_true, ite_false]
    push_cast
    have him' : -(c : ℝ) ≤ lam0 s i ∧ (lam0 s i : ℝ) ≤ c := by exact_mod_cast him
    have h2 := key2 (0 - -(b : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) (by linarith)
    refine ⟨by linarith, by linarith, by nlinarith, by linarith, by nlinarith⟩

/-- **The dimensions of the cloud step** (N15, the Weyl count): for `λ` of the cloud shape with `A_s, B_s ≥ b′/3 > 0`,
`m = ∏_{s ∈ TT} ∏_{i<j} midFac(λ_s)_{ij}` and `ε = 12Nkc/b′`: `m·d(H) ≤ d(λ) ≤ e^ε·m·d(H)` and `d(H⁺) ≤ e^ε·d(H)`
(`WeylDim`; blocks off the tops have dimension `1`; `dimW_bounds` with `cloud_pairs` at each top, and
`(1 + 6c/b′)^{2kN} ≤ e^{12Nkc/b′}`). -/
theorem cloud_dims {Kf : Type} [Field Kf] (hk : 2 ≤ k) (hWD : WeylDim Kf n' k) {TT : Finset (Fin n')} {c : ℕ}
    {b' : ℝ} (hb' : 0 < b') {A B : TT → ℤ} (hA : ∀ s, b' / 3 ≤ (A s : ℝ)) (hB : ∀ s, b' / 3 ≤ (B s : ℝ))
    {lam0 : Fin n' → Fin k → ℤ}
    (hsh : IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0)
    (hz : ∀ s ∉ TT, lam0 s = 0) :
    ((∏ x ∈ TT, ∏ i : Fin k, ∏ j ∈ Ioi i, midFac (lam0 x) i j : ℚ) : ℝ) * dimV Kf (flatWt (k := k) TT A B) ≤
        dimV Kf lam0 ∧
      (dimV Kf lam0 : ℝ) ≤ Real.exp (12 * TT.card * k * c / b') *
        (((∏ x ∈ TT, ∏ i : Fin k, ∏ j ∈ Ioi i, midFac (lam0 x) i j : ℚ) : ℝ) * dimV Kf (flatWt (k := k) TT A B)) ∧
      (dimV Kf (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) : ℝ) ≤
        Real.exp (12 * TT.card * k * c / b') * dimV Kf (flatWt (k := k) TT A B) := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set δ : ℝ := 6 * c / b' with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h3 : (0 : ℝ) < b' / 3 := by positivity
  have hA0 : ∀ s, 0 ≤ A s := fun s => by
    have : (0 : ℝ) ≤ A s := by linarith [hA s]
    exact_mod_cast this
  have hB0 : ∀ s, 0 ≤ B s := fun s => by
    have : (0 : ℝ) ≤ B s := by linarith [hB s]
    exact_mod_cast this
  have hc2 : (0 : ℤ) ≤ 2 * c := by positivity
  have hHa := antitone_flatWt hk hA0 hB0
  have hPa := antitone_flatWt (α := A + fun _ => 2 * (c : ℤ)) (β := B + fun _ => 2 * (c : ℤ)) hk
    (fun s => add_nonneg (hA0 s) hc2) (fun s => add_nonneg (hB0 s) hc2)
  rw [hWD lam0 hsh.1, hWD _ hHa, hWD _ hPa]
  have hoff : ∀ f : Fin n' → Fin k → ℤ, (∀ s ∉ TT, f s = 0) → ∏ s, dimW k (f s) = ∏ s ∈ TT, dimW k (f s) :=
    fun f hf => (prod_subset (subset_univ TT) fun s _ hs => by rw [hf s hs, dimW_zero]).symm
  have hfz : ∀ α β : TT → ℤ, ∀ s ∉ TT, flatWt (k := k) TT α β s = 0 := fun α β s hs => by
    funext i
    simp [flatWt, ext_of_not_mem _ hs]
  rw [hoff _ hz, hoff _ (hfz _ _), hoff _ (hfz _ _), Nat.cast_prod, Nat.cast_prod, Nat.cast_prod, Rat.cast_prod]
  have hmid : ∀ (α β : TT → ℤ) (s : Fin n') (i : Fin k), 0 < i.val → i.val + 1 < k → flatWt (k := k) TT α β s i = 0 :=
    fun α β s i h1 h2 => by simp [flatWt, show i.val ≠ 0 by omega, show i.val + 1 ≠ k by omega]
  have hb1 : ∀ s ∈ TT, _ := fun s hs => dimW_bounds (hsh.1 s) (hHa s) (hmid A B s) hδ0 fun i j hij hm =>
    let P := cloud_pairs hb' hA hB hsh hs i j hij hm
    ⟨P.1, P.2.1, P.2.2.1⟩
  have hb2 : ∀ s ∈ TT, _ := fun s hs => dimW_bounds (hPa s) (hHa s) (hmid A B s) hδ0 fun i j hij hm =>
    let P := cloud_pairs hb' hA hB hsh hs i j hij hm
    ⟨P.1, P.2.2.2.1, P.2.2.2.2⟩
  have hm2 : ∀ s, ∏ i : Fin k, ∏ j ∈ Ioi i, midFac (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ))
      (B + fun _ => 2 * (c : ℤ)) s) i j = 1 := fun s => prod_midFac_eq_one (hmid _ _ s)
  -- the exponential
  have hexp : ((1 + δ) ^ (2 * k)) ^ TT.card ≤ Real.exp (12 * TT.card * k * c / b') := by
    calc ((1 + δ) ^ (2 * k)) ^ TT.card ≤ (Real.exp δ ^ (2 * k)) ^ TT.card := by
          gcongr
          linarith [Real.add_one_le_exp δ]
      _ = Real.exp (12 * TT.card * k * c / b') := by
          rw [← pow_mul, ← Real.exp_nat_mul]
          congr 1
          rw [hδ]
          push_cast
          ring
  have hexp0 : (0 : ℝ) ≤ ((1 + δ) ^ (2 * k)) ^ TT.card := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [← prod_mul_distrib]
    exact prod_le_prod₀ (fun s hs => mul_nonneg (hb1 s hs).1 (Nat.cast_nonneg _)) fun s hs => (hb1 s hs).2.1
  · calc ∏ s ∈ TT, (dimW k (lam0 s) : ℝ)
        ≤ ∏ s ∈ TT, ((1 + δ) ^ (2 * k) * (((∏ i : Fin k, ∏ j ∈ Ioi i, midFac (lam0 s) i j : ℚ) : ℝ) *
          dimW k (flatWt (k := k) TT A B s))) :=
          prod_le_prod₀ (fun s _ => Nat.cast_nonneg _) fun s hs => (hb1 s hs).2.2
      _ = ((1 + δ) ^ (2 * k)) ^ TT.card * ((∏ s ∈ TT, ((∏ i : Fin k, ∏ j ∈ Ioi i, midFac (lam0 s) i j : ℚ) : ℝ)) *
          ∏ s ∈ TT, (dimW k (flatWt (k := k) TT A B s) : ℝ)) := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp
          (mul_nonneg (prod_nonneg fun s hs => (hb1 s hs).1) (prod_nonneg fun _ _ => Nat.cast_nonneg _))
  · calc ∏ s ∈ TT, (dimW k (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ)) s) : ℝ)
        ≤ ∏ s ∈ TT, ((1 + δ) ^ (2 * k) * (dimW k (flatWt (k := k) TT A B s) : ℝ)) :=
          prod_le_prod₀ (fun s _ => Nat.cast_nonneg _) fun s hs => by
            have := (hb2 s hs).2.2
            rwa [hm2 s, Rat.cast_one, one_mul] at this
      _ = ((1 + δ) ^ (2 * k)) ^ TT.card * ∏ s ∈ TT, (dimW k (flatWt (k := k) TT A B s) : ℝ) := by
          rw [prod_mul_distrib, prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (prod_nonneg fun _ _ => Nat.cast_nonneg _)

end Cloud

end

end FirstCloud
