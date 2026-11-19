/-
# Brun's sieve in product form, with weights and abstract events

Plain statement. `fundamentalW` is `SieveBrun.fundamental` for a finite set `C` with weights `w ≥ 0` and, in place of
`1[p ∣ n]`, any numbers `y_n(p) ∈ [0, 1]` for the moduli `p` of the families `T_j`. If every sum
`Σ_{n∈C} w(n) ∏_j ∏_{p∈s_j} y_n(p)` with `s_j ⊆ T_j` is `X ∏_j ∏_{p∈s_j} g(p)` within `R`, where `X ≥ 0` and
`0 ≤ g ≤ 1` on each `T_j`, then `Σ_{n∈C} w(n) ∏_j ∏_{p∈T_j} (1 − y_n(p))` is `X ∏_j ∏_{p∈T_j} (1 − g(p))` within
`X Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)` plus `(#ι + 1)R ∏_j Σ_{i≤k_j} C(#T_j, i)`, for even levels
`k_j ≥ 1`.

The proof is that of `fundamental`: Bonferroni's inequalities need only `0 ≤ y_n(p) ≤ 1`, and the weights enter the
two lemmas on sums of product weights (`sum_prod_weightsW`, `sum_prod_weightsW_sub`). The gap is bounded by
`SieveBrun.gap_le` as before.

`LeastPrimitiveRootLog.lean` uses it with `C` the integers up to `x` prime to `q`, `w = Λ`, and `y_n(ℓ)` saying
whether `n` is an `ℓ`-th power mod `q`.

The file imports `SieveBrun.lean`.
-/
import SieveBrun

open Finset

namespace SieveBrun

/-! ### Sieve weights summed over a finite set with weights -/

/-- **Product weights over a weighted finite set.** For `w_j(n) = Σ_{b∈F_j} c_j(b) ∏_{p∈S_j(b)} y_n(p)`,
`Σ_{n∈C} w(n) ∏_j w_j(n) = Σ_σ (∏_j c_j(σ_j))·Σ_{n∈C} w(n) ∏_j ∏_{p∈S_j(σ_j)} y_n(p)`. -/
theorem sum_prod_weightsW {γ ι β : Type*} [Fintype ι] [DecidableEq ι] (C : Finset γ) (w : γ → ℝ)
    (y : γ → ℕ → ℝ) (F : ι → Finset β) (S : ι → β → Finset ℕ) (c : ι → β → ℝ) :
    ∑ n ∈ C, w n * ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, y n p =
      ∑ σ ∈ Fintype.piFinset F, (∏ j, c j (σ j)) * ∑ n ∈ C, w n * ∏ j, ∏ p ∈ S j (σ j), y n p := by
  simp_rw [Finset.prod_univ_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.prod_mul_distrib]; ring

/-- The same, against a model `X ∏ g` of the weighted sums with error at most `R`. -/
theorem sum_prod_weightsW_sub {γ ι β : Type*} [Fintype ι] [DecidableEq ι] (C : Finset γ) (w : γ → ℝ)
    (y : γ → ℕ → ℝ) (F : ι → Finset β) (S : ι → β → Finset ℕ) (c : ι → β → ℝ) (X : ℝ) (g : ℕ → ℝ) {R : ℝ}
    (hR : ∀ σ ∈ Fintype.piFinset F,
      |∑ n ∈ C, w n * ∏ j, ∏ p ∈ S j (σ j), y n p - X * ∏ j, ∏ p ∈ S j (σ j), g p| ≤ R) :
    |∑ n ∈ C, w n * ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, y n p -
        X * ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, g p| ≤ R * ∏ j, ∑ b ∈ F j, |c j b| := by
  rw [sum_prod_weightsW, Finset.prod_univ_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.prod_univ_sum,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ hσ => ?_)
  have e : (∏ j, c j (σ j)) * (∑ n ∈ C, w n * ∏ j, ∏ p ∈ S j (σ j), y n p) -
      X * ∏ j, (c j (σ j) * ∏ p ∈ S j (σ j), g p) =
      (∏ j, c j (σ j)) * (∑ n ∈ C, w n * ∏ j, ∏ p ∈ S j (σ j), y n p - X * ∏ j, ∏ p ∈ S j (σ j), g p) := by
    rw [Finset.prod_mul_distrib]; ring
  rw [e, abs_mul, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_right (hR σ hσ) (Finset.prod_nonneg fun j _ => abs_nonneg _)

/-- **The fundamental lemma in product form, with weights and abstract events.** Let `C` be a finite set with
weights `w ≥ 0`, and for `n ∈ C` let `y_n(p) ∈ [0, 1]` for the moduli `p` of finite families `T_j`. Truncate the
inclusion–exclusion of `T_j` at the even level `k_j ≥ 1` for the upper sieve and at `k_j − 1` for the lower. If every
sum `Σ_{n∈C} w(n) ∏_j ∏_{p∈s_j} y_n(p)` with `s_j ⊆ T_j` is `X ∏_j ∏_{p∈s_j} g(p)` within `R`, where `X ≥ 0` and
`0 ≤ g ≤ 1` on each `T_j`, then `Σ_{n∈C} w(n) ∏_j ∏_{p∈T_j} (1 − y_n(p))` is `X ∏_j ∏_{p∈T_j} (1 − g(p))` within
`X Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)` plus `(#ι + 1)R ∏_j Σ_{i≤k_j} C(#T_j, i)`. With `w = 1` and
`y_n(p) = 1[p ∣ n]` this is `fundamental`. -/
theorem fundamentalW {γ ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset γ) {w : γ → ℝ}
    (hw : ∀ n ∈ C, 0 ≤ w n) {y : γ → ℕ → ℝ} (T : ι → Finset ℕ)
    (hy0 : ∀ n ∈ C, ∀ j, ∀ p ∈ T j, 0 ≤ y n p) (hy1 : ∀ n ∈ C, ∀ j, ∀ p ∈ T j, y n p ≤ 1)
    (k : ι → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) {X : ℝ} (hX : 0 ≤ X) {g : ℕ → ℝ}
    (hg0 : ∀ j, ∀ p ∈ T j, 0 ≤ g p) (hg1 : ∀ j, ∀ p ∈ T j, g p ≤ 1) {R : ℝ}
    (hR : ∀ s : ι → Finset ℕ, (∀ j, s j ⊆ T j) →
      |∑ n ∈ C, w n * ∏ j, ∏ p ∈ s j, y n p - X * ∏ j, ∏ p ∈ s j, g p| ≤ R) :
    |∑ n ∈ C, w n * ∏ j, ∏ p ∈ T j, (1 - y n p) - X * ∏ j, ∏ p ∈ T j, (1 - g p)| ≤
      X * ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) +
        (Fintype.card ι + 1) * R * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ) := by
  set N := ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ) with hN
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR (fun _ => ∅) fun _ => Finset.empty_subset _)
  have hN0 : 0 ≤ N := Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  -- pointwise bounds
  have hpt : ∀ n ∈ C, ∀ j, 0 ≤ ∏ p ∈ T j, (1 - y n p) ∧
      trunc (T j) (y n) (k j - 1) ≤ ∏ p ∈ T j, (1 - y n p) ∧
      ∏ p ∈ T j, (1 - y n p) ≤ trunc (T j) (y n) (k j) := fun n hn j => by
    obtain ⟨h1, h2⟩ := trunc_bounds (T := T j) (y := y n) (hy0 n hn j) (hy1 n hn j) (hk j) (hk1 j)
    exact ⟨Finset.prod_nonneg fun p hp => by linarith [hy1 n hn j p hp], h1, h2⟩
  have hdiff : ∀ (y : ℕ → ℝ) j, trunc (T j) y (k j) - trunc (T j) y (k j - 1) = esym (T j) y (k j) :=
    fun y j => trunc_sub_pred (hk j) (hk1 j)
  -- the upper sum
  set U := ∑ n ∈ C, w n * ∏ j, trunc (T j) (y n) (k j) with hU
  have hUerr : |U - X * ∏ j, trunc (T j) g (k j)| ≤ R * N := by
    have h := sum_prod_weightsW_sub C w y (fun j => Ftr (T j) (k j)) (fun _ b => b.2)
      (fun _ b => (-1 : ℝ) ^ b.1) X g (R := R)
      (fun σ hσ => hR (fun j => (σ j).2) fun j => mem_Ftr_sub (Fintype.mem_piFinset.1 hσ j))
    simp only [← trunc_eq_weight, abs_Ftr] at h
    exact h
  -- the gap sums
  set Lg : ι → ℝ := fun j₀ => ∑ n ∈ C, w n * (esym (T j₀) (y n) (k j₀) *
    ∏ i ∈ Finset.univ.erase j₀, trunc (T i) (y n) (k i)) with hLg
  have hLerr : ∀ j₀, |Lg j₀ - X * (esym (T j₀) g (k j₀) * ∏ i ∈ Finset.univ.erase j₀, trunc (T i) g (k i))| ≤
      R * N := by
    intro j₀
    have h := sum_prod_weightsW_sub C w y (fun j => if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j))
      (fun _ b => b.2) (fun j b => if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1) X g (R := R)
      (fun σ hσ => hR (fun j => (σ j).2) fun j => by
        have := Fintype.mem_piFinset.1 hσ j
        split_ifs at this
        · exact mem_Fes_sub this
        · exact mem_Ftr_sub this)
    have hwt : ∀ y : ℕ → ℝ, ∏ j, ∑ b ∈ (if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j)),
        (if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1) * ∏ p ∈ b.2, y p =
        esym (T j₀) y (k j₀) * ∏ i ∈ Finset.univ.erase j₀, trunc (T i) y (k i) := by
      intro y
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
      congr 1
      · simp only [ite_true]; exact (esym_eq_weight _ _ _).symm
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
        simp only [hij, ite_false]
        exact (trunc_eq_weight _ _ _).symm
    have habs : ∏ j, ∑ b ∈ (if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j)),
        |(if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1)| ≤ N := by
      rw [hN, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
        ← Finset.mul_prod_erase Finset.univ (fun j => ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ))
          (Finset.mem_univ j₀)]
      simp only [ite_true]
      rw [abs_Fes]
      have hrest : ∏ i ∈ Finset.univ.erase j₀, ∑ b ∈ (if i = j₀ then Fes (T i) (k i) else Ftr (T i) (k i)),
          |(if i = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1)| =
          ∏ i ∈ Finset.univ.erase j₀, ∑ i' ∈ Finset.range (k i + 1), ((T i).card.choose i' : ℝ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
        simp only [hij, ite_false]
        exact abs_Ftr _ _
      rw [hrest]
      exact mul_le_mul_of_nonneg_right (choose_le_sum_choose _ _)
        (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun i' _ => Nat.cast_nonneg _)
    simp only [hwt] at h
    exact h.trans (mul_le_mul_of_nonneg_left habs hR0)
  -- the sum against the upper and lower sums
  have hup : ∑ n ∈ C, w n * ∏ j, ∏ p ∈ T j, (1 - y n p) ≤ U := by
    rw [hU]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => (hpt n hn j).1) fun j _ => (hpt n hn j).2.2) (hw n hn)
  have hlow : U - ∑ j, Lg j ≤ ∑ n ∈ C, w n * ∏ j, ∏ p ∈ T j, (1 - y n p) := by
    rw [hU, hLg]
    simp only
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have h := prod_lower Finset.univ (fun j => ∏ p ∈ T j, (1 - y n p)) (fun j => trunc (T j) (y n) (k j - 1))
      (fun j => trunc (T j) (y n) (k j)) (fun j _ => (hpt n hn j).1) (fun j _ => (hpt n hn j).2.1)
      (fun j _ => (hpt n hn j).2.2)
    simp only [hdiff] at h
    rw [← Finset.mul_sum, ← mul_sub]
    exact mul_le_mul_of_nonneg_left h (hw n hn)
  -- the model against the same main terms
  have hV : ∀ j, trunc (T j) g (k j - 1) ≤ ∏ p ∈ T j, (1 - g p) ∧ ∏ p ∈ T j, (1 - g p) ≤ trunc (T j) g (k j) :=
    fun j => trunc_bounds (hg0 j) (hg1 j) (hk j) (hk1 j)
  have hV0 : ∀ j, 0 ≤ ∏ p ∈ T j, (1 - g p) := fun j =>
    Finset.prod_nonneg fun p hp => by linarith [hg1 j p hp]
  have hMup : ∏ j, ∏ p ∈ T j, (1 - g p) ≤ ∏ j, trunc (T j) g (k j) :=
    Finset.prod_le_prod₀ (fun j _ => hV0 j) fun j _ => (hV j).2
  have hMlow : ∏ j, trunc (T j) g (k j) - ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) ≤
      ∏ j, ∏ p ∈ T j, (1 - g p) := by
    have h := prod_lower Finset.univ (fun j => ∏ p ∈ T j, (1 - g p)) (fun j => trunc (T j) g (k j - 1))
      (fun j => trunc (T j) g (k j)) (fun j _ => hV0 j) (fun j _ => (hV j).1) (fun j _ => (hV j).2)
    simp only [hdiff] at h
    exact h
  -- combine
  set G := ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) with hG
  set P := ∏ j, trunc (T j) g (k j) with hP
  have hLsum : ∑ j, Lg j ≤ X * G + Fintype.card ι * (R * N) := by
    calc ∑ j, Lg j ≤ ∑ j, (X * (esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i)) + R * N) :=
          Finset.sum_le_sum fun j _ => by linarith [(abs_le.1 (hLerr j)).2]
      _ = X * G + Fintype.card ι * (R * N) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hU1 := abs_le.1 hUerr
  have hXM1 : X * ∏ j, ∏ p ∈ T j, (1 - g p) ≤ X * P := mul_le_mul_of_nonneg_left hMup hX
  have hXM2 : X * P - X * G ≤ X * ∏ j, ∏ p ∈ T j, (1 - g p) := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left hMlow hX
  rw [abs_le]
  constructor <;> nlinarith

end SieveBrun
