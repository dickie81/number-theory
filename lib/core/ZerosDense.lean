/-
# The zeros of `ζ` are denser than any linear rate

Plain statement. Let `N(T)` be the number of zeros `±τ` of `Ξ(t) = ξ(½ + it)` with `|τ| ≤ T`, counted in pairs with
multiplicity (`count`): the nontrivial zeros `ρ = ½ ± iτ` of `ζ` with `|ρ − ½| ≤ T`, two to a pair. Then `N(T)/T` is
unbounded: no `A` has `N(T) ≤ A·T` for every `T ≥ 1` (`not_linear`). No hypothesis.

* Hadamard's factorisation bounds `Ξ` by its zeros: `‖Ξ(z)‖ ≤ ‖Ξ(0)‖·exp Σ_τ log(1 + |z|²/|τ|²)` (`norm_Xi_le`), from
  its partial products.
* If `N(T) ≤ AT` for `T ≥ 1`, summation by parts against the counting function, with
  `Σ_{1 ≤ j < M} log(1 + y²/j²) ≤ 5y + 2` (`sum_log_nat_le`), gives
  `Σ_τ log(1 + y²/|τ|²) ≤ A(5y + 2 + 2log(1 + y²)) + C` for `y ≥ 1` (`sum_log_le`).
* But `ξ(2m + 2) ≥ m!/π^{m+1}` (`ZerosInfinite.norm_xi_ge`), so at `y = 2m + 3/2` the sum is at least
  `m log m − O(m)`, which outgrows `18A(m + 1)`.

Riemann and von Mangoldt (1905) give `N(T) ~ (T/2π)log T`. This is a crude half of it: the zeros are denser than any
linear rate at some heights. It is what `BallHadamard.unbounded_gaps` needs.
-/
import Mathlib
import ZerosInfinite

open Complex Finset Filter Topology WeilForm WeilTest

noncomputable section

namespace ZerosDense

/-! ## Hadamard's factorisation bounds `Ξ` by its zeros -/

/-- **`‖Ξ(z)‖ ≤ ‖Ξ(0)‖·exp Σ_τ log(1 + ‖z‖²/|τ|²)`**: each partial product of `Π_τ(1 − z²/τ²)` is at most
`Π_τ(1 + ‖z‖²/|τ|²)`. -/
theorem norm_Xi_le (z : ℂ) :
    ‖Xi z‖ ≤ ‖Xi 0‖ * Real.exp (∑' i : ZeroIdx (sqF Xi), Real.log (1 + ‖z‖ ^ 2 * ‖i.1⁻¹‖)) := by
  have H := hadamardW_Xi xiGrowth Xi_zero_ne_zero
  set g : ZeroIdx (sqF Xi) → ℝ := fun i => Real.log (1 + ‖z‖ ^ 2 * ‖i.1⁻¹‖) with hgdef
  have hpos : ∀ i : ZeroIdx (sqF Xi), 0 < 1 + ‖z‖ ^ 2 * ‖i.1⁻¹‖ := fun i => by positivity
  have hg0 : ∀ i, 0 ≤ g i := fun i => Real.log_nonneg (by
    have := mul_nonneg (sq_nonneg ‖z‖) (norm_nonneg i.1⁻¹)
    linarith)
  have hgs : Summable g := (H.summ.mul_left (‖z‖ ^ 2)).of_nonneg_of_le hg0 fun i => by
    have h := Real.log_le_sub_one_of_pos (hpos i)
    simp only [hgdef]
    linarith
  have ht : Tendsto (fun s : Finset (ZeroIdx (sqF Xi)) => ‖∏ i ∈ s, (1 - z ^ 2 * i.1⁻¹)‖) atTop
      (𝓝 ‖Xi z / Xi 0‖) := Filter.Tendsto.norm (H.prod z)
  have hle : ‖Xi z / Xi 0‖ ≤ Real.exp (∑' i, g i) := by
    refine le_of_tendsto' ht fun s => ?_
    rw [norm_prod]
    calc ∏ i ∈ s, ‖1 - z ^ 2 * i.1⁻¹‖ ≤ ∏ i ∈ s, Real.exp (g i) := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [hgdef, Real.exp_log (hpos i)]
          calc ‖1 - z ^ 2 * i.1⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 * i.1⁻¹‖ := norm_sub_le _ _
            _ = 1 + ‖z‖ ^ 2 * ‖i.1⁻¹‖ := by rw [norm_one, norm_mul, norm_pow]
      _ = Real.exp (∑ i ∈ s, g i) := (Real.exp_sum s g).symm
      _ ≤ Real.exp (∑' i, g i) := Real.exp_le_exp.2 (hgs.sum_le_tsum s fun i _ => hg0 i)
  have h0 := norm_pos_iff.2 Xi_zero_ne_zero
  rw [norm_div, div_le_iff₀ h0] at hle
  linarith

/-! ## The counting function -/

/-- The zeros with `|τ| ≤ T` are finitely many. -/
lemma finite_le (T : ℝ) : {i : ZeroIdx (sqF Xi) | ‖tau i‖ ≤ T}.Finite := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ := (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  set K : ℝ := max (T ^ 2) 1 with hK
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK0))
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hi ⊢
  rw [norm_inv]
  have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx_ne_zero i)
  have e : ‖i.1‖ = ‖tau i‖ ^ 2 := by rw [← tau_sq, norm_pow]
  refine inv_anti₀ hp ?_
  rw [e]
  exact (pow_le_pow_left₀ (norm_nonneg _) hi 2).trans (le_max_left _ _)

/-- **The counting function** `N(T)`: the number of zero pairs `±τ` of `Ξ` with `|τ| ≤ T`, with multiplicity. -/
def count (T : ℝ) : ℕ := {i : ZeroIdx (sqF Xi) | ‖tau i‖ ≤ T}.ncard

lemma card_le_count {T : ℝ} (s : Finset (ZeroIdx (sqF Xi))) (hs : ∀ i ∈ s, ‖tau i‖ ≤ T) : s.card ≤ count T := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun i hi => hs i hi) (finite_le T)

/-! ## Summation by parts -/

lemma telescope (h : ℝ → ℝ) {k M : ℕ} (hkM : k ≤ M) :
    ∑ j ∈ Ico k M, (h j - h ((j : ℝ) + 1)) = h k - h M := by
  induction M, hkM using Nat.le_induction with
  | base => simp
  | succ M hkM ih => rw [Finset.sum_Ico_succ_top hkM, ih]; push_cast; ring

lemma abel (h : ℝ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ j ∈ Ico 1 M, (h j - h ((j : ℝ) + 1)) * ((j : ℝ) + 1) + M * h M = h 1 + ∑ j ∈ Ico 1 M, h j := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, Finset.sum_Ico_succ_top hM]
    push_cast
    linear_combination ih

/-- `log m! ≥ m log m − m`, from `m^m/m! ≤ e^m`. -/
lemma log_factorial_ge (m : ℕ) : (m : ℝ) * Real.log m - m ≤ Real.log m.factorial := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h2
  linarith

/-- **`Σ_{1 ≤ j < M} log(1 + y²/j²) ≤ 5y + 2`** for `y ≥ 1`: below `y` the terms are at most `log(2y²/j²)`, which sum to
`K log 2y² − 2log K!` with `K = ⌊y⌋`; above `y` they are at most `y²/j²`. -/
lemma sum_log_nat_le {y : ℝ} (hy : 1 ≤ y) (M : ℕ) :
    ∑ j ∈ Ico 1 M, Real.log (1 + y ^ 2 / (j : ℝ) ^ 2) ≤ 5 * y + 2 := by
  set K := ⌊y⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hy)
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hy0 : 0 < y := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not (Ico 1 M) (fun j => j ≤ K)]
  -- the terms with `j ≤ ⌊y⌋`
  have h1 : ∑ j ∈ (Ico 1 M).filter (fun j => j ≤ K), Real.log (1 + y ^ 2 / (j : ℝ) ^ 2) ≤
      K * (Real.log 2 + 2) + 2 := by
    calc ∑ j ∈ (Ico 1 M).filter (fun j => j ≤ K), Real.log (1 + y ^ 2 / (j : ℝ) ^ 2)
        ≤ ∑ j ∈ Ico 1 (K + 1), Real.log (1 + y ^ 2 / (j : ℝ) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => Real.log_nonneg ?_
          · simp only [Finset.mem_filter, Finset.mem_Ico] at hj
            exact Finset.mem_Ico.2 ⟨hj.1.1, by omega⟩
          · have : 0 ≤ y ^ 2 / (j : ℝ) ^ 2 := by positivity
            linarith
      _ ≤ ∑ j ∈ Ico 1 (K + 1), (Real.log 2 + 2 * Real.log y - 2 * Real.log j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj1 : 1 ≤ j := (Finset.mem_Ico.1 hj).1
          have hjK : j ≤ K := by have := (Finset.mem_Ico.1 hj).2; omega
          have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
          have hjy : (j : ℝ) ≤ y := le_trans (by exact_mod_cast hjK) hKy
          have hq : 1 ≤ y ^ 2 / (j : ℝ) ^ 2 := by
            rw [le_div_iff₀ (by positivity), one_mul]
            exact pow_le_pow_left₀ hj0.le hjy 2
          calc Real.log (1 + y ^ 2 / (j : ℝ) ^ 2) ≤ Real.log (2 * (y ^ 2 / (j : ℝ) ^ 2)) :=
                Real.log_le_log (by positivity) (by linarith)
            _ = Real.log 2 + 2 * Real.log y - 2 * Real.log j := by
                rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by positivity),
                  Real.log_pow, Real.log_pow]
                push_cast
                ring
      _ = K * (Real.log 2 + 2 * Real.log y) - 2 * Real.log K.factorial := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod (fun j hj => by
              have := (Finset.mem_Ico.1 hj).1
              positivity)]
      _ ≤ K * (Real.log 2 + 2) + 2 := by
          have hf := log_factorial_ge K
          have hlog : Real.log y - Real.log K ≤ y / K - 1 := by
            rw [← Real.log_div hy0.ne' hK0.ne']
            exact Real.log_le_sub_one_of_pos (by positivity)
          have e : (K : ℝ) * (y / K - 1) = y - K := by field_simp
          nlinarith
  -- the terms with `j > ⌊y⌋`
  have h2 : ∑ j ∈ (Ico 1 M).filter (fun j => ¬ j ≤ K), Real.log (1 + y ^ 2 / (j : ℝ) ^ 2) ≤ 2 * y := by
    calc ∑ j ∈ (Ico 1 M).filter (fun j => ¬ j ≤ K), Real.log (1 + y ^ 2 / (j : ℝ) ^ 2)
        ≤ ∑ j ∈ (Ico 1 M).filter (fun j => ¬ j ≤ K), y ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := Real.log_le_sub_one_of_pos (show 0 < 1 + y ^ 2 / (j : ℝ) ^ 2 by positivity)
          rw [div_eq_mul_inv] at h ⊢
          linarith
      _ ≤ ∑ j ∈ Ioo K M, y ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => by positivity
          simp only [Finset.mem_filter, Finset.mem_Ico, not_le] at hj
          exact Finset.mem_Ioo.2 ⟨hj.2, hj.1.2⟩
      _ = y ^ 2 * ∑ j ∈ Ioo K M, ((j : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ y ^ 2 * (2 / ((K : ℝ) + 1)) := mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le K M) (by positivity)
      _ ≤ 2 * y := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hl2 := Real.log_two_lt_d9
  have : (K : ℝ) * (Real.log 2 + 2) ≤ 3 * y := by nlinarith
  linarith

/-- **Summation by parts against the counting function**: if `N(T) ≤ AT` for `T ≥ 1`, then
`Σ_τ log(1 + y²/|τ|²) ≤ A(5y + 2 + 2log(1 + y²)) + C` for `y ≥ 1`, with `C` the contribution of the zeros with
`|τ| ≤ 1` at `y = 1`. -/
theorem sum_log_le {A : ℝ} (hA : ∀ T : ℝ, 1 ≤ T → (count T : ℝ) ≤ A * T) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ∑' i : ZeroIdx (sqF Xi), Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) ≤ A * (5 * y + 2 + 2 * Real.log (1 + y ^ 2)) + C := by
  have hA0 : 0 ≤ A := by
    have h := hA 1 le_rfl
    have : (0 : ℝ) ≤ count 1 := Nat.cast_nonneg _
    linarith
  set S₀ := (finite_le 1).toFinset with hS₀
  refine ⟨∑ i ∈ S₀, Real.log (1 + ‖i.1⁻¹‖), fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set h : ℝ → ℝ := fun x => Real.log (1 + y ^ 2 / x ^ 2) with hh
  have hpos : ∀ i : ZeroIdx (sqF Xi), 0 < 1 + y ^ 2 * ‖i.1⁻¹‖ := fun i => by positivity
  have hnn : ∀ i : ZeroIdx (sqF Xi), 0 ≤ Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) := fun i => Real.log_nonneg (by
    have := mul_nonneg (sq_nonneg y) (norm_nonneg i.1⁻¹)
    linarith)
  have hinv : ∀ i : ZeroIdx (sqF Xi), ‖i.1⁻¹‖ = (‖tau i‖ ^ 2)⁻¹ := fun i => by rw [norm_inv, ← tau_sq, norm_pow]
  have hhanti : ∀ a b : ℝ, 0 < a → a ≤ b → h b ≤ h a := fun a b ha hab => by
    simp only [hh]
    refine Real.log_le_log (by positivity) ?_
    have : y ^ 2 / b ^ 2 ≤ y ^ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha.le hab 2)
    linarith
  have hh0 : ∀ x : ℝ, 0 ≤ h x := fun x => Real.log_nonneg (by
    have : 0 ≤ y ^ 2 / x ^ 2 := by positivity
    linarith)
  refine tsum_le_of_sum_le' (by
    have := Finset.sum_nonneg (s := S₀) fun i _ => Real.log_nonneg (by
      have := norm_nonneg i.1⁻¹; linarith : (1 : ℝ) ≤ 1 + ‖i.1⁻¹‖)
    have : 0 ≤ Real.log (1 + y ^ 2) := Real.log_nonneg (by nlinarith)
    positivity) fun F => ?_
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => ‖tau i‖ ≤ 1)]
  -- the zeros with `|τ| ≤ 1`
  have hlow : ∑ i ∈ F.filter (fun i => ‖tau i‖ ≤ 1), Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) ≤
      A * Real.log (1 + y ^ 2) + ∑ i ∈ S₀, Real.log (1 + ‖i.1⁻¹‖) := by
    have hsub : F.filter (fun i => ‖tau i‖ ≤ 1) ⊆ S₀ := fun i hi => by
      simp only [Finset.mem_filter] at hi
      simpa [hS₀] using hi.2
    calc ∑ i ∈ F.filter (fun i => ‖tau i‖ ≤ 1), Real.log (1 + y ^ 2 * ‖i.1⁻¹‖)
        ≤ ∑ i ∈ F.filter (fun i => ‖tau i‖ ≤ 1), (Real.log (1 + y ^ 2) + Real.log (1 + ‖i.1⁻¹‖)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.log_mul (by positivity) (by positivity)]
          refine Real.log_le_log (hpos i) ?_
          have := mul_nonneg (sq_nonneg y) (norm_nonneg i.1⁻¹)
          nlinarith [norm_nonneg i.1⁻¹, sq_nonneg y]
      _ = (F.filter (fun i => ‖tau i‖ ≤ 1)).card * Real.log (1 + y ^ 2) +
          ∑ i ∈ F.filter (fun i => ‖tau i‖ ≤ 1), Real.log (1 + ‖i.1⁻¹‖) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ A * Real.log (1 + y ^ 2) + ∑ i ∈ S₀, Real.log (1 + ‖i.1⁻¹‖) := by
          gcongr
          · exact Real.log_nonneg (by nlinarith)
          · have h1 := card_le_count (T := 1) (F.filter (fun i => ‖tau i‖ ≤ 1)) fun i hi =>
              (Finset.mem_filter.1 hi).2
            have h2 := hA 1 le_rfl
            have : ((F.filter (fun i => ‖tau i‖ ≤ 1)).card : ℝ) ≤ count 1 := by exact_mod_cast h1
            linarith
          · exact fun i _ _ => Real.log_nonneg (by have := norm_nonneg i.1⁻¹; linarith)
  -- the zeros with `|τ| > 1`
  set F₁ := F.filter (fun i => ¬ ‖tau i‖ ≤ 1) with hF₁
  set M : ℕ := ⌈∑ i ∈ F₁, ‖tau i‖ + y⌉₊ + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have htM : ∀ i ∈ F₁, ‖tau i‖ < M := fun i hi => by
    have h1 := Finset.single_le_sum (f := fun i => ‖tau i‖) (fun i _ => norm_nonneg _) hi
    have h2 := Nat.le_ceil (∑ i ∈ F₁, ‖tau i‖ + y)
    push_cast [hM]
    linarith
  have hyM : y ≤ M := by
    have h1 := Finset.sum_nonneg (s := F₁) fun i _ => norm_nonneg (tau i)
    have h2 := Nat.le_ceil (∑ i ∈ F₁, ‖tau i‖ + y)
    push_cast [hM]
    linarith
  have hhigh : ∑ i ∈ F₁, Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) ≤ A * (Real.log (1 + y ^ 2) + (5 * y + 2)) := by
    set k : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊‖tau i‖⌋₊ with hk
    have hk1 : ∀ i ∈ F₁, 1 ≤ k i := fun i hi => by
      have : 1 < ‖tau i‖ := not_le.1 (Finset.mem_filter.1 hi).2
      exact Nat.le_floor (by exact_mod_cast this.le)
    have hkM : ∀ i ∈ F₁, k i ≤ M := fun i hi => by
      have h1 := Nat.floor_le (norm_nonneg (tau i))
      have h2 := htM i hi
      have : (k i : ℝ) < M := lt_of_le_of_lt h1 h2
      exact_mod_cast this.le
    -- each term is at most `h(⌊|τ|⌋)`, which telescopes
    have hterm : ∀ i ∈ F₁, Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) ≤
        ∑ j ∈ Ico 1 M, (if k i ≤ j then h j - h (j + 1) else 0) + h M := by
      intro i hi
      have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
      have e1 : Real.log (1 + y ^ 2 * ‖i.1⁻¹‖) = h ‖tau i‖ := by
        simp only [hh]
        rw [hinv i, div_eq_mul_inv]
      rw [e1]
      calc h ‖tau i‖ ≤ h (k i) := hhanti _ _ hk0 (Nat.floor_le (norm_nonneg _))
        _ = ∑ j ∈ Ico (k i) M, (h j - h ((j : ℝ) + 1)) + h M := by
            rw [telescope h (hkM i hi)]
            ring
        _ = ∑ j ∈ Ico 1 M, (if k i ≤ j then h j - h (j + 1) else 0) + h M := by
            rw [← Finset.sum_filter]
            congr 2
            ext j
            simp only [Finset.mem_Ico, Finset.mem_filter]
            have := hk1 i hi
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
            · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    have hd0 : ∀ j ∈ Ico 1 M, 0 ≤ h j - h (j + 1) := fun j hj => by
      have hj : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Ico.1 hj).1
      have := hhanti j (j + 1) hj (by linarith)
      linarith
    calc ∑ i ∈ F₁, Real.log (1 + y ^ 2 * ‖i.1⁻¹‖)
        ≤ ∑ i ∈ F₁, (∑ j ∈ Ico 1 M, (if k i ≤ j then h j - h (j + 1) else 0) + h M) :=
          Finset.sum_le_sum hterm
      _ = ∑ j ∈ Ico 1 M, ((F₁.filter (fun i => k i ≤ j)).card : ℝ) * (h j - h (j + 1)) + F₁.card * h M := by
          rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Ico 1 M, (A * ((j : ℝ) + 1)) * (h j - h (j + 1)) + (A * M) * h M := by
          gcongr with j hj
          · exact hd0 j hj
          · have h1 := card_le_count (T := (j : ℝ) + 1) (F₁.filter (fun i => k i ≤ j)) fun i hi => by
              have hkj : k i ≤ j := (Finset.mem_filter.1 hi).2
              have := Nat.lt_floor_add_one ‖tau i‖
              have : (k i : ℝ) ≤ j := by exact_mod_cast hkj
              linarith
            have h2 := hA ((j : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
            have : ((F₁.filter (fun i => k i ≤ j)).card : ℝ) ≤ count ((j : ℝ) + 1) := by exact_mod_cast h1
            linarith
          · exact hh0 _
          · have h1 := card_le_count (T := (M : ℝ)) F₁ fun i hi => (htM i hi).le
            have h2 := hA M (by exact_mod_cast hM1)
            have : (F₁.card : ℝ) ≤ count M := by exact_mod_cast h1
            linarith
      _ = A * (∑ j ∈ Ico 1 M, (h j - h ((j : ℝ) + 1)) * ((j : ℝ) + 1) + M * h M) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun j _ => by ring
          · ring
      _ = A * (h 1 + ∑ j ∈ Ico 1 M, h j) := by rw [abel h hM1]
      _ ≤ A * (Real.log (1 + y ^ 2) + (5 * y + 2)) := by
          gcongr
          · simp [hh]
          · exact sum_log_nat_le hy M
  linarith

/-! ## The zeros are denser than any linear rate -/

lemma xi_eq_Xi (m : ℕ) : xi ((2 * m + 2 : ℕ) : ℂ) = Xi (-I * ((2 * m + 3 / 2 : ℝ) : ℂ)) := by
  unfold Xi
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The zeros of `ζ` are not `O(T)`**: no `A` has `N(T) ≤ A·T` for every `T ≥ 1`. -/
theorem not_linear : ¬ ∃ A : ℝ, ∀ T : ℝ, 1 ≤ T → (count T : ℝ) ≤ A * T := by
  rintro ⟨A, hA⟩
  have hA0 : 0 ≤ A := by
    have h := hA 1 le_rfl
    have : (0 : ℝ) ≤ count 1 := Nat.cast_nonneg _
    linarith
  obtain ⟨C, hC⟩ := sum_log_le hA
  have hX0 := norm_pos_iff.2 Xi_zero_ne_zero
  -- at `y = 2m + 3/2`: `log m! − (m + 1)log π ≤ log ‖Ξ(0)‖ + 18A(m + 1) + C`
  have key : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * Real.log m - m - (m + 1) * Real.log Real.pi ≤
      Real.log ‖Xi 0‖ + 18 * A * (m + 1) + C := by
    intro m hm
    set y : ℝ := 2 * m + 3 / 2 with hy
    have hy1 : 1 ≤ y := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    have h1 := ZerosInfinite.norm_xi_ge m
    rw [xi_eq_Xi] at h1
    have h2 := norm_Xi_le (-I * ((2 * m + 3 / 2 : ℝ) : ℂ))
    have hnz : ‖-I * ((2 * m + 3 / 2 : ℝ) : ℂ)‖ = y := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnz] at h2
    have h3 := hC y hy1
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hpi : 0 < Real.pi ^ (m + 1) := by positivity
    have h4 : (m.factorial : ℝ) / Real.pi ^ (m + 1) ≤
        ‖Xi 0‖ * Real.exp (A * (5 * y + 2 + 2 * Real.log (1 + y ^ 2)) + C) :=
      h1.trans (h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hX0.le))
    have h5 := Real.log_le_log (by positivity) h4
    rw [Real.log_div hf.ne' hpi.ne', Real.log_pow, Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp] at h5
    have h6 := log_factorial_ge m
    have h7 : Real.log (1 + y ^ 2) ≤ 4 * m + 4 := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : 1 + y ^ 2 ≤ (2 * m + 3) ^ 2 := by rw [hy]; nlinarith
      calc Real.log (1 + y ^ 2) ≤ Real.log ((2 * m + 3) ^ 2) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log (2 * m + 3) := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 2 * ((2 * m + 3) - 1) := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * m + 3 by positivity)
            linarith
        _ = 4 * m + 4 := by ring
    have h8 : A * (5 * y + 2 + 2 * Real.log (1 + y ^ 2)) ≤ 18 * A * (m + 1) := by
      have : 5 * y + 2 + 2 * Real.log (1 + y ^ 2) ≤ 18 * (m + 1) := by rw [hy]; linarith
      nlinarith
    push_cast at h5
    linarith
  -- but `m log m` outgrows `m(1 + log π + 18A)`
  set K₁ : ℝ := 1 + Real.log Real.pi + 18 * A with hK₁
  set K₂ : ℝ := Real.log Real.pi + Real.log ‖Xi 0‖ + 18 * A + C with hK₂
  set m : ℕ := ⌈Real.exp (K₁ + 1) + |K₂| + 1⌉₊ with hm
  have hm1 : Real.exp (K₁ + 1) + |K₂| + 1 ≤ m := Nat.le_ceil _
  have hm0 : (0 : ℝ) < m := by have := Real.exp_pos (K₁ + 1); have := abs_nonneg K₂; linarith
  have hm1' : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by have := Real.exp_pos (K₁ + 1); linarith [abs_nonneg K₂])
  have hlog : K₁ + 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]
    linarith [abs_nonneg K₂]
  have hK2 : K₂ < m := by linarith [le_abs_self K₂, Real.exp_pos (K₁ + 1)]
  have h := key m hm1'
  have : (m : ℝ) * (K₁ + 1) ≤ m * Real.log m := mul_le_mul_of_nonneg_left hlog hm0.le
  nlinarith

end ZerosDense

#print axioms ZerosDense.not_linear
