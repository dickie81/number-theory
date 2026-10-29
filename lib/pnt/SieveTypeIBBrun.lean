/-
# Brun's weights for the leaves of the bilinear estimate

Plain statements. Sift by finite sets `T_j` of primes, `j` in a finite type `ι`, pairwise disjoint, truncated at even
levels `k_j ≥ 1`. The sifted indicator is `R(n) = ∏_j ∏_{p∈T_j} (1 − 1[p ∣ n])`. The weights above are indexed by
`σ ∈ Π_j Ftr(T_j, k_j)` (`wS₁`): `σ_j = (i, s)` with `s ⊆ T_j` of size `i ≤ k_j`, coefficient `λ_σ = ∏_j (−1)^{i_j}`
(`wl₁`) and modulus `f_σ = ∏_j ∏_{p∈s_j} p` (`wf`). The weights below (`wS₂`) are these, tagged `none`, and for each
`j` the indices tagged `some j` with `σ_j ∈ Fes(T_j, k_j)` (`|s_j| = k_j`), coefficient `−∏_{i≠j} (−1)^{i_i}` (`wl₂`).

* `sum_wS₁`, `sum_wS₂`: for any `y`, `Σ_σ λ_σ ∏_j ∏_{p∈s_j} y_p = ∏_j F_{k_j}(T_j, y)` and the weights below give
  `∏_j F_{k_j}(T_j, y) − Σ_j e_{k_j}(T_j, y) ∏_{i≠j} F_{k_i}(T_i, y)` (`SieveBrun.trunc`, `SieveBrun.esym`).
* `R_le`, `le_R`: `R ≤ Σ_σ λ_σ 1[f_σ ∣ ·]` and `Σ_τ λ_τ 1[f_τ ∣ ·] ≤ R`, by Bonferroni (`SieveBrun.bonferroni`) and
  `SieveBrun.prod_lower`.
* `gap_eq`: the sieve's gap `Γ` of `SieveTypeIBLeaf.errL` is `Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)` with
  `g(p) = 1[(p, q) = 1]/p`.

The file imports `SieveTypeIBLeaf.lean`; `SieveBrun.lean` comes with it through `SieveSpline.lean`'s imports, or
directly.
-/
import SieveTypeIBLeaf
import SieveBrun

open Finset

namespace SieveTypeIBBrun

open SieveBrun SieveTypeIBLeaf

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An index: a choice `σ_j = (i, s)` for each range. -/
abbrev Idx (ι : Type*) := ι → (Σ _ : ℕ, Finset ℕ)

/-- The weights above: `σ ∈ Π_j Ftr(T_j, k_j)`. -/
def wS₁ (T : ι → Finset ℕ) (k : ι → ℕ) : Finset (Idx ι) := Fintype.piFinset fun j => Ftr (T j) (k j)

/-- Their coefficient `λ_σ = ∏_j (−1)^{i_j}`. -/
def wl₁ (σ : Idx ι) : ℝ := ∏ j, (-1 : ℝ) ^ (σ j).1

/-- The modulus `f_σ = ∏_j ∏_{p∈s_j} p`. -/
def wf (σ : Idx ι) : ℕ := ∏ j, ∏ p ∈ (σ j).2, p

/-- The choices with `σ_j ∈ Fes(T_j, k_j)` at `j` and `σ_i ∈ Ftr(T_i, k_i)` elsewhere. -/
def corr (T : ι → Finset ℕ) (k : ι → ℕ) (j : ι) : Finset (Idx ι) :=
  Fintype.piFinset (Function.update (fun i => Ftr (T i) (k i)) j (Fes (T j) (k j)))

/-- The tag `none`. -/
def embN : Idx ι ↪ Option ι × Idx ι := ⟨fun σ => (none, σ), fun _ _ h => (Prod.mk.inj h).2⟩

/-- The tag `some j`. -/
def embS (j : ι) : Idx ι ↪ Option ι × Idx ι := ⟨fun σ => (some j, σ), fun _ _ h => (Prod.mk.inj h).2⟩

/-- The weights below: `(none, σ)` with `σ ∈ wS₁`, and `(some j, σ)` with `σ ∈ corr j`. -/
def wS₂ (T : ι → Finset ℕ) (k : ι → ℕ) : Finset (Option ι × Idx ι) :=
  (wS₁ T k).map embN ∪ univ.biUnion fun j => (corr T k j).map (embS j)

/-- Their coefficient: `λ_σ` for `(none, σ)`, and `−∏_{i≠j} (−1)^{i_i}` for `(some j, σ)`. -/
def wl₂ : Option ι × Idx ι → ℝ
  | (none, σ) => wl₁ σ
  | (some j, σ) => -∏ i ∈ univ.erase j, (-1 : ℝ) ^ (σ i).1

/-- Their modulus `f_σ`. -/
def wf₂ (x : Option ι × Idx ι) : ℕ := wf x.2

/-! ### The weights' expansions -/

/-- **The weights above**: `Σ_σ λ_σ ∏_j ∏_{p∈s_j} y_p = ∏_j F_{k_j}(T_j, y)`. -/
theorem sum_wS₁ (T : ι → Finset ℕ) (k : ι → ℕ) (y : ℕ → ℝ) :
    ∑ σ ∈ wS₁ T k, wl₁ σ * ∏ j, ∏ p ∈ (σ j).2, y p = ∏ j, trunc (T j) y (k j) := by
  simp_rw [trunc_eq_weight]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [wl₁, Finset.prod_mul_distrib]

/-- One correction: `Σ_{σ∈corr j} ∏_{i≠j} (−1)^{i_i} ∏_i ∏_{p∈s_i} y_p = e_{k_j}(T_j, y) ∏_{i≠j} F_{k_i}(T_i, y)`. -/
theorem sum_corr (T : ι → Finset ℕ) (k : ι → ℕ) (y : ℕ → ℝ) (j : ι) :
    ∑ σ ∈ corr T k j, (∏ i ∈ univ.erase j, (-1 : ℝ) ^ (σ i).1) * ∏ i, ∏ p ∈ (σ i).2, y p =
      esym (T j) y (k j) * ∏ i ∈ univ.erase j, trunc (T i) y (k i) := by
  set t : ι → Finset (Σ _ : ℕ, Finset ℕ) := Function.update (fun i => Ftr (T i) (k i)) j (Fes (T j) (k j)) with ht
  set g : ι → (Σ _ : ℕ, Finset ℕ) → ℝ := fun i b => (if i = j then 1 else (-1 : ℝ) ^ b.1) * ∏ p ∈ b.2, y p with hg
  have h1 : ∏ i, ∑ b ∈ t i, g i b = ∑ σ ∈ corr T k j, ∏ i, g i (σ i) := by
    rw [Finset.prod_univ_sum]; rfl
  have h2 : ∀ σ : Idx ι, ∏ i, g i (σ i) = (∏ i ∈ univ.erase j, (-1 : ℝ) ^ (σ i).1) * ∏ i, ∏ p ∈ (σ i).2, y p := by
    intro σ
    rw [hg, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.mul_prod_erase univ _ (mem_univ j), ite_eq_left rfl, one_mul]
    exact Finset.prod_congr rfl fun i hi => by rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
  have h3 : ∏ i, ∑ b ∈ t i, g i b = esym (T j) y (k j) * ∏ i ∈ univ.erase j, trunc (T i) y (k i) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    congr 1
    · rw [ht, Function.update_self, esym_eq_weight]
      exact Finset.sum_congr rfl fun b _ => by simp [hg]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hij := Finset.ne_of_mem_erase hi
      rw [ht, Function.update_of_ne hij, trunc_eq_weight]
      exact Finset.sum_congr rfl fun b _ => by simp [hg, hij]
  rw [← h3, h1]
  exact (Finset.sum_congr rfl fun σ _ => h2 σ).symm

/-- **The weights below**: `Σ_x λ_x ∏_j ∏_{p∈s_j} y_p` is
`∏_j F_{k_j}(T_j, y) − Σ_j e_{k_j}(T_j, y) ∏_{i≠j} F_{k_i}(T_i, y)`. -/
theorem sum_wS₂ (T : ι → Finset ℕ) (k : ι → ℕ) (y : ℕ → ℝ) :
    ∑ x ∈ wS₂ T k, wl₂ x * ∏ j, ∏ p ∈ (x.2 j).2, y p =
      ∏ j, trunc (T j) y (k j) - ∑ j, esym (T j) y (k j) * ∏ i ∈ univ.erase j, trunc (T i) y (k i) := by
  have hdisj : Disjoint ((wS₁ T k).map embN) (univ.biUnion fun j => (corr T k j).map (embS j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_map] at hx
    rw [Finset.mem_biUnion] at hx'
    obtain ⟨σ, -, rfl⟩ := hx
    obtain ⟨j, -, hj⟩ := hx'
    rw [Finset.mem_map] at hj
    obtain ⟨τ, -, h⟩ := hj
    exact Option.some_ne_none j (Prod.mk.inj h).1
  rw [wS₂, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_biUnion]
  · have hA : ∑ σ ∈ wS₁ T k, wl₂ (embN σ) * ∏ j, ∏ p ∈ ((embN σ).2 j).2, y p = ∏ j, trunc (T j) y (k j) := by
      rw [← sum_wS₁ T k y]
      rfl
    rw [hA, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_map, ← sum_corr T k y j, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    show wl₂ (some j, σ) * _ = _
    simp only [wl₂, neg_mul]
    rfl
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_map] at hx hx'
    obtain ⟨σ, -, rfl⟩ := hx
    obtain ⟨τ, -, h⟩ := hx'
    exact hij (Option.some_injective _ (Prod.mk.inj h).1).symm

/-! ### The sifted indicator between the weights -/

/-- The sifted indicator `R(n) = ∏_j ∏_{p∈T_j} (1 − 1[p ∣ n])`. -/
noncomputable def Rs (T : ι → Finset ℕ) (n : ℕ) : ℝ := ∏ j, ∏ p ∈ T j, (1 - ind n p)

omit [DecidableEq ι] in
/-- For `s_j ⊆ T_j`, sets of primes pairwise disjoint, `∏_j ∏_{p∈s_j} 1[p ∣ n] = 1[∏_j ∏_{p∈s_j} p ∣ n]`. -/
theorem prod_ind_eq_dv (T : ι → Finset ℕ) (hT : ∀ j, ∀ p ∈ T j, p.Prime)
    (hdisj : (Set.univ : Set ι).PairwiseDisjoint T) (σ : Idx ι) (hσ : ∀ j, (σ j).2 ⊆ T j) (n : ℕ) :
    ∏ j, ∏ p ∈ (σ j).2, ind n p = dv (wf σ) n := by
  classical
  have hdisj' : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint (fun j => (σ j).2) := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left (hσ i) (Finset.disjoint_of_subset_right (hσ j)
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij))
  have e1 : ∏ j, ∏ p ∈ (σ j).2, ind n p = ∏ p ∈ univ.biUnion (fun j => (σ j).2), ind n p :=
    (Finset.prod_biUnion hdisj').symm
  have e2 : wf σ = ∏ p ∈ univ.biUnion (fun j => (σ j).2), p := by
    rw [wf, Finset.prod_biUnion hdisj']
  have hpr : ∀ p ∈ univ.biUnion (fun j => (σ j).2), p.Prime := by
    intro p hp
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
    exact hT j p (hσ j hj)
  rw [e1, e2, dv]
  unfold ind
  by_cases h : ∀ p ∈ univ.biUnion (fun j => (σ j).2), p ∣ n
  · rw [Finset.prod_boole, ite_eq_left h, ite_eq_left (Finset.prod_primes_dvd n (fun p hp => (hpr p hp).prime) h)]
  · rw [Finset.prod_boole, ite_eq_right h, ite_eq_right]
    intro hd
    exact h fun p hp => (Finset.dvd_prod_of_mem _ hp).trans hd

omit [Fintype ι] [DecidableEq ι] in
theorem ind_mem (n p : ℕ) : 0 ≤ ind n p ∧ ind n p ≤ 1 := ⟨ind_nonneg n p, ind_le_one n p⟩

/-- The weights above have their primes in the ranges. -/
theorem sub_of_mem_wS₁ {T : ι → Finset ℕ} {k : ι → ℕ} {σ : Idx ι} (hσ : σ ∈ wS₁ T k) : ∀ j, (σ j).2 ⊆ T j :=
  fun j => mem_Ftr_sub (Fintype.mem_piFinset.1 hσ j)

/-- The weights below have their primes in the ranges. -/
theorem sub_of_mem_wS₂ {T : ι → Finset ℕ} {k : ι → ℕ} {x : Option ι × Idx ι} (hx : x ∈ wS₂ T k) :
    ∀ j, (x.2 j).2 ⊆ T j := by
  rw [wS₂, Finset.mem_union] at hx
  rcases hx with hx | hx
  · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_map.1 hx
    exact sub_of_mem_wS₁ hσ
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_map.1 hi
    intro j
    have h := Fintype.mem_piFinset.1 hσ j
    by_cases hij : j = i
    · subst hij
      rw [Function.update_self] at h
      exact mem_Fes_sub h
    · rw [Function.update_of_ne hij] at h
      exact mem_Ftr_sub h

/-- **The weights above bound the sifted indicator**: `R(n) ≤ Σ_σ λ_σ1[f_σ ∣ n]`, for even levels `k_j ≥ 1`. -/
theorem R_le (T : ι → Finset ℕ) (k : ι → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j)
    (hT : ∀ j, ∀ p ∈ T j, p.Prime) (hdisj : (Set.univ : Set ι).PairwiseDisjoint T) (n : ℕ) :
    Rs T n ≤ ∑ σ ∈ wS₁ T k, wl₁ σ * dv (wf σ) n := by
  have e : ∑ σ ∈ wS₁ T k, wl₁ σ * dv (wf σ) n = ∏ j, trunc (T j) (ind n) (k j) := by
    rw [← sum_wS₁ T k (ind n)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [prod_ind_eq_dv T hT hdisj σ (sub_of_mem_wS₁ hσ) n]
  rw [e, Rs]
  have h0 : ∀ j ∈ (univ : Finset ι), 0 ≤ ∏ p ∈ T j, (1 - ind n p) := fun j _ =>
    Finset.prod_nonneg fun p _ => by have := ind_le_one n p; linarith
  exact Finset.prod_le_prod₀ h0 fun j _ =>
    (trunc_bounds (fun p _ => ind_nonneg n p) (fun p _ => ind_le_one n p) (hk j) (hk1 j)).2

/-- **The weights below are below the sifted indicator**: `Σ_x λ_x1[f_x ∣ n] ≤ R(n)`. -/
theorem le_R (T : ι → Finset ℕ) (k : ι → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j)
    (hT : ∀ j, ∀ p ∈ T j, p.Prime) (hdisj : (Set.univ : Set ι).PairwiseDisjoint T) (n : ℕ) :
    ∑ x ∈ wS₂ T k, wl₂ x * dv (wf₂ x) n ≤ Rs T n := by
  have e : ∑ x ∈ wS₂ T k, wl₂ x * dv (wf₂ x) n =
      ∏ j, trunc (T j) (ind n) (k j) -
        ∑ j, (trunc (T j) (ind n) (k j) - trunc (T j) (ind n) (k j - 1)) *
          ∏ i ∈ univ.erase j, trunc (T i) (ind n) (k i) := by
    have e1 : ∑ x ∈ wS₂ T k, wl₂ x * dv (wf₂ x) n = ∑ x ∈ wS₂ T k, wl₂ x * ∏ j, ∏ p ∈ (x.2 j).2, ind n p := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [wf₂, prod_ind_eq_dv T hT hdisj x.2 (sub_of_mem_wS₂ hx) n]
    rw [e1, sum_wS₂ T k (ind n)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [trunc_sub_pred (hk j) (hk1 j)]
  rw [e, Rs]
  refine prod_lower univ (fun j => ∏ p ∈ T j, (1 - ind n p)) (fun j => trunc (T j) (ind n) (k j - 1))
    (fun j => trunc (T j) (ind n) (k j)) (fun j _ => Finset.prod_nonneg fun p _ => by
      have := ind_le_one n p; linarith) (fun j _ => ?_) (fun j _ => ?_)
  · exact (trunc_bounds (fun p _ => ind_nonneg n p) (fun p _ => ind_le_one n p) (hk j) (hk1 j)).1
  · exact (trunc_bounds (fun p _ => ind_nonneg n p) (fun p _ => ind_le_one n p) (hk j) (hk1 j)).2

omit [Fintype ι] [DecidableEq ι] in
/-- `1[(·, q) = 1]` of a product. -/
theorem gU_prod (q : ℕ) {α : Type*} (s : Finset α) (f : α → ℕ) : gU q (∏ i ∈ s, f i) = ∏ i ∈ s, gU q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gU]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, gU_mul, ih]

omit [DecidableEq ι] in
/-- `1[(f_σ, q) = 1]/f_σ = ∏_j ∏_{p∈s_j} g(p)` with `g(p) = 1[(p, q) = 1]/p`. -/
theorem gU_wf (q : ℕ) (σ : Idx ι) :
    gU q (wf σ) / (wf σ : ℝ) = ∏ j, ∏ p ∈ (σ j).2, gU q p / (p : ℝ) := by
  rw [wf, gU_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [gU_prod, Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **The sieve's gap**: `Γ = Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)`, `g(p) = 1[(p, q) = 1]/p`. -/
theorem gap_eq (q : ℕ) (T : ι → Finset ℕ) (k : ι → ℕ) :
    ∑ σ ∈ wS₁ T k, wl₁ σ * gU q (wf σ) / (wf σ : ℝ) - ∑ x ∈ wS₂ T k, wl₂ x * gU q (wf₂ x) / (wf₂ x : ℝ) =
      ∑ j, esym (T j) (fun p => gU q p / (p : ℝ)) (k j) *
        ∏ i ∈ univ.erase j, trunc (T i) (fun p => gU q p / (p : ℝ)) (k i) := by
  have e1 : ∑ σ ∈ wS₁ T k, wl₁ σ * gU q (wf σ) / (wf σ : ℝ) =
      ∏ j, trunc (T j) (fun p => gU q p / (p : ℝ)) (k j) := by
    rw [← sum_wS₁ T k]
    exact Finset.sum_congr rfl fun σ _ => by rw [mul_div_assoc, gU_wf]
  have e2 : ∑ x ∈ wS₂ T k, wl₂ x * gU q (wf₂ x) / (wf₂ x : ℝ) =
      ∏ j, trunc (T j) (fun p => gU q p / (p : ℝ)) (k j) -
        ∑ j, esym (T j) (fun p => gU q p / (p : ℝ)) (k j) *
          ∏ i ∈ univ.erase j, trunc (T i) (fun p => gU q p / (p : ℝ)) (k i) := by
    rw [← sum_wS₂ T k]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_div_assoc, wf₂, gU_wf]
  rw [e1, e2]
  ring

end SieveTypeIBBrun
