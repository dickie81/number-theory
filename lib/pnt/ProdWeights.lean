import Mathlib

/-!
# Independent selections as weighted finite sums

A step of the proof of the sharp frontier (`SharpInputs`, the design's Stage 2): the probability model of the random
tops (`TopsSelect`), without measure theory. A subset `T` of a finite type `α` is drawn by including each `a`
independently with probability `q_a`; the weight of `T` is `pw q T = ∏_{a ∈ T} q_a·∏_{a ∉ T}(1 − q_a)` and the mean of
`F : Finset α → ℝ` is `pexp q F = Σ_T pw q T·F(T)`.

**The facts.**
* The weights sum to `1` (`sum_pw`) and are nonnegative for probabilities (`pw_nonneg`); `pexp` is linear and monotone
  (`pexp_add`, `pexp_const_mul`, `pexp_sum`, `pexp_const`, `pexp_mono`).
* **Coordinate products** (`pexp_coord`): `pexp(∏_a [a ∈ T ? f_a : g_a]) = ∏_a (q_a f_a + (1 − q_a)g_a)`, by
  `Finset.prod_add` over `univ`. Hence the moments `P(U ⊆ T) = ∏_U q` (`pexp_subset`), the law of `T ∩ S`
  (`pexp_inter_eq`: `P(T ∩ S = U) = ∏_U q·∏_{S∖U}(1 − q)`) and the variance of a count (`pexp_var`:
  `E[(Σ_{a ∈ C}(1_{a ∈ T} − q_a))²] = Σ_C q_a(1 − q_a)`).
* **Independence over disjoint supports** (`pexp_mul_local`, `pexp_prod_local`): a function that reads only `T ∩ S`
  (`IsLocal`) is the combination `Σ_{U ⊆ S} F(U)·[T ∩ S = U]` of coordinate products supported on `S`
  (`local_eq_sum`), and coordinate products with disjoint supports multiply.
* **Selection** (`exists_le_two_mul`): two nonnegative functionals with means at most `c₁, c₂ > 0` are at most
  `2c₁, 2c₂` at one `T` (a minimiser of `F₁/2c₁ + F₂/2c₂` is at most its mean `≤ 1`).
* **Tails**: `1[|T ∩ W| ≥ N]` is at most the number of `N`-subsets of `W` inside `T` (`ind_le_sum_powersetCard`), so a
  forced point and a full window have `P(t ∈ T, |T ∩ W| ≥ N) ≤ δ(C(|W|, N−1)δ^{N−1} + C(|W|, N)δ^N)` for `q ≤ δ ≤ 1`
  (`pexp_forced_window_le`); and `C(G, N)δ^N ≤ (eGδ/N)^N` (`choose_mul_pow_le`).
-/

open Finset

namespace ZetaBalance

namespace ProdWeights

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of `T` under independent inclusion with probabilities `q`. -/
def pw (q : α → ℝ) (T : Finset α) : ℝ := (∏ a ∈ T, q a) * ∏ a ∈ Tᶜ, (1 - q a)

/-- The expectation of `F`. -/
def pexp (q : α → ℝ) (F : Finset α → ℝ) : ℝ := ∑ T : Finset α, pw q T * F T

/-- `q` is a vector of probabilities. -/
def IsProb (q : α → ℝ) : Prop := ∀ a, 0 ≤ q a ∧ q a ≤ 1

/-- `F` reads only `T ∩ S`. -/
def IsLocal (S : Finset α) (F : Finset α → ℝ) : Prop := ∀ T, F T = F (T ∩ S)

variable (q : α → ℝ)

/-! ## Linearity and coordinate products -/

/-- `pexp` is additive. -/
theorem pexp_add (F G : Finset α → ℝ) : pexp q (fun T => F T + G T) = pexp q F + pexp q G := by
  simp only [pexp, mul_add, sum_add_distrib]

/-- `pexp` is homogeneous. -/
theorem pexp_const_mul (c : ℝ) (F : Finset α → ℝ) : pexp q (fun T => c * F T) = c * pexp q F := by
  simp only [pexp, mul_sum]
  exact sum_congr rfl fun T _ => by ring

/-- `pexp` commutes with finite sums. -/
theorem pexp_sum {ι : Type*} (s : Finset ι) (F : ι → Finset α → ℝ) :
    pexp q (fun T => ∑ i ∈ s, F i T) = ∑ i ∈ s, pexp q (F i) := by
  simp only [pexp, mul_sum]
  exact sum_comm

/-- **Coordinate products** (`Finset.prod_add` over `univ`). -/
theorem pexp_coord (f g : α → ℝ) :
    pexp q (fun T => ∏ a, if a ∈ T then f a else g a) = ∏ a, (q a * f a + (1 - q a) * g a) := by
  rw [prod_add, powerset_univ, pexp]
  refine sum_congr rfl fun T _ => ?_
  have h1 : ∏ a ∈ T, (if a ∈ T then f a else g a) = ∏ a ∈ T, f a := prod_congr rfl fun a ha => ite_eq_left ha
  have h2 : ∏ a ∈ Tᶜ, (if a ∈ T then f a else g a) = ∏ a ∈ Tᶜ, g a :=
    prod_congr rfl fun a ha => ite_eq_right (mem_compl.1 ha)
  rw [← compl_eq_univ_sdiff, pw, ← prod_mul_prod_compl T (fun a => if a ∈ T then f a else g a), h1, h2,
    prod_mul_distrib, prod_mul_distrib]
  ring

/-- **The weights sum to `1`**: the coordinate product of `f = g = 1`. -/
theorem sum_pw : ∑ T : Finset α, pw q T = 1 := by
  have h := pexp_coord q (fun _ => 1) (fun _ => 1)
  simp only [ite_self, prod_const_one, mul_one] at h
  have e : ∏ a, (q a + (1 - q a)) = 1 := prod_eq_one fun a _ => by ring
  rw [e] at h
  simpa [pexp] using h

/-- **The weights are nonnegative** for probabilities. -/
theorem pw_nonneg {q : α → ℝ} (hq : IsProb q) (T : Finset α) : 0 ≤ pw q T :=
  mul_nonneg (prod_nonneg fun a _ => (hq a).1) (prod_nonneg fun a _ => sub_nonneg.2 (hq a).2)

/-- The mean of a constant. -/
theorem pexp_const (c : ℝ) : pexp q (fun _ => c) = c := by
  rw [pexp, ← sum_mul, sum_pw, one_mul]

/-- `pexp` is monotone for probabilities. -/
theorem pexp_mono {q : α → ℝ} (hq : IsProb q) {F G : Finset α → ℝ} (h : ∀ T, F T ≤ G T) :
    pexp q F ≤ pexp q G :=
  sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (h T) (pw_nonneg hq T)

/-- **Moments**: `P(U ⊆ T) = ∏_{a ∈ U} q_a`. -/
theorem pexp_subset (U : Finset α) : pexp q (fun T => if U ⊆ T then 1 else 0) = ∏ a ∈ U, q a := by
  have hF : (fun T : Finset α => if U ⊆ T then (1 : ℝ) else 0) =
      fun T => ∏ a, if a ∈ T then (1 : ℝ) else if a ∈ U then 0 else 1 := by
    funext T
    by_cases h : U ⊆ T
    · rw [ite_eq_left h]
      refine (prod_eq_one fun a _ => ?_).symm
      by_cases ha : a ∈ T
      · rw [ite_eq_left ha]
      · rw [ite_eq_right ha, ite_eq_right fun hu => ha (h hu)]
    · obtain ⟨a, haU, haT⟩ := not_subset.1 h
      rw [ite_eq_right h]
      exact (prod_eq_zero (mem_univ a) (by rw [ite_eq_right haT, ite_eq_left haU])).symm
  have e : ∏ a ∈ U, q a = ∏ a, if a ∈ U then q a else 1 := by rw [prod_ite_mem, univ_inter]
  rw [hF, pexp_coord, e]
  refine prod_congr rfl fun a _ => ?_
  split_ifs <;> ring

/-- The mean of an indicator, `P(a ∈ T) = q_a`. -/
theorem pexp_ind (a : α) : pexp q (fun T => if a ∈ T then 1 else 0) = q a := by
  have h := pexp_subset q {a}
  simp only [singleton_subset_iff, prod_singleton] at h
  exact h

/-- `P(a, b ∈ T) = q_a q_b` for `a ≠ b`. -/
theorem pexp_ind_mul {a b : α} (hab : a ≠ b) :
    pexp q (fun T => (if a ∈ T then 1 else 0) * (if b ∈ T then 1 else 0)) = q a * q b := by
  have h := pexp_subset q {a, b}
  rw [prod_pair hab] at h
  rw [← h]
  congr 1
  funext T
  simp only [insert_subset_iff, singleton_subset_iff]
  split_ifs <;> simp_all

/-- `E[(1_a − q_a)²] = q_a(1 − q_a)`. -/
theorem pexp_cov_self (a : α) :
    pexp q (fun T => ((if a ∈ T then 1 else 0) - q a) * ((if a ∈ T then 1 else 0) - q a)) = q a * (1 - q a) := by
  have e : (fun T : Finset α => ((if a ∈ T then (1 : ℝ) else 0) - q a) * ((if a ∈ T then 1 else 0) - q a)) =
      fun T => (1 - 2 * q a) * (if a ∈ T then 1 else 0) + q a ^ 2 := by
    funext T
    split_ifs <;> ring
  rw [e, pexp_add, pexp_const_mul, pexp_ind, pexp_const]
  ring

/-- `E[(1_a − q_a)(1_b − q_b)] = 0` for `a ≠ b`. -/
theorem pexp_cov_ne {a b : α} (hab : a ≠ b) :
    pexp q (fun T => ((if a ∈ T then 1 else 0) - q a) * ((if b ∈ T then 1 else 0) - q b)) = 0 := by
  have e : (fun T : Finset α => ((if a ∈ T then (1 : ℝ) else 0) - q a) * ((if b ∈ T then 1 else 0) - q b)) =
      fun T => (if a ∈ T then 1 else 0) * (if b ∈ T then 1 else 0) +
        ((-q b) * (if a ∈ T then 1 else 0) + ((-q a) * (if b ∈ T then 1 else 0) + q a * q b)) := by
    funext T
    ring
  rw [e, pexp_add, pexp_add, pexp_add, pexp_const_mul, pexp_const_mul, pexp_ind_mul q hab, pexp_ind, pexp_ind,
    pexp_const]
  ring

/-- **The variance of a count**: `E[(Σ_{a ∈ C} (1_{a ∈ T} − q_a))²] = Σ_{a ∈ C} q_a(1 − q_a)`. -/
theorem pexp_var (C : Finset α) :
    pexp q (fun T => (∑ a ∈ C, ((if a ∈ T then 1 else 0) - q a)) ^ 2) = ∑ a ∈ C, q a * (1 - q a) := by
  have e : (fun T : Finset α => (∑ a ∈ C, ((if a ∈ T then (1 : ℝ) else 0) - q a)) ^ 2) =
      fun T => ∑ a ∈ C, ∑ b ∈ C, ((if a ∈ T then (1 : ℝ) else 0) - q a) * ((if b ∈ T then 1 else 0) - q b) := by
    funext T
    rw [sq, sum_mul_sum]
  rw [e, pexp_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [pexp_sum, sum_eq_single a (fun b _ hb => pexp_cov_ne q (Ne.symm hb)) (fun h => absurd ha h),
    pexp_cov_self]

/-! ## The law of `T ∩ S` and independence -/

/-- The factor at `a` of the indicator `[T ∩ S = U]` when `a ∈ T`. -/
def cpf (S U : Finset α) (a : α) : ℝ := if a ∈ S then (if a ∈ U then 1 else 0) else 1

/-- The factor at `a` of the indicator `[T ∩ S = U]` when `a ∉ T`. -/
def cpg (S U : Finset α) (a : α) : ℝ := if a ∈ S then (if a ∈ U then 0 else 1) else 1

/-- **`[T ∩ S = U]` is a coordinate product** for `U ⊆ S`. -/
theorem prod_cp {S U : Finset α} (hU : U ⊆ S) (T : Finset α) :
    ∏ a, (if a ∈ T then cpf S U a else cpg S U a) = if T ∩ S = U then 1 else 0 := by
  split_ifs with h
  · refine prod_eq_one fun a _ => ?_
    by_cases haS : a ∈ S
    · by_cases haT : a ∈ T
      · have : a ∈ U := h ▸ mem_inter.2 ⟨haT, haS⟩
        simp [cpf, haT, haS, this]
      · have : a ∉ U := fun hu => haT (mem_inter.1 (by rw [h]; exact hu : a ∈ T ∩ S)).1
        simp [cpg, haT, haS, this]
    · simp [cpf, cpg, haS]
  · obtain ⟨a, ha⟩ : ∃ a, ¬ (a ∈ T ∩ S ↔ a ∈ U) := by
      by_contra hc
      push Not at hc
      exact h (ext hc)
    refine prod_eq_zero (mem_univ a) ?_
    by_cases haU : a ∈ U
    · have haS := hU haU
      have haT : a ∉ T := fun haT => ha ⟨fun _ => haU, fun _ => mem_inter.2 ⟨haT, haS⟩⟩
      simp [cpg, haT, haS, haU]
    · have h1 : a ∈ T ∩ S := by
        by_contra h2
        exact ha ⟨fun h3 => absurd h3 h2, fun h3 => absurd h3 haU⟩
      obtain ⟨haT, haS⟩ := mem_inter.1 h1
      simp [cpf, haT, haS, haU]

/-- **The law of `T ∩ S`**: `P(T ∩ S = U) = ∏_{a ∈ U} q_a·∏_{a ∈ S ∖ U}(1 − q_a)` for `U ⊆ S`. -/
theorem pexp_inter_eq {S U : Finset α} (hU : U ⊆ S) :
    pexp q (fun T => if T ∩ S = U then 1 else 0) = (∏ a ∈ U, q a) * ∏ a ∈ S \ U, (1 - q a) := by
  rw [show (fun T : Finset α => if T ∩ S = U then (1 : ℝ) else 0) =
      fun T => ∏ a, if a ∈ T then cpf S U a else cpg S U a from funext fun T => (prod_cp hU T).symm,
    pexp_coord]
  have h : ∀ a, q a * cpf S U a + (1 - q a) * cpg S U a =
      (if a ∈ U then q a else 1) * (if a ∈ S \ U then 1 - q a else 1) := by
    intro a
    by_cases haS : a ∈ S
    · by_cases haU : a ∈ U
      · simp [cpf, cpg, haS, haU]
      · simp [cpf, cpg, haS, haU]
    · have haU : a ∉ U := fun h => haS (hU h)
      simp only [cpf, cpg, haS, haU, ite_false, mem_sdiff, false_and]
      ring
  rw [prod_congr rfl fun a _ => h a, prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter]

/-- **A local function as a combination of coordinate products**: `F(T) = Σ_{U ⊆ S} F(U)·[T ∩ S = U]`. -/
theorem local_eq_sum {S : Finset α} {F : Finset α → ℝ} (hF : IsLocal S F) (T : Finset α) :
    F T = ∑ U ∈ S.powerset, F U * ∏ a, (if a ∈ T then cpf S U a else cpg S U a) := by
  have h : ∀ U ∈ S.powerset, F U * ∏ a, (if a ∈ T then cpf S U a else cpg S U a) =
      if T ∩ S = U then F U else 0 := by
    intro U hU
    rw [prod_cp (mem_powerset.1 hU)]
    split_ifs <;> simp
  rw [sum_congr rfl h, sum_ite_eq, ite_eq_left (mem_powerset.2 inter_subset_right)]
  exact hF T

/-- **The mean of a local function** through its coordinate products. -/
theorem pexp_local {S : Finset α} {F : Finset α → ℝ} (hF : IsLocal S F) :
    pexp q F = ∑ U ∈ S.powerset, F U * ∏ a, (q a * cpf S U a + (1 - q a) * cpg S U a) := by
  have e : F = fun T => ∑ U ∈ S.powerset, F U * ∏ a, (if a ∈ T then cpf S U a else cpg S U a) :=
    funext (local_eq_sum hF)
  conv_lhs => rw [e]
  rw [pexp_sum]
  exact sum_congr rfl fun U _ => by rw [pexp_const_mul, pexp_coord]

/-- **Independence of two local functions with disjoint supports**: `E[FG] = E[F]·E[G]`. Coordinate products
supported on disjoint sets multiply, factor by factor. -/
theorem pexp_mul_local {S S' : Finset α} (hd : Disjoint S S') {F G : Finset α → ℝ} (hF : IsLocal S F)
    (hG : IsLocal S' G) : pexp q (fun T => F T * G T) = pexp q F * pexp q G := by
  have e : (fun T => F T * G T) = fun T => ∑ U ∈ S.powerset, ∑ V ∈ S'.powerset,
      (F U * G V) * ∏ a, (if a ∈ T then cpf S U a * cpf S' V a else cpg S U a * cpg S' V a) := by
    funext T
    rw [local_eq_sum hF T, local_eq_sum hG T, sum_mul_sum]
    refine sum_congr rfl fun U _ => sum_congr rfl fun V _ => ?_
    rw [mul_mul_mul_comm, ← prod_mul_distrib]
    congr 1
    exact prod_congr rfl fun a _ => by split_ifs <;> rfl
  rw [e, pexp_sum, pexp_local q hF, pexp_local q hG, sum_mul_sum]
  refine sum_congr rfl fun U _ => ?_
  rw [pexp_sum]
  refine sum_congr rfl fun V _ => ?_
  rw [pexp_const_mul, pexp_coord, mul_mul_mul_comm, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun a _ => ?_
  by_cases haS : a ∈ S
  · have haS' : a ∉ S' := disjoint_left.1 hd haS
    rw [show cpf S' V a = 1 by simp [cpf, haS'], show cpg S' V a = 1 by simp [cpg, haS']]
    ring
  · rw [show cpf S U a = 1 by simp [cpf, haS], show cpg S U a = 1 by simp [cpg, haS]]
    ring

omit [Fintype α] in
/-- **A product of local functions is local** to the union of their supports. -/
theorem IsLocal.prod {ι : Type*} [DecidableEq ι] (I : Finset ι) (S : ι → Finset α) (F : ι → Finset α → ℝ)
    (hF : ∀ i ∈ I, IsLocal (S i) (F i)) : IsLocal (I.biUnion S) (fun T => ∏ i ∈ I, F i T) := fun T => by
  show ∏ i ∈ I, F i T = ∏ i ∈ I, F i (T ∩ I.biUnion S)
  refine prod_congr rfl fun i hi => ?_
  rw [hF i hi T, hF i hi (T ∩ I.biUnion S), inter_assoc, inter_eq_right.2 (subset_biUnion_of_mem S hi)]

/-- **Independence over disjoint supports**: the mean of a product of local functions with pairwise disjoint
supports is the product of their means. -/
theorem pexp_prod_local {ι : Type*} (I : Finset ι) (S : ι → Finset α) (hS : (I : Set ι).PairwiseDisjoint S)
    (F : ι → Finset α → ℝ) (hF : ∀ i ∈ I, IsLocal (S i) (F i)) :
    pexp q (fun T => ∏ i ∈ I, F i T) = ∏ i ∈ I, pexp q (F i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [prod_empty]; exact pexp_const q 1
  | insert i I hi ih =>
    have hS' : (I : Set ι).PairwiseDisjoint S := hS.subset (by rw [coe_insert]; exact Set.subset_insert _ _)
    have hF' : ∀ j ∈ I, IsLocal (S j) (F j) := fun j hj => hF j (mem_insert_of_mem hj)
    have hd : Disjoint (S i) (I.biUnion S) := by
      rw [disjoint_biUnion_right]
      intro j hj
      exact hS (by simp) (by simp [hj]) (fun h => hi (h ▸ hj))
    simp only [prod_insert hi]
    rw [pexp_mul_local q hd (hF i (mem_insert_self i I)) (IsLocal.prod I S F hF'), ih hS' hF']

/-! ## Selection and tails -/

/-- **Selection**: two nonnegative functionals with small means are small together somewhere. -/
theorem exists_le_two_mul {q : α → ℝ} (hq : IsProb q) {F₁ F₂ : Finset α → ℝ} {c₁ c₂ : ℝ}
    (h₁ : ∀ T, 0 ≤ F₁ T) (h₂ : ∀ T, 0 ≤ F₂ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hE₁ : pexp q F₁ ≤ c₁) (hE₂ : pexp q F₂ ≤ c₂) : ∃ T, F₁ T ≤ 2 * c₁ ∧ F₂ T ≤ 2 * c₂ := by
  obtain ⟨T₀, -, hT₀⟩ := exists_min_image univ (fun T => F₁ T / (2 * c₁) + F₂ T / (2 * c₂)) univ_nonempty
  have hle : F₁ T₀ / (2 * c₁) + F₂ T₀ / (2 * c₂) ≤ pexp q (fun T => F₁ T / (2 * c₁) + F₂ T / (2 * c₂)) :=
    calc _ = pexp q (fun _ => F₁ T₀ / (2 * c₁) + F₂ T₀ / (2 * c₂)) := (pexp_const q _).symm
      _ ≤ _ := pexp_mono hq fun T => hT₀ T (mem_univ T)
  have hE : pexp q (fun T => F₁ T / (2 * c₁) + F₂ T / (2 * c₂)) ≤ 1 := by
    have e : (fun T => F₁ T / (2 * c₁) + F₂ T / (2 * c₂)) =
        fun T => (2 * c₁)⁻¹ * F₁ T + (2 * c₂)⁻¹ * F₂ T := by
      funext T
      ring
    rw [e, pexp_add, pexp_const_mul, pexp_const_mul]
    have a1 : (2 * c₁)⁻¹ * pexp q F₁ ≤ 1 / 2 := by
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      linarith
    have a2 : (2 * c₂)⁻¹ * pexp q F₂ ≤ 1 / 2 := by
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have b1 : 0 ≤ F₁ T₀ / (2 * c₁) := div_nonneg (h₁ T₀) (by positivity)
  have b2 : 0 ≤ F₂ T₀ / (2 * c₂) := div_nonneg (h₂ T₀) (by positivity)
  refine ⟨T₀, ?_, ?_⟩
  · have : F₁ T₀ / (2 * c₁) ≤ 1 := by linarith
    rwa [div_le_one (by positivity)] at this
  · have : F₂ T₀ / (2 * c₂) ≤ 1 := by linarith
    rwa [div_le_one (by positivity)] at this

omit [Fintype α] in
/-- **Counting tail**: `1[|T ∩ W| ≥ N] ≤ #{U ⊆ W : |U| = N, U ⊆ T}`. -/
theorem ind_le_sum_powersetCard (W : Finset α) (N : ℕ) (T : Finset α) :
    (if N ≤ (T ∩ W).card then (1 : ℝ) else 0) ≤ ∑ U ∈ W.powersetCard N, if U ⊆ T then 1 else 0 := by
  have h0 : ∀ U ∈ W.powersetCard N, (0 : ℝ) ≤ if U ⊆ T then 1 else 0 := fun U _ => by
    split_ifs <;> norm_num
  split_ifs with h
  · obtain ⟨U, hUs, hUc⟩ := exists_subset_card_eq h
    have hU : U ∈ W.powersetCard N := mem_powersetCard.2 ⟨hUs.trans inter_subset_right, hUc⟩
    calc (1 : ℝ) = if U ⊆ T then 1 else 0 := by rw [ite_eq_left (hUs.trans inter_subset_left)]
      _ ≤ _ := single_le_sum (f := fun U => if U ⊆ T then (1 : ℝ) else 0) h0 hU
  · exact sum_nonneg h0

/-- **A union bound over subsets**: if `F ≤ Σ_{U ∈ 𝒰} [U ⊆ T]` then `E[F] ≤ Σ_{U ∈ 𝒰} ∏_U q`. -/
theorem pexp_le_sum_prod {q : α → ℝ} (hq : IsProb q) {F : Finset α → ℝ} (𝒰 : Finset (Finset α))
    (h : ∀ T, F T ≤ ∑ U ∈ 𝒰, if U ⊆ T then 1 else 0) : pexp q F ≤ ∑ U ∈ 𝒰, ∏ a ∈ U, q a :=
  calc pexp q F ≤ pexp q (fun T => ∑ U ∈ 𝒰, if U ⊆ T then 1 else 0) := pexp_mono hq h
    _ = _ := by rw [pexp_sum]; exact sum_congr rfl fun U _ => pexp_subset q U

/-- **A forced point and a full window**: `P(t ∈ T, |T ∩ W| ≥ N) ≤ δ(C(|W|, N−1)δ^{N−1} + C(|W|, N)δ^N)`, for
`0 ≤ q ≤ δ ≤ 1`. If `t ∈ W`, some `U ⊆ W ∖ {t}` of size `N − 1` has `U ∪ {t} ⊆ T`, of weight `≤ δ^N`; if `t ∉ W`,
some `U ⊆ W` of size `N`, of weight `≤ δ^{N+1}` with `t`. -/
theorem pexp_forced_window_le {q : α → ℝ} {δ : ℝ} (hq : ∀ a, 0 ≤ q a ∧ q a ≤ δ) (hδ : δ ≤ 1) (t : α)
    (W : Finset α) {N : ℕ} (hN : 1 ≤ N) :
    pexp q (fun T => if t ∈ T ∧ N ≤ (T ∩ W).card then 1 else 0) ≤
      δ * ((W.card.choose (N - 1) : ℝ) * δ ^ (N - 1) + (W.card.choose N : ℝ) * δ ^ N) := by
  have hq' : IsProb q := fun a => ⟨(hq a).1, (hq a).2.trans hδ⟩
  have hδ0 : 0 ≤ δ := (hq t).1.trans (hq t).2
  have hprod : ∀ U : Finset α, ∏ a ∈ U, q a ≤ δ ^ U.card := fun U =>
    (prod_le_prod₀ (fun a _ => (hq a).1) (fun a _ => (hq a).2)).trans_eq (prod_const δ)
  have h0 : ∀ (𝒰 : Finset (Finset α)) (T : Finset α), (0 : ℝ) ≤ ∑ U ∈ 𝒰, if insert t U ⊆ T then 1 else 0 :=
    fun 𝒰 T => sum_nonneg fun U _ => by split_ifs <;> norm_num
  have hC1 : 0 ≤ (W.card.choose (N - 1) : ℝ) * δ ^ (N - 1) := by positivity
  have hC2 : 0 ≤ (W.card.choose N : ℝ) * δ ^ N := by positivity
  by_cases htW : t ∈ W
  · have hle : ∀ T, (if t ∈ T ∧ N ≤ (T ∩ W).card then (1 : ℝ) else 0) ≤
        ∑ U ∈ ((W.erase t).powersetCard (N - 1)).image (insert t), if U ⊆ T then 1 else 0 := by
      intro T
      rw [sum_image fun U hU V hV hUV => ?_]
      · split_ifs with h
        · obtain ⟨htT, hc⟩ := h
          have e : T ∩ W = insert t (T ∩ W.erase t) := by
            ext a
            by_cases hat : a = t
            · subst hat
              simp [htT, htW]
            · simp [hat]
          have hc' : N - 1 ≤ (T ∩ W.erase t).card := by
            rw [e, card_insert_of_notMem (by simp)] at hc
            omega
          obtain ⟨U, hUs, hUc⟩ := exists_subset_card_eq hc'
          have hU : U ∈ (W.erase t).powersetCard (N - 1) :=
            mem_powersetCard.2 ⟨hUs.trans inter_subset_right, hUc⟩
          calc (1 : ℝ) = if insert t U ⊆ T then 1 else 0 :=
                by rw [ite_eq_left (insert_subset htT (hUs.trans inter_subset_left))]
            _ ≤ _ := single_le_sum (f := fun U => if insert t U ⊆ T then (1 : ℝ) else 0)
                (fun U _ => by split_ifs <;> norm_num) hU
        · exact h0 _ T
      · have htU : t ∉ U := fun h => by simpa using (mem_powersetCard.1 hU).1 h
        have htV : t ∉ V := fun h => by simpa using (mem_powersetCard.1 hV).1 h
        rw [← erase_insert htU, ← erase_insert htV, hUV]
    calc _ ≤ ∑ U ∈ ((W.erase t).powersetCard (N - 1)).image (insert t), ∏ a ∈ U, q a :=
          pexp_le_sum_prod hq' _ hle
      _ ≤ ∑ U ∈ ((W.erase t).powersetCard (N - 1)).image (insert t), δ ^ N := by
          refine sum_le_sum fun U hU => ?_
          obtain ⟨V, hV, rfl⟩ := mem_image.1 hU
          obtain ⟨hVs, hVc⟩ := mem_powersetCard.1 hV
          have htV : t ∉ V := fun h => by simpa using hVs h
          calc _ ≤ δ ^ (insert t V).card := hprod _
            _ = δ ^ N := by rw [card_insert_of_notMem htV, hVc, Nat.sub_add_cancel hN]
      _ ≤ ((W.erase t).card.choose (N - 1) : ℝ) * δ ^ N := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast card_image_le.trans (card_powersetCard _ _).le
      _ ≤ (W.card.choose (N - 1) : ℝ) * δ ^ N := by
          gcongr
          exact erase_subset t W
      _ = δ * ((W.card.choose (N - 1) : ℝ) * δ ^ (N - 1)) := by
          rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm, pow_succ, Nat.add_sub_cancel]
          ring
      _ ≤ _ := by nlinarith
  · have hle : ∀ T, (if t ∈ T ∧ N ≤ (T ∩ W).card then (1 : ℝ) else 0) ≤
        ∑ U ∈ (W.powersetCard N).image (insert t), if U ⊆ T then 1 else 0 := by
      intro T
      rw [sum_image fun U hU V hV hUV => ?_]
      · split_ifs with h
        · obtain ⟨htT, hc⟩ := h
          obtain ⟨U, hUs, hUc⟩ := exists_subset_card_eq hc
          have hU : U ∈ W.powersetCard N := mem_powersetCard.2 ⟨hUs.trans inter_subset_right, hUc⟩
          calc (1 : ℝ) = if insert t U ⊆ T then 1 else 0 :=
                by rw [ite_eq_left (insert_subset htT (hUs.trans inter_subset_left))]
            _ ≤ _ := single_le_sum (f := fun U => if insert t U ⊆ T then (1 : ℝ) else 0)
                (fun U _ => by split_ifs <;> norm_num) hU
        · exact h0 _ T
      · have htU : t ∉ U := fun h => htW ((mem_powersetCard.1 hU).1 h)
        have htV : t ∉ V := fun h => htW ((mem_powersetCard.1 hV).1 h)
        rw [← erase_insert htU, ← erase_insert htV, hUV]
    calc _ ≤ ∑ U ∈ (W.powersetCard N).image (insert t), ∏ a ∈ U, q a := pexp_le_sum_prod hq' _ hle
      _ ≤ ∑ U ∈ (W.powersetCard N).image (insert t), δ ^ (N + 1) := by
          refine sum_le_sum fun U hU => ?_
          obtain ⟨V, hV, rfl⟩ := mem_image.1 hU
          obtain ⟨hVs, hVc⟩ := mem_powersetCard.1 hV
          have htV : t ∉ V := fun h => htW (hVs h)
          calc _ ≤ δ ^ (insert t V).card := hprod _
            _ = δ ^ (N + 1) := by rw [card_insert_of_notMem htV, hVc]
      _ ≤ (W.card.choose N : ℝ) * δ ^ (N + 1) := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast card_image_le.trans (card_powersetCard _ _).le
      _ = δ * ((W.card.choose N : ℝ) * δ ^ N) := by rw [pow_succ]; ring
      _ ≤ _ := by nlinarith

end ProdWeights

/-- **The binomial tail** `C(G, N)δ^N ≤ (eGδ/N)^N`: `C(G, N) ≤ G^N/N!` and `N^N/N! ≤ e^N`
(`Real.pow_div_factorial_le_exp`). -/
theorem choose_mul_pow_le (G N : ℕ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) :
    (G.choose N : ℝ) * δ ^ N ≤ (Real.exp 1 * G * δ / N) ^ N := by
  have h1 : (G.choose N : ℝ) ≤ (G : ℝ) ^ N / N.factorial := Nat.choose_le_pow_div N G
  have h2 : (N : ℝ) ^ N / N.factorial ≤ Real.exp N := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have he : Real.exp N = Real.exp 1 ^ N := by rw [← Real.exp_nat_mul, mul_one]
  have h3 : (1 : ℝ) / N.factorial ≤ Real.exp 1 ^ N / (N : ℝ) ^ N := by
    rw [div_le_div_iff₀ hf (pow_pos hN0 N), one_mul, ← he]
    rwa [div_le_iff₀ hf] at h2
  have hGδ : 0 ≤ (G : ℝ) * δ := by positivity
  calc (G.choose N : ℝ) * δ ^ N ≤ (G : ℝ) ^ N / N.factorial * δ ^ N := by gcongr
    _ = (G * δ) ^ N * (1 / N.factorial) := by rw [mul_pow]; ring
    _ ≤ (G * δ) ^ N * (Real.exp 1 ^ N / (N : ℝ) ^ N) := by gcongr
    _ = _ := by rw [div_pow, mul_pow, mul_pow]; ring

end ZetaBalance
