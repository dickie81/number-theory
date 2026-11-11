/-
# Counts for role reversal

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements, used by `SieveAdRev.lean` for the terms of a reversed term (`SieveAdRevDefs.lean`).

* `primesIcc A B`: the primes of `[A, B]`. `sum_inv_primesIcc_le`: for `δ > 0` there is `T₀` such that for all
  `T₀ ≤ A ≤ B`, `Σ_{A ≤ p ≤ B} 1/p ≤ (log log B − log log A)(1 + δ) + δ`. `sum_inv_slab`: so for large `x`, every
  interval `[A, B]` with `A ≥ x^{a/DEN}` and `B ≤ A·x^{w/DEN}` has `Σ 1/p ≤ trB(a, w) + δ`, wherever it lies.
* `sum_piFinset_insertNth`: a sum over the tuples with entries in sets `S j`, as a sum over the entries but the
  `i`-th and then over the `i`-th. `slab_sum_le`: so the sum of `1/∏r` over the tuples whose product lies in
  `(θ₁, θ₂]` is at most `c·∏_{j ≠ i} Σ_{S j} 1/p`, when every interval `[A, B]` with `A` at least the entries of
  `S i` and `B ≤ A·θ₂/θ₁` has `Σ 1/p ≤ c`.
* `sum_snoc_le`: a sum over tuples with one more entry, of a product of a function of the first entries and one of
  the last, is at most the product of the two sums.
* `psi_level`: for large `x` and `r` between `x^{(s+y+1)/DEN}` and `x^{(s+y+W)/DEN}`, the numbers of `(x/r, 2x/r]`
  with no prime factor below `x^{y/DEN}` are at most `(omKw s y W 1/K·DEN/y + ε)(x/r)/log x`.
* `primes_level`: for large `x` and `Y` between `x^c` and `x^{h/DEN}`, the primes of `(Y, 2Y]` are at least
  `(1 − ε)(DEN/h)·Y/log x`.
* `card_sq_le`: for a unit `a` mod `q`, the `n ∈ (N₁, N₂]` in the class `a` that the square of a prime `s ≥ z`
  divides number at most `(N₂ − N₁)/(q(z − 1)) + √N₂`.
* `card_prime_tuples_le`: an `n` below `P^{M}` has at most `M³` triples of distinct primes at least `P` dividing it.

The file imports `SieveAdSpec.lean` and `SieveCount.lean`.
-/
import SieveAdSpec
import SieveCount

open Real Finset Filter SieveRough

namespace SieveAd

open Classical
open SieveCert (DEN K omKw DEN_pos' K_pos' trB)

/-! ### The primes of an interval that moves -/

/-- The primes `p` with `A ≤ p ≤ B`. -/
noncomputable def primesIcc (A B : ℝ) : Finset ℕ := (Finset.Icc ⌈A⌉₊ ⌊B⌋₊).filter Nat.Prime

theorem mem_primesIcc {A B : ℝ} (hB : 0 ≤ B) {p : ℕ} : p ∈ primesIcc A B ↔ p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ B := by
  rw [primesIcc, Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hB]
  tauto

/-- For `δ > 0` there is `T₀ > 1` such that for all `T₀ ≤ A ≤ B`:
`Σ_{A ≤ p ≤ B} 1/p ≤ (log log B − log log A)(1 + δ) + δ`. -/
theorem sum_inv_primesIcc_le {δ : ℝ} (hδ : 0 < δ) : ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ A B : ℝ, T₀ ≤ A → A ≤ B →
    ∑ p ∈ primesIcc A B, 1 / (p : ℝ) ≤ (Real.log (Real.log B) - Real.log (Real.log A)) * (1 + δ) + δ := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near (ε := δ / 6) (by positivity))
  have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  refine ⟨max (max T (Real.exp 1)) (2 / δ),
    lt_of_lt_of_le he1 (le_trans (le_max_right _ _) (le_max_left _ _)), fun A B hA hAB => ?_⟩
  have hAT : T ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hAe : Real.exp 1 ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hAδ : 2 / δ ≤ A := le_trans (le_max_right _ _) hA
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos 1) hAe
  have h1 := sum_inv_le hAe hAB (by positivity : (0 : ℝ) ≤ δ / 6) fun t ht => hT t (le_trans hAT ht.1)
  have hla : 1 ≤ Real.log A := by rw [Real.le_log_iff_exp_le hA0]; exact hAe
  have hll : 0 ≤ Real.log (Real.log B) - Real.log (Real.log A) :=
    sub_nonneg.2 (Real.log_le_log (by linarith) (Real.log_le_log hA0 hAB))
  have hsub : primesIcc A B ⊆ insert ⌈A⌉₊ ((Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime) := by
    intro p hp
    rw [primesIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_insert]
    by_cases h : p = ⌈A⌉₊
    · exact Or.inl h
    · refine Or.inr ?_
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_le_of_lt (Nat.floor_le_ceil A) (lt_of_le_of_ne hp.1.1 (Ne.symm h)), hp.1.2⟩, hp.2⟩
  have h2 : ∑ p ∈ primesIcc A B, 1 / (p : ℝ) ≤
      1 / (⌈A⌉₊ : ℝ) + ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_
    by_cases hm : ⌈A⌉₊ ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime
    · rw [Finset.insert_eq_of_mem hm]
      have : (0 : ℝ) ≤ 1 / (⌈A⌉₊ : ℝ) := by positivity
      linarith
    · rw [Finset.sum_insert hm]
  have h3 : 1 / (⌈A⌉₊ : ℝ) ≤ δ / 2 := by
    calc 1 / (⌈A⌉₊ : ℝ) ≤ 1 / A := one_div_le_one_div_of_le hA0 (Nat.le_ceil _)
      _ ≤ 1 / (2 / δ) := one_div_le_one_div_of_le (by positivity) hAδ
      _ = δ / 2 := by rw [one_div_div]
  have h4 : (Real.log (Real.log B) - Real.log (Real.log A)) * (1 + δ / 6 / Real.log A) ≤
      (Real.log (Real.log B) - Real.log (Real.log A)) * (1 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith [div_le_self (by positivity : (0 : ℝ) ≤ δ / 6) hla]) hll
  have h5 : 3 * (δ / 6) / Real.log A ^ 2 ≤ 3 * (δ / 6) := div_le_self (by positivity) (one_le_pow₀ hla)
  linarith

/-- For `a > 0`, `δ > 0` and large `x`: every interval `[A, B]` with `A ≥ x^{a/DEN}` and `B ≤ A·x^{w/DEN}` has
`Σ_{A ≤ p ≤ B} 1/p ≤ trB(a, w) + δ`. -/
theorem sum_inv_slab {a w : ℕ} (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ A B : ℝ, x ^ ((a : ℝ) / DEN) ≤ A → B ≤ A * x ^ ((w : ℝ) / DEN) →
      ∑ p ∈ primesIcc A B, 1 / (p : ℝ) ≤ trB a w + δ := by
  have hD := DEN_pos'
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have htr : 0 ≤ trB a w := SieveCert.trB_nonneg _ _
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = δ / (trB a w + 1) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  have hδ'e : δ' * (trB a w + 1) = δ := by rw [hδ']; field_simp
  obtain ⟨T₀, hT1, hT₀⟩ := sum_inv_primesIcc_le hδ'0
  have hlog : Real.log (((a : ℝ) + w) / a) ≤ trB a w := by
    have h1 : (1 : ℝ) ≤ ((a : ℝ) + w) / a := by rw [le_div_iff₀ ha']; linarith
    have h := SieveOmegaB.log_le_half_sub_inv h1
    have h2 : (((a : ℝ) + w) / a - (((a : ℝ) + w) / a)⁻¹) / 2 = trB a w := by
      unfold trB; field_simp; ring
    linarith
  filter_upwards [(tendsto_rpow_atTop (div_pos ha' hD)).eventually_ge_atTop T₀, eventually_gt_atTop 1]
    with x hxT hx1 A B hA hB
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  by_cases hAB : A ≤ B
  · have hAT : T₀ ≤ A := hxT.trans hA
    have hA1 : 1 < A := lt_of_lt_of_le hT1 hAT
    have hA0 : 0 < A := by linarith
    have hlA : 0 < Real.log A := Real.log_pos hA1
    have hlAx : (a : ℝ) / DEN * Real.log x ≤ Real.log A := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hA
      rwa [Real.log_rpow hx0] at this
    have hlB : Real.log B ≤ Real.log A + (w : ℝ) / DEN * Real.log x := by
      have := Real.log_le_log (by linarith) hB
      rwa [Real.log_mul hA0.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at this
    have hlB0 : 0 < Real.log B := lt_of_lt_of_le hlA (Real.log_le_log hA0 hAB)
    have hratio : Real.log B / Real.log A ≤ ((a : ℝ) + w) / a := by
      rw [div_le_div_iff₀ hlA ha']
      have h1 : (w : ℝ) / DEN * Real.log x * a ≤ w * Real.log A := by
        have := mul_le_mul_of_nonneg_left hlAx hw
        calc (w : ℝ) / DEN * Real.log x * a = w * ((a : ℝ) / DEN * Real.log x) := by ring
          _ ≤ w * Real.log A := this
      nlinarith
    have hll : Real.log (Real.log B) - Real.log (Real.log A) ≤ trB a w := by
      rw [← Real.log_div hlB0.ne' hlA.ne']
      exact (Real.log_le_log (div_pos hlB0 hlA) hratio).trans hlog
    have h := hT₀ A B hAT hAB
    have h2 : (Real.log (Real.log B) - Real.log (Real.log A)) * (1 + δ') ≤ trB a w * (1 + δ') :=
      mul_le_mul_of_nonneg_right hll (by linarith)
    nlinarith
  · have hempty : primesIcc A B = ∅ := by
      rw [primesIcc, Finset.filter_eq_empty_iff]
      intro p hp
      rw [Finset.mem_Icc] at hp
      exfalso
      have h1 : A ≤ (p : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hp.1)
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hB0 : 0 ≤ B := by
        by_contra hneg
        have : ⌊B⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
        have hp' : p = 0 := by omega
        have hA' : A ≤ 0 := by rw [hp'] at h1; simpa using h1
        have hxa : 0 < x ^ ((a : ℝ) / DEN) := Real.rpow_pos_of_pos hx0 _
        linarith
      have h2 : (p : ℝ) ≤ B := (Nat.cast_le.2 hp.2).trans (Nat.floor_le hB0)
      linarith
    rw [hempty, Finset.sum_empty]
    linarith

/-! ### Sums over the tuples of a box -/

/-- A sum over the tuples with entries in the sets `S j`: over the entries but the `i`-th, then over the `i`-th. -/
theorem sum_piFinset_insertNth {k : ℕ} (S : Fin (k + 1) → Finset ℕ) (i : Fin (k + 1))
    (G : (Fin (k + 1) → ℕ) → ℝ) :
    ∑ r ∈ Fintype.piFinset S, G r =
      ∑ o ∈ Fintype.piFinset (fun j => S (i.succAbove j)), ∑ Q ∈ S i,
        G (Fin.insertNth (α := fun _ => ℕ) i Q o) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun r => (Fin.removeNth i r, r i))
    (fun p => Fin.insertNth (α := fun _ => ℕ) i p.2 p.1) ?_ ?_ ?_ ?_ ?_
  · intro r h
    rw [Fintype.mem_piFinset] at h
    exact Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun j => h _, h i⟩
  · rintro ⟨o, Q⟩ h
    obtain ⟨ho, hQ⟩ := Finset.mem_product.1 h
    rw [Fintype.mem_piFinset] at ho ⊢
    intro j
    refine Fin.succAboveCases i ?_ (fun j => ?_) j
    · simpa using hQ
    · simpa using ho j
  · intro r _
    simp
  · rintro ⟨o, Q⟩ _
    simp
  · intro r _
    simp

/-- **The tuples of a box whose product lies in a range.** For sets `S j` of primes, the entries of `S i` at least
`A₀`, and `c` a bound of `Σ 1/p` over every interval `[A, B]` with `A ≥ A₀` and `B ≤ A·θ₂/θ₁`: the sum of `1/∏r`
over the tuples with entries in the `S j` and product in `(θ₁, θ₂]` is at most `c·∏_{j ≠ i} Σ_{S j} 1/p`. -/
theorem slab_sum_le {k : ℕ} (S : Fin (k + 1) → Finset ℕ) (i : Fin (k + 1)) {c θ₁ θ₂ A₀ : ℝ}
    (hS : ∀ j, ∀ p ∈ S j, p.Prime) (hi : ∀ p ∈ S i, A₀ ≤ (p : ℝ)) (hθ₁ : 0 < θ₁) (hθ₂ : 0 ≤ θ₂)
    (hfib : ∀ A B : ℝ, A₀ ≤ A → B ≤ A * (θ₂ / θ₁) → ∑ p ∈ primesIcc A B, 1 / (p : ℝ) ≤ c) :
    ∑ r ∈ (Fintype.piFinset S).filter (fun r => θ₁ < ((∏ j, r j : ℕ) : ℝ) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ θ₂),
        ∏ j, (1 / (r j : ℝ)) ≤ c * ∏ j : Fin k, ∑ p ∈ S (i.succAbove j), 1 / (p : ℝ) := by
  rw [Finset.sum_filter, sum_piFinset_insertNth S i, Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun o ho => ?_
  rw [Fintype.mem_piFinset] at ho
  have hopos : ∀ j, (0 : ℝ) < o j := fun j => by exact_mod_cast (hS _ _ (ho j)).pos
  set ρ : ℝ := ∏ j, (o j : ℝ) with hρ
  have hρ0 : 0 < ρ := Finset.prod_pos fun j _ => hopos j
  set w : ℝ := ∏ j, (1 / (o j : ℝ)) with hw
  have hw0 : 0 ≤ w := Finset.prod_nonneg fun j _ => by positivity
  -- each term, by the `i`-th entry
  have hterm : ∀ Q ∈ S i,
      (if θ₁ < ((∏ j, (Fin.insertNth (α := fun _ => ℕ) i Q o) j : ℕ) : ℝ) ∧
          ((∏ j, (Fin.insertNth (α := fun _ => ℕ) i Q o) j : ℕ) : ℝ) ≤ θ₂
        then ∏ j, (1 / ((Fin.insertNth (α := fun _ => ℕ) i Q o j : ℕ) : ℝ)) else 0) =
        w * (if θ₁ < (Q : ℝ) * ρ ∧ (Q : ℝ) * ρ ≤ θ₂ then 1 / (Q : ℝ) else 0) := by
    intro Q _
    have e1 : ((∏ j, (Fin.insertNth (α := fun _ => ℕ) i Q o) j : ℕ) : ℝ) = (Q : ℝ) * ρ := by
      rw [Fin.prod_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      push_cast
      rw [hρ]
    have e2 : ∏ j, (1 / ((Fin.insertNth (α := fun _ => ℕ) i Q o j : ℕ) : ℝ)) = w * (1 / (Q : ℝ)) := by
      rw [Fin.prod_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      rw [hw, mul_comm]
    rw [e1, e2]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_comm c]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  rw [← Finset.sum_filter]
  -- the `i`-th entries lie in an interval
  set A : ℝ := max (θ₁ / ρ) A₀ with hA
  set B : ℝ := θ₂ / ρ with hB
  have hB0 : 0 ≤ B := div_nonneg hθ₂ hρ0.le
  have hsub : (S i).filter (fun Q : ℕ => θ₁ < (Q : ℝ) * ρ ∧ (Q : ℝ) * ρ ≤ θ₂) ⊆ primesIcc A B := by
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    rw [mem_primesIcc hB0]
    refine ⟨hS i Q hQ.1, max_le ?_ (hi Q hQ.1), ?_⟩
    · rw [div_le_iff₀ hρ0]
      exact hQ.2.1.le
    · rw [hB, le_div_iff₀ hρ0]
      exact hQ.2.2
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans (hfib A B (le_max_right _ _) ?_)
  have h1 : B = θ₁ / ρ * (θ₂ / θ₁) := by rw [hB]; field_simp
  rw [h1]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg hθ₂ hθ₁.le)

/-- A sum over tuples with one more entry, of a product of a function of the first entries and one of the last, is
at most the product of the sums over the first entries and over the last. -/
theorem sum_snoc_le {k : ℕ} (F : Finset (Fin (k + 1) → ℕ)) (F₀ : Finset (Fin k → ℕ)) (S : Finset ℕ)
    (hF : ∀ rt ∈ F, Fin.init rt ∈ F₀ ∧ rt (Fin.last k) ∈ S) (G : (Fin k → ℕ) → ℝ) (f : ℕ → ℝ)
    (hG : ∀ r, 0 ≤ G r) (hf : ∀ p, 0 ≤ f p) :
    ∑ rt ∈ F, G (Fin.init rt) * f (rt (Fin.last k)) ≤ (∑ r ∈ F₀, G r) * ∑ p ∈ S, f p := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hinj : Set.InjOn (fun rt : Fin (k + 1) → ℕ => (Fin.init rt, rt (Fin.last k))) F := by
    intro r₁ _ r₂ _ h
    simp only [Prod.mk.injEq] at h
    rw [← Fin.snoc_init_self r₁, ← Fin.snoc_init_self r₂, h.1, h.2]
  rw [← Finset.sum_image (f := fun p : (Fin k → ℕ) × ℕ => G p.1 * f p.2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => mul_nonneg (hG _) (hf _)
  intro p hp
  obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.1 hp
  exact Finset.mem_product.2 (hF rt hrt)

/-! ### The numbers of `(x/r, 2x/r]` with no small prime factor, and its primes -/

/-- **Rough numbers of `(x/r, 2x/r]`.** For `y > 0` with `s + y + W ≤ DEN`, `ε > 0` and large `x`: for every `r`
between `x^{(s+y+1)/DEN}` and `x^{(s+y+W)/DEN}`, the numbers of `(x/r, 2x/r]` with no prime factor below
`⌈x^{y/DEN}⌉` are at most `(omKw s y W 1/K·DEN/y + ε)(x/r)/log x`. -/
theorem psi_level {y s W : ℕ} (hy : 0 < y) (hfit : s + y + W ≤ DEN) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ r : ℝ, x ^ (((s + y + 1 : ℕ) : ℝ) / DEN) ≤ r → r ≤ x ^ (((s + y + W : ℕ) : ℝ) / DEN) →
      (Psi (x / r) ⌈x ^ ((y : ℝ) / DEN)⌉₊ : ℝ) ≤
        ((omKw s y W 1 : ℝ) / K * ((DEN : ℝ) / y) + ε) * (x / r / Real.log x) := by
  have hD := DEN_pos'
  have hK := K_pos'
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ℝ, Ω = (omKw s y W 1 : ℝ) / K := ⟨_, rfl⟩
  have hΩ0 : 0 ≤ Ω := by rw [hΩ]; positivity
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = ε * y / DEN := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  obtain ⟨z₀, hz₀⟩ := psi_le (2 * DEN / y) hε₁0
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2),
    (tendsto_rpow_atTop (div_pos hy' hD)).eventually_ge_atTop (max (z₀ : ℝ) 2)] with x hx1 hlx2 hxz r hr1 hr2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log x * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  obtain ⟨z, hz⟩ : ∃ z : ℕ, z = ⌈x ^ ((y : ℝ) / DEN)⌉₊ := ⟨_, rfl⟩
  rw [← hz]
  have hxy0 : 0 < x ^ ((y : ℝ) / DEN) := Real.rpow_pos_of_pos hx0 _
  have hzge : x ^ ((y : ℝ) / DEN) ≤ z := by rw [hz]; exact Nat.le_ceil _
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ z := le_trans (le_trans (le_max_right _ _) hxz) hzge
    exact_mod_cast this
  have hzz₀ : z₀ ≤ z := by
    have : (z₀ : ℝ) ≤ z := le_trans (le_trans (le_max_left _ _) hxz) hzge
    exact_mod_cast this
  have hz0 : (0 : ℝ) < z := by
    have : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the logarithms
  have hlz1 : (y : ℝ) / DEN * Real.log x ≤ Real.log z := by
    have := Real.log_le_log hxy0 hzge
    rwa [Real.log_rpow hx0] at this
  have hlz2 : Real.log z ≤ ((y : ℝ) + 1) / DEN * Real.log x := by
    have h1 : (z : ℝ) < x ^ ((y : ℝ) / DEN) + 1 := by rw [hz]; exact Nat.ceil_lt_add_one hxy0.le
    have h2 : 1 ≤ x ^ ((y : ℝ) / DEN) := Real.one_le_rpow hx1.le (by positivity)
    have h3 : (z : ℝ) ≤ 2 * x ^ ((y : ℝ) / DEN) := by linarith
    have h4 := Real.log_le_log hz0 h3
    rw [Real.log_mul two_ne_zero hxy0.ne', Real.log_rpow hx0] at h4
    have h5 : Real.log 2 ≤ 1 / DEN * Real.log x := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hD]; linarith
    calc Real.log z ≤ Real.log 2 + (y : ℝ) / DEN * Real.log x := h4
      _ ≤ 1 / DEN * Real.log x + (y : ℝ) / DEN * Real.log x := by linarith
      _ = ((y : ℝ) + 1) / DEN * Real.log x := by ring
  have hr0 : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hr1
  have hlr1 : ((s : ℝ) + y + 1) / DEN * Real.log x ≤ Real.log r := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hr1
    rw [Real.log_rpow hx0] at this
    push_cast at this
    exact this
  have hlr2 : Real.log r ≤ ((s : ℝ) + y + W) / DEN * Real.log x := by
    have := Real.log_le_log hr0 hr2
    rw [Real.log_rpow hx0] at this
    push_cast at this
    exact this
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = r / z := ⟨_, rfl⟩
  have hdz : d * z = r := by rw [hd]; field_simp
  have hd0 : 0 < d := by rw [hd]; positivity
  have hld : Real.log d = Real.log r - Real.log z := by rw [hd, Real.log_div hr0.ne' hz0.ne']
  have hd1 : 1 ≤ d := by
    rw [← Real.log_nonneg_iff hd0, hld]
    have : ((y : ℝ) + 1) / DEN * Real.log x ≤ ((s : ℝ) + y + 1) / DEN * Real.log x :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; linarith)
        hD.le) hlx.le
    linarith
  have hz2' : (2 : ℝ) ≤ z := by exact_mod_cast hz2
  have hlz0 : 0 < Real.log z := Real.log_pos (by linarith)
  have conv : ∀ {u e : ℝ}, e / DEN * Real.log x ≤ u → e ≤ u / Real.log x * DEN := by
    intro u e h
    rw [div_mul_eq_mul_div, le_div_iff₀ hlx]
    have := mul_le_mul_of_nonneg_right h hD.le
    calc e * Real.log x = e / DEN * Real.log x * DEN := by field_simp
      _ ≤ u * DEN := this
  have conv' : ∀ {u e : ℝ}, u ≤ e / DEN * Real.log x → u / Real.log x * DEN ≤ e := by
    intro u e h
    rw [div_mul_eq_mul_div, div_le_iff₀ hlx]
    have := mul_le_mul_of_nonneg_right h hD.le
    calc u * DEN ≤ e / DEN * Real.log x * DEN := this
      _ = e * Real.log x := by field_simp
  have hs : (s : ℝ) ≤ Real.log d / Real.log x * DEN := by
    refine conv ?_
    rw [hld]
    have e : (s : ℝ) / DEN * Real.log x =
        ((s : ℝ) + y + 1) / DEN * Real.log x - ((y : ℝ) + 1) / DEN * Real.log x := by ring
    linarith
  have hsum : (Real.log d / Real.log x + Real.log z / Real.log x) * DEN ≤ (s : ℝ) + y + W := by
    rw [← add_div, hld, sub_add_cancel]
    exact conv' hlr2
  have hψ := psi_point_w (s := s) (t := y) (W := W) (w := 1) (ε := ε₁) (x := x) (d := d) (p := z) hy hz₀ hx1 hτ hd1
    hz2 hzz₀ hs (conv hlz1) (by push_cast; exact conv' hlz2) hsum (by exact_mod_cast hfit)
  rw [hdz, ← hΩ] at hψ
  rw [← hΩ]
  refine hψ.trans ?_
  have hxr : 0 ≤ x / r := by positivity
  have h1 : x / (r * Real.log z) ≤ (DEN : ℝ) / y * (x / r / Real.log x) := by
    rw [div_div, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (y : ℝ) * Real.log x ≤ DEN * Real.log z := by
      have := mul_le_mul_of_nonneg_right hlz1 hD.le
      calc (y : ℝ) * Real.log x = (y : ℝ) / DEN * Real.log x * DEN := by field_simp
        _ ≤ Real.log z * DEN := this
        _ = DEN * Real.log z := by ring
    nlinarith [mul_nonneg hx0.le hr0.le]
  have hxlx : 0 ≤ x / r / Real.log x := by positivity
  calc (Ω + ε₁) * (x / (r * Real.log z)) ≤ (Ω + ε₁) * ((DEN : ℝ) / y * (x / r / Real.log x)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (Ω * ((DEN : ℝ) / y) + ε) * (x / r / Real.log x) := by
        rw [hε₁]; field_simp

/-- **The primes of `(Y, 2Y]`.** For `c > 0`, `h > 0`, `ε > 0` and large `x`: for every `Y` between `x^c` and
`x^{h/DEN}`, the primes of `(Y, 2Y]` are at least `(1 − ε)(DEN/h)·Y/log x`. -/
theorem primes_level {h : ℕ} (hh : 0 < h) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ c ≤ Y → Y ≤ x ^ ((h : ℝ) / DEN) →
      (1 - ε) * ((DEN : ℝ) / h) * (Y / Real.log x) ≤ (((Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime).card : ℝ) := by
  have hD := DEN_pos'
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (SieveMain.primes_dyadic_ge hε)
  filter_upwards [(tendsto_rpow_atTop hc).eventually_ge_atTop (max Y₀ 2), eventually_gt_atTop 1]
    with x hxc hx1 Y hY1 hY2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hYge : Y₀ ≤ Y := le_trans (le_trans (le_max_left _ _) hxc) hY1
  have hY2' : 2 ≤ Y := le_trans (le_trans (le_max_right _ _) hxc) hY1
  have h1 := hY₀ Y hYge
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlYx : Real.log Y ≤ (h : ℝ) / DEN * Real.log x := by
    have := Real.log_le_log (by linarith) hY2
    rwa [Real.log_rpow hx0] at this
  by_cases hε1 : 1 - ε ≤ 0
  · have h0 : 0 ≤ (DEN : ℝ) / h * (Y / Real.log x) := by positivity
    have : (1 - ε) * ((DEN : ℝ) / h) * (Y / Real.log x) ≤ 0 := by
      rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg hε1 h0
    exact this.trans (Nat.cast_nonneg _)
  · push Not at hε1
    refine le_trans ?_ h1
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hε1.le
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hlY]
    have h2 : Real.log Y * DEN ≤ h * Real.log x := by
      have := mul_le_mul_of_nonneg_right hlYx hD.le
      calc Real.log Y * DEN ≤ (h : ℝ) / DEN * Real.log x * DEN := this
        _ = h * Real.log x := by field_simp
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Y) hlY.le]

/-! ### The numbers with a square factor -/

/-- `Σ_{z ≤ s ≤ S} 1/s² ≤ 1/(z − 1)` for `z ≥ 2`. -/
theorem sum_inv_sq_Icc_le {z : ℕ} (hz : 2 ≤ z) (S : ℕ) :
    ∑ s ∈ Finset.Icc z S, 1 / ((s : ℝ) ^ 2) ≤ 1 / ((z : ℝ) - 1) := by
  have hz' : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have key : ∀ S : ℕ, z - 1 ≤ S → ∑ s ∈ Finset.Icc z S, 1 / ((s : ℝ) ^ 2) ≤ 1 / ((z : ℝ) - 1) - 1 / (S : ℝ) := by
    intro S hS
    induction S, hS using Nat.le_induction with
    | base =>
      have he : Finset.Icc z (z - 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [he, Finset.sum_empty, Nat.cast_sub (by omega)]
      simp
    | succ S hS ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
      have h1 : 1 / (((S + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (S : ℝ) - 1 / ((S + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  by_cases hS : z - 1 ≤ S
  · have h := key S hS
    have : (0 : ℝ) ≤ 1 / (S : ℝ) := by positivity
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have : (0 : ℝ) < (z : ℝ) - 1 := by linarith
    positivity

/-- **The numbers with a square factor.** For a unit `a` mod `q > 0` and `z ≥ 2`, the `n ∈ (N₁, N₂]` in the class
`a` that the square of a prime `s ≥ z` divides number at most `(N₂ − N₁)/(q(z − 1)) + √N₂`. -/
theorem card_sq_le {q : ℕ} (hq : 0 < q) {a : ZMod q} (ha : IsUnit a) {N₁ N₂ z : ℕ} (hN : N₁ ≤ N₂) (hz : 2 ≤ z) :
    (((Ioc N₁ N₂).filter fun n : ℕ => (n : ZMod q) = a ∧ ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n).card : ℝ) ≤
      ((N₂ : ℝ) - N₁) / (q * ((z : ℝ) - 1)) + Nat.sqrt N₂ := by
  have : NeZero q := ⟨hq.ne'⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hz' : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hNN : (0 : ℝ) ≤ (N₂ : ℝ) - N₁ := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    linarith
  have hacop : Nat.Coprime a.val q := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact ha
  set P := (Finset.Icc z (Nat.sqrt N₂)).filter Nat.Prime with hP
  set T : ℕ → Finset ℕ := fun s => (Ioc N₁ N₂).filter fun n => n ≡ a.val [MOD q] ∧ s ^ 2 ∣ n with hT
  have hsub : ((Ioc N₁ N₂).filter fun n : ℕ => (n : ZMod q) = a ∧ ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n) ⊆
      P.biUnion T := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hna, s, hs, hzs, hd⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨s, ?_, ?_⟩
    · rw [hP, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hzs, ?_⟩, hs⟩
      rw [Nat.le_sqrt']
      exact (Nat.le_of_dvd (by omega) hd).trans h2
    · rw [hT, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨h1, h2⟩, ?_, hd⟩
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
      exact hna
  have hTs : ∀ s ∈ P, ((T s).card : ℝ) ≤ ((N₂ : ℝ) - N₁) / q * (1 / ((s : ℝ) ^ 2)) + 1 := by
    intro s hs
    rw [hP, Finset.mem_filter, Finset.mem_Icc] at hs
    have hsp := hs.2
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hsp.pos
    by_cases hcop : Nat.Coprime (s ^ 2) q
    · have h := SieveCount.card_A hq (pow_pos hsp.pos 2) hcop hN a.val
      rw [abs_le] at h
      have e : ((N₂ : ℝ) - N₁) / (((s ^ 2 : ℕ) : ℝ) * q) = ((N₂ : ℝ) - N₁) / q * (1 / ((s : ℝ) ^ 2)) := by
        push_cast; field_simp
      rw [e] at h
      linarith [h.2]
    · have hempty : T s = ∅ := by
        rw [hT, Finset.filter_eq_empty_iff]
        rintro n - ⟨hna, hd⟩
        have hsq : s ∣ q := by
          by_contra hns
          exact hcop (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hsp).2 hns))
        have hsn : s ∣ n := (dvd_pow_self s two_ne_zero).trans hd
        have hsa : s ∣ a.val := (Nat.ModEq.dvd_iff hna hsq).1 hsn
        exact hsp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hacop hsa hsq)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      have : 0 ≤ ((N₂ : ℝ) - N₁) / q * (1 / ((s : ℝ) ^ 2)) := by positivity
      linarith
  have hsum : ∑ s ∈ P, 1 / ((s : ℝ) ^ 2) ≤ 1 / ((z : ℝ) - 1) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => by positivity).trans
      (sum_inv_sq_Icc_le hz _)
  have hPc : (P.card : ℝ) ≤ Nat.sqrt N₂ := by
    have h1 : P.card ≤ (Finset.Icc z (Nat.sqrt N₂)).card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.card_Icc] at h1
    exact_mod_cast (show P.card ≤ Nat.sqrt N₂ by omega)
  calc (((Ioc N₁ N₂).filter fun n : ℕ => (n : ZMod q) = a ∧ ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n).card : ℝ)
      ≤ ((P.biUnion T).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ P, ((T s).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ P, (((N₂ : ℝ) - N₁) / q * (1 / ((s : ℝ) ^ 2)) + 1) := Finset.sum_le_sum hTs
    _ = ((N₂ : ℝ) - N₁) / q * ∑ s ∈ P, 1 / ((s : ℝ) ^ 2) + P.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((N₂ : ℝ) - N₁) / q * (1 / ((z : ℝ) - 1)) + Nat.sqrt N₂ :=
        add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) hPc
    _ = ((N₂ : ℝ) - N₁) / (q * ((z : ℝ) - 1)) + Nat.sqrt N₂ := by
        rw [div_mul_div_comm, mul_one]

/-- **Few tuples of large primes divide a number.** The tuples of a family whose entries are primes at least `P > 1`
that divide `n < P^M` number at most `M^k`. -/
theorem card_tuples_dvd_le {k : ℕ} (F : Finset (Fin k → ℕ)) {P : ℝ} {M n : ℕ} (hn : 0 < n) (hP : 1 < P)
    (hnP : (n : ℝ) < P ^ M) (hF : ∀ rt ∈ F, ∀ i, (rt i).Prime ∧ P ≤ (rt i : ℝ) ∧ rt i ∣ n) : F.card ≤ M ^ k := by
  set S := n.primeFactors.filter (fun p : ℕ => P ≤ (p : ℝ)) with hS
  have hsub : F ⊆ Fintype.piFinset fun _ : Fin k => S := by
    intro rt hrt
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨hp, hPp, hd⟩ := hF rt hrt i
    rw [hS, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hd, hn.ne'⟩, hPp⟩
  have hcard : S.card ≤ M := by
    have h1 : P ^ S.card ≤ ∏ p ∈ S, (p : ℝ) := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => by linarith) fun p hp => (Finset.mem_filter.1 hp).2
    have h2 : (∏ p ∈ S, p) ≤ n :=
      Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p => p)
        (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n))
    have h3 : (∏ p ∈ S, (p : ℝ)) ≤ n := by
      rw [← Nat.cast_prod]
      exact_mod_cast h2
    have h4 : P ^ S.card < P ^ M := lt_of_le_of_lt (h1.trans h3) hnP
    exact ((pow_lt_pow_iff_right₀ hP).1 h4).le
  calc F.card ≤ (Fintype.piFinset fun _ : Fin k => S).card := Finset.card_le_card hsub
    _ = S.card ^ k := by rw [Fintype.card_piFinset_const]
    _ ≤ M ^ k := Nat.pow_le_pow_left hcard k

end SieveAd

#print axioms SieveAd.sum_inv_slab
#print axioms SieveAd.slab_sum_le
#print axioms SieveAd.sum_snoc_le
#print axioms SieveAd.psi_level
#print axioms SieveAd.primes_level
#print axioms SieveAd.card_sq_le
#print axioms SieveAd.card_tuples_dvd_le
