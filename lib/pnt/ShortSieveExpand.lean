import ShortSieveBoxes

/-!
# Sieve terms with several rough items as tuples of primes

The terms of Li's decomposition sum over `k` primes `p` and `m` rough integers `ρ`, the item `ρ_i` free of primes
below `p_{s(i)}`. The Type II estimate counts tuples of primes. Every rough integer is the product of the monotone
tuple of its prime factors (`ShortSieveBoxes.ofFn_eq_primeFactorsList`), so for each pattern `len` of numbers of prime
factors the terms are the tuples `g` of primes indexed by `Fin k ⊕ (Σ i, Fin (len i))`: the primes `p` on the left,
and on the right one monotone block for each rough item, every prime of the block at least `p_{s(i)}`.

* `card_expand`: **the expansion.** For a predicate `P` on `(p, ρ)` under which every `ρ_i` has at most `R` prime
  factors, the pairs `(p, ρ)` with `ρ_i ≥ 1` free of primes below `p_{s(i)}` and `P p ρ` number
  `Σ_{len ≤ R} #{g : blocks monotone with products at most Y, every prime of block i at least p_{s(i)},
  P (g ∘ inl) (∏ blocks)}`.
-/

open Finset

namespace ShortSieveExpand

open ShortSieveBoxes

open Classical

/-- The index type of the expanded tuples: the `k` primes and one block of `len i` primes for each rough item. -/
abbrev Idx (k m : ℕ) (len : Fin m → ℕ) : Type := Fin k ⊕ (Σ i : Fin m, Fin (len i))

/-- The block of the rough item `i` in an expanded tuple. -/
def block {k m : ℕ} {len : Fin m → ℕ} (g : Idx k m len → ℕ) (i : Fin m) : Fin (len i) → ℕ :=
  fun j => g (Sum.inr ⟨i, j⟩)

/-- The pairs `(p, ρ)` of `k` primes and `m` integers in `[1, Y]`. -/
noncomputable def pairs (k m Y : ℕ) : Finset ((Fin k → ℕ) × (Fin m → ℕ)) :=
  (Fintype.piFinset fun _ : Fin k => SieveTypeIIU.primesLe Y) ×ˢ (Fintype.piFinset fun _ : Fin m => Icc 1 Y)

/-- The expanded tuples of primes up to `Y` for the pattern `len`. -/
noncomputable def tuplesOf (k m Y : ℕ) (len : Fin m → ℕ) : Finset (Idx k m len → ℕ) :=
  Fintype.piFinset fun _ : Idx k m len => SieveTypeIIU.primesLe Y

/-- The prime factors of `ρ`, as a function of the position (`0` past the end). -/
def fac (ρ : ℕ) (j : ℕ) : ℕ := ρ.primeFactorsList.getD j 0

/-- The expanded tuple of `(p, ρ)` for the pattern `len`. -/
def expand {k m : ℕ} (len : Fin m → ℕ) (x : (Fin k → ℕ) × (Fin m → ℕ)) : Idx k m len → ℕ :=
  Sum.elim x.1 fun ij => fac (x.2 ij.1) ij.2

/-- The pair `(p, ρ)` of an expanded tuple: the primes, and the products of the blocks. -/
def contract {k m : ℕ} {len : Fin m → ℕ} (g : Idx k m len → ℕ) : (Fin k → ℕ) × (Fin m → ℕ) :=
  (fun a => g (Sum.inl a), fun i => ∏ j, block g i j)

/-- The product of the first `ℓ` prime factors of `ρ ≥ 1` with exactly `ℓ` of them is `ρ`. -/
theorem prod_fac {ρ ℓ : ℕ} (hρ : ρ ≠ 0) (hℓ : ρ.primeFactorsList.length = ℓ) :
    ∏ j : Fin ℓ, fac ρ j = ρ := by
  subst hℓ
  have e : (fun j : Fin ρ.primeFactorsList.length => fac ρ j) = ρ.primeFactorsList.get := by
    funext j
    simp [fac]
  rw [e, ← List.prod_ofFn, List.ofFn_get, Nat.prod_primeFactorsList hρ]

/-- The prime factors of the product of a monotone tuple of primes are the tuple. -/
theorem fac_prod {ℓ : ℕ} {q : Fin ℓ → ℕ} (hq : ∀ j, (q j).Prime) (hm : Monotone q) (j : Fin ℓ) :
    fac (∏ j, q j) j = q j := by
  rw [fac, ← ofFn_eq_primeFactorsList hq hm, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.2),
    List.getElem_ofFn]

/-- The number of prime factors of the product of `ℓ` primes is `ℓ`. -/
theorem length_prod {ℓ : ℕ} {q : Fin ℓ → ℕ} (hq : ∀ j, (q j).Prime) (hm : Monotone q) :
    (∏ j, q j).primeFactorsList.length = ℓ := by
  rw [← ofFn_eq_primeFactorsList hq hm, List.length_ofFn]

/-- **The expansion.** Let `P` be a predicate on the pairs `(p, ρ)` of `k` primes and `m` integers, under which every
`ρ_i` free of primes below `p_{s(i)}` has at most `R` prime factors. The pairs in `[1, Y]` with `ρ_i` free of primes
below `p_{s(i)}` and `P p ρ` number the sum over the patterns `len ≤ R` of the expanded tuples of primes up to `Y`
with monotone blocks whose products are at most `Y`, every prime of block `i` at least `p_{s(i)}`, and `P` at
`(p, ∏ blocks)`. -/
theorem card_expand {k m : ℕ} (s : Fin m → Fin k) (Y R : ℕ) (P : (Fin k → ℕ) → (Fin m → ℕ) → Prop)
    (hR : ∀ x ∈ pairs k m Y, (∀ i, SieveTree.rough (x.1 (s i)) (x.2 i)) → P x.1 x.2 →
      ∀ i, (x.2 i).primeFactorsList.length ≤ R) :
    #{x ∈ pairs k m Y | (∀ i, SieveTree.rough (x.1 (s i)) (x.2 i)) ∧ P x.1 x.2} =
      ∑ len ∈ Fintype.piFinset (fun _ : Fin m => range (R + 1)),
        #{g ∈ tuplesOf k m Y len | (∀ i, Monotone (block g i)) ∧ (∀ i, ∏ j, block g i j ≤ Y) ∧
          (∀ i j, g (Sum.inl (s i)) ≤ block g i j) ∧ P (contract g).1 (contract g).2} := by
  set S := (pairs k m Y).filter fun x => (∀ i, SieveTree.rough (x.1 (s i)) (x.2 i)) ∧ P x.1 x.2 with hS
  -- split by the numbers of prime factors
  have hmaps : ∀ x ∈ S, (fun i => (x.2 i).primeFactorsList.length) ∈
      Fintype.piFinset (fun _ : Fin m => range (R + 1)) := fun x hx => by
    obtain ⟨hxp, hr, hP⟩ := mem_filter.1 hx
    exact Fintype.mem_piFinset.2 fun i => mem_range.2 (Nat.lt_succ_of_le (hR x hxp hr hP i))
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun len hlen => ?_
  -- one pattern: a bijection with the expanded tuples
  refine card_nbij' (expand len) contract ?_ ?_ ?_ ?_
  · -- `expand` maps into the expanded tuples
    intro x hx
    rw [mem_coe, mem_filter] at hx
    obtain ⟨hxS, hlenx⟩ := hx
    obtain ⟨hxp, hr, hP⟩ := mem_filter.1 hxS
    obtain ⟨hp, hρ⟩ := mem_product.1 hxp
    have hρ0 : ∀ i, x.2 i ≠ 0 := fun i => by
      have := mem_Icc.1 (Fintype.mem_piFinset.1 hρ i); omega
    have hρY : ∀ i, x.2 i ≤ Y := fun i => (mem_Icc.1 (Fintype.mem_piFinset.1 hρ i)).2
    have hl : ∀ i, (x.2 i).primeFactorsList.length = len i := fun i => congrFun hlenx i
    -- the factor at a position below the length
    have hget : ∀ i (j : Fin (len i)), fac (x.2 i) j ∈ (x.2 i).primeFactorsList := fun i j => by
      rw [fac, List.getD_eq_getElem _ _ (by rw [hl i]; exact j.2)]
      exact List.getElem_mem _
    rw [mem_coe, mem_filter]
    have hc : contract (expand len x) = x := by
      refine Prod.ext rfl (funext fun i => ?_)
      exact prod_fac (hρ0 i) (hl i)
    refine ⟨Fintype.mem_piFinset.2 fun a => ?_, fun i => ?_, fun i => ?_, fun i j => ?_, ?_⟩
    · rcases a with a | ⟨i, j⟩
      · exact Fintype.mem_piFinset.1 hp a
      · have hm := hget i j
        exact SieveTypeIIU.mem_primesLe.2 ⟨(Nat.le_of_mem_primeFactorsList hm).trans (hρY i),
          Nat.prime_of_mem_primeFactorsList hm⟩
    · -- the blocks are monotone: the sorted list
      intro j j' hjj'
      have hs := Nat.primeFactorsList_sorted (x.2 i)
      rw [List.sortedLE_iff_getElem_le_getElem_of_le] at hs
      simp only [block, expand, Sum.elim_inr, fac]
      rw [List.getD_eq_getElem _ _ (by rw [hl i]; exact j.2), List.getD_eq_getElem _ _ (by rw [hl i]; exact j'.2)]
      exact hs hjj'
    · -- the product of a block is `ρ_i ≤ Y`
      have := congrFun (congrArg Prod.snd hc) i
      simp only [contract] at this
      rw [this]
      exact hρY i
    · -- every factor is at least the sifting prime
      have hm := hget i j
      by_contra hlt
      exact hr i _ (not_le.1 hlt) (Nat.prime_of_mem_primeFactorsList hm) (Nat.dvd_of_mem_primeFactorsList hm)
    · -- `P` at the contracted pair, which is `(p, ρ)`
      rw [hc]
      exact hP
  · -- `contract` maps into the pairs of the pattern
    intro g hg
    rw [mem_coe, mem_filter] at hg
    obtain ⟨hgT, hmono, hY, hsift, hP⟩ := hg
    have hgp : ∀ a, (g a).Prime ∧ g a ≤ Y := fun a => by
      have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT a)
      exact ⟨this.2, this.1⟩
    have hbp : ∀ i j, (block g i j).Prime := fun i j => (hgp _).1
    have hpos : ∀ i, 0 < ∏ j, block g i j := fun i => prod_pos fun j _ => (hbp i j).pos
    rw [mem_coe, mem_filter, mem_filter]
    refine ⟨⟨mem_product.2 ⟨Fintype.mem_piFinset.2 fun a => SieveTypeIIU.mem_primesLe.2 ⟨(hgp _).2, (hgp _).1⟩,
      Fintype.mem_piFinset.2 fun i => mem_Icc.2 ⟨hpos i, hY i⟩⟩, fun i => ?_, hP⟩, ?_⟩
    · -- the product of a block is free of primes below the sifting prime
      intro q hq hqp hqd
      simp only [contract] at hq hqd
      obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
      have := (Nat.prime_dvd_prime_iff_eq hqp (hbp i j)).1 hj
      have := hsift i j
      omega
    · -- its number of prime factors is the block's length
      funext i
      exact length_prod (hbp i) (hmono i)
  · -- the left inverse
    intro x hx
    rw [mem_coe, mem_filter] at hx
    obtain ⟨hxS, hlenx⟩ := hx
    obtain ⟨hxp, -, -⟩ := mem_filter.1 hxS
    obtain ⟨-, hρ⟩ := mem_product.1 hxp
    refine Prod.ext rfl (funext fun i => ?_)
    have hρ0 : x.2 i ≠ 0 := by
      have := mem_Icc.1 (Fintype.mem_piFinset.1 hρ i); omega
    exact prod_fac hρ0 (congrFun hlenx i)
  · -- the right inverse
    intro g hg
    rw [mem_coe, mem_filter] at hg
    obtain ⟨hgT, hmono, -, -, -⟩ := hg
    have hbp : ∀ i j, (block g i j).Prime := fun i j =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT _)).2
    funext a
    rcases a with a | ⟨i, j⟩
    · rfl
    · exact fac_prod (hbp i) (hmono i) j

end ShortSieveExpand

#print axioms ShortSieveExpand.card_expand
