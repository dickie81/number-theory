import ShortSieveRoot

/-!
# The top of Li's decomposition: exact identities in an interval

For an interval `I = (x − y, x]`, `S(I_d, z)` counts the `m` free of primes below `z` with `dm ∈ I` (`sD`).

* `sD_buchstab`: **Buchstab's identity**, `S(I_d, z) = S(I_d, P) + Σ_{z ≤ p < P} S(I_{dp}, p)` for `z ≤ P`, from
  `ShortSieveBuch.rough_eq_add` (an `m` free of primes below `z` but not below `P` is `p·m′` with `p` its least
  prime factor and `m′` free of primes below `p`).
* `card_primes_ge_sD`: the primes of `I` are at least `S(I, ⌊√x⌋ + 1)` when `x − y ≥ 1`.
* `top_identity`: Li's identity (his (9)) in any interval: with `z₁ ≤ z₂` and levels `L_p ≤ p`,
  `S(I, z₂) = S(I, z₁) − Σ_{z₁ ≤ p < z₂} S(I_p, L_p) + Σ_{z₁ ≤ p < z₂} Σ_{L_p ≤ q < p} S(I_{pq}, q)`.
-/

open Finset Real Filter

namespace ShortSieveTop

open Classical

/-- `S(I_d, z)`: the `m ≤ x` free of primes below `z` with `dm ∈ (x − y, x]`. -/
noncomputable def sD (d z : ℕ) (x y : ℝ) : ℕ :=
  #{m ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z m ∧ x - y < ((d * m : ℕ) : ℝ) ∧ ((d * m : ℕ) : ℝ) ≤ x}

/-- **Buchstab's identity on an interval.** For `d ≥ 1` and `z ≤ P`:
`S(I_d, z) = S(I_d, P) + Σ_{z ≤ p < P} S(I_{dp}, p)`. -/
theorem sD_buchstab {d z P : ℕ} (hd : 1 ≤ d) (hzP : z ≤ P) (x y : ℝ) :
    sD d z x y = sD d P x y + ∑ p ∈ SieveTree.primesIco z P, sD (d * p) p x y := by
  set W : ℕ → Prop := fun n => x - y < (n : ℝ) ∧ (n : ℝ) ≤ x with hW
  set R := {m ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z m ∧ ¬ SieveTree.rough P m ∧ W (d * m)} with hR
  -- split by roughness for `P`
  have hsplit : sD d z x y = sD d P x y + #R := by
    unfold sD
    rw [← card_union_of_disjoint]
    · congr 1
      ext m
      simp only [mem_filter, mem_union, hR, hW]
      constructor
      · rintro ⟨hm, hz, hw⟩
        by_cases hP : SieveTree.rough P m
        · exact Or.inl ⟨hm, hP, hw⟩
        · exact Or.inr ⟨hm, hz, hP, hw⟩
      · rintro (⟨hm, hP, hw⟩ | ⟨hm, hz, -, hw⟩)
        · exact ⟨hm, SieveTree.rough_mono hzP hP, hw⟩
        · exact ⟨hm, hz, hw⟩
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [mem_filter, hR] at hm hm'
      exact hm'.2.2.1 hm.2.1
  rw [hsplit]
  congr 1
  -- the rest, by the least prime factor
  have hmaps : (R : Set ℕ).MapsTo Nat.minFac (SieveTree.primesIco z P) := by
    intro m hm
    rw [mem_coe, hR, mem_filter, mem_Icc] at hm
    obtain ⟨⟨hm1, -⟩, hz, hP, -⟩ := hm
    have hm1' : m ≠ 1 := by
      rintro rfl
      exact hP fun p _ hp hdvd => hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
    have hmp := Nat.minFac_prime hm1'
    rw [mem_coe, SieveTree.primesIco, mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, hmp⟩
    · by_contra hlt
      exact hz _ (not_le.1 hlt) hmp (Nat.minFac_dvd m)
    · by_contra hle
      apply hP
      intro p hp hpp hdvd
      have := Nat.minFac_le_of_dvd hpp.two_le hdvd
      omega
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := (mem_filter.1 hp).2
  have hpz : z ≤ p := (mem_Ico.1 (mem_filter.1 hp).1).1
  have hpP : p < P := (mem_Ico.1 (mem_filter.1 hp).1).2
  unfold sD
  refine card_nbij' (fun m => m / p) (fun m' => p * m') (fun m hm => ?_) (fun m' hm' => ?_)
    (fun m hm => ?_) (fun m' hm' => ?_)
  · -- `m ↦ m/p`
    rw [mem_coe, mem_filter, hR, mem_filter, mem_Icc] at hm
    obtain ⟨⟨⟨hm1, hmx⟩, hz, -, hw⟩, hmin⟩ := hm
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · obtain rfl : m = 1 := by omega
        rw [Nat.minFac_one] at hmin; exact absurd hmin hpp.one_lt.ne
      · exact h
    obtain ⟨hdvd, hrough⟩ := (ShortSieveBuch.dvd_rough_div_iff hpp hm2).2 hmin.symm
    rw [mem_coe, mem_filter, mem_Icc]
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpp.pos, le_trans (Nat.div_le_self m p) hmx⟩,
      hrough, ?_⟩
    rw [mul_assoc, Nat.mul_div_cancel' hdvd]
    exact hw
  · -- `m′ ↦ pm′`
    rw [mem_coe, mem_filter, mem_Icc] at hm'
    obtain ⟨⟨hm1, -⟩, hrough, hlo, hhi⟩ := hm'
    have hm2 : 2 ≤ p * m' := le_trans hpp.two_le (Nat.le_mul_of_pos_right p hm1)
    have hdm : (d * (p * m') : ℕ) = d * p * m' := by ring
    rw [mem_coe, mem_filter, hR, mem_filter, mem_Icc]
    have hmin : Nat.minFac (p * m') = p := by
      refine ((ShortSieveBuch.dvd_rough_div_iff hpp hm2).1 ⟨Dvd.intro m' rfl, ?_⟩).symm
      rwa [Nat.mul_div_cancel_left m' hpp.pos]
    refine ⟨⟨⟨le_trans (by norm_num) hm2, ?_⟩, ?_, ?_, ?_⟩, hmin⟩
    · apply Nat.le_floor
      have h1 : ((p * m' : ℕ) : ℝ) ≤ ((d * p * m' : ℕ) : ℝ) := by
        exact_mod_cast (show p * m' ≤ d * p * m' by nlinarith)
      exact le_trans h1 hhi
    · -- free of primes below `z`
      intro r hr hrp hrd
      have h1 := Nat.minFac_le_of_dvd hrp.two_le hrd
      rw [hmin] at h1
      omega
    · -- not free of primes below `P`
      intro h
      exact h p hpP hpp (Dvd.intro m' rfl)
    · rw [hdm]; exact ⟨hlo, hhi⟩
  · -- left inverse
    rw [mem_coe, mem_filter, hR, mem_filter, mem_Icc] at hm
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · obtain rfl : m = 1 := by omega
        rw [Nat.minFac_one] at hm; exact absurd hm.2 hpp.one_lt.ne
      · exact h
    have hdvd : p ∣ m := hm.2 ▸ Nat.minFac_dvd m
    exact Nat.mul_div_cancel' hdvd
  · -- right inverse
    exact Nat.mul_div_cancel_left m' hpp.pos

/-- The primes of `(x − y, x]` are at least `S(I, ⌊√x⌋ + 1)` when `x − y ≥ 1`: an `n ≤ x` free of primes up to
`√x` is `1` or a prime. -/
theorem card_primes_ge_sD {x y : ℝ} (hxy : 1 ≤ x - y) :
    sD 1 (⌊Real.sqrt x⌋₊ + 1) x y ≤ ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  unfold sD
  refine card_le_card_of_injOn id (fun n hn => ?_) (fun _ _ _ _ h => h)
  rw [mem_coe, mem_filter, mem_Icc] at hn
  obtain ⟨⟨hn1, hnx⟩, hr, hlo, hhi⟩ := hn
  rw [one_mul] at hlo hhi
  have hn1' : n ≠ 1 := by
    rintro rfl
    push_cast at hlo
    linarith
  have hn2 : 2 ≤ n := by omega
  have hnp : n.Prime := by
    by_contra hnp
    have hmf := Nat.minFac_sq_le_self (by omega) hnp
    have hmp := Nat.minFac_prime hn1'
    -- `minFac n ≤ √x < ⌊√x⌋ + 1`
    have h1 : ((Nat.minFac n : ℕ) : ℝ) ^ 2 ≤ x := by
      have : ((Nat.minFac n ^ 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hmf
      push_cast at this
      linarith
    have h2 : (Nat.minFac n : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le h1
    have h3 : Nat.minFac n < ⌊Real.sqrt x⌋₊ + 1 := Nat.lt_succ_of_le (Nat.le_floor h2)
    exact hr _ h3 hmp (Nat.minFac_dvd n)
  rw [mem_coe, mem_filter, mem_Ioc]
  refine ⟨⟨?_, hnx⟩, hnp⟩
  have : (⌊x - y⌋₊ : ℝ) < n := lt_of_le_of_lt (Nat.floor_le (by linarith)) (by exact_mod_cast hlo)
  exact_mod_cast this

/-- **Li's identity on an interval.** With `1 ≤ z₁ ≤ z₂` and levels `L_p ≤ p` for the primes `p ∈ [z₁, z₂)`:
`S(I, z₂) = S(I, z₁) − Σ_p S(I_p, L_p) + Σ_p Σ_{L_p ≤ q < p} S(I_{pq}, q)`. -/
theorem top_identity {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) (L : ℕ → ℕ)
    (hL : ∀ p ∈ SieveTree.primesIco z₁ z₂, L p ≤ p) (x y : ℝ) :
    (sD 1 z₂ x y : ℤ) = sD 1 z₁ x y - ∑ p ∈ SieveTree.primesIco z₁ z₂, (sD p (L p) x y : ℤ) +
      ∑ p ∈ SieveTree.primesIco z₁ z₂, ∑ q ∈ SieveTree.primesIco (L p) p, (sD (p * q) q x y : ℤ) := by
  have h1 := sD_buchstab (d := 1) le_rfl hz x y
  have h2 : ∀ p ∈ SieveTree.primesIco z₁ z₂, (sD p p x y : ℤ) =
      sD p (L p) x y - ∑ q ∈ SieveTree.primesIco (L p) p, (sD (p * q) q x y : ℤ) := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_filter.1 hp).2.one_lt.le
    have := sD_buchstab (d := p) hp1 (hL p hp) x y
    push_cast [this]
    ring
  have h1' : (sD 1 z₁ x y : ℤ) = sD 1 z₂ x y + ∑ p ∈ SieveTree.primesIco z₁ z₂, (sD p p x y : ℤ) := by
    rw [h1]
    push_cast
    simp only [one_mul]
  rw [h1', sum_congr rfl h2, sum_sub_distrib]
  ring

/-! ### The root terms as `S(I_d, z)` -/

/-- `S(I, x^ν)` is `sD 1 ⌈x^ν⌉`. -/
theorem sOne_eq (ν x y : ℝ) : ShortSieveRoot.sOne ν x y = sD 1 ⌈x ^ ν⌉₊ x y := by
  unfold ShortSieveRoot.sOne ShortSieveJ.sA sD
  simp

/-- One prime's `S(I_p, x^ν)` is `sD p ⌈x^ν⌉`. -/
theorem sA_one_eq (ν x y : ℝ) (g : Fin 1 → ℕ) : ShortSieveJ.sA ν x y g = sD (g 0) ⌈x ^ ν⌉₊ x y := by
  unfold ShortSieveJ.sA sD
  rw [Fin.prod_univ_one]

/-- The second root term as a sum over primes: `Σ_{x^a < p ≤ x^b} S(I_p, ⌈x^{ν(log p/log x)}⌉)`. -/
theorem sTwo_eq (ν : ℝ → ℝ) (a b x y : ℝ) :
    ShortSieveRoot.sTwo ν a b x y =
      ∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        (sD p ⌈x ^ ν (Real.log p / Real.log x)⌉₊ x y : ℝ) := by
  unfold ShortSieveRoot.sTwo
  have hinj : Set.InjOn (fun g : Fin 1 → ℕ => g 0)
      (ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊) : Set (Fin 1 → ℕ)) := by
    intro g _ g' _ h
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact h
  have himg : (ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊)).image (fun g => g 0) =
      (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime := by
    ext p
    rw [mem_image, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h1, h2, h3⟩ := ShortSieveRoot.mem_tuples_one.1 hg
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun _ => p, ShortSieveRoot.mem_tuples_one.2 ⟨h1, h2, h3⟩, rfl⟩
  rw [← himg, sum_image hinj]
  refine sum_congr rfl fun g _ => ?_
  rw [sA_one_eq]

end ShortSieveTop

#print axioms ShortSieveTop.sD_buchstab
#print axioms ShortSieveTop.card_primes_ge_sD
#print axioms ShortSieveTop.top_identity
