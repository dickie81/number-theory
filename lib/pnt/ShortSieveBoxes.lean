import SieveDecomp
import ShortSieveGroup

/-!
# Sieve terms as counts over boxes of primes

The terms of Li's decomposition count the `n` of an interval with `P ∣ n` and `n/P` free of primes below a threshold
`z`, summed over tuples of primes `P = p₁ ⋯ p_k`. The Type II estimates of `ShortSieveGroup` count tuples of primes
in boxes `(Nⱼ, Mⱼ]` by their products. This module joins the two:

* `card_dvd_rough_eq_sum`: **rough cofactors as sorted tuples of primes.** The cofactor `n/P` is the product of the
  monotone tuple of its prime factors (`monoPrimes`), and that tuple is unique (`ofFn_eq_primeFactorsList`): the `n`
  of a set `I ⊆ [1, Y]` with `P ∣ n` and `n/P` free of primes below `z` number
  `Σ_{r ≤ R} #{q monotone, primes in [z, Y], P·∏q ∈ I}` once `z^{R+1} > Y`.
* `abs_sum_sub_le_boxes`: **the box sandwich.** A finite set `S` split into classes `J`, each inside a set `full J`
  on which the two weights `f_A`, `f_B` compare with error `E`, satisfies
  `|Σ_S f_A − c Σ_S f_B| ≤ #classes·E + c Σ_J t J` when `t J ≥ Σ_{full J} f_B` for the classes `J` that straddle `S`
  (meet it without lying in it). Classes inside `S` cost `E`, classes outside cost nothing, and a straddling class
  costs at most the larger of its two sides, which the comparison on `full J` bounds by `c Σ_{full J} f_B + E`.
* The grid of boxes: for a finite set `G` of naturals, `nextG G e` is the least point of `G` above `e` and `idxG G p`
  the greatest point of `G` below `p`, so `p ∈ (idxG G p, nextG G (idxG G p)]` for `min G < p ≤ max G`
  (`mem_box_idxG`); a tuple of primes lies in the tuples of its boxes (`mem_tuples_idxG`).
-/

open Finset

namespace ShortSieveBoxes

open Classical

/-! ### Rough cofactors as sorted tuples of primes -/

/-- The monotone `r`-tuples of primes in `[z, Y]`. -/
noncomputable def monoPrimes (r z Y : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ : Fin r => (Icc z Y).filter Nat.Prime).filter fun q => Monotone q

theorem mem_monoPrimes {r z Y : ℕ} {q : Fin r → ℕ} :
    q ∈ monoPrimes r z Y ↔ (∀ i, z ≤ q i ∧ q i ≤ Y ∧ (q i).Prime) ∧ Monotone q := by
  simp only [monoPrimes, mem_filter, Fintype.mem_piFinset, mem_Icc, and_assoc]

/-- A monotone tuple of primes is the sorted list of the prime factors of its product. -/
theorem ofFn_eq_primeFactorsList {r : ℕ} {q : Fin r → ℕ} (hq : ∀ i, (q i).Prime) (hm : Monotone q) :
    List.ofFn q = (∏ i, q i).primeFactorsList := by
  have hperm : List.Perm (List.ofFn q) (∏ i, q i).primeFactorsList := by
    refine Nat.primeFactorsList_unique List.prod_ofFn fun p hp => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
    exact hq i
  exact hperm.eq_of_sortedLE (List.sortedLE_ofFn_iff.2 hm) (Nat.primeFactorsList_sorted _)

/-- A product of `r` numbers at least `z` is at least `z^r`. -/
theorem pow_le_prod {r z : ℕ} {q : Fin r → ℕ} (hq : ∀ i, z ≤ q i) : z ^ r ≤ ∏ i, q i := by
  calc z ^ r = ∏ _i : Fin r, z := by simp
    _ ≤ ∏ i, q i := prod_le_prod fun i _ => hq i

/-- **Rough cofactors as sorted tuples of primes.** Let `P ≥ 1` and `I` a finite set of naturals in `[1, Y]` with
`Y < z^{R+1}`. The `n ∈ I` with `P ∣ n` and `n/P` free of primes below `z` are the products `P·∏q` of the monotone
`r`-tuples `q` of primes in `[z, Y]`, `r ≤ R`, one `q` for each `n`. -/
theorem card_dvd_rough_eq_sum {P z Y R : ℕ} (hP : 0 < P) (I : Finset ℕ) (hI : ∀ n ∈ I, 0 < n ∧ n ≤ Y)
    (hR : Y < z ^ (R + 1)) :
    #{n ∈ I | P ∣ n ∧ SieveTree.rough z (n / P)} =
      ∑ r ∈ range (R + 1), #{q ∈ monoPrimes r z Y | P * ∏ i, q i ∈ I} := by
  rw [← card_sigma]
  symm
  refine card_nbij' (fun x => P * ∏ i, x.2 i)
    (fun n => ⟨(n / P).primeFactorsList.length, fun i => (n / P).primeFactorsList.get i⟩) ?_ ?_ ?_ ?_
  · -- the products lie in the left side
    rintro ⟨r, q⟩ hx
    rw [mem_coe, mem_sigma, mem_filter, mem_monoPrimes] at hx
    obtain ⟨-, ⟨hq, -⟩, hI'⟩ := hx
    rw [mem_coe, mem_filter]
    refine ⟨hI', Dvd.intro _ rfl, ?_⟩
    dsimp only
    rw [Nat.mul_div_cancel_left _ hP]
    intro p hpz hp hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp (hq i).2.2).1 hi
    have := (hq i).1
    omega
  · -- the sorted prime factors of the cofactor
    intro n hn
    rw [mem_coe, mem_filter] at hn
    obtain ⟨hnI, hPn, hr⟩ := hn
    obtain ⟨hn0, hnY⟩ := hI n hnI
    set m := n / P with hm
    have hm0 : m ≠ 0 := by
      rw [hm]
      exact (Nat.div_pos (Nat.le_of_dvd hn0 hPn) hP).ne'
    have hmn : m ≤ n := Nat.div_le_self n P
    have hmem : ∀ i : Fin m.primeFactorsList.length,
        z ≤ m.primeFactorsList.get i ∧ m.primeFactorsList.get i ≤ Y ∧ (m.primeFactorsList.get i).Prime := by
      intro i
      have hi : m.primeFactorsList.get i ∈ m.primeFactorsList := List.get_mem _ _
      have hp := Nat.prime_of_mem_primeFactorsList hi
      refine ⟨?_, (Nat.le_of_mem_primeFactorsList hi).trans (hmn.trans hnY), hp⟩
      by_contra hlt
      exact hr _ (not_le.1 hlt) hp (Nat.dvd_of_mem_primeFactorsList hi)
    have hprod : ∏ i, m.primeFactorsList.get i = m := by
      rw [← List.prod_ofFn, List.ofFn_get, Nat.prod_primeFactorsList hm0]
    rw [mem_coe, mem_sigma, mem_range, mem_filter, mem_monoPrimes]
    refine ⟨?_, ⟨hmem, Nat.primeFactorsList_sorted m⟩, ?_⟩
    · -- `z^r ≤ m ≤ Y < z^{R+1}`
      have h1 : z ^ m.primeFactorsList.length ≤ m := by
        have := pow_le_prod (q := fun i => m.primeFactorsList.get i) fun i => (hmem i).1
        rwa [hprod] at this
      have h2 : z ^ m.primeFactorsList.length < z ^ (R + 1) := lt_of_le_of_lt (h1.trans (hmn.trans hnY)) hR
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hR
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hR
        omega
      have hz : 1 < z := by omega
      exact (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    · dsimp only
      rw [hprod, hm, Nat.mul_div_cancel' hPn]
      exact hnI
  · -- the left inverse: the sorted factors of `∏q` are `q`
    rintro ⟨r, q⟩ hx
    rw [mem_coe, mem_sigma, mem_filter, mem_monoPrimes] at hx
    obtain ⟨-, ⟨hq, hmono⟩, -⟩ := hx
    dsimp only
    rw [Nat.mul_div_cancel_left _ hP]
    have h := ofFn_eq_primeFactorsList (fun i => (hq i).2.2) hmono
    rw [← List.ofFn_inj', ← h, List.ofFn_get]
  · -- the right inverse
    intro n hn
    rw [mem_coe, mem_filter] at hn
    obtain ⟨hnI, hPn, -⟩ := hn
    have hn0 := (hI n hnI).1
    have hm0 : n / P ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn0 hPn) hP).ne'
    show P * ∏ i, (n / P).primeFactorsList.get i = n
    rw [← List.prod_ofFn, List.ofFn_get, Nat.prod_primeFactorsList hm0, Nat.mul_div_cancel' hPn]

/-! ### The box sandwich -/

/-- **The box sandwich.** Let `S` be split by `box` into classes `J ∈ Js`, with `g ∈ full (box g)` for `g ∈ S`, and
let `f_A, f_B ≥ 0`, `c ≥ 0`. If every class `J` that meets `S` has `|Σ_{full J} f_A − c Σ_{full J} f_B| ≤ E`, and every
class that meets `S` without lying in it has `Σ_{full J} f_B ≤ t J`, with `t ≥ 0`, then
`|Σ_S f_A − c Σ_S f_B| ≤ #Js·E + c Σ_J t J`. -/
theorem abs_sum_sub_le_boxes {α κ : Type*} (S : Finset α) (Js : Finset κ) (box : α → κ)
    (hbox : ∀ g ∈ S, box g ∈ Js) (full : κ → Finset α) (hfull : ∀ g ∈ S, g ∈ full (box g))
    {fA fB : α → ℝ} (hA : ∀ g, 0 ≤ fA g) (hB : ∀ g, 0 ≤ fB g) {c E : ℝ} (hc : 0 ≤ c) (hE0 : 0 ≤ E)
    (hE : ∀ J ∈ Js, (∃ g ∈ S, box g = J) →
      |∑ g ∈ full J, fA g - c * ∑ g ∈ full J, fB g| ≤ E)
    (t : κ → ℝ) (ht0 : ∀ J ∈ Js, 0 ≤ t J)
    (ht : ∀ J ∈ Js, (∃ g ∈ S, box g = J) → (∃ g ∈ full J, ¬ (g ∈ S ∧ box g = J)) →
      ∑ g ∈ full J, fB g ≤ t J) :
    |∑ g ∈ S, fA g - c * ∑ g ∈ S, fB g| ≤ Js.card * E + c * ∑ J ∈ Js, t J := by
  set T : κ → Finset α := fun J => S.filter (box · = J) with hT
  have hTsub : ∀ J, T J ⊆ full J := fun J g hg => by
    obtain ⟨hgS, rfl⟩ := mem_filter.1 hg
    exact hfull g hgS
  have hsplit : ∀ f : α → ℝ, ∑ g ∈ S, f g = ∑ J ∈ Js, ∑ g ∈ T J, f g := fun f =>
    (sum_fiberwise_of_maps_to hbox f).symm
  -- the bound for one class
  have hone : ∀ J ∈ Js, |∑ g ∈ T J, fA g - c * ∑ g ∈ T J, fB g| ≤ E + c * t J := by
    intro J hJ
    have hct : 0 ≤ c * t J := mul_nonneg hc (ht0 J hJ)
    by_cases hmeet : ∃ g ∈ S, box g = J
    · by_cases hstr : ∃ g ∈ full J, ¬ (g ∈ S ∧ box g = J)
      · have hEJ := abs_le.1 (hE J hJ hmeet)
        have htJ := ht J hJ hmeet hstr
        have hAT : ∑ g ∈ T J, fA g ≤ ∑ g ∈ full J, fA g := sum_le_sum_of_subset_of_nonneg (hTsub J)
          fun g _ _ => hA g
        have hBT : ∑ g ∈ T J, fB g ≤ ∑ g ∈ full J, fB g := sum_le_sum_of_subset_of_nonneg (hTsub J)
          fun g _ _ => hB g
        have hA0 : 0 ≤ ∑ g ∈ T J, fA g := sum_nonneg fun g _ => hA g
        have hB0 : 0 ≤ ∑ g ∈ T J, fB g := sum_nonneg fun g _ => hB g
        have hcB : c * ∑ g ∈ T J, fB g ≤ c * ∑ g ∈ full J, fB g := mul_le_mul_of_nonneg_left hBT hc
        have hcB' : c * ∑ g ∈ full J, fB g ≤ c * t J := mul_le_mul_of_nonneg_left htJ hc
        rw [abs_le]
        constructor <;> nlinarith [mul_nonneg hc hB0]
      · push Not at hstr
        have heq : T J = full J := by
          refine Subset.antisymm (hTsub J) fun g hg => ?_
          obtain ⟨hgS, hgJ⟩ := hstr g hg
          exact mem_filter.2 ⟨hgS, hgJ⟩
        rw [heq]
        exact (hE J hJ hmeet).trans (le_add_of_nonneg_right hct)
    · have h0 : T J = ∅ := by
        refine filter_eq_empty_iff.2 fun g hg hgJ => hmeet ⟨g, hg, hgJ⟩
      rw [h0]
      simpa using add_nonneg hE0 hct
  rw [hsplit fA, hsplit fB, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum hone).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]

/-! ### The grid of boxes -/

/-- The least point of `G` above `e` (or `e` itself when there is none). -/
noncomputable def nextG (G : Finset ℕ) (e : ℕ) : ℕ :=
  if h : (G.filter (e < ·)).Nonempty then (G.filter (e < ·)).min' h else e

/-- The greatest point of `G` below `p` (or `0` when there is none). -/
noncomputable def idxG (G : Finset ℕ) (p : ℕ) : ℕ :=
  if h : (G.filter (· < p)).Nonempty then (G.filter (· < p)).max' h else 0

/-- The index of `p` is a point of `G` below `p`, when one exists. -/
theorem idxG_mem {G : Finset ℕ} {p : ℕ} (h : ∃ e ∈ G, e < p) : idxG G p ∈ G ∧ idxG G p < p := by
  have hne : (G.filter (· < p)).Nonempty := by
    obtain ⟨e, he, hep⟩ := h
    exact ⟨e, mem_filter.2 ⟨he, hep⟩⟩
  rw [idxG, dite_eq_left hne]
  exact mem_filter.1 (max'_mem _ hne)

/-- No point of `G` lies strictly between the index of `p` and `p`. -/
theorem le_idxG {G : Finset ℕ} {p e : ℕ} (he : e ∈ G) (hep : e < p) : e ≤ idxG G p := by
  have hne : (G.filter (· < p)).Nonempty := ⟨e, mem_filter.2 ⟨he, hep⟩⟩
  rw [idxG, dite_eq_left hne]
  exact le_max' _ e (mem_filter.2 ⟨he, hep⟩)

/-- The next point above `e`, when one exists, is a point of `G` above `e` with none in between. -/
theorem nextG_spec {G : Finset ℕ} {e : ℕ} (h : ∃ e' ∈ G, e < e') :
    nextG G e ∈ G ∧ e < nextG G e ∧ ∀ e' ∈ G, e < e' → nextG G e ≤ e' := by
  have hne : (G.filter (e < ·)).Nonempty := by
    obtain ⟨e', he', hee'⟩ := h
    exact ⟨e', mem_filter.2 ⟨he', hee'⟩⟩
  rw [nextG, dite_eq_left hne]
  refine ⟨(mem_filter.1 (min'_mem _ hne)).1, (mem_filter.1 (min'_mem _ hne)).2, fun e' he' hee' => ?_⟩
  exact min'_le _ e' (mem_filter.2 ⟨he', hee'⟩)

/-- **A number lies in its box.** If some point of `G` lies below `p` and some point at or above it, then
`idxG G p < p ≤ nextG G (idxG G p)`. -/
theorem mem_box_idxG {G : Finset ℕ} {p : ℕ} (hlo : ∃ e ∈ G, e < p) (hhi : ∃ e ∈ G, p ≤ e) :
    idxG G p < p ∧ p ≤ nextG G (idxG G p) := by
  obtain ⟨hmem, hlt⟩ := idxG_mem hlo
  refine ⟨hlt, ?_⟩
  obtain ⟨e, he, hpe⟩ := hhi
  obtain ⟨hnm, hnlt, hnmin⟩ := nextG_spec ⟨e, he, lt_of_lt_of_le hlt hpe⟩
  by_contra hcon
  push Not at hcon
  -- `nextG < p` is a point of `G` below `p` above the index
  have := le_idxG hnm hcon
  omega

/-- **A tuple of primes lies in the tuples of its boxes.** -/
theorem mem_tuples_idxG {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Finset ℕ} {g : ι → ℕ}
    (hp : ∀ j, (g j).Prime) (hlo : ∀ j, ∃ e ∈ G, e < g j) (hhi : ∀ j, ∃ e ∈ G, g j ≤ e) :
    g ∈ ShortSieveTypeII.tuples (fun j => idxG G (g j)) (fun j => nextG G (idxG G (g j))) := by
  rw [ShortSieveTypeII.tuples, Fintype.mem_piFinset]
  intro j
  obtain ⟨h1, h2⟩ := mem_box_idxG (hlo j) (hhi j)
  exact mem_filter.2 ⟨mem_Ioc.2 ⟨h1, h2⟩, hp j⟩

end ShortSieveBoxes

#print axioms ShortSieveBoxes.card_dvd_rough_eq_sum
#print axioms ShortSieveBoxes.abs_sum_sub_le_boxes
#print axioms ShortSieveBoxes.mem_tuples_idxG
