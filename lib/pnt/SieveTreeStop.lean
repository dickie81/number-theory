/-
# Buchstab's tree with a stopping rule

Plain statements. `rough z n` and `primesIco w z` are `SieveTree`'s. A *stopping rule* is a predicate `stop` on finite
sets of primes. A branch `P` (a set of primes of `[w, z₀)`, read in decreasing order) is *alive* when none of its upper
parts `{p ∈ P | t ≤ p}` stops (`alive`).

* `alive_insert`: for `q₀` below every element of `P`, `insert q₀ P` is alive iff `P` is alive and `insert q₀ P` does
  not stop.
* `alt_cancel_stop`: for `q₀` below every element of `Q'`,
  `Σ_{P ⊆ Q' ∪ {q₀}} (−1)^{|P|}[P alive] + Σ_{P ⊆ Q'} (−1)^{|P|+1}[P alive, P ∪ {q₀} stops] = 0`.
* `tree_pt_stop`: **Buchstab's tree with a stopping rule, at one `n`.** For `w ≤ z₀`, `r` with every prime factor at
  least `z₀`, and a rule under which `∅` does not stop: `[r ∣ n, rough z₀ n]` is the leaves' sum
  `Σ_{P ⊆ [w, z₀) alive} (−1)^{|P|}[r∏P ∣ n, rough w n]` plus the stops' sum
  `Σ_{w ≤ p < z₀} Σ_{P ⊆ (p, z₀) alive, P ∪ {p} stops} (−1)^{|P|+1}[r∏P·p ∣ n, rough p n]`.
* `tree_weighted_stop`: the same summed over a finite set, with weights.
* `alive_iff_lt`, `stop_insert_iff`: **small steps.** Let the rule stop a set `P'` only when `c∏P' ≥ E`, and stop
  every `P'` with `E ≤ c∏P' < Ez₀`, for `0 ≤ c < E`. A set `P` of integers in `[1, z₀)` is alive iff `c∏P < E`; and
  then, for `p ∈ [1, z₀)` not in `P`, `P ∪ {p}` stops iff `E ≤ c∏P·p`.

The threshold tree `SieveTree.tree_pt` is the rule `X < r∏P'`. The proof of `tree_pt_stop` is `tree_pt`'s: at an `n`
with `r ∣ n` and no prime factor below `w`, the leaves that count `n` are the alive `P ⊆ Q`, `Q` the primes of
`[w, z₀)` that divide `n`, and the stops those with `p = min Q`; `alt_cancel_stop` leaves `[Q = ∅]`. The proof of
`alive_iff_lt`: the products of the upper parts of `P` grow from `c` to `c∏P` by factors below `z₀`, so if `c∏P ≥ E`
the first upper part with `c∏ ≥ E` has `c∏ < Ez₀` and stops.

The file imports `SieveDiff.lean`.
-/
import SieveDiff

open Finset

namespace SieveTreeStop

open SieveTree

/-- A branch is alive when none of its upper parts stops. -/
def alive (stop : Finset ℕ → Prop) (P : Finset ℕ) : Prop := ∀ t : ℕ, ¬ stop (P.filter (t ≤ ·))

theorem alive_empty {stop : Finset ℕ → Prop} (hs : ¬ stop ∅) : alive stop ∅ := fun t => by
  rwa [Finset.filter_empty]

/-- For `q₀` below every element of `P`: `insert q₀ P` is alive iff `P` is alive and `insert q₀ P` does not stop. -/
theorem alive_insert (stop : Finset ℕ → Prop) {q₀ : ℕ} {P : Finset ℕ} (h : ∀ p ∈ P, q₀ < p) :
    alive stop (insert q₀ P) ↔ alive stop P ∧ ¬ stop (insert q₀ P) := by
  constructor
  · intro hA
    refine ⟨fun t => ?_, ?_⟩
    · have e : P.filter (t ≤ ·) = (insert q₀ P).filter (max t (q₀ + 1) ≤ ·) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hp, ht⟩
          exact ⟨Or.inr hp, max_le ht (h p hp)⟩
        · rintro ⟨hp | hp, hm⟩
          · subst hp
            have := le_max_right t (p + 1)
            omega
          · exact ⟨hp, le_trans (le_max_left _ _) hm⟩
      rw [e]
      exact hA _
    · have e : (insert q₀ P).filter (0 ≤ ·) = insert q₀ P :=
        Finset.filter_true_of_mem fun _ _ => Nat.zero_le _
      have := hA 0
      rwa [e] at this
  · rintro ⟨hP, hs⟩ t
    by_cases ht : t ≤ q₀
    · have e : (insert q₀ P).filter (t ≤ ·) = insert q₀ P := Finset.filter_true_of_mem fun p hp => by
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact ht
        · exact le_trans ht (h p hp).le
      rw [e]
      exact hs
    · have e : (insert q₀ P).filter (t ≤ ·) = P.filter (t ≤ ·) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hp | hp, hp'⟩
          · subst hp
            exact absurd hp' ht
          · exact ⟨hp, hp'⟩
        · rintro ⟨hp, hp'⟩
          exact ⟨Or.inr hp, hp'⟩
      rw [e]
      exact hP t

open Classical in
/-- The per-`n` alternating identity: for `q₀` below every element of `Q'`,
`Σ_{P ⊆ Q' ∪ {q₀}} (−1)^{|P|}[P alive] + Σ_{P ⊆ Q'} (−1)^{|P|+1}[P alive, P ∪ {q₀} stops] = 0`. -/
theorem alt_cancel_stop (stop : Finset ℕ → Prop) (q₀ : ℕ) (Q' : Finset ℕ) (hq : ∀ p ∈ Q', q₀ < p) :
    ∑ P ∈ (insert q₀ Q').powerset, (-1 : ℤ) ^ P.card * (if alive stop P then 1 else 0) +
      ∑ P ∈ Q'.powerset, (-1 : ℤ) ^ (P.card + 1) * (if alive stop P ∧ stop (insert q₀ P) then 1 else 0) = 0 := by
  have hqQ : q₀ ∉ Q' := fun h => lt_irrefl _ (hq q₀ h)
  rw [Finset.sum_powerset_insert hqQ, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun P hP => ?_
  have hPQ := Finset.mem_powerset.1 hP
  have hqP : q₀ ∉ P := fun h => hqQ (hPQ h)
  rw [Finset.card_insert_of_notMem hqP, alive_insert stop fun p hp => hq p (hPQ hp)]
  by_cases h1 : alive stop P <;> by_cases h2 : stop (insert q₀ P) <;> simp [h1, h2] <;> ring

open Classical in
/-- **Buchstab's tree with a stopping rule, at one `n`.** For `w ≤ z₀`, `r` with all primes at least `z₀`, and a rule
under which `∅` does not stop: `[r ∣ n, rough z₀ n]` is the alive leaves' alternating sum plus the stops'. -/
theorem tree_pt_stop (n : ℕ) {r w z₀ : ℕ} (hwz : w ≤ z₀) (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p)
    (stop : Finset ℕ → Prop) (hs : ¬ stop ∅) :
    (if r ∣ n ∧ rough z₀ n then (1 : ℤ) else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
          (if alive stop P then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if alive stop P ∧ stop (insert p P) then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  have hPprime : ∀ P ∈ (primesIco w z₀).powerset, ∀ p ∈ P, p.Prime := fun P hP p hp =>
    (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).2.2
  by_cases hb : r ∣ n ∧ rough w n
  · obtain ⟨hrn, hwn⟩ := hb
    set Q := (primesIco w z₀).filter (· ∣ n) with hQ
    have hQsub : Q ⊆ primesIco w z₀ := Finset.filter_subset _ _
    have hmemQ : ∀ p, p ∈ Q ↔ (w ≤ p ∧ p < z₀ ∧ p.Prime) ∧ p ∣ n := fun p => by
      rw [hQ, Finset.mem_filter, mem_primesIco]
    -- the left side
    have hL : (r ∣ n ∧ rough z₀ n) ↔ Q = ∅ := by
      constructor
      · rintro ⟨-, hz⟩
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        obtain ⟨⟨-, hpz, hpp⟩, hpn⟩ := (hmemQ p).1 hp
        exact hz p hpz hpp hpn
      · intro hQe
        refine ⟨hrn, fun p hpz hpp hpn => ?_⟩
        by_cases hpw : p < w
        · exact hwn p hpw hpp hpn
        · have : p ∈ Q := (hmemQ p).2 ⟨⟨not_lt.1 hpw, hpz, hpp⟩, hpn⟩
          rw [hQe] at this
          exact Finset.notMem_empty p this
    -- the leaves: `r∏P ∣ n` iff `P ⊆ Q`
    have hleaf : ∀ P ∈ (primesIco w z₀).powerset, (r * ∏ p ∈ P, p ∣ n ∧ rough w n) ↔ P ⊆ Q := by
      intro P hP
      have hPp := hPprime P hP
      have hPz : ∀ p ∈ P, p < z₀ := fun p hp => (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).2.1
      constructor
      · rintro ⟨h, -⟩ p hp
        exact (hmemQ p).2 ⟨mem_primesIco.1 (Finset.mem_powerset.1 hP hp),
          dvd_trans (dvd_trans (Finset.dvd_prod_of_mem _ hp) (dvd_mul_left _ r)) h⟩
      · intro hPQ
        refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_r hr hPp hPz) hrn
          ((prod_dvd_iff hPp n).2 fun p hp => ((hmemQ p).1 (hPQ hp)).2), hwn⟩
    have hleaves : ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
        (if alive stop P then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) =
        ∑ P ∈ Q.powerset, (-1 : ℤ) ^ P.card * (if alive stop P then 1 else 0) := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun P => P ⊆ Q)]
      have h0 : ∑ P ∈ ((primesIco w z₀).powerset).filter (fun P => ¬ P ⊆ Q), (-1 : ℤ) ^ P.card *
          (if alive stop P then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) = 0 :=
        Finset.sum_eq_zero fun P hP => by
          rw [Finset.mem_filter] at hP
          rw [ite_eq_right (fun h => hP.2 ((hleaf P hP.1).1 h))]
          simp
      rw [h0, add_zero]
      have hfilt : ((primesIco w z₀).powerset).filter (fun P => P ⊆ Q) = Q.powerset := by
        ext P
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨h.trans hQsub, h⟩⟩
      rw [hfilt]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPQ := Finset.mem_powerset.1 hP
      have hP' : P ∈ (primesIco w z₀).powerset := Finset.mem_powerset.2 (hPQ.trans hQsub)
      by_cases hX : alive stop P
      · rw [ite_eq_left hX, ite_eq_left hX, ite_eq_left ((hleaf P hP').2 hPQ)]
      · rw [ite_eq_right hX, ite_eq_right hX]
    -- the stops: only `p = min Q` contributes
    have hstop : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset,
        (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) ↔ (p ∈ Q ∧ (∀ q ∈ Q, p ≤ q) ∧ P ⊆ Q) := by
      intro p hp P hP
      have hpm := mem_primesIco.1 hp
      have hPm : ∀ p' ∈ P, p + 1 ≤ p' ∧ p' < z₀ ∧ p'.Prime := fun p' hp' =>
        mem_primesIco.1 (Finset.mem_powerset.1 hP hp')
      have hPp : ∀ p' ∈ P, p'.Prime := fun p' hp' => (hPm p' hp').2.2
      have hPz : ∀ p' ∈ P, p' < z₀ := fun p' hp' => (hPm p' hp').2.1
      constructor
      · rintro ⟨h, hrough⟩
        have hpn : p ∣ n := dvd_trans (dvd_mul_left p _) h
        refine ⟨(hmemQ p).2 ⟨hpm, hpn⟩, fun q hq => ?_, fun p' hp' => ?_⟩
        · obtain ⟨⟨-, -, hqp⟩, hqn⟩ := (hmemQ q).1 hq
          by_contra hlt
          exact hrough q (not_le.1 hlt) hqp hqn
        · refine (hmemQ p').2 ⟨⟨le_trans hpm.1 (by have := (hPm p' hp').1; omega), hPz p' hp', hPp p' hp'⟩, ?_⟩
          exact dvd_trans (dvd_trans (Finset.dvd_prod_of_mem _ hp') (dvd_mul_left _ r))
            (dvd_trans (dvd_mul_right _ p) h)
      · rintro ⟨hpQ, hmin, hPQ⟩
        have hpn := ((hmemQ p).1 hpQ).2
        have hPn : (∏ p' ∈ P, p') ∣ n := (prod_dvd_iff hPp n).2 fun p' hp' => ((hmemQ p').1 (hPQ hp')).2
        have hcop1 : Nat.Coprime r (∏ p' ∈ P, p') := coprime_r hr hPp hPz
        have hrP : r * ∏ p' ∈ P, p' ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop1 hrn hPn
        have hpr : ¬ p ∣ r := fun h => by have := hr p hpm.2.2 h; have := hpm.2.1; omega
        have hcop2 : Nat.Coprime (r * ∏ p' ∈ P, p') p := by
          refine Nat.coprime_mul_iff_left.2 ⟨((Nat.Prime.coprime_iff_not_dvd hpm.2.2).2 hpr).symm, ?_⟩
          exact Nat.Coprime.prod_left fun p' hp' => (Nat.coprime_primes (hPp p' hp') hpm.2.2).2
            (by have := (hPm p' hp').1; omega)
        refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 hrP hpn, fun q hq hqp hqn => ?_⟩
        by_cases hqw : q < w
        · exact hwn q hqw hqp hqn
        · have := hmin q ((hmemQ q).2 ⟨⟨not_lt.1 hqw, lt_trans hq hpm.2.1, hqp⟩, hqn⟩)
          omega
    rw [hleaves]
    by_cases hQe : Q = ∅
    · -- `n` is `z₀`-rough: the leaves give `[∅ alive] = 1` and the stops vanish
      have hstop0 : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if alive stop P ∧ stop (insert p P) then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
        intro p hp P hP
        have h := hstop p hp P hP
        rw [hQe] at h
        simp only [Finset.notMem_empty, false_and, iff_false] at h
        simp [h]
      rw [Finset.sum_congr rfl fun p hp => Finset.sum_eq_zero (hstop0 p hp), Finset.sum_const_zero, add_zero,
        ite_eq_left (hL.2 hQe), hQe, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
        one_mul, ite_eq_left (alive_empty hs)]
    · -- only the least prime `q₀` of `Q` stops, and the identity is `alt_cancel_stop`
      have hne : Q.Nonempty := Finset.nonempty_iff_ne_empty.2 hQe
      set q₀ := Q.min' hne with hq₀
      have hq₀Q : q₀ ∈ Q := Finset.min'_mem Q hne
      have hq₀min : ∀ q ∈ Q, q₀ ≤ q := fun q hq => Finset.min'_le Q q hq
      have hother : ∀ p ∈ primesIco w z₀, p ≠ q₀ → ∑ P ∈ (primesIco (p + 1) z₀).powerset,
          (-1 : ℤ) ^ (P.card + 1) * (if alive stop P ∧ stop (insert p P) then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
        intro p hp hpq
        refine Finset.sum_eq_zero fun P hP => ?_
        have h : ¬ (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) := fun h => by
          obtain ⟨hpQ, hmin, -⟩ := (hstop p hp P hP).1 h
          exact hpq (le_antisymm (hmin q₀ hq₀Q) (hq₀min p hpQ))
        simp [h]
      have hsub : (Q.erase q₀).powerset ⊆ (primesIco (q₀ + 1) z₀).powerset := by
        intro P hP
        refine Finset.mem_powerset.2 fun p hp => ?_
        have hpe := Finset.mem_erase.1 (Finset.mem_powerset.1 hP hp)
        obtain ⟨⟨-, hpz, hpp⟩, -⟩ := (hmemQ p).1 hpe.2
        have := hq₀min p hpe.2
        exact mem_primesIco.2 ⟨by have := hpe.1; omega, hpz, hpp⟩
      have hq₀mem : q₀ ∈ primesIco w z₀ := hQsub hq₀Q
      have hstopq : ∑ P ∈ (primesIco (q₀ + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
          (if alive stop P ∧ stop (insert q₀ P) then
            (if r * (∏ p' ∈ P, p') * q₀ ∣ n ∧ rough q₀ n then 1 else 0) else 0) =
          ∑ P ∈ (Q.erase q₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
            (if alive stop P ∧ stop (insert q₀ P) then 1 else 0) := by
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun P hP => ?_
          have hPQ : P ⊆ Q := (Finset.mem_powerset.1 hP).trans (Finset.erase_subset _ _)
          rw [ite_eq_left ((hstop q₀ hq₀mem P (hsub hP)).2 ⟨hq₀Q, hq₀min, hPQ⟩)]
        · intro P hP hP'
          have h : ¬ (r * (∏ p' ∈ P, p') * q₀ ∣ n ∧ rough q₀ n) := fun h => by
            obtain ⟨-, -, hPQ⟩ := (hstop q₀ hq₀mem P hP).1 h
            refine hP' (Finset.mem_powerset.2 fun p hp => Finset.mem_erase.2 ⟨fun he => ?_, hPQ hp⟩)
            have := (mem_primesIco.1 (Finset.mem_powerset.1 hP hp)).1
            omega
          simp [h]
      rw [Finset.sum_eq_single q₀ hother (fun h => absurd hq₀mem h), hstopq, ite_eq_right (fun h => hQe (hL.1 h))]
      have hlt : ∀ p ∈ Q.erase q₀, q₀ < p := fun p hp => by
        have hpe := Finset.mem_erase.1 hp
        exact lt_of_le_of_ne (hq₀min p hpe.2) (Ne.symm hpe.1)
      have hc := alt_cancel_stop stop q₀ (Q.erase q₀) hlt
      rw [Finset.insert_erase hq₀Q] at hc
      exact hc.symm
  · -- every term vanishes
    have hL0 : ¬ (r ∣ n ∧ rough z₀ n) := fun h => hb ⟨h.1, rough_mono hwz h.2⟩
    have h1 : ∀ P ∈ (primesIco w z₀).powerset, (-1 : ℤ) ^ P.card *
        (if alive stop P then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) = 0 := by
      intro P _
      have h : ¬ (r * ∏ p ∈ P, p ∣ n ∧ rough w n) := fun h => hb ⟨dvd_trans (dvd_mul_right r _) h.1, h.2⟩
      simp [h]
    have h2 : ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℤ) ^ (P.card + 1) *
        (if alive stop P ∧ stop (insert p P) then
          (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) = 0 := by
      intro p hp P _
      have h : ¬ (r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n) := fun h =>
        hb ⟨dvd_trans (dvd_trans (dvd_mul_right r _) (dvd_mul_right _ p)) h.1,
          rough_mono (mem_primesIco.1 hp).1 h.2⟩
      simp [h]
    rw [ite_eq_right hL0, Finset.sum_eq_zero h1, Finset.sum_congr rfl fun p hp => Finset.sum_eq_zero (h2 p hp),
      Finset.sum_const_zero, add_zero]

open Classical in
/-- **Buchstab's tree with a stopping rule, weighted.** `tree_pt_stop` summed over a finite set with weights `f`. -/
theorem tree_weighted_stop (C : Finset ℕ) (f : ℕ → ℂ) {r w z₀ : ℕ} (hwz : w ≤ z₀)
    (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) (stop : Finset ℕ → Prop) (hs : ¬ stop ∅) :
    ∑ n ∈ C, f n * (if r ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if alive stop P then ∑ n ∈ C, f n * (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if alive stop P ∧ stop (insert p P) then
            ∑ n ∈ C, f n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  have hptC : ∀ n, (if r ∣ n ∧ rough z₀ n then (1 : ℂ) else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if alive stop P then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if alive stop P ∧ stop (insert p P) then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
    intro n
    have h := congrArg (Int.cast : ℤ → ℂ) (tree_pt_stop n hwz hr stop hs)
    push_cast at h
    convert h using 1
  simp_rw [hptC, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp

/-! ### Small steps -/

/-- An upper part's product is at most the whole product, for positive factors. -/
theorem prod_filter_le (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (t : ℕ) :
    ∏ p ∈ P.filter (t ≤ ·), p ≤ ∏ p ∈ P, p :=
  Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) fun p hp _ => hP p hp

/-- **Small steps.** Let the rule stop a set `P'` only when `c∏P' ≥ E`, and stop every `P'` with `E ≤ c∏P' < Ez₀`, for
`0 ≤ c < E`. A set `P` of integers in `[1, z₀)` is alive iff `c∏P < E`. -/
theorem alive_iff_lt (stop : Finset ℕ → Prop) {c E z₀ : ℝ} (hc : 0 ≤ c) (hcE : c < E)
    (hlo : ∀ P' : Finset ℕ, stop P' → E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ))
    (hhi : ∀ P' : Finset ℕ, E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ) → c * ((∏ p ∈ P', p : ℕ) : ℝ) < E * z₀ → stop P')
    {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) < z₀) :
    alive stop P ↔ c * ((∏ p ∈ P, p : ℕ) : ℝ) < E := by
  constructor
  · intro hA
    by_contra hge0
    have hge := not_lt.1 hge0
    set g : ℕ → ℝ := fun t => c * ((∏ p ∈ P.filter (t ≤ ·), p : ℕ) : ℝ) with hg
    have hex : ∃ t, g t < E := by
      refine ⟨P.sup id + 1, ?_⟩
      have e : P.filter (P.sup id + 1 ≤ ·) = ∅ := Finset.filter_eq_empty_iff.2 fun p hp => by
        have := Finset.le_sup (f := id) hp
        simp only [id] at this
        omega
      simp only [hg, e, Finset.prod_empty, Nat.cast_one, mul_one]
      exact hcE
    set t₀ := Nat.find hex with ht₀
    have ht₀E : g t₀ < E := Nat.find_spec hex
    have hg0 : g 0 = c * ((∏ p ∈ P, p : ℕ) : ℝ) := by
      simp only [hg]
      rw [Finset.filter_true_of_mem fun p _ => Nat.zero_le p]
    have ht₀0 : t₀ ≠ 0 := fun h => by
      rw [h, hg0] at ht₀E
      linarith
    obtain ⟨u, hu⟩ : ∃ u, t₀ = u + 1 := ⟨t₀ - 1, by omega⟩
    have hprev : E ≤ g u := not_lt.1 (Nat.find_min hex (by omega))
    by_cases huP : u ∈ P
    · -- the upper part at `u` adds `u` to the one at `t₀` and stops
      have e : P.filter (u ≤ ·) = insert u (P.filter (t₀ ≤ ·)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hp, hpu⟩
          rcases Nat.eq_or_lt_of_le hpu with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨hp, by omega⟩
        · rintro (rfl | ⟨hp, hpt⟩)
          · exact ⟨huP, le_rfl⟩
          · exact ⟨hp, by omega⟩
      have hun : u ∉ P.filter (t₀ ≤ ·) := fun h => by
        have := (Finset.mem_filter.1 h).2
        omega
      have hgu : g u = (u : ℝ) * g t₀ := by
        simp only [hg]
        rw [e, Finset.prod_insert hun]
        push_cast
        ring
      obtain ⟨hu1, huz⟩ := hP u huP
      have hgt0 : 0 ≤ g t₀ := by
        simp only [hg]
        positivity
      have hlt : g u < E * z₀ := by
        rw [hgu]
        have hu0 : (0 : ℝ) < u := by exact_mod_cast hu1
        calc (u : ℝ) * g t₀ ≤ u * E := mul_le_mul_of_nonneg_left ht₀E.le hu0.le
          _ < z₀ * E := mul_lt_mul_of_pos_right huz (by linarith)
          _ = E * z₀ := mul_comm _ _
      exact hA u (hhi _ hprev hlt)
    · -- the upper parts at `u` and `t₀` agree
      have e : P.filter (u ≤ ·) = P.filter (t₀ ≤ ·) := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hpu⟩
          refine ⟨hp, ?_⟩
          rcases Nat.eq_or_lt_of_le hpu with h | h
          · exact absurd (h ▸ hp) huP
          · omega
        · rintro ⟨hp, hpt⟩
          exact ⟨hp, by omega⟩
      have : g u = g t₀ := by simp only [hg, e]
      linarith
  · intro hlt t hstop
    have h1 := hlo _ hstop
    have h2 : ((∏ p ∈ P.filter (t ≤ ·), p : ℕ) : ℝ) ≤ ((∏ p ∈ P, p : ℕ) : ℝ) := by
      exact_mod_cast prod_filter_le P (fun p hp => (hP p hp).1) t
    have h3 : c * ((∏ p ∈ P.filter (t ≤ ·), p : ℕ) : ℝ) ≤ c * ((∏ p ∈ P, p : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hc
    linarith

/-- **Small steps, the stops.** Under `alive_iff_lt`'s hypotheses, for an alive `P` and `p ∈ [1, z₀)` not in `P`:
`P ∪ {p}` stops iff `E ≤ c∏P·p`. -/
theorem stop_insert_iff (stop : Finset ℕ → Prop) {c E z₀ : ℝ} (hc : 0 ≤ c) (hcE : c < E)
    (hlo : ∀ P' : Finset ℕ, stop P' → E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ))
    (hhi : ∀ P' : Finset ℕ, E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ) → c * ((∏ p ∈ P', p : ℕ) : ℝ) < E * z₀ → stop P')
    {P : Finset ℕ} (hlt : c * ((∏ p ∈ P, p : ℕ) : ℝ) < E) {p : ℕ} (hp1 : 1 ≤ p) (hpz : (p : ℝ) < z₀)
    (hpP : p ∉ P) :
    stop (insert p P) ↔ E ≤ c * ((∏ p' ∈ P, p' : ℕ) : ℝ) * p := by
  have e : c * ((∏ p' ∈ insert p P, p' : ℕ) : ℝ) = c * ((∏ p' ∈ P, p' : ℕ) : ℝ) * p := by
    rw [Finset.prod_insert hpP]
    push_cast
    ring
  constructor
  · intro h
    rw [← e]
    exact hlo _ h
  · intro h
    refine hhi _ (by rw [e]; exact h) ?_
    rw [e]
    have h0 : 0 ≤ c * ((∏ p' ∈ P, p' : ℕ) : ℝ) := by positivity
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    calc c * ((∏ p' ∈ P, p' : ℕ) : ℝ) * p ≤ E * p := mul_le_mul_of_nonneg_right hlt.le hp0.le
      _ < E * z₀ := mul_lt_mul_of_pos_left hpz (by linarith)

end SieveTreeStop
