/-
# The term of a chain's box over the frozen part, by an estimate of the tuples given as a hypothesis

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozRes.lean` evaluates the term of a chain's box over the frozen part of a reversal by
the resonant window's estimate on the full tuples `(a, y, c, y′)` of the term (`SieveTypeIIHM.full_res_exp`), the
rest some of the frozen primes and of the chain's primes, each in its cell. The same argument works for any estimate
of the full tuples with the rest in its cells, `SieveTypeIIHM.FullEst`: the window's on a box with the variable tied
to the rest (`SieveTypeIIHM.fullEst_of_tightG`) is one.

* `evIF_frozP_gen`: **the term over `frozP … t` is evaluated** given `FullEst L κ n` for the region
  `q^{lo i} ≤ x_i ≤ q^{hi i}`, `lo`, `hi` the ends of the cells of a rest at injective positions `r` of the box.
* `evIF_froz_gen`: **so is the term over the frozen part**.

The proofs are `evIF_frozP_res`'s and `evIF_froz_res`'s, with the hypothesis in the place of `full_res_exp`.

The file imports `SieveAdFrozRes.lean` and `SieveResTight.lean`.
-/
import SieveAdFrozRes
import SieveResTight

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route]

variable [RouteOK] [SieveCert.IBPar] [IBFits]

omit [SieveCert.IBPar] [IBFits] in
set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, by an estimate of the tuples.**
Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, and `e₁, e₂ ≤ DEN`. Let the rest be at the
injective positions `r` of the box (frozen primes first, then the chain's), with `lo j = κ·lo(r j)` and
`hi j = κ·hi(r j)` for `κ = L/DEN`. If `FullEst L κ n` holds for the region `q^{lo i} ≤ x_i ≤ q^{hi i}`, the term
of the chain's box over `frozP … t` is evaluated. -/
theorem evIF_frozP_gen {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ} {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo hi : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hhi : ∀ j : Fin (n + 1), hi j = κ * ((Fin.append βx bx (r j)).2 : ℝ))
    (hfull : SieveTypeIIHM.FullEst L κ n
      (fun q x => ∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i)) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  intro η hη
  have hcore := fun t' : ℕ => hfull (s + 1 + t + k' + 1 + t')
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + t' * t' + t' + 2) (L + 1) (by linarith)
  choose δf hδf q₀f hq₀f using hcore
  have hall : ∀ᶠ q : ℕ in atTop, ∀ t' ∈ Finset.range (DEN + 1),
      q₀f t' ≤ q ∧ (q : ℝ) ^ (L - δf t') ≤ η / ((DEN : ℝ) + 1) * Xq q := by
    rw [Filter.eventually_all_finset]
    intro t' _
    exact (eventually_ge_atTop (q₀f t')).and (le_Xq (hδf t') (by positivity))
  filter_upwards [hall, big_ev] with q hq hbig a ha
  obtain ⟨hq2, hx3, -, hN2', -⟩ := big_facts hbig
  have hq1 : 1 ≤ q := by omega
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqn : NeZero q := ⟨by omega⟩
  have hx1 : 1 ≤ xq q := by linarith
  have hx1' : 1 < xq q := by linarith
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hN1 : 1 ≤ N1 q := Nat.le_floor (by push_cast; linarith)
  have hN12 : N1 q ≤ N2 q := Nat.floor_le_floor (by linarith)
  have hY : 1 ≤ N2 q := hN1.trans hN12
  have hlogN₂ : Real.log (N2 q : ℝ) ≤ (L + 1) * Real.log q := by
    have h1 : (N2 q : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      have h2 : (N2 q : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
      have h3 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      have h4 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
      rw [Real.rpow_add hq0, Real.rpow_one]
      nlinarith
    have h2 := Real.log_le_log (by exact_mod_cast hY) h1
    rwa [Real.log_rpow hq0] at h2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1'
  -- `q^{κ·e} = x^{e/DEN}`
  have hqx : ∀ e : ℕ, (q : ℝ) ^ (κ * (e : ℝ)) = Xe q e := fun e => by rw [hκ, qpow_eq]; rfl
  show |dIF q a (frozP q e₁ e₂ βx t) prodR bx| ≤ _
  rw [dIF_frozP_eq hbig a hβD he₁ he₂ t hbD1]
  have hbound : ∀ t' ∈ Finset.range (DEN + 1),
      |∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
          (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))| ≤ (q.totient : ℝ)⁻¹ * (η / ((DEN : ℝ) + 1) * Xq q) := by
    intro t' ht'
    obtain ⟨hq0', hXle⟩ := hq t' ht'
    have hcast : ∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)), dw q a (∏ i, z i) =
        ((∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
          (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
          (gA q a (∏ i, z i) - gB q (∏ i, z i)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun z _ => dw_eq q a _
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast]
    -- the rest's positions in the full tuple
    set f : Fin (s + 1 + (k' + 1)) → Fin (s + 1 + t + k' + 1 + t') :=
      fun i => Fin.castAdd t' (posB s t (k' + 1) i) with hf
    have hfi : Function.Injective f := fun i j hij =>
      posB_injective s t (k' + 1) (Fin.castAdd_injective _ _ hij)
    refine (hq₀f t' q hq0' a ha (fun j => f (r j)) (hfi.comp hr)
      (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)) ?_ ?_ ?_).trans
      (mul_le_mul_of_nonneg_left hXle hφ)
    · refine (length_fullTL_le (s + 1 + t + k') t' _ _ _).trans ?_
      have := frozΩ_length q e₁ e₂ βx t bx
      omega
    · intro C hC
      unfold fullTL at hC
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with ((⟨C', hC', rfl⟩ | hC) | hC) | rfl | rfl
      · show C'.c 0 ≤ _
        exact frozΩ_c hq1 hβD t hbD he₁ he₂ C' hC'
      · obtain ⟨a', b', -, rfl⟩ := mem_yPairs.1 hC
        show (0 : ℝ) ≤ _
        positivity
      · unfold yLast at hC
        obtain ⟨a', -, rfl⟩ := List.mem_map.1 hC
        show (0 : ℝ) ≤ _
        positivity
      · show Real.log ((0 : ℕ) : ℝ) - Real.log (N1 q : ℝ) ≤ _
        have h0 : 0 ≤ Real.log (N1 q : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
        have h1 : 0 ≤ (L + 1) * Real.log q := by positivity
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
      · show Real.log (N2 q : ℝ) - Real.log ((0 : ℕ) : ℝ) ≤ _
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
    · -- what a tuple of the family satisfies
      intro z hz hzΩ
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd t' i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlast, hlo', hhi'⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := t')
        (frozΩ q e₁ e₂ βx t bx)
        (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd t' i)) * ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
        Fin.prod_univ_add z
      have hlo'' : N1 q < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo'
      have hhi'' : ∏ i, z i ≤ N2 q := by rw [hprod]; exact_mod_cast hhi'
      have hz0 : 0 < ∏ i, z i := by omega
      have hrtW : (fun i => z (Fin.castAdd t' i)) ∈ frozW q e₁ e₂ βx t bx := by
        rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun i => SieveTypeIIU.mem_primesLe.2 ⟨?_, hz _⟩, hΩ'⟩
        exact (Nat.le_of_dvd hz0 (Finset.dvd_prod_of_mem z (Finset.mem_univ _))).trans hhi''
      have hge := frozW_ge hx1 (f := 1) (hβ (Fin.last s)).1 (fun j => (hb j).1) hrtW
      have hcell := cells_posB hrtW
      -- the cells of the rest's primes, as powers of `q`
      have hcc : ∀ i : Fin (s + 1 + (k' + 1)),
          (q : ℝ) ^ (κ * ((Fin.append βx bx i).1 : ℝ)) ≤ z (f i) ∧
            (z (f i) : ℝ) ≤ (q : ℝ) ^ (κ * ((Fin.append βx bx i).2 : ℝ)) := fun i => by
        rw [hqx, hqx]
        exact ⟨(hcell i).1, (hcell i).2.le⟩
      refine ⟨fun i => ?_, fun j => ?_, hlo'', hhi''⟩
      · have h1 : (q : ℝ) ^ κ = Xe q 1 := by
          have := hqx 1
          rwa [Nat.cast_one, mul_one] at this
        rw [h1]
        refine Fin.addCases (fun i' => ?_) (fun b => ?_) i
        · exact hge i'
        · have h2 : Xe q 1 ≤ (z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) : ℝ) :=
            hge (Fin.last (s + 1 + t + k'))
          have h3 : (z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) : ℝ) ≤
              z (Fin.natAdd (s + 1 + t + k' + 1) b) := by exact_mod_cast hlast b
          exact h2.trans h3
      · rw [hlo j, hhi j]
        exact hcc (r j)
  calc |∑ t' ∈ Finset.range (DEN + 1), ∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))|
      ≤ ∑ t' ∈ Finset.range (DEN + 1), |∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t' ∈ Finset.range (DEN + 1), (q.totient : ℝ)⁻¹ * (η / ((DEN : ℝ) + 1) * Xq q) :=
        Finset.sum_le_sum hbound
    _ = (q.totient : ℝ)⁻¹ * (η * Xq q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

omit [SieveCert.IBPar] [IBFits] in
/-- **The term of a chain's box over the frozen part, by an estimate of the tuples.** `evIF_frozP_gen` for every
number of the frozen cofactor's primes. -/
theorem evIF_froz_gen {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo hi : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hhi : ∀ j : Fin (n + 1), hi j = κ * ((Fin.append βx bx (r j)).2 : ℝ))
    (hfull : SieveTypeIIHM.FullEst L κ n
      (fun q x => ∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i)) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ => evIF_frozP_gen hβ he₁ he₂ t hb hκ r hr lo hi hlo hhi hfull

end SieveAd

#print axioms SieveAd.evIF_froz_gen
