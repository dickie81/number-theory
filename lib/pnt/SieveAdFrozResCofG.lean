/-
# The chain's cofactor over the frozen part, in the rest of an estimate given as a hypothesis

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozResCof.lean` evaluates the term of a chain's box over the frozen part of a reversal by
the resonant window with the chain's cofactor in the rest, when every multiple's chain cofactor is one prime
(`evIF_frozP_resC`, by `SieveTypeIIHM.full_res_exp`). The same argument works for any estimate of the full tuples
with the rest in its cells, `SieveTypeIIHM.FullEst`.

* `evIF_frozP_genC`: **the term over `frozP … t` is evaluated with the chain's cofactor in the rest**, given
  `FullEst L κ (n + 1)` for the region `q^{lo i} ≤ x_i ≤ q^{hi i}`, `lo`, `hi` the ends of the cells of a rest at
  injective positions `r` of the box and of the cofactor's cell after them.
* `evIF_froz_genC`: **so is the term over the frozen part.**

The proofs are `evIF_frozP_resC`'s and `evIF_froz_resC`'s, with the hypothesis in the place of `full_res_exp`.

The file imports `SieveAdFrozResCof.lean` and `SieveResTight.lean`.
-/
import SieveAdFrozResCof
import SieveResTight

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK]

set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, by an estimate of the tuples
with the chain's cofactor in the rest.** Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`,
`e₁, e₂ ≤ DEN`, the chain's upper ends with `e₂` summing to at most `DEN − 2`, and its lower ends with `e₁` and
twice its least prime's at least `DEN + 1`. Let the rest be at the injective positions `r` of the box (frozen
primes first, then the chain's) and the chain's cofactor, with `lo j = κ·lo(r j)`, `hi j = κ·hi(r j)`,
`lo (n + 1) = κ·max(DEN − e₂ − Σhi − 1, lo₀)` and `hi (n + 1) = κ·(DEN − e₁ − Σlo + 1)`, for `κ = L/DEN`. If
`FullEst L κ (n + 1)` holds for the region `q^{lo i} ≤ x_i ≤ q^{hi i}`, the term of the chain's box over
`frozP … t` is evaluated. -/
theorem evIF_frozP_genC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) (hslo : DEN + 1 ≤ e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo hi : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hhi : ∀ j : Fin (n + 1), hi j = κ * ((Fin.append βx bx (r j)).2 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ))
    (hhin : hi (n + 1) = κ * ((DEN - e₁ - ∑ j, (bx j).1 + 1 : ℕ) : ℝ))
    (hfull : SieveTypeIIHM.FullEst L κ (n + 1)
      (fun q x => ∀ i : Fin (n + 1 + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i)) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := hfull (s + 1 + t + k' + 1 + 1)
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + 1 * 1 + 1 + 2) (L + 1) (by linarith)
  filter_upwards [eventually_ge_atTop q₀, le_Xq hδ hη, big_ev] with q hq hXle hbig a ha
  obtain ⟨hq2, hx3, -, -, -⟩ := big_facts hbig
  have hq1 : 1 ≤ q := by omega
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqn : NeZero q := ⟨by omega⟩
  have hx1 : 1 ≤ xq q := by linarith
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
  rw [dIF_frozP_eq hbig a hβD he₁ he₂ t hbD1, Finset.sum_eq_single 1]
  rotate_left
  · -- the chain's cofactor is one prime: no full tuple has another number of cofactor primes
    intro t' _ ht'1
    refine Finset.sum_eq_zero fun z hz => ?_
    exfalso
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
    obtain ⟨hzp, hzΩ⟩ := hz
    have hzp' : ∀ i, z i ≤ N2 q ∧ (z i).Prime := fun i => SieveTypeIIU.mem_primesLe.1 (hzp i)
    have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd t' i) := fun i => (hzp' _).2.one_lt.le
    have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hzp' _).2.one_lt.le
    rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
    obtain ⟨hΩ', -, hlast, hlo', hhi'⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := t')
      (frozΩ q e₁ e₂ βx t bx) (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
    have hrtW : (fun i => z (Fin.castAdd t' i)) ∈ frozW q e₁ e₂ βx t bx := by
      rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i => SieveTypeIIU.mem_primesLe.2 (hzp' _), hΩ'⟩
    obtain ⟨hf0, hf2, -⟩ := frozCof_facts hbig hshi hslo hrtW
    have hw : ((∏ i, z (Fin.castAdd t' i) : ℕ) : ℝ) = ∏ i, (z (Fin.castAdd t' i) : ℝ) := Nat.cast_prod _ _
    rcases Nat.lt_or_ge t' 2 with ht2 | ht2
    · have ht0 : t' = 0 := by omega
      subst ht0
      rw [Fin.prod_univ_zero, mul_one, ← hw] at hlo'
      have h1 : N1 q < ∏ i, z (Fin.castAdd 0 i) := by exact_mod_cast hlo'
      have h2 : ∏ i, z (Fin.castAdd 0 i) ≤ N1 q := hf0
      omega
    · -- two primes at least the chain's last overshoot `N₂`
      have h01 : (⟨0, by omega⟩ : Fin t') ≠ ⟨1, by omega⟩ := by
        intro h
        simp [Fin.ext_iff] at h
      have hyy : z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) * z (Fin.castAdd t' (Fin.last (s + 1 + t + k')))
          ≤ ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) := by
        calc z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) * z (Fin.castAdd t' (Fin.last (s + 1 + t + k')))
            ≤ z (Fin.natAdd (s + 1 + t + k' + 1) ⟨0, by omega⟩) * z (Fin.natAdd (s + 1 + t + k' + 1) ⟨1, by omega⟩) :=
              Nat.mul_le_mul (hlast _) (hlast _)
          _ = ∏ b ∈ {⟨0, by omega⟩, ⟨1, by omega⟩}, z (Fin.natAdd (s + 1 + t + k' + 1) b) := by
              rw [Finset.prod_pair h01]
          _ ≤ ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
              Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) fun i _ _ => (hzp' _).2.one_lt.le
      have hf2' : N2 q < (∏ i, z (Fin.castAdd t' i)) *
          (z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) * z (Fin.castAdd t' (Fin.last (s + 1 + t + k')))) := hf2
      have hhiN : (∏ i, z (Fin.castAdd t' i)) * ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) ≤ N2 q := by
        have h := hhi'
        rw [← hw] at h
        exact_mod_cast h
      exact absurd (lt_of_lt_of_le hf2' ((Nat.mul_le_mul_left _ hyy).trans hhiN)) (lt_irrefl _)
  · intro h1
    exact absurd (Finset.mem_range.2 (by have := SieveCert.DEN_pos; omega)) h1
  -- one cofactor prime: the window on the full tuples with the cofactor in the rest
  have hcast : ∑ z ∈ RTg (s + 1 + t + k' + 1 + 1) (N2 q)
      (fullTL (s + 1 + t + k') 1 (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)), dw q a (∏ i, z i) =
      ((∑ z ∈ RTg (s + 1 + t + k' + 1 + 1) (N2 q)
        (fullTL (s + 1 + t + k') 1 (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun z _ => dw_eq q a _
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast]
  -- the rest's positions in the full tuple: the box's, then the cofactor's last
  set f : Fin (s + 1 + (k' + 1)) → Fin (s + 1 + t + k' + 1) := fun i => posB s t (k' + 1) i with hf
  have hfi : Function.Injective f := posB_injective s t (k' + 1)
  have hfr : Function.Injective fun j => f (r j) := hfi.comp hr
  refine (hq₀ q hq a ha (SieveTypeIIHM.snocR fun j => f (r j)) (SieveTypeIIHM.snocR_injective hfr)
    (fullTL (s + 1 + t + k') 1 (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)) ?_ ?_ ?_).trans
    (mul_le_mul_of_nonneg_left hXle hφ)
  · refine (length_fullTL_le (s + 1 + t + k') 1 _ _ _).trans ?_
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
    have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd 1 i) := fun i => (hz _).one_lt.le
    have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hz _).one_lt.le
    rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
    obtain ⟨hΩ', -, hlast, hlo', hhi'⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := 1)
      (frozΩ q e₁ e₂ βx t bx) (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
    have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd 1 i)) * ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
      Fin.prod_univ_add z
    have hlo'' : N1 q < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo'
    have hhi'' : ∏ i, z i ≤ N2 q := by rw [hprod]; exact_mod_cast hhi'
    have hz0 : 0 < ∏ i, z i := by omega
    have hrtW : (fun i => z (Fin.castAdd 1 i)) ∈ frozW q e₁ e₂ βx t bx := by
      rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => SieveTypeIIU.mem_primesLe.2 ⟨?_, hz _⟩, hΩ'⟩
      exact (Nat.le_of_dvd hz0 (Finset.dvd_prod_of_mem z (Finset.mem_univ _))).trans hhi''
    have hge := frozW_ge hx1 (f := 1) (hβ (Fin.last s)).1 (fun j => (hb j).1) hrtW
    have hcell := cells_posB hrtW
    have hy : ∏ b : Fin 1, z (Fin.natAdd (s + 1 + t + k' + 1) b) = z (Fin.last (s + 1 + t + k' + 1)) := by
      rw [Fin.prod_univ_one]
      rfl
    rw [hy] at hprod
    -- the cofactor's cell
    obtain ⟨-, -, hf1⟩ := frozCof_facts hbig hshi hslo hrtW
    obtain ⟨hcy, hcY⟩ := hf1 (z (Fin.last (s + 1 + t + k' + 1))) (hlast 0)
      (by have h := hlo''; rw [hprod] at h; exact h) (by have h := hhi''; rw [hprod] at h; exact h)
    -- the cells of the box's primes in the rest, as powers of `q`
    have hqc : ∀ i : Fin (s + 1 + (k' + 1)),
        (q : ℝ) ^ (κ * ((Fin.append βx bx i).1 : ℝ)) ≤ z (Fin.castAdd 1 (f i)) ∧
          (z (Fin.castAdd 1 (f i)) : ℝ) ≤ (q : ℝ) ^ (κ * ((Fin.append βx bx i).2 : ℝ)) := fun i => by
      rw [hqx, hqx]
      exact ⟨(hcell i).1, (hcell i).2.le⟩
    refine ⟨fun i => ?_, fun i => ?_, hlo'', hhi''⟩
    · -- every prime is at least `q^κ`
      have h1 : (q : ℝ) ^ κ = Xe q 1 := by
        have := hqx 1
        rwa [Nat.cast_one, mul_one] at this
      rw [h1]
      refine Fin.addCases (fun i' => ?_) (fun b => ?_) i
      · exact hge i'
      · have h2 : Xe q 1 ≤ (z (Fin.castAdd 1 (Fin.last (s + 1 + t + k'))) : ℝ) :=
          hge (Fin.last (s + 1 + t + k'))
        have h3 : (z (Fin.castAdd 1 (Fin.last (s + 1 + t + k'))) : ℝ) ≤
            z (Fin.natAdd (s + 1 + t + k' + 1) b) := by exact_mod_cast hlast b
        exact h2.trans h3
    · -- the rest's primes in their cells, the cofactor last
      induction i using Fin.lastCases with
      | last =>
        show (q : ℝ) ^ lo (n + 1) ≤ z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.last (n + 1))) ∧
          (z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.last (n + 1))) : ℝ) ≤ (q : ℝ) ^ hi (n + 1)
        simp only [SieveTypeIIHM.snocR, Fin.snoc_last]
        rw [hlon, hhin, hqx, hqx]
        exact ⟨hcy, hcY⟩
      | cast j =>
        show (q : ℝ) ^ lo (j : ℕ) ≤ z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.castSucc j)) ∧
          (z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.castSucc j)) : ℝ) ≤ (q : ℝ) ^ hi (j : ℕ)
        simp only [SieveTypeIIHM.snocR, Fin.snoc_castSucc]
        rw [hlo j, hhi j]
        exact hqc (r j)

/-- **The term of a chain's box over the frozen part, by an estimate of the tuples with the chain's cofactor in the
rest.** `evIF_frozP_genC` for every number of the frozen cofactor's primes. -/
theorem evIF_froz_genC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) (hslo : DEN + 1 ≤ e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo hi : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hhi : ∀ j : Fin (n + 1), hi j = κ * ((Fin.append βx bx (r j)).2 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ))
    (hhin : hi (n + 1) = κ * ((DEN - e₁ - ∑ j, (bx j).1 + 1 : ℕ) : ℝ))
    (hfull : SieveTypeIIHM.FullEst L κ (n + 1)
      (fun q x => ∀ i : Fin (n + 1 + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i)) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ =>
    evIF_frozP_genC hβ he₁ he₂ t hb hshi hslo hκ r hr lo hi hlo hhi hlon hhin hfull

end SieveAd

#print axioms SieveAd.evIF_froz_genC
