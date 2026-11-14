/-
# The term of a chain's box over the frozen part, by the resonant window

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozI.lean` evaluates the term of a chain's box over the frozen part of a reversal by the
estimate in two variables on the full tuples `(a, y, c, y′)` of the term (`evIF_froz_two`). This file evaluates it
by the resonant window's estimate on the same tuples (`SieveTypeIIHM.full_res_exp`): one variable, the product of
everything outside a rest, the rest's primes some of the frozen primes `a` and of the chain's primes `c`, each in its
cell. The kernel's test is that of the main tree, `chkIR`, on the box `ch ++ β`.

* `posB s t k`: the position in the tuple `(a, y, c)` of a cell of the box, by the box's index: the frozen primes'
  cells first, then the chain's (`posB_injective`); `boxFn_append_froz`: the box `ch ++ β` as a function of the
  index is `Fin.append` of the two; `cells_posB`: a tuple of `frozW` has its primes at `posB` in their cells.
* `evIF_frozP_res`: **the term over `frozP … t` is evaluated** when `ResBox` holds for a rest at injective
  positions `r` of the box, with the lower ends of the rest's cells and the sum of their upper ends.
* `evIF_froz_res`: **so is the term over the frozen part**; `evIF_froz_resT`: **when `chkIR` passes the box
  `ch ++ β`**, for the hint's rest and intervals.

The file imports `SieveAdFrozI.lean` and `SieveAdRes.lean`.
-/
import SieveAdFrozI
import SieveAdRes

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-! ### The cells of the box `ch ++ β` in the tuple -/

/-- The position in the tuple `(a, y, c)` of a cell of the box `ch ++ β`, by the box's index: the frozen primes'
cells first, then the chain's. -/
def posB (s t k : ℕ) : Fin (s + 1 + k) → Fin (s + 1 + t + k) :=
  Fin.append (fun i => posA s t k i) (fun j => posC s t k j)

theorem posB_injective (s t k : ℕ) : Function.Injective (posB s t k) := by
  intro i j
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i <;> refine Fin.addCases (fun a' => ?_) (fun c' => ?_) j <;>
    simp only [posB, Fin.append_left, Fin.append_right] <;> intro hij
  · rw [(posA s t k).injective hij]
  · exact absurd hij (posA_ne_posC s t k a c')
  · exact absurd hij.symm (posA_ne_posC s t k a' c)
  · rw [(posC s t k).injective hij]

/-- **The box `ch ++ β` by the index**: the cells of the frozen primes `β`, then those of the chain `ch`. -/
theorem boxFn_append_froz (ch β : List Cell) {s k : ℕ} (hβ : β.length = s + 1) (hch : ch.length = k)
    (h : (ch ++ β).length = s + 1 + k) :
    boxFn (ch ++ β) (s + 1 + k) h = Fin.append (boxFn β (s + 1) hβ) (boxFn ch k hch) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · rw [Fin.append_left]
    simp only [boxFn, Fin.val_castAdd]
    have ha := a.2
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega
  · rw [Fin.append_right]
    simp only [boxFn, Fin.val_natAdd]
    have hc := c.2
    rw [List.getElem_append_left (by omega)]
    congr 1
    omega

variable [Route]

/-- A tuple of `frozW` has its primes at `posB` in their cells. -/
theorem cells_posB {q e₁ e₂ s t k : ℕ} {βx : Fin (s + 1) → Cell} {bx : Fin k → Cell}
    {w : Fin (s + 1 + t + k) → ℕ} (hw : w ∈ frozW q e₁ e₂ βx t bx) (i : Fin (s + 1 + k)) :
    Xe q (Fin.append βx bx i).1 ≤ w (posB s t k i) ∧ (w (posB s t k i) : ℝ) < Xe q (Fin.append βx bx i).2 := by
  obtain ⟨-, hsem, -, -⟩ := frozW_iff.1 hw
  obtain ⟨⟨-, hca⟩, ⟨-, hcc⟩, -⟩ := (sem_frozA q e₁ e₂ βx t bx w).1 hsem
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · simp only [posB, Fin.append_left]
    exact hca a
  · simp only [posB, Fin.append_right]
    exact hcc c

/-! ### The term is evaluated -/

variable [RouteOK] [SieveCert.IBPar] [IBFits]

omit [SieveCert.IBPar] [IBFits] in
set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, by the resonant window.** Let
`βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, and `e₁, e₂ ≤ DEN`. Let the rest be at the
injective positions `r` of the box (frozen primes first, then the chain's), with `lo j = κ·lo(r j)` for `κ = L/DEN`
and `ρ₂ = κ·Σ hi` over the rest. If `ResBox` holds for the rest with `L − ρ₂ − κ > 0`, the term of the chain's box
over `frozP … t` is evaluated. -/
theorem evIF_frozP_res {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ} {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ)) {ρ₂ : ℝ}
    (hρ₂ : ρ₂ = κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 : ℕ) : ℝ)) (hLρ : 0 < L - ρ₂ - κ)
    (hres : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1) (L - ρ₂ - κ) (fun j => lo j - κ)) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; positivity
  intro η hη
  have hcore := fun t' : ℕ => SieveTypeIIHM.full_res_exp SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half
    SieveCurveHx.counts_hx hL0 L_le hκ0 (s + 1 + t + k' + 1 + t')
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + t' * t' + t' + 2) (Λ₁ := L + 1) (by linarith) hρ₂0 hκ0 hLρ
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
    have hprodr : ∀ z : Fin (s + 1 + t + k' + 1 + t') → ℕ,
        ∏ x ∈ Finset.univ.image (fun j => f (r j)), z x = ∏ i ∈ Finset.univ.image r, z (f i) := by
      intro z
      have e : Finset.univ.image (fun j => f (r j)) = (Finset.univ.image r).image f := by
        rw [Finset.image_image]
        rfl
      rw [e, Finset.prod_image fun i _ j _ hij => hfi hij]
    refine (hq₀f t' q hq0' a ha n (fun j => f (r j)) (hfi.comp hr) lo hres
      (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q))
      (κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).1 : ℕ) : ℝ)) ?_ ?_ ?_).trans
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
      have br := prod_set_bounds hq0 κ (Fin.append βx bx) (rt := fun i => z (f i)) hcc (Finset.univ.image r)
      rw [hprodr]
      refine ⟨fun i => ?_, fun j => ?_, br.1, by rw [hρ₂]; exact br.2, hlo'', hhi''⟩
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
      · rw [hlo j]
        exact (hcc (r j)).1
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
/-- **The term of a chain's box over the frozen part, by the resonant window.** `evIF_frozP_res` for every number
of the frozen cofactor's primes. -/
theorem evIF_froz_res {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ)) {ρ₂ : ℝ}
    (hρ₂ : ρ₂ = κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 : ℕ) : ℝ)) (hLρ : 0 < L - ρ₂ - κ)
    (hres : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1) (L - ρ₂ - κ) (fun j => lo j - κ)) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ => evIF_frozP_res hβ he₁ he₂ t hb hκ r hr lo hlo hρ₂ hLρ hres

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part, when the resonant window's test passes the box `ch ++ β`.**
For `e₁, e₂ ≤ DEN`: if `chkIR` passes the box `ch ++ β` with the rest `sr` and the hint's intervals, the term of the
chain `ch` over the frozen part `frozS` of `β` and the slab is evaluated. -/
theorem evIF_froz_resT {e₁ e₂ s : ℕ} (β : List Cell) (hβl : β.length = s + 1) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN)
    (ch : List Cell) (k' : ℕ) (hch : ch.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIR (ch ++ β) sr kk hh = true) :
    EvIF (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβl)) frozR (boxFn ch (k' + 1) hch) := by
  unfold chkIR at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨_, hcells⟩, hns⟩, hT⟩ := hok
  have hc := (cellsFrom_iff 1 (ch ++ β)).1 hcells
  have hlen : (ch ++ β).length = s + 1 + (k' + 1) := by rw [List.length_append, hch, hβl]; omega
  set βx := boxFn β (s + 1) hβl with hβx
  set bx := boxFn ch (k' + 1) hch with hbx
  set cx := boxFn (ch ++ β) (s + 1 + (k' + 1)) hlen with hcx
  have hcxe : cx = Fin.append βx bx := boxFn_append_froz ch β hβl hch hlen
  have hβc : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN :=
    fun i => hc _ (List.mem_append_right _ (boxFn_mem β _ hβl i))
  have hbc : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN :=
    fun j => hc _ (List.mem_append_left _ (boxFn_mem ch _ hch j))
  -- the rest's cells and positions
  have hcsr : mList (fun c => c.1) (ch ++ β) sr = (ridx (s + 1 + (k' + 1)) sr).map fun i => (cx i).1 :=
    mList_eq (fun c => c.1) (ch ++ β) (s + 1 + (k' + 1)) hlen sr
  obtain ⟨n, hn⟩ : ∃ n, (mList (fun c => c.1) (ch ++ β) sr).length = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hns).symm⟩
  have hlenr : (ridx (s + 1 + (k' + 1)) sr).length = n + 1 := by rw [← hn, hcsr, List.length_map]
  obtain ⟨r, hrdef⟩ : ∃ r : Fin (n + 1) → Fin (s + 1 + (k' + 1)),
      r = fun j : Fin (n + 1) => (ridx (s + 1 + (k' + 1)) sr)[(j : ℕ)]'(by rw [hlenr]; exact j.2) := ⟨_, rfl⟩
  have hr : Function.Injective r := by
    intro i j hij
    rw [hrdef] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff (ridx_nodup _ _)).1 hij)
  have himg : Finset.univ.image r = mset (s + 1 + (k' + 1)) sr := by
    ext i
    rw [← mem_ridx]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      rw [hrdef]
      exact List.getElem_mem _
    · intro hi
      obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hi
      exact ⟨⟨j, by rw [← hlenr]; exact hj⟩, by rw [hrdef]; exact hji⟩
  have hcsj : ∀ j : Fin (n + 1), (mList (fun c => c.1) (ch ++ β) sr).getD j 0 = (cx (r j)).1 := by
    intro j
    rw [List.getD_eq_getElem _ _ (by rw [hn]; exact j.2)]
    simp only [hcsr, List.getElem_map, hrdef]
  have hc1 : ∀ c ∈ mList (fun c => c.1) (ch ++ β) sr, 1 ≤ c := by
    intro c hcm
    rw [hcsr, List.mem_map] at hcm
    obtain ⟨i, -, rfl⟩ := hcm
    exact (hc _ (boxFn_mem (ch ++ β) _ hlen i)).1
  -- the exponent
  have hD := DEN_pos'
  obtain ⟨hden, -⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos L_pos (by exact_mod_cast hD)
  have hLeq : (Lnum : ℝ) / Lden = L := IBFits.L_eq
  have hLd : 0 < Lden := by exact_mod_cast hden
  -- the condition on the rest's cells
  have hres := SieveResTest.resT_sound_cells hLd hc1 hT
  have hhs : mSum (fun c => c.2) (ch ++ β) sr + 1 < DEN := by
    have := SieveResTest.resT_hs hT
    simpa [SieveResTest.DEN, SieveCert.DEN] using this
  have hDD : (SieveResTest.DEN : ℝ) = (DEN : ℝ) := by norm_num [SieveResTest.DEN, SieveCert.DEN]
  rw [hLeq, hDD, ← hκdef, hn] at hres
  have hshi : ∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 = mSum (fun c => c.2) (ch ++ β) sr := by
    rw [himg, ← hcxe, hcx, sum_mset (fun c => c.2) (ch ++ β) _ hlen sr]
  have hLρ : 0 < L - κ * (mSum (fun c => c.2) (ch ++ β) sr : ℝ) - κ := by
    have h1 : ((mSum (fun c => c.2) (ch ++ β) sr : ℕ) : ℝ) + 1 < DEN := by exact_mod_cast hhs
    have h2 : κ * (((mSum (fun c => c.2) (ch ++ β) sr : ℕ) : ℝ) + 1) < κ * DEN := mul_lt_mul_of_pos_left h1 hκ
    have h3 : κ * DEN = L := by rw [hκdef]; field_simp
    linarith
  refine evIF_froz_res hβc he₁ he₂ hbc hκdef r hr
    (fun j => κ * ((mList (fun c => c.1) (ch ++ β) sr).getD j 0 : ℝ)) (fun j => ?_) (ρ₂ := κ * (mSum (fun c => c.2)
      (ch ++ β) sr : ℝ)) (by rw [hshi]) hLρ hres
  show κ * ((mList (fun c => c.1) (ch ++ β) sr).getD (j : ℕ) 0 : ℝ) = κ * ((Fin.append βx bx (r j)).1 : ℝ)
  rw [hcsj j, hcxe]

end SieveAd

#print axioms SieveAd.evIF_froz_resT
