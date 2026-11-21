/-
# The chain's sifted cofactor over the frozen part, in the window's rest

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozRes.lean` evaluates the term of a chain's box over the frozen part of a reversal by the
resonant window, its rest among the frozen primes and the chain's, its variable everything else, the chain's cofactor
included. The chain's cofactor, free of primes below the chain's least, can be in the rest too, as one part whatever
its number of primes (`SieveTypeIIHM.sifGrp`), in the cell that the slab and the chain's cells leave it. With the
frozen number `R` in the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`, the chain's upper ends with `e₂` summing to at most `DEN − 2`
put `R·∏c` below `N₁`; the cofactor `y` is then at least `x^{(DEN − e₂ − Σhi − 1)/DEN}` and the chain's least prime,
and at most `x^{(DEN − e₁ − Σlo + 1)/DEN}`.

* `frozCof_facts`: those facts for a tuple of `frozW`.
* `evIF_frozP_sif`: **the term over `frozP … t` is evaluated with the chain's cofactor in the rest**, given for each
  number `u ≥ 1` of the cofactor's primes an estimate `FullEst` of the full tuples whose rest's primes and cofactor
  lie in a region `Reg` that the cells give. `evIF_froz_sif`: **so is the term over the frozen part.**
* `evIF_froz_resC`: the region of the resonant window, when `ResBox` holds for the rest at injective positions `r` of
  the box and the cofactor's cell after them (`SieveTypeIIHM.fullEst_sif_of_res`).
* `evIF_froz_resTC`: **when `chkIRF` passes the box `ch ++ β`**: by `evIF_froz_resC` with the cofactor's cell when the
  bit after the box's cells is set, by `evIF_froz_resT` otherwise.

The file imports `SieveAdFrozRes.lean`, `SieveAdFrozResDefs.lean` and `SieveAdResCof.lean`.
-/
import SieveAdFrozRes
import SieveAdFrozResDefs
import SieveAdResCof

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK]

/-- **The chain's cofactor over the frozen part.** For a tuple `w` of `frozW … t bx` at a large modulus, with the
chain's upper ends and `e₂` summing to at most `DEN − 2`: the tuple's product is at most `N₁`, and every `y` at least
the chain's last prime with `N₁ < ∏w·y ≤ N₂` lies in `[x^{max(DEN − e₂ − Σhi − 1, lo₀)/DEN},
x^{(DEN − e₁ − Σlo + 1)/DEN}]`. -/
theorem frozCof_facts {q : ℕ} (hq : Big q) {e₁ e₂ s t k' : ℕ} {βx : Fin (s + 1) → Cell}
    {bx : Fin (k' + 1) → Cell} (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) {w : Fin (s + 1 + t + (k' + 1)) → ℕ}
    (hw : w ∈ frozW q e₁ e₂ βx t bx) :
    ∏ i, w i ≤ N1 q ∧
      ∀ y : ℕ, w (posC s t (k' + 1) (Fin.last k')) ≤ y → N1 q < (∏ i, w i) * y → (∏ i, w i) * y ≤ N2 q →
        Xe q (maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1) ≤ y ∧
          (y : ℝ) ≤ Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) := by
  obtain ⟨-, hx3, hN1, hN2, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hN1' : Xe q (DEN - 1) ≤ N1 q := by
    have h := hN1
    unfold Xe
    rw [Nat.cast_sub (by have := SieveCert.DEN_pos; omega), Nat.cast_one]
    exact h
  have hN2' : (N2 q : ℝ) < Xe q (DEN + 1) := by
    unfold Xe
    push_cast
    exact hN2
  obtain ⟨-, hsem, -, -⟩ := frozW_iff.1 hw
  obtain ⟨-, ⟨-, hcc⟩, hRlo, hRhi⟩ := (sem_frozA q e₁ e₂ βx t bx w).1 hsem
  -- the frozen number `R` and the chain's product `C`
  have hpr := prod_set_bounds_x hx0 (bx := bx) (rt := fun j => w (posC s t (k' + 1) j)) hcc Finset.univ
  have hplo : Xe q (∑ j, (bx j).1) ≤ ∏ j, (w (posC s t (k' + 1) j) : ℝ) := hpr.1
  have hphi : ∏ j, (w (posC s t (k' + 1) j) : ℝ) ≤ Xe q (∑ j, (bx j).2) := hpr.2
  have hsplit : ((∏ i, w i : ℕ) : ℝ) =
      (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * ∏ j, (w (posC s t (k' + 1) j) : ℝ) := by
    rw [Nat.cast_prod, Fin.prod_univ_add]
    unfold posAY
    rw [Finset.prod_map]
    rfl
  have hR0 : 0 < ∏ i ∈ posAY s t (k' + 1), (w i : ℝ) := lt_trans (Xe_pos hx0 e₁) hRlo
  have hC0 : 0 < ∏ j, (w (posC s t (k' + 1) j) : ℝ) := lt_of_lt_of_le (Xe_pos hx0 _) hplo
  refine ⟨?_, fun y hy hlo hhi => ⟨?_, ?_⟩⟩
  · -- the product is below `N₁`
    have h1 : (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * ∏ j, (w (posC s t (k' + 1) j) : ℝ) ≤
        Xe q e₂ * Xe q (∑ j, (bx j).2) := mul_le_mul hRhi hphi hC0.le (Xe_pos hx0 _).le
    have h2 : Xe q e₂ * Xe q (∑ j, (bx j).2) ≤ N1 q := by
      rw [← Xe_add hx0]
      exact (Xe_mono hx1 (by omega)).trans hN1'
    have h3 : ((∏ i, w i : ℕ) : ℝ) ≤ N1 q := by rw [hsplit]; linarith
    exact_mod_cast h3
  · -- the cofactor's lower end
    refine Xe_maxN_le ?_ ((hcc (Fin.last k')).1.trans (by exact_mod_cast hy))
    have hlo' : (N1 q : ℝ) <
        (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * (∏ j, (w (posC s t (k' + 1) j) : ℝ)) * y := by
      have h : (N1 q : ℝ) < ((∏ i, w i : ℕ) : ℝ) * y := by exact_mod_cast hlo
      rwa [hsplit] at h
    have hsplitX : Xe q (DEN - 1) =
        Xe q e₂ * Xe q (∑ j, (bx j).2) * Xe q (DEN - e₂ - ∑ j, (bx j).2 - 1) := by
      rw [← Xe_add hx0, ← Xe_add hx0]
      congr 1
      omega
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * (∏ j, (w (posC s t (k' + 1) j) : ℝ)) * y ≤
        Xe q e₂ * Xe q (∑ j, (bx j).2) * Xe q (DEN - e₂ - ∑ j, (bx j).2 - 1) :=
      mul_le_mul (mul_le_mul hRhi hphi hC0.le (Xe_pos hx0 _).le) hcon.le (Nat.cast_nonneg _)
        (mul_pos (Xe_pos hx0 _) (Xe_pos hx0 _)).le
    rw [← hsplitX] at h1
    linarith
  · -- the cofactor's upper end
    have hhi' : (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * (∏ j, (w (posC s t (k' + 1) j) : ℝ)) * y ≤ N2 q := by
      have h : ((∏ i, w i : ℕ) : ℝ) * y ≤ N2 q := by exact_mod_cast hhi
      rwa [hsplit] at h
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Xe q (DEN + 1) ≤ Xe q e₁ * Xe q (∑ j, (bx j).1) * Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) := by
      rw [← Xe_add hx0, ← Xe_add hx0]
      exact Xe_mono hx1 (by omega)
    have h2 : Xe q e₁ * Xe q (∑ j, (bx j).1) * Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) <
        (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * (∏ j, (w (posC s t (k' + 1) j) : ℝ)) * y :=
      mul_lt_mul' (mul_le_mul hRlo.le hplo (Xe_pos hx0 _).le hR0.le) hcon (Xe_pos hx0 _).le (mul_pos hR0 hC0)
    linarith

/-! ### The term is evaluated -/

set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part with a frozen cofactor of `t` primes, with the chain's cofactor
in the rest.** Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, `e₁, e₂ ≤ DEN`, and the chain's
upper ends with `e₂` sum to at most `DEN − 2`. Let the rest be at the injective positions `r` of the box (frozen
primes first, then the chain's), and `Reg q xs m` a region of the rest's primes `xs` and the chain's cofactor `m` that
holds when each `xs j` is in the cell of `r j` and `m` in `[x^{max(DEN − e₂ − Σhi − 1, lo₀)/DEN},
x^{(DEN − e₁ − Σlo + 1)/DEN}]`. If for each number `u ≥ 1` of the cofactor's primes `FullEst L κ (n + u)` holds for
the full tuples whose rest's primes and cofactor's product, one part (`SieveTypeIIHM.sifGrp`), lie in `Reg`, the term
of the chain's box over `frozP … t` is evaluated. -/
theorem evIF_frozP_sif {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ} {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ}
    (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    {Reg : ℕ → (Fin (n + 1) → ℕ) → ℕ → Prop}
    (hreg : ∀ q : ℕ, Big q → ∀ (xs : Fin (n + 1) → ℕ) (m : ℕ),
      (∀ j, Xe q (Fin.append βx bx (r j)).1 ≤ xs j ∧ (xs j : ℝ) < Xe q (Fin.append βx bx (r j)).2) →
      Xe q (maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1) ≤ m →
      (m : ℝ) ≤ Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) → Reg q xs m)
    (hfull : ∀ u : ℕ, 1 ≤ u → SieveTypeIIHM.FullEst L κ (n + u) (fun q x =>
      Reg q (fun i => x (Fin.castLE (by omega) i))
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n + u + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i))) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  intro η hη
  -- the estimates at `v + 1` primes in the cofactor, `v < DEN`
  have H := fun v : ℕ => hfull (v + 1) (by omega) (s + 1 + t + k' + 1 + (v + 1))
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + (v + 1) * (v + 1) + (v + 1) + 2) (L + 1) (by linarith)
  choose δf hδf q₀f hq₀f using H
  -- (the minimum and the maximum over the `DEN` numbers, kept abstract: `DEN` is `2^40`)
  have hne : (Finset.range DEN).Nonempty := ⟨0, Finset.mem_range.2 SieveCert.DEN_pos⟩
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ v < DEN, δ₀ ≤ δf v :=
    ⟨(Finset.range DEN).inf' hne δf, (Finset.lt_inf'_iff hne).2 fun v _ => hδf v,
      fun v hv => Finset.inf'_le δf (Finset.mem_range.2 hv)⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : ℕ, ∀ v < DEN, q₀f v ≤ q₁ :=
    ⟨(Finset.range DEN).sup q₀f, fun v hv => Finset.le_sup (f := q₀f) (Finset.mem_range.2 hv)⟩
  clear hne
  have hev := (tendsto_rpow_atTop (half_pos hδ₀)).eventually_ge_atTop ((DEN : ℝ) + 1)
  filter_upwards [eventually_ge_atTop q₁, le_Xq (half_pos hδ₀) hη, big_ev,
    tendsto_natCast_atTop_atTop.eventually hev] with q hq hXle hbig hqK a ha
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
  rw [dIF_frozP_eq hbig a hβD he₁ he₂ t hbD1]
  -- the box's positions in the full tuple
  set f : Fin (s + 1 + (k' + 1)) → Fin (s + 1 + t + k' + 1) := fun i => posB s t (k' + 1) i with hf
  have hfi : Function.Injective f := posB_injective s t (k' + 1)
  have hfr : Function.Injective fun j => f (r j) := hfi.comp hr
  -- each number of the cofactor's primes
  have hbound : ∀ u ∈ Finset.range (DEN + 1),
      |∑ z ∈ RTg (s + 1 + t + k' + 1 + u) (N2 q)
          (fullTL (s + 1 + t + k') u (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))| ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀) := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with hu0 | hu0
    · -- no cofactor: the frozen number times the chain's product is at most `N₁`
      subst hu0
      rw [Finset.sum_eq_zero fun z hz => ?_, abs_zero]
      · positivity
      exfalso
      rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
      obtain ⟨hzp, hzΩ⟩ := hz
      have hzp' : ∀ i, z i ≤ N2 q ∧ (z i).Prime := fun i => SieveTypeIIU.mem_primesLe.1 (hzp i)
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd 0 i) := fun i => (hzp' _).2.one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hzp' _).2.one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, -, hlo', -⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := 0)
        (frozΩ q e₁ e₂ βx t bx) (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
      have hrtW : (fun i => z (Fin.castAdd 0 i)) ∈ frozW q e₁ e₂ βx t bx := by
        rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun i => SieveTypeIIU.mem_primesLe.2 (hzp' _), hΩ'⟩
      obtain ⟨hf0, -⟩ := frozCof_facts hbig hshi hrtW
      have hw : ((∏ i, z (Fin.castAdd 0 i) : ℕ) : ℝ) = ∏ i, (z (Fin.castAdd 0 i) : ℝ) := Nat.cast_prod _ _
      rw [Fin.prod_univ_zero, mul_one, ← hw] at hlo'
      have h1 : N1 q < ∏ i, z (Fin.castAdd 0 i) := by exact_mod_cast hlo'
      have h2 : ∏ i, z (Fin.castAdd 0 i) ≤ N1 q := hf0
      omega
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have hv : v < DEN := by have := Finset.mem_range.1 hu; omega
    have hq' : q₀f v ≤ q := (hq₁ v hv).trans hq
    have hcast : ∑ z ∈ RTg (s + 1 + t + k' + 1 + (v + 1)) (N2 q)
        (fullTL (s + 1 + t + k') (v + 1) (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)), dw q a (∏ i, z i) =
        ((∑ z ∈ RTg (s + 1 + t + k' + 1 + (v + 1)) (N2 q)
          (fullTL (s + 1 + t + k') (v + 1) (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
          (gA q a (∏ i, z i) - gB q (∏ i, z i)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun z _ => dw_eq q a _
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast]
    refine (hq₀f v q hq' a ha (SieveTypeIIHM.sifR (v + 1) fun j => f (r j)) (SieveTypeIIHM.sifR_injective hfr)
      (fullTL (s + 1 + t + k') (v + 1) (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)) ?_ ?_ ?_).trans ?_
    · refine (length_fullTL_le (s + 1 + t + k') (v + 1) _ _ _).trans ?_
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
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd (v + 1) i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlast, hlo', hhi'⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := v + 1)
        (frozΩ q e₁ e₂ βx t bx) (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd (v + 1) i)) * ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
        Fin.prod_univ_add z
      have hlo'' : N1 q < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo'
      have hhi'' : ∏ i, z i ≤ N2 q := by rw [hprod]; exact_mod_cast hhi'
      have hz0 : 0 < ∏ i, z i := by omega
      have hrtW : (fun i => z (Fin.castAdd (v + 1) i)) ∈ frozW q e₁ e₂ βx t bx := by
        rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun i => SieveTypeIIU.mem_primesLe.2 ⟨?_, hz _⟩, hΩ'⟩
        exact (Nat.le_of_dvd hz0 (Finset.dvd_prod_of_mem z (Finset.mem_univ _))).trans hhi''
      have hge := frozW_ge hx1 (f := 1) (hβ (Fin.last s)).1 (fun j => (hb j).1) hrtW
      have hcell := cells_posB hrtW
      -- the cofactor's cell
      obtain ⟨-, hf1⟩ := frozCof_facts hbig hshi hrtW
      have hylast : z (Fin.castAdd (v + 1) (Fin.last (s + 1 + t + k'))) ≤
          ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
        (hlast ⟨0, by omega⟩).trans (Finset.single_le_prod (fun b _ => hy1 b) (Finset.mem_univ _))
      obtain ⟨hcy, hcY⟩ := hf1 (∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b)) hylast
        (by have h := hlo''; rw [hprod] at h; exact h) (by have h := hhi''; rw [hprod] at h; exact h)
      refine ⟨fun i => ?_, ?_, hlo'', hhi''⟩
      · -- every prime is at least `q^κ`
        have h1 : (q : ℝ) ^ κ = Xe q 1 := by
          have := hqx 1
          rwa [Nat.cast_one, mul_one] at this
        rw [h1]
        refine Fin.addCases (fun i' => ?_) (fun b => ?_) i
        · exact hge i'
        · have h2 : Xe q 1 ≤ (z (Fin.castAdd (v + 1) (Fin.last (s + 1 + t + k'))) : ℝ) :=
            hge (Fin.last (s + 1 + t + k'))
          have h3 : (z (Fin.castAdd (v + 1) (Fin.last (s + 1 + t + k'))) : ℝ) ≤
              z (Fin.natAdd (s + 1 + t + k' + 1) b) := by exact_mod_cast hlast b
          exact h2.trans h3
      · -- the region: the rest's primes in their cells, the cofactor in its cell
        have hxs : (fun i : Fin (n + 1) =>
            z (SieveTypeIIHM.sifR (v + 1) (fun j => f (r j)) (Fin.castLE (by omega) i))) =
            fun i => z (Fin.castAdd (v + 1) (f (r i))) := by
          funext i
          simp [SieveTypeIIHM.sifR, Fin.is_le]
        have hm : ∏ i ∈ Finset.univ.filter (fun i : Fin (n + (v + 1) + 1) => SieveTypeIIHM.sifGrp n i = n + 1),
            z (SieveTypeIIHM.sifR (v + 1) (fun j => f (r j)) i) = ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
          SieveTypeIIHM.prod_filter_sifGrp_cof _ z
        beta_reduce
        rw [hxs, hm]
        exact hreg q hbig _ _ (fun j => hcell (r j)) hcy hcY
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1' (by linarith [hδ₀le v hv])) hφ
  -- the numbers of the cofactor's primes together
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_)
  rw [Finset.card_range, nsmul_eq_mul]
  calc ((DEN + 1 : ℕ) : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀))
      ≤ (q : ℝ) ^ (δ₀ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀)) :=
        mul_le_mul_of_nonneg_right (by push_cast; exact hqK) (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀ / 2) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring
    _ ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := mul_le_mul_of_nonneg_left hXle hφ

/-- **The term of a chain's box over the frozen part, with the chain's cofactor in the rest.** `evIF_frozP_sif` for
every number of the frozen cofactor's primes. -/
theorem evIF_froz_sif {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ}
    (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    {Reg : ℕ → (Fin (n + 1) → ℕ) → ℕ → Prop}
    (hreg : ∀ q : ℕ, Big q → ∀ (xs : Fin (n + 1) → ℕ) (m : ℕ),
      (∀ j, Xe q (Fin.append βx bx (r j)).1 ≤ xs j ∧ (xs j : ℝ) < Xe q (Fin.append βx bx (r j)).2) →
      Xe q (maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1) ≤ m →
      (m : ℝ) ≤ Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) → Reg q xs m)
    (hfull : ∀ u : ℕ, 1 ≤ u → SieveTypeIIHM.FullEst L κ (n + u) (fun q x =>
      Reg q (fun i => x (Fin.castLE (by omega) i))
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n + u + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i))) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ => evIF_frozP_sif hβ he₁ he₂ t hb hshi hκ r hr hreg hfull

/-- **The term of a chain's box over the frozen part, by the resonant window with the chain's cofactor in the
rest.** With the rest at the injective positions `r` of the box (frozen primes first, then the chain's) and the
chain's cofactor, `lo j = κ·lo(r j)`, `lo (n + 1) = κ·max(DEN − e₂ − Σhi − 1, lo₀)` and
`ρ₂ = κ·(Σ hi + DEN − e₁ − Σlo + 1)` for `κ = L/DEN`: if `ResBox` holds for the rest with `L − ρ₂ − κ > 0`, the term
is evaluated (`evIF_froz_sif` on `SieveTypeIIHM.fullEst_sif_of_res`). -/
theorem evIF_froz_resC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ)) {ρ₂ : ℝ}
    (hρ₂ : ρ₂ = κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 +
      (DEN - e₁ - ∑ j, (bx j).1 + 1) : ℕ) : ℝ)) (hLρ : 0 < L - ρ₂ - κ)
    (hres : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1 + 1) (L - ρ₂ - κ) (fun j => lo j - κ)) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hD := DEN_pos'
  have hκ0 : 0 < κ := by rw [hκ]; exact div_pos L_pos (by exact_mod_cast hD)
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; positivity
  refine evIF_froz_sif hβ he₁ he₂ hb hshi hκ r hr
    (Reg := fun q xs m => (∀ j : Fin (n + 1), (q : ℝ) ^ lo j ≤ xs j) ∧ (q : ℝ) ^ lo (n + 1) ≤ m ∧
      (((∏ j, xs j) * m : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) ?_ fun u hu => ?_
  · intro q hbig xs m hxs hm1 hm2
    obtain ⟨-, hx3, -, -, -⟩ := big_facts hbig
    have hx0 : 0 < xq q := by linarith
    have hqx : ∀ e : ℕ, (q : ℝ) ^ (κ * (e : ℝ)) = Xe q e := fun e => by rw [hκ, qpow_eq]; rfl
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rw [hlo j, hqx]
      exact (hxs j).1
    · rw [hlon, hqx]
      exact hm1
    · have hpr := (prod_set_bounds_x hx0 (bx := fun j => Fin.append βx bx (r j)) (rt := xs) hxs Finset.univ).2
      have hsum : ∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 = ∑ j, (Fin.append βx bx (r j)).2 :=
        Finset.sum_image fun i _ j _ h => hr h
      rw [hρ₂, hsum, hqx, Xe_add hx0, Nat.cast_mul, Nat.cast_prod]
      exact mul_le_mul hpr hm2 (Nat.cast_nonneg _) (Xe_pos hx0 _).le
  · exact SieveTypeIIHM.fullEst_sif_of_res SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half SieveCurveHx.counts_hx
      L_pos L_le hκ0 hρ₂0 hκ0 hLρ hres u hu

variable [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 4000000 in
/-- **The term of a chain's box over the frozen part, when the resonant window's test with the chain's cofactor
passes the box `ch ++ β`.** For `e₁, e₂ ≤ DEN`: if `chkIRF` passes the box `ch ++ β` with the rest `sr` and the hint's
intervals, the term of the chain `ch` over the frozen part `frozS` of `β` and the slab is evaluated: by
`evIF_froz_resC` with the cofactor's cell when the bit after the box's cells is set, by `evIF_froz_resT` otherwise. -/
theorem evIF_froz_resTC {e₁ e₂ s : ℕ} (β : List Cell) (hβl : β.length = s + 1) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN)
    (ch : List Cell) (k' : ℕ) (hch : ch.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRF e₁ e₂ β (ch ++ β) sr kk hh = true) :
    EvIF (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβl)) frozR (boxFn ch (k' + 1) hch) := by
  unfold chkIRF at hok
  beta_reduce at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩ := hok
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr (ch ++ β).length) 1) 1 = true
  swap
  · -- no cofactor: `chkIR`
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hok' : chkIR (ch ++ β) sr kk hh = true := by
      unfold chkIR
      rw [rpass_eq]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩
    exact evIF_froz_resT β hβl he₁ he₂ ch k' hch sr kk hh hok'
  rw [hbit, Bool.cond_true] at hcof
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcof
  obtain ⟨hshi, hT⟩ := hcof
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
  -- the chain's sums and its least prime
  have hlos : loSum (ch ++ β) - loSum β = ∑ j, (bx j).1 := by
    have e1 : loSum (ch ++ β) = loSum ch + loSum β := by
      rw [loSum_eq, loSum_eq, loSum_eq, List.map_append, List.sum_append]
    have e2 : loSum ch = ∑ j, (bx j).1 := by rw [loSum_eq, hbx, sum_boxFn (fun c => c.1) ch _ hch]
    omega
  have hhis : hiSum (ch ++ β) - hiSum β = ∑ j, (bx j).2 := by
    have e1 : hiSum (ch ++ β) = hiSum ch + hiSum β := by
      rw [hiSum_eq, hiSum_eq, hiSum_eq, List.map_append, List.sum_append]
    have e2 : hiSum ch = ∑ j, (bx j).2 := by rw [hiSum_eq, hbx, sum_boxFn (fun c => c.2) ch _ hch]
    omega
  have hhead : headLo (ch ++ β) = (bx (Fin.last k')).1 := by
    rw [hbx, ← headLo_eq ch k' hch]
    cases ch with
    | nil => simp at hch
    | cons c b => rfl
  simp only [Nat.add_eq, Nat.sub_eq] at hT hshi
  rw [hlos] at hT
  rw [hhis] at hT hshi
  rw [hhead] at hT
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
  -- the rest with the cofactor's cell after the box's
  set cl := maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 with hcl
  set cs := mList (fun c => c.1) (ch ++ β) sr ++ [cl] with hcs
  set hs := mSum (fun c => c.2) (ch ++ β) sr + (DEN - e₁ - ∑ j, (bx j).1 + 1) with hhs
  have hcsn : cs.length = n + 1 + 1 := by rw [hcs, List.length_append, hn]; rfl
  have hcsj : ∀ j : Fin (n + 1), cs.getD j 0 = (cx (r j)).1 := by
    intro j
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_left (by rw [hn]; exact j.2)]
    simp only [hcsr, List.getElem_map, hrdef]
  have hcsl : cs.getD (n + 1) 0 = cl := by
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_right (by rw [hn])]
    simp [hn]
  have hc1 : ∀ c ∈ cs, 1 ≤ c := by
    intro c hcm
    rw [hcs, List.mem_append, List.mem_singleton] at hcm
    rcases hcm with hcm | rfl
    · rw [hcsr, List.mem_map] at hcm
      obtain ⟨i, -, rfl⟩ := hcm
      exact (hc _ (boxFn_mem (ch ++ β) _ hlen i)).1
    · rw [hcl]
      rcases maxN_cases (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 with h' | h'
      · rw [h']
        omega
      · rw [h']
        exact (hbc _).1
  -- the exponent
  have hD := DEN_pos'
  obtain ⟨hden, -⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos L_pos (by exact_mod_cast hD)
  have hLeq : (Lnum : ℝ) / Lden = L := IBFits.L_eq
  have hLd : 0 < Lden := by exact_mod_cast hden
  -- the condition on the rest's cells
  have hres := SieveResTest.resX_sound_cells hLd hc1 hT
  have hhs1 : hs + 1 < DEN := by
    have := SieveResTest.resX_hs hT
    simpa [SieveResTest.DEN, SieveCert.DEN] using this
  have hDD : (SieveResTest.DEN : ℝ) = (DEN : ℝ) := by norm_num [SieveResTest.DEN, SieveCert.DEN]
  rw [hLeq, hDD, ← hκdef, hcsn] at hres
  have hLρ : 0 < L - κ * (hs : ℝ) - κ := by
    have h1 : ((hs : ℕ) : ℝ) + 1 < DEN := by exact_mod_cast hhs1
    have h2 : κ * (((hs : ℕ) : ℝ) + 1) < κ * DEN := mul_lt_mul_of_pos_left h1 hκ
    have h3 : κ * DEN = L := by rw [hκdef]; field_simp
    linarith
  have hshi' : ∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 = mSum (fun c => c.2) (ch ++ β) sr := by
    rw [himg, ← hcxe, hcx, sum_mset (fun c => c.2) (ch ++ β) _ hlen sr]
  refine evIF_froz_resC hβc he₁ he₂ hbc hshi hκdef r hr (fun j => κ * (cs.getD j 0 : ℝ)) (fun j => ?_) ?_
    (ρ₂ := κ * (hs : ℝ)) ?_ hLρ hres
  · show κ * (cs.getD (j : ℕ) 0 : ℝ) = κ * ((Fin.append βx bx (r j)).1 : ℝ)
    rw [hcsj j, hcxe]
  · show κ * (cs.getD (n + 1) 0 : ℝ) = _
    rw [hcsl]
  · rw [hshi', hhs]

end SieveAd

#print axioms SieveAd.evIF_froz_resTC
