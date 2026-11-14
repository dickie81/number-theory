/-
# The chain's cofactor over the frozen part, in the resonant window's rest

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozRes.lean` evaluates the term of a chain's box over the frozen part of a reversal by the
resonant window, its rest among the frozen primes and the chain's, its variable everything else, the chain's cofactor
included. When every multiple's chain cofactor is one prime, that prime can be in the rest too, in the cell that the
slab and the chain's cells leave it. With the frozen number `R` in the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`: the chain's
upper ends with `e₂` summing to at most `DEN − 2` put `R·∏c` below `N₁`, and its lower ends with `e₁` and twice its
least prime's reaching `DEN + 1` make two more primes at least the least overshoot `N₂`. The cofactor `y` is then at
least `x^{(DEN − e₂ − Σhi − 1)/DEN}` and the chain's least prime, and at most `x^{(DEN − e₁ − Σlo + 1)/DEN}`.

* `frozCof_facts`: those facts for a tuple of `frozW`.
* `evIF_frozP_resC`: **the term over `frozP … t` is evaluated with the chain's cofactor in the rest**, when
  `ResBox` holds for the rest at injective positions `r` of the box and the cofactor's cell after them.
* `evIF_froz_resC`: **so is the term over the frozen part.**
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

/-- **The chain's cofactor over the frozen part is one prime.** For a tuple `w` of `frozW … t bx` at a large modulus,
with the chain's upper ends and `e₂` summing to at most `DEN − 2` and its lower ends with `e₁` and twice its least
prime's at least `DEN + 1`: the tuple's product is at most `N₁`, the product times the square of the chain's last
prime is above `N₂`, and every `y` at least that prime with `N₁ < ∏w·y ≤ N₂` lies in
`[x^{max(DEN − e₂ − Σhi − 1, lo₀)/DEN}, x^{(DEN − e₁ − Σlo + 1)/DEN}]`. -/
theorem frozCof_facts {q : ℕ} (hq : Big q) {e₁ e₂ s t k' : ℕ} {βx : Fin (s + 1) → Cell}
    {bx : Fin (k' + 1) → Cell} (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN)
    (hslo : DEN + 1 ≤ e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1) {w : Fin (s + 1 + t + (k' + 1)) → ℕ}
    (hw : w ∈ frozW q e₁ e₂ βx t bx) :
    ∏ i, w i ≤ N1 q ∧
      N2 q < (∏ i, w i) * (w (posC s t (k' + 1) (Fin.last k')) * w (posC s t (k' + 1) (Fin.last k'))) ∧
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
  refine ⟨?_, ?_, fun y hy hlo hhi => ⟨?_, ?_⟩⟩
  · -- the product is below `N₁`
    have h1 : (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * ∏ j, (w (posC s t (k' + 1) j) : ℝ) ≤
        Xe q e₂ * Xe q (∑ j, (bx j).2) := mul_le_mul hRhi hphi hC0.le (Xe_pos hx0 _).le
    have h2 : Xe q e₂ * Xe q (∑ j, (bx j).2) ≤ N1 q := by
      rw [← Xe_add hx0]
      exact (Xe_mono hx1 (by omega)).trans hN1'
    have h3 : ((∏ i, w i : ℕ) : ℝ) ≤ N1 q := by rw [hsplit]; linarith
    exact_mod_cast h3
  · -- two primes at least the chain's last overshoot `N₂`
    have hlast := (hcc (Fin.last k')).1
    have h0 := Xe_pos hx0 (bx (Fin.last k')).1
    have hRC : Xe q e₁ * Xe q (∑ j, (bx j).1) <
        (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * ∏ j, (w (posC s t (k' + 1) j) : ℝ) :=
      mul_lt_mul hRlo hplo (Xe_pos hx0 _) hR0.le
    have hsq : Xe q (bx (Fin.last k')).1 * Xe q (bx (Fin.last k')).1 ≤
        (w (posC s t (k' + 1) (Fin.last k')) : ℝ) * w (posC s t (k' + 1) (Fin.last k')) :=
      mul_le_mul hlast hlast h0.le (h0.le.trans hlast)
    have h1 : Xe q (DEN + 1) < (∏ i ∈ posAY s t (k' + 1), (w i : ℝ)) * (∏ j, (w (posC s t (k' + 1) j) : ℝ)) *
        ((w (posC s t (k' + 1) (Fin.last k')) : ℝ) * w (posC s t (k' + 1) (Fin.last k'))) := by
      calc Xe q (DEN + 1) ≤ Xe q (e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1) := Xe_mono hx1 hslo
        _ = Xe q e₁ * Xe q (∑ j, (bx j).1) * (Xe q (bx (Fin.last k')).1 * Xe q (bx (Fin.last k')).1) := by
            rw [Xe_add hx0, Xe_add hx0, two_mul, Xe_add hx0]
        _ < _ := mul_lt_mul hRC hsq (mul_pos h0 h0) (mul_pos hR0 hC0).le
    have h2 : (N2 q : ℝ) < (((∏ i, w i) * (w (posC s t (k' + 1) (Fin.last k')) *
        w (posC s t (k' + 1) (Fin.last k'))) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, hsplit]
      push_cast
      linarith
    exact_mod_cast h2
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
/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, by the resonant window with the
chain's cofactor in the rest.** Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, `e₁, e₂ ≤ DEN`,
the chain's upper ends with `e₂` summing to at most `DEN − 2`, and its lower ends with `e₁` and twice its least
prime's at least `DEN + 1`. Let the rest be at the injective positions `r` of the box (frozen primes first, then the
chain's) and the chain's cofactor, with `lo j = κ·lo(r j)`, `lo (n + 1) = κ·max(DEN − e₂ − Σhi − 1, lo₀)` and
`ρ₂ = κ·(Σ hi + DEN − e₁ − Σlo + 1)`, for `κ = L/DEN`. If `ResBox` holds for the rest with `L − ρ₂ − κ > 0`, the term
of the chain's box over `frozP … t` is evaluated. -/
theorem evIF_frozP_resC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ} {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) (hslo : DEN + 1 ≤ e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ)) {ρ₂ : ℝ}
    (hρ₂ : ρ₂ = κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 +
      (DEN - e₁ - ∑ j, (bx j).1 + 1) : ℕ) : ℝ)) (hLρ : 0 < L - ρ₂ - κ)
    (hres : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1 + 1) (L - ρ₂ - κ) (fun j => lo j - κ)) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; positivity
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIHM.full_res_exp SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half
    SieveCurveHx.counts_hx hL0 L_le hκ0 (s + 1 + t + k' + 1 + 1)
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + 1 * 1 + 1 + 2) (Λ₁ := L + 1) (by linarith) hρ₂0 hκ0 hLρ
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
  refine (hq₀ q hq a ha (n + 1) (SieveTypeIIHM.snocR fun j => f (r j)) (SieveTypeIIHM.snocR_injective hfr) lo
    hres (fullTL (s + 1 + t + k') 1 (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)) 0 ?_ ?_ ?_).trans
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
    have br := prod_set_bounds hq0 κ (Fin.append βx bx) (rt := fun i => z (Fin.castAdd 1 (f i))) hqc
      (Finset.univ.image r)
    have hprodr : ∏ x ∈ Finset.univ.image (fun j => f (r j)), z (Fin.castAdd 1 x) =
        ∏ i ∈ Finset.univ.image r, z (Fin.castAdd 1 (f i)) := by
      have e : Finset.univ.image (fun j => f (r j)) = (Finset.univ.image r).image f := by
        rw [Finset.image_image]
        rfl
      rw [e, Finset.prod_image fun i _ j _ hij => hfi hij]
    have hρ := SieveTypeIIHM.prod_image_snocR (fun j => f (r j)) z
    rw [hprodr] at hρ
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, hlo'', hhi''⟩
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
        show (q : ℝ) ^ lo (n + 1) ≤ z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.last (n + 1)))
        simp only [SieveTypeIIHM.snocR, Fin.snoc_last]
        rw [hlon, hqx]
        exact hcy
      | cast j =>
        show (q : ℝ) ^ lo (j : ℕ) ≤ z (SieveTypeIIHM.snocR (fun j => f (r j)) (Fin.castSucc j))
        simp only [SieveTypeIIHM.snocR, Fin.snoc_castSucc]
        rw [hlo j]
        exact (hqc (r j)).1
    · -- the rest's product from below: at least `1`
      rw [Real.rpow_zero]
      have h : 0 < ∏ x ∈ Finset.univ.image (SieveTypeIIHM.snocR fun j => f (r j)), z x :=
        Finset.prod_pos fun i _ => (hz i).pos
      exact_mod_cast Nat.one_le_iff_ne_zero.2 h.ne'
    · -- the rest's product from above
      rw [hρ, Nat.cast_mul]
      calc ((∏ i ∈ Finset.univ.image r, z (Fin.castAdd 1 (f i)) : ℕ) : ℝ) * (z (Fin.last (s + 1 + t + k' + 1)) : ℝ)
          ≤ (q : ℝ) ^ (κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 : ℕ) : ℝ)) *
              Xe q (DEN - e₁ - ∑ j, (bx j).1 + 1) :=
            mul_le_mul br.2 hcY (Nat.cast_nonneg _) (by positivity)
        _ = (q : ℝ) ^ ρ₂ := by
            rw [← hqx (DEN - e₁ - ∑ j, (bx j).1 + 1), ← Real.rpow_add hq0, hρ₂]
            congr 1
            push_cast
            ring

/-- **The term of a chain's box over the frozen part, by the resonant window with the chain's cofactor in the
rest.** `evIF_frozP_resC` for every number of the frozen cofactor's primes. -/
theorem evIF_froz_resC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN) (hslo : DEN + 1 ≤ e₁ + ∑ j, (bx j).1 + 2 * (bx (Fin.last k')).1)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ)) {ρ₂ : ℝ}
    (hρ₂ : ρ₂ = κ * ((∑ i ∈ Finset.univ.image r, (Fin.append βx bx i).2 +
      (DEN - e₁ - ∑ j, (bx j).1 + 1) : ℕ) : ℝ)) (hLρ : 0 < L - ρ₂ - κ)
    (hres : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1 + 1) (L - ρ₂ - κ) (fun j => lo j - κ)) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ =>
    evIF_frozP_resC hβ he₁ he₂ t hb hshi hslo hκ r hr lo hlo hlon hρ₂ hLρ hres

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
  obtain ⟨⟨hshi, hslo⟩, hT⟩ := hcof
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
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hT hshi hslo
  rw [hlos] at hT hslo
  rw [hhis] at hT hshi
  rw [hhead] at hT hslo
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
  refine evIF_froz_resC hβc he₁ he₂ hbc hshi hslo hκdef r hr (fun j => κ * (cs.getD j 0 : ℝ)) (fun j => ?_) ?_
    (ρ₂ := κ * (hs : ℝ)) ?_ hLρ hres
  · show κ * (cs.getD (j : ℕ) 0 : ℝ) = κ * ((Fin.append βx bx (r j)).1 : ℝ)
    rw [hcsj j, hcxe]
  · show κ * (cs.getD (n + 1) 0 : ℝ) = _
    rw [hcsl]
  · rw [hshi', hhs]

end SieveAd

#print axioms SieveAd.evIF_froz_resTC
