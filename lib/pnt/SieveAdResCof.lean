/-
# The resonant window's test with the box's cofactor in the rest, in the main tree, is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The setting is a route with `RouteOK` whose exponent is `Lnum/Lden` (`SieveQ.IBFits`); the test
is `SieveAdResDefs.lean`'s `chkIRC`. Write `κ = L/DEN`. A box of the main tree whose upper ends sum to at most
`DEN − 2` and whose lower ends with twice its least prime's reach `DEN + 1` has one prime as the cofactor of each
multiple: the box's product is below `N₁`, and two primes at least its least would overshoot `N₂`. The cofactor `y`
is then at least `x^{(DEN − Σhi − 1)/DEN}` (as `N₁ ≥ x^{(DEN−1)/DEN}`) and the least prime, and below
`x^{(DEN − Σlo + 1)/DEN}` (as `N₂ < x^{(DEN+1)/DEN}`).

* `cof_facts`: those facts for a tuple of the box in its cells.
* `evI_resCE`: **a box evaluated by the resonant window with its cofactor in the rest, under more atoms**: if
  `chkIRC` passes the box, its term is evaluated (`chain_res_cof` with the cofactor's cell, or `evI_resE` when the
  cofactor's bit is clear). `evI_resC`, `resTestsFC_sound`: so the tests `resTestsFC` are sound.

The file imports `SieveAdRes.lean`, `SieveAdRev.lean`, `SieveAdFamSet.lean` and `SieveResCof.lean`.
-/
import SieveAdRes
import SieveAdRev
import SieveAdFamSet
import SieveResCof

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-- The first cell of a box is the cell of its last index, its least prime's. -/
theorem headLo_eq (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) :
    headLo bl = (boxFn bl (k' + 1) h (Fin.last k')).1 := by
  cases bl with
  | nil => simp at h
  | cons c b => simp [headLo, boxFn]

variable [Route] [RouteOK]

/-- **The cofactor's facts.** For a tuple `rt` of a box in its cells at a large modulus, with the box's upper ends
summing to at most `DEN − 2` and its lower ends with twice its least prime's at least `DEN + 1`: the product is at
most `N₁`, the product times the last prime's square is above `N₂`, and every `y` at least the last prime with
`N₁ < ∏rt·y ≤ N₂` lies in `[x^{max(DEN − Σhi − 1, lo₀)/DEN}, x^{(DEN − Σlo + 1)/DEN}]`. -/
theorem cof_facts {q : ℕ} (hq : Big q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (rt : Fin (k' + 1) → ℕ)
    (hc : ∀ i, Xe q (bx i).1 ≤ rt i ∧ (rt i : ℝ) < Xe q (bx i).2) (hlh : ∀ i, (bx i).1 ≤ (bx i).2)
    (hshi : ∑ i, (bx i).2 + 2 ≤ DEN) (hslo : DEN + 1 ≤ ∑ i, (bx i).1 + 2 * (bx (Fin.last k')).1) :
    ∏ i, rt i ≤ N1 q ∧ N2 q < (∏ i, rt i) * (rt (Fin.last k') * rt (Fin.last k')) ∧
      ∀ y : ℕ, rt (Fin.last k') ≤ y → N1 q < (∏ i, rt i) * y → (∏ i, rt i) * y ≤ N2 q →
        Xe q (maxN (DEN - ∑ i, (bx i).2 - 1) (bx (Fin.last k')).1) ≤ y ∧
          (y : ℝ) ≤ Xe q (DEN - ∑ i, (bx i).1 + 1) := by
  obtain ⟨-, hx3, hN1, hN2, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hx1' : 1 < xq q := by linarith
  have hN1' : Xe q (DEN - 1) ≤ N1 q := by
    have h := hN1
    unfold Xe
    rw [Nat.cast_sub (by have := SieveCert.DEN_pos; omega), Nat.cast_one]
    exact h
  have hN2' : (N2 q : ℝ) < Xe q (DEN + 1) := by
    unfold Xe
    push_cast
    exact hN2
  -- the product's bounds
  have hpr := prod_set_bounds_x hx0 (bx := bx) (rt := rt) hc Finset.univ
  have hplo : Xe q (∑ i, (bx i).1) ≤ ∏ i, (rt i : ℝ) := hpr.1
  have hphi : ∏ i, (rt i : ℝ) ≤ Xe q (∑ i, (bx i).2) := hpr.2
  have hcast : ∀ y : ℕ, (((∏ i, rt i) * y : ℕ) : ℝ) = (∏ i, (rt i : ℝ)) * y := fun y => by push_cast; ring
  have hslo_le : ∑ i, (bx i).1 ≤ ∑ i, (bx i).2 := Finset.sum_le_sum fun i _ => hlh i
  refine ⟨?_, ?_, fun y hy hlo hhi => ⟨?_, ?_⟩⟩
  · -- the product is below `N₁`
    have h1 : ∏ i, (rt i : ℝ) ≤ N1 q :=
      hphi.trans ((Xe_mono hx1 (by omega)).trans hN1')
    have h2 : ((∏ i, rt i : ℕ) : ℝ) ≤ N1 q := by push_cast; exact h1
    exact_mod_cast h2
  · -- two primes at least the last overshoot `N₂`
    have hlast := (hc (Fin.last k')).1
    have h1 : Xe q (DEN + 1) ≤ (∏ i, (rt i : ℝ)) * ((rt (Fin.last k') : ℝ) * rt (Fin.last k')) := by
      calc Xe q (DEN + 1) ≤ Xe q (∑ i, (bx i).1 + 2 * (bx (Fin.last k')).1) := Xe_mono hx1 hslo
        _ = Xe q (∑ i, (bx i).1) * (Xe q (bx (Fin.last k')).1 * Xe q (bx (Fin.last k')).1) := by
            rw [Xe_add hx0, two_mul, Xe_add hx0]
        _ ≤ (∏ i, (rt i : ℝ)) * ((rt (Fin.last k') : ℝ) * rt (Fin.last k')) := by
            have h0 := Xe_pos hx0 (bx (Fin.last k')).1
            apply mul_le_mul hplo (mul_le_mul hlast hlast h0.le (by positivity)) (by positivity) (by positivity)
    have h2 : (N2 q : ℝ) < (((∏ i, rt i) * (rt (Fin.last k') * rt (Fin.last k')) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · -- the cofactor's lower end
    refine Xe_maxN_le ?_ ((hc (Fin.last k')).1.trans (by exact_mod_cast hy))
    have hlo' : (N1 q : ℝ) < (∏ i, (rt i : ℝ)) * y := by
      rw [← hcast]
      exact_mod_cast hlo
    have hsplit : Xe q (DEN - 1) = Xe q (DEN - ∑ i, (bx i).2 - 1) * Xe q (∑ i, (bx i).2) := by
      rw [← Xe_add hx0]
      congr 1
      omega
    have hpos := Xe_pos hx0 (∑ i, (bx i).2)
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (∏ i, (rt i : ℝ)) * y ≤ Xe q (∑ i, (bx i).2) * Xe q (DEN - ∑ i, (bx i).2 - 1) := by
      apply mul_le_mul hphi hcon.le (Nat.cast_nonneg _) hpos.le
    have h2 : (N1 q : ℝ) < Xe q (DEN - 1) := by
      rw [hsplit, mul_comm]
      linarith
    linarith
  · -- the cofactor's upper end
    have hhi' : (∏ i, (rt i : ℝ)) * y ≤ N2 q := by
      rw [← hcast]
      exact_mod_cast hhi
    have hsplit : Xe q (DEN + 1) = Xe q (DEN - ∑ i, (bx i).1 + 1) * Xe q (∑ i, (bx i).1) := by
      rw [← Xe_add hx0]
      congr 1
      omega
    have hpos := Xe_pos hx0 (∑ i, (bx i).1)
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Xe q (DEN - ∑ i, (bx i).1 + 1) * Xe q (∑ i, (bx i).1) ≤ (y : ℝ) * ∏ i, (rt i : ℝ) := by
      apply mul_le_mul hcon.le hplo hpos.le (Nat.cast_nonneg _)
    rw [← hsplit] at h1
    linarith

variable [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 4000000 in
/-- **A box evaluated by the resonant window with its cofactor in the rest, under more atoms.** If `chkIRC` passes
the box with the rest `sr`, the term of the box is evaluated under `m` more atoms, uniformly in the atoms, when the
box's atoms and those are at most `40`: by `chain_res_cof` with the cofactor's cell when the bit after the box's
cells is set, and by `evI_resE` otherwise. -/
theorem evI_resCE (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRC bl sr kk hh = true) {m : ℕ} (hm : 3 * min (k' + 1) 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E →
        |dIP q a (boxFn bl (k' + 1) h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  unfold chkIRC at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩ := hok
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr bl.length) 1) 1 = true
  swap
  · -- no cofactor: `chkIR`
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hok' : chkIR bl sr kk hh = true := by
      unfold chkIR
      rw [rpass_eq]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩
    exact evI_resE bl k' h sr kk hh hok' hm
  rw [hbit, Bool.cond_true] at hcof
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcof
  obtain ⟨⟨hshi, hslo⟩, hT⟩ := hcof
  have hc := (cellsFrom_iff 1 bl).1 hcells
  set bx := boxFn bl (k' + 1) h with hbx
  have hbxc : ∀ i, 1 ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl _ h i)
  -- the box's sums and its least prime
  have hlos : loSum bl = ∑ i, (bx i).1 := by rw [loSum_eq, hbx, sum_boxFn (fun c => c.1) bl _ h]
  have hhis : hiSum bl = ∑ i, (bx i).2 := by rw [hiSum_eq, hbx, sum_boxFn (fun c => c.2) bl _ h]
  have hhead : headLo bl = (bx (Fin.last k')).1 := headLo_eq bl k' h
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hT hshi hslo
  rw [hlos] at hT hslo
  rw [hhis] at hT hshi
  rw [hhead] at hT hslo
  -- the rest's cells and positions
  have hcsr : mList (fun c => c.1) bl sr = (ridx (k' + 1) sr).map fun i => (bx i).1 :=
    mList_eq (fun c => c.1) bl (k' + 1) h sr
  obtain ⟨n, hn⟩ : ∃ n, (mList (fun c => c.1) bl sr).length = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hns).symm⟩
  have hlenr : (ridx (k' + 1) sr).length = n + 1 := by rw [← hn, hcsr, List.length_map]
  obtain ⟨r, hrdef⟩ : ∃ r : Fin (n + 1) → Fin (k' + 1),
      r = fun j : Fin (n + 1) => (ridx (k' + 1) sr)[(j : ℕ)]'(by rw [hlenr]; exact j.2) := ⟨_, rfl⟩
  have hr : Function.Injective r := by
    intro i j hij
    rw [hrdef] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff (ridx_nodup _ _)).1 hij)
  have himg : Finset.univ.image r = mset (k' + 1) sr := by
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
  set cl := maxN (DEN - ∑ i, (bx i).2 - 1) (bx (Fin.last k')).1 with hcl
  set cs := mList (fun c => c.1) bl sr ++ [cl] with hcs
  set hs := mSum (fun c => c.2) bl sr + (DEN - ∑ i, (bx i).1 + 1) with hhs
  have hcsn : cs.length = n + 1 + 1 := by rw [hcs, List.length_append, hn]; rfl
  have hcsj : ∀ j : Fin (n + 1), cs.getD j 0 = (bx (r j)).1 := by
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
      exact (hbxc i).1
    · rw [hcl]
      rcases maxN_cases (DEN - ∑ i, (bx i).2 - 1) (bx (Fin.last k')).1 with h' | h'
      · rw [h']
        omega
      · rw [h']
        exact (hbxc _).1
  -- the exponent
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hLeq : (Lnum : ℝ) / Lden = L := IBFits.L_eq
  have hLd : 0 < Lden := by exact_mod_cast hden
  -- the condition on the rest's cells
  have hres := SieveResTest.resT_sound_cells hLd hc1 hT
  have hhs1 : hs + 1 < DEN := by
    have := SieveResTest.resT_hs hT
    simpa [SieveResTest.DEN, SieveCert.DEN] using this
  have hDD : (SieveResTest.DEN : ℝ) = (DEN : ℝ) := by norm_num [SieveResTest.DEN, SieveCert.DEN]
  rw [hLeq, hDD, ← hκdef, hcsn] at hres
  have hres' : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1 + 1) (L - κ * (hs : ℝ) - κ)
      (fun j => κ * (cs.getD j 0 : ℝ) - κ) := hres
  have hLρ : 0 < L - κ * (hs : ℝ) - κ := by
    have h1 : ((hs : ℕ) : ℝ) + 1 < DEN := by exact_mod_cast hhs1
    have h2 : κ * (((hs : ℕ) : ℝ) + 1) < κ * DEN := mul_lt_mul_of_pos_left h1 hκ
    have h3 : κ * DEN = L := by rw [hκdef]; field_simp
    linarith
  have hslo' : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).1 = mSum (fun c => c.1) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.1) bl _ h m]
  have hshi' : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).2 = mSum (fun c => c.2) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.2) bl _ h m]
  have hqx : ∀ (q : ℕ) (e : ℕ), (q : ℝ) ^ (κ * (e : ℝ)) = Xe q e := fun q e => by rw [hκdef, qpow_eq]; rfl
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIHM.chain_res_cof SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half
    SieveCurveHx.counts_hx (e₀ := κ * ((1 : ℕ) : ℝ)) (by positivity) k' 40 (Λ₁ := L + 1) (by linarith)
    (ρ₂ := κ * (hs : ℝ)) (ε := κ) (by positivity) hκ hLρ
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ hη, big_ev] with q hq hq2 hX hbig a ha E
    hEl hEt
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hx0 : 0 < xq q := by linarith
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx ++ E) :=
    thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
  have hmain := hq₀ q hq a ha n r hr (fun j => κ * (cs.getD j 0 : ℝ)) hres'
    ((specB q bx ++ E).map Atom.toG) (κ * ((mSum (fun c => c.1) bl sr + cl : ℕ) : ℝ))
    (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
        fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
      have hcc' : ∀ i, (q : ℝ) ^ (κ * ((bx i).1 : ℝ)) ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ (κ * ((bx i).2 : ℝ)) :=
        fun i => by
          rw [hκdef, qpow_eq, qpow_eq]
          exact ⟨(hcc i).1, (hcc i).2.le⟩
      have hcx : ∀ i, Xe q (bx i).1 ≤ rt i ∧ (rt i : ℝ) < Xe q (bx i).2 := fun i => hcc i
      obtain ⟨hf0, hf2, hf1⟩ := cof_facts hbig bx rt hcx (fun i => (hbxc i).2.1) hshi hslo
      have br := prod_set_bounds hq0 κ bx hcc' (mset (k' + 1) sr)
      rw [hslo' sr, hshi' sr] at br
      rw [himg]
      refine ⟨hsa, fun i => ?_, fun j => ?_, hf0, hf2, fun y hy hylo hyhi => ?_⟩
      · rw [hκdef, qpow_eq]
        exact (pow_mono hx1 (hbxc i).1).trans (hcc i).1
      · show (q : ℝ) ^ (κ * (cs.getD (j : ℕ) 0 : ℝ)) ≤ rt (r j)
        rw [hcsj j]
        exact (hcc' (r j)).1
      · obtain ⟨hyc, hyC⟩ := hf1 y hy hylo hyhi
        have hylo' : (q : ℝ) ^ (κ * (cs.getD (n + 1) 0 : ℝ)) ≤ y := by
          rw [hcsl, hqx]
          exact hyc
        refine ⟨hylo', ?_, ?_⟩
        · -- the rest's product from below
          have h1 := br.1
          rw [Nat.cast_mul]
          calc (q : ℝ) ^ (κ * ((mSum (fun c => c.1) bl sr + cl : ℕ) : ℝ))
              = (q : ℝ) ^ (κ * ((mSum (fun c => c.1) bl sr : ℕ) : ℝ)) * (q : ℝ) ^ (κ * (cl : ℝ)) := by
                rw [← Real.rpow_add hq0]
                congr 1
                push_cast
                ring
            _ ≤ ((∏ i ∈ mset (k' + 1) sr, rt i : ℕ) : ℝ) * y := by
                rw [hqx q cl]
                exact mul_le_mul h1 hyc (Xe_pos hx0 _).le (Nat.cast_nonneg _)
        · -- the rest's product from above
          have h2 := br.2
          rw [Nat.cast_mul]
          calc ((∏ i ∈ mset (k' + 1) sr, rt i : ℕ) : ℝ) * y
              ≤ (q : ℝ) ^ (κ * ((mSum (fun c => c.2) bl sr : ℕ) : ℝ)) * Xe q (DEN - ∑ i, (bx i).1 + 1) :=
                mul_le_mul h2 hyC (Nat.cast_nonneg _) (by positivity)
            _ = (q : ℝ) ^ (κ * (hs : ℝ)) := by
                rw [← hqx q (DEN - ∑ i, (bx i).1 + 1), ← Real.rpow_add hq0, hhs]
                congr 1
                push_cast
                ring)
  rw [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at hmain
  rw [dIP_eq_famSet]
  exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)

/-- **A box evaluated by the resonant window with its cofactor.** If `chkIRC` passes the box, its term is
evaluated. -/
theorem evI_resC (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRC bl sr kk hh = true) : EvI (boxFn bl (k' + 1) h) := by
  intro η hη
  filter_upwards [evI_resCE bl k' h sr kk hh hok (m := 0) (by omega) η hη] with q hq a ha
  have h' := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dIP_nil] at h'

/-- **The tests with the resonant window and the cofactor are sound.** -/
theorem resTestsFC_sound : (resTestsFC).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => ?_⟩
  · change cond (Nat.beq cfg.kind 3) (okIRC bl cfg) (fillTestsF.okI bl cfg) = true at hok
    by_cases h3 : cfg.kind = 3
    · rw [show Nat.beq cfg.kind 3 = true from Nat.beq_eq_true_eq _ _ ▸ h3, Bool.cond_true] at hok
      exact evI_resC bl k' h _ _ _ hok
    · rw [show Nat.beq cfg.kind 3 = false from Bool.eq_false_iff.mpr fun h' => h3 (Nat.eq_of_beq_eq_true h'),
        Bool.cond_false, fillTestsF_eq] at hok
      exact fillTests_sound.soundI bl cfg k' h hok
  · change fillTestsF.okJ bl f cfg = true at hok
    rw [fillTestsF_eq] at hok
    exact fillTests_sound.soundJ bl f cfg k h hok

end SieveAd

#print axioms SieveAd.resTestsFC_sound
