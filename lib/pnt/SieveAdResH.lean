/-
# The resonant window's tests with the lines named by the hint are sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveAdResHDefs.lean` has the resonant window's tests and the search with `SieveResTest.resXH`, which reads each
interval's lines from the hint (`SieveResTestHDefs.lean`). The proofs that the tests with `resX` are sound use of it
only `SieveResTest.resX_sound_cells` and `SieveResTest.resX_hs`, and `SieveResTestH.lean` has the same two facts for
`resXH`; so these are those proofs (`SieveAdRes.lean`, `SieveAdFrozRes.lean`, `SieveAdResCof.lean`,
`SieveAdFrozResCof.lean`, `SieveAdFrozResTree.lean`) with the tests' names ending in `H`:

* `evI_resEH`, `evI_resCEH`, `evI_resCH`, `resTestsFCH_sound`: a box of the main tree that the test passes is
  evaluated, with its cofactor in the rest or not; **the main tree's tests are sound**.
* `evIF_froz_resTH`, `evIF_froz_resTCH`: the same for a box `ch ++ β` of a tree over a frozen part.
* `rules_frozResCH`, `bd_flipCostDRH`, `altFDRH_sound`, `solveMDRH_sound`, `pr_of_partDRH`, `pr_of_partDRH_at`:
  **the search with the hinted bound `altFDRH` is sound**, as `pr_of_partDR_at`; `pr_of_partDRCH_at`, with the tests
  `resTestsFCH` and the configurations `cfgIMRCH`, `cfgJM`: what a certificate's parts use.

The file imports `SieveAdFrozResTree.lean`, `SieveAdResHDefs.lean` and `SieveResTestH.lean`.
-/
import SieveAdFrozResTree
import SieveAdResHDefs
import SieveResTestH

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos' K cdiv omKw topK w1K LD)

section

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 4000000 in
/-- **A box evaluated by the resonant window, under more atoms.** If `chkIRH` passes the box with the rest `sr`, the
term of the box is evaluated under `m` more atoms, uniformly in the atoms, when the box's atoms and those are at
most `40`: the variable is the product of the box's other primes and the cofactor, the rest the primes of `sr`. -/
theorem evI_resEH (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRH bl sr kk hh = true) {m : ℕ} (hm : 3 * min (k' + 1) 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E →
        |dIP q a (boxFn bl (k' + 1) h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  unfold chkIRH at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨_, hcells⟩, hns⟩, hT⟩ := hok
  have hc := (cellsFrom_iff 1 bl).1 hcells
  set bx := boxFn bl (k' + 1) h with hbx
  have hbxc : ∀ i, 1 ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl _ h i)
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
  have hcsj : ∀ j : Fin (n + 1), (mList (fun c => c.1) bl sr).getD j 0 = (bx (r j)).1 := by
    intro j
    rw [List.getD_eq_getElem _ _ (by rw [hn]; exact j.2)]
    simp only [hcsr, List.getElem_map, hrdef]
  have hc1 : ∀ c ∈ mList (fun c => c.1) bl sr, 1 ≤ c := by
    intro c hcm
    rw [hcsr, List.mem_map] at hcm
    obtain ⟨i, -, rfl⟩ := hcm
    exact (hbxc i).1
  -- the exponent
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hκD : κ * DEN = L := by rw [hκdef]; field_simp
  have hLeq : (Lnum : ℝ) / Lden = L := IBFits.L_eq
  have hLd : 0 < Lden := by exact_mod_cast hden
  -- the condition on the rest's cells
  have hres := SieveResTest.resXH_sound_cells hLd hc1 hT
  have hhs : mSum (fun c => c.2) bl sr + 1 < DEN := by
    have := SieveResTest.resXH_hs hT
    simpa [SieveResTest.DEN, SieveCert.DEN] using this
  have hDD : (SieveResTest.DEN : ℝ) = (DEN : ℝ) := by norm_num [SieveResTest.DEN, SieveCert.DEN]
  rw [hLeq, hDD, ← hκdef, hn] at hres
  have hres' : SieveTypeIIHM.ResBox SieveCurveHx.ghx L (n + 1) (L - κ * (mSum (fun c => c.2) bl sr : ℝ) - κ)
      (fun j => κ * ((mList (fun c => c.1) bl sr).getD j 0 : ℝ) - κ) := hres
  have hLρ : 0 < L - κ * (mSum (fun c => c.2) bl sr : ℝ) - κ := by
    have h1 : ((mSum (fun c => c.2) bl sr : ℕ) : ℝ) + 1 < DEN := by exact_mod_cast hhs
    have h2 : κ * (((mSum (fun c => c.2) bl sr : ℕ) : ℝ) + 1) < κ * DEN := mul_lt_mul_of_pos_left h1 hκ
    linarith
  have hslo : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).1 = mSum (fun c => c.1) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.1) bl _ h m]
  have hshi : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).2 = mSum (fun c => c.2) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.2) bl _ h m]
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIHM.chain_res_exp SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half
    SieveCurveHx.counts_hx (e₀ := κ * ((1 : ℕ) : ℝ)) (by positivity) k' 40 (Λ₁ := L + 1) (by linarith)
    (ρ₂ := κ * (mSum (fun c => c.2) bl sr : ℝ)) (ε := κ) (by positivity) hκ hLρ
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ hη] with q hq hq2 hX a ha E hEl hEt
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx ++ E) :=
    thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
  have hmain := hq₀ q hq a ha n r hr (fun j => κ * ((mList (fun c => c.1) bl sr).getD j 0 : ℝ)) hres'
    ((specB q bx ++ E).map Atom.toG) (κ * (mSum (fun c => c.1) bl sr : ℝ))
    (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
        fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
      have hcc' : ∀ i, (q : ℝ) ^ (κ * ((bx i).1 : ℝ)) ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ (κ * ((bx i).2 : ℝ)) :=
        fun i => by
          rw [hκdef, qpow_eq, qpow_eq]
          exact ⟨(hcc i).1, (hcc i).2.le⟩
      have br := prod_set_bounds hq0 κ bx hcc' (mset (k' + 1) sr)
      rw [hslo sr, hshi sr] at br
      rw [himg]
      refine ⟨hsa, fun i => ?_, fun j => ?_, br.1, br.2⟩
      · rw [hκdef, qpow_eq]
        exact (pow_mono hx1 (hbxc i).1).trans (hcc i).1
      · show (q : ℝ) ^ (κ * ((mList (fun c => c.1) bl sr).getD (j : ℕ) 0 : ℝ)) ≤ rt (r j)
        rw [hcsj j]
        exact (hcc' (r j)).1)
  rw [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at hmain
  rw [dIP_eq_famSet]
  exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)

set_option maxHeartbeats 1600000 in
/-- **The term of a chain's box over the frozen part, when the resonant window's test passes the box `ch ++ β`.** For
`e₁, e₂ ≤ DEN`: if `chkIRH` passes the box `ch ++ β` with the rest `sr` and the hint's intervals, the term of the chain
`ch` over the frozen part `frozS` of `β` and the slab is evaluated. -/
theorem evIF_froz_resTH {e₁ e₂ s : ℕ} (β : List Cell) (hβl : β.length = s + 1) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN)
    (ch : List Cell) (k' : ℕ) (hch : ch.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRH (ch ++ β) sr kk hh = true) :
    EvIF (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβl)) frozR (boxFn ch (k' + 1) hch) := by
  unfold chkIRH at hok
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
  have hres := SieveResTest.resXH_sound_cells hLd hc1 hT
  have hhs : mSum (fun c => c.2) (ch ++ β) sr + 1 < DEN := by
    have := SieveResTest.resXH_hs hT
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

set_option maxHeartbeats 4000000 in
/-- **A box evaluated by the resonant window with its cofactor in the rest, under more atoms.** If `chkIRCH` passes
the box with the rest `sr`, the term of the box is evaluated under `m` more atoms, uniformly in the atoms, when the
box's atoms and those are at most `40`: by `chain_res_cof` with the cofactor's cell when the bit after the box's
cells is set, and by `evI_resEH` otherwise. -/
theorem evI_resCEH (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRCH bl sr kk hh = true) {m : ℕ} (hm : 3 * min (k' + 1) 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E →
        |dIP q a (boxFn bl (k' + 1) h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  unfold chkIRCH at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩ := hok
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr bl.length) 1) 1 = true
  swap
  · -- no cofactor: `chkIRH`
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hok' : chkIRH bl sr kk hh = true := by
      unfold chkIRH
      rw [rpass_eq]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩
    exact evI_resEH bl k' h sr kk hh hok' hm
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
  have hres := SieveResTest.resXH_sound_cells hLd hc1 hT
  have hhs1 : hs + 1 < DEN := by
    have := SieveResTest.resXH_hs hT
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

/-- **A box evaluated by the resonant window with its cofactor.** If `chkIRCH` passes the box, its term is
evaluated. -/
theorem evI_resCH (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRCH bl sr kk hh = true) : EvI (boxFn bl (k' + 1) h) := by
  intro η hη
  filter_upwards [evI_resCEH bl k' h sr kk hh hok (m := 0) (by omega) η hη] with q hq a ha
  have h' := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dIP_nil] at h'

/-- **The tests with the resonant window, its lines named by the hint, and the cofactor are sound.** -/
theorem resTestsFCH_sound : (resTestsFCH).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => ?_⟩
  · change cond (Nat.beq cfg.kind 3) (okIRCH bl cfg) (fillTestsF.okI bl cfg) = true at hok
    by_cases h3 : cfg.kind = 3
    · rw [show Nat.beq cfg.kind 3 = true from Nat.beq_eq_true_eq _ _ ▸ h3, Bool.cond_true] at hok
      exact evI_resCH bl k' h _ _ _ hok
    · rw [show Nat.beq cfg.kind 3 = false from Bool.eq_false_iff.mpr fun h' => h3 (Nat.eq_of_beq_eq_true h'),
        Bool.cond_false, fillTestsF_eq] at hok
      exact fillTests_sound.soundI bl cfg k' h hok
  · change fillTestsF.okJ bl f cfg = true at hok
    rw [fillTestsF_eq] at hok
    exact fillTests_sound.soundJ bl f cfg k h hok

set_option maxHeartbeats 4000000 in
/-- **The term of a chain's box over the frozen part, when the resonant window's test with the chain's cofactor passes
the box `ch ++ β`.** For `e₁, e₂ ≤ DEN`: if `chkIRFH` passes the box `ch ++ β` with the rest `sr` and the hint's
intervals, the term of the chain `ch` over the frozen part `frozS` of `β` and the slab is evaluated: by `evIF_froz_resC`
with the cofactor's cell when the bit after the box's cells is set, by `evIF_froz_resTH` otherwise. -/
theorem evIF_froz_resTCH {e₁ e₂ s : ℕ} (β : List Cell) (hβl : β.length = s + 1) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN)
    (ch : List Cell) (k' : ℕ) (hch : ch.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIRFH e₁ e₂ β (ch ++ β) sr kk hh = true) :
    EvIF (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβl)) frozR (boxFn ch (k' + 1) hch) := by
  unfold chkIRFH at hok
  beta_reduce at hok
  rw [rpass_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩ := hok
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr (ch ++ β).length) 1) 1 = true
  swap
  · -- no cofactor: `chkIRH`
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hok' : chkIRH (ch ++ β) sr kk hh = true := by
      unfold chkIRH
      rw [rpass_eq]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨⟨⟨h13, hcells⟩, hns⟩, hcof⟩
    exact evIF_froz_resTH β hβl he₁ he₂ ch k' hch sr kk hh hok'
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
  have hres := SieveResTest.resXH_sound_cells hLd hc1 hT
  have hhs1 : hs + 1 < DEN := by
    have := SieveResTest.resXH_hs hT
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

/-- **The nodes of a tree over a frozen part, with the resonant window**: those of `rules_frozC`, and an evaluation
of kind `3` (`okIRFH` on the box `ch ++ β`) evaluates the term of the chain `ch` over the frozen part
(`evIF_froz_resTCH`), for a slab whose ends are at most `DEN` and are the tests' `e₁, e₂`. -/
theorem rules_frozResCH {O : Ops} {e₁ e₂ Kb : ℕ} {β : List Cell} {s : ℕ} (hβl : β.length = s + 1)
    {e₁' e₂' : ℕ} (he₁ : e₁' ≤ DEN) (he₂ : e₂' ≤ DEN) (hee₁ : e₁ = e₁') (hee₂ : e₂ = e₂')
    (hβ : cellsFrom 1 β = true)
    (h : Rules O (frozTests e₁ e₂ Kb β) (PF (fun q => frozS q e₁' e₂' (boxFn β (s + 1) hβl)) frozR β)) :
    Rules O (frozResTestsCH e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN))
      (PF (fun q => frozS q e₁' e₂' (boxFn β (s + 1) hβl)) frozR β) where
  van := h.van
  evl := by
    intro bl par cfg hg hI
    change cond (Nat.beq cfg.kind 3) (okIRFH e₁ e₂ β bl cfg)
      ((frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okI bl cfg) = true at hI
    by_cases h3 : cfg.kind = 3
    · rw [show Nat.beq cfg.kind 3 = true from Nat.beq_eq_true_eq _ _ ▸ h3, Bool.cond_true] at hI
      intro ch hbl k' hch ε hε
      subst hbl hee₁ hee₂
      have hev := evIF_froz_resTCH β hβl he₁ he₂ ch k' hch cfg.sr _ _ hI
      refine bdF_mono (bdF_eval hev) ?_
      simp only [Nat.cast_zero, zero_div, zero_add]
      exact hε.le
    · rw [show Nat.beq cfg.kind 3 = false from Bool.eq_false_iff.mpr fun h' => h3 (Nat.eq_of_beq_eq_true h'),
        Bool.cond_false] at hI
      exact (rules_frozC hβ h).evl hg hI
  drp := h.drp
  alt := h.alt
  split := h.split
  buch := (rules_frozC hβ h).buch

/-- **The cost of a reversal through the largest prime, its tree searched by hints with the resonant window,
bounds the term**, for a box of the sign `−` (`pos = false`) or `+`: `bd_flipCostD` for `flipCostDRH`. -/
theorem bd_flipCostDRH (κ hR fuel maxlen : ℕ) (pos : Bool) {bl : List Cell} {lim h : ℕ}
    (hlt : (flipCostDRH κ hR fuel maxlen pos bl lim h).1 < lim) (k' : ℕ) (hl : bl.length = k' + 1) :
    Bd pos (((flipCostDRH κ hR fuel maxlen pos bl lim h).1 : ℝ) / K) (boxFn bl (k' + 1) hl) := by
  unfold flipCostDRH at hlt ⊢
  rw [lastP_eq, initP_eq] at hlt ⊢
  revert hlt
  cases hβ : initC bl with
  | nil => exact fun hlt => absurd hlt (lt_irrefl _)
  | cons c0 b =>
    intro hlt
    simp only [] at hlt ⊢
    rw [tailP_eq] at hlt ⊢
    simp only [Nat.zero_add, Nat.one_mul] at hlt ⊢
    unfold flipCostBRH at hlt ⊢
    by_cases hok' : flipOKP maxlen (lastC bl) c0 (hiSum b) (cellI c0 * okProd b) b.length (lastHiP c0.2 b) = true
    swap
    · rw [Bool.not_eq_true] at hok'
      rw [hok', Bool.cond_false] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [hok', Bool.cond_true] at hlt ⊢
    have hok := flipOK_of_P hβ hok'
    have hne : bl ≠ [] := by
      intro h0
      rw [h0] at hβ
      simp [initC] at hβ
    have hbl : (c0 :: b) ++ [lastC bl] = bl := by
      rw [← hβ]
      exact initC_append_lastC hne
    simp only [dropL_eq, bdKP_eq] at hlt ⊢
    rw [hbl] at hlt ⊢
    obtain ⟨r, hrdef⟩ : ∃ r, r = flipTreeDRH κ hR fuel pos (lastC bl) c0 b (Nat.add c0.1 (loSum b))
        (Nat.add c0.2 (hiSum b)) (Nat.succ b.length) CAPK h := ⟨_, rfl⟩
    rw [← hrdef] at hlt ⊢
    by_cases hcap : Nat.ble CAPK r.1 = true
    · rw [hcap, Bool.cond_true] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [Bool.not_eq_true] at hcap
    rw [hcap, Bool.cond_false] at hlt ⊢
    have hccap : r.1 < CAPK := by
      by_contra hge
      rw [Nat.ble_eq_true_of_le (not_lt.1 hge)] at hcap
      exact Bool.noConfusion hcap
    -- the cells of the frozen primes
    have hcf : cellsFrom 1 (c0 :: b) = true := by
      have hok2 := hok
      simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcells⟩, hfit⟩, _⟩, _⟩, _⟩, _⟩ := hok2
      have h1 : cellsOK ((c0 :: b) ++ [lastC bl]) = true := by
        rw [hbl]
        exact hcells
      have h2 : hiSum ((c0 :: b) ++ [lastC bl]) ≤ DEN := by
        rw [hbl]
        omega
      exact cellsFrom_one_init (c0 :: b) h1 h2
    -- the ends of the slab are at most `DEN`
    have hctx : 3 ≤ (lastC bl).1 ∧ (lastC bl).1 < (lastC bl).2 := by
      have hok2 := hok
      simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcells⟩, _⟩, _⟩, h3⟩, _⟩, _⟩ := hok2
      have hmem : lastC bl ∈ bl := by
        have h := List.mem_append_right (c0 :: b) (List.mem_singleton_self (lastC bl))
        rwa [hbl] at h
      exact ⟨h3, ((cellsOK_iff bl).1 hcells _ hmem).2⟩
    have hDEN : 1 ≤ DEN := SieveCert.DEN_pos
    have he₁' : cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)) ≤ DEN := by
      have h1 : e1 (lastC bl) + 1 ≤ DEN := by
        unfold e1
        omega
      cases pos
      · exact (Nat.le_succ _).trans h1
      · exact h1
    have he₂' : cond pos (e2 (lastC bl) - 1) (e2 (lastC bl)) ≤ DEN := by
      have h1 : e2 (lastC bl) ≤ DEN := by
        unfold e2
        omega
      cases pos
      · exact h1
      · exact (Nat.sub_le _ _).trans h1
    -- the tree over the frozen part
    unfold flipTreeDRH at hrdef
    simp only [] at hrdef
    generalize hpdef : cfgJF (Nat.add 12 (Nat.div DEN c0.1))
      (maxN 1 (Nat.sub (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
        (Nat.add c0.2 (hiSum b))))
      (Nat.sub (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
        (Nat.add c0.1 (loSum b))) (c0 :: b) (Nat.succ b.length)
      (lomP (c0 :: b) DEN) (c0 :: b) h = p at hrdef
    by_cases hc : (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c0.1 (flipT (lastC bl))) &&
        (frozResTestsCH (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
          (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN)).okJ (c0 :: b) p.1.1 p.1.2) = true
    swap
    · rw [Bool.not_eq_true] at hc
      rw [hc, Bool.cond_false] at hrdef
      rw [hrdef] at hccap
      exact absurd hccap (lt_irrefl _)
    rw [hc, Bool.cond_true] at hrdef
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    have hokJ : (frozTests (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
        (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b)
        p.1.1 p.1.2 = true :=
      frozTestsC_okJ (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
        (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b) [] p.1.1 p.1.2 hcf
        hc.2
    refine bd_flip_coreB pos hok k' hl hβ.symm hc.1.2 hokJ fun s hβl hR' => ?_
    have hR'' : Rules (opsKP (lastC bl) (Nat.succ b.length))
        (frozResTestsCH (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
          (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN))
        (PF (fun q => frozS q (cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)))
          (cond pos (e2 (lastC bl) - 1) (e2 (lastC bl))) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) := by
      rw [opsKP_eq]
      refine rules_frozResCH hβl he₁' he₂' ?_ ?_ hcf hR'
      · cases pos <;> rfl
      · cases pos
        · rfl
        · show DEN - (lastC bl).1 = DEN - (lastC bl).1 + 1 - 1
          omega
    have hk := kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length) _
      (solveD_sound hR'' cfgIFRH _ (kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length)) (altH := noAltH)
        (fun _ _ _ _ _ hh => absurd hh (lt_irrefl _)) fuel)
      (flipT (lastC bl)) (c0 :: b) (!pos) p.1.1 CAPK p.2 (by rw [← hrdef]; exact hccap)
    rw [← hrdef] at hk
    exact hk

/-- **The hinted bound with the resonant window over the frozen parts proves `PR`**: a cost that `altFDRH` returns
below its limit bounds the term of the box, of either sign. -/
theorem altFDRH_sound (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hlt : (altFDRH κ hR fuel maxlen bl par l h).1 < l) : PR bl par (altFDRH κ hR fuel maxlen bl par l h).1 := by
  unfold altFDRH at hlt ⊢
  intro k' hl
  exact bd_flipCostDRH κ hR fuel maxlen par hlt k' hl

/-- **The main search led by hints, with the resonant window over the frozen parts, is sound**: `solveMD_sound`
with the hinted bound `altFDRH`. -/
theorem solveMDRH_sound {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) :
    RecPH PR (solveD opsMP τ dI dJ (kidsM κ hI) (altFDRH κ hR fuel maxlen) n) :=
  solveD_sound (rulesMP hτ) dI dJ (kidsM_sound pr_split κ hI)
    (fun bl par l h _ hlt => altFDRH_sound κ hR fuel maxlen bl par l h hlt) n

/-- **A part of the main search, with the resonant window over the frozen parts**, as the kernel checks it:
`pr_of_partD` with the hinted bound `altFDRH`. -/
theorem pr_of_partDRH {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool}
    {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (altFDRH κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_mono (partD_sound pr_split (solveMDRH_sound hτ dI dJ κ hI hR fuel maxlen n) top bl par cs a K h
    (lt_of_le_of_lt hk hc)) hk

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the main search with the resonant window over the frozen parts, for any route**: `pr_of_partDRH`
with the route and its exponent as variables. -/
theorem pr_of_partDRH_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (@altFDRH Pr κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  @pr_of_partDRH Rt hRt Pr hPr τ hτ dI dJ κ hI hR fuel maxlen n top bl par cs a c h hk hc

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the search with the window's lines named by the hint bounds its term**, for any route:
`pr_of_partDRH_at` with the tests `resTestsFCH` (`resTestsFCH_sound`) and the configurations read by `cfgIMRCH` and
`cfgJM`, the search of a certificate written with them (`tools/linnik/hint_cert.py --hl`). -/
theorem pr_of_partDRCH_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP (@resTestsFCH Pr) cfgIMRCH (@cfgJM Pr) (kidsM κ hI) (@altFDRH Pr κ hR fuel maxlen) n)
      top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  pr_of_partDRH_at Rt hRt Pr hPr (@resTestsFCH_sound Rt hRt Pr hPr) cfgIMRCH (@cfgJM Pr) κ hI hR fuel maxlen n hk hc

end

end SieveAd

#print axioms SieveAd.pr_of_partDRH_at
#print axioms SieveAd.pr_of_partDRCH_at
#print axioms SieveAd.resTestsFCH_sound
