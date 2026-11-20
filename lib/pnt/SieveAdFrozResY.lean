/-
# The window's test at the two corners of a box, over the frozen part, is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdResYDefs.lean`'s `chkIRFY` tests the box `ch ++ β` of a tree over a frozen part by
`SieveResTest.resYH` on the cells of a rest of its primes, and of the chain's cofactor, one part whatever its
number of primes. The test gives the estimate of the tuples with the rest in its cells (`fullEst_of_resYH`,
`fullEst_of_resYHS`), and that the term of the chain's box over the frozen part (`evIF_froz_gen`,
`evIF_froz_genC`).

* `evIF_froz_resTY`: **the term of a chain's box over the frozen part is evaluated when `chkIRFY` passes the box
  `ch ++ β`**: by `evIF_froz_genC` with the cofactor's cell when the bit after the box's cells is set, by
  `evIF_froz_gen` otherwise.

The file imports `SieveAdResY.lean`, `SieveAdFrozResG.lean` and `SieveAdFrozResCofG.lean`.
-/
import SieveAdResY
import SieveAdFrozResG
import SieveAdFrozResCofG

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 4000000 in
/-- **The term of a chain's box over the frozen part, when the window's test at the two corners passes the box
`ch ++ β`.** For `e₁, e₂ ≤ DEN`: if `chkIRFY` passes the box `ch ++ β` with the rest `sr` and the hints, the term of
the chain `ch` over the frozen part `frozS` of `β` and the slab is evaluated: by `evIF_froz_genC` with the
cofactor's cell when the bit after the box's cells is set, by `evIF_froz_gen` otherwise. -/
theorem evIF_froz_resTY {e₁ e₂ s : ℕ} (β : List Cell) (hβl : β.length = s + 1) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN)
    (ch : List Cell) (k' : ℕ) (hch : ch.length = k' + 1) (sr sY : ℕ)
    (hok : chkIRFY e₁ e₂ β (ch ++ β) sr sY = true) :
    EvIF (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβl)) frozR (boxFn ch (k' + 1) hch) := by
  unfold chkIRFY at hok
  beta_reduce at hok
  rw [rpassY_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, SieveResTest.resYHF_eq] at hok
  obtain ⟨⟨⟨_, hcells⟩, hns⟩, hcof⟩ := hok
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
  have hcsr : mCells (ch ++ β) sr = (ridx (s + 1 + (k' + 1)) sr).map fun i => cx i :=
    mCells_eq (ch ++ β) (s + 1 + (k' + 1)) hlen sr
  obtain ⟨n, hn⟩ : ∃ n, (mCells (ch ++ β) sr).length = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hns).symm⟩
  have hlenr : (ridx (s + 1 + (k' + 1)) sr).length = n + 1 := by rw [← hn, hcsr, List.length_map]
  obtain ⟨r, hrdef⟩ : ∃ r : Fin (n + 1) → Fin (s + 1 + (k' + 1)),
      r = fun j : Fin (n + 1) => (ridx (s + 1 + (k' + 1)) sr)[(j : ℕ)]'(by rw [hlenr]; exact j.2) := ⟨_, rfl⟩
  have hr : Function.Injective r := by
    intro i j hij
    rw [hrdef] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff (ridx_nodup _ _)).1 hij)
  have hcsj : ∀ j : Fin (n + 1), (mCells (ch ++ β) sr)[(j : ℕ)]'(by rw [hn]; exact j.2) = cx (r j) := by
    intro j
    simp only [hcsr, List.getElem_map, hrdef]
  -- the exponent
  have hD := DEN_pos'
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos L_pos (by exact_mod_cast hD)
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr (ch ++ β).length) 1) 1 = true
  swap
  · -- no cofactor: the estimate on the rest's cells
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hfull := fullEst_of_resYH hn hcof hκdef hκ
    refine evIF_froz_gen hβc he₁ he₂ hbc hκdef r hr
      (fun j => κ * (((mCells (ch ++ β) sr).getD j (0, 0)).1 : ℝ))
      (fun j => κ * (((mCells (ch ++ β) sr).getD j (0, 0)).2 : ℝ)) (fun j => ?_) (fun j => ?_) hfull
    · show κ * (((mCells (ch ++ β) sr).getD (j : ℕ) (0, 0)).1 : ℝ) = κ * ((Fin.append βx bx (r j)).1 : ℝ)
      rw [List.getD_eq_getElem _ _ (by rw [hn]; exact j.2), hcsj j, hcxe]
    · show κ * (((mCells (ch ++ β) sr).getD (j : ℕ) (0, 0)).2 : ℝ) = κ * ((Fin.append βx bx (r j)).2 : ℝ)
      rw [List.getD_eq_getElem _ _ (by rw [hn]; exact j.2), hcsj j, hcxe]
  -- the chain's cofactor in the rest, its cell after the box's
  rw [hbit, Bool.cond_true] at hcof
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcof
  obtain ⟨hshi, hT⟩ := hcof
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
  set cl := maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 with hcl
  set cu := DEN - e₁ - ∑ j, (bx j).1 + 1 with hcu
  set cs : List Cell := mCells (ch ++ β) sr ++ [(cl, cu)] with hcs
  have hcsn : cs.length = n + 1 + 1 := by rw [hcs, List.length_append, hn]; rfl
  have hcsj' : ∀ j : Fin (n + 1), cs.getD j (0, 0) = cx (r j) := by
    intro j
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_left (by rw [hn]; exact j.2)]
    exact hcsj j
  have hcsl : cs.getD (n + 1) (0, 0) = (cl, cu) := by
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_right (by rw [hn])]
    simp [hn]
  refine evIF_froz_genC hβc he₁ he₂ hbc hshi hκdef r hr (fun j => κ * ((cs.getD j (0, 0)).1 : ℝ))
    (fun j => κ * ((cs.getD j (0, 0)).2 : ℝ)) (fun j => ?_) (fun j => ?_) ?_ ?_
    fun u hu => fullEst_of_resYHS hcsn hT hκdef hκ u hu
  · show κ * ((cs.getD (j : ℕ) (0, 0)).1 : ℝ) = κ * ((Fin.append βx bx (r j)).1 : ℝ)
    rw [hcsj' j, hcxe]
  · show κ * ((cs.getD (j : ℕ) (0, 0)).2 : ℝ) = κ * ((Fin.append βx bx (r j)).2 : ℝ)
    rw [hcsj' j, hcxe]
  · show κ * ((cs.getD (n + 1) (0, 0)).1 : ℝ) = _
    rw [hcsl]
  · show κ * ((cs.getD (n + 1) (0, 0)).2 : ℝ) = _
    rw [hcsl]

end SieveAd

#print axioms SieveAd.evIF_froz_resTY
