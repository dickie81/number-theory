/-
# The resonant window's test at the two corners of a box, in the main tree, is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The setting is a route with `RouteOK` whose exponent is `Lnum/Lden` (`SieveQ.IBFits`); the test
is `SieveAdResYDefs.lean`'s `chkIRY`: `SieveResTest.resYH` on the cells of a rest of the box's primes, and of the
box's cofactor, one part whatever its number of primes. Write `κ = L/DEN`. The test gives the window's condition on
the box of the rest's cells with the variable tied to the rest (`SieveResTest.resY_sound`), that the estimate of the
tuples with the rest's parts in its cells (`SieveTypeIIHM.fullEst_of_tightG`), and that the box's term
(`SieveTypeIIHM.chain_res_gen`, `chain_res_sifG`).

* `mCells`, `rpassY_eq`, `mCells_eq`: the cells at the set bits of a rest, in the list's order: what `rpassY` gives
  its continuation, and the box's cells at the indices `ridx`.
* `fullEst_of_resYHG`: **the test gives the estimate on the box of the cells, with parts**: `FullEst L e₀ n` for the
  region `q^{κ·lo_p} ≤ ∏_{grp i = p} x_i ≤ q^{κ·hi_p}`. `fullEst_of_resYH`: each prime its own part.
  `fullEst_of_resYHS`: the parts of a chain's rest with a sifted cofactor of `t` primes (`SieveTypeIIHM.sifGrp`).
* `evI_resYE`: **a box evaluated by the test at the two corners, under more atoms**: if `chkIRY` passes the box, its
  term is evaluated, with the cofactor in the rest when its bit is set. `evI_resY`, `resTestsFY_sound`: so the
  tests `resTestsFY` are sound.

The file imports `SieveAdResCof.lean`, `SieveAdResYDefs.lean`, `SieveResCorner.lean` and `SieveResTermG.lean`.
-/
import SieveAdResCof
import SieveAdResYDefs
import SieveResTestF
import SieveResCorner
import SieveResTermG

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-! ### The rest's cells in the list's order -/

/-- The cells at the set bits of `m`, in the list's order. -/
def mCells : List Cell → ℕ → List Cell
  | [], _ => []
  | c :: b, m => if Nat.testBit m 0 then c :: mCells b (m / 2) else mCells b (m / 2)

theorem rpassY_cons {α : Type} (x : Cell) (b : List Cell) (m : ℕ) (k : List Cell → ℕ → Bool → ℕ → α) :
    rpassY (x :: b) m k = rpassY b (Nat.div m 2) fun cs ns ok n =>
      k (cond (Nat.beq (Nat.land m 1) 1) (x :: cs) cs) (Nat.add (Nat.land m 1) ns)
        (ok && Nat.ble 1 x.1 && Nat.ble x.1 x.2 && Nat.ble x.2 DEN) (Nat.succ n) :=
  rfl

/-- **What the pass gives its continuation**: the rest's cells, their number, the cells' check and the length. -/
theorem rpassY_eq {α : Type} : ∀ (bl : List Cell) (m : ℕ) (k : List Cell → ℕ → Bool → ℕ → α),
    rpassY bl m k = k (mCells bl m) (mCells bl m).length (cellsFrom 1 bl) bl.length
  | [], _, _ => rfl
  | x :: b, m, k => by
    rw [rpassY_cons, rpassY_eq b]
    have hbit : Nat.beq (Nat.land m 1) 1 = Nat.testBit m 0 := by
      rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl
    have hland : Nat.land m 1 = if Nat.testBit m 0 then 1 else 0 := by
      rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    have hdiv : Nat.div m 2 = m / 2 := rfl
    rw [hbit, hdiv]
    simp only [mCells, cellsFrom, List.length_cons]
    cases hb : Nat.testBit m 0
    · simp only [hland, hb, Bool.cond_false, ite_false, Bool.false_eq_true, Nat.add_eq, zero_add]
      congr 1
      cases cellsFrom 1 b <;> cases Nat.ble 1 x.1 <;> cases Nat.ble x.1 x.2 <;> cases Nat.ble x.2 DEN <;> rfl
    · simp only [hland, hb, Bool.cond_true, ite_true, Nat.add_eq, List.length_cons]
      congr 1
      · ring
      · cases cellsFrom 1 b <;> cases Nat.ble 1 x.1 <;> cases Nat.ble x.1 x.2 <;> cases Nat.ble x.2 DEN <;> rfl

/-- **`mCells` is the box's cells at its indices**, in the list's order. -/
theorem mCells_eq : ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k) (m : ℕ),
    mCells bl m = (ridx k m).map fun i => boxFn bl k h i
  | [], k, h, m => by
    subst h
    simp [mCells, ridx]
  | x :: b, k, h, m => by
    subst h
    show mCells (x :: b) m = (ridx (b.length + 1) m).map fun i => boxFn (x :: b) (b.length + 1) rfl i
    rw [ridx_succ, boxFn_cons x b b.length rfl, mCells, mCells_eq b b.length rfl (m / 2)]
    cases Nat.testBit m 0
    · simp only [Bool.false_eq_true, ite_false, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp [Function.comp, Fin.snoc_castSucc]
    · simp only [ite_true, List.map_cons, List.map_map, Fin.snoc_last]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp [Function.comp, Fin.snoc_castSucc]

/-! ### The estimate on the box of the rest's cells -/

section

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

/-- **The test at the two corners gives the estimate on the box of the cells, with parts**: if `resYH` passes the
`m + 1` cells, the tuples of `n + 1` primes whose parts (the primes `i` with `grp i = p`, each part nonempty) have
their products in those cells, `q^{κ·lo_p} ≤ ∏_{grp i = p} x_i ≤ q^{κ·hi_p}` with `κ = L/DEN`, are estimated
(`SieveTypeIIHM.FullEst`), by `resY_sound` and `fullEst_of_tightG`. -/
theorem fullEst_of_resYHG {cells : List Cell} {s m : ℕ} (hn : cells.length = m + 1)
    (hT : SieveResTest.resYH Lnum Lden cells s = true) {κ : ℝ} (hκ : κ = L / DEN) {e₀ : ℝ} (he₀ : 0 < e₀)
    {n : ℕ} {grp : ℕ → ℕ} (hgrp : ∀ j < n + 1, grp j < m + 1) (hne : ∀ p < m + 1, ∃ j < n + 1, grp j = p) :
    SieveTypeIIHM.FullEst L e₀ n (fun q x => ∀ p < m + 1,
      (q : ℝ) ^ (κ * ((cells.getD p (0, 0)).1 : ℝ)) ≤
          ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (x i : ℝ) ∧
        ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (x i : ℝ) ≤
          (q : ℝ) ^ (κ * ((cells.getD p (0, 0)).2 : ℝ))) := by
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, -⟩ := lnum_eq
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hLeq : (Lnum : ℝ) / Lden = L := IBFits.L_eq
  have hLd : 0 < Lden := by exact_mod_cast hden
  have hDD : (SieveResTest.DEN : ℝ) = (DEN : ℝ) := by norm_num [SieveResTest.DEN, SieveCert.DEN]
  obtain ⟨kH, hH, kL, hL, e⟩ := SieveResTest.resYH_eq Lnum Lden cells s
  rw [e] at hT
  have hres := SieveResTest.resY_sound hLd hT
  obtain ⟨hord, hroom⟩ := SieveResTest.resY_room hLd hT
  rw [hLeq, hDD, ← hκ, hn] at hres hroom
  refine SieveTypeIIHM.fullEst_of_tightG SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half SieveCurveHx.counts_hx
    hL0 L_le he₀ hgrp hne (lo := fun j => κ * ((cells.getD j (0, 0)).1 : ℝ))
    (hi := fun j => κ * ((cells.getD j (0, 0)).2 : ℝ)) (fun j hj => ⟨by positivity, ?_⟩) ?_ hres
  · have hj' : j < cells.length := by rw [hn]; exact hj
    have h1 : (cells.getD j (0, 0)).1 ≤ (cells.getD j (0, 0)).2 := by
      rw [List.getD_eq_getElem _ _ hj']
      exact hord _ (List.getElem_mem hj')
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 h1) hκ0.le
  · show ∑ j ∈ Finset.range (m + 1), κ * ((cells.getD j (0, 0)).2 : ℝ) + 1 / 10 ^ 5 ≤ L
    linarith

/-- **The test at the two corners gives the estimate on the box of the cells**: if `resYH` passes the `n + 1` cells,
the tuples of primes with a rest in those cells, `q^{κ·lo_i} ≤ x_i ≤ q^{κ·hi_i}` with `κ = L/DEN`, are estimated
(`SieveTypeIIHM.FullEst`): `fullEst_of_resYHG` with each prime its own part. -/
theorem fullEst_of_resYH {cells : List Cell} {s n : ℕ} (hn : cells.length = n + 1)
    (hT : SieveResTest.resYH Lnum Lden cells s = true) {κ : ℝ} (hκ : κ = L / DEN) {e₀ : ℝ} (he₀ : 0 < e₀) :
    SieveTypeIIHM.FullEst L e₀ n (fun q x => ∀ i : Fin (n + 1),
      (q : ℝ) ^ (κ * ((cells.getD i (0, 0)).1 : ℝ)) ≤ x i ∧
        (x i : ℝ) ≤ (q : ℝ) ^ (κ * ((cells.getD i (0, 0)).2 : ℝ))) := by
  refine SieveTypeIIHM.FullEst.mono (fullEst_of_resYHG hn hT hκ he₀ (n := n) (grp := id) (fun j hj => hj)
    (fun p hp => ⟨p, hp, rfl⟩)) fun q x hx p hp => ?_
  have hsing : Finset.univ.filter (fun i : Fin (n + 1) => id (i : ℕ) = p) = {⟨p, hp⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, id, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [hsing, Finset.prod_singleton]
  exact hx ⟨p, hp⟩

/-- **The test at the two corners gives the estimate with a sifted cofactor**: if `resYH` passes the `n + 2` cells,
then for each number `t ≥ 1` of the cofactor's primes the tuples of `n + 1 + t` primes with the first `n + 1` in the
first `n + 1` cells and the product of the last `t` in the last cell are estimated: `fullEst_of_resYHG` with the parts
`SieveTypeIIHM.sifGrp n`. -/
theorem fullEst_of_resYHS {cells : List Cell} {s n : ℕ} (hn : cells.length = n + 1 + 1)
    (hT : SieveResTest.resYH Lnum Lden cells s = true) {κ : ℝ} (hκ : κ = L / DEN) {e₀ : ℝ} (he₀ : 0 < e₀)
    (t : ℕ) (ht : 1 ≤ t) :
    SieveTypeIIHM.FullEst L e₀ (n + t) (fun q x =>
      (∀ i : Fin (n + 1), (q : ℝ) ^ (κ * ((cells.getD i (0, 0)).1 : ℝ)) ≤ x (Fin.castLE (by omega) i) ∧
        (x (Fin.castLE (by omega) i) : ℝ) ≤ (q : ℝ) ^ (κ * ((cells.getD i (0, 0)).2 : ℝ))) ∧
      (q : ℝ) ^ (κ * ((cells.getD (n + 1) (0, 0)).1 : ℝ)) ≤
          ((∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i : ℕ) : ℝ) ∧
        ((∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i : ℕ) : ℝ) ≤
          (q : ℝ) ^ (κ * ((cells.getD (n + 1) (0, 0)).2 : ℝ))) := by
  refine SieveTypeIIHM.FullEst.mono (fullEst_of_resYHG hn hT hκ he₀ (n := n + t) (grp := SieveTypeIIHM.sifGrp n)
    (fun j hj => ?_) (fun p hp => ?_)) fun q x hx p hp => ?_
  · unfold SieveTypeIIHM.sifGrp
    split_ifs <;> omega
  · by_cases hp' : p < n + 1
    · exact ⟨p, by omega, by unfold SieveTypeIIHM.sifGrp; rw [ite_eq_left hp']⟩
    · exact ⟨n + 1, by omega, by unfold SieveTypeIIHM.sifGrp; rw [ite_eq_right (by omega)]; omega⟩
  · by_cases hp' : p < n + 1
    · rw [SieveTypeIIHM.filter_sifGrp_lt hp', Finset.prod_singleton]
      exact hx.1 ⟨p, hp'⟩
    · obtain rfl : p = n + 1 := by omega
      push_cast at hx
      exact hx.2

/-! ### A box evaluated by the test at the two corners -/

set_option maxHeartbeats 4000000 in
/-- **A box evaluated by the test at the two corners, under more atoms.** If `chkIRY` passes the box with the rest
`sr`, the term of the box is evaluated under `m` more atoms, uniformly in the atoms, when the box's atoms and those
are at most `40`: by `chain_res_sifG` with the cofactor's cell when the bit after the box's cells is set, on the
estimate `fullEst_of_resYHS`, and by `chain_res_gen` otherwise, on the estimate `fullEst_of_resYH`. -/
theorem evI_resYE (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr s : ℕ)
    (hok : chkIRY bl sr s = true) {m : ℕ} (hm : 3 * min (k' + 1) 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E →
        |dIP q a (boxFn bl (k' + 1) h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  unfold chkIRY at hok
  rw [rpassY_eq] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, SieveResTest.resYHF_eq] at hok
  obtain ⟨⟨⟨_, hcells⟩, hns⟩, hcof⟩ := hok
  have hc := (cellsFrom_iff 1 bl).1 hcells
  set bx := boxFn bl (k' + 1) h with hbx
  have hbxc : ∀ i, 1 ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl _ h i)
  -- the rest's cells and positions
  have hcsr : mCells bl sr = (ridx (k' + 1) sr).map fun i => bx i := mCells_eq bl (k' + 1) h sr
  obtain ⟨n, hn⟩ : ∃ n, (mCells bl sr).length = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hns).symm⟩
  have hlenr : (ridx (k' + 1) sr).length = n + 1 := by rw [← hn, hcsr, List.length_map]
  obtain ⟨r, hrdef⟩ : ∃ r : Fin (n + 1) → Fin (k' + 1),
      r = fun j : Fin (n + 1) => (ridx (k' + 1) sr)[(j : ℕ)]'(by rw [hlenr]; exact j.2) := ⟨_, rfl⟩
  have hr : Function.Injective r := by
    intro i j hij
    rw [hrdef] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff (ridx_nodup _ _)).1 hij)
  have hcsj : ∀ j : Fin (n + 1), (mCells bl sr)[(j : ℕ)]'(by rw [hn]; exact j.2) = bx (r j) := by
    intro j
    simp only [hcsr, List.getElem_map, hrdef]
  -- the exponent
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have he₀ : 0 < κ * ((1 : ℕ) : ℝ) := by positivity
  have hqx : ∀ (q : ℕ) (e : ℕ), (q : ℝ) ^ (κ * (e : ℝ)) = Xe q e := fun q e => by rw [hκdef, qpow_eq]; rfl
  by_cases hbit : Nat.beq (Nat.land (Nat.shiftRight sr bl.length) 1) 1 = true
  swap
  · -- no cofactor: the estimate on the rest's cells
    rw [Bool.not_eq_true] at hbit
    rw [hbit, Bool.cond_false] at hcof
    have hfull := fullEst_of_resYH hn hcof hκdef he₀
    intro η hη
    obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIHM.chain_res_gen he₀ k' 40 (Λ₁ := L + 1) (by linarith) hfull
    filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ hη] with q hq hq2 hX a ha E hEl hEt
    have : NeZero q := ⟨by omega⟩
    have hq1 : 1 ≤ q := by omega
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
    have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
    have hthr : ThrOK q (specB q bx ++ E) :=
      thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
    have hmain := hq₀ q hq a ha r hr ((specB q bx ++ E).map Atom.toG)
      (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
      (fun rt hp hΩ => by
        obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
          fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
        refine ⟨hsa, fun i => ?_, fun j => ?_⟩
        · rw [hκdef, qpow_eq]
          exact (pow_mono hx1 (hbxc i).1).trans (hcc i).1
        · show (q : ℝ) ^ (κ * (((mCells bl sr).getD (j : ℕ) (0, 0)).1 : ℝ)) ≤ rt (r j) ∧
            (rt (r j) : ℝ) ≤ (q : ℝ) ^ (κ * (((mCells bl sr).getD (j : ℕ) (0, 0)).2 : ℝ))
          rw [List.getD_eq_getElem _ _ (by rw [hn]; exact j.2), hcsj j, hqx, hqx]
          exact ⟨(hcc (r j)).1, (hcc (r j)).2.le⟩)
    rw [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at hmain
    rw [dIP_eq_famSet]
    exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)
  -- the cofactor in the rest, its cell after the box's
  rw [hbit, Bool.cond_true] at hcof
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcof
  obtain ⟨hshi, hT⟩ := hcof
  have hlos : loSum bl = ∑ i, (bx i).1 := by rw [loSum_eq, hbx, sum_boxFn (fun c => c.1) bl _ h]
  have hhis : hiSum bl = ∑ i, (bx i).2 := by rw [hiSum_eq, hbx, sum_boxFn (fun c => c.2) bl _ h]
  have hhead : headLo bl = (bx (Fin.last k')).1 := headLo_eq bl k' h
  simp only [Nat.add_eq, Nat.sub_eq] at hT hshi
  rw [hlos] at hT
  rw [hhis] at hT hshi
  rw [hhead] at hT
  set cl := maxN (DEN - ∑ i, (bx i).2 - 1) (bx (Fin.last k')).1 with hcl
  set cu := DEN - ∑ i, (bx i).1 + 1 with hcu
  set cs : List Cell := mCells bl sr ++ [(cl, cu)] with hcs
  have hcsn : cs.length = n + 1 + 1 := by rw [hcs, List.length_append, hn]; rfl
  have hcsj' : ∀ j : Fin (n + 1), cs.getD j (0, 0) = bx (r j) := by
    intro j
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_left (by rw [hn]; exact j.2)]
    exact hcsj j
  have hcsl : cs.getD (n + 1) (0, 0) = (cl, cu) := by
    rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_append, hn]; simp),
      List.getElem_append_right (by rw [hn])]
    simp [hn]
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIHM.chain_res_sifG he₀ k' 40 (Λ₁ := L + 1) (by linarith)
    (Reg := fun q xs y => (∀ i : Fin (n + 1), (q : ℝ) ^ (κ * ((cs.getD i (0, 0)).1 : ℝ)) ≤ xs i ∧
        (xs i : ℝ) ≤ (q : ℝ) ^ (κ * ((cs.getD i (0, 0)).2 : ℝ))) ∧
      (q : ℝ) ^ (κ * ((cs.getD (n + 1) (0, 0)).1 : ℝ)) ≤ y ∧ (y : ℝ) ≤ (q : ℝ) ^ (κ * ((cs.getD (n + 1) (0, 0)).2 : ℝ)))
    (fun t ht => fullEst_of_resYHS hcsn hT hκdef he₀ t ht)
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ hη, big_ev] with q hq hq2 hX hbig a ha E
    hEl hEt
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx ++ E) :=
    thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
  have hmain := hq₀ q hq a ha r hr ((specB q bx ++ E).map Atom.toG)
    (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
        fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
      have hcx : ∀ i, Xe q (bx i).1 ≤ rt i ∧ (rt i : ℝ) < Xe q (bx i).2 := fun i => hcc i
      obtain ⟨hf0, hf1⟩ := cof_facts hbig bx rt hcx (fun i => (hbxc i).2.1) hshi
      refine ⟨hsa, fun i => ?_, hf0, fun y hy hylo hyhi => ⟨fun j => ?_, ?_⟩⟩
      · rw [hκdef, qpow_eq]
        exact (pow_mono hx1 (hbxc i).1).trans (hcc i).1
      · rw [hcsj' j, hqx, hqx]
        exact ⟨(hcc (r j)).1, (hcc (r j)).2.le⟩
      · obtain ⟨hyc, hyC⟩ := hf1 y hy hylo hyhi
        rw [hcsl, hqx, hqx]
        exact ⟨hyc, hyC⟩)
  rw [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at hmain
  rw [dIP_eq_famSet]
  exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)

/-- **A box evaluated by the test at the two corners.** If `chkIRY` passes the box, its term is evaluated. -/
theorem evI_resY (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr s : ℕ)
    (hok : chkIRY bl sr s = true) : EvI (boxFn bl (k' + 1) h) := by
  intro η hη
  filter_upwards [evI_resYE bl k' h sr s hok (m := 0) (by omega) η hη] with q hq a ha
  have h' := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dIP_nil] at h'

/-- **The tests with the window's test at the two corners too are sound.** -/
theorem resTestsFY_sound : (resTestsFY).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => resTestsFC_sound.soundJ bl f cfg k h hok⟩
  change cond (Nat.beq cfg.kind 4) (chkIRY bl cfg.sr cfg.s1) (resTestsFC.okI bl cfg) = true at hok
  by_cases h4 : cfg.kind = 4
  · rw [show Nat.beq cfg.kind 4 = true from Nat.beq_eq_true_eq _ _ ▸ h4, Bool.cond_true] at hok
    exact evI_resY bl k' h _ _ hok
  · rw [show Nat.beq cfg.kind 4 = false from Bool.eq_false_iff.mpr fun h' => h4 (Nat.eq_of_beq_eq_true h'),
      Bool.cond_false] at hok
    exact resTestsFC_sound.soundI bl cfg k' h hok

end

end SieveAd

#print axioms SieveAd.resTestsFY_sound
