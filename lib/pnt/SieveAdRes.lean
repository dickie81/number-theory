/-
# The resonant window's test of a box in the main tree is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The setting is a route with `RouteOK` whose exponent is `Lnum/Lden` (`SieveQ.IBFits`); the test
is `SieveAdResDefs.lean`'s `chkIR`. Write `κ = L/DEN`.

* `mList F bl m`: the values `F c` of the cells at the set bits of `m`, in the list's order; `rpass_eq`: `rpass`
  computes them, the sum of the upper ends, their number, the cells' check and the length. `ridx k m`: the box's
  indices of those cells, in the list's order; `mList_eq`: `mList` is `F` of the box's values there.
* `evI_resE`: **a box evaluated by the resonant window, under more atoms.** If `chkIR` passes the box with the rest
  `sr`, the term of the box is evaluated (`SieveAd.EvI`), the variable being the other primes and the cofactor:
  `SieveResTest.resT_sound_cells` gives `ResBox` on the rest's cells and `SieveTypeIIHM.chain_res_exp` the bound.
* `evI_res`, `resTestsF_sound`: so the tests with the resonant window, `resTestsF`, are sound (`SieveAd.Tests.Sound`).

The file imports `SieveAdTwo.lean`, `SieveAdFill.lean`, `SieveAdFast.lean`, `SieveAdResDefs.lean`,
`SieveResTerm.lean` and `SieveResTest.lean`.
-/
import SieveAdTwo
import SieveAdFill
import SieveAdFast
import SieveAdResDefs
import SieveResTerm
import SieveResTest

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-! ### The rest's cells in the list's order -/

/-- The values `F c` of the cells at the set bits of `m`, in the list's order. -/
def mList (F : Cell → ℕ) : List Cell → ℕ → List ℕ
  | [], _ => []
  | c :: b, m => if Nat.testBit m 0 then F c :: mList F b (m / 2) else mList F b (m / 2)

theorem rpass_cons {α : Type} (x : Cell) (b : List Cell) (m : ℕ) (k : List ℕ → ℕ → ℕ → Bool → ℕ → α) :
    rpass (x :: b) m k = rpass b (Nat.div m 2) fun los hs ns ok n =>
      k (cond (Nat.beq (Nat.land m 1) 1) (x.1 :: los) los) (Nat.add (Nat.mul (Nat.land m 1) x.2) hs)
        (Nat.add (Nat.land m 1) ns) (ok && Nat.ble 1 x.1 && Nat.ble x.1 x.2 && Nat.ble x.2 DEN) (Nat.succ n) :=
  rfl

/-- **What the pass gives its continuation**: the rest's lower ends, the sum of its upper ends, their number, the
cells' check and the length. -/
theorem rpass_eq {α : Type} : ∀ (bl : List Cell) (m : ℕ) (k : List ℕ → ℕ → ℕ → Bool → ℕ → α),
    rpass bl m k = k (mList (fun c => c.1) bl m) (mSum (fun c => c.2) bl m) (mList (fun c => c.1) bl m).length
      (cellsFrom 1 bl) bl.length
  | [], _, _ => rfl
  | x :: b, m, k => by
    rw [rpass_cons, rpass_eq b]
    have hbit : Nat.beq (Nat.land m 1) 1 = Nat.testBit m 0 := by
      rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl
    have hland : Nat.land m 1 = if Nat.testBit m 0 then 1 else 0 := by
      rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    have hdiv : Nat.div m 2 = m / 2 := rfl
    rw [hbit, hdiv]
    simp only [mList, mSum, cellsFrom, List.length_cons]
    cases hb : Nat.testBit m 0
    · simp only [hland, hb, Bool.cond_false, ite_false, Bool.false_eq_true, Nat.mul_eq, Nat.add_eq, zero_mul,
        zero_add]
      congr 1
      cases cellsFrom 1 b <;> cases Nat.ble 1 x.1 <;> cases Nat.ble x.1 x.2 <;> cases Nat.ble x.2 DEN <;> rfl
    · simp only [hland, hb, Bool.cond_true, ite_true, Nat.mul_eq, Nat.add_eq, one_mul, List.length_cons]
      congr 1
      · ring
      · cases cellsFrom 1 b <;> cases Nat.ble 1 x.1 <;> cases Nat.ble x.1 x.2 <;> cases Nat.ble x.2 DEN <;> rfl

/-- The box's indices of the cells at the set bits of `m`, in the list's order. -/
def ridx (k m : ℕ) : List (Fin k) := (List.finRange k).reverse.filter fun i => Nat.testBit m (k - 1 - (i : ℕ))

theorem ridx_nodup (k m : ℕ) : (ridx k m).Nodup := (List.nodup_reverse.mpr (List.nodup_finRange k)).filter _

theorem mem_ridx {k m : ℕ} (i : Fin k) : i ∈ ridx k m ↔ i ∈ mset k m := by
  simp [ridx, mset]

theorem ridx_succ (n m : ℕ) :
    ridx (n + 1) m = if Nat.testBit m 0 then Fin.last n :: (ridx n (m / 2)).map Fin.castSucc
      else (ridx n (m / 2)).map Fin.castSucc := by
  unfold ridx
  rw [List.finRange_succ_last, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.filter_cons, ← List.map_reverse, List.filter_map]
  have hlast : (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ)) = 0 := by simp
  have hcs : ((fun i : Fin (n + 1) => Nat.testBit m (n + 1 - 1 - (i : ℕ))) ∘ Fin.castSucc) =
      fun j : Fin n => Nat.testBit (m / 2) (n - 1 - (j : ℕ)) := by
    funext j
    have hj := j.2
    simp only [Function.comp, Fin.val_castSucc]
    rw [show n + 1 - 1 - (j : ℕ) = (n - 1 - (j : ℕ)) + 1 by omega, Nat.testBit_succ]
  rw [hcs, hlast]

/-- **`mList` is `F` of the box's values at its indices**, in the list's order. -/
theorem mList_eq (F : Cell → ℕ) : ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k) (m : ℕ),
    mList F bl m = (ridx k m).map fun i => F (boxFn bl k h i)
  | [], k, h, m => by
    subst h
    simp [mList, ridx]
  | x :: b, k, h, m => by
    subst h
    show mList F (x :: b) m = (ridx (b.length + 1) m).map fun i => F (boxFn (x :: b) (b.length + 1) rfl i)
    rw [ridx_succ, boxFn_cons x b b.length rfl, mList, mList_eq F b b.length rfl (m / 2)]
    cases Nat.testBit m 0
    · simp only [Bool.false_eq_true, ite_false, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp [Function.comp, Fin.snoc_castSucc]
    · simp only [ite_true, List.map_cons, List.map_map, Fin.snoc_last]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp [Function.comp, Fin.snoc_castSucc]

/-! ### A box evaluated by the resonant window -/

section

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 4000000 in
/-- **A box evaluated by the resonant window, under more atoms.** If `chkIR` passes the box with the rest `sr`, the
term of the box is evaluated under `m` more atoms, uniformly in the atoms, when the box's atoms and those are at
most `40`: the variable is the product of the box's other primes and the cofactor, the rest the primes of `sr`. -/
theorem evI_resE (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIR bl sr kk hh = true) {m : ℕ} (hm : 3 * min (k' + 1) 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E →
        |dIP q a (boxFn bl (k' + 1) h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  unfold chkIR at hok
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
  have hres := SieveResTest.resT_sound_cells hLd hc1 hT
  have hhs : mSum (fun c => c.2) bl sr + 1 < DEN := by
    have := SieveResTest.resT_hs hT
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

/-- **A box evaluated by the resonant window.** If `chkIR` passes the box with the rest `sr`, its term is
evaluated. -/
theorem evI_res (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (sr kk hh : ℕ)
    (hok : chkIR bl sr kk hh = true) : EvI (boxFn bl (k' + 1) h) := by
  intro η hη
  filter_upwards [evI_resE bl k' h sr kk hh hok (m := 0) (by omega) η hη] with q hq a ha
  have h' := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dIP_nil] at h'

/-- **The tests with the resonant window are sound.** -/
theorem resTestsF_sound : (resTestsF).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => ?_⟩
  · change cond (Nat.beq cfg.kind 3) (okIR bl cfg) (fillTestsF.okI bl cfg) = true at hok
    by_cases h3 : cfg.kind = 3
    · rw [show Nat.beq cfg.kind 3 = true from Nat.beq_eq_true_eq _ _ ▸ h3, Bool.cond_true] at hok
      exact evI_res bl k' h _ _ _ hok
    · rw [show Nat.beq cfg.kind 3 = false from Bool.eq_false_iff.mpr fun h' => h3 (Nat.eq_of_beq_eq_true h'),
        Bool.cond_false, fillTestsF_eq] at hok
      exact fillTests_sound.soundI bl cfg k' h hok
  · change fillTestsF.okJ bl f cfg = true at hok
    rw [fillTestsF_eq] at hok
    exact fillTests_sound.soundJ bl f cfg k h hok

end

end SieveAd
