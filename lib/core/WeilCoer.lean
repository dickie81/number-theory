import Mathlib
import WeilOddPos

/-! # Coercivity on mode sums: `weilQg (1/2) h ≥ 10⁻⁸ ‖h‖²` for `h = Σ xᵢT_{2i} + Σ yᵢT_{2i+1}` -/

namespace WeilCoer

open Real Finset MeasureTheory WeilPlanch WeilZhuRed WeilOdd WeilTailB WeilConst

theorem evenHead : EvenHead :=
  WeilHead.evenHead_of ⟨beta_enc_even, by have := pole_enc_even; simpa using this, CmFin.cmEnc_even⟩

theorem oddHead : OddHead :=
  WeilHead.oddHead_of ⟨beta_enc_odd.trans (by norm_num), fun i hi => (pole_enc_odd i hi).trans (by norm_num),
    CmFin.cmEnc_odd⟩

lemma QF0_ge (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) : (1 / 100000000 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ QF 0 1 N x :=
  (even_margin evenHead N hN x).trans (QF_ge_R 0 1 (modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))) N x)

lemma QF1_ge (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) : (2 / 1000000 : ℝ) * ∑ i ∈ range N, y i ^ 2 ≤ QF 1 (-1) N y :=
  (odd_margin oddHead N hN y).trans (QF_ge_R 1 (-1) (modePlancherel_of WeilModes.modeDecay 1 (WeilFourier.modeOrth (by norm_num))) N y)

lemma sq_mass (par : ℕ) (hp : par < 2) (N : ℕ) (x : ℕ → ℝ) :
    (1 / π) * ∫ t in Set.Ioi 0, Fx par N x t ^ 2 = ∑ i ∈ range N, x i ^ 2 := by
  have P := modePlancherel_of WeilModes.modeDecay par (WeilFourier.modeOrth hp)
  have h := (expand_int par N x (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P.int1 i j)).2
  simp only [one_mul] at h
  rw [h, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum, sum_eq_single i]
  · rw [← mul_assoc, mul_comm (1 / π), mul_assoc, P.orth, if_pos rfl]; ring
  · intro j _ hj; rw [← mul_assoc, mul_comm (1 / π), mul_assoc, P.orth, if_neg (Ne.symm hj)]; ring
  · intro h; exact absurd hi h

theorem normSq_hx (N : ℕ) (x y : ℕ → ℝ) :
    WeilForm.normSq (hx N x y) = ∑ i ∈ range N, x i ^ 2 + ∑ i ∈ range N, y i ^ 2 := by
  have hn : WeilForm.normSq (hx N x y) = WeilForm.autocorr (hx N x y) 0 := by
    unfold WeilForm.normSq WeilForm.autocorr; congr 1; funext t; rw [add_zero, sq]
  have P0 := modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))
  have P1 := modePlancherel_of WeilModes.modeDecay 1 (WeilFourier.modeOrth (by norm_num))
  have a0 := (expand_int 0 N x (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
  have a1 := (expand_int 1 N y (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
  simp only [one_mul] at a0 a1
  rw [hn, acorr_hx N x y (v := 0) (by norm_num)]
  simp only [mul_zero, Real.cos_zero, one_mul]
  unfold S
  rw [integral_add a0 a1, mul_add, sq_mass 0 (by norm_num), sq_mass 1 (by norm_num)]

/-- the coercivity constant -/
noncomputable def cW : ℝ := 1 / 100000000

theorem coer_hx (N : ℕ) (hN : 28 ≤ N) (x y : ℕ → ℝ) :
    cW * WeilForm.normSq (hx N x y) ≤ WeilForm.weilQg (1 / 2) (hx N x y) := by
  rw [normSq_hx, weilQg_hx]
  have a := QF0_ge N hN x; have b := QF1_ge N hN y
  have : 0 ≤ ∑ i ∈ range N, y i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  unfold cW; nlinarith

/-- padding: any `N` -/
theorem coer_hx' (N : ℕ) (x y : ℕ → ℝ) :
    cW * WeilForm.normSq (hx N x y) ≤ WeilForm.weilQg (1 / 2) (hx N x y) := by
  have e : hx N x y = hx (N + 28) (fun i => if i < N then x i else 0) (fun i => if i < N then y i else 0) := by
    funext u; unfold hx fx gx
    rw [sum_range_add, sum_range_add]
    simp only [lt_add_iff_pos_right, add_lt_iff_neg_left, not_lt_zero', if_false, zero_mul, sum_const_zero, add_zero]
    congr 1
    · exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.1 hi)]
    · exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.1 hi)]
  rw [e]; exact coer_hx _ (by omega) _ _

end WeilCoer
