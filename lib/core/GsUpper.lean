import Mathlib
import GsGap
import GsTail

/-! # Ground state at `L = 1/2`: the Rayleigh quotient of the trial vector is below `2·10⁻⁵`

`v = fx 10 xv = cut(p(u + 1/2))` with `p = Σ_{i<10} y_i P̃_{2i}` (shifted Legendre, rational `y`), chosen so that
`p, p', p⁽⁴⁾, p⁽⁵⁾` vanish at `0` and `1`. Then
`weilQg (1/2) v = R(xv) + (1/π)∫_{30}^∞ (Ψ−β*) F²`, the head `R(xv)` is bounded by the exact rational head
matrix plus the proved enclosure, and the tail by six integrations by parts and Plancherel (`GsTail.tail_bound`).
All rational arithmetic is checked by `decide +kernel`. -/

namespace GsUpper

open Finset Real Polynomial MeasureTheory WeilTail WeilTailB WeilHead GsGap

/-- list sum over `range n` -/
def lsum (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

lemma cast_lsum' (n : ℕ) (f : ℕ → ℚ) : ((lsum n f : ℚ) : ℝ) = ∑ k ∈ range n, (f k : ℝ) := cast_lsum n f

/-- coefficients of the shifted Legendre polynomial `P̃_n` -/
def slc (n k : ℕ) : ℚ := (-1) ^ k * (n.choose k) * ((n + k).choose n)

/-- coefficients of `p` -/
def c0 (k : ℕ) : ℚ := lsum 10 (fun i => yq.getD i 0 * slc (2 * i) k)

def lder (c : ℕ → ℚ) (k : ℕ) : ℚ := if k + 1 < 19 then c (k + 1) * (k + 1) else 0

def cj (j : ℕ) : ℕ → ℚ := lder^[j] c0

def ev (c : ℕ → ℚ) (r : ℚ) : ℚ := lsum 19 (fun k => c k * r ^ k)

def sq01 (c : ℕ → ℚ) : ℚ := lsum 19 (fun k => lsum 19 (fun m => c k * c m / (k + m + 1)))

def Aj (j : ℕ) : ℚ := |ev (cj j) 1| + |ev (cj j) 0|

def Ikq (k : ℕ) : ℚ := (202 / 100 - 1) * (1 / ((k - 1) * 30 ^ (k - 1))) + 1 / 30 * (1 / ((k - 2) * 30 ^ (k - 2)))

def qa : ℚ := lsum 10 (fun i => lsum 10 (fun j => Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j * xh i * xh j))
def qe : ℚ := lsum 10 (fun i => lsum 10 (fun j => |Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j|)) * (1 / 10 ^ 28)
def bb (i : ℕ) : ℚ := |yq.getD i 0| * (lq.getD i 0 + 1 / 10 ^ 30)
def ρq : ℚ := 1 / 10 ^ 12 + 10 * (1 / 10 ^ 12) + 6 / 10 ^ 9
def qr : ℚ := ρq * lsum 10 (fun i => lsum 10 (fun j => bb i * bb j))
def tl : ℚ := 100000 / 314159 * (3 / 2 * Aj 2 ^ 2 * Ikq 6 + 6 * Aj 3 ^ 2 * Ikq 8) + 6 * (202 / 100) / 30 ^ 12 * sq01 (cj 6)
def nq : ℚ := lsum 10 (fun i => yq.getD i 0 ^ 2 / (4 * i + 1))

theorem bc_chk : ([0, 1, 4, 5] : List ℕ).all (fun j => ev (cj j) 1 == 0 && ev (cj j) 0 == 0) = true := by
  decide +kernel

theorem upper_chk : qa + qe + qr + tl ≤ 2 / 10 ^ 5 * nq := by decide +kernel

/-! ## Polynomials from coefficient functions -/

noncomputable def lp (c : ℕ → ℚ) : ℝ[X] := ∑ k ∈ range 19, C ((c k : ℚ) : ℝ) * X ^ k

lemma coeff_lp (c : ℕ → ℚ) (k : ℕ) : (lp c).coeff k = if k < 19 then ((c k : ℚ) : ℝ) else 0 := by
  unfold lp
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [sum_eq_single k (fun b _ hb => ite_eq_right (Ne.symm hb)) (fun hk => absurd (mem_range.2 h) hk), ite_eq_left rfl]
  · exact sum_eq_zero (fun b hb => ite_eq_right (by intro e; subst e; exact h (mem_range.1 hb)))

lemma derivative_lp (c : ℕ → ℚ) : derivative (lp c) = lp (lder c) := by
  ext k
  rw [coeff_derivative, coeff_lp, coeff_lp]
  unfold lder
  by_cases h1 : k + 1 < 19
  · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_left h1]; push_cast; ring
  · rw [ite_eq_right h1, zero_mul]
    split_ifs <;> simp

lemma D_lp (j : ℕ) : GsFourier.D (lp c0) j = lp (cj j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    unfold GsFourier.D at ih ⊢
    rw [Function.iterate_succ_apply', ih, derivative_lp]
    unfold cj; rw [Function.iterate_succ_apply']

lemma eval_lp (c : ℕ → ℚ) (w : ℝ) : (lp c).eval w = ∑ k ∈ range 19, ((c k : ℚ) : ℝ) * w ^ k := by
  unfold lp; rw [eval_finsetSum]; simp

lemma eval_lp_q (c : ℕ → ℚ) (r : ℚ) : (lp c).eval (r : ℝ) = ((ev c r : ℚ) : ℝ) := by
  rw [eval_lp]; unfold ev; rw [cast_lsum']; push_cast; rfl

lemma int_lp_sq (c : ℕ → ℚ) : ∫ w in (0:ℝ)..1, (lp c).eval w ^ 2 = ((sq01 c : ℚ) : ℝ) := by
  have e : (fun w => (lp c).eval w ^ 2)
      = fun w => ∑ k ∈ range 19, ∑ m ∈ range 19, ((c k : ℚ) : ℝ) * ((c m : ℚ) : ℝ) * w ^ (k + m) := by
    funext w; rw [eval_lp, sq, sum_mul_sum]
    refine sum_congr rfl (fun k _ => sum_congr rfl (fun m _ => ?_)); ring
  rw [e, intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  unfold sq01; rw [cast_lsum']
  refine sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m _ => by apply Continuous.intervalIntegrable; fun_prop),
    cast_lsum']
  refine sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

/-! ## The trial vector is the cut polynomial -/

lemma slc_zero {n k : ℕ} (h : n < k) : slc n k = 0 := by
  unfold slc; rw [Nat.choose_eq_zero_of_lt h]; simp

lemma sum_sL_eq : ∑ i ∈ range 10, C ((yq.getD i 0 : ℚ) : ℝ) * WeilModes.sL (2 * i) = lp c0 := by
  ext k
  rw [finsetSum_coeff, coeff_lp]
  simp_rw [coeff_C_mul]
  have hc : ∀ i, (WeilModes.sL (2 * i)).coeff k = ((slc (2 * i) k : ℚ) : ℝ) := by
    intro i
    unfold WeilModes.sL slc
    rw [coeff_map, coeff_shiftedLegendre, eq_intCast]
    push_cast; ring
  simp_rw [hc]
  split_ifs with h
  · unfold c0; rw [cast_lsum']; push_cast; rfl
  · refine sum_eq_zero (fun i hi => ?_)
    rw [slc_zero (by have := mem_range.1 hi; omega)]; simp

lemma fx_cutp : WeilPlanch.fx 10 xv = LegSpan.cutp (fun u => (lp c0).eval (u + 1 / 2)) := by
  funext u
  unfold WeilPlanch.fx LegSpan.cutp WeilPlanch.legT
  beta_reduce
  split_ifs with h
  · have hp : (lp c0).eval (u + 1 / 2) = ∑ i ∈ range 10, ((yq.getD i 0 : ℚ) : ℝ) * (WeilModes.sL (2 * i)).eval (u + 1 / 2) := by
      rw [← sum_sL_eq, eval_finsetSum]; simp only [eval_mul, eval_C]
    rw [hp]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.1 hi
    unfold xv; rw [ite_eq_left hi']
    unfold WeilModes.sL
    rw [eval_map, aeval_def, algebraMap_int_eq]
    have hs : Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) = Real.sqrt (4 * i + 1) := by push_cast; ring_nf
    rw [hs]
    have : 0 < Real.sqrt (4 * (i:ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    field_simp
  · simp

lemma Fx_eq_Φ (t : ℝ) : ((WeilZhuRed.Fx 0 10 xv t : ℝ) : ℂ) = GsFourier.Φ (lp c0) t := by
  have h := WeilFourier.fourier_fx 10 xv (t / (2 * π))
  rw [← WeilFourier.fx_eq, fx_cutp, GsFourier.fourier_cutp] at h
  have e1 : 2 * π * (t / (2 * π)) = t := by field_simp
  rw [e1] at h
  exact h.symm

lemma Fx_bound {t : ℝ} (ht : 0 < t) :
    |WeilZhuRed.Fx 0 10 xv t| ≤ ((Aj 2 : ℚ) : ℝ) / t ^ 3 + ((Aj 3 : ℚ) : ℝ) / t ^ 4
      + |‖GsFourier.Φ (lp (cj 6)) t‖| / t ^ 6 := by
  have hb : ∀ j ∈ ({0, 1, 4, 5} : Finset ℕ), (GsFourier.D (lp c0) j).eval 1 = 0 ∧ (GsFourier.D (lp c0) j).eval 0 = 0 := by
    intro j hj
    have hc := bc_chk
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hc
    rw [D_lp, show (1:ℝ) = ((1:ℚ):ℝ) by simp, show (0:ℝ) = ((0:ℚ):ℝ) by simp, eval_lp_q, eval_lp_q]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [hc]
  have h := GsFourier.six_ibp (lp c0) ht hb
  rw [← Fx_eq_Φ, Complex.norm_real, Real.norm_eq_abs] at h
  simp only [D_lp, abs_norm] at h ⊢
  have e : ∀ j, |(lp (cj j)).eval 1| + |(lp (cj j)).eval 0| = ((Aj j : ℚ) : ℝ) := by
    intro j
    rw [show (1:ℝ) = ((1:ℚ):ℝ) by simp, show (0:ℝ) = ((0:ℚ):ℝ) by simp, eval_lp_q, eval_lp_q]
    unfold Aj; push_cast; rfl
  rw [e, e] at h
  exact h

/-! ## The head -/

lemma xv_le_bb {i : ℕ} (hi : i < 10) : |xv i| ≤ ((bb i : ℚ) : ℝ) := by
  obtain ⟨-, b2⟩ := bracket hi
  unfold xv bb; rw [ite_eq_left hi]; push_cast
  have hs : 0 < 1 / Real.sqrt (4 * (i:ℝ) + 1) := by
    have := Real.sqrt_pos.2 (by positivity : (0:ℝ) < 4 * i + 1); positivity
  rw [div_eq_mul_one_div, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)

lemma head_bd : qf (Rm 0 1 wψ βs) xv (range 10) (range 10) ≤ ((qa + qe + qr : ℚ) : ℝ) := by
  have E : HeadEnc 0 EvenQ.bq EvenQ.pq EvenQ.cq (1/10^12) (1/10^12) (6/10^9) :=
    ⟨WeilConst.beta_enc_even, by have := WeilConst.pole_enc_even; simpa using this, CmFin.cmEnc_even⟩
  have term : ∀ i < 10, ∀ j < 10, xv i * Rm 0 1 wψ βs i j * xv j
      ≤ ((Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j * xh i * xh j : ℚ) : ℝ)
        + ((|Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j| * (1 / 10 ^ 28) : ℚ) : ℝ) + ((ρq * (bb i * bb j) : ℚ) : ℝ) := by
    intro i hi j hj
    have hR := Rm_near (σ := 1) (by norm_num) E (by norm_num) even_pchk (by omega : i < 28) (by omega : j < 28)
    rw [Rat.cast_one] at hR
    set a := ((Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j : ℚ) : ℝ)
    have hn := xv_near i j
    have bi := xv_le_bb hi
    have bj := xv_le_bb hj
    have e1 : xv i * Rm 0 1 wψ βs i j * xv j
        = a * ((xh i : ℝ) * (xh j : ℝ)) + a * (xv i * xv j - (xh i : ℝ) * (xh j : ℝ))
          + (Rm 0 1 wψ βs i j - a) * (xv i * xv j) := by ring
    rw [e1]
    have t2 : a * (xv i * xv j - (xh i : ℝ) * (xh j : ℝ)) ≤ |a| * (1 / 10 ^ 28) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    have t3 : (Rm 0 1 wψ βs i j - a) * (xv i * xv j) ≤ (ρq : ℝ) * ((bb i : ℝ) * (bb j : ℝ)) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul]
      have hρ : |Rm 0 1 wψ βs i j - a| ≤ (ρq : ℝ) := by
        unfold ρq; push_cast; linarith
      have h0 : 0 ≤ |xv i| * |xv j| := by positivity
      calc |Rm 0 1 wψ βs i j - a| * (|xv i| * |xv j|) ≤ (ρq : ℝ) * (|xv i| * |xv j|) := by gcongr
        _ ≤ (ρq : ℝ) * ((bb i : ℝ) * (bb j : ℝ)) := by
          gcongr
          · unfold ρq; norm_num
          · exact (abs_nonneg _).trans bi
    push_cast
    unfold a at t2 t3 ⊢
    linarith
  unfold qf
  have e : ((qa + qe + qr : ℚ) : ℝ) = ∑ i ∈ range 10, ∑ j ∈ range 10,
      (((Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j * xh i * xh j : ℚ) : ℝ)
        + ((|Aq 1 EvenQ.bq EvenQ.pq EvenQ.cq i j| * (1 / 10 ^ 28) : ℚ) : ℝ) + ((ρq * (bb i * bb j) : ℚ) : ℝ)) := by
    unfold qa qe qr
    simp only [Rat.cast_add, Rat.cast_mul, cast_lsum', sum_add_distrib, mul_sum, sum_mul]
  rw [e]
  exact sum_le_sum (fun i hi => sum_le_sum (fun j hj => term i (mem_range.1 hi) j (mem_range.1 hj)))

/-! ## Main bound -/

lemma normSq_v : WeilForm.normSq (WeilPlanch.fx 10 xv) = ((nq : ℚ) : ℝ) := by
  have h := WeilCoer.normSq_hx 10 xv 0
  rw [WeilOdd.hx_y0] at h
  rw [h]; simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, add_zero]
  unfold nq; rw [cast_lsum']
  refine sum_congr rfl (fun i hi => ?_)
  unfold xv; rw [ite_eq_left (mem_range.1 hi), div_pow, Real.sq_sqrt (by positivity)]; push_cast; ring

lemma Ik_eq (k : ℕ) (_hk : 2 ≤ k) : GsTail.Ik k = ((Ikq k : ℚ) : ℝ) := by
  unfold GsTail.Ik Ikq
  push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
  ring

/-- **Upper bound for the ground state**: the explicit even trial vector `v = fx 10 xv` has Rayleigh quotient
`weilQg (1/2) v / ‖v‖² ≤ 2·10⁻⁵`. -/
theorem trial_upper :
    WeilForm.weilQg (1 / 2) (WeilPlanch.fx 10 xv) ≤ (2 / 10 ^ 5) * WeilForm.normSq (WeilPlanch.fx 10 xv) := by
  rw [WeilOdd.weilQg_fx, ← WeilOdd.QF0_eq, normSq_v]
  have P := WeilPlanch.modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))
  obtain ⟨-, hE⟩ := GsTail.QF_eq 0 1 P 10 xv
  obtain ⟨hg, hge⟩ := GsFourier.plancherel (lp (cj 6))
  rw [int_lp_sq] at hge
  have ht := GsTail.tail_bound 10 xv ((Aj 2 : ℚ) : ℝ) ((Aj 3 : ℚ) : ℝ) ((sq01 (cj 6) : ℚ) : ℝ)
    (fun t => ‖GsFourier.Φ (lp (cj 6)) t‖) hg hge.le (fun t ht => Fx_bound ht)
  rw [Ik_eq 6 (by norm_num), Ik_eq 8 (by norm_num)] at ht
  have hh := head_bd
  have hc : ((qa + qe + qr + tl : ℚ) : ℝ) ≤ ((2 / 10 ^ 5 * nq : ℚ) : ℝ) := by exact_mod_cast upper_chk
  have hπ := Real.pi_gt_d6
  have hX : 0 ≤ 3 / 2 * ((Aj 2 : ℚ) : ℝ) ^ 2 * ((Ikq 6 : ℚ) : ℝ) + 6 * ((Aj 3 : ℚ) : ℝ) ^ 2 * ((Ikq 8 : ℚ) : ℝ) := by
    have : (0:ℝ) ≤ ((Ikq 6 : ℚ) : ℝ) := by unfold Ikq; norm_num
    have : (0:ℝ) ≤ ((Ikq 8 : ℚ) : ℝ) := by unfold Ikq; norm_num
    positivity
  have hpi : 1 / π ≤ 100000 / 314159 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1 := mul_le_mul_of_nonneg_right hpi hX
  rw [hE]
  unfold tl at hc
  push_cast at hc hh
  nlinarith

end GsUpper
