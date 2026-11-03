import Mathlib
import CmWD
import CmMomDef
import WeilPlanch

/-! # Quadrature of `∫₀¹ wψ(30s) jₙ(15s) jₘ(15s) ds` against the piecewise model and the Bessel polynomials -/

namespace CmAsm

open Finset Real CmPoly CmW CmNu CmLhD CmBessel CmWD CmMom WeilTailB

def Bq (n : ℕ) : ℚ := (15 / 2) ^ n / (n.factorial : ℚ)
def eTq (n : ℕ) : ℚ := eT 128 40 96 n
def eJ (n m : ℕ) : ℚ := Bq n * eTq m + (Bq m + eTq m) * eTq n
noncomputable def A (n : ℕ) (s : ℝ) : ℝ := jA 128 40 96 n s
def q (n k : ℕ) : ℚ := (qh 128 40 96 n).getD k 0

lemma jP15 (n : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |jP n (15 * s)| ≤ (Bq n : ℝ) := by
  refine (jP_bound n (by positivity)).trans ?_
  unfold Bq; push_cast
  gcongr; linarith

lemma A_err (n : ℕ) (hn : n < 56) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n (15 * s) - A n s| ≤ (eTq n : ℝ) :=
  jP_s 128 40 96 n (by omega) (by norm_num) h0 h1

lemma eT_nonneg (n : ℕ) (hn : n < 56) : (0:ℝ) ≤ eTq n :=
  (abs_nonneg _).trans (A_err n hn (s := 0) le_rfl zero_le_one)

lemma JJ_err (n m : ℕ) (hn : n < 56) (hm : m < 56) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n (15 * s) * jP m (15 * s) - A n s * A m s| ≤ (eJ n m : ℝ) := by
  have a := jP15 n h0 h1; have b := jP15 m h0 h1
  have ea := A_err n hn h0 h1; have eb := A_err m hm h0 h1
  have hb : |A m s| ≤ (Bq m : ℝ) + eTq m := by
    have := abs_sub_abs_le_abs_sub (A m s) (jP m (15 * s)); rw [abs_sub_comm] at eb
    linarith [abs_sub_comm (A m s) (jP m (15 * s))]
  have e : jP n (15 * s) * jP m (15 * s) - A n s * A m s
      = jP n (15 * s) * (jP m (15 * s) - A m s) + A m s * (jP n (15 * s) - A n s) := by ring
  rw [e]; unfold eJ; push_cast
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul a eb (abs_nonneg _) ((abs_nonneg _).trans a))
    (mul_le_mul hb ea (abs_nonneg _) ((abs_nonneg _).trans hb))

lemma AA_eq (n m : ℕ) (s : ℝ) : A n s * A m s =
    ∑ k ∈ range 40, ∑ l ∈ range 40, ((q n k : ℚ) : ℝ) * ((q m l : ℚ) : ℝ) * s ^ (n + m + 2 * k + 2 * l) := by
  unfold A jA q
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

noncomputable def Wp (p : ℕ) (s : ℝ) : ℝ := hev GD (s ^ 2) - hev (LD p) s

lemma Wp_cont (p : ℕ) : Continuous (Wp p) := by
  unfold Wp; exact ((hev_cont _).comp (continuous_pow 2)).sub (hev_cont _)

lemma A_cont (n : ℕ) : Continuous (A n) := by
  unfold A jA; fun_prop

lemma mom_piece (p J : ℕ) (a b : ℚ) :
    ∫ s in (a:ℝ)..b, Wp p s * s ^ J = (pmom 2 GD J a b : ℝ) - (pmom 1 (LD p) J a b : ℝ) := by
  rw [← pmom_eq, ← pmom_eq, ← intervalIntegral.integral_sub]
  · congr 1; funext s; unfold Wp; rw [pow_one]; ring
  all_goals exact Continuous.intervalIntegrable (by
    first | exact ((hev_cont _).comp (continuous_pow 2)).mul (continuous_pow J)
          | exact ((hev_cont _).comp (continuous_pow 1)).mul (continuous_pow J)) _ _

lemma model_piece (p n m : ℕ) (a b : ℚ) :
    ∫ s in (a:ℝ)..b, Wp p s * (A n s * A m s) = ∑ k ∈ range 40, ∑ l ∈ range 40,
      ((q n k : ℚ) : ℝ) * ((q m l : ℚ) : ℝ) *
        ((pmom 2 GD (n + m + 2 * k + 2 * l) a b : ℝ) - (pmom 1 (LD p) (n + m + 2 * k + 2 * l) a b : ℝ)) := by
  simp_rw [AA_eq, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable; apply continuous_finsetSum; intro l _
    exact (Wp_cont p).mul (continuous_const.mul (continuous_pow _)))]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
    apply Continuous.intervalIntegrable; exact (Wp_cont p).mul (continuous_const.mul (continuous_pow _)))]
  refine sum_congr rfl fun l _ => ?_
  rw [← mom_piece, ← intervalIntegral.integral_const_mul]
  congr 1; funext s; ring

/-! ## pieces -/

lemma al_cast (p : ℕ) : ((al p : ℚ) : ℝ) = (p : ℝ) / 128 := by simp [al, NP]
lemma be_cast (p : ℕ) : ((be p : ℚ) : ℝ) = ((p : ℝ) + 1) / 128 := by simp [be, NP]

lemma adj (f : ℝ → ℝ) (hf : Continuous f) :
    ∑ p ∈ range 128, ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), f s = ∫ s in (0:ℝ)..1, f s := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / 128) (n := 128) (fun k _ => hf.intervalIntegrable _ _)
  simp only [CharP.cast_eq_zero, zero_div, Nat.cast_ofNat, div_self (by norm_num : (128:ℝ) ≠ 0)] at h
  rw [← h]
  refine sum_congr rfl fun p _ => ?_
  rw [al_cast, be_cast]; push_cast; rfl

lemma f_cont : Continuous (fun s : ℝ => wψ (30 * s)) := by
  unfold wψ; exact (WeilPlanch.Psi_cont.comp (continuous_const.mul continuous_id)).sub continuous_const

lemma jj_cont (n m : ℕ) : Continuous (fun s : ℝ => jP n (15 * s) * jP m (15 * s)) :=
  ((WeilPlanch.jP_cont n).comp (continuous_const.mul continuous_id)).mul
    ((WeilPlanch.jP_cont m).comp (continuous_const.mul continuous_id))

lemma piece_err (p n m : ℕ) (hp : p < 128) (hn : n < 56) (hm : m < 56) :
    |(∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), wψ (30 * s) * (jP n (15 * s) * jP m (15 * s)))
      - ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), Wp p s * (A n s * A m s)|
      ≤ (εw : ℝ) * (∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), |jP n (15 * s) * jP m (15 * s)|)
        + 56 * (eJ n m : ℝ) / 128 := by
  have hab : ((al p : ℚ) : ℝ) ≤ ((be p : ℚ) : ℝ) := by rw [al_cast, be_cast]; linarith
  have i1 : IntervalIntegrable (fun s : ℝ => wψ (30 * s) * (jP n (15 * s) * jP m (15 * s)))
      MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) := (f_cont.mul (jj_cont n m)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s : ℝ => Wp p s * (A n s * A m s))
      MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) :=
    ((Wp_cont p).mul ((A_cont n).mul (A_cont m))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub i1 i2]
  have hg : ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), ((εw : ℝ) * |jP n (15 * s) * jP m (15 * s)| + 56 * (eJ n m : ℝ))
      = (εw : ℝ) * (∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), |jP n (15 * s) * jP m (15 * s)|)
        + 56 * (eJ n m : ℝ) / 128 := by
    have j1 : IntervalIntegrable (fun s : ℝ => (εw : ℝ) * |jP n (15 * s) * jP m (15 * s)|)
        MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) :=
      (continuous_const.mul (jj_cont n m).abs).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun _ : ℝ => 56 * (eJ n m : ℝ))
        MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) := intervalIntegrable_const
    rw [intervalIntegral.integral_add j1 j2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      al_cast, be_cast, smul_eq_mul]
    ring
  rw [← hg, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (MeasureTheory.ae_of_all _ fun s hs => ?_)
    ((continuous_const.mul (jj_cont n m).abs).add continuous_const |>.intervalIntegrable _ _)
  rw [al_cast, be_cast] at hs
  have hNP : ((NP : ℕ) : ℝ) = 128 := by norm_num [NP]
  have h1 : (p : ℝ) / NP ≤ s := by rw [hNP]; exact hs.1.le
  have h2 : s ≤ ((p : ℝ) + 1) / NP := by rw [hNP]; exact hs.2
  have hp' : (p : ℝ) + 1 ≤ 128 := by exact_mod_cast hp
  have s0 : 0 ≤ s := le_trans (by positivity) hs.1.le
  have s1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by norm_num)]; exact hp')
  have hw := w_data p (by simpa [NP] using hp) h1 h2
  have hf := wψ_bound (t := 30 * s) (by linarith) (by linarith)
  have hJ := JJ_err n m hn hm s0 s1
  have hε : (εw : ℝ) ≤ 1 := by norm_num [εw]
  have hW : |Wp p s| ≤ 56 := by
    unfold Wp; have := abs_sub_abs_le_abs_sub (wψ (30 * s)) (hev GD (s ^ 2) - hev (LD p) s)
    have := abs_sub_comm (wψ (30 * s)) (hev GD (s ^ 2) - hev (LD p) s)
    have := abs_sub_abs_le_abs_sub (hev GD (s ^ 2) - hev (LD p) s) (wψ (30 * s)); linarith
  have e : wψ (30 * s) * (jP n (15 * s) * jP m (15 * s)) - Wp p s * (A n s * A m s)
      = (wψ (30 * s) - Wp p s) * (jP n (15 * s) * jP m (15 * s))
        + Wp p s * (jP n (15 * s) * jP m (15 * s) - A n s * A m s) := by ring
  rw [Real.norm_eq_abs, e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (wψ (30 * s) - Wp p s), abs_mul (Wp p s)]
  have hw' : |wψ (30 * s) - Wp p s| ≤ εw := by unfold Wp; exact hw
  have hε0 : (0:ℝ) ≤ εw := by norm_num [εw]
  exact add_le_add (mul_le_mul hw' le_rfl (abs_nonneg _) hε0) (mul_le_mul hW hJ (abs_nonneg _) (by norm_num))

/-- exact model quadrature value -/
noncomputable def Ih (n m : ℕ) : ℝ := ∑ k ∈ range 40, ∑ l ∈ range 40,
  ((q n k : ℚ) : ℝ) * ((q m l : ℚ) : ℝ) *
    (((mG ((n + m) / 2 + k + l) : ℚ) : ℝ) - ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ))

lemma Ih_eq (n m : ℕ) (hpar : (n + m) % 2 = 0) :
    ∑ p ∈ range 128, ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), Wp p s * (A n s * A m s) = Ih n m := by
  simp_rw [model_piece]
  rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]; refine sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum, sum_sub_distrib]
  have hJ : n + m + 2 * k + 2 * l = 2 * ((n + m) / 2 + k + l) := by omega
  congr 2
  · rw [hJ]
    have h := adj (fun s => hev GD (s ^ 2) * s ^ (2 * ((n + m) / 2 + k + l)))
      (((hev_cont _).comp (continuous_pow 2)).mul (continuous_pow _))
    simp only [pmom_eq] at h
    rw [h, show ((0:ℝ)) = ((0:ℚ):ℝ) by simp, show ((1:ℝ)) = ((1:ℚ):ℝ) by simp, pmom_eq]
    rfl
  · rw [hJ]; rfl

theorem I_err (n m : ℕ) (hn : n < 56) (hm : m < 56) (hpar : (n + m) % 2 = 0) :
    |(∫ s in (0:ℝ)..1, wψ (30 * s) * (jP n (15 * s) * jP m (15 * s))) - Ih n m|
      ≤ (εw : ℝ) * (∫ s in (0:ℝ)..1, |jP n (15 * s) * jP m (15 * s)|) + 56 * (eJ n m : ℝ) := by
  rw [← adj (fun s => wψ (30 * s) * (jP n (15 * s) * jP m (15 * s))) (f_cont.mul (jj_cont n m)),
    ← adj (fun s => |jP n (15 * s) * jP m (15 * s)|) (jj_cont n m).abs, ← Ih_eq n m hpar, ← sum_sub_distrib,
    Finset.mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : (56 * (eJ n m : ℝ)) = ∑ p ∈ range 128, 56 * (eJ n m : ℝ) / 128 := by
    rw [sum_const, card_range]; simp; ring
  rw [this, ← sum_add_distrib]
  exact sum_le_sum fun p hp => piece_err p n m (mem_range.1 hp) hn hm

end CmAsm
