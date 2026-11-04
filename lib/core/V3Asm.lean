import Mathlib
import CmAsm
import V3Bessel
import V3Scale

/-! # Quadrature of `∫₀¹ wψ(30s) jₙ(15λs) jₘ(15λs) ds`, `λ = log 3`, against the `L = 1/2` piecewise model

The weight side is `CmAsm`'s unchanged: the 128-piece model `Wp p` of `wψ(30 s)` (pointwise error `εw`) and its
exact moments. Only the Bessel side changes: `jP n (15 λ s)` is replaced by the polynomial `A3 n s` of
`jP n (X̂ s)`, `X̂ = 15·l3lo`, with error `eTq3 n` (Taylor, rounding and the Lipschitz move from `X̂` to `15 λ`). -/

namespace V3Asm

open Finset Real CmPoly CmNu CmLhD CmBessel CmWD CmMom WeilTailB V3Bessel CmAsm

/-- The rational stand-in for `15 λ`, the bound on its distance from `15 λ`, and a common upper bound. -/
def Xh : ℚ := 15 * V3Log.l3lo
def dX : ℚ := 15 * (V3Log.l3hi - V3Log.l3lo)
def X0 : ℚ := 33 / 2

def Bq3 (n : ℕ) : ℚ := (33 / 4) ^ n / (n.factorial : ℚ)
def Lip (n : ℕ) : ℚ := (2 * n * X0 ^ (n - 1) + 2 * X0 ^ n) / (2 ^ (n + 1) * (n.factorial : ℚ))
def eTq3 (n : ℕ) : ℚ := eTX 128 Xh 40 96 n + Lip n * dX
def eJ3 (n m : ℕ) : ℚ := Bq3 n * eTq3 m + (Bq3 m + eTq3 m) * eTq3 n
noncomputable def A3 (n : ℕ) (s : ℝ) : ℝ := jAX 128 Xh 40 96 n s
def q3 (n k : ℕ) : ℚ := (qhX 128 Xh 40 96 n).getD k 0

lemma lam15 : 15 * V3Scale.lam ≤ (X0 : ℝ) := by
  have := V3Scale.lam_bounds.2; unfold V3Log.l3hi at this; unfold X0; push_cast at this ⊢; linarith

lemma Xh_nonneg : (0:ℝ) ≤ Xh := by unfold Xh V3Log.l3lo; norm_num

lemma Xh_le : (Xh : ℝ) ≤ X0 := by unfold Xh V3Log.l3lo X0; norm_num

lemma dX_spec : |15 * V3Scale.lam - Xh| ≤ (dX : ℝ) := by
  obtain ⟨h1, h2⟩ := V3Scale.lam_bounds
  unfold Xh dX; push_cast
  rw [abs_le]; constructor <;> nlinarith

lemma jP3 (n : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |jP n (15 * V3Scale.lam * s)| ≤ (Bq3 n : ℝ) := by
  have hl := V3Scale.lam_pos
  refine (jP_bound n (by positivity)).trans ?_
  unfold Bq3; push_cast
  have : 15 * V3Scale.lam * s ≤ 33 / 2 := by
    have := lam15; unfold X0 at this; push_cast at this; nlinarith
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) n) (by positivity)

lemma A3_err (n : ℕ) (hn : n < 56) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n (15 * V3Scale.lam * s) - A3 n s| ≤ (eTq3 n : ℝ) := by
  have hl := V3Scale.lam_pos
  have hT := jP_sX 128 Xh 40 96 n (by omega) Xh_nonneg (by
    have := Xh_le; unfold X0 at this; push_cast at this ⊢; linarith) h0 h1
  have hL := jP_lip n (x := 15 * V3Scale.lam * s) (y := (Xh : ℝ) * s) (X0 := (X0 : ℝ)) (by positivity)
    (mul_nonneg Xh_nonneg h0) (by nlinarith [lam15]) (by nlinarith [Xh_le, Xh_nonneg])
  have hd : |15 * V3Scale.lam * s - (Xh : ℝ) * s| ≤ dX := by
    rw [← sub_mul, abs_mul, abs_of_nonneg h0]
    calc |15 * V3Scale.lam - Xh| * s ≤ dX * 1 := mul_le_mul dX_spec h1 h0 ((abs_nonneg _).trans dX_spec)
      _ = dX := by ring
  have hLip : ((2 * n * (X0 : ℝ) ^ (n - 1) + 2 * (X0 : ℝ) ^ n) / (2 ^ (n + 1) * n.factorial))
      = ((Lip n : ℚ) : ℝ) := by unfold Lip; push_cast; ring
  rw [hLip] at hL
  have hL0 : (0:ℝ) ≤ Lip n := by unfold Lip X0; positivity
  unfold eTq3 A3; push_cast
  calc |jP n (15 * V3Scale.lam * s) - jAX 128 Xh 40 96 n s|
      ≤ |jP n (15 * V3Scale.lam * s) - jP n ((Xh : ℝ) * s)| + |jP n ((Xh : ℝ) * s) - jAX 128 Xh 40 96 n s| :=
        abs_sub_le _ _ _
    _ ≤ (Lip n : ℝ) * dX + eTX 128 Xh 40 96 n := add_le_add (hL.trans (mul_le_mul_of_nonneg_left hd hL0)) hT
    _ = _ := by ring

lemma eT3_nonneg (n : ℕ) (hn : n < 56) : (0:ℝ) ≤ eTq3 n :=
  (abs_nonneg _).trans (A3_err n hn (s := 0) le_rfl zero_le_one)

lemma JJ3_err (n m : ℕ) (hn : n < 56) (hm : m < 56) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s) - A3 n s * A3 m s| ≤ (eJ3 n m : ℝ) := by
  have a := jP3 n h0 h1; have b := jP3 m h0 h1
  have ea := A3_err n hn h0 h1; have eb := A3_err m hm h0 h1
  have hb : |A3 m s| ≤ (Bq3 m : ℝ) + eTq3 m := by
    have := abs_sub_abs_le_abs_sub (A3 m s) (jP m (15 * V3Scale.lam * s)); rw [abs_sub_comm] at eb
    linarith [abs_sub_comm (A3 m s) (jP m (15 * V3Scale.lam * s))]
  have e : jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s) - A3 n s * A3 m s
      = jP n (15 * V3Scale.lam * s) * (jP m (15 * V3Scale.lam * s) - A3 m s)
        + A3 m s * (jP n (15 * V3Scale.lam * s) - A3 n s) := by ring
  rw [e]; unfold eJ3; push_cast
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul a eb (abs_nonneg _) ((abs_nonneg _).trans a))
    (mul_le_mul hb ea (abs_nonneg _) ((abs_nonneg _).trans hb))

lemma AA3_eq (n m : ℕ) (s : ℝ) : A3 n s * A3 m s =
    ∑ k ∈ range 40, ∑ l ∈ range 40, ((q3 n k : ℚ) : ℝ) * ((q3 m l : ℚ) : ℝ) * s ^ (n + m + 2 * k + 2 * l) := by
  unfold A3 jAX q3
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

lemma A3_cont (n : ℕ) : Continuous (A3 n) := by
  unfold A3 jAX; fun_prop

lemma model_piece3 (p n m : ℕ) (a b : ℚ) :
    ∫ s in (a:ℝ)..b, Wp p s * (A3 n s * A3 m s) = ∑ k ∈ range 40, ∑ l ∈ range 40,
      ((q3 n k : ℚ) : ℝ) * ((q3 m l : ℚ) : ℝ) *
        ((pmom 2 GD (n + m + 2 * k + 2 * l) a b : ℝ) - (pmom 1 (LD p) (n + m + 2 * k + 2 * l) a b : ℝ)) := by
  simp_rw [AA3_eq, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable; apply continuous_finsetSum; intro l _
    exact (Wp_cont p).mul (continuous_const.mul (continuous_pow _)))]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
    apply Continuous.intervalIntegrable; exact (Wp_cont p).mul (continuous_const.mul (continuous_pow _)))]
  refine sum_congr rfl fun l _ => ?_
  rw [← mom_piece, ← intervalIntegral.integral_const_mul]
  congr 1; funext s; ring

lemma jj3_cont (n m : ℕ) : Continuous (fun s : ℝ => jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)) :=
  ((WeilPlanch.jP_cont n).comp (continuous_const.mul continuous_id)).mul
    ((WeilPlanch.jP_cont m).comp (continuous_const.mul continuous_id))

lemma piece_err3 (p n m : ℕ) (hp : p < 128) (hn : n < 56) (hm : m < 56) :
    |(∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)))
      - ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), Wp p s * (A3 n s * A3 m s)|
      ≤ (εw : ℝ) * (∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ),
          |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)|)
        + 56 * (eJ3 n m : ℝ) / 128 := by
  have hab : ((al p : ℚ) : ℝ) ≤ ((be p : ℚ) : ℝ) := by rw [al_cast, be_cast]; linarith
  have i1 : IntervalIntegrable (fun s : ℝ => wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)))
      MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) := (f_cont.mul (jj3_cont n m)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s : ℝ => Wp p s * (A3 n s * A3 m s))
      MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) :=
    ((Wp_cont p).mul ((A3_cont n).mul (A3_cont m))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub i1 i2]
  have hg : ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ),
        ((εw : ℝ) * |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)| + 56 * (eJ3 n m : ℝ))
      = (εw : ℝ) * (∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ),
          |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)|)
        + 56 * (eJ3 n m : ℝ) / 128 := by
    have j1 : IntervalIntegrable (fun s : ℝ => (εw : ℝ) * |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)|)
        MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) :=
      (continuous_const.mul (jj3_cont n m).abs).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun _ : ℝ => 56 * (eJ3 n m : ℝ))
        MeasureTheory.volume ((al p : ℚ) : ℝ) ((be p : ℚ) : ℝ) := intervalIntegrable_const
    rw [intervalIntegral.integral_add j1 j2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      al_cast, be_cast, smul_eq_mul]
    ring
  rw [← hg, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (MeasureTheory.ae_of_all _ fun s hs => ?_)
    ((continuous_const.mul (jj3_cont n m).abs).add continuous_const |>.intervalIntegrable _ _)
  rw [al_cast, be_cast] at hs
  have hNP : ((CmW.NP : ℕ) : ℝ) = 128 := by norm_num [CmW.NP]
  have h1 : (p : ℝ) / CmW.NP ≤ s := by rw [hNP]; exact hs.1.le
  have h2 : s ≤ ((p : ℝ) + 1) / CmW.NP := by rw [hNP]; exact hs.2
  have hp' : (p : ℝ) + 1 ≤ 128 := by exact_mod_cast hp
  have s0 : 0 ≤ s := le_trans (by positivity) hs.1.le
  have s1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by norm_num)]; exact hp')
  have hw := w_data p (by simpa [CmW.NP] using hp) h1 h2
  have hf := wψ_bound (t := 30 * s) (by linarith) (by linarith)
  have hJ := JJ3_err n m hn hm s0 s1
  have hW : |Wp p s| ≤ 56 := by
    unfold Wp; have := abs_sub_abs_le_abs_sub (wψ (30 * s)) (hev GD (s ^ 2) - hev (LD p) s)
    have := abs_sub_comm (wψ (30 * s)) (hev GD (s ^ 2) - hev (LD p) s)
    have := abs_sub_abs_le_abs_sub (hev GD (s ^ 2) - hev (LD p) s) (wψ (30 * s))
    have : (εw : ℝ) ≤ 1 := by norm_num [εw]
    linarith
  have e : wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)) - Wp p s * (A3 n s * A3 m s)
      = (wψ (30 * s) - Wp p s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s))
        + Wp p s * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s) - A3 n s * A3 m s) := by ring
  rw [Real.norm_eq_abs, e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (wψ (30 * s) - Wp p s), abs_mul (Wp p s)]
  have hw' : |wψ (30 * s) - Wp p s| ≤ εw := by unfold Wp; exact hw
  have hε0 : (0:ℝ) ≤ εw := by norm_num [εw]
  exact add_le_add (mul_le_mul hw' le_rfl (abs_nonneg _) hε0) (mul_le_mul hW hJ (abs_nonneg _) (by norm_num))

/-- exact model quadrature value -/
noncomputable def Ih3 (n m : ℕ) : ℝ := ∑ k ∈ range 40, ∑ l ∈ range 40,
  ((q3 n k : ℚ) : ℝ) * ((q3 m l : ℚ) : ℝ) *
    (((mG ((n + m) / 2 + k + l) : ℚ) : ℝ) - ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ))

lemma Ih3_eq (n m : ℕ) (hpar : (n + m) % 2 = 0) :
    ∑ p ∈ range 128, ∫ s in ((al p : ℚ) : ℝ)..((be p : ℚ) : ℝ), Wp p s * (A3 n s * A3 m s) = Ih3 n m := by
  simp_rw [model_piece3]
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

theorem I3_err (n m : ℕ) (hn : n < 56) (hm : m < 56) (hpar : (n + m) % 2 = 0) :
    |(∫ s in (0:ℝ)..1, wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s))) - Ih3 n m|
      ≤ (εw : ℝ) * (∫ s in (0:ℝ)..1, |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)|)
        + 56 * (eJ3 n m : ℝ) := by
  rw [← adj (fun s => wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)))
      (f_cont.mul (jj3_cont n m)),
    ← adj (fun s => |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)|) (jj3_cont n m).abs,
    ← Ih3_eq n m hpar, ← sum_sub_distrib, Finset.mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : (56 * (eJ3 n m : ℝ)) = ∑ p ∈ range 128, 56 * (eJ3 n m : ℝ) / 128 := by
    rw [sum_const, card_range]; simp; ring
  rw [this, ← sum_add_distrib]
  exact sum_le_sum fun p hp => piece_err3 p n m (mem_range.1 hp) hn hm

end V3Asm
