import Mathlib
import V3Enc
import V3Pole
import WeilCoer

/-! # Weil positivity on Connes–Consani's subspace `V'` at support `log 3 / 2`, on rescaled Legendre mode sums

`f = sc (hx N x y)` is supported in `[−L*, L*]`, `L* = log 3 / 2`. On `V'` (`∫ f e^{±u/2} = 0`, `∫ f = 0`):

  `weilQg L* f ≥ 4·10⁻⁴ ‖f‖²`  (`vprime_hx`).

The even sector uses the two constraints `x₀ = 0` and `Σ xᵢ p̃₂ᵢ = 0` (`V3Pole`): there the Zhu-reduced matrix augmented
by `1000·(p̃p̃ᵀ + e₀e₀ᵀ)` is the reduced form itself, and its head has a kernel-checked LDLᵀ certificate at `δ = 1/40`
(`even_chk3`, smallest eigenvalue of the centre about `0.0286`), so the even form is at least `‖x‖²/50`. The odd
sector needs no constraint: its reduced head has a certificate at `δ = 4.5·10⁻⁴` (`odd_chk3`, smallest eigenvalue
about `4.75·10⁻⁴`). The entries `C3` come from `V3Enc` (to `3·10⁻⁹`), `β*` from `WeilConst.beta_enc_even` (to
`10⁻¹²`), the pole vector from `V3Pole.pole3_enc` (to `10⁻¹²`), and the tail from `V3Zhu.sector_margin3`. -/

namespace V3Main

open Real Finset WeilTail WeilTailB V3Scale V3Zhu V3Fin V3Cert

/-- The rational centre of the augmented head: `b̂·I + μp·p̂p̂ᵀ + μ0·e₀e₀ᵀ + ĉ`. -/
def Aq3 (μp μ0 bq : ℚ) (pq : List ℚ) (cq : List (List ℚ)) (i j : ℕ) : ℚ :=
  (if i = j then bq else 0) + μp * pq.getD i 0 * pq.getD j 0 + (if i = 0 ∧ j = 0 then μ0 else 0) + cs cq i j

/-- `|A − (MᵀDM + δI)| ≤ r` entrywise on the head, and `D ≥ 0`. -/
def chk3 (Mq : List (List ℚ)) (Dq : List ℚ) (δ μp μ0 bq : ℚ) (pq : List ℚ) (cq : List (List ℚ)) (r : ℚ) : Bool :=
  ((List.range 28).all fun i => (List.range 28).all fun j =>
    decide (Aq3 μp μ0 bq pq cq i j - WeilHead.certq Mq Dq δ i j ≤ r) &&
      decide (WeilHead.certq Mq Dq δ i j - Aq3 μp μ0 bq pq cq i j ≤ r)) && Dq.all (fun d => decide (0 ≤ d))

theorem even_chk3 : chk3 MqE DqE (1 / 40) 1000 1000 WeilHead.EvenQ.bq pqE cqE
    (1 / 10 ^ 8 - (1 / 10 ^ 12 + 1000 * (5 * (1 / 10 ^ 12)) + 3 / 10 ^ 9)) = true := by decide +kernel

theorem odd_chk3 : chk3 MqO DqO (45 / 10 ^ 5) 0 0 WeilHead.EvenQ.bq [] cqO
    (1 / 10 ^ 8 - (1 / 10 ^ 12 + 0 + 3 / 10 ^ 9)) = true := by decide +kernel

theorem pq_small : ((List.range 28).all fun i => decide (|pqE.getD i 0| ≤ 2)) = true := by decide +kernel

lemma chk3_spec {Mq Dq δ μp μ0 bq pq cq r} (h : chk3 Mq Dq δ μp μ0 bq pq cq r = true) :
    (∀ i < 28, ∀ j < 28, |((Aq3 μp μ0 bq pq cq i j : ℚ) : ℝ) - ((WeilHead.certq Mq Dq δ i j : ℚ) : ℝ)| ≤ (r : ℝ))
      ∧ ∀ k, (0:ℝ) ≤ ((Dq.getD k 0 : ℚ) : ℝ) := by
  unfold chk3 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi j hj => ?_, fun k => by exact_mod_cast WeilTail.getD_nonneg Dq h2 k⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h1 i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [abs_sub_le_iff]; constructor <;> [exact_mod_cast this.1; exact_mod_cast this.2]

/-- The augmented head is within `εb + εpp + εc` of its rational centre. -/
lemma R3_near (par : ℕ) (μp μ0 bq : ℚ) (pq : List ℚ) (cq : List (List ℚ)) {εb εpp εc : ℝ}
    (hb : |βs - (bq : ℝ)| ≤ εb)
    (hpp : ∀ i < 28, ∀ j < 28, |(μp : ℝ) * pole3 (2 * i + par) * pole3 (2 * j + par)
      - (μp : ℝ) * ((pq.getD i 0 : ℚ) : ℝ) * ((pq.getD j 0 : ℚ) : ℝ)| ≤ εpp)
    (hc : ∀ i < 28, ∀ j < 28, |C3 (2 * i + par) (2 * j + par) - ((cs cq i j : ℚ) : ℝ)| ≤ εc)
    {i j : ℕ} (hi : i < 28) (hj : j < 28) :
    |R3 par μp μ0 i j - ((Aq3 μp μ0 bq pq cq i j : ℚ) : ℝ)| ≤ εb + εpp + εc := by
  have hεb : (0:ℝ) ≤ εb := (abs_nonneg _).trans hb
  have hβ : |(if i = j then βs else 0) - (if i = j then (bq : ℝ) else 0)| ≤ εb := by
    split_ifs
    · exact hb
    · simp [hεb]
  have key : R3 par μp μ0 i j - ((Aq3 μp μ0 bq pq cq i j : ℚ) : ℝ)
      = ((if i = j then βs else 0) - (if i = j then (bq : ℝ) else 0))
        + ((μp : ℝ) * pole3 (2 * i + par) * pole3 (2 * j + par)
          - (μp : ℝ) * ((pq.getD i 0 : ℚ) : ℝ) * ((pq.getD j 0 : ℚ) : ℝ))
        + (C3 (2 * i + par) (2 * j + par) - ((cs cq i j : ℚ) : ℝ)) := by
    unfold R3 Aq3; push_cast [apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero]; ring
  rw [key]
  refine (abs_add_three _ _ _).trans ?_
  linarith [hpp i hi j hj, hc i hi j hj]

lemma pp_even : ∀ i < 28, ∀ j < 28, |((1000 : ℚ) : ℝ) * pole3 (2 * i + 0) * pole3 (2 * j + 0)
    - ((1000 : ℚ) : ℝ) * ((pqE.getD i 0 : ℚ) : ℝ) * ((pqE.getD j 0 : ℚ) : ℝ)| ≤ 1000 * (5 * (1 / 10 ^ 12)) := by
  intro i hi j hj
  have ps := List.all_eq_true.1 pq_small
  have ha' : |((pqE.getD i 0 : ℚ) : ℝ)| ≤ 2 := by
    have := of_decide_eq_true (ps i (List.mem_range.2 hi)); exact_mod_cast this
  have hb' : |((pqE.getD j 0 : ℚ) : ℝ)| ≤ 2 := by
    have := of_decide_eq_true (ps j (List.mem_range.2 hj)); exact_mod_cast this
  have ha := V3Pole.pole3_enc i hi
  have hb := V3Pole.pole3_enc j hj
  simp only [add_zero]
  set a := pole3 (2 * i); set b := pole3 (2 * j)
  set a' := ((pqE.getD i 0 : ℚ) : ℝ); set b' := ((pqE.getD j 0 : ℚ) : ℝ)
  have hbb : |b| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub b b'; linarith
  have hprod : |a * b - a' * b'| ≤ 5 * (1 / 10 ^ 12) := by
    rw [show a * b - a' * b' = (a - a') * b + a' * (b - b') by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg (a - a'), abs_nonneg (b - b'), abs_nonneg b, abs_nonneg a']
  rw [show ((1000 : ℚ) : ℝ) * a * b - ((1000 : ℚ) : ℝ) * a' * b' = 1000 * (a * b - a' * b') by push_cast; ring,
    abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1000)]
  linarith

theorem head_even : ∀ i < 28, ∀ j < 28, |R3 0 1000 1000 i j - certMat 28
    (fun k i => if _h : k < 28 ∧ i < 28 then ((getq MqE k i : ℚ) : ℝ) else 0)
    (fun k => if k < 28 then ((DqE.getD k 0 : ℚ) : ℝ) else 0) (((1 / 40 : ℚ)) : ℝ) i j| ≤ 1 / 10 ^ 8 := by
  intro i hi j hj
  have h1 := R3_near 0 1000 1000 WeilHead.EvenQ.bq pqE cqE WeilConst.beta_enc_even pp_even V3Fin.c3Enc_even hi hj
  have h2 := (chk3_spec even_chk3).1 i hi j hj
  rw [WeilHead.certMat_eq MqE DqE (1 / 40) hi hj]
  have e : R3 0 1000 1000 i j = R3 0 ((1000 : ℚ) : ℝ) ((1000 : ℚ) : ℝ) i j := by push_cast; rfl
  rw [e]
  calc _ ≤ |R3 0 ((1000 : ℚ) : ℝ) ((1000 : ℚ) : ℝ) i j - ((Aq3 1000 1000 WeilHead.EvenQ.bq pqE cqE i j : ℚ) : ℝ)|
        + |((Aq3 1000 1000 WeilHead.EvenQ.bq pqE cqE i j : ℚ) : ℝ)
          - ((WeilHead.certq MqE DqE (1 / 40) i j : ℚ) : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by push_cast; norm_num

theorem head_odd : ∀ i < 28, ∀ j < 28, |R3 1 0 0 i j - certMat 28
    (fun k i => if _h : k < 28 ∧ i < 28 then ((getq MqO k i : ℚ) : ℝ) else 0)
    (fun k => if k < 28 then ((DqO.getD k 0 : ℚ) : ℝ) else 0) (((45 / 10 ^ 5 : ℚ)) : ℝ) i j| ≤ 1 / 10 ^ 8 := by
  intro i hi j hj
  have h1 := R3_near 1 0 0 WeilHead.EvenQ.bq [] cqO (εpp := 0) WeilConst.beta_enc_even
    (fun i _ j _ => by simp) V3Fin.c3Enc_odd hi hj
  have h2 := (chk3_spec odd_chk3).1 i hi j hj
  rw [WeilHead.certMat_eq MqO DqO (45 / 10 ^ 5) hi hj]
  have e : R3 1 0 0 i j = R3 1 ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) i j := by push_cast; rfl
  rw [e]
  calc _ ≤ |R3 1 ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) i j - ((Aq3 0 0 WeilHead.EvenQ.bq [] cqO i j : ℚ) : ℝ)|
        + |((Aq3 0 0 WeilHead.EvenQ.bq [] cqO i j : ℚ) : ℝ)
          - ((WeilHead.certq MqO DqO (45 / 10 ^ 5) i j : ℚ) : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by push_cast; norm_num

/-- **Even sector**: the augmented reduced form is at least `‖x‖²/50` at every truncation `N ≥ 28`. -/
theorem even_sector (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    (1 / 50 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ qf (R3 0 1000 1000) x (range N) (range N) :=
  sector_margin3 0 (by norm_num) (by norm_num) 1000 _ _ (((1 / 40 : ℚ)) : ℝ) (1 / 10 ^ 8) (1 / 50) (1 / 10 ^ 22) 4605
    (by norm_num) (fun k => by
      by_cases hk : k < 28
      · simp only [ite_eq_left hk]; exact (chk3_spec even_chk3).2 k
      · simp only [ite_eq_right hk]; exact le_rfl)
    (by norm_num) head_even (by simpa using b3_56_le) (by norm_num) (by norm_num) (by norm_num) N hN x

/-- **Odd sector**: the reduced form is at least `4·10⁻⁴‖y‖²` at every truncation `N ≥ 28`. -/
theorem odd_sector (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) :
    (4 / 10 ^ 4 : ℝ) * ∑ i ∈ range N, y i ^ 2 ≤ qf (R3 1 0 0) y (range N) (range N) :=
  sector_margin3 1 le_rfl le_rfl 0 _ _ (((45 / 10 ^ 5 : ℚ)) : ℝ) (1 / 10 ^ 8) (4 / 10 ^ 4) (1 / 10 ^ 22) 605
    (by norm_num) (fun k => by
      by_cases hk : k < 28
      · simp only [ite_eq_left hk]; exact (chk3_spec odd_chk3).2 k
      · simp only [ite_eq_right hk]; exact le_rfl)
    (by norm_num) head_odd (by simpa using b3_57_le) (by norm_num) (by norm_num) (by norm_num) N hN y

lemma QF3_even_V (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) (h0 : x 0 = 0)
    (hp : ∑ i ∈ range N, x i * pole3 (2 * i) = 0) : (1 / 50 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ QF3 0 N x := by
  have h := even_sector N hN x
  rw [qf_R3 0 1000 1000 N (by omega) x] at h
  simp only [add_zero] at h
  rw [hp, h0] at h
  have hq := QF3_ge 0 (WeilPlanch.modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))) N x
  simp only [add_zero] at hq
  nlinarith

lemma QF3_odd (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) : (4 / 10 ^ 4 : ℝ) * ∑ i ∈ range N, y i ^ 2 ≤ QF3 1 N y := by
  have h := odd_sector N hN y
  rw [qf_R3 1 0 0 N (by omega) y] at h
  have hq := QF3_ge 1 (WeilPlanch.modePlancherel_of WeilModes.modeDecay 1 (WeilFourier.modeOrth (by norm_num))) N y
  nlinarith

/-- **Weil positivity on `V'` at support `log 3 / 2`** (rescaled Legendre mode sums `f = sc (hx N x y)`, `N ≥ 28`):
if `∫ f e^{−u/2} = ∫ f e^{u/2} = ∫ f = 0` over `[−L*, L*]`, then `weilQg L* f ≥ 4·10⁻⁴ ‖f‖²`. -/
theorem vprime_hx (N : ℕ) (hN : 28 ≤ N) (x y : ℕ → ℝ)
    (hR : WeilForm.poleR (sc (WeilOdd.hx N x y)) (lam / 2) = 0)
    (hL : WeilForm.poleL (sc (WeilOdd.hx N x y)) (lam / 2) = 0)
    (hI : ∫ u in (-(lam / 2))..(lam / 2), sc (WeilOdd.hx N x y) u = 0) :
    (4 / 10 ^ 4 : ℝ) * WeilForm.normSq (sc (WeilOdd.hx N x y)) ≤ WeilForm.weilQg (lam / 2) (sc (WeilOdd.hx N x y)) := by
  have hs := sqrt_lam_pos
  have hR' := hR; have hL' := hL
  rw [V3Pole.poleR_sc_hx] at hR'
  rw [V3Pole.poleL_sc_hx] at hL'
  rw [V3Pole.int_sc_hx N (by omega)] at hI
  have h1 := (mul_eq_zero.1 hR').resolve_left hs.ne'
  have h2 := (mul_eq_zero.1 hL').resolve_left hs.ne'
  have hA : ∑ i ∈ range N, x i * pole3 (2 * i) = 0 := by linarith
  have h0 : x 0 = 0 := (mul_eq_zero.1 hI).resolve_left hs.ne'
  rw [weilQg_sc, hR, normSq_sc, WeilCoer.normSq_hx]
  have e := QF3_even_V N hN x h0 hA
  have o := QF3_odd N hN y
  have hx2 : 0 ≤ ∑ i ∈ range N, x i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  nlinarith

end V3Main
