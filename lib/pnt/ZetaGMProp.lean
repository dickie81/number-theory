/-
# Guth–Maynard at `q = 1`: their Proposition 3.1 for separated points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Chen–Gupta–Li's Proposition 3.1 at one point per character is `LinnikCGLS3.prop31_pt`: `prop31_of_third` with
`third_of_s23`, `LinnikCGLS2.cgls2` and `LinnikCGLS3.cgls3`. At `q = 1` it is Guth and Maynard's key proposition,
"Let σ ∈ [7/10, 8/10] and ϵ > 0. ... W be a set of T^ϵ-separated points in an interval of length T = N^{6/5} ... Then
we have |W| ≤ TN^{(12−20σ)/5+o_ϵ(1)}." (their Proposition 3.1): for `T = N^{6/5}`, `T^{1/2}N^{3−4σ}` and
`T^{4/3}N^{2−4σ}` are both `TN^{12/5−4σ}`, and `N^{2−2σ}` is at most that for `σ ≤ 4/5`. This file proves it for
points `T^ε` apart (`gm_prop31`), from `ZetaGMS3.gms3` and the three steps below.
* `S₂`. `LinnikCGLS2.s2_main` holds for points at least `1` apart, with the residues `P_H` of the principal Gram
  entries added (`LinnikCGLFrob.resP`). For points `T^ε` apart, `|H(1 + iτ)| ≤ B(1 + T^ε)^{−(K+3)}`
  (`LinnikCGLMellin.exists_H_bound`), so `2N²P_H ≤ 12B²T|R|N^{2−2σ}` once `ε(K + 3) ≥ 1` (`res_term_le`). For
  `N ≤ 5/6`, where `S` may contain `1`, `T ≤ (5/3)^{3/2}` and the crude bound `|G(i, k)| ≤ N + 1` suffices.
* The cubic trace, `X = 3μ₀‖E‖_F² + S₃` with `0 ≤ μ₀ ≤ N`, as in `third_of_s23` (`gm_third`).
* Proposition 3.1, as in `prop31_of_third`: `prop46` and `alg112` for `N ≤ T`, `mvt_case` (now for points at least
  `1` apart) for `N ≥ max(T, 10)`, and for `T < N < 10` at most `2T + 1 ≤ 30` points (`ZetaGMS3.card_le_of_sep`).

Plain statements, with `P_H = Σ_{i≠k}|H(1 + i(t_i − t_k))|²` and points `|t_i| ≤ T` at least `T^ε` apart.
* `resP_le_sep`: for points at least `X ≥ 0` apart, `P_H ≤ |R|²(B(1 + X)^{−(K+3)})²`.
* `rpow_two_sub_ge`: `N^{2−2σ} ≥ 1/2` for `N ≥ 1/2` and `7/10 ≤ σ ≤ 4/5`.
* `res_term_le`: `2N²P ≤ 12B²TrN^{2−2σ}` for `P ≤ r²(B(1 + T^ε)^{−(K+3)})²`, `r ≤ 3T` and `ε(K + 3) ≥ 1`.
* `GMS2`, `gms2`: `‖E‖_F² ≤ C(TN)^εT|R|N^{2−2σ}`.
* `GMThird`, `gm_third`: `X ≤ C(TN)^ε(N³ + T²|R|^{3/2} + T|R|N^{3−2σ} + T|R|²N^{3/2−σ} + T^{9/8}|R|^{29/16}N^{3/2−σ})`.
* `GMProp31`, `gm_prop31`: `|R| ≤ C(TN)^ε(N^{2−2σ} + T^{1/2}N^{3−4σ} + T^{4/3}N^{2−4σ})` for `T^{2/3}/2 ≤ N`.
* `gm_prop31_pt`: `GMProp31`, from `CGLP81` and `CGLT101`.

The file imports `ZetaGMS3.lean`.
-/
import ZetaGMS3

open Complex Real Finset

noncomputable section

namespace ZetaGMProp

open DirichletCharacter LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLFrob LinnikCGLS2 LinnikCGLTrunc
  LinnikCGLJ LinnikCGLT101 ZetaGMS3

/-! ### `S₂` at `q = 1` -/

/-- **The residues for separated points**: with `(1 + |τ|)^{K+3}|H(1 + iτ)| ≤ B`, points at least `X ≥ 0` apart have
`P_H ≤ |R|²(B(1 + X)^{−(K+3)})²`. -/
lemma resP_le_sep {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {K : ℕ}
    {B : ℝ} (hB : ∀ τ : ℝ, (1 + |τ|) ^ (K + 3) * ‖H (1 + τ * I)‖ ≤ B) {X : ℝ} (hX : 0 ≤ X)
    (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → X ≤ |t i - t j|) :
    resP R χ t ≤ (R.card : ℝ) ^ 2 * (B * ((1 + X) ^ (K + 3))⁻¹) ^ 2 := by
  have hterm : ∀ i ∈ R, ∀ k ∈ R, resT χ t i k ≤ (B * ((1 + X) ^ (K + 3))⁻¹) ^ 2 := by
    intro i hi k hk
    unfold resT
    split_ifs with h
    · have hτ := hsep i hi k hk h.1
      have h1 := hB (t i - t k)
      have hpos : 0 < (1 + |t i - t k|) ^ (K + 3) := by positivity
      have h2 : ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ ≤ B * ((1 + |t i - t k|) ^ (K + 3))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]; exact h1
      have hB0 : 0 ≤ B := le_trans (by positivity) h1
      have h3 : B * ((1 + |t i - t k|) ^ (K + 3))⁻¹ ≤ B * ((1 + X) ^ (K + 3))⁻¹ := by
        gcongr
      exact pow_le_pow_left₀ (norm_nonneg _) (h2.trans h3) 2
    · positivity
  calc resP R χ t ≤ ∑ _i ∈ R, ∑ _k ∈ R, (B * ((1 + X) ^ (K + 3))⁻¹) ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hterm i hi k hk
    _ = (R.card : ℝ) ^ 2 * (B * ((1 + X) ^ (K + 3))⁻¹) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- `N^{2−2σ} ≥ 1/2` for `N ≥ 1/2` and `σ ≤ 4/5`: `N^{2−2σ} ≥ 1` for `N ≥ 1`, and `N^{2−2σ} ≥ N` for `N ≤ 1`. -/
lemma rpow_two_sub_ge {N σ : ℝ} (hN : 1 / 2 ≤ N) (hσ : σ ≤ 4 / 5) (hσ1 : 1 / 2 ≤ σ) :
    1 / 2 ≤ N ^ (2 - 2 * σ) := by
  rcases le_total 1 N with h | h
  · have := Real.one_le_rpow h (show (0 : ℝ) ≤ 2 - 2 * σ by linarith)
    linarith
  · have h1 : N ^ (1 : ℝ) ≤ N ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) h (by linarith)
    rw [Real.rpow_one] at h1
    linarith

/-- **The residue term of `s2_main`**: for `T ≥ 1`, `1/2 ≤ N ≤ T`, `1/2 ≤ σ ≤ 4/5`, `0 ≤ r ≤ 3T`,
`ε(K + 3) ≥ 1` and `P ≤ r²(B(1 + T^ε)^{−(K+3)})²`, `2N²P ≤ 12B²TrN^{2−2σ}`: `(1 + T^ε)^{K+3} ≥ T`. -/
lemma res_term_le {r N T σ ε B P : ℝ} {K : ℕ} (hT : 1 ≤ T) (hN : 1 / 2 ≤ N) (hNT : N ≤ T) (hσ : σ ≤ 4 / 5)
    (hσ1 : 1 / 2 ≤ σ) (hr0 : 0 ≤ r) (hr : r ≤ 3 * T) (hεK : 1 ≤ ε * (K + 3))
    (hP : P ≤ r ^ 2 * (B * ((1 + T ^ ε) ^ (K + 3))⁻¹) ^ 2) :
    2 * N ^ 2 * P ≤ 12 * B ^ 2 * (T * r * N ^ (2 - 2 * σ)) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hpow : T ≤ (1 + T ^ ε) ^ (K + 3) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (ε * (K + 3 : ℕ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hT ?_
          push_cast; exact hεK
      _ = (T ^ ε) ^ (K + 3) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      _ ≤ (1 + T ^ ε) ^ (K + 3) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hinv : ((1 + T ^ ε) ^ (K + 3))⁻¹ ≤ T⁻¹ := inv_anti₀ hT0 hpow
  have hP' : P ≤ r ^ 2 * B ^ 2 * (T⁻¹) ^ 2 := by
    refine hP.trans ?_
    rw [mul_pow, ← mul_assoc]
    gcongr
  have hN2 : N ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hN0.le hNT 2
  have hhalf := rpow_two_sub_ge hN hσ hσ1
  have hP0 : 0 ≤ r ^ 2 * B ^ 2 * (T⁻¹) ^ 2 := by positivity
  calc 2 * N ^ 2 * P ≤ 2 * T ^ 2 * (r ^ 2 * B ^ 2 * (T⁻¹) ^ 2) := by
        have : 0 ≤ P ∨ P < 0 := le_or_gt 0 P
        rcases this with h0 | h0
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hN2 (by norm_num)) hP' h0 (by positivity)
        · have : 2 * N ^ 2 * P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
          linarith [mul_nonneg (show (0 : ℝ) ≤ 2 * T ^ 2 by positivity) hP0]
    _ = 2 * r ^ 2 * B ^ 2 := by field_simp
    _ ≤ 2 * (3 * T * r) * B ^ 2 := by
        have : r ^ 2 ≤ 3 * T * r := by nlinarith
        gcongr
    _ = 6 * B ^ 2 * (T * r) := by ring
    _ ≤ 6 * B ^ 2 * (T * r) * (2 * N ^ (2 - 2 * σ)) := by
        have h2 : 1 ≤ 2 * N ^ (2 - 2 * σ) := by linarith
        exact le_mul_of_one_le_right (by positivity) h2
    _ = 12 * B ^ 2 * (T * r * N ^ (2 - 2 * σ)) := by ring

/-- **Their Proposition 6.1 at `q = 1`**, for `T^ε`-separated points: for every `ε > 0` there is `C ≥ 0` such that,
under the conditions of `ZetaGMS3.GMS3`, `‖E‖_F² ≤ C(TN)^ε·T|R|N^{2−2σ}`. -/
def GMS2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    (∀ i ∈ R, ∀ j ∈ R, i ≠ j → T ^ ε ≤ |t i - t j|) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    T ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    frobOff N R χ t ≤ C * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ))

set_option maxHeartbeats 1000000 in
/-- **`GMS2` holds**: for `N > 5/6`, `s2_main` at `δ = min(ε, 1)/16` with `T^{min(ε,1)} ≤ (6/5)^ε(TN)^ε`, and the
residues by `resP_le_sep` and `res_term_le` at `K = ⌈1/ε⌉`; for `N ≤ 5/6`, `T ≤ (5/3)^{3/2}`, at most `3T` points,
and `|G(i, k)| ≤ N + 1 ≤ 2`. -/
theorem gms2 : GMS2 := by
  intro ε hε
  have hη0 : 0 < min ε 1 := lt_min hε one_pos
  have hηε : min ε 1 ≤ ε := min_le_left _ _
  have hδ0 : 0 < min ε 1 / 16 := by positivity
  have hδ1 : min ε 1 / 16 ≤ 1 / 16 := by have := min_le_right ε 1; linarith
  have hC1 := C1_nonneg hδ0 (by linarith)
  have hC2 := C2_nonneg hδ0 (by linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈1 / ε⌉₊ := ⟨_, rfl⟩
  have hεK : 1 ≤ ε * (K + 3) := by
    have := Nat.le_ceil (1 / ε)
    rw [← hK, div_le_iff₀ hε] at this
    nlinarith
  obtain ⟨B, hB0, hB⟩ := exists_H_bound K (S := 1) zero_le_one
  have hB' : ∀ τ : ℝ, (1 + |τ|) ^ (K + 3) * ‖H (1 + τ * I)‖ ≤ B := fun τ => by
    simpa using hB 1 τ (by norm_num)
  refine ⟨(C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε + (12 * B ^ 2 + 24) * 2 ^ ε, by positivity, ?_⟩
  intro ι _ R χ t T N σ S b hsep hT hσ1 hσ2 hN1 hN2 hS hb ht hbig
  have hT0 : 0 < T := by linarith
  have hN12 : 1 / 2 ≤ N := by
    have : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hTε1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hcard := card_le_of_sep R hT0.le (by positivity) hsep ht
  have hr3 : (R.card : ℝ) ≤ 3 * T := by
    have : 2 * T / T ^ ε ≤ 2 * T := div_le_self (by positivity) hTε1
    linarith only [this, hcard, hT]
  have hr0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hW0 : 0 ≤ T * R.card * N ^ (2 - 2 * σ) := by positivity
  have hhalf := rpow_two_sub_ge hN12 hσ2 (by linarith)
  have h2ε : 1 ≤ 2 ^ ε * (T * N) ^ ε := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.one_le_rpow (by nlinarith) hε.le
  have hΦ0 : 0 ≤ (T * N) ^ ε := by positivity
  -- `c·T|R|N^{2−2σ} ≤ c·2^ε(TN)^ε·T|R|N^{2−2σ}`
  have hlift : ∀ c : ℝ, 0 ≤ c → c * (T * R.card * N ^ (2 - 2 * σ)) ≤
      c * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) := fun c hc => by
    have := mul_le_mul_of_nonneg_left h2ε (mul_nonneg hc hW0)
    nlinarith
  have hfin : (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) +
      (12 * B ^ 2 + 24) * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) =
      ((C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε + (12 * B ^ 2 + 24) * 2 ^ ε) * (T * N) ^ ε *
        (T * R.card * N ^ (2 - 2 * σ)) := by ring
  rw [← hfin]
  have hA0 : 0 ≤ (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε * (T * N) ^ ε *
      (T * R.card * N ^ (2 - 2 * σ)) := by positivity
  rcases le_or_gt N (5 / 6) with hN56 | hN56
  · -- the crude bound
    have hG : ∀ i k, ‖gramP N χ t i k‖ ^ 2 ≤ 4 := fun i k => by
      have := norm_gramP_le hN0 χ t i k
      nlinarith [norm_nonneg (gramP N χ t i k)]
    have hF : frobOff N R χ t ≤ (R.card : ℝ) ^ 2 * 4 := by
      unfold frobOff
      calc ∑ i ∈ R, ∑ k ∈ R, (if i = k then 0 else ‖gramP N χ t i k‖ ^ 2) ≤ ∑ _i ∈ R, ∑ _k ∈ R, (4 : ℝ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by split_ifs <;> [norm_num; exact hG i k]
        _ = (R.card : ℝ) ^ 2 * 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have h1 : (R.card : ℝ) ^ 2 * 4 ≤ 24 * (T * R.card * N ^ (2 - 2 * σ)) := by
      have h3 : (R.card : ℝ) ^ 2 ≤ 3 * T * R.card := by nlinarith
      have h4 : 3 * T * R.card * 4 ≤ 24 * (T * R.card * N ^ (2 - 2 * σ)) := by
        have := mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 24 * T * R.card by positivity)
        nlinarith
      nlinarith
    have h5 := hlift 24 (by norm_num)
    have h6 : 24 * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) ≤
        (12 * B ^ 2 + 24) * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) := by
      have : (0 : ℝ) ≤ 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) := by positivity
      nlinarith [sq_nonneg B]
    linarith
  · have hsep1 : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j| := fun i hi j hj hij _ =>
      hTε1.trans (hsep i hi j hj hij)
    have h := s2_main hsep1 hT hN56 (by rw [Nat.cast_one, one_mul]; exact hN2) hS hb ht hbig hδ0 hδ1
    simp only [Nat.cast_one, one_mul] at h
    -- the main term
    have hPN : T ≤ 6 / 5 * (T * N) := by
      have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 6 / 5 * N by linarith only [hN56]) hT0.le
      linarith only [h]
    have hpow : T ^ (16 * (min ε 1 / 16)) ≤ (6 / 5) ^ ε * (T * N) ^ ε := by
      rw [show 16 * (min ε 1 / 16) = min ε 1 by ring]
      calc T ^ min ε 1 ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT hηε
        _ ≤ (6 / 5 * (T * N)) ^ ε := Real.rpow_le_rpow hT0.le hPN hε.le
        _ = (6 / 5) ^ ε * (T * N) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
    have hm : (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (T * T ^ (16 * (min ε 1 / 16))) *
        (R.card * N ^ (2 - 2 * σ)) ≤ (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε * (T * N) ^ ε *
          (T * R.card * N ^ (2 - 2 * σ)) := by
      calc (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (T * T ^ (16 * (min ε 1 / 16))) *
            (R.card * N ^ (2 - 2 * σ)) ≤ (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) *
            (T * ((6 / 5) ^ ε * (T * N) ^ ε)) * (R.card * N ^ (2 - 2 * σ)) := by gcongr
        _ = _ := by ring
    -- the residues
    have hres := resP_le_sep R χ t hB' (by positivity) hsep
    have hrt := res_term_le hT hN12 hN2 hσ2 (by linarith) hr0 hr3 hεK hres
    have h7 := hlift (12 * B ^ 2) (by positivity)
    have h8 : 12 * B ^ 2 * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) ≤
        (12 * B ^ 2 + 24) * 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) := by
      have : (0 : ℝ) ≤ 2 ^ ε * (T * N) ^ ε * (T * R.card * N ^ (2 - 2 * σ)) := by positivity
      nlinarith
    linarith

/-! ### The cubic trace at `q = 1` -/

/-- **The bound on the cubic trace at `q = 1`**, for `T^ε`-separated points: for every `ε > 0` there is `C ≥ 0` such
that, under the conditions of `GMS2`,
`X ≤ C(TN)^ε(N³ + T²|R|^{3/2} + T|R|N^{3−2σ} + T|R|²N^{3/2−σ} + T^{9/8}|R|^{29/16}N^{3/2−σ})`. -/
def GMThird : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    (∀ i ∈ R, ∀ j ∈ R, i ≠ j → T ^ ε ≤ |t i - t j|) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    T ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    X3 N R χ t ≤ C * (T * N) ^ ε * (N ^ 3 + T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) + T * R.card * N ^ (3 - 2 * σ) +
      T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) + T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))

/-- **`GMThird` from `GMS2` and `GMS3`**: `X = 3μ₀‖E‖_F² + S₃` with `0 ≤ μ₀ ≤ N`, as in `third_of_s23`. -/
theorem gm_third (h2 : GMS2) (h3 : ZetaGMS3.GMS3) : GMThird := by
  intro ε hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := h2 ε hε
  obtain ⟨C₃, hC₃0, hC₃⟩ := h3 ε hε
  refine ⟨3 * C₂ + C₃, by positivity, ?_⟩
  intro ι _ R χ t T N σ S b hsep hT hσ1 hσ2 hN hNq hS hb ht hbig
  have hN0 : 0 < N := by
    have : (1 : ℝ) ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
    linarith
  have hF := hC₂ R χ t T N σ S b hsep hT hσ1 hσ2 hN hNq hS hb ht hbig
  have h3' := hC₃ R χ t T N σ S b hsep hT hσ1 hσ2 hN hNq hS hb ht hbig
  have hF0 := frobOff_nonneg N R χ t
  have hm0 := mu0_nonneg 1 hN0.le
  have hm1 := mu0_le 1 hN0.le
  set E := (T * N) ^ ε with hE
  have hE0 : 0 ≤ E := by positivity
  set A := T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) with hA
  set B := T * R.card * N ^ (3 - 2 * σ) with hB
  set Cc := T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) with hCc
  set D := T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) with hD
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hCc0 : 0 ≤ Cc := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hN3 : 0 ≤ N ^ 3 := by positivity
  have hNB : N * (T * R.card * N ^ (2 - 2 * σ)) = B := by
    rw [hB, show (3 - 2 * σ) = 1 + (2 - 2 * σ) by ring, Real.rpow_add hN0, Real.rpow_one]; ring
  have hS2 : 3 * mu0 1 N * frobOff N R χ t ≤ 3 * C₂ * E * B := by
    calc 3 * mu0 1 N * frobOff N R χ t ≤ 3 * N * (C₂ * E * (T * R.card * N ^ (2 - 2 * σ))) := by
          gcongr
      _ = 3 * C₂ * E * (N * (T * R.card * N ^ (2 - 2 * σ))) := by ring
      _ = 3 * C₂ * E * B := by rw [hNB]
  have hX : X3 N R χ t = 3 * mu0 1 N * frobOff N R χ t + S3 1 N R χ t := by unfold S3; ring
  rw [hX]
  calc 3 * mu0 1 N * frobOff N R χ t + S3 1 N R χ t ≤ 3 * C₂ * E * B + C₃ * E * (A + B + Cc + D) :=
        add_le_add hS2 h3'
    _ ≤ (3 * C₂ + C₃) * E * (N ^ 3 + A + B + Cc + D) := by
        have h1 : 3 * C₂ * E * B ≤ 3 * C₂ * E * (N ^ 3 + A + B + Cc + D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : C₃ * E * (A + B + Cc + D) ≤ C₃ * E * (N ^ 3 + A + B + Cc + D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith

/-! ### Their Proposition 3.1 at `q = 1` -/

/-- **Their Proposition 3.1 at `q = 1`** (Guth and Maynard's key proposition), for `T^ε`-separated points: for every
`ε > 0` there is `C ≥ 0` such that, for `T ≥ 1`, `7/10 ≤ σ ≤ 4/5`, `T^{2/3}/2 ≤ N`, `S ⊆ [6N/5, 9N/5]`,
`|b_n| ≤ 1` and points `|t_i| ≤ T` at least `T^ε` apart with `|Σ_{n∈S}b_nn^{it_i}| ≥ N^σ/6`,
`|R| ≤ C(TN)^ε(N^{2−2σ} + T^{1/2}N^{3−4σ} + T^{4/3}N^{2−4σ})`. -/
def GMProp31 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    (∀ i ∈ R, ∀ j ∈ R, i ≠ j → T ^ ε ≤ |t i - t j|) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    T ^ (2 / 3 : ℝ) / 2 ≤ N → (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) →
    (∀ i ∈ R, |t i| ≤ T) → (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    (R.card : ℝ) ≤ C * (T * N) ^ ε *
      (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ))

/-- **`GMProp31` from the bound on the cubic trace**, as `prop31_of_third`: for `N ≤ T`, `prop46` and `alg112` with
`K = max(C(TN)^{ε₁}, 1)`, `ε₁ = min(ε, 1)`; for `N ≥ max(T, 10)`, the mean value theorem (`mvt_case`, `polylog_le`);
for `T < N < 10`, at most `30` points. -/
theorem gm_prop31 (h : GMThird) : GMProp31 := by
  intro ε hε
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := h ε₁ hε₁0
  obtain ⟨Cm, hCm⟩ : ∃ x : ℝ, x = (11 + 24 / ε₁) * (2 + 36 / ε₁ ^ 2) := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  obtain ⟨Ctot, hCtot⟩ : ∃ x : ℝ, x = 10 * 216 ^ 3 * max C 1 + 36 * Cm + 30 := ⟨_, rfl⟩
  have hC1 : 1 ≤ max C 1 := le_max_right _ _
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; linarith
  refine ⟨2 ^ ε * Ctot, mul_nonneg (by positivity) hCtot0, ?_⟩
  intro ι R χ t T N σ S b hsep hT hσ1 hσ2 hN hS hb ht hbig
  classical
  have hN12 : 1 / 2 ≤ N := by
    have : (1 : ℝ) ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hT0 : 0 < T := by linarith
  have hTε : T ^ ε₁ ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT hε₁ε
  have hsep₁ : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → T ^ ε₁ ≤ |t i - t j| := fun i hi j hj hij =>
    hTε.trans (hsep i hi j hj hij)
  have hb1 : 0 ≤ N ^ (2 - 2 * σ) := by positivity
  have hb2 : 0 ≤ T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have hb3 : 0 ≤ T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  have hP : 0 < T * N := by positivity
  have hP2 : 1 ≤ 2 * (T * N) := by nlinarith
  set E := 2 ^ ε * (T * N) ^ ε with hE
  have hE1 : 1 ≤ E := by
    rw [hE, ← Real.mul_rpow (by norm_num) hP.le]; exact Real.one_le_rpow hP2 hε.le
  have hpow1 : (T * N) ^ ε₁ ≤ E := by
    rcases le_total 1 (T * N) with h1 | h1
    · calc (T * N) ^ ε₁ ≤ (T * N) ^ ε := Real.rpow_le_rpow_of_exponent_le h1 hε₁ε
        _ ≤ E := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) hε.le)
    · calc (T * N) ^ ε₁ ≤ 1 := Real.rpow_le_one hP.le h1 hε₁0.le
        _ ≤ E := hE1
  -- the final form
  have hfin : ∀ c : ℝ, 0 ≤ c → c ≤ Ctot → c * E * (N ^ (2 - 2 * σ) +
      T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) ≤
      2 ^ ε * Ctot * (T * N) ^ ε * (N ^ (2 - 2 * σ) +
      T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
    intro c hc0 hc
    have hB0 : 0 ≤ N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by
      positivity
    have hE0 : 0 ≤ E := by linarith
    calc c * E * _ ≤ Ctot * E * _ := by gcongr
      _ = _ := by rw [hE]; ring
  rcases le_or_gt N T with hNq | hNq
  · -- `N ≤ T`: the cubic trace
    have hX := hC R χ t T N σ S b hsep₁ hT hσ1 hσ2 hN hNq hS hb ht hbig
    have h46 := prop46 R χ t hN12 hS hb hbig
    set K := max (C * (T * N) ^ ε₁) 1 with hK
    have hK1 : 1 ≤ K := le_max_right _ _
    have hXK : X3 N R χ t ≤ K * (N ^ 3 + T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
        T * R.card * N ^ (3 - 2 * σ) + T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
        T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)) :=
      hX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hr := alg112 (Nat.cast_nonneg R.card) hN0 hT hσ1 hσ2 hK1 h46 hXK
    have hKE : K ≤ max C 1 * E := by
      rw [hK]
      apply max_le
      · exact mul_le_mul (le_max_left _ _) hpow1 (by positivity) (by positivity)
      · calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ max C 1 * E := mul_le_mul hC1 hE1 zero_le_one (by positivity)
    calc (R.card : ℝ) ≤ 5 * 216 ^ 3 * K * (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := hr
      _ ≤ 5 * 216 ^ 3 * max C 1 * E * (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
          rw [mul_assoc (5 * 216 ^ 3) (max C 1) E]
          gcongr
      _ ≤ _ := hfin _ (by positivity) (by rw [hCtot]; linarith)
  · rcases le_or_gt 10 N with hN10 | hN10
    · -- `N ≥ max(T, 10)`: the mean value theorem
      have hsep1 : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j| := fun i hi j hj hij _ =>
        (Real.one_le_rpow hT hε.le).trans (hsep i hi j hj hij)
      have hm := mvt_case R χ t hsep1 hT (by rw [Nat.cast_one, one_mul]; exact hNq.le) hN10 hS hb ht hbig
      have hpl := polylog_le (by linarith : (1 : ℝ) ≤ N) hε₁0 hε₁1
      rw [← hCm] at hpl
      have e : N ^ (2 - 2 * σ) = N ^ 2 / (N ^ σ) ^ 2 := by
        rw [LinnikCGLLV.npow_div_rpow_pow hN0 2 2 σ]; norm_num
      have h1 : (R.card : ℝ) ≤ 36 * Cm * N ^ ε₁ * N ^ (2 - 2 * σ) := by
        rw [e, show 36 * Cm * N ^ ε₁ * (N ^ 2 / (N ^ σ) ^ 2) = 36 * Cm * N ^ ε₁ * N ^ 2 / (N ^ σ) ^ 2 by ring,
          le_div_iff₀ (by positivity)]
        calc (R.card : ℝ) * (N ^ σ) ^ 2
            ≤ 36 * N ^ 2 * ((11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2)) := hm
          _ ≤ 36 * N ^ 2 * (Cm * N ^ ε₁) := by gcongr
          _ = 36 * Cm * N ^ ε₁ * N ^ 2 := by ring
      have h2 : N ^ ε₁ ≤ E :=
        le_trans (Real.rpow_le_rpow hN0.le (le_mul_of_one_le_left hN0.le hT) hε₁0.le) hpow1
      calc (R.card : ℝ) ≤ 36 * Cm * N ^ ε₁ * N ^ (2 - 2 * σ) := h1
        _ ≤ 36 * Cm * E * (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
            T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
            gcongr
            linarith
        _ ≤ _ := hfin _ (by positivity) (by rw [hCtot]; linarith)
    · -- `T < N < 10`: at most `30` points
      have hcard := card_le_of_sep R hT0.le (by positivity) hsep ht
      have hTε1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
      have hR30 : (R.card : ℝ) ≤ 30 := by
        have : 2 * T / T ^ ε ≤ 2 * T := div_le_self (by positivity) hTε1
        linarith only [this, hcard, hNq, hN10]
      have hN1 : 1 ≤ N := by linarith
      have hNB : 1 ≤ N ^ (2 - 2 * σ) := Real.one_le_rpow hN1 (by linarith)
      have hEB : 1 ≤ E * (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) :=
        one_le_mul_of_one_le_of_one_le hE1 (by linarith)
      calc (R.card : ℝ) ≤ 30 * E * (N ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
            T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by rw [mul_assoc]; linarith
        _ ≤ _ := hfin _ (by norm_num) (by rw [hCtot]; linarith)

/-- **Guth and Maynard's key proposition at `q = 1`**, from their Proposition 8.1 (`CGLP81`) and Heath-Brown's
Theorem 10.1 (`CGLT101`): `gm_prop31` with `gm_third`, `gms2` and `ZetaGMS3.gms3`. -/
theorem gm_prop31_pt (hP : CGLP81) (hT : CGLT101) : GMProp31 :=
  gm_prop31 (gm_third gms2 (gms3 hP hT))

end ZetaGMProp

#print axioms ZetaGMProp.resP_le_sep
#print axioms ZetaGMProp.res_term_le
#print axioms ZetaGMProp.gms2
#print axioms ZetaGMProp.gm_third
#print axioms ZetaGMProp.gm_prop31
#print axioms ZetaGMProp.gm_prop31_pt
