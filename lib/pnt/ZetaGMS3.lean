/-
# Guth–Maynard at `q = 1`: their Proposition 11.1 for separated points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`LinnikCGLS3.cgls3` proves Chen–Gupta–Li's Proposition 11.1 at one point per character, "S₃ ⪅ (qT)²|W|^{3/2} +
qT|W|N^{3−2σ} + qT|W|²N^{3/2−σ} + (qT)^{9/8}|W|^{29/16}N^{3/2−σ}" (p. 47). This file proves it at `q = 1` for points
`T^ε` apart (`gms3`), Guth and Maynard's setting: their Proposition 3.1 takes "W a set of T^ε-separated points". The
proof is `cgls3`'s, with three changes.
* The bound (11.2) is `ZetaGMBlock.S3_le_112_one`, in which `S₃,₁ = ∫_{[1/2,2]}|R|²` enters through an upper bound
  `S`. For spaced points `S₃,₁ ≤ 2X(∫ψ̃₀·|R| + |R|²D_K/X^K)` (`ZetaGMBlock.S31_le_one`), at most `S = 2X(∫ψ̃₀ + 1)|R|`
  once `|R|D_K ≤ X^K`. The main term is then `main_le_one`, with `X⁵` in place of `cgls3`'s `X⁴`, so `ε′ ≤ ε/20`.
* The trace at `q = 1` carries the `m = 0` terms of the Gram entries, at most `z = NB(1 + T^ε)^{−(k_z+3)}`
  (`ZetaGMTrace.norm_Zm_le_sep`), at most `BT^{−5/2}` for `ε(k_z + 3) ≥ 7/2`. Their two errors are
  `errors_part_one`.
* The energy is `LinnikCGLEps.prop102` for spaced points: points `T^ε ≥ 3` apart are spaced, and number at most
  `2T/T^ε + 1 ≤ T` (`card_le_of_sep`).

Plain statements, with `Q₁` the threshold of the large range, `r = |R|` and
`W = T²r^{3/2} + TrN^{3−2σ} + Tr²N^{3/2−σ} + T^{9/8}r^{29/16}N^{3/2−σ}`.
* `char_one_isPrimitive`: every character mod `1` is primitive.
* `card_le_of_sep`: points of `[−T, T]` at least `D > 0` apart number at most `2T/D + 1`.
* `sqrt_main_one`, `main_le_one`, `main_part_one`: the main term of (11.2) at `q = 1`, at most `K_m(TN)^εW`.
* `E3_le_one`, `Ez_le_one`, `errors_part_one`: the errors of (11.2) at `q = 1`, at most `K_e(TN)^εW`.
* `small_case_one`: for `T < Q₁` and `r ≤ 3T`, `S₃ ≤ 2^ε(3Q₁)^{3/2}(Q₁ + 1)³(TN)^εT²r^{3/2}` (`S3_le_crude`).
* `GMS3`, `gms3`: the statement, and `CGLP81 → CGLT101 → GMS3`.

The file imports `ZetaGMBlock.lean`.
-/
import ZetaGMBlock

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace ZetaGMS3

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLS23 LinnikCGLDiag LinnikCGLTrunc LinnikCGLP71
  LinnikCGLP72 LinnikCGLRt LinnikCGLMom4 LinnikCGLJ LinnikCGL112 LinnikCGLT101 LinnikCGLCase LinnikCGLEps
  LinnikCGLS3 LinnikCGLL105 LinnikCGLCS ZetaGMTrace ZetaGMBlock

/-! ### Points at `q = 1` -/

/-- Every character mod `1` is primitive: it is `1` (Mathlib's `level_one`). -/
lemma char_one_isPrimitive (χ : DirichletCharacter ℂ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.level_one χ]
  exact DirichletCharacter.isPrimitive_one_level_one

/-- **Separated points are few**: points of `[−T, T]`, `T ≥ 0`, at least `D > 0` apart number at most `2T/D + 1`,
since `i ↦ ⌊(t_i + T)/D⌋` is injective on them. -/
lemma card_le_of_sep {ι : Type*} (R : Finset ι) {t : ι → ℝ} {T D : ℝ} (hT : 0 ≤ T) (hD : 0 < D)
    (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → D ≤ |t i - t j|) (ht : ∀ i ∈ R, |t i| ≤ T) :
    (R.card : ℝ) ≤ 2 * T / D + 1 := by
  classical
  have h1 : R.card ≤ (Finset.range (⌊2 * T / D⌋₊ + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun i => ⌊(t i + T) / D⌋₊) (fun i hi => ?_) (fun i hi j hj hij => ?_)
    · rw [Finset.mem_coe] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      have h := abs_le.mp (ht i hi)
      exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith [h.2]) hD.le))
    · rw [Finset.mem_coe] at hi hj
      by_contra hne
      have hs := hsep i hi j hj hne
      have hi0 : 0 ≤ (t i + T) / D := div_nonneg (by linarith [(abs_le.mp (ht i hi)).1]) hD.le
      have hj0 : 0 ≤ (t j + T) / D := div_nonneg (by linarith [(abs_le.mp (ht j hj)).1]) hD.le
      have a1 := Nat.floor_le hi0
      have a2 := Nat.lt_floor_add_one ((t i + T) / D)
      have b1 := Nat.floor_le hj0
      have b2 := Nat.lt_floor_add_one ((t j + T) / D)
      have hij' : ⌊(t i + T) / D⌋₊ = ⌊(t j + T) / D⌋₊ := hij
      rw [hij'] at a1 a2
      have hlt : |(t i + T) / D - (t j + T) / D| < 1 := by rw [abs_lt]; constructor <;> linarith
      have hD' : D ≠ 0 := hD.ne'
      have e : t i - t j = D * ((t i + T) / D - (t j + T) / D) := by field_simp; ring
      have hlt' : |t i - t j| < D := by
        rw [e, abs_mul, abs_of_pos hD]
        calc D * |(t i + T) / D - (t j + T) / D| < D * 1 := mul_lt_mul_of_pos_left hlt hD
          _ = D := mul_one D
      linarith
  rw [Finset.card_range] at h1
  have h2 : ((⌊2 * T / D⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / D + 1 := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * T / D by positivity)
    linarith
  calc (R.card : ℝ) ≤ ((⌊2 * T / D⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ 2 * T / D + 1 := h2

/-! ### The main term of their (11.2) at `q = 1` -/

/-- `√(2CQ^{ε₁}X³·2X(I + 1)r) = √(4C(I + 1))Q^{ε₁/2}X²√r` for `C, I ≥ 0` and `Q > 0`. -/
lemma sqrt_main_one {C I Q ε₁ X r : ℝ} (hC : 0 ≤ C) (hI : 0 ≤ I) (hQ : 0 < Q) :
    √(2 * C * Q ^ ε₁ * X ^ 3 * (2 * X * (I + 1) * r)) = √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) * X ^ 2 * √r := by
  have e : 2 * C * Q ^ ε₁ * X ^ 3 * (2 * X * (I + 1) * r) = 4 * C * (I + 1) * Q ^ ε₁ * (X ^ 2) ^ 2 * r := by
    ring
  have hQe : 0 ≤ Q ^ ε₁ := by positivity
  rw [e, Real.sqrt_mul (by positivity) r, Real.sqrt_mul (by positivity) ((X ^ 2) ^ 2),
    Real.sqrt_mul (by positivity) (Q ^ ε₁), Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow (Q ^ ε₁),
    ← Real.rpow_mul hQ.le, show ε₁ * (1 / 2) = ε₁ / 2 by ring]

/-- **The main term of their (11.2) at `q = 1`**: with `S = 2X(I + 1)r`, for `a, I, C, E, D_K ≥ 0`, `Q, X ≥ 1`,
`0 ≤ r ≤ Q`, `0 ≤ N ≤ Q`, `c₂Λ ≥ 0`, `X³Q ≤ X^k`, the energy term `QN√r√E ≤ c₂ΛW` and `Q²r^{3/2} ≤ W`, the main
term is at most `192aIL²√(4C(I + 1))Q^{ε₁/2}X⁵((2(I + 1) + √D_K)W + √I·c₂ΛW)`. -/
lemma main_le_one {a I L C Q ε₁ X r N E DK c₂ Λ W : ℝ} (k : ℕ) (ha : 0 ≤ a) (hI : 0 ≤ I) (hC : 0 ≤ C)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) (hr : 0 ≤ r) (hrQ : r ≤ Q) (hN : 0 ≤ N) (hNQ : N ≤ Q) (hE : 0 ≤ E) (hDK : 0 ≤ DK)
    (hc₂Λ : 0 ≤ c₂ * Λ) (hXk : X ^ 3 * Q ≤ X ^ k) (hen : Q * N * √r * √E ≤ c₂ * Λ * W)
    (hW : Q ^ 2 * r ^ (3 / 2 : ℝ) ≤ W) :
    192 * a * I * L ^ 2 * √(2 * C * Q ^ ε₁ * X ^ 3 * (2 * X * (I + 1) * r)) *
        ((X * Q) ^ 2 * (2 * X * (I + 1) * r) + X * Q * N * √(I * E + r ^ 4 * DK / X ^ (2 * k))) ≤
      192 * a * I * L ^ 2 * √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) * X ^ 5 *
        ((2 * (I + 1) + √DK) * W + √I * (c₂ * Λ * W)) := by
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < X := by linarith
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  rw [sqrt_main_one hC hI hQ0]
  have hG := sqrt_Gq_le k hI hE hDK hX0 (r := r)
  have hr32 : √r * r = r ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one' hr (by norm_num)]; norm_num
  have h3 := term3_le hX0 hr hrQ hNQ hXk
  have hX35 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX5 : 1 ≤ X ^ 5 := one_le_pow₀ hX
  have t1 : 2 * (I + 1) * X ^ 5 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) ≤ 2 * (I + 1) * X ^ 5 * W := by gcongr
  have t2 : √I * X ^ 3 * (Q * N * √r * √E) ≤ √I * X ^ 5 * (c₂ * Λ * W) := by
    have h0 : 0 ≤ c₂ * Λ * W := mul_nonneg hc₂Λ hW0
    calc √I * X ^ 3 * (Q * N * √r * √E) ≤ √I * X ^ 3 * (c₂ * Λ * W) := by gcongr
      _ ≤ √I * X ^ 5 * (c₂ * Λ * W) := by gcongr
  have t3 : √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k) ≤ √DK * (X ^ 5 * W) := by
    have h4 : X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k ≤ X ^ 5 * W := by
      have : W ≤ X ^ 5 * W := le_mul_of_one_le_left hW0 hX5
      linarith
    exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
  have hc : 0 ≤ 192 * a * I * L ^ 2 * √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) := by positivity
  calc 192 * a * I * L ^ 2 * (√(4 * C * (I + 1)) * Q ^ (ε₁ / 2) * X ^ 2 * √r) *
        ((X * Q) ^ 2 * (2 * X * (I + 1) * r) + X * Q * N * √(I * E + r ^ 4 * DK / X ^ (2 * k)))
      ≤ 192 * a * I * L ^ 2 * (√(4 * C * (I + 1)) * Q ^ (ε₁ / 2) * X ^ 2 * √r) *
        ((X * Q) ^ 2 * (2 * X * (I + 1) * r) + X * Q * N * (√I * √E + r ^ 2 * √DK / X ^ k)) := by gcongr
    _ = 192 * a * I * L ^ 2 * √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) *
        (2 * (I + 1) * X ^ 5 * (Q ^ 2 * (√r * r)) + √I * X ^ 3 * (Q * N * √r * √E) +
          √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k)) := by ring
    _ ≤ 192 * a * I * L ^ 2 * √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) *
        (2 * (I + 1) * X ^ 5 * W + √I * X ^ 5 * (c₂ * Λ * W) + √DK * (X ^ 5 * W)) := by
        rw [hr32]
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hc
    _ = 192 * a * I * L ^ 2 * √(4 * C * (I + 1)) * Q ^ (ε₁ / 2) * X ^ 5 *
        ((2 * (I + 1) + √DK) * W + √I * (c₂ * Λ * W)) := by ring

/-- **The main term at `q = 1`**, at the order `2(k₀ + 3)` and the exponent `ε/2`: at most `K_mΦ^εW`, with `Φ = TN`
and `K_m = 192C_J(0)I√(4C₁(I + 1))(2(I + 1) + √D + √I·c₂)(1/(δ log 2) + 1)²`, for `T, N ≥ 1`, `N, |R| ≤ T`,
`E ≥ 0`, `0 < δ ≤ min(1, ε/12)`, `0 < ε′ ≤ ε/20`, `X = T^{ε′}` with `X³T ≤ X^{k₀+3}`, `1 ≤ M ≤ Φ`, `C₁, c₂ ≥ 0`,
`Λ = Φ^{ε/4}`, the energy term `TN√|R|√E ≤ c₂ΛW` and `T²|R|^{3/2} ≤ W`. -/
lemma main_part_one {ι : Type*} (R : Finset ι) {T N X E ε δ ε' C₁ c₂ Λ W : ℝ} {M k₀ : ℕ}
    (hT : 1 ≤ T) (hN1 : 1 ≤ N) (hNQ : N ≤ T) (hrq : (R.card : ℝ) ≤ T)
    (hE : 0 ≤ E) (hε : 0 < ε) (hδ0 : 0 < δ) (hδε : δ ≤ ε / 12) (hε'0 : 0 < ε')
    (hε'ε : ε' ≤ ε / 20) (hX : X = T ^ ε') (hXk : X ^ 3 * T ≤ X ^ (k₀ + 3))
    (hM1 : 1 ≤ M) (hMΦ : (M : ℝ) ≤ T * N) (hC₁ : 0 ≤ C₁) (hc₂ : 0 ≤ c₂)
    (hΛ : Λ = (T * N) ^ (ε / 4)) (hen : T * N * √(R.card : ℝ) * √E ≤ c₂ * Λ * W)
    (hW : T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ W) :
    192 * CJ 0 * (∫ x, psi0 x) * ((Nat.log 2 M : ℝ) + 1) ^ 2 *
        √(2 * C₁ * T ^ (ε / 2) * X ^ 3 * (2 * X * ((∫ x, psi0 x) + 1) * R.card)) *
        ((X * T) ^ 2 * (2 * X * ((∫ x, psi0 x) + 1) * R.card) + X * T * N *
          √((∫ x, psi0 x) * E + (R.card : ℝ) ^ 4 * Dpsi (2 * (k₀ + 3)) / X ^ (2 * (k₀ + 3)))) ≤
      192 * CJ 0 * (∫ x, psi0 x) * √(4 * C₁ * ((∫ x, psi0 x) + 1)) *
        (2 * ((∫ x, psi0 x) + 1) + √(Dpsi (2 * (k₀ + 3))) + √(∫ x, psi0 x) * c₂) *
        (1 / (δ * Real.log 2) + 1) ^ 2 * (T * N) ^ ε * W := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hΦQ : T ≤ T * N := le_mul_of_one_le_right hT0.le hN1
  have hΦ1 : 1 ≤ T * N := hT.trans hΦQ
  have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hT hε'0.le
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_rpow hΦ1 (by positivity)
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hCJ := CJ_nonneg 0
  have hDK := Dpsi_nonneg (2 * (k₀ + 3))
  have hmain := main_le_one (k₀ + 3) hCJ hI0 hC₁ hT hX1 hr0 hrq hN0.le hNQ hE hDK (mul_nonneg hc₂ (by linarith))
    hXk hen hW (L := (Nat.log 2 M : ℝ) + 1) (ε₁ := ε / 2)
  have hL := natlog_le_rpow hM1 hMΦ hδ0
  have hQe : T ^ (ε / 2 / 2) ≤ (T * N) ^ (ε / 4) := by
    rw [show ε / 2 / 2 = ε / 4 by ring]
    exact Real.rpow_le_rpow hT0.le hΦQ (by positivity)
  have hX5 : X ^ 5 ≤ (T * N) ^ (5 * ε') := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    push_cast
    rw [mul_comm ε' 5]
    exact Real.rpow_le_rpow hT0.le hΦQ (by positivity)
  have hfac := factors_le hΦ1 zero_le_one (show (1 : ℝ) ≤ 1 * (T * N) ^ δ by
      rw [one_mul]; exact Real.one_le_rpow hΦ1 hδ0.le) (by positivity) hL (by positivity) hQe (by positivity) hX5
    (by linarith) (le_of_eq hΛ) (ε := ε) (by linarith)
  rw [one_mul, one_mul] at hfac
  -- `(2(I + 1) + √D)W ≤ (2(I + 1) + √D)ΛW`, then the factors
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ x, psi0 x := ⟨_, rfl⟩
  rw [← hI] at hmain hI0 ⊢
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = (Nat.log 2 M : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hLd] at hmain hfac ⊢
  have hk : 0 ≤ 192 * CJ 0 * I * √(4 * C₁ * (I + 1)) := by positivity
  have h1 : (2 * (I + 1) + √(Dpsi (2 * (k₀ + 3)))) * W ≤
      (2 * (I + 1) + √(Dpsi (2 * (k₀ + 3)))) * (Λ * W) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hW0 hΛ1) (by positivity)
  have hB0 : 0 ≤ L ^ 2 * T ^ (ε / 2 / 2) * X ^ 5 := by positivity
  calc _ ≤ _ := hmain
    _ = 192 * CJ 0 * I * √(4 * C₁ * (I + 1)) * (L ^ 2 * T ^ (ε / 2 / 2) * X ^ 5) *
        ((2 * (I + 1) + √(Dpsi (2 * (k₀ + 3)))) * W + √I * (c₂ * Λ * W)) := by ring
    _ ≤ 192 * CJ 0 * I * √(4 * C₁ * (I + 1)) * (L ^ 2 * T ^ (ε / 2 / 2) * X ^ 5) *
        ((2 * (I + 1) + √(Dpsi (2 * (k₀ + 3)))) * (Λ * W) + √I * (c₂ * Λ * W)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 le_rfl) (mul_nonneg hk hB0)
    _ = 192 * CJ 0 * I * √(4 * C₁ * (I + 1)) * (2 * (I + 1) + √(Dpsi (2 * (k₀ + 3))) + √I * c₂) *
        (L ^ 2 * T ^ (ε / 2 / 2) * X ^ 5 * Λ) * W := by ring
    _ ≤ 192 * CJ 0 * I * √(4 * C₁ * (I + 1)) * (2 * (I + 1) + √(Dpsi (2 * (k₀ + 3))) + √I * c₂) *
        ((1 / (δ * Real.log 2) + 1) ^ 2 * (T * N) ^ ε) * W := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac ?_) hW0
        positivity
    _ = _ := by ring

/-! ### The errors of their (11.2) at `q = 1` -/

/-- **The third error with `z`**, `3r³τ(2N + 1 + z + τ)²`: for `0 ≤ r ≤ Q`, `τ ≥ 0`, `τQ^{3/2} ≤ c`, `0 ≤ z ≤ b`,
`0 ≤ N ≤ Q` and `Q ≥ 1`, at most `3c(3 + b + c)²Q²r^{3/2}`. -/
lemma E3_le_one {r τ c z b N Q : ℝ} (hr : 0 ≤ r) (hrQ : r ≤ Q) (hτ : 0 ≤ τ) (hτc : τ * Q ^ (3 / 2 : ℝ) ≤ c)
    (hz : 0 ≤ z) (hzb : z ≤ b) (hN : 0 ≤ N) (hNQ : N ≤ Q) (hQ : 1 ≤ Q) :
    3 * r ^ 3 * τ * (2 * N + 1 + z + τ) ^ 2 ≤ 3 * c * (3 + b + c) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by
  have hQ32 : 1 ≤ Q ^ (3 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hc0 : 0 ≤ c := le_trans (by positivity) hτc
  have hτ1 : τ ≤ c := by nlinarith
  have hb0 : 0 ≤ b := hz.trans hzb
  have hs : 2 * N + 1 + z + τ ≤ (3 + b + c) * Q := by nlinarith
  have hs2 : (2 * N + 1 + z + τ) ^ 2 ≤ ((3 + b + c) * Q) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have h3 := cube_le hr hrQ
  calc 3 * r ^ 3 * τ * (2 * N + 1 + z + τ) ^ 2 ≤
        3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) * τ * ((3 + b + c) * Q) ^ 2 := by gcongr
    _ = 3 * (3 + b + c) ^ 2 * (τ * Q ^ (3 / 2 : ℝ)) * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by ring
    _ ≤ 3 * (3 + b + c) ^ 2 * c * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by gcongr
    _ = 3 * c * (3 + b + c) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by ring

/-- **The error of the `m = 0` terms**, `3r³z(2N + 1 + z)²`: for `0 ≤ r ≤ Q`, `z ≥ 0`, `zQ^{5/2} ≤ b`, `0 ≤ N ≤ Q`
and `Q ≥ 1`, at most `3b(3 + b)²Q²r^{3/2}`. -/
lemma Ez_le_one {r z b N Q : ℝ} (hr : 0 ≤ r) (hrQ : r ≤ Q) (hz : 0 ≤ z) (hzb : z * Q ^ (5 / 2 : ℝ) ≤ b)
    (hN : 0 ≤ N) (hNQ : N ≤ Q) (hQ : 1 ≤ Q) :
    3 * r ^ 3 * z * (2 * N + 1 + z) ^ 2 ≤ 3 * b * (3 + b) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ52 : 1 ≤ Q ^ (5 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hb0 : 0 ≤ b := le_trans (by positivity) hzb
  have hzb' : z ≤ b := by nlinarith
  have hs : 2 * N + 1 + z ≤ (3 + b) * Q := by nlinarith
  have hs2 : (2 * N + 1 + z) ^ 2 ≤ ((3 + b) * Q) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have h3 := cube_le hr hrQ
  have e : Q ^ (3 / 2 : ℝ) * Q ^ 2 = Q ^ (5 / 2 : ℝ) * Q := by
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_add hQ0, ← Real.rpow_add_one hQ0.ne']; norm_num
  calc 3 * r ^ 3 * z * (2 * N + 1 + z) ^ 2 ≤
        3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) * z * ((3 + b) * Q) ^ 2 := by gcongr
    _ = 3 * (3 + b) ^ 2 * (z * (Q ^ (3 / 2 : ℝ) * Q ^ 2)) * r ^ (3 / 2 : ℝ) := by ring
    _ = 3 * (3 + b) ^ 2 * (z * Q ^ (5 / 2 : ℝ)) * Q * r ^ (3 / 2 : ℝ) := by rw [e]; ring
    _ ≤ 3 * (3 + b) ^ 2 * b * Q * r ^ (3 / 2 : ℝ) := by gcongr
    _ ≤ 3 * (3 + b) ^ 2 * b * Q ^ 2 * r ^ (3 / 2 : ℝ) := by
        have : Q ≤ Q ^ 2 := by nlinarith
        gcongr
    _ = 3 * b * (3 + b) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by ring

/-- **The errors of their (11.2) at `q = 1`**: at most `(K₁ + K₂ + K₃ + K_z)Φ^εW`, with `Φ = TN`, for `T, N ≥ 1`,
`N, |R| ≤ T`, `ε > 0`, `0 < δ ≤ min(1, ε/12)`, `X > 0`, `NM ≤ XT`, `M ≥ XT/(2N)`, `X³T^{5/2} ≤ X^{K₀+3}`,
`T^{7/2} ≤ X^{k_t}`, `0 ≤ z` with `zT^{5/2} ≤ b`, and `T²|R|^{3/2} ≤ W`; by `E1_le`, `E2_le`, `E3_le_one` with
`tauM_le`, and `Ez_le_one`. -/
lemma errors_part_one {ι : Type*} (R : Finset ι) {T N X ε δ W z b : ℝ} {M K₀ kt : ℕ}
    (hT : 1 ≤ T) (hN1 : 1 ≤ N) (hNQ : N ≤ T) (hrq : (R.card : ℝ) ≤ T)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδε : δ ≤ ε / 12) (hX0 : 0 < X)
    (hNM : N * M ≤ X * T) (hMlow : X * T / (2 * N) ≤ M)
    (hXK : X ^ 3 * T ^ (5 / 2 : ℝ) ≤ X ^ (K₀ + 3)) (hXkt : T ^ (7 / 2 : ℝ) ≤ X ^ kt)
    (hz0 : 0 ≤ z) (hzb : z * T ^ (5 / 2 : ℝ) ≤ b) (hW : T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ W) :
    3 * (2 * (M : ℝ)) ^ 3 * E71 1 N R X (K₀ + 3) + R.card * |muP 1 N - mu0 1 N| ^ 3 +
        (3 * (R.card : ℝ) ^ 3 * tauM N 1 T M (kt + 2) * (2 * N + 1 + z + tauM N 1 T M (kt + 2)) ^ 2 +
          3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2) ≤
      (54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) + (LinnikPower.Cdiv δ * Bw) ^ 3 +
        3 * (2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) *
          (3 + b + 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) ^ 2 + 3 * b * (3 + b) ^ 2) *
        (T * N) ^ ε * W := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hN2 : 1 / 2 ≤ N := by linarith
  have hΦQ : T ≤ T * N := le_mul_of_one_le_right hT0.le hN1
  have hΦ1 : 1 ≤ T * N := hT.trans hΦQ
  have hΦε : 1 ≤ (T * N) ^ ε := Real.one_le_rpow hΦ1 hε.le
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hcD : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hBw : 2 ≤ Bw := two_le_Bw
  have hCF := CF_nonneg (kt + 2)
  have hZ2 := Z2_nonneg
  have hT52 : 1 ≤ T ^ (5 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hb0 : 0 ≤ b := le_trans (by positivity) hzb
  have hzb' : z ≤ b := (le_mul_of_one_le_right hz0 hT52).trans hzb
  have hq1 : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) := by norm_num
  have he1 := E1_le R (q := 1) (M := M) (K' := K₀ + 3) hq1 hT hN0 hX0 (by rw [Nat.cast_one, one_mul]; exact hNM)
    (by rw [Nat.cast_one, one_mul]; exact hrq) (by rw [Nat.cast_one, one_mul]; exact hXK)
  rw [Nat.cast_one, one_mul] at he1
  have he2 := E2_le R (q := 1) hN0 hδ0 hδ1 (show ((1 : ℕ) : ℝ) ≤ T by rw [Nat.cast_one]; exact hT) (Q := T)
  have hτ := tauM_le (q := 1) (M := M) (k := kt) hq1 hT hN2 hX0 (by rw [Nat.cast_one, one_mul]; exact hMlow)
  rw [Nat.cast_one, one_mul] at hτ
  obtain ⟨cτ, hcτ⟩ : ∃ cτ : ℝ, cτ = 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt := ⟨_, rfl⟩
  rw [← hcτ] at hτ ⊢
  have hτ0 : 0 ≤ tauM N 1 T M (kt + 2) := by
    unfold tauM
    have : (0 : ℝ) ≤ M := by positivity
    positivity
  have hcτ0 : 0 ≤ cτ := by rw [hcτ]; positivity
  have hτc : tauM N 1 T M (kt + 2) * T ^ (3 / 2 : ℝ) ≤ cτ := by
    have hXkt0 : 0 < X ^ kt := by positivity
    have e : T ^ 2 * T ^ (3 / 2 : ℝ) = T ^ (7 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hT0]; norm_num
    calc tauM N 1 T M (kt + 2) * T ^ (3 / 2 : ℝ) ≤ cτ * T ^ 2 / X ^ kt * T ^ (3 / 2 : ℝ) := by gcongr
      _ = cτ * (T ^ 2 * T ^ (3 / 2 : ℝ)) / X ^ kt := by ring
      _ = cτ * T ^ (7 / 2 : ℝ) / X ^ kt := by rw [e]
      _ ≤ cτ * X ^ kt / X ^ kt := by gcongr
      _ = cτ := by field_simp
  have he3 := E3_le_one hr0 hrq hτ0 hτc hz0 hzb' hN0.le hNQ hT
  have hez := Ez_le_one hr0 hrq hz0 hzb hN0.le hNQ hT
  have ht : T ^ (3 * δ) ≤ (T * N) ^ ε :=
    (Real.rpow_le_rpow hT0.le hΦQ (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hΦ1 (by linarith))
  set P := T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hK1 : 0 ≤ 54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) := by have := CJ_nonneg (K₀ + 3); positivity
  have hK2 : 0 ≤ (LinnikPower.Cdiv δ * Bw) ^ 3 := by positivity
  have hK3 : 0 ≤ 3 * cτ * (3 + b + cτ) ^ 2 := by positivity
  have hKz : 0 ≤ 3 * b * (3 + b) ^ 2 := by positivity
  have hW0 : 0 ≤ W := hP0.trans hW
  -- each error against `Φ^εW`
  have hPW : P ≤ (T * N) ^ ε * W := hW.trans (le_mul_of_one_le_left hW0 hΦε)
  have f1 := mul_le_mul_of_nonneg_left hPW hK1
  have f2 : (LinnikPower.Cdiv δ * Bw) ^ 3 * T ^ (3 * δ) * P ≤ (LinnikPower.Cdiv δ * Bw) ^ 3 * ((T * N) ^ ε * W) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul ht hW hP0 (by positivity)) hK2
  have f3 := mul_le_mul_of_nonneg_left hPW hK3
  have fz := mul_le_mul_of_nonneg_left hPW hKz
  have e : (54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) + (LinnikPower.Cdiv δ * Bw) ^ 3 + 3 * cτ * (3 + b + cτ) ^ 2 +
      3 * b * (3 + b) ^ 2) * (T * N) ^ ε * W =
      54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) * ((T * N) ^ ε * W) +
        (LinnikPower.Cdiv δ * Bw) ^ 3 * ((T * N) ^ ε * W) + 3 * cτ * (3 + b + cτ) ^ 2 * ((T * N) ^ ε * W) +
        3 * b * (3 + b) ^ 2 * ((T * N) ^ ε * W) := by ring
  rw [e]
  refine (add_le_add (add_le_add he1 he2) (add_le_add he3 hez)).trans ?_
  have h := add_le_add (add_le_add f1 f2) (add_le_add f3 fz)
  linarith only [h]

/-! ### Their Proposition 11.1 at `q = 1` -/

/-- **The small range at `q = 1`**, by `S3_le_crude`: for `T ≥ 1`, `ε > 0`, `T^{2/3}/2 ≤ N ≤ T < Q₁` and `|R| ≤ 3T`,
`S₃ ≤ 2^ε(3Q₁)^{3/2}(Q₁ + 1)³(TN)^εT²|R|^{3/2}`. -/
lemma small_case_one {ι : Type*} [DecidableEq ι] (R : Finset ι) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ)
    {T N Q₁ ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) (hN : T ^ (2 / 3 : ℝ) / 2 ≤ N) (hNQ : N ≤ T) (hsmall : T < Q₁)
    (hr : (R.card : ℝ) ≤ 3 * T) :
    S3 1 N R χ t ≤ 2 ^ ε * (3 * Q₁) ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (T * N) ^ ε *
      (T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ)) := by
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hQ₁0 : 0 < Q₁ := by linarith
  have h1 := S3_le_crude hN0 R χ t
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have h2 := cube_le hr0 (hr.trans (by linarith : 3 * T ≤ 3 * Q₁))
  have h3 : (N + 1) ^ 3 ≤ (Q₁ + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h4 : 1 ≤ 2 ^ ε * (T * N) ^ ε := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.one_le_rpow (by nlinarith) hε.le
  have h5 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  have h6 : 1 ≤ (2 ^ ε * (T * N) ^ ε) * T ^ 2 := one_le_mul_of_one_le_of_one_le h4 h5
  have h0 : 0 ≤ (3 * Q₁) ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc S3 1 N R χ t ≤ (R.card : ℝ) ^ 3 * (N + 1) ^ 3 := h1
    _ ≤ ((3 * Q₁) ^ (3 / 2 : ℝ) * (R.card : ℝ) ^ (3 / 2 : ℝ)) * (Q₁ + 1) ^ 3 :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (3 * Q₁) ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) := by ring
    _ ≤ (3 * Q₁) ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) *
        ((2 ^ ε * (T * N) ^ ε) * T ^ 2) := le_mul_of_one_le_right h0 h6
    _ = _ := by ring

/-- **Their Proposition 11.1 at `q = 1`**, for `T^ε`-separated points: for every `ε > 0` there is `C ≥ 0` such that,
for `T ≥ 1`, `T^{2/3}/2 ≤ N ≤ T`, `S ⊆ [6N/5, 9N/5]`, `|b_n| ≤ 1`, points `|t_i| ≤ T` at least `T^ε` apart with
`|Σ_{n∈S}b_nn^{it_i}| ≥ N^σ/6`, `S₃ ≤ C(TN)^ε(T²|R|^{3/2} + T|R|N^{3−2σ} + T|R|²N^{3/2−σ} +
T^{9/8}|R|^{29/16}N^{3/2−σ})`. The characters `χ_i` mod `1` are all `1`. -/
def GMS3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    (∀ i ∈ R, ∀ j ∈ R, i ≠ j → T ^ ε ≤ |t i - t j|) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    T ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    S3 1 N R χ t ≤ C * (T * N) ^ ε * (T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) + T * R.card * N ^ (3 - 2 * σ) +
      T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) + T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))

set_option maxHeartbeats 1000000 in
/-- **Their Proposition 11.1 at `q = 1`**: `GMS3` from `CGLP81` (their Proposition 8.1) and `CGLT101` (Heath-Brown's
Theorem 10.1). For `T ≥ Q₁`: `S3_le_112_one` at `ϖ = 3/4`, `ε/2`, `X = T^{ε′}` with `ε′ = min(1/12, ε/20)`,
`M = ⌊XT/N⌋`, `S = 2X(∫ψ̃₀ + 1)|R|`, `z = NB(1 + T^ε)^{−(k_z+3)}` and the orders `2(k₀ + 3)`, `K₀ + 3` and `k_t + 2`;
the energy term by `prop102` at `ε/2` or `remark103` (`energy_term`); then `main_part_one` and `errors_part_one`.
For `T < Q₁`, `small_case_one`. -/
theorem gms3 (hP : CGLP81) (hT : CGLT101) : GMS3 := by
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 12) 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_right _ _
  have hδε : δ ≤ ε / 12 := hδ ▸ min_le_left _ _
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (1 / 12) (ε / 20) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min (by norm_num) (by positivity)
  have hε'1 : ε' ≤ 1 / 12 := hε' ▸ min_le_left _ _
  have hε'ε : ε' ≤ ε / 20 := hε' ▸ min_le_right _ _
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈1 / ε'⌉₊ := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = ⌈5 / (2 * ε')⌉₊ := ⟨_, rfl⟩
  obtain ⟨kt, hkt⟩ : ∃ kt : ℕ, kt = ⌈4 / ε'⌉₊ := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k1 : ℕ, k1 = ⌈2 / ε'⌉₊ := ⟨_, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ kz : ℕ, kz = ⌈4 / ε⌉₊ := ⟨_, rfl⟩
  have hk₀ε : (1 : ℝ) ≤ ε' * k₀ := by
    have := Nat.le_ceil (1 / ε')
    rw [← hk₀, div_le_iff₀ hε'0] at this
    linarith
  have hK₀ε : (5 / 2 : ℝ) ≤ ε' * K₀ := by
    have := Nat.le_ceil (5 / (2 * ε'))
    rw [← hK₀, div_le_iff₀ (by positivity)] at this
    linarith
  have hktε : (4 : ℝ) ≤ ε' * kt := by
    have := Nat.le_ceil (4 / ε')
    rw [← hkt, div_le_iff₀ hε'0] at this
    linarith
  have hk1ε : (2 : ℝ) ≤ ε' * k1 := by
    have := Nat.le_ceil (2 / ε')
    rw [← hk1, div_le_iff₀ hε'0] at this
    linarith
  have hkzε : (4 : ℝ) ≤ ε * kz := by
    have := Nat.le_ceil (4 / ε)
    rw [← hkz, div_le_iff₀ hε] at this
    linarith
  obtain ⟨Bz, hBz0, hBz⟩ := exists_hhat_zero_bound kz
  obtain ⟨C₁, Q₀, hC₁0, h112⟩ :=
    S3_le_112_one.{0} hP (ϖ := 3 / 4) (by norm_num) (by norm_num) (half_pos hε) (2 * (k₀ + 3))
  obtain ⟨C₂, hC₂0, h102⟩ := prop102 hT (half_pos hε)
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hCJ0 := CJ_nonneg 0
  have hCJK := CJ_nonneg (K₀ + 3)
  have hDK0 := Dpsi_nonneg (2 * (k₀ + 3))
  have hD10 := Dpsi_nonneg k1
  have hCF := CF_nonneg (kt + 2)
  have hZ2 := Z2_nonneg
  have hBw : 2 ≤ Bw := two_le_Bw
  have hcD : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the threshold: `Q₀`, `64`, `T^ε ≥ 3` and `T ≥ D_{k₁}`
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : ℝ, Q₁ = max (max Q₀ 64) (max ((3 : ℝ) ^ (1 / ε)) (Dpsi k1 + 1)) := ⟨_, rfl⟩
  have hQ₁64 : (64 : ℝ) ≤ Q₁ := by rw [hQ₁]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hQ₁0 : 0 < Q₁ := by linarith
  refine ⟨192 * CJ 0 * (∫ x, psi0 x) * √(4 * C₁ * ((∫ x, psi0 x) + 1)) *
      (2 * ((∫ x, psi0 x) + 1) + √(Dpsi (2 * (k₀ + 3))) + √(∫ x, psi0 x) * (8 + √C₂)) *
      (1 / (δ * Real.log 2) + 1) ^ 2 +
    (54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) + (LinnikPower.Cdiv δ * Bw) ^ 3 +
      3 * (2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) *
        (3 + Bz + 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) ^ 2 + 3 * Bz * (3 + Bz) ^ 2) +
    2 ^ ε * (3 * Q₁) ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3, by positivity, ?_⟩
  intro ι _ R χ t T N σ S b hsep hT1 _ _ hN hNT hS hb ht hbig
  have hT0 : 0 < T := by linarith
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hTε1 : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hE0 : (0 : ℝ) ≤ energy R χ t := by positivity
  have hW1 : T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ T ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
      T * R.card * N ^ (3 - 2 * σ) + T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
      T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by
    have h1 : 0 ≤ T * R.card * N ^ (3 - 2 * σ) := by positivity
    have h2 : 0 ≤ T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) := by positivity
    have h3 : 0 ≤ T ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by positivity
    linarith
  -- the number of points
  have hcard := card_le_of_sep R hT0.le (by positivity) hsep ht
  by_cases hsmall : T < Q₁
  · have hr3 : (R.card : ℝ) ≤ 3 * T := by
      have : 2 * T / T ^ ε ≤ 2 * T := div_le_self (by positivity) hTε1
      linarith only [this, hcard, hT1]
    have h := small_case_one R χ t hT1 hε hN hNT hsmall hr3
    exact final_small h hW1 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  · push Not at hsmall
    have hQ64 : 64 ≤ T := hQ₁64.trans hsmall
    have hQ₀' : Q₀ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans (hQ₁ ▸ hsmall))
    have hT3 : (3 : ℝ) ^ (1 / ε) ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans (hQ₁ ▸ hsmall))
    have hTD : Dpsi k1 + 1 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans (hQ₁ ▸ hsmall))
    -- `T^ε ≥ 3`: the points are spaced and at most `T` in number
    have hTε3 : 3 ≤ T ^ ε := by
      calc (3 : ℝ) = ((3 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ T ^ ε := Real.rpow_le_rpow (by positivity) hT3 hε.le
    have hsp : Spaced R χ t := fun i hi j hj hij _ =>
      lt_of_lt_of_le (show (2 : ℝ) < 3 by norm_num) (hTε3.trans (hsep i hi j hj hij))
    have hrq : (R.card : ℝ) ≤ T := by
      have : 2 * T / T ^ ε ≤ 2 * T / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hTε3
      linarith only [this, hcard, hQ64]
    have hN8 : 8 ≤ N := by
      have e : ((4 : ℝ) ^ 3) ^ (2 / 3 : ℝ) = 4 ^ 2 := pow_rpow_eq (by norm_num) 3 2 (by norm_num)
      have h16 : (16 : ℝ) ≤ T ^ (2 / 3 : ℝ) := by
        calc (16 : ℝ) = ((4 : ℝ) ^ 3) ^ (2 / 3 : ℝ) := by rw [e]; norm_num
          _ ≤ T ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith only [hQ64]) (by norm_num)
      linarith only [h16, hN]
    have hN1 : 1 ≤ N := by linarith only [hN8]
    have hΦQ : T ≤ T * N := le_mul_of_one_le_right hT0.le hN1
    have hΦ1 : 1 ≤ T * N := hT1.trans hΦQ
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = T ^ ε' := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hT1 hε'0.le
    have hX0 : 0 < X := by linarith
    obtain ⟨hM1, hNM, hMlow⟩ := M_props hX1 hN0 hNT
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊X * T / N⌋₊ := ⟨_, rfl⟩
    rw [← hM] at hM1 hNM hMlow
    have h2M := two_M_le hQ64 hN hX hε'1 hNM
    have hMΦ : (M : ℝ) ≤ T * N := by
      have h34 : T ^ (3 / 4 : ℝ) ≤ T := by
        calc T ^ (3 / 4 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
          _ = T := Real.rpow_one _
      have hM0 : (0 : ℝ) ≤ M := by positivity
      linarith only [h2M, h34, hΦQ, hM0]
    obtain ⟨hXk, hXK, hXkt⟩ := orders hT1 hk₀ε hK₀ε hktε
    rw [← hX] at hXk hXK hXkt
    -- `S₃,₁ ≤ S = 2X(∫ψ̃₀ + 1)|R|`, since `|R|D_{k₁} ≤ T² ≤ X^{k₁}`
    have hS31 : S31 R χ t ≤ 2 * X * ((∫ x, psi0 x) + 1) * R.card := by
      refine (S31_le_one R χ t hX1 k1 hsp).trans ?_
      have hXk1 : T ^ 2 ≤ X ^ k1 := by
        rw [hX]
        calc T ^ 2 = T ^ (2 : ℝ) := (Real.rpow_two T).symm
          _ ≤ T ^ (ε' * k1) := Real.rpow_le_rpow_of_exponent_le hT1 hk1ε
          _ = (T ^ ε') ^ k1 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      have hXk0 : 0 < X ^ k1 := by positivity
      have hRD : (R.card : ℝ) ^ 2 * Dpsi k1 / X ^ k1 ≤ R.card := by
        rw [div_le_iff₀ hXk0]
        have h1 : (R.card : ℝ) * Dpsi k1 ≤ T * T := mul_le_mul hrq (by linarith only [hTD]) hD10 hT0.le
        calc (R.card : ℝ) ^ 2 * Dpsi k1 = R.card * (R.card * Dpsi k1) := by ring
          _ ≤ R.card * (T * T) := mul_le_mul_of_nonneg_left h1 hr0
          _ = R.card * T ^ 2 := by ring
          _ ≤ R.card * X ^ k1 := mul_le_mul_of_nonneg_left hXk1 hr0
      have e : 2 * X * ((∫ x, psi0 x) + 1) * R.card = 2 * X * ((∫ x, psi0 x) * R.card + R.card) := by ring
      rw [e]
      gcongr
    -- the `m = 0` terms
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = N * Bz * ((1 + T ^ ε) ^ (kz + 3))⁻¹ := ⟨_, rfl⟩
    have hz0 : 0 ≤ z := by rw [hz]; positivity
    have hzZ : ∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z := fun i hi k hk => by
      rw [hz]
      exact norm_Zm_le_sep hN0.le t hBz0 hBz (by positivity) (fun hik => hsep i hi k hk hik)
    have hzb : z * T ^ (5 / 2 : ℝ) ≤ Bz := by
      have h1 : T ^ (7 / 2 : ℝ) ≤ (1 + T ^ ε) ^ (kz + 3) := by
        calc T ^ (7 / 2 : ℝ) ≤ T ^ (ε * (kz + 3 : ℕ)) := by
              refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
              push_cast
              have e1 : ε * ((kz : ℝ) + 3) = ε * kz + 3 * ε := by ring
              rw [e1]
              linarith only [hkzε, hε]
          _ = (T ^ ε) ^ (kz + 3) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          _ ≤ (1 + T ^ ε) ^ (kz + 3) := pow_le_pow_left₀ (by positivity) (by linarith) _
      have hpos : 0 < (1 + T ^ ε) ^ (kz + 3) := by positivity
      have e : T ^ (7 / 2 : ℝ) = T * T ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' (y := 5 / 2) hT0.le (by norm_num)]; norm_num
      rw [hz]
      calc N * Bz * ((1 + T ^ ε) ^ (kz + 3))⁻¹ * T ^ (5 / 2 : ℝ) =
            N * Bz * T ^ (5 / 2 : ℝ) / (1 + T ^ ε) ^ (kz + 3) := by ring
        _ ≤ T * Bz * T ^ (5 / 2 : ℝ) / (T * T ^ (5 / 2 : ℝ)) := by
            rw [← e]
            gcongr
        _ = Bz := by
            rw [mul_comm T Bz, mul_assoc, mul_div_assoc, div_self (by positivity), mul_one]
    have hS3 := h112 (X := X) (T := T) (M := M) (Kt := kt + 2) t (K₀ + 3) hS31 hz0 hzZ hQ₀' hT1 ht hN0 hX1 hM1
      (by omega) hNM h2M
    unfold Gq at hS3
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (T * N) ^ (ε / 4) := ⟨_, rfl⟩
    have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_rpow hΦ1 (by positivity)
    have hΛ2 : Λ ^ 2 = (T * N) ^ (ε / 2) := by
      rw [hΛ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have hS' : ∀ n ∈ S, N < n ∧ (n : ℝ) ≤ 2 * N := fun n hn =>
      ⟨by linarith [(hS n hn).1], by linarith [(hS n hn).2]⟩
    have h102' := h102 1 R χ t T N σ S b hsp (fun i _ => char_one_isPrimitive (χ i)) hT1 ht
      (by rw [Nat.cast_one, one_mul]; exact hN) hS' hb hbig
    simp only [Nat.cast_one, one_mul] at h102'
    rw [← hΛ2] at h102'
    have hen := energy_term hr0 hE0 hT1 hN hΛ1 hC₂0 h102'
    have hm := main_part_one R hT1 hN1 hNT hrq hE0 hε hδ0 hδε hε'0 hε'ε hX hXk hM1 hMΦ hC₁0
      (by positivity) hΛ hen hW1
    have he := errors_part_one R hT1 hN1 hNT hrq hε hδ0 hδ1 hδε hX0 hNM hMlow hXK hXkt hz0 hzb hW1 (M := M)
    exact final_large (combine3 hS3 hm he) (by positivity) (by positivity) (le_trans (by positivity) hW1)

end ZetaGMS3

#print axioms ZetaGMS3.char_one_isPrimitive
#print axioms ZetaGMS3.card_le_of_sep
#print axioms ZetaGMS3.main_le_one
#print axioms ZetaGMS3.main_part_one
#print axioms ZetaGMS3.E3_le_one
#print axioms ZetaGMS3.Ez_le_one
#print axioms ZetaGMS3.errors_part_one
#print axioms ZetaGMS3.small_case_one
#print axioms ZetaGMS3.gms3
