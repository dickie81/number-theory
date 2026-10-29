/-
# Guth–Maynard at `q = 1`: the second moment of `R`, and their (11.2) for several points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`LinnikCGLBlock.block_le` and `LinnikCGL112` bound `S₃` from Chen–Gupta–Li's Proposition 8.1 (`CGLP81`) and their
Lemmas 9.1 and 9.2, at one point per character. There Lemma 9.1 is an identity,
`∫_{[1/2,2]}Σ_{a unit}|R(v, a)|² dv = (3/2)φ(q)|R|` (`LinnikCGLMom.lemma91`), and it is the only step of those files
that needs one point per character. For several points this file proves the lemma as Chen and Gupta and Li state it,
for any points, with the pairs of points at distance at most `1` in place of `|R|` (`lemma91_gen`, from
`LinnikCGLL109.integral_sum_sq_le`); Guth and Maynard's
form is their Lemma 8.1, "Let W be a T^ε-separated set contained in an interval of length T. Then ∫_{v≍1}|R(v)|² dv
≪_ε |W|." Then it reruns `block_le` and `LinnikCGL112` at `q = 1` with any upper bound `S` of
`S₃,₁ = ∫_{[1/2,2]}|R|²` in place of `(3/2)φ(q)|R|`, and with `ZetaGMTrace.prop72_one` in place of
`LinnikCGLP72.prop72`.

Plain statements, with `R(v, a) = Σ_iv^{it_i}χ_i(a)` (`LinnikCGLRFact.Rf`), `ψ̃₀` and `D_K` as in `LinnikCGLMom4`,
`P = Σ_{i,k∈R}[|t_i − t_k| ≤ 1, χ_i = χ_k]` (`LinnikCGLL109.pairs1`) and `G = Gq`, the energy with its error.
* `lemma91_gen`: for any points, `X ≥ 1` and `K ∈ ℕ`,
  `∫_{[1/2,2]}Σ_{a unit}|R(v, a)|² dv ≤ 2φ(q)X(∫ψ̃₀·P + |R|²D_K/X^K)` (the proof of `LinnikCGLMom4.lemma92`, with the
  square in place of the fourth power).
* `S31_le_one`: for spaced points `P ≤ |R|` (`LinnikCGLL109.pairs1_le_card`), so at `q = 1`,
  `S₃,₁ ≤ 2X(∫ψ̃₀·|R| + |R|²D_K/X^K)`.
* `integral_sum_fb_le_S31`: `∫Σ_bf_b ≤ 2X∫ψ̃₀·S₃,₁` for `L, X > 0`, for any points
  (`LinnikCGLMom.integral_Rt_sq`).
* `block_le_one`: `LinnikCGLBlock.block_le` at `q = 1` for any points and any `S ≥ S₃,₁`, with `Vblk1` in place of
  `Vblk`: `S₃,₄ ≤ V`, `S₃,₃ ≤ 4V` and `(Σ_{m⃗∈B}Ĩ)² ≤ 2SV`.
* `sum_blk_It_le_one`: `Σ_{m⃗∈B_k}Ĩ ≤ 32(k + 1)∫ψ̃₀√P′(2^{3k}S + 2^{2k}√G)`, `P′ = 2CT^εX³S`.
* `S3_le_blocks_one`, `S3_le_112_one`: `LinnikCGL112.S3_le_blocks` and `S3_le_112` at `q = 1`:
  `S₃ ≤ 192C_J(0)∫ψ̃₀(log₂M + 1)²√P′((XT)²S + XTN√G)` plus the errors of `ZetaGMTrace.prop72_one`.

The file imports `ZetaGMTrace.lean`.
-/
import ZetaGMTrace

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace ZetaGMBlock

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72
  LinnikCGLMom LinnikCGLMom4 LinnikCGLCS LinnikCGLJ LinnikCGLFb LinnikCGLDecay LinnikCGLBlock LinnikCGL112
  LinnikCGLL105 LinnikCGLL109 ZetaGMTrace

universe u

/-! ### Their Lemma 9.1 for any points -/

/-- **Their Lemma 9.1 for `R`, for any points**: for `X ≥ 1` and `K ∈ ℕ`,
`∫_{[1/2,2]}Σ_{a unit}|R(v, a)|² dv ≤ 2φ(q)X(∫ψ̃₀·P + |R|²D_K/X^K)`, with `P = pairs1`: the majorant `ψ̃₀(log v/X)`,
`1` on `[1/2, 2]`, and `LinnikCGLL109.integral_sum_sq_le`. -/
theorem lemma91_gen {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X : ℝ} (hX : 1 ≤ X) (K : ℕ) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 2 ≤
      2 * q.totient * X * ((∫ x, psi0 x) * pairs1 R χ t + (R.card : ℝ) ^ 2 * Dpsi K / X ^ K) := by
  have hX0 : 0 < X := by linarith
  set G : ℝ → ℝ := fun v => ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 2 with hG
  set H : ℝ → ℝ := fun τ => psi0 (τ / X) * G (Real.exp τ) with hH
  have hG0 : ∀ v, 0 ≤ G v := fun v => Finset.sum_nonneg fun a _ => by positivity
  have hGm : Measurable G := Finset.measurable_sum _ fun a _ => ((measurable_Rf R χ t _).norm).pow_const 2
  have hGc : Continuous fun τ => G (Real.exp τ) := by
    simp only [hG, Rf_exp]
    exact continuous_finsetSum _ fun a _ => ((continuous_finsetSum _ fun i _ => by fun_prop).norm).pow 2
  have hHc : Continuous H := (continuous_psi0.comp (continuous_id.div_const X)).mul hGc
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * X)) (b := 2 * X)) fun τ hτ => ?_
    simp only [hH]
    rw [psi0_eq_zero, zero_mul]
    rw [abs_div, abs_of_pos hX0, le_div_iff₀ hX0]
    by_contra hc
    exact hτ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
  have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hHcs
  have hH0 : ∀ τ, 0 ≤ H τ := fun τ => mul_nonneg (psi0_nonneg _) (hG0 _)
  -- the majorant `ψ̃₀(log v/X)`, which is `1` on `[1/2, 2]`
  have hstep1 : ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ 2 * ∫ τ, H τ := by
    rw [← integral_comp_log_Ioi_zero H]
    have hint : IntegrableOn (fun v : ℝ => v⁻¹ • H (Real.log v)) (Ioi 0) :=
      (integrableOn_comp_log_Ioi_zero H).2 hHi
    have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun v hv => show (0 : ℝ) < v by linarith [hv.1]
    have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2, G v ≤ 2 * (v⁻¹ • H (Real.log v)) := by
      intro v hv
      have hv0 : 0 < v := by linarith [hv.1]
      have hlog : |Real.log v / X| ≤ 1 := by
        rw [abs_div, abs_of_pos hX0, div_le_one hX0]
        have h1 : |Real.log v| ≤ Real.log 2 := by
          rw [abs_le]; constructor
          · have := Real.log_le_log (by norm_num) hv.1
            rw [one_div, Real.log_inv] at this; linarith
          · exact Real.log_le_log hv0 hv.2
        linarith [Real.log_two_lt_d9]
      simp only [hH, smul_eq_mul, Real.exp_log hv0, psi0_eq_one hlog, one_mul]
      have h2 : 1 ≤ 2 * v⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hv0]; linarith [hv.2]
      calc G v = 1 * G v := (one_mul _).symm
        _ ≤ 2 * v⁻¹ * G v := mul_le_mul_of_nonneg_right h2 (hG0 v)
        _ = 2 * (v⁻¹ * G v) := by ring
    have hGint : IntegrableOn G (Icc (1 / 2 : ℝ) 2) := by
      refine integrableOn_Icc_of_le hGm (C := Fintype.card (ZMod q)ˣ * (R.card : ℝ) ^ 2) fun v hv => ?_
      rw [abs_of_nonneg (hG0 v)]
      calc G v ≤ ∑ _a : (ZMod q)ˣ, (R.card : ℝ) ^ 2 :=
            Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _)
              (norm_Rf_le R χ t (by linarith [hv.1]) _) 2
        _ = Fintype.card (ZMod q)ˣ * (R.card : ℝ) ^ 2 := by simp
    calc ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ ∫ v in Icc (1 / 2 : ℝ) 2, 2 * (v⁻¹ • H (Real.log v)) :=
          setIntegral_mono_on hGint ((hint.mono_set hsub).const_mul 2) measurableSet_Icc hpt
      _ = 2 * ∫ v in Icc (1 / 2 : ℝ) 2, v⁻¹ • H (Real.log v) := integral_const_mul _ _
      _ ≤ 2 * ∫ v in Ioi 0, v⁻¹ • H (Real.log v) := by
          refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub))
            (by norm_num)
          exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv =>
            smul_nonneg (inv_nonneg.2 (le_of_lt hv)) (hH0 _))
  have hstep2 := integral_sum_sq_le R χ t hX K
  calc ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ 2 * ∫ τ, H τ := hstep1
    _ ≤ 2 * (q.totient * X * ((∫ x, psi0 x) * pairs1 R χ t + (R.card : ℝ) ^ 2 * Dpsi K / X ^ K)) :=
        mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ = 2 * q.totient * X * ((∫ x, psi0 x) * pairs1 R χ t + (R.card : ℝ) ^ 2 * Dpsi K / X ^ K) := by ring

/-- **`S₃,₁` at `q = 1` for spaced points**: for spaced points (`LinnikCGLL105.Spaced`; at `q = 1`, distinct points
more than `2` apart), `X ≥ 1` and `K ∈ ℕ`, `S₃,₁ ≤ 2X(∫ψ̃₀·|R| + |R|²D_K/X^K)`. -/
theorem S31_le_one {ι : Type*} (R : Finset ι) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) {X : ℝ}
    (hX : 1 ≤ X) (K : ℕ) (hsp : Spaced R χ t) :
    S31 R χ t ≤ 2 * X * ((∫ x, psi0 x) * R.card + (R.card : ℝ) ^ 2 * Dpsi K / X ^ K) := by
  have h := lemma91_gen R χ t hX K
  have hp := pairs1_le_card R χ t hsp
  rw [Nat.totient_one, Nat.cast_one, mul_one] at h
  unfold S31
  refine h.trans ?_
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hX0 : 0 ≤ 2 * X := by linarith
  gcongr

/-! ### The first moment of `f` by `S₃,₁` -/

/-- **The first moment of `f`, for any points**: `∫Σ_bf_b ≤ 2X∫ψ̃₀·S₃,₁` for `L, X > 0`. -/
lemma integral_sum_fb_le_S31 {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) :
    ∫ u, ∑ b, fb N R χ t X M₂ b u ≤ 2 * X * (∫ x, psi0 x) * S31 R χ t := by
  have hRt : ∫ v, ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ v a ^ 2 = 2 * X * (∫ x, psi0 x) * S31 R χ t := by
    rw [integral_finsetSum (s := Finset.univ) (f := fun (a : (ZMod q)ˣ) v => Rt N R χ t X M₂ v (a : ZMod q) ^ 2)
      fun a _ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).1]
    simp_rw [fun a : (ZMod q)ˣ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).2]
    rw [← Finset.mul_sum]
    congr 1
    unfold S31
    have hint : ∀ a ∈ (Finset.univ : Finset (ZMod q)ˣ),
        Integrable (fun v => ‖Rf R χ t v (a : ZMod q)‖ ^ 2) (volume.restrict (Icc (1 / 2 : ℝ) 2)) := by
      intro a _
      refine integrableOn_Icc_of_le (((measurable_Rf R χ t _).norm).pow_const 2) (C := (R.card : ℝ) ^ 2)
        fun x hx => ?_
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hx.1]) _) 2
    rw [integral_finsetSum _ hint]
  rw [← hRt]
  refine integral_mono (integrable_finsetSum _ fun b _ => integrable_fb R χ t hL hX b)
    (integrable_finsetSum _ fun a _ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).1) fun u => ?_
  calc ∑ b, fb N R χ t X M₂ b u ≤ ∑ b : (ZMod q)ˣ, Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 2 :=
        Finset.sum_le_sum fun b _ => mul_le_of_le_one_left (sq_nonneg _) (psiW_le_one u)
    _ = ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ u a ^ 2 := Fintype.sum_equiv (Equiv.neg _) _ _ fun b => rfl

/-! ### The block `k` at `q = 1` -/

/-- The bound on the block `k` at `q = 1`, for an upper bound `S` of `S₃,₁`:
`4(k + 1)²CT^ε·4(∫ψ̃₀)²X³(M⁶S² + 2M⁴G)` with `M = 2^{k+1}` and `G = Gq`. -/
def Vblk1 {ι : Type*} (R : Finset ι) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (C ε T X S : ℝ) (K k : ℕ) : ℝ :=
  4 * (k + 1) ^ 2 * C * T ^ ε * (4 * (∫ x, psi0 x) ^ 2 * X ^ 3 *
    (((2 : ℝ) ^ (k + 1)) ^ 6 * S ^ 2 + 2 * ((2 : ℝ) ^ (k + 1)) ^ 4 * Gq R χ t X K))

/-- **The block `k` at `q = 1`, for any points** (`LinnikCGLBlock.block_le` with `S ≥ S₃,₁` in place of
`(3/2)φ(q)|R|`): from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ` there are `C ≥ 0` and `Q₀` such that, for
`S₃,₁ ≤ S`, `T ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`, `2^kN ≤ XT` and `2^{k+1} ≤ T^ϖ`, the block `k` has
`S₃,₄ ≤ V`, `S₃,₃ ≤ 4V` and `(Σ_{m⃗∈B}Ĩ(m⃗))² ≤ 2SV`, with `V = Vblk1`. -/
theorem block_le_one (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ)
      {X T S : ℝ} (M k : ℕ), S31 R χ t ≤ S → Q₀ ≤ T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X →
      N * 2 ^ k ≤ X * T → (2 : ℝ) ^ (k + 1) ≤ T ^ ϖ →
      S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ Vblk1 R χ t C ε T X S K k ∧
      S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * Vblk1 R χ t C ε T X S K k ∧
      (∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2) ^ 2 ≤ 2 * S * Vblk1 R χ t C ε T X S K k := by
  obtain ⟨C, Q₀, hC0, hS⟩ := S34_le_P81.{u} hP hϖ0 hϖ1 hε
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι N R χ t X T S M k hS31 hQ hT ht hN hX hLX hMϖ
  have hX0 : 0 < X := by linarith
  have hL : 0 < N * 2 ^ k / ((1 : ℕ) : ℝ) := by rw [Nat.cast_one, div_one]; positivity
  have hQ' : Q₀ ≤ ((1 : ℕ) : ℝ) * T := by rw [Nat.cast_one, one_mul]; exact hQ
  have hLX' : N * 2 ^ k / ((1 : ℕ) : ℝ) ≤ X * T := by rw [Nat.cast_one, div_one]; exact hLX
  have hMϖ' : (2 : ℝ) ^ (k + 1) ≤ (((1 : ℕ) : ℝ) * T) ^ ϖ := by rw [Nat.cast_one, one_mul]; exact hMϖ
  have hqT : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) ε
  set Iψ := ∫ x, psi0 x with hI
  have hI0 : 0 ≤ Iψ := integral_nonneg psi0_nonneg
  set Mk : ℝ := (2 : ℝ) ^ (k + 1) with hMk
  set A1 := ∫ u, ∑ b, fb N R χ t X (2 ^ k) b u with hA1
  set A2 := ∫ u, ∑ b, fb N R χ t X (2 ^ k) b u ^ 2 with hA2
  set G := Gq R χ t X K with hG
  have hG0 : 0 ≤ G := Gq_nonneg R χ t hX0 K
  have hS31_0 : 0 ≤ S31 R χ t := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hS0 : 0 ≤ S := hS31_0.trans hS31
  have hA10 : 0 ≤ A1 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => fb_nonneg R χ t b u
  have hA1le : A1 ≤ 2 * X * Iψ * S :=
    (integral_sum_fb_le_S31 R χ t hX0 hL).trans (mul_le_mul_of_nonneg_left hS31 (by positivity))
  have hA2le : A2 ≤ (2 * X * Iψ) ^ 2 * (2 * X * G) := by
    have h := integral_sum_fb_sq_le R χ t hX hL K
    rw [Nat.totient_one, Nat.cast_one, mul_one] at h
    exact h
  have hM0 : 0 ≤ Mk := by positivity
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  -- `S₃,₄ ≤ V`
  have hS34 : S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ Vblk1 R χ t C ε T X S K k := by
    have h := hS R χ t M k hQ' hT ht hN hX0 hLX' hMϖ'
    simp only [Nat.totient_one, Nat.cast_one, one_mul, one_pow] at h
    refine h.trans ?_
    unfold Vblk1
    rw [← hI, ← hMk, ← hG, ← hA1, ← hA2]
    have hpre : 0 ≤ 4 * ((k : ℝ) + 1) ^ 2 * C * T ^ ε := mul_nonneg (mul_nonneg (by positivity) hC0) hqT
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have h1 : A1 ^ 2 ≤ (2 * X * Iψ * S) ^ 2 := pow_le_pow_left₀ hA10 hA1le 2
    have hc1 : 0 ≤ Mk ^ 6 := pow_nonneg hM0 6
    have hc2 : 0 ≤ Mk ^ 4 := pow_nonneg hM0 4
    have hc3 : 0 ≤ 4 * (Iψ ^ 2 * Mk ^ 6 * S ^ 2) := by positivity
    calc Mk ^ 6 * A1 ^ 2 + Mk ^ 4 * A2
        ≤ Mk ^ 6 * (2 * X * Iψ * S) ^ 2 + Mk ^ 4 * ((2 * X * Iψ) ^ 2 * (2 * X * G)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left hA2le hc2)
      _ = 4 * (Iψ ^ 2 * Mk ^ 6 * S ^ 2) * X ^ 2 + 4 * Iψ ^ 2 * X ^ 3 * (2 * Mk ^ 4 * G) := by ring
      _ ≤ 4 * (Iψ ^ 2 * Mk ^ 6 * S ^ 2) * X ^ 3 + 4 * Iψ ^ 2 * X ^ 3 * (2 * Mk ^ 4 * G) :=
          add_le_add (mul_le_mul_of_nonneg_left hX23 hc3) le_rfl
      _ = 4 * Iψ ^ 2 * X ^ 3 * (Mk ^ 6 * S ^ 2 + 2 * Mk ^ 4 * G) := by ring
  -- `S₃,₃ ≤ 4V`
  have hS33 : S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * Vblk1 R χ t C ε T X S K k :=
    (S33_le_S34 R χ t hL.le fun m hm => swap_mem_blk hm).trans (by linarith)
  refine ⟨hS34, hS33, ?_⟩
  -- the block sum
  set V := Vblk1 R χ t C ε T X S K k with hV
  have hS34_0 : 0 ≤ S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) :=
    setIntegral_nonneg measurableSet_Icc fun v _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hV0 : 0 ≤ V := hS34_0.trans hS34
  have h32 := S32_le R χ t (X := X) (M₂ := 2 ^ k) (blk M k) hL.le
  have hsq33 : Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ 2 * Real.sqrt V := by
    calc Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ Real.sqrt (4 * V) :=
          Real.sqrt_le_sqrt hS33
      _ = 2 * Real.sqrt V := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq34 : Real.sqrt (S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ Real.sqrt V :=
    Real.sqrt_le_sqrt hS34
  have h32' : S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 2 * V := by
    calc S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)
        ≤ Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) *
          Real.sqrt (S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) := h32
      _ ≤ 2 * Real.sqrt V * Real.sqrt V :=
          mul_le_mul hsq33 hsq34 (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * V := by rw [mul_assoc, Real.mul_self_sqrt hV0]
  have hS32_0 : 0 ≤ S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) :=
    setIntegral_nonneg measurableSet_Icc fun v _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  calc (∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2) ^ 2
      ≤ S31 R χ t * S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) := sum_It_sq_le R χ t (blk M k) hL.le
    _ ≤ S * (2 * V) := mul_le_mul hS31 h32' hS32_0 hS0
    _ = 2 * S * V := by ring

/-- **One block at `q = 1`, square-rooted**: from `CGLP81`, under the hypotheses of `block_le_one`,
`Σ_{m⃗∈B_k}Ĩ ≤ 32(k + 1)∫ψ̃₀√(2CT^εX³S)(2^{3k}S + 2^{2k}√G)`. -/
theorem sum_blk_It_le_one (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ)
      {X T S : ℝ} (M k : ℕ), S31 R χ t ≤ S → Q₀ ≤ T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X →
      N * 2 ^ k ≤ X * T → (2 : ℝ) ^ (k + 1) ≤ T ^ ϖ →
      ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 ≤
        32 * (k + 1) * (∫ x, psi0 x) * Real.sqrt (2 * C * T ^ ε * X ^ 3 * S) *
          (((2 : ℝ) ^ k) ^ 3 * S + ((2 : ℝ) ^ k) ^ 2 * Real.sqrt (Gq R χ t X K)) := by
  obtain ⟨C, Q₀, hC0, hB⟩ := block_le_one.{u} hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι N R χ t X T S M k hS31 hQ hT ht hN hX hLX hMϖ
  obtain ⟨-, -, hsq⟩ := hB R χ t M k hS31 hQ hT ht hN hX hLX hMϖ
  have hX0 : 0 < X := by linarith
  have hqT : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) ε
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hG0 := Gq_nonneg R χ t hX0 K
  have hS31_0 : 0 ≤ S31 R χ t := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hS0 : 0 ≤ S := hS31_0.trans hS31
  set P := 2 * C * T ^ ε * X ^ 3 * S with hPdef
  have hP0 : 0 ≤ P := by positivity
  set a := 4 * ((k : ℝ) + 1) * (∫ x, psi0 x) with ha
  have ha0 : 0 ≤ a := by positivity
  set G := Gq R χ t X K with hG
  set Mk : ℝ := (2 : ℝ) ^ (k + 1) with hMk
  have hM0 : 0 ≤ Mk := by positivity
  set Q := Mk ^ 6 * S ^ 2 + 2 * Mk ^ 4 * G with hQdef
  have hV : 2 * S * Vblk1 R χ t C ε T X S K k = a ^ 2 * (P * Q) := by
    unfold Vblk1
    rw [hQdef, hG, hMk, ha, hPdef]
    ring
  have hs : ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 ≤ Real.sqrt (a ^ 2 * (P * Q)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (hsq.trans_eq hV))
  have hsqrt : Real.sqrt (a ^ 2 * (P * Q)) = a * Real.sqrt P * Real.sqrt Q := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0, Real.sqrt_mul hP0]
    ring
  have hsG : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG0
  have hsG0 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg G
  have hQle : Real.sqrt Q ≤ Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G := by
    have hB0 : 0 ≤ Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G := by positivity
    have h1 : 0 ≤ Mk ^ 5 * S * Real.sqrt G := by positivity
    have h2 : 0 ≤ Mk ^ 4 * G := by positivity
    have hle : Q ≤ (Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G) ^ 2 := by
      have e : (Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G) ^ 2 =
          Mk ^ 6 * S ^ 2 + 4 * (Mk ^ 5 * S * Real.sqrt G) + 4 * Mk ^ 4 * Real.sqrt G ^ 2 := by ring
      rw [e, hsG, hQdef]
      linarith
    calc Real.sqrt Q ≤ Real.sqrt ((Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G) ^ 2) := Real.sqrt_le_sqrt hle
      _ = Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G := Real.sqrt_sq hB0
  have hPs0 : 0 ≤ a * Real.sqrt P := mul_nonneg ha0 (Real.sqrt_nonneg P)
  calc ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2
      ≤ a * Real.sqrt P * Real.sqrt Q := hs.trans_eq hsqrt
    _ ≤ a * Real.sqrt P * (Mk ^ 3 * S + 2 * Mk ^ 2 * Real.sqrt G) := mul_le_mul_of_nonneg_left hQle hPs0
    _ = 32 * (k + 1) * (∫ x, psi0 x) * Real.sqrt P *
          (((2 : ℝ) ^ k) ^ 3 * S + ((2 : ℝ) ^ k) ^ 2 * Real.sqrt G) := by
        rw [ha, hMk]
        ring

/-! ### Their (11.2) at `q = 1` -/

/-- The algebra of one block at `q = 1`: `AN²/u·32(k + 1)Is(u³S + u²g) = 64·(A/2)Is(k + 1)(N²u²S + N²ug)`. -/
lemma block_alg_one (A N u I s g S k : ℝ) (hu : u ≠ 0) :
    A * N ^ 2 / u * (32 * (k + 1) * I * s * (u ^ 3 * S + u ^ 2 * g)) =
      32 * A * I * s * ((k + 1) * (N ^ 2 * u ^ 2 * S + N ^ 2 * u * g)) := by
  field_simp

/-- **The blocks summed at `q = 1`**: from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ` there are `C ≥ 0` and `Q₀`
such that, for `S₃,₁ ≤ S`, `|Z| ≤ z` on `R` with `z ≥ 0`, `T ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`,
`M ≥ 1`, `K_t ≥ 2`, `NM ≤ XT` and `2M ≤ T^ϖ`,
`S₃ ≤ 192C_J(0)∫ψ̃₀(log₂M + 1)²√(2CT^εX³S)((NM)²S + N²M√G)` plus the errors of `ZetaGMTrace.prop72_one`. -/
theorem S3_le_blocks_one (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [DecidableEq ι] {N : ℝ} {R : Finset ι}
      {χ : ι → DirichletCharacter ℂ 1} (t : ι → ℝ) {X T S z : ℝ} {M Kt : ℕ} (K' : ℕ),
      S31 R χ t ≤ S → 0 ≤ z → (∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z) →
      Q₀ ≤ T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → 1 ≤ M → 2 ≤ Kt →
      N * M ≤ X * T → 2 * (M : ℝ) ≤ T ^ ϖ →
      S3 1 N R χ t ≤ 192 * CJ 0 * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
          Real.sqrt (2 * C * T ^ ε * X ^ 3 * S) * ((N * M) ^ 2 * S + N ^ 2 * M * Real.sqrt (Gq R χ t X K)) +
        3 * (2 * (M : ℝ)) ^ 3 * E71 1 N R X K' + R.card * |muP 1 N - mu0 1 N| ^ 3 +
        (3 * (R.card : ℝ) ^ 3 * tauM N 1 T M Kt * (2 * N + 1 + z + tauM N 1 T M Kt) ^ 2 +
          3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2) := by
  obtain ⟨C, Q₀, hC0, hB⟩ := sum_blk_It_le_one.{u} hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι _ N R χ t X T S z M Kt K' hS31 hz0 hz hQ hT ht hN hX hM hKt hNM hMϖ
  have hX0 : 0 < X := by linarith
  have h72 := prop72_one hN R χ t ht hM hKt hX0 K' hz0 hz
  set Kl := Nat.log 2 M with hKl
  set P := 2 * C * T ^ ε * X ^ 3 * S with hPdef
  set G := Gq R χ t X K with hG
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hG0 : 0 ≤ G := Gq_nonneg R χ t hX0 K
  have hS31_0 : 0 ≤ S31 R χ t := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hS0 : 0 ≤ S := hS31_0.trans hS31
  have hN0 : 0 ≤ N := hN.le
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- the constant in front
  set c := 64 * CJ 0 * (∫ x, psi0 x) * Real.sqrt P with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0)) hI0)
    (Real.sqrt_nonneg _)
  set W := (N * M) ^ 2 * S + N ^ 2 * M * Real.sqrt G with hW
  have hKM : 2 ^ Kl ≤ M := by
    rw [hKl]
    exact Nat.pow_log_le_self 2 (by omega)
  clear_value Kl P G c W
  -- each block
  have hblock : ∀ k ∈ Finset.range (Kl + 1),
      ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2 ≤ c * ((Kl + 1) * W) := by
    intro k hk
    have hkK : k ≤ Kl := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h2k : (2 : ℝ) ^ k ≤ M := by
      have : 2 ^ k ≤ M := (Nat.pow_le_pow_right (by norm_num) hkK).trans hKM
      exact_mod_cast this
    have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
    have hLk : N * 2 ^ k ≤ X * T := (mul_le_mul_of_nonneg_left h2k hN0).trans hNM
    have hMk : (2 : ℝ) ^ (k + 1) ≤ T ^ ϖ := by
      rw [pow_succ]
      linarith
    have hS := hB R χ t M k hS31 hQ hT ht hN hX hLk hMk
    rw [← hPdef, ← hG] at hS
    have hAk : ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2 =
        2 * CJ 0 * N ^ 2 / 2 ^ k * ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 := by
      unfold Ak
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp
    have hck : 0 ≤ 2 * CJ 0 * N ^ 2 / 2 ^ k :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0)) (sq_nonneg _)) (by positivity)
    have hk1 : (k : ℝ) + 1 ≤ Kl + 1 := by
      have : (k : ℝ) ≤ Kl := by exact_mod_cast hkK
      linarith
    have hinner : N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * S + N ^ 2 * 2 ^ k * Real.sqrt G ≤ W := by
      rw [hW]
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ h2k0.le h2k 2
      have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
      have e1 : (N * M) ^ 2 = N ^ 2 * (M : ℝ) ^ 2 := by ring
      rw [e1]
      have hA : N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * S ≤ N ^ 2 * (M : ℝ) ^ 2 * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hN2) hS0
      have hB' : N ^ 2 * 2 ^ k * Real.sqrt G ≤ N ^ 2 * M * Real.sqrt G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2k hN2) (Real.sqrt_nonneg _)
      linarith
    have hinner0 : 0 ≤ N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * S + N ^ 2 * 2 ^ k * Real.sqrt G := by
      have := Real.sqrt_nonneg G
      positivity
    rw [hAk]
    calc 2 * CJ 0 * N ^ 2 / 2 ^ k * ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2
        ≤ 2 * CJ 0 * N ^ 2 / 2 ^ k *
          (32 * (k + 1) * (∫ x, psi0 x) * Real.sqrt P *
            (((2 : ℝ) ^ k) ^ 3 * S + ((2 : ℝ) ^ k) ^ 2 * Real.sqrt G)) :=
          mul_le_mul_of_nonneg_left hS hck
      _ = c * (((k : ℝ) + 1) * (N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * S + N ^ 2 * 2 ^ k * Real.sqrt G)) := by
          rw [hc, block_alg_one _ _ _ _ _ _ _ _ h2k0.ne']
          ring
      _ ≤ c * (((Kl : ℝ) + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          exact mul_le_mul hk1 hinner hinner0 (by positivity)
      _ = c * ((Kl + 1) * W) := by ring
  -- the sum over the blocks
  have hmain : 3 * ∑ k ∈ Finset.range (Kl + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
      (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) ≤
      192 * CJ 0 * (∫ x, psi0 x) * (Kl + 1) ^ 2 * Real.sqrt P * W := by
    rw [Finset.sum_congr rfl fun k _ => sum_blk M k (Ak N R χ t X k)]
    calc 3 * ∑ k ∈ Finset.range (Kl + 1), ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2
        ≤ 3 * ∑ _k ∈ Finset.range (Kl + 1), c * ((Kl + 1) * W) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (by norm_num)
      _ = 192 * CJ 0 * (∫ x, psi0 x) * (Kl + 1) ^ 2 * Real.sqrt P * W := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
          push_cast
          ring
  exact h72.trans (add_le_add (add_le_add (add_le_add hmain le_rfl) le_rfl) le_rfl)

/-- **Their (11.2) at `q = 1`, in explicit form**: under the hypotheses of `S3_le_blocks_one`, `NM ≤ XT` turns its
bound into `S₃ ≤ 192C_J(0)∫ψ̃₀(log₂M + 1)²√(2CT^εX³S)((XT)²S + XTN√G)` plus the same errors. -/
theorem S3_le_112_one (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [DecidableEq ι] {N : ℝ} {R : Finset ι}
      {χ : ι → DirichletCharacter ℂ 1} (t : ι → ℝ) {X T S z : ℝ} {M Kt : ℕ} (K' : ℕ),
      S31 R χ t ≤ S → 0 ≤ z → (∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z) →
      Q₀ ≤ T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → 1 ≤ M → 2 ≤ Kt →
      N * M ≤ X * T → 2 * (M : ℝ) ≤ T ^ ϖ →
      S3 1 N R χ t ≤ 192 * CJ 0 * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
          Real.sqrt (2 * C * T ^ ε * X ^ 3 * S) * ((X * T) ^ 2 * S + X * T * N * Real.sqrt (Gq R χ t X K)) +
        3 * (2 * (M : ℝ)) ^ 3 * E71 1 N R X K' + R.card * |muP 1 N - mu0 1 N| ^ 3 +
        (3 * (R.card : ℝ) ^ 3 * tauM N 1 T M Kt * (2 * N + 1 + z + tauM N 1 T M Kt) ^ 2 +
          3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2) := by
  obtain ⟨C, Q₀, hC0, hB⟩ := S3_le_blocks_one.{u} hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι _ N R χ t X T S z M Kt K' hS31 hz0 hz hQ hT ht hN hX hM hKt hNM hMϖ
  have h := hB t K' hS31 hz0 hz hQ hT ht hN hX hM hKt hNM hMϖ
  have hX0 : 0 < X := by linarith
  have hS31_0 : 0 ≤ S31 R χ t := setIntegral_nonneg measurableSet_Icc fun v _ =>
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hS0 : 0 ≤ S := hS31_0.trans hS31
  have hNM0 : 0 ≤ N * M := mul_nonneg hN.le (by positivity)
  have hpre : 0 ≤ 192 * CJ 0 * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
      Real.sqrt (2 * C * T ^ ε * X ^ 3 * S) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0))
      (integral_nonneg psi0_nonneg)) (by positivity)) (Real.sqrt_nonneg _)
  have hW : (N * M) ^ 2 * S + N ^ 2 * M * Real.sqrt (Gq R χ t X K) ≤
      (X * T) ^ 2 * S + X * T * N * Real.sqrt (Gq R χ t X K) := by
    have h1 : (N * M) ^ 2 ≤ (X * T) ^ 2 := pow_le_pow_left₀ hNM0 hNM 2
    have hs := Real.sqrt_nonneg (Gq R χ t X K)
    have hA : (N * M) ^ 2 * S ≤ (X * T) ^ 2 * S := mul_le_mul_of_nonneg_right h1 hS0
    have hB' : N ^ 2 * M * Real.sqrt (Gq R χ t X K) ≤ X * T * N * Real.sqrt (Gq R χ t X K) := by
      have : N ^ 2 * (M : ℝ) ≤ X * T * N := by nlinarith
      exact mul_le_mul_of_nonneg_right this hs
    linarith
  have := mul_le_mul_of_nonneg_left hW hpre
  linarith

end ZetaGMBlock

#print axioms ZetaGMBlock.lemma91_gen
#print axioms ZetaGMBlock.S31_le_one
#print axioms ZetaGMBlock.integral_sum_fb_le_S31
#print axioms ZetaGMBlock.block_le_one
#print axioms ZetaGMBlock.sum_blk_It_le_one
#print axioms ZetaGMBlock.S3_le_blocks_one
#print axioms ZetaGMBlock.S3_le_112_one
