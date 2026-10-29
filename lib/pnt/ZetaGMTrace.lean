/-
# Guth–Maynard's cubic trace at `q = 1`, with several points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The library's Chen–Gupta–Li files (`LinnikCGL*`) run Guth and Maynard's argument (arXiv:2405.20552) with characters
modulo `q`, at one point per character (`Set.InjOn χ R`). Modulo `1` there is one character, and Guth–Maynard's large
values lie at many heights `t_i`. This file proves the identities of the cubic trace that `LinnikCGLTrace`,
`LinnikCGLDiag`, `LinnikCGLTrunc` and `LinnikCGLP72` prove at one point per character, at `q = 1` for any points.

What changes. At one point per character the term `m = 0` of an off-diagonal Gram entry vanishes by orthogonality.
At `q = 1` it is `Z(i, k) = Nĥ_{t_i−t_k}(0)` (`Zm`). Guth and Maynard bound it by separation, in their §5: "Since W is
T^ε-separated, we see that if t₁ ≠ t₂, by Lemma 4.2 we have |ĥ_{t₁−t₂}(0)| ≪_ε T^{−100}." Here `ĥ_τ(0) = H(1 + iτ)`
(`fourier_Wt_zero_eq`), the Mellin transform of `w²` (`LinnikCGLMellin.H`), whose decay on vertical lines
(`LinnikCGLMellin.exists_H_bound`) gives `|Z(i, k)| ≤ NB(1 + X)^{−(K+3)}` for points `X` apart (`norm_Zm_le_sep`). The
identities carry `Z` as an explicit error.

Plain statements, with `q = 1`, `N > 0`, `F(i, k)` the terms `m ≠ 0` of a Gram entry (`LinnikCGLTrace.Fm`),
`F′ = F + Z` (`Fp`), `S₃ = X − 3μ₀‖E‖_F²` (`LinnikCGLS23.S3`) and `μ`, `μ₀` as in `LinnikCGLDiag`.
* `char_one_apply`, `sum_range_one_mul_star`: a character modulo `1` is `1` everywhere, so
  `Σ_{a<1}χ(a)conj(ψ(a)) = 1`.
* `norm_Wt_le`, `integrable_wsq`, `integral_wsq`, `norm_hhat_zero_le`: `|W_τ(u)| ≤ w(u)²`, and `|ĥ_τ(0)| ≤ ∫w² ≤ 1`.
* `fourier_Wt_zero_eq`, `exists_hhat_zero_bound`: `ĥ_τ(0) = H(1 + iτ)`, and for every `K` there is `B ≥ 0` with
  `(1 + |τ|)^{K+3}|ĥ_τ(0)| ≤ B`.
* `Em_eq_gen`: for any `q ≥ 1` and any points,
  `E′(i, k) = N^{iτ}(F(i, k) + [i ≠ k](N/q)ĥ_τ(0)Σ_{a<q}χ_i(a)conj(χ_k(a)))`, `τ = t_i − t_k`:
  `LinnikCGLTrace.Em_eq` without its orthogonality step.
* `Em_eq_one`, `S3_eq_Fp`: at `q = 1`, `E′(i, k) = N^{iτ}F′(i, k)`, and `S₃ = Re Σ F′(i, j)F′(j, k)F′(k, i)` over the
  triples that are not all equal.
* `Zm_diag`, `Fp_diag`, `Fm_diag_one`, `norm_Fp_le`, `norm_Zm_le`, `norm_Zm_le_sep`: `Z(i, i) = 0`,
  `F′(i, i) = F(i, i) = μ − μ₀`, `|F′| ≤ 2N + 1`, `|Z| ≤ N`, and `|Z(i, k)| ≤ NB(1 + X)^{−(K+3)}` when `i ≠ k` gives
  `|t_i − t_k| ≥ X`.
* `S3_eq_all_one`: if `|Z| ≤ z` on `R`, then `|S₃ − (Re Σ_{i,j,k∈R}F(i, j)F(j, k)F(k, i) − |R|(μ − μ₀)³)| ≤
  3|R|³z(2N + 1 + z)²` (`LinnikCGLDiag.S3_eq_all`, which has no error at one point per character).
* `S3_trunc_one`: `LinnikCGLTrunc.S3_trunc` at `q = 1`, with `2N + 1 + z` in place of `2N + 1` and the error above.
* `prop72_one`: `LinnikCGLP72.prop72` at `q = 1`, with the same two changes.

The file imports `LinnikCGLHB101.lean`.
-/
import LinnikCGLHB101

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace ZetaGMTrace

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLP71 LinnikCGLSym LinnikCGLP72

/-! ### Characters modulo `1` -/

/-- Modulo `1` every character is `1` at every residue. -/
lemma char_one_apply (χ : DirichletCharacter ℂ 1) (a : ZMod 1) : χ a = 1 := by
  rw [Subsingleton.elim a 1, map_one]

/-- `Σ_{a<1}χ(a)conj(ψ(a)) = 1` for characters `χ` and `ψ` modulo `1`. -/
lemma sum_range_one_mul_star (χ ψ : DirichletCharacter ℂ 1) :
    ∑ a ∈ Finset.range 1, χ a * star (ψ a) = 1 := by
  simp [char_one_apply]

/-! ### `ĥ_τ(0)` -/

lemma wsq_nonneg (u : ℝ) : 0 ≤ wsq u := by unfold wsq; positivity

/-- `|W_τ(u)| ≤ w(u)²`. -/
lemma norm_Wt_le (τ u : ℝ) : ‖Wt τ u‖ ≤ wsq u := by
  unfold Wt Wc
  rcases le_or_gt u 0 with hu | hu
  · rw [wsq_eq_zero (Or.inl (by linarith))]; simp
  · rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp [abs_of_nonneg (wsq_nonneg u)]

lemma integrable_wsq : Integrable wsq :=
  contDiff_wsq.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Icc 1 2) isCompact_Icc fun u hu => by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      exact wsq_eq_zero (hu.elim (fun h => Or.inl h.le) fun h => Or.inr h.le))

/-- `∫w² = ∫_1^2 w²`. -/
lemma integral_wsq : ∫ u, wsq u = ∫ u in (1 : ℝ)..2, wCGL u ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
  exact wsq_eq_zero (hu.elim Or.inl fun h => Or.inr h.le)

lemma fourier_Wt_zero_eq_integral (τ : ℝ) : 𝓕 (Wt τ) 0 = ∫ u : ℝ, Wt τ u := by
  rw [Real.fourier_real_eq]; simp

/-- `|ĥ_τ(0)| ≤ ∫_1^2 w² ≤ 1`. -/
lemma norm_hhat_zero_le (τ : ℝ) : ‖𝓕 (Wt τ) 0‖ ≤ 1 := by
  rw [fourier_Wt_zero_eq_integral]
  calc ‖∫ u : ℝ, Wt τ u‖ ≤ ∫ u, wsq u :=
        norm_integral_le_of_norm_le integrable_wsq (Eventually.of_forall (norm_Wt_le τ))
    _ = ∫ u in (1 : ℝ)..2, wCGL u ^ 2 := integral_wsq
    _ ≤ 1 := integral_w_sq_le_one

/-- `ĥ_τ(0) = H(1 + iτ)`: both are `∫ u^{iτ}w(u)² du`, the weight vanishing for `u ≤ 1`. -/
lemma fourier_Wt_zero_eq (τ : ℝ) : 𝓕 (Wt τ) 0 = H (1 + τ * I) := by
  rw [fourier_Wt_zero_eq_integral, ← mellin_Wt τ 1]
  unfold mellin
  simp only [sub_self, Complex.cpow_zero, one_smul]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
  rw [mem_Ioi, not_lt] at hu
  unfold Wt Wc
  rw [wsq_eq_zero (Or.inl (by linarith))]
  simp

/-- **The decay of `ĥ_τ(0)`**: for every `K` there is `B ≥ 0` with `(1 + |τ|)^{K+3}|ĥ_τ(0)| ≤ B`
(`LinnikCGLMellin.exists_H_bound` on the line `Re s = 1`). -/
lemma exists_hhat_zero_bound (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, (1 + |τ|) ^ (K + 3) * ‖𝓕 (Wt τ) 0‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_H_bound K (S := 1) zero_le_one
  refine ⟨B, hB0, fun τ => ?_⟩
  have h := hB 1 τ (by norm_num)
  rw [fourier_Wt_zero_eq]
  simpa using h

/-! ### The Gram entries at `q = 1` -/

/-- **A Gram entry less its main term, for any points** (`LinnikCGLTrace.Em_eq` without its orthogonality step):
`E′(i, k) = N^{iτ}(F(i, k) + [i ≠ k](N/q)ĥ_τ(0)Σ_{a<q}χ_i(a)conj(χ_k(a)))`, `τ = t_i − t_k`. -/
theorem Em_eq_gen {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) :
    Em q N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * (Fm N χ t i k +
      if i = k then 0 else ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) 0 *
        ∑ a ∈ Finset.range q, χ i a * star (χ k a)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsplit : ∀ a : ℕ, (∑' m : ℤ, ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) *
      Complex.exp (2 * π * I * m * (a / q))) = ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) 0 +
      ∑' m : ℤ, if m = 0 then 0 else ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) *
        Complex.exp (2 * π * I * m * (a / q)) := by
    intro a
    rw [(summable_poisson _ hN hq a).tsum_eq_add_tsum_ite 0]
    congr 1
    simp
  have hsum : ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) * ∑' m : ℤ, ((N / q : ℝ) : ℂ) *
      𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) =
      ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) 0 * ∑ a ∈ Finset.range q, χ i a * star (χ k a) +
      Fm N χ t i k := by
    unfold Fm
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsplit a]; ring
  unfold Em
  rw [gram_poisson hN χ t i k, hsum]
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_left rfl, ite_eq_left rfl, sum_range_mul_star_self]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul, fourier_Wt_zero, add_zero]
    unfold mu0
    push_cast
    ring
  · rw [ite_eq_right hik, ite_eq_right hik, sub_zero]
    ring

/-- **The term `m = 0` of an off-diagonal Gram entry** at `q = 1`: `Z(i, k) = Nĥ_{t_i−t_k}(0)` for `i ≠ k`, and
`Z(i, i) = 0`. -/
def Zm {ι : Type*} [DecidableEq ι] (N : ℝ) (t : ι → ℝ) (i k : ι) : ℂ :=
  if i = k then 0 else (N : ℂ) * 𝓕 (Wt (t i - t k)) 0

/-- `F′ = F + Z`: the terms `m ≠ 0` of a Gram entry, with the term `m = 0` of the off-diagonal entries. -/
def Fp {ι : Type*} [DecidableEq ι] (N : ℝ) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) (i k : ι) : ℂ :=
  Fm N χ t i k + Zm N t i k

/-- **A Gram entry less its main term at `q = 1`**: `E′(i, k) = N^{iτ}F′(i, k)`. -/
theorem Em_eq_one {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ 1)
    (t : ι → ℝ) (i k : ι) :
    Em 1 N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * Fp N χ t i k := by
  rw [Em_eq_gen hN χ t i k, sum_range_one_mul_star]
  unfold Fp Zm
  split_ifs <;> simp

/-- **`S₃` at `q = 1`**: `S₃ = Re Σ F′(i, j)F′(j, k)F′(k, i)` over the triples of `R` that are not all equal. -/
theorem S3_eq_Fp {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) :
    S3 1 N R χ t = (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      if i = j ∧ j = k then 0 else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i).re := by
  rw [S3_eq_cube]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · rw [Em_eq_one hN χ t i j, Em_eq_one hN χ t j k, Em_eq_one hN χ t k i]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hph : (N : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I) * (N : ℂ) ^ (((t j - t k : ℝ) : ℂ) * I) *
        (N : ℂ) ^ (((t k - t i : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0,
        show ((t i - t j : ℝ) : ℂ) * I + ((t j - t k : ℝ) : ℂ) * I + ((t k - t i : ℝ) : ℂ) * I = 0 by
          push_cast; ring]
      exact Complex.cpow_zero _
    linear_combination (Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) * hph

lemma Zm_diag {ι : Type*} [DecidableEq ι] (N : ℝ) (t : ι → ℝ) (i : ι) : Zm N t i i = 0 := by simp [Zm]

/-- `F′(i, i) = μ − μ₀`. -/
lemma Fp_diag {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ)
    (i : ι) : Fp N χ t i i = ((muP 1 N - mu0 1 N : ℝ) : ℂ) := by
  have h := Em_eq_one hN χ t i i
  unfold Em at h
  rw [ite_eq_left rfl, gramP_diag hN χ t i] at h
  simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul] at h
  rw [← h]; push_cast; ring

/-- `F(i, i) = μ − μ₀` at `q = 1`. -/
lemma Fm_diag_one {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ 1)
    (t : ι → ℝ) (i : ι) : Fm N χ t i i = ((muP 1 N - mu0 1 N : ℝ) : ℂ) := by
  have h := Fp_diag hN χ t i
  unfold Fp at h
  rwa [Zm_diag, add_zero] at h

/-- `|F′(i, k)| ≤ 2N + 1` (`|F′| = |E′| ≤ |G| + μ₀`). -/
lemma norm_Fp_le {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ 1)
    (t : ι → ℝ) (i k : ι) : ‖Fp N χ t i k‖ ≤ 2 * N + 1 := by
  have h := Em_eq_one hN χ t i k
  have hph : ‖(N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have hE : ‖Em 1 N χ t i k‖ = ‖Fp N χ t i k‖ := by rw [h, norm_mul, hph, one_mul]
  rw [← hE]
  unfold Em
  have hmu := mu0_le 1 hN.le
  have hmu0 := mu0_nonneg 1 hN.le
  calc ‖gramP N χ t i k - (if i = k then (mu0 1 N : ℂ) else 0)‖
      ≤ ‖gramP N χ t i k‖ + ‖(if i = k then (mu0 1 N : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ (N + 1) + N := by
        refine add_le_add (norm_gramP_le hN χ t i k) ?_
        split_ifs
        · rw [Complex.norm_real, Real.norm_of_nonneg hmu0]; exact hmu
        · rw [norm_zero]; exact hN.le
    _ = 2 * N + 1 := by ring

/-- `|Z(i, k)| ≤ N`. -/
lemma norm_Zm_le {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 ≤ N) (t : ι → ℝ) (i k : ι) : ‖Zm N t i k‖ ≤ N := by
  unfold Zm
  split_ifs
  · rw [norm_zero]; exact hN
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN]
    exact mul_le_of_le_one_right hN (norm_hhat_zero_le _)

/-- **`Z` for separated points**: with `B` as in `exists_hhat_zero_bound`, if `i ≠ k` gives `|t_i − t_k| ≥ X ≥ 0`,
then `|Z(i, k)| ≤ NB(1 + X)^{−(K+3)}`. -/
lemma norm_Zm_le_sep {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 ≤ N) (t : ι → ℝ) {K : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ τ : ℝ, (1 + |τ|) ^ (K + 3) * ‖𝓕 (Wt τ) 0‖ ≤ B) {X : ℝ} (hX : 0 ≤ X) {i k : ι}
    (hik : i ≠ k → X ≤ |t i - t k|) : ‖Zm N t i k‖ ≤ N * B * ((1 + X) ^ (K + 3))⁻¹ := by
  unfold Zm
  split_ifs with h
  · rw [norm_zero]; positivity
  · have h1 := hB (t i - t k)
    have hX' := hik h
    have hpos : 0 < (1 + X) ^ (K + 3) := by positivity
    have hle : (1 + X) ^ (K + 3) ≤ (1 + |t i - t k|) ^ (K + 3) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2 : ‖𝓕 (Wt (t i - t k)) 0‖ ≤ B * ((1 + X) ^ (K + 3))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖𝓕 (Wt (t i - t k)) 0‖ * (1 + X) ^ (K + 3)
          ≤ ‖𝓕 (Wt (t i - t k)) 0‖ * (1 + |t i - t k|) ^ (K + 3) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = (1 + |t i - t k|) ^ (K + 3) * ‖𝓕 (Wt (t i - t k)) 0‖ := by ring
        _ ≤ B := h1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hN

/-! ### `S₃` over all triples, and the truncation -/

/-- The sum over the triples that are not all equal is the sum over all triples less the diagonal, where
`F(i, i) = μ − μ₀`. -/
lemma sum_nae_eq {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) :
    (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i) =
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i) -
        ∑ _i ∈ R, ((muP 1 N - mu0 1 N : ℝ) : ℂ) ^ 3 := by
  have hdiag : ∀ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      (if i = j ∧ j = k then Fm N χ t i j * Fm N χ t j k * Fm N χ t k i else 0) =
      ((muP 1 N - mu0 1 N : ℝ) : ℂ) ^ 3 := by
    intro i hi
    have h1 : ∀ j ∈ R, ∑ k ∈ R, (if i = j ∧ j = k then Fm N χ t i j * Fm N χ t j k * Fm N χ t k i else 0) =
        if i = j then Fm N χ t i i * Fm N χ t i i * Fm N χ t i i else 0 := by
      intro j _
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, Finset.sum_eq_single_of_mem i hi]
        · rw [ite_eq_left ⟨rfl, rfl⟩]
        · intro k _ hk; exact ite_eq_right fun h => hk h.2.symm
      · rw [ite_eq_right hij]; exact Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hij h.1
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq R i, ite_eq_left hi, Fm_diag_one hN χ t i]
    ring
  rw [← Finset.sum_congr rfl hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- **`S₃` over all triples at `q = 1`** (`LinnikCGLDiag.S3_eq_all` with the terms `m = 0` as an error): if
`|Z(i, k)| ≤ z` on `R`, then `|S₃ − (Re Σ_{i,j,k∈R}F(i, j)F(j, k)F(k, i) − |R|(μ − μ₀)³)| ≤ 3|R|³z(2N + 1 + z)²`. -/
theorem S3_eq_all_one {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : ∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z) :
    |S3 1 N R χ t - ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
      R.card * (muP 1 N - mu0 1 N) ^ 3)| ≤ 3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2 := by
  have hW : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
      R.card * (muP 1 N - mu0 1 N) ^ 3 = (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
        if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re := by
    rw [sum_nae_eq hN R χ t, Complex.sub_re, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [show (R.card : ℂ) * ((muP 1 N - mu0 1 N : ℝ) : ℂ) ^ 3 = ((R.card * (muP 1 N - mu0 1 N) ^ 3 : ℝ) : ℂ) by
      push_cast; ring]
    exact (Complex.ofReal_re _).symm
  rw [hW, S3_eq_Fp hN R χ t, ← Complex.sub_re]
  have hterm : ∀ i ∈ R, ∀ j ∈ R, ∀ k ∈ R,
      ‖(if i = j ∧ j = k then (0 : ℂ) else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) -
        (if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i)‖ ≤
        3 * z * (2 * N + 1 + z) ^ 2 := by
    intro i hi j hj k hk
    split_ifs
    · simp only [sub_self, norm_zero]; positivity
    · have hd : ∀ a ∈ R, ∀ b ∈ R, ‖Fp N χ t a b - Fm N χ t a b‖ ≤ z := fun a ha b hb => by
        unfold Fp; rw [add_sub_cancel_left]; exact hz a ha b hb
      exact norm_cube_sub_le (hd i hi j hj) (hd j hj k hk) (hd k hk i hi) (norm_Fp_le hN χ t i j)
        (norm_Fp_le hN χ t j k) (norm_Fp_le hN χ t k i) hz0
  calc |((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          if i = j ∧ j = k then (0 : ℂ) else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) -
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re|
      ≤ ‖(∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          if i = j ∧ j = k then (0 : ℂ) else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) -
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          ((if i = j ∧ j = k then (0 : ℂ) else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) -
            (if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i))‖ := by
        simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          ‖(if i = j ∧ j = k then (0 : ℂ) else Fp N χ t i j * Fp N χ t j k * Fp N χ t k i) -
            (if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ _i ∈ R, ∑ _j ∈ R, ∑ _k ∈ R, 3 * z * (2 * N + 1 + z) ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
          hterm i hi j hj k hk
    _ = 3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The truncation in `m` at `q = 1`** (`LinnikCGLTrunc.S3_trunc`): for `N > 0`, points `|t_i| ≤ T`, `M ≥ 1`,
`K ≥ 2` and `|Z| ≤ z` on `R`, `|S₃ − (Re Σ_{0<|m_i|≤M}I′(m⃗) − |R|(μ − μ₀)³)| ≤
3|R|³τ_M(2N + 1 + z + τ_M)² + 3|R|³z(2N + 1 + z)²`. -/
theorem S3_trunc_one {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) {T : ℝ} (ht : ∀ i ∈ R, |t i| ≤ T) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 2 ≤ K) {z : ℝ} (hz0 : 0 ≤ z) (hz : ∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z) :
    |S3 1 N R χ t - ((∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, Ip N R χ t m₁ m₂ m₃).re -
        R.card * (muP 1 N - mu0 1 N) ^ 3)| ≤
      3 * (R.card : ℝ) ^ 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 +
        3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2 := by
  rcases R.eq_empty_or_nonempty with hR | ⟨i₀, hi₀⟩
  · subst hR; simp [S3, X3, frobOff, Ip]
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (ht i₀ hi₀)
  have hτ0 : 0 ≤ tauM N 1 T M K := by unfold tauM; have := CF_nonneg K; have := Z2_nonneg; positivity
  have htail : ∀ i ∈ R, ∀ k ∈ R, ‖Fm N χ t i k - FmT M N χ t i k‖ ≤ tauM N 1 T M K := by
    intro i hi k hk
    refine (norm_Fm_sub_FmT_le hN χ t i k hM hK).trans ?_
    unfold tauM
    have hik : |t i - t k| ≤ 2 * T := by
      calc |t i - t k| ≤ |t i| + |t k| := abs_sub _ _
        _ ≤ T + T := add_le_add (ht i hi) (ht k hk)
        _ = 2 * T := by ring
    have := CF_nonneg K
    have := Z2_nonneg
    gcongr
  have hA : ∀ i ∈ R, ∀ k ∈ R, ‖Fm N χ t i k‖ ≤ 2 * N + 1 + z := by
    intro i hi k hk
    have e : Fm N χ t i k = Fp N χ t i k - Zm N t i k := by unfold Fp; ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_Fp_le hN χ t i k) (hz i hi k hk))
  have hS3 := S3_eq_all_one hN R χ t hz0 hz
  rw [← sum_FmT_cube]
  have e : S3 1 N R χ t - ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i).re -
      R.card * (muP 1 N - mu0 1 N) ^ 3) =
      (S3 1 N R χ t - ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
        R.card * (muP 1 N - mu0 1 N) ^ 3)) +
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re := by
    simp only [Finset.sum_sub_distrib, Complex.sub_re]; ring
  rw [e]
  have htr : |(∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
      FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re| ≤
      3 * (R.card : ℝ) ^ 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 := by
    calc |(∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
          FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re|
        ≤ ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
          FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ‖Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
          FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact norm_sum_le _ _
      _ ≤ ∑ _i ∈ R, ∑ _j ∈ R, ∑ _k ∈ R, 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
            norm_cube_sub_le (htail i hi j hj) (htail j hj k hk) (htail k hk i hi) (hA i hi j hj)
              (hA j hj k hk) (hA k hk i hi) hτ0
      _ = 3 * (R.card : ℝ) ^ 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  calc |S3 1 N R χ t - ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
        R.card * (muP 1 N - mu0 1 N) ^ 3) +
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re|
      ≤ |S3 1 N R χ t - ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
          R.card * (muP 1 N - mu0 1 N) ^ 3)| +
        |(∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
          FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Their Proposition 7.2 at `q = 1`** (`LinnikCGLP72.prop72`, with `S3_trunc_one` for the truncation): for
`N > 0`, points `|t_i| ≤ T`, `M ≥ 1`, `K ≥ 2`, `X > 0`, any `K′` and `|Z| ≤ z` on `R`, `S₃` is at most
`LinnikCGLP72.prop72`'s bound with `2N + 1 + z` in place of `2N + 1`, plus `3|R|³z(2N + 1 + z)²`. -/
theorem prop72_one {ι : Type*} [DecidableEq ι] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ 1) (t : ι → ℝ) {T : ℝ} (ht : ∀ i ∈ R, |t i| ≤ T)
    {M K : ℕ} (hM : 1 ≤ M) (hK : 2 ≤ K) {X : ℝ} (hX : 0 < X) (K' : ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : ∀ i ∈ R, ∀ k ∈ R, ‖Zm N t i k‖ ≤ z) :
    S3 1 N R χ t ≤ 3 * ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
        (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) +
      3 * (2 * (M : ℝ)) ^ 3 * E71 1 N R X K' + R.card * |muP 1 N - mu0 1 N| ^ 3 +
      (3 * (R.card : ℝ) ^ 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 +
        3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2) := by
  set B := boxM M with hBdef
  have htr := S3_trunc_one hN R χ t ht hM hK hz0 hz
  have hS : S3 1 N R χ t ≤ ‖∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃‖ +
      R.card * |muP 1 N - mu0 1 N| ^ 3 +
      (3 * (R.card : ℝ) ^ 3 * tauM N 1 T M K * (2 * N + 1 + z + tauM N 1 T M K) ^ 2 +
        3 * (R.card : ℝ) ^ 3 * z * (2 * N + 1 + z) ^ 2) := by
    have h1 := (abs_le.1 htr).2
    have h2 := Complex.re_le_norm (∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃)
    have h4 : -((muP 1 N - mu0 1 N) ^ 3) ≤ |muP 1 N - mu0 1 N| ^ 3 := by
      rw [← abs_pow]; exact neg_le_abs _
    have h3 : -(R.card * (muP 1 N - mu0 1 N) ^ 3) ≤ R.card * |muP 1 N - mu0 1 N| ^ 3 := by
      have := (Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)
      nlinarith
    linarith
  have hsum : ‖∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃‖ ≤
      3 * ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
        (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun m₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun m₂ _ => norm_sum_le _ _)) ?_
    exact sum_le_three_mul B (fun a b c => ‖Ip N R χ t a b c‖) (fun a b c => norm_nonneg _)
      fun a b c => by rw [Ip_cyc]
  have hpt : ∀ m₁ ∈ B, ∀ m₂ ∈ B, ∀ m₃ ∈ B,
      (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) ≤
        (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
          E71 1 N R X K' := by
    intro m₁ _ m₂ hm₂ m₃ _
    have hE0 : 0 ≤ E71 1 N R X K' := by unfold E71; have := CJ_nonneg K'; positivity
    split_ifs
    · exact Ip_le_It hN R χ t m₁ m₂ m₃ hX (M₂ := (2 : ℝ) ^ Nat.log 2 m₂.natAbs) (by positivity)
        (two_pow_log_le (mem_boxM hm₂).1) K'
    · linarith
  have hboxE : ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, E71 1 N R X K' = (2 * (M : ℝ)) ^ 3 * E71 1 N R X K' := by
    simp only [Finset.sum_const, hBdef, card_boxM, nsmul_eq_mul]; push_cast; ring
  have hmain : ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
      (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) ≤
      ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
        (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) +
        (2 * (M : ℝ)) ^ 3 * E71 1 N R X K' := by
    calc ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0)
        ≤ ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
            ((if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
              E71 1 N R X K') :=
          Finset.sum_le_sum fun m₁ h₁ => Finset.sum_le_sum fun m₂ h₂ => Finset.sum_le_sum fun m₃ h₃ =>
            hpt m₁ h₁ m₂ h₂ m₃ h₃
      _ = ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
            (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
            ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, E71 1 N R X K' := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hboxE, hBdef, sum_Ak_regroup]
  have hfin := hS.trans (add_le_add (add_le_add
    (hsum.trans (mul_le_mul_of_nonneg_left hmain (by norm_num))) le_rfl) le_rfl)
  refine hfin.trans (le_of_eq ?_)
  ring

end ZetaGMTrace

#print axioms ZetaGMTrace.sum_range_one_mul_star
#print axioms ZetaGMTrace.norm_hhat_zero_le
#print axioms ZetaGMTrace.fourier_Wt_zero_eq
#print axioms ZetaGMTrace.exists_hhat_zero_bound
#print axioms ZetaGMTrace.Em_eq_gen
#print axioms ZetaGMTrace.Em_eq_one
#print axioms ZetaGMTrace.S3_eq_Fp
#print axioms ZetaGMTrace.Fm_diag_one
#print axioms ZetaGMTrace.norm_Fp_le
#print axioms ZetaGMTrace.norm_Zm_le_sep
#print axioms ZetaGMTrace.S3_eq_all_one
#print axioms ZetaGMTrace.S3_trunc_one
#print axioms ZetaGMTrace.prop72_one
