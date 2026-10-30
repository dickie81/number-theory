/-
# The off-diagonal mass of the Gram matrix, explicitly

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`LinnikCGLPair.norm_gram_le` bounds one Gram entry. This file sums the squares over the pairs, with the
large polynomial put back, into an explicit bound on `‖E‖_F² = Σ_{i≠k}|G(i, k)|²` (`frobOff`), the
quantity of the displayed hypothesis `CGLS2`. It is the proof of Chen–Gupta–Li's Proposition 6.1 from their
Lemma 6.2, for points whose characters are distinct or which are at least `1` apart, before `Z` and `K` are
chosen.

Plain statement (`frobOff_le`). Let two points of `R` have distinct characters or be at least `1` apart,
`|t_i| ≤ T`, `N > 0`, `S ⊆ [2, N′]`, and
`|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥ V > 0` for every `i ∈ R`. Let `Z, K ≥ 1`, and `d(k) ≤ τ` for `k ≤ N′Z`. Then
`‖E‖_F² ≤ N·Q₀(q)²I_H²·|R|·V^{−2}L(N′Z)·τ·Σ_{n∈S}|b_n|²·H_Z + |R|²B² + 2N²P_H`, where `I_H = ∫|H(1/2 + iu)| du`,
`L(X)` is
the large-sieve factor `LSX`, `H_Z = Σ_{m≤Z}1/m`, `Q₀(q)` is `Q0` of `LinnikCGLPair`, and `B` is the tail bound
at `|τ| = 2T` (`Bmax`), and `P_H = Σ_{i≠k, χ_i=χ_k}|H(1 + i(t_i − t_k))|²` (`resP`), the residues of the principal
Gram entries, which vanish at one point per character (`resP_eq_zero_of_injOn`).

Their proof of Proposition 6.1 says (p. 21): "Now we proceed with an argument
based on the mean value theorem. Notice that |Σ_{n∼N} w(n/N)b_n n^{it₂}χ₂(n)| ≥ N^σ for (t₂, χ₂) ∈ W." It multiplies
each dual sum by the large polynomial, takes "some coefficients c_l depending on (t₁, χ₁) such that
|c_l^{(t₁,χ₁)}| ⪅ 1, by the divisor bound", and applies the mean value theorem with characters. Their Remark 6.3: "In
particular, we reintroduce our large Dirichlet polynomial here whereas their proof only depended on the 1-separation
of W." The library does the same with the product trick, in its squared form. Three differences: the dual sum
is not split into dyadic ranges of `m` (its coefficients keep the weight `m^{−1/2}`, whence `H_Z`), `u` is not
truncated (it is integrated against `|H(1/2 + iu)|`, whence `I_H`), and the pairs are not split by `|t₁ − t₂|` (one
`Z` and one `K` serve every pair).

* `sq_le_mul_of_forall`, `two_mul_le_lam`, `integral_sq_le`: Cauchy–Schwarz against a weight, through
  `2hd ≤ λh + hd²/λ` for every `λ > 0`.
* `ls_points`: the large sieve at the points `(χ_i, t_i)`, from `LinnikPoints.large_values_points` on dyadic
  pieces, as `ls_pv_dyadic` is from `large_values_chars_off`.
* `prod_trick_points`: `|E| ≤ |FE|/V` at each point; `FE` is a polynomial on `[2, N′Z]` (`pv_mul`);
  then `ls_points` and `mass_mulCo_le`. `huxley_core` is the same argument for a sum of
  `|E|`, with Cauchy–Schwarz over the points.
* `norm_dualS_pair`, `HZ`, `mass_dualCo_half`: `|D_{ik}(u)|` is the polynomial `Σ_{m≤Z}e_{k,u}(m)χ_i(m)m^{it_i}`
  at the point of `χ_i`, `e_{k,u}(m) = conj(χ_k(m)m^{−1/2+i(u+t_k)})` (`dualS_eq_conj_pv`), and
  `Σ_{m≤Z}|e_{k,u}(m)|² ≤ H_Z`.
* `wH`, `IH`, `Dp`, `sum_Dp_sq_le`: `Σ_{i,k∈R}|D_{ik}(u)|² ≤ |R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z` at every `u`.
* `Bmax`, `gram_sq_le`, `gram_sq_le0`: `|G(i, k)|² ≤ N·Q₀(q)²(∫|H(1/2 + iu)||D_{ik}(u)| du)² + B²` for
  `χ_i ≠ χ_k`; and for `χ_i = χ_k` the same with `2(N|H(1 + i(t_i − t_k))|)²` added
  (`LinnikCGLRefl0.norm_gram_le0`).
* `resT`, `resP`, `resT_nonneg`, `resP_eq_zero_of_injOn`: the residues.
* `frobOff_le`: Cauchy–Schwarz in `u` for each pair, and the sum over the pairs.

The file imports `LinnikCGLPair.lean`, `LinnikCGLRefl0.lean`, `LinnikDual.lean` and `LinnikWeighted.lean`.
-/

import LinnikCGLPair
import LinnikCGLRefl0
import LinnikDual
import LinnikWeighted

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikCGLFrob

open LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLReflect LinnikCGLPair DirichletCharacter LinnikReflect
  LinnikPower

/-! ### Cauchy–Schwarz through a free parameter -/

/-- If `2C ≤ λA + B/λ` for every `λ > 0`, with `A, B, C ≥ 0`, then `C² ≤ AB`. -/
lemma sq_le_mul_of_forall {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ l : ℝ, 0 < l → 2 * C ≤ l * A + B / l) : C ^ 2 ≤ A * B := by
  rcases hC.eq_or_lt with hC0 | hC0
  · rw [← hC0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  rcases hA.eq_or_lt with hA0 | hA0
  · exfalso
    have hl : 0 < (B + 1) / (2 * C) := by positivity
    have h1 := h _ hl
    rw [← hA0, mul_zero, zero_add] at h1
    have h2 : B / ((B + 1) / (2 * C)) = B * (2 * C) / (B + 1) := by field_simp
    have h3 : B * (2 * C) / (B + 1) < 2 * C := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  · have hl : 0 < C / A := div_pos hC0 hA0
    have h1 := h _ hl
    have e1 : C / A * A = C := div_mul_cancel₀ C hA0.ne'
    have e2 : B / (C / A) = B * A / C := by field_simp
    rw [e1, e2] at h1
    have h2 : C ≤ B * A / C := by linarith
    rw [le_div_iff₀ hC0] at h2
    nlinarith

/-- `2hd ≤ λh + hd²/λ` for `h ≥ 0` and `λ > 0`. -/
lemma two_mul_le_lam {h d l : ℝ} (hh : 0 ≤ h) (hl : 0 < l) : 2 * (h * d) ≤ l * h + h * d ^ 2 / l := by
  have h1 : 0 ≤ h * (d - l) ^ 2 / l := by positivity
  have h2 : h * (d - l) ^ 2 / l = l * h + h * d ^ 2 / l - 2 * (h * d) := by
    field_simp; ring
  linarith

/-- **Cauchy–Schwarz against a weight**: `(∫hd)² ≤ (∫h)(∫hd²)` for `h, d ≥ 0` with `h`, `hd` and `hd²`
integrable. -/
lemma integral_sq_le {h d : ℝ → ℝ} (hh : ∀ u, 0 ≤ h u) (hd : ∀ u, 0 ≤ d u) (i1 : Integrable h)
    (i2 : Integrable fun u => h u * d u) (i3 : Integrable fun u => h u * d u ^ 2) :
    (∫ u, h u * d u) ^ 2 ≤ (∫ u, h u) * ∫ u, h u * d u ^ 2 := by
  refine sq_le_mul_of_forall (integral_nonneg hh) (integral_nonneg fun u => mul_nonneg (hh u) (sq_nonneg _))
    (integral_nonneg fun u => mul_nonneg (hh u) (hd u)) fun l hl => ?_
  have h1 : ∫ u, 2 * (h u * d u) ≤ ∫ u, (l * h u + h u * d u ^ 2 / l) :=
    integral_mono (i2.const_mul 2) ((i1.const_mul l).add (i3.div_const l)) fun u => two_mul_le_lam (hh u) hl
  rw [integral_const_mul, integral_add (i1.const_mul l) (i3.div_const l), integral_const_mul, integral_div] at h1
  exact h1

/-! ### The large sieve and the product trick at the points -/

/-- **The large sieve at the points**: for points whose characters are distinct or which are at least `1` apart,
`T ≥ 0` and `|t_i| ≤ T`, `Σ_{i∈R}|Σ_{k∈S_k}c_kχ_i(k)k^{it_i}|² ≤ L(X)Σ|c_k|²` for `S_k ⊆ [2, X]`
(`LinnikPoints.large_values_points` on the dyadic pieces `(2^j, 2^{j+1}]`, `j ≤ log₂ X`, and Cauchy–Schwarz over the
pieces, as in `ls_pv_dyadic`). -/
lemma ls_points {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    {t : ι → ℝ} (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j|) {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ i ∈ R, |t i| ≤ T) {Sk : Finset ℕ} {X : ℕ} (hSk : Sk ⊆ Finset.Icc 2 X) (c : ℕ → ℂ) :
    ∑ i ∈ R, ‖pv Sk c (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ ^ 2 ≤ LSX q T X * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by
  classical
  set J := Nat.log 2 X + 1 with hJ
  set g : ℕ → ℕ := fun k => Nat.log 2 (k - 1) with hg
  have hSk0 : 0 ∉ Sk := fun h => by have := (Finset.mem_Icc.1 (hSk h)).1; omega
  have hmaps : ∀ k ∈ Sk, g k ∈ Finset.range J := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 (hSk hk)
    rw [Finset.mem_range, hJ]
    have : Nat.log 2 (k - 1) ≤ Nat.log 2 X := Nat.log_mono_right (by omega)
    simp only [hg]; omega
  have hpiece : ∀ j ∈ Finset.range J, (Sk.filter fun k => g k = j) ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
    intro j _ k hk
    obtain ⟨hk, hkj⟩ := Finset.mem_filter.1 hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.1 (hSk hk)
    have h1 : 2 ^ Nat.log 2 (k - 1) ≤ k - 1 := Nat.pow_log_le_self 2 (by omega)
    have h2 : k - 1 < 2 ^ (Nat.log 2 (k - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    simp only [hg] at hkj
    rw [hkj] at h1 h2
    rw [pow_succ] at h2
    rw [Finset.mem_Ioc]
    constructor <;> omega
  set s : ι → ℂ := fun i => ((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I with hs
  -- the polynomial as the sum of its pieces, and Cauchy–Schwarz over the pieces
  have hcs : ∀ i, ‖pv Sk c (χ i) (s i)‖ ^ 2 ≤
      J * ∑ j ∈ Finset.range J, ‖pv (Sk.filter fun k => g k = j) c (χ i) (s i)‖ ^ 2 := by
    intro i
    have hsplit : pv Sk c (χ i) (s i) =
        ∑ j ∈ Finset.range J, pv (Sk.filter fun k => g k = j) c (χ i) (s i) := by
      unfold pv
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    rw [hsplit]
    have h1 := norm_sum_le (Finset.range J) fun j => pv (Sk.filter fun k => g k = j) c (χ i) (s i)
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range J)
      (f := fun j => ‖pv (Sk.filter fun k => g k = j) c (χ i) (s i)‖)
    rw [Finset.card_range] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  -- the mean value theorem at the points on each piece
  have hX0 : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set L0 : ℝ := Real.exp 1 * ((q * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2))
    with hL0
  have hL0nn : 0 ≤ L0 := by rw [hL0]; positivity
  have hls : ∀ j ∈ Finset.range J, ∑ i ∈ R, ‖pv (Sk.filter fun k => g k = j) c (χ i) (s i)‖ ^ 2 ≤
      L0 * ∑ k ∈ Sk.filter (fun k => g k = j), ‖c k‖ ^ 2 := by
    intro j hj
    rcases (Sk.filter fun k => g k = j).eq_empty_or_nonempty with he | hne
    · rw [he]; simp [pv]
    obtain ⟨k₀, hk₀⟩ := hne
    have hk₀X : k₀ ≤ X := (Finset.mem_Icc.1 (hSk (Finset.mem_filter.1 hk₀).1)).2
    have hjX : 2 ^ j < X := lt_of_lt_of_le (Finset.mem_Ioc.1 (hpiece j hj hk₀)).1 hk₀X
    have hS0' : 0 ∉ Sk.filter (fun k => g k = j) := fun h => hSk0 (Finset.mem_filter.1 h).1
    have h := LinnikPoints.large_values_points (hpiece j hj) c q (lo := -T - 1 / 2) (hi := T + 1 / 2)
      (by linarith) R χ (fun i => -t i)
      (fun i hi => ⟨by linarith [(abs_le.1 (ht i hi)).2], by linarith [(abs_le.1 (ht i hi)).1]⟩)
      (fun i hi k hk hik hχ => by
        rw [show -t i - -t k = -(t i - t k) by ring, abs_neg]; exact hsep i hi k hk hik hχ)
    have hconv : ∀ i, pv (Sk.filter fun k => g k = j) c (χ i) (s i) =
        DirMean.dp (Sk.filter fun k => g k = j) (fun k => c k * χ i k) (-t i) := by
      intro i
      rw [hs, pv_eq_dp _ hS0' c (χ i) 0 (-t i)]
      simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    simp_rw [hconv]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity))
    -- the factor at `P = 2^j` is at most the factor at `X`
    have hPX : ((2 ^ j : ℕ) : ℝ) ≤ X := by exact_mod_cast hjX.le
    have hP1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have hP0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
    have hlog1 : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log X := Real.log_le_log hP0 hPX
    have hlog2 : Real.log (2 * ((2 ^ j : ℕ) : ℝ)) ≤ Real.log (2 * X) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogP : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hlog2P : 0 ≤ Real.log (2 * ((2 ^ j : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
    have e : (q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) = q * (2 * T + 1) := by ring
    rw [e]
    have hA : ((q : ℝ) * (2 * T + 1) + 8 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))) *
        (2 + Real.log (2 * ((2 ^ j : ℕ) : ℝ)) ^ 2) ≤
        ((q : ℝ) * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2) := by
      gcongr
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc ((q : ℝ) * (2 * T + 1) + 8 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))) *
          (2 + Real.log (2 * ((2 ^ j : ℕ) : ℝ)) ^ 2) ≤
          ((q : ℝ) * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2) := hA
      _ ≤ L0 := by rw [hL0]; exact le_mul_of_one_le_left (by positivity) he1
  have hLSX : LSX q T X = L0 * J := by rw [hL0, hJ]; unfold LSX; push_cast; ring
  calc ∑ i ∈ R, ‖pv Sk c (χ i) (s i)‖ ^ 2
      ≤ ∑ i ∈ R, J * ∑ j ∈ Finset.range J, ‖pv (Sk.filter fun k => g k = j) c (χ i) (s i)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hcs i
    _ = J * ∑ j ∈ Finset.range J, ∑ i ∈ R, ‖pv (Sk.filter fun k => g k = j) c (χ i) (s i)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ J * ∑ j ∈ Finset.range J, L0 * ∑ k ∈ Sk.filter (fun k => g k = j), ‖c k‖ ^ 2 := by
        gcongr with j hj
        exact hls j hj
    _ = L0 * J * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]
        ring
    _ = LSX q T X * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by rw [hLSX]

/-- **The product trick at the points, squared**: for points whose characters are distinct or which are at least
`1` apart, `T ≥ 0` and `|t_i| ≤ T`, if
`|F(χ_i, −it_i)| ≥ V > 0` for every `i ∈ R`, with `F`
supported on `[2, N′]`, then for any polynomial `E` on `[1, Z]`,
`Σ_{i∈R}|E(χ_i, −it_i)|² ≤ V^{−2}L(N′Z)·τ·Σ|b_n|²·Σ|e_m|²` with `d(k) ≤ τ` for `k ≤ N′Z`
(`pv_mul`, `mass_mulCo_le` and `ls_points`). -/
lemma prod_trick_points {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} {t : ι → ℝ} (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j|)
    {T : ℝ} (hT : 0 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) {S M : Finset ℕ} {N' Z : ℕ} (hS : S ⊆ Finset.Icc 2 N')
    (hM : M ⊆ Finset.Icc 1 Z)
    (b e : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖) {τ : ℝ}
    (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) :
    ∑ i ∈ R, ‖pv M e (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ ^ 2 ≤
      (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2))) := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Icc.1 (hS h)).1; omega
  have hM0 : 0 ∉ M := fun h => by have := (Finset.mem_Icc.1 (hM h)).1; omega
  have hsupp : mulSupp S M ⊆ Finset.Icc 2 (N' * Z) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    obtain ⟨h11, h12⟩ := Finset.mem_Icc.1 (hS h1)
    obtain ⟨h21, h22⟩ := Finset.mem_Icc.1 (hM h2)
    exact Finset.mem_Icc.2 ⟨by nlinarith, Nat.mul_le_mul h12 h22⟩
  set s : ι → ℂ := fun i => ((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I with hs
  have hpt : ∀ i ∈ R, ‖pv M e (χ i) (s i)‖ ^ 2 ≤ (V ^ 2)⁻¹ * ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := by
    intro i hi
    rw [← pv_mul, norm_mul, mul_pow, ← mul_assoc]
    have h2 : V ^ 2 ≤ ‖pv S b (χ i) (s i)‖ ^ 2 := pow_le_pow_left₀ hV.le (hbig i hi) 2
    have h3 : 1 ≤ (V ^ 2)⁻¹ * ‖pv S b (χ i) (s i)‖ ^ 2 := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
    have h4 : 0 ≤ ‖pv M e (χ i) (s i)‖ ^ 2 := sq_nonneg _
    nlinarith
  calc ∑ i ∈ R, ‖pv M e (χ i) (s i)‖ ^ 2
      ≤ ∑ i ∈ R, (V ^ 2)⁻¹ * ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := Finset.sum_le_sum hpt
    _ = (V ^ 2)⁻¹ * ∑ i ∈ R, ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (V ^ 2)⁻¹ * (LSX q T (N' * Z) * ∑ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2) := by
        gcongr; exact ls_points hsep hT ht hsupp _
    _ ≤ (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2))) := by
        have := LSX_nonneg q hT (N' * Z)
        gcongr
        exact mass_mulCo_le hS0 hM0 b e (fun k hk => hτ k (Finset.mem_Icc.1 (hsupp hk)).2)

/-! ### The dual sums of the pairs at the points -/

/-- **The dual sum of a pair at the point of the first character**:
`|D_{ik}(u)| = |Σ_{m≤Z}e_{k,u}(m)χ_i(m)m^{it_i}|` with `e_{k,u}(m) = conj(χ_k(m)m^{−1/2+i(u+t_k)})`
(`dualS_eq_conj_pv` at `a = a′ = 0`, `g = −t_i`, `g′ = −t_k`, `κ = 1/2`, `v = u`). -/
lemma norm_dualS_pair {q : ℕ} (χi χk : DirichletCharacter ℂ q) (ti tk : ℝ) (Z : ℕ) (u : ℝ) :
    ‖dualS (χi * χk⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((ti - tk : ℝ) : ℂ)) * I)‖ =
      ‖pv (Finset.Icc 1 Z) (dualCo χk (1 / 2) 0 (-tk) u) χi (((0 : ℝ) : ℂ) + ((-ti : ℝ) : ℂ) * I)‖ := by
  have e : ((1 / 2 : ℝ) : ℂ) + (u - ((ti - tk : ℝ) : ℂ)) * I =
      (((0 + 0 : ℝ) : ℂ) + ((-ti - -tk : ℝ) : ℂ) * I) + (((1 / 2 - 2 * 0 : ℝ) : ℂ) + u * I) := by
    push_cast; ring
  rw [e, dualS_eq_conj_pv χi χk Z 0 0 (-ti) (-tk) (1 / 2) u, Complex.norm_conj]

/-- `H_Z = Σ_{m≤Z} 1/m`. -/
def HZ (Z : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 Z, ((m : ℝ))⁻¹

/-- `Σ_{m≤Z}|e_{k,u}(m)|² ≤ H_Z` (`norm_dualCo_le`). -/
lemma mass_dualCo_half {q : ℕ} (χk : DirichletCharacter ℂ q) (tk u : ℝ) (Z : ℕ) :
    ∑ m ∈ Finset.Icc 1 Z, ‖dualCo χk (1 / 2) 0 (-tk) u m‖ ^ 2 ≤ HZ Z := by
  unfold HZ
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have h1 := norm_dualCo_le χk (1 / 2) 0 (-tk) u hm0
  calc ‖dualCo χk (1 / 2) 0 (-tk) u m‖ ^ 2 ≤ ((m : ℝ) ^ (1 / 2 - 1 + 0 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ((m : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmr.le, ← Real.rpow_neg_one]; norm_num

/-- The weight `|H(1/2 + iu)|`. -/
def wH (u : ℝ) : ℝ := ‖H ((1 / 2 : ℝ) + u * I)‖

lemma wH_nonneg (u : ℝ) : 0 ≤ wH u := norm_nonneg _

/-- `I_H = ∫|H(1/2 + iu)| du`. -/
def IH : ℝ := ∫ u : ℝ, wH u

lemma IH_nonneg : 0 ≤ IH := integral_nonneg wH_nonneg

lemma integrable_wH : Integrable wH := by
  unfold wH
  have h := integrable_H_line (1 / 2) 0
  refine (h.congr (Eventually.of_forall fun u => ?_)).norm
  simp

lemma integrable_wH_mul {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hgB : ∀ u, ‖g u‖ ≤ B) :
    Integrable fun u => wH u * g u := by
  have hc : Continuous wH := continuous_H_half.norm
  refine (integrable_wH.mul_const B).mono' (hc.mul hg).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Real.norm_of_nonneg (wH_nonneg u)]
  exact mul_le_mul_of_nonneg_left (hgB u) (wH_nonneg u)

/-- The dual sum of a pair, `|D_{ik}(u)|`. -/
def Dp {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) : ℝ :=
  ‖dualS (χ i * (χ k)⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t i - t k : ℝ) : ℂ)) * I)‖

lemma Dp_nonneg {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) :
    0 ≤ Dp χ t Z i k u := norm_nonneg _

lemma Dp_le {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) :
    Dp χ t Z i k u ≤ Z :=
  norm_dualS_le _ Z (by simp; norm_num)

lemma continuous_Dp {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) :
    Continuous (Dp χ t Z i k) :=
  (continuous_dualS_line _ Z (1 / 2) (t i - t k)).norm

/-- **The mass of the dual sums over all pairs, at one height**: for points whose characters are distinct or which
are at least `1` apart, `|t_i| ≤ T`, `F` on
`[2, N′]` with `|F(χ_i, −it_i)| ≥ V > 0` on `R`, and `d(k) ≤ τ` for `k ≤ N′Z`,
`Σ_{i,k∈R}|D_{ik}(u)|² ≤ |R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z`. -/
lemma sum_Dp_sq_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} {t : ι → ℝ} (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j|)
    {T : ℝ} (hT : 0 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) {S : Finset ℕ} {N' Z : ℕ} (hS : S ⊆ Finset.Icc 2 N')
    (b : ℕ → ℂ) {V : ℝ}
    (hV : 0 < V) (hbig : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖) {τ : ℝ}
    (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) (u : ℝ) :
    ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤
      R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) := by
  have hτ0 : 0 ≤ τ := by have := hτ 0 (Nat.zero_le _); simpa using this
  have hk : ∀ k ∈ R, ∑ i ∈ R, Dp χ t Z i k u ^ 2 ≤
      (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))) := by
    intro k _
    simp only [Dp, norm_dualS_pair]
    refine (prod_trick_points hsep hT ht hS (Finset.Subset.refl _) b _ hV hbig hτ).trans ?_
    have := LSX_nonneg q hT (N' * Z)
    have hb0 : 0 ≤ ∑ n ∈ S, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    gcongr
    exact mass_dualCo_half (χ k) (t k) u Z
  rw [Finset.sum_comm]
  calc ∑ k ∈ R, ∑ i ∈ R, Dp χ t Z i k u ^ 2
      ≤ ∑ _k ∈ R, (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))) := Finset.sum_le_sum hk
    _ = R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The off-diagonal mass of the Gram matrix -/

/-- The tail bound of `norm_gram_le` at `|τ| ≤ 2T`. -/
def Bmax (q : ℕ) (N T : ℝ) (Z K : ℕ) : ℝ :=
  2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
    (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) * IK K

lemma Bmax_nonneg (q : ℕ) {N T : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (Z K : ℕ) : 0 ≤ Bmax q N T Z K := by
  unfold Bmax; have := CGK_pos K; have := EQh_pos q; have := IK_nonneg K; positivity

/-- **A Gram entry, squared**: for `χ_i ≠ χ_k`, `|t_i|, |t_k| ≤ T` and `Z, K ≥ 1`,
`|G(i, k)|² ≤ N·Q₀(q)²(∫|H(1/2 + iu)||D_{ik}(u)| du)² + B²` with `B` the tail bound at `|τ| ≤ 2T`
(`norm_gram_le`, `(a + b)² ≤ 2(a² + b²)` and `2(2π)^{−2} ≤ 1`). -/
lemma gram_sq_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {i k : ι} (hik : χ i ≠ χ k) {T : ℝ} (hti : |t i| ≤ T) (htk : |t k| ≤ T) {Z K : ℕ} (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) :
    ‖gramP N χ t i k‖ ^ 2 ≤ N * Q0 q ^ 2 * (∫ u : ℝ, wH u * Dp χ t Z i k u) ^ 2 + Bmax q N T Z K ^ 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans hti
  set J := ∫ u : ℝ, wH u * Dp χ t Z i k u with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun u => mul_nonneg (wH_nonneg u) (Dp_nonneg χ t Z i k u)
  have h : ‖gramP N χ t i k‖ ≤ (2 * Real.pi)⁻¹ * (N ^ (1 / 2 : ℝ) * Q0 q * J +
      2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K) :=
    norm_gram_le hN χ t hik hZ hK
  have htail : 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
      (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K ≤ Bmax q N T Z K := by
    unfold Bmax
    have h1 : |t i - t k| ≤ 2 * T := (abs_sub _ _).trans (by linarith)
    have := CGK_pos K; have := EQh_pos q; have := IK_nonneg K
    gcongr
  set a := N ^ (1 / 2 : ℝ) * Q0 q * J with ha
  have ha0 : 0 ≤ a := by have := Q0_nonneg q; positivity
  set B := Bmax q N T Z K with hB
  have hB0 : 0 ≤ B := Bmax_nonneg q hN.le hT Z K
  have h2 : ‖gramP N χ t i k‖ ≤ (2 * Real.pi)⁻¹ * (a + B) :=
    h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity))
  have hpi : (2 * Real.pi)⁻¹ ^ 2 * 2 ≤ 1 := by
    have := Real.pi_gt_three
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]; nlinarith
  have hN2 : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  have hsq : a ^ 2 = N * Q0 q ^ 2 * J ^ 2 := by rw [ha, mul_pow, mul_pow, hN2]
  calc ‖gramP N χ t i k‖ ^ 2 ≤ ((2 * Real.pi)⁻¹ * (a + B)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = (2 * Real.pi)⁻¹ ^ 2 * (a + B) ^ 2 := by rw [mul_pow]
    _ ≤ (2 * Real.pi)⁻¹ ^ 2 * (2 * (a ^ 2 + B ^ 2)) := by gcongr; nlinarith [sq_nonneg (a - B)]
    _ = ((2 * Real.pi)⁻¹ ^ 2 * 2) * (a ^ 2 + B ^ 2) := by ring
    _ ≤ 1 * (a ^ 2 + B ^ 2) := by gcongr
    _ = N * Q0 q ^ 2 * J ^ 2 + B ^ 2 := by rw [one_mul, hsq]

/-- **A principal Gram entry, squared**: for `χ_i = χ_k`, `|t_i|, |t_k| ≤ T` and `Z, K ≥ 1`, with `τ = t_i − t_k`,
`|G(i, k)|² ≤ 2(N|H(1 + iτ)|)² + N·Q₀(q)²(∫|H(1/2 + iu)||D_{ik}(u)| du)² + B²` with `B` the tail bound at
`|τ| ≤ 2T` (`LinnikCGLRefl0.norm_gram_le0`, `(a + b)² ≤ 2(a² + b²)` twice and `4(2π)^{−2} ≤ 1`). -/
lemma gram_sq_le0 {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {i k : ι} (hik : χ i = χ k) {T : ℝ} (hti : |t i| ≤ T) (htk : |t k| ≤ T) {Z K : ℕ} (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) :
    ‖gramP N χ t i k‖ ^ 2 ≤ 2 * (N * ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖) ^ 2 +
      N * Q0 q ^ 2 * (∫ u : ℝ, wH u * Dp χ t Z i k u) ^ 2 + Bmax q N T Z K ^ 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans hti
  set J := ∫ u : ℝ, wH u * Dp χ t Z i k u with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun u => mul_nonneg (wH_nonneg u) (Dp_nonneg χ t Z i k u)
  have h1 : χ i * (χ k)⁻¹ = 1 := by rw [hik, mul_inv_cancel]
  have hD : (∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ *
      ‖dualS (1 : DirichletCharacter ℂ q)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t i - t k : ℝ) : ℂ)) * I)‖) = J := by
    rw [hJ]
    simp only [wH, Dp, h1]
  have h := LinnikCGLRefl0.norm_gram_le0 hN χ t hik hZ hK
  rw [hD] at h
  have htail : 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
      (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K ≤ Bmax q N T Z K := by
    unfold Bmax
    have h1 : |t i - t k| ≤ 2 * T := (abs_sub _ _).trans (by linarith)
    have := CGK_pos K; have := EQh_pos q; have := IK_nonneg K
    gcongr
  set a := N ^ (1 / 2 : ℝ) * Q0 q * J with ha
  have ha0 : 0 ≤ a := by have := Q0_nonneg q; positivity
  set B := Bmax q N T Z K with hB
  have hB0 : 0 ≤ B := Bmax_nonneg q hN.le hT Z K
  set ρ := N * ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hpi : (2 * Real.pi)⁻¹ ^ 2 * 4 ≤ 1 := by
    have := Real.pi_gt_three
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]; nlinarith
  set c := (2 * Real.pi)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have h2 : ‖gramP N χ t i k‖ ≤ ρ + c * (a + B) :=
    h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) hc0))
  have hN2 : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  have hsq : a ^ 2 = N * Q0 q ^ 2 * J ^ 2 := by rw [ha, mul_pow, mul_pow, hN2]
  have hab : (a + B) ^ 2 ≤ 2 * (a ^ 2 + B ^ 2) := by nlinarith [sq_nonneg (a - B)]
  calc ‖gramP N χ t i k‖ ^ 2 ≤ (ρ + c * (a + B)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ 2 * ρ ^ 2 + 2 * c ^ 2 * (a + B) ^ 2 := by nlinarith [sq_nonneg (ρ - c * (a + B))]
    _ ≤ 2 * ρ ^ 2 + 2 * c ^ 2 * (2 * (a ^ 2 + B ^ 2)) := by gcongr
    _ = 2 * ρ ^ 2 + (c ^ 2 * 4) * (a ^ 2 + B ^ 2) := by ring
    _ ≤ 2 * ρ ^ 2 + 1 * (a ^ 2 + B ^ 2) := by gcongr
    _ = 2 * ρ ^ 2 + N * Q0 q ^ 2 * J ^ 2 + B ^ 2 := by rw [hsq]; ring

open scoped Classical in
/-- The residue of the pair `(i, k)`: `[i ≠ k, χ_i = χ_k]|H(1 + i(t_i − t_k))|²`. -/
def resT {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) : ℝ :=
  if i ≠ k ∧ χ i = χ k then ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ ^ 2 else 0

/-- **The residues of the principal Gram entries**: `Σ_{i≠k, χ_i=χ_k}|H(1 + i(t_i − t_k))|²`. -/
def resP {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) : ℝ :=
  ∑ i ∈ R, ∑ k ∈ R, resT χ t i k

lemma resT_nonneg {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) :
    0 ≤ resT χ t i k := by
  unfold resT; split_ifs <;> positivity

/-- At one point per character there are no residues. -/
lemma resP_eq_zero_of_injOn {ι : Type*} {q : ℕ} {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) (t : ι → ℝ) : resP R χ t = 0 := by
  unfold resP
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => ?_
  unfold resT
  refine ite_eq_right ?_
  rintro ⟨hik, h⟩
  exact hik (hinj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hk) h)

/-- **The off-diagonal mass of the Gram matrix, explicitly**: for points whose characters are distinct or which
are at least `1` apart, `|t_i| ≤ T`, `N > 0`, `F = Σ_{n∈S}b_nχ(n)n^{it}` on `S ⊆ [2, N′]` with `|F(χ_i, t_i)| ≥ V > 0`
for every `i ∈ R`, `Z, K ≥ 1` and `d(k) ≤ τ` for `k ≤ N′Z`,
`‖E‖_F² ≤ N·Q₀(q)²I_H²·|R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z + |R|²B² + 2N²P_H`, with `P_H` the residues (`resP`). -/
theorem frobOff_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    {t : ι → ℝ} (hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i = χ j → 1 ≤ |t i - t j|) {T N : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    (ht : ∀ i ∈ R, |t i| ≤ T)
    {S : Finset ℕ} {N' : ℕ} (hS : S ⊆ Finset.Icc 2 N') (b : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ i ∈ R, V ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) {Z K : ℕ} (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) {τ : ℝ} (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) :
    frobOff N R χ t ≤ N * Q0 q ^ 2 * IH ^ 2 * (R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) *
        (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))))) + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 +
      2 * N ^ 2 * resP R χ t := by
  classical
  have hbig' : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ := by
    intro i hi
    refine (hbig i hi).trans (le_of_eq ?_)
    unfold pv
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    push_cast; ring
  set W := (R.card : ℝ) * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) with hW
  have hWu : ∀ u, ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ W := fun u =>
    sum_Dp_sq_le hsep hT ht hS b hV hbig' hτ u
  have hB := Bmax_nonneg q hN.le hT Z K
  have hQ := Q0_nonneg q
  have hIH := IH_nonneg
  have hi2 : ∀ i k, Integrable fun u => wH u * Dp χ t Z i k u := fun i k =>
    integrable_wH_mul (continuous_Dp χ t Z i k) fun u => by
      rw [Real.norm_of_nonneg (Dp_nonneg χ t Z i k u)]; exact Dp_le χ t Z i k u
  have hi3 : ∀ i k, Integrable fun u => wH u * Dp χ t Z i k u ^ 2 := fun i k =>
    integrable_wH_mul ((continuous_Dp χ t Z i k).pow 2) fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (Dp_nonneg χ t Z i k u) (Dp_le χ t Z i k u) 2
  have hpair : ∀ i ∈ R, ∀ k ∈ R, (if i = k then 0 else ‖gramP N χ t i k‖ ^ 2) ≤
      N * Q0 q ^ 2 * IH * (∫ u, wH u * Dp χ t Z i k u ^ 2) + Bmax q N T Z K ^ 2 +
        2 * N ^ 2 * resT χ t i k := by
    intro i hi k hk
    have hint0 : 0 ≤ ∫ u, wH u * Dp χ t Z i k u ^ 2 :=
      integral_nonneg fun u => mul_nonneg (wH_nonneg u) (sq_nonneg _)
    have hres := resT_nonneg χ t i k
    split_ifs with hik
    · positivity
    · have hcs : (∫ u, wH u * Dp χ t Z i k u) ^ 2 ≤ IH * ∫ u, wH u * Dp χ t Z i k u ^ 2 :=
        integral_sq_le wH_nonneg (Dp_nonneg χ t Z i k) integrable_wH (hi2 i k) (hi3 i k)
      have h1 := mul_le_mul_of_nonneg_left hcs (show 0 ≤ N * Q0 q ^ 2 by positivity)
      have e1 : N * Q0 q ^ 2 * (IH * ∫ u, wH u * Dp χ t Z i k u ^ 2) =
          N * Q0 q ^ 2 * IH * ∫ u, wH u * Dp χ t Z i k u ^ 2 := by ring
      by_cases hχ : χ i = χ k
      · have hr : resT χ t i k = ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ ^ 2 := by
          unfold resT; exact ite_eq_left ⟨hik, hχ⟩
        refine (gram_sq_le0 hN χ t hχ (ht i hi) (ht k hk) hZ hK).trans ?_
        rw [hr]
        nlinarith [h1, e1]
      · refine (gram_sq_le hN χ t hχ (ht i hi) (ht k hk) hZ hK).trans ?_
        nlinarith [h1, e1]
  have hswap : ∑ i ∈ R, ∑ k ∈ R, (∫ u, wH u * Dp χ t Z i k u ^ 2) =
      ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 := by
    have e : ∀ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 =
        ∑ i ∈ R, ∑ k ∈ R, wH u * Dp χ t Z i k u ^ 2 := by
      intro u; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi3 i k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hi3 i k)]
  have hint : ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ IH * W := by
    have hl : Integrable fun u => wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 := by
      have e : (fun u => wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2) =
          fun u => ∑ i ∈ R, ∑ k ∈ R, wH u * Dp χ t Z i k u ^ 2 := by
        funext u; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
      rw [e]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hi3 i k
    calc ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ ∫ u, wH u * W :=
          integral_mono hl (integrable_wH.mul_const W) fun u => mul_le_mul_of_nonneg_left (hWu u) (wH_nonneg u)
      _ = IH * W := by rw [integral_mul_const]; rfl
  calc frobOff N R χ t = ∑ i ∈ R, ∑ k ∈ R, (if i = k then 0 else ‖gramP N χ t i k‖ ^ 2) := rfl
    _ ≤ ∑ i ∈ R, ∑ k ∈ R, (N * Q0 q ^ 2 * IH * (∫ u, wH u * Dp χ t Z i k u ^ 2) + Bmax q N T Z K ^ 2 +
          2 * N ^ 2 * resT χ t i k) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hpair i hi k hk
    _ = N * Q0 q ^ 2 * IH * (∑ i ∈ R, ∑ k ∈ R, (∫ u, wH u * Dp χ t Z i k u ^ 2)) +
          (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 + 2 * N ^ 2 * resP R χ t := by
        simp only [resP, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
        ring
    _ ≤ N * Q0 q ^ 2 * IH * (IH * W) + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 + 2 * N ^ 2 * resP R χ t := by
        rw [hswap]; gcongr
    _ = N * Q0 q ^ 2 * IH ^ 2 * W + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 + 2 * N ^ 2 * resP R χ t := by
        ring

end LinnikCGLFrob

#print axioms LinnikCGLFrob.ls_points
#print axioms LinnikCGLFrob.prod_trick_points
#print axioms LinnikCGLFrob.sum_Dp_sq_le
#print axioms LinnikCGLFrob.gram_sq_le
#print axioms LinnikCGLFrob.gram_sq_le0
#print axioms LinnikCGLFrob.resP_eq_zero_of_injOn
#print axioms LinnikCGLFrob.frobOff_le
