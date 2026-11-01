/-
# The object of step 6 for `ζ`: an orbit of similitudes, whose span is not a lattice

Plain statement. Let `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}` be the kernel of `BallKernel`, over the nontrivial zeros of
`ζ` with multiplicity. A *realization* of a kernel `k` on the positive reals (`Realization`) is a complex inner product
space with vectors `w_r`, one for each positive rational `r`, and linear maps `φ_n`, `n ≥ 1`, such that
* `⟨φ_n x, φ_n y⟩ = n⟨x, y⟩` and `φ_mφ_n = φ_{mn}`: commuting similitudes, `φ_n` of factor `n`;
* `φ_n(w_r) = w_{nr}`: the vectors are the orbit of `w_1`;
* `⟨w_b, w_a⟩ = √(ab)·k(a/b)`.
It is the object of the sixth of the first steps in `docs/ball-conjecture.md`, in a Hilbert space rather than a lattice.
* Mathlib's `RiemannHypothesis` holds if and only if `K` has a realization (`rh_iff_realization`). Under RH one is `ℓ²`
  of the zeros, with `w_r = (e^{(ρ − ½)²/4} r^ρ)_ρ` and `φ_n` multiplying the coordinate of `ρ` by `n^ρ`
  (`realization`, from `realizationOf`, which takes any square-summable weights), so that the eigenvalues of `φ_n` are
  the numbers `n^ρ` (`phi_single`).
* The similitudes alone give the Gram matrix its shape, `⟨w_b, w_a⟩ = b·⟨w_1, w_{a/b}⟩` (`gram_shape`), and an
  eigenvalue `p^ρ` of a similitude of factor `p > 1` has `Re ρ = ½` (`re_eq_half_of_eigen`).
* But in every realization of `K` the vectors `w_{n+1} − w_n` are nonzero and their norms tend to `0`
  (`not_discrete`): the orbit spans no lattice. This holds for every kernel with
  `‖k(r) + k(1/r) − 2k(1)‖ ≤ M(log r)²` near `r = 1` (`tendsto_norm_sub_of_smooth`), which `K` satisfies, its weights
  being Gaussian (`kerK_smooth`). The ratios `(n + 1)/n` of the orbit tend to `1`. Those of the Frobenius points of
  `ManinFrobenius` are powers of `q`, and there `B(P_{k+1} − P_k, P_{k+1} − P_k) = 2q^k·#E(𝔽_q)` grows.

So for `ζ` the "arithmetic" of step 6 cannot be integrality of a kernel that is smooth in `a/b`: the kernel would have
to see the primes separately, `ℚ₊^× ≅ ℤ^{(∞)}`, rather than through the real line, in which `ℚ₊^×` is dense. The kernel
of `dh` has no realization (`PsiOmega.not_realization_dh`, `lib/dh/DHBallKernel.lean`).
-/
import Mathlib
import BallKernel
import PsiOmega

open Real Complex Finset Filter Topology ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace BallLattice

open BallKernel

/-! ## Realizations -/

/-- A **realization** of a kernel `k` on the positive reals by similitudes: a complex inner product space with vectors
`w_r`, `r` a positive rational, and linear maps `φ_n`, `n ≥ 1`, such that `φ_n` is a similitude of factor `n`,
`φ_mφ_n = φ_{mn}`, `φ_n(w_r) = w_{nr}`, and `⟨w_b, w_a⟩ = √(ab)·k(a/b)`. -/
structure Realization (k : ℝ → ℂ) where
  /-- The space. -/
  E : Type
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace ℂ E]
  /-- The vectors `w_r`. -/
  w : ℚ → E
  /-- The similitudes `φ_n`. -/
  φ : ℕ → E →ₗ[ℂ] E
  similitude : ∀ n : ℕ, 0 < n → ∀ x y : E, ⟪φ n x, φ n y⟫_ℂ = (n : ℂ) * ⟪x, y⟫_ℂ
  comp : ∀ m n : ℕ, 0 < m → 0 < n → (φ m).comp (φ n) = φ (m * n)
  orbit : ∀ (n : ℕ) (r : ℚ), 0 < n → 0 < r → φ n (w r) = w (n * r)
  gram : ∀ a b : ℚ, 0 < a → 0 < b → ⟪w b, w a⟫_ℂ = (Real.sqrt ((a : ℝ) * b) : ℂ) * k ((a : ℝ) / b)

attribute [instance] Realization.normedAddCommGroup Realization.innerProductSpace

/-- **The similitudes give the Gram matrix its shape**: if `φ_n` is a similitude of factor `n` with
`φ_n(w_r) = w_{nr}`, then `⟨w_b, w_a⟩ = b·⟨w_1, w_{a/b}⟩` for positive rationals `a`, `b`. So
`⟨w_b, w_a⟩ = √(ab)·k(a/b)` with `k(r) = ⟨w_1, w_r⟩/√r`: the Gram matrix of the orbit is its first row, as
`B(P_{j+d}, P_j) = q^j·B(P_d, P_0)` for the Frobenius points (`ManinHasse.gram_orbit`). -/
theorem gram_shape {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : ℚ → E) (φ : ℕ → E →ₗ[ℂ] E)
    (hsim : ∀ n : ℕ, 0 < n → ∀ x y : E, ⟪φ n x, φ n y⟫_ℂ = (n : ℂ) * ⟪x, y⟫_ℂ)
    (horb : ∀ (n : ℕ) (r : ℚ), 0 < n → 0 < r → φ n (w r) = w (n * r)) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    ⟪w b, w a⟫_ℂ = (b : ℂ) * ⟪w 1, w (a / b)⟫_ℂ := by
  have hnum := Rat.num_pos.2 hb
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = b.num := ⟨b.num.toNat, Int.toNat_of_nonneg hnum.le⟩
  have hm0 : 0 < m := by omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = b.den := ⟨_, rfl⟩
  have hn0 : 0 < n := hn ▸ b.den_pos
  have hbmn : b = (m : ℚ) / n := by
    rw [hn]
    conv_lhs => rw [← Rat.num_div_den b]
    rw [← hm]
    push_cast
    rfl
  have hden : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have h1 : φ n (w b) = φ m (w 1) := by
    rw [horb n b hn0 hb, horb m 1 hm0 one_pos]
    congr 1
    rw [hbmn]
    field_simp
  have h2 : φ n (w a) = φ m (w (a / b)) := by
    rw [horb n a hn0 ha, horb m (a / b) hm0 (div_pos ha hb)]
    congr 1
    rw [hbmn]
    field_simp
  have e := hsim n hn0 (w b) (w a)
  rw [h1, h2, hsim m hm0] at e
  have hden' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hb' : (b : ℂ) = (m : ℂ) / (n : ℂ) := by
    rw [hbmn]
    push_cast
    ring
  rw [hb']
  field_simp
  linear_combination -e

/-- **An eigenvalue `p^ρ` of a similitude of factor `p > 1` has `Re ρ = ½`**: if `⟨φx, φy⟩ = p⟨x, y⟩` and
`φv = p^ρ v` with `v ≠ 0`, then `|p^ρ|² = p`. -/
theorem re_eq_half_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {φ : E →ₗ[ℂ] E} {p : ℝ}
    (hp : 1 < p) (hφ : ∀ x y : E, ⟪φ x, φ y⟫_ℂ = (p : ℂ) * ⟪x, y⟫_ℂ) {ρ : ℂ} {v : E} (hv : v ≠ 0)
    (h : φ v = cexp (ρ * Real.log p) • v) : ρ.re = 1 / 2 := by
  have e := hφ v v
  rw [h, inner_smul_left, inner_smul_right, ← mul_assoc] at e
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  have e2 : conj (cexp (ρ * Real.log p)) * cexp (ρ * Real.log p) = p := mul_right_cancel₀ hvv e
  rw [Complex.conj_mul', Complex.norm_exp] at e2
  have e3 : Real.exp ((ρ * Real.log p).re) ^ 2 = p := by exact_mod_cast e2
  have hre : (ρ * Real.log p).re = ρ.re * Real.log p := by simp
  rw [hre, ← Real.exp_nat_mul] at e3
  have hlog : 0 < Real.log p := Real.log_pos hp
  have e4 : ((2 : ℕ) : ℝ) * (ρ.re * Real.log p) = Real.log p := by
    rw [← Real.log_exp (((2 : ℕ) : ℝ) * (ρ.re * Real.log p)), e3]
  push_cast at e4
  have : (2 * ρ.re - 1) * Real.log p = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · linarith

/-- **A realization makes its kernel positive-definite on `ℚ₊^×`**:
`Σ_{a,b} x_a x̄_b k(a/b) = ‖Σ_a (x_a/√a) w_a‖² ≥ 0`. -/
theorem posDefQ_of_realization {k : ℝ → ℂ} (R : Realization k) : PosDefQ k := by
  intro S x hS
  set v : R.E := ∑ a ∈ S, (x a / (Real.sqrt a : ℂ)) • R.w a with hv
  have h : ⟪v, v⟫_ℂ = ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * k ((a : ℝ) / b) := by
    rw [hv, sum_inner]
    simp_rw [inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have ha0 : (0 : ℝ) < a := by exact_mod_cast hS a ha
    have hb0 : (0 : ℝ) < b := by exact_mod_cast hS b hb
    have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha0).ne'
    have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb0).ne'
    have hsa' : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast hsa
    have hsb' : (Real.sqrt b : ℂ) ≠ 0 := by exact_mod_cast hsb
    rw [inner_smul_left, inner_smul_right, R.gram a b (hS a ha) (hS b hb), Real.sqrt_mul ha0.le, map_div₀,
      Complex.conj_ofReal]
    push_cast
    field_simp
  rw [← h, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  exact Complex.zero_le_real.2 (sq_nonneg _)

/-! ## The realization in `ℓ²` of the zeros, under RH -/

/-- `ℓ²` of the nontrivial zeros of `ζ`, with multiplicity. -/
abbrev L2 : Type := lp (fun _ : ZIdx => ℂ) 2

/-- `c_ρ = e^{(ρ − ½)²/4}`, with `|c_ρ|² = e^{−γ²/2}` on the line. -/
def cw (q : ZIdx) : ℂ := cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 4)

/-- `r^ρ`, written `e^{ρ log r}`. -/
def pw (q : ZIdx) (r : ℝ) : ℂ := cexp (zetaZeroFamily q * Real.log r)

lemma norm_cw_sq (q : ZIdx) : ‖cw q‖ ^ 2 = ‖gw (poleP q)‖ := by
  unfold cw gw poleP
  rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  have e : (2 * (zetaZeroFamily q - 1 / 2)) ^ 2 / 8 = ((2 : ℝ) : ℂ) * ((zetaZeroFamily q - 1 / 2) ^ 2 / 4) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]
  push_cast
  ring

lemma memℓp_of_sq {f : ZIdx → ℂ} (h : Summable fun q => ‖f q‖ ^ 2) : Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa using h

lemma summable_sq_of_mem (x : L2) : Summable fun q => ‖x q‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp x)
  simpa using h

lemma re_zero_mem (q : ZIdx) : 0 < (zetaZeroFamily q).re ∧ (zetaZeroFamily q).re < 1 := q.1.2.mem_strip

lemma norm_pw_le (q : ZIdx) (r : ℝ) : ‖pw q r‖ ≤ Real.exp |Real.log r| := by
  unfold pw
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  obtain ⟨h0, h1⟩ := re_zero_mem q
  have e : (zetaZeroFamily q * Real.log r).re = (zetaZeroFamily q).re * Real.log r := by simp
  rw [e]
  calc (zetaZeroFamily q).re * Real.log r ≤ |(zetaZeroFamily q).re * Real.log r| := le_abs_self _
    _ = |(zetaZeroFamily q).re| * |Real.log r| := abs_mul _ _
    _ ≤ 1 * |Real.log r| := mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
    _ = |Real.log r| := one_mul _

lemma norm_pw_of_rh (hRH : RiemannHypothesis) (q : ZIdx) (r : ℝ) : ‖pw q r‖ = Real.exp (Real.log r / 2) := by
  unfold pw
  rw [Complex.norm_exp]
  congr 1
  have h := line_of_RH hRH q
  simp [h]
  ring

lemma summable_cw_sq : Summable fun q => ‖cw q‖ ^ 2 := summable_gw.congr fun q => (norm_cw_sq q).symm

/-- The vector `w_r = (c_ρ r^ρ)_ρ`, for weights with `Σ_ρ |c_ρ|² < ∞`. -/
def wvOf (c : ZIdx → ℂ) (hc : Summable fun q => ‖c q‖ ^ 2) (r : ℚ) : L2 :=
  ⟨fun q => c q * pw q r, memℓp_of_sq <| by
    refine (hc.mul_right (Real.exp |Real.log r| ^ 2)).of_nonneg_of_le (fun q => by positivity) fun q => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_pw_le q r) 2) (by positivity)⟩

/-- The map multiplying the coordinate of `ρ` by `n^ρ`. -/
def phiL (n : ℕ) : L2 →ₗ[ℂ] L2 where
  toFun x := ⟨fun q => pw q n * x q, memℓp_of_sq <| by
    refine ((summable_sq_of_mem x).mul_left (Real.exp |Real.log n| ^ 2)).of_nonneg_of_le
      (fun q => by positivity) fun q => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_pw_le q n) 2) (by positivity)⟩
  map_add' x y := by
    ext q
    show pw q n * (x + y) q = pw q n * x q + pw q n * y q
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    ext q
    show pw q n * (c • x) q = c * (pw q n * x q)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

lemma phiL_apply (n : ℕ) (x : L2) (q : ZIdx) : phiL n x q = pw q n * x q := rfl

lemma wvOf_apply (c : ZIdx → ℂ) (hc : Summable fun q => ‖c q‖ ^ 2) (r : ℚ) (q : ZIdx) :
    wvOf c hc r q = c q * pw q r := rfl

lemma pw_mul (q : ZIdx) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) : pw q (s * t) = pw q s * pw q t := by
  unfold pw
  rw [Real.log_mul hs ht, ← Complex.exp_add]
  push_cast
  ring_nf

open scoped Classical in
/-- **The eigenvalues of `φ_n` are the numbers `n^ρ`**: `φ_n` multiplies the basis vector of `ρ` by `n^ρ`. -/
theorem phi_single (q : ZIdx) (n : ℕ) : phiL n (lp.single 2 q 1) = pw q n • lp.single 2 q 1 := by
  ext i
  rw [phiL_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  rcases eq_or_ne i q with rfl | h
  · rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-- **A realization in `ℓ²` of the zeros, under RH**: for weights `c_ρ` with `Σ_ρ |c_ρ|² < ∞` and
`Σ_ρ c_ρa^ρ·conj(c_ρb^ρ) = √(ab)·k(a/b)`, the vectors `w_r = (c_ρ r^ρ)_ρ` and the maps `φ_n` multiplying the coordinate
of `ρ` by `n^ρ` realize `k`. On the line `|n^ρ|² = n`. -/
def realizationOf (hRH : RiemannHypothesis) {k : ℝ → ℂ} (c : ZIdx → ℂ) (hc : Summable fun q => ‖c q‖ ^ 2)
    (hk : ∀ a b : ℚ, 0 < a → 0 < b →
      ∑' q, c q * pw q a * conj (c q * pw q b) = (Real.sqrt ((a : ℝ) * b) : ℂ) * k ((a : ℝ) / b)) :
    Realization k where
  E := L2
  w := wvOf c hc
  φ := phiL
  similitude n hn x y := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [phiL_apply, phiL_apply, RCLike.inner_apply, RCLike.inner_apply]
    dsimp only
    rw [map_mul]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn2 : ‖pw q n‖ ^ 2 = (n : ℝ) := by
      rw [norm_pw_of_rh hRH, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (Real.log n / 2) = Real.log n by ring, Real.exp_log hn']
    have h : conj (pw q n) * pw q n = n := by
      rw [Complex.conj_mul']
      exact_mod_cast hn2
    linear_combination (y q * conj (x q)) * h
  comp m n hm hn := by
    refine LinearMap.ext fun x => ?_
    ext q
    rw [LinearMap.comp_apply, phiL_apply, phiL_apply, phiL_apply, ← mul_assoc]
    congr 1
    push_cast
    rw [pw_mul q (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  orbit n r hn hr := by
    ext q
    rw [phiL_apply, wvOf_apply, wvOf_apply]
    push_cast
    rw [pw_mul q (by exact_mod_cast hn.ne') (by exact_mod_cast hr.ne')]
    ring
  gram a b ha hb := by
    rw [lp.inner_eq_tsum, ← hk a b ha hb]
    refine tsum_congr fun q => ?_
    rw [wvOf_apply, wvOf_apply, RCLike.inner_apply]

/-- Under RH, `e^{(ρ−½)²/4}·a^ρ` paired with `e^{(ρ−½)²/4}·b^ρ` is `√(ab)·e^{−γ²/2}(a/b)^{iγ}`. -/
lemma gram_cw (hRH : RiemannHypothesis) (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    ∑' q, cw q * pw q a * conj (cw q * pw q b) = (Real.sqrt ((a : ℝ) * b) : ℂ) * BallKernel.kerK ((a : ℝ) / b) := by
  unfold BallKernel.kerK
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hsq : (Real.sqrt ((a : ℝ) * b) : ℂ) = cexp ((Real.log a + Real.log b) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos ha0 hb0), Real.log_mul ha0.ne' hb0.ne']
    push_cast
    ring_nf
  unfold cw pw
  rw [hsq, hline, Real.log_div ha0.ne' hb0.ne', map_mul, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, map_div₀, map_pow, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_sub]
  push_cast
  ring

/-- **Under RH, `K` has a realization**: `ℓ²` of the zeros, with `w_r = (e^{(ρ − ½)²/4} r^ρ)_ρ` and `φ_n` multiplying
the coordinate of `ρ` by `n^ρ` (`realizationOf`). -/
def realization (hRH : RiemannHypothesis) : Realization BallKernel.kerK :=
  realizationOf hRH cw summable_cw_sq (gram_cw hRH)

/-- **The Riemann hypothesis is the existence of a realization of `K`**: an inner product space with commuting
similitudes `φ_n` of factor `n` and an orbit `w_r` with `⟨w_b, w_a⟩ = √(ab)·K(a/b)`. -/
theorem rh_iff_realization : RiemannHypothesis ↔ Nonempty (Realization BallKernel.kerK) :=
  ⟨fun h => ⟨realization h⟩, fun ⟨R⟩ => rh_of_posDef (posDefQ_of_realization R)⟩

/-! ## The orbit of a realization of `K` spans no lattice -/

/-- In a realization, `‖w_r‖² = r·k(1)`. -/
lemma norm_sq_w {k : ℝ → ℂ} (R : Realization k) {r : ℚ} (hr : 0 < r) :
    ((‖R.w r‖ ^ 2 : ℝ) : ℂ) = (r : ℂ) * k 1 := by
  have h := R.gram r r hr hr
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.sqrt_mul_self hr0.le, div_self hr0.ne'] at h
  exact_mod_cast h

/-- In a realization, `‖w_a − w_b‖² = (a + b)·k(1) − √(ab)·(k(a/b) + k(b/a))`. -/
lemma norm_sub_sq {k : ℝ → ℂ} (R : Realization k) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    ((‖R.w a - R.w b‖ ^ 2 : ℝ) : ℂ) =
      ((a : ℂ) + b) * k 1 - (Real.sqrt ((a : ℝ) * b) : ℂ) * (k ((a : ℝ) / b) + k ((b : ℝ) / a)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (R.w a - R.w b)
  rw [← RCLike.ofReal_pow] at h
  have e : ((‖R.w a - R.w b‖ ^ 2 : ℝ) : ℂ) = ⟪R.w a - R.w b, R.w a - R.w b⟫_ℂ := h.symm
  rw [e, inner_sub_left, inner_sub_right, inner_sub_right, R.gram a a ha ha, R.gram b a hb ha, R.gram a b ha hb,
    R.gram b b hb hb, Real.sqrt_mul_self ha0.le, Real.sqrt_mul_self hb0.le, div_self ha0.ne', div_self hb0.ne',
    mul_comm (b : ℝ) a]
  push_cast
  ring

/-- **A kernel smooth at `1` has an orbit that spans no lattice**: if `‖k(r) + k(1/r) − 2k(1)‖ ≤ M(log r)²` for
`1 ≤ r ≤ 2`, then in every realization of `k`, `‖w_{n+1} − w_n‖² ≤ (‖k(1)‖ + 2|M|)/n`, so `‖w_{n+1} − w_n‖ → 0`. -/
theorem tendsto_norm_sub_of_smooth {k : ℝ → ℂ} (R : Realization k) {M : ℝ}
    (hk : ∀ r : ℝ, 1 ≤ r → r ≤ 2 → ‖k r + k r⁻¹ - 2 * k 1‖ ≤ M * Real.log r ^ 2) :
    Tendsto (fun n : ℕ => ‖R.w ((n : ℚ) + 1) - R.w n‖) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖R.w ((n : ℚ) + 1) - R.w n‖ ^ 2 ≤ (‖k 1‖ + 2 * |M|) / n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hq1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    have hq0 : (0 : ℚ) < n := by exact_mod_cast hn
    have e := norm_sub_sq R hq1 hq0
    push_cast at e
    set s := Real.sqrt (((n : ℝ) + 1) * n) with hs
    set r : ℝ := ((n : ℝ) + 1) / n with hr
    have hr' : (n : ℝ) / ((n : ℝ) + 1) = r⁻¹ := by rw [hr, inv_div]
    rw [hr'] at e
    have e2 : ((‖R.w ((n : ℚ) + 1) - R.w n‖ ^ 2 : ℝ) : ℂ) =
        ((2 * n + 1 - 2 * s : ℝ) : ℂ) * k 1 - (s : ℂ) * (k r + k r⁻¹ - 2 * k 1) := by
      rw [Complex.ofReal_pow, e]
      push_cast
      ring
    have h1 : 1 ≤ r := by rw [hr, le_div_iff₀ hn0]; linarith
    have h2 : r ≤ 2 := by rw [hr, div_le_iff₀ hn0]; linarith
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ^ 2 = ((n : ℝ) + 1) * n := Real.sq_sqrt (by positivity)
    have hsn : (n : ℝ) ≤ s := by nlinarith
    have hsn1 : s ≤ (n : ℝ) + 1 := by nlinarith
    have hsl : s ≤ (n : ℝ) + 1 / 2 := by nlinarith [hss, hs0]
    have hd : 0 ≤ 2 * (n : ℝ) + 1 - 2 * s := by linarith
    have hd3 : 2 * (n : ℝ) + 1 - 2 * s ≤ 1 / n := by
      rw [le_div_iff₀ hn0]
      nlinarith [mul_nonneg hd (show 0 ≤ (n : ℝ) + 1 + 2 * s by linarith), hss]
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg h1
    have hlog1 : Real.log r ≤ 1 / n := by
      have h := Real.log_le_sub_one_of_pos (show 0 < r by linarith)
      have h' : r - 1 = 1 / n := by rw [hr]; field_simp; ring
      linarith
    have hkr : ‖k r + k r⁻¹ - 2 * k 1‖ ≤ |M| * (1 / n) ^ 2 :=
      (hk r h1 h2).trans ((mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog1 2) (abs_nonneg M)))
    have hnorm : ‖R.w ((n : ℚ) + 1) - R.w n‖ ^ 2 = ‖((‖R.w ((n : ℚ) + 1) - R.w n‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnorm, e2]
    calc ‖((2 * n + 1 - 2 * s : ℝ) : ℂ) * k 1 - (s : ℂ) * (k r + k r⁻¹ - 2 * k 1)‖
        ≤ ‖((2 * n + 1 - 2 * s : ℝ) : ℂ) * k 1‖ + ‖(s : ℂ) * (k r + k r⁻¹ - 2 * k 1)‖ := norm_sub_le _ _
      _ = (2 * n + 1 - 2 * s) * ‖k 1‖ + s * ‖k r + k r⁻¹ - 2 * k 1‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hd,
            Real.norm_of_nonneg hs0]
      _ ≤ 1 / n * ‖k 1‖ + ((n : ℝ) + 1) * (|M| * (1 / n) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_right hd3 (norm_nonneg _))
            (mul_le_mul hsn1 hkr (norm_nonneg _) (by linarith))
      _ ≤ (‖k 1‖ + 2 * |M|) / n := by
          have hM := abs_nonneg M
          have key : (‖k 1‖ + 2 * |M|) / n - (1 / n * ‖k 1‖ + ((n : ℝ) + 1) * (|M| * (1 / n) ^ 2)) =
              |M| * ((n : ℝ) - 1) / n ^ 2 := by
            field_simp
            ring
          have : 0 ≤ |M| * ((n : ℝ) - 1) / n ^ 2 := div_nonneg (mul_nonneg hM (by linarith)) (by positivity)
          linarith
  have hlim : Tendsto (fun n : ℕ => Real.sqrt ((‖k 1‖ + 2 * |M|) / n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (‖k 1‖ + 2 * |M|))
    rw [Real.sqrt_zero] at h
    exact h
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← Real.sqrt_sq (norm_nonneg (R.w ((n : ℚ) + 1) - R.w n))]
  exact Real.sqrt_le_sqrt (hbound n hn)

/-- `‖e^z − 1 − z‖ ≤ 3‖z‖²e^{‖z‖}`. -/
lemma norm_exp_sub_one_sub_le (z : ℂ) : ‖cexp z - 1 - z‖ ≤ 3 * ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have he : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
  rcases le_or_gt ‖z‖ 1 with h | h
  · calc ‖cexp z - 1 - z‖ ≤ ‖z‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le h
      _ ≤ 3 * ‖z‖ ^ 2 * Real.exp ‖z‖ := by nlinarith [sq_nonneg ‖z‖]
  · have h1 : ‖cexp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
    have h2 : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
    have h3 : ‖cexp z - 1 - z‖ ≤ ‖cexp z‖ + 1 + ‖z‖ := by
      calc ‖cexp z - 1 - z‖ ≤ ‖cexp z - 1‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ ‖cexp z‖ + ‖(1 : ℂ)‖ + ‖z‖ := by linarith [norm_sub_le (cexp z) 1]
        _ = ‖cexp z‖ + 1 + ‖z‖ := by rw [norm_one]
    have h4 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    nlinarith

/-- `‖e^z + e^{−z} − 2‖ ≤ 6‖z‖²e^{‖z‖}`. -/
lemma norm_exp_add_exp_neg_sub_le (z : ℂ) : ‖cexp z + cexp (-z) - 2‖ ≤ 6 * ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have h1 := norm_exp_sub_one_sub_le z
  have h2 := norm_exp_sub_one_sub_le (-z)
  rw [norm_neg] at h2
  calc ‖cexp z + cexp (-z) - 2‖ = ‖(cexp z - 1 - z) + (cexp (-z) - 1 - -z)‖ := by congr 1; ring
    _ ≤ ‖cexp z - 1 - z‖ + ‖cexp (-z) - 1 - -z‖ := norm_add_le _ _
    _ ≤ 6 * ‖z‖ ^ 2 * Real.exp ‖z‖ := by linarith

/-- `‖e^{p²/8}‖·‖p‖⁴·e^{‖p‖} ≤ 24e^{73/8}` on `|Re p| < 1`: the Gaussian beats `‖p‖⁴e^{‖p‖}`. -/
lemma norm_gw_pow_le {p : ℂ} (hp : |p.re| < 1) : ‖gw p‖ * ‖p‖ ^ 4 * Real.exp ‖p‖ ≤ 24 * Real.exp (73 / 8) := by
  set t := |p.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hx : p.re ^ 2 ≤ 1 := by have := abs_lt.1 hp; nlinarith
  have hn : ‖p‖ ≤ 1 + t := (Complex.norm_le_abs_re_add_abs_im p).trans (by linarith)
  have hg : ‖gw p‖ = Real.exp ((p.re ^ 2 - p.im ^ 2) / 8) := by
    unfold gw
    rw [Complex.norm_exp]
    congr 1
    simp [sq]
  have h4 : ‖p‖ ^ 4 ≤ 24 * Real.exp t := by
    have hs := Real.sum_le_exp_of_nonneg ht0 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, Nat.cast_ofNat,
      Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one, zero_add, div_one] at hs
    calc ‖p‖ ^ 4 ≤ (1 + t) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hn 4
      _ ≤ 24 * Real.exp t := by nlinarith [sq_nonneg t]
  have he : Real.exp ‖p‖ ≤ Real.exp (1 + t) := Real.exp_le_exp.2 hn
  have hy : p.im ^ 2 = t ^ 2 := (sq_abs _).symm
  calc ‖gw p‖ * ‖p‖ ^ 4 * Real.exp ‖p‖
      ≤ Real.exp ((p.re ^ 2 - p.im ^ 2) / 8) * (24 * Real.exp t) * Real.exp (1 + t) := by
        rw [hg]
        gcongr
    _ = 24 * Real.exp ((p.re ^ 2 - p.im ^ 2) / 8 + t + (1 + t)) := by
        simp only [Real.exp_add]
        ring
    _ ≤ 24 * Real.exp (73 / 8) := by
        gcongr
        nlinarith [sq_nonneg (t - 8)]

/-- The Gaussian weights against `‖P‖²e^{‖P‖}` are summable over the zeros, by Hadamard's `Σ_ρ |ρ − ½|^{−2} < ∞`. -/
lemma summable_gw_mul : Summable fun q : ZIdx => ‖gw (poleP q)‖ * (‖poleP q‖ ^ 2 * Real.exp ‖poleP q‖) := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ := (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  have hs2 : Summable fun p : Bool × ZeroIdx (sqF Xi) => ‖p.2.1⁻¹‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun _ => hs, Summable.of_finite⟩
  have hs3 : Summable fun q : ZIdx => ‖((zetaEquiv q).2.1)⁻¹‖ :=
    (zetaEquiv.summable_iff (f := fun p : Bool × ZeroIdx (sqF Xi) => ‖p.2.1⁻¹‖)).2 hs2
  refine (hs3.mul_left (6 * Real.exp (73 / 8))).of_nonneg_of_le (fun q => by positivity) fun q => ?_
  have e1 : ‖poleP q‖ = 2 * ‖tau (zetaEquiv q).2‖ := by
    unfold poleP; rw [norm_mul, norm_zZF_sub]; simp
  have e2 : ‖(zetaEquiv q).2.1‖ = ‖tau (zetaEquiv q).2‖ ^ 2 := by rw [← tau_sq, norm_pow]
  have hP : 0 < ‖poleP q‖ := norm_pos_iff.2 fun h => im_poleP_ne q (by rw [h]; simp)
  have hT : 0 < ‖tau (zetaEquiv q).2‖ := by rw [e1] at hP; linarith
  have hb := norm_gw_pow_le (abs_re_poleP q)
  rw [norm_inv, e2, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [e1] at hb ⊢
  set T := ‖tau (zetaEquiv q).2‖
  have e3 : ‖gw (poleP q)‖ * ((2 * T) ^ 2 * Real.exp (2 * T)) * T ^ 2 =
      ‖gw (poleP q)‖ * (2 * T) ^ 4 * Real.exp (2 * T) / 4 := by ring
  rw [e3]
  linarith

/-- **`K` is smooth at `1`**: there is `M` with `‖K(r) + K(1/r) − 2K(1)‖ ≤ M(log r)²` for `1 ≤ r ≤ 2`. In the twin
sum `2K(1) + K(r) + K(1/r) = Σ_ρ c_ρ(2 + e^{λP_ρ} + e^{−λP_ρ})`, `λ = (log r)/2` (`BallKernel.twin_eq_kerK`), each
`e^{λP} + e^{−λP} − 2` is at most `6λ²‖P‖²e^{‖P‖}`, and the Gaussian weights beat `‖P‖²e^{‖P‖}`. -/
theorem kerK_smooth : ∃ M : ℝ, ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
    ‖BallKernel.kerK r + BallKernel.kerK r⁻¹ - 2 * BallKernel.kerK 1‖ ≤ M * Real.log r ^ 2 := by
  set M₀ := ∑' q : ZIdx, ‖gw (poleP q)‖ * (‖poleP q‖ ^ 2 * Real.exp ‖poleP q‖)
  refine ⟨6 * M₀, fun r h1 h2 => ?_⟩
  set l := Real.log r / 2 with hl
  have hlog0 := Real.log_nonneg h1
  have hl0 : 0 ≤ l := by rw [hl]; linarith
  have hl1 : l ≤ 1 := by
    have h3 : Real.log r ≤ Real.log 2 := Real.log_le_log (by linarith) h2
    have h4 := Real.log_two_lt_d9
    rw [hl]
    linarith
  have hW := twin_eq_kerK r
  have hW0 := twin_eq_kerK 1
  rw [Real.log_one, zero_div, inv_one] at hW0
  have e : BallKernel.kerK r + BallKernel.kerK r⁻¹ - 2 * BallKernel.kerK 1 =
      TwinLandau.Wsum poleP (fun q => gw (poleP q)) l - TwinLandau.Wsum poleP (fun q => gw (poleP q)) 0 := by
    rw [hl, hW, hW0]
    ring
  rw [e]
  unfold TwinLandau.Wsum
  have hsum : ∀ l' : ℝ, Summable fun q => TwinLandau.wq poleP (fun q => gw (poleP q)) q l' := fun l' =>
    (twinPoles_gw.summ.mul_right (4 * Real.exp |l'|)).of_norm_bounded fun q =>
      TwinLandau.norm_wq_le twinPoles_gw q l'
  rw [← (hsum l).tsum_sub (hsum 0)]
  have hterm : ∀ q : ZIdx, ‖TwinLandau.wq poleP (fun q => gw (poleP q)) q l -
      TwinLandau.wq poleP (fun q => gw (poleP q)) q 0‖ ≤
        6 * Real.log r ^ 2 * (‖gw (poleP q)‖ * (‖poleP q‖ ^ 2 * Real.exp ‖poleP q‖)) := by
    intro q
    unfold TwinLandau.wq
    have ez : gw (poleP q) * (2 + cexp ((l : ℂ) * poleP q) + cexp (-((l : ℂ) * poleP q))) -
        gw (poleP q) * (2 + cexp (((0 : ℝ) : ℂ) * poleP q) + cexp (-(((0 : ℝ) : ℂ) * poleP q))) =
        gw (poleP q) * (cexp ((l : ℂ) * poleP q) + cexp (-((l : ℂ) * poleP q)) - 2) := by
      simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero]
      ring
    rw [ez, norm_mul]
    have hb := norm_exp_add_exp_neg_sub_le ((l : ℂ) * poleP q)
    have hz : ‖(l : ℂ) * poleP q‖ = l * ‖poleP q‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0]
    rw [hz] at hb
    have hlz : l * ‖poleP q‖ ≤ ‖poleP q‖ := by nlinarith [norm_nonneg (poleP q)]
    have hl2 : l ^ 2 ≤ Real.log r ^ 2 := by rw [hl]; nlinarith
    calc ‖gw (poleP q)‖ * ‖cexp ((l : ℂ) * poleP q) + cexp (-((l : ℂ) * poleP q)) - 2‖
        ≤ ‖gw (poleP q)‖ * (6 * (l * ‖poleP q‖) ^ 2 * Real.exp (l * ‖poleP q‖)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ ‖gw (poleP q)‖ * (6 * (Real.log r ^ 2 * ‖poleP q‖ ^ 2) * Real.exp ‖poleP q‖) := by
          gcongr
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right hl2 (sq_nonneg _)
      _ = 6 * Real.log r ^ 2 * (‖gw (poleP q)‖ * (‖poleP q‖ ^ 2 * Real.exp ‖poleP q‖)) := by ring
  calc ‖∑' q, (TwinLandau.wq poleP (fun q => gw (poleP q)) q l - TwinLandau.wq poleP (fun q => gw (poleP q)) q 0)‖
      ≤ ∑' q : ZIdx, 6 * Real.log r ^ 2 * (‖gw (poleP q)‖ * (‖poleP q‖ ^ 2 * Real.exp ‖poleP q‖)) :=
        tsum_of_norm_bounded (summable_gw_mul.mul_left _).hasSum hterm
    _ = 6 * M₀ * Real.log r ^ 2 := by
        rw [tsum_mul_left]
        ring

/-- `ζ` has a nontrivial zero: Hadamard's `Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π` is not `0`. -/
lemma nonempty_ZIdx : Nonempty ZIdx := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hasSum_empty.unique hadamard_zeta
  have h0 : (2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) = 0 := by exact_mod_cast this.symm
  linarith [PsiOmega.hadamard_const_pos]

/-- Under RH, `K(1) = Σ_ρ e^{−γ²/2} ≠ 0`. -/
lemma kerK_one_ne_zero (hRH : RiemannHypothesis) : BallKernel.kerK 1 ≠ 0 := by
  obtain ⟨q0⟩ := nonempty_ZIdx
  set t : ZIdx → ℝ := fun q => (zetaZeroFamily q).im with ht
  have hline : ∀ q : ZIdx, zetaZeroFamily q - 1 / 2 = I * (t q : ℂ) := fun q => by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hterm : ∀ q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) *
      cexp ((zetaZeroFamily q - 1 / 2) * Real.log 1) = ((Real.exp (-(t q) ^ 2 / 2) : ℝ) : ℂ) := fun q => by
    rw [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hline, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination ((t q : ℂ) ^ 2 / 2) * Complex.I_sq
  have hsw : Summable fun q : ZIdx => Real.exp (-(t q) ^ 2 / 2) := by
    refine summable_gw.congr fun q => ?_
    unfold gw poleP
    rw [Complex.norm_exp]
    congr 1
    rw [show (2 * (zetaZeroFamily q - 1 / 2)) ^ 2 / 8 = (zetaZeroFamily q - 1 / 2) ^ 2 / 2 by ring, hline]
    simp [sq]
  unfold BallKernel.kerK
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  have hpos : 0 < ∑' q : ZIdx, Real.exp (-(t q) ^ 2 / 2) :=
    hsw.tsum_pos (fun q => (Real.exp_pos _).le) q0 (Real.exp_pos _)
  exact_mod_cast hpos.ne'

/-- **In every realization of `K`, the orbit spans no lattice**: the vectors `w_{n+1} − w_n`, `n ≥ 1`, of the group it
generates are nonzero and their norms tend to `0`. For the Frobenius points of a curve the corresponding vectors have
`B(P_{k+1} − P_k, P_{k+1} − P_k) = 2q^k·#E(𝔽_q)`, which grows (`ManinHasse.gram_orbit_card`). -/
theorem not_discrete (R : Realization BallKernel.kerK) :
    (∀ n : ℕ, 0 < n → R.w ((n : ℚ) + 1) ≠ R.w n) ∧
      Tendsto (fun n : ℕ => ‖R.w ((n : ℚ) + 1) - R.w n‖) atTop (𝓝 0) := by
  have hRH := rh_of_posDef (posDefQ_of_realization R)
  refine ⟨fun n hn h => ?_, ?_⟩
  · have h1 := norm_sq_w R (show (0 : ℚ) < n + 1 by positivity)
    have h2 := norm_sq_w R (show (0 : ℚ) < n by exact_mod_cast hn)
    rw [h] at h1
    have h3 := h1.symm.trans h2
    push_cast at h3
    exact kerK_one_ne_zero hRH (by linear_combination h3)
  · obtain ⟨M, hM⟩ := kerK_smooth
    exact tendsto_norm_sub_of_smooth R hM

end BallLattice

#print axioms BallLattice.gram_shape
#print axioms BallLattice.re_eq_half_of_eigen
#print axioms BallLattice.rh_iff_realization
#print axioms BallLattice.phi_single
#print axioms BallLattice.tendsto_norm_sub_of_smooth
#print axioms BallLattice.kerK_smooth
#print axioms BallLattice.not_discrete
