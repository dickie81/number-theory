/-
# Primes in almost all short intervals, part 3: the exceptional set

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`almost_all_short_primes`). For every `θ > 1/6` there is `δ > 0` such that, for all large `X`, the
`y ∈ [X, 2X]` for which `(y, y + y^θ]` holds no prime form a set of measure at most `X^{1−δ}`. This is Huxley's
companion to his exponent `7/12`: a density estimate `N(σ, T) ≪ T^{A(1−σ)+ε}` gives primes in almost all intervals of
length `y^θ` for `θ > 1 − 2/A` (`almost_all_of_density`), and `A = 12/5` gives `1/6`.

The scale `X` fixes `b = X^{θ'−1}` and `T = X^{1−θ'+ε}` for some `θ'` between `1 − 2/A` and `θ`. For `y ∈ [X, 2X]` the
explicit formula is taken at `x = ye^{2D}`, `D = 2^{J+1}b`, whose window `[xe^{−D}, xe^{D}] = [ye^{D}, ye^{3D}]` lies in
`(y, y + y^θ]`:
* `prime_of_head_small`: the pole term beats the archimedean term (`AlmostAll.arch_far`) and the zeros with
  `|Re τ| > T` (`norm_tail_le`, from `ShortWeil.tail_le`), so a prime is found unless the zeros with `|Re τ| ≤ T`
  (`ZH`, a finite sum) are large at `L = log y + 2D`.
* `bad_measure_le`: by Markov's inequality in `L` against the weight `1 − cos(L − L₀)`, `L₀ = log X − 2`, and the change
  of variables `y = e^t`, the exceptional `y` have measure at most `32/m₀² · ∫|ZH|²W`, `m₀ = (2be^{−b/2})^k`.
* `head_sum_le`: `AlmostAll.head_mean_square` with `|ĝ(τ)| ≤ (4be^{b/2})^{2^J}`, and `ShortWeil.head_le` with the
  density estimate and the half-plane `|Im τ| ≤ 5/12` (`HalfPlaneJoins.abs_im_tau_le_five_twelfths`), which removes
  the zeros near `σ = 1` that would otherwise need the Korobov–Vinogradov region.
* `almost_all_of_density`: the exponents. The mean square carries `X^{1/M}(T^A/X²)^{1/12}` against `X`, and
  `T^A ≤ X^{2−κ/2}` with `κ = 2 − A(1 − θ')`.
-/
import AlmostAllMean
import HalfPlaneJoinsFinal
import ZetaHuxley

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace AlmostAll

open ShortWeil WeilForm WeilTest WeilStrip Kaiser

/-! ## The head and the tail of the zero sum -/

/-- The zeros of `Ξ` with `|Re τ| ≤ T`. -/
def headSet (T : ℝ) : Finset (ZeroIdx (sqF Xi)) := (finite_re_le T).toFinset

theorem mem_headSet {T : ℝ} {i : ZeroIdx (sqF Xi)} : i ∈ headSet T ↔ |(tau i).re| ≤ T := by
  simp [headSet]

/-- The head of the zero sum, `Σ_{|Re τ| ≤ T} h(τ)`. -/
def ZH (b : ℝ) (J : ℕ) (T L : ℝ) : ℂ := ∑ i ∈ headSet T, hmod b J L (tau i)

theorem continuous_ZH (b : ℝ) (J : ℕ) (T : ℝ) : Continuous (ZH b J T) := by
  unfold ZH hmod
  exact continuous_finsetSum _ fun i _ => by fun_prop

/-- **The tail**: `‖Σ_τ h(τ) − ZH‖ ≤ 2e^{L/2}(4be^{b/2})^k · 4S₀/(b²(bT)^{k−2})`. -/
theorem norm_tail_le {b : ℝ} (hb : 0 < b) (J : ℕ) {L T : ℝ} (hL : 0 ≤ L) (hT : 1 ≤ T) :
    ‖∑' i : ZeroIdx (sqF Xi), hmod b J L (tau i) - ZH b J T L‖
      ≤ 2 * Real.exp (L / 2) * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1))
        * (4 * S0 / (b ^ 2 * (b * T) ^ (2 ^ (J + 1) - 2))) := by
  set c := 2 * Real.exp (L / 2) * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1)) with hc
  set h : ZeroIdx (sqF Xi) → ℂ := fun i => hmod b J L (tau i) with hh
  have hs : Summable h := summable_hmod_tau hb J hL
  set f : ZeroIdx (sqF Xi) → ℂ := fun i => if |(tau i).re| ≤ T then h i else 0 with hf
  set g : ZeroIdx (sqF Xi) → ℂ := fun i => if |(tau i).re| ≤ T then 0 else h i with hg
  have hfg : ∀ i, h i = f i + g i := fun i => by simp only [hf, hg]; split_ifs <;> simp
  have hfs : Summable f := summable_of_ne_finset_zero (s := headSet T) fun i hi => by
    rw [mem_headSet] at hi; simp [hf, hi]
  have hgs : Summable g := by
    have e : g = fun i => h i - f i := funext fun i => by rw [hfg i]; ring
    rw [e]; exact hs.sub hfs
  have hfsum : ∑' i, f i = ZH b J T L := by
    rw [tsum_eq_sum (s := headSet T) (fun i hi => by rw [mem_headSet] at hi; simp [hf, hi])]
    unfold ZH
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_headSet] at hi; simp [hf, hh, hi]
  have hsplit : ∑' i, h i = ∑' i, f i + ∑' i, g i := by
    rw [← hfs.tsum_add hgs]; exact tsum_congr hfg
  rw [hsplit, hfsum, add_sub_cancel_left]
  have hk : 2 ≤ 2 ^ (J + 1) := two_le_two_pow_succ J
  have hw := summable_wT (Real.one_le_exp hL) hb hk
  set w : ZeroIdx (sqF Xi) → ℝ := fun i =>
    if |(tau i).re| ≤ T then 0 else wT (Real.exp L) b (2 ^ (J + 1)) (tau i) with hwd
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    simp only [hwd]; split_ifs
    · exact le_rfl
    · exact wT_nonneg (Real.exp_pos L) hb.le _ _
  have hws : Summable w := Summable.of_nonneg_of_le hw0 (fun i => by
    simp only [hwd]; split_ifs
    · exact wT_nonneg (Real.exp_pos L) hb.le _ _
    · exact le_rfl) hw
  have hpt : ∀ i, ‖g i‖ ≤ c * w i := fun i => by
    simp only [hg, hwd]; split_ifs
    · simp
    · simpa [hh, hc] using norm_hmod_tau_le hb J hL i
  have hgn : Summable fun i => ‖g i‖ := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hpt (hws.mul_left c)
  have hc0 : 0 ≤ c := by positivity
  calc ‖∑' i, g i‖ ≤ ∑' i, ‖g i‖ := norm_tsum_le_tsum_norm hgn
    _ ≤ ∑' i, c * w i := hgn.tsum_le_tsum hpt (hws.mul_left c)
    _ = c * ∑' i, w i := tsum_mul_left
    _ ≤ c * (4 * S0 / (b ^ 2 * (b * T) ^ (2 ^ (J + 1) - 2))) :=
        mul_le_mul_of_nonneg_left (tail_le (Real.one_le_exp hL) hb hT hk) hc0

/-! ## A prime near `y` unless the head is large -/

set_option maxHeartbeats 1000000 in
/-- **A prime in `(y, y + y^θ]` unless the head of the zero sum is large at `L = log y + 2D`.** -/
theorem prime_of_head_small {b T X y θ : ℝ} {J : ℕ} (hb : 0 < b) (hJ : 1 ≤ J) (hT : 1 ≤ T)
    (hD : 2 ^ (J + 1) * b ≤ 1 / 4) (hX : Real.exp 2 ≤ X) (hy : y ∈ Icc X (2 * X)) (hθ1 : θ ≤ 1)
    (hW : 2 * Real.log (12 * X) ^ 2 * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1)
      < b * X * Real.exp (-((2 ^ (J + 1) + 1) / 2)))
    (hA : 16 * 2 ^ (J + 1) * Real.exp (2 ^ (J + 1) * b) ≤ X)
    (hTl : 64 * S0 * (2 * Real.exp b) ^ (2 ^ (J + 1)) ≤ b ^ 2 * (b * T) ^ (2 ^ (J + 1) - 2))
    (hwin : Real.exp (3 * (2 ^ (J + 1) * b)) - 1 ≤ (2 * X) ^ (θ - 1))
    (hsmall : ‖ZH b J T (Real.log y + 2 * (2 ^ (J + 1) * b))‖
      ≤ Real.sqrt X * (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1)) / 4) :
    ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  set k := 2 ^ (J + 1) with hk
  set D : ℝ := 2 ^ (J + 1) * b with hDdef
  set m₀ := (2 * b * Real.exp (-(b / 2))) ^ k with hm₀
  have hkR : (k : ℝ) = (2 : ℝ) ^ (J + 1) := by rw [hk]; push_cast; ring
  have hk4 : (4 : ℝ) ≤ (2 : ℝ) ^ (J + 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hD0 : 0 < D := by positivity
  have hb1 : b ≤ 1 := by nlinarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX : 2 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hX
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 < y := lt_of_lt_of_le hX0 hy1
  set L := Real.log y + 2 * D with hL
  set x := Real.exp L with hx
  have hxy : x = y * Real.exp (2 * D) := by rw [hx, hL, Real.exp_add, Real.exp_log hy0]
  have he2D : Real.exp (2 * D) ≤ 2 := by
    calc Real.exp (2 * D) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
  have hxX : X ≤ x := by
    rw [hxy]; have := Real.one_le_exp (by linarith : 0 ≤ 2 * D); nlinarith
  have hx4 : x ≤ 4 * X := by rw [hxy]; nlinarith [Real.exp_pos (2 * D)]
  have hx0 : 0 < x := Real.exp_pos L
  have hlogy : Real.log X ≤ Real.log y := Real.log_le_log hX0 hy1
  have hLD : D + 1 / 2 ≤ L := by rw [hL]; linarith
  have hLD' : D < L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsx : Real.sqrt x = Real.exp (L / 2) := by
    rw [hx, Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  have hsX : Real.sqrt X ≤ Real.sqrt x := Real.sqrt_le_sqrt hxX
  -- the explicit formula at `x`
  have hid := explicit_identity hb hb1 J hLD'
  have harch := arch_far hb hb1 hJ hLD
  have htail := norm_tail_le hb J hL0 hT (b := b)
  set P := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - L) with hP
  set E := 1 / (2 * π) * ∫ r, hmodR b J L r * psiRe r with hE
  set Zi := ∑' i : ZeroIdx (sqF Xi), hmod b J L (tau i) with hZi
  -- the pole term
  have hpole : 2 * Real.sqrt x * m₀ ≤ 4 * Real.cosh (L / 2) * poleR (bx b) b ^ k := by
    have hp := poleR_bx_ge hb.le
    have hpk : m₀ ≤ poleR (bx b) b ^ k := pow_le_pow_left₀ (by positivity) hp k
    have hcosh : Real.exp (L / 2) ≤ 2 * Real.cosh (L / 2) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(L / 2))]
    rw [hsx]
    have hm0 : 0 ≤ m₀ := by positivity
    nlinarith [Real.exp_pos (L / 2)]
  -- the archimedean term
  have hE4 : |E| ≤ Real.sqrt x * m₀ / 4 := by
    have harch' : |E| ≤ 8 * D * (2 * b) ^ (k - 1) * Real.exp (-((L - D) / 2)) := harch
    refine harch'.trans ?_
    have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_two_pow
    set Q := (2 * b) ^ (k - 1) with hQ
    set E2 := Real.exp (D / 2) with hE2
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hE20 : 0 < E2 := Real.exp_pos _
    have hQ0 : 0 < Q := by positivity
    have e1 : Real.exp (-((L - D) / 2)) = E2 / Real.sqrt x := by
      rw [hsx, hE2, ← Real.exp_sub]; congr 1; ring
    have e2 : m₀ = Q * (2 * b) / E2 := by
      rw [eq_div_iff hE20.ne', hm₀, mul_pow, hQ, ← pow_succ, Nat.sub_add_cancel hk1, ← Real.exp_nat_mul, hE2,
        mul_assoc, ← Real.exp_add]
      have : (k : ℝ) * -(b / 2) + D / 2 = 0 := by rw [hDdef, hkR]; ring
      rw [this, Real.exp_zero, mul_one]
    rw [e1, e2]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hEE : E2 * E2 = Real.exp D := by rw [hE2, ← Real.exp_add]; ring_nf
    have hA' : 16 * (k : ℝ) * Real.exp D ≤ x := by rw [hkR]; linarith
    have hDk : D = (k : ℝ) * b := by rw [hDdef, hkR]
    have hc : 0 < 4 * Real.sqrt x * E2 := by positivity
    refine le_of_mul_le_mul_right ?_ hc
    have l1 : 8 * D * Q * (E2 / Real.sqrt x) * (4 * Real.sqrt x * E2) = 32 * D * Q * (E2 * E2) := by
      field_simp; ring
    have l2 : Real.sqrt x * (Q * (2 * b) / E2) / 4 * (4 * Real.sqrt x * E2)
        = (Real.sqrt x * Real.sqrt x) * Q * (2 * b) := by
      field_simp
    rw [l1, l2, hxx, hEE]
    calc 32 * D * Q * Real.exp D = (16 * k * Real.exp D) * Q * (2 * b) := by rw [hDk]; ring
      _ ≤ x * Q * (2 * b) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA' hQ0.le) (by positivity)
  -- the tail
  have hT8 : ‖Zi - ZH b J T L‖ ≤ Real.sqrt x * m₀ / 8 := by
    refine htail.trans ?_
    have e : (4 * b * Real.exp (b / 2)) ^ k = (2 * Real.exp b) ^ k * m₀ := by
      rw [hm₀, ← mul_pow]; congr 1
      have : Real.exp b * Real.exp (-(b / 2)) = Real.exp (b / 2) := by rw [← Real.exp_add]; ring_nf
      linear_combination (-(4 * b)) * this
    rw [← hsx, e]
    set R := b ^ 2 * (b * T) ^ (k - 2) with hR
    have hR0 : 0 < R := by positivity
    have hTl' : 8 * S0 * (2 * Real.exp b) ^ k ≤ R / 8 := by linarith
    have hm0 : 0 ≤ m₀ := by positivity
    calc 2 * Real.sqrt x * ((2 * Real.exp b) ^ k * m₀) * (4 * S0 / R)
        = Real.sqrt x * m₀ * (8 * S0 * (2 * Real.exp b) ^ k) / R := by ring
      _ ≤ Real.sqrt x * m₀ * (R / 8) / R := by gcongr
      _ = Real.sqrt x * m₀ / 8 := by field_simp
  -- the zero sum
  have hZ : (2 * Zi).re ≤ Real.sqrt x * m₀ * 3 / 4 := by
    have h1 : (2 * Zi).re = 2 * Zi.re := by simp [Complex.mul_re]
    have h2 : Zi.re ≤ ‖Zi‖ := Complex.re_le_norm Zi
    have h3 : ‖Zi‖ ≤ ‖ZH b J T L‖ + ‖Zi - ZH b J T L‖ := by
      have := norm_add_le (ZH b J T L) (Zi - ZH b J T L)
      rwa [add_sub_cancel] at this
    have h4 : ‖ZH b J T L‖ ≤ Real.sqrt x * m₀ / 4 := by
      refine hsmall.trans ?_
      have hm0 : 0 ≤ m₀ := by positivity
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsX hm0) (by norm_num)
    calc (2 * Zi).re = 2 * Zi.re := h1
      _ ≤ 2 * (‖ZH b J T L‖ + ‖Zi - ZH b J T L‖) := mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
      _ ≤ 2 * (Real.sqrt x * m₀ / 4 + Real.sqrt x * m₀ / 8) :=
          mul_le_mul_of_nonneg_left (add_le_add h4 hT8) (by norm_num)
      _ = Real.sqrt x * m₀ * 3 / 4 := by ring
  have hP2 : Real.sqrt x * m₀ ≤ 2 * P := by
    have hE' := (abs_le.1 hE4).1
    rw [hid]
    calc Real.sqrt x * m₀ = 2 * Real.sqrt x * m₀ - Real.sqrt x * m₀ / 4 - Real.sqrt x * m₀ * 3 / 4 := by ring
      _ ≤ 4 * Real.cosh (L / 2) * poleR (bx b) b ^ k + E - (2 * Zi).re :=
          sub_le_sub (add_le_add hpole hE' |>.trans_eq' (by ring)) hZ
  -- the window
  have hlx : Real.log x = L := Real.log_exp L
  have hD1 : 2 ^ (J + 1) * b ≤ 1 := by linarith
  have hx3 : 3 ≤ x := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    linarith
  have hW' : 2 * Real.log (3 * x) ^ 2 * (8 * (2 ^ (J + 1) * b) * Real.sqrt x + 1)
      < b * x * Real.exp (-((2 ^ (J + 1) + 1) / 2)) := by
    have hl1 : Real.log (3 * x) ≤ Real.log (12 * X) := Real.log_le_log (by positivity) (by linarith)
    have hl0 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    have hsx2 : Real.sqrt x ≤ 2 * Real.sqrt X := by
      rw [show (2 : ℝ) * Real.sqrt X = Real.sqrt (4 * X) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hx4
    have h1 : 2 * Real.log (3 * x) ^ 2 * (8 * D * Real.sqrt x + 1)
        ≤ 2 * Real.log (12 * X) ^ 2 * (16 * D * Real.sqrt X + 1) := by
      have : 8 * D * Real.sqrt x + 1 ≤ 16 * D * Real.sqrt X + 1 := by nlinarith
      have hsq : Real.log (3 * x) ^ 2 ≤ Real.log (12 * X) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
      have : 0 ≤ 8 * D * Real.sqrt x + 1 := by positivity
      nlinarith
    have h2 : b * X * Real.exp (-((2 ^ (J + 1) + 1) / 2)) ≤ b * x * Real.exp (-((2 ^ (J + 1) + 1) / 2)) := by
      gcongr
    linarith
  have hP2' : Real.sqrt x * (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1))
      ≤ 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x) := by
    rw [hlx]; exact hP2
  obtain ⟨p, hp, hp1, hp2⟩ := prime_of_P hb hD1 hx3 hP2' hW'
  refine ⟨p, hp, ?_, ?_⟩
  · have : y < x * Real.exp (-D) := by
      rw [hxy, mul_assoc, ← Real.exp_add, show 2 * D + -D = D by ring]
      have := Real.add_one_le_exp D
      nlinarith
    linarith
  · have h1 : x * Real.exp D = y * Real.exp (3 * D) := by
      rw [hxy, mul_assoc, ← Real.exp_add]; congr 2; ring
    have h2 : y * (Real.exp (3 * D) - 1) ≤ y ^ θ := by
      have h3 : (2 * X) ^ (θ - 1) ≤ y ^ (θ - 1) := Real.rpow_le_rpow_of_nonpos hy0 hy2 (sub_nonpos.2 hθ1)
      have h4 : y * y ^ (θ - 1) = y ^ θ := by
        conv_rhs => rw [show θ = 1 + (θ - 1) by ring, Real.rpow_add hy0, Real.rpow_one]
      calc y * (Real.exp (3 * D) - 1) ≤ y * y ^ (θ - 1) := mul_le_mul_of_nonneg_left (hwin.trans h3) hy0.le
        _ = y ^ θ := h4
    rw [h1] at hp2
    linarith

/-! ## The measure of the exceptional set at one scale -/

/-- **The exceptional set at one scale**: the `y ∈ [X, 2X]` with no prime in `(y, y + y^θ]` have measure at most
`32/m₀² · ∫_{L₀}^{L₀+2π} |ZH(L)|²(1 − cos(L − L₀)) dL`, `L₀ = log X − 2`, `m₀ = (2be^{−b/2})^k`. -/
theorem bad_measure_le {b T X θ : ℝ} {J : ℕ} (hb : 0 < b) (hJ : 1 ≤ J) (hT : 1 ≤ T)
    (hD : 2 ^ (J + 1) * b ≤ 1 / 4) (hX : Real.exp 2 ≤ X) (hθ1 : θ ≤ 1)
    (hW : 2 * Real.log (12 * X) ^ 2 * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1)
      < b * X * Real.exp (-((2 ^ (J + 1) + 1) / 2)))
    (hA : 16 * 2 ^ (J + 1) * Real.exp (2 ^ (J + 1) * b) ≤ X)
    (hTl : 64 * S0 * (2 * Real.exp b) ^ (2 ^ (J + 1)) ≤ b ^ 2 * (b * T) ^ (2 ^ (J + 1) - 2))
    (hwin : Real.exp (3 * (2 ^ (J + 1) * b)) - 1 ≤ (2 * X) ^ (θ - 1)) :
    volume {y | y ∈ Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
      ≤ ENNReal.ofReal (32 / ((2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1))) ^ 2
        * ∫ L in (Real.log X - 2)..(Real.log X - 2 + 2 * π),
          ‖ZH b J T L‖ ^ 2 * (1 - Real.cos (L - (Real.log X - 2)))) := by
  set D : ℝ := 2 ^ (J + 1) * b with hDdef
  set m₀ := (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1)) with hm₀
  set L₀ := Real.log X - 2 with hL₀
  set L₁ := L₀ + 2 * π with hL₁
  set c := Real.sqrt X * m₀ / 4 with hc
  set f : ℝ → ℝ := fun L => ‖ZH b J T L‖ ^ 2 * (1 - Real.cos (L - L₀)) with hf
  set I := ∫ L in L₀..L₁, f L with hI
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX : 2 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have hD0 : 0 < D := by positivity
  have hm0 : 0 < m₀ := by positivity
  have hc0 : 0 < c := by positivity
  have hfc : Continuous f := by
    simp only [hf]
    exact ((continuous_ZH b J T).norm.pow 2).mul (by fun_prop)
  -- the exceptional `y` through `t = log y`
  set S' := {t : ℝ | t ∈ Icc (Real.log X) (Real.log (2 * X)) ∧ c < ‖ZH b J T (t + 2 * D)‖} with hS'
  have hsub1 : {y | y ∈ Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ} ⊆ Real.exp '' S' := by
    rintro y ⟨hy, hno⟩
    have hy0 : 0 < y := lt_of_lt_of_le hX0 hy.1
    refine ⟨Real.log y, ⟨⟨Real.log_le_log hX0 hy.1, Real.log_le_log hy0 hy.2⟩, ?_⟩, Real.exp_log hy0⟩
    by_contra hle
    push Not at hle
    exact hno (prime_of_head_small hb hJ hT hD hX hy hθ1 hW hA hTl hwin hle)
  have hS'm : MeasurableSet S' :=
    measurableSet_Icc.inter (measurableSet_lt measurable_const
      ((continuous_ZH b J T).comp (continuous_id.add continuous_const)).norm.measurable)
  have hexp_img : volume (Real.exp '' S') ≤ ENNReal.ofReal (2 * X) * volume S' := by
    have h := lintegral_image_eq_lintegral_abs_deriv_mul hS'm
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn (fun _ => 1)
    rw [setLIntegral_one] at h
    rw [h, ← setLIntegral_const]
    refine setLIntegral_mono' hS'm fun t ht => ?_
    rw [mul_one, abs_of_pos (Real.exp_pos t)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp t ≤ Real.exp (Real.log (2 * X)) := Real.exp_le_exp.2 ht.1.2
      _ = 2 * X := Real.exp_log (by positivity)
  -- shifted into the middle of the window, where the weight is at least 1
  set S'' := {L : ℝ | L ∈ Icc L₀ L₁ ∧ c ^ 2 ≤ f L} with hS''
  have hsub2 : S' ⊆ (fun t => t + 2 * D) ⁻¹' S'' := by
    rintro t ⟨⟨ht1, ht2⟩, hct⟩
    have hlog2 : Real.log (2 * X) = Real.log 2 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hpi := Real.pi_gt_three
    have hpi4 := Real.pi_le_four
    have hlo : π / 2 ≤ t + 2 * D - L₀ := by rw [hL₀]; linarith
    have hhi : t + 2 * D - L₀ ≤ π + π / 2 := by rw [hL₀]; linarith
    have hcos : Real.cos (t + 2 * D - L₀) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hlo hhi
    refine ⟨⟨by linarith, by rw [hL₁]; linarith⟩, ?_⟩
    simp only [hf]
    have hsq : c ^ 2 ≤ ‖ZH b J T (t + 2 * D)‖ ^ 2 := pow_le_pow_left₀ hc0.le hct.le 2
    have hn : 0 ≤ ‖ZH b J T (t + 2 * D)‖ ^ 2 := by positivity
    nlinarith
  have hS''v : volume S' ≤ volume S'' := by
    calc volume S' ≤ volume ((fun t => t + 2 * D) ⁻¹' S'') := measure_mono hsub2
      _ = volume S'' := measure_preimage_add_right volume (2 * D) S''
  -- Markov's inequality
  have hL01 : L₀ ≤ L₁ := by rw [hL₁]; linarith [Real.pi_pos]
  set μ := volume.restrict (Icc L₀ L₁) with hμ
  have hf0 : ∀ L, 0 ≤ f L := fun L => by
    simp only [hf]; have := Real.cos_le_one (L - L₀); positivity
  have hfint : Integrable f μ := (hfc.integrableOn_Icc).integrable
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Eventually.of_forall hf0) hfint (c ^ 2)
  have hIeq : ∫ L, f L ∂μ = I := by
    rw [hI, intervalIntegral.integral_of_le hL01, hμ, integral_Icc_eq_integral_Ioc]
  rw [hIeq] at hmk
  have hS''μ : volume S'' = μ {L | c ^ 2 ≤ f L} := by
    rw [hμ, Measure.restrict_apply' measurableSet_Icc]
    congr 1; ext L; simp only [hS'', mem_ofPred_eq, mem_inter_iff]; tauto
  have hfin : μ {L | c ^ 2 ≤ f L} ≠ ⊤ := by
    rw [hμ, Measure.restrict_apply' measurableSet_Icc]
    exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right)
  have hS''le : volume S'' ≤ ENNReal.ofReal (I / c ^ 2) := by
    rw [hS''μ, ← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hmk
  -- assemble
  have hc2 : c ^ 2 = X * m₀ ^ 2 / 16 := by
    rw [hc, div_pow, mul_pow, Real.sq_sqrt hX0.le]; ring
  calc volume {y | y ∈ Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
      ≤ volume (Real.exp '' S') := measure_mono hsub1
    _ ≤ ENNReal.ofReal (2 * X) * volume S' := hexp_img
    _ ≤ ENNReal.ofReal (2 * X) * ENNReal.ofReal (I / c ^ 2) := by gcongr; exact hS''v.trans hS''le
    _ = ENNReal.ofReal (2 * X * (I / c ^ 2)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (32 / m₀ ^ 2 * I) := by
        congr 1; rw [hc2]; field_simp; ring

/-- **The head's mean square through the density estimate**: with `L₁ = L₀ + 2π`, `x₁ = e^{L₁}` and
`T^A ≤ x₁²`,
`∫|ZH|²W ≤ 180π(5 + kLam + ½ log(T + 2))(4be^{b/2})^{2k} x₁ M(x₁²)^{1/(2M)} C(log T)^B (T^A/x₁²)^{1/12}`. -/
theorem head_integral_le {b T L₀ : ℝ} {J M : ℕ} {A B C : ℝ} (hb : 0 < b) (hL₀ : 0 ≤ L₀) (hT : 2 ≤ T)
    (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hden : ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 → (NX w T : ℝ) ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B)
    (hQ : T ^ A ≤ Real.exp (2 * (L₀ + 2 * π))) :
    ∫ L in L₀..L₀ + 2 * π, ‖ZH b J T L‖ ^ 2 * (1 - Real.cos (L - L₀))
      ≤ 180 * π * (5 + kLam + Real.log (T + 2) / 2) * (4 * b * Real.exp (b / 2)) ^ (2 * 2 ^ (J + 1))
        * (Real.exp (L₀ + 2 * π) * (M * Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) * (C * Real.log T ^ B)
          * (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ))) := by
  set L₁ := L₀ + 2 * π with hL₁
  set S := headSet T with hS
  have hT0 : 0 ≤ T := by linarith
  have hmean := head_mean_square (b := b) J hL₀ hT0 S fun i hi => mem_headSet.1 hi
  refine hmean.trans ?_
  have hC0 : 0 ≤ 5 + kLam + Real.log (T + 2) / 2 := by
    have := Kaiser.kLam_nonneg; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); positivity
  rw [mul_assoc (180 * π * (5 + kLam + Real.log (T + 2) / 2))]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hC0)
  set G := (4 * b * Real.exp (b / 2)) ^ (2 * 2 ^ (J + 1)) with hG
  set x₂ := Real.exp (2 * L₁) with hx₂
  -- each term
  have hterm : ∀ i ∈ S, ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ^ 4 * Real.exp (2 * L₁ * |(tau i).im|)
      ≤ G * (Real.exp L₁ * x₂ ^ (|(tau i).im| - 1 / 2)) := by
    intro i _
    have hg := norm_ghatC_gI_le hb J (tau i)
    have him := (abs_lt.1 (tau_im i))
    have hg' : ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ≤ (4 * b * Real.exp (b / 2)) ^ (2 ^ J) := by
      refine hg.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      rw [div_le_iff₀ (by positivity)]
      have h1 : Real.exp (b * |(tau i).im|) ≤ Real.exp (b / 2) :=
        Real.exp_le_exp.2 (by nlinarith [abs_nonneg (tau i).im, tau_im i])
      have h2 : 0 ≤ b * ‖tau i‖ := by positivity
      have h3 : 0 ≤ 4 * b * Real.exp (b / 2) := by positivity
      nlinarith [Real.exp_pos (b * |(tau i).im|)]
    have hg4 : ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ^ 4 ≤ G := by
      calc ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ^ 4 ≤ ((4 * b * Real.exp (b / 2)) ^ (2 ^ J)) ^ 4 :=
            pow_le_pow_left₀ (norm_nonneg _) hg' 4
        _ = G := by rw [hG, ← pow_mul]; congr 1; rw [pow_succ]; ring
    have he : Real.exp (2 * L₁ * |(tau i).im|) = Real.exp L₁ * x₂ ^ (|(tau i).im| - 1 / 2) := by
      rw [hx₂, ← Real.exp_mul, ← Real.exp_add]; congr 1; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hg4 (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) (by positivity)
  -- `ShortWeil.head_le` at `x = e^{2L₁}`
  have hx1 : 1 ≤ x₂ := Real.one_le_exp (by positivity)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hQ0 : 0 < T ^ A := Real.rpow_pos_of_pos (by linarith) A
  refine head_le S (fun i => |(tau i).im|) (fun i _ => abs_nonneg _) hx1 hQ0 hQ (by positivity)
    (fun i _ => tau_im i) (fun i _ => by
      have := HalfPlaneJoins.abs_im_tau_le_five_twelfths i; linarith) hM (fun j hj => ?_)
  have hw0 : (0 : ℝ) ≤ (j : ℝ) / (2 * M) := by positivity
  have hw1 : (j : ℝ) / (2 * M) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (j : ℝ) < M := by exact_mod_cast hj
    linarith
  have h := hden _ hw0 hw1
  rw [NX_eq_card] at h
  calc ((S.filter fun i => (j : ℝ) / (2 * M) ≤ |(tau i).im|).card : ℝ)
      ≤ C * T ^ (A * (1 / 2 - (j : ℝ) / (2 * M))) * Real.log T ^ B := h
    _ = C * Real.log T ^ B * (T ^ A) ^ (1 / 2 - (j : ℝ) / (2 * M)) := by
        rw [← Real.rpow_mul (by linarith)]; ring

/-! ## The exponents -/

theorem eventually_log_rpow_le (r : ℝ) {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ r ≤ c * X ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).bound hc
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have h1 : 0 ≤ Real.log X ^ r := Real.rpow_nonneg (Real.log_nonneg hX1) r
  have h2 : 0 ≤ X ^ s := Real.rpow_nonneg (by linarith) s
  rwa [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] at hX

theorem eventually_rpow_ge {a : ℝ} (ha : 0 < a) (c : ℝ) : ∀ᶠ X : ℝ in atTop, c ≤ X ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop c

set_option maxHeartbeats 4000000 in
/-- **Primes in almost all short intervals, from a density estimate.** If `N(σ, T) ≪ T^{(A₀+ε)(1−σ)}(log T)^B` for
every `ε > 0`, then for every `θ` with `max(0, 1 − 2/A₀) < θ ≤ 1` there is `δ > 0` such that for all large `X` the
`y ∈ [X, 2X]` with no prime in `(y, y + y^θ]` have measure at most `X^{1−δ}`. -/
theorem almost_all_of_density {A₀ : ℝ} (hA₀ : 0 < A₀) (hd : ∀ ε > 0, ∃ B : ℝ, DensityXi (A₀ + ε) B)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθ : 1 - 2 / A₀ < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      volume {y | y ∈ Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
        ≤ ENNReal.ofReal (X ^ (1 - δ)) := by
  -- the exponents
  set lo := max 0 (1 - 2 / A₀) with hlo
  have hlo0 : 0 ≤ lo := le_max_left _ _
  have hlo1 : 1 - 2 / A₀ ≤ lo := le_max_right _ _
  have hloθ : lo < θ := max_lt hθ0 hθ
  set θ' := (lo + θ) / 2 with hθ'
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  have hθ'θ : θ' < θ := by rw [hθ']; linarith
  have hθ'1 : θ' < 1 := by linarith
  have hθ'A : 1 - 2 / A₀ < θ' := by rw [hθ']; linarith
  set κ := 2 - A₀ * (1 - θ') with hκ
  have hκ0 : 0 < κ := by
    have h1 : 1 - θ' < 2 / A₀ := by linarith
    have h2 := (lt_div_iff₀ hA₀).1 h1
    rw [hκ]; linarith
  set ε := min (1 / 2) (κ / (4 * (2 + A₀))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ κ / (4 * (2 + A₀)) := min_le_right _ _
  set A := A₀ + ε with hA
  obtain ⟨B, C, hC, hCd⟩ := hd ε hε0
  have hAexp : A * (1 - θ' + ε) ≤ 2 - κ / 2 := by
    have h1 : ε * (2 + A₀) ≤ κ / 4 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (2 + A₀))).1 hε2
      linarith
    have h2 : A * (1 - θ' + ε) = A₀ * (1 - θ') + ε * (1 - θ' + A₀ + ε) := by rw [hA]; ring
    have h3 : ε * (1 - θ' + A₀ + ε) ≤ ε * (2 + A₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hε0.le
    rw [h2]; linarith
  -- `J` and `M`
  set J := ⌈3 / ε⌉₊ + 1 with hJ
  have hJ1 : 1 ≤ J := by omega
  set k := 2 ^ (J + 1) with hk
  have hkJ : J + 2 ≤ k := by
    have h : J + 1 < 2 ^ (J + 1) := Nat.lt_two_pow_self
    rw [hk]; omega
  have hkR : (k : ℝ) = (2 : ℝ) ^ (J + 1) := by rw [hk]; push_cast; ring
  have hεk : 3 ≤ ε * ((k : ℝ) - 2) := by
    have h1 : 3 / ε ≤ (⌈3 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (J : ℝ) + 2 ≤ k := by exact_mod_cast hkJ
    have h3 : (J : ℝ) = ⌈3 / ε⌉₊ + 1 := by rw [hJ]; push_cast; ring
    have h4 : 3 / ε ≤ (k : ℝ) - 2 := by linarith
    rw [div_le_iff₀ hε0] at h4; linarith
  set M := ⌈48 / κ⌉₊ + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMκ : 1 / (M : ℝ) ≤ κ / 48 := by
    have h1 : 48 / κ ≤ (⌈48 / κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (M : ℝ) = ⌈48 / κ⌉₊ + 1 := by rw [hM]; push_cast; ring
    have hM0 : (0 : ℝ) < M := by rw [h2]; positivity
    rw [div_le_div_iff₀ hM0 (by norm_num)]
    rw [div_le_iff₀ hκ0] at h1
    nlinarith
  set δ := κ / 100 with hδ
  refine ⟨δ, by positivity, ?_⟩
  -- constants of the final bound
  set K := 32 * (180 * π) * (2 * Real.exp 1) ^ (2 * k) * Real.exp (2 * π - 2) * M * Real.exp (2 * π) * C
    with hK
  have hK0 : 0 ≤ K := by positivity
  set c₁ := Real.exp (-((2 ^ (J + 1) + 1) / 2)) / (16 * (16 * 2 ^ (J + 1) + 1)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set s₁ := min (1 / 2) θ' with hs₁
  have hs₁0 : 0 < s₁ := lt_min (by norm_num) hθ'0
  set s₂ := κ / 48 - κ / 100 with hs₂
  have hs₂0 : 0 < s₂ := by rw [hs₂]; linarith
  -- the eventual conditions
  have e1 : ∀ᶠ X : ℝ in atTop, (2 : ℝ) ^ (J + 1) * X ^ (θ' - 1) ≤ 1 / 4 := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - θ')).const_mul ((2 : ℝ) ^ (J + 1))
    rw [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with X hX
    rw [show θ' - 1 = -(1 - θ') by ring]; exact hX.le
  have e2 := eventually_log_rpow_le 2 hs₁0 hc₁0
  have e3 := eventually_ge_atTop (max (max (Real.exp 2) 12) (max (32 * 2 ^ (J + 1)) (64 * S0 * (2 * Real.exp 1) ^ k)))
  have e5 := eventually_rpow_ge (by linarith : 0 < θ - θ') (12 * 2 ^ (J + 1))
  have e6 := eventually_rpow_ge (by linarith : 0 < 1 - θ' + ε) 3
  have e7 := eventually_log_rpow_le (|B| + 1) hs₂0 (by positivity : (0 : ℝ) < 1 / (3 * K * 2 ^ |B| + 1))
  have e8 := (Real.tendsto_log_atTop.eventually_ge_atTop (5 + kLam))
  filter_upwards [e1, e2, e3, e5, e6, e7, e8] with X h1 h2 h3 h5 h6 h7 h8
  -- the scale `X`
  have hX2 : Real.exp 2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h3
  have hX12 : 12 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h3
  have hX32 : 32 * 2 ^ (J + 1) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h3
  have hX64 : 64 * S0 * (2 * Real.exp 1) ^ k ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h3
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hlogX : 2 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX2
  set b := X ^ (θ' - 1) with hb
  set T := X ^ (1 - θ' + ε) with hT
  have hb0 : 0 < b := Real.rpow_pos_of_pos hX0 _
  have hb1 : b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hT3 : 3 ≤ T := h6
  have hD : 2 ^ (J + 1) * b ≤ 1 / 4 := h1
  -- `hW`
  have hW : 2 * Real.log (12 * X) ^ 2 * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1)
      < b * X * Real.exp (-((2 ^ (J + 1) + 1) / 2)) := by
    have hl12 : Real.log (12 * X) ≤ 2 * Real.log X := by
      rw [Real.log_mul (by norm_num) hX0.ne']
      have : Real.log 12 ≤ Real.log X := Real.log_le_log (by norm_num) hX12
      linarith
    have hl0 : 0 ≤ Real.log (12 * X) := Real.log_nonneg (by linarith)
    have hsq : Real.log (12 * X) ^ 2 ≤ 4 * Real.log X ^ (2 : ℝ) := by
      rw [show Real.log X ^ (2 : ℝ) = Real.log X ^ 2 by norm_cast]
      nlinarith
    have hbX : b * X = X ^ θ' := by
      rw [hb, ← Real.rpow_add_one hX0.ne']; congr 1; ring
    have hbsX : b * Real.sqrt X = X ^ (θ' - 1 / 2) := by
      rw [hb, Real.sqrt_eq_rpow, ← Real.rpow_add hX0]; congr 1; ring
    have hs1 : X ^ s₁ * X ^ (θ' - 1 / 2) ≤ X ^ θ' := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by have := min_le_left (1 / 2 : ℝ) θ'; linarith)
    have hs2 : X ^ s₁ ≤ X ^ θ' := Real.rpow_le_rpow_of_exponent_le hX1 (min_le_right _ _)
    have hXs : 0 ≤ X ^ s₁ := Real.rpow_nonneg hX0.le _
    have hXt : 0 < X ^ θ' := Real.rpow_pos_of_pos hX0 _
    have hEk : 0 < Real.exp (-((2 ^ (J + 1) + 1) / 2)) := Real.exp_pos _
    calc 2 * Real.log (12 * X) ^ 2 * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1)
        ≤ 2 * (4 * (c₁ * X ^ s₁)) * (16 * 2 ^ (J + 1) * (b * Real.sqrt X) + 1) := by
          have hpos : 0 ≤ 16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1 := by positivity
          have := hsq.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
          calc 2 * Real.log (12 * X) ^ 2 * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1)
              ≤ 2 * (4 * (c₁ * X ^ s₁)) * (16 * (2 ^ (J + 1) * b) * Real.sqrt X + 1) := by gcongr
            _ = _ := by ring
      _ = 8 * c₁ * (16 * 2 ^ (J + 1) * (X ^ s₁ * X ^ (θ' - 1 / 2)) + X ^ s₁) := by rw [hbsX]; ring
      _ ≤ 8 * c₁ * (16 * 2 ^ (J + 1) * X ^ θ' + X ^ θ') := by gcongr
      _ = Real.exp (-((2 ^ (J + 1) + 1) / 2)) / 2 * X ^ θ' := by
          rw [hc₁]; field_simp; ring
      _ < Real.exp (-((2 ^ (J + 1) + 1) / 2)) * X ^ θ' := by nlinarith
      _ = b * X * Real.exp (-((2 ^ (J + 1) + 1) / 2)) := by rw [hbX]; ring
  -- `hA`
  have hA' : 16 * 2 ^ (J + 1) * Real.exp (2 ^ (J + 1) * b) ≤ X := by
    have he : Real.exp (2 ^ (J + 1) * b) ≤ 2 := by
      calc Real.exp (2 ^ (J + 1) * b) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
        _ ≤ 2 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 2)]
    have h16 : (0 : ℝ) ≤ 16 * 2 ^ (J + 1) := by positivity
    calc 16 * 2 ^ (J + 1) * Real.exp (2 ^ (J + 1) * b) ≤ 16 * 2 ^ (J + 1) * 2 := mul_le_mul_of_nonneg_left he h16
      _ = 32 * 2 ^ (J + 1) := by ring
      _ ≤ X := hX32
  -- `hTl`
  have hTl : 64 * S0 * (2 * Real.exp b) ^ (2 ^ (J + 1)) ≤ b ^ 2 * (b * T) ^ (2 ^ (J + 1) - 2) := by
    have hbT : b * T = X ^ ε := by rw [hb, hT, ← Real.rpow_add hX0]; congr 1; ring
    have hk2 : 2 ≤ k := le_trans (by omega) hkJ
    have hpow : b ^ 2 * (b * T) ^ (k - 2) = X ^ (2 * (θ' - 1) + ε * ((k : ℝ) - 2)) := by
      rw [hbT, hb, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
        ← Real.rpow_add hX0]
      congr 1; push_cast [Nat.cast_sub hk2]; ring
    have hS0 : 0 ≤ S0 := tsum_nonneg fun _ => by positivity
    have h2e : (2 * Real.exp b) ^ k ≤ (2 * Real.exp 1) ^ k :=
      pow_le_pow_left₀ (by positivity) (by gcongr) k
    have hXe : X ≤ X ^ (2 * (θ' - 1) + ε * ((k : ℝ) - 2)) := by
      conv_lhs => rw [← Real.rpow_one X]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    rw [← hk, hpow]
    calc 64 * S0 * (2 * Real.exp b) ^ k ≤ 64 * S0 * (2 * Real.exp 1) ^ k := by gcongr
      _ ≤ X := hX64
      _ ≤ _ := hXe
  -- `hwin`
  have hwin : Real.exp (3 * (2 ^ (J + 1) * b)) - 1 ≤ (2 * X) ^ (θ - 1) := by
    have h3D : |3 * (2 ^ (J + 1) * b)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]; linarith
    have he := (abs_le.1 (Real.abs_exp_sub_one_le h3D)).2
    rw [abs_of_nonneg (by positivity)] at he
    have h2 : (2 : ℝ) ^ (θ - 1) ≥ 1 / 2 := by
      calc (2 : ℝ) ^ (θ - 1) ≥ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    have hXθ : X ^ (θ - 1) = X ^ (θ - θ') * b := by
      rw [hb, ← Real.rpow_add hX0]; congr 1; ring
    have hmain : 12 * 2 ^ (J + 1) * b ≤ X ^ (θ - 1) := by
      rw [hXθ]; exact mul_le_mul_of_nonneg_right h5 hb0.le
    rw [Real.mul_rpow (by norm_num) hX0.le]
    have hXθ0 : 0 ≤ X ^ (θ - 1) := Real.rpow_nonneg hX0.le _
    have h4 := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (θ - 1) from h2) hXθ0
    linarith
  -- the measure at scale `X`
  have hbad := bad_measure_le hb0 hJ1 (by linarith : 1 ≤ T) hD hX2 hθ1 hW hA' hTl hwin
  set L₀ := Real.log X - 2 with hL₀
  have hL₀0 : 0 ≤ L₀ := by rw [hL₀]; linarith
  have heL : Real.exp (L₀ + 2 * π) = X * Real.exp (2 * π - 2) := by
    rw [hL₀, show Real.log X - 2 + 2 * π = Real.log X + (2 * π - 2) by ring, Real.exp_add, Real.exp_log hX0]
  have hpi := Real.pi_gt_three
  have he2 : X ^ 2 ≤ Real.exp (2 * (L₀ + 2 * π)) := by
    rw [show 2 * (L₀ + 2 * π) = (L₀ + 2 * π) + (L₀ + 2 * π) by ring, Real.exp_add, heL]
    have hc : 1 ≤ Real.exp (2 * π - 2) := Real.one_le_exp (by linarith)
    have hcc : 1 ≤ Real.exp (2 * π - 2) * Real.exp (2 * π - 2) := one_le_mul_of_one_le_of_one_le hc hc
    calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
      _ ≤ X ^ 2 * (Real.exp (2 * π - 2) * Real.exp (2 * π - 2)) := mul_le_mul_of_nonneg_left hcc (sq_nonneg X)
      _ = X * Real.exp (2 * π - 2) * (X * Real.exp (2 * π - 2)) := by ring
  have hTA : T ^ A ≤ X ^ (2 - κ / 2) := by
    rw [hT, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by rw [mul_comm]; exact hAexp)
  have hX2' : X ^ (2 - κ / 2) ≤ X ^ 2 := by
    rw [show (X ^ 2 : ℝ) = X ^ (2 : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hQ : T ^ A ≤ Real.exp (2 * (L₀ + 2 * π)) := hTA.trans (hX2'.trans he2)
  have hden : ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 → (NX w T : ℝ) ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B :=
    fun w hw0 hw1 => hCd T (by linarith) w hw0 hw1
  have hI := head_integral_le (J := J) hb0 hL₀0 (by linarith : 2 ≤ T) hM1 hC hden hQ
  refine hbad.trans (ENNReal.ofReal_le_ofReal ?_)
  set m₀ := (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1)) with hm₀
  have hm0 : 0 < m₀ := by positivity
  refine (mul_le_mul_of_nonneg_left hI (by positivity)).trans ?_
  -- the pieces
  set G := (4 * b * Real.exp (b / 2)) ^ (2 * 2 ^ (J + 1)) with hG
  have hGm : G / m₀ ^ 2 ≤ (2 * Real.exp 1) ^ (2 * k) := by
    have e : G = (2 * Real.exp b) ^ (2 * k) * m₀ ^ 2 := by
      have hbase : 4 * b * Real.exp (b / 2) = 2 * Real.exp b * (2 * b * Real.exp (-(b / 2))) := by
        have : Real.exp b * Real.exp (-(b / 2)) = Real.exp (b / 2) := by rw [← Real.exp_add]; ring_nf
        linear_combination (-(4 * b)) * this
      rw [hG, hm₀, hbase, mul_pow, ← pow_mul, hk]
      ring
    rw [e, mul_div_assoc, div_self (by positivity), mul_one]
    exact pow_le_pow_left₀ (by positivity) (by gcongr) _
  have hC0 : 5 + kLam + Real.log (T + 2) / 2 ≤ 3 * Real.log X := by
    have hT2 : T + 2 ≤ X ^ 2 := by
      have hTX : T ≤ X ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      have h32 : X ^ (3 / 2 : ℝ) + 2 ≤ X ^ (2 : ℝ) := by
        have e : X ^ (2 : ℝ) = X ^ (3 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
        have h1 : 2 ≤ X ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow, show (2 : ℝ) = Real.sqrt 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by linarith)
        have h2 : 2 ≤ X ^ (3 / 2 : ℝ) := by
          calc (2 : ℝ) ≤ X ^ (1 / 2 : ℝ) := h1
            _ ≤ X ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
        rw [e]; nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ X ^ (3 / 2 : ℝ))]
      rw [show (X ^ 2 : ℝ) = X ^ (2 : ℝ) by norm_cast]; linarith
    have hl : Real.log (T + 2) ≤ 2 * Real.log X := by
      calc Real.log (T + 2) ≤ Real.log (X ^ 2) := Real.log_le_log (by linarith) hT2
        _ = 2 * Real.log X := by rw [Real.log_pow]; norm_num
    linarith
  have hlogT : Real.log T ^ B ≤ 2 ^ |B| * Real.log X ^ |B| := by
    have hlT : Real.log T = (1 - θ' + ε) * Real.log X := by rw [hT, Real.log_rpow hX0]
    have hlT1 : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hlT2 : Real.log T ≤ 2 * Real.log X := by
      rw [hlT]; have : 0 ≤ Real.log X := by linarith
      nlinarith
    calc Real.log T ^ B ≤ Real.log T ^ |B| := Real.rpow_le_rpow_of_exponent_le hlT1 (le_abs_self B)
      _ ≤ (2 * Real.log X) ^ |B| := Real.rpow_le_rpow (by linarith) hlT2 (abs_nonneg B)
      _ = 2 ^ |B| * Real.log X ^ |B| := Real.mul_rpow (by norm_num) (by linarith)
  have hpowM : Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) ≤ X ^ (1 / (M : ℝ)) * Real.exp (2 * π) := by
    have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hM0 : (0 : ℝ) < M := by linarith
    have e1 : Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) = Real.exp ((L₀ + 2 * π) / M) := by
      rw [← Real.exp_mul]; congr 1; field_simp
    have e2 : X ^ (1 / (M : ℝ)) = Real.exp (Real.log X / M) := by
      rw [Real.rpow_def_of_pos hX0]; congr 1; ring
    rw [e1, e2, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (2 * π - 2) / M ≤ 2 * π := by
      rw [div_le_iff₀ hM0]; nlinarith [Real.pi_gt_three]
    have h2 : (L₀ + 2 * π) / M = Real.log X / M + (2 * π - 2) / M := by rw [hL₀]; ring
    linarith
  have hQ12 : (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ) ≤ X ^ (-(κ / 24)) := by
    have h1 : T ^ A / Real.exp (2 * (L₀ + 2 * π)) ≤ X ^ (-(κ / 2)) := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      calc T ^ A ≤ X ^ (2 - κ / 2) := hTA
        _ = X ^ (-(κ / 2)) * X ^ (2 : ℝ) := by rw [← Real.rpow_add hX0]; ring_nf
        _ ≤ X ^ (-(κ / 2)) * Real.exp (2 * (L₀ + 2 * π)) := by
            gcongr; rw [show (X ^ (2 : ℝ)) = X ^ 2 by norm_cast]; exact he2
    have h0 : 0 ≤ T ^ A / Real.exp (2 * (L₀ + 2 * π)) := by positivity
    calc (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ) ≤ (X ^ (-(κ / 2))) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow h0 h1 (by norm_num)
      _ = X ^ (-(κ / 24)) := by rw [← Real.rpow_mul hX0.le]; ring_nf
  -- assemble
  have hkLam := Kaiser.kLam_nonneg
  have hlX0 : 0 ≤ Real.log X := by linarith
  have hlXB : 0 ≤ Real.log X ^ |B| := Real.rpow_nonneg hlX0 _
  have hpieces : 32 / m₀ ^ 2 * (180 * π * (5 + kLam + Real.log (T + 2) / 2) * G
        * (Real.exp (L₀ + 2 * π) * (M * Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) * (C * Real.log T ^ B)
          * (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ))))
      ≤ K * 3 * 2 ^ |B| * (Real.log X * Real.log X ^ |B|) * (X * X ^ (1 / (M : ℝ)) * X ^ (-(κ / 24))) := by
    have hG0 : 0 ≤ G / m₀ ^ 2 := by positivity
    have e : 32 / m₀ ^ 2 * (180 * π * (5 + kLam + Real.log (T + 2) / 2) * G
        * (Real.exp (L₀ + 2 * π) * (M * Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) * (C * Real.log T ^ B)
          * (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ))))
        = 32 * (180 * π) * (G / m₀ ^ 2) * (5 + kLam + Real.log (T + 2) / 2) * Real.exp (L₀ + 2 * π) * M
          * Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) * C * Real.log T ^ B
          * (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ) := by
      field_simp
    rw [e, heL, hK]
    have hc5 : 0 ≤ 5 + kLam + Real.log (T + 2) / 2 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); positivity
    have hlT0 : 0 ≤ Real.log T ^ B := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hQ0 : 0 ≤ (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ) := by positivity
    have hpM0 : 0 ≤ Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) := by positivity
    calc 32 * (180 * π) * (G / m₀ ^ 2) * (5 + kLam + Real.log (T + 2) / 2) * (X * Real.exp (2 * π - 2)) * M
          * Real.exp (2 * (L₀ + 2 * π)) ^ (1 / (2 * M : ℝ)) * C * Real.log T ^ B
          * (T ^ A / Real.exp (2 * (L₀ + 2 * π))) ^ (1 / 12 : ℝ)
        ≤ 32 * (180 * π) * (2 * Real.exp 1) ^ (2 * k) * (3 * Real.log X) * (X * Real.exp (2 * π - 2)) * M
          * (X ^ (1 / (M : ℝ)) * Real.exp (2 * π)) * C * (2 ^ |B| * Real.log X ^ |B|) * X ^ (-(κ / 24)) := by
          gcongr
      _ = _ := by ring
  refine hpieces.trans ?_
  -- the final exponent
  have hexp : X * X ^ (1 / (M : ℝ)) * X ^ (-(κ / 24)) ≤ X ^ (1 - κ / 48) := by
    have e : X * X ^ (1 / (M : ℝ)) * X ^ (-(κ / 24)) = X ^ (1 + 1 / (M : ℝ) + -(κ / 24)) := by
      rw [Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hlog : Real.log X * Real.log X ^ |B| = Real.log X ^ (|B| + 1) := by
    rw [Real.rpow_add_one' hlX0 (by positivity), mul_comm]
  have hfin : K * 3 * 2 ^ |B| * Real.log X ^ (|B| + 1) ≤ X ^ s₂ := by
    have hden0 : 0 < 3 * K * 2 ^ |B| + 1 := by positivity
    have h := h7
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hden0] at h
    have hl0 : 0 ≤ Real.log X ^ (|B| + 1) := Real.rpow_nonneg hlX0 _
    have e : Real.log X ^ (|B| + 1) * (3 * K * 2 ^ |B| + 1)
        = K * 3 * 2 ^ |B| * Real.log X ^ (|B| + 1) + Real.log X ^ (|B| + 1) := by ring
    linarith
  rw [hlog]
  calc K * 3 * 2 ^ |B| * Real.log X ^ (|B| + 1) * (X * X ^ (1 / (M : ℝ)) * X ^ (-(κ / 24)))
      ≤ X ^ s₂ * X ^ (1 - κ / 48) := by
        gcongr
      _ = X ^ (1 - δ) := by rw [← Real.rpow_add hX0, hs₂, hδ]; ring_nf

/-- **Primes in almost all short intervals for every `θ > 1/6`** (Huxley): from `ZetaHuxley.densityXi_twelve_fifths`,
`1 − 2/(12/5) = 1/6`. -/
theorem almost_all_short_primes {θ : ℝ} (hθ : 1 / 6 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      volume {y | y ∈ Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
        ≤ ENNReal.ofReal (X ^ (1 - δ)) := by
  set θ₁ := min θ 1 with hθ₁
  have hθ₁0 : 0 < θ₁ := lt_min (by linarith) one_pos
  have hθ₁6 : 1 - 2 / (12 / 5 : ℝ) < θ₁ := lt_min (by norm_num; linarith) (by norm_num)
  obtain ⟨δ, hδ, h⟩ := almost_all_of_density (A₀ := 12 / 5) (by norm_num)
    (fun ε hε => ⟨12, ZetaHuxley.densityXi_twelve_fifths hε⟩) hθ₁0 (min_le_right _ _) hθ₁6
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  refine le_trans (measure_mono ?_) hX
  rintro y ⟨hy, hno⟩
  refine ⟨hy, fun ⟨p, hp, h1, h2⟩ => hno ⟨p, hp, h1, h2.trans ?_⟩⟩
  have hy1 : 1 ≤ y := le_trans hX1 hy.1
  have := Real.rpow_le_rpow_of_exponent_le hy1 (min_le_left θ 1)
  linarith

end AlmostAll

#print axioms AlmostAll.norm_tail_le
#print axioms AlmostAll.prime_of_head_small
#print axioms AlmostAll.bad_measure_le
#print axioms AlmostAll.head_integral_le
#print axioms AlmostAll.almost_all_of_density
#print axioms AlmostAll.almost_all_short_primes
