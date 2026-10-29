/-
# The density exponent `12/5` for `ζ` on `3/4 ≤ σ ≤ 11/12`, and primes in short intervals for `θ > 7/12`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `ε > 0`, `N(σ, T) ≪ T^{(12/5 + ε)(1−σ)}(log T)^{12}` for `1/2 ≤ σ ≤ 1` and `T ≥ 2`
(`densityXi_twelve_fifths`), and for every `θ > 7/12` every interval `(y, y + y^θ]` with `y` large holds a prime
(`short_primes_seven_twelfths`). On `3/4 ≤ σ ≤ 11/12` the exponent `12/5` is Huxley's (`nx_huxley`), but the proof
is not his large-values estimate: the detector of `InghamDensity` at `X = ⌊U^{1/25}⌋`, `Y = U^{3/5}`, with a power of
each dyadic block of its polynomial counted by the Halász–Montgomery inequality at well-spaced heights
(`ZetaKernel.power_count_pts`) in subintervals of height `T₀ = U^{(12σ−7)/5−8ε}Λ^{2−2σ}`, and the integral piece
counted with `|M_X| ≤ X` and the fourth moment of `ζ`. The off-diagonal terms need `|ζ(1/12 + it)| ≪ |t|^{5/12+ε}`
(`ZetaKernel.norm_kz_le`), which comes from the zero-free half-plane (`Subconvexity.zeta_strip_eleven_twelfths`). On
`7/12 ≤ σ ≤ 3/4` the count is Ingham's (`ZetaIngham.nx_ingham`); below `7/12` it is the trivial count, and above
`11/12` there is no zero (`Eis.ne_zero_of_re_gt_eleven_twelfths`).

* `tail_le7`, `trichotomy7`: `InghamDensity.tail_le` and `InghamDensity.trichotomy` with `36864U ≤ Y⁷` in place of
  `U ≤ Y`, which admits `Y = U^{3/5}` (the tail is at most `2304UY⁴/Y^{11}`).
* `class3_count_small`: the integral class, as `LinnikHuxley.class2_count_small` over the zeros: `|M_X| ≤ X` on the
  line, `l ≤ l⁴/(4λ³) + 3λ/4` at `λ = 1/(3AX)` and `ZetaFourth.zeta_fourth_moment` at the points `γ + v`.
* `feas_zeta`, `count_bound_zeta`: for a block of length `P` with `(2P)^m = Λ ∈ [U^{4/5}, U^{6/5+ε}]`, `m ≤ 22`, the
  kernel bound at height `T₀` makes `2e·G_m(KE + B) ≤ (4K)^{−2m}` (the `U`-exponent of `G_mΛ^{1/12}T₀^{5/12+ε}` is
  at most `(57 − 76σ)/60 − (23/15)ε`), and the `⌊4U/T₀⌋ + 1` subintervals carry
  `10e(4C⁴)^{22}U^{(12/5)(1−σ)+12ε}` (the first term is `4U^{(12/5)(1−σ)+8ε}Λ^ε`).
* `class_poly_huxley`: some dyadic block of `P_b(ρ)` is at least `1/(4K)`; bins of width `1/48` in `β`; in each block
  a power `m` with `(2P)^m ≥ U^{4/5}` (`LinnikHuxley.choose_m`); subintervals of height `T₀`; `power_count_pts`.
* `window_classes_huxley`, `window_count_huxley`: the three classes in a window `U ≤ |γ| ≤ 2U`, at
  `X = ⌊U^{1/25}⌋`, `Y = U^{3/5}`, `N = ⌊22Y log Y/X⌋ + 1` for all large `U` (`eventually_zeta`).
* `nx_huxley`: `ZetaIngham.nx_le_of_windows`; `(12/5)(1 − σ) + 13ε ≤ (12/5 + 156ε)(1 − σ)` for `σ ≤ 11/12`.
* `short_primes_of_density_eps_hp`: `InghamDensity.short_primes_of_density_eps` with the zero-free region of the
  half-plane (`ShortPrimesHalfPlane.zeroFreeXi_of_halfplane`) in place of Korobov–Vinogradov's, so that
  `short_primes_seven_twelfths` has the half-plane as its only analytic input beyond PNT+ and Mathlib.
-/
import ZetaKernel
import ZetaIngham
import ShortPrimesHalfPlane

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace ZetaHuxley

open ShortWeil PsiOmega WeilForm WeilTest DirMean Finset InghamDensity ZetaIngham ZetaFourth ZetaKernel LinnikPower
  LinnikHuxley

/-! ### The detector with `Y < U` -/

/-- **The tail of the detector** with `36864U ≤ Y⁷` (`InghamDensity.tail_le`, whose last step used `U ≤ Y`). -/
theorem tail_le7 (X : ℕ) {Y U : ℝ} (hY : 8 ≤ Y) (hU : 2 ≤ U) (hUY : 36864 * U ≤ Y ^ 7) {ρ : ℂ} (hρ : 0 ≤ ρ.re)
    (hρ1 : ‖ρ - 1‖ ≤ 2 * U + 1) {M : ℕ} (hM : 22 * Y * Real.log Y ≤ M) :
    ‖∑' n : ℕ, if M < n then cn X Y ρ n else 0‖ ≤ 1 / 16 := by
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  -- `e^{−M/(2Y)} ≤ Y^{−11}`
  have hexp : Real.exp ((M : ℝ) / (2 * Y)) ≥ Y ^ 11 := by
    have h1 : 11 * Real.log Y ≤ (M : ℝ) / (2 * Y) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc Y ^ 11 = Real.exp (((11 : ℕ) : ℝ) * Real.log Y) := by
          rw [Real.exp_nat_mul, Real.exp_log hY0]
      _ ≤ Real.exp ((M : ℝ) / (2 * Y)) := Real.exp_le_exp.2 (by push_cast; linarith)
  set K : ℝ := 1152 * U * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ n : ℕ, ‖if M < n then cn X Y ρ n else 0‖ ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n
    split_ifs with hn
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn.le
      refine (norm_cn_le X hY0 hρ n).trans ?_
      -- `n(n/Y + |ρ − 1|) ≤ 3U n²`
      have hA : (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) ≤ 3 * U * (n : ℝ) ^ 2 := by
        have h1 : (n : ℝ) / Y ≤ n := div_le_self hn0.le (by linarith)
        have h2 : (n : ℝ) / Y + ‖ρ - 1‖ ≤ n + (2 * U + 1) := by linarith
        have h3 : (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) ≤ n * (n + (2 * U + 1)) :=
          mul_le_mul_of_nonneg_left h2 hn0.le
        have h4 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have h5 : (2 * U + 1) * (n : ℝ) ≤ (2 * U + 1) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        have h6 : (2 * U + 2) * (n : ℝ) ^ 2 ≤ 3 * U * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith
      -- `n² e^{−n/Y} ≤ 384 Y⁴ e^{−M/(2Y)} / n²`
      have hB : (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
          ≤ 384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) := by
        have hy : 0 ≤ (n : ℝ) / (2 * Y) := by positivity
        have h4 := pow_mul_exp_neg_le 4 hy
        have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
        rw [hf] at h4
        have hsplit : Real.exp (-((n : ℝ) / Y))
            = Real.exp (-((n : ℝ) / (2 * Y))) * Real.exp (-((n : ℝ) / (2 * Y))) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        have hmono : Real.exp (-((n : ℝ) / (2 * Y))) ≤ Real.exp (-((M : ℝ) / (2 * Y))) :=
          Real.exp_le_exp.2 (by
            have : (M : ℝ) / (2 * Y) ≤ (n : ℝ) / (2 * Y) := by gcongr
            linarith)
        have e4 : (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = 16 * Y ^ 4 * ((n : ℝ) / (2 * Y)) ^ 4 := by
          field_simp; ring
        calc (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
            = 16 * Y ^ 4 * (((n : ℝ) / (2 * Y)) ^ 4 * Real.exp (-((n : ℝ) / (2 * Y))))
              * Real.exp (-((n : ℝ) / (2 * Y))) := by rw [hsplit]; nlinarith [e4]
          _ ≤ 16 * Y ^ 4 * 24 * Real.exp (-((M : ℝ) / (2 * Y))) := by gcongr
          _ = 384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y))) := by ring
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      rw [mul_one_div, le_div_iff₀ hn2]
      calc (n : ℝ) * ((n : ℝ) / Y + ‖ρ - 1‖) * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
          ≤ 3 * U * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2 := by gcongr
        _ = 3 * U * ((n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2) := by ring
        _ ≤ 3 * U * (384 * Y ^ 4 * Real.exp (-((M : ℝ) / (2 * Y)))) := by gcongr
        _ = K := by rw [hK]; ring
    · rw [norm_zero]; positivity
  have hsum : HasSum (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) (K * (π ^ 2 / 6)) :=
    hasSum_zeta_two.mul_left K
  refine (tsum_of_norm_bounded hsum hpt).trans ?_
  -- `K π²/6 ≤ 2K ≤ 2304 U Y⁴ Y^{−11} ≤ 2304 / Y⁶ ≤ 1/16`
  have hpi : π ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  have hY11 : 0 < Y ^ 11 := by positivity
  have hKle : K ≤ 1152 * U * Y ^ 4 / Y ^ 11 := by
    rw [hK, Real.exp_neg, ← div_eq_mul_inv]
    gcongr
  have hfin : 2 * (1152 * U * Y ^ 4 / Y ^ 11) ≤ 1 / 16 := by
    rw [mul_div_assoc', div_le_div_iff₀ hY11 (by norm_num)]
    have e : Y ^ 11 = Y ^ 7 * Y ^ 4 := by ring
    rw [e]
    have hY4 : 0 ≤ Y ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hUY hY4]
  calc K * (π ^ 2 / 6) ≤ K * 2 := by gcongr
    _ = 2 * K := by ring
    _ ≤ 2 * (1152 * U * Y ^ 4 / Y ^ 11) := by gcongr
    _ ≤ 1 / 16 := hfin

/-- **The trichotomy at a zero** (`InghamDensity.trichotomy` with `36864U ≤ Y⁷` in place of `U ≤ Y`): for a zero
`ρ = β + iγ` of `ζ` with `½ < β < 1` and `U ≤ |γ| ≤ 2U`, `|P₁(ρ)| ≥ ¼`, `|P₂(ρ)| ≥ ¼` or `|I(ρ)| ≥ U/4`. -/
theorem trichotomy7 {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) {Y U : ℝ} (hY : 8 ≤ Y) (hU : 2 ≤ U)
    (hUY : 36864 * U ≤ Y ^ 7)
    (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ)) {β γ : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (hγ1 : U ≤ |γ|) (hγ2 : |γ| ≤ 2 * U) (hz : riemannZeta ((β : ℂ) + γ * I) = 0) :
    1 / 4 ≤ ‖Pv (b1 X Y) X N β γ‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N β γ‖ ∨ U / 4 ≤ ‖Iv X Y ((β : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (β : ℂ) + γ * I with hρdef
  have hY0 : 0 < Y := by linarith
  have hρre : ρ.re = β := by simp [hρdef]
  have hρim : ρ.im = γ := by simp [hρdef]
  have hXM : X ≤ X * N := Nat.le_mul_of_pos_right X hN
  have hid := detect_identity X (Y := Y) (by linarith) hz (by rw [hρre]; exact hβ1) (by rw [hρre]; exact hβ2)
  have hsplit := tsum_cn_split hX hXM hY0 (ρ := ρ) (by rw [hρre]; linarith)
  have hsum := sum_cn_eq X N Y β γ
  rw [← hρdef] at hsum
  -- `c₁ + P₂ + (ρ − 1)P₁ + T = I`
  set T := ∑' n : ℕ, if X * N < n then cn X Y ρ n else 0 with hT
  set P1 := Pv (b1 X Y) X N β γ
  set P2 := Pv (b2 X Y) X N β γ
  set II := Iv X Y ρ with hII
  have heq : cn X Y ρ 1 + (P2 + (ρ - 1) * P1) + T = II := by
    rw [← hsum, ← hsplit]; exact hid
  have hR1 : |γ| ≤ ‖ρ - 1‖ := by
    have := Complex.abs_im_le_norm (ρ - 1)
    simpa [hρim] using this
  have hR2 : ‖ρ - 1‖ ≤ 2 * U + 1 := by
    calc ‖ρ - 1‖ ≤ |(ρ - 1).re| + |(ρ - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |β - 1| + |γ| := by simp [hρre, hρim]
      _ ≤ 2 * U + 1 := by rw [abs_of_neg (by linarith)]; linarith
  have hT16 : ‖T‖ ≤ 1 / 16 := tail_le7 X hY hU hUY (by rw [hρre]; linarith) hR2 hM
  set R := ‖ρ - 1‖ with hRdef
  have hRU : U ≤ R := hγ1.trans hR1
  -- `|c₁| ≥ (105/128) R`
  have hc1 : (105 / 128) * R ≤ ‖cn X Y ρ 1‖ := by
    rw [cn_one hX, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : R - 1 / Y ≤ ‖(((1 / Y : ℝ) : ℂ) + (ρ - 1))‖ := by
      have := norm_sub_norm_le (ρ - 1) (-(((1 / Y : ℝ) : ℂ)))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), sub_neg_eq_add,
        add_comm] at this
      linarith
    have h2 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / Y)) := by
      have := Real.add_one_le_exp (-(1 / Y))
      have : 1 / Y ≤ 1 / 8 := by gcongr
      linarith
    have h3 : (15 / 16) * R ≤ R - 1 / Y := by
      have : 1 / Y ≤ 1 / 8 := by gcongr
      linarith
    calc (105 / 128) * R = ((15 / 16) * R) * (7 / 8) := by ring
      _ ≤ ‖(((1 / Y : ℝ) : ℂ) + (ρ - 1))‖ * Real.exp (-(1 / Y)) := by
          gcongr
          linarith
  -- `|c₁| ≤ |P₂| + R|P₁| + |T| + |I|`
  have hle : ‖cn X Y ρ 1‖ ≤ ‖P2‖ + R * ‖P1‖ + ‖T‖ + ‖II‖ := by
    have e : cn X Y ρ 1 = II - P2 - (ρ - 1) * P1 - T := by rw [← heq]; ring
    rw [e]
    calc ‖II - P2 - (ρ - 1) * P1 - T‖ ≤ ‖II‖ + ‖P2‖ + ‖(ρ - 1) * P1‖ + ‖T‖ := by
          refine (norm_sub_le _ _).trans ?_
          have h1 := norm_sub_le (II - P2) ((ρ - 1) * P1)
          have h2 := norm_sub_le II P2
          linarith
      _ = ‖P2‖ + R * ‖P1‖ + ‖T‖ + ‖II‖ := by rw [norm_mul]; ring
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hP1R : R * ‖P1‖ ≤ R * (1 / 4) := mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
  nlinarith

/-! ### The integral class with a short mollifier -/

/-- **The integral class with a short mollifier.** A parity class of window representatives whose zeros have
`|I(ρ)| ≥ U/4` has at most `27A⁴X⁴M₂` members, `A = 3KG Y^{½−σ}/δ`, `M₂ = C₄(2U + 2)^{1+ε}`: `|M_X| ≤ X` on the line,
`l ≤ l⁴/(4λ³) + 3λ/4` at `λ = 1/(3AX)` (`LinnikHuxley.le_quartic`) and the fourth moment at the points `γ + v`. -/
theorem class3_count_small {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ U Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hU : 2 ≤ U) (hY : 1 ≤ Y)
    (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hdet : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧
      (σ ≤ βs (rep n) ∧ U / 4 ≤ ‖Iv X Y ((βs (rep n) : ℂ) + γs (rep n) * I)‖)) :
    (C.card : ℝ) ≤ 27 * (3 * KG * Y ^ (1 / 2 - σ) / δ) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε)) := by
  classical
  obtain ⟨CP, hCP0, hCP⟩ := zeta_half_poly
  set A := 3 * KG * Y ^ (1 / 2 - σ) / δ with hA
  have hKG := KG_pos
  have hA0 : 0 < A := by
    have : 0 < Y := by linarith
    positivity
  have hU0 : 0 < U := by linarith
  set M₂ := C₄ * (2 * U + 2) ^ (1 + ε) with hM₂
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  set lam := 1 / (3 * A * X) with hlam
  have hlam0 : 0 < lam := by positivity
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  set m : ℕ → ℝ → ℝ := fun n v => ‖moll X (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ with hm
  set l : ℕ → ℝ → ℝ := fun n v => ‖riemannZeta (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ with hl
  have hmc : ∀ n, Continuous (m n) := fun n => continuous_moll_line X (γs (rep n))
  have hlc : ∀ n, Continuous (l n) := by
    intro n
    refine Continuous.norm (continuous_iff_continuousAt.2 fun v => ?_)
    have hne : (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    exact ContinuousAt.comp (g := riemannZeta) (f := fun v : ℝ => 1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  have hmX : ∀ n v, m n v ≤ X := fun n v => norm_moll_le_X X (by simp)
  have hm0 : ∀ n v, 0 ≤ m n v := fun n v => norm_nonneg _
  have hl0 : ∀ n v, 0 ≤ l n v := fun n v => norm_nonneg _
  have hγU : ∀ n ∈ C, |γs (rep n)| ≤ 2 * U := fun n hn => by rw [abs_γs]; exact (hdet n hn).1
  -- `l` grows at most quadratically
  have hlb : ∀ n ∈ C, ∀ v, l n v ≤ CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2 := by
    intro n hn v
    have h := hCP (γs (rep n) + v)
    have hb : 1 + |γs (rep n) + v| ≤ (1 + 2 * U) * (1 + |v|) := by
      have := abs_add_le (γs (rep n)) v
      nlinarith [abs_nonneg (γs (rep n)), abs_nonneg v, hγU n hn]
    calc l n v ≤ CP * (1 + |γs (rep n) + v|) ^ 2 := h
      _ ≤ CP * ((1 + 2 * U) * (1 + |v|)) ^ 2 := by gcongr
      _ = CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2 := by ring
  have hint : ∀ n ∈ C, Integrable fun v => m n v * l n v * wt4 v := by
    intro n hn
    refine integrable_real_of_le (((hmc n).mul (hlc n)).mul continuous_wt4)
      (K := X * (CP * (1 + 2 * U) ^ 2)) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hm0 n v) (hl0 n v)) (wt4_pos v).le)]
    have hw := (wt4_pos v).le
    calc m n v * l n v * wt4 v ≤ X * (CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2) * wt4 v := by
          gcongr
          · exact hmX n v
          · exact hlb n hn v
      _ = X * (CP * (1 + 2 * U) ^ 2) * (wt4 v * (1 + |v|) ^ 2) := by ring
      _ ≤ X * (CP * (1 + 2 * U) ^ 2) * (1 + v ^ 2)⁻¹ := by
          have : 0 ≤ (X : ℝ) * (CP * (1 + 2 * U) ^ 2) := by positivity
          exact mul_le_mul_of_nonneg_left (wt4_mul_sq_le v) this
  -- (i) each zero
  have hIv : ∀ n ∈ C, 1 / 4 ≤ A / (2 * π) * ∫ v, m n v * l n v * wt4 v := by
    intro n hn
    obtain ⟨hre, hσβ, hI⟩ := hdet n hn
    have hβ1 : βs (rep n) < 1 := βs_lt_one (rep n)
    have hρ1 : ((βs (rep n) : ℂ) + γs (rep n) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hz : Zr ((βs (rep n) : ℂ) + γs (rep n) * I) = 0 :=
      Zr_zero_of_zeta (DetectCore.zeta_βsγs (rep n)) hρ1
    unfold Iv at hI
    rw [norm_mul] at hI
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2] at hI
    set B := KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ with hB
    have hle : ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
        (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, B * (m n v * l n v * wt4 v) := by
      refine norm_integral_le_of_norm_le ((hint n hn).const_mul B) (Eventually.of_forall fun v => ?_)
      have h := Gfun_left_le_zeta X hδ hσδ hσβ hβ1 hU0.le (hγU n hn) hY hz v
      have hp : 0 < (1 + |v|) ^ 4 := by positivity
      have e : B * (m n v * l n v * wt4 v) = B * (m n v * l n v) / (1 + |v|) ^ 4 := by
        unfold wt4; ring
      rw [e, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    have hBA : B ≤ U * A := by
      rw [hB, hA]
      have hY0 : 0 ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg (by linarith) _
      have h3 : 1 + 2 * U ≤ 3 * U := by linarith
      calc KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ ≤ KG * (3 * U) * Y ^ (1 / 2 - σ) / δ := by gcongr
        _ = U * (3 * KG * Y ^ (1 / 2 - σ) / δ) := by ring
    have hI0 : 0 ≤ ∫ v, m n v * l n v * wt4 v :=
      integral_nonneg fun v => mul_nonneg (mul_nonneg (hm0 n v) (hl0 n v)) (wt4_pos v).le
    have hmain : U / 4 ≤ U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by
      calc U / 4 ≤ 1 / (2 * π) * ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
            (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖ := hI
        _ ≤ 1 / (2 * π) * (B * ∫ v, m n v * l n v * wt4 v) := by gcongr
        _ ≤ 1 / (2 * π) * ((U * A) * ∫ v, m n v * l n v * wt4 v) := by gcongr
        _ = U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by ring
    have h4' : U * (1 / 4) ≤ U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by linarith
    exact le_of_mul_le_mul_left h4' hU0
  -- (ii) the sum over the class
  have hsum1 : (C.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v := by
    rw [integral_finsetSum C fun n hn => hint n hn, mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hIv
  -- (iii) pointwise
  have hsep := sep_of_windows C rep hC hwin
  set K' := X * (M₂ / (4 * lam ^ 3)) + X * ((C.card : ℝ) * (3 * lam / 4)) with hK'
  have hpt : ∀ v : ℝ, ∑ n ∈ C, m n v * l n v * wt4 v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ n, m n v * l n v ≤ X * (l n v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) := by
      intro n
      calc m n v * l n v ≤ X * l n v := mul_le_mul_of_nonneg_right (hmX n v) (hl0 n v)
        _ ≤ X * (l n v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) :=
            mul_le_mul_of_nonneg_left (le_quartic (hl0 n v) hlam0) hX0.le
    have hsepv : ∀ n ∈ C, ∀ k ∈ C, n ≠ k → 1 ≤ |γs (rep n) + v - (γs (rep k) + v)| := by
      intro n hn k hk hnk
      rw [show γs (rep n) + v - (γs (rep k) + v) = γs (rep n) - γs (rep k) by ring]
      exact hsep n hn k hk hnk
    have h4v := h4 C (fun n => γs (rep n) + v) hsepv (2 * U + |v|) (by positivity)
      (fun n hn => by
        have h1 := abs_add_le (γs (rep n)) v
        have h2 := hγU n hn
        linarith)
    have hS4 : ∑ n ∈ C, l n v ^ 4 ≤ M₂ * (1 + |v|) ^ 2 := by
      have hb : 2 * U + |v| + 2 ≤ (2 * U + 2) * (1 + |v|) := by nlinarith [abs_nonneg v]
      have hv1 : (1 : ℝ) ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hp1 : (2 * U + |v| + 2) ^ (1 + ε) ≤ (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2 := by
        calc (2 * U + |v| + 2) ^ (1 + ε) ≤ ((2 * U + 2) * (1 + |v|)) ^ (1 + ε) :=
              Real.rpow_le_rpow (by positivity) hb (by linarith)
          _ = (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ (1 + ε) := Real.mul_rpow (by positivity) (by positivity)
          _ ≤ (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ (2 : ℝ) := by
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith))
                (by positivity)
          _ = (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc ∑ n ∈ C, l n v ^ 4 ≤ C₄ * (2 * U + |v| + 2) ^ (1 + ε) := h4v
        _ ≤ C₄ * ((2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2) := by gcongr
        _ = M₂ * (1 + |v|) ^ 2 := by rw [hM₂]; ring
    have hw0 := (wt4_pos v).le
    have hw2 := wt4_mul_sq_le v
    have hw := wt4_le v
    have hc4 : 0 ≤ (X : ℝ) * (M₂ / (4 * lam ^ 3)) := by positivity
    have hc3 : 0 ≤ (X : ℝ) * ((C.card : ℝ) * (3 * lam / 4)) := by positivity
    calc ∑ n ∈ C, m n v * l n v * wt4 v = wt4 v * ∑ n ∈ C, m n v * l n v := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
      _ ≤ wt4 v * ∑ n ∈ C, X * (l n v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun n _ => hamgm n) hw0
      _ = wt4 v * (X * ((∑ n ∈ C, l n v ^ 4) / (4 * lam ^ 3)) + X * ((C.card : ℝ) * (3 * lam / 4))) := by
          rw [← mul_sum, sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul]; ring
      _ ≤ wt4 v * (X * ((M₂ * (1 + |v|) ^ 2) / (4 * lam ^ 3)) + X * ((C.card : ℝ) * (3 * lam / 4))) := by
          gcongr
      _ = X * (M₂ / (4 * lam ^ 3)) * (wt4 v * (1 + |v|) ^ 2) + X * ((C.card : ℝ) * (3 * lam / 4)) * wt4 v := by
          ring
      _ ≤ X * (M₂ / (4 * lam ^ 3)) * (1 + v ^ 2)⁻¹ + X * ((C.card : ℝ) * (3 * lam / 4)) * (1 + v ^ 2)⁻¹ := by
          gcongr
      _ = K' * (1 + v ^ 2)⁻¹ := by rw [hK']; ring
  -- (iv) integrate
  have hint_sum : Integrable fun v => ∑ n ∈ C, m n v * l n v * wt4 v :=
    integrable_finsetSum C fun n hn => hint n hn
  have hI2 : ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v ≤ K' * π := by
    calc ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v ≤ ∫ v, K' * (1 + v ^ 2)⁻¹ :=
          integral_mono hint_sum (integrable_inv_one_add_sq.const_mul K') hpt
      _ = K' * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : (C.card : ℝ) * (1 / 4) ≤ A / 2 * K' := by
    calc (C.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v := hsum1
      _ ≤ A / (2 * π) * (K' * π) := by gcongr
      _ = A / 2 * K' := by field_simp
  rw [hK'] at hfin
  have e : A / 2 * (X * (M₂ / (4 * lam ^ 3)) + X * ((C.card : ℝ) * (3 * lam / 4))) =
      27 * A ^ 4 * (X : ℝ) ^ 4 * M₂ / 8 + (C.card : ℝ) / 8 := by
    rw [hlam]; field_simp; ring
  rw [e] at hfin
  linarith

/-! ### The exponents of one block -/

/-- `(4C(ε/88)⁴)^{22}`, the constant of the divisor bound for powers up to `22`. -/
def A22 (ε : ℝ) : ℝ := (4 * Cdiv (ε / 88) ^ 4) ^ 22

lemma one_le_A22 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ A22 ε := by
  have hCd := one_le_Cdiv (ε := ε / 88) (by positivity) (by linarith)
  unfold A22
  exact one_le_pow₀ (by nlinarith [one_le_pow₀ (n := 4) hCd])

/-- The height of the subintervals for a power of length `Λ`: `T₀ = U^{(12σ−7)/5−8ε}Λ^{2−2σ}`. -/
def T0 (ε σ U Λ : ℝ) : ℝ := U ^ ((12 * σ - 7) / 5 - 8 * ε) * Λ ^ (2 - 2 * σ)

/-- `G_m(σ_b) ≤ (4C⁴)^{22}Λ^{1−2σ+ε}` for `m ≤ 22` (`LinnikHuxley.Gm_le` at `ε_d = ε/88`). -/
lemma Gm_le_A22 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22) {σ σb : ℝ}
    (hσ1 : σ ≤ 1) (hσb : σ ≤ σb) :
    Gm (ε / 88) P m σb ≤ A22 ε * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 - 2 * σ + ε) := by
  have hεd : 0 < ε / 88 := by positivity
  have hεd1 : ε / 88 ≤ 1 := by linarith
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ 4 * Cdiv (ε / 88) ^ 4 := by nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
  refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
  unfold A22
  exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
    (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)

/-- **Feasibility of the power count** at height `T₀`: for `3/4 ≤ σ ≤ σ_b`, `Λ = (2P)^m ≥ U^{4/5}`, `m ≤ 22`,
`4K ≤ U^{ε/44}` and `12e(4C⁴)^{22}(KE + C_K) ≤ U^{ε/2}`, `2e·G_m(σ_b)(KE + C_KΛ^{1/12}(T₀ + 2)^{5/12+ε}) ≤ (4K)^{−2m}`.
Both terms are at most a constant times `U^{−(23/15)ε}`. -/
lemma feas_zeta {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK : 0 ≤ CK) {σ σb U : ℝ}
    (hσ : 3 / 4 ≤ σ) (hσb : σ ≤ σb) (hσ1 : σ ≤ 1) (hU : 1 ≤ U) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22)
    (hΛ : U ^ (4 / 5 : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ m) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ U ^ (ε / 44))
    (hfe : 12 * Real.exp 1 * A22 ε * (KE + CK) ≤ U ^ (ε / 2)) :
    2 * Real.exp 1 * Gm (ε / 88) P m σb * (KE + CK * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 : ℝ) *
      (T0 ε σ U (((2 * P : ℕ) : ℝ) ^ m) + 2) ^ (5 / 12 + ε)) ≤ (1 / (4 * K)) ^ (2 * m) := by
  have hU0 : 0 < U := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hKE := KE_pos
  have hA1 := one_le_A22 hε (by linarith)
  have hGm : Gm (ε / 88) P m σb ≤ A22 ε * Λ ^ (1 - 2 * σ + ε) := Gm_le_A22 hε (by linarith) hP hm hσ1 hσb
  set e : ℝ := 5 / 12 + ε with he
  have he0 : 0 ≤ e := by positivity
  set a : ℝ := (12 * σ - 7) / 5 - 8 * ε with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hT0def : T0 ε σ U Λ = U ^ a * Λ ^ (2 - 2 * σ) := rfl
  have hT01 : 1 ≤ T0 ε σ U Λ := by
    rw [hT0def]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hU ha0) (Real.one_le_rpow hΛ1 (by linarith))
  -- `(T₀ + 2)^e ≤ 3T₀^e`
  have hT02 : (T0 ε σ U Λ + 2) ^ e ≤ 3 * (T0 ε σ U Λ) ^ e := by
    have h3 : T0 ε σ U Λ + 2 ≤ 3 * T0 ε σ U Λ := by linarith
    calc (T0 ε σ U Λ + 2) ^ e ≤ (3 * T0 ε σ U Λ) ^ e := Real.rpow_le_rpow (by linarith) h3 he0
      _ = (3 : ℝ) ^ e * (T0 ε σ U Λ) ^ e := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 3 * (T0 ε σ U Λ) ^ e := by
          gcongr
          calc (3 : ℝ) ^ e ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 3 := Real.rpow_one 3
  have hT0e : (T0 ε σ U Λ) ^ e = U ^ (a * e) * Λ ^ ((2 - 2 * σ) * e) := by
    rw [hT0def, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hU0.le, ← Real.rpow_mul hΛ0.le]
  -- the `Λ`-exponent of the second term is negative
  set lam : ℝ := 1 - 2 * σ + ε + 1 / 12 + (2 - 2 * σ) * e with hlam
  have hle : (2 - 2 * σ) * e ≤ 1 / 2 * e := mul_le_mul_of_nonneg_right (by linarith) he0
  have hlam0 : lam ≤ 0 := by rw [hlam]; rw [he] at hle ⊢; linarith
  have hΛlam : Λ ^ lam ≤ U ^ (4 / 5 * lam) := by
    rw [Real.rpow_mul hU0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hΛ hlam0
  have hcomb : Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * Λ ^ ((2 - 2 * σ) * e) = Λ ^ lam := by
    rw [← Real.rpow_add hΛ0, ← Real.rpow_add hΛ0, hlam]
  have hUexp : a * e + 4 / 5 * lam ≤ -(23 / 15) * ε := by
    have key : a * e + 4 / 5 * lam = (57 - 76 * σ) / 60 + ε * ((4 * σ + 5) / 5 - 10 / 3) - 8 * ε ^ 2 := by
      rw [ha, he, hlam]; ring
    have h1 : ε * ((4 * σ + 5) / 5 - 10 / 3) ≤ ε * (-(23 / 15)) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    rw [key]; linarith
  -- the first term
  have hT1 : Λ ^ (1 - 2 * σ + ε) ≤ U ^ (-(23 / 15) * ε) := by
    calc Λ ^ (1 - 2 * σ + ε) ≤ (U ^ (4 / 5 : ℝ)) ^ (1 - 2 * σ + ε) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hΛ (by linarith)
      _ = U ^ (4 / 5 * (1 - 2 * σ + ε)) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (-(23 / 15) * ε) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  -- the second term
  have hT2 : Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (T0 ε σ U Λ) ^ e ≤ U ^ (-(23 / 15) * ε) := by
    rw [hT0e]
    calc Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (U ^ (a * e) * Λ ^ ((2 - 2 * σ) * e))
        = U ^ (a * e) * (Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * Λ ^ ((2 - 2 * σ) * e)) := by ring
      _ = U ^ (a * e) * Λ ^ lam := by rw [hcomb]
      _ ≤ U ^ (a * e) * U ^ (4 / 5 * lam) := by gcongr
      _ = U ^ (a * e + 4 / 5 * lam) := by rw [← Real.rpow_add hU0]
      _ ≤ U ^ (-(23 / 15) * ε) := Real.rpow_le_rpow_of_exponent_le hU hUexp
  -- `(1/(4K))^{2m} ≥ U^{−ε}`
  have hR : U ^ (-ε) ≤ (1 / (4 * K)) ^ (2 * m) := by
    have hK0 : 0 < 4 * K := by linarith
    have h1 : U ^ (-(ε / 44)) ≤ 1 / (4 * K) := by
      rw [Real.rpow_neg hU0.le, one_div]
      exact inv_anti₀ hK0 hK
    have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
    calc U ^ (-ε) ≤ U ^ (-(ε / 44) * (2 * m : ℕ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hU ?_
          push_cast; nlinarith
      _ = (U ^ (-(ε / 44))) ^ (2 * m) := by rw [Real.rpow_mul hU0.le, Real.rpow_natCast]
      _ ≤ (1 / (4 * K)) ^ (2 * m) := pow_le_pow_left₀ (by positivity) h1 _
  have hUe : U ^ (ε / 2) * U ^ (-(23 / 15) * ε) ≤ U ^ (-ε) := by
    rw [← Real.rpow_add hU0]
    exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hG0 : 0 ≤ Gm (ε / 88) P m σb := by
    have := one_le_Cdiv (ε := ε / 88) (by positivity) (by linarith); unfold Gm; positivity
  have hu0 : 0 ≤ U ^ (-(23 / 15) * ε) := by positivity
  have hfe' : 6 * Real.exp 1 * A22 ε * (KE + CK) * U ^ (-(23 / 15) * ε) ≤
      U ^ (ε / 2) * U ^ (-(23 / 15) * ε) / 2 := by
    have := mul_le_mul_of_nonneg_right hfe hu0
    linarith
  calc 2 * Real.exp 1 * Gm (ε / 88) P m σb * (KE + CK * Λ ^ (1 / 12 : ℝ) * (T0 ε σ U Λ + 2) ^ e)
      ≤ 2 * Real.exp 1 * (A22 ε * Λ ^ (1 - 2 * σ + ε)) *
          (KE + CK * Λ ^ (1 / 12 : ℝ) * (3 * (T0 ε σ U Λ) ^ e)) := by gcongr
    _ = 2 * Real.exp 1 * A22 ε * (KE * Λ ^ (1 - 2 * σ + ε) +
          3 * CK * (Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (T0 ε σ U Λ) ^ e)) := by ring
    _ ≤ 2 * Real.exp 1 * A22 ε * (KE * U ^ (-(23 / 15) * ε) + 3 * CK * U ^ (-(23 / 15) * ε)) := by gcongr
    _ ≤ 6 * Real.exp 1 * A22 ε * (KE + CK) * U ^ (-(23 / 15) * ε) := by
        have : 0 ≤ Real.exp 1 * A22 ε * KE * U ^ (-(23 / 15) * ε) := by positivity
        linarith
    _ ≤ U ^ (ε / 2) * U ^ (-(23 / 15) * ε) / 2 := hfe'
    _ ≤ U ^ (-ε) := by
        have : 0 ≤ U ^ (ε / 2) * U ^ (-(23 / 15) * ε) := by positivity
        linarith
    _ ≤ (1 / (4 * K)) ^ (2 * m) := hR

/-- **The count of one block and one bin**: with `Λ = (2P)^m ≤ U^{6/5+ε}`, `m ≤ 22`, `4K ≤ U^{ε/44}` and
`1 + KE(4 log U + 1) ≤ U^ε`, the `⌊4U/T₀⌋ + 1` subintervals of height `T₀` carry at most
`10e(4C⁴)^{22}U^{(12/5)(1−σ)+12ε}` in all: `(4U/T₀)Λ^{2−2σ} = 4U^{(12/5)(1−σ)+8ε}` and
`Λ^{2−2σ} ≤ U^{(12/5)(1−σ)+8ε}`. -/
lemma count_bound_zeta {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb U : ℝ}
    (hσ : 3 / 4 ≤ σ) (hσb : σ ≤ σb) (hσ1 : σ ≤ 1) (hU : 1 ≤ U) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ U ^ (6 / 5 + ε)) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ U ^ (ε / 44))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε) :
    ((⌊4 * U / T0 ε σ U (((2 * P : ℕ) : ℝ) ^ m)⌋₊ + 1 : ℕ) : ℝ) *
      (2 * Real.exp 1 * Gm (ε / 88) P m σb * ((2 * P : ℕ) : ℝ) ^ m *
        (1 + KE * (2 * Real.log (((2 * P : ℕ) : ℝ) ^ m) + 1)) / (1 / (4 * K)) ^ (2 * m))
      ≤ 10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε) := by
  have hU0 : 0 < U := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hKE := KE_pos
  have hA1 := one_le_A22 hε (by linarith)
  have hGm : Gm (ε / 88) P m σb ≤ A22 ε * Λ ^ (1 - 2 * σ + ε) := Gm_le_A22 hε (by linarith) hP hm hσ1 hσb
  have hG0 : 0 ≤ Gm (ε / 88) P m σb := by
    have := one_le_Cdiv (ε := ε / 88) (by positivity) (by linarith); unfold Gm; positivity
  set a : ℝ := (12 * σ - 7) / 5 - 8 * ε with ha
  set T₀ := T0 ε σ U Λ with hT₀
  have hT0def : T₀ = U ^ a * Λ ^ (2 - 2 * σ) := rfl
  have hT₀pos : 0 < T₀ := by rw [hT0def]; positivity
  have hLc : ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * U / T₀ + 1 := by
    push_cast; linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 4 * U / T₀)]
  -- the logarithm and the power of `4K`
  have hlogΛ : Real.log Λ ≤ 2 * Real.log U := by
    have h1 : Real.log Λ ≤ Real.log (U ^ (6 / 5 + ε)) := Real.log_le_log hΛ0 hΛ
    rw [Real.log_rpow hU0] at h1
    have hl : 0 ≤ Real.log U := Real.log_nonneg hU
    nlinarith
  have hL : 1 + KE * (2 * Real.log Λ + 1) ≤ U ^ ε := by
    have h1 : KE * (2 * Real.log Λ + 1) ≤ KE * (4 * Real.log U + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hKE.le
    linarith
  have hL0 : 0 ≤ 1 + KE * (2 * Real.log Λ + 1) := by have := Real.log_nonneg hΛ1; positivity
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (2 * m) ≤ U ^ ε := by
    have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
    calc (4 * K) ^ (2 * m) ≤ (U ^ (ε / 44)) ^ (2 * m) := pow_le_pow_left₀ hK0.le hK _
      _ = U ^ (ε / 44 * (2 * m : ℕ)) := by rw [Real.rpow_mul hU0.le, Real.rpow_natCast]
      _ ≤ U ^ ε := Real.rpow_le_rpow_of_exponent_le hU (by push_cast; nlinarith)
  -- the powers of `Λ`
  have hsplitΛ : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ) * Λ ^ ε := by
    rw [← Real.rpow_add_one hΛ0.ne', ← Real.rpow_add hΛ0]; congr 1; ring
  have hΛε : Λ ^ ε ≤ U ^ (2 * ε) := by
    calc Λ ^ ε ≤ (U ^ (6 / 5 + ε)) ^ ε := Real.rpow_le_rpow hΛ0.le hΛ hε.le
      _ = U ^ ((6 / 5 + ε) * ε) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (2 * ε) := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hΛ2 : Λ ^ (2 - 2 * σ) ≤ U ^ (12 / 5 * (1 - σ) + 8 * ε) := by
    calc Λ ^ (2 - 2 * σ) ≤ (U ^ (6 / 5 + ε)) ^ (2 - 2 * σ) := Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
      _ = U ^ ((6 / 5 + ε) * (2 - 2 * σ)) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (12 / 5 * (1 - σ) + 8 * ε) := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hUT : 4 * U / T₀ * Λ ^ (2 - 2 * σ) = 4 * U ^ (12 / 5 * (1 - σ) + 8 * ε) := by
    have e1 : 12 / 5 * (1 - σ) + 8 * ε = 1 - a := by rw [ha]; ring
    have hΛp : Λ ^ (2 - 2 * σ) ≠ 0 := by positivity
    have hUa : U ^ a ≠ 0 := by positivity
    rw [e1, Real.rpow_sub hU0, Real.rpow_one, hT0def]
    field_simp
  have hpow : ∀ x : ℝ, U ^ ε * U ^ ε * (U ^ x * U ^ (2 * ε)) = U ^ (x + 4 * ε) := by
    intro x
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, ← Real.rpow_add hU0]; congr 1; ring
  have e2 : 12 / 5 * (1 - σ) + 8 * ε + 4 * ε = 12 / 5 * (1 - σ) + 12 * ε := by ring
  have hUε : 0 ≤ U ^ ε := by positivity
  calc ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
        (2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / (1 / (4 * K)) ^ (2 * m))
      = ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
          (2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) * (4 * K) ^ (2 * m)) := by
        rw [one_div, inv_pow, div_inv_eq_mul]
    _ ≤ (4 * U / T₀ + 1) * (2 * Real.exp 1 * (A22 ε * Λ ^ (1 - 2 * σ + ε)) * Λ * U ^ ε * U ^ ε) := by
        gcongr
    _ = 2 * Real.exp 1 * A22 ε * (U ^ ε * U ^ ε * (4 * U / T₀ * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) +
          U ^ ε * U ^ ε * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) := by
        rw [← hsplitΛ]; ring
    _ = 2 * Real.exp 1 * A22 ε * (U ^ ε * U ^ ε * ((4 * U / T₀ * Λ ^ (2 - 2 * σ)) * Λ ^ ε) +
          U ^ ε * U ^ ε * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) := by ring
    _ ≤ 2 * Real.exp 1 * A22 ε * (U ^ ε * U ^ ε * ((4 * U ^ (12 / 5 * (1 - σ) + 8 * ε)) * U ^ (2 * ε)) +
          U ^ ε * U ^ ε * (U ^ (12 / 5 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) := by
        rw [hUT]; gcongr
    _ = 2 * Real.exp 1 * A22 ε * (4 * (U ^ ε * U ^ ε * (U ^ (12 / 5 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) +
          U ^ ε * U ^ ε * (U ^ (12 / 5 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) := by ring
    _ = 10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε) := by
        rw [hpow, e2]; ring

/-! ### The polynomial classes on `3/4 ≤ σ ≤ 1` -/

/-- **The polynomial class with powers at well-spaced heights.** Points `β_r + iγ_r`, `σ ≤ β_r < 1`, with
1-separated heights `|γ_r| ≤ 2U`, at which `|P_b(β_r, γ_r)| ≥ ¼` (`|b_j| ≤ d(j)`), number at most
`12K·10e(4C⁴)^{22}U^{(12/5)(1−σ)+12ε}`, `K = ⌊log₂ N⌋ + 1`, for `3/4 ≤ σ ≤ 1`: some dyadic block is at least
`1/(4K)` (`InghamDensity.Pv_eq_blocks`); bins of width `1/48` in `β`; in each block a power `m` with
`(2P)^m ≥ U^{4/5}` (`LinnikHuxley.choose_m`), at most `U^{6/5+ε}` long; subintervals of height `T₀`; and
`ZetaKernel.power_count_pts` with `feas_zeta` and `count_bound_zeta`. -/
theorem class_poly_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, kTerm χ₁ Λ z n‖ ≤ KE * Λ * Real.exp (-|z.im|) + CK * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε))
    (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {σ U : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1)
    (hU : 1 < U) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXU : U ^ (1 / 25 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ U ^ (ε / 44))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (6 / 5 + ε))
    (hfe : 12 * Real.exp 1 * A22 ε * (KE + CK) ≤ U ^ (ε / 2))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε)
    {ι : Type*} (Rs : Finset ι) (β γ : ι → ℝ) (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r < 1)
    (hγ : ∀ r ∈ Rs, |γ r| ≤ 2 * U) (hsep : ∀ r ∈ Rs, ∀ r' ∈ Rs, r ≠ r' → 1 ≤ |γ r - γ r'|)
    (hbig : ∀ r ∈ Rs, 1 / 4 ≤ ‖Pv b X N (β r) (γ r)‖) :
    (Rs.card : ℝ) ≤ 12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
      (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε)) := by
  classical
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set B := 10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε) with hB
  have hU0 : 0 < U := by linarith
  -- some dyadic block of each point is at least `V`
  have hlarge : ∀ r ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkb b X N k (β r) (γ r)‖ := by
    intro r hr
    by_contra hcon
    push Not at hcon
    have h1 := hbig r hr
    rw [Pv_eq_blocks b X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkb b X N k (β r) (γ r)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkb b X N k (β r) (γ r)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset ι := fun k j =>
    Rs.filter fun r => V ≤ ‖Fkb b X N k (β r) (γ r)‖ ∧ ⌊48 * (β r - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range 12).biUnion fun j => Ck k j := by
    intro r hr
    obtain ⟨k, hk, hbigk⟩ := hlarge r hr
    have h1 := hβ r hr
    have hj : ⌊48 * (β r - σ)⌋₊ < 12 := by
      rw [Nat.floor_lt (by linarith)]
      push_cast
      linarith
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hr, hbigk, rfl⟩⟩⟩
  have hCk : ∀ k ∈ range K, ∀ j ∈ range 12, ((Ck k j).card : ℝ) ≤ B := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : U ^ (1 / 25 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * X ≤ 2 * P)
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hm22, hΛlo, hΛhi⟩ := choose_m hU (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num) h2Px
    set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
    have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P))
    have hΛ : Λ ≤ U ^ (6 / 5 + ε) := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ U ^ (6 / 5 + ε) := hXN
      · rw [show 3 * (4 / 5 : ℝ) / 2 = 6 / 5 by norm_num]
        exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
    set σb : ℝ := σ + j / 48 with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) / 48 := by positivity
      rw [hσb]; linarith
    have hbin : ∀ r ∈ Ck k j, σb ≤ β r ∧ β r < σb + 1 / 48 := by
      intro r hr
      obtain ⟨hrR, -, hbj⟩ := mem_filter.1 hr
      have h0 : 0 ≤ 48 * (β r - σ) := by have := (hβ r hrR).1; linarith
      have h1 : ((⌊48 * (β r - σ)⌋₊ : ℕ) : ℝ) ≤ 48 * (β r - σ) := Nat.floor_le h0
      have h2 : 48 * (β r - σ) < ((⌊48 * (β r - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      rw [hσb]
      constructor <;> linarith
    -- the subintervals of height `T₀`
    set T₀ := T0 ε σ U Λ with hT₀
    have hT₀pos : 0 < T₀ := by rw [hT₀, T0]; positivity
    set D : ℕ → Finset ι := fun l => (Ck k j).filter fun r => ⌊(γ r + 2 * U) / T₀⌋₊ = l with hD
    have hsubD : Ck k j ⊆ (range (⌊4 * U / T₀⌋₊ + 1)).biUnion D := by
      intro r hr
      have hγr := hγ r (mem_filter.1 hr).1
      refine mem_biUnion.2 ⟨⌊(γ r + 2 * U) / T₀⌋₊, mem_range.2 ?_, mem_filter.2 ⟨hr, rfl⟩⟩
      rw [Nat.lt_succ_iff]
      exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [(abs_le.1 hγr).2]) hT₀pos.le)
    have hDl : ∀ l ∈ range (⌊4 * U / T₀⌋₊ + 1), ((D l).card : ℝ) ≤ 2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ *
        (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m) := by
      intro l _
      have hDsub : ∀ r ∈ D l, r ∈ Ck k j := fun r hr => (mem_filter.1 hr).1
      have hT : ∀ r ∈ D l, ∀ r' ∈ D l, |γ r - γ r'| ≤ T₀ := by
        intro r hr r' hr'
        have hl1 := (mem_filter.1 hr).2
        have hl2 := (mem_filter.1 hr').2
        have g1 := hγ r (mem_filter.1 (hDsub r hr)).1
        have g2 := hγ r' (mem_filter.1 (hDsub r' hr')).1
        have a1 : 0 ≤ (γ r + 2 * U) / T₀ := div_nonneg (by linarith [(abs_le.1 g1).1]) hT₀pos.le
        have a2 : 0 ≤ (γ r' + 2 * U) / T₀ := div_nonneg (by linarith [(abs_le.1 g2).1]) hT₀pos.le
        have f1 := Nat.floor_le a1
        have f2 := Nat.lt_floor_add_one ((γ r + 2 * U) / T₀)
        have f3 := Nat.floor_le a2
        have f4 := Nat.lt_floor_add_one ((γ r' + 2 * U) / T₀)
        rw [hl1] at f1 f2
        rw [hl2] at f3 f4
        rw [le_div_iff₀ hT₀pos] at f1 f3
        rw [div_lt_iff₀ hT₀pos] at f2 f4
        rw [abs_le]; constructor <;> nlinarith
      refine power_count_pts hP hSsub (c := b) (fun i _ => hb i) hm1 (σb := σb) (by linarith) β γ
        (fun r hr => hbin r (hDsub r hr))
        (fun r hr r' hr' hne => hsep r (mem_filter.1 (hDsub r hr)).1 r' (mem_filter.1 (hDsub r' hr')).1 hne)
        hT hV0 (fun r hr => by rw [← Fkb_eq_pv]; exact (mem_filter.1 (hDsub r hr)).2.1)
        (εd := ε / 88) (by positivity) (by linarith) (B := CK * Λ ^ (1 / 12 : ℝ) * (T₀ + 2) ^ (5 / 12 + ε))
        (by positivity) (fun z hz0 hz1 hzT => ?_) ?_
      · refine (hCK Λ hΛ1 z hz0 hz1).trans ?_
        gcongr
      · exact feas_zeta hε hε1 hCK0 hσ hσσb hσ1 hU.le hP hm22 hΛlo hK1 hK hfe
    calc ((Ck k j).card : ℝ) ≤ ((range (⌊4 * U / T₀⌋₊ + 1)).biUnion D).card := by
          exact_mod_cast card_le_card hsubD
      _ ≤ ∑ l ∈ range (⌊4 * U / T₀⌋₊ + 1), ((D l).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _l ∈ range (⌊4 * U / T₀⌋₊ + 1),
            (2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m)) :=
          sum_le_sum hDl
      _ = ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
            (2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ B := count_bound_zeta hε hε1 hσ hσσb hσ1 hU.le hP hm22 hΛ hK1 hK hlog
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range 12).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range 12).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 12, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 12, B := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = 12 * (K : ℝ) * B := by simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-! ### One window -/

/-- **The three classes in one window, with powers and the Halász–Montgomery inequality**: `trichotomy7`, then
`class_poly_huxley` for the two polynomial classes and `class3_count_small` (at `δ = 1/4`) for the integral class, over
the parity classes of the unit windows (`InghamDensity.card_le_of_classes`). -/
theorem window_classes_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, kTerm χ₁ Λ z n‖ ≤ KE * Λ * Real.exp (-|z.im|) + CK * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε))
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε))
    {σ U Y : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) (hY : 8 ≤ Y) (hUY : 36864 * U ≤ Y ^ 7)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hXU : U ^ (1 / 25 : ℝ) ≤ 2 * X) (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ U ^ (ε / 44))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (6 / 5 + ε))
    (hfe : 12 * Real.exp 1 * A22 ε * (KE + CK) ≤ U ^ (ε / 2))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε)
    (Z : Finset (ZeroIdx (sqF Xi))) (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ 2 * Kloc (2 * U + 1) * (2 * (12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
        (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε))) +
      27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))) := by
  classical
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  set B1 := 12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε))
    with hB1
  set B3 := 27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε)) with hB3
  have hB10 : 0 ≤ B1 := by have := one_le_A22 hε (by linarith); positivity
  have hB30 : 0 ≤ B3 := by have := KG_pos; positivity
  have htri : ∀ i ∈ Z, 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
      ∨ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖ := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hZ i hi
    exact trichotomy7 hX hN hY hU hUY hM (by linarith) (βs_lt_one i) (by rw [abs_γs]; exact h1)
      (by rw [abs_γs]; exact h2) (DetectCore.zeta_βsγs i)
  set Z1 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖
  set Z2 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
  set Z3 := Z.filter fun i => U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖
  have hcover : Z ⊆ Z1 ∪ Z2 ∪ Z3 := by
    intro i hi
    rcases htri i hi with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hpoly : ∀ b : ℕ → ℂ, (∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) → ∀ (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi)),
      (∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n) →
      (∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1) →
      (∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ (σ ≤ βs (rep n) ∧ 1 / 4 ≤ ‖Pv b X N (βs (rep n)) (γs (rep n))‖)) →
      (C.card : ℝ) ≤ B1 := by
    intro b hb C rep hC hwin hdet
    exact class_poly_huxley hε hε1 hCK0 hCK b hb hσ hσ1 (by linarith) hX hN hXU hK hXN hfe hlog C
      (fun n => βs (rep n)) (fun n => γs (rep n)) (fun n hn => ⟨(hdet n hn).2.1, βs_lt_one _⟩)
      (fun n hn => by rw [abs_γs]; exact (hdet n hn).1) (sep_of_windows C rep hC hwin)
      (fun n hn => (hdet n hn).2.2)
  have hZ1 : (Z1.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖) Z1
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b1 X Y) (norm_b1_le X hY0) C rep hC hwin hdet
  have hZ2 : (Z2.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖) Z2
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b2 X Y) (norm_b2_le X hY0) C rep hC hwin hdet
  have hZ3 : (Z3.card : ℝ) ≤ 2 * B3 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖) Z3
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB30 fun C rep hC hwin hdet =>
        class3_count_small hε.le (by linarith) hC₄ h4 hX (δ := 1 / 4) (by norm_num) (by linarith) hU
          (by linarith) C rep hC hwin hdet
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2 ∪ Z3).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card + Z3.card := by
        have h1 := card_union_le (Z1 ∪ Z2) Z3
        have h2 := card_union_le Z1 Z2
        exact_mod_cast h1.trans (by omega)
    _ ≤ 2 * B1 * Kloc (2 * U + 1) + 2 * B1 * Kloc (2 * U + 1) + 2 * B3 * Kloc (2 * U + 1) := by
        linarith
    _ = 2 * Kloc (2 * U + 1) * (2 * B1 + B3) := by ring

/-- **The integral class at `Y = U^{3/5}`, `X ≤ U^{1/25}`**: `27(12KG)⁴Y^{2−4σ}X⁴C₄(2U + 2)^{1+ε} ≤
243(12KG)⁴C₄U^{(12/5)(1−σ)+13ε}`, the exponent `(12/5)(1 − σ) − 1/25 + ε` (`LinnikHuxley.class2_bound_huxley`). -/
lemma class3_bound_zeta {ε C₄ σ U : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hC₄ : 0 ≤ C₄) (hU : 8 ≤ U)
    {X : ℕ} (hXU : (X : ℝ) ≤ U ^ (1 / 25 : ℝ)) :
    27 * (3 * KG * (U ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))
      ≤ 243 * (12 * KG) ^ 4 * C₄ * U ^ (12 / 5 * (1 - σ) + 13 * ε) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hKG := KG_pos
  have hY : ((U ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = U ^ (12 / 5 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ U ^ (4 / 25 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (U ^ (1 / 25 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXU 4
      _ = U ^ (4 / 25 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  have hM : (2 * U + 2) ^ (1 + ε) ≤ 9 * U ^ (1 + ε) := by
    calc (2 * U + 2) ^ (1 + ε) ≤ (3 * U) ^ (1 + ε) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + ε) * U ^ (1 + ε) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + ε) := by
          gcongr
          calc (3 : ℝ) ^ (1 + ε) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have hexp : 12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε) ≤ 12 / 5 * (1 - σ) + 13 * ε := by linarith
  calc 27 * (3 * KG * (U ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))
      = 27 * (12 * KG) ^ 4 * C₄ * (((U ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 * (2 * U + 2) ^ (1 + ε)) := by
        ring
    _ ≤ 27 * (12 * KG) ^ 4 * C₄ * (U ^ (12 / 5 * (1 / 2 - σ)) * U ^ (4 / 25 : ℝ) * (9 * U ^ (1 + ε))) := by
        rw [hY]; gcongr
    _ = 243 * (12 * KG) ^ 4 * C₄ * (U ^ (12 / 5 * (1 / 2 - σ)) * U ^ (4 / 25 : ℝ) * U ^ (1 + ε)) := by ring
    _ = 243 * (12 * KG) ^ 4 * C₄ * U ^ (12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε)) := by
        rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
    _ ≤ 243 * (12 * KG) ^ 4 * C₄ * U ^ (12 / 5 * (1 - σ) + 13 * ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 hexp) (by positivity)

/-! ### Large `U` -/

/-- The conditions on `U` used in the range `3/4 ≤ σ ≤ 1` hold for all large `U`: `log U ≤ U^η/η`
(`Real.log_le_rpow_div`) and `c ≤ U^θ` eventually. -/
lemma eventually_zeta {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ U : ℝ in atTop, (8 : ℝ) ^ 25 ≤ U ∧ 4 * (1 + 2 * Real.log U) ≤ U ^ (ε / 44) ∧
      (2 * (23 * U ^ (3 / 5 : ℝ) * Real.log (U ^ (3 / 5 : ℝ)))) ^ 2 ≤ U ^ (6 / 5 + ε) ∧
      23 * U ^ (3 / 5 : ℝ) * Real.log (U ^ (3 / 5 : ℝ)) ≤ U ∧ A ≤ U ^ (ε / 2) ∧
      1 + KE * (4 * Real.log U + 1) ≤ U ^ ε := by
  have hev : ∀ c θ : ℝ, 0 < θ → ∀ᶠ U : ℝ in atTop, c ≤ U ^ θ := fun c θ hθ =>
    (tendsto_rpow_atTop hθ).eventually_ge_atTop c
  have hKE := KE_pos
  set r := ε / 44 with hr
  have hr0 : 0 < r := by positivity
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 25), hev (4 + 16 / r) (r / 2) (by positivity),
    hev ((138 / 5) ^ 2 * (4 / ε) ^ 2) (ε / 2) (by positivity), hev 69 (1 / 5) (by norm_num),
    hev A (ε / 2) (by positivity), hev (1 + KE + 8 * KE / ε) (ε / 2) (by positivity)]
    with U h1 h2 h3 h4 h5 h6
  have hU1 : 1 ≤ U := le_trans (by norm_num) h1
  have hU0 : 0 < U := by linarith
  have hl0 : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hlog : Real.log (U ^ (3 / 5 : ℝ)) = 3 / 5 * Real.log U := Real.log_rpow hU0 _
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  · have hl : Real.log U ≤ U ^ (r / 2) / (r / 2) := Real.log_le_rpow_div hU0.le (by positivity)
    have hUr : 1 ≤ U ^ (r / 2) := Real.one_le_rpow hU1 (by positivity)
    calc 4 * (1 + 2 * Real.log U) ≤ 4 * (1 + 2 * (U ^ (r / 2) / (r / 2))) := by gcongr
      _ = 4 + 16 / r * U ^ (r / 2) := by field_simp; ring
      _ ≤ (4 + 16 / r) * U ^ (r / 2) := by
          have : 0 ≤ 16 / r := by positivity
          nlinarith
      _ ≤ U ^ (r / 2) * U ^ (r / 2) := by gcongr
      _ = U ^ r := by rw [← Real.rpow_add hU0]; ring_nf
  · have hl : Real.log U ≤ 4 / ε * U ^ (ε / 4) := by
      have h := Real.log_le_rpow_div hU0.le (by positivity : (0 : ℝ) < ε / 4)
      calc Real.log U ≤ U ^ (ε / 4) / (ε / 4) := h
        _ = 4 / ε * U ^ (ε / 4) := by field_simp
    have e1 : (U ^ (3 / 5 : ℝ)) ^ 2 = U ^ (6 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; congr 1; norm_num
    have e2 : (U ^ (ε / 4)) ^ 2 = U ^ (ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
    calc (2 * (23 * U ^ (3 / 5 : ℝ) * Real.log (U ^ (3 / 5 : ℝ)))) ^ 2
        = (138 / 5) ^ 2 * (U ^ (3 / 5 : ℝ)) ^ 2 * Real.log U ^ 2 := by rw [hlog]; ring
      _ ≤ (138 / 5) ^ 2 * (U ^ (3 / 5 : ℝ)) ^ 2 * (4 / ε * U ^ (ε / 4)) ^ 2 := by gcongr
      _ = (138 / 5) ^ 2 * (4 / ε) ^ 2 * (U ^ (6 / 5 : ℝ) * U ^ (ε / 2)) := by
          rw [mul_pow (4 / ε), e1, e2]; ring
      _ ≤ U ^ (ε / 2) * (U ^ (6 / 5 : ℝ) * U ^ (ε / 2)) := by gcongr
      _ = U ^ (6 / 5 + ε) := by rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]; ring_nf
  · have hl : Real.log U ≤ 5 * U ^ (1 / 5 : ℝ) := by
      have h := Real.log_le_rpow_div hU0.le (by norm_num : (0 : ℝ) < 1 / 5)
      calc Real.log U ≤ U ^ (1 / 5 : ℝ) / (1 / 5) := h
        _ = 5 * U ^ (1 / 5 : ℝ) := by ring
    calc 23 * U ^ (3 / 5 : ℝ) * Real.log (U ^ (3 / 5 : ℝ)) = 69 / 5 * U ^ (3 / 5 : ℝ) * Real.log U := by
          rw [hlog]; ring
      _ ≤ 69 / 5 * U ^ (3 / 5 : ℝ) * (5 * U ^ (1 / 5 : ℝ)) := by gcongr
      _ = 69 * U ^ (4 / 5 : ℝ) := by
          have e : U ^ (3 / 5 : ℝ) * U ^ (1 / 5 : ℝ) = U ^ (4 / 5 : ℝ) := by rw [← Real.rpow_add hU0]; norm_num
          rw [← e]; ring
      _ ≤ U ^ (1 / 5 : ℝ) * U ^ (4 / 5 : ℝ) := by gcongr
      _ = U := by rw [← Real.rpow_add hU0]; norm_num
  · have hl : Real.log U ≤ 2 / ε * U ^ (ε / 2) := by
      have h := Real.log_le_rpow_div hU0.le (by positivity : (0 : ℝ) < ε / 2)
      calc Real.log U ≤ U ^ (ε / 2) / (ε / 2) := h
        _ = 2 / ε * U ^ (ε / 2) := by field_simp
    have hUe : 1 ≤ U ^ (ε / 2) := Real.one_le_rpow hU1 (by positivity)
    calc 1 + KE * (4 * Real.log U + 1) ≤ 1 + KE * (4 * (2 / ε * U ^ (ε / 2)) + 1) := by gcongr
      _ = (1 + KE) + 8 * KE / ε * U ^ (ε / 2) := by field_simp; ring
      _ ≤ (1 + KE + 8 * KE / ε) * U ^ (ε / 2) := by
          have : 0 ≤ 8 * KE / ε := by positivity
          nlinarith
      _ ≤ U ^ (ε / 2) * U ^ (ε / 2) := by gcongr
      _ = U ^ ε := by rw [← Real.rpow_add hU0]; ring_nf

/-- **One window on `3/4 ≤ σ ≤ 1`**: for every `0 < ε ≤ 1/200` there is `Cw` such that for `3/4 ≤ σ ≤ 1` and `U ≥ 8` at
most `Cw(log U)^{11}U^{(12/5)(1−σ)+13ε}` zeros have `U ≤ |γ| ≤ 2U` and `β ≥ σ`. For `U ≥ U₁` (`eventually_zeta`),
`window_classes_huxley` at `X = ⌊U^{1/25}⌋`, `Y = U^{3/5}`, `N = ⌊22Y log Y/X⌋ + 1` (`Xw`, `Yw`, `Nw` at `U^{1/25}`,
`c = 7`); below `U₁` the zeros with `|γ| ≤ 2U₁`. -/
theorem window_count_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 → ∀ U : ℝ, 8 ≤ U → ∀ Z : Finset (ZeroIdx (sqF Xi)),
      (∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) →
        (Z.card : ℝ) ≤ Cw * Real.log U ^ 11 * U ^ (12 / 5 * (1 - σ) + 13 * ε) := by
  obtain ⟨CK, hCK0, hCK⟩ := norm_kz_le (ε := ε) hε (by linarith)
  obtain ⟨C₄', hC₄'⟩ := zeta_fourth_moment (ε := ε) hε (by linarith)
  set C₄ := max C₄' 0 with hC₄def
  have hC₄0 : 0 ≤ C₄ := le_max_right _ _
  have h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε) := by
    intro C' t hsep T hT ht
    refine (hC₄' C' t hsep T hT ht).trans ?_
    gcongr
    exact le_max_left _ _
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (eventually_zeta hε (12 * Real.exp 1 * A22 ε * (KE + CK)))
  set U₁ := max U₀ ((8 : ℝ) ^ 25) with hU₁
  set Cfin : ℝ := ((finite_re_le (2 * U₁)).toFinset.card : ℝ) with hCfin
  have hKG := KG_pos
  have hKc := Kc_nonneg
  have hA1 := one_le_A22 hε (by linarith)
  set Cmain : ℝ := 2 * Kc * (240 * Real.exp 1 * A22 ε + 243 * (12 * KG) ^ 4 * C₄) with hCmain
  have hCmain0 : 0 ≤ Cmain := by positivity
  have hCf : 0 ≤ Cfin := Nat.cast_nonneg _
  refine ⟨Cfin + Cmain, by positivity, fun σ hσ hσ1 U hU Z hZ => ?_⟩
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  set E := 12 / 5 * (1 - σ) + 13 * ε with hE
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hUE : 1 ≤ U ^ E := Real.one_le_rpow hU1 hE0
  have hL := log_ge_two hU
  have hL11 : 1 ≤ Real.log U ^ 11 := one_le_pow₀ (by linarith)
  rcases lt_or_ge U U₁ with hsmall | hlarge
  · -- below `U₁`: every zero counted has `|γ| ≤ 2U₁`
    have hsub : Z ⊆ (finite_re_le (2 * U₁)).toFinset := fun i hi => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      linarith [(hZ i hi).2.1]
    have hc : (Z.card : ℝ) ≤ Cfin := by rw [hCfin]; exact_mod_cast card_le_card hsub
    have h1 : 1 ≤ Real.log U ^ 11 * U ^ E := one_le_mul_of_one_le_of_one_le hL11 hUE
    have h2 : 0 ≤ Cmain * (Real.log U ^ 11 * U ^ E) := by positivity
    calc (Z.card : ℝ) ≤ Cfin := hc
      _ ≤ Cfin * (Real.log U ^ 11 * U ^ E) := le_mul_of_one_le_right hCf h1
      _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by nlinarith
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := hU₀ U (le_trans (le_max_left _ _) hlarge)
  -- the parameters
  set U' : ℝ := U ^ (1 / 25 : ℝ) with hU'
  have hU'8 : 8 ≤ U' := by
    rw [hU']
    calc (8 : ℝ) = ((8 : ℝ) ^ 25) ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ U ^ (1 / 25 : ℝ) := Real.rpow_le_rpow (by positivity) ha (by norm_num)
  have hYU : Yw 7 U' = U ^ (3 / 5 : ℝ) := by rw [hU']; exact Yw_seven hU0
  have hX : 1 ≤ Xw U' := Xw_one hU'8
  have hN : 1 ≤ Nw 7 U' := Nw_one
  have hY8 : 8 ≤ Yw 7 U' := le_trans hU'8 (Yw_ge (by norm_num) hU'8)
  have hM : 22 * Yw 7 U' * Real.log (Yw 7 U') ≤ ((Xw U' * Nw 7 U' : ℕ) : ℝ) := XN_ge hU'8
  have hXNle : ((Xw U' * Nw 7 U' : ℕ) : ℝ) ≤ 23 * Yw 7 U' * Real.log (Yw 7 U') := XN_le (by norm_num) hU'8
  have hXU' : (Xw U' : ℝ) ≤ U ^ (1 / 25 : ℝ) := Xw_le hU'8
  have hXU2 : U ^ (1 / 25 : ℝ) ≤ 2 * (Xw U' : ℝ) := by have := Xw_half hU'8; rw [← hU']; linarith
  have hXr : (1 : ℝ) ≤ Xw U' := by exact_mod_cast hX
  have hUY : 36864 * U ≤ (Yw 7 U') ^ 7 := by
    rw [hYU, ← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    have e : U ^ ((3 / 5 : ℝ) * ((7 : ℕ) : ℝ)) = U ^ (16 / 5 : ℝ) * U := by
      rw [← Real.rpow_add_one hU0.ne']; norm_num
    rw [e]
    have h36 : (36864 : ℝ) ≤ U ^ (16 / 5 : ℝ) := by
      calc (36864 : ℝ) ≤ ((8 : ℝ) ^ 25) ^ (16 / 5 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ U ^ (16 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) ha (by norm_num)
    nlinarith
  have hNU : (Nw 7 U' : ℝ) ≤ U := by
    have h1 : (Nw 7 U' : ℝ) ≤ ((Xw U' * Nw 7 U' : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYU] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 7 U') + 1 : ℕ) : ℝ) ≤ U ^ (ε / 44) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNU) (by norm_num)).trans hb
  have hXN : (2 * ((Xw U' * Nw 7 U' : ℕ) : ℝ)) ^ 2 ≤ U ^ (6 / 5 + ε) := by
    refine le_trans ?_ hc
    rw [← hYU]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hwc := window_classes_huxley hε hε1 hCK0 hCK hC₄0 h4 hσ hσ1 (by linarith) hY8 hUY hX hN hM hXU2 hK hXN
    he hf Z hZ
  rw [hYU] at hwc
  refine hwc.trans ?_
  -- the two classes as powers of `U`
  have hKle : ((Nat.log 2 (Nw 7 U') + 1 : ℕ) : ℝ) ≤ U ^ ε := by
    have h1 : U ^ (ε / 44) ≤ U ^ ε := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
    linarith
  have hpow : U ^ ε * U ^ (12 / 5 * (1 - σ) + 12 * ε) = U ^ E := by
    rw [← Real.rpow_add hU0, hE]; congr 1; ring
  have hpart1 : 2 * (12 * ((Nat.log 2 (Nw 7 U') + 1 : ℕ) : ℝ) *
      (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε))) ≤ 240 * Real.exp 1 * A22 ε * U ^ E := by
    calc 2 * (12 * ((Nat.log 2 (Nw 7 U') + 1 : ℕ) : ℝ) *
          (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε)))
        ≤ 2 * (12 * U ^ ε * (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε))) := by gcongr
      _ = 240 * Real.exp 1 * A22 ε * (U ^ ε * U ^ (12 / 5 * (1 - σ) + 12 * ε)) := by ring
      _ = 240 * Real.exp 1 * A22 ε * U ^ E := by rw [hpow]
  have hpart3 := class3_bound_zeta (σ := σ) hε hε1 hC₄0 (by linarith : 8 ≤ U) hXU'
  rw [← hE] at hpart3
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have hlogU : Real.log U ≤ Real.log U ^ 11 := by
    calc Real.log U = Real.log U ^ 1 := (pow_one _).symm
      _ ≤ Real.log U ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hUE0 : 0 ≤ U ^ E := by positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (12 * ((Nat.log 2 (Nw 7 U') + 1 : ℕ) : ℝ) *
        (10 * Real.exp 1 * A22 ε * U ^ (12 / 5 * (1 - σ) + 12 * ε))) +
      27 * (3 * KG * (U ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * ((Xw U' : ℕ) : ℝ) ^ 4 *
        (C₄ * (2 * U + 2) ^ (1 + ε)))
      ≤ 2 * (Kc * Real.log U) * (240 * Real.exp 1 * A22 ε * U ^ E + 243 * (12 * KG) ^ 4 * C₄ * U ^ E) := by
        gcongr
    _ = Cmain * Real.log U * U ^ E := by rw [hCmain]; ring
    _ ≤ Cmain * Real.log U ^ 11 * U ^ E := by gcongr
    _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by gcongr; linarith

/-! ### Huxley's estimate on `3/4 ≤ σ ≤ 11/12` -/

/-- **The density estimate with Huxley's exponent on `3/4 ≤ σ ≤ 11/12`**: for every `0 < ε ≤ 1/200` there is `C ≥ 0`
with `N(σ, T) ≤ C T^{(12/5 + 156ε)(1−σ)}(log T)^{12}` for `T ≥ 2` (`ZetaIngham.nx_le_of_windows` with
`window_count_huxley`; `13ε ≤ 156ε(1 − σ)` for `σ ≤ 11/12`). -/
theorem nx_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 11 / 12 →
      (NX (σ - 1 / 2) T : ℝ) ≤ C * T ^ ((12 / 5 + 156 * ε) * (1 - σ)) * Real.log T ^ 12 := by
  obtain ⟨Cw, hCw0, hCw⟩ := window_count_huxley hε hε1
  refine ⟨((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw, by positivity, fun T hT σ hσ hσ1 => ?_⟩
  have he0 : 0 ≤ 12 / 5 * (1 - σ) + 13 * ε := by nlinarith
  have hN := nx_le_of_windows he0 hCw0 (fun U hU Z hZ => hCw σ hσ (by linarith) U hU Z hZ) hT
  refine hN.trans ?_
  have hT1 : 1 ≤ T := by linarith
  have hexp : 12 / 5 * (1 - σ) + 13 * ε ≤ (12 / 5 + 156 * ε) * (1 - σ) := by nlinarith
  have hlog : 0 ≤ Real.log T ^ 12 := by have := Real.log_nonneg hT1; positivity
  have hc : 0 ≤ ((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw := by positivity
  gcongr

/-! ### The density exponent `12/5` and primes in short intervals -/

/-- **Zero density at the exponent `12/5`**: `N(σ, T) ≪ T^{(12/5 + ε)(1−σ)}(log T)^{12}` for every `ε > 0`: the trivial
count below `σ = 7/12`, `ZetaIngham.nx_ingham` on `[7/12, 3/4]`, `nx_huxley` on `[3/4, 11/12]`, and no zero above
`11/12` (`Eis.ne_zero_of_re_gt_eleven_twelfths`). -/
theorem densityXi_twelve_fifths {ε : ℝ} (hε : 0 < ε) : DensityXi (12 / 5 + ε) 12 := by
  classical
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set ε₂ := min ε (1 / 200) / 156 with hε₂
  have hm0 : 0 < min ε (1 / 200) := lt_min hε (by norm_num)
  have hm1 : min ε (1 / 200) ≤ 1 / 200 := min_le_right _ _
  have hmε : min ε (1 / 200) ≤ ε := min_le_left _ _
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂1 : ε₂ ≤ 1 / 200 := by rw [hε₂]; linarith
  have hε₂ε : 156 * ε₂ ≤ ε := by rw [hε₂]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := nx_ingham hε₁0 hε₁1
  obtain ⟨C₂, hC₂0, hC₂⟩ := nx_huxley hε₂0 hε₂1
  set Ca : ℝ := 2 * Kc * 2 ^ 11 with hCa
  have hKc := Kc_nonneg
  have hCa0 : 0 ≤ Ca := by positivity
  refine ⟨Ca + C₁ + C₂, by positivity, fun T hT w hw0 hw1 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set e := (12 / 5 + ε) * (1 / 2 - w) with he
  have he0 : 0 ≤ e := by rw [he]; nlinarith
  have hTe : 1 ≤ T ^ e := Real.one_le_rpow hT1 he0
  have hlog12 : 0 ≤ Real.log T ^ 12 := by have := Real.log_nonneg hT1; positivity
  have e12 : Real.log T ^ (12 : ℝ) = Real.log T ^ (12 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [e12]
  have hw' : w = 1 / 2 + w - 1 / 2 := by ring
  have he' : e = (12 / 5 + ε) * (1 - (1 / 2 + w)) := by rw [he]; ring
  rcases lt_or_ge w (1 / 12) with hw | hw
  · -- `σ < 7/12`: the trivial count
    rw [NX_eq_card]
    have h1 : (((finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im|).card : ℝ) ≤ (T + 1) * Kloc T :=
      (Nat.cast_le.2 (card_filter_le _ _)).trans (card_re_le hT0.le)
    have h2 : Kloc T ≤ Kc * Real.log T :=
      (Kloc_mono (by linarith) (by linarith : T ≤ 2 * T + 1)).trans (Kloc_le hT)
    have h3 : T ≤ T ^ e := by
      calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ e := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [he]; nlinarith)
    have h4 := log_le_pow12 hT
    have h5 : 0 ≤ Kc * Real.log T := mul_nonneg hKc (Real.log_nonneg hT1)
    calc (((finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im|).card : ℝ) ≤ (T + 1) * Kloc T := h1
      _ ≤ (2 * T) * (Kc * Real.log T) := by
          gcongr
          · exact Kloc_nonneg hT0.le
          · linarith
      _ ≤ (2 * T ^ e) * (Kc * (2 ^ 11 * Real.log T ^ 12)) := by gcongr
      _ = Ca * T ^ e * Real.log T ^ 12 := by rw [hCa]; ring
      _ ≤ (Ca + C₁ + C₂) * T ^ e * Real.log T ^ 12 := by gcongr; linarith
  rcases le_or_gt w (1 / 4) with hw2 | hw2
  · -- `7/12 ≤ σ ≤ 3/4`: Ingham
    have h := hC₁ T hT (1 / 2 + w) (by linarith) (by linarith)
    rw [← hw'] at h
    have hexp : (12 / 5 + ε₁) * (1 - (1 / 2 + w)) ≤ e := by rw [he']; nlinarith
    calc (NX w T : ℝ) ≤ C₁ * T ^ ((12 / 5 + ε₁) * (1 - (1 / 2 + w))) * Real.log T ^ 12 := h
      _ ≤ C₁ * T ^ e * Real.log T ^ 12 := by gcongr
      _ ≤ (Ca + C₁ + C₂) * T ^ e * Real.log T ^ 12 := by gcongr; linarith
  rcases le_or_gt w (5 / 12) with hw3 | hw3
  · -- `3/4 ≤ σ ≤ 11/12`: Huxley
    have h := hC₂ T hT (1 / 2 + w) (by linarith) (by linarith)
    rw [← hw'] at h
    have hexp : (12 / 5 + 156 * ε₂) * (1 - (1 / 2 + w)) ≤ e := by rw [he']; nlinarith
    calc (NX w T : ℝ) ≤ C₂ * T ^ ((12 / 5 + 156 * ε₂) * (1 - (1 / 2 + w))) * Real.log T ^ 12 := h
      _ ≤ C₂ * T ^ e * Real.log T ^ 12 := by gcongr
      _ ≤ (Ca + C₁ + C₂) * T ^ e * Real.log T ^ 12 := by gcongr; linarith
  · -- `σ > 11/12`: no zeros
    have hempty : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hwi
      have hβ : 11 / 12 < ((βs i : ℂ) + (γs i : ℝ) * I).re := by simp [βs]; linarith
      exact (Eis.ne_zero_of_re_gt_eleven_twelfths hβ).1 (DetectCore.zeta_βsγs i)
    have hzero : NX w T = 0 := by unfold NX; rw [hempty, Set.ncard_empty]
    rw [hzero, Nat.cast_zero]
    positivity

/-- `InghamDensity.short_primes_of_density_eps` with the zero-free region of the half-plane
(`ShortPrimesHalfPlane.zeroFreeXi_of_halfplane`) in place of Korobov–Vinogradov's (`ShortKV.zeroFreeXi_KV`). -/
theorem short_primes_of_density_eps_hp {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hd : ∀ ε > 0, ∃ B : ℝ, DensityXi (A₀ + ε) B) {θ : ℝ} (h1 : 1 / 2 < θ) (h2 : 1 - 1 / A₀ < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  have hzf := ShortPrimesHalfPlane.zeroFreeXi_of_halfplane (le_refl (0 : ℝ))
  rcases lt_or_ge θ 1 with hθ1 | hθ1
  · have h1θ : 0 < 1 - θ := by linarith
    have hinv : A₀ < 1 / (1 - θ) := by
      rw [lt_div_iff₀ h1θ]
      have h3 : 1 - θ < 1 / A₀ := by linarith
      rw [lt_div_iff₀ hA₀] at h3
      linarith
    set A := (A₀ + 1 / (1 - θ)) / 2 with hA
    have hAA₀ : A₀ < A := by rw [hA]; linarith
    have hA1 : A < 1 / (1 - θ) := by rw [hA]; linarith
    obtain ⟨B, hB⟩ := hd (A - A₀) (by linarith)
    rw [show A₀ + (A - A₀) = A by ring] at hB
    refine short_primes_of_density (by linarith) (by norm_num) hB hzf h1 ?_
    have h4 : A * (1 - θ) < 1 := by rwa [lt_div_iff₀ h1θ] at hA1
    have h5 : 1 - θ < 1 / A := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  · obtain ⟨B, hB⟩ := hd 1 one_pos
    refine short_primes_of_density (by linarith) (by norm_num) hB hzf h1 ?_
    have : 0 < 1 / (A₀ + 1) := by positivity
    linarith

/-- **Primes in short intervals for every `θ > 7/12`**: from `densityXi_twelve_fifths` (`1 − 5/12 = 7/12`), with the
zero-free region of the half-plane. -/
theorem short_primes_seven_twelfths {θ : ℝ} (hθ : 7 / 12 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ :=
  short_primes_of_density_eps_hp (A₀ := 12 / 5) (by norm_num) (fun ε hε => ⟨12, densityXi_twelve_fifths hε⟩)
    (by linarith) (by norm_num; linarith)

end ZetaHuxley

#print axioms ZetaHuxley.trichotomy7
#print axioms ZetaHuxley.class3_count_small
#print axioms ZetaHuxley.class_poly_huxley
#print axioms ZetaHuxley.window_count_huxley
#print axioms ZetaHuxley.nx_huxley
#print axioms ZetaHuxley.densityXi_twelve_fifths
#print axioms ZetaHuxley.short_primes_of_density_eps_hp
#print axioms ZetaHuxley.short_primes_seven_twelfths
