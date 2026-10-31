import SmoothPerron
import DirMean

/-!
# Short intervals from mean values of Dirichlet polynomials

For a finite set `S` of positive integers and `a : ℕ → ℂ` let `A(s) = Σ_{n∈S} a_n n^{−s}`; on the line,
`A(1/2 + it) = dp S (coef a) t` with `coef a n = a_n n^{−1/2}` (`dp_coef`, `DirMean.dp`). This module proves the
analytic step behind Type II estimates for primes in short intervals (Baker, Harman and Pintz's Lemma 6; Harman,
*Prime-detecting sieves*, §7). There is an absolute constant `C` such that for `0 < ε < 1`, `k ∈ ℕ`,
`0 < y ≤ y₁ ≤ x/2`, `0 < T₀ ≤ T` and `|a_n| ≤ B` on `S` (`norm_sum_Ioc_sub_le`):

`|Σ_{x−y<n≤x} a_n − (y/y₁) Σ_{x−y₁<n≤x} a_n| ≤ C(y/√x) ∫_{T₀≤|t|≤T} |A(1/2 + it)| dt
  + C(1 + T₀)(y/√x)(y₁/x) ∫_{|t|≤T₀} |A(1/2 + it)| dt + C√x (Σ_{n∈S} |a_n| n^{−1/2}) ε^{−1}(2/(εT))^k
  + 8B(xε(k + 3) + 1)`.

With `ε = y x^{−1−κ}` the last term is `8B(y x^{−κ}(k + 3) + 1)`; with `T = 2x^{1+κ+η}/y` the factor `(2/(εT))^k`
is `x^{−kη}`, so for `S ⊆ (x/2, 2x]` the tail term is `≪ B x^{2+κ−kη}/y`, which is `≪ B y x^{−κ}` once
`kη ≥ 2 + 2κ` (and `y ≥ 1`). The `k` averages below are what make `T` this short: for `k = 0` the tail term does
not decay in `T`. The low range `|t| ≤ T₀` costs at most `2CT₀(1 + T₀)(y/√x)(y₁/x) max_{|t|≤T₀} |A|`, and
`|A(1/2 + it)| ≤ Σ_{n∈S} |a_n| n^{−1/2}` (`norm_dp_le`, `integral_norm_dp_le`).

The route.
* The window. PNT+'s `Smooth1 ν ε` (`1` up to `1 − ε log 2`, `0` from `1 + 2ε log 2`) is averaged `k` times over
  the dilations `u ↦ u e^v`, `0 ≤ v ≤ ε`: `W₀ = Smooth1 ν ε`, `W_{k+1}(u) = (1/ε) ∫_0^ε W_k(u e^v) dv` (`W`). Then
  `W_k(u) = 1` for `u ≤ (1 − ε log 2)e^{−kε}`, `W_k(u) = 0` for `u ≥ 1 + 2ε log 2` and `|W_k| ≤ 1` (`W_eq_one`,
  `W_eq_zero`, `abs_W_le_one`). The window of `(x − y, x]` is `w_y(n) = W_k(n/x) − W_k(n/(x − y))` (`win`).
* Mellin inversion on `Re s = 1/2` (`W_eq_integral`, `sum_W_eq`). For `k = 0` this is
  Mathlib's `mellinInv_mellin_eq` at `σ = 1/2`, the transform being integrable on the line by PNT+'s bound
  `|𝓜(Smooth1)(s)| ≤ C/(ε|s|²)` (`MellinOfSmooth1b`). Each average multiplies the transform by
  `G(s) = (1/ε) ∫_0^ε e^{−vs} dv` (Fubini, `integral_integral_swap`), and `|G| ≤ 1`, `|G(s)| ≤ 2/(ε|s|)` on
  `Re s ≥ 0` (`norm_G_le_one`, `norm_G_le`). The finite sum over `S` is exchanged with the integral term by term,
  so no line of integration is moved.
* The kernel `x^s − (x − y)^s` (`powDiff`): on `Re s = 1/2` it is at most `2|s| y/√x` and `2√x`
  (`norm_powDiff_le`, `norm_powDiff_le_sqrt`), and `|(x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s)| ≤
  6|s|² y y₁/(x√x)` (`norm_powDiff_sub_le`): the linear terms `s x^{s−1}y` cancel and the remainders are integrals of
  `v^{s−1} − x^{s−1}`. Against `|𝓜(Smooth1)(s)| ≤ B/|s|` (`MediumPNTW.MellinOfSmooth1d`), `≤ C/(ε|s|²)` and the
  bounds on `G` this gives the kernel in the three ranges of `t` (`norm_MW_kernel_le_low`, `norm_MW_kernel_le_mid`,
  `norm_MW_kernel_le_tail`; for one window `norm_MW_powDiff_le`, `norm_MW_powDiff_le_tail`).
* `norm_sum_win_sub_le`: the comparison for the smooth windows, splitting `t` at `±T₀` and `±T`.
  `norm_sum_ind_sub_W_le`, `norm_sum_sharp_sub_win_le`: the transitions of `W_k(n/X)` hold at most
  `Xε(k + 3) + 1` integers, which gives `norm_sum_Ioc_sub_le_of_bump` and, with PNT+'s bump, `norm_sum_Ioc_sub_le`.
-/

open Complex Set Real Filter MeasureTheory

local notation (name := mellintransform4) "𝓜" => mellin

namespace ShortSieveInterval

/-! ### The line `Re s = 1/2` -/

/-- The point `1/2 + it`. -/
noncomputable def cl (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I

@[simp] lemma cl_re (t : ℝ) : (cl t).re = 1 / 2 := by simp [cl]

@[simp] lemma cl_im (t : ℝ) : (cl t).im = t := by simp [cl]

lemma continuous_cl : Continuous cl := by unfold cl; fun_prop

lemma cl_ne_zero (t : ℝ) : cl t ≠ 0 := fun h ↦ by
  have := congrArg Complex.re h
  simp at this

lemma abs_le_norm_cl (t : ℝ) : |t| ≤ ‖cl t‖ := by
  have := Complex.abs_im_le_norm (cl t); rwa [cl_im] at this

lemma half_le_norm_cl (t : ℝ) : 1 / 2 ≤ ‖cl t‖ := by
  have := Complex.abs_re_le_norm (cl t); rw [cl_re] at this; linarith [le_abs_self (1 / 2 : ℝ)]

lemma norm_cl_le (t : ℝ) : ‖cl t‖ ≤ 1 / 2 + |t| := by
  unfold cl
  refine (norm_add_le _ _).trans ?_
  simp

lemma norm_cl_sq (t : ℝ) : ‖cl t‖ ^ 2 = 1 / 4 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, cl_re, cl_im]
  ring

lemma norm_cl_sub_one (t : ℝ) : ‖cl t - 1‖ = ‖cl t‖ := by
  have h1 : ‖cl t - 1‖ ^ 2 = ‖cl t‖ ^ 2 := by
    rw [norm_cl_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, cl_re, one_re, sub_im, cl_im, one_im, sub_zero]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- `1 + t² ≤ 4|1/2 + it|²`. -/
lemma one_add_sq_le (t : ℝ) : 1 + t ^ 2 ≤ 4 * ‖cl t‖ ^ 2 := by
  rw [norm_cl_sq]; nlinarith [sq_nonneg t]

/-- A continuous function bounded by `K|1/2 + it|^{−2}` is integrable. -/
lemma integrable_of_le_inv_sq {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, ‖f t‖ ≤ K * (‖cl t‖ ^ 2)⁻¹) : Integrable f := by
  have hK0 : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hK 0)
    have hp : 0 < (‖cl 0‖ ^ 2)⁻¹ := by
      have := half_le_norm_cl 0
      positivity
    exact nonneg_of_mul_nonneg_left h hp
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (4 * K)) hf.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ (hK t).trans ?_)
  have h1 := one_add_sq_le t
  have h2 : 0 < 1 + t ^ 2 := by positivity
  have h3 : 0 < ‖cl t‖ ^ 2 := by have := half_le_norm_cl t; positivity
  have h4 : (‖cl t‖ ^ 2)⁻¹ ≤ 4 * (1 + t ^ 2)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ h3 h2]
    linarith
  calc K * (‖cl t‖ ^ 2)⁻¹ ≤ K * (4 * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h4 hK0
    _ = 4 * K * (1 + t ^ 2)⁻¹ := by ring

/-- **Differences of powers.** `|a^r − b^r| ≤ |r|(a − b) b^{Re r − 1}` for `0 < b ≤ a` and `Re r ≤ 1`. -/
lemma norm_cpow_sub_cpow_le {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) {r : ℂ} (hr : r.re ≤ 1) :
    ‖(a : ℂ) ^ r - (b : ℂ) ^ r‖ ≤ ‖r‖ * (a - b) * b ^ (r.re - 1) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have h0 : (0 : ℝ) ∉ uIcc b a := by
    rw [uIcc_of_le hba]; intro h; exact absurd h.1 (not_le.2 hb)
  have hint := integral_cpow (a := b) (b := a) (r := r - 1) (Or.inr ⟨fun h ↦ hr0 (by
    linear_combination h), h0⟩)
  rw [sub_add_cancel] at hint
  have e : (a : ℂ) ^ r - (b : ℂ) ^ r = r * ∫ x : ℝ in b..a, (x : ℂ) ^ (r - 1) := by
    rw [hint]; field_simp
  rw [e, norm_mul]
  have hbound : ∀ x ∈ uIoc b a, ‖(x : ℂ) ^ (r - 1)‖ ≤ b ^ (r.re - 1) := by
    intro x hx
    rw [uIoc_of_le hba] at hx
    have hx0 : 0 < x := hb.trans hx.1
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos hb hx.1.le (by linarith)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (by linarith)] at this
  calc ‖r‖ * ‖∫ x : ℝ in b..a, (x : ℂ) ^ (r - 1)‖ ≤ ‖r‖ * (b ^ (r.re - 1) * (a - b)) := by gcongr
    _ = ‖r‖ * (a - b) * b ^ (r.re - 1) := by ring

/-! ### The averaged smoothing -/

/-- PNT+'s hypotheses on the bump `ν` of `Smooth1 ν ε`. -/
structure Bump (ν : ℝ → ℝ) : Prop where
  diff : ContDiff ℝ 1 ν
  nonneg : ∀ x > 0, 0 ≤ ν x
  supp : ν.support ⊆ Icc (1 / 2) 2
  mass : ∫ x in Ioi 0, ν x / x = 1

/-- A bump exists (PNT+'s `SmoothExistence`). -/
lemma exists_bump : ∃ ν : ℝ → ℝ, Bump ν := by
  obtain ⟨ν, hd, hn, hs, hm⟩ := SmoothExistence
  exact ⟨ν, ⟨hd.of_le (by simp), fun x _ ↦ hn x, hs, by rwa [← integral_Ici_eq_integral_Ioi]⟩⟩

variable {ν : ℝ → ℝ} {ε : ℝ}

/-- `G(s) = (1/ε) ∫_0^ε e^{−vs} dv`: one average over the dilations `u ↦ u e^v`, `0 ≤ v ≤ ε`, multiplies a Mellin
transform by `G`. -/
noncomputable def G (ε : ℝ) (s : ℂ) : ℂ := (1 / ε : ℂ) * ∫ v in (0 : ℝ)..ε, cexp (-(v * s))

/-- `|G(s)| ≤ 1` on `Re s ≥ 0`. -/
lemma norm_G_le_one (εpos : 0 < ε) {s : ℂ} (hs : 0 ≤ s.re) : ‖G ε s‖ ≤ 1 := by
  have h : ∀ v ∈ uIoc 0 ε, ‖cexp (-(v * s))‖ ≤ 1 := by
    intro v hv
    rw [uIoc_of_le εpos.le] at hv
    rw [Complex.norm_exp]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_one_iff.2 (by nlinarith [hv.1])
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const h
  rw [sub_zero, abs_of_pos εpos, one_mul] at hi
  rw [G, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos εpos]
  calc 1 / ε * ‖∫ v in (0 : ℝ)..ε, cexp (-(v * s))‖ ≤ 1 / ε * ε := by gcongr
    _ = 1 := by field_simp

/-- `|G(s)| ≤ 2/(ε|s|)` on `Re s ≥ 0`: `G(s) = (1 − e^{−εs})/(εs)`. -/
lemma norm_G_le (εpos : 0 < ε) {s : ℂ} (hs : 0 ≤ s.re) (hs0 : s ≠ 0) : ‖G ε s‖ ≤ 2 / (ε * ‖s‖) := by
  have e : ∫ v in (0 : ℝ)..ε, cexp (-(v * s)) = (cexp (-s * ε) - 1) / (-s) := by
    have := integral_exp_mul_complex (a := 0) (b := ε) (neg_ne_zero.2 hs0)
    simp only [ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [← this]
    congr 1
    funext v
    ring_nf
  have hn : ‖cexp (-s * ε)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs0
  rw [G, e, norm_mul, norm_div, norm_div, norm_neg, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos εpos]
  have h2 : ‖cexp (-s * ε) - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  calc 1 / ε * (‖cexp (-s * ε) - 1‖ / ‖s‖) ≤ 1 / ε * (2 / ‖s‖) := by gcongr
    _ = 2 / (ε * ‖s‖) := by field_simp

lemma continuous_G_cl (ε : ℝ) : Continuous fun t : ℝ ↦ G ε (cl t) := by
  unfold G
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t v : ℝ ↦ cexp (-(v * cl t))) (by unfold cl; fun_prop) 0 ε

/-- The `k`-fold average of `Smooth1 ν ε` over the dilations `u ↦ u e^v`, `0 ≤ v ≤ ε`: `W₀ = Smooth1 ν ε` and
`W_{k+1}(u) = (1/ε) ∫_0^ε W_k(u e^v) dv`. -/
noncomputable def W (ν : ℝ → ℝ) (ε : ℝ) : ℕ → ℝ → ℝ
  | 0 => Smooth1 ν ε
  | k + 1 => fun u ↦ 1 / ε * ∫ v in (0 : ℝ)..ε, W ν ε k (u * Real.exp v)

lemma W_zero : W ν ε 0 = Smooth1 ν ε := rfl

lemma W_succ (k : ℕ) (u : ℝ) :
    W ν ε (k + 1) u = 1 / ε * ∫ v in (0 : ℝ)..ε, W ν ε k (u * Real.exp v) := rfl

/-- `|W_k(u)| ≤ 1` for `u > 0`. -/
lemma abs_W_le_one (hν : Bump ν) (εpos : 0 < ε) (k : ℕ) {u : ℝ} (hu : 0 < u) : |W ν ε k u| ≤ 1 := by
  induction k generalizing u with
  | zero =>
    rw [W_zero, abs_le]
    exact ⟨by linarith [Smooth1Nonneg hν.nonneg hu εpos], Smooth1LeOne hν.nonneg hν.mass εpos hu⟩
  | succ k ih =>
    rw [W_succ]
    have h : ∀ v ∈ uIoc 0 ε, ‖W ν ε k (u * Real.exp v)‖ ≤ 1 := fun v _ ↦ by
      rw [Real.norm_eq_abs]; exact ih (mul_pos hu (Real.exp_pos v))
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const h
    rw [sub_zero, abs_of_pos εpos, one_mul, Real.norm_eq_abs] at hi
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / ε)]
    calc 1 / ε * |∫ v in (0 : ℝ)..ε, W ν ε k (u * Real.exp v)| ≤ 1 / ε * ε := by gcongr
      _ = 1 := by field_simp

/-- `W_k(u) = 1` for `0 < u ≤ (1 − ε log 2)e^{−kε}`. -/
lemma W_eq_one (hν : Bump ν) (εpos : 0 < ε) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (h : u ≤ (1 - Real.log 2 * ε) * Real.exp (-(k * ε))) : W ν ε k u = 1 := by
  obtain ⟨c₁, -, hc₁, hbelow⟩ := Smooth1Properties_below hν.supp hν.mass
  induction k generalizing u with
  | zero =>
    rw [W_zero]
    exact hbelow ε u εpos hu (by rw [hc₁]; simpa using h)
  | succ k ih =>
    rw [W_succ]
    have hc : ∀ v ∈ uIcc 0 ε, W ν ε k (u * Real.exp v) = 1 := by
      intro v hv
      rw [uIcc_of_le εpos.le] at hv
      refine ih (mul_pos hu (Real.exp_pos v)) ?_
      calc u * Real.exp v ≤ (1 - Real.log 2 * ε) * Real.exp (-((k + 1 : ℕ) * ε)) * Real.exp ε := by
            gcongr
            · exact hu.le.trans h
            · exact hv.2
        _ = (1 - Real.log 2 * ε) * Real.exp (-(k * ε)) := by
            rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    field_simp

/-- `W_k(u) = 0` for `u ≥ 1 + 2ε log 2`. -/
lemma W_eq_zero (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {u : ℝ}
    (h : 1 + 2 * Real.log 2 * ε ≤ u) : W ν ε k u = 0 := by
  obtain ⟨c₂, -, hc₂, habove⟩ := Smooth1Properties_above hν.supp
  induction k generalizing u with
  | zero =>
    rw [W_zero]
    exact habove ε u ⟨εpos, ε_lt_one⟩ (by rw [hc₂]; exact h)
  | succ k ih =>
    rw [W_succ]
    have hu : 0 ≤ u := by
      have : 0 ≤ 2 * Real.log 2 * ε := by positivity
      linarith
    have hc : ∀ v ∈ uIcc 0 ε, W ν ε k (u * Real.exp v) = 0 := by
      intro v hv
      rw [uIcc_of_le εpos.le] at hv
      refine ih (h.trans ?_)
      calc u = u * 1 := (mul_one u).symm
        _ ≤ u * Real.exp v := by gcongr; exact Real.one_le_exp hv.1
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_zero, mul_zero]

/-! ### Mellin inversion on the line `Re s = 1/2` -/

lemma continuous_mellin_cl (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    Continuous fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t) :=
  SmoothPerron.continuous_mellin_line hν.diff hν.nonneg hν.supp hν.mass εpos ε_lt_one (σ := 1 / 2)
    (by norm_num)

/-- `𝓜(W_k)(1/2 + it) = 𝓜(Smooth1 ν ε)(1/2 + it) G(1/2 + it)^k`. -/
noncomputable def MW (ν : ℝ → ℝ) (ε : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t) * G ε (cl t) ^ k

lemma norm_MW_le (εpos : 0 < ε) (k : ℕ) (t : ℝ) :
    ‖MW ν ε k t‖ ≤ ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ := by
  rw [MW, norm_mul, norm_pow]
  have h := norm_G_le_one εpos (s := cl t) (by rw [cl_re]; norm_num)
  calc ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ * ‖G ε (cl t)‖ ^ k
      ≤ ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) h
    _ = _ := mul_one _

lemma continuous_MW (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) : Continuous (MW ν ε k) :=
  (continuous_mellin_cl hν εpos ε_lt_one).mul ((continuous_G_cl ε).pow k)

lemma integrable_MW (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) : Integrable (MW ν ε k) := by
  obtain ⟨C, -, hC⟩ := MellinOfSmooth1b hν.diff hν.supp
  refine integrable_of_le_inv_sq (continuous_MW hν εpos ε_lt_one k) (K := C / ε) fun t ↦ ?_
  refine (norm_MW_le εpos k t).trans ?_
  have := hC (1 / 2) (by norm_num) (cl t) (by rw [cl_re]) (by rw [cl_re]; norm_num) ε εpos ε_lt_one
  calc _ ≤ C * (ε * ‖cl t‖ ^ 2)⁻¹ := this
    _ = C / ε * (‖cl t‖ ^ 2)⁻¹ := by rw [mul_inv]; ring

/-- A continuous function bounded by a multiple of `|𝓜(W_k)|` on the line is integrable. -/
lemma integrable_of_le_MW (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {f : ℝ → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C * ‖MW ν ε k t‖) : Integrable f :=
  Integrable.mono' ((integrable_MW hν εpos ε_lt_one k).norm.const_mul C) hf.aestronglyMeasurable
    (Eventually.of_forall hC)

/-- `(u e^v)^{−s} = u^{−s} e^{−vs}`. -/
lemma cpow_mul_exp {u : ℝ} (hu : 0 < u) (v : ℝ) (s : ℂ) :
    (((u * Real.exp v : ℝ)) : ℂ) ^ (-s) = (u : ℂ) ^ (-s) * cexp (-(v * s)) := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hu.le (Real.exp_pos v).le]
  congr 1
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos v).ne'), ← ofReal_log (Real.exp_pos v).le,
    Real.log_exp]
  congr 1
  ring

/-- **Mellin inversion for the averaged smoothing.** For `u > 0`,
`W_k(u) = (1/2π) ∫ u^{−1/2−it} 𝓜(Smooth1 ν ε)(1/2 + it) G(1/2 + it)^k dt`. -/
theorem W_eq_integral (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (W ν ε k u : ℂ) = (1 / (2 * π) : ℝ) • ∫ t : ℝ, (u : ℂ) ^ (-cl t) * MW ν ε k t := by
  induction k generalizing u with
  | zero =>
    have hconv : MellinConvergent (fun x ↦ (Smooth1 ν ε x : ℂ)) ((1 / 2 : ℝ) : ℂ) :=
      Smooth1MellinConvergent hν.diff hν.supp ⟨εpos, ε_lt_one⟩ hν.nonneg hν.mass (by simp)
    have hvi : VerticalIntegrable (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ))) (1 / 2) := by
      have h : Integrable fun t ↦ MW ν ε 0 t := integrable_MW hν εpos ε_lt_one 0
      simp only [MW, pow_zero, mul_one] at h
      exact h
    have hcont : ContinuousAt (fun x ↦ (Smooth1 ν ε x : ℂ)) u :=
      (Smooth1ContinuousAt hν.diff hν.nonneg hν.supp εpos hu).ofReal
    have h := mellinInv_mellin_eq (1 / 2) _ hu hconv hvi hcont
    rw [W_zero, ← h, mellinInv]
    simp only [MW, pow_zero, mul_one, smul_eq_mul]
    rfl
  | succ k ih =>
    set F : ℝ → ℝ → ℂ := fun v t ↦ (u : ℂ) ^ (-cl t) * cexp (-(v * cl t)) * MW ν ε k t with hF
    have key : ∀ v : ℝ, (W ν ε k (u * Real.exp v) : ℂ) = (1 / (2 * π) : ℝ) • ∫ t : ℝ, F v t := by
      intro v
      rw [ih (mul_pos hu (Real.exp_pos v))]
      congr 2
      funext t
      rw [hF, cpow_mul_exp hu]
    have hFc : Continuous (Function.uncurry F) := by
      have h1 : Continuous fun p : ℝ × ℝ ↦ (u : ℂ) ^ (-cl p.2) :=
        Continuous.const_cpow (continuous_cl.comp continuous_snd).neg (Or.inl (ofReal_ne_zero.2 hu.ne'))
      have h2 : Continuous fun p : ℝ × ℝ ↦ cexp (-((p.1 : ℂ) * cl p.2)) := by
        have := continuous_cl
        fun_prop
      have h3 : Continuous fun p : ℝ × ℝ ↦ MW ν ε k p.2 :=
        (continuous_MW hν εpos ε_lt_one k).comp continuous_snd
      exact (h1.mul h2).mul h3
    have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 ε)).prod volume) := by
      have h1 : Integrable (fun v : ℝ ↦ u ^ (-(1 / 2 : ℝ)) * Real.exp (-(v * (1 / 2))))
          (volume.restrict (Ioc 0 ε)) := (by fun_prop : Continuous fun v : ℝ ↦
            u ^ (-(1 / 2 : ℝ)) * Real.exp (-(v * (1 / 2)))).integrableOn_Ioc
      have h2 : Integrable (fun t ↦ ‖MW ν ε k t‖) := (integrable_MW hν εpos ε_lt_one k).norm
      refine Integrable.mono' (h1.mul_prod h2) hFc.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
      refine le_of_eq ?_
      simp only [Function.uncurry, hF, norm_mul, norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
      simp
    have hG : ∀ t : ℝ, ∫ v in (0 : ℝ)..ε, F v t = (u : ℂ) ^ (-cl t) * MW ν ε k t * (ε * G ε (cl t)) := by
      intro t
      have e : ∀ v : ℝ, F v t = (u : ℂ) ^ (-cl t) * MW ν ε k t * cexp (-(v * cl t)) := fun v ↦ by
        rw [hF]; ring
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul, G]
      have : (ε : ℂ) ≠ 0 := ofReal_ne_zero.2 εpos.ne'
      field_simp
    calc (W ν ε (k + 1) u : ℂ) = (1 / ε : ℂ) * ∫ v in (0 : ℝ)..ε, (W ν ε k (u * Real.exp v) : ℂ) := by
          rw [W_succ, intervalIntegral.integral_ofReal]; push_cast; ring
      _ = (1 / ε : ℂ) * ∫ v in (0 : ℝ)..ε, (1 / (2 * π) : ℝ) • ∫ t : ℝ, F v t := by
          congr 1
          exact intervalIntegral.integral_congr fun v _ ↦ key v
      _ = (1 / ε : ℂ) * ((1 / (2 * π) : ℝ) • ∫ t : ℝ, ∫ v in (0 : ℝ)..ε, F v t) := by
          rw [intervalIntegral.integral_smul, intervalIntegral.integral_of_le εpos.le]
          congr 2
          rw [integral_integral_swap hFint]
          congr 1
          funext t
          rw [intervalIntegral.integral_of_le εpos.le]
      _ = (1 / (2 * π) : ℝ) • ∫ t : ℝ, (u : ℂ) ^ (-cl t) * MW ν ε (k + 1) t := by
          rw [mul_smul_comm, ← integral_const_mul]
          congr 2
          funext t
          rw [hG t, MW, MW, pow_succ]
          have : (ε : ℂ) ≠ 0 := ofReal_ne_zero.2 εpos.ne'
          field_simp

/-! ### Dirichlet polynomials on the line -/

/-- `n^{−(1/2+it)} = n^{−1/2} e^{−it log n}`. -/
lemma natCast_cpow_neg_cl {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-cl t) = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(I * ((t * Real.log n : ℝ) : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
  rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [cl]
  push_cast
  ring

/-- The coefficients `a_n n^{−1/2}`, so that `dp S (coef a) t = Σ_{n∈S} a_n n^{−1/2−it}` (`dp_coef`). -/
noncomputable def coef (a : ℕ → ℂ) (n : ℕ) : ℂ := a n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

lemma dp_coef {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (t : ℝ) :
    DirMean.dp S (coef a) t = ∑ n ∈ S, a n * (n : ℂ) ^ (-cl t) := by
  unfold DirMean.dp coef
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [natCast_cpow_neg_cl (hS n hn)]
  ring

/-- `|Σ_{j∈S} c_j j^{−it}| ≤ Σ_{j∈S} |c_j|`. -/
lemma norm_dp_le (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ‖DirMean.dp S c t‖ ≤ ∑ n ∈ S, ‖c n‖ := by
  unfold DirMean.dp
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
  rw [norm_mul, DirMean.norm_exp_neg_I_mul, mul_one]

/-- `∫_a^b |Σ_{j∈S} c_j j^{−it}| dt ≤ (b − a) Σ_{j∈S} |c_j|`. -/
lemma integral_norm_dp_le (S : Finset ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖DirMean.dp S c t‖ ≤ (b - a) * ∑ n ∈ S, ‖c n‖ := by
  have h := intervalIntegral.integral_mono_on hab
    ((DirMean.continuous_dp S c).norm.intervalIntegrable (μ := volume) a b)
    intervalIntegrable_const fun t _ ↦ norm_dp_le S c t
  rwa [intervalIntegral.integral_const, smul_eq_mul] at h

/-- `(n/X)^{−s} = n^{−s} X^s`. -/
lemma div_cpow_neg {n X : ℝ} (hn : 0 ≤ n) (hX : 0 < X) (s : ℂ) :
    (((n / X : ℝ)) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) * (X : ℂ) ^ s := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hn (inv_nonneg.2 hX.le), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hX.le]; exact Real.pi_ne_zero.symm)]
  congr 1
  rw [cpow_neg, inv_inv]

/-- The integrand `A(1/2 + it) 𝓜(W_k)(1/2 + it) X^{1/2+it}` is integrable. -/
lemma integrable_dp_MW (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) (S : Finset ℕ)
    (c : ℕ → ℂ) {X : ℝ} (hX : 0 < X) :
    Integrable fun t : ℝ ↦ DirMean.dp S c t * MW ν ε k t * (X : ℂ) ^ cl t := by
  refine integrable_of_le_MW hν εpos ε_lt_one k (C := (∑ n ∈ S, ‖c n‖) * X ^ (1 / 2 : ℝ)) ?_ fun t ↦ ?_
  · exact ((DirMean.continuous_dp S c).mul (continuous_MW hν εpos ε_lt_one k)).mul
      (Continuous.const_cpow continuous_cl (Or.inl (ofReal_ne_zero.2 hX.ne')))
  · rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hX, cl_re]
    have := norm_dp_le S c t
    calc ‖DirMean.dp S c t‖ * ‖MW ν ε k t‖ * X ^ (1 / 2 : ℝ)
        ≤ (∑ n ∈ S, ‖c n‖) * ‖MW ν ε k t‖ * X ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := by ring

/-- **Mellin inversion for a Dirichlet polynomial on `Re s = 1/2`.** For a finite set `S` of positive integers
and `X > 0`, `Σ_{n∈S} a_n W_k(n/X) = (1/2π) ∫ A(1/2 + it) 𝓜(Smooth1 ν ε)(1/2 + it) G(1/2 + it)^k X^{1/2+it} dt`,
with `A(1/2 + it) = Σ_{n∈S} a_n n^{−1/2−it} = dp S (coef a) t`. -/
theorem sum_W_eq (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) {X : ℝ} (hX : 0 < X) :
    ∑ n ∈ S, a n * (W ν ε k (n / X) : ℂ) =
      (1 / (2 * π) : ℝ) • ∫ t : ℝ, DirMean.dp S (coef a) t * MW ν ε k t * (X : ℂ) ^ cl t := by
  have hterm : ∀ n ∈ S, a n * (W ν ε k (n / X) : ℂ) =
      (1 / (2 * π) : ℝ) • ∫ t : ℝ, a n * (n : ℂ) ^ (-cl t) * MW ν ε k t * (X : ℂ) ^ cl t := by
    intro n hn
    have hnX : 0 < (n : ℝ) / X := div_pos (by exact_mod_cast hS n hn) hX
    rw [W_eq_integral hν εpos ε_lt_one k hnX, mul_smul_comm, ← integral_const_mul]
    congr 2
    funext t
    rw [div_cpow_neg (Nat.cast_nonneg n) hX]
    push_cast
    ring
  have hint : ∀ n ∈ S, Integrable fun t : ℝ ↦ a n * (n : ℂ) ^ (-cl t) * MW ν ε k t * (X : ℂ) ^ cl t := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
    have hnr : (0 : ℝ) < n := by exact_mod_cast hS n hn
    refine integrable_of_le_MW hν εpos ε_lt_one k (C := ‖a n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * X ^ (1 / 2 : ℝ))
      ?_ fun t ↦ ?_
    · exact ((continuous_const.mul (Continuous.const_cpow continuous_cl.neg (Or.inl hn0))).mul
        (continuous_MW hν εpos ε_lt_one k)).mul
        (Continuous.const_cpow continuous_cl (Or.inl (ofReal_ne_zero.2 hX.ne')))
    · have e : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
      rw [norm_mul, norm_mul, norm_mul, e, norm_cpow_eq_rpow_re_of_pos hnr, norm_cpow_eq_rpow_re_of_pos hX]
      simp only [neg_re, cl_re]
      exact le_of_eq (by ring)
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← integral_finsetSum _ hint]
  congr 2
  funext t
  rw [dp_coef hS a t, Finset.sum_mul, Finset.sum_mul]

/-! ### The kernels -/

/-- `x^s − (x − y)^s`: the window `(x − y, x]` multiplies the Mellin transform by it. -/
noncomputable def powDiff (x y : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s - ((x - y : ℝ) : ℂ) ^ s

/-- `b^{−1/2} ≤ 2/√x` for `b ≥ x/4`. -/
lemma rpow_neg_half_le {x b : ℝ} (hx : 0 < x) (hb : x / 4 ≤ b) : b ^ (-(1 / 2 : ℝ)) ≤ 2 / √x := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have h : √x / 2 ≤ √b := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [div_pow, Real.sq_sqrt hx.le]
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.sqrt_pos.2 hb0) hsx]
  linarith

/-- `b^{−3/2} ≤ 3/(x√x)` for `b ≥ x/2`. -/
lemma rpow_neg_three_halves_le {x b : ℝ} (hx : 0 < x) (hb : x / 2 ≤ b) :
    b ^ (-(3 / 2 : ℝ)) ≤ 3 / (x * √x) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have e : b ^ (3 / 2 : ℝ) = b * √b := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have h : 2 * √x / 3 ≤ √b := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [div_pow, mul_pow, Real.sq_sqrt hx.le]
    linarith
  have h2 : x * √x / 3 ≤ b * √b := by
    calc x * √x / 3 = x / 2 * (2 * √x / 3) := by ring
      _ ≤ b * √b := by gcongr
  rw [Real.rpow_neg hb0.le, e, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- `|x^s − (x − y)^s| ≤ 2√x` on `Re s = 1/2`, for `0 ≤ y < x`. -/
lemma norm_powDiff_le_sqrt {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y < x) (t : ℝ) :
    ‖powDiff x y (cl t)‖ ≤ 2 * √x := by
  have hxy : 0 < x - y := by linarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos hxy, cl_re, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  have : √(x - y) ≤ √x := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `|x^s − (x − y)^s| ≤ 2|s| y/√x` on `Re s = 1/2`, for `0 ≤ y ≤ x/2`. -/
lemma norm_powDiff_le {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2) (t : ℝ) :
    ‖powDiff x y (cl t)‖ ≤ 2 * ‖cl t‖ * y / √x := by
  have hxy : 0 < x - y := by linarith
  have h := norm_cpow_sub_cpow_le hxy (by linarith : x - y ≤ x) (r := cl t) (by rw [cl_re]; norm_num)
  rw [cl_re, show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, show x - (x - y) = y by ring] at h
  have h2 := rpow_neg_half_le hx (b := x - y) (by linarith)
  calc ‖powDiff x y (cl t)‖ ≤ ‖cl t‖ * y * (x - y) ^ (-(1 / 2 : ℝ)) := h
    _ ≤ ‖cl t‖ * y * (2 / √x) := by gcongr
    _ = 2 * ‖cl t‖ * y / √x := by ring

/-- The second order term: `|x^s − (x − u)^s − s x^{s−1} u| ≤ |s|² u² · 3/(x√x)` on `Re s = 1/2`, for
`0 ≤ u ≤ x/2`. -/
lemma norm_powDiff_sub_lin_le {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) (hux : u ≤ x / 2) (t : ℝ) :
    ‖powDiff x u (cl t) - cl t * (x : ℂ) ^ (cl t - 1) * u‖ ≤ ‖cl t‖ ^ 2 * u ^ 2 * (3 / (x * √x)) := by
  have hxu : 0 < x - u := by linarith
  have hre : -1 < (cl t - 1).re := by simp only [sub_re, cl_re, one_re]; norm_num
  have hint := integral_cpow (a := x - u) (b := x) (r := cl t - 1) (Or.inl hre)
  rw [sub_add_cancel] at hint
  have hs0 : cl t ≠ 0 := cl_ne_zero t
  have e1 : powDiff x u (cl t) = cl t * ∫ v : ℝ in (x - u)..x, (v : ℂ) ^ (cl t - 1) := by
    rw [hint, powDiff]; field_simp
  have e2 : cl t * (x : ℂ) ^ (cl t - 1) * u = cl t * ∫ _ : ℝ in (x - u)..x, (x : ℂ) ^ (cl t - 1) := by
    rw [intervalIntegral.integral_const, show x - (x - u) = u by ring, Complex.real_smul]
    ring
  have hi1 : IntervalIntegrable (fun v : ℝ ↦ (v : ℂ) ^ (cl t - 1)) volume (x - u) x :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr (by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]))
  have e3 : powDiff x u (cl t) - cl t * (x : ℂ) ^ (cl t - 1) * u =
      cl t * ∫ v : ℝ in (x - u)..x, ((v : ℂ) ^ (cl t - 1) - (x : ℂ) ^ (cl t - 1)) := by
    rw [e1, e2, intervalIntegral.integral_sub hi1 intervalIntegrable_const, mul_sub]
  rw [e3, norm_mul]
  have hb : ∀ v ∈ uIoc (x - u) x,
      ‖(v : ℂ) ^ (cl t - 1) - (x : ℂ) ^ (cl t - 1)‖ ≤ ‖cl t‖ * u * (3 / (x * √x)) := by
    intro v hv
    rw [uIoc_of_le (by linarith)] at hv
    have hv0 : 0 < v := by linarith [hv.1]
    rw [norm_sub_rev]
    have h := norm_cpow_sub_cpow_le hv0 hv.2 (r := cl t - 1) (by simp only [sub_re, cl_re, one_re]; norm_num)
    have hre' : (cl t - 1).re - 1 = -(3 / 2 : ℝ) := by simp only [sub_re, cl_re, one_re]; norm_num
    rw [hre', norm_cl_sub_one] at h
    have h3 := rpow_neg_three_halves_le hx (b := v) (by linarith [hv.1])
    calc ‖(x : ℂ) ^ (cl t - 1) - (v : ℂ) ^ (cl t - 1)‖ ≤ ‖cl t‖ * (x - v) * v ^ (-(3 / 2 : ℝ)) := h
      _ ≤ ‖cl t‖ * u * (3 / (x * √x)) := by
          gcongr
          linarith [hv.1]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show x - (x - u) = u by ring, abs_of_nonneg hu] at this
  calc ‖cl t‖ * ‖∫ v : ℝ in (x - u)..x, ((v : ℂ) ^ (cl t - 1) - (x : ℂ) ^ (cl t - 1))‖
      ≤ ‖cl t‖ * (‖cl t‖ * u * (3 / (x * √x)) * u) := by gcongr
    _ = ‖cl t‖ ^ 2 * u ^ 2 * (3 / (x * √x)) := by ring

/-- **The kernel near `t = 0`.** For `0 < y ≤ y₁ ≤ x/2`, on `Re s = 1/2`,
`|(x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s)| ≤ 6|s|² y y₁/(x√x)`. -/
lemma norm_powDiff_sub_le {x y y₁ : ℝ} (hx : 0 < x) (hy : 0 < y) (hyy : y ≤ y₁) (hy₁ : y₁ ≤ x / 2) (t : ℝ) :
    ‖powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t)‖ ≤ 6 * ‖cl t‖ ^ 2 * (y * y₁ / (x * √x)) := by
  have hy₁0 : 0 < y₁ := hy.trans_le hyy
  have h1 := norm_powDiff_sub_lin_le hx hy.le (hyy.trans hy₁) t
  have h2 := norm_powDiff_sub_lin_le hx hy₁0.le hy₁ t
  set L : ℂ := cl t * (x : ℂ) ^ (cl t - 1) with hL
  have e : powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t) =
      (powDiff x y (cl t) - L * y) - (y / y₁ : ℝ) * (powDiff x y₁ (cl t) - L * y₁) := by
    have : (y₁ : ℂ) ≠ 0 := ofReal_ne_zero.2 hy₁0.ne'
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hy hy₁0)]
  have hK : 0 ≤ 3 / (x * √x) := by positivity
  calc ‖powDiff x y (cl t) - L * y‖ + y / y₁ * ‖powDiff x y₁ (cl t) - L * y₁‖
      ≤ ‖cl t‖ ^ 2 * y ^ 2 * (3 / (x * √x)) + y / y₁ * (‖cl t‖ ^ 2 * y₁ ^ 2 * (3 / (x * √x))) := by
        gcongr
    _ = 3 * ‖cl t‖ ^ 2 * (y * y + y * y₁) / (x * √x) := by field_simp
    _ ≤ 3 * ‖cl t‖ ^ 2 * (y * y₁ + y * y₁) / (x * √x) := by gcongr
    _ = 6 * ‖cl t‖ ^ 2 * (y * y₁ / (x * √x)) := by ring

/-! ### The kernel against the smoothing -/

section kernel

variable {Bν Cν : ℝ}

lemma nonneg_of_mellin_le (hB : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Bν * ‖cl t‖⁻¹) :
    0 ≤ Bν := by
  have h := (norm_nonneg _).trans (hB 0)
  have hp : 0 < ‖cl 0‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (cl_ne_zero 0))
  exact nonneg_of_mul_nonneg_left h hp

lemma nonneg_of_mellin_le_sq (εpos : 0 < ε)
    (hC : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹) : 0 ≤ Cν := by
  have h := (norm_nonneg _).trans (hC 0)
  have hp : 0 < (ε * ‖cl 0‖ ^ 2)⁻¹ := by
    have := norm_pos_iff.2 (cl_ne_zero 0)
    positivity
  exact nonneg_of_mul_nonneg_left h hp

/-- `|m(p − cq)| ≤ |mp| + c|mq|` for `c ≥ 0`. -/
lemma norm_mul_sub_le (m p q : ℂ) {c : ℝ} (hc : 0 ≤ c) : ‖m * (p - (c : ℂ) * q)‖ ≤ ‖m * p‖ + c * ‖m * q‖ := by
  rw [mul_sub, ← mul_assoc, mul_comm m (c : ℂ), mul_assoc]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul (c : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

/-- **The kernel of one window, for all `t`.** If `|𝓜(Smooth1 ν ε)(s)| ≤ B/|s|` on `Re s = 1/2`, then there
`|𝓜(W_k)(s)(x^s − (x − y)^s)| ≤ 2B y/√x`, for `0 ≤ y ≤ x/2`. -/
lemma norm_MW_powDiff_le (hB : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Bν * ‖cl t‖⁻¹) (εpos : 0 < ε)
    (k : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2) (t : ℝ) :
    ‖MW ν ε k t * powDiff x y (cl t)‖ ≤ 2 * Bν * y / √x := by
  have hB0 := nonneg_of_mellin_le hB
  have hc : 0 < ‖cl t‖ := norm_pos_iff.2 (cl_ne_zero t)
  have hM := (norm_MW_le εpos k t).trans (hB t)
  have h1 := norm_powDiff_le hx hy hyx t
  rw [norm_mul]
  calc ‖MW ν ε k t‖ * ‖powDiff x y (cl t)‖ ≤ Bν * ‖cl t‖⁻¹ * (2 * ‖cl t‖ * y / √x) := by gcongr
    _ = 2 * Bν * y / √x := by field_simp

/-- **The tail of `𝓜(W_k)`.** If `|𝓜(Smooth1 ν ε)(s)| ≤ C/(ε|s|²)` on `Re s = 1/2`, then for `0 < T ≤ |t|`,
`|𝓜(W_k)(1/2 + it)| ≤ 4(C/ε)(2/(εT))^k (1 + t²)^{−1}`: each average gains `|G(s)| ≤ 2/(ε|s|)`. -/
lemma norm_MW_le_tail (hC : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹)
    (εpos : 0 < ε) (k : ℕ) {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : T ≤ |t|) :
    ‖MW ν ε k t‖ ≤ 4 * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ := by
  have hc : 0 < ‖cl t‖ := norm_pos_iff.2 (cl_ne_zero t)
  have hTc : T ≤ ‖cl t‖ := ht.trans (abs_le_norm_cl t)
  have hC0 := nonneg_of_mellin_le_sq εpos hC
  have hG : ‖G ε (cl t)‖ ≤ 2 / (ε * T) := by
    refine (norm_G_le εpos (by rw [cl_re]; norm_num) (cl_ne_zero t)).trans ?_
    gcongr
  have hsq : (ε * ‖cl t‖ ^ 2)⁻¹ ≤ 4 / ε * (1 + t ^ 2)⁻¹ := by
    have h1 := one_add_sq_le t
    have h2 : 0 < 1 + t ^ 2 := by positivity
    rw [show 4 / ε * (1 + t ^ 2)⁻¹ = 4 / (ε * (1 + t ^ 2)) by field_simp, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [MW, norm_mul, norm_pow]
  calc ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ * ‖G ε (cl t)‖ ^ k
      ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹ * (2 / (ε * T)) ^ k :=
        mul_le_mul (hC t) (pow_le_pow_left₀ (norm_nonneg _) hG k) (by positivity) (by positivity)
    _ ≤ Cν * (4 / ε * (1 + t ^ 2)⁻¹) * (2 / (ε * T)) ^ k := by gcongr
    _ = 4 * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ := by ring

/-- **The kernel of one window, in the tail.** If `|𝓜(Smooth1 ν ε)(s)| ≤ C/(ε|s|²)` on `Re s = 1/2`, then for
`0 ≤ y < x` and `0 < T ≤ |t|`, `|𝓜(W_k)(s)(x^s − (x − y)^s)| ≤ 8√x (C/ε)(2/(εT))^k (1 + t²)^{−1}`. -/
lemma norm_MW_powDiff_le_tail
    (hC : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹) (εpos : 0 < ε) (k : ℕ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y < x) {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : T ≤ |t|) :
    ‖MW ν ε k t * powDiff x y (cl t)‖ ≤ 8 * √x * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ := by
  have hC0 := nonneg_of_mellin_le_sq εpos hC
  rw [norm_mul]
  calc ‖MW ν ε k t‖ * ‖powDiff x y (cl t)‖
      ≤ 4 * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ * (2 * √x) :=
        mul_le_mul (norm_MW_le_tail hC εpos k hT ht) (norm_powDiff_le_sqrt hx hy hyx t) (norm_nonneg _)
          (by positivity)
    _ = 8 * √x * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ := by ring

/-- The middle range: `|𝓜(W_k)(s)((x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s))| ≤ 4B y/√x`. -/
lemma norm_MW_kernel_le_mid (hB : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Bν * ‖cl t‖⁻¹)
    (εpos : 0 < ε) (k : ℕ) {x y y₁ : ℝ} (hx : 0 < x) (hy : 0 < y) (hyy : y ≤ y₁) (hy₁ : y₁ ≤ x / 2) (t : ℝ) :
    ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤ 4 * Bν * y / √x := by
  have hy₁0 : 0 < y₁ := hy.trans_le hyy
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have h1 := norm_MW_powDiff_le hB εpos k hx hy.le (hyy.trans hy₁) t
  have h2 := norm_MW_powDiff_le hB εpos k hx hy₁0.le hy₁ t
  refine (norm_mul_sub_le _ _ _ (div_pos hy hy₁0).le).trans ?_
  calc ‖MW ν ε k t * powDiff x y (cl t)‖ + y / y₁ * ‖MW ν ε k t * powDiff x y₁ (cl t)‖
      ≤ 2 * Bν * y / √x + y / y₁ * (2 * Bν * y₁ / √x) := by gcongr
    _ = 4 * Bν * y / √x := by field_simp; ring

/-- Near `t = 0`: `|𝓜(W_k)(s)((x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s))| ≤ 6B(1/2 + |t|) y y₁/(x√x)`. -/
lemma norm_MW_kernel_le_low (hB : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Bν * ‖cl t‖⁻¹)
    (εpos : 0 < ε) (k : ℕ) {x y y₁ : ℝ} (hx : 0 < x) (hy : 0 < y) (hyy : y ≤ y₁) (hy₁ : y₁ ≤ x / 2) (t : ℝ) :
    ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤
      6 * Bν * (1 / 2 + |t|) * (y * y₁ / (x * √x)) := by
  have hB0 := nonneg_of_mellin_le hB
  have hc : 0 < ‖cl t‖ := norm_pos_iff.2 (cl_ne_zero t)
  have hM := (norm_MW_le εpos k t).trans (hB t)
  have hD := norm_powDiff_sub_le hx hy hyy hy₁ t
  have hq : 0 ≤ y * y₁ / (x * √x) := by
    have : 0 < y₁ := hy.trans_le hyy
    positivity
  rw [norm_mul]
  calc ‖MW ν ε k t‖ * ‖powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t)‖
      ≤ Bν * ‖cl t‖⁻¹ * (6 * ‖cl t‖ ^ 2 * (y * y₁ / (x * √x))) := by gcongr
    _ = 6 * Bν * ‖cl t‖ * (y * y₁ / (x * √x)) := by field_simp
    _ ≤ 6 * Bν * (1 / 2 + |t|) * (y * y₁ / (x * √x)) := by gcongr; exact norm_cl_le t

/-- The tail: for `0 < T ≤ |t|`,
`|𝓜(W_k)(s)((x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s))| ≤ 16√x (C/ε)(2/(εT))^k (1 + t²)^{−1}`. -/
lemma norm_MW_kernel_le_tail
    (hC : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹)
    (εpos : 0 < ε) (k : ℕ) {x y y₁ : ℝ} (hx : 0 < x) (hy : 0 < y) (hyy : y ≤ y₁) (hy₁ : y₁ ≤ x / 2) {T : ℝ}
    (hT : 0 < T) {t : ℝ} (ht : T ≤ |t|) :
    ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤
      16 * √x * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹ := by
  have hy₁0 : 0 < y₁ := hy.trans_le hyy
  have h1 := norm_MW_powDiff_le_tail hC εpos k hx hy.le (by linarith) hT ht
  have h2 := norm_MW_powDiff_le_tail hC εpos k hx hy₁0.le (by linarith) hT ht
  have h3 : y / y₁ ≤ 1 := (div_le_one hy₁0).2 hyy
  have h5 : y / y₁ * ‖MW ν ε k t * powDiff x y₁ (cl t)‖ ≤
      1 * (8 * √x * Cν / ε * (2 / (ε * T)) ^ k * (1 + t ^ 2)⁻¹) :=
    mul_le_mul h3 h2 (norm_nonneg _) zero_le_one
  refine (norm_mul_sub_le _ _ _ (div_pos hy hy₁0).le).trans ((add_le_add h1 h5).trans (le_of_eq ?_))
  ring

end kernel

/-! ### The smooth windows -/

/-- The smooth window of `(x − y, x]`: `w(n) = W_k(n/x) − W_k(n/(x − y))`. -/
noncomputable def win (ν : ℝ → ℝ) (ε : ℝ) (k : ℕ) (x y : ℝ) (n : ℕ) : ℝ :=
  W ν ε k (n / x) - W ν ε k (n / (x - y))

/-- **The two windows as one integral.** For `y, y₁ < x`, with `s = 1/2 + it`,
`Σ a_n w_y(n) − (y/y₁) Σ a_n w_{y₁}(n) = (1/2π) ∫ A(s) 𝓜(W_k)(s) ((x^s − (x − y)^s) − (y/y₁)(x^s − (x − y₁)^s)) dt`.
-/
theorem sum_win_sub_eq (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) {x y y₁ : ℝ} (hx : 0 < x) (hyx : y < x) (hy₁x : y₁ < x) :
    ∑ n ∈ S, a n * (win ν ε k x y n : ℂ) - (y / y₁ : ℝ) * ∑ n ∈ S, a n * (win ν ε k x y₁ n : ℂ) =
      (1 / (2 * π) : ℝ) • ∫ t : ℝ, DirMean.dp S (coef a) t * MW ν ε k t *
        (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t)) := by
  have hxy : 0 < x - y := by linarith
  have hxy₁ : 0 < x - y₁ := by linarith
  have hw : ∀ z : ℝ, ∑ n ∈ S, a n * (win ν ε k x z n : ℂ) =
      ∑ n ∈ S, a n * (W ν ε k (n / x) : ℂ) - ∑ n ∈ S, a n * (W ν ε k (n / (x - z)) : ℂ) := by
    intro z
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [win]
    push_cast
    ring
  have hi : ∀ X : ℝ, 0 < X →
      Integrable fun t : ℝ ↦ DirMean.dp S (coef a) t * MW ν ε k t * (X : ℂ) ^ cl t :=
    fun X hX ↦ integrable_dp_MW hν εpos ε_lt_one k S (coef a) hX
  rw [hw, hw, sum_W_eq hν εpos ε_lt_one k hS a hx, sum_W_eq hν εpos ε_lt_one k hS a hxy,
    sum_W_eq hν εpos ε_lt_one k hS a hxy₁]
  have e : (fun t : ℝ ↦ DirMean.dp S (coef a) t * MW ν ε k t *
      (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))) = fun t ↦
      (DirMean.dp S (coef a) t * MW ν ε k t * (x : ℂ) ^ cl t -
        DirMean.dp S (coef a) t * MW ν ε k t * ((x - y : ℝ) : ℂ) ^ cl t) -
      (y / y₁ : ℝ) * (DirMean.dp S (coef a) t * MW ν ε k t * (x : ℂ) ^ cl t -
        DirMean.dp S (coef a) t * MW ν ε k t * ((x - y₁ : ℝ) : ℂ) ^ cl t) := by
    funext t
    simp only [powDiff]
    ring
  set F : ℝ → ℝ → ℂ := fun X t ↦ DirMean.dp S (coef a) t * MW ν ε k t * (X : ℂ) ^ cl t with hF
  have h1 : Integrable fun t ↦ F x t - F (x - y) t := (hi x hx).sub (hi _ hxy)
  have h2 : Integrable fun t ↦ F x t - F (x - y₁) t := (hi x hx).sub (hi _ hxy₁)
  have h3 : Integrable fun t ↦ (y / y₁ : ℝ) * (F x t - F (x - y₁) t) := h2.const_mul _
  rw [e, integral_sub h1 h3, integral_sub (hi x hx) (hi _ hxy), integral_const_mul,
    integral_sub (hi x hx) (hi _ hxy₁)]
  simp only [Complex.real_smul]
  ring

/-- **The smoothed comparison.** For a bump `ν` there is `C > 0` such that for `0 < ε < 1`, `k ∈ ℕ`,
`0 < y ≤ y₁ ≤ x/2`, `0 < T₀ ≤ T` and a finite set `S` of positive integers,
`|Σ_{n∈S} a_n w_y(n) − (y/y₁) Σ_{n∈S} a_n w_{y₁}(n)|` is at most
`C(y/√x) ∫_{T₀≤|t|≤T} |A(1/2 + it)| dt + C(1 + T₀)(y/√x)(y₁/x) ∫_{|t|≤T₀} |A(1/2 + it)| dt
+ C√x (Σ_{n∈S} |a_n| n^{−1/2}) ε^{−1}(2/(εT))^k`, with `A(1/2 + it) = Σ_{n∈S} a_n n^{−1/2−it} = dp S (coef a) t`. -/
theorem norm_sum_win_sub_le (hν : Bump ν) : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (k : ℕ) (x y y₁ T₀ T : ℝ),
    0 < x → 0 < y → y ≤ y₁ → y₁ ≤ x / 2 → 0 < T₀ → T₀ ≤ T →
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ a : ℕ → ℂ,
    ‖∑ n ∈ S, a n * (win ν ε k x y n : ℂ) - (y / y₁ : ℝ) * ∑ n ∈ S, a n * (win ν ε k x y₁ n : ℂ)‖ ≤
      C * (y / √x) * ((∫ t in T₀..T, ‖DirMean.dp S (coef a) t‖) +
        ∫ t in (-T)..(-T₀), ‖DirMean.dp S (coef a) t‖) +
      C * (1 + T₀) * (y / √x) * (y₁ / x) * (∫ t in (-T₀)..T₀, ‖DirMean.dp S (coef a) t‖) +
      C * √x * (∑ n ∈ S, ‖coef a n‖) / ε * (2 / (ε * T)) ^ k := by
  obtain ⟨Bν, Bpos, hBν⟩ := MediumPNTW.MellinOfSmooth1d hν.diff hν.supp
  obtain ⟨Cν, Cpos, hCν⟩ := MellinOfSmooth1b hν.diff hν.supp
  refine ⟨Bν + 8 * Cν, by positivity, fun ε εpos ε_lt_one k x y y₁ T₀ T hx hy hyy hy₁ hT₀ hT S hS a ↦ ?_⟩
  have hB : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Bν * ‖cl t‖⁻¹ := fun t ↦
    hBν (cl t) (by rw [cl_re]; norm_num) (by rw [cl_re]; norm_num) ε εpos ε_lt_one
  have hC : ∀ t, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (cl t)‖ ≤ Cν * (ε * ‖cl t‖ ^ 2)⁻¹ := fun t ↦
    hCν (1 / 2) (by norm_num) (cl t) (by rw [cl_re]) (by rw [cl_re]; norm_num) ε εpos ε_lt_one
  have hy₁0 : 0 < y₁ := hy.trans_le hyy
  have hTpos : 0 < T := hT₀.trans_le hT
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  rw [sum_win_sub_eq hν εpos ε_lt_one k hS a hx (by linarith) (by linarith)]
  set A : ℝ → ℝ := fun t ↦ ‖DirMean.dp S (coef a) t‖ with hA
  set L₁ : ℝ := ∑ n ∈ S, ‖coef a n‖ with hL₁
  set b₁ : ℝ := 6 * Bν * (1 / 2 + T₀) * (y * y₁ / (x * √x)) with hb₁
  set b₂ : ℝ := 4 * Bν * y / √x with hb₂
  set b₃ : ℝ := 16 * √x * Cν / ε * (2 / (ε * T)) ^ k with hb₃
  have hb₁0 : 0 ≤ b₁ := by positivity
  have hb₂0 : 0 ≤ b₂ := by positivity
  have hb₃0 : 0 ≤ b₃ := by positivity
  set g : ℝ → ℝ := fun t ↦ b₁ * (Icc (-T₀) T₀).indicator A t +
    b₂ * ((Icc T₀ T).indicator A t + (Icc (-T) (-T₀)).indicator A t) + b₃ * (A t * (1 + t ^ 2)⁻¹) with hg
  have hAc : Continuous A := (DirMean.continuous_dp S (coef a)).norm
  have hAL : ∀ t, A t ≤ L₁ := fun t ↦ norm_dp_le S (coef a) t
  have hA0 : ∀ t, 0 ≤ A t := fun t ↦ norm_nonneg _
  have hind : ∀ c d : ℝ, Integrable ((Icc c d).indicator A) := fun c d ↦
    (hAc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have htailI : Integrable fun t ↦ A t * (1 + t ^ 2)⁻¹ := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul L₁)
      (hAc.mul ((by fun_prop : Continuous fun t : ℝ ↦ 1 + t ^ 2).inv₀ fun t ↦ by positivity)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 t) (by positivity))]
    gcongr
    exact hAL t
  have i1 : Integrable fun t ↦ b₁ * (Icc (-T₀) T₀).indicator A t := (hind _ _).const_mul b₁
  have i2 : Integrable fun t ↦ b₂ * ((Icc T₀ T).indicator A t + (Icc (-T) (-T₀)).indicator A t) :=
    ((hind _ _).add (hind _ _)).const_mul b₂
  have i3 : Integrable fun t ↦ b₃ * (A t * (1 + t ^ 2)⁻¹) := htailI.const_mul b₃
  have i12 : Integrable fun t ↦ b₁ * (Icc (-T₀) T₀).indicator A t +
      b₂ * ((Icc T₀ T).indicator A t + (Icc (-T) (-T₀)).indicator A t) := i1.add i2
  have hgi : Integrable g := i12.add i3
  -- the pointwise bound, in the three ranges of `t`
  have hpt : ∀ t, ‖DirMean.dp S (coef a) t * MW ν ε k t *
      (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤ g t := by
    intro t
    rw [mul_assoc, norm_mul]
    have hi1 : 0 ≤ (Icc (-T₀) T₀).indicator A t := Set.indicator_nonneg (fun t _ ↦ hA0 t) t
    have hi2 : 0 ≤ (Icc T₀ T).indicator A t := Set.indicator_nonneg (fun t _ ↦ hA0 t) t
    have hi3 : 0 ≤ (Icc (-T) (-T₀)).indicator A t := Set.indicator_nonneg (fun t _ ↦ hA0 t) t
    have hi4 : 0 ≤ A t * (1 + t ^ 2)⁻¹ := mul_nonneg (hA0 t) (by positivity)
    rcases le_or_gt |t| T₀ with h1 | h1
    · have hmem : t ∈ Icc (-T₀) T₀ := abs_le.1 h1
      have hk := norm_MW_kernel_le_low hB εpos k hx hy hyy hy₁ t
      have hk' : ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤ b₁ := by
        refine hk.trans ?_
        rw [hb₁]
        gcongr
      have : (Icc (-T₀) T₀).indicator A t = A t := Set.indicator_of_mem hmem A
      calc ‖DirMean.dp S (coef a) t‖ * ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖
          ≤ A t * b₁ := mul_le_mul_of_nonneg_left hk' (hA0 t)
        _ ≤ g t := by
            rw [hg]
            simp only
            rw [this]
            nlinarith [mul_nonneg hb₂0 (add_nonneg hi2 hi3), mul_nonneg hb₃0 hi4]
    rcases le_or_gt |t| T with h2 | h2
    · have hk := norm_MW_kernel_le_mid hB εpos k hx hy hyy hy₁ t
      have hsum : A t ≤ (Icc T₀ T).indicator A t + (Icc (-T) (-T₀)).indicator A t := by
        rcases le_or_gt 0 t with h0 | h0
        · rw [abs_of_nonneg h0] at h1 h2
          rw [Set.indicator_of_mem (show t ∈ Icc T₀ T from ⟨h1.le, h2⟩)]
          linarith
        · rw [abs_of_neg h0] at h1 h2
          rw [Set.indicator_of_mem (show t ∈ Icc (-T) (-T₀) from ⟨by linarith, by linarith⟩)]
          linarith
      calc ‖DirMean.dp S (coef a) t‖ * ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖
          ≤ A t * b₂ := mul_le_mul_of_nonneg_left hk (hA0 t)
        _ ≤ g t := by
            rw [hg]
            simp only
            nlinarith [mul_nonneg hb₁0 hi1, mul_nonneg hb₃0 hi4, mul_le_mul_of_nonneg_left hsum hb₂0]
    · have hk := norm_MW_kernel_le_tail hC εpos k hx hy hyy hy₁ hTpos h2.le
      calc ‖DirMean.dp S (coef a) t‖ * ‖MW ν ε k t * (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖
          ≤ A t * (b₃ * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hk (hA0 t)
        _ ≤ g t := by
            rw [hg]
            simp only
            nlinarith [mul_nonneg hb₁0 hi1, mul_nonneg hb₂0 (add_nonneg hi2 hi3)]
  have hint := norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)
  -- the integral of the bound
  have hIcc : ∀ c d : ℝ, c ≤ d → ∫ t, (Icc c d).indicator A t = ∫ t in c..d, A t := by
    intro c d hcd
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hcd]
  have hgint : ∫ t, g t = b₁ * (∫ t in (-T₀)..T₀, A t) +
      b₂ * ((∫ t in T₀..T, A t) + ∫ t in (-T)..(-T₀), A t) + b₃ * ∫ t, A t * (1 + t ^ 2)⁻¹ := by
    simp only [hg]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add (hind _ _) (hind _ _), hIcc _ _ (by linarith),
      hIcc _ _ hT, hIcc _ _ (by linarith)]
  have htail : ∫ t, A t * (1 + t ^ 2)⁻¹ ≤ L₁ * π := by
    calc ∫ t, A t * (1 + t ^ 2)⁻¹ ≤ ∫ t, L₁ * (1 + t ^ 2)⁻¹ :=
          integral_mono htailI (integrable_inv_one_add_sq.const_mul L₁) fun t ↦ by
            gcongr
            exact hAL t
      _ = L₁ * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hI₁ : 0 ≤ ∫ t in (-T₀)..T₀, A t := intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ hA0 t
  have hI₂ : 0 ≤ ∫ t in T₀..T, A t := intervalIntegral.integral_nonneg hT fun t _ ↦ hA0 t
  have hI₃ : 0 ≤ ∫ t in (-T)..(-T₀), A t := intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ hA0 t
  have hL0 : 0 ≤ L₁ := Finset.sum_nonneg fun n _ ↦ norm_nonneg _
  have hπ : 3 < π := Real.pi_gt_three
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  -- compare the coefficients
  have c₁ : 1 / (2 * π) * b₁ ≤ (Bν + 8 * Cν) * (1 + T₀) * (y / √x) * (y₁ / x) := by
    rw [hb₁]
    have e : y * y₁ / (x * √x) = y / √x * (y₁ / x) := by field_simp
    rw [e]
    have hq : 0 ≤ y / √x * (y₁ / x) := by positivity
    have h3 : 1 / (2 * π) * 6 ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
    calc 1 / (2 * π) * (6 * Bν * (1 / 2 + T₀) * (y / √x * (y₁ / x)))
        = (1 / (2 * π) * 6) * (Bν * ((1 / 2 + T₀) * (y / √x * (y₁ / x)))) := by ring
      _ ≤ 1 * ((Bν + 8 * Cν) * ((1 + T₀) * (y / √x * (y₁ / x)))) := by
          gcongr
          · linarith
          · linarith
      _ = (Bν + 8 * Cν) * (1 + T₀) * (y / √x) * (y₁ / x) := by ring
  have c₂ : 1 / (2 * π) * b₂ ≤ (Bν + 8 * Cν) * (y / √x) := by
    rw [hb₂]
    have h3 : 1 / (2 * π) * 4 ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
    have hq : 0 ≤ y / √x := by positivity
    calc 1 / (2 * π) * (4 * Bν * y / √x) = (1 / (2 * π) * 4) * (Bν * (y / √x)) := by ring
      _ ≤ 1 * ((Bν + 8 * Cν) * (y / √x)) := by
          gcongr
          linarith
      _ = (Bν + 8 * Cν) * (y / √x) := by ring
  have c₃ : 1 / (2 * π) * (b₃ * (L₁ * π)) ≤ (Bν + 8 * Cν) * √x * L₁ / ε * (2 / (ε * T)) ^ k := by
    rw [hb₃]
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    have e : 1 / (2 * π) * (16 * √x * Cν / ε * (2 / (ε * T)) ^ k * (L₁ * π)) =
        8 * Cν * (√x * L₁ / ε * (2 / (ε * T)) ^ k) := by field_simp; ring
    rw [e]
    have hq : 0 ≤ √x * L₁ / ε * (2 / (ε * T)) ^ k := by positivity
    calc 8 * Cν * (√x * L₁ / ε * (2 / (ε * T)) ^ k) ≤ (Bν + 8 * Cν) * (√x * L₁ / ε * (2 / (ε * T)) ^ k) := by
          gcongr
          linarith
      _ = (Bν + 8 * Cν) * √x * L₁ / ε * (2 / (ε * T)) ^ k := by ring
  have hmain : 1 / (2 * π) * ‖∫ t, DirMean.dp S (coef a) t * MW ν ε k t *
      (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖ ≤
      1 / (2 * π) * b₁ * (∫ t in (-T₀)..T₀, A t) +
      1 / (2 * π) * b₂ * ((∫ t in T₀..T, A t) + ∫ t in (-T)..(-T₀), A t) +
      1 / (2 * π) * (b₃ * (L₁ * π)) := by
    have h2π : 0 ≤ 1 / (2 * π) := by positivity
    calc 1 / (2 * π) * ‖∫ t, DirMean.dp S (coef a) t * MW ν ε k t *
          (powDiff x y (cl t) - (y / y₁ : ℝ) * powDiff x y₁ (cl t))‖
        ≤ 1 / (2 * π) * ∫ t, g t := mul_le_mul_of_nonneg_left hint h2π
      _ ≤ 1 / (2 * π) * (b₁ * (∫ t in (-T₀)..T₀, A t) +
          b₂ * ((∫ t in T₀..T, A t) + ∫ t in (-T)..(-T₀), A t) + b₃ * (L₁ * π)) := by
          rw [hgint]
          gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  have k₁ := mul_le_mul_of_nonneg_right c₁ hI₁
  have k₂ := mul_le_mul_of_nonneg_right c₂ (add_nonneg hI₂ hI₃)
  linarith

/-! ### Unsmoothing -/

/-- **Unsmoothing at one endpoint.** `1_{n ≤ X} − W_k(n/X)` vanishes unless
`X(1 − ε log 2)e^{−kε} < n < X(1 + 2ε log 2)`, an interval of length at most `Xε(k + 3)`, and is at most `2`; so
`|Σ_{n∈S} a_n (1_{n ≤ X} − W_k(n/X))| ≤ 2B(Xε(k + 3) + 1)` when `|a_n| ≤ B` on `S`. -/
lemma norm_sum_ind_sub_W_le (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) {a : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n ∈ S, ‖a n‖ ≤ B) {X : ℝ} (hX : 0 < X) :
    ‖∑ n ∈ S, a n * ((if (n : ℝ) ≤ X then 1 else 0) - (W ν ε k (n / X) : ℂ))‖ ≤
      2 * B * (X * ε * (k + 3) + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set lo : ℝ := X * ((1 - Real.log 2 * ε) * Real.exp (-(k * ε))) with hlo
  set hi : ℝ := X * (1 + 2 * Real.log 2 * ε) with hhi
  have h1c : 0 ≤ 1 - Real.log 2 * ε := by nlinarith
  have hlo0 : 0 ≤ lo := by positivity
  have hloX : lo ≤ X := by
    have h1 : Real.exp (-(k * ε)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : 1 - Real.log 2 * ε ≤ 1 := by nlinarith
    have : (1 - Real.log 2 * ε) * Real.exp (-(k * ε)) ≤ 1 :=
      (mul_le_mul h2 h1 (Real.exp_pos _).le zero_le_one).trans (by norm_num)
    calc lo = X * ((1 - Real.log 2 * ε) * Real.exp (-(k * ε))) := rfl
      _ ≤ X * 1 := by gcongr
      _ = X := mul_one X
  have hXhi : X < hi := by
    have : 0 < Real.log 2 * ε := mul_pos hlog2 εpos
    rw [hhi]
    nlinarith
  have hlohi : lo ≤ hi := hloX.trans hXhi.le
  have hlen : hi - lo ≤ X * ε * (k + 3) := by
    have he : 1 - k * ε ≤ Real.exp (-(k * ε)) := by linarith [Real.add_one_le_exp (-(k * ε))]
    have h2 : (1 - Real.log 2 * ε) * (1 - k * ε) ≤ (1 - Real.log 2 * ε) * Real.exp (-(k * ε)) :=
      mul_le_mul_of_nonneg_left he h1c
    have h3 : 0 ≤ Real.log 2 * k * ε ^ 2 := by positivity
    have key : (1 + 2 * Real.log 2 * ε) - (1 - Real.log 2 * ε) * Real.exp (-(k * ε)) ≤ ε * (k + 3) := by
      nlinarith
    calc hi - lo = X * ((1 + 2 * Real.log 2 * ε) - (1 - Real.log 2 * ε) * Real.exp (-(k * ε))) := by
          rw [hhi, hlo]; ring
      _ ≤ X * (ε * (k + 3)) := by gcongr
      _ = X * ε * (k + 3) := by ring
  -- termwise
  have hterm : ∀ n ∈ S, ‖a n * ((if (n : ℝ) ≤ X then 1 else 0) - (W ν ε k (n / X) : ℂ))‖ ≤
      2 * B * (if lo < n ∧ (n : ℝ) < hi then 1 else 0) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hS n hn
    have hu : 0 < (n : ℝ) / X := div_pos hnpos hX
    rw [norm_mul]
    by_cases hw : lo < n ∧ (n : ℝ) < hi
    · rw [ite_eq_left hw, mul_one]
      have hW := abs_W_le_one hν εpos k hu
      have hd : ‖(if (n : ℝ) ≤ X then (1 : ℂ) else 0) - (W ν ε k (n / X) : ℂ)‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        split_ifs <;> simp <;> linarith
      calc ‖a n‖ * ‖(if (n : ℝ) ≤ X then (1 : ℂ) else 0) - (W ν ε k (n / X) : ℂ)‖ ≤ B * 2 :=
            mul_le_mul (hB n hn) hd (norm_nonneg _) hB0
        _ = 2 * B := mul_comm B 2
    · rw [ite_eq_right hw, mul_zero]
      rw [not_and_or, not_lt, not_lt] at hw
      rcases hw with h | h
      · have hW : W ν ε k (n / X) = 1 := by
          refine W_eq_one hν εpos k hu ?_
          rw [div_le_iff₀ hX]
          linarith
        rw [ite_eq_left (h.trans hloX), hW, ofReal_one, sub_self, norm_zero, mul_zero]
      · have hW : W ν ε k (n / X) = 0 := by
          refine W_eq_zero hν εpos ε_lt_one k ?_
          rw [le_div_iff₀ hX]
          linarith
        rw [ite_eq_right (by linarith), hW, ofReal_zero, sub_self, norm_zero, mul_zero]
  calc ‖∑ n ∈ S, a n * ((if (n : ℝ) ≤ X then 1 else 0) - (W ν ε k (n / X) : ℂ))‖
      ≤ ∑ n ∈ S, ‖a n * ((if (n : ℝ) ≤ X then 1 else 0) - (W ν ε k (n / X) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, 2 * B * (if lo < n ∧ (n : ℝ) < hi then 1 else 0) := Finset.sum_le_sum hterm
    _ = 2 * B * (S.filter fun n : ℕ ↦ lo < n ∧ (n : ℝ) < hi).card := by
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ 2 * B * (hi - lo + 1) := by gcongr; exact SmoothPerron.card_window_le hlo0 hlohi S
    _ ≤ 2 * B * (X * ε * (k + 3) + 1) := by gcongr

/-- **A sharp interval against its smooth window.** For `0 ≤ y < x`,
`|Σ_{n∈S, x−y<n≤x} a_n − Σ_{n∈S} a_n w_y(n)| ≤ 4B(xε(k + 3) + 1)` when `|a_n| ≤ B` on `S`. -/
lemma norm_sum_sharp_sub_win_le (hν : Bump ν) (εpos : 0 < ε) (ε_lt_one : ε < 1) (k : ℕ) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) {a : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n ∈ S, ‖a n‖ ≤ B) {x y : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hyx : y < x) :
    ‖∑ n ∈ S.filter (fun n : ℕ ↦ x - y < n ∧ (n : ℝ) ≤ x), a n - ∑ n ∈ S, a n * (win ν ε k x y n : ℂ)‖ ≤
      4 * B * (x * ε * (k + 3) + 1) := by
  have hxy : 0 < x - y := by linarith
  have e : ∑ n ∈ S.filter (fun n : ℕ ↦ x - y < n ∧ (n : ℝ) ≤ x), a n -
      ∑ n ∈ S, a n * (win ν ε k x y n : ℂ) =
      ∑ n ∈ S, a n * ((if (n : ℝ) ≤ x then 1 else 0) - (W ν ε k (n / x) : ℂ)) -
      ∑ n ∈ S, a n * ((if (n : ℝ) ≤ x - y then 1 else 0) - (W ν ε k (n / (x - y)) : ℂ)) := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [win]
    push_cast
    by_cases h1 : (n : ℝ) ≤ x - y
    · rw [ite_eq_right (by intro h; linarith [h.1]), ite_eq_left (by linarith), ite_eq_left h1]
      ring
    · by_cases h2 : (n : ℝ) ≤ x
      · rw [ite_eq_left ⟨by linarith, h2⟩, ite_eq_left h2, ite_eq_right h1]
        ring
      · rw [ite_eq_right (by intro h; exact h2 h.2), ite_eq_right h2, ite_eq_right h1]
        ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sum_ind_sub_W_le hν εpos ε_lt_one k hS hB0 hB hx
  have h2 := norm_sum_ind_sub_W_le hν εpos ε_lt_one k hS hB0 hB hxy
  have h3 : 2 * B * ((x - y) * ε * (k + 3) + 1) ≤ 2 * B * (x * ε * (k + 3) + 1) := by
    have : (0 : ℝ) ≤ k + 3 := by positivity
    gcongr
    linarith
  linarith

/-- **The sharp comparison, for a bump `ν`**: `norm_sum_win_sub_le` plus the cost `8B(xε(k + 3) + 1)` of the
transitions of the smoothing (`norm_sum_sharp_sub_win_le` for `y` and for `y₁`). -/
theorem norm_sum_Ioc_sub_le_of_bump (hν : Bump ν) : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ (k : ℕ) (x y y₁ T₀ T : ℝ), 0 < x → 0 < y → y ≤ y₁ → y₁ ≤ x / 2 → 0 < T₀ → T₀ ≤ T →
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ (a : ℕ → ℂ) (B : ℝ), 0 ≤ B → (∀ n ∈ S, ‖a n‖ ≤ B) →
    ‖∑ n ∈ S.filter (fun n : ℕ ↦ x - y < n ∧ (n : ℝ) ≤ x), a n -
        (y / y₁ : ℝ) * ∑ n ∈ S.filter (fun n : ℕ ↦ x - y₁ < n ∧ (n : ℝ) ≤ x), a n‖ ≤
      C * (y / √x) * ((∫ t in T₀..T, ‖DirMean.dp S (coef a) t‖) +
        ∫ t in (-T)..(-T₀), ‖DirMean.dp S (coef a) t‖) +
      C * (1 + T₀) * (y / √x) * (y₁ / x) * (∫ t in (-T₀)..T₀, ‖DirMean.dp S (coef a) t‖) +
      C * √x * (∑ n ∈ S, ‖coef a n‖) / ε * (2 / (ε * T)) ^ k +
      8 * B * (x * ε * (k + 3) + 1) := by
  obtain ⟨C, Cpos, hC⟩ := norm_sum_win_sub_le hν
  refine ⟨C, Cpos, fun ε εpos ε_lt_one k x y y₁ T₀ T hx hy hyy hy₁ hT₀ hT S hS a B hB0 hB ↦ ?_⟩
  have hy₁0 : 0 < y₁ := hy.trans_le hyy
  have hsm := hC ε εpos ε_lt_one k x y y₁ T₀ T hx hy hyy hy₁ hT₀ hT S hS a
  have e1 := norm_sum_sharp_sub_win_le hν εpos ε_lt_one k hS hB0 hB hx hy.le (by linarith : y < x)
  have e2 := norm_sum_sharp_sub_win_le hν εpos ε_lt_one k hS hB0 hB hx hy₁0.le (by linarith : y₁ < x)
  set P : ℂ := ∑ n ∈ S.filter (fun n : ℕ ↦ x - y < n ∧ (n : ℝ) ≤ x), a n
  set P₁ : ℂ := ∑ n ∈ S.filter (fun n : ℕ ↦ x - y₁ < n ∧ (n : ℝ) ≤ x), a n
  set Q : ℂ := ∑ n ∈ S, a n * (win ν ε k x y n : ℂ)
  set Q₁ : ℂ := ∑ n ∈ S, a n * (win ν ε k x y₁ n : ℂ)
  have hc : ‖((y / y₁ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hy hy₁0)]
    exact (div_le_one hy₁0).2 hyy
  have e : P - (y / y₁ : ℝ) * P₁ = (Q - (y / y₁ : ℝ) * Q₁) + (P - Q) - (y / y₁ : ℝ) * (P₁ - Q₁) := by ring
  rw [e]
  have h3 : ‖((y / y₁ : ℝ) : ℂ) * (P₁ - Q₁)‖ ≤ 4 * B * (x * ε * (k + 3) + 1) := by
    rw [norm_mul]
    calc ‖((y / y₁ : ℝ) : ℂ)‖ * ‖P₁ - Q₁‖ ≤ 1 * (4 * B * (x * ε * (k + 3) + 1)) :=
          mul_le_mul hc e2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc ‖(Q - (y / y₁ : ℝ) * Q₁) + (P - Q) - (y / y₁ : ℝ) * (P₁ - Q₁)‖
      ≤ ‖Q - (y / y₁ : ℝ) * Q₁‖ + ‖P - Q‖ + ‖((y / y₁ : ℝ) : ℂ) * (P₁ - Q₁)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by linarith

/-- **Sums over short intervals by mean values of Dirichlet polynomials.** There is an absolute constant `C > 0`
such that for `0 < ε < 1`, `k ∈ ℕ`, `0 < y ≤ y₁ ≤ x/2`, `0 < T₀ ≤ T`, a finite set `S` of positive integers and
`|a_n| ≤ B` on `S`, the sums running over `n ∈ S`,
`|Σ_{x−y<n≤x} a_n − (y/y₁) Σ_{x−y₁<n≤x} a_n| ≤ C(y/√x) ∫_{T₀≤|t|≤T} |A(1/2 + it)| dt
+ C(1 + T₀)(y/√x)(y₁/x) ∫_{|t|≤T₀} |A(1/2 + it)| dt + C√x (Σ_{n∈S} |a_n| n^{−1/2}) ε^{−1}(2/(εT))^k
+ 8B(xε(k + 3) + 1)`, where `A(1/2 + it) = Σ_{n∈S} a_n n^{−1/2−it} = dp S (coef a) t`. -/
theorem norm_sum_Ioc_sub_le : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ (k : ℕ) (x y y₁ T₀ T : ℝ), 0 < x → 0 < y → y ≤ y₁ → y₁ ≤ x / 2 → 0 < T₀ → T₀ ≤ T →
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ (a : ℕ → ℂ) (B : ℝ), 0 ≤ B → (∀ n ∈ S, ‖a n‖ ≤ B) →
    ‖∑ n ∈ S.filter (fun n : ℕ ↦ x - y < n ∧ (n : ℝ) ≤ x), a n -
        (y / y₁ : ℝ) * ∑ n ∈ S.filter (fun n : ℕ ↦ x - y₁ < n ∧ (n : ℝ) ≤ x), a n‖ ≤
      C * (y / √x) * ((∫ t in T₀..T, ‖DirMean.dp S (coef a) t‖) +
        ∫ t in (-T)..(-T₀), ‖DirMean.dp S (coef a) t‖) +
      C * (1 + T₀) * (y / √x) * (y₁ / x) * (∫ t in (-T₀)..T₀, ‖DirMean.dp S (coef a) t‖) +
      C * √x * (∑ n ∈ S, ‖coef a n‖) / ε * (2 / (ε * T)) ^ k +
      8 * B * (x * ε * (k + 3) + 1) := by
  obtain ⟨ν, hν⟩ := exists_bump
  exact norm_sum_Ioc_sub_le_of_bump hν

end ShortSieveInterval

#print axioms ShortSieveInterval.W_eq_integral
#print axioms ShortSieveInterval.sum_W_eq
#print axioms ShortSieveInterval.norm_sum_win_sub_le
#print axioms ShortSieveInterval.norm_sum_Ioc_sub_le
