/-
# The fourth moment of `ζ(½ + it)` at well-spaced points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `0 < ε ≤ 1` there is `C` such that `Σ_r |ζ(½ + it_r)|⁴ ≤ C(T + 2)^{1+ε}` for every finite
family of points `t_r` with `|t_r| ≤ T` and `|t_r − t_s| ≥ 1` for `r ≠ s` (`zeta_fourth_moment`). This is the input
of Ingham's density estimate for `ζ` (`ZetaIngham.lean`), as `LinnikFourth.fourth_moment` is over the characters
mod `q`; the proof is the same, with the points in place of the characters and Montgomery–Vaughan's mean value
(`DirMean.large_values_off'`) in place of the large sieve over characters.

* `norm_zeta_sq_le`, `norm_zeta_four_le`: `|ζ(½ + it)|⁴ ≤ 2|D(½ + it)|² + 2|D(½ − it)|²` with `D = J/ξ_F²`
  (`afeDx`), `ξ_F(s) = ½s(s − 1)Γ_ℝ(s)`, from `ZetaFourth.afe_xi` and `|ξ_F(½ − it)| = |ξ_F(½ + it)|`.
* `sum_norm_Pd_sq_le_sep`: `Σ_r |P(½ + c₀ + ix_r)|²` for `P(z) = Σ_{n ≤ N₀} d(n)n^{−z}` (`LinnikFourth.Pd` at the
  trivial character mod `1`, whose `L`-function is `ζ`) at 1-separated points, by the dyadic blocks of `P`,
  `DirMean.large_values_off'` and `InghamDensity.block_mass_le_b`.
* `afeJx_split`: `J = (1/2πi)∫_{(c₀)} ξ_F²P e^{w²}dw/w + (1/2πi)∫_{(c₁)} ξ_F²T e^{w²}dw/w` for `0 < c₀ ≤ 2 ≤ c₁`, with
  `T = ζ² − P` (`LinnikFourth.Tl`), which is holomorphic on `Re z > 1`; no pole is crossed. On `Re w = c > 0` the
  integrand is at most `KG2x(c, t)|M(½ + it + w)|W_{c+9/2}(v)` (`norm_GGx_le`): `LinnikGamma.norm_Gamma_ratio_le` for
  `Γ_ℝ`, and `|s + w||s + w − 1| ≤ (2(1 + c)(1 + |v|))²|s||s − 1|` on the critical line.
* `sum_norm_afeDx_sq_le`: `Σ_r |D(½ + it_r)|² ≤ C(T + 2)^{1+ε}` at `c₀ = ε/8`, `c₁ = 40/ε`,
  `N₀ = ⌈(T + 2)^{1+ε/8}⌉`; `zeta_fourth_moment`: the points `t_r` for the first term and `−t_r` for the second.
* `norm_zeta_le_strip`: `|ζ(σ + it)| ≤ 2 + 2|t|/σ` for `0 < σ ≤ 2` and `|t| ≥ 2` (PNT+'s `ZetaBnd_aux1`), for
  `ZetaIngham` and `ZetaKernel`.
-/
import ZetaAFE
import LinnikFourth

open Complex Real Set MeasureTheory Finset

noncomputable section

namespace ZetaFourth

open LinnikGamma DirMean ShortWeil InghamDensity LinnikFourth

/-! ### From the approximate functional equation to `|ζ|²` -/

/-- `D(s) = J(s)/ξ_F(s)²`. -/
def afeDx (s : ℂ) : ℂ := afeJx s / xiF s ^ 2

lemma xiF_ne_zero (t : ℝ) : xiF (1 / 2 + t * I) ≠ 0 := by
  unfold xiF
  have h0 : (1 / 2 + t * I : ℂ) ≠ 0 := fun h => by
    rw [Complex.ext_iff] at h; norm_num at h
  have h1 : (1 / 2 + t * I : ℂ) - 1 ≠ 0 := fun h => by
    rw [Complex.ext_iff] at h; norm_num at h
  have hG : Gammaℝ (1 / 2 + t * I) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp)
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero) hG

/-- On the critical line `|ξ_F(1 − s)| = |ξ_F(s)|`. -/
lemma norm_xiF_one_sub (t : ℝ) : ‖xiF (1 - (1 / 2 + t * I))‖ = ‖xiF (1 / 2 + t * I)‖ := by
  have h : (1 : ℂ) - (1 / 2 + t * I) = starRingEnd ℂ (1 / 2 + t * I) := by
    apply Complex.ext <;> norm_num
  have h1 : starRingEnd ℂ (1 / 2 + t * I) - 1 = starRingEnd ℂ (1 / 2 + t * I - 1) := by simp
  rw [h]
  unfold xiF
  rw [norm_mul, norm_mul, norm_div, norm_div, norm_mul, norm_mul, norm_Gammaℝ_conj, Complex.norm_conj, h1,
    Complex.norm_conj]

/-- **`|ζ(½ + it)|² ≤ |D(½ + it)| + |D(½ − it)|`**: the approximate functional equation for `ξ²`. -/
theorem norm_zeta_sq_le (t : ℝ) :
    ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 ≤ ‖afeDx (1 / 2 + t * I)‖ + ‖afeDx (1 / 2 + (-t : ℝ) * I)‖ := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hA := afe_xi (s := s) (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have h1s : (1 : ℂ) - s = 1 / 2 + ((-t : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hF : xiF s ≠ 0 := xiF_ne_zero t
  have hFn : 0 < ‖xiF s‖ := norm_pos_iff.2 hF
  have hxi : xi s = xiF s * riemannZeta s := xi_eq_mul (by rw [hsre]; norm_num) hs1
  have hmain : ‖riemannZeta s‖ ^ 2 * ‖xiF s‖ ^ 2 ≤ ‖afeJx s‖ + ‖afeJx (1 - s)‖ := by
    have e : ‖xi s ^ 2‖ = ‖riemannZeta s‖ ^ 2 * ‖xiF s‖ ^ 2 := by
      rw [hxi, norm_pow, norm_mul, mul_pow]; ring
    rw [← e, hA]
    exact norm_add_le _ _
  have hF' : ‖xiF (1 - s)‖ = ‖xiF s‖ := by rw [hs, norm_xiF_one_sub]
  have hD1 : ‖afeDx s‖ = ‖afeJx s‖ / ‖xiF s‖ ^ 2 := by rw [afeDx, norm_div, norm_pow]
  have hD2 : ‖afeDx (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ = ‖afeJx (1 - s)‖ / ‖xiF s‖ ^ 2 := by
    rw [← h1s, afeDx, norm_div, norm_pow, hF']
  rw [hD1, hD2, ← add_div, le_div_iff₀ (by positivity)]
  exact hmain

/-- **`|ζ(½ + it)|⁴ ≤ 2|D(½ + it)|² + 2|D(½ − it)|²`**. -/
theorem norm_zeta_four_le (t : ℝ) :
    ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤
      2 * ‖afeDx (1 / 2 + t * I)‖ ^ 2 + 2 * ‖afeDx (1 / 2 + (-t : ℝ) * I)‖ ^ 2 := by
  have h := norm_zeta_sq_le t
  have h0 : 0 ≤ ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 := by positivity
  calc ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 = (‖riemannZeta (1 / 2 + t * I)‖ ^ 2) ^ 2 := by ring
    _ ≤ (‖afeDx (1 / 2 + t * I)‖ + ‖afeDx (1 / 2 + (-t : ℝ) * I)‖) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖afeDx (1 / 2 + t * I)‖ - ‖afeDx (1 / 2 + (-t : ℝ) * I)‖)]

/-! ### The Dirichlet polynomial of `d(n)` at well-spaced points -/

/-- The trivial character mod `1`, whose `L`-function is `ζ`. -/
abbrev χ₁ : DirichletCharacter ℂ 1 := 1

lemma LFunction_χ₁ : DirichletCharacter.LFunction χ₁ = riemannZeta := DirichletCharacter.LFunction_modOne_eq

lemma χ₁_apply (a : ZMod 1) : χ₁ a = 1 := MulChar.one_apply (isUnit_of_subsingleton a)

/-- **`ζ` on `0 < σ ≤ 2`, `|t| ≥ 2`**: `|ζ(σ + it)| ≤ 2 + 2|t|/σ` (PNT+'s `Zeta0EqZeta` at `N = 1` and
`ZetaBnd_aux1`). -/
lemma norm_zeta_le_strip {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta (σ + t * I)‖ ≤ 2 + 2 * |t| / σ := by
  have hint := ZetaBnd_aux1 1 le_rfl ⟨hσ, hσ2⟩ ht
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim] at this
    simp at this
    rw [this] at ht
    norm_num at ht
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  rw [← Zeta0EqZeta (N := 1) one_pos (by rw [hsre]; exact hσ) hs1]
  unfold riemannZeta0
  have hsum : ∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s) = 1 := by
    simp [Finset.sum_range_succ, Complex.zero_cpow hs0]
  have h1s : 2 ≤ ‖1 - s‖ := by
    calc (2 : ℝ) ≤ |t| := ht
      _ = |(1 - s).im| := by simp [hsim]
      _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
  have hfr : ‖(-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 / 2 := by
    rw [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hhalf : ‖(-((1 : ℕ) : ℂ) ^ (-s)) / 2‖ = 1 / 2 := by
    rw [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one, Complex.norm_two]
  have hint' : ‖s * ∫ x in Set.Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ 2 * |t| / σ := by
    have e : 2 * |t| * ((1 : ℕ) : ℝ) ^ (-σ) / σ = 2 * |t| / σ := by rw [Nat.cast_one, Real.one_rpow, mul_one]
    rw [← e]
    exact hint
  calc ‖(∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s)) + (-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s) +
        (-((1 : ℕ) : ℂ) ^ (-s)) / 2 + s * ∫ x in Set.Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ‖∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s)‖ + ‖(-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s)‖ +
        ‖(-((1 : ℕ) : ℂ) ^ (-s)) / 2‖ + ‖s * ∫ x in Set.Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        exact norm_add₄_le
    _ ≤ 1 + 1 / 2 + 1 / 2 + 2 * |t| / σ := by
        rw [hsum, norm_one, hhalf]
        linarith
    _ = 2 + 2 * |t| / σ := by ring

/-- At most `2T + 1` points of `[−T, T]` are 1-separated. -/
lemma card_le_of_sep {ι : Type*} (Rs : Finset ι) (t : ι → ℝ) (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |t r - t s|)
    {T : ℝ} (hT : 0 ≤ T) (ht : ∀ r ∈ Rs, |t r| ≤ T) : (Rs.card : ℝ) ≤ 2 * T + 1 := by
  classical
  have hmaps : ∀ r ∈ Rs, ⌊t r + T⌋₊ ∈ range (⌊2 * T⌋₊ + 1) := by
    intro r hr
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (by linarith [(abs_le.1 (ht r hr)).2])
  have hinj : Set.InjOn (fun r => ⌊t r + T⌋₊) Rs := by
    intro r hr s hs hrs
    by_contra hne
    have h1 := hsep r hr s hs hne
    have hr0 : 0 ≤ t r + T := by linarith [(abs_le.1 (ht r hr)).1]
    have hs0 : 0 ≤ t s + T := by linarith [(abs_le.1 (ht s hs)).1]
    have a1 := Nat.floor_le hr0
    have a2 := Nat.floor_le hs0
    have b1 := Nat.lt_floor_add_one (t r + T)
    have b2 := Nat.lt_floor_add_one (t s + T)
    have e : ((⌊t r + T⌋₊ : ℕ) : ℝ) = ⌊t s + T⌋₊ := by exact_mod_cast hrs
    have : |t r - t s| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  have hc := card_le_card_of_injOn (fun r => ⌊t r + T⌋₊) hmaps hinj
  rw [card_range] at hc
  have h2 : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T + 1 := by
    push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
  exact (Nat.cast_le.2 hc).trans h2

/-- **Large values of `P` at well-spaced points**: for `0 < c₀ ≤ 1/2` and 1-separated points `|x_r| ≤ X`,
`Σ_r |P(1/2 + c₀ + ix_r)|² ≤ LSb(#R, 1, N₀, X)` (the bound of `LinnikFourth.sum_norm_Pd_sq_le` at one character):
the term `n = 1`, the dyadic blocks of `(1, N₀]`, `DirMean.large_values_off'` and `InghamDensity.block_mass_le_b`. -/
theorem sum_norm_Pd_sq_le_sep {ι : Type*} {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 2)
    (Rs : Finset ι) {X : ℝ} (hX : 0 ≤ X) (x : ι → ℝ) (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |x r - x s|)
    (hx : ∀ r ∈ Rs, |x r| ≤ X) :
    ∑ r ∈ Rs, ‖Pd χ₁ N₀ ((1 / 2 + c₀ : ℝ) + x r * I)‖ ^ 2 ≤ LSb Rs.card 1 N₀ X := by
  set σ₀ : ℝ := 1 / 2 + c₀ with hσ₀
  set K := Nat.log 2 N₀ + 1 with hK
  set B := fun (r : ι) (k : ℕ) =>
    dp ((Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k))
      (fun j => (j.divisors.card : ℂ) * χ₁ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ)) (x r) with hB
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  -- the polynomial: the term `n = 1` and the blocks
  have hsplit : ∀ r : ι, Pd χ₁ N₀ (σ₀ + x r * I) = 1 + ∑ k ∈ range K, B r k := by
    intro r
    rw [Pd_eq_dp, ← Finset.Ioc_insert_left hN₀]
    have h1 : dp (insert 1 (Finset.Ioc 1 N₀)) (fun j => (j.divisors.card : ℂ) * χ₁ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ))
          (x r) = 1 + dp (Finset.Ioc 1 N₀)
            (fun j => (j.divisors.card : ℂ) * χ₁ j * (((j : ℝ) ^ (-σ₀) : ℝ) : ℂ)) (x r) := by
      unfold dp
      rw [Finset.sum_insert (by simp)]
      congr 1
      simp [χ₁_apply]
    rw [h1, show Finset.Ioc 1 N₀ = Finset.Ioc 1 (1 * N₀) by rw [one_mul], dp_blocks 1 N₀ le_rfl]
  -- pointwise: `|P|² ≤ 2 + 2K Σ_k |B_k|²`
  have hpt : ∀ r : ι, ‖Pd χ₁ N₀ (σ₀ + x r * I)‖ ^ 2 ≤ 2 + 2 * K * ∑ k ∈ range K, ‖B r k‖ ^ 2 := by
    intro r
    rw [hsplit]
    have h1 : ‖(1 : ℂ) + ∑ k ∈ range K, B r k‖ ≤ 1 + ∑ k ∈ range K, ‖B r k‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one]
      gcongr
      exact norm_sum_le _ _
    have h2 : (∑ k ∈ range K, ‖B r k‖) ^ 2 ≤ K * ∑ k ∈ range K, ‖B r k‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := range K) (f := fun k => ‖B r k‖)
      simpa using this
    have h0 : 0 ≤ ∑ k ∈ range K, ‖B r k‖ := sum_nonneg fun _ _ => norm_nonneg _
    calc ‖(1 : ℂ) + ∑ k ∈ range K, B r k‖ ^ 2 ≤ (1 + ∑ k ∈ range K, ‖B r k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 + 2 * (∑ k ∈ range K, ‖B r k‖) ^ 2 := by nlinarith [sq_nonneg (1 - ∑ k ∈ range K, ‖B r k‖)]
      _ ≤ 2 + 2 * (K * ∑ k ∈ range K, ‖B r k‖ ^ 2) := by gcongr
      _ = 2 + 2 * K * ∑ k ∈ range K, ‖B r k‖ ^ 2 := by ring
  -- one block over the points
  set Lb := Real.exp 1 * ((((1 : ℕ) : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) *
    (2 + Real.log (2 * N₀) ^ 2)) * (2 * (1 + Real.log (2 * N₀)) ^ 3) with hLb
  have hblock : ∀ k ∈ range K, ∑ r ∈ Rs, ‖B r k‖ ^ 2 ≤ Lb := by
    intro k hk
    have hkK : k < Nat.log 2 N₀ + 1 := Finset.mem_range.1 hk
    set P := 2 ^ k * 1 with hPdef
    have hP : 1 ≤ P := by rw [hPdef]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ N₀ := by rw [hPdef, mul_one]; exact pow_blk_le hkK hN₀
    have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hPNr : (P : ℝ) ≤ N₀ := by exact_mod_cast hPN
    have hsub := block_sub (X := 1) (N := N₀) (k := k) le_rfl
    have hLV := large_values_off' hP hsub (fun j => (j.divisors.card : ℂ) * χ₁ j) (σ := σ₀)
      (lo := -X - 1 / 2) (hi := X + 1 / 2) (by linarith) Rs x (fun _ => σ₀) hsep
      (fun r hr => by have := abs_le.1 (hx r hr); constructor <;> linarith)
      (fun _ _ => ⟨le_rfl, by linarith⟩)
    have hmass := block_mass_le_b (fun j => (j.divisors.card : ℂ) * χ₁ j)
      (fun j => by
        rw [norm_mul, Complex.norm_natCast]
        have := DirichletCharacter.norm_le_one χ₁ (j : ZMod 1)
        have h0 : (0 : ℝ) ≤ (j.divisors.card : ℝ) := Nat.cast_nonneg _
        nlinarith) hP hsub (by linarith : 0 ≤ σ₀)
    have hlogP : Real.log P ≤ Real.log N₀ := Real.log_le_log (by linarith) hPNr
    have hlog2P : Real.log (2 * P) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
    have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hPr
    have hlog2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
    have hPpow : (P : ℝ) ^ (1 - 2 * σ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hPr (by linarith)
    have hmass' : ∑ j ∈ (Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k),
        ‖(j.divisors.card : ℂ) * χ₁ j‖ ^ 2 * ((j : ℝ) ^ (-σ₀)) ^ 2 ≤ 2 * (1 + Real.log (2 * N₀)) ^ 3 := by
      refine hmass.trans ?_
      have h3 : (1 + Real.log (2 * P)) ^ 3 ≤ (1 + Real.log (2 * N₀)) ^ 3 := by gcongr
      have h4 : 0 ≤ (1 + Real.log (2 * P)) ^ 3 := by positivity
      nlinarith
    have hfirst : (X + 1 / 2 - (-X - 1 / 2) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) ≤
        (((1 : ℕ) : ℝ) * (2 * X + 1) + 8 * N₀ * (1 + Real.log N₀)) * (2 + Real.log (2 * N₀) ^ 2) := by
      have e : X + 1 / 2 - (-X - 1 / 2) = ((1 : ℕ) : ℝ) * (2 * X + 1) := by push_cast; ring
      rw [e]
      have hNX : 0 ≤ ((1 : ℕ) : ℝ) * (2 * X + 1) := by positivity
      gcongr
    have hB' : ∀ r ∈ Rs, B r k = dp ((Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k))
        (fun j => (j.divisors.card : ℂ) * χ₁ j * (((j : ℝ) ^ (-(fun _ => σ₀) r) : ℝ) : ℂ)) (x r) :=
      fun r _ => rfl
    rw [sum_congr rfl fun r hr => by rw [hB' r hr]]
    refine hLV.trans ?_
    rw [hLb]
    have hm0 : 0 ≤ ∑ j ∈ (Finset.Ioc 1 (1 * N₀)).filter (fun j => blk 1 j = k),
        ‖(j.divisors.card : ℂ) * χ₁ j‖ ^ 2 * ((j : ℝ) ^ (-σ₀)) ^ 2 := sum_nonneg fun _ _ => by positivity
    have hf0 : 0 ≤ (X + 1 / 2 - (-X - 1 / 2) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) := by
      have : X + 1 / 2 - (-X - 1 / 2) = 2 * X + 1 := by ring
      rw [this]; positivity
    gcongr
  -- assemble
  calc ∑ r ∈ Rs, ‖Pd χ₁ N₀ ((1 / 2 + c₀ : ℝ) + x r * I)‖ ^ 2
      ≤ ∑ r ∈ Rs, (2 + 2 * K * ∑ k ∈ range K, ‖B r k‖ ^ 2) := sum_le_sum fun r _ => hpt r
    _ = 2 * Rs.card + 2 * K * ∑ k ∈ range K, ∑ r ∈ Rs, ‖B r k‖ ^ 2 := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_comm]; ring
    _ ≤ 2 * Rs.card + 2 * K * ∑ k ∈ range K, Lb := by
        gcongr with k hk
        exact hblock k hk
    _ = 2 * Rs.card + 2 * (K : ℝ) ^ 2 * Lb := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ = LSb Rs.card 1 N₀ X := by rw [hLb]; unfold LSb; ring

/-! ### The split integrands -/

/-- `|Γ_ℝ(½ + it + c + iv)| ≤ e^{KR(c)}(1 + |t|)^{c/2}(1 + |v|)^{c/2+1/4}e^{π|v|/4}|Γ_ℝ(½ + it)|` (the even case of
`LinnikGamma.norm_gammaFactor_ratio_le`). -/
lemma norm_Gammaℝ_ratio_le {c : ℝ} (hc : 0 ≤ c) (t v : ℝ) :
    ‖Gammaℝ (1 / 2 + t * I + (c + v * I))‖ ≤
      Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
        ‖Gammaℝ (1 / 2 + t * I)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have e1 : (1 / 2 + t * I + (c + v * I)) / 2 = (((1 / 4) + c / 2 : ℝ) : ℂ) + ((t / 2 + v / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have e0 : (1 / 2 + t * I) / 2 = (((1 / 4) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e0]
  have hG := norm_Gamma_ratio_le (x₀ := 1 / 4) (c := c) (y₀ := t / 2) (v := v) (by norm_num) (by norm_num) hc
  have hre1 : (-(1 / 2 + t * I + (c + v * I)) / 2 : ℂ).re = -(1 / 2 + c) / 2 := by simp
  have hre0 : (-(1 / 2 + t * I) / 2 : ℂ).re = -(1 / 2) / 2 := by simp
  rw [hre1, hre0]
  have hπ : Real.pi ^ (-(1 / 2 + c) / 2) ≤ Real.pi ^ (-(1 / 2) / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have ht : (1 + |t / 2|) ^ (c / 2) ≤ (1 + |t|) ^ (c / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  calc Real.pi ^ (-(1 / 2 + c) / 2) *
        ‖Complex.Gamma ((((1 / 4) + c / 2 : ℝ) : ℂ) + ((t / 2 + v / 2 : ℝ) : ℂ) * I)‖
      ≤ Real.pi ^ (-(1 / 2) / 2 : ℝ) * (Real.exp (KR c) * (1 + |t / 2|) ^ (c / 2) *
          (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
            ‖Complex.Gamma ((((1 / 4) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) :=
        mul_le_mul hπ hG (norm_nonneg _) (by positivity)
    _ ≤ Real.pi ^ (-(1 / 2) / 2 : ℝ) * (Real.exp (KR c) * (1 + |t|) ^ (c / 2) *
          (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
            ‖Complex.Gamma ((((1 / 4) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) := by gcongr
    _ = _ := by ring

/-- On the critical line, `|s + w| ≤ 2(1 + c)(1 + |v|)|s|` and the same for `s − 1`, for `w = c + iv`, `c ≥ 0`. -/
lemma norm_add_le_crit (t c v : ℝ) (hc : 0 ≤ c) (a : ℂ) (ha : a = 0 ∨ a = 1) :
    ‖1 / 2 + t * I + (c + v * I) - a‖ ≤ 2 * (1 + c) * (1 + |v|) * ‖1 / 2 + t * I - a‖ := by
  have hs : 1 / 2 ≤ ‖1 / 2 + t * I - a‖ := by
    have h := Complex.abs_re_le_norm (1 / 2 + t * I - a)
    rcases ha with rfl | rfl <;> norm_num at h ⊢ <;> linarith
  have hw : ‖(c : ℂ) + v * I‖ ≤ c + |v| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hc]
  have e : 1 / 2 + t * I + (c + v * I) - a = (1 / 2 + t * I - a) + ((c : ℂ) + v * I) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  set m := ‖1 / 2 + t * I - a‖ with hm
  have hv := abs_nonneg v
  nlinarith [mul_nonneg hc hv, mul_nonneg (mul_nonneg hc hv) (by linarith : (0 : ℝ) ≤ m)]

/-- The split integrand `ξ_F(s + w)²M(s + w)e^{w²}/w`. -/
def GGx (M : ℂ → ℂ) (s w : ℂ) : ℂ := xiF (s + w) ^ 2 * M (s + w) * Complex.exp (w ^ 2) / w

lemma afeGx_eq_GGx {s w : ℂ} (h : 0 < (s + w).re) (h1 : s + w ≠ 1) :
    afeGx s w = GGx (fun z => riemannZeta z ^ 2) s w := by
  unfold afeGx GGx
  rw [xi_eq_mul h h1]
  ring

lemma GGx_add (M₁ M₂ : ℂ → ℂ) (s w : ℂ) : GGx (fun z => M₁ z + M₂ z) s w = GGx M₁ s w + GGx M₂ s w := by
  unfold GGx; ring

/-- The constant of `norm_GGx_le`: `(e^{KR(c)}(1 + |t|)^{c/2}|ξ_F(½ + it)|)²(2(1 + c))⁴e^{c²}/c`. -/
def KG2x (c t : ℝ) : ℝ :=
  (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * ‖xiF (1 / 2 + t * I)‖) ^ 2 * (2 * (1 + c)) ^ 4 * Real.exp (c ^ 2) / c

lemma KG2x_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ KG2x c t := by unfold KG2x; positivity

/-- `|ξ_F(½ + it + c + iv)| ≤ A|ξ_F(½ + it)|` with
`A = (2(1 + c)(1 + |v|))²e^{KR(c)}(1 + |t|)^{c/2}(1 + |v|)^{c/2+1/4}e^{π|v|/4}`. -/
lemma norm_xiF_ratio_le {c : ℝ} (hc : 0 ≤ c) (t v : ℝ) :
    ‖xiF (1 / 2 + t * I + (c + v * I))‖ ≤
      (2 * (1 + c) * (1 + |v|)) ^ 2 * (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) *
        Real.exp (Real.pi * |v| / 4)) * ‖xiF (1 / 2 + t * I)‖ := by
  have h0 := norm_add_le_crit t c v hc 0 (Or.inl rfl)
  have h1 := norm_add_le_crit t c v hc 1 (Or.inr rfl)
  simp only [sub_zero] at h0
  have hG := norm_Gammaℝ_ratio_le hc t v
  unfold xiF
  rw [norm_mul, norm_mul, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_two]
  set A := 2 * (1 + c) * (1 + |v|) with hA
  have hA0 : 0 ≤ A := by positivity
  calc ‖1 / 2 + t * I + (c + v * I)‖ * ‖1 / 2 + t * I + (c + v * I) - 1‖ / 2 *
        ‖Gammaℝ (1 / 2 + t * I + (c + v * I))‖
      ≤ (A * ‖(1 / 2 + t * I : ℂ)‖) * (A * ‖1 / 2 + t * I - 1‖) / 2 *
          (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
            ‖Gammaℝ (1 / 2 + t * I)‖) := by gcongr
    _ = _ := by ring

/-- **The integrand on a vertical line**: for `c > 0`, `|G(c + iv)| ≤ KG2x(c, t)|M(½ + it + c + iv)|W_{c+9/2}(v)`. -/
lemma norm_GGx_le (M : ℂ → ℂ) {c : ℝ} (hc : 0 < c) (t v : ℝ) :
    ‖GGx M (1 / 2 + t * I) (c + v * I)‖ ≤ KG2x c t * ‖M (1 / 2 + t * I + (c + v * I))‖ * Wf (c + 9 / 2) v := by
  have hx := norm_xiF_ratio_le hc.le t v
  have hexp : ‖Complex.exp (((c : ℂ) + v * I) ^ 2)‖ = Real.exp (c ^ 2) * Real.exp (-v ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]; congr 1; simp [sq]; ring
  have hw : c ≤ ‖(c : ℂ) + v * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + v * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      add_zero] at this
    rwa [abs_of_pos hc] at this
  unfold GGx
  rw [norm_div, norm_mul, norm_mul, norm_pow, hexp]
  set m := ‖M (1 / 2 + t * I + (c + v * I))‖ with hm
  set g := ‖xiF (1 / 2 + t * I + (c + v * I))‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hv0 : (0 : ℝ) < 1 + |v| := by positivity
  have hpv : ((1 + |v|) ^ (c / 2 + 1 / 4)) ^ 2 * (1 + |v|) ^ 4 = (1 + |v|) ^ (c + 9 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le, ← Real.rpow_natCast (1 + |v|) 4, ← Real.rpow_add hv0]
    congr 1; push_cast; ring
  have hev : (Real.exp (Real.pi * |v| / 4)) ^ 2 = Real.exp (Real.pi * |v| / 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hnum : 0 ≤ g ^ 2 * m * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) := by positivity
  calc g ^ 2 * m * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / ‖(c : ℂ) + v * I‖
      ≤ g ^ 2 * m * (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / c :=
        div_le_div_of_nonneg_left hnum hc hw
    _ ≤ ((2 * (1 + c) * (1 + |v|)) ^ 2 * (Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) *
          Real.exp (Real.pi * |v| / 4)) * ‖xiF (1 / 2 + t * I)‖) ^ 2 * m *
            (Real.exp (c ^ 2) * Real.exp (-v ^ 2)) / c := by
        gcongr
    _ = KG2x c t * m * Wf (c + 9 / 2) v := by
        unfold KG2x Wf
        rw [← hpv, ← hev]
        field_simp

/-- `|G(x + iy)|(1 + |y|)² ≤ KG2x(b, t)·(b/a)·B·e^{(b+13/2)² + π²/4}` on the strip `a ≤ x ≤ b`, when `|M| ≤ B`
there. -/
lemma norm_GGx_strip_le (M : ℂ → ℂ) {a b : ℝ} (ha : 0 < a) (t : ℝ) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖M (1 / 2 + t * I + (x + y * I))‖ ≤ B) {x : ℝ} (hx : x ∈ Icc a b) (y : ℝ) :
    ‖GGx M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ^ 2 ≤
      KG2x b t * (b / a) * B * Real.exp ((b + 13 / 2) ^ 2 + Real.pi ^ 2 / 4) := by
  obtain ⟨hax, hxb⟩ := hx
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x ⟨hax, hxb⟩ y)
  have h1 := norm_GGx_le M hx0 t y
  have hK : KG2x x t ≤ KG2x b t * (b / a) := by
    unfold KG2x
    have e1 : Real.exp (KR x) ≤ Real.exp (KR b) := Real.exp_le_exp.2 (KR_mono hx0.le hxb)
    have e2 : (1 + |t|) ^ (x / 2) ≤ (1 + |t|) ^ (b / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    have e3 : Real.exp (x ^ 2) ≤ Real.exp (b ^ 2) := Real.exp_le_exp.2 (by nlinarith)
    have e4 : (2 * (1 + x)) ^ 4 ≤ (2 * (1 + b)) ^ 4 := by gcongr
    have e5 : 1 / x ≤ (b / a) / b := by
      have e : (b / a) / b = 1 / a := by field_simp
      rw [e]
      exact one_div_le_one_div_of_le ha hax
    have e6 : ∀ z : ℝ, 0 ≤ z → z / x ≤ z * ((b / a) / b) := fun z hz => by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left e5 hz
    calc (Real.exp (KR x) * (1 + |t|) ^ (x / 2) * ‖xiF (1 / 2 + t * I)‖) ^ 2 * (2 * (1 + x)) ^ 4 *
          Real.exp (x ^ 2) / x
        ≤ (Real.exp (KR x) * (1 + |t|) ^ (x / 2) * ‖xiF (1 / 2 + t * I)‖) ^ 2 * (2 * (1 + x)) ^ 4 *
          Real.exp (x ^ 2) * ((b / a) / b) := e6 _ (by positivity)
      _ ≤ (Real.exp (KR b) * (1 + |t|) ^ (b / 2) * ‖xiF (1 / 2 + t * I)‖) ^ 2 * (2 * (1 + b)) ^ 4 *
          Real.exp (b ^ 2) * ((b / a) / b) := by gcongr
      _ = _ := by field_simp
  have hW : Wf (x + 9 / 2) y * (1 + |y|) ^ 2 ≤ Real.exp ((b + 13 / 2) ^ 2 + Real.pi ^ 2 / 4) := by
    have e : Wf (x + 9 / 2) y * (1 + |y|) ^ 2 = Wf (x + 13 / 2) y := by
      rw [show x + 13 / 2 = x + 9 / 2 + 1 + 1 by ring, ← one_add_abs_mul_Wf, ← one_add_abs_mul_Wf]; ring
    rw [e]
    exact (Wf_mono (by linarith) y).trans (Wf_le' (by linarith) y)
  have hm := hB x ⟨hax, hxb⟩ y
  have hK0 := KG2x_nonneg hx0 t
  have hW0 := Wf_nonneg (x + 9 / 2) y
  have hKb := KG2x_nonneg hb0 t
  calc ‖GGx M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ^ 2
      ≤ KG2x x t * ‖M (1 / 2 + t * I + (x + y * I))‖ * Wf (x + 9 / 2) y * (1 + |y|) ^ 2 := by gcongr
    _ = KG2x x t * ‖M (1 / 2 + t * I + (x + y * I))‖ * (Wf (x + 9 / 2) y * (1 + |y|) ^ 2) := by ring
    _ ≤ (KG2x b t * (b / a)) * B * Real.exp ((b + 13 / 2) ^ 2 + Real.pi ^ 2 / 4) := by gcongr

lemma differentiableAt_xiF {z : ℂ} (h : 0 < z.re) : DifferentiableAt ℂ xiF z := by
  unfold xiF
  exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2).mul (differentiableAt_Gammaℝ h)

/-- `G` is holomorphic on `Re w > a`, for `M` holomorphic on `Re z > a + ½` and `Re s = ½`, `a ≥ 0`. -/
lemma differentiableOn_GGx {M : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hM : ∀ z : ℂ, a + 1 / 2 < z.re → DifferentiableAt ℂ M z)
    (t : ℝ) : DifferentiableOn ℂ (GGx M (1 / 2 + t * I)) {w | a < w.re} := by
  intro w hw
  have hw' : a < w.re := hw
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw'; simp at hw'; linarith
  have hre : (1 / 2 + t * I + w).re = 1 / 2 + w.re := by simp
  have h1 : DifferentiableAt ℂ (fun w => xiF (1 / 2 + t * I + w)) w :=
    (differentiableAt_xiF (by rw [hre]; linarith)).comp w (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun w => M (1 / 2 + t * I + w)) w :=
    (hM _ (by rw [hre]; linarith)).comp w (by fun_prop)
  have h4 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2)) w := by fun_prop
  exact (((h1.pow 2).mul h2).mul h4).div differentiableAt_id hw0 |>.differentiableWithinAt

lemma continuous_GGx_line {M : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ z : ℂ, a + 1 / 2 < z.re → DifferentiableAt ℂ M z) {c : ℝ} (hc : a < c) (t : ℝ) :
    Continuous fun v : ℝ => GGx M (1 / 2 + t * I) (c + v * I) := by
  have hd := differentiableOn_GGx ha hM t
  refine hd.continuousOn.comp_continuous (by fun_prop) fun v => ?_
  show a < ((c : ℂ) + v * I).re
  simp [hc]

/-- `G` is integrable on a vertical line `Re w = c > a` when `|M| ≤ B` there. -/
lemma integrable_GGx {M : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ z : ℂ, a + 1 / 2 < z.re → DifferentiableAt ℂ M z) {c : ℝ} (hc : a < c) (t : ℝ) {B : ℝ}
    (hB : ∀ y : ℝ, ‖M (1 / 2 + t * I + (c + y * I))‖ ≤ B) :
    Integrable fun v : ℝ => GGx M (1 / 2 + t * I) (c + v * I) :=
  InghamDensity.integrable_of_le_sq (continuous_GGx_line ha hM hc t) fun y =>
    norm_GGx_strip_le M (by linarith : 0 < c) t (a := c) (b := c) (fun x hx y' => by
      rw [show x = c from le_antisymm hx.2 hx.1]; exact hB y') ⟨le_rfl, le_rfl⟩ y

/-- `G` tends to `0` uniformly on the strip `a ≤ Re w ≤ b` when `|M| ≤ B` there. -/
lemma decay_GGx (M : ℂ → ℂ) {a b : ℝ} (ha : 0 < a) (t : ℝ) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖M (1 / 2 + t * I + (x + y * I))‖ ≤ B) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T₀ ≤ |y| → ‖GGx M (1 / 2 + t * I) (x + y * I)‖ ≤ η := by
  intro η hη
  set C := KG2x b t * (b / a) * B * Real.exp ((b + 13 / 2) ^ 2 + Real.pi ^ 2 / 4) with hC
  refine ⟨C / η, fun x hx y hy => ?_⟩
  have hb := norm_GGx_strip_le M ha t hB hx y
  have hpos : 0 < 1 + |y| := by positivity
  have h2 : 1 + |y| ≤ (1 + |y|) ^ 2 := le_self_pow₀ (by linarith [abs_nonneg y]) (by norm_num)
  have hCη : C ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hy
  have hG0 := norm_nonneg (GGx M (1 / 2 + t * I) (x + y * I))
  have : ‖GGx M (1 / 2 + t * I) (x + y * I)‖ * (1 + |y|) ≤ η * (1 + |y|) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hG0]
  exact le_of_mul_le_mul_right this hpos

/-! ### The contour split `J = J_P + J_T` -/

lemma differentiableAt_Pd (N₀ : ℕ) (z : ℂ) : DifferentiableAt ℂ (Pd χ₁ N₀) z := differentiable_Pd χ₁ N₀ z

lemma differentiableAt_Tl {N₀ : ℕ} {z : ℂ} (hz : 1 < z.re) : DifferentiableAt ℂ (Tl χ₁ N₀) z := by
  have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
  have hL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ₁) z := by
    rw [LFunction_χ₁]; exact differentiableAt_riemannZeta hz1
  unfold Tl
  exact (hL.pow 2).sub (differentiable_Pd χ₁ N₀ z)

/-- **The split of `J`**: for `0 < c₀ ≤ 2 ≤ c₁`, `J(½ + it) = (1/2πi)∫_{(c₀)} G_P + (1/2πi)∫_{(c₁)} G_T` with
`G_P = ξ_F²P e^{w²}/w` and `G_T = ξ_F²T e^{w²}/w`: on `Re w = 2` the integrand is `G_P + G_T`, and each piece moves to
its own line with no pole crossed. -/
theorem afeJx_split (N₀ : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₀2 : c₀ ≤ 2) (hc₁ : 2 ≤ c₁) (t : ℝ) :
    afeJx (1 / 2 + t * I) = VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t * I)) c₀ +
      VerticalIntegral' (GGx (Tl χ₁ N₀) (1 / 2 + t * I)) c₁ := by
  have hre : ∀ x y : ℝ, (1 / 2 + t * I + ((x : ℂ) + y * I)).re = 1 / 2 + x := fun x y => by simp
  have hPd : ∀ z : ℂ, (0 : ℝ) + 1 / 2 < z.re → DifferentiableAt ℂ (Pd χ₁ N₀) z :=
    fun z _ => differentiableAt_Pd N₀ z
  have hTd : ∀ z : ℂ, (1 : ℝ) + 1 / 2 < z.re → DifferentiableAt ℂ (Tl χ₁ N₀) z :=
    fun z hz => differentiableAt_Tl (by linarith)
  have hPdB : ∀ x ∈ Icc c₀ 2, ∀ y : ℝ, ‖Pd χ₁ N₀ (1 / 2 + t * I + (x + y * I))‖ ≤ (N₀ : ℝ) ^ 2 :=
    fun x hx y => norm_Pd_le χ₁ N₀ (by rw [hre]; linarith [hx.1])
  have hTlB : ∀ x ∈ Icc 2 c₁, ∀ y : ℝ,
      ‖Tl χ₁ N₀ (1 / 2 + t * I + (x + y * I))‖ ≤ ChiUniform.zeta32 ^ 2 + (N₀ : ℝ) ^ 2 :=
    fun x hx y => norm_Tl_le_crude χ₁ N₀ (by rw [hre]; linarith [hx.1])
  have hiP2 := integrable_GGx le_rfl hPd (by norm_num : (0 : ℝ) < 2) t (fun y => hPdB 2 ⟨hc₀2, le_rfl⟩ y)
  have hiP0 := integrable_GGx le_rfl hPd hc₀ t (fun y => hPdB c₀ ⟨le_rfl, hc₀2⟩ y)
  have hiT2 := integrable_GGx zero_le_one hTd (by norm_num : (1 : ℝ) < 2) t (fun y => hTlB 2 ⟨le_rfl, hc₁⟩ y)
  have hiT1 := integrable_GGx zero_le_one hTd (by linarith : (1 : ℝ) < c₁) t (fun y => hTlB c₁ ⟨hc₁, le_rfl⟩ y)
  have hsplit2 : ∀ v : ℝ, afeGx (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) =
      GGx (Pd χ₁ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) +
        GGx (Tl χ₁ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) := by
    intro v
    have hne : 1 / 2 + t * I + (((2 : ℝ) : ℂ) + v * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hre] at this; norm_num at this
    rw [afeGx_eq_GGx (by rw [hre]; norm_num) hne, ← GGx_add]
    congr 1
    funext z
    unfold Tl
    rw [LFunction_χ₁]
    ring
  have hfun : (fun v : ℝ => afeGx (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I)) =
      fun v : ℝ => GGx (Pd χ₁ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) +
        GGx (Tl χ₁ N₀) (1 / 2 + t * I) (((2 : ℝ) : ℂ) + v * I) := funext hsplit2
  have hsub : ∀ {a a' b : ℝ}, a' < a → Icc a b ×ℂ univ ⊆ {w : ℂ | a' < w.re} := fun ha w hw => by
    rw [mem_reProdIm] at hw
    show _ < w.re
    linarith [hw.1.1]
  have hshP : VerticalIntegral (GGx (Pd χ₁ N₀) (1 / 2 + t * I)) 2 =
      VerticalIntegral (GGx (Pd χ₁ N₀) (1 / 2 + t * I)) c₀ :=
    SmoothPerron.verticalIntegral_shift hc₀2 ((differentiableOn_GGx le_rfl hPd t).mono (hsub hc₀))
      hiP2 hiP0 (decay_GGx _ hc₀ t hPdB)
  have hshT : VerticalIntegral (GGx (Tl χ₁ N₀) (1 / 2 + t * I)) c₁ =
      VerticalIntegral (GGx (Tl χ₁ N₀) (1 / 2 + t * I)) 2 :=
    SmoothPerron.verticalIntegral_shift hc₁ ((differentiableOn_GGx zero_le_one hTd t).mono
      (hsub (by norm_num : (1 : ℝ) < 2))) hiT1 hiT2 (decay_GGx _ (by norm_num : (0 : ℝ) < 2) t hTlB)
  simp only [afeJx, VerticalIntegral', VerticalIntegral] at hshP hshT ⊢
  rw [hfun, integral_add hiP2 hiT2, smul_add, smul_add, hshP, ← hshT]

/-! ### The polynomial part `D_P` -/

/-- `KG2x = KG3x·|ξ_F(½ + it)|²`. -/
def KG3x (c t : ℝ) : ℝ := (Real.exp (KR c) * (1 + |t|) ^ (c / 2)) ^ 2 * (2 * (1 + c)) ^ 4 * Real.exp (c ^ 2) / c

lemma KG2x_eq (c t : ℝ) : KG2x c t = KG3x c t * ‖xiF (1 / 2 + t * I)‖ ^ 2 := by
  unfold KG2x KG3x; ring

lemma KG3x_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ KG3x c t := by unfold KG3x; positivity

lemma KG3x_mono {c t T : ℝ} (hc : 0 < c) (htT : |t| ≤ |T|) : KG3x c t ≤ KG3x c T := by
  unfold KG3x
  have h : (1 + |t|) ^ (c / 2) ≤ (1 + |T|) ^ (c / 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  gcongr

/-- `|J_c(G)/ξ_F(½ + it)²| ≤ KG3x(c, t)/(2π)·∫ |M(½ + it + c + iv)|W_{c+9/2}(v) dv`. -/
lemma norm_VI'_GGx_div_le (M : ℂ → ℂ) {c : ℝ} (hc : 0 < c) (t : ℝ)
    (hint : Integrable fun v : ℝ => ‖M (1 / 2 + t * I + (c + v * I))‖ * Wf (c + 9 / 2) v) :
    ‖VerticalIntegral' (GGx M (1 / 2 + t * I)) c / xiF (1 / 2 + t * I) ^ 2‖ ≤
      KG3x c t / (2 * π) * ∫ v : ℝ, ‖M (1 / 2 + t * I + ((c : ℂ) + (v : ℂ) * I))‖ * Wf (c + 9 / 2) v := by
  have hγ : xiF (1 / 2 + t * I) ≠ 0 := xiF_ne_zero t
  have hγn : 0 < ‖xiF (1 / 2 + t * I)‖ ^ 2 := pow_pos (norm_pos_iff.2 hγ) 2
  have h := norm_verticalIntegral'_le (G := GGx M (1 / 2 + t * I)) (c := c)
    (hint.const_mul (KG2x c t)) (fun (v : ℝ) => by
      have := norm_GGx_le M hc t v
      calc _ ≤ _ := this
        _ = KG2x c t * (‖M (1 / 2 + t * I + ((c : ℂ) + (v : ℂ) * I))‖ * Wf (c + 9 / 2) v) := by ring)
  rw [integral_const_mul, KG2x_eq] at h
  rw [norm_div, norm_pow, div_le_iff₀ hγn]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **The polynomial part at well-spaced points**: for `0 < c₀ ≤ ½` and 1-separated points `|t_r| ≤ T`,
`Σ_r |J_{c₀}(G_P)/ξ_F(½ + it_r)²|² ≤ (KG3x(c₀, T)/2π)²·∫W_{c₀+9/2}·LSb(T + 1)·∫W_{c₀+11/2}`: Cauchy–Schwarz in `v`
against `W_{c₀+9/2}`, then `sum_norm_Pd_sq_le_sep` at the points `t_r + v` for each `v`. -/
theorem sum_norm_DP_sq_le_sep {ι : Type*} {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 2)
    (Rs : Finset ι) {T : ℝ} (hT : 0 ≤ T) (t : ι → ℝ) (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |t r - t s|)
    (ht : ∀ r ∈ Rs, |t r| ≤ T) :
    ∑ r ∈ Rs, ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ / xiF (1 / 2 + t r * I) ^ 2‖ ^ 2 ≤
      (KG3x c₀ T / (2 * π)) ^ 2 * (∫ v, Wf (c₀ + 9 / 2) v) *
        (LSb Rs.card 1 N₀ (T + 1) * ∫ v, Wf (c₀ + 11 / 2) v) := by
  set W := Wf (c₀ + 9 / 2) with hWdef
  set p : ι → ℝ → ℝ := fun r v => ‖Pd χ₁ N₀ (1 / 2 + t r * I + ((c₀ : ℂ) + (v : ℂ) * I))‖ with hp
  have hW0 : ∀ v, 0 ≤ W v := Wf_nonneg _
  have hWi : Integrable W := integrable_Wf (by linarith)
  have hWpos : 0 < ∫ v, W v := integral_Wf_pos (by linarith)
  have hpc : ∀ r, Continuous (p r) := fun r =>
    ((differentiable_Pd χ₁ N₀).continuous.comp (by fun_prop)).norm
  have hpb : ∀ r v, p r v ≤ (N₀ : ℝ) ^ 2 := fun r v => norm_Pd_le χ₁ N₀ (by simp; linarith)
  have hp0 : ∀ r v, 0 ≤ p r v := fun r v => norm_nonneg _
  have hi1 : ∀ r, Integrable fun v => p r v * W v := fun r =>
    (hWi.const_mul ((N₀ : ℝ) ^ 2)).mono' ((hpc r).mul (continuous_Wf _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 r v) (hW0 v))]
        exact mul_le_mul_of_nonneg_right (hpb r v) (hW0 v))
  have hi2 : ∀ r, Integrable fun v => p r v ^ 2 * W v := fun r =>
    (hWi.const_mul ((N₀ : ℝ) ^ 2 * (N₀ : ℝ) ^ 2)).mono'
      (((hpc r).pow 2).mul (continuous_Wf _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hW0 v))]
        have h := hpb r v
        have h2 : p r v ^ 2 ≤ (N₀ : ℝ) ^ 2 * (N₀ : ℝ) ^ 2 := by nlinarith [hp0 r v]
        exact mul_le_mul_of_nonneg_right h2 (hW0 v))
  set K := KG3x c₀ T / (2 * π) with hK
  have hK0 : 0 ≤ K := div_nonneg (KG3x_nonneg hc₀ T) (by positivity)
  -- each point
  have hone : ∀ r ∈ Rs, ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ /
      xiF (1 / 2 + t r * I) ^ 2‖ ^ 2 ≤ K ^ 2 * ((∫ v, W v) * ∫ v, p r v ^ 2 * W v) := by
    intro r hr
    have h := norm_VI'_GGx_div_le (Pd χ₁ N₀) hc₀ (t r) (hi1 r)
    have hKm : KG3x c₀ (t r) / (2 * π) ≤ K :=
      div_le_div_of_nonneg_right (KG3x_mono hc₀ (by rw [abs_of_nonneg hT]; exact ht r hr)) (by positivity)
    have hI0 : 0 ≤ ∫ v, p r v * W v := integral_nonneg fun v => mul_nonneg (hp0 r v) (hW0 v)
    have h' : ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ /
        xiF (1 / 2 + t r * I) ^ 2‖ ≤ K * ∫ v, p r v * W v :=
      h.trans (mul_le_mul_of_nonneg_right hKm hI0)
    have hcs := sq_integral_mul_le hW0 hWi hWpos (hi1 r) (hi2 r)
    calc _ ≤ (K * ∫ v, p r v * W v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
      _ = K ^ 2 * (∫ v, p r v * W v) ^ 2 := by ring
      _ ≤ K ^ 2 * ((∫ v, W v) * ∫ v, p r v ^ 2 * W v) := by gcongr
  -- the pointwise large-values bound
  have hpt : ∀ v, ∑ r ∈ Rs, p r v ^ 2 * W v ≤ LSb Rs.card 1 N₀ (T + 1) * Wf (c₀ + 11 / 2) v := by
    intro v
    have hLV := sum_norm_Pd_sq_le_sep hN₀ hc₀ hc₀' Rs (X := T + |v|) (by positivity) (fun r => t r + v)
      (fun r hr s hs hrs => by
        rw [show t r + v - (t s + v) = t r - t s by ring]; exact hsep r hr s hs hrs)
      (fun r hr => (abs_add_le _ _).trans (by linarith [ht r hr]))
    have e : ∀ r : ι, Pd χ₁ N₀ (((1 / 2 + c₀ : ℝ) : ℂ) + ((t r + v : ℝ) : ℂ) * I) =
        Pd χ₁ N₀ (1 / 2 + t r * I + ((c₀ : ℂ) + (v : ℂ) * I)) := by
      intro r; congr 1; push_cast; ring
    simp only [e] at hLV
    have hsh := LSb_shift_le Rs.card 1 N₀ hN₀ hT (abs_nonneg v)
    have hLV' : ∑ r ∈ Rs, p r v ^ 2 ≤ LSb Rs.card 1 N₀ (T + |v|) := hLV
    calc ∑ r ∈ Rs, p r v ^ 2 * W v = (∑ r ∈ Rs, p r v ^ 2) * W v := by rw [sum_mul]
      _ ≤ LSb Rs.card 1 N₀ (T + |v|) * W v := mul_le_mul_of_nonneg_right hLV' (hW0 v)
      _ ≤ (LSb Rs.card 1 N₀ (T + 1) * (1 + |v|)) * W v := mul_le_mul_of_nonneg_right hsh (hW0 v)
      _ = LSb Rs.card 1 N₀ (T + 1) * Wf (c₀ + 11 / 2) v := by
          rw [mul_assoc, hWdef, one_add_abs_mul_Wf, show c₀ + 9 / 2 + 1 = c₀ + 11 / 2 by ring]
  have hsumint : ∫ v, ∑ r ∈ Rs, p r v ^ 2 * W v ≤ LSb Rs.card 1 N₀ (T + 1) * ∫ v, Wf (c₀ + 11 / 2) v := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finsetSum Rs fun r _ => hi2 r)
      ((integrable_Wf (by linarith)).const_mul _) hpt
  have hA0 : 0 ≤ ∫ v, W v := hWpos.le
  calc _ ≤ ∑ r ∈ Rs, K ^ 2 * ((∫ v, W v) * ∫ v, p r v ^ 2 * W v) := sum_le_sum hone
    _ = K ^ 2 * (∫ v, W v) * ∫ v, ∑ r ∈ Rs, p r v ^ 2 * W v := by
        rw [integral_finsetSum Rs fun r _ => hi2 r, mul_sum]
        exact sum_congr rfl fun r _ => by ring
    _ ≤ K ^ 2 * (∫ v, W v) * (LSb Rs.card 1 N₀ (T + 1) * ∫ v, Wf (c₀ + 11 / 2) v) := by gcongr

/-- **The tail part**: for `c₁ ≥ 5/2` and `|t| ≤ T`,
`|J_{c₁}(G_T)/ξ_F(½ + it)²| ≤ KG3x(c₁, T)/(2π)·2N₀^{5/2−c₁}·∫W_{c₁+9/2}` (`norm_Tl_le` on `Re z = ½ + c₁`). -/
theorem norm_DTx_le {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₁ : ℝ} (hc₁ : 5 / 2 ≤ c₁) {T t : ℝ} (hT : 0 ≤ T) (htT : |t| ≤ T) :
    ‖VerticalIntegral' (GGx (Tl χ₁ N₀) (1 / 2 + t * I)) c₁ / xiF (1 / 2 + t * I) ^ 2‖ ≤
      KG3x c₁ T / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 9 / 2) v) := by
  have hc₁0 : 0 < c₁ := by linarith
  set q : ℝ → ℝ := fun v => ‖Tl χ₁ N₀ (1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I))‖ with hq
  have hre : ∀ v : ℝ, (1 / 2 + (t : ℂ) * I + ((c₁ : ℂ) + (v : ℂ) * I)).re = 1 / 2 + c₁ := fun v => by simp
  have hqb : ∀ v, q v ≤ 2 * (N₀ : ℝ) ^ (5 / 2 - c₁) := fun v => by
    have h := norm_Tl_le χ₁ hN₀ (z := 1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I)) (by rw [hre]; linarith)
    rw [hre, show (3 : ℝ) - (1 / 2 + c₁) = 5 / 2 - c₁ by ring] at h
    exact h
  have hq0 : ∀ v, 0 ≤ q v := fun v => norm_nonneg _
  have hqc : Continuous q := by
    have hcont : Continuous fun v : ℝ => Tl χ₁ N₀ (1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I)) := by
      refine continuous_iff_continuousAt.2 fun v => ?_
      have hd := differentiableAt_Tl (N₀ := N₀) (z := 1 / 2 + t * I + ((c₁ : ℂ) + (v : ℂ) * I))
        (by rw [hre]; linarith)
      exact ContinuousAt.comp (g := Tl χ₁ N₀) (f := fun v : ℝ => 1 / 2 + (t : ℂ) * I + ((c₁ : ℂ) + (v : ℂ) * I))
        hd.continuousAt (by fun_prop)
    exact hcont.norm
  have hWi := integrable_Wf (a := c₁ + 9 / 2) (by linarith)
  have hint : Integrable fun v => q v * Wf (c₁ + 9 / 2) v :=
    (hWi.const_mul (2 * (N₀ : ℝ) ^ (5 / 2 - c₁))).mono' (hqc.mul (continuous_Wf _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 v) (Wf_nonneg _ v))]
        exact mul_le_mul_of_nonneg_right (hqb v) (Wf_nonneg _ v))
  have h := norm_VI'_GGx_div_le (Tl χ₁ N₀) hc₁0 t hint
  have hKm : KG3x c₁ t / (2 * π) ≤ KG3x c₁ T / (2 * π) :=
    div_le_div_of_nonneg_right (KG3x_mono hc₁0 (by rw [abs_of_nonneg hT]; exact htT)) (by positivity)
  have hI : ∫ v, q v * Wf (c₁ + 9 / 2) v ≤ 2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 9 / 2) v := by
    rw [← integral_const_mul]
    exact integral_mono hint (hWi.const_mul _) fun v => mul_le_mul_of_nonneg_right (hqb v) (Wf_nonneg _ v)
  have hI0 : 0 ≤ ∫ v, q v * Wf (c₁ + 9 / 2) v := integral_nonneg fun v => mul_nonneg (hq0 v) (Wf_nonneg _ v)
  calc _ ≤ KG3x c₁ t / (2 * π) * ∫ v, q v * Wf (c₁ + 9 / 2) v := h
    _ ≤ KG3x c₁ T / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 9 / 2) v) :=
        mul_le_mul hKm hI hI0 (div_nonneg (KG3x_nonneg hc₁0 T) (by positivity))

/-! ### Assembly -/

/-- The bound of `sum_norm_DP_sq_le_sep`. -/
def DPx (c₀ T : ℝ) (R N₀ : ℕ) : ℝ :=
  (KG3x c₀ T / (2 * π)) ^ 2 * (∫ v, Wf (c₀ + 9 / 2) v) * (LSb R 1 N₀ (T + 1) * ∫ v, Wf (c₀ + 11 / 2) v)

/-- The bound of `norm_DTx_le`. -/
def BTx (c₁ T : ℝ) (N₀ : ℕ) : ℝ := KG3x c₁ T / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - c₁) * ∫ v, Wf (c₁ + 9 / 2) v)

/-- **`D = D_P + D_T` and the explicit bound**: for 1-separated points `|t_r| ≤ T`, `N₀ ≥ 1`, `0 < c₀ ≤ ½` and
`c₁ ≥ 5/2`, `Σ_r |D(½ + it_r)|² ≤ 2·DPx + 2#R·BTx²`. -/
theorem sum_norm_afeDx_sq_le_explicit {ι : Type*} {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 1 / 2) (hc₁ : 5 / 2 ≤ c₁) (Rs : Finset ι) {T : ℝ} (hT : 0 ≤ T) (t : ι → ℝ)
    (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |t r - t s|) (ht : ∀ r ∈ Rs, |t r| ≤ T) :
    ∑ r ∈ Rs, ‖afeDx (1 / 2 + t r * I)‖ ^ 2 ≤ 2 * DPx c₀ T Rs.card N₀ + 2 * (Rs.card * BTx c₁ T N₀ ^ 2) := by
  have hpt : ∀ r ∈ Rs, ‖afeDx (1 / 2 + t r * I)‖ ^ 2 ≤
      2 * ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ / xiF (1 / 2 + t r * I) ^ 2‖ ^ 2 +
        2 * BTx c₁ T N₀ ^ 2 := by
    intro r hr
    unfold afeDx
    rw [afeJx_split N₀ (c₁ := c₁) hc₀ (by linarith) (by linarith) (t r), add_div]
    exact norm_add_sq_le' (norm_DTx_le hN₀ hc₁ hT (ht r hr))
  have hP := sum_norm_DP_sq_le_sep hN₀ hc₀ hc₀' Rs hT t hsep ht
  calc ∑ r ∈ Rs, ‖afeDx (1 / 2 + t r * I)‖ ^ 2
      ≤ ∑ r ∈ Rs, (2 * ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ /
          xiF (1 / 2 + t r * I) ^ 2‖ ^ 2 + 2 * BTx c₁ T N₀ ^ 2) := sum_le_sum hpt
    _ = 2 * ∑ r ∈ Rs, ‖VerticalIntegral' (GGx (Pd χ₁ N₀) (1 / 2 + t r * I)) c₀ /
          xiF (1 / 2 + t r * I) ^ 2‖ ^ 2 + 2 * (Rs.card * BTx c₁ T N₀ ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * DPx c₀ T Rs.card N₀ + 2 * (Rs.card * BTx c₁ T N₀ ^ 2) := by
        unfold DPx
        exact add_le_add (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)) le_rfl

/-! ### The exponents -/

/-- `KG3x(c, T) ≤ e^{2KR(c)}(2(1 + c))⁴e^{c²}/c·(T + 2)^c`. -/
lemma KG3x_le {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) :
    KG3x c T ≤ Real.exp (2 * KR c) * (2 * (1 + c)) ^ 4 * Real.exp (c ^ 2) / c * (T + 2) ^ c := by
  unfold KG3x
  rw [abs_of_nonneg hT]
  have e1 : Real.exp (KR c) ^ 2 = Real.exp (2 * KR c) := by
    rw [← Real.exp_nat_mul]; norm_num
  have e2 : ((1 + T) ^ (c / 2)) ^ 2 = (1 + T) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  rw [mul_pow, e1, e2]
  have h2 : (1 + T) ^ c ≤ (T + 2) ^ c := Real.rpow_le_rpow (by positivity) (by linarith) hc.le
  calc Real.exp (2 * KR c) * (1 + T) ^ c * (2 * (1 + c)) ^ 4 * Real.exp (c ^ 2) / c
      = Real.exp (2 * KR c) * (2 * (1 + c)) ^ 4 * Real.exp (c ^ 2) / c * (1 + T) ^ c := by ring
    _ ≤ _ := by gcongr

/-- `LSb(R, 1, N₀, T + 1) ≤ (2 + 256e)((T + 2) + N₀)(1 + log 2N₀)⁸` for `R ≤ (T + 2) + N₀`. -/
lemma LSb_le_sep {R N₀ : ℕ} (hN₀ : 1 ≤ N₀) {T : ℝ} (hT : 0 ≤ T) (hR : (R : ℝ) ≤ (T + 2) + N₀) :
    LSb R 1 N₀ (T + 1) ≤ (2 + 256 * Real.exp 1) * ((T + 2) + N₀) * (1 + Real.log (2 * N₀)) ^ 8 := by
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hl1 : 0 ≤ Real.log N₀ := Real.log_nonneg hN₀r
  have hl2 : 0 ≤ Real.log (2 * N₀) := Real.log_nonneg (by linarith)
  have hl12 : Real.log N₀ ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
  unfold LSb
  refine alg_bound hR (by positivity) (by linarith) (Nat.cast_nonneg _)
    (natLog_two_add_one_le hN₀) (Real.exp_pos 1).le (by positivity) ?_ (by positivity) (by nlinarith)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log N₀ ≤ 1 + Real.log (2 * N₀))
    (by linarith : (0 : ℝ) ≤ 8 * N₀), mul_nonneg (by linarith : (0 : ℝ) ≤ T + 2) hl2,
    mul_nonneg (by linarith : (0 : ℝ) ≤ N₀) hl2]

/-- **The second moment of `D` at well-spaced points**: for every `0 < ε ≤ 1` there is `C` with
`Σ_r |D(½ + it_r)|² ≤ C(T + 2)^{1+ε}` for every family of 1-separated points `|t_r| ≤ T`; at `δ = ε/8`, `c₀ = δ`,
`c₁ = 5/δ`, `N₀ = ⌈(T + 2)^{1+δ}⌉`. -/
theorem sum_norm_afeDx_sq_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ {ι : Type*} (Rs : Finset ι) (t : ι → ℝ), (∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |t r - t s|) →
      ∀ T : ℝ, 0 ≤ T → (∀ r ∈ Rs, |t r| ≤ T) →
        ∑ r ∈ Rs, ‖afeDx (1 / 2 + t r * I)‖ ^ 2 ≤ C * (T + 2) ^ (1 + ε) := by
  have hδ0 : 0 < ε / 8 := by positivity
  have hc₁5 : 5 / 2 ≤ 5 / (ε / 8) := by rw [le_div_iff₀ hδ0]; nlinarith
  have hc₁0 : 0 < 5 / (ε / 8) := by positivity
  have hδc : ε / 8 * (5 / (ε / 8)) = 5 := by field_simp
  obtain ⟨A₀, hA₀⟩ : ∃ x : ℝ,
      x = Real.exp (2 * KR (ε / 8)) * (2 * (1 + ε / 8)) ^ 4 * Real.exp ((ε / 8) ^ 2) / (ε / 8) := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = Real.exp (2 * KR (5 / (ε / 8))) * (2 * (1 + 5 / (ε / 8))) ^ 4 *
      Real.exp ((5 / (ε / 8)) ^ 2) / (5 / (ε / 8)) := ⟨_, rfl⟩
  obtain ⟨I₁, hI₁⟩ : ∃ x : ℝ, x = ∫ v, Wf (ε / 8 + 9 / 2) v := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ x : ℝ, x = ∫ v, Wf (ε / 8 + 11 / 2) v := ⟨_, rfl⟩
  obtain ⟨I₃, hI₃⟩ : ∃ x : ℝ, x = ∫ v, Wf (5 / (ε / 8) + 9 / 2) v := ⟨_, rfl⟩
  obtain ⟨CL, hCL⟩ : ∃ x : ℝ, x = (2 + 256 * Real.exp 1) * 3 * ((1 + 1 / (ε / 8 / 16)) ^ 8 * 4 ^ (ε / 8 / 2)) :=
    ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hI₁0 : 0 ≤ I₁ := by rw [hI₁]; exact (integral_Wf_pos (by linarith)).le
  have hI₂0 : 0 ≤ I₂ := by rw [hI₂]; exact (integral_Wf_pos (by linarith)).le
  have hI₃0 : 0 ≤ I₃ := by rw [hI₃]; exact (integral_Wf_pos (by linarith)).le
  have hCL0 : 0 ≤ CL := by rw [hCL]; positivity
  refine ⟨2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂)) + 4 * (A₁ / (2 * π) * (2 * I₃)) ^ 2,
    fun Rs t hsep T hT ht => ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ x : ℝ, x = T + 2 := ⟨_, rfl⟩
  rw [← hQ]
  have hQ1 : 1 ≤ Q := by rw [hQ]; linarith
  have hQ0 : 0 < Q := by linarith
  have hQδ1 : 1 ≤ Q ^ (1 + ε / 8) := Real.one_le_rpow hQ1 (by linarith)
  obtain ⟨N₀, hN₀def⟩ : ∃ n : ℕ, n = ⌈Q ^ (1 + ε / 8)⌉₊ := ⟨_, rfl⟩
  have hN₀ge : Q ^ (1 + ε / 8) ≤ N₀ := by rw [hN₀def]; exact Nat.le_ceil _
  have hN₀le : (N₀ : ℝ) ≤ 2 * Q ^ (1 + ε / 8) := by
    rw [hN₀def]
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Q ^ (1 + ε / 8))
    linarith
  have hN₀1 : 1 ≤ N₀ := by exact_mod_cast (show (1 : ℝ) ≤ N₀ by linarith)
  have hQQ : Q ≤ Q ^ (1 + ε / 8) := by
    calc Q = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
      _ ≤ Q ^ (1 + ε / 8) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hcard := card_le_of_sep Rs t hsep hT ht
  have hR : (Rs.card : ℝ) ≤ 2 * Q := by rw [hQ]; linarith
  have hRN : (Rs.card : ℝ) ≤ (T + 2) + N₀ := by rw [← hQ]; linarith
  have hmain := sum_norm_afeDx_sq_le_explicit hN₀1 hδ0 (by linarith : ε / 8 ≤ 1 / 2) hc₁5 Rs hT t hsep ht
  refine hmain.trans ?_
  -- the polynomial part
  have hKP : KG3x (ε / 8) T ≤ A₀ * Q ^ (ε / 8) := by rw [hA₀, hQ]; exact KG3x_le hδ0 hT
  have hKsq : (KG3x (ε / 8) T / (2 * π)) ^ 2 ≤ (A₀ / (2 * π)) ^ 2 * Q ^ (ε / 4) := by
    have h0 := KG3x_nonneg hδ0 T
    have h1 : (KG3x (ε / 8) T / (2 * π)) ^ 2 ≤ (A₀ * Q ^ (ε / 8) / (2 * π)) ^ 2 := by gcongr
    have h2 : (Q ^ (ε / 8)) ^ 2 = Q ^ (ε / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
    calc _ ≤ _ := h1
      _ = (A₀ / (2 * π)) ^ 2 * (Q ^ (ε / 8)) ^ 2 := by ring
      _ = _ := by rw [h2]
  have hLS : LSb Rs.card 1 N₀ (T + 1) ≤ CL * Q ^ (1 + ε / 4) := by
    have h1 := LSb_le_sep hN₀1 hT hRN
    rw [← hQ] at h1
    have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
    have hsum : Q + N₀ ≤ 3 * Q ^ (1 + ε / 8) := by linarith
    have hlog := one_add_log_pow_le (M := 2 * N₀) (a := ε / 8 / 16) (by linarith) (by positivity) 8
    have e8 : ((8 : ℕ) : ℝ) * (ε / 8 / 16) = ε / 8 / 2 := by push_cast; ring
    rw [e8] at hlog
    have h2N : 2 * (N₀ : ℝ) ≤ 4 * Q ^ (2 : ℝ) := by
      have : Q ^ (1 + ε / 8) ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      linarith
    have hpow : (2 * (N₀ : ℝ)) ^ (ε / 8 / 2) ≤ 4 ^ (ε / 8 / 2) * Q ^ (ε / 8) := by
      calc (2 * (N₀ : ℝ)) ^ (ε / 8 / 2) ≤ (4 * Q ^ (2 : ℝ)) ^ (ε / 8 / 2) :=
            Real.rpow_le_rpow (by positivity) h2N (by positivity)
        _ = 4 ^ (ε / 8 / 2) * (Q ^ (2 : ℝ)) ^ (ε / 8 / 2) := Real.mul_rpow (by norm_num) (by positivity)
        _ = 4 ^ (ε / 8 / 2) * Q ^ (ε / 8) := by
            rw [← Real.rpow_mul hQ0.le]; congr 2; ring
    have hL0 : 0 ≤ (1 + 1 / (ε / 8 / 16)) ^ 8 := by positivity
    have hlog' : (1 + Real.log (2 * N₀)) ^ 8 ≤ (1 + 1 / (ε / 8 / 16)) ^ 8 * (4 ^ (ε / 8 / 2) * Q ^ (ε / 8)) :=
      hlog.trans (mul_le_mul_of_nonneg_left hpow hL0)
    have hc : 0 ≤ 2 + 256 * Real.exp 1 := by positivity
    have hQN0 : 0 ≤ Q + N₀ := by positivity
    have hQe : Q ^ (1 + ε / 8) * Q ^ (ε / 8) = Q ^ (1 + ε / 4) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    calc LSb Rs.card 1 N₀ (T + 1) ≤ (2 + 256 * Real.exp 1) * (Q + N₀) * (1 + Real.log (2 * N₀)) ^ 8 := h1
      _ ≤ (2 + 256 * Real.exp 1) * (3 * Q ^ (1 + ε / 8)) *
          ((1 + 1 / (ε / 8 / 16)) ^ 8 * (4 ^ (ε / 8 / 2) * Q ^ (ε / 8))) := by gcongr
      _ = (2 + 256 * Real.exp 1) * 3 * ((1 + 1 / (ε / 8 / 16)) ^ 8 * 4 ^ (ε / 8 / 2)) *
          (Q ^ (1 + ε / 8) * Q ^ (ε / 8)) := by ring
      _ = CL * Q ^ (1 + ε / 4) := by rw [hQe, hCL]
  have hDP : DPx (ε / 8) T Rs.card N₀ ≤ (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * Q ^ (1 + ε / 2) := by
    unfold DPx
    rw [← hI₁, ← hI₂]
    have hLS0 : 0 ≤ LSb Rs.card 1 N₀ (T + 1) := by
      unfold LSb
      have hl : 0 ≤ Real.log (2 * N₀) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
        linarith)
      have hl' : 0 ≤ Real.log N₀ := Real.log_nonneg (by exact_mod_cast hN₀1)
      have h3 : 0 ≤ (1 + Real.log (2 * N₀)) ^ 3 := pow_nonneg (by linarith) 3
      have : 0 ≤ ((1 : ℕ) : ℝ) * (2 * (T + 1) + 1) := by positivity
      positivity
    have hQe : Q ^ (ε / 4) * Q ^ (1 + ε / 4) = Q ^ (1 + ε / 2) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    calc (KG3x (ε / 8) T / (2 * π)) ^ 2 * I₁ * (LSb Rs.card 1 N₀ (T + 1) * I₂)
        ≤ ((A₀ / (2 * π)) ^ 2 * Q ^ (ε / 4)) * I₁ * ((CL * Q ^ (1 + ε / 4)) * I₂) := by gcongr
      _ = (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * (Q ^ (ε / 4) * Q ^ (1 + ε / 4)) := by ring
      _ = _ := by rw [hQe]
  -- the tail part
  have hBT : BTx (5 / (ε / 8)) T N₀ ≤ A₁ / (2 * π) * (2 * I₃) := by
    unfold BTx
    rw [← hI₃]
    have hK := KG3x_le hc₁0 hT
    rw [← hA₁, ← hQ] at hK
    have hK0 := KG3x_nonneg hc₁0 T
    have hN₀p : (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) ≤ (Q ^ (1 + ε / 8)) ^ (5 / 2 - 5 / (ε / 8)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hN₀ge (by linarith)
    rw [← Real.rpow_mul hQ0.le] at hN₀p
    have hexp : Q ^ (5 / (ε / 8)) * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8))) ≤ 1 := by
      rw [← Real.rpow_add hQ0]
      refine Real.rpow_le_one_of_one_le_of_nonpos hQ1 ?_
      have e : 5 / (ε / 8) + (1 + ε / 8) * (5 / 2 - 5 / (ε / 8)) =
          5 / 2 + 5 / 2 * (ε / 8) - ε / 8 * (5 / (ε / 8)) := by ring
      rw [e, hδc]
      linarith
    have hpos : 0 ≤ (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) := by positivity
    calc KG3x (5 / (ε / 8)) T / (2 * π) * (2 * (N₀ : ℝ) ^ (5 / 2 - 5 / (ε / 8)) * I₃)
        ≤ A₁ * Q ^ (5 / (ε / 8)) / (2 * π) * (2 * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8))) * I₃) := by
          gcongr
      _ = A₁ / (2 * π) * (2 * I₃) * (Q ^ (5 / (ε / 8)) * Q ^ ((1 + ε / 8) * (5 / 2 - 5 / (ε / 8)))) := by
          ring
      _ ≤ A₁ / (2 * π) * (2 * I₃) * 1 := by
          gcongr
      _ = _ := mul_one _
  have hBT0 : 0 ≤ BTx (5 / (ε / 8)) T N₀ := by
    unfold BTx
    have := KG3x_nonneg hc₁0 T
    have : 0 ≤ ∫ v, Wf (5 / (ε / 8) + 9 / 2) v := (integral_Wf_pos (by linarith)).le
    positivity
  -- assemble
  have hQ2 : Q ^ (1 + ε / 2) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hQ3 : Q ≤ Q ^ (1 + ε) := by
    calc Q = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
      _ ≤ Q ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hBT2 : BTx (5 / (ε / 8)) T N₀ ^ 2 ≤ (A₁ / (2 * π) * (2 * I₃)) ^ 2 := pow_le_pow_left₀ hBT0 hBT 2
  have hCP0 : 0 ≤ (A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) := by positivity
  have hCT0 : 0 ≤ (A₁ / (2 * π) * (2 * I₃)) ^ 2 := sq_nonneg _
  have hR0 : (0 : ℝ) ≤ Rs.card := Nat.cast_nonneg _
  have hQe0 : 0 ≤ Q ^ (1 + ε) := by positivity
  have hR2 : (Rs.card : ℝ) ≤ 2 * Q ^ (1 + ε) := hR.trans (by linarith)
  calc 2 * DPx (ε / 8) T Rs.card N₀ + 2 * (Rs.card * BTx (5 / (ε / 8)) T N₀ ^ 2)
      ≤ 2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂) * Q ^ (1 + ε)) +
        2 * ((2 * Q ^ (1 + ε)) * (A₁ / (2 * π) * (2 * I₃)) ^ 2) := by
        gcongr
        exact hDP.trans (mul_le_mul_of_nonneg_left hQ2 hCP0)
    _ = (2 * ((A₀ / (2 * π)) ^ 2 * I₁ * (CL * I₂)) + 4 * (A₁ / (2 * π) * (2 * I₃)) ^ 2) * Q ^ (1 + ε) := by
        ring

/-! ### The fourth moment -/

/-- **The fourth moment of `ζ(½ + it)` at well-spaced points**: for every `0 < ε ≤ 1` there is `C` with
`Σ_r |ζ(½ + it_r)|⁴ ≤ C(T + 2)^{1+ε}` for every family of points `|t_r| ≤ T` with `|t_r − t_s| ≥ 1` for `r ≠ s`:
`norm_zeta_four_le`, and `sum_norm_afeDx_sq_le` at the points `t_r` and at the points `−t_r`. -/
theorem zeta_fourth_moment {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ {ι : Type*} (Rs : Finset ι) (t : ι → ℝ), (∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |t r - t s|) →
      ∀ T : ℝ, 0 ≤ T → (∀ r ∈ Rs, |t r| ≤ T) →
        ∑ r ∈ Rs, ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C * (T + 2) ^ (1 + ε) := by
  obtain ⟨C, hC⟩ := sum_norm_afeDx_sq_le hε hε1
  refine ⟨4 * C, fun Rs t hsep T hT ht => ?_⟩
  have hA := hC Rs t hsep T hT ht
  have hB := hC Rs (fun r => -t r)
    (fun r hr s hs hrs => by rw [show -t r - -t s = -(t r - t s) by ring, abs_neg]; exact hsep r hr s hs hrs)
    T hT (fun r hr => by rw [abs_neg]; exact ht r hr)
  calc ∑ r ∈ Rs, ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4
      ≤ ∑ r ∈ Rs, (2 * ‖afeDx (1 / 2 + t r * I)‖ ^ 2 + 2 * ‖afeDx (1 / 2 + ((-t r : ℝ) : ℂ) * I)‖ ^ 2) :=
        sum_le_sum fun r _ => norm_zeta_four_le (t r)
    _ = 2 * ∑ r ∈ Rs, ‖afeDx (1 / 2 + t r * I)‖ ^ 2 +
          2 * ∑ r ∈ Rs, ‖afeDx (1 / 2 + ((-t r : ℝ) : ℂ) * I)‖ ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 2 * (C * (T + 2) ^ (1 + ε)) + 2 * (C * (T + 2) ^ (1 + ε)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left (by simpa using hB) (by norm_num : (0 : ℝ) ≤ 2))
    _ = 4 * C * (T + 2) ^ (1 + ε) := by ring

end ZetaFourth

#print axioms ZetaFourth.norm_zeta_four_le
#print axioms ZetaFourth.sum_norm_Pd_sq_le_sep
#print axioms ZetaFourth.afeJx_split
#print axioms ZetaFourth.sum_norm_afeDx_sq_le
#print axioms ZetaFourth.zeta_fourth_moment
