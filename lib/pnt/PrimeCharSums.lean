import D2Tail
import HalfPlaneFinal
import PsiExplicit
import WindowGRH
import LeastNonresidue

/-!
# Sums of a Dirichlet character over primes, uniformly in the modulus — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "The analytic inputs"): the sums of a
character over primes, and over the primes of a progression, that the mean square over the family of primes meets in
its off-diagonal terms, and the splitting of the ramp error that the mean square starts from.

**CONDITIONAL.** The bounds here use the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function
(`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read (see
`formalisations/openai-half-plane.md`), through `ChiUniform.psiChi_le_uniform`,
`HalfPlanePNT.psi_isBigO_eleven_twelfths` and `GSTail.logDeriv_one_tail`. Lean checks them with the standard axioms
only, but they are only as good as that input, and must be cited as conditional on it. The results whose doc comments
do not say CONDITIONAL, the identity `rampErr_eq` among them, do not use it.

Throughout, `η > 0`, `α = 11/12 + η`, and the constants `C` depend on `η` only.

* `norm_sum_log_le`: `‖Σ_{p ≤ x} χ(p) log p‖ ≤ C log(N + 2) x^α` for every `χ ≠ 1` mod `N` and `x ≥ 0`. It is
  `ψ(x, χ)` less the prime powers, which weigh at most `ψ(x) − θ(x) ≤ C√x` (Mathlib's
  `Chebyshev.psi_sub_theta_le_mul_sqrt`).
* `norm_sum_prime_le`: the same for `‖Σ_{p ≤ x} χ(p)‖`, by partial summation against `1/log p`
  (`norm_sum_le_of_log`, with Mathlib's Abel inequality `Finset.abs_sum_mul_le_mul_of_abs_sum_range_le`).
* `norm_sum_modEq_le`, `norm_sum_Ioc_modEq_le`: for `N` and `a` prime to `M`,
  `‖Σ_{p ≤ x, p ≡ a (M)} χ(p)‖ ≤ C log(NM + 2) x^α`, and the same over `y < p ≤ x`. Orthogonality mod `M`
  (`norm_sum_modEq_sub_le`) leaves the sums of `ψχ` for the characters `ψ` mod `M`, and `ψχ` is a character `≠ 1`
  mod `NM` (`mul_changeLevel_ne_one`: otherwise `χ` would factor through `gcd(N, M) = 1`, by Mathlib's
  `factorsThrough_gcd`).
* `abs_sum_log_modEq_sub_le`: `|Σ_{p ≤ x, p ≡ a (M)} log p − x/φ(M)| ≤ C log(M + 2) x^α` for `a` prime to `M` and
  `x ≥ 1`. Orthogonality again, with `θ(x) = x + O(x^α)` (`PsiExplicit.abs_theta_sub_le`) and `Σ_{p ∣ M} log p ≤ log M`
  (`LeastNonresidue.sum_log_prime_dvd_le`) for the trivial character. So `card_Ioc_modEq_ge`: the primes
  `p ≡ a (M)` in `(y, x]` number at least `((x − y)/φ(M) − C log(M + 2) x^α)/log x`.
* `rampErr_eq`: for `χ ≠ 1` and `y ≤ Z`, the ramp error `WindowGRH.rampErr χ y` is
  `−Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n) + y(L′/L(1, χ) + Σ_{n ≤ Z} χ(n)Λ(n)/n)`. `norm_rampErr_add_le`: for
  `0 < η < 1/24` the second term is at most `yC log(N + 2) Z^{2η−1/12}` (`GSTail.logDeriv_one_tail`).
-/

open Finset DirichletCharacter
open scoped ArithmeticFunction.vonMangoldt

namespace PrimeCharSums

/-! ### Primes and prime powers -/

/-- `log(r + 2) ≥ 0` for `r ≥ 0`. -/
lemma log_add_two_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Real.log (r + 2) := Real.log_nonneg (by linarith)

/-- `log(r + 2) ≥ 1` for `r ≥ 1`. -/
lemma one_le_log_add_two {r : ℝ} (hr : 1 ≤ r) : 1 ≤ Real.log (r + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- There is no prime `p ≤ x` when `x < 2`. -/
lemma sum_primes_of_lt_two {x : ℝ} (hx : x < 2) (f : ℕ → ℂ) : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, f p = 0 :=
  sum_eq_zero fun p hp => by
    rw [mem_filter, mem_Ioc] at hp
    have h2 : ⌊x⌋₊ < 2 := (Nat.floor_lt' two_ne_zero).2 (by exact_mod_cast hx)
    exact absurd hp.2.two_le (by omega)

/-- The primes and the prime powers: `‖ψ(x, χ) − Σ_{p ≤ x} χ(p) log p‖ ≤ ψ(x) − θ(x)`. -/
lemma norm_psiChi_sub_le {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) :
    ‖ChiPNT.psiChi χ x - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * Real.log p‖ ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hI : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by simpa using Finset.Icc_add_one_left_eq_Ioc 0 ⌊x⌋₊
  rw [ChiPNT.psiChi, hI, ← sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  have hp : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * (Λ p : ℂ) =
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * Real.log p :=
    sum_congr rfl fun p hp => by rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hp).2]
  rw [hp, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _)

/-- **CONDITIONAL. Primes weighted by `log p`** (conditional on the half-plane, through
`ChiUniform.psiChi_le_uniform`): for `η > 0` there is `C` with `‖Σ_{p ≤ x} χ(p) log p‖ ≤ C log(N + 2) x^{11/12+η}`
for every `χ ≠ 1` mod `N` and `x ≥ 0`. -/
theorem norm_sum_log_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ x : ℝ, 0 ≤ x →
      ‖∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * Real.log p‖ ≤ C * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C₀, hC₀, hψ⟩ := ChiUniform.psiChi_le_uniform hη
  obtain ⟨C₁, hC₁⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C₀ + max C₁ 0, by positivity, fun N _ χ hχ x hx => ?_⟩
  have hL := one_le_log_add_two (r := N) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N))
  have hxa : 0 ≤ x ^ (11 / 12 + η) := Real.rpow_nonneg hx _
  rcases lt_or_ge x 2 with hx2 | hx2
  · rw [sum_primes_of_lt_two hx2, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) hxa
  have hsq : √x ≤ x ^ (11 / 12 + η) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h1 := hψ N χ hχ x (by linarith)
  have h2 := (norm_psiChi_sub_le χ x).trans ((hC₁ x).trans
    (mul_le_mul (le_max_left C₁ 0) hsq (Real.sqrt_nonneg x) (le_max_right C₁ 0)))
  have h3 : max C₁ 0 * x ^ (11 / 12 + η) ≤ max C₁ 0 * Real.log (N + 2) * x ^ (11 / 12 + η) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (le_max_right C₁ 0) hL) hxa
  linarith [norm_le_insert (ChiPNT.psiChi χ x) (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p * Real.log p)]

/-- **Partial summation over the primes.** If `‖Σ_{p ≤ m} c(p) log p‖ ≤ B` for every `m ≤ n`, then
`‖Σ_{p ≤ n} c(p)‖ ≤ 2B/log 2`: Abel's inequality (Mathlib's `Finset.abs_sum_mul_le_mul_of_abs_sum_range_le`) for the
real and the imaginary parts, against the antitone weight `1/log max(k, 2)`. -/
lemma norm_sum_le_of_log {c : ℕ → ℂ} {n : ℕ} {B : ℝ}
    (h : ∀ m ≤ n, ‖∑ p ∈ Ioc 0 m with p.Prime, c p * Real.log p‖ ≤ B) :
    ‖∑ p ∈ Ioc 0 n with p.Prime, c p‖ ≤ 2 * B / Real.log 2 := by
  set F : ℕ → ℂ := fun k => if k.Prime then c k * Real.log k else 0 with hF
  set g : ℕ → ℝ := fun k => (Real.log (max k 2))⁻¹ with hg
  have hS (m : ℕ) : ∑ p ∈ Ioc 0 m with p.Prime, c p * Real.log p = ∑ k ∈ range (m + 1), F k := by
    rw [← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_eq_filter_range, sum_filter]
  have hFg : ∑ p ∈ Ioc 0 n with p.Prime, c p = ∑ k ∈ range (n + 1), F k * (g k : ℂ) := by
    rw [← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_eq_filter_range, sum_filter]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime
    · have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.two_le
      have hl : (Real.log k : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (Real.log_pos (by linarith)).ne'
      simp only [hF, hg, hk, ↓reduceIte, max_eq_left h2, Complex.ofReal_inv]
      field_simp
    · simp [hF, hk]
  have hg0 : 0 ≤ g := fun k => inv_nonneg.2 (Real.log_nonneg (le_max_of_le_right one_le_two))
  have hanti : AntitoneOn g (Set.Iio (n + 1)) := fun i _ j _ hij =>
    inv_anti₀ (Real.log_pos (lt_max_of_lt_right one_lt_two))
      (Real.log_le_log (by positivity) (max_le_max (Nat.cast_le.2 hij) le_rfl))
  have hB (k : ℕ) (hk : k ≤ n + 1) : ‖∑ i ∈ range k, F i‖ ≤ B := by
    rcases k with _ | m
    · simpa using (norm_nonneg _).trans (h 0 (Nat.zero_le _))
    · rw [← hS]; exact h m (by omega)
  have hre := abs_sum_mul_le_mul_of_abs_sum_range_le (f := fun i => (F i).re)
    (fun k hk => by rw [← Complex.re_sum]; exact (Complex.abs_re_le_norm _).trans (hB k hk)) hg0 hanti
  have him := abs_sum_mul_le_mul_of_abs_sum_range_le (f := fun i => (F i).im)
    (fun k hk => by rw [← Complex.im_sum]; exact (Complex.abs_im_le_norm _).trans (hB k hk)) hg0 hanti
  have hg2 : g 0 = (Real.log 2)⁻¹ := by simp [hg]
  rw [hFg]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal]
  rw [hg2] at hre him
  linarith [show 2 * B / Real.log 2 = B * (Real.log 2)⁻¹ + B * (Real.log 2)⁻¹ by ring]

/-- **CONDITIONAL. Primes** (conditional on the half-plane, through `norm_sum_log_le`): for `η > 0` there is `C`
with `‖Σ_{p ≤ x} χ(p)‖ ≤ C log(N + 2) x^{11/12+η}` for every `χ ≠ 1` mod `N` and `x ≥ 0`. -/
theorem norm_sum_prime_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ x : ℝ, 0 ≤ x →
      ‖∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, χ p‖ ≤ C * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C, hC, h⟩ := norm_sum_log_le hη
  refine ⟨2 * C / Real.log 2, by positivity, fun N _ χ hχ x hx => ?_⟩
  have hL : 0 ≤ C * Real.log (N + 2) := mul_nonneg hC (log_add_two_nonneg (by positivity))
  refine (norm_sum_le_of_log (B := C * Real.log (N + 2) * x ^ (11 / 12 + η)) fun m hm => ?_).trans
    (le_of_eq (by ring))
  have hmx : (m : ℝ) ≤ x := (Nat.cast_le.2 hm).trans (Nat.floor_le hx)
  have hm' := h N χ hχ m (Nat.cast_nonneg m)
  rw [Nat.floor_natCast] at hm'
  exact hm'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg m) hmx (by linarith)) hL)

/-! ### Primes in a progression -/

/-- `χ` mod `N` at a level `K` divisible by `N` takes the value `χ(n)` at every `n` prime to `K`. -/
lemma changeLevel_natCast {N K : ℕ} (h : N ∣ K) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n.Coprime K) :
    changeLevel h χ n = χ n := by
  simpa [ZMod.cast_natCast h] using changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime n hn)

/-- The product of `ψ` mod `M` and `χ` mod `N`, at level `NM`, takes the value `ψ(n)χ(n)` at every `n`. -/
lemma mul_changeLevel_apply {N M : ℕ} (ψ : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (changeLevel (M.dvd_mul_left N) ψ * changeLevel (N.dvd_mul_right M) χ) n = ψ n * χ n := by
  rw [MulChar.mul_apply]
  by_cases hn : n.Coprime (N * M)
  · rw [changeLevel_natCast _ _ hn, changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    rw [Nat.coprime_mul_iff_right, not_and_or] at hn
    rcases hn with hn | hn
    · rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]
    · rw [MulChar.map_nonunit ψ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]

/-- **The product with a character of coprime level.** For `N` prime to `M`, `χ ≠ 1` mod `N` and any `ψ` mod `M`,
the product at level `NM` is not trivial: otherwise `χ` would factor through `gcd(N, M) = 1` (Mathlib's
`factorsThrough_gcd`). -/
lemma mul_changeLevel_ne_one {N M : ℕ} [NeZero N] (hNM : N.Coprime M) (ψ : DirichletCharacter ℂ M)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    changeLevel (M.dvd_mul_left N) ψ * changeLevel (N.dvd_mul_right M) χ ≠ 1 := by
  intro h
  have e : changeLevel (N.dvd_mul_right M) χ = changeLevel (M.dvd_mul_left N) ψ⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans h)
  have hf := factorsThrough_gcd χ ψ⁻¹ e
  rw [hNM.gcd_eq_one, factorsThrough_one_iff] at hf
  exact hχ hf

/-- **Orthogonality, with errors.** For `a` prime to `M`: if `‖Σ_{n ∈ s} ψ(n)f(n) − c(ψ)‖ ≤ B` for every character
`ψ` mod `M`, then `‖Σ_{n ∈ s, n ≡ a (M)} f(n) − φ(M)⁻¹ Σ_ψ ψ(a)⁻¹c(ψ)‖ ≤ B` (Mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq`). -/
lemma norm_sum_modEq_sub_le {M : ℕ} [NeZero M] {a : ℕ} (ha : a.Coprime M) (s : Finset ℕ) (f : ℕ → ℂ)
    (c : DirichletCharacter ℂ M → ℂ) {B : ℝ} (hB : ∀ ψ, ‖∑ n ∈ s, ψ n * f n - c ψ‖ ≤ B) :
    ‖∑ n ∈ s with n ≡ a [MOD M], f n -
        (M.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * c ψ‖ ≤ B := by
  have hau : IsUnit (a : ZMod M) := (ZMod.isUnit_iff_coprime a M).2 ha
  have hφ : (M.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne'
  have key (n : ℕ) : ∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * (ψ n * f n) =
      if n ≡ a [MOD M] then (M.totient : ℂ) * f n else 0 := by
    simp_rw [← mul_assoc]
    rw [← sum_mul, sum_char_inv_mul_char_eq ℂ hau]
    by_cases h : n ≡ a [MOD M]
    · rw [ite_eq_left ((ZMod.natCast_eq_natCast_iff _ _ _).2 h.symm), ite_eq_left h]
    · rw [ite_eq_right fun h' => h ((ZMod.natCast_eq_natCast_iff _ _ _).1 h').symm, ite_eq_right h, zero_mul]
  have hmain : ∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * ∑ n ∈ s, ψ n * f n =
      (M.totient : ℂ) * ∑ n ∈ s with n ≡ a [MOD M], f n := by
    rw [mul_sum, sum_filter]
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun n _ => key n
  have hid : ∑ n ∈ s with n ≡ a [MOD M], f n - (M.totient : ℂ)⁻¹ * ∑ ψ, ψ (a : ZMod M)⁻¹ * c ψ =
      (M.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * (∑ n ∈ s, ψ n * f n - c ψ) := by
    simp_rw [mul_sub, sum_sub_distrib, hmain]
    rw [mul_sub, inv_mul_cancel_left₀ hφ]
  have hcard : (univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [card_univ, ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  have hφ' : (M.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne'
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
  calc (M.totient : ℝ)⁻¹ * ‖∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * (∑ n ∈ s, ψ n * f n - c ψ)‖
      ≤ (M.totient : ℝ)⁻¹ * ∑ _ψ : DirichletCharacter ℂ M, B := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun ψ _ => ?_)) (by positivity)
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans (hB ψ)
    _ = B := by rw [sum_const, hcard, nsmul_eq_mul, inv_mul_cancel_left₀ hφ']

/-- **CONDITIONAL. Primes in a progression** (conditional on the half-plane, through `norm_sum_prime_le`): for `η > 0`
there is `C` with `‖Σ_{p ≤ x, p ≡ a (M)} χ(p)‖ ≤ C log(NM + 2) x^{11/12+η}` for every `M ≥ 1`, `N` and `a` prime to
`M`, `χ ≠ 1` mod `N` and `x ≥ 0`. -/
theorem norm_sum_modEq_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N M : ℕ) [NeZero N] [NeZero M], N.Coprime M → ∀ a : ℕ, a.Coprime M →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → ∀ x : ℝ, 0 ≤ x →
        ‖∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p‖ ≤
          C * Real.log (N * M + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C, hC, h⟩ := norm_sum_prime_le hη
  refine ⟨C, hC, fun N M _ _ hNM a ha χ hχ x hx => ?_⟩
  have h1 := norm_sum_modEq_sub_le ha {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime} (fun p => χ p) 0
    (B := C * Real.log (N * M + 2) * x ^ (11 / 12 + η)) fun ψ => by
      rw [Pi.zero_apply, sub_zero]
      simpa only [mul_changeLevel_apply, Nat.cast_mul] using
        h (N * M) _ (mul_changeLevel_ne_one hNM ψ hχ) x hx
  simpa [filter_filter] using h1

/-- The sum over `y < n ≤ x` is the sum up to `x` less the sum up to `y`. -/
lemma sum_Ioc_eq_sub {G : Type*} [AddCommGroup G] (P : ℕ → Prop) [DecidablePred P] (f : ℕ → G) {y x : ℝ}
    (hyx : y ≤ x) :
    ∑ n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with P n, f n = ∑ n ∈ Ioc 0 ⌊x⌋₊ with P n, f n - ∑ n ∈ Ioc 0 ⌊y⌋₊ with P n, f n := by
  rw [eq_sub_iff_add_eq', sum_filter, sum_filter, sum_filter,
    sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hyx)]

/-- **CONDITIONAL. Primes of a progression in an interval** (conditional on the half-plane, through
`norm_sum_modEq_le`): for `η > 0` there is `C` with `‖Σ_{y < p ≤ x, p ≡ a (M)} χ(p)‖ ≤ C log(NM + 2) x^{11/12+η}`
for every `M ≥ 1`, `N` and `a` prime to `M`, `χ ≠ 1` mod `N` and `0 ≤ y ≤ x`. -/
theorem norm_sum_Ioc_modEq_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N M : ℕ) [NeZero N] [NeZero M], N.Coprime M → ∀ a : ℕ, a.Coprime M →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → ∀ y x : ℝ, 0 ≤ y → y ≤ x →
        ‖∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p‖ ≤
          C * Real.log (N * M + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C, hC, h⟩ := norm_sum_modEq_le hη
  refine ⟨2 * C, by positivity, fun N M _ _ hNM a ha χ hχ y x hy hyx => ?_⟩
  have hL : 0 ≤ C * Real.log (N * M + 2) := mul_nonneg hC (log_add_two_nonneg (by positivity))
  have hy' := (h N M hNM a ha χ hχ y hy).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy hyx (by linarith)) hL)
  rw [sum_Ioc_eq_sub _ _ hyx]
  linarith [norm_sub_le (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p)
    (∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p), h N M hNM a ha χ hχ x (hy.trans hyx)]

/-! ### Counting the primes of a progression -/

/-- **CONDITIONAL. The prime number theorem in progressions, uniformly in the modulus** (conditional on the
half-plane, through `norm_sum_log_le` and `PsiExplicit.abs_theta_sub_le`): for `η > 0` there is `C` with
`|Σ_{p ≤ x, p ≡ a (M)} log p − x/φ(M)| ≤ C log(M + 2) x^{11/12+η}` for every `M ≥ 1`, `a` prime to `M` and
`x ≥ 1`. -/
theorem abs_sum_log_modEq_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (a : ℕ), a.Coprime M → ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], Real.log p - x / M.totient| ≤
        C * Real.log (M + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_sum_log_le hη
  obtain ⟨C₂, hC₂, h₂⟩ := PsiExplicit.abs_theta_sub_le hη
  refine ⟨C₁ + C₂ + 1, by positivity, fun M _ a ha x hx => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hL := one_le_log_add_two hM
  have hxa : 1 ≤ x ^ (11 / 12 + η) := Real.one_le_rpow hx (by linarith)
  have hau : IsUnit (a : ZMod M) := (ZMod.isUnit_iff_coprime a M).2 ha
  -- the trivial character: `Σ_{p ≤ x, p ∤ M} log p`, within `log M` of `θ(x)`
  have hprin : ‖∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : DirichletCharacter ℂ M) p * (Real.log p : ℂ) -
      (Chebyshev.theta x : ℂ)‖ ≤ Real.log M := by
    rw [Chebyshev.theta, Complex.ofReal_sum, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (le_trans ?_ (LeastNonresidue.sum_log_prime_dvd_le (NeZero.ne M) ⌊x⌋₊))
    rw [sum_filter (fun p => p ∣ M)]
    refine sum_le_sum fun p hp => ?_
    have hp' := (mem_filter.1 hp).2
    have hcop : IsUnit (p : ZMod M) ↔ ¬ p ∣ M := by
      rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp']
    split_ifs with hpM
    · rw [MulChar.map_nonunit _ (by rwa [hcop, not_not]), zero_mul, zero_sub, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le))]
    · rw [MulChar.one_apply (hcop.2 hpM), one_mul, sub_self, norm_zero]
  have h := norm_sum_modEq_sub_le ha {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime} (fun p => (Real.log p : ℂ))
    (fun ψ => if ψ = 1 then (x : ℂ) else 0) (B := (C₁ + C₂ + 1) * Real.log (M + 2) * x ^ (11 / 12 + η))
    fun ψ => by
      by_cases hψ : ψ = 1
      · subst hψ
        rw [ite_eq_left rfl]
        have h3 : ‖(Chebyshev.theta x : ℂ) - x‖ ≤ C₂ * x ^ (11 / 12 + η) := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact h₂ x hx
        have h4 := norm_sub_le_norm_sub_add_norm_sub (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime,
          (1 : DirichletCharacter ℂ M) p * (Real.log p : ℂ)) (Chebyshev.theta x : ℂ) (x : ℂ)
        have h5 : Real.log M ≤ Real.log (M + 2) * x ^ (11 / 12 + η) :=
          (Real.log_le_log (by linarith) (by linarith)).trans (le_mul_of_one_le_right (by linarith) hxa)
        have h6 := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ C₂ * x ^ (11 / 12 + η))
        have h7 : 0 ≤ C₁ * Real.log (M + 2) * x ^ (11 / 12 + η) := by positivity
        linarith
      · rw [ite_eq_right hψ, sub_zero]
        refine (h₁ M ψ hψ x (by linarith)).trans ?_
        have : 0 ≤ (C₂ + 1) * Real.log (M + 2) * x ^ (11 / 12 + η) := by positivity
        linarith
  have hainv : IsUnit ((a : ZMod M)⁻¹) :=
    IsUnit.of_mul_eq_one (a : ZMod M) (by rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hau)
  have hsum : ∑ ψ : DirichletCharacter ℂ M, ψ (a : ZMod M)⁻¹ * (if ψ = 1 then (x : ℂ) else 0) = x := by
    simp_rw [mul_ite, mul_zero]
    rw [sum_ite_eq' univ 1, ite_eq_left (mem_univ _), MulChar.one_apply hainv, one_mul]
  rw [hsum, filter_filter] at h
  have e : (((∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], Real.log p) - x / M.totient : ℝ) : ℂ) =
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], (Real.log p : ℂ) - (M.totient : ℂ)⁻¹ * x := by
    push_cast; ring
  rwa [← e, Complex.norm_real, Real.norm_eq_abs] at h

/-- **CONDITIONAL. The primes of a progression in an interval, counted from below** (conditional on the
half-plane, through `abs_sum_log_modEq_sub_le`): for `η > 0` there is `C` such that for every `M ≥ 1`, `a` prime
to `M` and `1 ≤ y ≤ x`, the primes `p ≡ a (M)` with `y < p ≤ x` number at least
`((x − y)/φ(M) − C log(M + 2) x^{11/12+η})/log x`. -/
theorem card_Ioc_modEq_ge {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (a : ℕ), a.Coprime M → ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ((x - y) / M.totient - C * Real.log (M + 2) * x ^ (11 / 12 + η)) / Real.log x ≤
        #{p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD M]} := by
  obtain ⟨C, hC, h⟩ := abs_sum_log_modEq_sub_le hη
  refine ⟨2 * C, by positivity, fun M _ a ha y x hy hyx => ?_⟩
  rcases (hy.trans hyx).eq_or_lt with hx | hx
  · rw [← hx, Real.log_one, div_zero]; positivity
  have hL : 0 ≤ C * Real.log (M + 2) := mul_nonneg hC (log_add_two_nonneg (by positivity))
  have hX := abs_le.1 (h M a ha x hx.le)
  have hY := abs_le.1 (h M a ha y hy)
  have hyα := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (z := 11 / 12 + η) (by linarith) hyx (by linarith)) hL
  have hup : ∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], Real.log p ≤
      #{p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD M]} * Real.log x := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun p hp => ?_
    rw [mem_filter, mem_Ioc] at hp
    exact Real.log_le_log (by exact_mod_cast hp.2.1.pos)
      ((Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith)))
  rw [sum_Ioc_eq_sub _ _ hyx] at hup
  rw [div_le_iff₀ (Real.log_pos hx), sub_div]
  linarith

/-! ### The ramp error -/

/-- **The ramp error, split at `Z`.** For `χ ≠ 1` mod `N` and `y ≤ Z`, the error `E_χ = WindowGRH.rampErr χ` is
`E_χ(y) = −Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n) + y(L′/L(1, χ) + Σ_{n ≤ Z} χ(n)Λ(n)/n)`: the terms `y < n ≤ Z` cancel, and
`Λ(n)χ(n)(y/n − 1) = yχ(n)Λ(n)/n − Λ(n)χ(n)` for `n ≤ y`. -/
theorem rampErr_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {y Z : ℝ} (hyZ : y ≤ Z) :
    WindowGRH.rampErr χ y =
      -∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ) +
        y * (deriv (LFunction χ) 1 / LFunction χ 1 + ∑ n ∈ Icc 1 ⌊Z⌋₊, χ n * (Λ n : ℂ) / n) := by
  have h : RampLaplace.rampSum (fun n => χ n) y = ∑ n ∈ Icc 1 ⌊Z⌋₊,
      ((y : ℂ) * (χ n * (Λ n : ℂ) / n) - (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ)) := by
    have e : {n ∈ Icc 1 ⌊Z⌋₊ | n ≤ ⌊y⌋₊} = Icc 1 ⌊y⌋₊ := by
      ext n
      simp only [mem_filter, mem_Icc]
      have := Nat.floor_le_floor (R := ℝ) hyZ
      omega
    rw [RampLaplace.rampSum, ← sum_filter_add_sum_filter_not (Icc 1 ⌊Z⌋₊) (· ≤ ⌊y⌋₊), e,
      sum_eq_zero (s := {n ∈ Icc 1 ⌊Z⌋₊ | ¬n ≤ ⌊y⌋₊}), add_zero]
    · refine sum_congr rfl fun n hn => ?_
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hny)]
      push_cast
      ring
    · intro n hn
      rw [mem_filter, mem_Icc, not_le] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
      rw [min_eq_right ((div_lt_one hn0).2 (Nat.lt_of_floor_lt hn.2)).le]
      push_cast
      ring
  rw [WindowGRH.rampErr, ite_eq_right hχ, logDeriv_apply, h, sum_sub_distrib, ← mul_sum]
  ring

/-- **CONDITIONAL. The ramp error at scale `Z`** (conditional on the half-plane, through
`GSTail.logDeriv_one_tail`): for `0 < η < 1/24` there is `C` such that the second term of `rampErr_eq` has norm at
most `yC log(N + 2) Z^{2η−1/12}`, that is `‖E_χ(y) + Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n)‖ ≤ yC log(N + 2) Z^{2η−1/12}`,
for every `χ ≠ 1` mod `N` and `0 ≤ y ≤ Z` with `Z > 1`. -/
theorem norm_rampErr_add_le {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y Z : ℝ, 0 ≤ y → y ≤ Z →
      1 < Z → ‖WindowGRH.rampErr χ y + ∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ)‖ ≤
        y * (C * Real.log (N + 2) * Z ^ (2 * η - 1 / 12)) := by
  obtain ⟨C, hC, h⟩ := GSTail.logDeriv_one_tail hη hη'
  refine ⟨C, hC, fun N _ χ hχ y Z hy hyZ hZ => ?_⟩
  rw [rampErr_eq hχ hyZ, neg_add_cancel_comm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy]
  exact mul_le_mul_of_nonneg_left (h N χ hχ Z hZ) hy

end PrimeCharSums

#print axioms PrimeCharSums.norm_sum_log_le
#print axioms PrimeCharSums.norm_sum_prime_le
#print axioms PrimeCharSums.norm_sum_modEq_le
#print axioms PrimeCharSums.norm_sum_Ioc_modEq_le
#print axioms PrimeCharSums.abs_sum_log_modEq_sub_le
#print axioms PrimeCharSums.card_Ioc_modEq_ge
#print axioms PrimeCharSums.rampErr_eq
#print axioms PrimeCharSums.norm_rampErr_add_le
