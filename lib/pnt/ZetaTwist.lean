import TwistFamily

/-!
# A pair of primes with small quadratic twists on a window — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "The analytic inputs": the twists). The
lattice side fixes a pair of primes `(q, d)` from the window's base `Y` and then chooses its sub-window, so the three
quadratic twists `χ_q`, `χ_d` and `χ_qχ_d` must have ramp errors of square-root size uniformly on `[Y, Y^A]`. With
`z = Y^{ε/5}` and `z′ = z log²Y`, the pair must also satisfy (`WinPair`):

* `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)`, primes with `z/2 < log q ≤ z` and `z′/2 < log d ≤ z′`;
* `q` and every odd prime `p ≤ z` divide `d + 1`.

**CONDITIONAL.** `exists_winPair_twists` uses the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function
(`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read (see
`formalisations/openai-half-plane.md`), through `TwistFamily.exists_good` and `PrimeCharSums.norm_rampErr_add_le`. Lean
checks it with the standard axioms only, but it is only as good as that input, and must be cited as conditional on it.

* `exists_winPair_twists`: for `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has such a pair with
  `‖E_χ(y)‖ ≤ y^{1/2+ε}` on `[Y, Y^A]` for `χ = χ_q`, `χ_d`, `χ_qχ_d` (`chiQD`). It applies the generic lemma
  `TwistFamily.exists_good` twice:
  - **`q`**: the primes `q ≡ 3 (mod 8)` with `L = z`, and the weight `1`;
  - **`d`, given `q`**: the primes `d ≡ 8K − 1 (mod 16K)` with `L = z′`, for `K = q·∏_{2 < p ≤ z} p`
    (`oddPrimorial`), and the weights `1` and `χ_q`. Then `d ≡ 7 (mod 16)` and `K ∣ d + 1` (`mod_sixteen_of_modEq`), and
    `log 16K ≤ 6z`.
* **From the free part to the ramp error** (`norm_rampErr_le`). For `χ(n) = b(n)J(n | d)`, the sum
  `Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n)` of `PrimeCharSums.rampErr_eq`, with `Z = ⌊Y^{48A}⌋`, is the free part
  `TwistFamily.free` plus the terms with `(n, M) > 1`. Those weigh at most `⌊log₂ Z⌋ log M` (`sum_not_coprime_le`),
  which is `≤ 576Az log Y ≤ √Y/4`, and the tail `yC log(N + 2) Y^{−2A}` of `PrimeCharSums.norm_rampErr_add_le` is at
  most `1/4`.
-/

open Finset DirichletCharacter ZetaBalance TwistFamily
open scoped ArithmeticFunction.vonMangoldt

namespace ZetaTwist

/-- The pairs of primes `(q, d)` that the lattice side needs at the window with base `Y`, for `z = Y^{ε/5}` and
`z′ = z log²Y`: `q ≡ 3 (mod 8)`, `d ≡ 7 (mod 16)`, `z/2 < log q ≤ z`, `z′/2 < log d ≤ z′`, and `q` and every odd prime
`p ≤ z` divide `d + 1`. -/
structure WinPair (ε Y : ℝ) (q d : ℕ) : Prop where
  /-- `q` is prime. -/
  q_prime : q.Prime
  /-- `d` is prime. -/
  d_prime : d.Prime
  /-- `q ≡ 3 (mod 8)`. -/
  q_mod : q % 8 = 3
  /-- `d ≡ 7 (mod 16)`. -/
  d_mod : d % 16 = 7
  /-- `z/2 < log q ≤ z`. -/
  q_size : Y ^ (ε / 5) / 2 < Real.log q ∧ Real.log q ≤ Y ^ (ε / 5)
  /-- `z′/2 < log d ≤ z′`. -/
  d_size : Y ^ (ε / 5) * Real.log Y ^ 2 / 2 < Real.log d ∧ Real.log d ≤ Y ^ (ε / 5) * Real.log Y ^ 2
  /-- `q ∣ d + 1`. -/
  q_dvd : q ∣ d + 1
  /-- Every odd prime `p ≤ z` divides `d + 1`. -/
  small_dvd : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (ε / 5) → p ∣ d + 1

/-- `χ_qχ_d`, the product of the Legendre symbols mod `q` and mod `d`, at level `qd`. -/
noncomputable def chiQD (q d : ℕ) [Fact q.Prime] [Fact d.Prime] : DirichletCharacter ℂ (q * d) :=
  changeLevel (q.dvd_mul_right d) (legChar q) * changeLevel (d.dvd_mul_left q) (legChar d)

/-- `χ_qχ_d(n) = (n/q)(n/d)`, with the Jacobi symbols `J(n | q)J(n | d)`. -/
lemma chiQD_apply (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (n : ℕ) :
    chiQD q d n = (((jacobiSym n q : ℝ) * jacobiSym n d : ℝ) : ℂ) := by
  rw [chiQD, mul_comm (changeLevel _ (legChar q)), PrimeCharSums.mul_changeLevel_apply, legChar_natCast,
    legChar_natCast,
    jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym]
  push_cast
  ring

/-- `χ_p(n) = (n/p) = 1·J(n | p)`. -/
lemma legChar_apply_jacobi (p : ℕ) [Fact p.Prime] (n : ℕ) :
    legChar p n = (((1 : ℝ) * jacobiSym n p : ℝ) : ℂ) := by
  rw [legChar_natCast, jacobiSym.legendreSym.to_jacobiSym]
  push_cast
  ring

/-- `χ_p ≠ 1` for an odd prime `p`: it is primitive mod `p` (`ZetaBalance.legChar_isPrimitive`). -/
lemma legChar_ne_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : legChar p ≠ 1 := fun h => by
  have := (isPrimitive_def _).1 (legChar_isPrimitive hp2)
  rw [h, conductor_one] at this
  exact hp.out.one_lt.ne this

/-- `Q(z) = ∏_{2 < p ≤ z} p`, the product of the odd primes up to `z`. -/
noncomputable def oddPrimorial (z : ℝ) : ℕ :=
  ∏ p ∈ range (⌊z⌋₊ + 1) with p.Prime ∧ p ≠ 2, p

/-- `Q(z)` is odd. -/
lemma oddPrimorial_odd (z : ℝ) : Odd (oddPrimorial z) :=
  prod_induction _ _root_.Odd (fun _ _ ha hb => ha.mul hb) odd_one fun _ hp =>
    (mem_filter.1 hp).2.1.odd_of_ne_two (mem_filter.1 hp).2.2

/-- `0 < Q(z) ≤ 4^{⌊z⌋}`: `Q(z)` divides the primorial of `⌊z⌋` (Mathlib's `primorial_le_four_pow`). -/
lemma oddPrimorial_le (z : ℝ) : 0 < oddPrimorial z ∧ oddPrimorial z ≤ 4 ^ ⌊z⌋₊ := by
  refine ⟨(oddPrimorial_odd z).pos, (Nat.le_of_dvd (primorial_pos _) ?_).trans (primorial_le_four_pow _)⟩
  unfold oddPrimorial primorial
  exact prod_dvd_prod_of_subset _ _ _ fun p hp => mem_filter.2 ⟨(mem_filter.1 hp).1, (mem_filter.1 hp).2.1⟩

/-- Every odd prime `p ≤ z` divides `Q(z)`. -/
lemma dvd_oddPrimorial {z : ℝ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpz : (p : ℝ) ≤ z) : p ∣ oddPrimorial z :=
  dvd_prod_of_mem _ (mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hpz)), hp, hp2⟩)

/-- `8K − 1` is prime to `16K`, as `16K = 2(8K − 1) + 2` and `8K − 1` is odd. -/
lemma coprime_eight_mul_sub_one {K : ℕ} (hK : 1 ≤ K) : (8 * K - 1).Coprime (16 * K) := by
  rw [show 16 * K = (8 * K - 1) * 2 + 2 by omega, Nat.coprime_mul_left_add_right]
  exact Nat.coprime_two_right.2 ⟨4 * K - 1, by omega⟩

/-- For odd `K`, `d ≡ 8K − 1 (mod 16K)` gives `d ≡ 7 (mod 16)` and `K ∣ d + 1`: `d + 1 = 16Kt + 8K`. -/
lemma mod_sixteen_of_modEq {K d : ℕ} (hK : Odd K) (hd : d ≡ 8 * K - 1 [MOD 16 * K]) :
    d % 16 = 7 ∧ K ∣ d + 1 := by
  obtain ⟨j, hj⟩ := hK
  have hmod : d % (16 * K) = 8 * K - 1 := by
    rw [hd]
    exact Nat.mod_eq_of_lt (by omega)
  have h := Nat.div_add_mod d (16 * K)
  rw [hmod] at h
  have e : d + 1 = K * (16 * (d / (16 * K)) + 8) := by
    rw [mul_add, ← mul_assoc, mul_comm K 16]
    omega
  refine ⟨?_, ⟨_, e⟩⟩
  generalize d / (16 * K) = t at e
  have e' : d + 1 = 16 * (K * t) + 8 * K := by rw [e]; ring
  generalize K * t = u at e'
  omega

/-- **The terms with `(n, M) > 1`.** `Σ_{n ≤ Z, (n, M) > 1} Λ(n) ≤ ⌊log₂ Z⌋ log M`: such `n` with `Λ(n) ≠ 0` are
powers `p^a ≤ Z` of primes `p ∣ M`, so they divide `M^{⌊log₂ Z⌋}`, and `Σ_{n ∣ N} Λ(n) = log N` (Mathlib's
`vonMangoldt_sum`). -/
lemma sum_not_coprime_le {M : ℕ} (hM : M ≠ 0) (Z : ℕ) :
    ∑ n ∈ Icc 1 Z with ¬n.Coprime M, Λ n ≤ Nat.log 2 Z * Real.log M := by
  calc ∑ n ∈ Icc 1 Z with ¬n.Coprime M, Λ n ≤ ∑ n ∈ (M ^ Nat.log 2 Z).divisors, Λ n := by
        rw [← Finset.sum_filter_ne_zero]
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg
        obtain ⟨hn, hΛ⟩ := mem_filter.1 hn
        obtain ⟨hnZ, hnM⟩ := mem_filter.1 hn
        obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff _).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
        have hpM : p ∣ M := by
          by_contra h
          exact hnM (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
        have haZ : a ≤ Nat.log 2 Z :=
          Nat.le_log_of_pow_le one_lt_two ((Nat.pow_le_pow_left hp.two_le a).trans (mem_Icc.1 hnZ).2)
        exact Nat.mem_divisors.2 ⟨(pow_dvd_pow_of_dvd hpM a).trans (pow_dvd_pow M haZ), pow_ne_zero _ hM⟩
    _ = Nat.log 2 Z * Real.log M := by
        rw [ArithmeticFunction.vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

/-- **CONDITIONAL. A ramp error from its free part** (conditional on the half-plane, through the bound `hC` of
`PrimeCharSums.norm_rampErr_add_le` at `η = 1/48`). Let `χ ≠ 1` mod `N` with `χ(n) = b(n)J(n | d)`, `y ∈ [Y, Y^A]` and
`Z = ⌊Y^{48A}⌋`. The sum `Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n)` is `T_d(y)` plus the terms with `(n, M) > 1`, at most
`⌊log₂ Z⌋ log M` (`sum_not_coprime_le`), and the tail is `yC log(N + 2) Y^{−2A} ≤ C log(N + 2)/Y`. So
`‖E_χ(y)‖ ≤ y^{1/2+ε}` if `|T_d(y)| ≤ y^{1/2+ε}/2`, `⌊log₂ Z⌋ log M ≤ √Y/4` and `C log(N + 2) ≤ Y/4`. -/
lemma norm_rampErr_le {C : ℝ}
    (hC : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y Z : ℝ, 0 ≤ y → y ≤ Z → 1 < Z →
      ‖WindowGRH.rampErr χ y + ∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ)‖ ≤
        y * (C * Real.log (N + 2) * Z ^ (2 * (1 / 48) - 1 / 12 : ℝ)))
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {M : ℕ} (hM : M ≠ 0) {b : ℕ → ℝ}
    (hb : ∀ n, |b n| ≤ 1) {d : ℕ} (hval : ∀ n : ℕ, χ n = ((b n * jacobiSym n d : ℝ) : ℂ)) {ε A Y y : ℝ}
    (hε : 0 ≤ ε) (hA : 1 ≤ A) (hY : 2 ≤ Y) (hy : y ∈ Set.Icc Y (Y ^ A))
    (hfree : |free M ⌊Y ^ (48 * A)⌋₊ b d y| ≤ y ^ (1 / 2 + ε) / 2)
    (hfix : Nat.log 2 ⌊Y ^ (48 * A)⌋₊ * Real.log M ≤ √Y / 4) (htail : C * Real.log (N + 2) ≤ Y / 4) :
    ‖WindowGRH.rampErr χ y‖ ≤ y ^ (1 / 2 + ε) := by
  obtain ⟨hYy, hyA⟩ := hy
  have hY0 : 0 < Y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hAZ : Y ^ A ≤ Y ^ (48 * A) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h := hC N χ hχ y _ (by linarith) (hyA.trans hAZ) (Real.one_lt_rpow (by linarith) (by linarith))
  -- the sum is `T_d(y)` plus the terms `F` with `(n, M) > 1`
  set T := free M ⌊Y ^ (48 * A)⌋₊ b d y with hT
  set F := ∑ n ∈ Icc 1 ⌊Y ^ (48 * A)⌋₊ with ¬n.Coprime M, Λ n * b n * min 1 (y / n) * (jacobiSym n d : ℝ) with hF
  have hsum : ∑ n ∈ Icc 1 ⌊Y ^ (48 * A)⌋₊, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ) = ((T + F : ℝ) : ℂ) := by
    rw [hT, free, hF, sum_filter_add_sum_filter_not, Complex.ofReal_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [hval]
    push_cast
    ring
  have hfixF : |F| ≤ Nat.log 2 ⌊Y ^ (48 * A)⌋₊ * Real.log M := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => ?_).trans (sum_not_coprime_le hM _))
    have hm0 : 0 ≤ min 1 (y / n) := le_min zero_le_one (by positivity)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg hm0]
    calc Λ n * |b n| * min 1 (y / n) * |(jacobiSym n d : ℝ)| ≤ Λ n * 1 * 1 * 1 := by
          gcongr
          exacts [hb n, min_le_left _ _, abs_jacobiSym_le _ _]
      _ = Λ n := by ring
  -- the tail: `yC log(N + 2) Y^{−2A} ≤ C log(N + 2) Y^{−A} ≤ C log(N + 2)/Y ≤ 1/4`
  have hyY : y * Y ^ (-(2 * A)) ≤ Y⁻¹ := by
    calc y * Y ^ (-(2 * A)) ≤ Y ^ A * Y ^ (-(2 * A)) :=
          mul_le_mul_of_nonneg_right hyA (Real.rpow_nonneg hY0.le _)
      _ = Y ^ (-A) := by
          rw [← Real.rpow_add hY0]
          ring_nf
      _ ≤ Y ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = Y⁻¹ := Real.rpow_neg_one Y
  have htail' : y * (C * Real.log (N + 2) * Y ^ (-(2 * A))) ≤ 1 / 4 := by
    calc y * (C * Real.log (N + 2) * Y ^ (-(2 * A))) = C * Real.log (N + 2) * (y * Y ^ (-(2 * A))) := by ring
      _ ≤ Y / 4 * Y⁻¹ :=
          mul_le_mul htail hyY (mul_nonneg (by linarith) (Real.rpow_nonneg hY0.le _)) (by linarith)
      _ = 1 / 4 := by field_simp
  rw [hsum, ← Real.rpow_mul hY0.le, show 48 * A * (2 * (1 / 48) - 1 / 12) = -(2 * A) by ring] at h
  -- `√Y ≤ y^{1/2+ε}` and `1 ≤ y^{1/2+ε}`
  have hsq : √Y ≤ y ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    calc Y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hY0.le hYy (by norm_num)
      _ ≤ y ^ (1 / 2 + ε) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have h1 : 1 ≤ y ^ (1 / 2 + ε) := Real.one_le_rpow hy1 (by linarith)
  calc ‖WindowGRH.rampErr χ y‖ = ‖(WindowGRH.rampErr χ y + ((T + F : ℝ) : ℂ)) - ((T + F : ℝ) : ℂ)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖WindowGRH.rampErr χ y + ((T + F : ℝ) : ℂ)‖ + ‖((T + F : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 / 4 + (|T| + |F|) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (h.trans htail') (abs_add_le _ _)
    _ ≤ y ^ (1 / 2 + ε) := by linarith

/-- **CONDITIONAL. The twists for `ζ`** (conditional on the half-plane `Re s > 11/12`, through
`TwistFamily.exists_good` and `PrimeCharSums.norm_rampErr_add_le`). For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has
a pair `(q, d)` meeting `WinPair ε Y` whose three quadratic twists `χ_q`, `χ_d`, `χ_qχ_d` have
`‖E_χ(y)‖ ≤ y^{1/2+ε}` for every `y ∈ [Y, Y^A]`. -/
theorem exists_winPair_twists {ε A : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hA : 1 ≤ A) :
    ∀ᶠ Y in Filter.atTop, ∃ q d : ℕ, WinPair ε Y q d ∧ ∀ [Fact q.Prime] [Fact d.Prime], ∀ y ∈ Set.Icc Y (Y ^ A),
      ‖WindowGRH.rampErr (legChar q) y‖ ≤ y ^ (1 / 2 + ε) ∧ ‖WindowGRH.rampErr (legChar d) y‖ ≤ y ^ (1 / 2 + ε) ∧
        ‖WindowGRH.rampErr (chiQD q d) y‖ ≤ y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := PrimeCharSums.norm_rampErr_add_le (η := 1 / 48) (by norm_num) (by norm_num)
  have hA0 : 0 < A := by linarith
  have hlo := (isLittleO_log_rpow_rpow_atTop 3 (by positivity : (0 : ℝ) < ε / 5)).bound
    (c := 1 / (20000 * A)) (by positivity)
  filter_upwards [exists_good hε hε' hA, hlo,
    Filter.eventually_ge_atTop (max (Real.exp (600 + 10000 * A)) ((16 * C + 1) ^ 2))] with Y hY hYlo hY₀
  -- the scales: `ℓ = log Y ≥ 600 + 10⁴A`, `z = Y^{ε/5} ≥ 1`, `ℓ³ ≤ z/(20000A)`, `z² ≤ √Y` and `√Y ≥ 16C + 1`
  have hYe : Real.exp (600 + 10000 * A) ≤ Y := (le_max_left _ _).trans hY₀
  have hY2 : 2 ≤ Y := by
    have := Real.add_one_le_exp (600 + 10000 * A)
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hℓ : 600 + 10000 * A ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).2 hYe
  have hℓ1 : 1 ≤ Real.log Y := by linarith
  set ℓ := Real.log Y with hℓdef
  set z := Y ^ (ε / 5) with hzdef
  have hz1 : 1 ≤ z := Real.one_le_rpow hY1 (by positivity)
  have hℓ3 : ℓ ^ 3 ≤ 1 / (20000 * A) * z := by
    have h := hYlo
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (by positivity),
      show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hz2 : z ^ 2 ≤ √Y := by
    rw [Real.sqrt_eq_rpow, hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by push_cast; linarith)
  have hsqY : 16 * C + 1 ≤ √Y := by
    rw [show 16 * C + 1 = √((16 * C + 1) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hY₀)
  have hℓℓ : ℓ ≤ ℓ ^ 3 := le_self_pow₀ hℓ1 (by norm_num)
  have hℓz : ℓ ^ 3 * z ≤ √Y / (20000 * A) := by
    calc ℓ ^ 3 * z ≤ 1 / (20000 * A) * z * z := by gcongr
      _ = z ^ 2 / (20000 * A) := by ring
      _ ≤ √Y / (20000 * A) := by gcongr
  -- the terms with `(n, M) > 1`: at most `⌊log₂ Z⌋ log M ≤ 96Aℓ·6z ≤ √Y/4` when `log M ≤ 6z`
  have hfix : ∀ M : ℕ, M ≠ 0 → Real.log M ≤ 6 * z → Nat.log 2 ⌊Y ^ (48 * A)⌋₊ * Real.log M ≤ √Y / 4 := by
    intro M hM hMz
    have hZ0 : ⌊Y ^ (48 * A)⌋₊ ≠ 0 := by
      have := (Nat.one_le_floor_iff (Y ^ (48 * A))).2 (Real.one_le_rpow hY1 (by positivity))
      omega
    have hlog2 : (Nat.log 2 ⌊Y ^ (48 * A)⌋₊ : ℝ) * Real.log 2 ≤ 48 * A * ℓ := by
      have h' : (2 : ℝ) ^ Nat.log 2 ⌊Y ^ (48 * A)⌋₊ ≤ Y ^ (48 * A) :=
        (by exact_mod_cast Nat.pow_log_le_self 2 hZ0 : (2 : ℝ) ^ Nat.log 2 ⌊Y ^ (48 * A)⌋₊ ≤
          (⌊Y ^ (48 * A)⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))
      rw [← Real.log_pow, hℓdef, ← Real.log_rpow hY0]
      exact Real.log_le_log (by positivity) h'
    have hl2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlM : 0 ≤ Real.log M := Real.log_natCast_nonneg M
    have hN : (Nat.log 2 ⌊Y ^ (48 * A)⌋₊ : ℝ) ≤ 96 * A * ℓ := by
      have := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊Y ^ (48 * A)⌋₊))
      linarith
    calc (Nat.log 2 ⌊Y ^ (48 * A)⌋₊ : ℝ) * Real.log M ≤ 96 * A * ℓ * (6 * z) := by gcongr
      _ = 576 * A * (ℓ * z) := by ring
      _ ≤ 576 * A * (ℓ ^ 3 * z) := by gcongr
      _ ≤ 576 * A * (√Y / (20000 * A)) := by gcongr
      _ = 576 / 20000 * √Y := by
          field_simp
      _ ≤ √Y / 4 := by linarith [Real.sqrt_nonneg Y]
  -- the primes `q ≡ 3 (mod 8)` with `z/2 < log q ≤ z`
  have hl8 : Real.log (8 : ℕ) ≤ 3 := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hqL : 100 * (Real.log (8 : ℕ) + 100 * A * ℓ) ≤ z := by
    have h1 : 100 * (Real.log (8 : ℕ) + 100 * A * ℓ) ≤ (300 + 10000 * A) * ℓ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hℓℓ (by positivity : (0 : ℝ) ≤ 10000 * A)
      have : (1 : ℝ) ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
      linarith
    have h2 : (300 + 10000 * A) * ℓ ^ 3 ≤ (300 + 10000 * A) * (1 / (20000 * A) * z) := by gcongr
    have h3 : (300 + 10000 * A) * (1 / (20000 * A) * z) ≤ z := by
      rw [← mul_assoc, mul_one_div]
      exact mul_le_of_le_one_left (by linarith) ((div_le_one (by positivity)).2 (by linarith))
    linarith
  obtain ⟨q, hqP, hq⟩ := hY 8 3 z (fun _ => 1) (fun _ => 1) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => by simp) (fun _ => by simp) hqL
  obtain ⟨hqp, hq3, hqlo, hqhi⟩ := mem_family hqP
  have hq8 : q % 8 = 3 := hq3
  have : Fact q.Prime := ⟨hqp⟩
  -- the primes `d ≡ 8K − 1 (mod 16K)` with `z′/2 < log d ≤ z′`, `K = q Q(z)`
  obtain ⟨hQ0, hQ⟩ := oddPrimorial_le z
  set K := q * oddPrimorial z with hK
  have hKodd : Odd K := (Nat.odd_iff.2 (by omega)).mul (oddPrimorial_odd z)
  have hK1 : 1 ≤ K := hKodd.pos
  have hlK : Real.log ((16 * K : ℕ) : ℝ) ≤ 6 * z := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hQ0' : (0 : ℝ) < oddPrimorial z := by exact_mod_cast hQ0
    have hlQ : Real.log (oddPrimorial z) ≤ 2 * z := by
      calc Real.log (oddPrimorial z) ≤ Real.log ((4 : ℝ) ^ ⌊z⌋₊) :=
            Real.log_le_log hQ0' (by exact_mod_cast hQ)
        _ = ⌊z⌋₊ * Real.log 4 := by rw [Real.log_pow]
        _ ≤ z * 2 := by
            gcongr
            · exact Nat.floor_le (by linarith)
            · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
              push_cast
              linarith [Real.log_two_lt_d9]
        _ = 2 * z := by ring
    have hl16 : Real.log 16 ≤ 3 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    rw [hK]
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hq0.ne' hQ0'.ne']
    linarith
  have hdL : 100 * (Real.log ((16 * K : ℕ) : ℝ) + 100 * A * ℓ) ≤ z * ℓ ^ 2 := by
    have h1 : 100 * (Real.log ((16 * K : ℕ) : ℝ) + 100 * A * ℓ) ≤ z * (600 + 10000 * A * ℓ) := by
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 10000 * A * ℓ) hz1
      linarith
    have h2 : 600 + 10000 * A * ℓ ≤ ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hℓ (by linarith : (0 : ℝ) ≤ ℓ)
      linarith
    calc _ ≤ z * (600 + 10000 * A * ℓ) := h1
      _ ≤ z * ℓ ^ 2 := by gcongr
  obtain ⟨d, hdP, hd⟩ := hY (16 * K) (8 * K - 1) (z * ℓ ^ 2) (fun _ => 1) (fun n => (jacobiSym n q : ℝ))
    (by omega) (dvd_mul_of_dvd_left (by norm_num) _) (coprime_eight_mul_sub_one hK1) (fun _ => by simp)
    (fun n => abs_jacobiSym_le _ _) hdL
  obtain ⟨hdp, hdr, hdlo, hdhi⟩ := mem_family hdP
  obtain ⟨hd16, hKd⟩ := mod_sixteen_of_modEq hKodd hdr
  have : Fact d.Prime := ⟨hdp⟩
  have hqd : q ≠ d := by omega
  -- the tails: `C log(N + 2) ≤ C log 3qd ≤ C(2 + z + z′) ≤ 4C√Y ≤ Y/4` for `N ≤ qd`
  have htail : ∀ N : ℕ, N ≤ q * d → C * Real.log (N + 2) ≤ Y / 4 := by
    intro N hN
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_lt.le
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdp.one_lt.le
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hlog : Real.log (N + 2) ≤ 2 + z + z * ℓ ^ 2 := by
      calc Real.log (N + 2) ≤ Real.log (3 * q * d) := by
            refine Real.log_le_log (by positivity) ?_
            have : (N : ℝ) ≤ q * d := by exact_mod_cast hN
            have : (1 : ℝ) ≤ q * d := one_le_mul_of_one_le_of_one_le hq1 hd1
            linarith
        _ = Real.log 3 + Real.log q + Real.log d := by
            rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 + z + z * ℓ ^ 2 := by linarith
    have hzl : z + z * ℓ ^ 2 ≤ 2 * √Y := by
      have h1 : z ≤ z * ℓ ^ 2 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hℓ1)
      have h2 : z * ℓ ^ 2 ≤ ℓ ^ 3 * z := by
        rw [mul_comm (ℓ ^ 3)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ1 (by norm_num)) (by linarith)
      have h3 : √Y / (20000 * A) ≤ √Y := div_le_self (Real.sqrt_nonneg _) (by linarith)
      linarith
    calc C * Real.log (N + 2) ≤ C * (4 * √Y) := by
          gcongr
          linarith
      _ ≤ √Y / 16 * (4 * √Y) := by
          gcongr
          linarith
      _ = √Y * √Y / 4 := by ring
      _ = Y / 4 := by rw [Real.mul_self_sqrt hY0.le]
  refine ⟨q, d, ⟨hqp, hdp, hq8, hd16, ⟨hqlo, hqhi⟩, ⟨hdlo, hdhi⟩, (Dvd.intro _ rfl).trans hKd,
    fun p hp hp2 hpz => ((dvd_oddPrimorial hp hp2 hpz).trans (Dvd.intro_left _ rfl)).trans hKd⟩,
    fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact norm_rampErr_le hC (legChar_ne_one (by omega)) (by norm_num : (8 : ℕ) ≠ 0)
      (fun _ => by simp) (legChar_apply_jacobi q) hε.le hA hY2 hy (hq y hy).1
      (hfix 8 (by norm_num) (by linarith)) (htail q (Nat.le_mul_of_pos_right _ hdp.pos))
  · exact norm_rampErr_le hC (legChar_ne_one (by omega)) (by omega : 16 * K ≠ 0)
      (fun _ => by simp) (legChar_apply_jacobi d) hε.le hA hY2 hy (hd y hy).1
      (hfix _ (by omega) hlK) (htail d (Nat.le_mul_of_pos_left _ hqp.pos))
  · have hχ : chiQD q d ≠ 1 := by
      rw [chiQD, mul_comm (changeLevel _ (legChar q))]
      exact PrimeCharSums.mul_changeLevel_ne_one ((Nat.coprime_primes hqp hdp).2 hqd) _ (legChar_ne_one (by omega))
    exact norm_rampErr_le hC hχ (by omega : 16 * K ≠ 0) (fun n => abs_jacobiSym_le _ _)
      (chiQD_apply q d) hε.le hA hY2 hy (hd y hy).2 (hfix _ (by omega) hlK) (htail _ le_rfl)

end ZetaTwist

#print axioms ZetaTwist.exists_winPair_twists
