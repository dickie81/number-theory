import TwistFamily
import ZetaGap

/-!
# A pair of primes with small twists on a window — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, "The analytic inputs": the twists). The lattice side fixes a pair of primes `(q, d)` from the
window's base `Y` and then chooses its sub-window, so the twists of a character `χ` of order `o` by `χ_q`, `χ_d` and
`χ_qχ_d` must have ramp errors of square-root size uniformly on `[Y, Y^A]`. With `z = Y^{ε/5}` and `z′ = z log²Y`, the
pair must also satisfy (`WinPair`):

* `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)`, primes with `z/2 < log q ≤ z` and `z′/2 < log d ≤ z′`;
* `q` and every odd prime `p ≤ z` divide `d + 1`.

**CONDITIONAL.** `exists_winPair_twists` and `exists_winPair_twists_one` use the half-plane `Re s > 11/12` for `ζ` and
every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has
read (see `formalisations/openai-half-plane.md`), through `TwistFamily.exists_good_fin` and
`PrimeCharSums.norm_rampErr_add_le`. Lean checks them with the standard axioms only, but they are only as good as that
input, and must be cited as conditional on it.

* **The twists** (`twist`): `χ_d^α χ_q^β ψ` at level `f·q·d`, for `ψ` mod `f` and `α, β ∈ {0, 1}`. For `ψ = χ^k` they
  are the characters `D_{(α,β,κ^k)}` of a setting in which `κ` lifts `χ` (`ZetaBalance.Setting.Lifts.g_twist`). At `n`
  prime to `f·q·d` the primitive character takes the value `χ_d(n)^α χ_q(n)^β ψ(n)` (`prim_twist_apply`). The twist is
  not trivial when `(α, β) ≠ (0, 0)` and `q ≠ d` are odd primes not dividing `f` (`twist_ne_one`): otherwise the
  conductor `d` of `χ_d`, or `q` of `χ_q`, would divide the product of the conductors of the other two factors.
* `exists_winPair_twists`: for `χ` mod `f`, `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has such a pair whose `3o`
  twists `χ_d^α χ_q^β χ^k`, `(α, β) ≠ (0, 0)` and `k < o`, have primitive characters with ramp errors
  `‖E(y)‖ ≤ y^{1/2+ε}` on `[Y, Y^A]`. It applies the generic lemma `TwistFamily.exists_good_fin` twice:
  - **`q`**: the primes `q ≡ 3 (mod 8)` with `L = z`, and the `o` weights `χ^k`;
  - **`d`, given `q`**: the primes `d ≡ 8K − 1 (mod 16K)` with `L = z′`, for `K = q·∏_{2 < p ≤ z} p`
    (`oddPrimorial`), and the `2o` weights `χ^k` and `χ^kχ_q`. Then `d ≡ 7 (mod 16)` and `K ∣ d + 1`
    (`mod_sixteen_of_modEq`), and `log 16K ≤ 6z`.

  For large `Y`, `log f ≤ z/2`, so `q` and `d` exceed `f`.
* **From the free part to the ramp error** (`norm_rampErr_le`). Let `χ(n) = b(n)J(n | d)` at every `n` prime to `Q`, a
  multiple of the family's modulus `M`. With `Z = ⌊Y^{48A}⌋`, the sum `Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n)` of
  `PrimeCharSums.rampErr_eq` differs from the free part `TwistFamily.freeC` only at the `n` that share a prime with `Q`.
  Those weigh at most `2⌊log₂ Z⌋ log Q` (`sum_not_coprime_le`), which is `≤ √Y/4` for `Q = M·f·q·d`, as
  `log Q ≤ 9z log²Y`. The tail `yC log(N + 2) Y^{−2A}` of `PrimeCharSums.norm_rampErr_add_le` is at most `1/4`.
* `exists_winPair_twists_one`: the case `χ = 1`, with the three quadratic twists as `χ_q`, `χ_d` and `χ_qχ_d`
  (`chiQD`, primitive by `chiQD_isPrimitive`).
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

/-! ### The twists -/

/-- The twist `χ_d^α χ_q^β ψ` of a character `ψ` mod `f`, at level `f·q·d`, for `α, β ∈ {0, 1}` (`false`, `true`). -/
noncomputable def twist {f : ℕ} (ψ : DirichletCharacter ℂ f) (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (α β : Bool) :
    DirichletCharacter ℂ (f * q * d) :=
  changeLevel (dvd_mul_left d (f * q)) (legPow d α) * changeLevel ((dvd_mul_left q f).mul_right d) (legPow q β) *
    changeLevel ((dvd_mul_right f q).mul_right d) ψ

/-- At `n` prime to `f·q·d`, the primitive character of the twist takes the value `χ_d(n)^α χ_q(n)^β ψ(n)`. -/
lemma prim_twist_apply {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) (q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (α β : Bool) {n : ℕ} (hn : n.Coprime (f * q * d)) :
    (twist ψ q d α β).primitiveCharacter n = legPow d α n * legPow q β n * ψ n := by
  have h := primitiveCharacter_apply_of_isCoprime (twist ψ q d α β) (Nat.isCoprime_iff_coprime.2 hn)
  simp only [Int.cast_natCast] at h
  rw [h, twist, MulChar.mul_apply, MulChar.mul_apply, PrimeCharSums.changeLevel_natCast _ _ hn,
    PrimeCharSums.changeLevel_natCast _ _ hn, PrimeCharSums.changeLevel_natCast _ _ hn]

/-- **A twist by `χ_q` or `χ_d` is not trivial**, for odd primes `q ≠ d` that do not divide `f`. Otherwise the conductor
`d` of `χ_d` (or `q` of `χ_q`) would divide the product of the conductors of the other two factors, which divides `qf`
(or `df`). -/
lemma twist_ne_one {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f) {q d : ℕ} [hq : Fact q.Prime] [hd : Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) (hqf : ¬q ∣ f) (hdf : ¬d ∣ f) {α β : Bool} (hαβ : (α || β) = true) :
    twist ψ q d α β ≠ 1 := by
  have h₁ : d ∣ f * q * d := dvd_mul_left d (f * q)
  have h₂ : q ∣ f * q * d := (dvd_mul_left q f).mul_right d
  have h₃ : f ∣ f * q * d := (dvd_mul_right f q).mul_right d
  -- the conductors of the three factors
  have hc {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : p ∣ f * q * d) (γ : Bool) :
      (changeLevel hp (legPow p γ)).conductor = if γ then p else 1 := by
    rw [conductor_changeLevel]
    cases γ
    · exact conductor_one
    · exact (isPrimitive_def _).1 (legChar_isPrimitive hp2)
  have hψ : (changeLevel h₃ ψ).conductor ∣ f := by
    rw [conductor_changeLevel]
    exact conductor_dvd_level _
  have hle (γ : Bool) (p : ℕ) : (if γ then p else 1) ∣ p := by cases γ <;> simp
  -- if `X·Y·Z = 1`, the conductor of `X` divides the product of those of `Y` and `Z`
  have key {X Y Z : DirichletCharacter ℂ (f * q * d)} (h : X * Y * Z = 1) :
      X.conductor ∣ Y.conductor * Z.conductor := by
    rw [eq_inv_of_mul_eq_one_left ((mul_assoc X Y Z).symm.trans h), conductor_inv]
    exact (conductor_mul_dvd_lcm_conductor Y Z).trans (Nat.lcm_dvd_mul _ _)
  intro h
  change changeLevel h₁ (legPow d α) * changeLevel h₂ (legPow q β) * changeLevel h₃ ψ = 1 at h
  cases α
  · -- `β = 1`: `q ∣ d·f`
    obtain rfl : β = true := by simpa using hαβ
    have := key (by rwa [mul_comm (changeLevel h₂ _)])
    rw [hc hq2 h₂, hc hd2 h₁] at this
    rcases (Nat.Prime.dvd_mul hq.out).1 (this.trans (mul_dvd_mul (hle _ d) hψ)) with h' | h'
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hq.out hd.out).1 h')
    · exact hqf h'
  · -- `α = 1`: `d ∣ q·f`
    have := key h
    rw [hc hd2 h₁, hc hq2 h₂] at this
    rcases (Nat.Prime.dvd_mul hd.out).1 (this.trans (mul_dvd_mul (hle _ q) hψ)) with h' | h'
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd.out hq.out).1 h').symm
    · exact hdf h'

/-! ### The arithmetic of the pair -/

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

/-! ### From the free part to the ramp error -/

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
`PrimeCharSums.norm_rampErr_add_le` at `η = 1/48`). Let `χ ≠ 1` mod `N`, `M ∣ Q`, and `χ(n) = b(n)J(n | d)` with
`‖b‖ ≤ 1` at every `n` prime to `Q`; let `y ∈ [Y, Y^A]` and `Z = ⌊Y^{48A}⌋`. The sum `Σ_{n ≤ Z} Λ(n)χ(n) min(1, y/n)`
differs from `T_d(y)` only at the `n` that share a prime with `Q`, by at most `2⌊log₂ Z⌋ log Q`
(`sum_not_coprime_le`), and the tail is `yC log(N + 2) Y^{−2A} ≤ C log(N + 2)/Y`. So `‖E_χ(y)‖ ≤ y^{1/2+ε}` if
`‖T_d(y)‖ ≤ y^{1/2+ε}/2`, `⌊log₂ Z⌋ log Q ≤ √Y/8` and `C log(N + 2) ≤ Y/4`. -/
lemma norm_rampErr_le {C : ℝ}
    (hC : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y Z : ℝ, 0 ≤ y → y ≤ Z → 1 < Z →
      ‖WindowGRH.rampErr χ y + ∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ)‖ ≤
        y * (C * Real.log (N + 2) * Z ^ (2 * (1 / 48) - 1 / 12 : ℝ)))
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {M Q : ℕ} (hQ : Q ≠ 0) (hMQ : M ∣ Q)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {d : ℕ} (hval : ∀ n : ℕ, n.Coprime Q → χ n = b n * jacobiSym n d)
    {ε A Y y : ℝ} (hε : 0 ≤ ε) (hA : 1 ≤ A) (hY : 2 ≤ Y) (hy : y ∈ Set.Icc Y (Y ^ A))
    (hfree : ‖freeC M ⌊Y ^ (48 * A)⌋₊ b d y‖ ≤ y ^ (1 / 2 + ε) / 2)
    (hfix : Nat.log 2 ⌊Y ^ (48 * A)⌋₊ * Real.log Q ≤ √Y / 8) (htail : C * Real.log (N + 2) ≤ Y / 4) :
    ‖WindowGRH.rampErr χ y‖ ≤ y ^ (1 / 2 + ε) := by
  obtain ⟨hYy, hyA⟩ := hy
  have hY0 : 0 < Y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hAZ : Y ^ A ≤ Y ^ (48 * A) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h := hC N χ hχ y _ (by linarith) (hyA.trans hAZ) (Real.one_lt_rpow (by linarith) (by linarith))
  set Z := ⌊Y ^ (48 * A)⌋₊
  set S := ∑ n ∈ Icc 1 Z, (Λ n : ℂ) * χ n * ((min 1 (y / n) : ℝ) : ℂ) with hS
  -- `S` differs from `T_d(y)` only at the `n` that share a prime with `Q`, each by at most `2Λ(n)`
  have hdiff : ‖S - freeC M Z b d y‖ ≤ 2 * (Nat.log 2 Z * Real.log Q) := by
    rw [hS, freeC, sum_filter, ← sum_sub_distrib, ← sum_filter_add_sum_filter_not _ fun n => n.Coprime Q,
      sum_eq_zero fun n hn => ?_, zero_add]
    · refine (norm_sum_le _ _).trans ((sum_le_sum (g := fun n => 2 * Λ n) fun n _ => ?_).trans ?_)
      swap
      · rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_not_coprime_le hQ Z) zero_le_two
      have hΛ (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖(Λ n : ℂ) * u‖ ≤ Λ n := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg hu
      have hm : ‖((min 1 (y / n) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (le_min zero_le_one (by positivity))]
        exact min_le_left _ _
      have hJ : ‖((jacobiSym n d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        exact abs_jacobiSym_le _ _
      have h1 := hΛ _ (norm_mul_le_of_le (norm_le_one χ n) hm |>.trans_eq (one_mul 1))
      have h2 := hΛ _ ((norm_mul_le_of_le (norm_mul_le_of_le (hb n) hm |>.trans_eq (one_mul 1)) hJ).trans_eq
        (one_mul 1))
      rw [← mul_assoc] at h1
      rw [← mul_assoc, ← mul_assoc] at h2
      split_ifs
      · exact (norm_sub_le _ _).trans (by linarith)
      · rw [sub_zero]
        linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
    · have hn := (mem_filter.1 hn).2
      rw [ite_eq_left (Nat.Coprime.coprime_dvd_right hMQ hn), hval n hn]
      ring
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
  rw [← Real.rpow_mul hY0.le, show 48 * A * (2 * (1 / 48) - 1 / 12) = -(2 * A) by ring] at h
  -- `√Y ≤ y^{1/2+ε}` and `1 ≤ y^{1/2+ε}`
  have hsq : √Y ≤ y ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    calc Y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hY0.le hYy (by norm_num)
      _ ≤ y ^ (1 / 2 + ε) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have h1 : 1 ≤ y ^ (1 / 2 + ε) := Real.one_le_rpow hy1 (by linarith)
  calc ‖WindowGRH.rampErr χ y‖ = ‖(WindowGRH.rampErr χ y + S) - (S - freeC M Z b d y) - freeC M Z b d y‖ := by
        congr 1
        ring
    _ ≤ ‖WindowGRH.rampErr χ y + S‖ + ‖S - freeC M Z b d y‖ + ‖freeC M Z b d y‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 / 4 + 2 * (√Y / 8) + y ^ (1 / 2 + ε) / 2 := by
        gcongr
        exacts [h.trans htail', hdiff.trans (by linarith)]
    _ ≤ y ^ (1 / 2 + ε) := by linarith

/-! ### The pair -/

/-- **CONDITIONAL. The twists for every character** (conditional on the half-plane `Re s > 11/12`, through
`TwistFamily.exists_good_fin` and `PrimeCharSums.norm_rampErr_add_le`). Let `χ` be a character mod `f`, of order `o`.
For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has a pair `(q, d)` meeting `WinPair ε Y` whose `3o` twists
`χ_d^α χ_q^β χ^k`, `(α, β) ≠ (0, 0)` and `k < o`, have primitive characters with `‖E(y)‖ ≤ y^{1/2+ε}` for every
`y ∈ [Y, Y^A]`. -/
theorem exists_winPair_twists {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) {ε A : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) (hA : 1 ≤ A) :
    ∀ᶠ Y in Filter.atTop, ∃ q d : ℕ, WinPair ε Y q d ∧ ∀ [Fact q.Prime] [Fact d.Prime], ∀ y ∈ Set.Icc Y (Y ^ A),
      ∀ α β : Bool, (α || β) = true → ∀ k < orderOf χ,
        ‖WindowGRH.rampErr (twist (χ ^ k) q d α β).primitiveCharacter y‖ ≤ y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := PrimeCharSums.norm_rampErr_add_le (η := 1 / 48) (by norm_num) (by norm_num)
  have hA0 : 0 < A := by linarith
  have hlo := (isLittleO_log_rpow_rpow_atTop 3 (by positivity : (0 : ℝ) < ε / 5)).bound
    (c := 1 / (20000 * A)) (by positivity)
  filter_upwards [exists_good_fin hε hε' hA (Fin (orderOf χ) × Bool), hlo,
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 5)).eventually_ge_atTop (2 * Real.log f),
    Filter.eventually_ge_atTop (max (Real.exp (600 + 10000 * A)) ((16 * C + 1) ^ 2))] with Y hY hYlo hzf hY₀
  -- the scales: `ℓ = log Y ≥ 600 + 10⁴A`, `z = Y^{ε/5} ≥ 1`, `ℓ³ ≤ z/(20000A)`, `z² ≤ √Y`, `√Y ≥ 16C + 1` and
  -- `log f ≤ z/2`
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
  have hzℓ : 9 * z * ℓ ^ 2 ≤ √Y / 2000 := by
    have h1 : z * ℓ ^ 2 ≤ ℓ ^ 3 * z := by
      rw [mul_comm (ℓ ^ 3)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ1 (by norm_num)) (by linarith)
    have h2 : √Y / (20000 * A) ≤ √Y / 20000 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) (by linarith)
    linarith
  -- a modulus `Q` with `log Q ≤ 9zℓ²`: the terms that share a prime with `Q`, at most `⌊log₂ Z⌋ log Q ≤ √Y/8`
  have hfix : ∀ Q : ℕ, Real.log Q ≤ 9 * z * ℓ ^ 2 → Nat.log 2 ⌊Y ^ (48 * A)⌋₊ * Real.log Q ≤ √Y / 8 := by
    intro Q hQz
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
    have hN : (Nat.log 2 ⌊Y ^ (48 * A)⌋₊ : ℝ) ≤ 96 * A * ℓ := by
      have := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊Y ^ (48 * A)⌋₊))
      linarith
    calc (Nat.log 2 ⌊Y ^ (48 * A)⌋₊ : ℝ) * Real.log Q ≤ 96 * A * ℓ * (9 * z * ℓ ^ 2) := by gcongr
      _ = 864 * A * (ℓ ^ 3 * z) := by ring
      _ ≤ 864 * A * (√Y / (20000 * A)) := by gcongr
      _ = 864 / 20000 * √Y := by field_simp
      _ ≤ √Y / 8 := by linarith [Real.sqrt_nonneg Y]
  -- and the tails: `C log(N + 2) ≤ C(2 + log Q) ≤ 3C√Y ≤ Y/4` for `0 < N ≤ Q`
  have htail : ∀ Q N : ℕ, Real.log Q ≤ 9 * z * ℓ ^ 2 → 0 < N → N ≤ Q → C * Real.log (N + 2) ≤ Y / 4 := by
    intro Q N hQz hN hNQ
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNQ' : (N : ℝ) ≤ Q := by exact_mod_cast hNQ
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hlog : Real.log (N + 2) ≤ 2 + 9 * z * ℓ ^ 2 := by
      calc Real.log (N + 2) ≤ Real.log (3 * Q) := Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 3 + Real.log Q := Real.log_mul (by norm_num) (by linarith)
        _ ≤ 2 + 9 * z * ℓ ^ 2 := by linarith
    have hsq1 : 1 ≤ √Y := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt hY1
    calc C * Real.log (N + 2) ≤ C * (3 * √Y) := by
          gcongr
          linarith
      _ ≤ √Y / 16 * (3 * √Y) := by
          gcongr
          linarith
      _ = 3 / 16 * (√Y * √Y) := by ring
      _ ≤ Y / 4 := by
          rw [Real.mul_self_sqrt hY0.le]
          linarith
  -- the primes `q ≡ 3 (mod 8)` with `z/2 < log q ≤ z`, good for the weights `χ^k`
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
  obtain ⟨q, hqP, hq⟩ := hY 8 3 z (fun i n => (χ ^ (i.1 : ℕ)) n) (by norm_num) (by norm_num) (by norm_num)
    (fun i n => norm_le_one _ _) hqL
  obtain ⟨hqp, hq3, hqlo, hqhi⟩ := mem_family hqP
  have hq8 : q % 8 = 3 := hq3
  have : Fact q.Prime := ⟨hqp⟩
  -- the primes `d ≡ 8K − 1 (mod 16K)` with `z′/2 < log d ≤ z′`, `K = q Q(z)`, good for the weights `χ^kχ_q^β`
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
  obtain ⟨d, hdP, hd⟩ := hY (16 * K) (8 * K - 1) (z * ℓ ^ 2) (fun i n => legPow q i.2 n * (χ ^ (i.1 : ℕ)) n)
    (by omega) (dvd_mul_of_dvd_left (by norm_num) _) (coprime_eight_mul_sub_one hK1)
    (fun i n => (norm_mul_le_of_le (norm_le_one _ _) (norm_le_one _ _)).trans_eq (one_mul 1)) hdL
  obtain ⟨hdp, hdr, hdlo, hdhi⟩ := mem_family hdP
  obtain ⟨hd16, hKd⟩ := mod_sixteen_of_modEq hKodd hdr
  have : Fact d.Prime := ⟨hdp⟩
  have hqd : q ≠ d := by omega
  -- `q` and `d` exceed `f`, as `log f ≤ z/2`
  have hf0 : (0 : ℝ) < f := by exact_mod_cast NeZero.pos f
  have hzz : z ≤ z * ℓ ^ 2 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hℓ1)
  have hlt {p : ℕ} (hp : p.Prime) (hpf : z / 2 < Real.log p) : ¬p ∣ f := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Nat.not_dvd_of_pos_of_lt (NeZero.pos f) (by exact_mod_cast (Real.log_lt_log_iff hf0 hp0).1 (by linarith))
  have hqf := hlt hqp hqlo
  have hdf := hlt hdp (by linarith)
  -- `log(M·f·q·d) ≤ 9zℓ²` for `log M ≤ 6z`
  have hlogQ {M : ℕ} (hM : 0 < M) (hMz : Real.log M ≤ 6 * z) :
      Real.log ((M * (f * q * d) : ℕ) : ℝ) ≤ 9 * z * ℓ ^ 2 := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hdp.pos
    push_cast
    rw [Real.log_mul hM0.ne' (by positivity), Real.log_mul (by positivity) hd0.ne', Real.log_mul hf0.ne' hq0.ne']
    linarith
  refine ⟨q, d, ⟨hqp, hdp, hq8, hd16, ⟨hqlo, hqhi⟩, ⟨hdlo, hdhi⟩, (Dvd.intro _ rfl).trans hKd,
    fun p hp hp2 hpz => ((dvd_oddPrimorial hp hp2 hpz).trans (Dvd.intro_left _ rfl)).trans hKd⟩,
    fun y hy α β hαβ k hk => ?_⟩
  -- the twist is not trivial, and its conductor is at most `f·q·d`
  have hT : (twist (χ ^ k) q d α β).primitiveCharacter ≠ 1 := fun h =>
    twist_ne_one (χ ^ k) (by omega) (by omega) hqd hqf hdf hαβ ((prim_eq_one_iff _).1 h)
  have hN {M : ℕ} (hM : 0 < M) : (twist (χ ^ k) q d α β).conductor ≤ M * (f * q * d) :=
    (Nat.le_of_dvd (NeZero.pos _) (conductor_dvd_level _)).trans (Nat.le_mul_of_pos_left _ hM)
  have hc {M n : ℕ} (hn : n.Coprime (M * (f * q * d))) : n.Coprime (f * q * d) :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hn
  cases α
  · -- `α = 0`, `β = 1`: the twist `χ^kχ_q`, from the family of `q`
    obtain rfl : β = true := by simpa using hαβ
    have hQ := hlogQ (M := 8) (by norm_num) (by linarith)
    refine norm_rampErr_le hC hT (Nat.mul_ne_zero (by norm_num) (NeZero.ne _)) (dvd_mul_right 8 _)
      (b := fun n => (χ ^ k) n) (fun n => norm_le_one _ _) (fun n hn => ?_) hε.le hA hY2 hy (hq (⟨k, hk⟩, true) y hy)
      (hfix _ hQ) (htail _ _ hQ (NeZero.pos _) (hN (by norm_num)))
    rw [prim_twist_apply _ _ _ _ _ (hc hn)]
    have hnd : IsUnit (n : ZMod d) :=
      (ZMod.isUnit_iff_coprime n d).2 (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) (hc hn))
    simp only [legPow, Bool.false_eq_true, ite_false, ite_true, MulChar.one_apply hnd, legChar_natCast,
      jacobiSym.legendreSym.to_jacobiSym]
    ring
  · -- `α = 1`: the twist `χ^kχ_q^βχ_d`, from the family of `d`
    have hQ := hlogQ (M := 16 * K) (by omega) hlK
    refine norm_rampErr_le hC hT (Nat.mul_ne_zero (by omega) (NeZero.ne _)) (dvd_mul_right _ _)
      (b := fun n => legPow q β n * (χ ^ k) n)
      (fun n => (norm_mul_le_of_le (norm_le_one _ _) (norm_le_one _ _)).trans_eq (one_mul 1))
      (fun n hn => ?_) hε.le hA hY2 hy (hd (⟨k, hk⟩, β) y hy) (hfix _ hQ) (htail _ _ hQ (NeZero.pos _) (hN (by omega)))
    rw [prim_twist_apply _ _ _ _ _ (hc hn)]
    simp only [legPow, ite_true, legChar_natCast, jacobiSym.legendreSym.to_jacobiSym]
    ring

/-! ### `ζ`: the quadratic twists -/

/-- `χ_qχ_d`, the product of the Legendre symbols mod `q` and mod `d`, at level `qd`. -/
noncomputable def chiQD (q d : ℕ) [Fact q.Prime] [Fact d.Prime] : DirichletCharacter ℂ (q * d) :=
  changeLevel (q.dvd_mul_right d) (legChar q) * changeLevel (d.dvd_mul_left q) (legChar d)

/-- **`χ_qχ_d` is primitive**, for distinct odd primes `q` and `d`. Its primitive character vanishes at `d`, as `χ_d`
does (`ZetaBalance.prim_mul_apply`), and likewise at `q`, so `qd` divides its conductor. -/
theorem chiQD_isPrimitive {q d : ℕ} [hq : Fact q.Prime] [hd : Fact d.Prime] (hq2 : q ≠ 2) (hd2 : d ≠ 2)
    (hqd : q ≠ d) : (chiQD q d).IsPrimitive := by
  have hcop := (Nat.coprime_primes hq.out hd.out).2 hqd
  have hzero {p : ℕ} (hp : p.Prime) (h : (chiQD q d).primitiveCharacter p = 0) : p ∣ (chiQD q d).conductor := by
    rwa [← Int.cast_natCast, apply_eq_zero_iff, Nat.isCoprime_iff_coprime, hp.coprime_iff_not_dvd, not_not] at h
  have h1 : (chiQD q d).primitiveCharacter d = 0 := by
    rw [chiQD, prim_mul_apply _ _ _ hd.out (hd.out.coprime_iff_not_dvd.1 hcop.symm), prim_changeLevel,
      prim_apply_of_isPrimitive (legChar_isPrimitive hd2), ZMod.natCast_self, legChar_zero, mul_zero]
  have h2 : (chiQD q d).primitiveCharacter q = 0 := by
    rw [chiQD, mul_comm (changeLevel _ (legChar q)), prim_mul_apply _ _ _ hq.out (hq.out.coprime_iff_not_dvd.1 hcop),
      prim_changeLevel, prim_apply_of_isPrimitive (legChar_isPrimitive hq2), ZMod.natCast_self, legChar_zero,
      mul_zero]
  exact Nat.dvd_antisymm (conductor_dvd_level _) (hcop.mul_dvd_of_dvd_of_dvd (hzero hq.out h2) (hzero hd.out h1))

/-- The ramp error of the primitive character of `D`, a primitive `ψ` changed to a higher level, is that of `ψ`. -/
theorem rampErr_prim_changeLevel_of_isPrimitive {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N)
    {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) {D : DirichletCharacter ℂ N} (hD : D = changeLevel h ψ)
    (y : ℝ) : WindowGRH.rampErr D.primitiveCharacter y = WindowGRH.rampErr ψ y := by
  subst hD
  rw [rampErr_prim_changeLevel]
  exact rampErr_congr ((isPrimitive_def _).1 hψ) (prim_apply_of_isPrimitive hψ) y

/-- **CONDITIONAL. The twists for `ζ`** (conditional on the half-plane `Re s > 11/12`, through
`exists_winPair_twists`). For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has a pair `(q, d)` meeting `WinPair ε Y`
whose three quadratic twists `χ_q`, `χ_d`, `χ_qχ_d` have `‖E_χ(y)‖ ≤ y^{1/2+ε}` for every `y ∈ [Y, Y^A]`: the case
`χ = 1` of `exists_winPair_twists`, as `χ_q`, `χ_d` and `χ_qχ_d` are primitive. -/
theorem exists_winPair_twists_one {ε A : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hA : 1 ≤ A) :
    ∀ᶠ Y in Filter.atTop, ∃ q d : ℕ, WinPair ε Y q d ∧ ∀ [Fact q.Prime] [Fact d.Prime], ∀ y ∈ Set.Icc Y (Y ^ A),
      ‖WindowGRH.rampErr (legChar q) y‖ ≤ y ^ (1 / 2 + ε) ∧ ‖WindowGRH.rampErr (legChar d) y‖ ≤ y ^ (1 / 2 + ε) ∧
        ‖WindowGRH.rampErr (chiQD q d) y‖ ≤ y ^ (1 / 2 + ε) := by
  filter_upwards [exists_winPair_twists (1 : DirichletCharacter ℂ 1) hε hε' hA] with Y ⟨q, d, hp, h⟩
  refine ⟨q, d, hp, fun y hy => ?_⟩
  have hq2 : q ≠ 2 := by have := hp.q_mod; omega
  have hd2 : d ≠ 2 := by have := hp.d_mod; omega
  have hqd : q ≠ d := by have := hp.q_mod; have := hp.d_mod; omega
  have e (α β : Bool) (hαβ : (α || β) = true) {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
      (hψ : ψ.IsPrimitive) (hM : M ∣ 1 * q * d) (hT : twist 1 q d α β = changeLevel hM ψ) :
      ‖WindowGRH.rampErr ψ y‖ ≤ y ^ (1 / 2 + ε) := by
    have := h y hy α β hαβ 0 (orderOf_pos _)
    rwa [pow_zero, rampErr_prim_changeLevel_of_isPrimitive hM hψ hT] at this
  refine ⟨e false true rfl (legChar_isPrimitive hq2) ((dvd_mul_left q 1).mul_right d) (by simp [twist, legPow]),
    e true false rfl (legChar_isPrimitive hd2) (dvd_mul_left d _) (by simp [twist, legPow]),
    e true true rfl (chiQD_isPrimitive hq2 hd2 hqd) ⟨1, by ring⟩ ?_⟩
  rw [chiQD, map_mul, ← changeLevel_trans, ← changeLevel_trans, mul_comm (changeLevel _ (legChar q))]
  simp [twist, legPow]

end ZetaTwist

#print axioms ZetaTwist.exists_winPair_twists
#print axioms ZetaTwist.exists_winPair_twists_one
