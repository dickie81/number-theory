import PrimeCharSums
import MeanSquareSup
import ZetaBalance

/-!
# A family of primes whose quadratic twists are small on a window — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "The analytic inputs": the twists). The
generic lemma behind `ZetaTwist.exists_winPair_twists`: in a family of primes `d` in a progression, most members have
a twisted prime sum of square-root size, uniformly on a window `[Y, Y^A]`.

**CONDITIONAL.** The results here whose doc comments say CONDITIONAL use the half-plane `Re s > 11/12` for `ζ` and every
Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read
(see `formalisations/openai-half-plane.md`), through `PrimeCharSums.norm_sum_Ioc_modEq_le` and
`PrimeCharSums.card_Ioc_modEq_ge`. Lean checks them with the standard axioms only, but they are only as good as that
input, and must be cited as conditional on it.

**The family.** For `M` with `4 ∣ M`, `r` prime to `M` and `L ≥ 0`, `family M r L` is the set `P` of primes `d ≡ r (M)`
with `e^{L/2} < d ≤ e^L`. For a weight `b` with `|b| ≤ 1` and a cutoff `Z`, the free part of `d` is
`T_d(y) = Σ_{n ≤ Z, (n, M) = 1} Λ(n) b(n) min(1, y/n) J(n | d)` (`free`), with `J` the Jacobi symbol.

* **The mean square** (`sum_sq_free_le`). Expanding `Σ_{d ∈ P} (Σ_n c(n)J(n | d))²` (`sum_sq_le`), a pair `(n, m)` with
  `nm` a square is bounded by `|P|`, and the others are sums of a character over `P`.
  - **Diagonal** (`sum_isSquare_le`). With `|c(n)| ≤ tΛ(n)/√n`, the square pairs weigh at most `t²·4 log²Z (1 + log Z)`:
    for `nm = j²`, `Σ_{nm = j²} Λ(n)Λ(m) ≤ (log j²)²` (Mathlib's `vonMangoldt_sum`).
  - **Off-diagonal** (`abs_sum_family_le`). For `nm` prime to `M` and not a square, reciprocity
    (`jacobiSym.quadratic_reciprocity'`) gives `J(n | d)J(m | d) = σ·J(d | nm)`, with a sign `σ` fixed by `d ≡ r (4)`.
    `J(· | nm)` is the library's Jacobi character (`JChar.jchar`), `≠ 1` as `nm` is not a square
    (`Kron.exists_jacobiSym_eq_neg_one`). So the sum over `P` is at most `C log(nmM + 2) e^{Lα}`,
    `α = 11/12 + 1/48` (`PrimeCharSums.norm_sum_Ioc_modEq_le`).
* **The size of the family** (`large_family`). Under `100(log M + 100 log W) ≤ L`, `|P| ≥ e^{31L/32}/(64M)`
  (`PrimeCharSums.card_Ioc_modEq_ge`), which beats the off-diagonal terms for `Z ≤ W^48`.
* **Sobolev and Markov** (`card_bad_quarter`). `MeanSquareSup.card_bad_le` with `M₀(k) = kD` and `M₁(k) = D/k`, where
  the increments `T_d(k + 1) − T_d(k)` have coefficients at most `Λ(n)/√(kn)`; its bound is `≤ D K₀^{−ε}(2 + 4ζ(1 + ε))`
  (`bound_le`). So at most a quarter of `P` has `T_d(k)² > k^{1+2ε}/16` for some integer `k ∈ [⌊Y⌋, ⌊Y^A⌋ + 1]`.
* **From integers to all `y`** (`abs_free_le`). `T_d` is affine between consecutive integers (`free_eq`), so a good `d`
  has `|T_d(y)| ≤ y^{1/2+ε}/2` on `[Y, Y^A]`.
* **The main result** (`exists_good`). For `Y` large, uniformly in `M`, `r`, `L` with `100(log M + 100A log Y) ≤ L` and
  in two weights `b₁`, `b₂`, some `d ∈ P` is good for both. The cutoff is `Z = ⌊Y^{48A}⌋`.

`ZetaTwist` applies it twice, and passes from `T_d` to the ramp errors.
-/

open Finset DirichletCharacter ZetaBalance
open scoped ArithmeticFunction.vonMangoldt

namespace TwistFamily

/-- The family `P`: the primes `d ≡ r (mod M)` with `e^{L/2} < d ≤ e^L`. -/
noncomputable def family (M r : ℕ) (L : ℝ) : Finset ℕ :=
  {d ∈ Ioc ⌊Real.exp (L / 2)⌋₊ ⌊Real.exp L⌋₊ | d.Prime ∧ d ≡ r [MOD M]}

/-- A member `d` of the family is a prime `≡ r (mod M)` with `L/2 < log d ≤ L`. -/
lemma mem_family {M r d : ℕ} {L : ℝ} (h : d ∈ family M r L) :
    d.Prime ∧ d ≡ r [MOD M] ∧ L / 2 < Real.log d ∧ Real.log d ≤ L := by
  obtain ⟨hd, hp, hr⟩ := mem_filter.1 h
  obtain ⟨h1, h2⟩ := mem_Ioc.1 hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hp.pos
  refine ⟨hp, hr, (Real.lt_log_iff_exp_lt hd0).2 (Nat.lt_of_floor_lt h1), (Real.log_le_iff_le_exp hd0).2 ?_⟩
  exact (Nat.cast_le.2 h2).trans (Nat.floor_le (Real.exp_pos _).le)

/-- The free part `T_d(y) = Σ_{n ≤ Z, (n, M) = 1} Λ(n) b(n) min(1, y/n) J(n | d)`. -/
noncomputable def free (M Z : ℕ) (b : ℕ → ℝ) (d : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 Z with n.Coprime M, Λ n * b n * min 1 (y / n) * (jacobiSym n d : ℝ)

/-! ### The mean square, expanded -/

/-- **The mean square, expanded.** For real `f` with `|f| ≤ 1`, the mean square over `P` of `Σ_{n ∈ I} c(n) f(n, d)` is
at most `|P|` times the sum of `|c(n)c(m)|` over the `bad` pairs, plus `E (Σ_n |c(n)|)²`, if every other pair has
`|Σ_{d ∈ P} f(n, d) f(m, d)| ≤ E`. -/
lemma sum_sq_le {ι : Type*} (P : Finset ι) (I : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ι → ℝ)
    (hf : ∀ n d, |f n d| ≤ 1) (bad : ℕ → ℕ → Prop) [DecidableRel bad] {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ n ∈ I, ∀ m ∈ I, ¬bad n m → |∑ d ∈ P, f n d * f m d| ≤ E) :
    ∑ d ∈ P, (∑ n ∈ I, c n * f n d) ^ 2 ≤
      #P * ∑ n ∈ I, ∑ m ∈ I with bad n m, |c n| * |c m| + E * (∑ n ∈ I, |c n|) ^ 2 := by
  have e : ∑ d ∈ P, (∑ n ∈ I, c n * f n d) ^ 2 =
      ∑ n ∈ I, ∑ m ∈ I, c n * c m * ∑ d ∈ P, f n d * f m d := by
    simp_rw [sq, sum_mul_sum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun d _ => by ring
  rw [e, sq, sum_mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  rw [sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun m hm => ?_
  have hX : |∑ d ∈ P, f n d * f m d| ≤ #P := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ P, |f n d * f m d| ≤ ∑ _d ∈ P, (1 : ℝ) := sum_le_sum fun d _ => by
          rw [abs_mul]
          nlinarith [hf n d, hf m d, abs_nonneg (f n d), abs_nonneg (f m d)]
      _ = #P := by simp
  have hcc : 0 ≤ |c n| * |c m| := by positivity
  have h1 : c n * c m * ∑ d ∈ P, f n d * f m d ≤ |c n| * |c m| * |∑ d ∈ P, f n d * f m d| := by
    rw [← abs_mul, ← abs_mul]
    exact le_abs_self _
  split_ifs with hb
  · nlinarith [mul_le_mul_of_nonneg_left hX hcc, mul_nonneg hE hcc]
  · nlinarith [mul_le_mul_of_nonneg_left (h n hn m hm hb) hcc]

/-- **The diagonal.** `Σ_{n, m ≤ Z, nm = □} Λ(n)Λ(m)/√(nm) ≤ 4 log²Z (1 + log Z)`: the pairs with `nm = j²` weigh at
most `Σ_{n ∣ j²} Λ(n) log j² = (log j²)²`, by Mathlib's `vonMangoldt_sum`. -/
lemma sum_isSquare_le (Z : ℕ) :
    ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z with IsSquare (n * m), Λ n / √n * (Λ m / √m) ≤
      4 * Real.log Z ^ 2 * (1 + Real.log Z) := by
  have hΛ := fun n : ℕ => (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  -- a square pair `nm = j²` is the term `j` of a sum over `j ≤ Z`
  have h1 : ∀ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z with IsSquare (n * m), Λ n / √n * (Λ m / √m) ≤
      ∑ m ∈ Icc 1 Z, ∑ j ∈ Icc 1 Z, if n * m = j * j then Λ n * Λ m / j else 0 := by
    intro n hn
    rw [sum_filter]
    refine sum_le_sum fun m hm => ?_
    split_ifs with hsq
    · obtain ⟨j, hj⟩ := hsq
      rw [mem_Icc] at hn hm
      have hj1 : j ∈ Icc 1 Z := mem_Icc.2 ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hj; omega),
        Nat.mul_self_le_mul_self_iff.1 (hj ▸ Nat.mul_le_mul hn.2 hm.2)⟩
      refine le_trans (le_of_eq ?_) (single_le_sum (f := fun j : ℕ => if n * m = j * j then Λ n * Λ m / j else 0)
        (fun j _ => by split_ifs <;> positivity) hj1)
      simp only [hj, ↓reduceIte]
      have hjr : √(n : ℝ) * √(m : ℝ) = j := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, hj, Nat.cast_mul,
          Real.sqrt_mul_self (Nat.cast_nonneg _)]
      rw [div_mul_div_comm, hjr]
    · exact sum_nonneg fun j _ => by split_ifs <;> positivity
  -- the pairs with `nm = j²` weigh at most `(log j²)²/j ≤ 4(log Z)²/j`
  have h2 : ∀ j ∈ Icc 1 Z, ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z, (if n * m = j * j then Λ n * Λ m / j else 0) ≤
      4 * Real.log Z ^ 2 * (j : ℝ)⁻¹ := by
    intro j hj
    rw [mem_Icc] at hj
    have hjj : j * j ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj.1)
    have hjZ : Real.log j ≤ Real.log Z := Real.log_le_log (by exact_mod_cast hj.1) (by exact_mod_cast hj.2)
    rw [← sum_product' (f := fun n m => if n * m = j * j then Λ n * Λ m / j else 0), ← sum_filter]
    calc ∑ x ∈ Icc 1 Z ×ˢ Icc 1 Z with x.1 * x.2 = j * j, Λ x.1 * Λ x.2 / j
        ≤ ∑ x ∈ (j * j).divisorsAntidiagonal, Λ x.1 * Λ x.2 / j := by
          refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => by positivity)
          exact Nat.mem_divisorsAntidiagonal.2 ⟨(mem_filter.1 hx).2, hjj⟩
      _ ≤ ∑ x ∈ (j * j).divisorsAntidiagonal, Λ x.1 * Real.log (j * j : ℕ) / j := by
          refine sum_le_sum fun x hx => ?_
          have h2 := Nat.snd_mem_divisors_of_mem_antidiagonal hx
          gcongr
          exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
            (by exact_mod_cast Nat.pos_of_mem_divisors h2) (by exact_mod_cast Nat.divisor_le h2))
      _ = Real.log (j * j : ℕ) ^ 2 / j := by
          rw [Nat.sum_divisorsAntidiagonal (fun a _ => Λ a * Real.log (j * j : ℕ) / j), ← sum_div, ← sum_mul,
            ArithmeticFunction.vonMangoldt_sum]
          ring
      _ ≤ 4 * Real.log Z ^ 2 * (j : ℝ)⁻¹ := by
          rw [Nat.cast_mul, Real.log_mul hj0 hj0, div_eq_mul_inv]
          gcongr
          nlinarith
  calc _ ≤ ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z, ∑ j ∈ Icc 1 Z, (if n * m = j * j then Λ n * Λ m / j else 0) :=
        sum_le_sum h1
    _ = ∑ j ∈ Icc 1 Z, ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z, (if n * m = j * j then Λ n * Λ m / j else 0) :=
        (sum_congr rfl fun n _ => sum_comm).trans sum_comm
    _ ≤ ∑ j ∈ Icc 1 Z, 4 * Real.log Z ^ 2 * (j : ℝ)⁻¹ := sum_le_sum h2
    _ ≤ 4 * Real.log Z ^ 2 * (1 + Real.log Z) := by
        rw [← mul_sum]
        gcongr
        have := harmonic_le_one_add_log Z
        rw [harmonic_eq_sum_Icc] at this
        push_cast at this
        exact this

/-! ### The off-diagonal pairs -/

/-- `|J(a | b)| ≤ 1` (`GSFund.norm_jac_le`). -/
lemma abs_jacobiSym_le (a : ℤ) (b : ℕ) : |(jacobiSym a b : ℝ)| ≤ 1 := by
  have := GSFund.norm_jac_le (n := b) a
  rwa [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at this

/-- The Jacobi character `J(· | N)` (`JChar.jchar`) is not `1` for odd `N` that is not a square: some `D` has
`J(D | N) = −1` (`Kron.exists_jacobiSym_eq_neg_one`). -/
lemma jchar_ne_one {N : ℕ} [Fact (1 < N)] (hN : Odd N) (hsq : ¬IsSquare N) : JChar.jchar N ≠ 1 := by
  obtain ⟨D, hD⟩ := Kron.exists_jacobiSym_eq_neg_one hN hsq
  refine GSEven.ne_one_of_neg _ (D % N).toNat ?_
  rw [JChar.jchar_nat, Int.toNat_of_nonneg (Int.emod_nonneg D (by have := (Fact.out : 1 < N); omega)),
    ← jacobiSym.mod_left, hD]
  norm_num

/-- **CONDITIONAL. The off-diagonal pairs** (conditional on the half-plane, through the bound `hC` of
`PrimeCharSums.norm_sum_Ioc_modEq_le`). For `nm` prime to `M` and not a square,
`|Σ_{d ∈ P} J(n | d)J(m | d)| ≤ C log(nmM + 2) e^{Lα}`. On `P`, `d ≡ r (4)`, so reciprocity gives
`J(n | d) = σ_n J(d | n)` with `σ_n = J(χ₄(r) | n)` (`jacobiSym.quadratic_reciprocity'`); and `J(d | n)J(d | m)` is
`J(d | nm)`, the Jacobi character mod `nm` (`JChar.jchar`), which is not `1` (`jchar_ne_one`). -/
lemma abs_sum_family_le {η C : ℝ}
    (hC : ∀ (N M : ℕ) [NeZero N] [NeZero M], N.Coprime M → ∀ a : ℕ, a.Coprime M →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → ∀ y x : ℝ, 0 ≤ y → y ≤ x →
        ‖∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p‖ ≤ C * Real.log (N * M + 2) * x ^ (11 / 12 + η))
    {M r : ℕ} [NeZero M] (hM : 4 ∣ M) (hr : r.Coprime M) {L : ℝ} (hL : 0 ≤ L) {n m : ℕ}
    (hnm : (n * m).Coprime M) (hsq : ¬IsSquare (n * m)) :
    |∑ d ∈ family M r L, (jacobiSym n d : ℝ) * jacobiSym m d| ≤
      C * Real.log (n * m * M + 2) * Real.exp L ^ (11 / 12 + η) := by
  have h2M : 2 ∣ M := (show 2 ∣ 4 by norm_num).trans hM
  have hodd : Odd (n * m) := Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right h2M hnm)
  have : Fact (1 < n * m) := ⟨by
    have h1 : n * m ≠ 1 := fun h => hsq (h ▸ ⟨1, rfl⟩)
    have := hodd.pos
    omega⟩
  -- reciprocity on the family: `J(n | d)J(m | d) = σ J(d | nm)`
  have hrec : ∀ d ∈ family M r L, (jacobiSym n d : ℝ) * jacobiSym m d =
      ((qrSign r n * qrSign r m * jacobiSym d (n * m) : ℤ) : ℝ) := by
    intro d hd
    obtain ⟨-, -, hdr⟩ := mem_filter.1 hd
    have hdM : d.Coprime M := by
      unfold Nat.Coprime
      rw [hdr.gcd_eq]
      exact hr
    have hd2 : Odd d := Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right h2M hdM)
    have h4 : (d : ZMod 4) = r := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hdr.of_dvd hM)
    have hq : ∀ k : ℕ, Odd k → jacobiSym k d = qrSign r k * jacobiSym d k := by
      intro k hk
      rw [jacobiSym.quadratic_reciprocity' hk hd2]
      simp only [qrSign, h4]
    rw [hq n (Nat.odd_mul.1 hodd).1, hq m (Nat.odd_mul.1 hodd).2,
      jacobiSym.mul_right' _ (Nat.odd_mul.1 hodd).1.pos.ne' (Nat.odd_mul.1 hodd).2.pos.ne']
    push_cast
    ring
  have hq1 : ∀ k : ℕ, |((qrSign r k : ℤ) : ℝ)| ≤ 1 := fun k => abs_jacobiSym_le _ _
  have hσ : ‖(((qrSign r n * qrSign r m : ℤ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Int.cast_mul, abs_mul]
    nlinarith [hq1 n, hq1 m, abs_nonneg ((qrSign r n : ℤ) : ℝ)]
  have hsum : ((∑ d ∈ family M r L, (jacobiSym n d : ℝ) * jacobiSym m d : ℝ) : ℂ) =
      (((qrSign r n * qrSign r m : ℤ) : ℝ) : ℂ) * ∑ d ∈ family M r L, JChar.jchar (n * m) d := by
    rw [Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun d hd => ?_
    rw [hrec d hd, JChar.jchar_nat]
    push_cast
    ring
  have hb := hC (n * m) M hnm r hr _ (jchar_ne_one hodd hsq) (Real.exp (L / 2)) (Real.exp L)
    (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith))
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hsum, norm_mul]
  calc _ ≤ 1 * ‖∑ d ∈ family M r L, JChar.jchar (n * m) d‖ := mul_le_mul_of_nonneg_right hσ (norm_nonneg _)
    _ ≤ _ := by
        rw [one_mul]
        exact hb.trans_eq (by push_cast; ring)

/-- **CONDITIONAL. The mean square of a free sum** (conditional on the half-plane, through `abs_sum_family_le`). If
`|c(n)| ≤ tΛ(n)/√n` and `|c(n)| ≤ Λ(n)`, then `Σ_{d ∈ P} (Σ_{n ≤ Z, (n, M) = 1} c(n)J(n | d))²` is at most
`|P| t²·4 log²Z (1 + log Z)`, the square pairs (`sum_isSquare_le`), plus `E (7Z)²` with
`E = C log(Z²M + 2) e^{Lα}`, the other pairs (`abs_sum_family_le`; `Σ_{n ≤ Z} Λ(n) = ψ(Z) ≤ 7Z`). -/
lemma sum_sq_free_le {η C : ℝ}
    (hC : ∀ (N M : ℕ) [NeZero N] [NeZero M], N.Coprime M → ∀ a : ℕ, a.Coprime M →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → ∀ y x : ℝ, 0 ≤ y → y ≤ x →
        ‖∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p‖ ≤ C * Real.log (N * M + 2) * x ^ (11 / 12 + η))
    (hC0 : 0 ≤ C) {M r : ℕ} [NeZero M] (hM : 4 ∣ M) (hr : r.Coprime M) {L : ℝ} (hL : 0 ≤ L) (Z : ℕ)
    (c : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) (hc : ∀ n, |c n| ≤ t * (Λ n / √n)) (hc' : ∀ n, |c n| ≤ Λ n) :
    ∑ d ∈ family M r L, (∑ n ∈ Icc 1 Z with n.Coprime M, c n * jacobiSym n d) ^ 2 ≤
      #(family M r L) * (t ^ 2 * (4 * Real.log Z ^ 2 * (1 + Real.log Z))) +
        C * Real.log (Z * Z * M + 2) * Real.exp L ^ (11 / 12 + η) * (7 * Z) ^ 2 := by
  have hE0 : 0 ≤ C * Real.log (Z * Z * M + 2) * Real.exp L ^ (11 / 12 + η) := by
    have : (0 : ℝ) ≤ Z * Z * M := by positivity
    have : 0 ≤ Real.log (Z * Z * M + 2) := Real.log_nonneg (by linarith)
    positivity
  refine (sum_sq_le (family M r L) {n ∈ Icc 1 Z | n.Coprime M} c (fun n d => (jacobiSym n d : ℝ))
    (fun n d => abs_jacobiSym_le _ _) (fun n m => IsSquare (n * m)) hE0 ?_).trans ?_
  · intro n hn m hm hsq
    obtain ⟨hn1, hnM⟩ := mem_filter.1 hn
    obtain ⟨hm1, hmM⟩ := mem_filter.1 hm
    refine (abs_sum_family_le hC hM hr hL (Nat.coprime_mul_iff_left.2 ⟨hnM, hmM⟩) hsq).trans ?_
    have hnZ : (n : ℝ) ≤ Z := by exact_mod_cast (mem_Icc.1 hn1).2
    have hmZ : (m : ℝ) ≤ Z := by exact_mod_cast (mem_Icc.1 hm1).2
    gcongr
  · refine add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) ?_
    · -- the square pairs
      calc _ ≤ ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z with IsSquare (n * m), t ^ 2 * (Λ n / √n * (Λ m / √m)) := by
            refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              fun n _ _ => sum_nonneg fun m _ => by positivity).trans' (sum_le_sum fun n _ => ?_)
            refine (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
              fun m _ _ => by positivity).trans' (sum_le_sum fun m _ => ?_)
            calc |c n| * |c m| ≤ (t * (Λ n / √n)) * (t * (Λ m / √m)) :=
                  mul_le_mul (hc n) (hc m) (abs_nonneg _) (by positivity)
              _ = _ := by ring
        _ = t ^ 2 * ∑ n ∈ Icc 1 Z, ∑ m ∈ Icc 1 Z with IsSquare (n * m), Λ n / √n * (Λ m / √m) := by
            simp_rw [mul_sum]
        _ ≤ t ^ 2 * (4 * Real.log Z ^ 2 * (1 + Real.log Z)) := by
            gcongr
            exact sum_isSquare_le Z
    · -- the other pairs: `Σ |c(n)| ≤ ψ(Z) ≤ 7Z`
      have hψ : ∑ n ∈ Icc 1 Z, Λ n ≤ 7 * Z := by
        have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) Z)
        have hI : Icc 1 Z = Ioc 0 Z := by simpa using Finset.Icc_add_one_left_eq_Ioc 0 Z
        rw [Chebyshev.psi, Nat.floor_natCast, ← hI] at h
        have h4 : Real.log 4 ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
          linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) Z]
      gcongr
      exact (sum_le_sum fun n _ => hc' n).trans ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg).trans hψ)

/-! ### The size of the family -/

/-- The arithmetic of the count: `v³²/(2M) ≤ (v³² − v¹⁶)/φ − cv³⁰` when `v ≥ 4`, `0 < φ ≤ M` and `4Mc ≤ v²`. -/
lemma count_arith {v M φ c : ℝ} (hv : 4 ≤ v) (hM : 1 ≤ M) (hφ : 0 < φ) (hφM : φ ≤ M)
    (hcv : 4 * M * c ≤ v ^ 2) : v ^ 32 / (2 * M) ≤ (v ^ 32 - v ^ 16) / φ - c * v ^ 30 := by
  have hv16 : 4 * v ^ 16 ≤ v ^ 32 := by
    have h4 : 4 ≤ v ^ 16 := hv.trans (le_self_pow₀ (by linarith) (by norm_num))
    calc 4 * v ^ 16 ≤ v ^ 16 * v ^ 16 := by gcongr
      _ = v ^ 32 := by ring
  have h0 : 0 ≤ v ^ 16 := by positivity
  have h1 : (v ^ 32 - v ^ 16) / M ≤ (v ^ 32 - v ^ 16) / φ := div_le_div_of_nonneg_left (by linarith) hφ hφM
  have h2 : 4 * (M * (c * v ^ 30)) ≤ v ^ 32 := by
    calc 4 * (M * (c * v ^ 30)) = 4 * M * c * v ^ 30 := by ring
      _ ≤ v ^ 2 * v ^ 30 := by gcongr
      _ = v ^ 32 := by ring
  have e : (v ^ 32 - v ^ 16) / M - c * v ^ 30 - v ^ 32 / (2 * M) =
      (v ^ 32 - 2 * v ^ 16 - 2 * (M * (c * v ^ 30))) / (2 * M) := by
    field_simp
    ring
  have : 0 ≤ (v ^ 32 - 2 * v ^ 16 - 2 * (M * (c * v ^ 30))) / (2 * M) :=
    div_nonneg (by linarith) (by linarith)
  linarith

/-- The arithmetic of the off-diagonal terms: `c log(Z²M + 2) v³⁰ (7Z)² K ≤ v³¹/(64M)` when `1 ≤ Z ≤ P`, `K ≤ 2W`,
`12544c ≤ W` and `2M²P⁴W² ≤ v`. -/
lemma offdiag_arith {v M c W P Z K : ℝ} (hv : 2 * M ^ 2 * P ^ 4 * W ^ 2 ≤ v) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (hW : 12544 * c ≤ W) (hZ1 : 1 ≤ Z) (hZ : Z ≤ P) (hK0 : 0 ≤ K) (hK : K ≤ 2 * W) :
    c * Real.log (Z * Z * M + 2) * v ^ 30 * (7 * Z) ^ 2 * K ≤ v ^ 31 / (64 * M) := by
  have hv0 : 0 ≤ v := le_trans (by positivity) hv
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  have hlog : Real.log (Z * Z * M + 2) ≤ 2 * M * Z ^ 2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Z * Z * M + 2)
    have h1 : (1 : ℝ) ≤ M * Z ^ 2 := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hZ1)
    linarith
  have hZ4 : Z ^ 4 ≤ P ^ 4 := pow_le_pow_left₀ (by linarith) hZ 4
  have hB : 3136 * c * M * Real.log (Z * Z * M + 2) * Z ^ 2 * K ≤ v := by
    calc 3136 * c * M * Real.log (Z * Z * M + 2) * Z ^ 2 * K ≤
          3136 * c * M * (2 * M * Z ^ 2) * Z ^ 2 * (2 * W) := by gcongr
      _ = 12544 * c * M ^ 2 * Z ^ 4 * W := by ring
      _ ≤ 12544 * c * M ^ 2 * P ^ 4 * W := by gcongr
      _ ≤ W * M ^ 2 * P ^ 4 * W := by gcongr
      _ ≤ 2 * M ^ 2 * P ^ 4 * W ^ 2 := by
          have : 0 ≤ M ^ 2 * P ^ 4 * W ^ 2 := by positivity
          nlinarith
      _ ≤ v := hv
  calc c * Real.log (Z * Z * M + 2) * v ^ 30 * (7 * Z) ^ 2 * K =
        (3136 * c * M * Real.log (Z * Z * M + 2) * Z ^ 2 * K) * v ^ 30 / (64 * M) := by
        field_simp
        ring
    _ ≤ v * v ^ 30 / (64 * M) := by gcongr
    _ = v ^ 31 / (64 * M) := by ring

/-- **CONDITIONAL. The family is large** (conditional on the half-plane, through the count `hcard` of
`PrimeCharSums.card_Ioc_modEq_ge`). If `100(log M + 100 log W) ≤ L` and `W ≥ 12544C₁ + 8C₂ + 4`, then `P ≠ ∅`, and
`|P|` is at least the total `E (7Z)² K` of the off-diagonal terms (`sum_sq_free_le`) for `Z ≤ W^48` and `K ≤ 2W`. With
`v = e^{L/32} ≥ 2M²W^194`, `|P| ≥ e^L/(2ML) ≥ v³¹/(64M)`. -/
lemma large_family {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcard : ∀ (M : ℕ) [NeZero M] (a : ℕ), a.Coprime M → ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ((x - y) / M.totient - C₂ * Real.log (M + 2) * x ^ (11 / 12 + 1 / 48 : ℝ)) / Real.log x ≤
        #{p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD M]})
    {M r : ℕ} [NeZero M] (hr : r.Coprime M) {W L : ℝ} (hW : 12544 * C₁ + 8 * C₂ + 4 ≤ W)
    (hL : 100 * (Real.log M + 100 * Real.log W) ≤ L) {Z K : ℕ} (hZ : (Z : ℝ) ≤ W ^ 48)
    (hK : (K : ℝ) ≤ 2 * W) :
    0 < #(family M r L) ∧
      C₁ * Real.log (Z * Z * M + 2) * Real.exp L ^ (11 / 12 + 1 / 48 : ℝ) * (7 * Z) ^ 2 * K ≤
        #(family M r L) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hlW : Real.log 2 ≤ Real.log W := Real.log_le_log (by norm_num) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hL0 : 0 < L := by nlinarith
  obtain ⟨v, hv⟩ : ∃ v, v = Real.exp (L / 32) := ⟨_, rfl⟩
  have hv0 : 0 < v := hv ▸ Real.exp_pos _
  -- `v = e^{L/32} ≥ 2M²P⁴W²`, with `P = W^48`
  obtain ⟨P, hP⟩ : ∃ P, P = W ^ 48 := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := hP ▸ one_le_pow₀ (by linarith)
  have hlP : Real.log P = 48 * Real.log W := by
    rw [hP, Real.log_pow]
    push_cast
    ring
  have hW0 : 0 < W := by linarith
  have hP0 : 0 < P := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hvMW : 2 * (M : ℝ) ^ 2 * P ^ 4 * W ^ 2 ≤ v := by
    rw [hv, ← Real.exp_log (mul_pos (mul_pos (mul_pos two_pos (pow_pos hM0 2)) (pow_pos hP0 4)) (pow_pos hW0 2)),
      Real.log_mul (mul_pos (mul_pos two_pos (pow_pos hM0 2)) (pow_pos hP0 4)).ne' (pow_pos hW0 2).ne',
      Real.log_mul (mul_pos two_pos (pow_pos hM0 2)).ne' (pow_pos hP0 4).ne',
      Real.log_mul two_ne_zero (pow_pos hM0 2).ne', Real.log_pow, Real.log_pow, Real.log_pow, hlP]
    push_cast
    exact Real.exp_le_exp.2 (by linarith)
  have hexpL : Real.exp L = v ^ 32 := by
    rw [hv, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexpL2 : Real.exp (L / 2) = v ^ 16 := by
    rw [hv, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexpα : Real.exp L ^ (11 / 12 + 1 / 48 : ℝ) = v ^ 30 := by
    rw [← Real.exp_mul, hv, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hL32 : L ≤ 32 * v := by
    have := Real.add_one_le_exp (L / 32)
    rw [hv]
    linarith
  have hvW : (M : ℝ) * W ≤ v := by
    have h1 : (M : ℝ) ≤ M ^ 2 := by nlinarith
    have h2 : W ≤ 2 * P ^ 4 * W ^ 2 := by
      have : 1 ≤ P ^ 4 := one_le_pow₀ hP1
      nlinarith
    calc (M : ℝ) * W ≤ M ^ 2 * (2 * P ^ 4 * W ^ 2) := mul_le_mul h1 h2 hW0.le (by positivity)
      _ = 2 * (M : ℝ) ^ 2 * P ^ 4 * W ^ 2 := by ring
      _ ≤ v := hvMW
  -- the count: `|P| ≥ e^L/(2ML) ≥ v³¹/(64M)`
  have hP0 := hcard M r hr (Real.exp (L / 2)) (Real.exp L) (Real.one_le_exp (by linarith))
    (Real.exp_le_exp.2 (by linarith))
  rw [Real.log_exp] at hP0
  have key1 : v ^ 32 / (2 * M) ≤ (Real.exp L - Real.exp (L / 2)) / M.totient -
      C₂ * Real.log (M + 2) * Real.exp L ^ (11 / 12 + 1 / 48 : ℝ) := by
    rw [hexpα, hexpL, hexpL2]
    have hlog : Real.log (M + 2) ≤ 2 * M := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < M + 2)
      linarith
    refine count_arith (by nlinarith) hM1 (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos M))
      (by exact_mod_cast Nat.totient_le M) ?_
    calc 4 * M * (C₂ * Real.log (M + 2)) ≤ 4 * M * (C₂ * (2 * M)) := by gcongr
      _ = 8 * C₂ * M ^ 2 := by ring
      _ ≤ W ^ 2 * M ^ 2 := by
          gcongr
          nlinarith
      _ = (M * W) ^ 2 := by ring
      _ ≤ v ^ 2 := pow_le_pow_left₀ (by positivity) hvW 2
  have hcount : v ^ 31 / (64 * M) ≤ #(family M r L) := by
    refine le_trans ?_ ((div_le_div_of_nonneg_right key1 hL0.le).trans hP0)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc v ^ 31 * (2 * M * L) ≤ v ^ 31 * (2 * M * (32 * v)) :=
          mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
      _ = v ^ 32 * (64 * M) := by ring
  refine ⟨by exact_mod_cast (show (0 : ℝ) < #(family M r L) from
    (div_pos (pow_pos hv0 31) (by positivity) : (0 : ℝ) < v ^ 31 / (64 * M)).trans_le hcount),
    le_trans ?_ hcount⟩
  rw [hexpα]
  rcases Nat.eq_zero_or_pos Z with hZ0 | hZ0
  · subst hZ0
    rw [show (7 * ((0 : ℕ) : ℝ)) ^ 2 = 0 by norm_num, mul_zero, zero_mul]
    positivity
  exact offdiag_arith hvMW hM1 hC₁ (by linarith) (by exact_mod_cast hZ0) (hP ▸ hZ) (Nat.cast_nonneg _) hK

/-! ### Sobolev and Markov -/

/-- `min(1, x) ≤ √x` for `x ≥ 0`. -/
lemma min_one_le_sqrt {x : ℝ} (hx : 0 ≤ x) : min 1 x ≤ √x := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    exact (Real.le_sqrt hx hx).2 (by nlinarith)
  · rw [min_eq_left h]
    exact Real.one_le_sqrt.2 h

/-- The coefficients of `T_d(y)`: `|Λ(n) b(n) min(1, y/n)|` is at most `√y Λ(n)/√n` and at most `Λ(n)`. -/
lemma abs_coef_le {b : ℕ → ℝ} (hb : ∀ n, |b n| ≤ 1) {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    |Λ n * b n * min 1 (y / n)| ≤ √y * (Λ n / √n) ∧ |Λ n * b n * min 1 (y / n)| ≤ Λ n := by
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hm0 : 0 ≤ min 1 (y / n) := le_min zero_le_one (by positivity)
  rw [abs_mul, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hm0]
  have hbn := hb n
  constructor
  · calc Λ n * |b n| * min 1 (y / n) ≤ Λ n * 1 * √(y / n) := by
          gcongr
          exact min_one_le_sqrt (by positivity)
      _ = √y * (Λ n / √n) := by
          rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
          ring
  · calc Λ n * |b n| * min 1 (y / n) ≤ Λ n * 1 * 1 := by gcongr; exact min_le_left _ _
      _ = Λ n := by ring

/-- The coefficients of `T_d(k + 1) − T_d(k)`: `|Λ(n) b(n)(min(1, (k+1)/n) − min(1, k/n))|` is at most
`Λ(n)/√(kn)` and at most `Λ(n)`, as the difference is `0` for `n ≤ k` and `1/n` for `n > k`. -/
lemma abs_coef_sub_le {b : ℕ → ℝ} (hb : ∀ n, |b n| ≤ 1) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    |Λ n * b n * (min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n))| ≤ 1 / √k * (Λ n / √n) ∧
      |Λ n * b n * (min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n))| ≤ Λ n := by
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ : |min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n)| ≤ 1 / √k * (1 / √n) ∧
      |min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n)| ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rcases le_or_gt n k with h | h
    · have h' : (n : ℝ) ≤ k := by exact_mod_cast h
      have h'' : (n : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      rw [min_eq_left ((one_le_div (by linarith)).2 h'), min_eq_left ((one_le_div (by linarith)).2 h''), sub_self,
        abs_zero]
      constructor <;> positivity
    · have hn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
      have hk' : (k : ℝ) ≤ n := by linarith
      have hk'' : ((k + 1 : ℕ) : ℝ) ≤ n := by push_cast; linarith
      rw [min_eq_right ((div_le_one (by linarith)).2 hk'), min_eq_right ((div_le_one (by linarith)).2 hk'')]
      push_cast
      rw [show ((k : ℝ) + 1) / n - k / n = 1 / n by ring, abs_of_pos (by positivity)]
      constructor
      · rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
        have h1 : √(k : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h2 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (n : ℝ)]
      · rw [div_le_one (by linarith)]
        exact hn1
  rw [abs_mul, abs_mul, abs_of_nonneg hΛ]
  have hbn := hb n
  constructor
  · calc Λ n * |b n| * |min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n)| ≤ Λ n * 1 * (1 / √k * (1 / √n)) := by
          gcongr
          exact hδ.1
      _ = 1 / √k * (Λ n / √n) := by ring
  · calc Λ n * |b n| * |min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n)| ≤ Λ n * 1 * 1 := by
          gcongr
          exact hδ.2
      _ = Λ n := by ring

/-- **The bound of `MeanSquareSup.card_bad_le`** for `M₀(k) = kD` and `M₁(k) = D/k`: at most
`D K₀^{−ε}(2 + 4S)`, `S = Σ_k k^{−(1+ε)}`. Each `√(M₁(k))(√(M₀(k)) + √(M₀(k + 1)))` is at most `3D`;
`Σ_k k(w(k) − w(k + 1))` telescopes to at most `K₀w(K₀) + Σ_k w(k)`; `K₀w(K₀) = K₀^{−2ε}`; and
`w(k) ≤ K₀^{−ε}k^{−(1+ε)}`. -/
lemma bound_le {ε D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) {K₀ K₁ : ℕ} (hK₀ : 1 ≤ K₀) (hK : K₀ ≤ K₁) :
    (K₀ : ℝ) * D * MeanSquareSup.w ε K₀ + ∑ k ∈ Ico K₀ K₁,
      (√(D / k) * (√(k * D) + √(((k + 1 : ℕ) : ℝ) * D)) * MeanSquareSup.w ε k +
        k * D * (MeanSquareSup.w ε k - MeanSquareSup.w ε (k + 1))) ≤
    D * (K₀ : ℝ) ^ (-ε) * (2 + 4 * ∑' k : ℕ, ((k : ℝ) ^ (1 + ε))⁻¹) := by
  set w := MeanSquareSup.w ε with hw
  set S := ∑' k : ℕ, ((k : ℝ) ^ (1 + ε))⁻¹ with hS
  have hK0 : (0 : ℝ) < K₀ := by exact_mod_cast hK₀
  have hw0 : ∀ k : ℕ, 0 ≤ w k := fun k => Real.rpow_nonneg k.cast_nonneg _
  have hwa : ∀ k : ℕ, K₀ ≤ k → w (k + 1) ≤ w k := fun k hk =>
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hK₀.trans hk) (by push_cast; linarith) (by linarith)
  -- `k w(k) = k^{−2ε} ≤ k^{−ε}`, and `w(k) ≤ K₀^{−ε} k^{−(1+ε)}`
  have hkw : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * w k ≤ (k : ℝ) ^ (-ε) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    calc (k : ℝ) * w k = (k : ℝ) ^ (-(2 * ε)) := by
          rw [hw, MeanSquareSup.w, show -(2 * ε) = 1 + -(1 + 2 * ε) by ring, Real.rpow_add (by linarith),
            Real.rpow_one]
      _ ≤ (k : ℝ) ^ (-ε) := Real.rpow_le_rpow_of_exponent_le hk' (by linarith)
  have hwS : ∀ k ∈ Ico K₀ K₁, w k ≤ (K₀ : ℝ) ^ (-ε) * ((k : ℝ) ^ (1 + ε))⁻¹ := by
    intro k hk
    have hk' : (K₀ : ℝ) ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    rw [hw, MeanSquareSup.w, show -(1 + 2 * ε) = -ε + -(1 + ε) by ring, Real.rpow_add (by linarith),
      Real.rpow_neg (k.cast_nonneg) (1 + ε)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hK0 hk' (by linarith)) (by positivity)
  have hsum : ∑ k ∈ Ico K₀ K₁, w k ≤ (K₀ : ℝ) ^ (-ε) * S := by
    refine (sum_le_sum hwS).trans ?_
    rw [← mul_sum]
    gcongr
    exact Summable.sum_le_tsum _ (fun k _ => by positivity) (Real.summable_nat_rpow_inv.2 (by linarith))
  -- the first part of each term is at most `3D w(k)`
  have hfirst : ∀ k ∈ Ico K₀ K₁, √(D / k) * (√(k * D) + √(((k + 1 : ℕ) : ℝ) * D)) ≤ 3 * D := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hK₀.trans (mem_Ico.1 hk).1
    have h1 : √(D / k) * √(k * D) = D := by
      rw [← Real.sqrt_mul (div_nonneg hD (by linarith)), show D / k * (k * D) = D * D by field_simp,
        Real.sqrt_mul_self hD]
    have h2 : √(D / k) * √(((k + 1 : ℕ) : ℝ) * D) ≤ 2 * D := by
      rw [← Real.sqrt_mul (div_nonneg hD (by linarith))]
      calc √(D / k * (((k + 1 : ℕ) : ℝ) * D)) ≤ √((2 * D) * (2 * D)) := by
            refine Real.sqrt_le_sqrt ?_
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
            push_cast
            nlinarith [mul_nonneg (mul_nonneg hD hD) (by linarith : (0 : ℝ) ≤ 3 * k - 1)]
        _ = 2 * D := Real.sqrt_mul_self (by linarith)
    rw [mul_add]
    linarith
  -- the telescoping part
  have htel : ∑ k ∈ Ico K₀ K₁, (k : ℝ) * D * (w k - w (k + 1)) ≤
      D * (K₀ * w K₀) + D * ∑ k ∈ Ico K₀ K₁, w k := by
    have e : ∑ k ∈ Ico K₀ K₁, (k : ℝ) * D * (w k - w (k + 1)) =
        D * (K₀ * w K₀ - K₁ * w K₁) + D * ∑ k ∈ Ico K₀ K₁, w (k + 1) := by
      have := sum_Ico_sub (fun k : ℕ => (k : ℝ) * w k) hK
      rw [mul_sum, ← neg_sub, ← this, ← sum_neg_distrib, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [e]
    have h1 : 0 ≤ (K₁ : ℝ) * w K₁ := mul_nonneg (Nat.cast_nonneg _) (hw0 _)
    have h2 : ∑ k ∈ Ico K₀ K₁, w (k + 1) ≤ ∑ k ∈ Ico K₀ K₁, w k :=
      sum_le_sum fun k hk => hwa k (mem_Ico.1 hk).1
    nlinarith
  have hK0w : (K₀ : ℝ) * w K₀ ≤ (K₀ : ℝ) ^ (-ε) := hkw K₀ hK₀
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  calc (K₀ : ℝ) * D * w K₀ + ∑ k ∈ Ico K₀ K₁, (√(D / k) * (√(k * D) + √(((k + 1 : ℕ) : ℝ) * D)) * w k +
        k * D * (w k - w (k + 1)))
      ≤ D * (K₀ * w K₀) + (∑ k ∈ Ico K₀ K₁, 3 * D * w k + (D * (K₀ * w K₀) + D * ∑ k ∈ Ico K₀ K₁, w k)) := by
        rw [sum_add_distrib]
        gcongr ?_ + (?_ + ?_)
        · exact le_of_eq (by ring)
        · exact sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hfirst k hk) (hw0 k)
    _ = 2 * D * (K₀ * w K₀) + 4 * D * ∑ k ∈ Ico K₀ K₁, w k := by
        rw [← mul_sum]
        ring
    _ ≤ 2 * D * (K₀ : ℝ) ^ (-ε) + 4 * D * ((K₀ : ℝ) ^ (-ε) * S) := by gcongr
    _ = D * (K₀ : ℝ) ^ (-ε) * (2 + 4 * S) := by ring

/-- **CONDITIONAL. At most a quarter of the family is bad** (conditional on the half-plane, through
`sum_sq_free_le`). If the off-diagonal terms `E (7Z)²`, times `K₁`, are at most `|P|`, and
`D K₀^{−ε}(2 + 4S) ≤ 1/64` with `D = 4 log²Z (1 + log Z) + 1`, then at most `|P|/4` members `d` have
`T_d(k)² > k^{1+2ε}/16` for some `k ∈ [K₀, K₁]`: `MeanSquareSup.card_bad_le` with `M₀(k) = kD` and `M₁(k) = D/k`
(`abs_coef_le`, `abs_coef_sub_le`), and `bound_le`. -/
lemma card_bad_quarter {ε C : ℝ} (hε : 0 < ε)
    (hC : ∀ (N M : ℕ) [NeZero N] [NeZero M], N.Coprime M → ∀ a : ℕ, a.Coprime M →
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → ∀ y x : ℝ, 0 ≤ y → y ≤ x →
        ‖∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD M], χ p‖ ≤
          C * Real.log (N * M + 2) * x ^ (11 / 12 + 1 / 48 : ℝ))
    (hC0 : 0 ≤ C) {M r : ℕ} [NeZero M] (hM : 4 ∣ M) (hr : r.Coprime M) {L : ℝ} (hL : 0 ≤ L)
    {Z K₀ K₁ : ℕ} (hK₀ : 1 ≤ K₀) (hK : K₀ ≤ K₁)
    (hoff : C * Real.log (Z * Z * M + 2) * Real.exp L ^ (11 / 12 + 1 / 48 : ℝ) * (7 * Z) ^ 2 * K₁ ≤
      #(family M r L))
    (hB : (4 * Real.log Z ^ 2 * (1 + Real.log Z) + 1) * (K₀ : ℝ) ^ (-ε) *
      (2 + 4 * ∑' k : ℕ, ((k : ℝ) ^ (1 + ε))⁻¹) ≤ 1 / 64)
    {b : ℕ → ℝ} (hb : ∀ n, |b n| ≤ 1) :
    4 * #{d ∈ family M r L | ∃ k ∈ Icc K₀ K₁,
      1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M Z b d k : ℝ) : ℂ)‖ ^ 2} ≤ #(family M r L) := by
  set D := 4 * Real.log Z ^ 2 * (1 + Real.log Z) + 1 with hD
  set E := C * Real.log (Z * Z * M + 2) * Real.exp L ^ (11 / 12 + 1 / 48 : ℝ) * (7 * Z) ^ 2 with hE
  have hlZ : 0 ≤ Real.log Z := Real.log_natCast_nonneg Z
  have hD0 : 0 ≤ D := by positivity
  have hE0 : 0 ≤ E := by
    have : (0 : ℝ) ≤ Z * Z * M := by positivity
    have : 0 ≤ Real.log (Z * Z * M + 2) := Real.log_nonneg (by linarith)
    positivity
  have hK₁ : (1 : ℝ) ≤ K₁ := by exact_mod_cast hK₀.trans hK
  have hEP : E ≤ #(family M r L) := le_trans (le_mul_of_one_le_right hE0 hK₁) hoff
  -- the mean squares
  have h0 : ∀ k ∈ Icc K₀ K₁, ∑ d ∈ family M r L, ‖((free M Z b d k : ℝ) : ℂ)‖ ^ 2 ≤
      #(family M r L) * (k * D) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hK₀.trans (mem_Icc.1 hk).1
    have h := sum_sq_free_le hC hC0 hM hr hL Z (fun n => Λ n * b n * min 1 ((k : ℝ) / n))
      (Real.sqrt_nonneg k) (fun n => (abs_coef_le hb (Nat.cast_nonneg k) n).1)
      (fun n => (abs_coef_le hb (Nat.cast_nonneg k) n).2)
    rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc ∑ d ∈ family M r L, free M Z b d k ^ 2 ≤
          #(family M r L) * (k * (4 * Real.log Z ^ 2 * (1 + Real.log Z))) + E := h
      _ ≤ #(family M r L) * (k * (4 * Real.log Z ^ 2 * (1 + Real.log Z))) + #(family M r L) * k := by
          gcongr
          exact hEP.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hk1)
      _ = #(family M r L) * (k * D) := by
          rw [hD]
          ring
  have h1 : ∀ k ∈ Ico K₀ K₁, ∑ d ∈ family M r L,
      ‖((free M Z b d (k + 1 : ℕ) : ℝ) : ℂ) - ((free M Z b d k : ℝ) : ℂ)‖ ^ 2 ≤ #(family M r L) * (D / k) := by
    intro k hk
    have hk1 : 1 ≤ k := hK₀.trans (mem_Ico.1 hk).1
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkK : (k : ℝ) ≤ K₁ := by exact_mod_cast (mem_Ico.1 hk).2.le
    have h := sum_sq_free_le hC hC0 hM hr hL Z
      (fun n => Λ n * b n * (min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n))) (by positivity)
      (fun n => (abs_coef_sub_le hb hk1 n).1) (fun n => (abs_coef_sub_le hb hk1 n).2)
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg k), one_pow] at h
    have e : ∀ d, free M Z b d (k + 1 : ℕ) - free M Z b d k = ∑ n ∈ Icc 1 Z with n.Coprime M,
        Λ n * b n * (min 1 (((k + 1 : ℕ) : ℝ) / n) - min 1 ((k : ℝ) / n)) * jacobiSym n d := by
      intro d
      rw [free, free, ← sum_sub_distrib]
      exact sum_congr rfl fun n _ => by ring
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, e]
    calc _ ≤ #(family M r L) * (1 / k * (4 * Real.log Z ^ 2 * (1 + Real.log Z))) + E := h
      _ ≤ #(family M r L) * (1 / k * (4 * Real.log Z ^ 2 * (1 + Real.log Z))) + #(family M r L) * (1 / k) := by
          gcongr
          calc E = E * K₁ / K₁ := by field_simp
            _ ≤ #(family M r L) / K₁ := by gcongr
            _ ≤ #(family M r L) / k := by gcongr
            _ = #(family M r L) * (1 / k) := by ring
      _ = #(family M r L) * (D / k) := by
          rw [hD]
          ring
  -- Sobolev and Markov
  have hbad := MeanSquareSup.card_bad_le (family M r L) (fun d k => ((free M Z b d k : ℝ) : ℂ)) hK₀ hK hε.le
    (fun k => (k : ℝ) * D) (fun k => D / k) h0 h1 (c := 1 / 16)
  have hBd := bound_le hε hD0 hK₀ hK
  have hP0 : (0 : ℝ) ≤ #(family M r L) := Nat.cast_nonneg _
  have : (1 / 16 : ℝ) * #{d ∈ family M r L | ∃ k ∈ Icc K₀ K₁,
      1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M Z b d k : ℝ) : ℂ)‖ ^ 2} ≤ #(family M r L) * (1 / 64) :=
    hbad.trans (mul_le_mul_of_nonneg_left (hBd.trans hB) hP0)
  have h4 : (4 * #{d ∈ family M r L | ∃ k ∈ Icc K₀ K₁,
      1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M Z b d k : ℝ) : ℂ)‖ ^ 2} : ℝ) ≤ #(family M r L) := by
    linarith
  exact_mod_cast h4

/-! ### From integers to all `y` -/

/-- `T_d` is affine between consecutive integers, as `min(1, y/n)` is for every `n ≥ 1`. -/
lemma free_eq (M Z : ℕ) (b : ℕ → ℝ) (d k : ℕ) {y : ℝ} (hk : (k : ℝ) ≤ y) (hy : y ≤ k + 1) :
    free M Z b d y = (k + 1 - y) * free M Z b d k + (y - k) * free M Z b d (k + 1 : ℕ) := by
  unfold free
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 (mem_filter.1 hn).1).1
  have key : min 1 (y / n) =
      (k + 1 - y) * min 1 ((k : ℝ) / n) + (y - k) * min 1 (((k + 1 : ℕ) : ℝ) / n) := by
    push_cast
    rcases le_or_gt (n : ℝ) k with h | h
    · rw [min_eq_left ((one_le_div (by linarith)).2 (by linarith)), min_eq_left ((one_le_div (by linarith)).2 h),
        min_eq_left ((one_le_div (by linarith)).2 (by linarith))]
      ring
    · have h' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.cast_lt.1 h
      rw [min_eq_right ((div_le_one (by linarith)).2 (by linarith)),
        min_eq_right ((div_le_one (by linarith)).2 h.le), min_eq_right ((div_le_one (by linarith)).2 h')]
      field_simp
      ring
  rw [key]
  ring

/-- **A good member is good on the whole window.** If `T_d(k)² ≤ k^{1+2ε}/16` for every integer
`k ∈ [⌊Y⌋, ⌊Y^A⌋ + 1]`, then `|T_d(y)| ≤ y^{1/2+ε}/2` for `y ∈ [Y, Y^A]`: `T_d(y)` lies between `T_d(k)` and
`T_d(k + 1)` (`free_eq`) for `k = ⌊y⌋`, and `(k + 1)^{1/2+ε}/4 ≤ (2y)^{1/2+ε}/4 ≤ y^{1/2+ε}/2`. -/
lemma abs_free_le {ε Y A : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hY : 1 ≤ Y) {M Z : ℕ} {b : ℕ → ℝ} {d : ℕ}
    (hgood : ∀ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1), free M Z b d k ^ 2 ≤ 1 / 16 * (k : ℝ) ^ (1 + 2 * ε))
    {y : ℝ} (hy : y ∈ Set.Icc Y (Y ^ A)) : |free M Z b d y| ≤ y ^ (1 / 2 + ε) / 2 := by
  obtain ⟨hYy, hyA⟩ := hy
  have hy0 : 0 ≤ y := by linarith
  have hk : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hk1 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hfl := Nat.floor_le_floor (R := ℝ) hYy
  have hfl' := Nat.floor_le_floor (R := ℝ) hyA
  -- the bound at `j ∈ {k, k + 1}`
  have hj : ∀ j ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1), (j : ℝ) ≤ 2 * y → |free M Z b d j| ≤ y ^ (1 / 2 + ε) / 2 := by
    intro j hjm hj2
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hsq : ((j : ℝ) ^ (1 / 2 + ε) / 4) ^ 2 = 1 / 16 * (j : ℝ) ^ (1 + 2 * ε) := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hj0]
      push_cast
      ring_nf
    have h1 : |free M Z b d j| ≤ (j : ℝ) ^ (1 / 2 + ε) / 4 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by rw [sq_abs, hsq]; exact hgood j hjm)
    have h2 : (j : ℝ) ^ (1 / 2 + ε) ≤ 2 * y ^ (1 / 2 + ε) := by
      calc (j : ℝ) ^ (1 / 2 + ε) ≤ (2 * y) ^ (1 / 2 + ε) := Real.rpow_le_rpow hj0 hj2 (by linarith)
        _ = 2 ^ (1 / 2 + ε) * y ^ (1 / 2 + ε) := Real.mul_rpow (by norm_num) hy0
        _ ≤ 2 ^ (1 : ℝ) * y ^ (1 / 2 + ε) := by
            gcongr
            exacts [by norm_num, by linarith]
        _ = 2 * y ^ (1 / 2 + ε) := by rw [Real.rpow_one]
    linarith
  have hA : |free M Z b d ⌊y⌋₊| ≤ y ^ (1 / 2 + ε) / 2 :=
    hj _ (mem_Icc.2 ⟨hfl, by omega⟩) (by linarith)
  have hB : |free M Z b d (⌊y⌋₊ + 1 : ℕ)| ≤ y ^ (1 / 2 + ε) / 2 :=
    hj _ (mem_Icc.2 ⟨by omega, by omega⟩) (by push_cast; linarith)
  rw [free_eq M Z b d ⌊y⌋₊ hk hk1.le]
  calc |(⌊y⌋₊ + 1 - y) * free M Z b d ⌊y⌋₊ + (y - ⌊y⌋₊) * free M Z b d (⌊y⌋₊ + 1 : ℕ)|
      ≤ (⌊y⌋₊ + 1 - y) * |free M Z b d ⌊y⌋₊| + (y - ⌊y⌋₊) * |free M Z b d (⌊y⌋₊ + 1 : ℕ)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ⌊y⌋₊ + 1 - y by linarith),
          abs_of_nonneg (show (0 : ℝ) ≤ y - ⌊y⌋₊ by linarith)]
    _ ≤ (⌊y⌋₊ + 1 - y) * (y ^ (1 / 2 + ε) / 2) + (y - ⌊y⌋₊) * (y ^ (1 / 2 + ε) / 2) := by gcongr
    _ = y ^ (1 / 2 + ε) / 2 := by ring

/-! ### The family -/

/-- **CONDITIONAL. Most of the family is good, uniformly** (conditional on the half-plane, through `large_family` and
`card_bad_quarter`). Let `0 < ε ≤ 1/2` and `A ≥ 1`. For all large `Y`, every `M > 0` with `4 ∣ M`, `r` prime to `M`,
`L` with `100(log M + 100A log Y) ≤ L` and weights `b₁`, `b₂` with `|bᵢ| ≤ 1`, some `d ∈ P` has
`|T_d(y)| ≤ y^{1/2+ε}/2` on `[Y, Y^A]` for both weights, with the cutoff `Z = ⌊Y^{48A}⌋`. Each weight is bad on at most
a quarter of `P`, and `P ≠ ∅`. The threshold for `Y` depends on `ε` and `A` only. -/
theorem exists_good {ε A : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hA : 1 ≤ A) :
    ∀ᶠ Y in Filter.atTop, ∀ (M r : ℕ) (L : ℝ) (b₁ b₂ : ℕ → ℝ), 0 < M → 4 ∣ M → r.Coprime M →
      (∀ n, |b₁ n| ≤ 1) → (∀ n, |b₂ n| ≤ 1) → 100 * (Real.log M + 100 * A * Real.log Y) ≤ L →
      ∃ d ∈ family M r L, ∀ y ∈ Set.Icc Y (Y ^ A),
        |free M ⌊Y ^ (48 * A)⌋₊ b₁ d y| ≤ y ^ (1 / 2 + ε) / 2 ∧
          |free M ⌊Y ^ (48 * A)⌋₊ b₂ d y| ≤ y ^ (1 / 2 + ε) / 2 := by
  obtain ⟨C₁, hC₁, hsum⟩ := PrimeCharSums.norm_sum_Ioc_modEq_le (η := 1 / 48) (by norm_num)
  obtain ⟨C₂, hC₂, hcard⟩ := PrimeCharSums.card_Ioc_modEq_ge (η := 1 / 48) (by norm_num)
  obtain ⟨S, hS⟩ : ∃ S, S = ∑' k : ℕ, ((k : ℝ) ^ (1 + ε))⁻¹ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ tsum_nonneg fun k => by positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 4 * (48 * A) ^ 2 * (49 * A) + 1 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκ]
    positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop 3 hε).bound (c := 1 / (128 * κ * (2 + 4 * S))) (by positivity)
  filter_upwards [hlo, Filter.eventually_ge_atTop (12544 * C₁ + 8 * C₂ + 4)] with Y hYlo hY
  intro M r L b₁ b₂ hM0 hM4 hr hb₁ hb₂ hL
  have : NeZero M := ⟨hM0.ne'⟩
  have hY4 : 4 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hℓ : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlM : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  have hL0 : 0 ≤ L := by nlinarith
  -- the window `[Y, W]`, `W = Y^A`, and the cutoff `Z ≤ W^48`
  have hW : Y ≤ Y ^ A := by simpa using Real.rpow_le_rpow_of_exponent_le hY1 hA
  have hW0 : 0 ≤ Y ^ A := by positivity
  have hZW : (⌊Y ^ (48 * A)⌋₊ : ℝ) ≤ (Y ^ A) ^ 48 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm]
    exact Nat.floor_le (by positivity)
  have hK₀ : 1 ≤ ⌊Y⌋₊ := (Nat.one_le_floor_iff Y).2 hY1
  have hK : ⌊Y⌋₊ ≤ ⌊Y ^ A⌋₊ + 1 := (Nat.floor_le_floor hW).trans (Nat.le_succ _)
  have hK₁ : ((⌊Y ^ A⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Y ^ A := by
    push_cast
    linarith [Nat.floor_le hW0]
  have hL' : 100 * (Real.log M + 100 * Real.log (Y ^ A)) ≤ L := by
    rw [Real.log_rpow (by linarith)]
    linarith
  obtain ⟨hP0, hoff⟩ := large_family hC₁ hC₂ hcard hr (W := Y ^ A) (by linarith) hL' hZW hK₁
  -- the bound of the Sobolev–Markov lemma is at most `1/64`
  have hB : (4 * Real.log ⌊Y ^ (48 * A)⌋₊ ^ 2 * (1 + Real.log ⌊Y ^ (48 * A)⌋₊) + 1) * (⌊Y⌋₊ : ℝ) ^ (-ε) *
      (2 + 4 * ∑' k : ℕ, ((k : ℝ) ^ (1 + ε))⁻¹) ≤ 1 / 64 := by
    rw [← hS]
    set ℓ := Real.log Y
    have hZ1 : (1 : ℝ) ≤ ⌊Y ^ (48 * A)⌋₊ := by
      exact_mod_cast (Nat.one_le_floor_iff _).2 (Real.one_le_rpow hY1 (by positivity))
    have hlZ0 : 0 ≤ Real.log ⌊Y ^ (48 * A)⌋₊ := Real.log_natCast_nonneg _
    have hlZ : Real.log ⌊Y ^ (48 * A)⌋₊ ≤ 48 * A * ℓ := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (Nat.floor_le (by positivity))
    have hD : 4 * Real.log ⌊Y ^ (48 * A)⌋₊ ^ 2 * (1 + Real.log ⌊Y ^ (48 * A)⌋₊) + 1 ≤ κ * ℓ ^ 3 := by
      have h1 : 1 + Real.log ⌊Y ^ (48 * A)⌋₊ ≤ 49 * A * ℓ := by nlinarith
      have h2 : Real.log ⌊Y ^ (48 * A)⌋₊ ^ 2 ≤ (48 * A * ℓ) ^ 2 := pow_le_pow_left₀ hlZ0 hlZ 2
      have h3 : (1 : ℝ) ≤ ℓ ^ 3 := one_le_pow₀ hℓ
      calc 4 * Real.log ⌊Y ^ (48 * A)⌋₊ ^ 2 * (1 + Real.log ⌊Y ^ (48 * A)⌋₊) + 1 ≤
            4 * (48 * A * ℓ) ^ 2 * (49 * A * ℓ) + ℓ ^ 3 := by gcongr
        _ = κ * ℓ ^ 3 := by
            rw [hκ]
            ring
    have hK0 : (⌊Y⌋₊ : ℝ) ^ (-ε) ≤ 2 * Y ^ (-ε) := by
      have hY2 : Y / 2 ≤ ⌊Y⌋₊ := by linarith [Nat.lt_floor_add_one Y]
      calc (⌊Y⌋₊ : ℝ) ^ (-ε) ≤ (Y / 2) ^ (-ε) := Real.rpow_le_rpow_of_nonpos (by linarith) hY2 (by linarith)
        _ = 2 ^ ε * Y ^ (-ε) := by
            rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
        _ ≤ 2 ^ (1 : ℝ) * Y ^ (-ε) := by
            gcongr
            exacts [by norm_num, by linarith]
        _ = 2 * Y ^ (-ε) := by rw [Real.rpow_one]
    have hℓ3 : ℓ ^ 3 ≤ 1 / (128 * κ * (2 + 4 * S)) * Y ^ ε := by
      have h := hYlo
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (by positivity),
        show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] at h
      exact h
    have hYε : Y ^ ε * Y ^ (-ε) = 1 := by
      rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ (by positivity)]
    calc (4 * Real.log ⌊Y ^ (48 * A)⌋₊ ^ 2 * (1 + Real.log ⌊Y ^ (48 * A)⌋₊) + 1) * (⌊Y⌋₊ : ℝ) ^ (-ε) *
          (2 + 4 * S) ≤ κ * (1 / (128 * κ * (2 + 4 * S)) * Y ^ ε) * (2 * Y ^ (-ε)) * (2 + 4 * S) := by
          gcongr
          exact hD.trans (by gcongr)
      _ = 1 / 64 * (Y ^ ε * Y ^ (-ε)) := by
          field_simp
          ring
      _ = 1 / 64 := by rw [hYε, mul_one]
  -- each weight is bad on at most a quarter of the family; find a member good for both
  have hq₁ := card_bad_quarter hε hsum hC₁ hM4 hr hL0 hK₀ hK hoff hB hb₁
  have hq₂ := card_bad_quarter hε hsum hC₁ hM4 hr hL0 hK₀ hK hoff hB hb₂
  obtain ⟨d, hdP, hd₁, hd₂⟩ : ∃ d ∈ family M r L,
      (∀ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1),
        ¬ 1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M ⌊Y ^ (48 * A)⌋₊ b₁ d k : ℝ) : ℂ)‖ ^ 2) ∧
      (∀ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1),
        ¬ 1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M ⌊Y ^ (48 * A)⌋₊ b₂ d k : ℝ) : ℂ)‖ ^ 2) := by
    by_contra hne
    have hsub : family M r L ⊆
        {d ∈ family M r L | ∃ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1),
          1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M ⌊Y ^ (48 * A)⌋₊ b₁ d k : ℝ) : ℂ)‖ ^ 2} ∪
        {d ∈ family M r L | ∃ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1),
          1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M ⌊Y ^ (48 * A)⌋₊ b₂ d k : ℝ) : ℂ)‖ ^ 2} := by
      intro d hd
      rw [mem_union, mem_filter, mem_filter]
      by_contra h
      rw [not_or, not_and, not_and] at h
      exact hne ⟨d, hd, fun k hk hlt => h.1 hd ⟨k, hk, hlt⟩, fun k hk hlt => h.2 hd ⟨k, hk, hlt⟩⟩
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  have hgood : ∀ b : ℕ → ℝ, (∀ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1),
      ¬ 1 / 16 * (k : ℝ) ^ (1 + 2 * ε) < ‖((free M ⌊Y ^ (48 * A)⌋₊ b d k : ℝ) : ℂ)‖ ^ 2) →
      ∀ k ∈ Icc ⌊Y⌋₊ (⌊Y ^ A⌋₊ + 1), free M ⌊Y ^ (48 * A)⌋₊ b d k ^ 2 ≤ 1 / 16 * (k : ℝ) ^ (1 + 2 * ε) := by
    intro b hb k hk
    have := not_lt.1 (hb k hk)
    rwa [Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  exact ⟨d, hdP, fun y hy => ⟨abs_free_le hε.le hε' hY1 (hgood b₁ hd₁) hy, abs_free_le hε.le hε' hY1 (hgood b₂ hd₂) hy⟩⟩

end TwistFamily

#print axioms TwistFamily.exists_good
