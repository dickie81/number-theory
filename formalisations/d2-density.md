# Fundamental discriminants: Granville–Soundararajan's Lemma 4.1, moments, and densities

**Lean:** `lib/pnt/D2GS.lean`:

```lean
theorem GSKron.gs_kron_pos {n : ℕ} (hn : 1 < n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then kron d n else 0)‖ ≤ GSB n x

theorem GSUncond.moment_pos_unconditional (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, a p * kron d p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * (dens CpPos CpPos0 (Nat.sqrt (∏ i, f i)) : ℂ)))

theorem GSNu.nu1_eq : nu1 = 4 / Real.pi ^ 2

theorem GSNu.delta_pos_closed (r : ℕ) (hr : 0 < r) :
    Tendsto (fun x : ℕ => (Nat.count (Q CpPos r) x : ℝ) / x) atTop (𝓝 (3 / Real.pi ^ 2 * gfac r))
```

and the same for negative discriminants (`GSKron.gs_kron_neg`, `GSUncond.moment_neg_unconditional`, `GSNu.delta_neg_closed`, with
`kron (-d) n` and `fundNeg`).

`fundPos d` (`fundNeg d`) says that `d` (`−d`) is a fundamental discriminant. `kron D n` is the Kronecker symbol
`(D/n)`: `χ₈(D)^{v₂(n)}` times the Jacobi symbol at the odd part of `n`. `GSB n x` is `3(2√(xB) + B)` with
`B = d(4n)√(4n)(1 + log 4n)` for odd `n`, and the same with `8m` for the odd part `m` of even `n`; so
`GSB n x ≪ x^{1/2} n^{1/4+ε}`. `Q CpPos r d` says that `d` is a positive fundamental discriminant coprime to `r`,
`gfac r = ∏_{p∣r} p/(p+1)`, `dens Cp _ r` is the density of `Q Cp r`, which exists, and `nu1` is the density of the
odd squarefree numbers.

In words: for non-square `n`, `Σ_{0<D≤x} χ_D(n) ≪ x^{1/2} n^{1/4+ε}` over fundamental discriminants of either sign;
the `k`-th moment of `Σ_{p∈P} a_p χ_D(p)` over such `D` has, as `x → ∞`, the limit given by the tuples whose product
is a square, each weighted by the density of the `D` coprime to it; and that density is `(3/π²)∏_{p∣r} p/(p+1)`.

## The characters `χ_D` are primitive

`lib/pnt/D2Prim.lean`:

```lean
theorem GSPrim.primitive_pos {d : ℕ} (hd : fundPos d) (h1 : 1 < d) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ ∀ n : ℕ, n ≠ 0 → χ n = kron d n

theorem GSPrim.primitive_neg {d : ℕ} (hd : fundNeg d) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ ∀ n : ℕ, n ≠ 0 → χ n = kron (-d) n
```

The character is the library's `QuadKronecker.jacBot |D|` for `D ≡ 1 (4)` (`GSPrim.kron_eq_jacobi_one`, by quadratic
reciprocity) and `QuadKronecker.jacTop (D/4)` for `4 ∣ D` (`GSPrim.kron_eq_jacTop`). Primitivity: for each prime
`p ∣ |D|` there is an `a ≡ 1 (|D|/p)`, coprime to `D`, with `(D|a) = −1` (`GSPrim.wit_odd`, `GSPrim.wit_two`), so
`χ` factors through no proper divisor (`GSPrim.isPrimitive_of_witness`). Unconditional.

## Quantitative `Hcount`

`lib/pnt/D2Hcount.lean`, unconditional:

```lean
theorem GSHcount.hcount_pos (r : ℕ) (hr : 0 < r) (x : ℕ) :
    |(Nat.count (Q CpPos r) x : ℝ) - 3 / Real.pi ^ 2 * gfac r * x| ≤ (16 * r + 3) * (Real.sqrt x + 1)
```

and `GSHcount.hcount_neg`, the same for `CpNeg`. Möbius over odd `e ≤ √x` (`GSHcount.sum_w`), a periodic count mod
`16r` for each `e` (`GSHcount.term_bound`), and the tail `Σ_{e>√x} 1/e²` (`GSHcount.tail_le`); the constant is
identified with the density through `GSNu.delta_pos_closed`.

## Method of moments (hypothesis B, milestone B1)

`lib/pnt/MomentConv.lean`, unconditional:

```lean
theorem MomentConv.tendsto_of_moments (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hi : ∀ n k, Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ))
    (hνi : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ))
    (hm : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, x ^ k ∂(ν : Measure ℝ))))
    {s : ℝ} (hs : 0 < s) (hνe : Integrable (fun x => Real.exp (s * |x|)) (ν : Measure ℝ)) :
    Tendsto μ atTop (𝓝 ν)
```

Ingredients: `MomentConv.ext_of_moments` (moments plus a finite exponential moment determine the law, via the
analytic `complexMGF`), `MomentConv.integrable_exp_of_moments`, `MomentConv.tight`, `MomentConv.even_moment_limit`
and `MomentConv.moment_tendsto` (moments along a weakly convergent sequence), then Prokhorov
(`isCompact_closure_of_isTightMeasureSet`) and a subsequence argument.

## The random model (hypothesis B, milestone B2)

`lib/pnt/RandModel.lean`, unconditional. On the product space `RandModel.P` of independent `X(n)`
(`RandModel.law`: at a prime `p`, `0` with probability `1/(p+1)`, `±1` each with probability `p/(2(p+1))`; `0` at
other `n`), Lamzouri's model `X = -Σ_p (log p) X(p)/(p - X(p))`:

```lean
theorem RandModel.ae_tendsto_X : ∀ᵐ ω ∂P, Tendsto (fun N => T N ω) atTop (𝓝 (X ω))
theorem RandModel.integrable_exp_X (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P
```

The centred partial sums form a martingale for the filtration of the first coordinates (`RandModel.martingale`), each
term is sub-Gaussian with proxy `β(n)² ≪ n^{-3/2}` by Hoeffding's lemma (`RandModel.subG`), so the sums are bounded in
`L¹` (`RandModel.eLpNorm_S_le`) and converge a.s. (Doob); the means are `≪ n^{-7/4}` (`RandModel.abs_m_le`). Fatou
gives the mgf. The law `RandModel.ν` has `RandModel.integrable_exp_abs_ν` and `RandModel.integrable_pow_ν`, the
hypotheses of `MomentConv.tendsto_of_moments` on the limit side.

## Main-term moments are the model's (hypothesis B, milestone B3)

`lib/pnt/ModelMoments.lean`, unconditional. With the completely multiplicative `ModelMoments.Xm`
(`X(n) = ∏_p X(p)^{v_p(n)}`), `ModelMoments.integral_Xm` gives `E[X(m)] = ∏_{p ∣ m} p/(p+1)` for square `m` and `0`
otherwise, and `ModelMoments.model_moment` expands `E[(Σ_{n ∈ P} a_n X(n))^k]`. The GS density is
`(3/π²) ∏_{p ∣ r} p/(p+1)` (`ModelMoments.dens_pos_eq`, `ModelMoments.dens_neg_eq`), hence:

```lean
theorem ModelMoments.moment_pos_model (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, (a p : ℂ) * kron d p) ^ k else 0)) atTop
      (𝓝 ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ))
```

and `ModelMoments.moment_neg_model` for `D = -d`.

## Model-side truncation (hypothesis B, toward B4)

`lib/pnt/ModelTrunc.lean`, unconditional:

```lean
theorem ModelTrunc.moment_A_tendsto (k : ℕ) :
    Tendsto (fun N => ∫ ω, A N ω ^ k ∂(RandModel.P)) atTop (𝓝 (∫ ω, (-X ω) ^ k ∂(RandModel.P)))
```

with `A N = Σ_{n ≤ N} Λ(n) X(n)/n`. Almost surely `|A_N + T_{N+1}| ≤ 2 log N (1 + log N)/√N`
(`ModelTrunc.abs_A_add_T_le`, from `ModelTrunc.vm_regroup` and `ModelTrunc.trunc_prime`); the moments pass to the limit
by `ModelTrunc.tendsto_integral_of_sq_bdd` (a.s. convergence with eventually bounded second moments).

## Quantitative moments, uniform in `P ⊆ [1, y]`

`lib/pnt/QuantMoments.lean`, unconditional:

```lean
theorem QuantMoments.moment_quant_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) {y : ℕ} (hPy : ∀ p ∈ P, p ≤ y)
    (a : ℕ → ℝ) (k x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, (a p : ℂ) * kron d p) ^ k else 0) -
        (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)‖ ≤
      (∑ p ∈ P, |a p|) ^ k * (2048 * (y : ℝ) ^ (3 * k) * (Real.sqrt x + 2))
```

and `QuantMoments.moment_quant_neg`. The error is `(Σ|a_n|)^k y^{3k} √x`, so `y = (log x)^A` is admissible.
`QuantMoments.GSB_le` bounds the GS Lemma 4.1 error polynomially in `n`.

## The random model has no atoms

`lib/pnt/NoAtoms.lean`, unconditional:

```lean
theorem NoAtoms.ν_singleton (t : ℝ) : (RandModel.ν : Measure ℝ) {t} = 0
```

Along `K` sparse primes (`NoAtoms.exists_J`), each gap `|g(p, −1)|` exceeds the spread `Σ_{q > p} β(q)` of the later
ones, so the partial sum over them lies in an interval of length `2δ` with probability at most `2^{−K}`
(`NoAtoms.ball_le`). The rest of `T_N` is independent of it (`NoAtoms.indep_FR`), and `T_N → X` in measure, so
`P(X = t) ≤ 2^{−K}` for every `K` (`NoAtoms.atom_zero`).

## CONDITIONAL: the distribution of `L′/L(1, χ_d)`

**CONDITIONAL on the half-plane `Re s > 11/12`**, through the tail identity below. `lib/pnt/D2Dist.lean`:

```lean
theorem D2Dist.moments_pos (k : ℕ) :
    Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if fundPos d ∧ 1 < d then lpos d ^ k else 0)) / x) atTop
      (𝓝 (κ * mν k))

theorem D2Dist.dist_pos : Tendsto (emp fundPos lpos) atTop (𝓝 RandModel.ν)
```

with `lpos d = Re L′/L(1, χ_d)`, `κ = 3/π²`, `mν k = E[X^k]`, and `emp fundPos lpos x` the empirical law of `lpos d`
over the fundamental discriminants `1 < d ≤ x`; likewise `D2Dist.moments_neg` and `D2Dist.dist_neg` for `-d`. The
proof (`D2Dist.core`, unconditional given its hypotheses) takes the cutoff `Y(x) = ⌈log(x + 2)⌉^48` in the
quantitative moments, the tail identity with `η = 1/48` (error `C log(d + 2) / ⌈log(x + 2)⌉²`), and the model
moments; `D2Dist.emp_tendsto` then applies `MomentConv.tendsto_of_moments`.

## The zero sum `K₁` at `s = 1` (towards `hK1`), given `GoodChar`

`lib/core/WeilChiK1.lean`, unconditional given the explicit hypothesis `GoodChar χ` (primitive, real, `χ ≠ 1`,
`L(½, χ) ≠ 0`):

```lean
theorem PsiOmega.hasSum_K1 (hG : GoodChar χ) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 / (1 / 4 + i.1))
      ((Real.log N : ℂ) - (Real.log π : ℂ) + Complex.digamma ((1 + parity χ) / 2)
        + 2 * logDeriv (LFunction χ) 1)
```

`PsiOmega.hasSum_K1` is Hadamard's product for `Ξ_χ` (`PsiOmega.hasSum_logDeriv_XiC`) at `t = −i/2`, with `PsiOmega.logDeriv_LamG_of_ne` for
`Λ*′/Λ*` at `s = 1`. Each `u = τ²` stands for the pair of zeros `ρ = ½ ± iτ`, so the sum is `K₁ = Σ_ρ 1/(ρ(1 − ρ))`.

## `K₁ > 0` (`hpos`), given `GoodChar`

`lib/core/WeilChiPos.lean`, unconditional given `GoodChar χ`. `PsiOmega.nonempty_zeros`: `Ξ_χ` has a zero (otherwise
Hadamard's product makes `Λ*` constant, and `Γ_ℝ(s + 2) = Γ_ℝ(s)s/(2π)` with `L(σ) → 1` gives a contradiction as
`σ → ∞`). `PsiOmega.K1C_pos`: `K₁ = Re Σ_u 2/(¼ + u) > 0` (`PsiOmega.K1C`), each term being `2/(ρ(1 − ρ))` with
`0 < Re ρ < 1` (`D2Density.re_inv_pos`).

## CONDITIONAL: `hdist` at every `t`, and the d₂ < d₁ density

**CONDITIONAL on the half-plane `Re s > 11/12`**, through `D2Dist.dist_pos` / `D2Dist.dist_neg`. `lib/pnt/D2Hdist.lean`:

```lean
theorem D2Hdist.hdist_pos (t : ℝ) : Tendsto (fun x => prop (Spos x) (fun D => t < ℓpos D)) atTop
    (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi t)).toReal)
```

and `D2Hdist.hdist_neg`. The frontier `{t}` of `Ioi t` is `ν`-null by `NoAtoms.ν_singleton`, so the portmanteau
theorem applies at every `t`. `D2Hdist.d2_density_pos` and `D2Hdist.d2_density_neg` are `D2Density.d2_density_log`
(`lib/pnt/D2Density.lean`, moved from `scratch/d2density/`) with `hdist` discharged; the hypotheses `hK1`, `hpos` and
`hB` remain, and are only required on the discriminant sets (`D2Hdist.Apos`: `1 < D` fundamental; `D2Hdist.Aneg`: `D < −1`
fundamental), through the set `A ⊇ S x` of `D2Density.d2_density_log`. `D2Density.K1_pos` gives the positivity of a summable zero sum `K₁`.

## The parity of `χ_D`, and `K₁`

`lib/pnt/D2Parity.lean`, unconditional. `D2Parity.kron_pos`: `(d | d − 1) = 1` for a positive fundamental
discriminant `d > 1`; `D2Parity.kron_neg`: `(−d | d − 1) = −1`. Both by quadratic reciprocity (for `d = 4m`, via
`J(m | 4m − 1) = 1`). With `D2Parity.chi_neg_one` this makes `χ_d` even and `χ_{−d}` odd.

`lib/pnt/D2Good.lean`. `D2Good.real_of` shows `χ_D` is a primitive real character `≠ 1` (`PsiOmega.RealChar`;
`χ_D` quadratic from `D2Good.kron_tri`), with no hypothesis on `L(½, χ_D)`. Then `D2Good.hK1_pos` /
`D2Good.hK1_neg` prove `hK1` and `hpos` for `K₁ = PsiOmega.K1Z χ_D` (`D2Good.K1pos`, `D2Good.K1neg`), with
`κ = Re ψ(½)` resp. `Re ψ(1)`.

**CONDITIONAL (half-plane).** `D2Good.d2_density_pos'` / `D2Good.d2_density_neg'`: the d₂ < d₁ density with only
`hB` left as a hypothesis.

## A zero at the centre

`lib/core/WeilChiZ.lean`, `lib/core/WeilChiZB.lean`, unconditional; no hypothesis on `L(½, χ)`. Let `m = PsiOmega.mC χ`
be the order of `Ξ_χ` at `0` and `Ξ_χ(t) = t^m Y(t)` (`PsiOmega.YC`, `PsiOmega.XiC_eq_pow_mul`, `Y(0) ≠ 0`). The
functional equation forces the root number to be `(−1)^m` (`PsiOmega.rootNumber_eq_neg_one_pow`), so `Y` is even
(`PsiOmega.YC_even`) and has Hadamard's product (`PsiOmega.hadamard_YC`); no Gauss-sum sign is needed. Since
`Ξ_χ′/Ξ_χ = m/t + Y′/Y` (`PsiOmega.logDeriv_XiC_split`) and `∫h(r − i)/(r − i)dr = πi h(0)`, the zero side gains
`mπi h(0)` (`PsiOmega.zero_sideZ`), and Weil's explicit formula reads `Σ_u 2h(τ_u) = weilRHSC − m h(0)` over the zeros of
`Y` (`PsiOmega.weil_XiZ`; the line integral is `PsiOmega.line_logDeriv_XiC`). Counting `ρ = ½` with multiplicity `m`,
`K₁ = Σ_u 2/(¼ + u) + 4m` (`PsiOmega.K1Z`) satisfies the same identity as before (`PsiOmega.K1Z_eq`, from
`PsiOmega.hasSum_K1Z`), `K₁ > 0` (`PsiOmega.K1Z_pos`), and Theorem B holds for
`K(x) = Σ_u 2cos(τ_u log x)/(¼ + u) + 4m` (`PsiOmega.KxZ`, `PsiOmega.KxZ_explicit`, `PsiOmega.theoremBZ`): the `m`
terms cancel, since `H_u(0) = 4(1 − cosh(u/2))`.

## Theorem B for a good real character, and `hB`

`lib/core/WeilChiB.lean`, unconditional given `GoodChar χ`. `PsiOmega.KxC_explicit`: Weil's explicit formula
(`PsiOmega.weil_XiC`) for BallPsi's test function `H_u(t) = (cos(tu) − cosh(u/2))/(t² + ¼)` gives
`K(e^u) = cosh(u/2)K₁ − sinh(u/2)log(N/π) + A_χ(u) − 2Σ Λ(n)χ(n)n^{−1/2}ĝ_{H_u}(log n)` for
`K(x) = Σ_ρ x^{ρ−½}/(ρ(1 − ρ))` (`PsiOmega.KxC`), with the archimedean integral `A_χ(u)` (`PsiOmega.archC`). At `x = 2`
the prime sum vanishes (`PsiOmega.prime_two`), giving **Theorem B** (`PsiOmega.theoremB`):
`K(2) = √2(K₁/2 + c_a + ℓ/2)`, where `c_a = Re ψ((1 + a)/2)/4 + A_a(log 2)/√2` (`PsiOmega.cA`, `PsiOmega.archA`) depends
only on the parity `a`.

**CONDITIONAL (half-plane).** `D2Good.d2_density_pos_B` / `D2Good.d2_density_neg_B` (from `D2Good.B_pos`,
`D2Good.B_neg`, via `PsiOmega.theoremBZ`): the d₂ < d₁ density with `K(2)` in place of `K₂`, limit `ν(−2c_a, ∞)`, with no
hypothesis on `L(½, χ_D)`.

## The closed forms `c₀ = −¼ log(27/4)`, `c₁ = ¾ log(3/4)`

`lib/core/CAClosed.lean`, unconditional. The digamma series `Re ψ(q + ir/2) = −γ + Σ_k (1/(k + 1) − 2s_k/(s_k² + r²))`
is integrated term by term against `H_{log 2}` (`CAClosed.hasSum_archA`, dominated by `CAClosed.bd`). Each term is
`∫e^{−s|x|}ĝ(x)dx` (`CAClosed.J_eq`, from `CAClosed.integral_exp_abs_cos`), elementary since `ĝ` vanishes beyond
`log 2` (`CAClosed.J_closed`). The series sum to `log 2`, `log 3`, `log(4/3)` (`CAClosed.hasSum_one`,
`CAClosed.hasSum_zero`). Result: `CAClosed.cA_zero`, `CAClosed.cA_one`.

**CONDITIONAL (half-plane).** `D2Good.d2_density_pos_closed` / `D2Good.d2_density_neg_closed`: the limits are
`ν(½ log(27/4), ∞)` and `ν((3/2) log(4/3), ∞)`, with no hypothesis on `L(½, χ_D)`.

## CONDITIONAL: the tail identity for `L′/L(1, χ_D)`

**CONDITIONAL on the half-plane `Re s > 11/12`** (`Eis.LFunction_ne_zero_of_re_gt`, [openai-half-plane.md](openai-half-plane.md)),
through `ChiUniform.psiChi_le_uniform`. `lib/pnt/D2Tail.lean`:

```lean
theorem GSTail.logDeriv_one_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ y : ℝ, 1 < y →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
          ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (vonMangoldt n : ℂ) / n‖ ≤
        C * Real.log (N + 2) * y ^ (2 * η - 1 / 12)
```

and `GSTail.tail_pos`, `GSTail.tail_neg`, the same for the primitive `χ_D` above with `χ_D(n) = (D|n)`, uniformly in
`D`. Proof: partial summation for the tail `n > y` at `σ > 1` (`Littlewood.norm_LSeries_le_of_sum_le`), with
`|ψ(t, χ) − ψ(y, χ)| ≤ 2C log(N + 2) t^{11/12+η} ≤ 2C log(N + 2) y^{2η−1/12} t^{1−η}`, then `σ → 1⁺`. Lean uses only
the standard axioms, since the library proves the half-plane; the result is conditional in the sense that it
rests on that input, and must be cited so.

## How the statements differ from the source

Granville and Soundararajan state Lemma 4.1 as `Σ χ_D(n) = (main term) + O(x^{1/2} n^{1/4} log n)` with the main
term for square `n`. Here the bound is for non-square `n` only, with `d(n)` in place of the log factor; the square
`n` are handled by the densities. The moments are limits, with no rate.

## How it was done

Squarefree sieve `μ²(d) = Σ_{e²∣d} μ(e)`, split at `e ≤ √(x/B)`, with Pólya–Vinogradov for the Jacobi character
(a non-principal character mod `4n`) on the small `e` and a trivial bound on the rest; the residues mod 16 and the
part at 2 by characters mod 8. The densities come from truncating the odd-square condition to `e ≤ E` (a periodic
set, with tail at most `x/E`), a dilation lemma for the prime factors of `r`, and Pólya–Vinogradov for `χ₄` to split
the odd `D` into classes mod 4. `nu1 = 4/π²` follows from the density `6/π²` of the squarefree numbers
(`SquarefreeCount.squarefree_isBigO_twelve_25ths`), which split into odd ones and twice odd ones. The lemmas
`μ² = Σ μ` and `d² ∣ e² m → ...` are `SquarefreeCount`'s.

Everything here is unconditional except the tail identity (`lib/pnt/D2Tail.lean`) the distribution of `L′/L(1, χ_d)` (`lib/pnt/D2Dist.lean`) and `hdist` with the density (`lib/pnt/D2Hdist.lean`), which are CONDITIONAL on the half-plane. The theorems are printed in `lib/check/CheckAll.lean` and depend only on
`propext`, `Classical.choice` and `Quot.sound`. No paper of the repository uses them.

## Source

- A. Granville and K. Soundararajan, *The distribution of values of L(1, χ_d)*, Geom. Funct. Anal. 13 (2003),
  992–1028, Lemma 4.1.
