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

Everything here is unconditional except the tail identity (`lib/pnt/D2Tail.lean`), which is CONDITIONAL on the half-plane. The theorems are printed in `lib/check/CheckAll.lean` and depend only on
`propext`, `Classical.choice` and `Quot.sound`. No paper of the repository uses them.

## Source

- A. Granville and K. Soundararajan, *The distribution of values of L(1, χ_d)*, Geom. Funct. Anal. 13 (2003),
  992–1028, Lemma 4.1.
