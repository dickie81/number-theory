# Searching for the positivity of `ζ` without its zeros: a checkpoint

Labels: **Proved** (Lean, no `sorry`), **Numerical** (floating point, not certified), **Speculative**.

## Finite fields and the orbit curve (Proved)

`BallFrobenius` gives the dictionary between Manin's twist and the orbit curve of `BallCurve`. In log coordinates the
curve has a stationary Gram kernel `⟨v_u, v_t⟩ = k(e^{t−u})` (`BallFrobenius.gram_v`); its samples at any step `h`
are an orbit of the flow, `U_h v_{nh} = v_{(n+1)h}` (`BallFrobenius.sample_orbit`); so every Toeplitz form
`Σ x_i x_j k(e^{(i−j)h})` is nonnegative (`BallFrobenius.toeplitz_nonneg`), as `ManinHasse.toeplitz_nonneg` is for
the Frobenius points with `h = log q`. Dictionary: degree `d ∈ ℤ` ↔ log scale `t ∈ ℝ`; `c_d` ↔ `k(e^t)`; Frobenius ↔
`U_{log q}`; the tower `𝔽_{q^n}` ↔ the multiples of one step. For `ζ` no step is distinguished and nothing plays the
integral lattice; these results assume a realization and so do not construct positivity.

## Prime-only kernels (Numerical)

`scripts/positivity/` evaluates `K_H` for `ζ` (formula of `scripts/ball_orbit.py`) and `K_χ` for Dirichlet characters
(closed form `dcore.py` from the tests of the orbit-lattice conjecture), from prime sums and archimedean terms only,
primes up to `2·10^4`.

| test | `ζ` | `χ mod 19`, failing pair | `χ₋₁₆₃` |
|---|---|---|---|
| `K(1)` | 0.0462 | 4.3578 | 7.7085 |
| two-prime slice `min (Re K(2^a3^b) + K(1))/K(1)`, `|a| ≤ 6`, `|b| ≤ 4` | 0.546 | 1.882 | 0.831 |
| `min d_k/d_1`, `k ≤ 30` | 1 | 0.351 (k = 3) | 0.499 (k = 2) |
| Toeplitz at `h = log 2`, `λ_min/K(1)`, size 10 | 0.151 | 0.015 | 0.053 |

The two-prime slice and the Toeplitz forms are positive for all of them, as GRH predicts: they are Weil-type positivity
and cannot separate `ζ` from the characters. Only the pivot inequality `d_k ≥ d_1` separates. Over all 252 nontrivial
characters to prime moduli `5 ≤ p ≤ 43` (`k1scan.py`, pivots `k ≤ 8`), 34 fail, and failure tracks `K(1)`: none with
`K(1) < 1` fails (156 characters), 20 of 20 with `K(1) ≥ 3` fail. Since `K(1) = Σ_ρ 1/|ρ|²` under GRH, a large `K(1)`
means a low first zero.

**Reading (Speculative).** The pivot conjecture appears to measure the height of the lowest zero, not an arithmetic
structure: `ζ` passes because `γ₁ ≈ 14.13` is high and `K(1)` small. So it is unlikely to be the zero-free analogue of
Castelnuovo–Severi. The feature `ζ` has that the characters lack is the pole, whose terms `r^{±1/2}` play the classes
`e₁, e₂` of `C × C` (the `m + n` in `BallWeil.inter`); the most promising lead is a statement that uses the pole in
that role, negativity on its orthogonal complement, rather than a normalisation by `K(1)`.
