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

## The pole complement (Proved, reformulation)

`BallPole` makes the lead precise. The pole classes `e₁`, `e₂` span a hyperbolic plane (`BallPole.pole_hyperbolic`),
every class splits orthogonally as `D² = 2(D·e₁)(D·e₂) + D⊥²` (`BallPole.selfInt_decomp`), and RH is `D⊥² ≤ 0` on the
complement with real coefficients (`BallPole.rh_iff_hodge_index_real`, `BallPole.rh_iff_cs_real`). On the complement
`D² = −Q(c)`, so this is again positivity of the Gram form of the orbit: the pole splits off exactly and adds no
constraint. Without a pole the complement is everything (`BallPole.hodge_no_pole_iff`). So the difference between `ζ`
and the characters seen by the pivot test is not explained by the pole as a hyperbolic summand; what is open is a proof
of negativity on the complement that does not pass through the zeros. The pivot normalisation by `d_1 = K(1)` is a
statement about the complement alone, and nothing in this decomposition forces it.

## Integrality and the primes (Proved formulas; obstruction)

`BallPrimes` evaluates the Gram matrix at integer ratios from the primes alone: `G(kn, n) = n·G(k, 1)`
(`BallPrimes.gram_mul`), and `G(k, 1) = P(k) + ((k + 1)/2)K₁ + ((k − 1)/2)(log π − 2 log k) + √k·A(log k)`
(`BallPrimes.gram_explicit_int`), with the prime part `P(k) = Σ_{j ≤ k} Λ(j)(k/j − 1) ≥ 0`
(`BallPrimes.primePart_nonneg`).

**Obstructions found.**
1. *Integrality.* `P(k)` is a combination of the `log p` with coefficients `Σ_{p^a ≤ k}(k/p^a − 1)`, rational and not
   integral, and `K₁`, `A` are transcendental-looking constants. The integral objects nearby are `e^{ψ(k)} = lcm(1..k)`
   and `e^{Σ Λ(j)⌊k/j⌋} = k!`, but `G` uses `k/j`, not `⌊k/j⌋`: the fractional parts `{k/j}` are exactly what
   separates `G` from an integral form (not formalised).
2. *No tensor structure.* The Euler product makes the kernel additive over the primes (it comes from `ζ′/ζ`), so `G` is
   a sum of per-prime pieces plus pole and archimedean terms, not a tensor product of per-prime kernels. Positivity
   cannot reduce to local positivity: the prime pieces enter the kernel `K_H` with a minus sign (the `−ψ(x)/√x` of
   `BallPsi.kerH_explicit`) and must be beaten by the archimedean and pole terms, a global cancellation.
3. *Restricted families.* Unconditional positivity on a two-prime slice is already RH (`BallSlice.rh_iff_bound_pair`,
   `BallSlice.rh_iff_two_three`), so extending slice positivity to more primes cannot be done unconditionally
   without proving RH; any finite-prime bound has to be numerical or conditional.

**Next lead (Speculative).** Replace `k/j` by `⌊k/j⌋`, which gives the integral form `log k!` (the Chebyshev
identity), and measure the difference: the fractional-part correction `Σ Λ(j){k/j}` is the obstruction term, and its
size is controlled by the error term in the prime number theorem, which is where RH re-enters.

## The integral part and the fractional parts (Proved split; Numerical test)

`BallFract` proves Chebyshev's identity `log k! = Σ_{j ≤ k} Λ(j)⌊k/j⌋` (`BallFract.log_factorial_eq`), the split
`P(k) = log k! − ψ(k) + C(k)` with `C(k) = Σ_{j ≤ k} Λ(j){k/j}` (`BallFract.primePart_split`), the bounds
`0 ≤ C(k) ≤ ψ(k) ≤ k·log 4 + 2√k·log k` (`BallFract.fracPart_nonneg`, `BallFract.fracPart_le`), and
`G(k, 1) = log k! − ψ(k) + C(k) + (pole and archimedean terms)` (`BallFract.gram_split`).

**Numerical** (`scripts/positivity/intpart.py`, floating point, uncertified). Extend `C` to real ratios by
`C(x) = Σ_{j ≤ x} Λ(j){x/j}` and compare the Gram matrix `G(m, n)`, `1 ≤ m, n ≤ N`, with two modifications:

| N | full `G`: `λ_min`, negatives | integral part (`C` removed) | `C` replaced by its mean `(1 − γ)x` |
|---|---|---|---|
| 10 | 0.0137, 0 | −5.83, 3 | −1.85, 4 |
| 50 | 0.0040, 0 | −198, 12 | −46.7, 14 |
| 100 | 0.0023, 0 | −830, 26 | −189, 27 |
| 200 | 0.0013, 0 | −3380, 50 | −753, 51 |

The integral part alone is far from positive: about `N/4` negative eigenvalues, with `λ_min` of order `−N²/12`. Even
replacing `C(x)` by its mean `(1 − γ)x` (the mean value is the classical one, not proved here) leaves about `N/4`
negative directions.

**Obstruction.** The positivity of `G` is not carried by an integral part with a small correction: it is carried by
the fractional parts `{x/j}` themselves, whose fluctuations around their mean cancel negative eigenvalues of order
`N²`, down to a margin `λ_min ≈ 0.26/N`. A bound on `C` of the form `|C(x) − (1 − γ)x| ≤ E(x)` can give positivity
only through a perturbation argument, which needs `E` small against the margin; since the margin is `O(1/N)` while the
negative part is `O(N²)`, no size bound on `C` suffices (Speculative but robust in these numerics): positivity is a
statement about the correlations of `{x/j}`, as RH is a statement about the oscillation of `ψ(x) − x` (equivalently
`ψ(x) = x + O(x^{1/2+ε})`, `LonelyJoins.rh_iff_lonely_weight` for the library's form).

**Next lead (Speculative).** Treat the fractional parts as the object: `Σ_j Λ(j){x/j}` is a sawtooth sum, whose Fourier
expansion `{y} = 1/2 − Σ_h sin(2πhy)/(πh)` turns the Gram matrix into exponential sums over `Λ`. Positivity then asks
for a structured (not size) property of these sums, the place where the large sieve or Montgomery–Vaughan mean values
would enter.

## The harmonics of the sawtooth (Proved split; Numerical test)

`BallSaw` writes `C(k) = ψ(k)/2 + Σ_{j ≤ k} Λ(j)s(k/j)`, `s(y) = {y} − 1/2` (`BallSaw.fracPart_saw`), with
`|C(k) − ψ(k)/2| ≤ ψ(k)/2` (`BallSaw.abs_fracPart_sub_le`). The Fourier series `s(y) = −Σ_h sin(2πhy)/(πh)` (classical,
not formalised) takes the value `0` at the integers, so it misses `Σ_{j ∣ k} Λ(j)/2 = (log k)/2` (`BallSaw.jump_eq`);
the numerics below add that jump back exactly, so `H → ∞` recovers `G`.

**Numerical** (`scripts/positivity/harm.py`, floating point, uncertified): negative eigenvalues of the Gram matrix with
`C` replaced by `ψ/2 −` (jump) `− Σ_{h ≤ H} Σ_j Λ(j) sin(2πh x/j)/(πh)`.

| N | H = 0 | 8 | 32 | 128 | 512 | 1024 | 2048 | first `H` with none |
|---|---|---|---|---|---|---|---|---|
| 25 | 11 | 8 | 3 | 1 | 0 | 0 | 0 | 256 |
| 50 | 20 | 17 | 10 | 3 | 1 | 0 | 0 | 1024 |
| 100 | 44 | 41 | 34 | 19 | 4 | 1 | 0 | 2048 |
| 200 | 89 | 88 | 76 | 58 | 25 | 13 | 4 | > 2048 |

No low band of harmonics carries the positivity: the number of negative directions falls slowly and steadily with `H`,
and the `H` needed grows roughly like `N²` (between `N^{1.5}` and `N²` in this range). That is the resolution of the
ratios `m/n` with `m, n ≤ N`, whose arguments `x/j` are spaced by about `1/N²`.

**The gap to mean values (Speculative estimate).** A large sieve / Montgomery–Vaughan bound controls
`Σ_{h ≤ H} |Σ_j a_j e(h x/j)|²` by `(H + N²)·Σ|a_j|²` over well-spaced points: it bounds sizes. Here the tail
`h > H` must be smaller in operator norm than the margin `λ_min ≈ 0.26/N`, while a mean-value bound on the tail gives
about `ψ(N)/√H ≈ N/√H` per entry, so `H ≫ N⁴` before the bound alone suffices, against the observed `H ≈ N²`. The two
missing factors of `N²` are cancellation between the harmonics that a size bound cannot see.

**Obstruction (Speculative).** Positivity is spread over all scales up to the Farey resolution `1/N²` and is a
cancellation between harmonics, not a dominant low-frequency term plus a bounded tail. A proof by truncation and mean
values loses a power of `N` in this model. What would be needed is a positivity statement for the full sawtooth
kernel `Σ_j Λ(j)s(x/j)` on Farey-type point sets, which is again a form of RH.

## The tower (Proved: limits and dictionary; Speculative: what the limit lacks)

`FrobTower` defines Toeplitz positivity of `c : ℕ → ℝ`, `Σ_{i,j<K} x_i x_j c(|i − j|) ≥ 0`, proves it closed under
positive rescaling, sums and pointwise limits (`FrobTower.ToeplitzPos.of_tendsto`, `FrobTower.ToeplitzPos.add`,
`FrobTower.tower_limit`), shows that the normalised traces of an elliptic curve over `𝔽_q`, `q` odd, have it
(`FrobTower.manin_toeplitzPos`), and that in every curve realization of a kernel `k`, `d ↦ Re k(e^{dh})` has it for every
step `h` (`FrobTower.curve_toeplitzPos`).

**Dictionary.** `𝔽_q` and its extensions `𝔽_{q^d}` ↔ one step `h = log q` and its multiples; normalised trace `c_d` ↔
`Re k(e^{dh})`; Frobenius ↔ `U_h`; a tower `E_m/𝔽_{q_m}` with normalisation `g_m` ↔ a family of kernels whose limit is
Toeplitz positive. In the curve, every `h > 0` is a step at once: positivity on `ℝ` is positivity at all `h`, which a
single tower over one `q` does not give.

**What the limit loses (Speculative).** Positivity survives limits, but the finite-field proof does not come from
positivity alone: it comes from an integral lattice (`End(E)`, the Néron–Severi group of `C × C`) on which the Gram
entries are integers (point counts) and the Hodge index theorem holds. Limits of normalised traces keep the
positivity and lose the integrality: the normalised entries `c_d` are real, and the limit kernel has no lattice. So a
tower produces a kernel of the same shape as `ζ`'s with no extra structure that could prove positivity; it cannot be
the missing input. Letting `q → 1`, i.e. `h → 0`, formally turns the samples `d·log q` into a continuum, which is the
passage from `ℤ` to `ℝ` of `BallCurve`; that the kernel of `ζ` arises this way (an "`𝔽_1`" limit) is a heuristic only.
Asymptotically, towers over a fixed `q` have `#C(𝔽_q)/g ≤ √q − 1` (Drinfeld–Vlăduţ) and towers attaining it exist for
square `q` (Ihara; Garcia–Stichtenoth): there the normalised point counts have a limit distribution of Frobenius
angles, but these are context, not checked here, and none of it is formalised.
