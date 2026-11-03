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

## A different lattice: Smith's gcd lattice (Proved; Numerical; where RH sits)

`SmithLattice` proves Smith's factorisation `gcd(i, j) = Σ_{d ∣ i, d ∣ j} φ(d)` (`SmithLattice.gcd_eq_sum_totient`), so
`Σ_{i,j ≤ N} x_i x_j gcd(i, j) = Σ_{d ≤ N} φ(d)(Σ_{d ∣ i} x_i)²` (`SmithLattice.smith_form`): the gcd matrix is
`E·diag(φ)·Eᵀ`, `E` the divisibility matrix. It is an integral Gram matrix, positive (`SmithLattice.smith_nonneg`) and
definite (`SmithLattice.smith_pos`), unconditionally, with the explicit basis `√φ(d)·(column d of E)`. Smith's
determinant `∏φ(k)` is `Redheffer.det_smith`. In the same basis,
`Σ_{d ≤ N} μ(d)⌊N/d⌋ = 1` (`SmithLattice.mertens_identity`).

**Where RH sits.** `E` is unitriangular with inverse `E⁻¹(d, n) = μ(n/d)` for `d ∣ n`, so `μ` gives the coordinates of
`δ_1` in the basis of divisibility vectors, and Mertens' `M(N) = Σ_{n ≤ N} μ(n)` is the sum of those coordinates.
RH is equivalent to `M(N) = O(N^{1/2+ε})` (`MertensExponent.rh_iff_mertens`). The determinant of the Redheffer matrix
(`1` where `i ∣ j` or `j = 1`) is `M(N)` (Redheffer 1977; now `Redheffer.det_redheffer`): that matrix is `Eᵀ` with its
first column replaced by ones, a rank-one change of the lattice basis. So in this lattice positivity is free, and RH is
a growth bound on one coordinate functional, the covolume change under a rank-one perturbation, not a positivity
statement.

**Compared with the finite-field lattice.** Both are integral and unconditionally positive. In `End(E)` the RH content
is that the Frobenius orbit sits in the lattice with Gram entries the point counts, and positivity gives the bound. In
Smith's lattice nothing ties `M(N)` to the form: its Gram entries `gcd` carry no zeros, and the bound on `M` is not
implied by positivity. The two halves (an integral positive lattice; the arithmetic quantity bounded by positivity)
are realised separately and not together.

**Numerical** (`scripts/positivity/gcdnum.py`, floating point): the normalised gcd matrix `gcd(i, j)/√(ij)` has
`λ_min` = 0.0486, 0.0364, 0.0293, 0.0233, 0.0186 and `λ_max` = 8.47, 10.9, 13.8, 17.2, 21.1 at `N` = 50, 100, 200,
400, 800. `λ_max` grows faster than `log N` (the size of GCD sums, studied by Aistleitner, Berkes and Seip, is the
relevant literature; not checked here); `λ_min` decays slowly, about like `N^{−1/3}` in this range. This matrix is the
`s = 1/2` member of the family `gcd(i, j)^{2s}/(ij)^s`, whose Dirichlet-series structure involves `ζ(2s)` near the
critical line (Speculative link to Beurling–Nyman and Báez-Duarte, not explored).

**Next lead (Speculative).** Put the Redheffer perturbation inside the Smith form: the Gram matrix of the perturbed
basis is `G + (rank two)`, and `M(N)` enters its determinant. A bound `|M(N)| ≤ N^{1/2+ε}` is then a statement on how
far a rank-one change can shrink the covolume of an explicit positive integral lattice.

## Redheffer inside Smith (Proved; Numerical)

`Redheffer` proves `det E = 1` (`Redheffer.det_E`), that `Eᵀ·diag(φ)·E` is the gcd matrix (`Redheffer.smith_entry`)
with determinant `∏φ(k)` (`Redheffer.det_smith`), `Σ_{m ≤ K} M(K/m) = 1` (`Redheffer.sum_mertens_div`), so that
`c_j = M(n/j)` solves `E c = 1`, and by Cramer's rule Redheffer's theorem `det R_n = M(n)` (`Redheffer.det_redheffer`).
The positive semidefinite integral form `R·diag(φ)·Rᵀ` has determinant `M(n)²·∏φ(k)` (`Redheffer.det_gram_redheffer`):
`M(n)²` is the ratio of the covolumes of Redheffer's and Smith's forms. Unconditionally `|M(n)| ≤ n`
(`Redheffer.abs_mertens_le`).

**What positivity gives.** `M(n) = c_1` is a coordinate of `c` in Smith's form `G = Eᵀ·diag(φ)·E`, with
`cᵀGc = (Ec)ᵀdiag(φ)(Ec) = Σ_{k ≤ n} φ(k)` and `(G⁻¹)_{11} = Σ_{k ≤ n} μ(k)²/φ(k)`. Cauchy–Schwarz in `G` gives
`M(n)² ≤ Σφ(k)·Σμ(k)²/φ(k) ≈ (3/π²)n²·log n` (derived here, not formalised): about `1.3n` to `1.8n` for
`n = 10²` to `10⁴`, worse than the trivial `n`. Hadamard's inequality for `R·diag(φ)·Rᵀ` gives `|M(n)| ≤ e^{6150}` at
`n = 10⁴`. Numerical (`scripts/positivity/redh.py`): `M(10⁴) = −23`, `|M|/√n` = 0.10, 0.06, 0.11, 0.23 at
`n` = 10², 10³, 3·10³, 10⁴.

**What would be needed (Speculative).** Positivity of these forms costs nothing and bounds `M(n)` only through
Cauchy–Schwarz, which loses because the vector `c = (M(n/j))_j` has `G`-norm `≈ n` while its first coordinate is of
size `√n`: RH says that `c` is far from aligned with the dual vector of the first coordinate, an equidistribution
statement about `M(n/j)` in Smith's metric, `|⟨e_1, c⟩| ≤ n^{−1/2+ε}·‖c‖_G·‖e_1‖_{G⁻¹}`. No inequality from positivity,
interlacing or Hadamard alone sees that cancellation; it needs the sign changes of `μ`.

## What forces the signature: the Hodge index axioms (Proved)

`HodgeAxioms` proves the classical argument abstractly: for a symmetric bilinear form `B`, an effective set `Eff` and
a class `h` with (ample) `B(D, h) > 0` for nonzero effective `D` and (Riemann–Roch) `B(D, D) > 0 ⇒ D` or `−D`
effective, `B(D, h) = 0 ⇒ B(D, D) ≤ 0` (`HodgeAxioms.hodge_index`), and `B(D, D)B(h, h) ≤ B(D, h)²` when `B(h, h) > 0`
(`HodgeAxioms.hodge_cs`). For Weil's form of `ζ` with `h = e₁ + e₂`:

| axiom | status for `ζ` |
|---|---|
| `h² > 0` | `h² = 2`, unconditional (`BallPole.pole_hyperbolic`) |
| ample on the cone of nonnegative classes | holds, unconditional (`HodgeAxioms.ample_naive`) |
| effective classes meet nonnegatively, `D_m·D_n ≥ 0` | Numerical: minimum `1.9538` at `m = n = 1` over `m, n ≤ 200`; not proved |
| Riemann–Roch dichotomy, nonnegative cone | fails, unconditional (`HodgeAxioms.rr_fails_naive`: `D = e₁ + e₂ − D_1/4`) |
| Riemann–Roch dichotomy, positive cone `{D² ≥ 0, D·h ≥ 0}` | automatic, but then ampleness is RH (`HodgeAxioms.rh_iff_ample_pos`) |
| conclusion (Hodge index for `h`) | equivalent to RH (`HodgeAxioms.rh_iff_hodge_h`) |

**The single missing mechanism.** A notion of effectivity defined independently of the intersection form, for which
both ampleness and the Riemann–Roch dichotomy hold. On a surface it is `h^0(D) > 0`, and the dichotomy is the
Riemann–Roch inequality `h^0(D) + h^0(K − D) ≥ D²/2 − D·K/2 + χ`; for `ζ` there is no cohomology `h^0` of the formal
classes `D_n`, and both natural candidate cones fail, one on the dichotomy and the other by circularity.

## Transposing the spheres (`Transpose`)

Proved: for `B' = −B` the transposed dichotomy (`D² < 0 ⇒ ±D effective`) fails for the nonnegative cone (`e₁ − e₂`), the natural ample class `e₁ − e₂` is not positive on that cone, and the transposed index statement `D·h' = 0 ⇒ D² ≥ 0` is false unconditionally (`D_1 − e₁ − e₂`). `−B` has infinitely many positive directions under RH, so it is not of Hodge-index shape. On finite sections, positivity of the dual Gram matrix `G⁻¹` is equivalent to positivity of `G`. Remark (not formalised): any Lorentz-type reflection of the pole plane is an isometry, so it preserves the signature and cannot change the missing axiom. Conclusion: the missing axiom stays where it was — an effectivity notion, defined independently of the form, satisfying the Riemann–Roch dichotomy.

## The tower of spheres (`GravastarTower`)

Proved: on nested sections the excess `ε_N = −λ_min(G_N)` is monotone; RH ⇔ `ε_N ≤ 0` for all `N`; balance up to every `δ > 0` at infinitely many levels already gives RH, so every normalised "asymptotic balance" (`ε_N ≤ f(N)`, `f → 0`) collapses to exact balance. For spheres meeting at a junction (windows, not nested): `Q(x_S + x_T) = Q_S + Q_T + cross terms`, and if the windows are cofinal with excess → 0 this again gives RH. The threshold: non-cofinal windows (disjoint dyadic blocks) avoid the collapse, but then balance on the spheres does not control the cross terms, and adding a gluing condition strong enough to control them is RH again.

Numerics (uncertified, `scripts/positivity/tower.py`): `ε_N < 0` up to `N = 400` (`ε_400 ≈ −7.3e−4`, `N·ε_N ≈ −0.29`); dyadic blocks have `λ_min` bounded away from 0 (≈ 0.24–0.51), but the cross-term norm grows like the block size (≈ 1.1 → 69 for `N = 8 → 64`), far above the crude Schur gluing bound `‖C‖² ≤ λ₁λ₂`. The block spheres are comfortably balanced; the difficulty is entirely in the junction.

## A four-dimensional junction (`Junction4`)

Proved: if cross terms factor through `k` coordinates `p_i, q_i` and `Q_S ≥ Σp_i²`, `Q_T ≥ Σq_i²`, the glued form is nonnegative (`k = 4` stated). Sufficient only.

Numerics (uncertified, `scripts/positivity/junction4.py`, dyadic blocks `[8,16) … [256,512)` of the orbit Gram): every cross block is numerically full rank (rank = smaller block size at tolerance 1e−10); `σ₅/σ₁ ≈ 0.18–0.36` and the relative Frobenius tail beyond rank 4 is ≈ 0.20–0.35; projecting out the candidate directions `1, n, √n, √n·log n` on both sides leaves 80–92% of the cross term; the top-4 singular subspaces of `[8,16)` against different partners have principal angles up to 51°–88°, so there is no common four-dimensional junction. The four-dimensional junction hypothesis is false for the orbit form; the pole-complement version was not tested.

### Different hyperplanes (uncertified, `scripts/positivity/junction4.py`)

Best common junction = top-`k` singular directions of the off-block-diagonal part of the form (jointly over all pairs), `M = 255, 511`:

| family | orbit Gram: k=4 / k=16 / k for 95% | dual `G⁻¹`: k=4 / k for 95% |
|---|---|---|
| dyadic | 0.81 / 0.97 / 12 | 0.97 / 3 |
| triadic | 0.79–0.81 / 0.98 / 11 | 0.97 / 4 |
| largest prime `P(n)` | 0.72 / 0.89 / 31–34 | 0.98 / 3 |
| `n mod 5` | 0.66–0.67 / 0.87–0.88 / 31–34 | 0.97 / 3 |
| 2-adic `2^v·odd` | 0.63 / 0.90 / 28–30 | 0.99 / 3 |
| 7-smooth / rough | 0.68–0.69 / 0.94–0.95 / 17–19 | 0.98 / 4 |
| Mellin frequency bands (dyadic) | 0.88–0.89 / 0.97–0.98 / 7–11 | — |

The orbit Gram has no low-rank common junction (dyadic: `k ≈ 12` for 95%, stable in `M`; arithmetic families worse). The pole-complement form is `−Q(c)` on the same coefficients (`BallPole.selfInt_of_orth`), so its cross terms are the same up to sign. The dual's apparent rank-3 junction is an artefact: 91% of `‖G⁻¹‖²` sits in the single softest eigenvector of `G` (`λ_min ≈ 6e−4` at `M = 511`) and 99% in the softest four; removing those four, the dual needs `k ≈ 19–20` for 95%. A junction through the softest directions of `G` would need positivity margin there, which is exactly the RH-sensitive part, so it was not formalised.

### Scaling of the dyadic junction (uncertified, `scripts/positivity/junction_scale.py`)

| size | k for 90% | k for 95% | k for 99% |
|---|---|---|---|
| 255 | 8 | 12 | 26 |
| 511 | 8 | 12 | 26 |
| 1023 | 8 | 12 | 26 |
| 2047 | 8 | 12 | 26 |
| 4095 | 8 | 12 | 26 |

Checks: `gram(2047)` agrees exactly with the top-left block of `gram(4095)` and the matrix is exactly symmetric; this checks cutoff consistency, not floating-point accuracy of `K_H` at large `n`. Successive singular-value ratios are size-independent (0.89, 0.93, 0.87, 0.49, 0.90, 0.99, …) but not geometric: the spectrum comes in groups of four with gaps. Coupling between blocks does not decay with the gap `|a − b|` (normalised ≈ 0.63–0.78 for gaps 1–8): it is not near-neighbour.

Directions: the top four common directions have block profiles in `u = n/2^a` stable across blocks (|corr| ≈ 0.7–0.95), and on the largest block they are fitted far better by `n^{±iγ}` with `γ` near the first zeta ordinates than by polynomials in `log u` or by `u^{±1/2}, u^{1/2}log u` (residual ≈ 0.07–0.11 against ≈ 0.5–0.9; control frequencies 10, 17 give 0.13–0.27). A single-frequency scan gives best `γ ≈ 13.6–14.5` for directions 1–4 and `≈ 21.4–23.4` for 5–8. A block spans only `log 2` in `log n`, so frequency resolution is ≈ `2π/log 2 ≈ 9`: this is consistent with `γ₁ = 14.13, γ₂ = 21.02` but does not pin them.

Interpretation: this is expected and not zero-free. The Gram matrix is computed from primes, but by the explicit formula it is the zero-indexed `ℓ²` Gram (`BallLattice.gram_cw`), `Σ_ρ` of rank-two oscillating terms `n^{1/2 ± iγ}` plus a smooth part. The junction is the zeros, seen through the primes, with a slowly decaying tail (`k₉₉ = 26`), not a finite-rank structure. A gluing inequality on these directions would be a statement about the zeros. So it was not formalised: `Junction4.glued_nonneg` already covers the sufficient direction for any finite `k`, and no finite-rank hypothesis holds here.

### Gluing by relative surface areas (Proved; uncertified numerics, `scripts/positivity/junction_area.py`)

Weight dyadic block `k` (n in [2^k, 2^(k+1))) of the prime-side Gram matrix by a unit-sphere area
`|S^(d-1)| = 2π^(d/2)/Γ(d/2)`, with `d = k+1`, `d = 2^k`, or the ratio `|S^d|/|S^(d-1)|`.

- **Symmetric gluing** (cross terms by `√(w_a w_b)`) is the congruence `W^(1/2) G W^(1/2)`. `Junction4.weighted_nonneg_iff`
  proves it is nonnegative iff the unweighted form is, for any positive weights. Numerically, the minimum eigenvalue stays
  positive exactly when the unweighted one does (sizes 255 to 4095). With `d = 2^k` the weights fall below 1e-57, so the form is
  numerically zero there; the tiny negative values (about -1e-35) are rounding, not a sign change.
- **Blocks weighted, cross terms not**: strongly indefinite for every scheme and size (minimum eigenvalue from -0.3 down to -1.8e4).
  Shrinking the blocks relative to the junction destroys positivity.
- **Verdict**: area weighting cannot make the problem easier. Symmetric weighting changes nothing, and asymmetric weighting breaks
  positivity. Positivity of the weighted form for all sizes is exactly as strong as the unweighted one.

## A de Sitter tower of spheres (`DeSitterTower`)

Construction: stack the unit spheres of the dyadic blocks as time slices, with time from the pole plane, and use the
Lorentzian form `Q(t, x) = −t² + Σ_k q_k(x_k)`. Proved (no `sorry`, standard axioms only): at time `sinh τ` the
hyperboloid `Q = 1` meets the tower in the sphere `Σ_k q_k = cosh² τ` (`slice_radius`); with every slice form
nonnegative the tower is Lorentzian, with a negative direction (`time_neg`) and no negative-definite plane
(`no_timelike_plane`, `tower_lorentz`). For the glued prime-side form, `−D² = −½(D·e₁ + D·e₂)² + ½(D·e₁ − D·e₂)² + Q(c)`
(`neg_selfInt_eq`), the space-like part is nonnegative on every real class if and only if RH (`rh_iff_deSitter`), and
under RH the glued form is Lorentzian (`deSitter_of_rh`). So "the glued tower is de Sitter" is RH, not a route to it.

Numerics (uncertified, `scripts/positivity/desitter.py`): with blocks scaled by `cosh(k log 2)` (a congruence), the glued
form has one negative direction for `M = 255, 511, 1023`; at `M = 2047` a second appears at size ~1e−9 against a top
eigenvalue ~1e7, which is round-off. Time evolution `u = log x` of the prime-side kernel `K_H(e^u)`, by a matrix pencil
on `u ∈ [log 20, log X]`, recovers the first ten zeros to about 1e−3 for `X = 10⁶` (resolution ≈ 0.6), with real parts
`β − ½` between −0.004 and +0.0006. This is the explicit formula read from the primes (a classical fact), and it
measures real parts only for low zeros and to the resolution of a finite range of `u`; it does not bound real parts
for all zeros, which is what RH needs.

## The junction as a sphere (`JunctionSphere`)

Question: can the cross terms between neighbouring dyadic blocks be realised as inner products of explicit vectors built
from primes, making the glued form a Gram matrix? Proved (no `sorry`): a Gram kernel has nonnegative form
(`formG_gram`); for any split `gram = g₁ − g₂`, RH holds iff `Q_{g₂} ≤ Q_{g₁}` on every real vector
(`rh_iff_remainder`), and a manifest Gram part with a bounded remainder gives positivity (`nonneg_of_remainder`).

Numerics (uncertified, `scripts/positivity/junction_sphere.py`, sizes 255 to 4095). From
`K_H(x)/√x = Σ_{k≤x} Λ(k)(1/k − 1/x) − log x + 1 + γ − log(2π)/x + tail(1/x)`, two natural splits: primes `P`
(nonnegative weights, but zero diagonal) plus archimedean `A`; and a prime-free main part `C` plus the fluctuation
`R = hi·∫₁^r (ψ(t) − t)/t² dt`. None of `P, A, C, R` is positive semidefinite: their smallest eigenvalues are of order
`−M²` (−5e6 at 4095) while `λ_min(G) ≈ 1e−4`, and `‖R‖/‖C‖ = 1.000` on every block pair, so `G` is a near-total
cancellation of two indefinite pieces. Neighbouring block pairs are positive, so the junction is realised by the
blocks' own vectors, but the contraction `‖A^{−1/2} B C^{−1/2}‖` is 0.9699, 0.9903, 0.9970, 0.9991, 0.9997, 0.9999
for the pairs up to `[1024,2047]×[2048,4095]`: the margin `1 − ‖·‖` falls by about a factor 3 per doubling. The
non-Gram remainder sits exactly where RH lives, and no zero-free explicit Gram part was found.

## The gravastar margin (`GravastarMargin`)

Proved (no `sorry`): a nonnegative margin `f(N)·‖x‖² ≤ Q_N(x)` at every level gives RH (`rh_of_margin`), RH gives
margin `0` (`margin_zero_of_rh`), and if RH fails a negative vector appears at some level and persists at every higher
level (`exists_neg_of_not_rh`, `neg_persists`).

Numerics (uncertified, `scripts/positivity/gravastar_margin.py`, `M = 2^k − 1` up to 8191): the junction margin
`1 − ‖A^{−1/2}BC^{−1/2}‖` of the top two dyadic blocks is 9.7e−3, 3.0e−3, 9.2e−4, 3.1e−4, 9.9e−5, 2.9e−5 (pure power
fit `M^{−1.66 ± 0.01}`); the global `λ_min(G)` is 1.07e−3 … 5.2e−5 (`M^{−0.87 ± 0.004}`, close to `1/M` with a slowly
rising `M·λ_min` 0.27 → 0.42). Control: the arithmetic-free positive-definite kernel `x^{−1/2}` (that is `e^{−|u|/2}`)
gives margin exactly halving per doubling (`a = 1.00`), so a power-law decay by itself is a normalisation effect; the
prime-side exponent 1.66 differs, but smoother toy kernels (sech, Gaussian) were numerically singular and could not be
compared. Synthetic off-line zero: replacing the pair at `½ ± 14.13i` by the quartet `½ ± δ ± 14.13i` (note `δ → 0` is a
double zero, not the original kernel) makes the margin negative from `M ≈ 1023` (`δ = 0.05`), `4095` (`δ = 0.02`),
`8191` (`δ = 0.01`); `δ = 0.005` stays positive to 8191. So the margin is a detector of off-line zeros with a reach
growing as `δ` shrinks, but a positive margin at finite `M` says nothing about `δ` below the reach, and no finite run
can prove RH.

## The sphere tower at equilibrium (`SphereTower`)

Construction: write `log ξ(s) = log(π^{−s/2}Γ(s/2+1)) + log((s−1)ζ(s))`. The first term is `−log V_s`, the unit-ball
volume in dimension `s` (the sphere tower; `π^{−s/2}Γ(s/2) = 2/|S^{s−1}|`), the second is the prime radiation (Euler
product). Proved (no `sorry`): `arch_eq_inv_area`, `arch_succ_eq_inv_vol`, `area_eq_mul_vol` (`|S^{s−1}| = s·V_s`),
`vol_eq_volume_ball` (Mathlib's unit-ball volume of `ℝⁿ`), `gaussian_one`, `area_pos`, and the abstract
`balance_iff` (`λ = a + b ≥ 0` iff `−b ≤ a`). Li's criterion (RH iff all `λ_n ≥ 0`) is not formalised.

Numerics (uncertified, `scripts/positivity/sphere_tower.py`, 230 digits; radiation Taylor coefficients by a Cauchy
integral of `log((s−1)ζ(s))` on `|s − 1| = 2.5`; `λ_n = Σ_k k·C(n,k)·ℓ_k`): `λ_1 = 0.0230957`, `λ_2 = 0.0923457`
(match the known values), and the split is

| n | sphere part | radiation part | λ_n | radiation / sphere |
|---|---|---|---|---|
| 1 | −0.5541 | 0.5772 | 0.0231 | −1.04 |
| 10 | 0.9555 | 1.3238 | 2.2793 | 1.39 |
| 100 | 117.975 | 0.629 | 118.604 | 0.0053 |
| 500 | 989.237 | 2.664 | 991.900 | 0.0027 |
| 1000 | 2324.297 | 1.756 | 2326.053 | 0.00076 |

No `λ_n < 0` for `n ≤ 1000`. For small `n` the sphere part is negative and the radiation holds `λ_n` up; for large
`n` the sphere part grows like `(n/2) log n` and the radiation stays `O(1)` here. Honest caveat: a zero off the line at
height `T` makes the radiation part grow exponentially only once `n ≳ T²`, and all zeros below height ~3e12 are known
to be on the line, so `n ≤ 1000` cannot see one; the finite balance is consistent with RH and proves nothing.

## A tower of black holes (uncertified numerics, no Lean)

Tangherlini black holes `f = 1 − (r_h/r)^{D−3}`, `D = 4 … 40`, massless scalar `l = 0, 1, 2`, overtones `n < 4`, first-order
WKB (Schutz–Will; checks against the known `D = 4`, `l = 2` mode `0.967 − 0.194i` (units `r_h = 1`) to about 5%).
Shells: `κ_D = (D−3)/2`, `T_H = κ/2π`, horizon area `|S^{D−2}|` (peaks near `D = 8`, then collapses), unit-area radius
`|S^{D−2}|^{−1/(D−2)}`. No zeros were used as input; the first 30 zeros are only the comparison target (`scripts/positivity/bh_tower.py`).
Best affine fit to the first 30 zeros (rms residual; mean zero spacing 3.0): Re `ω r_h` 2.73, Im `ω r_h` 2.38, the
shells `κ_D` 2.57 (exactly a picket fence), `log |S^{D−2}|` 1.94, the asymptotic ladder `2πT_H(n+½)` 2.84; controls:
picket fence 2.57, random uniform 4.21, and `k / log k` (the zero-count shape, no zeros) 1.06. Spacing statistic `⟨r⟩`:
zeros 0.603 (GUE); black-hole spectra 0.37–0.39 (Poisson-like superpositions of ladders) or 0.74–1.0 (picket fences).
Nothing beats the arithmetic-free `k / log k` control; the horizon ladders are evenly spaced by construction, and
modes "stuck" with a common damping per level are a generic property of horizons, not of `ζ`.

## Shell-to-shell relations of the tower (uncertified numerics, no Lean)

Shells `D = 4 … 203` (`scripts/positivity/shell_relations.py`): `κ_D`, `T_H`, unit-area `r_h`, `log |S^{D−2}|` and its
increments, the ratio `√π Γ((D−1)/2)/Γ(D/2)`, and cumulative sums, against the first 200 zeros (comparison target
only). Unfolded to mean spacing 1, the zeros have `⟨r⟩ = 0.615` (GUE) with the GUE-like spacing histogram (few small
gaps, a broad peak). Every shell sequence is smooth: `⟨r⟩` between 0.89 and 1.00, spacings piled at 1 (picket fence).
The `T log T` thinning of the zero count is matched by `Σ log D` (`≈ log Γ`) and best by the arithmetic-free control
`k/log k`; this is a smooth-growth fact, reproducible by any sequence of that growth, and carries none of the
fluctuations of the zeros.

## Outer products in the limit (`OuterLimit`)

Proved (no `sorry`): a kernel `Σ_i w_i f_i(m) f_i(n)` with `w_i ≥ 0` has nonnegative form (`formG_outer_nonneg`),
positivity is closed under pointwise limits of kernels (`formG_nonneg_of_tendsto`), so if the prime-side Gram kernel is
a pointwise limit of such sums then RH (`rh_of_outer_limit`).

Numerics (uncertified, `scripts/positivity/outer_limit.py`). (a) In the log variable `m = 2^{k+u}`, `n = 2^{k+1+v}` the
dyadic junction is exactly scale invariant: `G/(4^k ln 2)` converges to the fixed kernel
`B_∞(u, v) = 2^u 2^{1+v} K_H(2^{1+v−u})` on `[0, 1]²`, with top singular values 0.0243, 0.0208, 0.0070, 0.0058, 0.0044,
0.0042 (relative error to the discrete blocks 4e−3 at `k = 6`, 3e−4 at `k = 11`; leading singular functions agree to
correlation 0.995). It is not an outer product: the leading term carries 51% and 4 terms reach 95%. This is why all the
earlier junction spectra were independent of size. (b) The limit of the whole tower is convolution by
`k(t) = K_H(e^{|t|})` on the log line. Its Fejér-windowed Fourier transform on `|t| ≤ log 10⁵` is nonnegative (minimum
7e−6) with peaks at 14.14, 21.01, 25.02, 30.42, 32.94, 37.59, 40.93, 43.32: the outer-product (Bochner) decomposition
`k(t − s) = ∫ (cos ξt cos ξs + sin ξt sin ξs) dμ(ξ)` exists numerically, and its measure sits at the zeros. Its
positivity for all `t` is Weil's criterion, so the manifestly positive outer-product structure in the limit is the zero
side, not a zero-free construction. (c) Averaged outer products of unit vectors of a block metric are `G⁻¹/d` (Monte
Carlo error 1% at `d = 32`): positive iff `G` is, nothing new.

## Arithmetic horizons (uncertified numerics, no Lean)

`scripts/positivity/arith_horizon.py` (results in `arith_horizon_results.txt`) treats closed geodesics on the modular surface PSL(2,Z)\H as BTZ-type horizons. All numbers are uncertified floating point; the Maass eigenvalues are quoted literature values, not recomputed.

- Primitive geodesics of trace t have length 2 arccosh(t/2) and norm N = ε² with N + 1/N = t² − 2. N is a quadratic irrational, so log N is never log p. The near-misses (e.g. t = 5, 7, 9, 13, 15) are only the statement that t² − 2 happens to be prime.
- The prime geodesic theorem is visible: #{N ≤ x}/Li(x) rises 0.76, 0.88, 0.975, 0.994 for x = 10², 10³, 10⁴, 9·10⁴. Multiplicities grow (mean 29, max 140 for t ≤ 300): the arithmetic degeneracy behind Poisson statistics.
- The first 20 Maass r_j show no alignment with the zeta zeros, and their spacings lean towards Poisson rather than GUE (small sample; the literature confirms Poisson on thousands of levels). The zeros' own spacings repel.
- As horizons (AdS radius 1): 2πr₊ = length and T_H = length/4π², giving a temperature tower ∝ 2 log t, not ∝ log p.
- Forcing lengths log p with Γ_p = ⟨diag(p^{1/2}, p^{−1/2})⟩ gives a discrete BTZ for each p, but p is put in by hand. The group generated by all Γ_p has translation lengths dense in ℝ (log p are rationally independent; |1054 log 2 − 665 log 3| ≈ 4·10⁻⁵), so it is not discrete and gives no quotient spacetime.

Conclusion: arithmetic horizons carry number theory (class numbers, Pell units, Hecke operators) but their spectrum is not ζ's. In this setting the primes reach ζ through Hecke eigenvalues of Maass forms, i.e. through L-functions, not through horizon lengths.

## Where the rational primes enter the modular surface (uncertified numerics, no Lean)

`scripts/positivity/prime_thread.py` (results in `prime_thread_results.txt`), floating point via mpmath, uncertified.

- **Class number formula.** For every fundamental D < 400 (where the Pell search finished), h⁺(D) log ε⁺(D) = √D L(1, χ_D) to about 10⁻¹⁵. Multiplicity × geodesic length is therefore √D ∏_p (1 − χ_D(p)/p)⁻¹: primes enter through how they split in ℚ(√D), not through lengths. Zagier's Dirichlet-series identity was not checked.
- **Frobenius mod p.** Reducing the 8704 primitive geodesics with trace ≤ 300 into SL(2, F_p) and sorting them by split / inert / t ≡ ±2 matches the SL(2, F_p) class proportions to within about 0.015 for p = 3, …, 13 (a Chebotarev-type equidistribution).
- **Hecke operators.** Not computed.
- **Scattering.** φ(s) = √π Γ(s − ½) ζ(2s − 1) / (Γ(s) ζ(2s)) has |φ(½ + it)| = 1 and poles at s = ρ/2, checked at the first five zeros. The modular surface's cusp resonances are exactly the Riemann zeros, halved. They all lie on Re s = ¼ iff RH, which is a restatement and not leverage, because the scattering problem is not self-adjoint.

## A leaky gravastar tower of truncated cusps (uncertified numerics, no Lean)

`scripts/positivity/leaky_tower.py` (results in `leaky_tower_results.txt`), uncertified.

- **One shell.** The modular cusp is cut at height Y (pseudo-Laplacian). The condition Y^{2s−1} = −φ(s) has only real solutions r on s = ½ + ir, spaced about π/log Y. They sit closer to γ_n/2 than chance (Y = 20: 0.08 against 0.26). That is the known phase-shift effect of the poles of φ at ρ/2, which sit a distance ¼ off the line: it reads off Im ρ once the zeros are known and says nothing about Re ρ. Roots seeded at ρ/2 drift with Y.
- **Tower.** K shells of length 1 are joined by lossless Fresnel steps whose impedances are the sphere areas A_d. The spectrum is real by construction. Distances to γ_n and γ_n/2 are at or above the random baseline (K = 10: 0.137 and 0.109 against 0.098), and random-phase junction controls behave the same.
- **Verdict.** Closing the leaks makes the tower self-adjoint, so it has a real cavity spectrum, but that spectrum is not the zeros. The zeros stay at the poles of φ, off the unitary line, and are neither moved onto it nor turned into eigenvalues. Losslessness gives no leverage on RH.

## Looking for the geometric glue (uncertified numerics, no Lean)

Known ways to turn the zeros into a spectrum, none of which is defined without ζ:
- Pavlov–Faddeev / Lax–Phillips: the zeros are the spectrum of the generator of a non-unitary semigroup, and RH ⇔ the poles lie on the line (Lax–Phillips, Bull. AMS 1980).
- Connes: the zeros as an absorption spectrum on the adele classes.
- Burnol: causal Lax–Phillips scattering.
- Berry–Keating, Sierra–Townsend, Bender–Brody–Müller: xp-type models with boundary conditions.
- Wu–Sprung: a fractal 1D potential fitted to the zeros.
- Lagarias: a de Branges space for ξ exists iff RH.

`scripts/positivity/debranges_glue.py` (results in `debranges_glue_results.txt`) builds the Jacobi chain (a discrete Krein string, i.e. a chain of 2×2 de Branges "shells") whose spectral measure has atoms at ±γ_n for the first 100 zeros. Circular by construction.
- With equal or Weil weights, the off-diagonals b_n match a GUE control with the same smooth density to within 4–7% over n ≤ 40. The smooth trend is fixed by the counting function N̄(T), i.e. by the Γ factor, and Poisson controls are only slightly rougher.
- The ζ chain is a little smoother than the controls (roughness 0.21 against 0.27, one control sample each), consistent with the rigidity of the zeros.
- No recognisable geometric pattern appears, nothing like the sphere-area ratios A_{d+1}/A_d.

Verdict: the glue that makes the zeros a self-adjoint spectrum exists (under RH), but it is read off from the zeros. No glue defined independently of ζ is known.

## Physics clues (literature, uncertified)

A short survey of established physics in which ζ, its zeros, or Weil positivity arise from geometry or physical consistency.

- **Kaluza–Klein and the Casimir effect.** Compact extra dimensions give Kaluza–Klein towers whose vacuum energies are regularised by Epstein zeta functions. The functional equation does the work, and there is no positivity statement (Hawking, CMP 55 (1977) 133; Elizalde, arXiv 1205.7032). Here a "slice" is literal: we see the zero mode of a higher-dimensional field.
- **2d CFT on SL(2,ℤ)\H.** Spectral decomposition of partition functions runs over the modular surface (Benjamin–Collier–Fitzpatrick–Maloney–Perlmutter, arXiv 2107.10744). For any U(1)^c CFT, a crossing equation for the scalar operators contains every ζ zero, and RH ⇔ a bound on the subleading density of scalar operators at high temperature (Benjamin–Chang, arXiv 2208.02259). Modular invariance plus unitarity gives positivity of densities, but that does not yet imply the bound.
- **Adelic strings.** The Veneziano amplitude times all its p-adic counterparts is a constant, which is equivalent to ζ's functional equation (Freund–Witten, PLB 199 (1987) 191). The real world appears as one place of an adelic whole, but this is a symmetry of ζ, not positivity.
- **Primon gas and Bost–Connes.** Z(β) = ζ(β) with a Hagedorn divergence at β = 1. Uncertified check: ⟨E⟩ = −ζ′/ζ(β) = 0.57, 9.44, 99.4 at β = 2, 1.1, 1.01, tracking 1/(β−1) (Julia; Spector, CMP 127 (1990) 239). Bost–Connes give the operator-algebra version, with symmetry breaking at β = 1 (Selecta 1 (1995) 411). Positivity of KMS states is established, but it concerns Re s > 1 only.
- **Weil positivity as compressed scaling.** At the archimedean place, Weil positivity is the positivity of a trace of the scaling action compressed onto Sonin space (Connes–Consani, arXiv 2006.13771). The prolate operator has negative eigenvalues whose ultraviolet behaviour matches the squares of the zeros (Connes–Moscovici, arXiv 2112.05500). This is the nearest thing to reflection positivity yielding Weil positivity, but only for one place.
- **Black-hole chaos and microstates.** The SYK spectral form factor shows a random-matrix ramp (Cotler et al., arXiv 1611.04650), a statistic shared with the zeros but with no mechanism linking the two. Black-hole microstate counting uses modular forms and Rademacher sums (Dijkgraaf–Maldacena–Moore–Verlinde, arXiv hep-th/0005003). Zeta values appear; the zeros do not.

Strongest clues for the "we see a slice" picture: (1) the modular bootstrap, where every 2d CFT's scalar spectrum contains the zeros and RH is a statement about physical operator densities; (2) Connes–Consani's archimedean Weil positivity from a compressed positive trace, which is positivity derived from a cut-off geometry and a projection. Bottom line: no established physical principle (unitarity, causality, reflection positivity, the second law) is known to imply full Weil or Li positivity; every route found reduces to RH-equivalent statements or to a single place.

## Same-dimension black-hole networks: Ramanujan graphs (uncertified numerics, no Lean)

`scripts/positivity/ramanujan_net.py` (results in `ramanujan_net_results.txt`) uses quotients of the Bruhat–Tits tree, the p-adic analogue of AdS, as a network of identical "black holes" (Lubotzky–Phillips–Sarnak, Combinatorica 1988; p-adic AdS/CFT: Gubser et al., arXiv 1605.01061; Heydeman–Marcolli–Saberi–Stoica, arXiv 1605.07639). Floating point, uncertified.

- **Single prime.** LPS X^{p,13} on PGL(2,13) has 2184 vertices. Max nontrivial |λ| is 4.250 (p = 5, bound 2√5 = 4.472), 7.851 (p = 17, bound 8.246) and 9.932 (p = 29, bound 10.770). All Ihara poles satisfy |u| = p^{−1/2} to 10⁻¹⁶, which is RH for the graph. A random 6-regular graph is only just Ramanujan (4.464).
- **Two primes on one quotient.** A₅ and A₁₇ commute exactly, and every joint eigenvector is Ramanujan at both primes. The product of local factors is the Satake/automorphic L-function picture. Ramanujan at every p is Ramanujan–Petersson, a theorem here (via Deligne), and it says nothing about ζ's zeros, which need the archimedean place.
- **Bad gluing.** Two copies of X^{5,13} are joined by k edge swaps (out of 6552 edges per copy, staying 6-regular). The margin 2√5 − λ is −1.53 at k = 1, −1.16 at k = 300 and −0.43 at k = 1000. A weak junction breaks RH and is recovered only once the junction is a large fraction of the graph.

Verdict: RH for these networks is a theorem, and it comes from arithmetic gluing (quaternion/Hecke structure), not from regularity: generic junctions fail it. That matches the junction-margin story, but it is the finite-place analogue, and it does not reach ζ.

## Ramanujan networks in the limit (uncertified numerics, no Lean)

`scripts/positivity/ramanujan_limit.py` (results in `ramanujan_limit_results.txt`), floating point and exact integer walk counts, uncertified.

- **Size limit (q → ∞, p = 5).** The closed-walk moments tr(Aᵏ)/n of X^{5,q} match the 6-regular tree's (Kesten–McKay: 6, 66, 876, 12786, …) up to k = 8, 8, 9, 10, 9 for q = 13, 17, 29, 37, 41, and the k = 10 moment approaches the tree's value (231156 → 197922 against 197796). The spectral measure converges weakly to Kesten–McKay.
- **Hecke angles (11a, 3243 primes < 30000).** No Hasse/Ramanujan violations. The moments of 2cos θ_p are 0.993, 1.973, 4.911 against Sato–Tate 1, 2, 5. Rescaled Kesten–McKay tends to Sato–Tate as p → ∞.
- **Zeros need the archimedean place.** Using the completed Λ = (√11/2π)^s Γ(s) L(11a, s), the zeros on Re s = 1 below t = 20 are 6.3626, 8.6035, 10.0355, … (first zero matches LMFDB). Ramanujan at every finite p does not locate zeros: the Davenport–Heilbronn function (period-5 coefficients with |a_n| ≤ 1, a Riemann-type functional equation, no Euler product) has a zero at 0.8085171825 + 85.6993485i, matching Spira and Balanzario–Sánchez-Ortiz (Math. Comp. 2007).
- **Archimedean limit.** No p → ∞ limit of the trees yields the hyperbolic plane. The object that combines all the trees with H is the adelic quotient GL₂(ℚ)\GL₂(𝔸)/K, whose continuous spectrum is the Eisenstein series, with ζ(2s) in the constant term. That brings us back to the modular-surface cusp, where the zeros are scattering poles.

## Closing the cusp as a Möbius loop (uncertified numerics, no Lean)

`scripts/positivity/mobius_cusp.py` (results in `mobius_cusp_results.txt`), uncertified. With v = y^{−1/2} u = e^{irx} + φ e^{−irx}:

- **Periodic closure.** e^{irL} = 1, and φ drops out entirely.
- **Möbius closure.** The identification y → Y²/y with sign ε gives φ(s) = ε Y^{2s−1}, the pseudo-Laplacian condition. Twisted closures give φ(s) = e^{iα} Y^{2s−1}. For Y ≥ 2 all modes are real (s on Re = ½).
- **Distances to γ_n/2.** At Y = 1000 they are 0.064 (ε = +1), 0.079 (ε = −1) and 0.072 (random twist), against chance 0.114. Möbius and random twists are alike; this is the known phase shift of φ near its poles.
- **Can the zeros be modes?** φ(s) = c with c finite never holds at ζ(2s) = 0, because φ has a pole there. Roots converge to ρ/2 only as Y → 0 (distance 0.047 at Y = 0.01 and about 0.014–0.022 at 10⁻³, roughly like Y^{1/2}), where the cut lies below the cusp and the closure is no longer self-adjoint (roots move off the line).

Verdict: orientation reversal mirrors s ↔ 1 − s, but it only reproduces the pseudo-Laplacian. The zeros are reached only in a degenerate, non-self-adjoint limit.

## Doubling the cusp: an indefinite metric and its negative squares (`KreinNeutral`, plus uncertified numerics)

**Lean (`KreinNeutral`, standard axioms only).** If `A` is self-adjoint for an indefinite form `[x, y] = ⟪Jx, y⟫` and `Av = μv` with μ non-real, then `[v, v] = 0` (`neutral_of_nonreal`). With a definite form the spectrum is therefore real (`im_eq_zero_of_pos`). The Pontryagin bound (at most κ non-real pairs when the form has κ negative squares) is not formalised.

**Literature.**
- Weil's quadratic functional is positive semidefinite iff RH. If only finitely many zeros are off the line, large enough truncations have exactly half that many negative eigenvalues (Bombieri, Rend. Lincei 2000; Yoshida 1992 for small supports).
- Pontryagin de Branges spaces: a Hermite–Biehler-type E whose kernel has finitely many negative squares (Kaltenbäck–Woracek).

**Numerics (`scripts/positivity/krein_detector.py`, results in `krein_detector_results.txt`).** The truncated Weil form uses 60 zeros and a Gaussian basis.
- With the true zeros: 0 negative squares.
- Injected synthetic off-line quadruples: with a basis symmetric in ±γ, 2 and 4 negative squares for 4 and 8 off-line zeros, exactly half as Bombieri predicts. A one-sided basis sees one per quadruple. Even δ = 0.01 is detected.

Verdict: the doubled, indefinite-metric picture is an exact detector, with κ equal to half the number of off-line zeros. The form is built from the zeros, though, and its prime-side version (the explicit formula) gives no geometric reason for κ = 0. "RH ⇔ κ = 0" is Weil's criterion restated.

## Weil's finite-field proof: Hodge index ⇒ Weil bound (`WeilHodge`, plus uncertified numerics)

**Lean (`WeilHodge`, standard axioms only).**
- `hodge_cs`: if the intersection form is negative semidefinite on H^⊥ with H·H > 0, then D·D · H·H ≤ (D·H)².
- `castelnuovo`: with fibre classes e₁, e₂ and H = e₁ + e₂, D·D ≤ 2(D·e₁)(D·e₂).
- `weil_bound_sq`, `weil_bound_of_hodge`: given the intersection numbers of the diagonal Δ and the Frobenius graph Γ on C × C, (N − q − 1)² ≤ 4g²q and |N − (q + 1)| ≤ 2g√q.

The intersection numbers and the Hodge index property are hypotheses. Applied to every Frobenius power, the bound gives |α| = √q.

**Numerics (`scripts/positivity/weil_hodge.py`, results in `weil_hodge_results.txt`; point counts exact, eigenvalues floating point).** For y² = x³ + x + 1 (q = 23, 101), y² = x³ − x (q = 29, 103) and the genus-2 curve y² = x⁵ + x + 3 (q = 13, 31):
- the Gram matrix of ⟨e₁, e₂, Δ, Γ⟩ has signature (1, 3), exactly one positive direction;
- N and the count over F_{q²} satisfy the Weil bounds;
- every Frobenius eigenvalue has |α|/√q = 1.000000. The supersingular case q = 103 meets the F² bound with equality.

**Spec ℤ.** The analogue of the Gram matrix is our BallWeil form: e₁, e₂ ↔ the pole plane, Δ·Γ ↔ the prime side of the explicit formula, the Frobenius graph ↔ the scaling action (Connes–Consani). What is missing:
1. An intersection theory on "Spec ℤ × Spec ℤ" for which the scaling graphs are classes. Arakelov theory covers Spec ℤ alone, and Connes–Consani's Riemann–Roch for Spec ℤ (arXiv 2205.01391) is one-dimensional.
2. Finiteness: the genus is infinite (infinitely many zeros), so the classes live in an infinite-dimensional space where Hodge index is a positivity statement, not a finite signature count.
3. The Hodge index property itself. Over ℤ, "exactly one positive direction" is our `DeSitterTower.rh_iff_deSitter` / BallWeil signature statement, which is RH (Weil positivity). Over F_q it is a theorem about surfaces; over ℤ it is the thing to prove.

`WeilHodge` makes precise that only this last input is missing: given Hodge index, the rest is elementary.

## Weil positivity place by place (uncertified numerics, no Lean)

`scripts/positivity/place_margin.py` (results in `place_margin_results.txt`). The Weil form is restricted to test functions supported in [−L, L] on the log scale (40 sine modes) and orthogonal to the two pole functionals. Prime powers n enter as 2L passes log n. The explicit formula agrees with a 300-zero spectral sum to relative 10⁻⁵. Uncertified.

- **Archimedean place alone** (exact for 2L < log 2): margin 1.80, 1.11, 0.70 at L = 0.1, 0.2, 0.3. It stays positive until L ≈ 0.6, then turns negative (−0.53 at L = 1, −2.07 at L = 3). The archimedean term alone is not positive for larger supports.
- **Primes entering.** p = 2 enters at L = 0.35: the margin is 0.41 arch-only against 0.24 with the prime at L = 0.4, and 0.19 against 0.014 at L = 0.5. From L ≈ 0.7 on, the full margin sits at the discretisation noise floor (|m| < 4·10⁻⁷ up to L = 3, 98 prime powers). The true margin is ≥ 0 but tends to 0, because the prime terms cancel the archimedean deficit almost exactly. No per-prime drop law is visible: the cancellation is collective.
- **Detector.** Moving γ₁ to γ₁ ± iδ makes the margin clearly negative from L ≈ 0.75. At L = 2 the margin is −0.49, −0.050 and −0.0043 for δ = 0.3, 0.1 and 0.03, far above the noise floor.

Verdict: consistent with RH on every support tested, not a proof. Positivity is not built up place by place. Beyond the smallest supports the archimedean term is negative, and the primes restore positivity only collectively, to within 10⁻⁷ of zero. That is the explicit-formula cancellation, with no monotone per-prime mechanism.

## Sonin slice: Connes–Consani archimedean positivity in the place-by-place setup (uncertified)

**What is proved** (Connes–Consani, "Weil positivity and trace formula, the archimedean place", arXiv:2006.13771, https://arxiv.org/abs/2006.13771):
- Theorem 1: for g smooth, supported in [2^{-1/2}, 2^{1/2}] (log half-width log2/2 ≈ 0.3466), with ĝ(±i/2)=0 and ĝ(0)=0: W_∞(g∗g*) ≥ Tr(ϑ(g) S ϑ(g)*) ≥ 0, where S projects onto the Sonin space (even functions vanishing with their Fourier transform on [−1,1]). Theorem 11 relaxes ĝ(0)=0 at a cost of c|ĝ(0)|², with 13<c<17.
- Theorems 3/7: Tr(ϑ(f)S) = W_∞(f) + E(f) for all f, where ε(ρ) is a sum over the prolate eigenfunctions (c=2π). So the Sonin trace is positive for every support; only the archimedean place is involved, and no prime terms appear.
- Theorem 6, Corollary 8 and Remark 9 give the D∘Q bounds (≤0 up to u≈1.15; fails on [1/2,2]).
- Connes–Moscovici, arXiv:2112.05500 (https://arxiv.org/abs/2112.05500), give the spectral realisation of the UV prolate operator. It does not prove positivity of the semilocal Weil form.

**Numerics** (`scripts/positivity/sonin_prolate.py`, `sonin_slice.py`, results in `sonin_slice_results.txt`; float64, not certified):
- Reproduced the paper's values: prolate eigenvalues 0.999971, −0.979485, 0.524086, −0.058977, 0.002732; Σλ² = 2.237484835; ε′(1⁺) ≈ 22.993 (paper 22.9965).
- On the constrained subspace (ĝ(±i/2)=ĝ(0)=0):
  - S = W_∞+E stays ≥ 0 at every L tested, down to −4e−5 at L=1.5, which is at quadrature level.
  - −E = W_∞−S is ≥ 0 up to L≈0.6, beyond the proven 0.3466. It is negative by L=0.8.
- The prime terms are a different matter. W−S = −E − primes turns negative the moment 2 enters: +1.4e−3 → −2.1e−2 across L=log2/2. After that it is O(1) negative (−0.48 at L=0.4, −1.9 at L≈1.3). Meanwhile the full Weil form W sits at the noise floor (≤5e−8 in magnitude), as in the place-by-place section.
- Not done this round: the synthetic off-line zero injection. The run budget was used by the E-matrix build.

**Verdict.** The Sonin trace absorbs the archimedean place exactly, and its positivity is a theorem. But it is not a lower bound that survives the primes: the margin it leaves (−E) is about 1e−3, while the prime 2 alone costs about 2e−2. Any route via "W ≥ Sonin trace" would need a semilocal Sonin space that includes the finite places. That is the open step in Connes–Consani's programme, and these numerics give no shortcut to it.

## A slice through the junction (uncertified)

Scripts are in `scripts/positivity/`: `junction_slice.py` and `junction_shell.py`, with results in `junction_slice_results.txt` and `junction_shell_results.txt`. Everything is float64 and uncertified.

**Junction slice.** As the support grows from L− = log(n)/2 − d to L+ = log(n)/2 + d, the orthogonal complement of L²[−L−,L−] inside L²[−L+,L+] is exactly the space of functions supported in the shell L− < |x| < L+.
- A first attempt worked in the 40-mode sine basis (`junction_slice.py`). There the two spans coincide numerically, the complement is empty, and the measured "drop" is 1e−15. This is a basis artefact, not a result.
- Done exactly with 10 sines per strip, on the pole-orthogonal shell:
  - Earlier primes do not act on the shell, so W without n equals the archimedean term: about 2.04 at d = 0.05 and about 2.97 at d = 0.02.
  - The entering prime power costs exactly Λ(n)/√n: 0.484 (n=2), 0.631 (3), 0.345 (4), 0.718 (5), 0.734 (7), 0.245 (8), 0.366 (9), 0.722 (11), 0.711 (13).
  - The margin on the shell stays at least 1.3. The archimedean slack grows as the shell narrows, but the prime cost does not.
- So the new directions are never where negativity enters. Any loss of positivity lives in how the shell couples to the old interior, and that coupling is what the 40-mode results above put at the noise floor.

**Semilocal slice (scoped partial).** The semilocal Sonin projector, with its p-adic cutoff and semilocal Fourier transform (Connes, Selecta Math. 1999, https://arxiv.org/abs/math/9811068; Connes–Consani, https://arxiv.org/abs/2006.13771), was **not** built. Instead I took the S-truncated Weil form W_S = W_∞ − (terms of the primes in S) and compared its smallest eigenvalue on the pole-orthogonal subspace ("slack") with the largest eigenvalue of the prime terms outside S ("cost"):
- At L = 0.6, W_{∞,2,3} has slack +8e−5, and its outside cost is 0 because 5 has not yet entered.
- In every other case tested (L from 0.6 to 1.5, S = {∞,2} and {∞,2,3}) the slack is negative, from −0.04 to −1.0, while the outside cost is 0.6 to 2.0.
- So truncating S destroys positivity rather than leaving slack. Positivity of W comes from cancellation across all primes, not from S-local slack absorbing the remaining primes.

**Verdict.** No inductive mechanism appears in either slice:
- Junction directions are robustly positive. The archimedean slack of about 2 exceeds each single cost Λ(n)/√n, but those slices are not where W gets tight.
- S-truncated forms are not positive once L is past the first prime outside S, so there is no slack to spend.
A true semilocal Sonin trace might behave differently. That question remains open here.

## Shell–interior Schur test (uncertified)

**Lean (`lib/core/ShellSchur.lean`).** These are abstract lemmas, sorry-free and using only the standard axioms:
- `ShellSchur.nonneg_of_coupling`: if A ≥ a s, C ≥ c t, B² ≤ b² s t and b² ≤ ac, then A + 2B + C ≥ 0.
- `ShellSchur.margin_of_coupling`: if b² ≤ (a−m)(c−m), the glued form keeps margin m.
- `ShellSchur.chain_nonneg`: over a finite chain of shells, if every step satisfies the margin condition then every form in the chain is ≥ 0.

Nothing in these lemmas asserts that the Weil form meets the hypotheses.

**Numerics** (`scripts/positivity/shell_schur.py`, results in `shell_schur_results.txt`; float64, uncertified):
- Setup: at each prime-power entry n ≤ 49, with d = 0.02, the interior is |x| < L− (40 sines) and the shell is L− < |x| < L+ (10 sines per strip), on the pole-orthogonal subspace.
- Quadrature check: a first run with coarser quadrature gave spurious whole-form values down to −0.3. With finer quadrature the whole form sits at the noise floor (|min| ≤ 4e−5, growing with n).

| n | a (interior) | c (shell) | b = ‖B‖ | b²/(ac) | exact Schur | Λ(n)/√n |
|---|---|---|---|---|---|---|
| 2 | 0.615 | 1.37 | 0.61 | 0.43 | +1.11 | 0.49 |
| 3 | 3.2e−3 | 1.24 | 0.70 | 123 | +0.75 | 0.63 |
| 4 | 5.9e−7 | 1.53 | 0.89 | 8.8e5 | +0.66 | 0.35 |
| 5–49 | noise (−1e−6 … −7e−10) | 1.17–1.78 | 0.91–1.36 | — | undefined (A not > 0) | 0.12–0.74 |

- Synthetic off-line zero at γ = 14.13: it shows up in the **interior** block, not in the junction. For δ = 0.3 / 0.1, a = −0.087 / −0.009 at n = 7, a = −0.23 / −0.023 at n = 13 and a = −0.46 / −0.047 at n = 23. The shell block c stays at about 1.2–1.4.

**Verdict.** The inductive Schur condition b² ≤ ac holds only at n = 2. It fails from n = 3 onwards.
- The coupling norm b stays O(1). It is about 0.6–1.4, does not follow Λ(n)/√n, and grows slowly with L.
- The interior margin a collapses to the noise floor once L ≳ 0.7. That is the known behaviour of the Weil form, whose infimum on growing supports tends to 0.
- So there is no room to absorb the coupling. The exact Schur complement is positive while it is defined (n ≤ 4), but past that point it is undefined.

Any proof along these lines would need control of B relative to the *near-null directions of A*, not a norm bound. Those near-null directions are exactly where an off-line zero would appear.

## Near-null directions of the Weil form (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

`scripts/positivity/near_null.py` (results in `near_null_results.txt`, plot `near_null.png`) uses the 40-sine basis on [−L,L], restricted to the 38-dimensional pole-orthogonal subspace. All values are float64 and uncertified.

**Setup check.** On this subspace W equals the zero-side form Z = 2Σ_γ|f̂(γ)|² over the first 600 zeros, to a relative error of about 1e−5 at every L tested.

**Near-null dimension against a zero count.** Here K = 40π/(2L) is the basis bandwidth and N(K) is the number of zeros below K. Each zero below K kills two real dimensions.

| L | #eig < 1e−3 | #eig < 1e−6 | N(K) | 38 − 2N(K) |
|---|---|---|---|---|
| 0.7 | 2 | 1 | 25 | — |
| 1.0 | 9 | 7 | 14 | 10 |
| 1.5 | 20 | 18 | 7 | 24 |
| 2.0 | 26 | 24 | 4 | 30 |
| 3.0 | 32 | 29 | 1 | 36 |

The near-null dimension is roughly 38 − 2N(K) − (2 to 4). The shortfall comes from the tails of zeros above K.

**What the near-null directions are.** They are the functions whose transforms vanish at the low zeros. For the bottom eigenvector:
- At L = 1, max|f̂(γ₁…γ₁₀)| = 1.5e−7, against max|f̂| = 0.78. The zero sum is 9.0e−10, against an eigenvalue of −9.7e−10.
- At L = 2, max|f̂(γ₁…γ₁₀)| = 2.9e−5, against max|f̂| = 0.61.
- In other words, |f̂|² carries O(1) energy between the zeros and has notches at them.

**Shape test.** There is no fixed profile:
- Overlaps of the bottom eigenvector with its rescaling to the next L are 0.18, 0.39, 0.16 and 0.28.
- The best overlap with an even or odd prolate function ξ_n(|x|/L) falls from 0.79 (L = 0.7) to 0.24 (L = 3).

**GUE control.** I replaced the zeros with 600 GUE-spaced fake ordinates of the same smooth density. The near-null counts are almost the same: 7 / 25 / 31 below 1e−3 at L = 1 / 2 / 3, against 9 / 26 / 32 for the real zeros.

**Verdict.** The near-null space is the interpolation kernel {f supported in [−L,L] : f̂(γ) ≈ 0 at the zeros below the bandwidth}. Its dimension is set by Paley–Wiener degrees of freedom minus 2N(T). Its shape depends on where the zeros sit and on the basis truncation, not on a universal profile, and it looks the same for GUE fake zeros. So the near-null directions encode the zeros themselves rather than a separate structured object. Positivity on them is equivalent to the zero-side statement. I found nothing intrinsic here to prove things about independently of the zeros.

## Sum-of-squares certificates from local data (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Script: `scripts/positivity/sos.py`, output `sos_results.txt`, plot `sos.png`. The setup is the same truncated Weil form as the near-null study: pole-orthogonal test functions, support [-L,L], a 40-sine basis, and float64 numerics with Clarabel SDP. We looked for a certificate W − tI = (PSD) built only from archimedean and prime-side pieces, then maximised the slack t.

- **C0, unstructured:** t = min eig, which is about 0 (|t| ≲ 1e-7) for every L in 0.7–2.5. This is plain eigen-decomposition.
- **C1, per-prime scalar shares of the archimedean form:** infeasible for every L. The archimedean form on its own isn't positive definite.
- **C2, per-prime local (AM–GM-type) domination:** each shift term P_n is bounded by a position-bin multiplier D_n, and arch − ΣD_n − tI must be PSD. The best slack is t = −0.94, −2.36, −5.37, −9.72, −15.9 at L = 0.7, 1, 1.5, 2, 2.5. That is roughly quadratic growth in L as the prime-power count rises from 3 to 47.
- **C3, C2 plus per-prime archimedean shares:** t = −0.35, −1.53, −4.35, −8.54, −14.7.
- **Certificate structure:** the multipliers are dense, with almost all bins active. Their singular values decay slowly (1, 0.43, 0.25, 0.17, …), so there is no low-rank shared profile.
- **Controls:** we jittered log n (σ = 0.02–0.1) or flipped the signs of p = 3 or p = 5, 7 (Davenport–Heilbronn style). The true min eig breaks to between −0.5 and −3.2, but the C3 slack barely moves (−8.35 to −8.59 against −8.54 for the real primes). Local certificates can't tell real primes from fake ones.

Verdict: positivity of the Weil form can't be certified place by place, even with generous local multipliers. The gap grows with L, and the only certificate that works is the global eigen-decomposition, which is Weil positivity restated. This agrees with the near-null study: the cancellation is collective, across primes and the archimedean place together. No new Lean lemma was added. "A sum of PSD forms is PSD" is already covered in spirit by the ShellSchur chain lemma. Numerics by Grok Bot.

## Monotone flow in L (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Script: `scripts/positivity/flow.py`, output `flow_results.txt`, plot `flow.png`. The setup is the same Weil form W_L as before: pole-orthogonal test functions supported in [-L,L], a 40-sine basis, float64. The grid runs over L = 0.3–3.0 in steps of 0.05.

- **Exact monotonicity, no numerics:** the test spaces are nested in L, so the true λ_min(L) is non-increasing. A flow can only lose positivity as L grows, never gain it. "Positive for all L" is the same as "positive in the limit", which is RH, so propagating from small L can't work. The 40-mode basis isn't exactly nested, and the largest spurious increase was 1.7e-7, which is at noise level.
- **Collapse:**
  - λ_min falls 0.70 → 0.24 → 1.4e-2 → 8e-5 → 7e-8 at L = 0.3, 0.4, 0.5, 0.6, 0.7.
  - From L ≈ 0.8 on, it sits at 0 within float noise (between −4e-7 and +1e-9).
  - The next eigenvalues follow one after another. From L ≈ 1 on, λ_1..λ_4 are all ≲ 1e-8.
  - The Hadamard boundary term, the edge slope of the bottom eigenvector, drops from about 100 to about 0.3. Its finite-difference dλ/dL is ≤ 0 up to noise.
- **Prime-power entries:** a new log n = 2L enters continuously. The overlap starts at zero support, so there is no jump, only a change in slope. Below L ≈ 0.8 the entries at n = 2, 3, 4 coincide with the steepest stretch of the descent. Above it, nothing can be resolved because everything is near-null.
- **Riccati-type propagation:** there is no gap left to propagate. For L ≳ 0.8 the flow is degenerate, with several eigenvalues near 0, so a Hellmann–Feynman or Riccati ODE has nothing to protect. Its sign at the boundary is exactly the unknown.
- **Fake-prime control:**
  - With log n jittered (σ = 0.05), λ_min < −1e-4 first at L = 0.5. Its minimum over the grid is −3.6.
  - With the sign of p = 3 flipped, it first breaks at L = 0.6. Its minimum over the grid is −2.3.
  - Real primes instead approach zero from above and stay pinned at it.
  - The flows separate exactly where the real flow enters the near-null regime. That is the same information as the zero-side vanishing found in the near-null study.

Verdict: the flow runs the wrong way. Monotonicity is exact but goes downward, and λ_min is pinned at zero from L ≈ 0.8 on, so it gives nothing beyond Weil positivity restated. No Lean lemma was added. Downward propagation along nested spaces is trivial, and the upward version would need the missing boundary sign, which is RH. Numerics by Grok Bot.

## Symmetry splitting (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Script: `scripts/positivity/ideas256.py`, output `ideas256_results.txt`, plot `ideas256.png`. The setup is the same W_L as before: support [-L,L], a 40-sine basis, float64. Controls: log n jittered (σ = 0.05) and the sign of p = 3 flipped.

- **Parity:** W_L commutes with x → −x, with a cross-block norm of about 1e-6 (quadrature level). Each block takes its own pole constraint (e^{x/2} ± e^{−x/2}).
  - With the real primes, both blocks are positive at small L: min eig 1.4e-2 even / 0.21 odd at L = 0.5.
  - Both collapse to 0 together. Even and odd reach 7e-8 and 8e-6 at L = 0.7, then sit at noise level from L ≈ 1 on.
  - The near-null dimension splits evenly between the blocks (4/3, 9/9, 12/12, 14/13), so neither block carries the near-null directions.
  - With the controls, both blocks fail at the same rate, about −0.5 to −2.8.
- **Dirichlet twists (χ mod 3, 4, 5, 8; no pole):** every twisted form behaves the same way. It is positive at small L, collapses to 0 at roughly the L where the first zero of L(s,χ) comes into resolution, and from then on its near-null dimension grows like the twisted zero count. With a flipped prime, each fails at −0.25 to −2.2.

Verdict: splitting gives smaller copies of the same problem. No block can be certified on its own while the controls fail.

## Reweighted metric (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Same script. We computed c(L) = min of W/M on the pole-orthogonal space for M_w = ∫|f̂|² w(t), with w = 1, (1+t²)^{−1}, (1+t²)^{−2}, a Gaussian e^{−(t/10)²}, log(2+t), and a "zero-dip" weight that vanishes at the first 10 zeros.

- For every weight that is positive at the zeros, c(L) is about 0 (within noise) from L ≈ 1 on. The smoother weights only rescale the noise.
- With the jittered control, the same metrics give large negative c (down to −1e6 for H^{−2}).
- The zero-dip weight doesn't help either: c is still 0. Removing the first 10 zeros isn't enough, because there are more near-null directions than that.
- Any M that keeps c > 0 has to vanish on f̂ at every zero below the bandwidth. That metric is the zero-side form itself, so the argument is circular.

## GUE bridge (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Same script. We compared the zero-side form 2Σ|f̂(γ)|² (600 ordinates) for the real zeros against 40 GUE fake-zero sets, all unfolded to the same smooth density.

- **Near-null dimension:** at L = 1, real 7 against a GUE mean of 7.0 ± 0.8. At L = 2, real 24 against 23.5 ± 1.1.
- **Eigenvalue percentiles:** the log-eigenvalue percentiles of the real zeros fall between 35% and 78% of the GUE spread. The lowest eigenvalues sit at the 1e-18 float floor for both, so those comparisons carry no information.
- **Verdict:** the real configuration is typical of GUE on every statistic tested. Any real zero set gives a positive zero-side form, so positivity carries no information here. There is no atypicality to exploit.

Overall: all three ideas reduce to Weil positivity restated. No Lean lemma was added, because "block-diagonal with nonnegative blocks implies nonnegative" is trivial. Numerics by Grok Bot.

## Entropy routes (uncertified)

> **Correction (high-precision rerun, see "High-precision Weil spectrum" below).** The float64 values reported here as "≈ 0", "near-null" or "pinned at zero" for L ≳ 0.7 were below float64 resolution. In the mpmath rerun the true minimum is positive and falls double-exponentially (5.0e-13 at L = 0.7, 2.3e-17 at 0.8, 8e-30 at 1.0, 9.9e-49 at 1.2). Counts of eigenvalues "< 1e-6" mostly measured that floor. Qualitative conclusions that compare real primes with controls are unaffected, because the controls fail at O(1).

Script: `scripts/positivity/entropy.py`, output `entropy_results.txt`, plot `entropy.png`. The setup is the same W_L as before. Controls: log n jittered (σ = 0.05) and the sign of p = 3 flipped. Fourier convention: f̂(t) = ∫f e^{−itx}, with density |f̂|²/(2π‖f‖²). In this convention the Hirschman–Beckner bound is H(|f|²) + H(|f̂|²) ≥ log(πe) ≈ 2.145.

- **Entropic uncertainty:** every vector tested satisfies the bound, with entropy sums of 3.0–4.3 for real primes and controls alike.
  - The real near-null vectors put only 0.04% (L = 1) and 0.09% (L = 2) of the mass of |f̂|² within 0.25 of a zero. Those windows cover 25% of [0, 400].
  - The sign-flip control's bottom vector also hides its mass (0.01–0.06%), yet has eigenvalue −1.3 to −2.0.
  - So low dip mass doesn't imply positivity. The entropy bound only says |f̂|² is spread out, and a function of exponential type can vanish at roughly N(K) prescribed points at no entropy cost. No entropic lower bound on W_L follows.
- **Von Neumann entropy of W₊/Tr W₊:**
  - For real primes it falls from 3.58 to 1.34 over L = 0.4–3, as the near-null directions drop out of the effective rank.
  - The controls stay higher: 2.55 (jitter) and 2.76 (flip) at L = 3.
  - The negative-mass ratio Tr W₋/Tr|W| is ≲ 2e-8 for real primes against 0.37–0.39 for the controls. That detects failure, but it is just the eigenvalue sign again.
  - No data-processing monotonicity is available: restricting to a subspace is a compression, not a quantum channel acting on a fixed state, and S isn't monotone in any useful direction.
- **Bost–Connes:**
  - Z(β) = ζ(β), energy E = −ζ′/ζ, S = log Z + βE. Both diverge as β → 1⁺ (E = 99.4 and S = 105 at β = 1.01). This is the pole that drives the KMS phase transition.
  - No positivity statement in the complex-β plane is known to be equivalent to RH beyond the explicit formula itself.
  - Lee–Yang circle theorems need ferromagnetic pair interactions, and no such structure is known for this system.
- **de Bruijn–Newman heat flow:**
  - H_t is computed by quadrature over u ∈ [0, 1.2]. At t = 0, its zeros divided by 2 match γ to 2e-9.
  - All 8 zeros below 90 stay real for t ∈ [−0.2, 0.2] and drift steadily, with dz/dt ≈ −0.5 to −1.
  - The ODE dz_k/dt = 2Σ1/(z_k − z_j), truncated to the computed zeros, doesn't reproduce the drift, because the far zeros dominate.
  - The near-null dimension at L = 2 stays at 24 for every t. The near-null structure depends only on the zero count, not on reality, so the heat flow doesn't interact with it.
- **Literature:** RH ⇔ Λ ≤ 0. Rodgers and Tao proved Λ ≥ 0 (Forum Math. Pi 2020, arXiv 2018), so RH ⇔ Λ = 0. Λ = 0 itself is *not* known. Polymath15 proved Λ ≤ 0.22 and Platt–Trudgian improved it to Λ ≤ 0.2. Bost–Connes is from Selecta Math. 1995; that citation is from memory and wasn't rechecked.
- **Prime and Liouville entropy:** up to N = 10⁶, the block entropy of the Liouville function is indistinguishable from a random ±1 sequence, with deficits of 3.0e-3 against 3.1e-3 bits at block length 12. max|M(x)|/√x on [10³, 10⁶] is 0.47. RH ⇔ M(x) = O(x^{1/2+ε}) is the known equivalence. Entropy at this scale is a weaker statistic than M(x) itself and adds nothing.

Verdict: none of the entropy routes adds anything beyond Weil positivity or a known RH equivalence. No Lean lemma was added. Numerics by Grok Bot.

## Literature context

Conventions: f is supported in [−L, L] in log scale, so f∗f̃ has support [−2L, 2L] and prime powers with log n < 2L enter. This is the same as our W_L. Literature survey compiled by Grok Bot; citations checked online except where marked.

- **Weil (1952), "Sur les formules explicites…":** RH ⇔ the quadratic form is positive. Cited via Bombieri; the original wasn't rechecked.
- **Yoshida (1992), Adv. Stud. Pure Math. 21, 281–325:** positivity for small support, verified at 2L = log 2, i.e. L ≤ 0.347. At L ≤ 0.347 no prime enters at all, so the result is archimedean only.
- **Bombieri (2000), Rend. Lincei Mat. Appl. 11, 183–233:** the minimum is attained, Yoshida is reproved, and the number of negative eigenvalues equals half the number of off-line zeros. He calls the functional "as intractable as RH itself".
- **Connes (1999), Selecta Math. 5, 29–106:** trace formula. **Connes–Consani (2021), Selecta Math. 27, arXiv 2006.13771:** archimedean positivity via the Sonin trace, at the same support log 2 / 2. **Connes–Consani (2023), Enseign. Math. 69, arXiv 2106.01715:** the very small eigenvalues of the Weil form come from prolate functions. **Connes–Consani–Moscovici (2024), Ann. Funct. Anal., arXiv 2310.18423.** **Connes–van Suijlekom (2025), CMP, arXiv 2511.23257:** a simple, even, isolated ground state implies its transform has only real zeros. **Connes–Consani–Moscovici, "Zeta spectral triples", arXiv 2511.22755:** convergence as λ → ∞ would give RH. The open steps are a simple even ground state at every scale, and convergence.
- **Li (1997), JNT 65, 325–333; Bombieri–Lagarias (1999), JNT 77, 274–287:** Li coefficients, which are again Weil positivity. **de Branges:** Conrey–Li (arXiv math/9812166) showed his positivity condition fails for ζ. **Suzuki:** screw functions, JLMS 2023 and arXiv 2606.09096. **Groskin, arXiv 2607.02828:** an "inconclusive band" for truncated forms. **Burnol:** not checked.
- **Zhu, arXiv 2608.24827 (2026 preprint, not refereed):** uses exactly our convention.
  - Certified Q ≥ 8.9e-18‖f‖² for L ≤ 0.8. The true floor at L = 0.8 is about 1.7e-17.
  - Measured law: −ln λ*(L) ≈ 2π² N(T*)/ln N(T*), with T* = 2πe^{2L}. This is double-exponential decay.
  - Barrier: pointwise-envelope certificates need resolution up to T₁ = 2πe^{A_L}, which grows doubly exponentially. To go further one has to show that the phases t·log p cannot align.
  - Float64 gives spurious negative eigenvalues.

How this lines up with our results:

- **Our "collapse at L ≈ 0.8" is not a threshold.** It is the float64 floor: the true λ_min goes below 1e-16 near L ≈ 0.8. Our "λ ≈ 0" readings for L ≳ 0.8 are noise around a positive but tiny value. Our numbers are also on the pole-orthogonal subspace with only 40 modes, so they aren't converged (for example 6.8e-8 against Zhu's 5e-13 at L = 0.7).
- **Our near-null directions are the Landau–Widom suppression:** f̂ vanishes at the zeros below T* (at L = 0.8, the 4 zeros below 31.1). Each extra zero costs a double-exponentially small factor in λ.
- **Our negative certificate results** (no local or SOS certificate, no reweighted metric) agree with Zhu's barrier theorem.
- **Parity:** Zhu certifies that the ground state is even, with the odd sector about 10³ times higher at L = 0.8. Our float64 parity split couldn't resolve that difference.
- **Open handle the literature points to:** cancellation in the prime comb, i.e. that the phases t·log p cannot all align. That is an arithmetic, Diophantine statement. A second handle is the Connes–van Suijlekom route: prove a simple, even ground state at every scale.

## High-precision Weil spectrum (mpmath, not interval-certified)

Scripts: `scripts/positivity/hpcore.py` and `hp1_run.py`; plot `hp1.png`. The convention is exactly Zhu's (arXiv 2608.24827, eq. 17):
- f is supported in [−L, L], and g = f∗f̃;
- the archimedean term is in exact time-domain form, and the prime sum has log n < 2L;
- the pole term is included, +2(∫f cosh)² for even f and −2(∫f sinh)² for odd f, with **no** pole-orthogonal projection;
- the eigenvalue is Q/‖f‖².

The basis is orthonormal sines with Zhu's mode rule K = max(48, ⌊5LT*/π⌋ + 8). The arithmetic is mpmath at 40–80 digits, with Gauss–Legendre panel quadrature.

| L | even λ₁ | Zhu Table 3 | even λ₂ | odd λ₁ |
|---|---|---|---|---|
| 0.5 | 1.05e-6 | 1.05e-6 | 2.1e-2 | 2.3e-4 |
| 0.6 | 1.82e-9 | 1.82e-9 | 1.2e-4 | 7.0e-7 |
| 0.7 | 4.99e-13 | 4.99e-13 | 1.0e-7 | 2.9e-10 |
| 0.8 | 2.270e-17 | 2.27e-17 | 1.06e-11 | 2.24e-14 |
| 0.9 | 5.91e-23 | 5.91e-23 | 1.0e-16 | 1.0e-19 |
| 1.0 | 7.97e-30 | 8.08e-30 | 3.3e-23 | 2.2e-26 |
| 1.1 | 2.76e-38 | 2.78e-38 | 2.0e-31 | 1.1e-34 |
| 1.2 | 9.90e-49 | 9.98e-49 | 1.8e-41 | 6.2e-45 |

- **Agreement with Zhu:** we reproduce Zhu's sine-basis upper bounds to 3 digits.
- **Convergence in modes:** more modes lower the value, as a Galerkin method should. At L = 0.8, 48 → 64 modes gives 2.27e-17 → 2.02e-17, heading toward Zhu's Legendre value of 1.65e-17. At L = 1.0, 81 → 105 modes gives 7.97e-30 → 7.39e-30. Every value lies inside Zhu's certified enclosure where one exists, [8.9e-18, 2.27e-17] at L = 0.8.
- **Why this differs from our earlier numbers:** those used a pole-orthogonal projection and only 40 modes, and they were float64.
- **Fake-prime controls at proper precision (even λ₁):**
  - Jitter σ = 0.05: −0.07, −0.085, −0.11, −0.49 at L = 0.5, 0.6, 0.8, 1.0.
  - p = 3 flipped: −6e-3, −0.85, −1.27 at L = 0.6, 0.8, 1.0. At L = 0.5 the result is unchanged, because 3 is not yet in range.
  - So the controls fail at O(1) as soon as the altered prime enters, while the real form stays positive at 1e-49.
- **Near-null count:** the even eigenvalues below a fixed fraction of λ₂ track N(T*), but there is no sharp "null" dimension. The spectrum is a geometric ladder: λ₁ : λ₂ : λ₃ ≈ 1 : 1e7 : 1e14 at L = 1.2.
- **Parity:** the odd sector sits 214 times higher at L = 0.5 and 6300 times higher at L = 1.2, so parity is well resolved.
- **Not done:** L ≥ 1.4 was too costly here (L = 1.4 needs 123 modes at about 110 digits). Nothing is interval-certified.

## Ground state on Connes' route (mpmath)

Script: `scripts/positivity/hp2.py`; plot `hp2.png`. Lean: `lib/core/ParityGround.lean`, theorem `parity_of_simple`. It says that for an involution P, if v ≠ 0 and Pv = c·v, then c = ±1. So a simple eigenvector of a parity-commuting form is even or odd. This is abstract linear algebra only, and uses only standard axioms.

- **The ground state is simple and even at every L tested.** λ₂/λ₁ in the even sector is 2e4, 4.7e5, 4.2e6, 1.8e7 at L = 0.5, 0.8, 1.0, 1.2, growing roughly like e^{3.4L} in log terms. λ₁(odd)/λ₁(even) is 214, 986, 2797, 6307 at the same L.
- **The ground state's transform has only real zeros.** Write ξ̂(r) = cos(rL)·P(r²)/∏(α_k² − r²). The transform's zeros are then the roots of a polynomial P of degree n − 1, together with cos zeros beyond the basis.
  - At every L in 0.5–1.2, all n − 1 roots of P are real and positive: 23, 30, 40, 53, 69 roots, with no complex or negative roots.
  - This matches the Connes–van Suijlekom theorem, since the ground state is simple and even.
- **Comparison with Ξ:** the real zeros reproduce the zeta zeros consecutively, well beyond T*.

| L | N(T*) | zeros within 1e-6 | within 1e-3 | within 0.1 |
|---|---|---|---|---|
| 0.8 | 4 | 4 | 7 | 10 |
| 1.0 | 8 | 13 | 18 | 22 |
| 1.2 | 16 | 30 | 37 | 42 |

  This is the ζ-cycle phenomenon of Connes–Consani, reproduced here from the geometric side alone, with no zero data entering the matrix.
- **Verdict:** this is a strong numerical confirmation of the Connes route's first missing step (simple, even ground state) for L ≤ 1.2. It is not a proof at any scale: there is no interval certification, and the second step (convergence of the zeros as L → ∞, which would give RH) is untouched.

## Prime-phase alignment and Zhu's barrier (float64 adequate; λ via mpmath)

Scripts: `scripts/positivity/hp3.py` and `hp3b.py`; plot `hp3.png`. We measured S(t)/A, with S(t) = Σ 2Λ(n)n^{−½} cos(t log n) and A its total weight, on t ∈ [1, T*].

- **Real primes avoid alignment better than random ones, increasingly with L.** The real maximum is 0.87, 0.73, 0.61, 0.49, 0.40 at L = 0.8, 1.0, 1.2, 1.5, 2.0. Twenty Cramér random prime sets give 0.89, 0.81, 0.79, 0.72, 0.62 (sd 0.04–0.11). At L = 2 the real value sits below every random set (minimum 0.50), about 3 sd low.
- **Kronecker test:** the best simultaneous approximation of the prime phases on [1, T*] is max‖t log p/2π‖ = 0.066, 0.134, 0.206, 0.252 at L = 0.8, 1.0, 1.2, 1.5.
- **But alignment does not track positivity:**
  - Jittered and flipped sets have similar maxima: at L = 1, 0.72 and 0.75 against real 0.73.
  - At L = 0.8 and 1.0, every Cramér set that differs from the real primes has λ_min between −0.35 and −0.93, including sets with *lower* alignment than the real primes (0.675 against 0.732 at L = 1).
  - Sets identical to the real primes give λ ≈ +1e-17. That value comes from float64-rounded inputs; the exact value is 2.27e-17.
- **Verdict:** in the range positivity cares about, it is decided by the exact arithmetic of log n and its weights, not by how close the phases come to aligning. The barrier phrase "the phases cannot align" refers to frequencies up to T₁ = 2πe^{A_L} ≫ T*, and low alignment on [1, T*] neither implies nor follows from positivity. Credit: Grok Bot numerics.

## Lean certificate for finite-mode Weil positivity (`WeilCert`)

Scripts: `scripts/positivity/arbcert.py` (python-flint/arb ball arithmetic) and `certgen.py` (exact rationals).

**Lean module `lib/core/WeilCert.lean`:**
- **`pos_of_cert`, fully proved:** let C = MᵀDM + δI with D ≥ 0. If |A_ij − C_ij| ≤ ρ for all i, j and n²ρ < δ, then xᵀAx > 0 for every x ≠ 0.
- **`WeilEnclosure`, a structure:** its field `encl` is the explicit hypothesis that the true Weil-matrix entries lie within ρ of C. This is the arb claim, and Lean does not check it.
- **`L05_pos`, `L07_pos`, `L08_pos`:** positivity of the 24-mode even-sector Weil matrix at L = 1/2, 7/10, 4/5, *given* that hypothesis. The concrete checks (D ≥ 0 and n²ρ < δ) are done by `norm_num`; there is no `native_decide`.
- **Axioms:** `#print axioms` shows only propext, Classical.choice and Quot.sound.

**Enclosure (arb):**
- **Setup:** Zhu's convention (eq. 17), with modes s_k, k odd ≤ 47. The prime and pole terms are in closed form.
- **Archimedean integral:** on [η, 2L] it is computed with `acb.integral`. On [0, η] it is a Taylor series at 0, with the remainder bounded by Cauchy's estimate on |z| = R. The bound uses a ball cover of the circle, R = min(1, 7/α_max) and η = R/4.

**Margins:** the certificate has far more room than needed at every L.

| L | λ_min(mid) | δ | max arb radius | ρ | n²ρ/δ |
|---|---|---|---|---|---|
| 0.5 | 1.05e-6 | 5.3e-7 | 1.8e-30 | 1.8e-30 | 2e-21 |
| 0.7 | 4.99e-13 | 2.5e-13 | 5.5e-40 | 5.5e-40 | 1e-24 |
| 0.8 | 2.27e-17 | 1.1e-17 | 2.3e-51 | 2.4e-51 | 1e-31 |

The gap of about 2e-17 at L = 0.8 is easily reachable at 200-bit precision.

**What is not proved in Lean:**
- the arb computation, including its quadrature, Taylor remainder and Cauchy bounds;
- the explicit formula and Zhu's time-domain archimedean identity;
- the identification of A_ij with Q(s_i, s_j).

The result covers only the 24-dimensional span of the modes, so it is not positivity for every f supported in [−L, L]. Zhu's certified theorem handles the infinite-dimensional tail with a separate frequency-split argument, which isn't reproduced here. Built with Grok Bot assistance.

## Full-window tail certificate, even sector, L = 1/2 (`WeilTail`)

This section extends the finite `WeilCert` check to every truncation size, so the infinitely many modes are covered. Credit: computations and Lean by an AI assistant (Grok Bot).

**Reduction (Zhu, arXiv 2608.24827, Thm 1.1 and Lemma 3.1).** Let supp f ⊂ [−L, L], F = f̂, and T# > T₁ = 2π e^{A_L}. Then
Q(f) ≥ R(f) = 2F(i/2)² + (1/π)∫₀^{T#}(Ψ_L(t) − β*)|F(t)|² dt + β*‖f‖², where β* = log(T#/2π) − 1/T# − A_L.
The chain is as follows. Write Q as pole + archimedean − primes (eq. 17). In the frequency domain the archimedean and prime parts combine into (1/π)∫Ψ_L|F|². The envelope bound of Lemma 3.1 gives Ψ_L ≥ β* for t ≥ T#. Plancherel then turns the part with t ≥ T# into β*‖f‖² minus the integral over [0, T#].
Settings here: L = 1/2, T# = 30, A_L = 2 log 2/√2 = 0.98026… (the only prime-power term is n = 2), and β* = 0.5497288384… (arb).

**Basis.** T_n(x) = P̄_n(x/L)/√L, n even. This is an orthonormal basis of L² of the even functions on [−L, L], so it is complete in that space.
- Transform: T̂_n(t) = (−1)^{n/2} 2√(Lν_n) j_n(tL), ν_n = n + ½.
- Pole vector: p_n = 2√(Lν_n) i_n(L/2).
- Matrix entries: R_nm = β*δ_nm + 2p_n p_m + C_nm, with C_nm = (1/π)∫₀^{T#}(Ψ_L − β*)T̂_n T̂_m.

Mode index i corresponds to Legendre order 2i.

**Head (orders 0..54, 28 modes).** All 406 entries C_nm were computed with arb `acb.integral` at 256 bits, max radius 4.1e-37 (`scripts/positivity/tailcert.py`).
- λ_min of the midpoint matrix is about 2.24e-7, which is small but positive.
- Exact-rational certificate (`tailheadcert.py`): M with D ≥ 0, δ = 7/62500000, ρ = 4.87e-24, n²ρ/δ = 3.4e-13. The head margin is λ0 = δ − 28²ρ.

**Tail (orders ≥ 56).** The script `tailbounds.py` uses these bounds:
- |j_n(x)| ≤ min(1, xⁿ/(2n+1)!!) for real x ≥ 0, from the Poisson integral.
- 0 ≤ i_n(z) ≤ zⁿ cosh z/(2n+1)!!.
- M_Ψ = sup_{[0,30]}|Ψ_L − β*| ≤ 6.9376, from an arb interval cover with 6000 boxes.

These give:
- |C_nm| ≤ (M_Ψ/π)·4L√(ν_nν_m)·L^{n+m}T^{n+m+1}/((n+m+1)(2n+1)!!(2m+1)!!).
- Tail diagonal: d ≥ 0.5497 − 2·max|C_nn| (max|C_nn| ≈ 1.8e-52).
- Off-diagonal row sums: e ≤ 1e-53.
- Head–tail Frobenius coupling: c² ≤ 1e-48, using |j_head| ≤ 1.
- Margin: m = λ0/2.

The block condition c² ≤ (λ0 − m)(d − e − m) holds with about 40 orders of magnitude to spare.

Caveats on rigour:
- The scripts form the tail sums explicitly only up to order 600, and take the supremum of e over only the first 40 tail rows. Beyond that they rely on the super-exponential decay, which is obvious from the bound formula, but the scripts do not bound that remainder formally.
- The analytic Bessel inequalities are standard but are not formalised.

**Lean (`lib/core/WeilTail.lean`).** Fully proved, using only propext, Classical.choice and Quot.sound:
- `head_margin`: an entrywise certificate gives the margin δ − h²ρ.
- `tail_lower`: a symmetric Gershgorin bound.
- `coupling_sq`: Cauchy–Schwarz over the product finset.
- `block_margin`: an abstract head/tail theorem, uniform in the truncation size N ≥ h, built on `ShellSchur.margin_of_coupling`.
- Concrete data `L05Tail` (M, D, δ, ρ, d, e, c², m), checked by `norm_num`.
- `reduced_margin`: m‖x‖² ≤ xᵀR_N x for every N ≥ 28.
- `L05_even_pos`: 0 < xᵀQ_N x for every N ≥ 28 and every x ≠ 0.

The following are **named hypotheses**, not proved in Lean:
- `ZhuReduction`: Q_N dominates R_N, which is Zhu's Thm 1.1 and Lemma 3.1.
- `TailHyp`: symmetry, the arb head enclosure, and the tail bounds d, e, c² above.

**What is stated.** Positivity is stated for coefficient sequences, uniformly over all finite truncations. It is not stated for functions. To pass to every even f ∈ L²[−L, L] you need two more things, neither formalised:
- Legendre completeness, which holds;
- continuity of Q in a norm controlled by the coefficients.

Even then the conclusion is only Q ≥ 0 on the closure. The uniform margin m > 0 holds in the coefficient ℓ² norm, so the conclusion is in fact Q(f) ≥ m‖f‖² for the reduced form.

**Not done.** The odd sector (pole term −2(∫f sinh)², and odd Legendre orders) and L = 0.8 were not done. At L = 0.8, T₁ grows and T#·L ≈ 160, so the head would need about 200 modes and the arb cost is out of reach in this session.

## Closing the tail: unconditional Bessel and tail bounds, both sectors at L = 1/2 (`WeilTailB`)

This section removes the tail and weight hypotheses of `WeilTail` and adds the odd sector. Credit: an AI assistant (Grok Bot).

**Reuse from the stack.**
- `WeilForm.norm_digamma_le`: ‖ψ(z)‖ ≤ 12√(1+‖z‖) for Re z ≥ 1/4.
- `WeilTail.head_margin` and `WeilTail.block_margin`, with `ShellSchur.margin_of_coupling` underneath.
- Mathlib: `intervalIntegral.norm_integral_le_of_norm_le_const`, `Real.pow_div_factorial_le_exp`, `Real.cosh_le_cosh`, and the d9 bounds for e, log 2 and π.

Other material surveyed but not usable here:
- Mathlib has a Bessel J definition through ₀F₁ (no integral representation and no bounds) and `shiftedLegendre` polynomials (no L² completeness).
- The repo's explicit-formula modules (`WeilZeta`, `WeilCriterion`, `WeilAssemble`, …) give the explicit formula over zeta zeros for strip test functions. They contain neither Zhu's frequency-cutoff reduction nor the envelope Lemma 3.1.
- `DigammaGauss` and `KaiserZeroWeight` give digamma symmetry and an upper bound for Re ψ.

**Proved in Lean, using only the standard axioms:**
- `jP_bound`: spherical Bessel functions are defined by Poisson's integral, j_n(x) = xⁿ/(2^{n+1}n!)∫₋₁¹cos(xt)(1−t²)ⁿdt. This gives |j_n(x)| ≤ (x/2)ⁿ/n! for x ≥ 0.
- `iP_bound`: likewise |i_n(z)| ≤ 2(z/2)ⁿ/n! for 0 ≤ z ≤ 1.
  - These are weaker than xⁿ/(2n+1)!!, but that does not matter for the tail, and no |j_n| ≤ 1 bound is needed.
- `That_bound` and `pole_bound`: |T̂_n(t)| ≤ b_n on [0, 30] and |p_n| ≤ 2b_n, where b_n = (1+(2n+1)/4)(15/2)ⁿ/n!.
- `βs_ge`: β* ≥ 0.37.
- `wψ_bound`: |Ψ_L − β*| ≤ 55 on [0, 30]. Here Ψ_L = Re ψ(1/4+it/2) − log π − √2 log 2·cos(t log 2).
- Every entry satisfies |R_ij − β*δ_ij| ≤ 558·b_{2i+par}·b_{2j+par} (`Rm_entry`), and `Rm_symm` proves symmetry.
- `b_step`: b_{n+2} ≤ b_n/2 for n ≥ 20. A geometric-majorant lemma then gives, for **every** truncation size N:
  - tail row sums ≤ 558·B0·2B0;
  - tail diagonal ≥ 0.37 − 558·B0²;
  - coupling ≤ 558²·28·190269²·2B0², using b_n ≤ 29·e^{15/2} on the head;
  - where B0 = 5e-25 ≥ b_56 and b_57, checked by `norm_num`.
- `sector_margin`, `even_margin`, `odd_margin`, `L05_even_full`, `L05_odd_full`.

**Odd sector.** The basis is odd Legendre orders 1..55. The pole term enters with sign −: −2(∫f sinh(x/2))².
- arb head: max radius 5.2e-37, λ_min(mid) = 4.66e-5.
- Certificate: δ = 233/10⁷, ρ = 1.9e-24, n²ρ/δ = 6.4e-16.
- Margin: m = 1e-5.

The even sector margin is m = 5e-8.

**Final theorems.** `WeilTailB.L05_even_full` and `L05_odd_full` cover any Q : ℕ → ℕ → ℝ (the Weil form in sector Legendre coordinates). Given `ZhuRed Q par σ` and the sector head enclosure, they conclude 0 < xᵀQ_N x for every N ≥ 28 and every x ≠ 0 supported in range N.

**Hypotheses that remain:**
1. `EvenHead` and `OddHead` (**arb numerics**). These are the entrywise enclosures of the 28×28 head of the reduced matrix, computed by `tailcert.py` at 256 bits.
   - They also identify Lean's Poisson-integral j_n with arb's ₀F₁ evaluation (a classical identity).
   - They identify Re ψ with arb's half-sum of conjugate digammas (`DigammaGauss.digamma_conj`).
2. `ZhuRed` (**Zhu analytic**). This says Q_N ≥ R_N on every truncation, which is Zhu's Theorem 1.1 and envelope Lemma 3.1 written in Legendre coordinates. The quadratic form Q is abstract in Lean.
3. Coefficients versus functions (**functional analysis**). Positivity is stated for coefficient vectors of every finite size. Turning it into Q(f) > 0 for every even or odd f ∈ L²[−1/2, 1/2] requires two things, neither formalised (Mathlib lacks them):
   - L² completeness of the normalised Legendre basis;
   - continuity of Q.

**Not done.** L = 0.8 is not done; the head would need about 200 modes, which is out of reach for the arb cost.

## Zhu's reduction at L = 1/2, formalised up to two named inputs (`WeilZhuRed`)

This section works by an AI assistant (Grok Bot) and splits the earlier `ZhuRed` hypothesis into proved steps and two smaller named inputs.

**Proof chain** (Zhu, arXiv 2608.24827, eq. 17, Lemma 2.5, Lemma 3.1, Thm 1.1), for supp f ⊂ [−L, L], g = f⋆f̃, ĝ = |F|²:
1. Frequency form. Since g(x) = (1/π)∫₀^∞|F|²cos(tx)dt, the prime term becomes −(1/π)∫₀^∞|F|²Σ_{log n<2L}2Λ(n)n^{−1/2}cos(t log n). Lemma 2.5 writes the archimedean term as (1/π)∫₀^∞(Re ψ(1/4+it/2) − log π)|F|². Together, Q(f) = pole + (1/π)∫₀^∞Ψ_L|F|².
2. At L = 1/2 only n = 2 has log n < 1, so Ψ_L(t) = Re ψ(1/4+it/2) − log π − √2 log 2·cos(t log 2).
3. Envelope (Lemma 3.1): Ψ_L(t) ≥ β* for t ≥ T#.
4. Split at T#. Use Ψ_L ≥ β* on (T#, ∞) and Plancherel ∫₀^∞|F|² = π‖f‖². This gives Q ≥ pole + (1/π)∫₀^{T#}(Ψ_L − β*)|F|² + β*‖f‖² = R.

**Proved in Lean (standard axioms only):**
- `primes_L05`: Λ(n) ≠ 0 and log n < 1 imply n = 2.
- `prime_coeff_L05`: 2Λ(2)/√2 = √2 log 2.
- `envelope`: Ψ_L(t) ≥ β* for all t ≥ 30. This reuses the vendored vertical-line Stirling bound `Zeta23.StirlingVert.re_digamma_stirling'`, |Re ψ(a+it) − log|t|| ≤ 5/t² for 0 < a ≤ 1 and |t| ≥ 1/2. The proof is: Re ψ(1/4+it/2) ≥ log(t/2) − 20/t² ≥ log(t/2) − 1/30, and log(t/2) − log π ≥ log(30/2π).
- `QF_ge_R`: R_N(x) ≤ QF_N(x) for every truncation size N and every x. This is steps 3–4 done exactly in Lean: the set-integral split at 30, monotonicity on (30, ∞), the finite-sum expansion, and identifying the [0, 30] piece with the matrix C.
- `zhuRed_of`: `FreqRep` and `ModePlancherel` together imply `ZhuRed`.
- `L05_even` and `L05_odd`: positivity of the Weil form.
- `QF_even_pos` and `QF_odd_pos`: positivity of the frequency form, assuming only `ModePlancherel` and the arb head.

**Named inputs that remain:**
- `ModePlancherel par` (**functional analysis**):
  - (1/π)∫₀^∞T̂_nT̂_m = δ_nm within a sector, which follows from Legendre orthonormality plus Plancherel;
  - integrability of T̂_nT̂_m and Ψ_L·T̂_nT̂_m on (0, ∞).
  - Mathlib has the L² Fourier transform (`Analysis/Fourier/LpSpace`), but bridging it to these Poisson-integral modes, and the 1/t decay needed for integrability, are not done.
- `FreqRep Q par σ` (**Zhu analytic**): the Weil functional (pole + archimedean − primes) equals the frequency form QF on sector modes. This is step 1, i.e. Lemma 2.5 and the cosine expansion of g.
  - The repo's explicit-formula modules (`weilExplicit_*` in `WeilZeta`, `WeilCriterion`, `WeilAssemble`) work with strip-class test functions over zeta zeros. They do not express the archimedean term as a digamma integral against |F|² for compactly supported f, so this bridge is not formalised.
  - `primes_L05` already settles the arithmetic part of step 1.
- `EvenHead` / `OddHead` (**arb numerics**): unchanged.
- Coefficients versus functions (**functional analysis**): unchanged; positivity is stated on coefficient vectors.

## Plancherel inputs and the repo's Weil form on Legendre modes (`WeilPlanch`)

This section's work was done by an AI assistant (Grok Bot).

**Sign correction.** `WeilTailB.That` now carries the factor (−1)^{⌊n/2⌋}. This is the real part of iⁿ in the Legendre–Fourier identity, and it is the convention the arb head computation uses. Without it, the Lean matrix differed from the arb matrix by signs on the entries with i + j odd, so `EvenHead`/`OddHead` as stated would not have matched the numerics. All bounds are unaffected, because they only use |T̂ₙ|.

**What the repo provides.**
- `WeilForm.weilQ a g` (in `Roadmap`) is the concrete time-domain Weil form. It consists of:
  - the pole term 2(∫g e^{−u/2})²;
  - the archimedean part (Re ψ(1/4) − log π)‖g‖² + ∫₀^∞[g⋆g(0) − g⋆g(u)]e^{u/2}/sinh u du;
  - the prime sum −2ΣΛ(n)n^{−1/2}g⋆g(log n).
- It is defined for any real g and is the right form for even g. The `Probe` class adds evenness, support, L² and convergence of the archimedean integral. The strip class `StripTest` (analyticity of ĝ² on |Im| < 1 with 1/(1+Re²) decay) is only used to tie the form to zeta zeros, and is not needed here.
- The Legendre functions T_n(u) = √(2n+1)·P̃_n(u + 1/2) on [−1/2, 1/2] are built from Mathlib's `shiftedLegendre`.

**Proved (standard axioms only):**
- `Psi_cont` and `That_cont`: continuity, using the stack's `differentiableOn_digamma` and Mathlib's parametric-integral continuity.
- `Psi_growth`: |Ψ_L(t)| ≤ 21√(1+t), from `norm_digamma_le`.
- `modePlancherel_of`: `ModePlancherel` follows from `ModeDecay` and `ModeOrth`. Integrability of T̂ₙT̂ₘ and Ψ_L·T̂ₙT̂ₘ on (0, ∞) is proved using the majorant K(1+|t|)^{−3/2} (Mathlib's `integrable_one_add_norm`).
- `prime_sum_L05`: the repo's full prime series for f = Σxᵢ T_{2i} equals its n = 2 term. The autocorrelation vanishes for |u| > 1, and log n > 1 for n ≥ 3.
- `weilQ_eq_QF`: weilQ(1/2)(f) = QF(x), given the bridge below. This uses the integral split Ψ_L = (Re ψ − log π) − √2 log 2·cos(t log 2) and 2Λ(2)/√2 = √2 log 2.
- **Final theorem `L05_even_weilQ`:** for N ≥ 28 and x ≠ 0, 0 < weilQ(1/2)(Σ_{i<N} xᵢ T_{2i}).
- **Odd sector `L05_odd_QF`:** positivity of the frequency form. The repo's `weilQ` covers only even g (its pole term has the even sign).

**Named inputs left:**
- `EvenHead` / `OddHead` — arb numerics.
- `ModeDecay` — special functions: |T̂ₙ(t)| ≤ Cₙ/(1+t), i.e. jₙ(x) = O(1/x).
- `ModeOrth par` — functional analysis: (1/π)∫₀^∞ T̂ₙT̂ₘ = δₙₘ. This follows from:
  - the Legendre–Fourier identity ∫₋₁¹Pₙe^{ixt} = 2iⁿjₙ(t);
  - Legendre orthonormality;
  - Plancherel, which Mathlib has only as an abstract L² isometry, not linked to the integral formula for L¹ ∩ L² functions.
- `EvenBridge.pole` — special functions: ∫₋₁¹Pₙ(x)e^{ax}dx = 2iₙ(a).
- `EvenBridge.arch` — Zhu analytic (Lemma 2.5): the archimedean distribution in |F|² form.
- `EvenBridge.acorr` — Fourier: f⋆f(log 2) = (1/π)∫₀^∞cos(t log 2)F². This is Wiener–Khinchin, reachable from Mathlib's `Continuous.fourierInv_fourier_eq` once `ModeDecay` makes F² integrable, but not formalised here.
- Odd sector — Zhu analytic: a concrete odd Weil form, with pole −2(∫f sinh)², is not in the repo, so the odd statement remains about the frequency form.
