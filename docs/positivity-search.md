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

`scripts/positivity/ramanujan_net.py` (results in `ramanujan_net_results.txt`) uses quotients of the Bruhat–Tits tree, the p-adic analogue of AdS, as a network of identical "black holes" (Lubotzky–Phillips–Sarnak, Combinatorica 1988; p-adic AdS/CFT: Gubser et al., arXiv 1605.01061; Heydeman et al., arXiv 1605.00599). Floating point, uncertified.

- **Single prime.** LPS X^{p,13} on PGL(2,13) has 2184 vertices. Max nontrivial |λ| is 4.250 (p = 5, bound 2√5 = 4.472), 7.851 (p = 17, bound 8.246) and 9.932 (p = 29, bound 10.770). All Ihara poles satisfy |u| = p^{−1/2} to 10⁻¹⁶, which is RH for the graph. A random 6-regular graph is only just Ramanujan (4.464).
- **Two primes on one quotient.** A₅ and A₁₇ commute exactly, and every joint eigenvector is Ramanujan at both primes. The product of local factors is the Satake/automorphic L-function picture. Ramanujan at every p is Ramanujan–Petersson, a theorem here (via Deligne), and it says nothing about ζ's zeros, which need the archimedean place.
- **Bad gluing.** Two copies of X^{5,13} are joined by k edge swaps (out of 6552 edges per copy, staying 6-regular). The margin 2√5 − λ is −1.53 at k = 1, −1.16 at k = 300 and −0.43 at k = 1000. A weak junction breaks RH and is recovered only once the junction is a large fraction of the graph.

Verdict: RH for these networks is a theorem, and it comes from arithmetic gluing (quaternion/Hecke structure), not from regularity: generic junctions fail it. That matches the junction-margin story, but it is the finite-place analogue, and it does not reach ζ.
