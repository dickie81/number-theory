# The Connes strand and the rest of the library

This page lists what joins the library's work around A. Connes's approach to RH to its other parts. It covers the
links that are already theorems, the links found in a survey of the import graph (November 2026), and which of those
are now proved. Every Lean name on the page is a declaration of the library.

## The strand

| Part | What it is | Lean |
|---|---|---|
| Weil's form on `[−a, a]` | The object of A. Connes and C. Consani's archimedean work: Weil's form `Q` on probes supported in `[−a, a]`, its ground energy `λ₁(a)` and its ground states. Positivity for `2a ≤ log 2` is classical: H. Yoshida (1992), and Connes and Consani by another method | `WeilForm.weil_criterion_zeta`, `WeilForm.rh_iff_lam_subexp`, `WeilForm.weilQg_ge_twentieth_all`, `WeilForm.groundState_unique_below_log2`, `WeilForm.weilQg_ge_both`, `WeilForm.finrank_le_offline_zeta` |
| Connes' map `E` | `E(F)(x) = √x Σ_{n≥1} F(nx)`, with `𝓜(Ef)(s) = ζ(s + ½)𝓜f(s + ½)` and the Poisson symmetry `E(h)(x) = E(H)(1/x)`; the Kaiser trial built from it has a transform that vanishes at every zero, and it bounds `λ₁(a)` double-exponentially | `Kaiser.mellin_E`, `Kaiser.poisson_E`, `Kaiser.integral_KF_zero`, `Kaiser.lam_kaiser`, `WeilForm.lam_dexp` |
| The orbit lattice | The Hilbert–Pólya picture of [ball-conjecture.md](ball-conjecture.md): vectors `w_n` with `⟨w_m, w_n⟩ = √(mn)·K_H(m/n)`, computed from the primes, a realization exactly under RH, Weil's dictionary, the slices of two primes, the lonely primes | `BallHadamard.rh_iff_posDefH`, `BallPsi.kerH_explicit`, `BallLattice.rh_iff_realization`, `BallWeil.rh_iff_castelnuovo_severi`, `BallSlice.rh_iff_bound_pair`, `LonelyPrimes.tendsto_lonely_ratio` |
| The Bohr ball | The lift `z(s) = (p^{−s})_p`: the critical line is the unit sphere after normalisation, zero-free regions are shells, density estimates count zeros outside shells | `BohrSphere.riemannHypothesis_iff_mem_sphere`, `BohrJoins.shell_of_zeroFree`, `ShellCount.NX_eq_ncard_outside`, `BohrTorus.tendsto_mean_character` |
| The function-field model | Weil's criterion over a finite field in both directions, Manin's lattice for an elliptic curve, and a variety with an Euler product and a functional equation whose kernel is not positive | `WeilFF.countKernel_posDef_iff`, `ManinHasse.toeplitz_nonneg`, `ManinHasse.gram_orbit_card`, `PurityTest.not_posDef` |

## Links already in the library

The import graph of `lib/core`, `lib/pnt`, `lib/dh` and `lib/zeta23` shows these joins.

- **Weil's explicit formula is a tool for the primes.**
  - The short-primes theorems go through it. `ShortWeil.short_primes_of_density` takes its test function from the
    iterated autocorrelations of a box, the explicit formula over Mathlib's zeros from `WeilZeta.lean` and the zero
    weights from `KaiserZeroWeight.lean`.
  - So `ZetaGMDensity.short_primes_seventeen_thirtieths`, a prime in `(y, y + y^θ]` for `θ > 17/30`, rests on the
    strand's machinery.
  - Zero detection (`DetectCore.lean`), the zero sum of the prime window (`ShortZeros.lean`) and `zeta23`'s
    comparison of local zero counts (`lib/zeta23/CountCompare.lean`) use it too.
- **Zero-free regions feed Weil's form, and its failure feeds back.**
  - The half-plane gives `λ₁(a) ≤ K(a + 1)e^{(59/6)a − 4πe^{2a}}` and a rate for the twin form
    (`HalfPlaneJoins.lam_prefactor_eleven_twelfths`, `HalfPlaneJoins.weil_rate_eleven_twelfths`).
  - Korobov and Vinogradov's region sharpens the Kaiser prefactor (`KaiserKV.lam_prefactor_KV`).
  - If RH fails, `ψ(x) − x = Ω±(√x)`, through the Landau argument of `WeilLandau.lean` and Landau's theorem
    (`HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH`, `LandauLaplace.LSeries_landau`).
- **Characters.**
  - GRH in the strand's form, `PsiOmega.GRH`, gives Linnik's exponent `2 + η` (`LinnikGRH.linnik_two_of_GRH`).
  - The machinery of Weil's form for characters gives the prime races mod 3, 4, 7 and 8 (`PsiOmega.race_three_half`).
- **Quadratic fields and physics.**
  - The radial member of the angular family is `ζ·L(χ₋₄)` (`AngularFamily.member_zero_eq`). It feeds the Madelung
    constant's Dirichlet series (`Madelung.lseries_coeff`) and `L(1, χ₋₄) = π/4` (`AngularResidue.LFunction_chi4_one`).
- **The Bohr ball and the zero counts.**
  - Zero-free regions are shells around the sphere (`BohrJoins.shell_of_zeroFree`), and a density estimate counts the
    zeros outside a shell (`ShellCount.NX_eq_ncard_outside`).
  - If RH fails, some pair of zeros has one Bohr vector inside the sphere and one outside
    (`BohrJoins.zero_pair_of_not_RH`).
- **The dh column.** Each family of criteria has a test on the Davenport–Heilbronn function, the orbit's kernel
  included (`PsiOmega.not_posDef_dh`).
- **The orbit lattice** was the least joined part. `BallLattice.lean` imports `PsiOmega.lean`, `lib/dh` tests it, and
  otherwise it rests on Mathlib and PrimeNumberTheoremAnd alone. Most of the links below are its.

## New links

### 1. The orbit lattice is Weil's form on translates of one probe

In `v = log x`, let `g₀(v) = e^{v/2}` for `v ≤ 0` and `0` for `v > 0`, so `ĝ₀(τ) = ∫ g₀(v)e^{iτv} dv = 1/(½ + iτ)`.
The vector `w_n` is the probe `√n·g₀(v − log n) = e^{v/2}·1_{v ≤ log n}`, since its transform at a zero `ρ = ½ + iτ`
is `n^ρ/ρ`, and `Σ_ρ m^ρ n^{1−ρ}/(ρ(1 − ρ)) = √(mn)·K_H(m/n)`. So:
- **The Gram matrix is Weil's form.** `G(m, n)` is the bilinear zero sum of the two probes (`WeilForm.bil_zero_sum` is
  the library's form of it), and the weights `1/(ρ(1 − ρ))` of Hadamard's identity are `|ĝ₀|²`.
- **The scaling is the translation.** `U_n = n^{iD}` translates by `log n`, so `D = −i d/dv`. This is Connes' scaling
  action, in the coordinates of Weil's form.
- **The increments are Connes and Consani's probes.** A combination `Σ c_n w_n` over `M ≤ n ≤ N` with `Σ c_n = 0` is
  a step probe supported in `[log M, log N]`, of support `2a = log(N/M)`.
- **The archimedean range is the window of ratio 2.** `G(k, k − 1)` has no prime term, since `k/(k − 1) < 2`. So a
  window of ratio below 2 is the range `2a < log 2` of Yoshida's and Connes and Consani's theorems, where Weil's form
  has no prime term (the argument of `WeilForm.weilQ_ge_quarter`). The bound `d_k ≤ log(k/2π) + 1 − γ + o(1)` of
  ball-conjecture.md comes from that range.
- **What the library's positivity gives the orbit.** Once `WeilForm.weilQg` is identified with the orbit form on
  these probes, `WeilForm.weilQg_ge_twentieth_all` makes the increments in every window `[M, e^{1/6}M]` positive, for
  every `M`, with no RH and no computation. Under its two certificates, `WeilForm.weilQg_ge_both` does the same for
  windows `[M, e^{1.6}M]`, a ratio of about 4.95.
- **What the certificate gives Weil's form.** `scripts/ball_certificate.py` proves Weil's form positive definite on
  the `10⁴`-dimensional space spanned by these probes for `n ≤ 10⁴`. That is support `log 10⁴ ≈ 9.2` for the
  increments, far past `1.6`, but on a thin family of probes, not on all of them.
- **The space degenerates and the lattice need not.** `λ₁(a)` tends to `0` double-exponentially
  (`WeilForm.lam_dexp`), and the orbit's Gram matrix has smallest eigenvalue `1.3·10⁻⁴` at `N = 3000`. The
  orbit-lattice conjecture asks that the integer step probes stay away from those directions.

Not yet a theorem: the identification of `WeilForm.weilQg` on step probes with `BallHadamard`'s kernel. Both are the
zero side of the explicit formula. The step probes, translated into `[−a, a]`, are bounded with compact support, the
kind of probe that `WeilForm.SProbe` describes, and the translation leaves the form unchanged.

### 2. Connes' map is the sum over the orbit's divisions

For the orbit's base probe `1_{(0, r]}`, `E(1_{(0, r]})(x) = √x Σ_{m≥1} 1_{(0, r]}(mx) = Σ_{m≥1} √x·1_{(0, r/m]}(x)`.
That is the sum of the probes of `w_{r/m}` over `m ≥ 1`, at the rationals where `BallKernel` works.
- **It vanishes at every zero.** By the identity of `Kaiser.mellin_E`, continued past `Re s = ½`, its transform at
  `ρ − ½` is `ζ(ρ)·r^ρ/ρ = 0`. Termwise, with `ζ(ρ)` as the regularised sum, it is `Σ_m (r/m)^ρ/ρ = r^ρ ζ(ρ)/ρ`.
- **So the zeros are the relations that `E` imposes.** In the realization, whose coordinates are indexed by the zeros,
  the formal sum `Σ_m w_{r/m}` has every coordinate zero. This is Connes's picture: the zeros as the spectrum of the
  scaling action on the cokernel of `E`.
- **The Kaiser trial is such a sum, made smooth.** Its transform vanishes at every zero (`Kaiser.integral_KF_zero`),
  and cut to the window it is the near-null probe behind `λ₁(a) ≤ Ke^{16a − 2πe^{2a}}` (`Kaiser.ghat_zero_decomp`,
  `Kaiser.lam_kaiser`).

### 3. The Nyman–Beurling criterion lives in the flat model

B. Nyman (1950), A. Beurling (1955) and L. Báez-Duarte (2003) proved the criterion.
- **The criterion.** RH holds if and only if `d_N → 0`, where `d_N` is the distance in `L²(0, ∞)` from `1_{(0,1]}` to
  the span of the dilates `{1/(kx)}`, `k ≤ N`, of the fractional part.
- **Its space is the flat model's.** `1_{(0,n]}` is the flat `w_n`, whose Gram matrix is `min(m, n)` (`BallFlat`), and
  the target is `w_1`.
- **Its approximants are Connes' sums.** `{1/(kx)} = 1/(kx) − Σ_{m≥1} 1_{(0, 1/(km)]}(x)` is a sum over divisions, as
  in link 2.
- **On the critical line.** `d_N² = (1/2π)∫ |1 + ζ(s)D_N(s)|² dt/|s|²`, with `D_N(s) = Σ_{k≤N} c_k k^{−s}`. The
  weight `dt/|s|²` is the flat model's measure, and `ζ` is what turns the flat orbit into the criterion's vectors.
- **The rate has the orbit's constant.** J.-F. Burnol (Adv. Math. 170, 2002) proves `liminf d_N² log N ≥ Σ m_ρ²/|ρ|²`
  over the zeros on the line, with `m_ρ` the multiplicity. S. Bettin, J. B. Conrey and D. W. Farmer (arXiv:1211.5191)
  prove `d_N² log N → 2 + γ − log 4π` under RH and a bound for `Σ 1/|ζ′(ρ)|²`.
  - With simple zeros on the line the constant is `d_1 = K_H(1)`, the first pivot of the orbit lattice.
  - Heuristically, `ζ(s)D_N(s)` vanishes at each zero. The error there is `1/ρ`, which is `w_1`'s coordinate at `ρ` in
    the realization, and a Dirichlet polynomial of length `N` moves on the scale `1/log N`.
- **Open.** The criterion asks how fast `w_1` is reached by Connes' sums, and the orbit-lattice conjecture asks how far
  each `w_k` stays from the earlier `w_n`. How the pivots `d_k` relate to `d_N` is not worked out here.

### 4. Rows and columns of one matrix

Both pictures read the table `(n^{−ρ})`, with a row for each zero and a column for each integer.
- **The two vectors.** The Bohr vector of a zero `ρ` is its row over the primes, `(p^{−ρ})_p`, normalised. The orbit
  vector of an integer `n` is its column, `(n^{ρ−½})_ρ` with weights `1/|ρ|`, up to the factor `√n` and the reflection
  `ρ ↦ 1 − ρ` that the functional equation allows.
- **RH is that every entry has modulus `n^{−½}`.** `BohrSphere.riemannHypothesis_iff_mem_sphere` reads it on the
  rows, as the normalised Bohr vector lying on the unit sphere. `BallLattice.rh_iff_realization` reads it on the
  columns, as the orbit being realized.
- **An off-line pair is the same object in both.** For a pair `ρ`, `1 − ρ̄` off the line,
  `BohrJoins.zero_pair_of_not_RH` puts one Bohr vector inside the sphere and one outside. In the orbit picture that
  pair is the hyperbolic plane in which the coordinates `n^{β−½}` and `n^{½−β}` grow and shrink.

### 5. The frontier's half has the error exponent `Θ` (proved: `LonelyJoins`)

The lonely primes of stage `N` are the primes in `(N/2, N]`.
- **The exponent.** For `a ≥ ½`, `θ(x) − θ(x/2) = x/2 + O(x^{a+ε})` for every `ε > 0` if and only if `Θ ≤ a`
  (`LonelyJoins.lonely_weight_isBigO_iff`).
- **RH.** So RH holds exactly when the lonely primes carry half of `x` to within `x^{½+ε}`
  (`LonelyJoins.rh_iff_lonely_weight`).
- **What it joins.** `LonelyPrimes` to `PsiExponent` and `MertensExponent`. The half itself is the prime number theorem;
  how exactly it holds is RH.
- **The proof.** `LonelyJoins.isBigO_of_sub_half` telescopes `x, x/2, x/4, …`, so a bound on `f(x) − f(x/2)` is a bound
  on `f(x)`. Then `PsiExponent.psi_omega_Theta` rules out every `a < Θ`.

### 6. The frontier is filled at every scale (proved: `LonelyJoins`)

For `θ > 17/30` and every large `y`, each interval `(y, y + y^θ]` inside `[N/2, N]` holds a lonely prime of stage `N`
(`LonelyJoins.lonely_in_window`), by `ZetaGMDensity.short_primes_seventeen_thirtieths`. So once `N/2` is large, the
gaps between the lonely primes of stage `N` are at most about `N^θ`, across the whole frontier.

### 7. One method for both certificates

- **The proposal.** `WeilForm.weilQg_ge_both` waits on two certificates, `WeilForm.CertE` and `WeilForm.CertO`: lower
  bounds for 350 mode energies, and the definiteness of two Gram matrices. `scripts/ball_certificate.py` proves the
  definiteness of `10⁴ × 10⁴` Gram matrices with every rounding bounded, by a congruence, Gershgorin's theorem and the
  Schur complement. `tools/linnik/` turns a computation into Lean files the kernel checks.
- **Not yet done.** The congruence method, written out in rationals for the kernel, would discharge `CertE` and
  `CertO`. That would make Weil positivity at `2a ≤ 1.6`, past the primes 2 and 3, a theorem, beyond Connes and
  Consani's `log 2`.
- **Parallel work.** X. Zhu, "Weil positivity in compact windows: a finite reduction, certified two-sided bounds, and a
  Landau–Widom decay law" (arXiv:2608.24827, 2026), claims that window by interval arithmetic:
  `Q(f) ≥ 8.9·10⁻¹⁸‖f‖²` for every `f` supported in `[−0.8, 0.8]`. A kernel-checked version is what the library
  would add.

### 8. GRH from Weil's form would give Bach's bound

- **The proposal.** The library's algorithmic results have `11/12` written in, so `A > 12`:
  - `SmallPrimes.closure_primes_eq_top`;
  - `MillerTest.prime_iff_forall_strongProbablePrime`;
  - `LeastNonresidue.exists_prime_ne_one`.

  [account.md](account.md) (the frontier, item 3) names the refactor that makes them depend on the half-plane as a
  parameter.
- **Not yet done.** Then GRH, in the form of the strand's criteria for characters (`PsiOmega.grh_iff_QC_subexp_all`),
  would give `A > 2`: Bach's bound, and Miller's test with `(log n)^{2+ε}` bases.

### 9. Weil's criterion over `𝔽_q` and Manin's lattice

- **The gap.** `WeilFF.countKernel_posDef_iff` and `ManinHasse.toeplitz_nonneg` have no import between them.
- **Not yet done.** The missing input is the rationality `#E(𝔽_{q^d}) = q^d + 1 − α^d − ᾱ^d`. With it, Manin's
  positivity and Weil's criterion would give `|α| = √q` through the criterion: the shape of proof that the strand looks
  for over `ℚ`.

### 10. An overlap

`BallSlice.irrational_log_div` (`log p/log q` is irrational, by valuations) is the two-prime case of
`BohrTorus.eq_zero_of_sum_log`, the linear independence of the `log p`. `BallSlice.dense_log_pair` is the
one-dimensional shadow of Kronecker and Weyl on Bohr's torus (`BohrTorus.tendsto_mean_character`).

## What is new

- **Links 1 to 4 restate known structure.** Weil's form is Weil's (1952), and its positivity in windows is due to
  Yoshida, to Connes and Consani, and to Zhu. The spectral realization is Connes' (1999), and the dilation criterion is
  Nyman, Beurling and Báez-Duarte's, with Burnol's constant. What is added is the dictionary to the orbit lattice: its
  vectors are Weil's probes, and its `d_1` is Burnol's constant.
- **`LonelyJoins` proves classical mathematics.** The equivalence of RH with the error of `θ(x) − θ(x/2)` follows from
  the classical ones by telescoping. The short-window statement is the short-primes theorem read on `(N/2, N]`. The
  Lean proofs are new.
- **The certificate is a new computation on a thin family.** It proves positivity on the `10⁴` step probes, where
  certified positivity on every probe is claimed only to `2a ≤ 1.6`.
- **The orbit-lattice conjecture's integrality condition** (`d_k ≥ d_1`, so `±w_1` are the shortest vectors) has no
  earlier statement that the searches of October and November 2026 found.
