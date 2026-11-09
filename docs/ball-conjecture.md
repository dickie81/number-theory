# The discretised infinite ball: a research direction

A conjecture of the library's author, recorded here as a direction for work. No theorem of the library proves it,
though the library proves exactly what it would have to deliver for `ζ` (`BallKernel.rh_iff_posDef`), and the
structure it asks for in the case of an elliptic curve over a finite field (`ManinHasse.frobenius_similitude`). For
`ζ` it also proves a constraint: with the kernel of step 5 the configuration spans no lattice
(`BallLattice.not_discrete`). With Hadamard's weights in place of the Gaussian the kernel is computed from the primes
through Chebyshev's `ψ` (`BallPsi.kerH_explicit`), and numerically its configuration does span a lattice, with `w_1` as
a shortest vector (step 6). In Weil's own terms, RH is the Castelnuovo–Severi inequality for formal divisors whose
intersection numbers are computed from the primes, and that lattice statement implies it (`BallWeil`, "Weil's form"
below). This page says what it claims, what is proved in the finite-rank cases it generalises, what the library already
has towards it, what any version of it must survive, and the first steps.

The tests so far tell against that lattice statement as a route to RH. It fails for curves over finite fields, where RH
is proved, and for a positive proportion of Dirichlet `L`-functions, where GRH is expected. So as stated it is specific
to `ζ` ("What it must survive", the last item).

## The conjecture

Weil proved the Riemann hypothesis for a curve `C` over a finite field from positivity on the surface `C × C`. On its
Néron–Severi lattice the intersection form is negative definite away from one class (the Hodge index theorem, in the
form of the Castelnuovo–Severi inequality), and the graph of the Frobenius, placed in that lattice, has to sit where
that inequality allows. No such surface is known for `ζ`. The conjecture is about what takes its place:

> The object that plays the role of `C × C` for `ζ` is the discretisation of the infinite-dimensional unit ball.

One reading, which the statement leaves open: a lattice of infinite rank in a definite quadratic space, with a
direction for each prime, whose definiteness would place the zeros of `ζ` on the boundary sphere, as definiteness
places the Frobenius of a curve over `𝔽_q` on a sphere of radius `√q`.

## What is proved in finite rank

- **Elliptic curves (rank two).** The degree is a positive definite quadratic form on `End(E)`, and the Frobenius `π`
  has degree `q`, so `π` lies on the sphere of radius `√q` in that lattice; Hasse's bound `|q + 1 − #E(𝔽_q)| ≤ 2√q`
  follows. For the curves `y² = x³ + D` the library proves this without isogenies: when `q ≡ 1 (mod 3)` the
  Frobenius is an Eisenstein integer `u + vω` of norm `q`, a point of the lattice `ℤ[ω]` on the circle of radius `√q`
  (`HasseEisenstein.exists_eisenstein_trace`), and `HasseEisenstein.abs_trace_le` is Hasse's bound. For every elliptic
  curve over a finite field of odd characteristic the library proves Hasse's bound by Yu. I. Manin's argument, also
  without isogenies (`ManinHasse.abs_trace_le`). It is this positivity in another guise, and the library makes the
  lattice explicit (`ManinLattice`). Over `𝔽_q(t)`, take the twist of `E` by `s = f(t)`. On its points the degree of
  `x/s` is a quadratic form (`ManinHasse.pdeg_parallelogram`). The point `P₀ = (st, s²)` plays the identity, and the
  Frobenius points `P_k = (st^{q^k}, s^{(q^k+3)/2})` play `π^k`, with `deg P_k = q^k`. The vectors `P_k/q^{k/2}` lie on
  the unit sphere of that form, with inner products the normalised traces
  `c_{|i−j|} = (q^d + 1 − #E(𝔽_{q^d}))/(2q^{d/2})`, `d = |i − j|`. So `k ↦ c_k` is a positive-definite function on `ℤ`
  (`ManinHasse.toeplitz_nonneg`): the Riemann hypothesis for `E` in every degree, from definiteness alone. The bounds
  are stated against Mathlib's `WeierstrassCurve` and its points. This lattice is Weil's for `C = E`. The twist is the
  generic fibre of `(E × E)/±1 → E/±1 = ℙ¹`, and its points are the maps `E → E` that commute with `−1`. Up to
  2-torsion the lattice is `End(E)`, and the degree of `φ − ψ` is the intersection number of the graphs of `φ` and `ψ`
  in `E × E`. The Frobenius acts on this lattice: composition with it, which on the twist is `t ↦ t^q` followed by a
  rescaling, multiplies the degree by `q` and carries `P_k` to `P_{k+1}` (`ManinHasse.frobenius_similitude`).
- **Curves of every genus.** The Néron–Severi lattice of `C × C`, definite away from an ample class. Not formalised:
  Mathlib has no intersection theory on surfaces, no Riemann–Roch for curves and no isogenies.

## What the library has towards it

The infinite sphere, with the zeros on it exactly under RH:

- `BohrSphere.memℓp_two_bohr_iff`: the Bohr vector `(p^{−s})` over the primes `p` lies in `ℓ²` exactly when
  `Re s > 1/2`.
- `CubeBall.vLp_mem_sphere_iff`: for every nonempty finite set of primes and every `ℓ^r` norm, `r ≥ 1`, the normalised
  Bohr vector lies on the unit sphere exactly when `Re s = 1/2`; `CubeBall.line_inside_cube_not_in_ell2` places the
  critical line inside the infinite cube and outside `ℓ²`.
- `BohrJoins.zero_pair_of_not_RH`: if RH fails, a pair of zeros `ρ`, `1 − ρ` has Bohr vectors that straddle the unit
  sphere, one strictly inside and one strictly outside, on every finite set of primes.

So in the library's terms RH says that the zeros' Bohr vectors lie on the infinite unit sphere. What is missing is the
discrete structure whose definiteness would force them there. The library states the target exactly: RH holds if and
only if the kernel `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}` is positive-definite on `ℚ₊^×` (`BallKernel.rh_iff_posDef`),
and the explicit formula computes `K` from the primes (`BallKernel.kerK_explicit`). With Hadamard's weights the
kernel is a formula in Chebyshev's `ψ`, and RH holds if and only if that formula, which does not mention the zeros, is
positive-definite (`BallPsi.rh_iff_posDef_psi`).

Discretised balls in finite dimension: `BallTower.count_div_pow_tendsto_ballVol` (the points of `ℤⁿ` in a ball),
`BallTower.counted_volume_max_five` (their counted volume is largest in dimension 5), and `LocalTeeth.card_two_sq`
and `LocalTeeth.card_four_sq` (the local densities of the points on a sphere).

## What it must survive

- **The Davenport–Heilbronn function.** It has a functional equation of `ζ`'s kind and zeros off the line, and the
  library proves that a located pair of them straddles the sphere (`PsiOmega.dh_zero_pair_off_sphere`). A candidate
  object built for `dh` in the same way must fail to be definite, so its definiteness has to use the Euler product.
- **The Euler product is not enough.** Over a finite field Weil's criterion is a theorem in both directions
  (`WeilFF.countKernel_posDef_iff`), and it can be tested. The variety `Y = 𝔾_m × (𝔸² ∖ 0)` over `𝔽_3` has the zeta
  function `(1 − 9T)(1 − 3T)/((1 − T)(1 − 27T))`, with an Euler product over its closed points
  (`PurityTest.euler_product`) and the functional equation of an elliptic curve over `𝔽_27`
  (`PurityTest.zeta_functional_equation`). Its kernel is not positive-definite (`PurityTest.not_posDef`), while that
  of every elliptic curve of odd characteristic is (`PurityTest.posDef_elliptic`). What a curve has and `Y` lacks is
  purity: the inverse zeros all have the one absolute value `√q`. In the lattice that is the Frobenius multiplying the
  definite form by `q`; the inverse zeros of `Y` have the absolute values `9` and `3`. Over `ℚ`, Beurling's
  generalised primes give Euler products whose zeros leave the line, though without a functional equation
  (H. G. Diamond, H. L. Montgomery and U. M. A. Vorhauer, Math. Ann. 334 (2006)). So a candidate object for `ζ` has to
  use more than its Euler product and its functional equation, as the twist uses the curve itself.
- **Purity over `ℚ`.** Over `ℚ` itself an Euler product with a functional equation of `ζ`'s kind can have its zeros
  off the line. `ζ(s)ζ(s − 1)`, the zeta function of `ℙ¹` over `ℤ`, has the Euler product
  `∏_p (1 − p^{−s})^{−1}(1 − p^{1−s})^{−1}`, and its completion `ζ̂(s)ζ̂(s − 1)` is invariant under `s ↦ 2 − s`. Its
  zeros are the `ρ` and the `ρ + 1`, off its line `Re s = 1` whatever the truth of RH. In Lean: the Euler product
  (`PurityRational.euler_product`), the functional equation (`PurityRational.functional_equation`) and a zero off the
  line (`PurityRational.exists_zero_re_ne_one`).
  - **Its orbit form.** Build it as for `ζ`: `K(r) = Σ_{ρ′} r^{ρ′ − 1}/(ρ′(2 − ρ′))` over its zeros `ρ′`, with the Gram
    matrix `mn·K(m/n)`, the analogue of `√(mn)·K_H(m/n)` for the line `Re s = 1`. `scripts/ball_orbit.py --purity`
    computes it from the primes, by the method of `K_H`'s closed form, and `--purity-zeros` checks it against the zeros.
    In Lean the explicit formula computes it from the primes as `BallPsi.kerH_explicit` computes `K_H`
    (`PurityPsi.kerP1_explicit`), and that kernel from the primes is not positive-definite (`PurityPsi.not_posDef_psi`).
  - **It has the structure of `ζ`'s.** The similitude `G(km, kn) = k²·G(m, n)`; a sum over the places, whose local
    part at `p` is `Σ_{p^j ≤ m/n} log p·(m²/(2p^{2j}) − n²/2 + (m² − p^{2j}n²)/(2p^j)) ≥ 0` for `m ≥ n`; and the
    integral structure over the logarithms of the primes, with Glaisher's constant `A` added at the real place.
  - **It is indefinite.** From `N = 9`; at `N = 60` its smallest eigenvalue is −9.7 against a largest of 1.0·10³,
    where `ζ`'s matrix has 3.5·10⁻³ and 11. So the similitude, the places and the integrality do not carry the
    positivity. Under RH the zeros of `ℙ¹` have the two real parts `1/2` and `3/2`, as the inverse zeros of `Y` have
    two absolute values. This is the number-field form of `PurityTest`, and in Lean it needs no hypothesis: `K` is
    not positive-definite on the positive rationals (`PurityRational.not_posDef`), by the Landau argument of
    `BallHadamard.rh_of_posDefH` applied to the zeros of `ℙ¹`.
  - **The integral quaternions.** Their zeta function `(1 − 4^{1−s})ζ(s)ζ(s − 1)`, the case `w = 4` of the next item
    (`TwoVariableZeta.Z_four`; its kernel is not positive-definite, `PurityQuaternion.not_posDef_quaternion`),
    changes only the factor at `2` and adds the zeros `1 + πik/log 2`, on the line. Its form is indefinite from
    `N = 17`.
- **The balls of Arakelov geometry.** G. van der Geer and R. Schoof's Riemann–Roch for number fields, with Arakelov
  divisors, gives `ℚ` a zeta function of two variables. For `ℚ`, `h⁰(D) = log Σ_{n ∈ ℤ} e^{−πe^{−2 deg D}n²}` is the
  logarithm of a Gaussian-weighted count of lattice points, and their Riemann–Roch `h⁰(D) − h⁰(−D) = deg D` is the
  functional equation of `θ` (`ArakelovRiemannRoch.riemann_roch`). J. C. Lagarias and E. Rains write it as
  `Z(w, s) = ½∫₀^∞ θ(t)^w t^{s/2} dt/t`, with `θ(t) = Σ_{n ∈ ℤ} e^{−πn²t}`, so that `Z(1, s) = ζ̂(s)` (Ann. Inst.
  Fourier 53 (2003)). In Lean, for real `w > 0`: `Z(w, w − s) = Z(w, s)` (`TwoVariableZeta.functional_equation`),
  `Z(1, s) = ζ̂(s)` (`TwoVariableZeta.Z_one`) and, by Jacobi's four-square theorem (`JacobiFourSquares.r4_eq`),
  `Z(4, s) = 4Γ_ℝ(s)(1 − 4^{1−s/2})ζ(s/2)ζ(s/2 − 1)` on `Re s > 4` (`TwoVariableZeta.Z_four`). It is their integral
  `∫ (e^{w·h⁰(D)} − 1)e^{−s·deg D} d(deg D)` over the Arakelov divisors of `ℚ` (`ArakelovRiemannRoch.Z_eq_integral`).
  - **Lattice points in balls.** For an integer `w`, `θ^w` is the theta function of `ℤ^w`, a Gaussian-weighted count of
    the points that `BallTower` counts, and `Z(w, s)` is the completed Epstein zeta function of the cubic lattice. Its
    Dirichlet series has an Euler product only for `w = 0, 1, 2, 4, 8`: the zeta functions of `ℤ`, the Gaussian
    integers, the integral quaternions and the integral octaves (their Lemma 3.5). At `w = 4` the count closes up in
    Lean: the points of `ℤ⁴` in the ball of radius `√N` number `∼ (π²/2)N²` (`FourSquareResidue.tendsto_sum_r4`), which
    with Jacobi's theorem gives the residue of `(1 − 4^{1−s})ζ(s)ζ(s − 1)` at `s = 2` and so `ζ(2) = π²/6`
    (`FourSquareResidue.riemannZeta_two_of_lattice`); at `w = 8` the same count gives `ζ(4) = π⁴/90`
    (`EightSquareResidue.riemannZeta_four_of_lattice`).
  - **Where RH holds.** The line is `Re s = w/2`. RH there is expected at `w = 1` and `2`. It fails at `w = 4` and `8`
    whatever the truth of RH: with `z = s/2` the Dirichlet series are `(1 − 4^{1−z})ζ(z)ζ(z − 1)` and
    `(1 − 2^{1−z} + 2^{4−2z})ζ(z)ζ(z − 3)`, and their zeros at `z = ρ` lie off the lines `Re z = 1` and `2`. In Lean
    for `w = 4`: `Z(4, 2z) = c(z)·ζ̂(z)ζ̂(z − 1)` off `z = 0, 1, 2` with `c` entire, by continuation from `Re s > 4`
    (`TwoVariableZetaPurity.Z_four_eq`), so `Z(4, 2ρ) = 0` and `Z(4, ·)` has zeros off its line
    (`TwoVariableZetaPurity.exists_zero_re_ne_two`). At `w = 2`, `Z(2, 2z)` is the completed Dedekind zeta function
    of `ℚ(i)` (`TwoVariableZetaTwo.Z_two_eq`), and RH on its line is RH with GRH for `χ₋₄`
    (`TwoVariableZetaTwo.rh_two_iff`); the hexagonal lattice, `x² + 2y²` and `x² + xy + 2y²` do the same for
    `ℚ(√−3)`, `ℚ(√−2)` and `ℚ(√−7)`, with `χ₋₃`, `χ₋₈` and `χ₋₇` (`EpsteinHexagonal.rh_hex_iff`, `EpsteinTwo.rh_iff`,
    `EpsteinSeven.rh_iff`). At `w = 8`, by Jacobi's eight-square theorem (`JacobiEightSquares.r8_eq`),
    `Z(8, 2z) = c₈(z)ζ̂(z)ζ̂(z − 3)` with `c₈` entire (`TwoVariableZetaEight.Z_eight_eq`), and `Z(8, ·)` has zeros off
    its line `Re s = 4` (`TwoVariableZetaEight.exists_zero_re_ne_four`). Between
    `w = 1` and `2`, without an Euler product, Lagarias and Rains follow two zeros of `ζ` that meet on the line and
    leave it as `w` grows (their Lemma 8.1). For `w < 0` the function is positive on its line, which they call an
    anti-Riemann hypothesis (their Theorem 1.2).
  - **What it asks of a construction.** In the family of discretised balls that Arakelov geometry itself produces, RH
    is expected only at `w = 1` and `2`, whose Euler products are pure, and fails where the Euler product is mixed. A
    construction from lattice points in balls has to see that purity, or it would work at `w = 4` too.
    The rectangular lattices `ℤ ⊕ yℤ` make the same point in rank 2: at `y = 1` and `y = √2` RH for their Epstein zeta
    functions is `RH ∧ GRH` (`EpsteinFlat.rh_one_iff`, `EpsteinFlat.rh_sqrt_two_iff`), and once `y > e²` they have real
    zeros in `(½, 1)` with no hypothesis (`EpsteinFlat.not_rh`), `x² + 58y²` of class number `2` among them
    (`EpsteinFlat.not_rh_fiftyEight`): the same self-dual theta function and functional equation, without an Euler
    product. The threshold is near `4πe^{−γ} ≈ 7.06`, where the constant term of the Eisenstein series acquires its two
    real zeros (J. C. Lagarias and M. Suzuki).
  - **Rank 2.** Weng's zeta function of the rank-2 semistable lattices over `ℚ`, `ξ̂(2s)/(s − 1) − ξ̂(2s − 1)/s`, his
    integral of `(e^{h⁰} − 1)e^{−s·deg}` over their moduli (not formalised), satisfies RH with no hypothesis
    (`WengRankTwo.rh_weng`; Lagarias and Suzuki, J. Number Theory 118 (2006)). The proof compares `|ξ(2s)|` with
    `|ξ(2s − 1)|`, the reflection of `ξ` across `Re w = 1`, left of which every zero of `ξ` lies
    (`XiReflection.reflect_xi_one`). RH for `ζ` is the same reflection inequality across every line `Re s = c > ½`
    (`XiReflection.rh_iff_reflect_xi`), equivalently `Re ξ′/ξ > 0` on `Re s > ½` (`XiReflection.rh_iff_logDeriv_pos`);
    the library's band gives it for `c > 11/12` (`XiReflectionBand.reflect_xi_band`). So counting rank-2 lattices gives
    a zeta function with RH, whose zeros say nothing about those of `ζ`.
- **The real line.** The kernel of step 5 depends on `a/b` through the real line, where the positive rationals are
  dense, and it is smooth at `1`: `‖K(r) + K(1/r) − 2K(1)‖ ≤ M(log r)²` (`BallLattice.kerK_smooth`). So in every
  realization of `K` by similitudes, which exists exactly under RH (`BallLattice.rh_iff_realization`), the vectors
  `w_{n+1} − w_n` are nonzero and their norms tend to `0` (`BallLattice.not_discrete`). The orbit spans no lattice,
  and no positive multiple of the form takes integer values on it. The same holds for every kernel smooth at `1`
  (`BallLattice.tendsto_norm_sub_of_smooth`). For the Frobenius points the ratios `q^d` stay away from `1`, and
  `B(P_{k+1} − P_k, P_{k+1} − P_k) = 2q^k·#E(𝔽_q)` grows (`ManinHasse.gram_orbit_card`). So a lattice for `ζ` has to
  carry a kernel that is not smooth in `a/b`. It has to see the primes separately, `ℚ₊^× ≅ ℤ^{(∞)}` with a direction for
  each prime, rather than through `log(a/b) ∈ ℝ`. Or it can weight the zeros less steeply. With the weights of
  Hadamard's identity, `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))` has `K_H(1) = 2 + γ − log 4π` (`BallHadamard.kerH_one`),
  RH is again its positive-definiteness (`BallHadamard.rh_iff_posDefH`), and it is not smooth at `1` in any
  realization (`BallHadamard.not_smooth`). The reason is that `ζ` has infinitely many zeros
  (`ZerosInfinite.infinite_ZIdx`), and each with `|γ| ≥ 1` adds about `(log r)²` to `2K_H(1) − K_H(r) − K_H(1/r)`. So
  the obstruction does not apply to `K_H`. In every realization of `K_H` the gaps `‖w_{n+1} − w_n‖` are unbounded
  (`BallHadamard.unbounded_gaps`), because the number of zeros up to height `T` is not `O(T)`
  (`ZerosDense.not_linear`).
- **No estimate can supply the positivity.** The least value of Weil's form on supports `[−a, a]` is at most
  `Ke^{16a − 2πe^{2a}}` (`WeilForm.lam_dexp`), so positivity on growing supports has a double-exponentially small
  margin. It has to come from an exact structure, as the definiteness of a lattice would.
- **The pivot inequality fails where RH holds.**
  - **The statement.** The lattice statement that implies RH (`BallWeil.rh_of_pivots`) says that the pivots `d_k` of
    the orbit's Gram matrix `√(mn)·K_H(m/n)` satisfy `d_k ≥ d_1`.
  - **The analogues fail.** The statement has natural analogues for curves over finite fields and for Dirichlet
    `L`-functions, and both fail ([ball-conjecture-tests.md](ball-conjecture-tests.md)).
  - **For curves, where RH is a theorem.** The zeros repeat vertically, which forces a null vector at `k = q^{2g}`.
    Of a sample of 148 curves, 98 have some `d_k < d_1` with `k ≤ 150` (§4).
  - **For Dirichlet `L`-functions.** 5983 of the 29468 primitive characters with `q ≤ 400` have `d_2 < d_1` (§5).
    - For a real character this happens exactly when the zero sum `Σ_ρ 1/|ρ|²` exceeds `log(q/π) + ψ((1+a)/2) − 4c_a`,
      that is, when the low zeros carry more weight than their density accounts for (§5.1).
    - In the range scanned, the first two or three pivots decide the whole inequality.
  - **A positive proportion.** A positive proportion of quadratic characters fail. Per sign the proportion tends to
    `P(X > ½ log(27/4)) = 0.0511` and `P(X > (3/2) log(4/3)) = 0.1609`, where `X` is Lamzouri's random model
    ([d2-density.md](d2-density.md)). That is a written proof, unconditional, and a Lean proof,
    `D2Good.d2_density_pos_closed`, conditional on the half-plane. These characters are expected to satisfy GRH, and
    under GRH their Weil forms are positive.
  - **The conclusion.** So the inequality does not follow from the structure that gives RH, or GRH, elsewhere: it fails
    for curves, where RH is proved, and for characters where GRH is expected.
  - **For `ζ`.** For `ζ` it holds as far as it has been checked: `scripts/ball_certificate.py` proves it for
    `k ≤ 10⁴`, with a wide margin at `k = 2` (`d_2/d_1 = 1.718`). The data point to a reason particular to `ζ`:
    conductor `1`, `K_H(1) = 0.046`, and no zero below `14.13`. So it reads as a property of `ζ`'s numbers rather than of
    its structure, and as stated it is not a promising route to RH.
  - **What a surviving version would need.** It would have to correct for the flat model, or depend on the conductor
    and the low zeros. It would then no longer be a uniform statement about a lattice.

## Related work

None of the following states the conjecture in this form; a search in October 2026 found no statement of it, and a
second in November 2026 found none either. The closest in structure is the criterion of Nyman, Beurling and
Báez-Duarte, the last entry.

- A. Weil (1948) for curves, and his explicit formula and positivity criterion (1952). A. Grothendieck's standard
  conjectures isolate a Künneth formula and a Hodge index theorem as what the finite-field proof needs.
- C. Deninger, "The Hilbert–Pólya strategy and height pairings" (arXiv:1001.1621): RH from the positivity of a
  Hodge-type form on a conjectural cohomology.
- A. Connes (1999), and A. Connes and C. Consani: the adele class space, and the arithmetic and scaling sites, as the
  geometry over `Spec ℤ`.
- H. Bohr (1913), and H. Hedenmalm, P. Lindqvist and K. Seip, Duke Math. J. 86 (1997): Dirichlet series as functions
  on the infinite polydisc. The Hilbert space of Dirichlet series with square-summable coefficients is the Hardy space
  of the infinite polydisc; its functions are analytic on `Re s > 1/2`, and its reproducing kernel is `ζ(z + w̄)`.
- F. Dyson, "Birds and Frogs" (2009): the zeros as a one-dimensional quasicrystal. Quasicrystals arise as projections
  of lattices; through the explicit formula the zeros are paired with the numbers `log n`, the projection of the
  lattice of exponent vectors of the integers under the weights `log p`.
- J. S. Chahal, A. Soomro and J. Top, "A supplement to Manin's proof of the Hasse inequality", Rocky Mountain J. Math.
  44 (2014), 1457–1470: Manin's proof related to the proofs through isogenies, and an elementary proof of the same kind
  in characteristic 2, which Manin's argument excludes.
- E. Ruiz Duarte and J. Top, "A proof of the Hasse–Weil inequality for genus 2 à la Manin" (arXiv:1904.08662): Manin's
  argument carried to curves of genus 2, the first case past rank two.
- G. van der Geer and R. Schoof, Selecta Math. 6 (2000), and J. C. Lagarias and E. Rains, "On a two-variable zeta
  function for number fields", Ann. Inst. Fourier 53 (2003): Riemann–Roch for number fields with Arakelov divisors, and
  the zeta function of two variables it gives. Its slices at integer `w` are the Epstein zeta functions of the cubic
  lattices ("What it must survive").
- G. Faltings (1984) and P. Hriljac (1985), the Hodge index theorem on arithmetic surfaces; H. Gillet and C. Soulé, and
  A. Abbes and T. Bouche (1995), the arithmetic Hilbert–Samuel theorem; A. Moriwaki (arXiv:math/0612269), a Hodge index
  theorem from the arithmetic volume. In Faltings's and Moriwaki's proofs the positivity comes from counting lattice
  points in balls ("The limit and the lattice").
- B. Gross and D. Zagier, Invent. Math. 84 (1986), and Z. Yun and W. Zhang, Ann. of Math. 186 (2017). They write central
  derivatives of `L`-functions as heights, or as self-intersection numbers on moduli of shtukas, so positivity of an
  intersection form gives inequalities that GRH predicts, such as `L′(E/K, 1) ≥ 0`. In each case a moduli space
  supplies the surface; for `ζ` none is known.
- B. Nyman (thesis, Uppsala, 1950), A. Beurling, "A closure problem related to the Riemann zeta-function", Proc. Nat.
  Acad. Sci. 41 (1955), and L. Báez-Duarte, "A strengthening of the Nyman–Beurling criterion for the Riemann
  hypothesis", Rend. Lincei Mat. Appl. 14 (2003).
  - **The criterion.** RH holds if and only if `d_N → 0`, where `d_N` is the distance in `L²(0, ∞)` from `1_{(0,1]}`
    to the span of the dilates `{1/(kx)}`, `k ≤ N`, of the fractional part.
  - **Its space is the flat model's.** `1_{(0,n]}` is the flat `w_n`, with Gram matrix `min(m, n)` (`BallFlat`), and
    the target is `w_1`. Each `{1/(kx)} = 1/(kx) − Σ_{m≥1} 1_{(0, 1/(km)]}(x)` is a sum over divisions, of the kind
    that Connes' map gives ([connes-links.md](connes-links.md), link 2).
  - **The rate.** J.-F. Burnol, "A lower bound in an approximation problem involving the zeros of the Riemann zeta
    function", Adv. Math. 170 (2002), proves `liminf d_N² log N ≥ Σ m_ρ²/|ρ|²` over the zeros on the line, with `m_ρ`
    the multiplicity. S. Bettin, J. B. Conrey and D. W. Farmer, "An optimal choice of Dirichlet polynomials for the
    Nyman–Beurling criterion" (arXiv:1211.5191), prove `d_N² log N → 2 + γ − log 4π` under RH and a bound for
    `Σ 1/|ζ′(ρ)|²`.
  - **The shared constant.** With simple zeros on the line that limit is `d_1 = K_H(1)`, the first pivot of the orbit
    lattice. So the criterion's distance and the lattice's shortest vector carry the same constant. How the pivots `d_k`
    relate to `d_N` is not worked out here.

## First steps

1. Rank two: `HasseEisenstein`, done.
2. Hasse's bound for every elliptic curve: done in odd characteristic, by Manin's proof (`ManinHasse`). Characteristic 2
   remains: its twist is by an Artin–Schreier extension rather than by a square root. Chahal, Soomro and Top (2014)
   give the elementary proof in that case.
3. **The lattice itself, in rank two**: done (`ManinLattice`). Manin's proof uses the degree along one line only,
   `n ↦ deg(P₁ + nP₀)`. On all the points of the twist, which are `End(E)` up to 2-torsion, the degree is a quadratic
   form: `deg(P + Q) + deg(P − Q) = 2 deg P + 2 deg Q` (`ManinHasse.pdeg_parallelogram`). The Frobenius points have
   `deg(P_i − P_j) = q^j·#E(𝔽_{q^{i−j}})`, so their Gram matrix is positive semidefinite (`ManinHasse.gram_nonneg`), and
   `k ↦ c_k` is a positive-definite function on `ℤ` (`ManinHasse.toeplitz_nonneg`). It gives constraints between
   `#E(𝔽_q)`, `#E(𝔽_{q²})`, … that Hasse's bound field by field does not: `c₂ ≥ 2c₁² − 1`, that is
   `(q + 1 − #E(𝔽_q))² − 2q ≤ q² + 1 − #E(𝔽_{q²})` (`ManinHasse.trace_two_ge`); the zeta function of `E` makes it an
   equality.
4. **Weil positivity for function fields**: the criterion and its test are done (`WeilFF`, `PurityTest`). For nonzero
   `α_i` closed under `α ↦ q/ᾱ` and `N_d = q^d + 1 − Σ_i α_i^d`, the kernel `c(d) = (q^{|d|} + 1 − N_{|d|})/q^{|d|/2}`,
   computed from the counts alone, is positive-definite on `ℤ` exactly when every `|α_i| = √q`
   (`WeilFF.countKernel_posDef_iff`). A bound `|q^d + 1 − N_d| ≤ Cq^{d/2}` in every degree is already enough
   (`WeilFF.norm_eq_sqrt_of_bound`). For an elliptic curve the positivity is the lattice's
   (`PurityTest.posDef_elliptic`), and the zeta function of `Y` above shows that no step that only uses an Euler product
   and a functional equation can give it. Remaining: the positivity itself past rank two. Ruiz Duarte and Top carry
   Manin's argument to genus 2; in general it needs the Néron–Severi lattice of `C × C`, which Mathlib does not have.
5. **The statement for `ζ`**: done (`BallKernel`). Replace the Frobenius powers, indexed by `ℤ`, by the positive
   rationals `ℚ₊^× ≅ ℤ^{(∞)}`, with a direction for each prime. Replace `c_k` by the kernel
   `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}`, which at `ρ = ½ + iγ_ρ` is `Σ_ρ ĥ(γ_ρ) r^{iγ_ρ}` with the Gaussian
   `ĥ(γ) = e^{−γ²/2}`. RH holds exactly when `K` is positive-definite on `ℚ₊^×` (`BallKernel.rh_iff_posDef`): the
   positive rationals then sit on a sphere in a Hilbert space, with `K` for their inner products. The `2 × 2` minors
   `2K(1) + K(r) + K(1/r)` are the library's twin form with Gaussian weights, so the converse is its Landau argument
   (`BallKernel.re_eq_zero_of_dense`). `K` is even (`BallKernel.kerK_inv`). The explicit formula computes it from the
   primes (`BallKernel.kerK_explicit`): `K(r) = e^{1/8}(r^{1/2} + r^{−1/2})` from the poles, minus a sum over the prime
   powers `n` of `Λ(n)n^{−1/2}` against Gaussians in `log n ∓ log r`, plus two archimedean terms. That equivalence is
   Weil's criterion restated, and it is no evidence for RH. The test: the kernel of the Davenport–Heilbronn function,
   built in the same way from its zeros, is not positive-definite (`PsiOmega.not_posDef_dh`), as some of its zeros
   leave the line. So a candidate has to use unique factorisation, which is what `ℤ^{(∞)}` encodes, and, by the purity
   test, more: unique factorisation is also what Beurling's generalised integers have.
6. **The conjecture itself**, open: that the configuration of step 5 is an arithmetic definite lattice, as the twist's
   lattice is for `E`. The case of an elliptic curve over `𝔽_q`, `q` odd, is done (`ManinFrobenius`). The Frobenius
   of the twist, `t ↦ t^q` followed by a rescaling, is an additive map `φ` with `deg φ(P) = q·deg P`, so a similitude
   of factor `q` of the lattice, and the Frobenius points are the orbit of `P₀`: `φ^k(P₀) = P_k`
   (`ManinHasse.frobenius_similitude`). The similitude alone makes the Gram matrix of the orbit Toeplitz up to powers
   of `q`, `B(P_{j+d}, P_j) = q^j·B(P_d, P_0)` (`ManinHasse.gram_orbit`), and its entries are the point counts,
   `B(φ^{j+d}P₀, φ^jP₀) = q^j(q^d + 1 − #E(𝔽_{q^d}))` for `d ≥ 1` (`ManinHasse.gram_orbit_card`). So the count kernel
   of `E` is the Gram kernel of an orbit of a similitude of an integral lattice. A similitude of factor `q` of a
   definite form has its eigenvalues on `|α| = √q` (`ManinHasse.normSq_eq_of_similitude`). That is how such a lattice
   gives the Riemann hypothesis; for `E` the library proves it from the positivity instead
   (`ManinHasse.toeplitz_nonneg`). For `ζ` the analogue in a Hilbert space exists exactly under RH (`BallLattice`):
   vectors `w_r` for the positive rationals and commuting similitudes `φ_n` of factor `n` with `φ_n(w_r) = w_{nr}` and
   Gram kernel `√(ab)·K(a/b)` (`BallLattice.rh_iff_realization`). Under RH one is `ℓ²` of the zeros, where `φ_n`
   multiplies the coordinate of `ρ` by `n^ρ` (`BallLattice.phi_single`). The similitudes alone give a kernel of that
   shape, `⟨w_b, w_a⟩ = b⟨w_1, w_{a/b}⟩` (`BallLattice.gram_shape`), as in rank two (`ManinHasse.gram_orbit`), and an
   eigenvalue `p^ρ` of a similitude of factor `p > 1` has `Re ρ = ½` (`BallLattice.re_eq_half_of_eigen`). The kernel
   of `dh` has no realization (`PsiOmega.not_realization_dh`). But `ℓ²` of the zeros presupposes them, and no
   realization of `K` is a lattice: its orbit spans none (`BallLattice.not_discrete`, under "The real line" above).
   Unlike the counts of `E`, `K` is not built from integers: the explicit formula expresses it through `Λ(n)n^{−1/2}`
   and Gaussians. So for `ζ` "arithmetic" cannot mean integral in the same way, and a lattice needs a kernel that sees
   the primes separately, or one that is not smooth at `1`. The kernel `K_H` with Hadamard's weights `1/(ρ(1 − ρ))`
   is the second kind (`BallHadamard`): RH is its positive-definiteness, and the obstruction does not apply to it. Its
   realizations are not shown to span a lattice. But their gaps `‖w_{n+1} − w_n‖` are unbounded, where for `K` they
   tend to `0` (`BallHadamard.unbounded_gaps`). Each zero with `1 < |γ| ≤ n` adds at least `(2/5)n/(n + 1)²` to
   `‖w_{n+1} − w_n‖²`, and the zeros up to height `T` are not `O(T)` (`ZerosDense.not_linear`). The Riemann–von
   Mangoldt count, which the library does not prove, would give `‖w_{n+1} − w_n‖² ≈ log n`.

   Its explicit formula brings in Chebyshev's `ψ`, the nearest thing for `ζ` to the point counts of `E`
   (`BallPsi.kerH_explicit`). For `x ≥ 1`, with `u = log x`,
   `K_H(x) = cosh(u/2)(2 + γ − log 4π) + sinh(u/2)(log π − 2u) + A(u) + √x·Σ_{n ≤ x} Λ(n)/n − ψ(x)/√x`, with an
   archimedean term `A`. The weights `1/(¼ + γ²)` have poles at the edge of the strip where the library proves the
   explicit formula. Subtracting `cosh(u/2)/(¼ + γ²)`, whose sum over the zeros is Hadamard's identity, removes them.
   So RH holds exactly when a kernel built from the primes is positive-definite (`BallPsi.rh_iff_posDef_psi`). In a
   realization the Gram matrix of the orbit has the prime part `Σ_{kn ≤ m} Λ(k)(m − kn)/k` (`BallPsi.gram_explicit`),
   where that of `E` has the point counts.

   This makes the Gram matrices of `w_1, …, w_N` computable from the primes. The computation takes `A` in a closed form,
   `A(u) = γ·sinh(u/2) + sinh(u/2)·log(4sinh(u/2)) − cosh(u/2)·log cosh(u/2) − (u/2)e^{−u/2}`. The closed form is
   checked numerically against the integral that defines `A`, and is not proved in Lean. The whole formula is the
   classical explicit formula with the kernel `1/(s(s − 1))`, from the residues at `1`, `0`, the zeros and the trivial
   zeros; `scripts/ball_certificate.py` records the derivation. It agrees with the sum over the first 2000 zeros to
   within `10⁻⁴`. `scripts/ball_orbit.py` gives, up to `N = 3000`:
   - The Gram matrices are positive definite, as RH requires.
   - Let `d_k` be the squared distance of `w_k` from the span of `w_1, …, w_{k−1}`. Then `d_k ≥ 1.718·d_1` for
     `2 ≤ k ≤ 3000`, and `d_k` grows, roughly like `1.87·d_1·log²k` for `k` between 1000 and 3000.
   - That growth cannot last. No prime enters `G(k, k − 1)`, as `k/(k − 1) < 2`. So `w_{k−1}` alone leaves `w_k` at
     squared distance `u_k = log(k/2π) + 1 − γ + o(1)`, about `21.6·d_1·(log k − 1.42)`, and `d_k ≤ u_k` whenever
     `G_{k−1}` is positive definite. The pivots grow at most like `log k`, and `1.87·d_1·log²k` would pass `u_k` near
     `k = 2·10⁴`. They bend towards `u_k` instead: `d_k/u_k` is 0.77 at `k = 1000`, 0.85 at 3000 and 0.90 at `10^4`,
     where `d_k = 152·d_1` against `159·d_1` from the fit (`ball_orbit.py 10000`, in 2 minutes).
   - So `w_1, …, w_3000` span a lattice whose shortest nonzero vectors are `±w_1`, of squared length
     `d_1 = K_H(1) = 2 + γ − log 4π ≈ 0.0462` (`BallPsi.orbit_lattice`).
   - The smallest eigenvalue of the Gram matrix tends to `0` (`1.3·10⁻⁴` at `N = 3000`). The form degenerates on the
     space but not on the lattice.

   Up to `N = 10^4` the bound is proved, not only observed (`scripts/ball_certificate.py`):
   - The script encloses every entry of the matrix, computed from the primes by the explicit formula, in interval
     arithmetic with all rounding errors bounded.
   - It bounds the pivots through a congruence `T·G·Tᵀ`, with `T` unit lower-triangular so that the pivots do not
     change, and Gershgorin's theorem.
   - The result: `d_k > d_1` for `2 ≤ k ≤ 10^4`, and `d_k > d_2 = 1.7184·d_1` for `3 ≤ k ≤ 10^4`. Every pivot after
     the second is at least `2.3713·d_1`, the least bound being at `k = 3`.
   - So these matrices are positive definite, unconditionally. The lattice with Gram matrix `G_N`, `N ≤ 10^4`, has the
     first basis vector and its negative as its shortest nonzero vectors (`BallPsi.norm_sq_ge_of_dist`). Under RH this
     is the lattice spanned by `w_1, …, w_N` in any realization of `K_H`.

   So with Hadamard's weights the configuration of step 5 looks like a lattice. The precise statement:

   > **The orbit lattice.** The Gram–Schmidt pivots `d_k` of the matrices `(√(mn)·K_H(m/n))_{m,n ≤ N}`, which
   > `BallPsi.gram_explicit` writes through `ψ`, satisfy `d_k ≥ d_1` for every `k`.

   It holds for `k ≤ 10^4`, by the certificate above.

   It is a statement about the primes. Under RH it says that in every realization of `K_H`, `w_{k+1}` keeps distance
   `‖w_1‖` from the span of `w_1, …, w_k`. The orbit then spans a lattice with `w_1` as a shortest vector
   (`BallPsi.orbit_lattice`). Unconditionally it implies RH (`BallWeil.rh_of_pivots`). Positive pivots make every such
   matrix positive definite, and its `2 × 2` minors at the squares `(p/q)²` are enough for the Landau argument of
   step 5. It asks for more
   than RH, a margin: where RH needs `d_k ≥ 0`, it asks for `d_k ≥ d_1`. It fails for the Gaussian kernel `K`, whose
   gaps tend to `0` (`BallLattice.not_discrete`). It fails for `dh`, whose kernel is not positive-definite
   (`PsiOmega.not_posDefH_dh`). For `E` such a margin comes from integrality: a positive-definite integral form has no
   nonzero vector of norm below `1`. For `ζ` no such reason is known. What remains open is a proof, or the structure
   that would give one. The last section says what a proof under RH would need.

## What a proof under RH would need

The orbit-lattice conjecture of step 6 implies RH, so the question is whether RH implies it. It would then be another
form of RH, and would not by itself prove RH. Four computations locate the difficulty; `scripts/ball_orbit.py`
reproduces them.

- **The flat model is the equality case** (`BallFlat`). Replace the zeros by Lebesgue measure, with the same weights
  `1/(¼ + γ²)`. The kernel becomes `e^{−|log x|/2} = min(√x, 1/√x)` (`BallFlat.kerFlat_eq_integral`), and the orbit's
  Gram matrix becomes `min(m, n)` (`BallFlat.gram_flat`), the covariance of Brownian motion. Its increments
  `w_{n+1} − w_n` are orthogonal, each of squared norm `‖w_1‖²` (`BallFlat.inner_increments`). So the orbit spans a
  copy of the cubic lattice `ℤ^∞` (`BallFlat.telescope`, `BallFlat.norm_sq_lattice`), and every pivot equals `d_1`
  (`BallFlat.flat_pivot`; in `ℓ²`, `BallFlat.flatOrbit_pivot`). Here the conjecture holds with equality, and the
  discretised infinite-dimensional ball is the cubic lattice. The conjecture says that the zeros of `ζ` never do worse
  than Lebesgue measure.
- **The density of the zeros gives a large margin.** Replace the zeros instead by their density `(1/2π)log(|γ|/2π)` on
  `|γ| ≥ 2π`, without the primes (`--smooth`). The pivots become about `k·d_1`: `d_k/d_1` is 2.00, 3.00, 3.95 and 4.88
  at `k = 2, 3, 4, 5`, and 38.8 at `k = 60`.
- **The primes take back part of it.** For `k ≤ 60` the true pivots are 0.59 to 0.86 times those of the density model.
  The ratio is about 0.8 at primes and lowest at numbers with several small prime factors, 0.59 at `k = 30` and 0.62 at
  `k = 60`. This is the correlation of `w_k` with `w_j` when `k/j` is a prime power, through which the zeros see the
  primes, as in Landau's formula `Σ_{0 < γ ≤ T} x^{iγ} ≈ −(T/2π)Λ(x)/√x`. Between 2000 and 3000 the effect is small:
  the pivots at 2310, 2520 and 2880 are about 3% below those at nearby primes.
- **It is not a positivity statement.** The Gram matrix does not dominate that of the flat model: `G − d_1·min(m, n)`
  has negative eigenvalues, −0.44 at `N = 5` and −187 at `N = 100` (`--flat`). The reason is `ζ` itself. At each zero
  the coordinate of `Σ_{m ≤ N} w_m/m` is a partial sum of the series of `ζ(ρ)`, which nearly vanishes, so
  `‖Σ_{m ≤ N} w_m/m‖² = 0.012` at `N = 100`, against 9.0 in the flat model. The form degenerates along real directions,
  and its smallest eigenvalue tends to `0`. The conjecture says that integer combinations cannot follow those
  directions, as the coefficients `1/m` are far from any short integer vector. Whatever gives the margin has to see
  integrality, as for `E`.

Where the pivot is decided (`--zeros`, from the first 2000 zeros): at `k = 2`, 70% of `d_k` comes from zeros above
height `4πk`. At `k = 30`, 80% comes from zeros below `4πk`, and 42% from zeros below `πk`. A proof under RH needs a
lower bound for the pivot that holds uniformly in `k` and allows for the prime-power correlations. The mean-value
theorems for Dirichlet polynomials at the zeros, built on Landau's formula, control `Σ_γ |D(γ)|²` well only where the
zeros sample `D` above the critical rate by a fixed factor. A Dirichlet polynomial of length `k` has bandwidth `log k`,
and the zeros near height `T` have density `(1/2π)log(T/2π)`, so this needs `T ≥ k^{1+ε}`. There the weights
`1/(¼ + γ²)` leave mass of order `log k/k^{1+ε}`, and `k` times that tends to `0`, short of `d_1`. The pivot is decided
at heights comparable to `k`, near the critical rate, where the correlation terms are as large as the main term. So RH,
through the known theorems, does not give the conjecture. A proof would need sharper information about the zeros near
height `k`, in the direction of their pair correlation, or the integral structure behind the lattice that the
conjecture is about. Neither is in hand.

## Building the lattice forwards

A proof along the lines of the conjecture would build the lattice of step 6 from the integers, as Weil's surface is
built from the curve, so that its definiteness has a reason of its own. Concretely, it would give vectors
`v_1, v_2, …`, constructed without the zeros, whose inner products are the Gram matrix of the orbit,
`G(m, n) = √(mn)·K_H(m/n)`. A Gram matrix is positive semidefinite, so such vectors would prove RH
(`BallPsi.rh_iff_posDef_psi`), and the lattice they span would be the object of the conjecture. Three properties of `G`
constrain them (`scripts/ball_orbit.py --places`, with the archimedean term in the closed form above):

- **It is a sum over the places.** For `m ≥ n`, `G(m, n) = Σ_p log p·C_p(m, n) + G_∞(m, n)`, with
  `C_p(m, n) = Σ_{j ≥ 1, p^j n ≤ m} (m/p^j − n) ≥ 0` and
  `G_∞(m, n) = m + n + γm − n·log 2π + m·log n − (m − n)log m + ½(m − n)log(m − n) − ½(m + n)log(m + n)`.
  This is the shape of an intersection number in Arakelov geometry: a local multiplicity at each prime, weighted by
  `log p`, and a term at the real place. The prime part counts integer points:
  `Σ_p log p·C_p(m, n) = Σ_k (Λ(k)/k)·#{t ∈ ℤ : kn < t ≤ m}`.
- **Its positivity needs every prime.** For `N = 60` the archimedean part alone has smallest eigenvalue −983. Adding the
  primes one at a time raises it, and it turns positive only with the last prime, 59; without 59 it is −1.6·10⁻⁴.
- **It needs them exactly.** A fake prime 57, or `log 2` changed by 0.1%, also makes the matrix indefinite. A change of
  0.01% does not.

So the vectors cannot come from the primes approximately or statistically. They have to see each prime and its
logarithm, as an arithmetic surface over `Spec ℤ` sees them through its fibres. A positivity statement of this shape is
an arithmetic Hodge index theorem; Faltings and Hriljac proved one for arithmetic surfaces. For `ζ` the surface would be
the `Spec ℤ × Spec ℤ` that the work under "Related work" looks for, Deninger's height pairings and Connes and Consani's
arithmetic site among it. The conjecture adds what that work does not say: the lattice of such a surface should be a
discretised infinite-dimensional ball, the cubic lattice in the flat model. No construction of these vectors is known.

Building the vectors one place at a time fails in a definite way (`scripts/ball_orbit.py --forward`):

- **No place gives a positive piece.** Each `C_p` has zero diagonal, so it is indefinite: for `p = 2` and `N = 60` its
  eigenvalues run from −489 to 524. The pieces cannot be the Gram matrices of local vectors, one space for each prime.
- **Making them positive costs more than the real place has.** At a prime power `k` the prime part can be completed to
  `Λ(k)/√k` times the Gram matrix of the vectors `1_{[0,n]} − √k·1_{[0,n/k]}` of `L²(0, ∞)`, which is positive. Here
  `⟨1_{[0,a]}, 1_{[0,b]}⟩ = min(a, b)`, as in the flat model. Once `X ≥ N` the rest is exactly
  `G_∞ + (m + n)·Σ_{k ≤ X} Λ(k)/k − 2·min(m, n)·Σ_{k ≤ X} Λ(k)/√k`, where the last sum is about `2√X`. The archimedean
  part cannot pay for that. The rest's smallest eigenvalue is −260 with the prime 2 alone and −2.5·10⁴ with the prime
  powers up to 60, where the whole matrix has 0.0035. The positivity is a cancellation among all the places at once.
- **The lattice does see each prime.** `K_H(r)/K_H(1)` is −0.375, −0.454, −0.453 and −0.442 at `r = 2, 3, 5, 7`; about
  −0.05 at `4` and `8`; and positive at `6`, `10`, `3/2`, `5/2` and `7/2`. So `w_n` and `w_{n/p}` are anti-correlated
  for each small prime `p`, enough that `w_n + w_{n/p}` is shorter than `w_n`. The LLL-reduced basis is then made of
  divisor sums `Σ_{d | n} w_d`: `w_1 + w_2`, `w_1 + w_2 + w_4`, `w_1 + w_3 + w_5 + w_15`,
  `w_1 + w_2 + w_3 + w_4 + w_6 + w_12`, and so on. For `n = Π_p p^{a_p}` such a sum is
  `Π_p (1 + φ_p + ⋯ + φ_p^{a_p}) w_1` in a realization: a truncated Euler factor at each prime, applied to `w_1`. In the
  flat model the reduced basis is the increments `w_{n+1} − w_n` instead. Up to `N = 40` the divisor sums are nearly as
  good as LLL's basis, with Hadamard ratio 0.886 against 0.891. By `N = 200` they are no better than the increments,
  0.703 and 0.712 against 0.754.
- **The real place couples the prime directions.** Independent directions would make `K_H` multiplicative over coprime
  parts: `K_H(ab) = K_H(a/b) = K_H(a)K_H(b)/K_H(1)`. Instead, in units of `K_H(1)`, `K_H(6) = 0.291` and
  `K_H(2/3) = 0.116`, against `K_H(2)K_H(3) = 0.170`. The multiplicative kernel with the exact values at the prime
  powers gives the Gram matrix of the tensor product of the lattices of the single primes. It is positive definite
  here, as each of those lattices is under RH. Its pivots grow roughly in proportion to `k`, to `587·d_1` at
  `k = 1000`, where the true ones grow at most like `log k`, to `89·d_1`. The coupling comes from the real place.
  Integers that are close as real numbers have nearly parallel vectors, `cos(w_997, w_996) = 0.94`, where independent
  directions make them orthogonal. It cuts the pivots by a factor of 0.15 at `k = 1000`, and by more at the primes.
  It does not touch the smallest pivot. `d_2 = 2(1 − K_H(2)²/K_H(1)²)·d_1 = 1.718·d_1` involves only the prime 2,
  and it is the minimum in both.

Slicing the lattice by primes isolates the coupling (`--slices`). The slice of a set `S` of primes is the part of the
lattice spanned by the `w_n` with every prime factor of `n` in `S`, so the directions of `S` alone. Let
`e = d(n)/(n·d_1)` be the pivot as a fraction of `‖w_n‖² = n·d_1`; `e = 1` for a vector orthogonal to the earlier ones.

- **One prime.** The slice `{p^j}` has the Gram matrix `p^{(i+j)/2}·K_H(p^{i−j})`. That is the shape of the Frobenius
  orbit of an elliptic curve over `𝔽_p` (`ManinHasse.gram_orbit_card`), with `K_H(p^j)/K_H(1)` in the place of the
  normalised traces. It is nearly free: `e` runs from 0.86 down to 0.6 for `p = 2, 3, 5` and `p^j ≤ 10^6`, where the
  curve's orbit has `e = 0` after its rank 2. A prime's direction is not determined by that prime and the real place.
  With only `p` in the explicit formula the slice is already indefinite at `p^j = 4` for `p = 2`, and at `p` itself for
  `p = 3, 5`. For instance `⟨w_1, w_3⟩ = G_∞(3, 1) + (log 2)/2` carries the prime 2.
- **Two primes.** The real place couples 2 and 3 through the near-coincidences of their powers. At the Pythagorean
  comma `3^12/2^19 = 1.0136`, `cos(w_{3^12}, w_{2^19}) = 0.573`, against 0.003 for independent directions. Over the
  `{2, 3}`-smooth numbers in `[10^5, 10^6]` the median `e` is 0.29, against 0.52 with the two directions independent.
- **Two primes carry RH.** The logarithms of the slice of two distinct primes `p` and `q` are dense in `ℝ`, as
  `log p/log q` is irrational (`BallSlice.irrational_log_div`). That is all the Landau argument of step 5 needs
  (`BallSlice.re_eq_zero_of_dense_set`). So RH holds if and only if `K_H` is positive-definite on the slice
  (`BallSlice.rh_iff_posDefOn_pair`), and if and only if `K_H(p^a q^b) ≥ −K_H(1)` for all integers `a, b`
  (`BallSlice.rh_iff_bound_pair`; for `2` and `3`, `BallSlice.rh_iff_two_three`). In Weil's terms each of the upper
  Weil bound and Castelnuovo–Severi, for the divisors `D_n` with `n = p^i q^j` alone, is equivalent to RH
  (`BallSlice.rh_iff_weil_bound_pair`, `BallSlice.rh_iff_castelnuovo_severi_pair`). So the conjecture on a single
  two-prime slice is already stronger than RH. One prime would not do: the logarithms of its powers are discrete.
- **More primes.** The median `e` over the top decade of each slice falls as `S` grows:
  - 0.61 for `{2}`, 0.29 for `{2, 3}`, 0.16 for `{2, 3, 5}` and 0.10 for `{2, 3, 5, 7}`, up to `10^6`;
  - 0.073 for the primes up to 31, up to `2·10^4`;
  - 0.064 for all the primes, up to 3000.

  With the directions independent it stays between 0.42 and 0.74.
- **The smallest pivot.** In every slice the smallest pivot is `d_2 = 1.718·d_1`, inside the direction of the prime 2.

So the margin of the conjecture is set in a single prime's direction, at `n = 2`. The coupling between the primes
grows with their number and brings the other pivots down towards it.

So the true lattice lies between two extremes. One is the tensor product of the lattices of the single primes: all
arithmetic, no real place. The other is the flat model, the cubic lattice: all real place, no primes. The conjecture
says that the coupling never brings a pivot below the flat model's. A construction from the integers would have to
produce that coupling, so it cannot be a direct sum of local pieces. It would be something shaped like an Euler
product, a product of local factors, in which the real place ties the primes together.

## Weil's form

The conjecture names the object; Weil's proof says what has to be true on it. In the form that Mattuck and Tate and
Grothendieck gave it, the proof for a curve `C` of genus `g` over `𝔽_q` uses the fibres `e₁ = pt × C` and
`e₂ = C × pt` of `C × C` and the graphs `Γ_k` of the powers of the Frobenius. The Hodge index theorem on `C × C` gives
the Castelnuovo–Severi inequality `D² ≤ 2(D·e₁)(D·e₂)` for every divisor `D`. Applied to the combinations of the
diagonal `Δ = Γ_0` and `Γ_k`, it gives the Hasse–Weil bound. `BallWeil` writes down the same configuration for `ζ`,
with the intersection numbers computed from the primes:

| `C` over `𝔽_q` | `ζ` (`BallWeil`) |
|---|---|
| the fibres `e₁`, `e₂`: `e₁² = e₂² = 0`, `e₁·e₂ = 1` | classes `e₁`, `e₂`, with the same numbers |
| `Γ_k`, of degree `q^k`: `Γ_k·e₁ = 1`, `Γ_k·e₂ = q^k` | `D_n`, `n ≥ 1`: `D_n·e₁ = 1`, `D_n·e₂ = n` |
| `Γ_j·Γ_k = q^j + q^k − √(q^j q^k)·Σ_i (α_i/√q)^{j−k}` for `j ≥ k`, with the Frobenius eigenvalues `α_i` | `D_m·D_n = m + n − √(mn)·K_H(m/n)` (`BallWeil.inter`) |
| `Δ² = 2 − 2g` | `D_1² = 2 − K_H(1)` (`BallWeil.inter_one`), so `K_H(1) = 2 + γ − log 4π` plays `2g` |
| `#C(𝔽_{q^k}) = Γ_k·Δ` | `D_n·D_1 = n + 1 − √n·K_H(n)` |
| `Γ_{i+j}·Γ_{i+k} = q^i·(Γ_j·Γ_k)` | `D_{km}·D_{kn} = k·(D_m·D_n)` (`BallWeil.inter_mul`) |
| `D² ≤ 2(D·e₁)(D·e₂)`, Castelnuovo–Severi, a theorem | equivalent to RH (`BallWeil.rh_iff_castelnuovo_severi`) |
| `D² ≤ 0` when `D·e₁ = D·e₂ = 0`, from the Hodge index theorem | equivalent to RH (`BallWeil.rh_iff_hodge_index`) |
| `\|#C(𝔽_{q^k}) − q^k − 1\| ≤ 2g·q^{k/2}` | `\|D_m·D_n − m − n\| ≤ K_H(1)·√(mn)` under RH (`BallWeil.weil_bound`) |

The equivalences hold for divisors with integer coefficients, as on `C × C`. On the coefficients of the `D_n`,
`2(D·e₁)(D·e₂) − D²` is the form of the Gram matrix of the orbit, and the fibres drop out
(`BallWeil.two_deg_sub_selfInt`). Under RH that form is `‖Σ_n c_n w_n‖²` in a realization (`BallWeil.form_eq_norm_sq`).
In the other direction the divisor `q·D_{p²} + p·D_{q²}` gives the `2 × 2` minor `K_H((p/q)²) ≥ −K_H(1)`. The
logarithms `log(p/q)` are dense, which is all the Landau argument of step 5 needs.

Two differences from the curve case:

- **One side of the Weil bound is enough.** RH holds if and only if `D_m·D_n ≤ m + n + K_H(1)·√(mn)` for all `m`, `n`
  (`BallWeil.rh_iff_weil_bound`), the analogue of an upper bound on the point counts, and the `m`, `n` of the form
  `2^i 3^j` are enough (`BallSlice.rh_iff_weil_bound_pair`). For a curve such an upper bound,
  which Stepanov's method gives, is not enough by itself, and Bombieri derives the lower bound from upper bounds on a
  Galois cover. For `ζ` the upper bound suffices because no zero of `ζ` is real. The poles of the twin form then lie
  off the real axis, and Landau's theorem rules out any of them to the right of it. Numerically
  (`scripts/ball_orbit.py --weil`), `K_H(m/n)/K_H(1)` runs from −0.454 at `m/n = 3` to 0.976 for `m, n ≤ 3000`. So
  the side that gives RH holds there with a factor 2 to spare. The margin is not uniform: if the ordinates of the zeros
  are linearly independent over `ℚ`, Kronecker's theorem brings `K_H(r)` arbitrarily close to `−K_H(1)`.
- **The intersection numbers are real.** `D_1² = 1.9538…` is not an integer, so the `D_n` cannot be divisors on an
  algebraic surface. Intersection numbers on an arithmetic surface are real for the same reason. The real place
  contributes a term that is not an integer, and each prime `p` contributes an integer multiple of `log p`. The
  decomposition of the previous section has this shape, `G = Σ_p log p·C_p + G_∞`, though the `C_p` are rational with
  powers of `p` in their denominators.

The orbit-lattice conjecture implies RH (`BallWeil.rh_of_pivots`), as a statement about the Gram matrix alone. In
Weil's terms it is about the primitive parts `D'_n = D_n − n·e₁ − e₂`, which have `D'_n·e₁ = D'_n·e₂ = 0` and
`−D'_m·D'_n = √(mn)·K_H(m/n)`. The Hodge index theorem asks that `−D²` be a positive semidefinite form on their span.
The conjecture asks that in the norm `√(−D²)` each `D'_k` keep distance `√K_H(1)` from the span of the earlier ones.
In the Arakelov geometry of Euclidean lattices, as hermitian vector bundles over `Spec ℤ` (U. Stuhler, D. Grayson, and
J.-B. Bost's slopes), the flag `F_k = ℤw_1 + ⋯ + ℤw_k` has quotients `F_k/F_{k−1}` of degree `−½ log d_k`. So the
conjecture says that no quotient of the flag has a larger slope than `F_1`.

How this sits with the existing programmes:

- **Finitely many places.** A. Connes's semi-local trace formula (Selecta Math. 5, 1999) restricts Weil's positivity to
  a finite set of places `{∞, 2, …, p}`, where it would still imply RH. The matrices here are in that regime. Their
  entries up to `N` involve exactly the prime powers up to `N`, and "Building the lattice forwards" finds that their
  positivity at `N = 60` needs every prime up to 59.
- **The archimedean place.** A. Connes and C. Consani work out the case of the archimedean place alone. They account
  for the positivity there by the trace of the scaling action, compressed by cutoff projections ("Weil positivity and
  trace formula, the archimedean place", arXiv:2006.13771). In the matrices here no prime enters at `N = 1`, where the
  form is `K_H(1) > 0`. At `N = 60` the archimedean part alone, `G_∞`, has smallest eigenvalue −983, and the primes are
  needed.
- **Integrality.** Connes and Consani also prove a Riemann–Roch theorem for the Arakelov compactification of
  `Spec ℤ`, with integer-valued dimensions ("Riemann–Roch for `Spec ℤ`", arXiv:2205.01391; "Riemann–Roch for the ring
  `ℤ`", arXiv:2306.00456). It is the kind of integrality the margin `d_k ≥ d_1` would need, on the curve rather than
  on the surface.

What the library adds is a statement that is finite and checkable. For each `N`, Castelnuovo–Severi for the divisors
supported on `e₁`, `e₂`, `D_1, …, D_N` is the positivity of an `N × N` matrix computed from the primes up to `N`. RH is
that statement for every `N`.

## The limit and the lattice

**The limit is a Hilbert–Pólya space.** For each `N`, vectors `w_1, …, w_N` with the Gram matrix `G_N` exist exactly
when `G_N` is positive semidefinite. `scripts/ball_certificate.py` proves this for `N ≤ 10^4`. If every `G_N` is, the
Moore–Aronszajn theorem gives the limit: a Hilbert space with a point `w_r` for each positive rational `r`, on the
unit sphere after scaling, and `⟨w_b, w_a⟩ = √(ab)·K_H(a/b)`. That limit exists if and only if RH holds
(`BallHadamard.rh_iff_realizationH`).

- In it each prime acts by a similitude `φ_p` of factor `p` with `φ_p(w_r) = w_{pr}`, so `U_p = φ_p/√p` is a rotation,
  and the rotations commute.
- Under RH, in `ℓ²` of the zeros, `U_n` multiplies the coordinate of `ρ` by `n^{iγ}`. So `U_n = n^{iD}`, with `D` the
  diagonal operator of the ordinates.
- One operator generates all the rotations because of the product formula. The size of `n` is the product of its
  prime powers, so one real `t` fixes the angle `t·log p` of every prime at once.
- An eigenvalue `p^ρ` of a similitude of factor `p` has `Re ρ = ½` (`BallLattice.re_eq_half_of_eigen`).

So the configuration's limit is a Hilbert–Pólya space, and the conjecture adds that the orbit of `w_1` under the
integers is a lattice in it.

**The space of all relationships.** By Ostrowski's theorem the absolute values on `ℚ` are the real one and the `p`-adic
ones, so two integers are close in size or in divisibility by powers of a prime, and in no other way. The adeles hold
all of these at once. The integers sit in them diagonally, which imposes the product formula. Dividing by `ℚ^×` gives
Connes's adele class space. There the explicit formula is a trace formula, and the decomposition of `G` over the places
in "Building the lattice forwards" is its list of local terms.

The outer product over the primes alone, with each prime's direction free, gives the tensor product of the
single-prime lattices of that section. It is positive by Schur's product theorem.

- Its spectral measure is spread over the torus `T^∞ = Π_p T`, one circle for each prime.
- ζ's spectral measure lies on the line `t ↦ (t·log p)_p`, which is the product formula.
- Multiplying in a factor for the real place cannot move a product measure onto that line. In outline: the spectral
  measure of a product of kernels is the convolution of theirs. A convolution with a measure without atoms has no
  atoms, while under RH ζ's measure is atomic, at the zeros.

**The lattice.** The lattice the conjecture is about is the ring `ℤ[x_2, x_3, x_5, …]` of integer Dirichlet
polynomials. In it `x_p` stands for `p^s` and `n` for `x^n = Π_p x_p^{v_p(n)}`, so the ring is the outer product over
the primes of the rings `ℤ[x_p]`. Its inner product is a trace form:

- the involution is `x_p* = p/x_p`, from the functional equation `s ↔ 1 − s`, so that `x_p·x_p* = p`;
- the trace of a positive rational `r` is `Tr(r) = √r·K_H(r)`, computed from the primes. Then `Tr(1) = K_H(1)`, and in
  the terms of `BallWeil` `Tr(n) = n + 1 − D_n·D_1`;
- the form is `⟨x^m, x^n⟩ = Tr(x^m·(x^n)*) = n·Tr(m/n) = √(mn)·K_H(m/n) = G(m, n)`;
- multiplication by `x_p` scales it by `p`, `G(pm, pn) = p·G(m, n)`. That is a Frobenius of norm `p` for each prime.

This is the shape of Weil's first proof, through the Jacobian. For `E` it reads:

- the endomorphism ring of `E`, with the dual isogeny `φ'` as involution;
- the Frobenius `π`, with `ππ' = q`;
- the traces `Tr(π^k) = q^k + 1 − #E(𝔽_{q^k})`;
- the positivity `Tr(φφ') = 2 deg φ > 0`.

For `E` the positivity is free, since the degree of an isogeny is a positive integer. For `ζ`, `Tr(DD*) ≥ 0` for every
real `D` is RH (`BallPsi.rh_iff_posDef_psi`). The conjecture asks more: `Tr(DD*) ≥ Tr(1)` for every
`D = x^k + Σ_{n < k} c_n x^n`. What is missing is the counterpart of the degree: a reading of `Tr(DD*)` as the size of
something attached to `D`, a count or a dimension. The nearest thing is Connes and Consani's Riemann–Roch for `Spec ℤ`,
whose dimensions are integers.

On an arithmetic surface the counterpart exists, and it is a count.
- **Hilbert–Samuel.** For an ample hermitian line bundle `L̄` on an arithmetic surface, the arithmetic Hilbert–Samuel
  theorem (H. Gillet and C. Soulé; A. Abbes and T. Bouche, Ann. Inst. Fourier 45 (1995)) gives
  `log #{sections of nL̄ of norm ≤ 1} = (n²/2)·L̄² + o(n²)`. The self-intersection is the growth rate of the number of
  lattice points in a ball.
- **The Hodge index theorem.** Minkowski's theorem turns a large volume into a nonzero small section. In Faltings's
  treatment this is how the arithmetic Riemann–Roch theorem gives the Hodge index theorem on arithmetic surfaces
  (G. Faltings, Ann. of Math. 119 (1984); P. Hriljac, Amer. J. Math. 107 (1985), proves it through the Néron–Tate
  height). A. Moriwaki derives a generalised Hodge index theorem from the arithmetic volume, which is defined by
  counting small sections ("Continuity of volumes on arithmetic varieties", arXiv:math/0612269).
- **What it asks here.** This is the Riemann–Roch dichotomy that `HodgeAxioms` finds Weil's form lacking
  ([research-opportunities.md](research-opportunities.md), §6.1). Read this way, the missing degree is a growth rate of
  lattice points in balls, a real number, as the intersection numbers here are, rather than an integer dimension. A
  class `D` with `D² > 0` would need lattices `Λ(nD)` whose points in a ball number `exp((n²/2)·D² + o(n²))`, and a
  reason why a nonzero one forces `D·(e₁ + e₂) > 0`. `HodgeCounting` states this route for the divisors of `BallWeil`:
  lattices `Λ(D)` with unit balls `B(D)`, such that a nonzero point of `Λ(D)` in `B(D)` forces `D·(e₁ + e₂) > 0` and,
  when `D² > 0`, the ball of `nD` or of `−nD` exceeds Minkowski's bound for some `n ≥ 1`. Minkowski's theorem then gives
  the Hodge index theorem (`HodgeCounting.hodge_index`), and RH holds exactly when such lattices exist
  (`HodgeCounting.rh_iff_counting`), or lattices whose balls grow like `e^{cn²}` covolumes with rank `O(n)`, the shape
  of the arithmetic Hilbert–Samuel theorem (`HodgeCounting.rh_iff_hilbertSamuel`). The lattices that RH gives back are
  degenerate, so the content is in building them from `D`. The integral quaternions show what the lattices must see:
  they have balls, an Euler product and a functional equation, and no positivity ("What it must survive").

**Its integral structure.** Write each logarithm of an integer in the explicit formula through the logarithms of the
primes. For `m ≥ n` this gives `G(m, n) = (1 + γ)(m + n) − (γ + log 2π)·n + Σ_p log p·Q_p(m, n)`, where
`Q_p(m, n) = Σ_{j ≥ 1, p^j ≤ m/n} (m/p^j − n) + m·v_p(n) − (m − n)·v_p(m) + ½(m − n)·v_p(m − n) − ½(m + n)·v_p(m + n)`.

- So the form takes values in `ℚ + ℚγ + ℚ·log 2π + Σ_p ℚ·log p`.
- Its coefficients are rational numbers made from the relations between `m` and `n`: the powers of `p` that divide
  `m`, `n`, `m − n` and `m + n`, and the powers of `p` below `m/n`. Their denominators are `1`, `2`, powers of `p`
  and twice those.
- The numbers `m − n` and `m + n` come from the archimedean term.
- On the diagonal `Q_2(n, n) = −n` and `Q_p(n, n) = 0` for odd `p`, which is how `G(n, n) = n·K_H(1)` comes out.

`scripts/ball_orbit.py --lattice` checks the identity to `10⁻¹³`, and the similitude. So the lattice is integral over
the logarithms of the primes, and each coefficient records how two integers are related at one prime. As for the
elliptic curve, the open part is the positivity, and no single piece gives it. At `N = 60`, each of `Q_2`, `Q_3`,
`Q_5`, `Q_7`, `Q_59` and `(1 + γ)(m + n) − (γ + log 2π)·min(m, n)` has eigenvalues of both signs.

**The frontier.** At stage `N`, a prime `p ≤ N` has no other multiple up to `N` exactly when `N/2 < p`
(`LonelyPrimes.lonely_iff`). Composites have not yet reached these lonely primes.

- They are never absent (`LonelyPrimes.exists_lonely`, Bertrand's postulate).
- They are asymptotically half of the primes up to `N` (`LonelyPrimes.tendsto_lonely_ratio`, from the prime number
  theorem).
- So they are a fraction bounded below at every stage (`LonelyPrimes.lonely_ratio_pos`). Numerically they are 41% at
  `N = 60`, 44% at 3000, 46% at `10^4` and 47% at `10^6` (`scripts/ball_orbit.py --frontier`).

In the sum over the prime powers in the Gram matrix of stage `N`, a lonely prime `p` enters only the entries
`⟨w_1, w_m⟩` with `p < m ≤ N`, as `log p·(m/p − 1)`. For `m ≥ n ≥ 2` the ratio `m/n` is at most `N/2`, below `p`.

- **Positivity needs each of them.** At `N = 60`, removing any one of the lonely primes 31, …, 59 makes the matrix
  indefinite. Without 31 its smallest eigenvalue is −9.5. Without 59 it is −1.6·10⁻⁴, though 59 enters only
  `⟨w_1, w_60⟩`.
- **Their weight is large.** By the prime number theorem they contribute about `(log 2 − ½)·N ≈ 0.193·N` to
  `⟨w_1, w_N⟩`: 192,928 at `N = 10^6`, where the entry itself is 9.20. Under RH the entry is at most `K_H(1)·√N`.
  Holding the frontier in balance to within `√N` is the size of the error term in the prime number theorem.

So a positive proportion of the prime directions is always the newest. They are held only through `w_1` and the
comparisons of size, and their balance is as delicate as RH.

## The orbit curve

`BallCurve` extends the realization of `BallLattice` from the positive rationals to the positive reals: vectors `w_x`
for real `x > 0`, similitudes `ψ_s` of factor `s` for real `s > 0`, `ψ_s(w_x) = w_{sx}` and
`⟨w_y, w_x⟩ = √(xy)·K(x/y)`. In log coordinates `v_t = e^{−t/2}w_{e^t}` is the orbit of `v_0` under the one-parameter
group of isometries `U_s = e^{−s/2}ψ_{e^s}` (`BallCurve.flow_inner`, `BallCurve.flow_orbit`, `BallCurve.flow_add`).
RH holds exactly when `K` has such a curve realization (`BallCurve.rh_iff_curveRealization`); every one is continuous
and injective on `(0, ∞)` (`BallCurve.continuousOn_kerK`, `BallCurve.injective_kerK`), and at the integers its
increments are nonzero with norms tending to `0` (`BallCurve.not_discrete`). The flow `s ↦ U_s x` is continuous for
every `x` in the closed span of the curve (`BallCurve.flow_continuous_closure`, by an ε/3 argument from
`BallCurve.continuous_of_mem_closure_span`), hence on the whole space when the curve spans densely
(`BallCurve.flow_continuous_of_dense`), and on the whole of `ℓ²` for the model of RH (`BallCurve.flow_continuous_model`).
For an abstract realization it can fail off the closed span: on an orthogonal summand `ℂ` the definition allows `U_s`
to act by any character of `ℝ`, including a discontinuous one built from a Hamel basis.

Whether the curve spans `ℓ²` densely in the model is, under RH, exactly the simple-zeros conjecture. This is a
written argument, not in Lean.
- Why multiplicity matters. `ZIdx` counts a zero of multiplicity `m` with `m` indices, and every `w_x` has equal
  coordinates at those indices. So if some zero is multiple, `e_q − e_{q′}` for two of its indices `q ≠ q′` is
  orthogonal to the whole curve.
- The converse. Suppose every zero is simple and `y` is orthogonal to every `w_x`. Then
  `0 = ⟪w_{e^t}, y⟫ = e^{t/2} Σ_q a_q e^{−iγ_q t}` for all real `t`, where `a_q = \overline{c_q}\,y_q` and
  `c_q = e^{(ρ_q−½)²/4}`. These coefficients are absolutely summable, since `c, y ∈ ℓ²`, and the frequencies `γ_q`
  are distinct. So Bohr's mean value `a_q = lim_T (1/2T)∫_{−T}^{T} f(t)e^{iγ_q t}dt` gives every `a_q = 0`, hence
  `y = 0` because `c_q ≠ 0`.
- The same holds for the rational orbit of `BallLattice`, since `x ↦ ⟪w_x, y⟫` is continuous.

`flow_continuous_model` does not need density. Not proved: anything about lattices spanned by points of the curve
other than the integers.

## Tests

[ball-conjecture-tests.md](ball-conjecture-tests.md) collects:
- the closed form of `K_H` (the derivation that `scripts/ball_certificate.py` records), and its Dirichlet analogue;
- an exact criterion for `d_2 ≥ d_1`;
- an independent cross-check in ball arithmetic of the bound `d_k > d_1` for ζ, at `k ≤ 500`, inside the range
  `k ≤ 10^4` that `scripts/ball_certificate.py` proves (step 6);
- a function-field analogue, where a null vector is forced at `k = q^{2g}`;
- Dirichlet characters for which `d_2 < d_1` (for example χ mod 19 and χ₋₁₆₃);
- results on the smallest eigenvalue of the orbit Gram matrix (it is positive definite under RH, with `λ_min ≪ log²N/N`).

The scripts are in `scripts/ball_tests/`.
