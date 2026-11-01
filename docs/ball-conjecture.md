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

## Related work

None of the following states the conjecture in this form; a search in October 2026 found no statement of it.

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
  `k = 1000`, where the true ones grow like `log²k`, to `89·d_1`. The coupling comes from the real place. Integers
  that are close as real numbers have nearly parallel vectors, `cos(w_997, w_996) = 0.94`, where independent
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
