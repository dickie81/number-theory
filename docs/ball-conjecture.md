# The discretised infinite ball: a research direction

A conjecture of the library's author, recorded here as a direction for work. No theorem of the library proves it or
tests it yet. This page says what it claims, what is proved in the finite-rank cases it generalises, what the library
already has towards it, what any version of it must survive, and the first steps.

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
  in `E × E`.
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
discrete structure whose definiteness would force them there.

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
5. **The statement for `ζ`.** Replace the Frobenius powers, indexed by `ℤ`, by the positive rationals `ℚ₊^× ≅ ℤ^{(∞)}`,
   with a direction for each prime. Replace `c_k` by the kernel `K(r) = Σ_ρ ĥ(γ_ρ) r^{iγ_ρ}`, where `ρ = 1/2 + iγ_ρ` and
   `h` is a Gaussian; the explicit formula computes `K` from the primes. RH holds exactly when `K` is positive-definite
   on `ℚ₊^×`: the positive rationals then sit on a sphere in a Hilbert space, with `K` for their inner products. That
   equivalence is Weil's criterion restated. The conjecture is that this configuration is an arithmetic definite
   lattice, as the twist's lattice is for `E`. It comes with a test. The Davenport–Heilbronn function's kernel is
   unbounded, as its zeros leave the line, so it is not positive-definite; a candidate has to use unique factorisation,
   which is what `ℤ^{(∞)}` encodes. By the purity test it has to use more: unique factorisation is also what Beurling's
   generalised integers have.
