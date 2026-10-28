# Formalisations

A paper in this repository claims only its own results. When a paper uses a result from the literature, that result
is formalised in `lib/` and documented here. Each note gives:

- the source;
- the Lean statement;
- how the Lean statement differs from the source's;
- how the formalisation was done.

The paper cites the note and does not restate the result as its own.

## Index

| Result | Source | Lean | Used by | Note |
|---|---|---|---|---|
| No zero of any Dirichlet `L`-function in `Re s > 11/12`, the pole at `s = 1` excepted | OpenAI, `github.com/openai/math`, entry 003 (the companion preprint of 5 October 2026) | `Eis.LFunction_ne_zero_of_re_gt` | The Linnik exponent paper. One use is the top bin of the Type II estimate (`SieveTypeII.bin_rect`). | [openai-half-plane.md](openai-half-plane.md) |
| At most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `\|Im s\| ≤ T`, for `5/7 ≤ σ ≤ 16/21` | B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296v2 | `LinnikCGLDensity.cglDensity`, which proves `LinnikCGL.CGLDensity` | The Linnik exponent paper: `Linnik22240R.linnik_22240r` uses the step `LinnikCGLStep.charDensity_cglGen`; the earlier `899/400` route, which applied `cglDensity`, is in the git history | [chen-gupta-li-density.md](chen-gupta-li-density.md) |
| Ingham's zero-density estimate over the characters mod `q`, with a constant exponent on each step | A. E. Ingham, Quart. J. Math. 11 (1940); H. L. Montgomery, *Topics in Multiplicative Number Theory* (1971), Theorem 12.1 | `LinnikInghamC.charDensity_ingham_c` | The density curve of the Linnik paper's Type II estimate, on `[4/7, 5/7]` | [ingham-density.md](ingham-density.md) |
| Huxley's zero-density estimate over the characters mod `q`, with a constant exponent on each step | M. N. Huxley, Invent. Math. 15 (1972) and Acta Arith. 26 (1975) | `LinnikHuxStep.charDensity_gen`, `LinnikStep.charDensity_step` | The same curve, on `[131/168, 1]` | [huxley-density.md](huxley-density.md) |
| The Halász–Montgomery inequality over the characters mod `q` | G. Halász, Acta Math. Acad. Sci. Hungar. 19 (1968); H. L. Montgomery, Invent. Math. 8 (1969) | `LinnikPower.hm_duality` | Huxley's estimate, and the top piece `[5/6, 11/12]` of the Type II estimate (`SieveHMBin`) | [halasz-montgomery.md](halasz-montgomery.md) |
| The hybrid fourth moment of `L(1/2 + it, χ)`, at one point per character | H. L. Montgomery, *Topics in Multiplicative Number Theory* (1971) | `LinnikFourth.fourth_moment` | Ingham's and Huxley's estimates | [hybrid-fourth-moment.md](hybrid-fourth-moment.md) |
| Mean values of Dirichlet polynomials over the characters mod `q`, and Gallagher's lemma | H. L. Montgomery and R. C. Vaughan, J. London Math. Soc. 8 (1974); P. X. Gallagher, Mathematika 14 (1967) and Invent. Math. 11 (1970) | `LinnikHybrid.mean_value_chars`, `LinnikHybrid.large_values_chars` | Ingham's and Huxley's estimates, and the fourth moment | [mean-values.md](mean-values.md) |
| Harman's sieve in the form used, with Brun's fundamental lemma and Buchstab's identity | G. Harman, J. London Math. Soc. 27 (1983) and *Prime-Detecting Sieves* (2007); V. Brun (1920); A. A. Buchstab, Mat. Sb. 2(44) (1937) | `SieveProp6.prop6`, `SieveBrun.fundamental` | The leaves of the Linnik paper's decomposition (`SieveLeaves`) | [harman-sieve.md](harman-sieve.md) |
| Kubota's cubic theta function, with Patterson's coefficients, in the form the half-plane's route uses | T. Kubota (1969); S. J. Patterson, J. Reine Angew. Math. 296 (1977); A. Dunn and M. Radziwiłł, Ann. of Math. 200 (2024) | `Eis.kubotaTheta`, which proves `Eis.KubotaTheta` | The zero-free half-plane (`Eis.thetaRows_of_kubota`) | [cubic-theta.md](cubic-theta.md) |
| The quadratic large sieve over `ℤ[ω]` | D. R. Heath-Brown, Acta Arith. 72 (1995); L. Goldmakher and B. Louvel, Math. Proc. Cambridge Philos. Soc. 154 (2013) | `Eis.quadLargeSieve`, which proves `Eis.QuadLargeSieve` | The zero-free half-plane (the companion preprint's Lemma 6.5) | [quadratic-large-sieve.md](quadratic-large-sieve.md) |

The Chen–Gupta–Li note also covers the paper's Theorem 10.1, which they state for primitive characters and credit to
Heath-Brown. Heath-Brown's paper could not be read, so the library proves the theorem (`LinnikCGLHB101.cglt101`) by
combining two other sources. It is documented with the rest of the formalisation of their paper, and no paper here
claims it.

## The density curve

The Type II estimate of the Linnik paper counts characters by a density curve, `g7d`
(`SieveTypeIIU22240D.counts_7d`). It is glued from these pieces:

- the trivial count below `4/7`;
- Ingham's estimate, on twenty steps of `[4/7, 5/7]` ([ingham-density.md](ingham-density.md));
- Chen–Gupta–Li's estimate, on 110 steps of `[5/7, 131/168]` ([chen-gupta-li-density.md](chen-gupta-li-density.md));
- Huxley's estimate, on fifteen steps of `[131/168, 5/6]`, and with the exponent `101/50` from `5/6` on
  ([huxley-density.md](huxley-density.md)).

Each piece counts characters, not zeros.

## Standard results

The proof of `Linnik22240R.linnik_22240r` also uses textbook results. The library proves them, or takes them from
Mathlib, and no note covers them:

- Perron's formula with a smooth weight, and the shifting of vertical contours (`Linnik.perron_exp`,
  `SmoothPerron.verticalIntegral_shift`);
- bounds for logarithmic derivatives in zero-free discs, through the Borel–Carathéodory inequality
  (`LogDerivDisc.logDeriv_le_Kld`);
- a Lindelöf-type bound in the zero-free half-plane (`LinnikLindelof.lindelof`);
- the prime number theorem with the error term that a zero-free half-plane gives
  (`HalfPlanePNT.psi_isBigO_of_zeroFree`). Its proof needs a zero of `ζ` with real part at least `1/2`
  (`PsiOmega.exists_zero_re_ge_half`), which the library derives from Hadamard's product for `ξ`
  (`WeilForm.hadamardW_Xi`, `WeilForm.hadamard_zeta`);
- the functional equation of Dirichlet `L`-functions (Mathlib's), and bounds for the Gamma function on vertical lines
  (`LinnikGamma`, `LinnikReflect`, and Gauss's and Binet's integrals for the digamma function in `GammaIntegrals`);
- the divisor bound `d(n) ≤ C(ε)n^ε` (`LinnikPower.card_divisors_le`);
- the separation of variables by Fourier and Mellin inversion (`MellinSep`, `SieveSep`);
- Dirichlet's theorem on primes in progressions, for the moduli below the route's threshold (Mathlib's
  `Nat.forall_exists_prime_gt_and_modEq`).

The zero-free half-plane's route ([openai-half-plane.md](openai-half-plane.md)) uses, besides the theta function and
the large sieve of the index, these classical results:

- cubic reciprocity in `ℤ[ω]` (`Eis.cub_recip`), by the Jacobi- and Gauss-sum proof of K. Ireland and M. Rosen's
  *A Classical Introduction to Modern Number Theory* (Springer, 1990), Chapter 9, and its supplementary laws as
  periodicity modulo `9` (`EisensteinSupplement`);
- quadratic and sextic reciprocity in `ℤ[ω]` (`Eis.quad_recip`, `Eis.sextic_recip`), from quadratic Gauss sums as in
  the companion preprint's Appendix A.1, with their supplementary laws (`EisensteinQuadSupplement`);
- Gauss sums and Poisson summation over `ℤ[ω]` and in the plane (`EisensteinGaussSum`, `EisensteinQuadGauss`,
  `EisensteinPoisson`, `PlanePoisson`, `PlaneGaussian`);
- the Bessel function `K_ν` and its Mellin transform (`BesselK`, `KubotaBesselMellin`);
- hyperbolic three-space: the action of `SL_2(ℂ)`, the invariant measure, reduction theory for `SL_2(ℤ[ω])` and
  unfolding (`UpperHalfSpace`, `KubotaMeasure`, `KubotaSiegel`, `KubotaUnfold`), as Dunn and Radziwiłł's §5.1 sets
  them out after J. Elstrodt, F. Grunewald and J. Mennicke's *Groups Acting on Hyperbolic Space* (Springer, 1998);
- resolvents of self-adjoint operators (`HilbertResolvent`);
- the ideals of `ℤ[ω]` by norm, the Möbius function on them, and the Dedekind zeta function of a quadratic field
  (`EisensteinIdealCount`, `EisensteinMobius`, `QuadIdeals`).

These lists come from a census of the declarations that the proof of `Linnik22240R.linnik_22240r` uses
(`scripts/census.py`), read module by module.

## The vendored libraries

`lib/vendor/` holds two upstream Lean libraries, each with its license, its upstream commit and the patch that ports
it to this repository's Lean and Mathlib:

- PrimeNumberTheoremAnd (`lib/vendor/pnt-plus`);
- `zeta23` of `anthropics/formal-math` (`lib/vendor/zeta23`).

Their results are those projects' own, and the notes above do not cover them.
