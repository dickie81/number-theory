# Formalisations

A paper in this repository claims only its own results. When a paper uses a result from the literature, that result
is formalised in `lib/` and documented here. A few results from the literature that the library formalises for their
own sake, with no paper using them, are documented here too; the index says so. Each note gives:

- the source;
- the Lean statement;
- how the Lean statement differs from the source's;
- how the formalisation was done.

The paper cites the note and does not restate the result as its own.

## Index

| Result | Source | Lean | Used by | Note |
|---|---|---|---|---|
| No zero of any Dirichlet `L`-function in `Re s > 11/12`, the pole at `s = 1` excepted | OpenAI, `github.com/openai/math`, entry 003 (the companion preprint of 5 October 2026) | `Eis.LFunction_ne_zero_of_re_gt` | The Linnik exponent paper. One use is the top bin of the Type II estimate (`SieveTypeII.bin_rect`). | [openai-half-plane.md](openai-half-plane.md) |
| At most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `\|Im s\| ≤ T`, for `5/7 ≤ σ ≤ 16/21` | B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296v2 | `LinnikCGLDensity.cglDensity`, which proves `LinnikCGL.CGLDensity` | The Linnik exponent paper: `Linnik22000E.linnik_22000e` uses the step `LinnikCGLStep.charDensity_cglGen`; the earlier `899/400` route, which applied `cglDensity`, is in the git history | [chen-gupta-li-density.md](chen-gupta-li-density.md) |
| Ingham's zero-density estimate over the characters mod `q`, with a constant exponent on each step | A. E. Ingham, Quart. J. Math. 11 (1940); H. L. Montgomery, *Topics in Multiplicative Number Theory* (1971), Theorem 12.1 | `LinnikInghamC.charDensity_ingham_c` | The density curve of the Linnik paper's Type II estimate, on `[4/7, 5/7]` | [ingham-density.md](ingham-density.md) |
| Huxley's zero-density estimate over the characters mod `q`, with a constant exponent on each step | M. N. Huxley, Invent. Math. 15 (1972) and Acta Arith. 26 (1975) | `LinnikHuxStep.charDensity_gen`, `LinnikStep.charDensity_step` | The same curve, on `[131/168, 1]` | [huxley-density.md](huxley-density.md) |
| The Halász–Montgomery inequality over the characters mod `q` | G. Halász, Acta Math. Acad. Sci. Hungar. 19 (1968); H. L. Montgomery, Invent. Math. 8 (1969) | `LinnikPower.hm_duality` | Huxley's estimate, and the top piece `[5/6, 11/12]` of the Type II estimate (`SieveHMBin`) | [halasz-montgomery.md](halasz-montgomery.md) |
| The hybrid fourth moment of `L(1/2 + it, χ)`, at one point per character | H. L. Montgomery, *Topics in Multiplicative Number Theory* (1971) | `LinnikFourth.fourth_moment` | Ingham's and Huxley's estimates | [hybrid-fourth-moment.md](hybrid-fourth-moment.md) |
| Mean values of Dirichlet polynomials over the characters mod `q`, and Gallagher's lemma | H. L. Montgomery and R. C. Vaughan, J. London Math. Soc. 8 (1974); P. X. Gallagher, Mathematika 14 (1967) and Invent. Math. 11 (1970) | `LinnikHybrid.mean_value_chars`, `LinnikHybrid.large_values_chars` | Ingham's and Huxley's estimates, and the fourth moment | [mean-values.md](mean-values.md) |
| Harman's sieve in the form used, with Brun's fundamental lemma and Buchstab's identity | G. Harman, J. London Math. Soc. 27 (1983) and *Prime-Detecting Sieves* (2007); V. Brun (1920); A. A. Buchstab, Mat. Sb. 2(44) (1937) | `SieveProp6.prop6`, `SieveBrun.fundamental` | The leaves of the Linnik paper's decomposition (`SieveLeaves`) | [harman-sieve.md](harman-sieve.md) |
| Kubota's cubic theta function, with Patterson's coefficients, in the form the half-plane's route uses | T. Kubota (1969); S. J. Patterson, J. Reine Angew. Math. 296 (1977); A. Dunn and M. Radziwiłł, Ann. of Math. 200 (2024) | `Eis.kubotaTheta`, which proves `Eis.KubotaTheta` | The zero-free half-plane (`Eis.thetaRows_of_kubota`) | [cubic-theta.md](cubic-theta.md) |
| The quadratic large sieve over `ℤ[ω]` | D. R. Heath-Brown, Acta Arith. 72 (1995); L. Goldmakher and B. Louvel, Math. Proc. Cambridge Philos. Soc. 154 (2013) | `Eis.quadLargeSieve`, which proves `Eis.QuadLargeSieve` | The zero-free half-plane (the companion preprint's Lemma 6.5) | [quadratic-large-sieve.md](quadratic-large-sieve.md) |
| Zero density for `ζ` with Guth and Maynard's exponent `30/13`, and the classical `12/5`, with primes in short intervals for `θ > 17/30` and in almost all for `θ > 2/15` | L. Guth and J. Maynard, Ann. of Math. 203 (2026); A. E. Ingham, Quart. J. Math. 11 (1940); M. N. Huxley, Invent. Math. 15 (1972) | `ZetaGMDensity.densityXi_thirty_thirteenths`, `ZetaGMLV.gm_large_values`, `ZetaGMDensity.short_primes_seventeen_thirtieths`, `ZetaGMDensity.almost_all_short_primes_two_fifteenths` | No paper: a result of the library | [zeta-density.md](zeta-density.md) |
| The Davenport–Heilbronn function, a combination of two Dirichlet `L`-functions mod 5 with the functional equation of `ζ`: its zeros off the critical line, four of them located, and its columns of the library's criteria for RH | H. Davenport and H. Heilbronn, J. London Math. Soc. 11 (1936); E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §10.25 | `PsiOmega.dh_offline_zero`, `PsiOmega.Locate.dh_zeros_located_four_box` | No paper | [davenport-heilbronn.md](davenport-heilbronn.md) |
| Primes in `(x − x^{13/25}, x]` for large `x`, after R. Li: in progress, the lower bound from loss bounds on the certificate's root cells and the certificate's decisions | R. Li, arXiv:2308.04458v8; R. C. Baker, G. Harman and J. Pintz, Proc. London Math. Soc. 83 (2001) | `ShortSieveThree.primes_of_cells` | No paper: work in progress | [short-intervals.md](short-intervals.md) |

The Chen–Gupta–Li note also covers the paper's Theorem 10.1, which they state for primitive characters and credit to
Heath-Brown. Heath-Brown's paper could not be read, so the library proves the theorem (`LinnikCGLHB101.cglt101`) by
combining two other sources. It is documented with the rest of the formalisation of their paper, and no paper here
claims it.

## The density curve

The Type II estimate of the Linnik paper counts characters by a density curve, `g7d`
(`SieveCurve7D.counts_7d`). It is glued from these pieces:

- the trivial count below `4/7`;
- Ingham's estimate, on twenty steps of `[4/7, 5/7]` ([ingham-density.md](ingham-density.md));
- Chen–Gupta–Li's estimate, on 30 steps of `[5/7, 131/168]` ([chen-gupta-li-density.md](chen-gupta-li-density.md));
- Huxley's estimate, on fifteen steps of `[131/168, 5/6]`, and with the exponent `101/50` from `5/6` on
  ([huxley-density.md](huxley-density.md)).

Each piece counts characters, not zeros.

## Standard results

The proof of `Linnik22000E.linnik_22000e` also uses textbook results. The library proves them, or takes them from
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

These lists come from a census of the declarations that the proof of the theorem at `278/125` used
(`Linnik22240R.linnik_22240r`, now in the git history; `scripts/census.py`), read module by module. The theorem at
`11/5` takes the same route, with the bilinear Type I estimate and the decomposition to depth 8 added.

## Results that no paper uses

The library proves results that no paper uses, and each is named here or in a note, so that it is accounted for.
`scripts/dead_code.py`, which CI runs, requires every theorem that the check files print, and that no other printed
theorem uses, to be one of the papers' results (`lib/check/Check.lean`), on the page on the zeros, or named in
`formalisations/`; and it requires every other declaration of the library to be used by one of them. A result here
needs no hypothesis unless the next section lists it; "the half-plane" is Input 1 of the Linnik paper, `Re s > 11/12`
for every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`), and `Θ` is the supremum of the real parts of the
nontrivial zeros of `ζ` (`PsiExponent.Theta`).

| Result | Lean | Source |
|---|---|---|
| The prime number theorem with the Korobov–Vinogradov error term, `ψ(x) = x + O(x·exp(−c(log x)^{3/5}(log log x)^{−1/5}))`; zero-free regions of width `(log t)^{−n}` for every `n > 2/3`, with the error terms they give; the growth bound behind them, and Vinogradov's mean value theorem in a weak form | `PNTKV.PNT_KV`, `KVBridge.zeroFree_kv`, `KVBridge.rung3_kv`, `KVBridge.polylogGrowth_kv`, `VinoRec.vmvt_weak` | N. M. Korobov and I. M. Vinogradov (1958); Vinogradov's mean value theorem (1935) |
| Primes in short intervals `(y, y + y^θ]` for every `θ > 2Θ/(1 + 2Θ)` | `InghamDensity.short_primes_Theta` | the method of G. Hoheisel (1930) and A. E. Ingham (1937) |
| The exponents of the errors: `limsup log\|ψ(x) − x\|/log x = Θ`, the same for Mertens' function `M(x)`, and the abscissa of convergence of `Σ μ(n)n^{−s}` is `Θ`; from the half-plane, `M(x) = O(x^{11/12+η})`, and `Σ_{n ≤ x} χ(n)μ(n) = O(x^{11/12+η})` for each character `χ ≠ 1` | `PsiExponent.limsup_expo`, `MertensExponent.limsup_mexpo`, `MertensExponent.moebiusAbscissa_eq_Theta`, `MertensExponent.mertens_isBigO_eleven_twelfths`, `MertensChi.isBigO` | classical; the bounds at `11/12` from the half-plane |
| Littlewood's criterion: RH holds if and only if `M(x) = O(x^{1/2+η})` for every `η > 0` | `MertensExponent.rh_iff_mertens` | J. E. Littlewood (1912) |
| The divisor problems, `Σ_{n ≤ x} d_k(n) = xP_k(log x) + O(x^{θ+η})` at `θ = Θ` and at `θ = 11/12`, with `P_k` of degree `k − 1`; the squarefree numbers, `Q(x) = 6x/π² + O(x^{1/(3−θ)+η})` at `θ = Θ`, and with the exponent `12/25 + η` from the half-plane | `DivisorExponent.divisor_isBigO_Theta`, `DivisorExponent.divisor_isBigO_eleven_twelfths`, `DivisorExponent.natDegree_Pk_eq`, `SquarefreeCount.squarefree_isBigO_Theta`, `SquarefreeCount.squarefree_isBigO_twelve_25ths` | classical arguments from a zero-free half-plane |
| The prime number theorem modulo every `q`, `ψ(x; q, a) = x/φ(q) + O(x^{11/12+η})` for every `a` prime to `q`; a Lindelöf bound, `ζ(s)` and `1/ζ(s)` at most `C\|t\|^ε` on `Re s ≥ σ₀`, for every `σ₀ > Θ` and every `σ₀ > 11/12` | `PNTProgressions.psiAP_isBigO`, `HalfPlaneLindelof.zeta_bound_Theta`, `HalfPlaneLindelof.zeta_bound_eleven_twelfths` | classical arguments, with the half-plane |
| The strip bound from a critical-line bound: if `ζ(s) ≠ 0` on `Re s > θ` and `\|ζ(1/2 + it)\| ≪ \|t\|^c`, then `\|ζ(σ + it)\| ≪ \|t\|^{c(θ − σ)/(θ − 1/2) + ε}` on `1/2 ≤ σ ≤ θ`; at `θ = 11/12`, from the half-plane, `\|t\|^{(12/5)c(11/12 − σ) + ε}`, below the strip bound's `(11/12 − σ)/2` for every `c < 5/24` | `Subconvexity.zeta_strip_of_crit`, `Subconvexity.zeta_strip_eleven_twelfths_of_crit` | the convexity principle of Phragmén and Lindelöf (E. Lindelöf, 1908), between the critical line and the Lindelöf bound right of `θ` |
| Littlewood's bounds for `L(1, χ)` at the quadratic characters `χ ≠ 1` mod `q`: `1/log log q ≪ \|L(1, χ)\| ≪ log log q` and `L′/L(1, χ) ≪ log log q` | `Littlewood.norm_LFunction_one_ge`, `Littlewood.norm_LFunction_one_le`, `Littlewood.norm_logDeriv_one_le` | J. E. Littlewood (1928), under GRH; here from the half-plane |
| Quadratic fields: the class number of an imaginary field, and the class number times the regulator of a real one, between `c√\|D\|/log log \|D\|` and `C√\|D\| log log \|D\|`; a split and an inert prime below `C_A(log \|D\|)^A` for every `A > 12`, and below `10^{298}(log \|D\|)^{13}`; the Euler–Kronecker constant; every prime splits, is inert or ramifies | `QuadClassNumber.classNumber_ge_loglog`, `QuadClassNumber.classNumber_le`, `QuadClassNumber.regulator_mul_classNumber_ge_loglog`, `QuadClassNumber.regulator_mul_classNumber_le`, `QuadClassNumber.exists_split_le`, `QuadClassNumber.exists_split_le_13`, `QuadClassNumber.exists_inert_le`, `QuadClassNumber.exists_inert_le_13`, `QuadClassNumber.eulerKronecker`, `QuadIdeals.trichotomy` | J. E. Littlewood (1928) for the class numbers, under GRH; here from the half-plane |
| The least quadratic non-residue: below `C_δ p^δ` for every odd prime `p` and every `δ > 0`, Vinogradov's conjecture, also with explicit constants; for every character `χ ≠ 1` mod `q`, a prime `p ≤ C(log q)^A` with `χ(p) ≠ 1`, for every `A > 12` | `LeastNonresidue.exists_nonsquare_le_rpow`, `ExplicitConstants.exists_nonsquare_le_rpow_explicit`, `LeastNonresidue.exists_prime_ne_one` | the argument of N. C. Ankeny (1952), under GRH; here from the half-plane |
| The small primes generate the units mod `q`: every proper subgroup of `(ℤ/qℤ)ˣ` misses the class of a prime `p ≤ C(log(q + 2))^A` prime to `q`, for every `A > 12`, so these primes generate `(ℤ/qℤ)ˣ`; and for a prime `p` and every `k ≥ 2` dividing `p − 1`, a prime `ℓ ≤ C(log(p + 2))^A` that is not a `k`-th power mod `p` | `SmallPrimes.exists_prime_not_mem`, `SmallPrimes.closure_primes_eq_top`, `SmallPrimes.exists_prime_not_pow` | N. C. Ankeny (1952) and E. Bach (1990), under GRH and with `(log q)²`; here from the half-plane |
| Gauss's class number problem with an explicit bound: `\|D_K\| ≤ (320π e^{2·10²¹} h_K)⁴` for every imaginary quadratic field `K` | `ClassNumberBound.abs_discr_le` | C. F. Gauss's conjecture, proved by H. Heilbronn (1934); a bound polynomial in `h_K` is what GRH gives, here from the half-plane |
| The Madelung constant of the square lattice: `Σ_{n ≥ 1} (−1)^n r₂(n) n^{−s} = −4(1 − 2^{1−s}) ζ(s) L(s, χ₋₄)` on `Re s > 1`, with the right side holomorphic off `s = 1`; at `s = 1/2` it is minus the electrostatic energy of an ion of a two-dimensional ionic crystal | `Madelung.lseries_coeff`, `Madelung.differentiableOn_rhs` | classical, from Jacobi's two-square theorem: J. M. Borwein, M. L. Glasser, R. C. McPhedran, J. G. Wan and I. J. Zucker, *Lattice Sums Then and Now* (2013); no hypothesis and no use of the half-plane |
| The band for every Dirichlet `L`-function: every zero `ρ` of `L(s, χ)`, `χ ≠ 1`, with `0 < Re ρ < 1` has `1/12 ≤ Re ρ ≤ 11/12`; the twin forms of `L(s, χ₋₄)`, `L(s, χ₋₈)`, `ζ·ζ_{ℚ(i)}`, of `L(s, χ)` and `ζ·L(s, χ)` for every good `χ` with no real zero in `(0, 1)`, and of `ζ` at every real-rooted monotone base probe are at least `−Ce^{5λ/6}` | `HalfPlaneJoins.LFunction_band_eleven_twelfths`, `HalfPlaneJoins.chi4_rate_eleven_twelfths`, `HalfPlaneJoins.chi8_rate_eleven_twelfths`, `HalfPlaneJoins.QK4_rate_eleven_twelfths`, `HalfPlaneJoins.QC_rate_eleven_twelfths`, `HalfPlaneJoins.QKχ_rate_eleven_twelfths`, `HalfPlaneJoins.realRooted_rate_eleven_twelfths` | the half-plane with the functional equation of a primitive character |
| Integer points in balls: the points of `ℤⁿ` in the ball of radius `R` number `V_n Rⁿ(1 + o(1))`, `V_n = π^{n/2}/Γ(n/2 + 1)`, and the counted volume is largest in dimension 5; in the plane they give the residue `π/4` of `ζ(s)L(s, χ₋₄)` at `s = 1`, so `L(1, χ₋₄) = π/4` | `BallTower.count_div_pow_tendsto_ballVol`, `BallTower.counted_volume_max_five`, `AngularResidue.residue_angular`, `AngularResidue.LFunction_chi4_one` | Gauss's circle problem in its first form; G. W. Leibniz's series |
| The local densities of sums of squares: over a finite field of odd size `q`, `x² + y² = a` has `q − χ₋₄(q)` solutions for `a ≠ 0`, and `x² + y² + z² + w² = a` has `q³ − q` | `LocalTeeth.card_two_sq`, `LocalTeeth.card_four_sq`, `LocalTeeth.teeth_mod_prime` | the local factors of the formulas of Jacobi and Siegel, by Jacobi sums |
| Hasse's bound for the curves `y² = x³ + D`: over a finite field `𝔽_q` of characteristic neither 2 nor 3, `#E(𝔽_q) = q + 1` if `q ≡ 2 (mod 3)`, and `q + 1 − #E(𝔽_q) = 2u − v` with `u² − uv + v² = q` if `q ≡ 1 (mod 3)`, the Frobenius being the Eisenstein integer `u + vω`; so `\|q + 1 − #E(𝔽_q)\| ≤ 2√q`, counted with Mathlib's `WeierstrassCurve` | `HasseEisenstein.card_points_of_mod_three_eq_two`, `HasseEisenstein.exists_eisenstein_trace`, `HasseEisenstein.abs_trace_le` | H. Hasse (1936) for every elliptic curve; for these curves the count by Jacobi sums is classical (K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 18) |
| Hasse's bound for every elliptic curve over a finite field of odd characteristic: `(q + 1 − #E(𝔽_q))² ≤ 4q`, so `\|q + 1 − #E(𝔽_q)\| ≤ 2√q`, for every `WeierstrassCurve` `E` with `[E.IsElliptic]` over `𝔽_q`, `q` odd, counted with Mathlib's points. On the twist `y² = x³ + a₂sx² + a₄s²x + a₆s³` over `𝔽_q(t)`, `s = f(t)`, the degree of `x/s` satisfies `deg(P + P₀) + deg(P − P₀) = 2 deg P + 2` with `P₀ = (st, s²)`, and the Frobenius point `P₁` has `deg(P₁ − P₀) = #E(𝔽_q)` | `ManinHasse.abs_trace_le`, `ManinHasse.trace_sq_le`, `ManinHasse.pdeg_add_add_pdeg_sub`, `ManinHasse.pdeg_P1_sub_P0` | Yu. I. Manin, Izv. Akad. Nauk SSSR Ser. Mat. 20 (1956), the elementary proof of H. Hasse's theorem (1936), without isogenies |
| Bohr's torus: the logarithms of distinct primes are linearly independent over `ℤ`, and along a vertical line the means of the characters of the torus tend to their integrals (Kronecker and Weyl), with the moments of prime polynomials | `BohrTorus.eq_zero_of_sum_log`, `BohrTorus.tendsto_mean_character`, `BohrTorus.sum_norm_sq_torus`, `BohrTorus.prod_eq_iff_map_eq`, `BohrTorus.agree_not_rigid`, `BohrTorus.tendsto_mean_moment_rearrangements` | H. Bohr's view of Dirichlet series on the torus |
| Landau's theorem: a Dirichlet series with nonnegative coefficients is singular at the real point of its abscissa of convergence (not in Mathlib) | `LandauLaplace.LSeries_landau`, `LandauLaplace.LSeries_not_holomorphic_at_abscissa` | E. Landau (1905) |
| The energy on hyperbolic 3-space: the action of `SL_2(ℂ)` on `ℍ³` is conformal, and the energy `∫ v²\|∇F\|² dz dv/v³` is invariant under `F ↦ F∘g`; for an automorphic `F` its density is invariant | `Eis.lintegral_energy_actP`, `Eis.edens_automorphic` | the Dirichlet form of the Laplacian of `ℍ³`, in the setting of J. Elstrodt, F. Grunewald and J. Mennicke (1998) |
| Euler's constant to seven digits, `0.57721566 < γ < 0.57721580`, from Binet's formula for the digamma function | `Electron.eulerMascheroni_bounds` | J. P. M. Binet's formula |
| The linear algebra of the Weil-positivity certificates: `LLᵀ` is positive definite for a lower-triangular `L` with a positive diagonal; a positive definite Gram matrix makes a bilinear form positive on its span; a zero off the line makes `F²` negative near it, and the sum over a quadruple of zeros; the probes' Fourier transforms and window functions; the certificate theorems for the prime cut-offs `2` and `3` as instances of the weighted one | `WindowForm.posDef_of_cholesky`, `WindowForm.gram_pos`, `WindowForm.offline_negative`, `WindowForm.quadruple_sum`, `WindowForm.ghat_cos`, `WindowForm.ghat_pole`, `WindowForm.product_dd`, `WindowForm.hasDerivAt_uA`, `WindowForm.phi_u_trig`, `WindowForm.basis_trig`, `WeilForm.memLp_ind`, `WeilForm.ind_mul_ind`, `WeilForm.wP_zero`, `WeilForm.log_three_le`, `CertInstances.weilQ_ge_of_cert'`, `CertInstances.weilQ_ge_of_certP'` | the library |
| The first supplementary law of quadratic reciprocity in `ℤ[ω]` | `Eis.quadR_neg_one` | the companion preprint's Appendix A.1 (see the half-plane's note) |
| `ψ(x) − x` and Mertens' `M(x)` are `Ω±(x^θ)` for every `θ < 1/2`, unconditionally, and so are the differences of the prime races mod 3, 4, 7 and 8 | `PsiOmega.psi_omega_half`, `PsiOmega.mertens_omega_half`, `PsiOmega.race_three_half`, `PsiOmega.race_four_half`, `WeilTwinGeneral.race_seven_half`, `PsiOmega.race_eight_half` | Landau's theorem on Dirichlet series with nonnegative coefficients; H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2007), Chapter 15 |
| The Hadamard product of `L(s, χ₋₄)` | `PsiOmega.hadamard_chi4` | J. Hadamard (1893); H. Davenport, *Multiplicative Number Theory*, Chapter 12 |
| The ideals of `ℤ[ω]` of norm `p^k`: `k + 1` for `p ≡ 1 (mod 3)`, one or none for `p ≡ 2 (mod 3)` as `k` is even or odd, and one for `3` | `Eis.card_ofNorm_split`, `Eis.card_ofNorm_inert`, `Eis.card_ofNorm_three` | the decomposition of primes in `ℚ(√−3)` |
| Heath-Brown's Lemmas 2 and 10 of the quadratic large sieve, for any nonnegative summable weight | `Eis.fBound_gcd`, `Eis.fBound_sep` | D. R. Heath-Brown, Acta Arith. 72 (1995); L. Goldmakher and B. Louvel's Lemmas 5.1 and 7.1 (see the quadratic large sieve's note) |
| Weil's criterion for `ζ`, and the library's criteria for RH and GRH from Weil's form, with its unconditional bounds | `WeilForm.weil_criterion_zeta`, `WeilForm.rh_iff_lam_subexp` and the others of the note [weil-positivity.md](weil-positivity.md) | A. Weil (1952); the library |
| A bound for the third moment of character sums over the characters mod `q`, by their Gram matrix, and its refinement with the diagonal removed | `LinnikMoment.moment_three_chars`, `LinnikMoment.refined_moment_chars` | the library; the refinement is Lemma 4.2 of B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296v2, over the characters mod `q` |
| Short character sums: `\|Σ_{n ≤ x} χ(n)\| ≤ C(q + 2)^η x^{11/12+η}` for every character `χ ≠ 1` mod every `q`, so `Σ_{n ≤ x} χ(n) = O(x^{11/12+ε})` and `o(x)` on `x ≥ q^δ`, for every `δ > 0`, uniformly in `q` and `χ`; the quadratic residues and the non-residues mod an odd prime `p` in `[1, x]` differ in number by `O(x^{11/12+ε})` for `x ≥ p^δ` | `ShortCharSums.norm_sum_le_rpow`, `ShortCharSums.norm_sum_le_mul`, `ShortCharSums.card_squares_sub_le` | D. A. Burgess (1962–63) has `o(x)` for `x ≥ q^{1/4+ε}`, `q` cube-free, and the generalised Lindelöf hypothesis has `x ≥ q^δ`; here from the half-plane, through the Lindelöf bound |
| The least primitive root: modulo every `q` with `(ℤ/qℤ)ˣ` cyclic, a prime primitive root `ℓ ≤ C(d(φ(q))² log(q + 2))^A` for every `A > 12`, so `ℓ ≤ C_ε q^ε`, in particular modulo every prime and every power of an odd prime, and `ℓ ≤ C(log p)^A` for a safe prime `p = 2r + 1`; up to `x`, the prime powers that are primitive roots weigh `(φ(m)/m)ψ(x, χ₀)`, `m = φ(q)`, within `d(m)C log(q + 2)x^{11/12+η}` | `LeastPrimitiveRoot.exists_prime_primRoot_le`, `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow`, `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime`, `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_pow`, `LeastPrimitiveRoot.exists_prime_primRoot_le_safe`, `LeastPrimitiveRoot.norm_sum_primRoot_sub_le` | D. A. Burgess (1962) has `p^{1/4+ε}` for the least primitive root mod `p`, and V. Shoup (1992) `(log p)^6` under GRH; here from the half-plane, through `ψ(x, χ) ≪ log q · x^{11/12+η}` uniformly in `q` |
| Lucas's primality test with small witnesses: `n ≥ 2` is prime if and only if some `a ≤ C_ε n^ε` has `a^{n−1} ≡ 1` and `a^{(n−1)/r} ≢ 1 (mod n)` for every prime `r ∣ n − 1`; for `n = 2r + 1`, `r` an odd prime, some `a ≤ C(log n)^A`, `A > 12` | `LucasWitness.prime_iff_exists_lucas_le_rpow`, `LucasWitness.prime_iff_exists_lucas_le_safe` | É. Lucas (1876) and D. H. Lehmer (1927) for the test; under GRH V. Shoup (1992) has witnesses `≤ (log n)^6`; here from the half-plane, through the least primitive root |
| The Galois groups of the cyclotomic fields: the automorphisms `ζ ↦ ζ^ℓ` (the Frobenius elements) of the primes `ℓ ≤ C(log(q + 2))^A`, `A > 12`, generate `Gal(ℚ(ζ_q)/ℚ)`, and when `(ℤ/qℤ)ˣ` is cyclic one of them with `ℓ ≤ C_ε q^ε` does | `CyclotomicFrobenius.closure_frob_eq_top`, `CyclotomicFrobenius.exists_frob_generator` | E. Bach (1990) under GRH, with `2(log q)²`; here from the half-plane, through `SmallPrimes` and the least primitive root |
| Miller's primality test with small bases: every odd prime is a strong probable prime to every base prime to it, and every odd composite `n` fails the test at a prime base `a ≤ C(log(n + 2))^A` prime to `n`, `A > 12`; so an odd `n ≥ 3` is prime if and only if it passes the test at every base `a ≤ C(log(n + 2))^A` prime to `n` | `MillerTest.strongProbablePrime_of_prime`, `MillerTest.exists_witness_le`, `MillerTest.prime_iff_forall_strongProbablePrime` | G. L. Miller (1976) under the extended Riemann hypothesis, and E. Bach (1990) with the bases `a < 2(log n)²`; here from the half-plane, through `SmallPrimes` |
| The twin form of Weil's explicit formula: its lower bounds with the Korobov–Vinogradov region, its exact rate `2Θ − 1` for `ζ`, the rate at most `5/6` for `L(s, χ₋₃)` and for `ζ·ζ_{ℚ(√−3)}`, and the Korobov–Vinogradov saving in the Kaiser prefactor | `TwinKV.twins_lower_KV'`, `TwinKV.twins_lower_KV_sharp`, `TwinKV.twins_lower_cut`, `HalfPlaneJoinsPNT.weil_twins_rate_Theta`, `HalfPlaneJoins.chi3_rate_eleven_twelfths`, `HalfPlaneJoins.QK3_rate_eleven_twelfths`, `KaiserKV.lam_prefactor_KV` | the library, on A. Weil's explicit formula (1952) |
| A criterion for RH: a relative spectral gap of the Weil form's normalised probes | `WeilForm.rh_of_relgap` | the library |
| The Bohr vectors of the zeros: the nontrivial zeros lie strictly between the shells at `Re s = 0` and `Re s = 1`, and inside the shell at `11/12`; the Korobov–Vinogradov region as a shell; the radii's limits; the normalised vector lies on the unit sphere of every `ℓ^r` norm exactly on the critical line, which lies inside the infinite cube and outside `ℓ²`, the cube's surface being `Re s = 0`; the radius as the root mean square of the prime sum; `Λ(n) = (2/\|S^{n−1}\|)·exp(Σ_p p^{−n})·D₂(n)` | `BohrJoins.shell_unconditional`, `BohrJoins.shell_eleven_twelfths`, `BohrKV.shell_of_KV`, `BohrJoins.shell_radii_tendsto`, `CubeBall.vLp_mem_sphere_iff`, `CubeBall.line_inside_cube_not_in_ell2`, `CubeBall.norm_zCube_eq_one_iff`, `Orthogonality.tendsto_mean_sq_norm_primeSum`, `BohrJoins.completed_eq_sphereArea_bohr` | the library |
| Balls, spheres and cubes: the ball's volume is largest in dimension 5 and the sphere's area in dimension 7; the ball's share of the cube tends to 0; the cube `[−1, 1]ⁿ` has no isometric copy in an inner product space, and a linear embedding distorts it by at least `√n`; among the `ℓ^p` gauges only `p = 2` satisfies Pythagoras; in `ℓ²` the sphere is weakly dense in the ball, the norm is not weakly continuous, and the ball is not homeomorphic to the Hilbert cube; the factor that completes `ζ` is unique | `BallTower.ballVol_lt_five`, `BallTower.sphereArea_lt_seven`, `CubeBall.tendsto_ball_div_cube`, `CubeBall.no_isometry_cube`, `CubeBall.cube_distortion`, `Orthogonality.pythagoras_lpGauge_iff`, `CubeBall.exists_unit_seq_tendsto_inner`, `CubeBall.tendsto_inner_ellUnit`, `CubeBall.isEmpty_homeomorph_ball_hilbertCube`, `BallTower.completing_factor_unique` | classical |
| The `zeta23` layer's results in other forms: the proportions outside the shells in sphere form, the count outside the shell, variants of the hybrid certificate, the local count with the library's constant, and the wall law for `ζ` with von Mangoldt's bound proved | `BohrLandau.tendsto_outside_div_pos`, `ShellDensity.tendsto_outside_div_quarter`, `ShellSixth.tendsto_outside_div_sixth`, `ShellDensity.ncard_outside_le_unconditional`, `HybridCert.cert_offline`, `HybridCert.hybrid_cert_eta_zero`, `HybridCert.hybrid_cert_of_moments`, `HybridCert.hybrid_cert_of_no_offline`, `HybridCert.hybrid_cert_pairs`, `CountCompare.local_count_le`, `SlogZeta.wall_law_zeta_S` | `zeta23` of Anthropic's `formal-math`, with the library's zero counts |
| The zeros of `ζ` on the critical line: infinitely many; for all large `T`, at least `T log T/(12π)` of them with `T < Im ρ ≤ 2T`, a positive proportion of all the zeros there, and at least `T log T/(16π)` simple ones; with `N(T, 2T)` the zeros with `T < Im ρ ≤ 2T` counted with multiplicity, at least `(2/3 − ε)N(T, 2T)` distinct zeros on the line, `(1/2 − ε)N(T, 2T)` simple zeros on the line, and `(3/4 − ε)N(T, 2T)` distinct zeros | `CriticalLine.infinite_zeros`, `CriticalLine.infinite_simple_zeros`, `CriticalLine.two_thirds`, `CriticalLine.two_thirds_cumulative`, `CriticalLine.half_simple`, `CriticalLine.three_quarters_distinct` | G. H. Hardy (1914) for infinitely many, A. Selberg (1942) for a positive proportion; the proportions are L. Alpöge and R. Furman's (2026, arXiv:2608.13637), proved by `zeta23` with no hypothesis |

## Conditional results

The library proves these results under a hypothesis that it does not prove, and no unconditional result uses them;
the last is the column of the Davenport–Heilbronn function of a statement about `ζ`, under a hypothesis that fails for
it. `scripts/dead_code.py` reads the Lean column of the table, and of the tables of the same name in the notes (that of
[weil-positivity.md](weil-positivity.md), for the criteria for RH): a printed theorem with a hypothesis that mentions
none of its variables passes only if an unconditional result uses it, or a result listed in one of them does, or it is
listed in one of them.

| Result | Hypothesis | Lean |
|---|---|---|
| Linnik's theorem with every exponent above `2`, through the density exponent `2` | GRH for every Dirichlet `L`-function | `LinnikGRH.linnik_two_of_GRH`, `LinnikGRH.charDensity_two_of_GRH` |
| The Lindelöf hypothesis (J. E. Littlewood, 1912) | RH | `Subconvexity.lindelof_of_RH` |
| `ψ(x) − x = Ω±(√x)` | that RH fails | `HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH` |
| A pair of zeros whose Bohr vectors straddle the unit sphere, one strictly inside and one strictly outside | that RH fails | `BohrJoins.zero_pair_of_not_RH` |
| The Weil form of the Davenport–Heilbronn function `dh` is nonnegative: the dh column of one direction of Weil's criterion | `PsiOmega.DHRHcross`, every zero of `dh` with `Re s > 0` on the critical line or the real axis, which fails (`PsiOmega.dh_offline_nonreal_zero`) | `PsiOmega.QDHu_nonneg_of_DHRHcross` |
| Weil positivity at small supports: every normalised even probe has `Q(g) ≥ 10⁻³` at supports `a ≤ 1/4`, `≥ 10⁻⁴` at `a ≤ 2/5`, past `2a = log 2` where the prime `2` enters, and `≥ 2·10⁻⁸` at `a ≤ 0.5493`, below `2a = log 3`; and `Q(g) ≥ min(3·10⁻¹⁸, 5·10⁻¹⁵)‖g‖²` for every real probe at `a ≤ 4/5`, past the prime powers `2`, `3` and `4` | lower bounds for the energies of the circle modes and the definiteness of Gram matrices, computed by arb and not checked by the kernel (`WeilForm.Cert14`, `WeilForm.CertP`, `WeilForm.CertP3`, `WeilForm.CertE`, `WeilForm.CertO`) | `WeilForm.weilQ_ge_pole`, `WeilForm.weilQ_ge_prime`, `WeilForm.weilQ_ge_prime3`, `WeilForm.weilQg_ge_both` |
| The density hypothesis (A. E. Ingham, 1940) | the Lindelöf hypothesis | `InghamDensity.densityHypothesis_of_lindelof` |
| The Weyl bound for `ζ`, and Huxley's exponents above `5/6` for the characters | the Weyl bound for every Dirichlet `L`-function, jointly in `q` and `t` (I. Petrow and M. P. Young) | `LinnikWeylBridge.weylBound_of_PYWeyl`, `LinnikStairs7.charDensity_hy_0`, `LinnikStairs7.charDensity_hy_top` |
| `\|ζ(σ + it)\| ≪ \|t\|^{(2/5)(11/12 − σ) + ε}` on `1/2 ≤ σ ≤ 11/12`, from the half-plane | the Weyl bound for `ζ`, `\|ζ(1/2 + it)\| ≪ \|t\|^{1/6 + ε}` (`CrossCriteria.WeylBound`; H. Weyl, G. H. Hardy and J. E. Littlewood) | `Subconvexity.zeta_strip_eleven_twelfths_of_weyl` |

## The vendored libraries

`lib/vendor/` holds two upstream Lean libraries, each with its license, its upstream commit and the patch that ports
it to this repository's Lean and Mathlib:

- PrimeNumberTheoremAnd (`lib/vendor/pnt-plus`);
- `zeta23` of `anthropics/formal-math` (`lib/vendor/zeta23`).

Their results are those projects' own, and the notes above do not cover them.
