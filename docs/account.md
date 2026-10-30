# An account of the library

The library on one page: what it proves, what that rests on, how much of number theory it covers, and where the next
results are. Every result here names the Lean theorem that proves it; a check file prints its axioms, or those of a
theorem that uses it. [`inventory.md`](inventory.md) lists all 914 printed theorems, and
[`formalisations/`](../formalisations/README.md) gives the sources. `scripts/check_account.py`, which CI runs, checks
that every Lean name and path on this page exists.

## How much of number theory

A deep vertical slice, not a survey: the zeros of `ζ` and of Dirichlet `L`-functions, and what they say about primes.
In that slice the library reaches current research (Guth and Maynard's large values estimate, Chen, Gupta and Li's
density estimate, OpenAI's zero-free half-plane) and proves a Linnik exponent of its own. Outside it the library has
what its proofs needed and nothing more. By the sections of MSC 2020's Number theory (11):

| Section | Here |
|---|---|
| 11M `ζ` and `L`-functions | In depth: zero-free regions, zero counting, zero density, moments, approximate functional equations, explicit formulae, criteria for RH |
| 11N Multiplicative number theory | In depth: the prime number theorem and its error terms, primes in progressions, Linnik's theorem, primes in short intervals, Mertens' function, divisor problems, squarefree numbers, sieves |
| 11L Exponential and character sums | What the routes need: mean and large values of Dirichlet polynomials, the Halász–Montgomery inequality, the quadratic large sieve over `ℤ[ω]`, Vinogradov's mean value theorem in a weak form |
| 11F Automorphic forms | One object: Kubota's cubic theta function on hyperbolic 3-space, with Patterson's coefficients |
| 11A, 11R, 11T Elementary, global fields, finite fields | Over `ℤ[ω]`: quadratic, cubic and sextic reciprocity, Gauss and Jacobi sums, the ideals of each norm. Quadratic fields: the splitting law, `ζ_K = ζ·L(s, χ_K)`, class numbers. The least quadratic non-residue |
| 11Y Computational number theory | Certificates that the kernel checks: the sieve's loss (1136 parts), four zeros of the Davenport–Heilbronn function, explicit constants |
| 11B, 11C, 11D, 11E, 11G, 11H, 11J, 11K, 11P, 11S, 11U, 11Z | Nothing beyond Mathlib: no Diophantine equations, quadratic forms, elliptic curves, modular forms in general, Diophantine approximation, additive problems or local fields |

Two of the twenty sections in depth, six in part, twelve not at all. Mathlib supplies the floor: `ζ` and Dirichlet
`L`-functions with their functional equations and their non-vanishing on `Re s = 1`, Dirichlet's theorem, and number
fields with their class groups and the class number formula.

## What it rests on

- **The kernel, Mathlib and the toolchain**: Lean `v4.35.0-rc3` and Mathlib `0f64d30a`. CI fails unless every printed
  theorem depends on `propext`, `Classical.choice` and `Quot.sound` only (`scripts/check_axioms.py`), the sources hold
  no `sorry`, `native_decide` or declared axiom (`scripts/check_hygiene.py`), and every declaration is used by a
  printed theorem (`scripts/dead_code.py`).
- **Two vendored libraries**, PrimeNumberTheoremAnd and `zeta23`, which `scripts/check_vendor.py` checks against
  upstream and the port patches. PrimeNumberTheoremAnd's `Wiener.lean` keeps two upstream `sorry`s; no printed theorem
  uses them.
- **Two inputs that no referee has read, both proved here, not assumed**:
  - the half-plane, OpenAI's: no Dirichlet `L`-function vanishes on `Re s > 11/12`, the pole of `ζ` aside
    (`Eis.LFunction_ne_zero_of_re_gt`, along their companion preprint; [note](../formalisations/openai-half-plane.md));
  - Chen, Gupta and Li's Proposition 3.1, with Heath-Brown's Theorem 10.1 for characters, which the library rebuilds
    from Kerr's and Jutila's arguments (`LinnikCGLHB101.prop31`, `LinnikCGLHB101.cglt101`;
    [note](../formalisations/chen-gupta-li-density.md)).

  Their Lean proofs are complete, and the half-plane is stated with Mathlib's `riemannZeta` and `LFunction`, so
  everything below is a theorem if Lean's kernel and Mathlib are sound. What is missing is review of the mathematics:
  OpenAI's own catalogue marks its Lean "unchecked", and no review of the Dirichlet case independent of OpenAI and this
  library is known.

## The results

Column H: whether the proof uses the half-plane. *yes*; *no* when the half-plane's proof (`KubotaThetaProof.lean` for
`ζ`, `DirichletCharHalfPlane.lean` for the characters) is not in the module's import cone, or the census in the
result's note finds it unused; blank where neither has been checked.

### Where the zeros are

| Result | Lean | H |
|---|---|---|
| No zero of `L(s, χ)` on `Re s > 11/12`, for every `χ` mod every `q` | `Eis.LFunction_ne_zero_of_re_gt` | input |
| Every nontrivial zero of `ζ` has `1/12 ≤ Re ρ ≤ 11/12`, so `Θ = sup Re ρ` has `1/2 ≤ Θ ≤ 11/12` | `HalfPlaneJoins.zeta_band_eleven_twelfths`, `PsiExponent.half_le_Theta`, `PsiExponent.Theta_le` | yes, for the upper bounds |
| Every zero of every Dirichlet `L(s, χ)`, `χ ≠ 1`, with `0 < Re ρ < 1` has `1/12 ≤ Re ρ ≤ 11/12`, by the half-plane and the functional equation | `HalfPlaneJoins.LFunction_band_eleven_twelfths` | yes |
| Korobov–Vinogradov: no zero of `ζ` with `σ ≥ 1 − A(log t)^{−2/3}(log log t)^{−1/3}`; regions of width `(log t)^{−n}` for every `n > 2/3` | `LandauKV.zeroFree_KV`, `KVBridge.zeroFree_kv` | no |
| Bohr–Landau: for every `w > 0`, almost every zero has `\|β − 1/2\| < w` | `BohrLandau.tendsto_NX_div_pos` | no |
| `S(t) = O(log t)`, and the gaps between the ordinates are bounded | `SlogZeta.Slog_zeta`, `ZeroWindow.zero_in_window` | no |

### How many zeros

| Result | Lean | H |
|---|---|---|
| `N(σ, T) ≪ T^{(30/13+ε)(1−σ)}(log T)^{12}` for `ζ`, and the classical `12/5` | `ZetaGMDensity.densityXi_thirty_thirteenths`, `ZetaHuxley.densityXi_twelve_fifths` | yes |
| Guth and Maynard's large values estimate, their Theorem 1.1 at `7/10 ≤ σ ≤ 4/5` | `ZetaGMLV.gm_large_values` | no |
| At most `C(qT)^{A(1−σ)}(log qT)^{10}` characters mod `q` have a zero with `β ≥ σ`, `\|γ\| ≤ T`: Ingham's `A = 3/(2 − σ)` and Huxley's `3/(3σ − 1)`, in steps | `LinnikInghamC.charDensity_ingham_c`, `LinnikHuxStep.charDensity_gen` | no |
| The same with `A = 101/50` on `[5/6, 1]` | `LinnikStep.charDensity_step` | yes |
| Chen, Gupta and Li's `(qT)^{(7/3)(1−σ)+ε}` on `[5/7, 16/21]`; and, on 30 steps of `[5/7, 131/168]`, exponents within `10^{−4}` of `4/(1 + σ)` with `(log qT)^{10}` | `LinnikCGLDensity.cglDensity`, `LinnikCGLSteps.charDensity_s0`, `LinnikCGLSteps.charDensity_s29` | |
| The Linnik paper's curve `g*`, glued from these pieces: at most `2.3334(1 − σ)`, its largest exponent `7/3` (in Lean `2.3334`) at `σ = 5/7` | `SieveCurve7D.counts_7d`, `SieveCurve7D.g7d_le_lin` | yes |

### Primes

| Result | Lean | H |
|---|---|---|
| `ψ(x) = x + O(x^{11/12+ε})` | `HalfPlanePNT.psi_isBigO_eleven_twelfths` | yes |
| `ψ(x) = x + O(x·exp(−c(log x)^{3/5}(log log x)^{−1/5}))`, the strongest form known from refereed results | `PNTKV.PNT_KV` | no |
| `ψ(x; q, a) = x/φ(q) + O(x^{11/12+η})` for every `q` and every `a` prime to `q`, at fixed `q` | `PNTProgressions.psiAP_isBigO` | yes |
| Linnik: every class `a` mod `q` with `(a, q) = 1` holds a prime `p ≤ Kq^{11/5}` | `Linnik22000E.linnik_22000e` | yes |
| Linnik by density estimates and the classical deduction, with the exponents `12`, `4`, `17/6`, `36/13`, `87/35`, `12/5` and `2.3334`, each `+ η` | `Linnik.linnik_twelve`, `LinnikDensity.linnik_four`, `LinnikSubconvex.linnik_seventeen_sixths`, `LinnikIngham.linnik_thirtysix_thirteenths`, `LinnikHuxley.linnik_eighty_seven_thirty_fifths`, `LinnikTwelve.linnik_twelve_fifths`, `LinnikG7.linnik_g7d` | yes |
| A prime in `(y, y + y^θ]` for every large `y`, `θ > 17/30`; and for all `y ∈ [X, 2X]` outside a set of measure `X^{1−δ}`, `θ > 2/15` | `ZetaGMDensity.short_primes_seventeen_thirtieths`, `ZetaGMDensity.almost_all_short_primes_two_fifteenths` | yes |
| In terms of `Θ`: `limsup log\|ψ(x) − x\|/log x = Θ`, the same for `M(x)`, `Σ μ(n)n^{−s}` converges exactly on `Re s > Θ`, and a prime in `(y, y + y^θ]` for `θ > 2Θ/(1 + 2Θ)` | `PsiExponent.limsup_expo`, `MertensExponent.limsup_mexpo`, `MertensExponent.moebiusAbscissa_eq_Theta`, `InghamDensity.short_primes_Theta` | |
| `ψ(x) − x`, `M(x)` and the prime races mod 3, 4, 7 and 8 are `Ω±(x^θ)` for every `θ < 1/2` | `PsiOmega.psi_omega_half`, `PsiOmega.mertens_omega_half`, `PsiOmega.race_three_half`, `PsiOmega.race_four_half`, `WeilTwinGeneral.race_seven_half`, `PsiOmega.race_eight_half` | no |
| `M(x) = O(x^{11/12+η})`; `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{11/12+η})` with `deg P_k = k − 1`; `Q(x) = 6x/π² + O(x^{12/25+η})` for the squarefree numbers | `MertensExponent.mertens_isBigO_eleven_twelfths`, `DivisorExponent.divisor_isBigO_eleven_twelfths`, `DivisorExponent.natDegree_Pk_eq`, `SquarefreeCount.squarefree_isBigO_twelve_25ths` | yes |

### Values of `L`-functions, and quadratic fields

| Result | Lean | H |
|---|---|---|
| `ζ` and `1/ζ`, and uniformly in `q` every `L(s, χ)` and `1/L(s, χ)`, are `≪ (q\|t\|)^ε` on `Re s ≥ σ₀ > 11/12` | `HalfPlaneLindelof.zeta_bound_eleven_twelfths`, `LinnikLindelof.lindelof` | yes |
| `\|ζ(σ + it)\| ≪ \|t\|^{(11/12−σ)/2+ε}` on `[1/12, 11/12]`, so `5/24` on the critical line; `\|L(1/2 + it, χ)\| ≪ (q(\|t\| + 2))^{5/24+ε}` uniformly | `Subconvexity.zeta_strip_eleven_twelfths`, `LinnikSubconvex.critBoundχ` | yes |
| Littlewood's bounds, which he proved under GRH: `1/log log q ≪ \|L(1, χ)\| ≪ log log q` and `L′/L(1, χ) ≪ log log q` for quadratic `χ ≠ 1` | `Littlewood.norm_LFunction_one_ge`, `Littlewood.norm_LFunction_one_le`, `Littlewood.norm_logDeriv_one_le` | yes |
| Class numbers with explicit constants, so effective: `h_K ≥ e^{−2·10²¹}√\|D\|/(80π log log \|D\|)` for imaginary quadratic `K`, `h_K R_K` likewise for real `K`, and `≪ √\|D\| log log \|D\|` from above | `QuadClassNumber.classNumber_ge_loglog`, `QuadClassNumber.regulator_mul_classNumber_ge_loglog`, `QuadClassNumber.classNumber_le`, `QuadClassNumber.regulator_mul_classNumber_le` | yes |
| A split and an inert prime below `C_A(log \|D\|)^A` for every `A > 12`, and below `10^{298}(log \|D\|)^{13}`; the Euler–Kronecker constant | `QuadClassNumber.exists_split_le`, `QuadClassNumber.exists_inert_le`, `QuadClassNumber.exists_split_le_13`, `QuadClassNumber.exists_inert_le_13`, `QuadClassNumber.eulerKronecker` | yes |
| Vinogradov's conjecture: the least quadratic non-residue mod an odd prime `p` is at most `10^{304}(13/δ)^{13}p^δ`; for every `χ ≠ 1` mod `q`, a prime `p ≤ C(log q)^A` with `χ(p) ≠ 1`, `A > 12` | `ExplicitConstants.exists_nonsquare_le_rpow_explicit`, `LeastNonresidue.exists_nonsquare_le_rpow`, `LeastNonresidue.exists_prime_ne_one` | yes |
| Cubic, quadratic and sextic reciprocity in `ℤ[ω]`; its ideals of norm `p^k`; for quadratic `K`, `ζ_K = ζ·L(s, χ_K)`, `L(1, χ_K) = 2πh_K/(w_K√\|D\|)` when `K` is imaginary, and every prime splits, is inert or ramifies | `Eis.cub_recip`, `Eis.quad_recip`, `Eis.sextic_recip`, `Eis.card_ofNorm_split`, `QuadKronecker.dedekindZeta_eq`, `QuadKronecker.classNumber_formula`, `QuadIdeals.trichotomy` | no |

### The Riemann hypothesis: criteria, and what a proof must use

| Result | Lean | H |
|---|---|---|
| Weil's criterion: RH if and only if Weil's form `Q` is nonnegative on every probe; RH if and only if its ground energy has no negative part of exponential rate | `WeilForm.weil_criterion_zeta`, `WeilForm.rh_iff_lam_subexp` | no |
| GRH for `L(s, χ)` by the same test; RH with GRH for `ℚ(i)` by twin forms (and for `ℚ(√−2)`, `ℚ(√−3)`, `ℚ(√−7)`); about forty further criteria ([note](../formalisations/weil-positivity.md)) | `PsiOmega.grh_iff_QC_subexp_all`, `WeilTwinGeneral.rh_grh_iff_twins_Q4` | no |
| RH if and only if `M(x) = O(x^{1/2+η})` for every `η > 0` (Littlewood), if and only if `Θ = 1/2` | `MertensExponent.rh_iff_mertens`, `MertensExponent.rh_iff_Theta_eq_half` | |
| With no hypothesis: the ground energies are at most `Ke^{−Ba}` for every `B`; `Q(g) ≥ ‖g‖²/20` at every support `a ≤ 1/12`; one probe with `Q < 0` exhibits a zero off the line | `WeilForm.lam_decay_uncond`, `WeilForm.weilQg_ge_twentieth_all`, `WeilForm.exists_offline_of_neg_C2` | no |
| The Davenport–Heilbronn function `dh` has `ζ`'s functional equation and zeros off the line, four of them located; the hypotheses of the library's criteria, restated for `dh`, fail, so a proof of one for `ζ` must use what `dh` lacks, such as the Euler product ([note](../formalisations/davenport-heilbronn.md)) | `PsiOmega.dh_offline_zero`, `PsiOmega.Locate.dh_zeros_located_four_box`, `PsiOmega.not_D_dh` | no |

### The tools

The estimates that the results above are built from, each stated for reuse:

| Tool | Lean |
|---|---|
| Mean values of Dirichlet polynomials over the characters mod `q`, and their values at one point per character | `LinnikHybrid.mean_value_chars`, `LinnikHybrid.large_values_chars` |
| Large values: Halász–Montgomery, Huxley's estimate, Guth and Maynard's, and Chen, Gupta and Li's with characters | `LinnikPower.hm_duality`, `LinnikReflect.huxley_large_values`, `ZetaGMLV.gm_large_values`, `LinnikCGLHB101.prop31` |
| The hybrid fourth moment of `L(1/2 + it, χ)`; the fourth moment of `ζ` at well-spaced points; the approximate functional equation of `L(s, χ)²` | `LinnikFourth.fourth_moment`, `ZetaFourth.zeta_fourth_moment`, `LinnikGamma.afe` |
| Zero detection by a mollified Dirichlet polynomial; log-derivatives in zero-free discs; Perron's formula with a smooth weight, and contour shifts | `LinnikDetect.dichotomy`, `LogDerivDisc.logDeriv_le_Kld`, `Linnik.perron_exp`, `SmoothPerron.verticalIntegral_shift` |
| Sieves: Brun's fundamental lemma, Buchstab's identity on tuples of primes, Harman's comparison with and without the bilinear Type I estimate, that estimate by Parseval's identity, rough numbers by Buchstab's `ω` | `SieveBrun.fundamental`, `SieveDecomp.buchstab_fam`, `SieveProp6.prop6`, `SieveP6ib.prop6ib`, `SieveTypeIB.typeIB_bound`, `SieveRough.psi_le` |
| Over `ℤ[ω]` and `ℍ³`: the quadratic large sieve, and Kubota's theta function with Patterson's coefficients | `Eis.quadLargeSieve`, `Eis.kubotaTheta` |
| Vinogradov's mean value theorem, weak form; Weil's explicit formula as a form | `VinoRec.vmvt_weak`, `WeilForm.weilQ_symbol` |

Of these, the mean values, the Halász–Montgomery inequality, Guth and Maynard's estimate, the log-derivative bound,
Brun's lemma, the large sieve, the theta function, Vinogradov's mean value theorem and Weil's form do not use the
half-plane. The certificate pipeline, `tools/linnik/`, turns a sieve decomposition into Lean files that the kernel
checks by `decide +kernel`.

## What a new input buys at once

The deductions are stated for any input, against Mathlib's `ζ` and `LFunction`, so an input proved anywhere plugs in:

| Prove | and the library gives | Through |
|---|---|---|
| no zero of `ζ` on `Re s > β`, for some `β < 1` | the errors of `ψ`, `M` and `Σ d_k` at `x^{β+η}`, and of the squarefree count at `x^{1/(3−β)+η}` | `HalfPlanePNT.psi_isBigO_of_zeroFree`, `MertensExponent.mertens_isBigO_of_zeroFree`, `DivisorExponent.divisor_isBigO_of_zeroFree`, `SquarefreeCount.squarefree_isBigO_of_zeroFree` |
| the same for `L(s, χ)`, `χ ≠ 1` | `ψ(x, χ) = O(x^{β+η})` | `ChiPNT.psiChi_isBigO_of_zeroFree` |
| a density estimate `Linnik.CharDensity A B C` over the characters, `A ≥ 2` | Linnik's theorem with every exponent above `A` | `Linnik.linnik_of_charDensity` |
| `ShortWeil.DensityXi A B` and a zero-free region `ShortWeil.ZeroFreeXi α` for `ζ` | a prime in `(y, y + y^θ]` for `θ > max(1/2, 1 − 1/A)` | `ShortWeil.short_primes_of_density` |
| `ShortWeil.DensityXi (A + ε) B` for every `ε > 0` | primes in almost all intervals `(y, y + y^θ]` for `θ > 1 − 2/A` | `AlmostAll.almost_all_of_density` |
| `\|ζ(1/2 + it)\| ≪ \|t\|^c` (`CrossCriteria.ZetaCritBound`) | the density exponent `2 + 4c` | `InghamDensity.densityXi_of_zetaCrit` |
| RH | the Lindelöf hypothesis, and from it the density hypothesis | `Subconvexity.lindelof_of_RH`, `InghamDensity.densityHypothesis_of_lindelof` |
| GRH for every `L(s, χ)` | Linnik's theorem with every exponent above `2` | `LinnikGRH.linnik_two_of_GRH` |
| Petrow and Young's Weyl bound for every `L(s, χ)`, uniformly (`LinnikWeyl.PYWeyl`) | Weyl's bound for `ζ`, and Huxley's exponents above `5/6` for the characters | `LinnikWeylBridge.weylBound_of_PYWeyl`, `LinnikStairs7.charDensity_hy_0`, `LinnikStairs7.charDensity_hy_top` |
| that RH fails | `ψ(x) − x = Ω±(√x)` | `HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH` |
| a Type II estimate on a window (`SieveRoute.TypeIIAt`) | Harman's comparison for the primes in a class mod `q` | `SieveProp6.prop6` |

## Connections

What the results give in other parts of number theory, and in physics. Every row is a theorem with no hypothesis,
whose axioms are Lean's three; H is as above.

| Connection | Lean | H |
|---|---|---|
| Algorithms: every proper subgroup of `(ℤ/qℤ)ˣ` misses a prime `p ≤ C(log q)^A`, `A > 12`, so these primes generate `(ℤ/qℤ)ˣ`. Under GRH this is E. Bach's bound, which makes G. L. Miller's primality test deterministic | `SmallPrimes.exists_prime_not_mem`, `SmallPrimes.closure_primes_eq_top` | yes |
| Power residues: for every `k ≥ 2` dividing `p − 1`, a prime `ℓ ≤ C(log p)^A` that is not a `k`-th power mod `p` | `SmallPrimes.exists_prime_not_pow` | yes |
| Class groups: Gauss's class number problem with an explicit bound, `\|D_K\| ≤ (320π e^{2·10²¹} h_K)⁴` for imaginary quadratic `K`, polynomial in `h_K` as under GRH | `ClassNumberBound.abs_discr_le` | yes |
| Physics, crystals: `Σ_{n≥1} (−1)^n r₂(n) n^{−s} = −4(1 − 2^{1−s}) ζ(s) L(s, χ₋₄)`, holomorphic off `s = 1`. At `s = 1/2` it is `−M`, where `M ≈ 1.6155` is the Madelung constant of the square lattice: an ion of a two-dimensional ionic crystal has electrostatic energy `−Me²/a` | `Madelung.lseries_coeff`, `Madelung.differentiableOn_rhs` | no |
| Physics, the primon gas: `Σ μ(n) n^{−β}` is the partition function of B. Julia's primon gas with the sign `(−1)^F` of D. Spector's fermion number. It converges for `β > Θ` and diverges for `β < Θ`, with `1/2 ≤ Θ ≤ 11/12`: past the bosonic gas's Hagedorn point `β = 1` | `MertensExponent.moebiusAbscissa_eq_Theta`, `PsiExponent.half_le_Theta`, `PsiExponent.Theta_le` | yes |
| Geometry of numbers: the points of `ℤⁿ` in a ball of radius `R` number `V_n Rⁿ(1 + o(1))`, `V_n = π^{n/2}/Γ(n/2 + 1)`, most in dimension 5; in the plane they give `L(1, χ₋₄) = π/4`, Leibniz's series | `BallTower.count_div_pow_tendsto_ballVol`, `BallTower.counted_volume_max_five`, `AngularResidue.LFunction_chi4_one` | no |
| Quadratic forms: over a finite field of odd size `q`, `x² + y² = a` has `q − χ₋₄(q)` solutions and `x² + y² + z² + w² = a` has `q³ − q`, for `a ≠ 0`: the local factors of Jacobi's and Siegel's formulas | `LocalTeeth.card_two_sq`, `LocalTeeth.card_four_sq` | no |
| Ergodic theory: the logarithms of the primes are linearly independent over `ℤ`, and a vertical line equidistributes on Bohr's torus (Kronecker and Weyl) | `BohrTorus.eq_zero_of_sum_log`, `BohrTorus.tendsto_mean_character` | no |
| Analysis: Landau's theorem, a Dirichlet series with nonnegative coefficients is singular at the real point of its abscissa; Mathlib does not have it | `LandauLaplace.LSeries_landau` | no |
| Noncommutative geometry: the least value `λ₁(a)` of Weil's form on supports `[−a, a]`, which A. Connes and C. Consani study, is positive for `a ≤ 1/12`, has a unique ground state for `2a < log 2` (the range of their archimedean positivity theorem), and is at most `Ke^{16a − 2πe^{2a}}` | `WeilForm.weilQg_ge_twentieth_all`, `WeilForm.groundState_unique_below_log2`, `WeilForm.lam_dexp` | no |

Within reach, with no hypothesis, from results the library has:

- **Short character sums**: `Σ_{n≤x} χ(n) = o(x)` uniformly for `x ≥ q^δ`, every `δ > 0`, where Burgess's method
  needs `x ≥ q^{1/4+ε}`: Perron's formula with the Lindelöf bound on `Re s > 11/12` (`LinnikLindelof.lindelof`).
- **Pell's equation**: the least solution of `x² − dy² = 1`, `d` squarefree, has `log(x₁ + y₁√d) ≪ √d log log d`:
  `QuadClassNumber.regulator_mul_classNumber_le`, and `x₁ + y₁√d = ε^m` with `ε` the fundamental unit of `ℚ(√d)` and
  `m` dividing 6.
- **Primitive roots**: the least prime primitive root mod `p` is `≪_ε p^ε`, where Burgess's method gives `p^{1/4+ε}`
  for the least primitive root: the characters of order dividing `p − 1` against the bound
  `ψ(x, χ) ≪ log q · x^{11/12+η}`, uniform in `q` (`ChiUniform.psiChi_le_uniform`).
- **Binary quadratic forms**: `2` is a cube mod a prime `p ≡ 1 (mod 3)` if and only if `p = x² + 27y²` (Gauss), from
  cubic reciprocity (`Eis.cub_recip`) and its supplementary laws.
- **Weil positivity past the prime 2**, to supports `2a < log 3`, beyond Connes and Consani's `log 2`. The module
  PrimeRelax3, in the git history, proves it from 60 mode energies that arb computes, taken as a hypothesis; a
  certificate that the kernel checks, as the Linnik sieve's is, would remove the hypothesis.
- **Hyperbolic 3-space**: Kubota's `θ` (`Eis.kubotaTheta`) as an eigenfunction of the Laplacian at `s(2 − s) = 8/9`,
  below the continuous spectrum `[1, ∞)`: a bound state of a free particle on the cubic metaplectic cover.
- **The half-plane's `dh` column**: `dh` vanishes somewhere in `Re s > 1` (Davenport and Heilbronn), so a located zero
  there would show in Lean that the half-plane needs the Euler product.

## The frontier

In order of what is in reach.

1. **Primes in short intervals, below `θ = 0.52`.** The library proves `θ > 17/30` by density. R. Li's sieve gives
   `0.52` (arXiv:2308.04458). [Pull request #48](https://github.com/dickie81/number-theory/pull/48) is putting Li's
   argument into Lean for `θ = 0.52`, with Type II information at real Hölder exponents. Its computation, Monte Carlo
   and not a proof, keeps Li's constant positive down to `θ ≈ 0.5182` once Guth and Maynard's estimate
   (`ZetaGMLV.gm_large_values`) joins Huxley's. A Lean proof below `0.52` would go below Li, resting on the half-plane
   as Linnik's exponent does: the sieve's main terms take the prime number theorem in short ranges from it.
2. **Linnik's exponent.** The theorem is `11/5`. With the window chosen afresh, the same method's certificate passes
   at `2.199` (total `0.96729K` on 276 cells a side) and fails at `2.198` (supplement §S6, computed, not a theorem): a
   regeneration with `tools/linnik/`, not new mathematics. Below that, the sieve has no window under `1 + A/2 = 13/6`
   for the curve's peak `A = 7/3`, and `0.7151K` of the certificate's `0.9321K` is cells that no depth of
   decomposition reaches. Two things move it: a lower density exponent for the characters near `σ = 5/7`, where Chen,
   Gupta and Li call the dominant term "quite difficult" to improve (their Remark 12.3), or Type I information on
   longer products than the bilinear estimate's `d₁d₂² < x`. The half-plane at `7/8` would not.
   `tools/linnik/density_payoff.py` prices a hypothetical curve.
3. **The half-plane at `7/8`.** OpenAI's main preprint states `Re s > 7/8`, and their own Lean proves it for every
   `χ`; the library proves `11/12`, by the companion route. A proof of `7/8` here would feed the deductions above at
   once: `ψ`, `M`, `ψ(x, χ)` and `Σ d_k` at `x^{7/8+η}`, the squarefree count at `x^{8/17+η}`, and `Θ ≤ 7/8`. The
   Ankeny, Littlewood and class-number chain and `Subconvexity.zeta_strip_eleven_twelfths` have `11/12` written in;
   made parametric, they would give `A > 8` in place of `A > 12`, and `3/16` in place of `5/24` on the critical line.
   Linnik's exponent would not move.
4. **Density estimates.** For `ζ` the library proves Guth and Maynard's maximum, `30/13`, as one exponent for all `σ`,
   not their curve. For the characters it proves Chen, Gupta and Li's Proposition 3.1 and the steps the Linnik curve
   needs, not their Theorem 1.2; above `5/6` its exponent is `101/50` against Huxley's `2`: the zeros that its
   detector counts with the fourth moment cost at least `1.974`, and only `LinnikWeyl.PYWeyl` would remove them. Each
   sharper estimate enters through the deductions above.
5. **The Riemann hypothesis.** The library reduces RH to properties of Weil's form in about forty ways, proves none of
   their hypotheses, and shows, through `dh`, that no argument which applies to `dh` as well can prove them. A new
   criterion should come with its `dh` column, which tests it before any work on `ζ`.
6. **Tools that are missing.** The large sieve over all moduli `q ≤ Q` (the library has one modulus at a time), so no
   Bombieri–Vinogradov; bounds for Kloosterman sums, which the bilinear Type I estimate avoids; exponent pairs (the
   Weyl bound is only a hypothesis); Selberg's and Rosser's sieves; anything in the twelve sections the library does
   not touch.

## Debts

- `PNTProgressions`'s module header, and so its line in `docs/inventory.md`, says "modulo the divisors of 24":
  `PNTProgressions.psiAP_isBigO` holds for every `q`. The fix is a Lean edit that rebuilds the modules above it.
- 21 files of `lib/dh` name their generator, `gen_locate_zero.py`, `gen_locate.py`, `gen_logext.py` or
  `gen_oddterms.py`, and none of the four is in the repository, so the files can be neither regenerated nor checked
  ([survey](dry-efficiency-survey.md)).
- Weaker than the sources, and absorbed where used: the mean value theorem with `8P(1 + log P)` for `O(P)`; the fourth
  moment with `(qT)^ε` for `(log qT)^4`; the density counts with `(log qT)^{10}`, steps up to `1/2000` above the
  curves, and characters counted in place of zeros; the quadratic large sieve over `ℚ(ω)` only; Harman's sieve stated
  for the Linnik problem only, with Brun's sieve in its leaves.
- Sources formalised in part: Chen, Gupta and Li (Proposition 3.1, not Theorems 1.1 and 1.2), Guth and Maynard
  (Theorem 1.1 at `7/10 ≤ σ ≤ 4/5` only), Kubota and Patterson (the display the half-plane's route uses), OpenAI
  (`11/12` for Dirichlet `L`-functions; not `7/8`, nor their Hecke `L`-functions over `ℚ(√−3)`).
- Computations that are not theorems: the exponents `2.199` and `2.239` of the Linnik supplement, and the
  short-interval Monte Carlo of pull request #48.
- Each note lists the sources that were not read; one entry of the Linnik paper's bibliography, Buchstab (1937), is
  unverified.

## Building on it

- **Where code goes.** `lib/core` needs Mathlib only; `lib/pnt` adds PrimeNumberTheoremAnd; `lib/zeta23` adds `zeta23`
  and cannot be imported with `lib/pnt`; `lib/dh` is its own layer. Module names are flat, so after adding a module
  run `python3 scripts/gen_lakefile.py`.
- **A new result.** Print its axioms in a check file: `lib/check/CheckAll.lean`, or `lib/check/Check.lean` for a
  paper's. Another printed result must use it, or `formalisations/` must name it, or `scripts/dead_code.py` fails; a
  result under a hypothesis the library does not prove goes in a table "Conditional results" there. Then run
  `python3 scripts/inventory.py`, and update this page if the result changes a line of it.
- **A result from the literature** gets a note in `formalisations/`: its source, its Lean statement, the differences,
  how it was done. A paper claims only its own steps ([papers](../papers/README.md)).
- **The build.** Before importing a module into one the default build reaches, `python3 scripts/import_cone.py Check
  --why MODULE` shows what it brings, certificates included; certificates are generated by `tools/` and compared byte
  for byte in CI. Memory and CI's stages are in [`building.md`](building.md).
- **Where to start.** This page, then the note of the area, then [`inventory.md`](inventory.md) for the names.
