# Inventory of the library's results

Written by `scripts/inventory.py` from the sources; do not edit it by hand. `python3 scripts/inventory.py`
rewrites it, and CI checks that it is current (`--check`).

`lib/check/CheckAll.lean` and `lib/check/Check.lean` print the axioms of 694 theorems: the library's final
results and the papers' theorems, of which there are 117, marked *paper*. Each line gives a theorem's
name and the headline of its docstring, and links the note of `formalisations/` that names it, if one does.
The last section lists the 100 modules that neither `Check` nor `CheckAll` imports, directly or
not, with their headline theorems (those whose docstring opens with a bold title).

| Layer | Modules with results | Results | Modules outside both | Their headline theorems |
|---|---|---|---|---|
| `lib/core` | 7 | 8 | 34 | 118 |
| `lib/pnt` | 210 | 686 | 2 | 17 |
| `lib/dh` | 0 | 0 | 53 | 303 |
| `lib/zeta23` | 0 | 0 | 11 | 25 |

## The results of `CheckAll`

### `lib/core`

#### `BohrLandauCore`: For every w > 0, almost every zero lies within w of the critical line

- `BohrLandauCore.tendsto_NX_div_of_lower`: For every `w > 0`, almost every zero lies within `w` of the critical line

#### `DirichletCharHalfPlane`: Every Dirichlet character, `L(s, χ) ≠ 0` on `Re s > 11/12`

- `Eis.LFunction_ne_zero_of_re_gt`: The half-plane `Re s > 11/12` for every Dirichlet character *paper* ([note](../formalisations/openai-half-plane.md))

#### `EisensteinCubicRecip`: S1, part 3b: cubic reciprocity on `ℤ[ω]`

- `Eis.cub_recip`: Cubic reciprocity *paper*

#### `EisensteinQuadSieveFinal`: The quadratic large sieve, part 8: Theorem 2, `(E_1)` and Lemma 6.5

- `Eis.quadLargeSieve`: The companion paper's Lemma 6.5 is proved *paper* ([note](../formalisations/quadratic-large-sieve.md))

#### `HalfPlaneJoinsFinal`: The half-plane's joins with no hypothesis

- `HalfPlaneJoins.zeta_band_eleven_twelfths`: Every nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ 5/6`.

#### `KubotaThetaProof`: The Kubota–Patterson display, proved

- `Eis.kubotaTheta`: The display `KubotaTheta`, proved *paper* ([note](../formalisations/cubic-theta.md))
- `Eis.ne_zero_of_re_gt_eleven_twelfths`: The half-plane ([note](../formalisations/openai-half-plane.md))

#### `TwinLandau`: The Landau argument for twin forms, for any zero family

- `TwinLandau.Q_ge_of_rates`: The converse bound with a rate per pole

### `lib/pnt`

#### `AlmostAllArch`: Primes in almost all short intervals, part 1: the explicit formula at one point

- `AlmostAll.arch_far`: The archimedean term far from `0`

#### `AlmostAllMean`: Primes in almost all short intervals, part 2: the zero sum in mean square

- `AlmostAll.head_mean_square`: The head in mean square

#### `AlmostAllPrimes`: Primes in almost all short intervals, part 3: the exceptional set

- `AlmostAll.almost_all_of_density`: Primes in almost all short intervals, from a density estimate ([note](../formalisations/zeta-density.md))
- `AlmostAll.almost_all_short_primes`: Primes in almost all short intervals for every `θ > 1/6` ([note](../formalisations/zeta-density.md))

#### `BohrKV`: The Korobov–Vinogradov region as a shell around the Bohr sphere

- `BohrKV.shell_of_KV`: The Korobov–Vinogradov region is a shell at each height

#### `ChiPNT`: `ψ(x, χ) = O(x^{11/12+η})` for every Dirichlet character `χ ≠ 1`

- `ChiPNT.logDeriv_le_of_zeroFree`: The log-derivative of an entire function in a zero-free half-plane
- `ChiPNT.sum_le_uniform_of`: Sums of the coefficients of `−F′/F`, with explicit constants
- `ChiPNT.sum_le_uniform`: Sums of the coefficients of `−F′/F`, with their constants
- `ChiPNT.sum_isBigO_of_zeroFree`: Sums of the coefficients of `−F′/F` in a zero-free half-plane
- `ChiPNT.psiChi_isBigO_of_zeroFree`: `ψ(x, χ)` in a zero-free half-plane
- `ChiPNT.psiChi_isBigO_eleven_twelfths`: `ψ(x, χ) = O(x^{11/12+η})`

#### `ChiUniform`: Bounds for the real Dirichlet L-functions, uniform in the modulus

- `ChiUniform.LFunction_ctr_inv_le`: `‖L(3/2 + it, χ)‖⁻¹ ≤ ζ(3/2)`, from `1/L(s, χ) = Σ χ(n)μ(n)n^{−s}` (a step of `psiChi_le_uniform_of`).
- `ChiUniform.logDeriv_LFunction_right`: `‖L′/L(s, χ)‖ ≤ −ζ′/ζ(3/2)` on `Re s ≥ 3/2` (a step of `psiChi_le_uniform_of`).
- `ChiUniform.psiChi_le_uniform_of`: `ψ(x, χ)` uniformly in the modulus, from the constants of `sum_le_uniform`
- `ChiUniform.psiChi_le_uniform`: `ψ(x, χ)` uniformly in the modulus

#### `DetectEM`: Zero detection by Euler–Maclaurin, and primes in short intervals

- `DetectEM.density_unconditional`: Zero density
- `DetectEM.short_primes`: Primes in short intervals

#### `DivisorExponent`: The divisor problems in a zero-free half-plane

- `DivisorExponent.integral_pow_mul_cexp`: `∫_0^∞ u^m e^{−cu} du = m!/c^{m+1}`
- `DivisorExponent.inv_sub_one_pow_eq_integral`: `(s − 1)^{−m} = ∫_0^∞ (u^{m−1}/(m−1)!) e^{−(s−1)u} du` for `Re s > 1`, `m ≥ 1`.
- `DivisorExponent.LSeries_dk`: `L(d_k, s) = ζ(s)^k` on `Re s > 1`, with absolute convergence.
- `DivisorExponent.verticalIntegral_inv_sub_one_pow`: The principal parts against the smoothing
- `DivisorExponent.zeta_pow_eq`: `ζ(s)^k = Σ_{j<k} c_j (s − 1)^{j−k} + g_k(s)`
- `DivisorExponent.smoothedSum_dk_eq`: The smoothed divisor sum
- `DivisorExponent.norm_remainder_le`: The remainder
- `DivisorExponent.coeff_Pk`: The leading coefficient
- `DivisorExponent.natDegree_Pk_eq`: `P_k` has degree exactly `k − 1`.
- `DivisorExponent.divisor_isBigO_of_zeroFree`: The divisor problems in a zero-free half-plane
- `DivisorExponent.divisor_isBigO_eleven_twelfths`: The divisor problems at `11/12`
- `DivisorExponent.divisor_isBigO_Theta`: The divisor problems at `Θ`

#### `Domination`: Domination corollaries

- `Domination.lam_prefactor_KV'`: The statement of `KaiserKV.lam_prefactor_KV`, from `lam_nine` (`c = 1`).

#### `ExplicitConstants`: Explicit constants for Littlewood's bounds and the least quadratic nonresidue

- `ExplicitConstants.psiChi_le_explicit`: `ψ(x, χ)` uniformly in the modulus, with an explicit constant
- `ExplicitConstants.logDeriv_le_explicit`: `|L′/L(σ, χ)| ≤ 10²¹ log log(N + 16)` on `(1, 2]`
- `ExplicitConstants.norm_LFunction_one_le_explicit`: `|L(1, χ)| ≤ e^{2·10²¹} log log(N + 16)`
- `ExplicitConstants.norm_LFunction_one_ge_explicit`: `|L(1, χ)| ≥ e^{−2·10²¹}/log log(N + 16)`
- `ExplicitConstants.norm_logDeriv_one_le_explicit`: `|L′/L(1, χ)| ≤ 10²¹ log log(N + 16)`
- `ExplicitConstants.exists_prime_eq_explicit`: The least primes with `χ(p) = ±1`, with an explicit constant, for every `A > 12`
- `ExplicitConstants.exists_prime_eq_13`: The least primes with `χ(p) = ±1`, at `A = 13`
- `ExplicitConstants.exists_nonsquare_le_explicit`: The least quadratic nonresidue, with an explicit constant, for every `A > 12`
- `ExplicitConstants.exists_nonsquare_le_13`: `n(p) ≤ 10³⁰⁴ (log p)¹³`
- `ExplicitConstants.exists_nonsquare_le_rpow_explicit`: `n(p) ≤ 10³⁰⁴(13/δ)¹³p^δ`

#### `ExplicitSmooth`: An explicit smoothing and its Mellin constants

- `ExplicitSmooth.contDiff_ν₀`
- `ExplicitSmooth.mass_ν₀`
- `ExplicitSmooth.mellin_ν₀_le_geom`: The Mellin transform of `Smooth1 ν₀ ε` on a line, with its constant

#### `HalfPlaneFinal`: The half-plane `Re s > 11/12` in the prime number theorem

- `HalfPlanePNT.psi_isBigO_eleven_twelfths`: The prime number theorem with error `O(x^{11/12+ε})` *paper* ([note](../formalisations/harman-sieve.md))

#### `HalfPlaneJoinsPNT`: Joins from the exponent `Θ` and the half-plane into older sockets

- `HalfPlaneJoinsPNT.weil_twins_rate_Theta`: The exponential rate of the negative part of `ζ`'s twin form is exactly `2Θ − 1`
- `HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH`: If RH fails, `ψ(x) − x = Ω±(√x)`
- `HalfPlaneJoinsPNT.zeroFree_KV_explicit`: `LandauKV.zeroFree_KV` with `A = 1/6`

#### `HalfPlaneLindelof`: A Lindelöf bound in a zero-free half-plane

- `HalfPlaneLindelof.norm_le_interp`: Interpolation on a rectangle
- `HalfPlaneLindelof.hasDerivAt_log_norm`: The derivative of `log |f|`
- `HalfPlaneLindelof.logDeriv_le_interp`: The interpolated bound on `ζ′/ζ`
- `HalfPlaneLindelof.zeta_bound_of_zeroFree`: A Lindelöf bound in a zero-free half-plane
- `HalfPlaneLindelof.zeta_bound_eleven_twelfths`: The Lindelöf bound on `Re s > 11/12`
- `HalfPlaneLindelof.zeta_bound_Theta`: The Lindelöf bound on `Re s > Θ`

#### `HalfPlanePNT`: A zero-free half-plane gives a power saving in the prime number theorem

- `HalfPlanePNT.logDeriv_le_of_zeroFree`: The log-derivative under a zero-free half-plane
- `HalfPlanePNT.psi_isBigO_of_zeroFree`: A zero-free half-plane gives a power saving in the prime number theorem
- `HalfPlanePNT.psi_isBigO_of_smoothBound`: Under `SmoothBound β`, `β < 1`
- `HalfPlanePNT.psi_isBigO_of_completed`: Under the completed mean square (`Eis.CompletedMeanSquare`, the companion paper's Proposition 5.2), which gives `ζ(s) ≠ 0` on `Re s > 11/12`

#### `InghamDensity`: Ingham's zero-density exponent `2 + 4c` from `|ζ(1/2 + it)| ≪ |t|^c`

- `InghamDensity.densityXi_of_zetaCrit`: Ingham's exponent from a pointwise bound on the critical line
- `InghamDensity.inghamFromC`: `CrossCriteria.InghamFromC c` for every `c ≥ 0`
- `InghamDensity.densityXi_17_6`: Zero density at the exponent
- `InghamDensity.densityXi_Theta`: Zero density at `Θ`
- `InghamDensity.densityHypothesis_of_lindelof`: Lindelöf implies the density hypothesis
- `InghamDensity.short_primes_11_17`: Primes in short intervals for every `θ > 11/17`
- `InghamDensity.short_primes_Theta`: Primes in short intervals at `Θ`

#### `InghamDetect`: A zero detector with the line moved to `Re s = 1/2`

- `InghamDensity.norm_Gamma_exp_le`: `|Γ(x + it)| ≤ KE e^{−|t|}` on `½ ≤ x ≤ 3`
- `InghamDensity.detect_identity`: The identity at a zero
- `InghamDensity.trichotomy`: The trichotomy at a zero

#### `KVBridge`: Rung 3, closed: the growth bound for ζ and the zero-free region it gives

- `KVBridge.polylogGrowth_kv`: The growth hypothesis holds for every `4/5 ≤ a ≤ 1`
- `KVBridge.polylogGrowth_sharp`: The growth hypothesis holds for every `2/3 < a ≤ 1`
- `KVBridge.zeroFree_kv`: Zero-free region
- `KVBridge.rung3_kv`: Rung 3

#### `KVSubsumes`: The Korobov–Vinogradov width subsumes the growth chain

- `KVSubsumes.kvInput_of_KV`: The named input `KVInput`, discharged for every `n₁ > 2/3` (with `n₂ = 3`).

#### `KaiserKV`: The Korobov–Vinogradov region in the Kaiser prefactor

- `KaiserKV.lam_prefactor_KV`: The Kaiser prefactor with the Korobov–Vinogradov saving

#### `Landau`: Landau's lemma, general form: layer III of rung 3

- `Landau.zeroFree_of_growth`: L3 (Landau's theorem, general form)
- `Landau.logDerivBnd_of_growth`: L4
- `Landau.rung3_of_growth`: Layer III, assembled: polylog growth ⇒ rung 3

#### `LandauKV`: The last bit, step R3: the Korobov–Vinogradov zero-free region

- `LandauKV.zeroFree_KV`: The Korobov–Vinogradov zero-free region

#### `LeastNonresidue`: The least quadratic nonresidue, and the least primes with `χ(p) = ±1`

- `LeastNonresidue.re_psiChi_ge`: If `χ(p) = ε`, `ε = ±1`, at every prime `p ≤ x` that does not divide `q`, then `ε·Re ψ(x, χ) ≥ ψ(x) − 4√x log x − log q`.
- `LeastNonresidue.rpow_le_of_forall_eq`: If `χ(p) = ε` at every prime `p ≤ x` not dividing `q`, then `x^{1/A} ≤ K log(q + 2)`, for every `A > 12`, with `K` depending on `A` only…
- `LeastNonresidue.exists_prime_eq`: The least primes with `χ(p) = ±1`
- `LeastNonresidue.exists_prime_ne_one`: A prime with `χ(p) ≠ 1`, for every Dirichlet character `χ ≠ 1`
- `LeastNonresidue.exists_nonsquare_le_of`: The least quadratic nonresidue, with the constant
- `LeastNonresidue.exists_nonsquare_le`: Vinogradov's least quadratic nonresidue conjecture, in Ankeny's form
- `LeastNonresidue.exists_nonsquare_le_rpow_of`: `n(p) ≤ C₀(13/δ)^{13}p^δ` from `n(p) ≤ C₀(log p)^{13}`
- `LeastNonresidue.exists_nonsquare_le_rpow`: `n(p) ≪_δ p^δ`

#### `Linnik22015R`: Linnik's theorem with exponent `4403 / 2000` by the bilinear Type I rule, from its certificate's inequality

- `Linnik22015R.linnik_22015r_of_cert`: Linnik's theorem with exponent `4403 / 2000`, from the certificate's inequality

#### `Linnik22240R`: Linnik's theorem with exponent `278 / 125`, under the refined certificate at `n = 340`

- `Linnik22240R.routeOK22240D`: `route22240D` is a route *paper*
- `Linnik22240R.fits22240R`: `grid22240R` fits `route22240D` *paper*
- `Linnik22240R.linnik_22240r`: Linnik's theorem with exponent `278 / 125`, by the refined certificate at `n = 340` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikAFE`: The approximate functional equation for `L(s, χ)²`

- `LinnikGamma.norm_gammaFactor_ratio_le`: The ratio of two values of the Archimedean factor
- `LinnikGamma.verticalIntegral_sub_eq`: Moving the line of integration across a simple pole at `0`
- `LinnikGamma.afe`: The approximate functional equation for `L(s, χ)²` ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikBuckets`: The off-diagonal pairs in dyadic buckets of the analytic conductor

- `LinnikReflect.pair_sum_pointwise`: Pointwise in `v`, all characters `χ ≠ χ′` at once

#### `LinnikCGL112`: Their (11.2), the blocks of their Proposition 7.2 summed

- `LinnikCGL112.S3_le_blocks`: The blocks summed
- `LinnikCGL112.S3_le_112`: Their (11.2), in explicit form

#### `LinnikCGLAsum`: The sum over `a` in their Lemma 8.2, by the Ramanujan sum

- `LinnikCGLAsum.sum_a_finite_le`: The sum over `a`, finite form

#### `LinnikCGLBlock`: `S₃,₃`, `S₃,₄` and the block sums of `Ĩ`, by their Proposition 8.1 and Lemmas 9.1 and 9.2

- `LinnikCGLBlock.S34_le_P81`: `S₃,₄` on the block `k`, by their Proposition 8.1
- `LinnikCGLBlock.block_le`: The block `k`, by their Proposition 8.1 and Lemmas 9.1 and 9.2

#### `LinnikCGLCS`: The two Cauchy–Schwarz steps of their §11 (the `S₃` side)

- `LinnikCGLCS.sum_It_sq_le`: Their first Cauchy–Schwarz step
- `LinnikCGLCS.S32_le`: Their second Cauchy–Schwarz step, (11.1)

#### `LinnikCGLCase`: Their Lemma 10.10 with its case analysis, and their Remark 10.3 (the `S₃` side)

- `LinnikCGLCase.case_le`: Their case analysis (10.4)–(10.5)
- `LinnikCGLCase.remark103`: Their Remark 10.3, in the library's form ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLCase.lemma1010_case`: Their Lemma 10.10 (large gcd terms)

#### `LinnikCGLConst`: The constants of their Lemma 8.2

- `LinnikCGLConst.sum_gw_le`: For `q ≥ 1`, `Σ_{h mod q}(h, q) ≤ q·d(q)`, for `gw`.
- `LinnikCGLConst.KX_le`: For `q ≥ 1`, `L > 0`, `0 ≤ M₁ ≤ L`, `X ≥ 0` and `0 < δ ≤ 1`, `K_X ≤ 40πC_δB₄d(q)⁴L²q(1 + qX)^δ(1 + 2q)^δ`.

#### `LinnikCGLCount`: The count of the pairs `(m₁′, n′)` in their Lemma 8.2

- `LinnikCGLCount.count_le`: Their count

#### `LinnikCGLCov`: The terms `n ≠ 0` of `ĝ_a` over `|ξ| ≤ X`, by the change of variables to their `Σ_II`

- `LinnikCGLCov.integral_r_eq`: Their change of variables
- `LinnikCGLCov.integral_gstar_le`: The terms `n ≠ 0` over `|ξ| ≤ X`

#### `LinnikCGLDecay`: The Fourier decay of their `f_b`, in the form of their Proposition 8.1 (the `S₃` side)

- `LinnikCGLDecay.fb_decay`: The decay for `j ≥ 1`
- `LinnikCGLDecay.fb_decay_all`: The decay premise of `CGLP81` for their `f_b`

#### `LinnikCGLDensity`: Chen–Gupta–Li's density estimate on `[5/7, 16/21]` for every `ε` (`LinnikCGL.CGLDensity`)

- `LinnikCGLDensity.cglDensity`: Chen–Gupta–Li's density estimate on `[5/7, 16/21]` ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLDiag`: The Gram matrix's diagonal against its main term

- `LinnikCGLDiag.muP_sub_mu0_le`: The diagonal against its main term
- `LinnikCGLDiag.muP_sub_mu0_le_rpow`: For `q ≥ 1` and `N > 0`, `|μ − μ₀| ≤ C_δBq^δ` for `0 < δ ≤ 1` (the divisor bound).
- `LinnikCGLDiag.S3_eq_all`: The condition "not all equal" removed

#### `LinnikCGLEps`: Their Lemmas 10.9 and 10.10 with their `⪅`, and their Proposition 10.2

- `LinnikCGLEps.lemma109_eps`: Their Lemma 10.9 with their `⪅`
- `LinnikCGLEps.lemma1010_eps`: Their Lemma 10.10 with their `⪅`
- `LinnikCGLEps.prop102`: Their Proposition 10.2

#### `LinnikCGLFb`: Their `f_b = ψR̃(·, −b)²` for §11, with a `ψ` that is `1` on the centres (the `S₃` side)

- `LinnikCGLFb.contDiff_fb`
- `LinnikCGLFb.fb_one_ge`: The lower bound of `f`
- `LinnikCGLFb.S34_le_fb`: `S₃,₄` against their `J` for this `f`

#### `LinnikCGLForm`: Their Lemma 8.2 in their form, with the parameters chosen

- `LinnikCGLForm.term2_parts`: Their `II`, the parts
- `LinnikCGLForm.lemma82_form`: Their Lemma 8.2, in their form

#### `LinnikCGLFourier`: Chen–Gupta–Li's Lemma 4.3 (1), the decay of `ĥ_t` (the `S₃` side)

- `LinnikCGLFourier.hasDerivAt_F`: `F_k′ = F_{k+1}`
- `LinnikCGLFourier.fourier_F`
- `LinnikCGLFourier.lemma43`: Chen–Gupta–Li's Lemma 4.3 (1)

#### `LinnikCGLFrob`: The off-diagonal mass of the Gram matrix, explicitly

- `LinnikCGLFrob.ls_points`: The large sieve at the points
- `LinnikCGLFrob.prod_trick_points`: The product trick at the points, squared
- `LinnikCGLFrob.sum_Dp_sq_le`: The mass of the dual sums over all pairs, at one height
- `LinnikCGLFrob.gram_sq_le`: A Gram entry, squared
- `LinnikCGLFrob.frobOff_le`: The off-diagonal mass of the Gram matrix, explicitly

#### `LinnikCGLFtil`: Their smoothing `f̃_b`, and the inner integral of their `Σ_II`

- `LinnikCGLFtil.integral_S2_le`: The inner integral
- `LinnikCGLFtil.sum_psi_norm_Phi_sq_le_ftil`: Their `Σ_II` with the majorant

#### `LinnikCGLFtilP`: Their smoothing `f̃_b` in their induction, and `Λ` against `F`

- `LinnikCGLFtilP.integral_ftil_sq_le`: `L²` against `f̃_b`
- `LinnikCGLFtilP.Lam_le`: `Λ` against `F`

#### `LinnikCGLG`: The majorant of their `J(f⃗)`, Plancherel, and its Fourier transform

- `LinnikCGLG.Jint_le_ga`: `J(f⃗) ≤ Σ_a∫g_a²`
- `LinnikCGLG.integral_sq_ga`: Plancherel for `g_a`
- `LinnikCGLG.fourier_ga`: The Fourier transform of `g_a`

#### `LinnikCGLHB101`: Heath-Brown's Theorem 10.1 with characters, and Chen–Gupta–Li's Propositions 11.1 and 3.1

- `LinnikCGLHB101.cglt101`: Heath-Brown's Theorem 10.1 with characters *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLHB101.cgls3`: Their Proposition 11.1, at one point per character, with no hypothesis *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLHB101.prop31`: Their Proposition 3.1, at one point per character, with no hypothesis *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLHB101.char_density`: The density count with no hypothesis

#### `LinnikCGLHBIter`: Kerr's iteration with characters

- `LinnikCGLHBIter.caseB`: Case B
- `LinnikCGLHBIter.sig_bound`: Kerr's iteration with characters

#### `LinnikCGLHBLen`: The lengthening of Heath-Brown's double sums

- `LinnikCGLHBLen.cqU_mul_sig_le`: The lengthening
- `LinnikCGLHBLen.sig_le_lengthen`: The lengthening with its constant

#### `LinnikCGLHBPos`: Positivity, and the double sums of Heath-Brown's bound

- `LinnikCGLHBPos.dsum_le`: Positivity
- `LinnikCGLHBPos.shat_sq_le`: Squaring

#### `LinnikCGLHBRefl`: The reflection of Heath-Brown's double sums

- `LinnikCGLHBRefl.sum_gram_sq_le`: The Gram matrices summed
- `LinnikCGLHBRefl.sig_le_refl`: The reflection of the double sum

#### `LinnikCGLJ`: Their `J(f⃗)`, their Proposition 8.1 as a displayed hypothesis, and `S₃,₃`, `S₃,₄` in its form (the `S₃` side)

- `LinnikCGLJ.S34_le_Jint`: `S₃,₄` against their `J` ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLJ.S33_le_S34`: `S₃,₃ ≤ 4S₃,₄` ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLJtil`: Their Cauchy–Schwarz back to `J(f̃⃗)`, for the terms `|n| ≤ N₀` of their `Σ_II`

- `LinnikCGLJtil.sum_psi_norm_Phi_sq_le_J`: Their `Σ_II` against `J(f̃⃗)`
- `LinnikCGLJtil.sum_integral_Phi_le`: The terms `|n| ≤ N₀` of `B_II`

#### `LinnikCGLL1010`: Their Lemma 10.10, the large-gcd terms, before their case analysis (the `S₃` side)

- `LinnikCGLL1010.lemma106'`: Their Lemma 10.6 without a lower bound on `qT`
- `LinnikCGLL1010.lemma1010`: Their Lemma 10.10 (large gcd terms), before their case analysis

#### `LinnikCGLL105`: Their Lemma 10.5, the energy by the third moment of `R` (the `S₃` side)

- `LinnikCGLL105.sum_triple_le`: The triples bounded
- `LinnikCGLL105.lemma105`: Their Lemma 10.5

#### `LinnikCGLL107`: Their Lemma 10.7, the fourth moment of `R` (the `S₃` side)

- `LinnikCGLL107.group_le`: Their Theorem 10.1 on one group of keys
- `LinnikCGLL107.lemma107`: Their Lemma 10.7, from `CGLT101`

#### `LinnikCGLL109`: Their Lemma 10.9, the small-gcd terms

- `LinnikCGLL109.sum_cube_moment_le`: The weighted third moment over the units
- `LinnikCGLL109.lemma109`: Their Lemma 10.9 (small gcd terms)

#### `LinnikCGLL82`: Their Lemma 8.2 with explicit constants

- `LinnikCGLL82.lemma82_explicit`: Their Lemma 8.2, with explicit constants

#### `LinnikCGLLV`: Chen–Gupta–Li's Proposition 3.1 as a hypothesis, and the large-values counts it gives

- `LinnikCGLLV.lv_range`: The large values of `D_N` on Proposition 3.1's range ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLLV.cgl_all`: Proposition 3.1's count over all characters mod `q`
- `LinnikCGLLV.taylor_pick`: One character off the line
- `LinnikCGLLV.cgl_shift`: Proposition 3.1's count off the line

#### `LinnikCGLLoc`: Local averages of finite exponential sums, toward their Lemmas 10.4 and 10.8 (the

- `LinnikCGLLoc.norm_esum_le_integral`: The local average
- `LinnikCGLLoc.norm_sq_esum_le`: The local average of `|F|²`
- `LinnikCGLLoc.norm_cube_esum_le`: The local average of `|F|³`

#### `LinnikCGLMat`: Chen–Gupta–Li's Proposition 3.1 from a bound on the cubic trace

- `LinnikCGLMat.refined_moment_points`: The moment inequality for the points
- `LinnikCGLMat.prop46`: Their Proposition 4.6 for the points *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLMat.mvt_case`: The mean value theorem at the points
- `LinnikCGLMat.alg112`: Their §11.2's algebra
- `LinnikCGLMat.prop31_of_third`: Proposition 3.1 from the bound on the cubic trace

#### `LinnikCGLMellin`: The Mellin transform of `w²`, and the Gram entries as vertical integrals

- `LinnikCGLMellin.exists_H_bound`: The decay of `H` on vertical strips
- `LinnikCGLMellin.differentiable_H`: `H` is entire
- `LinnikCGLMellin.perron_Wt`: Perron's formula for `W_τ`
- `LinnikCGLMellin.perron_gram`: Perron's formula for the Gram entries

#### `LinnikCGLMom`: Their Lemma 9.1, the second moments of `R` and `R̃`

- `LinnikCGLMom.lemma91`: Their Lemma 9.1 for `R`
- `LinnikCGLMom.lemma91_Rt`: Their Lemma 9.1 for `R̃`, exact at one point per character

#### `LinnikCGLMom4`: Their Lemma 9.2, the fourth moments of `R` and `R̃`

- `LinnikCGLMom4.lemma92`: Their Lemma 9.2 for `R`, at one point per character ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLMom4.lemma92_Rt`: Their Lemma 9.2 for `R̃`, at one point per character

#### `LinnikCGLN0`: The term `n = 0` of `ĝ_a`, their `I`

- `LinnikCGLN0.sum_integral_g0_le`: Their `I`, the term `n = 0`

#### `LinnikCGLNsum`: `ĝ_a` as a sum over `m₁` and `n`, and the sum over `a` for every `n ≠ 0`

- `LinnikCGLNsum.fourier_ga_split`: The term `n = 0` split off
- `LinnikCGLNsum.sum_a_fourier_ga_le`: `ĝ_a` without its term `n = 0`

#### `LinnikCGLP71`: Their Proposition 7.1 (the `S₃` side)

- `LinnikCGLP71.norm_Psi_le`: The integrand of their (7.3), bounded
- `LinnikCGLP71.prop71`: Their Proposition 7.1

#### `LinnikCGLP72`: Their Proposition 7.2 (the `S₃` side)

- `LinnikCGLP72.Ip_le_It`: Their bound for `|I′(m⃗)|`
- `LinnikCGLP72.sum_Ak_regroup`: Regrouping the bounds by the dyadic scale of `m₂`, with `−m₂` replaced by `m₂` in each block.
- `LinnikCGLP72.prop72`: Their Proposition 7.2 at one point per character

#### `LinnikCGLP81`: Their Proposition 8.1, by their downward induction

- `LinnikCGLP81.cglp81`: Their Proposition 8.1 *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLPair`: The bounds of the reflected Gram entries

- `LinnikCGLPair.norm_Eu_mul_le`: The Euler factor against the conductor
- `LinnikCGLPair.norm_dualT_le`: The dual tail far left
- `LinnikCGLPair.norm_integral_Mn_le`: The main part, bounded by its dual sum
- `LinnikCGLPair.norm_integral_Tl_le`: The tail far left
- `LinnikCGLPair.norm_gram_le`: A Gram entry, bounded through its reflection

#### `LinnikCGLPhi`: The Fourier decay of `ψ·K(· − u′)`, the pieces of their `f_b`

- `LinnikCGLPhi.integral_abs_iteratedDeriv_phi_le`: `∫|φ_{u′}^{(j)}| ≤ B_j(L, X)` for `L, X > 0`.
- `LinnikCGLPhi.fourier_phi_le`: The Fourier decay of `φ_{u′}`

#### `LinnikCGLPois8`: The Poisson expansion of `ĝ_a` in residue classes

- `LinnikCGLPois8.poisson_S`: Poisson in residue classes
- `LinnikCGLPois8.fourier_ga_poisson`: `ĝ_a` by Poisson in residue classes

#### `LinnikCGLPoisson`: The Poisson expansion of the Gram entries in residue classes

- `LinnikCGLPoisson.poisson_scaled`: Poisson summation, scaled
- `LinnikCGLPoisson.sum_colsP_residue`: A finite sum over `colsP N` by residue classes
- `LinnikCGLPoisson.gram_poisson`: The Poisson expansion of a Gram entry in residue classes

#### `LinnikCGLProd`: A product of three `ĥ`s as an integral over `(v₁, v₂)`

- `LinnikCGLProd.prod_eq_iter`: The substitution
- `LinnikCGLProd.iter_swap`: Fubini
- `LinnikCGLProd.hhat_prod`: A product of three `ĥ`s

#### `LinnikCGLRFact`: Their `I′_{m⃗}` as an integral over `(v₁, v₂)`

- `LinnikCGLRFact.S2_triple`: The residue sums of a triple
- `LinnikCGLRFact.sum_Qk`: The sum over the triples of points, at one `(v₁, v₂)`
- `LinnikCGLRFact.Ip_eq`: Their `I′_{m⃗}` as an integral over `(v₁, v₂)`

#### `LinnikCGLRam`: The Ramanujan sum's bound and the decay of `J` (the `S₃` side)

- `LinnikCGLRam.norm_Cq_le`: The Ramanujan sum's bound
- `LinnikCGLRam.Jk_decay`: The decay of `J`
- `LinnikCGLRam.Jk_eq_zero_of`: `J(v₁, v₂, λ) = 0` unless `v₁, v₂ ∈ (1/2, 2)`.

#### `LinnikCGLRefl0`: The reflection of the principal Gram entries

- `LinnikCGLRefl0.reflect_gram0`: The principal reflection
- `LinnikCGLRefl0.norm_gram_le0`: A principal Gram entry, bounded through its reflection

#### `LinnikCGLReflect`: The reflection of the Gram entries

- `LinnikCGLReflect.norm_Phi_le_far`: The reflection factor far left
- `LinnikCGLReflect.LFunction_reflected`: The reflected `L`-function
- `LinnikCGLReflect.shift_of_bound`: A contour shift
- `LinnikCGLReflect.reflect_gram`: The reflection of the Perron integral
- `LinnikCGLReflect.gram_reflect`: The Gram entries reflected

#### `LinnikCGLRt`: Their `R̃` and the inner integral of Proposition 7.2

- `LinnikCGLRt.local_le_Rt_sq`: `R̃` controls the local second moment
- `LinnikCGLRt.inner_le`: The inner `v₂` integral by Cauchy–Schwarz
- `LinnikCGLRt.Vr_inner_le`: The inner integral of their Proposition 7.2

#### `LinnikCGLS2`: `CGLS2`

- `LinnikCGLS2.LSX_le`: The large-sieve factor as a power
- `LinnikCGLS2.Bmax_le`: The tail bound as a power of `P`
- `LinnikCGLS2.s2_main`: The main case of `CGLS2`
- `LinnikCGLS2.cgls2`: `CGLS2` holds *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLS23`: The off-diagonal of the cubic trace as Chen–Gupta–Li's `S₂ + S₃`

- `LinnikCGLS23.X3_eq`: The cubic trace's off-diagonal
- `LinnikCGLS23.third_of_s23`: `CGLThird` from the two hypotheses

#### `LinnikCGLS3`: Their Proposition 11.1, `CGLS3` from `CGLP81` and `CGLT101`

- `LinnikCGLS3.cgls3`: Their Proposition 11.1 at one point per character
- `LinnikCGLS3.prop31_pt`: Their Proposition 3.1 at one point per character, from their Proposition 8.1 and Heath-Brown's Theorem 10.1

#### `LinnikCGLSep`: Separated points, and the fractions of their Lemma 10.9

- `LinnikCGLSep.log_sep`: The separation in `log`
- `LinnikCGLSep.sum_cube_le`: A finite exponential sum at separated points ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLSig2`: Their `Σ_II` expanded, and their `Σ₂` by Poisson summation

- `LinnikCGLSig2.sum_psi_norm_Phi_sq_le`: Their `Σ_II`, expanded
- `LinnikCGLSig2.norm_S2_le`: For `q ≥ 1` and `N₀ > 0`, `|S₂(k₀, x)| ≤ N₀Σ_k|ψ̂₀(N₀(k − x + k₀/q))|`, a convergent series.

#### `LinnikCGLStep`: The density step from Chen–Gupta–Li's Proposition 3.1, `7/3 + 1/2000` on `[5/7, 16/21]`

- `LinnikCGLStep.block_bin_cgl`: One dyadic block and one bin, by Chen–Gupta–Li's estimate
- `LinnikCGLStep.class1_cgl`: The polynomial class with Chen–Gupta–Li's estimate on `[lo, hi]`
- `LinnikCGLStep.count_cgl`: The range `[lo, hi]`
- `LinnikCGLStep.charDensity_cgl`: Chen–Gupta–Li's density step `7/3 + 1/2000` on `[5/7, 16/21]`, from their Proposition 3.1

#### `LinnikCGLSteps`: Chen–Gupta–Li's Proposition 3.1 at every point of `[5/7, 131/168]`: 30 density steps with the exponent

- `LinnikCGLSteps.charDensity_s0`: Chen–Gupta–Li's Proposition 3.1 on `[5 / 7, 1201 / 1680]`, density step 0 *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLSteps.charDensity_s29`: Chen–Gupta–Li's Proposition 3.1 on `[163 / 210, 131 / 168]`, density step 29 *paper*
- `LinnikCGLSteps.charDensity_inT`: Ingham's last step at `ε = 1/400000` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLSym`: The support of `J` in `v₂/v₁`, and the cyclic symmetry of `I′` (the `S₃` side)

- `LinnikCGLSym.prop71r`: Their Proposition 7.1 with the support of `J` in `v₂/v₁` kept ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLSym.Ip_cyc`: The cyclic symmetry
- `LinnikCGLSym.sum_le_three_mul`: The reduction to `|m₂|` largest

#### `LinnikCGLT101`: Their Theorem 10.1 (Heath-Brown) displayed, and their Lemma 10.6 (the `S₃` side)

- `LinnikCGLT101.sum_sq_R2_eq`: The square of `R₂`, expanded
- `LinnikCGLT101.lemma106`: Their Lemma 10.6

#### `LinnikCGLTail`: The terms `|n| > N₀` of their `Σ_II` and the range `|ξ| > X` of `ĝ_a`, by the decay premise

- `LinnikCGLTail.sum_integral_Phi_tail_le`: The terms `|n| > N₀`
- `LinnikCGLTail.setIntegral_ga_tail_le`: The range `|ξ| > X`

#### `LinnikCGLTrace`: Chen–Gupta–Li's `S₃` at one point per character (the `S₃` side)

- `LinnikCGLTrace.S3_eq_cube`: `S₃` as a cubic trace
- `LinnikCGLTrace.Em_eq`: A Gram entry less its main term
- `LinnikCGLTrace.S3_eq_Fm`: Chen–Gupta–Li's `S₃` at one point per character

#### `LinnikCGLTrunc`: The truncation in `m` and their `I′_{m⃗}` (the `S₃` side)

- `LinnikCGLTrunc.sum_FmT_cube`: The truncated cubic trace as a sum of their `I′`
- `LinnikCGLTrunc.norm_Fm_sub_FmT_le`: The tail beyond `M`
- `LinnikCGLTrunc.S3_trunc`: Their (7.1) at one point per character, before the triangle inequality

#### `LinnikChar`: The bound for one character with the weight `e^{−n/x}`

- `Linnik.perron_exp`: Perron's formula for `e^{−n/x}`
- `Linnik.logDeriv_LFunction_le`: `L′/L(·, χ)` where `L(·, χ)` has no zero in one disc
- `Linnik.norm_Sx_le`: The bound for one character

#### `LinnikDeduction`: Linnik's theorem from a density estimate over the characters mod `q`

- `Linnik.totient_mul_SAP`: Orthogonality
- `Linnik.re_Sx_one_ge`: The trivial character
- `Linnik.SAP_le_of_noPrime`: A class with no prime up to `Y`
- `Linnik.error_le`: The characters other than the trivial one
- `Linnik.total_le`: The sizes
- `Linnik.prime_in_class`: A prime in the class up to `10x log x`
- `Linnik.linnik_of_charDensity`: Linnik's theorem from a density estimate over the characters mod `q` *paper*
- `Linnik.charDensity_twelve`: The trivial density from the half-plane
- `Linnik.linnik_twelve`: Linnik's theorem with exponent `12 + η`, from the half-plane alone *paper*

#### `LinnikDensity`: Density over the characters mod `q` from a bound on the critical line

- `LinnikDensity.class1_count`: The polynomial class ([note](../formalisations/ingham-density.md))
- `LinnikDensity.class2_count`: The integral class
- `LinnikDensity.count_nontrivial`: The two classes at one modulus
- `LinnikDensity.charDensity_of_LBound`: Density over the characters from a uniform critical-line bound
- `LinnikDensity.charDensity_of_critBound`
- `LinnikDensity.linnik_of_critBound`: Linnik's theorem from a uniform critical-line bound

#### `LinnikDetect`: Zero detection for `L(s, χ)`, `χ ≠ 1`

- `LinnikDetect.LSeries_aXχ`: `Σ χ(n)a_n n^{−s} = M_X(s, χ)L(s, χ)` on `Re s > 1`.
- `LinnikDetect.detect_identityχ`: The identity at a zero
- `LinnikDetect.dichotomy`: The dichotomy at a zero ([note](../formalisations/ingham-density.md))

#### `LinnikDual`: The dual sums as polynomials at the points of the first character, and the kernel of a pair

- `LinnikReflect.pair_kernel_one`: The kernel on the first line
- `LinnikReflect.pair_kernel_two`: The kernel on the second line

#### `LinnikFE`: The functional equation of `L(s, χ)` on vertical lines

- `LinnikFE.rootNumber_inv`: `ε(χ⁻¹) = conj ε(χ)`.
- `LinnikFE.rootNumber_mul_inv`: For primitive `χ`, `ε(χ)ε(χ⁻¹) = 1`
- `LinnikFE.norm_rootNumber`: `|ε(χ)| = 1` for primitive `χ`
- `LinnikFE.norm_Gamma_mul_sin_le`: `|Γ(σ + it)sin(π(σ + it)/2)| ≤ 3(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2` ( `Subconvexity.norm_Gamma_mul_le_of`, as its `norm_Gamma_mul_cos_le`).
- `LinnikFE.norm_LFunction_one_sub_le`: The left line from the right one, for `L(s, χ)`

#### `LinnikFourth`: The hybrid fourth moment of `L(½ + it, χ)` over the characters mod `q`

- `LinnikFourth.norm_LFunction_four_le`: `|L(1/2 + it, χ)|⁴ ≤ 2|D(1/2 + it, χ)|² + 2|D(1/2 − it, χ⁻¹)|²` ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.sum_norm_Pd_sq_le`: Large values of `P` at one point per character ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.afeJ_split`: The split of `J` ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.sum_norm_afeD_sq_le`: The second moment of `D` at one modulus ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.fourth_moment_primitive`: The hybrid fourth moment at one modulus, for primitive characters ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.fourth_moment`: The hybrid fourth moment over the characters mod `q` *paper* ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikG7`: Linnik's theorem with exponent `2.3334 + ε` from the curve `g7d`, by the classical deduction

- `LinnikG7.charDensity_g7d`: The density estimate of the curve `g7d` *paper*
- `LinnikG7.linnik_g7d`: Linnik's theorem with exponent `11667/5000 + η` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikGRH`: GRH for every Dirichlet L-function gives the density hypothesis `CharDensity 2 0 1`, and so Linnik's exponent `2 + η`

- `LinnikGRH.charDensity_two_of_GRH`: GRH for every Dirichlet character gives `Linnik.CharDensity 2 0 1`
- `LinnikGRH.linnik_two_of_GRH`: The consequence

#### `LinnikGammaRatio`: Ratios of `Γ` on vertical lines, and the functional equation reflected to the modulus `q`

- `LinnikReflect.LFunction_eq_reflect`: The functional equation, reflected to the modulus `q`

#### `LinnikHalf`: The partial-summation bound for `L(½ + it, χ)` and Linnik's exponent `4 + η`

- `LinnikDensity.LFunction_split`: The split at `M`
- `LinnikDensity.norm_LFunction_half_le`: The partial-summation bound
- `LinnikDensity.critBoundχ_half`: `CritBoundχ (1/2)`, with constant `11`.
- `LinnikDensity.linnik_four`: Linnik's theorem with exponent `4 + η`

#### `LinnikHuxStep`: A step of Huxley's bound with parameters, `7/3 + 1/2000` on `[16/21, 5/6]` (the second goal's input D3)

- `LinnikHuxStep.class1_gen`: The polynomial class with Huxley's estimate on `[lo, hi]`
- `LinnikHuxStep.count_gen`: The range `[lo, hi]`
- `LinnikHuxStep.charDensity_gen`: A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]` *paper* ([note](../formalisations/huxley-density.md))
- `LinnikHuxStep.charDensity_hux73`: The step `7/3 + 1/2000` on `[16/21, 5/6]`
- `LinnikHuxStep.charDensity_step'`: The step from the parameters ([note](../formalisations/huxley-density.md))

#### `LinnikHuxStepY`: The step of Huxley's bound with the detector's height as a parameter, class II empty under the Weyl bound

- `LinnikHuxStepY.charDensity_genY`: A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]`, class II empty under the Weyl bound
- `LinnikHuxStepY.parY_example_good`
- `LinnikHuxStepY.parY_example'_good`

#### `LinnikHuxley`: The power trick on `23/29 ≤ σ ≤ 11/12`, and Linnik's exponent `87/35 + η`

- `LinnikHuxley.power_count`: Large values of a power, one point per character
- `LinnikHuxley.class2_count_small`: The integral class with a short mollifier
- `LinnikHuxley.class1_huxley`: The polynomial class with powers
- `LinnikHuxley.count_huxley`: The range `23/29 ≤ σ ≤ 11/12`
- `LinnikHuxley.charDensity_huxley`: A density estimate over the characters mod `q` with exponent `87/35`
- `LinnikHuxley.linnik_eighty_seven_thirty_fifths`: Linnik's theorem with exponent `87/35 + η`, with no hypothesis

#### `LinnikHybrid`: The hybrid mean value over the characters mod `q`

- `LinnikHybrid.mean_value_row`: The mean value theorem with a row bound ([note](../formalisations/mean-values.md))
- `LinnikHybrid.sum_chars_norm_sq_le`: Orthogonality ([note](../formalisations/mean-values.md))
- `LinnikHybrid.mean_value_chars`: The hybrid mean value *paper* ([note](../formalisations/mean-values.md))
- `LinnikHybrid.large_values_chars`: Large values at one point per character *paper* ([note](../formalisations/mean-values.md))
- `LinnikHybrid.large_values_chars_off`: Large values off the line at one point per character ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikIngham`: Ingham's density estimate over the characters mod `q`, and Linnik's exponent `36/13 + η`

- `LinnikIngham.class2_count_ingham`: The integral class, Ingham's way ([note](../formalisations/ingham-density.md))
- `LinnikIngham.count_nontrivial_ingham`: The two classes at one modulus, Ingham's way
- `LinnikIngham.charDensity_ingham`: Ingham's density estimate over the characters mod `q`
- `LinnikIngham.linnik_thirtysix_thirteenths`: Linnik's theorem with exponent `36/13 + η`, with no hypothesis *paper*

#### `LinnikInghamC`: Ingham's density estimate with the detector's `c` as a parameter (a staircase below `3/4`)

- `LinnikInghamC.charDensity_ingham_c`: Ingham's density estimate with exponent `2 + 4c + 4ε` on `[1/2 + δ₀, σ₂]` *paper* ([note](../formalisations/ingham-density.md))

#### `LinnikLargeValues`: A large-values estimate of Huxley's shape over the characters mod `q`

- `LinnikReflect.kernel_sum_le`: The kernel sum of the Halász–Montgomery inequality
- `LinnikReflect.huxley_large_values`: Huxley's large-values estimate over the characters mod `q` ([note](../formalisations/huxley-density.md))

#### `LinnikLindelof`: A Lindelöf bound for `L(s, χ)` on `Re s > 11/12`, uniformly in the modulus

- `LinnikLindelof.norm_LFunction_le_zeta32`: `‖L(s, χ)‖ ≤ ζ(3/2)` on `Re s ≥ 3/2`.
- `LinnikLindelof.inv_norm_LFunction_le_zeta32`: `‖L(s, χ)‖⁻¹ ≤ ζ(3/2)` on `Re s ≥ 3/2`, from `1/L(s, χ) = Σ χ(n)μ(n)n^{−s}`.
- `LinnikLindelof.logDeriv_le_interp`: The interpolated bound on `L′/L`
- `LinnikLindelof.lindelof`: A Lindelöf bound for `L(s, χ)`, uniformly in the modulus *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikLines`: The line-sum identity for prime moduli

- `LinnikLines.triple_eq`: Step 1
- `LinnikLines.line_sum_identity`: The line-sum identity
- `LinnikLines.line_sum_identity_of_zero`: The line-sum identity for weights off `0`
- `LinnikLines.gram_eq_gramZ`: The Gram matrix on `S` is the Gram matrix with the residue weights of `c`.
- `LinnikLines.large_values_lines`: Large values and the line sums

#### `LinnikMoment`: Third-moment bounds for the largest singular value

- `LinnikMoment.moment_three`: The simple bound at `r = 3`
- `LinnikMoment.moment_three_chars`: The simple bound at `r = 3` over the characters mod `q`
- `LinnikMoment.refined_moment`: Chen–Gupta–Li's Lemma 4.2
- `LinnikMoment.refined_moment_cube`: Lemma 4.2 cubed
- `LinnikMoment.refined_moment_chars`: Chen–Gupta–Li's Lemma 4.2 over the characters mod `q`

#### `LinnikOffDiag`: `L(s, χ)` on the line `Re s = 1/12 − δ` and the off-diagonal sums

- `LinnikOffDiag.left_line`: The left line for every character `χ ≠ 1`, uniformly in the modulus
- `LinnikOffDiag.norm_offK_le`: The off-diagonal bound *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikPoints`: Large values at several points per character

- `LinnikPoints.large_values_points`: Large values at several points per character
- `LinnikPoints.large_values_chars_of_points`: `LinnikHybrid.large_values_chars` is the case of one point per character.

#### `LinnikPower`: The divisor bound, powers of Dirichlet polynomials and the Halász–Montgomery inequality

- `LinnikPower.card_divisors_le`: The divisor bound
- `LinnikPower.pv_pow`: The power of a Dirichlet polynomial ([note](../formalisations/huxley-density.md))
- `LinnikPower.hm_duality`: The Halász–Montgomery duality inequality over the characters mod `q` *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikReflect`: The reflection of the smoothed character sum

- `LinnikReflect.reflect`: The reflection of the smoothed character sum

#### `LinnikS2`: The closed form of `S₂`, and the socket for prime moduli

- `LinnikS2.S2_closed`: The closed form of `S₂`
- `LinnikS2.large_values_socket`: The socket for prime moduli at one point per character

#### `LinnikSplit`: The zero frequency and the degenerate lines

- `LinnikSplit.lineSum_zero`: The zero frequency
- `LinnikSplit.sum_lines_split`: The split
- `LinnikSplit.large_values_split`: Large values through `S₂` and `S₃`

#### `LinnikStairs7`: The staircase of the Weyl-conditional route (Ingham steps on `[4/7, 5/7]`, Huxley's on `[16/21, 11/12]`)

- `LinnikStairs7.charDensity_in7_0`: Ingham's step `0` *paper* ([note](../formalisations/ingham-density.md))
- `LinnikStairs7.charDensity_in7_18`: Ingham's step `18` *paper*
- `LinnikStairs7.charDensity_hx7_0`: Huxley's step `0` ([note](../formalisations/huxley-density.md))
- `LinnikStairs7.charDensity_hx7_5`: Huxley's step `5` *paper* ([note](../formalisations/huxley-density.md))
- `LinnikStairs7.charDensity_hx7_19`: Huxley's step `19` *paper*
- `LinnikStairs7.charDensity_hy_0`: The step `0` above `5/6`, under `PYWeyl`
- `LinnikStairs7.charDensity_hy_top`: The last step, extended to `σ ≤ 1`, under `PYWeyl`

#### `LinnikStep`: A step of Huxley's bound, exponent `101/50` on `5/6 ≤ σ ≤ 11/12`

- `LinnikStep.class1_step`: The polynomial class with Huxley's estimate on `5/6 ≤ σ ≤ 11/12`
- `LinnikStep.count_step`: The range `5/6 ≤ σ ≤ 11/12`
- `LinnikStep.charDensity_step`: A density estimate over the characters mod `q` with exponent `101/50` on `5/6 ≤ σ ≤ 1` *paper* ([note](../formalisations/huxley-density.md))

#### `LinnikSubconvex`: `|L(1/2 + it, χ)| ≪ (q(|t| + 2))^{5/24+ε}` uniformly in `q`, and Linnik's exponent `17/6 + η`

- `LinnikSubconvex.primitive_bound`: Subconvexity for primitive characters, uniformly in the modulus
- `LinnikSubconvex.prod_primeFactors_le`: `∏_{p | q}(1 + p^{−1/2}) ≤ 2^{⌈e^{1/ε}⌉}q^ε` for `q ≥ 1` and `ε > 0`
- `LinnikSubconvex.critBoundχ`: The bound on the critical line for every character `χ ≠ 1`, uniformly in the modulus
- `LinnikSubconvex.linnik_seventeen_sixths`: Linnik's theorem with exponent `17/6 + η`, with no hypothesis

#### `LinnikTwelve`: The power trick on `3/4 ≤ σ ≤ 11/12` with the estimate, and Linnik's exponent `12/5 + η`

- `LinnikTwelve.class1_twelve`: The polynomial class with Huxley's estimate
- `LinnikTwelve.count_twelve_fifths`: The range `3/4 ≤ σ ≤ 11/12`
- `LinnikTwelve.charDensity_twelve_fifths`: A density estimate over the characters mod `q` with exponent `12/5`
- `LinnikTwelve.linnik_twelve_fifths`: Linnik's theorem with exponent `12/5 + η`, with no hypothesis *paper*

#### `LinnikTwelveBins`: One block and one bin by the large-values estimate, and Ingham's method at `c = 1/10`

- `LinnikTwelve.block_bin_hux`: One dyadic block and one bin, by Huxley's estimate
- `LinnikTwelve.count_middle_c10`: The range `7/12 ≤ σ ≤ 3/4` at `Q = q(T + 6)`

#### `LinnikTwelveSizes`: One block and one bin as a power of `Q` on `3/4 ≤ σ ≤ 11/12`

- `LinnikTwelve.term1_le`: The first term
- `LinnikTwelve.term2_le`: The second term

#### `LinnikWeighted`: The Halász–Montgomery inequality with a smooth weight, its kernel through the primitive

- `LinnikReflect.hm_duality_W`: The Halász–Montgomery inequality with the weight `W(n) = e^{−n/U} − e^{−2n/U}` ([note](../formalisations/halasz-montgomery.md))
- `LinnikReflect.norm_hTerm_le_reflect`: The reflected kernel bound for one pair ([note](../formalisations/halasz-montgomery.md))
- `LinnikReflect.huxley_core`: The product trick against the large values

#### `LinnikWeyl`: The integral class is empty under a pointwise bound on the critical line

- `LinnikWeyl.class2_empty`: The integral class is empty under a pointwise bound
- `LinnikWeyl.class2_finset_empty`: A finite integral class is empty
- `LinnikWeyl.class2_card_eq_zero`: A finite integral class has no members

#### `LinnikWeylBridge`: `PYWeyl` contains `WeylBound`: the Weyl bound for every character gives the Weyl bound for ζ

- `LinnikWeylBridge.weylBound_of_PYWeyl`: `LinnikWeyl.PYWeyl` (all moduli, jointly in `q` and `t`) gives `CrossCriteria.WeylBound` (ζ alone), by its case `q = 1`.

#### `Littlewood`: Littlewood's bounds for `L(1, χ)` at the real characters

- `Littlewood.norm_LSeries_le_of_sum_le`: Partial summation for an L-series
- `Littlewood.logDeriv_le_loglog_of`: The log-derivative on `(1, 2]`, uniformly in the modulus, from a bound on `ψ(x, χ)`
- `Littlewood.logDeriv_le_loglog`: `L′/L(σ, χ) ≪ log log q` on `(1, 2]`
- `Littlewood.norm_LFunction_le_real`: `|L(σ, χ)| ≤ σ/(σ − 1)` and `1/|L(σ, χ)| ≤ σ/(σ − 1)` for `σ > 1`, from the partial sums of `χ` and of `χμ`, each at most `t` in absolute value.
- `Littlewood.abs_log_norm_LFunction_one_le_of`: Littlewood's argument
- `Littlewood.abs_log_norm_LFunction_one_le`: Littlewood's bounds for `L(1, χ)`
- `Littlewood.norm_LFunction_one_le`: `L(1, χ) ≪ log log q`
- `Littlewood.norm_LFunction_one_ge`: `L(1, χ) ≫ 1/log log q`
- `Littlewood.norm_logDeriv_one_le`: `L′/L(1, χ) ≪ log log q`

#### `LogDerivDisc`: The log-derivative of a function with no zero in a half-plane, by the disc step

- `LogDerivDisc.disc_point_ball`: The disc step
- `LogDerivDisc.disc_point`: The disc step
- `LogDerivDisc.logDeriv_le_ball`: The log-derivative of an entire function with no zero in one disc
- `LogDerivDisc.logDeriv_le_uniform_of`: The log-derivative of an entire function in a zero-free half-plane, with its constants
- `LogDerivDisc.logDeriv_le_uniform`: The log-derivative of an entire function in a zero-free half-plane, with its constants

#### `LogDerivKV`: R4a: the log-derivative bound on the Korobov–Vinogradov region

- `LogDerivKV.logDerivBnd_KV`: R4a: `ζ'/ζ = O((log|t|)³)` on the Korobov–Vinogradov region

#### `MediumPNTW`: PNT+'s contour bounds for a zero-free region of general width

- `MediumPNTW.GenPNTW'`: Generic PNT from a width-`D` region, with the small-height abscissa given
- `MediumPNTW.GenPNTWNoEps`: Generic PNT from a width-`D` region, without `1/ε` on the left
- `MediumPNTW.GenPNTW`: Generic PNT from a width-`D` region

#### `MertensChi`: Mertens' function twisted by a character, uniformly in the modulus

- `MertensChi.LSeries_fχμ`: `L(χμ, s) = 1/L(s, χ)` on `Re s > 1` (Mathlib's `LSeries.mul_mu_eq_one`).
- `MertensChi.norm_sum_le`: Mertens' function twisted by a character, uniformly in the modulus
- `MertensChi.isBigO`: For one character `χ ≠ 1`

#### `MertensExponent`: Mertens' function in a zero-free half-plane, and `Θ` as its exponent

- `MertensExponent.mertens_isBigO_of_zeroFree`: Mertens' function in a zero-free half-plane
- `MertensExponent.mertens_isBigO_eleven_twelfths`: `M(x) = O(x^{11/12+η})`
- `MertensExponent.mertens_isBigO_Theta`: `M(x) = O(x^{Θ+η})`
- `MertensExponent.mertens_omega_Theta`: `M(x) = Ω±(x^{Θ−η})`
- `MertensExponent.rh_iff_Theta_eq_half`: `RH ⟺ Θ = ½`
- `MertensExponent.rh_iff_mertens`: Littlewood's criterion
- `MertensExponent.limsup_mexpo`: The exponent of Mertens' function is `Θ`
- `MertensExponent.moebius_tendsto_of_Theta_lt`: `Σ μ(n) n^{−s}` converges for `Re s > Θ`
- `MertensExponent.moebius_not_tendsto_of_lt_Theta`: `Σ μ(n) n^{−s}` diverges for `Re s < Θ`
- `MertensExponent.moebiusAbscissa_eq_Theta`: The abscissa of convergence of `Σ μ(n) n^{−s}` is `Θ`

#### `PNTKV`: The prime number theorem with the Korobov–Vinogradov error term

- `PNTKV.PNT_KV`: The prime number theorem with the Korobov–Vinogradov error term

#### `PNTProgressions`: The prime number theorem modulo the divisors of `24`

- `PNTProgressions.sum_dvd_le_log`: `Σ_{n ≤ N, p ∣ n} Λ(n) ≤ log N` for a prime `p`
- `PNTProgressions.sum_not_coprime_le`: `Σ_{n ≤ N, (n, q) > 1} Λ(n) ≤ ω(q) log N` for `q ≠ 0`.
- `PNTProgressions.psiChi_one`: `ψ(x, χ)` for the trivial character mod `q`
- `PNTProgressions.psiAP_eq_sum`: Orthogonality
- `PNTProgressions.psiAP_isBigO`: The prime number theorem in progressions modulo every `q`

#### `PsiExponent`: The exponent of the error in the prime number theorem

- `PsiExponent.Theta_le`: `Θ ≤ 11/12`
- `PsiExponent.half_le_Theta`: `½ ≤ Θ`
- `PsiExponent.zeta_ne_zero_of_Theta_lt`: `ζ(s) ≠ 0` for `Re s > Θ`.
- `PsiExponent.psi_isBigO_Theta`: The upper half
- `PsiExponent.psi_omega_Theta`: The lower half
- `PsiExponent.limsup_expo`: The exponent of the error in the prime number theorem is `Θ`

#### `QuadClassNumber`: Class numbers, the least inert and split primes and the Euler–Kronecker constant of a quadratic field

- `QuadClassNumber.classNumber_ge`: The class number of an imaginary quadratic field, from below
- `QuadClassNumber.classNumber_le`: The class number of an imaginary quadratic field, from above
- `QuadClassNumber.classNumber_ge_sqrt`: Door 4(b)'s bound for imaginary quadratic fields
- `QuadClassNumber.regulator_mul_classNumber_ge`: The class number and regulator of a real quadratic field, from below
- `QuadClassNumber.regulator_mul_classNumber_le`: The class number and regulator of a real quadratic field, from above
- `QuadClassNumber.regulator_mul_classNumber_ge_sqrt`: Door 4(b)'s bound for real quadratic fields
- `QuadClassNumber.classNumber_ge_loglog`: Door 4(b)'s bound for imaginary quadratic fields, in the form `c√|D_K|/log log |D_K|`
- `QuadClassNumber.regulator_mul_classNumber_ge_loglog`: Door 4(b)'s bound for real quadratic fields, in the form `c√D_K/log log D_K`
- `QuadClassNumber.exists_inert_le`: An inert prime below `C_A(log(|D_K| + 2))^A`
- `QuadClassNumber.exists_split_le`: A split prime below `C_A(log(|D_K| + 2))^A`
- `QuadClassNumber.exists_inert_le_13`: An inert prime below `10²⁹⁸(log(|D_K| + 2))¹³`
- `QuadClassNumber.exists_split_le_13`: A split prime below `10²⁹⁸(log(|D_K| + 2))¹³`
- `QuadClassNumber.eulerKronecker`: The Euler–Kronecker constant of a quadratic field

#### `QuadKronecker`: The Kronecker character of a quadratic field

- `QuadKronecker.jacBot_natCast`
- `QuadKronecker.jacTop_natCast`
- `QuadKronecker.jacobiSym_natAbs`: For `d ≡ 1 (mod 4)` and an odd prime `p`, `J(p | |d|) = J(d | p)`.
- `QuadKronecker.jacobiSym_two_natAbs`: For `d ≡ 1 (mod 4)`, `J(2 | |d|)` is `1` if `d ≡ 1 (mod 8)` and `−1` if `d ≡ 5 (mod 8)`.
- `QuadKronecker.dedekindZeta_eq`: `ζ_K = ζ·L(·, χ)`
- `QuadKronecker.ne_one_of_eq`: A character in a factorization `ζ_K = ζ·L(·, χ)` is not trivial
- `QuadKronecker.type_one`: The splitting law, `d ≡ 1 (mod 4)`
- `QuadKronecker.type_two_three`: The splitting law, `d ≡ 2, 3 (mod 4)`
- `QuadKronecker.exists_kronecker`: The Kronecker character of a quadratic field
- `QuadKronecker.classNumber_formula`: The class number formula for every imaginary quadratic field, with its Kronecker character

#### `QuadRing`: The ring of integers of a quadratic field

- `QuadRing.int_of_mul_sq`: If `d` is squarefree and `d r² ∈ ℤ`, then `r ∈ ℤ`.
- `QuadRing.exists_eq`: Every element of `K` is `a + bs`
- `QuadRing.minpoly_eq`: The minimal polynomial of `a + bs`, `b ≠ 0`, is `X² − 2aX + (a² − db²)`
- `QuadRing.isIntegral_iff`: Integrality of `a + bs`
- `QuadRing.discr_eq_of_basis`: If `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then `D_K = 4c + e²`
- `QuadRing.span_θ₁`: Every integer of `K` is `u + vθ`
- `QuadRing.adjoin_θ₁`: `𝓞 K = ℤ[θ]`
- `QuadRing.discr_θ₁`: The discriminant is `d`
- `QuadRing.minpoly_θ₁`: The minimal polynomial of `θ = (1 + s)/2` over `ℤ` is `X² − X − (d − 1)/4`
- `QuadRing.span_θ₂`
- `QuadRing.adjoin_θ₂`: `𝓞 K = ℤ[s]`
- `QuadRing.discr_θ₂`: The discriminant is `4d`
- `QuadRing.minpoly_θ₂`: The minimal polynomial of `s` over `ℤ` is `X² − d`
- `QuadRing.exists_sqrt`: Every quadratic field contains a square root `s` of a squarefree integer `d ≠ 1`

#### `QuadSplit`: The splitting law in a quadratic field

- `QuadSplit.split_of_factors`
- `QuadSplit.ramified_of_factors`
- `QuadSplit.inert_of_factors`
- `QuadSplit.split_of_root`: The splitting law from the roots mod `p`
- `QuadSplit.ramified_of_root`
- `QuadSplit.inert_of_no_root`
- `QuadSplit.ramified_of_dvd₂`: `p ∣ d`
- `QuadSplit.ramified_two₂`: `2` ramifies.
- `QuadSplit.split₂`: `p` odd, `p ∤ d`, `d` a square mod `p`
- `QuadSplit.inert₂`: `d` not a square mod `p`
- `QuadSplit.ramified_of_dvd₁`: `p` odd, `p ∣ d`
- `QuadSplit.split₁`: `p` odd, `p ∤ d`, `d` a square mod `p`
- `QuadSplit.inert₁`: `d` not a square mod `p`
- `QuadSplit.split_two₁`: `d ≡ 1 (mod 8)`
- `QuadSplit.inert_two₁`: `d ≡ 5 (mod 8)`

#### `ShortKV`: Primes in short intervals: the Korobov–Vinogradov input

- `ShortKV.zeroFreeXi_KV`: The Korobov–Vinogradov region as `ZeroFreeXi (3/4)` ([note](../formalisations/zeta-density.md))

#### `ShortPrimesHalfPlane`: Primes in short intervals for every `θ > 11/17`, from the zero-free half-plane instead of Korobov–Vinogradov

- `ShortPrimesHalfPlane.zeroFreeXi_of_halfplane`: The zero-free half-plane gives `ZeroFreeXi α` for every `α` (here `α < 1` is what `short_primes_of_density` takes), with no Korobov–Vinogradov input. ([note](../formalisations/zeta-density.md))
- `ShortPrimesHalfPlane.short_primes_11_17_noKV`: With it, `short_primes_of_density` at the density `DensityXi (17/6 + ε) 12` of `InghamDensity` needs no KV region (the same statement as…

#### `SieveBrun`: Brun's sieve in product form, abstractly

- `SieveBrun.bonferroni`: Bonferroni's inequalities
- `SieveBrun.fundamental`: The fundamental lemma in product form, abstractly *paper* ([note](../formalisations/harman-sieve.md))
- `SieveBrun.gap_le`: For even `k_j`, `0 ≤ g ≤ 1` on each `T_j`, `C₀ ≥ 0` with `Σ_{T_j} g ≤ C₀`, and `∏_{T_j} (1 − g) ≥ c₀ > 0` ([note](../formalisations/harman-sieve.md))

#### `SieveBuch`: The decomposition to depth 6, with the certificate's classification

- `SieveBuch.Par.T_eq`: Depth 0 *paper*
- `SieveBuch.Par.I_S1`: Depth 1 *paper*
- `SieveBuch.Par.I_S2`: Depth 2 *paper*
- `SieveBuch.Par.I_S3`: Depth 3 *paper*
- `SieveBuch.Par.I_S4`: Depth 4 *paper*
- `SieveBuch.Par.I_S5`: Depth 5 *paper*
- `SieveBuch.Par.I_S6`: Depth 6 *paper*
- `SieveBuch.Par.I_S3c_vanish`: Depth 3, outside `inKK` *paper*
- `SieveBuch.Par.I_S4c_vanish_lt`: Depth 4, `l > k` *paper*
- `SieveBuch.Par.I_S4c_vanish_reg`: Depth 4, outside the region *paper*
- `SieveBuch.Par.I_S5c_vanish_lt`: Depth 5, `eC b ≥ e_l + H` *paper*
- `SieveBuch.Par.I_S5c_vanish_reg`: Depth 5, outside the region *paper*
- `SieveBuch.Par.I_S6c_vanish_lt`: Depth 6, `c > b` *paper*
- `SieveBuch.Par.I_S6c_vanish_reg`: Depth 6, outside the region *paper*
- `SieveBuch.Par.decomp`: The decomposition's inequality

#### `SieveBuch2`: The decomposition with the kept parts of the dropped cells

- `SieveBuch.Par.lvl1k`: Level 1 with the kept parts *paper*
- `SieveBuch.Par.decompk`: The decomposition's inequality with the kept parts *paper*

#### `SieveCert`: The certificate of the sieve route's loss, checked by the kernel

- `SieveCert.total_div_le`: The certificate in the reals
- `SieveCert.cover2`: On a grid with `GridOK`, a point of the region of depth 2 that is not evaluable lies in a candidate cell.
- `SieveCert.cover3`: On a grid with `GridOK`, on a cell that may be decomposed, a non-evaluable `α₃` of the region of depth 3 keeps `α₁ + α₂ + α₃ ≤ 1 − u₂`, and lies in a…
- `SieveCert.cover4`: On a grid with `GridOK`, a non-evaluable point of the region of depth 4 lies in a counted cell, with `l ≤ k`.
- `SieveCert.omegaC_le_w`: `ω*` on a box *paper*
- `SieveCert.omegaC_le`: `ω*` on a cell
- `SieveCert.bound2_ge`: A cell of depth 2 with lower corner `(a, b)` costs at least `omK/K` times the first cell's trapezoid bound and the last cell's `DEN·H/(b(b + H))`. *paper*
- `SieveCert.bound4_ge`: A cell of depth 4 with lower corner `(a, b, c, d)` costs at least `omK/K` times the trapezoid bounds of the first three cells and the last cell's… *paper*
- `SieveCert.bound6_ge`: A cell of depth 6 (four fine cells and two coarse ones) with lower corner `(a, b, c, d, f, g)` costs at least `omKw/K` times the trapezoid bounds of the… *paper*

#### `SieveCert2`: The refined certificate, in the reals and over `Finset`

- `SieveCert.cost2_ge`: A dropped candidate cell's refined cost is at least its bound less `sub2`, in the reals.
- `SieveCert.keepK_le`: The kept share's bound

#### `SieveCert22240R`: The refined certificate of the sieve route's loss at `L = 278/125` with `n = 340`: `total2 < K`

- `SieveCert.total2_lt_22240R`: The refined certificate on `grid22240R` *paper*

#### `SieveChain`: Type II for chains of primes

- `SieveChain.sum_rough_tuples`: For `z ≥ 2`, `Y ≥ 1` and `Y < z^{K+1}`, the `z`-rough `k ∈ [1, Y]` are the products of the non-increasing tuples of at most `K` primes at least `z`, the… *paper*
- `SieveChain.typeII_gcmp'`: `typeII_gcmp` (with `RouteOK` and `hII`) for any number `K ≥ 1` of primes.
- `SieveChain.chainTU_bound`: Chains times a rough cofactor in the window *paper*
- `SieveChain.chainTL_bound`: Chains with a product of some of their primes in the window *paper*

#### `SieveChainR`: Type II for chains with part of their product in the reflection of the window

- `SieveChainR.chainTR_bound`: Chains with part of their product in the reflection of the window

#### `SieveCount`: Type I counts in a residue class

- `SieveCount.card_A`: Type I for `A` *paper*
- `SieveCount.card_B`: Type I for `B` *paper*

#### `SieveDecomp`: Families of prime tuples, and Buchstab's identity on them

- `SieveDecomp.buchstab_fam`: Buchstab's identity on a family *paper* ([note](../formalisations/harman-sieve.md))
- `SieveDecomp.famI_cells`: The cells of the prime `t`
- `SieveDecomp.famI_vanish`: A family whose products are at most `N₁` and whose products times their last prime exceed `N₂` contributes `0`

#### `SieveDiff`: The tree's weights, and a leaf's difference

- `SieveDiff.leaf_diff`: A leaf's difference

#### `SieveDrop`: The dropped terms' `B`-count

- `SieveDrop.drop2_le`: A dropped cell of depth 2 *paper*
- `SieveDrop.drop4_le`: A dropped cell of depth 4 *paper*
- `SieveDrop.drop6_le`: A dropped cell of depth 6 *paper*
- `SieveDrop.corner_le`: A corner cell *paper*
- `SieveDrop.corner_ev`: The corner is `o(x/log x)` *paper*
- `SieveDrop.shares_ev`: The shares, eventually *paper*
- `SieveDrop.drop_ev`: The dropped terms, for large `q`

#### `SieveDrop2`: The dropped terms less the kept parts

- `SieveDrop2.drop_ev2`: The dropped terms less the kept parts, for large `q` *paper*

#### `SieveDyadic`: A dyadic partition of unity

- `SieveDyadic.sum_bump`: The dyadic partition of unity

#### `SieveExact`: Type II for exact products of chains of primes

- `SieveExact.chainT0_bound`: Exact products of chains with a product of some of their primes in the window *paper*
- `SieveExact.T0_spec`: Exact products, on a family of atoms

#### `SieveFamily`: Type II families

- `SieveFamily.family_bound`: The bound for a smooth family
- `SieveFamily.Dsum_sharp_le`: A sharp family, explicitly
- `SieveFamily.typeII_sharp_explicit`: A sharp family, with the Type II estimate
- `SieveFamily.typeII_sharp`: The Type II estimate for a sharp family (Lemmas 4′ and 4″), asymptotic form *paper*

#### `SieveGrid22240R`: The grid of the refined certificate at `L = 278/125` with `n = 340`

- `SieveCert.gridOK22240R` *paper*
- `SieveCert.gridOKC22240R`: The coarse grid `Gc` (`n / 4 = 85` cells) and the facts about it that the deepest levels use. *paper*

#### `SieveHMBin`: Halász–Montgomery for one bin of characters at one height

- `SieveTypeIIHM.dp_eq_pv`: The bridge
- `SieveTypeIIHM.sum_bin_hm`: Halász–Montgomery for one bin at one height *paper* ([note](../formalisations/halasz-montgomery.md))

#### `SieveHMBins`: Proposition 3′ pointwise, by bins, with the Halász–Montgomery bound per bin

- `SieveTypeIIHM.sum_typeII_bins_hm`: Proposition 3′ pointwise, by bins, with the better bound per bin *paper*
- `SieveTypeIIHM.offK_bound`: A uniform kernel bound at `z = 0` *paper*

#### `SieveHMWindow`: The window condition with the Halász–Montgomery branch

- `SieveCurveGlue.affine_corner_bound`: A function affine in each of `w`, `β`, `m` separately is at most its maximum over the corners of a box
- `SieveCurveGlue.windowPieceHM_affine`: An affine piece by the Halász–Montgomery branch
- `SieveCurveGlue.windowPieceHM_affine_split`: An affine piece by the Halász–Montgomery branch below `m = 1` and by orthogonality above it
- `SieveCurveGlue.windowPieceHM_const_split`: The piece `g β = A(1 − β)` by `windowPieceHM_affine_split` at `p = A` (as `windowPiece_const`), for `lo ≤ hi` (`hlo`) and the corner inequalities `h1`, `h2`…

#### `SieveKept`: The kept parts of the dropped cells of depth 2

- `SieveBuch.Par.Kp2_le`: The kept parts are terms of the dropped term *paper*
- `SieveBuch.Par.Kk_eq`: The kept part as three sorted families *paper*

#### `SieveKeptB`: The kept parts' `B`-count, from below

- `SieveKeptB.Kk_gB_ge`: The kept part's `B`-count, from below *paper*

#### `SieveKeptLeaf`: The kept parts' leaves at `x = q^L`

- `SieveKeptLeaf.lf_Kk`: A kept part's leaf *paper*
- `SieveKeptLeaf.leaves_ev2`: The leaves and the kept leaves, for large `q` *paper*

#### `SieveLeaf`: The leaves of Buchstab's tree, by the fundamental lemma

- `SieveLeaf.leaf_A`: A leaf, for `A` ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.leaf_B`: A leaf, for `B/φ(q)` ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.leaf_gap`: The relative error of a leaf *paper* ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.prod_primesBelow_le`: Mertens' product bound, in its elementary form *paper* ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.prod_T_le`: The main term of a leaf *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveLeaves`: The leaves' estimates on families of atoms

- `SieveLeaves.TL_spec`: The lower window, on a family of atoms
- `SieveLeaves.TU_spec`: The upper window, on a family of atoms
- `SieveLeaves.TR_spec`: The reflected window, on a family of atoms
- `SieveLeaves.P6_spec`: Proposition 6, on a family of atoms ([note](../formalisations/harman-sieve.md))
- `SieveLeaves.P6IB_spec`: Proposition 6 with the bilinear estimate, on a family of atoms

#### `SieveLemma1`: Weighted prime sums at a height inside a zero-free rectangle (Lemma 1 of the sieve route, `Λ` form)

- `SieveLemma1.perron_weight`: Perron's formula with a weight `w`
- `SieveLemma1.norm_Sw_le`: Lemma 1 in `Λ` form

#### `SieveMain`: Linnik's theorem by the sieve route

- `SieveMain.TB_ev`: For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), and `ε > 0`
- `SieveMain.linnik_large`: Linnik's theorem at `x = q^L`, for large `q`
- `SieveMain.linnik_route`: Linnik's theorem with exponent `L`
- `SieveMain.linnik_route_lt`: Linnik's theorem with exponent `L`, under a certificate whose total is below `K`

#### `SieveMain2`: Linnik's theorem by the sieve route, under the refined certificate

- `SieveMain2.linnik_large2`: Linnik's theorem at `x = q^L`, for large `q`, under the refined certificate *paper*
- `SieveMain2.linnik_route_lt2`: Linnik's theorem with exponent `L`, under a refined certificate whose total is below `K` *paper*

#### `SieveOmegaB`: Buchstab's `ω` on `[2, 3]`, and the logarithm's bounds of the certificate's cells

- `SieveOmegaB.log_le_half_sub_inv`: `log y ≤ (y − 1/y)/2` for `y ≥ 1` *paper*
- `SieveOmegaB.two_mul_div_le_log`: `2(y − 1)/(y + 1) ≤ log y` for `y ≥ 1` *paper*
- `SieveOmegaB.omB_le_w1`: The maximum of Buchstab's `ω` on `[2, 3]` *paper*
- `SieveOmegaB.omB_mono`: Buchstab's `ω` increases on `[2, 2.76]` *paper*
- `SieveOmegaB.omB_anti`: Buchstab's `ω` decreases from `2.77` on *paper*
- `SieveOmegaB.lnT_ge`: The table *paper*
- `SieveOmegaB.omF_ge`: `omF` bounds Buchstab's `ω` *paper*

#### `SieveP6ib`: Proposition 6 with the bilinear estimate

- `SieveP6ib.prop6ib`: Proposition 6 with the bilinear estimate

#### `SieveProp6`: Proposition 6, Harman's fundamental theorem in the form used

- `SieveProp6.leaf_bound`: A leaf *paper* ([note](../formalisations/harman-sieve.md))
- `SieveProp6.prop6`: Proposition 6 *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveQ`: The decomposition at `x = q^L`, and its leaves for large `q`

- `SieveQ.good_of_large`: The decomposition's hypotheses hold for large `q`
- `SieveQ.P6IB_boxes`: Proposition 6-ib, uniformly over finitely many boxes
- `SieveQ.leaves_ev`: The leaves, for large `q` *paper*

#### `SieveRanges`: The ranges of Brun's sieve

- `SieveRanges.rng_sum_le`: The prime sums of the ranges `rng A`, `A ≥ 1`, are uniformly bounded

#### `SieveRough`: Rough numbers from above, and the shares of the certificate's cells

- `SieveRough.Psi_le_buchstab`: Buchstab's inequality *paper*
- `SieveRough.super_M`: The supersolution property *paper*
- `SieveRough.psi_le`: Rough numbers from above *paper* ([note](../formalisations/harman-sieve.md))
- `SieveRough.evLe_cell_tr`: On a grid with `GridOK`, the cell's `Σ 1/p` is at most the trapezoid bound `trB(e_k, H) = H(2e_k + H)/(2e_k(e_k + H))` of `log(1 + H/e_k)`, up to `o(1)`. *paper*
- `SieveRough.evLe_cell_ex`: On a grid with `GridOK`, the cell's `log x · Σ 1/(p log p)` is at most `exB(e_k, H) = H·DEN/(e_k(e_k + H))`, the exact `DEN(1/e_k − 1/(e_k + H))`, up to `o(1)`. *paper*
- `SieveRough.share2`: The share of a cell of depth 2
- `SieveRough.share4`: The share of a cell of depth 4
- `SieveRough.share2_of_cand`: `share2` on a candidate cell, on a grid with `GridOK`. ([note](../formalisations/harman-sieve.md))
- `SieveRough.share4_of_counted4`: `share4` on a counted cell, on a grid with `GridOK`. ([note](../formalisations/harman-sieve.md))

#### `SieveRoughLo`: Sums over the primes of a cell, from below

- `SieveRoughLo.evGe_cell_inv`: The cell's `Σ 1/p`, from below
- `SieveRoughLo.evGe_cell_tr`: The cell's `Σ 1/p`, from below, sharper *paper*

#### `SieveRoughTuple`: Rough numbers as tuples of primes

- `SieveRoughTuple.sum_rough_eq`: Rough numbers as tuples of primes

#### `SieveRoute`: The parameters of the sieve route, and its Type II input

- `SieveRoute.routeOK2333`
- `SieveRoute.typeII2333`: `SieveTypeII.typeII_step` as `TypeIIAt`

#### `SieveSep`: Separation of smooth comparisons by Fourier inversion over `ℝ^J`

- `SieveSep.sum_sep`: Separation of a finite sum
- `SieveSep.sep_bound`: The bound after separation

#### `SieveSmooth`: The smooth cut-off, and the separation of two variables

- `SieveSmooth.indicator_sub_G`: The cut-off against the indicator
- `SieveSmooth.pow_mul_norm_fourier_GC_le`: Decay of the cut-off's Fourier transform
- `SieveSmooth.integrable_fourier_GC`
- `SieveSmooth.GC_sub_eq_integral`: Separation by Fourier inversion

#### `SieveSpline`: Weights for the bilinear Type I estimate: Parseval for the weight, intervals and splines

- `SieveSpline.what_spl`: The spline's transform
- `SieveSpline.norm_what_spl_tail`: The spline's tail
- `SieveSpline.norm_Ew_spl_le`: `E_w` for a spline
- `SieveSpline.typeIB_spline`: The bilinear Type I estimate with a spline weight

#### `SieveStops1`: A stop's cofactor, and the stops below the window

- `SieveStops1.stops1_bound`: The stops below the window
- `SieveStops1.window_bound`: The terms inside the window

#### `SieveStops2`: The stops of Buchstab's tree above the threshold

- `SieveStops2.typeII_cmp`: Type II with a list of comparisons
- `SieveStops2.stops2_bound`: The stops above the threshold *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveTree`: Buchstab's tree over a finite set

- `SieveTree.tree_pt`: The Buchstab tree at one `n` *paper*
- `SieveTree.tree_sum`: The Buchstab tree over a finite set

#### `SieveTypeIB`: A bilinear Type I estimate by Parseval's identity

- `SieveTypeIB.sum_bilinear`: The bilinear sum in Fourier form
- `SieveTypeIB.typeIB_bound`: The bilinear Type I estimate

#### `SieveTypeII`: The Type II estimate of the sieve route at small heights (Proposition 3′, pointwise in the heights)

- `SieveTypeII.sum_chars_dp_sq_le`: Orthogonality (T1) *paper* ([note](../formalisations/mean-values.md))
- `SieveTypeII.typeII_pointwise`: Proposition 3′ pointwise, with Lemma 1 and (T1)
- `SieveTypeII.exponent_le`: The window's exponents
- `SieveTypeII.typeII_step`: Proposition 3′ for the curve step at `L = 2333/1000`, pointwise in the heights

#### `SieveTypeIIGen`: The Type II estimate for a curve and a window (Proposition 3′ with parameters)

- `SieveTypeIIGen.card_bin_gen`: The count of a bin of the grid
- `SieveTypeIIGen.bin_bound_gen`: One bin
- `SieveTypeIIGen.prod_MB_le_gen`: The product of Lemma 1's bounds
- `SieveTypeIIGen.typeII_gen`: Proposition 3′ for a curve and a window, pointwise in the heights

#### `SieveTypeIIHM`: The bin bound with the Halász–Montgomery branch, and Proposition 3′ for a curve on a window

- `SieveTypeIIHM.bin_bound_pt`: One bin by orthogonality, at one point
- `SieveTypeIIHM.bin_bound_gen_hm`: One bin, with the better bound *paper*
- `SieveTypeIIHM.typeII_gen_hm`: Proposition 3′ for a curve and a window with the Halász–Montgomery branch, pointwise in the heights *paper*

#### `SieveTypeIIR`: Type II for a variable times a rough cofactor

- `SieveTypeIIR.typeII_rough`: Type II for a variable times a rough cofactor

#### `SieveTypeIIU`: Type II families with sharp prime ranges

- `SieveTypeIIU.typeII_unw`: Type II for families with sharp prime ranges *paper*

#### `SieveTypeIIU22015D`: Proposition 3′ at `L = 4403 / 2000` on the window `[43336/100000, 46995/100000]·L`, for the curve `g7d`

- `SieveTypeIIU22015D.window_22015d`: The window's exponents
- `SieveTypeIIU22015D.typeII_22015d`: Proposition 3′ at `L = 4403 / 2000` on `[43336/100000, 46995/100000]·L`, for the curve `g7d`

#### `SieveTypeIIU22240D`: Proposition 3′ at `L = 278 / 125` on the Halász–Montgomery window `[41556/100000, 47531/100000]·L`, for the curve `g7d`

- `SieveTypeIIU22240D.g7d_le_one`: `g7d ≤ 1` *paper*
- `SieveTypeIIU22240D.g7d_half` *paper*
- `SieveTypeIIU22240D.g7d_le_lin`: `g7d σ ≤ (11667 / 5000)(1 − σ)` for `σ ≤ 1` *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `SieveTypeIIU22240D.counts_7d`: The counts of the curve *paper*
- `SieveTypeIIU22240D.window_22240d`: The window's exponents *paper*
- `SieveTypeIIU22240D.typeII_22240d`: Proposition 3′ at `L = 278 / 125` on `[41556/100000, 47531/100000]·L`, for the curve `g7d` *paper*

#### `SieveTypeIIU226C`: The curve `g7` without Petrow–Young's bound, `g7c`, at `L = 226/100`: its Halász–Montgomery window and

- `SieveTypeIIU226C.counts_7c`: The counts of the curve ([note](../formalisations/chen-gupta-li-density.md))
- `SieveTypeIIU226C.window_226c`: The window's exponents
- `SieveTypeIIU226C.typeII_226c`: Proposition 3′ at `L = 226/100` on `[4075/10000, 4835/10000]·L`, for the curve `g7c`

#### `SieveTypeIIU227`: The Weyl-conditional curve at `L = 227/100`: Ingham's and Huxley's staircases, Huxley's curve above `5/6`

- `SieveTypeIIU227.counts_7`: The counts of the curve
- `SieveTypeIIU227.window_7`: The window's exponents
- `SieveTypeIIU227.typeII_227`: Proposition 3′ at `L = 227/100` on `[4048/10000, 4858/10000]·L`, for the curve `g7`

#### `SieveWeight`: Lemma 1 of the sieve route for primes, with weights uniform in the scale

- `SieveWeight.exists_mellin_bound`: The Mellin transform of `ψ_P`, uniformly in `P ≥ 4`
- `SieveWeight.norm_Sw_wy_le`: Lemma 1 for the weights `ψ_P`, in `Λ` form, uniformly in `P ≥ 4`
- `SieveWeight.norm_Sp_le`: Lemma 1 for primes *paper*

#### `SmoothPerron`: A smoothed Perron formula for a general Dirichlet series

- `SmoothPerron.verticalIntegral_eq_smoothedSum`: The smoothed Perron formula
- `SmoothPerron.verticalIntegral_shift`: Moving the line of integration
- `SmoothPerron.mellin_le_geom_of`: The Mellin transform of `Smooth1` on a line, from two Mellin bounds
- `SmoothPerron.mellin_le_geom`: The Mellin transform of `Smooth1` on a line
- `SmoothPerron.norm_smoothedSum_sub_le`: Unsmoothing
- `SmoothPerron.verticalIntegral_integrand_shift`: Moving the Perron integral from `Re s = 2` to `Re s = σ′`
- `SmoothPerron.smoothedSum_eq_verticalIntegral_left`: The smoothed sum as an integral on a line left of `1`

#### `SquarefreeCount`: Squarefree numbers in a zero-free half-plane

- `SquarefreeCount.sum_sqf_eq`: `Q(N) = Σ_{d ≤ N} μ(d)⌊N/d²⌋`
- `SquarefreeCount.hasSum_moebius_div_sq`: `Σ μ(d)/d² = 1/ζ(2) = 6/π²`.
- `SquarefreeCount.abs_sub_sum_le`: The tail of `Σ μ(d)/d²`
- `SquarefreeCount.abs_sum_sqf_sub_le`: The count at an integer
- `SquarefreeCount.squarefree_isBigO_of_zeroFree`: Squarefree numbers in a zero-free half-plane
- `SquarefreeCount.squarefree_isBigO_twelve_25ths`: `Q(x) = 6x/π² + O(x^{12/25+η})`
- `SquarefreeCount.squarefree_isBigO_Theta`: `Q(x) = 6x/π² + O(x^{1/(3−Θ)+η})`

#### `Subconvexity`: Subconvexity from a zero-free half-plane

- `Subconvexity.zeta_strip_of_zeroFree`: Subconvexity from a zero-free half-plane
- `Subconvexity.zeta_strip_eleven_twelfths`: On the strip `1/12 ≤ σ ≤ 11/12`, with no hypothesis ([note](../formalisations/zeta-density.md))
- `Subconvexity.zetaCritBound_of_zeroFree`: On the critical line
- `Subconvexity.zetaCritBound_five_24`: Subconvexity on the critical line, with no hypothesis
- `Subconvexity.convexityBound`: The convexity bound
- `Subconvexity.zetaCritBound_Theta`: At `Θ`, the supremum of the real parts of the nontrivial zeros
- `Subconvexity.lindelof_of_RH`: RH implies Lindelöf

#### `TwinKV`: The Korobov–Vinogradov region as a lower bound on the twin form

- `TwinKV.twins_lower_KV`: The KV-graded lower bound for the twin form
- `TwinKV.twins_lower_KV'`: The KV-graded lower bound in explicit shape
- `TwinKV.twins_lower_cut`: The lower bound with a free cutoff `u`
- `TwinKV.twins_lower_KV_sharp`: The twin form with the PNT exponent

#### `ZetaAFE`: The approximate functional equation for `ξ(s)²`

- `ZetaFourth.afe_xi`: The approximate functional equation for `ξ(s)²`

#### `ZetaFourth`: The fourth moment of `ζ(½ + it)` at well-spaced points

- `ZetaFourth.zeta_fourth_moment`: The fourth moment of `ζ(½ + it)` at well-spaced points ([note](../formalisations/zeta-density.md))

#### `ZetaGMDensity`: The density exponent `30/13` for `ζ`, and primes in short intervals for `θ > 17/30`

- `ZetaGMDensity.densityXi_thirty_thirteenths`: Zero density at Guth and Maynard's exponent `30/13` ([note](../formalisations/zeta-density.md))
- `ZetaGMDensity.short_primes_seventeen_thirtieths`: Primes in short intervals for every `θ > 17/30`
- `ZetaGMDensity.almost_all_short_primes_two_fifteenths`: Primes in almost all short intervals for every `θ > 2/15`

#### `ZetaGMHux`: Huxley's count for `ζ` on `4/5 ≤ σ ≤ 11/12`, at the exponent `30/13`

- `ZetaGMHux.nx_gmh`: The density estimate at the exponent `30/13` on `4/5 ≤ σ ≤ 11/12` ([note](../formalisations/zeta-density.md))

#### `ZetaGMIngham`: Ingham's count for `ζ` up to `σ = 7/10 + η`, at the exponent `30/13`

- `ZetaGMIngham.nx_ingham13`: The count at the exponent `30/13` on `17/30 ≤ σ ≤ 7/10 + η` ([note](../formalisations/zeta-density.md))

#### `ZetaGMLV`: Guth–Maynard's large values estimate at `1`-separated points

- `ZetaGMLV.gm_prop31_one`: Guth and Maynard's key proposition at `q = 1` ([note](../formalisations/zeta-density.md))
- `ZetaGMLV.gm_large_values`: Guth and Maynard's large values estimate ([note](../formalisations/zeta-density.md))

#### `ZetaGMWin`: Guth and Maynard's exponent for `ζ` on `7/10 + η ≤ σ ≤ 4/5`

- `ZetaGMWin.nx_gm`: The density estimate with Guth and Maynard's exponent on `7/10 + η ≤ σ ≤ 4/5` ([note](../formalisations/zeta-density.md))

#### `ZetaHuxley`: The density exponent `12/5` for `ζ` on `3/4 ≤ σ ≤ 11/12`, and primes in short intervals for `θ > 7/12`

- `ZetaHuxley.nx_huxley`: The density estimate with Huxley's exponent on `3/4 ≤ σ ≤ 11/12` ([note](../formalisations/zeta-density.md))
- `ZetaHuxley.densityXi_twelve_fifths`: Zero density at the exponent `12/5` ([note](../formalisations/zeta-density.md))
- `ZetaHuxley.short_primes_seven_twelfths`: Primes in short intervals for every `θ > 7/12` ([note](../formalisations/zeta-density.md))

#### `ZetaIngham`: Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4`

- `ZetaIngham.nx_ingham`: Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4` ([note](../formalisations/zeta-density.md))

#### `ZetaKernel`: The Halász–Montgomery inequality at well-spaced heights, and the kernel of `ζ` past its pole

- `ZetaKernel.hm_duality_pts`: The Halász–Montgomery duality inequality at points
- `ZetaKernel.norm_kz_le`: The kernel bound ([note](../formalisations/zeta-density.md))
- `ZetaKernel.power_count_pts`: Large values of a power at well-spaced heights

## Modules outside `Check` and `CheckAll`

### `lib/core`

#### `AngularResidue`: The residue of the radial member and `L(1, χ₋₄) = π/4`

- `AngularResidue.latticeCount_two_sqrt`: Lattice count = shell sum
- `AngularResidue.residue_angular`: The residue of the radial member
- `AngularResidue.LFunction_chi4_one`: `L(1, χ₋₄) = π/4`

#### `BohrTorus`: The Bohr torus: Vinogradov's orthogonality on the lift of a vertical line

- `BohrTorus.eq_zero_of_sum_log`: The logarithms of distinct primes are linearly independent over `ℤ`
- `BohrTorus.tendsto_mean_character`: The character means along the Bohr line
- `BohrTorus.bohr_line`: The Bohr lift of the line `Re s = σ` runs on the torus
- `BohrTorus.sum_norm_sq_torus`: Every point of the torus has the same norm
- `BohrTorus.tendsto_mean_trigSum`: For every trigonometric polynomial on the torus, the mean along the Bohr line tends to the integral over the torus
- `BohrTorus.tendsto_mean_moment`: The moments along the line are the torus moments
- `BohrTorus.integral_moment_eq_count`: The torus moment of the unweighted prime sum is a Vinogradov count
- `BohrTorus.tendsto_mean_moment_count`: The limiting means of `|Σ_{p∈F} p^{−it}|^{2ℓ}` are the count
- `BohrTorus.prod_eq_iff_map_eq`: The multiplicative system is rigid at every `ℓ`
- `BohrTorus.agree_not_rigid`: The additive system is not rigid beyond its dimension
- `BohrTorus.tendsto_mean_moment_rearrangements`: The limiting means of `|Σ_{p∈F} p^{−it}|^{2ℓ}` count the pairs of rearrangements

#### `CertInstances`: The certificate theorems as instances of the weighted certificate

#### `ChiHalfSharp`: `GoodChar.half` from `hS`; kernel identities; sharper local constants

- `ChiHalf.grh_half_iff`: The decomposition
- `ChiHalf.QC_nonneg_of_GRH'`: Real zeros are invisible to the `ĝ²` form
- `ChiHalf.grh_of_twin_criterion`: The twin criterion without `hS` would decide the Siegel question
- `ArchKerQuarter.archKer_quarter_add`: The `Γ_ℂ` kernel
- `LocalSharp.card_local_le_sharp`: The local count with `5/2` in place of `13/2`

#### `DecayCorollaries`: Decay corollaries and the weak VMVT

#### `EuclideanForcing`: The forcing of the Euclidean unit ball

- `EuclideanForcing.eq_closedBall_of_innerPolar_eq`: Uniqueness
- `EuclideanForcing.innerPolar_eq_self_iff`: The Euclidean ball is forced by self-duality
- `EuclideanForcing.ell2_innerPolar_eq_self_iff`: The infinite-dimensional case
- `EuclideanForcing.innerPolar_lpBall`: Hölder duality
- `EuclideanForcing.innerPolar_lpBall_critExp`: The reflection in the critical line acts as the polarity
- `EuclideanForcing.innerPolar_lpBall_eq_self_iff`: Among the `ℓ^p` balls, self-duality forces `p = 2`
- `EuclideanForcing.innerPolar_lpBall_critExp_eq_self_iff`: The threshold ball is its own polar, hence Euclidean, exactly on the line
- `EuclideanForcing.tendsto_inner_fraction_cube`: The cube concentrates at its surface too

#### `EulerGammaBinet`: Euler's constant to seven digits, from Binet's formula

- `Electron.eulerMascheroni_bounds`: Euler's constant to seven digits

#### `ExteriorZeta`: The exterior identity over the zeros of `ζ`, for every probe

- `WeilForm.chi_strip`: `χ` in the strip class
- `WeilForm.exterior_identity_probe_zeta`: 1ca(iv) over the zeros of `ζ`, for every even probe, with no named input

#### `GhatSamples`: The Fourier coefficients of a probe are samples of `ĝ`

- `GhatSamples.hasSum_ghat_samples`: Sampled Plancherel

#### `GroundBlock`: The ground space as a negative block of Weil's form

- `WeilForm.striptest_Gpole`: The transform of a Green image is a strip test function
- `WeilForm.exists_ground_block`: A ground space with `λ₁ < 0` carries a negative block of `Q` of codimension one
- `WeilForm.gdim_sub_one_le_quadruples`: `gdim − 1` is at most the number of off-line quadruples
- `WeilForm.gdim_le_of_lam_neg`: Under the join, `λ₁ < 0` forces `gdim ≤ ⌊(M − 1)/2⌋ + 1`
- `WeilForm.rh_of_dim_bounded`: RH from (a) and any eventual dimension bound
- `WeilForm.rh_or_gdim_tendsto`: The dichotomy

#### `GroundIndex`: The ground-state ↔ Weil-index join

- `WeilForm.zeta_upper_offline_card_le`: At most `⌊(M − 1)/2⌋` zeros of `ζ` with `Re s > ½` and `Im s > 0`
- `WeilForm.finrank_le_ground_index`: The join: negative directions of Weil's form are at most `⌊(M − 1)/2⌋`
- `WeilForm.finrank_le_ground_index_C2`: The same for `C²` probes vanishing near `±b`
- `WeilForm.gdim_lower_of_neg_block`: Contrapositive: a certified negative block forces a ground-space dimension

#### `HalfPlaneJoinsChar`: The band for every `L(s, χ)` and the twin-form rates at `11/12`

- `HalfPlaneJoins.LFunction_band_of_isPrimitive`: The band for a primitive `χ ≠ 1`
- `HalfPlaneJoins.LFunction_band_eleven_twelfths`: The band `|2 Re ρ − 1| ≤ 5/6` for every `L(s, χ)`, `χ ≠ 1`
- `HalfPlaneJoins.chi4_rate_eleven_twelfths`: `L(s, χ₋₄)`'s twin form
- `HalfPlaneJoins.chi8_rate_eleven_twelfths`: `L(s, χ₋₈)`'s twin form
- `HalfPlaneJoins.QK4_rate_eleven_twelfths`: The twin form `2Q_ζ + Q_{χ₋₄}` of `ζ·ζ_{ℚ(i)}`
- `HalfPlaneJoins.QC_rate_eleven_twelfths`: Every good character
- `HalfPlaneJoins.QKχ_rate_eleven_twelfths`: The twin form `2Q_ζ + Q_χ` of `ζ·L(χ)`, every good character
- `HalfPlaneJoins.realRooted_rate_eleven_twelfths`: Every real-rooted monotone base probe

#### `HalfPlaneTrivial`: The trivial range of S0's hypothesis

- `HalfPlaneS0.smoothBound_of_one_le`: The trivial range of the hypothesis

#### `KernelChain`: RH from `L²` closeness to Riemann's kernel

- `WeilForm.kernelApprox_RPhi`: `KernelApprox` holds for Riemann's kernel
- `WeilForm.rh_of_close_RPhi`: RH from `L²` closeness to Riemann's kernel

#### `LSeriesLandau`: Landau's theorem for Dirichlet series with nonnegative coefficients

- `LandauLaplace.LSeries_landau`: Landau's theorem for L-series with nonnegative coefficients
- `LandauLaplace.LSeries_not_holomorphic_at_abscissa`: An L-series with nonnegative coefficients is singular at the real point of its abscissa

#### `LatticeCount`: The ball tower from counting integer points

- `BallTower.count_div_tendsto_ballVol`: Counting integer points gives the ball tower
- `BallTower.count_div_pow_tendsto_ballVol`: Same statement by radius

#### `LocalTeeth`: The teeth, one prime at a time

- `LocalTeeth.card_two_sq`: 2D teeth mod `p`, nonzero shell
- `LocalTeeth.card_two_sq_zero`: 2D teeth mod `p`, zero shell
- `LocalTeeth.card_four_sq`: 4D teeth mod `p`, nonzero shell
- `LocalTeeth.teeth_mod_prime`: At a prime `p`

#### `OddProbe`: Odd probes and real characters

#### `ParityCert`: Weil positivity in both parity sectors, as far as the relaxation reaches

- `WeilForm.weilQ_ge_E`: Even-sector positivity up to `a* = 0.80`
- `WeilForm.weilQ_ge_O`: Odd-sector positivity up to `a* = 0.80`
- `WeilForm.weilQg_ge_both`: Weil positivity for every real `g`

#### `ParityGapLower`: A parity gap from a one-sector lower bound at the prefactor scale

- `ParityGapLower.parityGap_of_lamO_lower`: The eventual parity gap from an odd lower bound at the Connes scale
- `ParityGapLower.rh_of_lamO_lower`: RH from `HypConv` and an odd lower bound at the Connes scale
- `ParityGapLower.ghatC_re_eq_zero_of_odd`: Odd transforms are purely imaginary on `ℝ`

#### `ParityRelax`: The relaxation for both parities and every prime power below the support

- `WeilForm.trunc_W`: Truncation with a weight
- `WeilForm.primeS_range`: The prime side below `e^{2a}`
- `WeilForm.weilQ_ge_relaxW`: The even relaxation with a general weight
- `WeilForm.weilQodd_ge_relaxW`: The odd relaxation with a general weight
- `WeilForm.weilQ_ge_of_certW`: The even certificate theorem
- `WeilForm.weilQodd_ge_of_certW`: The odd certificate theorem
- `WeilForm.weilQg_ge_min`: Both parities

#### `PrimeRelax`: Weil positivity past the first prime: every support `2a ≤ 0.8`

- `WeilForm.weilQ_ge_of_certP`: The certificate theorem below `log 3`
- `WeilForm.weilQ_ge_prime`: Weil positivity through the first prime

#### `PrimeRelax3`: Weil positivity up to the second prime: every support `2a ≤ 1.0986 < log 3`

- `WeilForm.weilQ_ge_prime3`: Weil positivity up to the second prime

#### `PsiReQDup`: The duplication formula for `Re ψ`

#### `ResponseKernel`: Response kernel and tone calculus, unconditional

- `RespKernel.response_kernel`: The response kernel (the first order), unconditional

#### `SixteenPi`: The constant `1/(16π)`: the Gaussian-multiplier time

- `WeilForm.wall_quadratic`: Quadratic stationarity at the wall
- `WeilForm.tau_at_wall`: The constant (3.6)
- `WeilForm.balayageSide_eq`: The rescaling `t = Xs`
- `WeilForm.J_eq`: `J(X)`
- `WeilForm.exteriorMoment_eq`: The exterior moment, given the balayage identity
- `WeilForm.sixteenPi_of_balayage`: The chain (iii)–(v), assembled
- `WeilForm.inv_sq_sub_le`: One displaced zero
- `WeilForm.defect_sub_tail`: (3.2): matched zeros cancel
- `WeilForm.defect_eq_tail_of_D`: Exact D ⇒ the exterior form (3.2)
- `WeilForm.defect_sub_tail_le`: D within tolerance (the paper's census)
- `WeilForm.multiplier_expansion`: (3.1), exactly
- `WeilForm.kBal_pair`: The pair kernel
- `WeilForm.balayage_identity`: The balayage identity, proved
- `WeilForm.exteriorMoment_reduced`: The exterior moment of the reduced problem, with no hypothesis
- `WeilForm.sixteenPi_reduced`: `1/(16π)` in the reduced problem, with no hypothesis
- `WeilForm.fBalExp_le`: The wall
- `WeilForm.integral_logRep`: The logarithm as an integral
- `WeilForm.integral_Qv`: The `v`-integral
- `WeilForm.Ibal_closed`: The Cauchy integral in closed form
- `WeilForm.tauBal_closed`: The balayage density in closed form
- `WeilForm.tauBal_two`: Admissibility at the wall, proved

#### `SphereDimensions`: Every point of the unit sphere is a dimension, and the sphere is the line

- `SphereDimensions.mem_orthonormalBasis_iff`: In finite dimension the points of the unit sphere are exactly the basis directions
- `SphereDimensions.mem_hilbertBasis_iff`: In a Hilbert space of any dimension the points of the unit sphere are exactly the Hilbert-basis directions
- `SphereDimensions.ell2_mem_hilbertBasis_iff`: The infinite-dimensional case
- `SphereDimensions.vF_mem_orthonormalBasis_iff`: The sphere is the line

#### `ToneHyperbola`: The tone law as hyperbolic geometry

- `ToneHyperbola.tone_law`: The tone law, assembled with `ToneCalc`

#### `VolumeShell`: At the limit all the volume is at the surface, and points carry no volume

- `VolumeShell.tendsto_inner_fraction`: At the limit all the volume is at the surface
- `VolumeShell.volume_countable_eq_zero`: Points carry no volume

#### `WallKernel`: The wall law under the involution `X ↦ 4/X`, and the `Γ_ℂ` kernel

- `ArchKerGammaC.archKer_three_quarter_eq`: The odd-character kernel
- `ArchKerGammaC.kerK_eq_gammaC`: FourierGap's split, read through the Γ-factors

#### `WanderBound`: Bounding the wander, rung 0

- `WanderBound.wander_rung0`: Rung 0 (Chebyshev level)

#### `WeilChiRoots`: The root locus of `Ξ_χ` and the `hS` blind spot

- `ChiRoots.grh'_iff_cross`: `GRH'` ⟺ every `τ` lies on the cross
- `ChiRoots.grh'_iff_roots_real`: `GRH'` ⟺ every zero `w` of `Ξ_χ(√w)` is real
- `ChiRoots.hS_iff_no_nonpos_root`: `hS` ⟺ no zero `w ≤ 0`
- `ChiRoots.grh_iff_roots_pos`: `GRH` ⟺ every zero `w` of `Ξ_χ(√w)` is real and positive

#### `ZeroCount`: Off-line zeros counted by the dimension of the ground space

- `WeilForm.card_offcross_le`: At most `m − 1` off-cross values of `ω²`
- `WeilForm.card_offcross_le_even`: Per support, with parity: at most `2⌊(m − 1)/2⌋` off-cross values of `ω²`
- `WeilForm.zeros_cross_of_dim_le_two`: `dim V ≤ 2` ⇒ zeros on the cross
- `WeilForm.xi_offcross_card_le`: Off-cross zeros of `Ξ`, counted by `z²`, number at most `2⌊(M − 1)/2⌋`
- `WeilForm.zeta_offline_card_le`: At most `2⌊(M − 1)/2⌋` zeros of `ζ` with `Re s > ½`
- `WeilForm.rh_of_dim_le_two`: RH from (a) for any ground states with eventually `dim V ≤ 2`

#### `ZetaJoins`: Joins on the `ζ` side

### `lib/pnt`

#### `Architect`

#### `SieveBuch8`: The decomposition to depth 8

- `SieveBuch.Par.I_S7`: Depth 7
- `SieveBuch.Par.I_S8`: Depth 8
- `SieveBuch.Par.I_S7c_vanish_lt`: Depth 7, `d > c`
- `SieveBuch.Par.I_S8c_vanish_lt`: Depth 8, `f > d`
- `SieveBuch.Par.I_S7c_vanish_reg`: Depth 7, outside the region
- `SieveBuch.Par.I_S8c_vanish_reg`: Depth 8, outside the region
- `SieveBuch.Par.I_S8_eq`: The cells of depth 8 below a cell of depth 7
- `SieveBuch.Par.lvl7`: Level 7
- `SieveBuch.Par.lvl7row`: The cells of depth 7 below a decomposed cell of depth 6
- `SieveBuch.Par.lvl6c`: A decomposed cell of depth 6
- `SieveBuch.Par.lvl6'`: Level 6
- `SieveBuch.Par.lvl5'`: Level 5
- `SieveBuch.Par.lvl4'`: Level 4
- `SieveBuch.Par.lvl3'`: Level 3
- `SieveBuch.Par.lvl2'`: Level 2
- `SieveBuch.Par.lvl1'`: Level 1
- `SieveBuch.Par.decomp8`: The decomposition's inequality to depth 8

### `lib/dh`

#### `ChiFirstFailure`: Continuity and the first positivity failure for every u-space form

- `PsiOmega.tendsto_archEQ_dil`: The `q`-energy is continuous under dilation
- `PsiOmega.farField_ge_log`: `∫_{u > 2a} K ≥ log 2 − log a − a`
- `PsiOmega.farQ_ge`: The far field of `K_q`
- `PsiOmega.archEQ_ge_far`: `E_q(g) ≥ ∫_{u > 2a} K_q`
- `PsiOmega.UData.lam_antitone`: `λ` is non-increasing in the support
- `PsiOmega.UData.lsc`: Lower semicontinuity along shrinking supports
- `PsiOmega.UData.lam_right`: Right-continuity of `λ`
- `PsiOmega.UData.tendsto_Q_dil`: `Q` is continuous under dilation
- `PsiOmega.UData.lam_left`: Left-continuity of `λ`
- `PsiOmega.UData.continuousOn_lam`: `λ` is continuous on `(0, ∞)`
- `PsiOmega.UData.Q_ge_small`: `Q(g) ≥ c − 2f(1) + log 2 − log a − a − 4`
- `PsiOmega.UData.lam_pos_small`: `λ ≥ log 2 − ¼` at small support
- `PsiOmega.UData.first_failure`: The first positivity failure for a u-space form
- `PsiOmega.continuousOn_lamC`: `λ_χ` is continuous on `(0, ∞)`
- `PsiOmega.lamC_pos_small`: `λ_χ ≥ log 2 − ¼` at small support
- `PsiOmega.first_failureC`: The first positivity failure for `L(s, χ)`
- `PsiOmega.first_failureDH`: The first positivity failure of `Q_dh`, unconditionally
- `PsiOmega.continuousOn_lamDH`: `λ_dh` is continuous on `(0, ∞)`

#### `ChiGround`: The ground-state stack for `L(s, χ)`

- `PsiOmega.UData.Q_ge`: `Q(g) ≥ −M(a)‖g‖²`
- `PsiOmega.UData.form`: `Q` is a `ProbeForm`
- `PsiOmega.UData.archE_le`: `E(g) ≤ e^{2a}E_q(g) + ‖g‖²·T(a)`
- `PsiOmega.UData.arch_of_archQU`: The archimedean condition of a probe from the `q`-integrand
- `PsiOmega.UData.exists_min`: A minimiser of `Q` exists at every support `a > 0`
- `PsiOmega.UData.exists_groundState`: A ground state exists at every support `a > 0`
- `PsiOmega.UData.euler_lagrange_mem`: Euler–Lagrange for any element of the ground space
- `PsiOmega.UData.split_mem`: Splitting a ground-space element
- `PsiOmega.UData.zero_swap_false`: The zero-swap lemma, core
- `PsiOmega.UData.zeros_real_or_imag`: Zeros of a simple ground state lie on `ℝ ∪ iℝ`
- `PsiOmega.UData.zeros_real_or_imag'`: Zeros of a simple ground state lie on `ℝ ∪ iℝ`
- `PsiOmega.UData.green_mem`: Swap closure
- `PsiOmega.UData.Gpole_annihilates`: `Q − λ` pairs `G v` with every pole-free probe to zero
- `PsiOmega.UData.G_mem_partner`: Rank-one step
- `PsiOmega.UData.finiteDimensional_groundL2`: The ground space is finite-dimensional
- `PsiOmega.UData.topGS_cross`: Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`
- `PsiOmega.exists_groundStateC`: A ground state of `QCu χ` exists at every support `a > 0`
- `PsiOmega.euler_lagrangeC_mem`: Euler–Lagrange for `QCu χ`
- `PsiOmega.theoremDC`: Theorem D for `QCu χ`
- `PsiOmega.topGSC_cross`: Every zero of `ĝ` for the top-of-chain ground state of `QCu χ` lies on `ℝ ∪ iℝ`
- `PsiOmega.grhCross_of_cross`: The Hurwitz step of `rh_of_prime_side_cross`
- `PsiOmega.grhCross_of_hypConvC_top`: GRH for `χ` off the real axis from `HypConvC χ` for the top-of-chain ground states
- `PsiOmega.grh_of_hypConvC_top`: GRH for `χ` from `HypConvC χ` for the top-of-chain ground states
- `PsiOmega.grh_of_eventually_simpleC`: GRH for `χ` from eventually simple ground states with `HypConvC χ`
- `PsiOmega.grh_chi3_of_hypConvC_top`: GRH for `χ₋₃` from `HypConvC` for its top-of-chain ground states
- `PsiOmega.grh_chi4_of_hypConvC_top`: GRH for `χ₋₄` from `HypConvC` for its top-of-chain ground states
- `PsiOmega.grh_chi8_of_hypConvC_top`: GRH for `χ₋₈` from `HypConvC` for its top-of-chain ground states
- `PsiOmega.grh_chi7_of_hypConvC_top`: GRH for `χ₋₇` from `HypConvC` for its top-of-chain ground states

#### `DHArch`: The archimedean term of the packet, bounded (certificate stage 2)

- `PsiOmega.integral_exp_sub_exp_div`: Frullani
- `PsiOmega.abs_integral_hK_cos_le`: The oscillatory integral of `h` is `O(1/c)`
- `PsiOmega.bq_frullani`: Frullani for exponentials
- `PsiOmega.integral_exp_mul_phi2_eq_eulerMascheroni`: The Euler–Mascheroni integral
- `PsiOmega.integral_hK_eq`: Binet at `3/4`
- `PsiOmega.psiReQ_three_quarters_sub`: The Gauss integral at shift `¾`, split
- `PsiOmega.psiReQ_three_quarters_le`: `Re ψ(¾ + iω/2) ≤ log √(9/16 + ω²/4) + 3/ω`
- `PsiOmega.psiReQ_three_quarters_sub_u`: The Gauss integral in the `u`-variable
- `PsiOmega.packet_archEQ_le`: The archimedean term of the packet
- `PsiOmega.packet_arch_total_le`: The archimedean total of the packet

#### `DHBohrSphere`: A zero pair off the sphere

- `PsiOmega.dh_zero_pair_off_sphere`: A zero pair of the Davenport–Heilbronn function off the unit sphere

#### `DHBridge`: Weil's form for the Davenport–Heilbronn function in u-space

- `PsiOmega.QDHu_hasSum`: The explicit formula for a probe, unscaled
- `PsiOmega.QDHu_nonneg_of_DHRH`: `DHRH ⟹ Q_dh ≥ 0`
- `PsiOmega.exists_offline_dh_of_neg_u`: A negative u-space Weil form certifies an off-line zero of `dh`
- `PsiOmega.ghat3_antitone_bound`: The raw width-3 strip bound
- `PsiOmega.striptest_antitone3`: `ĝ(3z)²` is a strip test function
- `PsiOmega.exists_offline_dh_of_neg_antitone`: The certificate for monotone probes
- `PsiOmega.exists_offline_dh_of_neg_box`: The certificate for the box

#### `DHCertificate`: The certificate — `Q_dh(packet 12/5 169/2) < 0`, hence an off-line zero of `dh` (stage 4)

- `PsiOmega.QDHu_packet_neg`: `Q_dh(packet 12/5 169/2) < 0`
- `PsiOmega.dh_offline_zero`: The Davenport–Heilbronn function has a zero off the critical line

#### `DHChannels`: The two channels of the Davenport–Heilbronn function

- `PsiOmega.conj_LFunction`: Conjugation symmetry
- `PsiOmega.LFunction_mul_one_sub`: The archimedean-free functional equation
- `PsiOmega.LFunction_ratio_mul`: The channel ratio
- `PsiOmega.phase_lock`: The phase lock
- `PsiOmega.dhL_eq_zero_iff_channel`: The zero condition
- `PsiOmega.chi5_channel_fe`: (1) for `χ₅`
- `PsiOmega.chi5_phase_lock`: (2) for `χ₅`, the phase lock
- `PsiOmega.dh_eq_zero_iff_channel`: (3) The zero condition of `dh`
- `PsiOmega.chi5_channel_ratio`: (4) The channel ratio of `χ₅`
- `PsiOmega.dh_line_zero_iff`: On the critical line the zero condition is one real equation

#### `DHCoeffs`: Generated: interval bounds for `u(d)`, `dinv(n)`, `c(n)`, `n ≤ 121` (certificate stage 3)

#### `DHColumn`: The dh column of the substitution matrix, part 1

- `PsiOmega.tau3_im_lt`: The zeros of `Ξ₃` lie in the open strip `|Im τ| < ½`
- `PsiOmega.dhRH_of_realRooted`: dh instance of `rh_of_prime_side`
- `PsiOmega.not_hypConvDH_of_realRooted`: The refutation
- `PsiOmega.dhRHcross_of_cross`: dh instance of `rh_of_prime_side_cross`
- `PsiOmega.dhRH_of_cross`: dh instance of `rh_of_prime_side_cross`
- `PsiOmega.not_hypConvDH_of_cross`: Refutation of the cross chain for dh
- `PsiOmega.dhRHcross_of_strip`: dh instance of `rh_of_strip_cross`
- `PsiOmega.not_realRooted_limit_XiDH`: The dh column of `rh_of_realRooted_limit`
- `PsiOmega.hypConvDH_of_D`: dh instance of `hypConv_of_D`
- `PsiOmega.dhRH_of_D_and_realRooted_proved`: dh instance of `rh_of_D_and_realRooted_proved`
- `PsiOmega.not_D_and_realRooted`: The refutation of the D route
- `PsiOmega.not_D_dh`: The dh column of `rh_of_D_and_realRooted_proved`
- `PsiOmega.not_dodging_dh`: The dh column of `rh_of_dodging_final`
- `PsiOmega.QDHu_nonneg_of_DHRHcross`: `DHRHcross ⟹ Q_dh ≥ 0`
- `PsiOmega.not_weil_positivity_dh`: Weil positivity fails for `dh`
- `PsiOmega.weil_criterion_dh`: The dh column of `weil_criterion_zeta`
- `PsiOmega.not_GRH_dh`: GRH fails for `dh`
- `PsiOmega.finrank_le_quadruples_dh`: The Davenport–Heilbronn instance

#### `DHColumnRest`: The dh column, part 4: the remaining G rows and the strip row of the P block

- `PsiOmega.not_ground_states_dh`: The dh column of `rh_of_ground_states`
- `PsiOmega.not_groundStates_dodging_dh`: The dh column of `rh_of_groundStates_dodging`
- `PsiOmega.not_D_and_realRooted_hadamard`: The dh column of `rh_of_D_and_realRooted`
- `PsiOmega.not_hypConvStripDH_top`: The dh column of `rh_of_hypConvStrip_top`
- `PsiOmega.not_XiDH_params`: The dh column of `rh_of_Xi_params`
- `PsiOmega.not_dodging_hadamard`: The dh column of `rh_of_dodging`
- `PsiOmega.not_pairing_and_realRooted`: The dh column of `rh_of_pairing_and_realRooted`

#### `DHConstants`: The constants of the archimedean bound at `(a, ω) = (12/5, 169/2)` (certificate stage 3)

#### `DHExplicit`: The explicit formula for the Davenport–Heilbronn function

- `PsiOmega.tau3_im`: The zeros of `Ξ₃` lie in `|Im τ| ≤ ½`
- `PsiOmega.logDeriv_XiDH_eq`: `Ξ_dh′/Ξ_dh` on `Re s > 2`
- `PsiOmega.logDeriv_XiDH3_eq`: `Ξ₃′/Ξ₃` on the line `Im t = −1`
- `PsiOmega.zero_side3`: The zero side
- `PsiOmega.conjFixed_cDH_chi5`: `c(n)` is real
- `PsiOmega.weil_XiDH3`: Weil's explicit formula for the Davenport–Heilbronn function
- `PsiOmega.QDH_hasSum`: The explicit formula for a probe
- `PsiOmega.QDH_nonneg_of_DHRH`: `DHRH ⟹ Q_dh ≥ 0`
- `PsiOmega.exists_offline_dh_of_neg`: A negative Weil form certifies an off-line zero of `dh`

#### `DHForm`: Weil's u-space form for `dh` is a `ProbeForm`; the DH ground energy

- `PsiOmega.QDHu_add_sub`: The parallelogram law for `QDHu`
- `PsiOmega.QDHu_ge_of_supp`: `Q_dh(g) ≥ −M_dh(a)‖g‖²`
- `PsiOmega.QDHu_ge`: `Q_dh(g) ≥ −M_dh(a)‖g‖²`
- `PsiOmega.QDHu_form`: `QDHu` is a `ProbeForm`
- `PsiOmega.lamDH_antitone`: `λ_dh` is non-increasing in the support
- `PsiOmega.lamDH_neg`: `λ_dh(b) < 0` for every `b ≥ 12/5`
- `PsiOmega.exists_lamDH_neg`: The `dh` column of `exists_lam_neg_of_not_RH`, unconditional

#### `DHGround`: The dh column, part 3: the ground-state stack of `QDHu`

- `PsiOmega.archIntegrand_le_dom`: The pointwise domination
- `PsiOmega.archE_le_DH`: `E(g) ≤ e^{2a}E_{3/4}(g) + ‖g‖²·T(a)`
- `PsiOmega.arch_of_archQ`: The archimedean condition of a probe from the `¾`-integrand
- `PsiOmega.exists_min_QDHu`: A minimiser of `QDHu` exists at every support `a > 0`
- `PsiOmega.exists_groundStateDH`: A ground state of `QDHu` exists at every support `a > 0`
- `PsiOmega.bilDH_polar`: `B_dh` is the polarisation of `QDHu`
- `PsiOmega.euler_lagrangeDH_mem`: Euler–Lagrange for any element of the ground space of `QDHu`
- `PsiOmega.euler_lagrangeDH`: Euler–Lagrange at a ground state
- `PsiOmega.split_mem_groundSpaceDH`: Splitting a ground-space element
- `PsiOmega.zero_swap_falseDH`: The zero-swap lemma for `QDHu`, core
- `PsiOmega.zeros_real_or_imagDH`: Zeros of a simple ground state of `QDHu` lie on `ℝ ∪ iℝ`
- `PsiOmega.zeros_real_or_imagDH'`: Zeros of a simple ground state of `QDHu` lie on `ℝ ∪ iℝ`
- `PsiOmega.dhRHcross_of_eventually_simple`: The chain for `dh` with eventual simplicity
- `PsiOmega.not_simple_hypConvDH`: The refutation
- `PsiOmega.green_mem_groundSpaceDH`: Swap closure
- `PsiOmega.Gpole_annihilatesDH`: `Q_dh − λ_dh` pairs `G v` with every pole-free probe to zero
- `PsiOmega.G_mem_partnerDH`: Rank-one step
- `PsiOmega.finiteDimensional_groundL2DH`: The ground space of `QDHu` is finite-dimensional
- `PsiOmega.theoremDDH`: Theorem D for `QDHu`
- `PsiOmega.topGSDH_cross`: Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`
- `PsiOmega.dhRHcross_of_hypConv_top`: The chain for `dh` with simplicity removed
- `PsiOmega.not_hypConvDH_top`: `HypConvDH` fails for the top-of-chain ground states of `QDHu`

#### `DHHadamard`: Davenport–Heilbronn in Lean, stage 2: the Hadamard product of `Ξ_{DH}`

- `PsiOmega.norm_XiC_le'`: The order of `Ξ_χ` for every primitive `χ ≠ 1`
- `PsiOmega.norm_XiDH_le`: The order of `Ξ_{DH}`
- `PsiOmega.XiDH_zero_ne`: `Ξ_{DH}(0) ≠ 0`
- `PsiOmega.hadamard_XiDH`: The Hadamard product of `Ξ_{DH}`
- `PsiOmega.hadamard_dh`: The Hadamard product of the Davenport–Heilbronn `Ξ`

#### `DHHurwitzEM`: The Euler–Maclaurin approximant of the Davenport–Heilbronn function `dh`

- `PsiOmega.dh_eq_hurwitz`: The bridge
- `PsiOmega.norm_dh_sub_EM_le`: The Euler–Maclaurin bound for `dh`
- `PsiOmega.norm_dh_sub_EM_le_box`: Box version

#### `DHInert`: Coefficient localisation of the Davenport–Heilbronn prime side

- `PsiOmega.smoothInd_conv_eq_one`: Unique factorisation into a `P`-part and a `Q`-part
- `PsiOmega.chi5_inv_eq_of_split`: `χ₅` is real on split-smooth integers
- `PsiOmega.splitSeq_conv_chi5Seq`: `χ₅ = s ⍟ t`
- `PsiOmega.splitSeq_conv_chi5InvSeq`: `χ₅⁻¹ = s ⍟ t̄`
- `PsiOmega.logDer_mul`: `log` is a derivation of Dirichlet convolution
- `PsiOmega.dhA_eq_splitA_mul_inertA`: `δ + u = s ⍟ b`
- `PsiOmega.logDer_dhA_mul_dhInvA`: The logarithmic derivative splits
- `PsiOmega.cDH_chi5_decomp`: The split/inert decomposition of the prime side
- `PsiOmega.cDH_chi5_eq_of_dvd`: Coefficient localisation

#### `DHJoins`: Joins in the Davenport–Heilbronn layer

- `PsiOmega.dhRH_iff_cross`: `DHRH ↔ DHRHcross`
- `PsiOmega.dh_conj`: `dh(s̄) = conj dh(s)`
- `PsiOmega.QDHu_add_even_odd`: The parity split of `Q_dh`
- `PsiOmega.QDHu_packet_plane_neg`: A negative-definite plane of `Q_dh` from the two packet certificates
- `PsiOmega.QCu_form`: `QCu χ` is a `ProbeForm`
- `PsiOmega.lamC_antitone`: `λ_χ` is non-increasing in the support
- `PsiOmega.probe_nonneg_iff_lamC_nonneg`: `Q_χ ≥ 0` on every probe at every support iff `λ_χ ≥ 0` at every support
- `PsiOmega.lamC_nonneg_of_GRH`: Under GRH(χ), `λ_χ ≥ 0` at every support
- `PsiOmega.grh_iff_lamC_nonneg`: GRH(χ) iff `λ_χ ≥ 0` at every support
- `PsiOmega.grh_iff_lamC_eventually_nonneg`: GRH(χ) iff `λ_χ ≥ 0` at all large supports
- `PsiOmega.exists_lamC_neg_of_not_GRH`: If GRH(χ) fails, `λ_χ` is negative from some support on
- `PsiOmega.grh_iff_lamC_nonneg_chi3`: GRH for `χ₋₃` iff `λ_{χ₋₃} ≥ 0` at every support
- `PsiOmega.grh_iff_lamC_nonneg_chi4`: GRH for `χ₋₄` iff `λ_{χ₋₄} ≥ 0` at every support
- `PsiOmega.grh_iff_lamC_nonneg_chi8`: GRH for `χ₋₈` iff `λ_{χ₋₈} ≥ 0` at every support
- `PsiOmega.grh_iff_lamC_nonneg_chi7`: GRH for `χ₋₇` iff `λ_{χ₋₇} ≥ 0` at every support
- `DHNegIndex.negIndex_ge_five`: The Weil index of `Q_dh` on probes of either parity is at least `5`

#### `DHLocate2Base`: A zero of `dh` within `1 / 200` of `c = 65083 / 100000 + (11416334 / 100000) i`: the certificate instance (generated)

- `PsiOmega.Locate.Z2.norm_dh_sub_dhEM_le_ball`: The Euler–Maclaurin error on the ball
- `PsiOmega.Locate.Z2.D2sum_le`: `D2sum(64583 / 100000, 28) ≤ 8109 / 100`
- `PsiOmega.Locate.Z2.m2_ball`: The second-derivative bound on the ball
- `PsiOmega.Locate.Z2.dh_zero_near_of_center`: The certificate at `cZ`, ball-uniform inputs discharged
- `PsiOmega.Locate.Z2.dh_zero_near_of_center'`: The open inputs with fixed tolerances

#### `DHLocate2Exp`: Generated (`gen_locate_zero.py 2`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 65083 / 100000`, `n ∈ NS`

#### `DHLocate2Num`: Generated (`gen_locate_zero.py 2`): the interval evaluation of `PReG cZ 28 12`, `PImG cZ 28 12`, `AReG cZ 28 12`

- `PsiOmega.Locate.Z2.PReG_mem`: The enclosure of `Re fEM(c)`
- `PsiOmega.Locate.Z2.PImG_mem`: The enclosure of `Im fEM(c)`
- `PsiOmega.Locate.Z2.AReG_mem`: The enclosure of `Re fEM′(c)`
- `PsiOmega.Locate.Z2.dh_zero_located`: The located zero
- `PsiOmega.Locate.dh_zero_located_2`: Zero 2
- `PsiOmega.Locate.dh_zero_located_box_2`: Zero 2

#### `DHLocate2Trig`: Generated (`gen_locate_zero.py 2`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 11416334 / 100000`, `n ∈ NS`

#### `DHLocate3Base`: A zero of `dh` within `1 / 500` of `c = 57436 / 100000 + (16647931 / 100000) i`: the certificate instance (generated)

- `PsiOmega.Locate.Z3.norm_dh_sub_dhEM_le_ball`: The Euler–Maclaurin error on the ball
- `PsiOmega.Locate.Z3.D2sum_le`: `D2sum(14309 / 25000, 41) ≤ 1567 / 10`
- `PsiOmega.Locate.Z3.m2_ball`: The second-derivative bound on the ball
- `PsiOmega.Locate.Z3.dh_zero_near_of_center`: The certificate at `cZ`, ball-uniform inputs discharged
- `PsiOmega.Locate.Z3.dh_zero_near_of_center'`: The open inputs with fixed tolerances

#### `DHLocate3Exp`: Generated (`gen_locate_zero.py 3`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 57436 / 100000`, `n ∈ NS`

#### `DHLocate3Num`: Generated (`gen_locate_zero.py 3`): the interval evaluation of `PReG cZ 41 12`, `PImG cZ 41 12`, `AReG cZ 41 12`

- `PsiOmega.Locate.Z3.PReG_mem`: The enclosure of `Re fEM(c)`
- `PsiOmega.Locate.Z3.PImG_mem`: The enclosure of `Im fEM(c)`
- `PsiOmega.Locate.Z3.AReG_mem`: The enclosure of `Re fEM′(c)`
- `PsiOmega.Locate.Z3.dh_zero_located`: The located zero
- `PsiOmega.Locate.dh_zero_located_3`: Zero 3
- `PsiOmega.Locate.dh_zero_located_box_3`: Zero 3

#### `DHLocate3Trig`: Generated (`gen_locate_zero.py 3`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 16647931 / 100000`, `n ∈ NS` (part 1 of 2: `2 ≤ n ≤ 104`)

#### `DHLocate3Trig2`: Generated (`gen_locate_zero.py 3`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 16647931 / 100000`, `n ∈ NS` (part 2 of 2: `106 ≤ n ≤ 209`)

#### `DHLocate4Base`: A zero of `dh` within `1 / 150` of `c = 72426 / 100000 + (17670246 / 100000) i`: the certificate instance (generated)

- `PsiOmega.Locate.Z4.norm_dh_sub_dhEM_le_ball`: The Euler–Maclaurin error on the ball
- `PsiOmega.Locate.Z4.D2sum_le`: `D2sum(107639 / 150000, 41) ≤ 8377 / 100`
- `PsiOmega.Locate.Z4.m2_ball`: The second-derivative bound on the ball
- `PsiOmega.Locate.Z4.dh_zero_near_of_center`: The certificate at `cZ`, ball-uniform inputs discharged
- `PsiOmega.Locate.Z4.dh_zero_near_of_center'`: The open inputs with fixed tolerances

#### `DHLocate4Exp`: Generated (`gen_locate_zero.py 4`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = 72426 / 100000`, `n ∈ NS`

#### `DHLocate4Num`: Generated (`gen_locate_zero.py 4`): the interval evaluation of `PReG cZ 41 12`, `PImG cZ 41 12`, `AReG cZ 41 12`

- `PsiOmega.Locate.Z4.PReG_mem`: The enclosure of `Re fEM(c)`
- `PsiOmega.Locate.Z4.PImG_mem`: The enclosure of `Im fEM(c)`
- `PsiOmega.Locate.Z4.AReG_mem`: The enclosure of `Re fEM′(c)`
- `PsiOmega.Locate.Z4.dh_zero_located`: The located zero
- `PsiOmega.Locate.dh_zero_located_4`: Zero 4
- `PsiOmega.Locate.dh_zero_located_box_4`: Zero 4

#### `DHLocate4Trig`: Generated (`gen_locate_zero.py 4`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 17670246 / 100000`, `n ∈ NS` (part 1 of 2: `2 ≤ n ≤ 104`)

#### `DHLocate4Trig2`: Generated (`gen_locate_zero.py 4`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = 17670246 / 100000`, `n ∈ NS` (part 2 of 2: `106 ≤ n ≤ 209`)

#### `DHLocateExp`: Generated (gen_locate.py): two-sided bounds for `ex (1617/2000) n = exp(-(1617/2000) log n)`, `n ∈ NS`

#### `DHLocateFour`: Four located off-line zeros of `dh`, and the Weil index of `Q_dh` is at least `4`

- `PsiOmega.Locate.negIndex_ge_four_of`: Four located off-line zeros give a `4`-dimensional negative space of `Q_dh`
- `PsiOmega.Locate.dh_zeros_located_four`: Four located zeros of `dh` off the critical line
- `PsiOmega.Locate.dh_zeros_located_four_box`: The four located zeros in coordinates
- `DHNegIndex.negIndex_ge_four`: The Weil index of `Q_dh` is at least `4`

#### `DHLocateGen`: The zero-location certificate for a general centre

- `PsiOmega.Locate.dh_zero_near_of_fEMG`: The certificate for a general centre
- `PsiOmega.Locate.norm_dh_sub_dhEM_le_ballG`: The Euler–Maclaurin error on `closedBall c r`
- `PsiOmega.Locate.norm_deriv2_GEM_ballG`: Cauchy for `G″` at a point of `closedBall c r`
- `PsiOmega.Locate.norm_deriv2_fEM_ballG`: The second-derivative bound on a ball
- `PsiOmega.Locate.dh_zero_near_of_elementaryG`: The ladder in elementary form

#### `DHLocateNum`: Generated (gen_locate.py): the interval evaluation of `PRe 20 12`, `PIm 20 12`, `ARe 20 12`

- `PsiOmega.Locate.PRe_20_mem`: The enclosure of `Re fEM(c)`
- `PsiOmega.Locate.PIm_20_mem`: The enclosure of `Im fEM(c)`
- `PsiOmega.Locate.ARe_20_mem`: The enclosure of `Re fEM′(c)`
- `PsiOmega.Locate.dh_zero_located`: A kernel-checked zero of the Davenport–Heilbronn function off the critical line

#### `DHLocateSkeleton`: A zero of `dh` within `1/100` of `c = 1617/2000 + (856993/10000) i`: the certificate skeleton

- `PsiOmega.Locate.exists_zero_of_approx`: Localisation in approximant form
- `PsiOmega.Locate.norm_sub_linear_le_ball`: The linearisation bound on a ball
- `PsiOmega.Locate.exists_zero_of_bounds`: The skeleton, abstract form
- `PsiOmega.Locate.dhEM_eq`: The approximant, normalised
- `PsiOmega.Locate.norm_deriv2_GEM_le`: Cauchy's estimate for `GEM″`
- `PsiOmega.Locate.prod_box_eq`: The Pochhammer box constant, exactly
- `PsiOmega.Locate.norm_dh_sub_dhEM_le_ball`: The Euler–Maclaurin error on the ball
- `PsiOmega.Locate.Gsup_ball_le`: The sup of `GEM 20 12` on `closedBall cLoc (41/100)`
- `PsiOmega.Locate.norm_deriv2_GEM_ball`: Cauchy for `G″` on the ball
- `PsiOmega.Locate.norm_deriv2_dhEM_ball`: The second-derivative bound on the ball
- `PsiOmega.Locate.dh_zero_near_of_numerics`: Stage 2, abstract form
- `PsiOmega.Locate.dh_zero_near_of_fEM`: Stage 2, normalised form
- `PsiOmega.Locate.QEM_twelve`: `Q_x` for `K = 12` with the Bernoulli coefficients `B_{2k+2}/(2k+2)!` as rationals
- `PsiOmega.Locate.EMmain_explicit`: `EMmain_explicit`
- `PsiOmega.Locate.norm_dh_sub_dhEM_le_ball'`: The Euler–Maclaurin error on the ball, in `dh` units
- `PsiOmega.Locate.dh_zero_near_of_elementary`: Stage 2, elementary form
- `PsiOmega.Locate.D2sum_le`: `D2sum(1597/2000, 20) ≤ 36`
- `PsiOmega.Locate.dh_zero_near_of_center`: Stage 2 with every ball-uniform input discharged
- `PsiOmega.Locate.dh_zero_near_of_center'`: The certificate's open inputs, packaged with fixed tolerances
- `PsiOmega.Locate.dh_zero_near_of_dhEM`: Stage 2 in `dh` units

#### `DHLocateTrig`: Generated (gen_locate.py): bounds for `cC n = cos(t log n)`, `sC n = sin(t log n)`, `t = 856993/10000`, `n ∈ NS`

#### `DHLogBounds`: Generated: rational bounds for `Real.log n`, `2 ≤ n ≤ 121` (certificate stage 3)

#### `DHLogBoundsExt`: Generated (gen_logext.py): rational bounds for `Real.log n`, `122 ≤ n ≤ 209`

#### `DHNegIndex`: Every off-line quadruple of `dh` gives a negative direction of `Q_dh`

- `DHNegIndex.striptest_twinComb3`: Twin combinations pass the width-3 strip test
- `DHNegIndex.negDirections_offline_dh`: Every off-line quadruple of `dh` gives a negative direction of `Q_dh`
- `DHNegIndex.negIndex_ge_of_located`: `n` located off-line zeros of `dh` give an `n`-dimensional negative space of `Q_dh`

#### `DHNumerics`: The verified-numerics toolkit for the certificate

- `PsiOmega.Num.mul_bounds`: Interval product

#### `DHOddPacket`: The sine packet: Weil's form of `dh` is negative on an odd probe

- `PsiOmega.sinPacket_oprobe`: The sine packet is an odd probe
- `PsiOmega.sinPacket_striptest`: `ĝ(3z)²` is a strip test function
- `PsiOmega.QDHu_sinPacket_eq`: Weil's form of `dh` on the sine packet, in closed form
- `PsiOmega.oprobe_archIntegrandQ_integrable`: Integrability for `q ≥ ¼`
- `PsiOmega.sinPacket_archEQ_le`: The archimedean term of the sine packet
- `PsiOmega.sinPacket_arch_total_le`: The archimedean total of the sine packet
- `PsiOmega.QDHu_sinPacket_le`: `Q_dh(sinPacket 12/5 169/2) ≤ −111/100`
- `PsiOmega.QDHu_sinPacket_neg`: `Q_dh(sinPacket 12/5 169/2) < 0`
- `PsiOmega.exists_oprobe_QDHu_neg`: A negative normalised odd probe at every support `b ≥ 12/5`
- `PsiOmega.not_odd_lower_dh`: The `dh` column of `rh_of_lamO_lower`'s hypothesis, refuted
- `PsiOmega.QDHu_ge_odd`: `Q_dh(o) ≥ −M_dh(a)‖o‖²`
- `PsiOmega.lamODH_neg`: `λ_dh^odd(b) < 0` for every `b ≥ 12/5`
- `PsiOmega.not_lamODH_lower`: `rh_of_lamO_lower`'s hypothesis with `λ_dh^odd` in place of `λ_odd`, refuted

#### `DHOddTerms`: Generated (gen_oddterms.py): lower bounds for the prime terms of the sine packet and their partial sums

#### `DHOffCross`: The certificate's zero is off the cross

- `PsiOmega.dh_offline_nonreal_zero`: The certificate's zero is non-real
- `PsiOmega.dh_offline_zero_right`: The free strengthening

#### `DHPacket`: The box wave packet: Weil's form of `dh` on `cos(ωu)·1_{[−a,a]}` in closed form

- `PsiOmega.packet_striptest`: `ĝ(3z)²` is a strip test function
- `PsiOmega.QDHu_packet_eq`: Weil's form of `dh` on the packet, in closed form
- `PsiOmega.packet_QDHu_hasSum`: The explicit formula on the packet
- `PsiOmega.exists_offline_dh_of_neg_packet`: A negative Weil form on a packet certifies an off-line zero of `dh`

#### `DHPrime`: The prime side of the Davenport–Heilbronn function

- `PsiOmega.dhL_eq_LSeries`: `DH_χ(s) = Σ a(n) n^{−s}` on `Re s > 1`
- `PsiOmega.LSeries_aDH_eq`: `Σ a(n) n^{−s} = a(1) · Σ (δ + u)(n) n^{−s}`
- `PsiOmega.aDH_one_eq`: `a(1) = (1 + ε_χ)(1 + ε_{χ⁻¹})`
- `PsiOmega.logDeriv_dhL_eq`: The logarithmic derivative of `DH_χ` is a Dirichlet series
- `PsiOmega.logDeriv_dh_eq`: The prime side of the Davenport–Heilbronn function

#### `DHRealAxis`: `dh` has no zero on the positive real axis

- `PsiOmega.aDH_chi5_eq_mul`: `a(n) = a(1)·u(n mod 5)`
- `PsiOmega.sum_range_aDH_chi5`: The partial sums of `a`
- `PsiOmega.Bval_values`: `B = 0, 0, 1, 1 + κ, 1`
- `PsiOmega.Bval_mod_five`: `B(m mod 5) ∈ {0, 1, 1 + κ}`
- `PsiOmega.BDH_eq_one`: `B = 1` on `[1, 2)`
- `PsiOmega.dh_eq_integral`: `dh(s) = s∫_1^∞ A(x)x^{−s−1}dx` on `Re s > 0`
- `PsiOmega.dh_eq_integral_real`: `dh(σ) = a(1)·σ∫_1^∞ B(x)x^{−σ−1}dx`
- `PsiOmega.integral_BDH_ge`: `σ∫_1^∞ B(x)x^{−σ−1}dx ≥ 1 − 2^{−σ}`
- `PsiOmega.dh_div_a1_real`: `dh(σ)/a(1)` is real
- `PsiOmega.dh_div_a1_real_ge`: `dh(σ)/a(1) ≥ 1 − 2^{−σ}`
- `PsiOmega.dh_ne_zero_of_real`: `dh(σ) ≠ 0` for `σ > 0`
- `PsiOmega.dhLam_real_ne_zero`: `Λ_{dh}(σ) ≠ 0` for every real `σ`
- `PsiOmega.XiDH_I_mul_ne_zero`: `Ξ_{dh}` has no zero on the imaginary axis
- `PsiOmega.dh_offcross_zero`: An off-line zero of `dh` off the real axis

#### `DHTerms`: Generated: lower bounds for the prime terms and their partial sums (certificate stage 3)

#### `DHTrigBounds`: Generated: rational bounds for `cos(ω log n)`, `sin(ω log n)`, `ω = 169/2`, `2 ≤ n ≤ 121`,

#### `DHTwin`: The dh column of the substitution matrix, part 2: the twin form

- `PsiOmega.twinData_dh`: The data of the twin-form Landau argument for `dh`
- `PsiOmega.dhRH_of_twins`: The dh column of `line_of_weil_twins`/`rh_of_weil_twins`
- `PsiOmega.not_twins_nonneg_dh`: The twin form of `dh` is negative somewhere
- `PsiOmega.dh_twins_rate`: The dh column of `weil_twins_rate`
- `PsiOmega.not_twins_subexp_dh`: The twin form of `dh` has a negative part of exponential rate
- `PsiOmega.twinData_dhu`: The u-space twin data for `dh`
- `PsiOmega.zeros_of_lamDH_ge`: A lower bound on `λ_dh` of exponential rate `σ` is a zero-free region
- `PsiOmega.lamDH_rate`: A zero with `|2 Re s − 1| > σ` makes `λ_dh(a) < −C·e^{σa}` at arbitrarily large `a`
- `PsiOmega.lamDH_fails_exponentially`: `λ_dh` fails exponentially, unconditionally
- `PsiOmega.not_lamDH_subexp`: `λ_dh` has a negative part of exponential rate

#### `DHZeros`: `L(½, χ₅) ≠ 0` and the zero side for `Ξ_{DH}`

- `PsiOmega.re_sum_range_cC_chi5`: The partial sums of `χ₅` have real part `0, 0, 1, 1, 1`
- `PsiOmega.re_LFunction_chi5_half_ge`: `Re L(½, χ₅) ≥ ½`
- `PsiOmega.LFunction_chi5_half_ne_zero`: `L(½, χ₅) ≠ 0`
- `PsiOmega.hadamard_dh'`: The Hadamard product of the Davenport–Heilbronn `Ξ`, unconditional
- `PsiOmega.hasSum_logDeriv_XiDH`: The logarithmic derivative of Hadamard's product
- `PsiOmega.hasSum_logDeriv_dh`: The zero side for the Davenport–Heilbronn `Ξ`

#### `DavenportHeilbronn`: Davenport–Heilbronn in Lean, stage 1

- `PsiOmega.rootNumber_mul_rootNumber_inv`: The root numbers of `χ` and `χ⁻¹` are inverse
- `PsiOmega.dhLam_one_sub`: The functional equation `Λ_{DH}(1 − s) = Λ_{DH}(s)`
- `PsiOmega.dhLam_eq`: `Λ_{DH} = N^{s/2} Γ_ℝ(s + 1) · DH`
- `PsiOmega.dhL_ne_zero`: `DH` is not identically zero
- `PsiOmega.dh_ne_zero`: `dh` is not identically zero
- `PsiOmega.dh_functional_equation`: The functional equation
- `PsiOmega.dh_zero_symm`: Zeros of `dh` in the strip are symmetric under `s ↦ 1 − s`

### `lib/zeta23`

#### `BohrLandau`: Bohr and Landau's theorem in the library's zero family

- `BohrLandau.tendsto_NX_div_pos`: For every `w > 0`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `BohrLandau.tendsto_outside_div_pos`: The same in sphere form

#### `CoImportGamma`: The pnt layer and zeta23's Gamma facts co-import

#### `CoImportMV`: The pnt layer and zeta23's mean-value module co-import

#### `CountCompare`: The two local zero counts compared

- `CountCompare.local_count_le`: zeta23's local count from the library's zero weight, with the library's explicit constant

#### `Dictionary`: The zeta23 ↔ library dictionary

#### `HybridCertificate`: The same-space hybrid certificate on zeta23's zero side, with the off-line term displayed

- `HybridCert.cert_general`: The rank–trace certificate in units c
- `HybridCert.cert_offline`: The certificate with the off-line pairs written out
- `HybridCert.hybrid_cert`: The same-space hybrid certificate
- `HybridCert.hybrid_cert_pairs`: The certificate on pair representatives
- `HybridCert.hybrid_cert_of_offline`: The certificate with the off-line input displayed
- `HybridCert.hybrid_cert_of_moments`: The off-line input split by order in η
- `HybridCert.hybrid_cert_of_no_offline`: No off-line zeros
- `HybridCert.hybrid_cert_eta_zero`: Consistency (η = 0)

#### `HybridExamples`: Concrete instances of the hybrid certificate

#### `ShellDensity`: For every `w > ¼`, almost every zero lies within `w` of the critical line, in Bohr-shell form

- `ShellDensity.emBound_zeta23`: The Euler–Maclaurin bound at a zero
- `ShellDensity.density_zeta23`: Zero density
- `ShellDensity.Ncount_le_NX`: zeta23's zeros with `T < γ ≤ 2T` inject into the library's pairs up to height `2T`
- `ShellDensity.NX_zero_ge`: Riemann–von Mangoldt in the library's family
- `ShellDensity.tendsto_NX_div_quarter`: For every `w > ¼`, the proportion of pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `ShellDensity.tendsto_outside_div_quarter`: The same in sphere form
- `ShellDensity.ncard_outside_le_unconditional`: The count

#### `ShellSixth`: For every w > 1/6, almost every zero lies within w of the critical line

- `ShellSixth.emApprox_zeta23`: The Euler–Maclaurin approximation of `ζ` by its partial sums
- `ShellSixth.tendsto_NX_div_sixth`: For every `w > 1/6`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `ShellSixth.tendsto_outside_div_sixth`: The same in sphere form

#### `SlogZeta`

- `SlogZeta.Slog_eventually`: `S(T) = O(log T)`, eventually
- `SlogZeta.Slog_zeta`: `S(t) = O(log t)` on `t ≥ 14`
- `SlogZeta.wall_law_zeta_S`: 1ca(i)–(iii) for ζ, with von Mangoldt's bound proved

#### `ZeroWindow`: Bounded gaps between the ordinates of the zeros of `ζ`

- `ZeroWindow.zero_in_window`: Bounded gaps between the zeros of `ζ`
