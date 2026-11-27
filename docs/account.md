# An account of the library

The library on one page: what it proves, what that rests on, how much of number theory it covers, and where the next
results are. Every result here names the Lean theorem that proves it; a check file prints its axioms, or those of a
theorem that uses it. [`inventory.md`](inventory.md) lists all 2588 printed theorems, marking *opt-in* the 14 that
rest on the Linnik paper's certificates, whose build is opt-in (`lib/check/CheckLinnik.lean`), and
[`formalisations/`](../formalisations/README.md) gives the sources. `scripts/check_account.py`, which CI runs, checks
that every Lean name and path on this page exists.

## How much of number theory

A deep vertical slice, not a survey: the zeros of `ζ` and of Dirichlet `L`-functions, and what they say about primes.
In that slice the library reaches current research (Guth and Maynard's large values estimate, Chen, Gupta and Li's
density estimate, OpenAI's zero-free half-plane, Alpöge and Furman's two thirds of the zeros on the critical line) and
proves Linnik exponents of its own: `21/10` and `43/20` with no hypothesis, on certificates whose build is opt-in, and
`2 + η` under GRH, which L. Alpöge's Lean archive proves (an input, below). Outside it the library has what its proofs
needed and nothing more. By the
sections of MSC 2020's Number theory (11):

| Section | Here |
|---|---|
| 11M `ζ` and `L`-functions | In depth: zero-free regions, zero counting, zero density, the zeros on the critical line, moments, approximate functional equations, explicit formulae, criteria for RH |
| 11N Multiplicative number theory | In depth: the prime number theorem and its error terms, primes in progressions, Linnik's theorem, primes in short intervals, Mertens' function, divisor problems, squarefree numbers, sieves |
| 11L Exponential and character sums | What the routes need: mean and large values of Dirichlet polynomials, the Halász–Montgomery inequality, the quadratic large sieve over `ℤ[ω]`, Vinogradov's mean value theorem in a weak form |
| 11F Automorphic forms | One object: Kubota's cubic theta function on hyperbolic 3-space, with Patterson's coefficients |
| 11A, 11R, 11T Elementary, global fields, finite fields | Over `ℤ[ω]`: quadratic, cubic and sextic reciprocity, Gauss and Jacobi sums, Jacobi's congruence `C(2k, k) ≡ −L (mod p)` for `p = 3k + 1 = (L² + 27M²)/4`, `L ≡ 1 (mod 3)` (`CubicBinomial.choose_modEq`), the ideals of each norm. Quadratic fields: the splitting law, `ζ_K = ζ·L(s, χ_K)`, class numbers. The least quadratic non-residue |
| 11Y Computational number theory | Certificates that the kernel checks: the Linnik sieve's two searches (108 926 parts in 1167 files, about 62 hours of one core, opt-in to build), five zeros of the Davenport–Heilbronn function (the fifth, at height `24415`, from `24 000` terms that the kernel evaluates in ball arithmetic), explicit constants, the search of the class number one problem (`3 200 000` cases) |
| 11G Arithmetic algebraic geometry | Hasse's bound for every elliptic curve over a finite field of odd characteristic, by Manin's proof, and the Riemann hypothesis for it in every degree from the lattice of Manin's twist; for `y² = x³ + D`, the Frobenius as an Eisenstein integer of norm `q`; Gauss's count `p − 2 + L` of `x³ + y³ = 1` modulo `p` and the `p + 1 + L` points of the Fermat cubic, within `2√p` of `p + 1` (`FermatCubicCount.card_eq`, `FermatCubicCount.abs_sub_le`) |
| 11E Forms | Jacobi's four-square theorem `r₄(n) = 8Σ_{d ∣ n, 4 ∤ d} d` (`JacobiFourSquares.r4_eq`), by Hirschhorn's proof from the triple product identity (`JacobiFourSquares.jtp`), and what it gives: `r₄` prime by prime (`FourSquareTeeth.r4_pow_mul`), the alternating lattice sum of `ℤ⁴` (`FourSquareTeeth.lseries_alt`), `ζ(2) = π²/6` from the points of `ℤ⁴` in balls (`FourSquareResidue.riemannZeta_two_of_lattice`), Siegel's formula `r₄(n) = π²n∏_p δ_p(n)` (`SiegelFour.siegel`), Jacobi's eight-square theorem (`JacobiEightSquares.r8_eq`) with `ζ(4) = π⁴/90` from the points of `ℤ⁸` in balls (`EightSquareResidue.riemannZeta_four_of_lattice`), the two-variable zeta function of Lagarias and Rains at `w = 4` (`TwoVariableZeta.Z_four`), and the lattices `x² + xy + y²` (hexagonal), `x² + 2y²` and `x² + xy + 2y²`, whose Epstein zeta functions are those of `ℚ(√−3)`, `ℚ(√−2)` and `ℚ(√−7)` and whose RH is `RH ∧ GRH(χ_d)` for `d = −3, −8, −7` (`EpsteinHexagonal.rh_hex_iff`, `EpsteinTwo.rh_iff`, `EpsteinSeven.rh_iff`); the flat rectangular lattices, whose Epstein zeta functions have a real zero in `(½, 1)` once `y > e²`, `x² + 58y²` among them (`EpsteinFlat.not_rh`, `EpsteinFlat.not_rh_fiftyEight`); and Weng's rank-2 zeta function of `ℚ`, which satisfies RH with no hypothesis (`WengRankTwo.rh_weng`); and congruences: the theta series of `x² + xy + y²`, `x² + xy + 2y²` and `x² + y²` agree with Eisenstein series modulo `3`, `7` and `4` (`SquaresCongruences.hex_modEq`, `SquaresCongruences.seven_modEq`, `SquaresCongruences.two_modEq`), and `r₈(n) ≡ 2r₄(n) (mod 64)` (`SquaresCongruences.r8_modEq`) |
| 11P Additive number theory; partitions | Ramanujan's congruences `p(5n + 4) ≡ 0 (mod 5)` and `p(7n + 5) ≡ 0 (mod 7)`, and their analogues for coloured partitions, `p₋₃(3n + 2) ≡ 0 (mod 9)` among them, from Jacobi's cube identity and Mathlib's pentagonal number theorem (`RamanujanCongruences.ramanujan_five`, `RamanujanCongruences.ramanujan_seven`, `RamanujanCongruences.coloured_three_nine`), and they are the first members of four infinite families, uniform in the prime `ℓ`, from `η`, `η³`, `η⁴` and `η⁶` (`RamanujanFamilies.family_one`, `RamanujanFamilies.family_three`, `RamanujanFamilies.family_four`, `RamanujanFamilies.family_six`). No additive problems beyond the sums of four and eight squares of 11E |
| 11B, 11C, 11D, 11H, 11J, 11K, 11S, 11U, 11Z | Nothing beyond Mathlib: no Diophantine equations, elliptic curves over global fields, modular forms in general, Diophantine approximation or local fields |

Two of the twenty sections in depth, seven in part, eleven not at all. Mathlib supplies the floor: `ζ` and Dirichlet
`L`-functions with their functional equations and their non-vanishing on `Re s = 1`, Dirichlet's theorem, and number
fields with their class groups and the class number formula.

## What it rests on

- **The kernel, Mathlib and the toolchain**: Lean `v4.35.0-rc3` and Mathlib `0f64d30a`. CI fails unless every printed
  theorem depends on `propext`, `Classical.choice` and `Quot.sound` only (`scripts/check_axioms.py`), the sources hold
  no `sorry`, `native_decide` or declared axiom (`scripts/check_hygiene.py`), every declaration is used by a
  printed theorem (`scripts/dead_code.py`), and the build emits no warning in the library's own sources
  (`scripts/check_warnings.py`). For the Linnik paper's two theorems, whose certificates are opt-in, the workflow
  `.github/workflows/linnik.yml` does the same every week, not CI on every change.
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
- **GRH, from L. Alpöge's Lean archive** (20 November 2026), an input that no referee has read either, proved but not
  here: the archive proves RH and GRH for every Dirichlet `L`-function on its own pins (Lean 4.33.1, Mathlib
  `0df444a`), and [`tools/rh/`](../tools/rh/README.md) builds it there, where the kernel accepts every constant and
  the two theorems rest on `propext`, `Classical.choice` and `Quot.sound` alone. The library does not import it and
  declares no axioms, so in its Lean GRH stays a hypothesis: the headline Linnik exponent, `2 + η`, is
  `LinnikGRH.linnik_two`, under GRH in the archive's words (`LinnikGRH.DirichletRH`). The library is rebuilding the
  archive's proof on its own stack ([`rh-rebuild.md`](rh-rebuild.md)); the rebuild's frontier `ZetaBalance.PairBound`
  gives that hypothesis, conditionally on the half-plane (`ZetaBalance.rhAndGRH_of_pairBound`,
  `LinnikGRH.dirichletRH_of_rhAndGRH`). The rebuild's top, RH with GRH (`HalfPlaneGRH.RHandGRH`), is the one
  hypothesis of what the library's deductions from a zero-free half-plane give at `1/2`, marked "under RH" or "under
  GRH" below (`HalfPlaneGRH.RHandGRH.corollaries`).
- **An input whose journal review is pending**: Alpöge and Furman's theorem that two thirds of the zeros of `ζ` lie on
  the critical line (arXiv:2608.13637), which `zeta23` proves with no hypothesis (`CriticalLine.two_thirds`). zeta23's
  [metadata](https://github.com/anthropics/formal-math/blob/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23/formalization.yaml)
  records that an analytic number theorist reviewed the paper and wrote an independent condensed proof of its main
  result, and that Furman checked zeta23's statements against the paper.

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
| Hardy: infinitely many zeros of `ζ` lie on the critical line. Selberg: for large `T`, at least `T log T/(12π)` of them have `T < Im ρ ≤ 2T`, a positive proportion, and at least `T log T/(16π)` simple ones | `CriticalLine.infinite_zeros`, `CriticalLine.ncard_zeros_ge`, `CriticalLine.ncard_simple_zeros_ge` | no |
| Alpöge and Furman: of the zeros with `T < Im ρ ≤ 2T`, counted with multiplicity, shares of at least `2/3 − ε` are matched by distinct zeros on the critical line, `1/2 − ε` by simple zeros on it, and `3/4 − ε` by distinct zeros | `CriticalLine.two_thirds`, `CriticalLine.half_simple`, `CriticalLine.three_quarters_distinct` | no |

### How many zeros

| Result | Lean | H |
|---|---|---|
| `N(σ, T) ≪ T^{(30/13+ε)(1−σ)}(log T)^{12}` for `ζ`, and the classical `12/5` | `ZetaGMDensity.densityXi_thirty_thirteenths`, `ZetaHuxley.densityXi_twelve_fifths` | yes |
| Guth and Maynard's large values estimate, their Theorem 1.1 at `7/10 ≤ σ ≤ 4/5` | `ZetaGMLV.gm_large_values` | no |
| At most `C(qT)^{A(1−σ)}(log qT)^{10}` characters mod `q` have a zero with `β ≥ σ`, `\|γ\| ≤ T`: Ingham's `A = 3/(2 − σ)` and Huxley's `3/(3σ − 1)`, in steps | `LinnikInghamC.charDensity_ingham_c`, `LinnikHuxStep.charDensity_gen` | no |
| The same with `A = 101/50` on `[5/6, 1]` | `LinnikStep.charDensity_step` | yes |
| Chen, Gupta and Li's `(qT)^{(7/3)(1−σ)+ε}` on `[5/7, 16/21]`; and, on 30 steps of `[5/7, 131/168]`, exponents within `10^{−4}` of `4/(1 + σ)` with `(log qT)^{10}` | `LinnikCGLDensity.cglDensity`, `LinnikCGLSteps.charDensity_s0`, `LinnikCGLSteps.charDensity_s29` | |
| The curve `g*`, glued from these pieces: at most `2.3334(1 − σ)`, its largest exponent `7/3` (in Lean `2.3334`) at `σ = 5/7` | `SieveCurve7D.counts_7d`, `SieveCurve7D.g7d_le_lin` | yes |
| The Linnik paper's curve `g_H`: the trivial count below `7789/10000`, Huxley's steps above, with no estimate of Ingham's or of Chen, Gupta and Li's | `SieveCurveHx.counts_hx`, `SieveCurveHx.charDensity_hxT` | yes |

### Primes

| Result | Lean | H |
|---|---|---|
| `ψ(x) = x + O(x^{11/12+ε})`; under RH, `x + O(x^{1/2+ε})`, and under GRH `ψ(x, χ) = O(x^{1/2+ε})` for every `χ ≠ 1` | `HalfPlanePNT.psi_isBigO_eleven_twelfths`, `HalfPlaneGRH.RHandGRH.psi_isBigO`, `HalfPlaneGRH.RHandGRH.psiChi_isBigO` | yes |
| `ψ(x) = x + O(x·exp(−c(log x)^{3/5}(log log x)^{−1/5}))`, the strongest form known from refereed results | `PNTKV.PNT_KV` | no |
| `ψ(x; q, a) = x/φ(q) + O(x^{11/12+η})` for every `q` and every `a` prime to `q`, at fixed `q`; under GRH, `x/φ(q) + O(x^{1/2+η})` | `PNTProgressions.psiAP_isBigO`, `HalfPlaneGRH.RHandGRH.psiAP_isBigO` | yes |
| Linnik under GRH, the library's headline exponent: every class `a` mod `q` with `(a, q) = 1` holds a prime `p ≤ Kq^{2+η}` for every `η > 0`, by the density estimate with `A = 2` that GRH gives; GRH is L. Alpöge's, an input (above), so in the Lean a hypothesis, stated as the archive states it | `LinnikGRH.linnik_two`, `LinnikGRH.linnik_two_of_GRH` | yes |
| Linnik: every class `a` mod `q` with `(a, q) = 1` holds a prime `p ≤ Kq^{2150/1000}`, below `13/6`, where the Type II estimate in one variable has no window: the search with the estimate in two variables alone, the rest of a term with no prime of the rest's size being a product of the primes of its comparison's own tree, and with the reversal of a term of three or five primes through its largest prime, the cofactor kept as one number, the kernel following the plan of the search by hints; from the half-plane and Huxley's estimate, with no input of Chen, Gupta and Li's: its tests have the paper's conditions on the leaves of a comparison alone (`SieveAd.Plain.fillTests`), so no module of that formalisation is in its import cone (the Linnik paper's Theorem 1.2). Its certificate, like those of the next two rows, is opt-in to build (`lib/check/CheckLinnik.lean`) | `Linnik21500.linnik_21500` | yes |
| The same with `p ≤ Kq^{2100/1000}`: that search with terms of the sign `+` reversed too, the leaves of a comparison cut in three (the fourth moment of the cofactor's polynomial), the resonant window in both trees, a Type II estimate in one variable that sorts the characters by the sizes of a rest's own prime sums as well as by their zeros, with Chen, Gupta and Li's large values of the powers and the cofactor in the rest when it is one prime, the window's test at the two corners of the box of a rest's cells where its test at one corner fails, the chains over the frozen parts on cells as fine as the main tree's, a box of two primes cut in two where that pays, and a plan that searches every configuration of the estimate in two variables that the kernel's tests accept over the frozen parts (the Linnik paper's Theorem 1.1) | `Linnik21000.linnik_21000` | yes |
| In number, at `2150/1000` and at `2100/1000`: for every `q`, every `a` prime to `q` and every `x ≥ Kq^L` the class holds at least `c·x/(φ(q) log x)` primes `p ≤ x`, with `c > 0`. The searches prove the count at `x = q^L`, where the primes of the class in `(q^L, 2q^L]` number at least `(1 − C)/2` of `x/(φ(q) log x)` for large `q`, `C` the search's cost; the multiples of the modulus carry it to every `x`, which uses that the theorems hold for every modulus and every class (the Linnik paper's Corollary 1.3) | `Linnik21500.count_21500`, `Linnik21000.count_21000`, `Linnik21500.count_large_21500`, `Linnik21000.count_large_21000`, `SieveAd.count_of_large` | yes |
| Linnik by density estimates and the classical deduction, with the exponents `12`, `4`, `17/6`, `36/13`, `87/35`, `12/5` and `2.3334`, each `+ η` | `Linnik.linnik_twelve`, `LinnikDensity.linnik_four`, `LinnikSubconvex.linnik_seventeen_sixths`, `LinnikIngham.linnik_thirtysix_thirteenths`, `LinnikHuxley.linnik_eighty_seven_thirty_fifths`, `LinnikTwelve.linnik_twelve_fifths`, `LinnikG7.linnik_g7d` | yes |
| Linnik for almost all classes, below exponent `2`: for every `η > 0`, all the reduced classes mod `q` but at most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{1+η}` under GRH (L. Alpöge's, an input, above; in the Lean a hypothesis), and a prime `p ≤ Kq^{11667/10000+η}` from the curve `g*`, which rests on the half-plane and on Chen, Gupta and Li's Proposition 3.1 (the two inputs above); from a density exponent `A`, the exponent `A/2 + η`. Under GRH, with GRH's `√x` for every character, a bound of Turán's type: for `0 < δ ≤ 1`, all the classes but `Kq^{1−δ+η}` hold a prime `p ≤ Kq^{1+δ}`, so at `δ = 1 − κ` all but `Kq^{κ+η}` hold one below `Kq^{2−κ}`. These hold for almost all classes, not every class. The method is classical, the deduction above in mean square over the classes (under GRH it is P. Turán's argument); the exponent `1.1667` was not found in the literature by a quick search, and is not claimed as new | `LinnikAlmostAll.almostAll_one`, `LinnikAlmostAll.almostAll_one_of_GRH`, `LinnikAlmostAll.almostAll_turan`, `LinnikAlmostAll.almostAll_g7d`, `LinnikAlmostAll.almostAll_of_charDensity` | yes |
| A prime in `(y, y + y^θ]` for every large `y`, `θ > 17/30`; and for all `y ∈ [X, 2X]` outside a set of measure `X^{1−δ}`, `θ > 2/15`; under RH, every `θ > 1/2` | `ZetaGMDensity.short_primes_seventeen_thirtieths`, `ZetaGMDensity.almost_all_short_primes_two_fifteenths`, `HalfPlaneGRH.RHandGRH.short_primes` | yes |
| In terms of `Θ`: `limsup log\|ψ(x) − x\|/log x = Θ`, the same for `M(x)`, `Σ μ(n)n^{−s}` converges exactly on `Re s > Θ`, and a prime in `(y, y + y^θ]` for `θ > 2Θ/(1 + 2Θ)` | `PsiExponent.limsup_expo`, `MertensExponent.limsup_mexpo`, `MertensExponent.moebiusAbscissa_eq_Theta`, `InghamDensity.short_primes_Theta` | |
| `ψ(x) − x`, `M(x)` and the prime races mod 3, 4, 7 and 8 are `Ω±(x^θ)` for every `θ < 1/2` | `PsiOmega.psi_omega_half`, `PsiOmega.mertens_omega_half`, `PsiOmega.race_three_half`, `PsiOmega.race_four_half`, `WeilTwinGeneral.race_seven_half`, `PsiOmega.race_eight_half` | no |
| `M(x) = O(x^{11/12+η})`; `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{11/12+η})` with `deg P_k = k − 1`; `Q(x) = 6x/π² + O(x^{12/25+η})` for the squarefree numbers; under RH, `M(x)` and the error for `d_k` are `O(x^{1/2+η})`, and that for `Q` is `O(x^{2/5+η})` | `MertensExponent.mertens_isBigO_eleven_twelfths`, `DivisorExponent.divisor_isBigO_eleven_twelfths`, `DivisorExponent.natDegree_Pk_eq`, `SquarefreeCount.squarefree_isBigO_twelve_25ths`, `MertensExponent.rh_iff_mertens`, `HalfPlaneGRH.RHandGRH.divisor_isBigO`, `HalfPlaneGRH.RHandGRH.squarefree_isBigO` | yes |

### Values of `L`-functions, and quadratic fields

| Result | Lean | H |
|---|---|---|
| `ζ` and `1/ζ`, and uniformly in `q` every `L(s, χ)` and `1/L(s, χ)`, are `≪ (q\|t\|)^ε` on `Re s ≥ σ₀ > 11/12`; under RH, `ζ` and `1/ζ` are `≪ \|t\|^ε` on `Re s ≥ σ₀ > 1/2` | `HalfPlaneLindelof.zeta_bound_eleven_twelfths`, `LinnikLindelof.lindelof`, `HalfPlaneGRH.RHandGRH.zeta_bound` | yes |
| `\|ζ(σ + it)\| ≪ \|t\|^{(11/12−σ)/2+ε}` on `[1/12, 11/12]`, so `5/24` on the critical line; `\|L(1/2 + it, χ)\| ≪ (q(\|t\| + 2))^{5/24+ε}` uniformly; under RH, `\|ζ(1/2 + it)\| ≪ \|t\|^ε`, Lindelöf's hypothesis, and so Weyl's `\|t\|^{1/6+ε}` | `Subconvexity.zeta_strip_eleven_twelfths`, `LinnikSubconvex.critBoundχ`, `Subconvexity.lindelof_of_RH`, `HalfPlaneGRH.RHandGRH.weylBound` | yes |
| Littlewood's bounds, which he proved under GRH: `1/log log q ≪ \|L(1, χ)\| ≪ log log q` and `L′/L(1, χ) ≪ log log q` for quadratic `χ ≠ 1`; with explicit constants for every `χ ≠ 1`, real or complex, `e^{−γ−3/100}/(13(52 + ℓ)) ≤ \|L(1, χ)\| ≤ 13e^{γ+3/100}(52 + ℓ)`, `ℓ = log log(q + 2)`, so `13e^{γ+3/100}(1 + o(1)) log log q` where GRH gives `2e^γ log log q` | `Littlewood.norm_LFunction_one_ge`, `Littlewood.norm_LFunction_one_le`, `Littlewood.norm_logDeriv_one_le`, `LittlewoodSharp.norm_LFunction_one_bounds_sharp` | yes |
| Class numbers with explicit constants, so effective: `h_K ≥ √\|D\|/(85(52 + log log(\|D\| + 2)))` for imaginary quadratic `K`, `R_Kh_K ≥ √D/(55(52 + log log(D + 2)))` for real `K`, and `≪ √\|D\| log log \|D\|` from above with explicit constants | `ClassNumberSharp.classNumber_ge_85`, `ClassNumberSharp.regulator_mul_classNumber_ge_55`, `ClassNumberSharp.classNumber_le_sharp`, `ClassNumberSharp.regulator_mul_classNumber_le_sharp` | yes |
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
| The Davenport–Heilbronn function `dh` has `ζ`'s functional equation and zeros off the line, five of them located, one with real part above `11/12`, inside the zero-free half-plane of the Dirichlet `L`-functions; the hypotheses of the library's criteria, restated for `dh`, fail, so a proof of one for `ζ`, and the half-plane's proof, must use what `dh` lacks, such as the Euler product. The second Davenport–Heilbronn function, the combination with the other sign, has a zero with real part above `2`, where its Dirichlet series converges absolutely ([note](../formalisations/davenport-heilbronn.md)) | `PsiOmega.dh_offline_zero`, `PsiOmega.Locate.dh_zeros_located_four_box`, `PsiOmega.Locate.Z5.dh_zero_re_gt`, `PsiOmega.not_D_dh`, `PsiOmega.Locate.Sec.dh2_zero_re_gt_one` | no |

### The tools

The estimates that the results above are built from, each stated for reuse:

| Tool | Lean |
|---|---|
| Mean values of Dirichlet polynomials over the characters mod `q`, and their values at one point per character | `LinnikHybrid.mean_value_chars`, `LinnikHybrid.large_values_chars` |
| Large values: Halász–Montgomery (also with weights, and in mean square over a set of characters), Huxley's estimate, Guth and Maynard's, and Chen, Gupta and Li's with characters | `LinnikPower.hm_duality`, `SieveTypeIIHM.hm_duality_wt`, `SieveTypeIIHM.sum_bin_hm_sq`, `LinnikReflect.huxley_large_values`, `ZetaGMLV.gm_large_values`, `LinnikCGLHB101.prop31` |
| The hybrid fourth moment of `L(1/2 + it, χ)`; the fourth moment of `ζ` at well-spaced points; the approximate functional equation of `L(s, χ)²` | `LinnikFourth.fourth_moment`, `ZetaFourth.zeta_fourth_moment`, `LinnikGamma.afe` |
| Zero detection by a mollified Dirichlet polynomial; log-derivatives in zero-free discs; Perron's formula with a smooth weight, and contour shifts | `LinnikDetect.dichotomy`, `LogDerivDisc.logDeriv_le_Kld`, `Linnik.perron_exp`, `SmoothPerron.verticalIntegral_shift` |
| Sieves: Brun's fundamental lemma, Buchstab's identity at one `n`, Harman's comparison with stops in two variables and the bilinear Type I estimate, that estimate by Parseval's identity without the condition `2HD < q`, Proposition 3′ for two polynomials (for a curve on a region, and for the curve `ghx` of Huxley's estimate) and Lemmas 4.4, 4.5 and 4.6 for families in two variables, rough numbers by Buchstab's `ω` | `SieveBrun.fundamental`, `SieveDecomp.buchstab_pt`, `SieveTypeIB.typeIB_bound_wide`, `SieveTypeIBPairWide.pair_le_wide`, `SieveTypeIBAsymWide.leaves_ib_wide`, `SieveTypeIIHM.typeII_two_gen`, `SieveTwoZone7D.typeII_two_hx`, `SieveFamilyTwo.typeII_sharp_two`, `SieveUnwTwo.typeII_unw_two`, `SieveTwoChain.chain_two`, `SieveTwoComp.prop6_two`, `SieveRough.psi_le` |
| Over `ℤ[ω]` and `ℍ³`: the quadratic large sieve, and Kubota's theta function with Patterson's coefficients | `Eis.quadLargeSieve`, `Eis.kubotaTheta` |
| Vinogradov's mean value theorem, weak form; Weil's explicit formula as a form | `VinoRec.vmvt_weak`, `WeilForm.weilQ_symbol` |

Of these, the mean values, the Halász–Montgomery inequality, Guth and Maynard's estimate, the log-derivative bound,
Brun's lemma, the large sieve, the theta function, Vinogradov's mean value theorem and Weil's form do not use the
half-plane. The certificate pipeline, `tools/linnik/`, turns a sieve decomposition into Lean files that the kernel
checks by `decide +kernel`, in the opt-in build (`lib/check/CheckLinnik.lean`).

## What a new input buys at once

The deductions are stated for any input, against Mathlib's `ζ` and `LFunction`, so an input proved anywhere plugs in:

| Prove | and the library gives | Through |
|---|---|---|
| no zero of `ζ` on `Re s > β`, for some `β < 1` | the errors of `ψ`, `M` and `Σ d_k` at `x^{β+η}`, and of the squarefree count at `x^{1/(3−β)+η}` | `HalfPlanePNT.psi_isBigO_of_zeroFree`, `MertensExponent.mertens_isBigO_of_zeroFree`, `DivisorExponent.divisor_isBigO_of_zeroFree`, `SquarefreeCount.squarefree_isBigO_of_zeroFree` |
| the same for `L(s, χ)`, `χ ≠ 1` | `ψ(x, χ) = O(x^{β+η})`; for every `χ ≠ 1` mod `q`, with the row above, `ψ(x; q, a) = x/φ(q) + O(x^{β+η})` for `a` prime to `q` | `ChiPNT.psiChi_isBigO_of_zeroFree`, `PNTProgressions.psiAP_isBigO_of` |
| a density estimate `Linnik.CharDensity A B C` over the characters, `A ≥ 2` | Linnik's theorem with every exponent above `A`, and for almost all classes every exponent above `A/2` | `Linnik.linnik_of_charDensity`, `LinnikAlmostAll.almostAll_of_charDensity` |
| `ShortWeil.DensityXi A B` and a zero-free region `ShortWeil.ZeroFreeXi α` for `ζ` | a prime in `(y, y + y^θ]` for `θ > max(1/2, 1 − 1/A)` | `ShortWeil.short_primes_of_density` |
| `ShortWeil.DensityXi (A + ε) B` for every `ε > 0` | primes in almost all intervals `(y, y + y^θ]` for `θ > 1 − 2/A` | `AlmostAll.almost_all_of_density` |
| `\|ζ(1/2 + it)\| ≪ \|t\|^c` (`CrossCriteria.ZetaCritBound`) | the density exponent `2 + 4c` | `InghamDensity.densityXi_of_zetaCrit` |
| RH, and with it GRH for every `L(s, χ)`: the rebuild's top `HalfPlaneGRH.RHandGRH`, which L. Alpöge's Lean archive proves (an input, above) | no zero of `ζ` or of any `L(s, χ)` on `Re s > 1/2`, so the deductions above at `β = 1/2`: `ψ`, `ψ(x, χ)`, `ψ(x; q, a)`, `M` and `Σ d_k` at `x^{1/2+η}`, the squarefree count at `x^{2/5+η}`; from RH alone the Lindelöf hypothesis, and from it Weyl's bound, the density hypothesis and a prime in `(y, y + y^θ]` for every `θ > 1/2` | `HalfPlaneGRH.RHandGRH.corollaries`, `Subconvexity.lindelof_of_RH`, `InghamDensity.densityHypothesis_of_lindelof` |
| GRH for every `L(s, χ)`, which L. Alpöge's Lean archive proves (an input, above) | Linnik's theorem with every exponent above `2`: the library's headline Linnik exponent | `LinnikGRH.linnik_two_of_GRH`, and in the archive's words `LinnikGRH.linnik_two` |
| Petrow and Young's Weyl bound for every `L(s, χ)`, uniformly (`LinnikWeyl.PYWeyl`) | Weyl's bound for `ζ`, and Huxley's exponents above `5/6` for the characters | `LinnikWeylBridge.weylBound_of_PYWeyl`, `LinnikStairs7.charDensity_hy_0`, `LinnikStairs7.charDensity_hy_top` |
| that RH fails | `ψ(x) − x = Ω±(√x)` | `HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH` |
| the arb certificates `WeilForm.CertE` and `WeilForm.CertO`: lower bounds for 350 mode energies, and the definiteness of two Gram matrices | Weil's form positive on every real probe at supports `2a ≤ 1.6`, past the prime powers `2`, `3` and `4` | `WeilForm.weilQg_ge_both` |
| Proposition 3′ in two variables at `L` on a region (`SieveFamilyTwo.TypeIITwoAt`), `2 < L ≤ 5/2` | Harman's comparison for the primes in a class mod `q` | `SieveTwoComp.prop6_two_at` |

## Connections

What the results give in other parts of number theory, and in physics. Every row is a theorem with no hypothesis,
whose axioms are Lean's three; H is as above.

| Connection | Lean | H |
|---|---|---|
| Algorithms: every proper subgroup of `(ℤ/qℤ)ˣ` misses a prime `p ≤ C(log q)^A`, `A > 12`, so these primes generate `(ℤ/qℤ)ˣ`. Under GRH this is E. Bach's bound, which makes G. L. Miller's primality test deterministic | `SmallPrimes.exists_prime_not_mem`, `SmallPrimes.closure_primes_eq_top` | yes |
| Power residues: for every `k ≥ 2` dividing `p − 1`, a prime `ℓ ≤ C(log p)^A` that is not a `k`-th power mod `p` | `SmallPrimes.exists_prime_not_pow` | yes |
| Character sums: `Σ_{n≤x} χ(n) = O(x^{11/12+ε})`, so `o(x)`, uniformly in `q` and `χ ≠ 1` on `x ≥ q^δ`, every `δ > 0`, where Burgess's method needs `x ≥ q^{1/4+ε}`; the quadratic residues and the non-residues mod `p` in `[1, x]` differ in number by `O(x^{11/12+ε})` for `x ≥ p^δ` | `ShortCharSums.norm_sum_le_rpow`, `ShortCharSums.norm_sum_le_mul`, `ShortCharSums.card_squares_sub_le` | yes |
| Primitive roots: every prime `p` has a prime primitive root `ℓ ≤ C_ε p^ε`, where Burgess's method gives `p^{1/4+ε}` for the least primitive root and GRH `(log p)^6`; so does every modulus with a primitive root, and for a safe prime `p = 2r + 1`, `ℓ ≤ C(log p)^A`, `A > 12` | `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime`, `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow`, `LeastPrimitiveRoot.exists_prime_primRoot_le_safe` | yes |
| Primality certificates: `n ≥ 2` is prime if and only if some `a ≤ C_ε n^ε` passes Lucas's test (`a^{n−1} ≡ 1`, `a^{(n−1)/r} ≢ 1` for every prime `r ∣ n − 1`); for `n = 2r + 1`, `r` an odd prime, some `a ≤ C(log n)^A` does, so given `r` the test runs in polynomial time | `LucasWitness.prime_iff_exists_lucas_le_rpow`, `LucasWitness.prime_iff_exists_lucas_le_safe` | yes |
| Primality testing: an odd `n ≥ 3` is prime if and only if it is a strong probable prime to every base `a ≤ C(log n)^A` prime to it, `A > 12`: G. L. Miller's deterministic test, which needed the extended Riemann hypothesis | `MillerTest.prime_iff_forall_strongProbablePrime`, `MillerTest.exists_witness_le` | yes |
| Galois theory: the Frobenius elements `ζ ↦ ζ^ℓ` of the primes `ℓ ≤ C(log q)^A` generate `Gal(ℚ(ζ_q)/ℚ)`, and when that group is cyclic one of them with `ℓ ≤ C_ε q^ε` does: effective Chebotarev for the cyclotomic fields, Bach's bound under GRH | `CyclotomicFrobenius.closure_frob_eq_top`, `CyclotomicFrobenius.exists_frob_generator` | yes |
| Class groups: Gauss's class number problem with an explicit bound, `\|D_K\| ≤ (320π e^{2·10²¹} h_K)⁴` for imaginary quadratic `K`, polynomial in `h_K` as under GRH; and class number one only for `\|D_K\| < 2.5·10⁷`, a finite search that the kernel checks: an imaginary quadratic field has class number one if and only if its discriminant is `−3, −4, −7, −8, −11, −19, −43, −67` or `−163` (Baker, Heegner, Stark; here without Heegner's method, [note](../formalisations/class-number-one.md)) | `ClassNumberBound.abs_discr_le`, `ClassNumberSharp.abs_discr_lt_of_classNumber_eq_one`, `ClassNumberOne.classNumber_eq_one_iff` | yes |
| Physics, crystals: `Σ_{n≥1} (−1)^n r₂(n) n^{−s} = −4(1 − 2^{1−s}) ζ(s) L(s, χ₋₄)`, holomorphic off `s = 1`. At `s = 1/2` it is `−M`, where `M ≈ 1.6155` is the Madelung constant of the square lattice: an ion of a two-dimensional ionic crystal has electrostatic energy `−Me²/a` | `Madelung.lseries_coeff`, `Madelung.differentiableOn_rhs` | no |
| Physics, the primon gas: `Σ μ(n) n^{−β}` is the partition function of B. Julia's primon gas with the sign `(−1)^F` of D. Spector's fermion number. It converges for `β > Θ` and diverges for `β < Θ`, with `1/2 ≤ Θ ≤ 11/12`: past the bosonic gas's Hagedorn point `β = 1` | `MertensExponent.moebiusAbscissa_eq_Theta`, `PsiExponent.half_le_Theta`, `PsiExponent.Theta_le` | yes |
| Geometry of numbers: the points of `ℤⁿ` in a ball of radius `R` number `V_n Rⁿ(1 + o(1))`, `V_n = π^{n/2}/Γ(n/2 + 1)`, most in dimension 5; in the plane they give `L(1, χ₋₄) = π/4`, Leibniz's series | `BallTower.count_div_pow_tendsto_ballVol`, `BallTower.counted_volume_max_five`, `AngularResidue.LFunction_chi4_one` | no |
| Quadratic forms: over a finite field of odd size `q`, `x² + y² = a` has `q − χ₋₄(q)` solutions and `x² + y² + z² + w² = a` has `q³ − q`, for `a ≠ 0`: the local factors of Jacobi's and Siegel's formulas; and Siegel's formula for four squares, `r₄(n) = π²n∏_p δ_p(n)` with the local density at every prime | `LocalTeeth.card_two_sq`, `LocalTeeth.card_four_sq`, `SiegelFour.siegel` | no |
| Elliptic curves: Hasse's bound `\|q + 1 − #E(𝔽_q)\| ≤ 2√q` for every elliptic curve over a finite field of odd characteristic, by Yu. I. Manin's proof without isogenies. On a twist over `𝔽_q(t)` the degree of a point is a quadratic form, and the Frobenius points `P_k` have a positive semidefinite Gram matrix: the normalised traces `c_d = (q^d + 1 − #E(𝔽_{q^d}))/(2q^{d/2})` form a positive-definite function on `ℤ`, the Riemann hypothesis for `E` in every degree, which gives for instance `(q + 1 − #E(𝔽_q))² − 2q ≤ q² + 1 − #E(𝔽_{q²})`. For `y² = x³ + D` in characteristic neither 2 nor 3: when `q ≡ 1 (mod 3)` the Frobenius is an Eisenstein integer `u + vω` of norm `q`, a point of the lattice `ℤ[ω]` on the circle of radius `√q`, and `#E(𝔽_q) = q + 1 − (2u − v)`; when `q ≡ 2 (mod 3)`, `#E(𝔽_q) = q + 1` | `ManinHasse.abs_trace_le`, `ManinHasse.toeplitz_nonneg`, `ManinHasse.trace_two_ge`, `HasseEisenstein.abs_trace_le`, `HasseEisenstein.exists_eisenstein_trace`, `HasseEisenstein.card_points_of_mod_three_eq_two` | no |
| Ergodic theory: the logarithms of the primes are linearly independent over `ℤ`, and a vertical line equidistributes on Bohr's torus (Kronecker and Weyl) | `BohrTorus.eq_zero_of_sum_log`, `BohrTorus.tendsto_mean_character` | no |
| Analysis: Landau's theorem, a Dirichlet series with nonnegative coefficients is singular at the real point of its abscissa; Mathlib does not have it | `LandauLaplace.LSeries_landau` | no |
| Noncommutative geometry: the least value `λ₁(a)` of Weil's form on supports `[−a, a]`, which A. Connes and C. Consani study, is positive for `a ≤ 1/12`, has a unique ground state for `2a < log 2` (the range of their archimedean positivity theorem), and is at most `Ke^{16a − 2πe^{2a}}` | `WeilForm.weilQg_ge_twentieth_all`, `WeilForm.groundState_unique_below_log2`, `WeilForm.lam_dexp` | no |

Within reach, with no hypothesis, from results the library has:

- **Pell's equation**: the least solution of `x² − dy² = 1`, `d` squarefree, has `log(x₁ + y₁√d) ≪ √d log log d`:
  `QuadClassNumber.regulator_mul_classNumber_le`, and `x₁ + y₁√d = ε^m` with `ε` the fundamental unit of `ℚ(√d)` and
  `m` dividing 6.
- **Binary quadratic forms**: `2` is a cube mod a prime `p ≡ 1 (mod 3)` if and only if `p = x² + 27y²` (Gauss), from
  cubic reciprocity (`Eis.cub_recip`) and its supplementary laws.
- **Weil positivity past the primes 2 and 3**, to supports `2a ≤ 1.6`, beyond Connes and Consani's `log 2`: the
  library proves it from hypotheses that arb computations support, lower bounds for 350 mode energies and the
  definiteness of two Gram matrices (`WeilForm.weilQg_ge_both`, and `WeilForm.weilQ_ge_prime3` for even probes below
  `2a = log 3`). Certificates that the kernel checks, as the Linnik sieve's are, would remove the hypotheses. X. Zhu's
  preprint arXiv:2608.24827 (2026) claims the same window by interval arithmetic. Where RH holds, which counts as
  proven here, Weil's form is nonnegative at every support (`WeilForm.weil_criterion_zeta`); the certificates would
  give the margin of `WeilForm.weilQg_ge_both` with no hypothesis.
- **Hyperbolic 3-space**: Kubota's `θ` (`Eis.kubotaTheta`) as an eigenfunction of the Laplacian at `s(2 − s) = 8/9`,
  below the continuous spectrum `[1, ∞)`: a bound state of a free particle on the cubic metaplectic cover. The library
  has the energy `∫ v²|∇F|² dz dv/v³` and its invariance (`Eis.lintegral_energy_actP`), not the Laplacian.
- **A zero of `dh` with `Re s > 1`**: the half-plane's `dh` column is filled, by a zero with `Re s > 11/12` at height
  `24415` (`PsiOmega.Locate.Z5.dh_zero_re_gt`). Davenport and Heilbronn's zeros in the half-plane of absolute
  convergence are rarer. Fifteen are located numerically, the lowest found at height `2.53·10¹²`
  ([research-opportunities.md](research-opportunities.md), §8.5), where the certificate's approximant has too many
  terms. A theorem would be either an approximate functional equation for `dh` with an explicit error, or the
  existence proof by Bohr's argument at low height, which needs Kronecker's theorem and one more located zero.
  The second Davenport–Heilbronn function has such zeros at low height, and one is certified, at height `1650` with
  real part above `2` (`PsiOmega.Locate.Sec.dh2_zero_re_gt_one`).

## The frontier

In order of what is in reach.

1. **Primes in short intervals, below `θ = 0.52`.** The library proves `θ > 17/30` by density. R. Li's sieve gives
   `0.52` (arXiv:2308.04458). [Pull request #48](https://github.com/dickie81/number-theory/pull/48) is putting Li's
   argument into Lean for `θ = 0.52`, with Type II information at real Hölder exponents. Its computation, Monte Carlo
   and not a proof, keeps Li's constant positive down to `θ ≈ 0.5182` once Guth and Maynard's estimate
   (`ZetaGMLV.gm_large_values`) joins Huxley's. A Lean proof below `0.52` would go below Li, resting on the half-plane
   as Linnik's exponent does: the sieve's main terms take the prime number theorem in short ranges from it.
   *24 November:* settled where RH holds, which counts as proven here: every `θ > 1/2`
   (`HalfPlaneGRH.RHandGRH.short_primes`). What the sieve would still add is an exponent that does not rest on
   L. Alpöge's archive.
2. **Linnik's exponent.** With GRH from L. Alpöge's archive the library's exponent is `2 + η`
   (`LinnikGRH.linnik_two`), what the density route gives at `A = 2`; an exponent below `2` for every modulus is not
   known even under GRH, so any route to one is of the greatest interest. For almost all classes the library is below
   `2`: `1 + η` under GRH and `11667/10000 + η` from the curve `g*`, for all classes but `Kφ(q)q^{−c}` of them
   (`LinnikAlmostAll.almostAll_one`, `LinnikAlmostAll.almostAll_g7d`); and under GRH all classes but `Kq^{κ+η}` have
   a prime below `Kq^{2−κ}` (`LinnikAlmostAll.almostAll_turan`). With no hypothesis, the Linnik paper proves
   `43/20 = 2150/1000` (`Linnik21500.linnik_21500`, its Theorem 1.2)
   from the half-plane and Huxley's density estimate alone, and `21/10 = 2100/1000` (`Linnik21000.linnik_21000`, its
   Theorem 1.1) from the half-plane, Chen, Gupta and Li's Proposition 3.1 and Ingham's and Huxley's density estimates;
   their certificates stay in the library, with a build that is opt-in (`lib/check/CheckLinnik.lean`).
   With the half-plane, Harman's
   theorem of 2005 on primes in a progression (refereed, not formalised) gives `1/0.472 < 2.1187`, below `43/20` and
   above `21/10` (the paper's Section 12). Both exponents are below
   `13/6`, where a Type II estimate in one variable on a window whose characters are counted only through the zeros'
   bins closes for the peak `A = 7/3` of Chen, Gupta and Li's curve (`1 + A/2 = 13/6`), and both
   sieves have a Type II estimate in two variables on an explicit region, which counts characters only from
   `7789/10000` on. The sieve of `43/20` has Harman's comparisons, with the rest among a term's own primes or among
   the primes of its comparison's own tree (`SieveFillComp.prop6_fill`), and the reversal of a term of three or five
   primes through its largest prime, as an identity with the cofactor kept as one number
   (`SieveAd.Plain.bd_flip_core`). Its certificate is the plan of a search, which the kernel follows by hints and
   checks step by step (`SieveAd.Plain.solveD_sound`). The sieve of `21/10` has three rules more. Terms of the sign
   `+` are reversed too. The leaves of Buchstab's tree whose cofactor is shorter than `√q`, out of the bilinear
   estimate's reach, are evaluated by the Type II estimate in two variables with the fourth moment of the cofactor's
   polynomial over a bin of characters (the case `r = 2` of Burgess's moments) as a third bound, a box of leaves that
   straddles the paper's region being cut in three. And a box may be evaluated by the resonant window
   (`SieveTypeIIHM.typeII_res`), a Type II estimate in one variable whose characters are sorted by the sizes of a
   rest's own prime sums as well as by their zeros, with Chen, Gupta and Li's large values of the powers and the
   cofactor in the rest when it is one prime, tested at one corner of the box of a rest's cells or at two
   (`SieveResTest.resY_sound`). With cells over the frozen parts as fine as the main tree's, and a plan that searches
   every configuration the kernel's tests accept there, the search passes at `2100/1000` at a cost of `0.97717K` on
   `9.01·10^7` steps. The certificates at weaker exponents are no longer in the tree; they are in the git history.
   Below `43/20`, by the exact search's measurements ([`research-opportunities.md`](research-opportunities.md), §3.1),
   about a quarter of the cost is the cells' width, each `0.005` of exponent costs `5%` to `9%`, and the rules that
   the certificate at `43/20` lacks are worth a few per cent each; a second level of reversal is not written. Going
   much further needs Type I information on longer products than the bilinear estimate's `d₁d₂² < x`, or a Type II
   estimate on a wider region, which a better density estimate above `7789/10000` would give only a little of.
3. **The half-plane at `7/8`.** OpenAI's main preprint states `Re s > 7/8`, and their own Lean proves it for every
   `χ`; the library proves `11/12`, by the companion route. A proof of `7/8` here would feed the deductions above at
   once: `ψ`, `M`, `ψ(x, χ)` and `Σ d_k` at `x^{7/8+η}`, the squarefree count at `x^{8/17+η}`, and `Θ ≤ 7/8`. The
   Ankeny, Littlewood and class-number chain and `Subconvexity.zeta_strip_eleven_twelfths` have `11/12` written in;
   made parametric, they would give `A > 8` in place of `A > 12`, and `3/16` in place of `5/24` on the critical line.
   Linnik's exponent would not move. *24 November:* superseded where RH and GRH hold: under the rebuild's top,
   `HalfPlaneGRH.RHandGRH`, the deductions above hold at `1/2` (`HalfPlaneGRH.RHandGRH.corollaries`), and the chains,
   made parametric, would give `A > 2`.
4. **Density estimates.** For `ζ` the library proves Guth and Maynard's maximum, `30/13`, as one exponent for all `σ`,
   not their curve. For the characters it proves Chen, Gupta and Li's Proposition 3.1 and the steps the Linnik curve
   needs, not their Theorem 1.2; above `5/6` its exponent is `101/50` against Huxley's `2`: the zeros that its
   detector counts with the fourth moment cost at least `1.974`, and only `LinnikWeyl.PYWeyl` would remove them. Each
   sharper estimate enters through the deductions above. *24 November:* settled where RH and GRH hold: RH gives the
   density hypothesis for `ζ` (`HalfPlaneGRH.RHandGRH.corollaries`), and GRH the exponent `2` for the characters
   (`LinnikGRH.charDensity_two_of_GRH`).
5. **The Riemann hypothesis.** *24 November:* RH and GRH now count as proven here, through L. Alpöge's archive (an
   input, above), whose proof the library is rebuilding on its own stack ([rh-rebuild.md](rh-rebuild.md)); in its
   Lean the rebuild's top, `HalfPlaneGRH.RHandGRH`, stays a hypothesis. The library reduces RH to properties of
   Weil's form in about forty ways, proves none of their hypotheses, and shows, through `dh`, that no argument which
   applies to `dh` as well can prove them. A new criterion should come with its `dh` column, which tests it before any
   work on `ζ`. A geometric direction, that the analogue for `ζ` of the surface `C × C` in Weil's proof for curves is
   the discretisation of the infinite unit ball, is set out in [ball-conjecture.md](ball-conjecture.md), with its
   rank-two case: Hasse's bound for every elliptic
   curve of odd characteristic (`ManinHasse.abs_trace_le`) and the Riemann hypothesis for it in every degree, from the
   lattice of Manin's twist (`ManinHasse.toeplitz_nonneg`), and for `y² = x³ + D` with the Frobenius an Eisenstein
   integer (`HasseEisenstein.abs_trace_le`). Over a finite field Weil's criterion is proved in both directions: the
   kernel of the point counts is positive-definite exactly when the inverse zeros lie on `|α| = √q`
   (`WeilFF.countKernel_posDef_iff`). Its test shows that an Euler product and a functional equation do not give the
   positivity: `𝔾_m × (𝔸² ∖ 0)` over `𝔽_3` has both, in the shape of an elliptic curve over `𝔽_27`, and its kernel is
   not positive-definite (`PurityTest.not_posDef`). Over `ℚ` the same holds for `ζ(s)ζ(s − 1)`, the zeta function
   of `ℙ¹` over `ℤ`, with Hadamard's weights and with the Gaussian ones (`PurityRational.not_posDef`,
   `PurityRational.not_posDef_gauss`), also for its kernel computed from the primes (`PurityPsi.not_posDef_psi`), and
   Lagarias and Rains's `Z(4, ·)`, which is that zeta function up to an entire factor, has zeros off its line
   (`TwoVariableZetaPurity.exists_zero_re_ne_two`), while at `w = 2` RH on its line is RH with GRH for `χ₋₄`
   (`TwoVariableZetaTwo.rh_two_iff`); Weil's twin form of `ℙ¹` has `ζ`'s rate plus one (`PurityTwins.rate_iff_zeta`),
   that of `ζ(s)ζ(s − k)` `ζ`'s rate plus `k`, so RH is the least rate of each (`PurityLadder.rh_iff_rate_k`). For `ζ`
   the statement the conjecture must deliver is proved: RH
   holds exactly when `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}` is positive-definite on the positive rationals
   (`BallKernel.rh_iff_posDef`), the explicit formula computes `K` from the primes (`BallKernel.kerK_explicit`), and
   the kernel of `dh` is not positive-definite (`PsiOmega.not_posDef_dh`). The structure the conjecture asks for is
   proved in the function-field case: the Frobenius of Manin's twist multiplies the degree form by `q` and carries
   `P_k` to `P_{k+1}` (`ManinHasse.frobenius_similitude`), so the point counts of `E` are the Gram kernel of an orbit
   of a similitude of an integral lattice (`ManinHasse.gram_orbit_card`). For `ζ` such an orbit exists in a Hilbert
   space exactly under RH, with `φ_n` acting on `ℓ²` of the zeros by `n^ρ` (`BallLattice.rh_iff_realization`), but it
   spans no lattice: the vectors `w_{n+1} − w_n` are nonzero and their norms tend to `0` (`BallLattice.not_discrete`).
   With the weights `1/(ρ(1 − ρ))` of Hadamard's identity in place of the Gaussian, RH is again positive-definiteness
   (`BallHadamard.rh_iff_posDefH`), but the kernel has a cusp at `1` and the obstruction does not apply
   (`BallHadamard.not_smooth`), since `ζ` has infinitely many zeros (`ZerosInfinite.infinite_ZIdx`). In every
   realization of that kernel the gaps `‖w_{n+1} − w_n‖` are unbounded (`BallHadamard.unbounded_gaps`), because the
   number of zeros up to height `T` is not `O(T)` (`ZerosDense.not_linear`). That kernel is computed from the primes
   through Chebyshev's `ψ` (`BallPsi.kerH_explicit`), so RH is the positive-definiteness of a kernel that does not
   mention the zeros (`BallPsi.rh_iff_posDef_psi`). With Lebesgue measure in place of the zeros the orbit spans the
   cubic lattice, and every Gram–Schmidt pivot equals the first (`BallFlat.flat_pivot`). In Weil's terms, take classes
   `D_n` with intersection numbers `D_m·D_n = m + n − √(mn)·K_H(m/n)`, computed from the primes. Then RH is the
   Castelnuovo–Severi inequality for their integer combinations (`BallWeil.rh_iff_castelnuovo_severi`), and also the
   upper half of the Hasse–Weil bound for those numbers (`BallWeil.rh_iff_weil_bound`), and the Hodge index theorem
   from counting, through Minkowski's theorem (`HodgeCounting.rh_iff_counting`). The orbit-lattice conjecture is
   equivalent to it (`PivotSharp.rh_iff_orbitLattice`; the direction to RH is `BallWeil.rh_of_pivots`). Under RH every
   Gram–Schmidt pivot of the orbit after the first is at least `0.0577`, against the first, `K_H(1) = 0.0462`
   (`PivotSharp.pivot_ge_rh`), and the pivots grow like `log k` (`BallPivot.pivot_ge`). RH is also equivalent to `w_1`
   being a shortest vector of the lattice the orbit spans: the form is at least `K_H(1)` at every nonzero integer vector
   (`PivotSharp.rh_iff_shortest`), and under RH `±w_1` are its only shortest vectors (`PivotSharp.shortest_unique`).
   Both forms fail for the same construction over curves and for a positive proportion of real Dirichlet characters, so
   they are specific to `ζ` ([ball-conjecture-tests.md](ball-conjecture-tests.md), §4, §5, §7). On the class of vectors `n·x_n = Σ_{d ∣ n, d ≤ D₀} E_d(n/N)`, to which the minimisers are seen to belong, a vector whose boundary function `G = Σ_d E_d/d` has `Ĝ(ρ) ≠ 0` at some zero has `Q_N(x) ≥ c·N` under RH, with `c` any number below the sum of `|Ĝ(ρ)|²/(¼ + γ²)` over finitely many zeros, so the vectors with `Q_N(x) = O((log N/N)·Σx_n²)` have `Ĝ(ρ) = 0` at every zero (`BallLoud.loud_sum`, `BallLoud.quiet_carries_zeta`). Two primes already carry RH: for distinct primes `p` and
   `q`, RH holds exactly when `K_H(p^a q^b) ≥ −K_H(1)` for all integers `a` and `b`
   (`BallSlice.rh_iff_bound_pair`), so in particular for `2^a 3^b` (`BallSlice.rh_iff_two_three`). At every stage `N` the primes above `N/2`, which have no other multiple
   up to `N`, are never absent and are asymptotically half of all the primes (`LonelyPrimes.lonely_ratio_pos`,
   `LonelyPrimes.tendsto_lonely_ratio`). Weighted by `log p` they carry half of `x` with an error of exponent exactly
   `Θ`, so RH holds when and only when the error is `O(x^{1/2+ε})` (`LonelyJoins.rh_iff_lonely_weight`), and for
   `θ > 17/30` every interval `(y, y + y^θ]` of the frontier holds one (`LonelyJoins.lonely_in_window`).
   [connes-links.md](connes-links.md) lists how this strand joins the rest of the library.
6. **Tools that are missing.** The large sieve over all moduli `q ≤ Q` (the library has one modulus at a time), so no
   Bombieri–Vinogradov; bounds for Kloosterman sums, which the bilinear Type I estimate avoids; exponent pairs (the
   Weyl bound is only a hypothesis, or a consequence of the rebuild's top, `HalfPlaneGRH.RHandGRH.weylBound`);
   Selberg's and Rosser's sieves; anything in the twelve sections the library does not touch.

## Debts

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
- Computations that are not theorems: the region's exactness and the Pólya–Vinogradov check of the Linnik
  supplement (§S6), the measurements of the sieve below `43/20`, and the short-interval Monte Carlo of pull request
  #48.
- Each note lists the sources that were not read; of the Linnik paper's bibliography, Buchstab (1937) is unverified,
  and the paper's README lists the entries that were not read.

## Building on it

- **Where code goes.** `lib/core` needs Mathlib only; `lib/pnt` adds PrimeNumberTheoremAnd; `lib/zeta23` adds `zeta23`
  and cannot be imported with `lib/pnt`; `lib/dh` is its own layer. Module names are flat, so after adding a module
  run `python3 scripts/gen_lakefile.py`.
- **A new result.** Print its axioms in a check file: `lib/check/CheckAll.lean`, or `lib/check/Check.lean` for a
  paper's, or `lib/check/CheckLinnik.lean` for one that needs the opt-in Linnik certificates. Another printed result
  must use it, or `formalisations/` must name it, or `scripts/dead_code.py` fails; a
  result under a hypothesis the library does not prove goes in a table "Conditional results" there. Then run
  `python3 scripts/inventory.py`, and update this page if the result changes a line of it.
- **A result from the literature** gets a note in `formalisations/`: its source, its Lean statement, the differences,
  how it was done. A paper claims only its own steps ([papers](../papers/README.md)).
- **The build.** Before importing a module into one the default build reaches, `python3 scripts/import_cone.py Check
  --why MODULE` shows what it brings, certificates included; certificates are generated by `tools/` and compared byte
  for byte in CI. The Linnik certificates are opt-in: only `lib/check/CheckLinnik.lean` may import them, which
  `scripts/gen_lakefile.py` checks. Memory, CI's stages and the opt-in build are in [`building.md`](building.md).
- **Where to start.** This page, then the note of the area, then [`inventory.md`](inventory.md) for the names.
