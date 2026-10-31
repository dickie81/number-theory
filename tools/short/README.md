# Primes in short intervals: Li's sieve with real-exponent Type II information

R. Li, *The number of primes in short intervals and numerical calculations for Harman's sieve* (arXiv:2308.04458v8),
proves that `[x − x^0.52, x]` contains primes for large `x`. These tools recompute his lower bound with more Type II
information, and find that the constant stays positive down to `θ ≈ 0.5182`. They reuse his published C++ predicates
(the arXiv ancillary file `LB_521_160_1.cpp`, which `build.sh` downloads; it is not redistributed here) and change only
the Type II_n regions of his Lemmas 4.2, 4.4 and 4.5. The computation is Monte Carlo, not a proof; the Lean side is
below.

## The variants

All four use Harman's moment lemma (Lemma 7.21 of *Prime-Detecting Sieves*): for a prime-factored Dirichlet polynomial
`L = T^{1/D}`, `∫_T |L(1/2+it)|^δ ≪ L^{δ/2}(log x)^{−K}` once `δ > δ_req(D)`. `dtable.py` computes `δ_req(D)` from large
values estimates for the powers `L^k`: the mean value theorem, Huxley's estimate, and optionally Guth–Maynard's Theorem
1.1 on `σ ∈ [7/10, 4/5]` (the library's `ZetaGMLV.gm_large_values`). With Huxley it reproduces Li's `δ_0 = (δ − 1)/2`
at even `δ` and Harman's `δ ≥ 4δ_0 − 2h` for real `δ`.

- **V0**: Li's predicates as published: Hölder with `δ_1 = 2` for a factor `≥ T`, even `δ_j` by the mean value
  theorem for the middle factors, and the moment lemma (Huxley) for the last factor only.
- **V1**: V0, with each tuple's last threshold from the Guth–Maynard table.
- **V2**: V0, or any Hölder assignment with real exponents: every factor takes the mean value theorem (an even moment,
  or any larger real one through the trivial bound `|L| ≤ L^{1/2}`) or the moment lemma (real `δ`), at least one takes
  the moment lemma (the saving), and `Σ 1/δ_j = 1` (Huxley).
- **V3**: V1, or V2's test with the Guth–Maynard table.

The general test runs once per set of factors: Li's wrappers present each set with every factor in turn as the
implicit one (`1 − Σ t_j`) and the explicit ones in every order, and the test takes the call with the explicit factors
in decreasing order and the implicit one smallest. Groupings of factors come from his wrappers too.

Guth–Maynard's estimate alone adds nothing to the mean value theorem here: `dreq_variants.py` prints `δ_req` with each
subset of the three estimates, and the gain of V2 comes from Huxley's, with Guth–Maynard's improving on it (V3).

## Files

| File | What it does |
|---|---|
| `build.sh` | Downloads `LB_521_160_1.cpp` from arXiv (checked by SHA-256), runs `make_li_param.py`, tabulates `δ_req` if `dtables.h` is missing (about 8 minutes), and compiles `harness_theta`. With `--validate` it also compiles `val_orig.cpp` and `val_param.cpp` and checks that they print the same thing. |
| `make_li_param.py` | Writes `li521_orig.inc` (Li's predicates, unchanged but for line endings), `li_param.inc` (the same with θ a parameter `TH`, `γ(θ)` from his Lemma 4.1, `ν(α)` from its definition, and his Type II_n predicates renamed `Li{3,4,5}DL722`) and `li_tuples.h` (the Hölder tuples inside them). |
| `val_orig.cpp`, `val_param.cpp` | Integrate every loss term at θ = 0.521 on the same sampled points with Li's predicates and with the parametric ones. |
| `dtable.py`, `gen_table.py` | `δ_req(D)` for Huxley (closed form) and Guth–Maynard (numerical); `gen_table.py` writes `dtables.h`. |
| `dreq_variants.py` | `δ_req` with the mean value theorem alone, with Huxley, with Guth–Maynard, and with all three. |
| `harness_theta.cpp` | Every region-C term of Li's final bound and region A, by Monte Carlo inside each term's domain in log coordinates, all variants on the same points. `./harness_theta N threads term seed theta`. |
| `runs.sh` | The runs behind `logs/runs1.txt` … `runs4.txt` (about four hours on four cores), then `summarize_full.py`. |
| `summarize_full.py` | The accounting below, from the logs: `python3 summarize_full.py logs/runs*.txt`. |
| `region_a_check.py` | No grouping of region A's three primes passes the general test, so region A is the same for every variant. |

## Accounting

Li's lower bound is `1 − 2·A − C`, with `A < 0.240227` (his bound (12), which his lower bound uses as is) and `C`
the region-C loss. `C` here is the sum of the terms his final bound adds, `U_C01 + U_C03 + U_C04 + U_C05 + U_C06 + U_C07 +
U_C08 + U_C12 + U_C13`, each integrated with his `ω_1`. Two choices make it a little larger than his:

- the savings are dropped: `U_C02` is subtracted, and `U_C09 + U_C10 − U_C11` counts, once each, the part of
  `U_C08`'s set where at least one of its two further decompositions is asymptotic, so it is `≥ 0`;
- `U_C05`–`U_C07` are integrated without their `G_7`, `G_8` exclusions.

At θ = 0.520 the terms come out at `C = 0.472 ± 0.004` against Li's printed `C < 0.514`: his printed bound rounds each
term up (`U_C01`: 0.2045 → 0.21, `U_C08`: 0.2125 → 0.22, `U_C04`: 0.034 → 0.05, …), and his own trapezoid values
agree with these.

## Results

Monte Carlo standard errors in brackets, in units of the last digit (`C` for V0; the variants' differences are
computed on the same points). θ = 0.5185 combines two independent runs (V3: +0.0248 and +0.0221).

| θ | C (V0) | V0 | V1 | V2 | V3 |
|---|---|---|---|---|---|
| 0.5180 | 0.6415 (63) | −0.1220 | −0.1176 | −0.0652 (67) | −0.0170 (71) |
| 0.5182 | 0.6303 (44) | −0.1108 | −0.1069 | −0.0508 (47) | −0.0005 (49) |
| 0.5185 | 0.6063 (29) | −0.0867 | −0.0831 | −0.0234 (31) | +0.0234 (33) |
| 0.5190 | 0.5546 (31) | −0.0350 | −0.0319 | +0.0333 (33) | +0.0720 (34) |
| 0.5195 | 0.5083 (33) | +0.0113 | +0.0144 | +0.0780 (36) | +0.1143 (38) |
| 0.5200 | 0.4723 (43) | +0.0473 | +0.0497 | +0.1059 (47) | +0.1392 (48) |

The constant crosses zero at θ ≈ 0.5194 for V0 (Li's decomposition and lemmas, integrated without rounding),
0.5187 for V2 and 0.5182 for V3. V1 (Guth–Maynard only inside Li's tuples) gains almost nothing.

## The first milestone: θ = 0.52

The first complete proof in Lean aims at `θ = 0.52`, where the real-exponent Type II information (V2) leaves a margin
of `0.106` against `0.033` at `0.519`, room for a coarse certificate. Stopping Li's decomposition at four primes is
not an option: the parts of region C that it decomposes to six primes through Type I information (his sets `D*`,
`D‡`) would cost a loss of about `6.5` at four (`C4Dstop` in the experiment harness), so the certificate follows his
decomposition to depth six or eight, as the Linnik certificate does. For this milestone the theorem takes as
hypotheses Li's Lemmas 3.1 and 3.2 (Baker, Harman and Pintz's Lemmas 12 and 13, which rest on Watt's mean value
theorem) and his Lemma 4.1 (their Lemma 9, two variables near `x^{1/2}`, which the real-exponent test does not reach);
the numbers are those of arXiv:2308.04458v8.
The comparison interval is `(x − x^{1−ρ}, x]` with `ρ < 1/300`, so that the prime number theorem with the half-plane's
error term counts primes down to `x^{2θ−1}` in it (`ShortSieveLong`); the Type II estimate takes any `ρ > 0`
(`ShortSieveTypeII.abs_card_tuples_sub_le_of_pos`).

## Toward a proof in Lean

The computation is not a proof: it needs the new Type II_n lemma proved, Li's other inputs, and certified integrals.
The plan, with what is done:

1. **The real-exponent Type II_n lemma.**
   - Hölder's inequality for `n` factors with real exponents, the Type II combination, and a moment raised through a
     pointwise bound: `ShortSieveHolder` (done).
   - Moments from counts of large values: the measure of a level set from the number of `1`-separated points in it,
     and the dyadic sum over levels: `ShortSieveLevel` (done).
   - The exponent arithmetic: for `D ∈ (m, m + 1/2]` and `δ ≥ 4D − 2m`, the mean value theorem on the `m`-th power
     below `σ = 3/4` and Huxley's estimate (or the library's Halász–Montgomery count) above: `ShortSieveDreq` (done).
   - The counts for powers of a Dirichlet polynomial from the mean value theorem (`DirMean.large_values`, with
     `ZetaGMWin.pow_piece_pick` for the powers) and the library's Halász–Montgomery count
     (`ZetaKernel.power_count_pts`): `ShortSieveCount` (done).
   - Harman's moment lemma with real exponents given a pointwise bound `|L| ≤ N^{1−η}`: `ShortSieveMoment` (done).
   - The pointwise bound for the primes from the zero-free half-plane, a twisted prime number theorem
     (`ShortSieveTwist`, done), and the two together, the moment lemma for the primes with no hypothesis
     (`ShortSieveHarman`, done).
   - The Type II estimate for products of primes in boxes `x^{αⱼ}/2 ≤ Nⱼ < pⱼ ≤ Mⱼ ≤ 2Nⱼ`, one Hölder factor per
     prime: the reduction of item 2, the moments of the boxes from the heights `Nⱼ^κ` and Hölder's inequality, for
     any comparison interval `(x − x^{1−ρ}, x]`, `ρ > 0`: `ShortSieveTypeII` (done).
   - Hölder factors that are groups of boxes, uniformly over all boxes whose groups' products are at least `x^{a_i}`:
     `ShortSieveGroup` (done). The rough cofactor of a term is the monotone tuple of its prime factors
     (`ShortSieveBoxes`), so a group that holds all of them is the cofactor as one factor, as the certificate needs.
   - Still to do: Guth–Maynard's estimate in the counts (V3; V2 needs only Huxley's).
2. **Li's other arithmetic information.**
   - The reduction of sums over short intervals to mean values of Dirichlet polynomials (Baker, Harman and Pintz's
     Lemma 6), by Mellin inversion on `Re s = 1/2` with a window averaged `k` times: `ShortSieveInterval` (done).
   - His Lemma 4.1 (their Lemma 9).
   - His Lemmas 3.1 and 3.2 (their Lemmas 12 and 13) rest on Watt's mean value theorem (their Lemma 2), which rests on
     Deshouillers and Iwaniec's bounds for sums of Kloosterman sums: not in the library, and a hypothesis until it
     is.
3. **The sieve.** Buchstab's identity on families of tuples (`SieveDecomp.buchstab_fam` has the form the Linnik route
   uses), the comparison of `(x − x^θ, x]` with `(x − x^{1−ρ}, x]`, and Li's decomposition into the regions `A`, `B`
   and `C`. The main terms in the comparison interval: the prime number theorem there and the upper bound with
   Buchstab's `ω` for its rough numbers, uniformly in the cofactors, are `ShortSieveLong` (done). The asymptotic
   formula for a term (done): its tuples of primes, cut out by conditions `Σ e_j log p_j ≤ b` (the bounds of a cell,
   the order of the primes, the sizes of products), are split by the boxes of a grid of ratio `2^{1/d}`; the boxes
   inside the term get the grouped Type II estimate from a witness of the certificate, and those that straddle a
   condition lie near its boundary, which is thin in the comparison interval (`ShortSieveThin`). Together:
   `ShortSieveTerm.abs_card_cut_sub_le`, with error `O(y/log² x)`. The terms of the certificate are nodes, `k`
   primes and `m` rough items with log-linear conditions, expanded into tuples of primes (`ShortSieveExpand`,
   `ShortSieveNode`, done). Buchstab's identity and Li's role reversals are exact identities between node counts, the
   Type I term (an item free of primes below a level `x^a ∏ p_j^{−b_j}`) being the node plus its child
   (`ShortSieveBuch`, done). With Li's Lemma 4.1 as a hypothesis the terms with two grouped variables are
   asymptotic (`ShortSieveLi`, done), and with his Lemmas 3.1 and 3.2 the Type I terms at a constant level `x^ν`,
   `ν ≤ 2θ − 1` (`ShortSieveJ`, `ShortSieveTypeI`, done). A dropped term needs only an upper bound in the comparison
   interval: its rough cofactor is counted with Buchstab's `ω` there, its primes by Mertens' sums on a box, and a
   second rough item, as in the role reversals, by the reciprocals of rough numbers (`ShortSieveDrop`, done). The
   root's Type I sums, `S(A, x^{ν(0)})` and `Σ_{p₁} S(A_{p₁}, x^{ν(α₁)})` with its level varying with `p₁`, follow
   from Lemma 3.1 on blocks of `p₁` between two constant levels (`ShortSieveRoot`, done).
4. **The certificate.** Kernel-checked bounds for region A and the region-C terms at the chosen θ, with Li's
   predicates in exact arithmetic on cells, in the manner of the Linnik certificate (`SieveCert`). The terms reach
   dimension 8, so the cost of the cells is the main question.
