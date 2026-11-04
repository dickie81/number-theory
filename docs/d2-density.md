# The density of real characters with d₂ < d₁

Status labels: **Lean** (machine-checked in `scratch/d2density/` and `lib/pnt/`, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound` only), **Written proof**, **Numerical**, **Conjecture**. Prepared with AI assistance; needs expert review.

## Statement

Let χ_D be the real primitive character of a fundamental discriminant D, a = 0 if D > 0 and a = 1 if D < 0, and
ℓ_D = L′/L(1, χ_D). Let d₁, d₂ be the first two pivots of the orbit Gram matrix (see `ball-conjecture.md`; Theorem B
in `ball-conjecture-tests.md` §2). By §5.1 there, for real χ with q ≤ 10⁴ the pivot d₂ alone decides the whole conjecture
(d_k ≥ d₁ for all k ≤ 300). So, in that range, the density below is also the density of real characters violating it.

1. **(Lean, given Theorem B and K₁ > 0)** d₂ ≥ d₁ ⇔ −2K₁ − 2c_a ≤ ℓ_D ≤ −2c_a, with c₀ = −¼ log(27/4) and
   c₁ = ¾ log(3/4). So the upper thresholds are ½ log(27/4) = 0.954771… (even) and (3/2) log(4/3) = 0.431523… (odd).
   (`D2Criterion.criterion`, `c0_closed`, `c1_closed`; the identification of c_a with the archimedean constant of Theorem B: `CAClosed.cA_zero`, `CAClosed.cA_one`.)
2. **(Lean)** K₁ = Σ_ρ 1/(ρ(1−ρ)) > 0 for any summable such sum over a nonempty set of zeros in the open strip (`D2Density.K1_pos`).
3. **(Written proof, unconditional; Lean, conditional on the half-plane input)** For each sign,
   #{D ∈ F±(x) : d₂ < d₁}/|F±(x)| → P(X > t_a), where X is Lamzouri's random model −Σ_p (log p) X(p)/(p − X(p)).
   The averaged limit is ½(0.051123 + 0.160911) = **0.10602** (numerical inversion of the characteristic function; not certified).
   - The written proof below is unconditional.
   - In Lean, `D2Hdist.d2_density_pos` and `d2_density_neg` apply `D2Density.d2_density_log` with `hdist` discharged.
   - `hdist` comes from `D2Dist.dist_pos` and `dist_neg`. These use the zero-free half-plane Re s > 11/12 (`Eis.LFunction_ne_zero_of_re_gt`; see `formalisations/openai-half-plane.md`).
   - That half-plane is itself a Lean theorem here, using only the standard axioms. It formalises OpenAI's 2026 preprints, so the Lean results are labelled conditional on that input.
   - The remaining hypotheses are listed at the end.

## Written proof (per-sign distribution)

### Notation
- F(x) is the set of fundamental discriminants with |D| <= x.
- F+(x) = {D in F(x) : D > 0} and F-(x) = {D in F(x) : D < 0}.
- For D in F+(x) the character chi_D is even (a = 0); for D in F-(x) it is odd (a = 1).
- l_D = L'/L(1, chi_D), and X = -sum_p (log p) X(p)/(p - X(p)) is Lamzouri's random model (arXiv:1410.1603, Section 1).
- t0 = (1/2) log(27/4) and t1 = (3/2) log(4/3).

### Theorem
For a = 0 (sign +) and a = 1 (sign -):
  #{D in F±(x) : d2(chi_D) < d1(chi_D)} / |F±(x)|  ->  P(X > t_a).
Hence over all real primitive characters with conductor <= x, the proportion with d2 < d1 tends to
(1/2)(P(X > t0) + P(X > t1)) = 0.10602 (numerical value, characteristic-function inversion, stable to about 1e-9).

### Inputs and their status
I1. Theorem B (repo, docs/ball-conjecture-tests.md): K(2) = sqrt2 (K1/2 + c_a + l/2). Paper proof, unconditional; Lean for good real characters (`PsiOmega.theoremB`, `lib/core/WeilChiB.lean`).
I2. K1 > 0 for real chi: Re 1/(rho(1-rho)) > 0 for every zero with 0 < beta < 1. The zero set is closed under conjugation, so K1 is a sum of positive terms.
I3. The criterion d2 >= d1 iff -2K1 - 2c_a <= l <= -2c_a, with c0 = -(1/4)log(27/4) and c1 = (3/4)log(3/4). Lean: `scratch/d2density/D2Criterion.lean`, no sorry.
I4. Moment asymptotics restricted to each sign (Lemma 1 below). This is the new step.

### Lemma 1 (signed moments)
For each fixed k >= 1,
  (1/|F±(x)|) sum_{D in F±*(x) \ E(x)} (-l_D)^k  ->  E[X^k]   (x -> infinity).
Here F±*(x) excludes Siegel-zero discriminants (O(log x) of them), and E(x) is the exceptional set of Lamzouri's Corollary 2.4 (O(x^{3/4}) elements).

Proof. Follow Lamzouri, Section 2 (Theorem 1.6), and change only the summation set.
(a) Corollary 2.4 (approximation by sum_{n<=x} Lambda_k(n) chi_D(n)/n) is a statement about each D separately, outside an exceptional set. Intersecting with one sign class only shrinks the exceptional set, so it holds verbatim.
(b) Bound (2.9), l_D << log^2|D| on F*, is pointwise, so it is unaffected. With |F±(x)| = 3x/pi^2 + O(sqrt x), the removed D cost O(x^{-1/4+o(1)}) relative to |F±(x)|.
(c) Square terms n = m^2. Lamzouri uses #{D in F(x) : (D,m) = 1} = |F(x)| prod_{p|m} p/(p+1) + O(x^{1/2+o(1)} tau(m)). The same holds for F±(x) with the same product. A fundamental D is either D = 1 mod 4 squarefree, or 4m' with m' = 2,3 mod 4 squarefree. Coprimality to odd p is a condition modulo p^2 that does not depend on sign. Each of the classes "D = 1 mod 8", "D = 5 mod 8" and "D even" has density 1/3 within each sign class: D -> -D swaps 1 mod 8 with 7 mod 8, but among negative D = 1 mod 4 squarefree the residues 1 and 5 mod 8 are again equally frequent. The standard Möbius sieve over a^2 | D gives each count with error O(x^{1/2} tau(m)), on the interval [1, x] or [-x, -1] alike.
(d) Non-square terms. Lamzouri cites Granville–Soundararajan, Lemma 4.1: sum_{D in F(x)} chi_D(n) << x^{1/2} n^{1/4} log n. Its proof writes D -> chi_D(n) as a non-principal character psi mod 4n, on the arithmetic progressions describing fundamental discriminants. It detects squarefreeness by sum_{a^2|D} mu(a), and applies Pólya–Vinogradov to psi over an interval for a <= A, with the trivial bound for a > A. Every step bounds a sum over an arbitrary interval, so it holds with the interval [1, x] or [-x, -1] in place of [-x, x]. The bound holds for F±(x) with the same shape. Lamzouri's (2.8) follows: the contribution is << x^{-1/6}.
(e) Combining (a)–(d) as in Lamzouri's proof of Theorem 1.6 gives
    sum_{m} Lambda_k(m^2)/m^2 prod_{p|m} p/(p+1) + o(1) = E[X^k],   by (2.10).   ∎

### Proof of the Theorem
1. Convention: X is the random model of l itself, X = -sum_p (log p) X(p)/(p - X(p)) = gamma_rand(X) - gamma. Lemma 1 for -l_D gives E[(-X)^k], so the moments of l_D tend to E[X^k]. By Lamzouri's Proposition 3.1, E|X|^k <= (c log k)^k, so Carleman's condition holds and the law of X is determined by its moments. By the method of moments, the empirical law of l_D on F±*(x) \ E(x) converges weakly to the law of X. The excluded set has size o(x), so the same holds on F±(x).
2. X has a continuous law. It is an a.s. convergent sum of independent discrete variables Y_p whose largest atom has probability max(1/(p+1), p/(2(p+1))) <= 1/2 + 1/(2p), and the product of these tends to 0. By Lévy's theorem on infinite convolutions, the law has no atoms. So P(-l_D-model > t) is continuous in t, and weak convergence gives #{D in F± : l_D > t_a}/|F±| -> P(X > t_a).
3. Lower failures: l_D < -(2/5)(log(|D|/pi) + psi_a + c_a). By tightness (weak convergence), for every M the proportion with l_D < -M tends to P(X < -M), which tends to 0 as M -> infinity. So the lower failures have density 0.
4. By I1–I3, d2 < d1 iff l_D > t_a or there is a lower failure. Hence the density is P(X > t_a) on F±. Since |F+(x)| ~ |F-(x)| ~ 3x/pi^2, the combined density is the average.   ∎

### Honest status
- The proof is unconditional. It is a routine but unchecked adaptation of Lamzouri's Section 2 and Granville–Soundararajan's Lemma 4.1. Lamzouri Sections 1–2 read from arXiv:1410.1603. Step (d) is now CHECKED against Granville–Soundararajan, arXiv:math/0206031 (GAFA 13 (2003) 992–1028), Lemma 4.1 (Section 4). Their proof says: "We shall confine our attention to d positive and ≡ 1 (mod 4): the cases d negative, or d ≡ 8, or 12 (mod 16) are handled similarly." So the bound is proved class by class, including each sign separately, and holds for F+(x) and F-(x) individually. The only implicit step is the authors' "handled similarly" for d < 0, which is a reflection of the interval [1, x] to [-x, -1] in Pólya–Vinogradov.
- Only fixed-k moments are needed, so Lamzouri's uniformity and saddle-point machinery is not needed. Mourtada–Murty [13] also have fixed-k moments over F(x).
- The numerical value 0.10602 is from the random model, not certified. In the data up to 1e8, the + rates reach the model. The − rates stay about 1σ high, which is unresolved. Between about 2e4 and 1e6 both signs show a transient excess. See "Numerics" and "The 2e4–1e5 excess" below.

## Numerics

Thresholds: ℓ > t_a, which is the same as d₂ < d₁ here, because no lower failure ℓ_D < −(2/5)(log(|D|/π) + ψ_a + c_a) occurs.
- The lower threshold is ≤ −3.2 only for D ≥ 1.076e5 (D > 0) and |D| ≥ 2.07e4 (D < 0). Beyond that, min ℓ ≥ −3.0 in all the data rules lower failures out.
- Below that the threshold is higher: −2.25 at D = 1e4, −2.53 at D = 2e4, and +0.79 at D = 5. So `lower.py` checks every fundamental discriminant with 1 < D ≤ 1.076e5 and every D < 0 with |D| ≤ 2.08e4 against its own threshold.
- That is 32708 D > 0 and 6316 D < 0, and there are no lower failures (`lower.json`). The minimum ℓ is −1.97 (D > 0) and −2.08 (D < 0). The closest calls are the smallest conductors: D = 8 is 0.030 above its threshold and D = −7 is 0.019 above.
- The same run reproduces the q ≤ 1e4 row, and `ball-conjecture-tests.md` §5.1 has the same counts from an independent flint scan.
Values of L′/L(1, χ_D) come from PARI `lfun` (cypari2), cross-checked against flint/arb (`emp.py`, `k2.py`) to 1e-16.

| window | + rate (n) | z | − rate (n) | z |
|---|---|---|---|---|
| q ≤ 1e4 (all) | 0.0503 (3043) | −0.2 | 0.1591 (3043) | −0.3 |
| 2e4–2.5e4 (all) | 0.0587 (1515) | +1.35 | 0.1764 (1525) | +1.65 |
| 6e4–6.4e4 (all) | 0.0699 (1216) | +2.97 | 0.1744 (1227) | +1.29 |
| 1e5–1.2e5 (all) | 0.0645 (6090) | | 0.1794 (6082) | |
| 2e5–2.1e5 (all) | 0.0582 | | 0.1748 | |
| 4e5–4.1e5 (all) | 0.0538 | | 0.1731 | |
| 1e6–1.05e6 (sample) | 0.0514 (5000) | +0.1 | 0.1670 (5000) | +1.2 |
| 1e7–1.01e7 (sample) | 0.0490 (5000) | −0.7 | 0.1646 (5000) | +0.7 |
| 1e8–1.001e8 (sample) | 0.0552 (2500) | +0.9 | 0.1668 (2500) | +0.8 |
| limit | 0.0511 | | 0.1609 | |

Counts are in `scripts/d2_density/summary.json`.

## The 2e4–1e5 excess (numerical; mechanism conjectural)


### 1. It is not an artefact
- PARI (big.py) and flint/arb (emp.py) agree on 600 overlapping D from 60k–64k to within 1.1e-16 (xchk.py).
- I recomputed [1e5,1.2e5] EXHAUSTIVELY with PARI (exh.py; 6090 D>0, 6082 D<0, all fundamental discriminants, no duplicates).
  Rates: 0.0645 (+) and 0.1794 (-), the same as the random sample (0.0653 / 0.1847). The excess is real.
- The 2-adic class mix is as expected (D mod 8 counts in the right ratios), and the signs are correct.
  Frequencies of chi_D(p)=-1 for p<=13 match p/(2(p+1)) in every window (|z|<0.3 in the exhaustive windows).
- Further exhaustive windows: [2e5,2.1e5] gives 0.0582/0.1748, and [4e5,4.1e5] gives 0.0538/0.1731.

### 2. What drives it: a skewness transient (shape), not mean or variance
Model (Lamzouri random Euler product): mean -0.438, sd 0.8635, skewness -0.077.

| window | + rate | + sd | + skew | - rate | - sd | - skew |
|---|---|---|---|---|---|---|
| q<=1e4 | 0.0503 | 0.650 | +1.07 | 0.1591 | 0.799 | +0.60 |
| 2e4–2.5e4 | 0.0587 | 0.755 | +0.73 | 0.1764 | 0.842 | +0.29 |
| 6e4–6.4e4 | 0.0699 | 0.796 | +0.56 | 0.1744 | 0.843 | +0.17 |
| 1e5–1.2e5 (exh) | 0.0645 | 0.807 | +0.44 | 0.1794 | 0.855 | +0.13 |
| 2e5–2.1e5 (exh) | 0.0582 | 0.815 | +0.34 | 0.1748 | 0.859 | +0.10 |
| 4e5–4.1e5 (exh) | 0.0538 | 0.827 | +0.25 | 0.1731 | 0.863 | +0.04 |
| 1e6 | 0.0514 | 0.838 | +0.20 | 0.1670 | 0.859 | -0.03 |
| 1e7 | 0.0490 | 0.848 | +0.05 | 0.1646 | 0.870 | -0.01 |
| 1e8 | 0.0552 | 0.861 | -0.04 | 0.1668 | 0.867 | -0.11 |
| model | 0.0511 | 0.8635 | -0.08 | 0.1609 | 0.8635 | -0.08 |

The mean is already at the model value by 1e4. Two finite-D distortions then decay at different speeds:
- sd is too small, which pushes the tail DOWN. This has mostly gone by about 4e5.
- skewness is strongly positive (a heavy right tail), which pushes the tail UP. This decays much more slowly and only reaches the model by about 1e7.
At q<=1e4 the two cancel, which is why the match there was a coincidence. As the sd recovers faster than the skew,
the net effect is an upward hump peaking around 6e4–1e5, which is gone by about 1e6. A 3-term Edgeworth fit using the empirical moments
reproduces the direction and most of the size of the hump (for example, + at 1e5: normal 0.043, Edgeworth 0.054, observed 0.0645). The rest of the gap is beyond Edgeworth's accuracy so far out in the tail.

Mechanism (supported, not proved): in the method of moments, the k-th moment of ell_D matches the model only once the
prime products p1...pk that appear in it are small compared with D (the character-sum error terms). So low moments converge first:
the mean converges first, then the variance, then the third moment. Evidence: the truncated Euler sum S_300 over the exhaustive 1e5 window already has skew +0.17
(model truncated at 300: -0.08). Its tail rate is 0.0599, against 0.0487 for the truncated model. And for D>0, S_300 is correlated with the residual (primes>300) at r=-0.38, against about 0 at 1e7.
So the joint law of {chi_D(p)} at D~1e5 is not yet the independent model, even though every single-prime marginal is correct.
This is a finite-prime effect, but not the one in trunc.py. It is not "fewer primes"; it is "primes not yet independent".

### 3. Significance
- Binomial z treats the D as iid. Exhaustive windows are deterministic, and their marginals are better than iid, so the z values are only indicative.
- Even so: there are 6 disjoint windows (1e4–4e5) on each sign, and the + excess decays monotonically, from z=+4.75 at 1e5 to +1.8 at 2e5 and +0.7 at 4e5.
  Across all 18 window-by-sign tests, Bonferroni still leaves p ~ 2e-5 for the 1e5 point alone. The skew trend runs smoothly across every window.
- The odd excess at 1e5 (z=+3.9) is also robust. The odd rates stay slightly high (z about +1) all the way to 1e8, so convergence on that side is slower or the model's 0.1609 is marginally low. This is unresolved.

### Confidence
High that the excess is genuine arithmetic, not an artefact. High that it is a shape effect (sd deficit and positive skew decaying at different rates).
Moderate on the mechanism (higher moments converging late because of character-sum error terms). That is consistent with the data and with how the method of moments works, but no error term was computed.
Files: exh.py (writes `exh_*.json`, which `st.py` reads; not committed), xchk.py, st.py, edge.py. The residual and
frequency checks above were run with scripts (`res.py`, `res2.py`, `freq.py`) that are not committed.

**Open:** the odd (D < 0) rates stay about 1σ above 0.1609 up to 1e8. Either convergence there is slower, or the
model constant is marginally off. This is unresolved.

## Remaining hypotheses of the Lean theorem

| hypothesis | content | status |
|---|---|---|
| `hdist` | per-sign weak convergence of ℓ_D to X, at every `t` | **Lean, CONDITIONAL on the half-plane** `Re s > 11/12`: `D2Hdist.hdist_pos`, `D2Hdist.hdist_neg` (moments via GS Lemma 4.1, the method of moments, no atoms `NoAtoms.ν_singleton`, the tail identity). `D2Hdist.d2_density_pos` / `D2Hdist.d2_density_neg` are `D2Density.d2_density_log` with `hdist` discharged |
| `hB` | Theorem B (closed form of K(2)) | Lean (`PsiOmega.theoremB`, `c_a` as the archimedean integral); closed form of `c_a` Lean (`CAClosed.cA_zero`, `CAClosed.cA_one`) |
| `hpos` | K₁ is the zero sum (summability) | positivity is Lean; the identification is open |

## Citations
- Y. Lamzouri, The distribution of Euler–Kronecker constants of quadratic fields, JMAA 2015, arXiv:1410.1603.
- A. Granville, K. Soundararajan, The distribution of values of L(1, χ_d), GAFA 13 (2003), arXiv:math/0206031, Lemma 4.1.
- M. Mourtada, V. K. Murty, Distribution of values of L′/L(σ, χ_D), Moscow Math. J. 15 (2015).
- Novelty: no prior statement of these thresholds or this density was found (searches, Nov 2026). The inputs are known.
