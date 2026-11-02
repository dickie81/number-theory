# The d2 < d1 density for real characters, split by the sign of D (written proof)

## Notation
- F(x) is the set of fundamental discriminants with |D| <= x.
- F+(x) = {D in F(x) : D > 0} and F-(x) = {D in F(x) : D < 0}.
- For D in F+(x) the character chi_D is even (a = 0); for D in F-(x) it is odd (a = 1).
- l_D = L'/L(1, chi_D), and X = -sum_p (log p) X(p)/(p - X(p)) is Lamzouri's random model (arXiv:1410.1603, Section 1).
- t0 = (1/2) log(27/4) and t1 = (3/2) log(4/3).

## Theorem
For a = 0 (sign +) and a = 1 (sign -):
  #{D in F±(x) : d2(chi_D) < d1(chi_D)} / |F±(x)|  ->  P(X > t_a).
Hence over all real primitive characters with conductor <= x, the proportion with d2 < d1 tends to
(1/2)(P(X > t0) + P(X > t1)) = 0.10602 (numerical value, characteristic-function inversion, stable to about 1e-9).

## Inputs and their status
I1. Theorem B (repo, docs/ball-conjecture-tests.md): K(2) = sqrt2 (K1/2 + c_a + l/2). Paper proof, unconditional.
I2. K1 > 0 for real chi: Re 1/(rho(1-rho)) > 0 for every zero with 0 < beta < 1. The zero set is closed under conjugation, so K1 is a sum of positive terms.
I3. The criterion d2 >= d1 iff -2K1 - 2c_a <= l <= -2c_a, with c0 = -(1/4)log(27/4) and c1 = (3/4)log(3/4). Lean: lean/D2Criterion.lean, no sorry.
I4. Moment asymptotics restricted to each sign (Lemma 1 below). This is the new step.

## Lemma 1 (signed moments)
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

## Proof of the Theorem
1. Convention: X is the random model of l itself, X = -sum_p (log p) X(p)/(p - X(p)) = gamma_rand(X) - gamma. Lemma 1 for -l_D gives E[(-X)^k], so the moments of l_D tend to E[X^k]. By Lamzouri's Proposition 3.1, E|X|^k <= (c log k)^k, so Carleman's condition holds and the law of X is determined by its moments. By the method of moments, the empirical law of l_D on F±*(x) \ E(x) converges weakly to the law of X. The excluded set has size o(x), so the same holds on F±(x).
2. X has a continuous law. It is an a.s. convergent sum of independent discrete variables Y_p whose largest atom has probability max(1/(p+1), p/(2(p+1))) <= 1/2 + 1/(2p), and the product of these tends to 0. By Lévy's theorem on infinite convolutions, the law has no atoms. So P(-l_D-model > t) is continuous in t, and weak convergence gives #{D in F± : l_D > t_a}/|F±| -> P(X > t_a).
3. Lower failures: l_D < -(2/5)(log(|D|/pi) + psi_a + c_a). By tightness (weak convergence), for every M the proportion with l_D < -M tends to P(X < -M), which tends to 0 as M -> infinity. So the lower failures have density 0.
4. By I1–I3, d2 < d1 iff l_D > t_a or there is a lower failure. Hence the density is P(X > t_a) on F±. Since |F+(x)| ~ |F-(x)| ~ 3x/pi^2, the combined density is the average.   ∎

## Honest status
- The proof is unconditional. It is a routine but unchecked adaptation of Lamzouri's Section 2 and Granville–Soundararajan's Lemma 4.1. Lamzouri Sections 1–2 read from arXiv:1410.1603. Step (d) is now CHECKED against Granville–Soundararajan, arXiv:math/0206031 (GAFA 13 (2003) 992–1028), Lemma 4.1 (Section 4). Their proof says: "We shall confine our attention to d positive and ≡ 1 (mod 4): the cases d negative, or d ≡ 8, or 12 (mod 16) are handled similarly." So the bound is proved class by class, including each sign separately, and holds for F+(x) and F-(x) individually. The only implicit step is the authors' "handled similarly" for d < 0, which is a reflection of the interval [1, x] to [-x, -1] in Pólya–Vinogradov.
- Only fixed-k moments are needed, so Lamzouri's uniformity and saddle-point machinery is not needed. Mourtada–Murty [13] also have fixed-k moments over F(x).
- The numerical value 0.10602 is from the random model, not certified. The finite-range data (q <= 6.4e4) do NOT yet show convergence (see NOTE_d2_density.md).
