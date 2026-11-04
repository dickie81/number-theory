# Where novel progress can be made: a survey (November 2026)

A reading of the library, asking where a new result is within reach and what each would cost. It complements the
frontier of [account.md](account.md), the author's own list: the directions here were checked against the Lean sources
and the notes, and against the literature wherever novelty is claimed. Labels: **Theorem (modulo the inputs)**, a
statement that follows from the library's theorems by an argument written out here and not in Lean; **Numerical**,
floating point, not certified; **Project**, formalisation of a known proof. "The half-plane" is Input 1 of the Linnik
paper, `Eis.LFunction_ne_zero_of_re_gt`: no Dirichlet `L`-function vanishes on `Re s > 11/12`. Prepared with AI
assistance (Claude); the literature positions in particular need expert review.

## Summary

| Direction | What would be new | Cost | Section |
|---|---|---|---|
| Exponential sums with `μ` and `Λ`, uniformly in `α`, with a power saving: `Σ_{n≤x} μ(n)e(nα) ≪ x^{35/36+ε}` | No unconditional power saving can exist without a zero-free half-plane for `ζ` (`α = 0` is Mertens' function); under GRH, Baker and Harman have `3/4` | Vaughan's identity and the bilinear exponential-sum bounds in Lean; the uniform major-arc inputs exist | [§1](#1-exponential-sums-over-primes-and-with-the-möbius-function) |
| The Euler–Kronecker constants of the cyclotomic fields: `−C(log q)² ≤ Σ_{χ≠χ₀} L′/L(1, χ) ≤ (12 + o(1)) log q` | Unconditionally only `O(φ(q) log q)` is known for one `q`; the shape matches Ihara's GRH bound `(2 + o(1)) log q` | A sharp-cutoff uniform prime number theorem in progressions (short); Brun–Titchmarsh for the sharper lower bound (moderate) | [§2](#2-the-eulerkronecker-constants-of-the-cyclotomic-fields) |
| The sieve programmes: Linnik at `2.199` by regeneration, a lever table for what would go lower; short intervals at `21/40`; the hybrid of the two | The hybrid, primes in `(x, x + x^θ]` in every class mod `q ≤ x^η` for `θ > 4/7`, needs density estimates that count zeros, not characters | Large | [§3](#3-the-sieve-programmes) |
| A zero of the Davenport–Heilbronn function with `Re s > 1` (Numerical) | Known to exist since 1936; the library's `dh` column would show that the half-plane's proof must use the Euler product | A certificate at height above 2000: 20–50 times the existing boxes, or an approximate functional equation for `dh` | [§4](#4-the-davenportheilbronn-function-a-zero-with-re-s--1-numerical) |
| The smaller harvest: the prime number theorem in progressions uniformly in `q` with a sharp cutoff, Liouville, `μ` in progressions, Mertens with a power saving, `k`-free numbers | Exercises given the half-plane, each a statement the literature has only under RH or GRH | A module or two each | [§5](#5-the-smaller-harvest) |
| Not recommended now: the orbit-lattice conjecture, Weil positivity, the half-plane at `7/8` | | | [§6](#6-directions-looked-at-and-not-recommended-now) |
| The missing tools, by what each unlocks | | | [§7](#7-the-missing-tools-by-what-they-unlock) |

The genuinely new mathematics of the library is where the author already is: the sieve certificates (§3). The inputs'
harvest is mostly taken (`account.md`, "The results"); what is left of it needs one of two tools, Vaughan's identity
(§1) or density estimates that count zeros (§3.3), and §2 is the one unclaimed consequence found that needs neither.

## 1. Exponential sums over primes and with the Möbius function

**Theorem A (modulo the half-plane).** For every `ε > 0`, uniformly in `α ∈ ℝ`,

```
Σ_{n ≤ x} μ(n) e(nα) ≪_ε x^{35/36 + ε}.
```

For `Λ`: if `α = a/q + β` with `(a, q) = 1`, `q ≤ x^{1/18}` and `|β| ≤ x^{−17/18}/q`, then
`Σ_{n ≤ x} Λ(n) e(nα) = (μ(q)/φ(q)) Σ_{n ≤ x} e(nβ) + O(x^{35/36+ε})`, and `Σ_{n ≤ x} Λ(n) e(nα) ≪ x^{35/36+ε}` for
every other `α`.

**Why it is new.** At `α = 0` the first bound is `M(x) ≪ x^{35/36+ε}`, and `M(x) ≪ x^{1−δ}` gives `ζ(s) ≠ 0` on
`Re s > 1 − δ` (`MertensExponent.zeta_ne_zero_of_mertens_isBigO`). So a power saving uniform in `α` is at least as
strong as a zero-free half-plane for `ζ`, and none is known: Davenport's theorem (1937) is `x(log x)^{−A}`. Under GRH,
Baker and Harman proved `x^{3/4+ε}` (J. London Math. Soc. 43 (1991), 193–198). The exponent `35/36` is what the
simplest dissection gives from `11/12`; with a half-plane `Re s > θ` the same argument gives `1 − (1 − θ)/3`, so `23/24`
from OpenAI's main preprint's `7/8` and `5/6` from GRH, short of Baker and Harman, whose tools are sharper.

**Proof.** Dirichlet's approximation with `Q = x^{1−c}`: `α = a/q + β` with `(a, q) = 1`, `q ≤ Q`, `|β| ≤ 1/(qQ)`.

*Minor arcs, `x^c < q ≤ Q`.* Vaughan's identity gives, for `|α − a/q| ≤ q^{−2}`,
`Σ_{n ≤ x} f(n) e(nα) ≪ (xq^{−1/2} + x^{4/5} + x^{1/2}q^{1/2})(log x)^4` for `f = Λ` (Vaughan, C. R. Acad. Sci. Paris
285 (1977)) and for `f = μ` (the same argument; Davenport's theorem is its corollary). For `c ≤ 2/5` this is
`≪ x^{1−c/2+ε}`.

*Major arcs, `q ≤ x^c`.* For `(n, q) = 1`, `e(an/q) = φ(q)^{−1} Σ_{χ mod q} χ̄(a) τ(χ) χ̄(n)`, so

```
Σ_{n ≤ y, (n,q)=1} Λ(n) e(an/q) = (μ(q)/φ(q)) ψ(y) + φ(q)^{−1} Σ_{χ ≠ χ₀} χ̄(a) τ(χ) ψ(y, χ) + O(log q · log y),
```

and with `|τ(χ)| = √q` and the uniform bound `ψ(y, χ) ≪ y^{11/12+ε} q^ε` (§5.1) the right side is
`(μ(q)/φ(q)) y + O(q^{1/2+ε} y^{11/12+ε})`. For `μ`, the terms with `(n, q) = d > 1` are the same sums at the modulus
`q/d` with the extra condition `(n, d) = 1`, and the identity
`Σ_{(n,q)=1} μ(n)χ(n)n^{−s} = L(s, χ)^{−1} ∏_{p ∣ q} (1 − χ(p)p^{−s})^{−1}` writes each as a short combination of the
sums that `MertensChi.norm_sum_le` bounds by `y^{11/12+ε} q^ε`, uniformly in `q`; so
`Σ_{n ≤ y} μ(n) e(an/q) ≪ q^{1/2+ε} y^{11/12+ε}`. Partial summation in `e(nβ)` costs the factor `1 + 2π|β|x ≤ 7x^c/q`,
and `(x^c/q) q^{1/2} ≤ x^c`, so the major arcs cost `≪ x^{11/12 + c + ε}`. The two bounds balance at `c = 1/18`. ∎

**In Lean.** Present: the uniform major-arc inputs, `MertensChi.norm_sum_le` and `ChiUniform.psiChi_le_uniform` (both
uniform in `q`, §5.1), and the Lindelöf and log-derivative bounds of `LinnikLindelof`. Missing: Vaughan's identity; the bound `Σ_{d ≤ D} min(x/d, ‖dα‖^{−1}) ≪ (x/q + D + q) log(2xq)` and
its bilinear form by Cauchy–Schwarz; Dirichlet's approximation and the Gauss-sum expansion of `e(an/q)` (Mathlib has
Dirichlet's theorem on approximation and Gauss sums). Nothing in it uses the sieve or the density estimates, so it is
a self-contained project of a few thousand lines. What it also buys: the ternary Goldbach problem with a power-saving
error term, `r₃(n) = S(n)n²/2 + O(n^{2−δ})`, since the same major arcs give its main term and the minor arcs are
Vaughan's (the singular series is extra work); and quantitative Möbius disjointness for rotations of the circle.

## 2. The Euler–Kronecker constants of the cyclotomic fields

**Theorem B (modulo the half-plane).** For `q ≥ 3`, with `χ₀` the trivial character mod `q`,

```
−C (log q)² ≤ Σ_{χ mod q, χ ≠ χ₀} L′/L(1, χ) ≤ (12 + o(1)) log q,
```

and the lower bound improves to `−C log q · log log q` given the Brun–Titchmarsh inequality
`π(y; q, a) ≤ 2y/(φ(q) log(y/q))` for `y > q` (Montgomery and Vaughan, Mathematika 20 (1973); unconditional, not in the
library). For prime `q` the sum is `γ_q − γ`, where `γ_q` is the Euler–Kronecker constant of `ℚ(ζ_q)`, since
`ζ_{ℚ(ζ_q)} = ζ ∏_{χ ≠ χ₀} L(s, χ)`; for composite `q` the imprimitive Euler factors change the sum by `O(log q)` (an
estimate of `Σ_{p ∣ q} log p · Σ_{χ: p ∤ f_χ} χ*(p)/(p − χ*(p))`, not checked in detail).

**Why it is new.** Under GRH for the Dirichlet `L`-functions, Ihara proved the one-sided bound `γ_q ≤ (2 + o(1)) log q`
(Ford, Luca and Moree, Math. Comp. 83 (2014), quote it so, from Ihara's paper in the Drinfeld volume, 2006), and
conjectured `(1/2 − ε) log q < γ_q < (3/2 + ε) log q` for large `q`; a two-sided GRH bound `|γ_q| ≪ (log q)²`, improved
by Badzyan to `|γ_q| ≪ log q · log log q`, is reported in the introduction of a recent paper found by search, whose
original sources were not read. Unconditionally, Fouvry proved `(1/Q) Σ_{Q < q ≤ 2Q} γ_q = log Q + O(log log Q)`
(J. Number Theory 133 (2013)), an average; for one `q` only `O(log |d_K|) = O(φ(q) log q)` is known (Dixit, for fields
without a Siegel zero, as reported in a survey by Murty; not read in the original). With a half-plane `Re s > θ` the constant
`12 = 1/(1 − 11/12)` becomes `1/(1 − θ)`, which is Ihara's `2` at `θ = 1/2`: the argument below is the one his bound
expresses, with the half-plane in place of GRH.

**Proof.** For `χ ≠ χ₀`, partial summation from `ψ(y, χ) ≪ y^{11/12+ε} q^ε` (§5.1) gives
`Σ_{n ≤ x} χ(n)Λ(n)/n = −L′/L(1, χ) + O(x^{−1/12+ε} q^ε)`, the series converging to the value by Abel's theorem.
Summing over `χ ≠ χ₀` with `Σ_{χ ≠ χ₀} χ(n) = φ(q)·𝟙[n ≡ 1 (q)] − 𝟙[(n, q) = 1]`:

```
Σ_{χ ≠ χ₀} L′/L(1, χ) = Σ_{n ≤ x, (n,q)=1} Λ(n)/n − φ(q) Σ_{n ≤ x, n ≡ 1 (q)} Λ(n)/n + O(φ(q) x^{−1/12+ε} q^ε).
```

Take `x = q^{12+δ}`, so that the error is `o(1)`. The first sum is `(12 + δ) log q + O(log log q)`, by Mertens and
`Σ_{p ∣ q} log p/(p − 1) ≪ log log q`. In the second, the uniform prime number theorem in progressions
`ψ(y; q, 1) = y/φ(q) + O(y^{11/12+ε} q^ε)` (§5.1) gives, for the part `y₀ = q^{12+δ/2} < n ≤ x`, the value
`(δ/2) log q/φ(q) + o(1/φ(q))`, and the part `n ≤ y₀` is nonnegative. So the sum is at most
`(12 + δ/2) log q + O(log log q)`, which is the upper bound as `δ → 0`. For the lower bound, the part `n ≤ y₀` is at
most `(log y₀) Σ_{k ≤ y₀/q} 1/(kq) ≪ (log q)²/q` trivially; with Brun–Titchmarsh and partial summation it is at most
`(2 log q/φ(q)) ∫_{1 + log 2/log q}^{12 + δ/2} u/(u − 1) du ≪ log q · log log q/φ(q)`, over `t = q^u` from `t = 2q`
(the single term `n = q + 1` costs `log q/q`). ∎

**In Lean.** Present: the half-plane; `ψ(x, χ)` uniform in `q` (`ChiUniform.psiChi_le_uniform`, §5.1); Mertens'
product bound (`SieveLeaf.prod_T_le`). Missing: the uniform prime number theorem in progressions as one statement
(§5.1); `L′/L(1, χ)` as the limit of the partial sums (Abel's theorem for the Dirichlet series at `s = 1`, with
Mathlib's `LSeries`); and, for the `log log q` lower bound, Brun–Titchmarsh, which the fundamental lemma in product form
(`SieveBrun.fundamental`) would give with level `(x/q)^{1/2}` and a bounded truncation, with a weaker constant.

## 3. The sieve programmes

### 3.1 Linnik's exponent: the lever table

Section 2.2 of the paper: with a density curve whose largest exponent is `A`, the Type II window exists exactly when
`L > 1 + A/2`, and the certificate needs between `0.03` and `0.04` above the threshold (paper §8, supplement §S6). So
the exponent each input would reach is:

| Input (its largest exponent `A`) | `A` | `1 + A/2` | Exponent reached |
|---|---|---|---|
| Chen, Gupta and Li's `4/(1 + σ)` at `σ = 5/7`, the library today | `7/3 = 2.3333` | `13/6 = 2.1667` | `2.198`–`2.2` (computed: `2.199` passes, `2.198` fails) |
| A hybrid large-values estimate of Guth–Maynard strength at `σ = 5/7`, `15/(3 + 5σ)` (the `gm` variant of `tools/linnik/density_payoff.py`) | `105/46 = 2.2826` | `2.1413` | about `2.17`–`2.18` |
| Guth and Maynard's `30/13` as a cap everywhere | `2.3077` | `2.1538` | about `2.18`–`2.19` |
| The classical `12/5` at `σ = 3/4` (no Chen–Gupta–Li) | `2.4` | `2.2` | `2.239` (computed, §S6) |
| The density hypothesis for the characters | `2` | `2` | about `2.03`–`2.04` |

Nothing known and unformalised lowers the peak: Heath-Brown's exponent `2` on `[15/19, 1]` and the Weyl bound
(`LinnikWeyl.PYWeyl`) act above `5/6` only, and the half-plane at `7/8` does not reach the corners at `5/7` (§S6). So
every exponent below about `2.17` needs new mathematics on the large values of Dirichlet polynomials over the
characters near `σ = 5/7`, where Chen, Gupta and Li call the needed cancellation "quite difficult" (their Remark 12.3).
The next exponent that is reachable is `2.199`, by regeneration with `tools/linnik/` and a kernel check of the new
certificate: a computation of hours, not a theorem yet.

### 3.2 Short intervals

The milestone `θ = 21/40` (`ShortSieveThree.primes_of_cells`, with the 204 per-cell certificate modules) is the active
project, and what remains is a set of cell certificates whose losses total below `1` (`tools/short/README.md`). The
Monte Carlo computation says the method keeps Li's constant positive down to `θ ≈ 0.5182`, below Li's `0.52`; a Lean
proof there would be below the literature, resting on the half-plane.

### 3.3 The hybrid: primes in short intervals in every progression

What the two programmes would give together: for `θ > 4/7 + η` and `q ≤ x^{η'}`, every `(x, x + x^θ]` holds a prime
`≡ a (mod q)` for each `(a, q) = 1`, from the Linnik curve's peak `7/3` through `θ > 1 − 1/A`. The obstacle is in the
form of the library's estimates: they count characters with a zero (`Linnik.CharDensity`), which Linnik's deduction can
afford, since its height `T` is `x^ε`, and a short-interval argument cannot, since its height is `x^{1−θ}` and a factor
`T` is lost in passing from characters to zeros. So this needs the zero-counting forms
`Σ_χ N(σ, T, χ) ≪ (qT)^{A(1−σ)} (log qT)^B`, that is the detectors of `LinnikDetect` and the Ingham, Huxley and
Chen–Gupta–Li steps redone with well-spaced zeros, and the explicit formula for `L(s, χ)` with the box test functions of
`ShortWeil`. Where `4/7` would stand against the literature is not settled: Kumchev (Quart. J. Math. 53 (2002)) treats
the joint distribution in progressions and short intervals by sieve methods, which stop short of `0.525` for want of
an analogue of Watt's theorem for `L`-functions, so his exponents for small `q` are likely below `4/7`, while the
uniformity in `q` here would come from the half-plane. Medium value, large cost.

## 4. The Davenport–Heilbronn function: a zero with `Re s > 1` (Numerical)

`dh` is a combination of two Dirichlet `L`-functions mod 5 with the functional equation of `ζ` and no Euler product.
Davenport and Heilbronn (1936) proved that it has more than `cT` zeros with `Re s > 1` and `0 < Im s ≤ T`; the
library locates four zeros in `1/2 < Re s < 1` and none in `Re s > 1`. One located there would show in Lean that the
half-plane's proof must use what `dh` lacks (`account.md`, "Within reach").

**Method.** `scripts/dh_sigma_scan.py`: `f(s) = ((1 − iκ)/2)L(s, χ) + ((1 + iκ)/2)L(s, χ̄)` (Titchmarsh §10.25, a
positive real multiple of `dh`) by Euler–Maclaurin, checked against mpmath to `10⁻¹³` and against Spira's zero
`0.808517182 + 85.699348485i`, which Newton's method reproduces to fifteen digits; then the winding number of `f`
around each window `[1, 3/2] × [t, t + 1]` (beyond `Re s = 3/2` the first coefficient dominates), and Newton's method
in each window with a nonzero winding number.

**Results.** No zero with `1 ≤ Re s ≤ 3/2` and `0 ≤ Im s ≤ 3000`: every window has winding number `0` and no phase
jump above `2.5` (so no zero sits near a window's boundary either). This agrees with a remark in the literature that none
occurs below height `2100` (arXiv:2609.09366, found by search; not read in full). The scan of `3000 ≤ Im s ≤ 7500` was
still running when this page was written; its outcome will be added here.

**The certificate in Lean.** The four located zeros, at heights up to `177`, use the Euler–Maclaurin approximant
`dhEM 20 12` (a Dirichlet polynomial over `n < 100` and a twelve-term tail) with its error bound
`PsiOmega.norm_dh_sub_EM_le`. At height `t` the approximant needs about `t/(2π)` terms before the tail converges, so
`N ≈ 1000`–`2000` at the heights found, with `log n` and the trigonometric values of `t log n`, arguments up to
`5·10⁴`, enclosed in rationals for the kernel: twenty to fifty times the cost of the existing boxes. The alternative is
an approximate functional equation of Riemann–Siegel type, with about `√(5t/2π) ≈ 40`–`70` terms a side, which would
first have to be proved for `dh` with an explicit error term. Either way a project, not a few modules.

## 5. The smaller harvest

Each is a module or two, and none is progress in the field: given the half-plane each is an exercise, and each is a
statement the literature has only under RH or GRH, or without a power saving. They are listed because they are cheap
and the inventory would carry them.

1. **The prime number theorem in progressions, uniformly in the modulus:**
   `ψ(x; q, a) = x/φ(q) + O(x^{11/12+η} log(q + 2))` for every `q` and `(a, q) = 1`, with the constant depending on
   `η` only. The character side is already there: `ChiUniform.psiChi_le_uniform` gives
   `|ψ(x, χ)| ≤ C log(q + 2) x^{11/12+η}` for every `χ ≠ 1` mod every `q` (its module header says "quadratic", a
   stale line; the theorem is general). What is left is orthogonality with `HalfPlanePNT.psi_isBigO_eleven_twelfths`
   for the trivial character, as in `PNTProgressions.psiAP_isBigO`, keeping the constant. Consequence: an asymptotic in
   every progression for `q ≤ x^{1/12−η}`, where Siegel–Walfisz allows `q ≤ (log x)^B`, and the Brun–Titchmarsh
   asymptotic in that range. §1 and §2 use it.
2. **Liouville's function:** `Σ_{n ≤ x} λ(n) ≪ x^{11/12+η}`, and `≪ x^{Θ+η}`: `MertensChi.norm_sum_le_of` with
   `F = ζ(2s)/ζ(s)` and `HalfPlaneLindelof.zeta_bound_eleven_twelfths`; `MertensOmega` has the converse direction and
   the identity `L(λ, s)ζ(s) = ζ(2s)`.
3. **Möbius in progressions:** `Σ_{n ≤ x, n ≡ a (q)} μ(n) ≪ x^{11/12+η} q^η` uniformly, from `MertensChi.norm_sum_le`
   and the coprimality identity of §1: a level of distribution `1/12` for `μ`, pointwise, where without GRH only the
   range `q ≤ (log x)^B` is known.
4. **Mertens' theorems with a power saving:** `Σ_{n ≤ x} Λ(n)/n = log x − γ + O(x^{−1/12+η})` and
   `Σ_{p ≤ x} 1/p = log log x + M + O(x^{−1/12+η})`, by partial summation from
   `HalfPlanePNT.psi_isBigO_eleven_twelfths`.
5. **`k`-free numbers:** `Q_k(x) = x/ζ(k) + O(x^{1/(k+1−Θ)+η})`, the argument of `SquarefreeCount` with `d^k` in
   place of `d²`.
6. **Pell's equation** and **`p = x² + 27y²`**: already in `account.md`'s within-reach list.

## 6. Directions looked at and not recommended now

- **The orbit-lattice conjecture.** The conclusion of 4 November stands: the pivot inequality fails where RH holds. Of
  the open problems in [ball-conjecture-tests.md](ball-conjecture-tests.md), a lower bound for `λ_min(G_N)` under RH,
  even `exp(−N^A)`, asks that the Dirichlet polynomial `V(s) = Σ_{n ≤ N} v_n n^s` be not small at all the low zeros at
  once. That is a sampling problem at the zeros, whose gaps, `≍ 1/log T` on average and `O(1)` in the worst case
  unconditionally, are coarser than the Nyquist spacing `π/log N` of such polynomials up to height `N`; no standard
  inequality (Turán's lemma needs sets of positive measure or nodes in progression) applies as it stands.
- **Weil positivity.** [Pull request #83](https://github.com/dickie81/number-theory/pull/83), positivity on
  Connes–Consani's subspace `V′` at every support `L ≤ log 3/2`, is in review. The within-reach item is unchanged:
  kernel-checked certificates for `WeilForm.CertE` and `CertO`, which would make `WeilForm.weilQg_ge_both`
  unconditional to `2a ≤ 1.6`; it is compute-bound (the cost figures of [weil-positivity-l05.md](weil-positivity-l05.md)).
- **The half-plane at `7/8`.** It does not move Linnik's exponent (§3.1); what it would improve is listed in
  `account.md`, and §1 and §2 above would gain `23/24` and the constant `8` in place of `12`.
- **Linnik below `2.198` by the present method:** not possible (§3.1).

### 6.1 The `positivity-search` branch and its gravastar strand

The branch (84 commits ahead of `main`, 3 November; `docs/positivity-search.md` there) is a search for the positivity
of `ζ`'s Weil form without its zeros. Its proved part on the Weil form at `L = 1/2` is on `main`
([weil-positivity-l05.md](weil-positivity-l05.md), pull request #81) and continues in #83. The rest is a sequence of
constructions, each tested and each ending in a verdict; the "gravastar" ones, a tower of spheres joined at shells,
are these, with the branch's own numbers (floating point, uncertified) checked against its results files:

- **`GravastarTower` (proved).** On nested sections of the orbit Gram form the excess `ε_N = −λ_min(G_N)` is monotone,
  RH is `ε_N ≤ 0` at every level, and balance up to every `δ > 0` at infinitely many levels is already RH
  (`rh_of_frequently_balanced`, `rh_of_tendsto`). So "balanced in the limit" is exact balance: no finite certificate
  and no asymptotic argument on nested sections can accumulate into RH. This is the strand's one real theorem, and it
  is a closing one.
- **`GravastarMargin` (proved) with `scripts/positivity/gravastar_margin.py`.** A nonnegative margin at every level is
  RH; a failure, once present, persists up the tower. Numerically the junction margin `1 − ‖A^{−1/2}BC^{−1/2}‖` between
  the top two dyadic blocks decays like `M^{−1.66}` and the global `λ_min` like `M^{−0.87}`, against `M^{−1}` for the
  arithmetic-free kernel `e^{−|u|/2}`. Moving the first zero off the line to `1/2 ± δ ± 14.13i` turns the margin negative
  from `M ≈ 1023, 4095, 8191` for `δ = 0.05, 0.02, 0.01`, so the margin detects an off-line zero of size `δ` from
  `M ≈ 80/δ` on: a detector whose reach is far behind direct computation of the zeros, and no proof.
- **The junction is the zeros.** The cross terms between dyadic blocks have no low-rank structure (about twelve
  directions for 95%, independent of size), are exactly scale invariant in the log variable (the limit kernel
  `B_∞(u, v)` has singular values `0.024, 0.021, 0.007, …`), and their leading directions are fitted by `n^{±iγ}` with
  `γ` near `14.1` and `21.0`. Weighting the shells by sphere areas is a congruence, which changes nothing, and any
  asymmetric weighting breaks positivity. The de Sitter and junction-sphere forms are RH restated
  (`DeSitterTower.rh_iff_deSitter`, `JunctionSphere.rh_iff_remainder`), and the only outer-product decomposition of the
  limit kernel is Bochner's sum over the zeros (`OuterLimit`).
- **The physical towers.** Truncated modular cusps joined by lossless Fresnel junctions (`leaky_tower.py`) have a real
  cavity spectrum whose distance to `γ_n` and `γ_n/2` is at the random baseline, like random junctions; the zeros sit at
  the poles `ρ/2` of the scattering matrix, off the unitary line, and closing the system does not move them.
  Tangherlini black holes in `D = 4…40` dimensions (`bh_tower.py`) and the shell sequences `κ_D`, `T_H`, `|S^{D−2}|`
  fit the first zeros worse than the arithmetic-free control `k/log k`, and have picket-fence spacings against the
  zeros' GUE repulsion. Closed geodesics of the modular surface as BTZ horizons carry class numbers and Pell units, but
  their lengths are `2 arccosh(t/2)`, never `log p`, and the primes reach `ζ` through Hecke eigenvalues, not lengths.
  The Li-coefficient split into a "sphere part" `−log V_s` and a "radiation part" is exact and shows `λ_n > 0` to
  `n = 1000`, which, as the branch notes, cannot see a zero off the line below height `3·10¹²`.
- **The verdict**, the branch's and mine after reading the numbers: every gravastar construction either restates RH
  or produces a spectrum with none of `ζ`'s structure, and the branch's literature survey finds no established physical
  principle that implies Weil or Li positivity. The strand is closed as a route; what it leaves are two handles the
  branch itself names, the cancellation of the prime phases `t·log p` (Zhu's barrier) and Connes–van Suijlekom's
  simple even ground state at every scale, the second of which is what #81 and #83 pursue.
- **One junction shared by all the shells** (`scripts/hub_junction.py`, uncertified numerics; `N = 2047`, shells
  `[64, 127]` to `[1024, 2047]`). The next form of the idea: a hub `H` of indices through which all the coupling
  passes. Conditioning on it, the Schur complement `G_SS − G_SH G_HH⁻¹ G_HS`, is the form on the complement of the
  hub's vectors, and the shells would decouple if the hub carried the junction. By energy they nearly do: the off-shell
  energy left is 44%, 20% and 2% for hubs of the first 8, 16 and 63 integers. By positivity they do not: the
  contraction norms of adjacent shells move from `0.990`–`1.000` only to `0.868`–`0.995` at 63, and the directions
  that carry 95% of the residual coupling grow from 12 to 55. Random integers below 64 and the smallest primes behave
  like the first integers (14% and 15% left for 16 of them), so there is no arithmetic hub. The hub removes the few
  heavy zero directions and leaves a longer tail: the shared junction is `ℓ²` of all the zeros, the Hilbert–Pólya space
  of `BallLattice.rh_iff_realization`, which exists exactly under RH. In the finite-field case the shared junction is
  the Néron–Severi lattice of `C × C`, of finite rank `2g`; for `ζ` it is infinite-dimensional, the point that
  `WeilHodge` isolates as the single missing input.
- **Worth keeping from the branch**, as reformulations for the criteria catalogue if the author wants them on `main`:
  `BallPole` (RH as the Hodge index statement on the pole complement, with the hyperbolic pole plane),
  `HodgeAxioms` (which of the three axioms of the Hodge index theorem Weil's form satisfies: the ample one yes, the
  Riemann–Roch dichotomy no, unconditionally), `WeilHodge` (Hodge index gives the Weil bound for curves, with the
  intersection numbers as hypotheses), `SmithLattice` and `Redheffer` (`M(n)²` as a covolume ratio of two integral
  positive lattices) and `KreinNeutral`. None is a lead; each says precisely which single input is missing.

## 7. The missing tools, by what they unlock

1. **Vaughan's identity with the bilinear exponential-sum bounds:** §1, the ternary Goldbach problem with a
   power-saving error term, quantitative Möbius disjointness; the smallest of the five.
2. **Density estimates for the characters that count zeros:** §3.3, and the Type II information of a sieve for primes
   in short intervals in progressions.
3. **Brun–Titchmarsh:** the `log log q` of §2, and an upper-bound sieve for both programmes; from
   `SieveBrun.fundamental` with a weaker constant.
4. **The large sieve over all moduli `q ≤ Q`:** Bombieri–Vinogradov, the Titchmarsh divisor problem, Chen's theorem;
   the largest.
5. **`ζ_K = ∏_χ L(s, χ)` for abelian `K`, through Kronecker–Weber:** effective Chebotarev for every abelian extension
   of `ℚ` (the library has the cyclotomic case, `CyclotomicFrobenius`), effective class numbers of cyclotomic fields,
   and §2 stated for the field itself.
