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
| A zero of the Davenport–Heilbronn function with `Re s > 1` (Numerical) | Known to exist since 1936; none below height 12000, by the scan here; the library's `dh` column would show that the half-plane's proof must use the Euler product. Since done for `Re s > 11/12`, in Lean, and zeros with `Re s > 1` located numerically from height `2.53·10¹²` ([§8.5](#85-the-davenportheilbronn-zeros-right-of-1112-certified-right-of-1-located)) | Finding one, then a certificate at that height: fifty times or more the existing boxes, or an approximate functional equation for `dh` | [§4](#4-the-davenportheilbronn-function-a-zero-with-re-s--1-numerical) |
| The smaller harvest: the prime number theorem in progressions uniformly in `q` with a sharp cutoff, Liouville, `μ` in progressions, Mertens with a power saving, `k`-free numbers | Exercises given the half-plane, each a statement the literature has only under RH or GRH | A module or two each | [§5](#5-the-smaller-harvest) |
| Not recommended now: the orbit-lattice conjecture, Weil positivity, the half-plane at `7/8` | | | [§6](#6-directions-looked-at-and-not-recommended-now) |
| The missing tools, by what each unlocks | | | [§7](#7-the-missing-tools-by-what-they-unlock) |
| A second scan, 9 November: what it proved, what the literature now has, and what is left of the orbit-lattice conjecture | Under RH the pivots of the orbit form grow like `log N` (`BallPivot`); the conjecture is RH up to a constant. `dh` has a zero with `Re s > 11/12`, at height `24415`, certified (`DHLocate5`) | The sampling inequality with its natural constants | [§8](#8-a-second-scan-9-november-2026) |

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

*Status, 9 November: stated elsewhere since this was written (§8.2).*

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

*Status, 9 November: the `dh` column is filled by a zero with `Re s > 11/12` at height `24415`, certified in Lean
(`PsiOmega.Locate.Z5.dh_zero_re_gt`); for `Re s > 1` the scan proposed at the end of this section cannot succeed,
but lattice reduction locates zeros there, the lowest found near height `2.53·10¹²`, numerically (§8.5).*

`dh` is a combination of two Dirichlet `L`-functions mod 5 with the functional equation of `ζ` and no Euler product.
Davenport and Heilbronn (1936) proved that it has more than `cT` zeros with `Re s > 1` and `0 < Im s ≤ T`; the
library locates four zeros in `1/2 < Re s < 1` and none in `Re s > 1`. One located there would show in Lean that the
half-plane's proof must use what `dh` lacks (`account.md`, "Within reach").

**Method.** `scripts/dh_sigma_scan.py`: `f(s) = ((1 − iκ)/2)L(s, χ) + ((1 + iκ)/2)L(s, χ̄)` (Titchmarsh §10.25, a
positive real multiple of `dh`) by Euler–Maclaurin, checked against mpmath to `10⁻¹³` and against Spira's zero
`0.808517182 + 85.699348485i`, which Newton's method reproduces to fifteen digits; then the winding number of `f`
around each window `[1, 3/2] × [t, t + 1]` (beyond `Re s = 3/2` the first coefficient dominates), and Newton's method
in each window with a nonzero winding number.

**Results.** No zero with `1 ≤ Re s ≤ 3/2` and `0 ≤ Im s ≤ 12000`: every window has winding number `0` and no phase
jump above `2.5` (so no zero sits within about `1/200` of a window's boundary either, `Re s = 1` included). This agrees
with a remark in the literature that none occurs below height `2100` (arXiv:2609.09366, found by search; not read in
full), and extends it. Davenport and Heilbronn's `cT` therefore has a small `c`: the first zero in the half-plane of
absolute convergence lies above height `12000`. The scan to `12000` took about four hours of one core; the cost per
unit height grows linearly, since the Euler–Maclaurin sum has about `t` terms.

**The certificate in Lean.** The four located zeros, at heights up to `177`, use the Euler–Maclaurin approximant
`dhEM 20 12` (a Dirichlet polynomial over `n < 100` and a twelve-term tail) with its error bound
`PsiOmega.norm_dh_sub_EM_le`. At height `t` the approximant needs about `t/(2π)` terms before the tail converges, so
at least `2000` terms at the heights above `12000` where the first such zero lies, with `log n` and the trigonometric
values of `t log n`, arguments above `10⁵`, enclosed in rationals for the kernel: fifty times or more the cost of the
existing boxes. The alternative is an approximate functional equation of Riemann–Siegel type, with about
`√(5t/2π) ≈ 100` terms a side, which would first have to be proved for `dh` with an explicit error term. Either way a
project, not a few modules, and the zero itself still has to be found: the scan should continue, in parallel over
height ranges, until one appears.

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
7. **Lagarias's criterion**, RH if and only if `σ(n) ≤ H_n + e^{H_n} log H_n` for every `n ≥ 1`: now in the library
   as `LagariasCriterion.lagarias_criterion`, deduced from Robin's theorem taken as two hypotheses, with the finite
   part `n ≤ 5040` a kernel-checked certificate ([lagarias-criterion.md](../formalisations/lagarias-criterion.md)).
   It is the one criterion in the catalogue stated inside the Euler product alone, so it has no `dh` column. What
   would make it unconditional is Robin's theorem itself: explicit bounds for `θ(x) − x` under RH and the analysis of
   the colossally abundant numbers.

## 6. Directions looked at and not recommended now

- **The orbit-lattice conjecture.** For `ζ` this is superseded by §8.3: under RH the pivot inequality holds for every
  large `k` (`BallPivot`). The conclusion of 4 November stands for the analogues: the pivot inequality fails where RH holds. Of
  the open problems in [ball-conjecture-tests.md](ball-conjecture-tests.md), a lower bound for `λ_min(G_N)` under RH,
  even `exp(−N^A)`, asks that the Dirichlet polynomial `V(s) = Σ_{n ≤ N} v_n n^s` be not small at all the low zeros at
  once. That is a sampling problem at the zeros, whose gaps, `≍ 1/log T` on average and `O(1)` in the worst case
  unconditionally, are coarser than the Nyquist spacing `π/log N` of such polynomials up to height `N`; no standard
  inequality (Turán's lemma needs sets of positive measure or nodes in progression) applies as it stands.
- **Weil positivity.** [Pull request #83](https://github.com/dickie81/number-theory/pull/83), positivity on
  Connes–Consani's subspace `V′` at every support `L ≤ log 3/2`, was merged on 4 November
  ([weil-vprime-log3.md](weil-vprime-log3.md)). The within-reach item is unchanged:
  kernel-checked certificates for `WeilForm.CertE` and `CertO`, which would make `WeilForm.weilQg_ge_both`
  unconditional to `2a ≤ 1.6`; it is compute-bound (the cost figures of [weil-positivity-l05.md](weil-positivity-l05.md)).
- **The half-plane at `7/8`.** It does not move Linnik's exponent (§3.1); what it would improve is listed in
  `account.md`, and §1 and §2 above would gain `23/24` and the constant `8` in place of `12`.
- **Linnik below `2.198` by the present method:** not possible (§3.1).

### 6.1 The `positivity-search` branch and its gravastar strand

The branch (84 commits ahead of `main`, 3 November; `docs/positivity-search.md` there) is a search for the positivity
of `ζ`'s Weil form without its zeros. Its proved part on the Weil form is on `main`: at `L = 1/2`
([weil-positivity-l05.md](weil-positivity-l05.md), pull request #81) and on Connes–Consani's subspace `V′` at
`L ≤ log 3/2` ([weil-vprime-log3.md](weil-vprime-log3.md), #83). The rest is a sequence of
constructions, each tested and each ending in a verdict; the "gravastar" ones, a tower of spheres joined at shells,
are these, with the branch's own numbers (floating point, uncertified) checked against its results files:

- **`GravastarTower` (proved).** On nested sections of the orbit Gram form the excess `ε_N = −λ_min(G_N)` is monotone,
  RH is `ε_N ≤ 0` at every level, and balance up to every `δ > 0` at infinitely many levels is already RH
  (`rh_of_frequently_balanced`, `rh_of_tendsto`). So "balanced in the limit" is exact balance: no finite certificate
  and no asymptotic argument on nested sections can accumulate into RH. This is the strand's one real theorem, and it
  is a closing one.
  It is now on `main`, re-proved in `BallRate` together with the quantitative picture around it (the explicit witness
  level of a dominant crossing, the approach `lim sup λ_N ≤ 0`, the rate under a sampling hypothesis;
  [ball-rate.md](../formalisations/ball-rate.md)).
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
  that carry 95% of the residual coupling grow from 12 to 55. Random integers below 64 and the primes below 64 behave
  like the first integers (14% left for 16 random ones, 12% for the 18 primes), so there is no arithmetic hub. The hub removes the few
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

## 8. A second scan (9 November 2026)

A second reading, asking the same question five days later. It checked the literature again, since the half-plane's
consequences are being drawn elsewhere week by week; it found one result that is the library's own, a zero of the
Davenport–Heilbronn function inside the half-plane, which it certified, and zeros of that function with real part
above `1`, which it located numerically. Prepared with AI assistance (Claude); the labels are those of the head of
this page.

### 8.1 What it added to the library

| Result | Lean | New? |
|---|---|---|
| Under RH the Gram–Schmidt pivots of the orbit form satisfy `d_N ≥ (log N/2 + log 4 + 2)/(22e⁸)`; the orbit-lattice conjecture is RH together with the pivot inequalities for `log k < 7100`; RH holds if and only if the form is at least `(log 4 + 2)/(22e⁸)` at every nonzero integer vector | `BallPivot.pivot_ge`, `BallPivot.orbitLattice_iff`, `BallPivot.rh_iff_lattice` | Yes: the conjecture and the form are this library's, and [ball-conjecture.md](ball-conjecture.md) had concluded that RH does not give the pivots |
| An imaginary quadratic field has class number one if and only if its discriminant is one of the nine | `ClassNumberOne.classNumber_eq_one_iff` | No: Baker, Heegner and Stark's theorem, and not the first kernel-checked proof without Heegner's method ([class-number-one.md](../formalisations/class-number-one.md)). It closes the "finite computation" that `ClassNumberSharp` left |
| The Davenport–Heilbronn function has a zero with `Re s > 11/12`, within `18/10000` of `0.918601 + 24415.47865i` | `PsiOmega.Locate.Z5.dh_zero_re_gt`, `PsiOmega.Locate.Z5.dh_zero_located_five` | The zero: found here, and no located zero of `dh` with real part above `0.81` is known to this scan from the literature (searched; Spira's and Balanzario and Sánchez-Ortiz's lists were not read in full). The statement closes the library's issue #35. The method is the library's certificate, with the `24 000` terms evaluated by the kernel in ball arithmetic (§8.5) |
| (Numerical) The Davenport–Heilbronn function has zeros with `Re s > 1`: fifteen located, the lowest found `1.0085585829 + 2528618752780.585033i` | None: `scripts/dh_abs_zero.py` | The zeros: no located zero of `dh` with `Re s > 1` is known to this scan from the literature. E. Bombieri and A. Ghosh's survey (2011), read after the scan, has the supremum `1.120362` of the real parts, calls such a zero "a rare event" for a neighbouring function, and exhibits zeros right of `1` only for the second Davenport–Heilbronn function (§8.5). Their existence is Davenport and Heilbronn's theorem |

The whole import cone of `ClassNumberSharp`, the half-plane's proof included (244 modules), was rebuilt from a clean
checkout on this scan's machine in about an hour on four cores, and `Eis.LFunction_ne_zero_of_re_gt` printed
`propext`, `Classical.choice` and `Quot.sound`.

### 8.2 What the literature now has

Found by search on 9 November 2026; READMEs and abstracts read, no proof or Lean checked.

- **§2 above (the Euler–Kronecker constants) is no longer unclaimed.** D. Bhattacharjee, P. Mandal and U. Bhattacharya
  (`github.com/creelie/Breakthrough-problems-3`, v4 of 2 November 2026) state `γ_m ≤ 12 log m + 36 log log m + C` and
  `γ_q ≥ −C log q · log log q` for primes `q`, from the half-plane at `11/12`.
- **Pólya–Vinogradov with `log log q`.** The same work states `M(χ) ≤ C√q log log q` for every primitive `χ` and
  `|L′/L(1, χ)| ≤ C log log q`, with a Lean check on OpenAI's `7/8`; a pull request of the same repository adds
  `|Σ_{n ≤ x} χ(n)| ≤ Ψ(x, ⌈log q⌉⁴⁰) + Cx/log q`, cancellation as soon as `log x/log log q → ∞`. This scan had derived
  the first from the library's inputs before finding it: Pólya's expansion; Montgomery and Vaughan's bound for
  exponential sums with multiplicative coefficients on the minor arcs; and on the major arcs `Σ_{h ≤ t} χψ(h)/h` equal
  to its part over the `(log q)^A`-smooth `h` up to `O((log q)^{−c})`, uniformly in `t` and in `ψ` of modulus at most
  `(log q)³`, from `ψ(x, χ) ≪ x^{11/12+η} log q` (`ChiUniform.psiChi_le_uniform`). It is not claimed here.
- **Class number one without Heegner's method** was the subject of a challenge of T. Tao (20 October 2026);
  `github.com/DrMurphyIsIn/tenth-discriminant` reports kernel-checked proofs from OpenAI's `7/8`.

So of this page's harvest, §1 (exponential sums with `μ` and `Λ` uniformly in `α`), §3 and §5 remain; what is drawn
from the half-plane alone should be expected to appear elsewhere. The library's own ground is §3, the certificates, and
the orbit form.

### 8.3 The orbit-lattice conjecture: what is left is a constant

**Theorem (Lean, under RH).** `d_N ≥ (log N/2 + log 4 + 2)/(22e⁸)` for every `N ≥ 1`.

The proof is in [ball-rate.md](../formalisations/ball-rate.md), "The pivots": the sampling theorem at `T ≍ N`
(`BallSharp.rate_slack`) bounds `Q_N(x)` below by `(Σc_n² + G(c))/(22e⁸N)`, and the top vertex `N` of the divisibility
graph of Landau's form has no children, so `Σc_n² + G(c) ≥ (log N/2 + log 4 + 2)c_N²` (`BallPivot.slack_top`).

Three things follow, in order of cost.

1. **The equivalence with RH outright (a computation, not new mathematics).** The pivot inequality `d_k ≥ d_1` is
   proved for `k ≤ 10⁴` (`scripts/ball_certificate.py`) and, under RH, for `log k ≥ 7100`. The gap is the constant
   `22e⁸`. Against the Fejér weight `sin²(πγ/2r)/γ²`, `r = ρN`, the mean of the zeros' density `log(|t|/2π)` is
   `log(ρN/12.93)`, and the same argument gives `d_k ≥ (π/(4ρ))(s + Σ_{q ∣ k}Λ(q)g/(g + Λ(q)/q))`, `g = s + 0.34`,
   from a sampling inequality with margin `s` over Landau's form. At `ρ = 120`, `s = 1/2` this is above `d_1` for
   every `k` from `5461` to `10⁶`; at `ρ = 100` from `1156` (`scripts/pivot_bound.py`, Numerical; the sum is
   `log k − O((log log k)²)`). It needs the archimedean cross terms, the region `|t| ≤ 2π` and the pole bounded with
   their natural constants, and Mertens' sum in the form `Σ_{n ≤ y}Λ(n)/n ≤ log y`.
2. **Block pivots (Theorem modulo `BallSharp.rate_slack`).** For `N ≥ 9` and `K ≤ N/(4 log N)`,
   `Σc_n² + G(c) ≥ (log N/4)·Σ_{N−K < m ≤ N}c_m²`, so under RH
   `Q_N(x) ≥ (log N/(100e⁸))·Σ_{N−K < n ≤ N}x_n²`: the top window is uniformly independent of everything below it.
   *Proof.* No two `m` of the window are parent and child. A parent `j` has at most `⌈K/j⌉` children `m = jn` in it.
   Charge `2c_m Λ(n)n^{−1/2}c_j ≤ c_j²/⌈K/j⌉ + c_m²Λ(n)²⌈K/j⌉/n`; the first terms total at most `Σ_j c_j²`, and
   `Λ(n)²⌈Kn/m⌉/n ≤ Λ(n)²(K/m + 1/n)` sums over `n ∣ m` to at most `(K/m)(log m)² + (log m)/2 ≤ (3/4)log N + 1/8`,
   which the diagonal `(log N + log 4 + 1)c_m²` covers with `(log N/4)c_m²` to spare. ∎ Not in Lean. For the whole top
   half `(N/2, N]` the charge at a parent is `Σ_{y/2 < n ≤ y}Λ(n)/n`, which tends to `log 2` and is largest at `y = 13`,
   `0.902` (for `y ≤ 2·10⁶`, Numerical): below `1`, so the same argument would give `c·log N` on the top half, given
   Mertens' sum on dyadic intervals with an explicit constant below `1`.
3. **The constant `d_1`.** The lattice exists under RH (`BallPivot.lattice_ge`); the conjecture's margin `K_H(1)` at
   the pivots below `e^{7100}` is item 1. No structure is needed for either: both are what RH says about the form.

### 8.4 Nyman–Beurling as the discrepancy of a sieve weight

A link between the library's `K_H(1) = 2 + γ − log 4π` and Báez-Duarte's distance `d_N`
([ball-conjecture.md](ball-conjecture.md), "Related work"), written out because the note there leaves it open. It may
be folklore; no source was found that states it this way.

**Identity.** Let `λ` be supported on `[1, N]`, `θ = 1 ∗ λ` and `c = Σ_k λ_k/k`. With `ρ_k(x) = {1/(kx)}` and
`χ = 1_{(0,1]}`,

```
‖χ + Σ_k λ_k ρ_k‖²_{L²(0,∞)} = c² + ∫_1^∞ (Σ_{n ≤ y} θ_n − 1 − c·y)² dy/y².
```

*Proof.* At `x = 1/y`, `Σ_k λ_k{y/k} = c·y − Σ_k λ_k⌊y/k⌋ = c·y − Σ_{n ≤ y}θ_n`, and `{y/k} = y/k` for `y < 1`. ∎

So `d_N²` is the least `L²(dy/y²)` discrepancy of a sieve weight of level `N`: of the sums of `θ_n` over `n ≤ y`
against `1 + c·y`, that is, when `λ_1 = 1`, of the sums over `2 ≤ n ≤ y` against their mean `c·y`. Burnol's bound
`d_N² ≥ (Σ_ρ m_ρ²/|ρ|² + o(1))/log N` says that no sieve weight of level `N` is equidistributed better than that.

**The primes attain it on `[1, N]`.** For `λ_k = μ(k)(1 − log k/log N)`, the weights of Bettin, Conrey and Farmer,
`θ_n = Λ(n)/log N` for `2 ≤ n ≤ N`, and beyond `N` it is Goldston and Yıldırım's truncated von Mangoldt function
`Λ_N(n) = Σ_{k ∣ n, k ≤ N}μ(k) log(N/k)` over `log N`. On `[1, N]` the integrand is `(ψ(y) − c·y·log N)²/log²N`, and
Cramér's mean square `∫_1^X (ψ(y) − y)² dy/y² ∼ (Σ_ρ m_ρ²/|ρ|²) log X` (RH) is Burnol's constant over `log N`, with
`K_H(1)` for simple zeros: the constant the two problems share is Cramér's.

**Where the hypothesis on `ζ′(ρ)` enters.** Twice, and only through Möbius sums: `c·log N − 1 = −∫_N^∞ m(t) dt/t`
with `m(t) = Σ_{k ≤ t}μ(k)/k`, which enters as `N(c log N − 1)²/log² N`; and the range `y > N`, where the discrepancy of
`Λ_N` has the mean `−½Σ_{k ≤ N}μ(k) log(N/k)` and Möbius sums with the phases `e(hy/k)`. Under RH alone these are
`√N·exp((log N)^{1/2+ε})`, not `√N`. Heuristically the zeros themselves cost nothing beyond `N`: a zero `ρ` stops
being heard in `ψ_N(y)` near `y ≈ N|γ|`, since `Σ_{m ≤ y/N} m^{−ρ} → ζ(ρ) = 0`, and the zeros above `y/N` contribute
`O(1)` in all.

**What would be new** (not attempted): `d_N² ≪ 1/log N` under RH alone. Two observations towards it, both
heuristic. A sieve weight with `Σ_k λ_k = 0`, obtained by adding `ε·ρ_K` with `K ≈ N` and
`ε = −Σ_k λ_k`, removes the mean beyond `N` at a cost `ε²/N`. And the profile matters at clusters of zeros: for a
zero of multiplicity `m` the far field of `1 − ζA` at distance `u` is of size `(u log N)^{m−1−j}` for the profile
`(1 − log k/log N)^j`, so the linear profile `j = 1` fails at a double zero and `j ≥ m` is needed; under RH alone
multiplicities are not bounded.

### 8.5 The Davenport–Heilbronn zeros: right of `11/12` certified, right of `1` located

§4 proposed to continue the scan in `Re s > 1` until a zero appears. It will not appear at a height that a blind scan
reaches. But the half-plane's `dh` column needs only `Re s > 11/12`, where zeros are within reach of a scan and of
the library's certificate; and in `Re s > 1` the count below says where to look, and lattice reduction finds them.

**How rare the zeros are (Heuristic, Numerical).** For `Re s > 1`, `dh(s) = 0` exactly when
`L(s, χ)/L(s, χ̄) = −(1 + iκ)/(1 − iκ)`, a number of modulus `1` and argument `π + 2 arctan κ`, that is `−2.588`. The
quotient is `∏_p (1 − χ̄(p)p^{−s})/(1 − χ(p)p^{−s})`, to which only the primes `p ≡ ±2 (mod 5)` contribute, each a
factor of argument at most `2 arctan p^{−σ}` in absolute value, attained when `p^{−it} = ±1` with the sign of its
class. So, by Kronecker's theorem and Rouché's, as in Davenport and Heilbronn's proof, there are zeros with real part
arbitrarily near `σ > 1` exactly when `Σ_{p ≡ ±2 (5)} 2 arctan p^{−σ} ≥ 2.588`:

- the real parts of the zeros in `Re s > 1` are dense in `(1, σ*)` and none exceeds `σ*`, with `σ* ≈ 1.1204` (primes
  to `2·10⁷` and the tail; Bombieri and Ghosh give `σ(τ₊, 1) = 1.120362`, below);
- at `σ = 1.005` the `22` primes `2, 3, 7, …, 167` of these classes, aligned exactly, are the fewest whose arguments
  reach `2.588`; at `σ = 1.05` it takes `68`.

With independent uniform phases for the primes (Bohr's model, which describes the values on a line `Re s = σ > 1/2`),
the probability that the arguments sum to `−2.588` or less is `e^{−I(σ)}` to leading order, with the large-deviation
rate

| `σ` | `0.80` | `0.85` | `0.90` | `11/12` | `0.95` | `0.97` | `0.99` | `1` | `1.005` | `1.01` | `1.02` | `1.05` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `I(σ)` | `4.5` | `6.0` | `8.6` | `9.9` | `13.6` | `17.3` | `22.9` | `27.0` | `29.5` | `32.4` | `39.9` | `94` |

(the primes to `2·10⁶`). The four located zeros below height `177` fit: one zero with `Re s > 0.8` per `200` of
height against `e^{4.5} = 89`. So zeros with `Re s > 11/12` should come about once in `e^{9.9} ≈ 2·10⁴` of height,
times a constant; and zeros with `Re s > 1` have a density of the order of `e^{−27} ≈ 2·10⁻¹²` or less, so the first
is to be expected at a height of the order of `10¹²` to `10¹⁴`, against the `12000` scanned. (Counting exact
alignments of `22` primes would give `10⁻²⁶`; the cheapest alignments are partial ones of many primes.)

**What Bombieri and Ghosh have.** E. Bombieri and A. Ghosh, *Around the Davenport–Heilbronn function*, Russian Math.
Surveys 66:2 (2011), 221–270. Its §§5, 6 and 9 were read on 10 November 2026, after the searches below were made; the
rest was not read. They treat the family `f(s, ξ) = Σ a_n n^{−s}` with `a_n = 1, ξ, −ξ, −1, 0` for
`n ≡ 1, 2, 3, 4, 0 (mod 5)`. Two real values of `ξ` give a functional equation: `τ₊ = −φ + √(1 + φ²) = 0.2841…`, `φ`
the golden ratio, which is the `κ` above and gives `dh`'s function; and `τ₋ = −φ − √(1 + φ²) = −1/τ₊`, "the second
Davenport–Heilbronn function", whose equation has the sign `−`. On the zeros right of `1` they have:

- the supremum of the real parts, by the criterion above: `σ(τ₊, 1) = 1.120362` and `σ(τ₋, 1) = 2.382286` (their §6);
- for `ξ = 0`, where the supremum is `1.0670`, a search of `1/2 ≤ σ < 1.2`, `0 ≤ t < 10⁴` by the secant method:
  `5358` zeros and none right of `1`. Their explanation is that such a zero needs the phases of at least `400` primes
  aligned, "so this should be a rare event". A search at `ξ = 0.1 + i` to height `3000` found none either;
- for `τ₋`, where the prime `2` alone exceeds the sum of arguments that is needed (`arctan(1/2) = 0.4636` against
  `0.2768`), `2479` zeros with `Re ρ ≥ 1/2` below height `10⁴`, with a concentration near `σ(τ₋, 1)`; the one of
  largest real part is `2.37474435 + 1649.8708285i`.

They report no search at `τ₊` and no zero of that function right of `1`. So the rate `I(σ)` above makes their "rare
event" quantitative for `dh`, and the fifteen zeros below are, as far as this page knows, the first located for the
classical function. What has cited the survey since 2011 was not looked at.

**The zeros right of `11/12` (Numerical).** `scripts/dh_right_scan.py` follows the argument of `f` along
`Re s = 11/12` by the approximate functional equation, `√(5t/2π)` terms a side where Euler–Maclaurin has `4t`, and
polishes each candidate by Newton's method on the exact function. To height `200000`:

| Zero | `Re s − 11/12` |
|---|---|
| `0.9186013197 + 24415.4786514i` | `+0.0019` |
| `0.9370576028 + 49688.3425744i` | `+0.0204` |
| `0.9183338056 + 74189.6447730i` | `+0.0017` |
| `0.9358236176 + 107847.3977486i` | `+0.0192` |
| `0.9248337058 + 196872.1113270i` | `+0.0082` |

Five zeros, where the count above predicts a few. The scan also flags six zeros within `0.01` to the left of the
line (near heights `43488`, `44838`, `46715`, `100469`, `116414` and `199846`). Below height `24500` the scan was
repeated with the exact function (`--exact`): the argument of `f` along the line winds once, at the first zero of
the table, so that zero is the first with `Re s > 11/12`.

**The first of them is certified (Lean).** `PsiOmega.Locate.Z5.dh_zero_re_gt`: `dh` has a zero with real part above
`11/12` ([davenport-heilbronn.md](../formalisations/davenport-heilbronn.md)). §4 expected the certificate at such a
height to cost fifty times the existing boxes or to need an approximate functional equation with a proved error. It
needs neither: the library's certificate takes any centre, and its Dirichlet polynomial, `24 000` terms at this
height, is a computation that the kernel can run. `DHBall` is the evaluator, integer arithmetic on balls, with the
proof that it encloses `n^{−c}` and the sums; the kernel runs it in about ten minutes of one core. The same files
would certify the zero at height `49688`, whose margin right of `11/12` is ten times as large, with `M = 12000`.

**Right of `1` (Numerical).** `scripts/dh_abs_zero.py` looks where the count says. The alignment wanted is
`t·log p/2π ≡ 1/2` for `p ≡ 2 (mod 5)` and `≡ 0` for `p ≡ 3 (mod 5)`, modulo 1, for the first twenty to thirty-odd
such primes, to within tolerances that grow with `p`: a closest-vector problem, which fpylll solves at once in
these dimensions. At each height found, `log(L(s, χ)/L(s, χ̄))` over the primes below `2·10⁶`, with the phases
`t·log p/2π` in exact arithmetic, and Newton's method for the value `−2.588i`. Each zero of that model is then
checked without the Euler product, by the approximate functional equation of `f` with exact phases: Newton's
method again, the value at the zero for three different splits of the sum, and the winding number round it.

| Zero | | Zero |
|---|---|---|
| `1.0085585829 + 2528618752780.585033i` | | `1.0029502487 + 9596471304522.507096i` |
| `1.0037216026 + 2582337860602.713409i` | | `1.0007985860 + 9863256896272.975492i` |
| `1.0014102322 + 3957169236029.476937i` | | `1.0137105856 + 12378817372805.348106i` |
| `1.0006712678 + 6880275255764.405114i` | | `1.0097835172 + 12726454553690.615528i` |
| `1.0009280806 + 7471572332010.195423i` | | `1.0017733639 + 13491009887731.507923i` |
| `1.0086347410 + 8811844211912.705511i` | | `1.0024898608 + 13924428708691.658590i` |
| `1.0046850258 + 9505605714798.102968i` | | `1.0029003514 + 15271050584519.775246i` |

and `1.0045596605 + 909897523359592.312141i`, the first found. For each of the fifteen: the model's zero and the
approximate functional equation's agree to `10⁻⁴`; the three splits (`λ = 1, 2, 1/2`, which share no partial sum)
agree at the zero to `7·10⁻⁷` or better, the size of the equation's error term `x^{−σ}`; and the winding number of
`f` round a circle of radius `0.003`, on which `|f| ≥ 0.0049`, is `1`. Thirteen zeros below `1.4·10¹³` is a density
of `10⁻¹²`, the count's `e^{−27}`. The search below `2.6·10¹²` was repeated with windows down to `4·10⁹` and found
no other, so the first zero in the half-plane of absolute convergence is probably the one at height
`2 528 618 752 780.585`; that is not proved, and a zero whose alignment the quadratic loss misjudges would be missed.

These are computations in floating point, not certificates. Two things would make a theorem of them:

- **One of these zeros.** The Euler–Maclaurin approximant needs about `t` terms, `10¹²`. The approximate functional
  equation needs `2√(5t/2π) ≈ 3·10⁶`, a hundred times the fifth zero's sum and within the kernel's reach with
  `DHBall`; but it would first have to be proved for `dh` with an explicit error term.
- **The existence theorem, `∃ s, dh s = 0 ∧ 1 < Re s`, at low height.** Bohr's argument in the form: choose phases
  `ψ(p)` for the primes below `750` (aligned as above) and `ψ(p) = 1` beyond; the Dirichlet series
  `g(s) = Σ a_n ψ(n) n^{−s}` is `L(s, χ)` and `L(s, χ̄)` with finitely many Euler factors changed, so it can be
  evaluated near a real point `σ₀ ≈ 1.05` with the library's Euler–Maclaurin approximants of the Hurwitz zeta
  functions (`HurwitzEM`) at height `0`, and a zero of `g` there certified as the located zeros are; Kronecker's
  theorem (the library has `BohrTorus.tendsto_mean_character`) gives
  `τ` with `p^{−iτ}` within `ε` of `ψ(p)` for every prime below `N`, so that `|f(s + iτ) − g(s)|` is at most
  `ε·log₂N·Σ_{n ≤ N} n^{−σ} + 2Σ_{n > N} n^{−σ}`, small on the disc; Rouché's theorem ends it. No prime number
  theory is needed, and no large height. This is a formalisation of a few modules, not attempted here.

**The second function: a zero right of `1`, certified (Lean; 10 November).** The combination with the other sign,
`dh2 = (1 − ε')L(s, χ₅) + (1 − ε)L(s, χ₅⁻¹)`, has the functional equation with the sign `−`, and coefficients
`1, τ₋, −τ₋, −1` up to a constant, `τ₋ = −1/κ`: the second Davenport–Heilbronn function of E. Bombieri and A. Ghosh
(Russian Math. Surveys 66:2 (2011)). For it the primes have to supply an argument of `2 arctan κ = 0.554`, where
`dh` needs `2.588`, and the prime `2` alone has `2 arctan(1/2) = 0.927`. So zeros right of `1` are common, and
Bombieri and Ghosh's §9 gives the one of largest real part below height `10⁴`, `2.37474435 + 1649.8708285i`.
`PsiOmega.Locate.Sec.dh2_zero_re_gt_one` proves it: `dh2` has a zero within `1/10000` of
`2.3747444 + 1649.8708285i` ([davenport-heilbronn.md](../formalisations/davenport-heilbronn.md)). Where the series
converges absolutely the approximant is the Dirichlet polynomial itself, `5000` terms here, with a bound for the
tail; the kernel's part is a sixth of one of the six files of the zero at `24415`. It is a kernel-checked zero in the
half-plane of absolute convergence, of a function with the functional equation of an `L`-function. It is not the
classical function's, whose zeros there are the numerical ones above.

### 8.6 Directions tried in this scan and set aside

- **`λ_N ≫ log N/N` for every vector.** The top-vertex argument does not reach it: the minimising vector has `x_N → 0`.
  What is missing is unchanged: an inverse theorem at the zeros below height `N` for the vectors near `δ_1`.
- **Linnik's exponent, the half-plane at `7/8`, Weil positivity past `log 2`:** as in §3 and §6; nothing found that
  changes them. A density estimate near the half-plane's edge gains nothing: by the usual accounting the
  Halász–Montgomery inequality with the Lindelöf bound on `Re s = 11/12` detects zeros only for `σ > 23/24`, where
  there are none.
- **Goldbach's exceptional set from the half-plane.** Hardy and Littlewood's argument gives `E(x) ≪ x^{2Θ−1/2+ε}`
  (`x^{1/2+ε}` under GRH, nothing for `Θ ≥ 3/4`); the half-plane removes the exceptional zeros of Montgomery and
  Vaughan's and Pintz's treatments, and what exponent that gives is not worked out here.
