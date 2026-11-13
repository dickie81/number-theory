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

**12 November: the paper at `43/20`, from the half-plane and Huxley's estimate.** The Linnik paper now proves
`43/20` (`Linnik21500.linnik_21500`). Its Type II estimate in two variables counts characters only from `7789/10000`
on, where Huxley's exponent is below Chen, Gupta and Li's, so its curve is now `ghx` (`SieveCurveHx`: the trivial
count below `7789/10000`, Huxley's steps above; `tools/linnik/gen_zone.py`), and the import cones of the theorems
with no window, at `2165/1000`, `2150/1000` and (since, in no paper) `2140/1000`, have no module of Chen, Gupta and
Li's paper; those at `11/5`, `219/100` and `218/100` keep their window, and with it the curve `g7d`. In the table
below the column `A` of those three rows is the window route's, which they do not use. "The paper" in the entries before this date means its version at
`11/5`.

Section 2.2 of the paper's version at `11/5`: with a density curve whose largest exponent is `A`, the Type II window
exists exactly when `L > 1 + A/2`, and the certificate needs between `0.03` and `0.04` above the threshold (that
version's §8 and §S6). So
the exponent each input would reach is:

| Input (its largest exponent `A`) | `A` | `1 + A/2` | Exponent reached |
|---|---|---|---|
| Chen, Gupta and Li's `4/(1 + σ)` at `σ = 5/7`, the window route's curve | `7/3 = 2.3333` | `13/6 = 2.1667` | `2.198`–`2.2` (computed: `2.199` passes, `2.198` fails) |
| The same, with the Type II estimate in two variables as one more way to evaluate a box (below; the estimate by bins is in Lean, the sieve with it is not) | `7/3` | `13/6` | `2.193` (computed: `2.193` passes, `2.192` fails) |
| The same inputs in a tree of Buchstab steps chosen term by term, with the window's tests and those of the estimate in two variables, and no role reversal (below; **in Lean**, the kernel searching for the tree) | `7/3` | `13/6` | **`2.19`, a theorem** (`Linnik21900.linnik_21900`) |
| The same tree with role reversal for a term of three primes that needs an upper bound, at one level (below; **in Lean**, the kernel running the search) | `7/3` | `13/6` | **`2.18`, a theorem** (`Linnik21800.linnik_21800`) |
| The same search with no Type II window: the estimate in two variables alone, and for a term with no prime of the size of its rest, the rest among the primes of the comparison's own tree (below; **in Lean**, the kernel running the search) | `7/3` | `13/6` | **`2.165`, a theorem** (`Linnik21650.linnik_21650`) |
| The same search with the reversal of a term of three or five primes through its largest prime, the cofactor kept as one number, at one level (below; **in Lean**, the kernel following the plan of the search by hints) | `7/3` | `13/6` | **`2.15`, a theorem** (`Linnik21500.linnik_21500`) |
| The same search with a term of the sign `+` reversed through its largest prime too, on cells of side `0.003`, its plan chosen by cost and by the kernel's time (below; **in Lean**, the kernel following the plan) | `7/3` | `13/6` | **`2.14`, a theorem** (`Linnik21400.linnik_21400`) |
| The same inputs in a decomposition that does not lean on the window: a floor for each term, the estimate in two variables at every depth, role reversal (below; floating point, no certificate; of what it assumes, the two estimates are in Lean as far as Harman's comparison with a rest among the term's primes) | `7/3` | `13/6` | `2.12` (computed conservatively on cells of side `0.002`: `2.12` passes, `2.11` fails); about `2.10` in the limit of fine cells |
| A hybrid large-values estimate of Guth–Maynard strength at `σ = 5/7`, `15/(3 + 5σ)` (the `gm` variant of `tools/linnik/density_payoff.py`) | `105/46 = 2.2826` | `2.1413` | about `2.17`–`2.18` |
| Guth and Maynard's `30/13` as a cap everywhere | `2.3077` | `2.1538` | about `2.18`–`2.19` |
| The classical `12/5` at `σ = 3/4` (no Chen–Gupta–Li) | `2.4` | `2.2` | `2.239` (computed, §S6) |
| The density hypothesis for the characters | `2` | `2` | about `2.03`–`2.04` |

Nothing known and unformalised lowers the peak: Heath-Brown's exponent `2` on `[15/19, 1]` and the Weyl bound
(`LinnikWeyl.PYWeyl`) act above `5/6` only, and the half-plane at `7/8` does not reach the corners at `5/7` (§S6). So
with the window as the Type II estimate, every exponent below about `2.17` needs new mathematics on the large values
of Dirichlet polynomials over the characters near `σ = 5/7`, where Chen, Gupta and Li call the needed cancellation
"quite difficult" (their Remark 12.3). The next exponent that the window route reaches is `2.199`, by regeneration with
`tools/linnik/` and a kernel check of the new certificate: a computation of hours, not a theorem yet.

**A Type II estimate in two variables (10 November; its bound by bins is in Lean, its use in the sieve is computed).**
The window needs
`L > 1 + A/2` because it bounds one polynomial against the number of characters in a bin. With two polynomials,
Cauchy–Schwarz between them needs no count of the bin: each gets orthogonality or the Halász–Montgomery inequality
in its mean-square form, with the paper's kernel bound, and the prime sums keep the paper's bound. In exponents of
`x`, at `11/5` the estimate holds for two variables within about `0.08` of each other and a rest, a product of
primes, of at most `0.164`: for example two primes near `x^{0.42}` and a third near `x^{0.16}`, which no window
covers. The region does not close at `13/6`.

- **In the paper's decomposition** (`tools/linnik/two_factor.py`). As one more way to evaluate a box of depth at
  most four, the estimate takes the certificate's total at `11/5` from `0.93214𝒦` to `0.76216𝒦` (the decomposed
  cells from `0.2149𝒦` to `0.0916𝒦`, the dropped ones from `0.7173𝒦` to `0.6706𝒦`), and the last exponent that
  passes from `2.199` to `2.193` (`0.97454𝒦` there, `1.03180𝒦` at `2.192`). It goes no further here: the
  decomposition's floor is the window's width, which tends to `0` at `13/6`, and the cells it must drop are those
  that the Type I rule does not reach. With the region that Lean proves in place of the sampled one, tested in
  exact integers on the rectangle of the two parts' exponents as the Lean lemmas ask (`--lean`), the totals are
  `0.77375𝒦` at `11/5`, `0.94408𝒦` at `2.194` and `0.98606𝒦` at `2.193`: the proved region keeps the exponent.
  Two variants change little: the estimate's stops in the rule (`0.7609𝒦` at
  `11/5`), and the bilinear Type I rule without the condition that `d₂` be shorter than the cofactor (`0.7335𝒦` at
  `11/5`, `1.0057𝒦` at `2.192`).
- **In Harman's decomposition**, which uses no window (`tools/linnik/type2_model.py`). A model of the large-value
  tools gives the region of his Type II lemma (Baker–Harman–Pintz, Lemma 9) with his tools, and shows that his proof
  cuts the modulus in one place, Huxley's theorem on powers of the prime-factored factor. Without it the region's
  condition `|α₁ − α₂| < 2θ − 1` is unchanged and its other side shrinks by at most a tenth (`ρ < 0.100` for his
  `0.112` at `θ = 0.528`), so that the region at `θ = 0.530` contains his at `0.528`. That suggests that his sieve
  reaches every modulus near `q < x^{0.47}`, an exponent of about `2.13`, given the half-plane. It is an estimate
  from one lemma's region: the sieve was not run, and his Type I lemmas were not modelled.
- **In a decomposition that does not lean on the window** (`tools/linnik/harman_sieve.py`, whose docstring states
  it). Each term has its own floor, the largest at which Harman's comparison evaluates it: its tree over the small
  primes is stopped by the estimate (the part that enters the zone is a set of the term's primes times the small
  primes, the rest a set of the term's primes or the first small prime), and its leaves are in the reach of Type I,
  taken with the bilinear estimate without the condition `2HD < q`. A box is evaluated by the window or by the
  estimate at every depth. And a term may be treated through any of its primes: the numbers `p₁⋯p_k m` are also
  `r′k` with `k = p_j` and `r′ = (r/p_j)m`, and Buchstab's identity then runs over the prime factors of `k` (role
  reversal, as in Harman's sieve for short intervals; here for terms of at most six primes, and once more inside a
  reversed tree). The loss, in units of the main term, with every test and every cost taken conservatively on boxes
  of cells of side `0.002` (first row), and with each cell replaced by its midpoint, the limit of fine cells
  (second row):

  | `L` | `11/5` | `2.18` | `2.16` | `2.15` | `2.14` | `2.13` | `2.12` | `2.11` | `2.10` |
  |---|---|---|---|---|---|---|---|---|---|
  | on cells | `0.033` | `0.163` | `0.400` | `0.511` | `0.634` | `0.765` | `0.924` | `1.097` | `1.273` |
  | at midpoints | `0.013` | `0.090` | `0.285` | `0.364` | `0.459` | `0.569` | `0.690` | `0.849` | `1.011` |

  So the computation passes at `2.12`, where the paper's decomposition stops at `2.193` (there this one loses
  `0.10`), and the limit of fine cells is near `2.10`, which is Baker, Harman and Pintz's `0.525` in the dictionary
  of the previous item, and agrees with its estimate of `2.13`. What carries it, at `2.13` on cells of side `0.004`,
  where the loss is `1.006`: role reversal (`1.090` without the second level, `1.269` for terms of at most four
  primes, `1.426` with none; with none the midpoints pass `1` at `2.16`) and the wider bilinear estimate (`1.174`
  with Lemma 4.2 as it stands). The linear sieve's bounds, for terms that the comparison does not evaluate, lower
  it to `0.999` and are left out. The cells pay for the boundary terms: a term `S(𝒜_r, z)` also counts `n = r`
  itself, Buchstab's identity on a box that is not regular at every point has such terms among its children, and
  a dropped box with such points costs their number too. Before they were paid for, the first row had `0.920` at
  `2.12` and `0.761` at `2.13`. Three checks of the program: in the paper's set-up at `11/5` (the window alone,
  Lemma 4.2, the window's width as the floor, no reversal) it gives `0.862` on cells of side `0.002` and `0.800` on
  cells of side `0.001`, where the certificate has `0.932` on its grid, and `0.728` at midpoints; with the linear
  sieve's bounds and no Type II information it gives `3.0`, so it does not detect primes, as parity requires; and
  the tabulated zone holds at `160000` points off its lattice. It is floating point, and not a certificate.
- **What is in Lean** (10 November; [`halasz-montgomery.md`](../formalisations/halasz-montgomery.md)). The two
  estimates, at the level of the paper's own:
  - the Halász–Montgomery inequality in mean square over a bin, `Σ_{χ∈R}|W(χ)|² ≤ e·Σ|a|²·(2P + |R|B)`
    (`SieveTypeIIHM.sum_bin_hm_sq`), and with it the estimate for two polynomials by bins
    (`SieveTypeIIHM.sum_typeII_two_bins`), as `SieveTypeIIHM.sum_typeII_bins_hm` is for one;
  - a bin's contribution as a power of `q`, under the exponent inequality of the estimate
    (`SieveTypeIIHM.bin_bound_two`), and that inequality for two variables of length at least `q` and a third factor
    of length at least `q^{1/2000}`, whatever the density curve (`SieveTypeIIHM.twoBound_of_long`). In exponents of
    `x` these are two variables in `[1/L, 1 − 1/L]` and a rest: the part of the region that needs no density
    estimate, `[0.4695, 0.5305]` at `2.13`;
  - the estimate itself, the paper's Proposition 3′ for two polynomials, for a curve and a region of the two
    lengths' exponents on which the inequality holds (`SieveTypeIIHM.typeII_two_gen`); with no density estimate for
    two variables of length at least `q` (`SieveTypeIIHM.typeII_two_long`); and for the curve of Huxley's estimate (the trivial
    count below `7789/10000`, Huxley's steps above) on an explicit region, for every `L` (`SieveTwoZone7D.zone_hx`,
    `SieveTwoZone7D.typeII_two_hx`; first proved for the curve `g7d`, with Chen, Gupta and Li's steps, which the
    region never needed: below `7789/10000` it bounds both variables by orthogonality, whatever the curve). With `s_i = 1 − m_i` for
    lengths `q^{m_i}` and `q^ρ` the length of the rest, the region is `ρ ≥ 1/2000`, `m_i ≥ 2/3` and `s₁`, `s₂`,
    `s₁ + s₂` at most `0.442192ρ − 1/12500`: a variable may be shorter than `q` by `0.442` times the exponent of
    the rest. The computations' zone is the union of such regions over the point where the Halász–Montgomery
    inequality takes over from orthogonality; this one is the region for that point at `s = 0`, and holds all of the
    zone but under 2% of `s` at its far end;
  - the paper's Lemma 4.4 for families with two polynomial variables (`SieveFamilyTwo.typeII_sharp_two`): `m₁` and
    `m₂` in dyadic blocks with the exponents of their lengths in the region, primes with smooth weights at fixed
    scales, and sharp comparisons with forms `φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i`, each with a prime as a pivot;
    the family's sum over `𝒜 − ℬ/φ(q)` is at most `A₀B₀q^{L−δ}/φ(q)`. It comes from the lemma's argument with the
    polynomial part abstract (`SieveFamilyGen.sharp_gen`): the argument uses the variable only through its value,
    its coefficient, its parts of the forms and the Type II estimate at each frequency, and for a pair the twisted
    sum is a product of two polynomials. Lemma 4.5, with the primes over all the primes up to `2q^L` and each
    `m_i` in an interval, is `SieveUnwTwo.typeII_unw_two`, for a rectangle of exponents inside the region;
  - the bilinear Type I estimate without `2HD < q`: on the diagonal the congruence `t d₂′ ≡ t′ d₂` has at most
    `F(⌊2HD/q⌋ + 1)` solutions for each `(t, d₂′)`, and the first term gains that factor
    (`SieveTypeIB.typeIB_bound_wide`; with a spline weight, `SieveSpline.typeIB_spline_wide`). It is carried to the
    leaves as far as a block pair (`lib/pnt/SieveTypeIBPairWide.lean`): over families with smooth and with sharp
    comparisons (`typeIB_smooth_wide`, `typeIB_sharp0_wide`), and on a block pair `(β₁, β₂)` with any cut `H` of
    the frequencies, `2H < q` (`pair_le_wide`), where the bound is
    `√(P₁P₂(P₁/q + 1)F(2HP₂/q + 1)(n/q + 1)n) + (B − A)(q/(2ℓ(H + 1)))^r P₁P₂ + P₁P₂d(q)/φ(q)`. The paper's
    `pair_le` is the cut `H = ⌊(q − 1)/(2⌊P₂⌋)⌋`, whose second term is small only for `P₂ ≤ ℓ`, that is
    `d₁d₂² ≤ x`; a cut `H ≈ qY/ℓ` makes it `Y^{−r}` for any `P₂`, with `2YP₂/ℓ + 1` under the root. With that cut,
    `H = ⌈qY/ℓ⌉`, the block pairs of a family of leaves are summed as in the paper's proof
    (`lib/pnt/SieveTypeIBSumWide.lean`): on the region `d₁ ≤ X₁`, `d₁d₂² ≤ X₂`, `d₁d₂ ≥ X₃` a block pair's bound is
    at most `√(ρ²(1 + η)N₂(ρX₁/q + 1)F(4Y·rρ³X₂/(ηN₁) + 1)((1 + η)ρ²N₂/(X₃q) + 1)) +
    ρ²(1 + η)N₂(2Y)^{−r} + ρ²√(X₁X₂)d(q)/φ(q)` (`bdPW_le`), and `leaves_family_wide` is
    `SieveTypeIBSum.leaves_family` with that bound, for `X₂` of any size. The asymptotic form is the paper's
    Lemma 4.3 on the wider region (`SieveTypeIBAsymWide.leaves_ib_wide`): for `a ≤ L − 2`, a margin `κ > 0`,
    `0 ≤ δ' ≤ min(κ/4, 1/8)` and `max(c, 0) ≤ a − δ' − κ`, the leaves with `d₁f_max ≤ q^{L−1−a}`,
    `d₁f_maxd₂² ≤ q^{L+c}` and `d₁d₂ ≥ q^{L−1−δ'}` are evaluated with an error `q^{L−δ}/φ(q)`. The paper's lemma
    is `c < 0`. In exponents of `x`, up to the margins, the region is `2a₁ + 2a₂ < 2 − τ` for `a₁ ≥ τ` and
    `a₁ + 2a₂ < 2 − 2τ` for `a₁ ≤ τ`, the rule of `two_factor.py --bil` and of `harman_sieve.py`.
  - the paper's Lemma 4.6 in two variables (`SieveTwoChain.chain_two`): a family of tuples of primes with
    comparisons of any kind, two disjoint sets of its primes as the two variables, at least one prime left as the
    rest, and the two products' exponents inside the region (asked on their rectangle cut by the band of their
    sum, since the product of the two variables is `n` over the rest), has `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`. A
    comparison with a prime of the rest has it as a pivot. One with none is a condition between the two variables:
    a bilinear bound `C|f|₂|g|₂` survives a condition `u(i) ≤ v(j)` at the cost of a factor `N + 1`, for `v` with
    fewer than `2^N` values (`SieveTwoCross.BilBd.cmp_list`: ranks, then binary digits, with the Cauchy–Schwarz
    inequality across the two halves), so `J₀` of them cost a power of `log q`. Every term `Σ_r S(A_r, z)` of a
    sieve, in the main tree or in a reversed one, is a sum of such families over the number of prime factors of
    its cofactor, whatever conditions tie its variables: with the cofactor in the second variable
    (`SieveTwoTerm.chain2_bound`) or in the rest (`SieveTwoTerm.chain2R_bound`).
  - Harman's comparison with these stops and with the leaves of the wider region (`SieveTwoComp.prop6_two`):
    for a family of chains in boxes, all at least `z₀ = q^{a₀}`, `Σ_r (S(A_r, z₀) − S(B_r, z₀)/φ(q))` is
    `o(q^L/(φ(q) log q))` when the product `c` of a set `S₀` of the chain's primes enters a window `(u, v)` wider
    than `a₀`, with the box of `c` below `v`, the product of a disjoint set `Sr ≠ ∅`, the rest, in `[q^{ρ₁}, q^{ρ₂}]`,
    the region at the exponents `(m₁, m₂)` with `u ≤ m₁ ≤ v` and `L − ρ₂ ≤ m₁ + m₂ ≤ L − ρ₁` (up to a margin), and
    the leaves' sizes
    `D₁ = Σ_{S₁} hi + t·[eIn₁]`, `D₂ = Σ_{S₁ᶜ} hi + t·[¬eIn₁]` (`t ≥ u − Σ_{S₀} lo` the tree's growth) with
    `D₁ < L − 1` and `max(D₁, 1) + D₁ + 2D₂ < 2L − 1`. This is the rule `exact floor` of `harman_sieve.py` for a
    rest among the term's primes, in exponents of `q`.
  - a certificate's format for a decomposition chosen term by term (`lib/pnt/SieveAdDefs.lean`,
    `lib/pnt/SieveAdTree.lean`): a tree on boxes of the exponents of a term's primes, whose nodes cut a cell,
    or apply Buchstab's identity with a floor of their own, and whose leaves are a box with no term, a box
    dropped at the bound of `SieveRough.shareBox` (for a term of the sign `+`), a box dropped for its products
    `n = p₁⋯p_k` alone at a bound for their number (`SieveAd.dropB_bound`: the last prime is a prime of a dyadic
    interval), and a box evaluated by a test.
    The check and the cost are functions on natural numbers, which the kernel evaluates, and the tests of the
    evaluations are a parameter. For tests that are sound, a tree that passes on the box of one prime with cost
    below `1` gives the theorem with the route's exponent (`SieveAd.linnik_tree`; `SieveAd.sound` is the bound of
    a tree, by induction). The paper's certificate is a fixed decomposition to depth 8; this one takes any tree.
    Two kinds of tests are proved sound. The window's (`SieveAd.winTests_sound`, from the paper's lemmas on
    boxes): a box surely evaluable, and a box that the bilinear rule passes at the window's width as the floor.
    And the estimate's (`SieveAd.twoTests_sound`), in exact integers on the region `Zone7d`: a box evaluated
    outright, its first variable and its rest two sets of its primes and its second variable the other primes
    and the cofactor (`SieveAd.evI_two`, from `chain2_bound`); and the comparison at a floor, for a set of
    primes that enters the window which the region leaves to the first variable, a rest among the primes, and a
    split of the leaves (`SieveAd.evJ_two`, from `prop6_two_at`). At `11/5` a tree that passes the two kinds
    gives the paper's theorem (`SieveAd22000.linnik_tree_22000`, with `SieveAd.mixTests`).
  - **Linnik's theorem with exponent `219/100`** (11 November; `Linnik21900.linnik_21900`): for every `q ≥ 1` and
    every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{219/100}`, with no hypothesis. The
    route is `L = 219/100` on the window `[0.44260, 0.46717]` (`SieveTypeIIU21900D.typeII_21900d`, by
    `gen_cgl_curve.py`), and the decomposition is a tree with the two kinds of tests, of cost `0.98189K`
    (`Linnik21900.tree21900`). The tree is not written out. `SieveAd.solveF` (`lib/pnt/SieveAdSearchDefs.lean`)
    is a search for a tree on a box that returns a cost and no tree: a box is evaluated by a proposed
    configuration, dropped, decomposed by Buchstab's identity at a proposed floor with the new prime's range cut
    into cells, or cut in two, and a limit stops a subtree whose cost reaches it. A cost that it returns below
    its limit is the cost of a tree that passes the check (`SieveAd.solveF_sound`): the search uses a node only
    after the check for that node has passed, so what proposes the nodes (the rest: one prime; the first
    variable: the set of the others with the largest lower sum below the window's top; cells of side `0.006`;
    terms of at most six primes) needs no proof. The kernel runs the search on `301834` boxes, in parts, each a
    range of consecutive cells of one prime (`lib/pnt/SieveTree21900P1.lean` and the files after it;
    `SieveAd.has_of_kids`), in about three quarters of an hour of its time. `tools/linnik/tree_cert.py` is the
    same search in Python: it cuts it into the parts and writes the files, and CI regenerates them
    (`check_certificate.py`).
  - **Linnik's theorem with exponent `218/100`** (11 November; `Linnik21800.linnik_21800`): for every `q ≥ 1` and
    every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{218/100}`, with no hypothesis. The
    route is `L = 218/100` on the window `[0.45073, 0.46472]` (`SieveTypeIIU21800D.typeII_21800d`), where the
    search for a tree costs `1.16K`. The search there has one more node, role reversal
    (`lib/pnt/SieveAdRevDefs.lean`; `SieveAd.bd_rev`), for a term of three primes `p₁ > p₂ > p₃` in cells, of the
    sign `−`, a term that needs an upper bound. Its numbers are `n = p₁p₂p₃m` with `m` rough at `p₃` and below
    `p₃³`, so `m` is a prime `Q` or a product `q₂Q`. The primes of `r' = n/p₁` in order (the atoms) are in one of
    five kinds of boxes: `p₂` above or below `Q`, and with `q₂` three places for `p₂`. `x/r'` is in the range of
    `p₁`, which is a condition on the atoms' product, and `n/r' = p₁` is rough at `z`, the least value of `p₃`.
    So the term in `𝒜` is at most the sum over those `r'` of the `n ≡ a` with `r' ∣ n` and `n/r'` rough at `z`,
    up to the `n` with a square factor at least `z` (`SieveAd.rev_cover`); and the term in the comparison set is
    at least the sum, over the `r'` of a range shorter by a factor `x^{1/DEN}` at each end, of the `n` with `n/r'`
    prime: they are terms of the box, each once, by unique factorisation (`SieveAd.rev_inject`). Each sum over
    `r'` is a term of the usual kind under a condition on its tuples, and has a tree of its own. The tree's boxes
    carry the atoms' cells and then the chain of the primes of `n/r'` that Buchstab's identity brings out; its
    steps keep the condition (`SieveAd.dIP_cut`, `SieveAd.dIP_buch`); the tests hold under two more conditions on
    the tuples (`SieveAd.mixTests_soundX`); and a chain's box is dropped at a bound by `Ψ`
    (`SieveAd.rootJ_sound`, `SieveAd.famCost_sound`). A reversal costs its trees' costs and what the numbers rough
    at `z` exceed the primes by in the comparison set, each times a bound of `Σ 1/r'` over its box. The search
    takes it where it is below the cost of Buchstab's identity, at `3664` of the `8185` boxes where it applies. A
    search with its nodes' tests as parameters is sound for any statement that the nodes prove
    (`SieveAd.solveG_sound`), and the reversed trees and the search itself are two uses of that
    (`SieveAd.solveK_sound`, `SieveAd.solveR_sound`). The bound's cost is `0.91812K`, from a search on `1063672`
    boxes with cells of side at most `0.006` and at most a tenth of the exponent. The kernel runs it in `587` parts
    (`lib/pnt/SieveTree21800P1.lean` and the files after it; `SieveAd.pr_of_kids`), in about an hour and forty
    minutes of its time, and `tools/linnik/rev_cert.py` is the same search in Python.
  - **Linnik's theorem with exponent `2165/1000`** (11 November; `Linnik21650.linnik_21650`): for every `q ≥ 1`
    and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2165/1000}`, with no hypothesis.
    The exponent is below `13/6`, where the Type II estimate in one variable has no window, and the route has the
    estimate in two variables alone. The rest of that estimate is a product of primes of exponent between `1/2000`
    and about `(L − 2)/0.558` in base `q`, and a term whose primes are all larger has none among them. For such a
    term at a floor `x^f`, the comparison takes its rest from the primes of its own tree of Buchstab steps below
    the floor (`SieveFillComp.prop6_fill`): the first of them, the largest, join the first variable until its
    product enters the window, as in `SieveTwoComp.prop6_two`; a stop of that tree is then sifted further, by the
    tree below its last prime (`SieveFillTree.tree_last`), and the primes of that second tree are the rest, until
    their product reaches `q^{1/2000}`. The rest is then below `q^{1/2000}x^f`, the window is the one that the
    region allows for all such rests, and the leaves grow by the floor and `q^{1/2000}` more; the level of the
    sieve still falls with the error, so nothing is lost but the room of that growth. The leaves pass through two
    trees, which costs one more product of `(1 + 1/p)` in the sums over them, and the level is chosen with
    `(2k + 4)³ζ(k)` small where one tree needs the square. The test of a box by this comparison is `okJ3`
    (`lib/pnt/SieveAdFillDefs.lean`), sound and sound under the atoms of a reversed term
    (`SieveAd.fillTests_sound`, `fillTests_soundX`), and the search is the one of the theorem at `218/100`, with
    role reversal, with a strategy that proposes no window and this test's floors
    (`lib/pnt/SieveAdFillSearchDefs.lean`). The root is the comparison of the whole sieve at the floor `x^{0.0489}`,
    by this test. The bound's cost is `0.95053K`, from a search on `3607561` boxes with cells of side at most
    `0.005` and at most a tenth of the exponent, which takes `8720` of the `18611` reversals that it tries. The
    kernel runs it in `2353` parts (`lib/pnt/SieveTree21650P1.lean` and the files after it), in about four hours of its
    time, and `tools/linnik/fill_cert.py` is the same search in Python.
  - **Linnik's theorem with exponent `2150/1000`** (12 November; `Linnik21500.linnik_21500`): for every `q ≥ 1`
    and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2150/1000}`, with no hypothesis.
    Two things are new. The first is a rule: a term of the sign `−` of three or five primes is reversed through
    its largest prime (below, *What is written of it*): summed over the frozen numbers `R = p₂⋯p_k·m`, it is
    the terms of `n/R` at a level between the square root of the greatest value of `p₁` and its least, and
    those have a tree of Buchstab steps of their own, searched with the tests `SieveAd.frozTests`. The second
    is the certificate. The kernel, running a search, takes `4` ms a box in the main tree and `13` ms over a
    frozen part, and most of what it searches is not kept: with this rule on terms of three primes alone the
    search at `2.165` is twenty-three hours of the kernel, and with terms of five primes it is out of reach.
    So the search is run once outside the kernel (`tools/linnik/hint_cert.py`), and the plan it keeps is
    written as a number for each part, the hints, read from the low end in the order of the search: what is
    done at a box, with which configuration, and where the range of each new prime is cut. `SieveAd.solveD`
    follows them and checks each step, and its cost is a bound whatever the hints are
    (`SieveAd.solveD_sound`): a step is one of the rules among which the search chooses, and a step whose test
    fails returns its limit. The kernel computes nothing that the plan knows: the configuration of an
    evaluation is in the hints, and so are the two sets of a Buchstab step's comparison, with four bits that
    name its rest, from which its floor is a line of arithmetic; a cut is a number of steps of the grid from
    the cut before (below, *The kernel's time*). Consecutive cells that one test evaluates are one cell (five
    in six of the evaluated cells go this way), and consecutive dropped cells are one cell while its bound is
    within `0.2%` of the sum of theirs. At `2150/1000`, with cells of side at most `0.004` and chains' cells
    of side at most `0.006` over the frozen parts: the search visits `3.4·10^7` boxes, `2.8·10^7` of them
    over frozen parts, in nine minutes on four cores, and costs `0.94847K`; its plan has `3.4·10^6` steps,
    `1.6·10^5` of them reversals, and `5.2` MB of hints, in `1552` parts (`lib/pnt/SieveHint21500P1.lean` and
    the sixteen files after it), which the kernel checks in 63 minutes of its time (17 files, of 143 to
    271 seconds each, three at a time on four cores).
- **What is not written.** Role reversal at a second level (below). The reversal of terms of the sign `+` is
  written since, and with it and a planner that counts the kernel's time there is a theorem at `2140/1000`
  (`Linnik21400.linnik_21400`; below, *The sign `+` in the search*). Without them the plan of the theorem's
  search passes at `2.145` with cells of side `0.0035` (`0.975K`, on `6.0·10^7` boxes; `6.6·10^6` steps), twice
  the build of the theorem at `2.15` for `0.005` of exponent. What the second level and tests that do not narrow
  with the cells would give in exact terms is measured in the first two items below.
  - *Where the cells' loss is, with this rule* (12 November; the theorem's search at `2.15`, on twenty of the
    `115` cells of the first prime, with some tests taken at the midpoints of the cells, which is no
    certificate). With every test at the midpoints the cost falls by `24.6%`; with those of one kind alone,
    by `12.1%` (the estimate in two variables over the frozen parts), `5.8%` (the same in the main tree),
    `5.8%` (the comparisons at a floor in the main tree) and `4.1%` (those over the frozen parts). So a
    quarter of the theorem's cost is the cells', half of it in the terms over the frozen parts, where the set
    of the first variable has cells of the main tree (of side `0.004`) and of the chain (`0.006`) in a window
    `0.07` wide. Two remedies were tried in the exact search. The newest cell cut at the ends of the part that
    one configuration evaluates, the rest searched further, saves `1.5%` in the main tree and `4.5%` in both
    trees; it is sound with the rules that are proved (`SieveAd.Rules.split` cuts a cell anywhere, and `evl`
    takes any configuration), and wants only a step of the search led by hints that reads the cut. Conditions
    on the sums of exponents carried by the boxes of the main tree alone (the part of a box whose first
    variable is in the window evaluated, the rest searched further under the condition) save `13%` on cells of
    side `0.02` at `2.165`; that is not written: it wants a search on boxes under conditions and a test that
    reads the sums' ranges from them, on `SieveAd.bdP_split`, `SieveAd.bdP_buch` (a box under a condition) and
    `SieveAd.full2_core_at` (the estimate for a family cut out by any number of comparisons), which are
    proved. Each `0.005` of exponent costs `5%` to `9%` (`0.829`, `0.981`, `1.034` at `2.165`, `2.155`, `2.15`
    on cells of side `0.005`).
  - *What the next rules are worth in exact terms* (12 November, after the theorem; `tools/linnik/hint_probe.py`,
    at the theorem's parameters on twenty of the `115` cells of the first prime, where the plan costs `0.15403K`;
    none of this is in Lean unless said). **Where the cost is**: dropped boxes of two primes `41.8%`, of four
    `22.2%`, of six `1.1%`; reversed boxes of three primes `33.8%`, all of it the dropped boxes of their chains'
    first prime, and of five primes `1.1%`. A reversed box of three primes costs about `1.05` times its own
    share. **The cells**, further: of the `12.1%` of the term tests over the frozen parts, the chain's cells
    are `4.0%`, the frozen primes' `5.2%` and the slab `1.2%` when each alone is taken at its midpoint; so the
    loss is spread over every kind of cell and of test. The cuts at the ends of an evaluated part
    (`4.5%`) are `1.2·10^6` cuts in all, two steps of the kernel each: no better, for the kernel's time, than
    finer cells. **The second level**: a chain's box of the sign `−`, in the tree of a reversed box of three
    primes, reversed again through `p₂`, the largest prime of the frozen number (the frozen numbers are then
    `R₂·N`, `N = n/R` in the cell of `p₁`, with `x/(R₂N)` in the cell of `p₂`; two slabs and two cofactors),
    saves `2.3%` for `2.6` times the search: its root, the terms at a floor over the new frozen part, fails
    two times in three (it needs `p₂` above about `x^{0.24}`, as the first level's needs `p₁`), and no
    configuration passes where the search's proposals fail (150 failing roots tried in full). A box reversed
    through a prime other than its largest: nothing. **The model on these shapes** (`harman_sieve.py`, Lean's
    forms, `2.15`, cells of side `0.004`): with only the terms that need an upper bound reversed, as in Lean,
    one level `0.898` (the exact search: `0.948`) and two levels `0.848`; with terms of either sign, `0.870`
    and `0.789`. Its second level is at the chains' boxes, through the largest prime of `r'` alone, with primes
    above `x^{0.24}`. So the `9%` that the model gave the second level was for boxes of the sign `+` reversed,
    their chains' first boxes, which need upper bounds, reversed again; for the shapes of the theorem it gives
    `5.6%`, and the exact search `2.3%`. **Boxes of the sign `+` reversed**, one level
    (`SieveAd.bd_flip_pos_at` is proved; the search's rule is not written): `2.3%`, on twice the search.
    **A planner that counts the kernel's time** (at the step times of the theorem's first certificate, seven
    hours of the kernel; below, *The kernel's time*): choosing each step by its cost plus `λK` for each second that
    it takes the kernel (a box of the sign `+` decomposed further only if that pays, a box of the sign `−`
    reversed or decomposed by the same count), with no change in Lean: `λ = 10⁻⁶` gives the cost `+0.13%` in
    `15%` less time, `3·10⁻⁶` `+0.6%` in `24%` less, `10⁻⁵` `+4.3%` in half the time, `3·10⁻⁵` `+11.6%` in
    a third. Coarser cells give `+9%` for about half the time, so at equal time the planner is worth about
    `5%`.
    So, by these numbers (an estimate: no plan was made at `2.14`; one has been made since, next item): `2.14`
    asks for the planner, the sign `+` and cells of side about `0.003` together, on a certificate two to three
    times the theorem's; nothing measured here gives `2.13`, and `2.12` is beyond these rules, not at their
    edge. The model's `2.12` leans on the second level for boxes of the sign `+`, and in the exact search that
    does not hold (`hint_probe.py … boxes`, on nine cells of the first prime from `x^{0.16}` to `x^{0.47}`):
    of the boxes of two primes that the plan drops, `42%` of its cost, none of the `80` of those cells costs
    less reversed than dropped, with one level or with two; they are the boxes with both primes and the
    cofactor near `x^{1/3}`, or `p₁` near `x^{0.4}` and `p₂` between `x^{0.19}` and `x^{0.29}`. Of the dropped
    boxes of four primes (`150` a cell), the reversal saves nothing for `p₁` below `x^{0.28}` or at
    `x^{0.47}`; in between, `3%` to `18%` of their cost with one level and `2%` to `18%` with two, and three
    quarters at `x^{0.45}`, where they are few: a hundredth or two of the plan's cost. (The whole search with
    the second level on boxes of the sign `+` was not finished on twenty cells in two and a half hours, and
    was stopped.)
  - *The sign `+` in the search, and a planner that counts the kernel's time* (12 November, after the theorem;
    in Lean and in `tools/linnik/hint_cert.py`). **The rule.** The hinted bound of the search led by hints is
    the reversal through the largest prime of a box of either sign (`SieveAd.altFD`, `SieveAd.flipCostD`,
    `SieveAd.bd_flipCostD`, from `SieveAd.bd_flip_coreB`, `lib/pnt/SieveAdFlipPos.lean`). For a box of the
    sign `+` (`SieveAd.bd_flip_core_pos`, from `SieveAd.bd_flip_pos`) the frozen numbers are those of the slab
    one unit narrower at each end, the tests are `frozTests` at those ends, the cells of the chain's first
    prime have the sign `−`, so that none is dropped before a Buchstab step, and the cost is `⌈(c·h₁·D₀ +
    bdK·E)/(DEN·K)⌉`. The kernel passes parts of a plan with such steps (eight parts of one cell of the first
    prime at `2.14`, with 82 of them), and the theorem at `2150/1000` is as it was: its hints have no such
    step, and its 17 files pass with the new definitions.
    **The planner.** `hint_cert.Planner` chooses by the cost plus `λK` for each second that it predicts of the
    kernel (`Par.lam`, in millionths of `K`): a box that may be dropped is decomposed only if that saves more
    than the decomposition's time is worth; a box of the sign `−` is reversed or decomposed, and a box of the
    sign `+` reversed, by the same count; dropped cells next to each other are one cell when that costs less
    than a step's time is worth. With `Par.blk` a new prime's cells are up to so many steps of the grid, each
    kept whole or halved, whichever is less by the same count (`Planner.pBlock`); the kernel's cuts are
    numbers of steps of the grid already, so nothing changes in Lean.
    **At `2.14`** (cells of side `0.003`, chains' cells `0.006`, boxes of at most six primes reversed). With
    no price on time the plan costs `0.96408K`, on `2.7·10^8` boxes (an hour on four cores), with `1.87·10^7`
    steps and five hours of the kernel predicted: it passes, at five and a half times the plan of the theorem
    at `2.15`. The sign `+` is `2.9%` of that (`0.16766K` without it and `0.16272K` with it on every sixth
    cell of the first prime, where `1.1·10^5` of the `5.5·10^5` boxes tried are reversed). The cost by the
    first prime: `0.0015K` below `x^{0.1}`, `0.018K` to `x^{0.2}`, `0.152K` to `x^{0.3}`, `0.404K` to
    `x^{0.4}`, `0.388K` above; the steps, in millions: `0.03`, `1.6`, `6.7`, `5.5` and `4.9`. So more than a
    third of the kernel's time is on a sixth of the cost, between `x^{0.2}` and `x^{0.3}`. Three fifths of the
    steps are over frozen parts, more than half of those evaluated boxes.
    With the price `λ`, on every sixth cell and with no blocks: `λ = 4` costs `0.6%` more for `27%` fewer
    steps, `λ = 8` `1.7%` more for `38%` fewer. On one cell of the first prime, at `x^{0.256}` (`3.5·10⁻³K`,
    `261` s of the kernel predicted): `λ = 3` gives `+1.3%` and `231` s, `λ = 10` `+19.8%` and `129` s; with
    cells of one or two steps of the grid (`blk = 2`), `λ = 3` gives `+1.2%` and `195` s, `λ = 6` `+6.9%` and
    `151` s, `λ = 10` `+17.1%` and `105` s, and with up to four steps the same within a point. The blocks cost
    the planner seven times its search, since it looks at a cell and at its halves at every level. Cells
    coarser throughout save nothing: at side `0.004` that cell costs `11.6%` more for `12%` less time, and at
    `0.005` `49%` more for none, the cells that no test takes whole being decomposed or reversed further. On a
    grid twice as fine, with `blk = 2` and `λ = 3` (and an earlier form of the rule for when the halves are
    looked at), the cell costs `4.5%` less than on the grid of side `0.003` in the same time of the kernel,
    and ten times the planner's.
    **The certificate at `2140/1000`** (`Linnik21400.linnik_21400`; `CERTS['21400']` in `hint_cert.py`: those
    cells, the sign `+`, `λ = 10`, no blocks). The plan costs `0.99055K`, with `9.79·10^6` steps, `3.56·10^5`
    of them reversals of boxes of the sign `−` and `2.3·10^4` of the sign `+`; the search visited `3.5·10^8`
    boxes, in eighty minutes on three cores (PyPy). Against the plan with no price on the kernel's time, that is
    `2.7%` more cost for `48%` fewer steps. It is `3705` parts in 39 files, `14.9` MB of hints (`31` MB as
    written), and 645 cells have a Buchstab step of their own outside the parts. The kernel checks the parts
    in `168` minutes of its time (39 files, of `244` to `271` seconds each, four at a time on four cores, so
    `44` minutes), where the planner predicted `155`: two and two thirds times the theorem's at `2.15`, for
    `2.9` times its steps.
    **What finer cells buy** (13 November; every sixth cell of the first prime, the sign `+`, no price on the
    kernel's time). With every test taken at the midpoints of the cells, which is no certificate but an
    estimate of the limit of fine cells (`hint_probe.py … pos,mI,mJ,fI,fJ`, on the grid of side `0.003`), the
    search costs `0.789K` at `2.14`, `0.913K` at `2.13` and `1.023K` at `2.12`: by these numbers the rules
    that are in Lean stop between `2.13` and `2.12`, near `2.122`, whatever the grid. The exact search at
    `2.14` costs `0.964K` with cells of side `0.003` and `0.917K` with `0.0025`, on twice the boxes: `22%` and
    `16%` above the limit. At `2.135` with cells of side `0.0025` it costs `0.967K`: it passes, on a plan of
    `4.3·10^7` steps and twelve hours of the kernel predicted (four and a half times the certificate at
    `2.14`), from a search of `5.6·10^8` boxes; a price on the kernel's time has `3%` to spend there. At
    `2.13` the limit leaves `9.5%` for the cells: cells of side about `0.002` or less, and several times that
    plan; not tried.
    **The planner's own search** (13 November; the certificate's parameters). Of the boxes that the planner
    searches on a cell of the first prime, `2%` to `9%` are under the plan that it keeps (four cells from
    `x^{0.28}` to `x^{0.50}`); the rest are in what it tried and did not keep: the decomposition of boxes that
    are then dropped (up to `57%` of a cell's search, most of it at boxes of two primes), reversals of boxes
    of the sign `+` that lose (`11%` to `41%`) and of the sign `−` (`10%` to `16%`), and the decomposition of
    boxes that are then reversed (up to `23%`). `Par.skip` (`hint_cert.py --try … --skip 3`) does not try
    again, at the next one, three or seven cells of a new prime, what lost at two cells in a row (the
    decomposition of a box that may be dropped, the reversal of a box of the sign `+`, the decomposition where
    the reversal won), tries it always at the last cell of the range, and solves the skipped cells again when
    it comes out the other way: on every sixth cell of the first prime the search is `0.55` of its boxes and
    the plan costs `0.17%` more, on `1%` fewer steps (the worst cell, `1.1%` more). The certificates are
    planned without it. What was tried and lost more: skipping after one loss costs `4.6%` on every sixth
    cell, most of it at cells from `x^{0.13}` to `x^{0.2}` (one costs seven times as much), where the one
    decomposition that loses in a prime's range is followed by one that wins; without solving the skipped
    cells again, `1.3%` on four cells where solving them again leaves `0.2%`; skipping fifteen cells, `2%` to
    `7%` on those four; skipping the reversal of a box of the sign `−`, `4.5%` at a cell near `x^{0.40}` for
    `6%` of its search. A box takes PyPy `25` µs; by CPython's profile of a cell near `x^{0.46}`, three fifths
    of that is the search for a configuration among the sets of the box's cells and a quarter the floor of a
    Buchstab step, and subset searches by index in place of slices gain `5%`. The cells of the first prime are
    planned apart, so the search goes as fast as there are cores.
  - *What the reversal is worth, shape by shape* (11 November; `harman_sieve.py cells` with `--no-window`, at
    `2.15` on cells of side `0.004` unless said; the switches of `--rev` are new). With no reversal the loss is
    `1.280`; with the shapes that are in Lean (`--flips 3 --nest 1 --rev odd,first,m2,low`: a term of three
    primes that needs an upper bound, through its largest prime, a cofactor of at most two primes, as an
    inequality sifted below the atoms) `0.998`; with every shape (`--flips 6 --nest 2`) `0.688`. **A term of the
    main tree needs to be opened through its largest prime only**: `--flips 5 --nest 2 --rev first` gives
    `0.697`. From there, each restriction alone costs: a cofactor of at most two primes (`m2`) `0.846`, of at
    most three (`m3`) `0.758`; only the terms that need an upper bound (`odd`) `0.797`; one level (`--nest 1`)
    `0.832`, and with `odd` too `0.867`, and with the inequality in place of the identity (`low`) `0.925`; terms
    of at most three primes (`--flips 3 --rev odd`) `0.972`. Inside a reversed tree, what is opened is a prime of
    `r'` of a term that needs an upper bound: only those (`natom`, `nodd`) give `0.738` and `0.698`; only the
    chain's first prime (`nchain`) `0.823`, no better than one level; only chains of one prime (`nc1`) `0.773`.
    So the gain is in four things together: terms of up to five primes, the cofactor kept as one number however
    many primes it has, the reversal as an identity (the chain of `n/r'` sifted from `x^{a₁/2}` down, its primes
    above some of `r'`'s), for either sign, and a second level through the primes of `r'`.
  - *How much of the loss is the cells.* `harman_sieve.py points` (each cell at its midpoint, the limit of fine
    cells) gives for the shapes in Lean `0.662` at `2.15`, `0.962` at `2.13` and `1.104` at `2.12`, and for
    `--flips 5 --nest 2 --rev first` `0.365`, `0.573` and `0.694`. The exact search of the theorem at `2.165`
    (`fill_cert.py`'s, cells of side `0.005`) costs `0.951`; with its tests taken at the midpoints of its cells,
    which is no certificate, `0.621` (`0.720` with the tests of the terms alone at the midpoints, `0.856` with
    those of the floors alone), `0.827` at `2.15` and `1.001` at `2.14`. So the rules that are proved stop near
    `2.145` whatever the cells, and a third of the theorem's cost is the cells', most of it at the boxes that a
    Type II configuration evaluates in part. One cheap remedy was tried in the exact search and is not enough: a
    box of the sign `+` dropped only outside the slab of the first variable's product that the zone takes, at the
    share that a prime confined to the remainder gives, costs `0.920` at `0.005`, `1.012` at `0.006` and `1.109`
    at `0.008` (`0.951`, `1.052`, `1.164` without).
  - *The model against the exact search.* With the stops in the form of `prop6_fill` (`--fill`) and no reversal,
    the model has `1.230` at `2.165` on cells of side `0.005` and the exact search `1.221`. With the shapes in
    Lean the model has `0.851` and the exact search `0.951`: the reversal as it is written gets `0.27` of the
    `0.38` that those shapes allow, because its boxes of atoms have independent cells where the sums of the
    atoms' exponents are tied (the cofactor's is `1` minus the others'), the cells of the cofactor's smaller
    prime are coarse, and the two ends of the range of `r'` are paid for. The first small prime as a rest in
    the model's own form, with a zone for each rest, is worth nothing more (`0.843` against `0.851`), nor is a
    rest of several primes; the leaves without the condition `2HD < q` are worth `0.13`.
  - *What it would give in Lean's forms* (`--fill --shrink 0.0015 --rev first,floor,offdiag`, and
    `natom,nodd` for two levels). At `2.16` on cells of side `0.005`: one level `0.804` (`4.4·10^6` nodes), two
    levels `0.735` (`8.2·10^6`); the shapes in Lean `0.958`. At `2.15` on cells of side `0.004`: `0.870`
    (`1.5·10^7`) and `0.789` (`3.1·10^7`). In the limit of fine cells: `0.47` and `0.40` at `2.15`, `0.78` and
    `0.64` at `2.13`, and `0.75` with two levels at `2.12`. So the general reversal with certificates of this
    kind is a theorem near `2.15`; **`2.12` needs it and, besides, a certificate that loses a small part of
    what cells of side `0.004` lose** (`0.39` at `2.15`), and has `0.25` to spare in the limit.
  - *A design for it* (its first two parts are written, below). A reversed term is a sum over a frozen part: the numbers `r' = p₂⋯p_k·m`,
    `m` rough at `p_k`, with `x/r'` in the cell of `p₁`, and over a chain `c₁ > ⋯ > c_t` of primes of `n/r'`, of
    the `n` with `r'c₁⋯c_t | n` and `n/r'` rough at `c_t`. The tree's steps (a cut, Buchstab's identity on
    `n/r'`, a drop at Buchstab's bound for `n/(r'c₁⋯c_t)`) see `r'` only through `x/r'`, as the tree of
    `SieveAdRev.lean` does, so they hold for any frozen part, with costs in units of `Σ 1/r'`. The term at the
    top level `x^{h₁/2}` is the term of the box, exactly, but for the `r'` within `x^{1/DEN}` of the two ends, so
    it serves either sign; and `Σ 1/r'` is at most `h₁/DEN` times the box's own drop bound, since each `r'`
    carries the primes of `(x/r', 2x/r']` (`SieveAd.primes_level`): the model's cost `v·a₁·(drop)`. A term of
    the reversed tree is evaluated by the estimate in two variables on the full tuples, the primes of `m` and of
    the cofactor written out, where `SieveTwoChain.chain_two` asks for no order between them; its terms at a
    floor below every prime of `r'` are evaluated by the tests that are proved, on the sorted boxes that the
    tuples `(p₂, …, p_k, primes of m, c₁, …, c_t)` fall into when the primes of `m` have cells of side `1/DEN`
    and the tuple is sorted (the `n` with a square factor apart): the tests pass on those boxes when they pass on
    the ranges of the sums, which are exact because every atom's exponent is affine in the cells. A second level
    opens a prime of `r'` in a term with a chain: the frozen part is then the rest of `r'` times `c₁⋯c_t` times
    the cofactor rough at `c_t`, under two conditions.
  - *What is written of it* (11 November). The tree over any frozen part in the range of `r'`
    (`lib/pnt/SieveAdFroz.lean`, `SieveAdFrozTree.lean`): the terms on the multiples of `R`, the cut and
    Buchstab's identity on the chain, the box with no term and the dropped box, and the soundness of the search
    of `SieveAdRevDefs.lean` over it, given tests that are sound for the frozen part
    (`SieveAd.frozSolve_sound_at`, with the interface `SieveAd.SoundF`); and the top of the tree
    (`SieveAd.dJF_level_at`). And the reversal of a box through its largest prime as an identity
    (`lib/pnt/SieveAdFlip.lean`, `SieveAdFlipSum.lean`): the frozen part with the cofactor as one number
    (`SieveAd.frozS`), the two inclusions (`SieveAd.flip_cover`, `flip_inject`: the term of the box lies between
    the terms at the level `⌈x^{t/DEN}⌉`, `l₁ ≥ t ≥ h₁/2`, over two frozen parts that differ in the `R` within
    `x^{1/DEN}` of the ends), the weight of the frozen part by the share of the box
    (`SieveAd.froz_weight_le_at`), and the bound for either sign from a tree's cost (`SieveAd.bd_flip_neg_at`,
    `bd_flip_pos_at`). And the terms at a floor over this frozen part, evaluated by the two comparisons
    (`lib/pnt/SieveAdSort.lean`, `SieveAdFillCore.lean`, `SieveAdFamSet.lean`, `SieveAdFamCore.lean`,
    `SieveAdFrozP.lean`, `SieveAdFrozJ.lean`, `SieveAdFrozRole.lean`): the cofactor written out as its primes,
    the tuples of distinct primes as a family of atoms in no order, the family as a union of sorted boxes of
    cells of side `1/DEN`, the comparisons on the sums of a box, and the bounds for the products over sets made
    of some primes of `r'`, the cofactor or not, and some primes of the chain, from the cells and the slab
    (`SieveAd.evJF_froz_fill_at`, `SieveAd.evJF_froz_two_at`); the tuples with a repeated prime are bounded by
    the `n` with a square factor. And the term of a chain's box over this frozen part, evaluated by the estimate
    in two variables (`lib/pnt/SieveAdFull.lean`, `SieveAdFrozI.lean`; `SieveAd.evIF_froz_two_at`): the chain's
    cofactor written out too, the tuples (primes of `r'`, of its cofactor, of the chain, of the chain's cofactor)
    as a family of comparisons with product in `(N₁, N₂]`, and `SieveTwoChain.chain_two` on it with the first
    variable and the rest given by their parts. So both evaluations that the tree over the frozen part asks for
    are proved, on finite sets of indices and numbers that pass `coreJ3`, `coreJ2`, `coreI2`; and the tests on
    the bits of the search's lists (`lib/pnt/SieveAdFrozDefs.lean`, without Mathlib) are sound for the frozen
    part (`SieveAd.frozTests_sound_at`, the hypothesis `SieveAd.SoundF` of the tree's search). And the main
    search with the reversal of a box of the sign `−` of up to eleven primes through its largest prime
    (`lib/pnt/SieveAdFlipDefs.lean`, without Mathlib; `lib/pnt/SieveAdFlipSearch.lean`): the cost of a reversal
    from the tree's cost and the shares of three boxes bounds the term (`SieveAd.bd_flipCost`), so the search is
    sound for any strategies (`SieveAd.pr_of_kidsF_at`). And strategies for it
    (`lib/pnt/SieveAdFlipStratDefs.lean`), with the search in Python definition by definition
    (`tools/linnik/flip_cert.py`), checked against the kernel on one part at `2165/1000`
    (`Linnik21650.flip_box_21650`: a box of two primes that the theorem's search drops at `0.000734·K` costs
    `0.000501·K`). Not written: the reversal of a box of the sign `+` in the
    search (worth `0.004` at `2.165` with cells of side `0.01`, and `2.3%` at `2.15` with the theorem's cells),
    and the second level (above). The kernel takes about
    `13` ms a box over a frozen part, where it takes `4` ms a box of the main tree (the sets of the tests are
    searched among more cells), and most of the boxes of the search with the rule are over frozen parts: a
    certificate at cells of side `0.005` is some twenty hours of the kernel, against the theorem's four. So the
    certificate of the theorem at `2150/1000` is not that search but its plan, which the kernel follows by
    hints (`lib/pnt/SieveAdDirDefs.lean`, `SieveAdDir.lean`; `SieveAd.solveD_sound`, `SieveAd.bd_flipCostD`,
    `SieveAd.pr_of_partD_at`), above.
  - *The kernel's time* (12 November, after the theorem; timed in the kernel on boxes of the theorem's plan,
    300 of each kind). The theorem's first certificate was a search led by hints of a few bits a step: what is
    done at a box, four bits that name a floor, and one bit at each proposed cut. The kernel computed the rest,
    and checked the certificate in seven hours of its time (39 files). The plan has `5.5·10^5` evaluated boxes,
    `6.1·10^5` Buchstab steps, `2.4·10^5` dropped boxes and `1.6·10^5` reversals in the main tree, and
    `8.3·10^5`, `3.5·10^5` and `6.1·10^5` over the frozen parts. A step cost the kernel, in milliseconds: an
    evaluated box `3.7` in the main tree (the strategy's search for a configuration `1.6`, the test `2.2`) and
    `7.2` over a frozen part (`3.4` and `3.4`); a Buchstab step `7.6` (the guide, which searches the sets of the
    comparison, `1.7`, the test `2.5`, the proposed cuts and their loop `3.4`) and `13.3` over a frozen part
    (`6.4`, `5.0`, `2.0`); the root of a reversal `20.5` (the guide `4.2`, the test `4.4`, the cuts `5.5`, the
    shares of the box and of its two ends `4.2`); a dropped box `0.9` to `1.1`. Over the plan: the tests `37%`
    of the time, the searches for configurations `36%`, the cuts `17%`, the dropped boxes and the reversal's
    arithmetic `9%`. The kernel is slow at what those definitions did most: a definition by structural
    recursion costs about three times its recursor, each `cond`, `&&` and operation through a type class is
    several reductions, and a list was walked once for each sum read from it. What was done, in the order of
    its worth:
    **the configurations in the hints** (`lib/pnt/SieveAdDirDefs.lean`). The rules that a search chooses among
    take any configuration, any floor and any cut (`SieveAd.Rules`), so a search that reads them from the hints
    is sound with the same proof, and computes none: an evaluation is its test alone, on the rest's cell and
    the set that the hints give (a bit for each cell of the box); a Buchstab step reads four bits that name
    its rest, computes its floor from the rest's cell, and reads the two sets of its comparison.
    **The tests in one pass** (`lib/pnt/SieveAdFastDefs.lean`). The sums that a test reads, of the cells' ends
    over each set of its configuration, are accumulated in one pass by the lists' recursor, with the bits of
    the masks as factors and no branch; the cells' check `f ≤ lo ≤ hi ≤ DEN` is the sum of
    `(lo − f) + (hi − lo) + (DEN − hi)` compared with `n(DEN − f)`; over a frozen part a second pass read the
    frozen primes (it is gone: below). The tests of the main tree are equal to the tests that are proved
    sound (`SieveAd.fillTestsF_eq`). A test costs `0.14` ms in place of `2.3` in the main tree, `0.4` in place of
    `2.6` at a floor, `1.5` in place of `4.4` at a reversal's root, and `0.5` and `1.1` in place of `3.0` and
    `4.4` over a frozen part. With them alone and the first certificate's hints unchanged, one of its 39 files
    took `339` s in place of `469` s.
    **The cuts as steps of the grid.** A list of proposed cuts with a bit for each cost the kernel as much as a
    test. Now each cut is a code: the number of steps of the grid from the last cut, which the kernel takes
    without reading anything, or one of the three cuts that the strategy proposes off the grid.
    **The dropped boxes in one pass**, with Buchstab's function in the arithmetic of `ℕ` written out
    (`SieveAd.drpMP_eq`, `SieveAd.opsKP_eq`, `SieveAd.omKwP_eq`), and the reversal's shares from one pass over
    the frozen primes.
    A step then cost: an evaluated box `0.3` ms in the main tree; a Buchstab step `1.2`; a reversal's root
    `3`; a dropped box `0.25`. Over a frozen part the same profile gave `0.8`, `2.1` and `0.35`, which were
    not the search's costs: it computed the sums and the number of the frozen primes at each box by the
    definitions that the proofs use, where the search has them once for a tree, and `0.35` was the cost of the
    dropped box's bound without its step. Timed a tree at a time (below), the boxes over a frozen part cost
    `0.67` (evaluated), `1.46` (a Buchstab step) and `0.45` (dropped). The hints are `5.2` MB where they were
    `2.5`: ten bits or so for an evaluation, fifteen for a Buchstab step, three for a cut. The kernel checked
    the theorem's certificate in 76 minutes of its time (17 files), where it took seven hours: the same plan,
    the same cost `0.94847K`.
    **The frozen primes once for a tree** (`SieveAd.frozTestsC`). A box of a tree over a frozen part is the
    cells of a chain, one or two, followed by the tree's frozen primes, two or four, the same at every box of
    the tree; the tests read them at every box, in their second pass. Now a test reads the chain alone in its
    pass, and takes from the frozen primes the sums of their ends over a set of bits and their least lower
    end, which are values of the tree (`SieveAd.roleB`, `SieveAd.lomP`). The kernel keeps what it has computed
    for a term, and so computes such a value once if it meets it as the same term: a set comes out of the
    hints as a number computed at the box, and `SieveAd.canonN` hands it on as a numeral, the same term for
    the same set. The floor of a Buchstab step and the cuts of a new prime read the chain alone too
    (`SieveAd.cfgJF`, `SieveAd.kidsF`). The tests are no longer the proved ones as functions, for they do not
    check the cells after the chain's; they imply them on the boxes of the tree (`SieveAd.frozTestsC_okI`,
    `SieveAd.frozTestsC_okJ`), and a statement of the tree concerns no other box (`SieveAd.rules_frozC`). The
    hints and the part files are the same. On the boxes of 150 trees of the plan, the boxes of a tree
    evaluated together with the tree's frozen primes as one term, as in the search (777 evaluated boxes, 300
    Buchstab steps), an evaluated box costs `0.50` ms where it cost `0.67`, and a Buchstab step `1.07` where
    it cost `1.46` (its test `0.58` where `0.98`). Side by side on one machine, on every twentieth part of the
    plan, the kernel takes `11%` to `12%` less time than it did (`181`, `185` and `193` s where the two passes
    took `203`, `209` and `220`), in agreement with those two costs, which give a tenth over the plan's steps.
    The 17 files took 63 minutes in the run after the change, three at a time; that run and the one of 76
    minutes were hours apart on a machine whose speed drifts, so their difference says less than the measure
    side by side. What limits the gain: the trees are small (in thirty parts of the plan, 3822 trees of 6.7
    tests on average), half of the sets of an evaluation and three fifths of the sets of a Buchstab step had
    been met before in their tree, and the first computation of the sums for a set (`0.14` ms) costs about
    what the second pass did.
    **Measured and not written**: a box packed into one number, each end a field of 64 bits, with the sum
    over a set by one `AND` with a mask and one remainder. On 300 boxes of the plan, one at a time, the test
    of an evaluation takes `0.13` ms that way where the pass takes `0.11` in the main tree, and `0.34` where
    the two passes took `0.59` over a frozen part, which reading the frozen primes once gains by other means.
    **What is left**: no one part of a step stands out. A Buchstab step of the main tree (`1.2` ms) is its
    test (`0.4`), the reading of its hints with the branches of the step (`0.4`) and the loop over the cells
    of the new prime (`0.4`). The kernel's per-step time varies by a third from run to run on the machine
    used, so a gain is measured side by side, the old search against the new on the same parts at the same
    time: the three runs above gave `11.2%`, `11.4%` and `12.3%`.
  - *The exact search with it* (12 November; `tools/linnik/flip_proto.py`, the search of `fill_cert.py` with
    this rule in exact integers; not yet a Lean search). The cost of a reversed box of the sign `−` is
    `(c(h₁D₀ + E) + bdK·E)/(DEN·K)`, with `c` the cost of the tree over the frozen part, `D₀` the share of the
    box (`dropCost`), `E` the shares of the two ends and `bdK` Buchstab's bound at the level `⌈h₁/2⌉`; for the
    sign `+`, `(c·h₁D₀ + bdK·E)/(DEN·K)`. With cells of side `0.005` and boxes of at most four primes reversed:
    at `2.165`, `0.897` (with the three-prime reversal that is in the theorem's search too; `0.911` without it;
    the theorem's search, `0.951`; no reversal, `1.221`), on `1.1·10^7` boxes where the theorem's search has
    `3.6·10^6`; at `2.16`, `0.967`, where the theorem's search has `1.018`. The model has `0.781` for this rule
    at `2.165` (one level, terms of at most four primes, Lean's forms), as it has `0.851` for the theorem's
    shapes: the exact search stays `0.10` to `0.12` above the model in both, and takes three quarters of the gain
    that the model sees. What the rule cannot do is the same in both: a box is reversed only if the terms at a
    floor over its frozen part are evaluated, and the frozen number `R ≈ x/p₁` is part of those terms' tuple, so
    the comparison's leaves leave room only when `p₁` is large (the root fails below about `x^{0.25}`); and a
    term of the sign `+` needs every chain prime from the floor to `x^{h₁/2}` evaluated or decomposed, since the
    tree's first level cannot be dropped, which fails where the chain's prime is too large to be a rest and the
    leaves have no room (`0.19·10^4` such reversals win of `1.6·10^4` tried, against `0.5·10^4` of the sign `−`).
    So one level of this rule on boxes of at most four primes is worth `0.05` in exact terms: a theorem at
    `2.16` on three times the theorem's boxes. Boxes of five primes add as much again: with cells of side `0.01`
    at `2.165` the search costs `1.438` with no reversal, `1.286` with this rule on at most four primes and
    `1.213` on at most five (`9·10^3` reversals of the sign `−` taken, against `1.3·10^3`), on twice the boxes;
    with cells of side `0.005`, `0.829` on at most five primes (`7.8·10^4` reversals of boxes of five primes
    taken of `2.6·10^5` tried), on `2.7·10^7` boxes, `2.4·10^7` of them in the trees over the frozen parts.
    At `2.155` the same costs `0.981`, and at `2.15`, `1.034`. In the Lean definitions (terms of the sign `−`
    alone, the tree searched with the limit past which the reversal does not win; `tools/linnik/flip_cert.py`),
    with terms of three primes reversed and cells of side `0.005`: `0.908` at `2.165` and `0.977` at `2.16`.
    Over the frozen parts, chains' cells of side `0.006` in place of `0.012` gain `0.02`, and chains of one more
    prime nothing; in the main tree, boxes of one more prime decomposed gain `0.007`, and cells at most a
    fourteenth of the exponent in place of a tenth `0.016` for twice the steps. Without the reversal of three
    primes, with terms of three and five primes reversed through the largest prime and chains' cells `0.006`
    (`tools/linnik/hint_cert.py --try`): `0.966` at `2.155` with cells of side `0.005`, `0.948` at `2.15` with
    `0.004` (the theorem), `0.975` at `2.145` with `0.0035`.
    The model's `0.69` at `2.15` is two levels and terms of five primes, and `2.12` is that and a certificate
    that loses much less than the cells do.
  - *Why `2.19`.* Without reversal, and without the stops whose rest is the first small prime, the cells pass at
    `2.19` with the window, and not at `2.18` (`harman_sieve.py cells 2190/1000 --flips 0 --no-first --h 0.005`:
    `0.945`; `0.967` with Lemma 4.2's leaves; `0.865` at `2.195`; `1.066` at `2.18` with every stop). The tree
    needs boxes evaluated by the window (`1.10` without) and by the estimate with the cofactor in the second
    variable (`1.20` without), and none with the cofactor in the rest: these are the tests that are proved sound.
    One of the tree's boxes is the corner where the first two primes are both near `x^{1/2}`: its only terms are
    the products `n = p₁p₂` in `(x, 2x]`, dropped at a bound for their number (`SieveAd.dropB_bound`), which is
    the width of the first prime's top cell up to a constant. The window alone does not go below `11/5` with a
    tree of that size (`harman_sieve.py paper`: `1.22` at `11/5` and `1.75` at `2.195` on cells of side `0.005`).
    The search costs `0.98189K` on cells of side `0.006` with terms of at most six primes, `0.93489K` at `0.005`
    with nearly twice the boxes, and `1.00099K` at `0.0065` (`tree_cert.py --try`).
  - *Why `2.18`.* With the reversal of a term of three primes the search passes at `2.18` (`0.91849K`; `0.90043K`
    with the reversed trees' chains of up to three primes in cells of side `0.006`). It is sensitive to the
    cells: `1.01637K` at `2.18` with cells of side `0.007`, and `2.10K` with terms of at most five primes. At
    `2.175` (window `[0.45481, 0.46349]`) it costs `1.05257K` with the same cells and `0.98482K` with cells of
    side `0.005`, on `2.6·10^6` boxes, two and a half times the search at `2.18`: a theorem there is a matter of
    the kernel's time, and is not written. At `2.17` (window `[0.45892, 0.46226]`) the search does not pass:
    `1.26965K` with the same cells, `1.18333K` at side `0.005`, and `1.03938K` at side `0.004` with terms of at
    most seven primes, on `10^7` boxes (`rev_cert.py --try`). The window closes at `13/6`: the curve has none at
    `2.165`. So below `2.175` the search needs more of the reversal (in the computation, `0.981` at `2.17` with
    terms of at most six primes reversed), and below `13/6` the stops whose rest is among the small primes.
  - *The rest among the small primes.* Below `13/6` there is no window, and the term at the root, `S(𝒜, x^f)`,
    has no prime to be the rest: its tree is stopped with the first small prime as the rest. The region takes a
    rest of exponent at least `1/2000`, so the paths whose small primes are all below that are not stopped. They
    are left to Brun's sieve at a fixed level, whose gap is tiny and is not `o(1)`; the computation takes it as
    zero. In Lean the comparison has its rest among the term's primes and an error `o(1)`
    (`SieveTwoComp.prop6_two`); one with the rest among the small primes, and that gap as a cost, is not written.
  - *Without the window, in exact terms* (11 November; a search in exact integers with the tests that are
    proved, `SieveAd.twoTests`, and no window). The rest of the estimate in two variables is a product of primes
    of exponent between `1/2000` and about `(L − 2)/0.558` in base `q`, at most `x^{0.133}` at `2.16`. A term whose
    primes are all larger has none among them, and its rest is then the first of the small primes below its floor.
    Bringing that prime out by Buchstab's identity at the least floor `q^{1/2000}` leaves the terms at that floor
    to Brun's sieve at a fixed level, and the library has that bound with its constants
    (`SieveProp6.leaf_bound`, `SieveP6TreeLeaves.large_leaves_le`): the gap is `2ζ(k)L/ε_w` times `Σ 1/r`,
    below `10^{−12}` at `ε_w = 1/2000` and the levels `k + 2j`, `k = 36`, once the sums `Σ 1/p` over the ranges
    `[A, A²)` have an explicit bound (`4` is elementary; the library's constant comes from the prime number
    theorem and is not explicit; `3` is now proved, `SieveRanges.rng_sum_le_three`). So the gap is a cost of no
    size, and the window is not needed for the floor. What the fixed level does cost is room in the Type I
    estimates. The sieve's divisors reach `q^c`, `c = (2k + 4)ε_w`, and the leaves that the bilinear estimate
    takes need `c < δ' ≤ κ/4` in `SieveP6LeavesWide.leaves_chain_wide`, so a box's two blocks must fit with
    about `6c` to spare: `D₁ + 6c < L − 1`, `2(D₁ + D₂) + 7c < 2L − 1`, `D₁ + 2D₂ + 6c < 2L − 2`. With sums at
    most `3` the level is `k = 20` (`c = 0.022`), with `2` it is `16`, with `1` it is `12`. The search below
    costs `1.44K` at `2.16` with no margin, `1.50K` with `k = 12`, `1.61K` with `k = 18`, `1.69K` with
    `k = 24`, and `2.36K` if only the trivial Type I range is used at the floor: the bilinear estimate is
    needed there, and a sharper value of the sums, or leaves with less to spare, is worth `0.1K` to `0.2K`.
    What the search then costs: `1.52K` at `2.16` with no reversal (cells of side `0.006`; the model has `1.36`
    at `0.007`), and with the reversal of `Linnik21800`'s shape, its trees stopped the same way, `1.44K` at
    `2.16`, `1.30K` at `2.17` and `1.08K` at `2.18`, where the window's tests bring it to `0.92K`. Two things
    are needed besides the floor. A drop that counts the strictly decreasing tuples of a cell once, not `j!`
    times: the cells of a small prime repeat down a chain, and without it the search costs `2.5K`. And the
    reversal of the model, which the exact search does not have yet: of a term of two or three primes, of
    either sign, through any of its primes, with a cofactor of any number of prime factors
    (`harman_sieve.py cells 2160/1000 --no-window --flips 3 --nest 1 --h 0.005`: `0.881` with `2.5·10^6` nodes,
    `0.782` at `--h 0.004`, `1.083` at `--h 0.007`; `1.059` with `--rev odd,prime`; `1.361` with `--flips 0`;
    at `2.165` with `--h 0.007`, `0.984` with `5.7·10^5` nodes).
  - *The rest from the comparison's own small primes* (11 November; the same search with one more floor test).
    The floor at `q^{1/2000}` is not needed either. In the comparison of the terms at a floor `x^f` the tree of
    Buchstab steps runs over the primes below the floor, down to a level that tends to `0`, and its rule for
    stopping can use those primes twice: the first of them, the largest, join the first variable until its
    product enters the window, as now; the next ones are the rest, until their product reaches `q^{1/2000}`. A
    stop then has its rest between `q^{1/2000}` and `q^{1/2000}x^f`, and the window is the one that the zone
    allows for all such rests, `[1 − 0.442/2000, L − 1 − 0.558(1/2000 + Lf)]` in exponents of `q`, which must be
    wider than the floor: `f < 0.0475` at `2.16`. The leaves grow by the floor and by `q^{1/2000}` more, and
    their level still tends to `0`: there is no gap, no cost, and no room lost in the Type I estimates. With
    this test for the boxes that have no rest among their primes (and for the root, at `x^{0.0475}` at `2.16`),
    no window, and the reversal of `Linnik21800`'s shape, the search costs `0.850K` at `2.18` (cells of side
    `0.006`, `1.4·10^6` boxes; the theorem's search, with the window, has `0.918K`), `0.957K` at `2.17`,
    `1.055K` at `2.165` and `1.110K` at `2.16`; with cells of side `0.005`, `0.961K` at `2.165` (`3.4·10^6`
    boxes) and `1.018K` at `2.16`; with side `0.004`, `0.889K` at `2.165` and `0.946K` at `2.16` (`7.2·10^6`
    boxes). Without the reversal it costs `1.176K` at `2.18` and `1.227K` at `2.165`. So an exponent below
    `13/6` needs neither the window, nor the gap of a fixed level, nor a wider reversal: it needs this
    comparison and a build of several million boxes. The comparison is proved
    (`SieveFillComp.prop6_fill`, `prop6_fill_at`; `SieveTwoComp.prop6_two` takes its rest among the family's
    primes): the tree to the window is `prop6_two`'s, and each of its stops is sifted by a second tree, below
    its last prime, whose primes are the rest. So is the test of a box by it, in the search's terms and under
    the atoms of a reversed term (`SieveAd.fillTests_sound`, `fillTests_soundX`), and the theorem at `2165/1000`
    above is the search with it. Of the route by a fixed level, `SieveGap.gap_at` is proved and nothing uses it.
  - *Role reversal*, in exact terms: for a term `Σ S(A_{p₁⋯p_k}, p_k)` on a box of cells and one of its primes
    `p_j` in `[X, X′)`, the numbers `n = (r/p_j)·m·p_j` with `N₂/X′ < (r/p_j)m ≤ N₁/X` have `p_j = n/((r/p_j)m)`
    in its cell whatever `n` in `(N₁, N₂]`, so on them the term is `Σ S(A_{r′}, ⌈X′^{1/2}⌉)` over `r′ = (r/p_j)m`
    with that condition and no other on the cofactor, a term of the usual kind; the rest has `p_j` within a factor
    `N₂/N₁` of an end of its cell, a share `O(1/log x)` of the box. In the computation (`harman_sieve.py --rev`,
    whose docstring has the commands), what carries the reversal is the terms that need an upper bound (`1.06` at
    `2.19` if only the others are reversed, against `0.46`; cells of side `0.007`, one level), the bilinear
    Type I estimate inside the reversed trees (`1.09` with the linear one alone), and cofactors that are not
    prime (`0.66` if only prime cofactors are reversed); floors below every prime of a reversed term cost little
    (`0.47`). With the window, without the stops whose rest is the first small prime, and with one level of
    reversal for terms of at most three primes, the cells pass at `2.18` (`0.863`, `463000` nodes at side
    `0.007`) and not at `2.17` (`1.042`; `0.981` with terms of at most six primes reversed, off the diagonal,
    `693000` nodes); with prime cofactors only and off the diagonal they fail at `2.18` (`1.067`). The theorem
    at `2.18` has the reversal for one shape of term: three primes, of the sign `−`, reversed through the
    largest, with the cofactor below the cube of the smallest, so that the cofactor's prime factors are at most
    two and are written out as atoms; and at one level. It is an inequality, not the identity above: the `n` with
    `n/r'` rough at the least value of `p₃` bound the term, the comparison set pays for the rough numbers that are
    not primes, and the `r'` within a factor `x^{1/DEN}` of an end of the range are counted at a bound with
    nothing subtracted. What the computation at `2.12` has and Lean does not: the reversal of a term of more
    primes, whose cofactor is a number sifted at the term's last prime with more prime factors, as a variable of
    the new term; the reversal through a prime other than the largest; a second level, the terms of a reversed
    tree reversed again; and the stops of the reversed trees with a rest among the small primes.
  - *The size of a tree.* Without reversal the cells pass at `2.19` only (`0.87` with the window, `276000` nodes
    at side `0.005`); with it, `0.81` at `2.19` with `113000` nodes (side `0.01`, terms of at most three primes,
    one level), `0.75` at `2.17` with `10^6` nodes (side `0.007`, one level), `0.49` at `2.17` with `1.4·10^7`
    (side `0.005`, two levels), and `0.92` at `2.12` with the cells of side `0.002` of the table above, a tree of
    `4.7·10^9` nodes. The kernel searches about a hundred boxes a second (the tree at `2.19`, and the search at
    `2.18`, whose `10^6` boxes are near what a build can check), so it does not check that many one by one: a
    certificate at `2.12` needs a coarser tree, with cells chosen where they matter, or a check that shares work
    between boxes. Half of the search's time at `2.18` was in boxes that it drops after looking for a cheaper
    tree; the files drop `216` such cells outright (`SieveAd.pr_drop`), which a search told what to take would do
    everywhere.

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
- **Linnik below `2.198`:** not by the paper's decomposition with the window as its Type II estimate. With the estimate in two
  variables it reaches `2.193`, and in a decomposition without the window the computation of §3.1 passes at `2.12`.
  The two estimates behind them are in Lean at the level of their bounds; the sieves are not.

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
tail; the kernel's part is one file, where the zero at `24415` has six. It is a kernel-checked zero in the half-plane
of absolute convergence, of a function with the functional equation of an `L`-function. It is not the classical
function's, whose zeros there are the numerical ones above.

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
