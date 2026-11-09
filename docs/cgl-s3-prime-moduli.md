# Chen–Gupta–Li's 7/3 at prime moduli: the S₃ term

Status labels: **Written proof** (argued here; not machine-checked, not refereed), **Numerical**, **Conjecture**.
Prepared with AI assistance; needs expert review. The scripts are in `scripts/cgl_s3/` (numpy and sympy).

## The question

B. Chen, V. Gupta and Y. C. Li (arXiv:2507.08296v2) prove `Σ_{χ mod q} N(σ, T, χ) ≤ (qT)^{(7/3)(1−σ)+o(1)}` for every
`q`. The library proves a weaker form on `[5/7, 16/21]`, a bound for the number of characters with a zero rather
than for the number of zeros (`LinnikCGLDensity.cglDensity`, see
[`formalisations/chen-gupta-li-density.md`](../formalisations/chen-gupta-li-density.md)). For `q` with a factor of a
suitable size their method gives Guth and Maynard's `30/13`; the exponent `7/3` comes from prime `q` at `T = 1`.

Their Remark 12.3 names the critical case: `σ = 5/7`, a detector polynomial of length `N = q^{7/9}`, and a set `W` of
`|W| = q^{2/3}` characters, where the binding inequality is their bound `S₃ ⪅ (qT)²|W|^{3/2}`. In their words, this
term "corresponds to square root cancellation in the R functions but no cancellation in the sums over m. To improve this
term, we would need to find some joint cancellation in R and the m sums, which seems quite difficult."

Section 8 shows that at `T = 1` their detector is a sum over an interval. That opens a second route, on the other side of
the same critical point, and it shows that the numerics at the `q` we can reach are not yet asymptotic.

Throughout, `q` is prime, `T = 1`, `M = q/N = q^{2/9}`, and `R(y) = Σ_{χ∈W} χ(y)`.

## 1. What a saving is worth (Numerical)

Suppose `S₃ ⪅ q^{2−δ}|W|^{3/2}`. In their §12 case split (the mean value theorem on `[q^b, q^{3a/2}]`, their Theorem
1.1 with `q₁ = q` below), the term `4/(1+σ)` of their Theorem 1.2 becomes `(4 − 2δ)/(1+σ)`. It meets Ingham's
`3/(2−σ)` at `σ* = (5 − 4δ)/(7 − 2δ)`, so the uniform exponent is `7/3 − 2δ/3` for `δ ≤ 1/26`. At `δ = 1/26` Ingham's
bound, Guth and Maynard's term `15/(3+5σ)` and the new term meet at `σ = 0.7`, and the exponent stays at `30/13` for
larger `δ` (`price.py`). For Linnik's constant the payoff is small: the variant `gm` of
`tools/linnik/density_payoff.py` (their bound without the term behind `7/3`) moves the sieve route's reach by about
`0.01`.

## 2. The exact form of S₃ (Written proof)

At `T = 1` a separated `W` has one point per character, and the factors `n^{it}`, `|t| ≤ 1`, only reshape the smooth
weight; take `t = 0`. Let `K(ψ) = Σ_n w(n/N)² ψ(n)` and `E = (K(χχ̄′))_{χ ≠ χ′ ∈ W}`, the off-diagonal Gram matrix of
`W`. Their Lemma 4.5 and split (5.2) give `S₃ = tr(E³)` up to the coincident-pair terms, which are `O(N/q)` times `S₂`.

By finite Fourier analysis mod `q` (exact, no Poisson approximation),
`K(ψ) = (ψ(−1)τ(ψ)/q) Σ_m ψ̄(m) H(m)` with `H(m) = Σ_n w(n/N)² e(mn/q)`, which is concentrated on `|m| ≲ M`.
The three Gauss sums of a triangle combine into a Jacobi sum, and

`tr(E³) ≈ q^{−2} Σ_{x ≠ 0,1} tr( X_{−x} X_{(1−x)/x} X_{−1/(1−x)} )`,  `X_c[a, b] = |H(a)|^{1/2} R(ca/b) H(b)|H(b)|^{−1/2}`,

with `a, b` running over `0 < |m| ≤ L ≈ 4M`. This is checked numerically: the right side matches `tr(E³)` to within
`2–3%` (`schatten.py`). Their Proposition 7.1 bounds the corresponding sum with absolute values on every `R`, which is
where the phases are lost.

## 3. Where their bound is attained (Numerical)

Their bound `S₃ ⪅ q²|W|^{3/2}` is, at the critical point, the statement that the large-sieve constant
`s₁(M_W)² = λ_max(Gram matrix of W)` is at most about `q`. The truncated power method (one FFT on discrete logarithms
per step) maximises `s₁²` over sets of `q^{2/3}` characters (`probe.py`, `scale2.py`):

| `q` | `N` | random `W`: `s₁²/q` | adversarial `W`: `s₁²/q` | its singular vector's support | `N^{5/7}` | best with `\|bₙ\| = 1` |
|---|---|---|---|---|---|---|
| `10⁴` | `1292` | `0.25` | `0.70` | `46` | `167` | `0.39` (`3.0N`) |
| `10⁵` | `7743` | `0.14` | `0.50` | `109` | `600` | `0.23` (`2.9N`) |
| `10⁶` | `46416` | `0.08` | `0.43` | `311` | `2154` | `0.14` (`3.0N`) |
| `3·10⁶` | `109084` | `0.06` | `0.40` | – | – | – |

- Random sets and Singer difference sets (where `|R|` is exactly flat) have `S₃` at `5–9%` of the bound, falling
  with `q` (`s3direct.py`, primes `401` to `81401`). Subgroups are lower still.
- Adversarial sets reach about `40%` of the bound at every `q` tested, so no bound in terms of `|W|` alone beats theirs
  at these sizes. Their singular vectors sit on dilated short intervals: at `q = 100003`, on `n = (q + 15m)/8` with
  `|m| < 270`, where `χ(n) = χ(15/8)χ(m)` (`diag.py`, `diag2.py`). A polynomial with `|bₙ| ≤ 1` and values `N^{5/7}`
  needs at least `N^{5/7}` integers, so these are not large-values sets.
- With `|bₙ| = 1` the best found is about `3N`, the conjectured scale, and the sets it picks out have `S₃` at `7–15%`
  of the bound, falling with `q` (`unimod.py`, `unimodW.py`).

## 4. A Schatten–Hölder bound (Written proof)

Hölder's inequality for Schatten norms, `|tr(ABC)| ≤ ‖A‖_{S3}‖B‖_{S3}‖C‖_{S3}`, applied to each `x` and then across
`x` (the maps `x ↦ −x, (1−x)/x, −1/(1−x)` are injective), and then `‖X‖³_{S3} ≤ ‖X‖_{S2}‖X‖²_{S4}` and
Cauchy–Schwarz, give

`|S₃| ≲ q^{−2} Σ_c ‖X_c‖³_{S3} ≤ q^{−1} (Σ_m |H(m)|) |W|^{1/2} Q₄^{1/2}`.

Both sums are exact by orthogonality: `Σ_c ‖X_c‖²_{S2} = (Σ|H|)²(q−1)|W|`, and `Σ_c ‖X_c‖⁴_{S4} = (q−1)Q₄` with

`Q₄ = Σ_{χ₁χ₃ = χ₂χ₄} P(χ̄₁χ₂) P(χ̄₂χ₃) P(χ̄₃χ₄) P(χ̄₄χ₁)`,  `P(ψ) = Σ_m |H(m)| ψ(m)`,

a sum of 4-cycles over the additive quadruples of `W`, weighted by short character sums of length about `M`. It splits
into two parts:

- **The degenerate quadruples** (`χ₁ = χ₂` or `χ₁ = χ₄`): `|W|S_H⁴ + 2S_H² Σ_{ψ≠1} r_W(ψ)|P(ψ)|²`, where
  `S_H = Σ|H|` and `r_W(ψ) = #{χ ∈ W : χψ ∈ W}`. By Cauchy–Schwarz,
  `Σ r_W|P|² ≤ E(W)^{1/2} (Σ_ψ |P(ψ)|⁴)^{1/2}`, and the fourth moment of `P` is exact (`M² < q`). With their energy
  bound (Proposition 10.2), which is `E(W) ⪅ |W|⁴/q = q^{5/3}` at the critical point, this part contributes
  `q^{3/2}N^{1/2}|W|^{3/2}`: their binding term `q²|W|^{3/2}` improved by `M^{1/2} = q^{1/9}`.
- **The weighted energy** `(iv) = Σ_{non-degenerate quadruples} |P(ψ)|²|P(ψ′)|² ≥ 0`, with `ψ = χ̄₁χ₂`,
  `ψ′ = χ̄₂χ₃`. With typical weights (`|P|² ≈ Σ|H|²`) it is `E(W)(Σ|H|²)²`, and its contribution is exactly their
  energy term `qN|W|^{1/2}E(W)^{1/2}`.

## 5. The weighted energy (Conjecture, Numerical)

**Conjecture.** For the large-values sets of Proposition 3.1 at the critical point, `(iv) ⪅ E(W)(Σ|H|²)²`.

Under it, the large-values term `(qT)^{4/3}N^{2−4σ}` of their Proposition 3.1 is replaced by terms whose exponent at
`σ = 5/7`, `N = q^{7/9}` is at most `0.62` instead of `2/3`; the large-values exponent at `σ = 5/7` drops from `2.334`
to `2.224`, and the uniform exponent from `7/3` to `30/13`, set by Ingham's bound at `σ = 0.7` (`price2.py`). Below
`0.7` the new bound coincides with Ingham's. For a given `δ` it is enough that the bias
`ρ = (iv)/(E_nondeg (Σ|H|²)²)` be at most `q^{1/9 − 2δ} q^{5/3}/E(W)`.

What is known about it:

- Pure moment and Hölder arguments leave a worst-case gap of `q^{5/36}`.
- Two sufficient conditions: `max_{x≠1}|R(x)| ≤ |W|^{1/2}q^{1/9−2δ}` (with Heath-Brown's double-sum bound, their
  Theorem 10.1, applied to `P²`), or `max_{ψ≠1} r_W(ψ) ≤ (|W|²/q) q^{1/9−2δ}` (with the exact eighth moment of `P`).
- Both fail on the natural test sets. The sets picked out by `|bₙ| = 1` polynomials are biased on small rationals:
  `|R(x)| = 0.4–0.6|W|` at `x = −2/3, −3/2, −4, 6` (`q ≈ 10⁴`) and `x = −3/5, −5/4, 4/3, −2/7` (`q ≈ 10⁵`)
  (`uniform.py`, `whichx.py`). These proxies reach only `0.2–0.36 N^{5/7}` on `W`; true large-values sets of this size
  are conjectured not to exist.
- The bias itself stays bounded on every family tested (`q4split.py`, `popular.py`):

| `q` | random `W` | `W` from `\|bₙ\| = 1` | adversarial `W` | allowed at `δ = 1/26` (for `\|bₙ\| = 1`) |
|---|---|---|---|---|
| `3001` | `1.07` | `2.55` | `4.7` | `1.05` |
| `10007` | `0.99` | `3.81` | `7.8` | `0.95` |
| `30011` | `1.03` | `3.23` | `6.6` | `1.19` |
| `100003` | `1.00` | `3.35` | `4.7` | `1.26` |

A bounded bias would satisfy the condition for every `δ < 1/18` once `q^{1/9−2δ}` outgrows it, but nothing here
proves it stays bounded. The obstruction to this bound is specific: large-values sets clustered on characters that
agree on small rationals, the prime-modulus analogue of the clustering in `t` that Guth and Maynard remove by
subdividing `[0, T]`. Section 6 tests that analogy.

## 6. The Bohr-set test (Numerical)

Can the bias be removed by subdividing `W` along the small rationals it is biased on, as a stand-in for the `q₁ | q`
subdivision that prime moduli lack?

- **Subdividing concentrates the bias** (`bohr.py A`). Cells cut by the phases of `χ(x)` at the two most biased
  small rationals have bias `3.8–9.7` at `q = 10007` and `3.1–13.0` at `q = 30011`, against `3.8` and `3.2` for `W`.
  Quadruples inside single cells carry `54%` and `29%` of `(iv)` but only `35%` and `19%` of the energy.
- **Structured sets are a blind spot, not an obstruction** (`bohr.py B`). Bohr sets
  `{χ : |arg χ(p)| ≤ η for the first k primes}` of size `q^{2/3}` have bias `9–32`, growing with `q`, and energy
  above the random level. Yet their `S₃` is below that of random sets: `0.000–0.045` of the bound, against
  `0.056–0.067`.
- **Splitting the dilations instead gains nothing at these sizes** (`hybrid.py`). Splitting by the operator norm of
  `X_c` puts `10–50%` of the dilations among the structured ones for the Bohr and adversarial sets.
- **Where the cancellation lives** (`where.py`). With `T(x) = tr(X_{−x} X_{(1−x)/x} X_{−1/(1−x)})`, all over
  their bound, at `q = 10007 / 30011`:

| `W` | `S₃` | `Σ_x \|T(x)\|` | von Neumann `Σ_x Σ_i s_i s_i s_i` | Schatten `B₃` |
|---|---|---|---|---|
| random | `0.066 / 0.056` | `0.092 / 0.075` | `0.87 / 0.81` | `0.91 / 0.84` |
| from `\|bₙ\| = 1` | `0.148 / 0.093` | `0.176 / 0.110` | `1.12 / 0.97` | `1.24 / 1.06` |
| adversarial | `0.63 / 0.51` | `0.71 / 0.54` | `1.90 / 1.65` | `3.09 / 2.88` |
| Bohr, `k = 3` | `0.011 / 0.000` | `0.073 / 0.045` | `2.90 / 3.65` | `5.06 / 7.23` |
| Bohr, `k = 6` | `0.045 / 0.024` | `0.083 / 0.054` | `1.47 / 1.67` | `2.19 / 2.53` |

Across `x` the Jacobi-sum phases cancel little: `Σ_x |T(x)|` is within `1.1–1.4` of `S₃`, except for Bohr sets.
Inside each trace the three matrices' singular vectors are misaligned. The von Neumann bound is the best any
argument using only singular values can give term by term, and it overshoots `|T(x)|`:

- about `10×` for random `W`, growing like `M^{1/2}` (`9.5` at `M = 7.75`, `10.8` at `M = 9.89`), which is the gap
  between the Schatten bound and the truth;
- `20–80×` for Bohr sets.

Conclusions:

- Subdividing along the bias is the wrong move for this bound.
- Structured sets are a blind spot of norm-based bounds (theirs, the Schatten bound, the hybrid), not an
  obstruction to the truth.
- The next idea has to use the relative orientation of `X_{−x}`, `X_{(1−x)/x}` and `X_{−1/(1−x)}` inside each trace,
  that is, the phases `χ(y_i(x))` in the character-side triple sum.

## 7. Which coefficients make the bias, and the fourth moment (Numerical, Written proof)

- **The bias comes from multiplicatively structured coefficients** (`arith.py`, `arith2.py`). Take the top `q^{2/3}`
  characters of `D_b` for several `b`. Generic coefficients give unbiased sets: random signs or phases, and quadratic or
  additive phases, all have small-rational bias at the random level and `ρ = 0.9–1.05`. Structured ones do not:

| `b` | `ρ` at `q = 10007 / 30011 / 100003` | small-rational bias at `q = 100003` |
|---|---|---|
| Möbius | `1.13 / 1.31 / 1.27` | `0.20` |
| Liouville | `1.82 / 2.87 / 3.58` | `0.42` |
| primes | `2.13 / 1.53 / 1.20` | `0.12` |
| zero detector `Σ_{d \| n, d ≤ √N} μ(d)` | `1.42 / 1.89 / 2.37` | `0.31` |
| quadratic phase, random signs | `≈ 1.0` | `0.05` |

  The zero detector's bias grows faster than the allowance of §5, so the conditional route of §5 probably fails for
  these polynomials at the `q` we can reach. Two caveats from §8: Chen, Gupta and Li's own mollifier is shorter
  (`(qT)^ε`, which makes their detector a block sum at `T = 1`), and at these `q` the sizes involved are not yet
  asymptotic.

- **The fourth-moment cap** (`cap4.py`). For any `b` and `W`, `Σ_W |D_b|² ≤ (|W| Σ_χ |D_b|⁴)^{1/2}`. The adversarial
  extremisers of §3 sit at `78–84%` of this cap, and their normalised multiplicative energy mod `q`,
  `ρ_E = Σ_{χ≠χ₀}|D_b|⁴/(q‖b‖⁴)`, is `16.7 / 28.6 / 38.7` at `q = 10⁵ / 10⁶ / 3·10⁶`. The best `|bₙ| = 1` vector has
  `ρ_E ≈ 2.1`, the random level, and also sits near its cap `(2q|W|)^{1/2}`.
- **Dilated short intervals are harmless** (Written proof). Suppose `b`, or its Fourier transform mod `q`, is supported
  on a dilate `c·[−A, A]` with `A ≤ (q/2)^{1/2}`. Then `m₁m₂ ≡ m₃m₄ (mod q)` forces `m₁m₂ = m₃m₄`, so
  `Σ_χ |D_b|⁴ ≤ 2q·max_{k ≤ A²} d(k)·‖b‖⁴`. Hence `Σ_W |D_b|² ≤ (2q|W| max d)^{1/2} ‖b‖² = q^{5/6+o(1)} ‖b‖²` at
  `|W| = q^{2/3}`, a factor `q^{1/6−o(1)}` below their bound. The extremisers of §3 are essentially of this kind: at
  `q = 100003` their support is `|m| < 270`, against `(q/2)^{1/2} ≈ 224`. They look sharp at `q ≤ 3·10⁶` because the
  divisor bound is still `100–240` there, and `ρ_E` grows with it.
- **What a genuine large-values set needs.** At the critical point `|W|V² = qN`, so by Cauchy–Schwarz
  `Σ_{χ∈W} |D_b|⁴ ≥ q^{4/3}N²`. That is, the fourth moment of a `1`-bounded `b` on `W` must be `q^{1/3}` times its
  random value. So `b` can be neither localised (previous point) nor random-like (`ρ_E ≈ 2`). It must carry
  multiplicative energy mod `q`, spread over many characters, beyond what an interval or a random sequence has.
  Sieve-type coefficients such as the zero detector are the natural candidates.
- **The classical fourth-moment bound.** `Σ_χ |D_b|⁴ ≤ N⁴ + O(qN² log²N)` (Ayyad, Cochrane and Zheng count the
  congruence for intervals) gives `|W| ≲ N^{4−4σ} + qN^{2−4σ}`. Its second term is `q^{1/3}` at the critical point,
  and only the first, `q^{8/9}`, is bad. That term comes from multiplicative energy that `b` concentrates on special
  characters. Removing it for the large-values sets is the whole problem in this form.
- **The scaling in `|W|`** (`sparse_ls.py`). At `q = 10⁵` and `10⁶` the power method gives
  `s₁² ≈ (0.4–0.5)·q^{2/3}|W|^{1/2}` for `q^{1/2} ≤ |W| ≤ q^{3/4}`, the shape of their bound read as a bound for
  `s₁²`. A bound `s₁² ≲ q^ε(N + (q|W|)^{1/2})` for every `W` would give `|W| ≲ q^ε(N^{2−2σ} + qN^{2−4σ})` from their
  Lemma 4.1 alone. Through the power trick of their §12 that already implies the density hypothesis at `T = 1` for
  prime `q`, so in that generality it is out of reach. The case needed for `7/3` is the critical point alone, with any
  power saving.

## 8. At `T = 1` the detector is a sum over an interval (Written proof, Numerical)

The zero detector of §7 used a mollifier of length `√N`. Chen, Gupta and Li's is shorter: in their §12 the mollifier
`M_X` has `X = (qT)^ε`. At `T = 1` that makes their class-I detector a block sum, and the critical case becomes a
statement about `S_I(χ) = Σ_{n∈I} χ(n)` for intervals `I` of length about `q^{7/18}`.
The library's formal step does the same: `LinnikCGLStep` takes `X ≈ Q^{1/2000}`, `Q = q(T + 6)`, and
`Y = Q^{201/400}`.

- **The reduction** (Written proof). Their class-I zeros satisfy their (12.5):
  `|Σ_{N<n≤2N} cₙ χ(n) n^{−ρ} e^{−n/Y}| ≫ 1/log q` for a dyadic `N ∈ [X, Y log²Y]`, with `cₙ = Σ_{d|n, d≤X} μ(d)` and
  `Y = (qT)^{1/2}`. Writing `n = dm`, the sum is `Σ_{d≤X} μ(d)χ(d)d^{−ρ} Σ_{N/d<m≤2N/d} χ(m) m^{−ρ} e^{−dm/Y}`, so for
  some `d ≤ X` the inner sum is `≫ 1/(X log q)`. On `(x, 2x]`, `x = N/d`, the weight `m^{−β−it} e^{−dm/Y}` has size
  and variation `O(x^{−β})` when `|t| ≤ 1`. Partial summation then gives an interval `I ⊂ (x, 2x]` with
  `|S_I(χ)| ≥ x^σ q^{−2ε}`. With their class-II bound `q^{2(1−σ)+ε}`,

  `Σ_{χ mod q} N(σ, 1, χ) ≤ q^{O(ε)} (q^{2(1−σ)} + max_x #{χ ≠ χ₀ : max_{I⊂(x,2x]} |S_I(χ)| ≥ x^σ q^{−ε}})`,

  over `x ≤ q^{1/2+ε}`. The maximum over `I` is handled by cutting `I` into dyadic pieces. For the bounds below this
  costs powers of `log q`, and under (H) a constant factor in `η`. So at `T = 1` only block sums matter. The arbitrary coefficients of their Theorem 1.1 never arise.
- **Where `7/3` comes from** (Written proof). Take `σ = 5/7`, `x = q^θ` and the threshold `V = x^{5/7}`.
  - Fourth moment: `4x² < q` makes `ab ≡ cd (mod q)` an equation on `I⁴`. So `Σ_χ |S_I|⁴ = (q−1)E₄(I)`, with
    `E₄(I) = #{ab = cd in I} ≍ x² log x`, and the count is `≲ q x^{2−4σ} log x = q^{1−6θ/7+o(1)}`.
  - Sixth moment: for `x³ > q` the mean value theorem gives `Σ_χ |S_I|⁶ ≤ (q + 8x³)E₆(I) = x^{6+o(1)}`. The count is
    then `≲ x^{6(1−σ)+o(1)} = q^{12θ/7+o(1)}`.
  - The two meet at `θ = 7/18`, at `q^{2/3}`: Ingham's `3/(2−σ)` at `σ = 5/7`. They are the two ends of their §12
    split with `a = 7/9`: `N^k = q^{7/9}` (`k = 2`, their Theorem 1.1, whose `S₃` term gives the same `q^{2/3}`) and
    `N^k = q^{7/6}` (`k = 3`, their mean value case).

  The `x⁶` at the sixth-moment end is the principal character's `|S_I(χ₀)|⁶ = |I|⁶`. The mean value theorem cannot
  see that it belongs to `χ₀` alone.
- **A second route** (Written proof, given the hypothesis). By orthogonality,
  `Σ_{χ≠χ₀} |S_I|⁶ = (q−1)J₆(I) − |I|⁶`, where `J₆(I) = #{a₁a₂a₃ ≡ b₁b₂b₃ (mod q) : aᵢ, bᵢ ∈ I}`. Suppose that for
  some `η, c > 0`, uniformly in prime `q`, in `x ∈ [q^{7/18−c}, q^{7/18+c}]` and in intervals `I ⊂ (x, 2x]`,

  `J₆(I) = |I|⁶/(q−1) + O(x⁶ q^{−1−η})`. (H)

  That is, triple products from a short interval equidistribute mod `q` in mean square, with a power saving. Then the
  sixth-moment end improves to `q^{12θ/7−η}`, and the ends meet at `θ = 7(1+η)/18`. Near `σ = 5/7` the `T = 1` exponent
  is at most `3/(2−σ) − η(2σ−1)/((2−σ)(1−σ))`, which is `7/3 − 7η/6` at `σ = 5/7`. Against their `4/(1+σ)` above `5/7`,
  the uniform exponent at `T = 1` for prime `q` is at most `7/3 − η/2 + O(η²)`.

  This route works on the other side of the critical point from §§2–7. Those sections try to improve the
  fourth-moment end (length `q^{7/9}`, `S₃`, arbitrary coefficients). (H) improves the sixth-moment end (length
  `q^{7/6}`, interval coefficients).
- **(H) restates the problem in arithmetic form.** If `q^{2/3}` characters have `|S_I| ≥ x^{5/7}`, they alone give
  `Σ_{χ≠χ₀} |S_I|⁶ ≥ x⁶`. So (H) for some `η` is equivalent, at the level of exponents, to a power saving in the count
  near the critical threshold. It is not a reduction to something known. What it gives is a concrete counting problem,
  open to arithmetic methods that do not exist for arbitrary coefficients: shifted convolutions of three-fold divisor
  functions with box conditions, Kloosterman sums, geometry of numbers.

  Literature status: I found no asymptotic of the form (H) for `|I| ≈ q^{7/18}`. The nearest results are Ayyad, Cochrane
  and Zheng's for four variables, Garaev's on products from two short intervals, and the sixth moment of `L(1/2, χ)` on
  average over moduli (Conrey, Iwaniec and Soundararajan; Chandee, Li, Matomäki and Radziwiłł). Through Perron's
  formula, (H) would follow from `Σ_χ ∫_{|t|≤q^ε} |L(1/2+it, χ)|⁶ dt ≪ q^{7/6−η}` for the single modulus `q`. The Weyl
  bound (Petrow and Young) times the fourth moment gives only `q^{4/3+ε}`. Averaging over moduli is easy (the large
  sieve over `q ≤ Q` makes `x³ < Q²` diagonal), but it gives almost all `q`, not every prime.
- **The critical case is real at every `q` we can reach** (Numerical, `blocks.py`). For `x = q^{7/18}` the table gives
  the count `#{χ ≠ χ₀ : |S_I(χ)| ≥ x^{5/7}}`, its share of the fourth-moment bound `(q−1)E₄(I)/x^{20/7}`, and
  `M₆ = Σ_{χ≠χ₀} |S_I|⁶`.

| `q` | `x` | `[1, x]`: count `/ q^{2/3}` | share of bound | `M₆/x⁶` | `(x, 2x]`: count `/ q^{2/3}` | share of bound | `M₆/x⁶` |
|---|---|---|---|---|---|---|---|
| `100003` | `88` | `1.04` | `0.21` | `8.2` | `0.32` | `0.12` | `1.64` |
| `1000003` | `215` | `1.20` | `0.20` | `9.7` | `0.27` | `0.095` | `1.58` |
| `10000019` | `528` | `1.32` | `0.19` | `10.9` | `0.22` | `0.070` | `1.45` |
| `30000001` | `809` | `1.39` | `0.18` | `11.1` | `0.20` | `0.063` | `1.41` |

  - The sum over `[1, x]` realises their critical case: `(1.0–1.4)·q^{2/3}` characters cross `x^{5/7}`, a fifth of the
    rigorous bound. Its nonprincipal sixth moment is `8–11` times `x⁶`. It is also `91–95%` of `q·E₆`, where
    `E₆ = #{abc = def in [1, x]}`, so the integer diagonal accounts for it. `E₆/x³ = 61, 103, 171, 208`, about
    `0.1(log x)⁴`, the exponent `(k−1)²` of Conrey and Gamburd's count of `a₁⋯a_k = b₁⋯b_k`. The diagonal `q·E₆` falls
    below `x⁶` only when `q^{1/6}` beats `0.1(log x)⁴`, near `q ≈ 10^{27}`.
  - The dyadic block, which is the detector, is milder. Its count falls from `0.32` to `0.20` of `q^{2/3}` over a factor
    `300` in `q` (local exponent `0.59`), and from `12%` to `6%` of the bound. Its `M₆/x⁶` falls from `1.64` to `1.41`,
    still above `1`. The difference is the small integers. Pretentious characters (`χ(p) ≈ 1` for small `p`) collect
    the smooth numbers up to `x`, and `(x, 2x]` has far fewer of those than `[1, x]`.
  - The genuine critical sets are not near their `S₃` extremal configuration (`blocks_s3.py`). For the dyadic block,
    `S₃(W_crit)` is `5.5%` of `q²|W|^{3/2}` at `q = 10⁵` and `6.6%` at `10⁶`, which is `7` and `16` times a random `W`
    of the same size. `λ_max(G)/N` is `2.9` and `3.9`, against their `q/N = 12.9` and `21.6`.
- **What this does to the numerics of §§3–7.** At the `q` we can reach, log powers are as large as the savings at
  stake: `q^{1/6}` against `(log x)⁴` here, and a saving `q^δ` with `δ ≤ 1/26` is at most `1.9` at `q = 3·10⁷`.
  Finite-`q` evidence cannot separate "these methods give `7/3`" from "`7/3 − δ` holds for large `q`". The falling count
  for the dyadic block is weak evidence for the second at `T = 1`. Heuristically, pretentiousness cannot carry the
  critical sets for large `q`. Reaching `x^{5/7}` from smooth numbers needs `χ(p) ≈ 1` for every `p ≤ (log x)^{7/2}`,
  since `Ψ(x, (log x)^A) = x^{1−1/A+o(1)}`, and such characters should die out. What remains is the proof technology for
  the other characters, where only moments are available.

## 9. The counting problem, directly (Written proof, Numerical)

Take `I = (x, 2x]`, `x = q^{7/18}` and `J₆(I)` as in (H). Every congruent pair has `a₁a₂a₃ − b₁b₂b₃ = kq` with
`|k| ≤ K = ⌊7x³/q⌋ ≈ 7q^{1/6}`. So `J₆ = Σ_{|k|≤K} N(kq)`, where `N(h) = #{a₁a₂a₃ − b₁b₂b₃ = h : aᵢ, bᵢ ∈ I}` is the
shifted convolution of the ternary divisor function with all three factors in `I`.

- **The split** (Numerical, `shifts.py`). Let `Ñ(h)` be a local fit of `N` on `|h' − h| < q/2`, using only the `h'`
  whose small-prime factorisation pattern matches `h` (`p^{min(v_p, 2)}` for `p ≤ 13`). Then
  `J₆ − |I|⁶/(q−1) = D + S + F`:
  - `D = N(0) − Ñ(0)` is the integer diagonal minus its band;
  - `F = Σ_{k≠0}(N(kq) − Ñ(kq))` is the error of the shifted convolution at the shifts `kq`;
  - `S` is the rest, chiefly the singular series of `N` averaged over `k ≤ K`.

  Each column is a multiple of `|I|⁶/q`:

| `q` | `x` | `K` | `J₆ − \|I\|⁶/q` | `D` | `S` | `F` |
|---|---|---|---|---|---|---|
| `100003` | `88` | `47` | `+1.644` | `+1.998` | `−0.273` | `−0.081` |
| `300007` | `135` | `57` | `+1.570` | `+1.884` | `−0.234` | `−0.079` |
| `1000003` | `215` | `69` | `+1.575` | `+1.865` | `−0.213` | `−0.076` |

  Matching the small-prime pattern matters. Without it, `F` is `−0.32`, `−0.28` and `−0.26`: most of the shift-to-shift
  scatter of `N(kq)` is the singular series, that is, the arithmetic of `k`.
- **What each piece needs.**
  - `D ≍ x³(log x)^c`, a power `q^{1/6}` below `|I|⁶/q`. It is large here only through the log powers.
  - `S` is a main term: the singular series averaged over `K ≍ q^{1/6}` shifts, expected to be `O(|I|⁶q^{−1}K^{−1+ε})`.
  - `F` is the problem. (H) asks for a power-saving asymptotic for `N(h)` on average over the `K` shifts `h = kq`.
- **Where the literature stands.** For `d₃` the shifted convolution is open at a single shift. The known averages
  (Baier, Browning, Marasingha and Zhao; Matomäki, Radziwiłł and Tao) run over all shifts `h ≤ H`, and the first uses
  the sixth moment of `ζ`. Its analogue here is the sixth moment for one modulus, the input that is missing. With
  `X = x³` our shifts are `X^{1/7}` points spaced `X^{6/7}` apart, which no average over an interval of shifts reaches.
- **Why it looks within reach and is not.** Fix `a₃, b₃` and open the rest along the lattice lines of
  `{(u, v) : a₃u ≡ b₃v (mod q)}`. `N` becomes a multilinear sum of Kloosterman fractions `e(h(α ē/d + β d̄/e))` over
  `d, e ∈ I`, with `α, β ≈ x²`. The saving needed is `x·q^η` over the trivial bound, well short of square-root
  cancellation (`≈ q^{0.86}`). But for each fixed line the coefficients are of size `x³`, beyond Duke, Friedlander and
  Iwaniec's bilinear bound, so the saving must come from the average over `a₃`, `b₃` and the lines.
- **What known results give** (Written proof, given the Weyl bound). For smooth weights,
  `Σ_{χ≠χ₀} |S_I|⁶ ≤ max_χ |S_I|² · (q−1)E₄(I) ≪ x q^{1/3+ε} · q x² log x`. This uses Petrow and Young's
  `L(1/2+it, χ) ≪ q^{1/6+ε}` through Perron's formula, and the exact fourth moment. So (H) holds for
  `x ≥ q^{4/9+ε}`, against the `q^{7/18}` needed. The equivalent targets in the language of `L`-functions, for the
  single modulus `q`, are:
  - a sixth moment `Σ_χ ∫_{|t|≤q^ε} |L(1/2+it, χ)|⁶ dt ≪ q^{7/6−η}` (the Weyl bound times the fourth moment gives
    `q^{4/3+ε}`);
  - a twisted second moment with the twist `S_I(χ)²` of length `q^{7/9}` (the classical range is about `q^{1/2}`);
  - a twisted fourth moment with the twist `S_I(χ)` of length `q^{7/18}`.

  All three reduce to the same obstacle.

## 10. The multilinear Kloosterman sum (Written proof, Numerical, Conjecture)

- **The reduction** (Written proof, sketch). Write `A = a₂a₃` and `B = b₂b₃`, pair products in `(x², 4x²]` with weights
  `r₂`. Then `a₁a₂a₃ − b₁b₂b₃ = h` reads `A a₁ − B b₁ = h`. For coprime `A, B` this fixes `a₁ ≡ h Ā (mod B)`, and
  since `B > 2x` at most one `a₁ ∈ I` qualifies. With smooth weights on `a₁` and `b₁`, Poisson summation mod `B` in `a₁`
  leaves frequencies `0 < |ℓ| ≤ x^{1+ε}` with coefficients of size `1/x`. Summing over the shifts `h = kq` turns the
  error into

  `F ≈ Σ_{m ≤ x^{1+ε}K} ν_m Σ_{A,B ∼ x², (A,B)=1} r₂(A) r₂(B) Φ(m, A, B) e(q m Ā/B)`,
  `ν_m = Σ_{ℓk=m} c_ℓ w_k`, `‖ν‖₂ ≍ (K/x)^{1/2}`,

  where `Φ` is smooth. This is Bettin and Chandee's trilinear form `Σ ν_a α_m β_n e(ϑ a m̄/n)`, with `ϑ = q`, `a = m`
  of size `xK`, and `α = β = r₂` of size `N ≍ x²`. The terms with `(A, B) > 1` and the separation of variables in `Φ`
  are standard and cost `q^ε`.
- **The size of the problem.** The trivial bound for the form is `Kx⁴`, while (H) needs `Kx³q^{−η}`. That is a saving
  of `x q^η = N^{1/2} q^η`, at every `θ`.
- **What Bettin and Chandee give.** Their Theorem 1 bounds the form by
  `‖α‖‖β‖‖ν‖ (1 + |ϑ|A/(MN))^{1/2} ((AMN)^{7/20+ε}(M+N)^{1/4} + (AMN)^{3/8+ε}(AN+AM)^{1/8})`.
  Here `|ϑ|A/(MN) = q·xK/(16x⁴) ≈ 7/16`: the modulus `q` of the shifts exactly balances the ranges, so the penalty
  factor is `O(1)`. Their saving, `min(A^{3/20}N^{1/20}, N^{1/8}) = N^{1/8} = x^{1/4}`, is `q^{0.097}` at `θ = 7/18`,
  against the `q^{0.389+η}` needed. In this arrangement no `θ < 1/2` comes within reach, and not even the classical
  `θ = 1/2`. The loss is the factor `x` that the Poisson step gives away (the event `a₁ ∈ I` has probability `1/x`),
  which bounds for arbitrary `α, β` do not recover.
- **What would suffice** (Conjecture). Suppose that at `|ϑ|A ≍ MN` the form satisfies the large-sieve-type bound
  `≪ q^ε ‖α‖‖β‖‖ν‖ (A + M + N)^{1/2}`, as a random kernel would. Then `F ≪ q^ε x^{5/2}K^{1/2} = Kx³ q^{−(4θ−1)/2+ε}`,
  so (H) holds for every `θ > 1/3`, with `η = 5/18` at `θ = 7/18`. Less suffices: the full large sieve in `a` (a
  saving of `A^{1/2}`) together with a saving of `N^{1/7}` from the `(A, B)` structure. Bettin and Chandee get
  `A^{3/20}` and `N^{1/20}`.
- **Numerics** (`shifts.py --z 47 --e 3`). Matching each shift's signature over `p ≤ 47` (exponents up to `3`) shrinks
  `F` from `−0.08` to `−0.028`, `−0.025` and `−0.025` of `|I|⁶/q` at `q = 10⁵`, `3·10⁵` and `10⁶`. So most of §9's `F`
  was the arithmetic of the shifts. What remains is `0.3–0.45` times `x^{5/2}K^{1/2}`, the size the conjecture
  predicts. It still drifts up with `q`, probably from singular series of larger primes.
- **Using the coefficients' structure.** The trilinear bounds treat `α` and `β` as arbitrary, but here
  `r₂ = 1_I * 1_I` is a convolution of two intervals. Using that structure leads back to Kloosterman fractions with
  factorable moduli `b₂b₃` and inverted variables of length `√(modulus)`. Each piece sits at the Weil barrier, so the
  saving has to come from Kuznetsov-type averaging over the moduli.

## 11. Kuznetsov over the moduli (Written proof, heuristic accounting)

The moduli that vary in §10 are the integer products `B = b₂b₃`. Kuznetsov's formula and the spectral large sieve
average over them; the fixed prime `q` cannot be averaged over.

- **The Deshouillers–Iwaniec bound** (`kuznetsov.py`). Their Theorem 12, in Drappeau's form (his Theorem 2.1, with the
  correction `D²NR` of Bombieri, Friedlander and Iwaniec), bounds
  `Σ b_{n,r,s} g(c, d, n, r, s) e(n \overline{rd}/(sc))` with smooth `c, d` by `𝒦‖b‖₂`, where
  `𝒦² = CS(RS+N)(C+RD) + C²DS((RS+N)R)^{1/2} + D²NR`.
  The phase `e(ℓkq Ā/B)` forces the matching `sc = b₂b₃` (`c = b₃`) and `rd = a₂a₃` (`d = a₃`), with the numerator
  carrying `ℓkq`. The numerators are then multiples of `q`: only `xK` of them, spread over a range `N ≍ x⁴`.
  Theorem 12 sees the range, not the support. The result is worse than the trivial bound `Kx⁴` by `q^{1/2−θ}` at
  `x = q^θ`, and equal to it at `θ = 1/2`. Moving `q` into the inverted variable (`r = qa₂`) is worse still.
- **Bettin and Chandee's form is the better use of the same machinery.** They keep `ϑ = q` as a real scale on a dense
  variable, and their penalty `(1 + |ϑ|A/(MN))^{1/2}` is `O(1)` here (§10). That gives the saving `x^{1/4}`.
- **Heuristic accounting.** Averaging over the numerator variable `m = ℓk` can save at most its square root,
  `(xK)^{1/2}`. A version of Theorem 12 with the numerator's support in place of its range would give exactly that, a
  bound of exponent `5θ − 1/2` against the `6θ − 1` needed. That is enough only for `θ > 1/2`, the classical range.
  Below it, the remaining factor `x/(xK)^{1/2} ≍ q^{(1−2θ)/2}` (`q^{1/9}` at `θ = 7/18`) has to come from cancellation
  among the Kloosterman sums themselves as the modulus `b₂b₃ ∼ x²` varies. The arguments have `√(mn)/c ≍ x^{1/2}`,
  the transition range of the Bessel transforms. This is Linnik–Selberg-type cancellation, beyond what Kuznetsov's
  formula with the Kim–Sarnak exponent `7/64` delivers.
- **Where spectral methods do reach a single modulus.** Conrey and Iwaniec, and Petrow and Young, get the Weyl bound
  for one modulus from moments over families of level `q`. That is a different family from the moduli here, and so far
  it gives only the `q^{4/3}` sixth moment of §9.

## Scripts

All take primes as arguments (the next prime above each) and print their tables.

| Script | What it does |
|---|---|
| `probe.py` | Discrete logarithms, the FFT of a polynomial over all characters, and the truncated power method for `max_{\|W\|=R} s₁(M_W)²`. |
| `scale2.py` | The scaling table of §3, with the alignment of the maximiser on small primes. About 10 minutes to `q = 10⁷`. |
| `s3direct.py` | `S₃ = tr(E³)` exactly for random, Singer, subgroup and adversarial `W` at the Singer primes `q = p³+p²+p+2`. |
| `diag.py`, `diag2.py` | The Gram spectrum of the adversarial `W` and where its singular vector lives. |
| `unimod.py`, `unimodW.py` | The same search with `\|bₙ\| = 1`, and the large-sieve constant and `S₃` of the sets it finds. |
| `price.py`, `price2.py` | The density exponent of §1 as a function of `δ`, and of §5 under the conjecture. `price.py` takes about 15 minutes. |
| `schatten.py` | The exact form of §2 and the bounds of §4 against `tr(E³)`. |
| `q4split.py` | The split of `Q₄` into its degenerate part and `(iv)`, and the bias ratios. |
| `popular.py`, `uniform.py`, `whichx.py` | Popular differences, the sufficient conditions of §5, and the biased small rationals. |
| `bohr.py` | §6: `A`, the proxies cut into Bohr cells; `B`, synthetic Bohr sets. `(iv)` by one FFT per element. |
| `hybrid.py` | §6: the bound with the dilations split by the operator norm of `X_c`. |
| `where.py` | §6: `S₃`, `Σ\|T(x)\|`, the von Neumann bound and `B₃` side by side. |
| `arith.py`, `arith2.py` | §7: the bias of the top sets of arithmetic coefficients, and its growth in `q`. |
| `cap4.py` | §7: the extremisers against their fourth-moment cap, and `ρ_E`. |
| `sparse_ls.py` | §7: the largest `s₁²` against `\|W\|` at fixed `q`. |
| `blocks.py` | §8: the counts, fourth-moment shares and sixth moments of the block sums at `x = q^{7/18}`. About a minute to `q = 3·10⁷`. |
| `blocks_s3.py` | §8: `S₃` and `λ_max(G)/N` on the genuine critical set, against random sets. |
| `shifts.py` | §§9–10: the split of the count into the diagonal, the singular series and the shifted-convolution error; `--z`, `--e` set the signature. About ten minutes. |
| `kuznetsov.py` | §11: the exponents that Deshouillers and Iwaniec's Theorem 12 gives for the sum of §10, for both placements of `q`. |
