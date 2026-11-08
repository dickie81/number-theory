# Chen–Gupta–Li's 7/3 at prime moduli: the S₃ term

Status labels: **Written proof** (argued here; not machine-checked, not refereed), **Numerical**, **Conjecture**.
Prepared with AI assistance; needs expert review. The scripts are in `scripts/cgl_s3/` (numpy and sympy).

## The question

B. Chen, V. Gupta and Y. C. Li (arXiv:2507.08296v2) prove `Σ_{χ mod q} N(σ, T, χ) ≤ (qT)^{(7/3)(1−σ)+o(1)}` for every
`q`. The library formalises it on `[5/7, 16/21]` (`LinnikCGLDensity.cglDensity`, see
[`formalisations/chen-gupta-li-density.md`](../formalisations/chen-gupta-li-density.md)). For `q` with a factor of a
suitable size their method gives Guth and Maynard's `30/13`; the exponent `7/3` comes from prime `q` at `T = 1`.

Their Remark 12.3 names the critical case: `σ = 5/7`, a detector polynomial of length `N = q^{7/9}`, and a set `W` of
`|W| = q^{2/3}` characters, where the binding inequality is their bound `S₃ ⪅ (qT)²|W|^{3/2}`. In their words, this
term "corresponds to square root cancellation in the R functions but no cancellation in the sums over m. To improve this
term, we would need to find some joint cancellation in R and the m sums, which seems quite difficult."

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

  The zero detector's bias grows faster than the allowance of §5. So the conditional route of §5 probably fails for
  exactly the polynomials the density argument uses.

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
