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
proves it stays bounded. The obstruction is now specific: large-values sets clustered on characters that agree on small
rationals, the prime-modulus analogue of the clustering in `t` that Guth and Maynard remove by subdividing `[0, T]`.

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
