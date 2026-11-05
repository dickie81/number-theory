# The evaporation rate of the orbit form: witness level, approach, rate

**Lean:** `BallRate` (`lib/core/BallRate.lean`), printed by `lib/check/CheckAll.lean`. The theorems are mapped onto the
gravastar language in the section after the statements; the first section, written before the Lean, fixes the three
statements and says what each costs.

## The three statements, and what can be proved

**Setting.** `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n)` is `BallWeil.form N x`, with `K_H` computed from the primes
(`BallWeil.kψ`, equal to `BallHadamard.kerH` on `x > 0`): `K_H(r) = Σ_ρ r^{ρ−½}/(ρ(1 − ρ))` over the nontrivial zeros
with multiplicity, `K_H(1) = H₀ := 2 + γ_E − log 4π ≈ 0.0462`. Write `a_ρ = 1/(ρ(1 − ρ))`, so `Σ_ρ a_ρ = H₀` and every
`Re a_ρ > 0`; and `λ_N = min{Q_N(x) : Σ x_n² = 1}`, the smallest eigenvalue of the Gram matrix `G_N`. Then
`Q_N(x) = Σ_ρ a_ρ V_x(ρ) V_x(1 − ρ)` with `V_x(s) = Σ_{n ≤ N} x_n n^s`, which under RH is `Σ_ρ |V_x(ρ)|²/(¼ + γ²)`.
Numerically (`scripts/ball_rate.py`, with the first 30000 zeros from `scripts/zeta_zeros_rs.py`):
`λ_N = (0.048 ± 0.002)·log N/N` for `100 ≤ N ≤ 2000`; the minimising vector is
`x_n ≈ (1 − n/N)²/ψ(n)` with `ψ` Dedekind's function `n Π_{p ∣ n}(1 + 1/p)`, within a factor `2.2`–`2.5` in the
Rayleigh quotient; and the first zero moved to `½ + δ ± iγ₁` makes `G_N` indefinite from `N = 512` for `δ = 0.05` and
`N = 1024` for `δ = 0.02` (among powers of two).

### 1. Witness level ("evaporation in finite time")

**Statement 1A (witness level, explicit, for a dominant crossing).** Let `ρ₀ = β + iγ` be a nontrivial zero with
`β > ½`, `γ > 0`, `δ = β − ½`, `a₀ = a_{ρ₀}`, and let `S₀` be the four zeros `ρ₀, ρ̄₀, 1 − ρ₀, 1 − ρ̄₀` (with their
multiplicities). Say `ρ₀` is **dominant** when (i) every zero `ρ` has `|Re ρ − ½| ≤ δ` and (ii) the other off-line
zeros weigh less: `M := Σ_{ρ ∉ S₀, Re ρ ≠ ½} |a_ρ| < 2|a₀|`. Then, with
`Λ = (1/2δ)·log((4H₀ + 4|a₀| + M)/(2|a₀| − M))`, `q₀ = ⌈6γ/π⌉`, `p₀ = ⌈q₀ e^{λ*}⌉` for the first `λ* ≥ Λ` at which
`2γλ* + arg a₀ ≡ π (mod 2π)` (so `Λ ≤ λ* < Λ + π/γ`), the vector `x = q₀δ_{p₀²} + p₀δ_{q₀²}` has `Q_{p₀²}(x) < 0`:

> `witness_level : Dominant ρ₀ → p₀² ≤ N₀(ρ₀) ∧ Q_{p₀²}(q₀δ_{p₀²} + p₀δ_{q₀²}) < 0`, with
> `N₀(ρ₀) = (⌈6γ/π⌉·⌈e^{Λ + π/γ}⌉ + 1)²`.

A **single crossing** (every zero outside `S₀` on the line) is dominant with `M = 0`, so
`N₀(β, γ) = (⌈6γ/π⌉·⌈e^{π/γ}·((2H₀ + 2|a₀|)/|a₀|)^{1/2δ}⌉ + 1)²`; with `|a₀| ≈ 1/γ²` this is about
`(2γ)²·(0.1γ²)^{1/δ}`: for `γ = 14.13`, `Λ = 30.2, 75.5, 151` and `N₀ ≈ 10^{29}, 10^{69}, 10^{134}` at
`δ = 0.05, 0.02, 0.01`, against the levels `512` and `1024` seen numerically.

*Feasibility.* Provable now, from the library's twin sum: the test vector is the `2 × 2` minor at `(p₀², q₀²)`,
whose value is `p₀²q₀²·Re W(log(p₀/q₀))` with `W(λ) = Σ_ρ a_ρ(2 + e^{λP_ρ} + e^{−λP_ρ})`, `P_ρ = 2(ρ − ½)`
(`BallHadamard.twin_eq_kerH`, `BallWeil.form_two`). The on-line zeros contribute at most `2H₀` whatever `λ` is, by
Hadamard's identity and `Re a_ρ > 0`, which is why the minor is the one test vector whose positive part is bounded
without knowing the zeros; the four zeros of `S₀` contribute `4|a₀|e^{2δλ}cos(2γλ + arg a₀) + O(|a₀|)`, and (i)–(ii)
bound the rest by `(e^{2δλ} + 1)M`. The level `p₀² ≈ e^{2Λ}` is exponential in `1/δ`, where the numerical first witness
is `≈ 25/δ`: the eigenvector resolves the zeros near height `γ` and pays only for them, the minor pays `2H₀` for all of
them. **What is not provable this way:** a level `N₀(β, γ)` for an arbitrary off-line zero. The argument that gives
`rh_of_posDefH` is Landau's theorem on the Laplace transform of the twin sum, which is not effective, and the obstruction
is real: zeros of the same real part at nearby heights carry comparable weights `≈ 1/γ²` and unknown phases, and no
spacing or local counting result excludes their cancelling `ρ₀` on any finite window. An unconditional effective
version is a Turán power-sum argument with local zero counts, a separate project; the hypothesis `Dominant` is what the
Landau mechanism can isolate, and it is a hypothesis on the zeros, not on RH.

**Statement 1B (collapse, with any rate).** If `λ_N ≥ −ε(N)` for infinitely many `N` with `ε(N) → 0`, then RH
(`rh_of_frequently_balanced`, re-proved from the `positivity-search` branch's `GravastarTower`), in particular for
`ε(N) = 1/N` at every level (`rh_of_excess_le_inv`). Together: a crossing with a dominant zero is seen at an explicit
finite level, and a crossing of any kind cannot hide in the limit. *Feasibility:* proved on the branch; re-proved
here, a hundred lines.

### 2. The approach ("time dilation")

**Statement 2A (the rate, with an explicit vector; conjectural).** For `x_n = (1 − n/N)²/ψ(n)`,
`Q_N(x) ≤ C·(log N/N)·Σ x_n²` with `C = 0.13`, so `λ_N ≤ 0.13·log N/N`. Numerically the constant is `0.112`–`0.120`
for `100 ≤ N ≤ 2000` and the quotient is `2.2`–`2.5` times `λ_N`, which is `0.048·log N/N`. *Why this vector:*
`Σ_n n^{−w}/ψ(n) = ζ(w + 1)·E(w)` with `E(w) = Π_p(1 − p^{−w}/(p(p + 1)))` absolutely convergent on `Re w > −1`, so
`V_x(s)` is the Riesz mean of order `2` of the series of `ζ(1 − s)E(−s)`; at a zero the main term vanishes, the cutoff
leaves `2E(0)N^ρ/(ρ(ρ + 1)(ρ + 2))` and a remainder, and `Σ_ρ |·|²/|ρ|²` of the first is `≍ N·Σ_ρ |ρ|^{−8}`.
*Feasibility:* the remainder, summed over the zeros with the weights `|ρ|^{−2}`, needs mean-value estimates for
`ζ(ε + it)` at shifts of the zeros, which the library does not have; the vector with a sharp cutoff (`1/ψ(n)`, or
`1/n`) has `Q_N ≈ 7.6·10^{−5}·N`, so the smoothing is essential and the proof is the analytic part. Left as a
conjecture with the constant checked to `N = 2000`.

**Statement 2B (the approach, unconditional, no rate).** `lim sup λ_N ≤ 0`: for every `ε > 0` there is `N₀` with
`λ_N ≤ ε` for all `N ≥ N₀`, by an explicit test vector (`approach`). Under RH the two-point vector `x = δ_n − √n·δ_1`
has `Q_N(x) = 2n(H₀ − K_H(n))`, `Σ x² = n + 1`, and `H₀ − K_H(n) = Σ_ρ (1 − cos(γ log n))/(¼ + γ²)`
(`BallHadamard.kerH_second_diff`); choosing `n` with `γ_j log n` within `η` of `2πℤ` for the finitely many zeros that
carry all but `ε/8` of the weight (simultaneous Dirichlet approximation on the ordinates, `exists_simultaneous`) makes
this `≤ ε/2`. If RH fails, some level has a negative vector and negativity persists upward. *Feasibility:* proved,
about three hundred lines; the vector is explicit given the first `J(ε)` ordinates and the level is not, the price of
not using the arithmetic that 2A uses.

### 3. The rate (under RH; the open one)

**Statement 3A (the models).** With Lebesgue measure for the zeros (`BallFlat`: Gram matrix `H₀·min(m, n)`),
`λ_N ≥ H₀/4` for every `N`, by the telescoping identity `Σ x_m x_n min(m, n) = Σ_k (Σ_{n ≥ k} x_n)²`
(`flat_margin`, proved). With the zeros replaced by their **density** `(1/2π)log(|t|/2π)` on `|t| ≥ 2π`,
`λ_N = 0.0505 − O(10^{−4})` for `N ≤ 400`, the minimiser being `δ_1` to within `0.3%`: a uniform margin, as claimed,
but not a Toeplitz statement (the points are `log n`, not a grid, and the symbol's infimum is `0`); a proof needs a
multi-scale form of the Montgomery–Vaughan mean value theorem against the weight `log|t|/t²`, which the library's
`DirMean.mean_value` (an upper bound) does not give. Not attempted. With the zeros at their **mean positions** (the
`k`-th at the `t` with `(t/2π)log(t/2πe) + 7/8 = k`, the first `20000` of them, and the density beyond), `λ_N` decays
like `N^{−0.45}` for `N ≤ 400`: the discreteness alone sags, and the arithmetic doubles the exponent to
`N^{−1}log N`. So "the sag is arithmetic, not geometric" is half true: the continuous density has no sag, the
discrete picket fence has half of it.

**Statement 3B (the rate, under RH and a sampling hypothesis).** Say the zeros **sample at `(c, C, θ)`** when for
every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ C·N^{1+θ}`,
`Σ_{|γ_ρ| ≤ T} |V_x(ρ)|² ≥ c·T·Σ_{n ≤ N} x_n² n` (`SamplingAtZeros c C θ`). Then under RH, `λ_N ≥ (c/2C)·N^{−1−θ}`
for every `N ≥ 1` (`rate_of_sampling`): the sag is at most polynomial, `A = 1 + θ`. *Feasibility:* proved, from
`Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` under RH (`hasSum_form`, from `BallHadamard.realizationH`) and `¼ + γ² ≤ 2T²` on
`|γ| ≤ T`. The hypothesis is the Marcinkiewicz–Zygmund inequality for Dirichlet polynomials of length `N` at the zeros
up to height `C·N^{1+θ}`; by Beurling–Landau it needs `θ > 0` for a general sampling set of this density, and for the
zeros it would follow from Landau's formula `Σ_{0<γ≤T} x^{iγ} = −(T/2π)Λ(x)/√x + O(…)` with a pair-correlation input,
neither of which is in the library. The numerics are in the last section.

**Statement 3C (what is missing, as a conjecture).** The inequality on `|V_x(ρ)|` at the zeros that the rate needs,
with its numerics, is stated in the last section.

## The theorems, in the gravastar language

| Picture | Theorem | Statement | Conditional on |
|---|---|---|---|
| The tower's excess is monotone; exact balance at every level is RH | `BallRate.excess_mono`, `BallRate.rh_iff_balance` | `ExcessLe N' t → ExcessLe N t` for `N ≤ N'`; RH `↔ ∀ N, ExcessLe N 0` | nothing |
| **Collapse**: balance in the limit is exact balance | `BallRate.rh_of_frequently_balanced` | `(∀ δ > 0, ∃ᶠ N, ExcessLe N δ) → RH` | its hypothesis |
| Collapse at the rate `1/N` | `BallRate.rh_of_excess_le_inv` | `(∀ N, ExcessLe N (1/N)) → RH` | its hypothesis |
| A failure, once present, never heals | `BallRate.neg_persists` | `Q_N(x) < 0 → ∃ y, Q_{N'}(y) < 0` for `N' ≥ N` | nothing |
| **Witness level** of a dominant crossing | `BallRate.witness_level` | `Dominant ρ₀ → p₀² ≤ witnessLevel ρ₀ ∧ Q_{p₀²}(minorVec p₀ q₀) < 0` | `Dominant ρ₀`, a hypothesis on the zeros |
| Witness level of a single crossing, `N₀(β, γ)` | `BallRate.witness_level_single` | `SingleCrossing ρ₀ → ∃ N ≤ witnessLevel ρ₀, ∃ x, Q_N(x) < 0` | `SingleCrossing ρ₀` |
| **Approach**: the sag is real, `lim sup λ_N ≤ 0` | `BallRate.approach` | `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∃ x ≠ 0, Q_N(x) ≤ ε·Σ x²` | nothing |
| The form is a weighted sum over the zeros | `BallRate.hasSum_form` | `HasSum (ρ ↦ \|V_x(ρ)\|²/(¼ + γ²)) (Q_N(x))` | RH |
| **Rate**: the sag is at most polynomial | `BallRate.rate_of_sampling` | `(c/2C)·N^{−1−θ}·Σ x² ≤ Q_N(x)` | RH and `SamplingAtZeros c C θ` |
| The flat model does not sag | `BallRate.flat_margin`, `BallRate.flatForm_eq_kerFlat` | `(H₀/4)·Σ x² ≤ Σ x_m x_n H₀ min(m, n)`, the form of `BallFlat.kerFlat` | nothing |

`Dominant ρ₀` is `∀ ρ, |Re ρ − ½| ≤ Re ρ₀ − ½` and `offMass ρ₀ < 2|a_{ρ₀}|`; `SingleCrossing ρ₀` is `Re ρ = ½` for
every `ρ` outside the quadruple of `ρ₀`, and implies it (`dominant_of_single`). Both are statements about the zeros,
consistent with RH failing; nothing in the module assumes RH except `hasSum_form` and `rate_of_sampling`, and
`SamplingAtZeros` is a named hypothesis with no proof. All ten printed theorems depend on `propext`,
`Classical.choice` and `Quot.sound` only.

## How it was done

- **The twin sum.** `Re W(λ) = 2H₀ + Σ_q g_q(λ)` with `g_q(λ) = Re(a_q(e^{λP_q} + e^{−λP_q}))` (`re_Wsum`), from
  Hadamard's identity `Σ_q a_q = H₀` (`ZetaInputs.hadamard_zeta`). On the line `g_q ≤ 2Re a_q` (`gq_le_online`);
  within `δ` of the line `g_q ≤ |a_q|(e^{2δλ} + 1)` (`gq_le_offline`); the four zeros of the quadruple have the same
  `g_q` (`gq_quad`, by `riemannZeta_conj` and `riemannZeta_one_sub` they are zeros, and there are at least four of
  them, `four_le_card_quad`). Summing (`re_Wsum_le`, `quad_term_le`) gives
  `Re W(λ) ≤ 4H₀ − 8Re a₀ + 4|a₀|(e^{2δλ}cos(2γλ + arg a₀) + 1) + (e^{2δλ} + 1)M`, negative once `e^{2δλ}` passes
  `(4H₀ + 4|a₀| + M)/(2|a₀| − M)` and the cosine is at most `−½` (`re_Wsum_neg`). The `−8Re a₀` is what makes the
  inequality strict at `λ = Λ`.
- **The rational point.** `λ* = (π − arg a₀ + 2πk)/(2γ)` with `k = ⌈(2γΛ + arg a₀ − π)/2π⌉` (`lamStar_spec`),
  `q₀ = ⌈6γ/π⌉`, `p₀ = ⌈q₀e^{λ*}⌉`: `0 ≤ log(p₀/q₀) − λ* ≤ 1/q₀ ≤ π/6γ` (`log_pWit_div`), so the cosine at
  `log(p₀/q₀)` is at most `−½` (`cos_log_pWit`), and `Q_{p₀²}(q₀δ_{p₀²} + p₀δ_{q₀²}) = p₀²q₀²·Re W(log(p₀/q₀))`
  (`form_minorVec`, from `BallWeil.form_two` and `BallHadamard.twin_eq_kerH`).
- **The approach.** `exists_simultaneous`: for reals `α_1, …, α_J` and `Q ≥ 1`, some `1 ≤ m ≤ Q^J` has every `mα_i`
  within `1/Q` of an integer, by the pigeonhole principle on the `Q^J` boxes of `[0, 1)^J`
  (`Fintype.exists_ne_map_eq_of_card_lt`); `exists_near_two_pi`: for a finite set of zeros and `η > 0` some
  `n ≥ n₁` has every `γ_q log n` within `η` of `2πℤ`, with `u = 2πm/γ_{q₁}` and `n = ⌈e^u⌉`, `log n` being within
  `e^{−u}` of `u`; `exists_defect_le`: `H₀ − K_H(n) ≤ ε` from the head (`1 − cos θ ≤ θ²/2`, `one_sub_cos_le`) and
  the tail (`Σ_{q ∉ F} 1/(¼ + γ_q²) ≤ ε/8`, from the convergence of the partial sums to `H₀`).
- **The rate.** In the realization `BallHadamard.realizationH` the coordinate of `Σ x_n w_n` at `ρ` is
  `V_x(ρ)/|ρ(1 − ρ)|^{½}` (`coord_eq`), so `Q_N(x) = ‖Σ x_n w_n‖² = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` (`hasSum_form`); on the
  zeros of height at most `T` (`zerosUpTo T`, finite by `WeilLandau.finite_poleP`) the weight is at least `1/(2T²)`.
- **The flat model.** `min(m, n) = Σ_k [k ≤ m][k ≤ n]`, so the form is `Σ_k S_k²` (`sum_min_eq`);
  `x_n = S_n − S_{n+1}` and `Σ_{k ≤ N} S_{k+1}² + S_1² = Σ_{k ≤ N} S_k² + S_{N+1}²` (`sum_shift`) give
  `Σ x_n² ≤ 4Σ S_k²` (`sum_sq_le_four_tail`).

## The numerics (`scripts/ball_rate.py`, prime-side Gram matrices to `N = 2000`, the first 2000 zeros from mpmath and the first 30000 from `scripts/zeta_zeros_rs.py`; uncertified)

| Quantity | Values |
|---|---|
| `N·λ_N/log N` at `N = 100, 200, 400, 800, 1000, 1600, 2000` | `0.0509, 0.0489, 0.0485, 0.0481, 0.0480, 0.0478, 0.0476` |
| `C = q_N·N/log N` for `x_n = (1 − n/N)²/ψ(n)`, and `q_N/λ_N` | `0.112`–`0.120`; `2.21`–`2.51` |
| `H₀` against `Σ_ρ 1/(¼ + γ²)` over the first 2000 (30000) zeros plus the density tail | `0.046191` against `0.045307 + 0.000758 = 0.046065` (`0.046076 + 0.000103 = 0.046179`) |
| The moved first zero, `δ = 0.05, 0.02, 0.01`: `Λ`, `N₀`, `W(λ*)` | `30.2, 75.5, 151.0`; `10^{29.2}, 10^{68.6}, 10^{134.0}`; `−0.318, −0.341, −0.333` (the twin sum from the first 2000 zeros, tail `≤ 0.003`) |
| First indefinite level of the moved Gram matrix (powers of two) | `512` at `δ = 0.05`, `1024` at `δ = 0.02` |
| The sampling constant `c(T)` on the minimising vector of `G_N`, at `T = N, 2N, 4N, 8N, 12N`, for every `N = 100, …, 2000` | `6·10^{−4}, 2.2·10^{−3}, 1.3·10^{−2}, 0.10, 0.18` (each within `±15%` across `N`; the first 30000 zeros) |
| Share of `Q_N` on the minimiser carried by the zeros below `T = N, 2N, 4N, 8N, 12N`, for every `N` | `1.5%, 3%, 8%, 25%, 39%` (within `±1` point across `N`); below height `25755`: `93%` at `N = 100`, `42%` at `N = 2000` |
| The density model, `N = 50, 100, 200, 400` | `λ_N = 0.05046, 0.05046, 0.05045, 0.05045`, `K_dens(1) = 0.05063` |
| The picket fence, `N = 50, 100, 200, 400` | `λ_N = 0.0146, 0.0108, 0.0081, 0.0057` |

## What is missing: the sampling inequality at the zeros, and what the zeros say about it

The rate `λ_N ≥ c·N^{−A}` needs, under RH, a lower bound for `Σ_{|γ| ≤ T} |V_x(ρ)|²` in terms of `T·Σ x_n² n` with
`T` a power of `N`. With the first 30000 zeros (to height `25755`) the minimising vectors of `G_N`, the natural
adversaries, show a scaling law: on them `c(T) = Σ_{|γ| ≤ T}|V_x(ρ)|²/(T·Σ x_n² n)` and the share of `Q_N` carried
by the zeros below `T` depend on `T/N` alone, for every `N` from `100` to `2000`:

| `T/N` | `1` | `2` | `4` | `8` | `12` |
|---|---|---|---|---|---|
| `c(T)` | `6·10^{−4}` | `2.2·10^{−3}` | `1.3·10^{−2}` | `0.10` | `0.18` |
| share of `Q_N` below `T` | `1.5%` | `3%` | `8%` | `25%` | `39%` |

(and `93%` of `Q_{100}` below `T = 258·N`). So the minimiser's Dirichlet polynomial is nearly orthogonal to the zeros
below height `N`, where its length would let it resolve them, and spreads its weight over the zeros from `4N` to about
`100N`, where the zeros are sparser than its bandwidth: the rate `0.048·log N/N` is decided by the zeros at heights
`≍ 10N`–`100N`, not by the low zeros, and not by zeros beyond `N^{1+θ}` for any fixed `θ > 0` once `N` is large. The
sampling inequality is therefore plausible at `T ≍ N`: `SamplingAtZeros c C 0` holds on the minimisers with
`(c, C) = (0.013, 4)`, `(0.10, 8)` or `(0.18, 12)` uniformly in `N ≤ 2000`, and `rate_of_sampling` then gives
`λ_N ≥ (c/2C)/N`, e.g. `0.006/N` at `C = 8`, against the observed `0.048·log N/N`. The conjecture:

> The zeros sample at `(c, C, 0)` for some `C ≥ 1` and `c > 0`: for every `N ≥ 1`, every real `x` on `[1, N]` and
> every `T ≥ C·N`, `Σ_{|γ_ρ| ≤ T} |Σ_{n ≤ N} x_n n^ρ|² ≥ c·T·Σ_{n ≤ N} x_n² n`; numerically `c ≈ 0.1` at `C = 8`.

What a proof needs is a lower bound for a Dirichlet polynomial of length `N` sampled at the zeros of height `T ≍ 8N`,
whose density `(1/2π)log(T/2π)` is below the polynomial's bandwidth `log N` only by the constant `log 8`: a
Marcinkiewicz–Zygmund inequality at essentially the critical density, which for a general separated sequence fails
(Beurling–Landau) and for the zeros would have to come from their arithmetic, Landau's formula
`Σ_{0<γ≤T} x^{iγ} = −(T/2π)Λ(x)/√x + O(…)` with a pair-correlation input. That is the inequality on `|V_x(ρ)|` that the
rate is missing; the numbers above say it is true on the vectors that matter, with explicit constants, and that
nothing below height `N` or above `100N` is involved.
