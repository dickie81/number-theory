# The evaporation rate of the orbit form: witness level, approach, rate

**Lean:** `BallRate` (`lib/core/BallRate.lean`), printed by `lib/check/CheckAll.lean`, with `BallSampling`,
`BallDensity` and `BallCutoff` in the last three sections. The theorems are mapped onto the gravastar language in the
section after the statements; the first section, written before the Lean, fixes the three statements and says what each
costs. The rate, open when that section was written, is now proved under RH alone: `λ_N ≥ 1/(200e²⁴N)` for every
`N ≥ 1` (`BallCutoff.rate_cut`, last section). It comes from the sampling conjecture of the section "What is missing",
which `BallCutoff.sampling_rh` proves under RH with `c = 1/100` and `C = e²⁴`.

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
with its numerics, is stated in the section "What is missing". A Gaussian-smoothed form of it, at height
`T₀ ≍ N log²N`, is now proved from the explicit formula under RH and gives `λ_N ≥ 10⁻¹²/(N log³N)`
(`BallDensity`). The sharp-cutoff form itself, with `c = 1/100` and `C = e²⁴`, is proved under RH too and gives
`λ_N ≥ 1/(200e²⁴N)` (`BallCutoff`, last section).

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
`SamplingAtZeros` is a named hypothesis, with no proof in the module (`BallCutoff.sampling_rh`, last section, proves
it under RH at `θ = 0`). All ten printed theorems depend on `propext`,
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
whose density `(1/2π)log(T/2π)` exceeds the Nyquist density `(1/2π)log N` of a polynomial of length `N` only by
`(1/2π)log(T/2πN)`, a constant for `T ≍ N`: a Marcinkiewicz–Zygmund inequality at essentially the critical density, which for a general separated sequence fails
(Beurling–Landau) and for the zeros would have to come from their arithmetic, Landau's formula
`Σ_{0<γ≤T} x^{iγ} = −(T/2π)Λ(x)/√x + O(…)` with a pair-correlation input. That is the inequality on `|V_x(ρ)|` that the
rate is missing; the numbers above say it is true on the vectors that matter, with explicit constants, and that
nothing below height `N` or above `100N` is involved. Under RH the conjecture is now a theorem, with
`(c, C) = (1/100, e²⁴)` (`BallCutoff.sampling_rh`, last section).

## The rate from the gaps between the zeros (`BallSampling`)

**Lean:** `BallSampling` (`lib/core/BallSampling.lean`), printed by `lib/check/CheckAll.lean`; the nine results
depend on `propext`, `Classical.choice` and `Quot.sound` only. This is statement 3B with a zero-spacing hypothesis in
place of `SamplingAtZeros`: the sampling inequality, and a lower bound for `λ_N`, from the gaps between the zeros.

| Theorem | Statement | Conditional on |
|---|---|---|
| `BallSampling.meanValue` | for `D(t) = Σ_{j ≤ N} c_j j^{−it}`, `\|∫_a^b \|D\|² − (b − a)Σ\|c_j\|²\| ≤ 2N²Σ\|c_j\|²` | nothing |
| `BallSampling.cells_bound` | for `F` with a continuous derivative and a point `γ_j` in each cell `[T₁ + jh, T₁ + (j + 1)h]`, `∫\|F\|² ≤ 2hΣ_j\|F(γ_j)\|² + 2h²∫\|F'\|²` | nothing |
| `BallSampling.exists_sampling` | if every `[u, u + 1/(1 + log N))` with `T₁ ≤ u ≤ T₁ + L` holds the ordinate of a zero (`GapsOn N T₁ L`) and `L ≥ 12N² + 1`, the zeros of `[T₁, T₁ + L]` have `Σ\|V_x(ρ)\|² ≥ (L − 1)(1 + log N)/8·Σ x_n² n` | RH and `GapsOn N T₁ L` |
| `BallSampling.rate_of_gaps` | `GapsOn N T₁ T₁` with `T₁ ≥ 12N² + 2` gives `λ_N ≥ (1 + log N)/(80T₁)` | RH and `GapsOn N T₁ T₁` |
| `BallSampling.rate_of_zeroGaps` | `ZeroGaps g u₀` (from `u₀` on, every `[u, u + g(u))` holds an ordinate), `T₁ ≥ max(u₀, 14N²)` and `g ≤ 1/(1 + log N)` from `T₁` on give `λ_N ≥ (1 + log N)/(80T₁)` | RH and `ZeroGaps g u₀` |
| `BallSampling.rate_of_gapsLog` | `g = K/log u`: `T₁ = max(u₀, (eN)^K, 14N²)`, a **polynomial** rate, `λ_N ≥ (1 + log N)/(80e^K N^K)` for `K > 2` and `N` large | RH and `ZeroGaps (K/log u) u₀` |
| `BallSampling.samplingAtZeros_of_gapsLog` | for `K ≥ 2` the same hypothesis gives `BallRate.SamplingAtZeros (1/32) (2e^K·max(u₀, 13)) (K − 1)` | RH and `ZeroGaps (K/log u) u₀` |
| `BallSampling.rate_of_gapsSqrt` | `g = K/√(log u)`: `T₁ = max(u₀, e^{K²(1 + log N)²}, 14N²)`, a **quasi-polynomial** rate | RH and `ZeroGaps (K/√(log u)) u₀` |
| `BallSampling.rate_of_gapsLogLog` | `g = K/log log u`: `T₁ = max(u₀, e^{e^{K(1 + log N)}}, 14N²)`, so `λ_N ≥ (1 + log N)e^{−e^K N^K}/80` | RH and `ZeroGaps (K/log log u) u₀` |

**How it is proved.** Under RH, `V_x(ρ) = Σ x_n√n·n^{iγ}` is the conjugate of `D(γ)` with `c_n = x_n√n`
(`dpoly_eq_conj`), and `Σ|c_n|² = Σ x_n² n`. Multiplying by `e^{iκt}`, `κ = ½ log N`, centres the frequencies in
`[−κ, κ]` and keeps the modulus (`dcen`). Cut `[T₁, T₁ + L]` into `J` cells of length `h = 1/(1 + log N)` and take a
zero in each: on a cell, `|F(t)| ≤ |F(γ)| + ∫_cell|F'|` by the fundamental theorem of calculus, and Cauchy–Schwarz
(`sq_integral_le`) gives `∫_cell|F|² ≤ 2h|F(γ)|² + 2h²∫_cell|F'|²`. The mean value theorem bounds
`∫|F|² ≥ (Jh − 2N²)Σ|c|²` and `∫|F'|² ≤ (Jh + 2N²)κ²Σ|c|²`, and `2h²κ² ≤ ½`; so `Σ_{cells}|V(ρ)|² ≥ JΣ|c|²/8` once
`Jh ≥ 12N²`. The off-diagonal terms of the mean value theorem are at most `2/|log j' − log j| ≤ 2N` each, which costs
the error `2N²` (Montgomery and Vaughan's `O(Σ n|c_n|²)` would do better, and only changes the side conditions). On
the window `[T₁, 2T₁]` the weight of `Q_N` is `1/(¼ + γ²) ≥ 1/(5T₁²)`, which gives `(1 + log N)/(80T₁)`.

**The three gap hypotheses**, each a bound for the largest gap between consecutive zeros near height `u`:

- **`K/log u`**: gaps at most `K/2π` times the mean spacing `2π/log(u/2π)`; it gives the polynomial rate
  `λ_N ≫ N^{−K}`. It is not known to fail, but it is believed false for every fixed `K`: in the random-matrix model
  the largest normalised gap among `n` eigenvalues grows like `√(32 log n)/2π` (G. Ben Arous and P. Bourgade, Ann.
  Probab. 41 (2013), for the unitary ensembles), and the zeros are expected to follow the model.
- **`K/√(log u)`**: the size of the largest gaps that the model predicts near height `u`, about `√(32 log u)/log u`;
  expected for every `K > √32` from some height on. It gives `λ_N ≫ e^{−K²(1 + log N)²} = e^{−K²}N^{−K²(log N + 2)}`:
  quasi-polynomial.
- **`K/log log u`**: what is known under RH (J. E. Littlewood, 1924: the gaps are `O(1/log log u)`; E. C. Titchmarsh,
  *The Theory of the Riemann Zeta-Function*, ch. XIV), so this hypothesis holds under RH for some `K` and `u₀`; it is
  not proved in this library. It gives `λ_N ≫ e^{−e^K N^K}`. The next section's `λ_N ≥ 10⁻¹²/(N log³N)` also
  has RH as its only deep input, and it is far stronger.

**What this says about the rate.** The method needs a zero in *every* cell of length `≍ 1/log N` at height `T₁`,
where the mean spacing is `2π/log T₁`: it forces `log T₁ ≳ 2π·(largest normalised gap)·log N`. So bounded normalised
gaps give a polynomial rate, the model's growing gaps a quasi-polynomial one, and Littlewood's bound a doubly
exponential one, against the observed `0.048·log N/N`. A polynomial rate needs a sampling theorem of Beurling–Landau
type, which asks for the right *density* of zeros on windows rather than a zero in every cell. The numerics of the
previous section say the truth is such a density statement at `T ≍ N`, where the zeros exceed the Nyquist density of
the polynomial only by `(1/2π)log(T/2πN)`. The next section proves one, with the explicit formula supplying the
density.

## The rate from the density of the zeros (`BallDensity`)

**Lean:** `BallDensity` (`lib/core/BallDensity.lean`), printed by `lib/check/CheckAll.lean`. The five results depend on
`propext`, `Classical.choice` and `Quot.sound` only. The previous section needs a zero in every short cell. This one
needs only the density of the zeros, which Weil's explicit formula supplies (`WeilForm.weilExplicit_zeta`, proved with
no RH input). It proves the rate with RH as the only hypothesis.

| Theorem | Statement | Conditional on |
|---|---|---|
| `BallDensity.mertens_le` | `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 4` | nothing |
| `BallDensity.landau_le` | for every real `b`, `2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤ (log N + log 4 + 4)Σ_{j ≤ N} b_j²` | nothing |
| `BallDensity.weil_htest` | Weil's explicit formula for `h(z) = D(z)D(−z)(w(z − T₀) + w(z + T₀))`, with `D(z) = Σ_{j ≤ N} c_j e^{−iz log j}` and `w(z) = e^{−z²/(2σ²)}` | nothing |
| `BallDensity.density_bound` | for `σ² ≥ 16N`, `T₀ ≥ 16` and `L₀ = log(T₀/4π) − 3 ≥ 0`, with `c_n = x_n√n`: `(σ√(2π)/π)(L₀ − log N − log 4 − 4)Σc_n² − errD·(Σ\|c_n\|)² ≤ 2(1 + 2T₀² + 4σ²)Q_N(x)` | RH |
| `BallDensity.rate_rh` | `Q_N(x) ≥ Σ x_n²/(10¹²N log³N)` for every `N ≥ 3`, so `λ_N ≥ 10⁻¹²/(N log³N)` | RH |

The error coefficient `errD` (`BallDensity.errD`) has four parts. With `E₁ = 2σ√(2π)e^{−σ²/16N²}` they are:

- the pole term `2N²e^{1/2σ²}W(0)`;
- the near-diagonal terms of `∫|D|²W`, `(L₀/2π)E₁N²`;
- the archimedean tail `((L₀ + 9)/2π)e^{−T₀²/16σ²}·2√2σ√(2π)`;
- the near misses of the prime side, `(π/3)E₁N²`.

All four are Gaussian-small once `σ ≫ N√(log N)` and `T₀ ≫ σ√(log N)`.

**How it is proved.** Under RH, `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)`. Also `V_x(ρ)` is the conjugate of `D(γ)` with
`c_n = x_n√n` (`BallSampling.dpoly_eq_conj`). The test function `h` is entire and even. On the real line it is real,
`h(t) = |D(t)|²W(t)` with `W = w(· − T₀) + w(· + T₀)`. On `|Im z| ≤ 1` it satisfies
`|h(z)| ≤ (NS₁)²e^{1/2σ²}W(Re z)`, where `S₁ = Σ|c_n|`. So the explicit formula applies (`weil_htest`).

- **Zero side.** Under RH `h(t_ρ) = |V_x(ρ)|²W(γ)` (`zero_term_eq`). Since `W(γ)(1 + γ²) ≤ 2(1 + 2T₀² + 4σ²)`
  (`Wd_mul_le`), the zero side is at most `2(1 + 2T₀² + 4σ²)Q_N(x)` (`zero_side_le`).
- **Fourier side.** `|D(t)|² = Σ_{j,j'} c_j c_{j'} cos((log j' − log j)t)` (`Kc_eq`). The Gaussian cosine transform
  is `∫W(t)cos(vt) dt = Ŵ(v) = 2σ√(2π)e^{−σ²v²/2}cos(T₀v)` (`integral_gw_cos`, from Mathlib's
  `integral_cexp_quadratic`). Together they give `g_h(u) = (1/2π)Σ_{j,j'} c_j c_{j'}Ŵ(log j' − log j − u)`
  (`gh_htestR`).
- **Exact matches and near misses.** At `u = log n` the pairs with `j' = jn` give `Ŵ(0)Σ_{jn ≤ N} c_j c_{jn}`. Every
  other pair has `|log j' − log(jn)| ≥ 1/(2N)` (`sep_log`), and at least `log(n/N)` once `n > N`. So when
  `σ² ≥ 16N` its Gaussian is at most `e^{−σ²/16N²}N²/n²` (`near_miss_le`, `sum_What_log_sub`). At `n = 1` this is
  the diagonal of `∫h` (`integral_htestR_ge`).
- **Prime side.** The exact matches give Landau's form `(Ŵ(0)/2π)·2Σ_n Λ(n)n^{−1/2}Σ_{jn ≤ N} c_j c_{jn}`. Schur's
  test with the weights `j^{−1/2}` bounds it by `(Ŵ(0)/2π)(log N + log 4 + 4)Σc_n²` (`landau_le`). The test uses
  `b_j b_{jn}/√n ≤ ½(b_j²/n + b_{jn}²)`, then Mertens' bound for `n ≤ N/j`, then `Σ_{n ∣ m} Λ(n) = log m`; the two
  `log j` terms cancel. Mertens' bound itself (`mertens_le`) comes from `Σ_{m ≤ M} log m = Σ_n Λ(n)⌊M/n⌋ ≤ M log M`
  and Chebyshev's `ψ(M) ≤ (log 4 + 4)M` from Mathlib. The near misses are summable against `Λ(n)/√n ≤ 2` and
  `Σ 1/n² = π²/6` (`prime_le`).
- **Archimedean side.** `−g_h(0)log π + (1/2π)∫h Re ψ(¼ + ir/2)` equals `(1/2π)∫h·(Re ψ − log π)`. Stirling
  (`DigammaStirling.re_digamma_quarter`) gives `Re ψ(¼ + ir/2) − log π ≥ log(T₀/4π) − 3` on `|r| ≥ T₀/2`
  (`psiRe_good`), and `≥ −9` everywhere (`psiRe_sub_log_pi_ge`). Away from `±T₀` the window is below
  `e^{−T₀²/16σ²}` times a Gaussian of width `√2σ` (`gw_tail`, `arch_ge`). This term is the density
  `(1/2π)log(t/2π)` of the zeros against `|D|²W`.
- **Pole term.** `h(i/2) + h(−i/2)` is at least `−2(NS₁)²e^{1/2σ²}W(0)`, with `W(0) = 2e^{−T₀²/2σ²}` (`pole_ge`).

Summing these, the density term `(Ŵ(0)/2π)L₀Σc_n²` beats Landau's `(Ŵ(0)/2π)(log N + log 4 + 4)Σc_n²` once
`log(T₀/4π) − 3 > log N + log 4 + 4`. That is `T₀ > 16πe⁷N ≈ 5.5·10⁴N` (`density_bound`). `rate_rh` takes
`σ = 32N log N` and `T₀ = 10⁶N log²N`. Then:

1. The margin is at least `2`, from `e⁹ < 8104`.
2. `N·errD ≤ σ/2` (`errD_le`), since every error carries a factor `N^{−64}`.
3. `(Σ|c_n|)² ≤ NΣc_n²` and `Σc_n² ≥ Σx_n²`.
4. `2(1 + 2T₀² + 4σ²) ≤ 10¹²N log³N·σ`.

**What this says.** The density of the zeros near height `T`, `(1/2π)log(T/2π)`, must exceed the bandwidth
`(1/2π)log N` of a polynomial of length `N` by Landau's arithmetic term, `(1/2π)(log 4 + 4 + O(1))`. That is the
Beurling–Landau condition for these polynomials, and the explicit formula proves it sufficient. The density condition
alone asks only `T₀ ≍ N`, as the numerics of the section "What is missing" predicted (`T ≍ 8N`). The window has to
resolve frequencies `1/N` apart with Gaussian accuracy, which needs width `σ ≫ N√(log N)`, and its tails must miss the
low zeros, which needs `T₀ ≫ σ√(log N)`. The weight `1/(¼ + γ²)` at height `T₀` costs `1/T₀²` against the gain `σ`,
so this method gives at best `1/(N log^{3/2}N)`. `rate_rh` takes `σ = 32N log N` and `T₀ = 10⁶N log²N` to keep the
arithmetic simple, and gets `1/(N log³N)`. Against the observed `0.048·log N/N`, the exponent of `N` is right and the
power of `log N` is four too low. What is proved here is the Gaussian-smoothed form of the sharp-cutoff conjecture
`SamplingAtZeros c C 0`, at `T ≍ N log²N`. The next section proves the conjecture itself with a different test
function, and removes all but one factor `log N` from the gap.

## Sampling at the zeros up to height `T ≍ N` (`BallCutoff`)

**Lean:** `BallCutoff` (`lib/core/BallCutoff.lean`), printed by `lib/check/CheckAll.lean`. The four results depend on
`propext`, `Classical.choice` and `Quot.sound` only. This section proves the conjecture of the section "What is
missing" under RH, with explicit constants. With it comes the rate at the Nyquist exponent with no logarithm.

| Theorem | Statement | Conditional on |
|---|---|---|
| `BallCutoff.weil_htC` | Weil's explicit formula for `h(z) = D(z)D(−z)Φ(z)`, with `D(z) = Σ_{j ≤ N} c_j e^{−iz log j}` and the minorant `Φ(r) = (r/T)²(1 − (r/T)²)sinc⁶(br/T)`, `sinc x = sin x/x`, for `0 < b ≤ T` | nothing |
| `BallCutoff.integral_Kc_majR_le` | for `r ≥ 8`, `∫\|D(t)\|²M_r(t) dt ≤ (π²/2)Σ_{j ≤ N}(r + 8j)c_j²`, with `M_r(t) = (r/t)²sin²(πt/2r) ≥ 1` on `[−r, r]` | nothing |
| `BallCutoff.sampling_rh` | `BallRate.SamplingAtZeros (1/100) e²⁴ 0`: for every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ e²⁴N`, `Σ_{\|γ_ρ\| ≤ T}\|Σ_{n ≤ N} x_n n^ρ\|² ≥ (T/100)Σ_{n ≤ N} x_n² n` | RH |
| `BallCutoff.rate_cut` | `Q_N(x) ≥ Σ x_n²/(200e²⁴N)` for every `N ≥ 1`, so `λ_N ≥ 1/(200e²⁴N)` | RH |

**How it is proved.** The test function is `h(t) = |D(t)|²Φ(t)` with `c_n = x_n√n`, at `b = 6`.

- **The minorant.** On `|r| ≤ T`, `0 ≤ Φ(r) ≤ min((r/T)², ¼)` (`phiR_bounds`). On `|r| ≥ T`, `Φ(r) ≤ 0` and
  `|Φ(r)| ≤ T²/(b⁶r²)` (`phiR_tail`). So under RH the zero side `Σ_ρ |V_x(ρ)|²Φ(γ)` is at most
  `¼Σ_{|γ| ≤ T}|V_x(ρ)|²` (`zero_term_cut`, `zero_side_cut`).
- **Its transform.** Put `β = b/T`. Then `Φ(r)` is a combination of `(1 − cos 2βr)ĝ₁(r)²` and
  `(3 − 4cos 2βr + cos 4βr)ĝ₀(r)²`. Here `ĝ₀(r) = 2sin(βr)/r` is the transform of the box `1_{[−β, β]}` and
  `ĝ₁ = ĝ₀²` that of the triangle, its autocorrelation. So the cosine transform `Φ̂` is an explicit combination of the
  autocorrelations of the box and the triangle (`integral_phiR_cos`). It is supported in `|v| ≤ 6β`
  (`phihat_eq_zero`), and `Φ̂(0) = πT(2b² − 3)/(8b⁵)` (`phihat_zero`), from the triangle's autocorrelation `16β³/3` at
  `0` and `4β³/3` at `2β`.
- **Exactness.** For `T > 12bN` the support `6b/T` is below `1/(2N)`. Every pair with `j' ≠ jn` has
  `|log j' − log(jn)| ≥ 1/(2N)` (`BallDensity.sep_log`), so only the exact matches `j' = jn` survive. The diagonal is
  exact, `∫|D|²Φ = Φ̂(0)Σc_n²` (`integral_hRC`). The prime side is exactly Landau's form, at most
  `(Φ̂(0)/2π)(log N + log 4 + 4)Σc_n²` (`prime_le_cut`, from `BallDensity.landau_le`). Nothing is approximated.
- **The pole.** `Φ` vanishes to second order at `0`, and `‖Φ(i/2)‖ ≤ 1/T²` (`phiC_I_half_le`). So the pole term is at
  least `−2NΣc_n²` (`pole_ge_N`).
- **The archimedean side.** It is `(1/2π)∫|D|²Φ·L`, with `L(t) = Re ψ(¼ + it/2) − log π`. Compare `L` with
  `L₁ = log(T/16π) − 3`, its floor on `|t| ≥ T/8`. The defect `Φ(L − L₁)` is at least `−W` (`phiR_mul_L_ge`), where
  `W` has three parts:
  - the low-height majorant `M_{T/8}/256`. On `|t| < T/8`, `Φ ≤ (t/T)²`, `L₁ − L ≤ log(T/8|t|)` (Stirling), and
    `(t/T)²log(T/8|t|) ≤ 1/256` (`low_le`);
  - the dyadic shells `ε_i M_{2^{i+1}T}`, with `ε_i = (i + 20)/(b⁶4^i)`, on `2^i T < |t| ≤ 2^{i+1}T` for `i < 2J`.
    There `|Φ| ≤ 4^{−i}/b⁶` and `L − L₁ ≤ i + 20` (`shell_ge`);
  - the far weight `(21T√T/b⁶)|t|^{−3/2}` beyond `4^J T` (`far_ge`, `integral_farW`).

  `M_r` is a Fejér kernel. Its transform `(πr²/2)(π/r − |v|)⁺` is supported in `|v| < π/r`. A Schur test and the count
  `#{j' ≤ N : |log j' − log j| < π/r} ≤ 1 + (12/5)(π/r)j` (`card_near_le`) give the mean-value bound
  `∫|D|²M_r ≤ (π²/2)Σ_j (r + 8j)c_j²` (`integral_Kc_majR_le`). The shells sum to at most
  `(π²/2)(84T + 336N)Σc_n²/b⁶` (`sum_epsS_le`). `J = N + 10` makes the far weight negligible against
  `|D|² ≤ (Σ|c_n|)² ≤ NΣc_n²`.

Summing these at `b = 6`, with `Φ̂(0)/2π = 69T/124416` and `log(T/N) ≥ 24`, gives
`¼Σ_{|γ| ≤ T}|V_x(ρ)|² ≥ (69T/124416)(log(T/N) − log 64π − 7)Σc_n² − 0.0018TΣc_n² − O(NΣc_n²)`. That is at least
`0.0045TΣc_n²` (`cutoff_bound`), and `Σc_n² = Σx_n²n`. Then `rate_of_sampling` gives `rate_cut`.

**What this says.** Under RH, the zeros up to height `T` sample the Dirichlet polynomials of length `N` once
`T ≥ e²⁴N`. This is the Marcinkiewicz–Zygmund inequality at a constant multiple of the Nyquist density, which the
section "What is missing" observed (`c ≈ 0.1` at `C = 8`) and conjectured. The constants are far from optimal:
`e²⁴ ≈ 2.6·10¹⁰`, against the observed `8`. The shape is right, though. `λ_N ≥ 1/(200e²⁴N)` has the Nyquist exponent
and no logarithm, against the observed `0.048·log N/N`; one factor `log N` is missing. Two properties of the test
function account for the gain over `BallDensity`:

- Its transform has compact support, so the diagonal and the prime side are exact, not Gaussian-approximate. That
  removes the window width `σ ≫ N√(log N)`.
- It vanishes to second order at `0` and changes sign at `T`. So the zeros up to `T` are counted with weight at most
  `¼`, and the pole and the low heights of the archimedean term cost `O(NΣc_n²)` and `O(TΣc_n²)`, with no `log T`.
  The weight `1/(¼ + γ²)` then costs `1/T² ≍ 1/N²` against the gain `T ≍ N`.
