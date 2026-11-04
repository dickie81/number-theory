# The evaporation rate of the orbit form: witness level, approach, rate

**Lean:** `BallRate` (`lib/core/BallRate.lean`), printed by `lib/check/CheckAll.lean`. The theorems are listed after the
statements; this section, written before the Lean, fixes the three statements and says what each costs.

## The three statements, and what can be proved

**Setting.** `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n)` is `BallWeil.form N x`, with `K_H` computed from the primes
(`BallWeil.kψ`, equal to `BallHadamard.kerH` on `x > 0`): `K_H(r) = Σ_ρ r^{ρ−½}/(ρ(1 − ρ))` over the nontrivial zeros
with multiplicity, `K_H(1) = H₀ := 2 + γ_E − log 4π ≈ 0.0462`. Write `a_ρ = 1/(ρ(1 − ρ))`, so `Σ_ρ a_ρ = H₀` and every
`Re a_ρ > 0`; and `λ_N = min{Q_N(x) : Σ x_n² = 1}`, the smallest eigenvalue of the Gram matrix `G_N`. Then
`Q_N(x) = Σ_ρ a_ρ V_x(ρ) V_x(1 − ρ)` with `V_x(s) = Σ_{n ≤ N} x_n n^s`, which under RH is `Σ_ρ |V_x(ρ)|²/(¼ + γ²)`.
Numerically (`scripts/ball_rate.py`): `λ_N = (0.048 ± 0.001)·log N/N` for `100 ≤ N ≤ 3200`; the minimising vector is
`x_n ≈ (1 − n/N)²/ψ(n)` with `ψ` Dedekind's function `n Π_{p ∣ n}(1 + 1/p)`, within a factor `2.3`–`2.6` in the
Rayleigh quotient; and a zero moved to `½ + δ ± iγ₁` makes `G_N` indefinite from `N ≈ 1000, 4000, 8000` for
`δ = 0.05, 0.02, 0.01` (the branch's `gravastar_margin.py`).

### 1. Witness level ("evaporation in finite time")

**Statement 1A (witness level, explicit, for a dominant crossing).** Let `ρ₀ = β + iγ` be a nontrivial zero with
`β > ½`, `γ > 0`, `δ = β − ½`, `a₀ = a_{ρ₀}`, and let `S₀` be the four zeros `ρ₀, ρ̄₀, 1 − ρ₀, 1 − ρ̄₀` (with their
multiplicities). Say `ρ₀` is **dominant** when (i) every zero `ρ` has `|Re ρ − ½| ≤ δ` and (ii) the other off-line
zeros weigh less: `M := Σ_{ρ ∉ S₀, Re ρ ≠ ½} |a_ρ| < 2|a₀|`. Then, with
`Λ = (1/2δ)·log((4H₀ + 4|a₀| + M)/(2|a₀| − M))`, `q₀ = ⌈6γ/π⌉`, `p₀ = ⌈q₀ e^{λ*}⌉` for the first `λ* ≥ Λ` at which
`2γλ* + arg a₀ ≡ π (mod 2π)` (so `Λ ≤ λ* ≤ Λ + π/γ`), the vector `x = q₀δ_{p₀²} + p₀δ_{q₀²}` has `Q_{p₀²}(x) < 0`:

> `witness_level : Dominant ρ₀ → ∃ N ≤ N₀(ρ₀), ∃ x, Q_N(x) < 0`, with `N₀(ρ₀) = (⌈6γ/π⌉·⌈e^{Λ + π/γ}⌉ + 1)²`.

A **single crossing** (every zero outside `S₀` on the line) is dominant with `M = 0`, so
`N₀(β, γ) = (⌈6γ/π⌉·⌈e^{π/γ}·((2H₀ + 2|a₀|)/|a₀|)^{1/2δ}⌉ + 1)²`; with `|a₀| ≈ 1/γ²` this is about
`(2γ)²·(0.1γ²)^{1/δ}`, e.g. `10^{16}` for `γ = 14.13`, `δ = 0.05`, against the level `≈ 1000` seen numerically.

*Feasibility.* Provable now, from the library's twin sum: the test vector is the `2 × 2` minor at `(p₀², q₀²)`,
whose value is `p₀²q₀²·W(log(p₀/q₀))` with `W(λ) = Σ_ρ a_ρ(2 + e^{λP_ρ} + e^{−λP_ρ})`, `P_ρ = 2(ρ − ½)`
(`BallHadamard.twin_eq_kerH`, `BallWeil.form_two`). The on-line zeros contribute at most `2H₀` whatever `λ` is, by
Hadamard's identity and `Re a_ρ > 0`, which is why the minor is the one test vector whose positive part is bounded
without knowing the zeros; the four zeros of `S₀` contribute `4|a₀|e^{2δλ}cos(2γλ + arg a₀) + O(|a₀|)`, and (i)–(ii)
bound the rest by `(e^{2δλ} + 1)M`. The level `p₀² ≈ e^{2Λ}` is exponential in `1/δ`, where the numerical first witness
is `≈ 80/δ`: the eigenvector resolves the zeros near height `γ` and pays only for them, the minor pays `2H₀` for all of
them. **What is not provable this way:** a level `N₀(β, γ)` for an arbitrary off-line zero. The argument that gives
`rh_of_posDefH` is Landau's theorem on the Laplace transform of the twin sum, which is not effective, and the obstruction
is real: zeros of the same real part at nearby heights carry comparable weights `≈ 1/γ²` and unknown phases, and no
spacing or local counting result excludes their cancelling `ρ₀` on any finite window. An unconditional effective
version is a Turán power-sum argument with local zero counts, a separate project; the hypothesis `Dominant` is what the
Landau mechanism can isolate, and it is a hypothesis on the zeros, not on RH.

**Statement 1B (collapse, with any rate).** If `λ_N ≥ −ε(N)` for infinitely many `N` with `ε(N) → 0`, then RH
(`rh_of_frequently_balanced`, ported from the `positivity-search` branch's `GravastarTower`), in particular for
`ε(N) = 1/N`. Together: a crossing with a dominant zero is seen at an explicit finite level, and a crossing of any kind
cannot hide in the limit. *Feasibility:* proved on the branch; port and re-prove, a hundred lines.

### 2. The approach ("time dilation")

**Statement 2A (the rate, with an explicit vector; conjectural).** For `x_n = (1 − n/N)²/ψ(n)`,
`Q_N(x) ≤ C·(log N/N)·Σ x_n²` with `C = 0.13`, so `λ_N ≤ 0.13·log N/N`. Numerically the quotient is `2.3`–`2.6` times
`λ_N` for `200 ≤ N ≤ 3200`, and `λ_N` itself is `0.048·log N/N`. *Why this vector:* `Σ_n n^{−w}/ψ(n) = ζ(w + 1)·E(w)`
with `E(w) = Π_p(1 − p^{−w}/(p(p + 1)))` absolutely convergent on `Re w > −1`, so `V_x(s)` is the Riesz mean of
order `2` of the series of `ζ(1 − s)E(−s)`; at a zero the main term vanishes, the cutoff leaves
`2E(0)N^ρ/(ρ(ρ + 1)(ρ + 2))` and a remainder, and `Σ_ρ |·|²/|ρ|²` of the first is `≍ N·Σ_ρ |ρ|^{−8}`. *Feasibility:*
the remainder, summed over the zeros with the weights `|ρ|^{−2}`, needs mean-value estimates for `ζ(ε + it)` at
shifts of the zeros, which the library does not have; the vector with a sharp cutoff (`1/ψ(n)`, or `1/n`) has
`Q_N ≈ 7.6·10^{−5}·N`, so the smoothing is essential and the proof is the analytic part. Left as a conjecture with the
constant checked to `N = 3200`.

**Statement 2B (the approach, unconditional, no rate).** `lim sup λ_N ≤ 0`: for every `ε > 0` there is `N₀` with
`λ_N ≤ ε` for all `N ≥ N₀`, by an explicit test vector. Under RH the two-point vector `x = δ_n − √n·δ_1` has
`Q_N(x) = 2n(H₀ − K_H(n))`, `Σ x² = n + 1`, and `H₀ − K_H(n) = Σ_ρ a_ρ(1 − cos(γ log n))`
(`BallHadamard.kerH_second_diff`); choosing `n` with `γ_j log n` within `η` of `2πℤ` for the finitely many zeros that
carry all but `ε/2` of the weight (simultaneous Dirichlet approximation on the ordinates) makes this `< ε`. If RH
fails, some level has a negative vector and negativity persists upward. *Feasibility:* provable, about four hundred
lines (pigeonhole for the approximation, the cusp identity, `form_two`, and 1B); the vector is explicit given the
first `J(ε)` ordinates and the rate is iterated-logarithmic, the price of not using the arithmetic that 2A uses.

### 3. The rate (under RH; the open one)

**Statement 3A (the models).** With Lebesgue measure for the zeros (`BallFlat`: Gram matrix `H₀·min(m, n)`),
`λ_N ≥ H₀/4` for every `N`, by the telescoping identity `Σ x_m x_n min(m, n) = Σ_k (Σ_{n ≥ k} x_n)²`: provable, a
page. With the zeros replaced by their **density** `(1/2π)log(|t|/2π)` on `|t| ≥ 2π`, `λ_N = 0.0505 − O(10^{−4})`
for `N ≤ 800`, the minimiser being `δ_1` to within `0.3%`: a uniform margin, as claimed, but not a Toeplitz statement
(the points are `log n`, not a grid, and the symbol's infimum is `0`); a proof needs a multi-scale form of the
Montgomery–Vaughan mean value theorem against the weight `log|t|/t²`, which the library's `DirMean.mean_value` (an
upper bound) does not give. Not attempted. With the zeros at their **mean positions** (the `k`-th at the `t` with
`(t/2π)log(t/2πe) + 7/8 = k`, the first `20000` of them), `λ_N` decays like `N^{−0.45}` for `N ≤ 400`: the
discreteness alone sags, and the arithmetic doubles the exponent to `N^{−1}log N`. So "the sag is arithmetic, not
geometric" is half true: the continuous density has no sag, the discrete picket fence has half of it.

**Statement 3B (the rate, under RH and a sampling hypothesis).** Say the zeros **sample at `(c, C, θ)`** when for
every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ C·N^{1+θ}`,
`Σ_{|γ_ρ| ≤ T} |V_x(ρ)|² ≥ c·T·Σ_{n ≤ N} x_n² n`. Then under RH, `λ_N ≥ (c/2C)·N^{−1−θ}` for every `N ≥ 1`: the sag
is at most polynomial, `A = 1 + θ`. *Feasibility:* provable now, from `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` under RH
(`BallHadamard.realizationH`) and `¼ + γ² ≤ 2T²` on `|γ| ≤ T`; two hundred lines. The hypothesis is the
Marcinkiewicz–Zygmund inequality for Dirichlet polynomials of length `N` at the zeros up to height `C·N^{1+θ}`; by
Beurling–Landau it needs `θ > 0` for a general sampling set of this density, and for the zeros it would follow from
Landau's formula `Σ_{0<γ≤T} x^{iγ} = −(T/2π)Λ(x)/√x + O(…)` with a pair-correlation input, neither of which is in the
library. The numerics (`scripts/ball_rate.py`) measure `c` at `T = 2000` on the minimising vectors of `G_N`,
`N ≤ 2000`, from the first `2000` zeros, and find `c ≈ …` (filled in by the script).

**Statement 3C (what is missing, as a conjecture).** The inequality on `|V_x(ρ)|` at the zeros that the rate needs,
with its numerics, is stated in the last section of this note.
