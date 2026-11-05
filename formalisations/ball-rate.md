# The evaporation rate of the orbit form: witness level, approach, rate

**Lean:** `BallRate` (`lib/core/BallRate.lean`), printed by `lib/check/CheckAll.lean`, with `BallSampling`,
`BallDensity`, `BallCutoff` and `BallSharp` in four later sections, `BallUpper` with `BallUpperEta` in the next-to-last,
and `BallGap` in the last. The theorems are mapped onto the gravastar
language in the section after the statements; the first section, written before the Lean, fixes the three statements
and says what each costs. The rate, open when that section was written, is now proved under RH alone:
`λ_N ≥ 1/(22e⁸N)` for every `N ≥ 1` (`BallSharp.rate_sharp`, last section). It comes from the sampling conjecture of
the section "What is missing", which `BallCutoff.sampling_rh` proves under RH with `c = 1/100` and `C = e²⁴`, and
`BallSharp.sampling_e8` with `c = 1/11` and `C = e⁸`. `BallSharp.sampling_log` gives sampling its natural form: a
frame bound `(T/11)(log(T/N) − 7)`, which grows like the number of zeros up to `T`. The rate from above is proved too
(`BallUpper`, `BallUpperEta`, last section): `λ_N ≤ 67(1 + log N)/N` under RH, by the alternating vector
`x_n = (−1)^{n+1}/n`, and `λ_N ≤ C(1 + log N)/N` with some constant `C` unconditionally (`BallUpperEta.rate_upper`).
Under RH `λ_N` is therefore between `1/(22e⁸N)` and `67(1 + log N)/N`; numerically it is `0.048·log N/N`. Keeping
Landau's slack `G(c)`, `BallSharp.rate_slack` reduces the missing `log N` of the lower bound to the vectors with
`Σx_n² n + G(c) = o(log N·Σx_n²)` (section "Why the sampling route stops short of `log N/N`"). Every vector has
`Σx_n² n + G(c) ≥ (√log N/10)Σx_n²` (`BallGap.edge_law`, last section), so under RH `λ_N ≥ √log N/(220e⁸N)` for every
`N ≥ 3` (`BallGap.rate_gap`): this route recovers `√log N` of the missing `log N`, which by the numerics of that
section is all it can give.

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
conjecture with the constant checked to `N = 2000`. **Correction.** The conjecture is false. The cutoff term contributes
`≍ N·Σ_ρ|ρ|^{−8}` to `Q_N(x)` while `Σ x_n²` stays bounded, so `q_N = Q_N(x)/Σ x_n²` eventually grows like `N`. Past
`N = 2000` the constant rises: `q_N·N/log N = 0.1218, 0.1441, 0.2870` at `N = 3000, 10⁴, 3·10⁴`
(`scripts/alt_vector.py`), past `0.13` before `N = 10⁴`. The rate statement holds for another explicit vector:
`x_n = (−1)^{n+1}/n`, whose
polynomial at a zero is a partial sum of `η(ρ̄) = (1 − 2^{1−ρ̄})ζ(ρ̄) = 0`, has `q_N·N/log N = 0.1522`–`0.1527` from
`N = 100` to `3·10⁴`. It gives `λ_N ≤ 67(1 + log N)/N` under RH (`BallUpperEta.rate_upper_rh`, last section).

**Statement 2B (the approach, unconditional, no rate).** `lim sup λ_N ≤ 0`: for every `ε > 0` there is `N₀` with
`λ_N ≤ ε` for all `N ≥ N₀`, by an explicit test vector (`approach`). Under RH the two-point vector `x = δ_n − √n·δ_1`
has `Q_N(x) = 2n(H₀ − K_H(n))`, `Σ x² = n + 1`, and `H₀ − K_H(n) = Σ_ρ (1 − cos(γ log n))/(¼ + γ²)`
(`BallHadamard.kerH_second_diff`); choosing `n` with `γ_j log n` within `η` of `2πℤ` for the finitely many zeros that
carry all but `ε/8` of the weight (simultaneous Dirichlet approximation on the ordinates, `exists_simultaneous`) makes
this `≤ ε/2`. If RH fails, some level has a negative vector and negativity persists upward. *Feasibility:* proved,
about three hundred lines; the vector is explicit given the first `J(ε)` ordinates and the level is not, the price of
not using the arithmetic that 2A uses. `BallUpperEta.rate_upper` (last section) now gives a rate, unconditionally:
`λ_N ≤ C(1 + log N)/N` for every `N ≥ 1`.

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
neither of which is in the library. (`BallCutoff` and `BallSharp`, the last two sections, prove the case `θ = 0` with
neither, from the explicit formula.) The numerics are in the section "The numerics".

**Statement 3C (what is missing, as a conjecture).** The inequality on `|V_x(ρ)|` at the zeros that the rate needs,
with its numerics, is stated in the section "What is missing". A Gaussian-smoothed form of it, at height
`T₀ ≍ N log²N`, is now proved from the explicit formula under RH and gives `λ_N ≥ 10⁻¹²/(N log³N)`
(`BallDensity`). The sharp-cutoff form itself, with `c = 1/100` and `C = e²⁴`, is proved under RH too and gives
`λ_N ≥ 1/(200e²⁴N)` (`BallCutoff`); with `c = 1/11` and `C = e⁸` it gives `λ_N ≥ 1/(22e⁸N)` (`BallSharp`, last
section).

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
`SamplingAtZeros` is a named hypothesis, with no proof in the module (`BallCutoff.sampling_rh` and
`BallSharp.sampling_e8`, the last two sections, prove it under RH at `θ = 0`). All ten printed theorems depend on `propext`,
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
| `C = q_N·N/log N` for `x_n = (1 − n/N)²/ψ(n)`, and `q_N/λ_N` | `0.112`–`0.120`; `2.21`–`2.51` (beyond `N = 2000` `C` grows, see statement 2A) |
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
`(c, C) = (1/100, e²⁴)` (`BallCutoff.sampling_rh`) and `(1/11, e⁸)` (`BallSharp.sampling_e8`, last section).

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

**Lean:** `BallDensity` (`lib/core/BallDensity.lean`), printed by `lib/check/CheckAll.lean`. The seven results depend on
`propext`, `Classical.choice` and `Quot.sound` only. The previous section needs a zero in every short cell. This one
needs only the density of the zeros, which Weil's explicit formula supplies (`WeilForm.weilExplicit_zeta`, proved with
no RH input). It proves the rate with RH as the only hypothesis.

| Theorem | Statement | Conditional on |
|---|---|---|
| `BallDensity.mertens_le` | `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 4` | nothing |
| `BallDensity.landau_le` | for every real `b`, `2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤ (log N + log 4 + 4)Σ_{j ≤ N} b_j²` | nothing |
| `BallDensity.mertens_le_sharp` | `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 1` | nothing |
| `BallDensity.landau_le_sharp` | the same as `landau_le` with `log 4 + 1` in place of `log 4 + 4` | nothing |
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
  and Chebyshev's `ψ(M) ≤ (log 4 + 4)M` from Mathlib. `mertens_le_sharp` replaces `M log M` by Stirling's
  `M log M − M + log M + 1` (Mathlib's `Real.sum_log_le`) and Chebyshev's bound by `ψ(M) ≤ M log 4 + 2√M log M`
  (`Chebyshev.psi_le`); with `2√M log M ≤ 4M/e` this gives `log 4 + 1` (the truth is `−γ`), which `BallSharp` uses
  (`landau_le_sharp`). The near misses are summable against `Λ(n)/√n ≤ 2` and
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
`T ≥ e²⁴N`. This is the Marcinkiewicz–Zygmund inequality that the section "What is missing" observed (`c ≈ 0.1` at
`C = 8`) and conjectured. The zeros near height `T` have density `(1/2π)log(T/2π)`, so at `T = CN` they exceed the
Nyquist density `(1/2π)log N` of a polynomial of length `N` by the constant `(1/2π)log(C/2π)`, an additive excess
whose ratio to the Nyquist density tends to `1`. The constants are far from optimal:
`e²⁴ ≈ 2.6·10¹⁰`, against the observed `8`; `BallSharp` (next section) brings it down to `e⁸ ≈ 3·10³`. The shape is right, though. `λ_N ≥ 1/(200e²⁴N)` has the Nyquist exponent
and no logarithm, against the observed `0.048·log N/N`; one factor `log N` is missing. Two properties of the test
function account for the gain over `BallDensity`:

- Its transform has compact support, so the diagonal and the prime side are exact, not Gaussian-approximate. That
  removes the window width `σ ≫ N√(log N)`.
- It vanishes to second order at `0` and changes sign at `T`. So the zeros up to `T` are counted with weight at most
  `¼`, and the pole and the low heights of the archimedean term cost `O(NΣc_n²)` and `O(TΣc_n²)`, with no `log T`.
  The weight `1/(¼ + γ²)` then costs `1/T² ≍ 1/N²` against the gain `T ≍ N`.

**Prior work.** A literature check found no statement of `sampling_rh`, or of anything stronger, at `T ≍ N`. The report
is [reports/Sampling Dirichlet polynomials at zeta zeros.md](../reports/Sampling%20Dirichlet%20polynomials%20at%20zeta%20zeros.md),
and the notes behind it are in `research_notes/`. The searches covered arXiv and the web but not MathSciNet or zbMATH.
The nearest results:

- **Discrete mean values.** H. M. Bui, A. Florea and M. B. Milinovich (Bull. London Math. Soc. 56 (2024); Theorem 3.1
  of arXiv:2310.03949) evaluate `Σ_{0<γ≤T}|Σ_{n≤x} a_n n^{−ρ}|²` under RH for every length. They use S. M. Gonek's
  uniform version of Landau's formula (Contemp. Math. 143 (1993)), with error `O(x log²(xT)Σ|a_n|²/n)`. Together with
  the bound on Landau's form, this gives a lower bound `≫ T log(T/N)Σb_n²`. But that holds only for `N ≤ cT/log²T`,
  with inexplicit constants; at `T ≍ N` the error exceeds the diagonal by a factor `≍ log T`.
- **Windowed comparisons.** The method of H. L. Montgomery and A. M. Odlyzko (Colloq. Math. Soc. János Bolyai 34
  (1984)) compares the zeros with `∫|A|²` uniformly in the coefficients. J. B. Conrey, A. Ghosh and S. M. Gonek (Bull.
  London Math. Soc. 16 (1984)) put it in that form. Each zero is smeared over a window of a few mean spacings, and the
  lengths go up to `T/log²T`. Its bound for Landau's form is the device of `BallDensity.landau_le`.
- **The method.** The explicit formula with band-limited minorants and majorants is the method of D. A. Goldston and
  S. M. Gonek for `S(t)` (Bull. London Math. Soc. 39 (2007)). It comes after Montgomery–Odlyzko and J. D. Vaaler's
  extremal functions (Bull. Amer. Math. Soc. 12 (1985)), and the formula is that of Iwaniec–Kowalski, Theorem 5.12.
  E. Carneiro, M. B. Milinovich and K. Soundararajan (Comment. Math. Helv. 94 (2019)) use the one-term case
  `f(z)a^{iz}` of `|D|²Φ`. The separation argument of `BallDensity.sep_log` is in C. P. Hughes and Z. Rudnick (C. R.
  Math. Acad. Sci. Paris 335 (2002)). The Fejér-kernel bound `integral_Kc_majR_le` is in the tradition of Selberg's
  band-limited large sieve (H. L. Montgomery, Bull. Amer. Math. Soc. 84 (1978)). The minorant `Φ` itself was not
  found.

What is new is the combination: Fourier support below the spacing of the `log(m/n)`, which makes the diagonal and
Landau's form exact. With it comes a pointwise lower bound with explicit constants at `T ≍ N`.

The range is necessary up to its constant. Titchmarsh's Theorem 4.11 gives
`ζ(s) = Σ_{n≤x} n^{−s} − x^{1−s}/(1 − s) + O(x^{−σ})` for `|t| ≤ 2πx/C′`, `C′ > 1`. So under RH the vector `x_n = 1/n`
breaks the inequality for `T ≤ (2π − ε)N` once `N` is large: the left side is `O(N)` against a right side `≍ N log N`.
The best threshold therefore lies between `2πN` and `e⁷N`: `BallSharp.sampling_log` (next section) gives sampling
with some `c > 0` at every `C > e⁷`.

For the corollary, no earlier polynomial lower bound, `c/N` or `N^{−A}`, was found for the smallest eigenvalue of an
RH-related positive form. The Nyman–Beurling lower bounds `lim inf d_N² log N ≥ Σ_ρ m_ρ²/|ρ|²` are ineffective in `N`
and come from interpolation at finitely many zeros. They are due to L. Báez-Duarte, M. Balazard, B. Landreau and
E. Saias (Adv. Math. 149 (2000)) and to J.-F. Burnol (Adv. Math. 170 (2002)). A. Connes and C. Consani (Enseign. Math.
69 (2023)) find the smallest eigenvalues of Weil's form on growing windows super-exponentially small.

## Sampling at the zeros in its natural form (`BallSharp`)

**Lean:** `BallSharp` (`lib/core/BallSharp.lean`), printed by `lib/check/CheckAll.lean`. The seven results depend on
`propext`, `Classical.choice` and `Quot.sound` only. `BallCutoff` gives the zeros up to height `T` the frame bound
`T/100`, a constant times the length of the window. This section gives it the shape of the number of zeros,
`T log(T/N)`, from `T ≥ 2000N` on. With it the rate improves from `1/(200e²⁴N)` to `1/(22e⁸N)`.

| Theorem | Statement | Conditional on |
|---|---|---|
| `BallSharp.integral_Kc_conv` | for `2aN ≤ 1` and integrable `E`, `∫\|D(t)\|²(E ⋆ F_a)(t) dt = Σ_{j ≤ N} c_j²·∫E`, with `D(t) = Σ_{j ≤ N} c_j j^{−it}` and the Fejér kernel `F_a(u) = sin²(au)/(πau²)` | nothing |
| `BallSharp.sampling_log` | for every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ 2000N`, `Σ_{\|γ_ρ\| ≤ T}\|Σ_{n ≤ N} x_n n^ρ\|² ≥ (T/11)(log(T/N) − 7)Σ_{n ≤ N} x_n² n` | RH |
| `BallSharp.sampling_log_clean` | the same with `(T/22)log(T/N)` in place of `(T/11)(log(T/N) − 7)`, for every `T ≥ e¹⁴N` | RH |
| `BallSharp.sampling_e8` | `BallRate.SamplingAtZeros (1/11) e⁸ 0`: the same with `T/11`, for every `T ≥ e⁸N` | RH |
| `BallSharp.rate_sharp` | `Q_N(x) ≥ Σ x_n²/(22e⁸N)` for every `N ≥ 1`, so `λ_N ≥ 1/(22e⁸N)` | RH |
| `BallSharp.sharp_bound_slack` | `sampling_log` with Landau's slack kept: `Σ_{\|γ_ρ\| ≤ T}\|V_x(ρ)\|² ≥ (T/11)((log(T/N) − 7)Σ x_n² n + G(c))` for `T ≥ 2000N`, with `c_n = x_n√n` and `G(c) = (log N + log 4 + 1)Σc_n² − L(c) ≥ 0` (`landauSlack`) | RH |
| `BallSharp.rate_slack` | `Q_N(x) ≥ (Σ x_n² n + G(c))/(22e⁸N)` for every `N ≥ 1`, which contains `rate_sharp` | RH |

**How it is proved.** The test function is `BallCutoff`'s `h(t) = |D(t)|²Φ(t)`, with `c_n = x_n√n`, now at `b = 3`.
Five changes turn the constant `T/100` into `(T/11)(log(T/N) − 7)`.

- **A taller minorant.** At `b = 3`, `Φ(r) = (r/T)²(1 − (r/T)²)sinc⁶(3r/T)` has mass `Φ̂(0) = 5πT/648`, about seven
  times that at `b = 6`, and it stays below `1/25` on `[−T, T]` (`phiR3_le`). That comes from `sinc θ ≤ 1/(1 + θ²/6)` on
  `[0, 3]` and `v(1 − v) ≤ (1 + 3v/2)⁶/25` on `[0, 1]`. So the zero side is at most `(1/25)Σ_{|γ| ≤ T}|V_x(ρ)|²`
  (`zero_side_sharp`). The transform is supported in `|v| ≤ 18/T`, so exactness needs only `T > 36N`.
- **A sharper floor for the archimedean weight.** Stirling at `N = 2`, with two steps of the recurrence
  `ψ(s + 1) = ψ(s) + 1/s`, gives `|Re ψ(¼ + it/2) − log(|t|/2)| ≤ 21/(2t²) + 1/3000` for `|t| ≥ 8` (`psiRe_near`).
  So `L(t) = Re ψ(¼ + it/2) − log π` is at least `L₁ = log(T/8π) − ε₁` on `|t| ≥ T/4`, with
  `ε₁ = 21/2048 + 1/3000`.
- **A sharper Mertens bound.** `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 1` (`BallDensity.mertens_le_sharp`), so Landau's
  form is at most `(log N + log 4 + 1)Σc_n²` (`BallDensity.landau_le_sharp`), and the main term
  `(Φ̂(0)/2π)(L₁ − log N − log 4 − 1)Σc_n²` is at least `(5T/1296)(log(T/N) − 5.633)Σc_n²`.
- **The low heights.** For `T ≥ 2000`, `(t/T)²(L₁ − L(t))⁺ ≤ (23/2000)M_{T/4}(t)` for every `t` (`low_le_s`). On
  `32 ≤ |t| < T/4` this is `y²log(1/4y) ≤ 1/(32e)` with `y = |t|/T`, and below `32` it is `O(log T/T²)`. The
  Fejér-kernel bound `BallCutoff.integral_Kc_majR_le` then gives a cost of `0.0023TΣc_n²`.
- **The tail, by Fejér smoothing.** Beyond `T`, `|Φ(t)|(L(t) − L₁)⁺ ≤ T²(log(|t|/T) + c₁)/(729t²)`, with
  `c₁ = log 4 + 2ε₁` (`tail_w_le`). In place of `BallCutoff`'s dyadic shells, the weight is dominated by a
  convolution. On the windows `|u| ≤ T/10` it is at most `E(t − u)`, where `E(s) = K(log(|s|/R) + c₁)/s²` on
  `|s| > R`, with `K = (1.1T)²/729` and `R = 0.9T` (`envT_ge`). The Fejér kernel `F_a` at `a = 1/(2N)` has mass at
  least `1 − 2/(πaT/10) ≥ 156/157` on the window (`fej_mass_ge`). So the weight is at most `(157/156)(E ⋆ F_a)`
  (`conv_ge`, `tail_conv_le`). The transform of `F_a` is `(1 − N|v|)⁺`, and distinct `log j` are at least `1/N`
  apart (`log_sep`). So `|D|² ⋆ F_a` is the constant `Σc_n²` (`Kc_conv_fej`), and by Fubini the weight costs exactly
  `Σc_n²·∫E` (`integral_Kc_conv`). Here `∫E = 2K(1 + c₁)/R ≤ 0.0089T` (`integral_envT`), with no dependence on `N`.

The pole costs at most `10⁻⁶TΣc_n²` (`pole_ge_sharp`). Summing these,
`(1/25)Σ_{|γ| ≤ T}|V_x(ρ)|² ≥ (5T/1296)(log(T/N) − 5.633)Σc_n² − 0.0039TΣc_n²`. So the sum is at least
`0.0964T(log(T/N) − 6.65)Σc_n²`, which is at least `(T/11)(log(T/N) − 7)Σc_n²` because `log(T/N) ≥ 7`. The prime side
is `(5T/1296)L(c)` exactly, so Landau's slack `G(c) = (log N + log 4 + 1)Σc_n² − L(c)` enters with the coefficient
`125T/1296 ≥ T/11` and can be kept (`sharp_bound_slack`); `G(c) ≥ 0` gives `sharp_bound`. For the rate,
`rate_of_sampling` turns `SamplingAtZeros c C 0` into `λ_N ≥ c/(2CN)`. With `c = (log C − 7)/11` the best `C` is
`e⁸`, where `c = 1/11`; this gives `rate_sharp`. At the same `T = e⁸N`, `sharp_bound_slack` gives `rate_slack`,
`Q_N(x) ≥ (Σx_n² n + G(c))/(22e⁸N)`.

**What this says.** At `x = δ₁` the sum counts the zeros up to height `T`, about `(T/π)log(T/2πe)`. So the shape
`T log T` is right, and the constant `1/11` is within a factor `11/π ≈ 3.5` of the count's `1/π`. For general `x`,
the discrete mean value of Bui, Florea and Milinovich (previous section) has the same shape `T log(T/N)`, with
inexplicit constants and only for `N ≤ cT/log²T`. `sampling_log` holds for `N` up to `T/2000`, at `T ≍ N`, where
that error term exceeds the main term. The statement says nothing for `T ≤ e⁷N`. Below `T = 2πN` no lower bound
of this kind can hold: the vector `x_n = 1/n` breaks it (previous section). The rate `λ_N ≥ 1/(22e⁸N)`, about
`1.5·10⁻⁵/N`, is `8·10⁷` times `BallCutoff`'s `1/(200e²⁴N)`. The observed rate is `0.048·log N/N`, so the factor
`log N` is still missing; the next section shows that this route cannot recover more than `√log N` of it.

**Prior work.** The literature check of the previous section covers this one. Its nearest result, the discrete mean
value of Bui–Florea–Milinovich, already has the shape `T log(T/N)`, but stops at `N ≤ cT/log²T`. The identity
`|D|² ⋆ F_a = Σc_n²` is the large-sieve principle behind the previous section's Fejér-kernel bound, used here as an
equality: the kernel's transform is supported below the separation of the frequencies, so only the diagonal survives.

## Why the sampling route stops short of `log N/N`: the Landau gap is `√log N` (`scripts/landau_gap.py`, uncertified)

**The reduction.** In `BallSharp`'s assembly the prime side is exactly `(Φ̂(0)/2π)L(c)`, with Landau's form
`L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N} c_j c_{jn}` (`BallCutoff.prime_eq_cut`), and `landau_le_sharp` bounds it by
`(log N + c₀)Σc_n²`, `c₀ = log 4 + 1`. Keeping the slack `G(c) = (log N + c₀)Σc_n² − L(c) ≥ 0` instead of discarding
it, the same proof gives `Σ_{|γ| ≤ T}|V_x(ρ)|² ≥ (T/11)((log(T/N) − 7)Σx_n² n + G(c))` (`BallSharp.sharp_bound_slack`),
hence `Q_N(x) ≥ (Σx_n² n + G(c))/(22e⁸N)` (`BallSharp.rate_slack`), and `Σ_m c_m²/m = Σ x_m²` for `c_m = x_m√m`. So a
bound `G(c) ≥ η_N Σ_m c_m²/m` would give `λ_N ≫ η_N/N`, and `η_N ≍ log N` the observed order.

**The ground-state form.** With `c_m = f_m/√m`, Schur's test becomes an identity:
`G(c) = Σ_m (f_m²/m)κ(N/m) + Σ_{j,n}(Λ(n)/(nj))(f_j − f_{jn})²`, with `κ(y) = c₀ + log y − Σ_{n ≤ y}Λ(n)/n ≥ 0`
(`mertens_le_sharp`). The bound wanted is a Hardy inequality on the divisibility graph: the electrical network with
conductance `Λ(n)/(nj)` on each edge `j — jn` and grounding `κ(N/m)/m` at `m`.

**The numbers.** `η_N`, the largest `η` with `(log N + c₀)I − M ⪰ η·diag(1/m)` (`M` the matrix of `L`), and the
capacity of the vertex `1`, `Cap(1) = min{G(c) : c₁ = 1}`, by conjugate gradients:

| `N` | `η_N/log N` | `Cap(1)/log N` | `Cap(1)/√log N` | `Cap(1)/√log N` at `c₀ = 0` |
|---|---|---|---|---|
| `10³` | `0.922` | `0.950` | `2.497` | `0.896` |
| `10⁴` | `0.797` | `0.817` | `2.481` | `0.952` |
| `10⁵` | `0.715` | `0.732` | `2.484` | `1.001` |
| `10⁶` | `0.658` | `0.672` | `2.497` | `1.045` |
| `3·10⁶` | `0.635` | `0.649` | `2.505` | `1.065` |

The minimiser sits at `m = 1`, with the star of the prime powers (`η_N ≈ Cap(1)`). `Cap(1)/log N` keeps falling while
`Cap(1)/√log N` is flat, near `√(2(c₀ + γ)) = 2.435` (and `1.074` at `c₀ = 0`). So `η_N ≍ √log N`: the gap is the
square root of the one the rate needs, and the same holds with the true Mertens constant.

**The mechanism.** The walk of the network moves from `j` to `jn` with weight `Λ(n)/n` and from `m` to `m/n` with weight
`Λ(n)`. In the scale `log m/log N` the next position is uniform on `[0, 1]`, so the size of `m` mixes at once, but
`Ω(m)`, the number of prime factors, makes a recurrent one-dimensional walk: it falls with probability `log m/log N`,
about `½`, and a prime power `q` returns straight to `1` with probability `log q/log N`. Killing at rate about
`κ/log N` gives a lifetime of `log N/κ` steps, in which a recurrent walk visits `1` about `√(log N/κ)` times. Hence
`Cap(1) ≍ √(κ log N)`: the spectral measure of `δ₁` under `M` has an arcsine edge at `log N − γ`, which gives
`Cap(1) ≈ √(2(c₀ + γ)log N)`.

**What it means.** The prime side with Fourier support below `1/N` cannot give more than `λ_N ≫ √(log N)/N`, even with
Landau's form kept exact. The last section proves that it gives that much (`BallGap.rate_gap`). The vectors with the
small gap are not the ones that make `λ_N` small. For `δ₁` plus the star,
`x_q ∝ Λ(q)/q`, the polynomial is `V_x(ρ) = x₁ + Σ_q x_q q^ρ`, and at a zero `Σ_{q ≤ N}Λ(q)q^{ρ−1} = N^ρ/ρ − log N + …`
(the explicit formula at `1 − ρ = ρ̄`), so `|V_x(ρ)| ≈ √N/(|γ| log N)` at the low zeros and `Q_N(x) ≫ N/log²N`. The
near-flat vector `x_n = (1 − n/N)²/ψ(n)` comes within a factor `2.5` of `λ_N` for `N ≤ 2000` (section B of
`scripts/ball_rate.py`), and for it `Σ x_n² n ≍ log N·Σ x_n²`, so the sampling bound already gives the order `log N/N`
there. The missing factor lives in the low zeros, which a test function at height `T ≍ N` weights only by `1/T²`. The
next section bounds `λ_N` from above by an explicit vector that vanishes at the low zeros.

**Which vectors the slack leaves** (`scripts/landau_gap.py --spread`, prime-side Gram matrices, uncertified). With the
spread `A = Σx_n² n/Σx_n²` and `B = G(c)/Σx_n²`, `rate_slack` reads `Q_N(x) ≥ (A + B)Σx_n²/(22e⁸N)`. A vector with
`A + B ≥ ε log N` therefore has `Q_N(x) ≥ (ε/22e⁸)(log N/N)Σx_n²`, and `λ_N ≫ log N/N` is a statement about the vectors
with `A + B = o(log N)` alone. The edge vector is the minimiser of `A + B`:

| `N` | `λ_N·N/log N` | minimiser of `Q_N`: `A/log N` | `B/log N` | edge vector: `(A + B)/√log N` | `x₁²` | `Q_N(x)·N/log N` | eigenvalues of `A + B` over `√log N` |
|---|---|---|---|---|---|---|---|
| `250` | `0.0492` | `0.492` | `1.509` | `3.00` | `0.968` | `0.57` | `3.00, 6.43, 9.89, 13.48` |
| `500` | `0.0484` | `0.476` | `1.467` | `2.96` | `0.970` | `0.84` | `2.96, 6.37, 9.85, 13.41` |
| `1000` | `0.0480` | `0.467` | `1.443` | `2.94` | `0.971` | `1.80` | `2.94, 6.32, 9.78, 13.34` |
| `2000` | `0.0476` | `0.458` | `1.418` | `2.93` | `0.973` | `4.69` | `2.93, 6.29, 9.73, 13.27` |

- The minimiser of `Q_N` has `A ≈ 0.46 log N` and `B ≈ 1.42 log N`, both of order `log N`. For it the slack-kept bound
  already gives the order `log N/N`.
- The edge vector is `97%` `δ₁`, with `A + B ≈ 2.9√log N`: the capacity of the vertex `1`, plus `A ≈ 1`. Its `Q_N` is
  of order one, `0.01`–`0.02`, so `17` to `100` times `λ_N` over this range. At the low zeros `V_x(ρ) ≈ x₁`, and they
  charge it a fraction of `K_H(1)`.
- The bottom of the spectrum of `A + B` is roughly evenly spaced in units of `√log N`. At these `N` only its first
  eigenvalue lies below `2·log N`; the number below `ε log N` grows like `ε√log N/3.4`.

So `λ_N ≍ log N/N` needs one more ingredient: the vectors in the bottom of this spectrum cannot be small at all the zeros
below height `≍ N`. The alternating vector of the next section shows how a vector avoids the low zeros, by being a
multiple of `ζ` (through `η = (1 − 2^{1−s})ζ`), and it pays `A ≍ log N` for it. At `N ≤ 2000`, `√log N` and `log N` differ
by less than a factor `3`, so these numbers show trends, not a separation of the two scales.

## The rate from above: `λ_N ≤ 67(1 + log N)/N` under RH, and `λ_N ≪ log N/N` unconditionally (`BallUpper`, `BallUpperEta`)

**Lean:** `BallUpper` (`lib/core/BallUpper.lean`) and `BallUpperEta` (`lib/pnt/BallUpperEta.lean`, which imports PNT+'s
`ZetaBounds`), printed by `lib/check/CheckAll.lean`. The seven printed results depend on `propext`, `Classical.choice`
and `Quot.sound` only.

| Result | Statement | Conditional on |
|---|---|---|
| `BallUpper.tail_le` | `\|Σ_{N < n ≤ N + M}(−1)^{n+1}n^{−s}\| ≤ 20/√N` for `Re s = ½`, `\|Im s\| ≤ 2N` and every `M` | nothing |
| `BallUpper.upper_mean` | `Σ_{\|γ_ρ\| ≤ r}\|V_x(ρ)\|² ≤ (πr/4)((log(r/2π) + 1/5 + 22/π)Σc_n² − L(c)) + 46(Σ_j\|c_j\|√j)(Σ_j\|c_j\|/√j)` for `r ≥ 8N`, `c_n = x_n√n` | RH |
| `BallUpper.mean_xa_le` | `Σ_{\|γ_ρ\| ≤ r}\|V_x(ρ)\|² ≤ ((πr/4)(log(r/N) + 12) + 46N)H_N` for `r ≥ 8N` at `x_n = (−1)^{n+1}/n`, `H_N = Σ_{j ≤ N}1/j` | RH |
| `BallUpper.form_xa_le` | if `\|V_x(ρ)\|² ≤ 400/N` at the zeros with `\|γ\| ≤ 2N`, then `Q_N(x) ≤ (400K_H(1) + 45)H_N/N`, at the same vector | RH and its hypothesis |
| `BallUpperEta.dpoly_xa_le` | `\|V_x(ρ)\| ≤ 20/√N` at the zeros with `\|γ\| ≤ 2N`, at the same vector | RH |
| `BallUpperEta.rate_upper_rh` | `Q_N(x) ≤ 67(1 + log N)/N·Σ_{n ≤ N}x_n²` for every `N ≥ 1`, at the same vector | RH |
| `BallUpperEta.rate_upper` | `∃ C, ∀ N ≥ 1, ∃ x, Σ_{n ≤ N}x_n² > 0 ∧ Q_N(x) ≤ C(1 + log N)/N·Σ_{n ≤ N}x_n²` | nothing |

Here `L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}` is Landau's form. With `BallSharp.rate_sharp`, under RH,
`1/(22e⁸N) ≤ λ_N ≤ 67(1 + log N)/N` for every `N ≥ 1`. The upper bound has the order of the observed
`0.048·log N/N`; the lower bound is short of it by `log N`. The previous section shows that the sampling route
can recover at most `√log N` of that, and the next section recovers it (`BallGap.rate_gap`).

**Why the alternating vector.** At a zero under RH, `V_x(ρ) = Σ_{n ≤ N}(−1)^{n+1}n^{−s}` with `s = 1 − ρ = ρ̄`: a partial
sum of `η(s) = (1 − 2^{1−s})ζ(s)`, which vanishes there. So at the low zeros only the tail beyond `N` is left, which is
`O(1/√N)` while `|Im s| ≤ 2N`; for `x_n = 1/n` it would be `N^{1−s}/(1 − s)`, of size `√N/|ρ|`, the pole of `ζ` that
`η` does not have. At the high zeros the explicit formula counts, and there Landau's form, `(log N)² + O(log N)` at this
vector, turns the diagonal's `log r` into `log(r/N)`. A dyadic shell at height `R ≥ 8N` contributes
`≪ log(R/N)·H_N/R`, and these are summable. Numerically (`scripts/alt_vector.py`, uncertified):

| `N` | `100` | `300` | `1000` | `3000` | `10⁴` | `3·10⁴` |
|---|---|---|---|---|---|---|
| alternating vector, `q_N·N/log N` | `0.1527` | `0.1524` | `0.1523` | `0.1523` | `0.1522` | `0.1522` |
| near-flat vector `(1 − n/N)²/ψ(n)`, `q_N·N/log N` | `0.1125` | `0.1156` | `0.1185` | `0.1218` | `0.1441` | `0.2870` |
| `λ_N·N/log N` | `0.0509` | `0.0490` | `0.0480` | `0.0473` | | |

So the alternating vector's Rayleigh quotient is `0.1523·log N/N`, `3.0`–`3.2` times `λ_N` where that is computed, and `Q_N(x)` itself, with
`Σ x_n² → π²/6`, is `0.2505·log N/N`. The constant `67` loses a factor of about `440` against `0.1523`. Most of the loss
is at the low zeros (the `20/√N` of the Abel summation) and in the zone `2N < |γ| ≤ 8N`, where only the trivial weight
`1/(4N²)` is used.

**How it was done.**

- **The test function** is `|D(t)|²M_r(t)`, with `BallCutoff`'s majorant `M_r(t) = (r/t)²sin²(πt/2r) ≥ 1_{[−r, r]}`
  extended to `ℂ` as `(r²/4)ĝ_{box}(z)²` (`majC`). It satisfies the strip bound
  `|M_r(z)| ≤ 4r²e^{π/r}/(1 + (Re z)²)` (`norm_majC_le`), and its transform is supported in `|v| ≤ π/r ≤ 1/(2N)` for
  `r ≥ 2πN`. Then the diagonal `(π²r/2)Σc_n²` and the prime side `(πr/4)L(c)` are exact (`integral_hRM`, `prime_eq_M`),
  and `M_r ≥ 1` on `[−r, r]` and `M_r ≥ 0` give the zero side (`zero_side_M`).
- **The archimedean term from above.** Two steps of the digamma recurrence in Stirling's series bound
  `Re ψ(¼ + it/2) ≤ ½log(81/16 + t²/4) + 1/50` for every `t` (`psiRe_le_all`). So the weight is at most
  `log(r/2π) + 1/5 + log⁺(|t|/r)` for `r ≥ 8` (`psiRe_sub_le`). On `|t| > r`, `M_r(t)log(|t|/r) ≤ r²log(|t|/r)/t²`.
  This is dominated by `(729/(1 − 1/π))(E ⋆ F_a)(t)`: `BallSharp`'s envelope, smoothed by the Fejér kernel of
  `a = 1/(2N)` on the windows `|u| ≤ r/2`, which hold mass `1 − 8N/(πr) ≥ 1 − 1/π` (`tail_conv_le_U`). The envelope's
  `|D|²`-mass is exact (`BallSharp.integral_Kc_conv`), and the excess costs `(11/2)rΣc_n²` (`arch_le_M`).
- **The pole**: `|D(±i/2)| ≤ Σ_j|c_j|j^{±1/2}` and `|M_r(i/2)| ≤ 9π²/4 ≤ 23` (`pole_le_M`), which is `46NH_N` at the
  alternating vector.
- **Landau's form at the alternating vector from below** (`landau_xa_ge`). For `c_j = (−1)^{j+1}/√j`,
  `c_j c_{jn} = (−1)^{j(n+1)}/(j√n)`: this is `1/(j√n)` for odd `n`, and at least `−1/(j√n)` for even `n`. The even `n`
  with `Λ(n) ≠ 0` are the powers of `2`, so their terms total at most `H_N log 2` (`sum_even_vonMangoldt_le`).
  `Σ_{n ∣ m}Λ(n) = log m` gives `Σ_n Λ(n)n^{−1}Σ_{jn ≤ N}1/j = Σ_{m ≤ N}(log m)/m ≥ (log N)²/2 − 1`
  (`sum_vonMangoldt_Hf`, `sum_log_div_ge`). Hence `L(c) ≥ (log N)² − 2 − 4H_N log 2`, and with
  `log N ≤ H_N ≤ 1 + log N` this gives `mean_xa_le`.
- **The sum over the zeros** (`form_xa_le`). `Q_N(x) = Σ_ρ|V_x(ρ)|²/(¼ + γ²)` (`BallRate.hasSum_form`), checked on
  every finite set of zeros. The zeros fall into three groups:
  - those with `|γ| ≤ 2N` cost `(400/N)Σ_ρ 1/(¼ + γ²) = 400K_H(1)/N`, with `δ₁` (`hasSum_inv_quarter`);
  - those with `2N < |γ| ≤ 8N` cost `mean_xa_le` at `r = 8N` divided by `4N²`, at most `34H_N/N`;
  - the shell `2^k·8N < |γ| ≤ 2^{k+1}·8N` costs `mean_xa_le` at its top divided by `(2^k·8N)²`, at most
    `(π/16 + 23/640)(k + 20)2^{−k}H_N/N` (`shell_le`), which totals at most `10H_N/N`.
  `K_H(1) < 0.0539` (`WeilTest.hadamard_const_lt`) turns `400K_H(1) + 45` into `67`.
- **The low zeros** (`BallUpperEta`). PNT+'s `ζ₀` (`riemannZeta0`, equal to `ζ` on `Re s > 0` by `Zeta0EqZeta`)
  gives `Σ_{n ≤ X}n^{−s} = ζ(s) + X^{1−s}/(1 − s) + X^{−s}/2 − sI(X)` with `|I(X)| ≤ 2/√X` on `Re s = ½`
  (`ZetaBnd_aux1b`). In `Σ_{n ≤ 2K}(−1)^{n+1}n^{−s} = Σ_{n ≤ 2K}n^{−s} − 2^{1−s}Σ_{m ≤ K}m^{−s}` the terms in
  `X^{1−s}` cancel. So at a zero of `ζ` the partial sums are at most `(1 + 6|s|)/√K` (`eta_partial`, `norm_eta_le`)
  and tend to `0`. The tail from `N` to `2K` is Abel-summed with `τ_n = ((n + 1)/n)^{−s}` and `d_n = 1/(1 + τ_n)`,
  through the identity `u_n = (u_n d_n − u_{n+1}d_{n+1}) + u_{n+1}(d_{n+1} − d_n)`
  (`BallUpper.tail_le`). Its two bounds are:
  - for `|Im s| ≤ 2N` the phase of `τ_n` stays in `[−2, 2]`, so `Re τ_n ≥ cos 2 ≥ −½` and `|d_n| ≤ 2`;
  - `|d_{n+1} − d_n| ≤ 8|s|/(n(n + 1))`.
  Letting `K → ∞` gives `|V_x(ρ)| ≤ 20/√N` (`alt_le`, `dpoly_xa_le`), with `ζ(ρ̄) = 0` from `riemannZeta_conj`.
- **Without RH** (`rate_upper`). `BallWeil.rh_iff_form` gives an integer vector with `Q_{N₀}(x) < 0`. Extended by zero
  it has the same negative value at every `N ≥ N₀` (`form_extend`). Below `N₀`, `δ₁` works with `C = N₀K_H(1)`. So
  `λ_N ≪ log N/N` holds for every `N`, with an ineffective constant, strengthening `BallRate.approach`
  (`lim sup λ_N ≤ 0`).

**Prior work.** Upper bounds of the shape `T log(T/N)` for the discrete mean value over the zeros are those of
Bui–Florea–Milinovich (cited in the `BallCutoff` section), for `N ≤ cT/log²T`. Here the explicit formula gives an
upper bound for every `T ≥ 8N`, at the price of Landau's form, which is exact. The alternating vector's vanishing at
the zeros is the classical identity `η = (1 − 2^{1−s})ζ`.

## The Landau gap from below: `Σx_n² n + G(c) ≥ (√log N/10)Σx_n²`, and `λ_N ≫ √log N/N` under RH (`BallGap`)

**Lean:** `BallGap` (`lib/core/BallGap.lean`), printed by `lib/check/CheckAll.lean`. The three printed results depend on
`propext`, `Classical.choice` and `Quot.sound` only.

| Result | Statement | Conditional on |
|---|---|---|
| `BallGap.gap_ge` | `5Σ_{n ≤ N}c_n² + G(c) ≥ (√log N/2)Σ_{n ≤ N}c_n²/n` for every `N ≥ 3` and every real `c` | nothing |
| `BallGap.edge_law` | `Σ_{n ≤ N}x_n² n + G(c) ≥ (√log N/10)Σ_{n ≤ N}x_n²` for every `N ≥ 3` and every real `x`, `c_n = x_n√n` | nothing |
| `BallGap.rate_gap` | `Q_N(x) ≥ √log N/(220e⁸N)·Σ_{n ≤ N}x_n²` for every `N ≥ 3` and every real `x` | RH |

Here `G(c) = (log N + log 4 + 1)Σc_n² − L(c)` is Landau's slack (`BallSharp.landauSlack`). In the notation of
"Which vectors the slack leaves", `edge_law` says `A + B ≥ √log N/10` at every vector: the spread and the slack
cannot both be small. With `BallSharp.rate_slack` it gives `rate_gap`, so under RH
`√log N/(220e⁸N) ≤ λ_N ≤ 67(1 + log N)/N` for every `N ≥ 3`. The constant is poor: `rate_gap` beats
`BallSharp.rate_sharp`'s `1/(22e⁸N)` only for `log N > 100`. What it settles is the order. The section "Why the
sampling route stops short of `log N/N`" found the gap to be `√log N` numerically; that order is now a lower bound.

**The numbers** (`scripts/landau_gap.py --gap`, uncertified). The minimum of `A + B`, the smallest eigenvalue of
`(log N + c₀ + 1)diag(n) − diag(√n)M diag(√n)` (`M` the matrix of `L`, `c₀ = log 4 + 1`), by inverse iteration, and
two checks of the proof at its weights:

| `N` | `10³` | `10⁴` | `10⁵` | `10⁶` | `10⁷` |
|---|---|---|---|---|---|
| `min(A + B)/√log N` | `2.944` | `2.902` | `2.887` | `2.887` | `2.894` |
| `min(A + B)/√(2(c₀ + γ + 1)log N)` | `1.046` | `1.031` | `1.025` | `1.025` | `1.028` |
| `min(A + B)` over the proved `√log N/10` | `29.4` | `29.0` | `28.9` | `28.9` | `28.9` |
| smallest `d(m)`, `2 ≤ m ≤ N` | `1.77` | `1.82` | `1.85` | `1.87` | — |
| smallest slack of the vertex inequality | `5.62` | `5.57` | `5.54` | `5.51` | — |

The minimum is `2.89`–`2.94` times `√log N` over this range. It is within `5%` of `√(2(c₀ + γ + 1)log N)`, the
profile's prediction below with the grounding `κ_j + 1 ≈ c₀ + γ + 1`. So `√log N` is the right order where it can be
computed. The proof loses a factor `29` in the constant:
- `4` at the small vertices;
- `5` in the factor `5` of `gap_ge`;
- `1.45` in the choice `K = 2log N`, as `D(0) = 2√log N`.

Both checks of the proof hold with room.

**How it was done.**

- **The defect of Landau's form.** On each edge `(j, jn)`,
  `2(Λ(n)/√n)c_j c_{jn} = (Λ(n)/n)c_j² + Λ(n)c_{jn}² − (Λ(n)/n)(c_j − √n c_{jn})²`. Summing with `Σ_{n ∣ m}Λ(n) = log m`
  as in `BallDensity.landau_le_of`, whose Schur test drops the last term, gives
  `G(c) = Σ_j κ_j c_j² + Σ_{n, jn ≤ N}(Λ(n)/n)(c_j − √n c_{jn})²`, where
  `κ_j = log N + log 4 + 1 − Σ_{n ≤ N/j}Λ(n)/n − log j ≥ 0` (`mertens_le_sharp`). This is the ground-state form of the
  section "Why the sampling route stops short", in the variables `c`.
- **Sharing each vertex among its parents.** Give each `m ≥ 2` a weight `d(m) ≥ 0`. Split it among the edges into `m`
  in proportion to `Λ(n)`: the edge `(m/n, m)` gets `Λ(n)d(m)/log m`, and the shares sum to `d(m)`. On each edge
  `(Λ(n)/n)(a − √n b)² + (Λ(n)d/ℓ)b² ≥ (Λ(n)/n)(d/(ℓ + d))a²`, with `ℓ = log m` and `d = d(m)` (`edge_ineq`; the
  difference is `Λ(n)(aℓ − √n b(ℓ + d))²/(nℓ(ℓ + d))`). Summing,
  `G(c) ≥ Σ_j c_j²(κ_j + Σ_{n ≤ N/j}(Λ(n)/n)r(jn) − d(j)[j ≥ 2])`, with `r(m) = d(m)/(log m + d(m))` (`slack_ge`).
  So `5Σc_n² + G(c) ≥ ηΣc_n²/n` follows from the vertex inequality
  `5 + κ_j + Σ_{n ≤ N/j}(Λ(n)/n)r(jn) ≥ η/j + d(j)[j ≥ 2]` at every `j ≤ N`. This is the Allegretto–Piepenbrink
  criterion, with a supersolution that depends on `log m` only. The proportional split is what makes it
  one-dimensional: `r(jn)` sees `log(jn)`, not the factorisation of `jn`.
- **The profile.** In the continuum, with `Σ_{n ≤ y}Λ(n)/n ≈ log y`, the vertex inequality at `j = e^u` reads
  `d(u) ≤ k + ∫_u^{log N} d(s)/(s + d(s))ds`. `D(u) = √(u² + 2K) − u` solves it with equality for `k = D(log N)`,
  since `D/(s + D) = 1 − s/√(s² + 2K) = −D′`, and `D(0) = √(2K)`. To compare the sum with the integral:
  - Abel summation against Mertens from below, `Σ_{n ≤ k}Λ(n)/n ≥ log k − 1` (`mertens_ge`, from Stirling's
    `log k! ≥ k log k − k`, Mathlib's `Real.le_sum_log_nat`), with the concavity of `−D` (`abel_ge`, `tele_ge`,
    `prof_step`);
  - which gives `Σ_{n ≤ N/j}(Λ(n)/n)·D/(s + D) at s = log(jn) ≥ D(log j) − D(log N) − 1 − log 2` (`child_ge`).
  The factor `5` pays for `D(log N) ≤ 2` and the `1 + log 2`.
- **The small vertices.** Once `j < η`, the target weight `η/j` is more than the factor `5` can pay. The weights
  `d(m) = D(log m) − 4η/m` push the cost onto the parents. Lowering `d(m)` by `4η/m` costs each parent `j = m/n` at most
  `(Λ(n)/n)·4η/(m log m) ≤ 4η/(jn²)` (`rr_ge`), in all at most `3η/j`, since `Σ_{n ≥ 2}1/n² ≤ 3/4`
  (`sum_inv_sq_le`). It frees `4η/j` at `j` itself. At the root the cost is `3η`, paid by `D(0) = √(2K)`. With
  `K = 2log N` and `η = √log N/2`, `D(0) = 4η`, and `d(m) ≥ 0` for every `m ≥ 2` once `log N ≥ 1` (`prof_ge`, from
  `√log N(m² − 1) ≥ m log m`).

**Prior work.** The method is the ground-state transform of W. Allegretto (Pacific J. Math. 55 (1974)) and
J. Piepenbrink (J. Differential Equations 15 (1974)): a positive supersolution of a Schrödinger operator bounds its form
from below. Its form on weighted graphs, with optimal Hardy weights, is M. Keller, Y. Pinchover and F. Pogorzelski,
Comm. Math. Phys. 358 (2018). Here the graph is the divisibility graph of `[1, N]` with the weights of Landau's form.
The bound on its slack, and the rate it gives, are new as far as this note knows.
