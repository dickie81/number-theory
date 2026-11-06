# The evaporation rate of the orbit form: witness level, approach, rate

**Lean:** `BallRate` (`lib/core/BallRate.lean`), printed by `lib/check/CheckAll.lean`, with `BallSampling`,
`BallDensity`, `BallCutoff` and `BallSharp` in four later sections, then `BallUpper` with `BallUpperEta`, `BallGap`,
and `BallLow` in the third from last. The theorems are mapped onto the gravastar
language in the section after the statements; the first section, written before the Lean, fixes the three statements
and says what each costs. The rate, open when that section was written, is now proved under RH alone:
`λ_N ≥ 1/(22e⁸N)` for every `N ≥ 1` (`BallSharp.rate_sharp`, last section). It comes from the sampling conjecture of
the section "What is missing", which `BallCutoff.sampling_rh` proves under RH with `c = 1/100` and `C = e²⁴`, and
`BallSharp.sampling_e8` with `c = 1/11` and `C = e⁸`. `BallSharp.sampling_log` gives sampling its natural form: a
frame bound `(T/11)(log(T/N) − 7)`, which grows like the number of zeros up to `T`. The rate from above is proved too
(`BallUpper`, `BallUpperEta`, last section): `λ_N ≤ 67(1 + log N)/N` under RH, by the alternating vector
`x_n = (−1)^{n+1}/n`, and `λ_N ≤ C(1 + log N)/N` with some constant `C` unconditionally (`BallUpperEta.rate_upper`).
Under RH `λ_N` is therefore between `1/(22e⁸N)` and `67(1 + log N)/N`. Numerically it is `0.048·log N/N` for
`N ≤ 2000`, and `λ_N·N = 0.0434·log N + 0.032` to within `2·10⁻⁴` for `10³ ≤ N ≤ 3·10⁴` (section "The low zeros"). Keeping
Landau's slack `G(c)`, `BallSharp.rate_slack` reduces the missing `log N` of the lower bound to the vectors with
`Σx_n² n + G(c) = o(log N·Σx_n²)` (section "Why the sampling route stops short of `log N/N`"). Every vector has
`Σx_n² n + G(c) ≥ (√log N/10)Σx_n²` (`BallGap.edge_law`, last section), so under RH `λ_N ≥ √log N/(220e⁸N)` for every
`N ≥ 3` (`BallGap.rate_gap`): this route recovers `√log N` of the missing `log N`, which by the numerics of that
section is all it can give. The section "Packing", numerics only, compares the zeros with point sets of the same
density and no arithmetic, which give `λ_N` near `N^{−1/2}` for `N ≤ 6400`, and finds the shape of the minimiser: `w(n/N)/ψ(n)`, `ψ`
Dedekind's function, with `w(u) = Σ_{k ≤ 1/u} c(ku)` for one fixed function `c`. The section "The variational
problem, solved" derives the constant at leading order, heuristically:
`λ_N·N/log N → (1/12)(T + κP²)/D = 0.0429`, with `κ = 0.096` from the profile and `T`, `P`, `D` Euler products.
The section after it proves the matching upper bound on paper, for an explicit vector:
`λ_N ≤ (0.04294 + o(1))·log N/N` under RH. The last section proves, on that class of vectors, the inverse
theorem (quiet at the zeros means carrying `ζ`, and costs `≥ 0.0400·log N/N`) and the absence of any sag at the
picket fence. It also proves, for every vector and with no hypothesis,
`λ^pf_N ≍ N^{−3/5}log N` at the picket fence: a power of `N` above the zeros' `λ_N`, so that `λ^pf_N ≫ N^{−1/2}`
fails. Its
numerics measure what silence at the zeros costs over all vectors:
`≍ log N` in `A + B` at heights `≍ N`, carried by the `⌊2πN/T⌋` dilates of the zeta vector, where the fence pays
`≍ T log N`.

## The three statements, and what can be proved

**Setting.** `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n)` is `BallWeil.form N x`, with `K_H` computed from the primes
(`BallWeil.kψ`, equal to `BallHadamard.kerH` on `x > 0`): `K_H(r) = Σ_ρ r^{ρ−½}/(ρ(1 − ρ))` over the nontrivial zeros
with multiplicity, `K_H(1) = H₀ := 2 + γ_E − log 4π ≈ 0.0462`. Write `a_ρ = 1/(ρ(1 − ρ))`, so `Σ_ρ a_ρ = H₀` and every
`Re a_ρ > 0`; and `λ_N = min{Q_N(x) : Σ x_n² = 1}`, the smallest eigenvalue of the Gram matrix `G_N`. Then
`Q_N(x) = Σ_ρ a_ρ V_x(ρ) V_x(1 − ρ)` with `V_x(s) = Σ_{n ≤ N} x_n n^s`, which under RH is `Σ_ρ |V_x(ρ)|²/(¼ + γ²)`.
Numerically (`scripts/ball_rate.py`, with the first 30000 zeros from `scripts/zeta_zeros_rs.py`):
`λ_N = (0.048 ± 0.002)·log N/N` for `100 ≤ N ≤ 2000`, which up to `N = 3·10⁴` is the law
`λ_N·N = 0.0434·log N + 0.032` (section "The low zeros"); the minimising vector is
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
| smallest `d(m)`, `2 ≤ m ≤ N` | `1.77` | `1.82` | `1.85` | `1.87` | `1.89` |
| smallest slack of the vertex inequality | `5.62` | `5.57` | `5.54` | `5.51` | `5.50` |

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

## The low zeros: what the zeros above `8N` give, and `λ_N` to `N = 3·10⁴` (`BallLow`; `scripts/lambda_large.py`)

**Lean:** `BallLow` (`lib/core/BallLow.lean`), printed by `lib/check/CheckAll.lean`. The two printed results depend on
`propext`, `Classical.choice` and `Quot.sound` only.

| Result | Statement | Conditional on |
|---|---|---|
| `BallLow.short_le` | `Q_N(x) ≥ Σ_{n ≤ N}x_n²/(22e⁸M)` for every `x` with `x_n = 0` for `n > M`, `1 ≤ M ≤ N` | RH |
| `BallLow.high_le` | `Σ_{ρ ∈ F}\|V_x(ρ)\|²/(¼ + γ²) ≤ (4Σc_n² + G(c)/2)/N + (Σ_j\|c_j\|√j)(Σ_j\|c_j\|/√j)/N²` for every finite set `F` of zeros of height `\|γ\| > 8N`, `c_n = x_n√n` | RH |

`short_le` is `BallUpper.form_extend` with `BallSharp.rate_sharp` at `M`. `high_le` is `BallUpper.upper_mean` on the
dyadic shells `2^k·8N < |γ| ≤ 2^{k+1}·8N`. Shell `k` costs `π/(16·2^k N)·(((k + 4)log 2 + 1/5 + 22/π − log 4 − 1)Σc² + G)`
plus a pole term, and the sum over `k` is `(4Σc² + G/2)/N` and the pole term. In terms of the spread
`A = Σx_n² n/Σx_n²` and the slack `B = G(c)/Σx_n²`, the zeros above `8N` contribute at most `(4A + B/2)Σx_n²/N`, plus
`(Σ|x_j| j)(Σ|x_j|)/N²`. The pole term is small for the vectors below: they are concentrated at small `n`, or spread
like `1/n`. `rate_slack` gets `(A + B)/(22e⁸N)` from the zeros up to `e⁸N`. So the zeros above `8N` give the order
`(A + B)/N` and no more, and `λ_N ≫ log N/N` holds or fails on the vectors with `A + B = o(log N)`. For those, the
missing factor has to come from the zeros below height `8N`. By `short_le`, a vector with `Q_N(x) ≤ ε(log N/N)Σx_n²`
is not supported below `N/(22e⁸ε log N)`.

**`λ_N` to `N = 3·10⁴`** (`scripts/lambda_large.py`, uncertified). The orbit form is built from the primes in column
blocks and factored in place by Cholesky. Block inverse iteration gives the bottom of its spectrum, and `A` and `B` are
read off at the minimiser. The floor of `A + B` is `min(A + B) ≈ 2.9√log N` (section "The Landau gap from below").

| `N` | `10³` | `2·10³` | `4·10³` | `8·10³` | `1.2·10⁴` | `1.6·10⁴` | `2·10⁴` | `2.5·10⁴` | `3·10⁴` |
|---|---|---|---|---|---|---|---|---|---|
| `λ_N·N/log N` | `0.04803` | `0.04756` | `0.04722` | `0.04694` | `0.04678` | `0.04667` | `0.04661` | `0.04652` | `0.04647` |
| `λ_N·N` | `0.3318` | `0.3615` | `0.3916` | `0.4219` | `0.4394` | `0.4518` | `0.4616` | `0.4711` | `0.4791` |
| `λ₂/λ₁`, `λ₃/λ₁` | `3.83, 7.72` | `3.86, 7.82` | `3.88, 7.89` | `3.90, 7.97` | `3.91, 8.01` | `3.92, 8.04` | `3.92, 8.05` | `3.93, 8.07` | `3.93, 8.09` |
| minimiser `A/log N`, `B/log N` | `0.467, 1.443` | `0.458, 1.418` | `0.451, 1.400` | `0.445, 1.385` | `0.443, 1.377` | `0.441, 1.372` | `0.439, 1.368` | `0.438, 1.365` | `0.437, 1.362` |
| minimiser `(A + B)/log N` | `1.910` | `1.876` | `1.851` | `1.831` | `1.820` | `1.813` | `1.808` | `1.803` | `1.799` |
| floor `2.9√log N/log N` | `1.10` | `1.06` | `1.01` | `0.97` | `0.95` | `0.93` | `0.92` | `0.91` | `0.90` |

- **A line in `log N`.** By least squares, `λ_N·N = 0.04335·log N + 0.0322`, with largest residual `1.8·10⁻⁴` and no
  pattern in the signs. The best `a·√log N + b` has `b = −0.34` and largest residual `2.3·10⁻³`, with systematic signs. A
  power `c(log N)^β` gives `β = 0.919` and `4.3·10⁻⁴`. The local exponent `d log(λ_N N)/d log log N` rises from `0.90`
  to `0.94`, as a line with a positive intercept requires. So `0.048·log N/N` was this law at `N ≤ 2000`, with the
  intercept folded in, and the asymptotic constant is about `0.043`.
- **The minimiser stays away from the floor.** Its `A + B` falls by `6%` against `log N`, the floor by `18%`; it sits
  at about twice the floor, and the ratio grows. It is the `ζ`-like vector: `n·x_n` has a fixed profile in `n/N`, and
  `A ≈ 0.44 log N`.
- The ratios `λ₂/λ₁` and `λ₃/λ₁` rise slowly, to `3.93` and `8.09` at `N = 3·10⁴`.
- Above `N ≈ 2·10⁴`, OpenBLAS's multithreaded Cholesky crashed on the machine that ran this, so the script runs it
  single-threaded. A single-threaded rerun at `N = 2·10⁴` gave the same digits.

**The frontier** (`--frontier`). For `μ = s·log N/N`, the minimiser of `Q_N + μ(A + B)Σx_n²` gives one point
`(A + B, Q_N)`:

| `s` | `N = 2·10³`: `Q·N/log N` (`(A+B)/log N`) | `N = 8·10³` | `N = 1.6·10⁴` |
|---|---|---|---|
| `0` | `0.0476` (`1.876`) | `0.0469` (`1.831`) | `0.0467` (`1.813`) |
| `0.01` | `0.0578` (`1.477`) | `0.0592` (`1.407`) | `0.0599` (`1.380`) |
| `0.1` | `0.1326` (`1.195`) | `0.1492` (`1.125`) | `0.1557` (`1.103`) |
| `1` | `0.3755` (`1.088`) | `0.4910` (`1.001`) | `0.5663` (`0.969`) |
| `10` | `0.8184` (`1.067`) | `1.1210` (`0.976`) | `1.4101` (`0.938`) |
| `100` | `1.8167` (`1.063`) | `2.3847` (`0.971`) | `2.8829` (`0.933`) |
| floor | `1.062` | `0.969` | `0.931` |

At every `s > 0`, `Q·N/log N` grows with `N` while `A + B` follows the floor down. Near the floor, a vector pays more
`Q`, relative to `log N/N`, as `N` grows. A rate below `log N/N` would need the opposite.

**The low modes of `A + B`** (`--modes`, `N = 10⁵`):

- **Where they sit.** The `k`-th eigenvector sits at `n = k` with its star of prime powers, `99%` of its mass on four
  entries. Its eigenvalue is `λ_k(A + B) = c_k·k√log N` with `c_k = 2.89, 3.11, 3.21, 3.29, 3.33, 3.39, 3.41, 3.45`.
- **At the low zeros.** All eight look like `αN^ρ/ρ`, the boundary term of the truncated prime sum `Σ_{q ≤ N}Λ(q)q^{ρ−1}`,
  with nearly the same `α`: `|α|√N = 35`–`56`. The relative residual of that fit is `14`–`58%`, and it shrinks with
  `N` (`48%` to `14%` for the first mode from `N = 10⁴` to `10⁵`).
- **On their span.** The smallest eigenvalue of `Σ_{j ≤ J}2|V_x(ρ_j)|²/(¼ + γ_j²)` on the span of the first `d` modes
  is `0.14`–`0.21` for `d = 1`, `1.9·10⁻³`–`1.0·10⁻²` for `d = 2`, and `2.3·10⁻³`–`5.7·10⁻³` for `d = 8` once
  `J ≥ 10` (zero for `J < d/2`). Against `log N/N = 1.2·10⁻⁴` that is `20` to `1800` times as much.

**What a proof of `λ_N ≫ log N/N` would need.** Three steps; the first is proved, the other two are numerics and
heuristics:

1. **The high zeros are capped** (`high_le`): above `8N` they give `O((A + B)/N)`.
2. **The low zeros can be silenced cheaply.** At a zero under RH, the vector `x_n = 1/n` has
   `V_x(ρ) = Σ_{n ≤ N}n^{ρ−1} = ζ(ρ̄) + N^ρ/ρ + O(N^{−1/2}) = N^ρ/ρ + O(N^{−1/2})`. So subtracting `α·(1/n)` from a mode
   removes its loud term at every zero at once.
   - **The cost.** Its `Σx_n² n + G` is `4.15·log N` at `N = 10⁵`, so the cost is `α²·4.15·log N`. For the first
     mode `α = 1.9/log N`, and the cost is `15/log N`.
   - **The residual.** It can then be cancelled zero by zero with oscillating tails near `n = N`, at a cost of order
     `log N/N` in `A + B` per zero.
   - **Consequence.** An argument that uses `o(N/log N)` zeros, any number of low zeros with the zeros above `8N`,
     can be defeated by such vectors and stays at `√log N/N`. The frontier shows the first step. At `N = 2000` the
     floor itself has `Q·N/log N = 3.76`. Raising `A + B` by `0.001·log N` halves that (`s = 100`), and raising it by
     `0.026·log N` divides it by `10` (`s = 1`).
3. **The zeros below `N`.** A proof has to show that silencing a vector at the `≍ N` zeros below height `N` costs
   `A + B ≳ log N`. Two difficulties:
   - **The explicit formula.** At those heights it is no longer exact: the pairs with `|log(jk/j′)| < 1/T` enter.
   - **The large sieve.** It bounds the cost from below only through an upper mean value for Dirichlet polynomials at
     the zeros below their length. The standard bound has a term `N log N`, which loses the whole factor: fed into
     the split into a short head and a long tail, it gives `1/N`.

   What is missing is a mean value at the zeros below height `N` that tells the `ζ`-multiples from the incoherent
   tails, at about the strength of the pair-correlation conjecture beyond `α = 1`.

## Packing: what the zeros allow that a fence does not (`scripts/packing.py`, uncertified)

Step 3 above asks what it costs to make a vector quiet at the zeros below height `N`. For points with the zeros'
density and no arithmetic, a packing count answers that, and numerically the answer is `λ_N ≍ N^{−1/2}`. The zeros
beat the count by a factor `√N/log N`, because the minimiser carries `ζ` as a factor and the zeros below `N` come
with it.

**The count.** At height `T` a Dirichlet polynomial of length `N` resolves its frequencies `log n` at spacing `2π/T`:
each `n ≤ T/2π` on its own, and the band `[log(T/2π), log N]` at density `T/2π`. In `[T, 2T]` that is about
`(T/2π)(1 + log(2πN/T))` degrees of freedom, against `Φ(2T) − Φ(T) = (T/2π)log(4T/2πe)` points, where
`Φ(t) = (t/2π)log(t/2πe) + 7/8` is the smooth zero count. Room for all of them needs `T ≤ πe√N ≈ 8.5√N`. Above that
height a point set without arithmetic cannot all be silenced, and the points left over charge `λ_N` of order `N^{−1/2}`,
up to logarithms. The count bounds what can be silenced exactly, not the residual. The last section proves
`λ^pf_N ≍ N^{−3/5}log N` for every vector at the fence. So `N^{−1/2}` is a pre-asymptotic phase,
which the fence's constrained minima still show at `N = 12800`.

**Three point sets with the zeros' density.**

- The picket fence: the `k`-th point at `Φ = k − ½`.
- Jittered pickets: the `k`-th point uniform in `Φ ∈ [k − 1, k]`.
- A Poisson process of intensity `Φ'`.

The points are explicit up to `16N` and replaced by their density beyond. Moving that cut to `64N` changes `λ_N` in the
fifth digit at `N = 100` and `400`. The zeros' column is the prime-side Gram matrix.

| `N` | `100` | `200` | `400` | `800` | `1600` | `3200` | `6400` |
|---|---|---|---|---|---|---|---|
| zeros: `λ_N·N/log N` | `0.0509` | `0.0489` | `0.0485` | `0.0481` | `0.0478` | `0.0474` | `0.0470` |
| zeros: `λ_N·√N` | `0.0234` | `0.0183` | `0.0145` | `0.0114` | `0.0088` | `0.0068` | `0.0051` |
| picket fence: `λ_N·√N` | `0.1131` | `0.1160` | `0.1173` | `0.1193` | `0.1229` | `0.1270` | `0.1315` |
| jittered (two seeds): `λ_N·√N` | `0.159, 0.159` | `0.162, 0.162` | `0.174, 0.167` | `0.186, 0.171` | `0.186, 0.180` | `0.184, 0.187` | |
| Poisson (two seeds): `λ_N·√N` | `0.253, 0.134` | `0.220, 0.181` | `0.244, 0.185` | `0.309, 0.222` | `0.264, 0.188` | `0.279, 0.276` | |

- **The exponents.** The slope of `log λ_N` against `log N` from `100` to `3200` is `−0.857` for the zeros, where
  `log N/N` gives `−1 + 1/log N`. It is `−0.468` for the fence, `−0.450` and `−0.452` for the jittered pickets, and
  `−0.448` and `−0.339` for the Poisson sets.
- **The fence against the zeros.** `λ_N·√N` for the fence drifts from `0.110` at `N = 50` to `0.132` at `6400`, and
  the slope from `100` to `6400` is `−0.465`. The fence's `λ_N` is `4.8` times the zeros' at `N = 100` and `25.5`
  times at `N = 6400`.
- **The fence's minimiser is `δ₁` plus a tail.** It has `x₁` from `0.983` at `N = 100` to `0.997` at `3200`, and
  `A/log N` falling from `0.39` to `0.29`. The tail is spread over large `n`, small in `Σx_n²`, and cancels `x₁` at the
  low points.

**How far up each minimiser stays quiet** (`--silence`). The table gives the mean of `|V_x(γ)|²/Σx_n² n` over the
points in `[T, 2T]`, at `N = 1600` (`√N = 40`, the zeros from the first 30000).

| `T` | `64` | `128` | `256` | `512` | `1024` | `2048` | `4096` | `8192` |
|---|---|---|---|---|---|---|---|---|
| `T/√N`, `T/N` | `1.6`, `0.04` | `3.2`, `0.08` | `6.4`, `0.16` | `12.8`, `0.32` | `25.6`, `0.64` | `51`, `1.28` | `102`, `2.56` | `205`, `5.12` |
| zeros, at their minimiser | `0.0000` | `0.0000` | `0.0001` | `0.0003` | `0.0010` | `0.0041` | `0.0156` | `0.1203` |
| fence, at its minimiser | `0.0003` | `0.0047` | `0.0990` | `0.1923` | `0.2988` | `0.4151` | `0.5075` | `0.9253` |
| jittered, at its minimiser | `0.0024` | `0.0645` | `0.2069` | `0.3957` | `0.7032` | `0.8480` | `0.9670` | `0.9919` |
| the zeros' minimiser at the fence | `0.336` | `0.414` | `0.491` | `0.570` | `0.645` | `0.704` | `0.720` | `0.960` |
| the fence's minimiser at the zeros | `0.807` | `0.858` | `0.426` | `0.443` | `0.483` | `0.512` | `0.528` | `0.568` |

- **Where each goes loud.** The fence goes loud at a few `√N`, as the count says. The zeros stay below `10⁻³` up to
  `T ≈ 1.3N` and below `0.016` up to `5N`, which is where the `92%` of `Q_N` above `4N` comes from.
- **Neither minimiser is quiet on the other set.** The quietness is specific to the points.
- `N = 800` gives the same picture: the fence goes loud at `T ≈ 4√N`, the zeros at `T ≈ 5N`.

**Why the zeros beat the count: the minimiser carries `ζ` twice** (`--ground`). The minimiser is
`x_n ≈ x₁·w(n/N)/ψ(n)`, with `ψ(n) = n·Π_{p | n}(1 + 1/p)` Dedekind's function and `w` a staircase.

- **Multiplicative, with local factor `p/(p + 1)`.** With `f(n) = n·x_n/x₁`, `f(mn)/(f(m)f(n))` is within `2%` of `1`
  for coprime `m, n` at `N = 4000` and `16000`. `f(p)` is `p/(p + 1)` to `0.006` for `p ≤ 31`: `0.668, 0.748, 0.829,
  0.870` at `p = 2, 3, 5, 7`, at `N = 16000`.
  - **The measured factors.** Dividing `f` by its own local factors (`f` at the prime powers below `N/10`) leaves a
    profile in `n/N` with half-interquartile scatter `0.1%` on `n ≤ N/100` and `1%` on `[N/20, N/10]`.
  - **`n/ψ(n)`.** Dividing by `n/ψ(n)` instead leaves `2`–`3%`, mostly from the higher prime powers: `f(2^k)` tends to
    `0.60`, not `2/3`. In the quotient below the two do equally well (`1.097` and `1.099` at `N = 4000`, smooth `w` in
    32 B-splines).
- **`p/(p + 1)` is the optimum.** With `F(p^k) = 1 − θ/(p + 1)` for every `k ≥ 1`, `x_n = F(n)w(n/N)/n` and the best
  staircase `w`, the smallest Rayleigh quotient over `λ_N` at `N = 4000` is `1.205, 1.072, 1.036, 1.031, 1.030, 1.033,
  1.041, 1.088` at `θ = 0, 0.5, 0.8, 0.9, 1, 1.1, 1.2, 1.5`. The factor `φ(n)/n` gives `1.066`, and the best
  `1 − θ/p` gives `1.035`.
- **The profile is a staircase of a fixed function.** The best `w` has jumps at `u = 1/2, 1/3, …`. It is
  `w(u) = Σ_{k ≤ 1/u} c(ku)` with one function `c` on `[0, 1]`. The smallest quotient over `λ_N`:

  | `N` | `2000` | `4000` | `8000` | `1.6·10⁴` | `3·10⁴` |
  |---|---|---|---|---|---|
  | `w` smooth, 16 cubic B-splines | `1.133` | `1.190` | `1.233` | | |
  | staircase, `c` in 8 B-splines | `1.034` | `1.032` | `1.031` | | |
  | staircase, `c` in 16 B-splines | `1.032` | `1.030` | `1.030` | `1.029` | `1.029` |

  A smooth profile gets worse with `N`; the staircase does not. Twisting the staircase, `Σ_k a(k)c(ku)` with
  `a(k) = k/ψ(k)`, `φ(k)/k` or `μ²(k)`, is worse by factors `10` to `340`.
- **`c` does not depend on `N`.** It is recovered by Möbius inversion, `c(u) = Σ_k μ(k)w(ku)`, with `w(1/N) = 1`:

  | `u` | `0.02` | `0.12` | `0.22` | `0.32` | `0.42` | `0.52` | `0.62` | `0.72` | `0.82` | `0.92` |
  |---|---|---|---|---|---|---|---|---|---|---|
  | `N = 2000` | `−1.989` | `−1.694` | `−1.119` | `−0.378` | `0.310` | `0.859` | `1.051` | `1.056` | `0.844` | `0.455` |
  | `N = 8000` | `−1.990` | `−1.697` | `−1.121` | `−0.377` | `0.315` | `0.863` | `1.055` | `1.058` | `0.841` | `0.448` |

  The two rows differ by at most `0.007`, and `N = 4000` agrees with both to `0.003`. At every `N`,
  `∫_{0.02}^1 c = 0.040`, and `c ≈ −2` on `[0, 0.02]`. So `∫_0^1 c = 0` to three digits and `c(0) = −2`, which is
  `w(0) = −c(0)/2 = 1` by Euler–Maclaurin.
- **The mechanism** (heuristic). Write `𝓕(s) = Σ_n (n/ψ(n))n^{−s} = ζ(s)M(s)`, with
  `M(s) = Π_p(1 − p^{−s}/(p + 1))` absolutely convergent on `Re s > 0`. The staircase has Mellin transform
  `ŵ(z) = ζ(z)ĉ(z)`. Then `V_x(ρ) = (1/2πi)∫ζ(1 − ρ + z)M(1 − ρ + z)ζ(z)ĉ(z)N^z dz`, and shifting left past `Re z = 0`
  meets three residues, each zero at every zero `ρ`:
  - at `z = 0`, `ζ(0)c(0)·ζ(1 − ρ)M(1 − ρ) = 0`: the bulk;
  - at `z = ρ`, `M(1)ĉ(ρ)·ζ(ρ)N^ρ = 0`: the loud boundary term `N^ρ/ρ` of step 2, now silent at every zero at once;
  - at `z = 1`, `ĉ(1)N·𝓕(2 − ρ) = 0`, because `∫c = 0`.

  What is left is the integral on `Re z < 0`, small while `γ ≪ N`. So the zeros below height `≍ N` cost one box in
  all, not one box each.
- **The price is the spread.** Carrying `ζ` over `[1, N]` costs `Σx_n² n ≈ C_F log N·Σx_n²/D`. Here
  `C_F = Π_p(1 − (2p + 1)/(p(p + 1)²)) = 0.529` is the mean of `(n/ψ(n))²` and `D = Σ1/ψ(n)² = 1.320`, so
  `A/log N → 0.401`. The diagonal of Landau's slack adds `log 4 + 1 + γ = 2.96` per unit of `Σc_n²`, and its edges
  `0.098·C_F`, so `B/log N → 1.23`. The measured values at `3·10⁴` are `0.437` and `1.362`, both still falling.
  `high_le` charges `A + B` at the zeros above `8N`.
- **The ladder.** `K_H` depends on `m/n` only, so `G_{km,kn} = k·G_{mn}`. The dilation `(D_k x)_{kn} = x_n` therefore
  has `Q_N(D_k x) = k·Q_{N/k}(x)` and `‖D_k x‖ = ‖x‖`. The dilated minimiser of `Q_{N/k}` therefore has quotient
  `k·λ_{N/k} ≈ k²·0.0434·log N/N`: the ladder, up to the overlaps between the dilates. Fitted at `N = 2000, 4000,
  8000`, the low eigenvalues have `λ_k·N ≈ a_k log N + b_k` with `a_k = 0.0435, 0.1794, 0.3852, 0.7173`, in the
  ratios `1 : 4.12 : 8.85 : 16.48`.

**What this changes in step 3.** The count that gives the fence its `√N` gives the zeros nothing: a polynomial of
length `N` can be quiet on every zero up to height `≍ N`. A lower bound `λ_N ≫ log N/N` therefore cannot come from
counting zeros. It has to be an inverse theorem: a vector quiet at the zeros up to height `≍ N` carries the factor
`ζ`, through `n/ψ(n)` in the bulk and the staircase at the cut, and carrying it costs `A ≍ log N`. The last section
measures this over all vectors (its paragraph "What silence costs"). Silence at the zeros up to height `cN` costs
`A + B ≈ a_c + 1.4 log N`, and the only silent directions the zeros add to a fence's are the `⌊2πN/T⌋` dilates of the
zeta vector. The continuum limit
reduces the constant to a variational problem in one function: `0.0434` is, to within `3%`, the minimum over `c` with
`∫c = 0` of the quotient of `x_n = Σ_{k ≤ N/n} c(kn/N)/ψ(n)`, times `N/log N`. The next section solves it.

## The variational problem, solved: `λ_N ~ 0.0429·log N/N` (`scripts/packing.py --solve`; heuristic, uncertified)

The constant comes out of three parts:

1. **A reduction to `N = ∞`.** It is heuristic.
2. **A profile problem.** A quadratic problem for one function on `[0, 1]`, with no `N` in it, solved numerically.
3. **An arithmetic problem.** Euler products, optimised prime by prime.

**The reduction.**
- **The class of vectors.** Write `n·x_n = Σ_{d | n} E_d(n/N)`, each `E_d` a fixed function on `[0, 1]` (zero beyond 1).
  Put `e(d) = E_d(0)` and `F = 1 ∗ e`, so `x_n → F(n)/n` for fixed `n`. Take a zero `ρ` at height `γ = 2πτN`.
- **Three terms for each `d`.** The smoothed approximate functional equation splits `Σ_m E_d(dm/N)m^{ρ−1}` into:
  - `e(d)ζ(1 − ρ)`, which vanishes;
  - the boundary term `(N/d)^ρÊ_d(ρ)`. These add up to `N^ρĜ(ρ)` with `G = Σ_d E_d/d`. That vanishes at every zero
    exactly when `G` is a staircase `Σ_k c(k·)` with `c` continuous: the condition of the previous section;
  - the dual sum `−χ(1 − ρ)Σ_k k^{−ρ}Δ_d(τd/k)`, where `Δ_d(y) = e(d) − E_d(y)`.
- **The dual sum over ratios.** Summed over `d` it is a sum over the ratios `d/k = a/b`, in lowest terms. The
  coefficient of `(a/b)^{iγ}` is `(ab)^{−1/2}H_a(τa/b)`, with `H_a = Σ_g Δ_{ag}/g`. Its mean square over the zeros near
  `γ` is the diagonal `Σ_{(a,b) = 1}H_a(τa/b)²/ab`, up to Landau's `O(1/log N)`.
- **The `τ`-integral factors out.** Weighting by `1/|ρ|²` and the zero density `(log N)/2π` gives

  `Q_N(x)·N/(log N·Σx_n²) → (1/12D)·Σ_{a ≥ 1} ω_a ∫_0^∞ H_a(y)² dy/y²`,

  with `ω_a = Π_{p | a}(1 − p⁻²)` and `D = Σ_n F(n)²/n²`. The `1/12` is `ζ(2)/2π²`.

**The minimum.**
- **Above `y = 1`.** There `H_a = S(a) := Σ_g e(ag)/g` whatever the profiles. So for `a ≥ 2` the best choice is
  `H_a = 0` on `[0, 1]`, a sharp cut for `d ≥ 2`, at cost `S(a)²` each.
- **At `a = 1`.** `G = S(1)·w` with `w` a staircase, and the cost is `S(1)²·I[c]`, where

  `I[c] = ∫_0^∞ (1 − W(x))² dx`, `W(x) = Σ_{1 ≤ k ≤ x} c(k/x)`, `W = 0` for `x < 1`.

  This is `∫(1 − w(y))²dy/y²` in `x = 1/y`. `I` is finite only if:
  - `c(0) = −2` and `∫c = 0`, or `W` does not tend to `1`;
  - `c(1) = 0` and `c` is continuous, or `W` keeps a sawtooth that does not decay.
- **The two problems separate:**

  `λ_N·N/log N → Λ* = min_e (1/12)·(T(e) + (I_min − 1)·P(e)²)/D(e)`,

  with `P = S(1) = Σ_d e(d)/d` and `T = Σ_a ω_a S(a)²`. `T`, `P` and `D` are Euler products in the local factors
  `F(p^v)`. Write `κ = I_min − 1`.
- **The optimal vector is additive:** `x_n = (F(n) − P·(1 − w(n/N)))/n`. The bulk weight `F(n)/n` has a sharp cut, and
  the staircase correction carries no arithmetic.
- **The separable vectors `F(n)w(n/N)/n` of the previous section** are the special case `G_a = S(a)w` for every `a`.
  They give `K(F)·I[c]` with `K = T/12D`. The additive form beats them by moving the profile onto `a = 1` alone.

**The profile problem: `I_min = 1.0959`.** `c` is a cubic spline on `[0, 1]` under the three constraints. The
quadrature is Gauss–Legendre on each `[k, k + 1]` up to `x = 300`. Beyond that the tail is
`(c'(1)²/720 + c'(0)²/144)/x²` from Euler–Maclaurin: `1 − W ≈ −(c'(1)B₂({x})/2 − c'(0)/12)/x`.

| knots | 16 uniform | 32 | 64 | uniform plus kinks at the rationals of denominator `≤ 4`, `6`, `8`, `10` |
|---|---|---|---|---|
| functions | 16 | 32 | 64 | 31, 49, 80, 113 |
| `I_min` | `1.1014` | `1.0981` | `1.0970` | `1.0973`, `1.0966`, `1.0963`, `1.0959` |

- **The kinks matter.** `W` couples `c` at rational multiples, so the minimiser has corners at the rationals.
- **The limit.** It is about `1.095`, so `κ ≈ 0.096`.
- **The minimiser.** Its slope at `u = 1` is `c'(1) ≈ −7`: `c` climbs from `0` to about `1` within `0.3` of `u = 1`,
  which keeps `W` near `1` on `(1, 2)`. Against the profile recovered from the minimiser of `Q_N` at `N = 8000`:

  | `u` | `0.02` | `0.12` | `0.22` | `0.32` | `0.42` | `0.52` | `0.62` | `0.72` | `0.82` | `0.92` |
  |---|---|---|---|---|---|---|---|---|---|---|
  | `c_opt` | `−1.992` | `−1.726` | `−1.142` | `−0.389` | `0.299` | `0.885` | `1.076` | `1.068` | `0.860` | `0.462` |
  | `N = 8000` | `−1.990` | `−1.697` | `−1.121` | `−0.377` | `0.315` | `0.863` | `1.055` | `1.058` | `0.841` | `0.448` |

**The arithmetic problem.**
- **At `κ = 0`.** It splits into one generalized eigenproblem per prime.
  - The minimum is `K_min = 0.040021`, against `K(ψ) = 0.040162` for `F = n/ψ(n)` and `1/(2π²) = 0.050661` for `F = 1`.
  - The optimal `F(2^v)` are `0.676, 0.629, 0.619, 0.616`, tending to `0.615`.
  - For large `p` the optimum is `1 − 1/(p + 1) + O(p⁻⁴)`. That is why the minimiser looked like `ψ`.
- **At `κ = 0.0959`.** The coupling through `P²` tilts every prime.
  - `Λ* = 0.042887`.
  - `F(p) = 0.6468, 0.7324, 0.8214, 0.8661, 0.9108` at `p = 2, 3, 5, 7, 11`, and `F(p) ≈ 1 − 1.070/(p + 1)` for large
    `p`.
  - With `F = n/ψ(n)` kept fixed it is `0.043166`.

**Checks against finite `N`.**
- **Fixed vectors built from `c_opt`.** No re-optimisation at each `N`. The table gives quotient·`N/log N`.

  | vector | `2000` | `4000` | `8000` | `1.6·10⁴` | `3·10⁴` | fit `A + B/log N` | predicted |
  |---|---|---|---|---|---|---|---|
  | `w(n/N)/n` (`F = 1`) | `0.05795` | `0.05773` | `0.05762` | `0.05740` | `0.05736` | `0.05564` | `0.05552` |
  | `F·w/n`, `F = n/ψ(n)` | `0.04897` | `0.04852` | `0.04824` | `0.04787` | `0.04776` | `0.04424` | `0.04401` |
  | `(F − P(1 − w))/n` | `0.04825` | `0.04804` | `0.04753` | `0.04726` | `0.04703` | `0.04345` | `0.04317` |
  | `λ_N` | `0.04756` | `0.04722` | `0.04694` | `0.04667` | `0.04647` | `0.04341` | `Λ* = 0.04289` |

  - The three fixed vectors meet their predicted limits to `0.2`–`0.6%`.
  - `λ_N` extrapolates `1.2%` above `Λ*`. Adding a term `C/log²N` to the fit gives `0.04279`.
  - The likely cause is the slow drift of the local factors toward the tilted optimum.
    - For `p ≥ 11` the minimiser's local factors already match it: `f(11) = 0.911`–`0.913` against `0.9108`.
    - At `p ≤ 7` they are still near their `κ = 0` values: `f(2) = 0.668`–`0.674` against `0.6468`.
- **Re-optimised families.** With the best `c` at each `N`, among 16 B-splines:
  - The extrapolations are `0.04436` (separable) and `0.04347` (additive), against `K(ψ)·I_16 = 0.04423` and
    `(T + κ_16P²)/12D = 0.04334`.
  - The predicted separable/additive ratio is `1.020`; at finite `N` it is `1.013`–`1.017`.
  - For `F = 1` the re-optimised quotient stays at `0.0569` from `N = 2000` to `3·10⁴`. The fixed vector shows the limit
    is lower.
- **`θ`.** In the separable class the predicted optimum of `1 − θ/(p + 1)` is `θ = 1.035`, very flat, and the scan at
  `N = 4000` and `8000` has its minimum at `θ ≈ 1`. Far from the optimum the finite-`N` ratios are milder than
  predicted: `θ = 0` costs `1.17` against `1.26`.

**What this gives, and what it does not.**
- **The constant.** It is `(1/12)·(T + κP²)/D`, three pieces:
  - `1/12` is the zero density against the dual sum over `b`;
  - `T/D` is the arithmetic weight, `0.480` at its optimum;
  - `κ ≈ 0.096` is the price of silencing the boundary at every zero with a staircase.
- **The profile problem is of Nyman–Beurling type.** For a step function `c` the staircase `w(y) = Σ_k c(ky)` is a
  Nyman–Beurling function `−Σa_i{θ_i/y}`. Here the approximation of `1` is on `(1, ∞)` in `L²(dx)`, `c` must be
  continuous, and the minimum is positive.
- **What is not proved.** The reduction is heuristic: the dual-sum approximation and the diagonal mean value over the
  zeros. It gives the limit of the quotient for vectors of the form above. A lower bound for every vector needs more.

## The upper bound with the sharp constant: `λ_N ≤ (0.04294 + o(1))·log N/N` under RH (a proof on paper)

The previous section's reduction is heuristic for general vectors, but for one explicit vector it can be carried out
rigorously, and that vector gives an upper bound. The constant is `0.04294`, against the `67` of `BallUpperEta`, and
the infimum over the admissible class is `Λ* ≈ 0.0429`. The proof uses one Lean theorem, `BallLow.shell_bound`, and
standard analytic inputs: Mellin inversion, the functional equation with Stirling's formula, the convexity bound,
and Gonek's uniform version of Landau's formula. It is not formalised.

**Theorem.** Assume RH. Let:
- `e` be supported on `d ≤ D₀`, and `F = 1 ∗ e`, `P = Σ_d e(d)/d`, `S(a) = Σ_g e(ag)/g`;
- `T = Σ_a Π_{p | a}(1 − p⁻²)·S(a)²` and `D = Σ_n F(n)²/n² = ζ(2)Σ_{d,d'} e(d)e(d')/lcm(d, d')²`;
- `c ∈ C²[0, 1]`, with `c''` of bounded variation, `c(0) = −2`, `∫_0^1 c = 0`, `c(1) = c'(1) = c''(1) = 0`;
- `I[c] = ∫_0^∞ (1 − W(x))² dx`, with `W(x) = Σ_{1 ≤ k ≤ x} c(k/x)`.

Then `lim sup_{N→∞} λ_N·N/log N ≤ Λ(e, c) := (T + (I[c] − 1)·P²)/(12D)`.

**The admissible optimum** (`packing.py --solve`).
- `c` is a quintic spline on 192 intervals with `I[c] = 1.097632`.
- The best `e` on `d ≤ 2000` is the bottom of a generalized eigenproblem.
- Together they give `Λ = 0.042937`. Both minimisations converge to `Λ* ≈ 0.0429` as the classes grow:
  - `I`: `1.1112`, `1.1042`, `1.0996`, `1.0976` on 24 to 192 intervals;
  - `Λ`: `0.04308`, `0.04299`, `0.04296`, `0.04294` for `D₀ = 100` to `1000`.

**The test vector.**
- **Two profiles.** For `δ ∈ (0, ½)` take `η ∈ C^∞` with `η = 1` on `[0, 1 − δ]` and `η = 0` on `[1, ∞)`. Take
  `w(u) = Σ_{k ≤ 1/u} c(ku)` for `u ≤ 1` and `w = 0` beyond.
- **The vector.** `x_n = ((F(n) − P)·η(n/N) + P·w(n/N))/n`.
- **The claim.** `Q_N(x)/Σx_n² = (Λ_δ + o(1))·log N/N`, with `Λ_δ = (T(1 + J) + P²(I[c] − 1 − J))/(12D)` and
  `J = ∫_{1−δ}^1 (1 − η(y))² dy/y² ≤ 2δ`. Letting `δ → 0` gives the theorem.

**Step 0: the sum over zeros, and the norm.**
- **The sum over zeros.** Under RH, `Q_N(x) = Σ_ρ |V(ρ)|²/(¼ + γ²)` with `V(ρ) = Σ_n x_n n^ρ` (`BallRate.hasSum_form`).
  For real `x`, `V(ρ̄)` is the conjugate of `V(ρ)`, so it is enough to take `γ > 0`.
- **The norm.** `w(u) = 1 + O(u)` by Euler–Maclaurin, using `−c(0)/2 = 1` and `∫c = 0`. So `|x_n| ≪ 1/n`, and
  `x_n → F(n)/n` for each fixed `n`. Hence `Σ x_n² → D`.

**Step 1: every residue vanishes.**
- **Mellin form.** For a profile `E` put `S_E(ρ, X) = Σ_m E(m/X)m^{ρ−1} = (1/2πi)∫_{(2)} ζ(1 − ρ + z)Ê(z)X^z dz`. Then
  `V(ρ) = Σ_d e(d)d^{ρ−1}S_η(ρ, N/d) − P·S_η(ρ, N) + P·S_w(ρ, N)`.
- **The transforms.**
  - `ŵ(z) = ζ(z)ĉ(z)`.
  - `ĉ` has a simple pole at `0` with residue `c(0)`. Three integrations by parts give
    `|ĉ(−σ + iy)| ≪ (1 + |y|)^{−3}` for `0 < σ < 1`.
  - `η̂` has a simple pole at `0` with residue `1`, and decays faster than every power.
- **Move every contour to `Re z = −σ`, `½ < σ < 1`.** Three residues appear, each zero at a zero `ρ`:
  - at `z = ρ`: `N^ρ·(η̂(ρ)(Σ_d e(d)/d − P) + P·ζ(ρ)ĉ(ρ)) = 0`;
  - at `z = 0`: `ζ(1 − ρ)·(Σ_d e(d)d^{ρ−1} − P + P·ζ(0)c(0)) = 0`;
  - at `z = 1`: `P·N·ĉ(1)·ζ(2 − ρ) = 0`.
- **What is left.** `V(ρ)` is the sum of the integrals on `Re z = −σ`.

**Step 2: the low zeros, `γ ≤ √N`.**
- **The bound.** On `Re z = −σ`:
  - `|ζ(1 − ρ + z)| ≪ (2 + |y − γ|)^σ log(2 + |y − γ|)`, by the functional equation and convexity;
  - `|ζ(z)| ≪ (2 + |y|)^{½+σ}`;
  - `|Σ_d e(d)d^{ρ−1−z}| ≤ Σ_d |e(d)|d^{σ−½}`.
  So `|V(ρ)| ≪ N^{−σ}(2 + γ)^σ log(2 + γ)`.
- **The sum.** `σ = 0.7` keeps the integral over `y` convergent. The zeros with `γ ≤ √N` then give
  `≪ N^{−6/5}log³N`.

**Step 3: the dual sum, for `√N ≤ γ ≤ N/ε`.**
- **Expand `ζ(ρ − z)`.** On `Re z = −σ`, `ζ(1 − ρ + z) = χ(1 − ρ + z)ζ(ρ − z)`, and `ζ(ρ − z) = Σ_k k^{z−ρ}`
  converges absolutely.
- **Stirling.** For `|Im z| ≤ √γ`, `χ(1 − ρ + z) = χ(1 − ρ)(γ/2π)^{−z}(1 + O((1 + |z|²)/γ))`. Beyond that,
  `|χ(1 − ρ + z)| ≪ (2 + |Im z − γ|)^σ`.
- **Mellin inversion.** The pole at `0` is crossed, and it turns the `k`-th term into
  `−χ(1 − ρ)k^{−ρ}φ_E(γ/(2πkX))`, where `φ_E = E(0) − E` and `E = 0` beyond `1`.
- **The error.** It is `≪ k^{−½}(γ/kX)^σ·γ^{−2/5}` over `k`. Summed over `k` and over `d ≤ D₀`, with `X ≥ N/D₀`:
  `V(ρ) = −χ(1 − ρ)·D(γ) + O_{ε, D₀}(N^{−1/5})`. Here `τ = γ/2πN` and
  `D(γ) = Σ_d e(d)d^{−½+iγ}Σ_k k^{−½−iγ}φ_η(τd/k) − P·Σ_k k^{−½−iγ}(φ_η − φ_w)(τ/k)`.
- **Absolute convergence.** `φ_η(y) = 0` for `y ≤ 1 − δ`. And `|φ_w(y)| ≪ y`, since `w(u) = 1 + O(u)`. So the sums over
  `k` converge absolutely, uniformly for `τ ≤ 1/ε`.

**Step 4: the mean square over the zeros.**
- **Ratios.** Group `D(γ) = Σ_{(a,b)=1} A(a/b; τ)(a/b)^{iγ}`, with `A(a/b; τ) = (ab)^{−½}H_a(τa/b)`. Here
  `H_1 = P·φ_w`, and `H_a = S(a)φ_η` for `a ≥ 2` (zero for `a > D₀`). Put `Φ(τ) = Σ_{(a,b)=1} A(a/b; τ)²`.
- **The claim.** Over the zeros with `√N ≤ γ ≤ N/ε`,
  `Σ|D(γ)|²/(¼ + γ²) = (log N/N)·(1/4π²)·∫_{1/2π√N}^{1/2πε} Φ(τ)τ^{−2}dτ + o(log N/N)`.
- **Proof, in four steps.**
  - **Truncate.** Keep `b ≤ K = N^{1/40}`. The rest is `≪_{ε,D₀} K^{−½}` pointwise.
  - **Freeze the coefficients.** Cut the range into intervals of length `H = N^{3/4}` and freeze `τ` in `A` on each:
    `|∂_τ A| ≪ D₀`, so the error is `≪ D₀H/N`.
  - **Apply Gonek's uniform Landau formula** to each ratio `x = r/r' ≠ 1`, whose numerator and denominator are
    `≤ D₀K`. It gives `Σ_{t<γ≤t+H} x^{iγ} = −(H/2π)Λ(x)x^{−½} + O((D₀K)²log²N)`, with `Λ(x) = 0` unless `x^{±1}` is
    a prime power. (S. M. Gonek, *An explicit formula of Landau and its applications to the theory of the
    zeta-function*, Contemp. Math. 143 (1993).)
  - **Collect the terms.**
    - The diagonal gives `(H/2π)log(t/2π)Φ`.
    - The Landau terms are `O(Φ·(1 + log(1/ε))/log N)` relative to it: for fixed `r`, only `q ≤ D₀K` occur, and
      `Σ_q Λ(q)/q·φ(τ/qk)` stays bounded.
    - Weighted by `1/t² ≤ 1/N`, the error terms add up to `≪ D₀⁴ N^{1/10 − 5/4}log²N = o(log N/N)`.
- **The integral.** Summing `(H/2π)log(t/2π)Φ/t²` over the intervals gives the integral, since `log(t/2π) = log N +
  log τ`.

**Step 5: the high zeros, `γ > N/ε`.**
- **The shell bound.** `BallLow.shell_bound` on the shells `2^k·8N < |γ| ≤ 2^{k+1}·8N` with `2^k ≥ 1/8ε` gives
  `≪ ε·log(1/ε)·(S2 + G)/N`, plus a term `≪ ε²·log N/N`. Here `S2 = Σ x_n²n` and `G` is Landau's slack at
  `c_n = x_n√n`.
- **Both are `≪ log N`.**
  - `S2 ≪ Σ 1/n`.
  - The vertex part of `G` has bounded weights `κ_j`, by Mertens.
  - Its edges `(Λ(n)/n)(f(j) − f(jn))²/j`, with `f(m) = m·x_m`, are of three kinds:
    - the edges of `F` occur only at primes `p ≤ D₀`;
    - those of `η` only for `jn ∈ ((1 − δ)N, N]`;
    - those of `w` are `≪ (jn/N)²`.

    Each kind sums to `O(log N)`.

**Step 6: assembly.**
- **The `τ`-integral factors.** Substitute `y = τa/b`:
  `∫_0^∞ Φ(τ)τ^{−2}dτ = Σ_{(a,b)=1} b^{−2}∫_0^∞ H_a(y)²y^{−2}dy = ζ(2)Σ_a Π_{p | a}(1 − p⁻²)∫H_a²/y²`.
- **The two integrals.** `∫H_1²/y² = P²·I[c]`, because `φ_w = 1 − w` on `[0, 1]` and `1` beyond. For `a ≥ 2`,
  `∫H_a²/y² = S(a)²(1 + J)`.
- **The small `τ`.** Below `τ = (1 − δ)/D₀` only `a = 1` survives, and `Φ(τ) ≪ τ²`. So `∫_0^ε Φτ^{−2} ≪ ε`.
- **Collect.** Steps 2 to 5, with `Σ x_n² → D` and `ζ(2)/2π² = 1/12`, give
  `Q_N(x)/Σ x_n² = (Λ_δ + O(ε log(1/ε)) + o(1))·log N/N`. Let `N → ∞`, then `ε → 0`, then `δ → 0`. ∎

The proof gives an asymptotic, not only an upper bound: the quotient of this vector is `(Λ + o(1))·log N/N`. For
the fixed vectors of the previous section the computed quotients approach their predicted limits from above, as an
`O(1/log N)` correction would.

**What it says about `λ_N`.**
- **The constant.** If the computed `λ_N` keeps falling like `0.0316/log N`, its limit is at most `0.04294`. The fit
  `a·log N + b` over `N ≤ 3·10⁴` gives `0.0434`. A curvature term brings that to `0.0428`, within the theorem.
- **Against `BallUpperEta`.** That theorem has `67(1 + log N)/N`. Its alternating vector meets the low zeros through
  `η = (1 − 2^{1−s})ζ`, while the vector here meets every residue exactly.

## The inverse theorem on the arithmetic class, and the picket fence (proofs on paper)

The proof of the previous section works for the whole class of vectors the earlier sections found, and on that class
it settles the other two open steps. Theorem C below then drops the class at the picket fence, with a margin that
falls like a power of `N`, and Theorems D′ and E pin it down: `λ^pf_N ≍ N^{−3/5}log N`.

**The class.** `n·x_n = Σ_{d | n, d ≤ D₀} E_d(n/N)`, with `D₀` fixed, and fixed profiles `E_d` on `[0, 1]`. Each `E_d`
is `C²`, with `E_d''` of bounded variation and `E_d(1) = E_d'(1) = E_d''(1) = 0`. Write `e(d) = E_d(0)`, `F = 1 ∗ e`,
`G = Σ_d E_d/d` and `M_e(s) = Σ_d e(d)d^{−s}`.

The vectors of the theorem above belong to it. So does the minimiser of `Q_N`, to within `1.2`–`1.5%` in the Rayleigh
quotient for `N ≤ 3·10⁴`. Since `λ₂ ≈ 4λ₁`, that means within about `1.6%` in the norm of `Q_N`.

**Theorem A (the inverse theorem on the class; RH).** Let `x` be in the class, with `e ≠ 0`.
1. **Loud.** If `Ĝ(ρ) ≠ 0` at some zero `ρ`, then `Q_N(x)/Σx_n² ≥ (|Ĝ(ρ)|²/((¼ + γ²)D) + o(1))·N`.
2. **Quiet.** If `Ĝ` vanishes at every zero, then `Q_N(x)/Σx_n² = (Λ(E) + o(1))·log N/N`. Here
   `Λ(E) = (1/12D)·Σ_a Π_{p | a}(1 − p⁻²)∫_0^∞ H_a(y)² dy/y²`, with `H_a = Σ_g (E_{ag}(0) − E_{ag}(·))/g`, and
   `Λ(E) ≥ K_min = 0.040021`.
3. **The spread.** In both cases `A = Σx_n²n/Σx_n² = (C_F/D + o(1))·log N`, where `C_F > 0` is the mean of `F²`.

So a vector of the class that is quiet at the zeros, `Q_N(x) = O(log N/N)·Σx_n²`, carries `ζ`: `Ĝ` vanishes at every
zero. Its spread is `≍ log N`, and its quotient is at least `(0.0400 + o(1))·log N/N`.

*Proof.*
1. **The single zero.** The contour shift of Step 1 above gives
   `V(ρ) = ζ(1 − ρ)M_e(1 − ρ) + N^ρĜ(ρ) + O(N^{−σ}(2 + |γ|)^σ log)`. The first term vanishes at a zero. Then
   `Q_N(x) ≥ |V(ρ)|²/(¼ + γ²)`, and `Σx_n² → D`.
2. **The asymptotic.** Steps 1 to 5 above use only that every residue vanishes and that the profiles are smooth.
   Step 6 then gives the stated asymptotic, with the coefficients `H_a` of the dual sum.
   - **First lower bound.** On `(1, ∞)` every `E` vanishes, so `H_a = S(a)`. Hence
     `Σ_a ω_a ∫H_a²/y² ≥ Σ_a ω_a S(a)² = T`.
   - **Second lower bound.** `T` and `D` are tensor products, over the primes, of the local forms `T_p` and `D_p` in
     the local factors. So the smallest value of `T/D` is the product of the local minima `μ_p`, each below
     `1 − p⁻²`. That gives `T/(12D) ≥ (1/12)Π_p μ_p = K_min`, the value of `--solve` at `κ = 0`.
3. **The spread.** `f(n) = Σ_{d | n}E_d(n/N) = F(n) + O(n/N)`, and `F` is periodic modulo `lcm(1, …, D₀)`. ∎

**Theorem B (the picket fence on the class; no hypothesis).** Let `Φ(γ_k) = k − ½` be the fence, and
`Q^pf_N(x) = Σ_k 2|V_x(½ + iγ_k)|²/(¼ + γ_k²)`. For `x` in the class with `e ≠ 0`:
- `lim inf_{N→∞} Q^pf_N(x)/Σx_n² ≥ c(D₀)`, with `c(D₀) = min_e m(e)/D(e)` and
  `m(e) = Σ_k 2|ζ(½ + iγ_k)M_e(½ − iγ_k)|²/(¼ + γ_k²)`;
- if `Ĝ(½ + iγ_k) ≠ 0` for some `k`, then `Q^pf_N(x)/Σx_n²` grows like `N`.

  | `D₀` | `1` | `2` | `4` | `8` | `16` | `32` | `64` |
  |---|---|---|---|---|---|---|---|
  | `c(D₀) ≥`, first 3000 points | `0.0350` | `0.0348` | `0.0306` | `0.0261` | `0.0242` | `0.0207` | `0.0138` |
  | `c(D₀) ≥`, first 12000 points | `0.0365` | `0.0362` | `0.0321` | `0.0278` | `0.0260` | `0.0228` | `0.0159` |

  The first 3000 fence points reach height `3533`, the first 12000 height `11566`. Each row is a lower bound, because
  every term of `m` is `≥ 0`, so more points can only raise it.

*Proof.* At a fixed fence point the same contour shift gives
`V(½ + iγ_k) = ζ(½ − iγ_k)M_e(½ − iγ_k) + N^{½+iγ_k}Ĝ(½ + iγ_k) + O(N^{−σ})`, uniformly for `γ_k` in a bounded set.
- **The residues no longer vanish.** `ζ(½ − iγ_k) ≠ 0` at a point of the fence that is not a zero.
- **A boundary term that survives**, `Ĝ(½ + iγ_k) ≠ 0`, makes that one term of `Q^pf` grow like `N`.
- **Otherwise, the limit.** For every fixed `k`, `|V(½ + iγ_k)|² → |ζ(½ − iγ_k)M_e(½ − iγ_k)|²` as `N → ∞`.
  Every term of `Q^pf` is `≥ 0`, so for every `K`,
  `Q^pf_N(x) ≥ Σ_{k ≤ K} 2|V(½ + iγ_k)|²/(¼ + γ_k²) → m_K(e) = Σ_{k ≤ K} 2|ζ(½ + iγ_k)M_e(½ − iγ_k)|²/(¼ + γ_k²)`.
  - Hence `lim inf_N Q^pf_N(x) ≥ m_K(e)` for every `K`, and `≥ m(e)` as `K → ∞`. This is Fatou's lemma for a series
    of nonnegative terms.
  - Each `K` involves finitely many points, so no uniformity in `k` is needed.
  - Again `Σx_n² → D(e)`.
- **The margin.** `m_K` and `D` are quadratic forms in `e ∈ ℝ^{D₀}`, and `D` is positive definite.
  - So `c_K(D₀) = min_e m_K(e)/D(e)` is the bottom of a pencil of size `D₀`. It increases with `K`, and
    `c(D₀) ≥ c_K(D₀)`.
  - The table gives `c_K` at `K = 3000` and `12000` (`--fence-class K`).
  - These are floating-point eigenvalues of pencils of size at most `64`, with `ζ` from mpmath at 15 digits. The
    margins are far above any rounding error. ∎

**Theorem C (the picket fence for every vector; no hypothesis).** There are absolute constants `c > 0` and `N₀` such
that `Q^pf_N(x) ≥ c·N^{−2/3}log N·Σx_n²` for every real `x` on `[1, N]` and every `N ≥ N₀`. So
`λ^pf_N ≫ N^{−2/3}log N` for every vector, not only on the class. Under RH `λ_N ≤ 67(1 + log N)/N` (`BallUpper`), so
the fence's smallest eigenvalue exceeds the zeros' by a factor `≫ N^{1/3}`. Theorem E below raises the exponent to
`−3/5`, and the factor to `≫ N^{2/5}`.

*Setting.* Put `b_n = x_n√n`, `B(t) = Σ_{n≤N} b_n n^{it}`, `t_k = Φ⁻¹(k − ½)` and `L(t) = log(t/2π)`, so `Φ' = L/2π`.
Fix `η ∈ C_c^∞((½, 2))` with `η ≥ 0` and `Σ_{j∈ℤ} η(t/2^j) = 1` on `t > 0`, and put
`h_j(t) = η(t/2^j)·2/(¼ + t²)`. Then `Q^pf_N(x) = Σ_j E_j`, where
`E_j = Σ_k h_j(t_k)|B(t_k)|² = Σ_{m,n} b_m b_n F_j(m/n) ≥ 0` and `F_j(r) = Σ_k h_j(t_k)r^{it_k}`. Write `T = 2^j`.
- **Poisson summation on the fence.** `Φ` maps `(2π, ∞)` onto `(−1/8, ∞)`. For `f ∈ C_c^∞((2π, ∞))`, Poisson
  summation for `f∘Φ⁻¹` at the half-integers gives `Σ_k f(t_k) = Σ_{ℓ∈ℤ}(−1)^ℓ ∫ f(t)e^{−2πiℓΦ(t)}Φ'(t)dt`. So
  `F_j(r) = Σ_ℓ (−1)^ℓ I_ℓ(r)`, with `I_ℓ(r) = ∫ h_jΦ' e^{iψ_ℓ}`, `ψ_ℓ(t) = t log r − 2πℓΦ(t)`,
  `ψ_ℓ' = log r − ℓL(t)` and `ψ_ℓ'' = −ℓ/t`. The term `ℓ` is the `ℓ`-th alias: it couples `m` and `n` when
  `log(m/n) = ℓL(t)`.
- **Size.** `H_j = F_j(1) = (c_η + o(1))·L(T)/(πT)`, with `c_η = ∫η(u)u^{−2}du`; the terms `ℓ ≠ 0` at `r = 1` are
  non-stationary.
- **Non-stationary terms.** If `|ψ_ℓ'| ≥ λ` on `[T/2, 2T]`, then `k` integrations by parts give
  `|I_ℓ(r)| ≤ C_k H_j (Tλ)^{−k}(1 + |ℓ|/λ)^k`. For `ℓ = 0` this is `C_k H_j (T|log r|)^{−k}`.
- **The stationary term.** For `ℓ = 1` the phase is stationary at `t* = 2πr`, with
  `ψ_1(t*) − π/4 = 2πr − 7π/4 − π/4 ≡ 2πr (mod 2π)`. So, uniformly in `r`,
  `I_1(r) = a_j(r)e^{2πir} + O(H_j T^{−3/2})`. Here `a_j(r) = h_j(2πr)Φ'(2πr)·2π√r ≥ 0`, and `a_j(r) ≤ C H_j/√T`.
  At `r = m/n` the phase `e^{2πim/n}` depends on `m mod n`.

Write `M_n = max(n, N/n)` and `W(T) = ∫_T^∞ 2Φ'(t)dt/(¼ + t²) = (L(T) + 1)/(πT) + O(T^{−3})`.

**Lemma F (free sampling).** For `A ≥ A₀` and `N ≥ N₀(A)`, `Q^pf_N(x) ≥ ½Σ_n b_n²·W(16πA·M_n)`.

Above height `2πM_n` the component `n` has no alias in `[1, N]`: its partners `nt/2π` and `2πn/t` both lie outside.
The lemma says that all such components are sampled at once, and none of them can be cancelled.

*Proof.* Fix `j` and let `Fr_j = {n : M_n ≤ T/(4πA)}`.
- **No alias is stationary.** Take `n ∈ Fr_j`, any `m ≤ N`, `ℓ ≠ 0` and `t ∈ [T/2, 2T]`. Then
  `|log(m/n) − ℓL(t)| ≥ log A`, because `N/n` and `n` are at most `T/(4πA)` while `L(t) ≥ log(T/4π)`. So the terms
  `ℓ ≠ 0` of `F_j(m/n)` sum to `O(H_j T^{−4})`.
- **The test sequences `u_n(t_k) = n^{it_k}`, `n ∈ Fr_j`, are almost orthogonal** in `ℓ²(h_j)`. For `n ≠ n'` in
  `Fr_j`, `T|log(n'/n)| ≥ 4πA|n − n'|`. So the Gram matrix `(F_j(n'/n))` has norm at most `H_j(1 + ε_A)`, with
  `ε_A = C_k(4πA)^{−k} + O(NT^{−4}) → 0`.
- **Each inner product recovers its coefficient.** `⟨B, u_n⟩ = Σ_m b_m F_j(m/n) = b_n H_j + e_n`. Here `e_n` collects
  the `ℓ = 0` terms of the neighbours `m ∈ [n/2, 2n]`, with `|F_j(m/n)| ≤ C_k H_j (2πA|m − n|)^{−k}`, and terms
  `O(H_j T^{−4})`. By Young's inequality,
  `Σ_{n∈Fr_j}|e_n|² ≤ ε'_A H_j² Σ_{m∈Fr_j*} b_m² + O(H_j² N²T^{−8}Σb²)`, with `Fr_j* = ∪_{n∈Fr_j}[n/2, 2n]` and
  `ε'_A → 0`.

Bessel's inequality for this family then gives
`E_j ≥ (1 + ε_A)^{−1}H_j[(1 − δ)Σ_{Fr_j} b_n² − δ^{−1}ε'_A Σ_{Fr_j*} b_m²] − O(H_j N^{−2}Σb²)`.
Now sum over `j`:
- `n ∈ Fr_j` exactly when `2^j ≥ 4πA·M_n`; `n ∈ Fr_j*` only if `2^j ≥ 2πA·M_n`, one dyadic level lower. So
  `Σ_{j: n∈Fr_j*} H_j ≤ 4Σ_{j: n∈Fr_j} H_j`.
- `Σ_{j: n∈Fr_j} H_j ≥ W(16πA·M_n)`, because `Σ_{j ≥ j₀} η(t/2^j) = 1` for `t ≥ 2^{j₀}`.
- The remainder `O(N^{−2}Σb²)` lies far below `Σb_n²W(16πAN) ≫ (log N/N)Σb²`.

Take `δ = ¼` and `A` large enough that the bracket is at least `½`. ∎

**Lemma C (the chain).** For `A ≥ A₀`, `K = ⌊N^{1/6}⌋` and `N ≥ N₀(A)`,
`Q^pf_N(x) ≥ c(A)·(log N/√N)·Σ_{n ≤ K} x_n²/n`.

At a height `t ∈ [2π√N, 2πN/n]` the fence can silence `x_n` only through its partners `m ≈ nt/2π`. Higher up those
partners are free, and Lemma F charges them there. The charge falls like `1/n`, because the partners of `n` sit `n`
times higher.

*Proof.* Take the window `j` with `T = 2^j ∈ [8πA√N, 16πA√N]`, `H = H_j`, and the test sequences `u_n` for `n ≤ K`.
- **The family is almost orthogonal.** Distinct `n, n' ≤ K` have `T|log(n'/n)| ≥ T/K ≥ N^{1/3}`. Every `ℓ ≠ 0` term
  is non-stationary, since `|ℓ|L(t) − log K ≥ ½L(T/2)`. So the Gram norm is `H(1 + o(1))`.
- **Only the partners alias.** `⟨B, u_n⟩ = b_n H + Σ_{m∈P_n} b_m F(m/n) + e_n`, with the partners
  `P_n = {m : m/n ∈ [T/8π, 2T/π]}`. Every other `m` is non-stationary in every `ℓ`: on the window
  `|log(m/n) − L(t)| ≥ log 2`. So `Σ_n|e_n|² ≤ H²N^{−2}Σb²`.
- **The partners are free higher up.** Every partner has `A√N ≤ m ≤ 32AK√N ≤ N^{2/3 + o(1)}`. So `M_m = m`, and
  Lemma F charges it `Ω_m = W(16πA·m)`.

Let `R` be the matrix with entries `F(m/n)/(n√Ω_m)`, for `n ≤ K` and `m` a partner. By the triangle inequality,
`H(Σ_{n≤K} b_n²/n²)^{1/2} ≤ (H(1 + o(1))E_j)^{1/2} + ‖R‖·(Σ_m b_m²Ω_m)^{1/2} + O(HN^{−1}(Σb²)^{1/2})`.
The first term is at most `(2HQ)^{1/2}`, and by Lemma F the second is at most `‖R‖(2Q)^{1/2}`. Bound `‖R‖²` by
Schur's test on `RR*`:
- **The diagonal.** `n` has at most `2nT/π` partners, each with `|F(m/n)|² ≤ CH²/T` and `1/Ω_m ≤ CAnT/L(T)`. So
  `(RR*)_{nn} ≤ C·A·H·(TH/L(T)) ≤ C'A·H`, the same for every `n`: the weight `1/n²` pays for the `n`-fold number of
  partners and their `n`-fold height.
- **Off the diagonal.** `(RR*)_{nn'} = (nn')^{−1}Σ_m g(m)e^{2πimθ}` plus stationary-phase errors. Here
  `θ = 1/n − 1/n'`, `g = a(m/n)a(m/n')/Ω_m` is smooth, and `‖θ‖ ≥ 1/(nn')`. Summation by parts gives
  `|(RR*)_{nn'}| ≤ CA·H·min(n, n')/T`, and the errors are smaller. So `Σ_{n'≠n}|(RR*)_{nn'}| ≤ CA·H·K²/T = o(H)`.

Hence `‖R‖² ≤ C₁A·H` and `HΣ_{n≤K} b_n²/n² ≤ 2(1 + √(C₁A))²Q(1 + o(1))`. Finally `b_n²/n² = x_n²/n`, and
`H ≥ c_η L(T)/(2πT) ≥ c_η log N/(70π²A√N)`. ∎

*Proof of Theorem C.* Normalise `Σx_n² = 1`, and fix `A = A₀`.
- If `Σ_{n≤K} x_n² ≥ ½`, Lemma C gives `Q ≥ c(A)(log N/√N)/(2K) ≫ N^{−2/3}log N`.
- Otherwise `Σ_{n>K} x_n² ≥ ½`, and Lemma F applies term by term.
  - For `K < n ≤ √N`, `b_n²W(16πAN/n) = n²x_n²(L(16πAN/n) + 1)/(16π²AN) ≥ x_n²K²log N/(32π²AN) ≫ x_n²N^{−2/3}log N`.
  - For `n > √N`, `b_n²W(16πAn) ≥ x_n² log N/(32π²A)`. ∎

**What the proof loses.** Lemma C has `x_n²/n` where `x_n²` would give `N^{−1/2}`. It charges the partners of `x_n`
only what they pay where they are free, and those partners are free `n` times higher. The free cost `n²log N/N` of
`x_n` itself, from Lemma F, takes over at `n ≍ N^{1/6}`; that is the exponent `−2/3`. How fast the cost of
cancelling `x_n` really falls with `n` decides the exponent. A fall like `1/n` gives Theorem C's `−2/3`; no fall gives
the `−1/2` of the fence's minimiser at `N ≤ 12800`. Lemma E below moves the window down to `≍ A√(N/n)`, where the
partners are free only `√n` times higher. The fall is then `1/√n`, and the exponent `−3/5` (Theorem E).

**The constrained minima** (`--fence-cap`, and `--fence-cap 12800` for the last rows). Put
`q_n = min{Q^pf_N(x) : x_n = 1} = 1/(G⁻¹)_{nn}`, for `G` the fence's Gram matrix. `q_n` splits into three parts:
- **free:** `n·W(2πM_n)`, the energy of `x_n = 1` where it has no alias. This is Lemma F's charge without the margin
  `16A`.
- **below:** the cost paid below that height. Divided by `log₂(√N/n)`, the number of dyadic windows between `2π√N`
  and `2πN/n`, it gives a cost per window.
- **the excess:** the rest, which is the partners' own energy above `2πN/n`.

| `n` | `1` | `2` | `3` | `4` | `5` | `8` | `16` | `32` |
|---|---|---|---|---|---|---|---|---|
| `q_n√N`, `N = 400` | `0.119` | `0.199` | `0.450` | `0.541` | `0.641` | `1.053` | `2.903` | `7.956` |
| `q_n√N`, `N = 1600` | `0.124` | `0.195` | `0.476` | `0.526` | `0.585` | `0.830` | `2.056` | `6.497` |
| `q_n√N`, `N = 6400` | `0.132` | `0.198` | `0.510` | `0.534` | `0.559` | `0.684` | `1.417` | `4.286` |
| `q_n√N`, `N = 12800` | `0.137` | `0.202` | `0.531` | `0.545` | `0.558` | `0.638` | `1.182` | `3.428` |
| free·`√N`, `N = 12800` | `0.005` | `0.018` | `0.038` | `0.065` | `0.099` | `0.240` | `0.881` | `3.206` |
| below·`√N`, `N = 12800` | `0.125` | `0.162` | `0.449` | `0.405` | `0.357` | `0.238` | `0.077` | `0.017` |
| per window, `N = 6400` | `0.019` | `0.028` | `0.086` | `0.083` | `0.077` | `0.057` | `0.017` | `0.020` |
| per window, `N = 12800` | `0.018` | `0.028` | `0.086` | `0.084` | `0.079` | `0.062` | `0.027` | `0.010` |
| tail amplitude `A_n`, `N = 12800` | `0.53` | `0.78` | `1.29` | `1.55` | `1.68` | `1.85` | `1.93` | `1.92` |

- **The shape.** For `m ≥ 2√N` the constrained minimiser has `m·x_m ≈ A_n cos(2πm/n)`: the partners carry the phase
  `e^{2πim/n}` of the stationary term, in its real form. Full cancellation needs `A_n = 1` for `n ≤ 2`, where that
  phase is real, and `A_n = 2` for `n ≥ 3`, where the cosine splits into two conjugate twists. So `x_1` is cancelled
  by about half, and `x_n` by `92`–`95%` for `n ≥ 8`.
- **The free part** is Lemma F's lower bound, and the minimisers meet it.
- **The excess** is about the partners' mass `(A_n²/2)log(√N/n)` times `W(2πN/n)`. At `N = 6400` that gives `0.075`,
  `0.151` and `0.207` for `n = 4, 8, 16`, against `0.089`, `0.183` and `0.243` measured. Its ratio to the free part
  falls like `log N/n`.
- **The cost per window** is `0.018`–`0.019` for `n = 1` and about `0.028` for `n = 2`, at every `N`. At `N = 12800`
  it falls from `0.086` at `n = 3` to `0.047` at `n = 11`, about as `n^{−0.45}` between the two. That is slower than
  the `1/n` of Lemma C. For fixed `n ≥ 8` it is still rising with `N`, so the slope in `n` has not settled.

**Where the cost is paid** (`--fence-windows 12800`: window by window, in units of `1/√N`). Here `T₀ = 2π√N`, and `*` marks the
window that holds the free height `2πN/n`.

| `n` | `[T₀/4, T₀/2)` | `[T₀/2, T₀)` | `[T₀, 2T₀)` | `[2T₀, 4T₀)` | `[4T₀, 8T₀)` | `[8T₀, 16T₀)` | `[16T₀, 32T₀)` |
|---|---|---|---|---|---|---|---|
| `1` | `0.0000` | `0.0004` | `0.0264` | `0.0277` | `0.0245` | `0.0188` | `0.0133` |
| `4` | `0.0009` | `0.0531` | `0.0622` | `0.0950` | `0.0859` | `0.0672` | `0.0538*` |
| `8` | `0.0086` | `0.0109` | `0.0059` | `0.0608` | `0.0872` | `0.1012*` | `0.1558` |
| `16` | `0.0034` | `0.0019` | `0.0011` | `0.0044` | `0.1640*` | `0.4299` | `0.2530` |
| `32` | `0.0006` | `0.0004` | `0.0005` | `0.3197*` | `1.3366` | `0.7750` | `0.4440` |

- **`n = 1`** is silent below `T₀`, then pays about `0.025` per window. That is a quarter of `x₁`'s uncancelled energy
  in `[T₀, 2T₀)`, and nearly all of it by `[8T₀, 16T₀)`.
- **`n ≥ 16`** pays at most `0.004` per window below its free height, and those entries are the same at `N = 6400` to
  the digits shown.
- **`n = 4` and `8`** pay `0.06`–`0.10` per window from about `(n − 1)T₀/2` up to the free height. That is where the
  conjugate images (`q ≡ −1 mod n`) of the partners used near `T₀` land, at `n − 1` times their height. For `n = 16`
  and `32` that height lies above the free height, so no image shows below it.
- **So the asymptotic regime for a centre `n` needs `N ≫ n⁴`,** with the images below the free height. The costs per
  window above, and the slope `n^{−0.45}`, are pre-asymptotic for `n ≥ 8`. Counting the images in that regime gives
  about `H(nT₀)√N ≍ log N/n` in all, the dependence on `n` of Lemma C. Counted alone, the images would favour
  `α = 1`. With the cost of silencing below the partners' start included, the count in the next paragraph gives
  `α = ½`. Either way `N^{−1/2}` would fail beyond some `N` near `10⁹`–`10¹⁰`, and neither is proved.

**The partners are a functional equation** (`packing.py --fence-twist`, `--fence-two`; numerics, with heuristic counts).
- **The fence is the set of anti-Gram points.** For the Riemann–Siegel theta function Stirling gives
  `θ(t) = (t/2)log(t/2πe) − π/8 + 1/(48t) + O(t^{−3})`, so `πΦ(t) = θ(t) + π − 1/(48t) + O(t^{−3})`. Hence
  `θ(t_k) = (k − 3/2)π + 1/(48t_k) + O(t_k^{−3})` and `χ(½ + it_k) = e^{−2iθ(t_k)} = −1 + O(1/t_k)`: on the fence
  `ζ(½ + it)` is purely imaginary, up to `O(1/t)`. mpmath gives the `1/(48t_k)` to four digits for `k = 1` to `10⁵`.
- **So the first alias is the functional equation of the periodic zeta function.** The phase `e^{2πim/n}` of the
  stationary term is the additive character of `F(a, s) = Σ_m e(am)m^{−s}`. In its approximate functional equation
  the factor `(2π)^{−½−it}Γ(½ + it)e^{−πi/4}e^{πt/2}` is `−1 + O(1/t)` on the fence. For the partners
  `p_m = 2cos(2πm/n)f(m)/m` that gives, at the fence points,
  `B_p(t_k) ≈ −√n·n^{it_k}f(nt_k/2π) − Σ_{k′≥1}f(nt_k/(2π(nk′+1)))·((nk′+1)/n)^{−½−it_k}
  − Σ_{k′≥0}f(nt_k/(2π(nk′+n−1)))·((nk′+n−1)/n)^{−½−it_k}`.
  The first sum holds the Hurwitz images, the second the conjugate images (`q ≡ −1 mod n`) of the window table.
- **So `δ_n + p` is silent from `2πX/n` until the first conjugate image switches on.** With `f` rising on `[X/2, X]`
  and falling on `[N/2, N]`, and `X = n√N`, that is from `T₀` to about `(n − 1)T₀`, the conjugate image's weight
  rising from `(n − 1)T₀/2`. At `N = 6400`, window by window (cost·`√N`, with `δ_n` alone in brackets):

  | `n` | `[T₀/2, T₀)` | `[T₀, 2T₀)` | `[2T₀, 4T₀)` | `[4T₀, 8T₀)` |
  |---|---|---|---|---|
  | `4` | `0.446` (`0.813`) | `0.0002` (`0.476`) | `0.066` (`0.273`) | `0.093` (`0.154`) |
  | `6` | `0.668` (`1.219`) | `0.0000` (`0.714`) | `0.0036` (`0.409`) | `0.059` (`0.231`) |
  | `8` | `0.891` (`1.626`) | `0.0000` (`0.953`) | `0.0000` (`0.545`) | `0.038` (`0.308`) |

  Below `T₀/2`, where `f(nt/2π) = 0`, `δ_n` is left as it is.
- **The images cost about `log N/(6n√N)` in all** (heuristic count). The image `(nk′ ± 1)/n` has `|·|² = n/(nk′ ± 1)`
  and switches on near `(nk′ ± 1)T₀/2`, where the remaining weight is `W ≈ log N/(2π²(nk′ ± 1)√N)`. Each family sums
  to `(π²/6)·log N/(2π²n√N)`. For partners started at `X = n√N` that is Lemma C's `1/n`, concentrated near the
  onsets. But starting there leaves `x_n` to be silenced below `T₀` by other means, and that costs more (the next
  bullets).
- **Below the partners' start the large components do the silencing.** In the constrained minimiser at `N = 6400` and
  `n = 8`, `m·x_m ≈ 1.85·cos(2πm/8)` on `m ≥ 256`, with `R²` from `0.949` to `0.996` in octaves. It ramps up over
  `[128, 256)` and has rms below `0.06` on `m < 128`. At the lowest fence points the large components cancel the
  centre, through the fence's higher aliases rather than the first. At `t = 14.5` those above `1024` give
  `−1.128 + 2.612i` against the centre's `0.973 − 2.656i`; by `t ≈ 70` it is those in `[256, 1024)`.
- **That is interpolation on a band, and it costs about `nH³/N²`.** To silence `x_n` at the fence points below `H`,
  the frequencies `log m` must cover a band at least the local Nyquist width `L(H)`, so `m ∈ [2πN/H, N]`.
  - For `H < T₀/√s`, the band `[2πN/(sH), N]` has no stationary aliases at those points. Its Gram matrix is that of
    exponentials on an interval longer than `2π` over their least gap, so Ingham's inequality bounds it below.
  - The least-norm interpolant is then quiet from `H` up to about `4π²N/(sH)`. Above that it pays its components'
    free energy, about `s²nH³log N/(N²L(H))` up to constants. That is the least-norm interpolant's price: Theorem D′
    silences the same points with a chirp near the top of `[1, N]` for almost nothing.
- **So the two mechanisms balance at `H ≍ √(N/n)`, and `α = ½`.** Twisted partners started at `X = nH/2π` cost about
  `log N/(nH)` in images.
  - The two costs balance at `H ≍ √(N/n)`, where each is about `(log N)^{3/4}/(√n√N)`: `α = ½` in the notation below,
    not `α = 1`.
  - At `N = 12800` the cost below the free height is `0.449`, `0.405` and `0.357` (times `1/√N`) at `n = 3, 4, 5`. That
    is `K·(log N)^{3/4}/√n` with `K = 0.144`, `0.150` and `0.148`. The measured slope `α ≈ 0.45` is the same law.
- **The explicit construction comes within a factor of the constrained minimum** (`--fence-two`). Take
  `x = δ_n + p + y`, with `y` the least-norm interpolant on the band `[πN/H, N]`, weights `φ(log m)/m`, and
  `H = 8√(N/n)`. At `N = 6400`:

  | `n` | `3` | `4` | `6` | `8` | `12` | `16` |
  |---|---|---|---|---|---|---|
  | `Q^pf(x)·√N` | `0.972` | `0.863` | `0.826` | `0.904` | `1.243` | `1.761` |
  | `q_n·√N` | `0.510` | `0.534` | `0.591` | `0.684` | `0.983` | `1.417` |

  The ratio falls with `n`, from `1.91` to `1.24`. The best `κ` in `H = κ√(N/n)` is about `8` at both `N = 1600` and
  `6400`, as `H ∝ √(N/n)` says. The interpolation's condition number stays below `40` until `H` passes `T₀/√2`, where
  the band starts to alias.
- **What follows** (heuristic). With the free cost `n²log N/N`, the best centre is `n ≍ N^{1/5}`, and
  `λ^pf_N ≍ N^{−3/5}(log N)^c`. So `N^{−1/2}` fails, and Theorem C's `−2/3` is not sharp. At the measured constants
  the crossover with the vector centred at `1` is near `N ≈ 10⁹`–`10¹⁰`.
- **Theorem D below turns this into a proof** of `λ^pf_N ≪ N^{−3/5}(log N)³`, with the partners started a little
  earlier so that `δ_n + p` is already silent at the top of the band's range.

**Theorem D (the fence from above; no hypothesis).** There are absolute constants `C` and `N₀` with
`λ^pf_N ≤ C·N^{−3/5}(log N)³` for every `N ≥ N₀`. So `λ^pf_N√N → 0`: the bound `λ^pf_N ≫ N^{−1/2}` fails, and with
Theorem E below, `N^{−3/5}log N ≪ λ^pf_N ≪ N^{−3/5}(log N)³`. Theorem D′ below removes two of the logarithms.

*The vector.* Put `L = log N`, `n = ⌊N^{1/5}⌋`, `H = √(N/n)`, `X = nH/2π`, `M₁ = πN/(2e²H)` and `w(t) = 2/(¼ + t²)`.
Fix `ψ ∈ C^∞` with `ψ = 0` on `(−∞, 0]` and `ψ = 1` on `[1, ∞)`, and a Gevrey-class `φ` with `0 ≤ φ ≤ 1`, `φ = 1` on
`[log M₁ + 1, L − 1]`, `φ = 0` off `[log M₁, L]`, and `|φ̂(ξ)| ≤ Ce^{−c|ξ|^{1/2}}` for `|ξ| ≥ 1`, where
`φ̂(ξ) = ∫φ(v)e^{iξv}dv`.
- `f(u) = ψ(4u/X − 1)(1 − ψ(4u/N − 1))`: `0` below `X/4`, `1` on `[X/2, N/4]`, `0` above `N/2`.
- `p_m = 2cos(2πm/n)f(m)/m`, the twisted partners of `n`.
- `P = {±t_k : t_k ≤ H}`, and for `τ ∈ P` the target `a_τ = −B_{δ_n+p}(τ)`.
- `ω_m = φ(log m)/m` and `G_{τσ} = Σ_m ω_m m^{i(τ−σ)}` for `τ, σ ∈ P`. With `β = G^{−1}a`, put
  `y_m = ω_m m^{−1/2}Σ_{τ∈P}β_τ m^{−iτ}`. It is real, since `P = −P` and `a_{−τ} = ā_τ`, and it lives on `[M₁, N]`,
  away from `n`.

Then `x = δ_n + p + y` has `x_n = 1`, and `B_x(τ) = 0` at every `τ ∈ P`, because `B_y(τ) = (Gβ)_τ = a_τ`.

*Lemma D1 (the band's Gram matrix).* `G = [φ̂(τ − σ)] + E` with `‖E‖ ≤ N^{−10}`. Its smallest eigenvalue is at least
an absolute `c₁ > 0`, and `|(G^{−1})_{τσ}| ≤ N^{−10}` once `|τ − σ| ≥ L⁵`.
- *No aliases.* Poisson summation gives `G_{τσ} = Σ_q ∫φ(log u)u^{−1+i(τ−σ)}e(−qu)du`. The term `q = 0` is
  `φ̂(τ − σ)`. For `q ≠ 0` the phase has derivative `(τ − σ)/u − 2πq`, and `|τ − σ| ≤ 2H ≤ πM₁`, so it is at least
  `π|q|` on the support. Integrating by parts gives `≪_A (M₁|q|)^{−A}`.
- *Ingham.* Consecutive fence points below `H` are `1/Φ′ ≥ γ = 2π/L(H)` apart, and `t_k + t_l ≥ 2t₁ > 29`, so the
  points of `P` are `γ`-separated. `φ = 1` on an interval of length `ℓ = log(N/M₁) − 2 = L(H) + log 4`. So
  `α*[φ̂(τ − σ)]α = ∫φ|Σ_τα_τe^{iτv}|²dv` is at least the integral over that interval. Ingham's inequality (1936)
  bounds it below by `≫ ℓ(1 − (2π/γℓ)²)Σ|α_τ|² ≥ ℓ·(log 4/L(H))·Σ|α_τ|²`, which is `≫ Σ|α_τ|²`.
- *Localisation.* Cutting `G` to `|τ − σ| ≤ L³` changes it by at most `N^{−10}` in norm, by the decay of `φ̂`. The
  cut matrix is banded, with bandwidth `≪ L⁴` in the index. Its condition number is `≪ L`, since the largest
  eigenvalue is `≪ ℓ + 2π/γ`. The bound of Demko, Moss and Smith (1984) for inverses of banded matrices then gives
  `|(G^{−1})_{τσ}| ≪ L(1 − c/√L)^{|k−l|/L⁴}`, which is at most `N^{−10}` once `|τ − σ| ≥ L⁵`.

*Lemma D2 (the partners at the fence).* For every fence point `t_k ≥ 1`,
`B_{δ_n+p}(t_k) = √n·n^{it_k}(1 − f(nt_k/2π)) − I(t_k) + O(√n/t_k + (t_kX)^{−1/2})`, where
`I(t) = Σ_{q≥1}f(nt/(2π(nq+1)))((nq+1)/n)^{−1/2−it} + Σ_{q≥1}f(nt/(2π(nq−1)))((nq−1)/n)^{−1/2−it}`
holds the images.
- `2cos(2πm/n) = e(m/n) + e(m(1 − 1/n))`, so `B_p = S_{1/n} + S_{1−1/n}`, with `S_a(t) = Σ_m e(am)f(m)m^{−1/2+it}`.
- Poisson summation writes `S_a(t) = Σ_q ∫f(u)u^{−1/2+it}e((a − q)u)du`. For `q > a` the phase
  `t log u − 2π(q − a)u` is stationary at `u_q = t/(2π(q − a))`, with second derivative `−t/u_q²`.
- If `q ≤ a`, or `u_q` is more than a factor `2` from the support of `f`, each integration by parts gains `≪ 1/H`:
  `f^{(j)}(u) ≪ u^{−j}`, and `|q − a|·u ≥ X/(4n) ≍ H` or `t ≥ H/2` on the support. These terms give `≪_A N^{−A}`.
- For the other terms `t ≥ H/8`, and stationary phase with a smooth weight (Blomer, Khan and Young 2013,
  Proposition 8.2) gives `f(u_q)(q − a)^{−1/2−it}e^{i(t log(t/2π) − t − π/4)} + O(t^{−1}(q − a)^{−1/2})`.
- `t log(t/2π) − t − π/4 = 2θ(t) + O(1/t)`, and at the anti-Gram points `e^{2iθ(t_k)} = −1 + O(1/t_k)`.
- For `a = 1 − 1/n` the term `q = 1` is `−f(nt/2π)√n·n^{it}`, and the terms `q ≥ 2` give the first sum of `I`;
  `a = 1/n` gives the second. At most `≪ 1 + t/X` terms are active, which gives the error term.
- *Check* (`packing.py --fence-d`, `N = 10⁶`). For `n = 12`, `15` and `16`, `|B_{δ_n+p}(t_k)|/√n` is at most
  `1.7·10⁻⁴` at the fence points from `H` up to `(n − 1)H/4`, and at most `2.9·10⁻²` between `H/2` and `H`. Past
  `(n − 1)H/4`, where the images are on, its maximum on each band is `0.48`–`0.95`.

*Lemma D3 (the partners above `H`).* `Σ_{t_k > H} w(t_k)|B_{δ_n+p}(t_k)|² ≪ n²L/N + L/X`.
- *The centre.* Above `H`, `1 − f(nt/2π) ≠ 0` only where `nt/2π > N/4`. There it costs at most
  `n·W(πN/2n) ≪ n²L/N`.
- *The images.* They switch on at `(n − 1)H/4`, where `f(nt/(2π(n − 1)))` first leaves `0`. On a window `[T, 2T]`
  above that, the active `λ = (nq ± 1)/n` have `q ≪ T/X`, and their logarithms are at least `1/(2nq) ≫ X/(nT)` apart.
  - Montgomery and Vaughan's mean value theorem gives `∫_T^{2T}|I|² ≪ T·Σ_λλ^{−1} ≪ T log(T/X)`. The weights `f(·)`
    vary on the scale of `t`, which costs a constant, and `I′` obeys the same bound with an extra `L²`.
  - Gallagher's lemma, at the fence points of the window, which are `2π/L(2T)` apart, then gives
    `Σ_{t_k∈[T,2T]}|I(t_k)|² ≪ TL·log(T/X)`.
  - Weighted by `w ≍ T^{−2}` and summed over the windows from `(n − 1)H/4 ≍ X` up, this is `≪ L/X`: the factor
    `log(T/X)` grows by `log 2` from one window to the next while `w` falls by `4`, so the first window dominates.
    Past `T = N` the count of active `λ` stops growing, and those windows add `≪ L²/N`.
- *The error.* The error of Lemma D2 contributes `≪ nL/H³`, which is `≪ n²L/N`.

*Lemma D4 (the interpolant above `H`).* `Σ_{t_k > H} w(t_k)|B_y(t_k)|² ≪ L³nH³/N² + N^{−1}`.
- *Up to `πM₁`.* Here `B_y(t) = Σ_τβ_τW̃(t − τ)`, with `W̃(Δ) = Σ_m ω_m m^{iΔ} = φ̂(Δ) + O(N^{−10})` for
  `|Δ| ≤ 3πM₁/2`: as in Lemma D1 there is no alias, the first stationary point being at `|Δ| = 2πM₁`.
  - For `n > 9`, `δ_n + p` is silent on `[H/2, 2H]` up to the error of Lemma D2: `f(nt/2π) = 1` there, and no image
    is on below `(n − 1)H/4`. So `|a_τ| ≪ √n/H` for `|τ| ≥ H/2`.
  - By the localisation of Lemma D1, `|β_τ| ≪ √nL^{O(1)}/H` for `|τ| ≥ 3H/4`.
  - For a fence point `t ∈ (H, πM₁)`, the `τ ≤ 3H/4` then contribute `≪ ‖β‖₁e^{−c√(H/4)}`, and the others
    `≪ √nL^{O(1)}/H·Σ_τ|φ̂(t − τ)|`, which is negligible once `t > H + L²`. So the cost is `≪ nL^{O(1)}/H⁴ ≤ N^{−1}`.
- *Above `πM₁`.* Two band components have ratio at most `N/M₁ = 2e²H/π`, and `L(πM₁/2) > log(2e²H/π) + 1` for `N`
  large. So on windows `T ≥ πM₁` no alias `ℓ ≠ 0` of the fence is stationary for `y`. The fence sum is then the
  continuous integral `∫h_jΦ′|B_y|²`, up to `O(N^{−5})`, by the same Poisson summation as in Lemma F.
  - Montgomery and Vaughan give `∫_T^{2T}|B_y|² ≤ Σ_m|b_m|²(T + O(m))`, with `b_m = √m·y_m = ω_mΣ_τβ_τm^{−iτ}`.
  - By the dual large sieve on the band, `Σ_m|b_m|²m = Σ_m(φ²/m)|Σ_τβ_τm^{−iτ}|² ≪ L|β|²`, and
    `Σ_m|b_m|² ≤ L|β|²/M₁`. So `∫_T^{2T}|B_y|² ≪ (T/M₁ + 1)L|β|²`.
  - Against `w ≍ T^{−2}` and `Φ′ ≍ L`, summed from `T = πM₁`, this is `≪ L²|β|²/M₁²`. With
    `|β|² ≤ c₁^{−2}|a|² ≪ n·#P ≪ nHL` and `M₁ ≍ N/H`, that is `≪ L³nH³/N²`.

*Proof of Theorem D.* Since `x_n = 1`, `λ^pf_N ≤ Q^pf_N(x)`. At the points of `P` (all fence points up to `H`),
`B_x = 0`. Above `H`, `|B_x|² ≤ 2|B_{δ_n+p}|² + 2|B_y|²`. So by Lemmas D3 and D4,
`λ^pf_N ≪ n²L/N + L/X + L³nH³/N² + N^{−1}`.
With `n = N^{1/5}`, `H = N^{2/5}` and `X ≍ N^{3/5}`, each term is `≪ L³N^{−3/5}`. ∎

- **What the proof does not settle** is the power of `log N`. Theorem E below gives the lower bound with one
  logarithm, and Theorem D′ the upper bound: `λ^pf_N ≍ N^{−3/5}log N`.

**Theorem E (the fence's exponent; no hypothesis).** There are absolute constants `c > 0` and `N₀` such that
`Q^pf_N(x) ≥ c·N^{−3/5}log N·Σx_n²` for every real `x` on `[1, N]` and every `N ≥ N₀`. With Theorem D′ below,
`λ^pf_N ≍ N^{−3/5}log N`: the exponent at the fence is `−3/5`, and the power of `log N` is `1`.

**Lemma E (the chain at the band's edge).** For `A ≥ A₀`, `ε ≤ ε₀` and `N ≥ N₀(A, ε)`,
`Q^pf_N(x) ≥ c(A)·(log N/√N)·Σ_{n ≤ εN^{1/5}} x_n²/√n`.

Lemma C works at one height, `T ≍ A√N`, for every `n`. But `x_n` has aliases beyond the first, at `m = n(t/2π)^ℓ`
with `ℓ ≥ 2`, only below height `2π√(N/n)`, and they are how Theorem D's band silences it. At height `≍ A√(N/n)`
only the partners `m ≈ nt/2π` can cancel `x_n`, and they are free above `2πm ≍ A√(nN)`: `√n` times higher, not `n`
times. So the window moves with `n`.

*Proof.* Put `K = εN^{1/5}`. For `0 ≤ i ≤ log₄K` take the block `I_i = [4^i, 4^{i+1})` and the window `j_i` with
`T_i = 2^{j_i} ∈ [4πA√N/2^i, 8πA√N/2^i)`. The windows are distinct, since the left end halves from `i` to `i + 1`.
Fix `i`, write `T = T_i` and `H = H_{j_i}`, and run the proof of Lemma C with the test sequences `u_n`, `n ∈ I_i`.
- **No alias beyond the first.** For `n ∈ I_i` and `t ≥ T/2`, `n(t/2π)² ≥ A²N`. So for every `m ≤ N`,
  `|log(m/n) − ℓL(t)| ≥ 2 log A` when `ℓ ≥ 2`, and `≥ log(A√N/(4K^{3/2}))`, which tends to infinity, when `ℓ ≤ −1`.
- **The family is almost orthogonal.** For distinct `n, n' ∈ I_i`, `T|log(n'/n)| ≥ T/4^{i+1} ≥ πA√N/K^{3/2}`, which
  tends to infinity. The terms `ℓ ≠ 0` between them are non-stationary, as in Lemma C.
- **Only the partners alias.** As in Lemma C, with `P_n = {m : m/n ∈ [T/8π, 2T/π]}`. Every partner has
  `(A/2)2^i√N ≤ m ≤ 64A·2^i√N`. So `√N ≤ m ≤ N` for `A ≥ 2`, `M_m = m`, and Lemma F charges it `Ω_m = W(16πA·m)`.
- **Schur's test.** The diagonal bound `(RR*)_{nn} ≤ C₁A·H` of Lemma C depends on neither `n` nor `T`. Off the
  diagonal, `Σ_{n'∈I_i, n'≠n}|(RR*)_{nn'}| ≤ CA·H·(4^{i+1})²/T ≤ (4C/π)H·K^{5/2}/√N = (4C/π)ε^{5/2}H`, which is at
  most `H` once `ε ≤ ε₀`.

So, as in Lemma C, `H·Σ_{n∈I_i} x_n²/n ≤ C(A)(E_{j_i} + Σ_{m∈P^{(i)}} b_m²Ω_m) + O(HN^{−1}Σx_n²)`, with
`P^{(i)} = ∪_{n∈I_i}P_n`. Now sum over `i`:
- The windows are distinct, so `Σ_i E_{j_i} ≤ Q^pf_N(x)`.
- `P^{(i)}` lies in `[(A/2)2^i√N, 64A·2^i√N]`, an interval of ratio `2⁷` that doubles with `i`. So each `m` lies in at
  most `8` of the `P^{(i)}`, and by Lemma F `Σ_iΣ_{m∈P^{(i)}} b_m²Ω_m ≤ 8Σ_m b_m²Ω_m ≤ 16Q^pf_N(x)`.
- `H_{j_i} ≥ c_η L(T_i)/(2πT_i) ≥ c_η·log N·2^i/(40π²A√N)`, and `2^i > √n/2` on `I_i`. So
  `H_{j_i}/n ≥ c_η log N/(80π²A√(nN))`.
- The remainders lie far below Lemma F's `Q^pf_N(x) ≫ (log N/N)Σx_n²`. ∎

*Proof of Theorem E.* Normalise `Σx_n² = 1`, and fix `A = A₀`, `ε = ε₀` and `K = εN^{1/5}`.
- For `n ≤ K`, Lemma E charges `x_n²` at least `c log N/√(KN) = cε^{−1/2}N^{−3/5}log N`.
- For `K < n ≤ √N`, Lemma F charges it `n²(L(16πAN/n) + 1)/(16π²AN) ≥ K²log N/(32π²AN) = ε²N^{−3/5}log N/(32π²A)`.
- For `n > √N`, Lemma F charges it at least `log N/(32π²A)`.

Adding the two lemmas gives `2Q^pf_N(x) ≥ c'·N^{−3/5}log N`. ∎

- **Why Theorem C missed it.** Lemma C fixed the window at `T ≍ A√N` for every `n`: the lowest height at which no
  `x_n` has a second alias. There the partners of `x_n` are free only `n` times higher, which gives `1/n`. The second
  alias of `x_n` already leaves `[1, N]` at `2π√(N/n)`, and from there the partners are free `√n` times higher, which
  gives `1/√n`: the `α = ½` of the two-mechanism count.
- **What it leaves** is the constant. Theorem D′ below brings the upper bound down to `N^{−3/5}log N`.
- **The numbers agree.** At `N = 12800` the part of `q_n` paid below the free height (the row "below" of
  `--fence-cap`) is `0.78/√(nN)`, `0.81/√(nN)` and `0.80/√(nN)` for `n = 3`, `4` and `5`.

**Theorem D′ (the order at the fence; no hypothesis).** There are absolute constants `C` and `N₀` with
`λ^pf_N ≤ C·N^{−3/5}log N` for every `N ≥ N₀`. With Theorem E, `λ^pf_N ≍ N^{−3/5}log N`.

Two of Theorem D's three logarithms come from its band (the third was a lossy sum in Lemma D3). The interpolant `y`
is least-norm in `Σ_m b_m²m`, which spreads its mass down to the bottom `M₁ ≍ √(nN)` of the band. What the fence
charges a component above its free height is `b_m²W(2πm) ≍ log N·b_m²/m`, which wants the mass at the top. A chirp
puts it there. At each height `t` it cancels `x_n` through the largest alias `ℓ ≥ 2` with `n(t/2π)^ℓ ≤ N/2`, and at
the fence points `e^{2πiℓΦ(t_k)} = (−1)^ℓ` makes the cancellation exact. What is left is what Lemma E charges: the
partners above `≍ √(N/n)`, where only the first alias exists.

*The vector.* Put `L = log N`, `n = ⌊N^{1/5}⌋`, `H₀ = π√(N/n)`, `X = nH₀/2π`, `T_c = L⁶` and
`m_c = (N/2e)^{2/3}n^{1/3}`. Then `x = δ_n + p + y_c + y_b`, where:
- `p` is Theorem D's twisted partners for this `X`: `f` rises on `[X/4, X/2]` and falls on `[N/4, N/2]`.
- `y_c` is the chirp. Fix a Gevrey step `σ`, `0` on `(−∞, −1]` and `1` on `[0, ∞)`. Put
  `A_ℓ(t) = log(N/2n) − ℓL(t)`, `χ_ℓ = σ(A_ℓ − 1) − σ(A_{ℓ+1} − 1)` for `ℓ ≥ 2`, and
  `e(t) = σ(t/T_c − 2)(1 − f(nt/2π))`. For `t > 0` let
  `g(t) = −√n·e(t)Σ_{ℓ≥2}χ_ℓ(t)(−1)^ℓe^{i(t log n + 2πℓΦ(t))}`, and `g(−t) = ḡ(t)`. Then
  `Ĝ(v) = (1/2π)∫g(t)e^{−itv}dt` is real, and `y_{c,m} = Ĝ(log m)m^{−3/2}` for `m ≤ N`.
- `y_b` is Theorem D's least-norm interpolant, now only at the fence points `|τ| ≤ 4T_c`, on the band
  `[πN/(16e²T_c), N]`, with the targets `a_τ = −B_{δ_n+p+y_c}(τ)`.

*Lemma D5 (the chirp).*
1. `Σ_ℓχ_ℓ = 1` on `[T_c, H₀/2]`. Where `χ_ℓ ≠ 0`, `m_ℓ(t) = n(t/2π)^ℓ` lies in `[m_c, N/2]`. And `Ĝ(v) ≪ N^{−11}`
   unless `log m_c − 1 ≤ v ≤ log N`.
2. For `|t| ≤ m_c/12`, `B_{y_c}(t) = g(t) + O(N^{−10})`. So at the fence points up to `m_c/12`,
   `B_{y_c}(t_k) = −√n·e(t_k)n^{it_k} + O(N^{−10})`, which is `O(N^{−10})` above `H₀/2`.
3. `Σ_{t_k > m_c/12} w(t_k)|B_{y_c}(t_k)|² ≪ L·nH₀/m_c²`.

*Proof.*
1. The sum telescopes to `σ(A₂ − 1)`, which is `1` once `m₂(t) ≤ N/2e`; at `t = H₀/2`, `m₂ = N/16`. And `χ_ℓ ≠ 0`
   needs `A_ℓ > 0`, so `m_ℓ < N/2`, and `A_{ℓ+1} < 1`, so `m_{ℓ+1} > N/2e` and
   `m_ℓ > (N/2e)^{ℓ/(ℓ+1)}n^{1/(ℓ+1)} ≥ m_c`. On piece `ℓ` the phase `t log n + 2πℓΦ(t) − tv` has `t`-derivative
   `log m_ℓ(t) − v`, which is at least `log 2` in size for `v` off `[log m_c − 1, log N]`. The amplitude is Gevrey of
   order `2` on the scale `T_c/L = L⁵`, since `χ_ℓ` varies on the scale `t/ℓ`. So non-stationary phase gives
   `≪ √nH₀e^{−cL^{5/2}}` there.
2. By part 1, `B_{y_c}(t) = Σ_m ρ(m)Ĝ(log m)m^{it−1} + O(N^{−10})`, with `ρ` smooth, `1` on `[m_c/e, N]` and `0` off
   `[m_c/2e, 2N]`. Poisson summation turns this into `Σ_q ∫ρ(u)Ĝ(log u)u^{it−1}e(−qu)du`.
   - The term `q = 0` is `∫ρ(e^v)Ĝ(v)e^{itv}dv = g(t) + O(N^{−10})`.
   - For `q ≠ 0`, each integration by parts gains `≪ (|t| + H₀ + log N)/(|q|m_c)`, at most `1/(2|q|)` for
     `|t| ≤ m_c/12`, because `|Ĝ^{(j)}| ≤ (1/2π)∫|t|^j|g|` and `g` lives below `H₀/2`.
   - At the fence points `(−1)^ℓe^{2πiℓΦ(t_k)} = 1` and `Σ_ℓχ_ℓ = 1`, so `g(t_k) = −√n·e(t_k)n^{it_k}`. Above `H₀/2`,
     `g = 0`.
3. On the windows `T ≥ m_c/24`, the components of `y_c` have log-ratio `log(eN/m_c) < L(T/2) − 1`. So no alias of the
   fence is stationary, and the fence sum is the continuous integral up to `O(N^{−5})`, as in Lemma D4.
   - Montgomery and Vaughan give `∫_T^{2T}|B_{y_c}|² ≤ Σ_m b_m²(T + O(m))`, with `b_m = Ĝ(log m)/m`.
   - `Σ_m b_m²m ≈ ∫Ĝ² = (1/2π)∫|g|² ≤ nH₀/π`, and `Σ_m b_m² ≤ (e/m_c)Σ_m b_m²m`.
   - Against `w ≍ T^{−2}` and `Φ′ ≍ L` this sums to `≪ L·nH₀/m_c²`. ∎

*Proof of Theorem D′.* `λ^pf_N ≤ Q^pf_N(x)`, and the fence points split as follows.
- **Up to `4T_c`:** `B_x(τ) = 0`, by `y_b`. Its targets are `O(N^{−10})` on `[2T_c, 4T_c]`, where `e = 1` and `p` is
  inactive. So by the localisation of Lemma D1, `B_{y_b} = O(N^{−5})` from `4T_c` up to `π²N/(16e²T_c)`. Above that,
  Lemma D4 bounds its cost by `≪ L²|β|²(T_c/N)² ≪ nL³T_c³/N²`.
- **From `4T_c` to `H₀/8`:** `B_x = O(N^{−5})`. The chirp cancels `δ_n` exactly, and `p` is inactive.
- **From `H₀/8` to `(n − 1)H₀/4`:** `B_x = O(√n/t + (tX)^{−1/2})` by Lemma D2, since the chirp cancels its main term
  `√n n^{it}(1 − f(nt/2π))`. This costs `≪ nL/H₀³`.
- **Above that:** Lemma D3 for `δ_n + p`, Lemma D5 for the chirp, Lemma D4 for `y_b`.

So `λ^pf_N ≪ n²L/N + L/X + nL/H₀³ + LnH₀/m_c² + nL³T_c³/N² + N^{−1}`. With `n = N^{1/5}`, `X ≍ N^{3/5}`,
`H₀ ≍ N^{2/5}` and `m_c ≍ N^{11/15}`, the first two terms are `≍ L·N^{−3/5}` and the rest `≪ L·N^{−4/5}`. ∎

- **The check** (`packing.py --fence-chirp`: `N = 10⁶`, `n = 15`, `T_c = 60`, `H₀ = 2π√(N/n) = 1622`, and `Ĝ` replaced
  by its leading stationary-phase term). The chirp uses `m` from `12029` to `754879`. It matches `−√n n^{it}` at the
  fence points of `[120, 811)` to within `3.4%` (rms at most `1.6%`, the stationary-phase error), at a fence cost of
  `1.7·10⁻⁵`. Above `H₀/2 = 811` it is silent, to `10⁻⁴·√n` and then `10⁻¹²·√n`. Its free energy `Σ_m b_m²W(2πm)` is
  `6.9·10⁻⁷`, against `log N/X = 3.6·10⁻³` for the partners.
- **So the band was never the constraint.** Silencing `x_n` below `√(N/n)` is nearly free. What costs is that above
  `2π√(N/n)` only the first alias is left, as Lemma E says. The two-mechanism count of the paragraph "Below the
  partners' start" balanced the least-norm band against the images: it found the right height for the wrong reason.

**What the numbers allowed.** Suppose the cost per window behaves like `C·n^{−α}` for large `n`. The free cost
`n²log N/N` balances it at the centre `n ≍ N^{1/(4+2α)}`, and then `λ^pf_N ≍ N^{−1/2−α/(4+2α)}log N`. Theorems D and
E decide for `α = ½`.
- **`α = 1`**, the dependence on `n` in Lemma C, gives `−2/3`. Theorem E rules it out.
- **`α = ½`**, the balance of the two mechanisms above, gives `−3/5`. Theorems D′ and E prove it, with the power of
  `log N`.
- **`α ≈ 0.45`**, the slope between `n = 3` and `11` at `N = 12800`, with `C ≈ 0.14`, gives `−0.59`. A model with this
  law, the free part, the excess as modelled above, and `n = 1`'s own cost per window reproduces `q_1` and `q_5` at
  `N ≈ 10⁴` to within `5%`. In that model the vector centred at `1` loses, around `N ≈ 10¹⁰`, to one centred near
  `n ≈ 80`. Asymptotically the slope is `½`.
- **A floor, `α = 0`,** would keep the vector centred at `1` optimal and the exponent at `−1/2`. Theorem D rules it
  out.

So `λ^pf_N ≍ N^{−3/5}log N` is proved (Theorems D′ and E), although up to `N = 12800` the fence
behaves like `N^{−1/2}`: `λ^pf_N√N = 0.117, 0.123, 0.132, 0.136` at `N = 400, 1600, 6400, 12800`. The decay faster
than `N^{−1/2}` shows only far beyond that, near `N ≈ 10⁹`–`10¹⁰` at the measured constants.

**What the theorems settle.**
- **The mechanism needs arithmetic.** On the class, the zeta form sags like `log N/N`: Theorem A, and the theorem
  above. The picket fence has a margin that does not depend on `N`: Theorem B. The sag is exactly the bulk residue
  `ζ(1 − ρ)M_e(1 − ρ)`, which vanishes at the zeros of `ζ` and nowhere else. Its partner, the boundary residue
  `N^ρĜ(ρ)`, vanishes at every zero only when `Ĝ` carries the factor `ζ`.
- **The inverse theorem holds on the class.** There, being quiet at the zeros means carrying `ζ`, and carrying `ζ`
  costs spread `≍ log N` and quotient `≥ 0.0400·log N/N`.
- **For every vector the fence is louder by a power of `N`.** Theorem E gives `λ^pf_N ≫ N^{−3/5}log N` (Theorem C
  had `N^{−2/3}log N`), against `λ_N ≤ 67(1 + log N)/N` at the zeros under RH. A point set with the zeros' density
  and no arithmetic cannot be as quiet as the zeros, for any vector.
- **But not by `N^{1/2}`: the order is `N^{−3/5}log N`.** Theorems D′ and E give `λ^pf_N ≍ N^{−3/5}log N`, so
  `λ^pf_N ≫ N^{−1/2}` fails and the exponent at the fence is exactly `−3/5`. The vector that shows it is centred at
  `n ≍ N^{1/5}`: a chirp of components near `N` below `√(N/n)`, and above it the twisted partners, which the fence's own functional equation (its points are the anti-Gram points) makes cancel `x_n`
  exactly. Lemma E shows that nothing does better: just above `√(N/n)` only those partners can cancel `x_n`, and they
  are free `√n` times higher.

**What silence costs** (`scripts/landau_gap.py --silent`, `--split`, `--quiet`; numerics, uncertified). Step 3 of the
section "The low zeros" says a proof has to show that silencing a vector at the zeros below height `≍ N` costs
`A + B ≳ log N`. Here that cost is measured over all vectors, together with where the cheap silent vectors live.

- **The measurement.** `m(T)` is the least `A + B` of a unit vector with `V_x(ρ) = 0` at every zero up to height `T`.
  A direction counts as silent below `10⁻⁷` of the top singular value of the conditions, since the ordinates carry nine
  decimals. Up to `T = N`, moving the threshold to `10⁻⁵` changes the zeros' `m` by under `3%`.

  | `T` | `110` | `350` | `1000` | `2000` | `4000` | `8000` |
  |---|---|---|---|---|---|---|
  | zeros, `N = 1000` | `8.07` | `9.86` | `12.19` | `14.08` | | |
  | zeros, `N = 2000` | `8.20` | `9.37` | `11.49` | `13.04` | `15.47` | |
  | zeros, `N = 4000` | `8.47` | `8.98` | `11.13` | `12.43` | `13.90` | `16.01` |
  | zeros, `N = 8000` | `8.76` | `9.01` | `10.80` | `11.96` | | |
  | picket fence, `N = 2000` | `8.64` | `12.14` | `2256` | `5956` | `14993` | |

- **At the low zeros silence is nearly free.** At the first 33 zeros, `m(110)` is within `4.3%`, `1.6%`, `0.9%` and
  `0.5%` of the unconstrained minimum `2.9√log N` at `N = 1000`, `2000`, `4000` and `8000`. At a fixed `T` it falls
  slowly as `N` grows.
- **At heights `≍ N` it grows like `log N`.** There is no wall below `2N`. At a fixed ratio `T/N`, `m` rises by the
  same step each time `N` doubles:

  | `T/N` | `N = 1000` | `2000` | `4000` | the two steps |
  |---|---|---|---|---|
  | `½` | `10.544` | `11.487` | `12.432` | `0.943`, `0.945` |
  | `0.7` | `11.170` | `12.155` | `13.148` | `0.985`, `0.993` |

  - At threshold `10⁻⁵` the steps are `0.943, 0.943` and `0.991, 0.989`.
  - A law in `√log N` would make the second step `4%` shorter than the first.
  - Along `T/N = 0.35`, from `N = 2000` to `8000`, the steps are `0.883` and `0.874`, or `0.895` and `0.861` at
    `10⁻⁵`. That diagonal cannot tell the two laws apart.

  So silence up to height `cN` costs about `a_c + 1.4 log N`.
- **Quiet costs a little less, and grows the same way** (`--quiet`). `Q_≤N` is the zeta form cut at height `N`. The
  least `A + B` of a unit vector with `Q_≤N ≤ ε·log N/N` is:

  | `ε` | `N = 1000` | `2000` | `4000` | the two steps |
  |---|---|---|---|---|
  | `0.02` | `9.111` | `9.791` | `10.506` | `0.680`, `0.715` |
  | `0.01` | `9.502` | `10.258` | `11.027` | `0.756`, `0.769` |
  | `0.005` | `9.866` | `10.680` | `11.501` | `0.814`, `0.821` |
  | `0.002` | `10.278` | `11.153` | `12.028` | `0.875`, `0.875` |

  These come from exact eigensolves along the frontier, interpolated in `log ε`, with no threshold. At every `ε` the
  second step is at least as long as the first. The minimiser of `Q_N` has `Q_≤4N·N/log N ≈ 0.004`, since `92%` of its
  `Q_N` comes from above `4N` (section "Packing"). So it is at least as quiet below `N` as the row `ε = 0.005`.
- **The fence pays for silence linearly.** Of the `2·#{γ ≤ T}` real conditions only about `(T/π)(1 + log(πN/T))` are
  independent. That is the count of the section "Packing", made for the window `[−T, T]`.
  - At the fence the numerical rank is the smaller of the two, to within `5%` near their crossing at `T ≈ πe√(2N)` and
    `2%` away from it.
  - Past the crossing the fence's silent vectors are pushed off `n ≲ T/π`. From `T = N` on their spread is
    `A ≈ T/π` to within `15%`, and `m ≈ (log N + c₀ + 1)A`.
  - The zeros' silent minimisers keep `A ≤ 3.3`.
- **The cheap silence is the dilates of `ζ`** (`--split`). On the silent space, `A + B` has exactly `⌊2πN/T⌋` more
  eigenvalues at the zeros than at the fence, and they are the cheap ones:

  | `N`, `T` | `2πN/T` | the zeros' lowest eigenvalues | the zeros' next three over the fence's first three |
  |---|---|---|---|
  | `2000`, `2000` | `6.28` | `13.0, 30.6, 55.4, 81.1, 107.6, 194.9` | `0.995, 0.996, 1.000` |
  | `4000`, `4000` | `6.28` | `13.9, 32.3, 55.4, 87.4, 117.5, 152.3` | `0.995, 0.996, 1.000` |
  | `4000`, `2000` | `12.57` | twelve, from `12.4` to `303.5` | `0.993, 0.989, 0.993` |

  - The fence's lowest eigenvalues are `5956`, `12583` and `4895`. Above the extra ones the two spectra agree
    eigenvalue by eigenvalue: the next four to within `1%` in all three cases.
  - **Removing the dilates.** Take the part of the silent space that is `K`-orthogonal to
    `Y_D = span{[d | n]B_j(n/N)/n : d ≤ D, j ≤ 12}`, with `B_j` cubic B-splines. Its lowest eigenvalue jumps to the
    fence's level by `D = ⌊2πN/T⌋` and barely moves beyond it. For `N = 4000`, `T = 2000` it is `302` at `D = 11` and
    `6017` at `D = 12`. For `N = T = 4000` it is `348` at `D = 5` and `16208` at `D = 6`.
  - **The rank.** Well past the crossing, the zeros' numerical rank is below the fence's by `⌊2πN/T⌋`. That
    holds exactly in `11` of `13` cases at `N = 1000`, `1500` and `2000`, and by one more in the other two.
  - **Why `⌊2πN/T⌋`** (heuristic). It counts the `d` with `2πN/d > T`. Since `ζ(1 − ρ) = 0`, the approximate
    functional equation keeps the dilate `[d | n]/n` of the zeta vector silent below `2πN/d`, up to a boundary term
    that all the dilates share.
  - **Quiet needs the dilates too** (`--quiet`). At `μ = 2048` the frontier minimiser has `A + B = 11.2, 12.1, 13.1`
    and `Q_≤N·N/log N ≈ 10⁻⁴` at `N = 1000, 2000, 4000`. Taken `K`-orthogonal to the dilates `d ≤ D`, it gets louder
    and dearer with every `d` removed:

    | `D` | `1` | `3` | `5` | `6` | `7` | `8` |
    |---|---|---|---|---|---|---|
    | `A + B`, `N = 2000` | `22.9` | `68.5` | `107.9` | `140.9` | `185.6` | `244.2` |
    | `Q_≤N·N/log N`, `N = 1000` | `0.00022` | `0.0022` | `0.020` | `0.0893` | `0.336` | `0.459` |
    | `Q_≤N·N/log N`, `N = 2000` | `0.00025` | `0.0020` | `0.014` | `0.0887` | `0.338` | `0.456` |
    | `Q_≤N·N/log N`, `N = 4000` | `0.00030` | `0.0021` | `0.010` | `0.0891` | `0.346` | `0.457` |

    From `D = 6 = ⌊2π⌋` on, the loudness no longer depends on `N`. By the Lagrange bound, a vector `K`-orthogonal to
    the dilates `d ≤ 6` that is as quiet below `N` as the minimiser of `Q_N` (`Q_≤N·N/log N ≤ 0.0475`) has
    `A + B ≥ 224` at all three `N`.
- **The zeta vector.** `x_n = w(n/N)/n`, with `w = 1` on `[0, ½]` and `0` past `1`, has `A + B = 2.6 log N` at
  `N = 1000` to `8000`. Its rms `|V_x(ρ)|/‖x‖` is below `10⁻⁴` from height `100` to `2N`. At the fence it is between
  `0.5` and `2`.

So the inverse theorem through `rate_slack` comes down to a robust form of this split. A vector quiet at the zeros up to
height `cN` should lie, up to a part that costs `≫ log N`, in the span of the dilates `d ≤ 2π/c`. That span is the
class with `D₀ = 2π/c`, where Theorem A applies. Numerically the robust form holds at `N ≤ 4000` ("Quiet needs the
dilates too"). What is missing is its proof: the mean value of step 3, one that tells the `ζ`-multiples from the
incoherent tails at the zeros below `N` for vectors that are only quiet. No count can supply it, since at the zeros the
counted conditions are dependent through `ζ`.

**What stays open.**
- **For every vector, `λ_N ≫ log N/N`.** It would follow from the claim that minimisers of `Q_N` stay within
  `o(log N/N)`, in the norm of `Q_N`, of the class with some fixed `D₀`. The class reaches within `1.6%` at
  `N ≤ 3·10⁴`, and its profile and local factors match the minimiser's.
  - Theorem C's method does not carry over. At the zeros no component is ever free below height `N`, because Landau's
    form couples every `m` to its multiples and divisors at every height.
  - So nothing plays the part of Lemma F except the slack bound `BallSharp.rate_slack`, and its gap is `√log N`
    (`BallGap`).
  - By `rate_slack` only the vectors with `A + B = o(log N)` matter. They sit near the bottom of the spectrum of
    `A + B`: mostly `δ₁`, with a tail that is nearly harmonic on the divisibility network. Along the frontier of the
    section "The low zeros" they get louder with `N`, not quieter.
  - The obstruction is the tail. A vector with `A ≤ log N` has at most `(log N/M)Σx_n²` of its mass beyond `M`, but
    up to `log N·Σx_n²` of `Σb_n²` there. At the zeros below `N` that is enough to cancel a head of length `M` that the
    zeros up to `e⁸M` sample (`BallSharp`). Ruling the cancellation out is the inverse theorem again.
  - **Silence and quiet at the zeros below `N`** (the paragraph "What silence costs" above). Silence at the low zeros
    is nearly free, so the low zeros together with `A + B` carry nothing usable. Silence or quiet up to height `≍ N`
    costs `≍ log N`, and the cheap silent vectors are the `⌊2πN/T⌋` dilates of `ζ`. Numerically the split holds for
    vectors that are only quiet, too. What is missing is a proof of it for them.
  - **Nor does a split along the low eigenspace of `A + B` help.** Put the vector's part in that eigenspace against the
    first few zeros. The part outside it can buy as much loudness there, per unit of `A + B`, as the eigenspace has,
    so the cross terms are not controlled.
- **For the fence, only the constant.** `λ^pf_N ≍ N^{−3/5}log N` (Theorems D′ and E).
