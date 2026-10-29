# Zero density for `ζ` with the exponents `12/5` and `30/13`, and primes in short intervals

**Lean:** `lib/pnt/ZetaGMDensity.lean`:

```lean
theorem ZetaGMDensity.densityXi_thirty_thirteenths {ε : ℝ} (hε : 0 < ε) : DensityXi (30 / 13 + ε) 12

theorem ZetaGMDensity.short_primes_seventeen_thirtieths {θ : ℝ} (hθ : 17 / 30 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ

theorem ZetaGMDensity.almost_all_short_primes_two_fifteenths {θ : ℝ} (hθ : 2 / 15 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      volume {y | y ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ}
        ≤ ENNReal.ofReal (X ^ (1 - δ))
```

`DensityXi A B` (`lib/core/ShortPrimes.lean`) says that `N(½ + w, T) ≤ C T^{A(½ − w)}(log T)^B` for `T ≥ 2` and
`0 ≤ w ≤ ½`, where `ShortWeil.NX w T` counts the zeros of `ζ` with `|γ| ≤ T` and `β ≥ ½ + w`. In words: for every
`ε > 0`, `N(σ, T) ≪ T^{(30/13 + ε)(1−σ)}(log T)^{12}`; for every `θ > 17/30` every interval `(y, y + y^θ]` with `y`
large holds a prime; and for every `θ > 2/15` the `y ∈ [X, 2X]` whose interval holds no prime have measure at most
`X^{1−δ}`.

The classical stage comes first, with the same shapes: `ZetaHuxley.densityXi_twelve_fifths` (`DensityXi (12/5 + ε) 12`),
`ZetaHuxley.short_primes_seven_twelfths` (`θ > 7/12`) and `AlmostAll.almost_all_short_primes` (`θ > 1/6`). The last
is a case of `AlmostAll.almost_all_of_density`, which gives `θ > max(0, 1 − 2/A)` from `DensityXi (A + ε) B` for every
`ε > 0`; `1 − 2/(30/13) = 2/15`.

Behind the exponent `30/13` is Guth and Maynard's large values estimate (`lib/pnt/ZetaGMLV.lean`):

```lean
theorem ZetaGMLV.gm_large_values {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (R : Finset ι) (x : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (c : ℕ → ℂ),
      0 ≤ T → 1 ≤ N → 7 / 10 ≤ σ → σ ≤ 4 / 5 → (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) →
      (∀ n, ‖c n‖ ≤ 1) → (∀ r ∈ R, |x r| ≤ T) → (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |x r - x r'|) →
      (∀ r ∈ R, N ^ σ / 6 ≤ ‖dp S c (x r)‖) →
      (R.card : ℝ) ≤ C * N ^ ε * (T * N ^ (12 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ))
```

In words: for `7/10 ≤ σ ≤ 4/5`, a Dirichlet polynomial `D(x) = Σ_{n∈S} c_n n^{−ix}` (`DirMean.dp`) with `|c_n| ≤ 1`
on `[6N/5, 9N/5]` is at least `N^σ/6` at at most `CN^ε(TN^{12/5−4σ} + N^{18/5−4σ})` points of `[−T, T]` that are
`1` apart. Its key proposition, Guth and Maynard's Proposition 3.1 at `T^ε`-separated points, is
`ZetaGMLV.gm_prop31_one`.

These theorems, the counts on each range named below (`nx_ingham`, `nx_huxley`, `nx_ingham13`, `nx_gm`, `nx_gmh`),
`ZetaFourth.zeta_fourth_moment` and `ZetaKernel.norm_kz_le` are printed in `lib/check/CheckAll.lean`, and depend only
on `propext`, `Classical.choice` and `Quot.sound`. No paper of the repository uses them, and none claims them: they
are results of the literature that the library formalises.

## Sources

- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*, Ann. of Math. (2) 203 (2026),
  623–675; arXiv:2405.20552 (v2 of 7 April 2026). Their abstract announces the zero density estimate
  `N(σ, T) ≤ T^{30(1−σ)/13+o(1)}` and the expected number of primes in short intervals of length `x^{17/30+o(1)}`. The
  module docstrings quote their Theorem 1.1, `R ≤ T^{o(1)}(N²V^{−2} + N^{18/5}V^{−4} + TN^{12/5}V^{−4})`
  (`ZetaGMLV`), and their Proposition 3.1, the key proposition, for "a set of T^ϵ-separated points in an interval of
  length T = N^{6/5}" (`ZetaGMProp`).
- A. E. Ingham, *On the estimation of N(σ, T)*, Quart. J. Math. Oxford Ser. 11 (1940), 291–292: the exponent
  `3/(2 − σ)`, which is at most `12/5` exactly for `σ ≤ 3/4`. M. N. Huxley, *On the difference between consecutive
  primes*, Invent. Math. 15 (1972), 164–170: the exponent `12/5` for `σ ≥ 3/4`, primes in short intervals for
  `θ > 7/12`, and in almost all of them for `θ > 1/6`.
- B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296v2, whose large-values argument with characters the library
  formalises ([chen-gupta-li-density.md](chen-gupta-li-density.md)). At `q = 1` it is Guth and Maynard's.

## What the formalisation here is

- **Guth and Maynard's key proposition** (`ZetaGMProp.gm_prop31_pt`, from Chen–Gupta–Li's Proposition 8.1 and
  Theorem 10.1, which the library proves: `ZetaGMLV.gm_prop31_one`) is the library's Chen–Gupta–Li chain at `q = 1`,
  with several points in place of one point per character. The
  energy side (their Lemmas 10.5, 10.6, 10.9 and 10.10, Proposition 10.2 and Theorem 10.1) holds for points more than
  `2` apart when they share a character (`LinnikCGLL105.Spaced`), and the `S₂` chain (Propositions 4.6 and 6.1) for
  points at least `1` apart; one point per character is a case of both, so the Linnik chain's statements are
  unchanged. At `q = 1` the term `m = 0` of an off-diagonal Gram entry no longer vanishes by orthogonality: it is
  carried as an error that decays in `|t_i − t_k|` (`ZetaGMTrace`). Lemma 9.1 is proved for any points, with their
  (11.2) (`ZetaGMBlock`), and Proposition 11.1 for `T^ε`-separated points (`ZetaGMS3.gms3`).
- **Their Theorem 1.1** (`ZetaGMLV.gm_large_values`) follows as in their proof: the points are divided into
  intervals of length `N^{6/5}`, and each interval into classes whose points are far enough apart for the key
  proposition.
- **The count on `[7/10 + η, 4/5]`** (`ZetaGMWin.nx_gm`) uses the zero detector of `InghamDensity` at
  `X = ⌊U^{1/100}⌋`, `Y = U^{1/2}`. Each zero is moved to the line `Re s = σ` by a Taylor polynomial
  (`taylor_pick_dp`), and a power `m ≤ 77` of each block, of length in `[U^{10/13}, U^{15/13}]`, is cut into pieces
  of ratio `3/2`, the shape `[6N/5, 9N/5]` of the key proposition. Each piece is counted by Guth and Maynard's
  estimate when `N^{18/5−4σ} ≤ U^{(30/13)(1−σ)}`, and otherwise by the mean value theorem at well-spaced points.
- **The other ranges of `30/13`:** the trivial count below `17/30`; Ingham's window at `c = 1/13` on
  `[17/30, 7/10 + η]` (`ZetaGMIngham.nx_ingham13`); Huxley's argument with the exponent `30/13` on `[4/5, 11/12]`
  (`ZetaGMHux.nx_gmh`); and no zero above `11/12`. They are glued at `η = min(ε, 1)/100`.
- **The exponent `12/5`:** Ingham's window on `[7/12, 3/4]` (`ZetaIngham.nx_ingham`), with the fourth moment of `ζ`
  at well-spaced points (`ZetaFourth.zeta_fourth_moment`, from the approximate functional equation for `ξ²` in
  `ZetaAFE`); and on `[3/4, 11/12]` (`ZetaHuxley.nx_huxley`) the same detector with each block's power counted by the
  Halász–Montgomery inequality at well-spaced heights (`ZetaKernel`). This is the method of the library's estimates
  over the characters mod `q` ([ingham-density.md](ingham-density.md), [huxley-density.md](huxley-density.md)), not
  Huxley's large-values estimate.
- **The primes:** a density estimate and a zero-free region give primes in short intervals
  (`ShortWeil.short_primes_of_density`; here `ZetaHuxley.short_primes_of_density_eps_hp`). Primes in almost all
  intervals come from Weil's explicit formula, whose sum over the zeros is bounded in mean square over windows of
  `log x` (`AlmostAllArch`, `AlmostAllMean`, `AlmostAllPrimes`).

## Differences from the sources

- **Theorem 1.1 in part.** It is stated at `V = N^σ/6` with `7/10 ≤ σ ≤ 4/5`, for coefficients on `[6N/5, 9N/5]`:
  the range of their key proposition, and all that the density count needs. There their term `N²V^{−2}` is at most a
  constant times `N^{18/5}V^{−4}`, and it is left out. The factor is `CN^ε` in place of `T^{o(1)}`.
- **The zero-free half-plane above `σ = 4/5`.** Guth and Maynard's estimate is unconditional. Here the density
  estimates use the half-plane `Re s > 11/12` ([openai-half-plane.md](openai-half-plane.md)): above `11/12` there is
  no zero, and on `[4/5, 11/12]` (on `[3/4, 11/12]` for `12/5`) the bound `|ζ(1/12 + it)| ≪ |t|^{5/12+ε}` of the
  Halász–Montgomery step comes from it (`ZetaKernel.norm_kz_le`, through `Subconvexity.zeta_strip_eleven_twelfths`).
  The short-interval theorems take their zero-free region from it (`ShortPrimesHalfPlane.zeroFreeXi_of_halfplane`),
  not from Korobov and Vinogradov's (`ShortKV.zeroFreeXi_KV`), and the almost-all theorems use it through
  `HalfPlaneJoins.abs_im_tau_le_five_twelfths`. So `densityXi_thirty_thirteenths` and its corollaries rest on the
  half-plane, while Guth and Maynard's own part does not: `python3 scripts/census.py` finds the half-plane's proof
  (`lib/core/KubotaThetaProof.lean`) among the declarations behind `densityXi_thirty_thirteenths` and `nx_gmh`, and
  no module of it behind `gm_large_values`, `nx_gm`, `nx_ingham13` or `nx_ingham`.
- **Forms that the half-plane allows.** The almost-all theorems bound the exceptional set by `X^{1−δ}`, a power
  saving that comes from the half-plane. The short-interval theorems give one prime in each interval, where Guth and
  Maynard give the expected number.
