# Weil positivity on Connes and Consani's subspace at support log 3 / 2

Labels: **Proved** means Lean, no `sorry`, axioms `propext`, `Classical.choice` and `Quot.sound` only. The modules are
`lib/core/V3*.lean`. They build on the `L = 1/2` machinery of [weil-positivity-l05.md](weil-positivity-l05.md).

## Summary

- **Theorem (Proved).** Take `0 ≤ L ≤ log 3/2` and a `C¹` function `f` with `f(u) = 0` for `|u| > L`. Suppose `f`
  lies in the subspace `V'`, that is, `∫ f(u) e^{−u/2} du = ∫ f(u) e^{u/2} du = ∫ f(u) du = 0` over `[−L, L]`
  (`V3Gen.InVp`). Then
  - `weilQg L f ≥ 4·10⁻⁴ ‖f‖²` (`V3Gen.coer_vprime`);
  - `weilQg L f > 0` for `f ≠ 0` (`V3Gen.pos_vprime`).

  The same holds on the rescaled Legendre mode sums, with `N ≥ 28` modes of each parity (`V3Main.vprime_hx`). Every
  numerical input is checked by the kernel (`decide +kernel` over `ℚ`).
- **Where it sits.**
  - `V'` is the subspace on which A. Connes and C. Consani prove archimedean positivity, at support `log 2/2`
    (Selecta Math. 27 (2021), arXiv 2006.13771).
  - Support `log 3/2` is where the prime `3` enters the prime sum: `f ⋆ f̃` lives on `[−2L, 2L]`, and `2L = log 3`.
  - Below it, only the prime `2` can contribute. At `2L = log 3` the prime `3` sits on the boundary, where the
    autocorrelation of a function supported in `[−L, L]` vanishes.
- **What the constraints do.**
  - **Even sector.** The Zhu-reduced even matrix `β*I + C3`, which leaves out the pole term, has a negative
    eigenvalue, about `−2.19`, along the constant mode. Adding `1000` times each of the two even constraints
    (`x₀ = 0`, `Σ xᵢ p̃₂ᵢ = 0`), which vanish on `V'`, raises its smallest eigenvalue to about `0.0286`.
  - **Odd sector.** The smallest eigenvalue is about `4.75·10⁻⁴`, with or without the odd constraint
    (`Σ yᵢ p̃₂ᵢ₊₁ = 0`). The odd constraint is used only to remove the pole term `2·poleR·poleL`, which vanishes
    on `V'`.

## The proof

1. **Rescaling (`V3Scale`).** Write `λ = log 3` and `f = sc g`, with `f(u) = g(u/λ)/√λ`. Then `g` is supported in
   `[−1/2, 1/2]`.
   - For `g = hx N x y`, a sum of normalised Legendre modes of both parities,
     `weilQg (λ/2) f = 2·poleR·poleL + QF3₀(x) + QF3₁(y)` (`weilQg_sc`).
   - Here `QF3_par = (1/π) ∫₀^∞ Ψ(t/λ) F_par(t)² dt`, and `Ψ` is the frequency weight of the window `1/2`.
   - Only the prime `2` enters, at `log 2/λ` (`primeS_sc`). The archimedean frequency `t` becomes `t/λ` (`arch_sc`).
2. **Zhu's reduction at `T# = 30λ` (`V3Zhu`).**
   - `Ψ(t/λ) ≥ β*` for `t ≥ 30λ` (`envelope3`), so `QF3 ≥ β*‖x‖² + xᵀ C3 x` (`QF3_ge`), with
     `C3 n m = (1/π)∫₀^{30λ} (Ψ(t/λ) − β*) T̂ₙ T̂ₘ`.
   - The tail bound uses `|T̂ₙ| ≤ b3 n = (1 + (2n+1)/4)(33/4)ⁿ/n!` on `[0, 30λ]`, which is below `10⁻²²` at `n = 56, 57`.
   - Together they give the head/tail theorem `sector_margin3`. It applies to the reduced matrix augmented by
     `μ_p p̃p̃ᵀ + μ₀e₀e₀ᵀ`, and a 28-mode head certificate bounds the form at every truncation size.
3. **The constraints in coefficients (`V3Pole`).**
   - Rodrigues' identity for the weight `e^{−au}` (`pole_mode_gen`) gives `∫ f e^{∓u/2} = √λ(Σ xᵢ p̃₂ᵢ ± Σ yᵢ p̃₂ᵢ₊₁)`,
     with `p̃ₙ = √(2n+1)·iₙ(λ/4)`.
   - At `a = 0` the same identity gives `∫ f = √λ·x₀`.
   - The even `p̃` is enclosed to `10⁻¹²` (`pole3_enc`): `iₙ` is increasing, so it suffices to bound it at the two
     rational ends of `λ/4`, with a degree-10 Taylor polynomial of `cosh`.
4. **The entries `C3` (`V3Bessel`, `V3Asm`, `V3FinD`, `V3FinP`, `V3FinA`, `V3FinR*`, `V3Enc`).** The substitution
   `t = 30λs` gives `C3 n m = (30λ/π) σₙσₘ √(2n+1)√(2m+1) ∫₀¹ wψ(30s) jₙ(15λs) jₘ(15λs) ds`.
   - **Weight side.** This is the `L = 1/2` one: the piecewise model of `wψ(30s)` with error `1.6·10⁻⁹`, and its exact
     moments `nuN`. Both are reused unchanged.
   - **Bessel side.**
     - `jₙ(X̂s)` with `X̂ = 15·l3lo` rational is a polynomial up to `10⁻¹⁸` (`jP_sX`).
     - A Lipschitz bound moves `X̂` to `15λ` (`jP_lip`); `|15λ − X̂| ≤ 1.5·10⁻¹⁹`.
   - **Entry bound.** The rational entry bound `R3e` adds the Taylor, rounding and model errors. It also brackets
     `30λ/π` between the rational bounds of `log 3` (`V3Log`, to `10⁻²⁰`) and of `π`.
   - **Kernel checks.** They cover the upper triangle of both 28×28 heads: every entry lies within `3·10⁻⁹` of its
     centre, the largest bound being `2.86·10⁻⁹` (`c3Enc_even`, `c3Enc_odd`).
5. **Certificates (`V3Main`).** The centre matrices are `β̂I + μ_p p̂p̂ᵀ + μ₀e₀e₀ᵀ + ĉ`, with exact LDLᵀ certificates
   of `A − δI` checked in the kernel (`even_chk3`, `odd_chk3`).
   - **Even sector.** `μ_p = μ₀ = 1000` and `δ = 1/40`, giving margin `1/50` (`even_sector`).
   - **Odd sector.** No multiplier, `δ = 4.5·10⁻⁴`, giving margin `4·10⁻⁴` (`odd_sector`).
   - **Head tolerance.** It is `ρ = 10⁻⁸`: `β*` to `10⁻¹²`, `1000·5·10⁻¹²` from the pole vector, the entries
     to `3·10⁻⁹`, and the rounding of the certificate.
   - **Assembly.** On `V'` the multiplier terms vanish, and the two sectors combine to give `vprime_hx`.
6. **Every test function and every `L ≤ log 3/2` (`V3Gen`).**
   - **Smaller supports.** For `L ≤ L* = log 3/2`, the form and the three functionals of `f` are those at `L*`
     (`weilQg_shrink`).
   - **Approximation.** Write `f = sc g`. `WeilGen.approx` gives cut polynomials `gₖ → g`, uniformly bounded and
     uniformly Lipschitz inside `[−1/2, 1/2]`; each is a mode sum.
   - **Projection onto `V'`.** Subtract `c₀T₀ + c₁T₂ + c₂T₁`. The coefficients are linear in the three functionals of
     `gₖ`, and the result is in `V'` (`corr_V`).
   - **Limit.** The functionals of `gₖ` tend to those of `g`, which vanish, so the coefficients tend to `0`. The
     rescaled form is continuous along such sequences (`tendsto_weilQg_sc`): the archimedean term is dominated by
     `B(M+B)/λ·8e^{−u/4}`.

## Precision and cost

The certificate needs much less precision than it gets.

- **What the margins need.** The odd margin `4.75·10⁻⁴` over 28 modes leaves an entry budget of about `10⁻⁵`.
- **What the enclosure gives.** The `L = 1/2` weight model and moments come for free, and only the Bessel coefficients
  are new, so the entries come out to `3·10⁻⁹`.
- **Kernel checks.**
  - **Entries.** The four modules `V3FinRe0`, `V3FinRe1`, `V3FinRo0` and `V3FinRo1` take about 6–7 minutes and
    2.3–3.0 GiB each. They are marked `-- heavy:`, so `scripts/build.sh` runs at most two of them at once.
  - **Bessel data.** The checks in `V3FinP` take under a minute.
  - **Certificates.** The checks in `V3Main` take about a minute.
- **Generator.** `scripts/positivity/v3gen.py --emit` regenerates every data module in exact rational arithmetic and
  checks every bound before writing. Its inputs are `CmMomData.nuN`, `CmData.sqb` and `WeilHead.EvenQ.bq`. The
  outputs are `V3FinD` (Bessel coefficients, error bounds, entry centres), `V3FinR*` and `V3CertD`.

## Beyond log 3/2 (Numerical)

These are double-precision and mpmath computations, not certified. They show what the method would give past `log 3/2`,
and why `log 3/2` is the natural end of the statement on `V'`.

**The certifiable constant.** The table below gives the smallest eigenvalue on `V'` of the reduced form (Zhu's
reduction at cutoff `T#`, every prime power with `log n < 2L` in the weight). This is the quantity a certificate like
`V3Main`'s proves. The true form's value is listed alongside. The odd sector is the smaller of the two at every
support.

| `L` | prime powers | `T#` | reduced, on `V'` (odd) | true, on `V'` (odd) |
|---|---|---|---|---|
| `log 3/2 ≈ 0.549` | 2 | 30 | `4.8·10⁻⁴` (proved: `4·10⁻⁴`) | `4·10⁻²` |
| `log 3/2` | 2 | 100 | `2.8·10⁻²` | |
| 0.56 | 2, 3 | 100 | `1.5·10⁻²` | |
| 0.60 | 2, 3 | 150 | `2.9·10⁻³` | `3.9·10⁻³` |
| 0.65 | 2, 3 | 150 | `1.5·10⁻⁴` | `2.3·10⁻⁴` |
| `log 2 ≈ 0.693` | 2, 3 (4 on the boundary) | 150–250 | `8–10·10⁻⁶` | |
| 0.70 | 2, 3, 4 | 200 | `5.0·10⁻⁶` | `7.7·10⁻⁶` |
| 0.75 | 2, 3, 4 | 300 | `7.9·10⁻⁸` | |
| 0.80 | 2, 3, 4 | 300 | `8.5·10⁻¹⁰` | `1.3·10⁻⁹` |

**What the numbers show:**

- **Decay.** The constant falls roughly like `exp(−8.8·e^{2L})`, a factor of ten for every `0.03`–`0.05` in `L`. The
  true form stays positive on `V'` throughout, as RH predicts, down to about `10⁻²⁰` at `L = 1`.
- **The cutoff 30 is what limits the proved constant.** With `T# = 100` the same statement at `log 3/2` would give about
  `3·10⁻²` instead of `4·10⁻⁴`. Past `log 3/2` the cutoff must grow anyway:
  - `β* = log(T#/2π) − 1/T# − Σ 2Λ(n)/√n` must stay positive;
  - the coefficients are `0.98` for `2`, `1.27` for `3`, `0.69` for `4` and `1.44` for `5`;
  - so `β* ≈ 0.5` needs `T# ≈ 30` with `2` alone, `≈ 100` once `3` enters, `≈ 200` once `4` enters and `≈ 850` once
    `5` enters at `L = log 5/2 ≈ 0.805`.
- **The margin on `V'` is set by the next eigenvalue of the full form.** By interlacing it is at most `λ₃` in the even
  sector, where `V'` removes two directions, and at most `λ₂` in the odd sector, where it removes one. In practice it
  is within a factor of about 3 of them.

  | `L` | even `λ₁, λ₂, λ₃` | odd `λ₁, λ₂` |
  |---|---|---|
  | 0.55 | `6·10⁻⁸, 1.6·10⁻³, 0.69` | `1.7·10⁻⁵, 9.3·10⁻²` |
  | 0.60 | `2·10⁻⁹, 1.2·10⁻⁴, 0.24` | `7·10⁻⁷, 1.0·10⁻²` |
  | 0.65 | `4·10⁻¹¹, 4·10⁻⁶, 3.8·10⁻²` | `2·10⁻⁸, 6·10⁻⁴` |
  | 0.70 | `5·10⁻¹³, 1·10⁻⁷, 2.0·10⁻³` | `3·10⁻¹⁰, 2·10⁻⁵` |
  | 0.80 | `2·10⁻¹⁷, 1·10⁻¹¹, 8·10⁻⁷` | `2·10⁻¹⁴, 3·10⁻⁹` |

  At `log 3/2` the eigenvalues that `V'` leaves are large, which is why `V'` works so well there. Past about
  `0.62`–`0.65` the odd constraint of `V'` no longer binds. Without it, the reduced matrix has the same odd minimum:
  `9.9·10⁻⁴` against `9.7·10⁻⁴` at `0.62`, and equal at `0.70`. That matrix leaves out the pole term, which `V'` kills;
  `v3past.py` prints both values.
- **So the picture holds only near the first prime.** There, the low spectrum is one channel per sector, and the three
  constraints of `V'` remove it. Each new prime power brings further near-null directions. Past `log 3/2`, positivity on
  `V'` stays true but carries a constant that falls as fast as the full form's next eigenvalue.

**Reproducing the tables.**

- `python3 scripts/positivity/v3past.py 64 0.6:150 0.65:150` computes the reduced values.
- `python3 scripts/positivity/v3beyond.py 48 40 0.6 0.65` computes the true values and the full-form eigenvalues, with
  `hpcore`'s high-precision form.

**What an extension would cost.**

- **A longer weight model.** It would cover a range three to eight times longer, with Bessel polynomials of two to three
  times the degree. The `L = 1/2` model reused here could no longer serve.
- **A larger head.** It would need about 64 modes per parity instead of 28, because the tail bound `b3` is crude.
- **Tighter entries.** They would need to be accurate to about `3·10⁻⁷` at `log 2`.

It would be the first kernel-checked case in which two primes interact. It would not bear on RH, which needs every `L`.

## Scope

This is Weil's form on `V'`, at supports up to `log 3/2`.

- The certificate uses the even constraints. Whether the form is positive at this support without them is not
  addressed here.
- Past `log 3/2`, the prime `3` enters and the argument stops.
- Nothing here bears on RH directly.
