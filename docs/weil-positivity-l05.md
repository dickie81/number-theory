# Weil positivity at half-support 1/2

Labels: **Proved** (Lean, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only) and **Numerical**
(floating point or mpmath, not certified). Contributed with AI assistance (Grok Bot). This note and its modules were
split out of the `positivity-search` branch.

## Summary

Take test functions `f` supported in `[−1/2, 1/2]` in log scale. Then `f∗f̃` is supported in `[−1, 1]`, so the
prime `2` enters the prime sum of Weil's form (`log 2 < 1 < log 3`).

- **Positivity (Proved).** For every `C¹` function `f` on `ℝ` with `f(u) = 0` for `|u| > 1/2`:
  - `weilQg (1/2) f ≥ 10⁻⁸‖f‖²` (`WeilGen.coer`), and `weilQg (1/2) f > 0` for `f ≠ 0` (`WeilGen.pos`).
  - For even `f` the same holds for the library's `weilQ` (`WeilGen.coer_even`, `WeilGen.pos_even`).
  - The finite-mode versions, for both parities, are `CmFin.L05_even_uncond` and `CmFin.L05_odd_uncond`.
- **Ground state (Proved, min-max form).** `GsMain.ground_state_testFn`. There is an even test function `v` with
  `Q(v) ≤ 2·10⁻⁵‖v‖²`, and every two-dimensional span of test functions contains a nonzero `h` with
  `Q(h) ≥ 4·10⁻⁵‖h‖²`. So the lowest level is simple, even and isolated, in the min-max sense. The operator statement
  is not formalised (see the last section).
- **Relation to what was already in the library.** The conditional row "Weil positivity at small supports" of
  [formalisations/README.md](../formalisations/README.md) proves `Q(g) ≥ 2·10⁻⁸` for normalised even probes at every
  `a ≤ 0.5493`. It does so given arb enclosures that the kernel does not check (`WeilForm.CertE` and the others).
  At the single support `a = 1/2`, every numerical input here is checked in the kernel (`decide +kernel` over `ℚ`).
  So the statement is unconditional, and it covers probes of both parities. The other supports of that row stay
  conditional.
- **Scope.** This is one window length. It says nothing about other `L` or about RH.
- **Sources.** Two steps follow a 2026 preprint attributed to Zhu (arXiv 2608.24827): the reduction `QF ≥ R`
  (`WeilZhuRed`) and the archimedean identity, "Zhu's Lemma 2.5" (`WeilArch`).
  - We could not locate that preprint (November 2026), so the attribution is unverified.
  - The Lean proofs do not depend on it: both steps are proved in Lean.
- **Build cost.** The kernel checks (`CmLhChk*`, `CmMomC*`, `CmFinRe*`, `CmFinRo*`, `CmFinRp*`) are split into
  modules of a few minutes each. Together they need roughly an hour of serial kernel time and several GB of memory per
  module.

The sections below are the corresponding part of the `positivity-search` log, edited only where it pointed at
material that stays on that branch.

## Literature context

Conventions: f is supported in [−L, L] in log scale, so f∗f̃ has support [−2L, 2L] and prime powers with log n < 2L enter. This is the same as our W_L. Literature survey compiled by Grok Bot; citations checked online except where marked.

- **Weil (1952), "Sur les formules explicites…":** RH ⇔ the quadratic form is positive. Cited via Bombieri; the original wasn't rechecked.
- **Yoshida (1992), Adv. Stud. Pure Math. 21, 281–325:** positivity for small support, verified at 2L = log 2, i.e. L ≤ 0.347. At L ≤ 0.347 no prime enters at all, so the result is archimedean only.
- **Bombieri (2000), Rend. Lincei Mat. Appl. 11, 183–233:** the minimum is attained, Yoshida is reproved, and the number of negative eigenvalues equals half the number of off-line zeros. He calls the functional "as intractable as RH itself".
- **Connes (1999), Selecta Math. 5, 29–106:** trace formula. **Connes–Consani (2021), Selecta Math. 27, arXiv 2006.13771:** archimedean positivity via the Sonin trace, at the same support log 2 / 2. **Connes–Consani (2023), Enseign. Math. 69, arXiv 2106.01715:** the very small eigenvalues of the Weil form come from prolate functions. **Connes–Consani–Moscovici (2024), Ann. Funct. Anal., arXiv 2310.18423.** **Connes–van Suijlekom (2025), CMP, arXiv 2511.23257:** a simple, even, isolated ground state implies its transform has only real zeros. **Connes–Consani–Moscovici, "Zeta spectral triples", arXiv 2511.22755:** convergence as λ → ∞ would give RH. The open steps are a simple even ground state at every scale, and convergence.
- **Li (1997), JNT 65, 325–333; Bombieri–Lagarias (1999), JNT 77, 274–287:** Li coefficients, which are again Weil positivity. **de Branges:** Conrey–Li (arXiv math/9812166) showed his positivity condition fails for ζ. **Suzuki:** screw functions, JLMS 2023 and arXiv 2606.09096. **Groskin, arXiv 2607.02828:** an "inconclusive band" for truncated forms. **Burnol:** not checked.
- **Zhu, arXiv 2608.24827 (2026 preprint, not refereed):** uses exactly our convention. **Unverified:** a search in
  November 2026 did not find this preprint, so everything attributed to it below is as reported by the original
  survey and has not been rechecked.
  - Certified Q ≥ 8.9e-18‖f‖² for L ≤ 0.8. The true floor at L = 0.8 is about 1.7e-17.
  - Measured law: −ln λ*(L) ≈ 2π² N(T*)/ln N(T*), with T* = 2πe^{2L}. This is double-exponential decay.
  - Barrier: pointwise-envelope certificates need resolution up to T₁ = 2πe^{A_L}, which grows doubly exponentially. To go further one has to show that the phases t·log p cannot align.
  - Float64 gives spurious negative eigenvalues.

How this lines up with the work here (the float64 experiments that the original log also compared stay on the
`positivity-search` branch):

- **Parity:** Zhu certifies that the ground state is even, with the odd sector about 10³ times higher at L = 0.8. Our float64 parity split couldn't resolve that difference.
- **Open handle the literature points to:** cancellation in the prime comb, i.e. that the phases t·log p cannot all align. That is an arithmetic, Diophantine statement. A second handle is the Connes–van Suijlekom route: prove a simple, even ground state at every scale.

## High-precision Weil spectrum (mpmath, not interval-certified)

Scripts: `scripts/positivity/hpcore.py` and `hp1_run.py`; plot `hp1.png`. The convention is exactly Zhu's (arXiv 2608.24827, eq. 17):
- f is supported in [−L, L], and g = f∗f̃;
- the archimedean term is in exact time-domain form, and the prime sum has log n < 2L;
- the pole term is included, +2(∫f cosh)² for even f and −2(∫f sinh)² for odd f, with **no** pole-orthogonal projection;
- the eigenvalue is Q/‖f‖².

The basis is orthonormal sines with Zhu's mode rule K = max(48, ⌊5LT*/π⌋ + 8). The arithmetic is mpmath at 40–80 digits, with Gauss–Legendre panel quadrature.

| L | even λ₁ | Zhu Table 3 | even λ₂ | odd λ₁ |
|---|---|---|---|---|
| 0.5 | 1.05e-6 | 1.05e-6 | 2.1e-2 | 2.3e-4 |
| 0.6 | 1.82e-9 | 1.82e-9 | 1.2e-4 | 7.0e-7 |
| 0.7 | 4.99e-13 | 4.99e-13 | 1.0e-7 | 2.9e-10 |
| 0.8 | 2.270e-17 | 2.27e-17 | 1.06e-11 | 2.24e-14 |
| 0.9 | 5.91e-23 | 5.91e-23 | 1.0e-16 | 1.0e-19 |
| 1.0 | 7.97e-30 | 8.08e-30 | 3.3e-23 | 2.2e-26 |
| 1.1 | 2.76e-38 | 2.78e-38 | 2.0e-31 | 1.1e-34 |
| 1.2 | 9.90e-49 | 9.98e-49 | 1.8e-41 | 6.2e-45 |

- **Agreement with Zhu:** we reproduce Zhu's sine-basis upper bounds to 3 digits.
- **Convergence in modes:** more modes lower the value, as a Galerkin method should. At L = 0.8, 48 → 64 modes gives 2.27e-17 → 2.02e-17, heading toward Zhu's Legendre value of 1.65e-17. At L = 1.0, 81 → 105 modes gives 7.97e-30 → 7.39e-30. Every value lies inside Zhu's certified enclosure where one exists, [8.9e-18, 2.27e-17] at L = 0.8.
- **Why this differs from our earlier numbers:** those used a pole-orthogonal projection and only 40 modes, and they were float64.
- **Fake-prime controls at proper precision (even λ₁):**
  - Jitter σ = 0.05: −0.07, −0.085, −0.11, −0.49 at L = 0.5, 0.6, 0.8, 1.0.
  - p = 3 flipped: −6e-3, −0.85, −1.27 at L = 0.6, 0.8, 1.0. At L = 0.5 the result is unchanged, because 3 is not yet in range.
  - So the controls fail at O(1) as soon as the altered prime enters, while the real form stays positive at 1e-49.
- **Near-null count:** the even eigenvalues below a fixed fraction of λ₂ track N(T*), but there is no sharp "null" dimension. The spectrum is a geometric ladder: λ₁ : λ₂ : λ₃ ≈ 1 : 1e7 : 1e14 at L = 1.2.
- **Parity:** the odd sector sits 214 times higher at L = 0.5 and 6300 times higher at L = 1.2, so parity is well resolved.
- **Not done:** L ≥ 1.4 was too costly here (L = 1.4 needs 123 modes at about 110 digits). Nothing is interval-certified.

## Ground state on Connes' route (mpmath)

Script: `scripts/positivity/hp2.py`; plot `hp2.png`. Lean: `lib/core/ParityGround.lean`, theorem `parity_of_simple`. It says that for an involution P, if v ≠ 0 and Pv = c·v, then c = ±1. So a simple eigenvector of a parity-commuting form is even or odd. This is abstract linear algebra only, and uses only standard axioms.

- **The ground state is simple and even at every L tested.** λ₂/λ₁ in the even sector is 2e4, 4.7e5, 4.2e6, 1.8e7 at L = 0.5, 0.8, 1.0, 1.2, growing roughly like e^{3.4L} in log terms. λ₁(odd)/λ₁(even) is 214, 986, 2797, 6307 at the same L.
- **The ground state's transform has only real zeros.** Write ξ̂(r) = cos(rL)·P(r²)/∏(α_k² − r²). The transform's zeros are then the roots of a polynomial P of degree n − 1, together with cos zeros beyond the basis.
  - At every L in 0.5–1.2, all n − 1 roots of P are real and positive: 23, 30, 40, 53, 69 roots, with no complex or negative roots.
  - This matches the Connes–van Suijlekom theorem, since the ground state is simple and even.
- **Comparison with Ξ:** the real zeros reproduce the zeta zeros consecutively, well beyond T*.

| L | N(T*) | zeros within 1e-6 | within 1e-3 | within 0.1 |
|---|---|---|---|---|
| 0.8 | 4 | 4 | 7 | 10 |
| 1.0 | 8 | 13 | 18 | 22 |
| 1.2 | 16 | 30 | 37 | 42 |

  This is the ζ-cycle phenomenon of Connes–Consani, reproduced here from the geometric side alone, with no zero data entering the matrix.
- **Verdict:** this is a strong numerical confirmation of the Connes route's first missing step (simple, even ground state) for L ≤ 1.2. It is not a proof at any scale: there is no interval certification, and the second step (convergence of the zeros as L → ∞, which would give RH) is untouched.

## Prime-phase alignment and Zhu's barrier (float64 adequate; λ via mpmath)

Scripts: `scripts/positivity/hp3.py` and `hp3b.py`; plot `hp3.png`. We measured S(t)/A, with S(t) = Σ 2Λ(n)n^{−½} cos(t log n) and A its total weight, on t ∈ [1, T*].

- **Real primes avoid alignment better than random ones, increasingly with L.** The real maximum is 0.87, 0.73, 0.61, 0.49, 0.40 at L = 0.8, 1.0, 1.2, 1.5, 2.0. Twenty Cramér random prime sets give 0.89, 0.81, 0.79, 0.72, 0.62 (sd 0.04–0.11). At L = 2 the real value sits below every random set (minimum 0.50), about 3 sd low.
- **Kronecker test:** the best simultaneous approximation of the prime phases on [1, T*] is max‖t log p/2π‖ = 0.066, 0.134, 0.206, 0.252 at L = 0.8, 1.0, 1.2, 1.5.
- **But alignment does not track positivity:**
  - Jittered and flipped sets have similar maxima: at L = 1, 0.72 and 0.75 against real 0.73.
  - At L = 0.8 and 1.0, every Cramér set that differs from the real primes has λ_min between −0.35 and −0.93, including sets with *lower* alignment than the real primes (0.675 against 0.732 at L = 1).
  - Sets identical to the real primes give λ ≈ +1e-17. That value comes from float64-rounded inputs; the exact value is 2.27e-17.
- **Verdict:** in the range positivity cares about, it is decided by the exact arithmetic of log n and its weights, not by how close the phases come to aligning. The barrier phrase "the phases cannot align" refers to frequencies up to T₁ = 2πe^{A_L} ≫ T*, and low alignment on [1, T*] neither implies nor follows from positivity. Credit: Grok Bot numerics.

## Current status of the Weil certification at L = 1/2

**Proved unconditionally** (Lean; axioms only `propext`, `Classical.choice`, `Quot.sound`):
`CmFin.L05_even_uncond` and `CmFin.L05_odd_uncond`. For every `N ≥ 28` and every nonzero coefficient vector
supported on the first `N` Legendre modes, the repo's Weil form at `L = 1/2` is strictly positive. This holds in both
the even sector (`WeilForm.weilQ (1/2)`) and the odd sector (`WeilZhuRed.QF 1 (-1)`). All of the earlier named inputs
are now proved: β*, the pole values, the C^ψ entry enclosures `CmEnc`, ModeOrth and the archimedean identity.

**Odd and mixed probes** (`WeilOdd`, `WeilOddPos`). The library's `weilQ` is the Weil form for even probes only.
For a general real probe the correct pole term is `2 ĝ(i/2) ĝ(−i/2)`, which gives `WeilForm.weilQg`. `weilQg_hx` proves
`weilQg (1/2) (Σ xᵢ T_{2i} + Σ yᵢ T_{2i+1}) = QF 0 1 N x + QF 1 (−1) N y`, with no hypotheses. The proof uses three facts:
the Fourier transform of the mixed probe is `F₀ + iF₁`, so its spectral density is `F₀² + F₁²` and the even/odd cross
terms cancel; the pole term is `2(A + B)(A − B)`; and the parity-free versions of Wiener–Khinchin, the archimedean
identity and the prime sum hold. From this:
* `L05_odd_weilQg` gives `0 < weilQg (1/2) g` for every nonzero odd `g`.
* `L05_mixed` gives `0 < weilQg (1/2) (f + g)` for every nonzero pair, with `N ≥ 28`.
* `L05_odd_weilQ` gives `0 < weilQ (1/2) g` for odd `g`. This is weaker, because for odd `g`,
  `weilQ = weilQg + 4 poleR²`.

**Scope:** a single window length `L = 1/2` and finite mode expansions of arbitrary size. The statement says nothing
about other `L` or about RH.

**Build notes:** the kernel checks (`CmLhChk*`, `CmMomC*`, `CmFinRe*`, `CmFinRo*`) are split into modules of about
3 minutes each. Together they need roughly 1 hour of serial kernel time. Each one needs several GB of memory, so on a
16 GB machine run at most 2 of them in parallel.

## Lean certificate for finite-mode Weil positivity (`WeilCert`)

Scripts: `scripts/positivity/arbcert.py` (python-flint/arb ball arithmetic) and `certgen.py` (exact rationals).

**Lean module `lib/core/WeilCert.lean`:**
- **`pos_of_cert`, fully proved:** let C = MᵀDM + δI with D ≥ 0. If |A_ij − C_ij| ≤ ρ for all i, j and n²ρ < δ, then xᵀAx > 0 for every x ≠ 0.
- **`WeilEnclosure`, a structure:** its field `encl` is the explicit hypothesis that the true Weil-matrix entries lie within ρ of C. This is the arb claim, and Lean does not check it.
- **`L05_pos`, `L07_pos`, `L08_pos`:** positivity of the 24-mode even-sector Weil matrix at L = 1/2, 7/10, 4/5, *given* that hypothesis. The concrete checks (D ≥ 0 and n²ρ < δ) are done by `norm_num`; there is no `native_decide`.
- **Axioms:** `#print axioms` shows only propext, Classical.choice and Quot.sound.

**Enclosure (arb):**
- **Setup:** Zhu's convention (eq. 17), with modes s_k, k odd ≤ 47. The prime and pole terms are in closed form.
- **Archimedean integral:** on [η, 2L] it is computed with `acb.integral`. On [0, η] it is a Taylor series at 0, with the remainder bounded by Cauchy's estimate on |z| = R. The bound uses a ball cover of the circle, R = min(1, 7/α_max) and η = R/4.

**Margins:** the certificate has far more room than needed at every L.

| L | λ_min(mid) | δ | max arb radius | ρ | n²ρ/δ |
|---|---|---|---|---|---|
| 0.5 | 1.05e-6 | 5.3e-7 | 1.8e-30 | 1.8e-30 | 2e-21 |
| 0.7 | 4.99e-13 | 2.5e-13 | 5.5e-40 | 5.5e-40 | 1e-24 |
| 0.8 | 2.27e-17 | 1.1e-17 | 2.3e-51 | 2.4e-51 | 1e-31 |

The gap of about 2e-17 at L = 0.8 is easily reachable at 200-bit precision.

**What is not proved in Lean:**
- the arb computation, including its quadrature, Taylor remainder and Cauchy bounds;
- the explicit formula and Zhu's time-domain archimedean identity;
- the identification of A_ij with Q(s_i, s_j).

The result covers only the 24-dimensional span of the modes, so it is not positivity for every f supported in [−L, L]. Zhu's certified theorem handles the infinite-dimensional tail with a separate frequency-split argument, which isn't reproduced here. Built with Grok Bot assistance.

## Full-window tail certificate, even sector, L = 1/2 (`WeilTail`)

This section extends the finite `WeilCert` check to every truncation size, so the infinitely many modes are covered. Credit: computations and Lean by an AI assistant (Grok Bot).

**Reduction (Zhu, arXiv 2608.24827, Thm 1.1 and Lemma 3.1).** Let supp f ⊂ [−L, L], F = f̂, and T# > T₁ = 2π e^{A_L}. Then
Q(f) ≥ R(f) = 2F(i/2)² + (1/π)∫₀^{T#}(Ψ_L(t) − β*)|F(t)|² dt + β*‖f‖², where β* = log(T#/2π) − 1/T# − A_L.
The chain is as follows. Write Q as pole + archimedean − primes (eq. 17). In the frequency domain the archimedean and prime parts combine into (1/π)∫Ψ_L|F|². The envelope bound of Lemma 3.1 gives Ψ_L ≥ β* for t ≥ T#. Plancherel then turns the part with t ≥ T# into β*‖f‖² minus the integral over [0, T#].
Settings here: L = 1/2, T# = 30, A_L = 2 log 2/√2 = 0.98026… (the only prime-power term is n = 2), and β* = 0.5497288384… (arb).

**Basis.** T_n(x) = P̄_n(x/L)/√L, n even. This is an orthonormal basis of L² of the even functions on [−L, L], so it is complete in that space.
- Transform: T̂_n(t) = (−1)^{n/2} 2√(Lν_n) j_n(tL), ν_n = n + ½.
- Pole vector: p_n = 2√(Lν_n) i_n(L/2).
- Matrix entries: R_nm = β*δ_nm + 2p_n p_m + C_nm, with C_nm = (1/π)∫₀^{T#}(Ψ_L − β*)T̂_n T̂_m.

Mode index i corresponds to Legendre order 2i.

**Head (orders 0..54, 28 modes).** All 406 entries C_nm were computed with arb `acb.integral` at 256 bits, max radius 4.1e-37 (`scripts/positivity/tailcert.py`).
- λ_min of the midpoint matrix is about 2.24e-7, which is small but positive.
- Exact-rational certificate (`tailheadcert.py`): M with D ≥ 0, δ = 7/62500000, ρ = 4.87e-24, n²ρ/δ = 3.4e-13. The head margin is λ0 = δ − 28²ρ.

**Tail (orders ≥ 56).** The script `tailbounds.py` uses these bounds:
- |j_n(x)| ≤ min(1, xⁿ/(2n+1)!!) for real x ≥ 0, from the Poisson integral.
- 0 ≤ i_n(z) ≤ zⁿ cosh z/(2n+1)!!.
- M_Ψ = sup_{[0,30]}|Ψ_L − β*| ≤ 6.9376, from an arb interval cover with 6000 boxes.

These give:
- |C_nm| ≤ (M_Ψ/π)·4L√(ν_nν_m)·L^{n+m}T^{n+m+1}/((n+m+1)(2n+1)!!(2m+1)!!).
- Tail diagonal: d ≥ 0.5497 − 2·max|C_nn| (max|C_nn| ≈ 1.8e-52).
- Off-diagonal row sums: e ≤ 1e-53.
- Head–tail Frobenius coupling: c² ≤ 1e-48, using |j_head| ≤ 1.
- Margin: m = λ0/2.

The block condition c² ≤ (λ0 − m)(d − e − m) holds with about 40 orders of magnitude to spare.

Caveats on rigour:
- The scripts form the tail sums explicitly only up to order 600, and take the supremum of e over only the first 40 tail rows. Beyond that they rely on the super-exponential decay, which is obvious from the bound formula, but the scripts do not bound that remainder formally.
- The analytic Bessel inequalities are standard but are not formalised.

**Lean (`lib/core/WeilTail.lean`).** Fully proved, using only propext, Classical.choice and Quot.sound:
- `head_margin`: an entrywise certificate gives the margin δ − h²ρ.
- `tail_lower`: a symmetric Gershgorin bound.
- `coupling_sq`: Cauchy–Schwarz over the product finset.
- `block_margin`: an abstract head/tail theorem, uniform in the truncation size N ≥ h, built on `ShellSchur.margin_of_coupling`.
- Concrete data `L05Tail` (M, D, δ, ρ, d, e, c², m), checked by `norm_num`.
- `reduced_margin`: m‖x‖² ≤ xᵀR_N x for every N ≥ 28.
- `L05_even_pos`: 0 < xᵀQ_N x for every N ≥ 28 and every x ≠ 0.

The following are **named hypotheses**, not proved in Lean:
- `ZhuReduction`: Q_N dominates R_N, which is Zhu's Thm 1.1 and Lemma 3.1.
- `TailHyp`: symmetry, the arb head enclosure, and the tail bounds d, e, c² above.

**What is stated.** Positivity is stated for coefficient sequences, uniformly over all finite truncations. It is not stated for functions. To pass to every even f ∈ L²[−L, L] you need two more things, neither formalised:
- Legendre completeness, which holds;
- continuity of Q in a norm controlled by the coefficients.

Even then the conclusion is only Q ≥ 0 on the closure. The uniform margin m > 0 holds in the coefficient ℓ² norm, so the conclusion is in fact Q(f) ≥ m‖f‖² for the reduced form.

**Not done.** The odd sector (pole term −2(∫f sinh)², and odd Legendre orders) and L = 0.8 were not done. At L = 0.8, T₁ grows and T#·L ≈ 160, so the head would need about 200 modes and the arb cost is out of reach in this session.

## Closing the tail: unconditional Bessel and tail bounds, both sectors at L = 1/2 (`WeilTailB`)

This section removes the tail and weight hypotheses of `WeilTail` and adds the odd sector. Credit: an AI assistant (Grok Bot).

**Reuse from the stack.**
- `WeilForm.norm_digamma_le`: ‖ψ(z)‖ ≤ 12√(1+‖z‖) for Re z ≥ 1/4.
- `WeilTail.head_margin` and `WeilTail.block_margin`, with `ShellSchur.margin_of_coupling` underneath.
- Mathlib: `intervalIntegral.norm_integral_le_of_norm_le_const`, `Real.pow_div_factorial_le_exp`, `Real.cosh_le_cosh`, and the d9 bounds for e, log 2 and π.

Other material surveyed but not usable here:
- Mathlib has a Bessel J definition through ₀F₁ (no integral representation and no bounds) and `shiftedLegendre` polynomials (no L² completeness).
- The repo's explicit-formula modules (`WeilZeta`, `WeilCriterion`, `WeilAssemble`, …) give the explicit formula over zeta zeros for strip test functions. They contain neither Zhu's frequency-cutoff reduction nor the envelope Lemma 3.1.
- `DigammaGauss` and `KaiserZeroWeight` give digamma symmetry and an upper bound for Re ψ.

**Proved in Lean, using only the standard axioms:**
- `jP_bound`: spherical Bessel functions are defined by Poisson's integral, j_n(x) = xⁿ/(2^{n+1}n!)∫₋₁¹cos(xt)(1−t²)ⁿdt. This gives |j_n(x)| ≤ (x/2)ⁿ/n! for x ≥ 0.
- `iP_bound`: likewise |i_n(z)| ≤ 2(z/2)ⁿ/n! for 0 ≤ z ≤ 1.
  - These are weaker than xⁿ/(2n+1)!!, but that does not matter for the tail, and no |j_n| ≤ 1 bound is needed.
- `That_bound` and `pole_bound`: |T̂_n(t)| ≤ b_n on [0, 30] and |p_n| ≤ 2b_n, where b_n = (1+(2n+1)/4)(15/2)ⁿ/n!.
- `βs_ge`: β* ≥ 0.37.
- `wψ_bound`: |Ψ_L − β*| ≤ 55 on [0, 30]. Here Ψ_L = Re ψ(1/4+it/2) − log π − √2 log 2·cos(t log 2).
- Every entry satisfies |R_ij − β*δ_ij| ≤ 558·b_{2i+par}·b_{2j+par} (`Rm_entry`), and `Rm_symm` proves symmetry.
- `b_step`: b_{n+2} ≤ b_n/2 for n ≥ 20. A geometric-majorant lemma then gives, for **every** truncation size N:
  - tail row sums ≤ 558·B0·2B0;
  - tail diagonal ≥ 0.37 − 558·B0²;
  - coupling ≤ 558²·28·190269²·2B0², using b_n ≤ 29·e^{15/2} on the head;
  - where B0 = 5e-25 ≥ b_56 and b_57, checked by `norm_num`.
- `sector_margin`, `even_margin`, `odd_margin`, `L05_even_full`, `L05_odd_full`.

**Odd sector.** The basis is odd Legendre orders 1..55. The pole term enters with sign −: −2(∫f sinh(x/2))².
- arb head: max radius 5.2e-37, λ_min(mid) = 4.66e-5.
- Certificate: δ = 233/10⁷, ρ = 1.9e-24, n²ρ/δ = 6.4e-16.
- Margin: m = 1e-5.

The even sector margin is m = 5e-8.

**Final theorems.** `WeilTailB.L05_even_full` and `L05_odd_full` cover any Q : ℕ → ℕ → ℝ (the Weil form in sector Legendre coordinates). Given `ZhuRed Q par σ` and the sector head enclosure, they conclude 0 < xᵀQ_N x for every N ≥ 28 and every x ≠ 0 supported in range N.

**Hypotheses that remain:**
1. `EvenHead` and `OddHead` (**arb numerics**). These are the entrywise enclosures of the 28×28 head of the reduced matrix, computed by `tailcert.py` at 256 bits.
   - They also identify Lean's Poisson-integral j_n with arb's ₀F₁ evaluation (a classical identity).
   - They identify Re ψ with arb's half-sum of conjugate digammas (`DigammaGauss.digamma_conj`).
2. `ZhuRed` (**Zhu analytic**). This says Q_N ≥ R_N on every truncation, which is Zhu's Theorem 1.1 and envelope Lemma 3.1 written in Legendre coordinates. The quadratic form Q is abstract in Lean.
3. Coefficients versus functions (**functional analysis**). Positivity is stated for coefficient vectors of every finite size. Turning it into Q(f) > 0 for every even or odd f ∈ L²[−1/2, 1/2] requires two things, neither formalised (Mathlib lacks them):
   - L² completeness of the normalised Legendre basis;
   - continuity of Q.

**Not done.** L = 0.8 is not done; the head would need about 200 modes, which is out of reach for the arb cost.

## Zhu's reduction at L = 1/2, formalised up to two named inputs (`WeilZhuRed`)

This section works by an AI assistant (Grok Bot) and splits the earlier `ZhuRed` hypothesis into proved steps and two smaller named inputs.

**Proof chain** (Zhu, arXiv 2608.24827, eq. 17, Lemma 2.5, Lemma 3.1, Thm 1.1), for supp f ⊂ [−L, L], g = f⋆f̃, ĝ = |F|²:
1. Frequency form. Since g(x) = (1/π)∫₀^∞|F|²cos(tx)dt, the prime term becomes −(1/π)∫₀^∞|F|²Σ_{log n<2L}2Λ(n)n^{−1/2}cos(t log n). Lemma 2.5 writes the archimedean term as (1/π)∫₀^∞(Re ψ(1/4+it/2) − log π)|F|². Together, Q(f) = pole + (1/π)∫₀^∞Ψ_L|F|².
2. At L = 1/2 only n = 2 has log n < 1, so Ψ_L(t) = Re ψ(1/4+it/2) − log π − √2 log 2·cos(t log 2).
3. Envelope (Lemma 3.1): Ψ_L(t) ≥ β* for t ≥ T#.
4. Split at T#. Use Ψ_L ≥ β* on (T#, ∞) and Plancherel ∫₀^∞|F|² = π‖f‖². This gives Q ≥ pole + (1/π)∫₀^{T#}(Ψ_L − β*)|F|² + β*‖f‖² = R.

**Proved in Lean (standard axioms only):**
- `primes_L05`: Λ(n) ≠ 0 and log n < 1 imply n = 2.
- `prime_coeff_L05`: 2Λ(2)/√2 = √2 log 2.
- `envelope`: Ψ_L(t) ≥ β* for all t ≥ 30. This reuses the vendored vertical-line Stirling bound `Zeta23.StirlingVert.re_digamma_stirling'`, |Re ψ(a+it) − log|t|| ≤ 5/t² for 0 < a ≤ 1 and |t| ≥ 1/2. The proof is: Re ψ(1/4+it/2) ≥ log(t/2) − 20/t² ≥ log(t/2) − 1/30, and log(t/2) − log π ≥ log(30/2π).
- `QF_ge_R`: R_N(x) ≤ QF_N(x) for every truncation size N and every x. This is steps 3–4 done exactly in Lean: the set-integral split at 30, monotonicity on (30, ∞), the finite-sum expansion, and identifying the [0, 30] piece with the matrix C.
- `zhuRed_of`: `FreqRep` and `ModePlancherel` together imply `ZhuRed`.
- `L05_even` and `L05_odd`: positivity of the Weil form.
- `QF_even_pos` and `QF_odd_pos`: positivity of the frequency form, assuming only `ModePlancherel` and the arb head.

**Named inputs that remain:**
- `ModePlancherel par` (**functional analysis**):
  - (1/π)∫₀^∞T̂_nT̂_m = δ_nm within a sector, which follows from Legendre orthonormality plus Plancherel;
  - integrability of T̂_nT̂_m and Ψ_L·T̂_nT̂_m on (0, ∞).
  - Mathlib has the L² Fourier transform (`Analysis/Fourier/LpSpace`), but bridging it to these Poisson-integral modes, and the 1/t decay needed for integrability, are not done.
- `FreqRep Q par σ` (**Zhu analytic**): the Weil functional (pole + archimedean − primes) equals the frequency form QF on sector modes. This is step 1, i.e. Lemma 2.5 and the cosine expansion of g.
  - The repo's explicit-formula modules (`weilExplicit_*` in `WeilZeta`, `WeilCriterion`, `WeilAssemble`) work with strip-class test functions over zeta zeros. They do not express the archimedean term as a digamma integral against |F|² for compactly supported f, so this bridge is not formalised.
  - `primes_L05` already settles the arithmetic part of step 1.
- `EvenHead` / `OddHead` (**arb numerics**): unchanged.
- Coefficients versus functions (**functional analysis**): unchanged; positivity is stated on coefficient vectors.

## Plancherel inputs and the repo's Weil form on Legendre modes (`WeilPlanch`)

This section's work was done by an AI assistant (Grok Bot).

**Sign correction.** `WeilTailB.That` now carries the factor (−1)^{⌊n/2⌋}. This is the real part of iⁿ in the Legendre–Fourier identity, and it is the convention the arb head computation uses. Without it, the Lean matrix differed from the arb matrix by signs on the entries with i + j odd, so `EvenHead`/`OddHead` as stated would not have matched the numerics. All bounds are unaffected, because they only use |T̂ₙ|.

**What the repo provides.**
- `WeilForm.weilQ a g` (in `Roadmap`) is the concrete time-domain Weil form. It consists of:
  - the pole term 2(∫g e^{−u/2})²;
  - the archimedean part (Re ψ(1/4) − log π)‖g‖² + ∫₀^∞[g⋆g(0) − g⋆g(u)]e^{u/2}/sinh u du;
  - the prime sum −2ΣΛ(n)n^{−1/2}g⋆g(log n).
- It is defined for any real g and is the right form for even g. The `Probe` class adds evenness, support, L² and convergence of the archimedean integral. The strip class `StripTest` (analyticity of ĝ² on |Im| < 1 with 1/(1+Re²) decay) is only used to tie the form to zeta zeros, and is not needed here.
- The Legendre functions T_n(u) = √(2n+1)·P̃_n(u + 1/2) on [−1/2, 1/2] are built from Mathlib's `shiftedLegendre`.

**Proved (standard axioms only):**
- `Psi_cont` and `That_cont`: continuity, using the stack's `differentiableOn_digamma` and Mathlib's parametric-integral continuity.
- `Psi_growth`: |Ψ_L(t)| ≤ 21√(1+t), from `norm_digamma_le`.
- `modePlancherel_of`: `ModePlancherel` follows from `ModeDecay` and `ModeOrth`. Integrability of T̂ₙT̂ₘ and Ψ_L·T̂ₙT̂ₘ on (0, ∞) is proved using the majorant K(1+|t|)^{−3/2} (Mathlib's `integrable_one_add_norm`).
- `prime_sum_L05`: the repo's full prime series for f = Σxᵢ T_{2i} equals its n = 2 term. The autocorrelation vanishes for |u| > 1, and log n > 1 for n ≥ 3.
- `weilQ_eq_QF`: weilQ(1/2)(f) = QF(x), given the bridge below. This uses the integral split Ψ_L = (Re ψ − log π) − √2 log 2·cos(t log 2) and 2Λ(2)/√2 = √2 log 2.
- **Final theorem `L05_even_weilQ`:** for N ≥ 28 and x ≠ 0, 0 < weilQ(1/2)(Σ_{i<N} xᵢ T_{2i}).
- **Odd sector `L05_odd_QF`:** positivity of the frequency form. The repo's `weilQ` covers only even g (its pole term has the even sign).

**Named inputs left:**
- `EvenHead` / `OddHead` — arb numerics.
- `ModeDecay` — special functions: |T̂ₙ(t)| ≤ Cₙ/(1+t), i.e. jₙ(x) = O(1/x).
- `ModeOrth par` — functional analysis: (1/π)∫₀^∞ T̂ₙT̂ₘ = δₙₘ. This follows from:
  - the Legendre–Fourier identity ∫₋₁¹Pₙe^{ixt} = 2iⁿjₙ(t);
  - Legendre orthonormality;
  - Plancherel, which Mathlib has only as an abstract L² isometry, not linked to the integral formula for L¹ ∩ L² functions.
- `EvenBridge.pole` — special functions: ∫₋₁¹Pₙ(x)e^{ax}dx = 2iₙ(a).
- `EvenBridge.arch` — Zhu analytic (Lemma 2.5): the archimedean distribution in |F|² form.
- `EvenBridge.acorr` — Fourier: f⋆f(log 2) = (1/π)∫₀^∞cos(t log 2)F². This is Wiener–Khinchin, reachable from Mathlib's `Continuous.fourierInv_fourier_eq` once `ModeDecay` makes F² integrable, but not formalised here.
- Odd sector — Zhu analytic: a concrete odd Weil form, with pole −2(∫f sinh)², is not in the repo, so the odd statement remains about the frequency form.

## Rodrigues integration by parts: mode decay and the pole identity (`WeilModes`)

This work was done by an AI assistant (Grok Bot).

**Core identity (`rod_ibp`).** Write P̃ₙ for Mathlib's shifted Legendre polynomial and W = yⁿ(1−y)ⁿ. For every complex c,

  n!·∫₀¹ e^{cy}P̃ₙ(y) dy = (−c)ⁿ ∫₀¹ e^{cy} yⁿ(1−y)ⁿ dy.

The proof combines three ingredients:
- Mathlib's Rodrigues formula `factorial_mul_shiftedLegendre_eq`, n!P̃ₙ = Dⁿ W.
- Vanishing of DʲW at 0 and 1 for j < n, from `pow_sub_dvd_iterate_derivative_of_pow_dvd`.
- n integrations by parts using `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.

**`pole_bridge` (closes `EvenBridge.pole`).** Take c = −1/2. Substitute s = 2y − 1, and use the symmetry W(1−y) = W(y) to replace cosh by a single exponential. This gives

  ∫_{−1/2}^{1/2} T_n(u)e^{−u/2} du = √(2n+1)·iₙ(1/4) = pₙ

for the repo's `legT` and the Poisson-defined iₙ, for every n. Summing over modes gives `poleR (fx N x) (1/2) = Σ xᵢ p_{2i}`.

**`modeDecay` (closes `ModeDecay`).**
1. With c = ±2ix, `cos_split` writes the Poisson integral as a combination of E(±2ix) = ∫₀¹e^{±2ixy}W.
2. `rod_ibp` turns each into n!/(2x)ⁿ times a Legendre–Fourier integral.
3. One more integration by parts (`ibp_bound`) bounds that integral by K/(2x), with K = |P̃ₙ(1)| + |P̃ₙ(0)| + sup_{[0,1]}|P̃ₙ'|. The supremum comes from compactness.
4. The powers of x cancel exactly: `jP_decay` gives |jₙ(x)| ≤ K/(2x) for x > 0.
5. Combined with |jₙ(x)| ≤ 1 for x ≤ 1, this gives |T̂ₙ(t)| ≤ Cₙ/(1+t) for every n.

**Final theorems.**
- `WeilModes.L05_even_final` concludes 0 < `weilQ (1/2)` applied to Σ_{i<N} xᵢT_{2i}, for N ≥ 28 and x ≠ 0. Its inputs are:
  - `EvenHead` (arb numerics);
  - `ModeOrth 0` (functional analysis);
  - `EvenBridge2.arch` (Zhu analytic, Lemma 2.5);
  - `EvenBridge2.acorr` (Fourier / Wiener–Khinchin at log 2).
- `L05_odd_final` concludes positivity of the odd frequency form. Its inputs are `OddHead` and `ModeOrth 1`.

**Notes.**
- Mathlib's shifted Legendre polynomial satisfies P̃ₙ(y) = Pₙ(1 − 2y). So `legT n` is the reflected Legendre function, and equals the usual one only for even n. The even sector uses only even n.
- `EvenBridge2.acorr` and `ModeOrth` remain. Both need Fourier inversion and Plancherel for the Legendre modes, and the autocorrelation-transform identity. Mathlib's L² Fourier isometry is not linked to the integral transform of L¹∩L² functions, and that bridge is not formalised here.

## Fourier bridge: Legendre orthonormality, the Legendre–Fourier identity and Parseval (`WeilFourier`)

This work was done by an AI assistant (Grok Bot).

The link from Mathlib's Fourier theory to the repo's mode transforms is built without abstract L². It uses Mathlib's pointwise Fourier inversion (`Integrable.fourierInv_fourier_eq`, which needs only continuity at the point) and its convolution theorem (`Real.fourier_mul_convolution_eq`).

**What is proved.**
- `beta_nat`: ∫₀¹ yᵃ(1−y)ᵇ = a!b!/(a+b+1)!, by induction with integration by parts.
- `sL_orth`: ∫₀¹ P̃ₘP̃ₙ = δₘₙ/(2n+1). It uses Rodrigues and n integrations by parts with polynomial weights. Dⁿ kills P̃ₘ for m < n, and DⁿP̃ₙ = n!(−1)ⁿC(2n,n).
- `legT_orth`: ∫_ℝ T_n T_m = δₙₘ for the repo's `legT`.
- `parseval`: let f and g be cut-offs to [−1/2, 1/2] of continuous functions. Suppose 𝓕f(ξ)·𝓕g(−ξ) = S(2πξ), where S is continuous, even and O((1+t)⁻²). Then ∫ f(t)g(t−v) dt = (1/π)∫₀^∞ cos(tv) S(t) dt for |v| < 1. The proof has four parts:
  - the correlation is a Mathlib convolution;
  - its transform is the product;
  - it is continuous for |v| < 1, written as a parametric integral with moving endpoints;
  - inversion is applied at v.
- `LF` (Legendre–Fourier identity, Mathlib normalisation 𝓕f(ξ) = ∫e^{−2πivξ}f(v)dv): 𝓕Tₙ(ξ) = iⁿ√(2n+1) jₙ(πξ). Equivalently, `LF_sec` gives 𝓕T_{2i+p}(ξ) = i^p·T̂_{2i+p}(2πξ). The proof uses `rod_ibp` at c = −2πiξ, the Poisson form of jₙ, and the symmetry E(c) = e^c E(−c).
- `modeOrth` closes `ModeOrth 0` and `ModeOrth 1`: (1/π)∫₀^∞ T̂ₐT̂_b = δ within each parity sector. The per-mode factors i^p cancel against the parity (−1)^b of T̂_b(−t). So the sign of the reflected odd `legT` does not matter, and the statement is about the same T̂ₙ (including the (−1)^⌊n/2⌋ factor) used by the arb head matrices.
- `acorr` closes `EvenBridge2.acorr`. It takes v = −log 2 in `parseval` with f = g = Σ xᵢT_{2i}.

**Final theorems.**
- `WeilFourier.L05_even` proves 0 < `weilQ (1/2)` applied to Σ_{i<N} xᵢT_{2i}, for N ≥ 28 and x ≠ 0. Its only inputs are `EvenHead` (arb numerics) and `ArchBridge`, the archimedean identity of Zhu's Lemma 2.5.
- `WeilFourier.L05_odd` proves positivity of the odd frequency form `QF 1 (−1)`. Its only input is `OddHead`.
- Axioms: propext, Classical.choice, Quot.sound only.

**What remains.**
- `EvenHead` and `OddHead`: arb interval numerics, not checked inside Lean.
- `ArchBridge`: Zhu's Lemma 2.5, the digamma/archimedean identity.
- The odd sector is stated for the frequency form. It is not yet tied to `weilQ` on odd functions.
- The result is for finite coefficient vectors (every N ≥ 28). It is not stated for general L² functions on [−1/2, 1/2].

## The archimedean identity (Zhu's Lemma 2.5) proved (`WeilArch`)

This work was done by an AI assistant (Grok Bot).

**What `ArchBridge` asserts.** Write f = Σ_{i<N} xᵢT_{2i}, h = f⋆f̃ for its autocorrelation, and F = Σ xᵢT̂_{2i}. Then

  (Re ψ(1/4) − log π)·‖f‖² + ∫₀^∞ (h(0) − h(u)) e^{u/2}/sinh u du = (1/π)∫₀^∞ (Re ψ(1/4 + it/2) − log π)·F(t)² dt.

**Proof.**
1. **Kernel identity (`kerD`).** Take the repo's Gauss integral `digamma_sub_eq_integral` with z = 1/4 + it/2 and w = 1/4. Take real parts and substitute x = 2u. This gives

   Re ψ(1/4 + it/2) − ψ(1/4) = ∫₀^∞ (1 − cos tu)·e^{u/2}/sinh u du,

   with the integrand integrable for every t.
2. **Wiener–Khinchin at every lag (`acorr_gen`).** h(v) = (1/π)∫₀^∞ cos(tv)F(t)² dt for |v| ≠ 1. To get this, `parseval` and the correlation-continuity lemma were extended from |v| < 1 to |v| ≠ 1, using the fact that h vanishes identically for |v| > 1. The single point u = 1 is a null set, which is enough for the u-integral.
3. **Fubini.** The product integrand F(t)²(1 − cos tu)·e^{u/2}/sinh u is non-negative on (0,∞)². Its iterated integral is ∫ D·F², which is integrable by the Psi-integrability already proved in `WeilPlanch`. So `integrable_prod_iff` gives integrability, and the order of integration can be swapped.
4. **Assembly.** The constant part uses ‖f‖² = h(0) = (1/π)∫F².

**Final theorem.** `WeilArch.L05_even` proves 0 < `weilQ (1/2)` applied to Σ_{i<N} xᵢT_{2i}, for N ≥ 28 and x ≠ 0. Its only input is `EvenHead`, the arb head certificate. Axioms: propext, Classical.choice, Quot.sound.

**What remains.**
- `EvenHead` and `OddHead`: arb numerics, not checked inside Lean.
- The odd sector is stated for the frequency form only.
- The result is for coefficient vectors, not for general functions on [−1/2, 1/2].

## Head certificates checked in the Lean kernel; residual enclosure families (`WeilHead`)

This work was done by an AI assistant (Grok Bot).

**What `EvenHead`/`OddHead` assert.** For i, j < 28,

  |R_ij − C_ij| ≤ ρ.

- R is the reduced Zhu matrix, R_ij = β*·δ_ij + 2σ·p_{2i+par}·p_{2j+par} + C^ψ_{2i+par,2j+par}, where C^ψ_nm = (1/π)∫₀³⁰ (Ψ_L − β*)·T̂ₙT̂ₘ.
- C = MᵀDM + δI is the exact-rational LDLᵀ certificate.
- ρ is about 5·10⁻²³.

**What is now proved.**
- The certificate data M and D in `WeilTail`/`WeilTailB` are now stored as exact rationals (`List (List ℚ)`), and the real matrices are their casts. Non-negativity of D is checked by kernel evaluation.
- `even_chk` / `odd_chk` check, by kernel evaluation over ℚ with `decide +kernel` (no `native_decide`), that |A_ij − C_ij| ≤ ρ − 12ε for all 784 entries. Here A = b̂·I + 2σp̂p̂ᵀ + ĉ is the rational centre matrix and ε = 10⁻³⁰. Each check takes about 25 s.
- `Rm_near` is interval algebra: the three family enclosures give |R_ij − A_ij| ≤ 12ε, using |p̂| ≤ 2, which is also kernel-checked.
- `evenHead_of` / `oddHead_of` derive `EvenHead` / `OddHead` from `HeadEnc`.
- `WeilHead.L05_even` proves 0 < `weilQ (1/2)` applied to Σ xᵢT_{2i}, and `WeilHead.L05_odd` proves positivity of the odd frequency form. Their only input is `HeadEnc`.
- Axioms: propext, Classical.choice, Quot.sound.

**The residual hypothesis `HeadEnc`.** It consists of arb enclosures at ε = 10⁻³⁰, produced by `scripts/positivity/headsplit.py` (actual radii ≤ 4·10⁻³⁴), in three families:
1. `beta`: |β* − b̂| ≤ ε, where β* = log(30/2π) − 1/30 − √2 log 2.
2. `pole`: |p_{2i+par} − p̂ᵢ| ≤ ε for i < 28, where p_n = √(2n+1)·iₙ(1/4).
3. `cm`: |C^ψ_{2i+par,2j+par} − ĉᵢⱼ| ≤ ε for i, j < 28.

**Why these families remain.** The certificate leaves room for n²ρ < δ ≈ 10⁻⁷, so every entry must be known to about 10⁻¹⁰ (the present data use 10⁻²³). The three families fall short for different reasons:
- **`cm`** is the real obstruction. It needs verified quadrature, inside Lean, of the complex digamma along Re s = 1/4 against oscillatory Bessel products on [0, 30]. That means enclosures of ψ(1/4 + it/2) on a fine grid (Stirling with remainder, available in the stack only as an O-bound), plus error control for the quadrature. None of this machinery exists in Lean or Mathlib.
- **`pole`** is reachable in principle. iₙ(1/4) has a rapidly convergent series, and √(2n+1) admits rational enclosures. It is left as a hypothesis because it does not change the conditional status while `cm` remains.
- **`beta`** needs log π, log 15 and √2 log 2 to about 10⁻¹⁰ or better. Mathlib provides π to 20 digits but log 2 only to 10, so further series bounds would be needed. It is left for the same reason as `pole`.

## Robust head certificates: crude entry tolerances (`WeilHead`, revised)

This work was done by an AI assistant (Grok Bot).

**Smallest eigenvalues of the 28×28 reduced head matrices** (arb midpoints, high-precision `eigsy`; uncertified):

| Sector | λ_min(R), 28 modes | Next eigenvalue | λ_min of leading 4 / 6 / 8 / 10 modes |
|---|---|---|---|
| Even | 2.2425·10⁻⁷ | 7.75·10⁻³ | 2.2·10⁻⁶ / 3.3·10⁻⁷ / 2.248·10⁻⁷ / 2.2425·10⁻⁷ |
| Odd | 4.6591·10⁻⁵ | 0.2346 | 1.9·10⁻⁴ / 4.68·10⁻⁵ / 4.662·10⁻⁵ / 4.6591·10⁻⁵ |

In each sector the bottleneck is a single near-null direction carried by the first 8–10 modes.

**Sharper head bound.** `WeilTail.head_margin` now loses h·ρ instead of h²·ρ. The proof bounds |xᵀEx| ≤ ρ(Σ|xᵢ|)² ≤ hρ‖x‖² by Cauchy–Schwarz. So an entrywise error ρ costs 28ρ, a Gershgorin-type loss.

**New certificates.** `L05Even2` and `L05Odd2` in `WeilTailB` are built as follows:
- δ ≈ 0.9·λ_min.
- The LDLᵀ factor of A − δI is rounded to 2⁻⁶⁴.
- The tolerance ρ satisfies 28ρ ≤ δ − m.

| Sector | δ | ρ | Final margin m | max \|A − MᵀDM − δI\| (kernel-checked bound) |
|---|---|---|---|---|
| Even | 2·10⁻⁷ | 6.7·10⁻⁹ | 10⁻⁸ | 10⁻¹⁸ (≤ 6.9·10⁻¹⁰) |
| Odd | 4.2·10⁻⁵ | 1.4·10⁻⁶ | 2·10⁻⁶ | 1.4·10⁻¹⁸ (≤ 9.9·10⁻⁸) |

The tail and coupling budget is negligible (B₀ ≈ 5·10⁻²⁵), so almost all of δ − 28ρ is available as margin.

**Tolerances now demanded by `HeadEnc`:**

| Sector | ε_β | ε_p | ε_c |
|---|---|---|---|
| Even | 10⁻¹² | 10⁻¹² | 6·10⁻⁹ |
| Odd | 10⁻¹⁰ | 10⁻¹⁰ | 1.3·10⁻⁶ |

The check is kernel-evaluated over ℚ: |A − C| ≤ ρ − (ε_β + 10ε_p + ε_c). Axioms: propext, Classical.choice, Quot.sound.

**Can ε grow further?**
- With 28 head modes, ε_c < λ_min/28 is the ceiling for an entrywise bound. That is about 8·10⁻⁹ (even) and 1.7·10⁻⁶ (odd).
- Shrinking the head to 10 modes would keep λ_min and gain a factor of about 3. But the tail bound b(n) = (1 + (2n+1)/4)(15/2)ⁿ/n! is about 0.1 at n = 20, so the current geometric tail estimate could not absorb modes 10–27. It would need sharper, explicit Bessel decay.
- A structured perturbation bound could tolerate larger errors in the high modes, where the eigenvector is negligible. One example is a weighted Schur bound with weights following the eigenvector.

**Is `cm` now provable in Lean? Not yet.** Even 10⁻⁶ absolute accuracy for (1/π)∫₀³⁰ wψ·T̂ₙT̂ₘ needs three things:
1. Rigorous pointwise enclosures of Re ψ(1/4 + it/2) to about 10⁻⁷. The stack has Stirling only with an O-type remainder, and the crude bound |ψ| ≤ 12√(1+|z|).
2. Derivative bounds for the quadrature error. These need polygamma bounds, which Mathlib does not have.
3. A quadrature fine enough for the target. A Lipschitz rule would need about 10¹⁰ nodes. A midpoint rule with a second-derivative bound would need about 10⁵–10⁷ nodes, each needing a digamma and a Bessel enclosure. That is out of reach for kernel evaluation.

A realistic route is Taylor models (degree about 10 on about 100 subintervals), with proved remainders for ψ (via the Gauss integral or the series ψ(z) − ψ(1) = Σ(1/(k+1) − 1/(k+z)) with explicit tail) and for jₙ (via the Poisson integral). This is a substantial separate project.

The other two families are within reach:
- **`pole`** (10⁻¹⁰–10⁻¹²): iₙ(1/4) has a rapidly convergent power series, with rational square-root enclosures for √(2n+1).
- **`beta`**: π is known to 20 digits in Mathlib, and log 2, log 3 and log 5 follow from Mathlib's `Real.abs_log_sub_add_sum_range_le` series bounds.

## WeilConst: β* and pole values proved; only C^ψ remains

`lib/core/WeilConst.lean` proves two of the three `HeadEnc` families outright (contributed with AI assistance (Grok Bot)).

- **β\*** (`beta_enc_even`, `beta_enc_odd`): |β\* − b̂| ≤ 10⁻¹². The proof uses Mathlib's 20-digit bounds on π, the `log(1−x)` series remainder `Real.abs_log_sub_add_sum_range_le` (50 terms for log 2, 25 terms for log(15/(4π)) at both π endpoints), and rational bounds on √2. A `decide +kernel` check over ℚ confirms the resulting interval.
- **Poles** (`pole_enc_even`, `pole_enc_odd`): |p_{2i+par} − p̂ᵢ| ≤ 10⁻¹² for i < 28.
  - The moments J(k,n) = ∫₋₁¹ t^{2k}(1−t²)ⁿ satisfy J(k,0) = 2/(2k+1) and J(k,n+1) = J(k,n) − J(k+1,n). A kernel-evaluated list recursion computes them exactly.
  - cosh(t/4) is replaced by its degree-10 Taylor polynomial, with remainder ≤ 4⁻¹²·13/(12!·12) from `Real.exp_bound`.
  - The √(2n+1) factor is handled by comparing squares.
- **Narrowed residual**: `WeilConst.L05_even` and `WeilConst.L05_odd` now take only `CmEnc par cq εc`. That is the entrywise enclosure of C^ψ_{nm} = (1/π)∫₀³⁰ wψ T̂ₙT̂ₘ, with εc = 6·10⁻⁹ for even and 1.3·10⁻⁶ for odd. Axioms: propext, Classical.choice, Quot.sound.

C^ψ is still open because it needs rigorous enclosures of Re ψ(1/4 + it/2) on [0, 30] and a validated quadrature of an oscillatory integrand. Proposed plan:
1. Shift ψ by recurrence to |z| ≥ 15, then apply Stirling with an explicit Bernoulli remainder. This needs a Mathlib-level bound on the remainder of the digamma asymptotic series, which is not available yet.
2. Use piecewise Taylor models of T̂ₙ and wψ on subintervals with proved derivative bounds, combined with a kernel-checked ℚ sum.

## DigammaStirling: explicit Stirling remainder for ψ

`lib/core/DigammaStirling.lean` (contributed with AI assistance (Grok Bot)) proves `digamma_stirling`: for Re z > 0,
‖ψ(z) − (log z − 1/(2z) − 1/(12z²))‖ ≤ 1/(120 (Re z)⁴).
It starts from the repo's Binet Laplace form `GammaIntegrals.digamma_eq_lap`, then uses the elementary kernel bound
−s³/720 ≤ φ(s) − s/12 ≤ 0 (`phiB_bounds`, via a chain of derivative-sign arguments for x cosh x − sinh x), the exact
integral ∫₀^∞ s e^{−zs} ds = 1/z² (FTC on (0,∞)), and ∫₀^∞ s³e^{−cs} ds = 6/c⁴. Combined with ψ(z+1) = ψ(z) + 1/z this
is the intended input for rigorous enclosures of Re ψ(1/4 + it/2) (the C^ψ family of the head certificate).

`re_digamma_quarter` (same module) gives the pointwise enclosure on the critical-line argument used by `Psi`. For every N and real b,
|Re ψ(1/4 + ib) − psiApx N b| ≤ 1/(120 (N + 1/4)⁴). Here psiApx N b is ½ log r − a/(2r) − (a² − b²)/(12r²) − Σ_{k<N} (k + 1/4)/((k + 1/4)² + b²), with a = N + 1/4 and r = a² + b². It is a rational function of b plus one real logarithm. It comes from Mathlib's `digamma_apply_add_nat` together with `digamma_stirling`. For example, N = 100 gives an error below 10⁻¹⁰.

## C^ψ enclosure proved: unconditional positivity at L = 1/2 (`Cm*` modules)

Contributed with AI assistance (Grok Bot). The modules `CmBessel`, `CmPoly`, `CmW`, `CmNu`, `CmWProof`, `CmGlob`, `CmLhD`,
`CmLhChk0–3`, `CmWD`, `CmMomDef`, `CmMomData`, `CmMomC0–7`, `CmMomProof`, `CmAsm`, `CmFinD`, `CmFinRe0–3`, `CmFinRo0–3`,
`CmFinP`, `CmFinA` and `CmEncP` discharge `WeilConst.CmEnc` for both sectors. As a result, `CmFin.L05_even_uncond` and
`CmFin.L05_odd_uncond` hold with no hypotheses. Their axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The proof works in the variable s = t/30 ∈ [0,1], where Cm wψ n m = (30/π) σₙσₘ √(2n+1)√(2m+1) ∫₀¹ wψ(30s) jₙ(15s) jₘ(15s) ds.

* **Model (`w_model`, `w_data`).** On each of 128 pieces [p/128, (p+1)/128], wψ(30s) is within εw = 1.6·10⁻⁹ of
  hev Gh(s²) − hev(Lh p)(s). The global part comes from the Stirling expansion around a = 48¼ plus Taylor series of
  log, inverse and cos. The local part comes from the 48 digamma poles, geometrically expanded about each piece centre.
  The coefficients are dyadic numbers on a 2⁻¹²⁸ grid. They are stored as data, and the kernel checks them piece by piece
  against their definitions.
* **Bessel polynomials (`jP_s`).** jₙ(15s) equals sⁿ Σ_{k<40} q̂ₖ s^{2k} up to an error eT ≈ 10⁻²³, using a
  cosine Taylor bound and dyadic rounding.
* **Moments (`nu_err`).** The model moments ∫ (model)·s^{2j}, j < 134, are floored per piece to the grid 2⁻¹²⁸. The chunk
  sums are kernel-checked in eight chunks, which gives the moments ν̂ to within 128·2⁻¹²⁸.
* **Quadrature error (`I_err`).** |∫₀¹ wψ jₙ jₘ − Σ q̂q̂ν| ≤ εw ∫₀¹|jₙjₘ| + 56·eJ. The factor εw is absorbed by
  (1/π)∫₀³⁰|T̂ₙT̂ₘ| ≤ 1, which follows from AM–GM and `modeOrth`.
* **Entry check (`entry`).** A rational bound R(n,m,c) combines the endpoint brackets for π and √(2n+1) with all the
  error terms. The kernel checks R ≤ εc row by row: εc = 6·10⁻⁹ (even) and 1.3·10⁻⁶ (odd). The largest R is
  ≈ 3.08·10⁻⁹ (even) and ≈ 2.95·10⁻⁹ (odd).

The kernel checks are split into many small modules, each taking about 3 minutes and a few GB of memory. The total kernel
time is roughly an hour.

## General test functions at L = 1/2: coercivity (`WeilCoer`, `LegSpan`, `WeilCont`, `WeilGen`)

The finite mode-sum results extend to a function class, with an explicit coercivity constant.

- **Coercivity on mode sums (`WeilCoer`).** For `h = hx N x y = Σ xᵢ T_{2i} + Σ yᵢ T_{2i+1}`,
  `‖h‖² = Σ xᵢ² + Σ yᵢ²` (Parseval and mode orthonormality). Combining the even margin (`10⁻⁸ Σ xᵢ²`) and the odd margin
  (`2·10⁻⁶ Σ yᵢ²`) with `weilQg (1/2) h = QF₀ + QF₁` gives `weilQg (1/2) h ≥ 10⁻⁸ ‖h‖²` for every `N`
  (pad short coefficient vectors with zeros up to `N ≥ 28`).
- **Span (`LegSpan`).** Every polynomial cut to `[−1/2, 1/2]` is some `hx N x y`. The proof uses the triangular
  shifted-Legendre basis, each `P̃_n` having exact degree `n`. The module also gives an explicit polynomial antiderivative.
- **Continuity (`WeilCont`).** Let `Good B M g` mean that `g` is measurable, vanishes off `[−1/2, 1/2]`, satisfies
  `|g| ≤ B`, and is `M`-Lipschitz on `[−1/2, 1/2]`. Jumps at `±1/2` are allowed, which matters because cut polynomials
  have them. If every `g k` and `f` are `Good B M` and `g k → f` pointwise, then `weilQg (1/2) (g k) → weilQg (1/2) f`.
  Each term is handled separately:
  - The pole and norm terms, and the autocorrelation, follow from dominated convergence on a compact set.
  - In the prime sum only `n = 2` survives, since `log n > 1` for `n ≥ 3`.
  - For the archimedean term, `|A(0) − A(u)| ≤ ∫ |g(t)|·|g(t) − g(t+u)| ≤ B(M+B)·u`. The interior Lipschitz bound covers
    the part where `t` and `t+u` both lie in `[−1/2, 1/2]`; the boundary layer `t ∈ (1/2−u, 1/2]` costs at most `B²u`.
    With `u·e^{u/2}/sinh u ≤ 8e^{−u/4}` this gives an integrable dominating function.
- **Conclusion (`WeilGen`).** Let `f` be `C¹` on `ℝ` with `f(u) = 0` for `|u| > 1/2`. Weierstrass-approximate `f'` by
  polynomials `q_k` with error below `1/(k+1)`. Integrate them to `p_k` with `p_k(−1/2) = f(−1/2)` and cut to `[−1/2, 1/2]`.
  The cut polynomials are uniformly bounded and uniformly interior-Lipschitz, and they converge pointwise to `f`. Passing
  to the limit gives
  - `weilQg (1/2) f ≥ 10⁻⁸ ‖f‖²`;
  - `0 < weilQg (1/2) f` for `f ≠ 0`;
  - for even `f`, the same two statements for `weilQ`, because the pole terms `ĝ(±i/2)` agree.

These results use only the standard axioms.

## Ground state at L = 1/2 (`GsGap`, `GsFourier`, `GsTail`, `GsUpper`, `OddMargin2`, `GsMain`)

**Relation to CCM.** Connes–Consani–Moscovici ("Zeta spectral triples") work with the Weil quadratic form `QW_λ` on
`L²([λ⁻¹, λ], d*u)`. Its restrictions `QW_λ^N` to the exponential spans `E_N` are real symmetric matrices commuting
with the parity `γ`. Their main theorem assumes, for each `N`, that the smallest eigenvalue of `QW_λ^N` is simple and
has an even eigenvector. Whether the lowest eigenvalue of `QW_λ` itself is simple and even is left open there.
Our setting is `u = log x ∈ [−1/2, 1/2]`, i.e. `λ = e^{1/2}`, and `Q = weilQg (1/2)`.

What is proved here is the min-max form of "simple, even, isolated", on the test class `TestFn`. That class consists of
the `C¹` functions supported in `[−1/2, 1/2]`; it contains the real and imaginary parts of CCM's `V_n`, so its span
is a form core. The theorems are stated for the form `Q`; nothing about an operator is formalized.

- **Trial vector (`GsUpper.trial_upper`).** The vector is `v = Σ_{i<10} (yᵢ/√(4i+1)) T_{2i}`, which equals
  `p(u+1/2)` cut to `[−1/2, 1/2]` for `p = Σ yᵢ P̃_{2i}` with rational `y`. The coefficients are chosen so that
  `p, p', p⁽⁴⁾, p⁽⁵⁾` vanish at `0` and `1` (checked exactly), and the result is `Q(v) ≤ μ₁‖v‖²` with `μ₁ = 2·10⁻⁵`.
  The exact rational value of the bound is `1.48·10⁻⁵ ‖v‖²`. The proof splits `Q` as follows:
  - **Exact split.** `Q = R(xv) + (1/π)∫_{30}^∞ (Ψ − β*) F²` (`GsTail.QF_eq`).
  - **Head.** The head `R(xv)` is bounded by the rational head matrix plus the proved entry enclosure.
  - **Six integrations by parts.** `|F(t)| ≤ A₂/t³ + A₃/t⁴ + |Φ_{p⁽⁶⁾}(t)|/t⁶` (`GsFourier.six_ibp`).
  - **Plancherel for cut polynomials.** `∫₀^∞ |Φ_q|² = π ∫₀¹ q²` (`GsFourier.plancherel`).
  - **Stirling bound.** `Ψ − β* ≤ 1.02 + t/30` for `t ≥ 30` (`GsTail.psi_upper`).

  All rational arithmetic is checked by `decide +kernel`.
- **Even gap (`GsGap.even_gap`).** For `N ≥ 28`, `QF₀(x) + c(Σ xᵢ xvᵢ)² ≥ (6/1000) Σ xᵢ²` with `c = 162471/262144`.
  The proof is an exact `LDLᵀ` certificate for `Rm + c·xh xhᵀ − (7/1000)I` on the 28-mode head (rounding `≤ 10⁻⁸`),
  plus the geometric tail bounds.
- **Odd sector (`OddMargin2.odd_margin2`).** `QF₁(y) ≥ 4·10⁻⁵ Σ yᵢ²`. Tightening the odd `C^ψ` enclosure to `6·10⁻⁹`
  (`CmFinRp*`, `CmEncOdd6`) lets the existing certificate yield this margin.
- **Lift (`GsMain`).** The two sector bounds above combine on mode sums. Approximation as in `WeilGen` then gives, for
  every `f ∈ TestFn`:
  - `Q(f) + c⟨f, v⟩² ≥ μ₂‖f‖²` with `μ₂ = 4·10⁻⁵` (`gap_general`);
  - hence `Q(f) ≥ μ₂‖f‖²` for `f ⊥ v` (`gap_perp`) and for every odd `f` (`odd_sector`).

  The trial vector `v` is itself in `TestFn`, since it is `C¹` because `p` and `p'` vanish at the ends (`v_testFn`).
  It is even, and `μ₁ < μ₂`. Every two-dimensional span of test functions contains a nonzero `h` with
  `Q(h) ≥ μ₂‖h‖²` (`minmax2`). Summary: `ground_state`, `ground_state_testFn`.

**Consequence (not formalized).** The form is lower bounded and closable, and the test class is a core (CCM Props
3.3–3.4). Granting those, together with identifying `weilQg (1/2)` with CCM's `QW_λ`, the Kato/Friedrichs operator
`A_λ` satisfies `λ₁ ≤ μ₁ < μ₂ ≤ λ₂` by min-max. Hence `λ₁` is simple and isolated, with gap at least `2·10⁻⁵`. Its
eigenvector is even, because the odd sector is bounded below by `μ₂ > λ₁` and `γ` commutes with `A_λ`. For the
truncations `QW_λ^N` the same conclusion follows for all sufficiently large `N`, a non-explicit threshold coming from
the core property. Mathlib has no form-closure / Friedrichs construction, so that step is cited rather than formalized.

These results use only the standard axioms.
