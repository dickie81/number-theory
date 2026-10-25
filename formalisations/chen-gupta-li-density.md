# Chen–Gupta–Li's zero-density estimate on `[5/7, 16/21]`

**Lean:** `LinnikCGLDensity.cglDensity` (`lib/pnt/LinnikCGLDensity.lean`) proves `LinnikCGL.CGLDensity`
(`lib/pnt/LinnikCGL.lean`):

```lean
def CGLDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ C * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + ε)
```

In words: for every `ε > 0` there is `C` such that, for every `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most
`C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`.
`LFunction` is Mathlib's `DirichletCharacter.LFunction`. The theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only (`lib/check/Check.lean`).

## Attribution

The estimate is B. Chen, V. Gupta and Y. C. Li's: "Large value estimates for Dirichlet polynomials with characters
and zero density of Dirichlet `L`-functions", arXiv:2507.08296v2 (27 July 2026). Version 1 (11 July 2025) was
B. Chen's alone. Their abstract states `Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}`, and "The exponent 7/3
improves upon Huxley’s earlier exponent of 12/5". Their method is Guth and Maynard's (Ann. of Math. 203 (2026),
623–675; arXiv:2405.20552).

The proof formalised here is theirs. Nothing in this library claims the estimate, or its proof, as its own.

**Scope.** The library formalises their Proposition 3.1 (`LinnikCGLHB101.prop31`) with the results it rests on
(Propositions 4.6, 6.1, 8.1 and 11.1 and Theorem 10.1, see below), and derives from it the steps
`LinnikCGLSteps.charDensity_s0` … `charDensity_s106` of the Linnik paper and the estimate `CGLDensity` below. It does not
formalise their Theorem 1.2 beyond the range `[5/7, 16/21]` (nor `[5/7, 1307/1680]` as a single statement), their Theorem 1.1,
or the other parts of their paper. Some of what it does formalise was read only in outline (list below). The Lean statements are the library's own, and the kernel checks
their proofs, not that they faithfully capture the preprint's theorems.

## What the formalisation here is

The formalisation follows the paper. It was read from the PDF's text layer:

- **in full:** §§1–7, §8 (Proposition 8.1, and Lemma 8.2 with its proof), §9, §11.2, and §§12.1, 12.2 and 12.4;
- **statements and early lemmas:** §10's statements and Lemmas 10.4–10.6, and §12.3 up to the statement of Lemma
  12.1;
- **in outline only:** Lemmas 10.7–10.10 and the proof of Proposition 10.2, §11.1, and the proof of Lemma 12.1.

The text layer drops the bar over `χ₂` in the statement of Theorem 10.1 (p. 40). The PDF has it, and so does
`LinnikCGLT101.CGLT101`.

The chain in Lean is as follows.

- **The density count from the large values** (their §12). `LinnikCGLStep.charDensity_cglGen` derives it from their
  Proposition 3.1 at one point per character. With the step's internal `ε` free, it gives the count at the exponent
  `(7/3 + 26e)(1 − σ)` with the factor `(log qT)^{10}` (`LinnikCGLDensity.charDensity_e`).
- **Their Proposition 3.1 at one point per character** (`LinnikCGLHB101.prop31`). Its inputs are:
  - their Proposition 4.6 (`LinnikCGLMat.prop46`);
  - their Proposition 6.1, the bound on `S₂` (`LinnikCGLS2.cgls2`);
  - their Proposition 11.1, the bound on `S₃` (`LinnikCGLHB101.cgls3`), with §§7–10 behind it.
- **Their Proposition 8.1** (`LinnikCGLP81.cglp81`), by their downward induction on `ε` from Lemma 8.2.
- **Their Theorem 10.1, Heath-Brown's bound for double sums with characters** (`LinnikCGLHB101.cglt101`). See below.
- **Ending at `CGLDensity` itself.** `cglDensity` takes the step's internal `ε` to `0` and absorbs the factor
  `(log qT)^{10}` into `(qT)^ε`.

The formalisation is in `lib/pnt`, in the modules whose names begin with `LinnikCGL`.

## Differences from the source

- **Characters, not zeros.** The source bounds `Σ_χ N(σ, T, χ)`, the number of zeros. The Lean statement bounds the
  number of characters with a zero, which is at most that sum. So the source implies the Lean statement, and not the
  other way round. Counting characters lets every large-values set carry one point per character, which is the form
  the whole formalisation uses.
- **The range.** The source's Theorem 1.2 holds for `1/2 < σ < 1`. Their §12 says that "Theorem 1.2 follows from
  Ingham’s result (1.4) when σ ≤ 0.7 and Huxley’s result (1.5) when σ ≥ 0.8", so the paper's own argument is needed
  only on `[0.7, 0.8]`. The Lean statement covers only `[5/7, 16/21]`, which lies inside `[0.7, 0.8]`. The Linnik
  paper uses it there and nowhere else.
- **Their Theorem 1.1 is not formalised.** The step needs the large-values count only at `V = N^σ/Z` with
  `5/7 ≤ σ ≤ 16/21`. That lies inside Proposition 3.1's range `[N^{7/10}, N^{4/5}]`, where the paper's reduction is
  the three-part split of the polynomial alone (`LinnikCGLLV.lv_range`). The subdivision in `T`, the mean value
  theorem and Huxley's estimate, which their proof of Theorem 1.1 uses, are not needed.
- **Explicit constants and extra factors.** Several of the paper's `≪` and `⪅` bounds are stated in Lean with
  explicit constants. Where the Lean form carries an extra factor, the factor is absorbed by `(qTN)^ε`. For example,
  the Ramanujan-sum bound is used as `|C_q(n)| ≤ d(q)(n, q)` where the paper has `(n, q)`.
- **The cut-off in `ξ`.** Their proof of Lemma 8.2 splits the integral of `Σ_a|ĝ_a(ξ)|²` at `|ξ| = (qT)²` and
  discards `|ξ| > (qT)²` by the decay of `Σ_b|f̂_b|` (p. 29). The library's bound on that range (`LinnikCGLTail`) is
  the same argument with a cut-off `X` in place of their `(qT)²`, and `LinnikCGLForm` takes `X = (qT)³`.
- **Lemma 10.8 is not formalised as stated.** `LinnikCGLSep.sum_cube_le` does its part in the proof of Lemma 10.9.

## Corrections to the source

The formalisation found six places where the paper's text needs a small repair. None of them affects the paper's
results.

- **Proposition 7.1.** The Cauchy–Schwarz step in the proof of Proposition 7.2 bounds an integral over `v₂` by
  `R̃_{M₂}` (their (7.5), p. 24), whose integral runs over `[1/2, 2]` only. So the step needs the integrand restricted
  to `v₂/v₁ ∈ [1/2, 2]`, which Proposition 7.1 as stated does not give. The restriction holds because the kernel `J`
  vanishes unless `v₂/v₁ ∈ (1/2, 2)` (`LinnikCGLSym.Jk_eq_zero_of_ratio`). The library's form of Proposition 7.1
  includes it (`LinnikCGLSym.prop71r`).
- **The proof of Proposition 7.2 (p. 26).** After the substitution `u′ = v₂/v₁`, a display omits the factor
  `√v₁ ≤ √2` that comes from `dv₂ = v₁du′`. The next line is stated with `≪_ϵ`, which absorbs it (`LinnikCGLRt`).
- **The proof of Lemma 9.2 (p. 39).** After the change of variables `v = e^τ`, the majorized integral in the display
  carries the Jacobian `e^τ`, and the identity that follows drops it. If it is kept, `e^τ` grows like `e^{(qT)^ϵ}` on
  the support of the majorant. The library bounds `e^τ ≤ 2` on the original range `|τ| ≤ log 2` before majorizing,
  at the cost of a factor `2` (`LinnikCGLMom4.lemma92`).
- **Remark 10.3 (p. 40).** The remark holds as stated, strictly and with the constant `1`, since `E(W) ≤ |W|³`.
  The slip is in the chain of inequalities given for it. Its step `(qT)³|W|³N^{−3} < qT|W|³` needs `N³ > (qT)²`, which
  fails for `(qT)^{2/3}/2 ≤ N ≤ (qT)^{2/3}`. The library proves the remark directly (`LinnikCGLCase.remark103`),
  without assuming `E ≤ |W|³` and with the constant `8`, which is then attained.
- **The bump `ψ` of §11 (p. 48).** To bound `S₃,₄` they apply Proposition 8.1 to `f_b(v) = ψ(v)|R̃_{M₂}(v, −b)|²`,
  "where ψ(v) is a smooth bump function supported on v ≍ 1 and such that ψ(1) > 0" (p. 48). Comparing `S₃,₄` with
  `J(f⃗)` term by term needs `f_{−b} ≥ R̃_{M₂}(·, b)²` at every centre `(m₁v + m₃)/m₂`. The centres include points
  near `0`, where such a `ψ` vanishes and `R̃_{M₂}` need not. On the library's dyadic blocks the centres lie in
  `[−3, 3]`, and the library takes for `ψ` Mathlib's smooth bump with radii `3` and `4`, which is `1` on `[−3, 3]`
  (`LinnikCGLFb.psiW`, `LinnikCGLFb.Rt_sq_le_fb`, `LinnikCGLJ.S34_le_Jint`).
- **The change of variables `u = v⁻¹` in §11 (p. 48).** It takes `(m₁v + m₃)/(m₂v)` to `(m₁ + m₃u)/m₂`, the form
  Proposition 8.1 needs, but the displays that follow print the denominator as `m₂u`. The library's bound on `S₃,₃`
  uses `(m₁ + m₃u)/m₂` (`LinnikCGLJ.S33_le_S34`).

## Heath-Brown's Theorem 10.1, with characters

The paper states its Theorem 10.1 for primitive characters and credits it to Heath-Brown: "Theorem 10.1
(Heath-Brown, [6]). Let T be a set of pairs (t, χ), where χ is a primitive character modulo q …". Their [6] is "A
large values estimate for Dirichlet polynomials", J. London Math. Soc. 20 (1979), 8–18. That paper could not be
obtained and was not read. The formalisation (`LinnikCGLHB101.cglt101`) follows two sources:

- B. Kerr's proof of the case `q = 1` (arXiv:1909.12075, Theorem 16 and §§5–6): positivity, lengthening, squaring
  and a reflection;
- for the reflection with characters, in place of Kerr's van der Corput B-process, M. Jutila's Lemma 1 ("Zero-density
  estimates for `L`-functions", Acta Arith. 32 (1977), 55–62).

The statement proved (`LinnikCGLT101.CGLT101`) is the paper's Theorem 10.1 for primitive characters, with its implicit
constants explicit and a factor `(qTM)^ε`, which their statement implies.

The result is adapted rather than transcribed: its cited source was not read, and the proof combines two other
sources. It is documented here, as part of the formalisation of the paper that states and uses it, and no paper in
this repository claims it.

## Where the Linnik paper uses it

The density curve of the Linnik paper's Type II estimate (`g7c`, `SieveTypeIIU226C.counts_7c`) is built from these
pieces:

- the trivial count below `4/7`;
- twenty steps from Ingham's estimate;
- this estimate on `[5/7, 16/21]` at `ε = 1/8400`, giving the exponent `(7/3 + 1/2000)(1 − σ)`
  (`SieveTypeIIU227.rangeCounts_cgl`);
- twenty steps from Huxley's estimate up to `5/6`;
- the library's `(101/50)(1 − σ)` from `5/6` on (`LinnikStep.charDensity_step`).

The theorem of the proof built on this curve, at an earlier exponent (`899/400`), is no longer in the tree: it was
superseded, and is in the git history. `cglDensity` stays and is printed by `lib/check/Check.lean`.

## Proposition 3.1 on `[5/7, 1307/1680]`, and Huxley's bound up to `131/168`: the second route

`LinnikCGLSteps` uses the same step (`LinnikCGLStep.charDensity_cglGen`, from Proposition 3.1,
`LinnikCGLHB101.prop31`) at other parameters, 107 steps of width `1/1680` on `[5/7, 1307/1680]`. Each step's exponent is
`A(1 − σ)` with `A` within `10⁻⁴` of `4/(1 + lo)` (the table in the file's header), which is the divisor form `4/(1 + σ)` of the
paper's Theorem 1.2 at `q₁ = q`, taken at the step's left end. The library does not prove Theorem 1.2: the exponents
come from what `ParC.Good` allows the library's own Proposition 3.1 route (`tools/linnik/gen_cgl_curve.py` computes
the parameters and checks every field of `ParC.Good` in exact rationals). For `σ > 5/7` this is below the flat
`7/3 + 1/2000` of `charDensity_cgl`, which the earlier route (at `899/400`, in the git history) used on `[5/7, 16/21]` and took to `ε → 0`
(`cglDensity`). No hypothesis is involved: the steps hold at `e = 1/100000` and need no `ε`.

From `7/9` on Huxley's exponent `3/(3σ − 1)` is below `4/(1 + σ)`, so on `[1307/1680, 131/168]`, the three steps that
contain `σ > 7/9`, the curve takes Huxley's bound: `LinnikHuxJunction` (`charDensity_hj0` … `charDensity_hj2`) is
`LinnikHuxStep.charDensity_gen` (the argument of `huxley-density.md`) at new `Par` parameters on these steps of width
`1/1680`, with `A` just above Huxley's exponent at the step's left end (`2.24915`, `2.24614`, `2.24315`, against the
Chen–Gupta–Li steps' `2.24983`, `2.24907`, `2.24833`). `tools/linnik/gen_cgl_curve.py` checks every field of `Par.Good` in
exact rationals. No hypothesis is involved.

The curve is `g7d` (`SieveTypeIIU22250D.lean`): `g7c` with the Chen–Gupta–Li steps on `[5/7, 1307/1680]` and these Huxley
steps on `[1307/1680, 131/168]`, in place of the plateau and Huxley's steps `hx7_0` … `hx7_4`, and with Ingham's last step
`[99/140, 5/7]` at `ε = 1/400000` (`LinnikCGLSteps.charDensity_inT`: `LinnikInghamC.charDensity_ingham_c` has exponent `2 + 4c + 4ε`, so the slack is `4ε`, and the exponent is `7/3 + 1/100000` in place of `7/3 + 1/2000` at `ε = 1/8000`). Huxley's steps
`hx7_5` … `hx7_19` stay, since their exponents are smaller than the Chen–Gupta–Li step's from `131/168` on. The steps are
narrow because the window's lower end is set where a step's exponent most exceeds the curve it bounds, at the steps
containing `7/9`, where `4/(1 + σ)` meets Huxley's `3/(3σ − 1)`; its upper end is set by the largest exponent, `7/3`
at `5/7`. `Linnik22250R.linnik_22250r` is Linnik's theorem with exponent `89/40` on `g7d`. (With Chen–Gupta–Li's
steps all the way to `131/168`, the library's certificate closed at `893/400`; the Huxley steps on the last three
steps, and two more levels of the Buchstab decomposition, lower `total2/K` enough to close at `89/40`.)
