# The Halász–Montgomery inequality over the characters mod `q`

**Lean:** `LinnikPower.hm_duality` (`lib/pnt/LinnikPower.lean`):

```lean
theorem hm_duality {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} (hS0 : 0 ∉ S) {Λ : ℝ} (hΛ : 0 < Λ)
    (hSΛ : ∀ n ∈ S, (n : ℝ) ≤ Λ) (a : ℕ → ℂ) {σ : ℝ} (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σ ≤ β χ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ ∈ R, ∀ χ' ∈ R, χ ≠ χ' →
      ‖∑' n : ℕ, kTerm (χ * χ'⁻¹) Λ (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ ≤ B) :
    (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 ≤
      Real.exp 1 * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * (R.card * Λ + R.card ^ 2 * B)
```

In words, let `F(χ, s) = Σ_{n∈S} a_nχ(n)n^{−s}` with `S ⊆ [1, Λ]`, and take one point `β_χ + iγ_χ` with `β_χ ≥ σ`
for each character `χ` of a set `R` of characters mod `q`. Let `B` bound the off-diagonal kernels
`|K_Λ(χχ′⁻¹, z_{χχ′})|` for `χ ≠ χ′` in `R`, where `K_Λ(ψ, z) = Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ}` (`kTerm`) and
`z_{χχ′} = β_χ + β_χ′ − 2σ + i(γ_χ − γ_χ′)`. Then

`(Σ_{χ∈R} |F(χ, β_χ + iγ_χ)|)² ≤ e·Σ_n |a_n|²n^{−2σ}·(|R|Λ + |R|²B)`.

Two forms of it are used.

- `LinnikReflect.hm_duality_W` (`lib/pnt/LinnikWeighted.lean`) takes the weight `e^{−n/U} − e^{−2n/U}` in place of
  `e^{−n/Λ}`. Huxley's large-values estimate is built on it ([huxley-density.md](huxley-density.md)).
- `SieveTypeIIHM.sum_bin_hm` (`lib/pnt/SieveHMBin.lean`) is the case `σ = 0`, `β_χ = 0` and `γ_χ = h₀`, one height
  for the whole bin, at `Λ = 2P` for `S ⊆ (P, 2P]`.

These theorems are in the proof of `Linnik22000E.linnik_22000e`, whose axioms are `propext`, `Classical.choice` and
`Quot.sound` (`lib/check/Check.lean`), so they depend on those only. `hm_duality` does not use the zero-free
half-plane.

## With weights, in mean square, and for two polynomials

`SieveTypeIIHM.hm_duality_wt` (`lib/pnt/SieveTwoBins.lean`) is the same inequality with a weight `η_χ ∈ ℂ` on each
character, under the same hypotheses:

`|Σ_{χ∈R} η_χ F(χ, β_χ + iγ_χ)|² ≤ e·Σ_n |a_n|²n^{−2σ}·(Λ·Σ_χ |η_χ|² + B·(Σ_χ |η_χ|)²)`.

`hm_duality` is the case in which `η_χ` is the phase of the conjugate of `F`, of modulus at most `1`. With `η_χ` the
conjugate of `F` itself, at `σ = 0`, `β_χ = 0`, `γ_χ = h₀` and `Λ = 2P` for `S ⊆ (P, 2P]`, the left side is the square
of `D = Σ_χ |W(χ)|²`, `W(χ) = dp S (aχ) h₀`, and the right side is at most `e·Σ|a|²·(2P + |R|B)·D`. So

`Σ_{χ∈R} |W(χ)|² ≤ e·Σ_{j∈S} |a_j|²·(2P + |R|·B)` (`SieveTypeIIHM.sum_bin_hm_sq`),

the mean-square form: against orthogonality's `(P + q)Σ|a|²`, the number of characters of the set multiplies the
kernel bound only. It does not follow from `hm_duality` on the subsets of `R` without a factor `log |R|`.

For two polynomials `W₁` and `W₂`, Cauchy–Schwarz over a bin needs no count of the bin:

- `SieveTypeIIHM.sum_bin_two`: `Σ_{χ∈R} |W₁(χ)||W₂(χ)|` is at most the product of the square roots of the two mean
  squares, each the smaller of orthogonality's bound and the one above (`sqTerm`);
- `SieveTypeIIHM.sum_typeII_two_bins`: the sum over `χ ≠ 1` of `|W₁(χ)||W₂(χ)||B(χ)|`, by bins, as
  `SieveTypeIIHM.sum_typeII_bins_hm` does for one polynomial;
- `SieveTypeIIHM.bin_bound_two` (`lib/pnt/SieveTwoZone.lean`): a bin's contribution as a power of `q`. For
  `P_i = q^{m_i}` it is at most a constant times `(1 + log qT)^{10} q^{L − 1/25000 + η}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`
  when there are exponents `M_i` for the two mean squares (`M_i ≥ max(m_i, 1)`, or `M_i ≥ max(m_i, g + b(m_i))` with
  `b` the exponent of the kernel bound) with `(L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000`
  (`twoBound`). The window's exponents have a term `g/2` that these do not;
- `SieveTypeIIHM.twoBound_of_long`: that inequality holds, for every value of the curve, when `m₁, m₂ ≥ 1` and
  `m₁ + m₂ + 1/2000 ≤ L`: two variables of length at least `q` and a third factor of length at least `q^{1/2000}`.

No theorem of the library uses these yet: `lib/check/CheckAll.lean` prints their axioms, which are `propext`,
`Classical.choice` and `Quot.sound`. They are the estimate in two variables of
[`docs/research-opportunities.md`](../docs/research-opportunities.md) (§3.1). What that section's computations use
and these do not give: the inequality `twoBound` for the paper's curve on a region of `(m₁, m₂)` (it is sampled there,
not proved), and the families of sums in two variables to which the bins apply.

## Source

The inequality is named after G. Halász and H. L. Montgomery, who used it for large values of Dirichlet polynomials
and zero density:

- G. Halász, "Über die Mittelwerte multiplikativer zahlentheoretischer Funktionen", Acta Math. Acad. Sci. Hungar. 19
  (1968), 365–403;
- H. L. Montgomery, "Mean and large values of Dirichlet polynomials", Invent. Math. 8 (1969), 334–345, and his
  *Topics in Multiplicative Number Theory*, Lecture Notes in Math. 227 (Springer, 1971).

None of these was read for the formalisation. Huxley's "Large values of Dirichlet polynomials" (Acta Arith. 24 (1973),
329–346), whose p. 329 was read, calls it "the Halász inequality (Montgomery's basic tool)". The library's proof was
written from the standard argument by duality. Nothing in this library claims the inequality as its own.

## What the formalisation here is

`hm_duality` is proved by duality. With the phases `η_χ = conj F_χ/|F_χ|`, the left side is `|Σ_n a_n n^{−σ}·w_n|²`
with `w_n = Σ_χ η_χχ(n)n^{−(β_χ−σ)−iγ_χ}`. Cauchy–Schwarz with the weight `e^{−n/Λ}`, which is at least `e^{−1}` on
`S`, bounds it by `e·Σ_n |a_n|²n^{−2σ}` times `Σ_{n≥1} e^{−n/Λ}|w_n|²`. That full series expands into the kernels:
`Σ_{χ,χ′} η_χη̄_χ′K_Λ(χχ′⁻¹, z_{χχ′})`. The diagonal kernels are at most `Σ_n e^{−n/Λ} ≤ Λ` (`wt_summable_le`), and
the others at most `B`.

## Differences from the source

- **The first-power form.** The bound is on `(Σ_χ |F|)²`, the square of the sum of the absolute values, which is the
  form a count of large values uses.
- **The kernel bound is a hypothesis.** `B` is any bound on the off-diagonal kernels. Each use supplies its own:
  - Huxley's estimate bounds the kernels through the functional equation
    (`LinnikReflect.norm_hTerm_le_reflect`; [huxley-density.md](huxley-density.md)).
  - The Type II estimate's top piece takes `B` from `LinnikOffDiag.norm_offK_le`:
    `C(2P)^{1/12−δ}(2q)^{5/12+δ+2ε′}`. That bound moves the kernel's integral to `Re w = 1/12 − δ`. There it uses the
    functional equation and the bound on `Re s = 11/12 + δ` that the zero-free half-plane gives
    (`LinnikLindelof.lindelof`; [openai-half-plane.md](openai-half-plane.md)).
- **One point per character.** The points of different characters are unrelated; no spacing is needed, since
  `χχ′⁻¹ ≠ 1` for `χ ≠ χ′`.

## Where the Linnik paper uses it

- Through Huxley's estimate, on the steps of the density curve from `131/168` on ([huxley-density.md](huxley-density.md)).
- Directly, on the top piece `[5/6, 11/12]` of the Type II estimate. There `SieveHMBins` and `SieveTypeIIHM` bound
  each bin of characters at one height by `SieveTypeIIHM.sum_bin_hm`, with the kernel bound above. The window of the
  library's exponent, which is the paper's, `[43457/100000, 46959/100000]·L` at `L = 11/5`, is the window of this
  branch (`SieveTypeIIU22000D`). (The earlier windows, `[41556/100000, 47531/100000]·L` at `L = 278/125`,
  `[41479/100000, 47555/100000]·L` at `L = 89/40` and `[41335/100000, 48069/100000]·L` at `L = 899/400`, are in the git
  history.)
