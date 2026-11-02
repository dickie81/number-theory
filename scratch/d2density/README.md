# d₂ < d₁ density: Lean files (not wired into the lakefile)

Check each file with `lake env lean scratch/d2density/<file>.lean`. Each one ends with `#print axioms`. None uses `sorry`,
and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. See `docs/d2-density.md` for the mathematics.

| file | main results |
|---|---|
| `D2Criterion.lean` | `criterion` (d₂ ≥ d₁ ⇔ −2K₁−2c ≤ ℓ ≤ −2c), `c0_closed`, `c1_closed` |
| `D2Density.lean` | `re_inv_pos`, `K1_pos`, `density_of_dist`, `d2_density`, `L0_finite`, `d2_density_log` |
| `PV.lean` | `polya_vinogradov`: ‖Σ_{M≤n<M+N} χ(n)‖ ≤ √q (1 + log q) for primitive χ mod q > 1; `norm_gaussSum_sq` |
| `PV.lean` (cont.) | `pv_Ioc`; `pv_nonprincipal`: ‖Σ_{0<m≤y} χ(m)‖ ≤ d(n) √n (1 + log n) for every non-principal χ mod n (imprimitive allowed, via the primitive character and μ over divisors) |
| `Kron.lean` | `exists_jacobiSym_eq_neg_one`: for odd non-square n there is D with J(D|n) = −1 (non-principality) |
| `GS.lean` | `sqf_sum_le`, `sqf_sum_le_sqrt`: the squarefree-sieve core of Granville–Soundararajan Lemma 4.1 |

Two lemmas are copied verbatim, so that each file depends on Mathlib only: `gaussSum_mul_gaussSum_inv` (from
`lib/core/RealCharHalfPlane.lean`) and `sum_sq_dvd_moebius` (from `lib/pnt/SquarefreeCount.lean`).

| `GSFull.lean` | self-contained concatenation of `PV`, `Kron` and `GS`, plus: `JChar.jchar` (D ↦ J(D|n) as a Dirichlet character mod n), `psiChar` (twist mod 4n by 1 or χ₄), `psiChar_ne_one` (non-principal for odd non-square n); `GSAssemble.class_sum_le` (for r ∈ {1,3}: ‖Σ_{d≤x sqf, d≡r (4)} J(d|n)‖ ≤ 2√(xB)+B) and `odd_sum_le`, with B = d(4n)√(4n)(1+log 4n) |
| `GSFull.lean` (cont.) | `GSFund.fundPos` and `fundNeg` (fundamental discriminants by sign, through \|D\|); **`gs_pos`, `gs_neg`: GS Lemma 4.1 per sign for odd non-square n**: ‖Σ_{0<\|D\|≤x, D fund.} χ_D(n)‖ ≤ 3(2√(xB)+B), with χ_D(n) = J(D\|n) (the Kronecker symbol for odd n) | |
| `GSFull.lean` (cont.) | `GSEven.kron D n := χ₈(D)^{v₂ n}·J(D \| n/2^{v₂ n})` (Kronecker symbol; checked against PARI `kronecker` for \|D\|<200, n<300); `psi8` mod 8m, non-principal when m non-square or v₂ odd; `gs_even_pos/neg`; **`GSKron.gs_kron_pos`, `gs_kron_neg`: GS Lemma 4.1 for every non-square n > 1, each sign**: ‖Σ_{0<\|D\|≤x fund.} (D\|n)‖ ≤ GSB n x ≪ √x·n^{1/4+ε} + n^{1/2+ε} |
| `GSFull.lean` (cont.) | **A1, moments of the short Euler-sum model.** `GSMoment.kron_mul`/`kron_prod` (Kronecker multiplicative in n); `moment_pos`/`moment_neg`: for finite P ⊂ ℕ>0, weights a, S_D = Σ_{p∈P} a_p (D\|p): ‖Σ_{fund. D≤x} S_D^k − x·Σ_{f∈P^k, ∏f=□} (∏a_{f i}) c(∏f)‖ ≤ Σ_f ‖∏a‖·(R(∏f) if square, else GSB); `moment_pos_tendsto`/`moment_neg_tendsto`: (1/x)Σ S_D^k → main term. **Conditional on the explicit hypothesis `Hcount`** (square-n count: ‖Σ_{fund. D≤x}(D\|n) − c(n)x‖ ≤ R n x, with R = o(x)); A2 will discharge it |

Remaining hypotheses of `d2_density_log`: `hdist`, `hB` and `hpos` (table in `docs/d2-density.md`).
