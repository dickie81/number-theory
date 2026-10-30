# Three bridges between parts of the library

Three small modules in `lib/pnt` state an implication between two parts of the library that had no import between
them. Each proves an implication that is known or elementary; what the modules add is the machine-checked link. None of
them is imported by `lib/check/Check.lean` or by a paper; their axioms are printed in `lib/check/CheckAll.lean`.

## `LinnikGRH`: GRH for every Dirichlet L-function gives Linnik's exponent `2 + η`

```lean
theorem LinnikGRH.charDensity_two_of_GRH
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), PsiOmega.GRH χ) : Linnik.CharDensity 2 0 1

theorem LinnikGRH.linnik_two_of_GRH
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), PsiOmega.GRH χ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2 + η)
```

It joins `PsiOmega.GRH` (`lib/core/WeilChiCriterion.lean`) to `Linnik.linnik_of_charDensity`
(`lib/pnt/LinnikDeduction.lean`). Under GRH the density estimate with exponent `A = 2` is elementary: only the trivial
character is counted at `σ > 1/2`, and at most `φ(q)` characters at `σ = 1/2`.

*Implication.* The density route has a conditional endpoint in the library: the exponent `2`, the lower limit of
`linnik_of_charDensity` (`hA : 2 ≤ A`). `linnik_of_charDensity` also uses the zero-free half-plane
`Eis.LFunction_ne_zero_of_re_gt`, so this is not a statement independent of it. The unconditional exponents of the Linnik
paper are different statements.

## `ShortPrimesHalfPlane`: the zero-free region of the short-primes theorems from the half-plane

```lean
theorem ShortPrimesHalfPlane.zeroFreeXi_of_halfplane {α : ℝ} (hα : 0 ≤ α) : ZeroFreeXi α
```

`zeroFreeXi_of_halfplane` takes the zero-free region input of `ShortWeil.short_primes_of_density` from
`HalfPlaneJoins.abs_im_tau_le_five_twelfths` (`lib/core/HalfPlaneJoinsFinal.lean`), a region of constant width `1/12`,
in place of the Korobov–Vinogradov region (`ShortKV.zeroFreeXi_KV`). `ZetaHuxley.short_primes_of_density_eps_hp` uses
it, and through it `ZetaHuxley.short_primes_seven_twelfths` (`θ > 7/12`) and
`ZetaGMDensity.short_primes_seventeen_thirtieths` (`θ > 17/30`).

*Implication.* The short-primes theorems take their zero-free region from the half-plane, not from Korobov and
Vinogradov's. The module's first theorem, `θ > 11/17` without the Korobov–Vinogradov region, and the library's two
earlier proofs of short primes (`θ > 11/17` and `θ > 3/4`) are in the git history: `θ > 17/30` is stronger.

(Checked by walking the constants each declaration depends on, with a one-off Lean script outside the repository. This
is not part of the library's checks.)

## `LinnikWeylBridge`: `PYWeyl` contains `WeylBound`

```lean
theorem LinnikWeylBridge.weylBound_of_PYWeyl (h : LinnikWeyl.PYWeyl) : CrossCriteria.WeylBound
```

`LinnikWeyl.PYWeyl` (`lib/pnt/LinnikWeyl.lean`) is the Weyl bound `‖L(1/2 + it, χ)‖ ≤ C (q(1 + |t|))^{1/6+ε}` for every
character; `CrossCriteria.WeylBound` (`lib/core/CrossCriteria.lean`) is the same bound for ζ alone. The proof takes
`q = 1`, where the only character's L-function is ζ (`DirichletCharacter.LFunction_modOne_eq`).

*Implication.* A proof of the Weyl bound for ζ alone would not discharge `PYWeyl`, which is uniform in `q`; `PYWeyl` is
the stronger hypothesis and `WeylBound` its case `q = 1`. Both are hypotheses in the library, and neither is proved here.
