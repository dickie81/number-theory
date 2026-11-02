# Four bridges between parts of the library

Four small modules in `lib/pnt` state an implication between two parts of the library that had no import between
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

## `LonelyJoins`: the lonely primes, the exponent `Θ` and short intervals

```lean
theorem LonelyJoins.lonely_weight_isBigO_iff {a : ℝ} (ha : 1 / 2 ≤ a) :
    (∀ ε > 0, lonelyDev =O[atTop] fun x => x ^ (a + ε)) ↔ Theta ≤ a

theorem LonelyJoins.rh_iff_lonely_weight :
    RiemannHypothesis ↔ ∀ ε > 0, lonelyDev =O[atTop] fun x => x ^ ((1 : ℝ) / 2 + ε)

theorem LonelyJoins.lonely_in_window {θ' : ℝ} (hθ : 17 / 30 < θ') :
    ∃ X : ℝ, ∀ (N : ℕ) (y : ℝ), X ≤ y → (N : ℝ) / 2 ≤ y → y + y ^ θ' ≤ N →
      ∃ p : ℕ, p.Prime ∧ (∀ k : ℕ, 2 ≤ k → N < k * p) ∧ p ≤ N ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ'
```

Here `lonelyDev x = θ(x) − θ(x/2) − x/2`, the log-weight of the primes in `(x/2, x]` less half of `x`. The module joins
`LonelyPrimes` (`lib/pnt/LonelyPrimes.lean`), the frontier of the orbit lattice of `docs/ball-conjecture.md`, to
`PsiExponent.Theta` and `MertensExponent.rh_iff_Theta_eq_half`, and to
`ZetaGMDensity.short_primes_seventeen_thirtieths`.

- **The first theorem.** It is proved by `LonelyJoins.isBigO_of_sub_half`, which telescopes over `x, x/2, x/4, …`.
  That telescoping is played against `PsiExponent.psi_omega_Theta`.
- **The third.** It is the short-primes theorem read at stage `N`, with `LonelyPrimes.lonely_iff`.

*Implication.* The half in `LonelyPrimes.tendsto_lonely_ratio` is the prime number theorem. The size of its error is set
exactly by the real parts of the zeros, so RH is the statement that the lonely primes carry half of `x` to within
`x^{1/2+ε}`. Once `N/2` is large, the lonely primes also leave no gap longer than about `N^θ` anywhere in the frontier.
[connes-links.md](connes-links.md) puts these with the other links of that strand.
