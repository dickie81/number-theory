/-
# GRH for every Dirichlet L-function gives the density hypothesis `CharDensity 2 0 1`, and so Linnik's exponent `2 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. If every Dirichlet L-function satisfies the generalized Riemann hypothesis in the library's form
(`PsiOmega.GRH χ` for every modulus `q ≥ 1` and every `χ` mod `q`), then `Linnik.CharDensity 2 0 1` holds
(`charDensity_two_of_GRH`), and so every reduced class modulo every `q ≥ 1` has a prime `p ≤ K q^{2+η}` for every
`η > 0` (`linnik_two_of_GRH`).

That Linnik's exponent is `2 + η` under GRH is a classical consequence of GRH (via the density estimate with `A = 2`,
which is then trivial). The module's content is the machine-checked link between two parts of the library that had no
import between them: the Weil-criterion layer's `PsiOmega.GRH` (`lib/core/WeilChiCriterion.lean`) and the density
deduction of `LinnikDeduction`. `Linnik.linnik_of_charDensity` itself uses the zero-free half-plane
`Eis.LFunction_ne_zero_of_re_gt` (through `error_le`), so `linnik_two_of_GRH` is not a half-plane-free statement. It is
conditional on GRH, so it is a different statement from the unconditional exponent `89/40` of the Linnik paper; `2` is
the exponent the density route gives under GRH, not claimed to be an optimum.

* `charDensity_two_of_GRH`: `(∀ q [NeZero q] χ, PsiOmega.GRH χ) → Linnik.CharDensity 2 0 1`, by cases `σ > 1/2` (only the
  trivial character is counted) and `σ = 1/2` (at most `φ(q)` characters).
* `linnik_two_of_GRH`: the same hypothesis gives `p ≡ a (mod q)`, `p ≤ K q^{2+η}`, by
  `Linnik.linnik_of_charDensity (le_refl _) (le_refl _) zero_le_one`.
-/
import LinnikDeduction
import WeilChiCriterion

open DirichletCharacter

namespace LinnikGRH

/-- **GRH for every Dirichlet character gives `Linnik.CharDensity 2 0 1`.** `PsiOmega.GRH χ` says every zero of
`L(·, χ)` in `0 < Re s < 1` has `Re s = 1/2`. For `σ > 1/2` the only character counted is then the trivial one (the
value of its `LFunction` at `s = 1` is Mathlib's junk value), so the count is `≤ 1 ≤ (qT)^{2(1−σ)}`; at `σ = 1/2` the
count is `≤ φ(q) ≤ q ≤ qT = (qT)^{2(1−σ)}·(qT)`. -/
theorem charDensity_two_of_GRH
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), PsiOmega.GRH χ) :
    Linnik.CharDensity 2 0 1 := by
  classical
  intro q _ σ T hσ hσ1 hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hqT : (1 : ℝ) ≤ q * T := by nlinarith
  have hrpow : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (2 * (1 - σ)) :=
    Real.one_le_rpow hqT (by linarith)
  simp only [Real.rpow_zero, mul_one, one_mul]
  rcases hσ.lt_or_eq with hlt | heq
  · -- σ > 1/2: only the trivial character can have such a "zero" (at s = 1, a junk value)
    have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ⊆ {1} := by
      intro χ hχ
      by_contra hne
      have hχ1 : χ ≠ 1 := by simpa using hne
      obtain ⟨s, hs1, hs2, hs3⟩ := (Finset.mem_filter.1 hχ).2
      rcases lt_or_ge s.re 1 with h1 | h1
      · have := h q χ s hs3 (by linarith) h1
        linarith
      · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1 hs3
    have hc : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ 1 := by exact_mod_cast hc
      _ ≤ _ := hrpow
  · -- σ = 1/2: at most φ(q) ≤ q ≤ qT characters
    have hc : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card ≤ q := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
      exact Nat.totient_le q
    have e : ((q : ℝ) * T) ^ (2 * (1 - σ)) = (q : ℝ) * T := by
      rw [← heq]; norm_num
    rw [e]
    calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ q := by exact_mod_cast hc
      _ ≤ q * T := by nlinarith

/-- The consequence: GRH for every modulus gives Linnik's theorem with every exponent `2 + η`. -/
theorem linnik_two_of_GRH
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), PsiOmega.GRH χ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2 + η) :=
  Linnik.linnik_of_charDensity (le_refl _) (le_refl _) zero_le_one (charDensity_two_of_GRH h) hη

end LinnikGRH

#print axioms LinnikGRH.charDensity_two_of_GRH
#print axioms LinnikGRH.linnik_two_of_GRH
