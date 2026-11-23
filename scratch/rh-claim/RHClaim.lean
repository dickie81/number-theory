import HalfPlanePNT
import MertensExponent
import DivisorExponent
import SquarefreeCount
import ChiPNT
import Subconvexity
import InghamDensity
import LinnikGRH
import PivotSharp
import BallRate

/-!
# What the library gives from the Riemann Hypothesis for `ζ` and for every Dirichlet `L`-function

On 20 November 2026 Levent Alpöge posted a Lean archive that claims a proof of the Riemann Hypothesis and of
its analogue for every Dirichlet `L`-function (https://alpo.ge/remark.pdf; `tools/rh/README.md`). The archive's
`Main.lean` states five theorems, with no hypothesis, about Mathlib's `riemannZeta` and
`DirichletCharacter.LFunction`. This file takes two of those statements as a hypothesis (`Claim`), shows that
the other three follow from them, and lists what this library then gives, each by a theorem that it already
proves for any such input.

Nothing here is unconditional. The archive is not compiled in this file's environment: it pins Lean v4.33.1 and
a Mathlib of 21 August 2026, and this library pins Lean v4.35.0-rc3 and a Mathlib of 29 September. When the
archive's `Main` and this file are compiled in one environment, `Claim` is
`⟨riemannHypothesis, LFunction_eq_zero_re⟩` and every theorem below loses its hypothesis.

Check with `lake build LinnikGRH InghamDensity SquarefreeCount DivisorExponent ChiPNT HalfPlanePNT Subconvexity
PivotSharp BallRate` and then `lake env lean scratch/rh-claim/RHClaim.lean`.
-/

open Complex Real Filter Topology Asymptotics
open scoped Chebyshev

namespace RHClaim

/-! ## The archive's statements -/

/-- The archive's `DirichletLZerosOnLine`: a zero of `L(s, χ)` in the open critical strip has real part `1/2`,
for every character of every modulus. -/
def DirichletRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The two statements that the archive's five theorems come to: its `riemannHypothesis`, which is Mathlib's
`RiemannHypothesis`, and its `LFunction_eq_zero_re`. -/
structure Claim : Prop where
  rh : RiemannHypothesis
  grh : DirichletRH

/-- The archive's `RiemannZetaZerosOnLine` is Mathlib's `RiemannHypothesis` with its definition unfolded. -/
theorem zetaZerosOnLine (h : RiemannHypothesis) :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := h

/-- The archive's `DirichletLNonvanishingRightOfHalf`: no zero of `L(s, χ)` on `Re s > 1/2`, the pole of the
principal character's `L`-function aside. On `Re s ≥ 1` this is Mathlib's theorem. -/
theorem lfunction_ne_zero_of_half_lt (h : DirichletRH) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 1 / 2 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : DirichletCharacter.LFunction χ s ≠ 0 := by
  rcases lt_or_ge s.re 1 with h1 | h1
  · intro h0
    have := h N χ s (by linarith) h1 h0
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs h1

/-- The archive's `PrimitiveDirichletLZerosOnLine` is the case of the primitive characters. -/
theorem primitive_zeros_on_line (h : DirichletRH) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (_ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  h N χ s h0 h1 hz

/-- The library's form of GRH for one character. -/
theorem grh_char (h : DirichletRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PsiOmega.GRH χ :=
  fun s hz h0 h1 => h N χ s h0 h1 hz

/-- Under RH `ζ` has no zero on `Re s > 1/2`: the trivial zeros have negative real part, and `ζ(1) ≠ 0` for
Mathlib's value at the pole. -/
theorem zeta_ne_zero_of_half_lt (h : RiemannHypothesis) (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro h0
  have h1 : s ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h0)
  have ht : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re]
    rw [hre] at hs
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have := h s h0 ht h1
  linarith

/-! ## From the Riemann Hypothesis -/

/-- `ψ(x) = x + O(x^{1/2 + ε})`. -/
theorem psi (h : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ (1 / 2 + ε) :=
  HalfPlanePNT.psi_isBigO_of_zeroFree (by norm_num) (zeta_ne_zero_of_half_lt h) hε

/-- Mertens' function: `M(x) = O(x^{1/2 + η})`. -/
theorem mertens (h : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ PsiOmega.fμ x) =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  MertensExponent.mertens_isBigO_of_zeroFree (by norm_num) (by norm_num) (zeta_ne_zero_of_half_lt h) hη

/-- The `k`-fold divisor problem: `Σ_{n ≤ x} d_k(n) = x P_k(log x) + O(x^{1/2 + η})`. -/
theorem divisor (h : RiemannHypothesis) {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ (fun n ↦ (DivisorExponent.dk k n : ℝ)) x
      - x * (DivisorExponent.Pk k).eval (Real.log x)) =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  DivisorExponent.divisor_isBigO_of_zeroFree (by norm_num) (by norm_num) (zeta_ne_zero_of_half_lt h) hk hη

/-- The squarefree numbers up to `x`: `(6/π²)x + O(x^{2/5 + η})`. -/
theorem squarefree (h : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ SquarefreeCount.sqf x - 6 / π ^ 2 * x) =O[atTop] fun x ↦ x ^ (2 / 5 + η) := by
  have h2 := SquarefreeCount.squarefree_isBigO_of_zeroFree (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num) (zeta_ne_zero_of_half_lt h) hη
  rwa [show (1 : ℝ) / (3 - 1 / 2) = 2 / 5 by norm_num] at h2

/-- The Lindelöf hypothesis. -/
theorem lindelof (h : RiemannHypothesis) : CrossCriteria.Lindelof := Subconvexity.lindelof_of_RH h

/-- The density hypothesis. -/
theorem densityHypothesis (h : RiemannHypothesis) : CrossCriteria.DensityHypothesis :=
  InghamDensity.densityHypothesis_of_lindelof (lindelof h)

/-- The orbit's quadratic form: every Gram–Schmidt pivot after the first is at least `0.0577`. -/
theorem pivot_ge (h : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    999 / 1000 * (2 / 45) * (13 / 10) * x N ^ 2 ≤ BallWeil.form N x :=
  PivotSharp.pivot_ge_rh h hN x

/-- The orbit-lattice conjecture. -/
theorem orbitLattice (h : RiemannHypothesis) (k : ℕ) (c : ℕ → ℝ) (hk : 1 ≤ k) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  PivotSharp.orbitLattice_of_rh h k c hk

/-- `w_1` is a shortest vector of the orbit lattice. -/
theorem shortest (h : RiemannHypothesis) {N : ℕ} (a : ℕ → ℤ) (ha : ∃ n ∈ Finset.Icc 1 N, a n ≠ 0) :
    BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ)) :=
  PivotSharp.shortest_of_rh h a ha

/-- Balance at every level: the form of the orbit has no negative part at any stage `N`. The archive does not
prove this as a positivity; it is the library's own equivalence, read from right to left. -/
theorem balance (h : RiemannHypothesis) (N : ℕ) : BallRate.ExcessLe N 0 :=
  BallRate.rh_iff_balance.1 h N

/-! ## From the Riemann Hypothesis for the Dirichlet `L`-functions -/

/-- `ψ(x, χ) = O(x^{1/2 + η})` for `χ ≠ 1`. -/
theorem psiChi (h : DirichletRH) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ}
    (hη : 0 < η) : ChiPNT.psiChi χ =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  ChiPNT.psiChi_isBigO_of_zeroFree hχ (by norm_num) (by norm_num)
    (fun s hs => lfunction_ne_zero_of_half_lt h N χ s hs (Or.inl hχ)) hη

/-- Linnik's theorem with every exponent above `2`: each reduced class modulo `q` has a prime `p ≤ K q^{2 + η}`. -/
theorem linnik_two (h : DirichletRH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2 + η) :=
  LinnikGRH.linnik_two_of_GRH (fun _ _ χ => grh_char h χ) hη

end RHClaim

#print axioms RHClaim.lfunction_ne_zero_of_half_lt
#print axioms RHClaim.zeta_ne_zero_of_half_lt
#print axioms RHClaim.psi
#print axioms RHClaim.mertens
#print axioms RHClaim.divisor
#print axioms RHClaim.squarefree
#print axioms RHClaim.densityHypothesis
#print axioms RHClaim.pivot_ge
#print axioms RHClaim.orbitLattice
#print axioms RHClaim.shortest
#print axioms RHClaim.balance
#print axioms RHClaim.psiChi
#print axioms RHClaim.linnik_two
