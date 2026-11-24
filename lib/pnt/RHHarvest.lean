import HalfPlaneGRH
import InghamDensity
import PNTProgressions
import SquarefreeCount
import DivisorExponent

/-!
# The corollaries of the top: RH and GRH through the library's zero-free half-planes

The top of the library's rebuild of L. Alpöge's proof (`docs/rh-rebuild.md`) is `HalfPlaneGRH.RHandGRH`, the Riemann
hypothesis for `ζ` and for the `L`-function of every Dirichlet character. Every frontier of the rebuild gives it
(`ZetaBalance.rhAndGRH_of_pairBound`, `ZetaBalance.rhAndGRH_of_sixTermBound`), so what follows here follows from the
construction alone, with the half-plane `Re s > 11/12` that those frontiers use; L. Alpöge's Lean archive proves the
top on its own pins (`docs/account.md`, an input), and in the library it stays a hypothesis.

The top is equivalent to the zero-free half-plane `Re s > 1/2` for every primitive character
(`HalfPlaneGRH.zeroFreeRightOf_half_iff`). This file turns it into the zero-free half-planes of `ζ` and of every
`L(s, χ)`, and puts them into the library's results that take a zero-free half-plane with any boundary `θ`, at
`θ = 1/2`. Each consequence is classical.

* `LFunction_ne_zero`, `riemannZeta_ne_zero`: no zero of any `L(s, χ)`, the pole of `ζ` aside, on `Re s > 1/2`
  (`HalfPlaneGRH.LFunction_ne_zero_of_zeroFreeRightOf`), and so none of `ζ`, the character mod `1`.
* `weylBound`: Weyl's bound `|ζ(1/2 + it)| ≪ |t|^{1/6+ε}`, from Lindelöf's hypothesis (`Subconvexity.lindelof_of_RH`).
* `zeta_bound`: `ζ(s)` and `1/ζ(s)` are `≪ |t|^ε` on `Re s ≥ σ₀ > 1/2` (`HalfPlaneLindelof.zeta_bound_of_zeroFree`).
* `short_primes`: a prime in `(y, y + y^θ]` for every `θ > 1/2` and every large `y`, from the density hypothesis
  (`InghamDensity.densityHypothesis_of_lindelof`, `InghamDensity.short_primes_of_density_eps`).
* `psi_isBigO`, `psiChi_isBigO`, `psiAP_isBigO`: `ψ(x) − x`, for `χ ≠ 1` `ψ(x, χ)`, and `ψ(x; q, a) − x/φ(q)` for
  `a` prime to `q` are `O(x^{1/2+ε})` (`HalfPlanePNT.psi_isBigO_of_zeroFree`, `ChiPNT.psiChi_isBigO_of_zeroFree`,
  `PNTProgressions.psiAP_isBigO_of`).
* `divisor_isBigO`, `squarefree_isBigO`: `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{1/2+η})` for every `k ≥ 1`
  (`DivisorExponent.divisor_isBigO_of_zeroFree`), and `Q(x) = 6x/π² + O(x^{2/5+η})` for the squarefree numbers, the
  exponent `1/(3 − θ)` of `SquarefreeCount.squarefree_isBigO_of_zeroFree`.
* `corollaries`: all of them at once, with Lindelöf's hypothesis, the density hypothesis and `M(x) = O(x^{1/2+η})`
  (`MertensExponent.rh_iff_mertens`).

The results stated at `Θ`, the supremum of the real parts of the zeros of `ζ`, hold at `1/2` by
`MertensExponent.rh_iff_Theta_eq_half`; Linnik's exponent `2 + η` and its forms for almost all classes take the top
through `LinnikGRH.dirichletRH_of_rhAndGRH`.
-/

open Complex Filter Asymptotics DirichletCharacter
open PsiOmega (summ fμ)
open SquarefreeCount (sqf)
open DivisorExponent (dk Pk)

namespace HalfPlaneGRH.RHandGRH

/-- **GRH: no zero of `L(s, χ)` on `Re s > 1/2`**, for every Dirichlet character `χ`, the pole of `ζ` aside: the top's
half-plane for the primitive characters (`zeroFreeRightOf_half_iff`) carried to every character. -/
theorem LFunction_ne_zero (h : RHandGRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 / 2 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_zeroFreeRightOf (zeroFreeRightOf_half_iff.2 h) (by norm_num) χ hs hχs

/-- **RH: no zero of `ζ` on `Re s > 1/2`**, the half-plane that the library's results take: the character mod `1`,
and `ζ(1) ≠ 0` (Mathlib's value at the pole). -/
theorem riemannZeta_ne_zero (h : RHandGRH) : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := fun s hs => by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  · simpa using h.LFunction_ne_zero (1 : DirichletCharacter ℂ 1) hs (Or.inr hs1)

/-- **Weyl's bound** `|ζ(1/2 + it)| ≪ |t|^{1/6+ε}` for every `ε > 0` (`CrossCriteria.WeylBound`), from Lindelöf's
hypothesis (`Subconvexity.lindelof_of_RH`). -/
theorem weylBound (h : RHandGRH) : CrossCriteria.WeylBound := fun ε hε =>
  Subconvexity.zetaCritBound_mono (by linarith) (Subconvexity.lindelof_of_RH h.1 ε hε)

/-- **`ζ(s)` and `1/ζ(s)` are `≪ |t|^ε` on `Re s ≥ σ₀ > 1/2`**: `HalfPlaneLindelof.zeta_bound_of_zeroFree` at `1/2`. -/
theorem zeta_bound (h : RHandGRH) {σ₀ ε : ℝ} (hσ₀ : 1 / 2 < σ₀) (hε : 0 < ε) :
    ∃ T C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → T ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε :=
  HalfPlaneLindelof.zeta_bound_of_zeroFree (by norm_num) (by norm_num) hσ₀ hε h.riemannZeta_ne_zero

/-- **Primes in short intervals**: for every `θ > 1/2`, every large `y` has a prime in `(y, y + y^θ]`. Lindelöf's
hypothesis gives the density hypothesis, the exponent `A = 2` (`InghamDensity.densityHypothesis_of_lindelof`), and an
exponent `A` gives every `θ > max(1/2, 1 − 1/A)` (`InghamDensity.short_primes_of_density_eps`). -/
theorem short_primes (h : RHandGRH) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ :=
  InghamDensity.short_primes_of_density_eps (A₀ := 2) two_pos
    (InghamDensity.densityHypothesis_of_lindelof (Subconvexity.lindelof_of_RH h.1)) hθ (by linarith)

/-- **The prime number theorem with a square-root error**: `ψ(x) − x = O(x^{1/2+ε})` for every `ε > 0`
(`HalfPlanePNT.psi_isBigO_of_zeroFree` at `1/2`). -/
theorem psi_isBigO (h : RHandGRH) {ε : ℝ} (hε : 0 < ε) :
    (Chebyshev.psi - id) =O[atTop] fun x : ℝ ↦ x ^ (1 / 2 + ε) :=
  HalfPlanePNT.psi_isBigO_of_zeroFree (by norm_num) h.riemannZeta_ne_zero hε

/-- **`ψ(x, χ) = O(x^{1/2+η})`** for every Dirichlet character `χ ≠ 1` and every `η > 0`
(`ChiPNT.psiChi_isBigO_of_zeroFree` at `1/2`). -/
theorem psiChi_isBigO (h : RHandGRH) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ}
    (hη : 0 < η) : ChiPNT.psiChi χ =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  ChiPNT.psiChi_isBigO_of_zeroFree hχ (by norm_num) (by norm_num)
    (fun _ hs ↦ h.LFunction_ne_zero χ hs (Or.inl hχ)) hη

/-- **The prime number theorem in progressions with a square-root error**: `ψ(x; q, a) − x/φ(q) = O(x^{1/2+η})`
for `a` prime to `q`, `a < q`, and every `η > 0` (`PNTProgressions.psiAP_isBigO_of` at `1/2 + η`). -/
theorem psiAP_isBigO (h : RHandGRH) {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) (haq : a < q) {η : ℝ}
    (hη : 0 < η) : (fun x ↦ PsiOmega.psiAP q a x - x / q.totient) =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  PNTProgressions.psiAP_isBigO_of ha haq (by linarith) (h.psi_isBigO hη) fun _ hχ ↦ h.psiChi_isBigO hχ hη

/-- **The divisor problems**: `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{1/2+η})` for every `k ≥ 1` and `η > 0`
(`DivisorExponent.divisor_isBigO_of_zeroFree` at `1/2`). -/
theorem divisor_isBigO (h : RHandGRH) {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ (fun n ↦ (dk k n : ℝ)) x - x * (Pk k).eval (Real.log x)) =O[atTop]
      fun x ↦ x ^ (1 / 2 + η) :=
  DivisorExponent.divisor_isBigO_of_zeroFree (by norm_num) (by norm_num) h.riemannZeta_ne_zero hk hη

/-- **Squarefree numbers**: `#{n ≤ x : n squarefree} = 6x/π² + O(x^{2/5+η})` for every `η > 0`
(`SquarefreeCount.squarefree_isBigO_of_zeroFree` at `1/2`, where `1/(3 − θ) = 2/5`). -/
theorem squarefree_isBigO (h : RHandGRH) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ sqf x - 6 / Real.pi ^ 2 * x) =O[atTop] fun x ↦ x ^ (2 / 5 + η) := by
  have hQ := SquarefreeCount.squarefree_isBigO_of_zeroFree (by norm_num) (by norm_num) h.riemannZeta_ne_zero hη
  rwa [show (1 : ℝ) / (3 - 1 / 2) = 2 / 5 by norm_num] at hQ

/-- **The corollaries of the top**, and so of every frontier of the rebuild, the construction alone. RH with GRH for
every Dirichlet `L`-function (`RHandGRH`) implies: no zero of `ζ`, nor of any `L(s, χ)` (the pole of `ζ` aside), on
`Re s > 1/2`; Lindelöf's hypothesis and Weyl's bound; `ζ(s)`, `1/ζ(s)` `≪ |t|^ε` on `Re s ≥ σ₀ > 1/2`; the density
hypothesis, and a prime in `(y, y + y^θ]` for every `θ > 1/2` and every large `y`; `ψ(x) − x`, `ψ(x, χ)` for `χ ≠ 1`,
`ψ(x; q, a) − x/φ(q)` for `a` prime to `q`, `M(x)` and `Σ_{n≤x} d_k(n) − xP_k(log x)` all `O(x^{1/2+η})`; and
`#{n ≤ x squarefree} − 6x/π² = O(x^{2/5+η})`. -/
theorem corollaries (h : RHandGRH) :
    (∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      LFunction χ s ≠ 0) ∧
    CrossCriteria.Lindelof ∧ CrossCriteria.WeylBound ∧
    (∀ σ₀ ε : ℝ, 1 / 2 < σ₀ → 0 < ε → ∃ T C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → T ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖⁻¹ ≤ C * |t| ^ ε) ∧
    CrossCriteria.DensityHypothesis ∧
    (∀ θ : ℝ, 1 / 2 < θ → ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ) ∧
    (∀ ε : ℝ, 0 < ε → (Chebyshev.psi - id) =O[atTop] fun x : ℝ ↦ x ^ (1 / 2 + ε)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ η : ℝ, 0 < η →
      ChiPNT.psiChi χ =O[atTop] fun x ↦ x ^ (1 / 2 + η)) ∧
    (∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → a < q → ∀ η : ℝ, 0 < η →
      (fun x ↦ PsiOmega.psiAP q a x - x / q.totient) =O[atTop] fun x ↦ x ^ (1 / 2 + η)) ∧
    (∀ η : ℝ, 0 < η → (fun x ↦ summ fμ x) =O[atTop] fun x ↦ x ^ (1 / 2 + η)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η →
      (fun x ↦ summ (fun n ↦ (dk k n : ℝ)) x - x * (Pk k).eval (Real.log x)) =O[atTop] fun x ↦ x ^ (1 / 2 + η)) ∧
    (∀ η : ℝ, 0 < η → (fun x ↦ summ sqf x - 6 / Real.pi ^ 2 * x) =O[atTop] fun x ↦ x ^ (2 / 5 + η)) :=
  ⟨h.riemannZeta_ne_zero, fun _ _ χ _ hs hχs => h.LFunction_ne_zero χ hs hχs, Subconvexity.lindelof_of_RH h.1,
    h.weylBound, fun _ _ hσ₀ hε => h.zeta_bound hσ₀ hε,
    InghamDensity.densityHypothesis_of_lindelof (Subconvexity.lindelof_of_RH h.1), fun _ => h.short_primes,
    fun _ => h.psi_isBigO, fun _ _ _ hχ _ => h.psiChi_isBigO hχ, fun _ _ _ ha haq _ => h.psiAP_isBigO ha haq,
    MertensExponent.rh_iff_mertens.1 h.1,
    fun _ hk _ => h.divisor_isBigO hk, fun _ => h.squarefree_isBigO⟩

end HalfPlaneGRH.RHandGRH

#print axioms HalfPlaneGRH.RHandGRH.LFunction_ne_zero
#print axioms HalfPlaneGRH.RHandGRH.riemannZeta_ne_zero
#print axioms HalfPlaneGRH.RHandGRH.weylBound
#print axioms HalfPlaneGRH.RHandGRH.zeta_bound
#print axioms HalfPlaneGRH.RHandGRH.short_primes
#print axioms HalfPlaneGRH.RHandGRH.psi_isBigO
#print axioms HalfPlaneGRH.RHandGRH.psiChi_isBigO
#print axioms HalfPlaneGRH.RHandGRH.psiAP_isBigO
#print axioms HalfPlaneGRH.RHandGRH.divisor_isBigO
#print axioms HalfPlaneGRH.RHandGRH.squarefree_isBigO
#print axioms HalfPlaneGRH.RHandGRH.corollaries
