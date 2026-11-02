/-
# The pole classes and their orthogonal complement: the Hodge index form of RH

Plain statement. In Weil's form of RH (`BallWeil`) the classes `e₁`, `e₂` carry the pole of `ζ`: they contribute the
terms `m + n` of `D_m·D_n = m + n − √(mn)·K_H(m/n)`, which come from the terms `r^{±1/2}` of the explicit formula. For
`D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n` with real coefficients:
* **the pole span is a hyperbolic plane** (unconditional): `e₁² = e₂² = 0` and `(a·e₁ + b·e₂)² = 2ab`, so
  `(e₁ + e₂)² = 2` and `(e₁ − e₂)² = −2`, signature `(1, 1)` (`pole_hyperbolic`);
* **the decomposition is orthogonal** (unconditional): `D⊥ = D − (D·e₂)e₁ − (D·e₁)e₂` lies in the pole complement,
  `D⊥·e₁ = D⊥·e₂ = 0` (`perp_orth`), and `D² = 2(D·e₁)(D·e₂) + D⊥²` (`selfInt_decomp`);
* on the complement, `D² = −Q(c)` with `Q` the Gram form of the orbit (`selfInt_of_orth`);
* **RH holds if and only if `D² ≤ 0` on the pole complement**, for real coefficients (`rh_iff_hodge_index_real`), and
  if and only if Castelnuovo–Severi `D² ≤ 2(D·e₁)(D·e₂)` holds for real coefficients (`rh_iff_cs_real`). The integer
  versions are `BallWeil.rh_iff_hodge_index` and `BallWeil.rh_iff_castelnuovo_severi`.
* **Without a pole** (the Dirichlet `L`-functions of a nontrivial character): there are no classes `e₁`, `e₂`, the
  intersection form is `−Q_g` for the Gram form `Q_g` of the kernel, and the pole complement is the whole space, so the
  Hodge index statement is just positivity of `Q_g` (`hodge_no_pole_iff`, a definitional statement).
These are reformulations: nothing here proves the negativity on the complement, which is RH.
-/
import Mathlib
import BallWeil

open Finset

noncomputable section

namespace BallPole

open BallWeil

/-- **The pole complement**: `D·e₁ = D·e₂ = 0`. -/
def PoleOrth (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) : Prop := deg₁ b N c = 0 ∧ deg₂ a N c = 0

/-- On the pole span, `(a·e₁ + b·e₂)² = 2ab`. -/
theorem selfInt_pole (a b : ℝ) (N : ℕ) : selfInt a b N (fun _ => 0) = 2 * a * b := by
  simp [selfInt]

/-- **The pole span is a hyperbolic plane**: `e₁, e₂` isotropic, `(e₁ + e₂)² = 2`, `(e₁ − e₂)² = −2`. -/
theorem pole_hyperbolic (N : ℕ) :
    selfInt 1 0 N (fun _ => 0) = 0 ∧ selfInt 0 1 N (fun _ => 0) = 0 ∧
      selfInt 1 1 N (fun _ => 0) = 2 ∧ selfInt 1 (-1) N (fun _ => 0) = -2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [selfInt_pole] <;> norm_num

/-- **The projection to the pole complement**: `D⊥ = D − (D·e₂)e₁ − (D·e₁)e₂` has `D⊥·e₁ = D⊥·e₂ = 0`. -/
theorem perp_orth (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) : PoleOrth (a - deg₂ a N c) (b - deg₁ b N c) N c := by
  constructor <;> simp only [deg₁, deg₂] <;> ring

/-- **On the pole complement `D² = −Q(c)`.** -/
theorem selfInt_of_orth {a b : ℝ} {N : ℕ} {c : ℕ → ℝ} (h : PoleOrth a b N c) : selfInt a b N c = -form N c := by
  have e := two_deg_sub_selfInt a b N c
  rw [h.1, mul_zero, zero_mul, zero_sub] at e
  linarith

/-- **The decomposition is orthogonal**: `D² = 2(D·e₁)(D·e₂) + D⊥²`. -/
theorem selfInt_decomp (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) :
    selfInt a b N c = 2 * deg₁ b N c * deg₂ a N c + selfInt (a - deg₂ a N c) (b - deg₁ b N c) N c := by
  rw [selfInt_of_orth (perp_orth a b N c)]
  linarith [two_deg_sub_selfInt a b N c]

/-- **RH is the Hodge index theorem on the pole complement**, with real coefficients. -/
theorem rh_iff_hodge_index_real : RiemannHypothesis ↔
    ∀ (a b : ℝ) (N : ℕ) (c : ℕ → ℝ), PoleOrth a b N c → selfInt a b N c ≤ 0 := by
  refine ⟨fun hRH a b N c h => ?_, fun h => rh_iff_hodge_index.2 fun a b N c h1 h2 => h _ _ N _ ⟨h1, h2⟩⟩
  rw [selfInt_of_orth h]
  linarith [form_nonneg hRH N c]

/-- **RH is Castelnuovo–Severi**, `D² ≤ 2(D·e₁)(D·e₂)`, with real coefficients. -/
theorem rh_iff_cs_real : RiemannHypothesis ↔
    ∀ (a b : ℝ) (N : ℕ) (c : ℕ → ℝ), selfInt a b N c ≤ 2 * deg₁ b N c * deg₂ a N c := by
  rw [rh_iff_hodge_index_real]
  refine ⟨fun h a b N c => ?_, fun h a b N c hc => ?_⟩
  · rw [selfInt_decomp a b N c]
    linarith [h _ _ N c (perp_orth a b N c)]
  · have := h a b N c
    rw [hc.1, mul_zero, zero_mul] at this
    exact this

/-! ## Without a pole -/

/-- The Gram form of a kernel `g` on the classes `D_1, …, D_N`. -/
def formG (g : ℕ → ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * g m n

/-- The intersection form without pole classes, `D² = −Q_g(c)`. -/
def selfIntNP (g : ℕ → ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := -formG g N c

/-- **Without a pole the complement is everything**: the Hodge index statement is positivity of the Gram form. -/
theorem hodge_no_pole_iff (g : ℕ → ℕ → ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ), selfIntNP g N c ≤ 0) ↔ ∀ (N : ℕ) (c : ℕ → ℝ), 0 ≤ formG g N c := by
  simp only [selfIntNP, neg_nonpos]

end BallPole

#print axioms BallPole.pole_hyperbolic
#print axioms BallPole.selfInt_decomp
#print axioms BallPole.rh_iff_hodge_index_real
#print axioms BallPole.rh_iff_cs_real
#print axioms BallPole.hodge_no_pole_iff
