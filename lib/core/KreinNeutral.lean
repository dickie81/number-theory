/-
# Non-real eigenvectors are neutral in an indefinite metric

Plain statement. Let `J` and `A` be linear maps on a complex inner product space with `A` self-adjoint for the
(possibly indefinite) form `[x, y] = ⟪J x, y⟫`, i.e. `[A x, y] = [x, A y]`. If `A v = μ v` with `μ` non-real,
then `[v, v] = 0` (`neutral_of_nonreal`). Hence if the form is definite (e.g. positive: no negative squares),
every eigenvalue is real (`im_eq_zero_of_pos`). This is the elementary step behind the Pontryagin-space bound
(at most κ non-real eigenvalue pairs when the form has κ negative squares); the bound itself is not formalised.
-/
import Mathlib

noncomputable section

namespace KreinNeutral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Non-real eigenvectors are neutral.** -/
theorem neutral_of_nonreal (J A : E →ₗ[ℂ] E) (hJA : ∀ x y, inner ℂ (J (A x)) y = inner ℂ (J x) (A y))
    (v : E) (μ : ℂ) (hv : A v = μ • v) (hμ : μ.im ≠ 0) : inner ℂ (J v) v = 0 := by
  have h1 := hJA v v
  rw [hv, map_smul, inner_smul_left, inner_smul_right] at h1
  have h2 : (starRingEnd ℂ μ - μ) * inner ℂ (J v) v = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exfalso; apply hμ
    have := congrArg Complex.im h
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  · exact h

/-- **No negative squares ⇒ real spectrum.** -/
theorem im_eq_zero_of_pos (J A : E →ₗ[ℂ] E) (hJA : ∀ x y, inner ℂ (J (A x)) y = inner ℂ (J x) (A y))
    (hpos : ∀ x, x ≠ 0 → inner ℂ (J x) x ≠ 0) (v : E) (hv0 : v ≠ 0) (μ : ℂ) (hv : A v = μ • v) :
    μ.im = 0 := by
  by_contra hμ
  exact hpos v hv0 (neutral_of_nonreal J A hJA v μ hv hμ)

end KreinNeutral
