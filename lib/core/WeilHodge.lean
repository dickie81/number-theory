/-
# Hodge index ⇒ Weil bound

Plain statement. Let `B` be a symmetric bilinear form on a real vector space, the intersection pairing on
divisor classes of `C × C`, and suppose the Hodge index property: `B` is negative semidefinite on the orthogonal
complement of an ample class `H` (`B H H > 0`). Then reversed Cauchy–Schwarz holds,
`B D D * B H H ≤ (B D H)²` (`hodge_cs`). With `H = e₁ + e₂` (the two fibre classes, `e₁·e₂ = 1`, `eᵢ² = 0`) this
gives Castelnuovo–Severi, `D·D ≤ 2 (D·e₁)(D·e₂)` (`castelnuovo`). Fed the intersection numbers of the diagonal `Δ` and
the Frobenius graph `Γ` (`Δ² = 2 − 2g`, `Γ² = q(2 − 2g)`, `Δ·Γ = N`, `Δ·eᵢ = 1`, `Γ·e₁ = 1`, `Γ·e₂ = q`), it gives
`(N − (q + 1))² ≤ 4 g² q` and `|N − (q + 1)| ≤ 2 g √q` (`weil_bound_of_hodge`). The intersection numbers and the
Hodge index property are hypotheses; for curves over finite fields they are theorems of algebraic geometry, and
over `Spec ℤ` neither is available.
-/
import Mathlib

noncomputable section

namespace WeilHodge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Reversed Cauchy–Schwarz from Hodge index.** -/
theorem hodge_cs (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (H : V) (hH : 0 < B H H)
    (hodge : ∀ D, B D H = 0 → B D D ≤ 0) (D : V) : B D D * B H H ≤ (B D H) ^ 2 := by
  set t := B D H / B H H with ht
  have hne : B H H ≠ 0 := hH.ne'
  have horth : B (D - t • H) H = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ht]
    field_simp; ring
  have h := hodge _ horth
  have hsym : B H D = B D H := hB H D
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hsym] at h
  have : B D D - (B D H) ^ 2 / B H H ≤ 0 := by
    have e : B D D - t * B D H - t * (B D H - t * B H H) = B D D - (B D H) ^ 2 / B H H := by
      rw [ht]; field_simp; ring
    linarith [e ▸ h]
  have h2 : B D D - (B D H) ^ 2 / B H H = (B D D * B H H - (B D H) ^ 2) / B H H := by
    field_simp
  rw [h2, div_nonpos_iff] at this
  rcases this with ⟨_, h3⟩ | ⟨h3, _⟩
  · linarith
  · linarith

/-- **Castelnuovo–Severi.** With fibre classes `e₁, e₂` (`e₁·e₂ = 1`, `eᵢ² = 0`) and Hodge index for
`H = e₁ + e₂`, every class satisfies `D·D ≤ 2 (D·e₁)(D·e₂)`. -/
theorem castelnuovo (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (e₁ e₂ : V)
    (h11 : B e₁ e₁ = 0) (h22 : B e₂ e₂ = 0) (h12 : B e₁ e₂ = 1)
    (hodge : ∀ D, B D (e₁ + e₂) = 0 → B D D ≤ 0) (D : V) :
    B D D ≤ 2 * B D e₁ * B D e₂ := by
  have h21 : B e₂ e₁ = 1 := by rw [hB]; exact h12
  have s1 : B e₁ D = B D e₁ := hB _ _
  have s2 : B e₂ D = B D e₂ := hB _ _
  set a := B D e₁
  set b := B D e₂
  have horth : B (D - b • e₁ - a • e₂) (e₁ + e₂) = 0 := by
    simp only [map_sub, map_smul, map_add, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, h11, h22, h12, h21]
    rw [← s1, ← s2]; simp only [s1, s2]; ring
  have h := hodge _ horth
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h11, h22, h12, h21,
    s1, s2] at h
  nlinarith [h]

/-- **Hodge index ⇒ Weil bound.** -/
theorem weil_bound_sq (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (e₁ e₂ Δ Γ : V) (g q N : ℝ)
    (hg : 0 ≤ g) (h11 : B e₁ e₁ = 0) (h22 : B e₂ e₂ = 0) (h12 : B e₁ e₂ = 1)
    (hΔΔ : B Δ Δ = 2 - 2 * g) (hΓΓ : B Γ Γ = q * (2 - 2 * g)) (hΔΓ : B Δ Γ = N)
    (hΔ1 : B Δ e₁ = 1) (hΔ2 : B Δ e₂ = 1) (hΓ1 : B Γ e₁ = 1) (hΓ2 : B Γ e₂ = q)
    (hodge : ∀ D, B D (e₁ + e₂) = 0 → B D D ≤ 0) :
    (N - (q + 1)) ^ 2 ≤ (2 * g) ^ 2 * q := by
  have hΓΔ : B Γ Δ = N := by rw [hB]; exact hΔΓ
  have key : ∀ r s : ℝ, 0 ≤ g * r ^ 2 - (N - (q + 1)) * r * s + g * q * s ^ 2 := by
    intro r s
    have h := castelnuovo B hB e₁ e₂ h11 h22 h12 hodge (r • Δ + s • Γ)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hΔΔ, hΓΓ, hΔΓ, hΓΔ,
      hΔ1, hΔ2, hΓ1, hΓ2] at h
    nlinarith [h]
  rcases hg.eq_or_lt with h0 | hpos
  · have h := key (N - (q + 1)) 1
    rw [← h0] at h ⊢
    nlinarith [h, sq_nonneg (N - (q + 1))]
  · have h := key (N - (q + 1)) (2 * g)
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith [h, hc', hpos]

/-- **Hodge index ⇒ Weil bound**, `|N − (q + 1)| ≤ 2 g √q`. -/
theorem weil_bound_of_hodge (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (e₁ e₂ Δ Γ : V) (g q N : ℝ)
    (hg : 0 ≤ g) (h11 : B e₁ e₁ = 0) (h22 : B e₂ e₂ = 0) (h12 : B e₁ e₂ = 1)
    (hΔΔ : B Δ Δ = 2 - 2 * g) (hΓΓ : B Γ Γ = q * (2 - 2 * g)) (hΔΓ : B Δ Γ = N)
    (hΔ1 : B Δ e₁ = 1) (hΔ2 : B Δ e₂ = 1) (hΓ1 : B Γ e₁ = 1) (hΓ2 : B Γ e₂ = q)
    (hodge : ∀ D, B D (e₁ + e₂) = 0 → B D D ≤ 0) :
    |N - (q + 1)| ≤ 2 * g * Real.sqrt q := by
  have h := weil_bound_sq B hB e₁ e₂ Δ Γ g q N hg h11 h22 h12 hΔΔ hΓΓ hΔΓ hΔ1 hΔ2 hΓ1 hΓ2 hodge
  have h1 := Real.abs_le_sqrt h
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)] at h1

end WeilHodge
