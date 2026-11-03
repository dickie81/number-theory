/-
# The sphere tower at equilibrium

Plain statement. The unit sphere `S^{s−1}` has area `|S^{s−1}| = 2π^{s/2}/Γ(s/2)` and the unit ball volume
`V_s = π^{s/2}/Γ(s/2 + 1)`.
* The archimedean factor of `ξ` is the inverse sphere area: `π^{−s/2}Γ(s/2) = 2/|S^{s−1}|` (`arch_eq_inv_area`),
  and `π^{−s/2}Γ(s/2 + 1) = 1/V_s` (`arch_succ_eq_inv_vol`), for `s > 0`.
* Shells: `|S^{s−1}| = s·V_s` (`area_eq_mul_vol`).
* In integer dimension `V_n` is Mathlib's volume of the unit ball of `ℝⁿ` (`vol_eq_volume_ball`).
* The Gaussian `e^{−πx²}` has integral `1` (`gaussian_one`).
* **Balance**: if `λ_n = a_n + b_n` (sphere part plus radiation part), then all `λ_n ≥ 0` iff the radiation never
  undercuts the sphere part, `−b_n ≤ a_n` (`balance_iff`).
The link of nonnegative Li coefficients to RH (Li's criterion) is not formalised here.
-/
import Mathlib

open Real MeasureTheory

noncomputable section

namespace SphereTower

/-- Area of the unit sphere `S^{s−1}`. -/
def area (s : ℝ) : ℝ := 2 * π ^ (s / 2) / Gamma (s / 2)

/-- Volume of the unit ball in dimension `s`. -/
def vol (s : ℝ) : ℝ := π ^ (s / 2) / Gamma (s / 2 + 1)

theorem arch_eq_inv_area {s : ℝ} (hs : 0 < s) : π ^ (-(s / 2)) * Gamma (s / 2) = 2 / area s := by
  have hg : 0 < Gamma (s / 2) := Gamma_pos_of_pos (by linarith)
  have hp : 0 < π ^ (s / 2) := rpow_pos_of_pos pi_pos _
  rw [area, rpow_neg pi_pos.le]; field_simp

theorem arch_succ_eq_inv_vol {s : ℝ} (hs : 0 < s) : π ^ (-(s / 2)) * Gamma (s / 2 + 1) = 1 / vol s := by
  have hg : 0 < Gamma (s / 2 + 1) := Gamma_pos_of_pos (by linarith)
  have hp : 0 < π ^ (s / 2) := rpow_pos_of_pos pi_pos _
  rw [vol, rpow_neg pi_pos.le]; field_simp

theorem area_eq_mul_vol {s : ℝ} (hs : 0 < s) : area s = s * vol s := by
  have hg : 0 < Gamma (s / 2) := Gamma_pos_of_pos (by linarith)
  rw [area, vol, Gamma_add_one (by positivity : s / 2 ≠ 0)]
  field_simp

theorem vol_eq_volume_ball (n : ℕ) [NeZero n] :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = vol n := by
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity), vol, sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul pi_pos.le]
  congr 2; ring

theorem gaussian_one : ∫ x : ℝ, exp (-π * x ^ 2) = 1 := by
  rw [integral_gaussian, div_self pi_ne_zero, sqrt_one]

theorem area_pos {s : ℝ} (hs : 0 < s) : 0 < area s := by
  have hg : 0 < Gamma (s / 2) := Gamma_pos_of_pos (by linarith)
  unfold area; positivity

/-- **Balance**: nonnegativity of `λ = a + b` is the radiation never undercutting the sphere part. -/
theorem balance_iff (a b : ℕ → ℝ) : (∀ n, 0 ≤ a n + b n) ↔ ∀ n, -b n ≤ a n :=
  forall_congr' fun n => by constructor <;> intro h <;> linarith
