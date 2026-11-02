/-
# Toeplitz positivity along a tower, and the dictionary to the orbit curve

Plain statement. Call `c : ℕ → ℝ` *Toeplitz positive* (`ToeplitzPos`) if `Σ_{i,j < K} x_i x_j c(|i − j|) ≥ 0` for
every `K` and real `x`: a positive-definite function on `ℤ`, even by construction.
* For an elliptic curve over `𝔽_q`, `q` odd, the normalised traces `c_d = (q^d + 1 − #E(𝔽_{q^d}))/(2q^{d/2})` are
  Toeplitz positive (`manin_toeplitzPos`, from `ManinHasse.toeplitz_nonneg`), the Riemann hypothesis for `E` in every
  degree.
* Toeplitz positivity is closed under nonnegative scaling and sums (`ToeplitzPos.smul`, `ToeplitzPos.add`) and under
  pointwise limits (`ToeplitzPos.of_tendsto`). So along any family of curves, `E_m` over `𝔽_{q_m}`, the pointwise
  limit of the normalised traces, or of any normalisation by positive constants such as the genus, is again Toeplitz
  positive (`tower_limit`).
* **The dictionary**: in a curve realization of a kernel `k` (`BallCurve.CurveRealization`) and for every step `h`,
  `d ↦ Re k(e^{dh})` is Toeplitz positive (`curve_toeplitzPos`), the analogue of `manin_toeplitzPos` with `h = log q`.
  Here `Re k(1/r) = Re k(r)` holds in every realization (`re_kernel_inv`).
What the finite-field case has and the limit loses is recorded in `docs/positivity-search.md`.
-/
import Mathlib
import ManinLattice
import BallFrobenius

open Real Finset Filter Topology

noncomputable section

namespace FrobTower

/-- **Toeplitz positivity** of `c : ℕ → ℝ`: `Σ_{i,j < K} x_i x_j c(|i − j|) ≥ 0`. -/
def ToeplitzPos (c : ℕ → ℝ) : Prop :=
  ∀ (K : ℕ) (x : Fin K → ℝ), 0 ≤ ∑ i, ∑ j, x i * x j * c (Nat.dist i j)

theorem ToeplitzPos.smul {c : ℕ → ℝ} (hc : ToeplitzPos c) {t : ℝ} (ht : 0 ≤ t) : ToeplitzPos fun d => t * c d := by
  intro K x
  have h : ∑ i, ∑ j, x i * x j * (t * c (Nat.dist i j)) = t * ∑ i, ∑ j, x i * x j * c (Nat.dist i j) := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
  rw [h]
  exact mul_nonneg ht (hc K x)

theorem ToeplitzPos.add {c c' : ℕ → ℝ} (hc : ToeplitzPos c) (hc' : ToeplitzPos c') :
    ToeplitzPos fun d => c d + c' d := by
  intro K x
  have h : ∑ i, ∑ j, x i * x j * (c (Nat.dist i j) + c' (Nat.dist i j)) =
      ∑ i, ∑ j, x i * x j * c (Nat.dist i j) + ∑ i, ∑ j, x i * x j * c' (Nat.dist i j) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_; ring
  rw [h]
  exact add_nonneg (hc K x) (hc' K x)

/-- **Toeplitz positivity passes to pointwise limits.** -/
theorem ToeplitzPos.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {c : ι → ℕ → ℝ} {c₀ : ℕ → ℝ}
    (hc : ∀ i, ToeplitzPos (c i)) (hlim : ∀ d, Tendsto (fun i => c i d) l (𝓝 (c₀ d))) : ToeplitzPos c₀ := by
  intro K x
  have ht : Tendsto (fun i => ∑ a : Fin K, ∑ b : Fin K, x a * x b * c i (Nat.dist a b)) l
      (𝓝 (∑ a : Fin K, ∑ b : Fin K, x a * x b * c₀ (Nat.dist a b))) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => (hlim _).const_mul _
  exact ge_of_tendsto ht (Eventually.of_forall fun i => hc i K x)

/-- **The normalised traces of an elliptic curve over `𝔽_q`, `q` odd, are Toeplitz positive.** -/
theorem manin_toeplitzPos {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
    (hF : ringChar F ≠ 2) (L : ℕ → Type*) [∀ d, Field (L d)] [∀ d, Fintype (L d)] [∀ d, Algebra F (L d)]
    (hL : ∀ d, 0 < d → Fintype.card (L d) = Fintype.card F ^ d) : ToeplitzPos (ManinHasse.ctrace W L) :=
  fun K x => ManinHasse.toeplitz_nonneg W hF L hL K x

/-- **Along a tower**: if each member is Toeplitz positive, so is every pointwise limit of positive rescalings. -/
theorem tower_limit {c : ℕ → ℕ → ℝ} {g : ℕ → ℝ} {c₀ : ℕ → ℝ} (hc : ∀ m, ToeplitzPos (c m)) (hg : ∀ m, 0 < g m)
    (hlim : ∀ d, Tendsto (fun m => c m d / g m) atTop (𝓝 (c₀ d))) : ToeplitzPos c₀ :=
  ToeplitzPos.of_tendsto (c := fun m d => (g m)⁻¹ * c m d)
    (fun m => (hc m).smul (inv_nonneg.2 (hg m).le)) fun d => by simpa [div_eq_inv_mul] using hlim d

/-! ## The dictionary to the orbit curve -/

open BallCurve

/-- In a curve realization, `Re k(1/r) = Re k(r)` for `r > 0`. -/
theorem re_kernel_inv {k : ℝ → ℂ} (C : CurveRealization k) {r : ℝ} (hr : 0 < r) : (k r⁻¹).re = (k r).re := by
  have h1 := C.gram r 1 hr one_pos
  have h2 := C.gram 1 r one_pos hr
  rw [← inner_conj_symm, h2] at h1
  simp only [one_mul, mul_one, div_one, one_div] at h1
  have hs : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.2 hr
  have h3 := congrArg Complex.re h1
  rw [Complex.conj_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h3
  exact mul_left_cancel₀ hs.ne' h3

/-- **The dictionary**: in a curve realization, `d ↦ Re k(e^{dh})` is Toeplitz positive for every step `h`. -/
theorem curve_toeplitzPos {k : ℝ → ℂ} (C : CurveRealization k) (h : ℝ) :
    ToeplitzPos fun d => (k (Real.exp (d * h))).re := by
  intro K x
  have H := BallFrobenius.toeplitz_nonneg C h K x
  rw [Complex.re_sum] at H
  refine H.trans_eq (sum_congr rfl fun i _ => ?_)
  rw [Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul]
  congr 1
  rcases le_total (j : ℕ) i with hij | hij
  · show _ = (k (Real.exp (((Nat.dist (i : ℕ) j : ℕ) : ℝ) * h))).re
    rw [Nat.dist_eq_sub_of_le_right hij, Nat.cast_sub hij]
  · show _ = (k (Real.exp (((Nat.dist (i : ℕ) j : ℕ) : ℝ) * h))).re
    rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij, ← re_kernel_inv C (Real.exp_pos _), ← Real.exp_neg]
    congr 3
    ring

end FrobTower

#print axioms FrobTower.ToeplitzPos.of_tendsto
#print axioms FrobTower.ToeplitzPos.add
#print axioms FrobTower.manin_toeplitzPos
#print axioms FrobTower.tower_limit
#print axioms FrobTower.curve_toeplitzPos
