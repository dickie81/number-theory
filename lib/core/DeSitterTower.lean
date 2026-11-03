/-
# A de Sitter tower of spheres

Plain statement. Stack sphere slices (the blocks of a tower, each with a nonnegative form `q_k`) along one time
direction and use the Lorentzian form `Q(t, x) = −t² + Σ_k q_k(x_k)`.
* **The slices of the hyperboloid are spheres of radius `cosh τ`**: at time `t = sinh τ`, `Q = 1` holds exactly when
  `Σ_k q_k(x_k) = cosh² τ` (`slice_radius`), pure algebra.
* **Lorentzian signature for unglued slices**: with every `q_k ≥ 0` the form has a negative direction (`Q(1, 0) = −1`,
  `time_neg`) and no plane on which it is negative definite (`no_timelike_plane`, `tower_lorentz`): exactly one negative
  direction.
* **The glued prime-side form**: for Weil's intersection form, `−D² = −½(D·e₁ + D·e₂)² + ½(D·e₁ − D·e₂)² + Q(c)`
  (`neg_selfInt_eq`), with time `D·e₁ + D·e₂` from the pole. The space-like part is nonnegative for all real classes
  if and only if RH (`rh_iff_deSitter`), and under RH the glued form is Lorentzian (`deSitter_of_rh`).
These are reformulations: the de Sitter shape of the glued tower is RH, not a proof of it.
-/
import Mathlib
import BallPole

open Finset

noncomputable section

namespace DeSitterTower

open BallWeil BallPole

/-- **Slices of the hyperboloid**: at time `sinh τ`, `Q = 1` iff the spatial form equals `cosh² τ`. -/
theorem slice_radius {K : ℕ} {V : Type*} (q : Fin K → V → ℝ) (x : Fin K → V) (τ : ℝ) :
    -(Real.sinh τ) ^ 2 + ∑ k, q k (x k) = 1 ↔ ∑ k, q k (x k) = Real.cosh τ ^ 2 := by
  rw [Real.cosh_sq]; constructor <;> intro h <;> linarith

/-- **No timelike plane**: if `Q = −T² + S` with `S ≥ 0` and `T` linear along a two-parameter family, `Q` is not
negative on every nonzero combination. -/
theorem no_timelike_plane {W : Type*} (T S : W → ℝ) (hS : ∀ w, 0 ≤ S w) (comb : ℝ → ℝ → W)
    (hT : ∀ α β, T (comb α β) = α * T (comb 1 0) + β * T (comb 0 1)) :
    ¬ ∀ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) → -T (comb α β) ^ 2 + S (comb α β) < 0 := by
  intro h
  set p := T (comb 1 0); set q := T (comb 0 1)
  by_cases hpq : p = 0 ∧ q = 0
  · have := h 1 0 (Or.inl one_ne_zero)
    have h0 : T (comb 1 0) = 0 := hpq.1
    rw [h0] at this; linarith [hS (comb 1 0)]
  · have hne : q ≠ 0 ∨ -p ≠ 0 := by
      by_contra hc; push Not at hc; exact hpq ⟨by linarith [hc.2], hc.1⟩
    have := h q (-p) hne
    have h0 : T (comb q (-p)) = 0 := by rw [hT]; ring
    rw [h0] at this; linarith [hS (comb q (-p))]

/-- The tower form `Q(t, x) = −t² + Σ_k q_k(x_k)`. -/
def towerQ {K : ℕ} {V : Type*} (q : Fin K → V → ℝ) (w : ℝ × (Fin K → V)) : ℝ := -w.1 ^ 2 + ∑ k, q k (w.2 k)

theorem time_neg {K : ℕ} {V : Type*} [Zero V] (q : Fin K → V → ℝ) (hq0 : ∀ k, q k 0 = 0) :
    towerQ q (1, 0) = -1 := by
  simp [towerQ, hq0]

/-- **Unglued tower is Lorentzian**: no plane of negative vectors, given every slice form is nonnegative. -/
theorem tower_lorentz {K : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V] (q : Fin K → V → ℝ)
    (hq : ∀ k v, 0 ≤ q k (v)) (u v : ℝ × (Fin K → V)) :
    ¬ ∀ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) → towerQ q (α • u + β • v) < 0 :=
  no_timelike_plane (fun w => w.1) (fun w => ∑ k, q k (w.2 k))
    (fun w => Finset.sum_nonneg fun k _ => hq k _) (fun α β => α • u + β • v) (by intro α β; simp)

/-- **The glued prime-side form in Lorentzian coordinates.** -/
theorem neg_selfInt_eq (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) :
    -selfInt a b N c = -(deg₁ b N c + deg₂ a N c) ^ 2 / 2 + (deg₁ b N c - deg₂ a N c) ^ 2 / 2 + form N c := by
  rw [selfInt_decomp, selfInt_of_orth (perp_orth a b N c)]; ring

theorem rh_iff_form_real : RiemannHypothesis ↔ ∀ (N : ℕ) (x : ℕ → ℝ), 0 ≤ form N x :=
  ⟨fun h N x => form_nonneg h N x, fun h => rh_iff_form.2 fun N x => h N (fun n => x n)⟩

/-- The space-like part of the glued form. -/
def spatial (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := (deg₁ b N c - deg₂ a N c) ^ 2 / 2 + form N c

/-- **RH iff the glued tower is de Sitter**: the space-like part is nonnegative on every real class. -/
theorem rh_iff_deSitter : RiemannHypothesis ↔ ∀ (a b : ℝ) (N : ℕ) (c : ℕ → ℝ), 0 ≤ spatial a b N c := by
  rw [rh_iff_form_real]
  refine ⟨fun h a b N c => add_nonneg (by positivity) (h N c), fun h N c => ?_⟩
  have := h (-∑ n ∈ Icc 1 N, c n * n) (-∑ n ∈ Icc 1 N, c n) N c
  simpa [spatial, deg₁, deg₂] using this

lemma deg₁_comb (α β b b' : ℝ) (N : ℕ) (c c' : ℕ → ℝ) :
    deg₁ (α * b + β * b') N (fun n => α * c n + β * c' n) = α * deg₁ b N c + β * deg₁ b' N c' := by
  simp only [deg₁, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

lemma deg₂_comb (α β a a' : ℝ) (N : ℕ) (c c' : ℕ → ℝ) :
    deg₂ (α * a + β * a') N (fun n => α * c n + β * c' n) = α * deg₂ a N c + β * deg₂ a' N c' := by
  simp only [deg₂, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

/-- **Under RH the glued form is Lorentzian**: no plane of classes with `D² > 0` throughout. -/
theorem deSitter_of_rh (hRH : RiemannHypothesis) (N : ℕ) (a b a' b' : ℝ) (c c' : ℕ → ℝ) :
    ¬ ∀ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) →
      -selfInt (α * a + β * a') (α * b + β * b') N (fun n => α * c n + β * c' n) < 0 := by
  intro h
  refine no_timelike_plane (fun w : ℝ × ℝ × (ℕ → ℝ) => (deg₁ w.2.1 N w.2.2 + deg₂ w.1 N w.2.2) / Real.sqrt 2)
    (fun w => spatial w.1 w.2.1 N w.2.2) (fun w => rh_iff_deSitter.1 hRH _ _ _ _)
    (fun α β => (α * a + β * a', α * b + β * b', fun n => α * c n + β * c' n)) ?_ ?_
  · intro α β; simp only [deg₁_comb, deg₂_comb]; simp; ring
  · intro α β hab
    have := h α β hab
    rw [neg_selfInt_eq] at this
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [spatial, div_pow, h2]
    linarith
