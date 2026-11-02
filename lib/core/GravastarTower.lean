/-
# The tower of spheres and asymptotic balance

Plain statement. Section the orbit form at every level `N`: the unit sphere `S^{N−1}` of coefficient vectors on
`1, …, N`. The **excess positivity** at level `N` is at most `t` when `−Q_N(x) ≤ t·‖x‖²` on that section, i.e.
`ε_N = −λ_min(G_N) ≤ t` (on the pole complement `D² = −Q_N`, `BallPole.selfInt_of_orth`).
* The sections nest, so the excess is **monotone**: a bound at level `N'` gives it at every `N ≤ N'` (`excess_mono`).
* **RH is exact balance**: `ε_N ≤ 0` at every level (`rh_iff_balance`).
* **Asymptotic balance collapses**: if for every `δ > 0` the bound `ε_N ≤ δ` holds at infinitely many levels, then
  RH (`rh_of_frequently_balanced`); in particular any normalised bound `ε_N ≤ f(N)` with `f(N) → 0` gives RH
  (`rh_of_tendsto`). So on a nested tower "imperfect but balanced in the limit" is the same as exact balance.
-/
import Mathlib
import BallPole

open Finset Filter

noncomputable section

namespace GravastarTower

open BallWeil

/-- The excess positivity at level `N` is at most `t`: `−Q_N(x) ≤ t·Σ_{n ≤ N} x_n²`. -/
def ExcessLe (N : ℕ) (t : ℝ) : Prop := ∀ x : ℕ → ℝ, -form N x ≤ t * ∑ n ∈ Icc 1 N, x n ^ 2

/-- Truncation of a vector to level `N`: the restriction map of the tower. -/
def trunc (N : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun n => if n ≤ N then x n else 0

lemma sum_trunc {N N' : ℕ} (h : N ≤ N') (x : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ n, g n 0 = 0) :
    ∑ n ∈ Icc 1 N', g n (trunc N x n) = ∑ n ∈ Icc 1 N, g n (x n) := by
  rw [← Finset.sum_subset (Icc_subset_Icc_right h)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp [trunc, (mem_Icc.1 hn).2]
  · intro n _ hn
    have : ¬ n ≤ N := fun h' => hn (mem_Icc.2 ⟨by simp_all, h'⟩)
    simp [trunc, this, hg]

/-- The sections nest: the level-`N` form is the level-`N'` form on truncated vectors. -/
lemma form_trunc {N N' : ℕ} (h : N ≤ N') (x : ℕ → ℝ) : form N' (trunc N x) = form N x := by
  unfold form
  rw [sum_trunc h x (fun m y => ∑ n ∈ Icc 1 N', y * trunc N x n * gram m n) (by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact sum_trunc h x (fun n y => x m * y * gram m n) (by simp)

/-- **Monotonicity of the excess**: a bound at level `N'` holds at every lower level. -/
theorem excess_mono {N N' : ℕ} (h : N ≤ N') {t : ℝ} (hN' : ExcessLe N' t) : ExcessLe N t := by
  intro x
  have := hN' (trunc N x)
  rwa [form_trunc h, sum_trunc h x (fun _ y => y ^ 2) (by simp)] at this

/-- **RH is exact balance at every level**. -/
theorem rh_iff_balance : RiemannHypothesis ↔ ∀ N, ExcessLe N 0 := by
  constructor
  · intro hRH N x
    simp only [zero_mul, neg_nonpos]
    exact form_nonneg hRH N x
  · intro h
    refine rh_iff_form.2 fun N x => ?_
    have := h N (fun n => x n)
    simp only [zero_mul, neg_nonpos] at this
    exact this

/-- **The collapse lemma**: balance up to every `δ > 0` at infinitely many levels is RH. -/
theorem rh_of_frequently_balanced (h : ∀ δ > 0, ∃ᶠ N in atTop, ExcessLe N δ) : RiemannHypothesis := by
  refine rh_iff_balance.2 fun N x => ?_
  simp only [zero_mul]
  set s := ∑ n ∈ Icc 1 N, x n ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg fun n _ => sq_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (s + 1) := div_pos hε (by linarith)
  obtain ⟨N', hb, hN'⟩ := ((h _ hδ).and_eventually (eventually_ge_atTop N)).exists
  have := excess_mono hN' hb x
  have hle : ε / (s + 1) * s ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **Normalised asymptotic balance collapses**: `ε_N ≤ f(N)` with `f(N) → 0` gives RH. -/
theorem rh_of_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) (h : ∀ N, ExcessLe N (f N)) :
    RiemannHypothesis := by
  refine rh_of_frequently_balanced fun δ hδ => Eventually.frequently ?_
  filter_upwards [(hf.eventually (gt_mem_nhds hδ))] with N hN x
  exact (h N x).trans (mul_le_mul_of_nonneg_right hN.le (Finset.sum_nonneg fun n _ => sq_nonneg _))

/-! ## Spheres meeting at a junction (non-nested windows)

Each sphere is a finite window `S ⊆ ℕ₊` with its own section of the form. -/

/-- The form on a window `S`. -/
def formS (S : Finset ℕ) (x : ℕ → ℝ) : ℝ := ∑ m ∈ S, ∑ n ∈ S, x m * x n * gram m n

/-- The cross term between two windows. -/
def cross (S T : Finset ℕ) (x : ℕ → ℝ) : ℝ := ∑ m ∈ S, ∑ n ∈ T, x m * x n * gram m n

/-- **Gluing identity**: on disjoint windows the form is the two sphere forms plus the junction cross terms. -/
theorem formS_union {S T : Finset ℕ} (h : Disjoint S T) (x : ℕ → ℝ) :
    formS (S ∪ T) x = formS S x + formS T x + (cross S T x + cross T S x) := by
  unfold formS cross
  simp only [Finset.sum_union h, Finset.sum_add_distrib]
  ring

/-- Balance on a window. -/
def Balanced (S : Finset ℕ) (t : ℝ) : Prop := ∀ x : ℕ → ℝ, -formS S x ≤ t * ∑ n ∈ S, x n ^ 2

lemma formS_Icc (N : ℕ) (x : ℕ → ℝ) : formS (Icc 1 N) x = form N x := rfl

/-- Balance passes to subwindows (zero outside). -/
lemma balanced_mono {S T : Finset ℕ} (h : S ⊆ T) {t : ℝ} (hT : Balanced T t) : Balanced S t := by
  intro x
  let y : ℕ → ℝ := fun n => if n ∈ S then x n else 0
  have e1 : formS T y = formS S x := by
    unfold formS
    rw [← Finset.sum_subset h (fun m _ hm => by simp [y, hm])]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_subset h (fun n _ hn => by simp [y, hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [y, hm, hn]
  have e2 : ∑ n ∈ T, y n ^ 2 = ∑ n ∈ S, x n ^ 2 := by
    rw [← Finset.sum_subset h (fun n _ hn => by simp [y, hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [y, hn]
  have := hT y
  rwa [e1, e2] at this

/-- **The junction collapse**: if the windows are cofinal (every initial segment lies in windows of arbitrarily
small excess), asymptotic balance is RH. Without cofinality (e.g. disjoint dyadic blocks) the cross terms of
`formS_union` are not controlled by the spheres, and balance on the spheres alone says nothing about them. -/
theorem rh_of_cofinal (W : ℕ → Finset ℕ) (ε : ℕ → ℝ) (hb : ∀ k, Balanced (W k) (ε k))
    (hc : ∀ N, ∀ δ > 0, ∃ k, Icc 1 N ⊆ W k ∧ ε k ≤ δ) : RiemannHypothesis := by
  refine rh_of_frequently_balanced fun δ hδ => Eventually.frequently (Eventually.of_forall fun N x => ?_)
  obtain ⟨k, hk, hε⟩ := hc N δ hδ
  have := balanced_mono hk (hb k) x
  rw [formS_Icc] at this
  exact this.trans (mul_le_mul_of_nonneg_right hε (Finset.sum_nonneg fun n _ => sq_nonneg _))

end GravastarTower

#print axioms GravastarTower.excess_mono
#print axioms GravastarTower.rh_iff_balance
#print axioms GravastarTower.rh_of_frequently_balanced
#print axioms GravastarTower.rh_of_tendsto
#print axioms GravastarTower.formS_union
#print axioms GravastarTower.rh_of_cofinal
