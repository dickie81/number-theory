/-
# Weng's rank-2 zeta function of `ℚ` satisfies the Riemann hypothesis

Plain statement. L. Weng's zeta function of the rank-2 semistable lattices over `ℚ` is
`ζ̂_{ℚ,2}(s) = ξ̂(2s)/(s − 1) − ξ̂(2s − 1)/s` (`weng`), with `ξ̂ = completedRiemannZeta`. J. C. Lagarias and M. Suzuki
proved that all its zeros lie on `Re s = ½` ("Riemann hypothesis for certain integrals of Eisenstein series",
J. Number Theory 118 (2006); it is their truncation integral at `T = 1`). Here:
* **The entire form** (`weng_eq`): with Riemann's `ξ(s) = ½s(s − 1)ξ̂(s)`,
  `ζ̂_{ℚ,2}(s) = (ξ(2s) − ξ(2s − 1))/(s(s − 1)(2s − 1))` off `s = 0, ½, 1`. The numerator vanishes at `½`, where the
  poles of the two terms cancel.
* **The functional equation** (`weng_one_sub`): `ζ̂_{ℚ,2}(1 − s) = ζ̂_{ℚ,2}(s)`; the numerator changes sign
  (`wengNum_one_sub`).
* **The domination** (`norm_xi_lt`): `|ξ(2s − 1)| < |ξ(2s)|` for `Re s > ½`. With `t = (2s − ½)/i`, `ξ(2s − 1)` is the
  conjugate of `Ξ` at the mirror image `t̄ − i` of `t` across the line `Re w = 1` of `w = 2s`, and every zero of `ξ`
  lies left of that line (`XiReflection.reflect_one`, `XiReflection.Xi_conj`).
* **The Riemann hypothesis, with no hypothesis** (`rh_wengNum`, `rh_weng`): every zero of `ξ(2s) − ξ(2s − 1)`, and
  every zero of `ζ̂_{ℚ,2}` other than `0` and `1`, has `Re s = ½`. In `Ξ` (`differenced_real`): the differenced
  function `Ξ(T − i/2) − Ξ(T + i/2)` has only real zeros.
Not formalised: Weng's identification of `ζ̂_{ℚ,2}` with the integral of `(e^{h⁰(Λ)} − 1)e^{−s·deg Λ}` over the moduli
of rank-2 semistable lattices; in rank 1 the same integral is `ξ̂` (`ArakelovRiemannRoch.Z_eq_integral` at `w = 1`).
The proof uses only that the zeros of `ξ(2s)` lie in `0 < Re s < ½`, left of the line: the Riemann hypothesis for
`ζ̂_{ℚ,2}` carries no information about the zeros of `ζ`. RH for `ζ` is the same reflection inequality across every
line `Re s = c > ½` (`XiReflection.rh_iff_reflect_xi`).
-/
import Mathlib
import XiReflection

open Complex ComplexConjugate

noncomputable section

namespace WengRankTwo

open WeilForm XiReflection

/-- **Weng's rank-2 zeta function of `ℚ`**, `ξ̂(2s)/(s − 1) − ξ̂(2s − 1)/s`. -/
def weng (s : ℂ) : ℂ := completedRiemannZeta (2 * s) / (s - 1) - completedRiemannZeta (2 * s - 1) / s

/-- Its numerator `ξ(2s) − ξ(2s − 1)`, entire. -/
def wengNum (s : ℂ) : ℂ := xi (2 * s) - xi (2 * s - 1)

/-- **The entire form**: off `s = 0, ½, 1`, `ζ̂_{ℚ,2}(s) = (ξ(2s) − ξ(2s − 1))/(s(s − 1)(2s − 1))`. -/
theorem weng_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    weng s = wengNum s / (s * (s - 1) * (2 * s - 1)) := by
  have a0 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero h0
  have a1 : 2 * s ≠ 1 := fun h => h1 (by linear_combination h / 2)
  have b0 : 2 * s - 1 ≠ 0 := sub_ne_zero.2 a1
  have b1 : 2 * s - 1 ≠ 1 := fun h => h2 (by linear_combination h / 2)
  have c1 : s - 1 ≠ 0 := sub_ne_zero.2 h2
  unfold weng wengNum
  rw [xi_eq a0 a1, xi_eq b0 b1]
  field_simp
  ring

/-- **The functional equation** `ζ̂_{ℚ,2}(1 − s) = ζ̂_{ℚ,2}(s)`. -/
theorem weng_one_sub (s : ℂ) : weng (1 - s) = weng s := by
  unfold weng
  have e1 : completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    rw [← completedRiemannZeta_one_sub (2 * s - 1)]
    congr 1
    ring
  have e2 : completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    rw [← completedRiemannZeta_one_sub (2 * s)]
    congr 1
    ring
  rw [e1, e2, show (1 : ℂ) - s - 1 = -s by ring, show (1 : ℂ) - s = -(s - 1) by ring, div_neg, div_neg]
  ring

/-- The numerator changes sign: `ξ(2(1 − s)) − ξ(2(1 − s) − 1) = −(ξ(2s) − ξ(2s − 1))`. -/
theorem wengNum_one_sub (s : ℂ) : wengNum (1 - s) = -wengNum s := by
  unfold wengNum
  rw [show 2 * (1 - s) = 1 - (2 * s - 1) by ring, xi_one_sub,
    show 1 - (2 * s - 1) - 1 = 1 - 2 * s by ring, xi_one_sub]
  ring

/-- **The domination**: `‖ξ(2s − 1)‖ < ‖ξ(2s)‖` for `Re s > ½`, by reflection across `Re(2s) = 1`. -/
theorem norm_xi_lt {s : ℂ} (hs : 1 / 2 < s.re) : ‖xi (2 * s - 1)‖ < ‖xi (2 * s)‖ := by
  set z : ℂ := (2 * s - 1 / 2) / I with hz
  have hXi : Xi z = xi (2 * s) := Xi_at_ordinate _
  have him : z.im < -(1 / 2) := by
    rw [hz, im_ordinate]
    simp
    linarith
  have h := reflect_one him
  have e : Xi (conj z - I) = conj (xi (2 * s - 1)) := by
    rw [show conj z - I = conj (z + I) by simp [map_add, conj_I, sub_eq_add_neg], Xi_conj]
    congr 1
    unfold Xi
    congr 1
    rw [hz]
    apply Complex.ext <;> simp [div_I]
    ring
  rw [e, norm_conj, hXi] at h
  exact h

/-- **The Riemann hypothesis for the numerator**: every zero of `ξ(2s) − ξ(2s − 1)` has `Re s = ½`. -/
theorem rh_wengNum {s : ℂ} (h : wengNum s = 0) : s.re = 1 / 2 := by
  have key : ∀ w : ℂ, 1 / 2 < w.re → wengNum w ≠ 0 := fun w hw h0 => by
    have h' := norm_xi_lt hw
    rw [wengNum, sub_eq_zero] at h0
    rw [h0] at h'
    exact lt_irrefl _ h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h' := key (1 - s) (by simp; linarith)
    rw [wengNum_one_sub, h, neg_zero] at h'
    exact h' rfl
  · exact key s hgt h

/-- **The Riemann hypothesis for Weng's rank-2 zeta function of `ℚ`** (Lagarias–Suzuki): every zero other than `0`
and `1` has `Re s = ½`. -/
theorem rh_weng {s : ℂ} (h : weng s = 0) (h0 : s ≠ 0) (h2 : s ≠ 1) : s.re = 1 / 2 := by
  by_cases h1 : s = 1 / 2
  · rw [h1]
    norm_num
  rw [weng_eq h0 h1 h2, div_eq_zero_iff] at h
  rcases h with h | h
  · exact rh_wengNum h
  · exfalso
    have c1 : s - 1 ≠ 0 := sub_ne_zero.2 h2
    have c2 : 2 * s - 1 ≠ 0 := fun h' => h1 (by linear_combination h' / 2)
    exact mul_ne_zero (mul_ne_zero h0 c1) c2 h

/-- **The differenced `Ξ`**: `Ξ(T − i/2) − Ξ(T + i/2)` has only real zeros. -/
theorem differenced_real {T : ℂ} (h : Xi (T - I / 2) - Xi (T + I / 2) = 0) : T.im = 0 := by
  have e : wengNum (1 / 2 + I * T / 2) = Xi (T - I / 2) - Xi (T + I / 2) := by
    unfold wengNum Xi
    rw [show 2 * (1 / 2 + I * T / 2) = 1 / 2 + I * (T - I / 2) by linear_combination (1 / 2 : ℂ) * I_sq,
      show 1 / 2 + I * (T - I / 2) - 1 = 1 / 2 + I * (T + I / 2) by linear_combination (-1 : ℂ) * I_sq]
  have h' := rh_wengNum (e.trans h)
  simp at h'
  linarith

end WengRankTwo

#print axioms WengRankTwo.weng_eq
#print axioms WengRankTwo.weng_one_sub
#print axioms WengRankTwo.wengNum_one_sub
#print axioms WengRankTwo.norm_xi_lt
#print axioms WengRankTwo.rh_wengNum
#print axioms WengRankTwo.rh_weng
#print axioms WengRankTwo.differenced_real
