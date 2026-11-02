import Mathlib
import D2Parity
import D2Hdist
import WeilChiPos
import WeilChiB
import CAClosed

/-!
# Wiring `K₁` into the d₂ density

`D2Good.good_of_half` builds `PsiOmega.GoodChar χ_D` from `L(½, χ_D) ≠ 0` (primitive, `≠ 1`, quadratic);
`D2Good.parity_pos` / `D2Good.parity_neg` give parity `0` / `1` from `D2Parity`. With
`K1pos D := PsiOmega.K1C χ_D`, the identity `hK1` (`D2Good.hK1_pos`, `D2Good.hK1_neg`) holds with
`κ = Re ψ(½)` resp. `Re ψ(1)`, and positivity `hpos` from `PsiOmega.K1C_pos`. So
`D2Good.d2_density_pos'` / `D2Good.d2_density_neg'` keep only the hypotheses `L(½, χ_D) ≠ 0` and `hB`.
With Theorem B (`PsiOmega.theoremB`, via `D2Good.B_pos`, `D2Good.B_neg`), `D2Good.d2_density_pos_B` /
`D2Good.d2_density_neg_B` keep only `L(½, χ_D) ≠ 0`, with thresholds `−2c_a`, `c_a = PsiOmega.cA a` the archimedean
constant; with `CAClosed.cA_zero`, `CAClosed.cA_one`, `D2Good.d2_density_pos_closed` /
`D2Good.d2_density_neg_closed` give the thresholds `½ log(27/4)` and `(3/2) log(4/3)`.
**CONDITIONAL (half-plane)** through `D2Hdist`. See `formalisations/d2-density.md`.
-/

namespace D2Good
open Filter Topology MeasureTheory DirichletCharacter PsiOmega GSFund GSEven GSPrim D2Hdist D2Dist D2Density

theorem tri_mul {x y : ℤ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    x * y = 0 ∨ x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp

theorem tri_pow {x : ℤ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (k : ℕ) : x ^ k = 0 ∨ x ^ k = 1 ∨ x ^ k = -1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact tri_mul ih hx

/-- `kron D n ∈ {0, ±1}`. -/
theorem kron_tri (D : ℤ) (n : ℕ) : kron D n = 0 ∨ kron D n = 1 ∨ kron D n = -1 := by
  have h8 : ((ZMod.χ₈ (D : ZMod 8) : ℤ)) = 0 ∨ (ZMod.χ₈ (D : ZMod 8) : ℤ) = 1 ∨
      (ZMod.χ₈ (D : ZMod 8) : ℤ) = -1 := ZMod.isQuadratic_χ₈ _
  have h := tri_mul (tri_pow h8 (n.factorization 2)) (jacobiSym.trichotomy D (n / 2 ^ n.factorization 2))
  have he : kron D n = (((ZMod.χ₈ (D : ZMod 8) : ℤ) ^ (n.factorization 2) *
      jacobiSym D (n / 2 ^ n.factorization 2) : ℤ) : ℂ) := by
    simp [kron]
  rw [he]; rcases h with h | h | h <;> rw [h] <;> simp

theorem quad_of {d : ℕ} [NeZero d] (h1 : 1 < d) (D : ℤ) (χ : DirichletCharacter ℂ d)
    (hv : ∀ n : ℕ, n ≠ 0 → χ n = kron D n) : χ.IsQuadratic := by
  intro a
  rw [← ZMod.natCast_zmod_val a]
  by_cases h0 : a.val = 0
  · left
    haveI : Fact (1 < d) := ⟨h1⟩
    rw [h0, Nat.cast_zero]; exact MulChar.map_nonunit χ not_isUnit_zero
  · rw [hv _ h0]; exact kron_tri D _

theorem good_of {d : ℕ} [NeZero d] (h1 : 1 < d) (D : ℤ) (χ : DirichletCharacter ℂ d) (hp : χ.IsPrimitive)
    (hv : ∀ n : ℕ, n ≠ 0 → χ n = kron D n) (hh : LFunction χ (1 / 2) ≠ 0) : GoodChar χ :=
  ⟨GSTail.ne_one_of_primitive h1 hp, quad_of h1 D χ hv, hp, hh⟩

theorem parity_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ (-1) = 1) : parity χ = 0 := by
  have : χ.Even := h
  simp [parity, this]

theorem parity_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ (-1) = -1) : parity χ = 1 := by
  have : ¬ χ.Even := by
    intro he; have he' : χ (-1) = 1 := he; rw [h] at he'; norm_num at he'
  simp [parity, this]

/-- The re-identity behind `hK1`. -/
theorem re_K1 {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hG : GoodChar χ) :
    K1C χ = Real.log N - Real.log Real.pi + (Complex.digamma ((1 + parity χ) / 2)).re
      + 2 * (deriv (LFunction χ) 1 / LFunction χ 1).re := by
  rw [K1C, (hasSum_K1 hG).tsum_eq, logDeriv_apply]
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.log_re]

open Classical in
/-- `K₁⁺(d) = Σ_ρ 2/(ρ(1−ρ))` for `χ_d`, `d > 1` a positive fundamental discriminant (`0` otherwise). -/
noncomputable def Kp (d : ℕ) : ℝ :=
  if h : fundPos d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    K1C (primitive_pos h.1 h.2).choose
  else 0

open Classical in
/-- `K₁⁻(d)` for `χ_{−d}`. -/
noncomputable def Kn (d : ℕ) : ℝ :=
  if h : fundNeg d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    K1C (primitive_neg h.1).choose
  else 0

open Classical in
/-- The hypothesis `L(½, χ_d) ≠ 0`, positive case. -/
def HalfPos (d : ℕ) : Prop :=
  if h : fundPos d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    LFunction (primitive_pos h.1 h.2).choose (1 / 2) ≠ 0
  else True

open Classical in
/-- The hypothesis `L(½, χ_{−d}) ≠ 0`, negative case. -/
def HalfNeg (d : ℕ) : Prop :=
  if h : fundNeg d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    LFunction (primitive_neg h.1).choose (1 / 2) ≠ 0
  else True

/-- `κ⁺ = Re ψ(½)`. -/
noncomputable def κp : ℝ := (Complex.digamma (1 / 2)).re
/-- `κ⁻ = Re ψ(1)`. -/
noncomputable def κn : ℝ := (Complex.digamma 1).re

theorem pos_facts {d : ℕ} (h : fundPos d ∧ 1 < d) (hh : HalfPos d) :
    Kp d = Real.log d - Real.log Real.pi + κp + 2 * lpos d ∧ 0 < Kp d := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hv⟩ := (primitive_pos h.1 h.2).choose_spec
  have hh' : LFunction (primitive_pos h.1 h.2).choose (1 / 2) ≠ 0 := by
    simpa [HalfPos, h] using hh
  have hG := good_of h.2 d _ hp hv hh'
  have hpar : parity (primitive_pos h.1 h.2).choose = 0 := parity_even (by
    rw [D2Parity.chi_neg_one _ h.2 hv]; exact_mod_cast D2Parity.kron_pos h.1 h.2)
  have hK : Kp d = K1C (primitive_pos h.1 h.2).choose := by simp only [Kp, h, and_self, dite_true]
  have hl : lpos d = (deriv (LFunction (primitive_pos h.1 h.2).choose) 1 /
      LFunction (primitive_pos h.1 h.2).choose 1).re := by simp only [lpos, h, and_self, dite_true]
  refine ⟨?_, hK ▸ K1C_pos hG⟩
  rw [hK, re_K1 hG, hpar, hl, κp]; norm_num

theorem neg_facts {d : ℕ} (h : fundNeg d ∧ 1 < d) (hh : HalfNeg d) :
    Kn d = Real.log d - Real.log Real.pi + κn + 2 * lneg d ∧ 0 < Kn d := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hv⟩ := (primitive_neg h.1).choose_spec
  have hh' : LFunction (primitive_neg h.1).choose (1 / 2) ≠ 0 := by
    simpa [HalfNeg, h] using hh
  have hG := good_of h.2 _ _ hp hv hh'
  have hpar : parity (primitive_neg h.1).choose = 1 := parity_odd (by
    rw [D2Parity.chi_neg_one _ h.2 hv]; exact D2Parity.kron_neg h.1)
  have hK : Kn d = K1C (primitive_neg h.1).choose := by simp only [Kn, h, and_self, dite_true]
  have hl : lneg d = (deriv (LFunction (primitive_neg h.1).choose) 1 /
      LFunction (primitive_neg h.1).choose 1).re := by simp only [lneg, h, and_self, dite_true]
  refine ⟨?_, hK ▸ K1C_pos hG⟩
  rw [hK, re_K1 hG, hpar, hl, κn]; norm_num

/-- `K₁` over `ℤ`, positive discriminants. -/
noncomputable def K1pos (D : ℤ) : ℝ := Kp D.toNat
/-- `K₁` over `ℤ`, negative discriminants. -/
noncomputable def K1neg (D : ℤ) : ℝ := Kn (-D).toNat

theorem hK1_pos (hh : ∀ D, Apos D → HalfPos D.toNat) (D : ℤ) (hD : Apos D) :
    K1pos D = (Real.log (|(D:ℝ)| / Real.pi) + κp) + 2 * ℓpos D ∧ 0 < K1pos D := by
  have h : fundPos D.toNat ∧ 1 < D.toNat := ⟨hD.2, by have := hD.1; omega⟩
  obtain ⟨e, p⟩ := pos_facts h (hh D hD)
  refine ⟨?_, p⟩
  have hc : ((D.toNat : ℕ) : ℝ) = |(D : ℝ)| := by
    rw [abs_of_pos (by have := hD.1; exact_mod_cast (by omega : (0:ℤ) < D))]
    have := hD.1; exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [K1pos, e, ℓpos, ← hc, Real.log_div (Nat.cast_pos.2 (by omega)).ne' Real.pi_ne_zero]

theorem hK1_neg (hh : ∀ D, Aneg D → HalfNeg (-D).toNat) (D : ℤ) (hD : Aneg D) :
    K1neg D = (Real.log (|(D:ℝ)| / Real.pi) + κn) + 2 * ℓneg D ∧ 0 < K1neg D := by
  have h : fundNeg (-D).toNat ∧ 1 < (-D).toNat := ⟨hD.2, by have := hD.1; omega⟩
  obtain ⟨e, p⟩ := neg_facts h (hh D hD)
  refine ⟨?_, p⟩
  have hc : (((-D).toNat : ℕ) : ℝ) = |(D : ℝ)| := by
    rw [abs_of_neg (by have := hD.1; exact_mod_cast (by omega : D < 0))]
    have := hD.1
    have : (((-D).toNat : ℕ) : ℤ) = -D := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [K1neg, e, ℓneg, ← hc, Real.log_div (Nat.cast_pos.2 (by omega)).ne' Real.pi_ne_zero]

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D > 1`**, with `hK1`, `hpos` discharged:
only `L(½, χ_D) ≠ 0` and the `K₂` identity `hB` remain. -/
theorem d2_density_pos' (K2 : ℤ → ℝ) (c : ℝ) (hh : ∀ D, Apos D → HalfPos D.toNat)
    (hB : ∀ D, Apos D → K2 D = √2 * (K1pos D / 2 + c + ℓpos D / 2)) :
    Tendsto (fun x => prop (Spos x) (fun D => 2 * (1 - K2 D ^ 2 / K1pos D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * c))).toReal) :=
  d2_density_pos K1pos K2 c κp (fun D hD => (hK1_pos hh D hD).1) (fun D hD => (hK1_pos hh D hD).2) hB

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D < 0`**, with `hK1`, `hpos` discharged. -/
theorem d2_density_neg' (K2 : ℤ → ℝ) (c : ℝ) (hh : ∀ D, Aneg D → HalfNeg (-D).toNat)
    (hB : ∀ D, Aneg D → K2 D = √2 * (K1neg D / 2 + c + ℓneg D / 2)) :
    Tendsto (fun x => prop (Sneg x) (fun D => 2 * (1 - K2 D ^ 2 / K1neg D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * c))).toReal) :=
  d2_density_neg K1neg K2 c κn (fun D hD => (hK1_neg hh D hD).1) (fun D hD => (hK1_neg hh D hD).2) hB

/-! ## Theorem B wired in: only `L(½, χ_D) ≠ 0` remains -/

open Classical in
/-- `K⁺(2) = Re Σ_ρ 2^{ρ−½}/(ρ(1 − ρ))` for `χ_d` (`0` otherwise). -/
noncomputable def K2p (d : ℕ) : ℝ :=
  if h : fundPos d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    (KxC (primitive_pos h.1 h.2).choose 2).re
  else 0

open Classical in
/-- `K⁻(2)` for `χ_{−d}`. -/
noncomputable def K2n (d : ℕ) : ℝ :=
  if h : fundNeg d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    (KxC (primitive_neg h.1).choose 2).re
  else 0

theorem B_pos {d : ℕ} (h : fundPos d ∧ 1 < d) (hh : HalfPos d) :
    K2p d = √2 * (Kp d / 2 + cA 0 + lpos d / 2) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hv⟩ := (primitive_pos h.1 h.2).choose_spec
  have hh' : LFunction (primitive_pos h.1 h.2).choose (1 / 2) ≠ 0 := by
    simpa [HalfPos, h] using hh
  have hG := good_of h.2 d _ hp hv hh'
  have hpar : parity (primitive_pos h.1 h.2).choose = 0 := parity_even (by
    rw [D2Parity.chi_neg_one _ h.2 hv]; exact_mod_cast D2Parity.kron_pos h.1 h.2)
  have hK : Kp d = K1C (primitive_pos h.1 h.2).choose := by simp only [Kp, h, and_self, dite_true]
  have hK2 : K2p d = (KxC (primitive_pos h.1 h.2).choose 2).re := by simp only [K2p, h, and_self, dite_true]
  have hl : lpos d = (deriv (LFunction (primitive_pos h.1 h.2).choose) 1 /
      LFunction (primitive_pos h.1 h.2).choose 1).re := by simp only [lpos, h, and_self, dite_true]
  rw [hK2, theoremB hG, cB_eq, hpar, hK, hl]

theorem B_neg {d : ℕ} (h : fundNeg d ∧ 1 < d) (hh : HalfNeg d) :
    K2n d = √2 * (Kn d / 2 + cA 1 + lneg d / 2) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hp, hv⟩ := (primitive_neg h.1).choose_spec
  have hh' : LFunction (primitive_neg h.1).choose (1 / 2) ≠ 0 := by
    simpa [HalfNeg, h] using hh
  have hG := good_of h.2 _ _ hp hv hh'
  have hpar : parity (primitive_neg h.1).choose = 1 := parity_odd (by
    rw [D2Parity.chi_neg_one _ h.2 hv]; exact D2Parity.kron_neg h.1)
  have hK : Kn d = K1C (primitive_neg h.1).choose := by simp only [Kn, h, and_self, dite_true]
  have hK2 : K2n d = (KxC (primitive_neg h.1).choose 2).re := by simp only [K2n, h, and_self, dite_true]
  have hl : lneg d = (deriv (LFunction (primitive_neg h.1).choose) 1 /
      LFunction (primitive_neg h.1).choose 1).re := by simp only [lneg, h, and_self, dite_true]
  rw [hK2, theoremB hG, cB_eq, hpar, hK, hl]

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D > 1`**, with `hK1`, `hpos` and Theorem B (`hB`)
discharged: given `L(½, χ_D) ≠ 0`, the proportion of `D` with `d₂/d₁ = 2(1 − K(2)²/K₁²) < 1` tends to
`ν(−2c₀, ∞)`, `c₀ = PsiOmega.cA 0`. -/
theorem d2_density_pos_B (hh : ∀ D, Apos D → HalfPos D.toNat) :
    Tendsto (fun x => prop (Spos x) (fun D => 2 * (1 - K2p D.toNat ^ 2 / K1pos D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * cA 0))).toReal) :=
  d2_density_pos' (fun D => K2p D.toNat) (cA 0) hh fun D hD =>
    B_pos ⟨hD.2, by have := hD.1; omega⟩ (hh D hD)

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D < 0`**, with `hK1`, `hpos`, `hB` discharged:
the limit is `ν(−2c₁, ∞)`, `c₁ = PsiOmega.cA 1`. -/
theorem d2_density_neg_B (hh : ∀ D, Aneg D → HalfNeg (-D).toNat) :
    Tendsto (fun x => prop (Sneg x) (fun D => 2 * (1 - K2n (-D).toNat ^ 2 / K1neg D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (-2 * cA 1))).toReal) :=
  d2_density_neg' (fun D => K2n (-D).toNat) (cA 1) hh fun D hD =>
    B_neg ⟨hD.2, by have := hD.1; omega⟩ (hh D hD)

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D > 1`, with the explicit threshold**: given
`L(½, χ_D) ≠ 0`, the proportion tends to `ν(½ log(27/4), ∞)` (`c₀ = −¼ log(27/4)`, `CAClosed.cA_zero`). -/
theorem d2_density_pos_closed (hh : ∀ D, Apos D → HalfPos D.toNat) :
    Tendsto (fun x => prop (Spos x) (fun D => 2 * (1 - K2p D.toNat ^ 2 / K1pos D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (Real.log (27 / 4) / 2))).toReal) := by
  have h := d2_density_pos_B hh
  rwa [CAClosed.cA_zero, show -2 * (-(1 / 4) * Real.log (27 / 4)) = Real.log (27 / 4) / 2 by ring] at h

/-- **CONDITIONAL (half-plane). The d₂ < d₁ density, `D < 0`, with the explicit threshold**: the limit is
`ν((3/2) log(4/3), ∞)` (`c₁ = ¾ log(3/4)`, `CAClosed.cA_one`). -/
theorem d2_density_neg_closed (hh : ∀ D, Aneg D → HalfNeg (-D).toNat) :
    Tendsto (fun x => prop (Sneg x) (fun D => 2 * (1 - K2n (-D).toNat ^ 2 / K1neg D ^ 2) < 1)) atTop
      (𝓝 ((RandModel.ν : Measure ℝ) (Set.Ioi (3 / 2 * Real.log (4 / 3)))).toReal) := by
  have h := d2_density_neg_B hh
  have e : -2 * (3 / 4 * Real.log (3 / 4)) = 3 / 2 * Real.log (4 / 3) := by
    rw [show (4 / 3 : ℝ) = (3 / 4)⁻¹ by norm_num, Real.log_inv]; ring
  rwa [CAClosed.cA_one, e] at h

end D2Good
