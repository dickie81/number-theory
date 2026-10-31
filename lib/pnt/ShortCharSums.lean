/-
# Short character sums

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `η > 0` there is `C` such that `|Σ_{n≤X} χ(n)| ≤ C(q + 2)^η X^{11/12+η}` for every
modulus `q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ 1` (`norm_sum_le`). So the sums cancel
from length `q^δ` on, for every `δ > 0`: for every `ε > 0` there is `C` with `|Σ_{n≤X} χ(n)| ≤ CX^{11/12+ε}` whenever
`X ≥ q^δ` (`norm_sum_le_rpow`), and `Σ_{n≤X} χ(n) = o(X)` on `X ≥ q^δ`, uniformly in `q` and `χ`
(`norm_sum_le_mul`). For the Legendre symbol: for every odd prime `p`, the quadratic residues and the non-residues
mod `p` in `[1, X]` differ in number by at most `CX^{11/12+ε}` whenever `X ≥ p^δ` (`card_squares_sub_le`), so each
makes up half of `[1, X]` up to `o(X)`. No hypothesis.

D. A. Burgess's bound (1962–63) gives `Σ_{n≤X} χ(n) = o(X)` for `X ≥ q^{1/4+ε}`, `q` cube-free, and the generalised
Lindelöf hypothesis gives it for `X ≥ q^δ`. Here the range `X ≥ q^δ` follows from the Lindelöf bound on
`Re s > 11/12` (`LinnikLindelof.lindelof`), which rests on the half-plane.

* `norm_sum_le`: `MertensChi.norm_sum_le_of` at `θ = 11/12` and `η₀ = min(η, 1/24)` with `F = L(·, χ)`, entire for
  `χ ≠ 1` (Mathlib's `DirichletCharacter.differentiable_LFunction`), and the direct half of `LinnikLindelof.lindelof`
  (`|L(σ + it, χ)| ≤ C₀((q + 2)(|t| + 4))^{η₀/8}`), so that `A = C₀(q + 2)^{η₀/8}`. The coefficient `χ(0)` is `0`
  since `χ ≠ 1` forces `q ≠ 1`.
* `norm_sum_le_rpow`: `norm_sum_le` at `η = εδ/(1 + δ)`, with `(q + 2)^η ≤ (3X^{1/δ})^η = 3^η X^{η/δ}` and
  `η + η/δ = ε`.
* `norm_sum_le_mul`: `norm_sum_le_rpow` at `ε = 1/24`, with `CX^{23/24} ≤ ηX` once `X ≥ (C/η)^{24}`.
* `card_squares_sub_le`: `norm_sum_le_rpow` for `LeastNonresidue.legendreChar p`, which is `1` at the residues, `−1`
  at the non-residues and `0` at the multiples of `p` (`legendreChar_eq`).
-/
import MertensChi
import LeastNonresidue

open Complex Real DirichletCharacter

noncomputable section

namespace ShortCharSums

/-- **Character sums, uniformly in the modulus.** For every `η > 0` there is `C > 0` such that for every modulus
`q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ 1`, `|Σ_{n≤X} χ(n)| ≤ C(q + 2)^η X^{11/12+η}`:
Perron's formula (`MertensChi.norm_sum_le_of`) for `L(s, χ)` with the Lindelöf bound `LinnikLindelof.lindelof`. -/
theorem norm_sum_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 1 ≤ X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n‖ ≤ C * ((q : ℝ) + 2) ^ η * X ^ (11 / 12 + η) := by
  set η₀ : ℝ := min η (1 / 24) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by norm_num)
  have hη₀η : η₀ ≤ η := min_le_left _ _
  have hη₀1 : η₀ ≤ 1 / 24 := min_le_right _ _
  obtain ⟨C, hC0, hC⟩ := MertensChi.norm_sum_le_of (θ := 11 / 12) (by norm_num) hη₀ (by linarith)
  obtain ⟨C₀, hC₀, hL⟩ := LinnikLindelof.lindelof (σ₀ := 11 / 12 + η₀ / 4) (by linarith)
    (by positivity : 0 < η₀ / 8)
  refine ⟨C * C₀ + 4, by positivity, fun q _ χ hχ X hX ↦ ?_⟩
  have hq2 : (1 : ℝ) ≤ (q : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.2 fun h ↦ hχ (level_one' χ h)
  have h := hC (fun n ↦ χ n) (LFunction χ) (C₀ * ((q : ℝ) + 2) ^ (η₀ / 8)) (by positivity)
    (by simp only [Nat.cast_zero]; exact MulChar.map_zero χ) (fun n ↦ norm_le_one χ n)
    (LSeriesSummable_of_one_lt_re χ (by norm_num)) (fun s hs ↦ (LFunction_eq_LSeries χ hs).symm)
    (fun s _ ↦ differentiable_LFunction hχ s)
    (fun σ t hσ ↦ (hL q χ hχ σ t hσ).1.trans_eq (by rw [Real.mul_rpow (by positivity) (by positivity)]; ring))
    X hX
  refine h.trans ?_
  have hqη : ((q : ℝ) + 2) ^ (η₀ / 8) ≤ ((q : ℝ) + 2) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hq2 (by linarith)
  have hqη1 : 1 ≤ ((q : ℝ) + 2) ^ η := Real.one_le_rpow hq2 hη.le
  have hX' : X ^ (11 / 12 + η₀) ≤ X ^ (11 / 12 + η) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  calc (C * (C₀ * ((q : ℝ) + 2) ^ (η₀ / 8)) + 4) * X ^ (11 / 12 + η₀)
      ≤ (C * (C₀ * ((q : ℝ) + 2) ^ η) + 4 * ((q : ℝ) + 2) ^ η) * X ^ (11 / 12 + η) := by
        gcongr
        linarith
    _ = (C * C₀ + 4) * ((q : ℝ) + 2) ^ η * X ^ (11 / 12 + η) := by ring

/-- **Short character sums.** For every `δ > 0` and `ε > 0` there is `C > 0` such that for every modulus `q ≥ 1`,
every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ 1` with `X ≥ q^δ`, `|Σ_{n≤X} χ(n)| ≤ CX^{11/12+ε}`. -/
theorem norm_sum_le_rpow {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 1 ≤ X →
      (q : ℝ) ^ δ ≤ X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n‖ ≤ C * X ^ (11 / 12 + ε) := by
  set η : ℝ := ε * δ / (1 + δ) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hδ0 : δ ≠ 0 := hδ.ne'
  have h1δ : 1 + δ ≠ 0 := (by linarith : (0 : ℝ) < 1 + δ).ne'
  have hexp : η + η / δ = ε := by
    rw [hηdef]
    field_simp
    ring
  obtain ⟨C, hC0, hC⟩ := norm_sum_le hη
  refine ⟨C * 3 ^ η, by positivity, fun q _ χ hχ X hX hqX ↦ ?_⟩
  have Xpos : 0 < X := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqX' : (q : ℝ) ≤ X ^ (1 / δ) := by
    calc (q : ℝ) = ((q : ℝ) ^ δ) ^ (1 / δ) := by
          rw [← Real.rpow_mul hq0, mul_one_div_cancel hδ.ne', Real.rpow_one]
      _ ≤ X ^ (1 / δ) := Real.rpow_le_rpow (by positivity) hqX (by positivity)
  have hX1δ : 1 ≤ X ^ (1 / δ) := Real.one_le_rpow hX (by positivity)
  have hq2 : ((q : ℝ) + 2) ^ η ≤ 3 ^ η * X ^ (η / δ) := by
    calc ((q : ℝ) + 2) ^ η ≤ (3 * X ^ (1 / δ)) ^ η := by gcongr; linarith
      _ = 3 ^ η * X ^ (η / δ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul Xpos.le,
            show 1 / δ * η = η / δ by ring]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n‖ ≤ C * ((q : ℝ) + 2) ^ η * X ^ (11 / 12 + η) := hC q χ hχ X hX
    _ ≤ C * (3 ^ η * X ^ (η / δ)) * X ^ (11 / 12 + η) := by gcongr
    _ = C * 3 ^ η * (X ^ (η / δ) * X ^ (11 / 12 + η)) := by ring
    _ = C * 3 ^ η * X ^ (11 / 12 + ε) := by
        rw [← Real.rpow_add Xpos, show η / δ + (11 / 12 + η) = 11 / 12 + ε by linarith]

/-- **Short character sums are `o(X)`.** For every `δ > 0` and `η > 0` there is `X₀` such that for every modulus
`q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ X₀` with `X ≥ q^δ`, `|Σ_{n≤X} χ(n)| ≤ ηX`. -/
theorem norm_sum_le_mul {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, X₀ ≤ X →
      (q : ℝ) ^ δ ≤ X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n‖ ≤ η * X := by
  obtain ⟨C, hC0, hC⟩ := norm_sum_le_rpow hδ (by norm_num : (0 : ℝ) < 1 / 24)
  refine ⟨max 1 ((C / η) ^ (24 : ℝ)), fun q _ χ hχ X hX hqX ↦ ?_⟩
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have Xpos : 0 < X := by linarith
  have hCη : 0 ≤ C / η := by positivity
  have h24 : C / η ≤ X ^ (1 / 24 : ℝ) := by
    calc C / η = ((C / η) ^ (24 : ℝ)) ^ (1 / 24 : ℝ) := by
          rw [← Real.rpow_mul hCη]; norm_num
      _ ≤ X ^ (1 / 24 : ℝ) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hX) (by norm_num)
  have h24' : C ≤ η * X ^ (1 / 24 : ℝ) := by
    have := (div_le_iff₀ hη).1 h24
    linarith
  refine (hC q χ hχ X hX1 hqX).trans ?_
  calc C * X ^ (11 / 12 + 1 / 24 : ℝ) ≤ η * X ^ (1 / 24 : ℝ) * X ^ (11 / 12 + 1 / 24 : ℝ) := by gcongr
    _ = η * X := by
        rw [mul_assoc, ← Real.rpow_add Xpos]
        norm_num

/-- The Legendre symbol mod `p` is `1` at the nonzero squares, `−1` at the non-squares and `0` at `0`. -/
lemma legendreChar_eq (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    LeastNonresidue.legendreChar p a = (if IsSquare a ∧ a ≠ 0 then 1 else 0) - (if ¬IsSquare a then 1 else 0) := by
  rw [LeastNonresidue.legendreChar_apply]
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases hs : IsSquare a
    · simp [h0, hs, (quadraticChar_one_iff_isSquare h0).2 hs]
    · simp [h0, hs, quadraticChar_neg_one_iff_not_isSquare.2 hs]

/-- **Quadratic residues in short intervals.** For every `δ > 0` and `ε > 0` there is `C > 0` such that for every odd
prime `p` and every `X ≥ 1` with `X ≥ p^δ`, the quadratic residues mod `p` in `[1, X]` and the non-residues there
differ in number by at most `CX^{11/12+ε}`. -/
theorem card_squares_sub_le {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : ℝ, 1 ≤ X → (p : ℝ) ^ δ ≤ X →
      |(((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ ↦ IsSquare (n : ZMod p) ∧ (n : ZMod p) ≠ 0).card : ℝ) -
        ((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ ↦ ¬IsSquare (n : ZMod p)).card| ≤ C * X ^ (11 / 12 + ε) := by
  obtain ⟨C, hC0, hC⟩ := norm_sum_le_rpow hδ hε
  refine ⟨C, hC0, fun p hp hp2 X hX hpX ↦ ?_⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h := hC p (LeastNonresidue.legendreChar p) (LeastNonresidue.legendreChar_ne_one p hp2) X hX hpX
  simp only [legendreChar_eq, Finset.sum_sub_distrib, Finset.sum_boole] at h
  rwa [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h

end ShortCharSums

#print axioms ShortCharSums.norm_sum_le
#print axioms ShortCharSums.norm_sum_le_rpow
#print axioms ShortCharSums.norm_sum_le_mul
#print axioms ShortCharSums.card_squares_sub_le
