/-
# `ζ` has infinitely many nontrivial zeros

Plain statement. The nontrivial zeros of Mathlib's `riemannZeta`, counted with multiplicity, are infinitely many
(`infinite_ZIdx`). No hypothesis.

* If the zero pairs of `Ξ(t) = ξ(½ + it)` were finitely many, Hadamard's factorisation `Ξ(z) = Ξ(0)Π_i(1 − z²/u_i)`
  (`hadamardW_Xi`) would make `Ξ` a polynomial: `‖Ξ(z)‖ ≤ ‖Ξ(0)‖(1 + ‖z‖²W)^N`, with `N` the number of pairs and
  `W = Σ_i |u_i|^{−1}`.
* But `ξ(s) = ½s(s − 1)π^{−s/2}Γ(s/2)ζ(s)`, so `ξ(2m + 2) ≥ m!/π^{m+1}` with `ζ(2m + 2) ≥ 1` (`norm_xi_ge`), and
  `m!` outgrows every `C·x^m` (`FloorSemiring.tendsto_pow_div_factorial_atTop`).

J. Hadamard (1893): `ξ` has order `1` and is not of the form `e^{a + bs}P(s)`. The library had one zero, from Hadamard's
identity `Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π` (`PsiOmega.exists_zero_re_ge_half`).
-/
import Mathlib
import WeilRH

open Complex Finset Filter Topology WeilForm WeilTest

noncomputable section

namespace ZerosInfinite

/-- `ξ(s) = ½s(s − 1)Γℝ(s)ζ(s)` away from `0` and `1`. -/
lemma xi_eq {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) : xi s = s * (s - 1) * (riemannZeta s * Gammaℝ s) / 2 := by
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hG]
  rw [hz, completedRiemannZeta_eq]
  unfold xi
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  field_simp
  ring

/-- **`‖ξ(2m + 2)‖ ≥ m!/π^{m+1}`**: `ξ(2m + 2) = (m + 1)(2m + 1)·π^{−(m+1)}·m!·ζ(2m + 2)` with `ζ(2m + 2) ≥ 1`. -/
lemma norm_xi_ge (m : ℕ) : (m.factorial : ℝ) / Real.pi ^ (m + 1) ≤ ‖xi ((2 * m + 2 : ℕ) : ℂ)‖ := by
  set s : ℂ := ((2 * m + 2 : ℕ) : ℂ) with hs
  have h0 : 0 < s.re := by rw [hs, Complex.natCast_re]; exact_mod_cast (by omega : 0 < 2 * m + 2)
  have h1 : s ≠ 1 := by rw [hs]; exact_mod_cast (by omega : 2 * m + 2 ≠ 1)
  rw [xi_eq h0 h1]
  -- `Γℝ(2m + 2) = π^{−(m+1)}·m!`
  have hG : Gammaℝ s = ((Real.pi ^ (m + 1))⁻¹ * m.factorial : ℝ) := by
    unfold Gammaℝ
    have e1 : -s / 2 = -((m + 1 : ℕ) : ℂ) := by rw [hs]; push_cast; ring
    have e2 : s / 2 = ((m : ℕ) : ℂ) + 1 := by rw [hs]; push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    ring
  -- `ζ(2m + 2) ≥ 1`
  have hk : 1 < 2 * m + 2 := by omega
  have hζ : riemannZeta s = ((∑' n : ℕ, 1 / (n : ℝ) ^ (2 * m + 2) : ℝ) : ℂ) := by
    rw [hs, zeta_nat_eq_tsum_of_gt_one hk, Complex.ofReal_tsum]
    push_cast
    rfl
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 * m + 2) := Real.summable_one_div_nat_pow.2 hk
  have hζ1 : 1 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * m + 2) := by
    have := hsum.le_tsum 1 (fun j _ => by positivity)
    simpa using this
  have hss : s * (s - 1) / 2 = (((m + 1) * (2 * m + 1) : ℕ) : ℝ) := by rw [hs]; push_cast; ring
  have hm1 : (1 : ℝ) ≤ (((m + 1) * (2 * m + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hB : 0 ≤ (Real.pi ^ (m + 1))⁻¹ * (m.factorial : ℝ) := by positivity
  rw [show s * (s - 1) * (riemannZeta s * Gammaℝ s) / 2 = s * (s - 1) / 2 * riemannZeta s * Gammaℝ s by ring,
    norm_mul, norm_mul, hss, hζ, hG, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hB]
  calc (m.factorial : ℝ) / Real.pi ^ (m + 1) = 1 * 1 * ((Real.pi ^ (m + 1))⁻¹ * m.factorial) := by ring
    _ ≤ (((m + 1) * (2 * m + 1) : ℕ) : ℝ) * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * m + 2)) *
        ((Real.pi ^ (m + 1))⁻¹ * m.factorial) := by gcongr

/-- **`ζ` has infinitely many zero pairs**: the index `ZeroIdx (sqF Ξ)` of Hadamard's factorisation is infinite. -/
theorem infinite_ZeroIdx : Infinite (ZeroIdx (sqF Xi)) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite (ZeroIdx (sqF Xi))
  have H := hadamardW_Xi xiGrowth Xi_zero_ne_zero
  set W : ℝ := ∑ i : ZeroIdx (sqF Xi), ‖i.1⁻¹‖ with hW
  set N : ℕ := Fintype.card (ZeroIdx (sqF Xi)) with hN
  have hW0 : 0 ≤ W := by positivity
  -- `Ξ` is a polynomial
  have hpoly : ∀ z : ℂ, ‖Xi z‖ ≤ ‖Xi 0‖ * (1 + ‖z‖ ^ 2 * W) ^ N := by
    intro z
    have hp := (H.prod z).unique (hasProd_fintype _)
    have hX : Xi z = Xi 0 * ∏ i : ZeroIdx (sqF Xi), (1 - z ^ 2 * i.1⁻¹) := by
      rw [← hp, mul_div_cancel₀ _ Xi_zero_ne_zero]
    rw [hX, norm_mul, norm_prod]
    gcongr
    calc ∏ i : ZeroIdx (sqF Xi), ‖1 - z ^ 2 * i.1⁻¹‖ ≤ ∏ _i : ZeroIdx (sqF Xi), (1 + ‖z‖ ^ 2 * W) := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          calc ‖1 - z ^ 2 * i.1⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 * i.1⁻¹‖ := norm_sub_le _ _
            _ = 1 + ‖z‖ ^ 2 * ‖i.1⁻¹‖ := by rw [norm_one, norm_mul, norm_pow]
            _ ≤ 1 + ‖z‖ ^ 2 * W := by
                gcongr
                exact Finset.single_le_sum (f := fun j : ZeroIdx (sqF Xi) => ‖j.1⁻¹‖)
                  (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ = (1 + ‖z‖ ^ 2 * W) ^ N := by rw [Finset.prod_const, Finset.card_univ]
  -- so `m! ≤ C·x^m`
  set x : ℝ := Real.pi * 4 ^ N with hx
  set C : ℝ := Real.pi * ‖Xi 0‖ * (1 + 4 * W) ^ N with hC
  have hbound : ∀ m : ℕ, (m.factorial : ℝ) ≤ C * x ^ m := by
    intro m
    have hz : xi ((2 * m + 2 : ℕ) : ℂ) = Xi (-I * ((2 * m + 3 / 2 : ℝ) : ℂ)) := by
      unfold Xi
      congr 1
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have h1 := norm_xi_ge m
    rw [hz] at h1
    have h2 := hpoly (-I * ((2 * m + 3 / 2 : ℝ) : ℂ))
    have hnz : ‖-I * ((2 * m + 3 / 2 : ℝ) : ℂ)‖ = 2 * m + 3 / 2 := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnz] at h2
    have hm2 : (1 : ℝ) + (2 * m + 3 / 2) ^ 2 * W ≤ (1 + 4 * W) * ((m : ℝ) + 1) ^ 2 := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hm3 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    have hm4 : ((m : ℝ) + 1) ^ 2 ≤ 4 ^ m := by
      calc ((m : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by gcongr
        _ = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hpi : 0 < Real.pi ^ (m + 1) := by positivity
    have h3 : (m.factorial : ℝ) ≤ Real.pi ^ (m + 1) * (‖Xi 0‖ * ((1 + 4 * W) * ((m : ℝ) + 1) ^ 2) ^ N) := by
      rw [← div_le_iff₀' hpi]
      refine h1.trans (h2.trans ?_)
      gcongr
    have hid : Real.pi ^ (m + 1) * (‖Xi 0‖ * ((1 + 4 * W) * 4 ^ m) ^ N) = C * x ^ m := by
      rw [hC, hx, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m N]
      ring
    calc (m.factorial : ℝ) ≤ Real.pi ^ (m + 1) * (‖Xi 0‖ * ((1 + 4 * W) * ((m : ℝ) + 1) ^ 2) ^ N) := h3
      _ ≤ Real.pi ^ (m + 1) * (‖Xi 0‖ * ((1 + 4 * W) * 4 ^ m) ^ N) := by gcongr
      _ = C * x ^ m := hid
  -- and `x^m/m! → 0`
  have hC0 : 0 < C := by
    have := norm_pos_iff.2 Xi_zero_ne_zero
    positivity
  obtain ⟨m, hm⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop x).eventually
    (gt_mem_nhds (inv_pos.2 hC0))).exists
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_lt_iff₀ hf] at hm
  have := hbound m
  have : C * x ^ m < m.factorial := by
    calc C * x ^ m < C * (C⁻¹ * m.factorial) := by gcongr
      _ = m.factorial := by field_simp
  linarith

/-- **`ζ` has infinitely many nontrivial zeros**, counted with multiplicity. -/
theorem infinite_ZIdx : Infinite ZIdx := by
  have := infinite_ZeroIdx
  exact Infinite.of_injective (fun i : ZeroIdx (sqF Xi) => zetaEquiv.symm (true, i)) fun a b h => by
    simpa using zetaEquiv.symm.injective h

end ZerosInfinite

#print axioms ZerosInfinite.infinite_ZIdx
