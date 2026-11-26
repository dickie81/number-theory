import SharpInputs

/-!
# The auxiliary primes (T) from the short-interval input

The core of the piece (T) of the proof of the sharp frontier (`SharpInputs`, `SharpObj.Primes`): primes `T = ππ̄` with
`π ≡ 1 (mod M)` (`4T = a² + d b²`, `M ∣ b`, `a ≡ b + 2 (mod 2M)`: `SharpDesign.ArithT`) exist in every dyadic window
`(e^Λ, 2e^Λ]` once `log(4dM²) ≤ c√Λ` (`exists_prime_norm_window`), so with `log T` within `log 2` of any target `Λ`
(`SharpDesign.exists_prime_arithT`, at the design's modulus `M = QS·q·d·(g₀g₁)²`). This is the input `ShortNorm`
(the short-interval prime number theorem for the Hecke characters of `ℚ(√−d)`) at `h = 1`, `Y = e^Λ`: its lower bound
`c'Y/((4dM²)^A log Y)` is positive, so the set it counts is not empty. `SharpObj.Primes` asks only `log T ≥ Λ_u − c_T`;
the upper bound `log T ≤ Λ_u + log 2` is what keeps the level-`T` terms of the other pieces (`log(2N_P)` in the slope
constant) at the size of `Λ_u`.
-/

namespace ZetaBalance

/-- **Primes of the shape of (T) in a dyadic window**: from `ShortNorm`, a constant `c > 0` such that for `d` prime,
`d ≡ 3 (mod 4)`, `d ≥ 100`, `M ≥ 3` and `Λ > 0` with `log(4dM²) ≤ c√Λ`, some prime `p` with `4p = a² + d b²`,
`M ∣ b`, `a ≡ b + 2 (mod 2M)` has `Λ < log p ≤ Λ + log 2`. -/
theorem exists_prime_norm_window (hS : ShortNorm) : ∃ c > 0, ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M →
    ∀ Λ : ℝ, 0 < Λ → Real.log (4 * d * M ^ 2) ≤ c * √Λ →
      ∃ p : ℕ, p.Prime ∧ (∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]) ∧
        Λ < Real.log p ∧ Real.log p ≤ Λ + Real.log 2 := by
  obtain ⟨A, c, c', -, hc, hc', H⟩ := hS
  refine ⟨c, hc, fun d M hd hd4 hd100 hM Λ hΛ hlog => ?_⟩
  have key := H d M hd hd4 hd100 hM (Real.exp Λ) 1 (by rwa [Real.log_exp])
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))) le_rfl
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 hd.pos
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 (by omega)
  have hpos : 0 < c' * 1 * Real.exp Λ / ((4 * d * M ^ 2 : ℝ) ^ A * Real.log (Real.exp Λ)) := by
    rw [Real.log_exp]
    exact div_pos (by positivity) (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hΛ)
  obtain ⟨p, hYp, hp2, hp, hab⟩ :=
    Set.nonempty_of_ncard_ne_zero (Nat.cast_pos.1 (hpos.trans_le key)).ne'
  have hp0 : (0 : ℝ) < p := (Real.exp_pos Λ).trans hYp
  refine ⟨p, hp, hab, (Real.lt_log_iff_exp_lt hp0).2 hYp, ?_⟩
  calc Real.log p ≤ Real.log (Real.exp Λ * 2) := Real.log_le_log hp0 (by linarith)
    _ = Λ + Real.log 2 := by rw [Real.log_mul (Real.exp_pos Λ).ne' two_ne_zero, Real.log_exp]

/-- **The auxiliary primes of a design** (the core of (T)): from `ShortNorm`, a constant `c > 0` such that, for a
design with `d ≡ 3 (mod 4)` and `d ≥ 100`, every target `Λ > 0` with `log(4dM²) ≤ c√Λ`, `M = QS·q·d·(g₀g₁)²`, has a
prime `T` meeting `ArithT` with `Λ < log T ≤ Λ + log 2`. -/
theorem SharpDesign.exists_prime_arithT (hS : ShortNorm) : ∃ c > 0, ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    (Dg : SharpDesign S κ x ε X), S.d % 4 = 3 → 100 ≤ S.d → ∀ Λ : ℝ, 0 < Λ →
      Real.log (4 * S.d * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℝ) ^ 2) ≤ c * √Λ →
        ∃ T : ℕ, T.Prime ∧ Dg.ArithT T ∧ Λ < Real.log T ∧ Real.log T ≤ Λ + Real.log 2 := by
  obtain ⟨c, hc, H⟩ := exists_prime_norm_window hS
  refine ⟨c, hc, fun {S} _ _ _ _ Dg hd4 hd100 Λ hΛ hlog => ?_⟩
  have hM : 3 ≤ S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 := by
    have h1 : 1 ≤ S.QS * S.q := Nat.one_le_iff_ne_zero.2
      (mul_ne_zero (NeZero.ne _) (Nat.Prime.ne_zero (Fact.out : S.q.Prime)))
    have h2 : 1 ≤ (Dg.g₀ * Dg.g₁) ^ 2 :=
      Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (mul_ne_zero Dg.g₀_prime.ne_zero Dg.g₁_prime.ne_zero))
    calc 3 ≤ 1 * S.d * 1 := by omega
      _ ≤ S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 := by gcongr
  obtain ⟨T, hT, hab, h1, h2⟩ := H S.d _ (Fact.out : S.d.Prime) hd4 hd100 hM Λ hΛ hlog
  exact ⟨T, hT, hab, h1, h2⟩

end ZetaBalance
