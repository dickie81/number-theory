import Mathlib

open Finset

namespace GSLemma

/-! Copied from `lib/pnt/SquarefreeCount.lean` (to avoid building PNT+): `μ² = Σ_{d²∣n} μ(d)`. -/
theorem dvd_of_sq_dvd_sq_mul {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  rw [← Nat.factorization_le_iff_dvd hd hb, Finsupp.le_def]
  have h2 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd)
    (mul_ne_zero (pow_ne_zero 2 hb) ha0)).2 h)
  intro p
  have hp := h2 p
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero 2 hb) ha0, Nat.factorization_pow]
    at hp
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hp
  have h1 := ha.natFactorization_le_one p
  omega

/-- `Σ_{d² ∣ n} μ(d)` is `1` if `n ≥ 1` is squarefree and `0` otherwise. -/
theorem sum_sq_dvd_moebius {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ (Finset.Ioc 0 n).filter (fun d ↦ d ^ 2 ∣ n), (ArithmeticFunction.moebius d : ℝ) =
      if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hset : (Finset.Ioc 0 (b ^ 2 * a)).filter (fun d ↦ d ^ 2 ∣ b ^ 2 * a) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd0, -⟩, hd⟩
      exact ⟨dvd_of_sq_dvd_sq_mul ha hb0.ne' hd0.ne' hd, hb0.ne'⟩
    · rintro ⟨hdb, -⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb hb0
      have hsq : d ^ 2 ∣ b ^ 2 * a := (pow_dvd_pow_of_dvd hdb 2).mul_right a
      refine ⟨⟨hd0, ?_⟩, hsq⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ b ^ 2 * a := Nat.le_of_dvd (by positivity) hsq
  rw [hset]
  have hμ : ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℝ) = if b = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f b) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [← Int.cast_sum, h]
    split_ifs <;> simp
  rw [hμ]
  have hiff : b = 1 ↔ Squarefree (b ^ 2 * a) := by
    constructor
    · rintro rfl
      simpa using ha
    · intro hsq
      exact Nat.isUnit_iff.1 (hsq b ⟨a, by ring⟩)
  by_cases hb1 : b = 1
  · rw [ite_eq_left hb1, ite_eq_left (hiff.1 hb1)]
  · rw [ite_eq_right hb1, ite_eq_right (fun h ↦ hb1 (hiff.2 h))]

/-- `Σ_{L < l ≤ L+K} 1/l² ≤ 1/L − 1/(L+K)` for `L ≥ 1`. -/
theorem tail_inv_sq (L : ℕ) (hL : 1 ≤ L) (K : ℕ) :
    ∑ l ∈ Ioc L (L + K), ((l:ℝ) ^ 2)⁻¹ ≤ (L:ℝ)⁻¹ - ((L + K : ℕ):ℝ)⁻¹ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show L + (K + 1) = (L + K) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
    have hpos : (0:ℝ) < (L + K : ℕ) := by exact_mod_cast (show 0 < L + K by omega)
    have h1 : (((L + K + 1 : ℕ):ℝ) ^ 2)⁻¹ ≤ ((L + K : ℕ):ℝ)⁻¹ - ((L + K + 1 : ℕ):ℝ)⁻¹ := by
      push_cast
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      push_cast at hpos
      rw [inv_sub_inv hpos.ne' (by positivity)]
      field_simp
      nlinarith
    linarith

/-- **The squarefree sieve (core of Granville–Soundararajan, Lemma 4.1).**
Let `ψ : ℕ → ℂ` be completely multiplicative with `‖ψ‖ ≤ 1` and every initial sum `‖Σ_{m ≤ y} ψ(m)‖ ≤ B`.
Then for every `L ≥ 1`, `‖Σ_{d ≤ N, d squarefree} ψ(d)‖ ≤ L·B + N/L`. -/
theorem sqf_sum_le (ψ : ℕ → ℂ) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b) (hle : ∀ m, ‖ψ m‖ ≤ 1)
    (B : ℝ) (hB : ∀ y, ‖∑ m ∈ Ioc 0 y, ψ m‖ ≤ B) (N L : ℕ) (hL : 1 ≤ L) :
    ‖∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d‖ ≤ L * B + N / L := by
  classical
  -- `Σ_{d≤N} sqf(d) ψ(d) = Σ_{l≤N} μ(l) ψ(l)² Σ_{m ≤ N/l²} ψ(m)`
  have hid : ∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d =
      ∑ l ∈ Ioc 0 N, (ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 * ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m := by
    have h1 : ∀ d ∈ Ioc 0 N, (if Squarefree d then ψ d else 0) =
        ∑ l ∈ Ioc 0 N, if l ^ 2 ∣ d then (ArithmeticFunction.moebius l : ℂ) * ψ d else 0 := by
      intro d hd
      rw [mem_Ioc] at hd
      have hs := sum_sq_dvd_moebius hd.1
      have hs' : ∑ l ∈ (Ioc 0 d).filter (fun l ↦ l ^ 2 ∣ d), (ArithmeticFunction.moebius l : ℂ) =
          if Squarefree d then 1 else 0 := by exact_mod_cast hs
      have hsub : (Ioc 0 d).filter (fun l ↦ l ^ 2 ∣ d) = (Ioc 0 N).filter (fun l ↦ l ^ 2 ∣ d) := by
        ext l; simp only [mem_filter, mem_Ioc]; constructor
        · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨⟨h0, h1.trans hd.2⟩, h2⟩
        · rintro ⟨⟨h0, -⟩, h2⟩
          exact ⟨⟨h0, (show l ≤ l ^ 2 by nlinarith).trans (Nat.le_of_dvd hd.1 h2)⟩, h2⟩
      rw [← sum_filter, ← sum_mul, ← hsub, hs']
      split_ifs <;> simp
    rw [sum_filter, sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [mem_Ioc] at hl
    rw [← sum_filter, mul_sum]
    -- reindex `d = l² m`
    have hl2 : 0 < l ^ 2 := pow_pos hl.1 2
    symm
    apply sum_nbij' (fun m => l ^ 2 * m) (fun d => d / l ^ 2)
    · intro m hm; simp only [mem_coe, mem_filter, mem_Ioc] at hm ⊢
      refine ⟨⟨Nat.mul_pos hl2 hm.1, ?_⟩, dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hl2).1 hm.2; linarith [mul_comm m (l^2)]
    · intro d hd; simp only [mem_coe, mem_filter, mem_Ioc] at hd ⊢
      obtain ⟨⟨h0, h1⟩, ⟨k, rfl⟩⟩ := hd
      rw [Nat.mul_div_cancel_left _ hl2]
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩
      rw [Nat.le_div_iff_mul_le hl2, mul_comm]; exact h1
    · intro m _; simp [Nat.mul_div_cancel_left _ hl2]
    · intro d hd; simp only [mem_coe, mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro m _; rw [hmul, show l ^ 2 = l * l by ring, hmul]; ring
  rw [hid]
  -- split at `L`
  have hterm : ∀ l ∈ Ioc 0 N, ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 *
      ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ ≤ if l ≤ L then B else (N:ℝ) / l ^ 2 := by
    intro l hl
    have hμ : ‖(ArithmeticFunction.moebius l : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hψ2 : ‖ψ l ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hle l)
    have hc : ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ hμ (norm_nonneg _) hψ2
    rw [norm_mul]
    have hinner_triv : ‖∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ ≤ (N:ℝ) / l ^ 2 := by
      calc _ ≤ ∑ m ∈ Ioc 0 (N / l ^ 2), ‖ψ m‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Ioc 0 (N / l ^ 2), (1:ℝ) := sum_le_sum fun m _ => hle m
        _ = ((N / l ^ 2 : ℕ) : ℝ) := by simp
        _ ≤ (N:ℝ) / l ^ 2 := by exact_mod_cast Nat.cast_div_le
    split_ifs
    · calc _ ≤ 1 * B := mul_le_mul hc (hB _) (norm_nonneg _) zero_le_one
        _ = B := one_mul _
    · calc _ ≤ 1 * ((N:ℝ) / l ^ 2) := mul_le_mul hc hinner_triv (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  calc _ ≤ ∑ l ∈ Ioc 0 N, ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 *
        ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Ioc 0 N, (if l ≤ L then B else (N:ℝ) / l ^ 2) := sum_le_sum hterm
    _ ≤ ∑ l ∈ Ioc 0 L, B + ∑ l ∈ Ioc L (L + N), (N:ℝ) / l ^ 2 := by
        rw [← sum_filter_add_sum_filter_not (Ioc 0 N) (fun l => l ≤ L)]
        apply add_le_add
        · rw [sum_ite_of_true (fun l hl => (mem_filter.1 hl).2)]
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => hB0)
          intro l hl; simp only [mem_filter, mem_Ioc] at hl ⊢; omega
        · rw [sum_ite_of_false (fun l hl => (mem_filter.1 hl).2)]
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
          intro l hl; simp only [mem_filter, mem_Ioc] at hl ⊢; omega
    _ ≤ L * B + N / L := by
        rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        have ht := tail_inv_sq L hL N
        have : ∑ l ∈ Ioc L (L + N), (N:ℝ) / l ^ 2 = N * ∑ l ∈ Ioc L (L + N), ((l:ℝ) ^ 2)⁻¹ := by
          rw [mul_sum]; rfl
        rw [this]
        have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
        have : (N:ℝ) * ∑ l ∈ Ioc L (L + N), ((l:ℝ) ^ 2)⁻¹ ≤ N * (L:ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hN
          have : (0:ℝ) ≤ ((L + N : ℕ):ℝ)⁻¹ := by positivity
          linarith
        rw [div_eq_mul_inv]; linarith


/-- Optimised: `‖Σ_{d ≤ N squarefree} ψ(d)‖ ≤ 2√(N B) + B` for `B > 0`. With `B = √n (1 + log n)` (Pólya–Vinogradov,
`PV.lean`) this is Granville–Soundararajan's `≪ x^{1/2} n^{1/4} (log n)^{1/2}`. -/
theorem sqf_sum_le_sqrt (ψ : ℕ → ℂ) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b) (hle : ∀ m, ‖ψ m‖ ≤ 1)
    (B : ℝ) (hBpos : 0 < B) (hB : ∀ y, ‖∑ m ∈ Ioc 0 y, ψ m‖ ≤ B) (N : ℕ) :
    ‖∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d‖ ≤ 2 * Real.sqrt (N * B) + B := by
  set r := Real.sqrt (N / B)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set L := ⌊r⌋₊ + 1
  have hL : 1 ≤ L := by omega
  have h := sqf_sum_le ψ hmul hle B hB N L hL
  have hLr : (L:ℝ) ≤ r + 1 := by
    simp only [L]; push_cast; linarith [Nat.floor_le hr0]
  have hrL : r < L := by simp only [L]; push_cast; exact Nat.lt_floor_add_one r
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hrB : r * B = Real.sqrt (N * B) := by
    rw [show (N:ℝ) * B = (N / B) * (B * B) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self hBpos.le]
  have h1 : (L:ℝ) * B ≤ Real.sqrt (N * B) + B := by nlinarith
  have h2 : (N:ℝ) / L ≤ Real.sqrt (N * B) := by
    rcases eq_or_lt_of_le hN with h0 | h0
    · rw [← h0]; simp
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hLpos : (0:ℝ) < L := by linarith
    rw [div_le_iff₀ hLpos]
    have hsq : r * r = N / B := Real.mul_self_sqrt (by positivity)
    have : (N:ℝ) = r * r * B := by rw [hsq]; field_simp
    calc (N:ℝ) = r * B * r := by rw [this]; ring
      _ ≤ r * B * L := by apply mul_le_mul_of_nonneg_left hrL.le; positivity
      _ = _ := by rw [hrB]
  linarith

end GSLemma

#print axioms GSLemma.sqf_sum_le
#print axioms GSLemma.sqf_sum_le_sqrt
