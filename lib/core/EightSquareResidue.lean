/-
# `ζ(4) = π⁴/90` from the points of `ℤ⁸` in a ball

Plain statement. The points of `ℤ⁸` in the ball `x₁² + ⋯ + x₈² ≤ N` are the shells `m ≤ N`, so the lattice count of
`LatticeCount` at radius `√N` is `Σ_{m ≤ N} r₈(m)` (`latticeCount_eight_sqrt`), and the volume `π⁴/24` of the unit
ball of `ℝ⁸` gives `Σ_{m ≤ N} r₈(m) ∼ (π⁴/24)N⁴` (`tendsto_sum_r8`). By Jacobi's eight-square theorem
(`JacobiEightSquares.r8_eq`), `r₈(m) = 16 f₈(m)` for `m ≥ 1`, with `f₈(m) = Σ_{d ∣ m} (−1)^{m+d} d³ ≥ 0`, so
`Σ_{k ≤ N} f₈(k) ∼ (π⁴/384)N⁴`. Partial summation with the weight `1/k³` turns this into
`Σ_{k ≤ N} f₈(k)/k³ ∼ (π⁴/96)N`, and Mathlib's Abelian theorem gives the residue
  `(s − 4)·Σ_{n ≥ 1} f₈(n)n^{−s} → π⁴/96` as `s → 4⁺`   (`residue_f8`).
The same series is `(1 − 2^{1−s} + 2^{4−2s})ζ(s)ζ(s − 3)` (`TwoVariableZetaEight.LSeries_f8`), whose residue at
`s = 4` is `(1 − 1/8 + 1/16)ζ(4) = (15/16)ζ(4)`, by the residue of `ζ` at `1`. So `ζ(4) = π⁴/90`
(`riemannZeta_four_of_lattice`), from counting the points of `ℤ⁸` in balls, without Mathlib's evaluation of `ζ(4)` or
of the Bernoulli numbers: the eight-dimensional form of `FourSquareResidue.riemannZeta_two_of_lattice`.
-/
import LatticeCount
import TwoVariableZetaEight

open Filter Topology Complex Finset JacobiEightSquares BallTower

noncomputable section

namespace EightSquareResidue

/-! ## The lattice count is the sum of the shells -/

/-- The points of `ℤ⁸` on the sphere `x₁² + ⋯ + x₈² = m`: the `Finset` that `r8` counts. -/
def shell (m : ℕ) : Finset (Fin 8 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 8 => Finset.Icc (-(m : ℤ)) m).filter (fun v => ∑ i, v i ^ 2 = (m : ℤ))

lemma mem_shell {m : ℕ} {v : Fin 8 → ℤ} : v ∈ shell m ↔ ∑ i, v i ^ 2 = (m : ℤ) := by
  simp only [shell, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  have hle : v i ^ 2 ≤ m := h ▸ Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have habs := Int.natAbs_le_self_sq (v i)
  rw [Int.natCast_natAbs] at habs
  exact abs_le.1 (habs.trans hle)

/-- The points of `ℤ⁸` in the ball `x₁² + ⋯ + x₈² ≤ N`. -/
def ball (N : ℕ) : Finset (Fin 8 → ℤ) := (range (N + 1)).biUnion shell

lemma mem_ball {N : ℕ} {v : Fin 8 → ℤ} : v ∈ ball N ↔ ∑ i, v i ^ 2 ≤ (N : ℤ) := by
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, mem_shell]
  constructor
  · rintro ⟨m, hm, h⟩
    rw [h]
    exact_mod_cast Nat.lt_succ_iff.1 hm
  · intro h
    have h0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact ⟨(∑ i, v i ^ 2).toNat, Nat.lt_succ_of_le (Int.toNat_le.2 h), (Int.toNat_of_nonneg h0).symm⟩

lemma card_ball (N : ℕ) : ((ball N).card : ℝ) = ∑ m ∈ range (N + 1), (r8 m : ℝ) := by
  unfold ball
  rw [Finset.card_biUnion]
  · push_cast
    rfl
  · intro m _ m' _ hmm'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [mem_shell] at hv hv'
    exact hmm' (by exact_mod_cast hv.symm.trans hv')

/-- The embedding `ℤ⁸ → ℝ⁸`. -/
def emb (v : Fin 8 → ℤ) : Fin 8 → ℝ := fun i => (v i : ℝ)

lemma emb_injective : Function.Injective emb :=
  fun _ _ h => funext fun i => Int.cast_injective (congrFun h i)

lemma eLen_emb (v : Fin 8 → ℤ) : eLen 8 (emb v) = Real.sqrt ((∑ i, v i ^ 2 : ℤ) : ℝ) := by
  unfold eLen emb
  rw [Real.sqrt_eq_rpow]
  push_cast
  simp only [Real.rpow_two, sq_abs]

/-- **Lattice count = shell sum**: `#{v ∈ ℤ⁸ : |v| ≤ √N} = Σ_{m ≤ N} r₈(m)`. -/
theorem latticeCount_eight_sqrt (N : ℕ) :
    (latticeCount 8 (Real.sqrt N) : ℝ) = ∑ m ∈ range (N + 1), (r8 m : ℝ) := by
  have hset : ({x : Fin 8 → ℝ | eLen 8 x ≤ Real.sqrt N} ∩ (intLattice 8 : Set (Fin 8 → ℝ))) =
      emb '' (ball N : Set (Fin 8 → ℤ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, Set.mem_image]
    constructor
    · rintro ⟨hx, hl⟩
      rw [mem_intLattice] at hl
      choose k hk using hl
      have hxe : x = emb k := funext fun i => (hk i).symm
      refine ⟨k, ?_, hxe.symm⟩
      rw [mem_ball]
      rw [hxe, eLen_emb, Real.sqrt_le_sqrt_iff (Nat.cast_nonneg N)] at hx
      exact_mod_cast hx
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [eLen_emb]
        exact Real.sqrt_le_sqrt (by exact_mod_cast mem_ball.1 hv)
      · rw [mem_intLattice]
        exact fun i => ⟨v i, rfl⟩
  unfold latticeCount
  rw [Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ emb_injective, Set.ncard_coe_finset, card_ball]

/-- **The points of `ℤ⁸` in a ball**: `Σ_{m ≤ N} r₈(m)/N⁴ → π⁴/24`, the volume of the unit ball of `ℝ⁸`. -/
theorem tendsto_sum_r8 :
    Tendsto (fun N : ℕ => (∑ m ∈ range (N + 1), (r8 m : ℝ)) / (N : ℝ) ^ 4) atTop (𝓝 (Real.pi ^ 4 / 24)) := by
  have h := (count_div_pow_tendsto_ballVol 8).comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  rw [ballVol_eight] at h
  refine h.congr' ?_
  filter_upwards with N
  simp only [Function.comp_apply]
  rw [latticeCount_eight_sqrt, show Real.sqrt N ^ 8 = (N : ℝ) ^ 4 by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]]

/-! ## The residue -/

/-- `f₈(m) = Σ_{d ∣ m} (−1)^{m+d} d³` over `ℝ`. -/
def f8R (m : ℕ) : ℝ := ∑ d ∈ m.divisors, (-1) ^ (m + d) * (d : ℝ) ^ 3

lemma r8_eq_f8R {m : ℕ} (hm : m ≠ 0) : (r8 m : ℝ) = 16 * f8R m := by
  rw [f8R]
  exact_mod_cast r8_eq hm

lemma f8R_zero : f8R 0 = 0 := by simp [f8R]

lemma f8R_nonneg (m : ℕ) : 0 ≤ f8R m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [f8R_zero]
  · have h := r8_eq_f8R hm
    have : (0 : ℝ) ≤ r8 m := Nat.cast_nonneg _
    linarith

lemma sum_r8_eq (N : ℕ) : ∑ m ∈ range (N + 1), (r8 m : ℝ) = 1 + 16 * ∑ m ∈ range (N + 1), f8R m := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' f8R, r8_zero]
  have h : ∀ i ∈ range N, (r8 (i + 1) : ℝ) = 16 * f8R (i + 1) := fun i _ => r8_eq_f8R (Nat.succ_ne_zero i)
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, f8R_zero]
  push_cast
  ring

/-- `Σ_{k ≤ N} f₈(k)/N⁴ → π⁴/384`. -/
lemma tendsto_sum_f8R :
    Tendsto (fun N : ℕ => (∑ m ∈ range (N + 1), f8R m) / (N : ℝ) ^ 4) atTop (𝓝 (Real.pi ^ 4 / 384)) := by
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ) ^ 4) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [Function.comp_def, one_div] using this
  have h := (tendsto_sum_r8.sub h1).div_const 16
  rw [show (Real.pi ^ 4 / 24 - 0) / 16 = Real.pi ^ 4 / 384 by ring] at h
  refine h.congr' ?_
  filter_upwards with N
  rw [sum_r8_eq]
  ring

/-- **Partial summation** with the weight `1/k³`: for `f` with `f 0 = 0` and `S n = Σ_{k ≤ n} f k`,
`Σ_{k ≤ n} f k/k³ = S n/n³ + Σ_{k < n} S k (1/k³ − 1/(k + 1)³)`. -/
lemma sum_div_cube_eq (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), f k / k ^ 3 = (∑ k ∈ range (n + 1), f k) / n ^ 3 +
      ∑ k ∈ range n, (∑ j ∈ range (k + 1), f j) * (1 / k ^ 3 - 1 / (k + 1) ^ 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ
      (fun k => (∑ j ∈ range (k + 1), f j) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3)),
      Finset.sum_range_succ f (n + 1)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- `Σ_{1 ≤ k ≤ N} f₈(k)/k³ ∼ (π⁴/96)N`. -/
lemma tendsto_sum_f8R_div :
    Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, (f8R k / k ^ 3)) / N) atTop (𝓝 (Real.pi ^ 4 / 96)) := by
  set S : ℕ → ℝ := fun n => ∑ m ∈ range (n + 1), f8R m with hS
  have hS4 := tendsto_sum_f8R
  -- the weight `k⁴ (1/k³ − 1/(k + 1)³) = 3x³ + 3x²y + xy²`, `x = k/(k + 1) → 1`, `y = 1/(k + 1) → 0`
  have hx : Tendsto (fun k : ℕ => (k : ℝ) / (k + 1)) atTop (𝓝 1) := tendsto_natCast_div_add_atTop 1
  have hy : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto (fun k : ℕ => 3 * ((k : ℝ) / (k + 1)) ^ 3 + 3 * ((k : ℝ) / (k + 1)) ^ 2 * (1 / ((k : ℝ) + 1)) +
      (k : ℝ) / (k + 1) * (1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 3) := by
    have := (((hx.pow 3).const_mul 3).add (((hx.pow 2).const_mul 3).mul hy)).add (hx.mul (hy.pow 2))
    simpa using this
  -- the Cesàro part: `S k (1/k³ − 1/(k + 1)³) → 3π⁴/384`
  have hu : Tendsto (fun k : ℕ => S k * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3)) atTop
      (𝓝 (Real.pi ^ 4 / 384 * 3)) := by
    refine (hS4.mul hw).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [hS]
    field_simp
    ring
  have hc := hu.cesaro
  -- the boundary part: `S N/N⁴ → π⁴/384`
  have h := hS4.add hc
  rw [show Real.pi ^ 4 / 384 + Real.pi ^ 4 / 384 * 3 = Real.pi ^ 4 / 96 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have e1 : ∑ k ∈ Icc 1 N, (f8R k / k ^ 3) = ∑ k ∈ range (N + 1), (f8R k / k ^ 3) := by
    have e : Icc 1 N = Ico 1 (N + 1) := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1), Finset.sum_range_one]
    simp
  rw [e1, sum_div_cube_eq f8R f8R_zero N]
  simp only [hS]
  field_simp

/-- **The residue at `s = 4`**: `(s − 4)·Σ_{n ≥ 1} f₈(n)n^{−s} → π⁴/96` as `s → 4⁺`, from the points of `ℤ⁸` in
balls. -/
theorem residue_f8 :
    Tendsto (fun s : ℝ => ((s : ℂ) - 4) * LSeries TwoVariableZetaEight.f8 s) (𝓝[>] 4)
      (𝓝 ((Real.pi ^ 4 / 96 : ℝ) : ℂ)) := by
  have h := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (fun n => f8R n / n ^ 3)
    tendsto_sum_f8R_div fun n => by have := f8R_nonneg n; positivity
  have hmap : Tendsto (fun s : ℝ => s - 3) (𝓝[>] 4) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_sub_right (3 : ℝ)).tendsto 4
      rw [show (4 : ℝ) - 3 = 1 by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.2 (by linarith [Set.mem_Ioi.1 hs])
  refine (h.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply]
  push_cast
  rw [show (s : ℂ) - 3 - 1 = s - 4 by ring]
  congr 1
  simp only [LSeries]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hc : (n : ℂ) ^ (s : ℂ) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn]
    rw [Complex.cpow_sub _ _ hn', show (3 : ℂ) = (3 : ℕ) by norm_num, Complex.cpow_natCast,
      TwoVariableZetaEight.f8, f8R]
    push_cast
    field_simp

/-- **`ζ(4) = π⁴/90` from counting the points of `ℤ⁸` in balls**: the residue of `Σ f₈(n)n^{−s}` at `s = 4` is
`π⁴/96` (`residue_f8`), and the series is `(1 − 2^{1−s} + 2^{4−2s})ζ(s)ζ(s − 3)`, whose residue there is
`(15/16)ζ(4)`. -/
theorem riemannZeta_four_of_lattice : riemannZeta 4 = ((Real.pi ^ 4 / 90 : ℝ) : ℂ) := by
  have hof : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 4) (𝓝 (4 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto 4).mono_left nhdsWithin_le_nhds
  -- `1 − 2^{1−s} + 2^{4−2s} → 15/16`
  have hE : Tendsto (fun s : ℝ => 1 - (2 : ℂ) ^ (1 - (s : ℂ)) + (2 : ℂ) ^ (4 - 2 * (s : ℂ))) (𝓝[>] 4)
      (𝓝 (15 / 16)) := by
    have hc : Continuous fun s : ℝ => 1 - (2 : ℂ) ^ (1 - (s : ℂ)) + (2 : ℂ) ^ (4 - 2 * (s : ℂ)) :=
      (continuous_const.sub ((continuous_const.sub Complex.continuous_ofReal).const_cpow
        (Or.inl two_ne_zero))).add ((continuous_const.sub (continuous_const.mul
          Complex.continuous_ofReal)).const_cpow (Or.inl two_ne_zero))
    convert (hc.tendsto 4).mono_left nhdsWithin_le_nhds using 2
    push_cast
    rw [show (1 : ℂ) - 4 = ((-3 : ℤ) : ℂ) by norm_num, show (4 : ℂ) - 2 * 4 = ((-4 : ℤ) : ℂ) by norm_num,
      Complex.cpow_intCast, Complex.cpow_intCast]
    norm_num
  -- `ζ(s) → ζ(4)`
  have hz : Tendsto (fun s : ℝ => riemannZeta s) (𝓝[>] 4) (𝓝 (riemannZeta 4)) :=
    ((differentiableAt_riemannZeta (by norm_num : (4 : ℂ) ≠ 1)).continuousAt.tendsto).comp hof
  -- `(s − 4)ζ(s − 3) → 1`
  have hmap : Tendsto (fun s : ℝ => (s : ℂ) - 3) (𝓝[>] 4) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hof.sub_const 3
      rwa [show (4 : ℂ) - 3 = 1 by norm_num] at this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Set.mem_compl_singleton_iff.2 fun h => ?_
      have : (s : ℂ) = 4 := by linear_combination h
      have hs4 : (4 : ℝ) < s := hs
      exact absurd (by exact_mod_cast this : s = 4) (ne_of_gt hs4)
  have hres : Tendsto (fun s : ℝ => ((s : ℂ) - 4) * riemannZeta ((s : ℂ) - 3)) (𝓝[>] 4) (𝓝 1) := by
    refine (riemannZeta_residue_one.comp hmap).congr fun s => ?_
    simp only [Function.comp_apply]
    ring_nf
  have hprod : ∀ᶠ s : ℝ in 𝓝[>] 4, ((s : ℂ) - 4) * LSeries TwoVariableZetaEight.f8 s =
      (1 - (2 : ℂ) ^ (1 - (s : ℂ)) + (2 : ℂ) ^ (4 - 2 * (s : ℂ))) * riemannZeta s *
        (((s : ℂ) - 4) * riemannZeta ((s : ℂ) - 3)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 4 < (s : ℂ).re := by simpa using hs
    rw [(TwoVariableZetaEight.LSeries_f8 hs').2]
    ring
  have h1 := residue_f8.congr' hprod
  have h2 := (hE.mul hz).mul hres
  have e := tendsto_nhds_unique h1 h2
  rw [mul_one] at e
  have : riemannZeta 4 = 16 / 15 * ((Real.pi ^ 4 / 96 : ℝ) : ℂ) := by
    rw [e]
    ring
  rw [this]
  push_cast
  ring

end EightSquareResidue

#print axioms EightSquareResidue.latticeCount_eight_sqrt
#print axioms EightSquareResidue.tendsto_sum_r8
#print axioms EightSquareResidue.residue_f8
#print axioms EightSquareResidue.riemannZeta_four_of_lattice
