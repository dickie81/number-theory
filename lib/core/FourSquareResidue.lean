/-
# `ζ(2) = π²/6` from the points of `ℤ⁴` in a ball

Plain statement. The points of `ℤ⁴` in the ball `x₁² + x₂² + x₃² + x₄² ≤ N` are the shells `m ≤ N`, so the lattice
count of `LatticeCount` at radius `√N` is `Σ_{m ≤ N} r₄(m)` (`latticeCount_four_sqrt`), and the volume `π²/2` of the
unit ball of `ℝ⁴` gives `Σ_{m ≤ N} r₄(m) ∼ (π²/2)N²` (`tendsto_sum_r4`). By Jacobi's four-square theorem
(`JacobiFourSquares.r4_eq`), `r₄(m) = 8σ₄(m)` for `m ≥ 1`, so `Σ_{k ≤ N} σ₄(k) ∼ (π²/16)N²`. Partial summation turns
this into `Σ_{k ≤ N} σ₄(k)/k ∼ (π²/8)N`, and Mathlib's Abelian theorem gives the residue
  `(s − 2)·Σ_{n ≥ 1} σ₄(n)n^{−s} → π²/8` as `s → 2⁺`   (`residue_sigma4`).
The same series is `(1 − 4^{1−s})ζ(s)ζ(s − 1)` (`TwoVariableZeta.LSeries_sigma4`), whose residue at `s = 2` is
`(1 − 1/4)ζ(2)`, by the residue of `ζ` at `1`. So `ζ(2) = π²/6` (`riemannZeta_two_of_lattice`), from counting the
points of `ℤ⁴` in balls, without Mathlib's evaluation of `ζ(2)`: the four-dimensional form of
`AngularResidue.LFunction_chi4_one`, which gets `L(1, χ₋₄) = π/4` from the points of `ℤ²` in discs.
-/
import LatticeCount
import TwoVariableZeta

open Filter Topology Complex Finset JacobiFourSquares BallTower

noncomputable section

namespace FourSquareResidue

/-! ## The lattice count is the sum of the shells -/

/-- The points of `ℤ⁴` on the sphere `x₁² + x₂² + x₃² + x₄² = m`: the `Finset` that `r4` counts. -/
def shell (m : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) m).filter (fun v => ∑ i, v i ^ 2 = (m : ℤ))

lemma mem_shell {m : ℕ} {v : Fin 4 → ℤ} : v ∈ shell m ↔ ∑ i, v i ^ 2 = (m : ℤ) := by
  simp only [shell, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  have hle : v i ^ 2 ≤ m := h ▸ Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have habs := Int.natAbs_le_self_sq (v i)
  rw [Int.natCast_natAbs] at habs
  exact abs_le.1 (habs.trans hle)

/-- The points of `ℤ⁴` in the ball `x₁² + x₂² + x₃² + x₄² ≤ N`. -/
def ball (N : ℕ) : Finset (Fin 4 → ℤ) := (range (N + 1)).biUnion shell

lemma mem_ball {N : ℕ} {v : Fin 4 → ℤ} : v ∈ ball N ↔ ∑ i, v i ^ 2 ≤ (N : ℤ) := by
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, mem_shell]
  constructor
  · rintro ⟨m, hm, h⟩
    rw [h]
    exact_mod_cast Nat.lt_succ_iff.1 hm
  · intro h
    have h0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact ⟨(∑ i, v i ^ 2).toNat, Nat.lt_succ_of_le (Int.toNat_le.2 h), (Int.toNat_of_nonneg h0).symm⟩

lemma card_ball (N : ℕ) : ((ball N).card : ℝ) = ∑ m ∈ range (N + 1), (r4 m : ℝ) := by
  unfold ball
  rw [Finset.card_biUnion]
  · push_cast
    rfl
  · intro m _ m' _ hmm'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [mem_shell] at hv hv'
    exact hmm' (by exact_mod_cast hv.symm.trans hv')

/-- The embedding `ℤ⁴ → ℝ⁴`. -/
def emb (v : Fin 4 → ℤ) : Fin 4 → ℝ := fun i => (v i : ℝ)

lemma emb_injective : Function.Injective emb :=
  fun _ _ h => funext fun i => Int.cast_injective (congrFun h i)

lemma eLen_emb (v : Fin 4 → ℤ) : eLen 4 (emb v) = Real.sqrt ((∑ i, v i ^ 2 : ℤ) : ℝ) := by
  unfold eLen emb
  rw [Real.sqrt_eq_rpow]
  push_cast
  simp only [Real.rpow_two, sq_abs]

/-- **Lattice count = shell sum**: `#{v ∈ ℤ⁴ : |v| ≤ √N} = Σ_{m ≤ N} r₄(m)`. -/
theorem latticeCount_four_sqrt (N : ℕ) :
    (latticeCount 4 (Real.sqrt N) : ℝ) = ∑ m ∈ range (N + 1), (r4 m : ℝ) := by
  have hset : ({x : Fin 4 → ℝ | eLen 4 x ≤ Real.sqrt N} ∩ (intLattice 4 : Set (Fin 4 → ℝ))) =
      emb '' (ball N : Set (Fin 4 → ℤ)) := by
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

/-- **The points of `ℤ⁴` in a ball**: `Σ_{m ≤ N} r₄(m)/N² → π²/2`, the volume of the unit ball of `ℝ⁴`. -/
theorem tendsto_sum_r4 :
    Tendsto (fun N : ℕ => (∑ m ∈ range (N + 1), (r4 m : ℝ)) / (N : ℝ) ^ 2) atTop (𝓝 (Real.pi ^ 2 / 2)) := by
  have h := (count_div_pow_tendsto_ballVol 4).comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  rw [ballVol_four] at h
  refine h.congr' ?_
  filter_upwards with N
  simp only [Function.comp_apply]
  rw [latticeCount_four_sqrt, show Real.sqrt N ^ 4 = (N : ℝ) ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]]

/-! ## The residue -/

lemma sum_r4_eq (N : ℕ) : ∑ m ∈ range (N + 1), (r4 m : ℝ) = 1 + 8 * ∑ m ∈ range (N + 1), (sigma4 m : ℝ) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun m => (sigma4 m : ℝ)), r4_zero]
  have h : ∀ i ∈ range N, (r4 (i + 1) : ℝ) = 8 * (sigma4 (i + 1) : ℝ) := fun i _ => by
    rw [r4_eq (Nat.succ_ne_zero i)]
    push_cast
    ring
  have h0 : sigma4 0 = 0 := by simp [sigma4]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, h0]
  push_cast
  ring

/-- `Σ_{k ≤ N} σ₄(k)/N² → π²/16`. -/
lemma tendsto_sum_sigma4 :
    Tendsto (fun N : ℕ => (∑ m ∈ range (N + 1), (sigma4 m : ℝ)) / (N : ℝ) ^ 2) atTop (𝓝 (Real.pi ^ 2 / 16)) := by
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [Function.comp_def, one_div] using this
  have h := (tendsto_sum_r4.sub h1).div_const 8
  rw [show (Real.pi ^ 2 / 2 - 0) / 8 = Real.pi ^ 2 / 16 by ring] at h
  refine h.congr' ?_
  filter_upwards with N
  rw [sum_r4_eq]
  ring

/-- **Partial summation**: for `f` with `f 0 = 0` and `S n = Σ_{k ≤ n} f k`,
`Σ_{k ≤ n} f k/k = S n/n + Σ_{k < n} S k/(k(k + 1))`. -/
lemma sum_div_eq (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), f k / k =
      (∑ k ∈ range (n + 1), f k) / n + ∑ k ∈ range n, (∑ j ∈ range (k + 1), f j) / (k * (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (∑ j ∈ range (k + 1), f j) / (k * (k + 1))),
      Finset.sum_range_succ f (n + 1)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- `Σ_{1 ≤ k ≤ N} σ₄(k)/k ∼ (π²/8)N`. -/
lemma tendsto_sum_sigma4_div :
    Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, ((sigma4 k : ℝ) / k)) / N) atTop (𝓝 (Real.pi ^ 2 / 8)) := by
  set S : ℕ → ℝ := fun n => ∑ m ∈ range (n + 1), (sigma4 m : ℝ) with hS
  have hS2 := tendsto_sum_sigma4
  -- the Cesàro part: `S k/(k(k + 1)) → π²/16`
  have hu : Tendsto (fun k : ℕ => S k / (k * (k + 1))) atTop (𝓝 (Real.pi ^ 2 / 16)) := by
    have h := hS2.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [hS]
    field_simp
  have hc := hu.cesaro
  -- the boundary part: `S N/N² → π²/16`
  have h := hS2.add hc
  rw [show Real.pi ^ 2 / 16 + Real.pi ^ 2 / 16 = Real.pi ^ 2 / 8 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have e1 : ∑ k ∈ Icc 1 N, ((sigma4 k : ℝ) / k) = ∑ k ∈ range (N + 1), ((sigma4 k : ℝ) / k) := by
    have e : Icc 1 N = Ico 1 (N + 1) := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1), Finset.sum_range_one]
    simp
  rw [e1, sum_div_eq (fun k => (sigma4 k : ℝ)) (by simp [sigma4]) N]
  simp only [hS]
  field_simp

/-- **The residue at `s = 2`**: `(s − 2)·Σ_{n ≥ 1} σ₄(n)n^{−s} → π²/8` as `s → 2⁺`, from the points of `ℤ⁴` in balls. -/
theorem residue_sigma4 :
    Tendsto (fun s : ℝ => ((s : ℂ) - 2) * LSeries (fun n => (sigma4 n : ℂ)) s) (𝓝[>] 2)
      (𝓝 ((Real.pi ^ 2 / 8 : ℝ) : ℂ)) := by
  have h := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (fun n => (sigma4 n : ℝ) / n)
    tendsto_sum_sigma4_div fun n => by positivity
  have hmap : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 2) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_sub_right (1 : ℝ)).tendsto 2
      rw [show (2 : ℝ) - 1 = 1 by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.2 (by linarith [Set.mem_Ioi.1 hs])
  refine (h.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs2 : (2 : ℝ) < s := hs
  simp only [Function.comp_apply]
  push_cast
  rw [show (s : ℂ) - 1 - 1 = s - 2 by ring]
  congr 1
  simp only [LSeries]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hc : (n : ℂ) ^ ((s : ℂ) - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn]
    rw [Complex.cpow_sub _ _ hn', Complex.cpow_one]
    field_simp

/-- **`ζ(2) = π²/6` from counting the points of `ℤ⁴` in balls**: the residue of `Σ σ₄(n)n^{−s}` at `s = 2` is
`π²/8` (`residue_sigma4`), and the series is `(1 − 4^{1−s})ζ(s)ζ(s − 1)`, whose residue there is `(3/4)ζ(2)`. -/
theorem riemannZeta_two_of_lattice : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  have hof : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 2) (𝓝 (2 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto 2).mono_left nhdsWithin_le_nhds
  -- `1 − 4^{1−s} → 3/4`
  have h4 : Tendsto (fun s : ℝ => 1 - (4 : ℂ) ^ (1 - (s : ℂ))) (𝓝[>] 2) (𝓝 (3 / 4)) := by
    have hc : Continuous fun s : ℝ => 1 - (4 : ℂ) ^ (1 - (s : ℂ)) :=
      continuous_const.sub ((continuous_const.sub Complex.continuous_ofReal).const_cpow (Or.inl (by norm_num)))
    have h : Tendsto (fun s : ℝ => 1 - (4 : ℂ) ^ (1 - (s : ℂ))) (𝓝[>] 2)
        (𝓝 (1 - (4 : ℂ) ^ (1 - ((2 : ℝ) : ℂ)))) := (hc.tendsto 2).mono_left nhdsWithin_le_nhds
    convert h using 2
    push_cast
    rw [show (1 : ℂ) - 2 = -1 by ring, Complex.cpow_neg_one]
    norm_num
  -- `ζ(s) → ζ(2)`
  have hz : Tendsto (fun s : ℝ => riemannZeta s) (𝓝[>] 2) (𝓝 (riemannZeta 2)) :=
    ((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto).comp hof
  -- `(s − 2)ζ(s − 1) → 1`
  have hmap : Tendsto (fun s : ℝ => (s : ℂ) - 1) (𝓝[>] 2) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hof.sub_const 1
      rwa [show (2 : ℂ) - 1 = 1 by norm_num] at this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Set.mem_compl_singleton_iff.2 fun h => ?_
      have : (s : ℂ) = 2 := by linear_combination h
      have hs2 : (2 : ℝ) < s := hs
      exact absurd (by exact_mod_cast this : s = 2) (ne_of_gt hs2)
  have hres : Tendsto (fun s : ℝ => ((s : ℂ) - 2) * riemannZeta ((s : ℂ) - 1)) (𝓝[>] 2) (𝓝 1) := by
    refine (riemannZeta_residue_one.comp hmap).congr fun s => ?_
    simp only [Function.comp_apply]
    ring_nf
  have hprod : ∀ᶠ s : ℝ in 𝓝[>] 2, ((s : ℂ) - 2) * LSeries (fun n => (sigma4 n : ℂ)) s =
      (1 - (4 : ℂ) ^ (1 - (s : ℂ))) * riemannZeta s * (((s : ℂ) - 2) * riemannZeta ((s : ℂ) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 2 < (s : ℂ).re := by simpa using hs
    rw [(TwoVariableZeta.LSeries_sigma4 hs').2]
    ring
  have h1 := residue_sigma4.congr' hprod
  have h2 := (h4.mul hz).mul hres
  have e := tendsto_nhds_unique h1 h2
  rw [mul_one] at e
  have : riemannZeta 2 = 4 / 3 * ((Real.pi ^ 2 / 8 : ℝ) : ℂ) := by
    rw [e]
    ring
  rw [this]
  push_cast
  ring

end FourSquareResidue

#print axioms FourSquareResidue.latticeCount_four_sqrt
#print axioms FourSquareResidue.tendsto_sum_r4
#print axioms FourSquareResidue.residue_sigma4
#print axioms FourSquareResidue.riemannZeta_two_of_lattice
