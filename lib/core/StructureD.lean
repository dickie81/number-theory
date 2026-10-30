import Mathlib
import GroundChain

/-! # Theorem D, formal

1. **Finite dimension.** The image `W` of the ground space in `L²` is finite-dimensional
   (`finiteDimensional_groundL2`): a Riesz-separated sequence in an infinite-dimensional `W` would be
   a bounded-energy sequence of probes with no `L²`-convergent subsequence, against
   `exists_convergent_subseq`.
2. **The Green chain spans.** With `G` the Green operator of the pole (DegenerateFlat.lean), a
   filtration argument gives a nonzero `w` whose iterates `w, Gw, …, G^{m−1}w` all lie in the ground
   space; they are independent (`Ĝ` multiplies by `−1/(z² + ¼)`), so they span it.
3. **Zeros on the cross.** The last iterate `h = G^{m−1}w` has `ĥ` vanishing only on `ℝ ∪ iℝ`.

In `z`-language: `V_ℂ = ĥ · {polynomials of degree < m in z²}`, Theorem D.

Steps 2–3 are proved once for any ground-state family (`GroundChain.lean`); this
file supplies Weil's form as the instance `zetaGD` (finite dimension here, the Green steps from
`DegenerateFlat`, the swap closure from `SimpleStructure`) and states the results under their
original names.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace WeilForm

/-! ## The ground space in `L²` -/

/-- The ground space mapped into `L²`. -/
abbrev iotaGS (a : ℝ) : groundSpace a →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) := iotaOf weilQ_form a

theorem norm_iotaGS_sq {a : ℝ} (x : groundSpace a) : ‖iotaGS a x‖ ^ 2 = normSq x.1 := by
  show ‖x.2.1.memL2.toLp x.1‖ ^ 2 = _
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [x.2.1.memL2.coeFn_toLp] with t ht
  rw [ht]

/-- The archimedean energy of a ground-space element is controlled by its norm. -/
theorem archE_le_of_mem {a : ℝ} {g : ℝ → ℝ} (hg : g ∈ groundSpace a) :
    archE g ≤ (|lam a| + |weilConst| + 2 * primeWeight a) * normSq g := by
  have hq : weilQ a g = lam a * normSq g := hg.2
  have hN := normSq_nonneg g
  have hS := abs_prime_sum_le hg.1
  have e : archE g = lam a * normSq g - 2 * poleR g a ^ 2 - weilConst * normSq g + 2 * primeS g := by
    rw [← hq, weilQ_eq']; ring
  have hS' : primeS g ≤ primeWeight a * normSq g := (le_abs_self _).trans hS
  have h1 : lam a * normSq g ≤ |lam a| * normSq g := mul_le_mul_of_nonneg_right (le_abs_self _) hN
  have h2 : -(weilConst * normSq g) ≤ |weilConst| * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs _) hN
  nlinarith [sq_nonneg (poleR g a)]

/-- **The ground space is finite-dimensional** (its image in `L²`). -/
theorem finiteDimensional_groundL2 {a : ℝ} (ha : 0 < a) :
    FiniteDimensional ℝ (LinearMap.range (iotaGS a)) := by
  by_contra hfin
  obtain ⟨R, f, hR, hfR, hsep⟩ :=
    exists_seq_norm_le_one_le_norm_sub (𝕜 := ℝ) (E := LinearMap.range (iotaGS a)) hfin
  have hx : ∀ n, ∃ x : groundSpace a, iotaGS a x = (f n : Lp ℝ 2 volume) :=
    fun n => LinearMap.mem_range.1 (f n).2
  choose x hxf using hx
  set h : ℕ → ℝ → ℝ := fun n => (x n).1
  have hp : ∀ n, Probe a (h n) := fun n => (x n).2.1
  have hN : ∀ n, normSq (h n) ≤ R ^ 2 := by
    intro n
    rw [← norm_iotaGS_sq, hxf n, Submodule.norm_coe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfR n) 2
  set K := |lam a| + |weilConst| + 2 * primeWeight a
  have hK : 0 ≤ K := by
    have : 0 ≤ primeWeight a := by
      unfold primeWeight
      exact Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_nonneg _)
    positivity
  have hC : ∀ n, archE (h n) ≤ K * R ^ 2 :=
    fun n => (archE_le_of_mem (x n).2).trans (mul_le_mul_of_nonneg_left (hN n) hK)
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp hN hC
  have hconv := tendsto_toLp (fun j => (hp (φ j)).memL2) hG hlim
  have hcau := hconv.cauchySeq
  obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff'.1 hcau 1 one_pos
  have hd := hN' (N + 1) (by omega)
  have hsep' := hsep (show φ (N + 1) ≠ φ N from (hφ (Nat.lt_succ_self N)).ne')
  have e1 : ((hp (φ (N + 1))).memL2.toLp (h (φ (N + 1)))) = (f (φ (N + 1)) : Lp ℝ 2 volume) :=
    hxf _
  have e2 : ((hp (φ N)).memL2.toLp (h (φ N))) = (f (φ N) : Lp ℝ 2 volume) := hxf _
  rw [dist_eq_norm, e1, e2, ← Submodule.coe_sub, Submodule.norm_coe] at hd
  linarith

/-! ## Weil's form as a ground-state family -/

/-- **Weil's form for `ζ` as a ground-state family.** -/
def zetaGD : GroundData where
  Q := weilQ
  form := weilQ_form
  partner := fun ha hw hwp hk hkp => G_mem_partner ha hw hwp hk hkp
  poleFree := fun ha hw hwp hGp => G_mem_pole_free ha hw hwp hGp
  green := fun ha hg hw hσ => green_mem_groundSpace ha hg hw hσ
  fd := fun ha => finiteDimensional_groundL2 ha
  nonzero := fun ha => by
    obtain ⟨g, hg⟩ := exists_groundState ha
    exact ⟨g, ((isGroundState_iff ha).1 hg).1, ((isGroundState_iff ha).1 hg).2⟩

/-- `f` starts a Green chain of length `j`: `f, Gf, …, G^j f` lie in the ground space and all but
the last are pole-free. -/
abbrev IsChain (a : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop := zetaGD.IsChain a j f

/-- The dimension of the ground space. -/
abbrev gdim (a : ℝ) : ℕ := zetaGD.gdim a

/-- The chain as ground-space vectors. -/
abbrev chainVec {a : ℝ} {j : ℕ} {w : ℝ → ℝ} (hc : IsChain a j w) (i : Fin (j + 1)) : groundSpace a :=
  zetaGD.chainVec hc i

/-- **Theorem D, zeros on the cross.** -/
theorem chain_top_zeros {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hpos : 0 < normSq w) {ω : ℂ} (hω : ghatC (Gi a (gdim a - 1) w) a ω = 0) :
    (ω ^ 2).im = 0 :=
  zetaGD.chain_top_zeros ha hc hpos hω

/-- **Theorem D, formal.** With `m = dim V` (finite, `finiteDimensional_groundL2`), there
is a nonzero `w` whose Green chain `w, Gw, …, G^{m−1}w` lies in the ground space (all but the last
pole-free), is linearly independent, and spans it a.e. Every zero `ω` of `ĥ`, `h = G^{m−1}w`, has
`ω² ∈ ℝ`. -/
theorem theoremD {a : ℝ} (ha : 0 < a) :
    ∃ w, IsChain a (gdim a - 1) w ∧ 0 < normSq w ∧
      (∃ hc : IsChain a (gdim a - 1) w,
        LinearIndependent ℝ (fun i => (iotaGS a).rangeRestrict (chainVec hc i))) ∧
      (∀ v ∈ groundSpace a, ∃ c : Fin (gdim a - 1 + 1) → ℝ,
        v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x) ∧
      ∀ ω : ℂ, ghatC (Gi a (gdim a - 1) w) a ω = 0 → (ω ^ 2).im = 0 :=
  zetaGD.theoremD ha

/-! ## Consequence for the RH chain: simplicity is no longer a separate input -/

/-- **The top-of-chain ground state**: `G^{m−1}w`, normalised. -/
abbrev topGS (a : ℝ) : ℝ → ℝ := zetaGD.topGS a

theorem topGS_isGroundState {a : ℝ} (ha : 0 < a) : IsGroundState a (topGS a) :=
  (isGroundState_iff ha).2 (zetaGD.topGS_mem ha)

/-- **Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`**, at every support `a > 0`,
with no simplicity assumption. -/
theorem topGS_cross {a : ℝ} (ha : 0 < a) (z : ℂ) (hz : ghatC (topGS a) a z = 0) :
    z.re = 0 ∨ z.im = 0 :=
  zetaGD.topGS_cross ha z hz

/-- **The RH chain with simplicity removed.** Convergence (a) for the top-of-chain ground states
alone gives Mathlib's `RiemannHypothesis`. -/
theorem rh_of_hypConv_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConv a fun n => topGS (a n)) : RiemannHypothesis :=
  rh_of_prime_side_cross (fun n => topGS_isGroundState (ha n))
    (Eventually.of_forall fun n z hz => topGS_cross (ha n) z hz) hconv zetaNoZeroInUnitInterval

end WeilForm

#print axioms WeilForm.finiteDimensional_groundL2
#print axioms WeilForm.chain_top_zeros
#print axioms WeilForm.theoremD
#print axioms WeilForm.topGS_cross
#print axioms WeilForm.rh_of_hypConv_top
