/-
# The Hodge index theorem from counting: Minkowski's theorem as the bridge to `BallWeil`

Plain statement. On an arithmetic surface the Hodge index theorem comes from counting (G. Faltings, Ann. of Math. 119
(1984)). The arithmetic Riemann–Roch theorem makes the logarithm of the volume of the unit ball of the sections of
`nD`, over the covolume of their lattice, grow like `(n²/2)·D²`. When `D² > 0`, Minkowski's theorem turns that growth
into a nonzero section of norm at most `1`, of `nD` or, by duality, on the other side, and a divisor with such a
section has positive degree against an ample class. So `D² > 0` forces `D·H ≠ 0`: the Hodge index theorem. This
file states that route for the divisors `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n·D_n` of `BallWeil` (`Div`), with the ample
class `e₁ + e₂`, and proves that it is exactly the Riemann hypothesis.
* A **counting model** (`CountingModel`) gives each `D` a lattice `Λ(D) = ℤ^d` in `ℝ^d`, the span of a basis, and a
  convex symmetric body `B(D)`, its unit ball. `D` is **effective** (`CountingModel.Eff`) when `Λ(D)` has a nonzero
  point in `B(D)`, a nonzero section of norm at most `1`.
* **Ample positivity** (`CountingModel.Ample`): an effective `D` has `D·(e₁ + e₂) > 0`.
* **Riemann–Roch growth** (`CountingModel.RiemannRoch`): if `D² > 0`, then for some `n ≥ 1` the volume of the body of
  `nD` or of `−nD` exceeds `2^d` covolumes, Minkowski's bound.
* **Hilbert–Samuel growth** (`CountingModel.HilbertSamuel`): if `D² > 0`, the multiples of `D` or of `−D` have unit
  balls of volume at least `e^{cn²}` covolumes, with rank `O(n)`. Since `2^{rank}` is then `e^{O(n)}`, it implies
  Riemann–Roch growth (`CountingModel.riemannRoch_of_hilbertSamuel`), and RH holds exactly when a model with ample
  positivity and Hilbert–Samuel growth exists (`rh_iff_hilbertSamuel`): the axiom in the shape of the arithmetic
  Hilbert–Samuel theorem.
Minkowski's convex body theorem (`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`)
makes `±nD` effective (`eff_of_minkowski`), and ample positivity then gives `D·e₁ = D·e₂ = 0 ⇒ D² ≤ 0`
(`hodge_index`), which is RH (`BallWeil.rh_iff_hodge_index`, `rh_of_counting`). Conversely, under RH the
Castelnuovo–Severi inequality `D² ≤ 2(D·e₁)(D·e₂)` (`BallWeil.rh_iff_castelnuovo_severi`) puts every `D` with
`D² > 0` on one side of `D·(e₁ + e₂) = 0`, and a model with one-dimensional lattices satisfies both axioms
(`counting_of_rh`). So RH holds if and only if there is a counting model with ample positivity and Riemann–Roch growth
(`rh_iff_counting`). Like `BallWeil`'s equivalences this is a reformulation. The model of `counting_of_rh` is
degenerate: its unit balls are the whole line or empty, chosen by the sign of the degree, so the equivalence says only
that the two axioms ask for nothing beyond RH. What would count is a model built from `D`, with `Λ(nD)` and `B(nD)`
determined by `nD` as the sections of `nL̄` are by `L̄` on an arithmetic surface, and their growth governed by `D²`.

Where such lattices could come from. The orbit-lattice conjecture of `docs/ball-conjecture.md` asks for one: if in a
realization of `K_H` every `w_{k+1}` keeps distance `‖w_1‖` from the span of the earlier vectors, the orbit generates a
lattice with `w_1` shortest (`BallPsi.orbit_lattice`), and RH follows (`BallWeil.rh_of_pivots`). For the Gaussian
kernel no realization spans one (`BallLattice.not_discrete`). Over a finite field the lattice is there: the Frobenius
points of Manin's twist have a positive semidefinite Gram matrix (`ManinHasse.gram_nonneg`).
-/
import Mathlib
import BallWeil

open Real Finset MeasureTheory Module BallWeil

noncomputable section

namespace HodgeCounting

/-! ## The divisors -/

/-- A divisor `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n·D_n` of `BallWeil`, with integer coefficients. -/
structure Div where
  /-- The coefficient of `e₁`. -/
  a : ℤ
  /-- The coefficient of `e₂`. -/
  b : ℤ
  /-- The `D_n` with `n ≤ N` occur. -/
  N : ℕ
  /-- The coefficient of `D_n`. -/
  c : ℕ → ℤ

namespace Div

/-- `D²`, `BallWeil.selfInt`. -/
def sq (D : Div) : ℝ := selfInt D.a D.b D.N fun n => D.c n

/-- `D·(e₁ + e₂) = D·e₁ + D·e₂`, the degree against the ample class `e₁ + e₂`. -/
def deg (D : Div) : ℝ := deg₁ D.b D.N (fun n => D.c n) + deg₂ D.a D.N fun n => D.c n

/-- `kD`. -/
def smul (k : ℤ) (D : Div) : Div := ⟨k * D.a, k * D.b, D.N, fun n => k * D.c n⟩

lemma deg_smul (k : ℤ) (D : Div) : (D.smul k).deg = k * D.deg := by
  unfold deg smul deg₁ deg₂
  push_cast
  have h1 : ∑ n ∈ Icc 1 D.N, (k : ℝ) * D.c n = k * ∑ n ∈ Icc 1 D.N, (D.c n : ℝ) := (Finset.mul_sum ..).symm
  have h2 : ∑ n ∈ Icc 1 D.N, (k : ℝ) * D.c n * n = k * ∑ n ∈ Icc 1 D.N, (D.c n : ℝ) * n := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1, h2]
  ring

lemma smul_smul (j k : ℤ) (D : Div) : (D.smul j).smul k = D.smul (k * j) := by
  unfold smul
  congr 1 <;> first | (funext n; ring) | ring

end Div

/-! ## Counting models -/

/-- **A counting model**: for each divisor `D` a lattice `Λ(D)`, the `ℤ`-span of a basis `b(D)` of `ℝ^{d(D)}`, and a
convex symmetric body `B(D)`: the sections of `D` and the ones of norm at most `1`. -/
structure CountingModel where
  /-- The rank of the lattice of sections. -/
  d : Div → ℕ
  /-- A basis whose `ℤ`-span is the lattice of sections. -/
  b : ∀ D, Basis (Fin (d D)) ℝ (EuclideanSpace ℝ (Fin (d D)))
  /-- The unit ball. -/
  B : ∀ D, Set (EuclideanSpace ℝ (Fin (d D)))
  symm : ∀ D, ∀ x ∈ B D, -x ∈ B D
  convex : ∀ D, Convex ℝ (B D)

namespace CountingModel

variable (M : CountingModel)

/-- **`D` is effective**: its lattice has a nonzero point in its unit ball. -/
def Eff (D : Div) : Prop := ∃ x ∈ Submodule.span ℤ (Set.range (M.b D)), x ≠ 0 ∧ x ∈ M.B D

/-- **Minkowski's bound is exceeded**: the unit ball of `D` has volume more than `2^d` covolumes of its lattice. -/
def Minkowski (D : Div) : Prop :=
  volume (ZSpan.fundamentalDomain (M.b D)) * 2 ^ M.d D < volume (M.B D)

/-- **Ample positivity**: an effective divisor has positive degree against `e₁ + e₂`. -/
def Ample : Prop := ∀ D, M.Eff D → 0 < D.deg

/-- **Riemann–Roch growth**: if `D² > 0`, the unit ball of `nD` or of `−nD` exceeds Minkowski's bound for some
`n ≥ 1`. -/
def RiemannRoch : Prop :=
  ∀ D : Div, 0 < D.sq → ∃ n : ℕ, 0 < n ∧ (M.Minkowski (D.smul n) ∨ M.Minkowski (D.smul (-n)))

/-- **Minkowski's convex body theorem**: past Minkowski's bound, `D` is effective. -/
theorem eff_of_minkowski {D : Div} (h : M.Minkowski D) : M.Eff D := by
  have : Countable (Submodule.span ℤ (Set.range (M.b D))).toAddSubgroup :=
    (inferInstance : Countable (Submodule.span ℤ (Set.range (M.b D))))
  obtain ⟨x, hx0, hxB⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' (M.b D) volume) (M.symm D) (M.convex D)
    (by rw [finrank_euclideanSpace_fin]; exact h)
  exact ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), hxB⟩

/-- **Hilbert–Samuel growth along the multiples of `D`**: for some `c > 0` and `C`, for every large `n` the lattice of
`nD` has rank at most `Cn` and its unit ball has volume at least `e^{cn²}` covolumes. -/
def Grows (D : Div) : Prop :=
  ∃ c > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, (M.d (D.smul n) : ℝ) ≤ C * n ∧
    ENNReal.ofReal (Real.exp (c * n ^ 2)) * volume (ZSpan.fundamentalDomain (M.b (D.smul n))) ≤
      volume (M.B (D.smul n))

/-- **Hilbert–Samuel growth**: if `D² > 0`, the multiples of `D` or those of `−D` grow. -/
def HilbertSamuel : Prop := ∀ D : Div, 0 < D.sq → M.Grows D ∨ M.Grows (D.smul (-1))

/-- **Growth beats Minkowski's bound**: `2^{Cn}` is `e^{O(n)}`, below `e^{cn²}`, so a growing `D` has a multiple past
Minkowski's bound. -/
theorem minkowski_of_grows {D : Div} (h : M.Grows D) : ∃ n : ℕ, 0 < n ∧ M.Minkowski (D.smul n) := by
  obtain ⟨c, hc, C, hev⟩ := h
  obtain ⟨n, ⟨hd, hvol⟩, hn⟩ := (hev.and (Filter.eventually_gt_atTop ⌈|C| * Real.log 2 / c⌉₊)).exists
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  refine ⟨n, hn0, ?_⟩
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn' : |C| * Real.log 2 / c < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
  have key : (2 : ℝ) ^ M.d (D.smul n) < Real.exp (c * n ^ 2) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ M.d (D.smul n)), Real.log_pow]
    refine Real.exp_lt_exp.2 ?_
    have h1 : (M.d (D.smul n) : ℝ) * Real.log 2 ≤ |C| * n * Real.log 2 :=
      mul_le_mul_of_nonneg_right (hd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnpos.le)) hlog.le
    have h2 : |C| * Real.log 2 < c * n := by
      have := (div_lt_iff₀ hc).1 hn'
      linarith
    nlinarith
  have hF0 : volume (ZSpan.fundamentalDomain (M.b (D.smul n))) ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero _
  have hFt : volume (ZSpan.fundamentalDomain (M.b (D.smul n))) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  unfold Minkowski
  calc volume (ZSpan.fundamentalDomain (M.b (D.smul n))) * 2 ^ M.d (D.smul n)
      = ENNReal.ofReal ((2 : ℝ) ^ M.d (D.smul n)) * volume (ZSpan.fundamentalDomain (M.b (D.smul n))) := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_comm]
    _ < ENNReal.ofReal (Real.exp (c * n ^ 2)) * volume (ZSpan.fundamentalDomain (M.b (D.smul n))) :=
        ENNReal.mul_lt_mul_left hF0 hFt ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2 key)
    _ ≤ volume (M.B (D.smul n)) := hvol

/-- **Hilbert–Samuel growth gives Riemann–Roch growth.** -/
theorem riemannRoch_of_hilbertSamuel (h : M.HilbertSamuel) : M.RiemannRoch := by
  intro D hD
  rcases h D hD with hg | hg
  · obtain ⟨n, hn, hm⟩ := M.minkowski_of_grows hg
    exact ⟨n, hn, Or.inl hm⟩
  · obtain ⟨n, hn, hm⟩ := M.minkowski_of_grows hg
    rw [Div.smul_smul, mul_neg_one] at hm
    exact ⟨n, hn, Or.inr hm⟩

end CountingModel

/-! ## The Hodge index theorem and RH -/

/-- **The Hodge index theorem from counting**: in a counting model with ample positivity and Riemann–Roch growth,
`D·e₁ = D·e₂ = 0` implies `D² ≤ 0`. If `D² > 0`, Minkowski makes `nD` or `−nD` effective, of degree `±n·0 = 0`. -/
theorem hodge_index (M : CountingModel) (hA : M.Ample) (hRR : M.RiemannRoch) {D : Div}
    (h1 : deg₁ D.b D.N (fun n => D.c n) = 0) (h2 : deg₂ D.a D.N (fun n => D.c n) = 0) : D.sq ≤ 0 := by
  by_contra hpos
  obtain ⟨n, -, h⟩ := hRR D (not_le.1 hpos)
  have h0 : D.deg = 0 := by rw [Div.deg, h1, h2, add_zero]
  rcases h with h | h
  · have := hA _ (M.eff_of_minkowski h)
    rw [Div.deg_smul, h0, mul_zero] at this
    exact lt_irrefl 0 this
  · have := hA _ (M.eff_of_minkowski h)
    rw [Div.deg_smul, h0, mul_zero] at this
    exact lt_irrefl 0 this

/-- **RH from counting**: a counting model with ample positivity and Riemann–Roch growth gives the Riemann
hypothesis, through `BallWeil.rh_iff_hodge_index`. -/
theorem rh_of_counting (M : CountingModel) (hA : M.Ample) (hRR : M.RiemannRoch) : RiemannHypothesis :=
  rh_iff_hodge_index.2 fun a b N c h1 h2 => hodge_index M hA hRR (D := ⟨a, b, N, c⟩) h1 h2

/-- Under RH, `D² > 0` puts `D·e₁` and `D·e₂` on the same side of `0` (Castelnuovo–Severi,
`BallWeil.rh_iff_castelnuovo_severi`), so `D·(e₁ + e₂) ≠ 0`. -/
lemma deg_pos_or_neg_of_rh (hRH : RiemannHypothesis) {D : Div} (hD : 0 < D.sq) : 0 < D.deg ∨ D.deg < 0 := by
  have hcs := rh_iff_castelnuovo_severi.1 hRH D.a D.b D.N D.c
  have hprod : 0 < deg₁ D.b D.N (fun n => D.c n) * deg₂ D.a D.N (fun n => D.c n) := by
    unfold Div.sq at hD
    linarith
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by unfold Div.deg; linarith)
  · exact Or.inr (by unfold Div.deg; linarith)

/-- The degenerate model: one-dimensional lattices, with the whole line as unit ball when `D·(e₁ + e₂) > 0` and the
empty set otherwise. -/
def trivialModel : CountingModel where
  d _ := 1
  b _ := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  B D := if 0 < D.deg then Set.univ else ∅
  symm D x hx := by
    by_cases h : 0 < D.deg
    · simp [h]
    · simp only [h, ite_false] at hx
      exact hx.elim
  convex D := by
    by_cases h : 0 < D.deg
    · simpa [h] using convex_univ
    · simpa [h] using convex_empty

lemma trivialModel_ample : trivialModel.Ample := fun D hE => by
  obtain ⟨x, -, -, hx⟩ := hE
  by_contra h
  simp only [trivialModel, h, ite_false] at hx
  exact hx.elim

lemma volume_trivialModel_B {D : Div} (hD : 0 < D.deg) : volume (trivialModel.B D) = ⊤ := by
  have h : trivialModel.B D = Set.univ := by simp [trivialModel, hD]
  rw [h]
  exact measure_univ_of_isAddLeftInvariant (volume : Measure (EuclideanSpace ℝ (Fin 1)))

lemma trivialModel_minkowski {D : Div} (hD : 0 < D.deg) : trivialModel.Minkowski D := by
  have hF : volume (ZSpan.fundamentalDomain (trivialModel.b D)) < ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (trivialModel.b D)).measure_lt_top
  rw [CountingModel.Minkowski, volume_trivialModel_B hD]
  exact ENNReal.mul_lt_top hF (by simp)

/-- **Under RH there is such a model**: the degenerate one. By Castelnuovo–Severi, `D² > 0` puts `D·e₁` and `D·e₂` on
the same side of `0`, so `D` or `−D` has positive degree. -/
theorem counting_of_rh (hRH : RiemannHypothesis) : ∃ M : CountingModel, M.Ample ∧ M.RiemannRoch := by
  refine ⟨trivialModel, trivialModel_ample, fun D hD => ⟨1, one_pos, ?_⟩⟩
  rcases deg_pos_or_neg_of_rh hRH hD with h | h
  · exact Or.inl (trivialModel_minkowski (by rw [Div.deg_smul]; push_cast; linarith))
  · exact Or.inr (trivialModel_minkowski (by rw [Div.deg_smul]; push_cast; linarith))

/-- **RH is the Hodge index theorem from counting**: `RiemannHypothesis` holds if and only if there is a counting
model, lattices of sections with unit balls for the divisors built from the primes, with ample positivity and
Riemann–Roch growth. -/
theorem rh_iff_counting : RiemannHypothesis ↔ ∃ M : CountingModel, M.Ample ∧ M.RiemannRoch :=
  ⟨counting_of_rh, fun ⟨M, hA, hRR⟩ => rh_of_counting M hA hRR⟩

/-- Under RH the degenerate model grows: the multiples of the side of positive degree have the whole line as ball. -/
lemma trivialModel_hilbertSamuel (hRH : RiemannHypothesis) : trivialModel.HilbertSamuel := by
  have grows : ∀ D : Div, 0 < D.deg → trivialModel.Grows D := fun D hD => by
    refine ⟨1, one_pos, 1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨by simpa [trivialModel] using hn', ?_⟩
    rw [volume_trivialModel_B (by rw [Div.deg_smul]; push_cast; nlinarith)]
    exact le_top
  intro D hD
  rcases deg_pos_or_neg_of_rh hRH hD with h | h
  · exact Or.inl (grows D h)
  · exact Or.inr (grows _ (by rw [Div.deg_smul]; push_cast; linarith))

/-- **RH is the Hodge index theorem from Hilbert–Samuel growth**: `RiemannHypothesis` holds if and only if there is a
counting model with ample positivity in which, for every `D` with `D² > 0`, the multiples of `D` or of `−D` have unit
balls of volume at least `e^{cn²}` covolumes with rank `O(n)`: the shape of the arithmetic Hilbert–Samuel theorem. -/
theorem rh_iff_hilbertSamuel : RiemannHypothesis ↔ ∃ M : CountingModel, M.Ample ∧ M.HilbertSamuel :=
  ⟨fun h => ⟨trivialModel, trivialModel_ample, trivialModel_hilbertSamuel h⟩,
    fun ⟨M, hA, hHS⟩ => rh_of_counting M hA (M.riemannRoch_of_hilbertSamuel hHS)⟩

end HodgeCounting

#print axioms HodgeCounting.hodge_index
#print axioms HodgeCounting.rh_iff_counting
#print axioms HodgeCounting.CountingModel.riemannRoch_of_hilbertSamuel
#print axioms HodgeCounting.rh_iff_hilbertSamuel
