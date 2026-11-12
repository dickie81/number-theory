/-
# Type II families in two variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The paper's Lemma 4.4 (`SieveFamily.typeII_sharp`) bounds the sum over `𝒜 − ℬ/φ(q)` of a family with one polynomial
variable `m` in the window. This file is the same for two polynomial variables, with Proposition 3′ in two variables
(`SieveTwoTypeII.typeII_two_gen`) in place of the estimate on the window.

A *family in two variables* has: a large `q`; `m₁ ∈ S₁ ⊆ (P₁, 2P₁]` and `m₂ ∈ S₂ ⊆ (P₂, 2P₂]` with coefficients
`a_{m₁}` and `b_{m₂}`, the exponents `(log_q P₁, log_q P₂)` in a region `R`; `n + 1 ≤ K₀` primes `x_i` of `Sp`'s ranges
at the scales `Q_i ≥ q^{e₁}`, with the weights `f0(x_i/Q_i)` and `∏_i Q_i ≤ 2^{K₀}q^L/(P₁P₂)`; and `J` sharp comparisons
with the forms `ℓ_j = φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i`, each with a pivot among the primes. Its `A − B/φ(q)` is
the sum of its weights times `1[n ≡ a] − 1[(n, q) = 1]/φ(q)` at `n = m₁m₂∏_i x_i`.

* `TypeIITwoAt L R`: Proposition 3′ in two variables at `L` on the region `R`, pointwise in the heights: the
  conclusion of `typeII_two_gen`. `typeIITwoAt_of_zone` gives it for a curve with its counts and the zone's exponents
  on `R`; `typeIITwoAt_hx` for the curve `ghx` (the trivial count, then Huxley's density estimate) on `Zone7d L`,
  with no hypothesis; `typeIITwoAt_long` for two variables of length at least `q` with `P₁P₂ ≤ q^{L − 1/2000}`, with
  no density estimate.
* `box_two`: the estimate at one frequency of the separated sum, for the pairs: the hypothesis of
  `SieveFamilyGen.sharp_gen`. A phase `κ + Σ_j ξ_j(φ_j(m₁) + ψ_j(m₂))` is a twist of `a` times a twist of `b`, and the
  character of `m₁m₂` is the product of the characters, so the sum over the pairs is a product of two polynomials.
* `typeII_sharp_two`, **Lemma 4.4 in two variables**: given `TypeIITwoAt L R`, `f0` smooth with support in `[1/2, 2]`
  and `0 ≤ f0 ≤ F₀`, and the family's shape (`K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0`, `Λ₀ ≥ 0`), there are `δ > 0` and `q₀`
  such that for `q ≥ q₀` every family in two variables with `|a_m| ≤ A₀`, `|b_m| ≤ B₀`, `J ≤ J₀`, `|e_{ji}| ≤ E₀`,
  `ℓ_j ≤ Λ₀ log q` on the family and pivots with coefficients `±1` has `|A − B/φ(q)| ≤ A₀B₀q^{L−δ}/φ(q)`.

A comparison between the two polynomial variables, with no prime in it, is not of this kind: it has no pivot, and
its cut-off does not separate into a twist of each. Conditions on `m₁` alone or on `m₂` alone go into the
coefficients.

The file imports `SieveFamilyGen.lean` and `SieveTwoZone7D.lean`.
-/
import SieveFamilyGen
import SieveTwoZone7D

open MeasureTheory Real Complex FourierTransform Finset SieveFamily SieveFamilyGen

namespace SieveFamilyTwo

open scoped Classical ContDiff in
/-- **Proposition 3′ in two variables at `L` on the region `R`, pointwise in the heights**: the conclusion of
`SieveTypeIIHM.typeII_two_gen`. -/
def TypeIITwoAt (L : ℝ) (R : ℝ → ℝ → Prop) : Prop :=
  ∀ {f0 : ℝ → ℝ}, ContDiff ℝ ∞ f0 → Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (K₀ : ℕ) {e₁ η : ℝ}, 0 < e₁ →
    0 < η → η ≤ 1 / 100000 →
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P₁ P₂ : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      0 < P₁ → 0 < P₂ → R (Real.logb q P₁) (Real.logb q P₂) →
      ∀ (a b : ℕ → ℂ) (h₁ h₂ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a m * χ m) h₁‖ * ‖DirMean.dp S₂ (fun m => b m * χ m) h₂‖ *
            ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) *
          (Real.sqrt ((∑ m ∈ S₁, ‖a m‖ ^ 2) / P₁) * Real.sqrt ((∑ m ∈ S₂, ‖b m‖ ^ 2) / P₂))

/-- Proposition 3′ in two variables for a curve `g ≤ 1` (`hg1`) with `g(1/2) = 1` (`hg0`), its counts (`hcnt`) and
the zone's exponents on `R` (`hzone`). -/
theorem typeIITwoAt_of_zone {g : ℝ → ℝ} {L : ℝ} {R : ℝ → ℝ → Prop} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1)
    (hcnt : SieveTypeIIGen.CurveCounts g) (hzone : SieveTypeIIHM.ZoneOK g L (1 / 1000) (1 / 1000) R) :
    TypeIITwoAt L R :=
  fun hf0 hsupp K₀ _ _ he₁ hη hη1 => SieveTypeIIHM.typeII_two_gen hg1 hg0 hcnt hzone hf0 hsupp K₀ he₁ hη hη1

/-- **Proposition 3′ in two variables for the curve `ghx` on `Zone7d L`**, with no hypothesis: the trivial count
below `7789/10000` and Huxley's density estimate from there on. -/
theorem typeIITwoAt_hx (L : ℝ) : TypeIITwoAt L (SieveTwoZone7D.Zone7d L) :=
  typeIITwoAt_of_zone SieveCurveHx.ghx_le_one SieveCurveHx.ghx_half SieveCurveHx.counts_hx
    (SieveTwoZone7D.zone_hx L)

/-- **Proposition 3′ for two variables of length at least `q`** with `m₁ + m₂ + 1/2000 ≤ L`, with no density
estimate: the curve `g = 1`. -/
theorem typeIITwoAt_long (L : ℝ) : TypeIITwoAt L (fun m₁ m₂ => 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ m₁ + m₂ + 1 / 2000 ≤ L) :=
  typeIITwoAt_of_zone (g := fun _ => 1) (fun _ => le_rfl) rfl
    (SieveCurveGlue.curveCounts_of_range (SieveCurveGlue.rangeCounts_trivial (1 / 2) 1))
    (SieveTypeIIHM.zoneOK_of_long (fun _ => 1) L (1 / 1000) (1 / 1000))

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- A twisted sum over the pairs is a product of two polynomials: for coefficients `a′_{m₁}b′_{m₂}` and a phase
`κ + Σ_j ξ_j(φ_j(m₁) + ψ_j(m₂))`, the sum over `S₁ × S₂` against `χ(m₁m₂)` is `dp S₁ (a″χ) 0 · dp S₂ (b″χ) 0` with
`a″_m = a′_m e(κ + Σ_j ξ_jφ_j(m))` and `b″_m = b′_m e(Σ_j ξ_jψ_j(m))`. -/
theorem pair_sum_eq (χ : DirichletCharacter ℂ q) (S₁ S₂ : Finset ℕ) (a' b' : ℕ → ℂ) {J : ℕ} (φ ψ : Fin J → ℕ → ℝ)
    (ξ : Fin J → ℝ) (κ : ℝ) :
    ∑ m ∈ S₁ ×ˢ S₂, a' m.1 * b' m.2 *
        Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * (φ j m.1 + ψ j m.2) : ℝ) : ℂ)) * χ ((m.1 * m.2 : ℕ) : ZMod q) =
      DirMean.dp S₁ (fun m => a' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ m) 0 *
        DirMean.dp S₂ (fun m => b' m * Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m : ℝ) : ℂ)) * χ m) 0 := by
  have hdp : ∀ (S : Finset ℕ) (c : ℕ → ℂ), DirMean.dp S c 0 = ∑ m ∈ S, c m := by
    intro S c
    rw [DirMean.dp]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  rw [hdp, hdp, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  have hsplit : (κ + ∑ j, ξ j * (φ j m₁ + ψ j m₂) : ℝ) = (κ + ∑ j, ξ j * φ j m₁) + ∑ j, ξ j * ψ j m₂ := by
    simp only [mul_add, Finset.sum_add_distrib]; ring
  have hexp : Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * (φ j m₁ + ψ j m₂) : ℝ) : ℂ)) =
      Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m₁ : ℝ) : ℂ)) *
        Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m₂ : ℝ) : ℂ)) := by
    rw [hsplit, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, Nat.cast_mul, map_mul]
  ring

open scoped ContDiff in
/-- **The estimate at one frequency of the separated sum, for the pairs.** Assume Proposition 3′ in two variables
at `L` on `R` (`hII`), and let `f0` be smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀` and `e₁ > 0`. There is
`q₀` such that for `q ≥ q₀`, `S_i ⊆ (P_i, 2P_i]` with `P_i ≥ 1` and `(log_q P₁, log_q P₂)` in `R`, coefficients with
`|a′_m| ≤ A₀` and `|b′_m| ≤ B₀`, `n + 1 ≤ K₀` scales `Q_i ≥ q^{e₁}` with `∏ Q_i ≤ 2^{K₀}q^L/(P₁P₂)`, heights
`|h_i| ≤ q^{1/100000}`, and every phase `κ + Σ_j ξ_j(φ_j(m₁) + ψ_j(m₂))`: the sum over `χ ≠ 1` of the twisted sum over
the pairs times the prime sums is at most `A₀B₀q^{L − 1/50000}`. -/
theorem box_two {L : ℝ} {R : ℝ → ℝ → Prop} (hII : TypeIITwoAt L R) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ : ℝ} (he₁ : 0 < e₁) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P₁ P₂ : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      0 < P₁ → 0 < P₂ → R (Real.logb q P₁) (Real.logb q P₂) →
      ∀ (a' b' : ℕ → ℂ) {A₀ B₀ : ℝ}, (∀ m, ‖a' m‖ ≤ A₀) → (∀ m, ‖b' m‖ ≤ B₀) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) →
      ∀ {J : ℕ} (φ ψ : Fin J → ℕ → ℝ) (ξ : Fin J → ℝ) (κ : ℝ) (hh : ℕ → ℝ),
      (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ m ∈ S₁ ×ˢ S₂, a' m.1 * b' m.2 *
            Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * (φ j m.1 + ψ j m.2) : ℝ) : ℂ)) *
              χ ((m.1 * m.2 : ℕ) : ZMod q)‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤
        A₀ * B₀ * (q : ℝ) ^ (L - 1 / 50000) := by
  obtain ⟨q₀, hq₀⟩ := hII hf0 hsupp K₀ he₁ (η := 1 / 100000) (by norm_num) (by norm_num)
  refine ⟨q₀, fun q _ hq P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁ hP₂ hR a' b' A₀ B₀ hA hB n hK Q hQ hQP J φ ψ ξ κ hh hhh => ?_⟩
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (2 * π * I * (r : ℂ))‖ = 1 := fun r => by
    have : 2 * π * I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hB0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB 0)
  have hqpow : 0 ≤ (q : ℝ) ^ (L - 1 / 50000) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  -- the two twisted coefficients
  have hA'' : ∀ m, ‖a' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ))‖ ≤ A₀ := fun m => by
    rw [norm_mul, hexp1, mul_one]; exact hA m
  have hB'' : ∀ m, ‖b' m * Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m : ℝ) : ℂ))‖ ≤ B₀ := fun m => by
    rw [norm_mul, hexp1, mul_one]; exact hB m
  have h := hq₀ q hq P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁ hP₂ hR
    (fun m => a' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ)))
    (fun m => b' m * Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m : ℝ) : ℂ))) 0 0 (n + 1) hK Q hh
    (fun j hj => ⟨hQ j hj, hhh j hj⟩) hQP
  have hs₁ := sqrt_sum_sq_le hP₁ hS₁ hA''
  have hs₂ := sqrt_sum_sq_le hP₂ hS₂ hB''
  calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ S₁ ×ˢ S₂, a' m.1 * b' m.2 *
          Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * (φ j m.1 + ψ j m.2) : ℝ) : ℂ)) *
            χ ((m.1 * m.2 : ℕ) : ZMod q)‖ *
          ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖
      = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ m) 0‖ *
            ‖DirMean.dp S₂ (fun m => b' m * Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m : ℝ) : ℂ)) * χ m) 0‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [pair_sum_eq χ S₁ S₂ a' b' φ ψ ξ κ, norm_mul]
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) *
          (Real.sqrt ((∑ m ∈ S₁, ‖a' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ))‖ ^ 2) / P₁) *
            Real.sqrt ((∑ m ∈ S₂, ‖b' m * Complex.exp (2 * π * I * ((∑ j, ξ j * ψ j m : ℝ) : ℂ))‖ ^ 2) / P₂)) := h
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) * (A₀ * B₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) hA0) hqpow
    _ = A₀ * B₀ * (q : ℝ) ^ (L - 1 / 50000) := by ring

open scoped ContDiff in
open Classical in
/-- **The Type II estimate for a sharp family in two variables (Lemma 4.4 in two variables).** Assume Proposition 3′
in two variables at `L` on `R` (`hII`). Let `f0` be smooth with support in `[1/2, 2]` and `0 ≤ f0 ≤ F₀`, and fix the
family's shape: `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₀ ≥ 0`. There are `δ > 0` and `q₀` with the following property.
Let `q ≥ q₀`, let `a` be a unit mod `q`, let `m₁` run over `S₁ ⊆ (P₁, 2P₁]` and `m₂` over `S₂ ⊆ (P₂, 2P₂]`, with
`P_i ≥ 1` and `(log_q P₁, log_q P₂)` in `R`, with coefficients `|a_m| ≤ A₀` and `|b_m| ≤ B₀`, and let `n + 1 ≤ K₀`
primes `x_i` run over `Sp`'s ranges at the scales `Q_i ≥ q^{e₁}`, `∏_i Q_i ≤ 2^{K₀}q^L/(P₁P₂)`, with the weights
`f0(x_i/Q_i)`. Let `J ≤ J₀` sharp comparisons `P_j` hold when `ℓ_j = φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i > 0` and
imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`, `ℓ_j ≤ Λ₀ log q` on the family, and for each `j` a pivot `i` with
`e_{ji} = ±1`. Then the family's `|A − B/φ(q)|`, at `n = m₁m₂∏_i x_i`, is at most `A₀B₀q^{L−δ}/φ(q)`. -/
theorem typeII_sharp_two {L : ℝ} {R : ℝ → ℝ → Prop} (hII : TypeIITwoAt L R) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (hf0nn : ∀ u, 0 ≤ f0 u) {F₀ : ℝ} (hF₀ : ∀ u, f0 u ≤ F₀)
    (K₀ J₀ : ℕ) {e₁ E₀ Λ₀ : ℝ} (he₁ : 0 < e₁) (hE₀ : 0 ≤ E₀) (hΛ₀ : 0 ≤ Λ₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      0 < P₁ → 0 < P₂ → R (Real.logb q P₁) (Real.logb q P₂) →
      ∀ (ac bc : ℕ → ℂ) {A₀ B₀ : ℝ}, (∀ m, ‖ac m‖ ≤ A₀) → (∀ m, ‖bc m‖ ≤ B₀) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) →
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ ψ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ℕ × ℕ → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m.1 + ψ j m.2 + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m.1 + ψ j m.2 + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ S₁ ×ˢ S₂, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m.1 + ψ j m.2 + ∑ i, e j i * Real.log (x i) ≤ Λ₀ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      ‖Dsum q a ((S₁ ×ˢ S₂) ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => (mx.1.1 * mx.1.2) * ∏ i, mx.2 i)
          (fun mx => (ac mx.1.1 * bc mx.1.2 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (A₀ * B₀ * (q : ℝ) ^ (L - δ)) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := sharp_gen (ι := ℕ × ℕ) hf0nn hF₀ K₀ J₀ L he₁ hE₀ hΛ₀
  obtain ⟨q₂, hq₂⟩ := box_two hII hf0 hsupp K₀ he₁
  refine ⟨δ, hδ, max q₁ q₂, fun q _ hq a ha P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁ hP₂ hR ac bc A₀ B₀ hA hB n hK Q hQ hQP J hJ
    φ ψ e Pr he hP hΛ piv hpiv => ?_⟩
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hB0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB 0)
  have hP₁' : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hP₂' : (0 : ℝ) < P₂ := by exact_mod_cast hP₂
  -- the sum of the coefficients
  have hsum : ∑ m ∈ S₁ ×ˢ S₂, ‖ac m.1 * bc m.2‖ ≤ ((P₁ : ℝ) * P₂) * (A₀ * B₀) := by
    have h1 := sum_norm_le hS₁ hA
    have h2 := sum_norm_le hS₂ hB
    calc ∑ m ∈ S₁ ×ˢ S₂, ‖ac m.1 * bc m.2‖ = (∑ m ∈ S₁, ‖ac m‖) * ∑ m ∈ S₂, ‖bc m‖ := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
          refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => norm_mul _ _
      _ ≤ ((P₁ : ℝ) * A₀) * ((P₂ : ℝ) * B₀) :=
          mul_le_mul h1 h2 (Finset.sum_nonneg fun m _ => norm_nonneg _) (by positivity)
      _ = ((P₁ : ℝ) * P₂) * (A₀ * B₀) := by ring
  have hmain := hq₁ q ((le_max_left _ _).trans hq) a ha (S₁ ×ˢ S₂) (fun m => m.1 * m.2) (fun m => ac m.1 * bc m.2)
    ((P₁ : ℝ) * P₂) (A₀ * B₀) (mul_pos hP₁' hP₂') (mul_nonneg hA0 hB0) hsum n hK Q hQ hQP hJ
    (fun j m => φ j m.1 + ψ j m.2) e Pr he hP hΛ piv hpiv
  refine hmain ?_
  -- the estimate at each frequency
  intro c' hc' ξ κ hh hhh
  rcases hc' with rfl | rfl
  · exact hq₂ q ((le_max_right _ _).trans hq) P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁ hP₂ hR ac bc hA hB n hK Q hQ hQP φ ψ ξ κ
      hh hhh
  · have h := hq₂ q ((le_max_right _ _).trans hq) P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁ hP₂ hR
      (fun m => ((‖ac m‖ : ℝ) : ℂ)) (fun m => ((‖bc m‖ : ℝ) : ℂ)) (A₀ := A₀) (B₀ := B₀)
      (fun m => by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hA m)
      (fun m => by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hB m) n hK Q hQ hQP φ ψ ξ κ hh hhh
    simpa only [norm_mul, Complex.ofReal_mul] using h

end SieveFamilyTwo

#print axioms SieveFamilyTwo.typeIITwoAt_hx
#print axioms SieveFamilyTwo.typeIITwoAt_long
#print axioms SieveFamilyTwo.typeII_sharp_two
