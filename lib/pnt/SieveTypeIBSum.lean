/-
# The leaves by the bilinear estimate: a family of leaves

Plain statements. `bdP` is a block pair's bound (`SieveTypeIBEv.bdP`), and the splines are those of `SieveTypeIBEv` at
the scale `D = ρ^{β₁+β₂}` of a block pair of `blk ρ`.

* `bdP_le`: let a block pair `(β₁, β₂)` hold `d₁` and `d₂` with `d₁ ≤ X₁`, `d₁d₂² ≤ X₂` and `X₃ ≤ d₁d₂`, and let a
  spline `t` have length and mass at most `N₂/D + ηN₁/(Dρ²)`, step `ℓ ≥ ηN₁/(rDρ²)` and power `r`. Then `bdP ≤ bdU`,
  `bdU = √(ρ²(1 + η)N₂(ρX₁/q + 1)F((1 + η)ρ²N₂/(X₃q) + 1)) + ρ²(1 + η)N₂(rρ³X₂/(ηN₁))^r + ρ²√(X₁X₂)d(q)/φ(q)`.
* `mass_leaf_le`, `massd_le`, `errL_le`: at a leaf `d₁d₂` and a weight `f`, the splines at the block pair of
  `(d₁f, d₂)` have masses differing by at most `Θ/(d₁fd₂) + 2`, `Θ = (N₁ + N₂)(ρ² − 1) + 2ηN₁`, and `(B − A)d₁fd₂`
  at most `(1 + η)ρ²N₂`; so the leaf's main errors (`SieveTypeIBLeaf.errL`) are at most
  `(N₂ − N₁)|Γ|/(qd₁d₂) + (VΘ/(d₁d₂) + 4W)/q + 2W·d(q)/φ(q)`, `V = Σ|λ_i|/f_i` and `W = Σ|λ_i|` over both sieves.
* `witness_le`: at a leaf with `p₁f_max ≤ X₁`, `p₁f_max p₂² ≤ X₂` and `X₃ ≤ p₁p₂`, the block pair of `(p₁f, p₂)` has
  `blk(p₁f) ≤ blk⌊X₁⌋`, `blk(p₂) ≤ blk⌊√X₂⌋`, and `bdP ≤ bdU` for both splines.
* `pair_le_W`, `blocks_le`: a block pair's bilinear sum is at most `(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂U` if the pair
  holds a leaf and `0` if not, plus its near-boundary masses; over the block pairs of one sieve, at most
  `2(K₁ + 1)(K₂ + 1)` times that plus `Σ_j 2φ(q)⁻¹Σ_{(y₁,σ),y₂} M_m|λ_σ|M_j(ℓ_j)/(π₁f_σπ₂)` (`sum_pairs`).
* `leaves_family`: **a family of leaves.** For leaves `(y₁, y₂)` with comparisons `c = ∏_j I_j` (as in
  `SieveTypeIBFam.typeIB_sharp0`), sieve weights `S₁` above and `S₂` below `R` with divisors `f ≤ f_max`, bounded
  fibres, `d(n) ≤ F` for `0 < n < q`, and every leaf in the region `π₁f_max ≤ X₁`, `π₁f_maxπ₂² ≤ X₂`,
  `X₃ ≤ π₁π₂`: `|Σ_y c Σ_m rng(d, m)R(m)dw(dm)|` is at most the leaves' main errors (`errL_le`), plus
  `4(K₁ + 1)(K₂ + 1)(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂·bdU` with `K₁ = blk⌊X₁⌋` and `K₂ = blk⌊√X₂⌋`, plus the
  near-boundary masses of both sieves with `M_m = (1 + η)ρ²N₂`.

The proof of `leaves_family`: `SieveTypeIBLeaf.leaves_bound` with the splines `TPs`, `TMs` at the block pairs
(`SieveTypeIBEv.sandwich`, `blk_pair`); the bilinear parts by `SieveTypeIBLeaf.abs_dwU_le`, `abs_dwL_le` and
`blocks_le`, where a block pair holding a leaf is bounded by `SieveTypeIBEv.pair_le` with `bdP ≤ bdU` at the leaf
(`witness_le`), and one holding none vanishes.

The file imports `SieveTypeIBEv.lean`.
-/
import SieveTypeIBEv

open Finset

namespace SieveTypeIBSum

open SieveTypeIB SieveSpline SieveTypeIBLeaf SieveTypeIBEv

/-! ### A leaf's splines -/

theorem blk_mono {ρ : ℝ} (hρ : 1 < ρ) {d d' : ℕ} (hd : 1 ≤ d) (hdd : d ≤ d') : blk ρ d ≤ blk ρ d' := by
  unfold blk
  apply Nat.floor_le_floor
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  apply div_le_div_of_nonneg_right _ hlρ.le
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hdd)

/-- The transition at a leaf: with the splines at the block pair of `(d₁f, d₂)`, the masses differ by at most
`((N₁ + N₂)(ρ² − 1) + 2ηN₁)/(d₁fd₂) + 2`. -/
theorem mass_leaf_le {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {r : ℕ}
    (hr : 1 ≤ r) {d₁ f d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hf : 1 ≤ f) (hd₂ : 1 ≤ d₂) :
    massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) -
        massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) ≤
      ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * f * d₂ : ℕ) + 2 := by
  have hρ0 : 0 < ρ := by linarith
  set D : ℝ := ρ ^ (blk ρ (d₁ * f) + blk ρ d₂) with hD
  have hD0 : 0 < D := by positivity
  have hm := mass_diff_le hη hη1 hρ.le hD0 hN hr
  have hdf : 1 ≤ d₁ * f := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hpair := (blk_pair hρ hdf hd₂).2
  rw [← hD] at hpair
  have hdd : 1 ≤ d₁ * f * d₂ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have he1 : (1 : ℝ) ≤ (d₁ * f * d₂ : ℕ) := by exact_mod_cast hdd
  have he : ((d₁ * f * d₂ : ℕ) : ℝ) ≤ D * ρ ^ 2 := hpair.le
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ.le
  have hN0 : (0 : ℝ) ≤ (N₁ + N₂) * (ρ ^ 2 - 1) := by positivity
  have e1 : ((N₁ : ℝ) + N₂) * (1 - 1 / ρ ^ 2) / D = (N₁ + N₂) * (ρ ^ 2 - 1) / (D * ρ ^ 2) := by
    field_simp
  have h1 : ((N₁ : ℝ) + N₂) * (ρ ^ 2 - 1) / (D * ρ ^ 2) ≤ (N₁ + N₂) * (ρ ^ 2 - 1) / (d₁ * f * d₂ : ℕ) :=
    div_le_div_of_nonneg_left hN0 (by linarith) he
  have h2 : η * N₁ / (D * ρ ^ 2) ≤ η * N₁ / (d₁ * f * d₂ : ℕ) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) he
  have e2 : ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / ((d₁ * f * d₂ : ℕ) : ℝ) =
      (N₁ + N₂) * (ρ ^ 2 - 1) / (d₁ * f * d₂ : ℕ) + 2 * (η * N₁ / (d₁ * f * d₂ : ℕ)) := by ring
  rw [e2]
  linarith

theorem massv_le_lenv (t : ℕ × ℕ × ℕ × ℕ) : massv t ≤ lenv t := by
  unfold massv lenv
  exact_mod_cast Nat.sub_le_sub_right (Nat.le_add_right _ _) _

/-- The mass at a leaf: `(B − A)d ≤ (1 + η)ρ²N₂` for the splines at the block pair of `(d₁f, d₂)`, `d = d₁fd₂`. -/
theorem massd_le {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 ≤ η) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {r : ℕ} (hr : 1 ≤ r)
    {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    massv (TPs η ρ (ρ ^ (blk ρ d₁ + blk ρ d₂)) N₁ N₂ r) * (d₁ * d₂ : ℕ) ≤ (1 + η) * ρ ^ 2 * N₂ ∧
      massv (TMs η ρ (ρ ^ (blk ρ d₁ + blk ρ d₂)) N₁ N₂ r) * (d₁ * d₂ : ℕ) ≤ (1 + η) * ρ ^ 2 * N₂ := by
  have hρ0 : 0 < ρ := by linarith
  set D : ℝ := ρ ^ (blk ρ d₁ + blk ρ d₂) with hD
  have hD0 : 0 < D := by positivity
  have hpair := (blk_pair hρ hd₁ hd₂).2
  rw [← hD] at hpair
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ.le
  have hNR : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
  have hb : N₂ / D + η * N₁ / (D * ρ ^ 2) ≤ (1 + η) * N₂ / D := by
    have : η * N₁ / (D * ρ ^ 2) ≤ η * N₂ / D := by
      calc η * N₁ / (D * ρ ^ 2) ≤ η * N₁ / D :=
            div_le_div_of_nonneg_left (by positivity) hD0 (le_mul_of_one_le_right hD0.le hρ2)
        _ ≤ η * N₂ / D := by gcongr
    rw [add_mul, add_div, one_mul]
    linarith
  have key : ∀ t : ℕ × ℕ × ℕ × ℕ, massv t ≤ lenv t → lenv t ≤ N₂ / D + η * N₁ / (D * ρ ^ 2) →
      massv t * (d₁ * d₂ : ℕ) ≤ (1 + η) * ρ ^ 2 * N₂ := by
    intro t h1 h2
    have hm0 : 0 ≤ massv t := Nat.cast_nonneg _
    calc massv t * (d₁ * d₂ : ℕ) ≤ (1 + η) * N₂ / D * (D * ρ ^ 2) :=
          mul_le_mul (h1.trans (h2.trans hb)) hpair.le (Nat.cast_nonneg _) (by positivity)
      _ = (1 + η) * ρ ^ 2 * N₂ := by field_simp
  exact ⟨key _ (massv_le_lenv _) (len_TPs_le hη hρ.le hD0 N₁ N₂ hr),
    key _ (massv_le_lenv _) (len_TMs_le hη hρ.le hD0 N₁ N₂ hr)⟩

/-- **A leaf's main errors** (`SieveTypeIBLeaf.errL`) with the splines at its block pairs: at most
`(N₂ − N₁)|Γ|/(qd) + (VΘ/d + 4W)/q + 2W·d(q)/φ(q)`, with `d = d₁d₂`, `V = Σ|λ_i|/f_i`, `W = Σ|λ_i|` and
`Θ = (N₁ + N₂)(ρ² − 1) + 2ηN₁`. -/
theorem errL_le (q : ℕ) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {r : ℕ} (hr : 1 ≤ r) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ) :
    errL q N₁ N₂ (d₁ * d₂) S₁ f₁ l₁ S₂ f₂ l₂
        (fun σ => TPs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r)
        (fun σ => TMs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r)
        (fun τ => TPs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r)
        (fun τ => TMs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) ≤
      ((N₂ : ℝ) - N₁) / q * (|∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| /
          (d₁ * d₂ : ℕ)) +
        ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) *
            (((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * d₂ : ℕ)) +
          4 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|)) / q +
        2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) := by
  set Θ : ℝ := ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * d₂ : ℕ) with hΘ
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hdd : (0 : ℝ) < ((d₁ * d₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
  -- one weight: `|λ|(m⁺ − m⁻ + 1) ≤ (|λ|/f)Θ + 3|λ|`
  have one : ∀ f : ℕ, 1 ≤ f → ∀ l : ℝ, |l| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) + 1) ≤ |l| / f * Θ + 3 * |l| := by
    intro f hf l
    have hm := mass_leaf_le hρ hη hη1 hN hr hd₁ hf hd₂
    have hf0 : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    have hcast : ((d₁ * f * d₂ : ℕ) : ℝ) = (f : ℝ) * ((d₁ * d₂ : ℕ) : ℝ) := by push_cast; ring
    have e : ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / ((d₁ * f * d₂ : ℕ) : ℝ) = Θ / f := by
      rw [hcast, hΘ, div_div, mul_comm ((d₁ * d₂ : ℕ) : ℝ)]
    rw [e] at hm
    have e2 : |l| / f * Θ + 3 * |l| = |l| * (Θ / f + 3) := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h₁ : ∑ σ ∈ S₁, |l₁ σ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) + 1) ≤
      (∑ σ ∈ S₁, |l₁ σ| / f₁ σ) * Θ + 3 * ∑ σ ∈ S₁, |l₁ σ| := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun σ hσ => one _ (hf₁ σ hσ) _
  have h₂ : ∑ τ ∈ S₂, |l₂ τ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) + 1) ≤
      (∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * Θ + 3 * ∑ τ ∈ S₂, |l₂ τ| := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun τ hτ => one _ (hf₂ τ hτ) _
  rw [errL]
  have k : (∑ σ ∈ S₁, |l₁ σ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) -
        massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q +
      (∑ τ ∈ S₂, |l₂ τ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) -
        massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q ≤
      ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * Θ + 4 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|)) /
        q := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hq
  have k3 : 2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) =
      2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) := rfl
  linarith

/-! ### The sum over the block pairs -/

/-- Over all block pairs, the pairs' sums make up the whole family. -/
theorem sum_pairs {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (S : Finset κ) (b₁ : ι₁ × κ → ℕ)
    (b₂ : ι₂ → ℕ) (g : ι₁ × κ → ι₂ → ℝ) :
    ∑ β₁ ∈ (Y₁ ×ˢ S).image b₁, ∑ β₂ ∈ Y₂.image b₂, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ x = β₁),
        ∑ y₂ ∈ Y₂.filter (fun y => b₂ y = β₂), g x y₂ = ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, g x y₂ := by
  classical
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem b₁ hx)]
  refine Finset.sum_congr rfl fun β₁ _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_fiberwise_of_maps_to (fun y hy => Finset.mem_image_of_mem b₂ hy)]
  refine Finset.sum_congr rfl fun β₂ _ => ?_
  exact Finset.sum_comm

open scoped FourierTransform
open MeasureTheory

variable {q : ℕ} [NeZero q]

theorem ppart_le_abs (x : ℝ) : |ppart x| ≤ |x| := by
  rw [abs_of_nonneg (ppart_nonneg x), ← ppart_add_npart]
  linarith [npart_nonneg x]

theorem npart_le_abs (x : ℝ) : |npart x| ≤ |x| := by
  rw [abs_of_nonneg (npart_nonneg x), ← ppart_add_npart]
  linarith [ppart_nonneg x]

end SieveTypeIBSum
