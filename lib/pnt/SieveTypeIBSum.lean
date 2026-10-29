/-
# The leaves by the bilinear estimate: a family of leaves

Plain statements. `bdP` is a block pair's bound (`SieveTypeIBEv.bdP`), and the splines are those of `SieveTypeIBEv` at
the scale `D = ρ^{β₁+β₂}` of a block pair of `blk ρ`.

* `bdP_le`: let a block pair `(β₁, β₂)` hold `d₁` and `d₂` with `d₁ ≤ X₁`, `d₁d₂² ≤ X₂` and `X₃ ≤ d₁d₂`, and let a
  spline `t` have length and mass at most `N₂/D + ηN₁/(Dρ²)`, step `ℓ ≥ ηN₁/(rDρ²)` and power `r`. Then `bdP ≤ bdU`,
  `bdU = √(ρ²(1 + η)N₂(ρX₁/q + 1)F((1 + η)ρ²N₂/(X₃q) + 1)) + ρ²(1 + η)N₂(rρ³X₂/(ηN₁))^r + ρ²√(X₁X₂)d(q)/φ(q)`.
* `mass_leaf_le`, `massd_le`, `errL_le`: at a leaf `d₁d₂` and a weight `f`, the splines at the block pair of
  `(d₁f, d₂)` have masses differing by at most `Θ/(d₁d₂) + 2`, `Θ = (N₁ + N₂)(ρ² − 1) + 2ηN₁`, and `(B − A)d₁fd₂` at
  most `(1 + η)ρ²N₂`; so the leaf's main errors (`SieveTypeIBLeaf.errL`) are at most
  `(N₂ − N₁)|Γ|/(qd₁d₂) + (W₁ + W₂)(Θ/(d₁d₂) + 4)/q + 2(W₁ + W₂)d(q)/φ(q)`, `W_i = Σ|λ_i|`.
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

/-- The uniform bound of a block pair in the region `d₁ ≤ X₁`, `d₁d₂² ≤ X₂`, `d₁d₂ ≥ X₃`. -/
noncomputable def bdU (q : ℕ) (ρ η : ℝ) (N₁ N₂ r F : ℕ) (X₁ X₂ X₃ : ℝ) : ℝ :=
  √(ρ ^ 2 * (1 + η) * N₂ * (ρ * X₁ / q + 1) * F * ((1 + η) * ρ ^ 2 * N₂ / (X₃ * q) + 1)) +
    ρ ^ 2 * (1 + η) * N₂ * (r * ρ ^ 3 * X₂ / (η * N₁)) ^ r + ρ ^ 2 * √(X₁ * X₂) * ((q.divisors.card : ℝ) / q.totient)

set_option maxHeartbeats 1000000 in
/-- **A block pair in the region.** If the block pair `(β₁, β₂)` holds `d₁`, `d₂` with `d₁ ≤ X₁`, `d₁d₂² ≤ X₂` and
`X₃ ≤ d₁d₂`, and the spline `t` has length and mass at most `N₂/D + ηN₁/(Dρ²)` (`D = ρ^{β₁+β₂}`), step at least
`ηN₁/(rDρ²)` and power `r`, then `bdP ≤ bdU`. -/
theorem bdP_le (q : ℕ) [NeZero q] {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) {N₁ N₂ : ℕ} (hN₁ : 1 ≤ N₁) (hN : N₁ ≤ N₂)
    {r : ℕ} (hr : 1 ≤ r) (F : ℕ) {X₁ X₂ X₃ : ℝ} (hX₃ : 0 < X₃) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (h1 : (d₁ : ℝ) ≤ X₁) (h2 : (d₁ : ℝ) * d₂ ^ 2 ≤ X₂) (h3 : X₃ ≤ (d₁ : ℝ) * d₂) (t : ℕ × ℕ × ℕ × ℕ)
    (hlen : lenv t ≤ N₂ / ρ ^ (blk ρ d₁ + blk ρ d₂) + η * N₁ / (ρ ^ (blk ρ d₁ + blk ρ d₂) * ρ ^ 2))
    (hmass : massv t ≤ N₂ / ρ ^ (blk ρ d₁ + blk ρ d₂) + η * N₁ / (ρ ^ (blk ρ d₁ + blk ρ d₂) * ρ ^ 2))
    (hℓ : η * N₁ / (r * ρ ^ (blk ρ d₁ + blk ρ d₂) * ρ ^ 2) ≤ t.2.2.1) (hrt : t.2.2.2 = r) :
    bdP q ρ (blk ρ d₁) (blk ρ d₂) t F ≤ bdU q ρ η N₁ N₂ r F X₁ X₂ X₃ := by
  have hρ0 : 0 < ρ := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  obtain ⟨hs₁, hs₁'⟩ := blk_spec hρ hd₁
  obtain ⟨hs₂, hs₂'⟩ := blk_spec hρ hd₂
  set β₁ := blk ρ d₁ with hβ₁
  set β₂ := blk ρ d₂ with hβ₂
  set D : ℝ := ρ ^ (β₁ + β₂) with hD
  have hD0 : 0 < D := by positivity
  clear_value β₁ β₂ D
  have hd₁R : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂R : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ.le
  have hN₁R : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hNR : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
  -- the block pair's scales
  have hP₁ : ρ ^ (β₁ + 1) ≤ ρ * X₁ := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (hs₁.trans h1) hρ0.le
  have hPP : ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) = ρ ^ 2 * D := by rw [hD, pow_add]; ring
  have hDd : D ≤ (d₁ : ℝ) * d₂ := by rw [hD, pow_add]; exact mul_le_mul hs₁ hs₂ (by positivity) (by positivity)
  have hdD : (d₁ : ℝ) * d₂ < D * ρ ^ 2 := by
    calc (d₁ : ℝ) * d₂ < ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) := mul_lt_mul'' hs₁' hs₂' (by positivity) (by positivity)
      _ = D * ρ ^ 2 := by rw [hPP]; ring
  have hXD : X₃ / ρ ^ 2 ≤ D := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- the length: `n ≤ (1 + η)N₂/D`
  have hn1 : N₂ / D + η * N₁ / (D * ρ ^ 2) ≤ (1 + η) * N₂ / D := by
    have : η * N₁ / (D * ρ ^ 2) ≤ η * N₂ / D := by
      rw [div_le_div_iff₀ (by positivity) hD0]
      have : η * N₁ * D ≤ η * N₂ * D := by gcongr
      nlinarith [mul_nonneg (mul_nonneg hη.le (by positivity : (0 : ℝ) ≤ N₂)) hD0.le]
    rw [add_mul, add_div, one_mul]
    linarith
  have hlen' : lenv t ≤ (1 + η) * N₂ / D := hlen.trans hn1
  have hmass' : massv t ≤ (1 + η) * N₂ / D := hmass.trans hn1
  have hlen0 : 0 ≤ lenv t := Nat.cast_nonneg _
  have hmass0 : 0 ≤ massv t := Nat.cast_nonneg _
  have hX₁ : 0 ≤ X₁ := le_trans (by positivity) h1
  have hX₂ : 0 ≤ X₂ := le_trans (by positivity) h2
  -- the first term
  have hA : √(ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * (ρ ^ (β₁ + 1) / q + 1) * F * (lenv t / q + 1) * lenv t) ≤
      √(ρ ^ 2 * (1 + η) * N₂ * (ρ * X₁ / q + 1) * F * ((1 + η) * ρ ^ 2 * N₂ / (X₃ * q) + 1)) := by
    apply Real.sqrt_le_sqrt
    have e1 : ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * lenv t ≤ ρ ^ 2 * (1 + η) * N₂ := by
      rw [hPP]
      calc ρ ^ 2 * D * lenv t ≤ ρ ^ 2 * D * ((1 + η) * N₂ / D) := by gcongr
        _ = ρ ^ 2 * (1 + η) * N₂ := by field_simp
    have e2 : ρ ^ (β₁ + 1) / q + 1 ≤ ρ * X₁ / q + 1 := by gcongr
    have e3 : lenv t / q + 1 ≤ (1 + η) * ρ ^ 2 * N₂ / (X₃ * q) + 1 := by
      have : lenv t ≤ (1 + η) * ρ ^ 2 * N₂ / X₃ := by
        refine hlen'.trans ?_
        rw [div_le_div_iff₀ hD0 hX₃]
        have : X₃ ≤ D * ρ ^ 2 := by rw [div_le_iff₀ (by positivity)] at hXD; linarith
        have h0 : (0 : ℝ) ≤ (1 + η) * N₂ := by positivity
        nlinarith
      have : lenv t / q ≤ (1 + η) * ρ ^ 2 * N₂ / (X₃ * q) := by
        rw [div_le_div_iff₀ hq (by positivity)]
        rw [le_div_iff₀ hX₃] at this
        nlinarith
      linarith
    have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
    calc ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * (ρ ^ (β₁ + 1) / q + 1) * F * (lenv t / q + 1) * lenv t
        = (ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * lenv t) * (ρ ^ (β₁ + 1) / q + 1) * F * (lenv t / q + 1) := by ring
      _ ≤ (ρ ^ 2 * (1 + η) * N₂) * (ρ * X₁ / q + 1) * F * ((1 + η) * ρ ^ 2 * N₂ / (X₃ * q) + 1) := by
        gcongr
      _ = ρ ^ 2 * (1 + η) * N₂ * (ρ * X₁ / q + 1) * F * ((1 + η) * ρ ^ 2 * N₂ / (X₃ * q) + 1) := by ring
  -- the tail
  have hB : massv t * (ρ ^ (β₂ + 1) / t.2.2.1) ^ t.2.2.2 * (ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1)) ≤
      ρ ^ 2 * (1 + η) * N₂ * (r * ρ ^ 3 * X₂ / (η * N₁)) ^ r := by
    rw [hrt, hPP]
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hℓ0 : 0 < η * N₁ / (r * D * ρ ^ 2) := by positivity
    have hℓ' : η * N₁ / (r * D * ρ ^ 2) ≤ t.2.2.1 := hℓ
    have hP₂ : ρ ^ (β₂ + 1) / t.2.2.1 ≤ r * ρ ^ 3 * X₂ / (η * N₁) := by
      calc ρ ^ (β₂ + 1) / t.2.2.1 ≤ ρ ^ (β₂ + 1) / (η * N₁ / (r * D * ρ ^ 2)) :=
            div_le_div_of_nonneg_left (by positivity) hℓ0 hℓ'
        _ = r * ρ ^ 3 * (ρ ^ β₂ * D) / (η * N₁) := by
            field_simp
            ring
        _ ≤ r * ρ ^ 3 * X₂ / (η * N₁) := by
            gcongr
            calc ρ ^ β₂ * D ≤ d₂ * (d₁ * d₂) := mul_le_mul hs₂ hDd hD0.le (by positivity)
              _ = d₁ * d₂ ^ 2 := by ring
              _ ≤ X₂ := h2
    have hpow : (ρ ^ (β₂ + 1) / t.2.2.1) ^ r ≤ (r * ρ ^ 3 * X₂ / (η * N₁)) ^ r :=
      pow_le_pow_left₀ (by positivity) hP₂ r
    have hmD : massv t * (ρ ^ 2 * D) ≤ ρ ^ 2 * (1 + η) * N₂ := by
      calc massv t * (ρ ^ 2 * D) ≤ (1 + η) * N₂ / D * (ρ ^ 2 * D) := by gcongr
        _ = ρ ^ 2 * (1 + η) * N₂ := by field_simp
    have hc0 : 0 ≤ (ρ ^ (β₂ + 1) / (t.2.2.1 : ℝ)) ^ r := by positivity
    have hb0 : 0 ≤ ρ ^ 2 * (1 + η) * (N₂ : ℝ) := by positivity
    have key := mul_le_mul hmD hpow hc0 hb0
    have e : massv t * (ρ ^ (β₂ + 1) / t.2.2.1) ^ r * (ρ ^ 2 * D) =
        massv t * (ρ ^ 2 * D) * (ρ ^ (β₂ + 1) / t.2.2.1) ^ r := by ring
    rw [e]
    exact key
  -- the last term
  have hC : ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * ((q.divisors.card : ℝ) / q.totient) ≤
      ρ ^ 2 * √(X₁ * X₂) * ((q.divisors.card : ℝ) / q.totient) := by
    rw [hPP]
    gcongr
    refine hDd.trans (Real.le_sqrt_of_sq_le ?_)
    calc ((d₁ : ℝ) * d₂) ^ 2 = d₁ * (d₁ * d₂ ^ 2) := by ring
      _ ≤ X₁ * X₂ := mul_le_mul h1 h2 (by positivity) hX₁
  rw [bdP, bdU]
  linarith

/-! ### A leaf's splines -/

theorem blk_mono {ρ : ℝ} (hρ : 1 < ρ) {d d' : ℕ} (hd : 1 ≤ d) (hdd : d ≤ d') : blk ρ d ≤ blk ρ d' := by
  unfold blk
  apply Nat.floor_le_floor
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  apply div_le_div_of_nonneg_right _ hlρ.le
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hdd)

/-- The transition at a leaf: with the splines at the block pair of `(d₁f, d₂)`, the masses differ by at most
`((N₁ + N₂)(ρ² − 1) + 2ηN₁)/(d₁d₂) + 2`. -/
theorem mass_leaf_le {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {r : ℕ}
    (hr : 1 ≤ r) {d₁ f d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hf : 1 ≤ f) (hd₂ : 1 ≤ d₂) :
    massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) -
        massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f) + blk ρ d₂)) N₁ N₂ r) ≤
      ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * d₂ : ℕ) + 2 := by
  have hρ0 : 0 < ρ := by linarith
  set D : ℝ := ρ ^ (blk ρ (d₁ * f) + blk ρ d₂) with hD
  have hD0 : 0 < D := by positivity
  have hm := mass_diff_le hη hη1 hρ.le hD0 hN hr
  have hdf : 1 ≤ d₁ * f := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hpair := (blk_pair hρ hdf hd₂).2
  rw [← hD] at hpair
  have hdd : 1 ≤ d₁ * d₂ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have he1 : (1 : ℝ) ≤ (d₁ * d₂ : ℕ) := by exact_mod_cast hdd
  have he : ((d₁ * d₂ : ℕ) : ℝ) ≤ D * ρ ^ 2 := by
    refine le_trans ?_ hpair.le
    exact_mod_cast Nat.mul_le_mul_right d₂ (Nat.le_mul_of_pos_right d₁ (by omega))
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ.le
  have hN0 : (0 : ℝ) ≤ (N₁ + N₂) * (ρ ^ 2 - 1) := by positivity
  have e1 : ((N₁ : ℝ) + N₂) * (1 - 1 / ρ ^ 2) / D = (N₁ + N₂) * (ρ ^ 2 - 1) / (D * ρ ^ 2) := by
    field_simp
  have h1 : ((N₁ : ℝ) + N₂) * (ρ ^ 2 - 1) / (D * ρ ^ 2) ≤ (N₁ + N₂) * (ρ ^ 2 - 1) / (d₁ * d₂ : ℕ) :=
    div_le_div_of_nonneg_left hN0 (by linarith) he
  have h2 : η * N₁ / (D * ρ ^ 2) ≤ η * N₁ / (d₁ * d₂ : ℕ) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) he
  have e2 : ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / ((d₁ * d₂ : ℕ) : ℝ) =
      (N₁ + N₂) * (ρ ^ 2 - 1) / (d₁ * d₂ : ℕ) + 2 * (η * N₁ / (d₁ * d₂ : ℕ)) := by ring
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
`(N₂ − N₁)|Γ|/(qd) + (W₁ + W₂)(Θ/d + 4)/q + 2(W₁ + W₂)d(q)/φ(q)`, with `d = d₁d₂`, `W_i = Σ|λ_i|` and
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
        (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * d₂ : ℕ) + 4) / q +
        2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) := by
  set Θ : ℝ := ((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) / (d₁ * d₂ : ℕ) with hΘ
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h₁ : ∑ σ ∈ S₁, |l₁ σ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) + 1) ≤ (∑ σ ∈ S₁, |l₁ σ|) * (Θ + 3) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := mass_leaf_le hρ hη hη1 hN hr hd₁ (hf₁ σ hσ) hd₂
    linarith
  have h₂ : ∑ τ ∈ S₂, |l₂ τ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) + 1) ≤ (∑ τ ∈ S₂, |l₂ τ|) * (Θ + 3) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ hτ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := mass_leaf_le hρ hη hη1 hN hr hd₁ (hf₂ τ hτ) hd₂
    linarith
  rw [errL]
  have hW₁ : 0 ≤ ∑ σ ∈ S₁, |l₁ σ| := Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hW₂ : 0 ≤ ∑ τ ∈ S₂, |l₂ τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have e : (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (Θ + 4) / q =
      ((∑ σ ∈ S₁, |l₁ σ|) * (Θ + 3) + ∑ τ ∈ S₂, |l₂ τ|) / q +
        ((∑ τ ∈ S₂, |l₂ τ|) * (Θ + 3) + ∑ σ ∈ S₁, |l₁ σ|) / q := by
    ring
  rw [e]
  have k1 : (∑ σ ∈ S₁, |l₁ σ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₁ σ) + blk ρ d₂)) N₁ N₂ r) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q ≤
      ((∑ σ ∈ S₁, |l₁ σ|) * (Θ + 3) + ∑ τ ∈ S₂, |l₂ τ|) / q :=
    div_le_div_of_nonneg_right (by linarith) hq
  have k2 : (∑ τ ∈ S₂, |l₂ τ| * (massv (TPs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) -
      massv (TMs η ρ (ρ ^ (blk ρ (d₁ * f₂ τ) + blk ρ d₂)) N₁ N₂ r) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q ≤
      ((∑ τ ∈ S₂, |l₂ τ|) * (Θ + 3) + ∑ σ ∈ S₁, |l₁ σ|) / q :=
    div_le_div_of_nonneg_right (by linarith) hq
  have k3 : 2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) =
      2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient) := rfl
  linarith

/-- **A leaf's block pair.** At a leaf with `p₁fmax ≤ X₁`, `p₁fmax·p₂² ≤ X₂` and `X₃ ≤ p₁p₂`, and a weight `f ≤ fmax`,
the block pair of `(p₁f, p₂)` has `blk(p₁f) ≤ blk⌊X₁⌋`, `blk(p₂) ≤ blk⌊√X₂⌋` and `bdP ≤ bdU` for both splines. -/
theorem witness_le (q : ℕ) [NeZero q] {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) {N₁ N₂ : ℕ} (hN₁ : 1 ≤ N₁) (hN : N₁ ≤ N₂)
    {r : ℕ} (hr : 1 ≤ r) (F : ℕ) {X₁ X₂ X₃ : ℝ} (hX₃ : 0 < X₃) {p₁ f p₂ : ℕ} (hp₁ : 1 ≤ p₁) (hf : 1 ≤ f)
    (hp₂ : 1 ≤ p₂) {fmax : ℝ} (hfm : (f : ℝ) ≤ fmax) (h1 : (p₁ : ℝ) * fmax ≤ X₁)
    (h2 : (p₁ : ℝ) * fmax * (p₂ : ℝ) ^ 2 ≤ X₂) (h3 : X₃ ≤ (p₁ : ℝ) * p₂) :
    blk ρ (p₁ * f) ≤ blk ρ ⌊X₁⌋₊ ∧ blk ρ p₂ ≤ blk ρ ⌊√X₂⌋₊ ∧
      bdP q ρ (blk ρ (p₁ * f)) (blk ρ p₂) (TPs η ρ (ρ ^ (blk ρ (p₁ * f) + blk ρ p₂)) N₁ N₂ r) F ≤
        bdU q ρ η N₁ N₂ r F X₁ X₂ X₃ ∧
      bdP q ρ (blk ρ (p₁ * f)) (blk ρ p₂) (TMs η ρ (ρ ^ (blk ρ (p₁ * f) + blk ρ p₂)) N₁ N₂ r) F ≤
        bdU q ρ η N₁ N₂ r F X₁ X₂ X₃ := by
  have hρ0 : 0 < ρ := by linarith
  have hd₁ : 1 ≤ p₁ * f := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hp₁R : (1 : ℝ) ≤ p₁ := by exact_mod_cast hp₁
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hp₂R : (1 : ℝ) ≤ p₂ := by exact_mod_cast hp₂
  have hd1 : ((p₁ * f : ℕ) : ℝ) ≤ X₁ := by
    push_cast
    exact le_trans (mul_le_mul_of_nonneg_left hfm (by positivity)) h1
  have hd2 : ((p₁ * f : ℕ) : ℝ) * (p₂ : ℝ) ^ 2 ≤ X₂ := by
    push_cast
    refine le_trans ?_ h2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfm (by positivity)) (by positivity)
  have hd3 : X₃ ≤ ((p₁ * f : ℕ) : ℝ) * p₂ := by
    push_cast
    refine h3.trans ?_
    have : (p₁ : ℝ) ≤ p₁ * f := le_mul_of_one_le_right (by positivity) hfR
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine ⟨blk_mono hρ hd₁ (Nat.le_floor hd1), blk_mono hρ hp₂ (Nat.le_floor ?_), ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    refine le_trans ?_ hd2
    have : (1 : ℝ) ≤ ((p₁ * f : ℕ) : ℝ) := by exact_mod_cast hd₁
    nlinarith
  · have hD0 : 0 < ρ ^ (blk ρ (p₁ * f) + blk ρ p₂) := by positivity
    have hl := len_TPs_le hη.le hρ.le hD0 N₁ N₂ hr
    exact bdP_le q hρ hη hN₁ hN hr F hX₃ hd₁ hp₂ hd1 hd2 hd3 _ hl ((massv_le_lenv _).trans hl)
      (le_stp η ρ _ N₁ r) rfl
  · have hD0 : 0 < ρ ^ (blk ρ (p₁ * f) + blk ρ p₂) := by positivity
    have hl := len_TMs_le hη.le hρ.le hD0 N₁ N₂ hr
    exact bdP_le q hρ hη hN₁ hN hr F hX₃ hd₁ hp₂ hd1 hd2 hd3 _ hl ((massv_le_lenv _).trans hl)
      (le_stp η ρ _ N₁ r) rfl

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

open Classical in
/-- **A block pair, by a witness.** Let `|λ| ≤ |l|`, and let the splines `T` give `bdP ≤ U` at every leaf
(`∏_j I_j ≠ 0`) and `(B − A)d ≤ M_m` at every `(y₁, σ), y₂` with `d = π₁(y₁)f_σπ₂(y₂)`. Then a block pair's bilinear
sum is at most `(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂U` if the pair holds a leaf (`0` if not), plus
`Σ_j 2φ(q)⁻¹Σ M_m|λ_σ|M_j(ℓ_j)/d` over the pair. -/
theorem pair_le_W (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (S : Finset κ) (f : κ → ℕ) (l lam : κ → ℝ) (hlam : ∀ σ, |lam σ| ≤ |l σ|)
    {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    {ρ : ℝ} (hρ : 1 < ρ)
    (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y) (hf : ∀ σ ∈ S, 1 ≤ f σ)
    {Mf M₂ : ℝ} (hMf0 : 0 ≤ Mf) (hMfib : ∀ d, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => π₁ x.1 * f x.2 = d), |l x.2| ≤ Mf)
    (hM₂ : ∀ d, (#(Y₂.filter (fun y => π₂ y = d)) : ℝ) ≤ M₂)
    {F : ℕ} (hF : ∀ n, 0 < n → n < q → n.divisors.card ≤ F)
    (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (hTℓ : ∀ β₁ β₂, 1 ≤ (T β₁ β₂).2.2.1) {U Mm : ℝ}
    (hU : ∀ x ∈ Y₁ ×ˢ S, ∀ y₂ ∈ Y₂, (∏ j, I j x.1 y₂) ≠ 0 →
      bdP q ρ (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂)) (T (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) F ≤ U)
    (hMm : ∀ x ∈ Y₁ ×ˢ S, ∀ y₂ ∈ Y₂,
      massv (T (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) * (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) ≤ Mm)
    (β₁ β₂ : ℕ) :
    ‖blockSum q a Y₁ Y₂ π₁ π₂ S f lam (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ) β₁ β₂ (T β₁ β₂)‖ ≤
      (if ∃ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∃ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), (∏ j, I j x.1 y₂) ≠ 0
        then ((∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) *
          (Mf * M₂ * U) else 0) +
        ∑ j, 2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂),
            Mm * |lam x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) := by
  set P₁ := (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁) with hP₁
  set P₂ := Y₂.filter (fun y => blk ρ (π₂ y) = β₂) with hP₂
  have hMs0 : ∀ j y₁ y₂, 0 ≤ Ms j (φ j y₁ + ψ j y₂) := fun j y₁ y₂ => le_trans (abs_nonneg _) (hIG j y₁ y₂)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hd0 : ∀ x ∈ Y₁ ×ˢ S, ∀ y₂ ∈ Y₂, (0 : ℝ) < (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) := by
    intro x hx y₂ hy₂
    obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx
    have := hπ₁ _ hy; have := hf _ hσ; have := hπ₂ _ hy₂
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  -- the near-boundary masses of the pair, against `M_m/d`
  have hNB : ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv (T β₁ β₂) *
      ∑ x ∈ P₁, ∑ y₂ ∈ P₂, |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) ≤
      ∑ j, 2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ P₁, ∑ y₂ ∈ P₂,
        Mm * |lam x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) := by
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y₂ hy₂ => ?_
    obtain ⟨hx1, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨hy1, hyb⟩ := Finset.mem_filter.1 hy₂
    have hm := hMm x hx1 y₂ hy1
    rw [hxb, hyb] at hm
    have hd := hd0 x hx1 y₂ hy1
    rw [le_div_iff₀ hd]
    have h0 : 0 ≤ |lam x.2| * Ms j (φ j x.1 + ψ j y₂) := mul_nonneg (abs_nonneg _) (hMs0 j x.1 y₂)
    nlinarith
  have hNB0 : 0 ≤ ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv (T β₁ β₂) *
      ∑ x ∈ P₁, ∑ y₂ ∈ P₂, |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ?_)
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y₂ _ => mul_nonneg (abs_nonneg _) (hMs0 j x.1 y₂)
  split_ifs with hW
  · -- a leaf in the pair: `SieveTypeIBEv.pair_le` and `bdP ≤ U`
    obtain ⟨x, hx, y₂, hy₂, hne⟩ := hW
    obtain ⟨hx1, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨hy1, hyb⟩ := Finset.mem_filter.1 hy₂
    have hbd := hU x hx1 y₂ hy1 hne
    rw [hxb, hyb] at hbd
    have hp := pair_le a ha Y₁ Y₂ π₁ π₂ S f lam (fun y₁ y₂ => ∏ j, I j y₁ y₂) I (fun _ _ => rfl) Gs Ms hGc hGi hGf
      hMc hMi hMf φ ψ hI hG hIG hρ β₁ β₂ (T β₁ β₂) (hTℓ β₁ β₂) hπ₁ hπ₂ hf hMf0
      (fun d => le_trans (Finset.sum_le_sum fun x _ => hlam x.2) (hMfib d)) hM₂ hF
    refine hp.trans (add_le_add ?_ hNB)
    have hFN : 0 ≤ (∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖ :=
      add_nonneg (Finset.prod_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _)
        (Finset.sum_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _)
    have hM₂0 : 0 ≤ M₂ := le_trans (Nat.cast_nonneg _) (hM₂ 0)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbd (mul_nonneg hMf0 hM₂0)) hFN
  · -- no leaf: every term vanishes
    have h0 : blockSum q a Y₁ Y₂ π₁ π₂ S f lam (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ) β₁ β₂ (T β₁ β₂) = 0 := by
      rw [blockSum]
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y₂ hy₂ => ?_
      have : (∏ j, I j x.1 y₂) = 0 := by
        by_contra hne
        exact hW ⟨x, hx, y₂, hy₂, hne⟩
      simp only [this, Complex.ofReal_zero, mul_zero, zero_mul]
    rw [h0, norm_zero, zero_add]
    exact le_trans hNB0 hNB

theorem ppart_le_abs (x : ℝ) : |ppart x| ≤ |x| := by
  rw [abs_of_nonneg (ppart_nonneg x), ← ppart_add_npart]
  linarith [npart_nonneg x]

theorem npart_le_abs (x : ℝ) : |npart x| ≤ |x| := by
  rw [abs_of_nonneg (npart_nonneg x), ← ppart_add_npart]
  linarith [ppart_nonneg x]

open Classical in
/-- **The block pairs of one sieve.** With the hypotheses of `pair_le_W` for the splines `Tp` and `Tm`, and at every
leaf `blk(π₁(y₁)f_σ) ≤ K₁`, `blk(π₂(y₂)) ≤ K₂` and `bdP ≤ U` for both splines: summed over the block pairs,
`|blockSum(λ₊, Tp)| + |blockSum(λ₋, Tm)|` is at most `2(K₁ + 1)(K₂ + 1)(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂U` plus
`Σ_j 2φ(q)⁻¹Σ_{(y₁,σ),y₂} M_m|λ_σ|M_j(ℓ_j)/d`. -/
theorem blocks_le (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (S : Finset κ) (f : κ → ℕ) (l : κ → ℝ)
    {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    {ρ : ℝ} (hρ : 1 < ρ)
    (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y) (hf : ∀ σ ∈ S, 1 ≤ f σ)
    {Mf M₂ : ℝ} (hMf0 : 0 ≤ Mf) (hMfib : ∀ d, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => π₁ x.1 * f x.2 = d), |l x.2| ≤ Mf)
    (hM₂ : ∀ d, (#(Y₂.filter (fun y => π₂ y = d)) : ℝ) ≤ M₂)
    {F : ℕ} (hF : ∀ n, 0 < n → n < q → n.divisors.card ≤ F)
    (Tp Tm : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (hTℓ : ∀ β₁ β₂, 1 ≤ (Tp β₁ β₂).2.2.1 ∧ 1 ≤ (Tm β₁ β₂).2.2.1)
    {U Mm : ℝ} (hU0 : 0 ≤ U) {K₁ K₂ : ℕ}
    (hU : ∀ x ∈ Y₁ ×ˢ S, ∀ y₂ ∈ Y₂, (∏ j, I j x.1 y₂) ≠ 0 →
      blk ρ (π₁ x.1 * f x.2) ≤ K₁ ∧ blk ρ (π₂ y₂) ≤ K₂ ∧
      bdP q ρ (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂)) (Tp (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) F ≤ U ∧
      bdP q ρ (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂)) (Tm (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) F ≤ U)
    (hMm : ∀ x ∈ Y₁ ×ˢ S, ∀ y₂ ∈ Y₂,
      massv (Tp (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) * (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) ≤ Mm ∧
      massv (Tm (blk ρ (π₁ x.1 * f x.2)) (blk ρ (π₂ y₂))) * (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) ≤ Mm) :
    ∑ β₁ ∈ (Y₁ ×ˢ S).image (fun x => blk ρ (π₁ x.1 * f x.2)), ∑ β₂ ∈ Y₂.image (fun y => blk ρ (π₂ y)),
        (‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => ppart (l σ)) (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
            β₁ β₂ (Tp β₁ β₂)‖ +
          ‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => npart (l σ)) (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
            β₁ β₂ (Tm β₁ β₂)‖) ≤
      2 * (((K₁ + 1) * (K₂ + 1) : ℕ) : ℝ) *
          (((∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) *
            (Mf * M₂ * U)) +
        ∑ j, 2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂,
          Mm * |l x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) := by
  set FN := (∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖
    with hFN
  have hFN0 : 0 ≤ FN := add_nonneg (Finset.prod_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _)
    (Finset.sum_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _)
  have hM₂0 : 0 ≤ M₂ := le_trans (Nat.cast_nonneg _) (hM₂ 0)
  set C := FN * (Mf * M₂ * U) with hC
  have hC0 : 0 ≤ C := by positivity
  set B₁ := (Y₁ ×ˢ S).image (fun x => blk ρ (π₁ x.1 * f x.2)) with hB₁
  set B₂ := Y₂.image (fun y => blk ρ (π₂ y)) with hB₂
  set W : ℕ × ℕ → Prop := fun β => ∃ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β.1),
    ∃ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β.2), (∏ j, I j x.1 y₂) ≠ 0 with hW
  set g : ι₁ × κ → ι₂ → Fin J → ℝ := fun x y₂ j =>
    Mm * |l x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) with hg
  set c₀ : ℝ := 2 * (q.totient : ℝ)⁻¹ with hc₀
  -- each block pair
  have hpair : ∀ β₁ β₂,
      ‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => ppart (l σ)) (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
          β₁ β₂ (Tp β₁ β₂)‖ +
        ‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => npart (l σ)) (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
          β₁ β₂ (Tm β₁ β₂)‖ ≤
      2 * (if W (β₁, β₂) then C else 0) +
        ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), g x y₂ j := by
    intro β₁ β₂
    have hp := pair_le_W a ha Y₁ Y₂ π₁ π₂ S f l (fun σ => ppart (l σ)) (fun σ => ppart_le_abs _) I Gs Ms hGc hGi
      hGf hMc hMi hMf φ ψ hI hG hIG hρ hπ₁ hπ₂ hf hMf0 hMfib hM₂ hF Tp (fun β₁ β₂ => (hTℓ β₁ β₂).1)
      (U := U) (Mm := Mm) (fun x hx y₂ hy₂ hne => (hU x hx y₂ hy₂ hne).2.2.1) (fun x hx y₂ hy₂ => (hMm x hx y₂ hy₂).1)
      β₁ β₂
    have hm := pair_le_W a ha Y₁ Y₂ π₁ π₂ S f l (fun σ => npart (l σ)) (fun σ => npart_le_abs _) I Gs Ms hGc hGi
      hGf hMc hMi hMf φ ψ hI hG hIG hρ hπ₁ hπ₂ hf hMf0 hMfib hM₂ hF Tm (fun β₁ β₂ => (hTℓ β₁ β₂).2)
      (U := U) (Mm := Mm) (fun x hx y₂ hy₂ hne => (hU x hx y₂ hy₂ hne).2.2.2) (fun x hx y₂ hy₂ => (hMm x hx y₂ hy₂).2)
      β₁ β₂
    have hite : (if ∃ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
        ∃ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), (∏ j, I j x.1 y₂) ≠ 0 then FN * (Mf * M₂ * U) else 0) =
        if W (β₁, β₂) then C else 0 := rfl
    rw [hite] at hp hm
    have hsplit : ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂),
            Mm * |ppart (l x.2)| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) +
        ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂),
            Mm * |npart (l x.2)| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f x.2 * π₂ y₂ : ℕ) =
        ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
          ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), g x y₂ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y₂ _ => ?_
      simp only [hg]
      rw [abs_of_nonneg (ppart_nonneg _), abs_of_nonneg (npart_nonneg _), ← ppart_add_npart]
      ring
    linarith
  -- the leaves' block pairs number at most `(K₁ + 1)(K₂ + 1)`
  have hcount : ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂, (if W (β₁, β₂) then C else 0) ≤ (((K₁ + 1) * (K₂ + 1) : ℕ) : ℝ) * C := by
    rw [← Finset.sum_product' (f := fun β₁ β₂ => if W (β₁, β₂) then C else 0), Finset.sum_ite, Finset.sum_const_zero,
      add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hC0
    have hsub : (B₁ ×ˢ B₂).filter (fun β => W (β.1, β.2)) ⊆ Finset.range (K₁ + 1) ×ˢ Finset.range (K₂ + 1) := by
      intro β hβ
      obtain ⟨-, x, hx, y₂, hy₂, hne⟩ := Finset.mem_filter.1 hβ
      obtain ⟨hx1, hxb⟩ := Finset.mem_filter.1 hx
      obtain ⟨hy1, hyb⟩ := Finset.mem_filter.1 hy₂
      obtain ⟨hK₁, hK₂, -⟩ := hU x hx1 y₂ hy1 hne
      rw [hxb] at hK₁
      rw [hyb] at hK₂
      exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_range, Finset.card_range] at this
    exact_mod_cast this
  -- the near-boundary masses make up the whole family
  have hNB : ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂, ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
      ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), g x y₂ j =
      ∑ j, c₀ * ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, g x y₂ j := by
    rw [Finset.sum_congr rfl fun β₁ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_pairs Y₁ Y₂ S (fun x => blk ρ (π₁ x.1 * f x.2)) (fun y => blk ρ (π₂ y)) (fun x y₂ => g x y₂ j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun β₁ _ => ?_
    rw [Finset.mul_sum]
  calc _ ≤ ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂, (2 * (if W (β₁, β₂) then C else 0) +
          ∑ j, c₀ * ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
            ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), g x y₂ j) :=
        Finset.sum_le_sum fun β₁ _ => Finset.sum_le_sum fun β₂ _ => hpair β₁ β₂
    _ = 2 * ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂, (if W (β₁, β₂) then C else 0) + ∑ j, c₀ * ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, g x y₂ j := by
        rw [← hNB, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun β₁ _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2 * ((((K₁ + 1) * (K₂ + 1) : ℕ) : ℝ) * C) + ∑ j, c₀ * ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, g x y₂ j := by
        linarith
    _ = _ := by rw [hc₀, hg]; ring

/-- `bdU ≥ 0` for `X₁, X₂ ≥ 0` and `η > 0`. -/
theorem bdU_nonneg (q : ℕ) {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) (N₁ N₂ r F : ℕ) {X₁ X₂ X₃ : ℝ} (hX₂ : 0 ≤ X₂) :
    0 ≤ bdU q ρ η N₁ N₂ r F X₁ X₂ X₃ := by
  unfold bdU
  have h1 : 0 ≤ (r : ℝ) * ρ ^ 3 * X₂ / (η * N₁) := by positivity
  positivity

set_option maxHeartbeats 1600000 in
open Classical in
/-- **A family of leaves by the bilinear estimate.** Let the leaves `(y₁, y₂)` carry the comparisons
`c = ∏_j I_j` of `SieveTypeIBFam.typeIB_sharp0`, the sieve weights `S₁` above and `S₂` below sandwich `R`, with
divisors `f ≤ f_max`, and the fibres be bounded (`M_f`, `M₂`, as in `SieveTypeIBEv.pair_le`); let `d(n) ≤ F` for
`0 < n < q`, `ρ > 1`, `0 < η ≤ 1` and `r ≥ 1`, and let every leaf (`c ≠ 0`) have `π₁f_max ≤ X₁`,
`π₁f_maxπ₂² ≤ X₂` and `X₃ ≤ π₁π₂`. Then `|Σ_{y₁,y₂} c Σ_m rng(d, m)R(m)dw(dm)|`, `d = π₁π₂`, is at most
`Σ_y c·((N₂ − N₁)|Γ|/(qd) + (W₁ + W₂)(Θ/d + 4)/q + 2(W₁ + W₂)d(q)/φ(q))` (`errL_le`, with
`Θ = (N₁ + N₂)(ρ² − 1) + 2ηN₁`) plus `4(K₁ + 1)(K₂ + 1)(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂·bdU`
(`K₁ = blk⌊X₁⌋`, `K₂ = blk⌊√X₂⌋`) plus the near-boundary masses
`Σ_j 2φ(q)⁻¹Σ_{(y₁,σ),y₂} (1 + η)ρ²N₂|λ_σ|M_j(ℓ_j)/(π₁f_σπ₂)` of both sieves. -/
theorem leaves_family (a : ZMod q) (ha : IsUnit a) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (hN₁ : 1 ≤ N₁)
    {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y)
    {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    (R : ℕ → ℝ) {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (hR₁ : ∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (hR₂ : ∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m)
    {fmax : ℝ} (hfm₁ : ∀ σ ∈ S₁, (f₁ σ : ℝ) ≤ fmax) (hfm₂ : ∀ τ ∈ S₂, (f₂ τ : ℝ) ≤ fmax)
    {Mf M₂ : ℝ} (hMf0 : 0 ≤ Mf)
    (hMf₁ : ∀ d, ∑ x ∈ (Y₁ ×ˢ S₁).filter (fun x => π₁ x.1 * f₁ x.2 = d), |l₁ x.2| ≤ Mf)
    (hMf₂ : ∀ d, ∑ x ∈ (Y₁ ×ˢ S₂).filter (fun x => π₁ x.1 * f₂ x.2 = d), |l₂ x.2| ≤ Mf)
    (hM₂ : ∀ d, (#(Y₂.filter (fun y => π₂ y = d)) : ℝ) ≤ M₂)
    {F : ℕ} (hF : ∀ n, 0 < n → n < q → n.divisors.card ≤ F)
    {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) (hη1 : η ≤ 1) {r : ℕ} (hr : 1 ≤ r)
    {X₁ X₂ X₃ : ℝ} (hX₂ : 0 ≤ X₂) (hX₃ : 0 < X₃)
    (hreg : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∏ j, I j y₁ y₂) ≠ 0 →
      (π₁ y₁ : ℝ) * fmax ≤ X₁ ∧ (π₁ y₁ : ℝ) * fmax * (π₂ y₂ : ℝ) ^ 2 ≤ X₂ ∧ X₃ ≤ (π₁ y₁ : ℝ) * π₂ y₂) :
    |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, I j y₁ y₂) * ∑ m ∈ range (N₂ + 1),
        rng N₁ N₂ (π₁ y₁ * π₂ y₂) m * R m * dwR q a (π₁ y₁ * π₂ y₂ * m)| ≤
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, I j y₁ y₂) *
          (((N₂ : ℝ) - N₁) / q * (|∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| /
              (π₁ y₁ * π₂ y₂ : ℕ)) +
            (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) /
              (π₁ y₁ * π₂ y₂ : ℕ) + 4) / q +
            2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient)) +
        4 * (((blk ρ ⌊X₁⌋₊ + 1) * (blk ρ ⌊√X₂⌋₊ + 1) : ℕ) : ℝ) *
          (((∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) *
            (Mf * M₂ * bdU q ρ η N₁ N₂ r F X₁ X₂ X₃)) +
        (∑ j, 2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ Y₁ ×ˢ S₁, ∑ y₂ ∈ Y₂,
            (1 + η) * ρ ^ 2 * N₂ * |l₁ x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f₁ x.2 * π₂ y₂ : ℕ) +
          ∑ j, 2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ Y₁ ×ˢ S₂, ∑ y₂ ∈ Y₂,
            (1 + η) * ρ ^ 2 * N₂ * |l₂ x.2| * Ms j (φ j x.1 + ψ j y₂) / (π₁ x.1 * f₂ x.2 * π₂ y₂ : ℕ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hc0 : ∀ y₁ y₂, 0 ≤ ∏ j, I j y₁ y₂ := fun y₁ y₂ => Finset.prod_nonneg fun j _ => (hI j y₁ y₂).1
  set TP : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ := fun β₁ β₂ => TPs η ρ (ρ ^ (β₁ + β₂)) N₁ N₂ r with hTP
  set TM : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ := fun β₁ β₂ => TMs η ρ (ρ ^ (β₁ + β₂)) N₁ N₂ r with hTM
  set U := bdU q ρ η N₁ N₂ r F X₁ X₂ X₃ with hUdef
  have hU0 : 0 ≤ U := bdU_nonneg q hρ0.le hη N₁ N₂ r F hX₂
  have hd1 : ∀ {p f : ℕ}, 1 ≤ p → 1 ≤ f → 1 ≤ p * f := fun hp hf =>
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  -- the sandwich at every leaf and weight
  have hsp₁ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ σ ∈ S₁,
      ∀ k, splv (TM (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂))) k ≤ rng N₁ N₂ (π₁ y₁ * f₁ σ * π₂ y₂) k ∧
        rng N₁ N₂ (π₁ y₁ * f₁ σ * π₂ y₂) k ≤ splv (TP (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂))) k := by
    intro y₁ hy₁ y₂ hy₂ σ hσ k
    obtain ⟨h1, h2⟩ := blk_pair hρ (hd1 (hπ₁ y₁ hy₁) (hf₁ σ hσ)) (hπ₂ y₂ hy₂)
    exact sandwich hη.le hη1 hρ.le (by positivity) N₁ N₂ hr h1 h2 k
  have hsp₂ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ τ ∈ S₂,
      ∀ k, splv (TM (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂))) k ≤ rng N₁ N₂ (π₁ y₁ * f₂ τ * π₂ y₂) k ∧
        rng N₁ N₂ (π₁ y₁ * f₂ τ * π₂ y₂) k ≤ splv (TP (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂))) k := by
    intro y₁ hy₁ y₂ hy₂ τ hτ k
    obtain ⟨h1, h2⟩ := blk_pair hρ (hd1 (hπ₁ y₁ hy₁) (hf₂ τ hτ)) (hπ₂ y₂ hy₂)
    exact sandwich hη.le hη1 hρ.le (by positivity) N₁ N₂ hr h1 h2 k
  have hlb := leaves_bound (q := q) a N₁ N₂ hN Y₁ Y₂ π₁ π₂ hπ₁ hπ₂ (fun y₁ y₂ => ∏ j, I j y₁ y₂)
    (fun y₁ _ y₂ _ => hc0 y₁ y₂) R
    S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂
    (fun y₁ y₂ σ => TP (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂)))
    (fun y₁ y₂ σ => TM (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂)))
    (fun y₁ y₂ τ => TP (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂)))
    (fun y₁ y₂ τ => TM (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂)))
    (fun _ _ _ _ _ _ => ⟨one_le_stp _ _ _ _ _, one_le_stp _ _ _ _ _⟩)
    (fun _ _ _ _ _ _ => ⟨one_le_stp _ _ _ _ _, one_le_stp _ _ _ _ _⟩)
    hsp₁ hsp₂
  beta_reduce at hlb
  refine hlb.trans ?_
  -- the main errors, leaf by leaf
  have hE : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, I j y₁ y₂) *
      errL q N₁ N₂ (π₁ y₁ * π₂ y₂) S₁ f₁ l₁ S₂ f₂ l₂
        (fun σ => TP (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂))) (fun σ => TM (blk ρ (π₁ y₁ * f₁ σ)) (blk ρ (π₂ y₂)))
        (fun τ => TP (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂))) (fun τ => TM (blk ρ (π₁ y₁ * f₂ τ)) (blk ρ (π₂ y₂))) ≤
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, I j y₁ y₂) *
          (((N₂ : ℝ) - N₁) / q * (|∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| /
              (π₁ y₁ * π₂ y₂ : ℕ)) +
            (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (((N₁ + N₂) * (ρ ^ 2 - 1) + 2 * η * N₁) /
              (π₁ y₁ * π₂ y₂ : ℕ) + 4) / q +
            2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * ((q.divisors.card : ℝ) / q.totient)) :=
    Finset.sum_le_sum fun y₁ hy₁ => Finset.sum_le_sum fun y₂ hy₂ => mul_le_mul_of_nonneg_left
      (errL_le q hN hρ hη.le hη1 hr (hπ₁ y₁ hy₁) (hπ₂ y₂ hy₂) S₁ f₁ l₁ hf₁ S₂ f₂ l₂ hf₂) (hc0 y₁ y₂)
  have hU₁ := abs_dwU_le (q := q) a Y₁ Y₂ π₁ π₂ S₁ f₁ l₁ (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
    ((Y₁ ×ˢ S₁).image (fun x => blk ρ (π₁ x.1 * f₁ x.2))) (Y₂.image (fun y => blk ρ (π₂ y)))
    (fun x hx => Finset.mem_image.2 ⟨x, hx, rfl⟩) (fun y hy => Finset.mem_image.2 ⟨y, hy, rfl⟩) TP TM
  have hB₁ := blocks_le a ha Y₁ Y₂ π₁ π₂ S₁ f₁ l₁ I Gs Ms hGc hGi hGf hMc hMi hMf φ ψ hI hG hIG hρ hπ₁ hπ₂ hf₁
    hMf0 hMf₁ hM₂ hF TP TM (fun _ _ => ⟨one_le_stp _ _ _ _ _, one_le_stp _ _ _ _ _⟩) hU0
    (fun x hx y₂ hy₂ hne => by
      obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx
      obtain ⟨h1, h2, h3⟩ := hreg x.1 hy y₂ hy₂ hne
      exact witness_le q hρ hη hN₁ hN hr F hX₃ (hπ₁ _ hy) (hf₁ _ hσ) (hπ₂ _ hy₂) (hfm₁ _ hσ) h1 h2 h3)
    (fun x hx y₂ hy₂ => by
      obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx
      exact massd_le hρ hη.le hN hr (hd1 (hπ₁ _ hy) (hf₁ _ hσ)) (hπ₂ _ hy₂))
  have hL₁ := abs_dwL_le (q := q) a Y₁ Y₂ π₁ π₂ S₂ f₂ l₂ (fun y₁ y₂ => ∏ j, I j y₁ y₂) (blk ρ) (blk ρ)
    ((Y₁ ×ˢ S₂).image (fun x => blk ρ (π₁ x.1 * f₂ x.2))) (Y₂.image (fun y => blk ρ (π₂ y)))
    (fun x hx => Finset.mem_image.2 ⟨x, hx, rfl⟩) (fun y hy => Finset.mem_image.2 ⟨y, hy, rfl⟩) TP TM
  have hB₂ := blocks_le a ha Y₁ Y₂ π₁ π₂ S₂ f₂ l₂ I Gs Ms hGc hGi hGf hMc hMi hMf φ ψ hI hG hIG hρ hπ₁ hπ₂ hf₂
    hMf0 hMf₂ hM₂ hF TM TP (fun _ _ => ⟨one_le_stp _ _ _ _ _, one_le_stp _ _ _ _ _⟩) hU0
    (fun x hx y₂ hy₂ hne => by
      obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx
      obtain ⟨h1, h2, h3⟩ := hreg x.1 hy y₂ hy₂ hne
      obtain ⟨k1, k2, k3, k4⟩ :=
        witness_le q hρ hη hN₁ hN hr F hX₃ (hπ₁ _ hy) (hf₂ _ hσ) (hπ₂ _ hy₂) (hfm₂ _ hσ) h1 h2 h3
      exact ⟨k1, k2, k4, k3⟩)
    (fun x hx y₂ hy₂ => by
      obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx
      exact (massd_le hρ hη.le hN hr (hd1 (hπ₁ _ hy) (hf₂ _ hσ)) (hπ₂ _ hy₂)).symm)
  beta_reduce at hU₁ hL₁
  linarith

end SieveTypeIBSum
