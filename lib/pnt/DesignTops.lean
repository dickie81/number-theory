import PairSetting

/-!
# The tops of the design: translates with exact or approximate coset counts

A step of the proof of the sharp frontier (`SharpInputs`, the field `SharpPieces.params`): the translates `TT` of the
design (its tops) and the field `Weights.shares` that they carry, for a character `κ` of order `o` of a finite
abelian group `A`, with kernel `A₀` (in the design, `A = S.A` and `κ` lifts `χ`).

**The tops** (`exists_TT_counts`): when `4M ≤ |A₀|`, a set `TT` with exactly `4M` elements in `A₀` and exactly `3M`
in each of the other `o − 1` cosets of `A₀`, that is, over each value `ζ ≠ 1` of `κ`. Every fibre of `κ` over a value
has `|A₀|` elements (`card_fibre`: `t ↦ u⁻¹t` maps the fibre over `κ(u)` onto `A₀`), so each fibre has a subset of the
prescribed size (`Finset.exists_subset_card_eq`), and `TT` is their union.

**Sums over the tops** (`sum_of_counts`): `Σ_{t ∈ TT} F(κ(t)) = 3M·Σ_{ζ ∈ κ(A)} F(ζ) + M·F(1)`, by summing over the
values of `κ` (`sum_comp_eq`). Two cases:
* `F = 1`: `κ` takes `o` values (`card_image_eq`, from `|A| = |κ(A)|·|A₀|` and `|A| = o·|A₀|`, `card_A_eq`), so
  `|TT| = (3o + 1)M` (`card_TT_of_counts`);
* `F(ζ) = ζ^k` with `0 < k < o`: the values of `κ^k` sum to `0` (`sum_image_pow`: `|A₀|·Σ_{ζ ∈ κ(A)} ζ^k = Σ_u κ(u)^k`,
  which vanishes as `κ^k ≠ 1`), so `Σ_{t ∈ TT} κ(t)^k = M = |TT|/(3o + 1)` (`sum_pow_of_counts`).

**The shares** (`shares_of_counts`): with scales `a₀ ≤ a_t ≤ a₀(1 + θ)` on `TT` and `2θ ≤ x^{ε−1}`, the field
`Weights.shares`, `‖Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)‖ ≤ x^{ε−1} Σ_t a_t` for `0 < k < o`. Writing `a_t = a₀ + r_t`,
the parts in `a₀` cancel by the two cases above, and what is left has norm at most
`(1 + (3o + 1)⁻¹) Σ_t r_t ≤ 2θ Σ_t a_t`, as `0 ≤ r_t ≤ θ a_t`.

**The coset counts of the archive** (`counts_archive`): for every `γ`, the tops in `γA₀` number `λ(γ)|TT|` exactly,
with `λ = 4/(3o + 1)` on `A₀` and `3/(3o + 1)` off it, so within the archive's precision `x^{ε−1}|TT|`.

**Approximate counts** (`shares_of_approx`, for the random tops of `TopsSelect`): if every coset holds
`λ(γ)|TT| + d_γ` tops with `|d_γ| ≤ η|TT|`, the part of the shares in `a₀` is `a₀Σ_ζ d_ζ ζ^k`, at most `oη Σ_t a_t`,
so the shares hold once `oη + 2θ ≤ x^{ε−1}`.

**Choices.** The archive draws `TT` with coset counts within `x^{ε−1}|TT|` of `λ(γ)|TT|`; exact counts make the
shares an identity up to the spread of the scales, and counts within `η|TT|` cost the factor `o` of
`shares_of_approx`. The statements hold for every finite abelian group, so they apply to `S.A` for every setting
`S`.
-/

open Finset

namespace ZetaBalance

variable {A : Type*} [CommGroup A] [Fintype A] (κ : A →* ℂˣ)

/-! ## The fibres and the values of a character -/

/-- **A fibre of `κ` over a value has `|A₀|` elements**: for `ζ = κ(u)`, `t ↦ u⁻¹t` maps the fibre over `ζ` onto
`A₀`, with inverse `t ↦ ut`. -/
theorem card_fibre {ζ : ℂˣ} (hζ : ζ ∈ κ.range) : (univ.filter (κ · = ζ)).card = (A₀ κ).card := by
  obtain ⟨u, rfl⟩ := hζ
  refine card_nbij' (u⁻¹ * ·) (u * ·) (fun t ht => ?_) (fun t ht => ?_) (fun t _ => ?_) (fun t _ => ?_)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
    rw [mem_coe, mem_A₀, map_mul, map_inv, ht, inv_mul_cancel]
  · rw [mem_coe, mem_A₀] at ht
    simp [ht]
  · simp
  · simp

/-- **Summing over the values of `κ`**: `Σ_{t ∈ s} F(κ(t)) = Σ_{ζ ∈ κ(A)} #{t ∈ s : κ(t) = ζ}·F(ζ)`. -/
theorem sum_comp_eq {β : Type*} [AddCommMonoid β] (s : Finset A) (F : ℂˣ → β) :
    ∑ t ∈ s, F (κ t) = ∑ ζ ∈ univ.image κ, (s.filter (κ · = ζ)).card • F ζ := by
  rw [← sum_fiberwise_of_maps_to (t := univ.image κ) (g := κ) fun t _ => mem_image_of_mem κ (mem_univ t)]
  refine sum_congr rfl fun ζ _ => ?_
  rw [← sum_const]
  exact sum_congr rfl fun t ht => by rw [(mem_filter.1 ht).2]

/-- **`κ` takes `o` values**: `|A| = Σ_{ζ ∈ κ(A)} |κ⁻¹(ζ)| = |κ(A)|·|A₀|` (`card_fibre`) and `|A| = o·|A₀|`
(`card_A_eq`). -/
theorem card_image_eq : (univ.image κ).card = orderOf κ := by
  have h0 : 0 < (A₀ κ).card := card_pos.2 ⟨1, mem_A₀.2 (map_one κ)⟩
  have h := card_eq_sum_card_image κ (univ : Finset A)
  rw [sum_congr rfl fun ζ hζ => card_fibre κ (by simpa using hζ), sum_const, smul_eq_mul, card_univ,
    card_A_eq] at h
  exact (Nat.eq_of_mul_eq_mul_right h0 h).symm

/-- **The values of a nontrivial power of `κ` sum to `0`**: for `0 < k < o`, `|A₀|·Σ_{ζ ∈ κ(A)} ζ^k = Σ_u κ(u)^k`
(`card_fibre`), which vanishes as `κ^k ≠ 1`. -/
theorem sum_image_pow {k : ℕ} (hk : 0 < k) (hko : k < orderOf κ) : ∑ ζ ∈ univ.image κ, (ζ : ℂ) ^ k = 0 := by
  have h := sum_apply_dual (κ ^ k)
  rw [ite_eq_right (pow_ne_one_of_lt_orderOf hk.ne' hko)] at h
  simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h
  rw [sum_comp_eq κ univ fun ζ : ℂˣ => (ζ : ℂ) ^ k,
    sum_congr rfl fun ζ hζ => by rw [card_fibre κ (by simpa using hζ)], ← smul_sum, nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 (card_pos.2 ⟨1, mem_A₀.2 (map_one κ)⟩).ne')

/-! ## The tops -/

/-- **Tops with exact coset counts**: when `4M ≤ |A₀|`, a set `TT` with `4M` elements in `A₀` and `3M` over each
other value of `κ`. Each count is at most the size `|A₀|` of its fibre (`card_fibre`), so the fibre has a subset of
that size (`Finset.exists_subset_card_eq`); `TT` is their union. -/
theorem exists_TT_counts (M : ℕ) (hM : 4 * M ≤ (A₀ κ).card) : ∃ TT : Finset A,
    ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0 := by
  classical
  have hle (ζ : ℂˣ) :
      (if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0) ≤ (univ.filter (κ · = ζ)).card := by
    split_ifs with h1 h2
    · subst h1
      rw [card_fibre κ (one_mem _)]
      exact hM
    · rw [card_fibre κ h2]
      omega
    · exact Nat.zero_le _
  choose F hF hcard using fun ζ => exists_subset_card_eq (hle ζ)
  refine ⟨univ.filter fun t => t ∈ F (κ t), fun ζ => ?_⟩
  rw [← hcard ζ, filter_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨ht, h⟩ => h ▸ ht, fun ht => ?_⟩
  obtain rfl : κ t = ζ := (mem_filter.1 (hF ζ ht)).2
  exact ⟨ht, rfl⟩

variable {κ} {M : ℕ} {TT : Finset A}

/-- **Sums over tops with exact counts**: `Σ_{t ∈ TT} F(κ(t)) = 3M·Σ_{ζ ∈ κ(A)} F(ζ) + M·F(1)`. -/
theorem sum_of_counts
    (hTT : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0)
    {β : Type*} [AddCommMonoid β] (F : ℂˣ → β) :
    ∑ t ∈ TT, F (κ t) = (3 * M) • ∑ ζ ∈ univ.image κ, F ζ + M • F 1 := by
  have h1 : (1 : ℂˣ) ∈ univ.image κ := mem_image.2 ⟨1, mem_univ _, map_one κ⟩
  rw [sum_comp_eq κ TT F]
  calc ∑ ζ ∈ univ.image κ, (TT.filter (κ · = ζ)).card • F ζ
      = ∑ ζ ∈ univ.image κ, ((3 * M) • F ζ + if ζ = 1 then M • F ζ else 0) := by
        refine sum_congr rfl fun ζ hζ => ?_
        rw [hTT, ite_eq_left (show ζ ∈ κ.range by simpa using hζ)]
        split_ifs
        · rw [← add_smul]
          ring_nf
        · rw [add_zero]
    _ = _ := by rw [sum_add_distrib, sum_ite_eq', ite_eq_left h1, smul_sum]

/-- **`|TT| = (3o + 1)M`**: `4M` tops over `1` and `3M` over each of the other `o − 1` values of `κ`
(`card_image_eq`). -/
theorem card_TT_of_counts
    (hTT : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0) :
    TT.card = (3 * orderOf κ + 1) * M := by
  have h := sum_of_counts hTT fun _ => (1 : ℕ)
  simp only [sum_const, smul_eq_mul, mul_one, card_image_eq] at h
  rw [h]
  ring

/-- **`Σ_{t ∈ TT} κ(t)^k = M`** for `0 < k < o`: the values of `κ^k` sum to `0` (`sum_image_pow`), and only the
extra `M` tops over `1` remain. -/
theorem sum_pow_of_counts
    (hTT : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0)
    {k : ℕ} (hk : 0 < k) (hko : k < orderOf κ) : ∑ t ∈ TT, (κ t : ℂ) ^ k = M := by
  rw [sum_of_counts hTT fun ζ : ℂˣ => (ζ : ℂ) ^ k, sum_image_pow κ hk hko, smul_zero, zero_add, Units.val_one,
    one_pow, nsmul_eq_mul, mul_one]

/-- **The shares** (`Weights.shares`) from exact counts: with scales `a₀ ≤ a_t ≤ a₀(1 + θ)` on `TT` and
`2θ ≤ x^{ε−1}`, `‖Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)‖ ≤ x^{ε−1} Σ_t a_t` for `0 < k < o`. The parts in `a₀` cancel
(`sum_pow_of_counts`, `card_TT_of_counts`); the rest, in `r_t = a_t − a₀ ∈ [0, θ a_t]`, has norm at most
`(1 + (3o + 1)⁻¹) Σ_t r_t ≤ 2θ Σ_t a_t`. -/
theorem shares_of_counts
    (hTT : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0)
    {a : A → ℝ} {a₀ θ x ε : ℝ} (ha₀ : 0 ≤ a₀) (hθ₀ : 0 ≤ θ) (ha : ∀ t ∈ TT, a₀ ≤ a t ∧ a t ≤ a₀ * (1 + θ))
    (hθ : 2 * θ ≤ x ^ (ε - 1)) :
    ∀ k, 0 < k → k < orderOf κ → ‖∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k -
      (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t : ℝ) : ℂ)‖ ≤ x ^ (ε - 1) * ∑ t ∈ TT, a t := by
  intro k hk hko
  have h3 : (3 * (orderOf κ : ℝ) + 1) ≠ 0 := by positivity
  have hc1 : (3 * (orderOf κ : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(orderOf κ).cast_nonneg (α := ℝ)])
  have hcard : (TT.card : ℝ) = (3 * orderOf κ + 1) * M := by exact_mod_cast card_TT_of_counts hTT
  have hr (t : A) (ht : t ∈ TT) : 0 ≤ a t - a₀ ∧ a t - a₀ ≤ θ * a t := by
    obtain ⟨h1, h2⟩ := ha t ht
    have := mul_le_mul_of_nonneg_right h1 hθ₀
    constructor <;> linarith
  have hR0 : 0 ≤ ∑ t ∈ TT, (a t - a₀) := sum_nonneg fun t ht => (hr t ht).1
  have hRle : ∑ t ∈ TT, (a t - a₀) ≤ θ * ∑ t ∈ TT, a t := by
    rw [mul_sum]
    exact sum_le_sum fun t ht => (hr t ht).2
  have hP : 0 ≤ ∑ t ∈ TT, a t := sum_nonneg fun t ht => ha₀.trans (ha t ht).1
  -- the parts in `a₀` cancel
  have hsplit : ∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k - (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t : ℝ) : ℂ) =
      ∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k -
        (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) : ℝ) : ℂ) := by
    have e1 : ∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k = ∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k - a₀ * M := by
      simp only [Complex.ofReal_sub, sub_mul, sum_sub_distrib, ← mul_sum, sum_pow_of_counts hTT hk hko]
    have e2 : (3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) =
        (3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t - a₀ * M := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
      field_simp
    rw [e1, e2]
    push_cast
    ring
  rw [hsplit]
  calc _ ≤ ‖∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k‖ +
        ‖(((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ∑ t ∈ TT, (a t - a₀) + (3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) := by
        refine add_le_add ((norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun t ht => ?_))) ?_
        · rw [norm_mul, norm_pow, norm_apply, one_pow, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (hr t ht).1]
        · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * (θ * ∑ t ∈ TT, a t) := by
        have := mul_le_mul_of_nonneg_right hc1 hR0
        linarith
    _ ≤ x ^ (ε - 1) * ∑ t ∈ TT, a t := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hθ hP

/-- **The coset counts of the archive** (the clause of A7), from exact counts: for every `γ`, the tops in the coset
`γA₀` (`γ⁻¹t ∈ A₀`) number exactly `λ(γ)|TT|`, with `λ(γ) = 4/(3o + 1)` for `γ ∈ A₀` and `3/(3o + 1)` otherwise, so
they are within `x^{ε−1}|TT|` of it. -/
theorem counts_archive [DecidableEq A]
    (hTT : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0)
    {x ε : ℝ} (hx : 0 ≤ x) (γ : A) :
    |((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) -
      (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * TT.card| ≤ x ^ (ε - 1) * TT.card := by
  have h3 : (3 * (orderOf κ : ℝ) + 1) ≠ 0 := by positivity
  have hfil : TT.filter (fun t => γ⁻¹ * t ∈ A₀ κ) = TT.filter (κ · = κ γ) := filter_congr fun t _ => by
    rw [mem_A₀, map_mul, map_inv, inv_mul_eq_one, eq_comm]
  have hcount : ((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) =
      (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * TT.card := by
    rw [hfil, hTT, card_TT_of_counts hTT]
    by_cases h : γ ∈ A₀ κ
    · rw [ite_eq_left (mem_A₀.1 h), ite_eq_left h]
      push_cast
      field_simp
    · rw [ite_eq_right (mt mem_A₀.2 h), ite_eq_left ⟨γ, rfl⟩, ite_eq_right h]
      push_cast
      field_simp
  rw [hcount, sub_self, abs_zero]
  exact mul_nonneg (Real.rpow_nonneg hx _) (Nat.cast_nonneg _)

/-- **The shares from approximate counts** (`Weights.shares` for random tops): if every coset `γA₀` holds
`λ(γ)|TT| + d_γ` tops with `|d_γ| ≤ η|TT|` (`λ = 4/(3o + 1)` on `A₀`, `3/(3o + 1)` off it), the scales satisfy
`a₀ ≤ a_t ≤ a₀(1 + θ)` on `TT` and `oη + 2θ ≤ x^{ε−1}`, then `‖Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)‖ ≤ x^{ε−1} Σ_t a_t`
for `0 < k < o`. Over the values `ζ` of `κ` (`sum_comp_eq`), `Σ_t κ(t)^k = Σ_ζ (λ_ζ|TT| + d_ζ)ζ^k` and
`Σ_ζ λ_ζ ζ^k = (3Σ_ζ ζ^k + 1)/(3o + 1) = 1/(3o + 1)` (`sum_image_pow`), so the part in `a₀` is at most
`a₀·o·η|TT| ≤ oη Σ_t a_t` (`card_image_eq`); the rest is at most `2θ Σ_t a_t`, as in `shares_of_counts`. -/
theorem shares_of_approx [DecidableEq A] {η : ℝ}
    (hTT : ∀ γ : A, |((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) -
      (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * TT.card| ≤ η * TT.card)
    {a : A → ℝ} {a₀ θ x ε : ℝ} (ha₀ : 0 ≤ a₀) (hθ₀ : 0 ≤ θ) (ha : ∀ t ∈ TT, a₀ ≤ a t ∧ a t ≤ a₀ * (1 + θ))
    (hθ : orderOf κ * η + 2 * θ ≤ x ^ (ε - 1)) :
    ∀ k, 0 < k → k < orderOf κ → ‖∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k -
      (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t : ℝ) : ℂ)‖ ≤ x ^ (ε - 1) * ∑ t ∈ TT, a t := by
  intro k hk hko
  rcases TT.eq_empty_or_nonempty with hT | hT
  · subst hT
    simp
  have hn₀ : (0 : ℝ) < TT.card := by exact_mod_cast hT.card_pos
  have hη : 0 ≤ η := le_of_mul_le_mul_right (by rw [zero_mul]; exact (abs_nonneg _).trans (hTT 1)) hn₀
  have hc1 : (3 * (orderOf κ : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [(orderOf κ).cast_nonneg (α := ℝ)])
  have hr (t : A) (ht : t ∈ TT) : 0 ≤ a t - a₀ ∧ a t - a₀ ≤ θ * a t := by
    obtain ⟨h1, h2⟩ := ha t ht
    have := mul_le_mul_of_nonneg_right h1 hθ₀
    constructor <;> linarith
  have hR0 : 0 ≤ ∑ t ∈ TT, (a t - a₀) := sum_nonneg fun t ht => (hr t ht).1
  have hRle : ∑ t ∈ TT, (a t - a₀) ≤ θ * ∑ t ∈ TT, a t := by
    rw [mul_sum]
    exact sum_le_sum fun t ht => (hr t ht).2
  have hP : 0 ≤ ∑ t ∈ TT, a t := sum_nonneg fun t ht => ha₀.trans (ha t ht).1
  have hA : a₀ * TT.card ≤ ∑ t ∈ TT, a t := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun t ht => (ha t ht).1
  -- the counts over the values of `κ`
  set d : ℂˣ → ℝ := fun ζ => ((TT.filter (κ · = ζ)).card : ℝ) -
    (if ζ = 1 then 4 else 3) / (3 * orderOf κ + 1) * TT.card with hd_def
  have hd : ∀ ζ ∈ univ.image κ, |d ζ| ≤ η * TT.card := by
    intro ζ hζ
    obtain ⟨γ, -, rfl⟩ := mem_image.1 hζ
    have hfil : TT.filter (fun t => γ⁻¹ * t ∈ A₀ κ) = TT.filter (κ · = κ γ) := filter_congr fun t _ => by
      rw [mem_A₀, map_mul, map_inv, inv_mul_eq_one, eq_comm]
    have := hTT γ
    rw [hfil] at this
    simpa only [hd_def, mem_A₀] using this
  have h1 : (1 : ℂˣ) ∈ univ.image κ := mem_image.2 ⟨1, mem_univ _, map_one κ⟩
  have hsum : ∑ t ∈ TT, (κ t : ℂ) ^ k =
      ∑ ζ ∈ univ.image κ, (d ζ : ℂ) * (ζ : ℂ) ^ k + ((TT.card / (3 * orderOf κ + 1) : ℝ) : ℂ) := by
    rw [sum_comp_eq κ TT fun ζ : ℂˣ => (ζ : ℂ) ^ k]
    have e : ∀ ζ : ℂˣ, (TT.filter (κ · = ζ)).card • (ζ : ℂ) ^ k = (d ζ : ℂ) * (ζ : ℂ) ^ k +
        ((TT.card / (3 * orderOf κ + 1) : ℝ) : ℂ) * (3 * (ζ : ℂ) ^ k + if ζ = 1 then 1 else 0) := by
      intro ζ
      rw [nsmul_eq_mul]
      simp only [hd_def]
      by_cases h : ζ = 1
      · rw [ite_eq_left h, ite_eq_left h, h, Units.val_one, one_pow]
        push_cast
        ring
      · rw [ite_eq_right h, ite_eq_right h]
        push_cast
        ring
    rw [sum_congr rfl fun ζ _ => e ζ, sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum,
      sum_image_pow κ hk hko, sum_ite_eq', ite_eq_left h1]
    ring
  have key : ∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k - (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t : ℝ) : ℂ) =
      (a₀ : ℂ) * ∑ ζ ∈ univ.image κ, (d ζ : ℂ) * (ζ : ℂ) ^ k +
        (∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k -
          (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) : ℝ) : ℂ)) := by
    have e1 : ∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k =
        (a₀ : ℂ) * ∑ t ∈ TT, (κ t : ℂ) ^ k + ∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun t _ => ?_
      push_cast
      ring
    have e3 : ∑ t ∈ TT, (a t - a₀) = ∑ t ∈ TT, a t - a₀ * TT.card := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
      ring
    rw [e1, hsum, e3]
    push_cast
    ring
  rw [key]
  have hD : ‖(a₀ : ℂ) * ∑ ζ ∈ univ.image κ, (d ζ : ℂ) * (ζ : ℂ) ^ k‖ ≤ orderOf κ * η * ∑ t ∈ TT, a t := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha₀]
    have h2 : ‖∑ ζ ∈ univ.image κ, (d ζ : ℂ) * (ζ : ℂ) ^ k‖ ≤ orderOf κ * (η * TT.card) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ ζ ∈ univ.image κ, ‖(d ζ : ℂ) * (ζ : ℂ) ^ k‖ ≤ ∑ _ζ ∈ univ.image κ, η * TT.card := by
            refine sum_le_sum fun ζ hζ => ?_
            obtain ⟨γ, -, rfl⟩ := mem_image.1 hζ
            rw [norm_mul, norm_pow, norm_apply, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hd _ hζ
        _ = orderOf κ * (η * TT.card) := by rw [sum_const, card_image_eq, nsmul_eq_mul]
    calc a₀ * ‖∑ ζ ∈ univ.image κ, (d ζ : ℂ) * (ζ : ℂ) ^ k‖ ≤ a₀ * (orderOf κ * (η * TT.card)) :=
          mul_le_mul_of_nonneg_left h2 ha₀
      _ = orderOf κ * η * (a₀ * TT.card) := by ring
      _ ≤ orderOf κ * η * ∑ t ∈ TT, a t := mul_le_mul_of_nonneg_left hA (by positivity)
  have hE : ‖∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k -
      (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) : ℝ) : ℂ)‖ ≤ 2 * θ * ∑ t ∈ TT, a t := by
    calc _ ≤ ‖∑ t ∈ TT, ((a t - a₀ : ℝ) : ℂ) * (κ t : ℂ) ^ k‖ +
          ‖(((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ ∑ t ∈ TT, (a t - a₀) + (3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (a t - a₀) := by
          refine add_le_add ((norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun t ht => ?_))) ?_
          · rw [norm_mul, norm_pow, norm_apply, one_pow, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (hr t ht).1]
          · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ 2 * θ * ∑ t ∈ TT, a t := by
          have := mul_le_mul_of_nonneg_right hc1 hR0
          linarith
  calc _ ≤ orderOf κ * η * ∑ t ∈ TT, a t + 2 * θ * ∑ t ∈ TT, a t := (norm_add_le _ _).trans (add_le_add hD hE)
    _ = (orderOf κ * η + 2 * θ) * ∑ t ∈ TT, a t := by ring
    _ ≤ x ^ (ε - 1) * ∑ t ∈ TT, a t := mul_le_mul_of_nonneg_right hθ hP

end ZetaBalance

#print axioms ZetaBalance.shares_of_approx
#print axioms ZetaBalance.exists_TT_counts
#print axioms ZetaBalance.card_TT_of_counts
#print axioms ZetaBalance.shares_of_counts
#print axioms ZetaBalance.counts_archive
