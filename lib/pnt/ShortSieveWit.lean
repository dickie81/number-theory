import ShortSieveTypeII

/-!
# Type II witnesses from a pointwise test

The certificate checks, on each box of exponents, that some Hölder exponents `δ` with `Σ 1/δ_g = 1` are admissible
for the groups' exponents `a_g` at every point (`MomentOK` at `D_g = (1 − θ + κ)/(a_g − κ)`). The Type II estimate
(`ShortSieveGroup`) takes finitely many fixed witnesses, each with lower bounds for the groups' exponents. Compactness
joins the two:

* `momentOK_of_le_add`: **admissibility is open in `D`.** If `δ` is admissible for `D`, it is admissible for every
  `D′ ≤ D + ε`, for some `ε > 0` (`δ > δ_req(D)` with `δ_req` continuous and nondecreasing, proved by cases on the
  two kinds of moment);
* `exists_wit_list`: **witnesses by compactness.** If at every point `α` of a compact set some `δ` with
  `Σ 1/δ_g = 1` is admissible for every `D_g(α)`, with continuous `a_g > κ`, then finitely many fixed pairs
  `(a′, δ)`, all admissible, and a margin `μ > 0` cover the set: at every point one of them has `a′_g + μ ≤ a_g(α)`;
* `dreq`, `momentOK_of_dreq_lt`, `dreq_mono`: **Harman's exponent** `δ_req(D)` (`2` up to `1`, then `4D − 2m` on
  `(m, m + 1/2]` and `2m + 2` on `(m + 1/2, m + 1]`), nondecreasing, with every `δ > δ_req(D)` admissible;
* `test_of_sum_inv_dreq`: **the test from Harman's exponents.** `Σ_g 1/δ_req(D_g) > 1` gives admissible `δ_g` with
  `Σ 1/δ_g = 1`, so the certificate need only bound `Σ_g 1/δ_req(D_g)` from below on a box, which `dreq_mono` reduces
  to the groups' least exponents there.
-/

open Finset

namespace ShortSieveWit

open ShortSieveTypeII

/-- **Admissibility is open in `D`.** If `MomentOK D δ`, then for some `ε > 0`, `MomentOK D′ δ` for all `D′ ≤ D + ε`. -/
theorem momentOK_of_le_add {D δ : ℝ} (h : MomentOK D δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ D' : ℝ, D' ≤ D + ε → MomentOK D' δ := by
  rcases h with ⟨m, hm, hmD, hDm, hδ⟩ | ⟨k, hk, hDk, hδ⟩
  · -- `m < D ≤ m + 1/2`, `4D − 2m < δ`
    refine ⟨min ((δ - (4 * D - 2 * m)) / 8) (1 / 2), lt_min (by linarith) (by norm_num), fun D' hD' => ?_⟩
    have hε1 : min ((δ - (4 * D - 2 * m)) / 8) (1 / 2) ≤ (δ - (4 * D - 2 * m)) / 8 := min_le_left _ _
    have hε2 : min ((δ - (4 * D - 2 * m)) / 8) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    by_cases h1 : D' ≤ m
    · exact Or.inr ⟨m, hm, h1, by linarith⟩
    by_cases h2 : D' ≤ m + 1 / 2
    · exact Or.inl ⟨m, hm, not_le.1 h1, h2, by linarith⟩
    · refine Or.inr ⟨m + 1, by omega, ?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith [not_le.1 h2]
  · -- `D ≤ k`, `2k < δ`
    refine ⟨min ((δ - 2 * k) / 8) (1 / 2), lt_min (by linarith) (by norm_num), fun D' hD' => ?_⟩
    have hε1 : min ((δ - 2 * k) / 8) (1 / 2) ≤ (δ - 2 * k) / 8 := min_le_left _ _
    have hε2 : min ((δ - 2 * k) / 8) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    by_cases h1 : D' ≤ k
    · exact Or.inr ⟨k, hk, h1, hδ⟩
    · exact Or.inl ⟨k, hk, not_le.1 h1, by linarith, by linarith⟩

/-- `D(a) = c/(a − κ)` stays below `D(a₀) + ε` for `a ≥ a₀ − τ`, `τ = (a₀ − κ)ε/(D(a₀) + ε)`. -/
theorem div_sub_le_add {c κ a₀ ε a : ℝ} (hc : 0 < c) (ha₀ : κ < a₀) (hε : 0 < ε)
    (ha : a₀ - (a₀ - κ) * ε / (c / (a₀ - κ) + ε) ≤ a) :
    κ < a ∧ c / (a - κ) ≤ c / (a₀ - κ) + ε := by
  have hu : 0 < a₀ - κ := by linarith
  set D₀ := c / (a₀ - κ) with hD₀
  have hD₀p : 0 < D₀ := div_pos hc hu
  have hfrac : (a₀ - κ) * ε / (D₀ + ε) < a₀ - κ := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have haκ : κ < a := by linarith
  refine ⟨haκ, ?_⟩
  -- `a − κ ≥ (a₀ − κ) D₀/(D₀ + ε) = c/(D₀ + ε)`
  have h1 : c / (D₀ + ε) ≤ a - κ := by
    have e : c / (D₀ + ε) = a₀ - κ - (a₀ - κ) * ε / (D₀ + ε) := by
      rw [hD₀]; field_simp; ring
    rw [e]; linarith
  rw [div_le_iff₀ (by linarith)]
  rw [div_le_iff₀ (by positivity)] at h1
  nlinarith

/-- **Witnesses by compactness.** Let `K` be compact, `a_g` continuous with `a_g > κ` on `K`, `θ < 1`, `κ > 0`, and
suppose that at every point of `K` some `δ` with `δ_g > 0` and `Σ 1/δ_g = 1` is admissible for every
`D_g = (1 − θ + κ)/(a_g − κ)`. Then there are finitely many pairs `(a′, δ)`, each with `a′_g > κ`, `δ_g > 0`,
`Σ 1/δ_g = 1` and `δ_g` admissible for `(1 − θ + κ)/(a′_g − κ)`, and a margin `μ > 0`, such that at every point of
`K` one of them has `a′_g + μ ≤ a_g` for every `g`. -/
theorem exists_wit_list {E : Type*} [TopologicalSpace E] {m : ℕ} {K : Set E} (hK : IsCompact K)
    (a : Fin m → E → ℝ) (ha : ∀ i, Continuous (a i)) {θ κ : ℝ} (hθ : θ < 1) (hκ : 0 < κ)
    (hpos : ∀ α ∈ K, ∀ i, κ < a i α)
    (htest : ∀ α ∈ K, ∃ δ : Fin m → ℝ, (∀ i, 0 < δ i) ∧ ∑ i, 1 / δ i = 1 ∧
      ∀ i, MomentOK ((1 - θ + κ) / (a i α - κ)) (δ i)) :
    ∃ L : List ((Fin m → ℝ) × (Fin m → ℝ)), ∃ μ : ℝ, 0 < μ ∧
      (∀ w ∈ L, (∀ i, κ < w.1 i) ∧ (∀ i, 0 < w.2 i) ∧ ∑ i, 1 / w.2 i = 1 ∧
        ∀ i, MomentOK ((1 - θ + κ) / (w.1 i - κ)) (w.2 i)) ∧
      ∀ α ∈ K, ∃ w ∈ L, ∀ i, w.1 i + μ ≤ a i α := by
  classical
  set c : ℝ := 1 - θ + κ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  choose! δf hδf using htest
  -- the openness of each admissibility
  have hε : ∀ α ∈ K, ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ D' : ℝ, D' ≤ c / (a i α - κ) + ε → MomentOK D' (δf α i) :=
    fun α hα i => momentOK_of_le_add ((hδf α hα).2.2 i)
  choose! εf hεf using hε
  -- the step `τ(α) = min_g (a_g − κ)ε_g/(D_g + ε_g)`, positive
  set τg : E → Fin m → ℝ := fun α i => (a i α - κ) * εf α i / (c / (a i α - κ) + εf α i) with hτg
  have hτg0 : ∀ α ∈ K, ∀ i, 0 < τg α i := fun α hα i => by
    have h1 := hpos α hα i
    have h2 := (hεf α hα i).1
    have h3 : 0 < c / (a i α - κ) := div_pos hc0 (by linarith)
    simp only [hτg]
    exact div_pos (mul_pos (by linarith) h2) (by linarith)
  set τ : E → ℝ := fun α => if h : (univ : Finset (Fin m)).Nonempty then univ.inf' h (τg α) else 1 with hτ
  have hτ0 : ∀ α ∈ K, 0 < τ α := fun α hα => by
    simp only [hτ]
    split_ifs with h
    · exact (lt_inf'_iff h).2 fun i _ => hτg0 α hα i
    · exact one_pos
  have hτle : ∀ α, ∀ i, τ α ≤ τg α i := fun α i => by
    simp only [hτ]
    rw [dite_eq_left ⟨i, mem_univ i⟩]
    exact inf'_le _ (mem_univ i)
  -- the witness at `α` and its neighbourhood
  set wf : E → (Fin m → ℝ) × (Fin m → ℝ) := fun α => (fun i => a i α - τ α, δf α) with hwf
  have hwOK : ∀ α ∈ K, (∀ i, κ < (wf α).1 i) ∧ (∀ i, 0 < (wf α).2 i) ∧ ∑ i, 1 / (wf α).2 i = 1 ∧
      ∀ i, MomentOK (c / ((wf α).1 i - κ)) ((wf α).2 i) := by
    intro α hα
    have key : ∀ i, κ < a i α - τ α ∧ c / (a i α - τ α - κ) ≤ c / (a i α - κ) + εf α i := fun i =>
      div_sub_le_add hc0 (hpos α hα i) (hεf α hα i).1 (by linarith [hτle α i])
    refine ⟨fun i => (key i).1, (hδf α hα).1, (hδf α hα).2.1, fun i => (hεf α hα i).2 _ (key i).2⟩
  set U : K → Set E := fun α => ⋂ i, a i ⁻¹' Set.Ioi (a i α - τ α / 2) with hU
  have hUo : ∀ α, IsOpen (U α) := fun α => isOpen_iInter_of_finite fun i => (ha i).isOpen_preimage _ isOpen_Ioi
  have hcover : K ⊆ ⋃ α, U α := fun α hα => by
    refine Set.mem_iUnion.2 ⟨⟨α, hα⟩, Set.mem_iInter.2 fun i => ?_⟩
    show a i α > a i α - τ α / 2
    linarith [hτ0 α hα]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcover
  -- the margin: the least half step over the finite subcover
  by_cases hne : t.Nonempty
  · set μ : ℝ := t.inf' hne fun α => τ α / 2 with hμ
    have hμ0 : 0 < μ := (lt_inf'_iff hne).2 fun α _ => by linarith [hτ0 α α.2]
    refine ⟨t.toList.map fun α : K => wf (α : E), μ, hμ0, fun w hw => ?_, fun α hα => ?_⟩
    · obtain ⟨α, -, rfl⟩ := List.mem_map.1 hw
      exact hwOK α α.2
    · obtain ⟨β, hβt, hαβ⟩ := Set.mem_iUnion₂.1 (ht hα)
      refine ⟨wf β, List.mem_map.2 ⟨β, mem_toList.2 hβt, rfl⟩, fun i => ?_⟩
      have h1 : a i α > a i β - τ β / 2 := Set.mem_iInter.1 hαβ i
      have h2 : μ ≤ τ β / 2 := inf'_le _ hβt
      show a i β - τ β + μ ≤ a i α
      linarith
  · -- an empty subcover: `K` is empty
    rw [not_nonempty_iff_eq_empty] at hne
    refine ⟨[], 1, one_pos, fun w hw => absurd hw List.not_mem_nil, fun α hα => ?_⟩
    have := ht hα
    simp [hne] at this

/-! ### Harman's exponent and the test from it -/

/-- **Harman's exponent** `δ_req(D)`: `2` for `D ≤ 1`, and for `m < D ≤ m + 1`, `m = ⌈D⌉ − 1 ≥ 1`: `4D − 2m` up to
`m + 1/2`, then `2m + 2`. -/
noncomputable def dreq (D : ℝ) : ℝ :=
  if D ≤ 1 then 2 else if D ≤ (⌈D⌉₊ - 1 : ℕ) + 1 / 2 then 4 * D - 2 * ((⌈D⌉₊ - 1 : ℕ) : ℝ)
    else 2 * ((⌈D⌉₊ - 1 : ℕ) : ℝ) + 2

/-- For `D > 1`, `m = ⌈D⌉ − 1` has `1 ≤ m`, `m < D ≤ m + 1`. -/
theorem ceil_sub_one_spec {D : ℝ} (hD : 1 < D) :
    1 ≤ ⌈D⌉₊ - 1 ∧ ((⌈D⌉₊ - 1 : ℕ) : ℝ) < D ∧ D ≤ ((⌈D⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have h1 : 2 ≤ ⌈D⌉₊ := by
    have : (1 : ℝ) < ⌈D⌉₊ := lt_of_lt_of_le hD (Nat.le_ceil D)
    exact_mod_cast this
  have hc : ((⌈D⌉₊ - 1 : ℕ) : ℝ) = (⌈D⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hc]
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ D by linarith)
    linarith
  · rw [hc]
    linarith [Nat.le_ceil D]

/-- `δ_req(D) ≥ 2`. -/
theorem two_le_dreq (D : ℝ) : 2 ≤ dreq D := by
  unfold dreq
  split_ifs with h1 h2
  · exact le_rfl
  · obtain ⟨-, hm, -⟩ := ceil_sub_one_spec (not_le.1 h1)
    have : (1 : ℝ) ≤ ((⌈D⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast (ceil_sub_one_spec (not_le.1 h1)).1
    linarith
  · have : (1 : ℝ) ≤ ((⌈D⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast (ceil_sub_one_spec (not_le.1 h1)).1
    linarith

/-- **Every moment above Harman's exponent is admissible.** -/
theorem momentOK_of_dreq_lt {D δ : ℝ} (h : dreq D < δ) : MomentOK D δ := by
  unfold dreq at h
  split_ifs at h with h1 h2
  · exact Or.inr ⟨1, le_rfl, by exact_mod_cast h1, by norm_num; linarith⟩
  · obtain ⟨hm1, hmD, -⟩ := ceil_sub_one_spec (not_le.1 h1)
    exact Or.inl ⟨⌈D⌉₊ - 1, hm1, hmD, h2, h⟩
  · obtain ⟨hm1, -, hDm⟩ := ceil_sub_one_spec (not_le.1 h1)
    refine Or.inr ⟨⌈D⌉₊ - 1 + 1, by omega, by push_cast; linarith, by push_cast; linarith⟩

/-- `δ_req` on `(m, m + 1]` by its two pieces, for any `m ≥ 1` with `m < D ≤ m + 1`. -/
theorem dreq_eq_of {D : ℝ} {m : ℕ} (hm : 1 ≤ m) (hmD : (m : ℝ) < D) (hDm : D ≤ m + 1) :
    dreq D = if D ≤ m + 1 / 2 then 4 * D - 2 * m else 2 * m + 2 := by
  have h1 : ¬ D ≤ 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  -- `m = ⌈D⌉ − 1`
  have hceil : ⌈D⌉₊ = m + 1 := by
    refine le_antisymm (Nat.ceil_le.2 (by push_cast; linarith)) ?_
    exact Nat.succ_le_of_lt (Nat.lt_ceil.2 hmD)
  unfold dreq
  rw [ite_eq_right h1, hceil, Nat.add_sub_cancel]

/-- **Harman's exponent is nondecreasing.** -/
theorem dreq_mono {D D' : ℝ} (h : D ≤ D') : dreq D ≤ dreq D' := by
  by_cases hD' : D' ≤ 1
  · have hD : D ≤ 1 := h.trans hD'
    unfold dreq; rw [ite_eq_left hD, ite_eq_left hD']
  by_cases hD : D ≤ 1
  · unfold dreq
    rw [ite_eq_left hD]
    exact two_le_dreq D'
  obtain ⟨hm1, hmD, hDm⟩ := ceil_sub_one_spec (not_le.1 hD)
  obtain ⟨hm1', hmD', hDm'⟩ := ceil_sub_one_spec (not_le.1 hD')
  set m := ⌈D⌉₊ - 1 with hm
  set m' := ⌈D'⌉₊ - 1 with hm'
  rw [dreq_eq_of hm1 hmD hDm, dreq_eq_of hm1' hmD' hDm']
  -- `m ≤ m'`, and the pieces in order
  have hmm : m ≤ m' := by
    have : (m : ℝ) < m' + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  rcases eq_or_lt_of_le hmm with heq | hlt
  · rw [← heq]
    split_ifs <;> linarith
  · have hlt' : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hlt
    split_ifs <;> linarith

/-- **The test from Harman's exponents.** If `Σ_g 1/δ_req(D_g) > 1`, then `δ_g = s·δ_req(D_g)`, `s = Σ_g 1/δ_req(D_g)`,
are admissible with `Σ 1/δ_g = 1`. -/
theorem test_of_sum_inv_dreq {G : ℕ} {D : Fin G → ℝ} (h : 1 < ∑ g, 1 / dreq (D g)) :
    ∃ δ : Fin G → ℝ, (∀ g, 0 < δ g) ∧ ∑ g, 1 / δ g = 1 ∧ ∀ g, MomentOK (D g) (δ g) := by
  set s := ∑ g, 1 / dreq (D g) with hs
  have hs0 : 0 < s := by linarith
  have hd : ∀ g, 0 < dreq (D g) := fun g => lt_of_lt_of_le two_pos (two_le_dreq _)
  refine ⟨fun g => s * dreq (D g), fun g => mul_pos hs0 (hd g), ?_, fun g => momentOK_of_dreq_lt ?_⟩
  · have e : ∀ g, 1 / (s * dreq (D g)) = 1 / s * (1 / dreq (D g)) := fun g => by
      rw [one_div_mul_one_div]
    simp only [e]
    rw [← mul_sum, ← hs, one_div_mul_cancel hs0.ne']
  · have := hd g
    nlinarith

end ShortSieveWit

#print axioms ShortSieveWit.momentOK_of_le_add
#print axioms ShortSieveWit.exists_wit_list
#print axioms ShortSieveWit.momentOK_of_dreq_lt
#print axioms ShortSieveWit.dreq_mono
#print axioms ShortSieveWit.test_of_sum_inv_dreq
