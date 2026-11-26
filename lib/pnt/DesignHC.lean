import CMHost
import ZetaGap

/-!
# The Harish-Chandra families of the design

A step of the proof of the sharp frontier (`SharpInputs`, the field `SharpPieces.params`): the Harish-Chandra
families `hc u` of a design at `x` (`SharpDesign`, whose weights are `w_{u,j} = e_j`), one per translate `u`, given
by the formulas of the archive's design, with their windows, and the root-of-unity condition that the pins ask of
them.

**Places** (`placeKind`). At the translate `u`, a place `ρ = (s, t) ∈ Φ` is a *top* if `s = 1` and `t ∈ TT`, *thick*
if `ρ ∈ Θ(u) = {(−1, s·u) : s ∈ T2}` (`Setting.thickSet`), and *thin* otherwise. Thick places have sign `−1`, so none
is a top, and `ρ` is thick exactly when it lies in `Θ(u)` (`placeKind_eq_thick`): the split that `Weights` sees.

**The families** (`hcFam`). From integers `Δ`, `H`, `B`, `W`, `P`, scales `a_t` and shifts `b_t` at the tops, and per
translate a place `ρ*(u)` and a shift `σ(u) ≥ 0`, the parameter at `ρ` is:
* `v_i = 4Δ(k − 2 − i)`, and `u_i = 4Δ(k − 1 − i) − ½` for `0 < i < k − 1`, at every place;
* `u_0 = a_t + (k − 1)/2` and `u_{k−1} = −b_t − (k − 1)/2` at the top `(1, t)` (`hcFam_u_top`), and
  `u_0 = 4Δ(2k − 2) + ½`, `u_{k−1} = −½` elsewhere (`hcFam_u_ntop`);
* `b_j = β(ρ) + 2jH` and `e_j = b_j + H` (`hcFam_b`, `hcFam_e`), where the base `β(ρ)` (`hcBase`) is `b_t + P` at the
  top `(1, t)`, `B` at a thick place (`B + σ(u)` at `ρ*(u)`), and `W` at a thin place.

They are Harish-Chandra parameters (`Setting.Ranks.HC`) under the inequalities `HCHyp`: `Δ ≥ 1`, `2H ≥ t + 3`,
`B, W ≥ 1`, `2P ≥ k`, and `a_t ≥ 4Δk`, `b_t ≥ 0` at every top. The interlacing
`u_0 > v_0 > u_1 > ⋯ > v_{k−2} = 0 > u_{k−1} > −b_0` is checked once for given ends (`Setting.Ranks.hcOf`, from
`Setting.Ranks.HCOk`): in the middle `u_{i+1} = v_i − ½` and `u_i − v_i = 4Δ − ½`, so only the two ends and `b_0`
depend on the place, a case split on `placeKind` (`hcOk_fam`). The ends are half-integers as `k` is even, and the gaps
are `e_j − b_j = b_{j+1} − e_j = H`.

**The windows** (`hcFam_windows`), for reals `b, w, p` with `B = ⌈b⌉`, `W = ⌈w⌉`, `P = ⌊p⌋`, shifts `σ ≤ H`, and
`η = 2mH`: `b_t + p ≤ e_j ≤ b_t + p + η` at the top `(1, t)`, `b ≤ e_j ≤ b + η + 1` at a thick place,
`w ≤ e_j ≤ w + η + 1` at a thin place, and `|b_i − e_j| ≤ η` everywhere. Every `e_j` is positive (`hcFam_e_pos`).

**The root-of-unity condition** (`exists_shift_RU`). When every `ρ*(u)` is thick and `w_E = torsionOrder E` divides
`H`, shifts `σ(u) < w_E` make `∏_ρ τ_ρ(ζ)^{e_j(ρ)} = 1` for every `j` and every root of unity `ζ ∈ E`. Every root of
unity of `E` is a `w_E`-th one (`pow_torsionOrder_eq_one_of_pow_eq_one`: it is a unit of `𝓞 E` of finite order), hence
a power `ζ_0^i` of a primitive one (`exists_isPrimitiveRoot_torsionOrder`, a generator of the torsion of `(𝓞 E)ˣ`). As
`w_E ∣ H`, `τ_ρ(ζ)^{e_j(ρ)} = τ_ρ(ζ)^{β(ρ)}` (`pow_zpow_add_mul`), and `β` depends on `σ` only at `ρ*(u)`
(`hcBase_eq_add`). So the product is `(c_u·ξ_u^{σ(u)})^i`, with `c_u` the product at `σ = 0` and
`ξ_u = τ_{ρ*(u)}(ζ_0)`. Now `c_u^{w_E} = 1` and `ξ_u` is a primitive `w_E`-th root of unity in `ℂ`, as `τ_{ρ*(u)}` is
injective, so `c_u⁻¹ = ξ_u^{σ(u)}` for one `σ(u) < w_E`.

**The number of roots of unity** (`torsionOrder_le`): `w_E ≤ 32|A|²`. A primitive `w_E`-th root of unity has degree
`φ(w_E)` over `ℚ`, its minimal polynomial being the cyclotomic one, so `φ(w_E) ≤ [E:ℚ] = 4|A|`. And `n ≤ 2φ(n)²` for
every `n` (`le_two_mul_totient_sq`), by multiplicativity: `p^e ≤ φ(p^e)²` for odd `p`, and `2^e ≤ 2φ(2^e)²`.

**Choices.**
* The inequalities are the weakest that the interlacing needs: `2P ≥ k`, `a_t ≥ 4Δk`, `B ≥ 1` and `b_t ≥ 0`. The
  margin `P > (k − 1)/2 + 3` that the gain asks, and every size, are the builder's.
* The constructor is generic in its integers, in `ρ*` and in `σ`; the design's values (`Δ = ⌈x^{c_D}⌉`,
  `H = w_E⌈x^{402}⌉`, `B = ⌈b⌉`, `W = ⌈w″⌉`, `P = ⌊b′/x⌋`, `ρ*(u) = (−1, a_0^{s*}u)`) are its builder's. The windows
  take reals with their ceilings and floor, so this file does not depend on the scale.
* The shift is added at `ρ*(u)` only when that place is thick; `exists_shift_RU` asks that it is.
* `w_E ≤ 32|A|²` is stated in `ℕ`.
-/

open NumberField

namespace ZetaBalance

/-! ## Places -/

/-- The kind of a place at a translate: a top, a thick place or a thin place (`placeKind`). -/
inductive PlaceKind
  /-- `ρ = (1, t)` with `t ∈ TT`. -/
  | top
  /-- `ρ ∈ Θ(u)`. -/
  | thick
  /-- Neither. -/
  | thin
  deriving DecidableEq

variable {S : Setting}

/-- The kind of the place `ρ` at the translate `u`: a top if `ρ = (1, t)` with `t ∈ TT`, thick if `ρ ∈ Θ(u)`, and thin
otherwise. -/
noncomputable def placeKind (TT T2 : Finset S.A) (u : S.A) (ρ : Φ S.A) : PlaceKind :=
  if ρ.1 = 1 ∧ ρ.2 ∈ TT then .top else if ρ ∈ S.thickSet T2 u then .thick else .thin

/-- A place is a top exactly when it is `(1, t)` with `t ∈ TT`. -/
theorem placeKind_eq_top {TT T2 : Finset S.A} {u : S.A} {ρ : Φ S.A} :
    placeKind TT T2 u ρ = .top ↔ ρ.1 = 1 ∧ ρ.2 ∈ TT := by
  unfold placeKind
  split_ifs with h1 h2 <;> simp [h1]

/-- A place is thick exactly when it lies in `Θ(u)`: the places of `Θ(u)` have sign `−1`, so none is a top. -/
theorem placeKind_eq_thick {TT T2 : Finset S.A} {u : S.A} {ρ : Φ S.A} :
    placeKind TT T2 u ρ = .thick ↔ ρ ∈ S.thickSet T2 u := by
  unfold placeKind
  split_ifs with h1 h2
  · simp only [false_iff]
    intro h
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 h
    exact absurd h1.1 (by decide : (-1 : ℤˣ) ≠ 1)
  · simp [h2]
  · simp [h2]

/-! ## One parameter, for given ends -/

namespace Setting.Ranks

variable (R : S.Ranks)

/-- What the parameter `Setting.Ranks.hcOf` with ends `u_0`, `u_{k−1}` and base `β` needs: `Δ ≥ 1`, `2H ≥ t + 3`,
half-integral ends, `u_0 > v_0`, `u_{k−1} < v_{k−2} = 0` and `−β < u_{k−1}`. -/
structure HCOk (Δ H : ℕ) (β : ℤ) (u0 uk : ℚ) : Prop where
  /-- `Δ ≥ 1`. -/
  Δ_pos : 1 ≤ Δ
  /-- `2H ≥ t + 3`. -/
  H_ge : R.t + 3 ≤ 2 * H
  /-- `u_0` is a half-integer. -/
  u0_half : ∃ n : ℤ, u0 = n + 1 / 2
  /-- `u_{k−1}` is a half-integer. -/
  uk_half : ∃ n : ℤ, uk = n + 1 / 2
  /-- `v_0 < u_0`. -/
  v0_lt : 4 * Δ * ((R.k : ℚ) - 2) < u0
  /-- `u_{k−1} < v_{k−2} = 0`. -/
  uk_neg : uk < 0
  /-- `−b_0 < u_{k−1}`. -/
  neg_lt : -(β : ℚ) < uk

/-- **The parameter with given ends**: `u_0`, `u_{k−1}` given and `u_i = 4Δ(k − 1 − i) − ½` in between,
`v_i = 4Δ(k − 2 − i)`, `b_j = β + 2jH` and `e_j = b_j + H`. -/
def hcOf (Δ H : ℕ) (β : ℤ) (u0 uk : ℚ) (h : R.HCOk Δ H β u0 uk) : R.HC where
  u i := if (i : ℕ) = 0 then u0 else if (i : ℕ) = R.k - 1 then uk else 4 * Δ * ((R.k : ℚ) - 1 - i) - 1 / 2
  v i := 4 * Δ * ((R.k : ℤ) - 2 - i)
  b j := β + j * (2 * H)
  e j := β + j * (2 * H) + H
  u_half i := by
    split_ifs
    · exact h.u0_half
    · exact h.uk_half
    · exact ⟨4 * Δ * ((R.k : ℤ) - 1 - i) - 1, by push_cast; ring⟩
  v_lt i := by
    have := R.m_add_three_le
    have := R.two_le_m
    have hΔ : (1 : ℚ) ≤ Δ := by exact_mod_cast h.Δ_pos
    simp only [Fin.val_castLE]
    split_ifs with h0 h1
    · push_cast
      rw [h0]
      simpa using h.v0_lt
    · omega
    · push_cast
      linarith
  lt_v i := by
    have := R.m_add_three_le
    have := R.two_le_m
    have hΔ : (1 : ℚ) ≤ Δ := by exact_mod_cast h.Δ_pos
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    split_ifs with h1
    · have h2 : (i : ℕ) + 2 = R.k := by omega
      have hi : ((i : ℕ) : ℚ) = R.k - 2 := by
        rw [eq_sub_iff_add_eq]
        exact_mod_cast h2
      push_cast
      rw [hi]
      simpa using h.uk_neg
    · push_cast
      linarith
  neg_b_lt := by
    have := R.m_add_three_le
    have := R.two_le_m
    simp only [show R.k - 1 ≠ 0 by omega, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero]
    exact h.neg_lt
  e_sub_b j := by
    have := h.H_ge
    rw [add_sub_cancel_left]
    omega
  b_sub_e j hj := by
    have := h.H_ge
    push_cast
    ring_nf
    omega

end Setting.Ranks

/-! ## The families -/

/-- **The inequalities** that make the design's formulas Harish-Chandra parameters: `Δ ≥ 1`, `H ≥ (t + 3)/2`,
`B, W ≥ 1`, `P > (k − 1)/2`, and at every top `a_t ≥ 4Δk` and `b_t ≥ 0`. -/
structure HCHyp (R : S.Ranks) (TT : Finset S.A) (a bT : S.A → ℤ) (Δ H : ℕ) (B W P : ℤ) : Prop where
  /-- `Δ ≥ 1`. -/
  Δ_pos : 1 ≤ Δ
  /-- `H ≥ (t + 3)/2`. -/
  H_ge : R.t + 3 ≤ 2 * H
  /-- `B ≥ 1`. -/
  B_pos : 1 ≤ B
  /-- `W ≥ 1`. -/
  W_pos : 1 ≤ W
  /-- `P > (k − 1)/2`. -/
  P_gt : (R.k : ℤ) ≤ 2 * P
  /-- `a_t ≥ 4Δk` at every top. -/
  a_ge : ∀ t ∈ TT, 4 * (Δ : ℤ) * R.k ≤ a t
  /-- `b_t ≥ 0` at every top. -/
  bT_nonneg : ∀ t ∈ TT, 0 ≤ bT t

/-- The base `β(ρ)` of `b` and `e` at `ρ`: `b_t + P` at the top `(1, t)`, `B` at a thick place (`B + σ(u)` at
`ρ*(u)`), and `W` at a thin place. -/
noncomputable def hcBase (TT T2 : Finset S.A) (bT : S.A → ℤ) (B W P : ℤ) (ρstar : S.A → Φ S.A) (σ : S.A → ℕ)
    (u : S.A) (ρ : Φ S.A) : ℤ :=
  match placeKind TT T2 u ρ with
  | .top => bT ρ.2 + P
  | .thick => B + if ρ = ρstar u then (σ u : ℤ) else 0
  | .thin => W

/-- `u_0` at `ρ`: `a_t + (k − 1)/2` at the top `(1, t)` and `4Δ(2k − 2) + ½` elsewhere. -/
noncomputable def hcU0 (R : S.Ranks) (TT T2 : Finset S.A) (a : S.A → ℤ) (Δ : ℕ) (u : S.A) (ρ : Φ S.A) : ℚ :=
  if placeKind TT T2 u ρ = .top then a ρ.2 + ((R.k : ℚ) - 1) / 2 else 4 * Δ * (2 * (R.k : ℚ) - 2) + 1 / 2

/-- `u_{k−1}` at `ρ`: `−b_t − (k − 1)/2` at the top `(1, t)` and `−½` elsewhere. -/
noncomputable def hcUk (R : S.Ranks) (TT T2 : Finset S.A) (bT : S.A → ℤ) (u : S.A) (ρ : Φ S.A) : ℚ :=
  if placeKind TT T2 u ρ = .top then -bT ρ.2 - ((R.k : ℚ) - 1) / 2 else -1 / 2

variable {R : S.Ranks} {TT T2 : Finset S.A} {a bT : S.A → ℤ} {Δ H : ℕ} {B W P : ℤ} {ρstar : S.A → Φ S.A}
  {σ : S.A → ℕ}

/-- The base at the top `(1, t)` is `b_t + P`. -/
theorem hcBase_top {u : S.A} {ρ : Φ S.A} (h : placeKind TT T2 u ρ = .top) :
    hcBase TT T2 bT B W P ρstar σ u ρ = bT ρ.2 + P := by
  simp [hcBase, h]

/-- The base at a thick place is `B`, plus `σ(u)` at `ρ*(u)`. -/
theorem hcBase_thick {u : S.A} {ρ : Φ S.A} (h : placeKind TT T2 u ρ = .thick) :
    hcBase TT T2 bT B W P ρstar σ u ρ = B + if ρ = ρstar u then (σ u : ℤ) else 0 := by
  simp [hcBase, h]

/-- The base at a thin place is `W`. -/
theorem hcBase_thin {u : S.A} {ρ : Φ S.A} (h : placeKind TT T2 u ρ = .thin) :
    hcBase TT T2 bT B W P ρstar σ u ρ = W := by
  simp [hcBase, h]

/-- The base is at least `1`: `b_t + P ≥ k/2` at a top. -/
theorem one_le_hcBase (hyp : HCHyp R TT a bT Δ H B W P) (u : S.A) (ρ : Φ S.A) :
    1 ≤ hcBase TT T2 bT B W P ρstar σ u ρ := by
  have := R.m_add_three_le
  have := R.two_le_m
  rcases hpk : placeKind TT T2 u ρ
  · rw [hcBase_top hpk]
    have := hyp.bT_nonneg _ (placeKind_eq_top.1 hpk).2
    have := hyp.P_gt
    omega
  · rw [hcBase_thick hpk]
    have := hyp.B_pos
    split_ifs <;> omega
  · rw [hcBase_thin hpk]
    exact hyp.W_pos

/-- **The interlacing**: the design's ends and base at `ρ` meet `Setting.Ranks.HCOk`, by a case split on the kind
of `ρ`. -/
theorem hcOk_fam (hyp : HCHyp R TT a bT Δ H B W P) (u : S.A) (ρ : Φ S.A) :
    R.HCOk Δ H (hcBase TT T2 bT B W P ρstar σ u ρ) (hcU0 R TT T2 a Δ u ρ) (hcUk R TT T2 bT u ρ) := by
  have := R.m_add_three_le
  have := R.two_le_m
  obtain ⟨c, hc⟩ := R.k_even
  have hkq : (R.k : ℚ) = 2 * c := by rw [hc]; push_cast; ring
  have hk5 : (5 : ℚ) ≤ R.k := by exact_mod_cast (show 5 ≤ R.k by omega)
  have hβ : (1 : ℚ) ≤ hcBase TT T2 bT B W P ρstar σ u ρ := by exact_mod_cast one_le_hcBase hyp u ρ
  have hΔ : (0 : ℚ) ≤ Δ * R.k := by positivity
  refine ⟨hyp.Δ_pos, hyp.H_ge, ?_, ?_, ?_, ?_, ?_⟩
  all_goals by_cases hpk : placeKind TT T2 u ρ = .top
  all_goals simp only [hcU0, hcUk, hpk, ite_true, ite_false]
  · exact ⟨a ρ.2 + c - 1, by push_cast; rw [hkq]; ring⟩
  · exact ⟨4 * Δ * (2 * R.k - 2), by push_cast; ring⟩
  · exact ⟨-bT ρ.2 - c, by push_cast; rw [hkq]; ring⟩
  · exact ⟨-1, by norm_num⟩
  · have := hyp.a_ge _ (placeKind_eq_top.1 hpk).2
    have h' : (4 * Δ * R.k : ℚ) ≤ a ρ.2 := by exact_mod_cast this
    linarith
  · linarith
  · have := hyp.bT_nonneg _ (placeKind_eq_top.1 hpk).2
    have h' : (0 : ℚ) ≤ bT ρ.2 := by exact_mod_cast this
    linarith
  · norm_num
  · rw [hcBase_top hpk]
    have := hyp.P_gt
    have h' : (R.k : ℚ) ≤ 2 * P := by exact_mod_cast this
    push_cast
    linarith
  · linarith

/-- **The design's Harish-Chandra family** at the translate `u`: at `ρ`, the parameter with the ends `hcU0`, `hcUk`
and the base `hcBase`. -/
noncomputable def hcFam (R : S.Ranks) (TT T2 : Finset S.A) (a bT : S.A → ℤ) (Δ H : ℕ) (B W P : ℤ)
    (ρstar : S.A → Φ S.A) (σ : S.A → ℕ) (hyp : HCHyp R TT a bT Δ H B W P) (u : S.A) : R.HCFamily :=
  fun ρ => R.hcOf Δ H (hcBase TT T2 bT B W P ρstar σ u ρ) (hcU0 R TT T2 a Δ u ρ) (hcUk R TT T2 bT u ρ)
    (hcOk_fam hyp u ρ)

variable (hyp : HCHyp R TT a bT Δ H B W P)

/-- `b_j = β(ρ) + 2jH`. -/
theorem hcFam_b (u : S.A) (ρ : Φ S.A) (j : Fin R.m) :
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).b j = hcBase TT T2 bT B W P ρstar σ u ρ + j * (2 * H) := rfl

/-- `e_j = β(ρ) + 2jH + H`. -/
theorem hcFam_e (u : S.A) (ρ : Φ S.A) (j : Fin R.m) :
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j = hcBase TT T2 bT B W P ρstar σ u ρ + j * (2 * H) + H :=
  rfl

/-- At the top `(1, t)`: `u_0 = a_t + (k − 1)/2` and `u_{k−1} = −b_t − (k − 1)/2`. -/
theorem hcFam_u_top {u : S.A} {ρ : Φ S.A} (h : placeKind TT T2 u ρ = .top) :
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).u ⟨0, by have := R.m_add_three_le; omega⟩ =
      a ρ.2 + ((R.k : ℚ) - 1) / 2 ∧
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).u ⟨R.k - 1, by have := R.m_add_three_le; omega⟩ =
      -bT ρ.2 - ((R.k : ℚ) - 1) / 2 := by
  have := R.m_add_three_le
  simp [hcFam, Setting.Ranks.hcOf, hcU0, hcUk, h, show R.k - 1 ≠ 0 by omega]

/-- At a place that is not a top: `u_0 = 4Δ(2k − 2) + ½` and `u_{k−1} = −½`. -/
theorem hcFam_u_ntop {u : S.A} {ρ : Φ S.A} (h : placeKind TT T2 u ρ ≠ .top) :
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).u ⟨0, by have := R.m_add_three_le; omega⟩ =
      4 * Δ * (2 * (R.k : ℚ) - 2) + 1 / 2 ∧
    (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).u ⟨R.k - 1, by have := R.m_add_three_le; omega⟩ = -1 / 2 := by
  have := R.m_add_three_le
  simp [hcFam, Setting.Ranks.hcOf, hcU0, hcUk, h, show R.k - 1 ≠ 0 by omega]

/-- Every `e_j` is positive. -/
theorem hcFam_e_pos (u : S.A) (ρ : Φ S.A) (j : Fin R.m) :
    0 < (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j := by
  have := one_le_hcBase (T2 := T2) (ρstar := ρstar) (σ := σ) hyp u ρ
  rw [hcFam_e]
  positivity

/-- **The windows**, for `B = ⌈b⌉`, `W = ⌈w⌉`, `P = ⌊p⌋`, `σ ≤ H` and `η = 2mH`: `b_t + p ≤ e_j ≤ b_t + p + η` at
the top `(1, t)`, `b ≤ e_j ≤ b + η + 1` at a thick place, `w ≤ e_j ≤ w + η + 1` at a thin place, and
`|b_i − e_j| ≤ η` everywhere. -/
theorem hcFam_windows {bR wR pR : ℝ} (hB : B = ⌈bR⌉) (hW : W = ⌈wR⌉) (hP : P = ⌊pR⌋) (hσ : ∀ u, σ u ≤ H)
    (u : S.A) (ρ : Φ S.A) (j : Fin R.m) :
    (placeKind TT T2 u ρ = .top → (bT ρ.2 : ℝ) + pR ≤ (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j ∧
      ((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j : ℝ) ≤ bT ρ.2 + pR + R.m * (2 * H)) ∧
    (placeKind TT T2 u ρ = .thick → bR ≤ (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j ∧
      ((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j : ℝ) ≤ bR + R.m * (2 * H) + 1) ∧
    (placeKind TT T2 u ρ = .thin → wR ≤ (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j ∧
      ((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j : ℝ) ≤ wR + R.m * (2 * H) + 1) ∧
    ∀ i, |((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).b i : ℝ) -
      (hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j| ≤ R.m * (2 * H) := by
  have hH : (2 : ℝ) ≤ H := by
    have := hyp.H_ge
    exact_mod_cast (show 2 ≤ H by omega)
  have hj : ((j : ℕ) : ℝ) + 1 ≤ R.m := by exact_mod_cast j.isLt
  have hjH := mul_le_mul_of_nonneg_right hj (by positivity : (0 : ℝ) ≤ H)
  have hj0 : (0 : ℝ) ≤ (j : ℕ) * H := by positivity
  rw [hcFam_e]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun i => ?_⟩
  · rw [hcBase_top h]
    have h1 := Int.floor_le pR
    have h2 := Int.sub_one_lt_floor pR
    rw [← hP] at h1 h2
    push_cast
    constructor <;> nlinarith
  · rw [hcBase_thick h]
    have h1 := Int.le_ceil bR
    have h2 := Int.ceil_lt_add_one bR
    rw [← hB] at h1 h2
    obtain ⟨c, hc0, hcH, hc⟩ : ∃ c : ℤ, 0 ≤ c ∧ c ≤ H ∧ (if ρ = ρstar u then (σ u : ℤ) else 0) = c := by
      split_ifs
      · exact ⟨σ u, by positivity, by exact_mod_cast hσ u, rfl⟩
      · exact ⟨0, le_rfl, by positivity, rfl⟩
    have h3 : (0 : ℝ) ≤ c := by exact_mod_cast hc0
    have h4 : (c : ℝ) ≤ H := by exact_mod_cast hcH
    rw [hc]
    push_cast
    constructor <;> nlinarith
  · rw [hcBase_thin h]
    have h1 := Int.le_ceil wR
    have h2 := Int.ceil_lt_add_one wR
    rw [← hW] at h1 h2
    push_cast
    constructor <;> nlinarith
  · rw [hcFam_b]
    have hi : ((i : ℕ) : ℝ) + 1 ≤ R.m := by exact_mod_cast i.isLt
    have hiH := mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ H)
    have hi0 : (0 : ℝ) ≤ (i : ℕ) * H := by positivity
    push_cast
    rw [abs_le]
    constructor <;> nlinarith

/-! ## Roots of unity -/

section RootsOfUnity

variable (K : Type*) [Field K] [NumberField K]

/-- A number field `K` has a primitive `w_K`-th root of unity, `w_K = torsionOrder K`: a generator of the torsion of
`(𝓞 K)ˣ`, which is cyclic. -/
theorem exists_isPrimitiveRoot_torsionOrder : ∃ ζ : K, IsPrimitiveRoot ζ (Units.torsionOrder K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Units.torsionOrder K) := by
    rw [Units.torsionOrder, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact IsPrimitiveRoot.orderOf g
  exact ⟨((g : (𝓞 K)ˣ) : K), IsPrimitiveRoot.coe_coe_iff.2 (IsPrimitiveRoot.coe_submonoidClass_iff.2 h1)⟩

omit [NumberField K] in
variable {K} in
/-- Every root of unity of `K` is a `w_K`-th root of unity: it is integral, so a unit of `𝓞 K` of finite order. -/
theorem pow_torsionOrder_eq_one_of_pow_eq_one {ζ : K} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ^ Units.torsionOrder K = 1 := by
  have hint : IsIntegral ℤ ζ :=
    (IsPrimitiveRoot.orderOf ζ).isIntegral (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h⟩))
  obtain ⟨x, rfl⟩ : ∃ x : 𝓞 K, (x : K) = ζ := ⟨⟨ζ, hint⟩, rfl⟩
  have hx : x ^ n = 1 := RingOfIntegers.ext (by simpa using h)
  have hv : (IsUnit.of_pow_eq_one hx hn.ne').unit ∈ Units.torsion K := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa using hx)⟩
  have := congrArg (fun y : (𝓞 K)ˣ => ((y : 𝓞 K) : K)) (Units.pow_torsionOrder_eq_one K hv)
  simpa using this

end RootsOfUnity

/-- For `z^w = 1`, `w ≠ 0`: `(z^i)^{β + s + wk} = (z^β·z^s)^i`. -/
theorem pow_zpow_add_mul {z : ℂ} {w : ℕ} (hw : w ≠ 0) (hz : z ^ w = 1) (i : ℕ) (β s k : ℤ) :
    (z ^ i) ^ (β + s + w * k) = (z ^ β * z ^ s) ^ i := by
  have hz0 : z ≠ 0 := fun h => by simp [h, zero_pow hw] at hz
  have hzi : z ^ i ≠ 0 := pow_ne_zero _ hz0
  have h1 : (z ^ i) ^ w = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have h2 (t : ℤ) : (z ^ i) ^ t = (z ^ t) ^ i := by
    rw [← zpow_natCast z i, ← zpow_natCast (z ^ t) i, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [zpow_add₀ hzi, zpow_add₀ hzi, zpow_mul, zpow_natCast, h1, one_zpow, mul_one, h2, h2, mul_pow]

/-- The shift `σ` moves the base only at `ρ*(u)`, when that place is thick. -/
theorem hcBase_eq_add {u : S.A} (hstar : placeKind TT T2 u (ρstar u) = .thick) (ρ : Φ S.A) :
    hcBase TT T2 bT B W P ρstar σ u ρ =
      hcBase TT T2 bT B W P ρstar (fun _ => 0) u ρ + if ρ = ρstar u then (σ u : ℤ) else 0 := by
  by_cases hρ : ρ = ρstar u
  · subst hρ
    rw [hcBase_thick hstar, hcBase_thick hstar]
    simp
  · rcases hpk : placeKind TT T2 u ρ
    · simp [hcBase_top hpk, hρ]
    · simp [hcBase_thick hpk, hρ]
    · simp [hcBase_thin hpk, hρ]

/-- **The root-of-unity condition**: when every `ρ*(u)` is thick and `w_E ∣ H`, there are shifts `σ(u) < w_E` with
`∏_ρ τ_ρ(ζ)^{e_j(ρ)} = 1` for every translate `u`, every `j` and every root of unity `ζ ∈ E`. -/
theorem exists_shift_RU (hstar : ∀ u, placeKind TT T2 u (ρstar u) = .thick)
    (hH : Units.torsionOrder S.E ∣ H) :
    ∃ σ : S.A → ℕ, (∀ u, σ u < Units.torsionOrder S.E) ∧ ∀ u j (ζ : S.E), (∃ n, 0 < n ∧ ζ ^ n = 1) →
      ∏ ρ, (S.τ ρ ζ) ^ ((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j) = 1 := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_torsionOrder S.E
  have hw := Units.torsionOrder_ne_zero S.E
  have hτ : ∀ ρ, S.τ ρ ζ₀ ^ Units.torsionOrder S.E = 1 := fun ρ => by rw [← map_pow, hζ₀.pow_eq_one, map_one]
  have key : ∀ u, ∃ s < Units.torsionOrder S.E,
      (∏ ρ, (S.τ ρ ζ₀) ^ hcBase TT T2 bT B W P ρstar (fun _ => 0) u ρ) * (S.τ (ρstar u) ζ₀) ^ s = 1 := by
    intro u
    have hc : (∏ ρ, (S.τ ρ ζ₀) ^ hcBase TT T2 bT B W P ρstar (fun _ => 0) u ρ) ^ Units.torsionOrder S.E = 1 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτ ρ, one_zpow]
    have hc0 : (∏ ρ, (S.τ ρ ζ₀) ^ hcBase TT T2 bT B W P ρstar (fun _ => 0) u ρ) ≠ 0 := fun h => by
      simp [h, zero_pow hw] at hc
    obtain ⟨s, hs, hs'⟩ := (hζ₀.map_of_injective (S.τ (ρstar u)).injective).eq_pow_of_pow_eq_one
      (by rw [inv_pow, hc, inv_one])
    exact ⟨s, hs, by rw [hs', mul_inv_cancel₀ hc0]⟩
  choose σ hσ hσ' using key
  refine ⟨σ, hσ, fun u j ζ hζ => ?_⟩
  obtain ⟨n, hn, hζn⟩ := hζ
  obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one (pow_torsionOrder_eq_one_of_pow_eq_one hn hζn)
  obtain ⟨c, hc⟩ := hH
  have hfac : ∀ ρ, (S.τ ρ (ζ₀ ^ i)) ^ ((hcFam R TT T2 a bT Δ H B W P ρstar σ hyp u ρ).e j) =
      ((S.τ ρ ζ₀) ^ hcBase TT T2 bT B W P ρstar (fun _ => 0) u ρ *
        (if ρ = ρstar u then S.τ ρ ζ₀ ^ σ u else 1)) ^ i := by
    intro ρ
    rw [hcFam_e, hcBase_eq_add (hstar u), map_pow,
      show ∀ x y : ℤ, x + y + (j : ℕ) * (2 * (H : ℤ)) + H = x + y + Units.torsionOrder S.E * ((2 * j + 1) * c)
        from fun x y => by rw [hc]; push_cast; ring,
      pow_zpow_add_mul hw (hτ ρ)]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun ρ _ => hfac ρ, Finset.prod_pow, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [hσ' u, one_pow]

/-! ## The order of the roots of unity -/

/-- `n ≤ 2φ(n)²`, and `n ≤ φ(n)²` for odd `n`: both are multiplicative over coprime factors, of which at most one
is even, and `p^e ≤ φ(p^e)²` for odd `p`, `2^e ≤ 2φ(2^e)²`. -/
theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    rcases k with _ | s
    · simp
    rw [Nat.totient_prime_pow_succ hp]
    have hX : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.pos
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => absurd h (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, by omega⟩))⟩
      rw [pow_succ]
      nlinarith
    · have h3 : 3 ≤ p := by
        rcases hodd with ⟨r, hr⟩
        have := hp.two_le
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
      have hle : (q + 3) ^ (s + 1) ≤ ((q + 3) ^ s * (q + 3 - 1)) ^ 2 := by
        rw [show q + 3 - 1 = q + 2 by omega, pow_succ, mul_pow]
        calc (q + 3) ^ s * (q + 3) ≤ (q + 3) ^ s * (q + 2) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
          _ ≤ ((q + 3) ^ s) ^ 2 * (q + 2) ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
      exact ⟨hle.trans (Nat.le_mul_of_pos_left _ two_pos), fun _ => hle⟩
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    rcases Nat.even_or_odd a with hae | hao
    · have hbo : Odd b := by
        rcases Nat.even_or_odd b with hbe | hbo
        · exact absurd (Nat.dvd_gcd (even_iff_two_dvd.1 hae) (even_iff_two_dvd.1 hbe)) (by rw [hab]; omega)
        · exact hbo
      refine ⟨?_, fun h => absurd (Nat.odd_mul.1 h).1 (Nat.not_odd_iff_even.2 hae)⟩
      calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hbo)
        _ = _ := by ring
    · refine ⟨?_, fun h => ?_⟩
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hao) ihb.1
          _ = _ := by ring
      · exact Nat.mul_le_mul (iha.2 hao) (ihb.2 (Nat.odd_mul.1 h).2)

/-- **`w_E ≤ 32|A|²`**: `φ(w_E) ≤ [E:ℚ] = 4|A|`, the degree of a primitive `w_E`-th root of unity, and
`w_E ≤ 2φ(w_E)²`. -/
theorem torsionOrder_le (S : Setting) : Units.torsionOrder S.E ≤ 32 * Fintype.card S.A ^ 2 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder S.E
  have h1 : (Units.torsionOrder S.E).totient ≤ Module.finrank ℚ S.E := by
    have := minpoly.natDegree_le (A := ℚ) ζ
    rwa [← Polynomial.cyclotomic_eq_minpoly_rat hζ (Units.torsionOrder_pos _),
      Polynomial.natDegree_cyclotomic] at this
  have h2 : Module.finrank ℚ S.E = 4 * Fintype.card S.A := by
    rw [← IsGalois.card_aut_eq_finrank, S.card_gal]
  calc _ ≤ 2 * (Units.torsionOrder S.E).totient ^ 2 := (le_two_mul_totient_sq _).1
    _ ≤ 2 * (4 * Fintype.card S.A) ^ 2 := by gcongr; omega
    _ = 32 * Fintype.card S.A ^ 2 := by ring

end ZetaBalance

#print axioms ZetaBalance.hcFam
#print axioms ZetaBalance.placeKind_eq_thick
#print axioms ZetaBalance.hcFam_u_top
#print axioms ZetaBalance.hcFam_u_ntop
#print axioms ZetaBalance.hcFam_windows
#print axioms ZetaBalance.hcFam_e_pos
#print axioms ZetaBalance.exists_shift_RU
#print axioms ZetaBalance.torsionOrder_le
