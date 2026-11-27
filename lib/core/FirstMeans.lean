import WeylCount
import LocalOrbit

/-!
# The first local theorem without lattices: windows, box means and numerics (L5, layer 1)

The setting-free half of L5's layer 1 (module 10 of the L5/L6 plan; the lattice half is `FirstAssembly`): the orbit
data of the first local theorem (flat weights, the weight shape, the depths, the windows, the box mean and the numeric
hypotheses `FirstHyp`), the averaging over the harmonic shifts (A-N12), the segment marginals (A-N13), the density of
the flat pieces in the tensor of polynomial pairs, and the numerics (A-N20) derived from `FirstHyp`.

**Conventions** (those of `LocalOrbit`; Annex I §2.1 of the L5/L6 spec). An orbit has positions `Fin n′`, the tops are
`TT`, `N = |TT|`; a point on the tops is `TT → ℤ`, extended by `0` to the positions (`ext`). The flat weight `fl(α, β)`
is `(α_s, 0, …, 0, −β_s)` at a top `s` and `0` elsewhere (`flatWt`); `topPart` keeps a weight on the tops. The previous
V-top of `y` is `prevV TT y` (`prevVDist TT y` positions back), and `minTerm` is the odd-top term
`Σ_{odd tops y} min(β_y, α_{y′}/p^{d(y)})` of the depths. Boxes are `W^ι` (`box`), and `boxSum Wa Wb f` sums `f(A, B)`
over `Wa^ι × Wb^ι`; `boxMean` divides by the size. `IsShape`, `aWin`, `bWin`, `boxMean`, `depthI` and `FirstHyp` are
the spec's §1 statements (with `LocalOrbit`'s `SegOK` and `prevVDist`); `depth0` is Annex I's input depth `t₀`. The
segment of a V-top `x` owns the tops `y` with `prevV TT y = x`; `SegMean` is input I2 in that form.

**Main results.**
* *Averaging* (`boxSum_le_of_key`, A-N12): if `Σ_{j ∈ 𝒥} f(A − j, B − j)·w(A − j, B − j, j) ≤ g(A, B)` on a big box,
  the shifts by `𝒥` of a small box stay in the big box and `Σ_{j ∈ 𝒥} w(α, β, j) ≥ δ` on the small box, then
  `δ·Σ_small f ≤ Σ_big g` (`f, w ≥ 0`); for the flat pieces (`boxSum_le_of_har`) the weights are
  `w = ∏_s ρ(α_s, β_s, j_s)`, the key inequality divided by `dim H(A, B) = ∏_s C(A_s + m, m)·C(B_s + m, m)` (`dimH`).
* *Density* (`one_sub_pow_le_sum_rho`, `deltaF_le_sum`): with `ρ(α, β, i) = Har_m(α, β)/(C(α + i + m, m)·
  C(β + i + m, m))` (`rho`), `Σ_{i ≤ J} ρ(α, β, i) ≥ 1 − r₀^{J+1}`, `r₀ = αβ/((α + m)(β + m)) ≤ β/(β + m)`: from
  `Har_m(α, β) = C(α + m, m)·C(β + m, m)·(1 − r₀)` and `C(α + i + m, m)·(α/(α + m))^i ≤ C(α + m, m)`,
  `ρ(α, β, i) ≥ (1 − r₀)·r₀^i`.
* *Segment marginals* (`sum_box_le_of_marginal`, `boxSum_kappaX_le`, A-N13): a sum over the owned coordinates bounded
  for every value of the others bounds the sum over the box; so I2 gives
  `Σ_big (κ_P + Σ_x κ_T(x)) ≤ |W_A|^N·|W_B|^N·(κ_P + C_A·N·N₁/Y)`, the segments owning each top once.
* *Numerics* (A-N20, for `C₀ ≥ 1` and `C_H ≥ 12`, resp. `108`, resp. `6C_I + 108`): `FirstHyp.base` (the basic
  consequences: `N ≥ 2`, `k ≥ 5`, `p ≥ 25`, `b′ ≥ 8C_H·k³·N·Y`, `pb′ < a`, `N₁² ≤ k`, `La·b′/k ≤ b′/(2C_H·N)`, …);
  the shift window `J = ⌊La·b′/k⌋` is small (`FirstHyp.J_le`); the enlarged windows have entries `≥ J` and
  `A + B + 1 ≤ 8a` (`FirstHyp.winP`); the cloud's side conditions (`FirstHyp.cloudCond`); the denominators
  `2(D₀ + 2u) + D_c ≤ D` (`FirstHyp.den`); the density `δ₁^N ≥ 3/4` (`FirstHyp.dens`); the box sizes
  `|W_A|^N ≤ 2|I_a|^N`, `|W_B|^N ≤ 2|I_b|^N` (`FirstHyp.ratio`); the depths
  `⌈t₀(a + c, b + c) + N·J⌉ + 2n′c ≤ t_I(a, b)` (`FirstHyp.depth`), with the shift
  `t₀(A, B) ≤ t₀(A − j, B − j) + N·J` (`depth0_shift`).

**The routes.** The averaging multiplies out the density, moves each shift `j` into the big box (injectively, the terms
being `≥ 0`) and exchanges the sums back. The segment marginals fibre the box over the coordinates outside the
segment (`sum_box_split`). The density bound is geometric; the exponential bounds `(1 − x)^N ≤ e^{−Nx}`,
`1 − Nx ≤ (1 − x)^N` and `(1 + x)^N ≤ 1/(1 − Nx)` (`one_sub_pow_le_exp`, `one_sub_mul_le_pow`, `one_add_pow_le_inv`)
turn `(β*/(β* + m))^{J+1} ≤ e^{−2La/5} ≤ (NY)^{−3}` and `2N(2c + J) ≤ |I_a|, |I_b|` into the constants `3/4` and `2`.

**Readings of the planning statements.** The Annex estimates the density as `≈ 1 − e^{−La}` and the averaging loss as
`2`; here `δ₁^N ≥ 3/4` and the box ratio is `≤ 4`, so the averaging loses `16/3`, and every constant stays explicit
(simplification S2). The exact bound `ρ(α, β, i) ≥ (1 − r₀)r₀^i` was checked against exact rationals (`m ≤ 6`,
`α, β < 12`, `J < 8`). `λ_a` is `log_p(8a + k) + 1` (the Annex has `m = k − 1` for `k`, a weaker requirement on the
inputs). `FirstHyp` is the spec's (`p_ge`, `band`, `band_small` are consumed by the inputs, not here).
-/

namespace FirstMeans

open Finset LocalOrbit

noncomputable section

/-! ## Boxes and box sums -/

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The box `W^ι`** of integer points with all coordinates in the window `W`. -/
abbrev box (W : Finset ℤ) : Finset (ι → ℤ) := Fintype.piFinset fun _ => W

/-- **The box sum** `Σ_{A ∈ Wa^ι} Σ_{B ∈ Wb^ι} f(A, B)`. -/
def boxSum (Wa Wb : Finset ℤ) (f : (ι → ℤ) → (ι → ℤ) → ℝ) : ℝ :=
  ∑ A ∈ box (ι := ι) Wa, ∑ B ∈ box (ι := ι) Wb, f A B

/-- **Membership in a box.** -/
theorem mem_box {W : Finset ℤ} {A : ι → ℤ} : A ∈ box W ↔ ∀ i, A i ∈ W := Fintype.mem_piFinset

/-- **The size of a box**: `|W^ι| = |W|^{|ι|}`. -/
theorem card_box (W : Finset ℤ) : (box (ι := ι) W).card = W.card ^ Fintype.card ι := by
  simp [Fintype.card_piFinset]

/-- **Box sums are monotone.** -/
theorem boxSum_mono {Wa Wb : Finset ℤ} {f g : (ι → ℤ) → (ι → ℤ) → ℝ}
    (h : ∀ A ∈ box Wa, ∀ B ∈ box Wb, f A B ≤ g A B) : boxSum Wa Wb f ≤ boxSum Wa Wb g :=
  sum_le_sum fun A hA => sum_le_sum fun B hB => h A hA B hB

/-- **Box sums are additive.** -/
theorem boxSum_add (Wa Wb : Finset ℤ) (f g : (ι → ℤ) → (ι → ℤ) → ℝ) :
    boxSum Wa Wb (fun A B => f A B + g A B) = boxSum Wa Wb f + boxSum Wa Wb g := by
  simp only [boxSum, sum_add_distrib]

/-- **Box sums are homogeneous.** -/
theorem boxSum_smul (Wa Wb : Finset ℤ) (c : ℝ) (f : (ι → ℤ) → (ι → ℤ) → ℝ) :
    boxSum Wa Wb (fun A B => c * f A B) = c * boxSum Wa Wb f := by
  simp only [boxSum, mul_sum]

/-- **The box sum of a constant.** -/
theorem boxSum_const (Wa Wb : Finset ℤ) (c : ℝ) :
    boxSum (ι := ι) Wa Wb (fun _ _ => c) = (Wa.card : ℝ) ^ Fintype.card ι * (Wb.card : ℝ) ^ Fintype.card ι * c := by
  simp only [boxSum, sum_const, card_box, nsmul_eq_mul]
  push_cast
  ring

/-- **Box sums of nonnegative functions are nonnegative.** -/
theorem boxSum_nonneg {Wa Wb : Finset ℤ} {f : (ι → ℤ) → (ι → ℤ) → ℝ} (h : ∀ A B, 0 ≤ f A B) :
    0 ≤ boxSum Wa Wb f :=
  sum_nonneg fun A _ => sum_nonneg fun B _ => h A B

/-- **A shifted box**: `box (W + τ) = box W + τ`, summed: `Σ_{A ∈ (W + τ)^ι} F(A) = Σ_{A ∈ W^ι} F(A + τ)` for
interval windows. -/
theorem sum_box_Icc_shift (lo hi τ : ℤ) (F : (ι → ℤ) → ℝ) :
    ∑ A ∈ box (ι := ι) (Icc (lo + τ) (hi + τ)), F A = ∑ A ∈ box (ι := ι) (Icc lo hi), F (A + fun _ => τ) := by
  symm
  refine sum_nbij' (fun A => A + fun _ => τ) (fun A => A - fun _ => τ) (fun A hA => ?_) (fun A hA => ?_)
    (fun A _ => by simp) (fun A _ => by simp) (fun A _ => rfl)
  · rw [mem_box] at hA ⊢
    intro i
    have := mem_Icc.1 (hA i)
    simp only [Pi.add_apply, mem_Icc]
    omega
  · rw [mem_box] at hA ⊢
    intro i
    have := mem_Icc.1 (hA i)
    simp only [Pi.sub_apply, mem_Icc]
    omega

/-- **Shifting both windows** of a box sum by `τ` shifts the points by `τ`. -/
theorem boxSum_shift (la ha lb hb τ : ℤ) (f : (ι → ℤ) → (ι → ℤ) → ℝ) :
    boxSum (Icc (la + τ) (ha + τ)) (Icc (lb + τ) (hb + τ)) f =
      boxSum (Icc la ha) (Icc lb hb) fun A B => f (A + fun _ => τ) (B + fun _ => τ) := by
  rw [boxSum, sum_box_Icc_shift]
  exact sum_congr rfl fun A _ => sum_box_Icc_shift lb hb τ _

end Box

/-! ## Averaging over the harmonic shifts (A-N12) -/

section Average

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Averaging over the shifts** (A-N12): let `f, w ≥ 0`, let the shifts `(α + j, β + j)`, `j ∈ 𝒥`, of the small box
`Sa^ι × Sb^ι` lie in the big box `Ba^ι × Bb^ι`, let `Σ_{j ∈ 𝒥} f(A − j, B − j)·w(A − j, B − j, j) ≤ g(A, B)` on the big
box (the key inequality) and `Σ_{j ∈ 𝒥} w(α, β, j) ≥ δ` on the small box (the density). Then
`δ·Σ_small f ≤ Σ_big g`. Proof: multiply out the density, exchange the sums, move each shift `j` to the big box
(injective, the terms are `≥ 0`) and exchange back. -/
theorem boxSum_le_of_key {Sa Sb Ba Bb : Finset ℤ} {𝒥 : Finset (ι → ℤ)} (f g : (ι → ℤ) → (ι → ℤ) → ℝ)
    (w : (ι → ℤ) → (ι → ℤ) → (ι → ℤ) → ℝ) {δ : ℝ} (hf : ∀ α β, 0 ≤ f α β) (hw : ∀ α β j, 0 ≤ w α β j)
    (hsub : ∀ α ∈ box Sa, ∀ β ∈ box Sb, ∀ j ∈ 𝒥, α + j ∈ box Ba ∧ β + j ∈ box Bb)
    (hkey : ∀ A ∈ box Ba, ∀ B ∈ box Bb, ∑ j ∈ 𝒥, f (A - j) (B - j) * w (A - j) (B - j) j ≤ g A B)
    (hdens : ∀ α ∈ box Sa, ∀ β ∈ box Sb, δ ≤ ∑ j ∈ 𝒥, w α β j) :
    δ * boxSum Sa Sb f ≤ boxSum Ba Bb g := by
  set S := box (ι := ι) Sa ×ˢ box (ι := ι) Sb
  set Bg := box (ι := ι) Ba ×ˢ box (ι := ι) Bb
  have hS : boxSum Sa Sb f = ∑ x ∈ S, f x.1 x.2 := by rw [sum_product]; rfl
  have hB : boxSum Ba Bb g = ∑ x ∈ Bg, g x.1 x.2 := by rw [sum_product]; rfl
  rw [hS, hB, mul_sum]
  -- the shift by `j`
  set sh : (ι → ℤ) → ((ι → ℤ) × (ι → ℤ)) → (ι → ℤ) × (ι → ℤ) := fun j x => (x.1 + j, x.2 + j)
  set h : (ι → ℤ) → ((ι → ℤ) × (ι → ℤ)) → ℝ := fun j y => f (y.1 - j) (y.2 - j) * w (y.1 - j) (y.2 - j) j
  calc ∑ x ∈ S, δ * f x.1 x.2
      ≤ ∑ x ∈ S, ∑ j ∈ 𝒥, h j (sh j x) := sum_le_sum fun x hx => by
        obtain ⟨h1, h2⟩ := mem_product.1 hx
        simp only [h, sh, add_sub_cancel_right, ← mul_sum]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hdens _ h1 _ h2) (hf _ _)
    _ = ∑ j ∈ 𝒥, ∑ x ∈ S, h j (sh j x) := sum_comm
    _ ≤ ∑ j ∈ 𝒥, ∑ y ∈ Bg, h j y := sum_le_sum fun j hj => by
        rw [← sum_image (s := S) (g := sh j) (f := h j) fun x _ y _ hxy => by
          simp only [sh, Prod.mk.injEq, add_left_inj] at hxy
          exact Prod.ext hxy.1 hxy.2]
        refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ => mul_nonneg (hf _ _) (hw _ _ _)
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        obtain ⟨h1, h2⟩ := mem_product.1 hx
        obtain ⟨h3, h4⟩ := hsub _ h1 _ h2 j hj
        exact mem_product.2 ⟨h3, h4⟩
    _ = ∑ y ∈ Bg, ∑ j ∈ 𝒥, h j y := sum_comm
    _ ≤ ∑ y ∈ Bg, g y.1 y.2 := sum_le_sum fun y hy => hkey _ (mem_product.1 hy).1 _ (mem_product.1 hy).2

end Average

/-! ## The density of the flat pieces -/

section Density

open WeylCount

/-- **The share of the flat piece** `fl(α, β)` in the tensor `Sym^{α+i} ⊗ Sym^{β+i}∨` of `GL_{m+1}`:
`ρ(α, β, i) = Har_m(α, β)/(C(α + i + m, m)·C(β + i + m, m))`. -/
def rho (m α β i : ℕ) : ℝ := (har m α β : ℝ) / (((α + i + m).choose m : ℝ) * ((β + i + m).choose m : ℝ))

/-- **The ratio** `r₀ = αβ/((α + m)(β + m))` of the density bound. -/
def rzero (m α β : ℕ) : ℝ := (α : ℝ) * β / (((α : ℝ) + m) * ((β : ℝ) + m))

/-- **One step down the column**: `C(α + m − 1, m)·(α + m) = C(α + m, m)·α` for `m ≥ 1`. -/
theorem choose_pred_mul {m : ℕ} (hm : 1 ≤ m) (α : ℕ) :
    ((α + m - 1).choose m : ℝ) * ((α : ℝ) + m) = ((α + m).choose m : ℝ) * α := by
  have h := Nat.choose_mul_succ_eq (α + m - 1) m
  rw [show α + m - 1 + 1 = α + m by omega, show α + m - m = α by omega] at h
  exact_mod_cast h

/-- **The harmonic count** `Har_m(α, β) = C(α + m, m)·C(β + m, m)·(1 − r₀)` for `m ≥ 1`. -/
theorem har_eq {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) :
    (har m α β : ℝ) = ((α + m).choose m : ℝ) * ((β + m).choose m : ℝ) * (1 - rzero m α β) := by
  have hle : (α + m - 1).choose m * (β + m - 1).choose m ≤ (α + m).choose m * (β + m).choose m :=
    Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
  rw [har, Nat.cast_sub hle]
  push_cast
  have hα : (0 : ℝ) < α + m := by positivity
  have hβ : (0 : ℝ) < β + m := by positivity
  have e1 := choose_pred_mul hm α
  have e2 := choose_pred_mul hm β
  have eα : ((α + m - 1).choose m : ℝ) = ((α + m).choose m : ℝ) * α / (α + m) := by
    rw [eq_div_iff hα.ne']; exact e1
  have eβ : ((β + m - 1).choose m : ℝ) = ((β + m).choose m : ℝ) * β / (β + m) := by
    rw [eq_div_iff hβ.ne']; exact e2
  rw [eα, eβ, rzero]
  field_simp

/-- **One step up the row**: `C(α + i + 1 + m, m)·(α/(α + m)) ≤ C(α + i + m, m)`, as
`C(α + i + 1 + m, m)·(α + i + 1) = C(α + i + m, m)·(α + i + 1 + m)` and `α(α + i + 1 + m) ≤ (α + m)(α + i + 1)`. -/
theorem choose_succ_mul_le (m α i : ℕ) :
    ((α + (i + 1) + m).choose m : ℝ) * ((α : ℝ) / (α + m)) ≤ ((α + i + m).choose m : ℝ) := by
  rcases Nat.eq_zero_or_pos (α + m) with h0 | h0
  · have : (α : ℝ) = 0 := by exact_mod_cast (show α = 0 by omega)
    rw [this, zero_div, mul_zero]
    positivity
  have h := Nat.choose_mul_succ_eq (α + i + m) m
  rw [show α + i + m + 1 = α + (i + 1) + m by omega, show α + (i + 1) + m - m = α + i + 1 by omega] at h
  have h' : ((α + (i + 1) + m).choose m : ℝ) * ((α : ℝ) + i + 1) =
      ((α + i + m).choose m : ℝ) * ((α : ℝ) + i + m + 1) := by
    have h2 : (α + (i + 1) + m).choose m * (α + i + 1) = (α + i + m).choose m * (α + i + m + 1) := by
      rw [h.symm]; ring
    exact_mod_cast h2
  have hpos : (0 : ℝ) < α + m := by exact_mod_cast h0
  have hpos' : (0 : ℝ) < α + i + 1 := by positivity
  rw [mul_div_assoc', div_le_iff₀ hpos]
  have hc : (0 : ℝ) ≤ ((α + i + m).choose m : ℝ) := by positivity
  have key : ((α + (i + 1) + m).choose m : ℝ) * α * (α + i + 1) ≤
      ((α + i + m).choose m : ℝ) * (α + m) * (α + i + 1) := by
    calc ((α + (i + 1) + m).choose m : ℝ) * α * (α + i + 1)
        = ((α + i + m).choose m : ℝ) * ((α : ℝ) + i + m + 1) * α := by rw [mul_right_comm, h']
      _ ≤ ((α + i + m).choose m : ℝ) * (α + m) * (α + i + 1) := by
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc
        nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact le_of_mul_le_mul_right key hpos'

/-- **Up the row, `i` steps**: `C(α + i + m, m)·(α/(α + m))^i ≤ C(α + m, m)`. -/
theorem choose_mul_pow_le (m α i : ℕ) :
    ((α + i + m).choose m : ℝ) * ((α : ℝ) / (α + m)) ^ i ≤ ((α + m).choose m : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hr : (0 : ℝ) ≤ (α : ℝ) / (α + m) := by positivity
    calc ((α + (i + 1) + m).choose m : ℝ) * ((α : ℝ) / (α + m)) ^ (i + 1)
        = ((α + (i + 1) + m).choose m : ℝ) * ((α : ℝ) / (α + m)) * ((α : ℝ) / (α + m)) ^ i := by ring
      _ ≤ ((α + i + m).choose m : ℝ) * ((α : ℝ) / (α + m)) ^ i :=
        mul_le_mul_of_nonneg_right (choose_succ_mul_le m α i) (pow_nonneg hr _)
      _ ≤ _ := ih

/-- **`r₀` is a probability**: `0 ≤ r₀ ≤ 1`. -/
theorem rzero_mem (m α β : ℕ) : 0 ≤ rzero m α β ∧ rzero m α β ≤ 1 := by
  refine ⟨by unfold rzero; positivity, ?_⟩
  unfold rzero
  rcases Nat.eq_zero_or_pos (α * β) with h | h
  · rcases Nat.mul_eq_zero.1 h with h | h <;> simp [h]
  have hα : (0 : ℝ) < α := by exact_mod_cast Nat.pos_of_mul_pos_right h
  have hβ : (0 : ℝ) < β := by exact_mod_cast Nat.pos_of_mul_pos_left h
  rw [div_le_one (by positivity)]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **The share decays at most geometrically**: `ρ(α, β, i) ≥ (1 − r₀)·r₀^i` for `m ≥ 1`. -/
theorem rho_ge {m : ℕ} (hm : 1 ≤ m) (α β i : ℕ) : (1 - rzero m α β) * rzero m α β ^ i ≤ rho m α β i := by
  have ha : (0 : ℝ) < ((α + i + m).choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hb : (0 : ℝ) < ((β + i + m).choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have h1 : 0 ≤ 1 - rzero m α β := by linarith [(rzero_mem m α β).2]
  have hr : rzero m α β ^ i = ((α : ℝ) / (α + m)) ^ i * ((β : ℝ) / (β + m)) ^ i := by
    rw [← mul_pow, rzero, div_mul_div_comm]
  rw [rho, har_eq hm, le_div_iff₀ (mul_pos ha hb)]
  calc (1 - rzero m α β) * rzero m α β ^ i * (((α + i + m).choose m : ℝ) * ((β + i + m).choose m : ℝ))
      = (1 - rzero m α β) * ((((α + i + m).choose m : ℝ) * ((α : ℝ) / (α + m)) ^ i) *
          (((β + i + m).choose m : ℝ) * ((β : ℝ) / (β + m)) ^ i)) := by rw [hr]; ring
    _ ≤ (1 - rzero m α β) * (((α + m).choose m : ℝ) * ((β + m).choose m : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (choose_mul_pow_le m α i) (choose_mul_pow_le m β i)
          (by positivity) (by positivity)) h1
    _ = _ := by ring

/-- **Density of the flat pieces** (one top): `Σ_{i ≤ J} ρ(α, β, i) ≥ 1 − r₀^{J+1}` for `m ≥ 1`. -/
theorem one_sub_pow_le_sum_rho {m : ℕ} (hm : 1 ≤ m) (α β J : ℕ) :
    1 - rzero m α β ^ (J + 1) ≤ ∑ i ∈ range (J + 1), rho m α β i := by
  rw [← mul_neg_geom_sum, mul_sum]
  exact sum_le_sum fun i _ => rho_ge hm α β i

/-- **`r₀ ≤ β/(β + m)`.** -/
theorem rzero_le (m α β : ℕ) : rzero m α β ≤ (β : ℝ) / (β + m) := by
  unfold rzero
  rcases Nat.eq_zero_or_pos (α + m) with h | h
  · have : (α : ℝ) = 0 := by exact_mod_cast (show α = 0 by omega)
    rw [this]
    simp only [zero_mul, zero_div]
    positivity
  have hα : (0 : ℝ) < α + m := by exact_mod_cast h
  rw [← div_mul_div_comm]
  have : (α : ℝ) / (α + m) ≤ 1 := (div_le_one hα).2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  calc (α : ℝ) / (α + m) * (β / (β + m)) ≤ 1 * (β / (β + m)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := one_mul _

/-- **The shifts multiply over the tops**: `Σ_{j ∈ [0, J]^ι} ∏_s ρ(α_s, β_s, j_s) = ∏_s Σ_{i ≤ J} ρ(α_s, β_s, i)`. -/
theorem prod_sum_rho {ι : Type*} [Fintype ι] [DecidableEq ι] (m J : ℕ) (α β : ι → ℕ) (jj : ι → ℕ → ℕ) :
    ∑ j ∈ Fintype.piFinset (fun _ : ι => range (J + 1)), ∏ s, rho m (α s) (β s) (jj s (j s)) =
      ∏ s, ∑ i ∈ range (J + 1), rho m (α s) (β s) (jj s i) :=
  (prod_univ_sum (fun _ => range (J + 1)) fun s i => rho m (α s) (β s) (jj s i)).symm

end Density

/-! ## Elementary bounds -/

section Elementary

/-- **`(1 + x)^N ≤ e^{Nx}`** for `x ≥ −1`. -/
theorem one_add_pow_le_exp {x : ℝ} (hx : -1 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ Real.exp (N * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) N

/-- **`(1 − x)^N ≤ e^{−Nx}`** for `x ≤ 1`. -/
theorem one_sub_pow_le_exp {x : ℝ} (hx : x ≤ 1) (N : ℕ) : (1 - x) ^ N ≤ Real.exp (-(N * x)) := by
  have := one_add_pow_le_exp (x := -x) (by linarith) N
  rw [← sub_eq_add_neg, mul_neg] at this
  exact this

/-- **Bernoulli**: `1 − Nx ≤ (1 − x)^N` for `x ≤ 2`. -/
theorem one_sub_mul_le_pow {x : ℝ} (hx : x ≤ 2) (N : ℕ) : 1 - N * x ≤ (1 - x) ^ N := by
  have := one_add_mul_le_pow (a := -x) (by linarith) N
  rw [mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
  exact this

/-- **`(1 + x)^N ≤ 1/(1 − Nx)`** for `x ≥ 0` and `Nx < 1`: `(1 + x)^N·(1 − x)^N = (1 − x²)^N ≤ 1` and Bernoulli
`(1 − x)^N ≥ 1 − Nx`. -/
theorem one_add_pow_le_inv {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : N * x < 1) : (1 + x) ^ N ≤ 1 / (1 - N * x) := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp
  have hx1 : x ≤ 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast h0
    nlinarith
  have hb := one_sub_mul_le_pow (x := x) (by linarith) N
  have hpos : 0 < 1 - N * x := by linarith
  rw [le_div_iff₀ hpos]
  calc (1 + x) ^ N * (1 - N * x) ≤ (1 + x) ^ N * (1 - x) ^ N :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)
    _ = (1 - x ^ 2) ^ N := by rw [← mul_pow]; ring
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

end Elementary

/-! ## Segment marginals (A-N13) -/

section Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Splitting a box along a set of coordinates**: the sum over `W^ι` is the sum over the values `A₀` of the
coordinates outside `P` (those in `P` set to `0`) of the sums over the coordinates in `P`, the others frozen at `A₀`
(the fibres of the projection forgetting the coordinates in `P`). -/
theorem sum_box_split (P : ι → Prop) [DecidablePred P] (W : Finset ℤ) (F : (ι → ℤ) → ℝ) :
    ∑ A ∈ box W, F A = ∑ A₀ ∈ Fintype.piFinset (fun i => if P i then ({0} : Finset ℤ) else W),
      ∑ A ∈ Fintype.piFinset (fun i => if P i then W else {A₀ i}), F A := by
  set proj : (ι → ℤ) → ι → ℤ := fun A i => if P i then 0 else A i
  have hmaps : ∀ A ∈ box W, proj A ∈ Fintype.piFinset (fun i => if P i then ({0} : Finset ℤ) else W) := by
    intro A hA
    rw [Fintype.mem_piFinset]
    intro i
    simp only [proj]
    split_ifs
    · exact mem_singleton_self 0
    · exact mem_box.1 hA i
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun A₀ hA₀ => sum_congr ?_ fun _ _ => rfl
  rw [Fintype.mem_piFinset] at hA₀
  ext A
  simp only [mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hA, rfl⟩ i
    simp only [proj]
    split_ifs with h
    · exact hA i
    · exact mem_singleton_self _
  · intro hA
    refine ⟨fun i => ?_, funext fun i => ?_⟩
    · have h1 := hA i
      have h2 := hA₀ i
      split_ifs at h1 h2 with h
      · exact h1
      · rw [mem_singleton.1 h1]; exact h2
    · have h1 := hA i
      have h2 := hA₀ i
      simp only [proj]
      split_ifs at h1 h2 ⊢ with h
      · exact (mem_singleton.1 h2).symm
      · exact mem_singleton.1 h1

/-- **Segment marginals** (A-N13): if the sum of `F` over the coordinates in `P`, the others frozen at any values in
`W`, is at most `|W|^{#P}·M`, then the sum over the whole box is at most `|W|^{|ι|}·M`. -/
theorem sum_box_le_of_marginal (P : ι → Prop) [DecidablePred P] (W : Finset ℤ) (F : (ι → ℤ) → ℝ) (M : ℝ)
    (h : ∀ A₀ : ι → ℤ, (∀ i, ¬ P i → A₀ i ∈ W) →
      ∑ A ∈ Fintype.piFinset (fun i => if P i then W else {A₀ i}), F A ≤
        (W.card : ℝ) ^ (univ.filter P).card * M) :
    ∑ A ∈ box W, F A ≤ (W.card : ℝ) ^ Fintype.card ι * M := by
  rw [sum_box_split P W F]
  calc _ ≤ ∑ _A₀ ∈ Fintype.piFinset (fun i => if P i then ({0} : Finset ℤ) else W),
        (W.card : ℝ) ^ (univ.filter P).card * M := sum_le_sum fun A₀ hA₀ => h A₀ fun i hi => by
          have := Fintype.mem_piFinset.1 hA₀ i
          simpa [hi] using this
    _ = _ := by
      rw [sum_const, Fintype.card_piFinset, nsmul_eq_mul]
      have hc : (∏ i, (if P i then ({0} : Finset ℤ) else W).card) = W.card ^ (univ.filter fun i => ¬ P i).card := by
        rw [show (fun i => (if P i then ({0} : Finset ℤ) else W).card) = fun i => if P i then 1 else W.card from
          funext fun i => by split_ifs <;> simp, prod_ite, prod_const_one, one_mul, prod_const]
      rw [hc, ← mul_assoc]
      congr 1
      push_cast
      rw [← pow_add, add_comm, card_filter_add_card_filter_not, card_univ]

end Marginal

/-! ## The orbit data: flat weights, the weight shape, depths and windows -/

section Orbit

variable {n' k : ℕ}

/-- **A point on the tops, extended by `0`**: `ext α s = α_s` at a top `s`, `0` elsewhere. -/
def ext (TT : Finset (Fin n')) (α : TT → ℤ) : Fin n' → ℤ := fun s => if h : s ∈ TT then α ⟨s, h⟩ else 0

/-- **`ext` at a top.** -/
theorem ext_of_mem {TT : Finset (Fin n')} (α : TT → ℤ) {s : Fin n'} (h : s ∈ TT) : ext TT α s = α ⟨s, h⟩ := by
  simp [ext, h]

/-- **`ext` off the tops.** -/
theorem ext_of_not_mem {TT : Finset (Fin n')} (α : TT → ℤ) {s : Fin n'} (h : s ∉ TT) : ext TT α s = 0 := by
  simp [ext, h]

/-- **`ext` of a top point.** -/
@[simp] theorem ext_coe {TT : Finset (Fin n')} (α : TT → ℤ) (s : TT) : ext TT α s = α s := by
  rw [ext_of_mem α s.2]

/-- **`ext` is additive.** -/
theorem ext_add {TT : Finset (Fin n')} (α β : TT → ℤ) (s : Fin n') : ext TT (α + β) s = ext TT α s + ext TT β s := by
  unfold ext; split_ifs <;> simp

/-- **`ext` is subtractive.** -/
theorem ext_sub {TT : Finset (Fin n')} (α β : TT → ℤ) (s : Fin n') : ext TT (α - β) s = ext TT α s - ext TT β s := by
  unfold ext; split_ifs <;> simp

/-- **`ext` of a nonnegative point is nonnegative.** -/
theorem ext_nonneg {TT : Finset (Fin n')} {α : TT → ℤ} (h : ∀ s, 0 ≤ α s) (s : Fin n') : 0 ≤ ext TT α s := by
  unfold ext; split_ifs <;> simp [h]

/-- **The flat weight** `fl(α, β)`: `(α_s, 0, …, 0, −β_s)` at a top `s`, `0` elsewhere. -/
def flatWt (TT : Finset (Fin n')) (α β : TT → ℤ) : Fin n' → Fin k → ℤ := fun s i =>
  if i.val = 0 then ext TT α s else if i.val + 1 = k then -ext TT β s else 0

/-- **Flat weights with nonnegative extremes are dominant** (`k ≥ 2`). -/
theorem antitone_flatWt (hk : 2 ≤ k) {TT : Finset (Fin n')} {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s)
    (hβ : ∀ s, 0 ≤ β s) (s : Fin n') : Antitone (flatWt (k := k) TT α β s) := by
  intro i i' (hii : i.val ≤ i'.val)
  have h1 := ext_nonneg hα s
  have h2 := ext_nonneg hβ s
  have hi := i.isLt
  have hi' := i'.isLt
  simp only [flatWt]
  split_ifs <;> omega

/-- **The top part** of a weight: `λ` at the tops, `0` elsewhere. -/
def topPart (TT : Finset (Fin n')) (lam0 : Fin n' → Fin k → ℤ) : Fin n' → Fin k → ℤ :=
  fun s => if s ∈ TT then lam0 s else 0

/-- **The design's weight shape** on one orbit: dominant; at a top `s`, `λ_s = (a_s, …, −b_s)` with middle entries
in `[−c, c]`; off the tops every entry in `[−c, c]`. -/
def IsShape (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) : Prop :=
  (∀ s, Antitone (lam0 s)) ∧ ∀ s i,
    (s ∈ TT → (i.val = 0 → lam0 s i = a s) ∧ (i.val + 1 = k → lam0 s i = -b s) ∧
      (0 < i.val → i.val + 1 < k → |lam0 s i| ≤ c)) ∧ (s ∉ TT → |lam0 s i| ≤ c)

/-- **The previous V-top** of `y`: the position `prevVDist TT y` steps back (cyclically). -/
def prevV (TT : Finset (Fin n')) (y : Fin n') : Fin n' :=
  ⟨(y.val + n' - prevVDist TT y % n') % n', Nat.mod_lt _ (Fin.pos y)⟩

/-- **The odd-top term of the depth**: `Σ_{odd tops y} min(β_y, α_{y′}/p^{d(y)})`, `y′` the previous V-top and
`d(y)` the distance to it. -/
def minTerm (p : ℕ) (TT : Finset (Fin n')) (α β : Fin n' → ℤ) : ℝ :=
  ∑ y ∈ TT.filter (fun y => ¬ Even y.val), min (β y : ℝ) ((α (prevV TT y) : ℝ) / (p : ℝ) ^ prevVDist TT y)

/-- **The depth of the input column families** at the flat weight `fl(α, β)` (Annex I §2.3, `t₀`):
`minTerm + C_t·N·(a/p² + b′/p + La·a/(pk) + La·b′/k + k·Q + Q·c₄)`, `Q = p^{G′}`, `c₄` the working conductor. -/
def depth0 (Ct La : ℝ) (p : ℕ) (TT : Finset (Fin n')) (k G' : ℕ) (a b' : ℝ) (c₄ : ℕ) (α β : TT → ℤ) : ℝ :=
  minTerm p TT (ext TT α) (ext TT β) + Ct * TT.card * (a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) + La * b' / k +
    k * (p : ℝ) ^ G' + (p : ℝ) ^ G' * c₄)

end Orbit

/-- **The `a`-window** `I_a = ℤ ∩ [a, a + a/(kY)]`. -/
def aWin (k : ℕ) (Y a : ℝ) : Finset ℤ := Finset.Icc ⌈a⌉ ⌊a + a / (k * Y)⌋

/-- **The `b`-window** `I_b = ℤ ∩ [b_ℓ, b_u]`. -/
def bWin (bl bu : ℝ) : Finset ℤ := Finset.Icc ⌈bl⌉ ⌊bu⌋

/-- **The box mean** of `κ` over `I_a^{TT} × I_b^{TT}`. -/
def boxMean {n' : ℕ} (TT : Finset (Fin n')) (k : ℕ) (Y a bl bu : ℝ) (κ : (TT → ℤ) → (TT → ℤ) → ℝ) : ℝ :=
  boxSum (aWin k Y a) (bWin bl bu) κ / (((aWin k Y a).card : ℝ) ^ TT.card * ((bWin bl bu).card : ℝ) ^ TT.card)

/-- **The first theorem's depth** `t_I(a, b)` (gain-spec §2.5 `dep` for `p ≥ p₀`):
`minTerm + C·N·N₁(a/p² + b′/p + La·a/(pk) + La·b′/k) + C·N·(Q·c_I + kQ + k·log_p a + c) + 2n′c`,
`c_I = c* + C·N·k·log_p a + 4Nc + 2n′c`. -/
def depthI (C La : ℝ) (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (a b' : ℝ) (c cStar : ℕ)
    (aw bw : Fin n' → ℤ) : ℝ :=
  let N : ℝ := TT.card
  let Q : ℝ := (p : ℝ) ^ G'
  let cI : ℝ := cStar + C * N * k * Real.logb p a + 4 * N * c + 2 * n' * c
  minTerm p TT aw bw + C * N * N₁ * (a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) + La * b' / k) +
    C * N * (Q * cI + k * Q + k * Real.logb p a + c) + 2 * n' * c

/-- **The numeric hypotheses of the first theorem** (h1–h20 of Annex I §2.2), with `La = C₀N₁²·log a`; `δ` is the
band width `C_H·N₁·La/k + 2(b_u − b_ℓ)/b′`. -/
structure FirstHyp (C₀ CH : ℝ) (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ)
    (c D cStar : ℕ) : Prop where
  /-- (h1) -/
  Y_ge : 1 ≤ Y
  /-- (h2) `p ≥ p₀ = k²Y²` (used by the inputs) -/
  p_ge : (k : ℝ) ^ 2 * Y ^ 2 ≤ p
  /-- (h3)–(h5) the segments -/
  seg : SegOK TT G' N₁
  /-- (h6) -/
  N₁_pos : 1 ≤ N₁
  /-- (h7) -/
  k_ge : 2 * N₁ + 3 ≤ k
  /-- (h8) -/
  La_ge : 8 * Real.log (TT.card * Y) ≤ C₀ * N₁ ^ 2 * Real.log a
  /-- (h9), (h10) the `b`-window -/
  b_win : 0 < b' ∧ bl ≤ b' ∧ b' ≤ bu ∧ Yb * TT.card * (C₀ * N₁ ^ 2 * Real.log a) * b' / k ≤ bu - bl ∧
    bu - bl ≤ b' / 2
  /-- (h11) -/
  Yb_ge : CH ≤ Yb ∧ 2 * Yb * TT.card * (C₀ * N₁ ^ 2 * Real.log a) < k
  /-- (h12) -/
  a_big : (k : ℝ) * Y ^ 2 * Yb * TT.card * (C₀ * N₁ ^ 2 * Real.log a) * Real.log a ≤ a / b'
  /-- (h13) the band width `δ < 1/6` (used by the inputs) -/
  band_small : CH * N₁ * (C₀ * N₁ ^ 2 * Real.log a) / k + 2 * (bu - bl) / b' < 1 / 6
  /-- (h14) -/
  p_lt : (p : ℝ) < a / b'
  /-- (h15) -/
  La_sq : CH * TT.card * (C₀ * N₁ ^ 2 * Real.log a) ^ 2 ≤ k
  /-- (h16) the band (used by the inputs) -/
  band : ∀ d : ℕ, Odd d → ¬ ((a / b') * (1 - 2 * (CH * N₁ * (C₀ * N₁ ^ 2 * Real.log a) / k + 2 * (bu - bl) / b')) ≤
      (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ (a / b') * (1 + 2 * (CH * N₁ * (C₀ * N₁ ^ 2 * Real.log a) / k + 2 * (bu - bl) / b')))
  /-- (h17) the cloud is small -/
  cloud : (c : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a * b' / k
  /-- (h18) the denominator -/
  D_ge : CH * TT.card * Y ^ 2 * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * Real.logb p a ≤ D
  /-- (h19) the conductor -/
  cStar_ge : 8 * (D + 1) ≤ cStar
  /-- (h20) -/
  b'_big : CH * (k : ℝ) ^ 3 * TT.card * ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) * Y ≤ b'


/-! ## The dimension of the tensor of polynomial pairs -/

section DimH

variable {n' : ℕ}

/-- **The dimension of `H(A, B)`**: `∏_s C(A_s + m, m)·C(B_s + m, m)`. -/
def dimH (m : ℕ) {TT : Finset (Fin n')} (A B : TT → ℤ) : ℕ :=
  ∏ s : TT, ((A s).toNat + m).choose m * ((B s).toNat + m).choose m

end DimH

/-! ## The means of the flat exceptional fraction (A-N12, A-N13 for the flat pieces) -/

section FlatMeans

open WeylCount

variable {n' : ℕ}

/-- **The segment mean bound** (I2, the output of layer 3, Theorem B): for every V-top `x` and every `B` in the
`b`-box, the sum of the bad share `κ_T(x)` over the `a`-coordinates owned by the segment of `x` (the tops whose
previous V-top is `x`, `s_x + 1` of them), the other coordinates frozen at any values in the window, is at most
`|W_A|^{s_x+1}·C_A·(s_x + 1)·N₁/Y`: the mean over the owned coordinates is at most `C_A·(s_x + 1)·N₁/Y`. -/
def SegMean (TT : Finset (Fin n')) (WA WB : Finset ℤ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ) (CA N₁ Y : ℝ) :
    Prop :=
  ∀ x ∈ vTops TT, ∀ B ∈ box WB, ∀ A₀ : TT → ℤ, (∀ y : TT, prevV TT y ≠ x → A₀ y ∈ WA) →
    ∑ A ∈ Fintype.piFinset (fun y : TT => if prevV TT y = x then WA else {A₀ y}), κT x A B ≤
      (WA.card : ℝ) ^ (univ.filter fun y : TT => prevV TT y = x).card *
        (CA * (univ.filter fun y : TT => prevV TT y = x).card * N₁ / Y)


/-- **Summing over a window of shifts**: `Σ_{i ∈ [0, J] ⊂ ℤ} F(i.toNat) = Σ_{i < J + 1} F(i)`. -/
theorem sum_Icc_toNat (J : ℕ) (F : ℕ → ℝ) : ∑ i ∈ Icc (0 : ℤ) J, F i.toNat = ∑ i ∈ range (J + 1), F i := by
  refine sum_nbij' (fun i => i.toNat) (fun i => (i : ℤ)) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    (fun i _ => by simp) (fun i _ => rfl)
  · rw [mem_Icc] at hi
    rw [mem_range]
    omega
  · rw [mem_range] at hi
    rw [mem_Icc]
    omega
  · rw [mem_Icc] at hi
    simp [hi.1]

/-- **Averaging the key inequality over the shifts** (A-N12 for the flat pieces): if on the big box (all coordinates
`≥ J`) `Σ_{j ∈ [0, J]^{TT}} f(A − j, B − j)·∏_s Har_m(A_s − j_s, B_s − j_s) ≤ κ_X(A, B)·dim H(A, B)`, the shifts of the
small box stay in the big box and `Σ_{i ≤ J} ρ(α, β, i) ≥ δ₁ ≥ 0` on the small windows, then
`δ₁^N·Σ_small f ≤ Σ_big κ_X` (`boxSum_le_of_key` with the weights `w = ∏_s ρ(α_s, β_s, j_s)`, which are the key
inequality divided by `dim H(A, B) = ∏_s C(A_s + m, m)·C(B_s + m, m)`). -/
theorem boxSum_le_of_har {TT : Finset (Fin n')} {m : ℕ} {Sa Sb Ba Bb : Finset ℤ} {J : ℕ}
    (f κX : (TT → ℤ) → (TT → ℤ) → ℝ) (hf : ∀ α β, 0 ≤ f α β) {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hBa : ∀ x ∈ Ba, (J : ℤ) ≤ x) (hBb : ∀ x ∈ Bb, (J : ℤ) ≤ x)
    (hsa : ∀ x ∈ Sa, ∀ i ∈ Icc 0 (J : ℤ), x + i ∈ Ba) (hsb : ∀ x ∈ Sb, ∀ i ∈ Icc 0 (J : ℤ), x + i ∈ Bb)
    (hkey : ∀ A ∈ box Ba, ∀ B ∈ box Bb, ∑ jh ∈ box (Icc 0 (J : ℤ)), f (A - jh) (B - jh) *
      (∏ s, har m (A s - jh s).toNat (B s - jh s).toNat : ℕ) ≤ κX A B * dimH m A B)
    (hdens : ∀ α ∈ Sa, ∀ β ∈ Sb, δ₁ ≤ ∑ i ∈ range (J + 1), rho m α.toNat β.toNat i) :
    δ₁ ^ TT.card * boxSum Sa Sb f ≤ boxSum Ba Bb κX := by
  have hcardT : Fintype.card TT = TT.card := Fintype.card_coe TT
  refine boxSum_le_of_key (𝒥 := box (Icc 0 (J : ℤ))) f κX
    (fun α β jh => ∏ s, rho m (α s).toNat (β s).toNat (jh s).toNat) hf
    (fun α β jh => Finset.prod_nonneg fun s _ => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (fun α hα β hβ jh hjh => ⟨mem_box.2 fun s => hsa _ (mem_box.1 hα s) _ (mem_box.1 hjh s),
      mem_box.2 fun s => hsb _ (mem_box.1 hβ s) _ (mem_box.1 hjh s)⟩) (fun A hA B hB => ?_)
    (fun α hα β hβ => ?_)
  · -- the key inequality divided by `dim H(A, B)`
    have hpos : (0 : ℝ) < dimH m A B := by
      unfold dimH
      push_cast
      exact Finset.prod_pos fun s _ => mul_pos (by exact_mod_cast Nat.choose_pos (by omega))
        (by exact_mod_cast Nat.choose_pos (by omega))
    have h := hkey A hA B hB
    rw [← div_le_iff₀ hpos, Finset.sum_div] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun jh hjh => ?_)) h
    have hj : ∀ s, 0 ≤ jh s ∧ jh s ≤ J := fun s => mem_Icc.1 (mem_box.1 hjh s)
    rw [mul_div_assoc]
    congr 1
    unfold dimH
    push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hA' := hBa _ (mem_box.1 hA s)
    have hB' := hBb _ (mem_box.1 hB s)
    simp only [Pi.sub_apply, rho]
    rw [show (A s - jh s).toNat + (jh s).toNat = (A s).toNat by have := hj s; omega,
      show (B s - jh s).toNat + (jh s).toNat = (B s).toNat by have := hj s; omega]
  · -- the density over the tops
    have h := prod_univ_sum (fun _ : TT => Icc (0 : ℤ) J) fun s i => rho m (α s).toNat (β s).toNat i.toNat
    rw [← h, ← hcardT, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => hδ₁) fun s _ => ?_
    rw [sum_Icc_toNat J (rho m (α s).toNat (β s).toNat)]
    exact hdens _ (mem_box.1 hα s) _ (mem_box.1 hβ s)

/-- **Box sums of sums** are sums of box sums. -/
theorem boxSum_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] (Wa Wb : Finset ℤ) (X : Finset κ)
    (F : κ → (ι → ℤ) → (ι → ℤ) → ℝ) :
    boxSum Wa Wb (fun A B => ∑ x ∈ X, F x A B) = ∑ x ∈ X, boxSum Wa Wb (F x) := by
  simp only [boxSum]
  calc ∑ A ∈ box (ι := ι) Wa, ∑ B ∈ box (ι := ι) Wb, ∑ x ∈ X, F x A B =
        ∑ A ∈ box (ι := ι) Wa, ∑ x ∈ X, ∑ B ∈ box (ι := ι) Wb, F x A B :=
        Finset.sum_congr rfl fun A _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- **The segments own each top once**: `Σ_{V-tops x} #{y : y′ = x} ≤ N`. -/
theorem sum_card_own_le (TT : Finset (Fin n')) :
    ∑ x ∈ vTops TT, ((univ.filter fun y : TT => prevV TT y = x).card : ℝ) ≤ TT.card := by
  have h := card_eq_sum_card_fiberwise (f := fun y : TT => prevV TT y) (s := univ) (t := univ)
    fun _ _ => mem_univ _
  rw [card_univ, Fintype.card_coe] at h
  rw [h]
  push_cast
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _

/-- **The mean of `κ_X`** (A-N13): with the segment mean bound (I2), the box sum of `κ_X = κ_P + Σ_x κ_T(x)` over the
enlarged box is at most `|W_A|^N·|W_B|^N·(κ_P + C_A·N·N₁/Y)`: each `κ_T(x)` has its mean over the owned coordinates
(`sum_box_le_of_marginal`), and the segments own each top once (`sum_card_own_le`). -/
theorem boxSum_kappaX_le {TT : Finset (Fin n')} {WA WB : Finset ℤ} {κP CA N₁ Y : ℝ}
    {κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ} (hseg : SegMean TT WA WB κT CA N₁ Y) (hCA : 0 ≤ CA * N₁ / Y) :
    boxSum WA WB (fun A B => κP + ∑ x ∈ vTops TT, κT x A B) ≤
      (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card * (κP + CA * TT.card * N₁ / Y) := by
  have hcardT : Fintype.card TT = TT.card := Fintype.card_coe TT
  rw [boxSum_add, boxSum_const, boxSum_sum, hcardT]
  have hx : ∀ x ∈ vTops TT, boxSum WA WB (κT x) ≤ (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card *
      (CA * N₁ / Y * (univ.filter fun y : TT => prevV TT y = x).card) := by
    intro x hxv
    unfold boxSum
    rw [Finset.sum_comm]
    calc ∑ B ∈ box WB, ∑ A ∈ box WA, κT x A B
        ≤ ∑ _B ∈ box (ι := TT) WB, (WA.card : ℝ) ^ Fintype.card TT *
          (CA * (univ.filter fun y : TT => prevV TT y = x).card * N₁ / Y) :=
          sum_le_sum fun B hB => sum_box_le_of_marginal (fun y : TT => prevV TT y = x) WA (fun A => κT x A B) _
            fun A₀ hA₀ => hseg x hxv B hB A₀ hA₀
      _ = _ := by
        rw [sum_const, card_box, hcardT, nsmul_eq_mul]
        push_cast
        ring
  calc (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card * κP + ∑ x ∈ vTops TT, boxSum WA WB (κT x)
      ≤ (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card * κP + ∑ x ∈ vTops TT,
          (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card *
            (CA * N₁ / Y * (univ.filter fun y : TT => prevV TT y = x).card) := by
        gcongr with x hx'
        exact hx x hx'
    _ ≤ (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card * κP +
          (WA.card : ℝ) ^ TT.card * (WB.card : ℝ) ^ TT.card * (CA * N₁ / Y * TT.card) := by
        rw [← mul_sum, ← mul_sum]
        gcongr
        exact sum_card_own_le TT
    _ = _ := by ring

end FlatMeans

/-! ## The numerics of the first theorem (A-N20) -/

section Numerics

/-- **The shift window** `J = ⌊La·b′/k⌋`, `La = C₀N₁²·log a`. -/
def Jsh (C₀ : ℝ) (N₁ k : ℕ) (a b' : ℝ) : ℕ := ⌊C₀ * N₁ ^ 2 * Real.log a * b' / k⌋₊

/-- **The enlarged `a`-window** `[⌈a⌉ − c, ⌊a + a/(kY)⌋ + c + J]`. -/
def WAp (k : ℕ) (Y a : ℝ) (c J : ℕ) : Finset ℤ := Icc (⌈a⌉ - c) (⌊a + a / (k * Y)⌋ + c + J)

/-- **The enlarged `b`-window** `[⌈b_ℓ⌉ − c, ⌊b_u⌋ + c + J]`. -/
def WBp (bl bu : ℝ) (c J : ℕ) : Finset ℤ := Icc (⌈bl⌉ - c) (⌊bu⌋ + c + J)

/-- **`λ_a = log_p(8a + k) + 1`**, the logarithm of the denominators. -/
def lamA (p k : ℕ) (a : ℝ) : ℝ := Real.logb p (8 * a + k) + 1

/-- **The input denominator** `D₀ = ⌊C_I·N·Y²·N₁²·k²·λ_a⌋`. -/
def D0 (CI : ℝ) (N : ℕ) (Y : ℝ) (N₁ k : ℕ) (lam : ℝ) : ℕ := ⌊CI * N * Y ^ 2 * N₁ ^ 2 * k ^ 2 * lam⌋₊

/-- **The harmonic exponent** `u = N·⌈(k + 1)·λ_a⌉`. -/
def uH (N k : ℕ) (lam : ℝ) : ℕ := N * ⌈((k : ℝ) + 1) * lam⌉₊

/-- **The cloud exponent** `D_c = N·⌈k²·λ_a⌉`. -/
def Dcl (N k : ℕ) (lam : ℝ) : ℕ := N * ⌈(k : ℝ) ^ 2 * lam⌉₊

variable {C₀ CH : ℝ} {p n' k : ℕ} {TT : Finset (Fin n')} {G' N₁ : ℕ} {Y Yb a b' bl bu : ℝ} {c D cStar : ℕ}

/-- **The basic consequences of the numeric hypotheses** (for `C₀ ≥ 1`, `C_H ≥ 12`): `N ≥ 2`, `k ≥ 5`, `p ≥ 25`,
`Q ≥ 1`, `b′ ≥ 8C_H·k³·N·Y`, `b′ ≥ C_H·kNcY`, `pb′ < a`, `log a ≥ 1`, `N₁² ≤ La`, `La ≥ 1`, `N₁² ≤ k`,
`La·b′/k ≤ b′/(2C_H·N)`, `b_ℓ ≥ b′/2`, `b_u ≤ 3b′/2`, `N₁ ≥ 1`, `b′ ≥ 1`. -/
theorem FirstHyp.base (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) :
    (2 : ℝ) ≤ TT.card ∧ (5 : ℝ) ≤ k ∧ (25 : ℝ) ≤ p ∧ (1 : ℝ) ≤ (p : ℝ) ^ G' ∧ 0 < b' ∧
      8 * CH * (k : ℝ) ^ 3 * TT.card * Y ≤ b' ∧ CH * (k : ℝ) * TT.card * c * Y ≤ b' ∧ (p : ℝ) * b' < a ∧
      1 ≤ Real.log a ∧ (N₁ : ℝ) ^ 2 ≤ C₀ * N₁ ^ 2 * Real.log a ∧ (1 : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a ∧
      (N₁ : ℝ) ^ 2 ≤ k ∧ C₀ * N₁ ^ 2 * Real.log a * b' / k ≤ b' / (2 * CH * TT.card) ∧
      b' / 2 ≤ bl ∧ bu ≤ 3 * b' / 2 ∧ (1 : ℝ) ≤ N₁ ∧ (1 : ℝ) ≤ b' := by
  have hN2 : (2 : ℝ) ≤ TT.card := by exact_mod_cast h.seg.1.trans (card_filter_le _ _)
  have hN₁ : (1 : ℝ) ≤ N₁ := by exact_mod_cast h.N₁_pos
  have hk5 : (5 : ℝ) ≤ k := by have := h.k_ge; have := h.N₁_pos; exact_mod_cast (by omega : 5 ≤ k)
  have hY := h.Y_ge
  have hp25 : (25 : ℝ) ≤ p := by
    have hk2 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hY2 : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
    calc (25 : ℝ) = 25 * 1 := by ring
      _ ≤ (k : ℝ) ^ 2 * Y ^ 2 := mul_le_mul hk2 hY2 (by norm_num) (by positivity)
      _ ≤ p := h.p_ge
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ G' := one_le_pow₀ (by linarith)
  have hb'0 := h.b_win.1
  have hcs : (8 : ℝ) ≤ cStar := by have := h.cStar_ge; exact_mod_cast (by omega : 8 ≤ cStar)
  have hbig := h.b'_big
  have hNc : (0 : ℝ) ≤ TT.card * c := by positivity
  have hnc : (0 : ℝ) ≤ n' * c := by positivity
  have hS8 : (8 : ℝ) ≤ cStar + TT.card * c + n' * c := by linarith
  have hQ4 : (1 : ℝ) ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hk3 : (k : ℝ) ≤ (k : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hpos : 0 ≤ CH * (k : ℝ) ^ 3 * TT.card * Y := by positivity
  have hQS : (8 : ℝ) ≤ ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) := by
    calc (8 : ℝ) = 1 * 8 := by ring
      _ ≤ ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) := mul_le_mul hQ4 hS8 (by norm_num) (by positivity)
  have hb1 : 8 * CH * (k : ℝ) ^ 3 * TT.card * Y ≤ b' := by
    calc 8 * CH * (k : ℝ) ^ 3 * TT.card * Y = (CH * (k : ℝ) ^ 3 * TT.card * Y) * 8 := by ring
      _ ≤ (CH * (k : ℝ) ^ 3 * TT.card * Y) * (((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c)) :=
          mul_le_mul_of_nonneg_left hQS hpos
      _ = CH * (k : ℝ) ^ 3 * TT.card * ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) * Y := by ring
      _ ≤ b' := hbig
  have hb2 : CH * (k : ℝ) * TT.card * c * Y ≤ b' := by
    have hcS : (c : ℝ) ≤ ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) := by
      have h1 : (c : ℝ) ≤ TT.card * c := le_mul_of_one_le_left (Nat.cast_nonneg c) (by linarith)
      have h2 : (c : ℝ) ≤ cStar + TT.card * c + n' * c := by
        linarith [(Nat.cast_nonneg cStar : (0 : ℝ) ≤ cStar)]
      exact h2.trans (le_mul_of_one_le_left (by positivity) hQ4)
    have h1 : (k : ℝ) * c ≤ (k : ℝ) ^ 3 * (((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c)) :=
      mul_le_mul hk3 hcS (Nat.cast_nonneg c) (by positivity)
    have h2 : 0 ≤ CH * TT.card * Y := by positivity
    calc CH * (k : ℝ) * TT.card * c * Y = (CH * TT.card * Y) * ((k : ℝ) * c) := by ring
      _ ≤ (CH * TT.card * Y) * ((k : ℝ) ^ 3 * (((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c))) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = CH * (k : ℝ) ^ 3 * TT.card * ((p : ℝ) ^ G') ^ 4 * (cStar + TT.card * c + n' * c) * Y := by ring
      _ ≤ b' := hbig
  have hpa : (p : ℝ) * b' < a := by have := h.p_lt; rwa [lt_div_iff₀ hb'0] at this
  have hb'1 : (1 : ℝ) ≤ b' := by
    have h1 : (1 : ℝ) ≤ 8 * CH := by linarith
    have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have h3 : (1 : ℝ) ≤ 8 * CH * (k : ℝ) ^ 3 := one_le_mul_of_one_le_of_one_le h1 h2
    have h4 : (1 : ℝ) ≤ 8 * CH * (k : ℝ) ^ 3 * TT.card := one_le_mul_of_one_le_of_one_le h3 (by linarith)
    have h5 : (1 : ℝ) ≤ 8 * CH * (k : ℝ) ^ 3 * TT.card * Y := one_le_mul_of_one_le_of_one_le h4 hY
    linarith
  have ha3 : (3 : ℝ) ≤ a := by
    have : (25 : ℝ) * 1 ≤ p * b' := mul_le_mul hp25 hb'1 (by norm_num) (by linarith)
    linarith
  have hloga : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLaN : (N₁ : ℝ) ^ 2 ≤ C₀ * N₁ ^ 2 * Real.log a := by
    have h1 : (N₁ : ℝ) ^ 2 * 1 ≤ N₁ ^ 2 * Real.log a := mul_le_mul_of_nonneg_left hloga (by positivity)
    have h2 : (N₁ : ℝ) ^ 2 * Real.log a ≤ C₀ * (N₁ ^ 2 * Real.log a) :=
      le_mul_of_one_le_left (by positivity) hC₀
    linarith [mul_assoc C₀ ((N₁ : ℝ) ^ 2) (Real.log a)]
  have hN₁2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ 2 := one_le_pow₀ hN₁
  have hLa1 : (1 : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a := hN₁2.trans hLaN
  have hN₁k : (N₁ : ℝ) ^ 2 ≤ k := by
    have hLsq := h.La_sq
    have h1 : (N₁ : ℝ) ^ 2 ≤ (C₀ * N₁ ^ 2 * Real.log a) ^ 2 :=
      hLaN.trans (le_self_pow₀ hLa1 (by norm_num))
    have h2 : (C₀ * N₁ ^ 2 * Real.log a) ^ 2 ≤ CH * TT.card * (C₀ * N₁ ^ 2 * Real.log a) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
    linarith
  have hLak : C₀ * N₁ ^ 2 * Real.log a * b' / k ≤ b' / (2 * CH * TT.card) := by
    have h1 := h.Yb_ge
    have hLa0 : (0 : ℝ) ≤ TT.card * (C₀ * N₁ ^ 2 * Real.log a) := by positivity
    have h2 : 2 * CH * TT.card * (C₀ * N₁ ^ 2 * Real.log a) ≤ k := by
      have : 2 * CH * (TT.card * (C₀ * N₁ ^ 2 * Real.log a)) ≤ 2 * Yb * (TT.card * (C₀ * N₁ ^ 2 * Real.log a)) :=
        mul_le_mul_of_nonneg_right (by linarith [h1.1]) hLa0
      have e1 : 2 * CH * TT.card * (C₀ * N₁ ^ 2 * Real.log a) =
        2 * CH * (TT.card * (C₀ * N₁ ^ 2 * Real.log a)) := by ring
      have e2 : 2 * Yb * TT.card * (C₀ * N₁ ^ 2 * Real.log a) =
        2 * Yb * (TT.card * (C₀ * N₁ ^ 2 * Real.log a)) := by ring
      linarith [h1.2]
    have hk0 : (0 : ℝ) < k := by linarith
    rw [div_le_div_iff₀ hk0 (by positivity)]
    have := mul_le_mul_of_nonneg_left h2 hb'0.le
    linarith [mul_comm b' (2 * CH * TT.card * (C₀ * N₁ ^ 2 * Real.log a))]
  have hbl : b' / 2 ≤ bl := by have := h.b_win; linarith [this.2.2.2.2, this.2.2.1]
  have hbu : bu ≤ 3 * b' / 2 := by have := h.b_win; linarith [this.2.2.2.2, this.2.1]
  exact ⟨hN2, hk5, hp25, hQ, hb'0, hb1, hb2, hpa, hloga, hLaN, hLa1, hN₁k, hLak, hbl, hbu, hN₁, hb'1⟩

/-- **The shift window is small**: `J + c ≤ b′/24`, `J ≤ La·b′/k` (for `C_H ≥ 12`). -/
theorem FirstHyp.J_le (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) :
    (Jsh C₀ N₁ k a b' : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a * b' / k ∧ (Jsh C₀ N₁ k a b' : ℝ) + c ≤ b' / 24 := by
  obtain ⟨hN2, hk5, -, -, hb'0, -, -, -, -, -, hLa1, -, hLak, -, -, -, -⟩ := h.base hC₀ hCH
  have hJ : (Jsh C₀ N₁ k a b' : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a * b' / k := Nat.floor_le (by positivity)
  have hc := h.cloud
  have h48 : b' / (2 * CH * TT.card) ≤ b' / 48 :=
    div_le_div_of_nonneg_left hb'0.le (by norm_num) (by nlinarith)
  refine ⟨hJ, ?_⟩
  have : (c : ℝ) ≤ C₀ * N₁ ^ 2 * Real.log a * b' / k := by rw [mul_div_assoc] at hc ⊢; linarith [hc]
  linarith

/-- **The enlarged windows** (for `C_H ≥ 12`): their entries are `≥ J`, and `A + B + 1 ≤ 8a` on them. -/
theorem FirstHyp.winP (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) :
    (∀ x ∈ WAp k Y a c (Jsh C₀ N₁ k a b'), (Jsh C₀ N₁ k a b' : ℤ) ≤ x) ∧
      (∀ x ∈ WBp bl bu c (Jsh C₀ N₁ k a b'), (Jsh C₀ N₁ k a b' : ℤ) ≤ x) ∧
      ∀ A ∈ WAp k Y a c (Jsh C₀ N₁ k a b'), ∀ B ∈ WBp bl bu c (Jsh C₀ N₁ k a b'),
        ((A + B + 1 : ℤ) : ℝ) ≤ 8 * a := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, -, -, hpa, -, -, -, -, -, hbl, hbu, -, hb'1⟩ := h.base hC₀ hCH
  obtain ⟨-, hJc⟩ := h.J_le hC₀ hCH
  have hab : 25 * b' ≤ a := by nlinarith
  have hkY : (1 : ℝ) ≤ k * Y := one_le_mul_of_one_le_of_one_le (by linarith) h.Y_ge
  have hakY : a / (k * Y) ≤ a := div_le_self (by linarith) hkY
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun A hA B hB => ?_⟩
  · have h1 := (mem_Icc.1 hx).1
    have h2 : ((⌈a⌉ - c : ℤ) : ℝ) ≤ x := by exact_mod_cast h1
    have h3 := Int.le_ceil a
    push_cast at h2
    have : (Jsh C₀ N₁ k a b' : ℝ) ≤ x := by linarith
    exact_mod_cast this
  · have h1 := (mem_Icc.1 hx).1
    have h2 : ((⌈bl⌉ - c : ℤ) : ℝ) ≤ x := by exact_mod_cast h1
    have h3 := Int.le_ceil bl
    push_cast at h2
    have : (Jsh C₀ N₁ k a b' : ℝ) ≤ x := by linarith
    exact_mod_cast this
  · have h1 : (A : ℝ) ≤ ((⌊a + a / (k * Y)⌋ + c + Jsh C₀ N₁ k a b' : ℤ) : ℝ) := by exact_mod_cast (mem_Icc.1 hA).2
    have h2 : (B : ℝ) ≤ ((⌊bu⌋ + c + Jsh C₀ N₁ k a b' : ℤ) : ℝ) := by exact_mod_cast (mem_Icc.1 hB).2
    have h3 := Int.floor_le (a + a / (k * Y))
    have h4 := Int.floor_le bu
    push_cast at h1 h2 ⊢
    have : (1 : ℝ) ≤ a := by linarith
    linarith

/-- **The cloud's side conditions** (for `C_H ≥ 108`): on the box, `b′/3 ≤ a_s − c, b_s − c`,
`(a_s − c) + (b_s − c) + 4c + 1 ≤ 8a`, and `ε = 12Nkc/b′ ≤ min(1/9, 1/Y)`. -/
theorem FirstHyp.cloudCond (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 108 ≤ CH) :
    (∀ x ∈ aWin k Y a, ∀ y ∈ bWin bl bu, b' / 3 ≤ ((x - c : ℤ) : ℝ) ∧ b' / 3 ≤ ((y - c : ℤ) : ℝ) ∧
      (((x - c) + (y - c) + 4 * c + 1 : ℤ) : ℝ) ≤ 8 * a) ∧
      12 * (TT.card : ℝ) * k * c / b' ≤ 1 / 9 ∧ 12 * (TT.card : ℝ) * k * c / b' ≤ 1 / Y := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, -, hb2, hpa, -, -, -, -, -, hbl, hbu, -, hb'1⟩ := h.base hC₀ (by linarith)
  obtain ⟨-, hJc⟩ := h.J_le hC₀ (by linarith)
  have hab : 25 * b' ≤ a := by nlinarith
  have hkY : (1 : ℝ) ≤ k * Y := one_le_mul_of_one_le_of_one_le (by linarith) h.Y_ge
  have hakY : a / (k * Y) ≤ a := div_le_self (by linarith) hkY
  have hc : (c : ℝ) ≤ b' / 24 := by linarith [(Nat.cast_nonneg (Jsh C₀ N₁ k a b') : (0 : ℝ) ≤ _)]
  have hY := h.Y_ge
  have hε : 12 * (TT.card : ℝ) * k * c / b' ≤ 12 / (CH * Y) := by
    rw [div_le_div_iff₀ hb'0 (by positivity)]
    nlinarith
  refine ⟨fun x hx y hy => ?_, hε.trans ?_, hε.trans ?_⟩
  · have hx1 : (⌈a⌉ : ℝ) ≤ x := by exact_mod_cast (mem_Icc.1 hx).1
    have hx2 : (x : ℝ) ≤ ⌊a + a / (k * Y)⌋ := by exact_mod_cast (mem_Icc.1 hx).2
    have hy1 : (⌈bl⌉ : ℝ) ≤ y := by exact_mod_cast (mem_Icc.1 hy).1
    have hy2 : (y : ℝ) ≤ ⌊bu⌋ := by exact_mod_cast (mem_Icc.1 hy).2
    have := Int.le_ceil a
    have := Int.le_ceil bl
    have := Int.floor_le (a + a / (k * Y))
    have := Int.floor_le bu
    push_cast
    refine ⟨by linarith, by linarith, by linarith⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith

/-- **The denominators fit** (for `C_I ≥ 0`, `C_H ≥ 6C_I + 108`): `2(D₀ + 2u) + D_c ≤ D`, as
`D₀ + u + D_c ≤ (C_I + 5)·N·Y²·N₁²·k²·λ_a`, `N₁² ≤ k` and `λ_a ≤ 3·log_p a`. -/
theorem FirstHyp.den (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀) {CI : ℝ}
    (hCI : 0 ≤ CI) (hCH : 6 * CI + 108 ≤ CH) :
    2 * (D0 CI TT.card Y N₁ k (lamA p k a) + 2 * uH TT.card k (lamA p k a)) + Dcl TT.card k (lamA p k a) ≤ D := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, hb1, -, hpa, -, -, -, hN₁k, -, -, -, hN₁, hb'1⟩ := h.base hC₀ (by linarith)
  have hY := h.Y_ge
  have hp1 : (1 : ℝ) < p := by linarith
  have hab : 25 * b' ≤ a := by nlinarith
  have hkb : (k : ℝ) ≤ b' := by
    have : (1 : ℝ) ≤ 8 * CH * (k : ℝ) ^ 2 * TT.card * Y := by
      have h1 : (1 : ℝ) ≤ 8 * CH := by linarith
      have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h1 h2) (by linarith)) hY
    nlinarith
  have hlam1 : 1 ≤ lamA p k a := by
    have : 0 ≤ Real.logb p (8 * a + k) := Real.logb_nonneg hp1 (by linarith)
    unfold lamA; linarith
  have hla1 : 1 ≤ Real.logb p a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]
    nlinarith
  have hlam3 : lamA p k a ≤ 3 * Real.logb p a := by
    have h1 : Real.logb p (8 * a + k) ≤ Real.logb p (a ^ 2) :=
      Real.logb_le_logb_of_le hp1 (by linarith) (by nlinarith)
    rw [Real.logb_pow] at h1
    unfold lamA
    push_cast at h1
    linarith
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = lamA p k a := ⟨_, rfl⟩
  rw [← hlam] at hlam1 hlam3 ⊢
  have hl0 : 0 ≤ lam := by linarith
  have hD0 : (D0 CI TT.card Y N₁ k lam : ℝ) ≤ CI * TT.card * Y ^ 2 * N₁ ^ 2 * k ^ 2 * lam :=
    Nat.floor_le (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCI (Nat.cast_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)) hl0)
  have hu : (uH TT.card k lam : ℝ) ≤ TT.card * (((k : ℝ) + 1) * lam + 1) := by
    unfold uH
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hl0)).le (by positivity)
  have hDc : (Dcl TT.card k lam : ℝ) ≤ TT.card * ((k : ℝ) ^ 2 * lam + 1) := by
    unfold Dcl
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hl0)).le (by positivity)
  -- the main term
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = TT.card * Y ^ 2 * N₁ ^ 2 * k ^ 2 * lam := ⟨_, rfl⟩
  have hY2 : (1 : ℝ) ≤ Y ^ 2 := one_le_pow₀ hY
  have hN₁2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ 2 := one_le_pow₀ hN₁
  have hNk : (TT.card : ℝ) * k ^ 2 * lam ≤ P := by
    rw [hPdef]
    have h1 : (1 : ℝ) ≤ Y ^ 2 * N₁ ^ 2 := one_le_mul_of_one_le_of_one_le hY2 hN₁2
    have h2 : (0 : ℝ) ≤ TT.card * k ^ 2 * lam := by positivity
    calc (TT.card : ℝ) * k ^ 2 * lam = (TT.card * k ^ 2 * lam) * 1 := by ring
      _ ≤ (TT.card * k ^ 2 * lam) * (Y ^ 2 * N₁ ^ 2) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have hk2 : (k : ℝ) + 2 ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
  have hkk : ((k : ℝ) + 1) * lam + 1 ≤ 2 * (k : ℝ) ^ 2 * lam := by
    have := mul_le_mul_of_nonneg_right hk2 hl0
    nlinarith
  have hk1 : (k : ℝ) ^ 2 * lam + 1 ≤ 2 * (k : ℝ) ^ 2 * lam := by
    have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hsum : (2 * (D0 CI TT.card Y N₁ k lam + 2 * uH TT.card k lam) + Dcl TT.card k lam : ℝ) ≤
      (2 * CI + 10) * P := by
    have e1 : CI * TT.card * Y ^ 2 * N₁ ^ 2 * k ^ 2 * lam = CI * P := by rw [hPdef]; ring
    have h4 : (TT.card : ℝ) * (((k : ℝ) + 1) * lam + 1) ≤ 2 * P := by
      have := mul_le_mul_of_nonneg_left hkk (Nat.cast_nonneg TT.card)
      linarith [mul_assoc (TT.card : ℝ) 2 ((k : ℝ) ^ 2 * lam)]
    have h5 : (TT.card : ℝ) * ((k : ℝ) ^ 2 * lam + 1) ≤ 2 * P := by
      have := mul_le_mul_of_nonneg_left hk1 (Nat.cast_nonneg TT.card)
      linarith [mul_assoc (TT.card : ℝ) 2 ((k : ℝ) ^ 2 * lam)]
    rw [e1] at hD0
    linarith
  have hP : P ≤ TT.card * Y ^ 2 * (k : ℝ) ^ 3 * (3 * Real.logb p a) := by
    rw [hPdef]
    have h1 : (N₁ : ℝ) ^ 2 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hN₁k (sq_nonneg (k : ℝ))
      linarith [pow_succ (k : ℝ) 2]
    have h2 : (0 : ℝ) ≤ TT.card * Y ^ 2 := by positivity
    calc (TT.card : ℝ) * Y ^ 2 * N₁ ^ 2 * k ^ 2 * lam = (TT.card * Y ^ 2) * ((N₁ : ℝ) ^ 2 * k ^ 2) * lam := by ring
      _ ≤ (TT.card * Y ^ 2) * (k : ℝ) ^ 3 * (3 * Real.logb p a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 h2) hlam3 hl0 (by positivity)
      _ = _ := by ring
  have hD := h.D_ge
  have hfin : (2 * CI + 10) * (TT.card * Y ^ 2 * (k : ℝ) ^ 3 * (3 * Real.logb p a)) ≤
      CH * TT.card * Y ^ 2 * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * Real.logb p a := by
    have h1 : (0 : ℝ) ≤ TT.card * Y ^ 2 * Real.logb p a := by positivity
    have h2 : (k : ℝ) ^ 3 ≤ (N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3 := by
      linarith [pow_nonneg (Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁) 5]
    have h3 : 3 * (2 * CI + 10) ≤ CH := by linarith
    calc (2 * CI + 10) * (TT.card * Y ^ 2 * (k : ℝ) ^ 3 * (3 * Real.logb p a))
        = (3 * (2 * CI + 10)) * (k : ℝ) ^ 3 * (TT.card * Y ^ 2 * Real.logb p a) := by ring
      _ ≤ CH * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * (TT.card * Y ^ 2 * Real.logb p a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h3 h2 (by positivity) (by linarith)) h1
      _ = _ := by ring
  have h6 := mul_le_mul_of_nonneg_left hP (by linarith : (0 : ℝ) ≤ 2 * CI + 10)
  have : (2 * (D0 CI TT.card Y N₁ k lam + 2 * uH TT.card k lam) + Dcl TT.card k lam : ℝ) ≤ D := by
    linarith
  exact_mod_cast this

/-- **`x/(x + m)` is monotone** for `m > 0` on `x ≥ 0`. -/
theorem div_add_le_div_add {m x y : ℝ} (hm : 0 < m) (hx : 0 ≤ x) (hxy : x ≤ y) : x / (x + m) ≤ y / (y + m) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hxy hm.le]

/-- **The density of the flat pieces at the first theorem's windows**: `δ₁ = 1 − (β*/(β* + m))^{J+1}`,
`β* = ⌊b_u⌋ + c`, `m = k − 1`. -/
def deltaF (k : ℕ) (bu : ℝ) (c J : ℕ) : ℝ :=
  1 - (((⌊bu⌋ + c : ℤ) : ℝ) / (((⌊bu⌋ + c : ℤ) : ℝ) + ((k - 1 : ℕ) : ℝ))) ^ (J + 1)

/-- **The density bound** (A-N20, for `C_H ≥ 12`): `δ₁ ≥ 0` and `δ₁^N ≥ 3/4`, as
`(β*/(β* + m))^{J+1} ≤ e^{−(J+1)m/(β*+m)} ≤ e^{−2La/5} ≤ (NY)^{−3}` (`J + 1 ≥ La·b′/k`, `m ≥ 4k/5`,
`β* + m ≤ 2b′`, `La ≥ 8·log(NY)`), and Bernoulli. -/
theorem FirstHyp.dens (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) :
    0 ≤ deltaF k bu c (Jsh C₀ N₁ k a b') ∧ 3 / 4 ≤ deltaF k bu c (Jsh C₀ N₁ k a b') ^ TT.card := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, hb1, -, -, -, -, hLa1, -, hLak, hbl, hbu, -, hb'1⟩ := h.base hC₀ hCH
  obtain ⟨hJ, hJc⟩ := h.J_le hC₀ hCH
  have hY := h.Y_ge
  have hk1 : 1 ≤ k - 1 := by
    have : (5 : ℝ) ≤ k := hk5
    have : 5 ≤ k := by exact_mod_cast this
    omega
  have hm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
  obtain ⟨J, hJdef⟩ : ∃ J, J = Jsh C₀ N₁ k a b' := ⟨_, rfl⟩
  rw [← hJdef] at hJ hJc ⊢
  have hbu' := h.b_win.2.2.1
  have hfl0 : (0 : ℤ) ≤ ⌊bu⌋ := Int.floor_nonneg.2 (by linarith)
  obtain ⟨βs, hβs⟩ : ∃ βs : ℝ, βs = ((⌊bu⌋ + c : ℤ) : ℝ) := ⟨_, rfl⟩
  have hβs0 : 0 ≤ βs := by rw [hβs]; exact_mod_cast (by omega : (0 : ℤ) ≤ ⌊bu⌋ + c)
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ((k - 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hm' : m = (k : ℝ) - 1 := by rw [hmdef, hm]
  have hm0 : (0 : ℝ) < m := by rw [hm']; linarith
  have hr0 : 0 ≤ βs / (βs + m) := by positivity
  have hr1 : βs / (βs + m) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  unfold deltaF
  rw [← hβs, ← hmdef]
  refine ⟨by linarith [pow_le_one₀ hr0 hr1 (n := J + 1)], ?_⟩
  · -- `δ₁^N ≥ 3/4`
    have hx1 : m / (βs + m) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have hrw : βs / (βs + m) = 1 - m / (βs + m) := by field_simp; ring
    have hexp := one_sub_pow_le_exp hx1 (J + 1)
    rw [← hrw] at hexp
    -- `(J + 1)·m/(β* + m) ≥ 2La/5`
    have hJ1 : C₀ * N₁ ^ 2 * Real.log a * b' / k ≤ (J : ℝ) + 1 := by
      rw [hJdef]; exact (Nat.lt_floor_add_one _).le
    have hkb : (k : ℝ) ≤ b' / 8 := by
      have : (8 : ℝ) * k ≤ 8 * CH * (k : ℝ) ^ 3 * TT.card * Y := by
        have h1 : (1 : ℝ) ≤ CH * (k : ℝ) ^ 2 * TT.card * Y := by
          have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
          exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
            (one_le_mul_of_one_le_of_one_le (by linarith) h2) (by linarith)) hY
        nlinarith
      linarith
    have hβm : βs + m ≤ 2 * b' := by
      have h1 : βs ≤ bu + c := by
        rw [hβs]; push_cast; linarith [Int.floor_le bu]
      have h2 : m ≤ k := by rw [hm']; linarith
      linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    have hm45 : 4 / 5 * (k : ℝ) ≤ m := by rw [hm']; linarith
    have hkey : 2 * (C₀ * N₁ ^ 2 * Real.log a) / 5 ≤ ((J + 1 : ℕ) : ℝ) * (m / (βs + m)) := by
      push_cast
      have h1 : 4 / 5 * (k : ℝ) / (2 * b') ≤ m / (βs + m) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc 2 * (C₀ * N₁ ^ 2 * Real.log a) / 5 =
            (C₀ * N₁ ^ 2 * Real.log a * b' / k) * (4 / 5 * (k : ℝ) / (2 * b')) := by
            field_simp
            ring
        _ ≤ ((J : ℝ) + 1) * (m / (βs + m)) :=
            mul_le_mul hJ1 h1 (by positivity) (by positivity)
    have hNY : (1 : ℝ) ≤ TT.card * Y := one_le_mul_of_one_le_of_one_le (by linarith) hY
    have hlog : 0 ≤ Real.log (TT.card * Y) := Real.log_nonneg hNY
    have hLa := h.La_ge
    have hexp2 : Real.exp (-(((J + 1 : ℕ) : ℝ) * (m / (βs + m)))) ≤ ((TT.card * Y) ^ 3)⁻¹ := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < TT.card * Y), ← Real.exp_nat_mul, ← Real.exp_neg]
      exact Real.exp_le_exp.2 (by push_cast at hkey ⊢; nlinarith)
    have hsmall : (βs / (βs + m)) ^ (J + 1) ≤ ((TT.card * Y) ^ 3)⁻¹ := hexp.trans hexp2
    have hb := one_sub_mul_le_pow (x := (βs / (βs + m)) ^ (J + 1)) (by linarith [pow_le_one₀ hr0 hr1 (n := J + 1)])
      TT.card
    have hfin : (TT.card : ℝ) * ((TT.card * Y) ^ 3)⁻¹ ≤ 1 / 4 := by
      have h4 : 4 * (TT.card : ℝ) ≤ (TT.card * Y) ^ 3 := by
        have hN4 : (4 : ℝ) ≤ (TT.card : ℝ) ^ 2 := by nlinarith
        have hY3 : (1 : ℝ) ≤ Y ^ 3 := one_le_pow₀ hY
        calc 4 * (TT.card : ℝ) ≤ (TT.card : ℝ) ^ 2 * TT.card :=
              mul_le_mul_of_nonneg_right hN4 (by positivity)
          _ = (TT.card : ℝ) ^ 3 * 1 := by ring
          _ ≤ (TT.card : ℝ) ^ 3 * Y ^ 3 := mul_le_mul_of_nonneg_left hY3 (by positivity)
          _ = (TT.card * Y) ^ 3 := by ring
      rw [mul_inv_le_iff₀ (by positivity)]
      linarith only [h4]
    have hNs := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg TT.card)
    linarith only [hb, hNs, hfin]

/-- **The density at one top** (A-N12's hypothesis): `Σ_{i ≤ J} ρ(α, β, i) ≥ δ₁` for `0 ≤ β ≤ β* = ⌊b_u⌋ + c`, as
`ρ ≥ (1 − r₀)r₀^i` with `r₀ ≤ β/(β + m) ≤ β*/(β* + m)` (`one_sub_pow_le_sum_rho`, `rzero_le`). -/
theorem deltaF_le_sum {k : ℕ} (hk : 2 ≤ k) {bu : ℝ} {c J : ℕ} (hbu : 0 ≤ bu) (α β : ℤ) (hβ0 : 0 ≤ β)
    (hβ : β ≤ ⌊bu⌋ + c) : deltaF k bu c J ≤ ∑ i ∈ range (J + 1), rho (k - 1) α.toNat β.toNat i := by
  have hk1 : 1 ≤ k - 1 := by omega
  have hfl0 : (0 : ℤ) ≤ ⌊bu⌋ := Int.floor_nonneg.2 hbu
  obtain ⟨βs, hβs⟩ : ∃ βs : ℝ, βs = ((⌊bu⌋ + c : ℤ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ((k - 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hm0 : (0 : ℝ) < m := by rw [hmdef]; exact_mod_cast (by omega : 0 < k - 1)
  unfold deltaF
  rw [← hβs, ← hmdef]
  have hβ' : ((β.toNat : ℕ) : ℝ) = β := by exact_mod_cast Int.toNat_of_nonneg hβ0
  have hββ : ((β.toNat : ℕ) : ℝ) ≤ βs := by rw [hβ', hβs]; exact_mod_cast hβ
  have hr : rzero (k - 1) α.toNat β.toNat ≤ βs / (βs + m) := by
    refine (rzero_le (k - 1) α.toNat β.toNat).trans ?_
    rw [← hmdef]
    exact div_add_le_div_add hm0 (Nat.cast_nonneg _) hββ
  have hpow : rzero (k - 1) α.toNat β.toNat ^ (J + 1) ≤ (βs / (βs + m)) ^ (J + 1) :=
    pow_le_pow_left₀ (rzero_mem _ _ _).1 hr _
  linarith only [hpow, one_sub_pow_le_sum_rho hk1 α.toNat β.toNat J]

/-- **A small extension of a window**: `(w + e)^N ≤ 2w^N` when `w > 0`, `e ≥ 0` and `2Ne ≤ w`. -/
theorem pow_add_le_two_mul {w e : ℝ} (hw : 0 < w) (he : 0 ≤ e) {N : ℕ} (h : 2 * N * e ≤ w) :
    (w + e) ^ N ≤ 2 * w ^ N := by
  have hx : 0 ≤ e / w := div_nonneg he hw.le
  have hNx : N * (e / w) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hw]; linarith
  have h1 := one_add_pow_le_inv hx (N := N) (by linarith)
  have h2 : 1 / (1 - N * (e / w)) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  calc (w + e) ^ N = w ^ N * (1 + e / w) ^ N := by rw [← mul_pow]; congr 1; field_simp
    _ ≤ w ^ N * 2 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 2 * w ^ N := by ring

/-- **The box sizes** (A-N20, for `C_H ≥ 12`): the windows `I_a`, `I_b` are nonempty, and the enlarged windows
(by `2c + J`) have `|W_A|^N ≤ 2|I_a|^N`, `|W_B|^N ≤ 2|I_b|^N` (`pow_add_le_two_mul`: `|I_a| ≥ a/(2kY)`,
`|I_b| ≥ Ŷ·N·La·b′/(2k)` and `2N(2c + J) ≤ 6N·La·b′/k` is below both). -/
theorem FirstHyp.ratio (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) :
    0 < ((aWin k Y a).card : ℝ) ∧ 0 < ((bWin bl bu).card : ℝ) ∧
      ((WAp k Y a c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card ≤ 2 * ((aWin k Y a).card : ℝ) ^ TT.card ∧
      ((WBp bl bu c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card ≤ 2 * ((bWin bl bu).card : ℝ) ^ TT.card := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, hb1, -, -, hloga, -, hLa1, -, hLak, hbl, hbu, -, hb'1⟩ := h.base hC₀ hCH
  obtain ⟨hJ, hJc⟩ := h.J_le hC₀ hCH
  have hY := h.Y_ge
  obtain ⟨J, hJdef⟩ : ∃ J, J = Jsh C₀ N₁ k a b' := ⟨_, rfl⟩
  rw [← hJdef] at hJ hJc ⊢
  obtain ⟨La, hLadef⟩ : ∃ La, La = C₀ * N₁ ^ 2 * Real.log a := ⟨_, rfl⟩
  rw [← hLadef] at hJ hLa1 hLak
  have hc : (c : ℝ) ≤ La * b' / k := by have := h.cloud; rw [← hLadef] at this; rw [mul_div_assoc] at this ⊢; exact this
  have hk0 : (0 : ℝ) < k := by linarith
  have hkb : (k : ℝ) ≤ b' := by
    have : (1 : ℝ) ≤ 8 * CH * (k : ℝ) ^ 2 * TT.card * Y := by
      have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) h2) (by linarith)) hY
    nlinarith
  have hYb := h.Yb_ge
  have he : 2 * (TT.card : ℝ) * (2 * c + J) ≤ 6 * TT.card * (La * b' / k) := by
    have h1 : 2 * (c : ℝ) + J ≤ 3 * (La * b' / k) := by linarith
    calc 2 * (TT.card : ℝ) * (2 * c + J) ≤ 2 * (TT.card : ℝ) * (3 * (La * b' / k)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 6 * TT.card * (La * b' / k) := by ring
  -- the `a`-window
  have haBig := h.a_big
  rw [← hLadef] at haBig
  have hab : (k : ℝ) * Y ^ 2 * Yb * TT.card * La * Real.log a * b' ≤ a := by
    rwa [le_div_iff₀ hb'0] at haBig
  have hkY : (0 : ℝ) < k * Y := by positivity
  have hkY1 : (1 : ℝ) ≤ k * Y := one_le_mul_of_one_le_of_one_le (by linarith) hY
  have hYb12 : (12 : ℝ) ≤ Yb := by linarith [hYb.1]
  have h12 : (12 : ℝ) * TT.card * La * b' * Y ≤ a := by
    have h1 : (12 : ℝ) ≤ k * Y * Yb * Real.log a := by
      have h0 : (12 : ℝ) ≤ k * Y * Yb := by
        calc (12 : ℝ) = 1 * 12 := by ring
          _ ≤ (k * Y) * Yb := mul_le_mul hkY1 hYb12 (by norm_num) (by positivity)
      exact h0.trans (le_mul_of_one_le_right (by positivity) hloga)
    have h2 : (0 : ℝ) ≤ TT.card * La * b' * Y := by positivity
    calc (12 : ℝ) * TT.card * La * b' * Y = 12 * (TT.card * La * b' * Y) := by ring
      _ ≤ (k * Y * Yb * Real.log a) * (TT.card * La * b' * Y) := mul_le_mul_of_nonneg_right h1 h2
      _ = (k : ℝ) * Y ^ 2 * Yb * TT.card * La * Real.log a * b' := by ring
      _ ≤ a := hab
  have hwa : a / (k * Y) - 1 < ((⌊a + a / (k * Y)⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
    push_cast
    linarith [Int.sub_one_lt_floor (a + a / (k * Y)), Int.ceil_lt_add_one a]
  have ha2 : 4 ≤ a / (k * Y) := by
    rw [le_div_iff₀ hkY]
    have h4 : (4 : ℝ) ≤ Y * Yb * TT.card * La * Real.log a * b' := by
      have h1 : (12 : ℝ) ≤ Y * Yb := by
        calc (12 : ℝ) = 1 * 12 := by ring
          _ ≤ Y * Yb := mul_le_mul hY hYb12 (by norm_num) (by positivity)
      have h2 : (12 : ℝ) ≤ Y * Yb * TT.card := h1.trans (le_mul_of_one_le_right (by positivity) (by linarith))
      have h3 : (12 : ℝ) ≤ Y * Yb * TT.card * La := h2.trans (le_mul_of_one_le_right (by positivity) hLa1)
      have h5 : (12 : ℝ) ≤ Y * Yb * TT.card * La * Real.log a :=
        h3.trans (le_mul_of_one_le_right (by positivity) hloga)
      have h6 : (12 : ℝ) ≤ Y * Yb * TT.card * La * Real.log a * b' :=
        h5.trans (le_mul_of_one_le_right (by positivity) hb'1)
      linarith
    calc 4 * (k * Y) = (k * Y) * 4 := by ring
      _ ≤ (k * Y) * (Y * Yb * TT.card * La * Real.log a * b') := mul_le_mul_of_nonneg_left h4 hkY.le
      _ = (k : ℝ) * Y ^ 2 * Yb * TT.card * La * Real.log a * b' := by ring
      _ ≤ a := hab
  obtain ⟨wa, hwadef⟩ : ∃ wa : ℤ, wa = ⌊a + a / (k * Y)⌋ + 1 - ⌈a⌉ := ⟨_, rfl⟩
  rw [← hwadef] at hwa
  have hwa0 : (0 : ℤ) ≤ wa := by
    have : (0 : ℝ) < wa := by linarith
    exact_mod_cast this.le
  have hcardA : ((aWin k Y a).card : ℝ) = wa := by
    rw [aWin, Int.card_Icc, ← hwadef]
    exact_mod_cast Int.toNat_of_nonneg hwa0
  have hcardWA : ((WAp k Y a c J).card : ℝ) = wa + (2 * c + J) := by
    rw [WAp, Int.card_Icc]
    have e : ⌊a + a / (k * Y)⌋ + c + J + 1 - (⌈a⌉ - c) = wa + (2 * c + J) := by rw [hwadef]; ring
    rw [e]
    have : (0 : ℤ) ≤ wa + (2 * c + J) := by positivity
    have h2 : (((wa + (2 * c + J)).toNat : ℕ) : ℝ) = ((wa + (2 * c + J) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg this
    rw [h2]
    push_cast
    ring
  -- the `b`-window
  have hbw := h.b_win
  rw [← hLadef] at hbw
  have hwb : bu - bl - 1 < ((⌊bu⌋ + 1 - ⌈bl⌉ : ℤ) : ℝ) := by
    push_cast
    linarith [Int.sub_one_lt_floor bu, Int.ceil_lt_add_one bl]
  have hYNL : (24 : ℝ) ≤ Yb * TT.card * La * b' / k := by
    rw [le_div_iff₀ hk0]
    have h2 : (24 : ℝ) ≤ Yb * TT.card := by
      calc (24 : ℝ) = 12 * 2 := by ring
        _ ≤ Yb * TT.card := mul_le_mul hYb12 hN2 (by norm_num) (by positivity)
    have h3 : (24 : ℝ) ≤ Yb * TT.card * La := h2.trans (le_mul_of_one_le_right (by positivity) hLa1)
    calc (24 : ℝ) * k ≤ 24 * b' := by linarith
      _ ≤ (Yb * TT.card * La) * b' := mul_le_mul_of_nonneg_right h3 hb'0.le
  obtain ⟨wb, hwbdef⟩ : ∃ wb : ℤ, wb = ⌊bu⌋ + 1 - ⌈bl⌉ := ⟨_, rfl⟩
  rw [← hwbdef] at hwb
  have hwb0 : (0 : ℤ) ≤ wb := by
    have : (0 : ℝ) < wb := by linarith [hbw.2.2.2.1]
    exact_mod_cast this.le
  have hcardB : ((bWin bl bu).card : ℝ) = wb := by
    rw [bWin, Int.card_Icc, ← hwbdef]
    exact_mod_cast Int.toNat_of_nonneg hwb0
  have hcardWB : ((WBp bl bu c J).card : ℝ) = wb + (2 * c + J) := by
    rw [WBp, Int.card_Icc]
    have e : ⌊bu⌋ + c + J + 1 - (⌈bl⌉ - c) = wb + (2 * c + J) := by rw [hwbdef]; ring
    rw [e]
    have : (0 : ℤ) ≤ wb + (2 * c + J) := by positivity
    have h2 : (((wb + (2 * c + J)).toNat : ℕ) : ℝ) = ((wb + (2 * c + J) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg this
    rw [h2]
    push_cast
    ring
  refine ⟨by rw [hcardA]; linarith, by rw [hcardB]; linarith [hbw.2.2.2.1], ?_, ?_⟩
  · rw [hcardWA, hcardA]
    refine pow_add_le_two_mul (by linarith) (by positivity) ?_
    have : 6 * (TT.card : ℝ) * (La * b' / k) ≤ a / (k * Y) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hkY]
      have e1 : 6 * (TT.card : ℝ) * (La * b' / k) * 2 * (k * Y) = 12 * TT.card * La * b' * Y := by
        field_simp
        ring
      rw [e1]
      exact h12
    linarith
  · rw [hcardWB, hcardB]
    refine pow_add_le_two_mul (by linarith [hbw.2.2.2.1]) (by positivity) ?_
    have : 6 * (TT.card : ℝ) * (La * b' / k) ≤ (Yb * TT.card * La * b' / k) / 2 := by
      have h1 : (12 : ℝ) ≤ Yb := by linarith [hYb.1]
      have e1 : (Yb * TT.card * La * b' / k) / 2 = Yb / 12 * (6 * TT.card * (La * b' / k)) := by ring
      rw [e1]
      have h2 : (0 : ℝ) ≤ 6 * TT.card * (La * b' / k) := by positivity
      exact le_mul_of_one_le_left h2 (by linarith)
    have h3 : Yb * TT.card * La * b' / k ≤ bu - bl := by
      have := hbw.2.2.2.1
      linarith
    linarith

/-- **The previous V-top is a V-top** (when there is one): `prevV TT y = x` for the V-top `x` lying
`prevVDist TT y` positions before `y` (`prevVDist_spec`). -/
theorem prevV_mem {n' : ℕ} {TT : Finset (Fin n')} (h : (vTops TT).Nonempty) (y : Fin n') :
    prevV TT y ∈ vTops TT := by
  obtain ⟨h1, h2, x, hx, hxy⟩ := prevVDist_spec h y
  suffices e : prevV TT y = x by rw [e]; exact hx
  have hy := y.isLt
  have hxl := x.isLt
  ext
  simp only [prevV]
  obtain ⟨d, hd⟩ : ∃ d, d = prevVDist TT y := ⟨_, rfl⟩
  rw [← hd] at h1 h2 hxy ⊢
  rcases Nat.lt_or_ge (x.val + d) n' with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hxy
    rw [Nat.mod_eq_of_lt (by omega : d < n'), show y.val + n' - d = x.val + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hxl]
  · have hlt : x.val + d - n' < n' := by omega
    rw [show x.val + d = (x.val + d - n') + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hlt] at hxy
    rcases Nat.lt_or_ge d n' with hdn | hdn
    · rw [Nat.mod_eq_of_lt hdn, show y.val + n' - d = x.val by omega, Nat.mod_eq_of_lt hxl]
    · have hdn' : d = n' := by omega
      rw [hdn', Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
      omega

/-- **The odd-top term moves by at most `N·e`**: if `β_y ≤ β′_y + e` and `α_{y′} ≤ α′_{y′} + e` at the tops
(`e ≥ 0`, `p ≥ 1`), then `minTerm(α, β) ≤ minTerm(α′, β′) + N·e`. -/
theorem minTerm_le_add {n' p : ℕ} (hp : 1 ≤ p) {TT : Finset (Fin n')} {α β α' β' : Fin n' → ℤ} {e : ℝ}
    (he : 0 ≤ e) (h : ∀ y ∈ TT, (β y : ℝ) ≤ β' y + e ∧ (α (prevV TT y) : ℝ) ≤ α' (prevV TT y) + e) :
    minTerm p TT α β ≤ minTerm p TT α' β' + TT.card * e := by
  unfold minTerm
  have hcard : ((TT.filter fun y => ¬ Even y.val).card : ℝ) * e ≤ TT.card * e :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) he
  have hsum : ∑ y ∈ TT.filter (fun y => ¬ Even y.val), min (β y : ℝ) ((α (prevV TT y) : ℝ) / (p : ℝ) ^ prevVDist TT y)
      ≤ ∑ y ∈ TT.filter (fun y => ¬ Even y.val),
        (min (β' y : ℝ) ((α' (prevV TT y) : ℝ) / (p : ℝ) ^ prevVDist TT y) + e) := by
    refine sum_le_sum fun y hy => ?_
    have hyT := (mem_filter.1 hy).1
    obtain ⟨h1, h2⟩ := h y hyT
    have hP : (1 : ℝ) ≤ (p : ℝ) ^ prevVDist TT y := one_le_pow₀ (by exact_mod_cast hp)
    have hP0 : (0 : ℝ) < (p : ℝ) ^ prevVDist TT y := by linarith
    rw [← min_add_add_right]
    refine min_le_min h1 ?_
    rw [div_le_iff₀ hP0, add_mul, div_mul_cancel₀ _ hP0.ne']
    nlinarith
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  linarith

variable {Ct : ℝ} in
/-- **The input depth after a harmonic shift** (A-N11's depth shift): `t₀(A, B) ≤ t₀(A − j, B − j) + N·J` for
`0 ≤ j ≤ J`. -/
theorem depth0_shift {n' p : ℕ} (hp : 1 ≤ p) {TT : Finset (Fin n')} (La : ℝ) (k G' : ℕ) (a b' : ℝ) (c₄ J : ℕ)
    (A B jh : TT → ℤ) (hj : ∀ s, 0 ≤ jh s ∧ jh s ≤ J) :
    depth0 Ct La p TT k G' a b' c₄ A B ≤ depth0 Ct La p TT k G' a b' c₄ (A - jh) (B - jh) + TT.card * J := by
  unfold depth0
  have hext : ∀ y, (ext TT jh y : ℝ) ≤ J := fun y => by
    unfold ext; split_ifs with hy
    · exact_mod_cast (hj _).2
    · simp
  have := minTerm_le_add hp (Nat.cast_nonneg (α := ℝ) J) (α := ext TT A) (β := ext TT B) (α' := ext TT (A - jh))
    (β' := ext TT (B - jh)) (TT := TT) fun y _ => by
      rw [ext_sub, ext_sub]; push_cast
      exact ⟨by linarith [hext y], by linarith [hext (prevV TT y)]⟩
  linarith

variable {Ct : ℝ} in
/-- **The input depth is monotone** in the extremes. -/
theorem depth0_mono {n' p : ℕ} (hp : 1 ≤ p) {TT : Finset (Fin n')} (La : ℝ) (k G' : ℕ) (a b' : ℝ) (c₄ : ℕ)
    {A B A' B' : TT → ℤ} (hA : ∀ s, A s ≤ A' s) (hB : ∀ s, B s ≤ B' s) :
    depth0 Ct La p TT k G' a b' c₄ A B ≤ depth0 Ct La p TT k G' a b' c₄ A' B' := by
  unfold depth0
  have hext : ∀ (X X' : TT → ℤ), (∀ s, X s ≤ X' s) → ∀ y, (ext TT X y : ℝ) ≤ ext TT X' y := fun X X' hX y => by
    unfold ext; split_ifs with hy
    · exact_mod_cast hX _
    · exact le_rfl
  have := minTerm_le_add hp le_rfl (α := ext TT A) (β := ext TT B) (α' := ext TT A') (β' := ext TT B') (TT := TT)
    fun y _ => ⟨by linarith [hext B B' hB y], by linarith [hext A A' hA (prevV TT y)]⟩
  linarith

/-- **The odd-top term is nonnegative** for nonnegative extremes. -/
theorem minTerm_nonneg {n' p : ℕ} {TT : Finset (Fin n')} {α β : Fin n' → ℤ}
    (h : ∀ y ∈ TT, 0 ≤ β y ∧ 0 ≤ α (prevV TT y)) : 0 ≤ minTerm p TT α β := by
  unfold minTerm
  refine sum_nonneg fun y hy => ?_
  obtain ⟨h1, h2⟩ := h y (mem_filter.1 hy).1
  exact le_min (by exact_mod_cast h1) (div_nonneg (by exact_mod_cast h2) (by positivity))

/-- **The term-by-term domination of the depths** (the algebra of A-N20's depth comparison). -/
theorem depth_dom {Mt MI N N₁ X₁ J Q k Ct C c4 cI c lg T : ℝ} (hM : Mt ≤ MI + N * c) (hX0 : 0 ≤ X₁)
    (hJ : J ≤ X₁) (hN₁ : 1 ≤ N₁) (hN : 0 ≤ N) (hNkQ : 1 ≤ N * (k * Q)) (hQ : 0 ≤ Q) (hc4 : 0 ≤ c4)
    (hcI : c4 ≤ cI) (hc : 0 ≤ c) (hC : Ct + 1 ≤ C) (hCt : 0 ≤ Ct) (hlg : 0 ≤ k * lg) :
    Mt + Ct * N * (X₁ + k * Q + Q * c4) + N * J + 1 + T ≤
      MI + C * N * N₁ * X₁ + C * N * (Q * cI + k * Q + k * lg + c) + T := by
  have hC0 : 0 ≤ C := by linarith
  have hCN : 0 ≤ C * N := mul_nonneg hC0 hN
  have e1 : C * N * X₁ * 1 ≤ C * N * X₁ * N₁ := mul_le_mul_of_nonneg_left hN₁ (mul_nonneg hCN hX0)
  have e2 : (Ct + 1) * N * X₁ ≤ C * N * X₁ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN) hX0
  have e3 : N * J ≤ N * X₁ := mul_le_mul_of_nonneg_left hJ hN
  have e4 : Ct * N * (Q * c4) ≤ C * N * (Q * cI) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hN) (mul_le_mul_of_nonneg_left hcI hQ)
      (mul_nonneg hQ hc4) hCN
  have e5 : (Ct + 1) * (N * (k * Q)) ≤ C * (N * (k * Q)) :=
    mul_le_mul_of_nonneg_right hC (by linarith)
  have e6 : 1 * (N * c) ≤ C * (N * c) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hN hc)
  have e7 : 0 ≤ C * N * (k * lg) := mul_nonneg hCN hlg
  nlinarith

/-- **The depth comparison** (A-N20, for `C ≥ C_t + 1`, `C_t ≥ 0`, nonnegative extremes): the depth
`⌈t₀(a + c, b + c) + N·J⌉ + 2n′c` of the per-weight assembly is at most `t_I(a, b)`: the odd-top term moves by
`≤ N·c` (`min(b + c, (a + c)/P) ≤ min(b, a/P) + c`), and the other terms of `t₀ + N·J` (with the conductor
`c₄ = c* + 2Nc + 2n′c ≤ c_I`) are dominated term by term, the `+1` of the ceiling by `N·k·Q` (`depth_dom`). -/
theorem FirstHyp.depth (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar) (hC₀ : 1 ≤ C₀)
    (hCH : 12 ≤ CH) {Ct C : ℝ} (hCt : 0 ≤ Ct) (hC : Ct + 1 ≤ C) (aw bw : Fin n' → ℤ)
    (haw : ∀ s ∈ TT, 0 ≤ aw s) (hbw : ∀ s ∈ TT, 0 ≤ bw s) :
    (⌈depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' (cStar + 2 * TT.card * c + 2 * n' * c)
        ((fun s : TT => aw s) + fun _ => (c : ℤ)) ((fun s : TT => bw s) + fun _ => (c : ℤ)) +
        TT.card * Jsh C₀ N₁ k a b'⌉₊ + 2 * n' * c : ℝ) ≤
      depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw := by
  obtain ⟨hN2, hk5, hp25, hQ, hb'0, -, -, hpa, hloga, -, hLa1, -, -, -, -, hN₁, hb'1⟩ := h.base hC₀ hCH
  obtain ⟨hJ, -⟩ := h.J_le hC₀ hCH
  have hp1 : 1 ≤ p := by exact_mod_cast (show (1 : ℝ) ≤ p by linarith)
  have hvT : (vTops TT).Nonempty := Finset.card_pos.1 (by have := h.seg.1; omega)
  have hprev : ∀ y, prevV TT y ∈ TT := fun y => (mem_filter.1 (prevV_mem hvT y)).1
  have hab : 25 * b' ≤ a := by nlinarith
  have ha1 : 1 ≤ a := by linarith
  -- the odd-top terms
  have hext : ∀ (X : Fin n' → ℤ) y, y ∈ TT → ext TT ((fun s : TT => X s) + fun _ => (c : ℤ)) y = X y + c :=
    fun X y hy => by rw [ext_of_mem _ hy]; rfl
  have hmin := minTerm_le_add hp1 (Nat.cast_nonneg (α := ℝ) c) (TT := TT)
    (α := ext TT ((fun s : TT => aw s) + fun _ => (c : ℤ))) (β := ext TT ((fun s : TT => bw s) + fun _ => (c : ℤ)))
    (α' := aw) (β' := bw) fun y hy => by
      rw [hext bw y hy, hext aw _ (hprev y)]; push_cast; exact ⟨le_rfl, le_rfl⟩
  have hmin0 : 0 ≤ minTerm p TT (ext TT ((fun s : TT => aw s) + fun _ => (c : ℤ)))
      (ext TT ((fun s : TT => bw s) + fun _ => (c : ℤ))) :=
    minTerm_nonneg fun y hy => by
      rw [hext bw y hy, hext aw _ (hprev y)]; exact ⟨by linarith [hbw y hy], by linarith [haw _ (hprev y)]⟩
  -- name the pieces
  obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt = minTerm p TT (ext TT ((fun s : TT => aw s) + fun _ => (c : ℤ)))
      (ext TT ((fun s : TT => bw s) + fun _ => (c : ℤ))) := ⟨_, rfl⟩
  obtain ⟨MI, hMI⟩ : ∃ MI, MI = minTerm p TT aw bw := ⟨_, rfl⟩
  obtain ⟨La, hLa⟩ : ∃ La, La = C₀ * N₁ ^ 2 * Real.log a := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) + La * b' / k := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = (p : ℝ) ^ G' := ⟨_, rfl⟩
  obtain ⟨c4, hc4d⟩ : ∃ c4 : ℝ, c4 = ((cStar + 2 * TT.card * c + 2 * n' * c : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨cI, hcId⟩ : ∃ cI : ℝ, cI = cStar + C * TT.card * k * Real.logb p a + 4 * TT.card * c + 2 * n' * c :=
    ⟨_, rfl⟩
  rw [← hMt, ← hMI] at hmin
  rw [← hMt] at hmin0
  rw [← hLa] at hJ hLa1
  have hp0 : (0 : ℝ) < p := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hX1J : (Jsh C₀ N₁ k a b' : ℝ) ≤ X₁ := by
    have : 0 ≤ a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) := by
      have : 0 ≤ La := by linarith
      positivity
    rw [hX₁]
    linarith
  have hX0 : 0 ≤ X₁ := le_trans (Nat.cast_nonneg _) hX1J
  have hlogp : 0 ≤ Real.logb p a := Real.logb_nonneg (by linarith) ha1
  have hdep : depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' (cStar + 2 * TT.card * c + 2 * n' * c)
      ((fun s : TT => aw s) + fun _ => (c : ℤ)) ((fun s : TT => bw s) + fun _ => (c : ℤ)) =
      Mt + Ct * TT.card * (X₁ + k * Q + Q * c4) := by
    rw [depth0, hMt, hX₁, hQd, hc4d, hLa]
  have hdepI : depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw =
      MI + C * TT.card * N₁ * X₁ + C * TT.card * (Q * cI + k * Q + k * Real.logb p a + c) + 2 * n' * c := by
    rw [depthI, hMI, hX₁, hQd, hcId, hLa]
  rw [hdep, hdepI]
  have hx0 : 0 ≤ Mt + Ct * TT.card * (X₁ + k * Q + Q * c4) + TT.card * Jsh C₀ N₁ k a b' := by
    have : 0 ≤ c4 := by rw [hc4d]; exact Nat.cast_nonneg _
    have : 0 ≤ Q := by rw [hQd]; positivity
    positivity
  have hceil := Nat.ceil_lt_add_one hx0
  have hc4I : c4 ≤ cI := by
    rw [hc4d, hcId]
    push_cast
    have : 0 ≤ C * TT.card * k * Real.logb p a := by
      have : 0 ≤ C := by linarith
      positivity
    have : (2 : ℝ) * TT.card * c ≤ 4 * TT.card * c := by nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
    linarith
  have hdom := depth_dom (T := 2 * n' * c) (lg := Real.logb p a) (k := (k : ℝ)) (Q := Q) (Ct := Ct) (C := C)
    (c4 := c4) (cI := cI) hmin hX0 hX1J hN₁ (Nat.cast_nonneg _)
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le (by linarith)
      (by rw [hQd]; exact hQ))) (by rw [hQd]; positivity) (by rw [hc4d]; exact Nat.cast_nonneg _) hc4I
    (Nat.cast_nonneg _) hC hCt (by positivity)
  linarith

end Numerics

end

end FirstMeans
