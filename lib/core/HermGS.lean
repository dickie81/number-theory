import ThetaCompare

/-!
# Gram–Schmidt over `ℤ_(ℓ)[ω]` and the four-squares orthonormal basis of `C⁴`

D1b-3 of the D1b plan: the local lattice at an inert prime `ℓ` with no completion, no Landherr, no norm surjectivity.
`C ⊆ ℂ^ι` is an `ω`-stable self-dual theta lattice (`ω = 1/2 + i·sd`, `ChainCanon.omegaD`, `4sd² = d`) for the form
`H = s·Σ z·w̄` (`ThetaChain.Hf`), and `h = sd·H`.

**The form.** On `C`, `h(x, y) = (E(ωx, y) − E(x, y)) + E(x, y)·ω` with `E = Im H` integral (`sd_mul_Hf`,
`sdHf_int`), and `h(x, x) ∈ ℤ` (`sdHf_self_int`). No congruence on `d` is needed for this.

**Gram–Schmidt** (`exists_gsBasis`). For an orthogonal family `b` in `C` with `h(b_i, b_j) = u_i·δ_ij`, `ℓ ∤ u_i`
(`IsOrthFam`), every `z ∈ C` decomposes as `U·z = Σ_i c_i·b_i + w`, `U = Π u_i`, `c_i = (U/u_i)·h(z, b_i) ∈ ℤ[ω]`,
`w ∈ W = C ∩ b^⊥` (`decomp`). If `ℓ ∣ h(z, z)` on `W`, polarising at `x + y` and `ωx + y` gives `2sd·Re H ∈ ℓℤ` and
`sd·Re H − 2sd²·Im H ∈ ℓℤ`, so `ℓ ∣ d·E`, hence `ℓ ∣ E` on `W` (`ell_dvd_im`; `ℓ ∤ d` as `ℓ` is inert). Then
self-duality and the decomposition give `ℓ⁻¹W ⊆ W` (`inv_smul_mem`), so a nonzero `x ∈ W` would have the positive
integer `h(x, x)` divisible by every `ℓ^{2k}`. Hence a nonzero `W` contains `x` with `ℓ ∤ h(x, x)`
(`exists_unit_perp`), and the family extends. By induction (`exists_orthFam`) there is such a family of length
`n = dim_ℂ`: for shorter families `W ≠ 0`, as otherwise `C ⊆ span_ℂ b`. For length `n`, `W = 0` (orthogonal nonzero
vectors are independent, `linIndep_orth`), so `U·C ⊆ ⊕ ℤ[ω]·b_i`: an `ℓ`-adapted orthogonal basis with unit diagonal
(`GSBasis`). Discreteness of `C` and `ℓ ≠ 2` are not used.

**Four squares** (`orth4_spec`). With `u_i = a_i² + b_i² + c_i² + e_i²` and `quatL` the left multiplication by the
quaternion (`quatL·quatLᵀ = quatLᵀ·quatL = u·1`), the vectors `f_{k,i} = u_i⁻¹·Σ_l quatL_i(k, l)·slot_l(b_i)` of
`C⁴ ⊆ ℂ^{Fin 4 × ι}` satisfy `H(f_p, f_q) = δ_pq/(|δ|²·sd)` (`Hf_orth4Vec`), so `g(e_p) = δ⁻¹f_p` (`orth4`) is a
bijective `H`-isometry (`s·|δ|²·sd = 1`), and `slot_l(b_i) = Σ_k quatL_i(k, l)·δ·f_{k,i}` with integer coefficients
(`slotV_eq_sum`) makes `g(Lc^{Fin 4 × ι})` and `C⁴` `ℓ`-adapted (`LAdapted`, multiplier `M·Π u_i`). The converse
inclusion needs `C` to be `ω`-stable, a hypothesis added to the spec's statement.

**`C⁴`** is a theta lattice (`isThetaLat_pow4`, with `α` multiplicative over the slices, `al_pow4`) and self-dual
(`isEDual_pow4`) with `C` (`pow4_theta_edual`). `ℓ`-adapted lattices are commensurable when one is finitely generated
(`isCommens_of_lAdapted`: `x ↦ M·x` embeds `Λ₁/(Λ₁ ∩ Λ₂)` in the finite `Λ₂/MΛ₂`), so `C⁴` and `g(Lc^{Fin 4 × ι})` are
commensurable (`isCommens_orth4`, with `fg_stdLc`), as `ThetaCompare.theta_compare` requires.

**Main declarations:** `okSpan`, `LAdapted`, `GSBasis`, `exists_gsBasis`, `quatL`, `quatL_mul_transpose`, `slotV`,
`orth4`, `orth4_spec`, `isThetaLat_pow4`, `isEDual_pow4`, `isCommens_orth4`.
-/

namespace HermGS

open ThetaChain ThetaNorm ThetaHeis ThetaCompare ChainCanon Complex

noncomputable section

/-! ## The lattices -/

section Defs

variable {ι : Type*}

/-- **The `ℤ[ω]`-span** of a family `b` (`O_{K₀} = ℤ[ω]` acts on `Amb` by complex scalars): the subgroup generated
by the `(m + nω)·b_i`, `m, n ∈ ℤ`. -/
def okSpan (ω : ℂ) {κ : Type*} (b : κ → (ι → ℂ)) : AddSubgroup (ι → ℂ) :=
  AddSubgroup.closure {z | ∃ i, ∃ m n : ℤ, z = ((m : ℂ) + n * ω) • b i}

/-- **Two lattices with the same `ℓ`-part**: each one, times some `M` prime to `ℓ`, lies in the other. -/
def LAdapted (ℓ : ℕ) (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ¬ ℓ ∣ M ∧ (∀ x ∈ Λ₁, M • x ∈ Λ₂) ∧ ∀ y ∈ Λ₂, M • y ∈ Λ₁

variable [Fintype ι] [DecidableEq ι]

/-- **An `ℓ`-adapted orthogonal basis with unit diagonal** of `C` (replacing an orthonormal basis over `ℤ_{ℓ²}`):
for `h = sd·H`, `h(b_i, b_j) = u_i·δ_ij` with `u_i ∈ ℕ` prime to `ℓ`, `b_i ∈ C`, and `M·C ⊆ ⊕_i ℤ[ω]·b_i` for some
`M` prime to `ℓ`. -/
structure GSBasis (ℓ : ℕ) (s sd : ℝ) (ω : ℂ) (C : AddSubgroup (ι → ℂ)) where
  /-- The basis vectors. -/
  b : ι → (ι → ℂ)
  /-- The diagonal `u_i = sd·H(b_i, b_i)`. -/
  u : ι → ℕ
  /-- The index multiplier. -/
  M : ℕ
  /-- `M > 0`. -/
  M_pos : 0 < M
  /-- `M` is prime to `ℓ`. -/
  M_cop : ¬ ℓ ∣ M
  /-- `u_i > 0`. -/
  u_pos : ∀ i, 0 < u i
  /-- `u_i` is prime to `ℓ`. -/
  u_cop : ∀ i, ¬ ℓ ∣ u i
  /-- Orthogonality with diagonal `u`. -/
  orth : ∀ i j, (sd : ℂ) * Hf s (b i) (b j) = if i = j then (u i : ℂ) else 0
  /-- The basis lies in `C`. -/
  mem : ∀ i, b i ∈ C
  /-- `M·C` lies in the `ℤ[ω]`-span of the basis. -/
  span : ∀ x ∈ C, M • x ∈ okSpan ω b

end Defs

/-! ## The hermitian form `h = sd·H` on an `ω`-stable theta lattice -/

section Form

variable {ι : Type*} [Fintype ι] {s sd : ℝ}

/-- **`H` of a difference in the first argument.** -/
theorem Hf_sub_left (x y z : ι → ℂ) : Hf s (x - y) z = Hf s x z - Hf s y z := by
  rw [sub_eq_add_neg, Hf_add_left, Hf_neg_left, ← sub_eq_add_neg]

/-- **`H` of a finite sum in the first argument.** -/
theorem Hf_sum_left {κ : Type*} (t : Finset κ) (f : κ → ι → ℂ) (y : ι → ℂ) :
    Hf s (∑ i ∈ t, f i) y = ∑ i ∈ t, Hf s (f i) y := by
  simp only [Hf, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- **`H` of a finite sum in the second argument.** -/
theorem Hf_sum_right {κ : Type*} (t : Finset κ) (x : ι → ℂ) (f : κ → ι → ℂ) :
    Hf s x (∑ i ∈ t, f i) = ∑ i ∈ t, Hf s x (f i) := by
  simp only [Hf, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- **`H(x, x)` is real.** -/
theorem Hf_self_im (x : ι → ℂ) : (Hf s x x).im = 0 := by
  linarith [Hf_swap_im s x x]

/-- **`H` is positive definite** for `s > 0`. -/
theorem Hf_self_re_pos (hs : 0 < s) {x : ι → ℂ} (hx : x ≠ 0) : 0 < (Hf s x x).re := by
  have e : Hf s x x = ((s * ∑ p, Complex.normSq (x p) : ℝ) : ℂ) := by
    simp only [Hf, Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_sum]
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hx
  rw [e, Complex.ofReal_re]
  exact mul_pos hs (Finset.sum_pos' (fun q _ => Complex.normSq_nonneg _)
    ⟨p, Finset.mem_univ _, Complex.normSq_pos.mpr hp⟩)

/-- **`H(cx, cx) = |c|²·H(x, x)`.** -/
theorem Hf_smul_self (c : ℂ) (x : ι → ℂ) : Hf s (c • x) (c • x) = (Complex.normSq c : ℂ) * Hf s x x := by
  rw [Hf_smul_left, Hf_smul_right, ← mul_assoc, Complex.mul_conj]

/-- **`sd·H` in the basis `1, ω`**: `sd·H(x, y) = (E(ωx, y) − E(x, y)) + E(x, y)·ω` with `E = Im H` and
`ω = 1/2 + i·sd` (`omegaD`). -/
theorem sd_mul_Hf (x y : ι → ℂ) :
    (sd : ℂ) * Hf s x y = (((Hf s (omegaD sd • x) y).im - (Hf s x y).im : ℝ) : ℂ) +
      ((Hf s x y).im : ℂ) * omegaD sd := by
  rw [Hf_smul_left]
  apply Complex.ext <;> simp [omegaD, Complex.mul_re, Complex.mul_im] <;> ring

variable {C : AddSubgroup (ι → ℂ)}

/-- **`h = sd·H` is `ℤ[ω]`-valued** on an `ω`-stable theta lattice. -/
theorem sdHf_int (hCt : IsThetaLat s sd C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {x y : ι → ℂ} (hx : x ∈ C)
    (hy : y ∈ C) : ∃ m n : ℤ, (sd : ℂ) * Hf s x y = m + n * omegaD sd := by
  obtain ⟨n, hn, -⟩ := hCt x hx y hy
  obtain ⟨k, hk, -⟩ := hCt _ (hω x hx) y hy
  refine ⟨k - n, n, ?_⟩
  rw [sd_mul_Hf, hn, hk]
  push_cast
  ring

/-- **`h(x, x) = sd·H(x, x)` is an integer** on an `ω`-stable theta lattice. -/
theorem sdHf_self_int (hCt : IsThetaLat s sd C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {x : ι → ℂ} (hx : x ∈ C) :
    ∃ m : ℤ, (sd : ℂ) * Hf s x x = m := by
  obtain ⟨m, hm⟩ := sdNorm_int_of_smul_mem hCt (by simp [omegaD]) hω x hx
  refine ⟨m, Complex.ext ?_ ?_⟩
  · simpa [Complex.mul_re, Hf_self_im] using hm
  · simp [Complex.mul_im, Hf_self_im]

omit [Fintype ι] in
/-- **`ℤ[ω]`-multiples stay in an `ω`-stable subgroup.** -/
theorem okMul_mem {Λ : AddSubgroup (ι → ℂ)} (hω : ∀ x ∈ Λ, omegaD sd • x ∈ Λ) {v : ι → ℂ} (hv : v ∈ Λ)
    (m n : ℤ) : ((m : ℂ) + n * omegaD sd) • v ∈ Λ := by
  rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact add_mem (zsmul_mem hv m) (zsmul_mem (hω v hv) n)

end Form

/-! ## The fourth power `C⁴` -/

section Pow4

variable {ι : Type*} {s sd : ℝ}

/-- **The vector `v` in slot `l`** of `ℂ^{Fin 4 × ι}`. -/
def slotV (l : Fin 4) (v : ι → ℂ) : Fin 4 × ι → ℂ := fun q => if q.1 = l then v q.2 else 0

/-- **The slices of a slot vector.** -/
theorem slice_slotV (k l : Fin 4) (v : ι → ℂ) : slice k (slotV l v) = if k = l then v else 0 := by
  ext p
  by_cases hk : k = l <;> simp [slice, slotV, hk]

/-- **`slotV l` is additive.** -/
theorem slotV_add (l : Fin 4) (v w : ι → ℂ) : slotV l (v + w) = slotV l v + slotV l w := by
  ext q
  by_cases h : q.1 = l <;> simp [slotV, h]

/-- **`slotV l` is linear.** -/
theorem slotV_smul (l : Fin 4) (c : ℂ) (v : ι → ℂ) : slotV l (c • v) = c • slotV l v := by
  ext q
  by_cases h : q.1 = l <;> simp [slotV, h]

/-- **`slotV l` as an additive map.** -/
def slotHom (l : Fin 4) : (ι → ℂ) →+ (Fin 4 × ι → ℂ) where
  toFun := slotV l
  map_zero' := by ext q; simp [slotV]
  map_add' := slotV_add l

/-- **A vector is the sum of its slices in their slots.** -/
theorem sum_slotV_slice (v : Fin 4 × ι → ℂ) : ∑ l, slotV l (slice l v) = v := by
  ext ⟨k, p⟩
  simp only [Finset.sum_apply, slotV, slice]
  rw [Finset.sum_eq_single k (fun l _ hl => ite_eq_right (Ne.symm hl)) (fun h => absurd (Finset.mem_univ k) h)]
  simp

/-- **The slices of a vector of `Λ⁴`** lie in `Λ`. -/
theorem slice_mem_pow4 {Λ : AddSubgroup (ι → ℂ)} {v : Fin 4 × ι → ℂ} (hv : v ∈ pow4 Λ) (k : Fin 4) :
    slice k v ∈ Λ :=
  AddSubgroup.mem_comap.mp (AddSubgroup.mem_iInf.mp hv k)

/-- **Membership in `Λ⁴`** is slicewise. -/
theorem mem_pow4 {Λ : AddSubgroup (ι → ℂ)} {v : Fin 4 × ι → ℂ} (hv : ∀ k, slice k v ∈ Λ) : v ∈ pow4 Λ :=
  AddSubgroup.mem_iInf.mpr fun k => AddSubgroup.mem_comap.mpr (hv k)

/-- **A slot vector of `Λ` lies in `Λ⁴`.** -/
theorem slotV_mem_pow4 {Λ : AddSubgroup (ι → ℂ)} {v : ι → ℂ} (hv : v ∈ Λ) (l : Fin 4) : slotV l v ∈ pow4 Λ :=
  mem_pow4 fun k => by
    rw [slice_slotV]
    split_ifs
    · exact hv
    · exact zero_mem _

/-- **`Λ⁴` is `ω`-stable** with `Λ`. -/
theorem pow4_smul_mem {Λ : AddSubgroup (ι → ℂ)} {w : ℂ} (hω : ∀ x ∈ Λ, w • x ∈ Λ) {v : Fin 4 × ι → ℂ}
    (hv : v ∈ pow4 Λ) : w • v ∈ pow4 Λ :=
  mem_pow4 fun k => by
    have e : slice k (w • v) = w • slice k v := by ext p; simp [slice]
    rw [e]
    exact hω _ (slice_mem_pow4 hv k)

variable [Fintype ι]

/-- **`H` against a slot vector**: `H(slot_l v, w) = H(v, w_l)`. -/
theorem Hf_slotV_left (l : Fin 4) (v : ι → ℂ) (w : Fin 4 × ι → ℂ) :
    Hf s (slotV l v) w = Hf s v (slice l w) := by
  rw [Hf_slice, Finset.sum_eq_single l (fun k _ hk => by rw [slice_slotV, ite_eq_right hk, Hf_zero_left])
    (fun h => absurd (Finset.mem_univ l) h), slice_slotV, ite_eq_left rfl]

/-- **`H` between slot vectors.** -/
theorem Hf_slotV (l l' : Fin 4) (v w : ι → ℂ) :
    Hf s (slotV l v) (slotV l' w) = if l = l' then Hf s v w else 0 := by
  rw [Hf_slotV_left, slice_slotV]
  split_ifs <;> simp [Hf_zero_right]

/-- **The semicharacter of `Λ⁴` is the product over the slices** when `sd·H(x, x)` is integral on `Λ`. -/
theorem al_pow4 {Λ : AddSubgroup (ι → ℂ)} (hint : ∀ x ∈ Λ, ∃ m : ℤ, sd * (Hf s x x).re = m)
    {v : Fin 4 × ι → ℂ} (hv : v ∈ pow4 Λ) : al s sd v = ∏ k : Fin 4, al s sd (slice k v) := by
  choose m hm using fun k => hint _ (slice_mem_pow4 hv k)
  have hsum : sd * (Hf s v v).re = ((∑ k, m k : ℤ) : ℝ) := by
    rw [Hf_slice, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun k _ => hm k
  rw [al_eq_of_int hsum, Finset.prod_congr rfl fun k _ => al_eq_of_int (hm k), Fin.sum_univ_four,
    Fin.prod_univ_four, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]

/-- **`Λ⁴` is a theta lattice** for a theta lattice `Λ` with `sd·H(x, x)` integral (`sdNorm_int_of_smul_mem`). -/
theorem isThetaLat_pow4 {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsThetaLat s sd Λ)
    (hint : ∀ x ∈ Λ, ∃ m : ℤ, sd * (Hf s x x).re = m) : IsThetaLat s sd (pow4 Λ) := by
  intro x hx y hy
  choose n hn hal using fun k => hΛ _ (slice_mem_pow4 hx k) _ (slice_mem_pow4 hy k)
  refine ⟨∑ k, n k, ?_, ?_⟩
  · rw [Hf_slice, Complex.im_sum]
    push_cast
    exact Finset.sum_congr rfl fun k _ => hn k
  · rw [al_pow4 hint (add_mem hx hy), al_pow4 hint hx, al_pow4 hint hy]
    simp only [map_add, hal, Fin.prod_univ_four, Fin.sum_univ_four, zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num)]
    ring

/-- **`Λ⁴` is self-dual** with `Λ` (test against the slot vectors `slot_k(x)`, `x ∈ Λ`). -/
theorem isEDual_pow4 {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsEDual s Λ) : IsEDual s (pow4 Λ) := by
  intro y hy
  refine mem_pow4 fun k => hΛ _ fun x hx => ?_
  obtain ⟨n, hn⟩ := hy (slotV k x) (slotV_mem_pow4 hx k)
  exact ⟨n, by rw [← hn, Hf_slotV_left]⟩

/-- **`C⁴` is a self-dual theta lattice** for `C` an `ω`-stable self-dual theta lattice. -/
theorem pow4_theta_edual {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsThetaLat s sd Λ) (hd : IsEDual s Λ)
    (hω : ∀ x ∈ Λ, omegaD sd • x ∈ Λ) : IsThetaLat s sd (pow4 Λ) ∧ IsEDual s (pow4 Λ) :=
  ⟨isThetaLat_pow4 hΛ (sdNorm_int_of_smul_mem hΛ (by simp [omegaD]) hω), isEDual_pow4 hd⟩

end Pow4


/-! ## Gram–Schmidt over `ℤ_(ℓ)[ω]` -/

section GS

variable {ι : Type*} [Fintype ι] {ℓ : ℕ} {s sd : ℝ} {C : AddSubgroup (ι → ℂ)}

/-- **An orthogonal family with unit diagonal** in `C`: `h(b_i, b_j) = u_i·δ_ij` with `0 < u_i`, `ℓ ∤ u_i`. -/
structure IsOrthFam (ℓ : ℕ) (s sd : ℝ) (C : AddSubgroup (ι → ℂ)) {κ : Type*} [DecidableEq κ] (b : κ → ι → ℂ)
    (u : κ → ℕ) : Prop where
  /-- `u_i > 0`. -/
  u_pos : ∀ i, 0 < u i
  /-- `u_i` is prime to `ℓ`. -/
  u_cop : ∀ i, ¬ ℓ ∣ u i
  /-- Orthogonality with diagonal `u`. -/
  orth : ∀ i j, (sd : ℂ) * Hf s (b i) (b j) = if i = j then (u i : ℂ) else 0
  /-- The family lies in `C`. -/
  mem : ∀ i, b i ∈ C

/-- **The orthogonal complement `C ∩ b^⊥`** of a family in `C`. -/
def Perp (s : ℝ) (C : AddSubgroup (ι → ℂ)) {κ : Type*} (b : κ → ι → ℂ) : Set (ι → ℂ) :=
  {z | z ∈ C ∧ ∀ i, Hf s z (b i) = 0}

variable {κ : Type*} [DecidableEq κ]

/-- **The vectors of an orthogonal family are nonzero.** -/
theorem IsOrthFam.ne_zero {b : κ → ι → ℂ} {u : κ → ℕ} (hb : IsOrthFam ℓ s sd C b u) (i : κ) : b i ≠ 0 := by
  intro h
  have := hb.orth i i
  rw [h, Hf_zero_left, mul_zero, ite_eq_left rfl] at this
  exact (hb.u_pos i).ne' (by exact_mod_cast this.symm)

/-- **Distinct vectors of an orthogonal family are `H`-orthogonal** (`sd ≠ 0`). -/
theorem IsOrthFam.Hf_eq_zero {b : κ → ι → ℂ} {u : κ → ℕ} (hb : IsOrthFam ℓ s sd C b u) (hsd0 : sd ≠ 0)
    {i j : κ} (hij : i ≠ j) : Hf s (b i) (b j) = 0 := by
  have := hb.orth i j
  rw [ite_eq_right hij] at this
  exact (mul_eq_zero.mp this).resolve_left (Complex.ofReal_ne_zero.mpr hsd0)

/-- **`H`-orthogonal nonzero vectors are linearly independent.** -/
theorem linIndep_orth {ι' : Type*} (hs : 0 < s) {v : ι' → ι → ℂ} (horth : ∀ i j, i ≠ j → Hf s (v i) (v j) = 0)
    (hv : ∀ i, v i ≠ 0) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro t g hg i hi
  have h := congrArg (fun w => Hf s w (v i)) hg
  simp only [Hf_sum_left, Hf_smul_left, Hf_zero_left] at h
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [horth j i hji, mul_zero])
    (fun h' => absurd hi h')] at h
  refine (mul_eq_zero.mp h).resolve_right fun h0 => ?_
  have := Hf_self_re_pos hs (hv i)
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

variable [Fintype κ]

/-- **The decomposition** `U·z = Σ_i c_i·b_i + w` with `U = Π_i u_i`, `c_i = (U/u_i)·h(z, b_i) ∈ ℤ[ω]` and
`w ∈ C ∩ b^⊥`. -/
theorem decomp (hCt : IsThetaLat s sd C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) (hsd0 : sd ≠ 0) {b : κ → ι → ℂ}
    {u : κ → ℕ} (hb : IsOrthFam ℓ s sd C b u) {z : ι → ℂ} (hz : z ∈ C) :
    ∃ m n : κ → ℤ, ((∏ i, u i : ℕ) : ℂ) • z - ∑ i, ((m i : ℂ) + n i * omegaD sd) • b i ∈ Perp s C b := by
  choose m' n' hmn using fun i => sdHf_int hCt hω hz (hb.mem i)
  set U' : κ → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, u j with hU'
  refine ⟨fun i => U' i * m' i, fun i => U' i * n' i, ⟨sub_mem ?_ (sum_mem fun i _ => ?_), fun j => ?_⟩⟩
  · rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hz _
  · exact okMul_mem hω (hb.mem i) _ _
  · have hU : ((∏ i, u i : ℕ) : ℂ) = (u j : ℂ) * (U' j : ℂ) := by
      rw [← Nat.cast_mul, hU', Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    refine (mul_eq_zero.mp ?_).resolve_left (Complex.ofReal_ne_zero.mpr hsd0)
    rw [Hf_sub_left, Hf_smul_left, Hf_sum_left, mul_sub, Finset.mul_sum]
    simp only [Hf_smul_left, mul_left_comm (sd : ℂ), hb.orth, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j, ite_eq_left (Finset.mem_univ j), hmn j, hU]
    push_cast
    ring

/-- **Polarisation**: if `ℓ ∣ h(z, z)` on an `ω`-stable additive set `P ⊆ C`, then `ℓ ∣ E(x, y) = Im H(x, y)` on `P`
(`2·sd·Re H(x, y) ∈ ℓℤ` from `x + y`, and from `ωx + y` also `sd·Re H − 2sd²·Im H ∈ ℓℤ`; so `d·Im H ∈ ℓℤ`, `ℓ ∤ d`). -/
theorem ell_dvd_im {d : ℕ} (hℓ : ℓ.Prime) (hdℓ : ¬ ℓ ∣ d) (h4 : 4 * sd ^ 2 = d) (hCt : IsThetaLat s sd C)
    {P : Set (ι → ℂ)} (hPC : P ⊆ C) (hadd : ∀ x ∈ P, ∀ y ∈ P, x + y ∈ P) (hωP : ∀ x ∈ P, omegaD sd • x ∈ P)
    (hdiv : ∀ z ∈ P, ∃ k : ℤ, sd * (Hf s z z).re = ℓ * k) {x y : ι → ℂ} (hx : x ∈ P) (hy : y ∈ P) :
    ∃ k : ℤ, (Hf s x y).im = ℓ * k := by
  obtain ⟨n, hn, -⟩ := hCt x (hPC hx) y (hPC hy)
  have h1 : ∀ x ∈ P, ∀ y ∈ P, ∃ a : ℤ, sd * (2 * (Hf s x y).re) = ℓ * a := by
    intro x hx y hy
    obtain ⟨k1, hk1⟩ := hdiv _ (hadd x hx y hy)
    obtain ⟨k2, hk2⟩ := hdiv x hx
    obtain ⟨k3, hk3⟩ := hdiv y hy
    refine ⟨k1 - k2 - k3, ?_⟩
    rw [Hf_add_add_re] at hk1
    push_cast
    linear_combination hk1 - hk2 - hk3
  obtain ⟨a, ha⟩ := h1 x hx y hy
  obtain ⟨b, hb⟩ := h1 _ (hωP x hx) y hy
  have hre : (Hf s (omegaD sd • x) y).re = (Hf s x y).re / 2 - sd * (Hf s x y).im := by
    rw [Hf_smul_left]
    simp [omegaD, Complex.mul_re]
    ring
  rw [hre, hn] at hb
  have key : ((d * n : ℤ) : ℝ) = ((ℓ * (a - 2 * b) : ℤ) : ℝ) := by
    push_cast
    linear_combination ha - 2 * hb - (n : ℝ) * h4
  have hdvd : (ℓ : ℤ) ∣ (d : ℤ) * n := ⟨a - 2 * b, by exact_mod_cast key⟩
  rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd hdvd with h | ⟨k, hk⟩
  · exact absurd (Int.natCast_dvd_natCast.mp h) hdℓ
  · exact ⟨k, by rw [hn, hk]; push_cast; ring⟩

/-- **Division by `ℓ` in `C ∩ b^⊥`**: if `ℓ ∣ E(w, x)` for all `w ∈ C ∩ b^⊥`, then `x/ℓ ∈ C ∩ b^⊥` (self-duality of
`C`: `U·E(z, x) = E(w, x)` for the decomposition `U·z = Σ c_i·b_i + w`, and `ℓ ∤ U`). -/
theorem inv_smul_mem (hℓ : ℓ.Prime) (hCt : IsThetaLat s sd C) (hCd : IsEDual s C)
    (hω : ∀ x ∈ C, omegaD sd • x ∈ C) (hsd0 : sd ≠ 0) {b : κ → ι → ℂ} {u : κ → ℕ} (hb : IsOrthFam ℓ s sd C b u)
    {x : ι → ℂ} (hx : x ∈ Perp s C b) (hdiv : ∀ w ∈ Perp s C b, ∃ k : ℤ, (Hf s w x).im = ℓ * k) :
    (ℓ : ℂ)⁻¹ • x ∈ Perp s C b := by
  refine ⟨hCd _ fun z hz => ?_, fun i => by rw [Hf_smul_left, hx.2 i, mul_zero]⟩
  obtain ⟨n₀, hn₀, -⟩ := hCt z hz x hx.1
  obtain ⟨m, n, hw⟩ := decomp hCt hω hsd0 hb hz
  obtain ⟨k, hk⟩ := hdiv _ hw
  have e : Hf s (((∏ i, u i : ℕ) : ℂ) • z - ∑ i, ((m i : ℂ) + n i * omegaD sd) • b i) x =
      ((∏ i, u i : ℕ) : ℂ) * Hf s z x := by
    rw [Hf_sub_left, Hf_smul_left, Hf_sum_left, sub_eq_self]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Hf_smul_left, Hf_swap s x (b i), hx.2 i, map_zero, mul_zero]
  rw [e, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, hn₀] at hk
  have hdvd : (ℓ : ℤ) ∣ ((∏ i, u i : ℕ) : ℤ) * n₀ := ⟨k, by exact_mod_cast hk⟩
  rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd hdvd with h | ⟨j, hj⟩
  · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp (Int.natCast_dvd_natCast.mp h)
    exact absurd hi (hb.u_cop i)
  · refine ⟨j, ?_⟩
    have hℓ0 : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
    rw [Hf_smul_right, show (ℓ : ℂ)⁻¹ = (((ℓ : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal,
      Complex.im_ofReal_mul, hn₀, hj]
    push_cast
    field_simp

/-- **A unit vector in a nonzero complement**: if `C ∩ b^⊥ ≠ 0`, it contains `x` with `h(x, x) = m ∈ ℕ`, `ℓ ∤ m`.
Otherwise `ℓ ∣ E` on it (`ell_dvd_im`), so it is stable under `x ↦ x/ℓ` (`inv_smul_mem`), and the positive integer
`h(x, x)` would be divisible by every `ℓ^{2k}`. -/
theorem exists_unit_perp {d : ℕ} (hℓ : ℓ.Prime) (hdℓ : ¬ ℓ ∣ d) (h4 : 4 * sd ^ 2 = d) (hsd : 0 < sd) (hs : 0 < s)
    (hCt : IsThetaLat s sd C) (hCd : IsEDual s C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {b : κ → ι → ℂ}
    {u : κ → ℕ} (hb : IsOrthFam ℓ s sd C b u) (hne : ∃ x ∈ Perp s C b, x ≠ 0) :
    ∃ x ∈ Perp s C b, ∃ m : ℕ, 0 < m ∧ ¬ ℓ ∣ m ∧ (sd : ℂ) * Hf s x x = m := by
  have hP : ∀ x ∈ Perp s C b, ∀ y ∈ Perp s C b, x + y ∈ Perp s C b := fun x hx y hy =>
    ⟨add_mem hx.1 hy.1, fun i => by rw [Hf_add_left, hx.2 i, hy.2 i, add_zero]⟩
  have hωP : ∀ x ∈ Perp s C b, omegaD sd • x ∈ Perp s C b := fun x hx =>
    ⟨hω x hx.1, fun i => by rw [Hf_smul_left, hx.2 i, mul_zero]⟩
  -- `h(z, z) = sd·Re H(z, z)` is a nonnegative integer, positive for `z ≠ 0`
  have hval : ∀ z ∈ C, ∃ m : ℤ, (sd : ℂ) * Hf s z z = m ∧ sd * (Hf s z z).re = m ∧ (z ≠ 0 → 0 < m) := by
    intro z hz
    obtain ⟨m, hm⟩ := sdHf_self_int hCt hω hz
    have hre : sd * (Hf s z z).re = m := by
      simpa [Complex.mul_re, Hf_self_im] using congrArg Complex.re hm
    refine ⟨m, hm, hre, fun hz0 => ?_⟩
    have := mul_pos hsd (Hf_self_re_pos hs hz0)
    rw [hre] at this
    exact_mod_cast this
  by_contra hcon
  push Not at hcon
  have hdiv : ∀ z ∈ Perp s C b, ∃ k : ℤ, sd * (Hf s z z).re = ℓ * k := by
    intro z hz
    obtain ⟨m, hm, hre, hpos⟩ := hval z hz.1
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, by simp [Hf_zero_left]⟩
    have hm0 := hpos hz0
    by_cases hℓm : (ℓ : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := hℓm
      exact ⟨k, by rw [hre]; push_cast; ring⟩
    · refine absurd ?_ (hcon z hz m.toNat (by omega) fun h => hℓm ?_)
      · rw [hm]
        congr 1
        exact_mod_cast (Int.toNat_of_nonneg hm0.le).symm
      · obtain ⟨c, hc⟩ := h
        exact ⟨c, by omega⟩
  have hE : ∀ x ∈ Perp s C b, ∀ y ∈ Perp s C b, ∃ k : ℤ, (Hf s x y).im = ℓ * k :=
    fun x hx y hy => ell_dvd_im hℓ hdℓ h4 hCt (fun z hz => hz.1) hP hωP hdiv hx hy
  have hinv : ∀ x ∈ Perp s C b, (ℓ : ℂ)⁻¹ • x ∈ Perp s C b := fun x hx =>
    inv_smul_mem hℓ hCt hCd hω hsd.ne' hb hx fun w hw => hE w hw x hx
  obtain ⟨x, hx, hx0⟩ := hne
  have hpow : ∀ k : ℕ, ((ℓ : ℂ)⁻¹) ^ k • x ∈ Perp s C b := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hinv _ ih
  have hℓ1 : (1 : ℝ) < (ℓ : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
    nlinarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (sd * (Hf s x x).re) hℓ1
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hxk0 : ((ℓ : ℂ)⁻¹) ^ k • x ≠ 0 := smul_ne_zero (pow_ne_zero _ (inv_ne_zero hℓ0)) hx0
  obtain ⟨m, -, hre, hpos⟩ := hval _ (hpow k).1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos hxk0
  have e : sd * (Hf s (((ℓ : ℂ)⁻¹) ^ k • x) (((ℓ : ℂ)⁻¹) ^ k • x)).re =
      sd * (Hf s x x).re / ((ℓ : ℝ) ^ 2) ^ k := by
    rw [Hf_smul_self, Complex.re_ofReal_mul, map_pow, map_inv₀, Complex.normSq_natCast, div_eq_mul_inv]
    ring
  rw [hre] at e
  rw [e, le_div_iff₀ (pow_pos (by positivity) k), one_mul] at hm1
  exact absurd hk (not_lt.mpr hm1)

end GS

/-! ## Existence of an `ℓ`-adapted orthogonal basis -/

section Exists

variable {ι : Type*} [Fintype ι] {ℓ : ℕ} {s sd : ℝ} {C : AddSubgroup (ι → ℂ)}

/-- **Orthogonal families of every length up to `dim`**: by induction, a family of length `k < n` leaves
`C ∩ b^⊥ ≠ 0` (otherwise `C ⊆ span_ℂ b`, against `span_ℝ C = ℂ^ι`), and `exists_unit_perp` extends it. -/
theorem exists_orthFam {d : ℕ} (hℓ : ℓ.Prime) (hdℓ : ¬ ℓ ∣ d) (h4 : 4 * sd ^ 2 = d) (hsd : 0 < sd) (hs : 0 < s)
    (hCt : IsThetaLat s sd C) (hCd : IsEDual s C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C)
    (hspan : Submodule.span ℝ (C : Set (ι → ℂ)) = ⊤) :
    ∀ k ≤ Fintype.card ι, ∃ (b : Fin k → ι → ℂ) (u : Fin k → ℕ), IsOrthFam ℓ s sd C b u := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, u, hb⟩ := ih (by omega)
    have hne : ∃ x ∈ Perp s C b, x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hsub : (C : Set (ι → ℂ)) ⊆ ((Submodule.span ℂ (Set.range b)).restrictScalars ℝ : Set (ι → ℂ)) := by
        intro z hz
        obtain ⟨m, n, hw⟩ := decomp hCt hω hsd.ne' hb hz
        have h0 := hcon _ hw
        rw [sub_eq_zero] at h0
        have hU : ((∏ i, u i : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (hb.u_pos i).ne')
        have hz' : z = ((∏ i, u i : ℕ) : ℂ)⁻¹ • ∑ i, ((m i : ℂ) + n i * omegaD sd) • b i := by
          rw [← h0, smul_smul, inv_mul_cancel₀ hU, one_smul]
        rw [Submodule.coe_restrictScalars, SetLike.mem_coe, hz']
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      have htop : Submodule.span ℂ (Set.range b) = ⊤ := by
        rw [eq_top_iff]
        intro v _
        have hv : v ∈ Submodule.span ℝ (C : Set (ι → ℂ)) := by
          rw [hspan]
          exact Submodule.mem_top
        exact Submodule.span_le.mpr hsub hv
      have h1 := finrank_range_le_card (R := ℂ) b
      rw [Set.finrank, htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx, m, hm0, hmℓ, hxx⟩ := exists_unit_perp hℓ hdℓ h4 hsd hs hCt hCd hω hb hne
    refine ⟨Fin.cons x b, Fin.cons m u, ⟨fun i => ?_, fun i => ?_, fun i j => ?_, fun i => ?_⟩⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hm0
      · simpa using hb.u_pos i
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hmℓ
      · simpa using hb.u_cop i
    · refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
      · simpa using hxx
      · simp [hx.2 j, (Fin.succ_ne_zero j).symm]
      · simp [Hf_swap s x (b i), hx.2 i, Fin.succ_ne_zero]
      · simpa [Fin.succ_inj] using hb.orth i j
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hx.1
      · simpa using hb.mem i

/-- **Existence of an `ℓ`-adapted orthogonal basis with unit diagonal** (`h = sd·H`, `ℓ` inert in `K₀`): by
induction (`exists_orthFam`) an orthogonal family with unit diagonal of length `n = dim_ℂ`; a nonzero vector of
`C ∩ b^⊥` would make `n + 1` orthogonal vectors (`linIndep_orth`), so `C ∩ b^⊥ = 0` and the decomposition
(`decomp`) gives `U·C ⊆ ⊕ ℤ[ω]·b_i`, `U = Π u_i`. Neither discreteness nor `ℓ ≠ 2` is used: `ℓ ∤ d`, read off from
inertness, suffices. -/
theorem exists_gsBasis [DecidableEq ι] {ℓ : ℕ} [Fact ℓ.Prime] (_hℓ2 : ℓ ≠ 2) {d : ℕ} {sd : ℝ}
    (hsd : sd = Real.sqrt d / 2) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) {C : AddSubgroup (ι → ℂ)}
    (hCt : IsThetaLat (sC sd) sd C) (hCd : IsEDual (sC sd) C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C)
    (_hdisc : DiscreteTopology C) (hspan : Submodule.span ℝ (C : Set (ι → ℂ)) = ⊤) :
    Nonempty (GSBasis ℓ (sC sd) sd (omegaD sd) C) := by
  have hℓ := (Fact.out : ℓ.Prime)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hin ⟨0, by rw [Nat.cast_zero]; exact (zero_pow two_ne_zero).trans neg_zero.symm⟩
  have hdℓ : ¬ ℓ ∣ d := fun h => hin ⟨0, by
    rw [(ZMod.natCast_eq_zero_iff d ℓ).mpr h]
    exact (zero_pow two_ne_zero).trans neg_zero.symm⟩
  have hsd0 : 0 < sd := by
    rw [hsd]
    exact div_pos (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd0)) two_pos
  have hs := sC_pos sd
  obtain ⟨b, u, hb⟩ := exists_orthFam hℓ hdℓ (sd_sq hsd) hsd0 hs hCt hCd hω hspan _ le_rfl
  have hW : ∀ x ∈ Perp (sC sd) C b, x = 0 := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℂ (Fin.cons x b : Fin (Fintype.card ι + 1) → ι → ℂ) := by
      refine linIndep_orth hs (fun i j hij => ?_) (fun i => ?_)
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hx.2 j
        | succ i =>
          induction j using Fin.cases with
          | zero => simp [Hf_swap _ x (b i), hx.2 i]
          | succ j => simpa using hb.Hf_eq_zero hsd0.ne' fun h => hij (by rw [h])
      · induction i using Fin.cases with
        | zero => simpa using hx0
        | succ i => simpa using hb.ne_zero i
    have h1 := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h1
    omega
  let e := Fintype.equivFin ι
  refine ⟨⟨fun i => b (e i), fun i => u (e i), ∏ j, u j, ?_, ?_, fun i => hb.u_pos _, fun i => hb.u_cop _,
    fun i j => ?_, fun i => hb.mem _, fun x hx => ?_⟩⟩
  · exact Finset.prod_pos fun j _ => hb.u_pos j
  · intro h
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp h
    exact hb.u_cop j hj
  · rw [hb.orth]
    simp [e.injective.eq_iff]
  · obtain ⟨m, n, hw⟩ := decomp hCt hω hsd0.ne' hb hx
    have h0 := hW _ hw
    rw [sub_eq_zero] at h0
    rw [← Nat.cast_smul_eq_nsmul ℂ, h0]
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨e.symm j, m j, n j, by simp⟩

end Exists

/-! ## Four squares: an `ℓ`-adapted orthonormal basis of `C⁴` -/

section Quat

/-- **Left multiplication by the quaternion `a + bi + cj + dk`**; `quatL·quatLᵀ = (a² + b² + c² + d²)·1`. -/
def quatL (a b c d : ℤ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(a : ℚ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

/-- **`quatL` over `ℤ`.** -/
def quatZ (a b c d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![a, -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

/-- **The entries of `quatL` are integers.** -/
theorem quatL_apply (a b c d : ℤ) (k l : Fin 4) : quatL a b c d k l = (quatZ a b c d k l : ℚ) := by
  fin_cases k <;> fin_cases l <;> simp [quatL, quatZ]

/-- **`quatL` is a similitude**: `quatL·quatLᵀ = (a² + b² + c² + d²)·1`. -/
theorem quatL_mul_transpose (a b c d : ℤ) :
    quatL a b c d * (quatL a b c d).transpose = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℚ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatL, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **`quatLᵀ·quatL = (a² + b² + c² + d²)·1`.** -/
theorem transpose_mul_quatL (a b c d : ℤ) :
    (quatL a b c d).transpose * quatL a b c d = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℚ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatL, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

variable {ι : Type*} [Fintype ι] {s sd : ℝ}

/-- **The four-squares map** `g : ℂ^{Fin 4 × ι} → ℂ^{Fin 4 × ι}`,
`g(e_{k,i}) = δ⁻¹·u_i⁻¹·Σ_l Q_i(k, l)·slot_l(b_i)` (for `Q_i = quatL` of `u_i = a_i² + b_i² + c_i² + d_i²`). -/
def orth4 (δ : ℂ) (b : ι → (ι → ℂ)) (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ) :
    (Fin 4 × ι → ℂ) →ₗ[ℂ] (Fin 4 × ι → ℂ) where
  toFun z := ∑ p : Fin 4 × ι, z p • (δ⁻¹ * (u p.2 : ℂ)⁻¹) • ∑ l, ((Q p.2 p.1 l : ℚ) : ℂ) • slotV l (b p.2)
  map_add' z w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

/-- **The image `f_p = g(e_p)` of a basis vector.** -/
def orth4Vec (δ : ℂ) (b : ι → (ι → ℂ)) (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ) (p : Fin 4 × ι) :
    Fin 4 × ι → ℂ :=
  (δ⁻¹ * (u p.2 : ℂ)⁻¹) • ∑ l, ((Q p.2 p.1 l : ℚ) : ℂ) • slotV l (b p.2)

/-- **`g(z) = Σ_p z_p·f_p`.** -/
theorem orth4_apply (δ : ℂ) (b : ι → (ι → ℂ)) (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ)
    (z : Fin 4 × ι → ℂ) : orth4 δ b u Q z = ∑ p, z p • orth4Vec δ b u Q p :=
  rfl

/-- **`H` of two linear combinations.** -/
theorem Hf_sum_smul_sum {κ κ' ι' : Type*} [Fintype ι'] (t : Finset κ) (t' : Finset κ') (a : κ → ℂ) (v : κ → ι' → ℂ)
    (a' : κ' → ℂ) (w : κ' → ι' → ℂ) :
    Hf s (∑ l ∈ t, a l • v l) (∑ l' ∈ t', a' l' • w l') =
      ∑ l ∈ t, ∑ l' ∈ t', a l * starRingEnd ℂ (a' l') * Hf s (v l) (w l') := by
  rw [Hf_sum_left]
  simp only [Hf_smul_left, Hf_sum_right, Hf_smul_right]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring

/-- **An `H`-orthonormal family defines an isometry**: if `H(f_p, f_q) = s·δ_pq`, then
`H(Σ z_p f_p, Σ w_q f_q) = H(z, w)`. -/
theorem Hf_sum_orthonormal {κ ι' : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι'] (F : κ → ι' → ℂ)
    (hF : ∀ p q, Hf s (F p) (F q) = if p = q then (s : ℂ) else 0) (z w : κ → ℂ) :
    Hf s (∑ p, z p • F p) (∑ q, w q • F q) = Hf s z w := by
  rw [Hf_sum_smul_sum]
  simp only [hF, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **The rows of a similitude**: `Q·Qᵀ = u·1` gives `Σ_l Q_{kl}Q_{k'l} = u·δ_{kk'}` in `ℂ`. -/
theorem sum_rows_cast {Q : Matrix (Fin 4) (Fin 4) ℚ} {u : ℕ} (h : Q * Q.transpose = (u : ℚ) • 1) (k k' : Fin 4) :
    ∑ l, ((Q k l : ℚ) : ℂ) * ((Q k' l : ℚ) : ℂ) = if k = k' then (u : ℂ) else 0 := by
  have hQe := congrFun (congrFun h k) k'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero] at hQe
  split_ifs at hQe ⊢ <;> exact_mod_cast hQe

/-- **The columns of a similitude**: `Qᵀ·Q = u·1` gives `Σ_k Q_{kl}Q_{kl'} = u·δ_{ll'}` in `ℂ`. -/
theorem sum_cols_cast {Q : Matrix (Fin 4) (Fin 4) ℚ} {u : ℕ} (h : Q.transpose * Q = (u : ℚ) • 1) (l l' : Fin 4) :
    ∑ k, ((Q k l : ℚ) : ℂ) * ((Q k l' : ℚ) : ℂ) = if l = l' then (u : ℂ) else 0 := by
  have hQe := congrFun (congrFun h l) l'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero] at hQe
  split_ifs at hQe ⊢ <;> exact_mod_cast hQe

variable [DecidableEq ι]

/-- **The images of the basis vectors are `H`-orthonormal** (for `h(b_i, b_j) = u_i·δ_ij`, `Q_iQ_iᵀ = u_i·1` and
`s·|δ|²·sd = 1`): `H(f_{k,i}, f_{k',j}) = |δ|⁻²u_i⁻¹u_j⁻¹·(Q_iQ_jᵀ)_{kk'}·H(b_i, b_j)`. -/
theorem Hf_orth4Vec {δ : ℂ} {b : ι → (ι → ℂ)} {u : ι → ℕ} {Q : ι → Matrix (Fin 4) (Fin 4) ℚ}
    (hb : ∀ i j, (sd : ℂ) * Hf s (b i) (b j) = if i = j then (u i : ℂ) else 0) (hsd0 : sd ≠ 0)
    (hu : ∀ i, u i ≠ 0) (hQ : ∀ i, Q i * (Q i).transpose = (u i : ℚ) • 1)
    (hn : s * Complex.normSq δ * sd = 1) (p q : Fin 4 × ι) :
    Hf s (orth4Vec δ b u Q p) (orth4Vec δ b u Q q) = if p = q then (s : ℂ) else 0 := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', j⟩ := q
  have hsdC : (sd : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsd0
  simp only [orth4Vec, Hf_smul_left, Hf_smul_right, Hf_sum_smul_sum, Hf_slotV, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_ratCast]
  by_cases hij : i = j
  · subst hij
    have hQc : ∑ l, ((Q i k l : ℚ) : ℂ) * ((Q i k' l : ℚ) : ℂ) * Hf s (b i) (b i) =
        (if k = k' then (u i : ℂ) else 0) * Hf s (b i) (b i) := by
      rw [← Finset.sum_mul, sum_rows_cast (hQ i)]
    have hHb : Hf s (b i) (b i) = (u i : ℂ) / sd := by
      rw [eq_div_iff hsdC, mul_comm, hb i i, ite_eq_left rfl]
    rw [hQc, hHb]
    have hu0 : (u i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hu i)
    have hδ : δ ≠ 0 := by
      rintro rfl
      simp at hn
    have hnC : (s : ℂ) * (Complex.normSq δ : ℂ) * sd = 1 := by exact_mod_cast hn
    have hδc : starRingEnd ℂ δ ≠ 0 := (map_ne_zero _).mpr hδ
    by_cases hkk : k = k'
    · subst hkk
      rw [ite_eq_left rfl, ite_eq_left rfl, map_mul, map_inv₀, map_inv₀, Complex.conj_natCast]
      rw [Complex.normSq_eq_conj_mul_self] at hnC
      have hs' : (s : ℂ) = (starRingEnd ℂ δ * δ * sd)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hnC)
      rw [hs']
      field_simp
    · rw [ite_eq_right hkk, ite_eq_right (fun h => hkk (Prod.mk.inj h).1)]
      ring
  · have hH : Hf s (b i) (b j) = 0 := by
      have := hb i j
      rw [ite_eq_right hij] at this
      exact (mul_eq_zero.mp this).resolve_left hsdC
    rw [ite_eq_right (fun h => hij (Prod.mk.inj h).2)]
    simp [hH]

omit [Fintype ι] [DecidableEq ι] in
/-- **The slot vectors in the orthonormal basis**: `slot_l(b_i) = Σ_k Q_i(k, l)·δ·f_{k,i}` (`Q_iᵀQ_i = u_i·1`). -/
theorem slotV_eq_sum {δ : ℂ} {b : ι → (ι → ℂ)} {u : ι → ℕ} {Q : ι → Matrix (Fin 4) (Fin 4) ℚ} (hδ : δ ≠ 0)
    (hu : ∀ i, u i ≠ 0) (hQ : ∀ i, (Q i).transpose * Q i = (u i : ℚ) • 1) (l : Fin 4) (i : ι) :
    slotV l (b i) = ∑ k, (((Q i k l : ℚ) : ℂ) * δ) • orth4Vec δ b u Q (k, i) := by
  have hu0 : (u i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hu i)
  have hc : ∀ l', ∑ k, ((Q i k l : ℚ) : ℂ) * δ * ((δ⁻¹ * (u i : ℂ)⁻¹) * ((Q i k l' : ℚ) : ℂ)) =
      if l = l' then 1 else 0 := by
    intro l'
    have e : ∑ k, ((Q i k l : ℚ) : ℂ) * δ * ((δ⁻¹ * (u i : ℂ)⁻¹) * ((Q i k l' : ℚ) : ℂ)) =
        (u i : ℂ)⁻¹ * ∑ k, ((Q i k l : ℚ) : ℂ) * ((Q i k l' : ℚ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [e, sum_cols_cast (hQ i)]
    split_ifs
    · exact inv_mul_cancel₀ hu0
    · exact mul_zero _
  simp only [orth4Vec, smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Quat

/-! ## The four-squares isometry is `ℓ`-adapted to `C⁴` -/

section Orth4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A lattice vector in one coordinate** lies in `Lc^κ`. -/
theorem single_mem_stdLc {κ : Type*} [DecidableEq κ] {sd : ℝ} {p : κ} {c : ℂ} (hc : c ∈ (cmLat sd).lattice) :
    Pi.single p c ∈ stdLc sd κ :=
  mem_stdLc.mpr fun q => by
    by_cases h : q = p
    · subst h
      simpa using hc
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _

/-- **`g(c·e_p) = c·f_p`.** -/
theorem orth4_single (δ : ℂ) (b : ι → (ι → ℂ)) (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ)
    (p : Fin 4 × ι) (c : ℂ) : orth4 δ b u Q (Pi.single p c) = c • orth4Vec δ b u Q p := by
  rw [orth4_apply, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq, zero_smul])
    (fun h => absurd (Finset.mem_univ p) h), Pi.single_eq_same]

/-- **The four-squares isometry** (`u_i = a_i² + b_i² + c_i² + e_i²`, Lagrange): `g = orth4(δ, b, u, quatL)` is a
bijective `H`-isometry, and `g(Lc^{Fin 4 × ι})` has the `ℓ`-part of `C⁴`, with multiplier `M·Π_i u_i`. The
orthonormality is `quatL·quatLᵀ = u·1` and `s·|δ|²·sd = 1`; `M·C ⊆ ⊕ ℤ[ω]b_i` and `slot_l(b_i) = Σ_k
quatL_i(k, l)·δ·f_{k,i}` give `M·C⁴ ⊆ g(Lc⁴)`, and `u_i·f_{k,i} ∈ ⊕_l ℤ·slot_l(b_i)` gives the converse, for which
`C` must be `ω`-stable (`hω`, an addition to the spec's statement: without it `C = ℤb + ℤℓωb` is a counterexample). -/
theorem orth4_spec {ℓ : ℕ} [Fact ℓ.Prime] {d : ℕ} {sd : ℝ} (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) {C : AddSubgroup (ι → ℂ)} (B : GSBasis ℓ (sC sd) sd (omegaD sd) C)
    (a b c e : ι → ℤ) (hsq : ∀ i, a i ^ 2 + b i ^ 2 + c i ^ 2 + e i ^ 2 = B.u i)
    (hω : ∀ x ∈ C, omegaD sd • x ∈ C) :
    let g := orth4 (deltaC sd) B.b B.u fun i => quatL (a i) (b i) (c i) (e i)
    Function.Bijective g ∧ (∀ z w, Hf (sC sd) (g z) (g w) = Hf (sC sd) z w) ∧
      LAdapted ℓ (pow4 C) ((stdLc sd (Fin 4 × ι)).map g.toAddMonoidHom) := by
  dsimp only
  set Q : ι → Matrix (Fin 4) (Fin 4) ℚ := fun i => quatL (a i) (b i) (c i) (e i) with hQdef
  set g := orth4 (deltaC sd) B.b B.u Q with hg
  have hℓ := (Fact.out : ℓ.Prime)
  have hs : 0 < sC sd := sC_pos sd
  have hδ : deltaC sd ≠ 0 := deltaC_ne_zero hΔ
  have hu : ∀ i, B.u i ≠ 0 := fun i => (B.u_pos i).ne'
  have hsdpos : ∀ _ : ι, 0 < sd := fun i => by
    have h := B.orth i i
    rw [ite_eq_left rfl] at h
    have hne : sd ≠ 0 := by
      rintro rfl
      rw [Complex.ofReal_zero, zero_mul] at h
      exact hu i (by exact_mod_cast h.symm)
    have hge : 0 ≤ sd := by
      rw [hsd]
      positivity
    exact lt_of_le_of_ne hge (Ne.symm hne)
  have hQZ : ∀ i k l, Q i k l = (quatZ (a i) (b i) (c i) (e i) k l : ℚ) := fun i k l => quatL_apply _ _ _ _ k l
  have hQ1 : ∀ i, Q i * (Q i).transpose = (B.u i : ℚ) • 1 := fun i => by
    rw [hQdef, quatL_mul_transpose, hsq i]
    norm_cast
  have hQ2 : ∀ i, (Q i).transpose * Q i = (B.u i : ℚ) • 1 := fun i => by
    rw [hQdef, transpose_mul_quatL, hsq i]
    norm_cast
  have hF : ∀ p q, Hf (sC sd) (orth4Vec (deltaC sd) B.b B.u Q p) (orth4Vec (deltaC sd) B.b B.u Q q) =
      if p = q then (sC sd : ℂ) else 0 := fun p q =>
    Hf_orth4Vec B.orth (hsdpos p.2).ne' hu hQ1 (sC_mul_normSq (hsdpos p.2) hΔ) p q
  have hiso : ∀ z w, Hf (sC sd) (g z) (g w) = Hf (sC sd) z w := fun z w => by
    rw [hg, orth4_apply, orth4_apply]
    exact Hf_sum_orthonormal _ hF z w
  have hinj : Function.Injective g := by
    intro z w hzw
    by_contra hne
    have h0 := Hf_self_re_pos hs (sub_ne_zero.mpr hne)
    rw [← hiso, map_sub, hzw, sub_self, Hf_zero_left, Complex.zero_re] at h0
    exact lt_irrefl _ h0
  refine ⟨⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, hiso, ?_⟩
  set T := (stdLc sd (Fin 4 × ι)).map g.toAddMonoidHom with hT
  refine ⟨B.M * ∏ i, B.u i, Nat.mul_pos B.M_pos (Finset.prod_pos fun i _ => B.u_pos i), ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact B.M_cop h
    · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp h
      exact B.u_cop i hi
  · -- `M·C⁴ ⊆ g(Lc⁴)`: the slots of the generators `(m + nω)·b_i` of the `ℤ[ω]`-span lie in `g(Lc⁴)`
    have hgen : ∀ l : Fin 4, okSpan (omegaD sd) B.b ≤ T.comap (slotHom l) := by
      intro l
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨i, m, n, rfl⟩
      show slotV l (((m : ℂ) + n * omegaD sd) • B.b i) ∈ T
      rw [slotV_smul, slotV_eq_sum hδ hu hQ2 l i, Finset.smul_sum]
      refine AddSubgroup.sum_mem _ fun k _ => ?_
      rw [smul_smul, ← orth4_single]
      refine AddSubgroup.mem_map_of_mem _ (single_mem_stdLc ((mem_cmLat_iff (hsdpos i) hΔ).mpr
        ⟨m * quatZ (a i) (b i) (c i) (e i) k l, n * quatZ (a i) (b i) (c i) (e i) k l, ?_⟩))
      rw [hQZ]
      push_cast
      ring
    intro x hx
    have hx' : B.M • x = ∑ l, slotHom l (B.M • slice l x) := by
      conv_lhs => rw [← sum_slotV_slice x]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      show B.M • slotV l (slice l x) = slotV l (B.M • slice l x)
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, slotV_smul]
    have hMx : B.M • x ∈ T := by
      rw [hx']
      exact AddSubgroup.sum_mem _ fun l _ => hgen l (B.span _ (slice_mem_pow4 hx l))
    rw [mul_comm, ← smul_smul]
    exact nsmul_mem hMx _
  · -- `M·g(Lc⁴) ⊆ C⁴`: `u_i·f_{k,i} ∈ ⊕_l ℤ·slot_l(b_i)`
    rintro _ ⟨z, hz, rfl⟩
    show (B.M * ∏ i, B.u i) • g z ∈ pow4 C
    rw [hg, orth4_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun p _ => ?_
    obtain ⟨k, i⟩ := p
    obtain ⟨m, n, hmn⟩ := (mem_cmLat_iff (hsdpos i) hΔ).mp (mem_stdLc.mp hz (k, i))
    have hS : ∑ l, ((Q i k l : ℚ) : ℂ) • slotV l (B.b i) ∈ pow4 C := by
      refine AddSubgroup.sum_mem _ fun l _ => ?_
      rw [hQZ, Rat.cast_intCast, Int.cast_smul_eq_zsmul]
      exact zsmul_mem (slotV_mem_pow4 (B.mem i) l) _
    have hprod : ((∏ j, B.u j : ℕ) : ℂ) = (B.u i : ℂ) * ((∏ j ∈ Finset.univ.erase i, B.u j : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have hu0 : (B.u i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hu i)
    have e : (B.M * ∏ j, B.u j) • (z (k, i) • orth4Vec (deltaC sd) B.b B.u Q (k, i)) =
        (B.M * ∏ j ∈ Finset.univ.erase i, B.u j) •
          (((m : ℂ) + n * omegaD sd) • ∑ l, ((Q i k l : ℚ) : ℂ) • slotV l (B.b i)) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, orth4Vec, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [Nat.cast_mul, Nat.cast_mul, hprod, hmn]
      field_simp
    rw [e]
    exact nsmul_mem (okMul_mem (fun v hv => pow4_smul_mem hω hv) hS m n) _

end Orth4

/-! ## Commensurability -/

section Commens

/-- **`ℓ`-adapted lattices are commensurable** when one of them is finitely generated: `M·Λ₂ ⊆ Λ₁ ∩ Λ₂` has finite
index in `Λ₂` (`Λ₂/MΛ₂` is finitely generated and torsion), and `x ↦ M·x mod MΛ₂` embeds `Λ₁/(Λ₁ ∩ Λ₂)` in it. -/
theorem isCommens_of_lAdapted {κ : Type*} {ℓ : ℕ} {Λ₁ Λ₂ : AddSubgroup (κ → ℂ)} (h : LAdapted ℓ Λ₁ Λ₂)
    (hfg : Λ₂.FG) : IsCommens Λ₁ Λ₂ := by
  obtain ⟨M, hM0, -, h12, h21⟩ := h
  have : AddGroup.FG Λ₂ := (AddGroup.fg_iff_addSubgroup_fg Λ₂).mpr hfg
  let mulM : Λ₂ →+ Λ₂ :=
    { toFun := fun x => M • x, map_zero' := smul_zero _, map_add' := fun x y => smul_add _ x y }
  set N := mulM.range with hN
  have hfin : Finite (Λ₂ ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M, hM0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨a, rfl⟩
  have hNi : N.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hcancel : ∀ x y : κ → ℂ, M • x = M • y → x = y := fun x y hxy => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hxy
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hM0.ne') hxy
  refine ⟨?_, ?_⟩
  · let φ : Λ₁ →+ Λ₂ ⧸ N :=
      (QuotientAddGroup.mk' N).comp
        { toFun := fun x => ⟨M • (x : κ → ℂ), h12 _ x.2⟩
          map_zero' := by ext; simp
          map_add' := fun x y => by ext; simp [smul_add] }
    have hker : φ.ker ≤ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₁ := by
      intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hx
      have e : (a : κ → ℂ) = x := hcancel _ _ (congrArg Subtype.val ha)
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
      exact ⟨x.2, e ▸ a.2⟩
    have hk : φ.ker.index ≠ 0 := by
      rw [AddSubgroup.index_ker]
      exact Nat.card_pos.ne'
    exact ne_zero_of_dvd_ne_zero hk (AddSubgroup.index_dvd_of_le hker)
  · have hle : N ≤ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂ := by
      rintro _ ⟨a, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
      exact ⟨h21 _ a.2, (mulM a).2⟩
    exact ne_zero_of_dvd_ne_zero hNi (AddSubgroup.index_dvd_of_le hle)

/-- **`Lc^κ` is finitely generated**, by the `δ·e_p` and `δω·e_p`. -/
theorem fg_stdLc {κ : Type*} [Finite κ] [DecidableEq κ] {sd : ℝ} (hsd : ∀ _ : κ, 0 < sd)
    (hΔ : discr (baseLat sd) ≠ 0) : (stdLc sd κ).FG := by
  set S : Set (κ → ℂ) :=
    Set.range fun x : κ × Bool => Pi.single x.1 (if x.2 then deltaC sd else deltaC sd * omegaD sd) with hS
  refine (AddSubgroup.fg_iff _).mpr ⟨S, ?_, Set.finite_range _⟩
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ?_) fun z hz => ?_
  · rintro _ ⟨⟨p, t⟩, rfl⟩
    refine single_mem_stdLc ((mem_cmLat_iff (hsd p) hΔ).mpr ?_)
    cases t
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 0, by simp⟩
  · have : Fintype κ := Fintype.ofFinite κ
    rw [← Finset.univ_sum_single z]
    refine AddSubgroup.sum_mem _ fun p _ => ?_
    obtain ⟨m, n, hmn⟩ := (mem_cmLat_iff (hsd p) hΔ).mp (mem_stdLc.mp hz p)
    have e : (Pi.single p (z p) : κ → ℂ) = m • (Pi.single p (deltaC sd) : κ → ℂ) +
        n • (Pi.single p (deltaC sd * omegaD sd) : κ → ℂ) := by
      ext q
      by_cases h : q = p
      · subst h
        simp [hmn]
        ring
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    have h1 : (Pi.single p (deltaC sd) : κ → ℂ) ∈ S := ⟨(p, true), by simp⟩
    have h2 : (Pi.single p (deltaC sd * omegaD sd) : κ → ℂ) ∈ S := ⟨(p, false), by simp⟩
    exact add_mem (zsmul_mem (AddSubgroup.subset_closure h1) m) (zsmul_mem (AddSubgroup.subset_closure h2) n)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`C⁴` and `g(Lc^{Fin 4 × ι})` are commensurable** for the four-squares isometry `g` (`orth4_spec`,
`isCommens_of_lAdapted`, `fg_stdLc`): the hypothesis `hc` of `ThetaCompare.theta_compare` for `θ^{⊗4}`. -/
theorem isCommens_orth4 {ℓ : ℕ} [Fact ℓ.Prime] {d : ℕ} {sd : ℝ} (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) {C : AddSubgroup (ι → ℂ)} (B : GSBasis ℓ (sC sd) sd (omegaD sd) C)
    (a b c e : ι → ℤ) (hsq : ∀ i, a i ^ 2 + b i ^ 2 + c i ^ 2 + e i ^ 2 = B.u i)
    (hω : ∀ x ∈ C, omegaD sd • x ∈ C) :
    IsCommens (pow4 C) ((stdLc sd (Fin 4 × ι)).map
      (orth4 (deltaC sd) B.b B.u fun i => quatL (a i) (b i) (c i) (e i)).toAddMonoidHom) := by
  refine isCommens_of_lAdapted (orth4_spec hsd hΔ B a b c e hsq hω).2.2 ?_
  have hsd0 : ∀ _ : Fin 4 × ι, 0 < sd := fun p => by
    have h := B.orth p.2 p.2
    rw [ite_eq_left rfl] at h
    have hne : sd ≠ 0 := by
      rintro rfl
      rw [Complex.ofReal_zero, zero_mul] at h
      exact (B.u_pos p.2).ne' (by exact_mod_cast h.symm)
    have hge : 0 ≤ sd := by
      rw [hsd]
      positivity
    exact lt_of_le_of_ne hge (Ne.symm hne)
  obtain ⟨S, hS, hSf⟩ := (AddSubgroup.fg_iff _).mp (fg_stdLc hsd0 hΔ)
  refine (AddSubgroup.fg_iff _).mpr ⟨_, ?_, hSf.image (orth4 (deltaC sd) B.b B.u fun i =>
    quatL (a i) (b i) (c i) (e i)).toAddMonoidHom⟩
  rw [← hS, AddMonoidHom.map_closure]

end Commens
end

end HermGS
