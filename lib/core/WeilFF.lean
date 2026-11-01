/-
# Weil's criterion over a finite field

Plain statement. Let `β₁, …, β_m` be nonzero complex numbers, closed under `β ↦ 1/β̄`: there is a permutation `σ` of
the indices with `β_{σ(i)} = 1/conj(β_i)`. Put `k(d) = Σ_i β_i^d` for `d ∈ ℤ`. The following are equivalent
(`posDef_iff`, `posDef_iff_bdd`):
* every `|β_i| = 1`;
* `k` is a positive-definite function on `ℤ`: `Σ_{j,l ∈ S} x_j x̄_l k(j − l) ≥ 0` for every finite `S ⊂ ℤ` and all
  complex `x`;
* `k(d)` is bounded for `d ≥ 0`.

In terms of point counts (`countKernel_posDef_iff`): let `q > 0`, let `α₁, …, α_m` be nonzero and closed under
`α ↦ q/ᾱ`, and let `N_d = q^d + 1 − Σ_i α_i^d` for `d ≥ 1`. The kernel `c(d) = (q^{|d|} + 1 − N_{|d|})/q^{|d|/2}`,
`c(0) = m`, is positive-definite on `ℤ` exactly when every `|α_i| = √q`. A bound `|q^d + 1 − N_d| ≤ Cq^{d/2}` in every
degree already gives `|α_i| = √q` (`norm_eq_sqrt_of_bound`).

For a curve over `𝔽_q` with zeta function `P(T)/((1 − T)(1 − qT))`, `P(T) = Π_i (1 − α_iT)`, the `N_d` are its point
counts over `𝔽_{q^d}`, the closure is the functional equation, and `|α_i| = √q` is the Riemann hypothesis. So the
Riemann hypothesis for the curve is the positive-definiteness of a kernel computed from the point counts alone. For an
elliptic curve that positivity is `ManinHasse.toeplitz_nonneg`, whose kernel is `c/2`.
* Positive-definite to bounded: the `2 × 2` minors give `|k(d)| ≤ 2k(0)` (`norm_le_of_posDef`).
* Bounded to `|β_i| ≤ 1`: write `k(d) = Σ_v c_v v^d` over the distinct values `v`, with multiplicities `c_v ≥ 1`. The
  Vandermonde matrix of the `v` is invertible, so each `c_v v^d` is a fixed combination of `k(d), …, k(d + n − 1)` and
  is bounded in `d` (`norm_le_one_of_bdd`).
* The closure turns `|β_i| ≤ 1` into `|β_i| = 1` (`norm_eq_one_of_bdd`). On the circle,
  `Σ_{j,l} x_j x̄_l k(j − l) = Σ_i |Σ_j x_jβ_i^j|²` (`posDef_of_norm_eq_one`).
* A real even kernel with `Σ_{i,j<K} y_iy_j c(i − j) ≥ 0` for all real `y`, the form of `ManinHasse.toeplitz_nonneg`,
  is positive-definite in this sense (`posDef_of_real`).

This is the first part of the fourth of the first steps in `docs/ball-conjecture.md`.
-/
import Mathlib

open Complex Finset ComplexConjugate
open scoped ComplexOrder

namespace WeilFF

/-- A function `k : ℤ → ℂ` is **positive-definite** when `Σ_{j,l ∈ S} x_j x̄_l k(j − l) ≥ 0` for every finite set `S`
and all complex `x`. In `ℂ`'s order this says that the sum is real and nonnegative. -/
def PosDef (k : ℤ → ℂ) : Prop :=
  ∀ (S : Finset ℤ) (x : ℤ → ℂ), 0 ≤ ∑ j ∈ S, ∑ l ∈ S, x j * conj (x l) * k (j - l)

variable {ι : Type*} [Fintype ι]

/-- The kernel `k(d) = Σ_i β_i^d` of a finite family of complex numbers. -/
noncomputable def kernel (β : ι → ℂ) (d : ℤ) : ℂ := ∑ i, β i ^ d

/-- **On the circle the kernel is positive-definite**: `Σ_{j,l} x_j x̄_l k(j − l) = Σ_i |Σ_j x_jβ_i^j|²`. -/
theorem posDef_of_norm_eq_one (β : ι → ℂ) (h : ∀ i, ‖β i‖ = 1) : PosDef (kernel β) := by
  intro S x
  have key : ∀ i, ∑ j ∈ S, ∑ l ∈ S, x j * conj (x l) * β i ^ (j - l) =
      (∑ j ∈ S, x j * β i ^ j) * conj (∑ l ∈ S, x l * β i ^ l) := by
    intro i
    have h0 : β i ≠ 0 := by
      intro h0
      have := h i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have hl : ‖β i ^ l‖ = 1 := by rw [norm_zpow, h i, one_zpow]
    rw [zpow_sub₀ h0, div_eq_mul_inv, Complex.inv_eq_conj hl, map_mul]
    ring
  calc (0 : ℂ) ≤ ∑ i, (∑ j ∈ S, x j * β i ^ j) * conj (∑ l ∈ S, x l * β i ^ l) :=
        Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
    _ = ∑ i, ∑ j ∈ S, ∑ l ∈ S, x j * conj (x l) * β i ^ (j - l) :=
        Finset.sum_congr rfl fun i _ => (key i).symm
    _ = ∑ j ∈ S, ∑ i, ∑ l ∈ S, x j * conj (x l) * β i ^ (j - l) := Finset.sum_comm
    _ = ∑ j ∈ S, ∑ l ∈ S, x j * conj (x l) * kernel β (j - l) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [kernel, Finset.mul_sum]
        exact Finset.sum_comm

/-- **The `2 × 2` minors**: a positive-definite `k` has `|k(d)| ≤ 2 re k(0)`. -/
theorem norm_le_of_posDef {k : ℤ → ℂ} (hk : PosDef k) (d : ℤ) : ‖k d‖ ≤ 2 * (k 0).re := by
  have h00 := hk {0} (fun _ => 1)
  simp only [Finset.sum_singleton, sub_self, map_one, one_mul] at h00
  obtain ⟨hre0, him0⟩ := Complex.nonneg_iff.1 h00
  rcases eq_or_ne d 0 with rfl | hd
  · have hnorm : ‖k 0‖ = (k 0).re := by
      have h : k 0 = ((k 0).re : ℂ) := Complex.ext rfl (by simp [← him0])
      conv_lhs => rw [h]
      rw [Complex.norm_real, Real.norm_of_nonneg hre0]
    linarith
  have hQ : ∀ w : ℂ, 0 ≤ k 0 + conj w * k (-d) + w * k d + w * conj w * k 0 := by
    intro w
    have h := hk {0, d} (fun j => if j = 0 then 1 else w)
    rw [Finset.sum_pair (Ne.symm hd), Finset.sum_pair (Ne.symm hd), Finset.sum_pair (Ne.symm hd)] at h
    simp only [hd, ↓reduceIte, map_one, one_mul, mul_one, sub_self, zero_sub, sub_zero] at h
    convert h using 1
    ring
  have e1 := Complex.nonneg_iff.1 (hQ 1)
  have e2 := Complex.nonneg_iff.1 (hQ (-1))
  have e3 := Complex.nonneg_iff.1 (hQ I)
  have e4 := Complex.nonneg_iff.1 (hQ (-I))
  simp only [map_one, map_neg, Complex.conj_I, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at e1 e2 e3 e4
  have hre : |(k d).re| ≤ (k 0).re := abs_le.2 ⟨by nlinarith [e1.1, e1.2, e3.2], by nlinarith [e2.1, e1.2, e3.2]⟩
  have him : |(k d).im| ≤ (k 0).re := abs_le.2 ⟨by nlinarith [e4.1, e1.2, e3.2], by nlinarith [e3.1, e1.2, e3.2]⟩
  calc ‖k d‖ ≤ |(k d).re| + |(k d).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * (k 0).re := by linarith

/-- **Bounded power sums**: if `‖Σ_i β_i^d‖ ≤ C` for every `d ≥ 0`, then every `‖β_i‖ ≤ 1`. -/
theorem norm_le_one_of_bdd (β : ι → ℂ) {C : ℝ} (hC : ∀ d : ℕ, ‖∑ i, β i ^ d‖ ≤ C) (i₀ : ι) : ‖β i₀‖ ≤ 1 := by
  classical
  -- the distinct values `v r` of `β`, with multiplicities `c r`
  set T : Finset ℂ := Finset.univ.image β with hT
  set n := T.card
  set e : Fin n ≃ T := T.equivFin.symm with he
  set v : Fin n → ℂ := fun r => ((e r : T) : ℂ) with hv
  have hinj : Function.Injective v := fun a b hab => e.injective (Subtype.ext hab)
  set c : Fin n → ℂ := fun r => ((Finset.univ.filter fun i => β i = v r).card : ℂ) with hc
  have hsum : ∀ d : ℕ, ∑ i, β i ^ d = ∑ r, c r * v r ^ d := by
    intro d
    rw [← Finset.sum_fiberwise_of_maps_to (g := β) (t := T)
      (fun i _ => Finset.mem_image_of_mem β (Finset.mem_univ i)), ← Finset.sum_coe_sort T, ← e.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const, nsmul_eq_mul]
  -- the transposed Vandermonde matrix of the `v r` is invertible
  set A : Matrix (Fin n) (Fin n) ℂ := (Matrix.vandermonde v).transpose with hA
  have hdet : IsUnit A.det := by
    rw [hA, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hinj)
  have hy : ∀ d : ℕ, (fun r => c r * v r ^ d) = A⁻¹.mulVec (fun s : Fin n => ∑ i, β i ^ (d + (s : ℕ))) := by
    intro d
    have hAy : A.mulVec (fun r => c r * v r ^ d) = fun s : Fin n => ∑ i, β i ^ (d + (s : ℕ)) := by
      funext s
      rw [hsum (d + (s : ℕ))]
      simp only [Matrix.mulVec, dotProduct, hA, Matrix.transpose_apply, Matrix.vandermonde_apply]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [← hAy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec]
  obtain ⟨r₀, hr₀⟩ : ∃ r, v r = β i₀ :=
    ⟨e.symm ⟨β i₀, Finset.mem_image_of_mem β (Finset.mem_univ i₀)⟩, by simp [hv]⟩
  have hc1 : 1 ≤ ‖c r₀‖ := by
    have hpos : 0 < (Finset.univ.filter fun i => β i = v r₀).card :=
      Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr₀.symm⟩⟩
    rw [hc, Complex.norm_natCast]
    exact_mod_cast hpos
  set M := ∑ s, ‖A⁻¹ r₀ s‖ * C with hM
  have hbound : ∀ d : ℕ, ‖β i₀‖ ^ d ≤ M := by
    intro d
    have hrow := congrFun (hy d) r₀
    calc ‖β i₀‖ ^ d ≤ ‖c r₀‖ * ‖v r₀‖ ^ d := by
          rw [hr₀]; exact le_mul_of_one_le_left (by positivity) hc1
      _ = ‖c r₀ * v r₀ ^ d‖ := by rw [norm_mul, norm_pow]
      _ = ‖∑ s, A⁻¹ r₀ s * ∑ i, β i ^ (d + (s : ℕ))‖ := by
          rw [hrow]; simp only [Matrix.mulVec, dotProduct]
      _ ≤ ∑ s, ‖A⁻¹ r₀ s‖ * ‖∑ i, β i ^ (d + (s : ℕ))‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun s _ => norm_mul _ _
      _ ≤ M := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  by_contra hgt
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt M (lt_of_not_ge hgt)
  exact absurd (hbound d) (not_le.2 hd)

/-- **Bounded and closed under `β ↦ 1/β̄` gives the circle.** -/
theorem norm_eq_one_of_bdd (β : ι → ℂ) (h0 : ∀ i, β i ≠ 0) (hfe : ∀ i, ∃ j, β j = (conj (β i))⁻¹) {C : ℝ}
    (hC : ∀ d : ℕ, ‖∑ i, β i ^ d‖ ≤ C) (i : ι) : ‖β i‖ = 1 := by
  obtain ⟨j, hj⟩ := hfe i
  have h1 := norm_le_one_of_bdd β hC j
  rw [hj, norm_inv, Complex.norm_conj] at h1
  have hpos : 0 < ‖β i‖ := norm_pos_iff.2 (h0 i)
  exact le_antisymm (norm_le_one_of_bdd β hC i) (by rwa [inv_le_one₀ hpos] at h1)

/-- **Weil's criterion over a finite field**: for nonzero `β_i` closed under `β ↦ 1/β̄`, the kernel
`k(d) = Σ_i β_i^d` is positive-definite on `ℤ` exactly when every `|β_i| = 1`. -/
theorem posDef_iff (β : ι → ℂ) (h0 : ∀ i, β i ≠ 0) (σ : Equiv.Perm ι) (hσ : ∀ i, β (σ i) = (conj (β i))⁻¹) :
    PosDef (kernel β) ↔ ∀ i, ‖β i‖ = 1 := by
  refine ⟨fun hk => norm_eq_one_of_bdd β h0 (fun i => ⟨σ i, hσ i⟩) (C := 2 * (kernel β 0).re) fun d => ?_,
    posDef_of_norm_eq_one β⟩
  simpa [kernel, zpow_natCast] using norm_le_of_posDef hk d

/-- **Positive-definite exactly when bounded.** -/
theorem posDef_iff_bdd (β : ι → ℂ) (h0 : ∀ i, β i ≠ 0) (σ : Equiv.Perm ι) (hσ : ∀ i, β (σ i) = (conj (β i))⁻¹) :
    PosDef (kernel β) ↔ ∃ C, ∀ d : ℕ, ‖∑ i, β i ^ d‖ ≤ C := by
  refine ⟨fun hk => ⟨_, fun d => by simpa [kernel, zpow_natCast] using norm_le_of_posDef hk d⟩, ?_⟩
  rintro ⟨C, hC⟩
  exact posDef_of_norm_eq_one β (norm_eq_one_of_bdd β h0 (fun i => ⟨σ i, hσ i⟩) hC)

/-! ## Real kernels -/

omit [Fintype ι] in
/-- Positivity of a real kernel on `Fin K` for every `K` gives it on every finite set of integers. -/
lemma real_nonneg_of_fin {c : ℤ → ℝ}
    (hc : ∀ (K : ℕ) (y : Fin K → ℝ), 0 ≤ ∑ i, ∑ j, y i * y j * c (((i : ℕ) : ℤ) - (j : ℕ)))
    (S : Finset ℤ) (y : ℤ → ℝ) : 0 ≤ ∑ j ∈ S, ∑ l ∈ S, y j * y l * c (j - l) := by
  classical
  set A : ℕ := S.sup Int.natAbs with hA
  -- the map `r ↦ r − A` from `Fin (2A + 1)` to `ℤ`, whose image contains `S`
  set f : Fin (2 * A + 1) → ℤ := fun r => ((r : ℕ) : ℤ) - A with hf
  have hfinj : Set.InjOn f ↑(Finset.univ : Finset (Fin (2 * A + 1))) := fun r _ r' _ h => by
    simp only [hf, sub_left_inj, Nat.cast_inj] at h
    exact Fin.ext h
  have hSU : S ⊆ Finset.univ.image f := by
    intro j hj
    have h1 : j.natAbs ≤ A := Finset.le_sup (f := Int.natAbs) hj
    have h2 : |j| ≤ (A : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h1
    obtain ⟨h3, h4⟩ := abs_le.1 h2
    rw [Finset.mem_image]
    refine ⟨⟨(j + A).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [hf]
    omega
  set yt : ℤ → ℝ := fun j => if j ∈ S then y j else 0 with hyt
  have hext : ∑ j ∈ S, ∑ l ∈ S, y j * y l * c (j - l) =
      ∑ j ∈ Finset.univ.image f, ∑ l ∈ Finset.univ.image f, yt j * yt l * c (j - l) := by
    calc ∑ j ∈ S, ∑ l ∈ S, y j * y l * c (j - l) = ∑ j ∈ S, ∑ l ∈ S, yt j * yt l * c (j - l) :=
          Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => by simp [hyt, hj, hl]
      _ = ∑ j ∈ Finset.univ.image f, ∑ l ∈ S, yt j * yt l * c (j - l) :=
          Finset.sum_subset hSU fun j _ hj => Finset.sum_eq_zero fun l _ => by simp [hyt, hj]
      _ = ∑ j ∈ Finset.univ.image f, ∑ l ∈ Finset.univ.image f, yt j * yt l * c (j - l) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_subset hSU fun l _ hl => by simp [hyt, hl]
  rw [hext, Finset.sum_image hfinj]
  simp_rw [Finset.sum_image hfinj]
  refine (hc (2 * A + 1) fun r => yt (((r : ℕ) : ℤ) - A)).trans_eq
    (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_)
  simp only [hf, sub_sub_sub_cancel_right]

/-- **Real Toeplitz positivity is positive-definiteness**: if `c` is real and even, and
`Σ_{i,j<K} y_iy_j c(i − j) ≥ 0` for every `K` and all real `y`, then `c` is positive-definite on `ℤ`. -/
theorem posDef_of_real {c : ℤ → ℝ} (heven : ∀ d, c (-d) = c d)
    (hc : ∀ (K : ℕ) (y : Fin K → ℝ), 0 ≤ ∑ i, ∑ j, y i * y j * c (((i : ℕ) : ℤ) - (j : ℕ))) :
    PosDef fun d => (c d : ℂ) := by
  intro S x
  have hsym : ∑ j ∈ S, ∑ l ∈ S, (x j).im * (x l).re * c (j - l) =
      ∑ j ∈ S, ∑ l ∈ S, (x j).re * (x l).im * c (j - l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [show l - j = -(j - l) by ring, heven]
    ring
  have hsplit : ∑ j ∈ S, ∑ l ∈ S, x j * conj (x l) * (c (j - l) : ℂ) =
      ((∑ j ∈ S, ∑ l ∈ S, (x j).re * (x l).re * c (j - l) +
        ∑ j ∈ S, ∑ l ∈ S, (x j).im * (x l).im * c (j - l) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, mul_zero, sub_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    · simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      have e1 : ∀ j ∈ S, ∑ l ∈ S, ((x j).re * -(x l).im + (x j).im * (x l).re) * c (j - l) =
          ∑ l ∈ S, (x j).im * (x l).re * c (j - l) - ∑ l ∈ S, (x j).re * (x l).im * c (j - l) := by
        intro j _
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, hsym, sub_self]
  rw [hsplit]
  exact Complex.zero_le_real.2 (add_nonneg (real_nonneg_of_fin hc S _) (real_nonneg_of_fin hc S _))

/-! ## Point counts -/

/-- The kernel of point counts `N_d`: `c(d) = (q^{|d|} + 1 − N_{|d|})/q^{|d|/2}` for `d ≠ 0`, and `c(0) = m`. -/
noncomputable def countKernel (q : ℝ) (m : ℕ) (N : ℕ → ℝ) (d : ℤ) : ℂ :=
  if d = 0 then (m : ℂ) else (((q ^ d.natAbs + 1 - N d.natAbs) / Real.sqrt q ^ d.natAbs : ℝ) : ℂ)

section counts

variable {q : ℝ} {α : ι → ℂ} {σ : Equiv.Perm ι}

omit [Fintype ι] in
/-- The closure `α ↦ q/ᾱ` of the `α_i` is the closure `β ↦ 1/β̄` of the `β_i = α_i/√q`. -/
lemma div_sqrt_closure (hq : 0 < q) (h0 : ∀ i, α i ≠ 0) (hσ : ∀ i, α (σ i) = q / conj (α i)) (i : ι) :
    α (σ i) / (Real.sqrt q : ℂ) = (conj (α i / (Real.sqrt q : ℂ)))⁻¹ := by
  have hsC : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq).ne'
  have hsq : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = q := by rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]
  have hc : conj (α i) ≠ 0 := (map_ne_zero _).2 (h0 i)
  rw [hσ i, map_div₀, Complex.conj_ofReal, ← hsq]
  field_simp

/-- The count kernel is the kernel of the `α_i/√q`. -/
lemma countKernel_eq (hq : 0 < q) (h0 : ∀ i, α i ≠ 0) (hσ : ∀ i, α (σ i) = q / conj (α i)) {N : ℕ → ℝ}
    (hN : ∀ d, 0 < d → (N d : ℂ) = q ^ d + 1 - ∑ i, α i ^ d) :
    countKernel q (Fintype.card ι) N = kernel fun i => α i / (Real.sqrt q : ℂ) := by
  have hpos : ∀ n : ℕ, 0 < n →
      countKernel q (Fintype.card ι) N n = kernel (fun i => α i / (Real.sqrt q : ℂ)) n := by
    intro n hn
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [countKernel, hn0, ↓reduceIte, Int.natAbs_natCast, kernel, zpow_natCast, div_pow]
    rw [← Finset.sum_div]
    push_cast
    rw [hN n hn]
    ring
  funext d
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = -n := ⟨d.natAbs, by omega⟩
    have hn : 0 < n := by omega
    -- `k(−n) = conj k(n)`, by the closure
    have hneg : kernel (fun i => α i / (Real.sqrt q : ℂ)) (-(n : ℤ)) =
        conj (kernel (fun i => α i / (Real.sqrt q : ℂ)) n) := by
      simp only [kernel, map_sum, zpow_neg, zpow_natCast]
      rw [← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_sqrt_closure hq h0 hσ i, inv_pow, inv_inv, ← map_pow]
    rw [hneg, ← hpos n hn]
    simp only [countKernel, show -(n : ℤ) ≠ 0 by omega, show (n : ℤ) ≠ 0 by omega, ↓reduceIte, Int.natAbs_neg,
      Int.natAbs_natCast, Complex.conj_ofReal]
  · simp [countKernel, kernel]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n := ⟨d.natAbs, by omega⟩
    exact hpos n (by omega)

/-- **Weil's criterion from the point counts**: with `N_d = q^d + 1 − Σ_i α_i^d` and the `α_i` closed under
`α ↦ q/ᾱ`, the count kernel is positive-definite on `ℤ` exactly when every `|α_i| = √q`. -/
theorem countKernel_posDef_iff (hq : 0 < q) (h0 : ∀ i, α i ≠ 0) (hσ : ∀ i, α (σ i) = q / conj (α i))
    {N : ℕ → ℝ} (hN : ∀ d, 0 < d → (N d : ℂ) = q ^ d + 1 - ∑ i, α i ^ d) :
    PosDef (countKernel q (Fintype.card ι) N) ↔ ∀ i, ‖α i‖ = Real.sqrt q := by
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsC : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  rw [countKernel_eq hq h0 hσ hN, posDef_iff _ (fun i => div_ne_zero (h0 i) hsC) σ (div_sqrt_closure hq h0 hσ)]
  refine forall_congr' fun i => ?_
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_eq_one_iff_eq hs0.ne']

/-- **A bound in every degree is enough**: if `|q^d + 1 − N_d| ≤ Cq^{d/2}` for every `d ≥ 1`, then every
`|α_i| = √q`. -/
theorem norm_eq_sqrt_of_bound (hq : 0 < q) (h0 : ∀ i, α i ≠ 0) (hσ : ∀ i, α (σ i) = q / conj (α i))
    {N : ℕ → ℝ} (hN : ∀ d, 0 < d → (N d : ℂ) = q ^ d + 1 - ∑ i, α i ^ d) {C : ℝ}
    (hC : ∀ d, 0 < d → |q ^ d + 1 - N d| ≤ C * Real.sqrt q ^ d) (i : ι) : ‖α i‖ = Real.sqrt q := by
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsC : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have hk := countKernel_eq hq h0 hσ hN
  refine (countKernel_posDef_iff hq h0 hσ hN).1 ?_ i
  rw [hk, posDef_iff_bdd _ (fun i => div_ne_zero (h0 i) hsC) σ (div_sqrt_closure hq h0 hσ)]
  refine ⟨max C (Fintype.card ι), fun d => ?_⟩
  have h := congrFun hk d
  simp only [kernel, zpow_natCast] at h
  rw [← h]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [countKernel, Nat.cast_zero, ↓reduceIte, Complex.norm_natCast]
    exact le_max_right _ _
  · simp only [countKernel, show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne', ↓reduceIte, Int.natAbs_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hs0 d)]
    rw [div_le_iff₀ (pow_pos hs0 d)]
    exact (hC d hd).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos hs0 d).le)

end counts

end WeilFF

#print axioms WeilFF.posDef_iff
#print axioms WeilFF.posDef_iff_bdd
#print axioms WeilFF.countKernel_posDef_iff
#print axioms WeilFF.norm_eq_sqrt_of_bound
#print axioms WeilFF.posDef_of_real
