import LocalKernels

/-!
# The Hecke relation of the theta chain and its iteration

D2-5 of the served valuation of the theta chain (layer 2, lattices).

**The iteration lemma** (`iterate_hecke`, pure algebra). Levels `j` carry modules `M j`, steps `K j`, normalised Hecke
operators `H j i` and scalars `ε j l` with the one-step relation `H_{j+1}(i) ∘ K_j = Σ_{l ≤ i} ε_{j,l}·K_j ∘ H_j(i−l)`
(`i ≤ r`). With `c_j` the coefficients of `P_j = ∏_{j′<j} Σ_l ε_{j′,l}X^l`, induction on `j` gives
`H_j(i) ∘ chain_j = Σ_{l ≤ i} c_{j,l}·chain_j ∘ H_0(i−l)` (`hecke_chain`): the step multiplies `P_j` by the next
factor, a convolution of coefficients (`sum_conv`). So if `η_j` inverts `P_j` modulo `X^{r+1}`, the combination
`Y_j = Σ_{l ≤ r} η_{j,l}·H_j(r−l)` satisfies `Y_j ∘ chain_j = chain_j ∘ H_0(r)`.
-/

open Finset

namespace HeckeTheta

/-! ## The iteration lemma -/

section Iterate

variable {R : Type} [CommRing R]

/-- **A convolution in two steps**:
`Σ_{l ≤ i} a_l·Σ_{l′ ≤ i−l} b_{l′}·y_{i−l−l′} = Σ_{m ≤ i} (Σ_{l ≤ m} a_l b_{m−l})·y_{i−m}`
(`Finset.sum_range_diag_flip`). -/
theorem sum_conv {A : Type} [AddCommGroup A] [Module R A] (i : ℕ) (a b : ℕ → R) (y : ℕ → A) :
    ∑ l ∈ range (i + 1), a l • ∑ l' ∈ range (i - l + 1), b l' • y (i - l - l') =
      ∑ m ∈ range (i + 1), (∑ l ∈ range (m + 1), a l * b (m - l)) • y (i - m) := by
  have hR : ∑ m ∈ range (i + 1), (∑ l ∈ range (m + 1), a l * b (m - l)) • y (i - m) =
      ∑ m ∈ range (i + 1), ∑ l ∈ range (m + 1), (a l * b (m - l)) • y (i - l - (m - l)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    rw [show i - l - (m - l) = i - m by omega]
  rw [hR, Finset.sum_range_diag_flip (i + 1) fun l l' => (a l * b l') • y (i - l - l')]
  refine Finset.sum_congr rfl fun l hl => ?_
  have : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  rw [Finset.smul_sum, show i + 1 - l = i - l + 1 by omega]
  exact Finset.sum_congr rfl fun l' _ => (mul_smul _ _ _).symm

variable {M : ℕ → Type} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

/-- **The Hecke operators along the chain**: `H_j(i) ∘ chain_j = Σ_{l ≤ i} c_{j,l}·chain_j ∘ H_0(i−l)`, `c_j` the
coefficients of `∏_{j′<j} Σ_l ε_{j′,l}X^l` (induction on `j`; the step convolves with `ε_j`). -/
theorem hecke_chain (K : ∀ j, M j →ₗ[R] M (j + 1)) (H : ∀ j, ℕ → M j →ₗ[R] M j) (ε : ℕ → ℕ → R) (r : ℕ)
    (hstep : ∀ j, ∀ i ≤ r, H (j + 1) i ∘ₗ K j = ∑ l ∈ range (i + 1), ε j l • (K j ∘ₗ H j (i - l)))
    (chain : ∀ j, M 0 →ₗ[R] M j) (hc0 : chain 0 = LinearMap.id) (hcs : ∀ j, chain (j + 1) = K j ∘ₗ chain j) :
    ∀ j, ∀ i ≤ r, ∀ x, H j i (chain j x) = ∑ l ∈ range (i + 1),
      PowerSeries.coeff l (∏ i' ∈ range j, PowerSeries.mk (ε i')) • chain j (H 0 (i - l) x) := by
  intro j
  induction j with
  | zero =>
    intro i _ x
    rw [Finset.sum_eq_single 0]
    · simp [hc0]
    · intro l _ hl
      simp [PowerSeries.coeff_one, hl]
    · intro h
      simp at h
  | succ j ih =>
    intro i hi x
    have hs := LinearMap.congr_fun (hstep j i hi) (chain j x)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] at hs
    rw [hcs, LinearMap.comp_apply, hs]
    have hih : ∀ l ∈ range (i + 1), ε j l • K j (H j (i - l) (chain j x)) = ε j l • ∑ l' ∈ range (i - l + 1),
        PowerSeries.coeff l' (∏ i' ∈ range j, PowerSeries.mk (ε i')) • K j (chain j (H 0 (i - l - l') x)) :=
      fun l _ => by
        rw [ih (i - l) (by omega) x, map_sum]
        simp only [map_smul]
    rw [Finset.sum_congr rfl hih]
    refine (sum_conv i (ε j) (fun l => PowerSeries.coeff l (∏ i' ∈ range j, PowerSeries.mk (ε i')))
      (fun n => K j (chain j (H 0 n x)))).trans (Finset.sum_congr rfl fun m _ => ?_)
    rw [Finset.prod_range_succ, mul_comm, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
    rfl

/-- **The iteration lemma** (pure algebra). Levels `j` with modules `M j`, steps `K j`, normalised Hecke operators
`H j i` (`H j 0 = id`) and scalars `ε j l` with the one-step relation
`H (j+1) i ∘ K j = Σ_{l ≤ i} ε j l • K j ∘ H j (i−l)` for `i ≤ r`. Put `η j` = the coefficients of `∏_{i<j} (Σ_l ε i l X^l)⁻¹` and `Y j = Σ_{l ≤ r} η j l • H j (r − l)`.
Then `Y j ∘ chain j = chain j ∘ H 0 r`. -/
theorem iterate_hecke (K : ∀ j, M j →ₗ[R] M (j + 1)) (H : ∀ j, ℕ → M j →ₗ[R] M j)
    (_hH0 : ∀ j, H j 0 = LinearMap.id) (ε : ℕ → ℕ → R) (_hε0 : ∀ j, ε j 0 = 1) (r : ℕ)
    (hstep : ∀ j, ∀ i ≤ r, H (j + 1) i ∘ₗ K j = ∑ l ∈ range (i + 1), ε j l • (K j ∘ₗ H j (i - l)))
    (chain : ∀ j, M 0 →ₗ[R] M j) (hc0 : chain 0 = LinearMap.id) (hcs : ∀ j, chain (j + 1) = K j ∘ₗ chain j)
    (η : ℕ → ℕ → R)
    (hη : ∀ j, ∀ i ≤ r, ∑ l ∈ range (i + 1),
      η j l * PowerSeries.coeff (i - l) (∏ i' ∈ range j, PowerSeries.mk (ε i')) = if i = 0 then 1 else 0) :
    ∀ j, (∑ l ∈ range (r + 1), η j l • H j (r - l)) ∘ₗ chain j = chain j ∘ₗ H 0 r := by
  intro j
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun l _ => by rw [hecke_chain K H ε r hstep chain hc0 hcs j (r - l) (by omega) x]]
  refine (sum_conv r (η j) (fun l => PowerSeries.coeff l (∏ i' ∈ range j, PowerSeries.mk (ε i')))
    (fun n => chain j (H 0 n x))).trans ?_
  rw [Finset.sum_eq_single 0]
  · rw [hη j 0 (Nat.zero_le r)]
    simp
  · intro m hm hm0
    rw [hη j m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)), ite_eq_right hm0, zero_smul]
  · intro h
    simp at h

end Iterate

end HeckeTheta
