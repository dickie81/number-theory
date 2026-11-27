import OffTop

/-!
# Products of `∇`-lattices in the same variables, and diagonal twists of top vectors (L5, A-N16, part 1)

The first part of module 11 (`FirstCloud`) of the L5/L6 plan: the algebra behind the cloud maps of Annex I N16,
which multiply polynomials in the *same* blocks of variables (`OffTop` multiplies polynomials in disjoint blocks).

**Main results.**
* *Shapes add* (`detShift_add`, `natW_add`, `mult_add`): for antitone weights `u, v`, `natW(u + v) = natW u + natW v`
  and the multiplicities of the leading minors add.
* *Bideterminants multiply* (`bidet_mul`): the product of bideterminants of shapes `ν₁`, `ν₂` is a bideterminant of
  shape `ν₁ + ν₂` (append the rows of the factors of each size, `exists_gfac_add`), so `∇_A(ν₁)·∇_A(ν₂) ⊆ ∇_A(ν₁ + ν₂)`
  (`mul_mem_nablaInt'`).
* *Twists multiply* (`twist_mul'`) when the determinant shifts add, hence the easy half of the Cartan product for every
  family of block lattices: `∇_Λ(λ₁)·∇_Λ(λ₂) ⊆ ∇_Λ(λ₁ + λ₂)` (`mul_mem_nablaB'`).
* *Diagonal twists of top vectors* (`twist_dg0`): on a row-homogeneous polynomial whose row weight has the entry `e_σ`
  in row `0` of block `σ`, the twist by `diag(c₀, 1, …, 1)` in every block is multiplication by
  `c₀^{Σ_σ (detShift λ_σ + e_σ)}`.
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice

open scoped Matrix

noncomputable section

/-! ## Shapes add -/

section Shape

variable {n : ℕ}

/-- **`detShift` is additive.** -/
theorem detShift_add (u v : Fin n → ℤ) : detShift (u + v) = detShift u + detShift v := by
  unfold detShift
  split_ifs <;> simp

/-- **`detShift` is at most every entry** of an antitone weight. -/
theorem detShift_le {u : Fin n → ℤ} (hu : Antitone u) (i : Fin n) : detShift u ≤ u i := by
  unfold detShift
  split_ifs with h
  · exact hu (Fin.mk_le_mk.2 (by have := i.isLt; omega) : i ≤ ⟨n - 1, by have := i.isLt; omega⟩)
  · exact absurd i.pos h

/-- **`natW` is additive on antitone weights.** -/
theorem natW_add {u v : Fin n → ℤ} (hu : Antitone u) (hv : Antitone v) : natW (u + v) = natW u + natW v := by
  funext i
  have h1 := detShift_le hu i
  have h2 := detShift_le hv i
  simp only [natW, Pi.add_apply, detShift_add]
  rw [show u i + v i - (detShift u + detShift v) = (u i - detShift u) + (v i - detShift v) by ring,
    Int.toNat_add (by omega) (by omega)]

/-- **Multiplicities add** on antitone shapes. -/
theorem mult_add {ν₁ ν₂ : Fin n → ℕ} (h₁ : Antitone ν₁) (h₂ : Antitone ν₂) (s : Fin n) :
    mult (ν₁ + ν₂) s = mult ν₁ s + mult ν₂ s := by
  unfold mult
  split_ifs with h
  · have e₁ : ν₁ ⟨s + 1, h⟩ ≤ ν₁ s := h₁ (Fin.le_def.2 (Nat.le_succ _))
    have e₂ : ν₂ ⟨s + 1, h⟩ ≤ ν₂ s := h₂ (Fin.le_def.2 (Nat.le_succ _))
    simp only [Pi.add_apply]
    omega
  · simp

end Shape

/-! ## Bideterminants multiply -/

section Bidet

variable {Φ : Type} [Fintype Φ] {n : ℕ} {L : Type} [Field L]

/-- **A product of leading minors** of block `τ`: `M s` minors of size `s + 1`, on the rows `r s c`. A block factor of
a bideterminant of shape `ν` is the case `M = mult (ν τ)`. -/
def gfac (τ : Φ) (M : Fin n → ℕ) (r : (s : Fin n) → Fin (M s) → Fin (s + 1) → Fin n) : Pol Φ n L :=
  ∏ s : Fin n, ∏ c, minor τ s (r s c)

omit [Fintype Φ] in
/-- **Products of minors concatenate**: for `M = M₁ + M₂`, a product with `M₁` and one with `M₂` minors of each size
multiply to a product with `M` minors of each size (append the rows). -/
theorem exists_gfac_add {τ : Φ} {M M₁ M₂ : Fin n → ℕ} (hM : M = fun s => M₁ s + M₂ s)
    (r₁ : (s : Fin n) → Fin (M₁ s) → Fin (s + 1) → Fin n) (r₂ : (s : Fin n) → Fin (M₂ s) → Fin (s + 1) → Fin n) :
    ∃ r : (s : Fin n) → Fin (M s) → Fin (s + 1) → Fin n,
      (gfac τ M r : Pol Φ n L) = gfac τ M₁ r₁ * gfac τ M₂ r₂ := by
  subst hM
  refine ⟨fun s => Fin.append (r₁ s) (r₂ s), ?_⟩
  simp only [gfac, ← Finset.prod_mul_distrib, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- **Bideterminants multiply**: the product of bideterminants of antitone shapes `ν₁` and `ν₂` is a bideterminant
of shape `ν₁ + ν₂`. -/
theorem bidet_mul {ν₁ ν₂ : Φ → Fin n → ℕ} (h₁ : ∀ τ, Antitone (ν₁ τ)) (h₂ : ∀ τ, Antitone (ν₂ τ))
    (r₁ : BRows Φ n ν₁) (r₂ : BRows Φ n ν₂) :
    ∃ r : BRows Φ n (ν₁ + ν₂), bidet L (ν₁ + ν₂) r = bidet L ν₁ r₁ * bidet L ν₂ r₂ := by
  have key : ∀ τ, ∃ r : (s : Fin n) → Fin (mult ((ν₁ + ν₂) τ) s) → Fin (s + 1) → Fin n,
      (gfac τ (mult ((ν₁ + ν₂) τ)) r : Pol Φ n L) =
        gfac τ (mult (ν₁ τ)) (r₁ τ) * gfac τ (mult (ν₂ τ)) (r₂ τ) :=
    fun τ => exists_gfac_add (funext fun s => mult_add (h₁ τ) (h₂ τ) s) _ _
  choose r hr using key
  refine ⟨r, ?_⟩
  show ∏ τ, gfac τ (mult ((ν₁ + ν₂) τ)) (r τ) =
    (∏ τ, gfac τ (mult (ν₁ τ)) (r₁ τ)) * ∏ τ, gfac τ (mult (ν₂ τ)) (r₂ τ)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => hr τ

/-- **Products of integral spans**: `∇_A(ν₁)·∇_A(ν₂) ⊆ ∇_A(ν₁ + ν₂)` for antitone shapes (`bidet_mul`). -/
theorem mul_mem_nablaInt' {A : Subring L} {ν₁ ν₂ : Φ → Fin n → ℕ} (h₁ : ∀ τ, Antitone (ν₁ τ))
    (h₂ : ∀ τ, Antitone (ν₂ τ)) {F G : Pol Φ n L} (hF : F ∈ nablaInt A ν₁) (hG : G ∈ nablaInt A ν₂) :
    F * G ∈ nablaInt A (ν₁ + ν₂) := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r₁, rfl⟩ := hx
      obtain ⟨r₂, rfl⟩ := hy
      obtain ⟨r, hr⟩ := bidet_mul (L := L) h₁ h₂ r₁ r₂
      rw [← hr]
      exact Submodule.subset_span ⟨r, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [show a • y = (a : L) • y from rfl, mul_smul_comm]
      exact Submodule.smul_mem _ a hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : L) • x from rfl, smul_mul_assoc]
    exact Submodule.smul_mem _ a hx

end Bidet

/-! ## Twists multiply; the easy half of the Cartan product -/

section Twist

variable {Φ : Type} [Fintype Φ] {n : ℕ} {L : Type} [Field L]

/-- **Twists multiply**: `twist_λ(F·G) = twist_{λ₁}(F)·twist_{λ₂}(G)` when the determinant shifts add and the
matrices are invertible (`lsub` is multiplicative). -/
theorem twist_mul' {lam lam₁ lam₂ : Φ → Fin n → ℤ} (h : ∀ σ, detShift (lam σ) = detShift (lam₁ σ) + detShift (lam₂ σ))
    {g : Φ → Matrix (Fin n) (Fin n) L} (hg : ∀ σ, (g σ).det ≠ 0) (F G : Pol Φ n L) :
    twist lam g (F * G) = twist lam₁ g F * twist lam₂ g G := by
  have e : ∏ σ, (g σ).det ^ detShift (lam σ) =
      (∏ σ, (g σ).det ^ detShift (lam₁ σ)) * ∏ σ, (g σ).det ^ detShift (lam₂ σ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => by rw [h σ, zpow_add₀ (hg σ)]
  simp only [twist, map_mul, e]
  ring

variable [DecidableEq Φ] {k : ℕ} {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]

/-- **The easy half of the Cartan product**: `∇_Λ(λ₁)·∇_Λ(λ₂) ⊆ ∇_Λ(λ₁ + λ₂)` for antitone weights, at every family
of block lattices `Λ` (`twist_mul'`, `mul_mem_nablaInt'`). -/
theorem mul_mem_nablaB' {lam₁ lam₂ : Φ → Fin k → ℤ} (h₁ : ∀ b, Antitone (lam₁ b)) (h₂ : ∀ b, Antitone (lam₂ b))
    {Λ : Φ → Submodule O (Fin k → Kf)} {F G : Pol Φ k Kf} (hF : F ∈ nablaB lam₁ Λ) (hG : G ∈ nablaB lam₂ Λ) :
    F * G ∈ nablaB (lam₁ + lam₂) Λ := by
  obtain ⟨hF1, C, hC, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := (mem_nablaB_iff hC).1 hG
  have hn : (fun b => natW ((lam₁ + lam₂) b)) = (fun b => natW (lam₁ b)) + fun b => natW (lam₂ b) :=
    funext fun b => natW_add (h₁ b) (h₂ b)
  refine ⟨?_, C, hC, ?_⟩
  · rw [hn]
    exact OffTop.mul_mem_nabla rfl hF1 hG1
  · rw [twist_mul' (lam := lam₁ + lam₂) (lam₁ := lam₁) (lam₂ := lam₂) (fun σ => detShift_add (lam₁ σ) (lam₂ σ))
      (fun σ => (hC σ).1.ne_zero), hn]
    exact mul_mem_nablaInt' (fun b => natW_antitone (h₁ b)) (fun b => natW_antitone (h₂ b)) hF2 hG2

end Twist

/-! ## Diagonal twists of top vectors -/

section Diag

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type} [Field L]

/-- **Products of integer powers** of a nonzero element: `∏_i c^{e_i} = c^{Σ_i e_i}`. -/
theorem prod_zpow_eq_zpow_sum' {ι : Type*} {c : L} (hc : c ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hc]

/-- **The diagonal matrix `diag(c₀, 1, …, 1)`**, scaling the coordinate `0`. -/
def dg0 (c₀ : L) : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => if i.val = 0 then c₀ else 1

/-- **Diagonal twists of row-homogeneous polynomials**: if `F` has row weight `μ` and `c₀ ≠ 0`, the twist by
`diag(c₀, 1, …, 1)` in every block is multiplication by `c₀^{Σ_σ (detShift λ_σ + μ_{σ,0})}`. -/
theorem twist_dg0 (hn : 0 < n) (lam : Φ → Fin n → ℤ) {F : Pol Φ n L} {μ : Φ → Fin n → ℕ}
    (hF : IsWeightedHomogeneous (rowW Φ n) F μ) {c₀ : L} (hc₀ : c₀ ≠ 0) :
    twist lam (fun _ => dg0 c₀) F = c₀ ^ (∑ σ, (detShift (lam σ) + (μ σ ⟨0, hn⟩ : ℤ))) • F := by
  rw [show (fun _ : Φ => (dg0 c₀ : Matrix (Fin n) (Fin n) L)) =
    fun σ => Matrix.diagonal fun i : Fin n => if i.val = 0 then c₀ else 1 from rfl, twist_diagonal_of_isWH lam hF]
  congr 1
  rw [← prod_zpow_eq_zpow_sum' hc₀]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have e1 : ∏ i : Fin n, (if i.val = 0 then c₀ else 1) = c₀ := by
    rw [Finset.prod_eq_single ⟨0, hn⟩ (fun i _ hi => by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]) (by simp)]
    simp
  have e2 : ∏ i : Fin n, (if i.val = 0 then c₀ else 1) ^ μ σ i = c₀ ^ μ σ ⟨0, hn⟩ := by
    rw [Finset.prod_eq_single ⟨0, hn⟩ (fun i _ hi => by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]) (by simp)]
    simp
  rw [e1, e2, zpow_add₀ hc₀, zpow_natCast]

end Diag

end

end FirstCloud
