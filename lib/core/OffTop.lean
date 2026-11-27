import FirstAssembly

/-!
# The off-top step: from the top part of a weight to the weight (L5, A-N18)

The hypothesis `FirstAssembly.OffTop` of the first local theorem (module 10 of the L5/L6 plan), at one orbit of an
inert prime `p` in the setting `Unram`. For a dominant weight `λ` with every entry off the tops `TT` in `[−c, c]`, the
top part `λ^top` (`topPart`) is `λ` at the tops and `0` elsewhere, the off-top part `λ^off` (`offPart`) the rest. A
per-edge rank `(1 − κ)·d(λ^top)/g` at depth `t`, conductor `c₃` gives the per-edge rank `(1 − κ)·d(λ)/g` at depth
`t + 2n′c`, conductor `c₃ − 2n′c`, same denominator (`offTop`); so the first local theorem holds without that
hypothesis (`first_local'`).

**The tensor factorisation.** The blocks of `λ^top` and of `λ^off` carry disjoint sets of variables, and
`V(λ) = V(λ^top) ⊗ V(λ^off)` is the product of polynomials. For a splitting of block weights along a predicate `P`
(`Split`: `λ₁ = λ`, `λ₂ = 0` on `P`, `λ₁ = 0`, `λ₂ = λ` off `P`; the blocks at the tops, `split_wt1`):
* the bideterminants of shape `ν` are the products of those of shapes `ν₁` and `ν₂` (`bidet_split`, `bidet_split'`),
  `hw(ν) = hw(ν₁)·hw(ν₂)` (`hw_split`), and twists split (`twist_mul_split`);
* `∇_Λ(λ₁)·∇_Λ(λ₂) ⊆ ∇_Λ(λ)`, and `∇_Λ(λ)` is the `O`-span of these products, for every family `Λ` of block lattices
  (`mul_mem_nablaB`, `mem_span_mul_of_nablaB`); `dim ∇(λ) ≤ dim ∇(λ₁)·dim ∇(λ₂)` (`finrank_nabla_le`);
* the Fock form is multiplicative over disjoint variables (`fock_mul_split`), so `κ(λ) = κ(λ₁)·κ(λ₂)` and
  `⟨F₁G₁, F₂G₂⟩_λ = ⟨F₁, F₂⟩_{λ₁}·⟨G₁, G₂⟩_{λ₂}` (`kappa_split`, `nf_split`), and products of duals are dual
  (`mul_mem_bdual`).

At an edge `e`: `𝓡_top(e)·𝓡_off(e) ⊆ 𝓡_λ(e)`, `𝓡′_top(e)·𝓡′_off(e) ⊆ 𝓡′_λ(e)` and
`pairE_λ(F₁G₁, F₂G₂) = pairE_top(F₁, F₂)·pairE_off(G₁, G₂)` (`mul_mem_edgeLat`, `mul_mem_edgeDual`, `pairE_split`).

**The off-top bound.** `𝓡_off(e) ⊆ ϖ^{−2n′c}∇_off(L″)` and `𝓡′_off(e) ⊆ ϖ^{−2n′c}∇_off(L)^∨`
(`smul_mem_nab_of_edgeLat_off`, `smul_mem_bdual_of_edgeDual_off`): in the adapted basis of the edge,
`𝓡(e) = span(ϖ^{π_i − A}x_i)` with `π_i = pexp i ≥ Σ_b λ_{b,k−1}` (`exists_adapted_basis_ge`), and
`A_1(λ^off) − Σ_b λ^off_{b,k−1} ≤ 2n′c` (`topA_sub_le`).

**Main results.**
* *The off-top step at one edge* (`goodSys_offTop`): a good system `(x_i, y_m, z, M)` of size `n` for `λ^top` at an
  edge gives the good system `(x_i·r_α, y_m·ρ_β, z, M ⊗ 1)` for `λ`, of size `n·|ZIdx| ≥ n·d(λ^off)`, where `r`, `ρ`
  are `pairE`-dual bases of `𝓡_off(e)` and `𝓡′_off(e)` (model fact 2, `edgeLat_dualPair`).
* *The off-top step* (`offTop`): `FirstAssembly.OffTop` at every setting, for all its parameters.
* *The first local theorem* (`first_local'`): `FirstAssembly.first_local` without the hypothesis `OffTop`.

**The routes.** Sources (`mul_mem_srcFam`): with `G₀ = ϖ^{2n′c}G ∈ ∇_off(L″)`, `F·G = ϖ^{−t−2n′c}·F₀G₀` with
`F₀G₀ ∈ ∇_λ(L″)`; on `e` the product lies in `𝓡_top(e)·𝓡_off(e)`; on an edge `e′ ≠ e` out of `L″`,
`F·G = ϖ^{c₃−2n′c}·F₁G₀` with `F₁ ∈ 𝓡_top(e′)` and `G₀ ∈ ∇_off(L″) ⊆ 𝓡_off(e′)` (model fact 1). Targets
(`mul_mem_tgtFam`) likewise, with `ρ₀ = ϖ^{2n′c}ρ ∈ ∇_off(L)^∨ ⊆ 𝓡′_off(e₁)`, and `G ∈ 𝓡′(e)` iff
`ϖ^{A_r}G ∈ ∇(mid)^∨` (`mem_edgeDual_iff`). The Gram matrix of the products is that of the top system times
`pairE_off(r_α, ρ_β) = δ_{αβ}`. The splitting lemmas run through block factors of bideterminants (`bfac`), which depend
only on the shape of their block, so no casts between row types are needed; the Fock form of products is a sum over
`supp F₂ × supp G₂`, on which `(a, b) ↦ a + b` is injective (`add_split_inj`, `coeff_add_mul_split`,
`fact_add_split`).

**Readings of the planning statements.** `OffTop` does not mention the setting; `offTop` takes `Unram`, which
`first_local` supplies. Only half of the tensor factorisation is used: the products lie in the lattices and span them,
and `d(λ) ≤ d(λ^top)·d(λ^off)`; the paper's Kronecker product with the identity is the matrix `M ⊗ 1` on an
enumeration of `Fin n × ZIdx`.
-/

namespace OffTop

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly Finset

open scoped Matrix Pointwise

noncomputable section

/-! ## Splitting the blocks -/

section Split

/-- **A splitting of a family along a predicate** `P` on the indices: `f₁ = f` and `f₂ = 0` where `P` holds, `f₁ = 0`
and `f₂ = f` where it fails. -/
def Split {β M : Type*} [Zero M] (P : β → Prop) (f f₁ f₂ : β → M) : Prop :=
  ∀ b, (P b → f₁ b = f b ∧ f₂ b = 0) ∧ (¬ P b → f₁ b = 0 ∧ f₂ b = f b)

variable {β : Type*} {P : β → Prop}

/-- **A splitting adds up**: `f = f₁ + f₂`. -/
theorem Split.add {M : Type*} [AddZeroClass M] {f f₁ f₂ : β → M} (h : Split P f f₁ f₂) (b : β) :
    f b = f₁ b + f₂ b := by
  by_cases hb : P b
  · rw [((h b).1 hb).1, ((h b).1 hb).2, add_zero]
  · rw [((h b).2 hb).1, ((h b).2 hb).2, zero_add]

/-- **A splitting is kept by maps** that keep `0`. -/
theorem Split.map {M N : Type*} [Zero M] [Zero N] {f f₁ f₂ : β → M} (h : Split P f f₁ f₂) (g : M → N)
    (hg : g 0 = 0) : Split P (fun b => g (f b)) (fun b => g (f₁ b)) (fun b => g (f₂ b)) := fun b =>
  ⟨fun hb => by simp [(h b).1 hb, hg], fun hb => by simp [(h b).2 hb, hg]⟩

/-- **`detShift 0 = 0`.** -/
theorem detShift_zero {n : ℕ} : detShift (0 : Fin n → ℤ) = 0 := by
  simp [detShift]

/-- **`natW 0 = 0`.** -/
theorem natW_zero {n : ℕ} : natW (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [natW, detShift]

/-- **The multiplicities of the zero shape** vanish. -/
theorem mult_zero {n : ℕ} (s : Fin n) : mult (0 : Fin n → ℕ) s = 0 := by
  simp [mult]

end Split

/-! ## Polynomials in disjoint blocks of variables -/

section Poly

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type} [Field L] {P : Φ → Prop}

omit [Fintype Φ] in
/-- **Products in `∇`**: `∇(ν₁)·∇(ν₂) ⊆ ∇(ν₁ + ν₂)` (degrees add, invariance is multiplicative). -/
theorem mul_mem_nabla {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : ν = ν₁ + ν₂) {F G : Pol Φ n L} (hF : F ∈ nabla L ν₁)
    (hG : G ∈ nabla L ν₂) : F * G ∈ nabla L ν := by
  rw [mem_nabla_iff] at hF hG ⊢
  exact ⟨h ▸ hF.1.mul hG.1, fun u hu => by rw [map_mul, hF.2 u hu, hG.2 u hu]⟩

/-- **A shape vanishing off `Q` uses only the variables of the blocks in `Q`**: a polynomial of column degrees `ν`
with `ν_τ = 0` for `τ ∉ Q` lies in the subalgebra generated by the variables `x_{τ,a,b}`, `τ ∈ Q`. -/
theorem mem_supported_of_isWH (Q : Φ → Prop) {ν : Φ → Fin n → ℕ} (hν : ∀ τ, ¬ Q τ → ν τ = 0) {F : Pol Φ n L}
    (hF : IsWeightedHomogeneous (colW Φ n) F ν) : F ∈ supported L {v | Q v.1} := by
  classical
  rw [mem_supported]
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
  by_contra hQ
  have h1 := congrFun (congrFun (hF (mem_support_iff.1 hd)) v.1) v.2.2
  rw [weight_colW_apply, hν v.1 hQ, Pi.zero_apply] at h1
  have h2 := (Finset.sum_eq_zero_iff.1 h1) v.2.1 (Finset.mem_univ _)
  exact (Finsupp.mem_support_iff.1 hvd) h2

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Exponents of a supported polynomial** are supported. -/
theorem support_sub_of_supported {S : Set (Φ × Fin n × Fin n)} {F : Pol Φ n L} (hF : F ∈ supported L S)
    {d : Φ × Fin n × Fin n →₀ ℕ} (hd : d ∈ F.support) : ↑d.support ⊆ S := fun v hv =>
  (mem_supported.1 hF) ((mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩)

/-- **Exponents on complementary sets add injectively**: `x + y = a + b` with `x, a` on `S` and `y, b` off `S` forces
`x = a`, `y = b`. -/
theorem add_split_inj {α : Type*} {S : Set α} {x y a b : α →₀ ℕ} (hx : ↑x.support ⊆ S) (hy : ↑y.support ⊆ Sᶜ)
    (ha : ↑a.support ⊆ S) (hb : ↑b.support ⊆ Sᶜ) (h : x + y = a + b) : x = a ∧ y = b := by
  have key : ∀ v, x v = a v ∧ y v = b v := fun v => by
    have hv := DFunLike.congr_fun h v
    simp only [Finsupp.add_apply] at hv
    by_cases hvS : v ∈ S
    · have h1 : y v = 0 := Finsupp.notMem_support_iff.1 fun h' => hy h' hvS
      have h2 : b v = 0 := Finsupp.notMem_support_iff.1 fun h' => hb h' hvS
      omega
    · have h1 : x v = 0 := Finsupp.notMem_support_iff.1 fun h' => hvS (hx h')
      have h2 : a v = 0 := Finsupp.notMem_support_iff.1 fun h' => hvS (ha h')
      omega
  exact ⟨Finsupp.ext fun v => (key v).1, Finsupp.ext fun v => (key v).2⟩

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Coefficients of a product in disjoint variables**: `(F·G)_{a+b} = F_a·G_b` for `F` on `S`, `G` off `S` and
exponents `a` on `S`, `b` off `S`. -/
theorem coeff_add_mul_split {S : Set (Φ × Fin n × Fin n)} {F G : Pol Φ n L} (hF : F ∈ supported L S)
    (hG : G ∈ supported L Sᶜ) {a b : Φ × Fin n × Fin n →₀ ℕ} (ha : ↑a.support ⊆ S) (hb : ↑b.support ⊆ Sᶜ) :
    (F * G).coeff (a + b) = F.coeff a * G.coeff b := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (a, b)]
  · intro x hx hne
    by_cases h1 : F.coeff x.1 = 0
    · rw [h1, zero_mul]
    by_cases h2 : G.coeff x.2 = 0
    · rw [h2, mul_zero]
    exfalso
    apply hne
    have := add_split_inj (support_sub_of_supported hF (mem_support_iff.2 h1))
      (support_sub_of_supported hG (mem_support_iff.2 h2)) ha hb (mem_antidiagonal.1 hx)
    exact Prod.ext this.1 this.2
  · intro h
    exact absurd (by simp) h

omit [DecidableEq Φ] in
/-- **Factorials of exponents on complementary sets** multiply: `(a + b)! = a!·b!`. -/
theorem fact_add_split {S : Set (Φ × Fin n × Fin n)} {a b : Φ × Fin n × Fin n →₀ ℕ} (ha : ↑a.support ⊆ S)
    (hb : ↑b.support ⊆ Sᶜ) : (fact (a + b) : L) = fact a * fact b := by
  unfold fact
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.add_apply]
  by_cases hv : v ∈ S
  · rw [Finsupp.notMem_support_iff.1 fun h => hb h hv]
    simp
  · rw [Finsupp.notMem_support_iff.1 fun h => hv (ha h)]
    simp

/-- **The Fock form is multiplicative over disjoint variables**: for `F₁, F₂` on `S` and `G₁, G₂` off `S`,
`⟨F₁G₁, F₂G₂⟩ = ⟨F₁, F₂⟩·⟨G₁, G₂⟩`. The support of `F₂G₂` is the injective image of `supp F₂ × supp G₂` under
`(a, b) ↦ a + b`, where the coefficients and the factorials split. -/
theorem fock_mul_split {S : Set (Φ × Fin n × Fin n)} {F₁ F₂ G₁ G₂ : Pol Φ n L} (hF₁ : F₁ ∈ supported L S)
    (hF₂ : F₂ ∈ supported L S) (hG₁ : G₁ ∈ supported L Sᶜ) (hG₂ : G₂ ∈ supported L Sᶜ) :
    fockWith (RingHom.id L) (F₁ * G₁) (F₂ * G₂) =
      fockWith (RingHom.id L) F₁ F₂ * fockWith (RingHom.id L) G₁ G₂ := by
  classical
  have hT : (F₂ * G₂).support ⊆ (F₂.support ×ˢ G₂.support).image fun x => x.1 + x.2 := by
    intro d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul F₂ G₂ hd)
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  rw [fock_eq_sum_right hT, Finset.sum_image, fock_eq_sum_right (subset_refl F₂.support),
    fock_eq_sum_right (subset_refl G₂.support), Finset.sum_mul_sum, Finset.sum_product]
  · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have ha' := support_sub_of_supported hF₂ ha
    have hb' := support_sub_of_supported hG₂ hb
    simp only
    rw [coeff_add_mul_split hF₁ hG₁ ha' hb', coeff_add_mul_split hF₂ hG₂ ha' hb', fact_add_split ha' hb']
    ring
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.1 hy
    have := add_split_inj (support_sub_of_supported hF₂ hx1) (support_sub_of_supported hG₂ hx2)
      (support_sub_of_supported hF₂ hy1) (support_sub_of_supported hG₂ hy2) hxy
    exact Prod.ext this.1 this.2

omit [DecidableEq Φ] in
/-- **The highest-weight vector splits**: `hw(ν) = hw(ν₁)·hw(ν₂)` for a splitting of the shape. -/
theorem hw_split {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : Split P ν ν₁ ν₂) : hw L ν = hw L ν₁ * hw L ν₂ := by
  unfold hw
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  by_cases hτ : P τ
  · rw [((h τ).1 hτ).1, ((h τ).1 hτ).2]
    simp [mult_zero]
  · rw [((h τ).2 hτ).1, ((h τ).2 hτ).2]
    simp [mult_zero]


/-- **A block factor of a bideterminant**: `∏_s ∏_c D_{τ,s+1}(rows_{s,c})`, the part of `bidet` in the block `τ`, for
any shape `m` of that block. -/
def bfac (τ : Φ) (m : Fin n → ℕ) (r : (s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n) : Pol Φ n L :=
  ∏ s : Fin n, ∏ c, minor τ s (r s c)

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A block factor of the zero shape** is `1`. -/
theorem bfac_eq_one {τ : Φ} {m : Fin n → ℕ} (hm : m = 0) (r : (s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n) :
    (bfac τ m r : Pol Φ n L) = 1 := by
  subst hm
  exact Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun c _ => absurd c.2 (by simp [mult_zero])

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Block factors depend only on the shape**: equal shapes have the same block factors. -/
theorem exists_bfac_eq {τ : Φ} {m m' : Fin n → ℕ} (hm : m = m')
    (r : (s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n) :
    ∃ r' : (s : Fin n) → Fin (mult m' s) → Fin (s + 1) → Fin n, (bfac τ m' r' : Pol Φ n L) = bfac τ m r := by
  subst hm
  exact ⟨r, rfl⟩

/-- **Rows of the zero shape** exist (there are none to choose). -/
theorem nonempty_rows_zero {m : Fin n → ℕ} (hm : m = 0) :
    Nonempty ((s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n) := by
  subst hm
  exact ⟨fun s c => absurd c.2 (by simp [mult_zero])⟩

omit [DecidableEq Φ] in
/-- **Bideterminants of split shapes multiply**: the product of bideterminants of shapes `ν₁` and `ν₂` is a
bideterminant of shape `ν`. -/
theorem bidet_split {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : Split P ν ν₁ ν₂) (rows₁ : BRows Φ n ν₁)
    (rows₂ : BRows Φ n ν₂) : ∃ rows : BRows Φ n ν, bidet L ν rows = bidet L ν₁ rows₁ * bidet L ν₂ rows₂ := by
  have key : ∀ τ, ∃ r : (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n,
      (bfac τ (ν τ) r : Pol Φ n L) = bfac τ (ν₁ τ) (rows₁ τ) * bfac τ (ν₂ τ) (rows₂ τ) := by
    intro τ
    by_cases hτ : P τ
    · obtain ⟨r, hr⟩ := exists_bfac_eq (L := L) (τ := τ) ((h τ).1 hτ).1 (rows₁ τ)
      exact ⟨r, by rw [hr, bfac_eq_one ((h τ).1 hτ).2, mul_one]⟩
    · obtain ⟨r, hr⟩ := exists_bfac_eq (L := L) (τ := τ) ((h τ).2 hτ).2 (rows₂ τ)
      exact ⟨r, by rw [hr, bfac_eq_one ((h τ).2 hτ).1, one_mul]⟩
  choose r hr using key
  refine ⟨r, ?_⟩
  show ∏ τ, bfac τ (ν τ) (r τ) = (∏ τ, bfac τ (ν₁ τ) (rows₁ τ)) * ∏ τ, bfac τ (ν₂ τ) (rows₂ τ)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => hr τ

omit [DecidableEq Φ] in
/-- **Bideterminants of a split shape factor**: a bideterminant of shape `ν` is the product of bideterminants of
shapes `ν₁` and `ν₂`. -/
theorem bidet_split' {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : Split P ν ν₁ ν₂) (rows : BRows Φ n ν) :
    ∃ (rows₁ : BRows Φ n ν₁) (rows₂ : BRows Φ n ν₂), bidet L ν rows = bidet L ν₁ rows₁ * bidet L ν₂ rows₂ := by
  have key : ∀ τ, ∃ (r₁ : (s : Fin n) → Fin (mult (ν₁ τ) s) → Fin (s + 1) → Fin n)
      (r₂ : (s : Fin n) → Fin (mult (ν₂ τ) s) → Fin (s + 1) → Fin n),
      (bfac τ (ν τ) (rows τ) : Pol Φ n L) = bfac τ (ν₁ τ) r₁ * bfac τ (ν₂ τ) r₂ := by
    intro τ
    by_cases hτ : P τ
    · obtain ⟨r, hr⟩ := exists_bfac_eq (L := L) (τ := τ) ((h τ).1 hτ).1.symm (rows τ)
      obtain ⟨r₂⟩ := nonempty_rows_zero ((h τ).1 hτ).2
      exact ⟨r, r₂, by rw [hr, bfac_eq_one ((h τ).1 hτ).2, mul_one]⟩
    · obtain ⟨r, hr⟩ := exists_bfac_eq (L := L) (τ := τ) ((h τ).2 hτ).2.symm (rows τ)
      obtain ⟨r₁⟩ := nonempty_rows_zero ((h τ).2 hτ).1
      exact ⟨r₁, r, by rw [hr, bfac_eq_one ((h τ).2 hτ).1, one_mul]⟩
  choose r₁ r₂ hr using key
  refine ⟨r₁, r₂, ?_⟩
  show ∏ τ, bfac τ (ν τ) (rows τ) = (∏ τ, bfac τ (ν₁ τ) (r₁ τ)) * ∏ τ, bfac τ (ν₂ τ) (r₂ τ)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => hr τ

omit [DecidableEq Φ] in
/-- **Twists split**: `twist_λ(F·G) = twist_{λ₁}(F)·twist_{λ₂}(G)` for a splitting of the weights (the determinant
factors of the two parts multiply, `lsub` is multiplicative). -/
theorem twist_mul_split {lam lam₁ lam₂ : Φ → Fin n → ℤ} (h : Split P lam lam₁ lam₂)
    (g : Φ → Matrix (Fin n) (Fin n) L) (F G : Pol Φ n L) :
    twist lam g (F * G) = twist lam₁ g F * twist lam₂ g G := by
  have e : ∏ σ, (g σ).det ^ detShift (lam σ) =
      (∏ σ, (g σ).det ^ detShift (lam₁ σ)) * ∏ σ, (g σ).det ^ detShift (lam₂ σ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun σ _ => ?_
    by_cases hσ : P σ
    · rw [((h σ).1 hσ).1, ((h σ).1 hσ).2, detShift_zero, zpow_zero, mul_one]
    · rw [((h σ).2 hσ).1, ((h σ).2 hσ).2, detShift_zero, zpow_zero, one_mul]
  simp only [twist, map_mul, e]
  ring

/-- **The first part is supported on `P`**: a polynomial of a shape vanishing off `P`. -/
theorem mem_supported_left {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : Split P ν ν₁ ν₂) {F : Pol Φ n L}
    (hF : F ∈ nabla L ν₁) : F ∈ supported L {v | P v.1} :=
  mem_supported_of_isWH P (fun τ hτ => ((h τ).2 hτ).1) (mem_nabla_iff.1 hF).1

/-- **The second part is supported off `P`**: a polynomial of a shape vanishing on `P`. -/
theorem mem_supported_right {ν ν₁ ν₂ : Φ → Fin n → ℕ} (h : Split P ν ν₁ ν₂) {F : Pol Φ n L}
    (hF : F ∈ nabla L ν₂) : F ∈ supported L {v | P v.1}ᶜ :=
  mem_supported_of_isWH (fun τ => ¬ P τ) (fun τ hτ => ((h τ).1 (not_not.1 hτ)).2) (mem_nabla_iff.1 hF).1

/-- **The constant `κ` splits**: `κ(λ) = κ(λ₁)·κ(λ₂)` for a splitting of dominant weights (`hw_split`,
`fock_mul_split`). -/
theorem kappa_split {lam lam₁ lam₂ : Φ → Fin n → ℤ} (h : Split P lam lam₁ lam₂) (h₁ : ∀ b, Antitone (lam₁ b))
    (h₂ : ∀ b, Antitone (lam₂ b)) : HermForms.kappa lam = HermForms.kappa lam₁ * HermForms.kappa lam₂ := by
  have hn := h.map natW natW_zero
  have m₁ := hw_mem_nabla (L := ℚ) fun b => natW_antitone (h₁ b)
  have m₂ := hw_mem_nabla (L := ℚ) fun b => natW_antitone (h₂ b)
  unfold HermForms.kappa
  rw [hw_split hn]
  exact fock_mul_split (mem_supported_left hn m₁) (mem_supported_left hn m₁) (mem_supported_right hn m₂)
    (mem_supported_right hn m₂)

/-- **The normalised Fock form splits**: `⟨F₁G₁, F₂G₂⟩_λ = ⟨F₁, F₂⟩_{λ₁}·⟨G₁, G₂⟩_{λ₂}` for `F_i ∈ ∇(λ₁)`,
`G_i ∈ ∇(λ₂)` and a splitting of dominant weights. -/
theorem nf_split [CharZero L] {lam lam₁ lam₂ : Φ → Fin n → ℤ} (h : Split P lam lam₁ lam₂)
    (h₁ : ∀ b, Antitone (lam₁ b)) (h₂ : ∀ b, Antitone (lam₂ b)) {F₁ F₂ G₁ G₂ : Pol Φ n L}
    (hF₁ : F₁ ∈ nabla L fun b => natW (lam₁ b)) (hF₂ : F₂ ∈ nabla L fun b => natW (lam₁ b))
    (hG₁ : G₁ ∈ nabla L fun b => natW (lam₂ b)) (hG₂ : G₂ ∈ nabla L fun b => natW (lam₂ b)) :
    nf lam (F₁ * G₁) (F₂ * G₂) = nf lam₁ F₁ F₂ * nf lam₂ G₁ G₂ := by
  have hn := h.map natW natW_zero
  simp only [nf_apply]
  rw [fock_mul_split (mem_supported_left hn hF₁) (mem_supported_left hn hF₂) (mem_supported_right hn hG₁)
    (mem_supported_right hn hG₂), kappa_split h h₁ h₂, map_mul, div_mul_div_comm]


/-- **The dimension is at most the product** of the dimensions of the parts: `∇(ν)` is spanned by the products of
bideterminants of shapes `ν₁`, `ν₂` (`span_bidet`, `bidet_split'`), hence by the products `zb_i·zb′_j` of the bases of
the parts (`span_zbK`, `linearIndependent_zbK`). -/
theorem finrank_nabla_le [CharZero L] {lam lam₁ lam₂ : Φ → Fin n → ℤ} (h : Split P lam lam₁ lam₂)
    (hl : ∀ b, Antitone (lam b)) (h₁ : ∀ b, Antitone (lam₁ b)) (h₂ : ∀ b, Antitone (lam₂ b)) :
    Module.finrank L (nabla L fun b => natW (lam b)) ≤
      Module.finrank L (nabla L fun b => natW (lam₁ b)) * Module.finrank L (nabla L fun b => natW (lam₂ b)) := by
  have hn := h.map natW natW_zero
  set f : ZIdx lam₁ × ZIdx lam₂ → Pol Φ n L := fun x => zbK L lam₁ x.1 * zbK L lam₂ x.2
  have hle : nabla L (fun b => natW (lam b)) ≤ Submodule.span L (Set.range f) := by
    rw [← span_bidet fun b => natW_antitone (hl b), Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    obtain ⟨r₁, r₂, hr⟩ := bidet_split' (L := L) hn rows
    have m₁ : bidet L _ r₁ ∈ Submodule.span L (Set.range (zbK L lam₁)) := by
      rw [span_zbK L h₁]
      exact bidet_mem_nabla (fun b => natW_antitone (h₁ b)) r₁
    have m₂ : bidet L _ r₂ ∈ Submodule.span L (Set.range (zbK L lam₂)) := by
      rw [span_zbK L h₂]
      exact bidet_mem_nabla (fun b => natW_antitone (h₂ b)) r₂
    have hm := Submodule.mul_mem_mul m₁ m₂
    rw [Submodule.span_mul_span] at hm
    rw [SetLike.mem_coe, hr]
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(i, l), rfl⟩
  have : Module.Finite L (Submodule.span L (Set.range f)) := Module.Finite.span_of_finite L (Set.finite_range f)
  calc Module.finrank L (nabla L fun b => natW (lam b)) ≤ Module.finrank L (Submodule.span L (Set.range f)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (ZIdx lam₁ × ZIdx lam₂) := finrank_range_le_card f
    _ = _ := by
        rw [Fintype.card_prod, ← span_zbK L h₁, ← span_zbK L h₂, finrank_span_eq_card (linearIndependent_zbK L lam₁),
          finrank_span_eq_card (linearIndependent_zbK L lam₂)]

end Poly

/-! ## Lattices of split weights -/

section Lattice

variable {β : Type} [Fintype β] [DecidableEq β] {k : ℕ} {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
  {P : β → Prop}

omit [DecidableEq β] in
/-- **Products of integral bideterminant spans**: `∇_A(ν₁)·∇_A(ν₂) ⊆ ∇_A(ν)` for a splitting of the shape. -/
theorem mul_mem_nablaInt {A : Subring Kf} {ν ν₁ ν₂ : β → Fin k → ℕ} (h : Split P ν ν₁ ν₂) {F G : Pol β k Kf}
    (hF : F ∈ nablaInt A ν₁) (hG : G ∈ nablaInt A ν₂) : F * G ∈ nablaInt A ν := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r₁, rfl⟩ := hx
      obtain ⟨r₂, rfl⟩ := hy
      obtain ⟨r, hr⟩ := bidet_split (L := Kf) h r₁ r₂
      rw [← hr]
      exact Submodule.subset_span ⟨r, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [show a • y = (a : Kf) • y from rfl, mul_smul_comm]
      exact Submodule.smul_mem _ a hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : Kf) • x from rfl, smul_mul_assoc]
    exact Submodule.smul_mem _ a hx

/-- **Products of `∇`-lattices**: `∇_Λ(λ₁)·∇_Λ(λ₂) ⊆ ∇_Λ(λ)` for a splitting of the weights, at any family of block
lattices `Λ` (`twist_mul_split`, `mul_mem_nablaInt`). -/
theorem mul_mem_nablaB {lam lam₁ lam₂ : β → Fin k → ℤ} (h : Split P lam lam₁ lam₂)
    {Λ : β → Submodule O (Fin k → Kf)} {F G : Pol β k Kf} (hF : F ∈ nablaB lam₁ Λ) (hG : G ∈ nablaB lam₂ Λ) :
    F * G ∈ nablaB lam Λ := by
  have hn := h.map natW natW_zero
  obtain ⟨hF1, C, hC, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := (mem_nablaB_iff hC).1 hG
  refine ⟨mul_mem_nabla (funext hn.add) hF1 hG1, C, hC, ?_⟩
  rw [twist_mul_split h]
  exact mul_mem_nablaInt hn hF2 hG2

/-- **`∇_Λ(λ)` is spanned by products**: every element of `∇_Λ(λ)` is an `O`-combination of products `F₁·F₂`,
`F_i ∈ ∇_Λ(λ_i)`, for a splitting of dominant weights. In basis matrices `C` of the blocks, the twist by `C` of `F` is
a combination of bideterminants, which factor (`bidet_split'`), and the twist by `C⁻¹` splits (`twist_mul_split`). -/
theorem mem_span_mul_of_nablaB {lam lam₁ lam₂ : β → Fin k → ℤ} (h : Split P lam lam₁ lam₂)
    (h₁ : ∀ b, Antitone (lam₁ b)) (h₂ : ∀ b, Antitone (lam₂ b)) {Λ : β → Submodule O (Fin k → Kf)}
    {F : Pol β k Kf} (hF : F ∈ nablaB lam Λ) :
    F ∈ Submodule.span O (Set.image2 (· * ·) (nablaB lam₁ Λ) (nablaB lam₂ Λ)) := by
  have hn := h.map natW natW_zero
  obtain ⟨-, C, hC, hF2⟩ := hF
  have hCu : ∀ b, IsUnit (C b).det := fun b => (hC b).1
  rw [← twist_inv_twist lam hCu F]
  generalize twist lam C F = G at hF2
  induction hF2 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨r₁, r₂, hr⟩ := bidet_split' (L := Kf) hn r
    rw [hr, twist_mul_split h]
    refine Submodule.subset_span ⟨_, ⟨twist_mem_nabla _ _ (bidet_mem_nabla (fun b => natW_antitone (h₁ b)) r₁), C,
      hC, ?_⟩, _, ⟨twist_mem_nabla _ _ (bidet_mem_nabla (fun b => natW_antitone (h₂ b)) r₂), C, hC, ?_⟩, rfl⟩
    · rw [twist_twist_inv lam₁ hCu]
      exact Submodule.subset_span ⟨r₁, rfl⟩
    · rw [twist_twist_inv lam₂ hCu]
      exact Submodule.subset_span ⟨r₂, rfl⟩
  | zero => rw [twist_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [twist_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨o, ho⟩ := a.2
    rw [show a • x = (a : Kf) • x from rfl, twist_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o hx

variable [CharZero Kf]

/-- **Duals of products**: if `y` is integral against `∇_Λ(λ₁)` and `ρ` against `∇_Λ(λ₂)` (for `⟨·,·⟩`), then
`y·ρ` is integral against `∇_Λ(λ)`, for a splitting of dominant weights (`mem_span_mul_of_nablaB`, `nf_split`). -/
theorem mul_mem_bdual {lam lam₁ lam₂ : β → Fin k → ℤ} (h : Split P lam lam₁ lam₂) (h₁ : ∀ b, Antitone (lam₁ b))
    (h₂ : ∀ b, Antitone (lam₂ b)) {Λ : β → Submodule O (Fin k → Kf)} {y ρ : Pol β k Kf}
    (hy : y ∈ bdual O (nf lam₁) (fun b => natW (lam₁ b)) (nablaB lam₁ Λ))
    (hρ : ρ ∈ bdual O (nf lam₂) (fun b => natW (lam₂ b)) (nablaB lam₂ Λ)) :
    y * ρ ∈ bdual O (nf lam) (fun b => natW (lam b)) (nablaB lam Λ) := by
  have hn := h.map natW natW_zero
  refine ⟨mul_mem_nabla (funext hn.add) hy.1 hρ.1, fun F hF => ?_⟩
  have hs := mem_span_mul_of_nablaB h h₁ h₂ hF
  clear hF
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F₁, hF₁, F₂, hF₂, rfl⟩ := hx
    rw [nf_split h h₁ h₂ hF₁.1 hy.1 hF₂.1 hρ.1]
    exact mul_mem (hy.2 F₁ hF₁) (hρ.2 F₂ hF₂)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply]; exact add_mem hx hz
  | smul o x _ hx =>
    rw [← algebraMap_smul Kf o x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem ⟨o, rfl⟩ hx

end Lattice

/-! ## The top and off-top parts of a weight -/

section Parts

variable {n' k : ℕ}

/-- **The off-top part** of a weight: `0` at the tops, `λ` elsewhere (`topPart` is the other half). -/
def offPart (TT : Finset (Fin n')) (lam0 : Fin n' → Fin k → ℤ) : Fin n' → Fin k → ℤ :=
  fun s => if s ∈ TT then 0 else lam0 s

/-- **`lamAt` depends only on the entry at the position.** -/
theorem lamAt_congr {f g : Fin n' → Fin k → ℤ} {s : Fin n'} (h : f s = g s) : lamAt f s = lamAt g s := by
  simp only [lamAt, h]

/-- **`lamAt` of a zero entry is zero.** -/
theorem lamAt_eq_zero {f : Fin n' → Fin k → ℤ} {s : Fin n'} (h : f s = 0) : lamAt f s = 0 := by
  funext i
  simp only [lamAt, h]
  split_ifs <;> simp

/-- **The block weights split** into those of the top part and of the off-top part, along the tops. -/
theorem split_wt1 (TT : Finset (Fin n')) (lam0 : Fin n' → Fin k → ℤ) :
    Split (fun b : Unit × Fin n' => b.2 ∈ TT) (wt1 lam0) (wt1 (topPart TT lam0)) (wt1 (offPart TT lam0)) :=
  fun _ => ⟨fun hb => ⟨lamAt_congr (by simp [topPart, hb]), lamAt_eq_zero (by simp [offPart, hb])⟩,
    fun hb => ⟨lamAt_eq_zero (by simp [topPart, hb]), lamAt_congr (by simp [offPart, hb])⟩⟩

/-- **The top part of a dominant weight is dominant.** -/
theorem antitone_topPart {TT : Finset (Fin n')} {lam0 : Fin n' → Fin k → ℤ} (h : ∀ s, Antitone (lam0 s))
    (s : Fin n') : Antitone (topPart TT lam0 s) := by
  unfold topPart
  split_ifs
  · exact h s
  · exact antitone_const

/-- **The off-top part of a dominant weight is dominant.** -/
theorem antitone_offPart {TT : Finset (Fin n')} {lam0 : Fin n' → Fin k → ℤ} (h : ∀ s, Antitone (lam0 s))
    (s : Fin n') : Antitone (offPart TT lam0 s) := by
  unfold offPart
  split_ifs
  · exact antitone_const
  · exact h s

/-- **`A_r` is additive** over the two parts. -/
theorem topA_split (r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin k → ℤ) :
    topA r lam0 = topA r (topPart TT lam0) + topA r (offPart TT lam0) := by
  simp only [topA, topSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => congrFun ((split_wt1 TT lam0).add ((), s)) i

/-- **The spread of the off-top part**: `A_1(λ^off) − Σ_b λ^off_{b,k−1} ≤ 2n′c` when every entry off the tops lies in
`[−c, c]`: each position contributes at most `c` to each term. -/
theorem topA_sub_le {TT : Finset (Fin n')} {lam0 : Fin n' → Fin k → ℤ} {c : ℕ}
    (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c) :
    topA 1 (offPart TT lam0) - ∑ b, detShift (wt1 (offPart TT lam0) b) ≤ 2 * n' * c := by
  have hb : ∀ s i, |lamAt (offPart TT lam0) s i| ≤ c := fun s i => by
    by_cases hs : s ∈ TT
    · rw [lamAt_eq_zero (by simp [offPart, hs])]
      simp
    · simp only [lamAt, offPart, hs, ite_false]
      split_ifs
      · exact hc s hs i
      · rw [abs_neg]
        exact hc s hs _
  have hone : ∀ s, ∑ i : Fin k with i.val < 1, lamAt (offPart TT lam0) s i ≤ c := fun s => by
    have hcard : (Finset.univ.filter fun i : Fin k => i.val < 1).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => Fin.ext (by
        simp only [Finset.mem_filter] at ha hb
        omega)
    calc ∑ i : Fin k with i.val < 1, lamAt (offPart TT lam0) s i ≤ ∑ i : Fin k with i.val < 1, (c : ℤ) :=
          Finset.sum_le_sum fun i _ => (abs_le.1 (hb s i)).2
      _ = (Finset.univ.filter fun i : Fin k => i.val < 1).card * (c : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = c := one_mul _
  have hlast : ∀ s, -detShift (lamAt (offPart TT lam0) s) ≤ c := fun s => by
    unfold detShift
    split_ifs
    · exact neg_le.1 (abs_le.1 (hb s _)).1
    · simp
  have e : ∑ b : Unit × Fin n', detShift (wt1 (offPart TT lam0) b) =
      ∑ s : Fin n', detShift (lamAt (offPart TT lam0) s) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  rw [e]
  simp only [topA, topSum]
  rw [← Finset.sum_sub_distrib]
  calc ∑ s : Fin n', (∑ i : Fin k with i.val < 1, lamAt (offPart TT lam0) s i - detShift (lamAt (offPart TT lam0) s))
      ≤ ∑ _s : Fin n', (2 * c : ℤ) := Finset.sum_le_sum fun s _ => by linarith [hone s, hlast s]
    _ = 2 * n' * c := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Parts

/-! ## The off-top part at an edge -/

section Edge

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **The adapted basis with its lower exponent bound**: `exists_adapted_basis` with `π_i = pexp i`, which is at
least `r·Σ_b λ_{b,k−1}` (the row weights in `pexp` are `≥ 0`). -/
theorem exists_adapted_basis_ge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    ∃ (x : ZIdx (wt1 lam0) → Pol (Unit × Fin n') k Kf) (π : ZIdx (wt1 lam0) → ℤ),
      nab O ι σ lam0 L'' = (Submodule.span O (Set.range x) : Set (Pol (Unit × Fin n') k Kf)) ∧
      nab O ι σ lam0 L = (Submodule.span O (Set.range fun i => (p : Kf) ^ π i • x i) :
        Set (Pol (Unit × Fin n') k Kf)) ∧
      nabMid ι σ ϖ lam0 L'' L = (Submodule.span O (Set.range fun i => algebraMap O Kf ϖ ^ π i • x i) :
        Set (Pol (Unit × Fin n') k Kf)) ∧
      ∀ i, (r : ℤ) * ∑ b, detShift (wt1 lam0 b) ≤ π i := by
  obtain ⟨B, S, hS, hB, hLB, hL''B⟩ := exists_basis_edge hU he
  have hϖ := varpiK_ne_zero hU
  have hp : (p : Kf) ≠ 0 := hU.castK_ne_zero
  set C : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf := fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B
  set D : Kf → Unit × Fin n' → Matrix (Fin k) (Fin k) Kf := fun c b => Matrix.diagonal (dg (fun _ => S) c b)
  have hC : ∀ b, IsBasisOf (blk (O := O) ι σ b.2 L) (C b) := fun b => isBasisOf_blk hU _ hB hLB
  have hC'' : ∀ b, IsBasisOf (blk (O := O) ι σ b.2 L'') (C b * D p b) := fun b => isBasisOf_blk_edge hU _ hB hL''B
  have hCm : ∀ b, IsBasisOf (midBlk ι σ ϖ b.2 L'' L) (C b * D (algebraMap O Kf ϖ) b) := fun b =>
    isBasisOf_midBlk hU _ hB hLB hL''B
  have hlam' : ∀ b, Antitone (wt1 lam0 b) := antitone_blockWt fun _ => hlam
  have key : ∀ {c : Kf}, c ≠ 0 → ∀ i, twist (wt1 lam0) (fun b => (C b * D c b)⁻¹) (zbK Kf (wt1 lam0) i) =
      c ^ (-pexp (wt1 lam0) S i) • twist (wt1 lam0) (fun b => (C b)⁻¹) (zbK Kf (wt1 lam0) i) := by
    intro c hc i
    have e : (fun b => (C b * D c b)⁻¹) = fun b => D c⁻¹ b * (C b)⁻¹ := funext fun b => by
      rw [Matrix.mul_inv_rev, inv_diag_dg _ hc]
    rw [e, ← twist_twist, twist_diag_zbK _ _ (inv_ne_zero hc), twist_smul, inv_zpow']
  set π := pexp (wt1 lam0) S
  set x := fun i => twist (wt1 lam0) (fun b => (C b * D p b)⁻¹) (zbK Kf (wt1 lam0) i)
  have hxL : ∀ i, twist (wt1 lam0) (fun b => (C b)⁻¹) (zbK Kf (wt1 lam0) i) = (p : Kf) ^ π i • x i := fun i => by
    simp only [x]
    rw [key hp, smul_smul, ← zpow_add₀ hp, add_neg_cancel, zpow_zero, one_smul]
  have hxm : ∀ i, twist (wt1 lam0) (fun b => (C b * D (algebraMap O Kf ϖ) b)⁻¹) (zbK Kf (wt1 lam0) i) =
      algebraMap O Kf ϖ ^ π i • x i := fun i => by
    rw [key hϖ, hxL, smul_smul, castK_eq_sq hU, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hϖ]
    congr 2
    push_cast
    ring
  refine ⟨x, π, nablaB_eq_span hlam' hC'', ?_, ?_, fun i => ?_⟩
  · rw [show nab O ι σ lam0 L = nablaB (wt1 lam0) fun b => blk ι σ b.2 L from rfl, nablaB_eq_span hlam' hC]
    simp only [hxL]
  · rw [nabMid_eq, nablaB_eq_span hlam' hCm]
    simp only [hxm]
  · simp only [π, pexp, hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

omit [CharZero Kf] in
/-- **`p^A = ϖ^{2A}`** for integer exponents. -/
theorem castK_zpow (hU : Unram p n' W Qq O Kf ι σ j ϖ) (A : ℤ) :
    (p : Kf) ^ A = algebraMap O Kf ϖ ^ (2 * A) := by
  rw [castK_eq_sq hU, ← zpow_natCast, ← zpow_mul]
  norm_num

/-- **The off-top edge lattice lies in `ϖ^{−2n′c}∇(L″)`** (N18): in the adapted basis `𝓡(e)` is spanned by the
`ϖ^{π_i − A}x_i` and `A − π_i ≤ 2n′c` (`topA_sub_le`). -/
theorem smul_mem_nab_of_edgeLat_off (hU : Unram p n' W Qq O Kf ι σ j ϖ) {TT : Finset (Fin n')}
    {lam0 : Fin n' → Fin k → ℤ} {c : ℕ} (hlam : ∀ s, Antitone (lam0 s)) (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c)
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ edgeLat ι σ ϖ 1 (offPart TT lam0) L'' L) :
    algebraMap O Kf ϖ ^ (2 * n' * c) • F ∈ nab O ι σ (offPart TT lam0) L'' := by
  obtain ⟨x, π, hx'', -, hxm, hπ⟩ := exists_adapted_basis_ge hU (antitone_offPart (TT := TT) hlam) he
  have hϖ := varpiK_ne_zero hU
  have hbd := topA_sub_le hc
  set A := topA 1 (offPart TT lam0)
  have hF' : algebraMap O Kf ϖ ^ A • F ∈ Submodule.span O (Set.range fun i => algebraMap O Kf ϖ ^ π i • x i) := by
    rw [← SetLike.mem_coe, ← hxm]
    exact hF
  have e : algebraMap O Kf ϖ ^ (2 * n' * c) • F =
      algebraMap O Kf ϖ ^ (((2 * n' * c : ℕ) : ℤ) - A) • (algebraMap O Kf ϖ ^ A • F) := by
    rw [smul_smul, ← zpow_add₀ hϖ, sub_add_cancel, zpow_natCast]
  rw [e, hx'', SetLike.mem_coe]
  refine smul_mem_span_range (fun i => ?_) hF'
  have hi : 0 ≤ ((2 * n' * c : ℕ) : ℤ) - A + π i := by
    have := hπ i
    push_cast at this ⊢
    linarith
  rw [smul_smul, ← zpow_add₀ hϖ, algebraMap_zpow_eq _ hi, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The off-top dual edge lattice lies in `ϖ^{−2n′c}∇(L)^∨`** (N18): for `F ∈ ∇(L) = span(p^{π_i}x_i)`,
`ϖ^{2n′c − 2A}F ∈ 𝓡(e)` (as `A − π_i ≤ 2n′c`), and its `pairE` with `G` is `⟨F, ϖ^{2n′c}G⟩`. -/
theorem smul_mem_bdual_of_edgeDual_off (hU : Unram p n' W Qq O Kf ι σ j ϖ) {TT : Finset (Fin n')}
    {lam0 : Fin n' → Fin k → ℤ} {c : ℕ} (hlam : ∀ s, Antitone (lam0 s)) (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c)
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) {G : Pol (Unit × Fin n') k Kf}
    (hG : G ∈ edgeDual p 1 ι σ ϖ (offPart TT lam0) L'' L) :
    algebraMap O Kf ϖ ^ (2 * n' * c) • G ∈
      bdual O (nf (wt1 (offPart TT lam0))) (nu1 (offPart TT lam0)) (nab O ι σ (offPart TT lam0) L) := by
  obtain ⟨x, π, -, hxL, hxm, hπ⟩ := exists_adapted_basis_ge hU (antitone_offPart (TT := TT) hlam) he
  have hϖ := varpiK_ne_zero hU
  have hbd := topA_sub_le hc
  set A := topA 1 (offPart TT lam0)
  set m : ℤ := ((2 * n' * c : ℕ) : ℤ)
  refine ⟨Submodule.smul_mem _ _ hG.1, fun F hF => ?_⟩
  have hF' : algebraMap O Kf ϖ ^ (m - 2 * A) • F ∈ edgeLat ι σ ϖ 1 (offPart TT lam0) L'' L := by
    show _ ∈ nabMid ι σ ϖ (offPart TT lam0) L'' L
    rw [smul_smul, ← zpow_add₀ hϖ, hxm, SetLike.mem_coe]
    rw [hxL, SetLike.mem_coe] at hF
    refine smul_mem_span_range (fun i => ?_) hF
    have hi : 0 ≤ m - A + π i := by
      have := hπ i
      simp only [m]
      push_cast at this ⊢
      linarith
    rw [castK_zpow hU, smul_smul, ← zpow_add₀ hϖ,
      show A + (m - 2 * A) + 2 * π i = (m - A + π i) + π i by ring, zpow_add₀ hϖ, ← smul_smul,
      algebraMap_zpow_eq _ hi, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h := hG.2 _ hF'
  rw [pairE_apply, smul_smul, castK_zpow hU, ← zpow_add₀ hϖ, show 2 * A + (m - 2 * A) = m by ring] at h
  rw [map_smul, smul_eq_mul, ← zpow_natCast]
  rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at h

omit [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **The dual of a scaled set**: `G ∈ (a·S)^∨` iff `a·G ∈ S^∨`. -/
theorem mem_bdual_smul_iff {β : Type} [Fintype β] [DecidableEq β] (B : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Kf)
    (ν : β → Fin k → ℕ) (S : Set (Pol β k Kf)) {a : Kf} (ha : a ≠ 0) {G : Pol β k Kf} :
    G ∈ bdual O B ν (a • S) ↔ a • G ∈ bdual O B ν S := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ _ h1, fun F hF => ?_⟩
    have := h2 (a • F) (Set.smul_mem_smul_set hF)
    simp only [map_smul, LinearMap.smul_apply] at this ⊢
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun F' hF' => ?_⟩
    · have := Submodule.smul_mem _ a⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    · obtain ⟨F, hF, rfl⟩ := Set.mem_smul_set.1 hF'
      have := h2 F hF
      simp only [map_smul, LinearMap.smul_apply] at this ⊢
      exact this

/-- **The dual edge lattice through the midpoint**: `G ∈ 𝓡′(e)` iff `ϖ^{A_r}G ∈ ∇(mid)^∨` (as `p^{A_r} = ϖ^{2A_r}`). -/
theorem mem_edgeDual_iff (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r : ℕ}
    {L₁ L : Submodule W (Fin k → Qq)} {G : Pol (Unit × Fin n') k Kf} :
    G ∈ edgeDual p r ι σ ϖ lam0 L₁ L ↔
      algebraMap O Kf ϖ ^ topA r lam0 • G ∈ bdual O (nf (wt1 lam0)) (nu1 lam0) (nabMid ι σ ϖ lam0 L₁ L) := by
  have hϖ := varpiK_ne_zero hU
  have ha : algebraMap O Kf ϖ ^ topA r lam0 ≠ 0 := zpow_ne_zero _ hϖ
  have hpa : (p : Kf) ^ topA r lam0 = algebraMap O Kf ϖ ^ topA r lam0 * algebraMap O Kf ϖ ^ topA r lam0 := by
    rw [castK_zpow hU, ← zpow_add₀ hϖ, two_mul]
  constructor
  · rintro ⟨hG1, hG2⟩
    refine ⟨Submodule.smul_mem _ _ hG1, fun H hH => ?_⟩
    have hH' : (algebraMap O Kf ϖ ^ topA r lam0)⁻¹ • H ∈ edgeLat ι σ ϖ r lam0 L₁ L := by
      show algebraMap O Kf ϖ ^ topA r lam0 • ((algebraMap O Kf ϖ ^ topA r lam0)⁻¹ • H) ∈ nabMid ι σ ϖ lam0 L₁ L
      rwa [smul_smul, mul_inv_cancel₀ ha, one_smul]
    have h := hG2 _ hH'
    rw [pairE_apply, smul_smul, hpa, mul_assoc, mul_inv_cancel₀ ha, mul_one] at h
    rw [map_smul, smul_eq_mul]
    rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  · rintro ⟨hG1, hG2⟩
    refine ⟨?_, fun F hF => ?_⟩
    · have := Submodule.smul_mem _ (algebraMap O Kf ϖ ^ topA r lam0)⁻¹ hG1
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    · have h := hG2 _ hF
      rw [pairE_apply, hpa, ← smul_smul]
      rw [map_smul, smul_eq_mul] at h
      rwa [map_smul, LinearMap.smul_apply, smul_eq_mul]

end Edge

/-! ## Products of sources and targets -/

section Prod

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {TT : Finset (Fin n')}
  {lam0 : Fin n' → Fin k → ℤ}

omit [CharZero Kf] in
/-- **Products of edge lattices**: `𝓡_top(e)·𝓡_off(e) ⊆ 𝓡_λ(e)` (`A_r` is additive, `mul_mem_nablaB` at the
midpoint). -/
theorem mul_mem_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    {F G : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r (topPart TT lam0) L'' L)
    (hG : G ∈ edgeLat ι σ ϖ r (offPart TT lam0) L'' L) : F * G ∈ edgeLat ι σ ϖ r lam0 L'' L := by
  show _ ∈ nabMid ι σ ϖ lam0 L'' L
  rw [topA_split r TT lam0, zpow_add₀ (varpiK_ne_zero hU), ← smul_mul_smul_comm]
  exact mul_mem_nablaB (split_wt1 TT lam0) hF hG

/-- **Products of dual edge lattices**: `𝓡′_top(e)·𝓡′_off(e) ⊆ 𝓡′_λ(e)` for dominant `λ` (`mem_edgeDual_iff`,
`mul_mem_bdual` at the midpoint). -/
theorem mul_mem_edgeDual (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ}
    {L₁ L : Submodule W (Fin k → Qq)} {y ρ : Pol (Unit × Fin n') k Kf}
    (hy : y ∈ edgeDual p r ι σ ϖ (topPart TT lam0) L₁ L) (hρ : ρ ∈ edgeDual p r ι σ ϖ (offPart TT lam0) L₁ L) :
    y * ρ ∈ edgeDual p r ι σ ϖ lam0 L₁ L := by
  rw [mem_edgeDual_iff hU] at hy hρ ⊢
  rw [topA_split r TT lam0, zpow_add₀ (varpiK_ne_zero hU), ← smul_mul_smul_comm]
  exact mul_mem_bdual (split_wt1 TT lam0) (antitone_blockWt fun _ => antitone_topPart hlam)
    (antitone_blockWt fun _ => antitone_offPart hlam) hy hρ

/-- **`pairE` splits**: `pairE_λ(F₁G₁, F₂G₂) = pairE_top(F₁, F₂)·pairE_off(G₁, G₂)` (`nf_split`, `topA_split`). -/
theorem pairE_split (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hlam : ∀ s, Antitone (lam0 s)) (r : ℕ)
    {F₁ F₂ G₁ G₂ : Pol (Unit × Fin n') k Kf} (hF₁ : F₁ ∈ nabla Kf (nu1 (topPart TT lam0)))
    (hF₂ : F₂ ∈ nabla Kf (nu1 (topPart TT lam0))) (hG₁ : G₁ ∈ nabla Kf (nu1 (offPart TT lam0)))
    (hG₂ : G₂ ∈ nabla Kf (nu1 (offPart TT lam0))) :
    pairE p r lam0 (F₁ * G₁) (F₂ * G₂) = pairE p r (topPart TT lam0) F₁ F₂ * pairE p r (offPart TT lam0) G₁ G₂ := by
  simp only [pairE, LinearMap.smul_apply, smul_eq_mul]
  rw [nf_split (split_wt1 TT lam0) (antitone_blockWt fun _ => antitone_topPart hlam)
    (antitone_blockWt fun _ => antitone_offPart hlam) hF₁ hF₂ hG₁ hG₂, topA_split r TT lam0,
    zpow_add₀ hU.castK_ne_zero]
  ring

/-- **Sources times off-top edge vectors** (N18, source side): for `F` in the source family of the top part at
`(t, c₃)` and `G ∈ 𝓡_off(e)`, `F·G` is in the source family of `λ` at `(t + 2n′c, c₃ − 2n′c)`. With
`G₀ = ϖ^{2n′c}G ∈ ∇_off(L″)`: `F·G ∈ ϖ^{−t−2n′c}∇(L″)`; on `e`, `F·G ∈ 𝓡_top(e)·𝓡_off(e)`; on `e′ ≠ e`,
`F·G = ϖ^{c₃−2n′c}·F₁G₀` with `F₁ ∈ 𝓡_top(e′)` and `G₀ ∈ ∇_off(L″) ⊆ 𝓡_off(e′)`. -/
theorem mul_mem_srcFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {c t c₃ : ℕ} (hlam : ∀ s, Antitone (lam0 s))
    (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c) (hc₃ : 2 * n' * c ≤ c₃) {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) {F G : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ SrcFam p 1 ι σ ϖ (topPart TT lam0) t c₃ L'' L) (hG : G ∈ edgeLat ι σ ϖ 1 (offPart TT lam0) L'' L) :
    F * G ∈ SrcFam p 1 ι σ ϖ lam0 (t + 2 * n' * c) (c₃ - 2 * n' * c) L'' L := by
  have hϖ := varpiK_ne_zero hU
  obtain ⟨⟨hF1, hF2⟩, hF3⟩ := hF
  have hG0 := smul_mem_nab_of_edgeLat_off hU hlam hc he hG
  have hother : ∀ L', IsEdge (n' := n') p 1 L'' L' → L' ≠ L → ∃ H ∈ edgeLat ι σ ϖ 1 lam0 L'' L',
      F * G = algebraMap O Kf ϖ ^ (c₃ - 2 * n' * c) • H := by
    intro L' he' hne
    obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hF3 L' he') hne)
    refine ⟨F₁ * (algebraMap O Kf ϖ ^ (2 * n' * c) • G),
      mul_mem_edgeLat hU hF₁ (nab_subset_edgeLat hU (antitone_offPart hlam) he' hG0), ?_⟩
    rw [mul_smul_comm, smul_smul, smul_mul_assoc, ← pow_add, Nat.sub_add_cancel hc₃]
  refine ⟨⟨?_, Set.mem_iInter₂.2 fun L' he' => ?_⟩, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
  · obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 hF1
    refine Set.mem_smul_set.2 ⟨F₀ * (algebraMap O Kf ϖ ^ (2 * n' * c) • G),
      mul_mem_nablaB (split_wt1 TT lam0) hF₀ hG0, ?_⟩
    rw [mul_smul_comm, smul_smul, smul_mul_assoc, pow_add, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hϖ), mul_one]
  · by_cases hL : L' = L
    · subst hL
      exact mul_mem_edgeLat hU (Set.mem_iInter₂.1 hF2 L' he') hG
    · obtain ⟨H, hH, e⟩ := hother L' he' hL
      rw [e]
      exact smul_mem_edgeLat ⟨ϖ ^ (c₃ - 2 * n' * c), by rw [map_pow]⟩ hH
  · obtain ⟨H, hH, e⟩ := hother L' he' hne
    exact Set.mem_smul_set.2 ⟨H, hH, e.symm⟩

/-- **Targets times off-top dual edge vectors** (N18, target side): for `y` in the target family of the top part at
`(t, c₃)` and `ρ ∈ 𝓡′_off(e)`, `y·ρ` is in the target family of `λ` at `(t + 2n′c, c₃ − 2n′c)`. With
`ρ₀ = ϖ^{2n′c}ρ ∈ ∇_off(L)^∨`: `ϖ^{t+2n′c}yρ ∈ ∇(L)^∨` (`mul_mem_bdual`); on `e`, `y·ρ ∈ 𝓡′_top(e)·𝓡′_off(e)`; on
`e₁ ≠ e`, `y·ρ = ϖ^{c₃−2n′c}·y₁ρ₀` with `y₁ ∈ 𝓡′_top(e₁)` and `ρ₀ ∈ ∇_off(L)^∨ ⊆ 𝓡′_off(e₁)`. -/
theorem mul_mem_tgtFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {c t c₃ : ℕ} (hlam : ∀ s, Antitone (lam0 s))
    (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c) (hc₃ : 2 * n' * c ≤ c₃) {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) {y ρ : Pol (Unit × Fin n') k Kf}
    (hy : y ∈ TgtFam p 1 ι σ ϖ (topPart TT lam0) t c₃ L'' L) (hρ : ρ ∈ edgeDual p 1 ι σ ϖ (offPart TT lam0) L'' L) :
    y * ρ ∈ TgtFam p 1 ι σ ϖ lam0 (t + 2 * n' * c) (c₃ - 2 * n' * c) L'' L := by
  have hϖ := varpiK_ne_zero hU
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hyA, hyB⟩ := Submodule.mem_inf.1 hy1
  have hρ0 := smul_mem_bdual_of_edgeDual_off hU hlam hc he hρ
  have hother : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → L₁ ≠ L'' → ∃ H ∈ edgeDual p 1 ι σ ϖ lam0 L₁ L,
      y * ρ = algebraMap O Kf ϖ ^ (c₃ - 2 * n' * c) • H := by
    intro L₁ he₁ hne
    obtain ⟨y₁, hy₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hy2 L₁ he₁) hne)
    refine ⟨y₁ * (algebraMap O Kf ϖ ^ (2 * n' * c) • ρ),
      mul_mem_edgeDual hU hlam hy₁ (bdual_nab_le_edgeDual hU (antitone_offPart hlam) he₁ hρ0), ?_⟩
    rw [mul_smul_comm, smul_smul, smul_mul_assoc, ← pow_add, Nat.sub_add_cancel hc₃]
  refine ⟨Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun L₁ => (Submodule.mem_iInf _).2 fun he₁ => ?_⟩,
    Set.mem_iInter₂.2 fun L₁ he₁ => Set.mem_iInter.2 fun hne => ?_⟩
  · rw [mem_bdual_smul_iff _ _ _ (pow_ne_zero _ hϖ)] at hyA ⊢
    have := mul_mem_bdual (split_wt1 TT lam0) (antitone_blockWt fun _ => antitone_topPart hlam)
      (antitone_blockWt fun _ => antitone_offPart hlam) hyA hρ0
    rwa [smul_mul_smul_comm, ← pow_add] at this
  · by_cases hL : L₁ = L''
    · subst hL
      exact mul_mem_edgeDual hU hlam ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hyB L₁) he₁) hρ
    · obtain ⟨H, hH, e⟩ := hother L₁ he₁ hL
      rw [e, ← map_pow, algebraMap_smul]
      exact Submodule.smul_mem _ _ hH
  · obtain ⟨H, hH, e⟩ := hother L₁ he₁ hne
    exact Set.mem_smul_set.2 ⟨H, hH, e.symm⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **Sources lie in `∇_{Kf}`.** -/
theorem mem_nabla_of_srcFam {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) : F ∈ nabla Kf (nu1 lam0) := by
  obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 hF.1.1
  exact Submodule.smul_mem _ _ hF₀.1

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Targets lie in `∇_{Kf}`.** -/
theorem mem_nabla_of_tgtFam {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} {y : Pol (Unit × Fin n') k Kf}
    (hy : y ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) : y ∈ nabla Kf (nu1 lam0) :=
  (Submodule.mem_inf.1 hy.1).1.1

/-- **The off-top step at one edge** (N18): a good system `(x_i, y_m, z, M)` of size `n` for the top part at
`(t, c₃, D)` gives one of size `n·|ZIdx|` for `λ` at `(t + 2n′c, c₃ − 2n′c, D)`: the `x_i·r_α` and `y_m·ρ_β` for
`pairE`-dual bases `r_α`, `ρ_β` of `𝓡_off(e)`, `𝓡′_off(e)` (`edgeLat_dualPair`), with the same `z` and the matrix
`M ⊗ 1` (`pairE_split`). The size is at least `n·d(λ^off)`, as the `r_α` span `∇_{Kf}(λ^off)`. -/
theorem goodSys_offTop (hU : Unram p n' W Qq O Kf ι σ j ϖ) {c t c₃ D n : ℕ} (hlam : ∀ s, Antitone (lam0 s))
    (hc : ∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c) (hc₃ : 2 * n' * c ≤ c₃) {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) (hg : GoodSys p 1 ι σ ϖ (topPart TT lam0) t c₃ D L'' L n) :
    ∃ N : ℕ, n * dimV Kf (offPart TT lam0) ≤ N ∧
      GoodSys p 1 ι σ ϖ lam0 (t + 2 * n' * c) (c₃ - 2 * n' * c) D L'' L N := by
  classical
  obtain ⟨x, y, z, M, hz, hzD, hx, hy, hG⟩ := hg
  obtain ⟨r, ρ, hr, hρ, hrρ, hsr, hsρ⟩ := edgeLat_dualPair hU (antitone_offPart (TT := TT) hlam) he
  have hrm : ∀ α, r α ∈ edgeLat ι σ ϖ 1 (offPart TT lam0) L'' L := fun α => by
    rw [hr]
    exact Submodule.subset_span ⟨α, rfl⟩
  have hρm : ∀ α, ρ α ∈ edgeDual p 1 ι σ ϖ (offPart TT lam0) L'' L := fun α => by
    rw [hρ]
    exact Submodule.subset_span ⟨α, rfl⟩
  have hrn : ∀ α, r α ∈ nabla Kf (nu1 (offPart TT lam0)) := fun α => hsr ▸ Submodule.subset_span ⟨α, rfl⟩
  have hρn : ∀ α, ρ α ∈ nabla Kf (nu1 (offPart TT lam0)) := fun α => hsρ ▸ Submodule.subset_span ⟨α, rfl⟩
  set e := Fintype.equivFin (Fin n × ZIdx (wt1 (offPart TT lam0)))
  refine ⟨Fintype.card (Fin n × ZIdx (wt1 (offPart TT lam0))), ?_, fun a => x (e.symm a).1 * r (e.symm a).2,
    fun a => y (e.symm a).1 * ρ (e.symm a).2, z,
    fun a b => if (e.symm a).2 = (e.symm b).2 then M (e.symm a).1 (e.symm b).1 else 0, hz, hzD,
    fun a => mul_mem_srcFam hU hlam hc hc₃ he (hx _) (hrm _),
    fun a => mul_mem_tgtFam hU hlam hc hc₃ he (hy _) (hρm _), fun a b => ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin]
    refine Nat.mul_le_mul_left _ ?_
    have := finrank_range_le_card (R := Kf) r
    rwa [Set.finrank, hsr] at this
  · obtain ⟨⟨i, α⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨l, γ⟩, rfl⟩ := e.surjective b
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    have hsplit : ∀ m β, pairE p 1 lam0 (x i * r α) (y m * ρ β) =
        pairE p 1 (topPart TT lam0) (x i) (y m) * if α = β then 1 else 0 := fun m β => by
      rw [pairE_split hU hlam 1 (mem_nabla_of_srcFam (hx i)) (mem_nabla_of_tgtFam (hy m)) (hrn α) (hρn β), hrρ]
    have hinner : ∀ m, ∑ β, pairE p 1 lam0 (x i * r α) (y m * ρ β) *
        algebraMap O Kf (if β = γ then M m l else 0) =
        if α = γ then pairE p 1 (topPart TT lam0) (x i) (y m) * algebraMap O Kf (M m l) else 0 := fun m => by
      simp only [hsplit]
      rw [Finset.sum_eq_single α (fun β _ hβ => by simp [Ne.symm hβ]) (by simp)]
      by_cases h : α = γ <;> simp [h]
    simp only [hinner]
    by_cases hαγ : α = γ
    · simp [hαγ, hG i l, e.injective.eq_iff]
    · simp [hαγ, e.injective.eq_iff]

variable (k) in
/-- **The off-top step** (A-N18, `FirstAssembly.OffTop`): at a setting `Unram`, for a dominant weight with all
entries off the tops in `[−c, c]` and `2n′c ≤ c₃`, a per-edge rank `(1 − κ)·d(λ^top)/g` of the top part at depth
`t`, conductor `c₃` gives the per-edge rank `(1 − κ)·d(λ)/g` at depth `t + 2n′c`, conductor `c₃ − 2n′c`, same
denominator: edge by edge `goodSys_offTop`, of size `n·d(λ^off)`, and `d(λ) ≤ d(λ^top)·d(λ^off)`
(`finrank_nabla_le`). -/
theorem offTop (hU : Unram p n' W Qq O Kf ι σ j ϖ) (TT : Finset (Fin n')) (c : ℕ) :
    FirstAssembly.OffTop W k p ι σ ϖ TT c := by
  intro lam0 t c₃ D κ hlam hc hc₃ hR L'' L he
  obtain ⟨n, hn, hg⟩ := hR L'' L he
  obtain ⟨N, hN, hg'⟩ := goodSys_offTop hU hlam hc hc₃ he hg
  refine ⟨N, ?_, hg'⟩
  have hdim : (dimV Kf lam0 : ℝ) ≤ dimV Kf (topPart TT lam0) * dimV Kf (offPart TT lam0) := by
    exact_mod_cast finrank_nabla_le (split_wt1 TT lam0) (antitone_blockWt fun _ => hlam)
      (antitone_blockWt fun _ => antitone_topPart hlam) (antitone_blockWt fun _ => antitone_offPart hlam)
  have hg0 : (0 : ℝ) ≤ gE p n' k := Nat.cast_nonneg _
  have hN' : (n : ℝ) * dimV Kf (offPart TT lam0) ≤ N := by exact_mod_cast hN
  by_cases hκ : 1 - κ ≤ 0
  · calc (1 - κ) * dimV Kf lam0 / gE p n' k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hκ (Nat.cast_nonneg _)) hg0
      _ ≤ N := Nat.cast_nonneg _
  · push Not at hκ
    calc (1 - κ) * dimV Kf lam0 / gE p n' k
        ≤ (1 - κ) * (dimV Kf (topPart TT lam0) * dimV Kf (offPart TT lam0)) / gE p n' k :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdim hκ.le) hg0
      _ = (1 - κ) * dimV Kf (topPart TT lam0) / gE p n' k * dimV Kf (offPart TT lam0) := by ring
      _ ≤ n * dimV Kf (offPart TT lam0) := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _)
      _ ≤ N := hN'

end Prod

/-! ## The first local theorem without the off-top hypothesis -/

/-- **The first local theorem (L5)** with the off-top step discharged (`offTop`): `FirstAssembly.first_local` from
the inputs `FlatDim`, `HarmSplit`, `InputRank`, `SegMean`, `κ_P ≤ C_P·N·N₁/Y` and `CloudStep` alone. -/
theorem first_local' (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
    (hCP : 0 ≤ CP) :
    ∃ CH C : ℝ, 0 < C ∧ ∀ (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ) (c D cStar : ℕ),
      Even n' → 5 ≤ p → FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar →
      ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
        [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
        (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (ϖ : O), Unram p n' W Qq O Kf ι σ j ϖ →
      FlatDim Kf TT k → HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a) →
      ∀ (κP : ℝ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ),
        InputRank W k p ι σ ϖ TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b'))
          (t0F Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D0 CI TT.card Y N₁ k (lamA p k a)) κP κT →
        SegMean TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b')) κT CA N₁ Y →
        κP ≤ CP * TT.card * N₁ / Y →
        CloudStep W k p ι σ ϖ TT c (Dcl TT.card k (lamA p k a)) b' a →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨CH, C, hC, h⟩ := first_local C₀ hC₀ Ct CI CA CP hCt hCI hCA hCP
  refine ⟨CH, C, hC, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hFD hHS κP κT
    hI1 hseg hκP hcl
  exact h p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf ι σ j ϖ hU hFD hHS κP κT hI1 hseg hκP hcl
    (offTop k hU TT c)

end

end OffTop
