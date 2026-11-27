import FirstCloudEdge

/-!
# The cloud pairing and the cloud maps at one edge (L5, A-N16, A-N17)

The inputs of the cloud step (module 11, `FirstCloud`, of the L5/L6 plan) and its per-edge statement, at one orbit of
an inert prime `p` in the setting `Unram`, for a weight `λ` of the cloud shape with flat weights `H = fl(A, B)`,
`H⁺ = fl(A + 2c, B + 2c)`, `fl₂ = fl(2c, 2c)`, cloud weight `μ` and dual cloud weight `μ*` (`FirstCloudEdge`).

**The inputs** (classical facts, stated as `Prop`s; exact statements in the definitions).
* `CloudPair` (Annex I's I5 with the contraction of N16): a `Kf`-bilinear contraction `Con : V(λ) × V(μ*) → V(H⁺)`,
  equivariant (on `V(λ) × V(μ*)` it commutes with the twists by invertible block matrices) and integral on
  `∇_O × ∇_O`, and top cloud
  vectors `ŝ_b ∈ ∇_O(μ)`, `ŝ′_a ∈ ∇_O(μ*)` (row weights maximal in row `0`), `b ∈ Z`, with
  `Con(F·ŝ_b, ŝ′_a) = δ_{ab}·p^{κ_a}·F·hw(fl₂)` on `V(H)`, `κ_a ≤ E`, and `|Z|` the Weyl dimension of the middle
  entries (`∏ midFac`). Classically `Con` pairs the middle entries by the `GL_{k−2}`-invariant pairing (the
  restriction of `V(λ)` and `V(μ*)` to a Levi of type `(1, k − 2, 1)`), and the `ŝ_b`, `ŝ′_a` are Smith-dual bases of
  the middle `GL_{k−2}`-modules (L3's sandwich, spec S3).
* `HwSat` (the domain half of Annex I's I6): multiplication by a highest weight vector is saturated,
  `F·hw(ν₂) ∈ ∇_O(ν + ν₂) ⇒ F ∈ ∇_O(ν)` (standard monomial theory: `∇_O(ν) = ∇_{Kf}(ν) ∩ O[x]`, and Gauss's lemma).

**Main results.**
* *Joint integrality* (`con_mem_nablaB`): `Con(∇_Λ(λ), ∇_Λ(μ*)) ⊆ ∇_Λ(H⁺)` for every family of block lattices.
* *The cloud targets* (`exists_adj_tgt`): for `s′` with `p^{A₁(μ*)}s′ ∈ ∇(L)`, `s′ ∈ 𝓡(e)` and
  `ϖ^{ℓ + A₁(μ*)}s′ ∈ ∇(mid e′)` on the other edges `e′` into `L`, every target `γ` at `H⁺` (conductor `c ≥ ℓ`) has a
  target `G` at `λ` (conductor `c − ℓ`) with `pairE_λ(v, G) = pairE_{H⁺}(Con(v, s′), γ)` on `V(λ)` (the
  `pairE`-adjoint through a dual pair of `𝓡_λ(e)`, model fact 2).
* *The cloud identity* (`con_topVec_delta`, `L_a∘U_b = δ_{ab}p^{κ_a}·io`): in the coordinates of an edge the
  normalised top vectors (`topVec`) satisfy `Con(F·s̃_b, s̃′_a) = δ_{ab}p^{κ_a}·F·h̃` on `V(H)` (equivariance).
* *Saturation of `io = ·h̃`* (`topVec_sat`): `F·h̃ ∈ 𝓡_{H⁺}(e) ⇒ F ∈ 𝓡_H(e)` (`HwSat` in midpoint coordinates).
* *The cloud step at one edge* (`goodSys_cloud`, N16–N17): good systems of sizes `n₁` at `H` and `n₂` at `H⁺`
  (conductor `c₂`, denominator `D₁`, `4D₁ < c₂`, `2Nc ≤ c₂`) give `r ≤ n₁` with `#edges·(n₁ − r + n₂) ≤ d(H⁺)` and a
  good system of size `|Z|·r` at `λ` (conductor `c₂ − 2Nc`, denominator `2D₁ + E`). The sources are `F_i·s̃_b`, `F_i`
  the combinations of `x¹` given by `cloud_count` (through `io`, with the retraction targets of
  `exists_retract_targets`); the targets come from primitive tests (`goodSys_of_primitive`), as the adjoints of the
  contractions with `s̃′_b` (`exists_adj_tgt`, loss `ℓ = 2Nc`: `ϖ^{Nc}∇_{μ*}(L) ⊆ ∇_{μ*}(mid e′)`).
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly

open scoped Matrix Pointwise

noncomputable section

/-! ## The inputs -/

section Hyp

variable (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] {n' : ℕ}

/-- **The cloud pairing** (Annex I's I5 with the contraction of N16, an input): for a weight `λ` of the cloud shape
(`A, B ≥ 0`, top extremes `(A_s + c, B_s + c)`, `0` off the tops), with `μ = cloudWt`, `μ* = cloudDual`,
`H = fl(A, B)`, `H⁺ = fl(A + 2c, B + 2c)`, `fl₂ = fl(2c, 2c)`, there are a finite index set `Z`, a `Kf`-bilinear
`Con : V(λ) × V(μ*) → V(H⁺)` commuting on `V(λ) × V(μ*)` with the twists by invertible block matrices (the
`GL_k`-action) and mapping `∇_O × ∇_O` into
`∇_O`, vectors `s_b ∈ ∇_O(μ)`, `s′_a ∈ ∇_O(μ*)` whose row weights have the maximal entry `natW(·)_{b,0}` in row `0` of
every block, and exponents `κ_a ≤ E`, with `Con(F·s_b, s′_a) = δ_{ab}·p^{κ_a}·(F·hw(fl₂))` for `F ∈ V(H)` and
`|Z| = ∏_{s ∈ TT} ∏_{i<j} midFac(λ_s)_{ij}` (the Weyl dimension of the middle entries). Annex I takes
`E = N·⌈(k − 1)²(log_p(8a + k) + 1)⌉`. -/
def CloudPair (p : ℕ) (TT : Finset (Fin n')) (k c E : ℕ) : Prop :=
  ∀ (lam0 : Fin n' → Fin k → ℤ) (A B : TT → ℤ), (∀ s, 0 ≤ A s) → (∀ s, 0 ≤ B s) →
    IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0 → (∀ s ∉ TT, lam0 s = 0) →
    ∃ (Z : Type) (_ : Fintype Z) (_ : DecidableEq Z)
      (Con : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf)
      (s s' : Z → Pol (Unit × Fin n') k Kf) (κ : Z → ℕ) (ρ ρ' : Z → Unit × Fin n' → Fin k → ℕ),
      ((Fintype.card Z : ℚ) = ∏ x ∈ TT, ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, midFac (lam0 x) i j) ∧
      (∀ a, κ a ≤ E) ∧
      (∀ a, s a ∈ nablaInt (Oint O Kf) (nu1 (cloudWt TT c lam0)) ∧
        IsWeightedHomogeneous (rowW (Unit × Fin n') k) (s a) (ρ a) ∧
        ∀ b (i : Fin k), i.val = 0 → ρ a b i = nu1 (cloudWt TT c lam0) b i) ∧
      (∀ a, s' a ∈ nablaInt (Oint O Kf) (nu1 (cloudDual TT c lam0)) ∧
        IsWeightedHomogeneous (rowW (Unit × Fin n') k) (s' a) (ρ' a) ∧
        ∀ b (i : Fin k), i.val = 0 → ρ' a b i = nu1 (cloudDual TT c lam0) b i) ∧
      (∀ F G, F ∈ nabla Kf (nu1 lam0) → G ∈ nabla Kf (nu1 (cloudDual TT c lam0)) →
        Con F G ∈ nabla Kf (nu1 (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))))) ∧
      (∀ g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf, (∀ b, IsUnit (g b).det) → ∀ F G,
        F ∈ nabla Kf (nu1 lam0) → G ∈ nabla Kf (nu1 (cloudDual TT c lam0)) →
        Con (twist (wt1 lam0) g F) (twist (wt1 (cloudDual TT c lam0)) g G) =
          twist (wt1 (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ)))) g (Con F G)) ∧
      (∀ F G, F ∈ nablaInt (Oint O Kf) (nu1 lam0) → G ∈ nablaInt (Oint O Kf) (nu1 (cloudDual TT c lam0)) →
        Con F G ∈ nablaInt (Oint O Kf) (nu1 (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))))) ∧
      ∀ F ∈ nabla Kf (nu1 (flatWt (k := k) TT A B)), ∀ a b, Con (F * s b) (s' a) =
        if a = b then (p : Kf) ^ κ a •
          (F * hw Kf (nu1 (flatWt (k := k) TT (fun _ => 2 * (c : ℤ)) fun _ => 2 * (c : ℤ)))) else 0

/-- **Highest weight vectors are saturated** (the domain half of Annex I's I6, an input): for antitone shapes `ν`, `ν₂`
and `F ∈ ∇_{Kf}(ν)`, `F·hw(ν₂) ∈ ∇_O(ν + ν₂)` implies `F ∈ ∇_O(ν)`. (Classically: `∇_O(ν) = ∇_{Kf}(ν) ∩ O[x]` by
standard monomial theory, and `hw(ν₂)` is primitive, so Gauss's lemma applies.) -/
def HwSat (n' k : ℕ) : Prop :=
  ∀ ν ν₂ : Unit × Fin n' → Fin k → ℕ, (∀ b, Antitone (ν b)) → (∀ b, Antitone (ν₂ b)) →
    ∀ F ∈ nabla Kf ν, F * hw Kf ν₂ ∈ nablaInt (Oint O Kf) (ν + ν₂) → F ∈ nablaInt (Oint O Kf) ν

end Hyp

/-! ## Joint integrality of an equivariant contraction -/

section Joint

variable {β : Type} [Fintype β] [DecidableEq β] {k : ℕ} {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]

/-- **Joint integrality**: a bilinear map that commutes on `∇ × ∇` with the twists by invertible block matrices and maps
`∇_O × ∇_O` into `∇_O` maps `∇_Λ(λ) × ∇_Λ(μ)` into `∇_Λ(ν)` for every family of block lattices `Λ` (twist both factors
by the same basis matrices). -/
theorem con_mem_nablaB {lam mu nu : β → Fin k → ℤ} (Con : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Pol β k Kf)
    (hV : ∀ F G, F ∈ nabla Kf (fun b => natW (lam b)) → G ∈ nabla Kf (fun b => natW (mu b)) →
      Con F G ∈ nabla Kf (fun b => natW (nu b)))
    (heq : ∀ g : β → Matrix (Fin k) (Fin k) Kf, (∀ b, IsUnit (g b).det) → ∀ F G,
      F ∈ nabla Kf (fun b => natW (lam b)) → G ∈ nabla Kf (fun b => natW (mu b)) →
      Con (twist lam g F) (twist mu g G) = twist nu g (Con F G))
    (hint : ∀ F G, F ∈ nablaInt (Oint O Kf) (fun b => natW (lam b)) →
      G ∈ nablaInt (Oint O Kf) (fun b => natW (mu b)) → Con F G ∈ nablaInt (Oint O Kf) (fun b => natW (nu b)))
    {Λ : β → Submodule O (Fin k → Kf)} {F G : Pol β k Kf} (hF : F ∈ nablaB lam Λ) (hG : G ∈ nablaB mu Λ) :
    Con F G ∈ nablaB nu Λ := by
  obtain ⟨hF1, C, hC, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := (mem_nablaB_iff hC).1 hG
  refine ⟨hV F G hF1 hG1, C, hC, ?_⟩
  rw [← heq C (fun b => (hC b).1) F G hF1 hG1]
  exact hint _ _ hF2 hG2

end Joint


/-! ## The cloud targets -/

section Targets

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [CharZero Kf] in
/-- **Scalars through a bilinear map**: `Con(a·F, b·G) = (a·b)·Con(F, G)`. -/
theorem con_smul_smul {β : Type} [Fintype β] (Con : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Pol β k Kf) (a b : Kf)
    (F G : Pol β k Kf) : Con (a • F) (b • G) = (a * b) • Con F G := by
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

/-- **The cloud targets** (the target side of N16): let `Con` be jointly integral from `(λ, μ)` to `λ⁺` for every
family of block lattices, `A₁(λ⁺) = A₁(λ) + A₁(μ)`, and let `s′` satisfy `p^{A₁(μ)}s′ ∈ ∇_μ(L)`, `s′ ∈ 𝓡_μ(e)` and
`ϖ^{ℓ + A₁(μ)}s′ ∈ ∇_μ(mid e′)` on the other edges `e′` into `L`. Then every target `γ` at `λ⁺` (depth `t`, conductor
`c ≥ ℓ`) has a target `G` at `λ` (depth `t`, conductor `c − ℓ`) with `pairE_λ(v, G) = pairE_{λ⁺}(Con(v, s′), γ)` on
`V(λ)`: `G = Σ_i pairE_{λ⁺}(Con(x_i, s′), γ)·y_i` for a `pairE`-dual pair `x, y` of `𝓡_λ(e)` (model fact 2). -/
theorem exists_adj_tgt (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam mu lamP : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam s)) (hA : topA 1 lamP = topA 1 lam + topA 1 mu)
    (Con : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf)
    (hconB : ∀ (Λ : Unit × Fin n' → Submodule O (Fin k → Kf)) F G, F ∈ nablaB (wt1 lam) Λ →
      G ∈ nablaB (wt1 mu) Λ → Con F G ∈ nablaB (wt1 lamP) Λ)
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) (s' : Pol (Unit × Fin n') k Kf)
    (hs'L : (p : Kf) ^ topA 1 mu • s' ∈ nab O ι σ mu L) (hs'e : s' ∈ edgeLat ι σ ϖ 1 mu L'' L) {ℓ : ℕ}
    (hs'o : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → L₁ ≠ L'' →
      algebraMap O Kf ϖ ^ ((ℓ : ℤ) + topA 1 mu) • s' ∈ nabMid ι σ ϖ mu L₁ L)
    {t c : ℕ} (hℓ : ℓ ≤ c) {γ : Pol (Unit × Fin n') k Kf} (hγ : γ ∈ TgtFam p 1 ι σ ϖ lamP t c L'' L) :
    ∃ G ∈ TgtFam p 1 ι σ ϖ lam t (c - ℓ) L'' L,
      ∀ v ∈ nabla Kf (nu1 lam), pairE p 1 lam v G = pairE p 1 lamP (Con v s') γ := by
  classical
  have := hU.frac_O
  have hϖ := varpiK_ne_zero hU
  have hp : (p : Kf) ≠ 0 := hU.castK_ne_zero
  obtain ⟨x, y, -, -, hxy, hsx, hsy⟩ := edgeLat_dualPair hU hlam he
  set G := ∑ i, pairE p 1 lamP (Con (x i) s') γ • y i with hGdef
  have hGV : G ∈ nabla Kf (nu1 lam) := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (by rw [← hsy]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hpair : ∀ v ∈ nabla Kf (nu1 lam), pairE p 1 lam v G = pairE p 1 lamP (Con v s') γ := by
    intro v hv
    have hv' : v ∈ Submodule.span Kf (Set.range x) := by rw [hsx]; exact hv
    refine LinearMap.eqOn_span' (f := (pairE p 1 lam).flip G) (g := ((pairE p 1 lamP).flip γ) ∘ₗ Con.flip s') ?_ hv'
    rintro _ ⟨l, rfl⟩
    show pairE p 1 lam (x l) G = pairE p 1 lamP (Con (x l) s') γ
    rw [hGdef, map_sum]
    simp only [map_smul, hxy, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  -- the contraction on the lattices of the edges
  have hCe : ∀ F ∈ edgeLat ι σ ϖ 1 lam L'' L, Con F s' ∈ edgeLat ι σ ϖ 1 lamP L'' L := by
    intro F hF
    show _ ∈ nablaB (wt1 lamP) fun b => midBlk ι σ ϖ b.2 L'' L
    rw [show algebraMap O Kf ϖ ^ topA 1 lamP • Con F s' =
      Con (algebraMap O Kf ϖ ^ topA 1 lam • F) (algebraMap O Kf ϖ ^ topA 1 mu • s') by
        rw [con_smul_smul, ← zpow_add₀ hϖ, hA]]
    exact hconB _ _ _ hF hs'e
  have hCo : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → L₁ ≠ L'' → ∀ F ∈ edgeLat ι σ ϖ 1 lam L₁ L,
      algebraMap O Kf ϖ ^ ℓ • Con F s' ∈ edgeLat ι σ ϖ 1 lamP L₁ L := by
    intro L₁ he₁ h₁ F hF
    show _ ∈ nablaB (wt1 lamP) fun b => midBlk ι σ ϖ b.2 L₁ L
    rw [show algebraMap O Kf ϖ ^ topA 1 lamP • algebraMap O Kf ϖ ^ ℓ • Con F s' =
      Con (algebraMap O Kf ϖ ^ topA 1 lam • F) (algebraMap O Kf ϖ ^ ((ℓ : ℤ) + topA 1 mu) • s') by
        rw [con_smul_smul, smul_smul, ← zpow_natCast, ← zpow_add₀ hϖ, ← zpow_add₀ hϖ, hA]
        ring_nf]
    exact hconB _ _ _ hF (hs'o L₁ he₁ h₁)
  -- the pairings on the other edges into `L` are `ϖ^{c−ℓ}`-small
  have hsmall : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → L₁ ≠ L'' → ∀ F ∈ edgeLat ι σ ϖ 1 lam L₁ L,
      ∃ o : O, pairE p 1 lam F G = algebraMap O Kf ϖ ^ (c - ℓ) * algebraMap O Kf o := by
    intro L₁ he₁ h₁ F hF
    obtain ⟨γ₁, hγ₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hγ.2 L₁ he₁) h₁)
    obtain ⟨o, ho⟩ := hγ₁.2 _ (hCo L₁ he₁ h₁ F hF)
    refine ⟨o, ?_⟩
    rw [hpair F (mem_nabla_of_edgeLat hU hF), map_smul, smul_eq_mul, ho, map_smul, LinearMap.smul_apply,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hℓ]
  refine ⟨G, ⟨⟨⟨hGV, fun F hF => ?_⟩, ?_⟩, ?_⟩, hpair⟩
  · -- the depth
    obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 hF
    have hF₀V : F₀ ∈ nabla Kf (nu1 lam) := hF₀.1
    have hFV : algebraMap O Kf ϖ ^ t • F₀ ∈ nabla Kf (nu1 lam) := Submodule.smul_mem _ _ hF₀V
    have e : nf (wt1 lam) (algebraMap O Kf ϖ ^ t • F₀) G =
        nf (wt1 lamP) (algebraMap O Kf ϖ ^ t • Con F₀ ((p : Kf) ^ topA 1 mu • s')) γ := by
      have h1 := hpair _ hFV
      simp only [pairE, LinearMap.smul_apply, map_smul, smul_eq_mul] at h1 ⊢
      rw [hA, zpow_add₀ hp] at h1
      apply mul_left_cancel₀ (zpow_ne_zero (topA 1 lam) hp)
      linear_combination h1
    rw [e]
    exact (Submodule.mem_inf.1 hγ.1).1.2 _ (Set.smul_mem_smul_set (hconB _ _ _ hF₀ hs'L))
  · -- the edges into `L`
    refine (Submodule.mem_iInf _).2 fun L₁ => (Submodule.mem_iInf _).2 fun he₁ => ⟨hGV, fun F hF => ?_⟩
    by_cases h₁ : L₁ = L''
    · subst h₁
      rw [hpair F (mem_nabla_of_edgeLat hU hF)]
      exact (tgtFam_subset_edgeDual he hγ).2 _ (hCe F hF)
    · obtain ⟨o, ho⟩ := hsmall L₁ he₁ h₁ F hF
      rw [ho]
      exact (Oint O Kf).mul_mem (pow_mem (show algebraMap O Kf ϖ ∈ Oint O Kf from ⟨ϖ, rfl⟩) _) ⟨o, rfl⟩
  · -- the smallness on the other edges into `L`
    refine Set.mem_iInter₂.2 fun L₁ he₁ => Set.mem_iInter.2 fun h₁ => ?_
    have hc0 : algebraMap O Kf ϖ ^ (c - ℓ) ≠ 0 := pow_ne_zero _ hϖ
    refine ⟨(algebraMap O Kf ϖ ^ (c - ℓ))⁻¹ • G, ⟨Submodule.smul_mem _ _ hGV, fun F hF => ?_⟩, ?_⟩
    · obtain ⟨o, ho⟩ := hsmall L₁ he₁ h₁ F hF
      rw [map_smul, smul_eq_mul, ho, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      exact ⟨o, rfl⟩
    · simp only [smul_smul, mul_inv_cancel₀ hc0, one_smul]

end Targets


/-! ## The cloud identity and the saturation of `io` at an edge -/

section Delta

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **The cloud identity at an edge** (`L_a∘U_b = δ_{ab}p^{κ_a}·io`): if `λ = H + μ` and `λ⁺ = H + fl₂` (determinant
shifts), `A₁(fl₂) = A₁(μ) + A₁(μ*)` and the equivariant `Con` has `Con(F·s_b, s′_a) = δ_{ab}p^{κ_a}F·h` on `V(H)` in
standard coordinates, then in the coordinates `C` of an edge
`Con(F·s̃_b, s̃′_a) = δ_{ab}p^{κ_a}·F·h̃` on `V(H)`, for the normalised top vectors (`topVec`). -/
theorem con_topVec_delta {lam H mu muS lamP f2 : Fin n' → Fin k → ℤ}
    (hl : ∀ b, detShift (wt1 lam b) = detShift (wt1 H b) + detShift (wt1 mu b))
    (hl2 : ∀ b, detShift (wt1 lamP b) = detShift (wt1 H b) + detShift (wt1 f2 b))
    (hA2 : topA 1 f2 = topA 1 mu + topA 1 muS) {C : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf}
    (hC : ∀ b, IsUnit (C b).det)
    (Con : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf)
    (heq : ∀ g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf, (∀ b, IsUnit (g b).det) → ∀ F G,
      F ∈ nabla Kf (nu1 lam) → G ∈ nabla Kf (nu1 muS) →
      Con (twist (wt1 lam) g F) (twist (wt1 muS) g G) = twist (wt1 lamP) g (Con F G))
    (hnu : nu1 lam = nu1 H + nu1 mu)
    {Z : Type} [DecidableEq Z] (s s' : Z → Pol (Unit × Fin n') k Kf) (hsV : ∀ b, s b ∈ nabla Kf (nu1 mu))
    (hs'V : ∀ a, s' a ∈ nabla Kf (nu1 muS)) (κ : Z → ℕ) (h : Pol (Unit × Fin n') k Kf)
    (hδ : ∀ F ∈ nabla Kf (nu1 H), ∀ a b, Con (F * s b) (s' a) = if a = b then (p : Kf) ^ κ a • (F * h) else 0)
    (hp : (p : Kf) ≠ 0) {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ nabla Kf (nu1 H)) (a b : Z) :
    Con (F * topVec p C mu (s b)) (topVec p C muS (s' a)) =
      if a = b then (p : Kf) ^ κ a • (F * topVec p C f2 h) else 0 := by
  set g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf := fun b => (C b)⁻¹
  have hg : ∀ b, IsUnit (g b).det := fun b => Matrix.isUnit_nonsing_inv_det _ (hC b)
  set F' := twist (wt1 H) C F
  have hFF : twist (wt1 H) g F' = F := by
    rw [twist_twist, show (fun b => C b * g b) = fun _ => 1 from
      funext fun b => Matrix.mul_nonsing_inv _ (hC b), twist_one]
  have hF'V : F' ∈ nabla Kf (nu1 H) := twist_mem_nabla _ _ hF
  have e1 : F * topVec p C mu (s b) = (p : Kf) ^ (-topA 1 mu) • twist (wt1 lam) g (F' * s b) := by
    rw [topVec, mul_smul_comm, twist_mul' hl (fun b => (hg b).ne_zero), hFF]
  rw [e1, topVec, con_smul_smul, heq g hg _ _ (OffTop.mul_mem_nabla hnu hF'V (hsV b)) (hs'V a), hδ F' hF'V]
  split_ifs
  · rw [twist_smul, twist_mul' hl2 (fun b => (hg b).ne_zero), hFF, topVec, mul_smul_comm, smul_smul, smul_smul]
    congr 1
    rw [hA2, neg_add, zpow_add₀ hp]
    ring
  · rw [twist_zero, smul_zero]

omit [CharZero Kf] in
/-- **`io` is saturated at the edge** (N16's `io(F) ∈ 𝓡_{H⁺}(e) ⟺ F ∈ 𝓡_H(e)`, one direction): for `λ⁺ = H + fl₂` and
`F ∈ V(H)`, if `F·h̃ ∈ 𝓡_{λ⁺}(e)`, `h̃` the normalised highest weight vector of `fl₂`, then `F ∈ 𝓡_H(e)`. In the
midpoint coordinates the twist of `ϖ^{A₁(λ⁺)}F·h̃` is `twist(ϖ^{A₁(H)}F)·hw(fl₂)` (`twist_topVec`), and `HwSat`. -/
theorem topVec_sat (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 0 < k) {L'' L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det) (hL : L = Submodule.span W (Set.range fun l i => B i l))
    (hL'' : L'' = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then (p : Qq) else 1) i l))
    {H f2 : Fin n' → Fin k → ℤ} (hH : ∀ s, Antitone (H s)) (hf2 : ∀ s, Antitone (f2 s)) (hsat : HwSat O Kf n' k)
    {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ nabla Kf (nu1 H))
    (hFz : F * topVec p (edgeC ι σ B) f2 (hw Kf (nu1 f2)) ∈ edgeLat ι σ ϖ 1 (H + f2) L'' L) :
    F ∈ edgeLat ι σ ϖ 1 H L'' L := by
  obtain ⟨hC, hCm, -⟩ := edgeC_bases (n' := n') (O := O) hU hk hB hL hL''
  have hdet : ∀ b, IsUnit (edgeC (n' := n') ι σ B b).det := fun b => (hC b).1
  have hϖ := varpiK_ne_zero hU
  have hp : (p : Kf) ≠ 0 := hU.castK_ne_zero
  have hHb : ∀ b, Antitone (wt1 H b) := antitone_blockWt fun _ => hH
  have hf2b : ∀ b, Antitone (wt1 f2 b) := antitone_blockWt fun _ => hf2
  have hnu : nu1 (H + f2) = nu1 H + nu1 f2 := funext fun b => by
    simp only [nu1, wt1_add, Pi.add_apply]
    exact natW_add (hHb b) (hf2b b)
  set Cm : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf := fun b => edgeC ι σ B b * dg0 (algebraMap O Kf ϖ)
  have hCmdet : ∀ b, (Cm b).det ≠ 0 := fun b => (hCm b).1.ne_zero
  have hz : twist (wt1 f2) Cm (topVec p (edgeC ι σ B) f2 (hw Kf (nu1 f2))) =
      ((p : Kf) ^ (-topA 1 f2) * algebraMap O Kf ϖ ^ topA 1 f2) • hw Kf (nu1 f2) :=
    twist_topVec hk hdet hf2 (hw_isWH_row fun b => natW_antitone (hf2b b)) (fun _ _ _ => rfl) hϖ
  have hFz' := hFz
  change _ ∈ nablaB (wt1 (H + f2)) fun b => midBlk ι σ ϖ b.2 L'' L at hFz'
  rw [mem_nablaB_iff hCm] at hFz'
  have e : twist (wt1 (H + f2)) Cm (algebraMap O Kf ϖ ^ topA 1 (H + f2) •
      (F * topVec p (edgeC ι σ B) f2 (hw Kf (nu1 f2)))) =
      twist (wt1 H) Cm (algebraMap O Kf ϖ ^ topA 1 H • F) * hw Kf (nu1 f2) := by
    rw [twist_smul, twist_mul' (lam₁ := wt1 H) (lam₂ := wt1 f2)
      (fun b => by rw [wt1_add, Pi.add_apply, detShift_add]) hCmdet, hz, twist_smul, mul_smul_comm, smul_smul,
      smul_mul_assoc, topA_add, OffTop.castK_zpow hU]
    congr 1
    rw [← zpow_add₀ hϖ, ← zpow_add₀ hϖ]
    ring_nf
  rw [e] at hFz'
  have h2 : twist (wt1 H) Cm (algebraMap O Kf ϖ ^ topA 1 H • F) * hw Kf (nu1 f2) ∈
      nablaInt (Oint O Kf) (nu1 H + nu1 f2) := by
    rw [← hnu]
    exact hFz'.2
  have h1 := hsat (nu1 H) (nu1 f2) (fun b => natW_antitone (hHb b)) (fun b => natW_antitone (hf2b b)) _
    (twist_mem_nabla _ _ (Submodule.smul_mem _ _ hF)) h2
  show _ ∈ nablaB (wt1 H) fun b => midBlk ι σ ϖ b.2 L'' L
  rw [mem_nablaB_iff hCm]
  exact ⟨Submodule.smul_mem _ _ hF, h1⟩

end Delta


/-! ## The cloud step at one edge -/

section PerEdge

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **Sources shrink with the conductor**: `SrcFam(t, c) ⊆ SrcFam(t, c′)` for `c′ ≤ c`. -/
theorem srcFam_anti {lam0 : Fin n' → Fin k → ℤ} {t c c' : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ SrcFam p 1 ι σ ϖ lam0 t c L'' L) (hc : c' ≤ c) :
    F ∈ SrcFam p 1 ι σ ϖ lam0 t c' L'' L := by
  refine ⟨hF.1, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
  obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hF.2 L' he') hne)
  refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ (c - c') • F₁,
    smul_mem_edgeLat (pow_mem (show algebraMap O Kf ϖ ∈ Oint O Kf from ⟨ϖ, rfl⟩) _) hF₁, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hc]

omit [CharZero Kf] in
/-- **The determinant shifts of the dual cloud weight** add up to `−Nc`. -/
theorem sum_detShift_cloudDual (hk : 2 ≤ k) (TT : Finset (Fin n')) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) :
    ∑ b : Unit × Fin n', detShift (wt1 (cloudDual TT c lam0) b) = -(TT.card * c) := by
  have key : ∀ s : Fin n', detShift (lamAt (cloudDual TT c lam0) s) = if s ∈ TT then -(c : ℤ) else 0 := by
    intro s
    simp only [detShift, show 0 < k from by omega, ↓reduceDIte, lamAt]
    split_ifs <;> simp only [cloudDual, cloudWt, Fin.val_rev, neg_neg] <;> split_ifs <;> omega
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  simp only [wt1, blockWt, key, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_neg]

/-- **The cloud step at one edge** (N16–N17): given the cloud pairing and the saturation of highest weight vectors,
good systems of sizes `n₁` at `H = fl(A, B)` and `n₂` at `H⁺ = fl(A + 2c, B + 2c)` (depth `t`, conductor `c₂`,
denominator `D₁`, `4D₁ < c₂`, `2Nc ≤ c₂`) at an edge give, for some `r ≤ n₁` with
`#edges·(n₁ − r + n₂) ≤ d(H⁺)`, a good system of size `m·r` at `λ` (conductor `c₂ − 2Nc`, denominator `2D₁ + E`),
where `m = ∏ midFac` is the number of cloud vectors. Sources `F_i·s̃_b` (`F_i` the combinations of `cloud_count` of
the `x¹`, through `io = ·h̃`, with the retraction targets of `exists_retract_targets`), targets the adjoints of the
contractions with `s̃′_b` (`exists_adj_tgt`), by primitive tests (`goodSys_of_primitive`) and the cloud identity
(`con_topVec_delta`). -/
theorem goodSys_cloud (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {TT : Finset (Fin n')} {c E : ℕ}
    (hCP : CloudPair O Kf p TT k c E) (hsat : HwSat O Kf n' k) {lam0 : Fin n' → Fin k → ℤ} {A B : TT → ℤ}
    (hA0 : ∀ s, 0 ≤ A s) (hB0 : ∀ s, 0 ≤ B s)
    (hsh : IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0)
    (hz : ∀ s ∉ TT, lam0 s = 0) {t c₂ D₁ : ℕ} (h4 : 4 * D₁ < c₂) (h2 : 2 * TT.card * c ≤ c₂)
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) {n₁ n₂ : ℕ}
    (h₁ : GoodSys p 1 ι σ ϖ (flatWt TT A B) t c₂ D₁ L'' L n₁)
    (h₂ : GoodSys p 1 ι σ ϖ (flatWt TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) t c₂ D₁ L'' L n₂) :
    ∃ m : ℕ, (m : ℚ) = ∏ x ∈ TT, ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, midFac (lam0 x) i j ∧ ∃ r : ℕ, r ≤ n₁ ∧
      nEdges (n' := n') p 1 L * (n₁ - r + n₂) ≤
        dimV Kf (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) ∧
      GoodSys p 1 ι σ ϖ lam0 t (c₂ - 2 * TT.card * c) (2 * D₁ + E) L'' L (m * r) := by
  classical
  have hk0 : 0 < k := by omega
  have hp : (p : Kf) ≠ 0 := hU.castK_ne_zero
  have hϖ := varpiK_ne_zero hU
  obtain ⟨Z, _, _, Con, s, s', κ, ρ, ρ', hcard, hκ, hs, hs', hV, heq, hint, hδ⟩ := hCP lam0 A B hA0 hB0 hsh hz
  refine ⟨Fintype.card Z, hcard, ?_⟩
  set H := flatWt (k := k) TT A B with hHdef
  set Hp := flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ)) with hHpdef
  set f2 := flatWt (k := k) TT (fun _ => 2 * (c : ℤ)) fun _ => 2 * (c : ℤ) with hf2def
  set mu := cloudWt TT c lam0 with hmudef
  set muS := cloudDual TT c lam0 with hmuSdef
  have hlamH : lam0 = H + mu := lam_eq_flat_add_cloud hsh hz
  have hHpH : Hp = H + f2 := flatWt_add TT A B (2 * c)
  -- dominance and `A₁`
  have hlam : ∀ s, Antitone (lam0 s) := hsh.1
  have hH : ∀ s, Antitone (H s) := antitone_flatWt hk hA0 hB0
  have hc0 : (0 : ℤ) ≤ 2 * c := by positivity
  have hHp : ∀ s, Antitone (Hp s) := antitone_flatWt hk (fun s => add_nonneg (hA0 s) hc0)
    (fun s => add_nonneg (hB0 s) hc0)
  have hf2 : ∀ s, Antitone (f2 s) := antitone_flatWt hk (fun _ => hc0) (fun _ => hc0)
  have hmu : ∀ s, Antitone (mu s) := antitone_cloudWt hk hsh
  have hmuS : ∀ s, Antitone (muS s) := antitone_cloudDual hk hsh
  have hAmu : topA 1 mu = TT.card * c := topA_cloudWt hk TT c lam0
  have hAmuS : topA 1 muS = TT.card * c := topA_cloudDual hk TT c lam0
  have hAf2 : topA 1 f2 = 2 * (TT.card * c) := topA_flat2 hk TT c
  have hAl : topA 1 lam0 = topA 1 H + topA 1 mu := by
    conv_lhs => rw [hlamH]
    exact topA_add _ _
  have hAP : topA 1 Hp = topA 1 lam0 + topA 1 muS := by
    rw [hHpH, topA_add, hAl, hAf2, hAmu, hAmuS]
    ring
  have hl : ∀ b, detShift (wt1 lam0 b) = detShift (wt1 H b) + detShift (wt1 mu b) := fun b => by
    conv_lhs => rw [hlamH]
    rw [wt1_add, Pi.add_apply, detShift_add]
  have hl2 : ∀ b, detShift (wt1 Hp b) = detShift (wt1 H b) + detShift (wt1 f2 b) := fun b => by
    rw [hHpH, wt1_add, Pi.add_apply, detShift_add]
  -- the edge and the normalised top vectors
  obtain ⟨B₀, hB₀, hL, hL''⟩ := exists_basis_edge0 hU hk0 he
  obtain ⟨hC, -, -⟩ := edgeC_bases (n' := n') (O := O) hU hk0 hB₀ hL hL''
  set C := edgeC (n' := n') ι σ B₀ with hCdef
  have hdet : ∀ b, IsUnit (C b).det := fun b => (hC b).1
  have hsE := fun b => topVec_mem hU hk0 hB₀ hL hL'' hmu (hs b).1 (hs b).2.1 (hs b).2.2
  have hs'E := fun a => topVec_mem hU hk0 hB₀ hL hL'' hmuS (hs' a).1 (hs' a).2.1 (hs' a).2.2
  have hf2b : ∀ b, Antitone (nu1 f2 b) := fun b => natW_antitone (antitone_blockWt (fun _ => hf2) b)
  have hzE := topVec_mem hU hk0 hB₀ hL hL'' hf2
    (Submodule.subset_span ⟨fun _ s _ => Fin.castLE s.isLt, (WeylSandwich.hw_eq_bidet Kf (nu1 f2)).symm⟩)
    (hw_isWH_row hf2b) (fun _ _ _ => rfl)
  set zE := topVec p C f2 (hw Kf (nu1 f2)) with hzEdef
  let io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf := LinearMap.mulRight Kf zE
  have hio : ∀ F, io F = F * zE := fun F => rfl
  have hconB : ∀ (Λ : Unit × Fin n' → Submodule O (Fin k → Kf)) F G, F ∈ nablaB (wt1 lam0) Λ →
      G ∈ nablaB (wt1 muS) Λ → Con F G ∈ nablaB (wt1 Hp) Λ := fun Λ F G hF hG => con_mem_nablaB Con hV heq hint hF hG
  -- the system at `H` and its images at `H⁺`
  obtain ⟨x₁, y₁, z₁, M₁, hz₁0, hz₁, hx₁, hy₁, hG₁⟩ := h₁
  set Y₁ : Fin n₁ → Pol (Unit × Fin n') k Kf := fun l => ∑ m, M₁ m l • y₁ m with hY₁def
  have hY₁ : ∀ l, Y₁ l ∈ TgtFam p 1 ι σ ϖ H t c₂ L'' L := fun l => sum_smul_mem_tgtFam _ _ hy₁
  have hxY₁ : ∀ i l, pairE p 1 H (x₁ i) (Y₁ l) = if i = l then algebraMap O Kf z₁ else 0 := by
    intro i l
    rw [pairE_sum_smul, ← hG₁ i l]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hiox : ∀ i, io (x₁ i) ∈ SrcFam p 1 ι σ ϖ Hp t c₂ L'' L := by
    intro i
    rw [hio, hHpH]
    exact mul_mem_srcFam' hU hH hf2 (hx₁ i) hzE.2.1
  have hnuP : nu1 Hp = nu1 H + nu1 f2 := funext fun b => by
    rw [hHpH]
    simp only [nu1, wt1_add, Pi.add_apply]
    exact natW_add (antitone_blockWt (fun _ => hH) b) (antitone_blockWt (fun _ => hf2) b)
  have hioV : ∀ F ∈ nabla Kf (nu1 H), io F ∈ nabla Kf (nu1 Hp) := fun F hF => OffTop.mul_mem_nabla hnuP hF hzE.1
  have hnuL : nu1 lam0 = nu1 H + nu1 mu := funext fun b => by
    conv_lhs => rw [hlamH]
    simp only [nu1, wt1_add, Pi.add_apply]
    exact natW_add (antitone_blockWt (fun _ => hH) b) (antitone_blockWt (fun _ => hmu) b)
  have hsV : ∀ b, s b ∈ nabla Kf (nu1 mu) := fun b => WeylSandwich.nablaInt_subset_nabla _
    (fun x => natW_antitone (antitone_blockWt (fun _ => hmu) x)) (hs b).1
  have hs'V : ∀ a, s' a ∈ nabla Kf (nu1 muS) := fun a => WeylSandwich.nablaInt_subset_nabla _
    (fun x => natW_antitone (antitone_blockWt (fun _ => hmuS) x)) (hs' a).1
  have hsatE : ∀ F ∈ nabla Kf (nu1 H), io F ∈ edgeLat ι σ ϖ 1 Hp L'' L → F ∈ edgeLat ι σ ϖ 1 H L'' L := by
    intro F hF h
    rw [hHpH] at h
    exact topVec_sat hU hk0 hB₀ hL hL'' hH hf2 hsat hF h
  obtain ⟨wR, hwR, hvwR⟩ := exists_retract_targets hU hHp he io hioV hsatE x₁ Y₁ z₁ hz₁0
    (fun i => OffTop.mem_nabla_of_srcFam (hx₁ i)) (fun i => srcFam_subset_edgeLat he (hiox i))
    (fun l => tgtFam_subset_edgeDual he (hY₁ l)) hxY₁
  obtain ⟨r, Cc, hr, hcount, htest⟩ := cloud_count hU hHp h4 he (fun i => io (x₁ i)) wR z₁ hz₁ hiox hwR hvwR h₂
  refine ⟨r, hr, hcount, ?_⟩
  -- the sources at `λ`
  set Fi : Fin r → Pol (Unit × Fin n') k Kf := fun i => ∑ l, Cc i l • x₁ l with hFidef
  have hFi : ∀ i, Fi i ∈ SrcFam p 1 ι σ ϖ H t c₂ L'' L := fun i => sum_smul_mem_srcFam hU he _ _ hx₁
  have hioFi : ∀ i, io (Fi i) = ∑ l, Cc i l • io (x₁ l) := fun i => by
    rw [hFidef, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [← algebraMap_smul Kf (Cc i l) (x₁ l), map_smul, algebraMap_smul]
  let eq : Fin (Fintype.card Z * r) ≃ Z × Fin r :=
    finProdFinEquiv.symm.trans ((Fintype.equivFin Z).symm.prodCongr (Equiv.refl _))
  set X : Fin (Fintype.card Z * r) → Pol (Unit × Fin n') k Kf := fun q => Fi (eq q).2 * topVec p C mu (s (eq q).1)
    with hXdef
  have hX : ∀ q, X q ∈ SrcFam p 1 ι σ ϖ lam0 t (c₂ - 2 * TT.card * c) L'' L := by
    intro q
    have h := mul_mem_srcFam' hU hH hmu (hFi (eq q).2) (hsE (eq q).1).2.1
    rw [← hlamH] at h
    exact srcFam_anti h (Nat.sub_le _ _)
  refine goodSys_of_primitive hU he X hX fun a ha => ?_
  obtain ⟨q₀, hq₀⟩ := ha
  set b₀ := (eq q₀).1 with hb₀
  set a' : Fin r → O := fun i => a (eq.symm (b₀, i)) with ha'def
  have ha' : ∃ i, IsUnit (a' i) := ⟨(eq q₀).2, by simp only [a', b₀, Prod.mk.eta, Equiv.symm_apply_apply]; exact hq₀⟩
  obtain ⟨γ, hγ, w', hw', hγw⟩ := htest a' ha'
  -- the target at `λ`
  have hs'o : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → L₁ ≠ L'' → algebraMap O Kf ϖ ^ (((2 * TT.card * c : ℕ) : ℤ) +
      topA 1 muS) • topVec p C muS (s' b₀) ∈ nabMid ι σ ϖ muS L₁ L := by
    intro L₁ he₁ _
    have h := smul_mem_nabMid_of_nab hU hmuS he₁ (m := TT.card * c)
      (by rw [hmuSdef, sum_detShift_cloudDual hk]; simp) (hs'E b₀).2.2.2
    rw [smul_smul, OffTop.castK_zpow hU, ← zpow_add₀ hϖ, hAmuS] at h
    rw [hAmuS]
    convert h using 3
    push_cast
    ring
  obtain ⟨G, hG, hGpair⟩ := exists_adj_tgt hU hlam hAP Con hconB he (topVec p C muS (s' b₀)) (hs'E b₀).2.2.2
    (hs'E b₀).2.2.1 hs'o h2 hγ
  refine ⟨G, hG, (p : O) ^ κ b₀ * w', ?_, ?_⟩
  · rw [show 2 * D₁ + E = E + 2 * D₁ by ring, pow_add]
    exact mul_dvd_mul (pow_dvd_pow _ (hκ b₀)) hw'
  · have hsumV : ∑ q, a q • X q ∈ nabla Kf (nu1 lam0) := Submodule.sum_mem _ fun q _ =>
      Submodule.smul_of_tower_mem _ _ (OffTop.mem_nabla_of_srcFam (hX q))
    have hδE : ∀ i b, Con (X (eq.symm (b, i))) (topVec p C muS (s' b₀)) =
        if b₀ = b then (p : Kf) ^ κ b₀ • (Fi i * zE) else 0 := fun i b => by
      simp only [hXdef, Equiv.apply_symm_apply]
      exact con_topVec_delta hl hl2 (by rw [hAf2, hAmu, hAmuS]; ring) hdet Con heq hnuL s s' hsV hs'V κ
        (hw Kf (nu1 f2)) hδ hp
        (OffTop.mem_nabla_of_srcFam (hFi i)) b₀ b
    have hcon : Con (∑ q, a q • X q) (topVec p C muS (s' b₀)) =
        (p : Kf) ^ κ b₀ • ∑ i, a' i • ∑ l, Cc i l • io (x₁ l) := by
      rw [map_sum, LinearMap.sum_apply, ← Equiv.sum_comp eq.symm, Fintype.sum_prod_type,
        Finset.sum_eq_single b₀ (fun b _ hb => Finset.sum_eq_zero fun i _ => by
          rw [← algebraMap_smul Kf (a _), map_smul, LinearMap.smul_apply, hδE, ite_eq_right (Ne.symm hb), smul_zero])
          (fun h => absurd (Finset.mem_univ b₀) h), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul Kf (a _), map_smul, LinearMap.smul_apply, hδE, ite_eq_left rfl, ← hioFi, hio,
        ← algebraMap_smul Kf (a' i), smul_comm]
    rw [hGpair _ hsumV, hcon, map_smul, LinearMap.smul_apply, smul_eq_mul, hγw, map_mul, map_pow, map_natCast]

end PerEdge

end

end FirstCloud
