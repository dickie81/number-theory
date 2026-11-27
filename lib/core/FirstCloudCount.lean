import FirstCloudBase

/-!
# The cloud count: good directions of a flat system at the next flat weight (L5, A-N17)

The linear algebra of Annex I N17 (module 11, `FirstCloud`), at one type-1 edge `e = (L″ ⊂ L)` and one dominant
weight (in the cloud step, `H⁺ = fl(A + 2c, B + 2c)`): the images `v_k = io(x¹_k)` of the sources of a good system at
`H = fl(A, B)`, with targets `w_l ∈ 𝓡′(e)` pairing to `z₁·δ_{kl}`, and a good system `(x², y², z₂, M₂)` of size `n₂`
at the weight itself.

**Main results.**
* *The retraction targets* (`exists_retract_targets`, N9″): if `io` is saturated on the edge lattices
  (`io F ∈ 𝓡(e) ⇒ F ∈ 𝓡(e)`), the targets `y¹` of `𝓡′_H(e)` pull back to targets `w_l ∈ 𝓡′(e)` with
  `pairE(io x¹_k, w_l) = z₁·δ_{kl}`.
* *The count* (`cloud_count`, N9′ with N3): there are `r` combinations `F_i = Σ_k C_{ik} v_k` with
  `#edges·(n₁ − r + n₂) ≤ dim V`, every primitive combination of which pairs with some target of the target family
  to a divisor of `p^{2D₁}`.

**The routes.** The pairing vectors `(pairE(v_k, γ))_k` of the targets `γ` form a submodule `Γ ⊆ O^{n₁}`; in a Smith
basis `b` of `O^{n₁}` for `Γ` (`Submodule.smithNormalForm`, elementary divisors `a_j`) the good coordinates are the
`b_{f(j)}` with `a_j ∣ z₁z₂`, and the coordinate functional of a good coordinate gives the combination `F_i`: it pairs
with the target realising `a_j·b_{f(j)}` to `a_j`. On a bad coordinate every target pairs into `z₁z₂·𝔪`, so the bad
combinations and `x²`, with the targets `Σ_k b_l(k)·w_k` and `y²·M₂`, have the Gram matrix `[[z₁, z₁z₂E₀], [B, z₂]]`,
`E₀ ≡ 0` modulo `𝔪`, which has a `z₁z₂`-right inverse (`exists_fromBlocks_inv`), and the per-edge upper bound
(`LocalRank.goodSys_card_le`, `2·2D₁ < c`) counts them. The retraction targets come from primitive tests
(`LocalRank.smul_mem_of_primitive`): a primitive combination `F` of `x¹` pairs to a unit times `z₁` with some `y¹`,
so `F ∉ z₁ϖ·𝓡_H(e)`, hence (saturation) `io F ∉ z₁ϖ·𝓡(e)`, and some vector of a dual basis of `𝓡′(e)` pairs it to a
divisor of `z₁` (`eq_sum_pairE`).
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstAssembly

open scoped Matrix Pointwise

noncomputable section

/-! ## A block matrix with a right inverse -/

section Block

variable {R : Type*} [CommRing R] [IsLocalRing R] {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
  [DecidableEq J]

/-- **A near-triangular block matrix has a `z₁z₂`-right inverse**: `[[z₁·1, z₁z₂·E₀], [B, z₂·1]]·M = z₁z₂·1` when the
entries of `E₀` lie in the maximal ideal. With `W = 1 − B·E₀` (invertible: `1` modulo `𝔪`),
`M = [[1, −z₂E₀], [0, 1]]·[[z₂·1, 0], [−W⁻¹B, z₁W⁻¹]]`. -/
theorem exists_fromBlocks_inv (z₁ z₂ : R) (E₀ : Matrix I J R) (hE : ∀ i l, E₀ i l ∈ IsLocalRing.maximalIdeal R)
    (B : Matrix J I R) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) R,
      Matrix.fromBlocks (z₁ • 1) ((z₁ * z₂) • E₀) B (z₂ • 1) * M = (z₁ * z₂) • (1 : Matrix (I ⊕ J) (I ⊕ J) R) := by
  set W : Matrix J J R := 1 - B * E₀
  have hW : IsUnit W.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have e : (IsLocalRing.residue R).mapMatrix W = 1 := by
      ext i l
      have h : (B * E₀) i l ∈ IsLocalRing.maximalIdeal R :=
        Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hE m l)
      simp [W, Matrix.one_apply, (IsLocalRing.residue_eq_zero_iff _).2 h]
    rw [e, Matrix.det_one]
    exact one_ne_zero
  have hWW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv _ hW
  have h1 : Matrix.fromBlocks (z₁ • 1) ((z₁ * z₂) • E₀) B (z₂ • 1) * Matrix.fromBlocks 1 (-(z₂ • E₀)) 0 1 =
      Matrix.fromBlocks (z₁ • 1) 0 B (z₂ • W) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp only [Matrix.mul_neg, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      exact neg_add_cancel _
    · simp
    · simp only [W, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, smul_sub]
      abel
  have h2 : Matrix.fromBlocks (z₁ • 1) 0 B (z₂ • W) * Matrix.fromBlocks (z₂ • 1) 0 (-(W⁻¹ * B)) (z₁ • W⁻¹) =
      (z₁ * z₂) • (1 : Matrix (I ⊕ J) (I ⊕ J) R) := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    congr 1
    · simp [smul_smul, mul_comm]
    · simp
    · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, Matrix.smul_mul, ← Matrix.mul_assoc, hWW,
        Matrix.one_mul, smul_zero]
      exact add_neg_cancel _
    · simp only [Matrix.mul_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, hWW, smul_smul]
  exact ⟨Matrix.fromBlocks 1 (-(z₂ • E₀)) 0 1 * Matrix.fromBlocks (z₂ • 1) 0 (-(W⁻¹ * B)) (z₁ • W⁻¹), by
    rw [← Matrix.mul_assoc, h1, h2]⟩

end Block

/-! ## Families, duals and expansions at an edge -/

section Edge

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Targets lie in the dual edge lattice** of their own edge. -/
theorem tgtFam_subset_edgeDual {lam0 : Fin n' → Fin k → ℤ} {t c : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) {G : Pol (Unit × Fin n') k Kf} (hG : G ∈ TgtFam p 1 ι σ ϖ lam0 t c L'' L) :
    G ∈ edgeDual p 1 ι σ ϖ lam0 L'' L :=
  (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hG.1).2 L'') he

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **Sources lie in the edge lattice** of their own edge. -/
theorem srcFam_subset_edgeLat {lam0 : Fin n' → Fin k → ℤ} {t c : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ SrcFam p 1 ι σ ϖ lam0 t c L'' L) :
    F ∈ edgeLat ι σ ϖ 1 lam0 L'' L :=
  Set.mem_iInter₂.1 hF.1.2 L he

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **Pairings of combinations on the left**: `pairE(Σ_i a_i·x_i, G) = Σ_i a_i·pairE(x_i, G)`. -/
theorem pairE_sum_smul_left [CharZero Kf] (lam0 : Fin n' → Fin k → ℤ) {ι' : Type} (s : Finset ι') (a : ι' → O)
    (x : ι' → Pol (Unit × Fin n') k Kf) (G : Pol (Unit × Fin n') k Kf) :
    pairE p 1 lam0 (∑ i ∈ s, a i • x i) G = ∑ i ∈ s, algebraMap O Kf (a i) * pairE p 1 lam0 (x i) G := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [← algebraMap_smul Kf, map_smul, LinearMap.smul_apply, smul_eq_mul]

omit [CharZero Kf] in
/-- **Expansion in a dual basis**: if `B(x_i, y_l) = δ_{il}`, every `v` in the `Kf`-span of the `x_i` is
`Σ_i B(v, y_i)·x_i`. -/
theorem eq_sum_pairE {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (Bf : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf →ₗ[Kf] Kf) {x y : ι' → Pol (Unit × Fin n') k Kf}
    (hxy : ∀ i l, Bf (x i) (y l) = if i = l then 1 else 0) {v : Pol (Unit × Fin n') k Kf}
    (hv : v ∈ Submodule.span Kf (Set.range x)) : v = ∑ i, Bf v (y i) • x i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Kf).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hxy, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The retraction targets** (N9″): if a `Kf`-linear `io : V(H) → V(H⁺)` is saturated on the edge lattices
(`io F ∈ 𝓡_{H⁺}(e) ⇒ F ∈ 𝓡_H(e)`), sources `x_i` with `io x_i ∈ 𝓡_{H⁺}(e)` and targets `y_l ∈ 𝓡′_H(e)` with
`pairE_H(x_i, y_l) = z₁·δ_{il}` give targets `w_l ∈ 𝓡′_{H⁺}(e)` with `pairE_{H⁺}(io x_i, w_l) = z₁·δ_{il}`. By primitive
tests (`smul_mem_of_primitive`): for a primitive `a`, `F = Σ a_i x_i` pairs to `z₁a_l` with `y_l`; if `io F` paired
into `z₁·𝔪` with every vector of a dual basis of `𝓡′_{H⁺}(e)`, then `io F ∈ z₁ϖ·𝓡_{H⁺}(e)`, so `F ∈ z₁ϖ·𝓡_H(e)` and
every `a_l` would lie in `ϖ·O`. -/
theorem exists_retract_targets (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lamH lamP : Fin n' → Fin k → ℤ}
    (hlamP : ∀ s, Antitone (lamP s)) {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L)
    (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf)
    (hioV : ∀ F ∈ nabla Kf (nu1 lamH), io F ∈ nabla Kf (nu1 lamP))
    (hsat : ∀ F ∈ nabla Kf (nu1 lamH), io F ∈ edgeLat ι σ ϖ 1 lamP L'' L → F ∈ edgeLat ι σ ϖ 1 lamH L'' L)
    {n₁ : ℕ} (x y : Fin n₁ → Pol (Unit × Fin n') k Kf) (z₁ : O) (hz₁ : z₁ ≠ 0)
    (hxV : ∀ i, x i ∈ nabla Kf (nu1 lamH)) (hx : ∀ i, io (x i) ∈ edgeLat ι σ ϖ 1 lamP L'' L)
    (hy : ∀ l, y l ∈ edgeDual p 1 ι σ ϖ lamH L'' L)
    (hxy : ∀ i l, pairE p 1 lamH (x i) (y l) = if i = l then algebraMap O Kf z₁ else 0) :
    ∃ w : Fin n₁ → Pol (Unit × Fin n') k Kf, (∀ l, w l ∈ edgeDual p 1 ι σ ϖ lamP L'' L) ∧
      ∀ i l, pairE p 1 lamP (io (x i)) (w l) = if i = l then algebraMap O Kf z₁ else 0 := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  have hϖ := varpiK_ne_zero hU
  obtain ⟨x', y', hx', hy', hxy', hsx, -⟩ := edgeLat_dualPair hU hlamP he
  have hRadd : ∀ F G, F ∈ edgeLat ι σ ϖ 1 lamP L'' L → G ∈ edgeLat ι σ ϖ 1 lamP L'' L →
      F + G ∈ edgeLat ι σ ϖ 1 lamP L'' L := fun F G hF hG => add_mem_edgeLat hF hG
  -- the pairing vectors of the dual edge lattice
  let S : Submodule O (Fin n₁ → O) :=
    { carrier := {u | ∃ t ∈ edgeDual p 1 ι σ ϖ lamP L'' L,
        ∀ i, pairE p 1 lamP (io (x i)) t = algebraMap O Kf (u i)}
      add_mem' := by
        rintro u u' ⟨t, ht, htu⟩ ⟨t', ht', htu'⟩
        exact ⟨t + t', add_mem ht ht', fun i => by rw [map_add, htu, htu', Pi.add_apply, map_add]⟩
      zero_mem' := ⟨0, zero_mem _, fun i => by simp⟩
      smul_mem' := by
        rintro a u ⟨t, ht, htu⟩
        refine ⟨a • t, Submodule.smul_mem _ a ht, fun i => ?_⟩
        rw [← algebraMap_smul Kf a t, map_smul, htu, smul_eq_mul, Pi.smul_apply, smul_eq_mul, map_mul] }
  have hP : ∀ v : Fin n₁ → O, z₁ • v ∈ S := by
    refine smul_mem_of_primitive S hz₁ fun a ha => ?_
    obtain ⟨l, hl⟩ := ha
    set F := ∑ i, a i • x i with hFdef
    have hFV : F ∈ nabla Kf (nu1 lamH) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (hxV i)
    have hioFR : io F ∈ edgeLat ι σ ϖ 1 lamP L'' L := by
      rw [hFdef, map_sum]
      exact Finset.sum_induction _ (· ∈ edgeLat ι σ ϖ 1 lamP L'' L) hRadd (by
        rw [hx']; exact zero_mem _) fun i _ => by
          rw [← algebraMap_smul Kf (a i) (x i), map_smul]
          exact smul_mem_edgeLat ⟨a i, rfl⟩ (hx i)
    have hval : ∀ i k', ∃ o : O, pairE p 1 lamP (io (x k')) (y' i) = algebraMap O Kf o := fun i k' => by
      have hm : y' i ∈ edgeDual p 1 ι σ ϖ lamP L'' L := by rw [hy']; exact Submodule.subset_span ⟨i, rfl⟩
      exact ((hm.2 _ (hx k')).imp fun _ h => h.symm)
    choose U hUv using hval
    have hUS : ∀ i, U i ∈ S := fun i =>
      ⟨y' i, by rw [hy']; exact Submodule.subset_span ⟨i, rfl⟩, hUv i⟩
    have hioF : io F = ∑ k', a k' • io (x k') := by
      rw [hFdef, map_sum]
      exact Finset.sum_congr rfl fun k' _ => by rw [← algebraMap_smul Kf (a k') (x k'), map_smul, algebraMap_smul]
    have hdot : ∀ i, pairE p 1 lamP (io F) (y' i) = algebraMap O Kf (a ⬝ᵥ U i) := fun i => by
      rw [hioF, pairE_sum_smul_left, dotProduct, map_sum]
      exact Finset.sum_congr rfl fun k' _ => by rw [hUv, map_mul]
    by_contra hno
    push Not at hno
    have hc : ∀ i, ∃ q : O, pairE p 1 lamP (io F) (y' i) = algebraMap O Kf (z₁ * ϖ * q) := by
      intro i
      obtain ⟨u, hu, hue⟩ := exists_eq_mul_of_not_dvd (hno _ (hUS i))
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hU.unif_O, Ideal.mem_span_singleton] at hu
      obtain ⟨q, rfl⟩ := hu
      exact ⟨q, by rw [hdot, hue, mul_assoc]⟩
    choose q hq using hc
    have hz₁ϖ : algebraMap O Kf (z₁ * ϖ) ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (mul_ne_zero hz₁ hU.unif_O.ne_zero)
    have hmem : io ((algebraMap O Kf (z₁ * ϖ))⁻¹ • F) ∈ edgeLat ι σ ϖ 1 lamP L'' L := by
      have hsp : io F ∈ Submodule.span Kf (Set.range x') := by rw [hsx]; exact hioV F hFV
      rw [map_smul, eq_sum_pairE (pairE p 1 lamP) hxy' hsp, Finset.smul_sum, hx']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hq i, smul_smul, show (algebraMap O Kf (z₁ * ϖ))⁻¹ * algebraMap O Kf (z₁ * ϖ * q i) =
        algebraMap O Kf (q i) by rw [map_mul _ (z₁ * ϖ), ← mul_assoc, inv_mul_cancel₀ hz₁ϖ, one_mul],
        algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hF' := hsat _ (Submodule.smul_mem _ _ hFV) hmem
    obtain ⟨o, ho⟩ := (hy l).2 _ hF'
    have h2 : pairE p 1 lamH F (y l) = algebraMap O Kf (a l * z₁) := by
      rw [hFdef, pairE_sum_smul_left, Finset.sum_eq_single l (fun i _ hi => by simp [hxy, hi])
        (fun h => absurd (Finset.mem_univ l) h), hxy]
      simp
    rw [map_smul, LinearMap.smul_apply, h2, smul_eq_mul] at ho
    have hz₁' : algebraMap O Kf z₁ ≠ 0 := (map_ne_zero_iff _ hinj).2 hz₁
    have e : algebraMap O Kf (a l) = algebraMap O Kf (ϖ * o) := by
      rw [map_mul, ho, map_mul, map_mul]
      field_simp
    rw [hinj e] at hl
    exact hU.unif_O.not_isUnit (isUnit_of_mul_isUnit_left hl)
  choose w hw hwv using fun l => hP (Pi.single l 1)
  refine ⟨w, hw, fun i l => ?_⟩
  rw [hwv l i, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The cloud count** (N17 at one edge, N9′ with N3): let `v_1, …, v_{n₁}` be sources at the weight with targets
`w_l ∈ 𝓡′(e)`, `pairE(v_i, w_l) = z₁·δ_{il}`, `z₁ ∣ p^{D₁}`, and let the edge carry a good system of size `n₂` at
denominator `D₁`, with `4D₁ < c`. Then there are `r` combinations `F_i = Σ_l C_{il}·v_l` with
`#edges·(n₁ − r + n₂) ≤ dim V` such that every primitive combination of the `F_i` pairs with some target of the target
family to a divisor of `p^{2D₁}`. -/
theorem cloud_count (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lamP : Fin n' → Fin k → ℤ} (hlam : ∀ s, Antitone (lamP s))
    {t c D₁ : ℕ} (hc : 4 * D₁ < c) {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L)
    {n₁ n₂ : ℕ} (v w : Fin n₁ → Pol (Unit × Fin n') k Kf) (z₁ : O) (hz₁ : z₁ ∣ (p : O) ^ D₁)
    (hv : ∀ i, v i ∈ SrcFam p 1 ι σ ϖ lamP t c L'' L) (hw : ∀ i, w i ∈ edgeDual p 1 ι σ ϖ lamP L'' L)
    (hvw : ∀ i l, pairE p 1 lamP (v i) (w l) = if i = l then algebraMap O Kf z₁ else 0)
    (h₂ : GoodSys p 1 ι σ ϖ lamP t c D₁ L'' L n₂) :
    ∃ (r : ℕ) (C : Fin r → Fin n₁ → O), r ≤ n₁ ∧ nEdges (n' := n') p 1 L * (n₁ - r + n₂) ≤ dimV Kf lamP ∧
      ∀ a : Fin r → O, (∃ i, IsUnit (a i)) → ∃ γ ∈ TgtFam p 1 ι σ ϖ lamP t c L'' L, ∃ w' : O,
        w' ∣ (p : O) ^ (2 * D₁) ∧ pairE p 1 lamP (∑ i, a i • ∑ l, C i l • v l) γ = algebraMap O Kf w' := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  obtain ⟨x₂, y₂, z₂, M₂, -, hz₂, hx₂, hy₂, hG₂⟩ := h₂
  set Y₂ : Fin n₂ → Pol (Unit × Fin n') k Kf := fun b => ∑ m, M₂ m b • y₂ m with hY₂def
  have hY₂ : ∀ b, Y₂ b ∈ TgtFam p 1 ι σ ϖ lamP t c L'' L := fun b => sum_smul_mem_tgtFam _ _ hy₂
  have hxY : ∀ a b, pairE p 1 lamP (x₂ a) (Y₂ b) = if a = b then algebraMap O Kf z₂ else 0 := by
    intro a b
    rw [pairE_sum_smul, ← hG₂ a b]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hzz : z₁ * z₂ ∣ (p : O) ^ (2 * D₁) := by rw [two_mul, pow_add]; exact mul_dvd_mul hz₁ hz₂
  -- the pairing vectors of the targets
  have hval : ∀ γ ∈ TgtFam p 1 ι σ ϖ lamP t c L'' L, ∀ i, ∃ o : O, pairE p 1 lamP (v i) γ = algebraMap O Kf o :=
    fun γ hγ i => (pairE_mem_of_src_tgt he (hv i).1 hγ.1).imp fun _ h => h.symm
  obtain ⟨h0, hadd, hsmul⟩ := tgtFam_closed (p := p) (ι := ι) (σ := σ) (ϖ := ϖ) (lam0 := lamP) (r := 1) (t := t)
    (c := c) (L'' := L'') (L := L)
  let T : Set (Fin n₁ → O) := {u | ∃ γ ∈ TgtFam p 1 ι σ ϖ lamP t c L'' L,
    ∀ i, pairE p 1 lamP (v i) γ = algebraMap O Kf (u i)}
  have hT : ∀ u ∈ Submodule.span O T, u ∈ T := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => exact hu
    | zero => exact ⟨0, h0, fun i => by simp⟩
    | add u u' _ _ hu hu' =>
      obtain ⟨G, hG, hGu⟩ := hu
      obtain ⟨G', hG', hGu'⟩ := hu'
      exact ⟨G + G', hadd G G' hG hG', fun i => by rw [map_add, hGu, hGu', Pi.add_apply, map_add]⟩
    | smul a u _ hu =>
      obtain ⟨G, hG, hGu⟩ := hu
      refine ⟨a • G, hsmul a G hG, fun i => ?_⟩
      rw [← algebraMap_smul Kf, map_smul, hGu, smul_eq_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  obtain ⟨m, B⟩ := (Submodule.span O T).smithNormalForm (Pi.basisFun O (Fin n₁))
  have hcoord : ∀ l (u : Fin n₁ → O), ∑ i, B.bM.coord l (Pi.single i 1) * u i = B.bM.coord l u := by
    intro l u
    conv_rhs => rw [← Finset.univ_sum_single u]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Pi.single i (u i) : Fin n₁ → O) = u i • Pi.single i 1 := by
      ext l'
      simp [Pi.single_apply]
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hΓf : ∀ (u : Submodule.span O T) (jj : Fin m),
      B.bM.coord (B.f jj) (u : Fin n₁ → O) = B.a jj * B.bN.repr u jj := by
    intro u jj
    rw [Module.Basis.coord_apply, B.repr_apply_embedding_eq_repr_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hcomb : ∀ γ (u : Fin n₁ → O), (∀ i, pairE p 1 lamP (v i) γ = algebraMap O Kf (u i)) →
      ∀ cc : Fin n₁ → O, pairE p 1 lamP (∑ l, cc l • v l) γ = algebraMap O Kf (∑ l, cc l * u l) := by
    intro γ u hu cc
    rw [pairE_sum_smul_left, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hu, map_mul]
  set G : Finset (Fin m) := Finset.univ.filter fun jj => B.a jj ∣ z₁ * z₂ with hGdef
  let eG : Fin G.card ≃ G := G.equivFin.symm
  refine ⟨G.card, fun i l => B.bM.coord (B.f (eG i)) (Pi.single l 1), ?_, ?_, ?_⟩
  · calc G.card ≤ Fintype.card (Fin m) := Finset.card_le_univ _
      _ = m := Fintype.card_fin m
      _ ≤ n₁ := by simpa using Fintype.card_le_of_embedding B.f
  · -- the count: the bad coordinates and the good system at the weight
    set Bad : Finset (Fin n₁) := Finset.univ \ G.map B.f with hBaddef
    have hBad : Bad.card = n₁ - G.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_map]
    let eB : Fin Bad.card ≃ Bad := Bad.equivFin.symm
    have hbad : ∀ u ∈ Submodule.span O T, ∀ l ∈ Bad, ∃ e₀ ∈ IsLocalRing.maximalIdeal O,
        B.bM.coord l u = z₁ * z₂ * e₀ := by
      intro u hu l hl
      by_cases hlf : l ∈ Set.range B.f
      · obtain ⟨jj, rfl⟩ := hlf
        have hjG : jj ∉ G := fun h => (Finset.mem_sdiff.1 hl).2 (Finset.mem_map_of_mem _ h)
        have hnd : ¬ B.a jj ∣ z₁ * z₂ := fun h => hjG (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        obtain ⟨e, he', hae⟩ := exists_eq_mul_of_not_dvd hnd
        refine ⟨e * B.bN.repr ⟨u, hu⟩ jj, Ideal.mul_mem_right _ _ he', ?_⟩
        have h1 : B.bM.coord (B.f jj) u = B.a jj * B.bN.repr ⟨u, hu⟩ jj := hΓf ⟨u, hu⟩ jj
        rw [h1, hae]
        ring
      · exact ⟨0, zero_mem _, by rw [Module.Basis.coord_apply, B.repr_eq_zero_of_notMem_range ⟨u, hu⟩ hlf,
          mul_zero]⟩
    let xs : Fin Bad.card → Pol (Unit × Fin n') k Kf := fun i => ∑ l, B.bM.coord (eB i) (Pi.single l 1) • v l
    let ws : Fin Bad.card → Pol (Unit × Fin n') k Kf := fun i => ∑ l, B.bM (eB i) l • w l
    have hxs : ∀ i, xs i ∈ SrcFam p 1 ι σ ϖ lamP t c L'' L := fun i => sum_smul_mem_srcFam hU he _ _ hv
    have hws : ∀ i, ws i ∈ edgeDual p 1 ι σ ϖ lamP L'' L := fun i =>
      Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hw l)
    have hxsws : ∀ i i', pairE p 1 lamP (xs i) (ws i') = if i = i' then algebraMap O Kf z₁ else 0 := by
      intro i i'
      have e1 : ∀ l, pairE p 1 lamP (v l) (ws i') = algebraMap O Kf (B.bM (eB i') l * z₁) := fun l => by
        rw [pairE_sum_smul, Finset.sum_eq_single l (fun l' _ hl' => by simp [hvw, Ne.symm hl'])
          (fun h => absurd (Finset.mem_univ l) h), hvw]
        simp [map_mul]
      rw [hcomb (ws i') (fun l => B.bM (eB i') l * z₁) e1]
      simp only [← mul_assoc, ← Finset.sum_mul]
      rw [hcoord, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hii : i = i'
      · subst hii
        simp
      · have : (eB i' : Fin n₁) ≠ eB i := fun h => hii (eB.injective (Subtype.ext h)).symm
        simp [hii, this]
    have hxsY : ∀ i b, ∃ e₀ ∈ IsLocalRing.maximalIdeal O,
        pairE p 1 lamP (xs i) (Y₂ b) = algebraMap O Kf (z₁ * z₂ * e₀) := by
      intro i b
      choose u hu using hval (Y₂ b) (hY₂ b)
      obtain ⟨e₀, he₀, hcoe⟩ := hbad u (Submodule.subset_span ⟨Y₂ b, hY₂ b, hu⟩) (eB i) (eB i).2
      exact ⟨e₀, he₀, by rw [hcomb _ u hu, hcoord, hcoe]⟩
    choose E₀ hE₀ hE₀eq using hxsY
    have hx₂ws : ∀ a i, ∃ o : O, pairE p 1 lamP (x₂ a) (ws i) = algebraMap O Kf o := fun a i =>
      ((hws i).2 _ (srcFam_subset_edgeLat he (hx₂ a))).imp fun _ h => h.symm
    choose Bm hBm using hx₂ws
    obtain ⟨M, hM⟩ := exists_fromBlocks_inv z₁ z₂ (Matrix.of E₀) hE₀ (Matrix.of Bm)
    let X : Fin Bad.card ⊕ Fin n₂ → Pol (Unit × Fin n') k Kf := Sum.elim xs x₂
    let Yt : Fin Bad.card ⊕ Fin n₂ → Pol (Unit × Fin n') k Kf := Sum.elim ws Y₂
    set Gm := Matrix.fromBlocks (z₁ • (1 : Matrix (Fin Bad.card) (Fin Bad.card) O)) ((z₁ * z₂) • Matrix.of E₀)
      (Matrix.of Bm) (z₂ • (1 : Matrix (Fin n₂) (Fin n₂) O)) with hGm
    have hgram : ∀ α β, pairE p 1 lamP (X α) (Yt β) = algebraMap O Kf (Gm α β) := by
      rintro (i | a) (i' | b)
      · simp only [X, Yt, Sum.elim_inl, hxsws, hGm, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [X, Yt, Sum.elim_inl, Sum.elim_inr, hE₀eq, hGm, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
          Matrix.of_apply, smul_eq_mul]
      · simp only [X, Yt, Sum.elim_inl, Sum.elim_inr, hBm, hGm, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      · simp only [X, Yt, Sum.elim_inr, hxY, hGm, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul]
        split_ifs <;> simp
    let e := (finSumFinEquiv (m := Bad.card) (n := n₂)).symm
    have hcard := goodSys_card_le hU hlam (show 2 * (2 * D₁) < c by omega) he (fun i => X (e i))
      (fun i => Yt (e i)) (z₁ * z₂) (M.submatrix e e) hzz
      (fun i => by
        rcases h : e i with i' | a
        · simpa [X, h] using hxs i'
        · simpa [X, h] using hx₂ a)
      (fun i => by
        rcases h : e i with i' | b
        · simpa [Yt, h] using hws i'
        · simpa [Yt, h] using tgtFam_subset_edgeDual he (hY₂ b))
      (fun i l => by
        have hsum : ∑ m', pairE p 1 lamP (X (e i)) (Yt (e m')) * algebraMap O Kf (M (e m') (e l)) =
            algebraMap O Kf ((Gm * M) (e i) (e l)) := by
          rw [Matrix.mul_apply, map_sum]
          rw [← Equiv.sum_comp e.symm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Equiv.apply_symm_apply, hgram, map_mul]
        simp only [Matrix.submatrix_apply]
        rw [hsum, hM, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        by_cases hil : i = l
        · subst hil
          simp
        · simp [hil, e.injective.ne hil])
    rwa [hBad] at hcard
  · -- the primitive test
    rintro a ⟨i₀, hi₀⟩
    set j₀ := (eG i₀ : Fin m)
    have hj₀ : B.a j₀ ∣ z₁ * z₂ := (Finset.mem_filter.1 (eG i₀).2).2
    obtain ⟨γ, hγ, hγu⟩ := hT _ (B.bN j₀).2
    refine ⟨γ, hγ, a i₀ * B.a j₀, (hi₀.mul_left_dvd.2 hj₀).trans hzz, ?_⟩
    have e1 : ∑ i, a i • ∑ l, B.bM.coord (B.f (eG i)) (Pi.single l 1) • v l =
        ∑ l, (∑ i, a i * B.bM.coord (B.f (eG i)) (Pi.single l 1)) • v l := by
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    rw [e1, hcomb γ _ hγu]
    congr 1
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hcoord]
    rw [Finset.sum_eq_single i₀]
    · rw [B.snf j₀, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp [j₀]
    · intro i _ hi
      have hne : B.f (eG i) ≠ B.f j₀ := fun h => hi (eG.injective (Subtype.ext (B.f.injective h)))
      rw [B.snf j₀, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp [Ne.symm hne]
    · exact fun h => absurd (Finset.mem_univ i₀) h

end Edge

end

end FirstCloud
