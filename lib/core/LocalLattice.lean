import InertModel

/-!
# The local lattice problem: edge lattices, the pairing and the model facts

L2 of the local theory of the gain, at one orbit of an inert prime `p` in the setting `Unram` of `InertModel`: the
blocks are `Unit × Fin n'`, block `((), s)` with the weight `lamAt lam0 s` (`wt1`), and `V = ∇_{Kf}` (`dimV`).

**Lattices of blocks.** For `O`-lattices `Λ_b` in `Kf^k`, one per block, `∇_Λ` (`nablaB`) and `Δ_Λ` (`deltaB`) are
the `F ∈ ∇_{Kf}` whose twist by basis matrices of the `Λ_b` lies in `∇_O`, resp. `Δ_O`; `NablaT` and `DeltaT` are the
blocks `σ^s(L_v) ⊗ O`, and `∇(L)` (`nab`) is `NablaT` of one lattice. The normalised bilinear Fock form
`⟨F, G⟩ = fock(F, G)/κ` (`nf`) makes `Δ_O` the dual of `∇_O`. The dual of a set `S` for a bilinear form `B` is the
`O`-module of the `G ∈ ∇_{Kf}` with `B(F, G) ∈ O` on `S` (`bdual`); `∇(L)^∨` is the dual of `∇(L)` for `nf`. The dual
lattice of an `R`-lattice in `K^k` is taken for the dot product (`dualLat`).

**The local lattice problem.** For an edge `L″ ⊂ L` of type `r` (`IsEdge`):
* the midpoint blocks `σ^s(L″)⊗O + ϖ·σ^s(L)⊗O` (`midBlk`), with `∇`-lattice `∇(mid)` (`nabMid`);
* the edge lattice `𝓡(L″ ⊂ L) = ϖ^{−A_r}·∇(mid)` (`edgeLat`), `A_r = topSum r` (`topA`);
* the pairing `pairE(F, G) = ⟨p^{A_r}F, G⟩` (`pairE`), and the dual edge lattice `𝓡′(L″ ⊂ L)`, the `pairE`-dual of
  `𝓡(L″ ⊂ L)` (`edgeDual`);
* the source lattice at depth `t` of `L″`, `ϖ^{−t}∇(L″) ∩ ⋂_{L″ ⊂ L′} 𝓡(L″ ⊂ L′)` (`srcLat`), and the target lattice
  at depth `t` of `L`, `ϖ^{−t}∇(L)^∨ ∩ ⋂_{L″ ⊂ L} 𝓡′(L″ ⊂ L)` (`tgtLat`), over the edges of type `r`.

`LLPAt … t D κ c* L` asks for edges `L″_i ⊂ L` and vectors `F_i` in the source lattices of the `L″_i`, `ϖ^{c*}`-small
on the other edges out of the `L″_i` (`F_i ∈ ϖ^{c*}·𝓡(L″_i ⊂ L′)` for `L′ ≠ L`), and an `O`-linear map
`u : O^n → tgtLat(L)`, `n ≥ (1 − κ)·dim V`, with an `O`-matrix `A` such that `Σ_i A_{a,i}·pairE(F_i, u(x)) = p^D·x_a`.
The pairings are in `O` (`pairE_mem_of_src_tgt`), and those of the `F_i` with the targets at `L′ ≠ L` are in
`ϖ^{c*}·O` (`pairE_mem_of_small`). The exceptional fraction `kappa` is the least `κ ≥ 0` for which `LLPAt` holds at
every lattice; it lies in `[0, 1]` (`kappa_nonneg`, `kappa_le_one`, `llpAt_one`), and `LLPAt` holds above it
(`llpAt_of_kappa_lt`, `llpAt_mono`).

**Main results: the six model facts.**
1. *Inclusions* (`nab_subset_edgeLat`, `bdual_nab_le_edgeDual`): `∇(L″) ⊆ 𝓡(e)` and `∇(L)^∨ ⊆ 𝓡′(e)` for every edge
   `e = (L″ ⊂ L)` and dominant weights; so `∇(L″)` lies in its source lattices and `∇(L)^∨` in its target lattices
   (`nab_subset_srcLat`, `bdual_nab_le_tgtLat`).
2. *Perfect pairing* (`edgeLat_dualPair`, `bdual_edgeDual`): `𝓡(e)` and `𝓡′(e)` are the `O`-spans of `pairE`-dual
   bases of `V`, so each is the other's `pairE`-dual.
3. *Adapted basis* (`exists_adapted_basis`): a basis `x_i` of `V` and integers `π_i ≤ A_r` with
   `∇(L″) = span_O(x_i)`, `∇(L) = span_O(p^{π_i}x_i)` and `∇(mid) = span_O(ϖ^{π_i}x_i)`.
4. *Spanning* (`exists_basis_NablaT`; for block lattices `nablaB_dualPair`): `∇(L)` is the `O`-span of a basis of `V`.
5. *Duality* (`bdual_NablaT`; for block lattices `bdual_nablaB_dualLat`): `∇(L)^∨ = Δ(L^∨)` exactly. With
   `κ·∇_Λ ⊆ Δ_Λ` and `det(κ·Gzb)·Δ_Λ ⊆ ∇_Λ` (`smul_nablaB_subset_deltaB`, `smul_deltaB_subset_nablaB`), `∇(L)^∨` and
   `∇(L^∨)` agree up to these two nonzero integers (`bdual_NablaT_compare`), that is up to `p^{e′}`,
   `e′ = v_p(κ) + v_p(det(κ·Gzb))`.
6. *One lattice suffices* (`llpAt_of_llpAt`, `kappa_eq`): `GL_k(Qq)` is transitive on lattices (`exists_gmap_eq`) and
   moves the local lattice problem (`llpAt_gmap`).

**The routes.** An edge has a basis matrix `B` of `L` and a set `S` of `r` indices with `L″` spanned by the columns of
`B·diag(p on S)` (`exists_basis_edge`); as `p = ϖ²`, the midpoint blocks have the basis matrices
`ι σ^s(B)·diag(ϖ on S)` (`isBasisOf_midBlk`). The twist by `diag(c on S)` multiplies the row-homogeneous `zb_i` by
`c^{π_i}` (`twist_diag_zbK`), which gives the adapted basis; `π_i ≤ A_r` is `exp_le` for a nonzero bideterminant of
the row weight of `zb_i` (`pexp_le`). Twists are adjoint for the Fock form, `⟨twist_g F, G⟩ = ⟨F, twist_{gᵀ}G⟩`
(`nf_twist`), so `twist_{C⁻¹} zb` and `twist_{Cᵀ} zdual` are dual families (`nf_twist_zbK_zdualK`), and the dual of
the `O`-span of a basis is the span of the dual basis (`bdual_span`, `bdual_flip_span`): facts 2, 4 and 5. For the Gram
constants, `κ·zb_i = Σ_l fock(zb_i, zb_l)·zdual_l` with integer coefficients, and `det(κ·Gzb)·Γ = κ·adj(κ·Gzb)` is
integral (`det_mul_Γ_mem`). For fact 6, `g` moves sources by the twist by the `ι σ^s(g⁻¹)` (`mvS`) and targets by the
twist by the `ι σ^s(g)ᵀ` (`mvT`), which keep the pairings (`nf_mv`, `pairE_mv`).

**Readings of the planning statement.** The smallness in `LLPAt` is relative to the edge lattices,
`F_i ∈ ϖ^{c*}·𝓡(L″_i ⊂ L′)`, so that it bounds the pairings with the targets at `L′` (`pairE_mem_of_small`); the
planning scratch wrote `ϖ^{c*}·∇(mid)`, without the `ϖ^{−A_r}`. The depth `ϖ^{−t}` is part of the source and target
lattices, and `LLPAt` asks `F_i ∈ srcLat t L″_i`.
-/

namespace LocalLattice

open MvPolynomial WeylFock HermForms InertModel

open scoped Matrix Pointwise

noncomputable section

/-! ## Lattices of blocks, the normalised Fock form and duals -/

section Blocks

variable {β : Type} [Fintype β] [DecidableEq β] {k : ℕ} {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]

/-- **The `∇`-lattice of a family of `O`-lattices** `Λ_b`, one per block: the `F ∈ ∇_{Kf}` whose twist by basis
matrices of the `Λ_b` lies in `∇_O` (`InertModel.NablaT` is the case `Λ_b = σ^s(L_v) ⊗ O`). -/
def nablaB (lam : β → Fin k → ℤ) (Λ : β → Submodule O (Fin k → Kf)) : Set (Pol β k Kf) :=
  {F | F ∈ nabla Kf (fun b => natW (lam b)) ∧ ∃ C : β → Matrix (Fin k) (Fin k) Kf,
    (∀ b, IsBasisOf (Λ b) (C b)) ∧ twist lam C F ∈ (nablaInt (Oint O Kf) fun b => natW (lam b) : Set (Pol β k Kf))}

/-- **The `Δ`-lattice of a family of `O`-lattices**, as `nablaB` with `Δ_O` (`InertModel.DeltaT` is the case
`Λ_b = σ^s(L_v) ⊗ O`). -/
def deltaB (lam : β → Fin k → ℤ) (Λ : β → Submodule O (Fin k → Kf)) : Set (Pol β k Kf) :=
  {F | F ∈ nabla Kf (fun b => natW (lam b)) ∧ ∃ C : β → Matrix (Fin k) (Fin k) Kf,
    (∀ b, IsBasisOf (Λ b) (C b)) ∧ twist lam C F ∈ Delta (Oint O Kf) fun b => natW (lam b)}

/-- **`∇_Λ` in any basis**: membership in `nablaB` can be tested in any basis matrices of the blocks. -/
theorem mem_nablaB_iff {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) {F : Pol β k Kf} :
    F ∈ nablaB lam Λ ↔ F ∈ nabla Kf (fun b => natW (lam b)) ∧
      twist lam C F ∈ (nablaInt (Oint O Kf) fun b => natW (lam b) : Set (Pol β k Kf)) := by
  refine ⟨fun ⟨hF, C', hC', hD⟩ => ⟨hF, ?_⟩, fun h => ⟨h.1, C, hC, h.2⟩⟩
  choose U V hU hV hCU hUV using fun b => exists_mul_eq_of_isBasisOf (hC' b) (hC b)
  have e : twist lam C F = twist lam U (twist lam C' F) := by
    rw [twist_twist]
    exact congrArg (twist lam · F) (funext hCU)
  rw [e]
  exact twist_mem_nablaInt _ hU hV hUV hD

/-- **`Δ_Λ` in any basis**: membership in `deltaB` can be tested in any basis matrices of the blocks. -/
theorem mem_deltaB_iff {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) {F : Pol β k Kf} :
    F ∈ deltaB lam Λ ↔ F ∈ nabla Kf (fun b => natW (lam b)) ∧
      twist lam C F ∈ Delta (Oint O Kf) fun b => natW (lam b) := by
  refine ⟨fun ⟨hF, C', hC', hD⟩ => ⟨hF, ?_⟩, fun h => ⟨h.1, C, hC, h.2⟩⟩
  choose U V hU hV hCU hUV using fun b => exists_mul_eq_of_isBasisOf (hC' b) (hC b)
  have e : twist lam C F = twist lam U (twist lam C' F) := by
    rw [twist_twist]
    exact congrArg (twist lam · F) (funext hCU)
  rw [e]
  exact (twist_mem_Delta_iff _ hU hV hUV).2 hD

/-- **Moving block lattices**: if `C` is a basis of `Λ` and `h·C` one of `Λ'`, then the twist by a left inverse `h'`
of `h` maps `∇_Λ` into `∇_{Λ'}`. -/
theorem twist_mem_nablaB {lam : β → Fin k → ℤ} {Λ Λ' : β → Submodule O (Fin k → Kf)}
    {C h h' : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b))
    (hC' : ∀ b, IsBasisOf (Λ' b) (h b * C b)) (hh : ∀ b, h' b * h b = 1) {F : Pol β k Kf}
    (hF : F ∈ nablaB lam Λ) : twist lam h' F ∈ nablaB lam Λ' := by
  rw [mem_nablaB_iff hC] at hF
  rw [mem_nablaB_iff hC', twist_twist]
  refine ⟨twist_mem_nabla _ _ hF.1, ?_⟩
  have e : (fun b => h' b * (h b * C b)) = C := funext fun b => by rw [← Matrix.mul_assoc, hh, Matrix.one_mul]
  rw [e]
  exact hF.2

variable [CharZero Kf]

/-- **The normalised bilinear Fock form** `⟨F, G⟩ = fock(F, G)/κ`, `κ = fock(hw, hw)`, as a bilinear map: `Δ_O` is
the dual of `∇_O` for it (`WeylFock.Delta`). -/
def nf (lam : β → Fin k → ℤ) : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Kf :=
  LinearMap.mk₂ Kf (fun F G => fockWith (RingHom.id Kf) F G / algebraMap ℚ Kf (HermForms.kappa lam))
    (fun F F' G => by simp only [fock_add_left, add_div])
    (fun c F G => by simp only [fock_smul_left, smul_eq_mul, mul_div_assoc])
    (fun F G G' => by simp only [fock_add_right, add_div])
    (fun c F G => by simp only [fock_smul_right, smul_eq_mul, mul_div_assoc])

omit [DecidableEq β] in
/-- **The normalised Fock form**, unfolded. -/
theorem nf_apply (lam : β → Fin k → ℤ) (F G : Pol β k Kf) :
    nf lam F G = fockWith (RingHom.id Kf) F G / algebraMap ℚ Kf (HermForms.kappa lam) := rfl

/-- **Adjointness of twists**: `⟨twist_g F, G⟩ = ⟨F, twist_{gᵀ} G⟩` (`fock_lsub`). -/
theorem nf_twist (lam : β → Fin k → ℤ) (g : β → Matrix (Fin k) (Fin k) Kf) (F G : Pol β k Kf) :
    nf lam (twist lam g F) G = nf lam F (twist lam (fun b => (g b)ᵀ) G) := by
  have h : fockWith (RingHom.id Kf) (lsub g F) G = fockWith (RingHom.id Kf) F (lsub (fun b => (g b)ᵀ) G) := by
    simpa only [Matrix.transpose_transpose] using fock_lsub (fun b => (g b)ᵀ) F G
  simp only [nf_apply, twist, fock_C_mul_left, fock_C_mul_right, Matrix.det_transpose, h]

variable (O) in
/-- **The dual of a set** `S` for a bilinear form `B`: the `G ∈ ∇_{Kf}(ν)` with `B(F, G) ∈ O` for every `F ∈ S`. -/
def bdual (B : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Kf) (ν : β → Fin k → ℕ) (S : Set (Pol β k Kf)) :
    Submodule O (Pol β k Kf) where
  carrier := {G | G ∈ nabla Kf ν ∧ ∀ F ∈ S, B F G ∈ Oint O Kf}
  add_mem' {G G'} hG hG' :=
    ⟨add_mem hG.1 hG'.1, fun F hF => by rw [map_add]; exact add_mem (hG.2 F hF) (hG'.2 F hF)⟩
  zero_mem' := ⟨zero_mem _, fun F _ => by rw [map_zero]; exact zero_mem _⟩
  smul_mem' o G hG := by
    refine ⟨Submodule.smul_of_tower_mem _ o hG.1, fun F hF => ?_⟩
    rw [← algebraMap_smul Kf o G, map_smul, smul_eq_mul]
    exact mul_mem ⟨o, rfl⟩ (hG.2 F hF)

omit [Fintype β] [CharZero Kf] in
/-- **The dual of a lattice with a dual basis**: if `y` spans `∇_{Kf}(ν)` and `B(x_i, y_j) = δ_{ij}`, then the dual of
the `O`-span of `x` is the `O`-span of `y`. -/
theorem bdual_span {ι' : Type} [Fintype ι'] [DecidableEq ι'] (B : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Kf)
    {ν : β → Fin k → ℕ} {x y : ι' → Pol β k Kf} (hy : Submodule.span Kf (Set.range y) = nabla Kf ν)
    (hxy : ∀ i l, B (x i) (y l) = if i = l then 1 else 0) :
    bdual O B ν (Submodule.span O (Set.range x)) = Submodule.span O (Set.range y) := by
  apply le_antisymm
  · intro G hG
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Kf).1 (hy ▸ hG.1 : G ∈ Submodule.span Kf _)
    have hi : ∀ i, a i ∈ Oint O Kf := fun i => by
      have := hG.2 (x i) (Submodule.subset_span ⟨i, rfl⟩)
      simpa only [← ha, map_sum, map_smul, hxy, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true] using this
    choose o ho using fun i => RingHom.mem_range.1 (hi i)
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨o, ?_⟩
    rw [← ha]
    exact Finset.sum_congr rfl fun i _ => by rw [← algebraMap_smul Kf (o i), ho]
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    refine ⟨hy ▸ Submodule.subset_span ⟨l, rfl⟩, fun F hF => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hF
    simp only [← algebraMap_smul Kf (c _), map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, hxy, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact ⟨c l, rfl⟩

omit [Fintype β] [CharZero Kf] in
/-- **The dual on the left**: if `x` spans `∇_{Kf}(ν)` and `B(x_i, y_j) = δ_{ij}`, then the left dual of the `O`-span
of `y` (the dual for the flipped form) is the `O`-span of `x`. -/
theorem bdual_flip_span {ι' : Type} [Fintype ι'] [DecidableEq ι'] (B : Pol β k Kf →ₗ[Kf] Pol β k Kf →ₗ[Kf] Kf)
    {ν : β → Fin k → ℕ} {x y : ι' → Pol β k Kf} (hx : Submodule.span Kf (Set.range x) = nabla Kf ν)
    (hxy : ∀ i l, B (x i) (y l) = if i = l then 1 else 0) :
    bdual O B.flip ν (Submodule.span O (Set.range y)) = Submodule.span O (Set.range x) :=
  bdual_span B.flip hx fun l i => by rw [LinearMap.flip_apply, hxy]; exact if_congr eq_comm rfl rfl

omit [CharZero Kf] in
/-- **Twisting keeps spanning families of `∇`**: if `f` spans `∇_{Kf}(ν)`, so does its twist by invertible `g`. -/
theorem span_twist {lam : β → Fin k → ℤ} {g : β → Matrix (Fin k) (Fin k) Kf} (hg : ∀ b, IsUnit (g b).det)
    {ι' : Type} [Fintype ι'] {f : ι' → Pol β k Kf}
    (hf : Submodule.span Kf (Set.range f) = nabla Kf fun b => natW (lam b)) :
    Submodule.span Kf (Set.range fun i => twist lam g (f i)) = nabla Kf fun b => natW (lam b) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact twist_mem_nabla _ _ (hf ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro G hG
    have h1 : twist lam (fun b => (g b)⁻¹) G ∈ Submodule.span Kf (Set.range f) := hf ▸ twist_mem_nabla _ _ hG
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Kf).1 h1
    rw [← twist_twist_inv lam hg G, ← ha, twist_sum]
    simp only [twist_smul]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **`zb_j` is row-homogeneous of weight `zwt j`** over `Kf`. -/
theorem zbK_isWH (lam : β → Fin k → ℤ) (j : ZIdx lam) :
    IsWeightedHomogeneous (rowW β k) (zbK Kf lam j) (zwt lam j) :=
  fun {d} hd => zb_isWH lam j fun h => hd (by rw [zbK, coeff_map, h, map_zero])

/-- **`∇_Λ` is spanned by the twisted `zb`** (spanning): for a basis `C` of the blocks, `∇_Λ` is the `O`-span of the
`twist_{C⁻¹} zb_j` (`exists_eq_sum_zbK`). -/
theorem nablaB_eq_span {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) {Λ : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) :
    nablaB lam Λ = (Submodule.span O (Set.range fun j => twist lam (fun b => (C b)⁻¹) (zbK Kf lam j)) :
      Set (Pol β k Kf)) := by
  ext F
  rw [mem_nablaB_iff hC]
  simp only [SetLike.mem_coe]
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨-, hF⟩
    obtain ⟨c, hc⟩ := exists_eq_sum_zbK hF
    choose o ho using fun l => RingHom.mem_range.1 (c l).2
    refine ⟨o, ?_⟩
    rw [← twist_inv_twist lam (fun b => (hC b).1) F, hc, twist_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [twist_smul, ← ho, algebraMap_smul]
  · rintro ⟨o, rfl⟩
    refine ⟨Submodule.sum_mem _ fun l _ =>
      Submodule.smul_of_tower_mem _ _ (twist_mem_nabla _ _ (zbK_mem Kf hlam l)), ?_⟩
    rw [twist_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← algebraMap_smul Kf, twist_smul, twist_twist_inv lam fun b => (hC b).1]
    exact Submodule.smul_mem _ (⟨_, o l, rfl⟩ : Oint O Kf) (zbK_mem_nablaInt _ l)

/-- **`Δ_Λ` is spanned by the twisted dual basis**: for a basis `C` of the blocks, `Δ_Λ` is the `O`-span of the
`twist_{C⁻¹} zdual_j` (`mem_Delta_iff`). -/
theorem deltaB_eq_span {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) {Λ : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) :
    deltaB lam Λ = (Submodule.span O (Set.range fun j => twist lam (fun b => (C b)⁻¹) (zdualK Kf lam j)) :
      Set (Pol β k Kf)) := by
  ext F
  rw [mem_deltaB_iff hC, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨-, hD⟩
    obtain ⟨hn, hd⟩ := (mem_Delta_iff Kf lam (Oint O Kf) _).1 hD
    choose o ho using fun l => RingHom.mem_range.1 (hd l)
    refine ⟨o, ?_⟩
    rw [← twist_inv_twist lam (fun b => (hC b).1) F, eq_sum_dc hlam hn, twist_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [twist_smul, ← ho, algebraMap_smul]
  · rintro ⟨o, rfl⟩
    refine ⟨Submodule.sum_mem _ fun l _ =>
      Submodule.smul_of_tower_mem _ _ (twist_mem_nabla _ _ (zdualK_mem_nabla hlam l)), ?_⟩
    rw [twist_sum]
    refine Finset.sum_induction _ (· ∈ Delta (Oint O Kf) _) (fun a b ha hb => add_mem_Delta ha hb)
      ⟨zero_mem _, fun rows => by simp [fockWith]⟩ fun l _ => ?_
    rw [← algebraMap_smul Kf, twist_smul, twist_twist_inv lam fun b => (hC b).1]
    exact smul_mem_Delta (zdualK_mem_Delta hlam _ l) ⟨o l, rfl⟩

/-- **The twisted bases are dual**: `⟨twist_{C⁻¹} zb_i, twist_{Cᵀ} zdual_j⟩ = δ_{ij}` (`nf_twist`,
`fock_zdualK_zbK`). -/
theorem nf_twist_zbK_zdualK (lam : β → Fin k → ℤ) {C : β → Matrix (Fin k) (Fin k) Kf}
    (hC : ∀ b, IsUnit (C b).det) (i l : ZIdx lam) :
    nf lam (twist lam (fun b => (C b)⁻¹) (zbK Kf lam i)) (twist lam (fun b => (C b)ᵀ) (zdualK Kf lam l)) =
      if i = l then 1 else 0 := by
  rw [nf_twist, twist_twist]
  have e : (fun b => (C b)ᵀ * ((C b)⁻¹)ᵀ) = fun _ => (1 : Matrix (Fin k) (Fin k) Kf) := funext fun b => by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hC b), Matrix.transpose_one]
  have hκ : algebraMap ℚ Kf (HermForms.kappa lam) ≠ 0 := (map_ne_zero _).2 (kappa_pos lam).ne'
  rw [e, twist_one, nf_apply, fock_comm, fock_zdualK_zbK]
  by_cases h : i = l
  · subst h
    simp [(kappa_pos lam).ne']
  · simp [h, Ne.symm h]

/-- **A basis of `∇_Λ` with its dual family** (spanning): for a basis `C` of the blocks, `x_j = twist_{C⁻¹} zb_j` is a
`Kf`-basis of `∇_{Kf}` whose `O`-span is `∇_Λ`, and `y_j = twist_{Cᵀ} zdual_j` spans `∇_{Kf}` with
`⟨x_i, y_j⟩ = δ_{ij}`. -/
theorem nablaB_dualPair {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) {Λ : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) :
    LinearIndependent Kf (fun j => twist lam (fun b => (C b)⁻¹) (zbK Kf lam j)) ∧
      Submodule.span Kf (Set.range fun j => twist lam (fun b => (C b)⁻¹) (zbK Kf lam j)) =
        nabla Kf (fun b => natW (lam b)) ∧
      Submodule.span Kf (Set.range fun j => twist lam (fun b => (C b)ᵀ) (zdualK Kf lam j)) =
        nabla Kf (fun b => natW (lam b)) ∧
      nablaB lam Λ = (Submodule.span O (Set.range fun j => twist lam (fun b => (C b)⁻¹) (zbK Kf lam j)) :
        Set (Pol β k Kf)) :=
  ⟨linearIndependent_twist _ (fun b => (hC b).1) (linearIndependent_zbK Kf _),
    span_twist (fun b => (Matrix.isUnit_nonsing_inv_det _ (hC b).1)) (span_zbK Kf hlam),
    span_twist (fun b => by rw [Matrix.det_transpose]; exact (hC b).1) (span_zdualK Kf hlam),
    nablaB_eq_span hlam hC⟩

/-- **Duality** (the core of model fact 5): the Fock dual of `∇_Λ` is `Δ_{Λ'}` when the blocks of `Λ'` have the basis
matrices `(C⁻¹)ᵀ`, that is, `Λ'` is the dual lattice of `Λ` (`isBasisOf_dualLat`). -/
theorem bdual_nablaB {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) {Λ Λ' : β → Submodule O (Fin k → Kf)}
    {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b))
    (hC' : ∀ b, IsBasisOf (Λ' b) ((C b)⁻¹)ᵀ) :
    (bdual O (nf lam) (fun b => natW (lam b)) (nablaB lam Λ) : Set (Pol β k Kf)) = deltaB lam Λ' := by
  obtain ⟨-, -, hy, hx⟩ := nablaB_dualPair hlam hC
  rw [hx, bdual_span (nf lam) hy (nf_twist_zbK_zdualK lam fun b => (hC b).1), deltaB_eq_span hlam hC']
  have e : (fun b => (((C b)⁻¹)ᵀ)⁻¹) = fun b => (C b)ᵀ := funext fun b => by
    rw [Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact (hC b).1)]
  rw [e]

omit [Fintype β] [DecidableEq β] [CharZero Kf] in
/-- **Scaling into a span**: if `c·x_i ∈ span_O(y)` for every `i`, then `c·span_O(x) ⊆ span_O(y)`. -/
theorem smul_mem_span_range {ι' : Type} [Fintype ι'] {x y : ι' → Pol β k Kf} {c : Kf}
    (h : ∀ i, c • x i ∈ Submodule.span O (Set.range y)) {F : Pol β k Kf}
    (hF : F ∈ Submodule.span O (Set.range x)) : c • F ∈ Submodule.span O (Set.range y) := by
  obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hF
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← algebraMap_smul Kf (o i), smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (h i)

omit [Fintype β] [DecidableEq β] [CharZero Kf] in
/-- **Scaling a span**: for `c ≠ 0`, `c·F ∈ span_O(f)` iff `F ∈ span_O(c⁻¹·f)`. -/
theorem smul_mem_span_iff {ι' : Type} [Fintype ι'] {f : ι' → Pol β k Kf} {c : Kf} (hc : c ≠ 0)
    {F : Pol β k Kf} :
    c • F ∈ Submodule.span O (Set.range f) ↔ F ∈ Submodule.span O (Set.range fun i => c⁻¹ • f i) := by
  constructor
  · intro h
    have := smul_mem_span_range (c := c⁻¹) (y := fun i => c⁻¹ • f i)
      (fun i => Submodule.subset_span ⟨i, rfl⟩) h
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · exact smul_mem_span_range fun i => by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      exact Submodule.subset_span ⟨i, rfl⟩

omit [Fintype β] [DecidableEq β] [CharZero Kf] in
/-- **Scaling keeps `Kf`-spans**: for `c ≠ 0`, `span_{Kf}(c·f) = span_{Kf}(f)`. -/
theorem span_smul_range {ι' : Type} {f : ι' → Pol β k Kf} {c : Kf} (hc : c ≠ 0) :
    Submodule.span Kf (Set.range fun i => c • f i) = Submodule.span Kf (Set.range f) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨i, rfl⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : f i = c⁻¹ • (c • f i) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [Fintype β] [DecidableEq β] [CharZero Kf] in
/-- **Inverting an edge diagonal**: `diag(dg S c)⁻¹ = diag(dg S c⁻¹)`. -/
theorem inv_diag_dg (S : β → Finset (Fin k)) {c : Kf} (hc : c ≠ 0) (b : β) :
    (Matrix.diagonal (dg S c b))⁻¹ = Matrix.diagonal (dg S c⁻¹ b) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [dg]
  split_ifs <;> simp [hc]

/-- **The exponent of an edge twist on `zb_j`**: `Σ_b (|S|·λ_{b,k−1} + Σ_{i∈S} (zwt j)_{b,i})`, the power of `c` by
which the twist by `diag(c on S, 1 off S)` in every block multiplies `zb_j` (`twist_diag_zbK`). -/
def pexp (lam : β → Fin k → ℤ) (S : Finset (Fin k)) (j : ZIdx lam) : ℤ :=
  ∑ b, ((S.card : ℤ) * detShift (lam b) + ∑ i ∈ S, (zwt lam j b i : ℤ))

/-- **An edge twist scales `zb_j`** by `c^{pexp j}`: `zb_j` is row-homogeneous (`twist_diagonal_of_isWH`). -/
theorem twist_diag_zbK (lam : β → Fin k → ℤ) (S : Finset (Fin k)) {c : Kf} (hc : c ≠ 0) (j : ZIdx lam) :
    twist lam (fun b => Matrix.diagonal (dg (fun _ => S) c b)) (zbK Kf lam j) = c ^ pexp lam S j • zbK Kf lam j := by
  rw [twist_diagonal_of_isWH lam (zbK_isWH lam j), prod_dg hc]
  rfl

/-- **The exponent bound for `zb_j`**: `pexp j ≤ Σ_b Σ_{i<|S|} λ_{b,i}` for dominant weights. The weight part of
`zb_j` contains a nonzero bideterminant, of row weight `zwt j`, to which `exp_le` applies. -/
theorem pexp_le {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) (S : Finset (Fin k)) (j : ZIdx lam) :
    pexp lam S j ≤ ∑ b, ∑ i : Fin k with i.val < S.card, lam b i := by
  obtain ⟨rows, hrows, h0⟩ : ∃ rows : BRows β k (fun b => natW (lam b)),
      rowWt rows = zwt lam j ∧ bidet ℚ (fun b => natW (lam b)) rows ≠ 0 := by
    by_contra h
    push Not at h
    have hbot : nablaZw lam (zwt lam j) = ⊥ :=
      Submodule.span_eq_bot.2 fun x ⟨rows, hr, hx⟩ => hx ▸ h rows hr
    have hmem : zb lam j ∈ nablaZw lam (zwt lam j) := (Module.Free.chooseBasis ℤ (nablaZw lam j.1) j.2).2
    rw [hbot] at hmem
    exact (Module.Free.chooseBasis ℤ (nablaZw lam j.1)).ne_zero j.2 (Subtype.ext ((Submodule.mem_bot ℤ).1 hmem))
  have := exp_le hlam (fun _ => S) h0
  rw [hrows] at this
  exact this

end Blocks

/-! ## Dual lattices -/

section Dual

variable {k : ℕ}

/-- **The dual lattice** `N^∨ = {y : y·x ∈ R for every x ∈ N}` of an `R`-submodule `N` of `K^k`, for the standard dot
product. -/
def dualLat {R K : Type} [CommRing R] [Field K] [Algebra R K] (N : Submodule R (Fin k → K)) :
    Submodule R (Fin k → K) where
  carrier := {y | ∀ x ∈ N, y ⬝ᵥ x ∈ (algebraMap R K).range}
  add_mem' hy hy' x hx := by rw [add_dotProduct]; exact add_mem (hy x hx) (hy' x hx)
  zero_mem' x _ := by rw [zero_dotProduct]; exact zero_mem _
  smul_mem' r y hy x hx := by rw [smul_dotProduct, Algebra.smul_def]; exact mul_mem ⟨r, rfl⟩ (hy x hx)

/-- **The dual of the lattice spanned by the columns of `B`** is spanned by the columns of `(B⁻¹)ᵀ`: the dot products
of the columns of `(B⁻¹)ᵀ` and `B` are the entries of `B⁻¹B = 1`. -/
theorem dualLat_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {B : Matrix (Fin k) (Fin k) K}
    (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun l i => B i l)) =
      Submodule.span R (Set.range fun l i => (B⁻¹)ᵀ i l) := by
  have hdot : ∀ m l, (fun i => (B⁻¹)ᵀ i m) ⬝ᵥ (fun i => B i l) = if m = l then 1 else 0 := fun m l => by
    rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hB, Matrix.mul_apply]
    rfl
  apply le_antisymm
  · intro y hy
    have hz : ∀ l, y ⬝ᵥ (fun i => B i l) ∈ (algebraMap R K).range := fun l =>
      hy _ (Submodule.subset_span ⟨l, rfl⟩)
    choose c hc using fun l => RingHom.mem_range.1 (hz l)
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, ?_⟩
    have e : y = (y ᵥ* B) ᵥ* B⁻¹ := by rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
    conv_rhs => rw [e]
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Matrix.transpose_apply]
    simp only [Algebra.smul_def, hc]
    simp only [Matrix.vecMul, dotProduct]
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hdot]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [dotProduct_add]; exact add_mem hx hx'
    | smul a x _ hx => rw [dotProduct_smul, Algebra.smul_def]; exact mul_mem ⟨a, rfl⟩ hx

/-- **A basis of the dual lattice**: if `C` is a basis matrix of the `O`-lattice `Λ`, then `(C⁻¹)ᵀ` is one of
`Λ^∨`. -/
theorem isBasisOf_dualLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {Λ : Submodule O (Fin k → Kf)}
    {C : Matrix (Fin k) (Fin k) Kf} (hC : IsBasisOf Λ C) : IsBasisOf (dualLat Λ) (C⁻¹)ᵀ := by
  refine ⟨by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hC.1, ?_⟩
  rw [hC.2, dualLat_span hC.1]

/-- **Model fact 5 for block lattices**: the Fock dual of `∇_Λ` is `Δ_{Λ^∨}`, `Λ^∨` the dual lattices of the blocks
(`bdual_nablaB`, `isBasisOf_dualLat`). -/
theorem bdual_nablaB_dualLat {β : Type} [Fintype β] [DecidableEq β] {O Kf : Type} [CommRing O] [Field Kf]
    [Algebra O Kf] [CharZero Kf] {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b))
    {Λ : β → Submodule O (Fin k → Kf)} {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b)) :
    (bdual O (nf lam) (fun b => natW (lam b)) (nablaB lam Λ) : Set (Pol β k Kf)) =
      deltaB lam fun b => dualLat (Λ b) :=
  bdual_nablaB hlam hC fun b => isBasisOf_dualLat (hC b)

/-- **Ring maps commute with inverting matrices.** -/
theorem mapMatrix_inv {K K' : Type} [Field K] [Field K'] (f : K →+* K') {A : Matrix (Fin k) (Fin k) K}
    (hA : IsUnit A.det) : f.mapMatrix A⁻¹ = (f.mapMatrix A)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← map_mul, Matrix.mul_nonsing_inv _ hA, map_one])).symm

end Dual

/-! ## Comparing `Δ` and `∇`: the Gram constants -/

section Gram

variable {β : Type} [Fintype β] [DecidableEq β] {k : ℕ} {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf]

omit [Fintype β] [DecidableEq β] in
/-- **Integer polynomials have integer Fock products.** -/
theorem fock_mem_int {P Q : Pol β k ℚ} (hP : ∀ d, P.coeff d ∈ (Int.castRingHom ℚ).range)
    (hQ : ∀ d, Q.coeff d ∈ (Int.castRingHom ℚ).range) : fockWith (RingHom.id ℚ) P Q ∈ (Int.castRingHom ℚ).range :=
  Subring.sum_mem _ fun d _ => Subring.mul_mem _ (Subring.mul_mem _ (hP d) (hQ d))
    (Subring.prod_mem _ fun _ _ => natCast_mem _ _)

omit [DecidableEq β] in
/-- **`κ` is an integer**: `hw` is a bideterminant, with integer coefficients (`coeff_bidet_mem`). -/
theorem kappa_mem_int (lam : β → Fin k → ℤ) : HermForms.kappa lam ∈ (Int.castRingHom ℚ).range := by
  have hhw : hw ℚ (fun b => natW (lam b)) = bidet ℚ (fun b => natW (lam b)) fun _ s _ => Fin.castLE s.isLt := by
    simp [hw, bidet, Finset.prod_const]
  have hc : ∀ d, (hw ℚ (fun b => natW (lam b))).coeff d ∈ (Int.castRingHom ℚ).range := fun d =>
    hhw ▸ coeff_bidet_mem _ _ _ d
  exact fock_mem_int hc hc

/-- **The scaled Gram matrix is integral**: `κ·Gzb_{il} = fock(zb_i, zb_l)`, an integer (`coeff_zb_mem`). -/
theorem kappa_mul_Gzb_mem (lam : β → Fin k → ℤ) (i l : ZIdx lam) :
    HermForms.kappa lam * Gzb lam i l ∈ (Int.castRingHom ℚ).range := by
  have e : HermForms.kappa lam * Gzb lam i l = fockWith (RingHom.id ℚ) (zb lam i) (zb lam l) := by
    show _ * (_ / _) = _
    rw [mul_div_cancel₀ _ (kappa_pos lam).ne']
  rw [e]
  exact fock_mem_int (coeff_zb_mem lam i) (coeff_zb_mem lam l)

/-- **The scaled inverse Gram matrix is integral**: `det(κ·Gzb)·Γ = κ·adj(κ·Gzb)`, with integer entries. -/
theorem det_mul_Γ_mem (lam : β → Fin k → ℤ) (i l : ZIdx lam) :
    (HermForms.kappa lam • Gzb lam).det * Γ lam i l ∈ (Int.castRingHom ℚ).range := by
  set G' := HermForms.kappa lam • Gzb lam
  have h1 : Gzb lam * (HermForms.kappa lam • G'.adjugate) = G'.det • (1 : Matrix (ZIdx lam) (ZIdx lam) ℚ) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, Matrix.mul_adjugate]
  have h2 : G'.det • Γ lam = HermForms.kappa lam • G'.adjugate :=
    calc G'.det • Γ lam = Γ lam * (G'.det • (1 : Matrix (ZIdx lam) (ZIdx lam) ℚ)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = HermForms.kappa lam • G'.adjugate := by rw [← h1, ← Matrix.mul_assoc, Γ_mul_Gzb, Matrix.one_mul]
  have e := congrFun (congrFun h2 i) l
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  rw [e]
  refine Subring.mul_mem _ (kappa_mem_int lam) ?_
  choose z hz using fun i l => RingHom.mem_range.1 (kappa_mul_Gzb_mem lam i l)
  have hG : G' = (Int.castRingHom ℚ).mapMatrix (Matrix.of z) := by
    ext i l
    simp only [G', Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact (hz i l).symm
  rw [hG, ← RingHom.map_adjugate]
  exact ⟨_, rfl⟩

/-- **`κ·∇_Λ ⊆ Δ_Λ`**: `κ·zb_i = Σ_l κ·Gzb_{il}·zdual_l` (`zbK_eq`) with integer coefficients. -/
theorem smul_nablaB_subset_deltaB {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b))
    {Λ : β → Submodule O (Fin k → Kf)} {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b))
    {F : Pol β k Kf} (hF : F ∈ nablaB lam Λ) : algebraMap ℚ Kf (HermForms.kappa lam) • F ∈ deltaB lam Λ := by
  rw [nablaB_eq_span hlam hC, SetLike.mem_coe] at hF
  rw [deltaB_eq_span hlam hC, SetLike.mem_coe]
  refine smul_mem_span_range (fun i => ?_) hF
  rw [← twist_smul, zbK_eq, Finset.smul_sum, twist_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [smul_smul, ← map_mul, twist_smul]
  obtain ⟨z, hz⟩ := RingHom.mem_range.1 (kappa_mul_Gzb_mem lam i l)
  rw [← hz, Int.coe_castRingHom, map_intCast, ← map_intCast (algebraMap O Kf), algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **`det(κ·Gzb)·Δ_Λ ⊆ ∇_Λ`**: `zdual_i = Σ_l Γ_{il}·zb_l` (`zdualK_eq`) and `det(κ·Gzb)·Γ` is integral. -/
theorem smul_deltaB_subset_nablaB {lam : β → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b))
    {Λ : β → Submodule O (Fin k → Kf)} {C : β → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (Λ b) (C b))
    {F : Pol β k Kf} (hF : F ∈ deltaB lam Λ) :
    algebraMap ℚ Kf (HermForms.kappa lam • Gzb lam).det • F ∈ nablaB lam Λ := by
  rw [deltaB_eq_span hlam hC, SetLike.mem_coe] at hF
  rw [nablaB_eq_span hlam hC, SetLike.mem_coe]
  refine smul_mem_span_range (fun i => ?_) hF
  rw [← twist_smul, zdualK_eq, Finset.smul_sum, twist_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [smul_smul, ← map_mul, twist_smul]
  obtain ⟨z, hz⟩ := RingHom.mem_range.1 (det_mul_Γ_mem lam i l)
  rw [← hz, Int.coe_castRingHom, map_intCast, ← map_intCast (algebraMap O Kf), algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end Gram

/-! ## Tuples: spanning and duality (model facts 4 and 5) -/

section Tuples

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **Model fact 4 (spanning)**: for a lattice tuple `L`, `∇_L` is the `O`-span of a `Kf`-basis of `∇_{Kf}`, the
twisted `zb` of `WeylZForm` (`nablaB_dualPair`); so it is a free `O`-lattice of rank `dim ∇` in `∇_{Kf}`. -/
theorem exists_basis_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L : V → Submodule W (Fin k → Qq)} (hL : ∀ v, (L v).IsLattice Qq) :
    ∃ x : ZIdx (blockWt lam0) → Pol (V × Fin n') k Kf, LinearIndependent Kf x ∧
      Submodule.span Kf (Set.range x) = nabla Kf (fun b => natW (blockWt lam0 b)) ∧
      NablaT O ι σ lam0 L = (Submodule.span O (Set.range x) : Set (Pol (V × Fin n') k Kf)) := by
  obtain ⟨C, hC⟩ := exists_basis_tuple (O := O) hU hL
  obtain ⟨h1, h2, -, h4⟩ := nablaB_dualPair (antitone_blockWt hlam) hC
  exact ⟨_, h1, h2, h4⟩

omit [CharZero Kf] in
/-- **The blocks of the dual lattice**: if the columns of `B` span `L`, then `(ι σ^s(B)⁻¹)ᵀ` is a basis matrix of
`σ^s(L^∨) ⊗ O` (`dualLat_span`). -/
theorem isBasisOf_blk_dualLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) {L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det) (hL : L = Submodule.span W (Set.range fun l i => B i l)) :
    IsBasisOf (blk (O := O) ι σ s (dualLat L)) ((((ι.comp (σ ^ s).toRingHom).mapMatrix B)⁻¹)ᵀ) := by
  have hB' : IsUnit ((B⁻¹)ᵀ).det := by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hB
  have h := isBasisOf_blk (O := O) (L := dualLat L) hU s hB' (by rw [hL, dualLat_span hB])
  have e : (ι.comp (σ ^ s).toRingHom).mapMatrix ((B⁻¹)ᵀ) = (((ι.comp (σ ^ s).toRingHom).mapMatrix B)⁻¹)ᵀ := by
    rw [← mapMatrix_inv _ hB]
    rfl
  rwa [e] at h

/-- **Model fact 5 (duality)**: for a lattice tuple `L`, the Fock dual `∇_L^∨` of `∇_L` is exactly `Δ_{L^∨}`, the
`Δ`-lattice of the dual tuple `L^∨ = (L_v^∨)_v` (`bdual_nablaB`). With the comparison of `Δ_O` and `∇_O`
(`smul_nablaB_subset_deltaB`, `smul_deltaB_subset_nablaB`, or the sandwich), `∇_L^∨` and `∇_{L^∨}` agree up to the
Gram constants. -/
theorem bdual_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L : V → Submodule W (Fin k → Qq)} (hL : ∀ v, (L v).IsLattice Qq) :
    (bdual O (nf (blockWt lam0)) (fun b => natW (blockWt lam0 b)) (NablaT O ι σ lam0 L) :
      Set (Pol (V × Fin n') k Kf)) = DeltaT O ι σ lam0 fun v => dualLat (L v) := by
  choose B S _ hB hLB _ using fun w => exists_basis_edge hU (isEdge_refl (n' := n') (p := p) (hL w))
  exact bdual_nablaB (antitone_blockWt hlam) (fun b => isBasisOf_blk hU _ (hB b.1) (hLB b.1))
    fun b => isBasisOf_blk_dualLat hU _ (hB b.1) (hLB b.1)

/-- **Model fact 5, up to the Gram constants**: for a lattice tuple `L`, `κ·∇(L^∨) ⊆ ∇(L)^∨` and
`det(κ·Gzb)·∇(L)^∨ ⊆ ∇(L^∨)`, `κ = fock(hw, hw)` and `κ·Gzb` the integral Gram matrix of `zb` (both nonzero
integers, `kappa_mem_int`, `det_Gzb_ne_zero`): `∇(L)^∨ = Δ(L^∨)` (`bdual_NablaT`), compared with `∇(L^∨)` blockwise
(`smul_nablaB_subset_deltaB`, `smul_deltaB_subset_nablaB`). So the two agree up to `p^{e′}`,
`e′ = v_p(κ) + v_p(det(κ·Gzb))`. -/
theorem bdual_NablaT_compare (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L : V → Submodule W (Fin k → Qq)} (hL : ∀ v, (L v).IsLattice Qq) :
    (∀ F ∈ NablaT O ι σ lam0 (fun v => dualLat (L v)), algebraMap ℚ Kf (HermForms.kappa (blockWt lam0)) • F ∈
      bdual O (nf (blockWt lam0)) (fun b => natW (blockWt lam0 b)) (NablaT O ι σ lam0 L)) ∧
    ∀ G ∈ bdual O (nf (blockWt lam0)) (fun b => natW (blockWt lam0 b)) (NablaT O ι σ lam0 L),
      algebraMap ℚ Kf (HermForms.kappa (blockWt lam0) • Gzb (blockWt lam0)).det • G ∈
        NablaT O ι σ lam0 fun v => dualLat (L v) := by
  choose B S _ hB hLB _ using fun w => exists_basis_edge hU (isEdge_refl (n' := n') (p := p) (hL w))
  have hC' := fun b : V × Fin n' => isBasisOf_blk_dualLat (O := O) hU b.2 (hB b.1) (hLB b.1)
  have e := bdual_NablaT (O := O) hU hlam hL
  refine ⟨fun F hF => ?_, fun G hG => ?_⟩
  · rw [← SetLike.mem_coe, e]
    exact smul_nablaB_subset_deltaB (antitone_blockWt hlam) hC' hF
  · rw [← SetLike.mem_coe, e] at hG
    exact smul_deltaB_subset_nablaB (antitone_blockWt hlam) hC' hG

end Tuples

/-! ## The local lattice problem at one orbit -/

section Orbit

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {k n' : ℕ}

/-- **The block weights of one orbit**: block `((), s)` has weight `lamAt lam0 s`. -/
abbrev wt1 (lam0 : Fin n' → Fin k → ℤ) : Unit × Fin n' → Fin k → ℤ := blockWt fun _ : Unit => lam0

/-- **The shape of `∇` at one orbit**: `natW` of the block weights. -/
abbrev nu1 (lam0 : Fin n' → Fin k → ℤ) : Unit × Fin n' → Fin k → ℕ := fun b => natW (wt1 lam0 b)

/-- **`A_r = Σ_s Σ_{i<r} λ_{s,i}`** at one orbit (`topSum`). -/
abbrev topA (r : ℕ) (lam0 : Fin n' → Fin k → ℤ) : ℤ := topSum r (fun _ : Unit => lam0) ()

variable (Kf) in
/-- **The dimension of `V = ∇_{Kf}`** at one orbit. -/
abbrev dimV (lam0 : Fin n' → Fin k → ℤ) : ℕ := Module.finrank Kf (nabla Kf (nu1 lam0))

variable (O) in
/-- **`∇(L)` at one orbit**: the `∇`-lattice of the lattice `L` (`NablaT` of the one-orbit tuple). -/
abbrev nab (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : Fin n' → Fin k → ℤ) (L : Submodule W (Fin k → Qq)) :
    Set (Pol (Unit × Fin n') k Kf) :=
  NablaT O ι σ (fun _ : Unit => lam0) fun _ => L

/-- **The midpoint block** of an edge `L″ ⊂ L` at position `s`: `σ^s(L″)⊗O + ϖ·σ^s(L)⊗O`. -/
def midBlk (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (s : ℕ) (L'' L : Submodule W (Fin k → Qq)) :
    Submodule O (Fin k → Kf) :=
  blk ι σ s L'' ⊔ Ideal.span {ϖ} • blk ι σ s L

/-- **`∇` at the midpoint** of an edge `L″ ⊂ L`: the `∇`-lattice of the midpoint blocks. -/
abbrev nabMid (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (Unit × Fin n') k Kf) :=
  nablaB (wt1 lam0) fun b => midBlk ι σ ϖ b.2 L'' L

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **`∇` at the midpoint, unfolded.** -/
theorem nabMid_eq (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) :
    nabMid ι σ ϖ lam0 L'' L = nablaB (wt1 lam0) fun b => midBlk ι σ ϖ b.2 L'' L := rfl

/-- **The edge lattice** `𝓡(L″ ⊂ L) = ϖ^{−A_r}·∇(mid)` of an edge of type `r`: the `F` with `ϖ^{A_r}F` in the
`∇`-lattice of the midpoint. -/
def edgeLat (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (r : ℕ) (lam0 : Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (Unit × Fin n') k Kf) :=
  {F | algebraMap O Kf ϖ ^ topA r lam0 • F ∈ nabMid ι σ ϖ lam0 L'' L}

/-- **The pairing** `pairE(F, G) = ⟨p^{A_r}F, G⟩`, the normalised bilinear Fock form scaled by `p^{A_r}`. -/
def pairE (p r : ℕ) (lam0 : Fin n' → Fin k → ℤ) :
    Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf →ₗ[Kf] Kf :=
  ((p : Kf) ^ topA r lam0) • nf (wt1 lam0)

/-- **The dual edge lattice** `𝓡′(L″ ⊂ L)`: the `pairE`-dual of `𝓡(L″ ⊂ L)` in `∇_{Kf}`, that is
`ϖ^{−A_r}·∇(mid)^∨`. -/
def edgeDual (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Submodule O (Pol (Unit × Fin n') k Kf) :=
  bdual O (pairE p r lam0) (nu1 lam0) (edgeLat ι σ ϖ r lam0 L'' L)

/-- **The source lattice at depth `t`** of `L″`: `ϖ^{−t}∇(L″) ∩ ⋂_{L″ ⊂ L′} 𝓡(L″ ⊂ L′)`, over the edges of type `r`
out of `L″`. -/
def srcLat (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t : ℕ)
    (L'' : Submodule W (Fin k → Qq)) : Set (Pol (Unit × Fin n') k Kf) :=
  (algebraMap O Kf ϖ ^ t)⁻¹ • nab O ι σ lam0 L'' ∩
    ⋂ (L' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L'), edgeLat ι σ ϖ r lam0 L'' L'

/-- **The target lattice at depth `t`** of `L`: `ϖ^{−t}∇(L)^∨ ∩ ⋂_{L″ ⊂ L} 𝓡′(L″ ⊂ L)`, over the edges of type `r`
into `L` (`∇(L)^∨` the normalised Fock dual, so `ϖ^{−t}∇(L)^∨` is the dual of `ϖ^t∇(L)`). -/
def tgtLat (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t : ℕ)
    (L : Submodule W (Fin k → Qq)) : Submodule O (Pol (Unit × Fin n') k Kf) :=
  bdual O (nf (wt1 lam0)) (nu1 lam0) (algebraMap O Kf ϖ ^ t • nab O ι σ lam0 L) ⊓
    ⨅ (L'' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L), edgeDual p r ι σ ϖ lam0 L'' L

/-- **The local lattice problem** `LLP(t, D, κ, c*)` at the lattice `L`: there are edges `L″_i ⊂ L` of type `r` and
vectors `F_i` in the source lattices at depth `t` of the `L″_i`, `ϖ^{c*}`-small on the other edges out of the `L″_i`
(in `ϖ^{c*}·𝓡(L″_i ⊂ L′)` for `L′ ≠ L`), whose pairings `G ↦ pairE(F_i, G)` against the target lattice of `L` have a
`p^D`-left inverse on a free part of rank at least `(1 − κ)·dim V`: an `O`-linear `u : O^n → tgtLat(L)` and an
`O`-matrix `A` with `Σ_i A_{a,i}·pairE(F_i, u(x)) = p^D·x_a`. -/
def LLPAt (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t D : ℕ) (κ : ℝ)
    (cStar : ℕ) (L : Submodule W (Fin k → Qq)) : Prop :=
  ∃ (M : ℕ) (e : Fin M → Submodule W (Fin k → Qq)) (F : Fin M → Pol (Unit × Fin n') k Kf),
    (∀ i, IsEdge (n' := n') p r (e i) L) ∧ (∀ i, F i ∈ srcLat p r ι σ ϖ lam0 t (e i)) ∧
    (∀ i (L' : Submodule W (Fin k → Qq)), IsEdge (n' := n') p r (e i) L' → L' ≠ L →
      F i ∈ (algebraMap O Kf ϖ ^ cStar) • edgeLat ι σ ϖ r lam0 (e i) L') ∧
    ∃ n : ℕ, (1 - κ) * (dimV Kf lam0 : ℝ) ≤ n ∧
      ∃ (u : (Fin n → O) →ₗ[O] tgtLat p r ι σ ϖ lam0 t L) (A : Matrix (Fin n) (Fin M) O),
        ∀ (x : Fin n → O) (a : Fin n),
          ∑ i, algebraMap O Kf (A a i) * pairE p r lam0 (F i) (u x) = algebraMap O Kf ((p : O) ^ D * x a)

variable (W) in
/-- **The exceptional fraction** `κ(t, D)`: the least `κ ≥ 0` for which the local lattice problem holds at every
lattice. -/
def kappa (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t D cStar : ℕ) : ℝ :=
  sInf {κ : ℝ | 0 ≤ κ ∧ ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq → LLPAt p r ι σ ϖ lam0 t D κ cStar L}

end Orbit

/-! ## Edges: bases of the midpoint, the adapted basis and the edge lattices (model facts 1–3) -/

section Edge

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **`p = ϖ²` in `Kf`.** -/
theorem castK_eq_sq (hU : Unram p n' W Qq O Kf ι σ j ϖ) : (p : Kf) = algebraMap O Kf ϖ ^ 2 := by
  rw [← map_pow, hU.sq, map_natCast]

/-- **`ϖ ≠ 0` in `Kf`.** -/
theorem varpiK_ne_zero (hU : Unram p n' W Qq O Kf ι σ j ϖ) : algebraMap O Kf ϖ ≠ 0 := by
  have := hU.frac_O
  exact (map_ne_zero_iff _ (IsFractionRing.injective O Kf)).2 hU.unif_O.ne_zero

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Nonnegative integer powers of elements of `O` lie in `O`.** -/
theorem algebraMap_zpow_eq (c : O) {m : ℤ} (hm : 0 ≤ m) :
    algebraMap O Kf c ^ m = algebraMap O Kf (c ^ m.toNat) := by
  rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg hm]

/-- **The blocks of the lower lattice of an edge**: if the columns of `B·diag(p on S)` span `L″`, then
`ι σ^s(B)·diag(p on S)` is a basis matrix of `σ^s(L″) ⊗ O`. -/
theorem isBasisOf_blk_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) {L'' : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} {S : Finset (Fin k)} (hB : IsUnit B.det)
    (hL'' : L'' = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1) i l)) :
    IsBasisOf (blk (O := O) ι σ s L'')
      ((ι.comp (σ ^ s).toRingHom).mapMatrix B * Matrix.diagonal fun i => if i ∈ S then (p : Kf) else 1) := by
  have hdet : IsUnit (B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    refine hB.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
    split_ifs
    · exact hU.cast_ne_zero
    · exact one_ne_zero
  convert isBasisOf_blk (O := O) hU s hdet hL'' using 1
  rw [map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal _), Matrix.diagonal_map (map_zero _)]
  congr 2
  funext i
  split_ifs <;> simp

/-- **The midpoint blocks of an edge**: if the columns of `B` span `L` and those of `B·diag(p on S)` span `L″`, then
`ι σ^s(B)·diag(ϖ on S)` is a basis matrix of `σ^s(L″)⊗O + ϖ·σ^s(L)⊗O`: with `c_l` the columns of `ι σ^s(B)`, the
sum is spanned by the `p·c_l`, `ϖ·c_l` (`l ∈ S`) and the `c_l`, `ϖ·c_l` (`l ∉ S`), and `p = ϖ²`. -/
theorem isBasisOf_midBlk (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) {L'' L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} {S : Finset (Fin k)} (hB : IsUnit B.det)
    (hL : L = Submodule.span W (Set.range fun l i => B i l))
    (hL'' : L'' = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1) i l)) :
    IsBasisOf (midBlk ι σ ϖ s L'' L)
      ((ι.comp (σ ^ s).toRingHom).mapMatrix B * Matrix.diagonal fun i => if i ∈ S then algebraMap O Kf ϖ else 1) := by
  have h1 := isBasisOf_blk (O := O) hU s hB hL
  have h2 := isBasisOf_blk_edge (O := O) hU s hB hL''
  have hϖ := varpiK_ne_zero hU
  set C := (ι.comp (σ ^ s).toRingHom).mapMatrix B
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine h1.1.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
    split_ifs
    · exact hϖ
    · exact one_ne_zero
  rw [midBlk, h2.2]
  simp only [Matrix.mul_diagonal]
  -- the columns, as `O`-multiples of the columns `c_l` of `C`
  have hp : ∀ l, (fun i => C i l * if l ∈ S then (p : Kf) else 1) =
      if l ∈ S then ϖ • (ϖ • fun i => C i l) else fun i => C i l := fun l => by
    split_ifs
    · funext i
      simp [Algebra.smul_def, castK_eq_sq hU]
      ring
    · funext i
      simp
  have hm : ∀ l, (fun i => C i l * if l ∈ S then algebraMap O Kf ϖ else 1) =
      if l ∈ S then ϖ • fun i => C i l else fun i => C i l := fun l => by
    split_ifs <;> funext i <;> simp [Algebra.smul_def, mul_comm]
  have hcol : ∀ l, (fun i => C i l) ∈ blk (O := O) ι σ s L := fun l => h1.2 ▸ Submodule.subset_span ⟨l, rfl⟩
  have hgm : ∀ l, (fun i => C i l * if l ∈ S then algebraMap O Kf ϖ else 1) ∈
      Submodule.span O (Set.range fun l i => C i l * if l ∈ S then algebraMap O Kf ϖ else 1) :=
    fun l => Submodule.subset_span ⟨l, rfl⟩
  have hgp : ∀ l, (fun i => C i l * if l ∈ S then (p : Kf) else 1) ∈
      Submodule.span O (Set.range fun l i => C i l * if l ∈ S then (p : Kf) else 1) :=
    fun l => Submodule.subset_span ⟨l, rfl⟩
  apply le_antisymm
  · refine sup_le (Submodule.span_le.2 ?_) (Submodule.smul_le.2 fun a ha n hn => ?_)
    · rintro _ ⟨l, rfl⟩
      have := hgm l
      beta_reduce
      rw [SetLike.mem_coe, hp]
      rw [hm] at this
      split_ifs at this ⊢ with hl
      · exact Submodule.smul_mem _ _ this
      · exact this
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [mul_smul]
      refine Submodule.smul_mem _ c ?_
      rw [h1.2] at hn
      induction hn using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        have := hgm l
        rw [hm] at this
        split_ifs at this with hl
        · exact this
        · exact Submodule.smul_mem _ _ this
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    beta_reduce
    rw [SetLike.mem_coe, hm]
    split_ifs with hl
    · exact Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) (hcol l))
    · refine Submodule.mem_sup_left ?_
      have := hgp l
      rw [hp] at this
      simpa [hl] using this

variable [CharZero Kf]

/-- **Model fact 3 (adapted basis)**: for an edge `L″ ⊂ L` of type `r` and dominant weights there are a `Kf`-basis
`x_i` of `V = ∇_{Kf}` and integers `π_i ≤ A_r` with `∇(L″) = span_O(x_i)`, `∇(L) = span_O(p^{π_i}x_i)` and
`∇(mid) = span_O(ϖ^{π_i}x_i)`. In an edge basis (`exists_basis_edge`) the blocks of `L`, `L″` and the midpoint have
the basis matrices `C`, `C·diag(p on S)` and `C·diag(ϖ on S)`; the twist by `diag(c on S)` scales `zb_i` by
`c^{π_i}`, `π_i = pexp i` (`twist_diag_zbK`), so `x_i = twist_{(C·diag(p))⁻¹} zb_i` works (`nablaB_eq_span`), and
`π_i ≤ A_r` is the bound of `exp_le` (`pexp_le`). -/
theorem exists_adapted_basis (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    ∃ (x : ZIdx (wt1 lam0) → Pol (Unit × Fin n') k Kf) (π : ZIdx (wt1 lam0) → ℤ),
      LinearIndependent Kf x ∧ Submodule.span Kf (Set.range x) = nabla Kf (nu1 lam0) ∧
      nab O ι σ lam0 L'' = (Submodule.span O (Set.range x) : Set (Pol (Unit × Fin n') k Kf)) ∧
      nab O ι σ lam0 L = (Submodule.span O (Set.range fun i => (p : Kf) ^ π i • x i) :
        Set (Pol (Unit × Fin n') k Kf)) ∧
      nabMid ι σ ϖ lam0 L'' L = (Submodule.span O (Set.range fun i => algebraMap O Kf ϖ ^ π i • x i) :
        Set (Pol (Unit × Fin n') k Kf)) ∧
      ∀ i, π i ≤ topA r lam0 := by
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
  -- the twist by `(C·D_c)⁻¹` of `zb_i` is `c^{−π_i}` times the twist by `C⁻¹`
  have key : ∀ {c : Kf}, c ≠ 0 → ∀ i, twist (wt1 lam0) (fun b => (C b * D c b)⁻¹) (zbK Kf (wt1 lam0) i) =
      c ^ (-pexp (wt1 lam0) S i) • twist (wt1 lam0) (fun b => (C b)⁻¹) (zbK Kf (wt1 lam0) i) := by
    intro c hc i
    have e : (fun b => (C b * D c b)⁻¹) = fun b => D c⁻¹ b * (C b)⁻¹ := funext fun b => by
      rw [Matrix.mul_inv_rev, inv_diag_dg _ hc]
    rw [e, ← twist_twist, twist_diag_zbK _ _ (inv_ne_zero hc), twist_smul, inv_zpow', ]
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
  obtain ⟨h1, h2, -, h4⟩ := nablaB_dualPair hlam' hC''
  refine ⟨x, π, h1, h2, h4, ?_, ?_, fun i => ?_⟩
  · rw [show nab O ι σ lam0 L = nablaB (wt1 lam0) fun b => blk ι σ b.2 L from rfl, nablaB_eq_span hlam' hC]
    simp only [hxL]
  · rw [nabMid_eq, nablaB_eq_span hlam' hCm]
    simp only [hxm]
  · have := pexp_le hlam' S i
    rwa [sum_blockWt_eq_topSum (fun _ : Unit => lam0) (S := fun _ => S) (v := ()) (r := r) (by simp [hS])] at this

omit [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **The lower `∇`-lattice scaled into the midpoint**: `ϖ^{A_r}·span_O(x_i) ⊆ span_O(ϖ^{π_i}x_i)`, as `π_i ≤ A_r`. -/
theorem smul_mem_span_of_le {β' : Type} [Fintype β'] {ι' : Type} [Fintype ι'] {x : ι' → Pol β' k Kf}
    {π : ι' → ℤ} {A : ℤ} (hϖ : algebraMap O Kf ϖ ≠ 0) (hπ : ∀ i, π i ≤ A) (c : ℤ → Kf)
    (hc : ∀ i, c (π i) = algebraMap O Kf ϖ ^ π i) {F : Pol β' k Kf}
    (hF : F ∈ Submodule.span O (Set.range x)) :
    algebraMap O Kf ϖ ^ A • F ∈ Submodule.span O (Set.range fun i => c (π i) • x i) := by
  refine smul_mem_span_range (fun i => ?_) hF
  have e : algebraMap O Kf ϖ ^ A • x i = (ϖ ^ (A - π i).toNat) • (c (π i) • x i) := by
    rw [← algebraMap_smul Kf (ϖ ^ (A - π i).toNat), ← algebraMap_zpow_eq _ (sub_nonneg.2 (hπ i)), hc, smul_smul,
      ← zpow_add₀ hϖ, sub_add_cancel]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Model fact 1, source side**: `∇(L″) ⊆ 𝓡(L″ ⊂ L)` for an edge of type `r` and dominant weights: in the adapted
basis, `ϖ^{A_r}·x_i = ϖ^{A_r − π_i}·(ϖ^{π_i}x_i)` with `A_r − π_i ≥ 0`. -/
theorem nab_subset_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) : nab O ι σ lam0 L'' ⊆ edgeLat ι σ ϖ r lam0 L'' L := by
  obtain ⟨x, π, -, -, hx'', -, hxm, hπ⟩ := exists_adapted_basis hU hlam he
  intro F hF
  rw [hx'', SetLike.mem_coe] at hF
  show _ ∈ nabMid ι σ ϖ lam0 L'' L
  rw [hxm, SetLike.mem_coe]
  exact smul_mem_span_of_le (varpiK_ne_zero hU) hπ (fun m => algebraMap O Kf ϖ ^ m) (fun _ => rfl) hF

/-- **The midpoint scaled into the upper lattice**: `ϖ^{A_r}·∇(mid) ⊆ ∇(L)`, so `p^{A_r}·𝓡(L″ ⊂ L) ⊆ ∇(L)`. -/
theorem pow_smul_mem_nab_of_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L) :
    (p : Kf) ^ topA r lam0 • F ∈ nab O ι σ lam0 L := by
  obtain ⟨x, π, -, -, -, hxL, hxm, hπ⟩ := exists_adapted_basis hU hlam he
  have hϖ := varpiK_ne_zero hU
  have hF' : algebraMap O Kf ϖ ^ topA r lam0 • F ∈
      Submodule.span O (Set.range fun i => algebraMap O Kf ϖ ^ π i • x i) := by
    rw [← SetLike.mem_coe, ← hxm]
    exact hF
  have hpA : (p : Kf) ^ topA r lam0 = algebraMap O Kf ϖ ^ topA r lam0 * algebraMap O Kf ϖ ^ topA r lam0 := by
    rw [castK_eq_sq hU, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hϖ]
    congr 1
    push_cast
    ring
  rw [hxL, SetLike.mem_coe, hpA, mul_smul]
  refine smul_mem_span_range (fun i => ?_) hF'
  have e : algebraMap O Kf ϖ ^ topA r lam0 • algebraMap O Kf ϖ ^ π i • x i =
      (ϖ ^ (topA r lam0 - π i).toNat) • ((p : Kf) ^ π i • x i) := by
    rw [← algebraMap_smul Kf (ϖ ^ (topA r lam0 - π i).toNat), ← algebraMap_zpow_eq _ (sub_nonneg.2 (hπ i)),
      smul_smul, smul_smul, castK_eq_sq hU,
      ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hϖ, ← zpow_add₀ hϖ]
    congr 2
    push_cast
    ring
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **`pairE` against the plain form**: `pairE(F, G) = ⟨p^{A_r}F, G⟩`. -/
theorem pairE_apply (p r : ℕ) (lam0 : Fin n' → Fin k → ℤ) (F G : Pol (Unit × Fin n') k Kf) :
    pairE p r lam0 F G = nf (wt1 lam0) ((p : Kf) ^ topA r lam0 • F) G := by
  simp only [pairE, LinearMap.smul_apply, map_smul]

/-- **Model fact 1, target side**: `∇(L)^∨ ⊆ 𝓡′(L″ ⊂ L)` for an edge of type `r` and dominant weights: for
`F ∈ 𝓡(L″ ⊂ L)`, `pairE(F, G) = ⟨p^{A_r}F, G⟩` and `p^{A_r}F ∈ ∇(L)` (`pow_smul_mem_nab_of_edgeLat`). -/
theorem bdual_nab_le_edgeDual (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    bdual O (nf (wt1 lam0)) (nu1 lam0) (nab O ι σ lam0 L) ≤ edgeDual p r ι σ ϖ lam0 L'' L :=
  fun G hG => ⟨hG.1, fun F hF => by
    rw [pairE_apply]
    exact hG.2 _ (pow_smul_mem_nab_of_edgeLat hU hlam he hF)⟩

/-- **Model fact 2 (perfect pairing)**: for an edge of type `r` and dominant weights, `𝓡(L″ ⊂ L)` and
`𝓡′(L″ ⊂ L)` are the `O`-spans of `pairE`-dual families `x_i`, `y_i`, both spanning `∇_{Kf}`: `x_i = ϖ^{−A_r}·x′_i`
and `y_i = ϖ^{−A_r}·y′_i` for the dual pair `x′_i = twist_{C⁻¹} zb_i`, `y′_i = twist_{Cᵀ} zdual_i` of the midpoint
(`nablaB_dualPair`, `nf_twist_zbK_zdualK`), as `p^{A_r}·ϖ^{−2A_r} = 1`. -/
theorem edgeLat_dualPair (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    ∃ x y : ZIdx (wt1 lam0) → Pol (Unit × Fin n') k Kf,
      edgeLat ι σ ϖ r lam0 L'' L = (Submodule.span O (Set.range x) : Set (Pol (Unit × Fin n') k Kf)) ∧
      edgeDual p r ι σ ϖ lam0 L'' L = Submodule.span O (Set.range y) ∧
      (∀ i l, pairE p r lam0 (x i) (y l) = if i = l then 1 else 0) ∧
      Submodule.span Kf (Set.range x) = nabla Kf (nu1 lam0) ∧
      Submodule.span Kf (Set.range y) = nabla Kf (nu1 lam0) := by
  obtain ⟨B, S, -, hB, hLB, hL''B⟩ := exists_basis_edge hU he
  have hϖ := varpiK_ne_zero hU
  set Cm : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf := fun b =>
    (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B * Matrix.diagonal fun i => if i ∈ S then algebraMap O Kf ϖ else 1
  have hCm : ∀ b, IsBasisOf (midBlk ι σ ϖ b.2 L'' L) (Cm b) := fun b => isBasisOf_midBlk hU _ hB hLB hL''B
  have hlam' : ∀ b, Antitone (wt1 lam0 b) := antitone_blockWt fun _ => hlam
  obtain ⟨-, h2, h3, h4⟩ := nablaB_dualPair hlam' hCm
  set c := (algebraMap O Kf ϖ ^ topA r lam0)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (zpow_ne_zero _ hϖ)
  refine ⟨fun i => c • twist (wt1 lam0) (fun b => (Cm b)⁻¹) (zbK Kf (wt1 lam0) i),
    fun i => c • twist (wt1 lam0) (fun b => (Cm b)ᵀ) (zdualK Kf (wt1 lam0) i), ?_, ?_, ?_,
    by rw [span_smul_range hc, h2], by rw [span_smul_range hc, h3]⟩
  · ext F
    show _ ∈ nabMid ι σ ϖ lam0 L'' L ↔ _
    rw [nabMid_eq, h4, SetLike.mem_coe, SetLike.mem_coe, smul_mem_span_iff (zpow_ne_zero _ hϖ)]
  · have hxy : ∀ i l, pairE p r lam0 (c • twist (wt1 lam0) (fun b => (Cm b)⁻¹) (zbK Kf (wt1 lam0) i))
        (c • twist (wt1 lam0) (fun b => (Cm b)ᵀ) (zdualK Kf (wt1 lam0) l)) = if i = l then 1 else 0 := by
      intro i l
      rw [pairE_apply, smul_smul, map_smul, map_smul, LinearMap.smul_apply, nf_twist_zbK_zdualK _ fun b => (hCm b).1,
        smul_eq_mul, smul_eq_mul]
      have e : c * ((p : Kf) ^ topA r lam0 * c) = 1 := by
        rw [castK_eq_sq hU, ← zpow_natCast, ← zpow_mul]
        simp only [c]
        rw [show ((2 : ℕ) : ℤ) * topA r lam0 = topA r lam0 + topA r lam0 by push_cast; ring, zpow_add₀ hϖ]
        field_simp
      rw [← mul_assoc, e, one_mul]
    rw [edgeDual, show edgeLat ι σ ϖ r lam0 L'' L = (Submodule.span O (Set.range fun i =>
      c • twist (wt1 lam0) (fun b => (Cm b)⁻¹) (zbK Kf (wt1 lam0) i)) : Set (Pol (Unit × Fin n') k Kf)) from ?_]
    · exact bdual_span _ (by rw [span_smul_range hc, h3]) hxy
    · ext F
      show _ ∈ nabMid ι σ ϖ lam0 L'' L ↔ _
      rw [nabMid_eq, h4, SetLike.mem_coe, SetLike.mem_coe, smul_mem_span_iff (zpow_ne_zero _ hϖ)]
  · intro i l
    rw [pairE_apply, smul_smul, map_smul, map_smul, LinearMap.smul_apply, nf_twist_zbK_zdualK _ fun b => (hCm b).1,
      smul_eq_mul, smul_eq_mul]
    have e : c * ((p : Kf) ^ topA r lam0 * c) = 1 := by
      rw [castK_eq_sq hU, ← zpow_natCast, ← zpow_mul]
      simp only [c]
      rw [show ((2 : ℕ) : ℤ) * topA r lam0 = topA r lam0 + topA r lam0 by push_cast; ring, zpow_add₀ hϖ]
      field_simp
    rw [← mul_assoc, e, one_mul]

/-- **Model fact 2, the duals**: `𝓡′(e)` is the `pairE`-dual of `𝓡(e)` (its definition), and `𝓡(e)` is the left
`pairE`-dual of `𝓡′(e)` (`edgeLat_dualPair`, `bdual_flip_span`). -/
theorem bdual_edgeDual (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    (bdual O (pairE (Kf := Kf) p r lam0).flip (nu1 lam0) (edgeDual p r ι σ ϖ lam0 L'' L) :
      Set (Pol (Unit × Fin n') k Kf)) =
      edgeLat ι σ ϖ r lam0 L'' L := by
  obtain ⟨x, y, hx, hy, hxy, hsx, -⟩ := edgeLat_dualPair hU hlam he
  rw [hy, bdual_flip_span _ hsx hxy, hx]

/-- **`∇(L″)` lies in its source lattices** (model fact 1): `∇(L″) ⊆ ϖ^{−t}∇(L″)`, and `∇(L″) ⊆ 𝓡(L″ ⊂ L′)` for every
edge out of `L″` (`nab_subset_edgeLat`). -/
theorem nab_subset_srcLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r t : ℕ} {L'' : Submodule W (Fin k → Qq)} (hL'' : L''.IsLattice Qq) :
    nab O ι σ lam0 L'' ⊆ srcLat p r ι σ ϖ lam0 t L'' := by
  intro F hF
  refine ⟨?_, Set.mem_iInter₂.2 fun L' he => nab_subset_edgeLat hU hlam he hF⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero (pow_ne_zero _ (varpiK_ne_zero hU))), inv_inv]
  exact smul_mem_NablaT hU (fun _ => hL'') ⟨ϖ ^ t, by rw [map_pow]⟩ hF

/-- **`∇(L)^∨` lies in its target lattices** (model fact 1): `∇(L)^∨ ⊆ ϖ^{−t}∇(L)^∨`, and `∇(L)^∨ ⊆ 𝓡′(L″ ⊂ L)` for
every edge into `L` (`bdual_nab_le_edgeDual`). -/
theorem bdual_nab_le_tgtLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r t : ℕ} {L : Submodule W (Fin k → Qq)} :
    bdual O (nf (wt1 lam0)) (nu1 lam0) (nab O ι σ lam0 L) ≤ tgtLat p r ι σ ϖ lam0 t L := by
  intro G hG
  refine Submodule.mem_inf.2 ⟨⟨hG.1, fun F' hF' => ?_⟩,
    Submodule.mem_iInf _ |>.2 fun L'' => Submodule.mem_iInf _ |>.2 fun he => bdual_nab_le_edgeDual hU hlam he hG⟩
  obtain ⟨F, hF, rfl⟩ := Set.mem_smul_set.1 hF'
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← map_pow]
  exact mul_mem ⟨_, rfl⟩ (hG.2 F hF)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Sources pair integrally with targets**: for an edge `L″ ⊂ L`, `F` in a source lattice of `L″` and `G` in a target
lattice of `L`, `pairE(F, G) ∈ O` (`F ∈ 𝓡(L″ ⊂ L)`, `G ∈ 𝓡′(L″ ⊂ L)`). So the left side of the equation of `LLPAt` is
an `O`-combination of elements of `O`. -/
theorem pairE_mem_of_src_tgt {lam0 : Fin n' → Fin k → ℤ} {r t t' : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) {F G : Pol (Unit × Fin n') k Kf} (hF : F ∈ srcLat p r ι σ ϖ lam0 t L'')
    (hG : G ∈ tgtLat p r ι σ ϖ lam0 t' L) : pairE p r lam0 F G ∈ Oint O Kf :=
  ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hG).2 L'') he).2 F
    (Set.mem_iInter₂.1 hF.2 L he)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **What smallness means**: if `F ∈ ϖ^c·𝓡(L″ ⊂ L′)` and `G` lies in a target lattice of `L′`, then
`pairE(F, G) ∈ ϖ^c·O`: the vectors of `LLPAt` pair `ϖ^{c*}`-small with the targets at the other ends `L′ ≠ L` of the
edges out of their sources. -/
theorem pairE_mem_of_small {lam0 : Fin n' → Fin k → ℤ} {r t c : ℕ} {L'' L' : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L') {F G : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ (algebraMap O Kf ϖ ^ c) • edgeLat ι σ ϖ r lam0 L'' L') (hG : G ∈ tgtLat p r ι σ ϖ lam0 t L') :
    ∃ a ∈ Oint O Kf, pairE p r lam0 F G = algebraMap O Kf ϖ ^ c * a := by
  obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 hF
  refine ⟨pairE p r lam0 F₁ G, ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1
    (Submodule.mem_inf.1 hG).2 L'') he).2 F₁ hF₁, ?_⟩
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

end Edge

/-! ## The exceptional fraction -/

section Kappa

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {ϖ : O} {p r k n' : ℕ} {lam0 : Fin n' → Fin k → ℤ} {t D cStar : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The local lattice problem with `κ = 1`** holds at every lattice: no edges, and a free part of rank `0`. -/
theorem llpAt_one (L : Submodule W (Fin k → Qq)) : LLPAt p r ι σ ϖ lam0 t D 1 cStar L :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 0, by simp, 0, 0,
    fun _ a => a.elim0⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The local lattice problem is monotone in `κ`.** -/
theorem llpAt_mono {κ κ' : ℝ} (h : κ ≤ κ') {L : Submodule W (Fin k → Qq)}
    (hL : LLPAt p r ι σ ϖ lam0 t D κ cStar L) : LLPAt p r ι σ ϖ lam0 t D κ' cStar L := by
  obtain ⟨M, e, F, he, hs, hm, n, hn, rest⟩ := hL
  exact ⟨M, e, F, he, hs, hm, n, le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) hn, rest⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The set defining `kappa` contains `1`.** -/
theorem one_mem_kappaSet :
    (1 : ℝ) ∈ {κ : ℝ | 0 ≤ κ ∧ ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
      LLPAt p r ι σ ϖ lam0 t D κ cStar L} :=
  ⟨zero_le_one, fun L _ => llpAt_one L⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`κ ≥ 0`.** -/
theorem kappa_nonneg : 0 ≤ kappa W p r ι σ ϖ lam0 t D cStar :=
  le_csInf ⟨1, one_mem_kappaSet⟩ fun _ h => h.1

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`κ ≤ 1`.** -/
theorem kappa_le_one : kappa W p r ι σ ϖ lam0 t D cStar ≤ 1 :=
  csInf_le ⟨0, fun _ h => h.1⟩ one_mem_kappaSet

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`κ` is at most any fraction for which the local lattice problem holds at every lattice.** -/
theorem kappa_le {κ : ℝ} (h0 : 0 ≤ κ)
    (h : ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq → LLPAt p r ι σ ϖ lam0 t D κ cStar L) :
    kappa W p r ι σ ϖ lam0 t D cStar ≤ κ :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨h0, h⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Above `κ` the local lattice problem holds** at every lattice. -/
theorem llpAt_of_kappa_lt {κ : ℝ} (h : kappa W p r ι σ ϖ lam0 t D cStar < κ) {L : Submodule W (Fin k → Qq)}
    (hL : L.IsLattice Qq) : LLPAt p r ι σ ϖ lam0 t D κ cStar L := by
  obtain ⟨κ', ⟨-, hκ'⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨1, one_mem_kappaSet⟩ h
  exact llpAt_mono hlt.le (hκ' L hL)

end Kappa

/-! ## Moving lattices: one lattice suffices (model fact 6) -/

section Move

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

variable (W) in
/-- **`g ∈ GL_k(Qq)` moves a lattice**: `N ↦ g·N`. -/
abbrev gmap (g : GL (Fin k) Qq) (N : Submodule W (Fin k → Qq)) : Submodule W (Fin k → Qq) :=
  N.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)

/-- **The blocks of `g`**: `ι σ^s(g)` at the block `((), s)`. -/
abbrev gblk (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (g : GL (Fin k) Qq) (b : Unit × Fin n') : Matrix (Fin k) (Fin k) Kf :=
  (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix (g : Matrix (Fin k) (Fin k) Qq)

/-- **`g` moves sources**: the twist by the blocks of `g⁻¹` (as `Level.actF`), mapping `∇(L)` onto `∇(gL)`. -/
abbrev mvS (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq)
    (F : Pol (Unit × Fin n') k Kf) : Pol (Unit × Fin n') k Kf :=
  twist (wt1 lam0) (gblk ι σ g⁻¹) F

/-- **`g` moves targets**: the twist by the transposed blocks of `g`, the contragredient of `mvS`. -/
def mvT (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq) :
    Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf where
  toFun := twist (wt1 lam0) fun b => (gblk ι σ g b)ᵀ
  map_add' := twist_add _ _
  map_smul' := twist_smul _ _

omit [CharZero Kf] in
/-- **The blocks of `g⁻¹` invert those of `g`.** -/
theorem gblk_inv_mul (g : GL (Fin k) Qq) (b : Unit × Fin n') : gblk ι σ g⁻¹ b * gblk ι σ g b = 1 := by
  simp only [gblk, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

omit [CharZero Kf] in
/-- **The blocks of `g` invert those of `g⁻¹`.** -/
theorem gblk_mul_inv (g : GL (Fin k) Qq) (b : Unit × Fin n') : gblk ι σ g b * gblk ι σ g⁻¹ b = 1 := by
  simp only [gblk, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]

omit [CharZero Kf] in
/-- **`mvS g` undoes `mvS g⁻¹`.** -/
theorem mvS_mvS_inv (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq) (F : Pol (Unit × Fin n') k Kf) :
    mvS ι σ lam0 g (mvS ι σ lam0 g⁻¹ F) = F := by
  simp only [mvS, twist_twist, inv_inv]
  rw [show (fun b => gblk ι σ g b * gblk ι σ g⁻¹ b) = fun _ => (1 : Matrix (Fin k) (Fin k) Kf) from
    funext (gblk_mul_inv g), twist_one]

omit [CharZero Kf] in
/-- **`mvT`, unfolded.** -/
theorem mvT_apply (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq) (G : Pol (Unit × Fin n') k Kf) :
    mvT ι σ lam0 g G = twist (wt1 lam0) (fun b => (gblk ι σ g b)ᵀ) G := rfl

/-- **The moves keep the normalised Fock form**: `⟨mvS g F, mvT g G⟩ = ⟨F, G⟩` (`nf_twist`). -/
theorem nf_mv (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq) (F G : Pol (Unit × Fin n') k Kf) :
    nf (wt1 lam0) (mvS ι σ lam0 g F) (mvT ι σ lam0 g G) = nf (wt1 lam0) F G := by
  rw [mvS, nf_twist, mvT_apply, twist_twist]
  rw [show (fun b => (gblk ι σ g b)ᵀ * (gblk ι σ g⁻¹ b)ᵀ) = fun _ => (1 : Matrix (Fin k) (Fin k) Kf) from
    funext fun b => by rw [← Matrix.transpose_mul, gblk_inv_mul, Matrix.transpose_one], twist_one]

/-- **The moves keep the pairing**: `pairE(mvS g F, mvT g G) = pairE(F, G)`. -/
theorem pairE_mv (p r : ℕ) (lam0 : Fin n' → Fin k → ℤ) (g : GL (Fin k) Qq) (F G : Pol (Unit × Fin n') k Kf) :
    pairE p r lam0 (mvS ι σ lam0 g F) (mvT ι σ lam0 g G) = pairE p r lam0 F G := by
  rw [pairE_apply, pairE_apply, mvS, ← twist_smul, ← mvS, nf_mv]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **`g` undoes `g⁻¹` on lattices.** -/
theorem gmap_gmap_inv (g : GL (Fin k) Qq) (N : Submodule W (Fin k → Qq)) : gmap W g (gmap W g⁻¹ N) = N := by
  simpa only [inv_inv] using map_map_inv g⁻¹ N

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **`g⁻¹` undoes `g` on lattices.** -/
theorem gmap_inv_gmap (g : GL (Fin k) Qq) (N : Submodule W (Fin k → Qq)) : gmap W g⁻¹ (gmap W g N) = N :=
  map_map_inv g N

omit [CharZero Kf] in
/-- **The blocks of `g·L`**: if the columns of `B` span `L`, then `ι σ^s(g)·ι σ^s(B)` is a basis matrix of
`σ^s(gL) ⊗ O`. -/
theorem isBasisOf_blk_gmap (hU : Unram p n' W Qq O Kf ι σ j ϖ) (g : GL (Fin k) Qq) (b : Unit × Fin n')
    {L : Submodule W (Fin k → Qq)} {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det)
    (hL : L = Submodule.span W (Set.range fun l i => B i l)) :
    IsBasisOf (blk (O := O) ι σ b.2 (gmap W g L)) (gblk ι σ g b * (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B) := by
  rw [gblk, ← map_mul]
  exact isBasisOf_blk hU _ (by rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units _).mul hB) (map_span_cols _ hL)

omit [CharZero Kf] in
/-- **`g` moves `∇(L)` into `∇(gL)`** (`twist_mem_nablaB`). -/
theorem mvS_mem_nab (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq) {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ nab O ι σ lam0 L) : mvS ι σ lam0 g F ∈ nab O ι σ lam0 (gmap W g L) := by
  obtain ⟨B, -, -, hB, hLB, -⟩ := exists_basis_edge hU (isEdge_refl (n' := n') (p := p) hL)
  exact twist_mem_nablaB (fun b => isBasisOf_blk hU _ hB hLB) (fun b => isBasisOf_blk_gmap hU g b hB hLB)
    (gblk_inv_mul g) hF

omit [CharZero Kf] in
/-- **`g` moves `∇(mid)` into `∇(g·mid)`** for an edge (`isBasisOf_midBlk`, `twist_mem_nablaB`). -/
theorem mvS_mem_nabMid (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ nabMid ι σ ϖ lam0 L'' L) : mvS ι σ lam0 g F ∈ nabMid ι σ ϖ lam0 (gmap W g L'') (gmap W g L) := by
  obtain ⟨B, S, -, hB, hLB, hL''B⟩ := exists_basis_edge hU he
  have hgB : IsUnit ((g : Matrix (Fin k) (Fin k) Qq) * B).det := by
    rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units _).mul hB
  have hgL'' : gmap W g L'' = Submodule.span W (Set.range fun l i =>
      ((g : Matrix (Fin k) (Fin k) Qq) * B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1) i l) := by
    have := map_span_cols g hL''B
    rw [← Matrix.mul_assoc] at this
    exact this
  refine twist_mem_nablaB (fun b => isBasisOf_midBlk hU _ hB hLB hL''B) (fun b => ?_) (gblk_inv_mul g) hF
  have := isBasisOf_midBlk (ϖ := ϖ) hU b.2 hgB (map_span_cols _ hLB) hgL''
  rwa [map_mul, Matrix.mul_assoc] at this

omit [CharZero Kf] in
/-- **`g` moves `𝓡(L″ ⊂ L)` into `𝓡(gL″ ⊂ gL)`.** -/
theorem mvS_mem_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L) :
    mvS ι σ lam0 g F ∈ edgeLat ι σ ϖ r lam0 (gmap W g L'') (gmap W g L) := by
  show _ ∈ nabMid ι σ ϖ lam0 _ _
  rw [mvS, ← twist_smul, ← mvS]
  exact mvS_mem_nabMid hU g he hF

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **`g` moves edges to edges** (`isEdge_map`). -/
theorem isEdge_gmap (g : GL (Fin k) Qq) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) : IsEdge (n' := n') p r (gmap W g L'') (gmap W g L) :=
  isEdge_map g he

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **`g` moves the edges out of `L″` onto those out of `gL″`**: an edge `gL″ ⊂ L′` is `g` of the edge
`L″ ⊂ g⁻¹L′`. -/
theorem isEdge_gmap_inv {g : GL (Fin k) Qq} {r : ℕ} {L'' L' : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r (gmap W g L'') L') : IsEdge (n' := n') p r L'' (gmap W g⁻¹ L') := by
  have := isEdge_gmap g⁻¹ he
  rwa [gmap_inv_gmap] at this

omit [CharZero Kf] in
/-- **`g` moves the source lattice of `L″` into that of `gL″`.** -/
theorem mvS_mem_srcLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r t : ℕ} {L'' : Submodule W (Fin k → Qq)} (hL'' : L''.IsLattice Qq) {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ srcLat p r ι σ ϖ lam0 t L'') : mvS ι σ lam0 g F ∈ srcLat p r ι σ ϖ lam0 t (gmap W g L'') := by
  have hc : (algebraMap O Kf ϖ ^ t)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (varpiK_ne_zero hU))
  obtain ⟨h1, h2⟩ := hF
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc, inv_inv] at h1
  refine ⟨?_, Set.mem_iInter₂.2 fun L' he' => ?_⟩
  · rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc, inv_inv, mvS, ← twist_smul, ← mvS]
    exact mvS_mem_nab hU g hL'' h1
  · have he₁ := isEdge_gmap_inv he'
    have := mvS_mem_edgeLat hU g he₁ (Set.mem_iInter₂.1 h2 _ he₁)
    rwa [gmap_gmap_inv] at this

/-- **`g` moves the target lattice of `L` into that of `gL`**: the pairings are kept (`nf_mv`, `pairE_mv`), and `g⁻¹`
moves the sources at `gL` back. -/
theorem mvT_mem_tgtLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r t : ℕ} {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq) {G : Pol (Unit × Fin n') k Kf}
    (hG : G ∈ tgtLat p r ι σ ϖ lam0 t L) : mvT ι σ lam0 g G ∈ tgtLat p r ι σ ϖ lam0 t (gmap W g L) := by
  rw [tgtLat, Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢
  obtain ⟨h1, h2⟩ := hG
  have hn : mvT ι σ lam0 g G ∈ nabla Kf (nu1 lam0) := twist_mem_nabla _ _ h1.1
  refine ⟨⟨hn, fun F' hF' => ?_⟩, fun L₂ => Submodule.mem_iInf _ |>.2 fun he₂ => ⟨hn, fun F hF => ?_⟩⟩
  · obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 hF'
    have h0 := mvS_mem_nab hU g⁻¹ (isLattice_map g hL) hF₁
    rw [gmap_inv_gmap] at h0
    rw [← mvS_mvS_inv (ι := ι) (σ := σ) lam0 g F₁, mvS, ← twist_smul, ← mvS, nf_mv]
    exact h1.2 _ (Set.smul_mem_smul_set h0)
  · have he₁ : IsEdge (n' := n') p r (gmap W g⁻¹ L₂) L := by
      have := isEdge_gmap g⁻¹ he₂
      rwa [gmap_inv_gmap] at this
    have h0 := mvS_mem_edgeLat hU g⁻¹ he₂ hF
    rw [gmap_inv_gmap] at h0
    rw [← mvS_mvS_inv (ι := ι) (σ := σ) lam0 g F, pairE_mv]
    exact (Submodule.mem_iInf _ |>.1 (h2 _) he₁).2 _ h0

/-- **`g` moves the local lattice problem at `L` to `gL`**: move the edges, the vectors `F_i` by `mvS g`, and compose
`u` with `mvT g`; the pairings, hence the matrix `A`, are unchanged. -/
theorem llpAt_gmap (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r t D cStar : ℕ} {κ : ℝ} {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq)
    (h : LLPAt p r ι σ ϖ lam0 t D κ cStar L) : LLPAt p r ι σ ϖ lam0 t D κ cStar (gmap W g L) := by
  obtain ⟨M, e, F, he, hsrc, hsmall, n, hn, u, A, hA⟩ := h
  refine ⟨M, fun i => gmap W g (e i), fun i => mvS ι σ lam0 g (F i), fun i => isEdge_map g (he i),
    fun i => mvS_mem_srcLat hU g (he i).2.1 (hsrc i), fun i L' he' hne => ?_, n, hn,
    LinearMap.codRestrict _ (((mvT ι σ lam0 g).restrictScalars O).comp ((tgtLat p r ι σ ϖ lam0 t L).subtype.comp u))
      (fun x => mvT_mem_tgtLat hU g hL (u x).2), A, fun x a => ?_⟩
  · have he₁ := isEdge_gmap_inv he'
    have hne₁ : gmap W g⁻¹ L' ≠ L := fun h => hne (by rw [← h, gmap_gmap_inv])
    obtain ⟨F₁, hF₁, hF⟩ := Set.mem_smul_set.1 (hsmall i _ he₁ hne₁)
    have := mvS_mem_edgeLat hU g he₁ hF₁
    rw [gmap_gmap_inv] at this
    show mvS ι σ lam0 g (F i) ∈ _ • edgeLat ι σ ϖ r lam0 (gmap W g (e i)) L'
    rw [← hF, mvS, twist_smul, ← mvS]
    exact Set.smul_mem_smul_set this
  · rw [← hA x a]
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (fun z => algebraMap O Kf (A a i) * z) (pairE_mv p r lam0 g (F i) (u x))

omit [CharZero Kf] in
/-- **`GL_k(Qq)` is transitive on lattices**: the matrix `B'·B⁻¹` moves the lattice spanned by the columns of `B` to
that of `B'`. -/
theorem exists_gmap_eq (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L L' : Submodule W (Fin k → Qq)}
    (hL : L.IsLattice Qq) (hL' : L'.IsLattice Qq) : ∃ g : GL (Fin k) Qq, gmap W g L = L' := by
  obtain ⟨B, -, -, hB, hLB, -⟩ := exists_basis_edge hU (isEdge_refl (n' := n') (p := p) hL)
  obtain ⟨B', -, -, hB', hLB', -⟩ := exists_basis_edge hU (isEdge_refl (n' := n') (p := p) hL')
  set g := Matrix.nonsingInvUnit (B' * B⁻¹)
    (by rw [Matrix.det_mul]; exact hB'.mul (Matrix.isUnit_nonsing_inv_det _ hB))
  refine ⟨g, (map_span_cols g hLB).trans ?_⟩
  rw [hLB']
  have e : (g : Matrix (Fin k) (Fin k) Qq) * B = B' := by
    rw [show (g : Matrix (Fin k) (Fin k) Qq) = B' * B⁻¹ from rfl, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB,
      Matrix.mul_one]
  rw [e]

/-- **Model fact 6 (one lattice suffices)**: the local lattice problem at one lattice gives it at every lattice
(`exists_gmap_eq`, `llpAt_gmap`). -/
theorem llpAt_of_llpAt (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t D cStar : ℕ} {κ : ℝ}
    {L₀ L : Submodule W (Fin k → Qq)} (hL₀ : L₀.IsLattice Qq) (hL : L.IsLattice Qq)
    (h : LLPAt p r ι σ ϖ lam0 t D κ cStar L₀) : LLPAt p r ι σ ϖ lam0 t D κ cStar L := by
  obtain ⟨g, rfl⟩ := exists_gmap_eq hU hL₀ hL
  exact llpAt_gmap hU g hL₀ h

/-- **`κ` at one lattice**: `kappa` is the least `κ ≥ 0` with the local lattice problem at any one lattice `L₀`. -/
theorem kappa_eq (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t D cStar : ℕ}
    {L₀ : Submodule W (Fin k → Qq)} (hL₀ : L₀.IsLattice Qq) :
    kappa W p r ι σ ϖ lam0 t D cStar = sInf {κ : ℝ | 0 ≤ κ ∧ LLPAt p r ι σ ϖ lam0 t D κ cStar L₀} := by
  rw [kappa]
  congr 1
  ext κ
  exact and_congr_right fun _ => ⟨fun h => h L₀ hL₀, fun h L hL => llpAt_of_llpAt hU hL₀ hL h⟩

end Move

end

end LocalLattice
