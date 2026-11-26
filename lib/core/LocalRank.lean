import LocalLattice

/-!
# Local ranks: good systems at the edges and the assembly of the local lattice problem

The shared frame of the two local theorems of the gain (L5 and L6), at one orbit of an inert prime `p` in the setting
`Unram` of `InertModel`, on the edge lattices `𝓡`, `𝓡′`, the pairing `pairE` and the local lattice problem `LLPAt` of
`LocalLattice`. Both theorems are proved edge by edge, and this module turns the per-edge statements into `LLPAt`.

**Good systems.** At an edge `L″ ⊂ L` of type `r`, at depth `t` and conductor `c`:
* the source family (`SrcFam`) is the source lattice of `L″` cut down to the vectors `ϖ^c`-small on the other edges
  out of `L″` (`F ∈ ϖ^c·𝓡(L″ ⊂ L′)` for `L′ ≠ L`), as for the vectors `F_i` of `LLPAt`;
* the target family (`TgtFam`) is the target lattice of `L` cut down to the vectors `ϖ^c`-small on the other edges
  into `L` (`G ∈ ϖ^c·𝓡′(L₁ ⊂ L)` for `L₁ ≠ L″`);
* a good system of size `n` (`GoodSys`) is `n` sources `x_i`, `n` targets `y_m`, a `z ≠ 0` with `z ∣ p^D` and an
  `O`-matrix `M` with `Σ_m pairE(x_i, y_m)·M_{ml} = z·δ_{il}`;
* the per-edge rank (`RankAll`) asks for a good system of size at least `X` at every edge of type `r`. It keeps what
  `LLPAt` forgets: the smallness of the targets and the block structure edge by edge.

`nEdges p r L` is the number of edges of type `r` into `L`.

**Main results.**
* *Assembly* (`llpAt_of_rankAll`): the per-edge rank `X` with `(1 − κ)·dim V ≤ #edges·X` and `c ≥ 2D + 1` gives
  `LLPAt(t, D, κ, c)` at every lattice. The second form (`goodSys_of_primitive`, the one of L6): sources tested by the
  target family on every primitive coefficient vector, up to divisors of `p^D`, carry a good system with `z = p^D`.
* *Transport* (`goodSys_transport`): good systems move between any two edges of the same type, as `GL_k(Qq)` is
  transitive on them (`exists_gmap_edge`); the smallness of the targets moves by `mvT_mem_edgeDual`, the target-side
  analogue of `mvS_mem_edgeLat`.
* *Upper bound* (`goodSys_card_le`): a system at one edge, with targets only in `𝓡′(L″ ⊂ L)`, has
  `#edges·n ≤ dim V`.
* *Edges are planes* (`edgeEquivPlane`, `outEdgeEquivPlane`): the edges of type `r ≤ k` into `L` are the subspaces of
  dimension `k − r` of `L/pL ≅ F_q^k` over `W/p` (for `r = 1` the hyperplanes), those out of `L″` the subspaces of
  dimension `r` of `M/pM`, `M = p⁻¹L″`. So there are as many edges out of a lattice as into one
  (`ncard_outEdges`), `#edges ≥ q^{r(k−r)}` (`nEdges_ge`) and `#edges·(q − 1) = q^k − 1` for `r = 1`
  (`nEdges_one`), `q = p^{n'}`.
* *Smith splitting* (`smith_split`): if `Σ_j A_j = z·1` over a discrete valuation ring, each `A_j` has a part
  `P_j·A_j·Q_j = z·1` of size `ν_j`, with `Σ_j ν_j ≥ n`.
* *Good rank* (`goodRank_eq_smith`): the largest family `x_i, y_i` with `xᵢᵀ·G·y_l = z_i·δ_{il}`, `z_i ∣ π^D`, for
  `G = U·diag(d)·V`, has size `#{i : d_i ∣ π^D}`.

**The routes.** The assembly takes as the `F_i` the sources of the good systems at the edges `e ⊂ L`, all cut to
size `⌈X⌉`, and as targets the `Y = y·M`. The Gram matrix is `z_e·1` on the block of `e` and `ϖ^c`-small off the
blocks: the targets at `e′ ≠ e` are `ϖ^c`-small on `𝓡′(e)`, and the sources at `e` lie in `𝓡(e)`. As `p = ϖ²` and
`c ≥ 2D + 1`, it is `diag(z) + p^D·𝔪`, which has a `p^D`-left inverse `A` (`exists_gram_inv`): after `diag(p^D/z)`
it is `p^D` times a matrix that is `1` modulo `𝔪` (`exists_mul_eq_smul_one`). Then `u(x) = Σ_l x_l·Y_l` and `A`
give `LLPAt` (`llpAt_of_gram`). The upper bound transports the system to every edge out of `L″`, fixing `L″`, and
runs the same Gram argument with the smallness of the sources, so the `#edges·n` sources are independent. Edges and
planes correspond through the image in `L/pL`, the index being `q^{codim}` (third isomorphism theorem,
`card_quot_plane`; `card_plane` for `L/L″`). The planes are counted by fibring the independent `m`-tuples of `F_q^k`
(`card_linearIndependent`) over their spans (`card_subspace_mul`), and dimension and codimension are exchanged by
the annihilator in the dual (`card_subspace_compl`). The Smith lemmas use Mathlib's Smith normal form of a submodule
of `R^n` (`Submodule.smithNormalForm`): the splitting with Nakayama, the good rank through `B·C = c·1` implying
`#rows(B) ≤ #columns(B)` (`card_le_of_mul_eq_smul_one`), the primitive tests through the coordinate functionals of a
Smith basis, which are primitive (`smul_mem_of_primitive`).

**Readings of the planning statements.** The dominance of the weights is not needed by the assembly nor by the
transport (they use `srcLat ⊆ 𝓡` and `tgtLat ⊆ 𝓡′` by definition); the upper bound uses it only for `dim V < ∞`, and
there `z ≠ 0` follows from `z ∣ p^D`. These hypotheses are dropped.
-/

namespace LocalRank

open MvPolynomial WeylFock HermForms InertModel LocalLattice

open scoped Matrix Pointwise

noncomputable section

/-! ## A near-diagonal matrix over a local ring -/

section Algebra

/-- **A near-diagonal matrix has a `P`-left inverse** over a local ring: if `G = diag(z) + P·H` with `H` in the
maximal ideal and every `z_i ∣ P`, then `A·G = P·1` for some `A`. With `P = z_i q_i`, `diag(q)·G = P·(1 + diag(q)·H)`,
and `1 + diag(q)·H` is invertible: its determinant is `1` modulo the maximal ideal. -/
theorem exists_mul_eq_smul_one {R : Type*} [CommRing R] [IsLocalRing R] {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I R) (z : I → R) {P : R} (hz : ∀ i, z i ∣ P)
    (hG : ∀ i l, ∃ h ∈ IsLocalRing.maximalIdeal R, G i l = (if i = l then z i else 0) + P * h) :
    ∃ A : Matrix I I R, A * G = P • 1 := by
  choose q hq using hz
  choose H hHm hH using hG
  set K : Matrix I I R := 1 + Matrix.diagonal q * Matrix.of H
  have hK : IsUnit K.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have e : (IsLocalRing.residue R).mapMatrix K = 1 := by
      ext i l
      simp [K, Matrix.one_apply, (IsLocalRing.residue_eq_zero_iff _).2 (hHm i l)]
    rw [e, Matrix.det_one]
    exact one_ne_zero
  have hQG : Matrix.diagonal q * G = P • K := by
    ext i l
    simp only [Matrix.diagonal_mul, hH, K, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.of_apply]
    split_ifs with h
    · subst h
      rw [hq i]
      ring
    · ring
  exact ⟨K⁻¹ * Matrix.diagonal q, by rw [Matrix.mul_assoc, hQG, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hK]⟩

/-- **A `c`-left-invertible product through `K` has at most `|K|` rows**: if `B·C = c·1` over a domain (`c ≠ 0`),
`B : m × K`, then `|m| ≤ |K|`: the independent `c·e_l` lie in the span of the `|K|` columns of `B`. -/
theorem card_le_of_mul_eq_smul_one {R : Type*} [CommRing R] [IsDomain R] {m K : Type*} [Fintype m] [Fintype K]
    [DecidableEq m] (B : Matrix m K R) (C : Matrix K m R) {c : R} (hc : c ≠ 0) (h : B * C = c • 1) :
    Fintype.card m ≤ Fintype.card K := by
  classical
  let v : m → m → R := fun l => c • Pi.single l 1
  have hv : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrFun hg l
    simp [v, Finset.sum_apply, Pi.single_apply, hc] at this
    exact this
  have hvB : Set.range v ≤ Submodule.span R (Set.range fun a i => B i a) := by
    rintro _ ⟨l, rfl⟩
    have e : v l = ∑ a, (C *ᵥ Pi.single l 1) a • fun i => B i a := by
      have := congrArg (· *ᵥ (Pi.single l (1 : R))) h
      simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [show v l = c • Pi.single l 1 from rfl, ← this]
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 := linearIndependent_le_span' v hv _ hvB
  rw [Cardinal.mk_fintype, Nat.cast_le] at h1
  exact h1.trans (Fintype.card_range_le _)

end Algebra

/-! ## Splitting a sum `Σ_j A_j = z·1` over a discrete valuation ring -/

section Smith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Divisibility is total** in a discrete valuation ring: if `a ∤ z` then `a = z·u` with `u` in the maximal
ideal. -/
theorem exists_eq_mul_of_not_dvd {a z : R} (h : ¬ a ∣ z) : ∃ u ∈ IsLocalRing.maximalIdeal R, a = z * u := by
  obtain ⟨u, hu⟩ := (ValuationRing.dvd_total a z).resolve_left h
  refine ⟨u, (IsLocalRing.mem_maximalIdeal u).2 fun hu' => h ⟨↑hu'.unit⁻¹, ?_⟩, hu⟩
  rw [hu, mul_assoc, IsUnit.mul_val_inv, mul_one]

/-- **Smith splitting**: if `Σ_j A_j = z·1` over a discrete valuation ring (`z ≠ 0`), each `A_j` has a part
`P_j·A_j·Q_j = z·1` of size `ν_j`, with `Σ_j ν_j ≥ n`. In a Smith basis `b` of `R^n` for the range of `A_j`
(`Submodule.smithNormalForm`, elementary divisors `a_s`), `ν_j` counts the `a_s ∣ z`: `Q_j` takes preimages of
`z·b_s`, `P_j` the coordinates. The other `a_s` are `z·𝔪`-multiples, so `z·R^n = Σ_j A_j(R^n)` lies in `T + 𝔪·zR^n`,
`T` the span of the chosen `b_s`; Nakayama gives `zR^n ⊆ T`, and `T` is spanned by `Σ_j ν_j` vectors. -/
theorem smith_split {J : Type*} [Fintype J] {n : ℕ} (A : J → Matrix (Fin n) (Fin n) R) (z : R) (hz : z ≠ 0)
    (hA : ∑ i, A i = z • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ ν : J → ℕ, n ≤ ∑ i, ν i ∧ ∀ i, ∃ (P : Matrix (Fin (ν i)) (Fin n) R) (Q : Matrix (Fin n) (Fin (ν i)) R),
      P * A i * Q = z • (1 : Matrix (Fin (ν i)) (Fin (ν i)) R) := by
  classical
  let N : J → Submodule R (Fin n → R) := fun i => LinearMap.range (A i).mulVecLin
  let B : ∀ i, Σ m : ℕ, Module.Basis.SmithNormalForm (N i) (Fin n) m := fun i =>
    (N i).smithNormalForm (Pi.basisFun R (Fin n))
  let S : ∀ i, Finset (Fin (B i).1) := fun i => Finset.univ.filter fun s => (B i).2.a s ∣ z
  let eS : ∀ i, Fin (S i).card ≃ S i := fun i => (S i).equivFin.symm
  refine ⟨fun i => (S i).card, ?_, fun i => ?_⟩
  · -- `zR^n` lies in the span `T` of the chosen basis vectors (Nakayama)
    let g : (Σ i, Fin (S i).card) → Fin n → R := fun x => (B x.1).2.bM ((B x.1).2.f (eS x.1 x.2))
    set T := Submodule.span R (Set.range g)
    let Z : Submodule R (Fin n → R) := LinearMap.range (z • LinearMap.id)
    have hT : ∀ i (s : Fin (B i).1), (B i).2.a s ∣ z → (B i).2.bM ((B i).2.f s) ∈ T := fun i s hs =>
      Submodule.subset_span ⟨⟨i, (eS i).symm ⟨s, by simpa [S] using hs⟩⟩, by simp [g]⟩
    have hZ : Z ≤ T ⊔ IsLocalRing.maximalIdeal R • (T ⊔ Z) := by
      rintro _ ⟨x, rfl⟩
      have hsum : (z • LinearMap.id : (Fin n → R) →ₗ[R] Fin n → R) x = ∑ i, A i *ᵥ x := by
        have h1 : (∑ i, A i) *ᵥ x = ∑ i, A i *ᵥ x := map_sum (Matrix.mulVec.addMonoidHomLeft x) A Finset.univ
        rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
        rw [LinearMap.smul_apply, LinearMap.id_apply, h1]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      let y : N i := ⟨A i *ᵥ x, x, rfl⟩
      have hy : (y : Fin n → R) = ∑ s, ((B i).2.bN.repr y s * (B i).2.a s) • (B i).2.bM ((B i).2.f s) := by
        conv_lhs => rw [← (B i).2.bN.sum_repr y]
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [Submodule.coe_smul, (B i).2.snf, smul_smul]
      change (y : Fin n → R) ∈ _
      rw [hy]
      refine Submodule.sum_mem _ fun s _ => ?_
      by_cases hs : (B i).2.a s ∣ z
      · rw [mul_comm, ← smul_smul]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hT i s hs)))
      · obtain ⟨u, hu, hau⟩ := exists_eq_mul_of_not_dvd hs
        refine Submodule.mem_sup_right ?_
        have e : ((B i).2.bN.repr y s * (B i).2.a s) • (B i).2.bM ((B i).2.f s) =
            u • (z • LinearMap.id : (Fin n → R) →ₗ[R] Fin n → R)
              ((B i).2.bN.repr y s • (B i).2.bM ((B i).2.f s)) := by
          simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, hau]
          congr 1
          ring
        rw [e]
        exact Submodule.smul_mem_smul hu (Submodule.mem_sup_right ⟨_, rfl⟩)
    have hZT : Z ≤ T := by
      have hle : T ⊔ Z ≤ T := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (IsLocalRing.maximalIdeal_le_jacobson ⊥) (sup_le le_sup_left hZ)
      exact le_sup_right.trans hle
    -- the `z·e_l` are independent in `T`
    let v : Fin n → Fin n → R := fun l => z • Pi.single l 1
    have hv : LinearIndependent R v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc l
      have := congrFun hc l
      simp [v, Finset.sum_apply, Pi.single_apply, hz] at this
      exact this
    have hvT : Set.range v ≤ T := by
      rintro _ ⟨l, rfl⟩
      exact hZT ⟨Pi.single l 1, rfl⟩
    have h := linearIndependent_le_span' v hv (Set.range g) hvT
    rw [Cardinal.mk_fin, Nat.cast_le] at h
    refine h.trans ((Fintype.card_range_le g).trans ?_)
    rw [Fintype.card_sigma]
    simp
  · -- the block of `A_i`: `Q` takes preimages of the `z·b_s`, `P` their coordinates
    set b := (B i).2
    choose w hw using fun s : S i => LinearMap.mem_range.1 (b.bN s).2
    choose q hq using fun s : S i => (Finset.mem_filter.1 s.2).2
    let pL : (Fin n → R) →ₗ[R] Fin (S i).card → R := LinearMap.pi fun t => b.bM.coord (b.f (eS i t))
    let qL : (Fin (S i).card → R) →ₗ[R] Fin n → R :=
      Fintype.linearCombination R fun t => q (eS i t) • w (eS i t)
    refine ⟨LinearMap.toMatrix' pL, LinearMap.toMatrix' qL, Matrix.toLin'.injective ?_⟩
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', map_smul,
      Matrix.toLin'_one]
    refine (Pi.basisFun R (Fin (S i).card)).ext fun t => ?_
    have e : (A i).mulVecLin (q (eS i t) • w (eS i t)) = z • b.bM (b.f (eS i t)) := by
      rw [map_smul, hw, b.snf, smul_smul, mul_comm, ← hq]
    rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply, Fintype.linearCombination_apply_single,
      one_smul, Matrix.toLin'_apply', e, map_smul, LinearMap.smul_apply, LinearMap.id_apply]
    congr 1
    funext t'
    change b.bM.coord (b.f (eS i t')) (b.bM (b.f (eS i t))) = (Pi.single t (1 : R) : Fin (S i).card → R) t'
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((eS i).injective (Subtype.ext (b.f.injective h1))).symm h2
    · exact absurd (by rw [h2]) h1
    · rfl

/-- **The good rank** `good(β, Λ, D)`: the largest `n` of a family `x_i, y_i` in `Λ` with `β(x_i, y_l) = z_i·δ_{il}`,
`z_i ≠ 0`, `z_i ∣ π^D`. -/
def goodRank {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (π : R) (β : V →ₗ[R] V →ₗ[R] R)
    (Λ : Submodule R V) (D : ℕ) : ℕ :=
  sSup {n | ∃ (x y : Fin n → V) (z : Fin n → R), (∀ i, x i ∈ Λ ∧ y i ∈ Λ ∧ z i ≠ 0 ∧ z i ∣ π ^ D) ∧
    ∀ i l, β (x i) (y l) = if i = l then z i else 0}

open Classical in
/-- **The good rank by Smith invariants**: for `G = U·diag(d)·V` (`U`, `V` invertible, `d_i ≠ 0`), the good rank of
the form `xᵀGy` on `R^n` is the number of `d_i ∣ π^D`. The dual families `e_i·U⁻¹`, `V⁻¹·e_i` (`d_i ∣ π^D`) realise
it. Conversely, for a good family of size `m`, in the coordinates `X = x·U`, `Y = V·y` the part of the Gram matrix
through the `d_a ∣ π^D` is `B·C = diag(z) + π^D·𝔪` (the other `d_a` lie in `π^D·𝔪`), which has a `π^D`-left inverse
(`exists_mul_eq_smul_one`), so `m ≤ #{d_a ∣ π^D}` (`card_le_of_mul_eq_smul_one`). -/
theorem goodRank_eq_smith {π : R} (hπ : Irreducible π) {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R) (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : ∀ i, d i ≠ 0)
    (hG : G = U * Matrix.diagonal d * V) :
    goodRank π (Matrix.toBilin' G) (⊤ : Submodule R (Fin n → R)) =
      fun D => (Finset.univ.filter fun i => d i ∣ π ^ D).card := by
  funext D
  set K := Finset.univ.filter fun i => d i ∣ π ^ D
  have hβ : ∀ x y : Fin n → R, Matrix.toBilin' G x y = (x ᵥ* U) ⬝ᵥ (Matrix.diagonal d *ᵥ (V *ᵥ y)) := by
    intro x y
    rw [Matrix.toBilin'_apply', hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · -- the dual families
    let eK : Fin K.card ≃ K := K.equivFin.symm
    refine ⟨fun k => Pi.single (eK k).1 1 ᵥ* U⁻¹, fun k => V⁻¹ *ᵥ Pi.single (eK k).1 1, fun k => d (eK k).1,
      fun k => ⟨Submodule.mem_top, Submodule.mem_top, hd _, (Finset.mem_filter.1 (eK k).2).2⟩, fun k l => ?_⟩
    rw [hβ]
    dsimp only
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one, Matrix.mulVec_mulVec _ V V⁻¹,
      Matrix.mul_nonsing_inv _ hV, Matrix.one_mulVec, Matrix.diagonal_mulVec_single, single_dotProduct,
      Pi.single_apply, one_mul]
    by_cases hkl : k = l
    · subst hkl
      simp
    · have : (eK k).1 ≠ (eK l).1 := fun h => hkl (eK.injective (Subtype.ext h))
      simp [hkl, this]
  · -- the upper bound
    rintro m ⟨x, y, z, hxyz, hxy⟩
    have hu : ∀ a, ∃ u ∈ IsLocalRing.maximalIdeal R, a ∉ K → d a = π ^ D * u := fun a => by
      by_cases ha : a ∈ K
      · exact ⟨0, zero_mem _, fun h => absurd ha h⟩
      · obtain ⟨u, hu, e⟩ := exists_eq_mul_of_not_dvd fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        exact ⟨u, hu, fun _ => e⟩
    choose u hum hu using hu
    let Bm : Matrix (Fin m) K R := fun i a => (x i ᵥ* U) a * d a
    let Cm : Matrix K (Fin m) R := fun a l => (V *ᵥ y l) a
    have hnear : ∀ i l, ∃ h ∈ IsLocalRing.maximalIdeal R,
        (Bm * Cm) i l = (if i = l then z i else 0) + π ^ D * h := by
      intro i l
      refine ⟨-∑ a ∈ Finset.univ.filter (fun a => ¬ d a ∣ π ^ D), (x i ᵥ* U) a * u a * (V *ᵥ y l) a,
        neg_mem (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hum a))), ?_⟩
      have h1 := hxy i l
      rw [hβ, dotProduct, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => d a ∣ π ^ D)] at h1
      have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬ d a ∣ π ^ D),
          (x i ᵥ* U) a * (Matrix.diagonal d *ᵥ (V *ᵥ y l)) a =
            π ^ D * ∑ a ∈ Finset.univ.filter (fun a => ¬ d a ∣ π ^ D), (x i ᵥ* U) a * u a * (V *ᵥ y l) a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Matrix.mulVec_diagonal, hu a fun h => (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 h).2]
        ring
      have h3 : (Bm * Cm) i l = ∑ a ∈ K, (x i ᵥ* U) a * (Matrix.diagonal d *ᵥ (V *ᵥ y l)) a := by
        rw [Matrix.mul_apply, ← Finset.sum_coe_sort K]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Bm, Cm, Matrix.mulVec_diagonal]
        ring
      rw [h2] at h1
      rw [h3, ← h1]
      ring
    obtain ⟨A, hA⟩ := exists_mul_eq_smul_one (Bm * Cm) z (fun i => (hxyz i).2.2.2) hnear
    have := card_le_of_mul_eq_smul_one (A * Bm) Cm (pow_ne_zero D hπ.ne_zero) (by rw [Matrix.mul_assoc, hA])
    simpa using this

/-- **Primitive tests reach `P·R^n`**: if a submodule `S ⊆ R^n` over a discrete valuation ring meets every primitive
functional `c` (some `c_i` a unit) in a divisor of `P ≠ 0` (`c·s ∣ P` for some `s ∈ S`), then `P·R^n ⊆ S`. In a
Smith basis `b` of `R^n` for `S` (elementary divisors `a_j`), the coordinate `b_k^*` is a primitive functional; it
vanishes on `S` unless `k = f(j)`, and then its values are multiples of `a_j`, so `a_j ∣ P` for every `j` and every
`k` is some `f(j)`: `P·b_k = (P/a_j)·(a_j·b_{f(j)}) ∈ S`. -/
theorem smul_mem_of_primitive {n : ℕ} (S : Submodule R (Fin n → R)) {P : R} (hP : P ≠ 0)
    (h : ∀ c : Fin n → R, (∃ i, IsUnit (c i)) → ∃ s ∈ S, c ⬝ᵥ s ∣ P) (v : Fin n → R) : P • v ∈ S := by
  classical
  obtain ⟨m, B⟩ := S.smithNormalForm (Pi.basisFun R (Fin n))
  -- the coordinate functionals are primitive
  have hcoord : ∀ k (w : Fin n → R), (fun i => B.bM.coord k (Pi.single i 1)) ⬝ᵥ w = B.bM.coord k w := by
    intro k w
    conv_rhs => rw [← Finset.univ_sum_single w]
    simp only [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Pi.single i (w i) : Fin n → R) = w i • Pi.single i 1 := by
      ext l
      simp [Pi.single_apply]
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hprim : ∀ k, ∃ i, IsUnit (B.bM.coord k (Pi.single i 1)) := by
    intro k
    by_contra hk
    push Not at hk
    have h1 : B.bM.coord k (B.bM k) ∈ IsLocalRing.maximalIdeal R := by
      rw [← hcoord]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hk i))
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
  -- every coordinate is hit, by an elementary divisor dividing `P`
  have hk : ∀ k, ∃ j, B.f j = k ∧ B.a j ∣ P := by
    intro k
    obtain ⟨s, hs, hsP⟩ := h _ (hprim k)
    rw [hcoord] at hsP
    by_cases hkf : k ∈ Set.range B.f
    · obtain ⟨j, rfl⟩ := hkf
      refine ⟨j, rfl, dvd_trans ?_ hsP⟩
      rw [Module.Basis.coord_apply, show s = ((⟨s, hs⟩ : S) : Fin n → R) from rfl,
        B.repr_apply_embedding_eq_repr_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    · rw [Module.Basis.coord_apply, show s = ((⟨s, hs⟩ : S) : Fin n → R) from rfl,
        B.repr_eq_zero_of_notMem_range ⟨s, hs⟩ hkf] at hsP
      exact absurd (zero_dvd_iff.1 hsP) hP
  -- so `P·b_k ∈ S` for every `k`
  have hb : ∀ k, P • B.bM k ∈ S := by
    intro k
    obtain ⟨j, rfl, q, hq⟩ := hk k
    rw [hq, mul_comm, ← smul_smul, ← B.snf]
    exact S.smul_mem _ (B.bN j).2
  rw [← B.bM.sum_repr v, Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => by rw [smul_comm]; exact S.smul_mem _ (hb k)


end Smith

/-! ## Counting subspaces of a finite vector space -/

section Grass

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- **Counting subspaces**: `#{U : dim U = m}·∏_{i<m}(q^m − q^i) = ∏_{i<m}(q^n − q^i)`, `n = dim V`, `q = #K`. The
linearly independent `m`-tuples (`card_linearIndependent`) fibre over their spans, and the fibre over `U` is the set
of independent `m`-tuples of `U`. -/
theorem card_subspace_mul {m : ℕ} (hm : m ≤ Module.finrank K V) :
    Nat.card {U : Submodule K V // Module.finrank K U = m} *
        ∏ i : Fin m, (Fintype.card K ^ m - Fintype.card K ^ i.val) =
      ∏ i : Fin m, (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i.val) := by
  classical
  have : Finite (Submodule K V) :=
    Finite.of_injective (fun U : Submodule K V => (U : Set V)) SetLike.coe_injective
  let _ : Fintype {U : Submodule K V // Module.finrank K U = m} := Fintype.ofFinite _
  let f : {s : Fin m → V // LinearIndependent K s} → {U : Submodule K V // Module.finrank K U = m} :=
    fun s => ⟨Submodule.span K (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin m)⟩
  have hfib : ∀ U : {U : Submodule K V // Module.finrank K U = m},
      Nat.card {s // f s = U} = ∏ i : Fin m, (Fintype.card K ^ m - Fintype.card K ^ i.val) := by
    rintro ⟨U, hU⟩
    have hsp : ∀ s : {s // f s = ⟨U, hU⟩}, Submodule.span K (Set.range s.1.1) = U := fun s =>
      congrArg Subtype.val s.2
    let e : {s // f s = ⟨U, hU⟩} ≃ {t : Fin m → U // LinearIndependent K t} :=
      { toFun := fun s => ⟨fun i => ⟨s.1.1 i, (hsp s).le (Submodule.subset_span ⟨i, rfl⟩)⟩,
          LinearIndependent.of_comp U.subtype s.1.2⟩
        invFun := fun t => ⟨⟨U.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype U)⟩, Subtype.ext <| by
          change Submodule.span K (Set.range (U.subtype ∘ t.1)) = U
          rw [Set.range_comp, Submodule.span_image,
            t.2.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hU]), Submodule.map_top,
            Submodule.range_subtype]⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
    rw [Nat.card_congr e, card_linearIndependent (le_of_eq hU.symm), hU]
  rw [← card_linearIndependent hm, ← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- **Many subspaces**: `q^{m(n−m)} ≤ #{U : dim U = m}` (`card_subspace_mul`, `q^{n−m}(q^m − q^i) ≤ q^n − q^i`). -/
theorem pow_le_card_subspace {m : ℕ} (hm : m ≤ Module.finrank K V) :
    Fintype.card K ^ (m * (Module.finrank K V - m)) ≤ Nat.card {U : Submodule K V // Module.finrank K U = m} := by
  set q := Fintype.card K
  set n := Module.finrank K V
  have hq : 1 < q := Fintype.one_lt_card
  have hpos : 0 < ∏ i : Fin m, (q ^ m - q ^ i.val) :=
    Finset.prod_pos fun i _ => Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq i.2)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [card_subspace_mul hm, mul_comm m, pow_mul, ← Fin.prod_const m (q ^ (n - m)), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun i _ => ?_
  rw [Nat.mul_sub, ← pow_add, Nat.sub_add_cancel hm]
  exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) _

omit [Fintype K] [Finite V] in
/-- **Isomorphic spaces have equally many subspaces of each dimension.** -/
theorem card_subspace_congr {V' : Type*} [AddCommGroup V'] [Module K V'] (φ : V ≃ₗ[K] V') (m : ℕ) :
    Nat.card {U : Submodule K V // Module.finrank K U = m} = Nat.card {U : Submodule K V' // Module.finrank K U = m} :=
  Nat.card_congr <| (Submodule.orderIsoMapComap φ).toEquiv.subtypeEquiv fun U => by
    change _ ↔ Module.finrank K (U.map (φ : V →ₗ[K] V')) = _
    rw [LinearEquiv.finrank_map_eq]

omit [Fintype K] in
/-- **Subspaces of dimension `m` and of codimension `m` are equinumerous**: `U ↦ U^⊥ ⊆ V^*`
(`dualAnnihilator`), and `V^* ≃ V`. -/
theorem card_subspace_compl {m : ℕ} (hm : m ≤ Module.finrank K V) :
    Nat.card {U : Submodule K V // Module.finrank K U = m} =
      Nat.card {U : Submodule K V // Module.finrank K U = Module.finrank K V - m} := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  set n := Module.finrank K V
  let e₁ : {U : Submodule K V // Module.finrank K U = m} ≃
      {U : Submodule K (Module.Dual K V) // Module.finrank K U = n - m} :=
    { toFun := fun U => ⟨U.1.dualAnnihilator, by
        have := Subspace.finrank_add_finrank_dualAnnihilator_eq U.1; omega⟩
      invFun := fun U => ⟨U.1.dualCoannihilator, by
        have := Subspace.finrank_add_finrank_dualCoannihilator_eq U.1; omega⟩
      left_inv := fun U => Subtype.ext (Subspace.dualAnnihilator_dualCoannihilator_eq)
      right_inv := fun U => Subtype.ext (Subspace.dualCoannihilator_dualAnnihilator_eq) }
  exact (Nat.card_congr e₁).trans
    (card_subspace_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq) (n - m))

end Grass

/-! ## Edges and planes -/

section Planes

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

variable (W) in
/-- **The ideal `pW`.** -/
abbrev pId (p : ℕ) : Ideal W := Ideal.span {(p : W)}

/-- **The residue space** `M/pM` of a `W`-submodule `M` of `Qq^k`, a module over `W/p`. -/
abbrev resSp (p : ℕ) (M : Submodule W (Fin k → Qq)) : Type :=
  ↥M ⧸ pId W p • (⊤ : Submodule W ↥M)

/-- **A `W`-submodule of `M/pM` as a subspace over `W/p`**: the scalars of `W/p` act through `W`. -/
def toRes {M : Submodule W (Fin k → Qq)} (S : Submodule W (resSp p M)) : Submodule (W ⧸ pId W p) (resSp p M) where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_smul]
    exact S.smul_mem a hx

/-- **The plane of `N`** in `M/pM`: the image of `N ∩ M`. -/
def plane (p : ℕ) (M N : Submodule W (Fin k → Qq)) : Submodule (W ⧸ pId W p) (resSp p M) :=
  toRes ((N.comap M.subtype).map (pId W p • (⊤ : Submodule W ↥M)).mkQ)

/-- **The lattice of a plane** `U ⊆ M/pM`: its preimage in `M`. -/
def ofPlane (p : ℕ) (M : Submodule W (Fin k → Qq)) (U : Submodule (W ⧸ pId W p) (resSp p M)) :
    Submodule W (Fin k → Qq) :=
  ((U.restrictScalars W).comap (pId W p • (⊤ : Submodule W ↥M)).mkQ).map M.subtype

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`pM` in coordinates**: `y ∈ pM` (in `M`) iff `y = p·z` with `z ∈ M`. -/
theorem mem_pId_smul_top {M : Submodule W (Fin k → Qq)} {y : ↥M} :
    y ∈ pId W p • (⊤ : Submodule W ↥M) ↔ ∃ z : ↥M, (p : W) • z = y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨z, _, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, Submodule.mem_top, hz⟩⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The plane of a plane's lattice** is the plane: `M ↪ Qq^k` is injective and `M → M/pM` surjective. -/
theorem plane_ofPlane (M : Submodule W (Fin k → Qq)) (U : Submodule (W ⧸ pId W p) (resSp p M)) :
    plane p M (ofPlane p M U) = U := by
  ext x
  change x ∈ (((ofPlane p M U).comap M.subtype).map (pId W p • (⊤ : Submodule W ↥M)).mkQ) ↔ x ∈ U
  rw [ofPlane, Submodule.comap_map_eq_of_injective M.injective_subtype,
    Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _)]
  rfl

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`pM ⊆ N ∩ M`** when `p·M ⊆ N`. -/
theorem pId_smul_le {M N : Submodule W (Fin k → Qq)} (hpN : ∀ x ∈ M, (p : W) • x ∈ N) :
    pId W p • (⊤ : Submodule W ↥M) ≤ N.comap M.subtype := fun y hy => by
  obtain ⟨z, rfl⟩ := mem_pId_smul_top.1 hy
  exact hpN _ z.2

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The lattice of the plane of `N`** is `N`, for `pM ⊆ N ⊆ M`. -/
theorem ofPlane_plane {M N : Submodule W (Fin k → Qq)} (hN : N ≤ M) (hpN : ∀ x ∈ M, (p : W) • x ∈ N) :
    ofPlane p M (plane p M N) = N := by
  change (((N.comap M.subtype).map (pId W p • (⊤ : Submodule W ↥M)).mkQ).comap
    (pId W p • (⊤ : Submodule W ↥M)).mkQ).map M.subtype = N
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 (pId_smul_le hpN), Submodule.map_comap_subtype, inf_eq_right.2 hN]

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **A plane's lattice lies in `M`.** -/
theorem ofPlane_le (M : Submodule W (Fin k → Qq)) (U : Submodule (W ⧸ pId W p) (resSp p M)) :
    ofPlane p M U ≤ M :=
  Submodule.map_subtype_le _ _

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **A plane's lattice contains `pM`.** -/
theorem smul_mem_ofPlane (M : Submodule W (Fin k → Qq)) (U : Submodule (W ⧸ pId W p) (resSp p M)) {x}
    (hx : x ∈ M) : (p : W) • x ∈ ofPlane p M U := by
  refine ⟨(p : W) • ⟨x, hx⟩, ?_, rfl⟩
  change Submodule.Quotient.mk _ ∈ U
  rw [(Submodule.Quotient.mk_eq_zero _).2 (mem_pId_smul_top.2 ⟨⟨x, hx⟩, rfl⟩)]
  exact zero_mem _

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **Between `pM` and `M` every submodule is a lattice**: finitely generated as `M` is noetherian, and spanning
since `x = p⁻¹·(p·x)`. -/
theorem isLattice_of_le {M N : Submodule W (Fin k → Qq)} [IsNoetherianRing W] (hp : (p : Qq) ≠ 0)
    (hM : M.IsLattice Qq) (hN : N ≤ M) (hpN : ∀ x ∈ M, (p : W) • x ∈ N) : N.IsLattice Qq := by
  have := hM
  refine ⟨?_, ?_⟩
  · have := (IsNoetherian.noetherian (N.comap M.subtype)).map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hN] at this
  · rw [eq_top_iff, ← hM.span_eq_top, Submodule.span_le]
    intro x hx
    have e : x = (p : Qq)⁻¹ • ((p : W) • x) := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul Qq, smul_smul, inv_mul_cancel₀ hp, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hpN x hx))

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **A plane's lattice is a lattice.** -/
theorem isLattice_ofPlane [IsNoetherianRing W] (hp : (p : Qq) ≠ 0) {M : Submodule W (Fin k → Qq)}
    (hM : M.IsLattice Qq) (U : Submodule (W ⧸ pId W p) (resSp p M)) : (ofPlane p M U).IsLattice Qq :=
  isLattice_of_le hp hM (ofPlane_le M U) fun _ hx => smul_mem_ofPlane M U hx

/-- **`q = p^{n'} > 1`**: the residue field `W/p` has `p^{n'}` elements and is nontrivial. -/
theorem one_lt_q (hU : Unram p n' W Qq O Kf ι σ j ϖ) : 1 < p ^ n' := by
  rcases Nat.eq_zero_or_pos n' with h | h
  · subst h
    have h1 := hU.res_card
    rw [pow_zero, Nat.card_eq_one_iff_unique] at h1
    exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.Quotient.subsingleton_iff.1 h1.1)) hU.unif_W.not_isUnit
  · exact Nat.one_lt_pow h.ne' hU.prime.one_lt

/-- **`M/pM` has `q^k` elements** for a lattice `M`: in a basis of `M`, `pM` is `(pW)^k` (`Submodule.quotientPi`). -/
theorem card_resSp (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M : Submodule W (Fin k → Qq)} (hM : M.IsLattice Qq) :
    Nat.card (resSp p M) = (p ^ n') ^ k := by
  classical
  have := hU.frac_W
  have := hM
  have hk : Module.finrank W M = k := by rw [Submodule.IsLattice.finrank_of_pi Qq M, Fintype.card_fin]
  set b := Module.finBasisOfFinrankEq W M hk
  have hmap : (pId W p • (⊤ : Submodule W M)).map (b.equivFun : ↥M →ₗ[W] Fin k → W) =
      Submodule.pi Set.univ fun _ => pId W p := by
    ext y
    rw [Submodule.mem_map_equiv, mem_pId_smul_top, Submodule.mem_pi]
    constructor
    · rintro ⟨z, hz⟩ i -
      have e : y = (p : W) • b.equivFun z := by rw [← map_smul, hz, LinearEquiv.apply_symm_apply]
      rw [e, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hy
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (hy i (Set.mem_univ _))
      refine ⟨b.equivFun.symm c, ?_⟩
      rw [← map_smul]
      congr 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hc i, mul_comm]
  rw [Nat.card_congr ((Submodule.Quotient.equiv _ _ b.equivFun hmap).trans (Submodule.quotientPi _)).toEquiv,
    Nat.card_pi]
  simp [hU.res_card]

/-- **`W/p` is a field**: `p` is irreducible in the principal ideal ring `W`. -/
theorem isMaximal_pId (hU : Unram p n' W Qq O Kf ι σ j ϖ) : (pId W p).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hU.unif_W

/-- **`M/pM` is finite** for a lattice `M` (`card_resSp`). -/
theorem finite_resSp (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M : Submodule W (Fin k → Qq)} (hM : M.IsLattice Qq) :
    Finite (resSp p M) :=
  Nat.finite_of_card_ne_zero (by rw [card_resSp hU hM]; exact pow_ne_zero _ (one_lt_q hU).ne_bot)

/-- **`W/p` is finite**, with `q = p^{n'}` elements. -/
theorem finite_res (hU : Unram p n' W Qq O Kf ι σ j ϖ) : Finite (W ⧸ pId W p) :=
  Nat.finite_of_card_ne_zero (by rw [hU.res_card]; exact pow_ne_zero _ hU.prime.ne_zero)

/-- **`M/pM` has dimension `k` over `W/p`** for a lattice `M` (`card_resSp`). -/
theorem finrank_resSp (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M : Submodule W (Fin k → Qq)} (hM : M.IsLattice Qq) :
    Module.finrank (W ⧸ pId W p) (resSp p M) = k := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hM
  have h := Module.natCard_eq_pow_finrank (K := W ⧸ pId W p) (V := resSp p M)
  rw [card_resSp hU hM, hU.res_card] at h
  exact (Nat.pow_right_injective (one_lt_q hU) h).symm

/-- **A plane has dimension at most `k`.** -/
theorem finrank_le_k (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M : Submodule W (Fin k → Qq)} (hM : M.IsLattice Qq)
    (U : Submodule (W ⧸ pId W p) (resSp p M)) : Module.finrank (W ⧸ pId W p) U ≤ k := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hM
  exact (Submodule.finrank_le U).trans (finrank_resSp hU hM).le

/-- **The index of `N` in `M` is `q^{codim}`** of its plane, for `pM ⊆ N ⊆ M`: `M/N ≅ (M/pM)/plane` (third
isomorphism theorem). -/
theorem card_quot_plane (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M N : Submodule W (Fin k → Qq)} (hM : M.IsLattice Qq)
    (hpN : ∀ x ∈ M, (p : W) • x ∈ N) :
    Nat.card (↥M ⧸ N.comap M.subtype) = (p ^ n') ^ (k - Module.finrank (W ⧸ pId W p) (plane p M N)) := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hM
  rw [← Nat.card_congr (Submodule.quotientQuotientEquivQuotient (pId W p • (⊤ : Submodule W ↥M))
    (N.comap M.subtype) (pId_smul_le hpN)).toEquiv,
    show (N.comap M.subtype).map (pId W p • (⊤ : Submodule W ↥M)).mkQ = (plane p M N).restrictScalars W from rfl,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv W (plane p M N)).toEquiv,
    Module.natCard_eq_pow_finrank (K := W ⧸ pId W p), hU.res_card]
  have h := Submodule.finrank_quotient_add_finrank (plane p M N)
  rw [finrank_resSp hU hM] at h
  congr 1
  omega

/-- **The index of `pM` in `N` is `q^{dim}`** of its plane, for `pM ⊆ N ⊆ M`, `pM` given as a submodule `L″` of
`Qq^k`: `N/pM` is the image of `N` in `M/pM`. -/
theorem card_plane (hU : Unram p n' W Qq O Kf ι σ j ϖ) {M N L'' : Submodule W (Fin k → Qq)}
    (hM : M.IsLattice Qq) (hN : N ≤ M) (hL'' : ∀ x, x ∈ L'' ↔ ∃ z ∈ M, (p : W) • z = x) :
    Nat.card (↥N ⧸ L''.comap N.subtype) = (p ^ n') ^ Module.finrank (W ⧸ pId W p) (plane p M N) := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hM
  set φ : ↥N →ₗ[W] resSp p M := (pId W p • (⊤ : Submodule W ↥M)).mkQ ∘ₗ Submodule.inclusion hN
  have hker : LinearMap.ker φ = L''.comap N.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hL'']
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_pId_smul_top]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩
  have hrange : LinearMap.range φ = (plane p M N).restrictScalars W := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
    rfl
  rw [← hker, Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv, hrange,
    show Nat.card ↥((plane p M N).restrictScalars W) = Nat.card ↥(plane p M N) from rfl,
    Module.natCard_eq_pow_finrank (K := W ⧸ pId W p), hU.res_card]

end Planes

/-! ## Good systems at the edges -/

section Defs

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {p n' k : ℕ}

/-- **The source family** at the edge `L″ ⊂ L` (depth `t`, conductor `c`): the source lattice of `L″` at depth `t`,
cut down to the vectors `ϖ^c`-small on the other edges `L″ ⊂ L′` (`L′ ≠ L`) of type `r`. -/
def SrcFam (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t c : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (Unit × Fin n') k Kf) :=
  srcLat p r ι σ ϖ lam0 t L'' ∩
    ⋂ (L' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L') (_ : L' ≠ L),
      (algebraMap O Kf ϖ ^ c) • edgeLat ι σ ϖ r lam0 L'' L'

/-- **The target family** at the edge `L″ ⊂ L`: the target lattice of `L` at depth `t`, cut down to the vectors
`ϖ^c`-small on the other edges `L₁ ⊂ L` (`L₁ ≠ L″`) of type `r`. -/
def TgtFam (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t c : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (Unit × Fin n') k Kf) :=
  (tgtLat p r ι σ ϖ lam0 t L : Set (Pol (Unit × Fin n') k Kf)) ∩
    ⋂ (L₁ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L₁ L) (_ : L₁ ≠ L''),
      (algebraMap O Kf ϖ ^ c) • (edgeDual p r ι σ ϖ lam0 L₁ L : Set (Pol (Unit × Fin n') k Kf))

/-- **A good system of size `n`** at the edge `L″ ⊂ L`: sources `x_i` in the source family, targets `y_m` in the
target family, `z ≠ 0` with `z ∣ p^D` and an `O`-matrix `M` with `Σ_m pairE(x_i, y_m)·M_{ml} = z·δ_{il}`. -/
def GoodSys (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t c D : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) (n : ℕ) : Prop :=
  ∃ (x y : Fin n → Pol (Unit × Fin n') k Kf) (z : O) (M : Matrix (Fin n) (Fin n) O),
    z ≠ 0 ∧ z ∣ (p : O) ^ D ∧ (∀ i, x i ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) ∧
      (∀ i, y i ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) ∧
      ∀ i l, ∑ m, pairE p r lam0 (x i) (y m) * algebraMap O Kf (M m l) = if i = l then algebraMap O Kf z else 0

variable (W) in
/-- **The per-edge rank** `Rank(t, c; D; X)`: every edge of type `r` carries a good system of size at least `X`. -/
def RankAll (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lam0 : Fin n' → Fin k → ℤ) (t c D : ℕ) (X : ℝ) :
    Prop :=
  ∀ L'' L : Submodule W (Fin k → Qq), IsEdge (n' := n') p r L'' L →
    ∃ n : ℕ, X ≤ n ∧ GoodSys p r ι σ ϖ lam0 t c D L'' L n

/-- **The number of edges of type `r` into a lattice** (the Gaussian binomial `[k, r]_q`, `q = p^{n'}`). -/
def nEdges (p r : ℕ) (L : Submodule W (Fin k → Qq)) : ℕ := Set.ncard {L'' | IsEdge (n' := n') p r L'' L}

end Defs

/-! ## The assembly -/

section Assembly

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The local lattice problem from a Gram matrix**: edges `e_i ⊂ L`, sources `F_i` in the source lattices of the
`e_i` and `ϖ^c`-small on the other edges out of them, targets `Y_l` in the target lattice of `L`, and a `p^D`-left
inverse `A` of the `O`-valued Gram matrix `G_{il} = pairE(F_i, Y_l)`: then `u(x) = Σ_l x_l·Y_l` gives `LLPAt`. -/
theorem llpAt_of_gram {lam0 : Fin n' → Fin k → ℤ} {r t c D M : ℕ} {κ : ℝ} {L : Submodule W (Fin k → Qq)}
    (e : Fin M → Submodule W (Fin k → Qq)) (F Y : Fin M → Pol (Unit × Fin n') k Kf)
    (he : ∀ i, IsEdge (n' := n') p r (e i) L) (hF : ∀ i, F i ∈ srcLat p r ι σ ϖ lam0 t (e i))
    (hsm : ∀ i (L' : Submodule W (Fin k → Qq)), IsEdge (n' := n') p r (e i) L' → L' ≠ L →
      F i ∈ (algebraMap O Kf ϖ ^ c) • edgeLat ι σ ϖ r lam0 (e i) L')
    (hY : ∀ l, Y l ∈ tgtLat p r ι σ ϖ lam0 t L) (G A : Matrix (Fin M) (Fin M) O)
    (hG : ∀ i l, pairE p r lam0 (F i) (Y l) = algebraMap O Kf (G i l)) (hA : A * G = ((p : O) ^ D) • 1)
    (hM : (1 - κ) * (dimV Kf lam0 : ℝ) ≤ M) : LLPAt p r ι σ ϖ lam0 t D κ c L := by
  set Y' : Fin M → tgtLat p r ι σ ϖ lam0 t L := fun l => ⟨Y l, hY l⟩
  refine ⟨M, e, F, he, hF, hsm, M, hM, Fintype.linearCombination O Y', A, fun x a => ?_⟩
  have key : ∀ i, pairE p r lam0 (F i) (Fintype.linearCombination O Y' x : Pol (Unit × Fin n') k Kf) =
      algebraMap O Kf ((G *ᵥ x) i) := fun i => by
    rw [Fintype.linearCombination_apply, Submodule.coe_sum, map_sum, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul Kf, map_smul, hG, smul_eq_mul, map_mul, mul_comm]
  simp only [key, ← map_mul, ← map_sum]
  congr 1
  have := congrFun (Matrix.mulVec_mulVec x A G) a
  rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
  exact this

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Pairing with a combination of targets**: `pairE(F, Σ_m M_m·y_m) = Σ_m M_m·pairE(F, y_m)` for `M_m ∈ O`. -/
theorem pairE_sum_smul (p r : ℕ) (lam0 : Fin n' → Fin k → ℤ) {n : ℕ} (F : Pol (Unit × Fin n') k Kf)
    (y : Fin n → Pol (Unit × Fin n') k Kf) (M : Fin n → O) :
    pairE p r lam0 F (∑ m, M m • y m) = ∑ m, algebraMap O Kf (M m) * pairE p r lam0 F (y m) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [← algebraMap_smul Kf, map_smul, smul_eq_mul]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Small pairings stay small** under `O`-combinations of the targets. -/
theorem pairE_sum_small {lam0 : Fin n' → Fin k → ℤ} {r c n : ℕ} {F : Pol (Unit × Fin n') k Kf}
    {y : Fin n → Pol (Unit × Fin n') k Kf} (M : Fin n → O)
    (h : ∀ m, ∃ o : O, pairE p r lam0 F (y m) = algebraMap O Kf (ϖ ^ c * o)) :
    ∃ o : O, pairE p r lam0 F (∑ m, M m • y m) = algebraMap O Kf (ϖ ^ c * o) := by
  choose o ho using h
  refine ⟨∑ m, M m * o m, ?_⟩
  rw [pairE_sum_smul, Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [ho, ← map_mul, mul_left_comm]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`ϖ^c·𝓡(e)` pairs `ϖ^c`-small with `𝓡′(e)`.** -/
theorem pairE_small_left {lam0 : Fin n' → Fin k → ℤ} {r c : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    {F G : Pol (Unit × Fin n') k Kf} (hF : F ∈ (algebraMap O Kf ϖ ^ c) • edgeLat ι σ ϖ r lam0 L'' L)
    (hG : G ∈ edgeDual p r ι σ ϖ lam0 L'' L) : ∃ o : O, pairE p r lam0 F G = algebraMap O Kf (ϖ ^ c * o) := by
  obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 hF
  obtain ⟨o, ho⟩ := hG.2 F₁ hF₁
  exact ⟨o, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← ho, map_mul, map_pow]⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`𝓡(e)` pairs `ϖ^c`-small with `ϖ^c·𝓡′(e)`.** -/
theorem pairE_small_right {lam0 : Fin n' → Fin k → ℤ} {r c : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    {F G : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L)
    (hG : G ∈ (algebraMap O Kf ϖ ^ c) • (edgeDual p r ι σ ϖ lam0 L'' L : Set (Pol (Unit × Fin n') k Kf))) :
    ∃ o : O, pairE p r lam0 F G = algebraMap O Kf (ϖ ^ c * o) := by
  obtain ⟨G₁, hG₁, rfl⟩ := Set.mem_smul_set.1 hG
  obtain ⟨o, ho⟩ := hG₁.2 F hF
  exact ⟨o, by rw [map_smul, smul_eq_mul, ← ho, map_mul, map_pow]⟩

/-- **A block Gram matrix has a `p^D`-left inverse**: if the pairings of sources `X_b` with targets `Y_{b′}` are
`z_e·δ_{bb′}` inside a block `e` (with `z_e ∣ p^D`) and `ϖ^c`-small across blocks, `c ≥ 2D + 1`, then the Gram matrix
is `O`-valued, `diag(z) + p^D·ϖ·H` (as `p = ϖ²`), and has a `p^D`-left inverse (`exists_mul_eq_smul_one`). -/
theorem exists_gram_inv (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r c D : ℕ}
    (hc : 2 * D + 1 ≤ c) {I E : Type*} [Fintype I] [DecidableEq I] (bl : I → E)
    (X Y : I → Pol (Unit × Fin n') k Kf) (z : E → O) (hzD : ∀ e, z e ∣ (p : O) ^ D)
    (hdiag : ∀ b b', bl b = bl b' →
      pairE p r lam0 (X b) (Y b') = if b = b' then algebraMap O Kf (z (bl b)) else 0)
    (hoff : ∀ b b', bl b ≠ bl b' → ∃ o : O, pairE p r lam0 (X b) (Y b') = algebraMap O Kf (ϖ ^ c * o)) :
    ∃ G A : Matrix I I O, (∀ b b', pairE p r lam0 (X b) (Y b') = algebraMap O Kf (G b b')) ∧
      A * G = ((p : O) ^ D) • 1 := by
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  have hGO : ∀ b b', ∃ g : O, pairE p r lam0 (X b) (Y b') = algebraMap O Kf g := by
    intro b b'
    by_cases h : bl b = bl b'
    · rw [hdiag b b' h]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨0, (map_zero _).symm⟩
    · obtain ⟨o, ho⟩ := hoff b b' h
      exact ⟨_, ho⟩
  choose G hG using hGO
  have hϖ : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hU.unif_O.not_isUnit
  have hnear : ∀ b b', ∃ h ∈ IsLocalRing.maximalIdeal O,
      G b b' = (if b = b' then z (bl b) else 0) + (p : O) ^ D * h := by
    intro b b'
    by_cases h : bl b = bl b'
    · refine ⟨0, zero_mem _, hinj ?_⟩
      rw [← hG, hdiag b b' h]
      split_ifs <;> simp
    · obtain ⟨o, ho⟩ := hoff b b' h
      refine ⟨ϖ * (ϖ ^ (c - (2 * D + 1)) * o), Ideal.mul_mem_right _ _ hϖ, hinj ?_⟩
      rw [← hG, ho, ite_eq_right_iff.2 fun hb => absurd (congrArg bl hb) h, zero_add]
      congr 1
      rw [← hU.sq, ← pow_mul, ← mul_assoc, ← pow_succ, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]
  obtain ⟨A, hA⟩ := exists_mul_eq_smul_one G (fun b => z (bl b)) (fun b => hzD (bl b)) hnear
  exact ⟨G, A, hG, hA⟩

/-- **The assembly** (per-edge ranks give the local lattice problem): if every edge of type `r` carries a good system
of size at least `X`, and `(1 − κ)·dim V ≤ #edges·X`, then `LLPAt(t, D, κ, c)` holds at every lattice, for
`c ≥ 2D + 1`. The `F_i` are the sources of the good systems at the edges `e ⊂ L` (all cut to size `⌈X⌉`), the targets
are `Y_l = Σ_m M_{ml}·y_m`. The Gram matrix is `z_e·1` on the block of `e`, and `ϖ^c`-small off the diagonal blocks:
the targets at `e′` are `ϖ^c`-small on `𝓡′(e)`, and the sources at `e` lie in `𝓡(e)` (`exists_gram_inv`,
`llpAt_of_gram`). -/
theorem llpAt_of_rankAll (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c D : ℕ} {κ X : ℝ}
    (hc : 2 * D + 1 ≤ c)
    (hX : ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq → (1 - κ) * dimV Kf lam0 ≤ nEdges (n' := n') p r L * X)
    (h : RankAll W p r ι σ ϖ lam0 t c D X) (L : Submodule W (Fin k → Qq)) (hL : L.IsLattice Qq) :
    LLPAt p r ι σ ϖ lam0 t D κ c L := by
  classical
  set E := {L'' : Submodule W (Fin k → Qq) | IsEdge (n' := n') p r L'' L}
  have : Finite E := (finite_edges hU r L).to_subtype
  let _ : Fintype E := Fintype.ofFinite E
  choose n hn hgs using fun e : E => h e.1 L e.2
  choose x y z Mm hz hzD hx hy hG using hgs
  have hn₀ : ∀ e, ⌈X⌉₊ ≤ n e := fun e => Nat.ceil_le.2 (hn e)
  set F : E × Fin ⌈X⌉₊ → Pol (Unit × Fin n') k Kf := fun b => x b.1 (Fin.castLE (hn₀ b.1) b.2)
  set Y : E × Fin ⌈X⌉₊ → Pol (Unit × Fin n') k Kf := fun b =>
    ∑ m, Mm b.1 m (Fin.castLE (hn₀ b.1) b.2) • y b.1 m
  have hsrc : ∀ b, F b ∈ srcLat p r ι σ ϖ lam0 t b.1.1 := fun b => (hx b.1 _).1
  have hsm : ∀ b (L' : Submodule W (Fin k → Qq)), IsEdge (n' := n') p r b.1.1 L' → L' ≠ L →
      F b ∈ (algebraMap O Kf ϖ ^ c) • edgeLat ι σ ϖ r lam0 b.1.1 L' := fun b L' he hne =>
    Set.mem_iInter.1 (Set.mem_iInter₂.1 (hx b.1 _).2 L' he) hne
  have htgt : ∀ b, Y b ∈ tgtLat p r ι σ ϖ lam0 t L := fun b =>
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy b.1 m).1
  have hdiag : ∀ b b' : E × Fin ⌈X⌉₊, b.1 = b'.1 →
      pairE p r lam0 (F b) (Y b') = if b = b' then algebraMap O Kf (z b.1) else 0 := by
    rintro ⟨e, i⟩ ⟨e', l⟩ (hee : e = e')
    subst hee
    have h2 := hG e (Fin.castLE (hn₀ e) i) (Fin.castLE (hn₀ e) l)
    simp only [mul_comm (pairE p r lam0 _ _)] at h2
    rw [pairE_sum_smul, show F (e, i) = x e (Fin.castLE (hn₀ e) i) from rfl, h2]
    by_cases hil : i = l
    · subst hil
      simp
    · simp [hil]
  -- off the diagonal blocks the targets are `ϖ^c`-small on the sources' edge
  have hoff : ∀ b b' : E × Fin ⌈X⌉₊, b.1 ≠ b'.1 →
      ∃ o : O, pairE p r lam0 (F b) (Y b') = algebraMap O Kf (ϖ ^ c * o) := fun b b' hne =>
    pairE_sum_small _ fun m => pairE_small_right (Set.mem_iInter₂.1 (hsrc b).2 L b.1.2)
      (Set.mem_iInter.1 (Set.mem_iInter₂.1 (hy b'.1 m).2 b.1.1 b.1.2) fun h => hne (Subtype.ext h))
  obtain ⟨G, A, hGdef, hA⟩ := exists_gram_inv hU hc Prod.fst F Y z hzD hdiag hoff
  -- reindex by `Fin N`
  set eI := (Fintype.equivFin (E × Fin ⌈X⌉₊)).symm
  refine llpAt_of_gram (fun a => (eI a).1.1) (F ∘ eI) (Y ∘ eI) (fun a => (eI a).1.2) (fun a => hsrc (eI a))
    (fun a => hsm (eI a)) (fun a => htgt (eI a)) (G.submatrix eI eI) (A.submatrix eI eI)
    (fun a a' => hGdef (eI a) (eI a')) ?_ ?_
  · rw [Matrix.submatrix_mul_equiv, hA]
    ext a b
    simp [Matrix.one_apply, eI.injective.eq_iff]
  · have hE : nEdges (n' := n') p r L = Fintype.card E := by
      rw [nEdges, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    refine (hX L hL).trans ?_
    rw [hE, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil X) (Nat.cast_nonneg _)

end Assembly

/-! ## Transport between edges -/

section Transport

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **`g` moves the dual edge lattice** `𝓡′(L″ ⊂ L)` into `𝓡′(gL″ ⊂ gL)`, the target-side analogue of
`mvS_mem_edgeLat`: `mvS g⁻¹` moves `𝓡(gL″ ⊂ gL)` back into `𝓡(L″ ⊂ L)`, and the moves keep the pairing
(`pairE_mv`). -/
theorem mvT_mem_edgeDual (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) {G : Pol (Unit × Fin n') k Kf}
    (hG : G ∈ edgeDual p r ι σ ϖ lam0 L'' L) :
    mvT ι σ lam0 g G ∈ edgeDual p r ι σ ϖ lam0 (gmap W g L'') (gmap W g L) := by
  refine ⟨twist_mem_nabla _ _ hG.1, fun F hF => ?_⟩
  have h0 := mvS_mem_edgeLat hU g⁻¹ (isEdge_gmap g he) hF
  rw [gmap_inv_gmap, gmap_inv_gmap] at h0
  rw [← mvS_mvS_inv (ι := ι) (σ := σ) lam0 g F, pairE_mv]
  exact hG.2 _ h0

omit [CharZero Kf] in
/-- **`g` moves the source family** of `L″ ⊂ L` into that of `gL″ ⊂ gL` (`mvS_mem_srcLat`, `mvS_mem_edgeLat`). -/
theorem mvS_mem_srcFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L)
    {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) :
    mvS ι σ lam0 g F ∈ SrcFam p r ι σ ϖ lam0 t c (gmap W g L'') (gmap W g L) := by
  refine ⟨mvS_mem_srcLat hU g he.2.1 hF.1, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
  have he₁ := isEdge_gmap_inv he'
  have hne₁ : gmap W g⁻¹ L' ≠ L := fun h => hne (by rw [← h, gmap_gmap_inv])
  obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hF.2 _ he₁) hne₁)
  have := mvS_mem_edgeLat hU g he₁ hF₁
  rw [gmap_gmap_inv] at this
  rw [mvS, twist_smul, ← mvS]
  exact Set.smul_mem_smul_set this

/-- **`g` moves the target family** of `L″ ⊂ L` into that of `gL″ ⊂ gL` (`mvT_mem_tgtLat`, `mvT_mem_edgeDual`). -/
theorem mvT_mem_tgtFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} (g : GL (Fin k) Qq)
    {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L)
    {G : Pol (Unit × Fin n') k Kf} (hG : G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) :
    mvT ι σ lam0 g G ∈ TgtFam p r ι σ ϖ lam0 t c (gmap W g L'') (gmap W g L) := by
  refine ⟨mvT_mem_tgtLat hU g he.1 hG.1, Set.mem_iInter₂.2 fun L₁ he₁ => Set.mem_iInter.2 fun hne => ?_⟩
  have he' : IsEdge (n' := n') p r (gmap W g⁻¹ L₁) L := by
    have := isEdge_gmap g⁻¹ he₁
    rwa [gmap_inv_gmap] at this
  have hne' : gmap W g⁻¹ L₁ ≠ L'' := fun h => hne (by rw [← h, gmap_gmap_inv])
  obtain ⟨G₁, hG₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hG.2 _ he') hne')
  have := mvT_mem_edgeDual hU g he' hG₁
  rw [gmap_gmap_inv] at this
  rw [map_smul]
  exact Set.smul_mem_smul_set this

/-- **A permutation matching two index sets of the same size.** -/
theorem exists_perm_mem_iff {S₁ S₂ : Finset (Fin k)} (h : S₁.card = S₂.card) :
    ∃ τ : Equiv.Perm (Fin k), ∀ l, l ∈ S₁ ↔ τ l ∈ S₂ := by
  classical
  have h1 : Fintype.card {l // l ∈ S₁} = Fintype.card {l // l ∈ S₂} := by
    rw [Fintype.card_coe, Fintype.card_coe, h]
  have h2 : Fintype.card {l // l ∉ S₁} = Fintype.card {l // l ∉ S₂} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun l => ?_⟩
  by_cases hl : l ∈ S₁
  · simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hl, hl]
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hl, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr, hl, false_iff]
    exact ((Fintype.equivOfCardEq h2) ⟨l, hl⟩).2

omit [CharZero Kf] in
/-- **`GL_k(Qq)` is transitive on the edges of type `r`**: with edge bases `B₁, S₁` of `L₁″ ⊂ L₁` and `B₂, S₂` of
`L₂″ ⊂ L₂` (`exists_basis_edge`) and a permutation `τ` with `τ(S₁) = S₂`, `g = B₂P_τ·B₁⁻¹` moves `L₁` to `L₂` and
`L₁″` to `L₂″`. -/
theorem exists_gmap_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} {L₁'' L₁ L₂'' L₂ : Submodule W (Fin k → Qq)}
    (h₁ : IsEdge (n' := n') p r L₁'' L₁) (h₂ : IsEdge (n' := n') p r L₂'' L₂) :
    ∃ g : GL (Fin k) Qq, gmap W g L₁'' = L₂'' ∧ gmap W g L₁ = L₂ := by
  obtain ⟨B₁, S₁, hS₁, hB₁, hL₁, hL₁''⟩ := exists_basis_edge hU h₁
  obtain ⟨B₂, S₂, hS₂, hB₂, hL₂, hL₂''⟩ := exists_basis_edge hU h₂
  obtain ⟨τ, hτ⟩ := exists_perm_mem_iff (hS₁.trans hS₂.symm)
  set B : Matrix (Fin k) (Fin k) Qq := B₂.submatrix id τ
  have hB : IsUnit B.det := by
    rw [Matrix.det_permute']
    exact ((Units.map (Int.castRingHom Qq).toMonoidHom (Equiv.Perm.sign τ)).isUnit).mul hB₂
  set g := Matrix.nonsingInvUnit (B * B₁⁻¹)
    (by rw [Matrix.det_mul]; exact hB.mul (Matrix.isUnit_nonsing_inv_det _ hB₁))
  have hg : (g : Matrix (Fin k) (Fin k) Qq) * B₁ = B := by
    rw [show (g : Matrix (Fin k) (Fin k) Qq) = B * B₁⁻¹ from rfl, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB₁,
      Matrix.mul_one]
  refine ⟨g, (map_span_cols g hL₁'').trans ?_, (map_span_cols g hL₁).trans ?_⟩
  · rw [← Matrix.mul_assoc, hg, hL₂'']
    have e : (fun l i => (B * Matrix.diagonal fun i => if i ∈ S₁ then (p : Qq) else 1) i l) =
        (fun l i => (B₂ * Matrix.diagonal fun i => if i ∈ S₂ then (p : Qq) else 1) i l) ∘ τ := by
      funext l i
      simp [B, Matrix.mul_diagonal, hτ]
    rw [e, τ.surjective.range_comp]
  · rw [hg, hL₂]
    exact congrArg (Submodule.span W) (τ.surjective.range_comp fun l i => B₂ i l)

/-- **Edge transport**: good systems move between edges of the same type (`exists_gmap_edge`; sources by `mvS g`,
targets by `mvT g`, which keep the pairing, so the same `z` and `M` serve). -/
theorem goodSys_transport (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c D n : ℕ}
    {L₁'' L₁ L₂'' L₂ : Submodule W (Fin k → Qq)} (h₁ : IsEdge (n' := n') p r L₁'' L₁)
    (h₂ : IsEdge (n' := n') p r L₂'' L₂) (h : GoodSys p r ι σ ϖ lam0 t c D L₁'' L₁ n) :
    GoodSys p r ι σ ϖ lam0 t c D L₂'' L₂ n := by
  obtain ⟨g, rfl, rfl⟩ := exists_gmap_edge hU h₁ h₂
  obtain ⟨x, y, z, M, hz, hzD, hx, hy, hG⟩ := h
  refine ⟨fun i => mvS ι σ lam0 g (x i), fun i => mvT ι σ lam0 g (y i), z, M, hz, hzD,
    fun i => mvS_mem_srcFam hU g h₁ (hx i), fun i => mvT_mem_tgtFam hU g h₁ (hy i), fun i l => ?_⟩
  simp only [pairE_mv]
  exact hG i l

end Transport

/-! ## Counting edges: edges are planes -/

section Count

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **Edges into `L` are planes** (type `r ≤ k`): `L″ ↦` its image in `L/pL` (`plane`), a subspace of dimension
`k − r` over `W/p`, with inverse the preimage (`ofPlane`); the index `[L : L″] = q^r` is `q^{codim}`
(`card_quot_plane`). -/
def edgeEquivPlane (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq)
    {r : ℕ} (hr : r ≤ k) :
    {L'' // IsEdge (n' := n') p r L'' L} ≃
      {U : Submodule (W ⧸ pId W p) (resSp p L) // Module.finrank (W ⧸ pId W p) U = k - r} where
  toFun L'' := ⟨plane p L L''.1, by
    have h := card_quot_plane hU hL L''.2.2.2.2.1
    rw [L''.2.2.2.2.2, pow_mul] at h
    have h2 := Nat.pow_right_injective (one_lt_q hU) h
    have h3 := finrank_le_k hU hL (plane p L L''.1)
    omega⟩
  invFun U := ⟨ofPlane p L U.1, hL, isLattice_ofPlane hU.cast_ne_zero hL U.1, ofPlane_le L U.1,
    fun _ hx => smul_mem_ofPlane L U.1 hx, by
      rw [card_quot_plane hU hL fun _ hx => smul_mem_ofPlane L U.1 hx, plane_ofPlane, U.2, pow_mul]
      congr 1
      omega⟩
  left_inv L'' := Subtype.ext (ofPlane_plane L''.2.2.2.1 L''.2.2.2.2.1)
  right_inv U := Subtype.ext (plane_ofPlane L U.1)

/-- **The number of edges of type `r` into `L` is the number of planes** of dimension `k − r` in `L/pL`. -/
theorem nEdges_eq_card (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq)
    {r : ℕ} (hr : r ≤ k) :
    nEdges (n' := n') p r L =
      Nat.card {U : Submodule (W ⧸ pId W p) (resSp p L) // Module.finrank (W ⧸ pId W p) U = k - r} :=
  (Nat.card_coe_set_eq _).symm.trans (Nat.card_congr (edgeEquivPlane hU hL hr))

/-- **Edge count** (type `r ≤ k`): `#edges into L ≥ q^{r(k−r)}` (`pow_le_card_subspace`). -/
theorem nEdges_ge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} (hr : r ≤ k) {L : Submodule W (Fin k → Qq)}
    (hL : L.IsLattice Qq) : (p ^ n') ^ (r * (k - r)) ≤ nEdges (n' := n') p r L := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hL
  have := finite_res hU
  let _ : Fintype (W ⧸ pId W p) := Fintype.ofFinite _
  have h := pow_le_card_subspace (K := W ⧸ pId W p) (V := resSp p L) (m := k - r)
    (by rw [finrank_resSp hU hL]; omega)
  rw [finrank_resSp hU hL, Fintype.card_eq_nat_card, hU.res_card, Nat.sub_sub_self hr, mul_comm] at h
  rw [nEdges_eq_card hU hL hr]
  exact h

/-- **Edge count, type `1`**: `#edges into L·(q − 1) = q^k − 1` (hyperplanes of `L/pL`, as many as lines,
`card_subspace_compl`, `card_subspace_mul`). -/
theorem nEdges_one (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq) :
    nEdges (n' := n') p 1 L * (p ^ n' - 1) = (p ^ n') ^ k - 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : {L'' | IsEdge (n' := n') p 1 L'' L} = ∅ := Set.eq_empty_of_forall_notMem fun L'' he => by
      have h := he.2.2.2.2
      have : Subsingleton (↥L ⧸ L''.comap L.subtype) := (Submodule.Quotient.mk_surjective _).subsingleton
      have h1 : Nat.card (↥L ⧸ L''.comap L.subtype) = 1 := Nat.card_unique
      rw [h, mul_one] at h1
      exact absurd h1 (one_lt_q hU).ne'
    simp [nEdges, this]
  · have := isMaximal_pId hU
    let _ := Ideal.Quotient.field (pId W p)
    have := finite_resSp hU hL
    have := finite_res hU
    let _ : Fintype (W ⧸ pId W p) := Fintype.ofFinite _
    have h1 := card_subspace_compl (K := W ⧸ pId W p) (V := resSp p L) (m := 1)
      (by rw [finrank_resSp hU hL]; exact hk)
    have h2 := card_subspace_mul (K := W ⧸ pId W p) (V := resSp p L) (m := 1)
      (by rw [finrank_resSp hU hL]; exact hk)
    rw [finrank_resSp hU hL] at h1 h2
    rw [Fintype.card_eq_nat_card, hU.res_card] at h2
    rw [nEdges_eq_card hU hL hk, ← h1]
    simpa using h2

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`p·y` over `W` is `p·y` over `Qq`.** -/
theorem natCast_smul_eq (y : Fin k → Qq) : (p : W) • y = (p : Qq) • y := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/-- **The lattice `p⁻¹L″`.** -/
def pInv (p : ℕ) (L'' : Submodule W (Fin k → Qq)) : Submodule W (Fin k → Qq) :=
  L''.map ((((p : Qq)⁻¹ • LinearMap.id : (Fin k → Qq) →ₗ[Qq] Fin k → Qq)).restrictScalars W)

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`x ∈ p⁻¹L″` iff `p·x ∈ L″`.** -/
theorem mem_pInv (hp : (p : Qq) ≠ 0) {L'' : Submodule W (Fin k → Qq)} {x : Fin k → Qq} :
    x ∈ pInv p L'' ↔ (p : W) • x ∈ L'' := by
  rw [natCast_smul_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul, mul_inv_cancel₀ hp] using hy
  · intro h
    exact ⟨(p : Qq) • x, h, by simp [smul_smul, inv_mul_cancel₀ hp]⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`p⁻¹L″` is a lattice** with `L″`. -/
theorem isLattice_pInv (hp : (p : Qq) ≠ 0) {L'' : Submodule W (Fin k → Qq)} (h : L''.IsLattice Qq) :
    (pInv p L'').IsLattice Qq := by
  refine ⟨h.fg.map _, ?_⟩
  rw [pInv, Submodule.map_coe, show ((((p : Qq)⁻¹ • LinearMap.id : (Fin k → Qq) →ₗ[Qq] Fin k → Qq)).restrictScalars W :
    (Fin k → Qq) → Fin k → Qq) = ((p : Qq)⁻¹ • LinearMap.id : (Fin k → Qq) →ₗ[Qq] Fin k → Qq) from rfl,
    Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨(p : Qq) • y, by simp [smul_smul, mul_inv_cancel₀ hp]⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`L″ = p·(p⁻¹L″)`.** -/
theorem mem_iff_pInv (hp : (p : Qq) ≠ 0) {L'' : Submodule W (Fin k → Qq)} (x : Fin k → Qq) :
    x ∈ L'' ↔ ∃ z ∈ pInv p L'', (p : W) • z = x := by
  have e : (p : W) • ((p : Qq)⁻¹ • x) = x := by rw [natCast_smul_eq, smul_smul, mul_inv_cancel₀ hp, one_smul]
  refine ⟨fun hx => ⟨(p : Qq)⁻¹ • x, (mem_pInv hp).2 (by rw [e]; exact hx), e⟩, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact (mem_pInv hp).1 hz

/-- **Edges out of `L″` are planes**: the edges `L″ ⊂ L` of type `r` are the `L` between `L″ = p·M` and
`M = p⁻¹L″` whose plane in `M/pM` has dimension `r` (`card_plane`). -/
def outEdgeEquivPlane (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L'' : Submodule W (Fin k → Qq)}
    (hL'' : L''.IsLattice Qq) (r : ℕ) :
    {L // IsEdge (n' := n') p r L'' L} ≃
      {U : Submodule (W ⧸ pId W p) (resSp p (pInv p L'')) // Module.finrank (W ⧸ pId W p) U = r} where
  toFun L := ⟨plane p (pInv p L'') L.1, by
    have h := card_plane hU (isLattice_pInv hU.cast_ne_zero hL'')
      (fun x hx => (mem_pInv hU.cast_ne_zero).2 (L.2.2.2.2.1 x hx)) (mem_iff_pInv hU.cast_ne_zero)
    rw [L.2.2.2.2.2, pow_mul] at h
    exact (Nat.pow_right_injective (one_lt_q hU) h).symm⟩
  invFun U := ⟨ofPlane p (pInv p L'') U.1, isLattice_ofPlane hU.cast_ne_zero (isLattice_pInv hU.cast_ne_zero hL'') U.1,
    hL'', fun x hx => by
      obtain ⟨z, hz, rfl⟩ := (mem_iff_pInv hU.cast_ne_zero x).1 hx
      exact smul_mem_ofPlane _ U.1 hz,
    fun x hx => (mem_pInv hU.cast_ne_zero).1 (ofPlane_le _ U.1 hx), by
      rw [card_plane hU (isLattice_pInv hU.cast_ne_zero hL'') (ofPlane_le _ U.1) (mem_iff_pInv hU.cast_ne_zero),
        plane_ofPlane, U.2, pow_mul]⟩
  left_inv L := Subtype.ext (ofPlane_plane (fun x hx => (mem_pInv hU.cast_ne_zero).2 (L.2.2.2.2.1 x hx))
    fun x hx => L.2.2.2.1 ((mem_pInv hU.cast_ne_zero).1 hx))
  right_inv U := Subtype.ext (plane_ofPlane _ U.1)

/-- **As many edges out of a lattice as into one** (type `r ≤ k`): both are counted by planes of `F_q^k`, of
dimension `r` and `k − r` (`outEdgeEquivPlane`, `edgeEquivPlane`, `card_subspace_compl`). -/
theorem ncard_outEdges (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L'' L : Submodule W (Fin k → Qq)}
    (hL'' : L''.IsLattice Qq) (hL : L.IsLattice Qq) {r : ℕ} (hr : r ≤ k) :
    Set.ncard {L' | IsEdge (n' := n') p r L'' L'} = nEdges (n' := n') p r L := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have hM := isLattice_pInv hU.cast_ne_zero hL''
  have := finite_resSp hU hM
  have := finite_resSp hU hL
  rw [nEdges_eq_card hU hL hr, ← Nat.card_coe_set_eq]
  refine (Nat.card_congr (outEdgeEquivPlane hU hL'' r)).trans ?_
  rw [card_subspace_compl (by rw [finrank_resSp hU hM]; exact hr), finrank_resSp hU hM]
  exact card_subspace_congr (LinearEquiv.ofFinrankEq _ _ ((finrank_resSp hU hM).trans (finrank_resSp hU hL).symm))
    (k - r)

end Count

/-! ## The per-edge upper bound -/

section Upper

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [CharZero Kf] in
/-- **Edges have type at most `k`**: `q^r = [L : L″] = q^{codim}` (`card_quot_plane`). -/
theorem le_of_isEdge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) : r ≤ k := by
  have h := card_quot_plane hU he.1 he.2.2.2.1
  rw [he.2.2.2.2, pow_mul] at h
  have := Nat.pow_right_injective (one_lt_q hU) h
  omega

/-- **Per-edge upper bound**: a system at one edge `L″ ⊂ L` with sources in the source family, targets only in
`𝓡′(L″ ⊂ L)` and `Gram·M = z·1`, `z ∣ p^D`, `2D < c`, has `#edges·n ≤ dim V`. Transport it to every edge `L″ ⊂ L′`
out of `L″` (`exists_gmap_edge` fixing `L″`); across two such edges the sources are `ϖ^c`-small on the other edge,
so the big Gram matrix has a `p^D`-left inverse (`exists_gram_inv`), and the `#edges·n` sources are independent.
There are as many edges out of `L″` as into `L` (`ncard_outEdges`). -/
theorem goodSys_card_le (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ}
    (hlam : ∀ s, Antitone (lam0 s)) {r t c D n : ℕ} (hc : 2 * D < c) {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) (x y : Fin n → Pol (Unit × Fin n') k Kf) (z : O)
    (M : Matrix (Fin n) (Fin n) O) (hzD : z ∣ (p : O) ^ D) (hx : ∀ i, x i ∈ SrcFam p r ι σ ϖ lam0 t c L'' L)
    (hy : ∀ i, y i ∈ edgeDual p r ι σ ϖ lam0 L'' L)
    (hG : ∀ i l, ∑ m, pairE p r lam0 (x i) (y m) * algebraMap O Kf (M m l) = if i = l then algebraMap O Kf z else 0) :
    nEdges (n' := n') p r L * n ≤ dimV Kf lam0 := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  set E := {L' : Submodule W (Fin k → Qq) | IsEdge (n' := n') p r L'' L'}
  have : Finite E := by
    have := isMaximal_pId hU
    let _ := Ideal.Quotient.field (pId W p)
    have := finite_resSp hU (isLattice_pInv hU.cast_ne_zero he.2.1)
    have : Finite (Submodule (W ⧸ pId W p) (resSp p (pInv p L''))) :=
      Finite.of_injective (fun U : Submodule (W ⧸ pId W p) (resSp p (pInv p L'')) => (U : Set (resSp p (pInv p L''))))
        SetLike.coe_injective
    exact Finite.of_equiv _ (outEdgeEquivPlane hU he.2.1 r).symm
  let _ : Fintype E := Fintype.ofFinite E
  choose g hg₁ hg₂ using fun e : E => exists_gmap_edge hU he e.2
  set X : E × Fin n → Pol (Unit × Fin n') k Kf := fun b => mvS ι σ lam0 (g b.1) (x b.2)
  set Y : E × Fin n → Pol (Unit × Fin n') k Kf := fun b => ∑ m, M m b.2 • mvT ι σ lam0 (g b.1) (y m)
  have hX : ∀ b, X b ∈ SrcFam p r ι σ ϖ lam0 t c L'' b.1.1 := fun b => by
    have := mvS_mem_srcFam hU (g b.1) he (hx b.2)
    rwa [hg₁, hg₂] at this
  have hYd : ∀ (e : E) m, mvT ι σ lam0 (g e) (y m) ∈ edgeDual p r ι σ ϖ lam0 L'' e.1 := fun e m => by
    have := mvT_mem_edgeDual hU (g e) he (hy m)
    rwa [hg₁, hg₂] at this
  have hdiag : ∀ b b' : E × Fin n, b.1 = b'.1 →
      pairE p r lam0 (X b) (Y b') = if b = b' then algebraMap O Kf z else 0 := by
    rintro ⟨e, i⟩ ⟨e', l⟩ (hee : e = e')
    subst hee
    have h2 := hG i l
    simp only [mul_comm (pairE p r lam0 _ _)] at h2
    simp only [X, Y, pairE_sum_smul, pairE_mv, h2, Prod.mk.injEq, true_and]
  have hoff : ∀ b b' : E × Fin n, b.1 ≠ b'.1 →
      ∃ o : O, pairE p r lam0 (X b) (Y b') = algebraMap O Kf (ϖ ^ c * o) := fun b b' hne =>
    pairE_sum_small _ fun m => pairE_small_left
      (Set.mem_iInter.1 (Set.mem_iInter₂.1 (hX b).2 b'.1.1 b'.1.2) fun h => hne (Subtype.ext h).symm)
      (hYd b'.1 m)
  obtain ⟨G, A, hGdef, hA⟩ := exists_gram_inv hU hc Prod.fst X Y (fun _ => z) (fun _ => hzD) hdiag hoff
  -- the Gram matrix is invertible over `Kf`
  have hdet : (G.map (algebraMap O Kf)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Ne, map_eq_zero_iff _ hinj]
    intro h0
    have h1 := congrArg Matrix.det hA
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have hp : (p : O) ≠ 0 := hU.sq ▸ pow_ne_zero 2 hU.unif_O.ne_zero
    exact pow_ne_zero _ (pow_ne_zero _ hp) h1.symm
  -- so the sources are independent
  have hli : LinearIndependent Kf X := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hv : a ᵥ* G.map (algebraMap O Kf) = 0 := by
      funext b'
      have := congrArg (fun F => pairE p r lam0 F (Y b')) ha
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero, LinearMap.zero_apply,
        smul_eq_mul, hGdef] at this
      simpa [Matrix.vecMul, dotProduct] using this
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv)
  have hXV : ∀ b, X b ∈ nabla Kf (nu1 lam0) := fun b => by
    obtain ⟨F, hF, hFe⟩ := Set.mem_smul_set.1 (hX b).1.1
    rw [← hFe]
    exact Submodule.smul_mem _ _ hF.1
  have : FiniteDimensional Kf (nabla Kf (nu1 lam0)) := by
    obtain ⟨x', -, -, hsx, -⟩ := exists_adapted_basis (O := O) hU hlam he
    rw [← hsx]
    exact FiniteDimensional.span_of_finite Kf (Set.finite_range _)
  have hcard := (LinearIndependent.of_comp (nabla Kf (nu1 lam0)).subtype
    (v := fun b => (⟨X b, hXV b⟩ : nabla Kf (nu1 lam0))) hli).fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at hcard
  rwa [← ncard_outEdges hU he.2.1 he.1 (le_of_isEdge hU he), ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

end Upper

/-! ## Good systems from primitive tests (the second form of the assembly) -/

section Primitive

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The target family is an `O`-module**: closed under `0`, sums and `O`-multiples, as `tgtLat` and the
`ϖ^c·𝓡′(e)` are. -/
theorem tgtFam_closed {lam0 : Fin n' → Fin k → ℤ} {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} :
    (0 : Pol (Unit × Fin n') k Kf) ∈ TgtFam p r ι σ ϖ lam0 t c L'' L ∧
    (∀ G G', G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L → G' ∈ TgtFam p r ι σ ϖ lam0 t c L'' L →
      G + G' ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) ∧
    ∀ (a : O) G, G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L → a • G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L := by
  refine ⟨⟨zero_mem _, Set.mem_iInter₂.2 fun _ _ => Set.mem_iInter.2 fun _ => ⟨0, zero_mem _, smul_zero _⟩⟩,
    fun G G' hG hG' => ⟨add_mem hG.1 hG'.1, Set.mem_iInter₂.2 fun L₁ he => Set.mem_iInter.2 fun hne => ?_⟩,
    fun a G hG => ⟨Submodule.smul_mem _ a hG.1, Set.mem_iInter₂.2 fun L₁ he => Set.mem_iInter.2 fun hne => ?_⟩⟩
  · obtain ⟨G₁, hG₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hG.2 L₁ he) hne)
    obtain ⟨G₂, hG₂, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hG'.2 L₁ he) hne)
    exact ⟨G₁ + G₂, add_mem hG₁ hG₂, smul_add _ _ _⟩
  · obtain ⟨G₁, hG₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 hG.2 L₁ he) hne)
    exact ⟨a • G₁, Submodule.smul_mem _ a hG₁, smul_comm _ _ _⟩

/-- **A good system from primitive tests** (the form of L6's assembly): if sources `x_1, …, x_n` in the source family
at `L″ ⊂ L` are tested by the target family, that is, for every primitive `a ∈ O^n` (some `a_i` a unit) some target
`G` pairs `Σ a_i·x_i` to a divisor of `p^D`, then the edge carries a good system of size `n` (with `z = p^D`,
`M = 1`). The pairing vectors `(pairE(x_i, G))_i` of the targets form an `O`-submodule of `O^n`, which contains
`p^D·O^n` (`smul_mem_of_primitive`); preimages of the `p^D·e_l` are the targets. -/
theorem goodSys_of_primitive (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c D n : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) (x : Fin n → Pol (Unit × Fin n') k Kf)
    (hx : ∀ i, x i ∈ SrcFam p r ι σ ϖ lam0 t c L'' L)
    (htest : ∀ a : Fin n → O, (∃ i, IsUnit (a i)) → ∃ G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L, ∃ w : O,
      w ∣ (p : O) ^ D ∧ pairE p r lam0 (∑ i, a i • x i) G = algebraMap O Kf w) :
    GoodSys p r ι σ ϖ lam0 t c D L'' L n := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  have hp : (p : O) ^ D ≠ 0 := pow_ne_zero _ (hU.sq ▸ pow_ne_zero 2 hU.unif_O.ne_zero)
  obtain ⟨h0, hadd, hsmul⟩ := tgtFam_closed (p := p) (ι := ι) (σ := σ) (ϖ := ϖ) (lam0 := lam0) (r := r) (t := t)
    (c := c) (L'' := L'') (L := L)
  -- the pairing vectors of the targets
  let T : Set (Fin n → O) := {v | ∃ G ∈ TgtFam p r ι σ ϖ lam0 t c L'' L,
    ∀ i, pairE p r lam0 (x i) G = algebraMap O Kf (v i)}
  have hT : ∀ v ∈ Submodule.span O T, v ∈ T := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨0, h0, fun i => by simp⟩
    | add v v' _ _ hv hv' =>
      obtain ⟨G, hG, hGv⟩ := hv
      obtain ⟨G', hG', hGv'⟩ := hv'
      exact ⟨G + G', hadd G G' hG hG', fun i => by rw [map_add, hGv, hGv', Pi.add_apply, map_add]⟩
    | smul a v _ hv =>
      obtain ⟨G, hG, hGv⟩ := hv
      refine ⟨a • G, hsmul a G hG, fun i => ?_⟩
      rw [← algebraMap_smul Kf, map_smul, hGv, smul_eq_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  have hP : ∀ v : Fin n → O, (p : O) ^ D • v ∈ Submodule.span O T := by
    refine smul_mem_of_primitive _ hp fun a ha => ?_
    obtain ⟨G, hG, w, hw, hGw⟩ := htest a ha
    have hvi : ∀ i, ∃ o : O, pairE p r lam0 (x i) G = algebraMap O Kf o := fun i =>
      (pairE_mem_of_src_tgt he (hx i).1 hG.1).imp fun _ h => h.symm
    choose v hv using hvi
    refine ⟨v, Submodule.subset_span ⟨G, hG, hv⟩, ?_⟩
    have e : a ⬝ᵥ v = w := by
      apply hinj
      rw [← hGw, dotProduct, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul Kf (a i), map_smul, LinearMap.smul_apply, hv, smul_eq_mul, map_mul]
    rw [e]
    exact hw
  choose y hy hyv using fun l => hT _ (hP (Pi.single l 1))
  refine ⟨x, y, (p : O) ^ D, 1, hp, dvd_rfl, hx, hy, fun i l => ?_⟩
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [Matrix.one_apply_ne hm, map_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, map_one, mul_one, hyv, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

end Primitive

end

end LocalRank
