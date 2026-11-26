import WeylZForm

/-!
# The inert local model: lattice tuples, local Weyl lattices and Hecke operators

L1 of the local theory of the gain.

**The setting** (`Unram`). `W` is a complete discrete valuation ring with uniformiser `p` and residue field of size
`q = p^{n'}`, `Qq` its fraction field, `σ` a Frobenius of `Qq` keeping `W`; `O ⊇ W` (through `j`) is a discrete
valuation ring with fraction field `Kf` and a uniformiser `ϖ` with `ϖ² = p`, and `ι : Qq → Kf` extends `j`.

**Tuples and blocks.** A tuple is `L : V → Submodule W (Qq^k)`, `V` the orbits; a lattice tuple has every `L_v` a
lattice (`Submodule.IsLattice Qq`). The blocks are `V × Fin n'`: block `(v, s)` carries the `O`-lattice
`σ^s(L_v)⊗O` (`blk`) and the weight `lamAt (lam0 v) s`, which is `λ_s` at even `s` and the dual `−λ_s ∘ rev` at odd
`s` (`blockWt`). The coefficients live in `Pol (V × Fin n') k Kf`, the block-wise polynomials of `WeylFock`.

**The local Weyl lattices.** `C` is a basis matrix of an `O`-lattice `Λ` (`IsBasisOf`) when it is invertible and its
columns span `Λ`. `F ∈ Δ_L` (`DeltaT`) when `F ∈ ∇_{Kf}` and its twist `WeylFock.twist` by basis matrices of the
blocks lies in `Δ_O`; `∇_L` (`NablaT`) likewise with `∇_O`. Two basis matrices of one lattice differ by `GL_k(O)`
(`exists_mul_eq_of_isBasisOf`), which keeps `Δ_O` and `∇_O` (`twist_mem_Delta_iff`, `twist_mem_nablaInt`), so the
choice does not matter (`mem_DeltaT_iff`, `mem_NablaT_iff`).

**Edges and Hecke operators.** An edge of type `r` (`IsEdge`) is a pair of lattices `pL ⊆ L″ ⊆ L` with
`[L : L″] = q^r`. The Hecke operator at the orbit `v` (`hecke`) is `F ↦ (L ↦ p^{A_v}·Σ_{L″} F(L with L_v ↦ L″))`, the
sum over the edges `L″ ⊂ L_v`, with `A_v = Σ_s Σ_{i<r} λ_{v,s,i}` (`topSum`).

**A level** (`Level`) is a group `Γ` acting on each orbit's `Qq^k` (`Level.smul`) with a character `χ : Γ → O^×`;
`γ` acts on the coefficients by the twist by `ι σ^s(γ_v⁻¹)` (`Level.actF`). Its forms with coefficient lattices `H`
(`Level.forms`) are the `Γ`-equivariant functions on tuples, valued in `H(L)` at lattice tuples and `0` elsewhere. The
integral forms are `M` (`H = DeltaT`) and `M∇` (`H = NablaT`).

**Main results.**
* *Finiteness* (`finite_edges`): a lattice has finitely many edges below it, as they are determined by their images
  in the finite `L/pL`; so the sum of `hecke` is finite (`hecke_eq_sum`).
* *Commutation* (`hecke_comm`): the Hecke operators at different orbits commute.
* *Edge bases* (`exists_basis_edge`): for an edge `L″ ⊂ L` there is a basis matrix `B` of `L` with `L″` spanned by
  the columns of `B·diag(d)`, `d_i = p` for `i` in a set `S` of size `r` and `1` elsewhere (Smith normal form over
  `W`, with `|L/L″| = q^{|S|}` from `Submodule.quotientPi`).
* *Integrality* (`smul_mem_DeltaT_of_edge`, `smul_mem_NablaT_of_edge`): `p^{A_v}·Δ_{L″} ⊆ Δ_L` and
  `p^{A_v}·∇_{L″} ⊆ ∇_L` for dominant weights. In the coordinates of edge bases, `Δ_{L″}` is the twist of `Δ_L` by
  `diag(d)` in the blocks of `v`. By Fock adjointness the twist by `diag(d)` multiplies the pairing with a
  bideterminant `β` by `p^{e(β)}`, `e(β) = Σ_s (r·λ_{s,k−1} + Σ_{i∈S} μ_{s,i}(β))`, `μ` the row weight
  (`twist_diag_bidet`). A nonzero bideterminant has injective rows in each minor, so at most `min(s + 1, r)` rows of a
  minor of size `s + 1` lie in `S` (`sum_rowWt_le`), and `e(β) ≤ A_v` (`exp_le`).
* *The forms are kept* (`hecke_mem_forms_DeltaT`, `hecke_mem_forms_NablaT`): integrality at lattice tuples; zero off
  them; and equivariance, as `γ_v` maps the edges below `L_v` bijectively onto those below `γ_v L_v` (`isEdge_map`).
* *Freeness* (`forms_free_DeltaT`, `forms_free_NablaT`): if every lattice tuple is `γ·L₀` for a unique `γ ∈ Γ` and
  `L₀` in a finite set `R` (finitely many classes, trivial stabilisers), then `M` and `M∇` are free `O`-modules of rank
  `|R|·dim ∇`. A form is determined by its values at `R`, and any values in `Δ_{L₀}` (resp. `∇_{L₀}`) extend
  (`Level.extend`, `forms_free_of`); `Δ_{L₀}` and `∇_{L₀}` are free on the twists of the dual basis `zdual` and of the
  basis `zb` of `WeylZForm` (`mem_Delta_iff`, `exists_eq_sum_zbK`).
-/

namespace InertModel

open MvPolynomial WeylFock HermForms

open scoped Matrix

noncomputable section

/-! ## The setting and the definitions -/

section Defs

/-- **The unramified setting at an inert prime `p`** with orbit length `n'`: `W` a complete discrete valuation ring
with uniformiser `p` and residue field of size `p^{n'}`, fraction field `Qq`, Frobenius `σ` (of order dividing `n'`,
lifting `x ↦ x^p`); `O ⊇ W` a discrete valuation ring with fraction field `Kf` and a uniformiser `ϖ` with `ϖ² = p`;
`ι : Qq → Kf` extends `j : W → O`. -/
structure Unram (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (ϖ : O) : Prop where
  prime : p.Prime
  frac_W : IsFractionRing W Qq
  frac_O : IsFractionRing O Kf
  unif_W : Irreducible (p : W)
  res_card : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n'
  complete_W : IsAdicComplete (Ideal.span {(p : W)}) W
  frob : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + p * y)
  period : σ ^ n' = 1
  compat : ∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)
  unif_O : Irreducible ϖ
  sq : ϖ ^ 2 = (p : O)

/-- **`O` as a subring of `Kf`.** -/
abbrev Oint (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] : Subring Kf := (algebraMap O Kf).range

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {k n' : ℕ} {V : Type}
  [Fintype V] [DecidableEq V]

/-- **The weight at position `s` of an orbit**: `λ_s` at even `s`, the dual `−λ_s ∘ rev` at odd `s` (the odd
positions are the conjugate places). -/
def lamAt (lam0 : Fin n' → Fin k → ℤ) (s : Fin n') : Fin k → ℤ :=
  if Even s.val then lam0 s else fun i => -lam0 s i.rev

/-- **The block lattice** `σ^s(L) ⊗ O` in `Kf^k` of a `W`-lattice `L` in `Qq^k`. -/
def blk (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (L : Submodule W (Fin k → Qq)) : Submodule O (Fin k → Kf) :=
  Submodule.span O ((fun v i => ι ((σ ^ s) (v i))) '' (L : Set (Fin k → Qq)))

/-- **`C` is a basis matrix of the `O`-lattice `Λ`**: invertible, with columns spanning `Λ`. -/
def IsBasisOf (Λ : Submodule O (Fin k → Kf)) (C : Matrix (Fin k) (Fin k) Kf) : Prop :=
  IsUnit C.det ∧ Λ = Submodule.span O (Set.range fun j i => C i j)

/-- **The block weights** of a tuple: block `(v, s)` has weight `lamAt (lam0 v) s`. -/
def blockWt (lam0 : V → Fin n' → Fin k → ℤ) : V × Fin n' → Fin k → ℤ := fun b => lamAt (lam0 b.1) b.2

variable (O) in
/-- **The `Δ`-lattice of a tuple** `L = (L_v)`: the `F ∈ ∇_{Kf}` that are `Δ_O`-integral in the coordinates of basis
matrices of the blocks `σ^s(L_v) ⊗ O` (the local form of `WeylFock.DeltaN`). -/
def DeltaT (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : V → Fin n' → Fin k → ℤ) (L : V → Submodule W (Fin k → Qq)) :
    Set (Pol (V × Fin n') k Kf) :=
  {F | F ∈ nabla Kf (fun b => natW (blockWt lam0 b)) ∧ ∃ C : V × Fin n' → Matrix (Fin k) (Fin k) Kf,
    (∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b)) ∧
      twist (blockWt lam0) C F ∈ Delta (Oint O Kf) fun b => natW (blockWt lam0 b)}

variable (O) in
/-- **The `∇`-lattice of a tuple**, as `DeltaT` with `∇_O` (the `O`-span of the bideterminants). -/
def NablaT (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : V → Fin n' → Fin k → ℤ) (L : V → Submodule W (Fin k → Qq)) :
    Set (Pol (V × Fin n') k Kf) :=
  {F | F ∈ nabla Kf (fun b => natW (blockWt lam0 b)) ∧ ∃ C : V × Fin n' → Matrix (Fin k) (Fin k) Kf,
    (∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b)) ∧
      twist (blockWt lam0) C F ∈ (nablaInt (Oint O Kf) fun b => natW (blockWt lam0 b) : Set (Pol _ k Kf))}

/-- **An edge of type `r`** from `L″` to `L`: lattices with `pL ⊆ L″ ⊆ L` and `[L : L″] = p^{n'r}`
(`L/L″ ≅ F_{p^{n'}}^r`). -/
def IsEdge (p r : ℕ) (L'' L : Submodule W (Fin k → Qq)) : Prop :=
  L.IsLattice Qq ∧ L''.IsLattice Qq ∧ L'' ≤ L ∧ (∀ x ∈ L, (p : W) • x ∈ L'') ∧
    Nat.card (↥L ⧸ L''.comap L.subtype) = p ^ (n' * r)

/-- **A level** at the prime: a group `Γ` acting on each orbit's `Qq^k` (the `p`-arithmetic points of the global
group) and a character `χ : Γ → O^×`. -/
structure Level (V : Type) (k : ℕ) (Qq O : Type) [Field Qq] [CommRing O] where
  /-- The group. -/
  Γ : Type
  /-- Its group structure. -/
  [grp : Group Γ]
  /-- The action on each orbit. -/
  act : V → Γ →* GL (Fin k) Qq
  /-- The character. -/
  χ : Γ →* Oˣ

attribute [instance] Level.grp

/-- **`γ` moves a tuple**: `L_v ↦ γ_v L_v`. -/
def Level.smul (C : Level V k Qq O) (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) : V → Submodule W (Fin k → Qq) :=
  fun v => (L v).map ((Matrix.mulVecLin ((C.act v γ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)

/-- **The action of `γ` on the coefficients**, `F ↦ ∏_b σ^s(det γ_v)^{−λ_{b,k−1}}·F((σ^s(γ_v)⁻¹x_b)_b)`: the twist
by the matrices `ι σ^s(γ_v⁻¹)`. -/
def Level.actF (C : Level V k Qq O) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : V → Fin n' → Fin k → ℤ) (γ : C.Γ) :
    Pol (V × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf where
  toFun := twist (blockWt lam0) fun b =>
    (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix ((C.act b.1 γ)⁻¹ : GL (Fin k) Qq).val
  map_add' := twist_add _ _
  map_smul' := twist_smul _ _

/-- **The local forms of a level** with coefficient lattices `H` (`DeltaT` or `NablaT`): functions on tuples, valued
in `H(L)` at lattice tuples, zero elsewhere, and `Γ`-equivariant with the character `χ`. -/
def Level.forms (C : Level V k Qq O) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : V → Fin n' → Fin k → ℤ)
    (H : (V → Submodule W (Fin k → Qq)) → Set (Pol (V × Fin n') k Kf)) :
    Set ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) :=
  {F | (∀ L, (∀ v, (L v).IsLattice Qq) → F L ∈ H L) ∧ (∀ L, ¬ (∀ v, (L v).IsLattice Qq) → F L = 0) ∧
    ∀ γ L, F (C.smul γ L) = algebraMap O Kf (C.χ γ : O) • C.actF ι σ lam0 γ (F L)}

/-- **`A_v = Σ_s Σ_{i<r} λ_{v,s,i}`**, the sum of the top `r` coordinates over the orbit. -/
def topSum (r : ℕ) (lam0 : V → Fin n' → Fin k → ℤ) (v : V) : ℤ :=
  ∑ s : Fin n', ∑ i : Fin k with i.val < r, lamAt (lam0 v) s i

/-- **The Hecke operator** at the orbit `v`, type `r`: `y_v F(L) = p^{A_v}·Σ_{L″ ⊂ L_v edge} F(L with L_v ↦ L″)`. -/
def hecke (p r : ℕ) (lam0 : V → Fin n' → Fin k → ℤ) (v : V)
    (F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) :
    (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf :=
  fun L => ((p : Kf) ^ topSum r lam0 v) •
    ∑ᶠ (L'' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' (L v)), F (Function.update L v L'')

end Defs

/-! ## Finiteness of the edges and commutation -/

section Finite

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **Finiteness of the edges**: there are finitely many `L″` with `pL ⊆ L″ ⊆ L`, as they are determined by their
images in the finite `L/pL`. -/
theorem finite_edges (hU : Unram p n' W Qq O Kf ι σ j ϖ) (r : ℕ) (L : Submodule W (Fin k → Qq)) :
    {L'' | IsEdge (n' := n') p r L'' L}.Finite := by
  by_cases hL : L.IsLattice Qq
  swap
  · exact Set.finite_empty.subset fun L'' h => absurd h.1 hL
  have : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hU.res_card]; exact pow_ne_zero _ hU.prime.ne_zero)
  have : Finite (↥L ⧸ Ideal.span {(p : W)} • (⊤ : Submodule W L)) :=
    Module.finite_of_finite (W ⧸ Ideal.span {(p : W)})
  have hP : ∀ {L''}, IsEdge (n' := n') p r L'' L →
      Ideal.span {(p : W)} • (⊤ : Submodule W L) ≤ L''.comap L.subtype := fun h =>
    Submodule.smul_le.2 fun a ha x _ => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul]
      exact Submodule.smul_mem _ _ (h.2.2.2.1 _ x.2)
  refine Set.Finite.of_finite_image
    (f := fun L'' => (L''.comap L.subtype).map (Ideal.span {(p : W)} • (⊤ : Submodule W L)).mkQ)
    (Set.toFinite _) fun L₁ h₁ L₂ h₂ he => ?_
  have hc : L₁.comap L.subtype = L₂.comap L.subtype := by
    have := congrArg (Submodule.comap (Ideal.span {(p : W)} • (⊤ : Submodule W L)).mkQ) he
    simpa only [Submodule.comap_map_mkQ, sup_eq_right.2 (hP h₁), sup_eq_right.2 (hP h₂)] using this
  calc L₁ = L ⊓ L₁ := (inf_eq_right.2 h₁.2.2.1).symm
    _ = (L₁.comap L.subtype).map L.subtype := (Submodule.map_comap_subtype L L₁).symm
    _ = (L₂.comap L.subtype).map L.subtype := by rw [hc]
    _ = L ⊓ L₂ := Submodule.map_comap_subtype L L₂
    _ = L₂ := inf_eq_right.2 h₂.2.2.1

omit [Fintype V] in
/-- **The Hecke operator as a finite sum** over the edges below `L_v`. -/
theorem hecke_eq_sum (hU : Unram p n' W Qq O Kf ι σ j ϖ) (r : ℕ) (lam0 : V → Fin n' → Fin k → ℤ) (v : V)
    (F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) (L : V → Submodule W (Fin k → Qq)) :
    hecke p r lam0 v F L =
      ((p : Kf) ^ topSum r lam0 v) • ∑ L'' ∈ (finite_edges hU r (L v)).toFinset, F (Function.update L v L'') := by
  rw [hecke, ← finsum_mem_eq_finite_toFinset_sum]
  rfl

omit [Fintype V] in
/-- **Commutation**: the Hecke operators at different orbits commute, as they move different coordinates. -/
theorem hecke_comm (hU : Unram p n' W Qq O Kf ι σ j ϖ) (lam0 : V → Fin n' → Fin k → ℤ) {v w : V} (hvw : v ≠ w)
    (r r' : ℕ) (F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) :
    hecke p r lam0 v (hecke p r' lam0 w F) = hecke p r' lam0 w (hecke p r lam0 v F) := by
  funext L
  have h1 : ∀ L'', Function.update L v L'' w = L w := fun L'' => Function.update_of_ne hvw.symm _ _
  have h2 : ∀ L'', Function.update L w L'' v = L v := fun L'' => Function.update_of_ne hvw _ _
  simp only [hecke_eq_sum hU, Finset.smul_sum]
  refine (Finset.sum_comm' fun L₁ L₂ => ?_).trans
    (Finset.sum_congr rfl fun L₂ _ => Finset.sum_congr rfl fun L₁ _ => ?_)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, h1, h2]
  · rw [Function.update_comm hvw, smul_comm]

end Finite

/-! ## Edge bases: Smith normal form -/

section Edge

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **A lattice is an edge of type `0` below itself.** -/
theorem isEdge_refl {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq) : IsEdge (n' := n') p 0 L L := by
  refine ⟨hL, hL, le_rfl, fun x hx => L.smul_mem _ hx, ?_⟩
  have : L.comap L.subtype = ⊤ := by simp
  rw [this, mul_zero, pow_zero]
  exact Nat.card_unique

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The basis matrix of a basis of a lattice is invertible**: its columns are a `Qq`-basis
(`Module.Basis.extendOfIsLattice`). -/
theorem isUnit_det_of_basis [IsFractionRing W Qq] {L : Submodule W (Fin k → Qq)} [L.IsLattice Qq]
    (b : Module.Basis (Fin k) W L) : IsUnit (Matrix.of fun i l => (b l : Fin k → Qq) i).det := by
  have h : LinearIndependent Qq (Matrix.of fun i l => (b l : Fin k → Qq) i).col := by
    convert (b.extendOfIsLattice Qq).linearIndependent using 1
    funext l i
    simp [Matrix.col]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h)

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The columns of the basis matrix of a basis of `L` span `L`.** -/
theorem span_cols_of_basis {L : Submodule W (Fin k → Qq)} (b : Module.Basis (Fin k) W L) :
    L = Submodule.span W (Set.range fun l i => (Matrix.of fun i l => (b l : Fin k → Qq) i) i l) := by
  have := congrArg (Submodule.map L.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
  exact this.symm

/-- **Edge bases** (Smith normal form): for an edge `L″ ⊂ L` of type `r` there are a basis matrix `B` of `L` and a
set `S` of `r` indices with `L″` spanned by the columns of `B·diag(d)`, `d_i = p` on `S` and `1` elsewhere. The
Smith normal form over `W` gives a basis `b` of `L` and `a_i` with `L″ = ⊕ a_i W b_i`; `pL ⊆ L″` makes `a_i | p`, so
`a_i` is a unit or associated to `p`, and `|L/L″| = Π |W/a_i| = q^{|S|}` (`Submodule.quotientPi`) gives `|S| = r`. -/
theorem exists_basis_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (h : IsEdge (n' := n') p r L'' L) :
    ∃ (B : Matrix (Fin k) (Fin k) Qq) (S : Finset (Fin k)), S.card = r ∧ IsUnit B.det ∧
      L = Submodule.span W (Set.range fun l i => B i l) ∧
      L'' = Submodule.span W (Set.range fun l i =>
        (B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1) i l) := by
  classical
  have := hU.frac_W
  have := h.1
  have := h.2.1
  have hk : Module.finrank W L = k := by rw [Submodule.IsLattice.finrank_of_pi Qq L, Fintype.card_fin]
  have hk'' : Module.finrank W (L''.comap L.subtype) = Module.finrank W L := by
    rw [(Submodule.comapSubtypeEquivOfLe h.2.2.1).finrank_eq, Submodule.IsLattice.finrank_of_pi Qq L'', hk,
      Fintype.card_fin]
  obtain ⟨b, a, ab, hab⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Module.finBasisOfFinrankEq W L hk) hk''
  -- membership in `L″` through the coordinates in `b`
  have hmem : ∀ y : L, y ∈ L''.comap L.subtype ↔ ∀ i, a i ∣ b.repr y i := fun y => by
    refine ⟨fun hy i => ?_, fun hy => ?_⟩
    · have e : y = ∑ l, (ab.repr ⟨y, hy⟩ l * a l) • b l := by
        have := congrArg (Submodule.subtype _) (ab.sum_repr ⟨y, hy⟩)
        simp only [map_sum, map_smul, Submodule.subtype_apply, hab, smul_smul] at this
        exact this.symm
      rw [e, b.repr_sum_self]
      exact Dvd.intro_left _ rfl
    · choose t ht using hy
      rw [← b.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [ht i, mul_comm, mul_smul, ← hab i]
      exact Submodule.smul_mem _ _ (ab i).2
  have hdvd : ∀ i, a i ∣ (p : W) := fun i => by
    have hpi : ((p : W) • b i) ∈ L''.comap L.subtype := h.2.2.2.1 _ (b i).2
    simpa using (hmem _).1 hpi i
  set S := Finset.univ.filter fun i => ¬ IsUnit (a i) with hSdef
  set d : Fin k → W := fun i => if i ∈ S then (p : W) else 1 with hd
  have hass : ∀ i, Associated (a i) (d i) := fun i => by
    by_cases hi : IsUnit (a i)
    · simp only [hd, hSdef, Finset.mem_filter, Finset.mem_univ, true_and, hi, not_true_eq_false, ↓reduceIte]
      exact associated_one_iff_isUnit.2 hi
    · simp only [hd, hSdef, Finset.mem_filter, Finset.mem_univ, true_and, hi, not_false_eq_true, ↓reduceIte]
      obtain ⟨c, hc⟩ := hdvd i
      obtain ⟨u, rfl⟩ := (hU.unif_W.isUnit_or_isUnit hc).resolve_left hi
      exact ⟨u, hc.symm⟩
  have hmem' : ∀ y : L, y ∈ L''.comap L.subtype ↔ ∀ i, d i ∣ b.repr y i := fun y => by
    rw [hmem]
    exact forall_congr' fun i => (hass i).dvd_iff_dvd_left
  -- the index
  have hmap : (L''.comap L.subtype).map (b.equivFun : ↥L →ₗ[W] Fin k → W) =
      Submodule.pi Set.univ fun i => Ideal.span {d i} := by
    ext y
    rw [Submodule.mem_map_equiv, hmem', Submodule.mem_pi, Module.Basis.equivFun_symm_apply, b.repr_sum_self]
    simp [Ideal.mem_span_singleton]
  have hcard : Nat.card (↥L ⧸ L''.comap L.subtype) = ∏ i, Nat.card (W ⧸ Ideal.span {d i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr ((Submodule.Quotient.equiv _ _ b.equivFun hmap).trans (Submodule.quotientPi _)).toEquiv
  have hci : ∀ i, Nat.card (W ⧸ Ideal.span {d i}) = if i ∈ S then p ^ n' else 1 := fun i => by
    by_cases hi : i ∈ S
    · simp only [hd, hi, ↓reduceIte, hU.res_card]
    · simp only [hd, hi, ↓reduceIte, Ideal.span_singleton_one]
      have : Subsingleton (W ⧸ (⊤ : Ideal W)) := Ideal.Quotient.subsingleton_iff.2 rfl
      exact Nat.card_unique
  have hn' : n' ≠ 0 := by
    rintro rfl
    have h1 := hU.res_card
    rw [pow_zero, Nat.card_eq_one_iff_unique] at h1
    exact hU.unif_W.not_isUnit (Ideal.span_singleton_eq_top.1 (Ideal.Quotient.subsingleton_iff.1 h1.1))
  have hr : S.card = r := by
    have h2 := h.2.2.2.2
    rw [hcard, Finset.prod_congr rfl fun i _ => hci i, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      ← pow_mul] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn') (Nat.pow_right_injective hU.prime.two_le h2)
  -- the spans
  have hL'' : L'' = Submodule.span W (Set.range fun l => ((d l • b l : L) : Fin k → Qq)) := by
    apply le_antisymm
    · intro x hx
      have hy : (⟨x, h.2.2.1 hx⟩ : L) ∈ L''.comap L.subtype := hx
      choose t ht using (hmem' _).1 hy
      have e := congrArg L.subtype (b.sum_repr ⟨x, h.2.2.1 hx⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply, ht] at e
      rw [← e]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [mul_comm, mul_smul, ← Submodule.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : (d i • b i : L) ∈ L''.comap L.subtype := (hmem' _).2 fun l => by
        rw [map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with hl
        · subst hl
          simp
        · simp
      exact this
  refine ⟨Matrix.of fun i l => (b l : Fin k → Qq) i, S, hr, isUnit_det_of_basis b, span_cols_of_basis b, ?_⟩
  rw [hL'']
  congr 2
  funext l i
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, hd]
  split_ifs <;> simp [mul_comm]

end Edge

/-! ## Basis matrices of the blocks; the choice does not matter -/

section Blocks

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **`ι ∘ σ^s` maps `W` into `O`**: `σ` keeps `W`, as it lifts the Frobenius, and `ι` extends `j`. -/
theorem Unram.exists_map_eq (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) (x : W) :
    ∃ o : O, ι ((σ ^ s) (algebraMap W Qq x)) = algebraMap O Kf o := by
  have key : ∀ x : W, ∃ y : W, (σ ^ s) (algebraMap W Qq x) = algebraMap W Qq y := by
    induction s with
    | zero => exact fun x => ⟨x, by rw [pow_zero]; rfl⟩
    | succ s ih =>
      intro x
      obtain ⟨y, hy⟩ := hU.frob x
      obtain ⟨z, hz⟩ := ih (x ^ p + p * y)
      exact ⟨z, by rw [pow_succ]; exact (congrArg (σ ^ s) hy).trans hz⟩
  obtain ⟨y, hy⟩ := key x
  exact ⟨j y, by rw [hy, hU.compat]⟩

/-- **Basis matrices of the blocks**: if the columns of `B` are a basis of `L`, then `ι σ^s(B)` is a basis matrix of
`σ^s(L) ⊗ O`. -/
theorem isBasisOf_blk (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) {L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det) (hL : L = Submodule.span W (Set.range fun l i => B i l)) :
    IsBasisOf (blk (O := O) ι σ s L) ((ι.comp (σ ^ s).toRingHom).mapMatrix B) := by
  refine ⟨by rw [← RingHom.map_det]; exact hB.map _, le_antisymm ?_ ?_⟩
  · rw [blk, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe]
    rw [hL] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact Submodule.subset_span ⟨l, rfl⟩
    | zero =>
      convert (Submodule.span O _).zero_mem using 1
      funext i
      simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext i
      simp
    | smul a x _ hx =>
      obtain ⟨o, ho⟩ := hU.exists_map_eq s a
      convert Submodule.smul_mem _ o hx using 1
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, ho]
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨fun i => B i l, hL ▸ Submodule.subset_span ⟨l, rfl⟩, rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Two basis matrices of one lattice differ by `GL_k(O)`**: `C' = C·U` with `U·V = 1`, `U`, `V` over `O`. -/
theorem exists_mul_eq_of_isBasisOf {Λ : Submodule O (Fin k → Kf)} {C C' : Matrix (Fin k) (Fin k) Kf}
    (hC : IsBasisOf Λ C) (hC' : IsBasisOf Λ C') :
    ∃ U V : Matrix (Fin k) (Fin k) Kf, (∀ i l, U i l ∈ Oint O Kf) ∧ (∀ i l, V i l ∈ Oint O Kf) ∧ C' = C * U ∧
      U * V = 1 := by
  have key : ∀ {C C' : Matrix (Fin k) (Fin k) Kf}, Submodule.span O (Set.range fun l i => C' i l) ≤
      Submodule.span O (Set.range fun l i => C i l) →
      ∃ U : Matrix (Fin k) (Fin k) Kf, (∀ i l, U i l ∈ Oint O Kf) ∧ C' = C * U := by
    intro C C' h
    have hj : ∀ l, ∃ c : Fin k → O, ∑ m, c m • (fun i => C i m) = fun i => C' i l := fun l =>
      (Submodule.mem_span_range_iff_exists_fun O).1 (h (Submodule.subset_span ⟨l, rfl⟩))
    choose c hc using hj
    refine ⟨Matrix.of fun m l => algebraMap O Kf (c l m), fun m l => ⟨c l m, rfl⟩, ?_⟩
    ext i l
    have := congrFun (hc l) i
    simp only [Finset.sum_apply, Algebra.smul_def] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, ← this]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  obtain ⟨U, hU, hCU⟩ := key (C := C) (C' := C') (le_of_eq (by rw [← hC.2, ← hC'.2]))
  obtain ⟨V, hV, hCV⟩ := key (C := C') (C' := C) (le_of_eq (by rw [← hC.2, ← hC'.2]))
  refine ⟨U, V, hU, hV, hCU, ?_⟩
  have h1 : C * (U * V) = C * 1 := by rw [← Matrix.mul_assoc, ← hCU, ← hCV, Matrix.mul_one]
  calc U * V = C⁻¹ * C * (U * V) := by rw [Matrix.nonsing_inv_mul _ hC.1, Matrix.one_mul]
    _ = 1 := by rw [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hC.1]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`∇_O` is kept by a twist by `GL_k(O)`**: a bideterminant goes to an `O`-combination of bideterminants
(`lsub_bidet`), the determinant factor being a unit. -/
theorem twist_mem_nablaInt {Φ : Type} [Fintype Φ] [DecidableEq Φ] (lam : Φ → Fin k → ℤ)
    {U V : Φ → Matrix (Fin k) (Fin k) Kf} (hU : ∀ b i l, U b i l ∈ Oint O Kf) (hV : ∀ b i l, V b i l ∈ Oint O Kf)
    (hUV : ∀ b, U b * V b = 1) {ν : Φ → Fin k → ℕ} {G : Pol Φ k Kf}
    (hG : G ∈ (nablaInt (Oint O Kf) ν : Set (Pol Φ k Kf))) :
    twist lam U G ∈ (nablaInt (Oint O Kf) ν : Set (Pol Φ k Kf)) := by
  rw [SetLike.mem_coe, nablaInt] at hG ⊢
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨rows, rfl⟩ := hx
    rw [twist, lsub_bidet, Finset.mul_sum]
    refine Submodule.sum_mem _ fun rows' _ => ?_
    rw [← mul_assoc, ← C_mul, ← smul_eq_C_mul]
    have hc : (∏ b, (U b).det ^ detShift (lam b)) *
        ∏ τ, ∏ s, ∏ c, ∏ i, U τ (rows τ s c i) (rows' τ s c i) ∈ Oint O Kf :=
      Subring.mul_mem _ (Subring.prod_mem _ fun b _ => det_zpow_mem_of_mul_eq_one (hU b) (hV b) (hUV b) _)
        (Subring.prod_mem _ fun τ _ => Subring.prod_mem _ fun s _ => Subring.prod_mem _ fun c _ =>
          Subring.prod_mem _ fun i _ => hU _ _ _)
    exact Submodule.smul_mem _ (⟨_, hc⟩ : Oint O Kf) (Submodule.subset_span ⟨rows', rfl⟩)
  | zero =>
    simp only [twist, map_zero, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [twist_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, twist_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`Δ_L` in any basis**: membership in `DeltaT` can be tested in any basis matrices of the blocks. -/
theorem mem_DeltaT_iff {lam0 : V → Fin n' → Fin k → ℤ} {L : V → Submodule W (Fin k → Qq)}
    {C : V × Fin n' → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b))
    {F : Pol (V × Fin n') k Kf} :
    F ∈ DeltaT O ι σ lam0 L ↔ F ∈ nabla Kf (fun b => natW (blockWt lam0 b)) ∧
      twist (blockWt lam0) C F ∈ Delta (Oint O Kf) fun b => natW (blockWt lam0 b) := by
  refine ⟨fun ⟨hF, C', hC', hD⟩ => ⟨hF, ?_⟩, fun h => ⟨h.1, C, hC, h.2⟩⟩
  choose U V hU hV hCU hUV using fun b => exists_mul_eq_of_isBasisOf (hC' b) (hC b)
  have e : twist (blockWt lam0) C F = twist (blockWt lam0) U (twist (blockWt lam0) C' F) := by
    rw [twist_twist]
    exact congrArg (twist (blockWt lam0) · F) (funext hCU)
  rw [e]
  exact (twist_mem_Delta_iff _ hU hV hUV).2 hD

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`∇_L` in any basis**: membership in `NablaT` can be tested in any basis matrices of the blocks. -/
theorem mem_NablaT_iff {lam0 : V → Fin n' → Fin k → ℤ} {L : V → Submodule W (Fin k → Qq)}
    {C : V × Fin n' → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b))
    {F : Pol (V × Fin n') k Kf} :
    F ∈ NablaT O ι σ lam0 L ↔ F ∈ nabla Kf (fun b => natW (blockWt lam0 b)) ∧
      twist (blockWt lam0) C F ∈ (nablaInt (Oint O Kf) fun b => natW (blockWt lam0 b) : Set (Pol _ k Kf)) := by
  refine ⟨fun ⟨hF, C', hC', hD⟩ => ⟨hF, ?_⟩, fun h => ⟨h.1, C, hC, h.2⟩⟩
  choose U V hU hV hCU hUV using fun b => exists_mul_eq_of_isBasisOf (hC' b) (hC b)
  have e : twist (blockWt lam0) C F = twist (blockWt lam0) U (twist (blockWt lam0) C' F) := by
    rw [twist_twist]
    exact congrArg (twist (blockWt lam0) · F) (funext hCU)
  rw [e]
  exact twist_mem_nablaInt _ hU hV hUV hD

end Blocks

/-! ## Diagonal twists: the scaling of bideterminants -/

section Scale

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {k : ℕ} {Kf : Type} [Field Kf]

/-- **The diagonal of an edge twist**: `x` at the indices `i ∈ S_b` of block `b`, `1` elsewhere. -/
def dg (S : Φ → Finset (Fin k)) (x : Kf) : Φ → Fin k → Kf := fun b i => if i ∈ S b then x else 1

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A product of integer powers of one nonzero `x`** is the power of the sum of the exponents. -/
theorem prod_zpow_eq {x : Kf} (hx : x ≠ 0) {ι' : Type} (s : Finset ι') (e : ι' → ℤ) :
    ∏ b ∈ s, x ^ e b = x ^ ∑ b ∈ s, e b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

omit [DecidableEq Φ] in
/-- **The factor of a diagonal twist** on a row-homogeneous polynomial of row weight `μ`: `x^e`, with
`e = Σ_b (|S_b|·s_b + Σ_{i∈S_b} μ_{b,i})`. -/
theorem prod_dg {x : Kf} (hx : x ≠ 0) (S : Φ → Finset (Fin k)) (s : Φ → ℤ) (μ : Φ → Fin k → ℕ) :
    ∏ b, ((∏ i, dg S x b i) ^ s b * ∏ i, dg S x b i ^ μ b i) =
      x ^ ∑ b, (((S b).card : ℤ) * s b + ∑ i ∈ S b, (μ b i : ℤ)) := by
  rw [← prod_zpow_eq hx]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h1 : ∏ i, dg S x b i = x ^ (S b).card := by
    simp only [dg]
    rw [Finset.prod_ite_mem Finset.univ (S b) fun _ => x, Finset.univ_inter, Finset.prod_const]
  have h2 : ∏ i, dg S x b i ^ μ b i = x ^ ∑ i ∈ S b, μ b i := by
    simp only [dg, ite_pow, one_pow]
    rw [Finset.prod_ite_mem Finset.univ (S b) fun i => x ^ μ b i, Finset.univ_inter, Finset.prod_pow_eq_pow_sum]
  rw [h1, h2, ← zpow_natCast x (S b).card, ← zpow_mul, ← zpow_natCast x (∑ i ∈ S b, μ b i), ← zpow_add₀ hx]
  push_cast
  ring_nf

/-- **A diagonal twist scales a bideterminant** by `x^{e(β)}`, `e(β) = Σ_b (|S_b|·λ_{b,k−1} + Σ_{i∈S_b} μ_{b,i})`,
`μ` its row weight (`twist_diagonal_of_isWH`). -/
theorem twist_diag_bidet {x : Kf} (hx : x ≠ 0) (lam : Φ → Fin k → ℤ) (S : Φ → Finset (Fin k))
    {ν : Φ → Fin k → ℕ} (rows : BRows Φ k ν) :
    twist lam (fun b => Matrix.diagonal (dg S x b)) (bidet Kf ν rows) =
      (x ^ ∑ b, (((S b).card : ℤ) * detShift (lam b) + ∑ i ∈ S b, (rowWt rows b i : ℤ))) • bidet Kf ν rows := by
  rw [twist_diagonal_of_isWH lam (bidet_isWH_rowW rows), prod_dg hx]

/-- **Diagonal twists are self-adjoint** for the bilinear Fock form (`fock_lsub`). -/
theorem fock_twist_diag (lam : Φ → Fin k → ℤ) (a : Φ → Fin k → Kf) (P Q : Pol Φ k Kf) :
    fockWith (RingHom.id Kf) (twist lam (fun b => Matrix.diagonal (a b)) P) Q =
      fockWith (RingHom.id Kf) P (twist lam (fun b => Matrix.diagonal (a b)) Q) := by
  simp only [twist, fock_C_mul_left, fock_C_mul_right]
  congr 1
  have := fock_lsub (fun b => Matrix.diagonal (a b)) P Q
  simpa only [Matrix.diagonal_transpose] using this

omit [DecidableEq Φ] in
/-- **A nonzero bideterminant has injective rows** in each of its minors: a minor with two equal rows is `0`. -/
theorem injective_rows {ν : Φ → Fin k → ℕ} {rows : BRows Φ k ν} (h : bidet Kf ν rows ≠ 0) (b : Φ)
    (s : Fin k) (c : Fin (mult (ν b) s)) : Function.Injective (rows b s c) := by
  intro t t' htt'
  by_contra hne
  refine h (Finset.prod_eq_zero (Finset.mem_univ b) (Finset.prod_eq_zero (Finset.mem_univ s)
    (Finset.prod_eq_zero (Finset.mem_univ c) ?_)))
  exact Matrix.det_zero_of_row_eq hne (by funext l; simp [htt'])

omit [DecidableEq Φ] in
/-- **The row bound**: in each block, a nonzero bideterminant of antitone shape `ν` has at most
`Σ_{i<|S|} ν_{b,i}` of its rows in `S`: a minor of size `s + 1` has at most `min(s + 1, |S|)` rows in `S`, and
`Σ_{i<|S|} ν_{b,i} = Σ_s (ν_s − ν_{s+1})·min(s + 1, |S|)`. -/
theorem sum_rowWt_le {ν : Φ → Fin k → ℕ} (hν : ∀ b, Antitone (ν b)) {rows : BRows Φ k ν}
    (h : bidet Kf ν rows ≠ 0) (b : Φ) (S : Finset (Fin k)) :
    ∑ i ∈ S, rowWt rows b i ≤ ∑ i : Fin k with i.val < S.card, ν b i := by
  classical
  have hL : ∑ i ∈ S, rowWt rows b i = ∑ s, ∑ c, (Finset.univ.filter fun t => rows b s c t ∈ S).card := by
    simp only [rowWt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm, Finset.card_filter]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_ite_eq S (rows b s c t) fun _ => 1
  have hν' : ∀ i, ν b i = ∑ s : Fin k, mult (ν b) s * if (i : ℕ) ≤ s then 1 else 0 := fun i => by
    have := congrFun (congrFun (sum_mult (Φ := Unit) (ν := fun _ => ν b) fun _ => hν b) ()) i
    simpa [Finset.sum_apply, Pi.single_apply] using this.symm
  have hR : ∑ i : Fin k with i.val < S.card, ν b i =
      ∑ s, mult (ν b) s * (Finset.univ.filter fun i : Fin k => i.val < min S.card (s.val + 1)).card := by
    rw [Finset.sum_congr rfl fun i _ => hν' i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, Finset.filter_filter]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.lt_min]
    omega
  rw [hL, hR]
  refine Finset.sum_le_sum fun s _ => ?_
  calc ∑ c, (Finset.univ.filter fun t => rows b s c t ∈ S).card
      ≤ ∑ _c : Fin (mult (ν b) s), (Finset.univ.filter fun i : Fin k => i.val < min S.card (s.val + 1)).card :=
        Finset.sum_le_sum fun c _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.card_filter_val_lt, min_eq_right (by have := s.isLt; omega)]
  refine le_min (Finset.card_le_card_of_injOn (rows b s c) (fun t ht => ?_)
    (injective_rows h b s c).injOn) ((Finset.card_filter_le _ _).trans (by simp))
  simpa using ht

omit [DecidableEq Φ] in
/-- **The exponent bound**: for antitone weights and a nonzero bideterminant `β`, the exponent `e(β)` of the
diagonal twist is at most `Σ_b Σ_{i<|S_b|} λ_{b,i}`. -/
theorem exp_le {lam : Φ → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) (S : Φ → Finset (Fin k))
    {rows : BRows Φ k fun b => natW (lam b)} (h : bidet Kf (fun b => natW (lam b)) rows ≠ 0) :
    ∑ b, (((S b).card : ℤ) * detShift (lam b) + ∑ i ∈ S b, (rowWt rows b i : ℤ)) ≤
      ∑ b, ∑ i : Fin k with i.val < (S b).card, lam b i := by
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 : ∑ i ∈ S b, (rowWt rows b i : ℤ) ≤ ∑ i : Fin k with i.val < (S b).card, (natW (lam b) i : ℤ) := by
    exact_mod_cast sum_rowWt_le (fun b => natW_antitone (hlam b)) h b (S b)
  have h2 : ∑ i : Fin k with i.val < (S b).card, lam b i =
      ∑ i : Fin k with i.val < (S b).card, (natW (lam b) i : ℤ) + (S b).card * detShift (lam b) := by
    rw [← Finset.sum_congr rfl fun i _ => natW_add_detShift (hlam b) i, Finset.sum_add_distrib, Finset.sum_const,
      Fin.card_filter_val_lt, min_eq_right (by simpa using Finset.card_le_univ (S b)), nsmul_eq_mul]
  rw [h2]
  linarith

/-- **Integrality through a diagonal twist, `Δ`**: if the twist of `G ∈ ∇` by `diag(dg S x)` is in `Δ_A`, then
`x^{Σ_b Σ_{i<|S_b|} λ_{b,i}}·G ∈ Δ_A`: against a bideterminant `β`, the twist multiplies the pairing by
`x^{e(β)}`, and `e(β)` is at most the exponent (`exp_le`). -/
theorem smul_mem_Delta_of_twist_diag {A : Subring Kf} {x : Kf} (hx : x ≠ 0) (hxA : x ∈ A)
    {lam : Φ → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) (S : Φ → Finset (Fin k)) {G : Pol Φ k Kf}
    (hG : G ∈ nabla Kf fun b => natW (lam b))
    (h : twist lam (fun b => Matrix.diagonal (dg S x b)) G ∈ Delta A fun b => natW (lam b)) :
    x ^ (∑ b, ∑ i : Fin k with i.val < (S b).card, lam b i) • G ∈ Delta A fun b => natW (lam b) := by
  refine ⟨Submodule.smul_mem _ _ hG, fun rows => ?_⟩
  by_cases h0 : bidet Kf (fun b => natW (lam b)) rows = 0
  · rw [h0, fock_zero_right, zero_div]
    exact A.zero_mem
  have hD := h.2 rows
  rw [fock_twist_diag, twist_diag_bidet hx, fock_smul_right] at hD
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (exp_le hlam S h0))
  have hE : x ^ (∑ b, ∑ i : Fin k with i.val < (S b).card, lam b i) =
      x ^ N * x ^ ∑ b, (((S b).card : ℤ) * detShift (lam b) + ∑ i ∈ S b, (rowWt rows b i : ℤ)) := by
    rw [← zpow_natCast, ← hN, ← zpow_add₀ hx, sub_add_cancel]
  rw [fock_smul_left, hE, mul_assoc, mul_div_assoc]
  exact A.mul_mem (A.pow_mem hxA N) hD

/-- **Integrality through a diagonal twist, `∇`**: if the twist of `G` by `diag(dg S x)` is in `∇_A`, then
`x^{Σ_b Σ_{i<|S_b|} λ_{b,i}}·G ∈ ∇_A`: `G` is the twist back by `diag(dg S x⁻¹)`, which scales a bideterminant `β`
by `x^{−e(β)}`. -/
theorem smul_mem_nablaInt_of_twist_diag {A : Subring Kf} {x : Kf} (hx : x ≠ 0) (hxA : x ∈ A)
    {lam : Φ → Fin k → ℤ} (hlam : ∀ b, Antitone (lam b)) (S : Φ → Finset (Fin k)) {G : Pol Φ k Kf}
    (h : twist lam (fun b => Matrix.diagonal (dg S x b)) G ∈ (nablaInt A fun b => natW (lam b) : Set (Pol Φ k Kf))) :
    x ^ (∑ b, ∑ i : Fin k with i.val < (S b).card, lam b i) • G ∈
      (nablaInt A fun b => natW (lam b) : Set (Pol Φ k Kf)) := by
  have hinv : G = twist lam (fun b => Matrix.diagonal (dg S x⁻¹ b))
      (twist lam (fun b => Matrix.diagonal (dg S x b)) G) := by
    rw [twist_twist]
    have e : (fun b => Matrix.diagonal (dg S x b) * Matrix.diagonal (dg S x⁻¹ b)) = fun _ => 1 := by
      funext b
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simp only [dg]
      split_ifs <;> simp [hx]
    rw [e, twist_one]
  rw [hinv]
  generalize twist lam (fun b => Matrix.diagonal (dg S x b)) G = H at h ⊢
  rw [SetLike.mem_coe, nablaInt] at h ⊢
  induction h using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨rows, rfl⟩ := hy
    by_cases h0 : bidet Kf (fun b => natW (lam b)) rows = 0
    · rw [h0]
      simp only [twist, map_zero, mul_zero, smul_zero]
      exact zero_mem _
    rw [twist_diag_bidet (inv_ne_zero hx), smul_smul, inv_zpow', ← zpow_add₀ hx, ← sub_eq_add_neg]
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (exp_le hlam S h0))
    rw [hN, zpow_natCast]
    exact Submodule.smul_mem _ (⟨x ^ N, A.pow_mem hxA N⟩ : A) (Submodule.subset_span ⟨rows, rfl⟩)
  | zero =>
    simp only [twist, map_zero, mul_zero, smul_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [twist_add, smul_add]
    exact add_mem hy hz
  | smul a y _ hy =>
    rw [Subring.smul_def, twist_smul, smul_comm, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hy

end Scale

/-! ## Integrality: `p^{A_v}·Δ_{L″} ⊆ Δ_L` and `p^{A_v}·∇_{L″} ⊆ ∇_L` -/

section Integral

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- **Dominant weights give antitone block weights**: the dual `−λ ∘ rev` of an antitone `λ` is antitone. -/
theorem antitone_blockWt {lam0 : V → Fin n' → Fin k → ℤ} (hlam : ∀ v s, Antitone (lam0 v s)) (b : V × Fin n') :
    Antitone (blockWt lam0 b) := by
  simp only [blockWt, lamAt]
  split_ifs
  · exact hlam _ _
  · intro i l hil
    exact neg_le_neg (hlam b.1 b.2 (Fin.rev_le_rev.2 hil))

omit [Fintype V] [DecidableEq V] in
/-- **`p ≠ 0` in `Qq`**: `p` is irreducible in `W ⊆ Qq`. -/
theorem Unram.cast_ne_zero (hU : Unram p n' W Qq O Kf ι σ j ϖ) : (p : Qq) ≠ 0 := by
  have := hU.frac_W
  rw [← map_natCast (algebraMap W Qq)]
  exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).2 hU.unif_W.ne_zero

omit [Fintype V] [DecidableEq V] in
/-- **`p ≠ 0` in `Kf`.** -/
theorem Unram.castK_ne_zero (hU : Unram p n' W Qq O Kf ι σ j ϖ) : (p : Kf) ≠ 0 := by
  rw [← map_natCast ι]
  exact (map_ne_zero ι).2 hU.cast_ne_zero

omit [Fintype V] [DecidableEq V] in
/-- **Basis matrices of the blocks of a lattice tuple** exist. -/
theorem exists_basis_tuple (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L : V → Submodule W (Fin k → Qq)}
    (hL : ∀ w, (L w).IsLattice Qq) :
    ∃ C : V × Fin n' → Matrix (Fin k) (Fin k) Kf, ∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b) := by
  choose B S _ hB hLB _ using fun w => exists_basis_edge hU (isEdge_refl (n' := n') (p := p) (hL w))
  exact ⟨fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix (B b.1), fun b => isBasisOf_blk hU _ (hB b.1) (hLB b.1)⟩

omit [Fintype V] in
/-- **Edge bases for tuples**: for tuples `L′ = L` off `v` with `L′_v ⊂ L_v` an edge of type `r`, there are basis
matrices `C` of the blocks of `L` such that the `C·diag(dg S p)` are basis matrices of the blocks of `L′`, with
`|S_b| = r` on the blocks of `v` and `0` elsewhere. -/
theorem exists_basis_edge_tuple (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L L' : V → Submodule W (Fin k → Qq)}
    (hL : ∀ w, (L w).IsLattice Qq) {v : V} {r : ℕ} (hL' : ∀ w, w ≠ v → L' w = L w)
    (he : IsEdge (n' := n') p r (L' v) (L v)) :
    ∃ (C : V × Fin n' → Matrix (Fin k) (Fin k) Kf) (S : V → Finset (Fin k)),
      (∀ w, (S w).card = if w = v then r else 0) ∧ (∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (C b)) ∧
      ∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L' b.1)) (C b * Matrix.diagonal (dg (fun b => S b.1) (p : Kf) b)) := by
  have hedge : ∀ w, IsEdge (n' := n') p (if w = v then r else 0) (L' w) (L w) := fun w => by
    split_ifs with hw
    · subst hw
      exact he
    · rw [hL' w hw]
      exact isEdge_refl (hL w)
  choose B S hS hB hLB hL'B using fun w => exists_basis_edge hU (hedge w)
  refine ⟨fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix (B b.1), S, hS,
    fun b => isBasisOf_blk hU _ (hB b.1) (hLB b.1), fun b => ?_⟩
  have hdet : IsUnit (B b.1 * Matrix.diagonal fun i => if i ∈ S b.1 then (p : Qq) else 1).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    refine (hB b.1).mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
    split_ifs
    · exact hU.cast_ne_zero
    · exact one_ne_zero
  convert isBasisOf_blk (O := O) hU b.2.val hdet (hL'B b.1) using 1
  rw [map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal _), Matrix.diagonal_map (map_zero _)]
  congr 2
  funext i
  simp only [dg]
  split_ifs <;> simp

/-- **The exponent of the edge twist is `A_v`**: `Σ_b Σ_{i<|S_b|} λ_{b,i} = topSum r lam0 v` when `|S_b| = r` on the
blocks of `v` and `0` elsewhere. -/
theorem sum_blockWt_eq_topSum (lam0 : V → Fin n' → Fin k → ℤ) {S : V → Finset (Fin k)} {v : V} {r : ℕ}
    (hS : ∀ w, (S w).card = if w = v then r else 0) :
    ∑ b : V × Fin n', ∑ i : Fin k with i.val < (S b.1).card, blockWt lam0 b i = topSum r lam0 v := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v (fun w _ hw => by simp [hS, hw]) (by simp)]
  simp only [hS]
  rfl

/-- **Integrality, `Δ`**: `p^{A_v}·Δ_{L′} ⊆ Δ_L` for tuples `L′ = L` off `v` with `L′_v ⊂ L_v` an edge of type `r`,
and dominant weights. In edge bases, `Δ_{L′}` is the twist of `Δ_L` by `diag(dg S p)`
(`smul_mem_Delta_of_twist_diag`). -/
theorem smul_mem_DeltaT_of_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L L' : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq)
    {v : V} {r : ℕ} (hL' : ∀ w, w ≠ v → L' w = L w) (he : IsEdge (n' := n') p r (L' v) (L v))
    {F : Pol (V × Fin n') k Kf} (hF : F ∈ DeltaT O ι σ lam0 L') :
    ((p : Kf) ^ topSum r lam0 v) • F ∈ DeltaT O ι σ lam0 L := by
  obtain ⟨C, S, hS, hC, hC'⟩ := exists_basis_edge_tuple (O := O) hU hL hL' he
  obtain ⟨hFn, hFD⟩ := (mem_DeltaT_iff hC').1 hF
  rw [← twist_twist] at hFD
  have key := smul_mem_Delta_of_twist_diag hU.castK_ne_zero
    (natCast_mem _ p) (antitone_blockWt hlam) _ (twist_mem_nabla _ _ hFn) hFD
  rw [sum_blockWt_eq_topSum lam0 hS, ← twist_smul] at key
  exact (mem_DeltaT_iff hC).2 ⟨Submodule.smul_mem _ _ hFn, key⟩

/-- **Integrality, `∇`**: `p^{A_v}·∇_{L′} ⊆ ∇_L` for tuples `L′ = L` off `v` with `L′_v ⊂ L_v` an edge of type `r`,
and dominant weights (`smul_mem_nablaInt_of_twist_diag`). -/
theorem smul_mem_NablaT_of_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L L' : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq)
    {v : V} {r : ℕ} (hL' : ∀ w, w ≠ v → L' w = L w) (he : IsEdge (n' := n') p r (L' v) (L v))
    {F : Pol (V × Fin n') k Kf} (hF : F ∈ NablaT O ι σ lam0 L') :
    ((p : Kf) ^ topSum r lam0 v) • F ∈ NablaT O ι σ lam0 L := by
  obtain ⟨C, S, hS, hC, hC'⟩ := exists_basis_edge_tuple (O := O) hU hL hL' he
  obtain ⟨hFn, hFD⟩ := (mem_NablaT_iff hC').1 hF
  rw [← twist_twist] at hFD
  have key := smul_mem_nablaInt_of_twist_diag hU.castK_ne_zero
    (natCast_mem _ p) (antitone_blockWt hlam) _ hFD
  rw [sum_blockWt_eq_topSum lam0 hS, ← twist_smul] at key
  exact (mem_NablaT_iff hC).2 ⟨Submodule.smul_mem _ _ hFn, key⟩

end Integral

/-! ## The Hecke operators keep the integral forms -/

section Hecke

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`g ∈ GL_k(Qq)` maps lattices to lattices.** -/
theorem isLattice_map (g : GL (Fin k) Qq) {N : Submodule W (Fin k → Qq)} (hN : N.IsLattice Qq) :
    (N.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)).IsLattice Qq := by
  refine ⟨hN.fg.map _, ?_⟩
  rw [Submodule.map_coe, show ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W :
    (Fin k → Qq) → Fin k → Qq) = Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq) from rfl, Submodule.span_image,
    hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) *ᵥ y, by simp [Matrix.mulVec_mulVec]⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`g ∈ GL_k(Qq)` maps edges to edges**: lattices to lattices, and `L/L″ ≅ gL/gL″`. -/
theorem isEdge_map (g : GL (Fin k) Qq) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (h : IsEdge (n' := n') p r L'' L) :
    IsEdge (n' := n') p r (L''.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W))
      (L.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)) := by
  set f := (Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W with hf
  have hinj : Function.Injective f := fun x y hxy => by
    have := congrArg (fun z => ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) *ᵥ z) hxy
    simpa [hf, Matrix.mulVec_mulVec] using this
  refine ⟨isLattice_map g h.1, isLattice_map g h.2.1, Submodule.map_mono h.2.2.1, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, h.2.2.2.1 x hx, map_smul f _ x⟩
  · rw [← h.2.2.2.2]
    refine Nat.card_congr (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hinj L) ?_).toEquiv.symm
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, hxP, hxy⟩
      exact ⟨x, hxP, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, h.2.2.1 hx⟩, hx, rfl⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`g⁻¹` undoes `g`** on submodules. -/
theorem map_map_inv (g : GL (Fin k) Qq) (N : Submodule W (Fin k → Qq)) :
    (N.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)).map
      ((Matrix.mulVecLin ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = N := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id N
  refine LinearMap.ext fun x => ?_
  simp [Matrix.mulVec_mulVec]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [Fintype V] in
/-- **Moving a tuple commutes with replacing its `v`-entry**, the new entry moved by `γ_v`. -/
theorem update_smul (C : Level V k Qq O) (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) (v : V)
    (L'' : Submodule W (Fin k → Qq)) :
    Function.update (C.smul γ L) v
      (L''.map ((Matrix.mulVecLin ((C.act v γ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)) =
      C.smul γ (Function.update L v L'') := by
  funext w
  by_cases hw : w = v
  · subst hw
    simp [Level.smul]
  · simp [Level.smul, Function.update_of_ne hw]

/-- **The Hecke operators keep the forms** with coefficient lattices `H` closed under sums at lattice tuples and with
the edge integrality `p^{A_v}·H(L′) ⊆ H(L)`. At lattice tuples the value is a sum of elements of `H(L)`; off them every
term vanishes; and `γ_v` maps the edges below `L_v` bijectively onto those below `γ_v L_v`. -/
theorem hecke_mem_forms (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O) {lam0 : V → Fin n' → Fin k → ℤ}
    (r : ℕ) (v : V) {H : (V → Submodule W (Fin k → Qq)) → Set (Pol (V × Fin n') k Kf)}
    (hzero : ∀ L, (∀ w, (L w).IsLattice Qq) → (0 : Pol (V × Fin n') k Kf) ∈ H L)
    (hadd : ∀ L, (∀ w, (L w).IsLattice Qq) → ∀ F ∈ H L, ∀ G ∈ H L, F + G ∈ H L)
    (hint : ∀ L L' : V → Submodule W (Fin k → Qq), (∀ w, (L w).IsLattice Qq) → (∀ w, w ≠ v → L' w = L w) →
      IsEdge (n' := n') p r (L' v) (L v) → ∀ F ∈ H L', ((p : Kf) ^ topSum r lam0 v) • F ∈ H L)
    {F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf} (hF : F ∈ C.forms ι σ lam0 H) :
    hecke p r lam0 v F ∈ C.forms ι σ lam0 H := by
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun γ L => ?_⟩
  · rw [hecke_eq_sum hU, Finset.smul_sum]
    refine Finset.sum_induction _ (· ∈ H L) (fun a b ha hb => hadd L hL a ha b hb) (hzero L hL) fun L'' hL'' => ?_
    have he : IsEdge (n' := n') p r L'' (L v) := by
      rw [Set.Finite.mem_toFinset] at hL''
      exact hL''
    refine hint L _ hL (fun w hw => Function.update_of_ne hw _ _) (by rw [Function.update_self]; exact he) _
      (hF.1 _ fun w => ?_)
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact he.2.1
    · rw [Function.update_of_ne hw]
      exact hL w
  · rw [hecke_eq_sum hU, Finset.sum_eq_zero, smul_zero]
    intro L'' hL''
    have he : IsEdge (n' := n') p r L'' (L v) := by
      rw [Set.Finite.mem_toFinset] at hL''
      exact hL''
    refine hF.2.1 _ fun h => hL fun w => ?_
    by_cases hw : w = v
    · subst hw
      exact he.1
    · simpa [Function.update_of_ne hw] using h w
  · have hsum : ∑ L'' ∈ (finite_edges hU r (L v)).toFinset,
        algebraMap O Kf (C.χ γ : O) • C.actF ι σ lam0 γ (F (Function.update L v L'')) =
        ∑ L₁ ∈ (finite_edges hU r (C.smul γ L v)).toFinset, F (Function.update (C.smul γ L) v L₁) := by
      refine Finset.sum_nbij'
        (fun L'' => L''.map
          ((Matrix.mulVecLin ((C.act v γ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W))
        (fun L'' => L''.map
          ((Matrix.mulVecLin (((C.act v γ)⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W))
        (fun L'' hL'' => ?_) (fun L'' hL'' => ?_) (fun L'' _ => map_map_inv _ L'') (fun L'' _ => ?_)
        fun L'' _ => ?_
      · rw [Set.Finite.mem_toFinset] at hL'' ⊢
        exact isEdge_map _ hL''
      · rw [Set.Finite.mem_toFinset] at hL'' ⊢
        have := isEdge_map (C.act v γ)⁻¹ hL''
        rwa [show C.smul γ L v = (L v).map ((Matrix.mulVecLin ((C.act v γ : GL (Fin k) Qq) :
          Matrix (Fin k) (Fin k) Qq)).restrictScalars W) from rfl, map_map_inv] at this
      · simpa using map_map_inv (C.act v γ)⁻¹ L''
      · rw [update_smul, hF.2.2]
    rw [hecke_eq_sum hU, hecke_eq_sum hU, ← hsum, map_smul, map_sum]
    simp only [Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

/-- **`Δ_L` contains `0`** at lattice tuples. -/
theorem zero_mem_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) :
    (0 : Pol (V × Fin n') k Kf) ∈ DeltaT O ι σ lam0 L := by
  obtain ⟨C, hC⟩ := exists_basis_tuple (O := O) hU hL
  refine (mem_DeltaT_iff hC).2 ⟨zero_mem _, ?_⟩
  simp only [twist, map_zero, mul_zero]
  exact ⟨zero_mem _, fun rows => by simp [fockWith]⟩

/-- **`Δ_L` is closed under sums** at lattice tuples (test both in one basis, `mem_DeltaT_iff`). -/
theorem add_mem_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) {F G : Pol (V × Fin n') k Kf}
    (hF : F ∈ DeltaT O ι σ lam0 L) (hG : G ∈ DeltaT O ι σ lam0 L) : F + G ∈ DeltaT O ι σ lam0 L := by
  obtain ⟨C, hC⟩ := exists_basis_tuple (O := O) hU hL
  rw [mem_DeltaT_iff hC] at hF hG ⊢
  exact ⟨add_mem hF.1 hG.1, by rw [twist_add]; exact add_mem_Delta hF.2 hG.2⟩

/-- **`∇_L` contains `0`** at lattice tuples. -/
theorem zero_mem_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) :
    (0 : Pol (V × Fin n') k Kf) ∈ NablaT O ι σ lam0 L := by
  obtain ⟨C, hC⟩ := exists_basis_tuple (O := O) hU hL
  refine (mem_NablaT_iff hC).2 ⟨zero_mem _, ?_⟩
  simp only [twist, map_zero, mul_zero]
  exact zero_mem _

/-- **`∇_L` is closed under sums** at lattice tuples. -/
theorem add_mem_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) {F G : Pol (V × Fin n') k Kf}
    (hF : F ∈ NablaT O ι σ lam0 L) (hG : G ∈ NablaT O ι σ lam0 L) : F + G ∈ NablaT O ι σ lam0 L := by
  obtain ⟨C, hC⟩ := exists_basis_tuple (O := O) hU hL
  rw [mem_NablaT_iff hC] at hF hG ⊢
  exact ⟨add_mem hF.1 hG.1, by rw [twist_add]; exact add_mem hF.2 hG.2⟩

/-- **The Hecke operators keep `M`**, the forms with values in `Δ_L`, for dominant weights. -/
theorem hecke_mem_forms_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) (C : Level V k Qq O) (r : ℕ) (v : V)
    {F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf} (hF : F ∈ C.forms ι σ lam0 (DeltaT O ι σ lam0)) :
    hecke p r lam0 v F ∈ C.forms ι σ lam0 (DeltaT O ι σ lam0) :=
  hecke_mem_forms hU C r v (fun _ hL => zero_mem_DeltaT hU hL) (fun _ hL _ hF _ hG => add_mem_DeltaT hU hL hF hG)
    (fun _ _ hL hL' he _ hF => smul_mem_DeltaT_of_edge hU hlam hL hL' he hF) hF

/-- **The Hecke operators keep `M∇`**, the forms with values in `∇_L`, for dominant weights. -/
theorem hecke_mem_forms_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) (C : Level V k Qq O) (r : ℕ) (v : V)
    {F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf} (hF : F ∈ C.forms ι σ lam0 (NablaT O ι σ lam0)) :
    hecke p r lam0 v F ∈ C.forms ι σ lam0 (NablaT O ι σ lam0) :=
  hecke_mem_forms hU C r v (fun _ hL => zero_mem_NablaT hU hL) (fun _ hL _ hF _ hG => add_mem_NablaT hU hL hF hG)
    (fun _ _ hL hL' he _ hF => smul_mem_NablaT_of_edge hU hlam hL hL' he hF) hF

end Hecke

/-! ## The level action, and freeness of the integral forms -/

section Free

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [Fintype V]
  [DecidableEq V] in
/-- **The action on tuples**: `(γδ)·L = γ·(δ·L)`. -/
theorem Level.smul_mul (C : Level V k Qq O) (γ δ : C.Γ) (L : V → Submodule W (Fin k → Qq)) :
    C.smul (γ * δ) L = C.smul γ (C.smul δ L) := by
  funext v
  simp only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, LinearMap.restrictScalars_comp,
    Submodule.map_comp]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [Fintype V]
  [DecidableEq V] in
/-- **The action on tuples**: `1·L = L`. -/
theorem Level.smul_one (C : Level V k Qq O) (L : V → Submodule W (Fin k → Qq)) : C.smul 1 L = L := by
  funext v
  simp [Level.smul]

omit [IsDomain O] [IsDiscreteValuationRing O] [DecidableEq V] [Algebra O Kf] in
/-- **The action on coefficients**: `actF(γδ) = actF(γ) ∘ actF(δ)` (`twist_twist`). -/
theorem Level.actF_mul (C : Level V k Qq O) (lam0 : V → Fin n' → Fin k → ℤ) (γ δ : C.Γ)
    (P : Pol (V × Fin n') k Kf) : C.actF ι σ lam0 (γ * δ) P = C.actF ι σ lam0 γ (C.actF ι σ lam0 δ P) := by
  simp only [Level.actF, LinearMap.coe_mk, AddHom.coe_mk, twist_twist]
  congr 1
  funext b
  simp only [map_mul, mul_inv_rev, Units.val_mul]

omit [IsDomain O] [IsDiscreteValuationRing O] [DecidableEq V] [Algebra O Kf] in
/-- **The action on coefficients**: `actF(1) = id`. -/
theorem Level.actF_one (C : Level V k Qq O) (lam0 : V → Fin n' → Fin k → ℤ) (P : Pol (V × Fin n') k Kf) :
    C.actF ι σ lam0 1 P = P := by
  simp only [Level.actF, LinearMap.coe_mk, AddHom.coe_mk, map_one, inv_one, Units.val_one]
  exact twist_one _ _

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The columns of `g·B` span `g·L`** when those of `B` span `L`. -/
theorem map_span_cols (g : GL (Fin k) Qq) {N : Submodule W (Fin k → Qq)} {B : Matrix (Fin k) (Fin k) Qq}
    (hN : N = Submodule.span W (Set.range fun l i => B i l)) :
    N.map ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) =
      Submodule.span W (Set.range fun l i => ((g : Matrix (Fin k) (Fin k) Qq) * B) i l) := by
  rw [hN, Submodule.map_span, ← Set.range_comp]
  congr 2

omit [Fintype V] [DecidableEq V] in
/-- **Basis matrices moved by `γ`**: for basis matrices `C` of the blocks of `L`, the `ι σ^s(γ_v)·C` are basis
matrices of the blocks of `γ·L`. -/
theorem exists_basis_smul (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O) (γ : C.Γ)
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) :
    ∃ Cm : V × Fin n' → Matrix (Fin k) (Fin k) Kf, (∀ b, IsBasisOf (O := O) (blk ι σ b.2 (L b.1)) (Cm b)) ∧
      ∀ b, IsBasisOf (O := O) (blk ι σ b.2 (C.smul γ L b.1))
        ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix (C.act b.1 γ : Matrix (Fin k) (Fin k) Qq) * Cm b) := by
  choose B S _ hB hLB _ using fun w => exists_basis_edge hU (isEdge_refl (n' := n') (p := p) (hL w))
  refine ⟨fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix (B b.1),
    fun b => isBasisOf_blk hU _ (hB b.1) (hLB b.1), fun b => ?_⟩
  rw [← map_mul]
  exact isBasisOf_blk hU _ (by rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units _).mul (hB b.1))
    (map_span_cols _ (hLB b.1))

omit [IsDomain O] [IsDiscreteValuationRing O] [DecidableEq V] [Algebra O Kf] in
/-- **The twist by the moved basis matrices undoes the action**. -/
theorem twist_actF (C : Level V k Qq O) (lam0 : V → Fin n' → Fin k → ℤ) (γ : C.Γ)
    (Cm : V × Fin n' → Matrix (Fin k) (Fin k) Kf) (P : Pol (V × Fin n') k Kf) :
    twist (blockWt lam0) (fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix
      (C.act b.1 γ : Matrix (Fin k) (Fin k) Qq) * Cm b) (C.actF ι σ lam0 γ P) = twist (blockWt lam0) Cm P := by
  simp only [Level.actF, LinearMap.coe_mk, AddHom.coe_mk, twist_twist]
  congr 1
  funext b
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- **`γ` moves `Δ_L` to `Δ_{γL}`.** -/
theorem actF_mem_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O) (γ : C.Γ)
    {lam0 : V → Fin n' → Fin k → ℤ} {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq)
    {P : Pol (V × Fin n') k Kf} (hP : P ∈ DeltaT O ι σ lam0 L) :
    C.actF ι σ lam0 γ P ∈ DeltaT O ι σ lam0 (C.smul γ L) := by
  obtain ⟨Cm, hC, hC'⟩ := exists_basis_smul (O := O) hU C γ hL
  rw [mem_DeltaT_iff hC] at hP
  rw [mem_DeltaT_iff hC', twist_actF]
  exact ⟨twist_mem_nabla _ _ hP.1, hP.2⟩

/-- **`γ` moves `∇_L` to `∇_{γL}`.** -/
theorem actF_mem_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O) (γ : C.Γ)
    {lam0 : V → Fin n' → Fin k → ℤ} {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq)
    {P : Pol (V × Fin n') k Kf} (hP : P ∈ NablaT O ι σ lam0 L) :
    C.actF ι σ lam0 γ P ∈ NablaT O ι σ lam0 (C.smul γ L) := by
  obtain ⟨Cm, hC, hC'⟩ := exists_basis_smul (O := O) hU C γ hL
  rw [mem_NablaT_iff hC] at hP
  rw [mem_NablaT_iff hC', twist_actF]
  exact ⟨twist_mem_nabla _ _ hP.1, hP.2⟩

/-- **`Δ_L` is an `O`-module** at lattice tuples. -/
theorem smul_mem_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) {c : Kf} (hc : c ∈ Oint O Kf)
    {P : Pol (V × Fin n') k Kf} (hP : P ∈ DeltaT O ι σ lam0 L) : c • P ∈ DeltaT O ι σ lam0 L := by
  obtain ⟨Cm, hC⟩ := exists_basis_tuple (O := O) hU hL
  rw [mem_DeltaT_iff hC] at hP ⊢
  exact ⟨Submodule.smul_mem _ _ hP.1, by rw [twist_smul]; exact smul_mem_Delta hP.2 hc⟩

/-- **`∇_L` is an `O`-module** at lattice tuples. -/
theorem smul_mem_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    {L : V → Submodule W (Fin k → Qq)} (hL : ∀ w, (L w).IsLattice Qq) {c : Kf} (hc : c ∈ Oint O Kf)
    {P : Pol (V × Fin n') k Kf} (hP : P ∈ NablaT O ι σ lam0 L) : c • P ∈ NablaT O ι σ lam0 L := by
  obtain ⟨Cm, hC⟩ := exists_basis_tuple (O := O) hU hL
  rw [mem_NablaT_iff hC] at hP ⊢
  exact ⟨Submodule.smul_mem _ _ hP.1, by rw [twist_smul]; exact Submodule.smul_mem _ (⟨c, hc⟩ : Oint O Kf) hP.2⟩

open Classical in
/-- **The form extending `P` from a tuple `L₀`**: `χ(γ)·γ·P` at `γ·L₀`, and `0` off the orbit of `L₀`. -/
def Level.extend (C : Level V k Qq O) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lam0 : V → Fin n' → Fin k → ℤ)
    (L₀ : V → Submodule W (Fin k → Qq)) (P : Pol (V × Fin n') k Kf) :
    (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf := fun L =>
  if h : ∃ γ, C.smul γ L₀ = L then algebraMap O Kf (C.χ h.choose : O) • C.actF ι σ lam0 h.choose P else 0

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [DecidableEq V] in
/-- **The extension on the orbit**, when the stabiliser of `L₀` is trivial. -/
theorem Level.extend_eq (C : Level V k Qq O) {lam0 : V → Fin n' → Fin k → ℤ} {L₀ L : V → Submodule W (Fin k → Qq)}
    (huniq : ∀ γ γ' : C.Γ, C.smul γ L₀ = C.smul γ' L₀ → γ = γ') {γ : C.Γ} (h : C.smul γ L₀ = L)
    (P : Pol (V × Fin n') k Kf) :
    C.extend ι σ lam0 L₀ P L = algebraMap O Kf (C.χ γ : O) • C.actF ι σ lam0 γ P := by
  have hex : ∃ γ, C.smul γ L₀ = L := ⟨γ, h⟩
  rw [Level.extend, dite_eq_left hex, huniq _ _ (hex.choose_spec.trans h.symm)]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [DecidableEq V] in
/-- **The extension off the orbit** is `0`. -/
theorem Level.extend_eq_zero (C : Level V k Qq O) {lam0 : V → Fin n' → Fin k → ℤ}
    {L₀ L : V → Submodule W (Fin k → Qq)} (h : ¬ ∃ γ, C.smul γ L₀ = L) (P : Pol (V × Fin n') k Kf) :
    C.extend ι σ lam0 L₀ P L = 0 := by
  rw [Level.extend, dite_eq_right h]

omit [DecidableEq V] in
/-- **Freeness of the forms, abstractly**: for coefficient lattices `H` that are `O`-modules moved by the action,
free on `e(L₀)` at the representatives `L₀ ∈ R` of the finitely many orbits of lattice tuples, all with trivial
stabilisers, the forms are a free `O`-module with basis the extensions of the `e(L₀)_i` (`Level.extend`): a form is
determined by its values at the representatives. -/
theorem forms_free_of (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O) (lam0 : V → Fin n' → Fin k → ℤ)
    {H : (V → Submodule W (Fin k → Qq)) → Set (Pol (V × Fin n') k Kf)}
    (hzero : ∀ L, (∀ w, (L w).IsLattice Qq) → (0 : Pol (V × Fin n') k Kf) ∈ H L)
    (hadd : ∀ L, (∀ w, (L w).IsLattice Qq) → ∀ F ∈ H L, ∀ G ∈ H L, F + G ∈ H L)
    (hsmul : ∀ L, (∀ w, (L w).IsLattice Qq) → ∀ c ∈ Oint O Kf, ∀ F ∈ H L, c • F ∈ H L)
    (hact : ∀ γ L, (∀ w, (L w).IsLattice Qq) → ∀ F ∈ H L, C.actF ι σ lam0 γ F ∈ H (C.smul γ L))
    (R : Finset (V → Submodule W (Fin k → Qq))) (hR : ∀ L ∈ R, ∀ w, (L w).IsLattice Qq)
    (hcov : ∀ L, (∀ w, (L w).IsLattice Qq) → ∃ γ, ∃ L₀ ∈ R, C.smul γ L₀ = L)
    (hfree : ∀ γ, ∀ L₀ ∈ R, ∀ L₁ ∈ R, C.smul γ L₀ = L₁ → γ = 1 ∧ L₀ = L₁)
    {ι' : Type} [Fintype ι'] (e : R → ι' → Pol (V × Fin n') k Kf) (hmem : ∀ (L₀ : R) i, e L₀ i ∈ H L₀)
    (hspan : ∀ L₀ : R, ∀ F ∈ H L₀, ∃ c : ι' → O, F = ∑ i, algebraMap O Kf (c i) • e L₀ i)
    (hli : ∀ L₀, LinearIndependent Kf (e L₀)) :
    ∃ M : Submodule O ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf),
      (M : Set _) = C.forms ι σ lam0 H ∧ Module.Free O M ∧ Module.finrank O M = R.card * Fintype.card ι' := by
  classical
  have := hU.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hback : ∀ (γ δ : C.Γ) (L₀ L : V → Submodule W (Fin k → Qq)), C.smul δ L₀ = C.smul γ L →
      C.smul (γ⁻¹ * δ) L₀ = L := fun γ δ L₀ L h => by
    rw [Level.smul_mul, h, ← Level.smul_mul, inv_mul_cancel, Level.smul_one]
  have huniq : ∀ L₀ ∈ R, ∀ γ γ' : C.Γ, C.smul γ L₀ = C.smul γ' L₀ → γ = γ' := fun L₀ h₀ γ γ' h =>
    (inv_mul_eq_one.1 (hfree _ L₀ h₀ L₀ h₀ (hback γ' γ L₀ L₀ h)).1).symm
  have hlat : ∀ (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)), (∀ w, (L w).IsLattice Qq) →
      ∀ w, (C.smul γ L w).IsLattice Qq :=
    fun γ L hL w => isLattice_map _ (hL w)
  have hext : ∀ L₀ ∈ R, ∀ P ∈ H L₀, C.extend ι σ lam0 L₀ P ∈ C.forms ι σ lam0 H := by
    intro L₀ h₀ P hP
    refine ⟨fun L hL => ?_, fun L hL => ?_, fun δ L => ?_⟩
    · by_cases h : ∃ γ, C.smul γ L₀ = L
      · obtain ⟨γ, rfl⟩ := h
        rw [Level.extend_eq C (huniq L₀ h₀) rfl]
        exact hsmul _ hL _ ⟨_, rfl⟩ _ (hact γ L₀ (hR L₀ h₀) P hP)
      · rw [Level.extend_eq_zero C h]
        exact hzero L hL
    · exact Level.extend_eq_zero C (fun ⟨γ, hγ⟩ => hL (hγ ▸ hlat γ L₀ (hR L₀ h₀))) P
    · by_cases h : ∃ γ, C.smul γ L₀ = L
      · obtain ⟨γ, rfl⟩ := h
        rw [Level.extend_eq C (huniq L₀ h₀) rfl, ← Level.smul_mul, Level.extend_eq C (huniq L₀ h₀) rfl, map_smul,
          Level.actF_mul, map_mul, Units.val_mul, map_mul, mul_smul]
      · have h' : ¬ ∃ γ, C.smul γ L₀ = C.smul δ L := fun ⟨γ, hγ⟩ => h ⟨δ⁻¹ * γ, hback δ γ L₀ L hγ⟩
        rw [Level.extend_eq_zero C h, Level.extend_eq_zero C h', map_zero, smul_zero]
  have hrep : ∀ L₀ ∈ R, ∀ L₁ ∈ R, ∀ (γ : C.Γ) (P : Pol (V × Fin n') k Kf), C.extend ι σ lam0 L₀ P (C.smul γ L₁) =
      if L₀ = L₁ then algebraMap O Kf (C.χ γ : O) • C.actF ι σ lam0 γ P else 0 := by
    intro L₀ h₀ L₁ h₁ γ P
    split_ifs with h
    · subst h
      exact Level.extend_eq C (huniq L₀ h₀) rfl P
    · exact Level.extend_eq_zero C (fun ⟨δ, hδ⟩ => h (hfree _ L₀ h₀ L₁ h₁ (hback γ δ L₀ L₁ hδ)).2) P
  let M : Submodule O ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) :=
    { carrier := C.forms ι σ lam0 H
      zero_mem' := ⟨fun L hL => hzero L hL, fun _ _ => rfl, fun γ L => by simp⟩
      add_mem' := fun {F G} hF hG => ⟨fun L hL => hadd L hL _ (hF.1 L hL) _ (hG.1 L hL),
        fun L hL => by simp [hF.2.1 L hL, hG.2.1 L hL], fun γ L => by simp [hF.2.2, hG.2.2, smul_add]⟩
      smul_mem' := fun o F hF => ⟨fun L hL => by
          rw [Pi.smul_apply, ← algebraMap_smul Kf o]
          exact hsmul L hL _ ⟨o, rfl⟩ _ (hF.1 L hL),
        fun L hL => by simp [hF.2.1 L hL],
        fun γ L => by
          rw [Pi.smul_apply, Pi.smul_apply, hF.2.2, ← algebraMap_smul Kf o, ← algebraMap_smul Kf o (F L),
            map_smul, smul_comm]⟩ }
  let v : R × ι' → M := fun x => ⟨C.extend ι σ lam0 x.1 (e x.1 x.2), hext x.1 x.1.2 _ (hmem x.1 x.2)⟩
  have hv : ∀ (x : R × ι') (L₁ : R), (v x : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) L₁ =
      if x.1 = L₁ then e x.1 x.2 else 0 := fun x L₁ => by
    have := hrep x.1 x.1.2 L₁ L₁.2 1 (e x.1 x.2)
    rw [Level.smul_one, map_one, Units.val_one, map_one, one_smul, Level.actF_one] at this
    exact this.trans (if_congr Subtype.ext_iff.symm rfl rfl)
  have hvli : LinearIndependent O v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have h1 := congrFun (congrArg Subtype.val hg) x.1
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, hv,
      Submodule.coe_zero, Pi.zero_apply, smul_ite, smul_zero] at h1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1 (fun L₀ _ hne => Finset.sum_eq_zero fun i _ =>
      ite_eq_right hne) (by simp)] at h1
    simp only [ite_true, ← algebraMap_smul Kf (g _)] at h1
    exact hinj (by rw [Fintype.linearIndependent_iff.1 (hli x.1) _ h1 x.2, map_zero])
  have hvsp : ⊤ ≤ Submodule.span O (Set.range v) := by
    rintro F -
    choose c hc using fun L₀ : R => hspan L₀ (F.1 L₀) (F.2.1 L₀ (hR L₀ L₀.2))
    have hF : F = ∑ x : R × ι', c x.1 x.2 • v x := by
      apply Subtype.ext
      funext L
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
      by_cases hL : ∀ w, (L w).IsLattice Qq
      · obtain ⟨γ, L₁, h₁, rfl⟩ := hcov L hL
        have hv' : ∀ x : R × ι', (v x : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) (C.smul γ L₁) =
            if (x.1 : V → Submodule W (Fin k → Qq)) = L₁ then
              algebraMap O Kf (C.χ γ : O) • C.actF ι σ lam0 γ (e x.1 x.2) else 0 :=
          fun x => hrep x.1 x.1.2 L₁ h₁ γ _
        rw [F.2.2.2 γ L₁, hc ⟨L₁, h₁⟩, map_sum, Finset.smul_sum, Fintype.sum_prod_type,
          Finset.sum_eq_single ⟨L₁, h₁⟩ (fun L₀ _ hne => Finset.sum_eq_zero fun i _ => by
            rw [hv', ite_eq_right (fun h => hne (Subtype.ext h)), smul_zero]) (by simp)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hv', ite_eq_left rfl, map_smul, smul_comm, algebraMap_smul]
      · rw [F.2.2.1 L hL]
        refine (Finset.sum_eq_zero fun x _ => ?_).symm
        rw [show (v x : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf) L = 0 from
          Level.extend_eq_zero C (fun ⟨γ, hγ⟩ => hL (hγ ▸ hlat γ _ (hR _ x.1.2))) _, smul_zero]
    rw [hF]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  let bas := Module.Basis.mk hvli hvsp
  refine ⟨M, rfl, Module.Free.of_basis bas, ?_⟩
  rw [Module.finrank_eq_card_basis bas, Fintype.card_prod, Fintype.card_coe]

end Free

/-! ## Freeness of `M` and `M∇` -/

section Coord

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {k : ℕ} {Kf : Type} [Field Kf] {lam : Φ → Fin k → ℤ}

omit [DecidableEq Φ] in
/-- **A twist kills `0`.** -/
theorem twist_zero (lam : Φ → Fin k → ℤ) (g : Φ → Matrix (Fin k) (Fin k) Kf) : twist lam g 0 = 0 := by
  simp [twist]

omit [DecidableEq Φ] in
/-- **A twist is additive** over finite sums. -/
theorem twist_sum (lam : Φ → Fin k → ℤ) (g : Φ → Matrix (Fin k) (Fin k) Kf) {ι' : Type} (s : Finset ι')
    (f : ι' → Pol Φ k Kf) : twist lam g (∑ i ∈ s, f i) = ∑ i ∈ s, twist lam g (f i) := by
  simp only [twist, map_sum, Finset.mul_sum]

omit [DecidableEq Φ] in
/-- **The twist by `C⁻¹` undoes the twist by `C`.** -/
theorem twist_inv_twist (lam : Φ → Fin k → ℤ) {Cm : Φ → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsUnit (Cm b).det)
    (P : Pol Φ k Kf) : twist lam (fun b => (Cm b)⁻¹) (twist lam Cm P) = P := by
  rw [twist_twist, show (fun b => Cm b * (Cm b)⁻¹) = fun _ => 1 from
    funext fun b => Matrix.mul_nonsing_inv _ (hC b), twist_one]

omit [DecidableEq Φ] in
/-- **The twist by `C` undoes the twist by `C⁻¹`.** -/
theorem twist_twist_inv (lam : Φ → Fin k → ℤ) {Cm : Φ → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsUnit (Cm b).det)
    (P : Pol Φ k Kf) : twist lam Cm (twist lam (fun b => (Cm b)⁻¹) P) = P := by
  rw [twist_twist, show (fun b => (Cm b)⁻¹ * Cm b) = fun _ => 1 from
    funext fun b => Matrix.nonsing_inv_mul _ (hC b), twist_one]

omit [DecidableEq Φ] in
/-- **Twisting keeps linear independence.** -/
theorem linearIndependent_twist (lam : Φ → Fin k → ℤ) {Cm : Φ → Matrix (Fin k) (Fin k) Kf}
    (hC : ∀ b, IsUnit (Cm b).det) {ι' : Type} [Fintype ι'] {f : ι' → Pol Φ k Kf} (hf : LinearIndependent Kf f) :
    LinearIndependent Kf fun i => twist lam (fun b => (Cm b)⁻¹) (f i) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro a ha
  apply hf a
  have := congrArg (twist lam Cm) ha
  simpa only [twist_sum, twist_smul, twist_twist_inv lam hC, twist_zero] using this

variable [CharZero Kf]

/-- **A vector of `∇` is the combination of the dual basis with its coordinates.** -/
theorem eq_sum_dc (hlam : ∀ b, Antitone (lam b)) {G : Pol Φ k Kf} (hG : G ∈ nabla Kf fun b => natW (lam b)) :
    G = ∑ l, dc Kf lam l G • zdualK Kf lam l := by
  have h1 : G = ∑ l, dcoord Kf hlam ⟨G, hG⟩ l • zdualK Kf lam l := by
    rw [← dcoord_symm_apply Kf hlam, LinearEquiv.symm_apply_apply]
  have h2 : ∀ l, dc Kf lam l G = dcoord Kf hlam ⟨G, hG⟩ l := fun l => by
    conv_lhs => rw [h1]
    exact dc_sum lam _ l
  exact h1.trans (Finset.sum_congr rfl fun l _ => by rw [h2])

/-- **The dual basis lies in `Δ_A`**: its coordinates are `0` and `1`. -/
theorem zdualK_mem_Delta (hlam : ∀ b, Antitone (lam b)) (A : Subring Kf) (i : ZIdx lam) :
    zdualK Kf lam i ∈ Delta A fun b => natW (lam b) := by
  refine (mem_Delta_iff Kf lam A _).2 ⟨zdualK_mem hlam i, fun l => ?_⟩
  have e : zdualK Kf lam i = ∑ m, (Pi.single i 1 : ZIdx lam → Kf) m • zdualK Kf lam m := by
    simp [Pi.single_apply]
  rw [e, dc_sum]
  by_cases h : l = i
  · subst h
    simp [A.one_mem]
  · simp [h, A.zero_mem]

/-- **The basis `zb` lies in `∇_A`**: it is an integer combination of bideterminants. -/
theorem zbK_mem_nablaInt (A : Subring Kf) (i : ZIdx lam) :
    zbK Kf lam i ∈ (nablaInt A fun b => natW (lam b) : Set (Pol Φ k Kf)) := by
  obtain ⟨z, hz⟩ := exists_zbK_eq Kf lam i
  rw [hz, SetLike.mem_coe]
  exact Submodule.sum_mem _ fun rows _ => zsmul_mem (show bidet Kf (fun b => natW (lam b)) rows ∈
    nablaInt A (fun b => natW (lam b)) from Submodule.subset_span ⟨rows, rfl⟩) _

/-- **`∇_A` is spanned by `zb`**: a bideterminant is an integer combination of the `zb`. -/
theorem exists_eq_sum_zbK {A : Subring Kf} {G : Pol Φ k Kf}
    (hG : G ∈ (nablaInt A fun b => natW (lam b) : Set (Pol Φ k Kf))) :
    ∃ c : ZIdx lam → A, G = ∑ l, (c l : Kf) • zbK Kf lam l := by
  have hle : nablaInt A (fun b => natW (lam b)) ≤ Submodule.span A (Set.range (zbK Kf lam)) := by
    rw [nablaInt, Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    obtain ⟨y, hy⟩ := exists_bidet_eq Kf lam rows
    rw [SetLike.mem_coe, hy]
    exact Submodule.sum_mem _ fun l _ => zsmul_mem (show zbK Kf lam l ∈ Submodule.span A (Set.range (zbK Kf lam))
      from Submodule.subset_span ⟨l, rfl⟩) _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (hle hG)
  exact ⟨c, hc.symm⟩

end Coord

section FreeT

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **`M` is free of rank `d = |R|·dim ∇`** when the lattice tuples fall into the finitely many orbits of the
representatives `R`, with trivial stabilisers: at each representative `Δ_{L₀}` is free on the twisted dual basis
`twist_{C⁻¹} zdual` (`mem_Delta_iff`), and `forms_free_of` applies. -/
theorem forms_free_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) (C : Level V k Qq O) (R : Finset (V → Submodule W (Fin k → Qq)))
    (hR : ∀ L ∈ R, ∀ w, (L w).IsLattice Qq)
    (hcov : ∀ L, (∀ w, (L w).IsLattice Qq) → ∃ γ, ∃ L₀ ∈ R, C.smul γ L₀ = L)
    (hfree : ∀ γ, ∀ L₀ ∈ R, ∀ L₁ ∈ R, C.smul γ L₀ = L₁ → γ = 1 ∧ L₀ = L₁) :
    ∃ M : Submodule O ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf),
      (M : Set ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf)) = C.forms ι σ lam0 (DeltaT O ι σ lam0) ∧
        Module.Free O M ∧
          Module.finrank O M = R.card * Module.finrank Kf (nabla Kf fun b => natW (blockWt lam0 b)) := by
  have hlam' := antitone_blockWt hlam
  choose Cm hCm using fun L₀ : R => exists_basis_tuple (O := O) hU (hR L₀ L₀.2)
  rw [Module.finrank_eq_card_basis (zdualBasis Kf hlam')]
  refine forms_free_of hU C lam0 (fun L hL => zero_mem_DeltaT hU hL)
    (fun L hL F hF G hG => add_mem_DeltaT hU hL hF hG) (fun L hL c hc F hF => smul_mem_DeltaT hU hL hc hF)
    (fun γ L hL F hF => actF_mem_DeltaT hU C γ hL hF) R hR hcov hfree
    (fun L₀ i => twist (blockWt lam0) (fun b => (Cm L₀ b)⁻¹) (zdualK Kf (blockWt lam0) i)) (fun L₀ i => ?_)
    (fun L₀ F hF => ?_) fun L₀ => linearIndependent_twist _ (fun b => (hCm L₀ b).1) (linearIndependent_zdualK Kf _)
  · rw [mem_DeltaT_iff (hCm L₀), twist_twist_inv _ fun b => (hCm L₀ b).1]
    exact ⟨twist_mem_nabla _ _ (zdualK_mem hlam' i), zdualK_mem_Delta hlam' _ i⟩
  · rw [mem_DeltaT_iff (hCm L₀)] at hF
    obtain ⟨hn, hd⟩ := (mem_Delta_iff Kf (blockWt lam0) (Oint O Kf) _).1 hF.2
    choose c hc using fun l => RingHom.mem_range.1 (hd l)
    refine ⟨c, ?_⟩
    rw [← twist_inv_twist (blockWt lam0) (fun b => (hCm L₀ b).1) F, eq_sum_dc hlam' hn, twist_sum]
    simp only [twist_smul, hc]

/-- **`M∇` is free of rank `d = |R|·dim ∇`** under the same hypotheses: at each representative `∇_{L₀}` is free on
the twisted basis `twist_{C⁻¹} zb` (`exists_eq_sum_zbK`). -/
theorem forms_free_NablaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) (C : Level V k Qq O) (R : Finset (V → Submodule W (Fin k → Qq)))
    (hR : ∀ L ∈ R, ∀ w, (L w).IsLattice Qq)
    (hcov : ∀ L, (∀ w, (L w).IsLattice Qq) → ∃ γ, ∃ L₀ ∈ R, C.smul γ L₀ = L)
    (hfree : ∀ γ, ∀ L₀ ∈ R, ∀ L₁ ∈ R, C.smul γ L₀ = L₁ → γ = 1 ∧ L₀ = L₁) :
    ∃ M : Submodule O ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf),
      (M : Set ((V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf)) = C.forms ι σ lam0 (NablaT O ι σ lam0) ∧
        Module.Free O M ∧
          Module.finrank O M = R.card * Module.finrank Kf (nabla Kf fun b => natW (blockWt lam0 b)) := by
  have hlam' := antitone_blockWt hlam
  choose Cm hCm using fun L₀ : R => exists_basis_tuple (O := O) hU (hR L₀ L₀.2)
  rw [Module.finrank_eq_card_basis (zdualBasis Kf hlam')]
  refine forms_free_of hU C lam0 (fun L hL => zero_mem_NablaT hU hL)
    (fun L hL F hF G hG => add_mem_NablaT hU hL hF hG) (fun L hL c hc F hF => smul_mem_NablaT hU hL hc hF)
    (fun γ L hL F hF => actF_mem_NablaT hU C γ hL hF) R hR hcov hfree
    (fun L₀ i => twist (blockWt lam0) (fun b => (Cm L₀ b)⁻¹) (zbK Kf (blockWt lam0) i)) (fun L₀ i => ?_)
    (fun L₀ F hF => ?_) fun L₀ => linearIndependent_twist _ (fun b => (hCm L₀ b).1) (linearIndependent_zbK Kf _)
  · rw [mem_NablaT_iff (hCm L₀), twist_twist_inv _ fun b => (hCm L₀ b).1]
    exact ⟨twist_mem_nabla _ _ (zbK_mem Kf hlam' i), zbK_mem_nablaInt _ i⟩
  · rw [mem_NablaT_iff (hCm L₀)] at hF
    obtain ⟨c, hc⟩ := exists_eq_sum_zbK hF.2
    choose o ho using fun l => RingHom.mem_range.1 (c l).2
    refine ⟨o, ?_⟩
    rw [← twist_inv_twist (blockWt lam0) (fun b => (hCm L₀ b).1) F, hc, twist_sum]
    simp only [twist_smul, ho]

end FreeT

end

end InertModel
