import Mathlib
import EuclidLattice

/-!
# Lattices with places, and heights averaged over them

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4): lattices with several
archimedean places, as hermitian lattices over a number field `K` have, and maps whose heights are averaged over the
places. These are the frames of Alpöge's argument.

**The setting** (`PlaceLattice`). A discrete subgroup `Λ` of a Euclidean space `E`, pairwise orthogonal subspaces `V v`
at its places `v ∈ P`, and a class `S` of saturated sublattices: a sublattice of `Sat Λ` with `0` and `Λ`, whose members
have balanced spans. A subspace `U` is balanced (`Balanced`) when `|P|·dim (U ∩ V v) = dim U` at every place. It is
then the orthogonal sum of its parts `U ∩ V v` (`Balanced.iSup_inf_eq`). For a hermitian lattice over a totally complex
`K`, the `V v` are the summands of `E = ⊕_v E_v` at the complex places, and `S` is the set of `O_K`-stable saturated
sublattices.

**Slopes.** The class `S`, with the rank and degree of `EuclidLattice.slopeLattice`, is a slope lattice
(`slopeLattice`). Sums of members keep their minimal slope (`supClosed`), since rank is modular and degree supermodular
on all of `Sat Λ`.

**Bost's inequality with averaged heights** (`bost`). Let `φ : E → F` send `Λ` into `Λ'`, with `‖φ x‖ ≤ e^{h v}‖x‖` on
each `V v`. Suppose images of members of `S` lie in the target's class, and preimages of members of the target's class
lie in `S`. Then `μ_min(img φ a) ≥ μ_min(a) − h̄`, with `h̄ = |P|⁻¹ Σ_v h v` the averaged height. At `b ≤ img φ a`,
`EuclidLattice.bost_le` asks that `φ` multiply volumes in `W = span a ⊖ span K` by at most `e^{h̄·dim W}`, where
`K = a ⊓ preimg φ b` is in `S`:
* `W` is balanced, as `span a` and `span K` are (`Balanced.orthogonal_inf`). At each place, `W ∩ V v` contains the
  complement of `span K ∩ V v` in `span a ∩ V v`, of dimension `dim W/|P|`, and the parts of `W` have total dimension at
  most `dim W`;
* Hadamard place by place (`GramVolume.volLe_iSup`) bounds the factor by `∏_v e^{h v·dim W/|P|} = e^{h̄·dim W}`
  (`Balanced.volLe`).

Only the norm of `φ` on each `V v` enters. The map need not respect any decomposition of the target, whose places go
unused.

**Frames** (`frame`). Sources with places, mapped into one target, form a `SlopeFrame.Frame` with the averaged heights.
The archive normalises `μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]` and `h(φ) = n_∞⁻¹ Σ_v log‖φ_v‖²`: twice the slopes
and heights here, with the slopes shifted by a constant. Its frame inequality is this one, in those units.
-/

namespace PlaceLattice

open Module Submodule GramVolume EuclidLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-! ### Balanced subspaces -/

section Balanced

variable {P : Type*} [Fintype P]

/-- A subspace `U` is **balanced** across subspaces `V v`, `v ∈ P`, if it meets each in dimension `dim U/|P|`. -/
def Balanced (V : P → Submodule ℝ E) (U : Submodule ℝ E) : Prop :=
  ∀ v, Fintype.card P * finrank ℝ ↥(U ⊓ V v) = finrank ℝ U

variable [FiniteDimensional ℝ E] [Nonempty P] {V : P → Submodule ℝ E} (hV : Pairwise fun v w => V v ⟂ V w)
include hV

/-- A balanced subspace is the sum of its parts at the places: these are orthogonal, of total dimension `dim U`. -/
theorem Balanced.iSup_inf_eq {U : Submodule ℝ E} (hU : Balanced V U) : ⨆ v, U ⊓ V v = U := by
  refine eq_of_le_of_finrank_eq (iSup_le fun v => inf_le_left) ?_
  rw [finrank_iSup_of_isOrtho (hV.mono fun v w h => h.mono inf_le_right inf_le_right)]
  refine Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := P)) ?_
  simp [Finset.mul_sum, hU _]

/-- **Complements of balanced subspaces are balanced**: if `B ≤ A` are balanced, so is `Bᗮ ⊓ A`. At each place it
contains the complement of `B ⊓ V v` in `A ⊓ V v`, as `B` is the sum of its parts. That complement has dimension
`dim (Bᗮ ⊓ A)/|P|`, and the parts of `Bᗮ ⊓ A` have total dimension at most `dim (Bᗮ ⊓ A)`. -/
theorem Balanced.orthogonal_inf {A B : Submodule ℝ E} (hA : Balanced V A) (hB : Balanced V B) (hBA : B ≤ A) :
    Balanced V (Bᗮ ⊓ A) := by
  have hW := finrank_add_inf_finrank_orthogonal hBA
  have hge v : finrank ℝ ↥(Bᗮ ⊓ A) ≤ Fintype.card P * finrank ℝ ↥(Bᗮ ⊓ A ⊓ V v) := by
    have h1 := finrank_add_inf_finrank_orthogonal (inf_le_inf_right (V v) hBA)
    have h2 : (B ⊓ V v)ᗮ ⊓ (A ⊓ V v) ≤ Bᗮ ⊓ A ⊓ V v := by
      refine le_inf (le_inf ?_ (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)
      have h4 : (B ⊓ V v)ᗮ ⊓ (A ⊓ V v) ⟂ ⨆ w, B ⊓ V w := isOrtho_iSup_right.2 fun w => by
        obtain rfl | hvw := eq_or_ne v w
        · exact isOrtho_iff_le.2 inf_le_left
        · exact (hV hvw).mono (inf_le_right.trans inf_le_right) inf_le_right
      rw [hB.iSup_inf_eq hV] at h4
      exact h4
    have h3 := Nat.mul_le_mul_left (Fintype.card P) ((Nat.le_of_eq h1.symm).trans
      (Nat.add_le_add_left (Submodule.finrank_mono h2) _))
    rw [mul_add, hA v, hB v] at h3
    omega
  have hle : ∑ v, finrank ℝ ↥(Bᗮ ⊓ A ⊓ V v) ≤ finrank ℝ ↥(Bᗮ ⊓ A) := by
    rw [← finrank_iSup_of_isOrtho (hV.mono fun v w h => h.mono inf_le_right inf_le_right)]
    exact Submodule.finrank_mono (iSup_le fun v => inf_le_left)
  have hsum : ∑ v, Fintype.card P * finrank ℝ ↥(Bᗮ ⊓ A ⊓ V v) ≤ ∑ v : P, finrank ℝ ↥(Bᗮ ⊓ A) := by
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_le_mul_left _ hle
  intro v
  exact ((Finset.sum_eq_sum_iff_of_le fun w _ => hge w).1
    (le_antisymm (Finset.sum_le_sum fun w _ => hge w) hsum) v (Finset.mem_univ v)).symm

/-- **Hadamard with averaged heights**: if `‖φ x‖ ≤ e^{h v}‖x‖` on each `V v`, then `φ` multiplies volumes in a balanced
subspace `U` by at most `e^{h̄·dim U}`, with `h̄ = |P|⁻¹ Σ_v h v` the averaged height. -/
theorem Balanced.volLe [FiniteDimensional ℝ F] {U : Submodule ℝ E} (hU : Balanced V U) {φ : E →L[ℝ] F}
    {h : P → ℝ} (hφ : ∀ v, ∀ x ∈ V v, ‖φ x‖ ≤ Real.exp (h v) * ‖x‖) :
    VolLe φ U (Real.exp (finrank ℝ U * ((Fintype.card P : ℝ)⁻¹ * ∑ v, h v))) := by
  have h1 := volLe_iSup (W := fun v => U ⊓ V v) (hV.mono fun v w h => h.mono inf_le_right inf_le_right)
    (fun v => (Real.exp_pos (h v)).le) fun v x hx => hφ v x hx.2
  rw [hU.iSup_inf_eq hV] at h1
  convert h1 using 1
  simp_rw [← Real.exp_nat_mul, ← Real.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← hU v]
  push_cast
  field_simp

end Balanced

end PlaceLattice

open Submodule in
/-- **A lattice with places**: a discrete subgroup `Λ` of `E`, pairwise orthogonal subspaces `V v` at its places
`v ∈ P`, and a class `S` of saturated sublattices: a sublattice of `Sat Λ` with `0` and `Λ`, whose members have
balanced spans. For a hermitian lattice over a totally complex number field, the `V v` are the summands at the complex
places and `S` is the set of `O_K`-stable saturated sublattices. -/
structure PlaceLattice (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The places. -/
  P : Type
  [fintype : Fintype P]
  [nonempty : Nonempty P]
  /-- The subspace at each place. -/
  V : P → Submodule ℝ E
  /-- The subspaces at the places are pairwise orthogonal. -/
  orth : Pairwise fun v w => V v ⟂ V w
  /-- The lattice. -/
  Λ : Submodule ℤ E
  [discrete : DiscreteTopology Λ]
  /-- The class of saturated sublattices. -/
  S : Sublattice (EuclidLattice.Sat Λ)
  /-- `0` is in the class. -/
  bot_mem : ⊥ ∈ S
  /-- `Λ` is in the class. -/
  top_mem : ⊤ ∈ S
  /-- The members of the class have balanced spans. -/
  balanced : ∀ a ∈ S, PlaceLattice.Balanced V (span ℝ (a.1 : Set E))

namespace PlaceLattice

open Module Submodule GramVolume EuclidLattice

attribute [instance] fintype nonempty discrete

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- `⊥ = 0` and `⊤ = Λ`. -/
instance (X : PlaceLattice E) : BoundedOrder X.S :=
  Subtype.boundedOrder X.bot_mem X.top_mem

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The slope lattice of `X`: its class `S`, with the rank and degree of `EuclidLattice.slopeLattice`. -/
noncomputable def slopeLattice (X : PlaceLattice E) : SlopeFrame.SlopeLattice X.S where
  rk a := (EuclidLattice.slopeLattice X.Λ).rk a.1
  deg a := (EuclidLattice.slopeLattice X.Λ).deg a.1
  rk_bot := (EuclidLattice.slopeLattice X.Λ).rk_bot
  deg_bot := (EuclidLattice.slopeLattice X.Λ).deg_bot
  rk_strictMono _ _ h := (EuclidLattice.slopeLattice X.Λ).rk_strictMono h

/-- Sums of members of `S` of minimal slope at least `θ` have minimal slope at least `θ`: rank is modular and degree
supermodular on `S`, as on all saturated sublattices. -/
theorem supClosed (X : PlaceLattice E) : X.slopeLattice.SupClosed :=
  SlopeFrame.SlopeLattice.supClosed_of_modular (fun a b => rk_sup_add_rk_inf a.1 b.1)
    fun a b => deg_add_deg_le a.1 b.1

/-- **Bost's inequality with averaged heights**: if `φ` sends `Λ` into `Λ'`, with `‖φ x‖ ≤ e^{h v}‖x‖` on each `V v`,
and images and preimages keep to the classes, then `μ_min(img φ a) ≥ μ_min(a) − h̄`, with `h̄ = |P|⁻¹ Σ_v h v`. -/
theorem bost {X : PlaceLattice E} {Y : PlaceLattice F} (φ : E →L[ℝ] F) (hφΛ : ∀ x ∈ X.Λ, φ x ∈ Y.Λ)
    {h : X.P → ℝ} (hφ : ∀ v, ∀ x ∈ X.V v, ‖φ x‖ ≤ Real.exp (h v) * ‖x‖)
    (himg : ∀ a ∈ X.S, img φ a ∈ Y.S) (hpre : ∀ b ∈ Y.S, preimg φ b ∈ X.S) {a : X.S} {θ : ℝ}
    (ha : X.slopeLattice.SlopeGe a θ) :
    Y.slopeLattice.SlopeGe ⟨img φ a.1, himg a.1 a.2⟩ (θ - (Fintype.card X.P : ℝ)⁻¹ * ∑ v, h v) := by
  intro b hb
  have hK := X.S.inf_mem a.2 (hpre b.1 b.2)
  have hab : a.1 ⊓ preimg φ b.1 ≤ a.1 := inf_le_left
  have hBA : span ℝ ((a.1 ⊓ preimg φ b.1).1 : Set E) ≤ span ℝ (a.1.1 : Set E) :=
    span_mono (show ((a.1 ⊓ preimg φ b.1).1 : Set E) ⊆ a.1.1 from hab)
  have hvol := (Balanced.orthogonal_inf X.orth (X.balanced a a.2) (X.balanced _ hK) hBA).volLe X.orth hφ
  exact bost_le φ hφΛ (show b.1 ≤ img φ a.1 from hb) hvol (ha ⟨_, hK⟩ hab)

end PlaceLattice

namespace PlaceLattice

open Module Submodule

/-- **Frames with averaged heights**: lattices with places `X ω`, mapped into one lattice with places `Y` by maps `φ ω`
that carry `Λ ω` into `Λ'`, with `‖φ ω x‖ ≤ e^{h ω v}‖x‖` on each `V v`, and with images and preimages keeping to the
classes, form a frame (`SlopeFrame.Frame`) with heights `h̄ ω = |P ω|⁻¹ Σ_v h ω v`. -/
noncomputable def frame {ι : Type} [Fintype ι] {E : ι → Type} [∀ ω, NormedAddCommGroup (E ω)]
    [∀ ω, InnerProductSpace ℝ (E ω)] [∀ ω, FiniteDimensional ℝ (E ω)] (X : ∀ ω, PlaceLattice (E ω)) {F : Type}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (Y : PlaceLattice F)
    (φ : ∀ ω, E ω →L[ℝ] F) (hφΛ : ∀ ω, ∀ x ∈ (X ω).Λ, φ ω x ∈ Y.Λ) (h : ∀ ω, (X ω).P → ℝ)
    (hφ : ∀ ω v, ∀ x ∈ (X ω).V v, ‖φ ω x‖ ≤ Real.exp (h ω v) * ‖x‖)
    (himg : ∀ ω, ∀ a ∈ (X ω).S, EuclidLattice.img (φ ω) a ∈ Y.S)
    (hpre : ∀ ω, ∀ b ∈ Y.S, EuclidLattice.preimg (φ ω) b ∈ (X ω).S)
    (hrk : 0 < finrank ℝ (span ℝ (Y.Λ : Set F))) : SlopeFrame.Frame where
  ι := ι
  L ω := (X ω).S
  N ω := (X ω).slopeLattice
  M := Y.S
  C := Y.slopeLattice
  img ω a := ⟨EuclidLattice.img (φ ω) a.1, himg ω a.1 a.2⟩
  h ω := (Fintype.card (X ω).P : ℝ)⁻¹ * ∑ v, h ω v
  bost ω _ _ ha := PlaceLattice.bost (φ ω) (hφΛ ω) (hφ ω) (himg ω) (hpre ω) ha
  supClosed := Y.supClosed
  rk_pos := hrk

end PlaceLattice

#print axioms PlaceLattice.bost
#print axioms PlaceLattice.supClosed
#print axioms PlaceLattice.frame
