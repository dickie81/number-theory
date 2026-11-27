import KernelCount
import JetMinor
import CMFormalInert

/-!
# The local chain at a served prime and the D1 → D2 contract

D2-0 of the served valuation of the theta chain (layer 3, definitions only).

**The Gaussian frame form** (the interface of D1b-8). On variables `P × Fin b × Fin a` (position, target index,
source index) with a successor `succ` on the positions, the twisted series
`tw(x) = Σ_l (−1)^l Z_{succ^{−2l}s,β,α}^{ℓ^{2l}}` (`twSer`), the position form `Σ_x u_{x.1}·tw(x)^ℓ·tw(succ x)`
(`posForm`) and its Gaussian `exp(−(ϖ^{ℓ+1}/ℓ)·posForm)` (`posGauss`, `ϖ^{ℓ²−1} = ℓ`). A series in the variables of
the orbits `V × ZMod n′` is **mixed-integral** (`IsMixInt`) when it is integral in `Z` and, orbit by orbit,
`κ!`-integral in `z = ϖZ`.

**The local chain** (`LocalChain`, D1c's output shape): levels `j ≤ m` with ranks `N j`, weights, levels with class
representatives (`KernelCount.ClassReps`), coefficient lattices `Λ j L` (D1's normalisation) and steps `K j` on the
local functions (`LFn`, functions on lattice tuples `Tup`). Derived: the integral forms `Int j`, the valuation
predicate `vGe` (`F ∈ ϖ^{⌈2g⌉}·Int j`), the composite `chain`, and the served Hecke-product lattice `Iprod`.

**The contract** (`LocalKernels`), over `ℂ_[p]` through an embedding `emb` with `‖emb x‖ ≤ 1 ↔ x ∈ O`: kernel series
`ser j L L′` in each pair's frame, kernel operators and scalars with (K1) the expansion of the step over the class
representatives, (K2) the Gaussian frame form `ser = posGauss(γ)·R` with `R` integral and mixed-integral, (K5) level
equivariance, and stabiliser losses `dG`. Two further contract clauses are `Prop`s on top: (K3) the bridge from
frame jets to lattice valuations (`Bridge`, with the combinations `InLatC`), and (K4) the normalisation law
(`NormLaw`).
-/

open Finset CMFormalInert JetMinor KernelCount

noncomputable section

namespace LocalContract

/-! ## The Gaussian frame form -/

section PosForm

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ}

/-- **The total degree** of an exponent. -/
def deg {σ : Type} (n : σ →₀ ℕ) : ℕ := n.sum fun _ e => e

/-- **The twisted series** at `x = (s, β, α)`: `Σ_l (−1)^l Z_{succ^{−2l}s, β, α}^{ℓ^{2l}}`. -/
def twSer (succ : Equiv.Perm P) (x : P × Fin b × Fin a) : MvPowerSeries (P × Fin b × Fin a) ℂ_[ℓ] :=
  fun n => ∑ l ∈ range (deg n + 1),
    if n = Finsupp.single (((succ ^ (2 * l)).symm x.1), x.2) (ℓ ^ (2 * l)) then (-1 : ℂ_[ℓ]) ^ l else 0

/-- **The position form** `Σ_x u_{x.1}·tw(x)^ℓ·tw(succ x)` (`u ≡ γ` constant for the chain). -/
def posForm (succ : Equiv.Perm P) (u : P → ℂ_[ℓ]) : MvPowerSeries (P × Fin b × Fin a) ℂ_[ℓ] :=
  ∑ x : P × Fin b × Fin a, MvPowerSeries.C (u x.1) * twSer (ℓ := ℓ) succ x ^ ℓ *
    twSer (ℓ := ℓ) succ (succ x.1, x.2)

/-- **The Gaussian of the position form** `exp(−(ϖ^{ℓ+1}/ℓ)·posForm)` (`ϖ^{ℓ²−1} = ℓ`). -/
def posGauss (ϖ : ℂ_[ℓ]) (succ : Equiv.Perm P) (u : P → ℂ_[ℓ]) : MvPowerSeries (P × Fin b × Fin a) ℂ_[ℓ] :=
  expMv (-(MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ) * posForm (a := a) (b := b) succ u))

end PosForm

section MixInt

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n' a b : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **Mixed integrality** of a series in the variables of the orbits `V × ZMod n'`: integral in `Z` and, orbit by
orbit, `κ!`-integral in `z = ϖZ`: `‖R_κ‖ ≤ ∏_v min(1, ‖ϖ‖^{|κ_v|}/‖κ_v!‖)`. -/
def IsMixInt (ϖ : ℂ_[ℓ]) (R : MvPowerSeries ((V × ZMod n') × Fin b × Fin a) ℂ_[ℓ]) : Prop :=
  ∀ κ, ‖MvPowerSeries.coeff κ R‖ ≤ ∏ v : V, min 1 (‖ϖ‖ ^ deg (κ.filter fun x => x.1.1 = v) /
    ‖((mfact (κ.filter fun x => x.1.1 = v) : ℕ) : ℂ_[ℓ])‖)

end MixInt

/-! ## The local chain -/

section Chain

open InertModel WeylFock

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {n' : ℕ}
  {V : Type} [Fintype V] [DecidableEq V]

/-- **Tuples of rank `N`.** -/
abbrev Tup (W Qq V : Type) [CommRing W] [Field Qq] [Algebra W Qq] (N : ℕ) := V → Submodule W (Fin N → Qq)

/-- **Local functions at rank `N`** (the local forms live here). -/
abbrev LFn (W Qq Kf V : Type) [CommRing W] [Field Qq] [Algebra W Qq] [Field Kf] (n' N : ℕ) :=
  Tup W Qq V N → Pol (V × Fin n') N Kf

/-- **The local chain at a served prime** (D1c's output shape): levels `j ≤ m`, ranks `N j`, weights, levels with
class representatives, the integral coefficient lattices `Λ j L` (D1's normalisation: the `Δ`-lattices scaled by the
forced/error exponents), and the steps `K j`. -/
structure LocalChain (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jW : W →+* O) (ϖ : O) where
  /-- The unramified setting. -/
  hU : Unram p n' W Qq O Kf ι σ jW ϖ
  /-- The number of steps. -/
  m : ℕ
  /-- The ranks. -/
  N : ℕ → ℕ
  /-- The weights. -/
  lam : ∀ j, V → Fin n' → Fin (N j) → ℤ
  /-- The levels. -/
  lev : ∀ j, Level V (N j) Qq O
  /-- Their class representatives. -/
  reps : ∀ j, ClassReps (W := W) (lev j)
  /-- The coefficient lattices. -/
  Λ : ∀ j, Tup W Qq V (N j) → Set (Pol (V × Fin n') (N j) Kf)
  /-- The steps. -/
  K : ∀ j, LFn W Qq Kf V n' (N j) →ₗ[Kf] LFn W Qq Kf V n' (N (j + 1))

variable {p : ℕ} {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O}

/-- **The integral forms** at level `j`. -/
def LocalChain.Int (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (j : ℕ) :
    Set (LFn W Qq Kf V n' (X.N j)) :=
  (X.lev j).forms ι σ (X.lam j) (X.Λ j)

/-- **`F ∈ ϖ^{⌈2g⌉}·Int_j`** (`v(p) = 1`, `ϖ² = p`). -/
def LocalChain.vGe (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (j : ℕ)
    (F : LFn W Qq Kf V n' (X.N j)) (g : ℝ) : Prop :=
  ∃ G ∈ X.Int j, F = ((algebraMap O Kf ϖ) ^ (⌈2 * g⌉)) • G

/-- **The composite** `chain j = K (j−1) ∘ … ∘ K 0`. -/
def LocalChain.chain (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) :
    ∀ j, LFn W Qq Kf V n' (X.N 0) →ₗ[Kf] LFn W Qq Kf V n' (X.N j)
  | 0 => LinearMap.id
  | j + 1 => X.K j ∘ₗ X.chain j

/-- **The served Hecke-product lattice** `Iprod(S, srv)`: the `O`-span of `∏_{v ∈ B} y_v^m(ϖ^{Σ_{v ∈ srv∖B} S_v}F)`
(`SelectionLemma.selSpan`'s set), `B ⊆ srv`, `F ∈ Int_0` (`y_v` the type-`r` Hecke operator at level 0). -/
def LocalChain.Iprod (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (r : ℕ) (S : V → ℕ)
    (srv : Finset V) : Submodule O (LFn W Qq Kf V n' (X.N 0)) :=
  Submodule.span O {F | ∃ B ⊆ srv, ∃ Lv : List V, Lv.Nodup ∧ Lv.toFinset = B ∧ ∃ F₀ ∈ X.Int 0,
    F = Lv.foldr (fun v G => (hecke (n' := n') p r (X.lam 0) v)^[X.m] G)
      (((algebraMap O Kf ϖ) ^ (∑ v ∈ srv \ B, S v)) • F₀)}

end Chain

/-! ## The contract -/

section Contract

open InertModel WeylFock

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {n' : ℕ} [NeZero n']
  {V : Type} [Fintype V] [DecidableEq V] {p : ℕ} {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O}

/-- **The D1 → D2 contract** at a served prime: kernels in frames with the Gaussian form, the expansion, level
equivariance, stabiliser losses (the bridge (K3) and the normalisation law (K4) are `Bridge` and `NormLaw`).
Everything is over `ℂ_[p]` through an embedding `emb` of `Kf`. -/
structure LocalKernels [Fact p.Prime] (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) where
  /-- The embedding of the coefficients. -/
  emb : Kf →+* ℂ_[p]
  /-- It detects `O`. -/
  emb_int : ∀ x : Kf, ‖emb x‖ ≤ 1 ↔ x ∈ (algebraMap O Kf).range
  /-- The frame uniformiser. -/
  ϖc : ℂ_[p]
  /-- `ϖ^{p²−1} = p`. -/
  ϖc_pow : ϖc ^ (p ^ 2 - 1) = p
  /-- The Gaussian constant. -/
  γ : ℂ_[p]
  /-- It is integral. -/
  γ_le : ‖γ‖ ≤ 1
  /-- The kernel series of step `j` from `L` to `L′`, in the pair's frame. -/
  ser : ∀ j, Tup W Qq V (X.N j) → Tup W Qq V (X.N (j + 1)) →
    MvPowerSeries ((V × ZMod n') × Fin (X.N (j + 1)) × Fin (X.N j)) ℂ_[p]
  /-- The kernel operator of a series for the pair `(L, L′)` (jet operator in the pair's frame). -/
  kerOp : ∀ j, Tup W Qq V (X.N j) → Tup W Qq V (X.N (j + 1)) →
    MvPowerSeries ((V × ZMod n') × Fin (X.N (j + 1)) × Fin (X.N j)) ℂ_[p] →ₗ[ℂ_[p]]
      (Pol (V × Fin n') (X.N j) ℂ_[p] →ₗ[ℂ_[p]] Pol (V × Fin n') (X.N (j + 1)) ℂ_[p])
  /-- The per-pair scalar (normalisation and unit). -/
  scal : ∀ j, Tup W Qq V (X.N j) → Tup W Qq V (X.N (j + 1)) → ℂ_[p]
  /-- **(K1) Expansion**: the step at `L′` is the mass-weighted sum over the class representatives. -/
  expand : ∀ j < X.m, ∀ F ∈ X.Int j, ∀ L' : Tup W Qq V (X.N (j + 1)), (∀ v, (L' v).IsLattice Qq) →
    MvPolynomial.map emb (X.K j F L') = ∑ L ∈ (X.reps j).R,
      ((stab (X.lev j) L : ℂ_[p])⁻¹ * scal j L L') • kerOp j L L' (ser j L L') (MvPolynomial.map emb (F L))
  /-- **(K2) The Gaussian frame form** (D1b-8 in each pair's frame). -/
  gauss : ∀ j L L', ∃ R : MvPowerSeries ((V × ZMod n') × Fin (X.N (j + 1)) × Fin (X.N j)) ℂ_[p],
    IsIntK R ∧ IsMixInt ϖc R ∧
    ser j L L' = posGauss ϖc (Equiv.prodCongr (Equiv.refl V) (Equiv.addRight (1 : ZMod n'))) (fun _ => γ) * R
  /-- **(K5) Level equivariance** of the scaled kernels. -/
  equiv : ∀ j (γ' : (X.lev j).Γ) L L' G, scal j ((X.lev j).smul γ' L) L' •
      kerOp j ((X.lev j).smul γ' L) L' (ser j ((X.lev j).smul γ' L) L')
        (MvPolynomial.map emb (algebraMap O Kf ((X.lev j).χ γ' : O) • (X.lev j).actF ι σ (X.lam j) γ' G)) =
    scal j L L' • kerOp j L L' (ser j L L') (MvPolynomial.map emb G)
  /-- The stabiliser losses. -/
  dG : ℕ → ℕ
  /-- **Stabiliser losses** `v_p|Stab L₀| ≤ dG j`. -/
  dG_spec : ∀ j, ∀ L ∈ (X.reps j).R, padicValNat p (stab (X.lev j) L) ≤ dG j

variable [Fact p.Prime]

/-- **`ℂ_p`-combinations of lattice vectors** with coefficients of valuation `≥ g`. -/
def InLatC (emb : Kf →+* ℂ_[p]) {N : ℕ} (Λ : Set (Pol (V × Fin n') N Kf)) (g : ℝ)
    (y : Pol (V × Fin n') N ℂ_[p]) : Prop :=
  y ∈ AddSubgroup.closure {y' | ∃ a : ℂ_[p], ‖a‖ ≤ (p : ℝ) ^ (-g) ∧ ∃ z ∈ Λ, y' = a • MvPolynomial.map emb z}

/-- **A column family of a target weight**: the shape `(colN, hts)` of step `j` at every orbit, with Z-columns
`I`. -/
def shapeCD (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (j : ℕ)
    (cN : V → ZMod n' → ℕ) (cH : ∀ v s, Fin (cN v s) → ℕ) (hle : ∀ v s c, cH v s c ≤ X.N j)
    (I : ∀ v s c, Fin (cH v s c) → Fin (X.N (j + 1))) : V → ColData n' (X.N j) (X.N (j + 1)) :=
  fun v => ⟨cN v, cH v, hle v, I v⟩

/-- **(K3) The bridge** (D1d: column-factor integrality and `N′`-scaling): for every edge-moved target `L″`
(type `i₀ v` below `L′_v`, or `L′_v` when `i₀ v = 0`) and every series `f`, if all weighted frame jets of `f` (all
integral frames, all Z-columns, the step's shape) are `≤ p^{−(g + ρ·deg)}`, then the kernel of `f` for `(L, L″)`
maps `Λ_j(L)` into `p^{−N′(i₀)}·(ℂ_p-valuation-g combinations of Λ_{j+1}(L′))`. -/
def Bridge (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (Kr : LocalKernels X)
    (cN : ℕ → V → ZMod n' → ℕ) (cH : ∀ j v s, Fin (cN j v s) → ℕ) (hle : ∀ j v s c, cH j v s c ≤ X.N j)
    (Nprime : ℕ → V → ℕ → ℤ) : Prop :=
  ∀ j < X.m, ∀ (L : Tup W Qq V (X.N j)) (L' L'' : Tup W Qq V (X.N (j + 1))) (i₀ : V → ℕ),
    (∀ v, (L v).IsLattice Qq) → (∀ v, (L' v).IsLattice Qq) →
    (∀ v, (i₀ v = 0 ∧ L'' v = L' v) ∨ (1 ≤ i₀ v ∧ IsEdge (n' := n') p (i₀ v) (L'' v) (L' v))) →
    ∀ (f : MvPowerSeries ((V × ZMod n') × Fin (X.N (j + 1)) × Fin (X.N j)) ℂ_[p]) (g : ℝ),
      (∀ (T : V × ZMod n' → Fin (X.N j) → Fin (X.N j) → ℂ_[p]), (∀ x i α, ‖T x i α‖ ≤ 1) →
        ∀ I, ‖(p : ℂ_[p]) ^ (∑ v, heckeExp (i₀ v) (shapeCD X j (cN j) (cH j) (hle j) I v)) *
          frameJetV T (shapeCD X j (cN j) (cH j) (hle j) I) f‖ ≤
            (p : ℝ) ^ (-(g + rhoL p * ∑ v, degC (shapeCD X j (cN j) (cH j) (hle j) I v)))) →
      ∀ G ∈ X.Λ j L, InLatC Kr.emb (X.Λ (j + 1) L') g
        (((p : ℂ_[p]) ^ (∑ v, Nprime (j + 1) v (i₀ v))) • Kr.scal j L L'' •
          Kr.kerOp j L L'' f (MvPolynomial.map Kr.emb G))

/-- **(K4) The normalisation law**: `scal·ker(L, L′) = s_j·∏_v u_v^{len L_v}·u′_v^{len L′_v}·
p^{−(n′/2)·volE_v}·Ξ_j(1_{Hom(L,L′)})`, `volE_v = N_j·len L′_v − N_{j+1}·len L_v`, `Ξ_j` additive, lengths drop by
`i` along type-`i` edges. -/
def NormLaw (X : LocalChain (W := W) (n' := n') (V := V) p ι σ jW ϖ) (Kr : LocalKernels X) : Prop :=
  ∀ j < X.m, ∃ (s : ℂ_[p]) (u u' : V → ℂ_[p]) (len : ∀ i, Tup W Qq V (X.N i) → V → ℤ)
    (Ξ : ((V → Matrix (Fin (X.N (j + 1))) (Fin (X.N j)) Qq) → ℚ) →+
      (Pol (V × Fin n') (X.N j) ℂ_[p] →ₗ[ℂ_[p]] Pol (V × Fin n') (X.N (j + 1)) ℂ_[p])),
    s ≠ 0 ∧ (∀ v, ‖u v‖ = 1 ∧ ‖u' v‖ = 1) ∧
    (∀ i (L : Tup W Qq V (X.N i)) v (L₁ : Submodule W (Fin (X.N i) → Qq)) r, IsEdge (n' := n') p r L₁ (L v) →
      len i (Function.update L v L₁) v = len i L v - r ∧
        ∀ v' ≠ v, len i (Function.update L v L₁) v' = len i L v') ∧
    ∀ (L : Tup W Qq V (X.N j)) (L' : Tup W Qq V (X.N (j + 1))), (∀ v, (L v).IsLattice Qq) →
      (∀ v, (L' v).IsLattice Qq) →
      Kr.scal j L L' • Kr.kerOp j L L' (Kr.ser j L L') =
        (s * ∏ v, (u v ^ len j L v * u' v ^ len (j + 1) L' v *
          (p : ℂ_[p]) ^ (-(((n' / 2 : ℕ) : ℤ) * ((X.N j : ℤ) * len (j + 1) L' v - X.N (j + 1) * len j L v))))) •
        Ξ (fun x => by classical exact if ∀ v, MapsInto (x v) (L v) (L' v) then 1 else 0)

end Contract

end LocalContract
