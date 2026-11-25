import Mathlib
import HermClasses
import WeylFock

/-!
# Branching, periods, the target `C_u` and the sources `N_ω`

Layer L6 of the sharp frontier (`docs/rh-rebuild.md`). Generic in the CM field `E`, the coefficient field `L`, the
CM type `Φ` and `τ : Φ → (E →+* L)`. Rank conventions: the chain ends on `X = E^{n+1}` (`n + 1 = N_m`), the
branching space is `X′ = E^n`.

**The interlacing weight** (L6.1, `sg`, `sgT`). `sg = sgHC − ρ_n` with
`sgHC = (v; for each q < m: −b_q, −e_q + (t−1)/2, …, −e_q − (t−1)/2)` and `ρ_n(i) = (n−1)/2 − i`, then
`sgT = sg` (the archive's `sgTrue = sg − m·h` with its `sgHC` carrying an extra `m(t+1)/2`; the shifts cancel, so
the block-`q` entries of `sgT` match `λ_m`). All entries are integers for the spec's ranks (`n = N_m − 1` odd, `t`
odd). As in
`WeylFock.wt`, the parameter families `v`, `b`, `e` are indexed by `ℕ` (extend by zero).

**The branching map** (L6.1, `br`). `br = (c_Br·∏_τ τ(tz)^{−nBr(λ_τ, σ_τ)})·Π_σ ∘ coefLast`, where `coefLast` takes
the coefficient of `∏_{τ,s} y_{τ,N,s}^{λ_{τ,s}−σ_{τ,s}}` (last row) as a polynomial in the top-left blocks
(`Finsupp.lcomapDomain`, so it is linear by construction). `c_Br ≠ 0` is a parameter. **`Π_σ` is a parameter**, an
`L`-linear map with the defining property `IsFockProj` of the Fock-orthogonal projection onto `∇_L(natW σ)`, the
`L`-span of `Δ(σ)`. (The bilinear and the hermitian projections agree: `∇_L(ν)` is defined over `ℚ`.)

**The period** (L6.3, `per`). For the chain's output `Φm`, read on points of rank `N_m`, and a row `F`:
`P(Φm, F) = Σ_c mass(c)·pair_σ(br(Φm(pt(rep c))), F(c))`, with `pair_σ` the bilinear normalised Fischer pairing
(`fockWith id`, normalised by the highest-weight vector, as in `WeylFock.Delta`). **Rows are finitely supported**
(`Cl →₀ Pol`): the classes are finite, so these are all functions, and the period is a finite sum, linear in `Φm`
(`perMap`) with no finiteness hypothesis; `per_eq_classSum` recovers the spec's `Σᶠ` (`HermClasses.classSum`).
**Interface:** `Φm` is any function on a type `Y` of points of rank `N_m` (`Col`), read at the point `pt x` over the
representative `x` of each class (audit 8, S2–S3: the archive's column depends on the frames, not only on the
lattice); L7 takes `Y` the decorated lattices of rank `N_m` and `pt` the decorated lift `HermClasses.tilQ`.

**Levels.** The class machinery is generic in a group action (`HermClasses.Cl`), so every level `μ` (the untwisted
`μ0` and the twisted tuples) is the same construction on its own classes: `PerData` bundles, for each `μ`, the
point of rank `N_m` over a point (`pt`) and its `Lsh`, the row space `V0_μ`, and the chain `col_μ`. **`V0_μ` is a
parameter**: the spec's `e·Amb_μ` needs the type group `𝔊` and an existential set of irreducible characters
(abstract in the archive). The integral rows are defined: `R_μ = {F ∈ V0_μ : F(c) ∈ ∇_{Lsh(rep c)}(σ) ∀c}`
(`rows`, with `WeylFock.nablaN`).

**The target** (L6.3–L6.4). `B_ω = P_{μ0}(·)|_{V0_{μ0}}` (`PerData.P`), `W_u = Σ_ω B_ω(V_ω)` (`PerData.W`, inside
`V0 → L`). The twist data `Tw`, `μ(w)` and the transfers `(τ_μ, ze_μ)` are parameters (`Twist`), with the spec's
properties in `Twist.IsTransfer`. `τ_μ` is taken on the ambient `V0_{μ0} → L`; only its restriction to `W_u` enters.
`C_u = {f ∈ W_u : f(R_{μ0}) ⊆ O_{L,(w)} ∀w ∉ Tw, τ_{μ(w)}(f)(R_{μ(w)}) ⊆ O_{L,(w)} ∀w ∈ Tw}` (`Ctgt`).

**The sources** (L6.5). `N_ω = {φ ∈ 𝔞⁻¹M_ω : B_ωφ ∈ C_u}` (`Nsrc`), with `M_ω` an `O_L`-submodule of the source
space `V_ω` and `𝔞` a parameter; `𝔞⁻¹M = {x : 𝔞x ⊆ M}` (`ainv`), which is the fractional-ideal product for a nonzero
`𝔞` (L7 supplies `𝔞 ≠ 0`).

**Sanity theorems:** `coeff_coefLast`, `per_eq_classSum`, `mem_Ctgt`, `Nsrc_le`.
-/

namespace PeriodTarget

open MvPolynomial NumberField IsDedekindDomain HermClasses WeylFock

noncomputable section

/-! ## The interlacing weight (L6.1) -/

section Weight

variable {Φ : Type*} {n : ℕ}

/-- `sgHC = (v_0, …, v_{k−2}; for each q: −b_q, −e_q + (t−1)/2, …, −e_q − (t−1)/2)`, on `Fin n`; meant for
`n = N_m − 1 = k − 1 + m(t+1)`. Entry `k − 1 + q(t+1) + r` is `−b_q` for `r = 0` and `−e_q + (t+1)/2 − r` else. -/
def sgHC (k t : ℕ) (v b e : Φ → ℕ → ℤ) : Φ → Fin n → ℤ := fun ρ i =>
  if (i : ℕ) < k - 1 then v ρ i
  else if ((i : ℕ) - (k - 1)) % (t + 1) = 0 then -b ρ (((i : ℕ) - (k - 1)) / (t + 1))
  else -e ρ (((i : ℕ) - (k - 1)) / (t + 1)) + ((t + 1) / 2 : ℕ) - (((i : ℕ) - (k - 1)) % (t + 1) : ℕ)

/-- `ρ_n(i) = (n−1)/2 − i` (exact for odd `n`, as `n = N_m − 1`). -/
def rhoW (i : Fin n) : ℤ := ((n - 1) / 2 : ℕ) - (i : ℤ)

/-- The interlacing weight `sg = sgHC − ρ_{N_m−1}`. -/
def sg (k t : ℕ) (v b e : Φ → ℕ → ℤ) : Φ → Fin n → ℤ := fun ρ i => sgHC k t v b e ρ i - rhoW i

/-- `sgT = sg`: the weight of the rows and of the branching map. Meant for L7. The library's `sg` (whose `sgHC` omits
the archive's constant `m(t+1)/2`) already equals the archive's `sgTrue = sg − m·h`, so no shift is applied; `m` is
kept as an (unused) argument so that callers do not change. -/
def sgT (k t _m : ℕ) (v b e : Φ → ℕ → ℤ) : Φ → Fin n → ℤ := sg k t v b e

end Weight

/-! ## The pairing, the projection and the branching map (L6.1) -/

section Branch

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

/-- The bilinear normalised Fischer pairing `pair_σ(F, G) = fock(F, G)/fock(hw, hw)`, without conjugation, with
`hw` the highest-weight vector of `natW σ` (CoefModB). -/
def pair (σ : Φ → Fin n → ℤ) (F G : Pol Φ n L) : L :=
  fockWith (RingHom.id L) F G / fockWith (RingHom.id L) (hw L fun ρ => natW (σ ρ)) (hw L fun ρ => natW (σ ρ))

omit [DecidableEq Φ] in
/-- `pair` is additive in its first argument. Used by `perMap`. -/
theorem pair_add_left (σ : Φ → Fin n → ℤ) (F F' G : Pol Φ n L) : pair σ (F + F') G = pair σ F G + pair σ F' G := by
  simp [pair, fockWith, add_mul, Finset.sum_add_distrib, add_div]

omit [DecidableEq Φ] in
/-- `pair` is homogeneous in its first argument. Used by `perMap`. -/
theorem pair_smul_left (σ : Φ → Fin n → ℤ) (a : L) (F G : Pol Φ n L) : pair σ (a • F) G = a * pair σ F G := by
  simp [pair, fockWith, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

omit [DecidableEq Φ] in
/-- `pair σ F 0 = 0`. Used by `per_eq_classSum`. -/
@[simp] theorem pair_zero_right (σ : Φ → Fin n → ℤ) (F : Pol Φ n L) : pair σ F 0 = 0 := by
  simp [pair, fockWith]

/-- `P` is the Fock-orthogonal projection onto `∇_L(natW σ)`, the span of `Δ(σ)`: `P F` lies there and `F − P F` is
Fock-orthogonal to it. The defining property of the parameter `Π_σ` of `br`; meant for L7. -/
def IsFockProj (σ : Φ → Fin n → ℤ) (P : Pol Φ n L →ₗ[L] Pol Φ n L) : Prop :=
  ∀ F, P F ∈ nabla L (fun ρ => natW (σ ρ)) ∧
    ∀ G ∈ nabla L (fun ρ => natW (σ ρ)), fockWith (RingHom.id L) (F - P F) G = 0

variable (Φ n) in
/-- The variables of the top-left blocks: `(τ, a, b) ↦ (τ, a, b)` with `a, b < n`. -/
def topLeft : Φ × Fin n × Fin n → Φ × Fin (n + 1) × Fin (n + 1) := fun p => (p.1, p.2.1.castSucc, p.2.2.castSucc)

omit [Fintype Φ] [DecidableEq Φ] in
/-- `topLeft` is injective. -/
theorem topLeft_injective : Function.Injective (topLeft Φ n) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp_all [topLeft, Prod.ext_iff]

/-- The last-row monomial `∏_{τ,s<n} y_{τ,n,s}^{ex τ s}`, as an exponent. -/
def lastMon (ex : Φ → Fin n → ℕ) : (Φ × Fin (n + 1) × Fin (n + 1)) →₀ ℕ :=
  ∑ ρ, ∑ s, Finsupp.single (ρ, Fin.last n, s.castSucc) (ex ρ s)

/-- `coefLast`: the coefficient of the last-row monomial `lastMon ex`, as a polynomial in the top-left blocks. -/
def coefLast (ex : Φ → Fin n → ℕ) : Pol Φ (n + 1) L →ₗ[L] Pol Φ n L :=
  (AddMonoidAlgebra.coeffLinearEquiv L).symm.toLinearMap ∘ₗ
    Finsupp.lcomapDomain (fun d => Finsupp.mapDomain (topLeft Φ n) d + lastMon ex)
      ((add_left_injective _).comp (Finsupp.mapDomain_injective topLeft_injective)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv L).toLinearMap

omit [DecidableEq Φ] in
/-- **Sanity:** the coefficient of `d` in `coefLast F` is that of `d·lastMon` in `F`. -/
theorem coeff_coefLast (ex : Φ → Fin n → ℕ) (F : Pol Φ (n + 1) L) (d : (Φ × Fin n × Fin n) →₀ ℕ) :
    (coefLast ex F).coeff d = F.coeff (Finsupp.mapDomain (topLeft Φ n) d + lastMon ex) := rfl

/-- `nBr(λ, σ) = Σλ − Σσ`, the degree in the last row. -/
def nBr (l : Fin (n + 1) → ℤ) (s : Fin n → ℤ) : ℤ := ∑ i, l i - ∑ i, s i

/-- The integer factor `cBr(λ, σ) = ∏_{i<n} ∏_{v ∈ R_i ∖ {σ_i}} ∏_{j<n} ((v − (i+1)) − (σ_j − (j+1)))` (spec-5 §1),
with `R_i = [λ_{i+1}, min(λ_i, λ_{i+1} + d₀)] ∩ ℤ` and `d₀ = Σ_i (σ_i − λ_{i+1})`; nonzero under interlacing. For
`brConst`. -/
def cBrZ (l : Fin (n + 1) → ℤ) (s : Fin n → ℤ) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Finset.Icc (l i.succ) (min (l i.castSucc) (l i.succ + ∑ k, (s k - l k.succ)))).erase (s i),
    ∏ j : Fin n, ((v - ((i : ℕ) + 1 : ℤ)) - (s j - ((j : ℕ) + 1 : ℤ)))

variable (L) in
/-- `ξ = ∏_τ ∏_{i<n} D_{τ,i+1}^{a_i}·Z_{τ,i}^{b_i}` (spec-5 §1), rank `n + 1`, with `a_i = σ_i − λ_{i+1}`,
`b_i = λ_i − σ_i`, `D_{i+1}` the leading `(i+1)`-minor and `Z_i` the `(i+1)`-minor on the rows `0, …, i − 1, n` and
the first `i + 1` columns. For `brConst`. -/
def xiBr (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) : Pol Φ (n + 1) L :=
  ∏ ρ, ∏ i : Fin n, minor ρ i.castSucc (Fin.castLE i.castSucc.isLt) ^ (σ ρ i - lam ρ i.succ).toNat *
    minor ρ i.castSucc (fun r => if h : (r : ℕ) < i then ⟨r, by have := i.isLt; omega⟩ else Fin.last n) ^
      (lam ρ i.castSucc - σ ρ i).toNat

variable (L) in
/-- **The branching constant** `c_Br = ∏_τ cBr(λ_τ, σ_τ)·fock(ξ_τ, ξ_τ)/fock(hw_{λ_τ}, hw_{λ_τ})` (spec-5 §1), with
`fock` the Fock form without conjugation. The `τ`-factors' Fock quotients are taken together, as `pair λ ξ ξ` with
`ξ = xiBr` the product over `τ`: the Fock form is multiplicative over disjoint blocks. Pins `BrPinned`'s `c_Br` (L7). -/
def brConst (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) : L :=
  (∏ ρ, (cBrZ (lam ρ) (σ ρ) : L)) * pair lam (xiBr L lam σ) (xiBr L lam σ)

variable {E : Type*} [Field E] (τ : Φ → (E →+* L))

/-- The branching map `br = (c_Br·∏_τ τ(tz)^{−nBr(λ_τ, σ_τ)})·Π_σ ∘ coefLast`, from `VV(λ)` (rank `n + 1`) to
`VV(σ)` (rank `n`), with the last-row exponents `λ_{τ,s} − σ_{τ,s}`. `P` is `Π_σ` (`IsFockProj`). Meant for L7. -/
def br (tz : E) (P : Pol Φ n L →ₗ[L] Pol Φ n L) (cBr : L) (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) :
    Pol Φ (n + 1) L →ₗ[L] Pol Φ n L :=
  (cBr * ∏ ρ, τ ρ tz ^ (-nBr (lam ρ) (σ ρ))) • (P ∘ₗ coefLast fun ρ s => (lam ρ s.castSucc - σ ρ s).toNat)

end Branch

/-! ## The period (L6.3) -/

section Period

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [Field L]
  {G X : Type*} [Group G] [MulAction G X]

variable (Φ n L) in
/-- The chain's output, read on a type `Y` of points of rank `N_m = n + 1`: a `Pol`-valued function on them (L7: the
decorated lattices of rank `N_m`). -/
abbrev Col (Y : Type*) := Y → Pol Φ (n + 1) L

/-- The period `P(Φm, F) = Σ_c mass(c)·pair_σ(b(Φm(pt(rep c))), F(c))` of a row `F` (finitely supported on the
classes `Cl G X` of `X′`), where `pt x` is the point of rank `n + 1` over a point `x` of `X′` (L7: the decorated lift
`tilQ x`, frames included) and `b` is the branching map. -/
def per {Y : Type*} (pt : X → Y) (b : Pol Φ (n + 1) L →ₗ[L] Pol Φ n L) (σ : Φ → Fin n → ℤ) (Φm : Col Φ n L Y)
    (F : Cl G X →₀ Pol Φ n L) : L :=
  F.sum fun c p => (mass c : L) * pair σ (b (Φm (pt c.out))) p

/-- The period is `L`-linear in the chain's output. Used by `PerData.P`. -/
def perMap {Y : Type*} (pt : X → Y) (b : Pol Φ (n + 1) L →ₗ[L] Pol Φ n L) (σ : Φ → Fin n → ℤ) :
    Col Φ n L Y →ₗ[L] ((Cl G X →₀ Pol Φ n L) → L) where
  toFun Φm := per pt b σ Φm
  map_add' Φ₁ Φ₂ := by
    funext F
    simp only [per, Pi.add_apply, map_add, pair_add_left, mul_add, Finsupp.sum_add]
  map_smul' a Φ₁ := by
    funext F
    simp only [per, Pi.smul_apply, map_smul, pair_smul_left, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

omit [DecidableEq Φ] in
/-- **Sanity:** the period is the spec's mass-weighted `Σᶠ` over the classes (`HermClasses.classSum`). -/
theorem per_eq_classSum [CharZero L] {Y : Type*} (pt : X → Y) (b : Pol Φ (n + 1) L →ₗ[L] Pol Φ n L)
    (σ : Φ → Fin n → ℤ) (Φm : Col Φ n L Y) (F : Cl G X →₀ Pol Φ n L) :
    per pt b σ Φm F = classSum fun c => pair σ (b (Φm (pt c.out))) (F c) := by
  rw [classSum, finsum_eq_sum_of_support_subset _ (s := F.support) fun c hc => ?_, per, Finsupp.sum]
  · simp only [Rat.smul_def]
  · contrapose! hc
    simp [Finsupp.notMem_support_iff.mp hc]

end Period

/-! ## The rows (L6.2) -/

section Rows

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [NumberField E] [Field L]
  [NumberField L] (τ : Φ → (E →+* L)) {G X : Type*} [Group G] [MulAction G X]

/-- The integral rows `R = M̃ ∩ V0 = {F ∈ V0 : F(c) ∈ ∇_{Lsh(rep c)}(σ) ∀c}`, where `lsh x` is the lattice `Lsh(x)` of a
point (`HermClasses.Lsh` at the untwisted level). The row space `V0 = e·Amb` is a parameter (module docstring). -/
def rows (σ : Φ → Fin n → ℤ) (lsh : X → Submodule (𝓞 E) (Fin n → E)) (V0 : Submodule L (Cl G X →₀ Pol Φ n L)) :
    Set V0 :=
  {F | ∀ c, (F : Cl G X →₀ Pol Φ n L) c ∈ nablaN τ σ (lsh c.out)}

end Rows

/-! ## The target (L6.3–L6.4) -/

section Target

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [NumberField E] [Field L]
  [NumberField L] (τ : Φ → (E →+* L)) {T : Type*} (G X : T → Type*) [∀ μ, Group (G μ)]
  [∀ μ, MulAction (G μ) (X μ)] {Ω : Type*} (Vs : Ω → Type*) [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)]
  (Y : Type*)

variable (Φ n E L) in
/-- The data of the levels `μ` (the untwisted `μ0` and the twisted tuples) and of the words `ω`, from which periods,
rows and the target are built:
* `tz = conj(π_T)`, the branching weight `σ = sgT` and, per word, the branching map `br ω` (with `λ = λ_m(ω)`);
* per level, the point `pt x ∈ Y` of rank `n + 1` at which the column is read over a point `x` of `X′` (L7: the
  decorated lift `tilQ`), the lattice `Lsh` (`lsh`) of `x`, and the row space `V0_μ` (a parameter);
* per level and word, the chain `col μ ω : V_ω → Col` of tuple `μ`, a function on `Y` (L5, connected by L7). -/
structure PerData where
  /-- `tz = conj(π_T)`. -/
  tz : E
  /-- The weight `σ = sgT` of the rows. -/
  σ : Φ → Fin n → ℤ
  /-- The branching map of a word. -/
  br : Ω → (Pol Φ (n + 1) L →ₗ[L] Pol Φ n L)
  /-- The point of rank `n + 1` at which the column is read, over a point of `X′` at level `μ`. -/
  pt : ∀ μ : T, X μ → Y
  /-- The lattice `Lsh` of a point of `X′` at level `μ`. -/
  lsh : ∀ μ : T, X μ → Submodule (𝓞 E) (Fin n → E)
  /-- The row space `V0_μ = e·Amb_μ`. -/
  V0 : ∀ μ : T, Submodule L (Cl (G μ) (X μ) →₀ Pol Φ n L)
  /-- The chain `φ ↦ col_μ φ` of tuple `μ`, on the sources of a word. -/
  col : T → ∀ ω : Ω, Vs ω →ₗ[L] Col Φ n L Y

variable {G X Vs Y} (D : PerData Φ n E L G X Vs Y)

/-- The period functionals `φ ↦ P_μ(col_μ φ, ·)|_{V0_μ}`; at `μ0` this is `B_ω`. -/
def PerData.P (μ : T) (ω : Ω) : Vs ω →ₗ[L] (D.V0 μ → L) :=
  LinearMap.funLeft L L (Subtype.val : D.V0 μ → _) ∘ₗ perMap (D.pt μ) (D.br ω) D.σ ∘ₗ D.col μ ω

/-- The integral rows `R_μ` of a level. -/
def PerData.R (μ : T) : Set (D.V0 μ) := rows τ D.σ (D.lsh μ) (D.V0 μ)

/-- `W_u = Σ_ω B_ω(V_ω) ⊆ (V0_{μ0})^*`. -/
def PerData.W (μ0 : T) : Submodule L (D.V0 μ0 → L) := ⨆ ω, LinearMap.range (D.P μ0 ω)

/-- The twist data `𝒯_u` and transfers, all parameters: the finite set `Tw` of places of `L` (closed under
conjugation, L7), the tuple `μ(w)` at `w ∈ Tw`, and for each tuple `μ` the transfer `τ_μ` (on the ambient
`V0_{μ0} → L`; only its restriction to `W_u` matters) and the scalars `ze_μ(ω)`. -/
structure Twist (μ0 : T) where
  /-- The twisted places. -/
  Tw : Finset (HeightOneSpectrum (𝓞 L))
  /-- The tuple `μ(w)` at a twisted place. -/
  μw : HeightOneSpectrum (𝓞 L) → T
  /-- The transfer `τ_μ`. -/
  tr : ∀ μ : T, (D.V0 μ0 → L) →ₗ[L] (D.V0 μ → L)
  /-- The scalar `ze_μ(ω)`. -/
  ze : T → Ω → L

variable {D}

/-- The spec's properties of the transfers, at every tuple `μ = μ(w)`, `w ∈ Tw`: `ze_μ(ω)` is a unit at `w`, and
the seesaw factorisation `τ_μ(B_ωφ) = ze_μ(ω)⁻¹·P_μ(φ, ·)`. Meant for L7. -/
def Twist.IsTransfer {μ0 : T} (tw : Twist D μ0) : Prop :=
  ∀ w ∈ tw.Tw, ∀ ω, w.valuation L (tw.ze (tw.μw w) ω) = 1 ∧
    ∀ φ, tw.tr (tw.μw w) (D.P μ0 ω φ) = (tw.ze (tw.μw w) ω)⁻¹ • D.P (tw.μw w) ω φ

/-- An element of `O_L` is integral at every finite place. -/
theorem coe_mem_Ow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) : (a : L) ∈ Ow w := w.valuation_le_one (K := L) a

/-- The functionals integral at `w` on a set `R`: `{f : f(R) ⊆ O_{L,(w)}}`, an `O_L`-module. -/
def IntOn (w : HeightOneSpectrum (𝓞 L)) {V : Type*} (R : Set V) : Submodule (𝓞 L) (V → L) where
  carrier := {f | ∀ r ∈ R, f r ∈ Ow w}
  add_mem' hf hg r hr := add_mem (hf r hr) (hg r hr)
  zero_mem' _ _ := zero_mem _
  smul_mem' a f hf r hr := by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem (coe_mem_Ow w a) (hf r hr)

/-- The target `C_u = {f ∈ W_u : f(R_{μ0}) ⊆ O_{L,(w)} ∀w ∉ Tw, τ_{μ(w)}(f)(R_{μ(w)}) ⊆ O_{L,(w)} ∀w ∈ Tw}`, an
`O_L`-submodule of `V0_{μ0} → L` inside `W_u`. Meant for L7. -/
def Ctgt {μ0 : T} (tw : Twist D μ0) : Submodule (𝓞 L) (D.V0 μ0 → L) :=
  (D.W μ0).restrictScalars (𝓞 L) ⊓ (⨅ (w) (_ : w ∉ tw.Tw), IntOn w (D.R τ μ0)) ⊓
    ⨅ (w) (_ : w ∈ tw.Tw), (IntOn w (D.R τ (tw.μw w))).comap ((tw.tr (tw.μw w)).restrictScalars (𝓞 L))

omit [NumberField E] in
/-- **Sanity:** membership in `C_u` is the spec's condition. -/
theorem mem_Ctgt {μ0 : T} (tw : Twist D μ0) (f : D.V0 μ0 → L) :
    f ∈ Ctgt τ tw ↔ f ∈ D.W μ0 ∧ (∀ w ∉ tw.Tw, ∀ r ∈ D.R τ μ0, f r ∈ Ow w) ∧
      ∀ w ∈ tw.Tw, ∀ r ∈ D.R τ (tw.μw w), tw.tr (tw.μw w) f r ∈ Ow w := by
  simp [Ctgt, IntOn, Submodule.mem_iInf, and_assoc]

end Target

/-! ## The sources (L6.5) -/

section Sources

variable {L : Type*} [Field L] {V : Type*} [AddCommGroup V] [Module (𝓞 L) V]

/-- `𝔞⁻¹M = {x : 𝔞x ⊆ M}`; for a nonzero ideal `𝔞` of the Dedekind domain `O_L` this is the product of the fractional
ideal `𝔞⁻¹` with `M`. -/
def ainv (𝔞 : Ideal (𝓞 L)) (M : Submodule (𝓞 L) V) : Submodule (𝓞 L) V where
  carrier := {x | ∀ a ∈ 𝔞, a • x ∈ M}
  add_mem' hx hy a ha := by rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' a _ := by rw [smul_zero]; exact M.zero_mem
  smul_mem' c x hx a ha := by rw [smul_comm]; exact M.smul_mem c (hx a ha)

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E : Type*} [Field E] [NumberField E] [NumberField L]
  (τ : Φ → (E →+* L)) {T : Type*} {G X : T → Type*} [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (X μ)] {Ω : Type*}
  {Vs : Ω → Type*} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)] [∀ ω, Module (𝓞 L) (Vs ω)]
  [∀ ω, IsScalarTower (𝓞 L) L (Vs ω)] {Y : Type*} {D : PerData Φ n E L G X Vs Y} {μ0 : T}

/-- The source `N_ω = {φ ∈ 𝔞_ω⁻¹M_ω : B_ωφ ∈ C_u}`, with `M_ω` the integral forms of the word (L4.3) and `𝔞_ω` a
nonzero ideal, both parameters. Meant for L7. -/
def Nsrc (tw : Twist D μ0) (𝔞 : Ω → Ideal (𝓞 L)) (M : ∀ ω, Submodule (𝓞 L) (Vs ω)) (ω : Ω) :
    Submodule (𝓞 L) (Vs ω) :=
  ainv (𝔞 ω) (M ω) ⊓ (Ctgt τ tw).comap ((D.P μ0 ω).restrictScalars (𝓞 L))

omit [NumberField E] in
/-- **Sanity:** `N_ω ⊆ 𝔞_ω⁻¹M_ω`, the inclusion behind the bound on `μ_max(N_ω)`. -/
theorem Nsrc_le (tw : Twist D μ0) (𝔞 : Ω → Ideal (𝓞 L)) (M : ∀ ω, Submodule (𝓞 L) (Vs ω)) (ω : Ω) :
    Nsrc τ tw 𝔞 M ω ≤ ainv (𝔞 ω) (M ω) :=
  inf_le_left

end Sources

end

end PeriodTarget
