import FirstMeans
import LocalRank
import LocalOrbit

/-!
# The first local theorem: assembly from the flat-weight ranks (L5, layer 1)

Module 10 of the L5/L6 plan: L5's layer 1 except the cloud step, at one orbit of an inert prime `p` in the setting
`Unram`, on the good systems and the assembly of `LocalRank`. The inputs of the other layers and modules (I1, I2, I3;
the harmonic splitting; the Weyl count; the cloud step; the off-top step) are hypotheses, stated as `Prop`s so that
the later modules can discharge them; everything else is proved. The setting-free half (windows, means, numerics,
`FirstHyp`, `depthI`, `IsShape`) is `FirstMeans`.

**The tensor of polynomial pairs** `H(A, B) = ⊗_{tops} Sym^{A_s} ⊗ Sym^{B_s}∨` is a tuple of two orbits (`lamH`):
`true` with the row weights `(A_s, 0, …, 0)`, `false` with the column weights `(0, …, 0, −B_s)`, both at the same
lattice; its `∇`, edge lattices, pairing, families and good systems are those of `LocalLattice`/`LocalRank` for the
tuple (`nabV`, `edgeLatV`, `pairEV`, `edgeDualV`, `SrcFamV`, `TgtFamV`, `GoodSysV`), with `A₁(H(A, B)) = A₁(fl(A, B))`
(`topAV_lamH`).

**The hypotheses** (exact statements in the definitions).
* `InputRank` (I1, layer 2's LT): at every `(A, B)` of the enlarged box some type-1 edge carries a good system for
  `H(A, B)` of size `(1 − κ_P − Σ_x κ_T(x, A, B))·dim H(A, B)/g` (`g = (q^k − 1)/(q − 1)`, `gE`).
* `SegMean` (I2, layer 3's Theorem B, in `FirstMeans`): the mean of `κ_T(x)` over the coordinates owned by the segment
  of `x` is `≤ C_A·(s_x + 1)·N₁/Y`; I3 is the plain hypothesis `κ_P ≤ C_P·N·N₁/Y` of `first_local`.
* `HarmSplit` (A-N7): `Kf`-linear `io_j`, `pr_j` between the flat pieces `fl(A − j, B − j)` and `H(A, B)` with
  `Σ_j io_j∘pr_j = id`, integral up to `p^u` for every family of block lattices.
* `FlatDim` (the classical half of A-N10): `dim V(fl(α, β)) = ∏_s Har_m(α_s, β_s)`.
* `CloudStep` (A-N15, module 11): per-edge ranks at `fl(A, B)` and `fl(A + 2c, B + 2c)` give one at a top weight with
  extremes `(A + c, B + c)` and middle entries in `[−c, c]`, of fraction `κ₁ + 2κ₂ + 12Nkc/b′`.
* `OffTop` (A-N18): a per-edge rank of the top part gives one of the weight, at depth `+2n′c` and conductor `−2n′c`.

**Main results.**
* *The flat exceptional fraction* (`kappaF`, A-N5): the least `κ ∈ [0, 1]` with a per-edge rank
  `(1 − κ)·d(fl(α, β))/g`; it is attained (`kappaF_spec`, via `exists_nat_of_sInf`).
* *Splitting* (`goodSys_split`, A-N8): a good system of size `n` for `H(A, B)` gives good systems of sizes `ν_j`,
  `Σ_j ν_j ≥ n`, for the flat pieces at the same edge, denominator `D + 2u`.
* *The key inequality* (`key_ineq`, A-N11): `Σ_{j ∈ [0, J]^{TT}} κ_F(A − j, B − j)·d(fl(A − j, B − j)) ≤
  κ_X(A, B)·dim H(A, B)`.
* *The means* (`boxSum_kappaF_le`, A-N12–N13): on every shift `|τ| ≤ c` of the box, the sum of `κ_F` is at most
  `(4/3)·|W_A|^N·|W_B|^N·(C_P + C_A)·N·N₁/Y`.
* *The per-weight assembly* (`llp_first`, A-N19) and *the first local theorem* (`first_local`, A-N22): with
  `κ(a, b) = κ_F(a − c, b − c) + 2κ_F(a + c, b + c) + 12Nkc/b′` (`kappaFirst`), box mean `≤ C·N·N₁/Y` and
  `LLPAt(1, λ, t, D, κ(a, b), c*)` at every lattice, for the weights of the shape and `t ≥ t_I(a, b)`.

**The routes.** The splitting moves sources by `p^u ϖ^{d_j}·pr_j` (`d_j = Σ_s j_s = A₁(H) − A₁(fl_j)`, which converts
the edge scalings exactly, `prMap_mem_srcFam`) and targets by the `pairE`-adjoint of `p^u ϖ^{−d_j}·io_j`, built from a
`pairE`-dual pair of the flat piece (`adjMap`, `pairE_adjMap`, `adjMap_mem_tgtFam`); the Gram matrices then add up to
`p^{2u}z·1` and `LocalRank.smith_split` cuts them. The key inequality transports the split systems to every edge
(`goodSys_transport`) and bounds them above (`goodSys_card_le`), so `κ_F·d_j ≤ d_j − g·ν_j`, and sums with
`Σ_{j ∈ J(A, B)} d_j = dim H(A, B)` (`sum_jBox_har`, from `FlatDim` and `WeylCount.sum_prod_har`). The per-weight
assembly runs `κ_F(a ∓ c, b ∓ c)` through the cloud step and the off-top step to `λ` and assembles with
`LocalRank.llpAt_of_rankAll` (`2D + 1 ≤ c*`). The good-system calculus (closure of the families, monotonicity in the
depth, conductor and denominator, sub-systems) is `srcFam_closed`, `goodSys_mono`, `goodSys_le`, `rankAll_mono`.

**Readings of the planning statements.**
* *One setting per prime* (S1): `κ_F` is defined at the setting, so `first_local` quantifies over the setting (and the
  inputs, and their constants `C_t, C_I, C_A, C_P`) before `κ`; the spec's `∃ κ, … ∀ settings` is not used.
* *The enlarged windows* of I1 and I2 are `[⌈a⌉ − c, ⌊a + a/(kY)⌋ + c + J] × [⌈b_ℓ⌉ − c, ⌊b_u⌋ + c + J]`,
  `J = ⌊La·b′/k⌋` (Annex I: `[⌈a⌉, a + a/(kY) + 2J] × [b_ℓ, b_u + 2J]`): reaching down by `c` lets both shifts
  `(a ∓ c, b ∓ c)` of the box be averaged, so `κ` needs no "else 1" boundary branch (Annex I.5.6).
* I1 is asked at one edge (S8), with the size written through `dim H(A, B) = ∏_s C(A_s + m, m)·C(B_s + m, m)`
  (`FirstMeans.dimH`), the depth `⌊t₀(A, B)⌋` at the conductor `c₄ = c* + 2Nc + 2n′c` (`t0F`, `c4F`) and the denominator
  `D₀ = ⌊C_I·N·Y²·N₁²·k²·λ_a⌋`. `HarmSplit` needs only `Σ_j io_j∘pr_j = id` and the integrality (no direct-sum clause:
  the dimensions come from `FlatDim`). The splitting costs `D + 2u` (Annex I: `D + 4u`).
* The constants are explicit (S2): `C_H = 6C_I + 108`, `C = C_t + 16(C_P + C_A) + 1`, `u = N·⌈(k + 1)λ_a⌉`,
  `D_c = N·⌈k²λ_a⌉`, `λ_a = log_p(8a + k) + 1`.
* *Not here*: proofs of the hypotheses. `FlatDim` is the Weyl dimension formula for the repo's `∇` (its combinatorial
  side is `WeylCount`); `HarmSplit` needs the two-letter identification (Annex I's I4), not in `LetterFock`; `OffTop`
  needs the tensor factorisation `V(λ) = V(λ^top) ⊗ V(λ^off)` with its lattices and pairings.
-/

namespace FirstAssembly

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank LocalOrbit FirstMeans WeylCount Finset

open scoped Matrix Pointwise

noncomputable section

/-! ## The tensor of polynomial pairs and the edge lattices of a tuple -/

section Tuple

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {V : Type} [Fintype V] [DecidableEq V] {p n' k : ℕ}

variable (O) in
/-- **`∇(L)` of a tuple** with every orbit at the lattice `L`. -/
abbrev nabV (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (lamV : V → Fin n' → Fin k → ℤ) (L : Submodule W (Fin k → Qq)) :
    Set (Pol (V × Fin n') k Kf) :=
  NablaT O ι σ lamV fun _ => L

/-- **`∇` at the midpoint** of an edge `L″ ⊂ L`, for a tuple with every orbit at that edge. -/
abbrev nabMidV (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (V × Fin n') k Kf) :=
  nablaB (blockWt lamV) fun b => midBlk ι σ ϖ b.2 L'' L

/-- **`A_r` of a tuple**: `Σ_v topSum r lamV v`. -/
abbrev topAV (r : ℕ) (lamV : V → Fin n' → Fin k → ℤ) : ℤ := ∑ v, topSum r lamV v

/-- **The edge lattice of a tuple** `𝓡(L″ ⊂ L) = ϖ^{−A_r}·∇(mid)`. -/
def edgeLatV (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (r : ℕ) (lamV : V → Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (V × Fin n') k Kf) :=
  {F | algebraMap O Kf ϖ ^ topAV r lamV • F ∈ nabMidV ι σ ϖ lamV L'' L}

/-- **The pairing of a tuple** `pairE(F, G) = ⟨p^{A_r}F, G⟩`. -/
def pairEV (p r : ℕ) (lamV : V → Fin n' → Fin k → ℤ) :
    Pol (V × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf →ₗ[Kf] Kf :=
  ((p : Kf) ^ topAV r lamV) • nf (blockWt lamV)

/-- **The dual edge lattice of a tuple**: the `pairEV`-dual of `edgeLatV`. -/
def edgeDualV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ)
    (L'' L : Submodule W (Fin k → Qq)) : Submodule O (Pol (V × Fin n') k Kf) :=
  bdual O (pairEV p r lamV) (fun b => natW (blockWt lamV b)) (edgeLatV ι σ ϖ r lamV L'' L)

/-- **The source lattice of a tuple** at depth `t`: `ϖ^{−t}∇(L″) ∩ ⋂_{L″ ⊂ L′} 𝓡(L″ ⊂ L′)`. -/
def srcLatV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ) (t : ℕ)
    (L'' : Submodule W (Fin k → Qq)) : Set (Pol (V × Fin n') k Kf) :=
  (algebraMap O Kf ϖ ^ t)⁻¹ • nabV O ι σ lamV L'' ∩
    ⋂ (L' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L'), edgeLatV ι σ ϖ r lamV L'' L'

/-- **The target lattice of a tuple** at depth `t`: `ϖ^{−t}∇(L)^∨ ∩ ⋂_{L″ ⊂ L} 𝓡′(L″ ⊂ L)`. -/
def tgtLatV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ) (t : ℕ)
    (L : Submodule W (Fin k → Qq)) : Submodule O (Pol (V × Fin n') k Kf) :=
  bdual O (nf (blockWt lamV)) (fun b => natW (blockWt lamV b)) (algebraMap O Kf ϖ ^ t • nabV O ι σ lamV L) ⊓
    ⨅ (L'' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L), edgeDualV p r ι σ ϖ lamV L'' L

/-- **The source family of a tuple** at `L″ ⊂ L`: `srcLatV` cut to the `ϖ^c`-small vectors on the other edges out
of `L″`. -/
def SrcFamV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ) (t c : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (V × Fin n') k Kf) :=
  srcLatV p r ι σ ϖ lamV t L'' ∩
    ⋂ (L' : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L'' L') (_ : L' ≠ L),
      (algebraMap O Kf ϖ ^ c) • edgeLatV ι σ ϖ r lamV L'' L'

/-- **The target family of a tuple** at `L″ ⊂ L`: `tgtLatV` cut to the `ϖ^c`-small vectors on the other edges into
`L`. -/
def TgtFamV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ) (t c : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) : Set (Pol (V × Fin n') k Kf) :=
  (tgtLatV p r ι σ ϖ lamV t L : Set (Pol (V × Fin n') k Kf)) ∩
    ⋂ (L₁ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p r L₁ L) (_ : L₁ ≠ L''),
      (algebraMap O Kf ϖ ^ c) • (edgeDualV p r ι σ ϖ lamV L₁ L : Set (Pol (V × Fin n') k Kf))

/-- **A good system of a tuple** of size `n` at `L″ ⊂ L` (as `LocalRank.GoodSys`). -/
def GoodSysV (p r : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (lamV : V → Fin n' → Fin k → ℤ) (t c D : ℕ)
    (L'' L : Submodule W (Fin k → Qq)) (n : ℕ) : Prop :=
  ∃ (x y : Fin n → Pol (V × Fin n') k Kf) (z : O) (M : Matrix (Fin n) (Fin n) O),
    z ≠ 0 ∧ z ∣ (p : O) ^ D ∧ (∀ i, x i ∈ SrcFamV p r ι σ ϖ lamV t c L'' L) ∧
      (∀ i, y i ∈ TgtFamV p r ι σ ϖ lamV t c L'' L) ∧
      ∀ i l, ∑ m, pairEV p r lamV (x i) (y m) * algebraMap O Kf (M m l) = if i = l then algebraMap O Kf z else 0

end Tuple

/-! ## The tensor of polynomial pairs and the hypotheses -/

section Hyp

variable {n' k : ℕ}

/-- **The tensor of polynomial pairs** `H(A, B)` as a tuple of two orbits: the orbit `true` has the row weights
`(A_s, 0, …, 0)`, the orbit `false` the column weights `(0, …, 0, −B_s)` at the tops (`0` elsewhere). After `lamAt`
the blocks at an even top are `(A_s, 0, …, 0)` and `(0, …, 0, −B_s)`, at an odd top `(0, …, 0, −A_s)` and
`(B_s, 0, …, 0)`: Annex I's blocks `(s, ±)` with `(d⁺_s, d⁻_s) = (A_s, B_s)` at even and `(B_s, A_s)` at odd `s`. -/
def lamH (TT : Finset (Fin n')) (A B : TT → ℤ) : Bool → Fin n' → Fin k → ℤ := fun v s i =>
  if v then (if i.val = 0 then ext TT A s else 0) else (if i.val + 1 = k then -ext TT B s else 0)

/-- **The harmonic indices** `J(A, B) = ∏_s [0, min(A_s, B_s)]`. -/
def jBox {TT : Finset (Fin n')} (A B : TT → ℤ) : Finset (TT → ℤ) :=
  Fintype.piFinset fun s => Icc 0 (min (A s) (B s))

/-- **The number of type-1 edges into a lattice**: `g = (q^k − 1)/(q − 1)`, `q = p^{n′}` (`nEdges_eq_gE`). -/
def gE (p n' k : ℕ) : ℕ := ((p ^ n') ^ k - 1) / (p ^ n' - 1)

variable (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] in
/-- **The harmonic splitting** (A-N7, an input): for `A, B ≥ 0` with `A_s + B_s + 1 ≤ a_max`, there are `Kf`-linear
maps `io_j : V(fl(A − j, B − j)) → H(A, B)` and `pr_j : H(A, B) → V(fl(A − j, B − j))`, `j ∈ J(A, B)`, with
`Σ_j io_j∘pr_j = id` on `H(A, B) = ∇_{Kf}`, integral up to `p^u` for every family of `O`-lattices `Λ_s` (one per
position, the blocks `(v, s)` of `H` and `((), s)` of the flat weight both at `Λ_s`):
`p^u·pr_j(∇_H(Λ)) ⊆ ∇_{fl}(Λ)` and `p^u·io_j(∇_{fl}(Λ)) ⊆ ∇_H(Λ)`. Annex I takes `a_max = 8a` and
`u = N·⌈(m + 2)λ_a⌉`, `λ_a = log_p(8a + m) + 1` (`h = Σx_iy_i`, `pr_j(f) = f_j` for `f = Σ_j h^j f_j`). -/
def HarmSplit (p : ℕ) (TT : Finset (Fin n')) (k u : ℕ) (amax : ℝ) : Prop :=
  ∀ A B : TT → ℤ, (∀ s, 0 ≤ A s) → (∀ s, 0 ≤ B s) → (∀ s, ((A s + B s + 1 : ℤ) : ℝ) ≤ amax) →
    ∃ (io : (TT → ℤ) → Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Bool × Fin n') k Kf)
      (pr : (TT → ℤ) → Pol (Bool × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf),
      (∀ x ∈ nabla Kf (fun b => natW (blockWt (lamH (k := k) TT A B) b)), ∑ j ∈ jBox A B, io j (pr j x) = x) ∧
      ∀ Λ : Fin n' → Submodule O (Fin k → Kf), (∀ s, ∃ C, IsBasisOf (Λ s) C) → ∀ j ∈ jBox A B,
        (∀ x ∈ nablaB (blockWt (lamH (k := k) TT A B)) (fun b => Λ b.2),
          (p : Kf) ^ u • pr j x ∈ nablaB (wt1 (flatWt (k := k) TT (A - j) (B - j))) (fun b => Λ b.2)) ∧
        (∀ v ∈ nablaB (wt1 (flatWt (k := k) TT (A - j) (B - j))) (fun b => Λ b.2),
          (p : Kf) ^ u • io j v ∈ nablaB (blockWt (lamH (k := k) TT A B)) (fun b => Λ b.2))

variable (Kf : Type) [Field Kf] in
/-- **The Weyl count at the flat weights** (the classical half of A-N10, an input): for `α, β ≥ 0`,
`dim V(fl(α, β)) = ∏_{s ∈ TT} Har_m(α_s, β_s)`, `m = k − 1` (the Weyl dimension formula for the repo's `∇`, whose
combinatorial side is `WeylCount.dimW_flatW`). -/
def FlatDim (TT : Finset (Fin n')) (k : ℕ) : Prop :=
  ∀ α β : TT → ℤ, (∀ s, 0 ≤ α s) → (∀ s, 0 ≤ β s) →
    dimV Kf (flatWt (k := k) TT α β) = ∏ s : TT, har (k - 1) (α s).toNat (β s).toNat

end Hyp

section SettingHyp

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {n' : ℕ}

variable (W) (k : ℕ) in
/-- **The input rank** (I1, the output of layer 2, LT): at every `(A, B)` in the enlarged box `W_A^{TT} × W_B^{TT}`
some type-1 edge carries a good system for `H(A, B)` at depth `t₀(A, B)`, conductor `c`, denominator `D₀`, of size at
least `(1 − κ_P − Σ_{V-tops x} κ_T(x, A, B))·dim H(A, B)/g`: `κ_P` is a numerical margin and `κ_T(x)` the bad share
of the segment of `x` (Annex I §3.3 N0 and §6 I1, at one edge by simplification S8). -/
def InputRank (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (TT : Finset (Fin n')) (WA WB : Finset ℤ)
    (t0 : (TT → ℤ) → (TT → ℤ) → ℕ) (c D : ℕ) (κP : ℝ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ) : Prop :=
  ∀ A ∈ box WA, ∀ B ∈ box WB, ∃ L'' L : Submodule W (Fin k → Qq), IsEdge (n' := n') p 1 L'' L ∧ ∃ n : ℕ,
    (1 - κP - ∑ x ∈ vTops TT, κT x A B) * dimH (k - 1) A B / gE p n' k ≤ n ∧
      GoodSysV p 1 ι σ ϖ (lamH (k := k) TT A B) (t0 A B) c D L'' L n

variable (W) (k : ℕ) in
/-- **The cloud step** (A-N15, module `FirstCloud`, an input): for a weight `λ` of the shape with top extremes
`(A_s + c, B_s + c)`, `0` off the tops, `b′/3 ≤ A_s, B_s`, `A_s + B_s + 4c + 1 ≤ 8a` and `12Nkc/b′ ≤ 1/9`: per-edge
ranks `(1 − κ₁)·d(fl(A, B))/g` and `(1 − κ₂)·d(fl(A + 2c, B + 2c))/g` at depth `t`, conductor `c₂`, denominator `D₁`
(`4D₁ < c₂`, `2Nc ≤ c₂`, `κ₁ ∈ [0, 1]`, `κ₂ ≥ 0`) give the per-edge rank `(1 − κ₁ − 2κ₂ − 12Nkc/b′)·d(λ)/g` at
conductor `c₂ − 2Nc` and denominator `2D₁ + D_c`. Annex I has `D_c = N·⌈m²λ_a⌉` (with L3's sandwich, S3,
`Σ jantzenExp ≤ N·k²·log_p(2c + k)`). -/
def CloudStep (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (TT : Finset (Fin n')) (c Dc : ℕ) (b' a : ℝ) :
    Prop :=
  ∀ (lam0 : Fin n' → Fin k → ℤ) (A B : TT → ℤ) (t c₂ D₁ : ℕ) (κ₁ κ₂ : ℝ),
    IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0 → (∀ s ∉ TT, lam0 s = 0) →
    (∀ s, b' / 3 ≤ (A s : ℝ) ∧ b' / 3 ≤ (B s : ℝ) ∧ ((A s + B s + 4 * c + 1 : ℤ) : ℝ) ≤ 8 * a) →
    12 * (TT.card : ℝ) * k * c / b' ≤ 1 / 9 → 4 * D₁ < c₂ → 2 * TT.card * c ≤ c₂ → 0 ≤ κ₁ → κ₁ ≤ 1 → 0 ≤ κ₂ →
    RankAll W p 1 ι σ ϖ (flatWt (k := k) TT A B) t c₂ D₁ ((1 - κ₁) * dimV Kf (flatWt (k := k) TT A B) / gE p n' k) →
    RankAll W p 1 ι σ ϖ (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) t c₂ D₁
      ((1 - κ₂) * dimV Kf (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) / gE p n' k) →
    RankAll W p 1 ι σ ϖ lam0 t (c₂ - 2 * TT.card * c) (2 * D₁ + Dc)
      ((1 - κ₁ - 2 * κ₂ - 12 * (TT.card : ℝ) * k * c / b') * dimV Kf lam0 / gE p n' k)

variable (W) (k : ℕ) in
/-- **The off-top step** (A-N18, an input): for a dominant weight with all entries off the tops in `[−c, c]` and
`2n′c ≤ c₃`, a per-edge rank `(1 − κ)·d(λ^top)/g` of the top part at depth `t`, conductor `c₃` gives the per-edge rank
`(1 − κ)·d(λ)/g` at depth `t + 2n′c`, conductor `c₃ − 2n′c`, same denominator (`V(λ) = V(λ^top) ⊗ V(λ^off)`, tensor
with `pairE`-dual bases of the off-top edge lattices, `𝓡_off(e) ⊆ ϖ^{−2n′c}∇_off(L″)`). -/
def OffTop (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (TT : Finset (Fin n')) (c : ℕ) : Prop :=
  ∀ (lam0 : Fin n' → Fin k → ℤ) (t c₃ D : ℕ) (κ : ℝ), (∀ s, Antitone (lam0 s)) →
    (∀ s ∉ TT, ∀ i, |lam0 s i| ≤ c) → 2 * n' * c ≤ c₃ →
    RankAll W p 1 ι σ ϖ (topPart TT lam0) t c₃ D ((1 - κ) * dimV Kf (topPart TT lam0) / gE p n' k) →
    RankAll W p 1 ι σ ϖ lam0 (t + 2 * n' * c) (c₃ - 2 * n' * c) D ((1 - κ) * dimV Kf lam0 / gE p n' k)

variable (W) (k : ℕ) in
/-- **The flat exceptional fraction** `κ_F(α, β)` (A-N5): the least `κ ∈ [0, 1]` such that every type-1 edge carries a
good system for `fl(α, β)` at depth `t_S(α, β)`, conductor `c`, denominator `D`, of size `(1 − κ)·d(fl(α, β))/g`. -/
def kappaF (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (TT : Finset (Fin n'))
    (tS : (TT → ℤ) → (TT → ℤ) → ℕ) (c D : ℕ) (α β : TT → ℤ) : ℝ :=
  sInf {κ : ℝ | 0 ≤ κ ∧ κ ≤ 1 ∧ RankAll W p 1 ι σ ϖ (flatWt (k := k) TT α β) (tS α β) c D
    ((1 - κ) * dimV Kf (flatWt (k := k) TT α β) / gE p n' k)}

end SettingHyp

/-! ## Good systems: closure, monotonicity and sub-systems -/

section Util

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} {β : Type} [Fintype β] [DecidableEq β]

/-- **`∇_Λ` is closed under multiples by elements of `O`.** -/
theorem smul_mem_nablaB {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)} {c : Kf} (hc : c ∈ Oint O Kf)
    {F : Pol β k Kf} (hF : F ∈ nablaB lam Λ) : c • F ∈ nablaB lam Λ := by
  obtain ⟨hF1, C, hC, hF2⟩ := hF
  exact ⟨Submodule.smul_mem _ _ hF1, C, hC, by
    rw [twist_smul]; exact Submodule.smul_mem _ (⟨c, hc⟩ : Oint O Kf) hF2⟩

/-- **`∇_Λ` is closed under sums.** -/
theorem add_mem_nablaB {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)} {F G : Pol β k Kf}
    (hF : F ∈ nablaB lam Λ) (hG : G ∈ nablaB lam Λ) : F + G ∈ nablaB lam Λ := by
  obtain ⟨hF1, C, hC, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := (mem_nablaB_iff hC).1 hG
  exact ⟨add_mem hF1 hG1, C, hC, by rw [twist_add]; exact add_mem hF2 hG2⟩

/-- **`0 ∈ ∇_Λ`** when the blocks have bases. -/
theorem zero_mem_nablaB {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)}
    (hΛ : ∀ b, ∃ C, IsBasisOf (Λ b) C) : (0 : Pol β k Kf) ∈ nablaB lam Λ := by
  choose C hC using hΛ
  exact ⟨zero_mem _, C, hC, by rw [twist_zero]; exact zero_mem _⟩

/-- **`∇_Λ` lies in `∇_{Kf}`.** -/
theorem mem_nabla_of_nablaB {lam : β → Fin k → ℤ} {Λ : β → Submodule O (Fin k → Kf)} {F : Pol β k Kf}
    (hF : F ∈ nablaB lam Λ) : F ∈ nabla Kf (fun b => natW (lam b)) := hF.1

/-- **A pairing of combinations**: `B(Σ_i a_i·X_i, Σ_l b_l·Y_l) = Σ_i Σ_l a_i·b_l·B(X_i, Y_l)` for `a, b` in `O`. -/
theorem bilin_sum_sum {Mo : Type*} [AddCommGroup Mo] [Module Kf Mo] [Module O Mo] [IsScalarTower O Kf Mo]
    (Bf : Mo →ₗ[Kf] Mo →ₗ[Kf] Kf) {n m : ℕ} (a : Fin n → O) (X : Fin n → Mo) (b : Fin m → O) (Y : Fin m → Mo) :
    Bf (∑ i, a i • X i) (∑ l, b l • Y l) =
      ∑ i, ∑ l, algebraMap O Kf (a i) * algebraMap O Kf (b l) * Bf (X i) (Y l) := by
  rw [LinearMap.map_sum₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← algebraMap_smul Kf (a i) (X i), ← algebraMap_smul Kf (b l) (Y l), map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul]
  ring

end Util

section GoodUtil

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [CharZero Kf] in
/-- **Bases at an edge**: the blocks of `L″`, of `L` and of the midpoint have basis matrices. -/
theorem bases_of_edge (hU : Unram p n' W Qq O Kf ι σ j ϖ) {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p r L'' L) :
    (∀ s, ∃ C, IsBasisOf (blk (O := O) ι σ s L'') C) ∧ (∀ s, ∃ C, IsBasisOf (blk (O := O) ι σ s L) C) ∧
      ∀ s, ∃ C, IsBasisOf (midBlk ι σ ϖ s L'' L) C := by
  obtain ⟨B, S, -, hB, hLB, hL''B⟩ := exists_basis_edge hU he
  exact ⟨fun s => ⟨_, isBasisOf_blk_edge hU s hB hL''B⟩, fun s => ⟨_, isBasisOf_blk hU s hB hLB⟩,
    fun s => ⟨_, isBasisOf_midBlk hU s hB hLB hL''B⟩⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **The edge lattice is closed under multiples by elements of `O`.** -/
theorem smul_mem_edgeLat {lam0 : Fin n' → Fin k → ℤ} {r : ℕ} {L'' L : Submodule W (Fin k → Qq)} {c : Kf}
    (hc : c ∈ Oint O Kf) {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L) :
    c • F ∈ edgeLat ι σ ϖ r lam0 L'' L := by
  show _ ∈ nabMid ι σ ϖ lam0 L'' L
  rw [smul_comm]
  exact smul_mem_nablaB hc hF

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **The edge lattice is closed under sums.** -/
theorem add_mem_edgeLat {lam0 : Fin n' → Fin k → ℤ} {r : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    {F G : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L) (hG : G ∈ edgeLat ι σ ϖ r lam0 L'' L) :
    F + G ∈ edgeLat ι σ ϖ r lam0 L'' L := by
  show _ ∈ nabMid ι σ ϖ lam0 L'' L
  rw [smul_add]
  exact add_mem_nablaB hF hG

omit [CharZero Kf] in
/-- **`0` lies in the edge lattice.** -/
theorem zero_mem_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) :
    (0 : Pol (Unit × Fin n') k Kf) ∈ edgeLat ι σ ϖ r lam0 L'' L := by
  show _ ∈ nabMid ι σ ϖ lam0 L'' L
  rw [smul_zero]
  exact zero_mem_nablaB fun b => (bases_of_edge hU he).2.2 b.2

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [CharZero Kf] in
/-- **Closure of a scaled set**: if `S` is closed under sums and `O`-multiples, so is `x·S`. -/
theorem smul_set_closed {M : Type*} [AddCommGroup M] [Module Kf M] {S : Set M} {x : Kf}
    (hadd : ∀ F ∈ S, ∀ G ∈ S, F + G ∈ S) (hsm : ∀ c ∈ Oint O Kf, ∀ F ∈ S, c • F ∈ S) :
    (∀ F ∈ x • S, ∀ G ∈ x • S, F + G ∈ x • S) ∧ ∀ c ∈ Oint O Kf, ∀ F ∈ x • S, c • F ∈ x • S := by
  refine ⟨fun F hF G hG => ?_, fun c hc F hF => ?_⟩
  · obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 hF
    obtain ⟨G₁, hG₁, rfl⟩ := Set.mem_smul_set.1 hG
    exact ⟨F₁ + G₁, hadd _ hF₁ _ hG₁, smul_add _ _ _⟩
  · obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 hF
    exact ⟨c • F₁, hsm c hc _ hF₁, smul_comm _ _ _⟩

omit [CharZero Kf] in
/-- **The source family is an `O`-module**: closed under `0`, sums and `O`-multiples (as `tgtFam_closed`). -/
theorem srcFam_closed (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) :
    (0 : Pol (Unit × Fin n') k Kf) ∈ SrcFam p r ι σ ϖ lam0 t c L'' L ∧
    (∀ F G, F ∈ SrcFam p r ι σ ϖ lam0 t c L'' L → G ∈ SrcFam p r ι σ ϖ lam0 t c L'' L →
      F + G ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) ∧
    ∀ (a : O) F, F ∈ SrcFam p r ι σ ϖ lam0 t c L'' L → a • F ∈ SrcFam p r ι σ ϖ lam0 t c L'' L := by
  have hnab := smul_set_closed (x := (algebraMap O Kf ϖ ^ t)⁻¹) (S := nab O ι σ lam0 L'')
    (fun F hF G hG => add_mem_nablaB hF hG) (fun c hc F hF => smul_mem_nablaB hc hF)
  have hedge : ∀ L', (∀ F ∈ edgeLat ι σ ϖ r lam0 L'' L', ∀ G ∈ edgeLat ι σ ϖ r lam0 L'' L',
      F + G ∈ edgeLat ι σ ϖ r lam0 L'' L') ∧
      ∀ c ∈ Oint O Kf, ∀ F ∈ edgeLat ι σ ϖ r lam0 L'' L', c • F ∈ edgeLat ι σ ϖ r lam0 L'' L' :=
    fun L' => ⟨fun F hF G hG => add_mem_edgeLat hF hG, fun c hc F hF => smul_mem_edgeLat hc hF⟩
  have hsmall := fun L' => smul_set_closed (x := algebraMap O Kf ϖ ^ c) (hedge L').1 (hedge L').2
  have hL'' : L''.IsLattice Qq := he.2.1
  refine ⟨⟨⟨⟨0, zero_mem_NablaT hU fun _ => hL'', smul_zero _⟩, Set.mem_iInter₂.2 fun L' he' =>
    zero_mem_edgeLat hU he'⟩, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun _ =>
      ⟨0, zero_mem_edgeLat hU he', smul_zero _⟩⟩, fun F G hF hG => ?_, fun a F hF => ?_⟩
  · refine ⟨⟨hnab.1 _ hF.1.1 _ hG.1.1, Set.mem_iInter₂.2 fun L' he' =>
      add_mem_edgeLat (Set.mem_iInter₂.1 hF.1.2 L' he') (Set.mem_iInter₂.1 hG.1.2 L' he')⟩,
      Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => (hsmall L').1 _
        (Set.mem_iInter.1 (Set.mem_iInter₂.1 hF.2 L' he') hne) _
        (Set.mem_iInter.1 (Set.mem_iInter₂.1 hG.2 L' he') hne)⟩
  · rw [← algebraMap_smul Kf a F]
    have ha : algebraMap O Kf a ∈ Oint O Kf := ⟨a, rfl⟩
    exact ⟨⟨hnab.2 _ ha _ hF.1.1, Set.mem_iInter₂.2 fun L' he' =>
      smul_mem_edgeLat ha (Set.mem_iInter₂.1 hF.1.2 L' he')⟩,
      Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => (hsmall L').2 _ ha _
        (Set.mem_iInter.1 (Set.mem_iInter₂.1 hF.2 L' he') hne)⟩

omit [CharZero Kf] in
/-- **Combinations of sources** with coefficients in `O` are sources. -/
theorem sum_smul_mem_srcFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p r L'' L) {n : ℕ} (a : Fin n → O)
    (x : Fin n → Pol (Unit × Fin n') k Kf) (hx : ∀ i, x i ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) :
    ∑ i, a i • x i ∈ SrcFam p r ι σ ϖ lam0 t c L'' L := by
  obtain ⟨h0, hadd, hsm⟩ := srcFam_closed hU (t := t) (c := c) (lam0 := lam0) he
  exact Finset.sum_induction _ (· ∈ SrcFam p r ι σ ϖ lam0 t c L'' L) (fun F G hF hG => hadd F G hF hG) h0
    fun i _ => hsm _ _ (hx i)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Combinations of targets** with coefficients in `O` are targets (`tgtFam_closed`). -/
theorem sum_smul_mem_tgtFam {lam0 : Fin n' → Fin k → ℤ} {r t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} {n : ℕ}
    (a : Fin n → O) (y : Fin n → Pol (Unit × Fin n') k Kf) (hy : ∀ i, y i ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) :
    ∑ i, a i • y i ∈ TgtFam p r ι σ ϖ lam0 t c L'' L := by
  obtain ⟨h0, hadd, hsm⟩ := tgtFam_closed (p := p) (ι := ι) (σ := σ) (ϖ := ϖ) (lam0 := lam0) (r := r) (t := t)
    (c := c) (L'' := L'') (L := L)
  exact Finset.sum_induction _ (· ∈ TgtFam p r ι σ ϖ lam0 t c L'' L) (fun F G hF hG => hadd F G hF hG) h0
    fun i _ => hsm _ _ (hy i)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDiscreteValuationRing O] in
/-- **The empty good system.** -/
theorem goodSys_zero {lam0 : Fin n' → Fin k → ℤ} {r t c D : ℕ} {L'' L : Submodule W (Fin k → Qq)} :
    GoodSys p r ι σ ϖ lam0 t c D L'' L 0 :=
  ⟨Fin.elim0, Fin.elim0, 1, 0, one_ne_zero, one_dvd _, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Sub-systems**: a good system of size `n` gives one of every size `n′ ≤ n` (the first `n′` sources, the targets
`Y_l = Σ_m M_{ml}·y_m`, `M′ = 1`). -/
theorem goodSys_le {lam0 : Fin n' → Fin k → ℤ} {r t c D n n₁ : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (h : GoodSys p r ι σ ϖ lam0 t c D L'' L n) (hn : n₁ ≤ n) : GoodSys p r ι σ ϖ lam0 t c D L'' L n₁ := by
  classical
  obtain ⟨x, y, z, M, hz, hzD, hx, hy, hG⟩ := h
  refine ⟨fun i => x (Fin.castLE hn i), fun l => ∑ m, M m (Fin.castLE hn l) • y m, z, 1, hz, hzD,
    fun i => hx _, fun l => sum_smul_mem_tgtFam _ _ hy, fun i l => ?_⟩
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [Matrix.one_apply_ne hm, map_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, map_one, mul_one, pairE_sum_smul]
  have := hG (Fin.castLE hn i) (Fin.castLE hn l)
  simp only [mul_comm (pairE p r lam0 _ _)] at this
  rw [this]
  simp [Fin.castLE_inj]

/-- **Good systems are monotone** in the depth (up), the conductor (down) and the denominator (up). -/
theorem goodSys_mono (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c D t' c' D' n : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} (h : GoodSys p r ι σ ϖ lam0 t c D L'' L n) (ht : t ≤ t') (hc : c' ≤ c)
    (hD : D ≤ D') : GoodSys p r ι σ ϖ lam0 t' c' D' L'' L n := by
  obtain ⟨x, y, z, M, hz, hzD, hx, hy, hG⟩ := h
  have hϖ : algebraMap O Kf ϖ ∈ Oint O Kf := ⟨ϖ, rfl⟩
  refine ⟨x, y, z, M, hz, hzD.trans (pow_dvd_pow _ hD), fun i => ?_, fun i => ?_, hG⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hx i
    refine ⟨⟨?_, h2⟩, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
    · obtain ⟨F₀, hF₀, hF⟩ := Set.mem_smul_set.1 h1
      refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ (t' - t) • F₀, smul_mem_nablaB (pow_mem hϖ _) hF₀, ?_⟩
      have hϖ0 : algebraMap O Kf ϖ ≠ 0 := varpiK_ne_zero hU
      rw [← hF, smul_smul]
      congr 1
      rw [← Nat.add_sub_cancel' ht, pow_add, mul_inv, mul_assoc, Nat.add_sub_cancel_left,
        inv_mul_cancel₀ (pow_ne_zero _ hϖ0), mul_one]
    · obtain ⟨F₁, hF₁, hF⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 h3 L' he') hne)
      refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ (c - c') • F₁, smul_mem_edgeLat (pow_mem hϖ _) hF₁, ?_⟩
      rw [← hF, smul_smul, ← pow_add, Nat.add_sub_cancel' hc]
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hy i
    refine ⟨⟨⟨h1.1, fun F hF => h1.2 F ?_⟩, h2⟩, Set.mem_iInter₂.2 fun L₁ he' => Set.mem_iInter.2 fun hne => ?_⟩
    · obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 hF
      refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ (t' - t) • F₀, smul_mem_nablaB (pow_mem hϖ _) hF₀, ?_⟩
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' ht]
    · obtain ⟨G₁, hG₁, hG⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 h3 L₁ he') hne)
      refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ (c - c') • G₁, ?_, ?_⟩
      · rw [← map_pow, algebraMap_smul]
        exact Submodule.smul_mem _ _ hG₁
      · rw [← hG, smul_smul, ← pow_add, Nat.add_sub_cancel' hc]

end GoodUtil

/-! ## Per-edge ranks and the flat exceptional fraction (A-N5) -/

/-- **Attaining an infimum on integers**: if every `κ ∈ S` has an `n ∈ ℕ` with `(1 − κ)·e ≤ n` and `P n` (`e ≥ 0`),
so does `inf S`: for `x = (1 − inf S)·e > 0` take `κ ∈ S` with `(1 − κ)·e > ⌈x⌉ − 1`; then `n ≥ ⌈x⌉ ≥ x`. -/
theorem exists_nat_of_sInf {P : ℕ → Prop} {S : Set ℝ} {e : ℝ} (he : 0 ≤ e) (hS : S.Nonempty)
    (h : ∀ κ ∈ S, ∃ n : ℕ, (1 - κ) * e ≤ n ∧ P n) : ∃ n : ℕ, (1 - sInf S) * e ≤ n ∧ P n := by
  by_cases hx : (1 - sInf S) * e ≤ 0
  · obtain ⟨κ, hκ⟩ := hS
    obtain ⟨n, -, hn⟩ := h κ hκ
    exact ⟨n, hx.trans (Nat.cast_nonneg n), hn⟩
  rw [not_le] at hx
  have he' : 0 < e := by
    rcases he.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at hx; exact absurd hx (lt_irrefl 0)
  set x := (1 - sInf S) * e
  set m := ⌈x⌉₊
  have hm1 : (m : ℝ) - 1 < x := by have := Nat.ceil_lt_add_one hx.le; linarith
  have hδ : 0 < (x - (m - 1)) / e := div_pos (by linarith) he'
  obtain ⟨κ, hκ, hκlt⟩ := exists_lt_of_csInf_lt hS (show sInf S < sInf S + (x - (m - 1)) / e by linarith)
  obtain ⟨n, hn, hP⟩ := h κ hκ
  refine ⟨n, ?_, hP⟩
  have h1 : κ * e < (sInf S + (x - (m - 1)) / e) * e := mul_lt_mul_of_pos_right hκlt he'
  rw [add_mul, div_mul_cancel₀ _ he'.ne'] at h1
  have h2 : (m : ℝ) - 1 < n := by
    have : (1 - κ) * e = e - κ * e := by ring
    have : x = e - sInf S * e := by simp only [x]; ring
    linarith
  have h3 : m ≤ n := by
    have : (m : ℝ) < n + 1 := by linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  calc x ≤ m := Nat.le_ceil x
    _ ≤ n := by exact_mod_cast h3

section Rank

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **Per-edge ranks are monotone** in the depth (up), the conductor (down), the denominator (up) and the size
(down). -/
theorem rankAll_mono (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r t c D t' c' D' : ℕ}
    {X X' : ℝ} (h : RankAll W p r ι σ ϖ lam0 t c D X) (ht : t ≤ t') (hc : c' ≤ c) (hD : D ≤ D') (hX : X' ≤ X) :
    RankAll W p r ι σ ϖ lam0 t' c' D' X' := fun L'' L he => by
  obtain ⟨n, hn, hg⟩ := h L'' L he
  exact ⟨n, hX.trans hn, goodSys_mono hU hg ht hc hD⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDiscreteValuationRing O] in
/-- **A per-edge rank of size `≤ 0`** holds (empty systems). -/
theorem rankAll_of_nonpos {lam0 : Fin n' → Fin k → ℤ} {r t c D : ℕ} {X : ℝ} (hX : X ≤ 0) :
    RankAll W p r ι σ ϖ lam0 t c D X := fun _ _ _ => ⟨0, by simpa using hX, goodSys_zero⟩

omit [CharZero Kf] in
/-- **The number of type-1 edges into a lattice** is `g = (q^k − 1)/(q − 1)` (`nEdges_one`). -/
theorem nEdges_eq_gE (hU : Unram p n' W Qq O Kf ι σ j ϖ) {L : Submodule W (Fin k → Qq)} (hL : L.IsLattice Qq) :
    nEdges (n' := n') p 1 L = gE p n' k := by
  have h := nEdges_one hU hL
  have hq := one_lt_q hU
  unfold gE
  rw [← h, Nat.mul_div_cancel _ (by omega)]

omit [CharZero Kf] in
/-- **There is at least one edge**: `g ≥ 1` for `k ≥ 1`. -/
theorem one_le_gE (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 1 ≤ k) : 1 ≤ gE p n' k := by
  have hq := one_lt_q hU
  unfold gE
  rw [Nat.one_le_div_iff (by omega)]
  have : p ^ n' ≤ (p ^ n') ^ k := Nat.le_self_pow (by omega) _
  omega

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDiscreteValuationRing O] in
/-- **The flat exceptional fraction is attained** (A-N5): `κ_F ∈ [0, 1]`, and every type-1 edge carries a good system
for `fl(α, β)` of size `(1 − κ_F)·d(fl(α, β))/g` (`exists_nat_of_sInf`). -/
theorem kappaF_spec {TT : Finset (Fin n')} {tS : (TT → ℤ) → (TT → ℤ) → ℕ}
    {c D : ℕ} (α β : TT → ℤ) :
    0 ≤ kappaF W k p ι σ ϖ TT tS c D α β ∧ kappaF W k p ι σ ϖ TT tS c D α β ≤ 1 ∧
      RankAll W p 1 ι σ ϖ (flatWt (k := k) TT α β) (tS α β) c D
        ((1 - kappaF W k p ι σ ϖ TT tS c D α β) * dimV Kf (flatWt (k := k) TT α β) / gE p n' k) := by
  set S := {κ : ℝ | 0 ≤ κ ∧ κ ≤ 1 ∧ RankAll W p 1 ι σ ϖ (flatWt (k := k) TT α β) (tS α β) c D
    ((1 - κ) * dimV Kf (flatWt (k := k) TT α β) / gE p n' k)}
  have h1 : (1 : ℝ) ∈ S := ⟨zero_le_one, le_rfl, rankAll_of_nonpos (by simp)⟩
  have hb : BddBelow S := ⟨0, fun κ h => h.1⟩
  have he : (0 : ℝ) ≤ dimV Kf (flatWt (k := k) TT α β) / gE p n' k := by positivity
  refine ⟨le_csInf ⟨1, h1⟩ fun κ h => h.1, csInf_le hb h1, fun L'' L hed => ?_⟩
  obtain ⟨n, hn, hP⟩ := exists_nat_of_sInf (P := GoodSys p 1 ι σ ϖ (flatWt (k := k) TT α β) (tS α β) c D L'' L)
    he ⟨1, h1⟩ fun κ hκ => by
      obtain ⟨n, hn, hg⟩ := hκ.2.2 L'' L hed
      exact ⟨n, by rwa [mul_div_assoc] at hn, hg⟩
  exact ⟨n, by rwa [mul_div_assoc], hP⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`κ_F` is below every qualifying `κ`.** -/
theorem kappaF_le {TT : Finset (Fin n')} {tS : (TT → ℤ) → (TT → ℤ) → ℕ} {c D : ℕ} {α β : TT → ℤ} {κ : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (h : RankAll W p 1 ι σ ϖ (flatWt (k := k) TT α β) (tS α β) c D
      ((1 - κ) * dimV Kf (flatWt (k := k) TT α β) / gE p n' k)) :
    kappaF W k p ι σ ϖ TT tS c D α β ≤ κ :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨h0, h1, h⟩

end Rank

/-! ## The exponents `A₁` of the flat weights and of the tensor -/

section TopA

variable {n' k : ℕ}

/-- **`A₁` at one orbit**: `topSum 1 lam0 v = Σ_s lamAt(lam0 v)_{s,0}`. -/
theorem topSum_one {V : Type} (hk : 1 ≤ k) (lam0 : V → Fin n' → Fin k → ℤ) (v : V) :
    topSum 1 lam0 v = ∑ s : Fin n', lamAt (lam0 v) s ⟨0, hk⟩ := by
  unfold topSum
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show (Finset.univ.filter fun i : Fin k => i.val < 1) = {⟨0, hk⟩} by
    ext i; simp [Fin.ext_iff], Finset.sum_singleton]

/-- **`lamAt` at the first coordinate**: `λ_{s,0}` at even `s`, `−λ_{s,k−1}` at odd `s`. -/
theorem lamAt_zero (hk : 1 ≤ k) (lam0 : Fin n' → Fin k → ℤ) (s : Fin n') :
    lamAt lam0 s ⟨0, hk⟩ = if Even s.val then lam0 s ⟨0, hk⟩ else -lam0 s ⟨k - 1, by omega⟩ := by
  unfold lamAt
  split_ifs
  · rfl
  · congr 2

/-- **The sum of `ext`** over the positions is the sum over the tops. -/
theorem sum_ext (TT : Finset (Fin n')) (α : TT → ℤ) : ∑ s : Fin n', ext TT α s = ∑ s : TT, α s := by
  rw [← Finset.sum_subset (Finset.subset_univ TT) fun s _ hs => ext_of_not_mem α hs,
    ← Finset.sum_coe_sort TT]
  exact Finset.sum_congr rfl fun s _ => ext_coe α s

/-- **`A₁` of a flat weight**: `Σ_{even s} α_s + Σ_{odd s} β_s` (`k ≥ 2`). -/
theorem topA_flatWt (hk : 2 ≤ k) (TT : Finset (Fin n')) (α β : TT → ℤ) :
    topA 1 (flatWt (k := k) TT α β) = ∑ s : Fin n', (if Even s.val then ext TT α s else ext TT β s) := by
  rw [topA, topSum_one (by omega)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lamAt_zero (by omega)]
  simp only [flatWt]
  split_ifs <;> first | rfl | omega

/-- **`A₁` of the tensor** `H(A, B)`: `Σ_{even s} A_s + Σ_{odd s} B_s`, the same as for `fl(A, B)` (`k ≥ 2`). -/
theorem topAV_lamH (hk : 2 ≤ k) (TT : Finset (Fin n')) (A B : TT → ℤ) :
    topAV 1 (lamH (k := k) TT A B) = ∑ s : Fin n', (if Even s.val then ext TT A s else ext TT B s) := by
  rw [topAV, Fintype.sum_bool, topSum_one (by omega), topSum_one (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lamAt_zero (by omega), lamAt_zero (by omega)]
  simp only [lamH]
  split_ifs <;> first | rfl | omega | contradiction

/-- **The exponent gap of a harmonic piece**: `A₁(H(A, B)) = A₁(fl(A − j, B − j)) + Σ_s j_s`. -/
theorem topAV_lamH_eq (hk : 2 ≤ k) (TT : Finset (Fin n')) (A B jh : TT → ℤ) :
    topAV 1 (lamH (k := k) TT A B) = topA 1 (flatWt (k := k) TT (A - jh) (B - jh)) + ∑ s : TT, jh s := by
  rw [topAV_lamH hk, topA_flatWt hk, ← sum_ext, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ext_sub, ext_sub]
  split_ifs <;> ring

end TopA

/-! ## Splitting the good systems of the tensor over the harmonic pieces (A-N8) -/

section Split

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The pairing of a tuple, unfolded**: `pairEV(F, G) = ⟨p^{A_r}F, G⟩`. -/
theorem pairEV_apply {V : Type} [Fintype V] [DecidableEq V] (p r : ℕ) (lamV : V → Fin n' → Fin k → ℤ)
    (F G : Pol (V × Fin n') k Kf) : pairEV p r lamV F G = nf (blockWt lamV) ((p : Kf) ^ topAV r lamV • F) G := by
  simp only [pairEV, LinearMap.smul_apply, map_smul]

omit [CharZero Kf] in
/-- **The edge lattice lies in `∇_{Kf}`.** -/
theorem mem_nabla_of_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : Fin n' → Fin k → ℤ} {r : ℕ}
    {L'' L : Submodule W (Fin k → Qq)} {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ edgeLat ι σ ϖ r lam0 L'' L) :
    F ∈ nabla Kf (nu1 lam0) := by
  have h := Submodule.smul_mem _ (algebraMap O Kf ϖ ^ topA r lam0)⁻¹ (mem_nabla_of_nablaB hF)
  rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ (varpiK_ne_zero hU)), one_smul] at h

omit [CharZero Kf] in
/-- **The source map** `x ↦ p^u ϖ^d·pr(x)` takes the edge lattices of the tensor into those of a flat piece, when
`A₁(H) = A₁(fl) + d` and `p^u·pr` is integral on the midpoint lattices. -/
theorem prMap_mem_edgeLat (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lamV : Bool → Fin n' → Fin k → ℤ}
    {lamF : Fin n' → Fin k → ℤ} (pr : Pol (Bool × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf) {u d : ℕ}
    (hA : topAV 1 lamV = topA 1 lamF + d)
    (hint : ∀ Λ : Fin n' → Submodule O (Fin k → Kf), (∀ s, ∃ C, IsBasisOf (Λ s) C) →
      ∀ x ∈ nablaB (blockWt lamV) (fun b => Λ b.2), (p : Kf) ^ u • pr x ∈ nablaB (wt1 lamF) (fun b => Λ b.2))
    {L'' L' : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L') {x : Pol (Bool × Fin n') k Kf}
    (hx : x ∈ edgeLatV ι σ ϖ 1 lamV L'' L') :
    ((p : Kf) ^ u * algebraMap O Kf ϖ ^ d) • pr x ∈ edgeLat ι σ ϖ 1 lamF L'' L' := by
  have h := hint (fun s => midBlk ι σ ϖ s L'' L') (fun s => (bases_of_edge hU he).2.2 s.val) _ hx
  show _ ∈ nabMid ι σ ϖ lamF L'' L'
  have hϖ := varpiK_ne_zero hU
  have e : algebraMap O Kf ϖ ^ topA 1 lamF • ((p : Kf) ^ u * algebraMap O Kf ϖ ^ d) • pr x =
      (p : Kf) ^ u • pr (algebraMap O Kf ϖ ^ topAV 1 lamV • x) := by
    rw [map_smul, smul_smul, smul_smul, hA, zpow_add₀ hϖ, zpow_natCast]
    congr 1
    ring
  rw [e]
  exact h

/-- **The source map takes sources to sources** (A-N8, source side): `x ↦ p^u ϖ^d·pr(x)` maps the source family of
the tensor at `L″ ⊂ L` into that of the flat piece (`p^u·pr` integral on the lattices of `L″` and of the midpoints,
`d ≥ 0` only helps the depth). -/
theorem prMap_mem_srcFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lamV : Bool → Fin n' → Fin k → ℤ}
    {lamF : Fin n' → Fin k → ℤ} (pr : Pol (Bool × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf) {u d : ℕ}
    (hA : topAV 1 lamV = topA 1 lamF + d)
    (hint : ∀ Λ : Fin n' → Submodule O (Fin k → Kf), (∀ s, ∃ C, IsBasisOf (Λ s) C) →
      ∀ x ∈ nablaB (blockWt lamV) (fun b => Λ b.2), (p : Kf) ^ u • pr x ∈ nablaB (wt1 lamF) (fun b => Λ b.2))
    {t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) {x : Pol (Bool × Fin n') k Kf}
    (hx : x ∈ SrcFamV p 1 ι σ ϖ lamV t c L'' L) :
    ((p : Kf) ^ u * algebraMap O Kf ϖ ^ d) • pr x ∈ SrcFam p 1 ι σ ϖ lamF t c L'' L := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  have hϖ1 : algebraMap O Kf ϖ ∈ Oint O Kf := ⟨ϖ, rfl⟩
  have hϖO : algebraMap O Kf ϖ ^ d ∈ Oint O Kf := pow_mem hϖ1 _
  refine ⟨⟨?_, Set.mem_iInter₂.2 fun L' he' => prMap_mem_edgeLat hU pr hA hint he'
    (Set.mem_iInter₂.1 h2 L' he')⟩, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
  · obtain ⟨x₀, hx₀, rfl⟩ := Set.mem_smul_set.1 h1
    have h := hint (fun s => blk ι σ s L'') (fun s => (bases_of_edge hU he).1 s.val) _ hx₀
    refine Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ d • ((p : Kf) ^ u • pr x₀), smul_mem_nablaB hϖO h, ?_⟩
    simp only [map_smul, smul_smul]
    congr 1
    ring
  · obtain ⟨x₁, hx₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 h3 L' he') hne)
    refine Set.mem_smul_set.2 ⟨((p : Kf) ^ u * algebraMap O Kf ϖ ^ d) • pr x₁,
      prMap_mem_edgeLat hU pr hA hint he' hx₁, ?_⟩
    simp only [map_smul, smul_smul]
    congr 1
    ring

/-- **The adjoint target map** `T(y) = Σ_i pairE_H(s′·io(x_i), y)·y_i` for a `pairE`-dual pair `(x_i, y_i)` of the
flat piece: `pairE(w, T(y)) = pairE_H(s′·io(w), y)` on `∇_{Kf}` (`pairE_adjMap`). -/
def adjMap (p : ℕ) {V : Type} [Fintype V] [DecidableEq V] (lamV : V → Fin n' → Fin k → ℤ)
    (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf) (s' : Kf) {ιx : Type} [Fintype ιx]
    (xb yb : ιx → Pol (Unit × Fin n') k Kf) (y : Pol (V × Fin n') k Kf) : Pol (Unit × Fin n') k Kf :=
  ∑ i, pairEV p 1 lamV (s' • io (xb i)) y • yb i

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`adjMap` is the adjoint**: `pairE(w, T(y)) = pairE_H(s′·io(w), y)` for `w ∈ ∇_{Kf}`. -/
theorem pairE_adjMap {V : Type} [Fintype V] [DecidableEq V] {lamV : V → Fin n' → Fin k → ℤ}
    {lamF : Fin n' → Fin k → ℤ} (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf) (s' : Kf)
    {ιx : Type} [Fintype ιx] [DecidableEq ιx] (xb yb : ιx → Pol (Unit × Fin n') k Kf)
    (hdual : ∀ i l, pairE p 1 lamF (xb i) (yb l) = if i = l then 1 else 0)
    (hspan : Submodule.span Kf (Set.range xb) = nabla Kf (nu1 lamF)) {w : Pol (Unit × Fin n') k Kf}
    (hw : w ∈ nabla Kf (nu1 lamF)) (y : Pol (V × Fin n') k Kf) :
    pairE p 1 lamF w (adjMap p lamV io s' xb yb y) = pairEV p 1 lamV (s' • io w) y := by
  rw [← hspan] at hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Kf).1 hw
  simp only [adjMap, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hdual, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`adjMap` is homogeneous.** -/
theorem adjMap_smul {V : Type} [Fintype V] [DecidableEq V] (lamV : V → Fin n' → Fin k → ℤ)
    (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf) (s' : Kf) {ιx : Type} [Fintype ιx]
    (xb yb : ιx → Pol (Unit × Fin n') k Kf) (a : Kf) (y : Pol (V × Fin n') k Kf) :
    adjMap p lamV io s' xb yb (a • y) = a • adjMap p lamV io s' xb yb y := by
  simp only [adjMap, map_smul, smul_eq_mul, smul_sum, smul_smul]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`adjMap` lands in `∇_{Kf}`.** -/
theorem adjMap_mem_nabla {V : Type} [Fintype V] [DecidableEq V] (lamV : V → Fin n' → Fin k → ℤ)
    {lamF : Fin n' → Fin k → ℤ} (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (V × Fin n') k Kf) (s' : Kf)
    {ιx : Type} [Fintype ιx] (xb yb : ιx → Pol (Unit × Fin n') k Kf)
    (hspan : Submodule.span Kf (Set.range yb) = nabla Kf (nu1 lamF)) (y : Pol (V × Fin n') k Kf) :
    adjMap p lamV io s' xb yb y ∈ nabla Kf (nu1 lamF) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)

/-- **The target map takes targets to targets** (A-N8, target side): with `s′ = p^u ϖ^{−d}`, the adjoint
`T(y) = Σ_i pairE_H(s′·io(x_i), y)·y_i` maps the target family of the tensor at `L″ ⊂ L` into that of the flat piece:
`pairE(w, T(y)) = pairE_H(s′·io(w), y)`, and `s′·io` maps the edge lattices of the flat piece into those of the
tensor and `ϖ^t∇(L)` into `ϖ^{t−d}`-multiples, which the factor `p^{A_H − A_fl} = ϖ^{2d}` absorbs. -/
theorem adjMap_mem_tgtFam (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lamV : Bool → Fin n' → Fin k → ℤ}
    {lamF : Fin n' → Fin k → ℤ} (io : Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Bool × Fin n') k Kf) {u d : ℕ}
    (hA : topAV 1 lamV = topA 1 lamF + d)
    (hint : ∀ Λ : Fin n' → Submodule O (Fin k → Kf), (∀ s, ∃ C, IsBasisOf (Λ s) C) →
      ∀ v ∈ nablaB (wt1 lamF) (fun b => Λ b.2), (p : Kf) ^ u • io v ∈ nablaB (blockWt lamV) (fun b => Λ b.2))
    {ιx : Type} [Fintype ιx] [DecidableEq ιx] (xb yb : ιx → Pol (Unit × Fin n') k Kf)
    (hdual : ∀ i l, pairE p 1 lamF (xb i) (yb l) = if i = l then 1 else 0)
    (hspx : Submodule.span Kf (Set.range xb) = nabla Kf (nu1 lamF))
    (hspy : Submodule.span Kf (Set.range yb) = nabla Kf (nu1 lamF))
    {t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L'' L) {y : Pol (Bool × Fin n') k Kf}
    (hy : y ∈ TgtFamV p 1 ι σ ϖ lamV t c L'' L) :
    adjMap p lamV io ((p : Kf) ^ u * (algebraMap O Kf ϖ ^ d)⁻¹) xb yb y ∈ TgtFam p 1 ι σ ϖ lamF t c L'' L := by
  have hϖ := varpiK_ne_zero hU
  have hpK : (p : Kf) ≠ 0 := hU.castK_ne_zero
  have hϖ1 : algebraMap O Kf ϖ ∈ Oint O Kf := ⟨ϖ, rfl⟩
  -- the edge-dual part, for any target of the tensor in `𝓡′_H(L₁ ⊂ L)`
  have hT2 : ∀ L₁, IsEdge (n' := n') p 1 L₁ L → ∀ y', y' ∈ edgeDualV p 1 ι σ ϖ lamV L₁ L →
      adjMap p lamV io ((p : Kf) ^ u * (algebraMap O Kf ϖ ^ d)⁻¹) xb yb y' ∈ edgeDual p 1 ι σ ϖ lamF L₁ L := by
    intro L₁ he₁ y' hy'
    refine ⟨adjMap_mem_nabla lamV io _ xb yb hspy y', fun F hF => ?_⟩
    rw [pairE_adjMap io _ xb yb hdual hspx (mem_nabla_of_edgeLat hU hF)]
    refine hy'.2 _ ?_
    show _ ∈ nabMidV ι σ ϖ lamV L₁ L
    have h := hint (fun s => midBlk ι σ ϖ s L₁ L) (fun s => (bases_of_edge hU he₁).2.2 s.val) _ hF
    have e : algebraMap O Kf ϖ ^ topAV 1 lamV • ((p : Kf) ^ u * (algebraMap O Kf ϖ ^ d)⁻¹) • io F =
        (p : Kf) ^ u • io (algebraMap O Kf ϖ ^ topA 1 lamF • F) := by
      rw [map_smul, smul_smul, smul_smul, hA, zpow_add₀ hϖ, zpow_natCast]
      congr 1
      field_simp
    rw [e]
    exact h
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  refine ⟨⟨⟨adjMap_mem_nabla lamV io _ xb yb hspy y, fun F hF => ?_⟩,
    Submodule.mem_iInf _ |>.2 fun L₁ => Submodule.mem_iInf _ |>.2 fun he₁ =>
      hT2 L₁ he₁ y ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 L₁) he₁)⟩,
    Set.mem_iInter₂.2 fun L₁ he₁ => Set.mem_iInter.2 fun hne => ?_⟩
  · obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 hF
    have hF₀n : F₀ ∈ nabla Kf (nu1 lamF) := mem_nabla_of_nablaB hF₀
    have hw : ((p : Kf) ^ topA 1 lamF)⁻¹ • (algebraMap O Kf ϖ ^ t • F₀) ∈ nabla Kf (nu1 lamF) :=
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hF₀n)
    have e1 : nf (wt1 lamF) (algebraMap O Kf ϖ ^ t • F₀) (adjMap p lamV io ((p : Kf) ^ u *
        (algebraMap O Kf ϖ ^ d)⁻¹) xb yb y) = pairE p 1 lamF (((p : Kf) ^ topA 1 lamF)⁻¹ •
          (algebraMap O Kf ϖ ^ t • F₀)) (adjMap p lamV io ((p : Kf) ^ u * (algebraMap O Kf ϖ ^ d)⁻¹) xb yb y) := by
      rw [pairE_apply, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hpK), one_smul]
    rw [e1, pairE_adjMap io _ xb yb hdual hspx hw, pairEV_apply]
    have h := hint (fun s => blk ι σ s L) (fun s => (bases_of_edge hU he).2.1 s.val) _ hF₀
    refine h1.2 _ (Set.mem_smul_set.2 ⟨algebraMap O Kf ϖ ^ d • ((p : Kf) ^ u • io F₀),
      smul_mem_nablaB (pow_mem hϖ1 _) h, ?_⟩)
    simp only [map_smul, smul_smul]
    congr 1
    rw [hA, zpow_add₀ hpK, zpow_natCast, castK_eq_sq hU]
    field_simp
    ring
  · obtain ⟨y₁, hy₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 h3 L₁ he₁) hne)
    exact Set.mem_smul_set.2 ⟨_, hT2 L₁ he₁ y₁ hy₁, (adjMap_smul lamV io _ xb yb _ y₁).symm⟩

/-- **Splitting the good systems of the tensor** (A-N8): a good system of size `n` for `H(A, B)` at an edge gives
good systems of sizes `ν_j`, `Σ_{j ∈ J(A, B)} ν_j ≥ n`, for the flat pieces `fl(A − j, B − j)` at the same edge, depth
and conductor, with denominator `D + 2u`. The sources go by `p^u ϖ^{d_j}·pr_j` (`d_j = Σ_s j_s`), the targets by the
adjoint of `p^u ϖ^{−d_j}·io_j`; the Gram matrices `A_j` then add up to `p^{2u}z·1` (`Σ_j io_j∘pr_j = id`), and Smith
splitting (`smith_split`) cuts each `A_j` to `P_j·A_j·Q_j = p^{2u}z·1`. -/
theorem goodSys_split (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {TT : Finset (Fin n')} {u : ℕ} {amax : ℝ}
    (hHS : HarmSplit O Kf p TT k u amax) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    (hAB : ∀ s, ((A s + B s + 1 : ℤ) : ℝ) ≤ amax) {t c D n : ℕ} {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) (h : GoodSysV p 1 ι σ ϖ (lamH (k := k) TT A B) t c D L'' L n) :
    ∃ ν : (TT → ℤ) → ℕ, n ≤ ∑ jh ∈ jBox A B, ν jh ∧
      ∀ jh ∈ jBox A B, GoodSys p 1 ι σ ϖ (flatWt (k := k) TT (A - jh) (B - jh)) t c (D + 2 * u) L'' L (ν jh) := by
  classical
  obtain ⟨io, pr, hsum, hint⟩ := hHS A B hA hB hAB
  obtain ⟨xs, ys, z, M, hz, hzD, hxs, hys, hG⟩ := h
  have hϖ := varpiK_ne_zero hU
  have hpK : (p : Kf) ≠ 0 := hU.castK_ne_zero
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  have hpO : (p : O) ≠ 0 := fun h0 => hpK (by rw [← map_natCast (algebraMap O Kf), h0, map_zero])
  let J := {jh // jh ∈ jBox A B}
  have hjh : ∀ jh : J, ∀ s, 0 ≤ jh.1 s ∧ jh.1 s ≤ A s ∧ jh.1 s ≤ B s := fun jh s => by
    have := Fintype.mem_piFinset.1 jh.2 s
    rw [mem_Icc, le_min_iff] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hanti : ∀ jh : J, ∀ s, Antitone (flatWt (k := k) TT (A - jh.1) (B - jh.1) s) := fun jh =>
    antitone_flatWt hk (fun s => by simp only [Pi.sub_apply]; linarith [hjh jh s])
      (fun s => by simp only [Pi.sub_apply]; linarith [hjh jh s])
  let d : J → ℕ := fun jh => (∑ s, jh.1 s).toNat
  have hd : ∀ jh : J, topAV 1 (lamH (k := k) TT A B) = topA 1 (flatWt (k := k) TT (A - jh.1) (B - jh.1)) + d jh :=
    fun jh => by
      rw [topAV_lamH_eq hk TT A B jh.1, Int.toNat_of_nonneg (Finset.sum_nonneg fun s _ => (hjh jh s).1)]
  choose xb yb _ _ hdual hspx hspy using fun jh : J => edgeLat_dualPair hU (hanti jh) he
  let Pm : J → Pol (Bool × Fin n') k Kf → Pol (Unit × Fin n') k Kf := fun jh x =>
    ((p : Kf) ^ u * algebraMap O Kf ϖ ^ d jh) • pr jh.1 x
  let Tm : J → Pol (Bool × Fin n') k Kf → Pol (Unit × Fin n') k Kf := fun jh y =>
    adjMap p (lamH (k := k) TT A B) (io jh.1) ((p : Kf) ^ u * (algebraMap O Kf ϖ ^ d jh)⁻¹) (xb jh) (yb jh) y
  have hPm : ∀ jh i, Pm jh (xs i) ∈ SrcFam p 1 ι σ ϖ (flatWt (k := k) TT (A - jh.1) (B - jh.1)) t c L'' L :=
    fun jh i => prMap_mem_srcFam hU (pr jh.1) (hd jh) (fun Λ hΛ x hx => (hint Λ hΛ jh.1 jh.2).1 x hx) he (hxs i)
  have hTm : ∀ jh m, Tm jh (ys m) ∈ TgtFam p 1 ι σ ϖ (flatWt (k := k) TT (A - jh.1) (B - jh.1)) t c L'' L :=
    fun jh m => adjMap_mem_tgtFam hU (io jh.1) (hd jh) (fun Λ hΛ v hv => (hint Λ hΛ jh.1 jh.2).2 v hv)
      (xb jh) (yb jh) (hdual jh) (hspx jh) (hspy jh) he (hys m)
  -- the Gram entries are integral
  have hO : ∀ jh i m, ∃ g : O, pairE p 1 (flatWt (k := k) TT (A - jh.1) (B - jh.1)) (Pm jh (xs i)) (Tm jh (ys m)) =
      algebraMap O Kf g := fun jh i m => by
    obtain ⟨g, hg⟩ := pairE_mem_of_src_tgt he (hPm jh i).1 (hTm jh m).1
    exact ⟨g, hg.symm⟩
  choose g hg using hO
  -- the split of the pairing: `Σ_j pairE(P_j x, T_j y) = p^{2u}·pairE_H(x, y)`
  have hsplit : ∀ i m, ∑ jh : J, pairE p 1 (flatWt (k := k) TT (A - jh.1) (B - jh.1)) (Pm jh (xs i)) (Tm jh (ys m)) =
      (p : Kf) ^ (2 * u) * pairEV p 1 (lamH (k := k) TT A B) (xs i) (ys m) := by
    intro i m
    have hxn : xs i ∈ nabla Kf (fun b => natW (blockWt (lamH (k := k) TT A B) b)) := by
      obtain ⟨x₀, hx₀, hx⟩ := Set.mem_smul_set.1 (hxs i).1.1
      rw [← hx]
      exact Submodule.smul_mem _ _ hx₀.1
    have e : ∀ jh : J, pairE p 1 (flatWt (k := k) TT (A - jh.1) (B - jh.1)) (Pm jh (xs i)) (Tm jh (ys m)) =
        pairEV p 1 (lamH (k := k) TT A B) ((p : Kf) ^ (2 * u) • io jh.1 (pr jh.1 (xs i))) (ys m) := fun jh => by
      have hPn : Pm jh (xs i) ∈ nabla Kf (nu1 (flatWt (k := k) TT (A - jh.1) (B - jh.1))) := by
        obtain ⟨x₀, hx₀, hx⟩ := Set.mem_smul_set.1 (hPm jh i).1.1
        rw [← hx]
        exact Submodule.smul_mem _ _ hx₀.1
      rw [pairE_adjMap (io jh.1) _ (xb jh) (yb jh) (hdual jh) (hspx jh) hPn]
      simp only [Pm, map_smul, smul_smul]
      congr 2
      field_simp
      ring
    rw [Finset.sum_congr rfl fun jh _ => e jh, ← LinearMap.map_sum₂, ← Finset.smul_sum,
      Finset.sum_coe_sort (jBox A B) (fun jh => io jh (pr jh (xs i))), hsum _ hxn, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
  -- the Gram matrices
  let Gm : J → Matrix (Fin n) (Fin n) O := fun jh => Matrix.of fun i m => g jh i m
  let Am : J → Matrix (Fin n) (Fin n) O := fun jh => Gm jh * M
  have hAm : ∑ jh, Am jh = ((p : O) ^ (2 * u) * z) • (1 : Matrix (Fin n) (Fin n) O) := by
    ext i l
    apply hinj
    rw [Matrix.sum_apply, map_sum]
    simp only [Am, Gm, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← hg, ← Finset.sum_mul, hsplit, mul_assoc, ← Finset.mul_sum, hG, map_pow, map_natCast]
    split_ifs <;> simp
  obtain ⟨ν, hν, hPQ⟩ := smith_split Am _ (mul_ne_zero (pow_ne_zero _ hpO) hz) hAm
  refine ⟨fun jh => if h : jh ∈ jBox A B then ν ⟨jh, h⟩ else 0, ?_, fun jh hjB => ?_⟩
  · refine hν.trans (le_of_eq ?_)
    rw [← Finset.sum_coe_sort (jBox A B)]
    exact Finset.sum_congr rfl fun jh _ => by simp only [jh.2, ↓reduceDIte, Subtype.coe_eta]
  · obtain ⟨jj, rfl⟩ : ∃ jj : J, jj.1 = jh := ⟨⟨jh, hjB⟩, rfl⟩
    simp only [jj.2, ↓reduceDIte, Subtype.coe_eta]
    obtain ⟨P', Q', hPQ'⟩ := hPQ jj
    refine ⟨fun a => ∑ i, P' a i • Pm jj (xs i), fun b => ∑ m, (M * Q') m b • Tm jj (ys m),
      (p : O) ^ (2 * u) * z, 1, mul_ne_zero (pow_ne_zero _ hpO) hz, ?_,
      fun a => sum_smul_mem_srcFam hU he _ _ fun i => hPm jj i,
      fun b => sum_smul_mem_tgtFam _ _ fun m => hTm jj m, fun a b => ?_⟩
    · rw [pow_add, mul_comm ((p : O) ^ D)]
      exact mul_dvd_mul_left _ hzD
    · beta_reduce
      rw [Finset.sum_eq_single b (fun m _ hm => by rw [Matrix.one_apply_ne hm, map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ b) h), Matrix.one_apply_eq, map_one, mul_one]
      refine (bilin_sum_sum (Mo := Pol (Unit × Fin n') k Kf)
        (pairE p 1 (flatWt (k := k) TT (A - jj.1) (B - jj.1)))
        (P' a) (fun i => Pm jj (xs i)) (fun m => (M * Q') m b) (fun m => Tm jj (ys m))).trans ?_
      have e : (P' * Am jj * Q') a b = ∑ i, ∑ m, P' a i * (M * Q') m b * g jj i m := by
        rw [show P' * Am jj * Q' = P' * (Gm jj * (M * Q')) by simp only [Am, Matrix.mul_assoc]]
        simp only [Matrix.mul_apply, Gm, Matrix.of_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring
      have e2 : (if a = b then algebraMap O Kf ((p : O) ^ (2 * u) * z) else 0) =
          algebraMap O Kf ((P' * Am jj * Q') a b) := by
        rw [hPQ', Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        split_ifs <;> simp
      rw [e2, e]
      simp only [hg, map_sum, map_mul]

end Split

/-! ## The key inequality (A-N11) -/

section Key

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **The `Har` sum over the harmonic indices** (A-N10 over `ℤ`): `Σ_{j ∈ J(A, B)} ∏_s Har_m(A_s − j_s, B_s − j_s) =
dim H(A, B)` for `A, B ≥ 0` (`WeylCount.sum_prod_har`, reindexed by `j ↦ j.toNat`). -/
theorem sum_jBox_har {TT : Finset (Fin n')} {m : ℕ} (hm : 1 ≤ m) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s)
    (hB : ∀ s, 0 ≤ B s) :
    ∑ jh ∈ jBox A B, ∏ s, har m (A s - jh s).toNat (B s - jh s).toNat = dimH m A B := by
  rw [FirstMeans.dimH, ← sum_prod_har hm (fun s => (A s).toNat) (fun s => (B s).toNat)]
  refine Finset.sum_nbij' (fun jh s => (jh s).toNat) (fun j s => (j s : ℤ)) (fun jh hjh => ?_) (fun j hj => ?_)
    (fun jh hjh => ?_) (fun j _ => by ext s; simp) (fun jh hjh => ?_)
  · rw [jBox, Fintype.mem_piFinset] at hjh
    rw [Fintype.mem_piFinset]
    intro s
    have := hjh s
    rw [mem_Icc, le_min_iff] at this
    rw [mem_range]
    omega
  · rw [Fintype.mem_piFinset] at hj
    rw [jBox, Fintype.mem_piFinset]
    intro s
    have := hj s
    rw [mem_range] at this
    rw [mem_Icc, le_min_iff]
    have := hA s
    have := hB s
    omega
  · rw [jBox, Fintype.mem_piFinset] at hjh
    ext s
    have := hjh s
    rw [mem_Icc] at this
    simp [this.1]
  · rw [jBox, Fintype.mem_piFinset] at hjh
    refine Finset.prod_congr rfl fun s _ => ?_
    have := hjh s
    rw [mem_Icc, le_min_iff] at this
    beta_reduce
    congr 1 <;> omega

/-- **The key inequality** (A-N11): at `(A, B)` in the enlarged box, with all `A_s, B_s ≥ J`,
`Σ_{j ∈ [0, J]^{TT}} κ_F(A − j, B − j)·∏_s Har_m(A_s − j_s, B_s − j_s) ≤ κ_X(A, B)·dim H(A, B)`,
`κ_X = κ_P + Σ_x κ_T(x)`, when the depth of `κ_F` dominates the input depth after the shift
(`t₀(A, B) ≤ t_S(A − j, B − j)`) and `2D₁ < c`, `D₁ = D₀ + 2u`. Proof: the input rank at one edge, split over
the harmonic pieces (`goodSys_split`), transported to every edge (`goodSys_transport`), bounded above
(`goodSys_card_le`: `g·ν_j ≤ d_j`), so `κ_F·d_j ≤ d_j − g·ν_j`; the sum over all `j ∈ J(A, B)` is
`dim H − g·Σν_j ≤ dim H − (1 − κ_X)·dim H`. -/
theorem key_ineq (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {TT : Finset (Fin n')} (hFD : FlatDim Kf TT k)
    {u : ℕ} {amax : ℝ} (hHS : HarmSplit O Kf p TT k u amax) {WA WB : Finset ℤ}
    {t0 : (TT → ℤ) → (TT → ℤ) → ℕ} {c D₀ : ℕ} {κP : ℝ} {κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ}
    (hI1 : InputRank W k p ι σ ϖ TT WA WB t0 c D₀ κP κT) (tS : (TT → ℤ) → (TT → ℤ) → ℕ) (J : ℕ)
    (hc : 2 * (D₀ + 2 * u) < c) {A B : TT → ℤ} (hAm : A ∈ box WA) (hBm : B ∈ box WB)
    (hJ : ∀ s, (J : ℤ) ≤ A s ∧ (J : ℤ) ≤ B s) (hamax : ∀ s, ((A s + B s + 1 : ℤ) : ℝ) ≤ amax)
    (hshift : ∀ jh ∈ box (Icc 0 (J : ℤ)), t0 A B ≤ tS (A - jh) (B - jh)) :
    ∑ jh ∈ box (Icc 0 (J : ℤ)), kappaF W k p ι σ ϖ TT tS c (D₀ + 2 * u) (A - jh) (B - jh) *
        (∏ s, har (k - 1) (A s - jh s).toNat (B s - jh s).toNat : ℕ) ≤
      (κP + ∑ x ∈ vTops TT, κT x A B) * dimH (k - 1) A B := by
  classical
  have hA0 : ∀ s, 0 ≤ A s := fun s => le_trans (Nat.cast_nonneg J) (hJ s).1
  have hB0 : ∀ s, 0 ≤ B s := fun s => le_trans (Nat.cast_nonneg J) (hJ s).2
  obtain ⟨L'', L, he, n, hn, hsys⟩ := hI1 A hAm B hBm
  obtain ⟨ν, hν, hgs⟩ := goodSys_split hU hk hHS hA0 hB0 hamax he hsys
  have hg1 := one_le_gE hU (k := k) (by omega)
  set g : ℝ := (gE p n' k : ℝ)
  have hgpos : (0 : ℝ) < g := by simp only [g]; exact_mod_cast hg1
  set dd : (TT → ℤ) → ℝ := fun jh => ((∏ s, har (k - 1) (A s - jh s).toNat (B s - jh s).toNat : ℕ) : ℝ)
  have hjB : ∀ jh ∈ jBox A B, ∀ s, 0 ≤ (A - jh) s ∧ 0 ≤ (B - jh) s := fun jh hjh s => by
    have := Fintype.mem_piFinset.1 hjh s
    rw [mem_Icc, le_min_iff] at this
    simp only [Pi.sub_apply]
    omega
  -- the dimension of a flat piece
  have hdim : ∀ jh ∈ jBox A B, (dimV Kf (flatWt (k := k) TT (A - jh) (B - jh)) : ℝ) = dd jh := fun jh hjh => by
    rw [hFD _ _ (fun s => (hjB jh hjh s).1) fun s => (hjB jh hjh s).2]
    rfl
  -- the upper bound `g·ν_j ≤ d_j`
  have hcard : ∀ jh ∈ jBox A B, g * ν jh ≤ dd jh := fun jh hjh => by
    obtain ⟨x, y, z, M, hz, hzD, hx, hy, hG⟩ := hgs jh hjh
    have h := goodSys_card_le hU (antitone_flatWt hk (fun s => (hjB jh hjh s).1) fun s => (hjB jh hjh s).2) hc he
      x y z M hzD hx (fun m => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hy m).1.2 L'') he) hG
    rw [nEdges_eq_gE hU he.1] at h
    rw [← hdim jh hjh]
    simp only [g]
    exact_mod_cast h
  -- `κ_F·d_j ≤ d_j − g·ν_j` on the shifts
  have hsubJ : box (Icc 0 (J : ℤ)) ⊆ jBox A B := fun jh hjh => by
    rw [mem_box] at hjh
    refine Fintype.mem_piFinset.2 fun s => ?_
    have := mem_Icc.1 (hjh s)
    rw [mem_Icc, le_min_iff]
    exact ⟨this.1, this.2.trans (hJ s).1, this.2.trans (hJ s).2⟩
  have hκ : ∀ jh ∈ box (Icc 0 (J : ℤ)),
      kappaF W k p ι σ ϖ TT tS c (D₀ + 2 * u) (A - jh) (B - jh) * dd jh ≤ dd jh - g * ν jh := by
    intro jh hjh
    have hjh' := hsubJ hjh
    have hrank : RankAll W p 1 ι σ ϖ (flatWt (k := k) TT (A - jh) (B - jh)) (tS (A - jh) (B - jh)) c
        (D₀ + 2 * u) (ν jh) := fun L₁'' L₁ he₁ =>
      ⟨ν jh, le_rfl, goodSys_mono hU (goodSys_transport hU he he₁ (hgs jh hjh')) (hshift jh hjh) le_rfl le_rfl⟩
    have hd0 : 0 ≤ dd jh := Nat.cast_nonneg _
    rcases hd0.lt_or_eq with hdpos | hdz
    · have hle := kappaF_le (W := W) (ι := ι) (σ := σ) (ϖ := ϖ) (k := k) (p := p) (tS := tS) (c := c)
        (D := D₀ + 2 * u) (α := A - jh) (β := B - jh) (κ := 1 - g * ν jh / dd jh)
        (by rw [sub_nonneg, div_le_one hdpos]; exact hcard jh hjh') (by
          have : 0 ≤ g * ν jh / dd jh := by positivity
          linarith) (rankAll_mono hU hrank le_rfl le_rfl le_rfl (le_of_eq (by
            rw [hdim jh hjh']; field_simp; ring)))
      calc kappaF W k p ι σ ϖ TT tS c (D₀ + 2 * u) (A - jh) (B - jh) * dd jh
          ≤ (1 - g * ν jh / dd jh) * dd jh := mul_le_mul_of_nonneg_right hle hd0
        _ = dd jh - g * ν jh := by field_simp
    · have h0 : (ν jh : ℝ) = 0 := by
        have := hcard jh hjh'
        rw [← hdz] at this
        nlinarith [(Nat.cast_nonneg (ν jh) : (0 : ℝ) ≤ ν jh)]
      rw [← hdz, h0]
      simp
  -- summing up
  have hsumd : ∑ jh ∈ jBox A B, dd jh = dimH (k - 1) A B := by
    simp only [dd]
    rw [← Nat.cast_sum, sum_jBox_har (by omega) hA0 hB0]
  have hn' : (1 - κP - ∑ x ∈ vTops TT, κT x A B) * dimH (k - 1) A B ≤ g * n := by
    rw [div_le_iff₀ hgpos] at hn
    linarith
  calc ∑ jh ∈ box (Icc 0 (J : ℤ)), kappaF W k p ι σ ϖ TT tS c (D₀ + 2 * u) (A - jh) (B - jh) * dd jh
      ≤ ∑ jh ∈ box (Icc 0 (J : ℤ)), (dd jh - g * ν jh) := Finset.sum_le_sum hκ
    _ ≤ ∑ jh ∈ jBox A B, (dd jh - g * ν jh) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubJ fun jh hjh _ => by linarith [hcard jh hjh]
    _ = dimH (k - 1) A B - g * ∑ jh ∈ jBox A B, (ν jh : ℝ) := by
        rw [Finset.sum_sub_distrib, hsumd, Finset.mul_sum]
    _ ≤ dimH (k - 1) A B - g * n := by
        have : (n : ℝ) ≤ ∑ jh ∈ jBox A B, (ν jh : ℝ) := by exact_mod_cast hν
        nlinarith
    _ ≤ _ := by nlinarith

end Key

/-! ## The parameters of the first theorem -/

section Params

variable {n' : ℕ}

/-- **The working conductor** `c₄ = c* + 2Nc + 2n′c`. -/
def c4F (TT : Finset (Fin n')) (c cStar : ℕ) : ℕ := cStar + 2 * TT.card * c + 2 * n' * c

/-- **The input depth** `⌊t₀(A, B)⌋` (at the conductor `c₄`), the depth of I1. -/
def t0F (Ct C₀ : ℝ) (N₁ p : ℕ) (TT : Finset (Fin n')) (k G' : ℕ) (a b' : ℝ) (c cStar : ℕ) (A B : TT → ℤ) : ℕ :=
  ⌊depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' (c4F TT c cStar) A B⌋₊

/-- **The depth of `κ_F`** `t*(α, β) = ⌈t₀(α, β) + N·J⌉`. -/
def tSF (Ct C₀ : ℝ) (N₁ p : ℕ) (TT : Finset (Fin n')) (k G' : ℕ) (a b' : ℝ) (c cStar : ℕ) (α β : TT → ℤ) : ℕ :=
  ⌈depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' (c4F TT c cStar) α β + TT.card * Jsh C₀ N₁ k a b'⌉₊

/-- **The denominator of `κ_F`** `D₁ = D₀ + 2u`. -/
def D1F (CI : ℝ) (TT : Finset (Fin n')) (Y : ℝ) (N₁ k p : ℕ) (a : ℝ) : ℕ :=
  D0 CI TT.card Y N₁ k (lamA p k a) + 2 * uH TT.card k (lamA p k a)

/-- **The input depth after a shift**: `⌊t₀(A, B)⌋ ≤ t*(A − j, B − j)` for `0 ≤ j ≤ J` (`depth0_shift`). -/
theorem t0F_le_tSF {Ct C₀ : ℝ} {N₁ p : ℕ} (hp : 1 ≤ p) {TT : Finset (Fin n')} {k G' : ℕ} {a b' : ℝ} {c cStar : ℕ}
    (A B jh : TT → ℤ) (hj : ∀ s, 0 ≤ jh s ∧ jh s ≤ Jsh C₀ N₁ k a b') :
    t0F Ct C₀ N₁ p TT k G' a b' c cStar A B ≤ tSF Ct C₀ N₁ p TT k G' a b' c cStar (A - jh) (B - jh) :=
  (Nat.floor_le_ceil _).trans (Nat.ceil_mono (depth0_shift hp _ k G' a b' _ _ A B jh hj))

end Params

/-! ## The means of the flat exceptional fraction at the first theorem's windows (A-N12, A-N13) -/

section MeanFirst

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **The box sum of `κ_F` on a shifted window** (A-N12 with A-N13): under the numeric hypotheses (`C_H ≥ 6C_I +
108`) and the inputs (the Weyl count, the harmonic splitting, I1 and I2 with `κ_P ≤ C_P·N·N₁/Y`), for every shift
`|τ| ≤ c` the sum of `κ_F` over `(I_a + τ)^{TT} × (I_b + τ)^{TT}` is at most `(4/3)·|W_A|^N·|W_B|^N·(C_P + C_A)·N·N₁/Y`:
the key inequality holds on the enlarged box (`key_ineq`), the density is `δ₁^N ≥ 3/4` (`FirstHyp.dens`), and the mean
of `κ_X` is `≤ κ_P + C_A·N·N₁/Y` (`boxSum_kappaX_le`). -/
theorem boxSum_kappaF_le (hU : Unram p n' W Qq O Kf ι σ j ϖ) {C₀ CH : ℝ} {TT : Finset (Fin n')} {G' N₁ : ℕ}
    {Y Yb a b' bl bu : ℝ} {c D cStar : ℕ} (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar)
    (hC₀ : 1 ≤ C₀) {Ct CI CA CP : ℝ} (hCI : 0 ≤ CI) (hCA : 0 ≤ CA) (hCH : 6 * CI + 108 ≤ CH)
    (hFD : FlatDim Kf TT k) (hHS : HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a))
    {κP : ℝ} {κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ}
    (hI1 : InputRank W k p ι σ ϖ TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b'))
      (t0F Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D0 CI TT.card Y N₁ k (lamA p k a)) κP κT)
    (hseg : SegMean TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b')) κT CA N₁ Y)
    (hκP : κP ≤ CP * TT.card * N₁ / Y) (τ : ℤ) (hτ : -(c : ℤ) ≤ τ ∧ τ ≤ c) :
    boxSum (Icc (⌈a⌉ + τ) (⌊a + a / (k * Y)⌋ + τ)) (Icc (⌈bl⌉ + τ) (⌊bu⌋ + τ))
        (kappaF W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D1F CI TT Y N₁ k p a)) ≤
      4 / 3 * (((WAp k Y a c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card *
        ((WBp bl bu c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card) * ((CP + CA) * TT.card * N₁ / Y) := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, -, -, -, -, -, -, -, -, hbl, -, hN₁, hb'1⟩ := h.base hC₀ (by linarith)
  obtain ⟨hJa, hJb, h8a⟩ := h.winP hC₀ (by linarith)
  obtain ⟨-, hJc⟩ := h.J_le hC₀ (by linarith)
  obtain ⟨hδ0, hδ⟩ := h.dens hC₀ (by linarith)
  have hden := h.den hC₀ hCI hCH
  have hcs := h.cStar_ge
  have hY := h.Y_ge
  have hk2 : 2 ≤ k := by have : (5 : ℝ) ≤ k := hk5; exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  have hp1 : 1 ≤ p := by exact_mod_cast (show (1 : ℝ) ≤ p by linarith)
  have hc4 : 2 * (D0 CI TT.card Y N₁ k (lamA p k a) + 2 * uH TT.card k (lamA p k a)) < c4F TT c cStar := by
    unfold c4F; omega
  set J := Jsh C₀ N₁ k a b'
  set κF := kappaF W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D1F CI TT Y N₁ k p a)
  have hf : ∀ α β, 0 ≤ κF α β := fun α β => (kappaF_spec α β).1
  have hbu0 : 0 ≤ bu := by linarith [h.b_win.2.2.1]
  have hav := boxSum_le_of_har (m := k - 1) (J := J) (Ba := WAp k Y a c J) (Bb := WBp bl bu c J)
    (Sa := Icc (⌈a⌉ + τ) (⌊a + a / (k * Y)⌋ + τ)) (Sb := Icc (⌈bl⌉ + τ) (⌊bu⌋ + τ)) κF
    (fun A B => κP + ∑ x ∈ vTops TT, κT x A B) hf hδ0 hJa hJb
    (fun x hx i hi => by
      have h1 := mem_Icc.1 hx; have h2 := mem_Icc.1 hi
      exact mem_Icc.2 ⟨by omega, by omega⟩)
    (fun x hx i hi => by
      have h1 := mem_Icc.1 hx; have h2 := mem_Icc.1 hi
      exact mem_Icc.2 ⟨by omega, by omega⟩)
    (fun A hA B hB => key_ineq hU hk2 hFD hHS hI1 _ J hc4 hA hB
      (fun s => ⟨hJa _ (mem_box.1 hA s), hJb _ (mem_box.1 hB s)⟩)
      (fun s => h8a _ (mem_box.1 hA s) _ (mem_box.1 hB s))
      (fun jh hjh => t0F_le_tSF hp1 A B jh fun s => mem_Icc.1 (mem_box.1 hjh s)))
    (fun α _ β hβ => by
      have h1 := mem_Icc.1 hβ
      have hcl : (c : ℝ) ≤ bl := by
        have := (Nat.cast_nonneg J : (0 : ℝ) ≤ J); linarith
      have hβ0 : 0 ≤ β := by
        have h2 : (⌈bl⌉ : ℝ) - c ≥ 0 := by linarith [Int.le_ceil bl]
        have h3 : (0 : ℤ) ≤ ⌈bl⌉ - c := by exact_mod_cast h2
        omega
      exact deltaF_le_sum hk2 hbu0 α β hβ0 (by omega))
  have hX := boxSum_kappaX_le (κP := κP) hseg (by positivity)
  have hS0 : 0 ≤ boxSum (Icc (⌈a⌉ + τ) (⌊a + a / (k * Y)⌋ + τ)) (Icc (⌈bl⌉ + τ) (⌊bu⌋ + τ)) κF :=
    boxSum_nonneg hf
  have hB0 : (0 : ℝ) ≤ ((WAp k Y a c J).card : ℝ) ^ TT.card * ((WBp bl bu c J).card : ℝ) ^ TT.card := by
    positivity
  have hXP : κP + CA * TT.card * N₁ / Y ≤ (CP + CA) * TT.card * N₁ / Y := by
    have : (CP + CA) * TT.card * N₁ / Y = CP * TT.card * N₁ / Y + CA * TT.card * N₁ / Y := by ring
    linarith
  have h34 : 3 / 4 * boxSum (Icc (⌈a⌉ + τ) (⌊a + a / (k * Y)⌋ + τ)) (Icc (⌈bl⌉ + τ) (⌊bu⌋ + τ)) κF ≤
      deltaF k bu c J ^ TT.card * boxSum (Icc (⌈a⌉ + τ) (⌊a + a / (k * Y)⌋ + τ)) (Icc (⌈bl⌉ + τ) (⌊bu⌋ + τ)) κF :=
    mul_le_mul_of_nonneg_right hδ hS0
  have hBX := mul_le_mul_of_nonneg_left hXP hB0
  nlinarith

variable (W) (k) in
/-- **The exceptional fraction of the first theorem** `κ(a, b) = κ_F(a − c, b − c) + 2κ_F(a + c, b + c) + 12Nkc/b′`,
the combination forced by the cloud step (A-N15). -/
def kappaFirst (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (TT : Finset (Fin n'))
    (tS : (TT → ℤ) → (TT → ℤ) → ℕ) (c₄ D₁ c : ℕ) (b' : ℝ) (aa bb : TT → ℤ) : ℝ :=
  kappaF W k p ι σ ϖ TT tS c₄ D₁ (aa + fun _ => -(c : ℤ)) (bb + fun _ => -(c : ℤ)) +
    2 * kappaF W k p ι σ ϖ TT tS c₄ D₁ (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ)) +
    12 * (TT.card : ℝ) * k * c / b'

/-- **The per-weight assembly** (A-N19): for a weight `λ` of the shape with top extremes `(a_s, b_s)` in the box and
`t ≥ t_I(a, b)`, `LLPAt(t, D, κ(a, b), c*)` holds at every lattice. The flat ranks `κ_F(a ∓ c, b ∓ c)` (attained,
`kappaF_spec`, moved to the larger depth `t*(a + c, b + c)`) go through the cloud step to the top part of `λ`
(conductor `c₄ − 2Nc`, denominator `2D₁ + D_c`), through the off-top step to `λ` (depth `+2n′c`, conductor `c*`),
and assemble (`llpAt_of_rankAll`, `2D + 1 ≤ c*`). -/
theorem llp_first (hU : Unram p n' W Qq O Kf ι σ j ϖ) {C₀ CH : ℝ} {TT : Finset (Fin n')} {G' N₁ : ℕ}
    {Y Yb a b' bl bu : ℝ} {c D cStar : ℕ} (h : FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar)
    (hC₀ : 1 ≤ C₀) {Ct CI C : ℝ} (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCH : 6 * CI + 108 ≤ CH) (hC : Ct + 1 ≤ C)
    (hcl : CloudStep W k p ι σ ϖ TT c (Dcl TT.card k (lamA p k a)) b' a) (hoff : OffTop W k p ι σ ϖ TT c)
    (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ) (hsh : IsShape TT aw bw c lam0)
    (hwin : ∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) (t : ℕ)
    (ht : depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t)
    (L : Submodule W (Fin k → Qq)) (hL : L.IsLattice Qq) :
    LLPAt p 1 ι σ ϖ lam0 t D (kappaFirst W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar)
      (D1F CI TT Y N₁ k p a) c b' (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨hN2, hk5, hp25, -, hb'0, -, -, hpa, -, -, -, -, -, hbl, -, hN₁, hb'1⟩ := h.base hC₀ (by linarith)
  obtain ⟨hcc, hε9, -⟩ := h.cloudCond hC₀ (by linarith)
  have hden := h.den hC₀ hCI hCH
  have hcs := h.cStar_ge
  have hp1 : 1 ≤ p := by exact_mod_cast (show (1 : ℝ) ≤ p by linarith)
  have hab : 25 * b' ≤ a := by nlinarith
  set tS := tSF Ct C₀ N₁ p TT k G' a b' c cStar
  set c₄ := c4F TT c cStar with hc₄
  set D₁ := D1F CI TT Y N₁ k p a with hD₁
  set Dc := Dcl TT.card k (lamA p k a)
  set aa : TT → ℤ := fun s => aw s
  set bb : TT → ℤ := fun s => bw s
  set A1 : TT → ℤ := aa + fun _ => -(c : ℤ)
  set B1 : TT → ℤ := bb + fun _ => -(c : ℤ)
  set ε : ℝ := 12 * (TT.card : ℝ) * k * c / b'
  obtain ⟨hκ₁0, hκ₁1, hR1⟩ := kappaF_spec (W := W) (k := k) (p := p) (ι := ι) (σ := σ) (ϖ := ϖ) (tS := tS)
    (c := c₄) (D := D₁) A1 B1
  obtain ⟨hκ₂0, -, hR2⟩ := kappaF_spec (W := W) (k := k) (p := p) (ι := ι) (σ := σ) (ϖ := ϖ) (tS := tS)
    (c := c₄) (D := D₁) (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ))
  set κ₁ := kappaF W k p ι σ ϖ TT tS c₄ D₁ A1 B1
  set κ₂ := kappaF W k p ι σ ϖ TT tS c₄ D₁ (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ))
  set T := tS (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ))
  have hmono : depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' c₄ A1 B1 ≤
      depth0 Ct (C₀ * N₁ ^ 2 * Real.log a) p TT k G' a b' c₄ (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ)) :=
    depth0_mono hp1 _ k G' a b' _ (fun s => by show aw s + -(c : ℤ) ≤ aw s + c; omega)
      (fun s => by show bw s + -(c : ℤ) ≤ bw s + c; omega)
  have hT1 : tS A1 B1 ≤ T := Nat.ceil_mono (by linarith [hmono])
  have hR1' := rankAll_mono hU hR1 hT1 le_rfl le_rfl le_rfl
  have e2 : ∀ X : TT → ℤ, (X + fun _ => -(c : ℤ)) + (fun _ => 2 * (c : ℤ)) = X + fun _ => (c : ℤ) := fun X => by
    funext s; simp only [Pi.add_apply]; ring
  have hR2' : RankAll W p 1 ι σ ϖ (flatWt (k := k) TT (A1 + fun _ => 2 * (c : ℤ)) (B1 + fun _ => 2 * (c : ℤ))) T c₄
      D₁ ((1 - κ₂) * dimV Kf (flatWt (k := k) TT (A1 + fun _ => 2 * (c : ℤ)) (B1 + fun _ => 2 * (c : ℤ))) /
        gE p n' k) := by
    simp only [A1, B1, e2]
    exact hR2
  -- the top part has the cloud's shape
  have e1 : ∀ X : TT → ℤ, (X + fun _ => -(c : ℤ)) + (fun _ => (c : ℤ)) = X := fun X => by
    funext s; simp only [Pi.add_apply]; ring
  have hshape : IsShape TT (ext TT (A1 + fun _ => (c : ℤ))) (ext TT (B1 + fun _ => (c : ℤ))) c
      (topPart TT lam0) := by
    simp only [A1, B1, e1]
    refine ⟨fun s => ?_, fun s i => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · unfold topPart; split_ifs
      · exact hsh.1 s
      · exact fun _ _ _ => le_rfl
    · have := (hsh.2 s i).1 hs
      simp only [topPart, hs, ↓reduceIte, ext_of_mem _ hs, aa, bb]
      exact this
    · simp [topPart, hs]
  have hzero : ∀ s ∉ TT, topPart TT lam0 s = 0 := fun s hs => by simp [topPart, hs]
  have hcond : ∀ s, b' / 3 ≤ (A1 s : ℝ) ∧ b' / 3 ≤ (B1 s : ℝ) ∧ ((A1 s + B1 s + 4 * c + 1 : ℤ) : ℝ) ≤ 8 * a := by
    intro s
    obtain ⟨h1, h2, h3⟩ := hcc (aw s) (hwin s s.2).1 (bw s) (hwin s s.2).2
    simp only [A1, B1, aa, bb, Pi.add_apply]
    refine ⟨by push_cast at h1 ⊢; linarith, by push_cast at h2 ⊢; linarith, by push_cast at h3 ⊢; linarith⟩
  have h4D : 4 * D₁ < c₄ := by simp only [hD₁, hc₄, D1F, c4F]; omega
  have h2Nc : 2 * TT.card * c ≤ c₄ := by simp only [hc₄, c4F]; omega
  have hRtop := hcl (topPart TT lam0) A1 B1 T c₄ D₁ κ₁ κ₂ hshape hzero hcond hε9 h4D h2Nc hκ₁0 hκ₁1 hκ₂0 hR1' hR2'
  have hRall := hoff lam0 T (c₄ - 2 * TT.card * c) (2 * D₁ + Dc) (κ₁ + 2 * κ₂ + ε) hsh.1
    (fun s hs i => (hsh.2 s i).2 hs) (by simp only [hc₄, c4F]; omega)
    (rankAll_mono hU hRtop le_rfl le_rfl le_rfl (le_of_eq (by ring)))
  -- the depth, the conductor and the denominator
  have haw : ∀ s ∈ TT, 0 ≤ aw s := fun s hs => by
    have h1 := (mem_Icc.1 (hwin s hs).1).1
    have h2 : (0 : ℤ) ≤ ⌈a⌉ := Int.ceil_nonneg (by linarith)
    omega
  have hbw : ∀ s ∈ TT, 0 ≤ bw s := fun s hs => by
    have h1 := (mem_Icc.1 (hwin s hs).2).1
    have h2 : (0 : ℤ) ≤ ⌈bl⌉ := Int.ceil_nonneg (by linarith)
    omega
  have hdep := h.depth hC₀ (by linarith) hCt hC aw bw haw hbw
  have hTt : T + 2 * n' * c ≤ t := by
    have : ((T + 2 * n' * c : ℕ) : ℝ) ≤ t := by
      push_cast
      exact hdep.trans ht
    exact_mod_cast this
  have hRfin := rankAll_mono hU hRall hTt (show cStar ≤ c₄ - 2 * TT.card * c - 2 * n' * c by
    simp only [hc₄, c4F]; omega) (show 2 * D₁ + Dc ≤ D by simp only [hD₁, D1F]; omega) le_rfl
  have hD2 : 2 * D + 1 ≤ cStar := by omega
  have hgpos : (0 : ℝ) < gE p n' k := by
    exact_mod_cast one_le_gE hU (k := k) (by have : (5 : ℝ) ≤ k := hk5; exact_mod_cast (show (1 : ℝ) ≤ k by linarith))
  refine llpAt_of_rankAll hU hD2 (fun L' hL' => ?_) hRfin L hL
  rw [nEdges_eq_gE hU hL', mul_div_assoc', mul_div_cancel_left₀ _ hgpos.ne']
  simp only [kappaFirst, κ₁, κ₂, ε, A1, B1, aa, bb]
  linarith

end MeanFirst

/-! ## The first local theorem (A-N22) -/

/-- **The first local theorem (L5)**, from the inputs: given the constants `C₀ ≥ 1` of `La = C₀N₁²·log a` and
`C_t, C_I, C_A, C_P ≥ 0` of the inputs, there are `C_H = 6C_I + 108` and `C = C_t + 16(C_P + C_A) + 1` such that under
the numeric hypotheses `FirstHyp` (with `C_H`), at a setting `Unram` (one setting per prime, simplification S1), the
inputs
* `FlatDim` (the Weyl count at the flat weights) and `HarmSplit` (the harmonic splitting, A-N7, with
  `u = N·⌈(k + 1)λ_a⌉`, `a_max = 8a`),
* `InputRank` (I1, at the depth `⌊t₀⌋` with constant `C_t`, the conductor `c₄ = c* + 2Nc + 2n′c` and the denominator
  `D₀ = ⌊C_I·N·Y²·N₁²·k²·λ_a⌋`, on the windows `[⌈a⌉ − c, ⌊a + a/(kY)⌋ + c + J] × [⌈b_ℓ⌉ − c, ⌊b_u⌋ + c + J]`,
  `J = ⌊La·b′/k⌋`), `SegMean` (I2, constant `C_A`) and `κ_P ≤ C_P·N·N₁/Y` (I3),
* `CloudStep` (A-N15, with `D_c = N·⌈k²λ_a⌉`) and `OffTop` (A-N18),

give `κ(a, b) ≥ 0` (`kappaFirst`) with box mean `≤ C·N·N₁/Y`, and `LLPAt(1, λ, t, D, κ(a, b), c*)` at every lattice
for every weight `λ` of the shape with top extremes in the box and every `t ≥ t_I(a, b)`. The box mean is three means
of `κ_F` over shifted boxes (`boxSum_shift`, `boxSum_kappaF_le`) and `12Nkc/b′ ≤ 1/Y`; the local lattice problem is
`llp_first`. -/
theorem first_local (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
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
        CloudStep W k p ι σ ϖ TT c (Dcl TT.card k (lamA p k a)) b' a → OffTop W k p ι σ ϖ TT c →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  refine ⟨6 * CI + 108, Ct + 16 * (CP + CA) + 1, by linarith, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar _ _ h W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hFD hHS κP κT
    hI1 hseg hκP hcl hoff
  obtain ⟨hN2, hk5, -, -, hb'0, -, -, -, -, -, -, -, -, -, -, hN₁, hb'1⟩ := h.base hC₀ (by linarith)
  set κF := kappaF W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D1F CI TT Y N₁ k p a)
  have hκF : ∀ α β, 0 ≤ κF α β := fun α β => (kappaF_spec α β).1
  have hε0 : 0 ≤ 12 * (TT.card : ℝ) * k * c / b' := by positivity
  refine ⟨kappaFirst W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D1F CI TT Y N₁ k p a)
    c b', fun aa bb => ?_, ?_, fun aw bw lam0 hsh hwin t ht L hL =>
      llp_first hU h hC₀ hCt hCI le_rfl (by linarith) hcl hoff aw bw lam0 hsh hwin t ht L hL⟩
  · unfold kappaFirst
    have := hκF (aa + fun _ => -(c : ℤ)) (bb + fun _ => -(c : ℤ))
    have := hκF (aa + fun _ => (c : ℤ)) (bb + fun _ => (c : ℤ))
    positivity
  · obtain ⟨-, -, hεY⟩ := h.cloudCond hC₀ (by linarith)
    obtain ⟨hA0, hB0, hrA, hrB⟩ := h.ratio hC₀ (by linarith)
    have hY := h.Y_ge
    have hcardT : Fintype.card TT = TT.card := Fintype.card_coe TT
    -- the box sum of `κ` is three box sums of `κ_F` on shifted boxes and a constant
    have e1 : boxSum (aWin k Y a) (bWin bl bu) (kappaFirst W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar)
        (c4F TT c cStar) (D1F CI TT Y N₁ k p a) c b') =
        boxSum (Icc (⌈a⌉ + -(c : ℤ)) (⌊a + a / (k * Y)⌋ + -(c : ℤ))) (Icc (⌈bl⌉ + -(c : ℤ)) (⌊bu⌋ + -(c : ℤ))) κF +
        2 * boxSum (Icc (⌈a⌉ + (c : ℤ)) (⌊a + a / (k * Y)⌋ + (c : ℤ))) (Icc (⌈bl⌉ + (c : ℤ)) (⌊bu⌋ + (c : ℤ))) κF +
        ((aWin k Y a).card : ℝ) ^ TT.card * ((bWin bl bu).card : ℝ) ^ TT.card *
          (12 * (TT.card : ℝ) * k * c / b') := by
      rw [boxSum_shift, boxSum_shift]
      show boxSum _ _ (fun A B => (κF (A + fun _ => -(c : ℤ)) (B + fun _ => -(c : ℤ)) +
        2 * κF (A + fun _ => (c : ℤ)) (B + fun _ => (c : ℤ))) + 12 * (TT.card : ℝ) * k * c / b') = _
      rw [boxSum_add, boxSum_add, boxSum_smul, boxSum_const, hcardT]
      rfl
    have hm1 := boxSum_kappaF_le hU h hC₀ hCI hCA le_rfl hFD hHS hI1 hseg hκP (-(c : ℤ)) ⟨le_rfl, by omega⟩
    have hp1 := boxSum_kappaF_le hU h hC₀ hCI hCA le_rfl hFD hHS hI1 hseg hκP (c : ℤ) ⟨by omega, le_rfl⟩
    set Big : ℝ := ((WAp k Y a c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card *
      ((WBp bl bu c (Jsh C₀ N₁ k a b')).card : ℝ) ^ TT.card
    set Small : ℝ := ((aWin k Y a).card : ℝ) ^ TT.card * ((bWin bl bu).card : ℝ) ^ TT.card
    set X' : ℝ := (CP + CA) * TT.card * N₁ / Y
    have hSmall : 0 < Small := by positivity
    have hX' : 0 ≤ X' := by positivity
    have hBig : Big ≤ 4 * Small := by
      have := mul_le_mul hrA hrB (by positivity) (by positivity)
      simp only [Big, Small]
      linarith
    have hsum : boxSum (aWin k Y a) (bWin bl bu) (kappaFirst W k p ι σ ϖ TT (tSF Ct C₀ N₁ p TT k G' a b' c cStar)
        (c4F TT c cStar) (D1F CI TT Y N₁ k p a) c b') ≤
        Small * (16 * X' + 12 * (TT.card : ℝ) * k * c / b') := by
      rw [e1]
      have h4 : 4 * Big * X' ≤ 16 * Small * X' := by nlinarith
      nlinarith
    have hεN : 12 * (TT.card : ℝ) * k * c / b' ≤ TT.card * N₁ / Y := by
      refine hεY.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have : (1 : ℝ) ≤ TT.card * N₁ := one_le_mul_of_one_le_of_one_le (by linarith) hN₁
      nlinarith
    unfold boxMean
    rw [div_le_iff₀ hSmall]
    have hC : 16 * X' + 12 * (TT.card : ℝ) * k * c / b' ≤ (Ct + 16 * (CP + CA) + 1) * TT.card * N₁ / Y := by
      have e : (Ct + 16 * (CP + CA) + 1) * TT.card * N₁ / Y =
          Ct * (TT.card * N₁ / Y) + 16 * X' + TT.card * N₁ / Y := by simp only [X']; ring
      have : 0 ≤ Ct * (TT.card * N₁ / Y) := by
        have : (0 : ℝ) < Y := by linarith
        positivity
      linarith
    calc boxSum (aWin k Y a) (bWin bl bu) _ ≤ Small * (16 * X' + 12 * (TT.card : ℝ) * k * c / b') := hsum
      _ ≤ Small * ((Ct + 16 * (CP + CA) + 1) * TT.card * N₁ / Y) := mul_le_mul_of_nonneg_left hC hSmall.le
      _ = _ := by ring

end

end FirstAssembly
