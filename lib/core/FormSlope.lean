import HermFormsLattice

/-!
# The slope lower bound (F)

Piece 3 of the proof of the sharp frontier (`SharpInputs.SlopeFV`, the (F) half): an explicit lower bound
`μ ≥ −c_F` for the slope of the source lattice of the forms (`HermForms.source`: the integral forms `M_ω` of the cut
`V_ω`, with the Petersson metrics `H_{σ_v}` at the complex places), first for the full lattice of integral forms,
then for the cut. Main results: `HermForms.slope_source_ge` (and `exists_slope_source_ge`, with the comparison
constants supplied), `HermForms.slope_source_ge_full` (`ST = ∅`), and the engine `KLattice.slope_ge_of_span`.

**The constant.** With `n_∞` the number of complex places of `L`, `ν = natW λ`, `κ = ⟨hw_ν, hw_ν⟩` (`kappa`),
`max⟨β, β⟩` the largest Fock norm of a bideterminant of shape `ν` (`bmax`), `e = |ν| + n·Σ_σ|λ_{σ,n−1}|` (`eDeg`),
`a, b` nonzero integers with `a·O_E^n ⊆ Lsh(rep c) ⊆ b⁻¹O_E^n` for every class (`Sand`; they exist,
`exists_sand_uniform`), and `N_P = |(O_E/P)^×|`:
`c_F = c_L + ½ log n_∞ + ½ max_c log|Stab(c)| + e·log|ab| + ½ log κ + ½ log max⟨β, β⟩ + Σ_{P∈ST} log(2N_P)`,
i.e. `c_F = c_L + ½ log B` with `B = bCut a b = D_T·B_F`, `D_T = Π_{P∈ST}(2N_P)²` (`DT`, the level-`T` denominator
of the projection onto the cut) and `B_F = n_∞·max|Stab|·(ab)^{2e}·κ·max⟨β, β⟩` (`bF`, the full lattice).
`c_L = Σ_k log nrm(ω_k)/(2[L:ℚ])` (`KLattice.cK`) is the lattice normalisation, `ω_k` a `ℤ`-basis of `O_L`.

**The engine** (`KLattice.slope_ge_of_span`). For a hermitian `O_K`-lattice `X` and vectors `g_i ∈ M` spanning
`K^ι` with `‖ψ g_i‖² ≤ B`: a `K`-basis `f_j` among them and the `ℤ`-basis `ω_k` of `O_K` give `[K:ℚ]·|ι| = rk`
vectors `ψ(ω_k f_j)` of `ψ(M)` spanning its real span (their `ℤ`-span is the full-rank `ψ(⊕_j O_K f_j)`). So
`covol ψ(M) ≤ ∏ ‖ψ(ω_k f_j)‖` (`EuclidLattice.covol_le` and Hadamard's inequality `GramVolume.vol_le_prod_norm`,
from Fischer's), `‖ψ(ωf)‖² ≤ nrm(ω)·‖ψ f‖²` with `nrm(ω) = Σ_v |σ_v ω|²`, and `μ(X) ≥ −c_K − ½ log B`. On the source,
`‖ψ(coords F)‖² = Σ_v Re H_{σ_v}(F, F)` (`norm_ψ_source_sq`, from the sesquilinearity `petAt_sum_smul`), so a
spanning family of integral cut forms with `Σ_v Re H_{σ_v} ≤ B` gives `μ(source) ≥ −c_L − ½ log B`
(`slope_source_ge_of_span`).

**Unitarity.** The hermitian Fock form is unitary for unitary substitutions (`fock_lsub_unitary`: adjointness
`fock_lsub` on the conjugate), the blocks `σ(τ(γ))` of a unitary `γ` are unitary since `σ ∘ conj = conj ∘ σ` on the CM
field (`conjTranspose_mul_map`), and `χ_SG` takes roots of unity (`Λ` is finite): so the action
`actP g = chr(g)·ρ_λ(γ_g)` on values is Fock-unitary at every embedding (`fockWith_map_actP`).

**Integral vectors** (`DeltaA`: `Δ_N` tested in every local basis, which is closed under sums, unlike the
library's `DeltaN`, which asks some basis). For `a·O_E^n ⊆ N ⊆ b⁻¹O_E^n`, `κ_L·(ab)^e·β ∈ Δ_N` for every
bideterminant `β` (`smul_bidet_mem_DeltaA`): in a local basis `C`, `(ab)^{|ν|}β(Cx) = a^{|ν|}β(bC·x)` is integral
(`lsub_smul`, homogeneity), `(ab)^{n|s|}det(C)^s` is integral (`det_zpow_integral`), and the Fock pairing of an
integral polynomial with a bideterminant is integral (`fock_bidet_mem`, `coeff_bidet_mem`). `ρ_λ(γ)` moves `Δ_N`
to `Δ_{γN}` (`rho_mem_DeltaA`, local bases move with `γ`), and `Lsh(g·d) = γ·Lsh(d)` (`Lsh_smul`).

**The full lattice.** The form `ext c P` supported on the class `c` with value `P` at its representative
(`ext_mem_Forms` for `P` stabiliser-invariant; `eq_sum_ext`: every form is the sum over its classes). The family
`F_{c,β} = ext c (proj_c(κ_L(ab)^e·β))`, `proj_c` the sum over the finite stabiliser (`famF`), is integral
(`famF_mem_Mint`: the stabiliser fixes `Lsh(rep c)`), spans the forms (`mem_span_famF`: bideterminants span,
`span_bidet`, and `proj_c = |Stab|` on invariants), and `Re H_σ(F_{c,β}) = mass(c)·fnorm(σ proj)/κ ≤
|Stab(c)|·(ab)^{2e}·κ·⟨β, β⟩` (`petAt_famF_le`: averaging costs `|Stab|²` by convexity, `fnorm_sum_le`, and the
mass gives one `|Stab|` back). With no level-`T` places the cut is all of the forms: `slope_source_ge_full`.

**The cut.** `V_ω = Forms ∩ ⋂_P ker Nm_P` is a sublattice, whose slope is not bounded by the ambient's; we use the
projection instead. The diamond operators form a commutative group action (`dOp_dOp`), keep the attached lattice
(`Lsh_dia`), hence the integral forms (`dOp_mem_MintA`), and keep the Petersson norm (`re_petAt_dOp`: they permute
the classes, keeping the masses, `stabilizer_diaPt`). So `T_P = N_P − Nm_P` (`Tc`) maps the forms into `ker Nm_P`
(`Nm_P² = N_P Nm_P`, `Nm_Nm`; the `Nm_P` commute, `Nm_comm`), is `N_P` on `ker Nm_P`, keeps integrality and costs
`(2N_P)²` in the Petersson norm (`re_petAt_Tc_le`: `T_P F = Σ_u (F − ⟨u⟩F)`). The family `G = Π_P T_P F_{c,β}`
(`famG`) is integral in the cut (`famG_mem_Mω`), spans it (`mem_span_famG`: `Π T_P = Π N_P` on `V_ω`), and has norms
at most `D_T·B_F` (`sum_petAt_famG_le`): `slope_source_ge`. No duality (`μ_min(Δ) = −μ_max(∇)`) is needed.

**What remains** for `SharpInputs.SlopeFV`. (1) The frontier's sources are `X_c ⊓ V_ω` for a further subspace `X_c`
of the forms (`SharpDesign.pinBody`), a sublattice of the cut: the bound here is for `X_c = ⊤`; for general `X_c`
the family must be projected into `X_c` with an integral projection of bounded denominator (as `T_P` does for the
cut), which needs the structure of `X_c`. (2) `a`, `b` are the comparison constants of the chosen representatives;
bounding them in terms of `E` and `n` needs reduction theory (short vectors of the unimodular lattices). (3) `κ` and
`max⟨β, β⟩` are explicit numbers of `ν` (bounding them needs the hook formula or a crude count). (4) The (V)
bookkeeping and the budget `c_F ≤ x^ε Σ_t a_t/8`.
-/

namespace GramVolume

open Matrix Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One vector spans a parallelotope of volume its norm. -/
theorem vol_unique {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι] (v : ι → E) : vol v = ‖v default‖ := by
  rw [vol, Matrix.det_unique, Matrix.gram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **Hadamard's inequality**: `vol v ≤ ∏ ‖vᵢ‖`, by Fischer's inequality (`vol_sumElim_le`) one vector at a time. -/
theorem vol_le_prod_norm [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    vol v ≤ ∏ i, ‖v i‖ := by
  suffices h : ∀ (n : ℕ) (w : Fin n → E), vol w ≤ ∏ i, ‖w i‖ by
    have := h _ (v ∘ (Fintype.equivFin ι).symm)
    rwa [vol_comp_equiv, Function.comp_def, Equiv.prod_comp (Fintype.equivFin ι).symm fun i => ‖v i‖] at this
  intro n
  induction n with
  | zero => intro w; simp [vol_of_isEmpty]
  | succ n ih =>
    intro w
    have h1 : vol w = vol (Sum.elim (fun i : Fin n => w (Fin.castAdd 1 i)) fun j : Fin 1 => w (Fin.natAdd n j)) := by
      rw [← vol_comp_equiv w finSumFinEquiv]
      congr 1
      funext s
      cases s <;> simp
    rw [h1, Fin.prod_univ_castSucc]
    refine (vol_sumElim_le _ _).trans (mul_le_mul (ih _) (le_of_eq ?_) (vol_nonneg _) ?_)
    · rw [vol_unique]
      rfl
    · exact Finset.prod_nonneg fun _ _ => norm_nonneg _

end GramVolume

namespace KLattice

open Module Submodule NumberField HermitianLattice Matrix WithLp

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical InnerProductSpace

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (X : KLattice K ι)

/-- The size `nrm(k) = Σ_v |σ_v(k)|²` of `k ∈ K` at the complex places. -/
noncomputable def nrm (k : K) : ℝ := ∑ v : Pl K, ‖v.1.embedding k‖ ^ 2

/-- The `ℤ`-basis `ω_k` of `O_K` in `K`. -/
noncomputable abbrev ω (k : Free.ChooseBasisIndex ℤ (𝓞 K)) : K := (RingOfIntegers.basis K k : K)

omit [Fintype ι] in
/-- `nrm k ≥ 0`. -/
theorem nrm_nonneg (k : K) : 0 ≤ nrm k := Finset.sum_nonneg fun _ _ => sq_nonneg _

variable (K) in
/-- **The lattice normalisation** `c_K = Σ_k log nrm(ω_k)/(2[K:ℚ])`, over the `ℤ`-basis `ω_k` of `O_K`
(`RingOfIntegers.basis`): a constant of `K` alone. -/
noncomputable def cK : ℝ := (∑ k, Real.log (nrm (ω (K := K) k))) / (2 * finrank ℚ K)

/-- The squared norm in `⊕_v ℂ^ι` is the sum of the squared moduli of the coordinates. -/
theorem norm_sq_eq (y : Space K ι) : ‖y‖ ^ 2 = ∑ p, ‖coord p y‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq (𝕜 := ℂ) (n := ι × Pl K) y

/-- `ψ(k·x)` has the coordinates of `ψ x` times `σ_v(k)`. -/
theorem coord_ψ_smul (k : K) (x : ι → K) (p : ι × Pl K) :
    coord p (X.ψ (k • x)) = p.2.1.embedding k * coord p (X.ψ x) := by
  rw [ψ_smul, coord_act]
  rfl

/-- `‖ψ(k·x)‖² ≤ nrm(k)·‖ψ x‖²`. -/
theorem norm_ψ_smul_sq_le (k : K) (x : ι → K) : ‖X.ψ (k • x)‖ ^ 2 ≤ nrm k * ‖X.ψ x‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [coord_ψ_smul, norm_mul, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact Finset.single_le_sum (f := fun v : Pl K => ‖v.1.embedding k‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ p.2)

/-- **The norm of `ψ x`** is the sum over the complex places of the metrics: `‖ψ x‖² = Σ_v σ_v(x)ᴴ G_v σ_v(x)`. -/
theorem norm_ψ_sq (x : ι → K) :
    ‖X.ψ x‖ ^ 2 = ∑ v : Pl K, (star (fun i => v.1.embedding (x i)) ⬝ᵥ (X.G v *ᵥ fun i => v.1.embedding (x i))).re := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_re_inner ℂ, inner_ψ, inner_apply, Fintype.sum_prod_type_right]
  show Complex.re _ = _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  simp only [dotProduct, mulVec, coord_op, coord_ψ₀, Pi.star_apply, RCLike.star_def]

omit [Fintype ι] in
/-- `ω_k·x = basis_k·x` for the `O_K`-action. -/
theorem ω_smul (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (x : ι → K) :
    ω k • x = RingOfIntegers.basis K k • x :=
  algebraMap_smul K (RingOfIntegers.basis K k) x

/-- The vectors `ψ(ω_k f_j)` of the lattice, `[K:ℚ]·|ι|` of them. -/
noncomputable def fam (f : ι → ι → K) : Free.ChooseBasisIndex ℤ (𝓞 K) × ι → Space K ι :=
  fun p => X.ψ (ω p.1 • f p.2)

/-- The `ψ(ω_k f_j)` lie in the lattice. -/
theorem fam_mem {f : ι → ι → K} (hfM : ∀ j, f j ∈ X.M) (p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι) :
    X.fam f p ∈ X.lattice :=
  ⟨ω p.1 • f p.2, by rw [ω_smul]; exact X.M.smul_mem _ (hfM p.2), rfl⟩

/-- `ψ` is additive, so `ℤ`-linear. -/
theorem ψ_zsmul (z : ℤ) (x : ι → K) : X.ψ (z • x) = z • X.ψ x := map_zsmul X.ψ z x

/-- The `ψ(a f_j)`, `a ∈ O_K`, lie in the `ℤ`-span of the `ψ(ω_k f_j)`: `a = Σ_k z_k ω_k`. -/
theorem ψ_smul_mem_span (f : ι → ι → K) (a : 𝓞 K) (j : ι) :
    X.ψ ((a : K) • f j) ∈ span ℤ (Set.range (X.fam f)) := by
  have ha : (a : K) = ∑ k, (RingOfIntegers.basis K).repr a k • ω k := by
    conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr a]
    simp only [map_sum, ω]
    exact Finset.sum_congr rfl fun k _ => map_zsmul (algebraMap (𝓞 K) K) _ _
  rw [ha, Finset.sum_smul, map_sum]
  refine sum_mem fun k _ => ?_
  rw [smul_assoc, ψ_zsmul]
  exact zsmul_mem (subset_span (Set.mem_range_self (f := X.fam f) (k, j))) _

/-- **The vectors span**: their `ℤ`-span contains `ψ(⊕_j O_K f_j)`, a full-rank sublattice (`span_lattice` for
`X.withLattice (⊕_j O_K f_j)`), when the `f_j` are a `K`-basis. -/
theorem top_le_span_fam {f : ι → ι → K} (hf : LinearIndependent K f) (hc : Fintype.card ι = finrank K (ι → K)) :
    ⊤ ≤ span ℝ (Set.range (X.fam f)) := by
  set N : Submodule (𝓞 K) (ι → K) := span (𝓞 K) (Set.range f)
  have hN : N.IsLattice K := ⟨fg_span (Set.finite_range f), by
    rw [Submodule.span_span_of_tower]
    exact hf.span_eq_top_of_card_eq_finrank' hc⟩
  have hle : (X.withLattice N).lattice ≤ span ℤ (Set.range (X.fam f)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun (𝓞 K)).1 hx
    show X.ψ _ ∈ _
    rw [map_sum]
    exact sum_mem fun j _ => by rw [← algebraMap_smul K]; exact X.ψ_smul_mem_span f (a j) j
  rw [← (X.withLattice N).span_lattice]
  refine span_le.2 fun y hy => ?_
  exact span_le_restrictScalars ℤ ℝ _ (hle hy)

variable [IsTotallyComplex K]

/-- The `ℤ`-rank of the lattice is `[K:ℚ]·|ι|`, the number of the `ψ(ω_k f_j)`. -/
theorem card_fam_le : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K) × ι) ≤ finrank ℤ X.lattice := by
  rw [← EuclidLattice.finrank_span]
  have h := X.rk_top
  change finrank ℝ (span ℝ (X.lattice : Set (Space K ι))) = _ at h
  rw [h, Fintype.card_prod, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

/-- **The covolume bound**: `covol ψ(M) ≤ ∏_{k,j} √nrm(ω_k)·‖ψ f_j‖` for a `K`-basis `f_j` in `M` (`covol_le`, then
Hadamard). -/
theorem covol_le_of_basis {f : ι → ι → K} (hf : LinearIndependent K f) (hc : Fintype.card ι = finrank K (ι → K))
    (hfM : ∀ j, f j ∈ X.M) :
    EuclidLattice.covol X.lattice ≤ ∏ p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι, (√(nrm (ω p.1)) * ‖X.ψ (f p.2)‖) := by
  refine (EuclidLattice.covol_le (X.fam_mem hfM) (le_top.trans (X.top_le_span_fam hf hc)) X.card_fam_le).trans
    ((GramVolume.vol_le_prod_norm _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p _ => ?_))
  show ‖X.fam f p‖ ≤ _
  rw [← Real.sqrt_sq (norm_nonneg (X.fam f p)), ← Real.sqrt_sq (norm_nonneg (X.ψ (f p.2))),
    ← Real.sqrt_mul (nrm_nonneg _)]
  exact Real.sqrt_le_sqrt (X.norm_ψ_smul_sq_le _ _)

/-- `nrm(ω_k) > 0`, as `ω_k ≠ 0` and `K` has a complex place. -/
theorem nrm_ω_pos (k : Free.ChooseBasisIndex ℤ (𝓞 K)) : 0 < nrm (ω (K := K) k) := by
  obtain ⟨v⟩ : Nonempty (Pl K) := ⟨⟨Classical.arbitrary _, IsTotallyComplex.isComplex _⟩⟩
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun v : Pl K => ‖v.1.embedding (ω k)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ v))
  have h : ω k ≠ 0 := fun h => (RingOfIntegers.basis K).ne_zero k (RingOfIntegers.coe_eq_zero_iff.1 h)
  have : v.1.embedding (ω k) ≠ 0 := (map_ne_zero _).2 h
  positivity

/-- `ψ x ≠ 0` for `x ≠ 0`. -/
theorem norm_ψ_pos {x : ι → K} (hx : x ≠ 0) : 0 < ‖X.ψ x‖ :=
  norm_pos_iff.2 fun h => hx (X.ψ_injective (h.trans (map_zero _).symm))

/-- **The slope from a basis**: `μ(X) ≥ −c_K − Σ_j log ‖ψ f_j‖/|ι|` for a `K`-basis `f_j` of `K^ι` in `M`. Divide
`log covol ≤ |ι|·Σ_k ½ log nrm(ω_k) + [K:ℚ]·Σ_j log ‖ψ f_j‖` (`covol_le_of_basis`) by `rk = [K:ℚ]·|ι|`. -/
theorem slope_ge_of_basis [Nonempty ι] {f : ι → ι → K} (hf : LinearIndependent K f)
    (hc : Fintype.card ι = finrank K (ι → K)) (hfM : ∀ j, f j ∈ X.M) :
    -cK K - (∑ j, Real.log ‖X.ψ (f j)‖) / Fintype.card ι ≤
      X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ := by
  have hpos : ∀ p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι, 0 < √(nrm (ω p.1)) * ‖X.ψ (f p.2)‖ := fun p =>
    mul_pos (Real.sqrt_pos.2 (nrm_ω_pos _)) (X.norm_ψ_pos (hf.ne_zero p.2))
  have hlog := Real.log_le_log (EuclidLattice.covol_pos _) (X.covol_le_of_basis hf hc hfM)
  rw [Real.log_prod (fun p _ => (hpos p).ne')] at hlog
  have hsum : ∑ p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι, Real.log (√(nrm (ω p.1)) * ‖X.ψ (f p.2)‖) =
      Fintype.card ι * (∑ k, Real.log (nrm (ω (K := K) k))) / 2 +
        finrank ℚ K * ∑ j, Real.log ‖X.ψ (f j)‖ := by
    rw [Fintype.sum_prod_type]
    have hd : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = finrank ℚ K := by
      rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
    simp_rw [Real.log_mul (Real.sqrt_pos.2 (nrm_ω_pos _)).ne' (X.norm_ψ_pos (hf.ne_zero _)).ne',
      Real.log_sqrt (nrm_nonneg _), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hd, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 finrank_pos
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [rk_top]
  show _ ≤ -Real.log (EuclidLattice.covol X.lattice) / _
  rw [le_div_iff₀ (by push_cast; positivity)]
  have : (-cK K - (∑ j, Real.log ‖X.ψ (f j)‖) / Fintype.card ι) * (finrank ℚ K * Fintype.card ι : ℕ) =
      -(Fintype.card ι * (∑ k, Real.log (nrm (ω (K := K) k))) / 2 +
        finrank ℚ K * ∑ j, Real.log ‖X.ψ (f j)‖) := by
    unfold cK
    push_cast
    field_simp
    ring
  rw [this]
  linarith

/-- **The slope from a spanning family** (the engine): if vectors `g_i ∈ M` span `K^ι` over `K` and
`‖ψ g_i‖² ≤ B` for every `i`, then `μ(X) ≥ −c_K − ½ log B`. A `K`-basis among them (`exists_linearIndependent'`)
gives `slope_ge_of_basis`, and `log ‖ψ f_j‖ ≤ ½ log B`. -/
theorem slope_ge_of_span [Nonempty ι] {I : Type*} (g : I → ι → K) (hg : span K (Set.range g) = ⊤)
    (hgM : ∀ i, g i ∈ X.M) {B : ℝ} (hB : ∀ i, ‖X.ψ (g i)‖ ^ 2 ≤ B) :
    -cK K - Real.log B / 2 ≤ X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' K g
  rw [hg] at hspan
  have : Finite κ := hli.finite
  let := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← finrank_span_eq_card hli, hspan, finrank_top, Module.finrank_fintype_fun_eq_card]
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hli' : LinearIndependent K (g ∘ a ∘ e) := hli.comp e e.injective
  refine le_trans ?_ (X.slope_ge_of_basis hli' (Module.finrank_fintype_fun_eq_card K).symm fun j => hgM _)
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hj : ∀ j, Real.log ‖X.ψ ((g ∘ a ∘ e) j)‖ ≤ Real.log B / 2 := fun j => by
    have hp := X.norm_ψ_pos (hli'.ne_zero j)
    have := Real.log_le_log (pow_pos hp 2) (hB (a (e j)))
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hS : ∑ j, Real.log ‖X.ψ ((g ∘ a ∘ e) j)‖ ≤ Fintype.card ι * (Real.log B / 2) := by
    simpa using Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
  have : (∑ j, Real.log ‖X.ψ ((g ∘ a ∘ e) j)‖) / Fintype.card ι ≤ Real.log B / 2 := by
    rw [div_le_iff₀ hr]
    linarith
  linarith

end KLattice

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial

open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]

/-! ## The Petersson form is sesquilinear -/

section Sesq

omit [Fintype Φ] [DecidableEq Φ] in
/-- The hermitian Fock form is the bilinear one on the conjugate. -/
theorem fockWith_star (P Q : Pol Φ n ℂ) :
    fockWith (starRingEnd ℂ) P Q = fockWith (RingHom.id ℂ) (map (starRingEnd ℂ) P) Q := by
  simp only [fockWith, coeff_map, RingHom.id_apply]

omit [DecidableEq Φ] in
/-- **The normalised Fock form is sesquilinear**: `⟨Σ aᵢPᵢ, Σ bⱼQⱼ⟩ = Σ conj(aᵢ)bⱼ⟨Pᵢ, Qⱼ⟩`. -/
theorem fock_sum_smul (ν : Φ → Fin n → ℕ) {I J : Type*} [Fintype I] [Fintype J] (a : I → ℂ) (P : I → Pol Φ n ℂ)
    (b : J → ℂ) (Q : J → Pol Φ n ℂ) :
    fock ν (∑ i, C (a i) * P i) (∑ j, C (b j) * Q j) =
      ∑ i, ∑ j, starRingEnd ℂ (a i) * b j * fock ν (P i) (Q j) := by
  unfold fock
  rw [fockWith_star (∑ i, C (a i) * P i)]
  simp only [map_sum, map_mul, map_C, fock_sum_left, fock_C_mul_left, fock_sum_right, fock_C_mul_right,
    ← fockWith_star, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (ST) (lam : Φ → Fin n → ℤ)

omit [DecidableEq Φ] [NumberField L] in
/-- The Petersson form at `σ` over the finitely many classes. -/
theorem petAt_eq_sum [Fintype (DCl E n ST Λ)] (σ : L →+* ℂ) (F G : Fn ST Λ Φ L) :
    petAt ST lam σ F G = ∑ c : DCl E n ST Λ,
      (mass c : ℂ) * fock (fun ρ => natW (lam ρ)) (map σ (F c.out)) (map σ (G c.out)) := by
  simp only [petAt, classSum, finsum_eq_sum_of_fintype, Rat.smul_def]

omit [DecidableEq Φ] [NumberField L] in
/-- **The Petersson form at `σ` is sesquilinear**:
`H_σ(Σ xᵢFᵢ, Σ yⱼGⱼ) = Σ conj(σxᵢ)·σyⱼ·H_σ(Fᵢ, Gⱼ)`. -/
theorem petAt_sum_smul (σ : L →+* ℂ) {I J : Type*} [Fintype I] [Fintype J] (x : I → L) (F : I → Fn ST Λ Φ L)
    (y : J → L) (G : J → Fn ST Λ Φ L) :
    petAt ST lam σ (∑ i, x i • F i) (∑ j, y j • G j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (x i)) * σ (y j) * petAt ST lam σ (F i) (G j) := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  simp only [petAt_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul, map_sum, map_mul, map_C,
    fock_sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Sesq

/-! ## Unitarity of the Fock form -/

section Unitary

open scoped Matrix

omit [Fintype Φ] [DecidableEq Φ] in
/-- A ring map on the coefficients commutes with a substitution, the matrices mapped too. -/
theorem map_lsub {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (g : Φ → Matrix (Fin n) (Fin n) K)
    (P : Pol Φ n K) : map φ (lsub g P) = lsub (fun σ => (g σ).map φ) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, lsub_X, map_sum]

/-- **The Fock form is unitary**: a substitution by unitary blocks, `U_σ U_σᴴ = 1`, keeps it. By adjointness
(`fock_lsub`), `⟨P(Ux), Q(Ux)⟩ = ⟨P((Ū Uᵀ)x), Q⟩` on the conjugate, and `Ū Uᵀ = conj(U Uᴴ) = 1`. -/
theorem fock_lsub_unitary (U : Φ → Matrix (Fin n) (Fin n) ℂ) (hU : ∀ σ, U σ * (U σ)ᴴ = 1) (P Q : Pol Φ n ℂ) :
    fockWith (starRingEnd ℂ) (lsub U P) (lsub U Q) = fockWith (starRingEnd ℂ) P Q := by
  rw [fockWith_star, fockWith_star, map_lsub, ← fock_lsub, lsub_lsub]
  have h1 : (fun σ => (U σ).map (starRingEnd ℂ) * (U σ)ᵀ) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) :=
    funext fun σ => by
      have h := congrArg (Matrix.map · (starRingEnd ℂ)) (hU σ)
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      rw [← h]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
  rw [h1, lsub_one]
  rfl

/-- At an embedding `φ : E → ℂ`, a unitary `γ` is a unitary matrix, `φ(γ)ᴴφ(γ) = 1`, as `φ ∘ conj = conj ∘ φ`
(`emb_herm`). -/
theorem conjTranspose_mul_map {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (φ : E →+* ℂ) :
    ((γ : Matrix (Fin n) (Fin n) E).map φ)ᴴ * (γ : Matrix (Fin n) (Fin n) E).map φ = 1 := by
  ext i j
  have h := congrArg φ (hγ (Pi.single i 1) (Pi.single j 1))
  rw [emb_herm, emb_herm] at h
  simp only [act_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def]
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij, Finset.sum_ite_eq']

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ(γ)` is the twist by `τ(γ⁻¹)`. -/
theorem rho_eq_twist (γ : GL (Fin n) E) (F : Pol Φ n L) :
    rho τ lam γ F = twist lam (fun σ => (τ σ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) F := by
  unfold rho twist
  congr 2
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← RingHom.map_det, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, inv_zpow']

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is multiplicative: `ρ(γδ) = ρ(γ)ρ(δ)` (`twist_twist`). -/
theorem rho_mul (γ δ : GL (Fin n) E) (F : Pol Φ n L) :
    rho τ lam (γ * δ) F = rho τ lam γ (rho τ lam δ F) := by
  rw [rho_eq_twist, rho_eq_twist, rho_eq_twist, twist_twist]
  congr 1
  funext σ
  rw [← map_mul, mul_inv_rev, Units.val_mul]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is additive. -/
theorem rho_add (γ : GL (Fin n) E) (F G : Pol Φ n L) : rho τ lam γ (F + G) = rho τ lam γ F + rho τ lam γ G := by
  rw [rho_eq_twist, rho_eq_twist, rho_eq_twist, twist_add]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is `L`-linear. -/
theorem rho_smul (γ : GL (Fin n) E) (a : L) (F : Pol Φ n L) : rho τ lam γ (a • F) = a • rho τ lam γ F := by
  rw [rho_eq_twist, rho_eq_twist, twist_smul]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ(1)` is the identity. -/
theorem rho_one (F : Pol Φ n L) : rho τ lam 1 F = F := by
  rw [rho_eq_twist, inv_one, Units.val_one]
  simp only [map_one]
  exact twist_one lam F

omit [DecidableEq Φ] in
/-- `‖φ(det γ)‖ = 1` for a unitary `γ`. -/
theorem norm_map_det {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (φ : E →+* ℂ) :
    ‖φ (γ : Matrix (Fin n) (Fin n) E).det‖ = 1 := by
  have h := congrArg Matrix.det (conjTranspose_mul_map hγ φ)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : ‖φ (γ : Matrix (Fin n) (Fin n) E).det‖ ^ 2 = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm, ← RCLike.star_def]
    simpa using h
  nlinarith [norm_nonneg (φ (γ : Matrix (Fin n) (Fin n) E).det)]

omit [NumberField L] in
/-- **`ρ_λ` is Fock-unitary at every embedding**: for `γ ∈ U_n(E)` and `σ : L → ℂ`, the blocks `σ(τ(γ⁻¹))` are
unitary (`conjTranspose_mul_map`) and the determinant factor has modulus `1` (`norm_map_det`). -/
theorem fockWith_map_rho {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (σ : L →+* ℂ) (F G : Pol Φ n L) :
    fockWith (starRingEnd ℂ) (map σ (rho τ lam γ F)) (map σ (rho τ lam γ G)) =
      fockWith (starRingEnd ℂ) (map σ F) (map σ G) := by
  set c := ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-detShift (lam ρ))
  have hc : ‖σ c‖ = 1 := by
    simp only [c, map_prod, map_zpow₀, norm_prod, norm_zpow]
    exact Finset.prod_eq_one fun ρ _ => by
      rw [show σ (τ ρ (γ : Matrix (Fin n) (Fin n) E).det) = (σ.comp (τ ρ)) (γ : Matrix (Fin n) (Fin n) E).det
        from rfl, norm_map_det hγ, one_zpow]
  have hU : ∀ ρ, ((τ ρ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).map σ *
      (((τ ρ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).map σ)ᴴ = 1 := fun ρ => by
    have h := conjTranspose_mul_map (inv_mem hγ) (σ.comp (τ ρ))
    exact mul_eq_one_comm.1 h
  unfold rho
  rw [map_mul, map_mul, map_C, map_lsub, map_lsub, fockWith_star, map_mul, map_C, fock_C_mul_left,
    fock_C_mul_right, ← fockWith_star, fock_lsub_unitary _ hU]
  have : starRingEnd ℂ (σ c) * σ c = 1 := by
    rw [mul_comm, Complex.mul_conj', hc]
    simp
  rw [← mul_assoc, this, one_mul]

end Unitary

/-! ## Integral vectors: `Δ_N` tested in every local basis -/

section Integral

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- The polynomials with coefficients in a subring `A` are the image of `A[x]`. -/
theorem mem_range_map_iff {A : Subring L} {F : Pol Φ n L} :
    F ∈ (map A.subtype).range ↔ ∀ d, F.coeff d ∈ A := by
  rw [RingHom.mem_range, ← Set.mem_range, mem_range_map_iff_coeffs_subset]
  refine ⟨fun h d => ?_, fun h x hx => ?_⟩
  · by_cases hd : F.coeff d = 0
    · rw [hd]
      exact A.zero_mem
    · obtain ⟨a, ha⟩ := h (coeff_mem_coeffs d hd)
      rw [← ha]
      exact a.2
  · obtain ⟨d, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact ⟨⟨_, h d⟩, rfl⟩

omit [DecidableEq Φ] [NumberField L] in
/-- **Bideterminants have integer coefficients**: they lie in every subring. -/
theorem coeff_bidet_mem (A : Subring L) (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) (d : Φ × Fin n × Fin n →₀ ℕ) :
    (bidet L ν rows).coeff d ∈ A := by
  set R := (map A.subtype : MvPolynomial (Φ × Fin n × Fin n) A →+* Pol Φ n L).range
  have hX : ∀ p, (X p : Pol Φ n L) ∈ R := fun p => ⟨X p, by simp⟩
  have hminor : ∀ τ s I, (minor τ s I : Pol Φ n L) ∈ R := fun τ s I => by
    rw [minor, Matrix.det_apply]
    exact R.sum_mem fun σ _ => by
      rw [Units.smul_def]
      exact zsmul_mem (R.prod_mem fun i _ => hX _) _
  have : bidet L ν rows ∈ R := R.prod_mem fun τ _ => R.prod_mem fun s _ => R.prod_mem fun c _ => hminor _ _ _
  exact mem_range_map_iff.1 this d

omit [DecidableEq Φ] [NumberField L] in
/-- The Fock pairing of a polynomial with coefficients in `A` with a bideterminant lies in `A`. -/
theorem fock_bidet_mem {A : Subring L} {Q : Pol Φ n L} (hQ : ∀ d, Q.coeff d ∈ A) (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    fockWith (RingHom.id L) Q (bidet L ν rows) ∈ A := by
  rw [fock_eq_sum_left (subset_refl _)]
  exact A.sum_mem fun d _ => A.mul_mem (A.mul_mem (hQ d) (coeff_bidet_mem A ν rows d))
    (A.prod_mem fun _ _ => natCast_mem A _)

omit [NumberField L] in
/-- **Homogeneity**: on polynomials of column degrees `m`, the substitution `x ↦ c·x` is multiplication by
`c^{|m|}`, `|m| = Σ m`. -/
theorem lsub_smul_one {F : Pol Φ n L} {m : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (colW Φ n) F m) (c : L) :
    lsub (fun _ => c • (1 : Matrix (Fin n) (Fin n) L)) F = c ^ (∑ σ, ∑ j, m σ j) • F := by
  have hX : ∀ p : Φ × Fin n × Fin n, lsub (fun _ => c • (1 : Matrix (Fin n) (Fin n) L)) (X p) = C c * X p :=
    fun p => by
      rw [lsub_X, Finset.sum_eq_single p.2.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  conv_rhs => rw [F.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ σ, ∑ j, m σ j = ∑ p ∈ d.support, d p := by
    rw [← hF (mem_support_iff.1 hd), Finsupp.weight_apply]
    simp only [Finsupp.sum, colW, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single p.1 (fun σ _ h => by simp [h]) (by simp),
      Finset.sum_eq_single p.2.2 (fun j _ h => by simp [h]) (by simp)]
    simp
  rw [hdeg, monomial_eq, map_mul, lsub_C, Finsupp.prod, map_prod]
  simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← map_pow, smul_eq_C_mul]
  ring

omit [NumberField L] in
/-- Scaling the substitution: `F(c·Ax) = c^{|m|}·F(Ax)` on column degrees `m`. -/
theorem lsub_smul {F : Pol Φ n L} {m : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (colW Φ n) F m)
    (c : L) (A : Φ → Matrix (Fin n) (Fin n) L) :
    lsub (fun σ => c • A σ) F = c ^ (∑ σ, ∑ j, m σ j) • lsub A F := by
  rw [← map_smul, ← lsub_smul_one hF c, lsub_lsub]
  congr 2
  funext σ
  rw [Matrix.smul_mul, Matrix.one_mul]

end Integral

/-! ## `Δ_N` in every local basis -/

section DeltaA

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

/-- `Δ_N(λ)` tested in **every** tuple of local bases (`DeltaN` asks some): closed under sums
(`add_mem_DeltaA`), and moved by `ρ_λ(γ)` to `Δ_{γN}` (`rho_mem_DeltaA`). It lies in `Δ_N` (`DeltaA_subset`). -/
def DeltaA (N : Submodule (𝓞 E) (Fin n → E)) : Set (Pol Φ n L) :=
  {F | F ∈ VV lam ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (C : Φ → Matrix (Fin n) (Fin n) L),
    (∀ σ, IsLocalBasis w (τ σ) N (C σ)) → twist lam C F ∈ Delta (Ow w) fun σ => natW (lam σ)}

variable {τ lam}

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis lies in `Δ_N`, local bases existing (`exists_localBasis`). -/
theorem DeltaA_subset {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b) :
    DeltaA τ lam N ⊆ DeltaN τ lam N := fun F hF =>
  ⟨hF.1, fun w => by
    choose C hC using fun σ => exists_localBasis (w := w) (σ := τ σ) h
    exact ⟨C, hC, hF.2 w C hC⟩⟩

omit [NumberField L] in
/-- `Δ_A` is closed under sums. -/
theorem add_mem_Delta {A : Subring L} {ν : Φ → Fin n → ℕ} {F G : Pol Φ n L} (hF : F ∈ Delta A ν)
    (hG : G ∈ Delta A ν) : F + G ∈ Delta A ν :=
  ⟨add_mem hF.1 hG.1, fun rows => by rw [fock_add_left, add_div]; exact A.add_mem (hF.2 rows) (hG.2 rows)⟩

omit [NumberField L] in
/-- `Δ_A` is closed under `A`. -/
theorem smul_mem_Delta {A : Subring L} {ν : Φ → Fin n → ℕ} {F : Pol Φ n L} (hF : F ∈ Delta A ν) {c : L}
    (hc : c ∈ A) : c • F ∈ Delta A ν :=
  ⟨Submodule.smul_mem _ _ hF.1, fun rows => by rw [fock_smul_left, mul_div_assoc]; exact A.mul_mem hc (hF.2 rows)⟩

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis is closed under sums. -/
theorem add_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} {F G : Pol Φ n L} (hF : F ∈ DeltaA τ lam N)
    (hG : G ∈ DeltaA τ lam N) : F + G ∈ DeltaA τ lam N :=
  ⟨add_mem hF.1 hG.1, fun w C hC => by rw [twist_add]; exact add_mem_Delta (hF.2 w C hC) (hG.2 w C hC)⟩

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis is closed under the elements of `L` integral at every `w`. -/
theorem smul_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} {F : Pol Φ n L} (hF : F ∈ DeltaA τ lam N) {c : L}
    (hc : ∀ w : HeightOneSpectrum (𝓞 L), c ∈ Ow w) : c • F ∈ DeltaA τ lam N :=
  ⟨Submodule.smul_mem _ _ hF.1, fun w C hC => by rw [twist_smul]; exact smul_mem_Delta (hF.2 w C hC) (hc w)⟩

omit [NumberField E] [IsCMField E] in
/-- `0 ∈ Δ_N`. -/
theorem zero_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} : (0 : Pol Φ n L) ∈ DeltaA τ lam N :=
  ⟨zero_mem _, fun w C hC => ⟨by simp [twist], fun rows => by simp [twist, fockWith]⟩⟩

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis is closed under finite sums. -/
theorem sum_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} {ι : Type*} (s : Finset ι) {F : ι → Pol Φ n L}
    (h : ∀ i ∈ s, F i ∈ DeltaA τ lam N) : ∑ i ∈ s, F i ∈ DeltaA τ lam N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_DeltaA
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_DeltaA (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [NumberField E] [IsCMField E] in
/-- **Local bases move with `γ`**: `σ(γ)·C` is a local basis of `γN` when `C` is one of `N`. -/
theorem isLocalBasis_map {w : HeightOneSpectrum (𝓞 L)} {σ : E →+* L} {N : Submodule (𝓞 E) (Fin n → E)}
    {C : Matrix (Fin n) (Fin n) L} (hC : IsLocalBasis w σ N C) (γ : GL (Fin n) E) :
    IsLocalBasis w σ (N.map (act γ)) (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E) * C) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero σ).2 (Matrix.isUnits_det_units γ).ne_zero) hC.1
  · let T : (Fin n → L) →ₗ[Ow w] (Fin n → L) :=
      (Matrix.mulVecLin (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E))).restrictScalars (Ow w)
    have h1 : (fun v i => σ (v i)) '' ((N.map (act γ) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        T '' ((fun v i => σ (v i)) '' (N : Set (Fin n → E))) := by
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, act_apply]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, funext fun i => by simp [T, RingHom.map_mulVec]; rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, funext fun i => by simp [T, RingHom.map_mulVec]; rfl⟩
    have h2 : Set.range (fun j i => (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E) * C) i j) =
        T '' Set.range (fun j i => C i j) := by
      rw [← Set.range_comp]
      congr 1
    rw [h1, h2, Submodule.span_image, Submodule.span_image, hC.2]

omit [NumberField E] [IsCMField E] in
/-- **`ρ_λ(γ)` moves `Δ_N` to `Δ_{γN}`**: a local basis `C'` of `γN` is `τ(γ)C` for the local basis
`C = τ(γ⁻¹)C'` of `N`, and `twist_{C'}(ρ(γ)F) = twist_C F` (`twist_twist`). -/
theorem rho_mem_DeltaA (γ : GL (Fin n) E) {N : Submodule (𝓞 E) (Fin n → E)} {F : Pol Φ n L}
    (hF : F ∈ DeltaA τ lam N) : rho τ lam γ F ∈ DeltaA τ lam (N.map (act γ)) := by
  refine ⟨?_, fun w C' hC' => ?_⟩
  · rw [rho_eq_twist]
    exact twist_mem_nabla _ _ hF.1
  · have hN : (N.map (act γ)).map (act γ⁻¹) = N := by
      rw [← Submodule.map_comp]
      convert Submodule.map_id N
      exact LinearMap.ext fun x => act_inv_act γ x
    have hC : ∀ σ, IsLocalBasis w (τ σ) N ((τ σ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * C' σ) :=
      fun σ => hN ▸ isLocalBasis_map (hC' σ) γ⁻¹
    rw [rho_eq_twist, twist_twist]
    exact hF.2 w _ hC

end DeltaA

/-! ## The integral vectors `κ·(ab)^e·β`, and the character -/

section IntVec

variable {τ : Φ → (E →+* L)} {lam : Φ → Fin n → ℤ}

variable (lam) in
/-- The exponent `e = |ν| + n·Σ_σ |λ_{σ,n−1}|` of the integrality constant `κ·(ab)^e`, `ν = natW λ`, `|ν| = Σ ν`. -/
def eDeg : ℕ := (∑ σ, ∑ j, natW (lam σ) j) + n * ∑ σ, (detShift (lam σ)).natAbs

omit [NumberField E] [IsCMField E] in
/-- `(ab)^{n|s|}·det(C)^s` is integral at `w` for a local basis `C` of `N` between `a·O_E^n` and `b⁻¹O_E^n`:
`b·C` is integral (`smul_integral`), and `a^n·det(C)⁻¹ = det U` with `a·1 = C·U`, `U` integral (`exists_U`). -/
theorem det_zpow_integral {w : HeightOneSpectrum (𝓞 L)} {σ : E →+* L} {N : Submodule (𝓞 E) (Fin n → E)}
    {a b : ℤ} (h : Sand N a b) {C : Matrix (Fin n) (Fin n) L} (hC : IsLocalBasis w σ N C) (s : ℤ) :
    ((a * b : ℤ) : L) ^ (n * s.natAbs) * C.det ^ s ∈ Ow w := by
  obtain ⟨U, hU, haU⟩ := exists_U h hC.2.symm
  have hcol : ∀ j, (fun i => C i j) ∈ Nw w σ N := fun j => by
    unfold Nw
    rw [hC.2]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hbC : ∀ i j, ((b : L) • C) i j ∈ Ow w := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact smul_integral h hcol i j
  have hdet : C.det * U.det = (a : L) ^ n := by
    rw [← Matrix.det_mul, ← haU, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · have : ((a * b : ℤ) : L) ^ (n * (k : ℤ).natAbs) * C.det ^ (k : ℤ) =
        (a : L) ^ (n * k) * ((b : L) • C).det ^ k := by
      rw [Int.natAbs_natCast, zpow_natCast, Matrix.det_smul, Fintype.card_fin]
      push_cast
      ring
    rw [this]
    exact (Ow w).mul_mem ((Ow w).pow_mem (intCast_mem _ a) _) ((Ow w).pow_mem (det_mem hbC) _)
  · have hC0 : C.det ≠ 0 := hC.1
    have : ((a * b : ℤ) : L) ^ (n * (-(k : ℤ)).natAbs) * C.det ^ (-(k : ℤ)) = (b : L) ^ (n * k) * U.det ^ k := by
      rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
        div_eq_iff (pow_ne_zero _ hC0), mul_assoc, ← mul_pow, mul_comm U.det, hdet]
      push_cast
      ring
    rw [this]
    exact (Ow w).mul_mem ((Ow w).pow_mem (intCast_mem _ b) _) ((Ow w).pow_mem (det_mem hU) _)

omit [NumberField E] [IsCMField E] in
/-- **Integral vectors**: for `N` between `a·O_E^n` and `b⁻¹O_E^n`, `κ·(ab)^e·β ∈ Δ_N` for every bideterminant
`β` of shape `ν = natW λ`, in every local basis `C`: `(ab)^{|ν|}·β(Cx) = a^{|ν|}·β(bC·x)` is integral (`lsub_smul`,
`b·C` integral), `(ab)^{n|s|}·det(C)^s` is integral (`det_zpow_integral`), and the Fock pairing of an integral
polynomial with a bideterminant is integral (`fock_bidet_mem`); `κ = fock(hw, hw)` cancels the normalisation. -/
theorem smul_bidet_mem_DeltaA (hlam : ∀ σ, Antitone (lam σ)) {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ}
    (h : Sand N a b) (rows : (ρ : Φ) → (s : Fin n) → Fin (mult (natW (lam ρ)) s) → Fin (s + 1) → Fin n) :
    (fockWith (RingHom.id L) (hw L fun ρ => natW (lam ρ)) (hw L fun ρ => natW (lam ρ)) *
      ((a * b : ℤ) : L) ^ eDeg lam) • bidet L (fun ρ => natW (lam ρ)) rows ∈ DeltaA τ lam N := by
  set ν : Φ → Fin n → ℕ := fun ρ => natW (lam ρ)
  set κ := fockWith (RingHom.id L) (hw L ν) (hw L ν)
  have hκ : κ ≠ 0 := fock_hw_hw_ne_zero ν
  have hβ : bidet L ν rows ∈ nabla L ν := bidet_mem_nabla (fun ρ => natW_antitone (hlam ρ)) rows
  refine ⟨Submodule.smul_mem _ _ hβ, fun w C hC => ⟨twist_mem_nabla _ _ (Submodule.smul_mem _ _ hβ),
    fun rows' => ?_⟩⟩
  have hcol : ∀ σ j, (fun i => C σ i j) ∈ Nw w (τ σ) N := fun σ j => by
    unfold Nw
    rw [(hC σ).2]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hbC : ∀ σ i j, ((b : L) • C σ) i j ∈ Ow w := fun σ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact smul_integral h (hcol σ) i j
  have hint : ∀ d, ((a : L) ^ (∑ σ, ∑ j, ν σ j) •
      lsub (fun σ => (b : L) • C σ) (bidet L ν rows)).coeff d ∈ Ow w := fun d => by
    rw [coeff_smul, smul_eq_mul]
    exact (Ow w).mul_mem ((Ow w).pow_mem (intCast_mem _ a) _) (lsub_coeff_mem hbC (coeff_bidet_mem _ ν rows) d)
  have h1 := fock_bidet_mem hint ν rows'
  rw [lsub_smul (mem_nabla_iff.1 hβ).1, smul_smul, fock_smul_left] at h1
  have h2 : ∏ σ, (((a * b : ℤ) : L) ^ (n * (detShift (lam σ)).natAbs) * (C σ).det ^ detShift (lam σ)) ∈ Ow w :=
    prod_mem fun σ _ => det_zpow_integral h (hC σ) _
  rw [twist_smul, fock_smul_left, twist, fock_C_mul_left]
  have : κ * ((a * b : ℤ) : L) ^ eDeg lam * ((∏ σ, (C σ).det ^ detShift (lam σ)) *
      fockWith (RingHom.id L) (lsub C (bidet L ν rows)) (bidet L ν rows')) / κ =
      (∏ σ, (((a * b : ℤ) : L) ^ (n * (detShift (lam σ)).natAbs) * (C σ).det ^ detShift (lam σ))) *
        ((a : L) ^ (∑ σ, ∑ j, ν σ j) * (b : L) ^ (∑ σ, ∑ j, ν σ j) *
          fockWith (RingHom.id L) (lsub C (bidet L ν rows)) (bidet L ν rows')) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, eDeg, pow_add, ← Finset.mul_sum]
    field_simp
    push_cast
    ring
  rw [this]
  exact (Ow w).mul_mem h2 h1

end IntVec

/-! ## The character is a root of unity -/

section Chr

omit [IsCMField E] in
/-- The level group is finite: the residue rings at `SG` are finite (`finite_residue`). -/
theorem finite_Λ : Finite Λ := by
  have : ∀ w : SG, Finite (𝓞 E ⧸ w.1.asIdeal) := fun w => finite_residue w.1
  infer_instance

omit [NumberField L] in
/-- `χ_SG(h)` is a root of unity, `Λ` being finite. -/
theorem exists_pow_chr (χ : Λ →* L) (g : Grp E n SG Λ) : ∃ m : ℕ, 0 < m ∧ chr χ g ^ m = 1 := by
  have := finite_Λ (Λ := Λ)
  refine ⟨orderOf g.2, orderOf_pos g.2, ?_⟩
  rw [chr, MonoidHom.comp_apply, ← map_pow]
  show χ (g.2 ^ orderOf g.2) = 1
  rw [pow_orderOf_eq_one, map_one]

/-- The character is integral at every finite place. -/
theorem chr_mem_Ow (χ : Λ →* L) (g : Grp E n SG Λ) (w : HeightOneSpectrum (𝓞 L)) : chr χ g ∈ Ow w := by
  obtain ⟨m, hm, h⟩ := exists_pow_chr χ g
  have hi : IsIntegral ℤ (chr χ g) := IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := w.valuation_le_one (K := L) (⟨chr χ g, hi⟩ : 𝓞 L)
  exact this

omit [NumberField L] in
/-- The character has modulus `1` at every embedding. -/
theorem norm_map_chr (χ : Λ →* L) (g : Grp E n SG Λ) (σ : L →+* ℂ) : ‖σ (chr χ g)‖ = 1 := by
  obtain ⟨m, hm, h⟩ := exists_pow_chr χ g
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, h, map_one]) hm.ne'

end Chr

/-! ## The action on values, and the forms supported on one class -/

section Ext

omit [NumberField E] [IsCMField E] in
/-- Membership in the image of a kernel in `E^n`. -/
theorem mem_map_subtype_ker {N : Submodule (𝓞 E) (Fin n → E)} {M : Type*} [AddCommGroup M] [Module (𝓞 E) M]
    (f : N →ₗ[𝓞 E] M) {x : Fin n → E} : x ∈ (LinearMap.ker f).map N.subtype ↔ ∃ hx : x ∈ N, f ⟨x, hx⟩ = 0 :=
  ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.2, hy⟩, fun ⟨hx, h⟩ => ⟨⟨x, hx⟩, h, rfl⟩⟩

/-- The level-`T` kernel moves with `g`: `kerLat(g·d) = γ·kerLat(d)`. -/
theorem kerLat_smul (g : Grp E n SG Λ) (d : Deco E n ST SG) : kerLat (g • d) = (kerLat d).map (act g.1.1) := by
  ext x
  rw [mem_map_act]
  simp only [kerLat, Submodule.mem_inf, Submodule.mem_iInf, mem_map_subtype_ker]
  constructor
  · rintro ⟨hx, h⟩
    have hx' : act g.1.1⁻¹ x ∈ d.N := mem_map_act.1 hx
    refine ⟨hx', fun P => ⟨hx', ?_⟩⟩
    obtain ⟨_, hP⟩ := h P
    rw [smul_f] at hP
    convert hP using 2
    exact Subtype.ext rfl
  · rintro ⟨hx', h⟩
    have hx : x ∈ (g • d).N := mem_map_act.2 hx'
    refine ⟨hx, fun P => ⟨hx, ?_⟩⟩
    obtain ⟨_, hP⟩ := h P
    rw [smul_f]
    convert hP using 2
    exact Subtype.ext rfl

/-- **The attached lattice moves with `g`**: `Lsh(g·d) = γ·Lsh(d)` (`kerLat_smul`, `dual_map`). -/
theorem Lsh_smul (g : Grp E n SG Λ) (d : Deco E n ST SG) : Lsh (g • d) = (Lsh d).map (act g.1.1) := by
  rw [Lsh, Lsh, kerLat_smul, dual_map g.1.2]

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The action `chr(g)·ρ_λ(γ_g)` on the values of forms: `F(g·d) = actP g (F d)` for a form. -/
def actP (g : Grp E n SG Λ) (P : Pol Φ n L) : Pol Φ n L := chr χ g • rho τ lam g.1.1 P

omit [DecidableEq Φ] [NumberField L] in
/-- The action is multiplicative. -/
theorem actP_mul (g h : Grp E n SG Λ) (P : Pol Φ n L) :
    actP τ χ lam (g * h) P = actP τ χ lam g (actP τ χ lam h P) := by
  simp only [actP, map_mul, rho_smul, smul_smul]
  rw [show (g * h).1.1 = g.1.1 * h.1.1 from rfl, rho_mul]

omit [DecidableEq Φ] [NumberField L] in
/-- `actP 1` is the identity. -/
theorem actP_one (P : Pol Φ n L) : actP τ χ lam 1 P = P := by
  simp only [actP, map_one, one_smul]
  exact rho_one τ lam P

omit [DecidableEq Φ] [NumberField L] in
/-- The action is additive. -/
theorem actP_add (g : Grp E n SG Λ) (P Q : Pol Φ n L) :
    actP τ χ lam g (P + Q) = actP τ χ lam g P + actP τ χ lam g Q := by
  simp only [actP, rho_add, smul_add]

omit [DecidableEq Φ] [NumberField L] in
/-- The action is `L`-linear. -/
theorem actP_smul (g : Grp E n SG Λ) (a : L) (P : Pol Φ n L) :
    actP τ χ lam g (a • P) = a • actP τ χ lam g P := by
  simp only [actP, rho_smul, smul_comm a]

omit [DecidableEq Φ] [NumberField L] in
/-- `actP g 0 = 0`. -/
theorem actP_zero (g : Grp E n SG Λ) : actP τ χ lam g (0 : Pol Φ n L) = 0 := by
  simpa using actP_smul τ χ lam g 0 0

omit [DecidableEq Φ] [NumberField L] in
/-- The action commutes with finite sums. -/
theorem actP_sum (g : Grp E n SG Λ) {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n L) :
    actP τ χ lam g (∑ i ∈ s, P i) = ∑ i ∈ s, actP τ χ lam g (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using actP_zero τ χ lam g
  | insert i s hi ih => rw [Finset.sum_insert hi, actP_add, ih, Finset.sum_insert hi]

omit [NumberField L] in
/-- The action keeps `VV(λ)`. -/
theorem actP_mem_VV (g : Grp E n SG Λ) {P : Pol Φ n L} (hP : P ∈ VV lam) : actP τ χ lam g P ∈ VV lam := by
  rw [actP, rho_eq_twist]
  exact Submodule.smul_mem _ _ (twist_mem_nabla _ _ hP)

/-- **The action moves integral vectors**: `actP g` maps `Δ_{Lsh(d)}` to `Δ_{Lsh(g·d)}` in every local basis
(`rho_mem_DeltaA`, `Lsh_smul`, `chr_mem_Ow`). -/
theorem actP_mem_DeltaA (g : Grp E n SG Λ) {d : Deco E n ST SG} {P : Pol Φ n L}
    (hP : P ∈ DeltaA τ lam (Lsh d)) : actP τ χ lam g P ∈ DeltaA τ lam (Lsh (g • d)) := by
  rw [Lsh_smul]
  exact smul_mem_DeltaA (rho_mem_DeltaA g.1.1 hP) (chr_mem_Ow χ g)

omit [NumberField L] in
/-- **The action is Fock-unitary at every embedding** (`fockWith_map_rho`, `norm_map_chr`). -/
theorem fockWith_map_actP (g : Grp E n SG Λ) (σ : L →+* ℂ) (P Q : Pol Φ n L) :
    fockWith (starRingEnd ℂ) (map σ (actP τ χ lam g P)) (map σ (actP τ χ lam g Q)) =
      fockWith (starRingEnd ℂ) (map σ P) (map σ Q) := by
  simp only [actP, smul_eq_C_mul, map_mul, map_C]
  rw [fockWith_star, map_mul, map_C, fock_C_mul_left, fock_C_mul_right, ← fockWith_star,
    fockWith_map_rho τ lam g.1.2]
  have h : starRingEnd ℂ (σ (chr χ g)) * σ (chr χ g) = 1 := by
    rw [mul_comm, Complex.mul_conj', norm_map_chr]
    simp
  rw [← mul_assoc, h, one_mul]

/-- A point in the class `c` is `g·rep c`. -/
theorem exists_smul_out {c : DCl E n ST Λ} {d : points (E := E) (n := n) (ST := ST) Λ}
    (h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c) :
    ∃ g : Grp E n SG Λ, g • c.out = d := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel (Grp E n SG Λ) _) d
  subst h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

open Classical in
/-- **The form supported on the class `c`** with value `P` at its representative: `F(g·rep c) = actP g P`, and `0`
off the class. It is a form when `P` is invariant under the stabiliser (`ext_mem_Forms`). -/
def ext (c : DCl E n ST Λ) (P : Pol Φ n L) : Fn ST Λ Φ L := fun d =>
  if h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c then
    actP τ χ lam (Classical.choose (exists_smul_out h)) P else 0

/-- `P` is invariant under the stabiliser of the representative of `c`. -/
def Inv (c : DCl E n ST Λ) (P : Pol Φ n L) : Prop := ∀ h ∈ stab c, actP τ χ lam h P = P

omit [DecidableEq Φ] [NumberField L] in
/-- The value of `ext c P` at `g·rep c` is `actP g P`, for invariant `P`. -/
theorem ext_smul_out {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : Inv τ χ lam c P) (g : Grp E n SG Λ) :
    ext τ χ lam c P (g • c.out) = actP τ χ lam g P := by
  have h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • c.out) : DCl E n ST Λ) = c :=
    (Quotient.sound ⟨g, rfl⟩ : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • c.out) : DCl E n ST Λ) =
      Quotient.mk _ c.out).trans (Quotient.out_eq c)
  rw [ext, dite_eq_left_of_eq_true (eq_true h)]
  set g' := Classical.choose (exists_smul_out h)
  have hg' : g' • c.out = g • c.out := Classical.choose_spec (exists_smul_out h)
  have hs : g⁻¹ * g' ∈ stab c := by
    show (g⁻¹ * g') • c.out = c.out
    rw [mul_smul, hg', inv_smul_smul]
  rw [show g' = g * (g⁻¹ * g') by group, actP_mul, hP _ hs]

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` has the value `P` at the representative of `c`. -/
theorem ext_out {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : Inv τ χ lam c P) : ext τ χ lam c P c.out = P := by
  have := ext_smul_out τ χ lam hP 1
  rwa [one_smul, actP_one] at this

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` vanishes off the class `c`. -/
theorem ext_eq_zero {c : DCl E n ST Λ} {d : points (E := E) (n := n) (ST := ST) Λ}
    (h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) ≠ c) (P : Pol Φ n L) :
    ext τ χ lam c P d = 0 := by
  rw [ext, dite_eq_right_of_eq_false (eq_false h)]

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` vanishes at the representatives of the other classes. -/
theorem ext_out_ne {c c' : DCl E n ST Λ} (hc : c' ≠ c) (P : Pol Φ n L) : ext τ χ lam c P c'.out = 0 :=
  ext_eq_zero τ χ lam (by rwa [Quotient.out_eq]) P

omit [NumberField L] in
/-- **`ext c P` is a form** for `P ∈ VV(λ)` invariant under the stabiliser. -/
theorem ext_mem_Forms {c : DCl E n ST Λ} {P : Pol Φ n L} (hV : P ∈ VV lam) (hP : Inv τ χ lam c P) :
    ext τ χ lam c P ∈ Forms ST τ χ lam := by
  refine ⟨fun d => ?_, fun g d => ?_⟩
  · unfold ext
    split_ifs
    · exact actP_mem_VV τ χ lam _ hV
    · exact zero_mem _
  · by_cases h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c
    · obtain ⟨g', rfl⟩ := exists_smul_out h
      rw [← mul_smul, ext_smul_out τ χ lam hP, ext_smul_out τ χ lam hP, actP_mul]
      rfl
    · have h' : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • d) : DCl E n ST Λ) ≠ c := by
        rwa [show (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • d) : DCl E n ST Λ) =
          Quotient.mk _ d from Quotient.sound ⟨g, rfl⟩]
      rw [ext_eq_zero τ χ lam h, ext_eq_zero τ χ lam h']
      exact (actP_zero τ χ lam g).symm

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c` is linear in the value. -/
theorem ext_sum_smul (c : DCl E n ST Λ) {ι : Type*} (s : Finset ι) (a : ι → L) (P : ι → Pol Φ n L) :
    ext τ χ lam c (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • ext τ χ lam c (P i) := by
  funext d
  simp only [Finset.sum_apply, Pi.smul_apply]
  unfold ext
  split_ifs
  · rw [actP_sum]
    exact Finset.sum_congr rfl fun i _ => actP_smul τ χ lam _ _ _
  · simp

omit [NumberField L] in
/-- **A form is the sum of the forms supported on its classes**: `F = Σ_c ext c (F(rep c))`. -/
theorem eq_sum_ext [Fintype (DCl E n ST Λ)] {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    F = ∑ c, ext τ χ lam c (F c.out) := by
  have hinv : ∀ c : DCl E n ST Λ, Inv τ χ lam c (F c.out) := fun c h hh => by
    show chr χ h • rho τ lam h.1.1 (F c.out) = F c.out
    rw [← hF.2]
    exact congrArg F hh
  funext d
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : DCl E n ST Λ, Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d = c₀ := ⟨_, rfl⟩
  obtain ⟨g, rfl⟩ := exists_smul_out hc₀
  rw [Finset.sum_apply, Finset.sum_eq_single c₀]
  · rw [ext_smul_out τ χ lam (hinv c₀), hF.2]
    rfl
  · intro c _ hc
    exact ext_eq_zero τ χ lam (hc₀.trans_ne (Ne.symm hc)) _
  · simp

end Ext

/-! ## Averaging over the stabiliser, and the Fock norm -/

section Proj

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The stabiliser average `Σ_{h ∈ Stab(rep c)} actP h P`: invariant (`inv_proj`), integral with `P`
(`proj_mem_DeltaA`), and `|Stab|·P` on invariant `P` (`proj_of_inv`). -/
def proj (c : DCl E n ST Λ) (P : Pol Φ n L) : Pol Φ n L := ∑ᶠ h : stab c, actP τ χ lam h P

omit [DecidableEq Φ] [NumberField L] in
/-- The average over the finite stabiliser as a sum. -/
theorem proj_eq_sum (c : DCl E n ST Λ) [Fintype (stab c)] (P : Pol Φ n L) :
    proj τ χ lam c P = ∑ h : stab c, actP τ χ lam h P :=
  finsum_eq_sum_of_fintype _

omit [DecidableEq Φ] [NumberField L] in
/-- **The average is invariant**: `actP h` permutes the terms. -/
theorem inv_proj (c : DCl E n ST Λ) (P : Pol Φ n L) : Inv τ χ lam c (proj τ χ lam c P) := fun h hh => by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  rw [proj_eq_sum, actP_sum]
  simp_rw [← actP_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : stab c)) _ _ fun h' => rfl

omit [DecidableEq Φ] [NumberField L] in
/-- On invariant vectors the average is `|Stab|·P`. -/
theorem proj_of_inv {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : Inv τ χ lam c P) :
    proj τ χ lam c P = (Nat.card (stab c) : L) • P := by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  rw [proj_eq_sum, Finset.sum_congr rfl fun h _ => hP h.1 h.2, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul L]

omit [DecidableEq Φ] [NumberField L] in
/-- The average is linear. -/
theorem proj_sum_smul (c : DCl E n ST Λ) {ι : Type*} (s : Finset ι) (a : ι → L) (P : ι → Pol Φ n L) :
    proj τ χ lam c (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • proj τ χ lam c (P i) := by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  simp only [proj_eq_sum, actP_sum, actP_smul, Finset.smul_sum]
  exact Finset.sum_comm

/-- **The average of an integral vector is integral**: the stabiliser fixes `Lsh(rep c)` (`actP_mem_DeltaA`). -/
theorem proj_mem_DeltaA {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : P ∈ DeltaA τ lam (Lsh c.rep)) :
    proj τ χ lam c P ∈ DeltaA τ lam (Lsh c.rep) := by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  rw [proj_eq_sum]
  refine sum_mem_DeltaA _ fun h _ => ?_
  have hh : h.1 • c.rep = c.rep := congrArg Subtype.val h.2
  have := actP_mem_DeltaA τ χ lam h.1 hP
  rwa [hh] at this

end Proj

section FNorm

/-- The Fock norm `Σ_d |P_d|²·d!` of a polynomial over `ℂ`. -/
def fnorm (P : Pol Φ n ℂ) : ℝ := ∑ d ∈ P.support, ‖P.coeff d‖ ^ 2 * ∏ p, ((d p).factorial : ℝ)

omit [DecidableEq Φ] in
/-- The Fock norm over any finite set of exponents containing the support. -/
theorem fnorm_eq_sum {P : Pol Φ n ℂ} {S : Finset (Φ × Fin n × Fin n →₀ ℕ)} (hS : P.support ⊆ S) :
    fnorm P = ∑ d ∈ S, ‖P.coeff d‖ ^ 2 * ∏ p, ((d p).factorial : ℝ) :=
  Finset.sum_subset hS fun d _ hd => by rw [notMem_support_iff.1 hd]; simp

omit [DecidableEq Φ] in
/-- `fnorm ≥ 0`. -/
theorem fnorm_nonneg (P : Pol Φ n ℂ) : 0 ≤ fnorm P :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

omit [DecidableEq Φ] in
/-- **The hermitian Fock form on the diagonal is the Fock norm.** -/
theorem fockWith_self (P : Pol Φ n ℂ) : fockWith (starRingEnd ℂ) P P = (fnorm P : ℂ) := by
  rw [fockWith_eq_sum _ (subset_refl _), fnorm]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj', fact]

omit [DecidableEq Φ] in
/-- `fnorm(a·P) = |a|²·fnorm P`. -/
theorem fnorm_smul (a : ℂ) (P : Pol Φ n ℂ) : fnorm (a • P) = ‖a‖ ^ 2 * fnorm P := by
  rw [fnorm_eq_sum (support_smul (a := a) (f := P)), fnorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  ring

omit [DecidableEq Φ] in
/-- **Convexity**: `fnorm(Σ_{i∈s} Pᵢ) ≤ |s|·Σ fnorm Pᵢ` (`|Σ xᵢ|² ≤ |s|·Σ|xᵢ|²` at each coefficient). -/
theorem fnorm_sum_le {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n ℂ) :
    fnorm (∑ i ∈ s, P i) ≤ s.card * ∑ i ∈ s, fnorm (P i) := by
  classical
  set S := (∑ i ∈ s, P i).support ∪ s.biUnion fun i => (P i).support
  rw [fnorm_eq_sum (Finset.subset_union_left : _ ⊆ S)]
  have hS : ∀ i ∈ s, fnorm (P i) = ∑ d ∈ S, ‖(P i).coeff d‖ ^ 2 * ∏ p, ((d p).factorial : ℝ) := fun i hi =>
    fnorm_eq_sum (fun d hd => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hd⟩))
  rw [Finset.sum_congr rfl hS, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
  rw [coeff_sum]
  calc ‖∑ i ∈ s, (P i).coeff d‖ ^ 2 ≤ (∑ i ∈ s, ‖(P i).coeff d‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ s.card * ∑ i ∈ s, ‖(P i).coeff d‖ ^ 2 := sq_sum_le_card_mul_sum_sq

end FNorm

/-! ## The constants `κ` and `‖β‖²`, and the Petersson norm of a form on one class -/

section Consts

variable (lam : Φ → Fin n → ℤ)

/-- `κ = ⟨hw_ν, hw_ν⟩ = Σ_d (hw_ν)_d²·d!`, `ν = natW λ`: the Fock norm of the highest-weight vector, a positive
rational (an integer). -/
def kappa : ℚ := fockWith (RingHom.id ℚ) (hw ℚ fun ρ => natW (lam ρ)) (hw ℚ fun ρ => natW (lam ρ))

/-- The Fock norm `⟨β, β⟩` of a bideterminant of shape `natW λ`. -/
def bnorm (rows : (ρ : Φ) → (s : Fin n) → Fin (mult (natW (lam ρ)) s) → Fin (s + 1) → Fin n) : ℚ :=
  fockWith (RingHom.id ℚ) (bidet ℚ (fun ρ => natW (lam ρ)) rows) (bidet ℚ (fun ρ => natW (lam ρ)) rows)

/-- The largest Fock norm `max_rows ⟨β, β⟩` of the bideterminants of shape `natW λ`. -/
def bmax : ℝ := ⨆ rows, (bnorm lam rows : ℝ)

omit [DecidableEq Φ] in
/-- `⟨β, β⟩ ≤ max`. -/
theorem bnorm_le_bmax (rows : (ρ : Φ) → (s : Fin n) → Fin (mult (natW (lam ρ)) s) → Fin (s + 1) → Fin n) :
    (bnorm lam rows : ℝ) ≤ bmax lam :=
  le_ciSup (f := fun rows => (bnorm lam rows : ℝ)) (Set.finite_range _).bddAbove rows

omit [DecidableEq Φ] in
/-- `κ > 0`. -/
theorem kappa_pos : 0 < kappa lam :=
  fock_self_pos_rat fun h => by simpa [h] using eval_one_hw (L := ℚ) (Φ := Φ) fun ρ => natW (lam ρ)

omit [DecidableEq Φ] in
/-- Bideterminants map to bideterminants under a ring map. -/
theorem map_bidet' {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    map φ (bidet K ν rows) = bidet K' ν rows := by
  simp only [bidet, minor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  simp [xMat]

omit [Fintype Φ] [DecidableEq Φ] in
/-- An embedding commutes with the bilinear Fock form. -/
theorem map_fockWith_id {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (P Q : Pol Φ n K) :
    φ (fockWith (RingHom.id K) P Q) = fockWith (RingHom.id K') (map φ P) (map φ Q) := by
  simp only [fockWith, map_sum, map_mul, coeff_map, support_map_of_injective _ φ.injective, Finsupp.prod,
    map_prod, map_natCast, RingHom.id_apply]

omit [Fintype Φ] [DecidableEq Φ] in
/-- The hermitian Fock norm of a polynomial with rational coefficients is the rational one. -/
theorem fockWith_star_map_rat (P : Pol Φ n ℚ) :
    fockWith (starRingEnd ℂ) (map (algebraMap ℚ ℂ) P) (map (algebraMap ℚ ℂ) P) =
      ((fockWith (RingHom.id ℚ) P P : ℚ) : ℂ) := by
  rw [fockWith_star, map_map]
  have : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  rw [this, ← map_fockWith_id]
  rfl

omit [DecidableEq Φ] in
/-- The normaliser of `fock` over `ℂ` is `κ`. -/
theorem fockWith_hw_C : fockWith (starRingEnd ℂ) (hw ℂ fun ρ => natW (lam ρ)) (hw ℂ fun ρ => natW (lam ρ)) =
    (kappa lam : ℂ) := by
  rw [← map_hw (algebraMap ℚ ℂ), fockWith_star_map_rat]
  rfl

omit [DecidableEq Φ] [NumberField L] in
/-- `σ(κ_L) = κ`: the normaliser over `L` maps to `κ`. -/
theorem map_kappa_L (σ : L →+* ℂ) :
    σ (fockWith (RingHom.id L) (hw L fun ρ => natW (lam ρ)) (hw L fun ρ => natW (lam ρ))) = (kappa lam : ℂ) := by
  rw [map_fockWith_id, map_hw, ← map_hw (algebraMap ℚ ℂ), ← map_fockWith_id]
  rfl

omit [DecidableEq Φ] [NumberField L] in
/-- The Fock norm of a bideterminant at an embedding is `⟨β, β⟩`. -/
theorem fnorm_map_bidet (σ : L →+* ℂ)
    (rows : (ρ : Φ) → (s : Fin n) → Fin (mult (natW (lam ρ)) s) → Fin (s + 1) → Fin n) :
    fnorm (map σ (bidet L (fun ρ => natW (lam ρ)) rows)) = bnorm lam rows := by
  have h := fockWith_self (map σ (bidet L (fun ρ => natW (lam ρ)) rows))
  rw [map_bidet', ← map_bidet' (algebraMap ℚ ℂ), fockWith_star_map_rat, map_bidet'] at h
  rw [map_bidet']
  exact_mod_cast h.symm

omit [DecidableEq Φ] in
/-- The normalised Fock form on the diagonal: `⟨P, P⟩ = fnorm P/κ`. -/
theorem fock_self (P : Pol Φ n ℂ) : fock (fun ρ => natW (lam ρ)) P P = ((fnorm P / kappa lam : ℝ) : ℂ) := by
  rw [fock, fockWith_self, fockWith_hw_C]
  push_cast
  rfl

end Consts

section ExtNorm

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [DecidableEq Φ] [NumberField L] in
/-- **The Petersson norm of a form on one class**: `H_σ(ext c Q, ext c Q) = mass(c)·fnorm(σQ)/κ`. -/
theorem petAt_ext {c : DCl E n ST Λ} {Q : Pol Φ n L} (hQ : Inv τ χ lam c Q) (σ : L →+* ℂ) :
    petAt ST lam σ (ext τ χ lam c Q) (ext τ χ lam c Q) =
      ((mass c * (fnorm (map σ Q) / kappa lam) : ℝ) : ℂ) := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  rw [petAt_eq_sum, Finset.sum_eq_single c, ext_out τ χ lam hQ, fock_self]
  · push_cast
    rfl
  · intro c' _ hc'
    rw [ext_out_ne τ χ lam hc', map_zero, fock_self]
    simp [fnorm]
  · simp

omit [NumberField L] in
/-- The action keeps the Fock norm at every embedding. -/
theorem fnorm_map_actP (g : Grp E n SG Λ) (σ : L →+* ℂ) (P : Pol Φ n L) :
    fnorm (map σ (actP τ χ lam g P)) = fnorm (map σ P) := by
  have h := fockWith_map_actP τ χ lam g σ P P
  rw [fockWith_self, fockWith_self] at h
  exact_mod_cast h

omit [NumberField L] in
/-- **The average costs `|Stab|²`**: `fnorm(σ·proj P) ≤ |Stab|²·fnorm(σP)` (`fnorm_sum_le`, `fnorm_map_actP`). -/
theorem fnorm_map_proj (c : DCl E n ST Λ) (σ : L →+* ℂ) (P : Pol Φ n L) :
    fnorm (map σ (proj τ χ lam c P)) ≤ (Nat.card (stab c) : ℝ) ^ 2 * fnorm (map σ P) := by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  rw [proj_eq_sum, map_sum]
  refine (fnorm_sum_le _ _).trans (le_of_eq ?_)
  simp only [fnorm_map_actP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

end ExtNorm

/-! ## The family of integral forms (full lattice) -/

section Family

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The rows of a bideterminant of shape `natW λ`. -/
abbrev Rows := (ρ : Φ) → (s : Fin n) → Fin (mult (natW (lam ρ)) s) → Fin (s + 1) → Fin n

variable (L) in
/-- The integrality constant `z = κ_L·(ab)^e` over `L`. -/
def zL (a b : ℤ) : L :=
  fockWith (RingHom.id L) (hw L fun ρ => natW (lam ρ)) (hw L fun ρ => natW (lam ρ)) * ((a * b : ℤ) : L) ^ eDeg lam

/-- **The family of integral forms** `F_{c,β} = ext c (proj c (z·β))`: supported on the class `c`, valued in the
stabiliser average of a scaled bideterminant `z·β`, `z = κ·(ab)^e`. -/
def famF (a b : ℤ) (p : DCl E n ST Λ × Rows lam) : Fn ST Λ Φ L :=
  ext τ χ lam p.1 (proj τ χ lam p.1 (zL L lam a b • bidet L (fun ρ => natW (lam ρ)) p.2))

omit [NumberField L] in
/-- The values of a form at the representatives are invariant. -/
theorem inv_out {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) (c : DCl E n ST Λ) : Inv τ χ lam c (F c.out) :=
  fun h hh => by
    show chr χ h • rho τ lam h.1.1 (F c.out) = F c.out
    rw [← hF.2]
    exact congrArg F hh

omit [NumberField L] in
/-- The average keeps `VV(λ)`. -/
theorem proj_mem_VV (c : DCl E n ST Λ) {P : Pol Φ n L} (hP : P ∈ VV lam) : proj τ χ lam c P ∈ VV lam := by
  have := finite_stab E n ST SG Λ c
  let := Fintype.ofFinite (stab c)
  rw [proj_eq_sum]
  exact Submodule.sum_mem _ fun h _ => actP_mem_VV τ χ lam h hP

omit [DecidableEq Φ] [NumberField L] in
/-- The average commutes with scalars. -/
theorem proj_smul (c : DCl E n ST Λ) (a : L) (P : Pol Φ n L) :
    proj τ χ lam c (a • P) = a • proj τ χ lam c P := by
  simpa using proj_sum_smul τ χ lam c (Finset.univ : Finset Unit) (fun _ => a) fun _ => P

omit [NumberField L] in
/-- The family consists of forms. -/
theorem famF_mem_Forms (hlam : ∀ ρ, Antitone (lam ρ)) (a b : ℤ) (p : DCl E n ST Λ × Rows lam) :
    famF τ χ lam a b p ∈ Forms ST τ χ lam :=
  ext_mem_Forms τ χ lam (proj_mem_VV τ χ lam _ (Submodule.smul_mem _ _
    (bidet_mem_nabla (fun ρ => natW_antitone (hlam ρ)) _))) (inv_proj τ χ lam _ _)

/-- **The family is integral** when `a·O_E^n ⊆ Lsh(rep c) ⊆ b⁻¹·O_E^n` for every class: at its class, the average
of the integral `z·β` (`smul_bidet_mem_DeltaA`, `proj_mem_DeltaA`); elsewhere `0`. -/
theorem famF_mem_Mint (hlam : ∀ ρ, Antitone (lam ρ)) {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b)
    (p : DCl E n ST Λ × Rows lam) : famF τ χ lam a b p ∈ Mint ST τ χ lam := by
  refine ⟨famF_mem_Forms τ χ lam hlam a b p, fun c => ?_⟩
  by_cases hc : c = p.1
  · subst hc
    rw [famF, ext_out τ χ lam (inv_proj τ χ lam _ _)]
    exact DeltaA_subset (hab _) (proj_mem_DeltaA τ χ lam (smul_bidet_mem_DeltaA hlam (hab _) _))
  · rw [famF, ext_out_ne τ χ lam hc]
    exact DeltaA_subset (hab c) zero_mem_DeltaA

/-- **The family spans the forms**: `F = Σ_c ext c (F(rep c))` (`eq_sum_ext`), `F(rep c)` is a
combination of bideterminants (`span_bidet`), and `F(rep c) = |Stab|⁻¹·proj_c F(rep c)` (`proj_of_inv`). -/
theorem mem_span_famF (hlam : ∀ ρ, Antitone (lam ρ)) {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b)
    {F : Fn ST Λ Φ L}
    (hF : F ∈ Forms ST τ χ lam) : F ∈ Submodule.span L (Set.range (famF τ χ lam a b)) := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  rw [eq_sum_ext τ χ lam hF]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hV : F c.out ∈ Submodule.span L (Set.range (bidet L fun ρ => natW (lam ρ))) := by
    rw [span_bidet fun ρ => natW_antitone (hlam ρ)]
    exact hF.1 c.out
  obtain ⟨a', ha'⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hV
  have := finite_stab E n ST SG Λ c
  have hS : (Nat.card (stab c) : L) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hz : zL L lam a b ≠ 0 := mul_ne_zero (fock_hw_hw_ne_zero _)
    (pow_ne_zero _ (Int.cast_ne_zero.2 (mul_ne_zero (hab c).a_ne (hab c).b_ne)))
  have h1 := proj_of_inv τ χ lam (inv_out τ χ lam hF c)
  rw [← ha', proj_sum_smul] at h1
  have key : F c.out = ∑ r, ((Nat.card (stab c) : L)⁻¹ * (zL L lam a b)⁻¹ * a' r) •
      proj τ χ lam c (zL L lam a b • bidet L (fun ρ => natW (lam ρ)) r) := by
    have h2 : F c.out = (Nat.card (stab c) : L)⁻¹ • ∑ r, a' r • proj τ χ lam c (bidet L (fun ρ => natW (lam ρ)) r) := by
      rw [h1, ← ha', smul_smul, inv_mul_cancel₀ hS, one_smul]
    rw [h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [proj_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  rw [key, ext_sum_smul]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c, r), rfl⟩)

omit [DecidableEq Φ] [NumberField L] in
/-- `fnorm(σ(z·β)) = (κ·|ab|^e)²·⟨β, β⟩`. -/
theorem fnorm_map_zL (σ : L →+* ℂ) (a b : ℤ) (r : Rows lam) :
    fnorm (map σ (zL L lam a b • bidet L (fun ρ => natW (lam ρ)) r)) =
      ((kappa lam : ℝ) * ((a * b : ℤ) : ℝ) ^ eDeg lam) ^ 2 * bnorm lam r := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fnorm_smul, fnorm_map_bidet, zL, map_mul, map_kappa_L,
    map_pow, map_intCast]
  congr 1
  rw [norm_mul, norm_pow, Complex.norm_ratCast, Complex.norm_intCast, mul_pow, mul_pow, sq_abs, ← abs_pow, sq_abs]

omit [DecidableEq Φ] [NumberField L] in
/-- **The Petersson norm of the family**: `Re H_σ(F_{c,β}, F_{c,β}) ≤ |Stab(c)|·(ab)^{2e}·κ·⟨β, β⟩`:
`mass(c)·|Stab|²·(κ(ab)^e)²·⟨β, β⟩/κ` (`petAt_ext`, `fnorm_map_proj`, `fnorm_map_zL`). -/
theorem petAt_famF_le (a b : ℤ) (p : DCl E n ST Λ × Rows lam) (σ : L →+* ℂ) :
    (petAt ST lam σ (famF τ χ lam a b p) (famF τ χ lam a b p)).re ≤
      Nat.card (stab p.1) * (((a * b : ℤ) : ℝ) ^ eDeg lam) ^ 2 * (kappa lam * bnorm lam p.2 : ℝ) := by
  classical
  rw [famF, petAt_ext τ χ lam (inv_proj τ χ lam _ _), Complex.ofReal_re]
  have := finite_stab E n ST SG Λ p.1
  have hS : (0 : ℝ) < Nat.card (stab p.1) := Nat.cast_pos.2 Nat.card_pos
  have hκ : (0 : ℝ) < kappa lam := by exact_mod_cast kappa_pos lam
  have h := fnorm_map_proj τ χ lam p.1 σ (zL L lam a b • bidet L (fun ρ => natW (lam ρ)) p.2)
  rw [fnorm_map_zL] at h
  have hm : (0 : ℝ) ≤ (mass p.1 : ℝ) := by rw [mass]; positivity
  calc (mass p.1 : ℝ) * (fnorm (map σ (proj τ χ lam p.1 (zL L lam a b • bidet L (fun ρ => natW (lam ρ)) p.2))) /
        kappa lam)
      ≤ (mass p.1 : ℝ) * ((Nat.card (stab p.1) : ℝ) ^ 2 * (((kappa lam : ℝ) * ((a * b : ℤ) : ℝ) ^ eDeg lam) ^ 2 *
          bnorm lam p.2) / kappa lam) := by gcongr
    _ = _ := by
      rw [mass]
      push_cast
      field_simp

end Family

/-! ## The diamond operators -/

section Dia

omit [NumberField E] [IsCMField E] in
/-- `dia_a ∘ dia_b = dia_{ab}`. -/
theorem dia_dia (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : dia a (dia b d) = dia (a * b) d :=
  Deco.ext' rfl (fun P x _ _ => by
    simp only [dia, smul_smul, Pi.mul_apply, Units.val_mul]
    rfl) (fun _ _ _ _ => rfl)

omit [NumberField E] [IsCMField E] in
/-- `dia_1` is the identity. -/
theorem dia_one (d : Deco E n ST SG) : dia 1 d = d :=
  Deco.ext' rfl (fun P x _ _ => by simp [dia]; rfl) (fun _ _ _ _ => rfl)

/-- `dia_a ∘ dia_b = dia_{ab}` on points. -/
theorem diaPt_diaPt (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : points (E := E) (n := n) (ST := ST) Λ) :
    diaPt a (diaPt b d) = diaPt (a * b) d :=
  Subtype.ext (dia_dia a b d.1)

/-- `dia_1` is the identity on points. -/
theorem diaPt_one (d : points (E := E) (n := n) (ST := ST) Λ) : diaPt 1 d = d := Subtype.ext (dia_one d.1)

/-- `dia_a` is injective. -/
theorem diaPt_injective (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    Function.Injective (diaPt (Λ := Λ) a) := fun d d' h => by
  have := congrArg (diaPt a⁻¹) h
  rwa [diaPt_diaPt, diaPt_diaPt, inv_mul_cancel, diaPt_one, diaPt_one] at this

/-- `dia_a` commutes with `𝒢` on points. -/
theorem diaPt_smul (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (g : Grp E n SG Λ)
    (d : points (E := E) (n := n) (ST := ST) Λ) : diaPt a (g • d) = g • diaPt a d :=
  Subtype.ext (dia_smul Λ a g d.1)

omit [NumberField E] [IsCMField E] in
/-- The diamond operators keep the level-`T` kernel: `u·f_P` has the kernel of `f_P` for a unit `u`. -/
theorem kerLat_dia (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : kerLat (dia a d) = kerLat d := by
  ext x
  simp only [kerLat, Submodule.mem_inf, Submodule.mem_iInf, mem_map_subtype_ker]
  refine and_congr_right fun _ => forall_congr' fun P => exists_congr fun hx => ?_
  show (a P : 𝓞 E ⧸ P.1.asIdeal) • d.f P ⟨x, hx⟩ = 0 ↔ _
  rw [smul_eq_mul, Units.mul_right_eq_zero]

/-- **The diamond operators keep the attached lattice** (`kerLat_dia`). -/
theorem Lsh_dia (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : Lsh (dia a d) = Lsh d := by
  rw [Lsh, Lsh, kerLat_dia]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `⟨a⟩⟨b⟩ = ⟨ba⟩`. -/
theorem dOp_dOp (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (F : Fn ST Λ Φ L) :
    dOp a (dOp b F) = dOp (b * a) F := by
  funext d
  simp only [dOp, LinearMap.funLeft_apply, diaPt_diaPt]

/-- The order `N_P = |(O_E/P)^×|` of the diamond group at `P`. -/
def NP (P : ST) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)ˣ

omit [IsCMField E] in
/-- The units of a residue field are finite. -/
theorem finite_units (P : ST) : Finite (𝓞 E ⧸ P.1.asIdeal)ˣ := by
  have := finite_residue P.1
  infer_instance

open Classical in
omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `Nm_P F = Σ_u ⟨u⟩_P F`. -/
theorem Nm_apply (P : ST) [Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ] (F : Fn ST Λ Φ L) :
    Nm P F = ∑ u : (𝓞 E ⧸ P.1.asIdeal)ˣ, dOp (Pi.mulSingle P u) F := by
  rw [Nm, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

open Classical in
omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- **`Nm_P² = N_P·Nm_P`**: `Σ_u Σ_v ⟨vu⟩ = N_P·Σ_w ⟨w⟩`. -/
theorem Nm_Nm (P : ST) (F : Fn ST Λ Φ L) : Nm P (Nm P F) = (NP P : L) • Nm P F := by
  have := finite_units P
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  simp only [Nm_apply, map_sum, dOp_dOp]
  have h : ∀ x : (𝓞 E ⧸ P.1.asIdeal)ˣ, ∑ y : (𝓞 E ⧸ P.1.asIdeal)ˣ, dOp (Pi.mulSingle P x * Pi.mulSingle P y) F =
      ∑ u : (𝓞 E ⧸ P.1.asIdeal)ˣ, dOp (Pi.mulSingle P u) F := fun x =>
    Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun y => by rw [Equiv.coe_mulLeft, Pi.mulSingle_mul]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ, NP, Nat.card_eq_fintype_card,
    Nat.cast_smul_eq_nsmul]

open Classical in
omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- **The norms commute**: the diamond group is commutative. -/
theorem Nm_comm (P Q : ST) (F : Fn ST Λ Φ L) : Nm P (Nm Q F) = Nm Q (Nm P F) := by
  have := finite_units P
  have := finite_units Q
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  let := Fintype.ofFinite (𝓞 E ⧸ Q.1.asIdeal)ˣ
  simp only [Nm_apply, map_sum, dOp_dOp]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [mul_comm]

end Dia

/-! ## The diamond operators on integral forms and on the Petersson norm -/

section DiaForms

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- **The integral forms in every local basis**: `F(rep c) ∈ Δ_{Lsh(rep c)}` tested in every local basis. They lie
in `M` (`MintA_subset`) and are stable under sums, integers and the diamond operators (`dOp_mem_MintA`). -/
def MintA : Set (Fn ST Λ Φ L) :=
  {F | F ∈ Forms ST τ χ lam ∧ ∀ c : DCl E n ST Λ, F c.out ∈ DeltaA τ lam (Lsh c.rep)}

/-- `MintA ⊆ M`, local bases existing. -/
theorem MintA_subset {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b) :
    MintA τ χ lam ⊆ Mint ST τ χ lam := fun _ hF => ⟨hF.1, fun c => DeltaA_subset (hab c) (hF.2 c)⟩

/-- An integral form is integral at every point: `F(g·rep c) = actP g F(rep c)` (`actP_mem_DeltaA`). -/
theorem MintA_apply {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) (d : points (E := E) (n := n) (ST := ST) Λ) :
    F d ∈ DeltaA τ lam (Lsh d.1) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : DCl E n ST Λ, Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d = c₀ := ⟨_, rfl⟩
  obtain ⟨g, rfl⟩ := exists_smul_out hc₀
  rw [hF.1.2]
  exact actP_mem_DeltaA τ χ lam g (hF.2 _)

/-- The diamond operators keep the integral forms (`Lsh_dia`). -/
theorem dOp_mem_MintA (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) :
    dOp a F ∈ MintA τ χ lam := by
  refine ⟨dOp_mem ST τ χ lam a hF.1, fun c => ?_⟩
  have := MintA_apply τ χ lam hF (diaPt a c.out)
  rwa [show (diaPt a c.out).1 = dia a c.rep from rfl, Lsh_dia] at this

/-- Integral forms in every local basis are closed under sums. -/
theorem add_mem_MintA {F G : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) (hG : G ∈ MintA τ χ lam) :
    F + G ∈ MintA τ χ lam :=
  ⟨add_mem hF.1 hG.1, fun c => add_mem_DeltaA (hF.2 c) (hG.2 c)⟩

/-- Integral forms in every local basis are closed under integers. -/
theorem zsmul_mem_MintA (z : ℤ) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) : (z : L) • F ∈ MintA τ χ lam :=
  ⟨Submodule.smul_mem _ _ hF.1, fun c => smul_mem_DeltaA (hF.2 c) fun _ => intCast_mem _ z⟩

/-- Integral forms in every local basis are closed under finite sums. -/
theorem sum_mem_MintA {ι : Type*} (s : Finset ι) {F : ι → Fn ST Λ Φ L} (h : ∀ i ∈ s, F i ∈ MintA τ χ lam) :
    ∑ i ∈ s, F i ∈ MintA τ χ lam := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ⟨zero_mem _, fun c => zero_mem_DeltaA⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_MintA τ χ lam (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [DecidableEq Φ] [NumberField L] in
/-- The real part of the Petersson norm: `Re H_σ(G, G) = Σ_c mass(c)·fnorm(σG(rep c))/κ`. -/
theorem re_petAt [Fintype (DCl E n ST Λ)] (σ : L →+* ℂ) (G : Fn ST Λ Φ L) :
    (petAt ST lam σ G G).re = ∑ c : DCl E n ST Λ, (mass c : ℝ) * (fnorm (map σ (G c.out)) / kappa lam) := by
  rw [petAt_eq_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fock_self, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul, Complex.ofReal_re]

omit [DecidableEq Φ] [NumberField L] in
/-- **Convexity of the Petersson norm**: `Re H_σ(Σ_{i∈s} Gᵢ) ≤ |s|·Σ Re H_σ(Gᵢ)` (`fnorm_sum_le` at each class). -/
theorem re_petAt_sum_le (σ : L →+* ℂ) {ι : Type*} (s : Finset ι) (G : ι → Fn ST Λ Φ L) :
    (petAt ST lam σ (∑ i ∈ s, G i) (∑ i ∈ s, G i)).re ≤ s.card * ∑ i ∈ s, (petAt ST lam σ (G i) (G i)).re := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  have hκ : (0 : ℝ) < kappa lam := by exact_mod_cast kappa_pos lam
  have hm : ∀ c : DCl E n ST Λ, (0 : ℝ) ≤ mass c := fun c => by rw [mass]; positivity
  simp only [re_petAt]
  calc ∑ c : DCl E n ST Λ, (mass c : ℝ) * (fnorm (map σ ((∑ i ∈ s, G i) c.out)) / kappa lam)
      ≤ ∑ c : DCl E n ST Λ, (mass c : ℝ) * ((s.card * ∑ i ∈ s, fnorm (map σ (G i c.out))) / kappa lam) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (by rw [Finset.sum_apply, map_sum]; exact fnorm_sum_le _ _) hκ.le) (hm c)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring

omit [DecidableEq Φ] [NumberField L] in
/-- `Re H_σ(−G, −G) = Re H_σ(G, G)`. -/
theorem re_petAt_neg [Fintype (DCl E n ST Λ)] (σ : L →+* ℂ) (G : Fn ST Λ Φ L) :
    (petAt ST lam σ (-G) (-G)).re = (petAt ST lam σ G G).re := by
  simp only [re_petAt, Pi.neg_apply, map_neg]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show -(map σ (G c.out)) = (-1 : ℂ) • map σ (G c.out) by simp, fnorm_smul]
  simp

/-- The stabilisers of `x` and `dia_a x` agree, as `dia_a` commutes with `𝒢` and is injective. -/
theorem stabilizer_diaPt (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (x : points (E := E) (n := n) (ST := ST) Λ) :
    MulAction.stabilizer (Grp E n SG Λ) (diaPt a x) = MulAction.stabilizer (Grp E n SG Λ) x := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  rw [← diaPt_smul, (diaPt_injective a).eq_iff]

omit [NumberField L] in
/-- **The diamond operators keep the Petersson norm**: they permute the classes, keeping the mass weights
(`stabilizer_diaPt`), and the values move by `actP`, which is Fock-unitary (`fnorm_map_actP`). -/
theorem re_petAt_dOp (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam)
    (σ : L →+* ℂ) : (petAt ST lam σ (dOp a F) (dOp a F)).re = (petAt ST lam σ F F).re := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  set φ : DCl E n ST Λ → DCl E n ST Λ := fun c => Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (diaPt a c.out)
  have hφ : Function.Bijective φ := by
    refine Finite.injective_iff_bijective.1 fun c c' h => ?_
    obtain ⟨g, hg⟩ := Quotient.exact h
    change g • diaPt a c'.out = diaPt a c.out at hg
    rw [← diaPt_smul, (diaPt_injective a).eq_iff] at hg
    rw [← Quotient.out_eq c, ← Quotient.out_eq c', ← hg]
    exact Quotient.sound ⟨g, rfl⟩
  have hterm : ∀ c, (mass c : ℝ) * (fnorm (map σ (dOp a F c.out)) / kappa lam) =
      (mass (φ c) : ℝ) * (fnorm (map σ (F (φ c).out)) / kappa lam) := fun c => by
    obtain ⟨g, hg⟩ := exists_smul_out (c := φ c) rfl
    have h1 : dOp a F c.out = actP τ χ lam g (F (φ c).out) := by
      show F (diaPt a c.out) = _
      rw [← hg, hF.2]
      rfl
    have h2 : mass (φ c) = mass c := by
      rw [mass_mk, mass, stab, stabilizer_diaPt]
    rw [h1, fnorm_map_actP, h2]
  rw [re_petAt, re_petAt, Finset.sum_congr rfl fun c _ => hterm c]
  exact Function.Bijective.sum_comp hφ fun c => (mass c : ℝ) * (fnorm (map σ (F c.out)) / kappa lam)

end DiaForms

/-! ## The projection onto the cut -/

section CutOp

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

variable (Λ Φ L) in
/-- The operator `T_P = N_P − Nm_P`: it maps into `ker Nm_P` (`Nm_Tc`) and is `N_P` there (`Tc_of_ker`). -/
def Tc (P : ST) : Module.End L (Fn ST Λ Φ L) := (NP P : L) • LinearMap.id - Nm P

variable (Λ Φ L) in
/-- The product `T_{P₁}⋯T_{P_k}` along a list of places. -/
def Tl (l : List ST) : Module.End L (Fn ST Λ Φ L) := (l.map (Tc Λ Φ L)).prod

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
theorem Tc_apply (P : ST) (F : Fn ST Λ Φ L) : Tc Λ Φ L P F = (NP P : L) • F - Nm P F := rfl

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `Nm_P T_P = N_P Nm_P − Nm_P² = 0`. -/
theorem Nm_Tc (P : ST) (F : Fn ST Λ Φ L) : Nm P (Tc Λ Φ L P F) = 0 := by
  rw [Tc_apply, map_sub, map_smul, Nm_Nm, sub_self]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `Nm_Q` commutes with `T_P`. -/
theorem Nm_Tc_comm (P Q : ST) (F : Fn ST Λ Φ L) : Nm Q (Tc Λ Φ L P F) = Tc Λ Φ L P (Nm Q F) := by
  rw [Tc_apply, Tc_apply, map_sub, map_smul, Nm_comm]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `T_P = N_P` on `ker Nm_P`. -/
theorem Tc_of_ker {P : ST} {F : Fn ST Λ Φ L} (h : Nm P F = 0) : Tc Λ Φ L P F = (NP P : L) • F := by
  rw [Tc_apply, h, sub_zero]

open Classical in
omit [NumberField L] in
/-- `Nm_P` keeps the forms. -/
theorem Nm_mem_Forms (P : ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) : Nm P F ∈ Forms ST τ χ lam := by
  have := finite_units P
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  rw [Nm_apply]
  exact Submodule.sum_mem _ fun u _ => dOp_mem ST τ χ lam _ hF

omit [NumberField L] in
/-- `T_P` keeps the forms. -/
theorem Tc_mem_Forms (P : ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    Tc Λ Φ L P F ∈ Forms ST τ χ lam :=
  sub_mem (Submodule.smul_mem _ _ hF) (Nm_mem_Forms τ χ lam P hF)

open Classical in
/-- `T_P` keeps the integral forms (`dOp_mem_MintA`). -/
theorem Tc_mem_MintA (P : ST) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) : Tc Λ Φ L P F ∈ MintA τ χ lam := by
  have := finite_units P
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  rw [Tc_apply, Nm_apply, sub_eq_add_neg, ← neg_one_smul L (∑ u, _)]
  refine add_mem_MintA τ χ lam (by exact_mod_cast zsmul_mem_MintA τ χ lam (NP P) hF) ?_
  exact_mod_cast zsmul_mem_MintA τ χ lam (-1) (sum_mem_MintA τ χ lam _ fun u _ => dOp_mem_MintA τ χ lam _ hF)

omit [DecidableEq Φ] [NumberField L] in
/-- `Re H_σ(G + H) ≤ 2(Re H_σ(G) + Re H_σ(H))`. -/
theorem re_petAt_add_le (σ : L →+* ℂ) (G H : Fn ST Λ Φ L) :
    (petAt ST lam σ (G + H) (G + H)).re ≤ 2 * ((petAt ST lam σ G G).re + (petAt ST lam σ H H).re) := by
  have h := re_petAt_sum_le lam σ (Finset.univ : Finset (Fin 2)) ![G, H]
  simpa [Fin.sum_univ_two] using h

open Classical in
omit [NumberField L] in
/-- **`T_P` costs `(2N_P)²`**: `T_P F = Σ_u (F − ⟨u⟩F)`, each term of norm at most `4·H(F)` (`re_petAt_dOp`), and
convexity over the `N_P` terms. -/
theorem re_petAt_Tc_le (P : ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) (σ : L →+* ℂ) :
    (petAt ST lam σ (Tc Λ Φ L P F) (Tc Λ Φ L P F)).re ≤ (2 * NP P : ℝ) ^ 2 * (petAt ST lam σ F F).re := by
  have := finite_units P
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  have hT : Tc Λ Φ L P F = ∑ u : (𝓞 E ⧸ P.1.asIdeal)ˣ, (F + -dOp (Pi.mulSingle P u) F) := by
    rw [Tc_apply, Nm_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      NP, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul L, sub_eq_add_neg]
  have hu : ∀ u : (𝓞 E ⧸ P.1.asIdeal)ˣ, (petAt ST lam σ (F + -dOp (Pi.mulSingle P u) F)
      (F + -dOp (Pi.mulSingle P u) F)).re ≤ 4 * (petAt ST lam σ F F).re := fun u => by
    refine (re_petAt_add_le lam σ _ _).trans (le_of_eq ?_)
    rw [re_petAt_neg, re_petAt_dOp τ χ lam _ hF]
    ring
  rw [hT]
  refine (re_petAt_sum_le lam σ _ _).trans ?_
  calc (Finset.univ.card : ℝ) * ∑ u : (𝓞 E ⧸ P.1.asIdeal)ˣ, (petAt ST lam σ (F + -dOp (Pi.mulSingle P u) F)
        (F + -dOp (Pi.mulSingle P u) F)).re
      ≤ (Finset.univ.card : ℝ) * ∑ _u : (𝓞 E ⧸ P.1.asIdeal)ˣ, 4 * (petAt ST lam σ F F).re :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => hu u) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, NP, Nat.card_eq_fintype_card]
      ring

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
theorem Tl_cons (P : ST) (l : List ST) (F : Fn ST Λ Φ L) : Tl Λ Φ L (P :: l) F = Tc Λ Φ L P (Tl Λ Φ L l F) := by
  simp [Tl, Module.End.mul_apply]

omit [NumberField L] in
/-- `T_l` keeps the forms. -/
theorem Tl_mem_Forms (l : List ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    Tl Λ Φ L l F ∈ Forms ST τ χ lam := by
  induction l with
  | nil => simpa [Tl] using hF
  | cons P l ih => rw [Tl_cons]; exact Tc_mem_Forms τ χ lam P ih

/-- `T_l` keeps the integral forms. -/
theorem Tl_mem_MintA (l : List ST) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) : Tl Λ Φ L l F ∈ MintA τ χ lam := by
  induction l with
  | nil => simpa [Tl] using hF
  | cons P l ih => rw [Tl_cons]; exact Tc_mem_MintA τ χ lam P ih

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `T_l` maps into `ker Nm_P` for `P ∈ l`. -/
theorem Nm_Tl {l : List ST} {P : ST} (hP : P ∈ l) (F : Fn ST Λ Φ L) : Nm P (Tl Λ Φ L l F) = 0 := by
  induction l with
  | nil => simp at hP
  | cons Q l ih =>
    rw [Tl_cons]
    by_cases h : P = Q
    · subst h
      exact Nm_Tc P _
    · rw [Nm_Tc_comm, ih (List.mem_of_ne_of_mem h hP), map_zero]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `T_l = Π_{P∈l} N_P` on `⋂_{P∈l} ker Nm_P`. -/
theorem Tl_of_ker {l : List ST} {F : Fn ST Λ Φ L} (h : ∀ P ∈ l, Nm P F = 0) :
    Tl Λ Φ L l F = (l.map fun P => (NP P : L)).prod • F := by
  induction l with
  | nil => simp [Tl]
  | cons Q l ih =>
    rw [Tl_cons, ih fun P hP => h P (List.mem_cons_of_mem Q hP), map_smul,
      Tc_of_ker (h Q (List.mem_cons_self ..)), smul_smul, List.map_cons, List.prod_cons, mul_comm]

omit [NumberField L] in
/-- **`T_l` costs `Π_{P∈l} (2N_P)²`** in the Petersson norm. -/
theorem re_petAt_Tl_le (l : List ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) (σ : L →+* ℂ) :
    (petAt ST lam σ (Tl Λ Φ L l F) (Tl Λ Φ L l F)).re ≤
      (l.map fun P => (2 * NP P : ℝ) ^ 2).prod * (petAt ST lam σ F F).re := by
  induction l with
  | nil => simp [Tl]
  | cons P l ih =>
    rw [Tl_cons, List.map_cons, List.prod_cons, mul_assoc]
    exact (re_petAt_Tc_le τ χ lam P (Tl_mem_Forms τ χ lam l hF) σ).trans
      (mul_le_mul_of_nonneg_left ih (sq_nonneg _))

end CutOp

/-! ## The slope of the source from a spanning family of integral forms -/

section Source

open scoped Matrix Classical

attribute [local instance] InnerProductSpace.complexToReal

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ) [FiniteDimensional L (Vω ST τ χ lam)]

omit [NumberField L] in
/-- **The Gram matrix computes the Petersson norm**: for `F ∈ V_ω` with coordinates `x`,
`σ(x)ᴴ·gram_σ·σ(x) = H_σ(F, F)` (`petAt_sum_smul`). -/
theorem dot_gram (σ : L →+* ℂ) (F : Vω ST τ χ lam) :
    star (fun i => σ (coords ST τ χ lam F i)) ⬝ᵥ (gram ST τ χ lam σ *ᵥ fun i => σ (coords ST τ χ lam F i)) =
      petAt ST lam σ (F : Fn ST Λ Φ L) F := by
  set b := Module.finBasis L (Vω ST τ χ lam)
  have hF : (F : Fn ST Λ Φ L) = ∑ i, coords ST τ χ lam F i • (b i : Fn ST Λ Φ L) := by
    calc (F : Fn ST Λ Φ L) = ((∑ i, b.equivFun F i • b i : Vω ST τ χ lam) : Fn ST Λ Φ L) := by
          rw [b.sum_equivFun]
      _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
  rw [hF, petAt_sum_smul]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, gram, Hω]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [(Mlat ST τ χ lam).IsLattice L]

/-- **The norm in the source** of the coordinates of a cut form is its Petersson norm summed over the complex
places: `‖ψ(coords F)‖² = Σ_v Re H_{σ_v}(F, F)`. -/
theorem norm_ψ_source_sq (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef)
    (F : Vω ST τ χ lam) :
    ‖(source ST τ χ lam hpos).ψ (coords ST τ χ lam F)‖ ^ 2 =
      ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (F : Fn ST Λ Φ L) F).re := by
  rw [KLattice.norm_ψ_sq]
  exact Finset.sum_congr rfl fun v _ => by rw [source_G, dot_gram]

/-- **The slope of the source from a spanning family of integral forms**: if integral cut forms `F_i ∈ M_ω` span
`V_ω` over `L` and `Σ_v Re H_{σ_v}(F_i, F_i) ≤ B` for every `i`, then `μ(source) ≥ −c_L − ½ log B`
(`KLattice.slope_ge_of_span`, `norm_ψ_source_sq`). -/
theorem slope_source_ge_of_span [IsTotallyComplex L] [Nonempty (Idx ST τ χ lam)]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) {I : Type*}
    (F : I → Vω ST τ χ lam) (hF : Submodule.span L (Set.range F) = ⊤)
    (hFM : ∀ i, (F i : Fn ST Λ Φ L) ∈ Mω ST τ χ lam) {B : ℝ}
    (hB : ∀ i, ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (F i : Fn ST Λ Φ L) (F i)).re ≤ B) :
    -KLattice.cK L - Real.log B / 2 ≤ (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.deg ⊤ /
      (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.rk ⊤ := by
  refine KLattice.slope_ge_of_span _ (fun i => coords ST τ χ lam (F i)) ?_ (fun i => ?_) fun i => ?_
  · rw [Set.range_comp' (coords ST τ χ lam) F, ← LinearEquiv.coe_toLinearMap, Submodule.span_image, hF,
      Submodule.map_top, LinearEquiv.range]
  · exact Submodule.subset_span ⟨F i, hFM i, rfl⟩
  · rw [norm_ψ_source_sq]
    exact hB i

end Source

/-! ## (F) for the full lattice of integral forms -/

section Full

open scoped Matrix Classical

attribute [local instance] InnerProductSpace.complexToReal

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [NumberField L] in
/-- A family in a subspace `W` whose span in the ambient space contains `W` spans `W`. -/
theorem span_eq_top_of_le {V : Type*} [AddCommGroup V] [Module L V] {W : Submodule L V} {I : Type*} (f : I → W)
    (h : ∀ x ∈ W, x ∈ Submodule.span L (Set.range fun i => (f i : V))) : Submodule.span L (Set.range f) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx := h x x.2
  rw [show (Set.range fun i => (f i : V)) = W.subtype '' Set.range f by rw [← Set.range_comp]; rfl,
    Submodule.span_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [Subtype.ext hyx] at hy

/-- The largest stabiliser `max_c |Stab(c)|`. -/
def stabMax : ℝ := ⨆ c : DCl E n ST Λ, (Nat.card (stab c) : ℝ)

/-- `|Stab(c)| ≤ max`. -/
theorem card_stab_le (c : DCl E n ST Λ) [Finite (DCl E n ST Λ)] : (Nat.card (stab c) : ℝ) ≤ stabMax ST (Λ := Λ) :=
  le_ciSup (f := fun c : DCl E n ST Λ => (Nat.card (stab c) : ℝ)) (Set.finite_range _).bddAbove c

variable (L) in
/-- **The bound on the full lattice**: `B_F = n_∞·max|Stab|·(ab)^{2e}·κ·max⟨β, β⟩`, `n_∞` the number of complex
places of `L`. -/
def bF (a b : ℤ) : ℝ :=
  Fintype.card (HermitianLattice.Pl L) * stabMax ST (Λ := Λ) * (((a * b : ℤ) : ℝ) ^ eDeg lam) ^ 2 *
    (kappa lam * bmax lam)

omit [DecidableEq Φ] [NumberField L] in
/-- Each form of the family has Petersson norm, summed over the complex places, at most `B_F`. -/
theorem sum_petAt_famF_le [NumberField L] (a b : ℤ) (p : DCl E n ST Λ × Rows lam) :
    ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (famF τ χ lam a b p) (famF τ χ lam a b p)).re ≤
      bF ST L lam (Λ := Λ) a b := by
  have := finite_DCl E n ST SG Λ
  have hκ : (0 : ℝ) ≤ kappa lam := by exact_mod_cast (kappa_pos lam).le
  have hb : (bnorm lam p.2 : ℝ) ≤ bmax lam := bnorm_le_bmax lam p.2
  have hb0 : (0 : ℝ) ≤ bnorm lam p.2 := by
    have := fockWith_self (map (algebraMap ℚ ℂ) (bidet ℚ (fun ρ => natW (lam ρ)) p.2))
    rw [fockWith_star_map_rat] at this
    have h2 : ((bnorm lam p.2 : ℚ) : ℝ) = fnorm (map (algebraMap ℚ ℂ) (bidet ℚ (fun ρ => natW (lam ρ)) p.2)) := by
      exact_mod_cast this
    rw [h2]
    exact fnorm_nonneg _
  calc ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (famF τ χ lam a b p) (famF τ χ lam a b p)).re
      ≤ ∑ _v : HermitianLattice.Pl L, stabMax ST (Λ := Λ) * (((a * b : ℤ) : ℝ) ^ eDeg lam) ^ 2 *
          (kappa lam * bmax lam) := Finset.sum_le_sum fun v _ => (petAt_famF_le τ χ lam a b p _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_right (card_stab_le ST p.1) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hb hκ) (mul_nonneg hκ hb0)
          (mul_nonneg ((Nat.cast_nonneg _).trans (card_stab_le ST p.1)) (sq_nonneg _)))
    _ = bF ST L lam (Λ := Λ) a b := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, bF]
      ring

/-- **(F) for the full lattice** (no level-`T` places, `ST = ∅`, where the cut is all of the forms): if every
attached lattice lies between `a·O_E^n` and `b⁻¹·O_E^n`, the source has slope
`μ ≥ −c_L − ½ log B_F`, `B_F = n_∞·max_c|Stab(c)|·(ab)^{2e}·κ·max_β⟨β, β⟩` (`bF`). The family `famF` is integral
(`famF_mem_Mint`), spans (`mem_span_famF`) and has Petersson norms at most `B_F` (`sum_petAt_famF_le`). -/
theorem slope_source_ge_full [IsEmpty ST] [IsTotallyComplex L] [FiniteDimensional L (Vω ST τ χ lam)]
    [(Mlat ST τ χ lam).IsLattice L] [Nonempty (Idx ST τ χ lam)]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) (hlam : ∀ ρ, Antitone (lam ρ))
    {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b) :
    -KLattice.cK L - Real.log (bF ST L lam (Λ := Λ) a b) / 2 ≤
      (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.deg ⊤ /
        (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.rk ⊤ := by
  have hV : ∀ F, F ∈ Forms ST τ χ lam → F ∈ Vω ST τ χ lam := fun F hF =>
    Submodule.mem_inf.2 ⟨hF, by simp⟩
  let F : DCl E n ST Λ × Rows lam → Vω ST τ χ lam := fun p =>
    ⟨famF τ χ lam a b p, hV _ (famF_mem_Forms τ χ lam hlam a b p)⟩
  refine slope_source_ge_of_span ST τ χ lam hpos F ?_ (fun p => ⟨famF_mem_Mint τ χ lam hlam hab p, (F p).2⟩)
    fun p => sum_petAt_famF_le ST τ χ lam a b p
  exact span_eq_top_of_le F fun x hx => mem_span_famF τ χ lam hlam hab (Submodule.mem_inf.1 hx).1

end Full

/-! ## (F) for the cut: the source -/

section Main

open scoped Matrix Classical

attribute [local instance] InnerProductSpace.complexToReal

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The family is integral in every local basis. -/
theorem famF_mem_MintA (hlam : ∀ ρ, Antitone (lam ρ)) {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b)
    (p : DCl E n ST Λ × Rows lam) : famF τ χ lam a b p ∈ MintA τ χ lam := by
  refine ⟨famF_mem_Forms τ χ lam hlam a b p, fun c => ?_⟩
  by_cases hc : c = p.1
  · subst hc
    rw [famF, ext_out τ χ lam (inv_proj τ χ lam _ _)]
    exact proj_mem_DeltaA τ χ lam (smul_bidet_mem_DeltaA hlam (hab _) _)
  · rw [famF, ext_out_ne τ χ lam hc]
    exact zero_mem_DeltaA

/-- **The cut family** `G_{c,β} = Π_{P∈ST} T_P F_{c,β}`, `T_P = N_P − Nm_P`. -/
def famG (a b : ℤ) (p : DCl E n ST Λ × Rows lam) : Fn ST Λ Φ L :=
  Tl Λ Φ L (Finset.univ : Finset ST).toList (famF τ χ lam a b p)

/-- **The level-`T` denominator** `D_T = Π_{P∈ST} (2N_P)²`, `N_P = |(O_E/P)^×|`: the cost of the projection onto the
cut. -/
def DT : ℝ := ∏ P : ST, (2 * NP P : ℝ) ^ 2

variable (L) in
/-- **The bound on the source**: `B = D_T·B_F` (`bF` for the full lattice). -/
def bCut (a b : ℤ) : ℝ := DT ST * bF ST L lam (Λ := Λ) a b

omit [NumberField L] in
/-- The cut family lies in the cut `V_ω`. -/
theorem famG_mem_Vω (hlam : ∀ ρ, Antitone (lam ρ)) (a b : ℤ) (p : DCl E n ST Λ × Rows lam) :
    famG ST τ χ lam a b p ∈ Vω ST τ χ lam :=
  Submodule.mem_inf.2 ⟨Tl_mem_Forms τ χ lam _ (famF_mem_Forms τ χ lam hlam a b p),
    (Submodule.mem_iInf _).2 fun P => LinearMap.mem_ker.2 (Nm_Tl (Finset.mem_toList.2 (Finset.mem_univ P)) _)⟩

/-- **The cut family is integral**: `T_P` keeps the integral forms (`Tc_mem_MintA`). -/
theorem famG_mem_Mω (hlam : ∀ ρ, Antitone (lam ρ)) {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b)
    (p : DCl E n ST Λ × Rows lam) : famG ST τ χ lam a b p ∈ Mω ST τ χ lam :=
  ⟨MintA_subset τ χ lam hab (Tl_mem_MintA τ χ lam _ (famF_mem_MintA ST τ χ lam hlam hab p)),
    famG_mem_Vω ST τ χ lam hlam a b p⟩

/-- **The cut family spans the cut**: on `V_ω`, `Π_P T_P = Π_P N_P ≠ 0` (`Tl_of_ker`), and the full family spans
the forms (`mem_span_famF`). -/
theorem mem_span_famG (hlam : ∀ ρ, Antitone (lam ρ)) {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b)
    {X : Fn ST Λ Φ L} (hX : X ∈ Vω ST τ χ lam) : X ∈ Submodule.span L (Set.range (famG ST τ χ lam a b)) := by
  have hXF := (Submodule.mem_inf.1 hX).1
  have hker : ∀ P ∈ (Finset.univ : Finset ST).toList, Nm P X = 0 := fun P _ =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hX).2 P)
  have h1 := Submodule.apply_mem_span_image_of_mem_span (Tl Λ Φ L (Finset.univ : Finset ST).toList)
    (mem_span_famF τ χ lam hlam hab hXF)
  rw [← Set.range_comp, Tl_of_ker hker] at h1
  have hc : ((Finset.univ : Finset ST).toList.map fun P => (NP P : L)).prod ≠ 0 := by
    rw [Finset.prod_map_toList, Finset.prod_ne_zero_iff]
    intro P _ h
    have := finite_units P
    exact Nat.card_pos.ne' (Nat.cast_eq_zero.1 h)
  have := Submodule.smul_mem _ (((Finset.univ : Finset ST).toList.map fun P => (NP P : L)).prod)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- The Petersson norms of the cut family, summed over the places, are at most `B = D_T·B_F`. -/
theorem sum_petAt_famG_le (hlam : ∀ ρ, Antitone (lam ρ)) (a b : ℤ) (p : DCl E n ST Λ × Rows lam) :
    ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (famG ST τ χ lam a b p) (famG ST τ χ lam a b p)).re ≤
      bCut ST L lam (Λ := Λ) a b := by
  have hD : (0 : ℝ) ≤ DT ST := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hl : ((Finset.univ : Finset ST).toList.map fun P => (2 * NP P : ℝ) ^ 2).prod = DT ST := by
    rw [Finset.prod_map_toList]
    rfl
  calc ∑ v : HermitianLattice.Pl L, (petAt ST lam v.1.embedding (famG ST τ χ lam a b p)
        (famG ST τ χ lam a b p)).re
      ≤ ∑ v : HermitianLattice.Pl L, DT ST * (petAt ST lam v.1.embedding (famF τ χ lam a b p)
          (famF τ χ lam a b p)).re := Finset.sum_le_sum fun v _ => by
        rw [← hl]
        exact re_petAt_Tl_le τ χ lam _ (famF_mem_Forms τ χ lam hlam a b p) _
    _ ≤ DT ST * bF ST L lam (Λ := Λ) a b := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_petAt_famF_le ST τ χ lam a b p) hD

/-- **(F), the slope lower bound for the source** `(M_ω, H_ω)` (`HermForms.source`): if every attached lattice lies
between `a·O_E^n` and `b⁻¹·O_E^n`, then `μ(source) ≥ −c_F` with
`c_F = c_L + ½·log B`, `B = D_T·n_∞·max_c|Stab(c)|·(ab)^{2e}·κ·max_β⟨β, β⟩` (`bCut`), i.e.
`c_F = c_L + ½ log n_∞ + ½ max_c log|Stab(c)| + e·log|ab| + ½ log κ + ½ log max⟨β, β⟩ + Σ_{P∈ST} log(2N_P)`.
The cut family `famG` is integral (`famG_mem_Mω`), spans the cut (`mem_span_famG`) and has Petersson norms at most
`B` (`sum_petAt_famG_le`); the engine is `slope_source_ge_of_span`. -/
theorem slope_source_ge [IsTotallyComplex L] [FiniteDimensional L (Vω ST τ χ lam)]
    [(Mlat ST τ χ lam).IsLattice L] [Nonempty (Idx ST τ χ lam)]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) (hlam : ∀ ρ, Antitone (lam ρ))
    {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b) :
    -KLattice.cK L - Real.log (bCut ST L lam (Λ := Λ) a b) / 2 ≤
      (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.deg ⊤ /
        (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.rk ⊤ :=
  slope_source_ge_of_span ST τ χ lam hpos (fun p => ⟨famG ST τ χ lam a b p, famG_mem_Vω ST τ χ lam hlam a b p⟩)
    (span_eq_top_of_le _ fun _ hx => mem_span_famG ST τ χ lam hlam hab hx) (fun p => famG_mem_Mω ST τ χ lam hlam hab p)
    fun p => sum_petAt_famG_le ST τ χ lam hlam a b p

end Main

/-! ## Uniform comparison constants -/

section Uniform

attribute [local instance] InnerProductSpace.complexToReal

omit [NumberField E] [IsCMField E] in
/-- A comparison `a·O_E^n ⊆ N ⊆ b⁻¹O_E^n` survives multiplying `a` and `b` by nonzero integers. -/
theorem Sand.mul {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b) {k k' : ℤ} (hk : k ≠ 0)
    (hk' : k' ≠ 0) : Sand N (a * k) (b * k') where
  a_ne := mul_ne_zero h.a_ne hk
  b_ne := mul_ne_zero h.b_ne hk'
  single_mem i := by
    have := int_smul_mem (h.single_mem i) k
    rwa [smul_smul, ← Int.cast_mul, mul_comm k] at this
  int x hx i := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h.int x hx i)
    refine Submodule.mem_one.2 ⟨(k' : 𝓞 E) * r, ?_⟩
    rw [map_mul, hr, map_intCast]
    push_cast
    ring

/-- **Uniform comparison constants exist**: one pair `a, b` of nonzero integers with
`a·O_E^n ⊆ Lsh(rep c) ⊆ b⁻¹O_E^n` for every class (`exists_sand_Lsh` for each of the finitely many classes, and
the products). -/
theorem exists_sand_uniform : ∃ a b : ℤ, ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b := by
  classical
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  choose a b hab using fun c : DCl E n ST Λ =>
    exists_sand_Lsh (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  refine ⟨∏ c, a c, ∏ c, b c, fun c => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ b (Finset.mem_univ c)]
  exact (hab c).mul (Finset.prod_ne_zero_iff.2 fun c' _ => (hab c').a_ne)
    (Finset.prod_ne_zero_iff.2 fun c' _ => (hab c').b_ne)

open scoped Classical in
/-- **(F) for the source, unconditionally**: for some uniform comparison constants `a, b`
(`exists_sand_uniform`), `μ(source) ≥ −c_L − ½ log B` with `B = bCut a b` (`slope_source_ge`). -/
theorem exists_slope_source_ge [IsTotallyComplex L] (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)
    [FiniteDimensional L (Vω ST τ χ lam)] [(Mlat ST τ χ lam).IsLattice L] [Nonempty (Idx ST τ χ lam)]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) (hlam : ∀ ρ, Antitone (lam ρ)) :
    ∃ a b : ℤ, (∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b) ∧
      -KLattice.cK L - Real.log (bCut ST L lam (Λ := Λ) a b) / 2 ≤
        (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.deg ⊤ /
          (source ST τ χ lam hpos).toPlaceLattice.slopeLattice.rk ⊤ := by
  obtain ⟨a, b, hab⟩ := exists_sand_uniform (E := E) (n := n) (ST := ST) (Λ := Λ)
  exact ⟨a, b, hab, slope_source_ge ST τ χ lam hpos hlam hab⟩

end Uniform

end

end HermForms
