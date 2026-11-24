import Mathlib
import HermitianLattice

/-!
# The frame condition at one place

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "Next"): the frame condition at one
complex place, and the rank spreading (RS) of the frame inequality (`SlopeFrame.Frame.RankSpread`) that it gives.

**The setting** (`FrameAtPlace.FrameCond`). Maps `B_ω : V_ω → W` between finite-dimensional inner product spaces, over
`ℝ` or `ℂ`, with `d_ω = dim V_ω` and `D = dim W`. Put `Q = Σ_ω B_ω B_ω*` (`frameOp`) and `X_ω = B_ω*B_ω − 1`
(`defect`), which are symmetric.
* **(I)**, near-isometry: `Σ_ω ‖X_ω‖²_HS ≤ e·Σ_ω d_ω`, with `e < 1`.
* **(T)**, near-tightness: `D·tr Q² ≤ (1 + η)(tr Q)²`, with `η ≥ 0`.

Weights `γ_ω > 0`, as in `‖γ_ω B_ω*B_ω − 1‖_HS` and `Q = Σ_ω γ_ω B_ω B_ω*`, are absorbed by replacing `B_ω` with
`√γ_ω B_ω`.

**The theorem** (`FrameAtPlace.FrameCond.codim_le`). Let subspaces `N_ω ≤ V_ω` have total codimension at most
`ε'·Σ_ω d_ω`, with `0 ≤ ε' ≤ 1`. Then `S = Σ_ω B_ω(N_ω)` has codimension at most `(η + 2(√e + ε')/(1 − √e))·D`.
Take orthonormal bases `u_j` of `S^⊥`, `c` of them, and `g_{ω,i}` of `N_ω^⊥`, `k = Σ_ω k_ω` of them.
1. **Above.** `B_ω* u_j` lies in `N_ω^⊥`, so `Σ_j ⟪u_j, Q u_j⟫ = Σ_{ω,j} ‖B_ω* u_j‖² = Σ_{ω,i,j} |⟪u_j, B_ω g_{ω,i}⟫|²`.
   Bessel's inequality bounds it by `Σ_{ω,i} ‖B_ω g_{ω,i}‖² ≤ Σ_{ω,i} (1 + ‖X_ω g_{ω,i}‖)`.
2. **Partial traces.** For symmetric `T` and orthonormal `v_i`, `Σ_i ‖T v_i‖² ≤ tr T²` (`sum_norm_sq_le`). With
   Cauchy–Schwarz over all `(ω, i)` (`sq_sum_le`), the bound above is `k + √k·√(eΣd) ≤ (ε' + √e)Σd`.
3. **The trace.** `tr Q = Σ_ω tr B_ω*B_ω = Σd + Σ_ω tr X_ω ≥ (1 − √e)Σd`, in the same way.
4. **Below.** With `m = tr Q/D`, `Σ_j ⟪u_j, Q u_j⟫ ≥ c·m − √c·‖Q − m‖_HS`. And (T) is `D·‖Q − m‖²_HS ≤ η(tr Q)²`.
5. **Combine** (`arith`). With `c = tD`, `t − √(tη) ≤ (ε' + √e)/(1 − √e)`, and `√(tη) ≤ (t + η)/2`.

**The padded target** (`FrameAtPlace.FrameCond.codim_le_padded`). If `(1 − δ)·D ≤ dim C`, with `δ < 1`, then
`dim C − dim S ≤ (1 − δ)⁻¹(η + 2(√e + ε')/(1 − √e))·dim C`. When `S ≤ C`, this bounds the codimension of `S` in `C`.

**Frames** (`PlaceLattice.spread_of_frameCond`). Take a frame of lattices with places (`PlaceLattice.frame`), all with
as many places as the target. Pick a place `v_ω` of each source and a place `w` of the target. The components of the
maps there are `π_w ∘ φ_ω` on `V_{v_ω}` (`PlaceLattice.component`). Suppose:
* the sources have full rank;
* multiples `c_ω` of the components meet the frame condition;
* the part of `span Λ_Y` at `w` has at least `1 − δ` of the dimension there.

Then the frame spreads ranks (`SlopeFrame.Frame.RankSpread`), with `α = (1 − δ)⁻¹(η + 2√e/(1 − √e))` and
`β = (1 − δ)⁻¹·2/(1 − √e)`.
* **Ranks at one place.** As spans are balanced, `rk a = |P|·dim (span a ∩ V_v)` (`PlaceLattice.rk_eq_card_mul`). So
  the coranks of sources and target are `|P|` times codimensions at the places.
* **Images.** The span of the sum `M` of the images contains each `φ_ω(span a_ω)`. Being balanced, it contains the parts
  of its vectors at `w` (`PlaceLattice.Balanced.starProjection_mem`). So its part at `w` contains the sum of the
  `π_w φ_ω(span a_ω ∩ V_{v_ω})`.

No `O_K`-linearity is used: the components are projections.

**Complex-linear maps** (`FrameAtPlace.FrameCond.restrictScalars`). Complex-linear maps that meet the frame condition
over `ℂ` meet it over `ℝ` with the same `e` and `η`. Real dimensions are twice the complex ones, real traces are twice
the real parts of the complex ones (`FrameAtPlace.trace_restrictScalars`), and adjoints commute with restricting
scalars. So both sides of (I) double, and both sides of (T) quadruple.

For hermitian frames (`HermitianLattice.spread_of_frameCond`) the places are the complex places of `K`, and the parts
at them are complex subspaces taken as real ones. The maps commute with `O_K`, so they send `V_v` into `W_v`
complex-linearly, and the components are these restrictions. The theorem takes the frame condition over `ℂ` for them,
as the archive states it.

The archive's frame condition gives `α = (1 − δ)⁻¹(η + 4√e)` and `β = 4(1 − δ)⁻¹`. The constants here are no larger
when `e ≤ 1/4`.
-/

namespace FrameAtPlace

open Module Submodule LinearMap RCLike
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Partial traces.** For a symmetric `T` and an orthonormal family `v`, `Σ_i ‖T v_i‖² ≤ tr T²`. In an orthonormal
basis `b`, `tr T² = Σ_l ‖T b_l‖²` and `‖T v_i‖² = Σ_l |⟪v_i, T b_l⟫|²`, so Bessel's inequality for `v` gives it. -/
theorem sum_norm_sq_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {κ : Type*} {v : κ → E}
    (hv : Orthonormal 𝕜 v) (s : Finset κ) :
    ∑ i ∈ s, ‖T (v i)‖ ^ 2 ≤ re (trace 𝕜 E (T * T)) := by
  set b := stdOrthonormalBasis 𝕜 E
  have h1 : re (trace 𝕜 E (T * T)) = ∑ l, ‖T (b l)‖ ^ 2 := by
    rw [trace_eq_sum_inner _ b, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Module.End.mul_apply, ← hT, inner_self_eq_norm_sq]
  have h2 (i : κ) : ‖T (v i)‖ ^ 2 = ∑ l, ‖⟪v i, T (b l)⟫_𝕜‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hT, norm_inner_symm]
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  exact Finset.sum_le_sum fun l _ => hv.sum_inner_products_le _

end Space

section FrameCondition

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ ω, NormedAddCommGroup (V ω)]
  [∀ ω, InnerProductSpace 𝕜 (V ω)] [∀ ω, FiniteDimensional 𝕜 (V ω)] {W : Type*} [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- **Cauchy–Schwarz over the words**: for orthonormal families `v ω` of `m ω` vectors and symmetric `T ω`,
`(Σ_ω Σ_i ‖T_ω v_{ω,i}‖)² ≤ (Σ_ω m ω)·Σ_ω tr T_ω²`. -/
theorem sq_sum_le {m : ι → ℕ} {v : ∀ ω, Fin (m ω) → V ω} (hv : ∀ ω, Orthonormal 𝕜 (v ω))
    {T : ∀ ω, V ω →ₗ[𝕜] V ω} (hT : ∀ ω, (T ω).IsSymmetric) :
    (∑ ω, ∑ i, ‖T ω (v ω i)‖) ^ 2 ≤ (∑ ω, (m ω : ℝ)) * ∑ ω, re (trace 𝕜 (V ω) (T ω * T ω)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Σ ω, Fin (m ω))))
    (f := fun x => ‖T x.1 (v x.1 x.2)‖)
  rw [Finset.card_univ, Fintype.card_sigma, Fintype.sum_sigma, Fintype.sum_sigma] at h
  refine h.trans ?_
  push_cast
  simp only [Fintype.card_fin]
  gcongr with ω
  exact sum_norm_sq_le (hT ω) (hv ω) _

/-- The defect of `B` from an isometry, `B*B − 1`. -/
noncomputable def defect {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
    (B : U →ₗ[𝕜] W) : U →ₗ[𝕜] U :=
  B.adjoint ∘ₗ B - 1

/-- `B*B − 1` is symmetric. -/
theorem defect_isSymmetric {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
    (B : U →ₗ[𝕜] W) : (defect B).IsSymmetric := fun x y => by
  simp [defect, inner_sub_left, inner_sub_right, adjoint_inner_left, adjoint_inner_right]

/-- The frame operator `Q = Σ_ω B_ω B_ω*`. -/
noncomputable def frameOp (B : ∀ ω, V ω →ₗ[𝕜] W) : W →ₗ[𝕜] W :=
  ∑ ω, B ω ∘ₗ (B ω).adjoint

/-- `⟪y, Q y⟫ = Σ_ω ‖B_ω* y‖²`. -/
theorem re_inner_frameOp (B : ∀ ω, V ω →ₗ[𝕜] W) (y : W) :
    re ⟪y, frameOp B y⟫_𝕜 = ∑ ω, ‖(B ω).adjoint y‖ ^ 2 := by
  simp only [frameOp, LinearMap.sum_apply, comp_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← adjoint_inner_left, inner_self_eq_norm_sq]

/-- The frame operator is symmetric. -/
theorem frameOp_isSymmetric (B : ∀ ω, V ω →ₗ[𝕜] W) : (frameOp B).IsSymmetric := fun x y => by
  simp only [frameOp, LinearMap.sum_apply, comp_apply, inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← adjoint_inner_right, adjoint_inner_left]

/-- **The frame condition at one place**, with constants `e < 1` and `η ≥ 0`: the maps `B ω` are nearly isometric (I)
and nearly tight (T). -/
structure FrameCond (B : ∀ ω, V ω →ₗ[𝕜] W) (e η : ℝ) : Prop where
  /-- Some source is not zero. -/
  pos : 0 < ∑ ω, finrank 𝕜 (V ω)
  /-- `e < 1`. -/
  e_lt_one : e < 1
  /-- `η ≥ 0`. -/
  η_nonneg : 0 ≤ η
  /-- **(I)**, near-isometry: `Σ_ω ‖B_ω*B_ω − 1‖²_HS ≤ e·Σ_ω dim V_ω`. -/
  isom : ∑ ω, re (trace 𝕜 (V ω) (defect (B ω) * defect (B ω))) ≤ e * ∑ ω, (finrank 𝕜 (V ω) : ℝ)
  /-- **(T)**, near-tightness: `dim W·tr Q² ≤ (1 + η)(tr Q)²`. -/
  tight : finrank 𝕜 W * re (trace 𝕜 W (frameOp B * frameOp B)) ≤ (1 + η) * re (trace 𝕜 W (frameOp B)) ^ 2

/-- **The arithmetic of the frame condition.** Suppose the partial trace `T` of `Q` on `S^⊥`, of dimension `c`, is at
most `k + A` with `k ≤ εn` and `A² ≤ k·s²n`, and at least `c·m − P` with `P² ≤ c·ηm²D`, where `mD = tr Q ≥ n − A'`
and `A'² ≤ n·s²n`. Then `c ≤ (η + 2(s + ε)/(1 − s))·D`. -/
theorem arith {n D c k T A A' m P s ε η : ℝ} (hn : 0 < n) (hD : 0 < D) (hs : 0 ≤ s) (hs1 : s < 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hη : 0 ≤ η) (hc : 0 ≤ c) (hk : k ≤ ε * n)
    (hT : T ≤ k + A) (hA2 : A ^ 2 ≤ k * (s ^ 2 * n))
    (hA'2 : A' ^ 2 ≤ n * (s ^ 2 * n)) (hm : n - A' ≤ m * D)
    (hP : c * m - P ≤ T) (hP2 : P ^ 2 ≤ c * (η * m ^ 2 * D)) :
    c ≤ (η + 2 * (s + ε) / (1 - s)) * D := by
  have hsn : 0 ≤ s * n := mul_nonneg hs hn.le
  have hA : A ≤ s * n := by
    have : A ^ 2 ≤ (s * n) ^ 2 := by nlinarith [mul_nonneg (mul_nonneg hs hs) hn.le]
    nlinarith
  have hA' : A' ≤ s * n := by nlinarith
  have hmD : (1 - s) * n ≤ m * D := by linarith
  have hm0 : 0 < m := by
    have : 0 < m * D := by nlinarith
    exact pos_of_mul_pos_left this hD.le
  have hP' : P ≤ m * (c + η * D) / 2 := by
    have : P ^ 2 ≤ (m * (c + η * D) / 2) ^ 2 := by
      nlinarith [sq_nonneg (c - η * D), sq_nonneg m, mul_nonneg (sq_nonneg m) (sq_nonneg (c - η * D))]
    nlinarith [mul_nonneg hm0.le (add_nonneg hc (mul_nonneg hη hD.le))]
  have h5 : m * (c - η * D) ≤ 2 * (ε + s) * n := by nlinarith
  have h6 : (1 - s) * (c - η * D) ≤ 2 * (ε + s) * D := by
    have : m * ((1 - s) * (c - η * D)) ≤ m * (2 * (ε + s) * D) := by
      nlinarith [mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 1 - s),
        mul_le_mul_of_nonneg_left hmD (by positivity : (0 : ℝ) ≤ 2 * (ε + s))]
    exact le_of_mul_le_mul_left this hm0
  rw [add_mul, div_mul_eq_mul_div, ← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
  linarith

variable {B : ∀ ω, V ω →ₗ[𝕜] W} {e η : ℝ}

/-- `√e < 1`. -/
theorem FrameCond.sqrt_lt_one (hB : FrameCond B e η) : √e < 1 :=
  (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hB.e_lt_one)

/-- **The frame condition at one place forces rank spreading**: if the `N ω ≤ V ω` have total codimension at most
`ε'·Σ_ω dim V_ω`, with `0 ≤ ε' ≤ 1`, then `S = Σ_ω B_ω(N ω)` has codimension at most
`(η + 2(√e + ε')/(1 − √e))·dim W`. -/
theorem FrameCond.codim_le (hB : FrameCond B e η) {ε' : ℝ} (hε0 : 0 ≤ ε') (hε1 : ε' ≤ 1)
    (N : ∀ ω, Submodule 𝕜 (V ω))
    (hN : ∑ ω, ((finrank 𝕜 (V ω) : ℝ) - finrank 𝕜 (N ω)) ≤ ε' * ∑ ω, (finrank 𝕜 (V ω) : ℝ)) :
    (finrank 𝕜 W : ℝ) - finrank 𝕜 ↥(⨆ ω, (N ω).map (B ω)) ≤
      (η + 2 * (√e + ε') / (1 - √e)) * finrank 𝕜 W := by
  set S := ⨆ ω, (N ω).map (B ω)
  set Q := frameOp B with hQ_def
  set n : ℝ := ∑ ω, (finrank 𝕜 (V ω) : ℝ) with hn_def
  have hn : 0 < n := by
    rw [hn_def, ← Nat.cast_sum]
    exact_mod_cast hB.pos
  have hc : (finrank 𝕜 W : ℝ) - finrank 𝕜 S = finrank 𝕜 ↥Sᗮ := by
    rw [← S.finrank_add_finrank_orthogonal]
    push_cast
    ring
  have hes : e ≤ √e ^ 2 := (le_max_left e 0).trans Real.sq_sqrt'.ge
  -- The case `W = 0`.
  rcases (Nat.cast_nonneg (α := ℝ) (finrank 𝕜 W)).eq_or_lt with hD | hD
  · rw [← hD, mul_zero, zero_sub, neg_nonpos]
    exact Nat.cast_nonneg _
  -- Orthonormal bases of `Sᗮ`, of the `(N ω)ᗮ` and of the `V ω`.
  set u := stdOrthonormalBasis 𝕜 ↥Sᗮ
  have hu : Orthonormal 𝕜 fun j => (u j : W) := u.orthonormal.comp_linearIsometry Sᗮ.subtypeₗᵢ
  set g := fun ω => stdOrthonormalBasis 𝕜 ↥(N ω)ᗮ
  have hg (ω : ι) : Orthonormal 𝕜 fun i => (g ω i : V ω) :=
    (g ω).orthonormal.comp_linearIsometry (N ω)ᗮ.subtypeₗᵢ
  set f := fun ω => stdOrthonormalBasis 𝕜 (V ω)
  -- A unit vector `x` has `‖B x‖² = 1 + ⟪x, X x⟫`, within `‖X x‖` of `1`.
  have hunit (ω : ι) {x : V ω} (hx : ‖x‖ = 1) : |‖B ω x‖ ^ 2 - 1| ≤ ‖defect (B ω) x‖ := by
    rw [show ‖B ω x‖ ^ 2 - 1 = re ⟪x, defect (B ω) x⟫_𝕜 by
      simp [defect, inner_sub_right, adjoint_inner_right, hx]]
    exact (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by rw [hx, one_mul]))
  -- **Above**: `Σ_j ⟪u_j, Q u_j⟫ ≤ Σ_ω codim N ω + Σ_ω Σ_i ‖X_ω g_{ω,i}‖`.
  have hadj (ω : ι) (j) : ‖(B ω).adjoint (u j)‖ ^ 2 = ∑ i, ‖⟪(u j : W), B ω (g ω i)⟫_𝕜‖ ^ 2 := by
    have hmem : (B ω).adjoint (u j) ∈ (N ω)ᗮ := by
      rw [mem_orthogonal]
      intro x hx
      rw [adjoint_inner_right]
      exact (mem_orthogonal S _).1 (u j).2 _ (mem_iSup_of_mem ω (mem_map_of_mem hx))
    rw [show ‖(B ω).adjoint (u j)‖ = ‖(⟨_, hmem⟩ : ↥(N ω)ᗮ)‖ from rfl, ← (g ω).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_inner, adjoint_inner_right, norm_inner_symm]
  have hup : ∑ j, re ⟪(u j : W), Q (u j)⟫_𝕜 ≤
      ∑ ω, (finrank 𝕜 ↥(N ω)ᗮ : ℝ) + ∑ ω, ∑ i, ‖defect (B ω) (g ω i)‖ := by
    calc ∑ j, re ⟪(u j : W), Q (u j)⟫_𝕜 = ∑ ω, ∑ i, ∑ j, ‖⟪(u j : W), B ω (g ω i)⟫_𝕜‖ ^ 2 := by
          simp only [hQ_def, re_inner_frameOp, hadj]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ω _ => Finset.sum_comm
      _ ≤ ∑ ω, ∑ i, (1 + ‖defect (B ω) (g ω i)‖) := by
          gcongr with ω _ i _
          refine (hu.sum_inner_products_le _).trans ?_
          linarith [(abs_le.1 (hunit ω ((hg ω).1 i))).2]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hA := sq_sum_le (v := fun ω i => (g ω i : V ω)) hg fun ω => defect_isSymmetric (B ω)
  -- **The trace of `Q`**: `tr Q = Σ_ω tr B_ω*B_ω = Σ_{ω,l} ‖B_ω f_{ω,l}‖² ≥ Σd − Σ_{ω,l} ‖X_ω f_{ω,l}‖`.
  have htr : n - ∑ ω, ∑ l, ‖defect (B ω) (f ω l)‖ ≤ re (trace 𝕜 W Q) := by
    simp only [hQ_def, frameOp, map_sum]
    rw [hn_def, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [trace_comp_comm', trace_eq_sum_inner _ (f ω), map_sum]
    simp only [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq]
    calc (finrank 𝕜 (V ω) : ℝ) - ∑ l, ‖defect (B ω) (f ω l)‖ = ∑ l, (1 - ‖defect (B ω) (f ω l)‖) := by
          simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun l _ => by linarith [(abs_le.1 (hunit ω ((f ω).orthonormal.1 l))).1]
  have hA' := sq_sum_le (v := fun ω => f ω) (fun ω => (f ω).orthonormal) fun ω => defect_isSymmetric (B ω)
  -- **Below**: with `m = tr Q/dim W`, `Σ_j ⟪u_j, Q u_j⟫ ≥ codim S·m − Σ_j ‖(Q − m) u_j‖`.
  set m := re (trace 𝕜 W Q) / finrank 𝕜 W
  set Q₀ := Q - (m : 𝕜) • (1 : W →ₗ[𝕜] W)
  have hQ₀ : Q₀.IsSymmetric := (frameOp_isSymmetric B).sub (IsSymmetric.one.smul (conj_ofReal m))
  have hlow : (finrank 𝕜 ↥Sᗮ : ℝ) * m - ∑ j, ‖Q₀ (u j)‖ ≤ ∑ j, re ⟪(u j : W), Q (u j)⟫_𝕜 := by
    have h (j) : m - ‖Q₀ (u j)‖ ≤ re ⟪(u j : W), Q (u j)⟫_𝕜 := by
      have h1 : re ⟪(u j : W), Q (u j)⟫_𝕜 = m + re ⟪(u j : W), Q₀ (u j)⟫_𝕜 := by
        simp [Q₀, inner_sub_right, inner_smul_right, hu.1 j]
      have h2 := (abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := 𝕜) (u j : W) (Q₀ (u j)))
      rw [hu.1 j, one_mul] at h2
      linarith [(abs_le.1 h2).1]
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h j
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hP : (∑ j, ‖Q₀ (u j)‖) ^ 2 ≤ finrank 𝕜 ↥Sᗮ * re (trace 𝕜 W (Q₀ * Q₀)) := by
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    gcongr
    exact sum_norm_sq_le hQ₀ hu _
  -- (T) is `dim W·tr (Q − m)² ≤ η (tr Q)²`.
  have hmD : m * finrank 𝕜 W = re (trace 𝕜 W Q) := div_mul_cancel₀ _ hD.ne'
  have hQ₀le : re (trace 𝕜 W (Q₀ * Q₀)) ≤ η * m ^ 2 * finrank 𝕜 W := by
    have htrQ₀ : re (trace 𝕜 W (Q₀ * Q₀)) =
        re (trace 𝕜 W (Q * Q)) - 2 * m * re (trace 𝕜 W Q) + m ^ 2 * finrank 𝕜 W := by
      simp only [Q₀, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_sub, map_smul,
        trace_one, smul_eq_mul, re_ofReal_mul, natCast_re]
      ring
    have := hB.tight
    rw [← hmD] at this
    refine le_of_mul_le_mul_left ?_ hD
    rw [htrQ₀, ← hmD]
    nlinarith
  -- **Combine.**
  rw [hc]
  refine arith hn hD (Real.sqrt_nonneg e) hB.sqrt_lt_one hε0 hε1 hB.η_nonneg (Nat.cast_nonneg _) ?_ hup ?_ ?_
    (htr.trans_eq hmD.symm) hlow (hP.trans (mul_le_mul_of_nonneg_left hQ₀le (Nat.cast_nonneg _)))
  · have hk (ω : ι) : (finrank 𝕜 ↥(N ω)ᗮ : ℝ) = finrank 𝕜 (V ω) - finrank 𝕜 (N ω) := by
      rw [← (N ω).finrank_add_finrank_orthogonal]
      push_cast
      ring
    simp only [hk]
    exact hN
  · refine hA.trans ?_
    gcongr
    exact hB.isom.trans (mul_le_mul_of_nonneg_right hes hn.le)
  · refine hA'.trans ?_
    gcongr
    exact hB.isom.trans (mul_le_mul_of_nonneg_right hes hn.le)

/-- **The padded target**: if `(1 − δ)·dim W ≤ dim C`, with `δ < 1`, then
`dim C − dim S ≤ (1 − δ)⁻¹(η + 2(√e + ε')/(1 − √e))·dim C`. When `S ≤ C`, the left side is the codimension of `S` in
`C`. -/
theorem FrameCond.codim_le_padded (hB : FrameCond B e η) {ε' : ℝ} (hε0 : 0 ≤ ε') (hε1 : ε' ≤ 1)
    (N : ∀ ω, Submodule 𝕜 (V ω))
    (hN : ∑ ω, ((finrank 𝕜 (V ω) : ℝ) - finrank 𝕜 (N ω)) ≤ ε' * ∑ ω, (finrank 𝕜 (V ω) : ℝ))
    (C : Submodule 𝕜 W) {δ : ℝ} (hδ : δ < 1) (hC : (1 - δ) * finrank 𝕜 W ≤ finrank 𝕜 C) :
    (finrank 𝕜 C : ℝ) - finrank 𝕜 ↥(⨆ ω, (N ω).map (B ω)) ≤
      (1 - δ)⁻¹ * (η + 2 * (√e + ε') / (1 - √e)) * finrank 𝕜 C := by
  have h := hB.codim_le hε0 hε1 N hN
  have hCW : (finrank 𝕜 C : ℝ) ≤ finrank 𝕜 W := by exact_mod_cast C.finrank_le
  have hR : 0 ≤ η + 2 * (√e + ε') / (1 - √e) :=
    add_nonneg hB.η_nonneg (div_nonneg (by positivity) (by linarith [hB.sqrt_lt_one]))
  have hW : (finrank 𝕜 W : ℝ) ≤ (1 - δ)⁻¹ * finrank 𝕜 C := by
    rw [le_inv_mul_iff₀ (by linarith)]
    exact hC
  calc (finrank 𝕜 C : ℝ) - finrank 𝕜 ↥(⨆ ω, (N ω).map (B ω)) ≤
        (η + 2 * (√e + ε') / (1 - √e)) * finrank 𝕜 W := by linarith
    _ ≤ (η + 2 * (√e + ε') / (1 - √e)) * ((1 - δ)⁻¹ * finrank 𝕜 C) := by gcongr
    _ = _ := by ring

end FrameCondition

/-! ### Complex-linear maps -/

section Complex

attribute [local instance] InnerProductSpace.complexToReal

variable {U U' : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup U'] [InnerProductSpace ℂ U'] [FiniteDimensional ℂ U']

/-- **The real trace** of a complex-linear map is twice the real part of its trace: in the real basis `b_l, i·b_l`, an
entry `a` of its complex matrix becomes the block `[[re a, −im a], [im a, re a]]`. -/
theorem trace_restrictScalars (T : U →ₗ[ℂ] U) : trace ℝ U (T.restrictScalars ℝ) = 2 * re (trace ℂ U T) := by
  rw [trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' (finBasis ℂ U)), restrictScalars_toMatrix,
    trace_eq_matrix_trace ℂ (finBasis ℂ U), re_to_complex, ← Algebra.trace_complex_apply, Matrix.trace,
    Matrix.trace, map_sum, Fintype.sum_prod_type]
  simp [Algebra.trace_eq_matrix_trace Complex.basisOneI, Matrix.trace]

/-- **The adjoint commutes with restricting scalars**, for the real inner products `re ⟪·, ·⟫`. -/
theorem adjoint_restrictScalars (B : U →ₗ[ℂ] U') : (B.restrictScalars ℝ).adjoint = B.adjoint.restrictScalars ℝ :=
  ((eq_adjoint_iff _ _).2 fun x y => by simp [real_inner_eq_re_inner ℂ, adjoint_inner_left]).symm

/-- **The frame condition over `ℝ` for complex-linear maps**: complex-linear maps that meet it over `ℂ` meet it over
`ℝ`, with the same `e` and `η`. Real dimensions are twice the complex ones, real traces twice the real parts of the
complex ones (`trace_restrictScalars`), and adjoints commute with restricting scalars (`adjoint_restrictScalars`). So
both sides of (I) double, and both sides of (T) quadruple. -/
theorem FrameCond.restrictScalars {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ ω, NormedAddCommGroup (V ω)]
    [∀ ω, InnerProductSpace ℂ (V ω)] [∀ ω, FiniteDimensional ℂ (V ω)] {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {B : ∀ ω, V ω →ₗ[ℂ] W} {e η : ℝ} (hB : FrameCond B e η) :
    FrameCond (fun ω => (B ω).restrictScalars ℝ) e η := by
  have hd (ω : ι) : defect ((B ω).restrictScalars ℝ) * defect ((B ω).restrictScalars ℝ) =
      (defect (B ω) * defect (B ω)).restrictScalars ℝ := by
    simp only [defect, adjoint_restrictScalars]
    rfl
  have hQ : frameOp (fun ω => (B ω).restrictScalars ℝ) = (frameOp B).restrictScalars ℝ := by
    ext y
    simp [frameOp, adjoint_restrictScalars]
  obtain ⟨hpos, he, hη, hI, hT⟩ := hB
  refine ⟨by simpa [finrank_real_of_complex, ← Finset.mul_sum] using hpos, he, hη, ?_, ?_⟩
  · simp only [hd, trace_restrictScalars, finrank_real_of_complex, re_to_real, Nat.cast_mul, Nat.cast_ofNat,
      ← Finset.mul_sum]
    linarith
  · rw [hQ, show (frameOp B).restrictScalars ℝ * (frameOp B).restrictScalars ℝ =
      (frameOp B * frameOp B).restrictScalars ℝ from rfl]
    simp only [trace_restrictScalars, finrank_real_of_complex, re_to_real, Nat.cast_mul, Nat.cast_ofNat]
    linarith

end Complex

end FrameAtPlace

namespace PlaceLattice

open Module Submodule FrameAtPlace

/-- A balanced subspace contains the parts of its vectors at the places, as it is the sum of its own parts there. -/
theorem Balanced.starProjection_mem {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] {P : Type*} [Fintype P] [Nonempty P] {V : P → Submodule ℝ G}
    (hV : Pairwise fun v w => V v ⟂ V w) {U : Submodule ℝ G} (hU : Balanced V U) (w : P) {y : G}
    (hy : y ∈ U) : (V w).starProjection y ∈ U := by
  refine iSup_induction (motive := fun y => (V w).starProjection y ∈ U) _ ((hU.iSup_inf_eq hV).ge hy)
    (fun v y hy => ?_) (by rw [map_zero]; exact zero_mem _) fun y z hy hz => by rw [map_add]; exact add_mem hy hz
  obtain rfl | hvw := eq_or_ne v w
  · rw [starProjection_eq_self_iff.2 hy.2]
    exact hy.1
  · rw [(starProjection_apply_eq_zero_iff (V w)).2 ((hV hvw) hy.2)]
    exact zero_mem _

/-- The rank of a member of the class, read at any one place: `rk a = |P|·dim (span a ∩ V v)`. -/
theorem rk_eq_card_mul {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (Z : PlaceLattice G) (a : Z.S) (v : Z.P) :
    Z.slopeLattice.rk a = Fintype.card Z.P * finrank ℝ ((span ℝ (a.1.1 : Set G)).comap (Z.V v).subtype) := by
  rw [← finrank_map_subtype_eq, map_comap_subtype, inf_comm]
  exact (Z.balanced a.1 a.2 v).symm

/-- The component of `φ` from a subspace `A` of its source to a subspace `A'` of its target: `π_{A'} ∘ φ` on `A`. -/
noncomputable def component {G G' : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [NormedAddCommGroup G'] [InnerProductSpace ℝ G'] [FiniteDimensional ℝ G'] (φ : G →L[ℝ] G')
    (A : Submodule ℝ G) (A' : Submodule ℝ G') : A →ₗ[ℝ] A' :=
  (A'.orthogonalProjectionOnto : G' →ₗ[ℝ] A') ∘ₗ (φ : G →ₗ[ℝ] G') ∘ₗ A.subtype

variable {ι : Type} [Fintype ι] {E : ι → Type} [∀ ω, NormedAddCommGroup (E ω)] [∀ ω, InnerProductSpace ℝ (E ω)]
  [∀ ω, FiniteDimensional ℝ (E ω)] {X : ∀ ω, PlaceLattice (E ω)} {F : Type} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {Y : PlaceLattice F}

/-- **Rank spreading from the frame condition at one place.** Let lattices with places `X ω`, all with as many places as
`Y`, map into `Y` by `φ ω`, forming a frame (`PlaceLattice.frame`). Take places `v ω` of the sources and `w` of the
target. Suppose that:
* the `X ω` have full rank;
* multiples `c ω` of the components `π_w ∘ φ ω` on the parts at `v ω` meet the frame condition with constants `e`, `η`;
* the part of `span Λ_Y` at `w` has at least `1 − δ` of the dimension of the part of `F` there.

Then the frame spreads ranks with `α = (1 − δ)⁻¹(η + 2√e/(1 − √e))` and `β = (1 − δ)⁻¹·2/(1 − √e)`. -/
theorem spread_of_frameCond (φ : ∀ ω, E ω →L[ℝ] F) (hφΛ : ∀ ω, ∀ x ∈ (X ω).Λ, φ ω x ∈ Y.Λ)
    (h : ∀ ω, (X ω).P → ℝ) (hφ : ∀ ω v, ∀ x ∈ (X ω).V v, ‖φ ω x‖ ≤ Real.exp (h ω v) * ‖x‖)
    (himg : ∀ ω, ∀ a ∈ (X ω).S, EuclidLattice.img (φ ω) a ∈ Y.S)
    (hpre : ∀ ω, ∀ b ∈ Y.S, EuclidLattice.preimg (φ ω) b ∈ (X ω).S) (hrk : 0 < finrank ℝ (span ℝ (Y.Λ : Set F)))
    (hΛ : ∀ ω, span ℝ ((X ω).Λ : Set (E ω)) = ⊤) (hP : ∀ ω, Fintype.card (X ω).P = Fintype.card Y.P)
    (v : ∀ ω, (X ω).P) (w : Y.P) (c : ι → ℝ) {e η : ℝ}
    (hB : FrameCond (fun ω => c ω • component (φ ω) ((X ω).V (v ω)) (Y.V w)) e η) {δ : ℝ} (hδ : δ < 1)
    (hpad : (1 - δ) * finrank ℝ (Y.V w) ≤ finrank ℝ ↥(span ℝ (Y.Λ : Set F) ⊓ Y.V w)) :
    (frame X Y φ hφΛ h hφ himg hpre hrk).RankSpread ((1 - δ)⁻¹ * (η + 2 * √e / (1 - √e)))
      ((1 - δ)⁻¹ * (2 / (1 - √e))) := by
  rintro ε' hε0 hε1 (a : ∀ ω, (X ω).S) ha
  change ∑ ω, (((X ω).slopeLattice.rk ⊤ : ℝ) - (X ω).slopeLattice.rk (a ω)) ≤
    ε' * ∑ ω, ((X ω).slopeLattice.rk ⊤ : ℝ) at ha
  change (Y.slopeLattice.rk ⊤ : ℝ) - Y.slopeLattice.rk
    (Finset.univ.sup fun ω => (⟨EuclidLattice.img (φ ω) (a ω).1, himg ω _ (a ω).2⟩ : Y.S)) ≤
    ((1 - δ)⁻¹ * (η + 2 * √e / (1 - √e)) + (1 - δ)⁻¹ * (2 / (1 - √e)) * ε') * Y.slopeLattice.rk ⊤
  set p := Fintype.card Y.P
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 Fintype.card_pos
  -- The sources, read at their places.
  set N := fun ω => (span ℝ ((a ω).1.1 : Set (E ω))).comap ((X ω).V (v ω)).subtype
  have htop (ω : ι) : ((X ω).slopeLattice.rk ⊤ : ℝ) = p * finrank ℝ ((X ω).V (v ω)) := by
    rw [rk_eq_card_mul (X ω) ⊤ (v ω), hP]
    simp only [Nat.cast_mul]
    congr 2
    rw [show ((⊤ : (X ω).S).1.1 : Set (E ω)) = (X ω).Λ from rfl, hΛ ω, comap_top, finrank_top]
  have ha' (ω : ι) : ((X ω).slopeLattice.rk (a ω) : ℝ) = p * finrank ℝ (N ω) := by
    rw [rk_eq_card_mul (X ω) (a ω) (v ω), hP]
    push_cast
    rfl
  have hN : ∑ ω, ((finrank ℝ ((X ω).V (v ω)) : ℝ) - finrank ℝ (N ω)) ≤
      ε' * ∑ ω, (finrank ℝ ((X ω).V (v ω)) : ℝ) := by
    simp only [htop, ha', ← mul_sub, ← Finset.mul_sum] at ha
    nlinarith
  -- The target: the components of the `N ω` lie in the part at `w` of the sum `M` of the images.
  set M := Finset.univ.sup fun ω => (⟨EuclidLattice.img (φ ω) (a ω).1, himg ω _ (a ω).2⟩ : Y.S)
  have hM : ⨆ ω, (N ω).map (c ω • component (φ ω) ((X ω).V (v ω)) (Y.V w)) ≤
      (span ℝ (M.1.1 : Set F)).comap (Y.V w).subtype := by
    refine iSup_le fun ω => ?_
    rintro _ ⟨x, hx, rfl⟩
    show c ω • (Y.V w).starProjection (φ ω x) ∈ span ℝ (M.1.1 : Set F)
    refine smul_mem _ _ (Balanced.starProjection_mem Y.orth (Y.balanced M.1 M.2) w ?_)
    have h1 : (⟨EuclidLattice.img (φ ω) (a ω).1, himg ω _ (a ω).2⟩ : Y.S) ≤ M :=
      Finset.le_sup (f := fun ω => (⟨EuclidLattice.img (φ ω) (a ω).1, himg ω _ (a ω).2⟩ : Y.S))
        (Finset.mem_univ ω)
    have h2 : φ ω x ∈ span ℝ ((EuclidLattice.img (Λ' := Y.Λ) (φ ω) (a ω).1).1 : Set F) := by
      rw [show (EuclidLattice.img (Λ' := Y.Λ) (φ ω) (a ω).1).1 =
        EuclidLattice.sat Y.Λ (φ ω '' ((a ω).1.1 : Set (E ω))) from rfl, EuclidLattice.span_sat]
      · exact (span_image (φ ω : E ω →ₗ[ℝ] F)).ge (mem_map_of_mem hx)
      · rintro _ ⟨y, hy, rfl⟩
        exact hφΛ ω y ((a ω).1.2.1 hy)
    exact span_mono (show ((EuclidLattice.img (Λ' := Y.Λ) (φ ω) (a ω).1).1 : Set F) ⊆ M.1.1 from h1) h2
  have hMrk : (Y.slopeLattice.rk M : ℝ) = p * finrank ℝ ((span ℝ (M.1.1 : Set F)).comap (Y.V w).subtype) := by
    rw [rk_eq_card_mul Y M w]
    push_cast
    rfl
  have hCrk : (Y.slopeLattice.rk ⊤ : ℝ) = p * finrank ℝ ((span ℝ (Y.Λ : Set F)).comap (Y.V w).subtype) := by
    rw [rk_eq_card_mul Y ⊤ w]
    push_cast
    rfl
  have hpad' : (1 - δ) * finrank ℝ (Y.V w) ≤ finrank ℝ ((span ℝ (Y.Λ : Set F)).comap (Y.V w).subtype) := by
    rwa [← finrank_map_subtype_eq, map_comap_subtype, inf_comm]
  have key := hB.codim_le_padded hε0 hε1 N hN _ hδ hpad'
  have hfin : (finrank ℝ ↥(⨆ ω, (N ω).map (c ω • component (φ ω) ((X ω).V (v ω)) (Y.V w))) : ℝ) ≤
      finrank ℝ ((span ℝ (M.1.1 : Set F)).comap (Y.V w).subtype) := by
    exact_mod_cast Submodule.finrank_mono hM
  rw [hMrk, hCrk]
  calc (p : ℝ) * finrank ℝ ((span ℝ (Y.Λ : Set F)).comap (Y.V w).subtype) -
        p * finrank ℝ ((span ℝ (M.1.1 : Set F)).comap (Y.V w).subtype) ≤
      p * ((1 - δ)⁻¹ * (η + 2 * (√e + ε') / (1 - √e)) *
        finrank ℝ ((span ℝ (Y.Λ : Set F)).comap (Y.V w).subtype)) := by
        rw [← mul_sub]
        exact mul_le_mul_of_nonneg_left (by linarith) hp.le
    _ = _ := by ring

end PlaceLattice

namespace HermitianLattice

open Module Submodule NumberField FrameAtPlace

attribute [local instance] InnerProductSpace.complexToReal

/-- **Rank spreading for hermitian frames from the frame condition at one complex place.** Let `v` be a complex place
of `K`, and `B ω : V ω v → W v` the components of the `φ ω` there: complex-linear maps that agree with the `φ ω`. They
exist, as maps that commute with `O_K` send `V ω v` into `W v` complex-linearly. Suppose that:
* the sources have full rank;
* multiples `c ω` of the `B ω` meet the frame condition over `ℂ` with constants `e` and `η`;
* the part of `span Λ'` at `v` has at least `1 − δ` of the dimension of `W v`.

Then the hermitian frame (`HermitianLattice.frame`) spreads ranks with `α = (1 − δ)⁻¹(η + 2√e/(1 − √e))` and
`β = (1 − δ)⁻¹·2/(1 − √e)`. -/
theorem spread_of_frameCond {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι]
    {E : ι → Type} [∀ ω, NormedAddCommGroup (E ω)] [∀ ω, InnerProductSpace ℂ (E ω)]
    [∀ ω, FiniteDimensional ℂ (E ω)] (V : ∀ ω, Pl K → Submodule ℂ (E ω))
    (hV : ∀ ω, Pairwise fun v w => V ω v ⟂ V ω w) (htop : ∀ ω, ⨆ v, V ω v = ⊤) (Λ : ∀ ω, Submodule ℤ (E ω))
    [∀ ω, DiscreteTopology (Λ ω)] (hΛ : ∀ ω, Stable (V ω) (Λ ω)) {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (W : Pl K → Submodule ℂ F) (hW : Pairwise fun v w => W v ⟂ W w)
    (hWtop : ⨆ v, W v = ⊤) (Λ' : Submodule ℤ F) [DiscreteTopology Λ'] (hΛ' : Stable W Λ')
    (φ : ∀ ω, E ω →L[ℝ] F) (hφΛ : ∀ ω, ∀ x ∈ Λ ω, φ ω x ∈ Λ')
    (hφK : ∀ ω (k : 𝓞 K) x, φ ω (act (V ω) (emb (k : K)) x) = act W (emb (k : K)) (φ ω x))
    (h : ι → Pl K → ℝ) (hφ : ∀ ω v, ∀ x ∈ V ω v, ‖φ ω x‖ ≤ Real.exp (h ω v) * ‖x‖)
    (hrk : 0 < finrank ℝ (span ℝ (Λ' : Set F))) (hspan : ∀ ω, span ℝ (Λ ω : Set (E ω)) = ⊤) (v : Pl K)
    (B : ∀ ω, V ω v →ₗ[ℂ] W v) (hBφ : ∀ ω x, (B ω x : F) = φ ω x) (c : ι → ℝ) {e η : ℝ}
    (hB : FrameCond (fun ω => c ω • B ω) e η) {δ : ℝ} (hδ : δ < 1)
    (hpad : (1 - δ) * finrank ℝ ((W v).restrictScalars ℝ) ≤
      finrank ℝ ↥(span ℝ (Λ' : Set F) ⊓ (W v).restrictScalars ℝ)) :
    (frame V hV htop Λ hΛ W hW hWtop Λ' hΛ' φ hφΛ hφK h hφ hrk).RankSpread
      ((1 - δ)⁻¹ * (η + 2 * √e / (1 - √e))) ((1 - δ)⁻¹ * (2 / (1 - √e))) := by
  refine PlaceLattice.spread_of_frameCond (X := fun ω => placeLattice (V ω) (hV ω) (htop ω) (Λ ω) (hΛ ω))
    (Y := placeLattice W hW hWtop Λ' hΛ') φ hφΛ h hφ (fun ω _ ha => hΛ'.img (hφK ω) ha)
    (fun ω _ hb => (hΛ ω).preimg (hφK ω) hb) hrk hspan (fun _ => rfl) (fun _ => v) v c ?_ hδ hpad
  -- The real components are the realifications of the `c ω • B ω`.
  have hc : (fun ω => (c ω • B ω).restrictScalars ℝ) =
      fun ω => c ω • PlaceLattice.component (φ ω) ((V ω v).restrictScalars ℝ) ((W v).restrictScalars ℝ) := by
    funext ω
    ext (x : V ω v)
    show c ω • (B ω x : F) = c ω • ((W v).restrictScalars ℝ).starProjection (φ ω x)
    rw [← hBφ, (starProjection_eq_self_iff (K := (W v).restrictScalars ℝ)).2 (B ω x).2]
  exact hc ▸ hB.restrictScalars

end HermitianLattice

#print axioms FrameAtPlace.FrameCond.codim_le
#print axioms FrameAtPlace.FrameCond.codim_le_padded
#print axioms FrameAtPlace.FrameCond.restrictScalars
#print axioms PlaceLattice.spread_of_frameCond
#print axioms HermitianLattice.spread_of_frameCond
