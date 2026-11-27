import SharpNI
import GainCert

/-!
# The range (R′) of the frame loss from the gain's certificate

The statement (R′) of the frame loss (`ZetaBalance.SharpRange`): in every realising frame, the source `N_ω` has
`μ_max(N_ω) ≤ μ(N_ω) + U` with `0 ≤ U ≤ x^{4ε}Σ_t a_t/4`. Here it is reduced to a bound on the maximal slope of the
lattice of integral forms `M_ω` and to gain certificates (`SharpObj.GainCert`) of small colength
(`ZetaBalance.sharpRange_of_cert`). All slopes are in the archive's units.

**The sandwich.** A certificate gives `N_ω ⊆ γM_ω`, `γ = β/α`, with colength `[γM_ω : N_ω] ≤ [M_ω : L]`
(`GainCert.N_le`, `GainCert.colength_le`). Then, for lattices in one metric space,
`μ_max(N_ω) − μ(N_ω) ≤ μ_max(M_ω) − μ(M_ω) + 2·log[γM_ω : N_ω]/rk` (`KLattice.slopeLe_rescale_of_le_smul`):
* a sublattice of `N_ω` lies in `γM_ω`, and its image under `γ⁻¹` in `M_ω`;
* `μ(N_ω) = μ(γM_ω) − 2·log[γM_ω : N_ω]/rk` (`KLattice.slope_withLattice`);
* the scaling by `γ` moves every slope by one amount, so it cancels between `μ_max` and `μ`. No norm of `γ` enters.

**Scaling** (`KLattice.exists_smul_sublattice`). Multiplication by `c ∈ K×` acts on `⊕_v ℂ^ι` by `σ_v(c)` on the
part at `v` (`HermitianLattice.act`). It sends `ψ(P)` into `ψ(Q)` when `cP ⊆ Q`, commutes with `O_K`, is injective, and
has norm `|σ_v(c)|` on the part at `v`. So it sends an `O_K`-stable saturated sublattice `a` of `ψ(P)` to the
saturation `b` of its image, of the same rank, with `deg a ≤ deg b + h̄(c)·rk a`, `h̄(c) = n_∞⁻¹ Σ_v log|σ_v(c)|`
(`KLattice.logScale`). This is Bost's inequality at the one quotient `a/0` (`PlaceLattice.deg_le_img`, from
`EuclidLattice.bost_le`): `φ` kills no point, so the kernel sublattice is `0`, and Hadamard place by place bounds the
volume. Used with `c = γ⁻¹` on the sublattices of `N_ω`, and with `c = γ` on `M_ω` itself, where the image of a full
sublattice is everything; as `h̄(γ⁻¹) = −h̄(γ)` (`KLattice.logScale_inv`), the two shifts cancel.

**The range of `M_ω`** (`SharpObj.sourceRangeLe_of_muMaxLe`). If `μ_max(M_ω) ≤ B` in every realising frame
(`SharpObj.MuMaxLe`), then `μ_max(M_ω) − μ(M_ω) ≤ B + c_F` for any `c_F` of (F) + (V) (`SharpObj.SlopeFV`): the index
bookkeeping (V) turns `μ(N_ω) ≥ −c_F + idx_ω` into `μ(M_ω) ≥ −c_F`. For the construction this is applied to the
object with its slack `c_F` replaced by the exact constant of (F) (`HermForms.cFx`), for which (F) + (V) is
`SharpObj.slopeFV_exact`; the object's own `c_F = x^{4ε}Σ_t a_t/8` would use up the budget.

**The result** (`ZetaBalance.sharpRange_of_cert`): (R′) holds with `U = max(B + c_F^{exact} + x^{4ε}Σ_t a_t/8, 0)` if,
eventually in the design, `μ_max(M_ω) ≤ B` with `B + c_F^{exact} ≤ x^{4ε}Σ_t a_t/8` (`SharpMuMax`), and every word has
a certificate of colength `2·log[M_ω : L]/rk ≤ x^{4ε}Σ_t a_t/8` (`SharpCertSmall`). The bound on `μ_max(M_ω)` is not
proved in the library: it needs an integrality bound for the Petersson values of the integral forms (the Fock duals
`Δ` of the bideterminant lattices `∇_O`), so `SharpMuMax` is a hypothesis.
-/

open NumberField

namespace SlopeFrame.SlopeLattice

variable {L : Type*} [Lattice L] [BoundedOrder L] {X : SlopeLattice L}

/-- **`SlopeLe` is monotone** in the slope. -/
theorem SlopeLe.mono {lam lam' : ℝ} (h : X.SlopeLe lam) (hl : lam ≤ lam') : X.SlopeLe lam' := fun b =>
  (h b).trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))

/-- **A lattice of rank `0` has every range**: its only sublattice is `0`. -/
theorem slopeLe_of_rk_top_eq_zero (h : X.rk ⊤ = 0) (lam : ℝ) : X.SlopeLe lam := by
  intro b
  have hb : b = ⊥ := by
    by_contra hne
    have h1 := X.rk_strictMono (bot_lt_iff_ne_bot.2 hne)
    have h2 := X.rk_mono (le_top : b ≤ ⊤)
    rw [X.rk_bot] at h1
    omega
  rw [hb, X.deg_bot, X.rk_bot, Nat.cast_zero, mul_zero]

end SlopeFrame.SlopeLattice

namespace PlaceLattice

open Module Submodule EuclidLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The degree under an injective map**: if `φ` is injective, sends `Λ` into `Λ'` and has norm at most `e^{h v}`
on the subspace at each place `v`, then the image `img φ a` of a member `a` of the class (the saturation of `φ(a)`)
has the rank of `a`, and `deg a ≤ deg (img φ a) + h̄·rk a` with `h̄ = |P|⁻¹ Σ_v h v`. This is Bost's inequality at the
one quotient `a/0` (`EuclidLattice.bost_le`): the kernel sublattice `a ⊓ preimg φ 0` is `0`. -/
theorem deg_le_img (X : PlaceLattice E) {Λ' : Submodule ℤ F} [DiscreteTopology Λ'] (φ : E →L[ℝ] F)
    (hφΛ : ∀ x ∈ X.Λ, φ x ∈ Λ') (hinj : Function.Injective φ) {h : X.P → ℝ}
    (hφ : ∀ v, ∀ x ∈ X.V v, ‖φ x‖ ≤ Real.exp (h v) * ‖x‖) (a : X.S) :
    (EuclidLattice.slopeLattice Λ').rk (img φ a.1) = X.slopeLattice.rk a ∧
      X.slopeLattice.deg a ≤ (EuclidLattice.slopeLattice Λ').deg (img φ a.1) +
        (Fintype.card X.P : ℝ)⁻¹ * (∑ v, h v) * X.slopeLattice.rk a := by
  show (EuclidLattice.slopeLattice Λ').rk (img φ a.1) = (EuclidLattice.slopeLattice X.Λ).rk a.1 ∧
    (EuclidLattice.slopeLattice X.Λ).deg a.1 ≤ (EuclidLattice.slopeLattice Λ').deg (img φ a.1) +
      (Fintype.card X.P : ℝ)⁻¹ * (∑ v, h v) * (EuclidLattice.slopeLattice X.Λ).rk a.1
  -- ranks: `span (img φ a) = φ(span a)`, and `φ` is injective
  have hrk : (EuclidLattice.slopeLattice Λ').rk (img φ a.1) = (EuclidLattice.slopeLattice X.Λ).rk a.1 := by
    show finrank ℝ (span ℝ (sat Λ' (φ '' (a.1.1 : Set E)) : Set F)) = finrank ℝ (span ℝ (a.1.1 : Set E))
    rw [span_sat (by rintro _ ⟨x, hx, rfl⟩; exact hφΛ x (a.1.2.1 hx)),
      show span ℝ (φ '' (a.1.1 : Set E)) = (span ℝ (a.1.1 : Set E)).map (φ : E →ₗ[ℝ] F) from span_image _]
    exact (equivMapOfInjective _ hinj _).finrank_eq.symm
  -- `φ` kills no point, so the kernel sublattice `a ⊓ preimg φ 0` is `0`
  have h0 : span ℝ (((⊥ : Sat Λ').1 : Submodule ℤ F) : Set F) = ⊥ := by
    rw [Sat.coe_bot, Submodule.bot_coe, span_zero_singleton]
  have hK0 : a.1 ⊓ preimg φ (⊥ : Sat Λ') = ⊥ := by
    refine Subtype.ext (eq_bot_iff.2 fun x hx => ?_)
    have h1 : x ∈ span ℝ ((preimg (Λ := X.Λ) φ (⊥ : Sat Λ')).1 : Set E) := subset_span hx.2
    have h2 := span_sat_le _ h1
    rw [span_eq, h0] at h2
    exact (mem_bot ℤ).2 (hinj (((mem_bot ℝ).1 h2).trans φ.map_zero.symm))
  have hK : a.1 ⊓ preimg φ (⊥ : Sat Λ') ∈ X.S := by
    rw [hK0]
    exact X.bot_mem
  have hvol := (Balanced.orthogonal_inf X.orth (X.balanced a a.2) (X.balanced _ hK)
    (span_mono (show ((a.1 ⊓ preimg φ (⊥ : Sat Λ')).1 : Set E) ⊆ a.1.1 from inf_le_left))).volLe X.orth hφ
  -- `θ·rk a = deg a` for `θ = deg a/rk a`, both sides being `0` when `a = 0`
  set r : ℝ := ((EuclidLattice.slopeLattice X.Λ).rk a.1 : ℝ)
  set θ := (EuclidLattice.slopeLattice X.Λ).deg a.1 / r
  have hθ : θ * r = (EuclidLattice.slopeLattice X.Λ).deg a.1 := by
    rcases eq_or_ne r 0 with hr | hr
    · have ha : a.1 = ⊥ := by
        by_contra hne
        have := (EuclidLattice.slopeLattice X.Λ).rk_strictMono (bot_lt_iff_ne_bot.2 hne)
        rw [(EuclidLattice.slopeLattice X.Λ).rk_bot] at this
        exact this.ne' (Nat.cast_eq_zero.1 hr)
      rw [hr, mul_zero, ha, (EuclidLattice.slopeLattice X.Λ).deg_bot]
    · exact div_mul_cancel₀ _ hr
  have hb := bost_le φ hφΛ (a := a.1) (b := ⊥) bot_le hvol (θ := θ) (by
    rw [hK0, (EuclidLattice.slopeLattice X.Λ).rk_bot, (EuclidLattice.slopeLattice X.Λ).deg_bot, Nat.cast_zero,
      sub_zero, sub_zero, hθ])
  rw [(EuclidLattice.slopeLattice Λ').rk_bot, (EuclidLattice.slopeLattice Λ').deg_bot, Nat.cast_zero, sub_zero,
    sub_zero, hrk, sub_mul, hθ] at hb
  exact ⟨hrk, by linarith⟩

end PlaceLattice

namespace KLattice

open Module Submodule EuclidLattice HermitianLattice

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

/-- **`K ⊗ ℝ` acts multiplicatively**: `act z ∘ act w = act (z·w)` on `⊕_v ℂ^ι`. -/
theorem act_mul (z w : Pl K → ℂ) (y : Space K ι) : act part z (act part w y) = act part (z * w) y :=
  ext_coord fun p => by simp only [coord_act, Pi.mul_apply, mul_assoc]

/-- **On the part at `v`**, `z` acts by the scalar `z v`. -/
theorem act_of_mem_part (z : Pl K → ℂ) {v : Pl K} {y : Space K ι}
    (hy : y ∈ (part v : Submodule ℂ (Space K ι))) : act part z y = z v • y := by
  obtain ⟨u, rfl⟩ := hy
  refine ext_coord fun p => ?_
  simp only [coord_act, map_smul, smul_eq_mul, ContinuousLinearMap.coe_coe, coord_op_single]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

/-- **The mean log-size of `c ∈ K` at the complex places**, `h̄(c) = n_∞⁻¹ Σ_v log|σ_v(c)|`: scaling by `c` shifts
the degree of a sublattice by at least `−h̄(c)·rk` (`exists_smul_sublattice`). -/
noncomputable def logScale (c : K) : ℝ :=
  (Fintype.card (Pl K) : ℝ)⁻¹ * ∑ v : Pl K, Real.log ‖v.1.embedding c‖

/-- **`h̄(c⁻¹) = −h̄(c)`**, as `log|σ_v(c⁻¹)| = −log|σ_v(c)|`. -/
theorem logScale_inv (c : K) : logScale c⁻¹ = -logScale c := by
  simp only [logScale, map_inv₀, norm_inv, Real.log_inv, Finset.sum_neg_distrib, mul_neg]

omit [NumberField K] [Fintype ι] in
/-- **A multiple of a lattice is a lattice**: if `γ ≠ 0`, `γM ⊆ Q` and `γ⁻¹Q ⊆ M`, then `Q = γM` is an
`O_K`-lattice whenever `M` is. -/
theorem isLattice_of_smul {M Q : Submodule (𝓞 K) (ι → K)} [M.IsLattice K] {γ : K} (hγ : γ ≠ 0)
    (hMQ : ∀ x ∈ M, γ • x ∈ Q) (hQM : ∀ x ∈ Q, γ⁻¹ • x ∈ M) : Q.IsLattice K := by
  have hQ : Q = M.map ((γ • LinearMap.id : (ι → K) →ₗ[K] (ι → K)).restrictScalars (𝓞 K)) := by
    ext y
    refine ⟨fun hy => ⟨γ⁻¹ • y, hQM y hy, by simp [smul_inv_smul₀ hγ]⟩, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact hMQ z hz
  refine ⟨hQ ▸ (IsLattice.fg (A := K) (M := M)).map _, eq_top_iff.2 ?_⟩
  rw [← IsLattice.span_eq_top (A := K) (M := M), span_le]
  intro z hz
  rw [show z = γ⁻¹ • γ • z by rw [inv_smul_smul₀ hγ]]
  exact smul_mem _ _ (subset_span (hMQ z hz))

variable [IsTotallyComplex K]

/-- **Scaling a sublattice**: if `c ≠ 0` and `cP ⊆ Q`, every `O_K`-stable saturated sublattice `a` of `ψ(P)` has a
partner `b` in `ψ(Q)`, the saturation of its image under `c`, of the same rank with `deg a ≤ deg b + h̄(c)·rk a`.
Multiplication by `c`, `σ_v(c)` on the part at `v` (`act (emb c)`), sends `ψ(P)` into `ψ(Q)` (`ψ_smul`), commutes with
`O_K`, is injective and has norm `|σ_v(c)|` on the part at `v`, so `PlaceLattice.deg_le_img` applies. -/
theorem exists_smul_sublattice (X : KLattice K ι) (P Q : Submodule (𝓞 K) (ι → K)) [P.IsLattice K]
    [Q.IsLattice K] {c : K} (hc : c ≠ 0) (hPQ : ∀ x ∈ P, c • x ∈ Q) (a : (X.withLattice P).toPlaceLattice.S) :
    ∃ b : (X.withLattice Q).toPlaceLattice.S,
      (X.withLattice Q).toPlaceLattice.slopeLattice.rk b = (X.withLattice P).toPlaceLattice.slopeLattice.rk a ∧
        (X.withLattice P).toPlaceLattice.slopeLattice.deg a ≤
          (X.withLattice Q).toPlaceLattice.slopeLattice.deg b +
            logScale c * (X.withLattice P).toPlaceLattice.slopeLattice.rk a := by
  set φ : Space K ι →L[ℝ] Space K ι :=
    LinearMap.toContinuousLinearMap ((act part (emb c) : Space K ι →ₗ[ℂ] Space K ι).restrictScalars ℝ)
  have hφ (y : Space K ι) : φ y = act part (emb c) y := rfl
  have hσ (v : Pl K) : emb c v ≠ 0 := (map_ne_zero v.1.embedding).2 hc
  have hφΛ : ∀ y ∈ (X.withLattice P).lattice, φ y ∈ (X.withLattice Q).lattice := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨c • x, hPQ x hx, X.ψ_smul c x⟩
  have hinj : Function.Injective φ := fun y y' h => ext_coord fun p => by
    have h' := congrArg (coord p) h
    rw [hφ, hφ, coord_act, coord_act] at h'
    exact mul_left_cancel₀ (hσ p.2) h'
  have hcomm (k : 𝓞 K) (y : Space K ι) : φ (act part (emb (k : K)) y) = act part (emb (k : K)) (φ y) := by
    rw [hφ, hφ, act_mul, act_mul, mul_comm]
  obtain ⟨hrk, hdeg⟩ := (X.withLattice P).toPlaceLattice.deg_le_img φ hφΛ hinj
    (h := fun v : Pl K => Real.log ‖v.1.embedding c‖) (fun v y hy => by
      rw [hφ, act_of_mem_part _ hy, norm_smul]
      exact (congrArg (· * ‖y‖) (Real.exp_log (norm_pos_iff.2 (hσ v)))).symm.le) a
  exact ⟨⟨img φ a.1, (X.withLattice Q).stable.img hcomm a.2⟩, hrk, hdeg⟩

/-- **The range under a sandwich** (the frame lemma of (R′)): for lattices `N = X.M ⊆ Q = γM` (`γ ≠ 0`; `γM ⊆ Q` and
`γ⁻¹Q ⊆ M`) with the metrics of `X`, `μ_max(M) ≤ μ(M) + U` gives `μ_max(N) ≤ μ(N) + U + 2·log[Q : N]/rk`, in the units
`μ ↦ 2μ + s` (`rescale s`; the archive's for `s = archShift K`), `rk = [K:ℚ]·|ι|`. A sublattice of `ψ(N)` lies in
`ψ(Q)`, and its image under `γ⁻¹` in `ψ(M)` (`exists_smul_sublattice`), at the cost `h̄(γ⁻¹)`; scaling `M` by `γ`
costs `h̄(γ) = −h̄(γ⁻¹)` (`logScale_inv`), the image of `ψ(M)` being of full rank, so all of `ψ(Q)`:
`μ(M) ≤ μ(Q) + h̄(γ)`; and `μ(N) = μ(Q) − log[Q : N]/rk` (`slope_withLattice`). -/
theorem slopeLe_rescale_of_le_smul (X : KLattice K ι) (M Q : Submodule (𝓞 K) (ι → K)) [M.IsLattice K]
    [Q.IsLattice K] {γ : K} (hγ : γ ≠ 0) (hMQ : ∀ x ∈ M, γ • x ∈ Q) (hQM : ∀ x ∈ Q, γ⁻¹ • x ∈ M)
    (hXQ : X.M ≤ Q) (s U : ℝ)
    (hU : ((X.withLattice M).toPlaceLattice.slopeLattice.rescale s).SlopeLe
      (((X.withLattice M).toPlaceLattice.slopeLattice.rescale s).deg ⊤ /
        ((X.withLattice M).toPlaceLattice.slopeLattice.rescale s).rk ⊤ + U)) :
    (X.toPlaceLattice.slopeLattice.rescale s).SlopeLe
      ((X.toPlaceLattice.slopeLattice.rescale s).deg ⊤ / (X.toPlaceLattice.slopeLattice.rescale s).rk ⊤ + U +
        2 * Real.log (X.M.toAddSubgroup.relIndex Q.toAddSubgroup) / (finrank ℚ K * Fintype.card ι)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact SlopeFrame.SlopeLattice.slopeLe_of_rk_top_eq_zero (show (X.toPlaceLattice.slopeLattice.rescale s).rk ⊤ = 0
      from (rk_top X).trans (by rw [Fintype.card_eq_zero, mul_zero])) _
  set R : ℝ := finrank ℚ K * Fintype.card ι
  have hR : 0 < R := mul_pos (Nat.cast_pos.2 finrank_pos) (Nat.cast_pos.2 Fintype.card_pos)
  have hrk (Y : KLattice K ι) : (Y.toPlaceLattice.slopeLattice.rk ⊤ : ℝ) = R := by
    rw [rk_top]
    push_cast
    rfl
  have harch (Y : KLattice K ι) : (Y.toPlaceLattice.slopeLattice.rescale s).deg ⊤ /
      (Y.toPlaceLattice.slopeLattice.rescale s).rk ⊤ = 2 * (Y.toPlaceLattice.slopeLattice.deg ⊤ / R) + s := by
    show (2 * Y.toPlaceLattice.slopeLattice.deg ⊤ + s * Y.toPlaceLattice.slopeLattice.rk ⊤) /
      (Y.toPlaceLattice.slopeLattice.rk ⊤ : ℝ) = _
    rw [hrk]
    field_simp
  rw [harch, SlopeFrame.SlopeLattice.slopeLe_rescale] at hU
  rw [harch, SlopeFrame.SlopeLattice.slopeLe_rescale]
  -- scaling `M` by `γ`: the image of `ψ(M)` is all of `ψ(Q)`, so `μ(M) ≤ μ(Q) + h̄(γ)`
  obtain ⟨t, ht, htd⟩ := exists_smul_sublattice X M Q hγ hMQ ⊤
  have htop : t = ⊤ := eq_of_le_of_not_lt le_top fun hlt =>
    ((X.withLattice Q).toPlaceLattice.slopeLattice.rk_strictMono hlt).ne (by rw [ht, rk_top, rk_top])
  rw [htop, hrk] at htd
  have hMQ' : (X.withLattice M).toPlaceLattice.slopeLattice.deg ⊤ / R ≤
      (X.withLattice Q).toPlaceLattice.slopeLattice.deg ⊤ / R + logScale γ := by
    rw [div_add' _ _ _ hR.ne', div_le_div_iff_of_pos_right hR]
    linarith
  -- the index: `μ(N) = μ(Q) − log[Q : N]/rk`
  have hidx : X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ =
      (X.withLattice Q).toPlaceLattice.slopeLattice.deg ⊤ / (X.withLattice Q).toPlaceLattice.slopeLattice.rk ⊤ -
        Real.log (X.M.toAddSubgroup.relIndex Q.toAddSubgroup) / (X.withLattice Q).toPlaceLattice.slopeLattice.rk ⊤ :=
    (X.withLattice Q).slope_withLattice hXQ
  rw [hrk, hrk] at hidx
  -- the sublattices of `ψ(N)`, through `γ⁻¹`
  intro a
  obtain ⟨b, hb, hab⟩ := exists_smul_sublattice X X.M M (inv_ne_zero hγ) (fun x hx => hQM x (hXQ hx)) a
  have hbU := hU b
  rw [hb] at hbU
  rw [logScale_inv] at hab
  show (X.withLattice X.M).toPlaceLattice.slopeLattice.deg a ≤
    _ * ((X.withLattice X.M).toPlaceLattice.slopeLattice.rk a : ℝ)
  have hl : (2 * ((X.withLattice M).toPlaceLattice.slopeLattice.deg ⊤ / R) + s + U - s) / 2 - logScale γ ≤
      (2 * (X.toPlaceLattice.slopeLattice.deg ⊤ / R) + s + U +
        2 * Real.log (X.M.toAddSubgroup.relIndex Q.toAddSubgroup) / R - s) / 2 := by
    rw [mul_div_assoc 2 (Real.log _)]
    linarith
  calc (X.withLattice X.M).toPlaceLattice.slopeLattice.deg a
      ≤ ((2 * ((X.withLattice M).toPlaceLattice.slopeLattice.deg ⊤ / R) + s + U - s) / 2 - logScale γ) *
          (X.withLattice X.M).toPlaceLattice.slopeLattice.rk a := by rw [sub_mul]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _)

end KLattice

namespace ZetaBalance

open Pointwise

attribute [local instance] InnerProductSpace.complexToReal

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- **The range of `M_ω`** with constant `U₀`: in every realising frame, at every word, the image of `M_ω` in the
frame's coordinates is an `O_K`-lattice with `μ_max(M_ω) ≤ μ(M_ω) + U₀` for the source's metrics, in the archive's
units. -/
def SourceRangeLe (U₀ : ℝ) : Prop :=
  ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω,
    let M := (b.M ω).map ((c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K))
    ∃ _ : M.IsLattice C.K, (((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale (archShift C.K)).SlopeLe
      ((((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale (archShift C.K)).deg ⊤ /
        (((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale (archShift C.K)).rk ⊤ + U₀)

/-- **The maximal slope of `M_ω`** at most `B`: in every realising frame, at every word, the image of `M_ω` in the
frame's coordinates is an `O_K`-lattice with `μ_max(M_ω) ≤ B` for the source's metrics, in the archive's units. -/
def MuMaxLe (B : ℝ) : Prop :=
  ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω,
    let M := (b.M ω).map ((c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K))
    ∃ _ : M.IsLattice C.K, (((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale (archShift C.K)).SlopeLe B

/-- **The range of `M_ω` from its maximal slope and (F) + (V)**: `μ_max(M_ω) ≤ B` and the piece `SlopeFV` give
`μ_max(M_ω) − μ(M_ω) ≤ B + c_F`. The index bookkeeping (V), `μ(N_ω) = μ(M_ω) + idx_ω`
(`KLattice.slope_rescale_withLattice_eq`, the indices taken in `V_ω`), turns `μ(N_ω) ≥ −c_F + idx_ω` into
`μ(M_ω) ≥ −c_F`. -/
theorem sourceRangeLe_of_muMaxLe (hFV : b.SlopeFV) {B : ℝ} (hB : b.MuMaxLe B) : b.SourceRangeLe (B + b.cF) := by
  intro F c eC hF ω
  obtain ⟨_, hle⟩ := hB F c eC hF ω
  set f := (c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K)
  refine ⟨‹_›, hle.mono ?_⟩
  have hi (P Q : Submodule (𝓞 C.K) (b.Vs ω)) :
      (P.map f).toAddSubgroup.relIndex (Q.map f).toAddSubgroup = P.toAddSubgroup.relIndex Q.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (c ω).injective
  have hrk : Module.finrank C.K (b.Vs ω) = Fintype.card (F.n ω) := by
    rw [(c ω).finrank_eq, Module.finrank_fintype_fun_eq_card]
  have h := hFV.2.2 F c eC hF ω
  rw [KFrame.frame_N, idx, hrk, ← hi (b.M ω), ← hi (b.N ω), ← hF.2.1 ω] at h
  have hV := h.trans_eq
    (((F.src ω).withLattice ((b.M ω).map f)).slope_rescale_withLattice_eq (F.src ω).M (archShift C.K))
  linarith

variable {b} in
/-- **`RangeLe` is monotone** in the constant. -/
theorem RangeLe.mono {U U' : ℝ} (h : b.RangeLe U) (hU : U ≤ U') : b.RangeLe U' := fun F c eC hF ω =>
  (h F c eC hF ω).mono (by linarith)

/-- **(R′) from the range of `M_ω` and certificates**: if `μ_max(M_ω) ≤ μ(M_ω) + U₀` (`SourceRangeLe`) and every
word has a gain certificate (`GainCert`) of colength `2·log[M_ω : L]/rk ≤ λ`, then `μ_max(N_ω) ≤ μ(N_ω) + U₀ + λ`
in every realising frame. In the frame's coordinates the certificate sandwiches the source, `N_ω ⊆ γM_ω`
(`GainCert.N_le`), with `[γM_ω : N_ω] ≤ [M_ω : L]` (`GainCert.colength_le`), so
`KLattice.slopeLe_rescale_of_le_smul` applies with `Q = γM_ω`. -/
theorem rangeLe_of_cert {U₀ : ℝ} (hS : b.SourceRangeLe U₀) {lam : ℝ}
    (hc : ∀ ω, ∃ c : b.GainCert ω, 2 * Real.log (c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup) /
      (Module.finrank ℚ C.K * Module.finrank C.K (b.Vs ω)) ≤ lam) : b.RangeLe (U₀ + lam) := by
  intro F c eC hF (ω : b.Ω)
  obtain ⟨g, hg⟩ := hc ω
  obtain ⟨_, hM⟩ := hS F c eC hF ω
  set f := (c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K)
  set γ : C.K := (g.β : C.K) / g.α
  have hγ : γ ≠ 0 := g.ratio_ne
  have hf (t : C.K) (φ : b.Vs ω) : f (t • φ) = t • f φ := (c ω).map_smul t φ
  -- `Q = γM_ω` in the frame's coordinates
  have hMQ : ∀ y ∈ (b.M ω).map f, γ • y ∈ (γ • b.M ω).map f := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨γ • φ, Submodule.smul_mem_pointwise_smul _ _ _ hφ, hf γ φ⟩
  have hQM : ∀ y ∈ (γ • b.M ω).map f, γ⁻¹ • y ∈ (b.M ω).map f := by
    rintro _ ⟨_, hx, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact ⟨φ, hφ, by rw [hf, inv_smul_smul₀ hγ]⟩
  have := KLattice.isLattice_of_smul hγ hMQ hQM
  have hXQ : (F.src ω).M ≤ (γ • b.M ω).map f := by
    rw [hF.2.1 ω]
    exact Submodule.map_mono g.N_le
  have h := (F.src ω).slopeLe_rescale_of_le_smul ((b.M ω).map f) ((γ • b.M ω).map f) hγ hMQ hQM hXQ
    (archShift C.K) U₀ hM
  -- the colength
  obtain ⟨h0, hcol⟩ := g.colength_le
  have hi : (F.src ω).M.toAddSubgroup.relIndex ((γ • b.M ω).map f).toAddSubgroup =
      (b.N ω).toAddSubgroup.relIndex (γ • b.M ω).toAddSubgroup := by
    rw [hF.2.1 ω, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (c ω).injective
  have hrk : Module.finrank C.K (b.Vs ω) = Fintype.card (F.n ω) := by
    rw [(c ω).finrank_eq, Module.finrank_fintype_fun_eq_card]
  have hlog : 2 * Real.log ((F.src ω).M.toAddSubgroup.relIndex ((γ • b.M ω).map f).toAddSubgroup) /
      (Module.finrank ℚ C.K * Fintype.card (F.n ω)) ≤ lam := by
    refine le_trans ?_ hg
    rw [hi, hrk]
    have hl := Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)) (Nat.cast_le.2 hcol)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  show ((F.src ω).toPlaceLattice.slopeLattice.rescale (archShift C.K)).SlopeLe
    (((F.src ω).toPlaceLattice.slopeLattice.rescale (archShift C.K)).deg ⊤ /
      ((F.src ω).toPlaceLattice.slopeLattice.rescale (archShift C.K)).rk ⊤ + (U₀ + lam))
  exact h.mono (by linarith)

end SharpObj

/-- **The bound on `μ_max(M_ω)`**, eventually in the design: at every admissible design with `ε` small and `x` large,
at every translate `u ∈ A₀`, some `B` with `B + c_F^{exact} ≤ x^{4ε}Σ_t a_t/8` bounds the maximal slope of the
construction's lattice of integral forms in every realising frame (`SharpObj.MuMaxLe`), where
`c_F^{exact} = HermForms.cFx` is the exact constant of (F) (at most `x^{4ε}Σ_t a_t/8`, `cFx_le`). Not proved in the
library: it needs an integrality bound for the Petersson values of the integral forms, whose values at the class
representatives lie in the Fock duals `Δ` of the bideterminant lattices `∇_O`. -/
def SharpMuMax : Prop :=
  EventuallyAdm (fun Dg => Dg.Adm) fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ∃ B : ℝ,
    B + HermForms.cFx Dg.R.k (sharpLam0 Dg u) (sharpST Dg u) ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 ∧
      ((sharpCons Dg).obj u).MuMaxLe B

/-- **Gain certificates of small colength**, eventually in the design: at every admissible design with `ε` small and
`x` large, at every translate `u ∈ A₀`, every word of the construction has a gain certificate (`SharpObj.GainCert`)
with `2·log[M_ω : L]/rk ≤ x^{4ε}Σ_t a_t/8`, `rk = [K:ℚ]·dim V_ω`. -/
def SharpCertSmall : Prop :=
  EventuallyAdm (fun Dg => Dg.Adm) fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ,
    ∀ ω, ∃ c : ((sharpCons Dg).obj u).GainCert ω,
      2 * Real.log (c.L.toAddSubgroup.relIndex (((sharpCons Dg).obj u).M ω).toAddSubgroup) /
          (Module.finrank ℚ (sharpCons Dg).C.K * Module.finrank (sharpCons Dg).C.K (((sharpCons Dg).obj u).Vs ω)) ≤
        x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8

/-- **(R′) from the bound on `μ_max(M_ω)` and small certificates** (`SharpRange`): eventually in the design
(`EventuallyAdm.and`), at every translate, with `c_F^{exact}` the exact constant of (F) and `T = x^{4ε}Σ_t a_t/8`:
* the object with its slack `c_F` replaced by `c_F^{exact}` meets (F) + (V) (`SharpObj.slopeFV_exact`, as in
  `sharpSlopeFV`), and has the object's frames, so `μ_max(M_ω) − μ(M_ω) ≤ B + c_F^{exact}`
  (`SharpObj.sourceRangeLe_of_muMaxLe`);
* the certificates give `μ_max(N_ω) − μ(N_ω) ≤ B + c_F^{exact} + T` (`SharpObj.rangeLe_of_cert`);
* so `U = max(B + c_F^{exact} + T, 0)` has `0 ≤ U ≤ 2T`. -/
theorem sharpRange_of_cert (hM : SharpMuMax) (hC : SharpCertSmall) : SharpRange := by
  obtain ⟨ε₁, hε₁, H⟩ := hM.and hC
  refine ⟨ε₁, hε₁, fun ε hε hle => ?_⟩
  obtain ⟨x₀, hx₀⟩ := H ε hε hle
  refine ⟨x₀, fun {S κ x X} Dg hx hA u hu => ?_⟩
  obtain ⟨hm, hc⟩ := hx₀ Dg hx hA
  obtain ⟨B, hB, hMu⟩ := hm u hu
  set T := x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 with hTdef
  set c₀ := HermForms.cFx Dg.R.k (sharpLam0 Dg u) (sharpST Dg u)
  have hT : 0 ≤ T := div_nonneg (mul_nonneg (Real.rpow_nonneg hA.big.pos.le _)
    (Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le)) (by norm_num)
  -- (F) + (V) with the exact constant `c₀`, for the object with `c_F := c₀`, which has the object's frames
  obtain ⟨h₀, h₁⟩ := exists_sharpSG hA
  let b' : SharpObj Dg (sharpCoeff Dg) := { sharpObj Dg u with cF := c₀ }
  have hFV : b'.SlopeFV := b'.slopeFV_exact h₀ h₁ (fun _ => rfl) (fun _ => Setting.Ranks.wt0_antitone _ _)
    (HermForms.cFx_nonneg _) (fun _ => le_rfl) (cFx_le hA u)
  have hS : ((sharpCons Dg).obj u).SourceRangeLe (B + c₀) := b'.sourceRangeLe_of_muMaxLe hFV hMu
  refine ⟨max (B + c₀ + T) 0, le_max_right _ _, max_le (by linarith) (by linarith), ?_⟩
  exact (((sharpCons Dg).obj u).rangeLe_of_cert hS (hc u hu)).mono (le_max_left _ _)

end ZetaBalance
