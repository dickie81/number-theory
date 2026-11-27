import SharpInputs
import GenIndex

/-!
# The gain's certificate: the index term from two elements and a sublattice

The reduction of the gain in (G↓) (`SharpObj.Gain`) to a per-word certificate, a statement about indices alone. The
index term is `idx_ω = 2·logIdx(N_ω, M_ω)/rk` (`SharpObj.idx_eq_logIdx`, the generalised index of module `GenIndex`),
`rk = [K:ℚ]·dim V_ω`, and the source is `N_ω = 𝔞_ω⁻¹M_ω ∩ B_ω⁻¹(C_u)` (`PeriodTarget.Nsrc`).

**The certificate** (`SharpObj.GainCert`) at a word `ω`: generators `α`, `β ∈ O_K∖0` of `𝔞⁺ = (α)` and `𝔞⁻ = (β)`, and
an `O_K`-submodule `L ⊆ M_ω` of finite index with `B_ω((β/α)L) ⊆ C_u`. For principal `𝔞^±` the fractional part of the
source is a scaling, `𝔞_ω⁻¹M_ω = (β/α)M_ω` (`SharpObj.N_eq_of_principal`): `x` lies in it iff `αx ∈ βM_ω`. So the
certificate sandwiches the source, `(β/α)L ⊆ N_ω ⊆ (β/α)M_ω` (`GainCert.le_N`, `GainCert.N_le`).

**The colength bound** (`GainCert.colength_le`): the colength of `N_ω` in `(β/α)M_ω` is at most `[M_ω : L]`, as
scaling keeps indices (`Submodule.relIndex_smul_smul`) and `N_ω` contains `(β/α)L`. It is meant for the range (R′) of
the frame loss (`ZetaBalance.SharpRange`, with `U = μ_max(M_ω) + c_F + 2·log[M_ω : L]/rk`): in a realising frame,
`N_ω ⊆ (β/α)M_ω` gives `μ_max(N_ω) ≤ μ_max((β/α)M_ω)`, the index gives
`μ(N_ω) = μ((β/α)M_ω) − 2·log[(β/α)M_ω : N_ω]/rk` (`KLattice.slope_rescale_withLattice_eq`), the scaling moves the
slopes of all sublattices of `M_ω` by one amount, and (F) bounds `μ(M_ω)` below by `−c_F`.

**The index lemma** (`GainCert.idx_ge`): `idx_ω ≥ (2/[K:ℚ])·log|N_{K/ℚ}(α/β)| − (2/rk)·log[M_ω : L]`. By the cocycle
rule through `(β/α)M_ω` (commensurable with `M_ω`, `Submodule.relIndex_smul_ne_zero`),
`logIdx(N_ω, M_ω) = −log[(β/α)M_ω : N_ω] + logIdx((β/α)M_ω, M_ω)`; the first term is at least `−log[M_ω : L]` (the
colength bound) and the second is `d·log|N(α/β)|` (`Submodule.logIdx_smul`), `d = dim V_ω`. Dividing by `rk/2` needs
`d > 0`: for `V_ω = 0` the index term is `0`.

**The gain** (`SharpObj.gain_of_cert`): if `0 ≤ c_G ≤ x^{4ε}Σ_t a_t/8` and every word has a certificate whose bound
exceeds `Σ_tΣ_j ASK − m(Σ_t a_t)·log(g₀g₁) + Fo − c_G`, the gain holds. The certificate's `L` is built by gluing
finitely many local conditions (`Submodule.relIndex_inf_iInf_le`), and with `α`, `β` from `ℚ(√−d)` the norm term is a
norm from there (`NumberField.log_abs_norm_map_div`).
-/

namespace ZetaBalance

open NumberField Pointwise

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}

/-- **The index term as a generalised index**: `idx_ω = 2·logIdx(N_ω, M_ω)/rk`, `rk = [K:ℚ]·dim V_ω`. -/
theorem idx_eq_logIdx (b : SharpObj Dg C) (ω : b.Ω) :
    b.idx ω = 2 * AddSubgroup.logIdx (b.N ω).toAddSubgroup (b.M ω).toAddSubgroup /
      (Module.finrank ℚ C.K * Module.finrank C.K (b.Vs ω)) :=
  rfl

/-- **The source for principal `𝔞^±`**: if `𝔞⁺ = (α)` and `𝔞⁻ = (β)` with `α ≠ 0`, then `𝔞_ω⁻¹M_ω = (β/α)M_ω`
(`x` lies in it iff `αx ∈ βM_ω`), so `N_ω = (β/α)M_ω ∩ B_ω⁻¹(C_u)`. -/
theorem N_eq_of_principal (b : SharpObj Dg C) (ω : b.Ω) {α β : 𝓞 C.K} (hα : α ≠ 0)
    (hp : b.𝔞p ω = Ideal.span {α}) (hn : b.𝔞n ω = Ideal.span {β}) :
    b.N ω = ((β : C.K) / α) • b.M ω ⊓
      (PeriodTarget.Ctgt C.τK b.tw).comap ((b.P.P b.μ0 ω).restrictScalars (𝓞 C.K)) := by
  have hαK : (α : C.K) ≠ 0 := by exact_mod_cast hα
  have hc : ∀ (t : 𝓞 C.K) (v : b.Vs ω), t • v = (t : C.K) • v := fun t v => (algebraMap_smul C.K t v).symm
  rw [N, PeriodTarget.Nsrc, hp, hn, Submodule.ideal_span_singleton_smul]
  congr 1
  ext v
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · obtain ⟨m, hm, hmv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h α (Ideal.mem_span_singleton_self α))
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨m, hm, ?_⟩
    rw [hc, hc] at hmv
    rw [div_eq_inv_mul, mul_smul, hmv, inv_smul_smul₀ hαK]
  · obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨r • m, (b.M ω).smul_mem r hm, ?_⟩
    rw [hc, hc, hc, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp

/-- **A gain certificate** at a word `ω` (the certificate of the index lemma): generators `α`, `β` of `𝔞⁺`, `𝔞⁻`, and
an `O_K`-submodule `L ⊆ M_ω` of finite index whose multiple `(β/α)L` the period map sends into the target `C_u`. -/
structure GainCert (b : SharpObj Dg C) (ω : b.Ω) where
  /-- The generator of `𝔞⁺`. -/
  α : 𝓞 C.K
  /-- The generator of `𝔞⁻`. -/
  β : 𝓞 C.K
  /-- `α ≠ 0`. -/
  α_ne : α ≠ 0
  /-- `β ≠ 0`. -/
  β_ne : β ≠ 0
  /-- `𝔞⁺ = (α)`. -/
  hp : b.𝔞p ω = Ideal.span {α}
  /-- `𝔞⁻ = (β)`. -/
  hn : b.𝔞n ω = Ideal.span {β}
  /-- The sublattice `L`. -/
  L : Submodule (𝓞 C.K) (b.Vs ω)
  /-- `L ⊆ M_ω`. -/
  le_M : L ≤ b.M ω
  /-- `L` has finite index in `M_ω`. -/
  finite : L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup ≠ 0
  /-- `B_ω((β/α)L) ⊆ C_u`. -/
  into : ∀ φ ∈ L, b.P.P b.μ0 ω (((β : C.K) / (α : C.K)) • φ) ∈ PeriodTarget.Ctgt C.τK b.tw

namespace GainCert

variable {b : SharpObj Dg C} {ω : b.Ω} (c : b.GainCert ω)

/-- **The scale is nonzero**: `β/α ≠ 0`. -/
theorem ratio_ne : (c.β : C.K) / c.α ≠ 0 :=
  div_ne_zero (by exact_mod_cast c.β_ne) (by exact_mod_cast c.α_ne)

/-- **The lower sandwich**: `(β/α)L ⊆ N_ω`, as `L ⊆ M_ω` and `B_ω((β/α)L) ⊆ C_u`. -/
theorem le_N : ((c.β : C.K) / c.α) • c.L ≤ b.N ω := by
  rw [N_eq_of_principal b ω c.α_ne c.hp c.hn]
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨Submodule.smul_mem_pointwise_smul _ _ _ (c.le_M hφ), c.into φ hφ⟩

/-- **The upper sandwich**: `N_ω ⊆ (β/α)M_ω = 𝔞_ω⁻¹M_ω`. -/
theorem N_le : b.N ω ≤ ((c.β : C.K) / c.α) • b.M ω := by
  rw [N_eq_of_principal b ω c.α_ne c.hp c.hn]
  exact inf_le_left

/-- **The colength bound**: `N_ω` has finite index in `(β/α)M_ω`, at most the certificate's colength `[M_ω : L]`, as
`(β/α)L ⊆ N_ω` and `[(β/α)M_ω : (β/α)L] = [M_ω : L]`. With `N_ω ⊆ (β/α)M_ω` (`N_le`) this is what the range (R′)
reads. -/
theorem colength_le :
    (b.N ω).toAddSubgroup.relIndex (((c.β : C.K) / c.α) • b.M ω).toAddSubgroup ≠ 0 ∧
      (b.N ω).toAddSubgroup.relIndex (((c.β : C.K) / c.α) • b.M ω).toAddSubgroup ≤
        c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup := by
  have h := Submodule.relIndex_smul_smul c.ratio_ne c.L (b.M ω)
  have hle : (((c.β : C.K) / c.α) • c.L).toAddSubgroup ≤ (b.N ω).toAddSubgroup := c.le_N
  exact ⟨mt (AddSubgroup.relIndex_eq_zero_of_le_left hle) (h ▸ c.finite),
    h ▸ AddSubgroup.relIndex_le_of_le_left hle (h ▸ c.finite)⟩

/-- **The index lemma**: `idx_ω ≥ (2/[K:ℚ])·log|N_{K/ℚ}(α/β)| − (2/rk)·log[M_ω : L]` for a lattice `M_ω` in a nonzero
`V_ω`. By the cocycle rule through `(β/α)M_ω`, `logIdx(N_ω, M_ω) = −log[(β/α)M_ω : N_ω] + d·log|N(α/β)|`, and the
colength is at most `[M_ω : L]` (`colength_le`). -/
theorem idx_ge (hM : (b.M ω).IsLattice C.K) (hV : 0 < Module.finrank C.K (b.Vs ω)) :
    2 * Real.log |(Algebra.norm ℚ ((c.α : C.K) / c.β) : ℝ)| / Module.finrank ℚ C.K -
      2 * Real.log (c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup) /
        (Module.finrank ℚ C.K * Module.finrank C.K (b.Vs ω)) ≤ b.idx ω := by
  set γ : C.K := (c.β : C.K) / c.α
  set d : ℝ := (Module.finrank C.K (b.Vs ω) : ℝ)
  have hγ : γ ≠ 0 := c.ratio_ne
  obtain ⟨h0, hcol⟩ := c.colength_le
  have hsc := Submodule.relIndex_smul_ne_zero (b.M ω) hγ
  have hNle : (b.N ω).toAddSubgroup ≤ (γ • b.M ω).toAddSubgroup := c.N_le
  -- `logIdx(N, M) = logIdx(N, γM) + logIdx(γM, M)`
  have hadd := AddSubgroup.logIdx_add (Y := (γ • b.M ω).toAddSubgroup)
    ⟨by rw [AddSubgroup.relIndex_eq_one.2 hNle]; exact one_ne_zero, h0⟩ ⟨hsc.2, hsc.1⟩
  rw [AddSubgroup.logIdx_of_le hNle, Submodule.logIdx_smul (b.M ω) hγ] at hadd
  -- `log|N(β/α)| = −log|N(α/β)|`
  have hαβ : (Algebra.norm ℚ ((c.α : C.K) / c.β) : ℝ) * Algebra.norm ℚ γ = 1 := by
    rw [← Rat.cast_mul, ← map_mul, div_mul_div_cancel₀ (by exact_mod_cast c.β_ne), div_self (by exact_mod_cast c.α_ne),
      map_one, Rat.cast_one]
  have hlog : Real.log |(Algebra.norm ℚ γ : ℝ)| = -Real.log |(Algebra.norm ℚ ((c.α : C.K) / c.β) : ℝ)| := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← Real.log_mul (abs_ne_zero.2 (left_ne_zero_of_mul_eq_one hαβ))
      (abs_ne_zero.2 (right_ne_zero_of_mul_eq_one hαβ)), ← abs_mul, hαβ, abs_one, Real.log_one]
  -- the colength
  have hlc : Real.log ((b.N ω).toAddSubgroup.relIndex (γ • b.M ω).toAddSubgroup) ≤
      Real.log (c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup) :=
    Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)) (Nat.cast_le.2 hcol)
  have hk : (0 : ℝ) < Module.finrank ℚ C.K := Nat.cast_pos.2 Module.finrank_pos
  have hd : 0 < d := Nat.cast_pos.2 hV
  set ℓ := Real.log |(Algebra.norm ℚ ((c.α : C.K) / c.β) : ℝ)|
  set lam := Real.log (c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup)
  have key : 2 * ℓ / Module.finrank ℚ C.K - 2 * lam / (Module.finrank ℚ C.K * d) =
      2 * (d * ℓ - lam) / (Module.finrank ℚ C.K * d) := by
    field_simp
  rw [idx_eq_logIdx, hadd, hlog, key]
  exact div_le_div_of_nonneg_right (by linarith) (mul_pos hk hd).le

end GainCert

/-- **The gain from certificates**: if `0 ≤ c_G ≤ x^{4ε}Σ_t a_t/8`, every `M_ω` is a lattice in a nonzero `V_ω`, and
every word has a certificate (`GainCert`) whose bound `(2/[K:ℚ])·log|N(α/β)| − (2/rk)·log[M_ω : L]` is at least
`Σ_tΣ_j ASK(a_t, t, w_{u,j}) − m(Σ_t a_t)·log(g₀g₁) + Fo − c_G`, then the gain holds at `u` (`GainCert.idx_ge`). -/
theorem gain_of_cert (b : SharpObj Dg C) {u : S.A} (h0 : 0 ≤ b.cG)
    (h1 : b.cG ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8) (hM : ∀ ω, (b.M ω).IsLattice C.K)
    (hV : ∀ ω, 0 < Module.finrank C.K (b.Vs ω))
    (hc : ∀ ω, ∃ c : b.GainCert ω,
      ∑ s ∈ Dg.TT, ∑ j, S.ASK (Dg.a s) s (Dg.w u j) - Dg.m * (∑ s ∈ Dg.TT, Dg.a s) * Real.log (Dg.g₀ * Dg.g₁) +
          b.Fo - b.cG ≤
        2 * Real.log |(Algebra.norm ℚ ((c.α : C.K) / c.β) : ℝ)| / Module.finrank ℚ C.K -
          2 * Real.log (c.L.toAddSubgroup.relIndex (b.M ω).toAddSubgroup) /
            (Module.finrank ℚ C.K * Module.finrank C.K (b.Vs ω))) :
    b.Gain u := by
  refine ⟨h0, h1, fun ω => ?_⟩
  obtain ⟨c, hc⟩ := hc ω
  exact hc.trans (c.idx_ge (hM ω) (hV ω))

end SharpObj

end ZetaBalance
