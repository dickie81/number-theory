import CMTorsion
import HermGS
import MvTay
import FormalQuad

/-!
# The Gaussian factorisation of the theta at an inert prime: `θ = c₀·exp(−Ψ)·U`

D1b-6 of the D1b plan. For `θ ∈ Th(C)`, `C ⊆ ℂ^ι` an `ω`-stable self-dual theta lattice for `H = s·Σ z·w̄`
(`s = 1/area(Lc)`, `Lc = δ(ℤ + ℤω)`, `d ≡ 7 (mod 8)`), an inert `ℓ ≥ 5` and an `ℓ`-adapted orthogonal basis `b_i` of
`C` with unit diagonal `u_i` (`HermGS.GSBasis`), the Taylor series of `θ` at the point `Σ_i ε·L(X_i)·δ⁻¹b_i`
(`thetaLT`; `L = log_LT`, `ε` the CM-b unit) is `c₀·exp(−Ψ)·U` with `U` integral and the explicit Gaussian
`Ψ = Σ_i u_i·(γ/2)·serAB(X_i, X_i)` (`gaussPsi`), `γ` the classification constant (`theta_gauss`).

**Four squares and the comparison.** `u_i = a_i² + b_i² + c_i² + e_i²` gives the four-squares isometry `g`
(`HermGS.orth4_spec`), `g(Lc^{Fin 4 × ι})` `ℓ`-adapted to `C⁴`, and `θ^{⊗4} = c·Θ_g`
(`ThetaCompare.theta_compare`). `Θ_g = (Iop(Lc^K, g⁻¹C⁴) F0) ∘ g⁻¹` is a finite sum of products of one-variable
factors `facT(c)(w) = th0_t(w + c)·e^{−πs(w c̄ + c c̄/2)}` over representatives `q` with `M·q ∈ Lc^K`, `ℓ ∤ M`
(`Iop_F0c_eq_sum`, `opU_F0c`). So `Θ_g` is analytic, and so is `θ`: `θ(v)·θ(a)³ = θ^{⊗4}(v, a, a, a)` at a point with
`θ(a) ≠ 0` (Mathlib has no Hartogs theorem, and `Th` asks only differentiability).

**Lubin–Tate series** (`ltS`): the Taylor series `mtay G` carried to `ℂ_ℓ` and evaluated at a tuple of series. It is
linear, takes products of one-variable functions of the coordinates to products (`ltS_prod_coord`), linear changes
of coordinates to substitutions (`ltS_comp_linear`) and tensor powers to tensor powers (`ltS_tens4`). The change from
the basis coordinates `x` (the point `Σ x_{l,i}·slot_l(β_i)`) to `g`'s orthonormal coordinates is the integer block
matrix `M_{(k,i),(l,j)} = [i = j]·Q_i(k, l)` (`quatM`; `g(Mx) = V₄x` by `HermGS.slotV_eq_sum`), so the points are
`ε·L(Y_p)`, `Y_p = ⊕_{p′}[M_{pp′}]X_{p′}` (`FormalQuad.linLT`).

**The translates** (`isGB_facT`). Each factor is `K·shS(t + c)` (`facT_eq`); in Lubin–Tate coordinates it is
`exp(−ph)` times a bounded series: `exp(−ph)·U_{t+c}` with `U_{t+c}` integral when `t + c ∉ Lc`
(`CMFormalBiadd.th0_eq_exp_neg_ph_mul`, `CMTorsion.isInt_translate_any`), and `εT·exp(−ph)` up to a constant when
`t + c ∈ Lc`. "Gaussian times bounded" (`IsGB`) is stable under sums, products and integral substitution, so
`θ^{⊗4} = exp(−Σ_p ph(Y_p))·(bounded)` (`isGB_ltS_facT`), bounded meaning `ℓ^k·W` integral for some `k` (`IsBddK`).

**The quadratic part** (`simeq_quad`). `MᵀM = diag(u)` (`quatM_mul`), so `FormalQuad.quad_transfer` and
`FormalQuad.ph_simeq_serAB_diag` give `Σ_p ph(Y_p) ≃ Σ_k Ψ(X_{k,·})`. Hence `(θ·exp(Ψ))^{⊗4}` is bounded
(`IsGB.isBddK_mul_expMv`, `tens4S_expMv`).

**The diagonal trick** (`norm_coeff_pow_four_le`, `isBddK_of_tens4S`): the coefficient of `g^{⊗4}` at `(m, m, m, m)`
is `g_m⁴` (`coeff_tens4S`), so `θ·exp(Ψ)` is bounded, i.e. `c₀` times an integral series.

**Inputs.** CM-a′/b/c/d (`CMUnramified`, `CMInertLubinTate`, `CMThetaOne.CMjIntegral`, `CMs2Unram`) and a Frobenius
lift on `K^ur` (any, or `UnramFrobLift.frobUnram`: `theta_gauss'`); no torsion input. `theta_gauss_core` takes the
CM-b unit and the classification `be ≃ γ·serAB` as hypotheses instead.

**Main declarations:** `thetaLT`, `gaussPsi`, `tens4S`, `norm_coeff_pow_four_le`, `theta_gauss`, `theta_gauss'`,
`theta_gauss_core`; on the way `IsBddK`, `IsGB`, `ltS`, `facT`, `isGB_facT`, `Iop_F0c_eq_sum`, `quatM`,
`simeq_quad`.
-/

namespace ThetaGauss

open PowerSeries CMFormalInert CMFormalBiadd Finset

noncomputable section

/-! ## Series with bounded coefficients -/

section Bdd

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **`‖ℓ^j‖ ≤ 1`** in `ℂ_ℓ`. -/
theorem norm_ell_pow_le_one (j : ℕ) : ‖(ℓ : ℂ_[ℓ]) ^ j‖ ≤ 1 := by
  rw [← Nat.cast_pow]
  exact IsUltrametricDist.norm_natCast_le_one ℂ_[ℓ] _

/-- **Bounded coefficients**: `ℓ^k·F` is integral for some `k`, so that `F` is a constant times an integral
series (`exists_eq_C_mul_of_isBddK`). -/
def IsBddK (F : MvPowerSeries σ ℂ_[ℓ]) : Prop := ∃ k : ℕ, IsIntK (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F)

/-- **Integral series are bounded.** -/
theorem _root_.CMFormalInert.IsIntK.isBddK {F : MvPowerSeries σ ℂ_[ℓ]} (h : IsIntK F) : IsBddK F :=
  ⟨0, by rwa [pow_zero, map_one, one_mul]⟩

/-- **A larger power of `ℓ`** keeps `ℓ^k·F` integral. -/
theorem isIntK_C_pow_mul_mono {F : MvPowerSeries σ ℂ_[ℓ]} {k k' : ℕ} (hk : k ≤ k')
    (h : IsIntK (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F)) : IsIntK (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k') * F) := by
  have e : MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k') * F =
      MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ (k' - k)) * (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F) := by
    rw [← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel hk]
  rw [e]
  exact (isIntK_C (norm_ell_pow_le_one _)).mul h

/-- **Sums of bounded series are bounded.** -/
theorem IsBddK.add {F G : MvPowerSeries σ ℂ_[ℓ]} (hF : IsBddK F) (hG : IsBddK G) : IsBddK (F + G) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨k', hk'⟩ := hG
  refine ⟨max k k', ?_⟩
  rw [mul_add]
  exact (isIntK_C_pow_mul_mono (le_max_left k k') hk).add (isIntK_C_pow_mul_mono (le_max_right k k') hk')

/-- **Products of bounded series are bounded.** -/
theorem IsBddK.mul {F G : MvPowerSeries σ ℂ_[ℓ]} (hF : IsBddK F) (hG : IsBddK G) : IsBddK (F * G) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨k', hk'⟩ := hG
  refine ⟨k + k', ?_⟩
  rw [show MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ (k + k')) * (F * G) =
    (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F) * (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k') * G) by
      rw [pow_add, map_mul]; ring]
  exact hk.mul hk'

/-- **Every `c ∈ ℂ_ℓ` becomes integral** after multiplication by a power of `ℓ` (`‖ℓ‖ < 1`). -/
theorem exists_norm_pow_mul_le (c : ℂ_[ℓ]) : ∃ j : ℕ, ‖(ℓ : ℂ_[ℓ]) ^ j * c‖ ≤ 1 := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hℓ1 : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
    rw [norm_ell_padicC]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓp.out.one_lt)
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc0) hℓ1
  refine ⟨j, ?_⟩
  rw [norm_mul, norm_pow]
  calc ‖(ℓ : ℂ_[ℓ])‖ ^ j * ‖c‖ ≤ ‖c‖⁻¹ * ‖c‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hc0.ne'

/-- **Constant multiples of bounded series are bounded.** -/
theorem IsBddK.C_mul {F : MvPowerSeries σ ℂ_[ℓ]} (hF : IsBddK F) (c : ℂ_[ℓ]) : IsBddK (MvPowerSeries.C c * F) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨j, hj⟩ := exists_norm_pow_mul_le c
  refine ⟨j + k, ?_⟩
  rw [show MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ (j + k)) * (MvPowerSeries.C c * F) =
    MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ j * c) * (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F) by
      rw [pow_add, map_mul, map_mul]; ring]
  exact (isIntK_C hj).mul hk

/-- **Finite sums of bounded series are bounded.** -/
theorem isBddK_sum {κ : Type} (s : Finset κ) {F : κ → MvPowerSeries σ ℂ_[ℓ]} (hF : ∀ i ∈ s, IsBddK (F i)) :
    IsBddK (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert j s hj ih =>
    rw [sum_insert hj]
    exact (hF j (mem_insert_self j s)).add (ih fun i hi => hF i (mem_insert_of_mem hi))

/-- **Finite products of bounded series are bounded.** -/
theorem isBddK_prod {κ : Type} (s : Finset κ) {F : κ → MvPowerSeries σ ℂ_[ℓ]} (hF : ∀ i ∈ s, IsBddK (F i)) :
    IsBddK (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isIntK_one (σ := σ) (K := ℂ_[ℓ])).isBddK
  | insert j s hj ih =>
    rw [prod_insert hj]
    exact (hF j (mem_insert_self j s)).mul (ih fun i hi => hF i (mem_insert_of_mem hi))

/-- **Integral substitution keeps boundedness** (zero constant terms). -/
theorem IsBddK.subst {τ : Type} [Finite σ] {F : MvPowerSeries σ ℂ_[ℓ]} (hF : IsBddK F)
    {ψ : σ → MvPowerSeries τ ℂ_[ℓ]} (hψ : ∀ s, IsIntK (ψ s)) (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) :
    IsBddK (F.subst ψ) := by
  obtain ⟨k, hk⟩ := hF
  have hb : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  refine ⟨k, ?_⟩
  have e : MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F.subst ψ = (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ k) * F).subst ψ := by
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_C]
  rw [e]
  exact hk.subst hψ hψ0

/-- **A bounded series is a constant times an integral series**: `F = ℓ^{−k}·(ℓ^k·F)`. -/
theorem exists_eq_C_mul_of_isBddK {F : MvPowerSeries σ ℂ_[ℓ]} (hF : IsBddK F) :
    ∃ (c : ℂ_[ℓ]) (U : MvPowerSeries σ ℂ_[ℓ]), IsIntK U ∧ F = MvPowerSeries.C c * U := by
  obtain ⟨k, hk⟩ := hF
  have hℓ0 : (ℓ : ℂ_[ℓ]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hℓp.out.ne_zero)
  refine ⟨((ℓ : ℂ_[ℓ]) ^ k)⁻¹, _, hk, ?_⟩
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hℓ0, map_one, one_mul]

end Bdd

/-! ## The tensor fourth power and the diagonal trick -/

section Tens

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {ι : Type}

/-- **The tensor fourth power** `g^{⊗4}(X) = Π_k g(X_{k,·})` of a series, in the variables `Fin 4 × ι`. -/
def tens4S (g : MvPowerSeries ι ℂ_[ℓ]) : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ] :=
  ∏ k : Fin 4, MvPowerSeries.subst (fun i => (MvPowerSeries.X (k, i) : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ])) g

/-- **The `k`-th copy** `i ↦ (k, i)` of `ι` in `Fin 4 × ι`. -/
def emb4 (k : Fin 4) : ι ↪ Fin 4 × ι := ⟨fun i => (k, i), fun _ _ h => (Prod.ext_iff.1 h).2⟩

/-- **The diagonal multi-index** `(m, m, m, m)` on `Fin 4 × ι`. -/
def diag4 (m : ι →₀ ℕ) : Fin 4 × ι →₀ ℕ := ∑ k : Fin 4, Finsupp.embDomain (emb4 k) m

/-- **The `j`-th copy of a multi-index**, pointwise. -/
theorem embDomain_emb4_apply (j : Fin 4) (m : ι →₀ ℕ) (p : Fin 4 × ι) :
    Finsupp.embDomain (emb4 j) m p = if p.1 = j then m p.2 else 0 := by
  obtain ⟨k, i⟩ := p
  by_cases h : k = j
  · subst h
    rw [ite_eq_left (rfl : (k, i).1 = k)]
    exact Finsupp.embDomain_apply_self (emb4 k) m i
  · rw [ite_eq_right h]
    refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨i', hi'⟩
    exact h (congrArg Prod.fst hi').symm

/-- **Substituting `X_{(k,i)}` for `X_i`** is renaming the variables along `emb4 k`. -/
theorem subst_X_emb4 (k : Fin 4) (g : MvPowerSeries ι ℂ_[ℓ]) :
    MvPowerSeries.subst (fun i => (MvPowerSeries.X (k, i) : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ])) g =
      MvPowerSeries.rename (emb4 k) g :=
  (MvPowerSeries.rename_eq_subst (f := ⇑(emb4 k)) g).symm

/-- **The diagonal coefficient** `[X^{(m,m,m,m)}] g^{⊗4} = ([X^m] g)⁴`: in `MvPowerSeries.coeff_prod` the only
term with every factor in the range of its renaming is the diagonal one. -/
theorem coeff_tens4S (g : MvPowerSeries ι ℂ_[ℓ]) (m : ι →₀ ℕ) :
    MvPowerSeries.coeff (diag4 m) (tens4S g) = MvPowerSeries.coeff m g ^ 4 := by
  classical
  simp only [tens4S, subst_X_emb4]
  rw [MvPowerSeries.coeff_prod]
  set l₀ : Fin 4 →₀ Fin 4 × ι →₀ ℕ := Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (emb4 k) m
    with hl₀
  have hl₀k : ∀ k, l₀ k = Finsupp.embDomain (emb4 k) m := fun k => by simp [hl₀]
  have hmem : l₀ ∈ univ.finsuppAntidiag (diag4 m) :=
    mem_finsuppAntidiag.2 ⟨by simp only [hl₀k, diag4], subset_univ _⟩
  refine (sum_eq_single_of_mem (f := fun l : Fin 4 →₀ Fin 4 × ι →₀ ℕ =>
    ∏ i, MvPowerSeries.coeff (l i) (MvPowerSeries.rename (emb4 i) g)) _ hmem ?_).trans ?_
  · intro l hl hne
    by_contra hprod
    apply hne
    have hk : ∀ k, ∃ m', l k = Finsupp.embDomain (emb4 k) m' := fun k => by
      by_contra hk
      push Not at hk
      refine hprod (prod_eq_zero (mem_univ k) (MvPowerSeries.coeff_rename_eq_zero _ _ ?_))
      rintro ⟨m', hm'⟩
      exact hk m' (by rw [Finsupp.embDomain_eq_mapDomain, hm'])
    choose m' hm' using hk
    have hsum := (mem_finsuppAntidiag.1 hl).1
    refine Finsupp.ext fun k => ?_
    rw [hm' k, hl₀k, Finsupp.embDomain_inj]
    ext i
    have h1 := congrArg (fun f : Fin 4 × ι →₀ ℕ => f (k, i)) hsum
    simp only [diag4, Finsupp.coe_finsetSum, Finset.sum_apply, hm', embDomain_emb4_apply] at h1
    simpa using h1
  · simp only [hl₀k, MvPowerSeries.coeff_embDomain_rename, prod_const, card_univ, Fintype.card_fin]

/-- **The diagonal trick**: the coefficient of `g^{⊗4}` at `(m, m, m, m)` is `g_m⁴`, so a bound `r` on the
coefficients of `g^{⊗4}` gives `‖g_m‖⁴ ≤ r`. -/
theorem norm_coeff_pow_four_le {g : MvPowerSeries ι ℂ_[ℓ]} {r : ℝ}
    (h : ∀ n, ‖MvPowerSeries.coeff n (tens4S g)‖ ≤ r) (m : ι →₀ ℕ) : ‖MvPowerSeries.coeff m g‖ ^ 4 ≤ r := by
  rw [← norm_pow, ← coeff_tens4S]
  exact h _

/-- **The diagonal trick, bounded form**: `g^{⊗4}` bounded gives `g` bounded (with the same power of `ℓ`:
`‖ℓ^k‖·‖g_m‖⁴ ≤ 1` forces `‖ℓ^k·g_m‖ ≤ 1`). -/
theorem isBddK_of_tens4S {g : MvPowerSeries ι ℂ_[ℓ]} (h : IsBddK (tens4S g)) : IsBddK g := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun m => ?_⟩
  have h1 := hk (diag4 m)
  rw [MvPowerSeries.coeff_C_mul, coeff_tens4S, norm_mul, norm_pow, norm_pow] at h1
  rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_pow]
  set a := ‖(ℓ : ℂ_[ℓ])‖ ^ k
  set x := ‖MvPowerSeries.coeff m g‖
  have ha : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    change ‖(ℓ : ℂ_[ℓ])‖ ^ k ≤ 1
    rw [← norm_pow]
    exact norm_ell_pow_le_one k
  have hx : 0 ≤ x := norm_nonneg _
  by_contra hlt
  push Not at hlt
  -- `1 < a·x` gives `a·x⁴ ≥ (a·x)⁴·a⁻³ ≥ (a x)⁴ > 1`
  have h2 : 1 < (a * x) ^ 4 := one_lt_pow₀ hlt (by norm_num)
  have h3 : (a * x) ^ 4 ≤ a * x ^ 4 := by
    rw [mul_pow]
    have : a ^ 4 ≤ a := pow_le_of_le_one ha ha1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

end Tens

/-! ## Exponentials, and Gaussian times bounded -/

section ExpH

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ τ : Type}

/-- **`exp` commutes with substitution** for series without constant term. -/
theorem expMv_subst {f : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0)
    {ψ : σ → MvPowerSeries τ ℂ_[ℓ]} (hb : MvPowerSeries.HasSubst ψ)
    (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) : (expMv f).subst ψ = expMv (f.subst ψ) := by
  have h0 : MvPowerSeries.constantCoeff (f.subst ψ) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero hb hψ0 hf
  rw [expMv_eq_subst h0, expMv_eq_subst hf, PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hb]

/-- **`exp` of a finite sum** is the product of the exponentials. -/
theorem expMv_sum {κ : Type} (s : Finset κ) {f : κ → MvPowerSeries σ ℂ_[ℓ]}
    (hf : ∀ i ∈ s, MvPowerSeries.constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expMv_zero]
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj, expMv_add (hf j (mem_insert_self j s)) (by
      rw [map_sum]; exact sum_eq_zero fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- **`tens4S` as a product of renamings.** -/
theorem tens4S_eq {ι : Type} (g : MvPowerSeries ι ℂ_[ℓ]) :
    tens4S g = ∏ k : Fin 4, MvPowerSeries.rename (emb4 k) g := by
  simp only [tens4S, subst_X_emb4]

/-- **`tens4S` is multiplicative.** -/
theorem tens4S_mul {ι : Type} (f g : MvPowerSeries ι ℂ_[ℓ]) : tens4S (f * g) = tens4S f * tens4S g := by
  simp only [tens4S_eq, map_mul, prod_mul_distrib]

/-- **The tensor power of an exponential**: `exp(f)^{⊗4} = exp(Σ_k f(X_{k,·}))`. -/
theorem tens4S_expMv {ι : Type} {f : MvPowerSeries ι ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0) :
    tens4S (expMv f) = expMv (∑ k : Fin 4, MvPowerSeries.rename (emb4 k) f) := by
  rw [expMv_sum _ fun k _ => by rw [MvPowerSeries.constantCoeff_rename, hf], tens4S_eq]
  refine prod_congr rfl fun k _ => ?_
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    expMv_subst hf (MvPowerSeries.HasSubst.X_comp _) fun i => MvPowerSeries.constantCoeff_X _]

/-- **Gaussian times bounded**: `F = exp(−P)·W` with `W` bounded. -/
def IsGB (P F : MvPowerSeries σ ℂ_[ℓ]) : Prop := ∃ W, IsBddK W ∧ F = expMv (-P) * W

/-- **Constant multiples** stay Gaussian times bounded. -/
theorem IsGB.C_mul {P F : MvPowerSeries σ ℂ_[ℓ]} (h : IsGB P F) (c : ℂ_[ℓ]) : IsGB P (MvPowerSeries.C c * F) := by
  obtain ⟨W, hW, rfl⟩ := h
  exact ⟨_, hW.C_mul c, by ring⟩

/-- **Sums** with the same Gaussian stay Gaussian times bounded. -/
theorem IsGB.add {P F G : MvPowerSeries σ ℂ_[ℓ]} (hF : IsGB P F) (hG : IsGB P G) : IsGB P (F + G) := by
  obtain ⟨W, hW, rfl⟩ := hF
  obtain ⟨W', hW', rfl⟩ := hG
  exact ⟨_, hW.add hW', by ring⟩

/-- **Finite sums** with the same Gaussian stay Gaussian times bounded. -/
theorem isGB_sum {κ : Type} (s : Finset κ) {P : MvPowerSeries σ ℂ_[ℓ]} {F : κ → MvPowerSeries σ ℂ_[ℓ]}
    (h : ∀ i ∈ s, IsGB P (F i)) : IsGB P (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, ⟨0, fun n => by simp⟩, by simp⟩
  | insert j s hj ih =>
    rw [sum_insert hj]
    exact (h j (mem_insert_self j s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- **Products**: the Gaussians multiply, `exp(−P)·exp(−Q) = exp(−(P + Q))`. -/
theorem IsGB.mul {P Q F G : MvPowerSeries σ ℂ_[ℓ]} (hP : MvPowerSeries.constantCoeff P = 0)
    (hQ : MvPowerSeries.constantCoeff Q = 0) (hF : IsGB P F) (hG : IsGB Q G) : IsGB (P + Q) (F * G) := by
  obtain ⟨W, hW, rfl⟩ := hF
  obtain ⟨W', hW', rfl⟩ := hG
  refine ⟨_, hW.mul hW', ?_⟩
  rw [neg_add, expMv_add (by rw [map_neg, hP, neg_zero]) (by rw [map_neg, hQ, neg_zero])]
  ring

/-- **Finite products**: the Gaussians multiply. -/
theorem isGB_prod {κ : Type} (s : Finset κ) {P F : κ → MvPowerSeries σ ℂ_[ℓ]}
    (hP : ∀ i ∈ s, MvPowerSeries.constantCoeff (P i) = 0) (h : ∀ i ∈ s, IsGB (P i) (F i)) :
    IsGB (∑ i ∈ s, P i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, isIntK_one.isBddK, by simp [expMv_zero]⟩
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    exact (h j (mem_insert_self j s)).mul (hP j (mem_insert_self j s))
      (by rw [map_sum]; exact sum_eq_zero fun i hi => hP i (mem_insert_of_mem hi))
      (ih (fun i hi => hP i (mem_insert_of_mem hi)) fun i hi => h i (mem_insert_of_mem hi))

/-- **Integral substitution** keeps the shape `exp(−P)·W`. -/
theorem IsGB.subst [Finite σ] {P F : MvPowerSeries σ ℂ_[ℓ]} (hP : MvPowerSeries.constantCoeff P = 0)
    (h : IsGB P F) {ψ : σ → MvPowerSeries τ ℂ_[ℓ]} (hψ : ∀ s, IsIntK (ψ s))
    (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) : IsGB (P.subst ψ) (F.subst ψ) := by
  obtain ⟨W, hW, rfl⟩ := h
  have hb : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  refine ⟨_, hW.subst hψ hψ0, ?_⟩
  rw [MvPowerSeries.subst_mul hb, expMv_subst (by rw [map_neg, hP, neg_zero]) hb hψ0,
    ← MvPowerSeries.coe_substAlgHom hb, map_neg]

/-- **Cancelling the Gaussian**: if `F = exp(−P)·W` with `W` bounded and `Q ≃ P`, then `F·exp(Q)` is bounded
(`exp(Q − P)` is integral). -/
theorem IsGB.isBddK_mul_expMv {P Q F : MvPowerSeries σ ℂ_[ℓ]} (h : IsGB P F) (hQP : Simeq Q P)
    (hP : MvPowerSeries.constantCoeff P = 0) (hQ : MvPowerSeries.constantCoeff Q = 0) :
    IsBddK (F * expMv Q) := by
  obtain ⟨W, hW, rfl⟩ := h
  have e : expMv (-P) * W * expMv Q = expMv (Q - P) * W := by
    rw [sub_eq_add_neg, expMv_add hQ (by rw [map_neg, hP, neg_zero])]
    ring
  rw [e]
  exact (IsIntK.isBddK hQP.2).mul hW

end ExpH

/-! ## Lubin–Tate series of functions on `ℂ^κ` -/

section LT

open MvTay ThetaNorm

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The Lubin–Tate series of a function** `G : ℂ^κ → ℂ` at the point `A` (a `κ`-tuple of series over `ℂ_ℓ`):
the Taylor series `mtay G` at `0`, carried to `ℂ_ℓ` by `ι′`, evaluated at `A`. -/
def ltS (ι' : ℂ ≃+* ℂ_[ℓ]) {κ σ : Type} [Fintype κ] [DecidableEq κ] (A : κ → MvPowerSeries σ ℂ_[ℓ])
    (G : (κ → ℂ) → ℂ) : MvPowerSeries σ ℂ_[ℓ] :=
  MvPowerSeries.subst A (MvPowerSeries.map (ι' : ℂ →+* ℂ_[ℓ]) (mtay G))

variable (ι' : ℂ ≃+* ℂ_[ℓ]) {κ κ' σ : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- **`ltS` is `ℂ`-linear** (`mtay_smul`). -/
theorem ltS_smul {A : κ → MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.HasSubst A) (c : ℂ) {G : (κ → ℂ) → ℂ}
    (hG : AnalyticAt ℂ G 0) : ltS ι' A (fun z => c * G z) = MvPowerSeries.C (ι' c) * ltS ι' A G := by
  have e : (fun z => c * G z) = c • G := rfl
  rw [ltS, ltS, e, mtay_smul c hG, map_mul, MvPowerSeries.map_C, MvPowerSeries.subst_mul hA,
    MvPowerSeries.subst_C]
  rfl

/-- **`ltS` of a finite sum** (`mtay_sum`). -/
theorem ltS_sum {A : κ → MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.HasSubst A) {α : Type} (s : Finset α)
    {G : α → (κ → ℂ) → ℂ} (hG : ∀ a ∈ s, AnalyticAt ℂ (G a) 0) :
    ltS ι' A (fun z => ∑ a ∈ s, G a z) = ∑ a ∈ s, ltS ι' A (G a) := by
  rw [ltS, mtay_sum s hG, map_sum, ← MvPowerSeries.coe_substAlgHom hA, map_sum]
  simp only [ltS, MvPowerSeries.coe_substAlgHom hA]

/-- **Linear changes of coordinates**: `ltS_A(G ∘ L) = ltS_{L·A}(G)` (`mtay_comp_linear`). -/
theorem ltS_comp_linear {A : κ' → MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.HasSubst A)
    (L : (κ' → ℂ) →ₗ[ℂ] (κ → ℂ)) {G : (κ → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) :
    ltS ι' A (G ∘ L) = ltS ι' (fun i => ∑ k, MvPowerSeries.C (ι' (L (Pi.single k 1) i)) * A k) G := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ k, MvPowerSeries.C (L (Pi.single k 1) i) *
      (MvPowerSeries.X k : MvPowerSeries κ' ℂ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
  rw [ltS, ltS, mtay_comp_linear L hG, MvPowerSeries.map_subst ha,
    MvPowerSeries.subst_comp_subst_apply (ha.map _) hA]
  congr 1
  funext i
  rw [← MvPowerSeries.coe_substAlgHom hA]
  simp only [map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, MvPowerSeries.coe_substAlgHom hA,
    MvPowerSeries.subst_C, MvPowerSeries.subst_X hA]
  rfl

/-- **A product of one-variable functions of the coordinates**: `ltS_A(Π_p f_p(z_p)) = Π_p (tay f_p)(A_p)`
(`mtay_prod_coord`). -/
theorem ltS_prod_coord {A : κ → MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.HasSubst A) (f : κ → ℂ → ℂ)
    (hf : ∀ p, AnalyticAt ℂ (f p) 0) :
    ltS ι' A (fun z => ∏ p, f p (z p)) =
      ∏ p, PowerSeries.subst (A p) (PowerSeries.map (ι' : ℂ →+* ℂ_[ℓ]) (tay (f p))) := by
  rw [ltS, mtay_prod_coord f hf, map_prod, ← MvPowerSeries.coe_substAlgHom hA, map_prod]
  refine prod_congr rfl fun p _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hA, PowerSeries.map_subst (PowerSeries.HasSubst.X p), MvPowerSeries.map_X,
    subst_subst _ (MvPowerSeries.constantCoeff_X p) hA, MvPowerSeries.subst_X hA]

omit [DecidableEq κ] [DecidableEq κ'] in
/-- **Reindexing keeps analyticity**. -/
theorem analyticAt_comp_reindex {G : (κ → ℂ) → ℂ} (hG : ∀ z, AnalyticAt ℂ G z) (e : κ → κ') (z : κ' → ℂ) :
    AnalyticAt ℂ (fun v : κ' → ℂ => G fun i => v (e i)) z := by
  have h := (hG _).comp_of_eq ((LinearMap.funLeft ℂ ℂ e).toContinuousLinearMap.analyticAt z) rfl
  exact h

/-- **The tensor fourth power in Lubin–Tate coordinates**: at the points `ε·L(X_p)`, the series of
`θ^{⊗4}` is the tensor fourth power of the series of `θ` (`mtay_prod`, `mtay_comp_reindex`). -/
theorem ltS_tens4 (ε : ℂ_[ℓ]) {ι : Type} [Fintype ι] [DecidableEq ι] {θ : (ι → ℂ) → ℂ}
    (hθ : ∀ z, AnalyticAt ℂ θ z) :
    tens4S (ltS ι' (fun p => PowerSeries.subst (MvPowerSeries.X p : MvPowerSeries ι ℂ_[ℓ]) (zLT ℓ ε)) θ) =
      ltS ι' (fun q => PowerSeries.subst (MvPowerSeries.X q : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]) (zLT ℓ ε))
        (tens4 θ) := by
  have hz0 : PowerSeries.constantCoeff (zLT ℓ ε) = 0 := constantCoeff_zLT hℓp.out.one_lt ε
  have hA : MvPowerSeries.HasSubst (fun p => PowerSeries.subst (MvPowerSeries.X p : MvPowerSeries ι ℂ_[ℓ])
      (zLT ℓ ε)) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun p =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X p) _ hz0
  have hA4 : MvPowerSeries.HasSubst (fun q => PowerSeries.subst
      (MvPowerSeries.X q : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]) (zLT ℓ ε)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q =>
      PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X q) _ hz0
  have hXk : ∀ k : Fin 4, MvPowerSeries.HasSubst
      (fun i => (MvPowerSeries.X (k, i) : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ])) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _
  have hXkC : ∀ k : Fin 4, MvPowerSeries.HasSubst
      (fun i => (MvPowerSeries.X (k, i) : MvPowerSeries (Fin 4 × ι) ℂ)) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _
  have e1 : tens4 θ = fun v : Fin 4 × ι → ℂ => ∏ k : Fin 4, θ (fun i => v (k, i)) := rfl
  rw [e1]
  simp only [ltS]
  rw [mtay_prod univ fun k _ => analyticAt_comp_reindex hθ (fun i : ι => (k, i)) 0, map_prod,
    ← MvPowerSeries.coe_substAlgHom hA4, map_prod, tens4S]
  refine prod_congr rfl fun k _ => ?_
  rw [mtay_comp_reindex (fun i : ι => (k, i)) (hθ 0), MvPowerSeries.map_subst (hXkC k),
    MvPowerSeries.coe_substAlgHom hA4, MvPowerSeries.subst_comp_subst_apply ((hXkC k).map _) hA4,
    MvPowerSeries.subst_comp_subst_apply hA (hXk k)]
  congr 1
  funext i
  rw [MvPowerSeries.map_X, MvPowerSeries.subst_X hA4, subst_subst _ (MvPowerSeries.constantCoeff_X i) (hXk k),
    MvPowerSeries.subst_X (hXk k)]

end LT

/-! ## The translate factors of the model theta -/

section Transl

open ThetaChain ThetaNorm ChainCanon CMThetaOne CMEquiv ThetaCompare EllipticSigma

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The shifted sigma** `shS(t′)(w) = σ*(w + t′)·exp(−(π/A)·t̄′·w)`. -/
def shS (Λ : PeriodPair) (t' w : ℂ) : ℂ :=
  sgStar Λ (w + t') * Complex.exp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t') * w)

/-- **The coordinate factor of `U_q F0`**: `facT(c)(w) = th0_t(w + c)·exp(−πs·w·c̄ − πs·c·c̄/2)`. -/
def facT (sd : ℝ) (c w : ℂ) : ℂ :=
  th0L (cmLat sd) (tC sd) (w + c) * Complex.exp (-(Real.pi : ℂ) * ((sC sd : ℂ) * (w * starRingEnd ℂ c)) -
    (Real.pi : ℂ) * ((sC sd : ℂ) * (c * starRingEnd ℂ c)) / 2)

/-- **`U_q F0` is a product of one-variable factors**: `U_qF0(z) = Π_p facT(q_p)(z_p)` (`H` is diagonal). -/
theorem opU_F0c {ι : Type} [Fintype ι] (sd : ℝ) (q z : ι → ℂ) :
    opU (sC sd) q (F0c (ι := ι) sd) z = ∏ p, facT sd (q p) (z p) := by
  simp only [facT, prod_mul_distrib, ← Complex.exp_sum]
  change F0c sd (z + q) * _ = _
  rw [F0c_apply, Hf_eq_sum, Hf_eq_sum]
  congr 2
  rw [mul_sum, mul_sum, sum_div, ← sum_sub_distrib]

/-- **`shS` is entire.** -/
theorem differentiable_shS (Λ : PeriodPair) (t' : ℂ) : Differentiable ℂ (shS Λ t') := by
  have h := differentiable_sgStar Λ
  unfold shS
  fun_prop

/-- **`facT` is entire.** -/
theorem differentiable_facT (sd : ℝ) (c : ℂ) : Differentiable ℂ (facT sd c) := by
  have h := differentiable_th0L (cmLat sd) (tC sd)
  unfold facT
  fun_prop

/-- **The factor is a shifted sigma**: `facT(c)(w) = K_c·shS(t + c)(w)` with an explicit constant `K_c`
(`th0L_eq`; `s = 1/A`). -/
theorem facT_eq {sd : ℝ} (c w : ℂ) :
    facT sd c w = Complex.exp (-(((Real.pi / area (cmLat sd) : ℝ) : ℂ) * starRingEnd ℂ (tC sd)) * c -
      ((Real.pi / area (cmLat sd) : ℝ) : ℂ) * (c * starRingEnd ℂ c) / 2) / sgStar (cmLat sd) (tC sd) *
        shS (cmLat sd) (tC sd + c) w := by
  set cπ : ℂ := ((Real.pi / area (cmLat sd) : ℝ) : ℂ) with hcπ
  have hπ : (Real.pi : ℂ) * (sC sd : ℂ) = cπ := by
    rw [hcπ, sC]
    push_cast
    ring
  have e1 : Complex.exp (-(cπ * starRingEnd ℂ (tC sd)) * (w + c)) *
      Complex.exp (-(Real.pi : ℂ) * ((sC sd : ℂ) * (w * starRingEnd ℂ c)) -
        (Real.pi : ℂ) * ((sC sd : ℂ) * (c * starRingEnd ℂ c)) / 2) =
      Complex.exp (-(cπ * starRingEnd ℂ (tC sd)) * c - cπ * (c * starRingEnd ℂ c) / 2) *
        Complex.exp (-(cπ * starRingEnd ℂ (tC sd + c)) * w) := by
    rw [← Complex.exp_add, ← Complex.exp_add, map_add]
    congr 1
    linear_combination (-(w * starRingEnd ℂ c) - c * starRingEnd ℂ c / 2) * hπ
  rw [facT, th0L_eq, shS, show w + c + tC sd = w + (tC sd + c) by ring]
  linear_combination (sgStar (cmLat sd) (w + (tC sd + c)) / sgStar (cmLat sd) (tC sd)) * e1

/-- **`tay` of a constant multiple.** -/
theorem tay_const_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    tay (fun w => c * f w) = PowerSeries.C c * tay f := by
  rw [tay_mul analyticAt_const hf, tay_const]

/-- **The Lubin–Tate series of a one-variable function**: `(ι′ tay f)(ε·L(T))`. -/
def ltS1 (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) (f : ℂ → ℂ) : ℂ_[ℓ]⟦X⟧ :=
  (PowerSeries.map (ι' : ℂ →+* ℂ_[ℓ]) (tay f)).subst (zLT ℓ ε)

/-- **`ltS1` of a constant multiple.** -/
theorem ltS1_const_mul (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    ltS1 ι' ε (fun w => c * f w) = PowerSeries.C (ι' c) * ltS1 ι' ε f := by
  rw [ltS1, ltS1, tay_const_mul hf, map_mul, PowerSeries.map_C,
    PowerSeries.subst_mul (HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓp.out.one_lt ε)),
    PowerSeries.subst_C]
  rfl

/-- **The Taylor series of `σ*`** is `X·exp(logSig)` (`σ* = z·sigE`, `tay_sigE`). -/
theorem tay_sgStar (Λ : PeriodPair) : tay (sgStar Λ) = X * expSig Λ.g₂ Λ.g₃ (s2 Λ) := by
  have e : sgStar Λ = fun z => z * sigE Λ z := by
    rw [sgStar_eq]
    funext z
    rw [pow_one]
  rw [e, tay_mul (f := fun z => z) analyticAt_id (analyticAt_sigE Λ 0), tay_id, tay_sigE]

/-- **The translate factors in Lubin–Tate coordinates are Gaussian times bounded**: `facT(c) = K·shS(t + c)`; if
`t + c ∉ Λ`, `shS(t + c) = σ*(t + c)·th0_{t+c}` and `th0_{t+c}(ε·L(T)) = exp(−ph)·U_{t+c}` with `U_{t+c}` integral
(`th0_eq_exp_neg_ph_mul`, `CMTorsion.isInt_translate_any`: `t + c` has order dividing `2N`, prime to `ℓ`); if
`t + c ∈ Λ`, `shS(t + c) = κ·σ*` (`exists_sgMult`) and `σ*(ε·L(T)) = εT·exp(−ph)` (`C_mul_X_mul_exp_neg_ph`). -/
theorem isGB_facT (h5 : 5 ≤ ℓ) {d : ℕ} {sd : ℝ} (hd4 : d % 4 = 3) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) (ι' : ℂ ≃+* ℂ_[ℓ]) (h2 : ‖ι' (cmLat sd).g₂‖ ≤ 1)
    (h3 : ‖ι' (cmLat sd).g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃)).subst (zLT ℓ ε))) (c : ℂ) {N : ℕ}
    (hNℓ : ¬ ℓ ∣ N) (hNc : (N : ℂ) * c ∈ (cmLat sd).lattice) :
    IsGB (ph ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε : MvPowerSeries Unit ℂ_[ℓ])
      (ltS1 ι' ε (facT sd c) : MvPowerSeries Unit ℂ_[ℓ]) := by
  set Λ := cmLat sd with hΛ
  have hℓ2 : ℓ ≠ 2 := by omega
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  obtain ⟨hor, h2t, ht0, -⟩ := canon_data (sd_pos hd4 hsd) hΔ
  have hph0 : MvPowerSeries.constantCoeff
      (ph ℓ (ι' Λ.g₂) (ι' Λ.g₃) (ι' (s2 Λ)) ε : MvPowerSeries Unit ℂ_[ℓ]) = 0 :=
    constantCoeff_ph hℓp.out.one_lt _ _ _ _
  have hexp : expMv (-(ph ℓ (ι' Λ.g₂) (ι' Λ.g₃) (ι' (s2 Λ)) ε : MvPowerSeries Unit ℂ_[ℓ])) =
      (exp ℂ_[ℓ]).subst (-ph ℓ (ι' Λ.g₂) (ι' Λ.g₃) (ι' (s2 Λ)) ε) :=
    expMv_eq_subst (by rw [map_neg, hph0, neg_zero])
  set K := Complex.exp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ (tC sd)) * c -
      ((Real.pi / area Λ : ℝ) : ℂ) * (c * starRingEnd ℂ c) / 2) / sgStar Λ (tC sd) with hK
  have hf : facT sd c = fun w => K * shS Λ (tC sd + c) w := funext (facT_eq c)
  rw [hf, ltS1_const_mul ι' ε ((differentiable_shS Λ _).analyticAt 0)]
  refine IsGB.C_mul ?_ (ι' K)
  by_cases hl : tC sd + c ∈ Λ.lattice
  · -- `t + c` a period: `shS = κ·σ*`
    obtain ⟨κ, hκ⟩ := exists_sgMult Λ hor hl
    have hs : shS Λ (tC sd + c) = fun w => κ * sgStar Λ w := by
      funext w
      rw [shS, hκ w, mul_assoc, mul_assoc, mul_comm (sgStar Λ w), ← mul_assoc (Complex.exp _),
        ← Complex.exp_add, show ((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ (tC sd + c) * w +
          -(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ (tC sd + c)) * w = 0 by ring, Complex.exp_zero, one_mul]
    rw [hs, ltS1_const_mul ι' ε ((differentiable_sgStar Λ).analyticAt 0)]
    refine IsGB.C_mul ?_ (ι' κ)
    have e : ltS1 ι' ε (sgStar Λ) =
        PowerSeries.C ε * X * (exp ℂ_[ℓ]).subst (-ph ℓ (ι' Λ.g₂) (ι' Λ.g₃) (ι' (s2 Λ)) ε) := by
      rw [ltS1, tay_sgStar, map_mul, PowerSeries.map_X, map_expSig, C_mul_X_mul_exp_neg_ph hℓp.out.one_lt]
      rfl
    refine ⟨(PowerSeries.C ε * X : ℂ_[ℓ]⟦X⟧), ?_, ?_⟩
    · exact (IsIntK.isBddK (isIntK_X ())).C_mul ε
    · rw [e, hexp]
      ring
  · -- `t + c` not a period: `shS = σ*(t + c)·th0_{t+c}`, and the translate is integral
    have hs : shS Λ (tC sd + c) = fun w => sgStar Λ (tC sd + c) * th0L Λ (tC sd + c) w := by
      funext w
      rw [th0L_eq, shS]
      field_simp [sgStar_ne_zero Λ hl]
    rw [hs, ltS1_const_mul ι' ε ((differentiable_th0L Λ _).analyticAt 0)]
    refine IsGB.C_mul ?_ (ι' (sgStar Λ (tC sd + c)))
    have h2N : ¬ ℓ ∣ 2 * N := fun h => by
      rcases (Nat.Prime.dvd_mul hℓp.out).1 h with h' | h'
      · have := Nat.le_of_dvd (by norm_num) h'
        omega
      · exact hNℓ h'
    have hmem : ((2 * N : ℕ) : ℂ) * (tC sd + c) ∈ Λ.lattice := by
      have e : ((2 * N : ℕ) : ℂ) * (tC sd + c) = N • (2 * tC sd) + 2 • ((N : ℂ) * c) := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [e]
      exact add_mem (nsmul_mem h2t N) (nsmul_mem hNc 2)
    obtain ⟨hUi, -⟩ := CMTorsion.isInt_translate_any hℓ2 Λ (ι' : ℂ →+* ℂ_[ℓ]) h2 h3 hε ht hl h2N hmem
    refine ⟨_, hUi.isIntK.isBddK, ?_⟩
    rw [hexp, ltS1, th0_eq_exp_neg_ph_mul Λ (ι' : ℂ →+* ℂ_[ℓ]) hl hε0]
    rfl

end Transl

/-! ## The model theta in Lubin–Tate coordinates -/

section Model

open ThetaChain ThetaNorm ChainCanon CMThetaOne CMEquiv ThetaCompare ThetaHeis

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **The model theta as a finite sum**: `Iop(Lc^κ, Λ₂) F0 = Σ_j a_j·Π_p facT(r_j(p))(z_p)` with representatives
`r_j ∈ Λ₂` of the finite quotient (`opU_F0c`). -/
theorem Iop_F0c_eq_sum (sd : ℝ) (Λ₂ : AddSubgroup (κ → ℂ)) (hfin : (stdLc sd κ ⊓ Λ₂).relIndex Λ₂ ≠ 0) :
    ∃ (α : Type) (_ : Fintype α) (r : α → κ → ℂ) (a : α → ℂ), (∀ j, r j ∈ Λ₂) ∧
      Iop (sC sd) sd (stdLc sd κ) Λ₂ (F0c sd) = fun z => ∑ j, a j * ∏ p, facT sd (r j p) (z p) := by
  have := finite_quot hfin
  have := Fintype.ofFinite (Λ₂ ⧸ (stdLc sd κ ⊓ Λ₂).addSubgroupOf Λ₂)
  refine ⟨Λ₂ ⧸ (stdLc sd κ ⊓ Λ₂).addSubgroupOf Λ₂, inferInstance, fun q => (q.out : κ → ℂ),
    fun q => ((Real.sqrt ((stdLc sd κ ⊓ Λ₂).relIndex Λ₂ : ℝ))⁻¹ : ℂ) * al (sC sd) sd (q.out : κ → ℂ),
    fun q => q.out.2, ?_⟩
  funext z
  rw [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, opU_F0c, mul_assoc]

omit [DecidableEq κ] in
/-- **The finite sums of products of factors are analytic everywhere.** -/
theorem analyticAt_sum_prod_facT (sd : ℝ) {α : Type} [Fintype α] (r : α → κ → ℂ) (a : α → ℂ) (z : κ → ℂ) :
    AnalyticAt ℂ (fun z => ∑ j, a j * ∏ p, facT sd (r j p) (z p)) z :=
  Finset.analyticAt_fun_sum _ fun _ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun p _ =>
    ((differentiable_facT sd _).analyticAt _).comp_of_eq
      ((ContinuousLinearMap.proj p : (κ → ℂ) →L[ℂ] ℂ).analyticAt z) rfl)

/-- **The model theta in Lubin–Tate coordinates is Gaussian times bounded**: at the points `Y_p`, the series of
`Σ_j a_j·Π_p facT(r_j(p))(z_p)` is `exp(−Σ_p ph(Y_p))·W` with `W` bounded, when the `r_j(p)` are torsion of order
prime to `ℓ` (`isGB_facT`, substituted at `Y_p`, multiplied over `p`, summed over `j`). -/
theorem isGB_ltS_facT (h5 : 5 ≤ ℓ) {d : ℕ} {sd : ℝ} (hd4 : d % 4 = 3) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) (ι' : ℂ ≃+* ℂ_[ℓ]) (h2 : ‖ι' (cmLat sd).g₂‖ ≤ 1)
    (h3 : ‖ι' (cmLat sd).g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃)).subst (zLT ℓ ε))) {σ α : Type} [Fintype α]
    (r : α → κ → ℂ) (a : α → ℂ) {M : ℕ} (hMℓ : ¬ ℓ ∣ M) (hM : ∀ j p, (M : ℂ) * r j p ∈ (cmLat sd).lattice)
    (Y : κ → MvPowerSeries σ ℂ_[ℓ]) (hY : ∀ p, IsIntK (Y p)) (hY0 : ∀ p, MvPowerSeries.constantCoeff (Y p) = 0) :
    IsGB (∑ p, PowerSeries.subst (Y p) (ph ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε))
      (ltS ι' (fun p => PowerSeries.subst (Y p) (zLT ℓ ε)) fun z => ∑ j, a j * ∏ p, facT sd (r j p) (z p)) := by
  have hℓ := hℓp.out.one_lt
  have hz0 : PowerSeries.constantCoeff (zLT ℓ ε) = 0 := constantCoeff_zLT hℓ ε
  have hA0 : ∀ p, MvPowerSeries.constantCoeff (PowerSeries.subst (Y p) (zLT ℓ ε)) = 0 := fun p =>
    PowerSeries.constantCoeff_subst_eq_zero (hY0 p) _ hz0
  have hA := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
  have hfa : ∀ c, AnalyticAt ℂ (facT sd c) 0 := fun c => (differentiable_facT sd c).analyticAt 0
  have hprod : ∀ j, AnalyticAt ℂ (fun z : κ → ℂ => ∏ p, facT sd (r j p) (z p)) 0 := fun j =>
    Finset.analyticAt_fun_prod _ fun p _ =>
      (hfa _).comp_of_eq ((ContinuousLinearMap.proj p : (κ → ℂ) →L[ℂ] ℂ).analyticAt 0) rfl
  have hph0 : MvPowerSeries.constantCoeff (ph ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε :
      MvPowerSeries Unit ℂ_[ℓ]) = 0 := constantCoeff_ph hℓ _ _ _ _
  rw [ltS_sum ι' hA univ (G := fun j z => a j * ∏ p, facT sd (r j p) (z p)) fun j _ =>
    analyticAt_const.mul (hprod j)]
  refine isGB_sum _ fun j _ => ?_
  rw [ltS_smul ι' hA (a j) (hprod j), ltS_prod_coord ι' hA _ fun p => hfa _]
  refine IsGB.C_mul ?_ _
  refine isGB_prod _ (fun p _ => PowerSeries.constantCoeff_subst_eq_zero (hY0 p) _ hph0) fun p _ => ?_
  rw [← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hz0)
    (HasSubst.of_constantCoeff_zero (hY0 p))]
  exact (isGB_facT h5 hd4 hsd hΔ ι' h2 h3 hε ht (r j p) hMℓ (hM j p)).subst hph0 (fun _ => hY p) fun _ => hY0 p

end Model

/-! ## The quadratic part -/

section Quad

open FormalQuad

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The explicit Gaussian** `Ψ = Σ_i u_i·(γ/2)·serAB(X_i, X_i)`. -/
def gaussPsi (γ : ℂ_[ℓ]) (u : ι → ℕ) : MvPowerSeries ι ℂ_[ℓ] :=
  ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) *
    MvPowerSeries.subst ![(MvPowerSeries.X i : MvPowerSeries ι ℂ_[ℓ]), MvPowerSeries.X i] (serAB ℓ)

/-- **The block quaternion matrix** on `Fin 4 × ι`: `M_{(k,i),(l,j)} = [i = j]·Q_i(k, l)`. -/
def quatM (Q : ι → Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 4 × ι) (Fin 4 × ι) ℚ :=
  fun p p' => if p'.2 = p.2 then Q p.2 p.1 p'.1 else 0

omit [DecidableEq ι] in
/-- **`Ψ` has no constant term.** -/
theorem constantCoeff_gaussPsi (γ : ℂ_[ℓ]) (u : ι → ℕ) : MvPowerSeries.constantCoeff (gaussPsi γ u) = 0 := by
  rw [gaussPsi, map_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair (MvPowerSeries.constantCoeff_X i)
    (MvPowerSeries.constantCoeff_X i)) (fun j => by fin_cases j <;> simp) constantCoeff_serAB, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- **Substituting into `F(X_x, X_x)`.** -/
theorem subst_pair_X {σ τ : Type} (F : MvPowerSeries (Fin 2) ℂ_[ℓ]) (x : σ)
    {ψ : σ → MvPowerSeries τ ℂ_[ℓ]} (hψ : MvPowerSeries.HasSubst ψ) :
    MvPowerSeries.subst ψ (MvPowerSeries.subst ![(MvPowerSeries.X x : MvPowerSeries σ ℂ_[ℓ]), MvPowerSeries.X x] F) =
      MvPowerSeries.subst ![ψ x, ψ x] F := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair (MvPowerSeries.constantCoeff_X x)
    (MvPowerSeries.constantCoeff_X x)) hψ]
  congr 1
  funext j
  fin_cases j <;> simp [MvPowerSeries.subst_X hψ]

omit [DecidableEq ι] in
/-- **The `k`-th copy of `Ψ`**: `Ψ(X_{k,·}) = Σ_i u_i·(γ/2)·serAB(X_{(k,i)}, X_{(k,i)})`. -/
theorem rename_gaussPsi (γ : ℂ_[ℓ]) (u : ι → ℕ) (k : Fin 4) :
    MvPowerSeries.rename (emb4 k) (gaussPsi γ u) = ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) *
      MvPowerSeries.subst ![(MvPowerSeries.X (k, i) : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]), MvPowerSeries.X (k, i)]
        (serAB ℓ) := by
  rw [gaussPsi, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_eq_subst,
    subst_pair_X _ _ (MvPowerSeries.HasSubst.X_comp _)]
  rfl

/-- **`MᵀM` is diagonal**: `(MᵀM)_{(l,i),(l′,i′)} = [(l, i) = (l′, i′)]·u_i` when `Q_iᵀQ_i = u_i·1`. -/
theorem quatM_mul (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ)
    (hQ : ∀ i, (Q i).transpose * Q i = (u i : ℚ) • 1) (p p' : Fin 4 × ι) :
    ((quatM Q).transpose * quatM Q) p p' = if p = p' then (u p.2 : ℚ) else 0 := by
  obtain ⟨l, i⟩ := p
  obtain ⟨l', i'⟩ := p'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quatM, Fintype.sum_prod_type]
  have e : ∀ k, (∑ j, (if i = j then Q j k l else 0) * (if i' = j then Q j k l' else 0)) =
      if i' = i then Q i k l * Q i k l' else 0 := fun k => by
    rw [sum_eq_single i (fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zero_mul]) (by simp)]
    by_cases h : i' = i <;> simp [h]
  simp only [e]
  by_cases h : i' = i
  · subst h
    have hq := congrFun (congrFun (hQ i') l) l'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hq
    simp only [ite_true, hq, Prod.mk.injEq, and_true]
    by_cases hl : l = l' <;> simp [hl]
  · rw [sum_eq_zero fun k _ => ite_eq_right h]
    have : ¬ (l, i) = (l', i') := fun h' => h (congrArg Prod.snd h').symm
    rw [ite_eq_right this]

/-- **The quadratic part**: `Σ_k Ψ(X_{k,·}) ≃ Σ_p ph(Y_p)` for `Y_p = ⊕_{p′} [M_{pp′}]X_{p′}`. By `quad_transfer`,
`Σ_p ph(Y_p) ≃ Σ_p (MᵀM)_{pp}·ph(X_p) = Σ_p u_{p₂}·ph(X_p)` (`quatM_mul`), and `ph ≃ (γ/2)·serAB(X, X)`
(`ph_simeq_serAB_diag`, substituted at `X_p`). The order on `Fin 4 × ι` that `quad_transfer` needs is arbitrary, as
`MᵀM` is diagonal. -/
theorem simeq_quad (hℓ2 : ℓ ≠ 2) {a b s ε γ : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    (hbe : Simeq (be ℓ a b s ε) (MvPowerSeries.C γ * serAB ℓ)) (u : ι → ℕ) (Q : ι → Matrix (Fin 4) (Fin 4) ℚ)
    (hQ : ∀ i, (Q i).transpose * Q i = (u i : ℚ) • 1) (hQn : ∀ i k l, ‖(Q i k l : ℚ_[ℓ])‖ ≤ 1) :
    Simeq (∑ k : Fin 4, MvPowerSeries.rename (emb4 k) (gaussPsi γ u))
      (∑ p, PowerSeries.subst (linLT fun p' => (quatM Q p p' : ℂ_[ℓ])) (ph ℓ a b s ε)) := by
  let _ : LinearOrder (Fin 4 × ι) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hMn : ∀ p p', ‖(quatM Q p p' : ℚ_[ℓ])‖ ≤ 1 := fun p p' => by
    simp only [quatM]
    split_ifs
    · exact hQn _ _ _
    · simp
  have hT := quad_transfer hℓ2 ha hb hε hAdd hODE ht (quatM Q) hMn
  have hquad : quadPh (ph ℓ a b s ε) (be ℓ a b s ε) (((quatM Q).transpose * quatM Q).map fun q => (q : ℂ_[ℓ])) =
      ∑ p, MvPowerSeries.C ((u p.2 : ℕ) : ℂ_[ℓ]) * PowerSeries.subst (MvPowerSeries.X p) (ph ℓ a b s ε) := by
    rw [quadPh, sum_eq_zero (s := univ) (f := fun i => ∑ j, if i < j then _ else 0) fun i _ => sum_eq_zero fun j _ => by
      split_ifs with hij
      · rw [Matrix.map_apply, quatM_mul u Q hQ, ite_eq_right (ne_of_lt hij), Rat.cast_zero, map_zero, zero_mul]
      · rfl, add_zero]
    refine sum_congr rfl fun p _ => ?_
    rw [Matrix.map_apply, quatM_mul u Q hQ, ite_eq_left rfl, Rat.cast_natCast]
  have h1 := ph_simeq_serAB_diag hℓ2 ha hb hε hAdd hODE ht hbe
  have hdiag : Simeq (∑ p : Fin 4 × ι, MvPowerSeries.C ((u p.2 : ℕ) : ℂ_[ℓ]) *
      PowerSeries.subst (MvPowerSeries.X p) (ph ℓ a b s ε))
      (∑ k : Fin 4, MvPowerSeries.rename (emb4 k) (gaussPsi γ u)) := by
    have hp : ∀ p : Fin 4 × ι, Simeq (MvPowerSeries.C ((u p.2 : ℕ) : ℂ_[ℓ]) *
        PowerSeries.subst (MvPowerSeries.X p) (ph ℓ a b s ε))
        (MvPowerSeries.C ((u p.2 : ℂ_[ℓ]) * (γ / 2)) *
          MvPowerSeries.subst ![(MvPowerSeries.X p : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]), MvPowerSeries.X p]
            (serAB ℓ)) := by
      intro p
      have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X p : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ])) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X p
      have h2 := (h1.subst (ψ := fun _ : Unit => (MvPowerSeries.X p : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]))
        (fun _ => isIntK_X p) fun _ => MvPowerSeries.constantCoeff_X p).natCast_mul (u p.2)
      rw [MvPowerSeries.subst_mul hX, MvPowerSeries.subst_C, subst_pair_X _ _ hX, ← mul_assoc, ← map_mul] at h2
      exact h2
    refine (simeq_sum _ fun p _ => hp p).trans (simeq_of_eq ?_)
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun k _ => (rename_gaussPsi γ u k).symm
  rw [hquad] at hT
  exact (hT.trans hdiag).symm

end Quad

/-! ## Coordinates, and the factorisation given the classification -/

section Assembly

open ThetaChain ThetaNorm ChainCanon CMThetaOne CMEquiv ThetaCompare ThetaHeis HermGS FormalQuad MvTay

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The linear combination map** `x ↦ Σ_k x_k·v_k`. -/
def linComb {κ ι' : Type} [Fintype κ] (v : κ → ι' → ℂ) : (κ → ℂ) →ₗ[ℂ] (ι' → ℂ) where
  toFun x := ∑ k, x k • v k
  map_add' x y := by simp only [Pi.add_apply, add_smul, sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_sum, mul_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- **`linComb`, by definition.** -/
theorem linComb_eq {κ ι' : Type} [Fintype κ] (v : κ → ι' → ℂ) (x : κ → ℂ) : linComb v x = ∑ k, x k • v k :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **`linComb`, coordinatewise.** -/
theorem linComb_apply {κ ι' : Type} [Fintype κ] (v : κ → ι' → ℂ) (x : κ → ℂ) (p : ι') :
    linComb v x p = ∑ k, x k * v k p := by
  simp [linComb, Finset.sum_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- **`linComb` on a basis vector.** -/
theorem linComb_single {κ ι' : Type} [Fintype κ] [DecidableEq κ] (v : κ → ι' → ℂ) (k : κ) :
    linComb v (Pi.single k 1) = v k := by
  funext p
  rw [linComb_apply, sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp),
    Pi.single_eq_same, one_mul]

/-- **`slot_l` as a linear map.** -/
def slotL (l : Fin 4) : (ι → ℂ) →ₗ[ℂ] (Fin 4 × ι → ℂ) where
  toFun := slotV l
  map_add' := slotV_add l
  map_smul' := slotV_smul l

/-- **The theta at `ℓ` in the Lubin–Tate coordinates of the basis `β`**: the Taylor series of `θ` at `0`, carried
to `ℂ_ℓ` by `ι′`, at the point `Σ_i ε·L(X_i)·β_i` (`β_i = δ⁻¹b_i` for a `GSBasis`). -/
def thetaLT (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) (β : ι → (ι → ℂ)) (θ : (ι → ℂ) → ℂ) : MvPowerSeries ι ℂ_[ℓ] :=
  MvPowerSeries.subst (fun p => ∑ i, MvPowerSeries.C (ε * ι' (β i p)) *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι ℂ_[ℓ]) (logLT ℂ_[ℓ] ℓ))
    (MvPowerSeries.map (ι' : ℂ →+* ℂ_[ℓ]) (mtay θ))

/-- **The points `ε·L(Y_p)` can be substituted.** -/
theorem hasSubst_zLT (ε : ℂ_[ℓ]) {κ σ : Type} [Finite κ] {Y : κ → MvPowerSeries σ ℂ_[ℓ]}
    (hY0 : ∀ p, MvPowerSeries.constantCoeff (Y p) = 0) :
    MvPowerSeries.HasSubst (fun p => PowerSeries.subst (Y p) (zLT ℓ ε)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun p =>
    PowerSeries.constantCoeff_subst_eq_zero (hY0 p) _ (constantCoeff_zLT hℓp.out.one_lt ε)

/-- **`ε·L` at a point.** -/
theorem subst_zLT (ε : ℂ_[ℓ]) {σ : Type} {Y : MvPowerSeries σ ℂ_[ℓ]} (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    PowerSeries.subst Y (zLT ℓ ε) = MvPowerSeries.C ε * PowerSeries.subst Y (logLT ℂ_[ℓ] ℓ) := by
  rw [zLT, PowerSeries.subst_mul (HasSubst.of_constantCoeff_zero hY0), PowerSeries.subst_C]

/-- **`thetaLT` as a Lubin–Tate series** of `θ ∘ V_β`, `V_β(x) = Σ_i x_i·β_i`, at the points `ε·L(X_i)`. -/
theorem thetaLT_eq_ltS (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) (β : ι → (ι → ℂ)) {θ : (ι → ℂ) → ℂ}
    (hθ : AnalyticAt ℂ θ 0) :
    thetaLT ι' ε β θ = ltS ι' (fun p => PowerSeries.subst (MvPowerSeries.X p : MvPowerSeries ι ℂ_[ℓ]) (zLT ℓ ε))
      (θ ∘ linComb β) := by
  rw [ltS_comp_linear ι' (hasSubst_zLT ε fun p => MvPowerSeries.constantCoeff_X p) (linComb β) hθ, thetaLT, ltS]
  congr 1
  funext p
  refine sum_congr rfl fun i _ => ?_
  rw [linComb_single, subst_zLT ε (MvPowerSeries.constantCoeff_X i), map_mul]
  ring

/-- **The Gaussian factorisation, given the classification constant** (D1b-6, core): for `θ ∈ Th(C)`, `C` an
`ω`-stable self-dual theta lattice, an `ℓ`-adapted `GSBasis`, a Lubin–Tate unit `ε` (CM-b) and `be ≃ γ·serAB`,
`θ = c₀·exp(−Ψ)·U` in the coordinates of the basis, with `U` integral. Proof: four squares and `orth4_spec`;
`theta_compare` on `C⁴` gives `θ^{⊗4} = c·Θ_g`; `Θ_g` is a finite sum of products of translates
(`Iop_F0c_eq_sum`), so `θ` is analytic (`θ(v)θ(a)³ = θ^{⊗4}(v, a, a, a)`); in Lubin–Tate coordinates
`θ^{⊗4} = exp(−Σ_p ph(Y_p))·(bounded)` (`isGB_ltS_facT`, with `Y = M·X` from `gE(W x) = V₄x`), `Σ_p ph(Y_p) ≃
Σ_k Ψ(X_{k,·})` (`simeq_quad`), and the diagonal trick (`isBddK_of_tens4S`). -/
theorem theta_gauss_core (h5 : 5 ≤ ℓ) {d : ℕ} {sd : ℝ} (hd : Squarefree d) (hd8 : d % 8 = 7)
    (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (ι' : ℂ ≃+* ℂ_[ℓ])
    (h2 : ‖ι' (cmLat sd).g₂‖ ≤ 1) (h3 : ‖ι' (cmLat sd).g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃)).subst (zLT ℓ ε))) {γ : ℂ_[ℓ]}
    (hbe : Simeq (be ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε)
      (MvPowerSeries.C γ * serAB ℓ))
    {C : AddSubgroup (ι → ℂ)} (hCt : IsThetaLat (sC sd) sd C) (hCd : IsEDual (sC sd) C)
    (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {θ : (ι → ℂ) → ℂ} (hθ : θ ∈ Th (sC sd) sd C)
    (B : GSBasis ℓ (sC sd) sd (omegaD sd) C) :
    ∃ (c₀ : ℂ_[ℓ]) (U : MvPowerSeries ι ℂ_[ℓ]), IsIntK U ∧
      thetaLT ι' ε (fun i => (deltaC sd)⁻¹ • B.b i) θ = MvPowerSeries.C c₀ * (expMv (-gaussPsi γ B.u) * U) := by
  classical
  have hℓ := hℓp.out.one_lt
  have hℓ2 : ℓ ≠ 2 := by omega
  have hd4 : d % 4 = 3 := by omega
  set β : ι → ι → ℂ := fun i => (deltaC sd)⁻¹ • B.b i with hβ
  set Ψ := gaussPsi γ B.u with hΨ
  have hΨ0 : MvPowerSeries.constantCoeff Ψ = 0 := constantCoeff_gaussPsi γ B.u
  -- it suffices to bound `θ·exp(Ψ)` in Lubin–Tate coordinates
  suffices hB : IsBddK (thetaLT ι' ε β θ * expMv Ψ) by
    obtain ⟨c₀, U, hU, hcU⟩ := exists_eq_C_mul_of_isBddK hB
    refine ⟨c₀, U, hU, ?_⟩
    have hinv : expMv Ψ * expMv (-Ψ) = 1 := by
      rw [← expMv_add hΨ0 (by rw [map_neg, hΨ0, neg_zero]), add_neg_cancel, expMv_zero]
    calc thetaLT ι' ε β θ = thetaLT ι' ε β θ * expMv Ψ * expMv (-Ψ) := by rw [mul_assoc, hinv, mul_one]
      _ = _ := by rw [hcU]; ring
  -- four squares, the isometry `g`, the comparison `θ^{⊗4} = c·Θ_g`
  choose qa qb qc qe hsq using fun i => Nat.sum_four_squares (B.u i)
  set Q : ι → Matrix (Fin 4) (Fin 4) ℚ := fun i => quatL (qa i) (qb i) (qc i) (qe i) with hQdef
  have hsqZ : ∀ i, ((qa i : ℤ)) ^ 2 + (qb i : ℤ) ^ 2 + (qc i : ℤ) ^ 2 + (qe i : ℤ) ^ 2 = B.u i := fun i => by
    exact_mod_cast hsq i
  obtain ⟨hbij, hiso, hLA⟩ := orth4_spec hsd hΔ B (fun i => (qa i : ℤ)) (fun i => (qb i : ℤ))
    (fun i => (qc i : ℤ)) (fun i => (qe i : ℤ)) hsqZ hω
  set g := orth4 (deltaC sd) B.b B.u Q with hg
  set gE : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ) := LinearEquiv.ofBijective g hbij with hgE
  have hgEg : ∀ x, gE x = g x := fun x => rfl
  have hcomm : IsCommens (pow4 C) ((stdLc sd (Fin 4 × ι)).map gE.toLinearMap.toAddMonoidHom) :=
    isCommens_orth4 hsd hΔ B (fun i => (qa i : ℤ)) (fun i => (qb i : ℤ)) (fun i => (qc i : ℤ))
      (fun i => (qe i : ℤ)) hsqZ hω
  obtain ⟨hC4t, hC4d⟩ := pow4_theta_edual hCt hCd hω
  have hθ4 : tens4 θ ∈ Th (sC sd) sd (pow4 C) :=
    tens4_mem_Th (sdNorm_int_of_smul_mem hCt (by simp [omegaD]) hω) hθ
  obtain ⟨cθ, hcθ⟩ := theta_compare hd hd8 hsd hΔ gE hiso hC4t hC4d hcomm hθ4
  -- the model theta as a finite sum of products of translates
  set C' := (pow4 C).comap gE.toLinearMap.toAddMonoidHom with hC'
  have hc' : IsCommens C' (stdLc sd (Fin 4 × ι)) := isCommens_comap gE hcomm
  have hfin : (stdLc sd (Fin 4 × ι) ⊓ C').relIndex C' ≠ 0 := by rw [inf_comm]; exact hc'.1
  obtain ⟨α, _, r, aa, hr, hIop⟩ := Iop_F0c_eq_sum sd C' hfin
  set IopF : (Fin 4 × ι → ℂ) → ℂ := fun z => ∑ j, aa j * ∏ p, facT sd (r j p) (z p) with hIopF
  have hΘ : ∀ x, tens4 θ x = cθ * IopF (gE.symm x) := fun x => by
    rw [hcθ]
    simp only [Pi.smul_apply, smul_eq_mul, thetaAdapt, Function.comp]
    rw [← hC', hIop]
  have hIopA : ∀ z, AnalyticAt ℂ IopF z := analyticAt_sum_prod_facT sd r aa
  -- the multiplier: `M·q ∈ Lc^K` for the representatives `q`
  obtain ⟨Mℓ, -, hMℓ, hM1, -⟩ := hLA
  have hMr : ∀ j p, (Mℓ : ℂ) * r j p ∈ (cmLat sd).lattice := fun j p => by
    have h1 := hM1 _ (AddSubgroup.mem_comap.1 (hr j))
    obtain ⟨y, hy, hyeq⟩ := AddSubgroup.mem_map.1 h1
    have hyM : y = Mℓ • r j := hbij.1 (by
      rw [map_nsmul]
      exact hyeq)
    have := mem_stdLc.1 (hyM ▸ hy) p
    simpa [nsmul_eq_mul] using this
  -- `θ = 0` is trivial; otherwise `θ` is analytic, through `θ(v)·θ(a₀)³ = θ^{⊗4}(v, a₀, a₀, a₀)`
  by_cases hθ0 : ∀ v, θ v = 0
  · have h0 : θ = fun _ => 0 := funext hθ0
    have : thetaLT ι' ε β θ = 0 := by
      rw [thetaLT_eq_ltS ι' ε β (by rw [h0]; exact analyticAt_const), ltS, h0,
        show ((fun _ : ι → ℂ => (0 : ℂ)) ∘ linComb β) = fun _ => 0 from rfl, mtay_const, map_zero, map_zero,
        ← MvPowerSeries.coe_substAlgHom (hasSubst_zLT ε fun p => MvPowerSeries.constantCoeff_X p), map_zero]
    rw [this, zero_mul]
    exact ⟨0, fun n => by simp⟩
  push Not at hθ0
  obtain ⟨a₀, ha₀⟩ := hθ0
  set w₀ : Fin 4 × ι → ℂ := slotV 1 a₀ + slotV 2 a₀ + slotV 3 a₀ with hw₀
  have hw : ∀ v, tens4 θ (slotV 0 v + w₀) = θ v * θ a₀ ^ 3 := fun v => by
    simp only [tens4, Fin.prod_univ_four, hw₀, map_add, slice_slotV]
    simp
    ring
  have hθeq : θ = fun v => (θ a₀ ^ 3)⁻¹ * (cθ * IopF (gE.symm (slotL 0 v + w₀))) := by
    funext v
    have h1 := hw v
    rw [hΘ] at h1
    change _ = (θ a₀ ^ 3)⁻¹ * (cθ * IopF (gE.symm (slotV 0 v + w₀)))
    rw [h1]
    field_simp
  have hθA : ∀ v, AnalyticAt ℂ θ v := by
    intro v
    rw [hθeq]
    have hL : AnalyticAt ℂ (fun v => gE.symm (slotL 0 v + w₀)) v :=
      ((gE.symm.toLinearMap.toContinuousLinearMap).analyticAt _).comp_of_eq
        ((((slotL 0 : (ι → ℂ) →ₗ[ℂ] (Fin 4 × ι → ℂ)).toContinuousLinearMap).analyticAt v).add analyticAt_const) rfl
    exact analyticAt_const.mul (analyticAt_const.mul ((hIopA _).comp_of_eq hL rfl))
  -- the linear changes of coordinates
  set Vβ := linComb β with hVβ
  set V4 := linComb (fun q : Fin 4 × ι => slotV q.1 (β q.2)) with hV4
  set M := quatM Q with hM
  set W := linComb (fun p' : Fin 4 × ι => fun p => ((M p p' : ℚ) : ℂ)) with hW
  have hQ : ∀ i, (Q i).transpose * Q i = (B.u i : ℚ) • 1 := fun i => by
    rw [hQdef]
    dsimp only
    rw [transpose_mul_quatL]
    congr 1
    exact_mod_cast hsqZ i
  have hQn : ∀ i k l, ‖((Q i k l : ℚ) : ℚ_[ℓ])‖ ≤ 1 := fun i k l => by
    rw [hQdef]
    dsimp only
    rw [quatL_apply, Rat.cast_intCast]
    exact Padic.norm_int_le_one _
  have hδ : deltaC sd ≠ 0 := deltaC_ne_zero hΔ
  have hu0 : ∀ i, B.u i ≠ 0 := fun i => (B.u_pos i).ne'
  have hcol : ∀ p', ∑ p, ((M p p' : ℚ) : ℂ) • orth4Vec (deltaC sd) B.b B.u Q p = slotV p'.1 (β p'.2) := by
    rintro ⟨l, i⟩
    rw [hβ]
    dsimp only
    rw [slotV_smul, slotV_eq_sum hδ hu0 hQ l i, smul_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single i (fun j _ hj => by simp [hM, quatM, Ne.symm hj]) (by simp)]
    simp only [hM, quatM, ite_true]
    rw [smul_smul]
    congr 1
    field_simp
  have hgW : ∀ x, gE (W x) = V4 x := fun x => by
    rw [hgEg, orth4_apply, linComb_eq (fun q : Fin 4 × ι => slotV q.1 (β q.2)) x]
    have e : ∀ p, W x p • orth4Vec (deltaC sd) B.b B.u Q p =
        ∑ p', x p' • (((M p p' : ℚ) : ℂ) • orth4Vec (deltaC sd) B.b B.u Q p) := fun p => by
      rw [linComb_apply, sum_smul]
      exact sum_congr rfl fun p' _ => by rw [mul_smul]
    rw [sum_congr rfl fun p _ => e p, sum_comm]
    exact sum_congr rfl fun p' _ => by rw [← smul_sum, hcol p']
  have hslice : ∀ k x, slice k (V4 x) = Vβ (slice k x) := fun k x => by
    funext p
    rw [linComb_apply]
    change V4 x (k, p) = _
    rw [linComb_apply, Fintype.sum_prod_type,
      sum_eq_single k (fun l _ hl => sum_eq_zero fun i _ => by simp [slotV, Ne.symm hl]) (by simp)]
    refine sum_congr rfl fun i _ => ?_
    show x (k, i) * (if k = k then β i p else 0) = x (k, i) * β i p
    rw [ite_eq_left rfl]
  have htens : tens4 (θ ∘ Vβ) = fun x => cθ * (IopF ∘ W) x := by
    funext x
    have : tens4 (θ ∘ Vβ) x = tens4 θ (V4 x) := by
      simp only [tens4, Function.comp, hslice]
    rw [this, hΘ, ← hgW, LinearEquiv.symm_apply_apply]
    rfl
  -- the points `Y_p = ⊕_{p′} [M_{pp′}]X_{p′}`
  set Y : Fin 4 × ι → MvPowerSeries (Fin 4 × ι) ℂ_[ℓ] := fun p => linLT fun p' => ((M p p' : ℚ) : ℂ_[ℓ]) with hY
  have hMn : ∀ p p', ‖((M p p' : ℚ) : ℚ_[ℓ])‖ ≤ 1 := fun p p' => by
    simp only [hM, quatM]
    split_ifs
    · exact hQn _ _ _
    · simp
  have hYi : ∀ p, IsIntK (Y p) := fun p => isIntK_linLT_rat _ (hMn p)
  have hY0 : ∀ p, MvPowerSeries.constantCoeff (Y p) = 0 := fun p =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_sum_logLT (ℓ := ℓ) _) _ (constantCoeff_expLT _ _)
  have hA4 := hasSubst_zLT (ℓ := ℓ) ε (κ := Fin 4 × ι) fun p => MvPowerSeries.constantCoeff_X p
  have hAY : (fun p => ∑ p', MvPowerSeries.C (ι' (W (Pi.single p' 1) p)) *
      PowerSeries.subst (MvPowerSeries.X p' : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]) (zLT ℓ ε)) =
      fun p => PowerSeries.subst (Y p) (zLT ℓ ε) := by
    funext p
    rw [subst_zLT ε (hY0 p)]
    have hl : PowerSeries.subst (Y p) (logLT ℂ_[ℓ] ℓ) = ∑ p', MvPowerSeries.C ((M p p' : ℚ) : ℂ_[ℓ]) *
        PowerSeries.subst (MvPowerSeries.X p' : MvPowerSeries (Fin 4 × ι) ℂ_[ℓ]) (logLT ℂ_[ℓ] ℓ) :=
      lgP_exP (constantCoeff_sum_logLT (ℓ := ℓ) _)
    rw [hl, mul_sum]
    refine sum_congr rfl fun p' _ => ?_
    rw [hW, linComb_single, map_ratCast, subst_zLT ε (MvPowerSeries.constantCoeff_X p')]
    ring
  -- `θ^{⊗4}` in Lubin–Tate coordinates is Gaussian times bounded
  have hθVA : ∀ z, AnalyticAt ℂ (θ ∘ Vβ) z := fun z =>
    (hθA _).comp_of_eq ((Vβ.toContinuousLinearMap).analyticAt z) rfl
  have hIW : AnalyticAt ℂ (IopF ∘ W) 0 := (hIopA _).comp_of_eq ((W.toContinuousLinearMap).analyticAt 0) rfl
  have e2 : tens4S (thetaLT ι' ε β θ) =
      MvPowerSeries.C (ι' cθ) * ltS ι' (fun p => PowerSeries.subst (Y p) (zLT ℓ ε)) IopF := by
    rw [thetaLT_eq_ltS ι' ε β (hθA 0), ltS_tens4 ι' ε hθVA, htens, ltS_smul ι' hA4 cθ hIW,
      ltS_comp_linear ι' hA4 W (hIopA 0), hAY]
  have hAdd := (addLaw_weierODE_map (cmLat sd) (ι' : ℂ →+* ℂ_[ℓ])).1
  have hODE := (addLaw_weierODE_map (cmLat sd) (ι' : ℂ →+* ℂ_[ℓ])).2
  have hq := simeq_quad hℓ2 h2 h3 hε hAdd hODE ht hbe B.u Q hQ hQn
  have hGB : IsGB (∑ p, PowerSeries.subst (Y p)
      (ph ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε)) (tens4S (thetaLT ι' ε β θ)) := by
    rw [e2]
    exact (isGB_ltS_facT h5 hd4 hsd hΔ ι' h2 h3 hε ht r aa hMℓ hMr Y hYi hY0).C_mul _
  have hP0 : MvPowerSeries.constantCoeff (∑ p, PowerSeries.subst (Y p)
      (ph ℓ (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃) (ι' (s2 (cmLat sd))) ε)) = 0 := by
    rw [map_sum]
    exact sum_eq_zero fun p _ => PowerSeries.constantCoeff_subst_eq_zero (hY0 p) _ (constantCoeff_ph hℓ _ _ _ _)
  have hQ0 : MvPowerSeries.constantCoeff (∑ k : Fin 4, MvPowerSeries.rename (emb4 k) Ψ) = 0 := by
    rw [map_sum]
    exact sum_eq_zero fun k _ => by rw [MvPowerSeries.constantCoeff_rename, hΨ0]
  have hB4 := hGB.isBddK_mul_expMv hq hP0 hQ0
  rw [← tens4S_expMv hΨ0, ← tens4S_mul] at hB4
  exact isBddK_of_tens4S hB4

end Assembly

/-! ## The factorisation -/

section Main

open ThetaChain ThetaNorm ChainCanon CMThetaOne ThetaHeis HermGS

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **D1b's Gaussian factorisation** (orthogonal-with-unit-diagonal coordinates): for `θ ∈ Th(C)`, `C` an
`ω`-stable self-dual theta lattice, and an `ℓ`-adapted `GSBasis`, `θ = c₀·exp(−Ψ)·U` with `U` integral, for the
CM-b unit `ε ∈ K^ur` and the classification constant `γ` (`φ(γ) = −γ`, `‖γ‖ ≤ 1`). The classification is
`CMTorsion.be_simeq_serAB_cm'` (no torsion input: the translates are integral by `CMTorsion.isInt_translate_any`). -/
theorem theta_gauss (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram)
    {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖) {d : ℕ} {sd : ℝ} (hd : Squarefree d)
    (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι' : ℂ ≃+* ℂ_[ℓ]) {C : AddSubgroup (ι → ℂ)}
    (hCt : IsThetaLat (sC sd) sd C) (hCd : IsEDual (sC sd) C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C)
    {θ : (ι → ℂ) → ℂ} (hθ : θ ∈ Th (sC sd) sd C) (B : GSBasis ℓ (sC sd) sd (omegaD sd) C) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ γ : unramC ℓ, φ γ = -γ ∧ ‖γ‖ ≤ 1 ∧ ∃ (c₀ : ℂ_[ℓ]) (U : MvPowerSeries ι ℂ_[ℓ]),
      IsIntK U ∧ thetaLT ι' ε (fun i => (deltaC sd)⁻¹ • B.b i) θ =
        MvPowerSeries.C c₀ * (expMv (-gaussPsi (γ : ℂ_[ℓ]) B.u) * U) := by
  have hd4 : d % 4 = 3 := by omega
  have hcm := hasCM_cmLat hd4 hsd hΔ
  have hΔ1 : (cmLat sd).g₂ ^ 3 - 27 * (cmLat sd).g₃ ^ 2 = 1 := discr_cmLat (sd_pos hd4 hsd).ne' hΔ
  obtain ⟨ε, hεu, hε, htn⟩ := hb d (cmLat sd) hd hd4 hcm hΔ1 ℓ h5 hdℓ hin ι'
  have ht : IsInt ((tSer (ι' (cmLat sd).g₂) (ι' (cmLat sd).g₃)).subst (zLT ℓ ε)) := fun n => (htn n).2
  obtain ⟨γ, hγφ, hγ1, hbe⟩ := CMTorsion.be_simeq_serAB_cm' hj hu hs hd hd4 hcm hΔ1 h5 hdℓ hin ι' hφ hεu hε ht
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ1 h5 ι'
  exact ⟨ε, hεu, hε, γ, hγφ, hγ1, theta_gauss_core h5 hd hd8 hsd hΔ ι' h2 h3 hε ht hbe hCt hCd hω hθ B⟩

/-- **`theta_gauss` for the Frobenius lift `UnramFrobLift.frobUnram`**: no Frobenius input. -/
theorem theta_gauss' (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram)
    {d : ℕ} {sd : ℝ} (hd : Squarefree d)
    (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι' : ℂ ≃+* ℂ_[ℓ]) {C : AddSubgroup (ι → ℂ)}
    (hCt : IsThetaLat (sC sd) sd C) (hCd : IsEDual (sC sd) C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C)
    {θ : (ι → ℂ) → ℂ} (hθ : θ ∈ Th (sC sd) sd C) (B : GSBasis ℓ (sC sd) sd (omegaD sd) C) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ γ : unramC ℓ, UnramFrobLift.frobUnram ℓ γ = -γ ∧ ‖γ‖ ≤ 1 ∧
      ∃ (c₀ : ℂ_[ℓ]) (U : MvPowerSeries ι ℂ_[ℓ]), IsIntK U ∧ thetaLT ι' ε (fun i => (deltaC sd)⁻¹ • B.b i) θ =
        MvPowerSeries.C c₀ * (expMv (-gaussPsi (γ : ℂ_[ℓ]) B.u) * U) :=
  theta_gauss hb hj hu hs UnramFrobLift.norm_frobUnram_sub_pow_le hd hd8 hsd hΔ h5 hdℓ hin ι' hCt hCd hω hθ B

end Main

end

end ThetaGauss
