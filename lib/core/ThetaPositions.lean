import ThetaGauss
import HClass
import UnramFrobLift

/-!
# The theta at an inert prime in frame coordinates: positions and the Gaussian frame form

D1b-8 of the D1b plan, D1b's output in the form D2 consumes (`theta_frame`): in frame coordinates `Z`
(`w = ε·ϖ·Fr·Z`, `ϖ^{ℓ²−1} = ℓ`, `thetaFrame`) with integral basis coordinates `y_i(Z)` (`ycoef`) and the odd twisted
dual-basis identities `Σ_i u_i c_{ix}φ^{2k+1}(c_{iy}) = [x = succ^{2k+1}y]` for the Frobenius successor `succ`, the
theta is `c₀·posGauss(γ)·R`, `posGauss = exp(−(ϖ^{ℓ+1}/ℓ)·γ·posForm)`, with `R` integral and mixed-integral
(`IsMixIntP`: integral in `Z` and, orbit by orbit, `κ!`-integral in `z = ϖZ`).

**The position form** (`twSer`, `posForm`, `posGauss`). `tw(x) = Σ_l (−1)^l Z_{succ^{−2l}x}^{ℓ^{2l}}` and
`posForm = Σ_x u_x·tw(x)^ℓ·tw(succ x)`; `posGauss ∈ HClass(posForm)` (`hClass_posGauss`), and over `V × P` it is the
product of the one-orbit Gaussians (`posGauss_orbits`).

**The frame** (`thetaFrame_eq_subst`). The basis expansion `Σ_i ι′(β_{ip})·ycoef_{ix} = ι′(Fr_{px})` (completeness of
the orthogonal basis `β_i = δ⁻¹b_i`, `gsBasis_orth`) and `L(e(t)) = t` make the frame theta the Lubin–Tate theta
`thetaLT` at `X_i = e(ϖy_i) = ϖ·λ(y_i)`, `λ = expLTInt` (`lamK`, integer coefficients). With `theta_gauss'` this gives
`thetaFrame = c₀·posGauss(γ)·exp(−G)·U(X)` (`thetaFrame_factor`), `G = Ψ(X) − (ϖ^{ℓ+1}/ℓ)·γ·posForm` (`gRem`).

**The leading term mod `ℓ`** (`isDivK_gaussLead_sub`, over `K^ur` with `frobUnram`). From `logLTInt(λ) = T`,
`λ + λ^{ℓ²} ≡ T (mod ℓ)`; the twisted identities give the Frobenius equivariance `φ²(c_{ix}) = c_{i,succ²x}`
(`frob_sq_c`), so `τ_i = Σ_x c_{ix}·tw(x)` satisfies `τ_i = y_i − τ_i^{φ²}(X^{ℓ²})` exactly (`tauS_eq`), and a
contraction (`isDivK_of_contract`: `D_m + D_{m+2} ≡ 0` with `ord D_m ≥ ℓ^m`) gives `λ(y_i) ≡ τ_i`. Then
`Σ_i u_i·λ(y_i)^{ℓ+1} ≡ Σ_i u_i·τ_i^φ(X^ℓ)·τ_i = Σ_x tw(x)^φ(X^ℓ)·tw(succ x) ≡ posForm`. With the small terms of
`serAB` (`norm_coeff_serAB_sub_le`) every coefficient of `G` has norm `≤ ‖ϖ‖^{ℓ+1}` (`norm_coeff_gRem_le`), so
`exp(−G)·U(X)` is integral (`theta_frame_int`, `isIntK_rem`).

**Mixed integrality.** For each set `S` of base orbits the weight `bS(κ) = ∏_{v∈S} ‖ϖ‖^{|κ_v|}/‖κ_v!‖` is
submultiplicative (`IsWeight`), and `R` bounded by every `bS` is mixed-integral (`isMixIntP_of_forall`). Divided
powers (`isWB_pow_of_dp`, `isWB_expMv_of_dp`: `‖c‖^k ≤ ‖k!‖·w(kμ)` for every coefficient) carry the bound to `exp`.
Split `y_i = a_i + b_i` (gain and base coordinates) and `X_i = A_i + R_i`, `A_i = e(ϖa_i)` pure gain; `R_i` is
base-supported with `R_i − ϖb_i` of size `‖ϖ‖^{ℓ²−1−ℓ}` (`isWB_R_sub`), from `‖λ_N‖·‖N‖ ≤ ‖ℓ‖` for `N ≥ 2`
(`norm_coeff_lamK_mul_le`, the one-variable contraction). Then `G` at base exponents is bounded by `bS`
(`norm_coeff_gRem_base`): the binomial terms are `ℓ`-small, and the cross term `Σ_i u_i·A_i^ℓ·ϖb_i` is
`ϖ^{ℓ+1}Σ_q Z_q·Σ_i u_i c_{iq}λ(a_i)^ℓ` with `Σ_i u_i c_{iq}λ(a_i)^ℓ ≡ 0 (mod ℓ)` (`isDivK_cross`: contraction along
the odd Frobenius powers, `[q = succ^{2n+1}x] = 0` across orbits). At gain exponents `G` is small; so `exp(−G)` is
bounded by `bS` (`isWB_rem`), and `U(X)` is since the points are (`isWB_xPt`).

**Main declarations:** `deg`, `mfact`, `twSer`, `posForm`, `posGauss`, `hClass_posGauss`, `posGauss_orbits`,
`thetaFrame`, `ycoef`, `IsMixIntP`, `theta_frame`; on the way `thetaFrame_eq_subst`, `isDivK_gaussLead_sub`,
`theta_frame_int`, `isWB_pow_of_dp`, `isMixIntP_of_forall`, `norm_coeff_gRem_base`, `isWB_rem`.
-/

namespace ThetaPositions

open CMFormalInert CMFormalBiadd ThetaHClass Finset

noncomputable section

/-! ## The position form -/

section PosForm

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ}

/-- Total degree of an exponent. -/
def deg {σ : Type} (n : σ →₀ ℕ) : ℕ := n.sum fun _ e => e

/-- **The factorial of an exponent** `κ! = ∏_x κ_x!`. -/
def mfact {σ : Type} (κ : σ →₀ ℕ) : ℕ := κ.prod fun _ e => e.factorial

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

/-- **The twisted series over any field** (coefficients `±1`), so that `twSer = twF ℂ_ℓ`. -/
def twF (K : Type) [Field K] (ℓ : ℕ) (succ : Equiv.Perm P) (x : P × Fin b × Fin a) :
    MvPowerSeries (P × Fin b × Fin a) K :=
  fun n => ∑ l ∈ range (deg n + 1),
    if n = Finsupp.single (((succ ^ (2 * l)).symm x.1), x.2) (ℓ ^ (2 * l)) then (-1 : K) ^ l else 0

omit [Fintype P] in
/-- **`twSer` is `twF` over `ℂ_ℓ`.** -/
theorem twSer_eq_twF (succ : Equiv.Perm P) (x : P × Fin b × Fin a) :
    twSer (ℓ := ℓ) succ x = twF ℂ_[ℓ] ℓ succ x := rfl

omit [Fintype P] in
/-- **`twF` is carried to `twF`** by ring maps. -/
theorem map_twF {K L : Type} [Field K] [Field L] (f : K →+* L) (ℓ : ℕ) (succ : Equiv.Perm P)
    (x : P × Fin b × Fin a) : MvPowerSeries.map f (twF K ℓ succ x) = twF L ℓ succ x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change f (twF K ℓ succ x n) = twF L ℓ succ x n
  simp only [twF, map_sum, apply_ite f, map_pow, map_neg, map_one, map_zero]

omit [Fintype P] in
/-- **`twF` has no constant term.** -/
theorem constantCoeff_twF (K : Type) [Field K] {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (succ : Equiv.Perm P)
    (x : P × Fin b × Fin a) : MvPowerSeries.constantCoeff (twF K ℓ succ x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change ∑ l ∈ range (deg (0 : P × Fin b × Fin a →₀ ℕ) + 1), _ = _
  refine sum_eq_zero fun l _ => ite_eq_right_iff.2 fun h => ?_
  exact absurd (Finsupp.single_eq_zero.1 h.symm) (pow_ne_zero _ hℓ0)

/-- **The position form has no constant term.** -/
theorem constantCoeff_posForm (succ : Equiv.Perm P) (u : P → ℂ_[ℓ]) :
    MvPowerSeries.constantCoeff (posForm (ℓ := ℓ) (a := a) (b := b) succ u) = 0 := by
  rw [posForm, map_sum]
  refine sum_eq_zero fun x _ => ?_
  rw [map_mul, twSer_eq_twF succ (succ x.1, x.2), constantCoeff_twF _ hℓ.out.ne_zero, mul_zero]

/-- **The class of the Gaussian frame form** (from `hClass_exp`, `HClass.mul`). -/
theorem hClass_posGauss {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (succ : Equiv.Perm P) (u : P → ℂ_[ℓ])
    {V : MvPowerSeries (P × Fin b × Fin a) ℂ_[ℓ]} (hV : IsIntK V) :
    HClass (posForm succ u) (posGauss ϖ succ u * V) :=
  (hClass_exp hϖ _).mul (constantCoeff_posForm succ u) hV

end PosForm

/-! ## The orbit split of the Gaussian -/

section Orbits

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ}
  {V : Type} [Fintype V] [DecidableEq V]

/-- **The embedding of one orbit's variables**: `(s, β, α) ↦ ((v, s), β, α)`. -/
def embV (v : V) : P × Fin b × Fin a ↪ (V × P) × Fin b × Fin a :=
  ⟨fun x => ((v, x.1), x.2), fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.2 h.2⟩

omit [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V] in
/-- **Powers of the successor on `V × P`.** -/
theorem prodCongr_pow_symm (succ : Equiv.Perm P) (n : ℕ) (v : V) (s : P) :
    ((Equiv.prodCongr (Equiv.refl V) succ) ^ n).symm (v, s) = (v, (succ ^ n).symm s) := by
  have h : ∀ t, ((Equiv.prodCongr (Equiv.refl V) succ) ^ n) (v, t) = (v, (succ ^ n) t) := fun t => by
    induction n generalizing t with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]; rfl
  rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]

omit [Fintype P] [Fintype V] in
/-- **The twisted series of an orbit** is the renamed twisted series. -/
theorem twSer_prodCongr (succ : Equiv.Perm P) (v : V) (x : P × Fin b × Fin a) :
    twSer (ℓ := ℓ) (Equiv.prodCongr (Equiv.refl V) succ) ((v, x.1), x.2) =
      MvPowerSeries.rename (embV v) (twSer succ x) := by
  classical
  ext n
  by_cases h : ∃ m, n = Finsupp.embDomain (embV v) m
  · obtain ⟨m, rfl⟩ := h
    rw [MvPowerSeries.coeff_embDomain_rename]
    change ∑ l ∈ range (deg (Finsupp.embDomain (embV v) m) + 1), _ = ∑ l ∈ range (deg m + 1), _
    have hd : deg (Finsupp.embDomain (embV v) m) = deg m := by
      simp only [deg, Finsupp.sum_embDomain]
    rw [hd]
    refine sum_congr rfl fun l _ => ?_
    have e : Finsupp.single (((Equiv.prodCongr (Equiv.refl V) succ ^ (2 * l)).symm ((v, x.1), x.2).1),
        ((v, x.1), x.2).2) (ℓ ^ (2 * l)) =
        Finsupp.embDomain (embV v) (Finsupp.single (((succ ^ (2 * l)).symm x.1), x.2) (ℓ ^ (2 * l))) := by
      rw [Finsupp.embDomain_single, prodCongr_pow_symm]
      rfl
    rw [e]
    simp only [Finsupp.embDomain_inj]
  · push Not at h
    rw [MvPowerSeries.coeff_rename_eq_zero _ _ fun ⟨m, hm⟩ => h m (by
      rw [← hm, Finsupp.embDomain_eq_mapDomain])]
    change ∑ l ∈ range (deg n + 1), _ = 0
    refine sum_eq_zero fun l _ => ite_eq_right fun he => ?_
    refine absurd ?_ (h (Finsupp.single (((succ ^ (2 * l)).symm x.1), x.2) (ℓ ^ (2 * l))))
    rw [he, Finsupp.embDomain_single, prodCongr_pow_symm]
    rfl

/-- **The position form splits over the orbits.** -/
theorem posForm_prodCongr (succ : Equiv.Perm P) (u : V × P → ℂ_[ℓ]) :
    posForm (a := a) (b := b) (Equiv.prodCongr (Equiv.refl V) succ) u =
      ∑ v : V, MvPowerSeries.rename (embV v) (posForm (a := a) (b := b) succ fun s => u (v, s)) := by
  rw [posForm, ← (Equiv.prodAssoc V P (Fin b × Fin a)).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [posForm, map_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [Equiv.prodAssoc_symm_apply, map_mul, map_pow, MvPowerSeries.rename_C]
  rw [twSer_prodCongr, show ((Equiv.prodCongr (Equiv.refl V) succ) (v, x.1), x.2) = ((v, succ x.1), x.2) from rfl,
    show (((v, succ x.1), x.2) : (V × P) × Fin b × Fin a) = ((v, (succ x.1, x.2).1), (succ x.1, x.2).2) from rfl,
    twSer_prodCongr]

/-- **Orbits split the Gaussian**: for positions `V × P` with `succ` acting on `P`, `posGauss` is the product over
the orbits of the one-orbit Gaussians (in disjoint variables). -/
theorem posGauss_orbits (ϖ : ℂ_[ℓ]) (succ : Equiv.Perm P) (u : V × P → ℂ_[ℓ]) :
    posGauss (a := a) (b := b) ϖ (Equiv.prodCongr (Equiv.refl V) succ) u =
      ∏ v : V, MvPowerSeries.rename (fun x : P × Fin b × Fin a => ((v, x.1), x.2))
        (posGauss (a := a) (b := b) ϖ succ fun s => u (v, s)) := by
  have h0 : ∀ v, MvPowerSeries.constantCoeff (-(MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ) *
      MvPowerSeries.rename (embV v) (posForm (a := a) (b := b) succ fun s => u (v, s)))) = 0 := fun v => by
    rw [map_neg, map_mul, MvPowerSeries.constantCoeff_rename, constantCoeff_posForm, mul_zero, neg_zero]
  rw [posGauss, posForm_prodCongr, mul_sum, ← sum_neg_distrib, ThetaGauss.expMv_sum _ fun v _ => h0 v]
  refine prod_congr rfl fun v _ => ?_
  have hP0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ) *
      (posForm (a := a) (b := b) succ fun s => u (v, s)))) = 0 := by
    rw [map_neg, map_mul, constantCoeff_posForm, mul_zero, neg_zero]
  change _ = MvPowerSeries.rename (embV v) _
  rw [posGauss]
  symm
  rw [MvPowerSeries.rename_eq_subst, ThetaGauss.expMv_subst hP0 (MvPowerSeries.HasSubst.X_comp _)
    fun x => MvPowerSeries.constantCoeff_X _, ← MvPowerSeries.rename_eq_subst, map_neg, map_mul,
    MvPowerSeries.rename_C]

end Orbits

/-- **A product of numbers in `[0, 1]`** is at most `1`. -/
theorem mul_le_one_of {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)

/-! ## Congruences modulo `ℓ` -/

section Cong

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit [IsUltrametricDist K] hℓp in
/-- **`ℓ` times an integral series is `ℓ`-divisible.** -/
theorem isDivK_C_mul {g : MvPowerSeries σ K} (hg : IsIntK g) :
    IsDivK ℓ (MvPowerSeries.C (ℓ : K) * g) := fun n => by
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hg n)

omit [IsUltrametricDist K] in
/-- **`ℓ`-divisible series are `ℓ` times integral series.** -/
theorem _root_.CMFormalInert.IsDivK.eq_C_mul [CharZero K] {f : MvPowerSeries σ K} (hf : IsDivK ℓ f) :
    ∃ g, IsIntK g ∧ f = MvPowerSeries.C (ℓ : K) * g := by
  have hℓ0 : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.2 hℓp.out.ne_zero
  refine ⟨MvPowerSeries.C (ℓ : K)⁻¹ * f, fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hf n) (norm_nonneg _)
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hℓ0, map_one, one_mul]

omit hℓp in
/-- **`ℓ`-divisible series are integral.** -/
theorem _root_.CMFormalInert.IsDivK.isIntK {f : MvPowerSeries σ K} (hf : IsDivK ℓ f) : IsIntK f :=
  fun n => (hf n).trans (IsUltrametricDist.norm_natCast_le_one K ℓ)

omit hℓp in
/-- **Integral times `ℓ`-divisible is `ℓ`-divisible.** -/
theorem _root_.CMFormalInert.IsDivK.isInt_mul {f g : MvPowerSeries σ K} (hf : IsIntK f) (hg : IsDivK ℓ g) :
    IsDivK ℓ (f * g) := by
  rw [mul_comm]
  exact hg.mul_isInt hf

omit hℓp in
/-- **Congruent products**: `A ≡ A′`, `B ≡ B′` (mod `ℓ`) with `A`, `B′` integral give `AB ≡ A′B′`. -/
theorem isDivK_mul_sub_mul {A A' B B' : MvPowerSeries σ K} (hA : IsIntK A) (hB' : IsIntK B')
    (h1 : IsDivK ℓ (A - A')) (h2 : IsDivK ℓ (B - B')) : IsDivK ℓ (A * B - A' * B') := by
  have e : A * B - A' * B' = A * (B - B') + (A - A') * B' := by ring
  rw [e]
  exact (h2.isInt_mul hA).add (h1.mul_isInt hB')

omit hℓp in
/-- **Congruent powers**: `A ≡ B (mod ℓ)` with `A`, `B` integral gives `Aⁿ ≡ Bⁿ`. -/
theorem isDivK_pow_sub_pow {A B : MvPowerSeries σ K} (hA : IsIntK A) (hB : IsIntK B) (h : IsDivK ℓ (A - B))
    (n : ℕ) : IsDivK ℓ (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]
  exact h.isInt_mul (isIntK_finsum _ fun i _ => (hA.pow _).mul (hB.pow _))

/-- **Integral substitution keeps `ℓ`-divisibility.** -/
theorem _root_.CMFormalInert.IsDivK.subst [CharZero K] {τ : Type} [Finite σ] {f : MvPowerSeries σ K} (hf : IsDivK ℓ f)
    {ψ : σ → MvPowerSeries τ K} (hψ : ∀ s, IsIntK (ψ s)) (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) :
    IsDivK ℓ (f.subst ψ) := by
  obtain ⟨g, hg, rfl⟩ := hf.eq_C_mul
  rw [MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0), MvPowerSeries.subst_C]
  exact isDivK_C_mul (hg.subst hψ hψ0)

/-- **Integral substitution into a one-variable series keeps `ℓ`-divisibility.** -/
theorem _root_.CMFormalInert.IsDivK.psubst [CharZero K] {f : PowerSeries K} (hf : IsDivK ℓ (f : MvPowerSeries Unit K))
    {Y : MvPowerSeries σ K}
    (hY : IsIntK Y) (hY0 : MvPowerSeries.constantCoeff Y = 0) : IsDivK ℓ (f.subst Y) :=
  IsDivK.subst hf (fun _ => hY) fun _ => hY0

/-- **Integral substitution into a one-variable series keeps integrality.** -/
theorem isIntK_psubst {f : PowerSeries K} (hf : IsInt f) {Y : MvPowerSeries σ K} (hY : IsIntK Y)
    (hY0 : MvPowerSeries.constantCoeff Y = 0) : IsIntK (f.subst Y) :=
  IsIntK.subst hf.isIntK (fun _ => hY) fun _ => hY0

omit [IsUltrametricDist K] in
/-- **Frobenius commutes with substitution** into a one-variable series with `φ`-fixed coefficients. -/
theorem frobS_psubst (φ : K →+* K) {f : PowerSeries K} (hf : PowerSeries.map φ f = f)
    {Y : MvPowerSeries σ K} (hY : MvPowerSeries.constantCoeff Y = 0) :
    frobS ℓ φ (f.subst Y) = f.subst (frobS ℓ φ Y) := by
  have has : PowerSeries.HasSubst Y := PowerSeries.HasSubst.of_constantCoeff_zero hY
  have hma : PowerSeries.HasSubst (MvPowerSeries.map φ Y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_map, hY, map_zero])
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ (f.subst Y)) =
    f.subst (MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ Y))
  rw [PowerSeries.map_subst has, hf, PowerSeries.expand_subst _ _ hma]

omit [IsUltrametricDist K] in
/-- **The Frobenius of a series without constant term has no constant term.** -/
theorem constantCoeff_frobS_eq_zero (φ : K →+* K) {Y : MvPowerSeries σ K}
    (hY : MvPowerSeries.constantCoeff Y = 0) : MvPowerSeries.constantCoeff (frobS ℓ φ Y) = 0 := by
  rw [constantCoeff_frobS, hY, map_zero]

/-- **Contraction**: if `D_m + D_{m+2} ≡ 0 (mod ℓ)` for every `m` and `D_m` vanishes below degree `ℓ^m`, then
every `D_m ≡ 0`: `D_m ≡ ±D_{m+2L}`, which vanishes in any given degree for `L` large. -/
theorem isDivK_of_contract {D : ℕ → MvPowerSeries σ K} (hD : ∀ m, IsDivK ℓ (D m + D (m + 2)))
    (hord : ∀ m, ((ℓ ^ m : ℕ) : ℕ∞) ≤ (D m).order) (m : ℕ) : IsDivK ℓ (D m) := by
  intro n
  have key : ∀ L m, ‖MvPowerSeries.coeff n (D m) - (-1) ^ L * MvPowerSeries.coeff n (D (m + 2 * L))‖ ≤
      ‖(ℓ : K)‖ := by
    intro L
    induction L with
    | zero => intro m; simp
    | succ L ih =>
      intro m
      have e : MvPowerSeries.coeff n (D m) - (-1) ^ (L + 1) * MvPowerSeries.coeff n (D (m + 2 * (L + 1))) =
          (MvPowerSeries.coeff n (D m) - (-1) ^ L * MvPowerSeries.coeff n (D (m + 2 * L))) +
            (-1) ^ L * MvPowerSeries.coeff n (D (m + 2 * L) + D (m + 2 * L + 2)) := by
        rw [map_add, show m + 2 * (L + 1) = m + 2 * L + 2 by ring]
        ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih m) ?_)
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hD _ n
  have hL : n.degree < ℓ ^ (m + 2 * n.degree) := by
    have h2 := hℓp.out.two_le
    calc n.degree < 2 ^ n.degree := Nat.lt_two_pow_self
      _ ≤ ℓ ^ n.degree := Nat.pow_le_pow_left h2 _
      _ ≤ ℓ ^ (m + 2 * n.degree) := Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : MvPowerSeries.coeff n (D (m + 2 * n.degree)) = 0 :=
    MvPowerSeries.coeff_of_lt_order ((ENat.natCast_lt_natCast.2 hL).trans_le (hord _))
  have := key n.degree m
  rwa [h0, mul_zero, sub_zero] at this

end Cong

/-! ## The rescaled exponential `λ` and its congruences -/

section Lam

/-- **The rescaled Lubin–Tate exponential** `λ` (`expLTInt`, integer coefficients): `e(πT) = π·λ(T)` for
`π^{ℓ²−1} = ℓ`. -/
def lamK (K : Type) [Field K] (ℓ : ℕ) : PowerSeries K := PowerSeries.map (Int.castRingHom K) (expLTInt ℓ)

/-- **`λ` is carried to `λ`** by ring maps. -/
theorem map_lamK {K L : Type} [Field K] [Field L] (f : K →+* L) (ℓ : ℕ) :
    PowerSeries.map f (lamK K ℓ) = lamK L ℓ := by
  rw [lamK, lamK, ← RingHom.comp_apply (PowerSeries.map f), ← PowerSeries.map_comp]
  congr 2
  exact RingHom.ext_int _ _

/-- **`λ` has no constant term.** -/
theorem constantCoeff_lamK (K : Type) [Field K] (ℓ : ℕ) : PowerSeries.constantCoeff (lamK K ℓ) = 0 := by
  rw [lamK, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_expLTInt, map_zero]

/-- **`λ` is integral.** -/
theorem isInt_lamK (K : Type) [NormedField K] [IsUltrametricDist K] (ℓ : ℕ) : IsInt (lamK K ℓ) := fun n => by
  rw [lamK, PowerSeries.coeff_map]
  exact IsUltrametricDist.norm_intCast_le_one K _

/-- **`e(πY) = π·λ(Y)`** for `π^{ℓ²−1} = ℓ` (`expLT_eq`). -/
theorem expLT_subst_C_mul {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K}
    (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) {σ : Type} {Y : MvPowerSeries σ K} (hY : MvPowerSeries.constantCoeff Y = 0) :
    (expLT K ℓ).subst (MvPowerSeries.C π * Y) = MvPowerSeries.C π * (lamK K ℓ).subst Y := by
  have hπ0 : π ≠ 0 := ne_zero_of_pow_eq hℓ hπ
  have hCY : PowerSeries.HasSubst (MvPowerSeries.C π * Y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul, hY, mul_zero])
  have hrX : PowerSeries.HasSubst (π⁻¹ • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [expLT_eq hℓ hπ, PowerSeries.subst_mul hCY, PowerSeries.subst_C, ← lamK,
    PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hrX hCY]
  congr 2
  rw [PowerSeries.subst_smul hCY, PowerSeries.subst_X hCY, MvPowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hπ0, map_one, one_mul]

/-- **The exponent `c_1 = 0`.** -/
theorem cExp_one (ℓ : ℕ) : cExp ℓ 1 = 0 := by simp [cExp]

/-- **The exponents `c_j ≥ 1` for `j ≥ 2`.** -/
theorem one_le_cExp {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {j : ℕ} (hj : 2 ≤ j) : 1 ≤ cExp ℓ j := by
  have h : ∑ i ∈ range j, (1 + if i = 1 then 3 else 0) ≤ ∑ i ∈ range j, ℓ ^ (2 * i) := by
    refine sum_le_sum fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one]
      nlinarith
    · simpa using Nat.one_le_pow _ _ (by omega)
  rw [sum_add_distrib, sum_ite_eq' (range j) 1, ite_eq_left (mem_range.2 (by omega))] at h
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at h
  unfold cExp
  omega

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit [IsUltrametricDist K] [CharZero K] hℓp in
/-- **`ℓ`-divisibility of a one-variable series**, coefficientwise. -/
theorem isDivK_of_coeff {f : PowerSeries K} (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ ‖(ℓ : K)‖) :
    IsDivK ℓ (f : MvPowerSeries Unit K) := fun n => by
  have : n = Finsupp.single () (n ()) := by ext; simp
  rw [this]
  exact h (n ())

omit [CharZero K] in
/-- **The rescaled logarithm mod `ℓ`**: `g ≡ T + T^{ℓ²} (mod ℓ)` (`c_0 = c_1 = 0`, `c_j ≥ 1` for `j ≥ 2`). -/
theorem isDivK_logLTInt_sub :
    IsDivK ℓ ((PowerSeries.map (Int.castRingHom K) (logLTInt ℓ) - PowerSeries.X -
      PowerSeries.X ^ (ℓ ^ 2) : PowerSeries K) : MvPowerSeries Unit K) := by
  have hℓ := hℓp.out
  have h2 := hℓ.two_le
  have hn1 : ‖(ℓ : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K ℓ
  refine isDivK_of_coeff fun k => ?_
  rw [map_sub, map_sub, PowerSeries.coeff_map, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hk : ∃ j : ℕ, k = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := hk
    rw [coeff_logLTInt_pow hℓ.one_lt]
    rcases j with _ | _ | j
    · have : ℓ ^ 2 ≠ 1 := by nlinarith
      simp [cExp, Ne.symm this]
    · simp [cExp_one, hℓ.one_lt.ne']
    · have h1 : ℓ ^ (2 * (j + 2)) ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
      have h3 : ℓ ^ (2 * (j + 2)) ≠ ℓ ^ 2 := fun h => by
        have := Nat.pow_right_injective h2 h
        omega
      rw [ite_eq_right h1, ite_eq_right h3, sub_zero, sub_zero, map_pow, map_natCast, norm_pow]
      obtain ⟨c, hc⟩ : ∃ c, cExp ℓ (j + 2) = c + 1 := ⟨cExp ℓ (j + 2) - 1, by
        have := one_le_cExp h2 (show 2 ≤ j + 2 by omega); omega⟩
      rw [hc, pow_succ]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hn1)
  · push Not at hk
    rw [coeff_logLTInt_of_ne hk, ite_eq_right (by simpa using hk 0), ite_eq_right (fun h => hk 1 (by simpa using h))]
    simp

/-- **`λ + λ^{ℓ²} ≡ T (mod ℓ)`**: substitute `λ` into `g ≡ T + T^{ℓ²}`, as `g(λ) = T`. -/
theorem isDivK_lamK_add_pow :
    IsDivK ℓ ((lamK K ℓ + lamK K ℓ ^ (ℓ ^ 2) - PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  have hℓ := hℓp.out
  have h0 := constantCoeff_lamK K ℓ
  have hs : PowerSeries.HasSubst (lamK K ℓ) := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hg : (PowerSeries.map (Int.castRingHom K) (logLTInt ℓ)).subst (lamK K ℓ) = PowerSeries.X := by
    have h := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_expLTInt ℓ))
      (h := Int.castRingHom K) (logLTInt ℓ)
    rw [logLTInt_subst_expLTInt hℓ.one_lt,
      show (MvPowerSeries.map (Int.castRingHom K)) PowerSeries.X = PowerSeries.X from MvPowerSeries.map_X _ _] at h
    exact h.symm
  have h := (isDivK_logLTInt_sub (K := K) (ℓ := ℓ)).psubst (σ := Unit) (isInt_lamK K ℓ).isIntK h0
  rw [PowerSeries.subst_sub hs, PowerSeries.subst_sub hs, hg, PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs] at h
  have e : lamK K ℓ + lamK K ℓ ^ (ℓ ^ 2) - PowerSeries.X =
      -(PowerSeries.X - lamK K ℓ - lamK K ℓ ^ (ℓ ^ 2)) := by ring
  rw [e]
  exact h.neg

variable {σ : Type}

/-- **`λ(Y) + λ(Y)^{ℓ²} ≡ Y (mod ℓ)`** for integral `Y` without constant term. -/
theorem isDivK_lamK_subst_add_pow {Y : MvPowerSeries σ K} (hY : IsIntK Y)
    (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    IsDivK ℓ ((lamK K ℓ).subst Y + ((lamK K ℓ).subst Y) ^ (ℓ ^ 2) - Y) := by
  have hs : PowerSeries.HasSubst Y := PowerSeries.HasSubst.of_constantCoeff_zero hY0
  have h := (isDivK_lamK_add_pow (K := K) (ℓ := ℓ)).psubst hY hY0
  rwa [PowerSeries.subst_sub hs, PowerSeries.subst_add hs, PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs] at h

omit [CharZero K] hℓp in
/-- **`λ(Y)` is integral.** -/
theorem isIntK_lamK_subst {Y : MvPowerSeries σ K} (hY : IsIntK Y) (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    IsIntK ((lamK K ℓ).subst Y) :=
  isIntK_psubst (isInt_lamK K ℓ) hY hY0

omit [IsUltrametricDist K] [CharZero K] hℓp in
/-- **`λ(Y)` has no constant term.** -/
theorem constantCoeff_lamK_subst {Y : MvPowerSeries σ K} (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    MvPowerSeries.constantCoeff ((lamK K ℓ).subst Y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hY0 _ (constantCoeff_lamK K ℓ)

omit [IsUltrametricDist K] [CharZero K] in
/-- **Frobenius commutes with `λ`.** -/
theorem frobS_lamK_subst (φ : K →+* K) {Y : MvPowerSeries σ K} (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    frobS ℓ φ ((lamK K ℓ).subst Y) = (lamK K ℓ).subst (frobS ℓ φ Y) :=
  frobS_psubst φ (map_lamK φ ℓ) hY0

variable [Finite σ] {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
include hφ

omit [CharZero K] in
/-- **`λ(Y)^ℓ ≡ λ(Y^φ(X^ℓ)) (mod ℓ)`.** -/
theorem isDivK_lamK_pow_sub_frob {Y : MvPowerSeries σ K} (hY : IsIntK Y)
    (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    IsDivK ℓ (((lamK K ℓ).subst Y) ^ ℓ - (lamK K ℓ).subst (frobS ℓ φ Y)) := by
  have h := (isDivK_frobS_sub_pow_of_isIntK hφ (isIntK_lamK_subst (ℓ := ℓ) hY hY0)).neg
  rwa [frobS_lamK_subst φ hY0, neg_sub] at h

omit [CharZero K] in
/-- **`λ(Y)^{ℓ²} ≡ λ(Y^{φ²}(X^{ℓ²})) (mod ℓ)`.** -/
theorem isDivK_lamK_pow_sq_sub_frob {Y : MvPowerSeries σ K} (hY : IsIntK Y)
    (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    IsDivK ℓ (((lamK K ℓ).subst Y) ^ (ℓ ^ 2) - (lamK K ℓ).subst (frobS ℓ φ (frobS ℓ φ Y))) := by
  have hY' : IsIntK (frobS ℓ φ Y) := hY.frobS hφ
  have hY0' := constantCoeff_frobS_eq_zero (ℓ := ℓ) φ hY0
  have h2 := isDivK_pow_sub_pow ((isIntK_lamK_subst (ℓ := ℓ) hY hY0).pow ℓ) (isIntK_lamK_subst (ℓ := ℓ) hY' hY0')
    (isDivK_lamK_pow_sub_frob hφ hY hY0) ℓ
  have h3 := isDivK_lamK_pow_sub_frob hφ hY' hY0'
  have e : ((lamK K ℓ).subst Y) ^ (ℓ ^ 2) - (lamK K ℓ).subst (frobS ℓ φ (frobS ℓ φ Y)) =
      ((((lamK K ℓ).subst Y) ^ ℓ) ^ ℓ - ((lamK K ℓ).subst (frobS ℓ φ Y)) ^ ℓ) +
        (((lamK K ℓ).subst (frobS ℓ φ Y)) ^ ℓ - (lamK K ℓ).subst (frobS ℓ φ (frobS ℓ φ Y))) := by
    rw [← pow_mul, ← sq]
    ring
  rw [e]
  exact h2.add h3

end Lam

/-! ## The twisted series: recursion and Frobenius -/

section Tw

variable {K : Type} [Field K] {ℓ : ℕ} {P : Type} [DecidableEq P] {a b : ℕ}

/-- **The degree of a single exponent.** -/
theorem deg_single {σ : Type} (y : σ) (k : ℕ) : deg (Finsupp.single y k) = k :=
  Finsupp.sum_single_index rfl

/-- **The degree of a multiple.** -/
theorem deg_smul {σ : Type} (p : ℕ) (n : σ →₀ ℕ) : deg (p • n) = p * deg n := by
  simp only [deg, Finsupp.sum, Finsupp.smul_apply, smul_eq_mul, ← mul_sum]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · rw [Finsupp.support_smul_eq hp.ne']

/-- **Conditional sums along a sequence of exponents** agree over any two ranges containing every index where
the condition holds. -/
theorem sum_range_ite_congr {σ : Type} [DecidableEq σ] {n : σ →₀ ℕ} {g : ℕ → σ →₀ ℕ} (c : ℕ → K) {N N' : ℕ}
    (h : ∀ l, n = g l → l < min N N') :
    ∑ l ∈ range N, (if n = g l then c l else 0) = ∑ l ∈ range N', (if n = g l then c l else 0) := by
  have key : ∀ M, min N N' ≤ M → ∑ l ∈ range M, (if n = g l then c l else 0) =
      ∑ l ∈ range (min N N'), (if n = g l then c l else 0) := fun M hM =>
    (sum_subset (range_subset_range.2 hM) fun l _ hl => ite_eq_right fun he => hl (mem_range.2 (h l he))).symm
  rw [key N (min_le_left _ _), key N' (min_le_right _ _)]

omit [DecidableEq P] in
/-- **Powers of `succ²`**: `(succ^{2l})⁻¹((succ²)⁻¹ s) = (succ^{2(l+1)})⁻¹ s`. -/
theorem perm_pow_symm_succ (succ : Equiv.Perm P) (l : ℕ) (s : P) :
    (succ ^ (2 * l)).symm ((succ ^ 2).symm s) = (succ ^ (2 * (l + 1))).symm s := by
  rw [show 2 * (l + 1) = 2 + 2 * l by ring, pow_add]
  rfl

/-- **`l < ℓ^{2l}`** for `ℓ ≥ 2`. -/
theorem lt_pow_two_mul {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (l : ℕ) : l < ℓ ^ (2 * l) :=
  calc l < 2 ^ l := Nat.lt_two_pow_self
    _ ≤ ℓ ^ l := Nat.pow_le_pow_left hℓ _
    _ ≤ ℓ ^ (2 * l) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **The recursion of the twisted series**: `tw(x) = X_x − tw(succ^{−2}x)(X^{ℓ²})`. -/
theorem twF_eq (hℓ : 2 ≤ ℓ) (succ : Equiv.Perm P) (x : P × Fin b × Fin a) :
    twF K ℓ succ x = MvPowerSeries.X x - MvPowerSeries.expand (ℓ ^ 2) (by positivity)
      (twF K ℓ succ (((succ ^ 2).symm x.1), x.2)) := by
  classical
  have hq : ℓ ^ 2 ≠ 0 := by positivity
  set y : ℕ → P × Fin b × Fin a := fun l => (((succ ^ (2 * l)).symm x.1), x.2) with hy
  ext n
  rw [map_sub, MvPowerSeries.coeff_X]
  change ∑ l ∈ range (deg n + 1), (if n = Finsupp.single (y l) (ℓ ^ (2 * l)) then (-1 : K) ^ l else 0) = _
  rw [sum_range_succ']
  have hy0 : y 0 = x := by simp only [hy, mul_zero, pow_zero]; rfl
  simp only [mul_zero, pow_zero, hy0]
  rw [add_comm, sub_eq_add_neg]
  congr 1
  by_cases hd : ∀ i, ℓ ^ 2 ∣ n i
  · obtain ⟨m, rfl⟩ := exists_eq_smul_of_dvd hd
    rw [MvPowerSeries.coeff_expand_smul]
    change _ = -∑ l ∈ range (deg m + 1), (if m = Finsupp.single
      (((succ ^ (2 * l)).symm ((succ ^ 2).symm x.1)), x.2) (ℓ ^ (2 * l)) then (-1 : K) ^ l else 0)
    have e1 : ∀ l, (m = Finsupp.single (((succ ^ (2 * l)).symm ((succ ^ 2).symm x.1)), x.2) (ℓ ^ (2 * l))) ↔
        (ℓ ^ 2 • m = Finsupp.single (y (l + 1)) (ℓ ^ (2 * (l + 1)))) := fun l => by
      have hs : Finsupp.single (y (l + 1)) (ℓ ^ (2 * (l + 1))) =
          ℓ ^ 2 • Finsupp.single (y (l + 1)) (ℓ ^ (2 * l)) := by
        rw [Finsupp.smul_single, smul_eq_mul, show 2 * (l + 1) = 2 + 2 * l by ring, pow_add]
      rw [hs, smul_right_inj hq, hy]
      dsimp only
      rw [perm_pow_symm_succ]
    simp only [e1]
    have hb : ∀ l, ℓ ^ 2 • m = Finsupp.single (y (l + 1)) (ℓ ^ (2 * (l + 1))) →
        l < min (deg (ℓ ^ 2 • m)) (deg m + 1) := by
      intro l h
      have h1 := congrArg deg h
      rw [deg_single, deg_smul, show 2 * (l + 1) = 2 + 2 * l by ring, pow_add] at h1
      have h2 : deg m = ℓ ^ (2 * l) := Nat.eq_of_mul_eq_mul_left (by positivity) h1
      have h3 := lt_pow_two_mul hℓ l
      have h4 : 1 ≤ ℓ ^ 2 := Nat.one_le_iff_ne_zero.2 hq
      refine lt_min ?_ (by omega)
      rw [deg_smul, h2]
      nlinarith
    rw [sum_range_ite_congr _ hb, ← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    rw [MvPowerSeries.coeff_expand_of_not_dvd _ _ _ hi, neg_zero]
    refine sum_eq_zero fun l _ => ite_eq_right ?_
    rintro rfl
    apply hi
    rw [Finsupp.single_apply]
    split_ifs
    · rw [show 2 * (l + 1) = 2 + 2 * l by ring, pow_add]
      exact dvd_mul_right _ _
    · exact dvd_zero _

end Tw

/-! ## The Gaussian leading term modulo `ℓ` -/

section PosMod

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ℓ : ℕ} [hℓp : Fact ℓ.Prime]
  {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ}

/-- **The successor on the variables** `(s, β, α) ↦ (succ s, β, α)`. -/
abbrev sucV (succ : Equiv.Perm P) : Equiv.Perm (P × Fin b × Fin a) := Equiv.prodCongr succ (Equiv.refl _)

omit [Fintype P] [DecidableEq P] in
/-- **Powers of the successor on the variables.** -/
theorem sucV_pow_apply (succ : Equiv.Perm P) (n : ℕ) (x : P × Fin b × Fin a) :
    (sucV succ ^ n) x = ((succ ^ n) x.1, x.2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]; rfl

/-- **The basis coordinates** `y_i = Σ_x c_{ix}·X_x` of a frame. -/
def ySer (c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K) (i : P × Fin b × Fin a) :
    MvPowerSeries (P × Fin b × Fin a) K :=
  ∑ x, MvPowerSeries.C (c i x) * MvPowerSeries.X x

/-- **The basis coordinates of the twisted series** `τ_i = Σ_x c_{ix}·tw(x)`. -/
def tauS (succ : Equiv.Perm P) (c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K) (i : P × Fin b × Fin a) :
    MvPowerSeries (P × Fin b × Fin a) K :=
  ∑ x, MvPowerSeries.C (c i x) * twF K ℓ succ x

omit [IsUltrametricDist K] [CharZero K] hℓp [DecidableEq P] in
/-- **`ySer` has no constant term.** -/
theorem constantCoeff_ySer (c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K) (i : P × Fin b × Fin a) :
    MvPowerSeries.constantCoeff (ySer c i) = 0 := by
  simp [ySer]

omit [CharZero K] hℓp [DecidableEq P] in
/-- **`ySer` is integral** for integral coefficients. -/
theorem isIntK_ySer {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K} (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (i : P × Fin b × Fin a) : IsIntK (ySer c i) :=
  isIntK_finsum _ fun x _ => (isIntK_C (hc i x)).mul (isIntK_X x)

omit [Fintype P] [CharZero K] hℓp in
/-- **`twF` is integral.** -/
theorem isIntK_twF (succ : Equiv.Perm P) (x : P × Fin b × Fin a) : IsIntK (twF K ℓ succ x) := fun n => by
  change ‖∑ l ∈ range (deg n + 1), _‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
  split_ifs <;> simp

omit [CharZero K] hℓp in
/-- **`tauS` is integral** for integral coefficients. -/
theorem isIntK_tauS {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K} (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (succ : Equiv.Perm P) (i : P × Fin b × Fin a) : IsIntK (tauS (ℓ := ℓ) succ c i) :=
  isIntK_finsum _ fun x _ => (isIntK_C (hc i x)).mul (isIntK_twF succ x)

omit [IsUltrametricDist K] [CharZero K] in
/-- **`tauS` has no constant term.** -/
theorem constantCoeff_tauS (succ : Equiv.Perm P) (c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K)
    (i : P × Fin b × Fin a) : MvPowerSeries.constantCoeff (tauS (ℓ := ℓ) succ c i) = 0 := by
  rw [tauS, map_sum]
  exact sum_eq_zero fun x _ => by rw [map_mul, constantCoeff_twF K hℓp.out.ne_zero, mul_zero]

omit [IsUltrametricDist K] [CharZero K] [Fintype P] in
/-- **The Frobenius of `twF`** is its `ℓ`-expansion (coefficients `±1`). -/
theorem frobS_twF (φ : K →+* K) (succ : Equiv.Perm P) (x : P × Fin b × Fin a) :
    frobS ℓ φ (twF K ℓ succ x) = MvPowerSeries.expand ℓ hℓp.out.ne_zero (twF K ℓ succ x) := by
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ (twF K ℓ succ x)) = _
  rw [map_twF]

omit [IsUltrametricDist K] in
/-- **Frobenius equivariance of the frame**: the twisted identities for `k = 0, 1` give `φ²(c_{ix}) = c_{i,succ²x}`
(the matrix `(u_i·φ³(c_{iy}))` has the left inverse `(c_{i,succ³y′})`, hence is invertible). -/
theorem frob_sq_c {φ : K →+* K} {succ : Equiv.Perm P} {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K}
    {u : P × Fin b × Fin a → ℕ}
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : K) * c i x * (φ ^ (2 * k + 1)) (c i y) =
      if x = (sucV succ ^ (2 * k + 1)) y then 1 else 0) (i x : P × Fin b × Fin a) :
    φ (φ (c i x)) = c i ((sucV succ ^ 2) x) := by
  set M : Matrix (P × Fin b × Fin a) (P × Fin b × Fin a) K := fun i y => (u i : K) * (φ ^ 3) (c i y) with hM
  set N : Matrix (P × Fin b × Fin a) (P × Fin b × Fin a) K := fun y i => c i ((sucV succ ^ 3) y) with hN
  have hNM : N * M = 1 := by
    ext y' y
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := hTp 1 ((sucV succ ^ 3) y') y
    simp only [show 2 * 1 + 1 = 3 by rfl, Equiv.apply_eq_iff_eq] at h
    rw [← h]
    exact sum_congr rfl fun i _ => by rw [hN, hM]; ring
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  set v : P × Fin b × Fin a → K := fun i => φ (φ (c i x)) - c i ((sucV succ ^ 2) x) with hv
  have hvM : Matrix.vecMul v M = 0 := by
    ext y
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have h0 := congrArg (fun z => φ (φ z)) (hTp 0 x y)
    have h1 := hTp 1 ((sucV succ ^ 2) x) y
    have hite : ∀ p : Prop, [Decidable p] → φ (φ (if p then (1 : K) else 0)) = if p then 1 else 0 := by
      intro p _
      split_ifs <;> simp
    have e1 : ∀ z, (φ ^ (2 * 0 + 1)) z = φ z := fun z => rfl
    have e3 : ∀ z, (φ ^ (2 * 1 + 1)) z = φ (φ (φ z)) := fun z => rfl
    simp only [map_sum, map_mul, map_natCast, hite, e1] at h0
    have e4 : (sucV succ ^ (2 * 1 + 1)) y = (sucV succ ^ 2) ((sucV succ ^ (2 * 0 + 1)) y) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
    rw [e4] at h1
    simp only [e3, Equiv.apply_eq_iff_eq] at h1
    rw [← sub_eq_zero.2 (h0.trans h1.symm), ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hv, hM]
    dsimp only
    rw [show (φ ^ 3) (c i y) = φ (φ (φ (c i y))) from rfl]
    ring
  have hv0 : v = 0 := by
    rw [← Matrix.vecMul_one v, ← hMN, ← Matrix.vecMul_vecMul, hvM, Matrix.zero_vecMul]
  exact sub_eq_zero.1 (congrFun hv0 i)

end PosMod


section PosMod2

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ℓ : ℕ} [hℓp : Fact ℓ.Prime]
  {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ} {σ : Type}

omit [IsUltrametricDist K] [CharZero K] in
/-- **The Frobenius of a constant.** -/
theorem frobS_C (φ : K →+* K) (r : K) : frobS ℓ φ (MvPowerSeries.C r : MvPowerSeries σ K) = MvPowerSeries.C (φ r) := by
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ (MvPowerSeries.C r)) = _
  rw [MvPowerSeries.map_C, MvPowerSeries.expand_C]

omit [IsUltrametricDist K] [CharZero K] hℓp in
/-- **`expand` depends only on the exponent.** -/
theorem expand_congr {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (h : p = q) (F : MvPowerSeries σ K) :
    MvPowerSeries.expand p hp F = MvPowerSeries.expand q hq F := by
  subst h
  rfl

omit [IsUltrametricDist K] [CharZero K] in
/-- **Two Frobenii**: `F^{φ²}(X^{ℓ²})`. -/
theorem frobS_frobS (φ : K →+* K) (F : MvPowerSeries σ K) :
    frobS ℓ φ (frobS ℓ φ F) = MvPowerSeries.expand (ℓ ^ 2) (pow_ne_zero 2 hℓp.out.ne_zero)
      (MvPowerSeries.map φ (MvPowerSeries.map φ F)) := by
  have h0 := hℓp.out.ne_zero
  change MvPowerSeries.expand ℓ h0 (MvPowerSeries.map φ (MvPowerSeries.expand ℓ h0 (MvPowerSeries.map φ F))) = _
  rw [MvPowerSeries.map_expand, ← MvPowerSeries.expand_mul, expand_congr _ _ (sq ℓ).symm]

omit [IsUltrametricDist K] [CharZero K] in
/-- **The Frobenius raises the order** by the factor `ℓ`. -/
theorem le_order_frobS (φ : K →+* K) (F : MvPowerSeries σ K) :
    (ℓ : ℕ∞) * F.order ≤ (frobS ℓ φ F).order := by
  change _ ≤ (MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ F)).order
  rw [MvPowerSeries.order_expand, nsmul_eq_mul]
  exact mul_le_mul_right (MvPowerSeries.le_order_map φ) _

omit [IsUltrametricDist K] [CharZero K] in
/-- **Iterated Frobenius**: `(F^{m+2})(G) = F(F(F^m G))`. -/
theorem frobS_pow_add_two (φ : K →+* K) (m : ℕ) (G : MvPowerSeries σ K) :
    (frobS ℓ φ ^ (m + 2)) G = frobS ℓ φ (frobS ℓ φ ((frobS ℓ φ ^ m) G)) := by
  rw [show m + 2 = 2 + m by ring, pow_add, sq]
  rfl

omit [IsUltrametricDist K] [CharZero K] in
/-- **Iterated Frobenius**: `(F^{m+1})(G) = F(F^m G)`. -/
theorem frobS_pow_succ (φ : K →+* K) (m : ℕ) (G : MvPowerSeries σ K) :
    (frobS ℓ φ ^ (m + 1)) G = frobS ℓ φ ((frobS ℓ φ ^ m) G) := by
  rw [pow_succ']
  rfl

omit [IsUltrametricDist K] [CharZero K] in
/-- **Iterated Frobenius keeps a zero constant term.** -/
theorem constantCoeff_frobS_pow (φ : K →+* K) {G : MvPowerSeries σ K} (hG : MvPowerSeries.constantCoeff G = 0)
    (m : ℕ) : MvPowerSeries.constantCoeff ((frobS ℓ φ ^ m) G) = 0 := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [frobS_pow_succ]; exact constantCoeff_frobS_eq_zero φ ih

omit [CharZero K] in
/-- **Iterated Frobenius keeps integrality.** -/
theorem isIntK_frobS_pow {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
    {G : MvPowerSeries σ K} (hG : IsIntK G) (m : ℕ) : IsIntK ((frobS ℓ φ ^ m) G) := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [frobS_pow_succ]; exact ih.frobS hφ

omit [IsUltrametricDist K] [CharZero K] in
/-- **Iterated Frobenius raises the order**: `ℓ^m ≤ ord(F^m G)` for `G` without constant term. -/
theorem le_order_frobS_pow (φ : K →+* K) {G : MvPowerSeries σ K} (hG : MvPowerSeries.constantCoeff G = 0)
    (m : ℕ) : ((ℓ ^ m : ℕ) : ℕ∞) ≤ ((frobS ℓ φ ^ m) G).order := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.cast_one]
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 hG
  | succ m ih =>
    rw [frobS_pow_succ, pow_succ', Nat.cast_mul]
    exact (mul_le_mul_right ih _).trans (le_order_frobS φ _)

omit [IsUltrametricDist K] in
/-- **The recursion of `τ`**: `τ_i = y_i − τ_i^{φ²}(X^{ℓ²})` (from `tw(x) = X_x − tw(succ^{−2}x)(X^{ℓ²})` and the
equivariance `φ²(c_{ix}) = c_{i,succ²x}`). -/
theorem tauS_eq {φ : K →+* K} {succ : Equiv.Perm P} {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K}
    {u : P × Fin b × Fin a → ℕ}
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : K) * c i x * (φ ^ (2 * k + 1)) (c i y) =
      if x = (sucV succ ^ (2 * k + 1)) y then 1 else 0) (i : P × Fin b × Fin a) :
    tauS (ℓ := ℓ) succ c i = ySer c i - frobS ℓ φ (frobS ℓ φ (tauS (ℓ := ℓ) succ c i)) := by
  have h2 := hℓp.out.two_le
  have hq : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓp.out.ne_zero
  have hFF : ∀ x, frobS ℓ φ (frobS ℓ φ (MvPowerSeries.C (c i x) * twF K ℓ succ x)) =
      MvPowerSeries.C (c i ((sucV succ ^ 2) x)) * MvPowerSeries.expand (ℓ ^ 2) hq (twF K ℓ succ x) := by
    intro x
    rw [frobS_frobS, map_mul, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C, map_twF, map_twF,
      MvPowerSeries.expand_C, frob_sq_c hTp]
  rw [tauS, ySer, map_sum, map_sum]
  simp only [hFF]
  have e : ∀ x, MvPowerSeries.C (c i x) * twF K ℓ succ x = MvPowerSeries.C (c i x) * MvPowerSeries.X x -
      MvPowerSeries.C (c i x) * MvPowerSeries.expand (ℓ ^ 2) hq (twF K ℓ succ (((succ ^ 2).symm x.1), x.2)) :=
    fun x => by rw [twF_eq h2 succ x, mul_sub]
  simp only [e, sum_sub_distrib]
  congr 1
  rw [← Equiv.sum_comp (sucV succ ^ 2)]
  refine sum_congr rfl fun z _ => ?_
  rw [sucV_pow_apply, Equiv.symm_apply_apply]

end PosMod2


section PosMod3

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ℓ : ℕ} [hℓp : Fact ℓ.Prime]
  {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ}
  {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
  {succ : Equiv.Perm P} {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K} {u : P × Fin b × Fin a → ℕ}
  (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : K) * c i x * (φ ^ (2 * k + 1)) (c i y) =
      if x = (sucV succ ^ (2 * k + 1)) y then 1 else 0)
  (hc : ∀ i x, ‖c i x‖ ≤ 1)
include hφ hTp hc

/-- **`λ(y_i) ≡ τ_i (mod ℓ)` after any number of Frobenii** (contraction: `D_m = λ(F^m y_i) − F^m τ_i` has
`D_m + D_{m+2} ≡ λ(Y) + λ(Y)^{ℓ²} − Y ≡ 0`, `Y = F^m y_i`, by `tauS_eq`). -/
theorem isDivK_lamK_sub_tauS (i : P × Fin b × Fin a) (m : ℕ) :
    IsDivK ℓ ((lamK K ℓ).subst ((frobS ℓ φ ^ m) (ySer c i)) - (frobS ℓ φ ^ m) (tauS (ℓ := ℓ) succ c i)) := by
  set F := frobS ℓ φ with hF
  have hy := isIntK_ySer hc i
  have hy0 := constantCoeff_ySer c i
  have hYi : ∀ m, IsIntK ((F ^ m) (ySer c i)) := isIntK_frobS_pow hφ hy
  have hY0 : ∀ m, MvPowerSeries.constantCoeff ((F ^ m) (ySer c i)) = 0 := constantCoeff_frobS_pow φ hy0
  have hrec : ∀ m, (F ^ m) (tauS (ℓ := ℓ) succ c i) + (F ^ (m + 2)) (tauS (ℓ := ℓ) succ c i) =
      (F ^ m) (ySer c i) := fun m => by
    have e : (F ^ (m + 2)) (tauS (ℓ := ℓ) succ c i) = (F ^ m) (F (F (tauS (ℓ := ℓ) succ c i))) := by
      rw [pow_add, sq]
      rfl
    rw [e, ← map_add, add_eq_of_eq_sub (tauS_eq hTp i)]
  refine isDivK_of_contract (D := fun m => (lamK K ℓ).subst ((F ^ m) (ySer c i)) -
    (F ^ m) (tauS (ℓ := ℓ) succ c i)) (fun m => ?_) (fun m => ?_) m
  · have h1 := isDivK_lamK_subst_add_pow (K := K) (ℓ := ℓ) (hYi m) (hY0 m)
    have h2 := isDivK_lamK_pow_sq_sub_frob hφ (hYi m) (hY0 m)
    have e : ((lamK K ℓ).subst ((F ^ m) (ySer c i)) - (F ^ m) (tauS (ℓ := ℓ) succ c i)) +
        ((lamK K ℓ).subst ((F ^ (m + 2)) (ySer c i)) - (F ^ (m + 2)) (tauS (ℓ := ℓ) succ c i)) =
        ((lamK K ℓ).subst ((F ^ m) (ySer c i)) + ((lamK K ℓ).subst ((F ^ m) (ySer c i))) ^ (ℓ ^ 2) -
          (F ^ m) (ySer c i)) - (((lamK K ℓ).subst ((F ^ m) (ySer c i))) ^ (ℓ ^ 2) -
          (lamK K ℓ).subst (F (F ((F ^ m) (ySer c i))))) := by
      rw [frobS_pow_add_two φ m (ySer c i), ← hrec m]
      ring
    exact e ▸ h1.sub h2
  · have hτ0 := constantCoeff_tauS (K := K) (ℓ := ℓ) succ c i
    have h1 : ((ℓ ^ m : ℕ) : ℕ∞) ≤ ((lamK K ℓ).subst ((F ^ m) (ySer c i))).order :=
      (le_order_frobS_pow φ hy0 m).trans (PowerSeries.le_order_subst_right (hY0 m) (constantCoeff_lamK K ℓ))
    have h2 := le_order_frobS_pow (ℓ := ℓ) φ hτ0 m
    rw [sub_eq_add_neg]
    refine le_trans (le_min h1 ?_) MvPowerSeries.min_order_le_add
    rwa [MvPowerSeries.order_neg]

/-- **`τ_i^φ(X^ℓ) ≡ λ(y_i)^ℓ (mod ℓ)`.** -/
theorem isDivK_frobS_tauS_sub (i : P × Fin b × Fin a) :
    IsDivK ℓ (frobS ℓ φ (tauS (ℓ := ℓ) succ c i) - ((lamK K ℓ).subst (ySer c i)) ^ ℓ) := by
  have h1 := isDivK_lamK_sub_tauS hφ hTp hc i 1
  have h2 := isDivK_lamK_pow_sub_frob hφ (isIntK_ySer hc i) (constantCoeff_ySer c i)
  rw [pow_one] at h1
  have e : frobS ℓ φ (tauS (ℓ := ℓ) succ c i) - ((lamK K ℓ).subst (ySer c i)) ^ ℓ =
      -(((lamK K ℓ).subst (frobS ℓ φ (ySer c i)) - frobS ℓ φ (tauS (ℓ := ℓ) succ c i)) +
        (((lamK K ℓ).subst (ySer c i)) ^ ℓ - (lamK K ℓ).subst (frobS ℓ φ (ySer c i)))) := by ring
  rw [e]
  exact (h1.add h2).neg

omit [IsUltrametricDist K] [CharZero K] hφ hc in
/-- **The twisted dual identity in the position form**: `Σ_x tw(x)^φ(X^ℓ)·tw(succ x) = Σ_i u_i·τ_i^φ(X^ℓ)·τ_i`
(the identity `Σ_i u_i c_{ix}φ(c_{iy}) = [x = succ y]`). -/
theorem sum_frobS_twF_mul :
    ∑ y : P × Fin b × Fin a, frobS ℓ φ (twF K ℓ succ y) * twF K ℓ succ (succ y.1, y.2) =
      ∑ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) * tauS (ℓ := ℓ) succ c i := by
  have h0 : ∀ x y, ∑ i, (u i : K) * c i x * φ (c i y) = if x = (succ y.1, y.2) then 1 else 0 := fun x y =>
    hTp 0 x y
  have hi : ∀ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) * tauS (ℓ := ℓ) succ c i =
      ∑ y, ∑ x, MvPowerSeries.C ((u i : K) * c i x * φ (c i y)) *
        (frobS ℓ φ (twF K ℓ succ y) * twF K ℓ succ x) := by
    intro i
    simp only [tauS, map_sum, map_mul, frobS_C, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
    ring
  rw [sum_congr rfl fun i _ => hi i, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  simp only [← sum_mul, ← map_sum, h0]
  rw [sum_eq_single (succ y.1, y.2) (fun x _ hx => by rw [ite_eq_right hx, map_zero, zero_mul])
    (fun h => absurd (mem_univ _) h), ite_eq_left rfl, map_one, one_mul]

/-- **The Gaussian leading term is the position form mod `ℓ`** (over a field with a Frobenius lift):
`Σ_i u_i·λ(y_i)^{ℓ+1} ≡ Σ_x tw(x)^ℓ·tw(succ x)`, from `tw^ℓ ≡ tw^φ(X^ℓ)`, the twisted dual identity, and
`τ_i ≡ λ(y_i)`, `τ_i^φ(X^ℓ) ≡ λ(y_i)^ℓ`. -/
theorem isDivK_gaussLead_sub :
    IsDivK ℓ (∑ i, MvPowerSeries.C (u i : K) * ((lamK K ℓ).subst (ySer c i)) ^ (ℓ + 1) -
      ∑ x : P × Fin b × Fin a, twF K ℓ succ x ^ ℓ * twF K ℓ succ (succ x.1, x.2)) := by
  have hT : ∀ i, IsIntK (tauS (ℓ := ℓ) succ c i) := isIntK_tauS hc succ
  have hL : ∀ i, IsIntK ((lamK K ℓ).subst (ySer c i)) := fun i =>
    isIntK_lamK_subst (ℓ := ℓ) (isIntK_ySer hc i) (constantCoeff_ySer c i)
  have hu : ∀ i, IsIntK (MvPowerSeries.C (u i : K) : MvPowerSeries (P × Fin b × Fin a) K) := fun i =>
    isIntK_C (IsUltrametricDist.norm_natCast_le_one K _)
  -- the position form side
  have hpos : IsDivK ℓ (∑ x : P × Fin b × Fin a, twF K ℓ succ x ^ ℓ * twF K ℓ succ (succ x.1, x.2) -
      ∑ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) * tauS (ℓ := ℓ) succ c i) := by
    rw [← sum_frobS_twF_mul hTp, ← sum_sub_distrib]
    refine IsDivK.sum _ fun x _ => ?_
    rw [← sub_mul]
    refine IsDivK.mul_isInt ?_ (isIntK_twF _ _)
    have h := (isDivK_frobS_sub_pow_of_isIntK hφ (isIntK_twF (K := K) (ℓ := ℓ) succ x)).neg
    rwa [neg_sub] at h
  -- the Gaussian side
  have hgl : IsDivK ℓ (∑ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) *
      tauS (ℓ := ℓ) succ c i - ∑ i, MvPowerSeries.C (u i : K) * ((lamK K ℓ).subst (ySer c i)) ^ (ℓ + 1)) := by
    rw [← sum_sub_distrib]
    refine IsDivK.sum _ fun i _ => ?_
    rw [pow_succ, ← mul_assoc]
    have h0 : IsDivK ℓ ((lamK K ℓ).subst ((frobS ℓ φ ^ 0) (ySer c i)) - (frobS ℓ φ ^ 0) (tauS (ℓ := ℓ) succ c i)) :=
      isDivK_lamK_sub_tauS hφ hTp hc i 0
    change IsDivK ℓ ((lamK K ℓ).subst (ySer c i) - tauS (ℓ := ℓ) succ c i) at h0
    have h0' : IsDivK ℓ (tauS (ℓ := ℓ) succ c i - (lamK K ℓ).subst (ySer c i)) := by
      have := h0.neg; rwa [neg_sub] at this
    refine isDivK_mul_sub_mul ((hu i).mul ((hT i).frobS hφ)) (hL i)
      (by rw [← mul_sub]; exact (isDivK_frobS_tauS_sub hφ hTp hc i).isInt_mul (hu i)) h0'
  have e : ∑ i, MvPowerSeries.C (u i : K) * ((lamK K ℓ).subst (ySer c i)) ^ (ℓ + 1) -
      ∑ x : P × Fin b × Fin a, twF K ℓ succ x ^ ℓ * twF K ℓ succ (succ x.1, x.2) =
      -((∑ x : P × Fin b × Fin a, twF K ℓ succ x ^ ℓ * twF K ℓ succ (succ x.1, x.2) -
        ∑ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) * tauS (ℓ := ℓ) succ c i) +
      (∑ i, MvPowerSeries.C (u i : K) * frobS ℓ φ (tauS (ℓ := ℓ) succ c i) * tauS (ℓ := ℓ) succ c i -
        ∑ i, MvPowerSeries.C (u i : K) * ((lamK K ℓ).subst (ySer c i)) ^ (ℓ + 1))) := by ring
  rw [e]
  exact (hpos.add hgl).neg

end PosMod3

/-! ## The theta in frame coordinates -/

section Frame

open MvTay ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

/-- The theta in frame coordinates `Z`: `w = ε·ϖ·Fr·Z` (eigencoordinates `w` on `Φ × Fin b × Fin a`). -/
def thetaFrame (ι' : ℂ ≃+* ℂ_[ℓ]) (ε ϖ : ℂ_[ℓ]) (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ)
    (θ : (Φ × Fin b × Fin a → ℂ) → ℂ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] :=
  MvPowerSeries.subst (fun x => ∑ y, MvPowerSeries.C (ε * ϖ * ι' (Fr x y)) *
      (MvPowerSeries.X y : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]))
    (MvPowerSeries.map (ι' : ℂ →+* ℂ_[ℓ]) (mtay θ))

/-- The basis coordinates in the frame: `y_i(Z) = u_i⁻¹·Σ_x ι′(Σ_y conj(β_{iy})·Fr_{yx})·Z_x`. -/
def ycoef (ι' : ℂ ≃+* ℂ_[ℓ]) (β : Φ × Fin b × Fin a → (Φ × Fin b × Fin a → ℂ)) (u : Φ × Fin b × Fin a → ℕ)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ) (i x : Φ × Fin b × Fin a) : ℂ_[ℓ] :=
  (u i : ℂ_[ℓ])⁻¹ * ι' (∑ y, starRingEnd ℂ (β i y) * Fr y x)

omit [DecidableEq Φ] in
/-- **Completeness of an orthogonal basis**: `Σ_p β_{ip}·conj(β_{jp}) = u_i·δ_{ij}` gives
`Σ_i β_{ip}·conj(β_{iy})/u_i = δ_{py}` (the matrix `(β/u)` has the right inverse `βᴴ`, hence the left one). -/
theorem sum_mul_conj_div [DecidableEq Φ] {β : Φ × Fin b × Fin a → (Φ × Fin b × Fin a → ℂ)}
    {u : Φ × Fin b × Fin a → ℕ} (hu : ∀ i, u i ≠ 0)
    (hβ : ∀ i j, ∑ p, β i p * starRingEnd ℂ (β j p) = if i = j then (u i : ℂ) else 0)
    (p y : Φ × Fin b × Fin a) : ∑ i, β i p * starRingEnd ℂ (β i y) / u i = if p = y then 1 else 0 := by
  set B : Matrix (Φ × Fin b × Fin a) (Φ × Fin b × Fin a) ℂ := Matrix.of fun i p => β i p with hB
  set D : Matrix (Φ × Fin b × Fin a) (Φ × Fin b × Fin a) ℂ := Matrix.of fun i p => (u i : ℂ)⁻¹ * β i p with hD
  have h1 : D * B.conjTranspose = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hD, hB, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, mul_assoc, ← mul_sum, hβ]
    split_ifs with h
    · subst h
      exact inv_mul_cancel₀ ((Nat.cast_ne_zero (R := ℂ)).2 (hu i))
    · exact mul_zero _
  have h2 : B.conjTranspose * D = 1 := mul_eq_one_comm.1 h1
  have h3 := congrFun (congrFun h2 y) p
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  simp only [hD, hB, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def] at h3
  rw [show (if p = y then (1 : ℂ) else 0) = if y = p then 1 else 0 by simp [eq_comm], ← h3]
  exact sum_congr rfl fun i _ => by field_simp

/-- **The basis expansion of the frame**: `Σ_i ι′(β_{ip})·ycoef_{ix} = ι′(Fr_{px})`. -/
theorem sum_beta_ycoef (ι' : ℂ ≃+* ℂ_[ℓ]) {β : Φ × Fin b × Fin a → (Φ × Fin b × Fin a → ℂ)}
    {u : Φ × Fin b × Fin a → ℕ} (hu : ∀ i, u i ≠ 0)
    (hβ : ∀ i j, ∑ p, β i p * starRingEnd ℂ (β j p) = if i = j then (u i : ℂ) else 0)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ) (p x : Φ × Fin b × Fin a) :
    ∑ i, ι' (β i p) * ycoef ι' β u Fr i x = ι' (Fr p x) := by
  have e : ∀ i, ι' (β i p) * ycoef ι' β u Fr i x =
      ι' (∑ y, β i p * starRingEnd ℂ (β i y) / u i * Fr y x) := fun i => by
    rw [ycoef, ← map_natCast ι', ← map_inv₀, ← map_mul, ← map_mul, mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun y _ => by field_simp
  simp only [e, ← map_sum]
  rw [sum_comm]
  simp only [← sum_mul, sum_mul_conj_div hu hβ, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- **The theta in frame coordinates is the Lubin–Tate theta at `X_i = e(ϖ·y_i(Z)) = ϖ·λ(y_i(Z))`**
(`L(e(t)) = t` and the basis expansion of the frame). -/
theorem thetaFrame_eq_subst (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ)
    {β : Φ × Fin b × Fin a → (Φ × Fin b × Fin a → ℂ)} {u : Φ × Fin b × Fin a → ℕ} (hu : ∀ i, u i ≠ 0)
    (hβ : ∀ i j, ∑ p, β i p * starRingEnd ℂ (β j p) = if i = j then (u i : ℂ) else 0)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ) (θ : (Φ × Fin b × Fin a → ℂ) → ℂ) :
    thetaFrame ι' ε ϖ Fr θ = MvPowerSeries.subst (fun i => MvPowerSeries.C ϖ *
      (lamK ℂ_[ℓ] ℓ).subst (ySer (ycoef ι' β u Fr) i)) (thetaLT ι' ε β θ) := by
  have hℓ1 := hℓ.out.one_lt
  set Xe : Φ × Fin b × Fin a → MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] := fun i => MvPowerSeries.C ϖ *
    (lamK ℂ_[ℓ] ℓ).subst (ySer (ycoef ι' β u Fr) i) with hXe
  have hXe0 : ∀ i, MvPowerSeries.constantCoeff (Xe i) = 0 := fun i => by
    rw [hXe, map_mul, constantCoeff_lamK_subst (constantCoeff_ySer _ i), mul_zero]
  have hXs : MvPowerSeries.HasSubst Xe := MvPowerSeries.hasSubst_of_constantCoeff_zero hXe0
  have hL0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i :
      MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) (logLT ℂ_[ℓ] ℓ)) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ (constantCoeff_logLT _ hℓ1)
  have hAs : MvPowerSeries.HasSubst (fun p => ∑ i, MvPowerSeries.C (ε * ι' (β i p)) *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) (logLT ℂ_[ℓ] ℓ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      rw [map_sum]
      exact sum_eq_zero fun i _ => by rw [map_mul, hL0, mul_zero]
  -- `L(X_i) = ϖ·y_i`
  have hLX : ∀ i, MvPowerSeries.subst Xe (PowerSeries.subst (MvPowerSeries.X i :
      MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) (logLT ℂ_[ℓ] ℓ)) =
      MvPowerSeries.C ϖ * ySer (ycoef ι' β u Fr) i := fun i => by
    have hy0 := constantCoeff_ySer (ycoef ι' β u Fr) i
    have hCy : MvPowerSeries.constantCoeff (MvPowerSeries.C ϖ * ySer (ycoef ι' β u Fr) i) = 0 := by
      rw [map_mul, hy0, mul_zero]
    rw [subst_subst _ (MvPowerSeries.constantCoeff_X i) hXs, MvPowerSeries.subst_X hXs, hXe]
    dsimp only
    rw [← expLT_subst_C_mul hℓ1 hϖ hy0, ← PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_expLT _ _))
      (PowerSeries.HasSubst.of_constantCoeff_zero hCy), logLT_subst_expLT _ hℓ1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hCy)]
  rw [thetaLT, MvPowerSeries.subst_comp_subst_apply hAs hXs, thetaFrame]
  congr 1
  funext p
  symm
  rw [← MvPowerSeries.coe_substAlgHom hXs, map_sum]
  simp only [MvPowerSeries.coe_substAlgHom hXs, MvPowerSeries.subst_mul hXs, MvPowerSeries.subst_C, hLX, ySer,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  have e : ∀ i, MvPowerSeries.C (ε * ι' (β i p)) * (MvPowerSeries.C ϖ * (MvPowerSeries.C (ycoef ι' β u Fr i x) *
      MvPowerSeries.X x)) = MvPowerSeries.C (ε * ϖ * (ι' (β i p) * ycoef ι' β u Fr i x)) *
        (MvPowerSeries.X x : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) := fun i => by
    simp only [map_mul]
    ring
  simp only [e, ← sum_mul, ← map_sum, ← mul_sum, sum_beta_ycoef ι' hu hβ Fr p x]

end Frame

/-! ## The explicit Gaussian at `X = ϖ·λ(y)`: the leading term and the small remainder -/

section SerAB

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {σ : Type}

/-- **Ultrametric finite sums**: a `finsum` of terms of norm `≤ r` has norm `≤ r`. -/
theorem norm_finsum_le {K α : Type} [NormedField K] [IsUltrametricDist K] {g : α → K} {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ d, ‖g d‖ ≤ r) : ‖∑ᶠ d, g d‖ ≤ r := by
  classical
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum _ h]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun d _ => hg d
  · rw [finsum_of_infinite_support h, norm_zero]
    exact hr

/-- **Substituting `(A, A)`** into a two-variable series: if `‖[Aᵏ]‖ ≤ sᵏ` and `‖f_n‖·s^{|n|} ≤ r`, the
coefficients of `f(A, A)` have norm `≤ r`. -/
theorem norm_coeff_subst_pair_le {f : MvPowerSeries (Fin 2) ℂ_[ℓ]} {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : MvPowerSeries.constantCoeff A = 0) {s r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ k κ, ‖MvPowerSeries.coeff κ (A ^ k)‖ ≤ s ^ k)
    (hf : ∀ n : Fin 2 →₀ ℕ, ‖MvPowerSeries.coeff n f‖ * s ^ (n 0 + n 1) ≤ r) (κ : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff κ (MvPowerSeries.subst ![A, A] f)‖ ≤ r := by
  rw [MvPowerSeries.coeff_subst (hasSubst_pair hA0 hA0)]
  refine norm_finsum_le hr fun d => ?_
  have e : (d.prod fun s e => (![A, A] s) ^ e) = A ^ (d 0 + d 1) := by
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, pow_add]
    rfl
  rw [e, smul_eq_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hA _ κ) (norm_nonneg _)).trans (hf d)

/-- **The leading term of `serAB`**: `(XY^ℓ + X^ℓY)/ℓ`, the support pair `(i, j) = (0, 0)`. -/
def serAB0 (ℓ : ℕ) [Fact ℓ.Prime] : MvPowerSeries (Fin 2) ℂ_[ℓ] :=
  MvPowerSeries.C ((ℓ : ℂ_[ℓ])⁻¹) * (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ ℓ +
    MvPowerSeries.X 0 ^ ℓ * MvPowerSeries.X 1)

/-- **The leading term on the diagonal**: `serAB0(A, A) = (2/ℓ)·A^{ℓ+1}`. -/
theorem subst_pair_serAB0 {A : MvPowerSeries σ ℂ_[ℓ]} (hA0 : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.subst ![A, A] (serAB0 ℓ) = MvPowerSeries.C (2 / (ℓ : ℂ_[ℓ])) * A ^ (ℓ + 1) := by
  have hs := hasSubst_pair hA0 hA0
  rw [serAB0, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_pow hs,
    MvPowerSeries.subst_pow hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [div_eq_mul_inv, map_mul, map_ofNat]
  ring

omit hℓ in
/-- **Monomials in two variables**: `[X^n](X₀^p X₁^q) = [n = (p, q)]`. -/
theorem coeff_X_pow_mul_X_pow {K : Type} [CommRing K] (p q : ℕ) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.X 0 ^ p * MvPowerSeries.X 1 ^ q : MvPowerSeries (Fin 2) K) =
      if n 0 = p ∧ n 1 = q then 1 else 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
    MvPowerSeries.coeff_monomial]
  congr 1
  apply propext
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

open Classical in
/-- **The coefficients of the leading term**: `ℓ⁻¹` on the support pair `(0, 0)` of `serAB`, `0` elsewhere. -/
theorem coeff_serAB0 (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (serAB0 ℓ) = if SupAB ℓ (n 0) (n 1) 0 0 then (ℓ : ℂ_[ℓ])⁻¹ else 0 := by
  have h1 : ℓ ≠ 1 := hℓ.out.one_lt.ne'
  have e1 : (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ ℓ : MvPowerSeries (Fin 2) ℂ_[ℓ]) =
      MvPowerSeries.X 0 ^ 1 * MvPowerSeries.X 1 ^ ℓ := by rw [pow_one]
  have e2 : (MvPowerSeries.X 0 ^ ℓ * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) =
      MvPowerSeries.X 0 ^ ℓ * MvPowerSeries.X 1 ^ 1 := by rw [pow_one]
  rw [serAB0, MvPowerSeries.coeff_C_mul, map_add, e1, e2, coeff_X_pow_mul_X_pow, coeff_X_pow_mul_X_pow]
  simp only [SupAB, le_refl, true_and, mul_zero, zero_add, pow_zero, pow_one]
  by_cases ha : n 0 = 1 ∧ n 1 = ℓ
  · have hb : ¬ (n 0 = ℓ ∧ n 1 = 1) := fun hb => h1 (ha.1 ▸ hb.1).symm
    rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (Or.inl ha), add_zero, mul_one]
  · by_cases hb : n 0 = ℓ ∧ n 1 = 1
    · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_left (Or.inr ⟨hb.2, hb.1⟩), zero_add, mul_one]
    · rw [ite_eq_right ha, ite_eq_right hb,
        ite_eq_right (by rintro (h | ⟨h, h'⟩) <;> [exact ha h; exact hb ⟨h', h⟩]), add_zero,
        mul_zero]

omit hℓ in
/-- **The exponents of the small terms**: `ℓ + (ℓ² − 1)(2j + 1) ≤ ℓ^{2j+1}` for `j ≥ 1`, `ℓ ≥ 3`. -/
theorem exp_small_le {ℓ : ℕ} (h3 : 3 ≤ ℓ) {j : ℕ} (hj : 1 ≤ j) : ℓ + (ℓ ^ 2 - 1) * (2 * j + 1) ≤ ℓ ^ (2 * j + 1) := by
  induction j, hj using Nat.le_induction with
  | base =>
    have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ (by omega)
    show ℓ + (ℓ ^ 2 - 1) * 3 ≤ ℓ ^ 3
    zify [this]
    have h3' : (3 : ℤ) ≤ ℓ := by exact_mod_cast h3
    have h4 : (0 : ℤ) ≤ (ℓ : ℤ) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 h3') h4]
  | succ j hj ih =>
    have h1 : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : ℓ ^ (2 * (j + 1) + 1) = ℓ ^ 2 * ℓ ^ (2 * j + 1) := by ring
    have h4 : 27 ≤ ℓ ^ (2 * j + 1) := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ ℓ ^ 3 := Nat.pow_le_pow_left h3 3
        _ ≤ ℓ ^ (2 * j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [h2]
    zify [h1] at ih ⊢
    nlinarith

open Classical in
/-- **The remainder of `serAB` is small** at `X = ϖ·(integral)`: its support pairs `(i, j) ≠ (0, 0)` have
`‖ℓ^{−(i+j+1)}‖·‖ϖ‖^{ℓ^{2i}+ℓ^{2j+1}} ≤ ‖ϖ‖^{ℓ+1}`. -/
theorem norm_coeff_serAB_sub_le (h3 : 3 ≤ ℓ) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (n : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff n (serAB ℓ - serAB0 ℓ)‖ * ‖ϖ‖ ^ (n 0 + n 1) ≤ ‖ϖ‖ ^ (ℓ + 1) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hϖp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hℓn : ‖(ℓ : ℂ_[ℓ])‖ = ‖ϖ‖ ^ (ℓ ^ 2 - 1) := by rw [← norm_pow, hϖ]
  rw [map_sub, coeff_serAB0]
  by_cases h : ∃ i j, SupAB ℓ (n 0) (n 1) i j
  · obtain ⟨i, j, hij⟩ := h
    rw [coeff_serAB_of hij]
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [ite_eq_left hij, zero_add, zero_add, pow_one, sub_self, norm_zero, zero_mul]
      positivity
    · have hn0 : ¬ SupAB ℓ (n 0) (n 1) 0 0 := fun h' => h00 (supAB_unique hij h')
      rw [ite_eq_right hn0, sub_zero]
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd ⟨Nat.le_zero.1 hij.1, rfl⟩ h00
        · exact hj
      have hM : n 0 + n 1 = ℓ ^ (2 * i) + ℓ ^ (2 * j + 1) := by
        rcases hij.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hle : ℓ + 1 + (ℓ ^ 2 - 1) * (i + j + 1) ≤ n 0 + n 1 := by
        have := exp_small_le h3 hj
        have h1 : 1 ≤ ℓ ^ (2 * i) := Nat.one_le_pow _ _ (by omega)
        have h2 : (ℓ ^ 2 - 1) * (i + j + 1) ≤ (ℓ ^ 2 - 1) * (2 * j + 1) :=
          Nat.mul_le_mul_left _ (by have := hij.1; omega)
        omega
      rw [norm_inv, norm_pow, hℓn, ← pow_mul, inv_mul_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_of_le_one hϖp.le hϖ1 (by omega)
  · push Not at h
    rw [coeff_serAB_of_not h, ite_eq_right (h 0 0), sub_zero, norm_zero, zero_mul]
    positivity

end SerAB

/-! ## The Gaussian frame form: factorisation and integrality -/

section ThetaInt

open MvTay ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

/-- **The points** `X_i = e(ϖ·y_i) = ϖ·λ(y_i)` in frame coordinates. -/
def xPt (ϖ : ℂ_[ℓ]) (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) (i : Φ × Fin b × Fin a) :
    MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] :=
  MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer c i)

omit [DecidableEq Φ] in
/-- **The points have no constant term.** -/
theorem constantCoeff_xPt (ϖ : ℂ_[ℓ]) (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ])
    (i : Φ × Fin b × Fin a) : MvPowerSeries.constantCoeff (xPt ϖ c i) = 0 := by
  rw [xPt, map_mul, constantCoeff_lamK_subst (constantCoeff_ySer c i), mul_zero]

omit [DecidableEq Φ] in
/-- **The points can be substituted.** -/
theorem hasSubst_xPt (ϖ : ℂ_[ℓ]) (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) :
    MvPowerSeries.HasSubst (xPt ϖ c) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_xPt ϖ c)

omit [DecidableEq Φ] in
/-- **Powers of the points**: `‖[Xᵏ]‖ ≤ ‖ϖ‖ᵏ` for integral frame coefficients. -/
theorem norm_coeff_xPt_pow_le {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (ϖ : ℂ_[ℓ]) (i : Φ × Fin b × Fin a) (k : ℕ) (κ : Φ × Fin b × Fin a →₀ ℕ) :
    ‖MvPowerSeries.coeff κ (xPt ϖ c i ^ k)‖ ≤ ‖ϖ‖ ^ k := by
  rw [xPt, mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity)
    ((isIntK_lamK_subst (ℓ := ℓ) (isIntK_ySer hc i) (constantCoeff_ySer c i)).pow k κ)

omit [DecidableEq Φ] in
/-- **The points are integral.** -/
theorem isIntK_xPt {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)
    {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (i : Φ × Fin b × Fin a) : IsIntK (xPt ϖ c i) := fun κ => by
  have h := norm_coeff_xPt_pow_le hc ϖ i 1 κ
  rw [pow_one, pow_one] at h
  exact h.trans (norm_le_one_of_pow_eq hℓ.out.one_lt hϖ)

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A constant position weight factors out.** -/
theorem posForm_const [Fintype Φ] [DecidableEq Φ] (succ : Equiv.Perm Φ) (γ : ℂ_[ℓ]) :
    posForm (a := a) (b := b) succ (fun _ => γ) = MvPowerSeries.C γ * posForm succ (fun _ => (1 : ℂ_[ℓ])) := by
  simp only [posForm, mul_sum, map_one, one_mul, mul_assoc]

/-- **The Gaussian exponent remainder** `G = Ψ(X) − (ϖ^{ℓ+1}/ℓ)·γ·posForm`, `Ψ = gaussPsi`. -/
def gRem (ϖ γ : ℂ_[ℓ]) (succ : Equiv.Perm Φ) (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ])
    (u : Φ × Fin b × Fin a → ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] :=
  MvPowerSeries.subst (xPt ϖ c) (gaussPsi γ u) -
    MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ * γ) * posForm succ (fun _ => (1 : ℂ_[ℓ]))

omit [DecidableEq Φ] in
/-- **The remainder has no constant term.** -/
theorem constantCoeff_gRem (ϖ γ : ℂ_[ℓ]) (succ : Equiv.Perm Φ) (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ])
    (u : Φ × Fin b × Fin a → ℕ) [DecidableEq Φ] :
    MvPowerSeries.constantCoeff (gRem (ℓ := ℓ) (a := a) (b := b) ϖ γ succ c u) = 0 := by
  rw [gRem, map_sub, map_mul, constantCoeff_posForm, mul_zero, sub_zero,
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_xPt ϖ c) (constantCoeff_xPt ϖ c)
      (constantCoeff_gaussPsi γ u)]

/-- **The Gaussian frame form, algebraically**: if `thetaLT = c₀·exp(−Ψ)·U`, then in frame coordinates
`thetaFrame = c₀·posGauss(γ)·(exp(−G)·U(X))` with `X_i = ϖ·λ(y_i)` (`thetaFrame_eq_subst`). -/
theorem thetaFrame_factor (ι' : ℂ ≃+* ℂ_[ℓ]) (ε : ℂ_[ℓ]) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ)
    {β : Φ × Fin b × Fin a → (Φ × Fin b × Fin a → ℂ)} {u : Φ × Fin b × Fin a → ℕ} (hu : ∀ i, u i ≠ 0)
    (hβ : ∀ i j, ∑ p, β i p * starRingEnd ℂ (β j p) = if i = j then (u i : ℂ) else 0)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ) (θ : (Φ × Fin b × Fin a → ℂ) → ℂ) (succ : Equiv.Perm Φ)
    {γ c₀ : ℂ_[ℓ]} {U : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}
    (hθ : thetaLT ι' ε β θ = MvPowerSeries.C c₀ * (expMv (-gaussPsi γ u) * U)) :
    thetaFrame ι' ε ϖ Fr θ = MvPowerSeries.C c₀ * (posGauss ϖ succ (fun _ => γ) *
      (expMv (-gRem ϖ γ succ (ycoef ι' β u Fr) u) * MvPowerSeries.subst (xPt ϖ (ycoef ι' β u Fr)) U)) := by
  set X := xPt ϖ (ycoef ι' β u Fr) with hX
  have hXs : MvPowerSeries.HasSubst X := hasSubst_xPt ϖ _
  have hX0 := constantCoeff_xPt (ℓ := ℓ) ϖ (ycoef ι' β u Fr)
  have hΨ0 := constantCoeff_gaussPsi γ u
  have hΨX0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst X (gaussPsi γ u)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hXs hX0 hΨ0
  have hP0 := constantCoeff_posForm (ℓ := ℓ) (a := a) (b := b) succ (fun _ => (1 : ℂ_[ℓ]))
  rw [thetaFrame_eq_subst ι' ε hϖ hu hβ Fr θ, hθ]
  change MvPowerSeries.subst X (MvPowerSeries.C c₀ * (expMv (-gaussPsi γ u) * U)) = _
  rw [MvPowerSeries.subst_mul hXs, MvPowerSeries.subst_C,
    MvPowerSeries.subst_mul hXs, expMv_subst (by rw [map_neg, hΨ0, neg_zero]) hXs hX0]
  have hneg : MvPowerSeries.subst X (-gaussPsi γ u) = -MvPowerSeries.subst X (gaussPsi γ u) := by
    rw [← MvPowerSeries.coe_substAlgHom hXs, map_neg]
  rw [hneg]
  congr 1
  rw [← mul_assoc]
  congr 1
  rw [posGauss, posForm_const, ← expMv_add]
  · congr 1
    rw [gRem, ← mul_assoc, ← map_mul]
    ring
  · rw [map_neg, map_mul, map_mul, hP0, mul_zero, mul_zero, neg_zero]
  · rw [map_neg, constantCoeff_gRem, neg_zero]

end ThetaInt


section ThetaInt2

open MvTay ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

/-- **`ℓ`-divisibility passes from `K^ur` to `ℂ_ℓ`.** -/
theorem isDivK_map_unramC {σ : Type} {f : MvPowerSeries σ (unramC ℓ)} (hf : IsDivK ℓ f) :
    IsDivK ℓ (MvPowerSeries.map (unramC ℓ).subtype f) := fun n => by
  rw [MvPowerSeries.coeff_map]
  have e : ‖((ℓ : unramC ℓ) : ℂ_[ℓ])‖ = ‖(ℓ : ℂ_[ℓ])‖ := by norm_cast
  exact (hf n).trans_eq e

omit [DecidableEq Φ] in
/-- **Frame coordinates are carried by ring maps.** -/
theorem map_ySer {K L : Type} [NormedField K] [NormedField L] (f : K →+* L)
    (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → K)
    (i : Φ × Fin b × Fin a) : MvPowerSeries.map f (ySer c i) = ySer (fun i x => f (c i x)) i := by
  simp only [ySer, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]

/-- **The Gaussian leading term is the position form mod `ℓ`** in frame coordinates over `ℂ_ℓ`, for a frame with
coefficients in `K^ur` satisfying the odd twisted dual identities for `frobUnram`
(`isDivK_gaussLead_sub` over `K^ur`). -/
theorem isDivK_gaussLead_sub_posForm {succ : Equiv.Perm Φ} {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ}
    {u : Φ × Fin b × Fin a → ℕ}
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
    (hc : ∀ i x, ‖c i x‖ ≤ 1) :
    IsDivK ℓ (∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) *
      ((lamK ℂ_[ℓ] ℓ).subst (ySer (fun i x => (c i x : ℂ_[ℓ])) i)) ^ (ℓ + 1) -
        posForm (ℓ := ℓ) succ (fun _ => (1 : ℂ_[ℓ]))) := by
  have h := isDivK_map_unramC (isDivK_gaussLead_sub (K := unramC ℓ) (ℓ := ℓ)
    UnramFrobLift.norm_frobUnram_sub_pow_le hTp hc)
  convert h using 1
  rw [map_sub, map_sum, map_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, MvPowerSeries.map_C, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_ySer c i)), map_lamK, map_ySer, map_natCast]
    rfl
  · rw [posForm]
    refine sum_congr rfl fun x _ => ?_
    rw [map_mul, map_pow, map_twF, map_twF, map_one, one_mul]
    rfl

/-- **`‖2‖ = 1`** in `ℂ_ℓ` for odd `ℓ`. -/
theorem norm_two_padicC (h3 : 3 ≤ ℓ) : ‖(2 : ℂ_[ℓ])‖ = 1 := by
  have h := norm_natCast_padicC (ℓ := ℓ) 2 two_ne_zero
  rw [padicValNat.eq_zero_of_not_dvd (fun h2 => by
    have := Nat.le_of_dvd two_pos h2; omega), Nat.cast_zero, neg_zero, zpow_zero] at h
  exact_mod_cast h

/-- **The Gaussian exponent remainder is small** (D1b plan §3.9, the integral part): every coefficient of
`G = Ψ(X) − (ϖ^{ℓ+1}/ℓ)·γ·posForm` has norm `≤ ‖ϖ‖^{ℓ+1}`. `Ψ(X) = Σ_i u_i(γ/2)·serAB(X_i, X_i)` splits into
`(ϖ^{ℓ+1}/ℓ)·γ·Σ_i u_i·λ(y_i)^{ℓ+1}` and the small terms of `serAB` (`norm_coeff_serAB_sub_le`), and the first is
`(ϖ^{ℓ+1}/ℓ)·γ·(posForm + ℓ·W)` (`isDivK_gaussLead_sub_posForm`). -/
theorem norm_coeff_gRem_le (h5 : 5 ≤ ℓ) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) {γ : ℂ_[ℓ]} (hγ : ‖γ‖ ≤ 1)
    {succ : Equiv.Perm Φ} {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ} {u : Φ × Fin b × Fin a → ℕ}
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
    (hc : ∀ i x, ‖c i x‖ ≤ 1) (κ : Φ × Fin b × Fin a →₀ ℕ) :
    ‖MvPowerSeries.coeff κ (gRem ϖ γ succ (fun i x => (c i x : ℂ_[ℓ])) u)‖ ≤ ‖ϖ‖ ^ (ℓ + 1) := by
  have h3 : 3 ≤ ℓ := by omega
  set cc : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ] := fun i x => (c i x : ℂ_[ℓ]) with hccdef
  have hcc : ∀ i x, ‖cc i x‖ ≤ 1 := hc
  set X := xPt ϖ cc with hX
  have hXs : MvPowerSeries.HasSubst X := hasSubst_xPt ϖ cc
  have hX0 : ∀ i, MvPowerSeries.constantCoeff (X i) = 0 := constantCoeff_xPt ϖ cc
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  have h20 : (2 : ℂ_[ℓ]) ≠ 0 := two_ne_zero
  obtain ⟨W, hW, hWe⟩ := (isDivK_gaussLead_sub_posForm hTp hc).eq_C_mul
  have hS : ∀ i, MvPowerSeries.subst ![X i, X i] (serAB ℓ) =
      MvPowerSeries.subst ![X i, X i] (serAB ℓ - serAB0 ℓ) +
        MvPowerSeries.C (ϖ ^ (ℓ + 1) * (2 / ℓ)) * ((lamK ℂ_[ℓ] ℓ).subst (ySer cc i)) ^ (ℓ + 1) := by
    intro i
    have hs := hasSubst_pair (hX0 i) (hX0 i)
    have hXp : X i ^ (ℓ + 1) = MvPowerSeries.C (ϖ ^ (ℓ + 1)) * ((lamK ℂ_[ℓ] ℓ).subst (ySer cc i)) ^ (ℓ + 1) := by
      rw [hX, xPt, mul_pow, ← map_pow]
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, MvPowerSeries.coe_substAlgHom hs,
      subst_pair_serAB0 (hX0 i), hXp, map_mul]
    ring
  have hΨ : MvPowerSeries.subst X (gaussPsi γ u) =
      ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.subst ![X i, X i] (serAB ℓ) := by
    rw [gaussPsi, ← MvPowerSeries.coe_substAlgHom hXs, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hXs, MvPowerSeries.subst_mul hXs, MvPowerSeries.subst_C,
      subst_pair_X _ _ hXs]
  have hdec : gRem ϖ γ succ cc u = (∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) *
      MvPowerSeries.subst ![X i, X i] (serAB ℓ - serAB0 ℓ)) + MvPowerSeries.C (ϖ ^ (ℓ + 1) * γ) * W := by
    rw [gRem, hΨ]
    simp only [hS, mul_add, sum_add_distrib]
    have h2 : ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * (MvPowerSeries.C (ϖ ^ (ℓ + 1) * (2 / ℓ)) *
        ((lamK ℂ_[ℓ] ℓ).subst (ySer cc i)) ^ (ℓ + 1)) = MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ * γ) *
          ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * ((lamK ℂ_[ℓ] ℓ).subst (ySer cc i)) ^ (ℓ + 1) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [← mul_assoc, ← map_mul]
      congr 2
      field_simp
    rw [h2, add_sub_assoc, ← mul_sub, hWe, ← mul_assoc, ← map_mul]
    congr 3
    field_simp
  rw [hdec, map_add, map_sum]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
    rw [MvPowerSeries.coeff_C_mul, norm_mul]
    have hu1 : ‖(u i : ℂ_[ℓ]) * (γ / 2)‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_two_padicC h3, div_one]
      exact mul_le_one_of (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _) hγ
    exact (mul_le_mul hu1 (norm_coeff_subst_pair_le (hX0 i) (by positivity) (norm_coeff_xPt_pow_le hcc ϖ i)
      (norm_coeff_serAB_sub_le h3 hϖ) κ) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_mul, norm_pow]
    calc ‖ϖ‖ ^ (ℓ + 1) * ‖γ‖ * ‖MvPowerSeries.coeff κ W‖ ≤ ‖ϖ‖ ^ (ℓ + 1) * 1 * 1 := by
          gcongr
          exact hW κ
      _ = ‖ϖ‖ ^ (ℓ + 1) := by ring

end ThetaInt2


section ThetaInt3

open ThetaChain ThetaNorm ThetaHeis ThetaCompare ChainCanon HermGS MvTay ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

omit hℓ in
/-- **The basis of a `GSBasis` in eigencoordinates is orthogonal** with diagonal `u`: `β_i = δ⁻¹b_i` has
`Σ_p β_{ip}·conj(β_{jp}) = u_i·δ_{ij}` (`sd·H(b_i, b_j) = u_i·δ_{ij}` and `s·|δ|²·sd = 1`). -/
theorem gsBasis_orth {d : ℕ} {sd : ℝ} (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0)
    {C : AddSubgroup (Φ × Fin b × Fin a → ℂ)} (B : GSBasis ℓ (sC sd) sd (omegaD sd) C) (i j : Φ × Fin b × Fin a) :
    ∑ p, ((deltaC sd)⁻¹ • B.b i) p * starRingEnd ℂ (((deltaC sd)⁻¹ • B.b j) p) =
      if i = j then (B.u i : ℂ) else 0 := by
  have hsd0 := sd_pos8 hd8 hsd
  have hδ : deltaC sd ≠ 0 := deltaC_ne_zero hΔ
  have hn := sC_mul_normSq hsd0 hΔ
  have hnC : (sC sd : ℂ) * ((Complex.normSq (deltaC sd) : ℝ) : ℂ) * (sd : ℂ) = 1 := by exact_mod_cast hn
  have h := B.orth i j
  rw [Hf] at h
  have e : ∑ p, ((deltaC sd)⁻¹ • B.b i) p * starRingEnd ℂ (((deltaC sd)⁻¹ • B.b j) p) =
      ((sC sd : ℂ) * ((Complex.normSq (deltaC sd) : ℝ) : ℂ) * (sd : ℂ))⁻¹ * ((sd : ℂ) * ((sC sd : ℂ) *
        ∑ p, B.b i p * starRingEnd ℂ (B.b j p))) := by
    simp only [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [Complex.normSq_eq_conj_mul_self]
    have hc : starRingEnd ℂ (deltaC sd) ≠ 0 := (map_ne_zero _).2 hδ
    have hs0 : (sC sd : ℂ) ≠ 0 := by exact_mod_cast (sC_pos sd).ne'
    have hsd0' : (sd : ℂ) ≠ 0 := by exact_mod_cast hsd0.ne'
    field_simp
  rw [e, hnC, inv_one, one_mul, h]

/-- **D1b-8, the integral part**: in a frame with integral basis coordinates and the odd twisted dual-basis
identities, the theta is `c₀·posGauss(γ)·(exp(−G)·U(X))` with `exp(−G)·U(X)` integral (`G = gRem` small,
`U(X)` integral). -/
theorem theta_frame_int (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram)
    {d : ℕ} {sd : ℝ} (hd : Squarefree d) (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι' : ℂ ≃+* ℂ_[ℓ]) {C : AddSubgroup (Φ × Fin b × Fin a → ℂ)} (hCt : IsThetaLat (sC sd) sd C)
    (hCd : IsEDual (sC sd) C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {θ : (Φ × Fin b × Fin a → ℂ) → ℂ}
    (hθ : θ ∈ Th (sC sd) sd C) (B : GSBasis ℓ (sC sd) sd (omegaD sd) C)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ) (succ : Equiv.Perm Φ)
    (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ)
    (hc : ∀ i x, (c i x : ℂ_[ℓ]) = ycoef ι' (fun i => (deltaC sd)⁻¹ • B.b i) B.u Fr i x)
    (hint : ∀ i x, ‖c i x‖ ≤ 1)
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (B.u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
    {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ γ : unramC ℓ, UnramFrobLift.frobUnram ℓ γ = -γ ∧ ‖(γ : ℂ_[ℓ])‖ ≤ 1 ∧
      ∃ (c₀ : ℂ_[ℓ]) (U : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]), IsIntK U ∧
        (∀ κ, ‖MvPowerSeries.coeff κ (gRem ϖ (γ : ℂ_[ℓ]) succ (fun i x => (c i x : ℂ_[ℓ])) B.u)‖ ≤
          ‖ϖ‖ ^ (ℓ + 1)) ∧
        thetaFrame ι' ε ϖ Fr θ = MvPowerSeries.C c₀ * (posGauss ϖ succ (fun _ => (γ : ℂ_[ℓ])) *
          (expMv (-gRem ϖ (γ : ℂ_[ℓ]) succ (fun i x => (c i x : ℂ_[ℓ])) B.u) *
            MvPowerSeries.subst (xPt ϖ (fun i x => (c i x : ℂ_[ℓ]))) U)) := by
  obtain ⟨ε, hεu, hε, γ, hγφ, hγ1, c₀, U, hU, hθLT⟩ :=
    theta_gauss' hb hj hu hs hd hd8 hsd hΔ h5 hdℓ hin ι' hCt hCd hω hθ B
  have hcc : (fun i x => (c i x : ℂ_[ℓ])) = ycoef ι' (fun i => (deltaC sd)⁻¹ • B.b i) B.u Fr := by
    funext i x
    exact hc i x
  refine ⟨ε, hεu, hε, γ, hγφ, hγ1, c₀, U, hU, norm_coeff_gRem_le h5 hϖ hγ1 hTp hint, ?_⟩
  rw [hcc]
  exact thetaFrame_factor ι' ε hϖ (fun i => (B.u_pos i).ne') (gsBasis_orth hd8 hsd hΔ B) Fr θ succ hθLT

omit [DecidableEq Φ] in
/-- **The remainder of the Gaussian frame form is integral**: `exp(−G)` (small exponent) times `U(X)`. -/
theorem isIntK_rem {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) {G U : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}
    (hG : ∀ κ, ‖MvPowerSeries.coeff κ G‖ ≤ ‖ϖ‖ ^ (ℓ + 1)) (hU : IsIntK U)
    {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1) :
    IsIntK (expMv (-G) * MvPowerSeries.subst (xPt ϖ c) U) :=
  (isIntK_expMv_of_small hϖ fun κ => by rw [map_neg, norm_neg]; exact hG κ).mul
    (hU.subst (isIntK_xPt hc hϖ) (constantCoeff_xPt ϖ c))

end ThetaInt3

/-! ## Weighted bounds and divided powers -/

section Weight

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {σ : Type}

/-- **A submultiplicative weight** on exponents: nonnegative, `w(0) = 1`, `w(μ)·w(ν) ≤ w(μ + ν)`. -/
structure IsWeight (w : (σ →₀ ℕ) → ℝ) : Prop where
  /-- Nonnegativity. -/
  nonneg : ∀ κ, 0 ≤ w κ
  /-- Normalisation. -/
  zero : w 0 = 1
  /-- Submultiplicativity. -/
  mul_le : ∀ μ ν, w μ * w ν ≤ w (μ + ν)

/-- **Weighted boundedness**: `‖f_κ‖ ≤ r·w(κ)` for every exponent `κ`. -/
def IsWB (w : (σ →₀ ℕ) → ℝ) (r : ℝ) (f : MvPowerSeries σ ℂ_[ℓ]) : Prop :=
  ∀ κ, ‖MvPowerSeries.coeff κ f‖ ≤ r * w κ

variable {w : (σ →₀ ℕ) → ℝ}

/-- **Sums** keep a weighted bound. -/
theorem IsWB.add {r : ℝ} {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) (hg : IsWB w r g) :
    IsWB w r (f + g) := fun κ => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf κ) (hg κ))

/-- **Negatives** keep a weighted bound. -/
theorem IsWB.neg {r : ℝ} {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) : IsWB (ℓ := ℓ) w r (-f) := fun κ => by
  rw [map_neg, norm_neg]
  exact hf κ

/-- **Differences** keep a weighted bound. -/
theorem IsWB.sub {r : ℝ} {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) (hg : IsWB w r g) :
    IsWB w r (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- **Finite sums** keep a weighted bound. -/
theorem isWB_sum {ι : Type} (s : Finset ι) {r : ℝ} (hr : 0 ≤ r) (hw : ∀ κ, 0 ≤ w κ)
    {f : ι → MvPowerSeries σ ℂ_[ℓ]} (hf : ∀ i ∈ s, IsWB w r (f i)) : IsWB w r (∑ i ∈ s, f i) := fun κ => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr (hw κ)) fun i hi => hf i hi κ

/-- **A larger constant** keeps a weighted bound. -/
theorem IsWB.mono {r r' : ℝ} {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) (hw : ∀ κ, 0 ≤ w κ) (h : r ≤ r') :
    IsWB w r' f := fun κ => (hf κ).trans (mul_le_mul_of_nonneg_right h (hw κ))

/-- **Constant multiples.** -/
theorem IsWB.C_mul {r : ℝ} {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) (c : ℂ_[ℓ]) :
    IsWB w (‖c‖ * r) (MvPowerSeries.C c * f) := fun κ => by
  rw [MvPowerSeries.coeff_C_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf κ) (norm_nonneg _)

/-- **Products** of weighted-bounded series (submultiplicative weight). -/
theorem IsWB.mul (hw : IsWeight w) {r s : ℝ} (hs : 0 ≤ s) {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f)
    (hg : IsWB w s g) : IsWB w (r * s) (f * g) := fun κ => by
  classical
  rw [MvPowerSeries.coeff_mul]
  have hr : ∀ μ, 0 ≤ r * w μ := fun μ => (norm_nonneg _).trans (hf μ)
  have hr0 : 0 ≤ r := by have := hr 0; rwa [hw.zero, mul_one] at this
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (mul_nonneg hr0 hs) (hw.nonneg κ))
    fun p hp => ?_
  rw [norm_mul, ← (mem_antidiagonal.1 hp)]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖ ≤ (r * w p.1) * (s * w p.2) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (hr _)
    _ = (r * s) * (w p.1 * w p.2) := by ring
    _ ≤ (r * s) * w (p.1 + p.2) := mul_le_mul_of_nonneg_left (hw.mul_le _ _) (mul_nonneg hr0 hs)

/-- **`1` has weight `1`.** -/
theorem isWB_one (hw : IsWeight w) : IsWB (ℓ := ℓ) w 1 (1 : MvPowerSeries σ ℂ_[ℓ]) := fun κ => by
  classical
  rw [MvPowerSeries.coeff_one, one_mul]
  split_ifs with h
  · rw [h, hw.zero, norm_one]
  · rw [norm_zero]
    exact hw.nonneg κ

/-- **Powers** of weighted-bounded series. -/
theorem IsWB.pow (hw : IsWeight w) {r : ℝ} (hr : 0 ≤ r) {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) (n : ℕ) :
    IsWB w (r ^ n) (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact isWB_one hw
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hw hr hf

/-- **Substitution into a one-variable series** is bounded by its monomial terms. -/
theorem isWB_psubst {f : PowerSeries ℂ_[ℓ]} {Y : MvPowerSeries σ ℂ_[ℓ]}
    (hY0 : MvPowerSeries.constantCoeff Y = 0) {r : ℝ} (hr : ∀ κ, 0 ≤ r * w κ)
    (h : ∀ N, IsWB w r (MvPowerSeries.C (PowerSeries.coeff N f) * Y ^ N)) : IsWB w r (f.subst Y) := fun κ => by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hY0)]
  refine norm_finsum_le (hr κ) fun N => ?_
  rw [smul_eq_mul, ← MvPowerSeries.coeff_C_mul]
  exact h N κ

/-- **A difference of substitutions into a one-variable series** is bounded by the differences of monomial
terms. -/
theorem isWB_psubst_sub {f : PowerSeries ℂ_[ℓ]} {Y Z : MvPowerSeries σ ℂ_[ℓ]}
    (hY0 : MvPowerSeries.constantCoeff Y = 0) (hZ0 : MvPowerSeries.constantCoeff Z = 0) {r : ℝ}
    (hr : ∀ κ, 0 ≤ r * w κ) (h : ∀ N, IsWB w r (MvPowerSeries.C (PowerSeries.coeff N f) * (Y ^ N - Z ^ N))) :
    IsWB w r (f.subst Y - f.subst Z) := fun κ => by
  have hY := PowerSeries.HasSubst.of_constantCoeff_zero hY0
  have hZ := PowerSeries.HasSubst.of_constantCoeff_zero hZ0
  rw [map_sub, PowerSeries.coeff_subst hY, PowerSeries.coeff_subst hZ,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hY f κ) (PowerSeries.coeff_subst_finite hZ f κ)]
  refine norm_finsum_le (hr κ) fun N => ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← MvPowerSeries.coeff_C_mul]
  exact h N κ

/-- **Substitution into a series** is bounded by its monomial terms. -/
theorem isWB_subst {τ : Type} {f : MvPowerSeries τ ℂ_[ℓ]} {Y : τ → MvPowerSeries σ ℂ_[ℓ]}
    (hY : MvPowerSeries.HasSubst Y) {r : ℝ} (hr : ∀ κ, 0 ≤ r * w κ)
    (h : ∀ d : τ →₀ ℕ, IsWB w r (MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod fun s e => Y s ^ e)) :
    IsWB w r (MvPowerSeries.subst Y f) := fun κ => by
  rw [MvPowerSeries.coeff_subst hY]
  refine norm_finsum_le (hr κ) fun d => ?_
  rw [smul_eq_mul, ← MvPowerSeries.coeff_C_mul]
  exact h d κ

end Weight


section DP

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {σ : Type} {w : (σ →₀ ℕ) → ℝ}

/-- **The divided-power condition** on a coefficient `c` at `μ`: `‖c‖ᵏ ≤ ‖k!‖·w(kμ)` for every `k`. -/
def DPc (w : (σ →₀ ℕ) → ℝ) (c : ℂ_[ℓ]) (μ : σ →₀ ℕ) : Prop :=
  ∀ k : ℕ, ‖c‖ ^ k ≤ ‖(k.factorial : ℂ_[ℓ])‖ * w (k • μ)

/-- **`0` satisfies the divided-power condition.** -/
theorem dPc_zero (hw : IsWeight w) (μ : σ →₀ ℕ) : DPc (ℓ := ℓ) w 0 μ := fun k => by
  rcases k with _ | k
  · simp [hw.zero]
  · rw [norm_zero, zero_pow (Nat.succ_ne_zero k)]
    exact mul_nonneg (norm_nonneg _) (hw.nonneg _)

/-- **Divided powers of a monomial.** -/
theorem isWB_monomial_pow (hw : IsWeight w) {c : ℂ_[ℓ]} {μ : σ →₀ ℕ} (h : DPc w c μ) (k : ℕ) :
    IsWB w ‖(k.factorial : ℂ_[ℓ])‖ (MvPowerSeries.monomial μ c ^ k) := fun κ => by
  classical
  rw [MvPowerSeries.monomial_pow, MvPowerSeries.coeff_monomial]
  split_ifs with h'
  · rw [h', norm_pow]
    exact h k
  · rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (hw.nonneg κ)

/-- **Divided powers of a sum**: `(f + g)ᵏ/k! = Σ_j (f^j/j!)(g^{k−j}/(k−j)!)`. -/
theorem isWB_add_pow (hw : IsWeight w) {f g : MvPowerSeries σ ℂ_[ℓ]}
    (hf : ∀ k, IsWB w ‖(k.factorial : ℂ_[ℓ])‖ (f ^ k)) (hg : ∀ k, IsWB w ‖(k.factorial : ℂ_[ℓ])‖ (g ^ k))
    (k : ℕ) : IsWB w ‖(k.factorial : ℂ_[ℓ])‖ ((f + g) ^ k) := by
  rw [add_pow]
  refine isWB_sum _ (norm_nonneg _) hw.nonneg fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hj)
  have e : ‖(k.factorial : ℂ_[ℓ])‖ = ‖((k.choose j : ℕ) : ℂ_[ℓ])‖ *
      (‖(j.factorial : ℂ_[ℓ])‖ * ‖((k - j).factorial : ℂ_[ℓ])‖) := by
    rw [← norm_mul, ← norm_mul, ← Nat.cast_mul, ← Nat.cast_mul, ← mul_assoc,
      Nat.choose_mul_factorial_mul_factorial hjk]
  have h := ((hf j).mul hw (norm_nonneg _) (hg (k - j))).C_mul ((k.choose j : ℕ) : ℂ_[ℓ])
  rw [← e, map_natCast] at h
  intro κ
  have h' := h κ
  rwa [mul_comm (((k.choose j : ℕ)) : MvPowerSeries σ ℂ_[ℓ])] at h'

/-- **Divided powers**: if every coefficient of `f` satisfies the divided-power condition, then
`‖[fᵏ]_κ‖ ≤ ‖k!‖·w(κ)` (the coefficient `κ` sees only the truncation of `f`, a finite sum of monomials). -/
theorem isWB_pow_of_dp [Finite σ] (hw : IsWeight w) {f : MvPowerSeries σ ℂ_[ℓ]}
    (hdp : ∀ μ, DPc w (MvPowerSeries.coeff μ f) μ) (k : ℕ) : IsWB w ‖(k.factorial : ℂ_[ℓ])‖ (f ^ k) := by
  classical
  intro κ
  set N := κ.degree + 1
  set P : MvPowerSeries σ ℂ_[ℓ] := ((MvPowerSeries.truncTotal N f : MvPolynomial σ ℂ_[ℓ]) :
    MvPowerSeries σ ℂ_[ℓ]) with hPdef
  have e : MvPowerSeries.coeff κ (f ^ k) = MvPowerSeries.coeff κ (P ^ k) :=
    ((agreeBelow_truncTotal N f).pow_eq k) κ (Nat.lt_succ_self _)
  have hPc : ∀ β, MvPowerSeries.coeff β P = if β.degree < N then MvPowerSeries.coeff β f else 0 :=
    fun β => by rw [hPdef, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
  have hPsum : P = ∑ β ∈ (MvPowerSeries.truncTotal N f).support,
      MvPowerSeries.monomial β (MvPowerSeries.coeff β P) := by
    ext γ
    rw [map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq]
    split_ifs with hγ
    · rfl
    · rw [hPdef, MvPolynomial.coeff_coe]
      exact MvPolynomial.notMem_support_iff.1 hγ
  have hdpP : ∀ β, DPc w (MvPowerSeries.coeff β P) β := fun β => by
    rw [hPc]
    split_ifs
    · exact hdp β
    · exact dPc_zero hw β
  have key : ∀ s : Finset (σ →₀ ℕ), ∀ k, IsWB w ‖(k.factorial : ℂ_[ℓ])‖
      ((∑ β ∈ s, MvPowerSeries.monomial β (MvPowerSeries.coeff β P)) ^ k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro k
      rw [sum_empty]
      rcases k with _ | k
      · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, norm_one]
        exact isWB_one hw
      · rw [zero_pow (Nat.succ_ne_zero k)]
        intro κ
        rw [map_zero, norm_zero]
        exact mul_nonneg (norm_nonneg _) (hw.nonneg κ)
    | insert β s hβ ih =>
      intro k
      rw [sum_insert hβ, add_comm]
      exact isWB_add_pow hw ih (isWB_monomial_pow hw (hdpP β)) k
  rw [e, hPsum]
  exact key _ k κ

/-- **The exponential under the divided-power condition** is weighted-bounded by `1`. -/
theorem isWB_expMv_of_dp [Finite σ] (hw : IsWeight w) {f : MvPowerSeries σ ℂ_[ℓ]}
    (hdp : ∀ μ, DPc w (MvPowerSeries.coeff μ f) μ) : IsWB w 1 (expMv f) := fun κ => by
  rw [coeff_expMv, one_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hw.nonneg κ) fun k _ => ?_
  have h := isWB_pow_of_dp hw hdp k κ
  have hk : 0 < ‖(k.factorial : ℂ_[ℓ])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))
  rw [norm_div, div_le_iff₀ hk]
  linarith

/-- **`(n!)ᵏ` divides `(kn)!`.** -/
theorem pow_factorial_dvd (n k : ℕ) : n.factorial ^ k ∣ (k * n).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, show (k + 1) * n = k * n + n by ring]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/-- **`k!·(n!)ᵏ` divides `(kn)!`** for `n ≥ 1` (set partitions into `k` blocks of size `n`). -/
theorem factorial_mul_pow_dvd {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    k.factorial * n.factorial ^ k ∣ (k * n).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set M := k * (m + 1) + m with hM
    have hc : (M + 1) * M.choose m = (M + 1).choose (m + 1) * (m + 1) := Nat.add_one_mul_choose_eq _ _
    have hc2 : (M + 1).choose (m + 1) = (k + 1) * M.choose m := by
      have h1 : M + 1 = (k + 1) * (m + 1) := by rw [hM]; ring
      rw [h1] at hc
      have : (m + 1) * ((k + 1) * M.choose m) = (m + 1) * ((k + 1) * (m + 1)).choose (m + 1) := by
        linarith [hc]
      rw [h1]
      exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) this).symm
    have e := Nat.add_choose_mul_factorial_mul_factorial (k * (m + 1)) (m + 1)
    have hM1 : k * (m + 1) + (m + 1) = M + 1 := by rw [hM]; ring
    rw [hM1, hc2] at e
    refine ⟨M.choose m * t, ?_⟩
    rw [show (k + 1) * (m + 1) = M + 1 by rw [hM]; ring, ← e, ht, Nat.factorial_succ k, pow_succ]
    ring

end DP

/-! ## Mixed integrality -/

section MixInt

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

/-- **Mixed integrality over an orbit map** `orb : Φ → V`: integral in `Z` and, orbit by orbit, `κ!`-integral in
`z = ϖZ`: `‖R_κ‖ ≤ ∏_v min(1, ‖ϖ‖^{|κ_v|}/‖κ_v!‖)`. -/
def IsMixIntP {V : Type} [Fintype V] [DecidableEq V] (orb : Φ → V) (ϖ : ℂ_[ℓ])
    (R : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) : Prop :=
  ∀ κ, ‖MvPowerSeries.coeff κ R‖ ≤ ∏ v : V, min 1 (‖ϖ‖ ^ deg (κ.filter fun x => orb x.1 = v) /
    ‖((mfact (κ.filter fun x => orb x.1 = v) : ℕ) : ℂ_[ℓ])‖)

end MixInt

/-! ## The orbit weights of mixed integrality -/

section OrbW

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ}

/-- **The part of an exponent in the orbit `v`.** -/
abbrev resV (orb : Φ → V) (v : V) (κ : Φ × Fin b × Fin a →₀ ℕ) : Φ × Fin b × Fin a →₀ ℕ :=
  κ.filter fun x => orb x.1 = v

/-- **The orbit factor** `‖ϖ‖^{|κ_v|}/‖κ_v!‖` of mixed integrality. -/
def aV (orb : Φ → V) (ϖ : ℂ_[ℓ]) (v : V) (κ : Φ × Fin b × Fin a →₀ ℕ) : ℝ :=
  ‖ϖ‖ ^ deg (resV orb v κ) / ‖((mfact (resV orb v κ) : ℕ) : ℂ_[ℓ])‖

/-- **The weight of a split** `S` (the base orbits): `∏_{v ∈ S} ‖ϖ‖^{|κ_v|}/‖κ_v!‖`. -/
def bS (orb : Φ → V) (ϖ : ℂ_[ℓ]) (S : Finset V) (κ : Φ × Fin b × Fin a →₀ ℕ) : ℝ := ∏ v ∈ S, aV orb ϖ v κ

/-- **The weight of the gain variables**: `1` on exponents without base-orbit part, `0` elsewhere. -/
def bG (orb : Φ → V) (S : Finset V) (κ : Φ × Fin b × Fin a →₀ ℕ) : ℝ :=
  if ∀ v ∈ S, resV orb v κ = 0 then 1 else 0

omit [Fintype V] [Fintype Φ] [DecidableEq Φ] in
/-- **Restriction to an orbit is additive.** -/
theorem resV_add (orb : Φ → V) (v : V) (μ ν : Φ × Fin b × Fin a →₀ ℕ) :
    resV orb v (μ + ν) = resV orb v μ + resV orb v ν := Finsupp.filter_add

omit [Fintype V] [Fintype Φ] [DecidableEq Φ] in
/-- **Restriction to an orbit commutes with multiples.** -/
theorem resV_smul (orb : Φ → V) (v : V) (k : ℕ) (μ : Φ × Fin b × Fin a →₀ ℕ) :
    resV orb v (k • μ) = k • resV orb v μ := Finsupp.filter_smul

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The degree is additive.** -/
theorem deg_add {σ : Type} (μ ν : σ →₀ ℕ) : deg (μ + ν) = deg μ + deg ν :=
  Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

/-- **The multi-factorial as a product.** -/
theorem mfact_eq {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) : mfact κ = ∏ x, (κ x).factorial :=
  Finsupp.prod_fintype _ _ fun _ => Nat.factorial_zero

/-- **Multi-factorials are positive.** -/
theorem mfact_ne_zero {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) : mfact κ ≠ 0 := by
  rw [mfact_eq]
  exact prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _

/-- **`μ!·ν!` divides `(μ + ν)!`.** -/
theorem mfact_mul_dvd {σ : Type} [Fintype σ] (μ ν : σ →₀ ℕ) : mfact μ * mfact ν ∣ mfact (μ + ν) := by
  rw [mfact_eq, mfact_eq, mfact_eq, ← prod_mul_distrib]
  exact prod_dvd_prod_of_dvd _ _ fun x _ => by
    rw [Finsupp.add_apply]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _

/-- **`(μ!)ᵏ` divides `(kμ)!`.** -/
theorem pow_factorial_dvd' {σ : Type} [Fintype σ] (μ : σ →₀ ℕ) (k : ℕ) : mfact μ ^ k ∣ mfact (k • μ) := by
  rw [mfact_eq, mfact_eq, ← prod_pow]
  exact prod_dvd_prod_of_dvd _ _ fun x _ => by rw [Finsupp.smul_apply, smul_eq_mul]; exact pow_factorial_dvd _ k

/-- **`k!·(μ!)ᵏ` divides `(kμ)!`** for `μ ≠ 0`. -/
theorem mfact_pow_dvd {σ : Type} [Fintype σ] (μ : σ →₀ ℕ) (k : ℕ) (hμ : μ ≠ 0) :
    k.factorial * mfact μ ^ k ∣ mfact (k • μ) := by
  classical
  obtain ⟨x₀, hx₀⟩ := Finsupp.ne_iff.1 hμ
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx₀
  rw [mfact_eq, mfact_eq, ← prod_pow, ← mul_prod_erase _ _ (mem_univ x₀), ← mul_prod_erase _ _ (mem_univ x₀),
    ← mul_assoc]
  refine Nat.mul_dvd_mul ?_ (prod_dvd_prod_of_dvd _ _ fun x _ => ?_)
  · rw [Finsupp.smul_apply, smul_eq_mul]
    exact factorial_mul_pow_dvd (Nat.one_le_iff_ne_zero.2 hx₀) k
  · rw [Finsupp.smul_apply, smul_eq_mul]
    exact pow_factorial_dvd _ k

/-- **The norm of a multiple**: `‖n‖ ≤ ‖m‖` for `m ∣ n` in `ℂ_ℓ`. -/
theorem norm_natCast_le_of_dvd' {m n : ℕ} (h : m ∣ n) : ‖(n : ℂ_[ℓ])‖ ≤ ‖(m : ℂ_[ℓ])‖ := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)

/-- **Natural numbers `≠ 0` have positive norm.** -/
theorem norm_natCast_pos {n : ℕ} (hn : n ≠ 0) : 0 < ‖(n : ℂ_[ℓ])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hn)

omit [Fintype V] [DecidableEq Φ] in
/-- **The orbit factor is positive** (for `ϖ ≠ 0`). -/
theorem aV_pos (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (v : V) (κ : Φ × Fin b × Fin a →₀ ℕ) :
    0 < aV orb ϖ v κ :=
  div_pos (pow_pos (norm_pos_iff.2 hϖ) _) (norm_natCast_pos (mfact_ne_zero _))

omit [Fintype V] [Fintype Φ] [DecidableEq Φ] in
/-- **The orbit factor of the zero exponent** is `1`. -/
theorem aV_of_resV_eq_zero (orb : Φ → V) (ϖ : ℂ_[ℓ]) {v : V} {κ : Φ × Fin b × Fin a →₀ ℕ}
    (h : resV orb v κ = 0) : aV orb ϖ v κ = 1 := by
  rw [aV, h]
  simp [deg, mfact]

omit [Fintype V] [DecidableEq Φ] in
/-- **The orbit factor is submultiplicative.** -/
theorem aV_mul_le (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (v : V) (μ ν : Φ × Fin b × Fin a →₀ ℕ) :
    aV orb ϖ v μ * aV orb ϖ v ν ≤ aV orb ϖ v (μ + ν) := by
  have hp := norm_pos_iff.2 hϖ
  have h1 := norm_natCast_pos (ℓ := ℓ) (mfact_ne_zero (resV orb v μ))
  have h2 := norm_natCast_pos (ℓ := ℓ) (mfact_ne_zero (resV orb v ν))
  rw [aV, aV, aV, resV_add, deg_add, pow_add, div_mul_div_comm]
  refine div_le_div_of_nonneg_left (by positivity) (norm_natCast_pos (mfact_ne_zero _)) ?_
  rw [← norm_mul, ← Nat.cast_mul]
  exact norm_natCast_le_of_dvd' (mfact_mul_dvd _ _)

omit [Fintype V] [DecidableEq Φ] in
/-- **The split weight is a weight.** -/
theorem isWeight_bS (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (S : Finset V) :
    IsWeight (bS (b := b) (a := a) orb ϖ S) where
  nonneg κ := prod_nonneg fun v _ => (aV_pos orb hϖ v κ).le
  zero := prod_eq_one fun v _ => aV_of_resV_eq_zero orb ϖ (Finsupp.filter_zero _)
  mul_le μ ν := by
    rw [bS, bS, bS, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun v _ => mul_nonneg (aV_pos orb hϖ v μ).le (aV_pos orb hϖ v ν).le)
      fun v _ => aV_mul_le orb hϖ v μ ν

omit [Fintype Φ] in
/-- **The gain weight is a weight.** -/
theorem isWeight_bG (orb : Φ → V) (S : Finset V) : IsWeight (bG (b := b) (a := a) orb S) where
  nonneg κ := by unfold bG; split_ifs <;> norm_num
  zero := by rw [bG, ite_eq_left fun v _ => Finsupp.filter_zero _]
  mul_le μ ν := by
    unfold bG
    by_cases hμ : ∀ v ∈ S, resV orb v μ = 0
    · by_cases hν : ∀ v ∈ S, resV orb v ν = 0
      · rw [ite_eq_left hμ, ite_eq_left hν, ite_eq_left fun v hv => by rw [resV_add, hμ v hv, hν v hv, add_zero],
          one_mul]
      · rw [ite_eq_right hν, mul_zero]; split_ifs <;> norm_num
    · rw [ite_eq_right hμ, zero_mul]; split_ifs <;> norm_num

/-- **The gain weight is below the split weight.** -/
theorem bG_le_bS (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (S : Finset V) (κ : Φ × Fin b × Fin a →₀ ℕ) :
    bG orb S κ ≤ bS orb ϖ S κ := by
  unfold bG
  split_ifs with h
  · exact (prod_eq_one fun v hv => aV_of_resV_eq_zero orb ϖ (h v hv)).ge
  · exact (isWeight_bS orb hϖ S).nonneg κ

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Mixed integrality from all splits**: if `R` is bounded by every split weight, it is mixed-integral (take
`S` the orbits whose factor is `< 1`). -/
theorem isMixIntP_of_forall (orb : Φ → V) (ϖ : ℂ_[ℓ]) {R : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}
    (h : ∀ S : Finset V, IsWB (bS orb ϖ S) 1 R) : IsMixIntP orb ϖ R := fun κ => by
  have e : ∏ v : V, min 1 (‖ϖ‖ ^ deg (κ.filter fun x => orb x.1 = v) /
      ‖((mfact (κ.filter fun x => orb x.1 = v) : ℕ) : ℂ_[ℓ])‖) =
      bS orb ϖ (univ.filter fun v => aV orb ϖ v κ < 1) κ := by
    rw [bS, prod_filter]
    refine prod_congr rfl fun v _ => ?_
    change min 1 (aV orb ϖ v κ) = _
    split_ifs with hv
    · exact min_eq_right hv.le
    · exact min_eq_left (not_lt.1 hv)
  rw [e, ← one_mul (bS _ _ _ κ)]
  exact h _ κ

omit [Fintype V] [DecidableEq Φ] in
/-- **Powers of an orbit factor**: `m·(κ_v!)ᵏ ∣ (kκ_v)!` gives `aV(κ)ᵏ ≤ ‖m‖·aV(kκ)`. -/
theorem aV_pow_le (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (v : V) (μ : Φ × Fin b × Fin a →₀ ℕ) (k : ℕ) {m : ℕ}
    (hm : m ≠ 0) (h : m * mfact (resV orb v μ) ^ k ∣ mfact (k • resV orb v μ)) :
    aV orb ϖ v μ ^ k ≤ ‖(m : ℂ_[ℓ])‖ * aV orb ϖ v (k • μ) := by
  have hp := norm_pos_iff.2 hϖ
  have h1 := norm_natCast_pos (ℓ := ℓ) (mfact_ne_zero (resV orb v μ))
  have h2 := norm_natCast_pos (ℓ := ℓ) (mfact_ne_zero (k • resV orb v μ))
  have hm' := norm_natCast_pos (ℓ := ℓ) hm
  have hd := norm_natCast_le_of_dvd' (ℓ := ℓ) h
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow] at hd
  rw [aV, aV, resV_smul, deg_smul, div_pow, ← pow_mul, mul_comm (deg _) k, mul_div_assoc',
    div_le_div_iff₀ (pow_pos h1 k) h2]
  calc ‖ϖ‖ ^ (k * deg (resV orb v μ)) * ‖((mfact (k • resV orb v μ) : ℕ) : ℂ_[ℓ])‖ ≤
      ‖ϖ‖ ^ (k * deg (resV orb v μ)) * (‖(m : ℂ_[ℓ])‖ * ‖((mfact (resV orb v μ) : ℕ) : ℂ_[ℓ])‖ ^ k) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

omit [DecidableEq Φ] [Fintype V] in
/-- **The divided-power condition for the split weight** at an exponent with a base-orbit part:
`‖c‖ ≤ bS(μ)` gives `‖c‖ᵏ ≤ ‖k!‖·bS(kμ)` (`k!·(μ_v!)ᵏ ∣ (kμ_v)!` for `μ_v ≠ 0`). -/
theorem dPc_bS_of_base (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ≠ 0) (S : Finset V) {μ : Φ × Fin b × Fin a →₀ ℕ}
    (hμ : ∃ v ∈ S, resV orb v μ ≠ 0) {c : ℂ_[ℓ]} (hc : ‖c‖ ≤ bS orb ϖ S μ) : DPc (bS orb ϖ S) c μ := fun k => by
  obtain ⟨v₀, hv₀, hμ0⟩ := hμ
  have hpos : ∀ v (κ : Φ × Fin b × Fin a →₀ ℕ), 0 ≤ aV orb ϖ v κ := fun v κ => (aV_pos orb hϖ v κ).le
  have h1 : ∀ v, aV orb ϖ v μ ^ k ≤ aV orb ϖ v (k • μ) := fun v => by
    have := aV_pow_le orb hϖ v μ k one_ne_zero (by rw [one_mul]; exact pow_factorial_dvd' _ k)
    rwa [Nat.cast_one, norm_one, one_mul] at this
  have h0 := aV_pow_le orb hϖ v₀ μ k (Nat.factorial_ne_zero k) (mfact_pow_dvd _ k hμ0)
  calc ‖c‖ ^ k ≤ bS orb ϖ S μ ^ k := pow_le_pow_left₀ (norm_nonneg _) hc k
    _ = aV orb ϖ v₀ μ ^ k * ∏ v ∈ S.erase v₀, aV orb ϖ v μ ^ k := by
        rw [bS, ← prod_pow]
        exact (mul_prod_erase S (fun v => aV orb ϖ v μ ^ k) hv₀).symm
    _ ≤ (‖(k.factorial : ℂ_[ℓ])‖ * aV orb ϖ v₀ (k • μ)) * ∏ v ∈ S.erase v₀, aV orb ϖ v (k • μ) :=
        mul_le_mul h0 (prod_le_prod₀ (fun v _ => pow_nonneg (hpos v μ) k) fun v _ => h1 v)
          (prod_nonneg fun v _ => pow_nonneg (hpos v μ) k) (mul_nonneg (norm_nonneg _) (hpos _ _))
    _ = ‖(k.factorial : ℂ_[ℓ])‖ * bS orb ϖ S (k • μ) := by
        rw [bS, ← mul_prod_erase S (fun v => aV orb ϖ v (k • μ)) hv₀, mul_assoc]

omit [Fintype Φ] [DecidableEq Φ] [Fintype V] in
/-- **The divided-power condition for the split weight** at an exponent without base-orbit part, for a small
coefficient `‖c‖ ≤ ‖ϖ‖^{ℓ+1}` (`ϖ^{(ℓ+1)k}/k!` is integral). -/
theorem dPc_bS_of_gain (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
    {μ : Φ × Fin b × Fin a →₀ ℕ} (hμ : ∀ v ∈ S, resV orb v μ = 0) {c : ℂ_[ℓ]} (hc : ‖c‖ ≤ ‖ϖ‖ ^ (ℓ + 1)) :
    DPc (bS orb ϖ S) c μ := fun k => by
  have hb : bS orb ϖ S (k • μ) = 1 := prod_eq_one fun v hv =>
    aV_of_resV_eq_zero orb ϖ (by rw [resV_smul, hμ v hv, smul_zero])
  have hk := norm_natCast_pos (ℓ := ℓ) (Nat.factorial_ne_zero k)
  have h := norm_pow_root_div_factorial_le hϖ k
  rw [norm_div, div_le_one hk, norm_pow, pow_mul] at h
  rw [hb, mul_one]
  exact (pow_le_pow_left₀ (norm_nonneg _) hc k).trans h

end OrbW

/-! ## Mixed integrality: valuations of factorials and of the exponential -/

section MixVal

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- **Legendre, first term**: `‖m!‖ ≤ ‖ℓ‖^{⌊m/ℓ⌋}`. -/
theorem norm_factorial_le (m : ℕ) : ‖(m.factorial : ℂ_[ℓ])‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ (m / ℓ) := by
  have hp := hℓ.out
  have hdvd : ℓ ^ (m / ℓ) ∣ m.factorial := by
    rcases Nat.lt_or_ge m ℓ with h | h
    · rw [Nat.div_eq_of_lt h, pow_zero]
      exact one_dvd _
    · rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero m),
        padicValNat_factorial (Nat.lt_succ_self (Nat.log ℓ m))]
      have h1 : 1 ∈ Ico 1 (Nat.log ℓ m + 1) := by
        rw [mem_Ico]
        exact ⟨le_rfl, Nat.succ_lt_succ (Nat.log_pos hp.one_lt h)⟩
      calc m / ℓ = m / ℓ ^ 1 := by rw [pow_one]
        _ ≤ ∑ i ∈ Ico 1 (Nat.log ℓ m + 1), m / ℓ ^ i :=
          single_le_sum (f := fun i => m / ℓ ^ i) (fun _ _ => Nat.zero_le _) h1
  have := norm_natCast_le_of_dvd' (ℓ := ℓ) hdvd
  rwa [Nat.cast_pow, norm_pow] at this

/-- **`(ℓ²−1)·⌊m/ℓ⌋ ≥ m − (ℓ − 1)`.** -/
theorem sub_le_mul_div (m : ℕ) : m ≤ (ℓ ^ 2 - 1) * (m / ℓ) + (ℓ - 1) := by
  have h2 := hℓ.out.two_le
  have h1 : ℓ ≤ ℓ ^ 2 - 1 := by
    have : ℓ * 2 ≤ ℓ * ℓ := Nat.mul_le_mul_left _ h2
    rw [sq]; omega
  have h3 := Nat.div_add_mod m ℓ
  have h4 := Nat.mod_lt m (by omega : 0 < ℓ)
  have h5 : ℓ * (m / ℓ) ≤ (ℓ ^ 2 - 1) * (m / ℓ) := Nat.mul_le_mul_right _ h1
  omega

/-- **Norms in `ℂ_ℓ` as powers of `ϖ`**: `‖ℓ‖ = ‖ϖ‖^{ℓ²−1}`. -/
theorem norm_ell_eq {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) : ‖(ℓ : ℂ_[ℓ])‖ = ‖ϖ‖ ^ (ℓ ^ 2 - 1) := by
  rw [← norm_pow, hϖ]

/-- **The factorial bound in powers of `ϖ`**: `‖m!‖·‖ϖ‖^{ℓ−1} ≤ ‖ϖ‖^m`. -/
theorem norm_factorial_mul_le {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (m : ℕ) :
    ‖(m.factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ^ (ℓ - 1) ≤ ‖ϖ‖ ^ m := by
  have hϖ1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  calc ‖(m.factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ^ (ℓ - 1) ≤ ‖ϖ‖ ^ ((ℓ ^ 2 - 1) * (m / ℓ)) * ‖ϖ‖ ^ (ℓ - 1) := by
        gcongr
        rw [pow_mul, ← norm_ell_eq hϖ]
        exact norm_factorial_le m
    _ = ‖ϖ‖ ^ ((ℓ ^ 2 - 1) * (m / ℓ) + (ℓ - 1)) := by rw [pow_add]
    _ ≤ ‖ϖ‖ ^ m := pow_le_pow_of_le_one hϖ0 hϖ1 (sub_le_mul_div m)

/-- **The descending factorial divides as `N·(k−1)!`**: `‖N(N−1)⋯(N−k+1)‖ ≤ ‖N‖·‖(k−1)!‖`. -/
theorem norm_descFactorial_le (N k : ℕ) (hk : 1 ≤ k) :
    ‖(N.descFactorial k : ℂ_[ℓ])‖ ≤ ‖(N : ℂ_[ℓ])‖ * ‖((k - 1).factorial : ℂ_[ℓ])‖ := by
  rcases N with _ | N
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.zero_descFactorial_succ, Nat.cast_zero, norm_zero]
    positivity
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_descFactorial_succ, Nat.cast_mul, norm_mul, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_left (norm_natCast_le_of_dvd' (Nat.factorial_dvd_descFactorial N j))
      (norm_nonneg _)

/-- **The rescaled exponential mod `ℓ`**: `‖λ_N‖ ≤ ‖ℓ‖` unless `N` is an even power of `ℓ` (one variable:
`λ ≡ Σ_l (−1)^l T^{ℓ^{2l}} (mod ℓ)`, the contraction `isDivK_lamK_sub_tauS` for a one-point frame). -/
theorem norm_coeff_lamK_le {N : ℕ} (hN : ∀ l, N ≠ ℓ ^ (2 * l)) :
    ‖PowerSeries.coeff N (lamK ℂ_[ℓ] ℓ)‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ := by
  set x₀ : Unit × Fin 1 × Fin 1 := ((), 0, 0)
  have hx : ∀ x : Unit × Fin 1 × Fin 1, x = x₀ := fun x => Subsingleton.elim _ _
  have hTp : ∀ k : ℕ, ∀ x y : Unit × Fin 1 × Fin 1, ∑ i : Unit × Fin 1 × Fin 1, ((1 : ℕ) : unramC ℓ) *
      (fun _ _ => (1 : unramC ℓ)) i x *
      (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) ((fun _ _ => (1 : unramC ℓ)) i y) =
        if x = (sucV (Equiv.refl Unit) ^ (2 * k + 1)) y then 1 else 0 := fun k x y => by
    rw [ite_eq_left (Subsingleton.elim _ _), Fintype.sum_subsingleton _ x₀]
    simp
  have h := isDivK_lamK_sub_tauS (K := unramC ℓ) UnramFrobLift.norm_frobUnram_sub_pow_le hTp
    (fun _ _ => by rw [norm_one]) x₀ 0 (Finsupp.single x₀ N)
  have hy : ySer (fun _ _ => (1 : unramC ℓ)) x₀ = MvPowerSeries.X x₀ := by
    rw [ySer, Fintype.sum_subsingleton _ x₀, map_one, one_mul]
  have ht : MvPowerSeries.coeff (Finsupp.single x₀ N) (tauS (ℓ := ℓ) (Equiv.refl Unit)
      (fun _ _ => (1 : unramC ℓ)) x₀) = 0 := by
    rw [tauS, Fintype.sum_subsingleton _ x₀, map_one, one_mul]
    change ∑ l ∈ range (deg (Finsupp.single x₀ N) + 1), _ = _
    refine sum_eq_zero fun l _ => ite_eq_right fun he => hN l ?_
    have := congrArg (fun n => n x₀) he
    simp only [Finsupp.single_eq_same] at this
    exact this
  rw [show (frobS ℓ (UnramFrobLift.frobUnram ℓ) ^ 0) = RingHom.id _ from pow_zero _, RingHom.id_apply,
    RingHom.id_apply, map_sub, ht, sub_zero, hy, PowerSeries.coeff_subst_single, ite_eq_left (by simp),
    Finsupp.single_eq_same] at h
  have e : PowerSeries.coeff N (lamK ℂ_[ℓ] ℓ) = ((PowerSeries.coeff N (lamK (unramC ℓ) ℓ) : unramC ℓ) : ℂ_[ℓ]) := by
    rw [← map_lamK (unramC ℓ).subtype, PowerSeries.coeff_map]
    rfl
  rw [e]
  have e2 : ‖((ℓ : unramC ℓ) : ℂ_[ℓ])‖ = ‖(ℓ : ℂ_[ℓ])‖ := by norm_cast
  exact h.trans_eq e2

/-- **The rescaled exponential times its degree**: `‖λ_N‖·‖N‖ ≤ ‖ℓ‖` for `N ≥ 2`. -/
theorem norm_coeff_lamK_mul_le {N : ℕ} (hN : 2 ≤ N) :
    ‖PowerSeries.coeff N (lamK ℂ_[ℓ] ℓ)‖ * ‖(N : ℂ_[ℓ])‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ := by
  have hlam : ‖PowerSeries.coeff N (lamK ℂ_[ℓ] ℓ)‖ ≤ 1 := isInt_lamK ℂ_[ℓ] ℓ N
  by_cases h : ∃ l, N = ℓ ^ (2 * l)
  · obtain ⟨l, rfl⟩ := h
    have hl : l ≠ 0 := by rintro rfl; simp at hN
    have hd : ℓ ∣ ℓ ^ (2 * l) := dvd_pow_self ℓ (by omega)
    calc _ ≤ 1 * ‖((ℓ ^ (2 * l) : ℕ) : ℂ_[ℓ])‖ := mul_le_mul_of_nonneg_right hlam (norm_nonneg _)
      _ ≤ ‖(ℓ : ℂ_[ℓ])‖ := by rw [one_mul]; exact norm_natCast_le_of_dvd' hd
  · push Not at h
    calc _ ≤ ‖(ℓ : ℂ_[ℓ])‖ * 1 :=
          mul_le_mul (norm_coeff_lamK_le h) (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _)
            (norm_nonneg _)
      _ = _ := mul_one _

end MixVal

/-! ## Mixed integrality: the frame points, split by a set of base orbits -/

section MixPts

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ}

/-- **The base weight**: `bS` on exponents with a base-orbit part, `0` on exponents without. -/
def bB (orb : Φ → V) (ϖ : ℂ_[ℓ]) (S : Finset V) (κ : Φ × Fin b × Fin a →₀ ℕ) : ℝ :=
  if ∀ v ∈ S, resV orb v κ = 0 then 0 else bS orb ϖ S κ

/-- **Products with three weights**: `w₁(μ)·w₂(ν) ≤ w₃(μ + ν)`. -/
theorem IsWB.mul' {σ : Type} {w₁ w₂ w₃ : (σ →₀ ℕ) → ℝ} (h : ∀ μ ν, w₁ μ * w₂ ν ≤ w₃ (μ + ν)) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hw₃ : ∀ κ, 0 ≤ w₃ κ) {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w₁ r f)
    (hg : IsWB w₂ s g) : IsWB w₃ (r * s) (f * g) := fun κ => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (mul_nonneg hr hs) (hw₃ κ))
    fun p hp => ?_
  rw [norm_mul, ← (mem_antidiagonal.1 hp)]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖ ≤ (r * w₁ p.1) * (s * w₂ p.2) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) ((norm_nonneg _).trans (hf _))
    _ = (r * s) * (w₁ p.1 * w₂ p.2) := by ring
    _ ≤ (r * s) * w₃ (p.1 + p.2) := mul_le_mul_of_nonneg_left (h _ _) (mul_nonneg hr hs)

/-- **A larger weight** keeps a weighted bound. -/
theorem IsWB.weight_mono {σ : Type} {w w' : (σ →₀ ℕ) → ℝ} (h : ∀ κ, w κ ≤ w' κ) {r : ℝ} (hr : 0 ≤ r)
    {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IsWB w r f) : IsWB w' r f := fun κ =>
  (hf κ).trans (mul_le_mul_of_nonneg_left (h κ) hr)

variable (orb : Φ → V) {ϖ : ℂ_[ℓ]} (S : Finset V)

/-- **The base weight is below the split weight.** -/
theorem bB_le_bS (hϖ : ϖ ≠ 0) (κ : Φ × Fin b × Fin a →₀ ℕ) : bB orb ϖ S κ ≤ bS orb ϖ S κ := by
  unfold bB
  split_ifs
  · exact (isWeight_bS orb hϖ S).nonneg κ
  · exact le_rfl

/-- **The base weight is nonnegative.** -/
theorem bB_nonneg (hϖ : ϖ ≠ 0) (κ : Φ × Fin b × Fin a →₀ ℕ) : 0 ≤ bB orb ϖ S κ := by
  unfold bB
  split_ifs
  · exact le_rfl
  · exact (isWeight_bS orb hϖ S).nonneg κ

/-- **Gain times base is base.** -/
theorem bG_mul_bB_le (hϖ : ϖ ≠ 0) (μ ν : Φ × Fin b × Fin a →₀ ℕ) :
    bG orb S μ * bB orb ϖ S ν ≤ bB orb ϖ S (μ + ν) := by
  unfold bG
  split_ifs with hμ
  · rw [one_mul]
    unfold bB
    by_cases hν : ∀ v ∈ S, resV orb v ν = 0
    · rw [ite_eq_left hν]
      exact bB_nonneg orb S hϖ _
    · have hμν : ¬ ∀ v ∈ S, resV orb v (μ + ν) = 0 := fun h => hν fun v hv => by
        have := h v hv
        rw [resV_add, hμ v hv, zero_add] at this
        exact this
      rw [ite_eq_right hν, ite_eq_right hμν]
      have h1 : bS orb ϖ S μ = 1 := prod_eq_one fun v hv => aV_of_resV_eq_zero orb ϖ (hμ v hv)
      calc bS orb ϖ S ν = bS orb ϖ S μ * bS orb ϖ S ν := by rw [h1, one_mul]
        _ ≤ _ := (isWeight_bS orb hϖ S).mul_le μ ν
  · rw [zero_mul]
    exact bB_nonneg orb S hϖ _

/-- **Base times split is base.** -/
theorem bB_mul_bS_le (hϖ : ϖ ≠ 0) (μ ν : Φ × Fin b × Fin a →₀ ℕ) :
    bB orb ϖ S μ * bS orb ϖ S ν ≤ bB orb ϖ S (μ + ν) := by
  by_cases hμ : ∀ v ∈ S, resV orb v μ = 0
  · rw [show bB orb ϖ S μ = 0 from ite_eq_left hμ, zero_mul]
    exact bB_nonneg orb S hϖ _
  · have hμν : ¬ ∀ v ∈ S, resV orb v (μ + ν) = 0 := fun h => hμ fun v hv => by
      have := h v hv
      rw [resV_add] at this
      exact (add_eq_zero.1 this).1
    rw [show bB orb ϖ S μ = bS orb ϖ S μ from ite_eq_right hμ, show bB orb ϖ S (μ + ν) = bS orb ϖ S (μ + ν) from
      ite_eq_right hμν]
    exact (isWeight_bS orb hϖ S).mul_le μ ν

omit [Fintype Φ] in
/-- **Combining a split bound with a base support.** -/
theorem isWB_bB_of {r s : ℝ} {f : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}
    (h1 : IsWB (bS orb ϖ S) r f) (h2 : IsWB (bB orb ϖ S) s f) : IsWB (bB orb ϖ S) r f := fun κ => by
  have h := h2 κ
  by_cases hκ : ∀ v ∈ S, resV orb v κ = 0
  · rw [show bB orb ϖ S κ = 0 from ite_eq_left hκ, mul_zero] at h ⊢
    exact h
  · rw [show bB orb ϖ S κ = bS orb ϖ S κ from ite_eq_right hκ]
    exact h1 κ

/-- **Divided powers from a base bound**: a coefficient of a series bounded by `bB` satisfies the divided-power
condition for `bS`. -/
theorem dPc_of_isWB_bB (hϖ : ϖ ≠ 0) {f : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]} (hf : IsWB (bB orb ϖ S) 1 f)
    (μ : Φ × Fin b × Fin a →₀ ℕ) : DPc (bS orb ϖ S) (MvPowerSeries.coeff μ f) μ := by
  have h := hf μ
  rw [one_mul] at h
  by_cases hμ : ∀ v ∈ S, resV orb v μ = 0
  · rw [show bB orb ϖ S μ = 0 from ite_eq_left hμ] at h
    rw [norm_le_zero_iff.1 h]
    exact dPc_zero (isWeight_bS orb hϖ S) μ
  · rw [show bB orb ϖ S μ = bS orb ϖ S μ from ite_eq_right hμ] at h
    push Not at hμ
    exact dPc_bS_of_base orb hϖ S hμ h

omit [Fintype V] [DecidableEq Φ] [Fintype Φ] in
/-- **Restriction of a single exponent.** -/
theorem resV_single (v : V) (x : Φ × Fin b × Fin a) (m : ℕ) :
    resV orb v (Finsupp.single x m) = if orb x.1 = v then Finsupp.single x m else 0 := by
  split_ifs with h
  · exact Finsupp.filter_single_of_pos _ h
  · exact Finsupp.filter_single_of_neg _ h

omit [Fintype V] [DecidableEq Φ] [Fintype Φ] in
/-- **A base variable gives a base exponent.** -/
theorem not_pure_single {x : Φ × Fin b × Fin a} (hx : orb x.1 ∈ S) {m : ℕ} (hm : m ≠ 0) :
    ¬ ∀ v ∈ S, resV orb v (Finsupp.single x m) = 0 := fun h => by
  have := h _ hx
  rw [resV_single, ite_eq_left rfl] at this
  exact hm (Finsupp.single_eq_zero.1 this)

omit [Fintype V] [DecidableEq Φ] [Fintype Φ] in
/-- **A gain variable gives a pure gain exponent.** -/
theorem pure_single {x : Φ × Fin b × Fin a} (hx : orb x.1 ∉ S) (m : ℕ) :
    ∀ v ∈ S, resV orb v (Finsupp.single x m) = 0 := fun v hv => by
  rw [resV_single, ite_eq_right (by rintro rfl; exact hx hv)]

omit [Fintype Φ] [DecidableEq Φ] [Fintype V] in
/-- **The split weight of a single base exponent** `x^m` is `‖ϖ‖^m/‖m!‖`. -/
theorem bS_single {x : Φ × Fin b × Fin a} (hx : orb x.1 ∈ S) (m : ℕ) :
    bS orb ϖ S (Finsupp.single x m) = ‖ϖ‖ ^ m / ‖(m.factorial : ℂ_[ℓ])‖ := by
  rw [bS, prod_eq_single (orb x.1) (fun v _ hv => aV_of_resV_eq_zero orb ϖ (by
    rw [resV_single, ite_eq_right fun h => hv h.symm])) (fun h => absurd hx h), aV, resV_single, ite_eq_left rfl,
    deg_single]
  congr 3
  exact Finsupp.prod_single_index Nat.factorial_zero

end MixPts


section MixPts2

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (S : Finset V)

/-- **The gain part of frame coefficients** (base variables set to `0`). -/
def cGain (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) (i x : Φ × Fin b × Fin a) : ℂ_[ℓ] :=
  if orb x.1 ∈ S then 0 else c i x

/-- **The base part of frame coefficients** (gain variables set to `0`). -/
def cBase (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) (i x : Φ × Fin b × Fin a) : ℂ_[ℓ] :=
  if orb x.1 ∈ S then c i x else 0

omit [DecidableEq Φ] [Fintype V] in
/-- **The frame coordinates split** into gain and base parts. -/
theorem ySer_split (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) (i : Φ × Fin b × Fin a) :
    ySer c i = ySer (cGain orb S c) i + ySer (cBase orb S c) i := by
  rw [ySer, ySer, ySer, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← add_mul, ← map_add]
  unfold cGain cBase
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] in
/-- **The coefficients of a linear form.** -/
theorem coeff_ySer (d : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]) (i : Φ × Fin b × Fin a)
    (μ : Φ × Fin b × Fin a →₀ ℕ) :
    MvPowerSeries.coeff μ (ySer d i) = ∑ x, if μ = Finsupp.single x 1 then d i x else 0 := by
  classical
  rw [ySer, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs <;> simp

/-- **The gain coordinates are integral and pure gain.** -/
theorem isWB_ySer_gain {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (i : Φ × Fin b × Fin a) : IsWB (bG orb S) 1 (ySer (cGain orb S c) i) := fun μ => by
  rw [coeff_ySer, one_mul]
  have hb : 0 ≤ bG orb S μ := (isWeight_bG orb S).nonneg μ
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun x _ => ?_
  unfold cGain
  split_ifs with h1 h2
  · rw [norm_zero]; exact hb
  · rw [h1, bG, ite_eq_left (pure_single orb S h2 1)]
    exact hc i x
  · rw [norm_zero]; exact hb

/-- **The base coordinates times `ϖ` are bounded by the base weight.** -/
theorem isWB_ySer_base (hϖ : ϖ ≠ 0) {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]}
    (hc : ∀ i x, ‖c i x‖ ≤ 1) (i : Φ × Fin b × Fin a) :
    IsWB (bB orb ϖ S) 1 (MvPowerSeries.C ϖ * ySer (cBase orb S c) i) := fun μ => by
  rw [MvPowerSeries.coeff_C_mul, coeff_ySer, mul_sum, one_mul]
  have hb : 0 ≤ bB orb ϖ S μ := bB_nonneg orb S hϖ μ
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun x _ => ?_
  unfold cBase
  split_ifs with h1 h2
  · rw [h1, show bB orb ϖ S (Finsupp.single x 1) = bS orb ϖ S (Finsupp.single x 1) from
      ite_eq_right (not_pure_single orb S h2 one_ne_zero), bS_single orb S h2, pow_one, Nat.factorial_one,
      Nat.cast_one, norm_one, div_one, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hc i x)
  · rw [mul_zero, norm_zero]; exact hb
  · rw [mul_zero, norm_zero]; exact hb

end MixPts2


section MixPts3

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- **The linear coefficient of `e`** is `1`. -/
theorem coeff_one_expLT : PowerSeries.coeff 1 (expLT ℂ_[ℓ] ℓ) = 1 := by
  have h : IsUnit (PowerSeries.coeff 1 (logLT ℂ_[ℓ] ℓ)) := by rw [coeff_one_logLT]; exact isUnit_one
  rw [expLT, PowerSeries.coeff_one_substInvOfIsUnit]
  have : (h.unit : ℂ_[ℓ]) = 1 := by rw [IsUnit.unit_spec, coeff_one_logLT]
  rw [Units.val_inv_eq_inv_val, this, inv_one]

/-- **The coefficients of `e` in terms of `λ`**: `‖e_N‖·‖ϖ‖^{N−1} = ‖λ_N‖`. -/
theorem norm_coeff_expLT_mul {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (N : ℕ) :
    ‖PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ)‖ * ‖ϖ‖ ^ (N - 1) = ‖PowerSeries.coeff N (lamK ℂ_[ℓ] ℓ)‖ := by
  rw [mul_comm, ← norm_pow, ← norm_mul, pow_mul_coeff_expLT hℓ.out.one_lt hϖ, lamK, PowerSeries.coeff_map]
  rfl

/-- **The terms of `e(ϖa + ϖb) − e(ϖa)`**: for `N ≥ 2`, `m < N`,
`‖e_N‖·‖C(N, m)‖·‖ϖ‖^m·‖(N − m)!‖ ≤ ‖ϖ‖^{ℓ²−1−ℓ}` (from `‖λ_N‖·‖N‖ ≤ ‖ℓ‖` and Legendre). -/
theorem norm_expLT_term_le {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) {N m : ℕ} (hN : 2 ≤ N) (hm : m < N) :
    ‖PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ)‖ * (‖((N.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m *
      ‖((N - m).factorial : ℂ_[ℓ])‖)) ≤ ‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ) := by
  have h2 := hℓ.out.two_le
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  set e := ‖PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ)‖
  have he0 : 0 ≤ e := norm_nonneg _
  have hdesc : ‖((N.choose m : ℕ) : ℂ_[ℓ])‖ * ‖((N - m).factorial : ℂ_[ℓ])‖ ≤
      ‖(N : ℂ_[ℓ])‖ * ‖((N - m - 1).factorial : ℂ_[ℓ])‖ := by
    rw [← norm_mul, ← Nat.cast_mul, mul_comm, ← Nat.choose_symm hm.le, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact norm_descFactorial_le N (N - m) (by omega)
  have hf := norm_factorial_mul_le hϖ (N - m - 1)
  have hl := norm_coeff_lamK_mul_le (ℓ := ℓ) hN
  rw [← norm_coeff_expLT_mul hϖ N, norm_ell_eq hϖ] at hl
  have key : e * (‖((N.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((N - m).factorial : ℂ_[ℓ])‖)) * ‖ϖ‖ ^ (ℓ - 1) ≤
      ‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ) * ‖ϖ‖ ^ (ℓ - 1) := by
    calc e * (‖((N.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((N - m).factorial : ℂ_[ℓ])‖)) * ‖ϖ‖ ^ (ℓ - 1)
        = e * ‖ϖ‖ ^ m * ((‖((N.choose m : ℕ) : ℂ_[ℓ])‖ * ‖((N - m).factorial : ℂ_[ℓ])‖) * ‖ϖ‖ ^ (ℓ - 1)) := by
          ring
      _ ≤ e * ‖ϖ‖ ^ m * ((‖(N : ℂ_[ℓ])‖ * ‖((N - m - 1).factorial : ℂ_[ℓ])‖) * ‖ϖ‖ ^ (ℓ - 1)) := by gcongr
      _ = e * ‖ϖ‖ ^ m * ‖(N : ℂ_[ℓ])‖ * (‖((N - m - 1).factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ^ (ℓ - 1)) := by ring
      _ ≤ e * ‖ϖ‖ ^ m * ‖(N : ℂ_[ℓ])‖ * ‖ϖ‖ ^ (N - m - 1) := by gcongr
      _ = e * ‖ϖ‖ ^ (N - 1) * ‖(N : ℂ_[ℓ])‖ := by
          rw [show N - 1 = m + (N - m - 1) by omega, pow_add]
          ring
      _ ≤ ‖ϖ‖ ^ (ℓ ^ 2 - 1) := hl
      _ = ‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ) * ‖ϖ‖ * ‖ϖ‖ ^ (ℓ - 1) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          have : ℓ ≤ ℓ ^ 2 - 1 := by
            have : ℓ * 2 ≤ ℓ * ℓ := Nat.mul_le_mul_left _ h2
            rw [sq]; omega
          omega
      _ ≤ ‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ) * ‖ϖ‖ ^ (ℓ - 1) := by
          gcongr
          exact mul_le_of_le_one_right (by positivity) hϖ1
  exact le_of_mul_le_mul_right key (pow_pos hp _)

end MixPts3


section MixPts4

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)

/-- **Divided powers of a base-bounded series**: `f` bounded by `bB` gives `fᵏ` bounded by `‖k!‖·bB` for
`k ≥ 1`. -/
theorem isWB_bB_pow (hϖ0 : ϖ ≠ 0) {f : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]} (hf : IsWB (bB orb ϖ S) 1 f)
    {k : ℕ} (hk : 1 ≤ k) : IsWB (bB orb ϖ S) ‖(k.factorial : ℂ_[ℓ])‖ (f ^ k) := by
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have h1 : IsWB (bS orb ϖ S) ‖(k.factorial : ℂ_[ℓ])‖ (f ^ k) :=
    isWB_pow_of_dp hS (dPc_of_isWB_bB orb S hϖ0 hf) k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : IsWB (bB orb ϖ S) (1 * 1 ^ j) (f * f ^ j) :=
    IsWB.mul' (bB_mul_bS_le orb S hϖ0) zero_le_one (by positivity) (bB_nonneg orb S hϖ0) hf
      ((hf.weight_mono (bB_le_bS orb S hϖ0) zero_le_one).pow hS zero_le_one j)
  rw [← pow_succ' f j] at h2
  exact isWB_bB_of orb S h1 h2

include hc in
/-- **The gain point** `ϖ·a_i` is pure gain, of size `‖ϖ‖`. -/
theorem isWB_aP (i : Φ × Fin b × Fin a) :
    IsWB (bG orb S) ‖ϖ‖ (MvPowerSeries.C ϖ * ySer (cGain orb S c) i) := by
  have h := (isWB_ySer_gain orb S hc i).C_mul ϖ
  rwa [mul_one] at h

include hc in
/-- **The gain Lubin–Tate point** `A_i = e(ϖ·a_i) = ϖ·λ(a_i)` is pure gain, of size `‖ϖ‖`. -/
theorem isWB_AP (i : Φ × Fin b × Fin a) :
    IsWB (bG orb S) ‖ϖ‖ (MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) := by
  have hG := isWeight_bG (b := b) (a := a) orb S
  have hy := isWB_ySer_gain orb S hc i
  have hl : IsWB (bG orb S) 1 ((lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) :=
    isWB_psubst (constantCoeff_ySer _ i) (fun κ => by rw [one_mul]; exact hG.nonneg κ) fun N => by
      refine ((hy.pow hG zero_le_one N).C_mul _).mono hG.nonneg ?_
      rw [one_pow, mul_one]
      exact isInt_lamK ℂ_[ℓ] ℓ N
  have h := hl.C_mul ϖ
  rwa [mul_one] at h

include hϖ hc in
/-- **The base part of a point**: `X_i − A_i − ϖ·b_i = Σ_{N ≥ 2} e_N((ϖy_i)^N − (ϖa_i)^N)` has size
`‖ϖ‖^{ℓ²−1−ℓ}` in the base weight (`norm_expLT_term_le`). -/
theorem isWB_R_sub (i : Φ × Fin b × Fin a) :
    IsWB (bB orb ϖ S) (‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ)) (xPt ϖ c i -
      MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) -
        MvPowerSeries.C ϖ * ySer (cBase orb S c) i) := by
  have hℓ1 := hℓ.out.one_lt
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ1 hϖ
  have hG := isWeight_bG (b := b) (a := a) orb S
  have hBn := bB_nonneg (b := b) (a := a) orb S hϖ0
  set Y := MvPowerSeries.C ϖ * ySer c i with hYdef
  set Z := MvPowerSeries.C ϖ * ySer (cGain orb S c) i with hZdef
  set B := MvPowerSeries.C ϖ * ySer (cBase orb S c) i with hBdef
  have hYZ : Y = Z + B := by rw [hYdef, hZdef, hBdef, ← mul_add, ← ySer_split]
  have hY0 : MvPowerSeries.constantCoeff Y = 0 := by rw [hYdef, map_mul, constantCoeff_ySer, mul_zero]
  have hZ0 : MvPowerSeries.constantCoeff Z = 0 := by rw [hZdef, map_mul, constantCoeff_ySer, mul_zero]
  have hY := PowerSeries.HasSubst.of_constantCoeff_zero hY0
  have hZ := PowerSeries.HasSubst.of_constantCoeff_zero hZ0
  have e : xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) - B =
      (expLT ℂ_[ℓ] ℓ - PowerSeries.X).subst Y - (expLT ℂ_[ℓ] ℓ - PowerSeries.X).subst Z := by
    rw [PowerSeries.subst_sub hY, PowerSeries.subst_sub hZ, PowerSeries.subst_X hY, PowerSeries.subst_X hZ,
      hYdef, hZdef, expLT_subst_C_mul hℓ1 hϖ (constantCoeff_ySer _ i),
      expLT_subst_C_mul hℓ1 hϖ (constantCoeff_ySer _ i), xPt]
    rw [← hYdef, ← hZdef, hYZ]
    ring
  rw [e]
  refine isWB_psubst_sub hY0 hZ0 (fun κ => mul_nonneg (by positivity) (hBn κ)) fun N => ?_
  rw [map_sub, PowerSeries.coeff_X]
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hz : PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ) - (if N = 1 then 1 else 0) = 0 := by
      interval_cases N
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_expLT]; simp
      · rw [coeff_one_expLT]; simp
    rw [hz, map_zero, zero_mul]
    intro κ
    rw [map_zero, norm_zero]
    exact mul_nonneg (by positivity) (hBn κ)
  · rw [ite_eq_right (by omega), sub_zero, hYZ, add_pow, sum_range_succ, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right, mul_sum]
    refine isWB_sum _ (by positivity) hBn fun m hm => ?_
    have hm' : m < N := mem_range.1 hm
    have h1 : IsWB (bB orb ϖ S) (‖ϖ‖ ^ m * ‖((N - m).factorial : ℂ_[ℓ])‖) (Z ^ m * B ^ (N - m)) :=
      IsWB.mul' (bG_mul_bB_le orb S hϖ0) (by positivity) (norm_nonneg _) hBn
        ((isWB_aP orb S hc i).pow hG (norm_nonneg _) m)
        (isWB_bB_pow orb S hϖ0 (isWB_ySer_base orb S hϖ0 hc i) (by omega))
    have h2 := (h1.C_mul ((N.choose m : ℕ) : ℂ_[ℓ])).C_mul (PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ))
    rw [map_natCast] at h2
    have h3 := h2.mono hBn (norm_expLT_term_le hϖ hN hm')
    have e2 : MvPowerSeries.C (PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ)) * (Z ^ m * B ^ (N - m) *
        ((N.choose m : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])) =
        MvPowerSeries.C (PowerSeries.coeff N (expLT ℂ_[ℓ] ℓ)) *
          (((N.choose m : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) * (Z ^ m * B ^ (N - m))) := by ring
    rw [e2]
    exact h3

include hϖ hc in
/-- **The base part of a point** `R_i = X_i − A_i` is bounded by the base weight. -/
theorem isWB_R (i : Φ × Fin b × Fin a) :
    IsWB (bB orb ϖ S) 1 (xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) := by
  have hℓ1 := hℓ.out.one_lt
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ1 hϖ
  have hϖ1 := norm_le_one_of_pow_eq hℓ1 hϖ
  have e : xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) =
      MvPowerSeries.C ϖ * ySer (cBase orb S c) i + (xPt ϖ c i -
        MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) -
          MvPowerSeries.C ϖ * ySer (cBase orb S c) i) := by ring
  rw [e]
  exact (isWB_ySer_base orb S hϖ0 hc i).add ((isWB_R_sub orb hϖ S hc i).mono (bB_nonneg orb S hϖ0)
    (pow_le_one₀ (norm_nonneg _) hϖ1))

include hϖ hc in
/-- **The points are bounded by every split weight**: `X_i = A_i + R_i`. -/
theorem isWB_xPt (i : Φ × Fin b × Fin a) : IsWB (bS orb ϖ S) 1 (xPt ϖ c i) := by
  have hℓ1 := hℓ.out.one_lt
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ1 hϖ
  have hϖ1 := norm_le_one_of_pow_eq hℓ1 hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have e : xPt ϖ c i = MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) +
      (xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) := by ring
  rw [e]
  exact (((isWB_AP orb S hc i).weight_mono (bG_le_bS orb hϖ0 S) (norm_nonneg _)).mono hS.nonneg hϖ1).add
    ((isWB_R orb hϖ S hc i).weight_mono (bB_le_bS orb S hϖ0) zero_le_one)

end MixPts4

/-! ## Mixed integrality: the cross term between gain and base orbits -/

section Cross

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ℓ : ℕ} [hℓp : Fact ℓ.Prime]
  {P : Type} [Fintype P] [DecidableEq P] {a b : ℕ} {σ : Type}

omit [CharZero K] hℓp in
/-- **Contraction, one step at a time**: `E_n + E_{n+1} ≡ 0 (mod ℓ)` and `ord E_n ≥ n` give `E_0 ≡ 0`. -/
theorem isDivK_of_contract1 {E : ℕ → MvPowerSeries σ K} (hE : ∀ n, IsDivK ℓ (E n + E (n + 1)))
    (hvan : ∀ n (κ : σ →₀ ℕ), κ.degree < n → MvPowerSeries.coeff κ (E n) = 0) : IsDivK ℓ (E 0) := by
  intro κ
  have key : ∀ L, ‖MvPowerSeries.coeff κ (E 0) - (-1) ^ L * MvPowerSeries.coeff κ (E L)‖ ≤ ‖(ℓ : K)‖ := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      have e : MvPowerSeries.coeff κ (E 0) - (-1) ^ (L + 1) * MvPowerSeries.coeff κ (E (L + 1)) =
          (MvPowerSeries.coeff κ (E 0) - (-1) ^ L * MvPowerSeries.coeff κ (E L)) +
            (-1) ^ L * MvPowerSeries.coeff κ (E L + E (L + 1)) := by
        rw [map_add]
        ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hE L κ
  have h0 : MvPowerSeries.coeff κ (E (κ.degree + 1)) = 0 := hvan _ κ (Nat.lt_succ_self _)
  have := key (κ.degree + 1)
  rwa [h0, mul_zero, sub_zero] at this

omit [IsUltrametricDist K] [CharZero K] [Fintype P] in
/-- **The Frobenius of a variable** is its `ℓ`-th power. -/
theorem frobS_X (φ : K →+* K) (x : σ) : frobS ℓ φ (MvPowerSeries.X x : MvPowerSeries σ K) =
    MvPowerSeries.X x ^ ℓ := by
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ (MvPowerSeries.X x)) = _
  rw [MvPowerSeries.map_X, MvPowerSeries.expand_X]

omit [IsUltrametricDist K] [CharZero K] [DecidableEq P] in
/-- **Iterated Frobenius of a linear form**: `F^m(Σ_x d_x X_x) = Σ_x φ^m(d_x)·X_x^{ℓ^m}`. -/
theorem frobS_pow_ySer (φ : K →+* K) (d : P × Fin b × Fin a → P × Fin b × Fin a → K) (i : P × Fin b × Fin a)
    (m : ℕ) : (frobS ℓ φ ^ m) (ySer d i) =
      ∑ x, MvPowerSeries.C ((φ ^ m) (d i x)) * MvPowerSeries.X x ^ (ℓ ^ m) := by
  induction m with
  | zero => simp [ySer]
  | succ m ih =>
    rw [frobS_pow_succ, ih, map_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [map_mul, map_pow, frobS_C, frobS_X, ← pow_mul, pow_succ' ℓ m, pow_succ' φ m]
    rfl

/-- **The gain part of frame coefficients** over any field. -/
def cGainK {V : Type} [DecidableEq V] (orb : P → V) (S : Finset V)
    (c : P × Fin b × Fin a → P × Fin b × Fin a → K) (i x : P × Fin b × Fin a) : K :=
  if orb x.1 ∈ S then 0 else c i x

omit [IsUltrametricDist K] [CharZero K] hℓp [Fintype P] [DecidableEq P] in
/-- **The successor preserves orbits**, in any power. -/
theorem orb_sucV_pow {V : Type} {orb : P → V} {succ : Equiv.Perm P} (horb : ∀ τ, orb (succ τ) = orb τ) (n : ℕ)
    (x : P × Fin b × Fin a) : orb ((sucV succ ^ n) x).1 = orb x.1 := by
  rw [sucV_pow_apply]
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, horb, ih]

variable {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
  {succ : Equiv.Perm P} {c : (P × Fin b × Fin a) → (P × Fin b × Fin a) → K} {u : P × Fin b × Fin a → ℕ}
  (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : K) * c i x * (φ ^ (2 * k + 1)) (c i y) =
      if x = (sucV succ ^ (2 * k + 1)) y then 1 else 0)
  (hc : ∀ i x, ‖c i x‖ ≤ 1) {V : Type} [DecidableEq V] (orb : P → V) (horb : ∀ τ, orb (succ τ) = orb τ)
  (S : Finset V)
include hφ hTp hc horb

/-- **The cross term vanishes mod `ℓ`**: for a base variable `q`, `Σ_i u_i c_{iq}·λ(a_i)^ℓ ≡ 0`, `a_i` the gain
coordinates (contraction along odd Frobenius powers; `Σ_i u_i c_{iq}φ^{2n+1}(c_{ix}) = [q = succ^{2n+1}x] = 0`
for `x` in another orbit). -/
theorem isDivK_cross {q : P × Fin b × Fin a} (hq : orb q.1 ∈ S) :
    IsDivK ℓ (∑ i, MvPowerSeries.C ((u i : K) * c i q) * ((lamK K ℓ).subst (ySer (cGainK orb S c) i)) ^ ℓ) := by
  have hcG : ∀ i x, ‖cGainK orb S c i x‖ ≤ 1 := fun i x => by
    unfold cGainK; split_ifs
    · rw [norm_zero]; exact zero_le_one
    · exact hc i x
  have hy : ∀ i, IsIntK (ySer (cGainK orb S c) i) := isIntK_ySer hcG
  have hy0 : ∀ i, MvPowerSeries.constantCoeff (ySer (cGainK orb S c) i) = 0 := constantCoeff_ySer _
  have hYi : ∀ m i, IsIntK ((frobS ℓ φ ^ m) (ySer (cGainK orb S c) i)) := fun m i => isIntK_frobS_pow hφ (hy i) m
  have hY0 : ∀ m i, MvPowerSeries.constantCoeff ((frobS ℓ φ ^ m) (ySer (cGainK orb S c) i)) = 0 := fun m i =>
    constantCoeff_frobS_pow φ (hy0 i) m
  have hu : ∀ i, ‖(u i : K) * c i q‖ ≤ 1 := fun i => by
    rw [norm_mul]; exact mul_le_one_of (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _) (hc i q)
  -- the odd Frobenius images of the gain coordinates are killed
  have hzero : ∀ n, ∑ i, MvPowerSeries.C ((u i : K) * c i q) *
      (frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i) = 0 := by
    intro n
    simp only [frobS_pow_ySer, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun x _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← sum_mul, ← map_sum]
    convert zero_mul _
    convert map_zero (MvPowerSeries.C (σ := P × Fin b × Fin a) (R := K))
    unfold cGainK
    by_cases hx : orb x.1 ∈ S
    · simp [hx]
    · simp only [hx, ite_false]
      rw [hTp n q x, ite_eq_right]
      intro h
      exact hx (by rw [← orb_sucV_pow horb (2 * n + 1) x, ← h]; exact hq)
  set E : ℕ → MvPowerSeries (P × Fin b × Fin a) K := fun n => ∑ i, MvPowerSeries.C ((u i : K) * c i q) *
    (lamK K ℓ).subst ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i)) with hE
  have hE0 : IsDivK ℓ (E 0) := by
    refine isDivK_of_contract1 (fun n => ?_) (fun n κ hκ => ?_)
    · have e : E n + E (n + 1) = ∑ i, MvPowerSeries.C ((u i : K) * c i q) *
          (((lamK K ℓ).subst ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i)) +
            ((lamK K ℓ).subst ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i))) ^ (ℓ ^ 2) -
              (frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i)) -
          (((lamK K ℓ).subst ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i))) ^ (ℓ ^ 2) -
            (lamK K ℓ).subst (frobS ℓ φ (frobS ℓ φ ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i)))))) +
          ∑ i, MvPowerSeries.C ((u i : K) * c i q) * (frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i) := by
        rw [hE]
        dsimp only
        rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]
        simp only [frobS_pow_add_two]
        rw [← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
      rw [e, hzero n, add_zero]
      refine IsDivK.sum _ fun i _ => (IsDivK.sub ?_ ?_).isInt_mul (isIntK_C (hu i))
      · exact isDivK_lamK_subst_add_pow (hYi _ i) (hY0 _ i)
      · exact isDivK_lamK_pow_sq_sub_frob hφ (hYi _ i) (hY0 _ i)
    · rw [hE]
      dsimp only
      rw [map_sum]
      refine sum_eq_zero fun i _ => ?_
      rw [MvPowerSeries.coeff_C_mul]
      convert mul_zero _
      refine MvPowerSeries.coeff_of_lt_order ?_
      have h1 : n < ℓ ^ (2 * n + 1) :=
        (lt_pow_two_mul hℓp.out.two_le n).trans_le (Nat.pow_le_pow_right hℓp.out.pos (by omega))
      calc (κ.degree : ℕ∞) < ((ℓ ^ (2 * n + 1) : ℕ) : ℕ∞) := by exact_mod_cast hκ.trans h1
        _ ≤ ((frobS ℓ φ ^ (2 * n + 1)) (ySer (cGainK orb S c) i)).order := le_order_frobS_pow φ (hy0 i) _
        _ ≤ _ := PowerSeries.le_order_subst_right (hY0 _ i) (constantCoeff_lamK K ℓ)
  have e : ∑ i, MvPowerSeries.C ((u i : K) * c i q) * ((lamK K ℓ).subst (ySer (cGainK orb S c) i)) ^ ℓ =
      ∑ i, MvPowerSeries.C ((u i : K) * c i q) * (((lamK K ℓ).subst (ySer (cGainK orb S c) i)) ^ ℓ -
        (lamK K ℓ).subst (frobS ℓ φ (ySer (cGainK orb S c) i))) + E 0 := by
    rw [hE]
    dsimp only
    rw [mul_zero, zero_add, pow_one, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  exact (IsDivK.sum _ fun i _ => (isDivK_lamK_pow_sub_frob hφ (hy i) (hy0 i)).isInt_mul (isIntK_C (hu i))).add hE0

end Cross

/-! ## Mixed integrality: the position form and the cross term over `ℂ_ℓ` -/

section MixPos

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)

omit [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V] in
/-- **Orbits are stable under the inverse powers of the successor.** -/
theorem orb_pow_symm {succ : Equiv.Perm Φ} (horb : ∀ τ, orb (succ τ) = orb τ) (n : ℕ) (s : Φ) :
    orb ((succ ^ n).symm s) = orb s := by
  have h : ∀ τ, orb ((succ ^ n) τ) = orb τ := fun τ => by
    induction n generalizing τ with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, horb, ih]
  rw [← h ((succ ^ n).symm s), Equiv.apply_symm_apply]

omit [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V] in
include hϖ in
/-- **`‖(ℓⁿ)!‖·‖ϖ‖ ≤ ‖ϖ‖^{ℓⁿ}`.** -/
theorem norm_factorial_pow_mul_le (n : ℕ) :
    ‖((ℓ ^ n).factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ≤ ‖ϖ‖ ^ (ℓ ^ n) := by
  have h2 := hℓ.out.two_le
  have hϖ1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle : ℓ ^ n ≤ (ℓ ^ 2 - 1) * (ℓ ^ n / ℓ) + 1 := by
    rcases n with _ | n
    · simp
    · rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
      have : ℓ ≤ ℓ ^ 2 - 1 := by
        have : ℓ * 2 ≤ ℓ * ℓ := Nat.mul_le_mul_left _ h2
        rw [sq]; omega
      nlinarith [Nat.mul_le_mul_left (ℓ ^ n) this]
  calc ‖((ℓ ^ n).factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ≤ ‖ϖ‖ ^ ((ℓ ^ 2 - 1) * (ℓ ^ n / ℓ)) * ‖ϖ‖ := by
        gcongr
        rw [pow_mul, ← norm_ell_eq hϖ]
        exact norm_factorial_le _
    _ = ‖ϖ‖ ^ ((ℓ ^ 2 - 1) * (ℓ ^ n / ℓ) + 1) := (pow_succ _ _).symm
    _ ≤ ‖ϖ‖ ^ (ℓ ^ n) := pow_le_pow_of_le_one hϖ0 hϖ1 hle

omit [Fintype Φ] in
/-- **A gain twisted series is pure gain and integral.** -/
theorem isWB_twSer_gain {succ : Equiv.Perm Φ} (horb : ∀ τ, orb (succ τ) = orb τ) {x : Φ × Fin b × Fin a}
    (hx : orb x.1 ∉ S) : IsWB (bG orb S) 1 (twSer (ℓ := ℓ) succ x) := fun μ => by
  change ‖∑ l ∈ range (deg μ + 1), _‖ ≤ _
  rw [one_mul]
  have hb : 0 ≤ bG orb S μ := (isWeight_bG orb S).nonneg μ
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun l _ => ?_
  split_ifs with h
  · rw [h, bG, ite_eq_left (pure_single orb S (by rw [orb_pow_symm orb horb]; exact hx) _), norm_pow, norm_neg,
      norm_one, one_pow]
  · rw [norm_zero]; exact hb

include hϖ in
/-- **A base twisted series times `ϖ` is bounded by the base weight** (`‖(ℓ^{2l})!‖·‖ϖ‖ ≤ ‖ϖ‖^{ℓ^{2l}}`). -/
theorem isWB_twSer_base {succ : Equiv.Perm Φ} (horb : ∀ τ, orb (succ τ) = orb τ) {x : Φ × Fin b × Fin a}
    (hx : orb x.1 ∈ S) : IsWB (bB orb ϖ S) 1 (MvPowerSeries.C ϖ * twSer (ℓ := ℓ) succ x) := fun μ => by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  rw [MvPowerSeries.coeff_C_mul, one_mul]
  change ‖ϖ * ∑ l ∈ range (deg μ + 1), _‖ ≤ _
  rw [mul_sum]
  have hb : 0 ≤ bB orb ϖ S μ := bB_nonneg orb S hϖ0 μ
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun l _ => ?_
  split_ifs with h
  · have hy : orb ((succ ^ (2 * l)).symm x.1, x.2).1 ∈ S := by rw [orb_pow_symm orb horb]; exact hx
    rw [h, show bB orb ϖ S _ = bS orb ϖ S _ from ite_eq_right (not_pure_single orb S hy (pow_ne_zero _ hℓ.out.ne_zero)),
      bS_single orb S hy, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      le_div_iff₀ (norm_natCast_pos (Nat.factorial_ne_zero _)), mul_comm, pow_mul]
    have := norm_factorial_pow_mul_le hϖ (2 * l)
    rwa [pow_mul] at this
  · rw [mul_zero, norm_zero]; exact hb

end MixPos

/-! ## Mixed integrality: the pieces of the Gaussian exponent -/

section MixG

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)

include hϖ hc in
/-- **The binomial terms of a point**: `A_i^m·R_i^{M−m}·C(M, m)` with `A_i` the gain point and `R_i = X_i − A_i`. -/
theorem isWB_binom_term (i : Φ × Fin b × Fin a) (M m : ℕ) :
    IsWB (bS orb ϖ S) (‖((M.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((M - m).factorial : ℂ_[ℓ])‖))
      ((MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) ^ m *
        (xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) ^ (M - m) *
          ((M.choose m : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have h1 := (((isWB_AP orb (ϖ := ϖ) S hc i).weight_mono (bG_le_bS orb hϖ0 S) (norm_nonneg _)).pow hS
    (norm_nonneg _) m).mul
    hS (norm_nonneg _) (isWB_pow_of_dp hS (dPc_of_isWB_bB orb S hϖ0 (isWB_R orb hϖ S hc i)) (M - m))
  have h2 := h1.C_mul ((M.choose m : ℕ) : ℂ_[ℓ])
  rw [map_natCast] at h2
  rw [mul_comm _ ((M.choose m : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])]
  exact h2

omit [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V] in
include hϖ in
/-- **The small terms of `serAB` against the binomial terms**: `‖f_n‖·‖C(M, m)‖·‖ϖ‖^m·‖(M−m)!‖ ≤ 1` for
`f = serAB − serAB0`, `M = n₀ + n₁`. -/
theorem norm_serAB_binom_le (h3 : 3 ≤ ℓ) (n : Fin 2 →₀ ℕ) {m : ℕ} (hm : m ≤ n 0 + n 1) :
    ‖MvPowerSeries.coeff n (serAB ℓ - serAB0 ℓ)‖ * (‖(((n 0 + n 1).choose m : ℕ) : ℂ_[ℓ])‖ *
      (‖ϖ‖ ^ m * ‖((n 0 + n 1 - m).factorial : ℂ_[ℓ])‖)) ≤ 1 := by
  classical
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  set M := n 0 + n 1
  -- `‖C(M,m)‖·‖ϖ‖^m·‖(M−m)!‖·‖ϖ‖^{ℓ−1} ≤ ‖ϖ‖^M`
  have hB : ‖((M.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((M - m).factorial : ℂ_[ℓ])‖) * ‖ϖ‖ ^ (ℓ - 1) ≤
      ‖ϖ‖ ^ M := by
    have hf := norm_factorial_mul_le hϖ (M - m)
    calc ‖((M.choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((M - m).factorial : ℂ_[ℓ])‖) * ‖ϖ‖ ^ (ℓ - 1)
        ≤ 1 * (‖ϖ‖ ^ m * (‖((M - m).factorial : ℂ_[ℓ])‖ * ‖ϖ‖ ^ (ℓ - 1))) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one _ _) (by positivity)
      _ ≤ 1 * (‖ϖ‖ ^ m * ‖ϖ‖ ^ (M - m)) := by gcongr
      _ = ‖ϖ‖ ^ M := by rw [one_mul, ← pow_add, Nat.add_sub_cancel' hm]
  rw [map_sub, coeff_serAB0]
  by_cases h : ∃ i j, SupAB ℓ (n 0) (n 1) i j
  · obtain ⟨i, j, hij⟩ := h
    rw [coeff_serAB_of hij]
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [ite_eq_left hij, zero_add, zero_add, pow_one, sub_self, norm_zero, zero_mul]
      exact zero_le_one
    · have hn0 : ¬ SupAB ℓ (n 0) (n 1) 0 0 := fun h' => h00 (supAB_unique hij h')
      rw [ite_eq_right hn0, sub_zero]
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd ⟨Nat.le_zero.1 hij.1, rfl⟩ h00
        · exact hj
      have hle : ℓ + 1 + (ℓ ^ 2 - 1) * (i + j + 1) ≤ M := by
        have h1 := exp_small_le h3 hj
        have h2 : 1 ≤ ℓ ^ (2 * i) := Nat.one_le_pow _ _ (by omega)
        have h4 : (ℓ ^ 2 - 1) * (i + j + 1) ≤ (ℓ ^ 2 - 1) * (2 * j + 1) :=
          Nat.mul_le_mul_left _ (by have := hij.1; omega)
        have hM : M = ℓ ^ (2 * i) + ℓ ^ (2 * j + 1) := by
          rcases hij.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        omega
      have key : ‖((ℓ : ℂ_[ℓ]) ^ (i + j + 1))⁻¹‖ * (‖((M.choose m : ℕ) : ℂ_[ℓ])‖ *
          (‖ϖ‖ ^ m * ‖((M - m).factorial : ℂ_[ℓ])‖)) * ‖ϖ‖ ^ (ℓ - 1) ≤ 1 * ‖ϖ‖ ^ (ℓ - 1) := by
        rw [mul_assoc, norm_inv, norm_pow, norm_ell_eq hϖ, ← pow_mul, inv_mul_le_iff₀ (by positivity)]
        calc _ ≤ ‖ϖ‖ ^ M := hB
          _ ≤ ‖ϖ‖ ^ ((ℓ ^ 2 - 1) * (i + j + 1) + (ℓ - 1)) := pow_le_pow_of_le_one hp.le hϖ1 (by omega)
          _ = _ := by rw [pow_add, one_mul]
      exact le_of_mul_le_mul_right key (pow_pos hp _)
  · push Not at h
    rw [coeff_serAB_of_not h, ite_eq_right (h 0 0), sub_zero, norm_zero, zero_mul]
    exact zero_le_one

include hϖ hc in
/-- **The small terms of the Gaussian at a point** are bounded by every split weight:
`(serAB − serAB0)(X_i, X_i)` (`X_i = A_i + R_i`, binomial expansion). -/
theorem isWB_serAB_sub (h3 : 3 ≤ ℓ) (i : Φ × Fin b × Fin a) :
    IsWB (bS orb ϖ S) 1 (MvPowerSeries.subst ![xPt ϖ c i, xPt ϖ c i] (serAB ℓ - serAB0 ℓ)) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have hX0 := constantCoeff_xPt (ℓ := ℓ) ϖ c i
  refine isWB_subst (hasSubst_pair hX0 hX0) (fun κ => by rw [one_mul]; exact hS.nonneg κ) fun d => ?_
  have e : (d.prod fun s e => (![xPt ϖ c i, xPt ϖ c i] s) ^ e) = xPt ϖ c i ^ (d 0 + d 1) := by
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, pow_add]
    rfl
  rw [e]
  set A := MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)
  rw [show xPt ϖ c i = A + (xPt ϖ c i - A) by ring, add_pow, mul_sum]
  refine isWB_sum _ zero_le_one hS.nonneg fun m hm => ?_
  have hm' : m ≤ d 0 + d 1 := Nat.lt_succ_iff.1 (mem_range.1 hm)
  have h := (isWB_binom_term orb hϖ S hc i (d 0 + d 1) m).C_mul (MvPowerSeries.coeff d (serAB ℓ - serAB0 ℓ))
  exact h.mono hS.nonneg (norm_serAB_binom_le hϖ h3 d hm')

end MixG


section MixG2

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ]} (hc : ∀ i x, ‖c i x‖ ≤ 1)

/-- **`ℓ ∣ C(ℓ+1, m)·(ℓ+1−m)!`** for `m < ℓ` (the product is `(ℓ+1)!/m!`). -/
theorem ell_dvd_choose_mul {m : ℕ} (hm : m < ℓ) : ℓ ∣ (ℓ + 1).choose m * (ℓ + 1 - m).factorial := by
  have hp := hℓ.out
  have e := Nat.choose_mul_factorial_mul_factorial (show m ≤ ℓ + 1 by omega)
  have h1 : ℓ ∣ (ℓ + 1).factorial := Nat.dvd_factorial hp.pos (by omega)
  rw [← e, mul_assoc, mul_comm (m.factorial), ← mul_assoc] at h1
  exact (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2
    fun h => by have := (Nat.Prime.dvd_factorial hp).1 h; omega) h1)

include hϖ hc in
/-- **The leading Gaussian term minus its gain and linear parts**:
`X^{ℓ+1} − A^{ℓ+1} − (ℓ+1)A^ℓ(X − A) = Σ_{m<ℓ} C(ℓ+1, m)A^mR^{ℓ+1−m}` is `ℓ`-small in every split weight. -/
theorem isWB_lead_rest (i : Φ × Fin b × Fin a) :
    IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ (xPt ϖ c i ^ (ℓ + 1) -
      (MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) ^ (ℓ + 1) -
        ((ℓ + 1 : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) *
          (MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) ^ ℓ *
            (xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i))) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  set A := MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)
  set R := xPt ϖ c i - A
  have e : xPt ϖ c i ^ (ℓ + 1) - A ^ (ℓ + 1) - ((ℓ + 1 : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) * A ^ ℓ * R =
      ∑ m ∈ range ℓ, A ^ m * R ^ (ℓ + 1 - m) * (((ℓ + 1).choose m : ℕ) : MvPowerSeries _ ℂ_[ℓ]) := by
    rw [show xPt ϖ c i = A + R by ring, add_pow, sum_range_succ, sum_range_succ, Nat.choose_self,
      Nat.choose_succ_self_right, Nat.sub_self, show ℓ + 1 - ℓ = 1 by omega]
    push_cast
    ring
  rw [e]
  refine isWB_sum _ (norm_nonneg _) hS.nonneg fun m hm => ?_
  have hm' : m < ℓ := mem_range.1 hm
  refine (isWB_binom_term orb hϖ S hc i (ℓ + 1) m).mono hS.nonneg ?_
  have hd := norm_natCast_le_of_dvd' (ℓ := ℓ) (ell_dvd_choose_mul hm')
  rw [Nat.cast_mul, norm_mul] at hd
  calc ‖(((ℓ + 1).choose m : ℕ) : ℂ_[ℓ])‖ * (‖ϖ‖ ^ m * ‖((ℓ + 1 - m).factorial : ℂ_[ℓ])‖)
      ≤ ‖(((ℓ + 1).choose m : ℕ) : ℂ_[ℓ])‖ * (1 * ‖((ℓ + 1 - m).factorial : ℂ_[ℓ])‖) := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hϖ1
    _ ≤ _ := by rw [one_mul]; exact hd

include hϖ hc in
/-- **The gain-times-higher-base term** `A^ℓ·(X − A − ϖb)` has size `‖ℓ‖` in the base weight. -/
theorem isWB_gain_rem (i : Φ × Fin b × Fin a) :
    IsWB (bB orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ ((MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) ^ ℓ *
      (xPt ϖ c i - MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i) -
        MvPowerSeries.C ϖ * ySer (cBase orb S c) i)) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have h := IsWB.mul' (bG_mul_bB_le orb S hϖ0) (by positivity) (by positivity) (bB_nonneg orb S hϖ0)
    ((isWB_AP orb (ϖ := ϖ) S hc i).pow (isWeight_bG orb S) (norm_nonneg _) ℓ) (isWB_R_sub orb hϖ S hc i)
  have e : ‖ϖ‖ ^ ℓ * ‖ϖ‖ ^ (ℓ ^ 2 - 1 - ℓ) = ‖(ℓ : ℂ_[ℓ])‖ := by
    rw [← pow_add, norm_ell_eq hϖ]
    congr 1
    have h2 := hℓ.out.two_le
    have : ℓ ≤ ℓ ^ 2 - 1 := by
      have : ℓ * 2 ≤ ℓ * ℓ := Nat.mul_le_mul_left _ h2
      rw [sq]; omega
    omega
  rwa [e] at h

include hc in
/-- **`λ` of the gain coordinates** is pure gain and integral. -/
theorem isWB_lam_gain (i : Φ × Fin b × Fin a) :
    IsWB (bG orb S) 1 ((lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S c) i)) := by
  have hG := isWeight_bG (b := b) (a := a) orb S
  have hy := isWB_ySer_gain orb S hc i
  exact isWB_psubst (constantCoeff_ySer _ i) (fun κ => by rw [one_mul]; exact hG.nonneg κ) fun N => by
    refine ((hy.pow hG zero_le_one N).C_mul _).mono hG.nonneg ?_
    rw [one_pow, mul_one]
    exact isInt_lamK ℂ_[ℓ] ℓ N

omit [Fintype Φ] in
/-- **A pure gain, `ℓ`-divisible series** has size `‖ℓ‖` in the gain weight. -/
theorem isWB_bG_of_isDivK {f : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]} (h1 : IsWB (bG orb S) 1 f)
    (h2 : IsDivK ℓ f) : IsWB (bG orb S) ‖(ℓ : ℂ_[ℓ])‖ f := fun κ => by
  have h := h1 κ
  unfold bG at h ⊢
  split_ifs at h ⊢
  · rw [mul_one]; exact h2 κ
  · rw [mul_zero] at h ⊢; exact h

include hϖ in
/-- **A base twisted pair** `ϖ^{ℓ+1}·tw(x)^ℓ·tw(succ x)` has size `‖ℓ‖` in every split weight. -/
theorem isWB_pos_base {succ : Equiv.Perm Φ} (horb : ∀ τ, orb (succ τ) = orb τ) {x : Φ × Fin b × Fin a}
    (hx : orb x.1 ∈ S) : IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖
      (MvPowerSeries.C (ϖ ^ (ℓ + 1)) * (twSer (ℓ := ℓ) succ x ^ ℓ * twSer succ (succ x.1, x.2))) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have hx' : orb (succ x.1, x.2).1 ∈ S := by rw [horb]; exact hx
  have h := IsWB.mul' (bB_mul_bS_le orb S hϖ0) (norm_nonneg _) zero_le_one (bB_nonneg orb S hϖ0)
    (isWB_bB_pow orb S hϖ0 (isWB_twSer_base orb hϖ S horb hx) hℓ.out.one_le)
    ((isWB_twSer_base orb hϖ S horb hx').weight_mono (bB_le_bS orb S hϖ0) zero_le_one)
  have e : MvPowerSeries.C (ϖ ^ (ℓ + 1)) * (twSer (ℓ := ℓ) succ x ^ ℓ * twSer succ (succ x.1, x.2)) =
      (MvPowerSeries.C ϖ * twSer succ x) ^ ℓ * (MvPowerSeries.C ϖ * twSer succ (succ x.1, x.2)) := by
    rw [map_pow, pow_succ, mul_pow]
    ring
  rw [e]
  refine (h.weight_mono (bB_le_bS orb S hϖ0) (by positivity)).mono hS.nonneg ?_
  rw [mul_one]
  exact norm_natCast_le_of_dvd' (Nat.dvd_factorial hℓ.out.pos le_rfl)

end MixG2


section MixCross

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {succ : Equiv.Perm Φ} {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ} {u : Φ × Fin b × Fin a → ℕ}
  (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
  (hc : ∀ i x, ‖c i x‖ ≤ 1) (horb : ∀ τ, orb (succ τ) = orb τ)

include hTp hc horb in
/-- **The cross series over `ℂ_ℓ`**: for a base variable `q`, `Σ_i u_i c_{iq}·λ(a_i)^ℓ` is pure gain and
`ℓ`-divisible (`isDivK_cross` over `K^ur`). -/
theorem isWB_cross_C {q : Φ × Fin b × Fin a} (hq : orb q.1 ∈ S) :
    IsWB (bG orb S) ‖(ℓ : ℂ_[ℓ])‖ (∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (c i q : ℂ_[ℓ])) *
      ((lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S fun i x => (c i x : ℂ_[ℓ])) i)) ^ ℓ) := by
  have hG := isWeight_bG (b := b) (a := a) orb S
  have hcc : ∀ i x, ‖((c i x : unramC ℓ) : ℂ_[ℓ])‖ ≤ 1 := hc
  have hm := isDivK_map_unramC (isDivK_cross (K := unramC ℓ) UnramFrobLift.norm_frobUnram_sub_pow_le hTp hc orb
    horb S hq)
  have e : (fun i x => (unramC ℓ).subtype (cGainK orb S c i x)) = cGain orb S fun i x => (c i x : ℂ_[ℓ]) := by
    funext i x
    unfold cGainK cGain
    split_ifs <;> simp
  refine isWB_bG_of_isDivK orb S ?_ ?_
  · refine isWB_sum _ zero_le_one hG.nonneg fun i _ => ?_
    have h := ((isWB_lam_gain orb S hcc i).pow hG zero_le_one ℓ).C_mul ((u i : ℂ_[ℓ]) * (c i q : ℂ_[ℓ]))
    refine h.mono hG.nonneg ?_
    rw [one_pow, mul_one, norm_mul]
    exact mul_le_one_of (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _) (hc i q)
  · convert hm using 1
    rw [map_sum]
    refine sum_congr rfl fun i _ => ?_
    symm
    rw [map_mul, map_pow, MvPowerSeries.map_C, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_ySer _ i)), map_lamK, map_ySer, e]
    congr 2

/-- **`ϖ·Z_q` for a base variable** is bounded by the base weight. -/
theorem isWB_X_base (hϖ0 : ϖ ≠ 0) {q : Φ × Fin b × Fin a} (hq : orb q.1 ∈ S) :
    IsWB (bB orb ϖ S) 1 (MvPowerSeries.C ϖ * (MvPowerSeries.X q : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])) :=
  fun μ => by
  classical
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, one_mul]
  split_ifs with h
  · rw [h, mul_one, show bB orb ϖ S _ = bS orb ϖ S _ from ite_eq_right (not_pure_single orb S hq one_ne_zero),
      bS_single orb S hq, pow_one, Nat.factorial_one, Nat.cast_one, norm_one, div_one]
  · rw [mul_zero, norm_zero]
    exact bB_nonneg orb S hϖ0 μ

include hϖ hTp hc horb in
/-- **The cross term** `Σ_i u_i·A_i^ℓ·ϖb_i = ϖ^ℓ·Σ_q ϖZ_q·Σ_i u_i c_{iq}λ(a_i)^ℓ` is `ℓ`-small in every split
weight (`isWB_cross_C`). -/
theorem isWB_cross_term :
    IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ (∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) *
      (MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S fun i x => (c i x : ℂ_[ℓ])) i)) ^ ℓ *
        (MvPowerSeries.C ϖ * ySer (cBase orb S fun i x => (c i x : ℂ_[ℓ])) i)) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  set cc : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ] := fun i x => (c i x : ℂ_[ℓ])
  set L : Φ × Fin b × Fin a → MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] := fun i =>
    (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S cc) i)
  have e : ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * (MvPowerSeries.C ϖ * L i) ^ ℓ *
      (MvPowerSeries.C ϖ * ySer (cBase orb S cc) i) = ∑ q, MvPowerSeries.C (ϖ ^ ℓ) *
        ((∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * cBase orb S cc i q) * L i ^ ℓ) *
          (MvPowerSeries.C ϖ * MvPowerSeries.X q)) := by
    simp only [ySer, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [e]
  refine isWB_sum _ (norm_nonneg _) hS.nonneg fun q _ => ?_
  by_cases hq : orb q.1 ∈ S
  · have hT : (∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * cBase orb S cc i q) * L i ^ ℓ) =
        ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (c i q : ℂ_[ℓ])) * L i ^ ℓ := by
      refine sum_congr rfl fun i _ => ?_
      rw [cBase, ite_eq_left hq]
    rw [hT]
    have h1 : IsWB (bG orb S) ‖(ℓ : ℂ_[ℓ])‖ (∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (c i q : ℂ_[ℓ])) * L i ^ ℓ) :=
      isWB_cross_C orb S hTp hc horb hq
    have h2 : IsWB (bB orb ϖ S) 1 (MvPowerSeries.C ϖ * (MvPowerSeries.X q : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])) :=
      isWB_X_base orb S hϖ0 hq
    have h := (IsWB.mul' (bG_mul_bB_le orb S hϖ0) (norm_nonneg _) zero_le_one (bB_nonneg orb S hϖ0) h1 h2).C_mul
      (ϖ ^ ℓ)
    refine (h.weight_mono (bB_le_bS orb S hϖ0) (by positivity)).mono hS.nonneg ?_
    rw [mul_one, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hϖ1)
  · have hT : (∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * cBase orb S cc i q) * L i ^ ℓ) = 0 :=
      sum_eq_zero fun i _ => by rw [cBase, ite_eq_right hq, mul_zero, map_zero, zero_mul]
    rw [hT, zero_mul, mul_zero]
    intro κ
    rw [map_zero, norm_zero]
    exact mul_nonneg (norm_nonneg _) (hS.nonneg κ)

end MixCross

/-! ## Mixed integrality of the remainder -/

section MixFinal

open ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ} (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {succ : Equiv.Perm Φ} {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ} {u : Φ × Fin b × Fin a → ℕ}
  (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
  (hc : ∀ i x, ‖c i x‖ ≤ 1) (horb : ∀ τ, orb (succ τ) = orb τ)

include hϖ hTp hc horb in
/-- **The Gaussian exponent remainder at base exponents**: for `κ` with a part in the base orbits `S`,
`‖G_κ‖ ≤ bS(κ)`. `G = G₁ + (γ/ℓ)(T₁ + (ℓ+1)T₂ + (ℓ+1)T₃ − P_B) + (γ/ℓ)(Σ_i u_iA_i^{ℓ+1} − P_G)`: the small terms
of `serAB` (`isWB_serAB_sub`), the binomial rest (`isWB_lead_rest`), the gain-times-higher-base term
(`isWB_gain_rem`), the cross term (`isWB_cross_term`), the base position form (`isWB_pos_base`), and a pure gain
part, which does not meet base exponents. -/
theorem norm_coeff_gRem_base (h5 : 5 ≤ ℓ) {γ : ℂ_[ℓ]} (hγ : ‖γ‖ ≤ 1) {κ : Φ × Fin b × Fin a →₀ ℕ}
    (hκ : ¬ ∀ v ∈ S, resV orb v κ = 0) :
    ‖MvPowerSeries.coeff κ (gRem ϖ γ succ (fun i x => (c i x : ℂ_[ℓ])) u)‖ ≤ bS orb ϖ S κ := by
  have h3 : 3 ≤ ℓ := by omega
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hϖ1 : ‖ϖ‖ ≤ 1 := norm_le_one_of_pow_eq hℓ.out.one_lt hϖ
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  have hℓn : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 hℓ0
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have hG := isWeight_bG (b := b) (a := a) orb S
  set cc : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ_[ℓ] := fun i x => (c i x : ℂ_[ℓ])
  have hcc : ∀ i x, ‖cc i x‖ ≤ 1 := hc
  set X := xPt ϖ cc with hXdef
  set A : Φ × Fin b × Fin a → MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] := fun i =>
    MvPowerSeries.C ϖ * (lamK ℂ_[ℓ] ℓ).subst (ySer (cGain orb S cc) i) with hAdef
  set Bp : Φ × Fin b × Fin a → MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] := fun i =>
    MvPowerSeries.C ϖ * ySer (cBase orb S cc) i with hBdef
  set L1 : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ] := ((ℓ + 1 : ℕ) : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ])
  set G1 := ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.subst ![X i, X i] (serAB ℓ - serAB0 ℓ)
  set T1 := ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * (X i ^ (ℓ + 1) - A i ^ (ℓ + 1) - L1 * A i ^ ℓ * (X i - A i))
  set T2 := ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * (A i ^ ℓ * (X i - A i - Bp i))
  set T3 := ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * A i ^ ℓ * Bp i
  set GA := ∑ i, MvPowerSeries.C (u i : ℂ_[ℓ]) * A i ^ (ℓ + 1)
  set PB := ∑ x ∈ univ.filter (fun x : Φ × Fin b × Fin a => orb x.1 ∈ S), MvPowerSeries.C (ϖ ^ (ℓ + 1)) *
    (twSer (ℓ := ℓ) succ x ^ ℓ * twSer succ (succ x.1, x.2))
  set PG := ∑ x ∈ univ.filter (fun x : Φ × Fin b × Fin a => orb x.1 ∉ S), MvPowerSeries.C (ϖ ^ (ℓ + 1)) *
    (twSer (ℓ := ℓ) succ x ^ ℓ * twSer succ (succ x.1, x.2))
  -- the decomposition
  have hXs : MvPowerSeries.HasSubst X := hasSubst_xPt ϖ cc
  have hX0 : ∀ i, MvPowerSeries.constantCoeff (X i) = 0 := constantCoeff_xPt ϖ cc
  have hΨ : MvPowerSeries.subst X (gaussPsi γ u) =
      ∑ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.subst ![X i, X i] (serAB ℓ) := by
    rw [gaussPsi, ← MvPowerSeries.coe_substAlgHom hXs, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hXs, MvPowerSeries.subst_mul hXs, MvPowerSeries.subst_C,
      subst_pair_X _ _ hXs]
  have key : ∀ i, MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.subst ![X i, X i] (serAB ℓ) =
      MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.subst ![X i, X i] (serAB ℓ - serAB0 ℓ) +
        MvPowerSeries.C (γ / ℓ) * (MvPowerSeries.C (u i : ℂ_[ℓ]) * (X i ^ (ℓ + 1) - A i ^ (ℓ + 1) -
          L1 * A i ^ ℓ * (X i - A i)) + L1 * (MvPowerSeries.C (u i : ℂ_[ℓ]) * (A i ^ ℓ * (X i - A i - Bp i))) +
            L1 * (MvPowerSeries.C (u i : ℂ_[ℓ]) * A i ^ ℓ * Bp i) + MvPowerSeries.C (u i : ℂ_[ℓ]) * A i ^ (ℓ + 1)) := by
    intro i
    have hs := hasSubst_pair (hX0 i) (hX0 i)
    have hsc : (MvPowerSeries.C ((u i : ℂ_[ℓ]) * (γ / 2)) * MvPowerSeries.C (2 / (ℓ : ℂ_[ℓ])) :
        MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]) = MvPowerSeries.C (γ / ℓ) * MvPowerSeries.C (u i : ℂ_[ℓ]) := by
      rw [← map_mul, ← map_mul]
      congr 1
      field_simp
    have h1 : MvPowerSeries.subst ![X i, X i] (serAB ℓ) = MvPowerSeries.subst ![X i, X i] (serAB ℓ - serAB0 ℓ) +
        MvPowerSeries.C (2 / (ℓ : ℂ_[ℓ])) * X i ^ (ℓ + 1) := by
      rw [← subst_pair_serAB0 (hX0 i), ← MvPowerSeries.coe_substAlgHom hs, ← map_add, sub_add_cancel]
    rw [h1, mul_add, ← mul_assoc, hsc]
    ring
  have hpos : MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ * γ) * posForm (a := a) (b := b) succ (fun _ => (1 : ℂ_[ℓ])) =
      MvPowerSeries.C (γ / ℓ) * (PB + PG) := by
    rw [posForm, sum_filter_add_sum_filter_not, mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [map_one, one_mul, ← mul_assoc (MvPowerSeries.C (γ / ℓ)) (MvPowerSeries.C (ϖ ^ (ℓ + 1))), ← map_mul]
    congr 2
    field_simp
  have hdec : gRem ϖ γ succ cc u = (G1 + MvPowerSeries.C (γ / ℓ) * (T1 + L1 * T2 + L1 * T3 - PB)) +
      MvPowerSeries.C (γ / ℓ) * (GA - PG) := by
    rw [gRem, hΨ, sum_congr rfl fun i _ => key i, hpos]
    simp only [sum_add_distrib, ← mul_sum]
    ring
  -- the bounds
  have hγℓ : ‖γ / (ℓ : ℂ_[ℓ])‖ * ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := by
    rw [norm_div, div_mul_cancel₀ _ hℓn.ne']
    exact hγ
  have hu1 : ∀ i, ‖((u i : ℕ) : ℂ_[ℓ])‖ ≤ 1 := fun i => IsUltrametricDist.norm_natCast_le_one _ _
  have hL1 : ‖((ℓ + 1 : ℕ) : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have hM1 : IsWB (bS orb ϖ S) 1 G1 := by
    refine isWB_sum _ zero_le_one hS.nonneg fun i _ => ?_
    refine ((isWB_serAB_sub orb hϖ S hcc h3 i).C_mul _).mono hS.nonneg ?_
    rw [mul_one, norm_mul, norm_div, norm_two_padicC h3, div_one]
    exact mul_le_one_of (hu1 i) (norm_nonneg _) hγ
  have hT1 : IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ T1 := isWB_sum _ (norm_nonneg _) hS.nonneg fun i _ =>
    ((isWB_lead_rest orb hϖ S hcc i).C_mul _).mono hS.nonneg (mul_le_of_le_one_left (norm_nonneg _) (hu1 i))
  have hT2 : IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ T2 := isWB_sum _ (norm_nonneg _) hS.nonneg fun i _ =>
    (((isWB_gain_rem orb hϖ S hcc i).weight_mono (bB_le_bS orb S hϖ0) (norm_nonneg _)).C_mul _).mono hS.nonneg
      (mul_le_of_le_one_left (norm_nonneg _) (hu1 i))
  have hT3 : IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ T3 := isWB_cross_term orb hϖ S hTp hc horb
  have hPB : IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ PB := isWB_sum _ (norm_nonneg _) hS.nonneg fun x hx =>
    isWB_pos_base orb hϖ S horb (mem_filter.1 hx).2
  have hL1T : ∀ {T : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}, IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ T →
      IsWB (bS orb ϖ S) ‖(ℓ : ℂ_[ℓ])‖ (L1 * T) := fun {T} hT => by
    have h := hT.C_mul ((ℓ + 1 : ℕ) : ℂ_[ℓ])
    rw [map_natCast] at h
    exact h.mono hS.nonneg (mul_le_of_le_one_left (norm_nonneg _) hL1)
  have hM : IsWB (bS orb ϖ S) 1 (G1 + MvPowerSeries.C (γ / ℓ) * (T1 + L1 * T2 + L1 * T3 - PB)) :=
    hM1.add ((((hT1.add (hL1T hT2)).add (hL1T hT3)).sub hPB).C_mul _ |>.mono hS.nonneg hγℓ)
  have hP : IsWB (bG orb S) (‖γ / (ℓ : ℂ_[ℓ])‖ * 1) (MvPowerSeries.C (γ / ℓ) * (GA - PG)) := by
    refine IsWB.C_mul (IsWB.sub ?_ ?_) _
    · refine isWB_sum _ zero_le_one hG.nonneg fun i _ => ?_
      refine (((isWB_AP orb (ϖ := ϖ) S hcc i).pow hG (norm_nonneg _) (ℓ + 1)).C_mul _).mono hG.nonneg ?_
      exact mul_le_one_of (hu1 i) (by positivity) (pow_le_one₀ (norm_nonneg _) hϖ1)
    · refine isWB_sum _ zero_le_one hG.nonneg fun x hx => ?_
      have hx' : orb x.1 ∉ S := (mem_filter.1 hx).2
      have hx'' : orb (succ x.1, x.2).1 ∉ S := by rw [horb]; exact hx'
      refine ((((isWB_twSer_gain orb S horb hx').pow hG zero_le_one ℓ).mul hG zero_le_one
        (isWB_twSer_gain orb S horb hx'')).C_mul _).mono hG.nonneg ?_
      rw [one_pow, mul_one, mul_one, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hϖ1
  have hP0 : MvPowerSeries.coeff κ (MvPowerSeries.C (γ / ℓ) * (GA - PG)) = 0 := by
    have h := hP κ
    rw [bG, ite_eq_right hκ, mul_zero] at h
    exact norm_le_zero_iff.1 h
  rw [hdec, map_add, hP0, add_zero]
  have := hM κ
  rwa [one_mul] at this

end MixFinal


section MixFinal2

open ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ V : Type} [Fintype Φ] [DecidableEq Φ] [Fintype V] [DecidableEq V]
  {a b : ℕ}

/-- **Finite products** of series bounded by `1` in a weight. -/
theorem isWB_prod {σ ι : Type} {w : (σ →₀ ℕ) → ℝ} (hw : IsWeight w) (s : Finset ι)
    {f : ι → MvPowerSeries σ ℂ_[ℓ]} (hf : ∀ i ∈ s, IsWB w 1 (f i)) : IsWB w 1 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty]; exact isWB_one hw
  | insert j s hj ih =>
    rw [prod_insert hj]
    have h := (hf j (mem_insert_self j s)).mul hw zero_le_one (ih fun i hi => hf i (mem_insert_of_mem hi))
    rwa [one_mul] at h

variable (orb : Φ → V) {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (S : Finset V)
  {succ : Equiv.Perm Φ} {c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ} {u : Φ × Fin b × Fin a → ℕ}
  (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
  (hc : ∀ i x, ‖c i x‖ ≤ 1) (horb : ∀ τ, orb (succ τ) = orb τ)

include hϖ hTp hc horb in
/-- **The remainder of the Gaussian frame form is bounded by every split weight**: `exp(−G)` by divided powers
(base exponents: `norm_coeff_gRem_base`; gain exponents: `‖G_κ‖ ≤ ‖ϖ‖^{ℓ+1}`), and `U(X)` since the points
are (`isWB_xPt`). -/
theorem isWB_rem (h5 : 5 ≤ ℓ) {γ : ℂ_[ℓ]} (hγ : ‖γ‖ ≤ 1) {U : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]}
    (hU : IsIntK U)
    (hG : ∀ κ, ‖MvPowerSeries.coeff κ (gRem ϖ γ succ (fun i x => (c i x : ℂ_[ℓ])) u)‖ ≤ ‖ϖ‖ ^ (ℓ + 1)) :
    IsWB (bS orb ϖ S) 1 (expMv (-gRem ϖ γ succ (fun i x => (c i x : ℂ_[ℓ])) u) *
      MvPowerSeries.subst (xPt ϖ fun i x => (c i x : ℂ_[ℓ])) U) := by
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_pow_eq hℓ.out.one_lt hϖ
  have hS := isWeight_bS (b := b) (a := a) orb hϖ0 S
  have hcc : ∀ i x, ‖((c i x : unramC ℓ) : ℂ_[ℓ])‖ ≤ 1 := hc
  have hE : IsWB (bS orb ϖ S) 1 (expMv (-gRem ϖ γ succ (fun i x => (c i x : ℂ_[ℓ])) u)) := by
    refine isWB_expMv_of_dp hS fun μ => ?_
    rw [map_neg]
    by_cases hμ : ∀ v ∈ S, resV orb v μ = 0
    · exact dPc_bS_of_gain orb hϖ S hμ (by rw [norm_neg]; exact hG μ)
    · push Not at hμ
      exact dPc_bS_of_base orb hϖ0 S hμ (by
        rw [norm_neg]
        exact norm_coeff_gRem_base orb hϖ S hTp hc horb h5 hγ (by push Not; exact hμ))
  have hX : IsWB (bS orb ϖ S) 1 (MvPowerSeries.subst (xPt ϖ fun i x => (c i x : ℂ_[ℓ])) U) := by
    refine isWB_subst (hasSubst_xPt ϖ _) (fun κ => by rw [one_mul]; exact hS.nonneg κ) fun d => ?_
    refine ((isWB_prod hS _ fun s _ => ((isWB_xPt orb hϖ S hcc s).pow hS zero_le_one _).mono hS.nonneg
      (by rw [one_pow])).C_mul _).mono hS.nonneg ?_
    rw [mul_one]
    exact hU d
  have h := hE.mul hS zero_le_one hX
  rwa [one_mul] at h

end MixFinal2

/-! ## The Gaussian frame form -/

section ThetaFrame

open ThetaChain ThetaNorm ThetaHeis ThetaCompare ChainCanon HermGS MvTay ThetaGauss

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {a b : ℕ}

/-- **D1b-8, the interface (freeze this)**: in a frame with integral basis coordinates and the twisted dual-basis
identities for the Frobenius successor `succ` on `Φ` (an `n′`-cycle on each orbit `orb⁻¹ v`), the theta is
`c₀·posGauss(γ)·R` with `R` integral and mixed-integral. (`HClass` follows by `hClass_posGauss`; the orbit split by
`posGauss_orbits` after `Φ ≃ V × ZMod n′`.) -/
theorem theta_frame (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram)
    {d : ℕ} {sd : ℝ} (hd : Squarefree d) (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι' : ℂ ≃+* ℂ_[ℓ]) {C : AddSubgroup (Φ × Fin b × Fin a → ℂ)} (hCt : IsThetaLat (sC sd) sd C)
    (hCd : IsEDual (sC sd) C) (hω : ∀ x ∈ C, omegaD sd • x ∈ C) {θ : (Φ × Fin b × Fin a → ℂ) → ℂ}
    (hθ : θ ∈ Th (sC sd) sd C) (B : GSBasis ℓ (sC sd) sd (omegaD sd) C)
    (Fr : Φ × Fin b × Fin a → Φ × Fin b × Fin a → ℂ)
    (hint : ∀ i x, ‖ycoef ι' (fun i => (deltaC sd)⁻¹ • B.b i) B.u Fr i x‖ ≤ 1)
    (succ : Equiv.Perm Φ) {V : Type} [Fintype V] [DecidableEq V] (orb : Φ → V) (horb : ∀ τ, orb (succ τ) = orb τ)
    (c : Φ × Fin b × Fin a → Φ × Fin b × Fin a → unramC ℓ)
    (hc : ∀ i x, (c i x : ℂ_[ℓ]) = ycoef ι' (fun i => (deltaC sd)⁻¹ • B.b i) B.u Fr i x)
    (hTp : ∀ k : ℕ, ∀ x y, ∑ i, (B.u i : unramC ℓ) * c i x * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i y) =
      if x = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) y then 1 else 0)
    (_hTm : ∀ k : ℕ, ∀ x y, ∑ i, (B.u i : unramC ℓ) * (UnramFrobLift.frobUnram ℓ ^ (2 * k + 1)) (c i x) * c i y =
      if y = (Equiv.prodCongr succ (Equiv.refl _) ^ (2 * k + 1)) x then 1 else 0)
    {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ γ : unramC ℓ, UnramFrobLift.frobUnram ℓ γ = -γ ∧ ‖(γ : ℂ_[ℓ])‖ ≤ 1 ∧
      ∃ (c₀ : ℂ_[ℓ]) (R : MvPowerSeries (Φ × Fin b × Fin a) ℂ_[ℓ]), IsIntK R ∧ IsMixIntP orb ϖ R ∧
        thetaFrame ι' ε ϖ Fr θ = MvPowerSeries.C c₀ * (posGauss ϖ succ (fun _ => (γ : ℂ_[ℓ])) * R) := by
  have hc1 : ∀ i x, ‖c i x‖ ≤ 1 := fun i x => by
    have := hint i x
    rwa [← hc i x] at this
  have hcc : ∀ i x, ‖((c i x : unramC ℓ) : ℂ_[ℓ])‖ ≤ 1 := hc1
  obtain ⟨ε, hεu, hε, γ, hγφ, hγ1, c₀, U, hU, hG, hθF⟩ :=
    theta_frame_int hb hj hu hs hd hd8 hsd hΔ h5 hdℓ hin ι' hCt hCd hω hθ B Fr succ c hc hc1 hTp hϖ
  exact ⟨ε, hεu, hε, γ, hγφ, hγ1, c₀, _, isIntK_rem hϖ hG hU hcc,
    isMixIntP_of_forall orb ϖ fun S => isWB_rem orb hϖ S hTp hc1 horb h5 hγ1 hU hG, hθF⟩

end ThetaFrame

end

end ThetaPositions
