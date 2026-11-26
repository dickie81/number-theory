import CMThetaOne

/-!
# The addition theorems of the Weierstrass functions

Items (1) and (2) of the Weierstrass theory that the gain's CM theta needs (d1 spec §2.2–§2.3), for Mathlib's `℘` and
the library's `σ_W`, `ζ_W` (`ThetaNorm.sigmaW`, `ThetaNorm.zetaW`, with `CMThetaOne`'s `ζ_W′ = −℘`, `σ_W′ = σ_W·ζ_W`
and `℘″ = 6℘² − g₂/2`): the addition theorems of `σ`, `ζ` and `℘`, and the Laurent coefficients of `℘` at `0` as the
formal `CMFormalInert.wpC`.

**`σ_W`.** The product `sigP` of `σ_W = z·sigP` converges locally uniformly, so `σ_W` is entire
(`differentiable_sigmaW`), odd, with `σ_W′(0) = 1`, and vanishes exactly on the lattice (`sigmaW_eq_zero_iff`). As
`ζ_W(z + l) − ζ_W(z)` is a constant `η`, `σ_W(z + l)·e^{−ηz}/σ_W(z)` has derivative `0` on the connected complement of
the lattice, so `σ_W(z + l) = c·e^{ηz}·σ_W(z)` (`sigmaW_add_lattice`; everywhere by density).

**Liouville.** An elliptic function holomorphic off the lattice that agrees near `0` with a function differentiable at
`0` is constant (`eq_of_periodic`): given its limit on the lattice, it is entire and periodic, and Mathlib's Liouville
theorem applies with `IsZLattice.isCompact_range_of_periodic`, as in Mathlib's proof of `℘′² = 4℘³ − g₂℘ − g₃`.

**Addition.** For fixed `w`, `σ(z + w)σ(z − w)/σ(z)² + σ(w)²℘(z)` is elliptic in `z` (the quasi-periodicity factors
cancel) and has no pole at `0`: `σ(z + w)σ(z − w) + σ(w)²·sigP(z)²` is even and vanishes at `0`, so it is `z²` times an
entire function (`exists_sq_mul_of_even`). Its value at `z = w` gives `σ(z + w)σ(z − w) = σ(z)²σ(w)²(℘(w) − ℘(z))`
(`sigmaW_add_mul_sub`), so `℘(z) = ℘(w)` iff `z ≡ ±w` (`weierstrassP_eq_iff`). Its logarithmic derivatives in `z` and
in `w` add up to the addition theorem of `ζ` (`zetaW_add`), whose derivative in `z` is that of `℘` (`weierstrassP_add`);
the derivative in `w` at `w = z` is the duplication `σ(2z) = −℘′(z)σ(z)⁴` (`sigmaW_two_mul`).

**Laurent coefficients.** With `ℰ = ℘ − z⁻² = ℘[Λ − 0]` and its Taylor coefficients `lc(n) = (n + 1)G_{n+2}` from
Mathlib's expansion (`lc_eq`), `℘″ = 6℘² − g₂/2` becomes `z²ℰ″ = 12ℰ + 6z²ℰ² − (g₂/2)z²` near `0`
(`ode_weierstrassPExcept`), coefficient by coefficient (Leibniz) `((n + 2)(n + 1) − 12)·lc(n + 2) =
6·Σ_i lc(i)lc(n − i) − [n = 0]·g₂/2` (`lc_rec`): on the even coefficients this is `wpC`'s recursion, with the initial
values `g₂/20 = 3G₄` and `g₃/28 = 5G₆` (the coefficient of `z⁴` is free in the recursion). Hence
`wpC(g₂, g₃, k) = lc(2k − 2)` (`wpC_eq_lc`), `= (2k − 1)·G_{2k}` (`wpC_eq_G`), and
`℘(z) = z⁻² + Σ_k wpC(k + 2)·z^{2k+2}` near `0` (`hasSum_weierstrassP`).

**Main declarations:** `sigmaW_add_mul_sub`, `weierstrassP_eq_iff`, `zetaW_add`, `weierstrassP_add`, `sigmaW_two_mul`,
`wpC_eq_lc`, `wpC_eq_G`, `hasSum_weierstrassP`; for the later modules `sigmaW_add_lattice`, `eq_of_periodic`,
`sigmaW_eq_zero_iff` and the definitions `sigP`, `lc`.
-/

namespace EllipticAdd

noncomputable section

open PeriodPair ThetaNorm CMThetaOne Complex Filter Topology

variable (Λ : PeriodPair)

/-! ## The Weierstrass `σ` is entire and odd -/

/-- **The product of `σ_W`**: `σ_W(z) = z·sigP(z)`. -/
def sigP (z : ℂ) : ℂ := ∏' l : Λ.lattice, sgFac l z

/-- **`σ_W = z·sigP`.** -/
theorem sigmaW_eq (z : ℂ) : sigmaW Λ z = z * sigP Λ z := rfl

/-- **The product of `σ_W` is entire.** -/
theorem differentiable_sigP : Differentiable ℂ (sigP Λ) := by
  intro x
  have hxs : x ∈ Metric.ball (0 : ℂ) (‖x‖ + 1) := by simp
  have h := TendstoLocallyUniformlyOn.differentiableOn (multipliable_sgFac Λ (R := ‖x‖ + 1)).hasProdLocallyUniformlyOn
    (.of_forall fun s => by simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun l _ => by fun_prop))
    Metric.isOpen_ball
  exact h.differentiableAt (Metric.isOpen_ball.mem_nhds hxs)

/-- **`σ_W` is entire.** -/
theorem differentiable_sigmaW : Differentiable ℂ (sigmaW Λ) :=
  differentiable_id.mul (differentiable_sigP Λ)

/-- **`sigP(0) = 1`.** -/
theorem sigP_zero : sigP Λ 0 = 1 := by simp [sigP, sgFac]

/-- **`sigP` is even.** -/
theorem sigP_neg (z : ℂ) : sigP Λ (-z) = sigP Λ z := by
  simp only [sigP]
  rw [← (Equiv.neg Λ.lattice).tprod_eq (fun l => sgFac l z)]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sgFac]
  ring_nf

/-- **`σ_W` is odd.** -/
theorem sigmaW_neg (z : ℂ) : sigmaW Λ (-z) = -sigmaW Λ z := by
  rw [sigmaW_eq, sigmaW_eq, sigP_neg]; ring

/-- **`σ_W(0) = 0`.** -/
theorem sigmaW_zero : sigmaW Λ 0 = 0 := by simp [sigmaW_eq]

/-- **`σ_W′(0) = 1`.** -/
theorem hasDerivAt_sigmaW_zero : HasDerivAt (sigmaW Λ) 1 0 := by
  have h := (hasDerivAt_id' (0 : ℂ)).fun_mul (differentiable_sigP Λ 0).hasDerivAt
  have hf : sigmaW Λ = fun y => y * sigP Λ y := funext (sigmaW_eq Λ)
  rw [hf]
  simpa [sigP_zero] using h

/-- **`σ_W` vanishes exactly on the lattice.** -/
theorem sigmaW_eq_zero_iff (z : ℂ) : sigmaW Λ z = 0 ↔ z ∈ Λ.lattice := by
  refine ⟨fun h => by_contra fun hz => sigmaW_ne_zero Λ hz h, fun hz => ?_⟩
  by_cases h0 : z = 0
  · simp [h0, sigmaW_zero]
  · rw [sigmaW_eq, sigP, (hasProd_zero_of_exists_eq_zero ⟨⟨z, hz⟩, by simp [sgFac, div_self h0]⟩).tprod_eq,
      mul_zero]

/-! ## Quasi-periodicity of `σ_W` -/

/-- **The quasi-period of a period exists**: `ζ_W(z + l) − ζ_W(z)` is a constant `η` off the lattice. -/
theorem exists_zetaW_add_sub {l : ℂ} (hl : l ∈ Λ.lattice) :
    ∃ η, ∀ z ∉ Λ.lattice, zetaW Λ (z + l) - zetaW Λ z = η :=
  ⟨_, fun _ hz => zetaW_add_sub_const Λ hl hz Λ.ω₁_div_two_notMem_lattice⟩

/-- **The lattice is countable.** -/
theorem countable_lattice : (Λ.lattice : Set ℂ).Countable :=
  Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete (X := Λ.lattice))

/-- **Quasi-periodicity of `σ_W`**: if `ζ_W(z + l) − ζ_W(z) = η` off the lattice, then
`σ_W(z + l) = c·e^{ηz}·σ_W(z)` for some `c ≠ 0` and all `z`. -/
theorem sigmaW_add_lattice {l η : ℂ} (hl : l ∈ Λ.lattice)
    (hη : ∀ z ∉ Λ.lattice, zetaW Λ (z + l) - zetaW Λ z = η) :
    ∃ c ≠ 0, ∀ z, sigmaW Λ (z + l) = c * cexp (η * z) * sigmaW Λ z := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  set q : ℂ → ℂ := fun z => sigmaW Λ (z + l) * cexp (-(η * z)) / sigmaW Λ z with hq
  have hdq : ∀ z ∉ Λ.lattice, HasDerivAt q 0 z := by
    intro z hz
    have h1 := (hasDerivAt_sigmaW Λ (add_mem_compl Λ hz hl)).comp_add_const z l
    have h2 : HasDerivAt (fun z => cexp (-(η * z))) (cexp (-(η * z)) * -η) z := by
      simpa using ((hasDerivAt_id z).const_mul η).neg.cexp
    have h := (h1.fun_mul h2).div (hasDerivAt_sigmaW Λ hz) (sigmaW_ne_zero Λ hz)
    convert h using 1
    have e := hη z hz
    have hs := sigmaW_ne_zero Λ hz
    generalize cexp (-(η * z)) = E
    rw [eq_div_iff (pow_ne_zero 2 hs)]
    linear_combination (-(sigmaW Λ (z + l) * E * sigmaW Λ z)) * e
  have hconst : ∀ z ∉ Λ.lattice, q z = q (Λ.ω₁ / 2) := fun z hz =>
    hU.is_const_of_deriv_eq_zero (isPreconnected_compl Λ)
      (fun x hx => (hdq x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hdq x hx).deriv) hz
      Λ.ω₁_div_two_notMem_lattice
  set c := q (Λ.ω₁ / 2)
  have heq : ∀ z ∉ Λ.lattice, sigmaW Λ (z + l) = c * cexp (η * z) * sigmaW Λ z := by
    intro z hz
    have h := hconst z hz
    simp only [hq] at h
    rw [div_eq_iff (sigmaW_ne_zero Λ hz)] at h
    have he : cexp (-(η * z)) * cexp (η * z) = 1 := by rw [← Complex.exp_add]; simp
    linear_combination cexp (η * z) * h - sigmaW Λ (z + l) * he
  have hc : c ≠ 0 := by
    intro h0
    have := heq _ Λ.ω₁_div_two_notMem_lattice
    rw [h0, zero_mul, zero_mul] at this
    exact sigmaW_ne_zero Λ (add_mem_compl Λ Λ.ω₁_div_two_notMem_lattice hl) this
  refine ⟨c, hc, fun z => ?_⟩
  have hfun : (fun z => sigmaW Λ (z + l)) = fun z => c * cexp (η * z) * sigmaW Λ z := by
    refine Continuous.ext_on ((countable_lattice Λ).dense_compl ℂ)
      ((differentiable_sigmaW Λ).continuous.comp (continuous_id.add continuous_const))
      ((continuous_const.mul (by fun_prop)).mul (differentiable_sigmaW Λ).continuous) fun z hz => heq z hz
  exact congrFun hfun z

/-! ## Liouville's theorem for elliptic functions -/

/-- **An elliptic function without poles is constant**: if `F` is `Λ`-periodic and holomorphic off the lattice, and
agrees near `0` (off `0`) with a function differentiable at `0`, then `F` is constant off the lattice. -/
theorem eq_of_periodic {F g : ℂ → ℂ} (hper : ∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, F (z + l) = F z)
    (hd : DifferentiableOn ℂ F Λ.latticeᶜ) (hg : DifferentiableAt ℂ g 0) (h0 : ∀ᶠ z in 𝓝[≠] 0, F z = g z)
    {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) : F z = F w := by
  classical
  set G : ℂ → ℂ := fun z => if z ∈ Λ.lattice then g 0 else F z with hG
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hperG : ∀ z, ∀ l ∈ Λ.lattice, G (z + l) = G z := by
    intro z l hl
    by_cases hz : z ∈ Λ.lattice
    · simp [hG, hz, add_mem hz hl]
    · simp [hG, hz, add_mem_compl Λ hz hl, hper z hz l hl]
  have hG0 : G =ᶠ[𝓝 0] g := by
    filter_upwards [Λ.compl_lattice_sdiff_singleton_mem_nhds 0, eventually_nhdsWithin_iff.mp h0] with y hy hy'
    by_cases hy0 : y = 0
    · simp [hG, hy0]
    · have hyΛ : y ∉ Λ.lattice := fun h => hy ⟨h, hy0⟩
      simp [hG, hyΛ, hy' hy0]
  have hdG : Differentiable ℂ G := by
    intro x
    by_cases hx : x ∈ Λ.lattice
    · have hfun : G = fun y => G (y - x) := funext fun y => by
        rw [← hperG (y - x) x hx, sub_add_cancel]
      rw [hfun]
      have h1 : DifferentiableAt ℂ G ((fun y => y - x) x) := by
        simp only [sub_self]; exact hG0.differentiableAt_iff.mpr hg
      show DifferentiableAt ℂ (G ∘ fun y => y - x) x
      exact DifferentiableAt.comp (f := fun y => y - x) x h1 (differentiableAt_id.sub_const x)
    · have hev : G =ᶠ[𝓝 x] F := by
        filter_upwards [hU.mem_nhds hx] with y hy
        simp [hG, show y ∉ Λ.lattice from hy]
      exact hev.differentiableAt_iff.mpr ((hd x hx).differentiableAt (hU.mem_nhds hx))
  have h := hdG.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic Λ.lattice G hdG.continuous fun z w hw => hperG z w hw).isBounded z w
  simpa [hG, hz, hw] using h

/-- **An even entire function vanishing at `0` is `z²` times an entire function.** -/
theorem exists_sq_mul_of_even {M : ℂ → ℂ} (hM : Differentiable ℂ M) (he : ∀ z, M (-z) = M z) (h0 : M 0 = 0) :
    Differentiable ℂ (dslope (dslope M 0) 0) ∧ ∀ z, M z = z ^ 2 * dslope (dslope M 0) 0 z := by
  have hd1 : Differentiable ℂ (dslope M 0) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]; exact hM.differentiableOn
  have hd2 : Differentiable ℂ (dslope (dslope M 0) 0) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]; exact hd1.differentiableOn
  have hder : deriv M 0 = 0 := by
    have h := deriv_comp_neg M 0
    simp only [he, neg_zero] at h
    linear_combination h / 2
  refine ⟨hd2, fun z => ?_⟩
  have e1 := sub_smul_dslope M 0 z
  have e2 := sub_smul_dslope (dslope M 0) 0 z
  rw [dslope_same, hder] at e2
  simp only [sub_zero, smul_eq_mul, h0] at e1 e2
  rw [← e1, ← e2]
  ring

/-! ## The addition theorems -/

/-- **`℘′` is the derivative of `℘`** off the lattice. -/
theorem hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ Λ.lattice) : HasDerivAt ℘[Λ] (℘'[Λ] z) z := by
  have h := ((Λ.differentiableOn_weierstrassP z hz).differentiableAt
    (Λ.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rwa [Λ.deriv_weierstrassP] at h

/-- **`℘″ = 6℘² − g₂/2`**, as a derivative, off the lattice. -/
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ Λ.lattice) :
    HasDerivAt ℘'[Λ] (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) z := by
  have h := (Λ.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  rwa [eqOn_deriv_derivWeierstrassP Λ hz] at h

/-- **`℘ = z⁻² + ℘[Λ − 0]`** (Mathlib's `℘` without its `0`-term). -/
theorem weierstrassP_eq (z : ℂ) : ℘[Λ] z = 1 / z ^ 2 + Λ.weierstrassPExcept 0 z := by
  have h := Λ.weierstrassPExcept_def ⟨0, zero_mem _⟩ z
  change Λ.weierstrassPExcept 0 z = ℘[Λ] z + (1 / (0 : ℂ) ^ 2 - 1 / (z - 0) ^ 2) at h
  rw [h]
  simp

/-- **The `σ` addition formula** `σ(z + w)σ(z − w) = σ(z)²σ(w)²(℘(w) − ℘(z))` off the lattice: for fixed `w`,
`σ(z + w)σ(z − w)/σ(z)² + σ(w)²℘(z)` is elliptic in `z` (the quasi-periodicity factors cancel) without poles (at `0`
the numerator `σ(z + w)σ(z − w) + σ(w)²(σ(z)/z)²` is even and vanishes), hence constant; its value at `z = w` is
`σ(w)²℘(w)`. -/
theorem sigmaW_add_mul_sub {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) :
    sigmaW Λ (z + w) * sigmaW Λ (z - w) = sigmaW Λ z ^ 2 * sigmaW Λ w ^ 2 * (℘[Λ] w - ℘[Λ] z) := by
  set s := sigmaW Λ w with hs
  have hσ := differentiable_sigmaW Λ
  set M : ℂ → ℂ := fun y => sigmaW Λ (y + w) * sigmaW Λ (y - w) + s ^ 2 * sigP Λ y ^ 2 with hM
  have hMd : Differentiable ℂ M :=
    ((hσ.comp (differentiable_id.add_const w)).mul (hσ.comp (differentiable_id.sub_const w))).add
      (((differentiable_sigP Λ).pow 2).const_mul _)
  have hMe : ∀ y, M (-y) = M y := by
    intro y
    simp only [hM]
    rw [show -y + w = -(y - w) by ring, show -y - w = -(y + w) by ring, sigmaW_neg, sigmaW_neg, sigP_neg]
    ring
  have hM0 : M 0 = 0 := by
    simp only [hM, zero_add, zero_sub, sigmaW_neg, sigP_zero, hs]
    ring
  obtain ⟨hmd, hm⟩ := exists_sq_mul_of_even hMd hMe hM0
  set m := dslope (dslope M 0) 0
  set F : ℂ → ℂ := fun y => sigmaW Λ (y + w) * sigmaW Λ (y - w) / sigmaW Λ y ^ 2 + s ^ 2 * ℘[Λ] y with hF
  have hper : ∀ y ∉ Λ.lattice, ∀ l ∈ Λ.lattice, F (y + l) = F y := by
    intro y hy l hl
    obtain ⟨η, hη⟩ := exists_zetaW_add_sub Λ hl
    obtain ⟨c, hc, hcl⟩ := sigmaW_add_lattice Λ hl hη
    have hsy := sigmaW_ne_zero Λ hy
    simp only [hF]
    rw [show y + l + w = y + w + l by ring, show y + l - w = y - w + l by ring, hcl, hcl, hcl,
      Λ.weierstrassP_add_coe y ⟨l, hl⟩]
    have he : cexp (η * (y + w)) * cexp (η * (y - w)) = cexp (η * y) * cexp (η * y) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    have hey := Complex.exp_ne_zero (η * y)
    congr 1
    rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hc hey) hsy)) (pow_ne_zero 2 hsy)]
    linear_combination (c ^ 2 * sigmaW Λ (y + w) * sigmaW Λ (y - w) * sigmaW Λ y ^ 2) * he
  have hdF : DifferentiableOn ℂ F Λ.latticeᶜ :=
    ((((hσ.comp (differentiable_id.add_const w)).mul (hσ.comp (differentiable_id.sub_const w))).differentiableOn).div
      (hσ.pow 2).differentiableOn fun y hy => pow_ne_zero 2 (sigmaW_ne_zero Λ hy)).add
      (Λ.differentiableOn_weierstrassP.const_mul _)
  set g : ℂ → ℂ := fun y => m y / sigP Λ y ^ 2 + s ^ 2 * Λ.weierstrassPExcept 0 y with hg
  have hdg : DifferentiableAt ℂ g 0 :=
    ((hmd 0).div ((differentiable_sigP Λ 0).pow 2) (by simp [sigP_zero])).add
      ((Λ.analyticAt_weierstrassPExcept 0).differentiableAt.const_mul _)
  have hev : ∀ᶠ y in 𝓝[≠] 0, F y = g y := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds 0)]
      with y hy0 hyΛ
    have hyΛ' : y ∉ Λ.lattice := fun h => hyΛ ⟨h, hy0⟩
    have hP : sigP Λ y ≠ 0 := sigma_prod_ne_zero Λ hyΛ'
    have hy0' : y ≠ 0 := hy0
    have hmy := hm y
    simp only [hM] at hmy
    simp only [hF, hg]
    rw [sigmaW_eq Λ y, weierstrassP_eq Λ y]
    field_simp
    linear_combination hmy
  have h := eq_of_periodic Λ hper hdF hdg hev hz hw
  simp only [hF, sub_self, sigmaW_zero, mul_zero, zero_div, zero_add] at h
  have hsz := sigmaW_ne_zero Λ hz
  field_simp at h
  linear_combination h

/-- **`℘(z) = ℘(w)` exactly when `z ≡ ±w`** (for `z, w` off the lattice). -/
theorem weierstrassP_eq_iff {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) :
    ℘[Λ] z = ℘[Λ] w ↔ z + w ∈ Λ.lattice ∨ z - w ∈ Λ.lattice := by
  have h := sigmaW_add_mul_sub Λ hz hw
  rw [← sigmaW_eq_zero_iff, ← sigmaW_eq_zero_iff, ← mul_eq_zero, h]
  have hsz := sigmaW_ne_zero Λ hz
  have hsw := sigmaW_ne_zero Λ hw
  simp only [mul_eq_zero, pow_eq_zero_iff two_ne_zero, hsz, hsw, or_self, false_or, sub_eq_zero]
  exact eq_comm

/-- **The sum of `ζ(z + w)` and `ζ(z − w)`**: `ζ(z + w) + ζ(z − w) = 2ζ(z) + ℘′(z)/(℘(z) − ℘(w))`, the logarithmic
derivative in `z` of the `σ` addition formula. -/
theorem zetaW_add_add_zetaW_sub {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) (hp : z + w ∉ Λ.lattice)
    (hm : z - w ∉ Λ.lattice) :
    zetaW Λ (z + w) + zetaW Λ (z - w) = 2 * zetaW Λ z + ℘'[Λ] z / (℘[Λ] z - ℘[Λ] w) := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hA := ((hasDerivAt_sigmaW Λ hp).comp_add_const z w).mul ((hasDerivAt_sigmaW Λ hm).comp_sub_const z w)
  have hB := (((hasDerivAt_sigmaW Λ hz).pow 2).mul_const (sigmaW Λ w ^ 2)).mul
    ((hasDerivAt_weierstrassP Λ hz).const_sub (℘[Λ] w))
  have heq : (fun y => sigmaW Λ (y + w) * sigmaW Λ (y - w)) =ᶠ[𝓝 z]
      fun y => sigmaW Λ y ^ 2 * sigmaW Λ w ^ 2 * (℘[Λ] w - ℘[Λ] y) := by
    filter_upwards [hU.mem_nhds hz] with y hy using sigmaW_add_mul_sub Λ hy hw
  have hd := hA.unique (hB.congr_of_eventuallyEq heq)
  simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat] at hd
  have hrel := sigmaW_add_mul_sub Λ hz hw
  have hsz := sigmaW_ne_zero Λ hz
  have hsw := sigmaW_ne_zero Λ hw
  have hne : ℘[Λ] z - ℘[Λ] w ≠ 0 := by
    intro h0
    have : sigmaW Λ (z + w) * sigmaW Λ (z - w) = 0 := by rw [hrel]; linear_combination (-(sigmaW Λ z ^ 2 *
      sigmaW Λ w ^ 2)) * h0
    rcases mul_eq_zero.mp this with h | h
    exacts [sigmaW_ne_zero Λ hp h, sigmaW_ne_zero Λ hm h]
  have key : sigmaW Λ z ^ 2 * sigmaW Λ w ^ 2 * ((zetaW Λ (z + w) + zetaW Λ (z - w)) * (℘[Λ] z - ℘[Λ] w) -
      (2 * zetaW Λ z * (℘[Λ] z - ℘[Λ] w) + ℘'[Λ] z)) = 0 := by
    linear_combination (-1 : ℂ) * hd + (zetaW Λ (z + w) + zetaW Λ (z - w)) * hrel
  have h2 : (zetaW Λ (z + w) + zetaW Λ (z - w)) * (℘[Λ] z - ℘[Λ] w) =
      2 * zetaW Λ z * (℘[Λ] z - ℘[Λ] w) + ℘'[Λ] z := by
    have := (mul_eq_zero.mp key).resolve_left (by positivity)
    linear_combination this
  field_simp
  linear_combination h2

/-- **The addition theorem for `ζ`**: `ζ(z + w) = ζ(z) + ζ(w) + ½(℘′(z) − ℘′(w))/(℘(z) − ℘(w))` when `z`, `w`,
`z ± w` are off the lattice. -/
theorem zetaW_add {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) (hp : z + w ∉ Λ.lattice)
    (hm : z - w ∉ Λ.lattice) :
    zetaW Λ (z + w) = zetaW Λ z + zetaW Λ w + (℘'[Λ] z - ℘'[Λ] w) / (2 * (℘[Λ] z - ℘[Λ] w)) := by
  have hm' : w - z ∉ Λ.lattice := fun h => hm (by simpa using neg_mem h)
  have h1 := zetaW_add_add_zetaW_sub Λ hz hw hp hm
  have h2 := zetaW_add_add_zetaW_sub Λ hw hz (by rwa [add_comm]) hm'
  rw [show w - z = -(z - w) by ring, zetaW_neg, add_comm w z] at h2
  have hne : ℘[Λ] z - ℘[Λ] w ≠ 0 := fun h0 =>
    (weierstrassP_eq_iff Λ hz hw).mp (sub_eq_zero.mp h0) |>.elim hp hm
  have hne' : ℘[Λ] w - ℘[Λ] z ≠ 0 := fun h0 => hne (by linear_combination -h0)
  have h1' : (zetaW Λ (z + w) + zetaW Λ (z - w)) * (℘[Λ] z - ℘[Λ] w) =
      2 * zetaW Λ z * (℘[Λ] z - ℘[Λ] w) + ℘'[Λ] z := by rw [h1]; field_simp
  have h2' : (zetaW Λ (z + w) + -zetaW Λ (z - w)) * (℘[Λ] w - ℘[Λ] z) =
      2 * zetaW Λ w * (℘[Λ] w - ℘[Λ] z) + ℘'[Λ] w := by rw [h2]; field_simp
  have key : 2 * (℘[Λ] z - ℘[Λ] w) * (zetaW Λ (z + w) - (zetaW Λ z + zetaW Λ w)) = ℘'[Λ] z - ℘'[Λ] w := by
    linear_combination h1' - h2'
  field_simp
  linear_combination key

/-- **The addition theorem for `℘`**: `℘(z + w) = ¼((℘′(z) − ℘′(w))/(℘(z) − ℘(w)))² − ℘(z) − ℘(w)` when `z`, `w`,
`z ± w` are off the lattice (differentiate the addition theorem for `ζ` in `z`). -/
theorem weierstrassP_add {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) (hp : z + w ∉ Λ.lattice)
    (hm : z - w ∉ Λ.lattice) :
    ℘[Λ] (z + w) = ((℘'[Λ] z - ℘'[Λ] w) / (℘[Λ] z - ℘[Λ] w)) ^ 2 / 4 - ℘[Λ] z - ℘[Λ] w := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hne : ℘[Λ] z - ℘[Λ] w ≠ 0 := fun h0 =>
    (weierstrassP_eq_iff Λ hz hw).mp (sub_eq_zero.mp h0) |>.elim hp hm
  have hV : {y | y ∉ Λ.lattice ∧ y + w ∉ Λ.lattice ∧ y - w ∉ Λ.lattice} ∈ 𝓝 z := by
    have h1 : IsOpen {y : ℂ | y + w ∉ Λ.lattice} := hU.preimage (continuous_id.add continuous_const)
    have h2 : IsOpen {y : ℂ | y - w ∉ Λ.lattice} := hU.preimage (continuous_id.sub continuous_const)
    exact (hU.inter (h1.inter h2)).mem_nhds ⟨hz, hp, hm⟩
  have heq : (fun y => zetaW Λ (y + w)) =ᶠ[𝓝 z]
      fun y => zetaW Λ y + zetaW Λ w + (℘'[Λ] y - ℘'[Λ] w) / (2 * (℘[Λ] y - ℘[Λ] w)) := by
    filter_upwards [hV] with y hy using zetaW_add Λ hy.1 hw hy.2.1 hy.2.2
  have hL := (hasDerivAt_zetaW Λ hp).comp_add_const z w
  have hR := (((hasDerivAt_zetaW Λ hz).add_const (zetaW Λ w))).fun_add
    (((hasDerivAt_derivWeierstrassP Λ hz).sub_const (℘'[Λ] w)).fun_div
      (((hasDerivAt_weierstrassP Λ hz).sub_const (℘[Λ] w)).const_mul 2) (mul_ne_zero two_ne_zero hne))
  have hd := hL.unique (hR.congr_of_eventuallyEq heq)
  have hd' : (-℘[Λ] (z + w) + ℘[Λ] z) * (2 * (℘[Λ] z - ℘[Λ] w)) ^ 2 =
      (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) * (2 * (℘[Λ] z - ℘[Λ] w)) - (℘'[Λ] z - ℘'[Λ] w) * (2 * ℘'[Λ] z) := by
    rw [hd]; field_simp; ring
  have hsz := Λ.derivWeierstrassP_sq z hz
  have hsw := Λ.derivWeierstrassP_sq w hw
  rw [show ((℘'[Λ] z - ℘'[Λ] w) / (℘[Λ] z - ℘[Λ] w)) ^ 2 / 4 - ℘[Λ] z - ℘[Λ] w =
      ((℘'[Λ] z - ℘'[Λ] w) ^ 2 - 4 * (℘[Λ] z - ℘[Λ] w) ^ 2 * (℘[Λ] z + ℘[Λ] w)) /
        (4 * (℘[Λ] z - ℘[Λ] w) ^ 2) by field_simp; ring, eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hne))]
  linear_combination -hd' + hsz - hsw

/-- **The duplication formula** `σ(2z) = −℘′(z)·σ(z)⁴` off the lattice (differentiate the `σ` addition formula in `w`
at `w = z`, where `σ(0) = 0` and `σ′(0) = 1`). -/
theorem sigmaW_two_mul {z : ℂ} (hz : z ∉ Λ.lattice) : sigmaW Λ (2 * z) = -℘'[Λ] z * sigmaW Λ z ^ 4 := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have h1 := ((differentiable_sigmaW Λ) (z + z)).hasDerivAt.comp_const_add z z
  have h2 : HasDerivAt (fun w => sigmaW Λ (z - w)) (-1) z := by
    have h := hasDerivAt_sigmaW_zero Λ
    rw [← sub_self z] at h
    exact h.comp_const_sub z z
  have hA := h1.fun_mul h2
  have hB := (((hasDerivAt_sigmaW Λ hz).fun_pow 2).const_mul (sigmaW Λ z ^ 2)).fun_mul
    ((hasDerivAt_weierstrassP Λ hz).sub_const (℘[Λ] z))
  have heq : (fun w => sigmaW Λ (z + w) * sigmaW Λ (z - w)) =ᶠ[𝓝 z]
      fun w => sigmaW Λ z ^ 2 * sigmaW Λ w ^ 2 * (℘[Λ] w - ℘[Λ] z) := by
    filter_upwards [hU.mem_nhds hz] with w hw using sigmaW_add_mul_sub Λ hz hw
  have hd := hA.unique (hB.congr_of_eventuallyEq heq)
  simp only [sub_self, sigmaW_zero, mul_zero, zero_add, mul_neg, mul_one] at hd
  rw [two_mul]
  linear_combination -hd

/-! ## The Laurent coefficients of `℘` at `0` -/

/-- **The Taylor coefficients of `℘(z) − z⁻²` at `0`**: `lc(n) = ℘[Λ − 0]^{(n)}(0)/n!`. -/
def lc (n : ℕ) : ℂ := iteratedDeriv n (Λ.weierstrassPExcept 0) 0 / n.factorial

/-- **The Taylor coefficients from Mathlib's expansion**: `lc(0) = 0` and `lc(n) = (n + 1)·G_{n+2}` for `n ≥ 1`. -/
theorem lc_eq (n : ℕ) : lc Λ n = if n = 0 then 0 else (n + 1) * Λ.G (n + 2) := by
  rw [lc, Λ.iteratedDeriv_weierstrassPExcept_self 0]
  split_ifs with h
  · simp
  · rw [Λ.sumInvPow_zero, Nat.factorial_succ]
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    push_cast
    field_simp

/-- **The odd Taylor coefficients vanish.** -/
theorem lc_odd {n : ℕ} (hn : Odd n) : lc Λ n = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  simp only [lc_eq, hn0, ↓reduceIte]
  rw [Λ.G_eq_zero_of_odd _ (by simpa [Nat.odd_add] using hn), mul_zero]

/-- **The derivative of `z⁻²`.** -/
theorem hasDerivAt_one_div_sq {y : ℂ} (hy : y ≠ 0) : HasDerivAt (fun y => 1 / y ^ 2) (-2 / y ^ 3) y := by
  have h := (hasDerivAt_const y (1 : ℂ)).fun_div (hasDerivAt_pow 2 y) (pow_ne_zero 2 hy)
  convert h using 1
  field_simp
  ring

/-- **The derivative of `2z⁻³`.** -/
theorem hasDerivAt_two_div_cube {y : ℂ} (hy : y ≠ 0) : HasDerivAt (fun y => 2 / y ^ 3) (-6 / y ^ 4) y := by
  have h := (hasDerivAt_const y (2 : ℂ)).fun_div (hasDerivAt_pow 3 y) (pow_ne_zero 3 hy)
  convert h using 1
  field_simp
  ring

/-- **The differential equation of `ℰ = ℘ − z⁻²` near `0`**: `z²ℰ″ = 12ℰ + 6z²ℰ² − (g₂/2)z²` (from
`℘″ = 6℘² − g₂/2`). -/
theorem ode_weierstrassPExcept : (fun z => z ^ 2 * deriv (deriv (Λ.weierstrassPExcept 0)) z) =ᶠ[𝓝 0]
    fun z => 12 * Λ.weierstrassPExcept 0 z +
      6 * (z ^ 2 * (Λ.weierstrassPExcept 0 z * Λ.weierstrassPExcept 0 z)) - Λ.g₂ / 2 * z ^ 2 := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hf : Λ.weierstrassPExcept 0 = fun y => ℘[Λ] y - 1 / y ^ 2 :=
    funext fun y => by rw [weierstrassP_eq]; ring
  filter_upwards [Λ.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  have hzΛ : z ∉ Λ.lattice := fun h => hz ⟨h, hz0⟩
  have h1 : deriv (Λ.weierstrassPExcept 0) =ᶠ[𝓝 z] fun y => ℘'[Λ] y + 2 / y ^ 3 := by
    filter_upwards [hU.mem_nhds hzΛ] with y hy
    have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
    rw [hf, ((hasDerivAt_weierstrassP Λ hy).fun_sub (hasDerivAt_one_div_sq hy0)).deriv]
    ring
  have h2 := (hasDerivAt_derivWeierstrassP Λ hzΛ).fun_add (hasDerivAt_two_div_cube hz0)
  rw [h1.deriv_eq, h2.deriv, weierstrassP_eq Λ z]
  field_simp
  ring

/-- **The `n + 2`-nd derivative of `z²h(z)` at `0`** is `(n + 2)(n + 1)·h^{(n)}(0)`. -/
theorem iteratedDeriv_sq_mul {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (n : ℕ) :
    iteratedDeriv (n + 2) (fun z => z ^ 2 * h z) 0 = ((n : ℂ) + 2) * (n + 1) * iteratedDeriv n h 0 := by
  rw [iteratedDeriv_fun_mul (f := fun z : ℂ => z ^ 2) (contDiffAt_id.pow 2) hh.contDiffAt, Finset.sum_eq_single 2]
  · have hc := Nat.choose_mul_factorial_mul_factorial (show 2 ≤ n + 2 by omega)
    have hf : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [show n + 2 - 2 = n by omega, hf, show (2 : ℕ).factorial = 2 from rfl] at hc
    have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hc' : ((n + 2).choose 2 : ℂ) * 2 = (n + 2) * (n + 1) := by
      refine mul_right_cancel₀ hn0 ?_
      have := congrArg (fun m : ℕ => (m : ℂ)) hc
      push_cast at this
      linear_combination this
    simp only [iteratedDeriv_fun_pow_zero, ↓reduceIte, show n + 2 - 2 = n by omega]
    linear_combination iteratedDeriv n h 0 * hc'
  · intro i _ hi
    rw [iteratedDeriv_fun_pow_zero, ite_eq_right_iff.mpr fun h => absurd h hi]
    simp
  · intro h2
    simp at h2

/-- **The recursion of the Taylor coefficients** (the differential equation, coefficient by coefficient):
`((n + 2)(n + 1) − 12)·lc(n + 2) = 6·Σ_{i ≤ n} lc(i)·lc(n − i) − [n = 0]·g₂/2`. -/
theorem lc_rec (n : ℕ) : (((n : ℂ) + 2) * (n + 1) - 12) * lc Λ (n + 2) =
    6 * ∑ i ∈ Finset.range (n + 1), lc Λ i * lc Λ (n - i) - if n = 0 then Λ.g₂ / 2 else 0 := by
  set f := Λ.weierstrassPExcept 0 with hfdef
  have hfa : AnalyticAt ℂ f 0 := Λ.analyticAt_weierstrassPExcept 0
  have h := (ode_weierstrassPExcept Λ).iteratedDeriv_eq (n + 2)
  have hA1 : AnalyticAt ℂ (fun z => 12 * f z + 6 * (z ^ 2 * (f z * f z))) 0 := by fun_prop
  have hA2 : AnalyticAt ℂ (fun z => Λ.g₂ / 2 * z ^ 2) 0 := by fun_prop
  have hA3 : AnalyticAt ℂ (fun z => f z * f z) 0 := by fun_prop
  have hA4 : AnalyticAt ℂ (fun z => 12 * f z) 0 := by fun_prop
  have hA5 : AnalyticAt ℂ (fun z => 6 * (z ^ 2 * (f z * f z))) 0 := by fun_prop
  rw [iteratedDeriv_sq_mul hfa.deriv.deriv, iteratedDeriv_fun_sub hA1.contDiffAt hA2.contDiffAt,
    iteratedDeriv_fun_add hA4.contDiffAt hA5.contDiffAt, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_sq_mul hA3, iteratedDeriv_fun_mul hfa.contDiffAt hfa.contDiffAt,
    iteratedDeriv_fun_pow_zero, ← iteratedDeriv_succ', ← iteratedDeriv_succ'] at h
  have hD : ∀ k, iteratedDeriv k f 0 = k.factorial * lc Λ k := fun k => by
    rw [lc, ← hfdef]
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (n - i) f 0 =
      n.factorial * ∑ i ∈ Finset.range (n + 1), lc Λ i * lc Λ (n - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i ≤ n := by simp at hi; omega
    rw [hD, hD, ← Nat.choose_mul_factorial_mul_factorial hi]
    push_cast
    ring
  rw [hsum, hD, show n + 1 + 1 = n + 2 from rfl] at h
  have hfac : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hne : ((n : ℂ) + 2) * (n + 1) * n.factorial ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_cast) (by norm_cast)) hn0
  refine mul_left_cancel₀ hne ?_
  rw [hfac] at h
  rcases n with _ | n
  · simp at h ⊢
    linear_combination h / 2
  · simp only [show n + 1 + 2 ≠ 2 by omega, ite_false, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h ⊢
    linear_combination h

/-- **Splitting a sum into even and odd indices.** -/
theorem sum_range_even_odd (c : ℕ → ℂ) (M : ℕ) : ∑ i ∈ Finset.range (2 * M + 1), c i =
    ∑ m ∈ Finset.range (M + 1), c (2 * m) + ∑ m ∈ Finset.range M, c (2 * m + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ (fun m => c (2 * m)) (M + 1), Finset.sum_range_succ (fun m => c (2 * m + 1)) M,
      show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show 2 * M + 1 + 1 = 2 * (M + 1) by ring]
    ring

/-- **The Laurent coefficients of `℘` are `wpC`** (item (1) of the plan): `℘(z) − z⁻² = Σ_n lc(n)·zⁿ` near `0` with
`lc(2k − 2) = wpC(g₂, g₃, k)` for every `k`, the recursion of `CMFormalInert.wpC` being the differential equation
`℘″ = 6℘² − g₂/2` coefficient by coefficient (`lc_rec`), and its two initial values `g₂/20 = 3G₄`, `g₃/28 = 5G₆`. -/
theorem wpC_eq_lc (k : ℕ) : CMFormalInert.wpC Λ.g₂ Λ.g₃ k = lc Λ (2 * k - 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [CMFormalInert.wpC, lc_eq]
    | 1 => simp [CMFormalInert.wpC, lc_eq]
    | 2 =>
      rw [lc_eq]
      simp only [CMFormalInert.wpC, g₂]
      norm_num
      ring
    | 3 =>
      rw [lc_eq]
      simp only [CMFormalInert.wpC, g₃]
      norm_num
      ring
    | K + 4 =>
      rw [CMFormalInert.wpC, show 2 * (K + 4) - 2 = 2 * K + 4 + 2 by omega]
      have h0 : lc Λ 0 = 0 := by simp [lc_eq]
      have hrec := lc_rec Λ (2 * K + 4)
      rw [ite_eq_right_iff.mpr fun h => absurd h (by omega), sub_zero] at hrec
      have hsplit := sum_range_even_odd (fun i => lc Λ i * lc Λ (2 * K + 4 - i)) (K + 2)
      rw [show 2 * (K + 2) + 1 = 2 * K + 4 + 1 by ring] at hsplit
      rw [hsplit] at hrec
      have hodd : ∑ m ∈ Finset.range (K + 2), lc Λ (2 * m + 1) * lc Λ (2 * K + 4 - (2 * m + 1)) = 0 :=
        Finset.sum_eq_zero fun m _ => by rw [lc_odd Λ (odd_two_mul_add_one m), zero_mul]
      rw [hodd, add_zero, Finset.sum_range_succ', Finset.sum_range_succ, mul_zero, h0, zero_mul,
        show 2 * K + 4 - 2 * (K + 1 + 1) = 0 by omega, h0, mul_zero, add_zero, add_zero] at hrec
      have hfin : ∑ m : Fin (K + 1), CMFormalInert.wpC Λ.g₂ Λ.g₃ (m.val + 2) *
          CMFormalInert.wpC Λ.g₂ Λ.g₃ (K + 2 - m.val) =
          ∑ m ∈ Finset.range (K + 1), lc Λ (2 * (m + 1)) * lc Λ (2 * K + 4 - 2 * (m + 1)) := by
        rw [Fin.sum_univ_eq_sum_range (fun m => CMFormalInert.wpC Λ.g₂ Λ.g₃ (m + 2) *
          CMFormalInert.wpC Λ.g₂ Λ.g₃ (K + 2 - m))]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm : m < K + 1 := by simpa using hm
        rw [ih (m + 2) (by omega), ih (K + 2 - m) (by omega)]
        congr 2
        omega
      rw [hfin]
      have hne : (2 * ((K : ℂ) + 4) + 1) * ((K : ℂ) + 1) ≠ 0 := by norm_cast
      rw [div_mul_eq_mul_div, div_eq_iff hne]
      push_cast at hrec
      linear_combination -hrec / 2

/-- **The Laurent coefficients of `℘` by Eisenstein series**: `wpC(g₂, g₃, k) = (2k − 1)·G_{2k}` for `k ≥ 2`. -/
theorem wpC_eq_G {k : ℕ} (hk : 2 ≤ k) : CMFormalInert.wpC Λ.g₂ Λ.g₃ k = (2 * k - 1) * Λ.G (2 * k) := by
  simp only [wpC_eq_lc, lc_eq, show 2 * k - 2 ≠ 0 by omega, ↓reduceIte, show 2 * k - 2 + 2 = 2 * k by omega]
  push_cast [show 2 ≤ 2 * k by omega]
  ring

/-- **The Laurent expansion of `℘` at `0` with the coefficients `wpC`**: `℘(z) = z⁻² + Σ_{k≥0} wpC(k + 2)·z^{2k+2}` for
`0 < ‖z‖` below the length of every nonzero period (Mathlib's expansion of `℘[Λ − 0]`, with `wpC_eq_lc`). -/
theorem hasSum_weierstrassP {z : ℂ} (hz : ∀ l ∈ Λ.lattice, l ≠ 0 → ‖z‖ < ‖l‖) :
    HasSum (fun k : ℕ => CMFormalInert.wpC Λ.g₂ Λ.g₃ (k + 2) * z ^ (2 * k + 2)) (℘[Λ] z - 1 / z ^ 2) := by
  have h := Λ.weierstrassPExceptSeries_hasSum 0 z 0 fun l hl => by simpa using hz l l.2 hl
  have hc : ∀ i, (Λ.weierstrassPExceptSeries 0 0).coeff i = lc Λ i := by
    intro i
    rw [lc_eq]
    rcases i with _ | i
    · simp [weierstrassPExceptSeries]
    · simp [weierstrassPExceptSeries, Λ.sumInvPow_zero]
  simp only [hc, sub_zero] at h
  rw [weierstrassP_eq, add_sub_cancel_left]
  refine (Function.Injective.hasSum_iff (g := fun k : ℕ => 2 * k + 2) (fun a b h => by simpa using h)
    fun i hi => ?_).mpr h |>.congr_fun fun k => ?_
  · rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ho
    · rcases j with _ | j
      · simp [lc_eq]
      · exact absurd ⟨j, by simp; ring⟩ hi
    · simp [lc_odd Λ ho]
  · simp only [Function.comp_apply, wpC_eq_lc, show 2 * (k + 2) - 2 = 2 * k + 2 by omega]

end

end EllipticAdd
