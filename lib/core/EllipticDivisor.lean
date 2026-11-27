import EllipticLegendre

/-!
# Elliptic functions with poles at the periods, and the translates `G_q`

Item (3) of the Weierstrass theory that the gain's CM theta needs: an elliptic function whose poles lie on the lattice
is `P(℘) + ℘′·Q(℘)` (`EllPole.exists_poly`), and for a torsion point `q ∉ Λ`, `Nq ∈ Λ`, the translate
`G_q(z) = e^{−η(q)z}σ(z + q)/(σ(z)σ(q))` has `G_qᴺ` of this form (`Gq_pow_eq_poly`), with divisor `N[−q] − N[0]`.

**Polynomials in `℘`, `℘′`.** `EllPole f m` says that `f` is periodic and holomorphic off the lattice and `zᵐf(z)` is
holomorphic at `0`. Subtracting `c℘^k` (order `2k`, with `z²℘ = wpU`) or adding `(c/2)℘′℘^k` (order `2k + 3`, with
`z³℘′ = wpV`) removes the leading coefficient `c` and lowers the order (`ellPole_lower`); order `0` is a constant
(`EllPole.eq_const`), and order `1` does not occur (`EllPole.lower_one`): if `zf(z) → c`, then `f − cζ_W` has additive
periods and no poles, so it is affine, and its periods give `c·(η₁ω₂ − η₂ω₁) = 0`, where Legendre's relation (in either
orientation, `legendre_ne_zero`) makes `c = 0`.

**The translates.** `η(q) = s₂q + (π/A)·q̄` (`etaR`) is the `ℝ`-linear extension of the quasi-periods
(`CMThetaOne.zetaW_add_lattice`, unconditional with `EllipticLegendre.legendre`). Then
`G_q(z + l) = e^{η(l)q − η(q)l}·G_q(z)` (`Gq_add`), and `η(l)q − η(q)l = (π/A)(l̄q − q̄l)` lies in `(2πi/N)ℤ` when
`Nq ∈ Λ`, as the area form `l̄l′ − l̄′l` of the lattice lies in `2iAℤ` (`conj_mul_sub_lattice`, `exp_factor_pow`). So
`G_qᴺ` is elliptic (`Gq_pow_add`) with a pole of order `N` at the periods (`z·G_q(z) → 1`, `tendsto_mul_Gq`), and its
zeros are the points of `−q + Λ` (`Gq_eq_zero_iff`), each of order `N` (`hasDerivAt_Gq_neg`: the zeros of `G_q` are
simple). The logarithmic derivative of `G_q` is `ζ(q) − η(q) + ½(℘′(z) − ℘′(q))/(℘(z) − ℘(q))` (`logDeriv_Gq`, by the
addition theorem of `ζ`).

**Main declarations:** `EllPole.exists_poly`, `Gq_pow_eq_poly`, `Gq_eq_zero_iff`, `tendsto_mul_Gq`,
`hasDerivAt_Gq_neg`, `hasDerivAt_Gq`, `logDeriv_Gq`, `legendre_ne_zero`; the definitions `EllPole`, `etaR`, `Gq`.
-/

namespace EllipticDivisor

noncomputable section

open PeriodPair ThetaNorm CMThetaOne EllipticAdd EllipticLegendre Complex Filter Topology

variable (Λ : PeriodPair)

/-! ## Legendre's relation in either orientation -/

/-- **`Im(ω₂/ω₁) ≠ 0`** (the periods are `ℝ`-independent). -/
theorem im_div_ne_zero : (Λ.ω₂ / Λ.ω₁).im ≠ 0 := by
  intro h
  have h1 : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
  have he : Λ.ω₂ = ((Λ.ω₂ / Λ.ω₁).re : ℂ) * Λ.ω₁ := by
    conv_lhs => rw [← div_mul_cancel₀ Λ.ω₂ h1, ← Complex.re_add_im (Λ.ω₂ / Λ.ω₁), h]
    simp
  have := LinearIndependent.pair_iff.mp Λ.indep ((Λ.ω₂ / Λ.ω₁).re) (-1) (by
    rw [Complex.real_smul, neg_one_smul, ← he, add_neg_cancel])
  norm_num at this

/-- **`η₁ω₂ − η₂ω₁ ≠ 0`** for either orientation of the basis (Legendre's relation for `(ω₁, ω₂)` or `(ω₂, ω₁)`,
which span the same lattice). -/
theorem legendre_ne_zero : 2 * zetaW Λ (Λ.ω₁ / 2) * Λ.ω₂ - 2 * zetaW Λ (Λ.ω₂ / 2) * Λ.ω₁ ≠ 0 := by
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rcases lt_or_gt_of_ne (im_div_ne_zero Λ) with h | h
  · let Λ' : PeriodPair := ⟨Λ.ω₂, Λ.ω₁, LinearIndependent.pair_iff.mpr fun s t hst =>
      (LinearIndependent.pair_iff.mp Λ.indep t s (by rw [add_comm]; exact hst)).symm⟩
    have hlat : Λ'.lattice = Λ.lattice := by
      simp only [PeriodPair.lattice, Λ', Set.pair_comm]
    have hz : zetaW Λ' = zetaW Λ := by
      funext z
      simp only [zetaW]
      rw [hlat]
    have h1 : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
    have h2 : Λ.ω₂ ≠ 0 := Λ.indep.ne_zero 1
    have hor' : 0 < (Λ'.ω₂ / Λ'.ω₁).im := by
      change 0 < (Λ.ω₁ / Λ.ω₂).im
      rw [show Λ.ω₁ / Λ.ω₂ = (Λ.ω₂ / Λ.ω₁)⁻¹ by rw [inv_div], inv_im, neg_div]
      exact neg_pos.mpr (div_neg_of_neg_of_pos h (normSq_pos.mpr (div_ne_zero h2 h1)))
    have hl := legendre Λ' hor'
    rw [hz] at hl
    change 2 * zetaW Λ (Λ.ω₂ / 2) * Λ.ω₁ - 2 * zetaW Λ (Λ.ω₁ / 2) * Λ.ω₂ = 2 * Real.pi * I at hl
    intro h0
    exact h2pi (by linear_combination -hl - h0)
  · rw [legendre Λ h]
    exact h2pi

/-! ## Elliptic functions with poles at the periods are polynomials in `℘`, `℘′` -/

/-- **An elliptic function with poles of order at most `m`, at the periods only**: `Λ`-periodic and holomorphic off the
lattice, with `zᵐf(z)` holomorphic at `0` (after removing the singularity). -/
def EllPole (f : ℂ → ℂ) (m : ℕ) : Prop :=
  (∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, f (z + l) = f z) ∧ DifferentiableOn ℂ f Λ.latticeᶜ ∧
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ z in 𝓝[≠] 0, z ^ m * f z = g z

/-- **`dslope` keeps analyticity.** -/
theorem analyticAt_dslope {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) : AnalyticAt ℂ (dslope g 0) 0 := by
  have hs : {y | AnalyticAt ℂ g y} ∈ 𝓝 (0 : ℂ) := hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g {y | AnalyticAt ℂ g y} := fun y hy => hy.differentiableAt.differentiableWithinAt
  exact ((Complex.differentiableOn_dslope hs).mpr hd).analyticAt hs

/-- **Lowering the pole order** when the leading coefficient vanishes. -/
theorem ellPole_lower {f g : ℂ → ℂ} {m : ℕ} (hper : ∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, f (z + l) = f z)
    (hd : DifferentiableOn ℂ f Λ.latticeᶜ) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hfg : ∀ᶠ z in 𝓝[≠] 0, z ^ (m + 1) * f z = g z) : EllPole Λ f m := by
  refine ⟨hper, hd, dslope g 0, analyticAt_dslope hg, ?_⟩
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have e := sub_smul_dslope g 0 z
  rw [hg0, sub_zero, sub_zero, smul_eq_mul, ← hz, pow_succ] at e
  exact mul_left_cancel₀ hz0' (by linear_combination -e)

/-- **An elliptic function without poles is constant** (in the form of `EllPole`). -/
theorem EllPole.eq_const {f : ℂ → ℂ} (hf : EllPole Λ f 0) {z : ℂ} (hz : z ∉ Λ.lattice) :
    f z = f (Λ.ω₁ / 2) := by
  obtain ⟨hper, hd, g, hg, hfg⟩ := hf
  exact eq_of_periodic Λ hper hd hg.differentiableAt (by simpa using hfg) hz Λ.ω₁_div_two_notMem_lattice

/-- **No elliptic function has a single simple pole**: an `EllPole` of order `1` has order `0`. If `zf(z) → c`, then
`F = f − cζ_W` has additive periods and no poles, so `F′` is constant, `F` is affine, and comparing its periods along
`ω₁`, `ω₂` gives `c·(η₁ω₂ − η₂ω₁) = 0`; Legendre's relation makes `c = 0`. -/
theorem EllPole.lower_one {f : ℂ → ℂ} (hf : EllPole Λ f 1) : EllPole Λ f 0 := by
  obtain ⟨hper, hd, g, hg, hfg⟩ := hf
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  suffices hc : g 0 = 0 from ellPole_lower Λ hper hd hg hc (by simpa using hfg)
  set c := g 0 with hcdef
  set F : ℂ → ℂ := fun z => f z - c * zetaW Λ z with hF
  have hFd : DifferentiableOn ℂ F Λ.latticeᶜ := hd.sub ((differentiableOn_zetaW Λ).const_mul c)
  have hFper : ∀ l ∈ Λ.lattice, ∀ z ∉ Λ.lattice,
      F (z + l) = F z - c * (zetaW Λ (Λ.ω₁ / 2 + l) - zetaW Λ (Λ.ω₁ / 2)) := by
    intro l hl z hz
    have h := zetaW_add_sub_const Λ hl hz Λ.ω₁_div_two_notMem_lattice
    simp only [hF, hper z hz l hl]
    linear_combination -c * h
  have hF'per : ∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, deriv F (z + l) = deriv F z := by
    intro z hz l hl
    have hev : (fun y => F (y + l)) =ᶠ[𝓝 z]
        fun y => F y - c * (zetaW Λ (Λ.ω₁ / 2 + l) - zetaW Λ (Λ.ω₁ / 2)) := by
      filter_upwards [hU.mem_nhds hz] with y hy using hFper l hl y hy
    have h1 := hev.deriv_eq
    rwa [deriv_comp_add_const, deriv_sub_const] at h1
  set G : ℂ → ℂ := fun z => dslope g 0 z - c * zetaE Λ z with hG
  have hEa : AnalyticAt ℂ (zetaE Λ) 0 :=
    (differentiableOn_zetaE Λ).analyticAt (Λ.isOpen_compl_lattice_sdiff.mem_nhds (by simp))
  have hGa : AnalyticAt ℂ G 0 := (analyticAt_dslope hg).sub (analyticAt_const.mul hEa)
  have hFG : ∀ᶠ z in 𝓝[≠] 0, F z = G z := by
    filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have e := sub_smul_dslope g 0 z
    rw [sub_zero, smul_eq_mul, ← hz, pow_one] at e
    simp only [hF, hG, zetaW_eq_add]
    field_simp
    linear_combination -e
  have hF'G : ∀ᶠ z in 𝓝[≠] 0, deriv F z = deriv G z := by
    filter_upwards [eventually_eventually_nhdsWithin.mpr hFG, self_mem_nhdsWithin] with y hy hy0
    have hy' : F =ᶠ[𝓝 y] G :=
      hy.filter_mono (le_of_eq (nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hy0)).symm)
    exact hy'.deriv_eq
  have hF'd : DifferentiableOn ℂ (deriv F) Λ.latticeᶜ := hFd.deriv hU
  set α := deriv F (Λ.ω₁ / 2)
  have hα : ∀ z ∉ Λ.lattice, deriv F z = α := fun z hz =>
    eq_of_periodic Λ hF'per hF'd hGa.deriv.differentiableAt hF'G hz Λ.ω₁_div_two_notMem_lattice
  have hlin : ∀ z ∉ Λ.lattice, F z - α * z = F (Λ.ω₁ / 2) - α * (Λ.ω₁ / 2) := by
    intro z hz
    refine hU.is_const_of_deriv_eq_zero (f := fun z => F z - α * z) (isPreconnected_compl Λ)
      (hFd.sub (differentiableOn_id.const_mul α)) (fun x hx => ?_) hz Λ.ω₁_div_two_notMem_lattice
    have hx' := ((hFd x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
    rw [(hx'.fun_sub ((hasDerivAt_id' x).const_mul α)).deriv, hα x hx]
    simp
  have hq : ∀ ω, ω ∈ Λ.lattice → ω / 2 ∉ Λ.lattice → α * ω = -c * (2 * zetaW Λ (ω / 2)) := by
    intro ω hω hh
    have z0 : Λ.ω₁ / 2 ∉ Λ.lattice := Λ.ω₁_div_two_notMem_lattice
    have h1 := hlin _ (add_mem_compl Λ z0 hω)
    have h2 := zetaW_add_basis Λ hω hh z0
    have h3 : F (Λ.ω₁ / 2 + ω) = F (Λ.ω₁ / 2) - c * (zetaW Λ (Λ.ω₁ / 2 + ω) - zetaW Λ (Λ.ω₁ / 2)) := by
      simp only [hF, hper _ z0 ω hω]; ring
    linear_combination -h1 + h3 - c * h2
  have e1 := hq _ Λ.ω₁_mem_lattice Λ.ω₁_div_two_notMem_lattice
  have e2 := hq _ Λ.ω₂_mem_lattice Λ.ω₂_div_two_notMem_lattice
  have key : c * (2 * zetaW Λ (Λ.ω₁ / 2) * Λ.ω₂ - 2 * zetaW Λ (Λ.ω₂ / 2) * Λ.ω₁) = 0 := by
    linear_combination Λ.ω₂ * e1 - Λ.ω₁ * e2
  exact (mul_eq_zero.mp key).resolve_right (legendre_ne_zero Λ)

/-- **`z²℘(z)` near `0`**: `1 + z²·℘[Λ − 0](z)`. -/
def wpU (z : ℂ) : ℂ := 1 + z ^ 2 * Λ.weierstrassPExcept 0 z

/-- **`z³℘′(z)` near `0`**: `−2 + z³·℘′[Λ − 0](z)`. -/
def wpV (z : ℂ) : ℂ := -2 + z ^ 3 * Λ.derivWeierstrassPExcept 0 z

/-- **`z²℘(z) = wpU(z)`** for `z ≠ 0`. -/
theorem sq_mul_weierstrassP {z : ℂ} (hz : z ≠ 0) : z ^ 2 * ℘[Λ] z = wpU Λ z := by
  rw [weierstrassP_eq, wpU]; field_simp

/-- **`z³℘′(z) = wpV(z)`** for `z ≠ 0`. -/
theorem cube_mul_derivWeierstrassP {z : ℂ} (hz : z ≠ 0) : z ^ 3 * ℘'[Λ] z = wpV Λ z := by
  have h := Λ.derivWeierstrassPExcept_def ⟨0, zero_mem _⟩ z
  change Λ.derivWeierstrassPExcept 0 z = ℘'[Λ] z + 2 / (z - 0) ^ 3 at h
  rw [wpV, h]
  field_simp
  ring

/-- **`wpU` is analytic at `0` with value `1`.** -/
theorem analyticAt_wpU : AnalyticAt ℂ (wpU Λ) 0 ∧ wpU Λ 0 = 1 := by
  have := Λ.analyticAt_weierstrassPExcept 0
  exact ⟨by unfold wpU; fun_prop, by simp [wpU]⟩

/-- **`wpV` is analytic at `0` with value `−2`.** -/
theorem analyticAt_wpV : AnalyticAt ℂ (wpV Λ) 0 ∧ wpV Λ 0 = -2 := by
  have := Λ.analyticAt_derivWeierstrassPExcept 0
  exact ⟨by unfold wpV; fun_prop, by simp [wpV]⟩

/-- **Elliptic functions with poles only at the periods are polynomials in `℘` and `℘′`**: if `f` is an `EllPole`,
then `f = P(℘) + ℘′·Q(℘)` off the lattice. Subtract `c℘^k` (order `2k`) or `−(c/2)℘′℘^k` (order `2k + 3`) to lower
the order, and order `1` does not occur (`EllPole.lower_one`). -/
theorem EllPole.exists_poly {m : ℕ} : ∀ {f : ℂ → ℂ}, EllPole Λ f m → ∃ P Q : Polynomial ℂ,
    ∀ z ∉ Λ.lattice, f z = P.eval (℘[Λ] z) + ℘'[Λ] z * Q.eval (℘[Λ] z) := by
  induction m with
  | zero =>
    intro f hf
    exact ⟨Polynomial.C (f (Λ.ω₁ / 2)), 0, fun z hz => by simp [hf.eq_const Λ hz]⟩
  | succ m ih =>
    intro f hf
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ih hf.lower_one
    obtain ⟨hper, hd, g, hg, hfg⟩ := hf
    have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
    have hPper : ∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, ℘[Λ] (z + l) = ℘[Λ] z := fun z _ l hl =>
      Λ.weierstrassP_add_coe z ⟨l, hl⟩
    have hP'per : ∀ z ∉ Λ.lattice, ∀ l ∈ Λ.lattice, ℘'[Λ] (z + l) = ℘'[Λ] z := fun z _ l hl =>
      Λ.derivWeierstrassP_add_coe z ⟨l, hl⟩
    have hPd : DifferentiableOn ℂ ℘[Λ] Λ.latticeᶜ := Λ.differentiableOn_weierstrassP
    have hP'd : DifferentiableOn ℂ ℘'[Λ] Λ.latticeᶜ := Λ.differentiableOn_derivWeierstrassP
    obtain ⟨hUa, hU0⟩ := analyticAt_wpU Λ
    obtain ⟨hVa, hV0⟩ := analyticAt_wpV Λ
    rcases Nat.even_or_odd (m + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even order `2k`: subtract `c·℘^k`
      set h : ℂ → ℂ := fun z => f z - g 0 * ℘[Λ] z ^ k with hh
      have hlow : EllPole Λ h m := by
        refine ellPole_lower Λ (g := fun z => g z - g 0 * wpU Λ z ^ k) (fun z hz l hl => ?_)
          (hd.sub ((hPd.pow k).const_mul _)) (hg.sub (analyticAt_const.mul (hUa.pow k))) (by simp [hU0]) ?_
        · simp only [hh, hper z hz l hl, hPper z hz l hl]
        · filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
          have hz0' : z ≠ 0 := hz0
          rw [← hz, ← sq_mul_weierstrassP Λ hz0', hk]
          simp only [hh]
          ring
      obtain ⟨P, Q, hPQ⟩ := ih hlow
      refine ⟨P + Polynomial.C (g 0) * Polynomial.X ^ k, Q, fun z hz => ?_⟩
      have := hPQ z hz
      simp only [hh] at this
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      linear_combination this
    · -- odd order `2k + 1 ≥ 3`: add `(c/2)·℘′℘^{k−1}`
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      set h : ℂ → ℂ := fun z => f z + g 0 / 2 * (℘'[Λ] z * ℘[Λ] z ^ j) with hh
      have hlow : EllPole Λ h m := by
        refine ellPole_lower Λ (g := fun z => g z + g 0 / 2 * (wpV Λ z * wpU Λ z ^ j)) (fun z hz l hl => ?_)
          (hd.add (((hP'd.mul (hPd.pow j))).const_mul _))
          (hg.add (analyticAt_const.mul (hVa.mul (hUa.pow j)))) (by simp [hU0, hV0]) ?_
        · simp only [hh, hper z hz l hl, hPper z hz l hl, hP'per z hz l hl]
        · filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
          have hz0' : z ≠ 0 := hz0
          rw [← hz, ← sq_mul_weierstrassP Λ hz0', ← cube_mul_derivWeierstrassP Λ hz0', hk]
          simp only [hh]
          ring
      obtain ⟨P, Q, hPQ⟩ := ih hlow
      refine ⟨P, Q - Polynomial.C (g 0 / 2) * Polynomial.X ^ j, fun z hz => ?_⟩
      have := hPQ z hz
      simp only [hh] at this
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      linear_combination this

/-! ## The translates `G_q` -/

/-- **The `ℝ`-linear quasi-period** `η(q) = s₂q + (π/A)·q̄` (Masser; equal to `ζ_W(z + q) − ζ_W(z)` for periods `q`,
`CMThetaOne.zetaW_add_lattice`). -/
def etaR (q : ℂ) : ℂ := s2 Λ * q + ((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ q

/-- **The translate** `G_q(z) = e^{−η(q)z}·σ(z + q)/(σ(z)σ(q))`, the function of divisor `[−q] − [0]` (up to the
periods). -/
def Gq (q z : ℂ) : ℂ := cexp (-(etaR Λ q * z)) * sigmaW Λ (z + q) / (sigmaW Λ z * sigmaW Λ q)

/-- **The area form on the lattice**: `l̄l′ − l̄′l = 2i·k·A` for periods `l`, `l′` and some `k ∈ ℤ`. -/
theorem conj_mul_sub_lattice (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l l' : ℂ} (hl : l ∈ Λ.lattice) (hl' : l' ∈ Λ.lattice) :
    ∃ k : ℤ, starRingEnd ℂ l * l' - starRingEnd ℂ l' * l = 2 * I * (k * area Λ) := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.mp hl
  obtain ⟨m', n', rfl⟩ := mem_lattice.mp hl'
  refine ⟨m * n' - n * m', ?_⟩
  have hD : starRingEnd ℂ Λ.ω₁ * Λ.ω₂ - starRingEnd ℂ Λ.ω₂ * Λ.ω₁ = 2 * I * (area Λ : ℂ) := by
    rw [area_eq_im Λ hor]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  simp only [map_add, map_mul, map_intCast]
  push_cast
  linear_combination (m * n' - n * m' : ℂ) * hD

/-- **The periodicity factor of `G_q` is an `N`-th root of unity** when `Nq` is a period (Legendre's relation makes
`η` the `ℝ`-linear map `s₂q + (π/A)q̄`, and `η(l)q − η(q)l = (π/A)(l̄q − q̄l)`). -/
theorem exp_factor_pow (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} {N : ℕ} (hNq : (N : ℂ) * q ∈ Λ.lattice) {l : ℂ}
    (hl : l ∈ Λ.lattice) : cexp (etaR Λ l * q - etaR Λ q * l) ^ N = 1 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  obtain ⟨k, hk⟩ := conj_mul_sub_lattice Λ hor hl hNq
  refine ⟨k, ?_⟩
  have hA : (area Λ : ℂ) ≠ 0 := by exact_mod_cast (ChainCanon.area_pos Λ).ne'
  have hκ : ((Real.pi / area Λ : ℝ) : ℂ) * (area Λ : ℂ) = Real.pi := by push_cast; field_simp
  simp only [map_mul, map_natCast] at hk
  simp only [etaR]
  linear_combination ((Real.pi / area Λ : ℝ) : ℂ) * hk + 2 * I * k * hκ

/-- **Quasi-periodicity of `G_q`**: `G_q(z + l) = e^{η(l)q − η(q)l}·G_q(z)`. -/
theorem Gq_add (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} (hq : q ∉ Λ.lattice) {l : ℂ} (hl : l ∈ Λ.lattice) {z : ℂ}
    (hz : z ∉ Λ.lattice) : Gq Λ q (z + l) = cexp (etaR Λ l * q - etaR Λ q * l) * Gq Λ q z := by
  obtain ⟨c, hc, hσ⟩ := sigmaW_add_lattice Λ hl (η := etaR Λ l) fun z hz => zetaW_add_lattice Λ legendre hor hl hz
  have hsz := sigmaW_ne_zero Λ hz
  have hsq := sigmaW_ne_zero Λ hq
  simp only [Gq]
  rw [show z + l + q = z + q + l by ring, hσ, hσ]
  have hE : cexp (-(etaR Λ q * (z + l))) * cexp (etaR Λ l * (z + q)) =
      cexp (etaR Λ l * q - etaR Λ q * l) * cexp (-(etaR Λ q * z)) * cexp (etaR Λ l * z) := by
    simp only [← Complex.exp_add]; ring_nf
  have he := Complex.exp_ne_zero (etaR Λ l * z)
  generalize cexp (-(etaR Λ q * (z + l))) = A at hE ⊢
  generalize cexp (etaR Λ l * (z + q)) = B at hE ⊢
  generalize cexp (etaR Λ l * q - etaR Λ q * l) = C at hE ⊢
  generalize cexp (-(etaR Λ q * z)) = D at hE ⊢
  generalize cexp (etaR Λ l * z) = E at hE he ⊢
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hc he) hsz) hsq)]
  field_simp
  linear_combination sigmaW Λ (z + q) * hE

/-- **`G_qᴺ` is `Λ`-periodic** when `Nq` is a period. -/
theorem Gq_pow_add (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ}
    (hNq : (N : ℂ) * q ∈ Λ.lattice) {z : ℂ} (hz : z ∉ Λ.lattice) {l : ℂ} (hl : l ∈ Λ.lattice) :
    Gq Λ q (z + l) ^ N = Gq Λ q z ^ N := by
  rw [Gq_add Λ hor hq hl hz, mul_pow, exp_factor_pow Λ hor hNq hl, one_mul]

/-- **`G_q` is holomorphic off the lattice.** -/
theorem differentiableOn_Gq {q : ℂ} (hq : q ∉ Λ.lattice) : DifferentiableOn ℂ (Gq Λ q) Λ.latticeᶜ := by
  have hσ := differentiable_sigmaW Λ
  refine DifferentiableOn.div (by fun_prop) ((hσ.mul_const _).differentiableOn) fun z hz =>
    mul_ne_zero (sigmaW_ne_zero Λ hz) (sigmaW_ne_zero Λ hq)

/-- **`z·G_q(z)` near `0`**: `e^{−η(q)z}σ(z + q)/(σ(q)·σ(z)/z)`, holomorphic at `0` with value `1`. -/
def GqRes (q z : ℂ) : ℂ := cexp (-(etaR Λ q * z)) * sigmaW Λ (z + q) / (sigP Λ z * sigmaW Λ q)

/-- **`z·G_q(z) = GqRes(z)`** for `z ≠ 0`. -/
theorem mul_Gq {q z : ℂ} (hz : z ≠ 0) : z * Gq Λ q z = GqRes Λ q z := by
  simp only [Gq, GqRes, sigmaW_eq Λ z]
  by_cases hP : sigP Λ z = 0
  · simp [hP]
  by_cases hs : sigmaW Λ q = 0
  · simp [hs]
  field_simp

/-- **`GqRes` is analytic at `0` with value `1`** (for `q ∉ Λ`). -/
theorem analyticAt_GqRes {q : ℂ} (hq : q ∉ Λ.lattice) : AnalyticAt ℂ (GqRes Λ q) 0 ∧ GqRes Λ q 0 = 1 := by
  have hsq := sigmaW_ne_zero Λ hq
  have hσ := differentiable_sigmaW Λ
  have h1 : AnalyticAt ℂ (fun z => sigmaW Λ (z + q)) 0 :=
    (hσ.comp (differentiable_id.add_const q)).differentiableOn.analyticAt Filter.univ_mem
  have h2 : AnalyticAt ℂ (sigP Λ) 0 := (differentiable_sigP Λ).differentiableOn.analyticAt Filter.univ_mem
  refine ⟨?_, by simp [GqRes, sigP_zero, hsq]⟩
  unfold GqRes
  refine AnalyticAt.div (by fun_prop) (h2.mul analyticAt_const) (by simp [sigP_zero, hsq])

/-- **`G_qᴺ` is an elliptic function with a pole of order `N` at the periods only.** -/
theorem ellPole_Gq_pow (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ}
    (hNq : (N : ℂ) * q ∈ Λ.lattice) : EllPole Λ (fun z => Gq Λ q z ^ N) N := by
  obtain ⟨ha, -⟩ := analyticAt_GqRes Λ hq
  refine ⟨fun z hz l hl => Gq_pow_add Λ hor hq hNq hz hl, (differentiableOn_Gq Λ hq).pow N,
    fun z => GqRes Λ q z ^ N, ha.pow N, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz0
  rw [← mul_pow, mul_Gq Λ hz0]

/-- **`G_qᴺ` is a polynomial in `℘` and `℘′`** (item (3)): for a torsion point `q ∉ Λ` with `Nq ∈ Λ` there are
polynomials `P`, `Q` with `G_q(z)ᴺ = P(℘(z)) + ℘′(z)·Q(℘(z))` off the lattice; its divisor is `N[−q] − N[0]`
(`Gq_eq_zero_iff`, `hasDerivAt_Gq_neg`, `tendsto_mul_Gq`). -/
theorem Gq_pow_eq_poly (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ}
    (hNq : (N : ℂ) * q ∈ Λ.lattice) : ∃ P Q : Polynomial ℂ,
      ∀ z ∉ Λ.lattice, Gq Λ q z ^ N = P.eval (℘[Λ] z) + ℘'[Λ] z * Q.eval (℘[Λ] z) :=
  (ellPole_Gq_pow Λ hor hq hNq).exists_poly

/-- **The zeros of `G_q`**: off the lattice, `G_q(z) = 0` exactly when `z ≡ −q`. -/
theorem Gq_eq_zero_iff {q z : ℂ} (hq : q ∉ Λ.lattice) (hz : z ∉ Λ.lattice) : Gq Λ q z = 0 ↔ z + q ∈ Λ.lattice := by
  simp only [Gq, div_eq_zero_iff, mul_eq_zero, Complex.exp_ne_zero, false_or, sigmaW_eq_zero_iff, hz, hq, or_self,
    or_false]

/-- **The pole of `G_q` at `0` is simple with residue `1`**: `z·G_q(z) → 1`. -/
theorem tendsto_mul_Gq {q : ℂ} (hq : q ∉ Λ.lattice) : Tendsto (fun z => z * Gq Λ q z) (𝓝[≠] 0) (𝓝 1) := by
  obtain ⟨ha, h1⟩ := analyticAt_GqRes Λ hq
  have h := ha.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [h1] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz0
  exact (mul_Gq Λ hz0).symm

/-- **The zero of `G_q` at `−q` is simple**: `G_q′(−q) = −e^{η(q)q}/σ(q)² ≠ 0`. -/
theorem hasDerivAt_Gq_neg {q : ℂ} (hq : q ∉ Λ.lattice) :
    HasDerivAt (Gq Λ q) (-cexp (etaR Λ q * q) / sigmaW Λ q ^ 2) (-q) ∧
      -cexp (etaR Λ q * q) / sigmaW Λ q ^ 2 ≠ 0 := by
  have hsq := sigmaW_ne_zero Λ hq
  have hmq : -q ∉ Λ.lattice := fun h => hq (by simpa using neg_mem h)
  have h1 : HasDerivAt (fun z => cexp (-(etaR Λ q * z))) (cexp (-(etaR Λ q * -q)) * -etaR Λ q) (-q) := by
    simpa using ((hasDerivAt_id (-q)).const_mul (etaR Λ q)).neg.cexp
  have h2 : HasDerivAt (fun z => sigmaW Λ (z + q)) 1 (-q) := by
    have h := hasDerivAt_sigmaW_zero Λ
    rw [show (0 : ℂ) = -q + q by ring] at h
    exact h.comp_add_const (-q) q
  have h3 := ((differentiable_sigmaW Λ) (-q)).hasDerivAt.mul_const (sigmaW Λ q)
  have h := (h1.fun_mul h2).fun_div h3 (by rw [sigmaW_neg]; exact mul_ne_zero (neg_ne_zero.mpr hsq) hsq)
  refine ⟨?_, div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) (pow_ne_zero 2 hsq)⟩
  have hfun : Gq Λ q = fun z => cexp (-(etaR Λ q * z)) * sigmaW Λ (z + q) / (sigmaW Λ z * sigmaW Λ q) := rfl
  rw [hfun]
  convert h using 1
  simp only [neg_add_cancel, sigmaW_zero, mul_zero, sigmaW_neg, mul_neg, neg_neg, mul_one, zero_mul, sub_zero]
  field_simp
  ring

/-- **The logarithmic derivative of `G_q`**: `G_q′ = G_q·(ζ(z + q) − ζ(z) − η(q))` where `z`, `z + q` are off the
lattice. -/
theorem hasDerivAt_Gq {q z : ℂ} (hq : q ∉ Λ.lattice) (hz : z ∉ Λ.lattice) (hzq : z + q ∉ Λ.lattice) :
    HasDerivAt (Gq Λ q) (Gq Λ q z * (zetaW Λ (z + q) - zetaW Λ z - etaR Λ q)) z := by
  have hsq := sigmaW_ne_zero Λ hq
  have hsz := sigmaW_ne_zero Λ hz
  have h1 : HasDerivAt (fun z => cexp (-(etaR Λ q * z))) (cexp (-(etaR Λ q * z)) * -etaR Λ q) z := by
    simpa using ((hasDerivAt_id z).const_mul (etaR Λ q)).neg.cexp
  have h2 := (hasDerivAt_sigmaW Λ hzq).comp_add_const z q
  have h3 := (hasDerivAt_sigmaW Λ hz).mul_const (sigmaW Λ q)
  have h := (h1.fun_mul h2).fun_div h3 (mul_ne_zero hsz hsq)
  have hfun : Gq Λ q = fun z => cexp (-(etaR Λ q * z)) * sigmaW Λ (z + q) / (sigmaW Λ z * sigmaW Λ q) := rfl
  rw [hfun]
  convert h using 1
  field_simp
  ring

/-- **The logarithmic derivative of `G_q` as a rational function** (by the `ζ` addition theorem):
`G_q′/G_q = (ζ(q) − η(q)) + ½(℘′(z) − ℘′(q))/(℘(z) − ℘(q))` for `z`, `q`, `z ± q` off the lattice. -/
theorem logDeriv_Gq {q z : ℂ} (hq : q ∉ Λ.lattice) (hz : z ∉ Λ.lattice) (hp : z + q ∉ Λ.lattice)
    (hm : z - q ∉ Λ.lattice) :
    HasDerivAt (Gq Λ q) (Gq Λ q z * (zetaW Λ q - etaR Λ q +
      (℘'[Λ] z - ℘'[Λ] q) / (2 * (℘[Λ] z - ℘[Λ] q)))) z := by
  convert hasDerivAt_Gq Λ hq hz hp using 2
  rw [zetaW_add Λ hz hq hp hm]
  ring

end

end EllipticDivisor
