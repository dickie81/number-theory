import ChainCanon

/-!
# The one-variable CM theta by the Hurwitz route

D1a of the D1 plan: the jets of the one-variable normalised theta `th0(z) = U_tσ*(z)/U_tσ*(0)` (`ThetaNorm.th0`, with
`s = 1/area` and `σ* = σ_W·exp(−s₂z²/2)`, here `th0L`) at a half-period `t`, as a theorem. The Hurwitz formula
`th0 = exp(−s₂z²/2 − Σ_{n≥0} ℘^{(n)}(t)·z^{n+2}/(n+2)!)` holds as Taylor series at `0` (`th0_taylor`, `logTh0`), and
the jets `∂^n th0(0)` are polynomials over `ℤ` in `g₂/2`, `℘(t)` and `s₂` (`th0_jets_mem`, `th0_jets_mem_closure`).
So they lie in `σ₀(K)`, are algebraic, and are `ℓ`-integral at every prime `ℓ ≠ 2`, wherever `g₂`, `℘(t)`, `s₂` do
or are (`th0_jets_mem_range`, `th0_jets_isAlgebraic`, `th0_jets_int`). For the construction's lattice
`Lc = δ(ℤ + ℤω)` (`Δ(Lc) = 1`) and point `t = δ/2` (`ChainCanon.cmLat`, `ChainCanon.tC`), the inputs CM-c and CM-d
make the jets algebraic and integral at every `ℓ ≥ 5`, `ℓ ∤ d` (`canon_jets_isAlgebraic`, `canon_jets_int`), and
`canon_jets_mem_range` is the statement in the shape of `ThetaChain.Data.JetsRat` (values in `σ₀(K)`).

**The analysis.** Mathlib has `℘`, `℘′`, `g₂`, `g₃` and `℘′² = 4℘³ − g₂℘ − g₃`, but no `σ` and no `ζ`. Here `ζ_W′ = −℘`
termwise, as Mathlib differentiates `℘` (`eqOn_deriv_zetaW`); `σ_W′ = σ_W·ζ_W`, from Mathlib's logarithmic derivative
of a locally uniformly convergent product and the factor bound `(1 − w)·e^{w + w²/2} = 1 + O(w³)`
(`hasDerivAt_sigmaW`); and `℘″ = 6℘² − g₂/2`, by differentiating Mathlib's relation and cancelling `℘′`, which is not
identically zero (`eqOn_deriv_derivWeierstrassP`). Then `th0′ = th0·logDer` with
`logDer(z) = ζ_W(z + t) − s₂(z + t) − (π/A)·t̄` (`hasDerivAt_th0L`), `logDer′ = −℘(· + t) − s₂`, and `logDer(0) = 0`
is Masser's half-period identity (`zetaW_half`). That identity follows from Legendre's relation (`Legendre`, an input:
it needs a contour integral of `ζ_W`) through the quasi-periodicity `ζ_W(z + l) − ζ_W(z) = s₂l + (π/A)·l̄`
(`zetaW_add_lattice`).

**The algebra.** Leibniz's rule turns `th0′ = th0·logDer` into the recursion
`∂^{n+1}th0(0) = Σ_i C(n, i)·∂^i th0(0)·∂^{n−i}logDer(0)` (`iteratedDeriv_th0L_succ`), and `℘″ = 6℘² − g₂/2` gives the
derivatives of `℘` at `t` the same way, where `℘′(t) = 0`. Both have integer coefficients, so the integrality needs no
divided-power (Hurwitz-series) argument and no explicit polynomials `P_n`, and `g₃` does not enter the jets. The formal
identity `th0_taylor` is the same recursion for `exp(logTh0)`, from `d(exp ∘ L)/dz = exp(L)·L′`.

**Inputs** (hypotheses, as typechecked in the D1 spec): Legendre's relation `Legendre`, and CM-c `CMjIntegral` and CM-d
`CMs2` (with `HasCM`) for the canonical lattice. As in `ChainCanon`, `Δ(ℤ + ℤω) ≠ 0` is a hypothesis.

**Main declarations:** `Legendre`, `HasCM`, `CMjIntegral`, `CMs2`, `th0L`, `logTh0`, `zetaW_half`, `th0_taylor`,
`th0_jets_mem`, `th0_jets_mem_closure`, `th0_jets_mem_range`, `th0_jets_isAlgebraic`, `th0_jets_int`,
`canon_jets_isAlgebraic`, `canon_jets_int`, `canon_jets_mem_range`.

**Sanity theorems:** `th0L_zero`, `hasDerivAt_sigmaW`, `hasDerivAt_zetaW`, `eqOn_deriv_derivWeierstrassP`.
-/

namespace CMThetaOne

noncomputable section

open PeriodPair ThetaChain ThetaNorm ChainCanon Complex Filter Topology

/-! ## Inputs (classical, as typechecked in the D1 spec) -/

/-- **`Λ` has CM by `O_F`**, `F = ℚ(√−d)`, `d ≡ 3 (mod 4)`: `(1 + √−d)/2·Λ ⊆ Λ` (local-spec §5.1). -/
def HasCM (d : ℕ) (Λ : PeriodPair) : Prop :=
  ∀ z ∈ Λ.lattice, (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 * z ∈ Λ.lattice

/-- **CM-c (Weber, Deuring)**: `j` is an algebraic integer (an input). -/
def CMjIntegral : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ →
    IsIntegral ℤ (1728 * Λ.g₂ ^ 3 / (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2))

/-- **CM-d (Masser; Katz)**: Masser's `s₂` of the `Δ = 1` CM lattice is algebraic, integral at every `ℓ ≥ 5`, `ℓ ∤ d`
(the CM eigen-splitting of `H¹_dR` is integral where the discriminant is invertible), and `d·s₂²` is integral at `ℓ ∣ d`
(an input). -/
def CMs2 : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ → Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1 →
    IsAlgebraic ℚ (s2 Λ) ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ∀ ι : ℂ ≃+* ℂ_[ℓ],
      (¬ ℓ ∣ d → ‖ι (s2 Λ)‖ ≤ 1) ∧ (ℓ ∣ d → ‖ι ((d : ℂ) * s2 Λ ^ 2)‖ ≤ 1)

/-- **Legendre's relation** for the library's `ζ_W` (classical; an input): `η₁ω₂ − η₂ω₁ = 2πi` for the quasi-periods
`η_i = 2ζ_W(ω_i/2)`, when `Im(ω₂/ω₁) > 0`. -/
def Legendre : Prop :=
  ∀ Λ : PeriodPair, 0 < (Λ.ω₂ / Λ.ω₁).im →
    2 * zetaW Λ (Λ.ω₁ / 2) * Λ.ω₂ - 2 * zetaW Λ (Λ.ω₂ / 2) * Λ.ω₁ = 2 * Real.pi * Complex.I

variable (Λ : PeriodPair)

/-! ## The Weierstrass `ζ`: termwise derivative -/

/-- **The summand of `ζ_W`** for `l ≠ 0`, `z ≠ l`: `1/(z − l) + 1/l + z/l² = z²/(l²(z − l))`. -/
theorem zeta_summand_eq {l z : ℂ} (hl : l ≠ 0) (hz : z ≠ l) :
    1 / (z - l) + 1 / l + z / l ^ 2 = z ^ 2 / (l ^ 2 * (z - l)) := by
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- **The summand bound of `ζ_W`**: for `‖z‖ < r` and `‖l‖ ≥ 2r` the summand is at most `2r²‖l‖⁻³`. -/
theorem zeta_bound {r : ℝ} {z l : ℂ} (hz : ‖z‖ < r) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) + 1 / l + z / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 < r := (norm_nonneg z).trans_lt hz
  have hl0 : 0 < ‖l‖ := by linarith
  have hzl : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]; have := norm_sub_norm_le l z; linarith
  have hzl0 : z ≠ l := by rintro rfl; linarith
  rw [zeta_summand_eq (norm_pos_iff.mp hl0) hzl0, norm_div, norm_mul, norm_pow, norm_pow,
    Real.rpow_neg hl0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
  _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by field_simp

/-- **`ζ_W` is the locally uniform sum of its summands** (as Mathlib's `℘`). -/
theorem hasSumLocallyUniformly_zetaW :
    HasSumLocallyUniformly (fun (l : Λ.lattice) (z : ℂ) => 1 / (z - l) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (zetaW Λ) := by
  refine Λ.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r _ =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact zeta_bound hs h

/-- **Each summand of `ζ_W` is holomorphic off the lattice.** -/
theorem differentiableOn_zeta_summand (l : Λ.lattice) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (z - l) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) Λ.latticeᶜ := by
  refine .add (.add (.div (by fun_prop) (by fun_prop) fun z hz => ?_) (by fun_prop)) (by fun_prop)
  intro h
  exact hz (sub_eq_zero.mp h ▸ l.2)

/-- **`ζ_W` is holomorphic off the lattice.** -/
theorem differentiableOn_zetaW : DifferentiableOn ℂ (zetaW Λ) Λ.latticeᶜ :=
  (hasSumLocallyUniformly_zetaW Λ).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => .fun_sum fun l _ => differentiableOn_zeta_summand Λ l) Λ.isClosed_lattice.isOpen_compl

/-- **`ζ_W′ = −℘` off the lattice**, termwise (the derivatives of the partial sums converge locally uniformly). -/
theorem eqOn_deriv_zetaW : Set.EqOn (deriv (zetaW Λ)) (fun z => -℘[Λ] z) Λ.latticeᶜ := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  refine ((hasSumLocallyUniformly_zetaW Λ).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun _ => .fun_sum fun l _ => differentiableOn_zeta_summand Λ l) hU).unique ?_
  have hneg := uniformContinuous_neg.comp_tendstoLocallyUniformlyOn
    (Λ.hasSumLocallyUniformly_weierstrassP.tendstoLocallyUniformlyOn (s := Λ.latticeᶜ))
  refine hneg.congr fun s z hz => ?_
  simp only [Function.comp_apply]
  rw [deriv_fun_sum fun l _ => (differentiableOn_zeta_summand Λ l).differentiableAt (hU.mem_nhds hz),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hzl : z - l ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ l.2)
  have h1 : HasDerivAt (fun w : ℂ => 1 / (w - l) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2)
      (-(1 / (z - l) ^ 2) + 1 / (l : ℂ) ^ 2) z := by
    have ha : HasDerivAt (fun w : ℂ => w - l) 1 z := (hasDerivAt_id z).sub_const _
    have hb := ha.inv hzl
    have hc : HasDerivAt (fun w : ℂ => w / (l : ℂ) ^ 2) (1 / (l : ℂ) ^ 2) z :=
      (hasDerivAt_id z).div_const _
    convert (hb.add_const (1 / (l : ℂ))).add hc using 1
    · ext w; simp [one_div]
    · simp [one_div, neg_div]
  rw [h1.deriv]
  ring

/-- **`ζ_W′ = −℘`** at a point off the lattice. -/
theorem hasDerivAt_zetaW {z : ℂ} (hz : z ∉ Λ.lattice) : HasDerivAt (zetaW Λ) (-℘[Λ] z) z := by
  have hd := (differentiableOn_zetaW Λ z hz).differentiableAt
    (Λ.isClosed_lattice.isOpen_compl.mem_nhds hz)
  have h := eqOn_deriv_zetaW Λ hz
  simp only at h
  exact h ▸ hd.hasDerivAt

/-- **`ζ_W` is odd.** -/
theorem zetaW_neg (z : ℂ) : zetaW Λ (-z) = -zetaW Λ z := by
  simp only [zetaW]
  rw [← (Equiv.neg Λ.lattice).tsum_eq, ← tsum_neg]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  rw [show -z - -(l : ℂ) = -(z - l) by ring, div_neg, div_neg, neg_sq, neg_div]
  ring

/-! ## The Weierstrass `σ`: logarithmic derivative -/

/-- **The Weierstrass factor is `1 + O(w³)`**: `‖(1 − w)·exp(w + w²/2) − 1‖ ≤ 2‖w‖³` for `‖w‖ ≤ 1/2` (the cubic Taylor
bound of `exp`). -/
theorem factor_bound {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w) * cexp (w + w ^ 2 / 2) - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  set a := w + w ^ 2 / 2 with ha
  have hw0 := norm_nonneg w
  have hna : ‖a‖ ≤ 5 / 4 * ‖w‖ := by
    calc ‖a‖ ≤ ‖w‖ + ‖w ^ 2 / 2‖ := norm_add_le _ _
    _ = ‖w‖ + ‖w‖ ^ 2 / 2 := by simp [norm_pow]
    _ ≤ 5 / 4 * ‖w‖ := by nlinarith
  have ha1 : ‖a‖ ≤ 1 := by nlinarith
  have hE := Complex.exp_bound ha1 (n := 3) (by norm_num)
  have hS : ∑ m ∈ Finset.range 3, a ^ m / (m.factorial : ℂ) = 1 + a + a ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hS] at hE
  norm_num [Nat.factorial] at hE
  have key : (1 - w) * cexp a - 1 =
      -(w ^ 3 / 2 + 3 * w ^ 4 / 8 + w ^ 5 / 8) + (1 - w) * (cexp a - (1 + a + a ^ 2 / 2)) := by
    rw [ha]; ring
  have h1 : ‖w ^ 3 / 2 + 3 * w ^ 4 / 8 + w ^ 5 / 8‖ ≤ ‖w‖ ^ 3 := by
    calc _ ≤ ‖w ^ 3 / 2‖ + ‖3 * w ^ 4 / 8‖ + ‖w ^ 5 / 8‖ := norm_add₃_le
    _ = ‖w‖ ^ 3 / 2 + 3 * ‖w‖ ^ 4 / 8 + ‖w‖ ^ 5 / 8 := by simp [norm_pow]
    _ ≤ ‖w‖ ^ 3 := by
      have h4 : ‖w‖ ^ 4 ≤ ‖w‖ ^ 3 / 2 := by nlinarith [pow_nonneg hw0 3]
      have h5 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 3 / 4 := by nlinarith [pow_nonneg hw0 3, pow_nonneg hw0 4]
      nlinarith
  have h2 : ‖(1 - w) * (cexp a - (1 + a + a ^ 2 / 2))‖ ≤ ‖w‖ ^ 3 := by
    rw [norm_mul]
    have h1w : ‖1 - w‖ ≤ 3 / 2 := (norm_sub_le _ _).trans (by simp; linarith)
    have ha3 : ‖a‖ ^ 3 ≤ (5 / 4 * ‖w‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hna 3
    calc ‖1 - w‖ * ‖cexp a - (1 + a + a ^ 2 / 2)‖ ≤ 3 / 2 * (‖a‖ ^ 3 * (2 / 9)) := by
          gcongr
    _ ≤ 3 / 2 * ((5 / 4 * ‖w‖) ^ 3 * (2 / 9)) := by gcongr
    _ ≤ ‖w‖ ^ 3 := by nlinarith [pow_nonneg hw0 3]
  rw [key]
  calc _ ≤ ‖-(w ^ 3 / 2 + 3 * w ^ 4 / 8 + w ^ 5 / 8)‖ + ‖(1 - w) * (cexp a - (1 + a + a ^ 2 / 2))‖ :=
        norm_add_le _ _
  _ ≤ ‖w‖ ^ 3 + ‖w‖ ^ 3 := by rw [norm_neg]; gcongr
  _ = 2 * ‖w‖ ^ 3 := by ring

/-- **The factor `(1 − z/l)·exp(z/l + z²/(2l²))` of `σ_W`** (the `l = 0` factor is `1`). -/
abbrev sgFac (l z : ℂ) : ℂ := (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2))

/-- **The factor bound on a disc**: `‖factor − 1‖ ≤ 2R³‖l‖⁻³` for `‖z‖ < R` and `‖l‖ ≥ 2R`. -/
theorem sgFac_bound {l z : ℂ} {R : ℝ} (hz : ‖z‖ < R) (hl : 2 * R ≤ ‖l‖) :
    ‖sgFac l z - 1‖ ≤ 2 * R ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  have hl0 : 0 < ‖l‖ := by linarith
  have hw : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hl0]; linarith
  have heq : sgFac l z = (1 - z / l) * cexp (z / l + (z / l) ^ 2 / 2) := by
    simp only [sgFac]; ring_nf
  rw [heq, Real.rpow_neg hl0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine (factor_bound hw).trans ?_
  rw [norm_div, div_pow]
  have : ‖z‖ ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hz.le 3
  calc 2 * (‖z‖ ^ 3 / ‖l‖ ^ 3) ≤ 2 * (R ^ 3 / ‖l‖ ^ 3) := by gcongr
  _ = 2 * R ^ 3 * (‖l‖ ^ 3)⁻¹ := by ring

/-- **All but finitely many periods have norm `≥ R`.** -/
theorem eventually_le_norm (R : ℝ) : ∀ᶠ l : Λ.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  refine Filter.eventually_cofinite.mpr
    (((isCompact_closedBall (0 : Λ.lattice) R).finite_of_discrete).subset fun l hl => ?_)
  simp only [Set.mem_ofPred_eq, not_le] at hl
  simpa using hl.le

/-- **`Σ_l c‖l‖⁻³` converges** over the lattice. -/
theorem summable_norm_rpow_neg_three (c : ℝ) : Summable fun l : Λ.lattice => c * ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
  (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _

/-- **The product of `σ_W` converges locally uniformly** on every disc about `0`. -/
theorem multipliable_sgFac {R : ℝ} :
    MultipliableLocallyUniformlyOn (fun (l : Λ.lattice) (z : ℂ) => sgFac l z) (Metric.ball 0 R) := by
  have h := Summable.multipliableLocallyUniformlyOn_one_add (f := fun (l : Λ.lattice) (z : ℂ) => sgFac l z - 1)
    (u := fun l : Λ.lattice => 2 * R ^ 3 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) Metric.isOpen_ball (summable_norm_rpow_neg_three Λ _)
    ((eventually_le_norm Λ (2 * R)).mono fun l hl z hz => sgFac_bound (mem_ball_zero_iff.mp hz) hl)
    (fun l => by fun_prop)
  simpa using h

/-- **A factor does not vanish off its period.** -/
theorem sgFac_ne_zero {l z : ℂ} (h : z ≠ l) : sgFac l z ≠ 0 := by
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : l = 0
  · simp [hl]
  · intro h'
    apply h
    have : z / l = 1 := by linear_combination -h'
    field_simp at this
    exact this

/-- **The logarithmic derivative of a factor** is the summand of `ζ_W`, except at `l = 0`, where the factor is `1` and
the summand is `1/z`. -/
theorem logDeriv_sgFac {l z : ℂ} (h : z ≠ l) :
    logDeriv (sgFac l) z = 1 / (z - l) + 1 / l + z / l ^ 2 - if l = 0 then 1 / z else 0 := by
  by_cases hl : l = 0
  · subst hl
    have : sgFac 0 = fun _ => 1 := by ext w; simp [sgFac]
    rw [this, logDeriv_const]
    simp
  · simp only [hl, ite_false, sub_zero]
    have h1 : HasDerivAt (fun w : ℂ => 1 - w / l) (-(1 / l)) z := by
      simpa using ((hasDerivAt_id z).div_const l).const_sub 1
    have h2 : HasDerivAt (fun w : ℂ => w / l + w ^ 2 / (2 * l ^ 2)) (1 / l + 2 * z / (2 * l ^ 2)) z := by
      have := ((hasDerivAt_id z).div_const l).fun_add ((hasDerivAt_pow 2 z).div_const (2 * l ^ 2))
      simpa using this
    have h3 := h1.fun_mul h2.cexp
    have hzl : z - l ≠ 0 := sub_ne_zero.mpr h
    have hzl' : 1 - z / l ≠ 0 := by
      intro e; apply h; have : z / l = 1 := by linear_combination -e
      field_simp at this; exact this
    rw [logDeriv_apply]
    change deriv (fun w => (1 - w / l) * cexp (w / l + w ^ 2 / (2 * l ^ 2))) z / _ = _
    rw [h3.deriv]
    have hE := Complex.exp_ne_zero (z / l + z ^ 2 / (2 * l ^ 2))
    simp only [sgFac]
    field_simp
    ring

/-- **The product of `σ_W` does not vanish off the lattice.** -/
theorem sigma_prod_ne_zero {z : ℂ} (hz : z ∉ Λ.lattice) : ∏' l : Λ.lattice, sgFac l z ≠ 0 := by
  have hz' : ∀ l : Λ.lattice, z ≠ l := fun l h => hz (h ▸ l.2)
  have h := tprod_one_add_ne_zero_of_summable (f := fun l : Λ.lattice => sgFac l z - 1)
    (fun l => by simpa using sgFac_ne_zero (hz' l))
    (Summable.of_norm_bounded_eventually (summable_norm_rpow_neg_three Λ (2 * (‖z‖ + 1) ^ 3)) <|
      (eventually_le_norm Λ (2 * (‖z‖ + 1))).mono fun l hl => by
        simpa using sgFac_bound (by linarith) hl)
  simpa using h

/-- **`σ_W′ = σ_W·ζ_W` off the lattice** (Mathlib's `logDeriv_tprod_eq_tsum` on a disc). -/
theorem hasDerivAt_sigmaW {x : ℂ} (hx : x ∉ Λ.lattice) :
    HasDerivAt (sigmaW Λ) (sigmaW Λ x * zetaW Λ x) x := by
  set R := ‖x‖ + 1
  have hxs : x ∈ Metric.ball (0 : ℂ) R := by simp [R]
  have hx' : ∀ l : Λ.lattice, x ≠ l := fun l h => hx (h ▸ l.2)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  have hmult := multipliable_sgFac Λ (R := R)
  have hPd : DifferentiableAt ℂ (fun z => ∏' l : Λ.lattice, sgFac l z) x := by
    have h := TendstoLocallyUniformlyOn.differentiableOn hmult.hasProdLocallyUniformlyOn
      (.of_forall fun s => by
        simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun l _ => by fun_prop))
      Metric.isOpen_ball
    exact h.differentiableAt (Metric.isOpen_ball.mem_nhds hxs)
  have hP0 := sigma_prod_ne_zero Λ hx
  have hsum : HasSum (fun l : Λ.lattice => logDeriv (sgFac l) x) (zetaW Λ x - 1 / x) := by
    simp only [logDeriv_sgFac (hx' _)]
    have hz : HasSum (fun l : Λ.lattice => 1 / (x - l) + 1 / (l : ℂ) + x / (l : ℂ) ^ 2) (zetaW Λ x) :=
      (hasSumLocallyUniformly_zetaW Λ).hasSum
    convert hz.sub (hasSum_ite_eq (0 : Λ.lattice) (1 / x)) using 2 with l
    simp
  have hlog := logDeriv_tprod_eq_tsum Metric.isOpen_ball hxs (fun l => sgFac_ne_zero (hx' l))
    (fun l => by fun_prop) hsum.summable hmult hP0
  rw [hsum.tsum_eq, logDeriv_apply] at hlog
  have hd := (hasDerivAt_id' x).fun_mul hPd.hasDerivAt
  convert hd using 1
  · ext z; simp [sigmaW]
  · rw [div_eq_iff hP0] at hlog
    change x * (∏' l : Λ.lattice, sgFac l x) * zetaW Λ x = _
    rw [hlog]
    generalize (∏' l : Λ.lattice, sgFac l x) = P
    field_simp
    ring

/-! ## The second-order equation of `℘` and the derivatives of `℘` -/

/-- **The complement of the lattice is connected** (a countable set removed from `ℂ ≅ ℝ²`). -/
theorem isPreconnected_compl : IsPreconnected (Λ.latticeᶜ : Set ℂ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (countable_of_Lindelof_of_discrete (X := Λ.lattice))).isPreconnected

/-- **The second-order equation `℘″ = 6℘² − g₂/2`** off the lattice: differentiate Mathlib's `℘′² = 4℘³ − g₂℘ − g₃` and
cancel `℘′`, which does not vanish identically on the connected complement (else `℘` would be constant there, against
its double pole at `0`). -/
theorem eqOn_deriv_derivWeierstrassP :
    Set.EqOn (deriv ℘'[Λ]) (fun z => 6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) Λ.latticeᶜ := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hP := Λ.analyticOnNhd_weierstrassP
  have hP' := Λ.analyticOnNhd_derivWeierstrassP
  have hP'' := hP'.deriv
  have hmul : ∀ z ∈ (Λ.latticeᶜ : Set ℂ),
      ℘'[Λ] z * (2 * deriv ℘'[Λ] z - (12 * ℘[Λ] z ^ 2 - Λ.g₂)) = 0 := by
    intro z hz
    have hR : (fun w => ℘'[Λ] w ^ 2 - (4 * ℘[Λ] w ^ 3 - Λ.g₂ * ℘[Λ] w - Λ.g₃)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hz] with w hw
      rw [Λ.derivWeierstrassP_sq w hw, sub_self]
    have hd1 : HasDerivAt ℘[Λ] (℘'[Λ] z) z := by
      have := (Λ.differentiableOn_weierstrassP z hz).differentiableAt (hU.mem_nhds hz)
      have h := this.hasDerivAt
      rwa [Λ.deriv_weierstrassP] at h
    have hd2 : HasDerivAt ℘'[Λ] (deriv ℘'[Λ] z) z := (hP' z hz).differentiableAt.hasDerivAt
    have hd := ((hd2.fun_pow 2).fun_sub (((hd1.fun_pow 3).const_mul 4).fun_sub
      (hd1.const_mul Λ.g₂) |>.sub_const Λ.g₃))
    have h0 := hd.deriv
    rw [hR.deriv_eq, deriv_const] at h0
    linear_combination -h0
  have hg : AnalyticOnNhd ℂ (fun z => 2 * deriv ℘'[Λ] z - (12 * ℘[Λ] z ^ 2 - Λ.g₂))
      Λ.latticeᶜ := fun z hz =>
    (analyticAt_const.mul (hP'' z hz)).sub ((analyticAt_const.mul ((hP z hz).pow 2)).sub analyticAt_const)
  rcases hP'.eq_zero_or_eq_zero_of_mul_eq_zero hg hmul (isPreconnected_compl Λ) with h | h
  · exfalso
    have hc : ∀ z ∈ (Λ.latticeᶜ : Set ℂ), ℘[Λ] z = ℘[Λ] (Λ.ω₁ / 2) := fun z hz =>
      hU.is_const_of_deriv_eq_zero (isPreconnected_compl Λ) Λ.differentiableOn_weierstrassP
        (fun w hw => by simpa [Λ.deriv_weierstrassP] using h w hw) hz Λ.ω₁_div_two_notMem_lattice
    have hev : ℘[Λ] =ᶠ[𝓝[≠] 0] fun _ => ℘[Λ] (Λ.ω₁ / 2) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds 0),
        self_mem_nhdsWithin] with z hz hz0
      refine hc z fun hz' => hz ⟨hz', hz0⟩
    have ho := Λ.order_weierstrassP 0 (zero_mem _)
    classical
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_const] at ho
    split_ifs at ho
    · exact absurd ho (by decide)
    · exact absurd ho (by decide)
  · intro z hz
    have := h z hz
    linear_combination this / 2

/-- **`℘` is smooth off the lattice.** -/
theorem contDiffAt_weierstrassP {z : ℂ} (hz : z ∉ Λ.lattice) (n : ℕ) : ContDiffAt ℂ n ℘[Λ] z :=
  (Λ.analyticOnNhd_weierstrassP z hz).contDiffAt

/-- **The derivatives of `℘`** from `℘″ = 6℘² − g₂/2`: `℘^{(n+2)} = −[n = 0]·g₂/2 + 6·Σ_i C(n, i)·℘^{(i)}·℘^{(n−i)}` off
the lattice. -/
theorem iteratedDeriv_weierstrassP_add_two {z : ℂ} (hz : z ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv (n + 2) ℘[Λ] z = (if n = 0 then -(Λ.g₂ / 2) else 0) +
      6 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i ℘[Λ] z *
        iteratedDeriv (n - i) ℘[Λ] z := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  rw [iteratedDeriv_succ', iteratedDeriv_succ', Λ.deriv_weierstrassP]
  have hev : deriv ℘'[Λ] =ᶠ[𝓝 z] fun w => -(Λ.g₂ / 2) + 6 * (℘[Λ] w * ℘[Λ] w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [eqOn_deriv_derivWeierstrassP Λ hw]
    ring
  rw [hev.iteratedDeriv_eq]
  have hcd := contDiffAt_weierstrassP Λ hz n
  rcases n with _ | n
  · simp
  · rw [iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_const_mul _ (hcd.mul hcd),
      iteratedDeriv_fun_mul hcd hcd]
    simp

/-- **`℘^{(n)}(z)` is a polynomial over `ℤ` in `℘(z)`, `℘′(z)` and `g₂/2`**: it lies in every subring of `ℂ` containing
them. -/
theorem iteratedDeriv_weierstrassP_mem {z : ℂ} (hz : z ∉ Λ.lattice) {R : Subring ℂ} (h0 : ℘[Λ] z ∈ R)
    (h1 : ℘'[Λ] z ∈ R) (h2 : Λ.g₂ / 2 ∈ R) (n : ℕ) : iteratedDeriv n ℘[Λ] z ∈ R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using h0
    | 1 => simpa [Λ.deriv_weierstrassP] using h1
    | n + 2 =>
      rw [iteratedDeriv_weierstrassP_add_two Λ hz]
      refine R.add_mem (by split_ifs <;> simp [R.neg_mem h2, R.zero_mem]) (R.mul_mem ?_ ?_)
      · exact_mod_cast natCast_mem R 6
      · refine R.sum_mem fun i hi => R.mul_mem (R.mul_mem (by exact_mod_cast natCast_mem R _) ?_) ?_
        · exact ih i (by simp at hi; omega)
        · exact ih (n - i) (by omega)

/-- **`℘′(t) = 0` at a half-period** (`℘′` is odd and periodic). -/
theorem derivWeierstrassP_half {t : ℂ} (ht : 2 * t ∈ Λ.lattice) : ℘'[Λ] t = 0 := by
  have h := Λ.derivWeierstrassP_sub_coe t ⟨2 * t, ht⟩
  rw [show t - 2 * t = -t by ring, Λ.derivWeierstrassP_neg] at h
  linear_combination -h / 2

/-- **`℘(t)` is a root of `4X³ − g₂X − g₃`** at a half-period `t ∉ Λ`. -/
theorem weierstrassP_half_root {t : ℂ} (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) :
    4 * ℘[Λ] t ^ 3 - Λ.g₂ * ℘[Λ] t - Λ.g₃ = 0 := by
  have h := Λ.derivWeierstrassP_sq t ht'
  rw [derivWeierstrassP_half Λ ht] at h
  linear_combination -h

/-! ## Masser's half-period identity -/

/-- **The area is `Im(ω̄₁ω₂)`** when `Im(ω₂/ω₁) > 0`. -/
theorem area_eq_im (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) : area Λ = (starRingEnd ℂ Λ.ω₁ * Λ.ω₂).im := by
  have h1 : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
  have : (Λ.ω₂ / Λ.ω₁).im = (starRingEnd ℂ Λ.ω₁ * Λ.ω₂).im / Complex.normSq Λ.ω₁ := by
    rw [Complex.div_im, Complex.mul_im]; simp [Complex.conj_re, Complex.conj_im]; ring
  rw [this] at hor
  have hpos : 0 < (starRingEnd ℂ Λ.ω₁ * Λ.ω₂).im :=
    (div_pos_iff_of_pos_right (Complex.normSq_pos.mpr h1)).mp hor
  exact abs_of_pos hpos

/-- **Masser's identity at the basis periods**: `η_i = s₂ω_i + (π/A)·ω̄_i` (from `Legendre`, as `ω₁ω̄₂ − ω₂ω̄₁ = −2iA`).
-/
theorem quasi_period_eq (hL : Legendre) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {ω : ℂ} (hω : ω = Λ.ω₁ ∨ ω = Λ.ω₂) :
    2 * zetaW Λ (ω / 2) = s2 Λ * ω + ((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ ω := by
  have hA := area_eq_im Λ hor
  have hApos : 0 < area Λ := ChainCanon.area_pos Λ
  have hD : Λ.ω₁ * starRingEnd ℂ Λ.ω₂ - Λ.ω₂ * starRingEnd ℂ Λ.ω₁ = -2 * Complex.I * (area Λ : ℂ) := by
    rw [hA]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hleg := hL Λ hor
  have hA0 : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hD0 : Λ.ω₁ * starRingEnd ℂ Λ.ω₂ - Λ.ω₂ * starRingEnd ℂ Λ.ω₁ ≠ 0 := by
    rw [hD]; simp [hA0, Complex.I_ne_zero]
  set cπ : ℂ := ((Real.pi / area Λ : ℝ) : ℂ) with hcπ
  have hcA : cπ * (area Λ : ℂ) = Real.pi := by rw [hcπ]; push_cast; field_simp
  have key : s2 Λ * ω = (2 * zetaW Λ (ω / 2) - cπ * starRingEnd ℂ ω) := by
    simp only [s2]
    rw [div_mul_eq_mul_div, div_eq_iff hD0]
    rcases hω with rfl | rfl
    · linear_combination (starRingEnd ℂ Λ.ω₁) * hleg + cπ * (starRingEnd ℂ Λ.ω₁) * hD +
        (-2 * Complex.I * starRingEnd ℂ Λ.ω₁) * hcA
    · linear_combination (starRingEnd ℂ Λ.ω₂) * hleg + cπ * (starRingEnd ℂ Λ.ω₂) * hD +
        (-2 * Complex.I * starRingEnd ℂ Λ.ω₂) * hcA
  rw [key]
  ring

/-- **Translating by a period keeps a point off the lattice.** -/
theorem add_mem_compl {z l : ℂ} (hz : z ∉ Λ.lattice) (hl : l ∈ Λ.lattice) : z + l ∉ Λ.lattice :=
  fun h => hz (by simpa using sub_mem h hl)

/-- **`ζ_W(z + l) − ζ_W(z)` does not depend on `z`** for a period `l`: its derivative `℘(z) − ℘(z + l)` vanishes on the
connected complement of the lattice. -/
theorem zetaW_add_sub_const {l : ℂ} (hl : l ∈ Λ.lattice) {z w : ℂ} (hz : z ∉ Λ.lattice) (hw : w ∉ Λ.lattice) :
    zetaW Λ (z + l) - zetaW Λ z = zetaW Λ (w + l) - zetaW Λ w := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  refine hU.is_const_of_deriv_eq_zero (f := fun z => zetaW Λ (z + l) - zetaW Λ z) (isPreconnected_compl Λ)
    ?_ ?_ hz hw
  · exact ((differentiableOn_zetaW Λ).comp (by fun_prop) fun x hx => add_mem_compl Λ hx hl).sub
      (differentiableOn_zetaW Λ)
  · intro x hx
    have h1 := (hasDerivAt_zetaW Λ (add_mem_compl Λ hx hl)).comp_add_const x l
    have h2 := hasDerivAt_zetaW Λ hx
    rw [(h1.fun_sub h2).deriv]
    simp [Λ.weierstrassP_add_coe x ⟨l, hl⟩]

/-- **Quasi-periodicity with Masser's quasi-periods**: `ζ_W(z + l) − ζ_W(z) = s₂l + (π/A)·l̄` for every period `l` and
`z ∉ Λ` (both sides are additive in `l`, and agree at `ω₁`, `ω₂`). -/
theorem zetaW_add_lattice (hL : Legendre) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l : ℂ} (hl : l ∈ Λ.lattice)
    {z : ℂ} (hz : z ∉ Λ.lattice) :
    zetaW Λ (z + l) - zetaW Λ z = s2 Λ * l + ((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l := by
  set c : ℂ := ((Real.pi / area Λ : ℝ) : ℂ)
  let G : AddSubgroup ℂ :=
    { carrier := {l | l ∈ Λ.lattice ∧ ∀ z ∉ Λ.lattice,
        zetaW Λ (z + l) - zetaW Λ z = s2 Λ * l + c * starRingEnd ℂ l}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun z hz => ?_⟩
        have h1 := ha' z hz
        have h2 := hb' (z + a) (add_mem_compl Λ hz ha)
        rw [← add_assoc, map_add]
        linear_combination h1 + h2
      zero_mem' := ⟨zero_mem _, fun z _ => by simp⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun z hz => ?_⟩
        have h := ha' (z + -a) (add_mem_compl Λ hz (neg_mem ha))
        rw [neg_add_cancel_right] at h
        rw [map_neg]
        linear_combination -h }
  have hgen : ∀ ω, (ω = Λ.ω₁ ∨ ω = Λ.ω₂) → ω ∈ G := by
    intro ω hω
    have hωΛ : ω ∈ Λ.lattice := by rcases hω with rfl | rfl; exacts [Λ.ω₁_mem_lattice, Λ.ω₂_mem_lattice]
    have hhalf : ω / 2 ∉ Λ.lattice := by
      rcases hω with rfl | rfl; exacts [Λ.ω₁_div_two_notMem_lattice, Λ.ω₂_div_two_notMem_lattice]
    refine ⟨hωΛ, fun z hz => ?_⟩
    have hmh : -(ω / 2) ∉ Λ.lattice := fun h => hhalf (by simpa using neg_mem h)
    rw [zetaW_add_sub_const Λ hωΛ hz hmh, show -(ω / 2) + ω = ω / 2 by ring, zetaW_neg]
    rw [sub_neg_eq_add, ← two_mul]
    exact quasi_period_eq Λ hL hor hω
  have hle : Λ.lattice ≤ G.toIntSubmodule := by
    rw [PeriodPair.lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hgen _ (Or.inl rfl)
    · exact hgen _ (Or.inr rfl)
  exact (hle hl).2 z hz

/-- **Masser's half-period identity** (from `Legendre`): `ζ_W(t) − s₂t − (π/A)·t̄ = 0` at every half-period `t`, with
the orientation `Im(ω₂/ω₁) > 0`. -/
theorem zetaW_half (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) :
    zetaW Λ t - s2 Λ * t - (Real.pi / area Λ : ℝ) * (starRingEnd ℂ) t = 0 := by
  have hmt : -t ∉ Λ.lattice := fun h => ht' (by simpa using neg_mem h)
  have h := zetaW_add_lattice Λ hL hor ht hmt
  rw [show -t + 2 * t = t by ring, zetaW_neg, map_mul, map_ofNat] at h
  linear_combination h / 2

/-! ## The theta and its jet recursion -/

/-- **`σ_W` does not vanish off the lattice.** -/
theorem sigmaW_ne_zero {x : ℂ} (hx : x ∉ Λ.lattice) : sigmaW Λ x ≠ 0 :=
  mul_ne_zero (fun h => hx (h ▸ zero_mem _)) (sigma_prod_ne_zero Λ hx)

/-- **`σ*′ = σ*·(ζ_W − s₂z)`** off the lattice. -/
theorem hasDerivAt_sgStar {x : ℂ} (hx : x ∉ Λ.lattice) :
    HasDerivAt (sgStar Λ) (sgStar Λ x * (zetaW Λ x - s2 Λ * x)) x := by
  have h1 := hasDerivAt_sigmaW Λ hx
  have h2 : HasDerivAt (fun z => -(s2 Λ) * z ^ 2 / 2) (-(s2 Λ) * (2 * x) / 2) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul (-(s2 Λ))).div_const 2
  have hs : sgStar Λ = fun z => sigmaW Λ z * cexp (-(s2 Λ) * z ^ 2 / 2) := rfl
  rw [hs]
  convert h1.fun_mul h2.cexp using 1
  ring

/-- **The one-variable normalised theta of a lattice at `t`**: the library's `th0` with `s = 1/area` and `σ = σ*`. -/
def th0L (Λ : PeriodPair) (t : ℂ) : ℂ → ℂ := th0 (area Λ)⁻¹ (sgStar Λ) t

/-- **The logarithmic derivative of `th0L`**: `ζ_W(z + t) − s₂(z + t) − (π/A)·t̄`. -/
def logDer (Λ : PeriodPair) (t z : ℂ) : ℂ :=
  zetaW Λ (z + t) - s2 Λ * (z + t) - ((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t

/-- **`th0` explicitly**: `th0(z) = σ*(z + t)·exp(−(π/A)·t̄·z)/σ*(t)`. -/
theorem th0L_eq (t z : ℂ) :
    th0L Λ t z = sgStar Λ (z + t) * cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * z) /
      sgStar Λ t := by
  simp only [th0L, th0, opU, Hf, Finset.univ_unique, Finset.sum_singleton, Pi.add_apply, Pi.zero_apply,
    zero_add, zero_mul, mul_zero]
  have hE : ∀ a b : ℂ, cexp (a - b) = cexp a * cexp (-b) := fun a b => by rw [← Complex.exp_add]; ring_nf
  rw [hE, zero_sub, ← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
  congr 3
  push_cast
  ring

/-- **`th0′ = th0·logDer`** where `z + t ∉ Λ`. -/
theorem hasDerivAt_th0L {t z : ℂ} (hz : z + t ∉ Λ.lattice) :
    HasDerivAt (th0L Λ t) (th0L Λ t z * logDer Λ t z) z := by
  have h1 := (hasDerivAt_sgStar Λ hz).comp_add_const z t
  have h2 : HasDerivAt (fun z => cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * z))
      (cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * z) *
        -(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t)) z := by
    simpa using ((hasDerivAt_id z).const_mul (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t))).cexp
  have h := (h1.fun_mul h2).div_const (sgStar Λ t)
  have heq : th0L Λ t = fun z => sgStar Λ (z + t) *
      cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * z) / sgStar Λ t :=
    funext (th0L_eq Λ t)
  rw [heq]
  convert h using 1
  simp only [logDer]
  ring

/-- **`th0(0) = 1`** for `t ∉ Λ`. -/
theorem th0L_zero {t : ℂ} (ht : t ∉ Λ.lattice) : th0L Λ t 0 = 1 := by
  rw [th0L_eq]
  simp only [zero_add, mul_zero, Complex.exp_zero, mul_one]
  refine div_self (mul_ne_zero (sigmaW_ne_zero Λ ht) (Complex.exp_ne_zero _))

/-- **`{z : z + t ∉ Λ}` is open.** -/
theorem isOpen_shift (t : ℂ) : IsOpen {z : ℂ | z + t ∉ Λ.lattice} :=
  Λ.isClosed_lattice.isOpen_compl.preimage (by fun_prop)

/-- **`th0` is smooth at `0`** for `t ∉ Λ`. -/
theorem contDiffAt_th0L {t : ℂ} (ht : t ∉ Λ.lattice) (n : ℕ) : ContDiffAt ℂ n (th0L Λ t) 0 := by
  have hd : DifferentiableOn ℂ (th0L Λ t) {z : ℂ | z + t ∉ Λ.lattice} := fun z hz =>
    (hasDerivAt_th0L Λ hz).differentiableAt.differentiableWithinAt
  exact (hd.analyticAt ((isOpen_shift Λ t).mem_nhds (by simpa using ht))).contDiffAt

/-- **`logDer′ = −℘(z + t) − s₂`** where `z + t ∉ Λ`. -/
theorem hasDerivAt_logDer {t z : ℂ} (hz : z + t ∉ Λ.lattice) :
    HasDerivAt (logDer Λ t) (-℘[Λ] (z + t) - s2 Λ) z := by
  have h1 := (hasDerivAt_zetaW Λ hz).comp_add_const z t
  have h2 : HasDerivAt (fun z => s2 Λ * (z + t)) (s2 Λ) z := by
    simpa using ((hasDerivAt_id z).add_const t).const_mul (s2 Λ)
  exact (h1.fun_sub h2).sub_const _

/-- **`logDer` is smooth at `0`** for `t ∉ Λ`. -/
theorem contDiffAt_logDer {t : ℂ} (ht : t ∉ Λ.lattice) (n : ℕ) : ContDiffAt ℂ n (logDer Λ t) 0 := by
  have hd : DifferentiableOn ℂ (logDer Λ t) {z : ℂ | z + t ∉ Λ.lattice} := fun z hz =>
    (hasDerivAt_logDer Λ hz).differentiableAt.differentiableWithinAt
  exact (hd.analyticAt ((isOpen_shift Λ t).mem_nhds (by simpa using ht))).contDiffAt

/-- **The jet recursion** (Leibniz's rule on `th0′ = th0·logDer`):
`∂^{n+1}th0(0) = Σ_i C(n, i)·∂^i th0(0)·∂^{n−i}logDer(0)`. -/
theorem iteratedDeriv_th0L_succ {t : ℂ} (ht : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv (n + 1) (th0L Λ t) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i (th0L Λ t) 0 * iteratedDeriv (n - i) (logDer Λ t) 0 := by
  have hev : deriv (th0L Λ t) =ᶠ[𝓝 0] th0L Λ t * logDer Λ t := by
    filter_upwards [(isOpen_shift Λ t).mem_nhds (by simpa using ht)] with z hz
    exact (hasDerivAt_th0L Λ hz).deriv
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_mul (contDiffAt_th0L Λ ht n)
    (contDiffAt_logDer Λ ht n)]

/-- **The derivatives of `logDer`**: `∂^{n+1}logDer(0) = −℘^{(n)}(t) − [n = 0]·s₂`. -/
theorem iteratedDeriv_logDer_succ {t : ℂ} (ht : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv (n + 1) (logDer Λ t) 0 = -iteratedDeriv n ℘[Λ] t - if n = 0 then s2 Λ else 0 := by
  have hev : deriv (logDer Λ t) =ᶠ[𝓝 0] fun z => -(s2 Λ + ℘[Λ] (z + t)) := by
    filter_upwards [(isOpen_shift Λ t).mem_nhds (by simpa using ht)] with z hz
    rw [(hasDerivAt_logDer Λ hz).deriv]; ring
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_fun_neg]
  rcases n with _ | n
  · simp; ring
  · rw [iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_comp_add_const]
    simp

/-! ## The jets are polynomials over `ℤ` in `g₂/2`, `℘(t)`, `s₂` -/

variable {Λ} in
/-- **`logDer(0) = 0`** at a half-period: Masser's half-period identity. -/
theorem logDer_zero (hL : Legendre) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {t : ℂ} (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) : logDer Λ t 0 = 0 := by
  simpa [logDer] using zetaW_half hL Λ hor t ht ht'

variable {Λ} in
/-- **The derivatives of `logDer` at `0` are polynomials over `ℤ` in `g₂/2`, `℘(t)`, `s₂`.** -/
theorem iteratedDeriv_logDer_mem (hL : Legendre) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {t : ℂ}
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) {R : Subring ℂ} (h2 : Λ.g₂ / 2 ∈ R) (hp : ℘[Λ] t ∈ R)
    (hs : s2 Λ ∈ R) (n : ℕ) : iteratedDeriv n (logDer Λ t) 0 ∈ R := by
  rcases n with _ | n
  · simp [logDer_zero hL hor ht ht']
  · rw [iteratedDeriv_logDer_succ Λ ht']
    refine R.sub_mem (R.neg_mem (iteratedDeriv_weierstrassP_mem Λ ht' hp
      (by rw [derivWeierstrassP_half Λ ht]; exact R.zero_mem) h2 n)) ?_
    split_ifs
    exacts [hs, R.zero_mem]

/-- **The jets of `th0` are polynomials over `ℤ` in `g₂/2`, `℘(t)`, `s₂`**: at a half-period, every `∂^n th0(0)` lies in
every subring of `ℂ` containing these three numbers (`g₃` does not enter). -/
theorem th0_jets_mem (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) {R : Subring ℂ} (h2 : Λ.g₂ / 2 ∈ R)
    (hp : Λ.weierstrassP t ∈ R) (hs : s2 Λ ∈ R) (n : ℕ) : iteratedDeriv n (th0L Λ t) 0 ∈ R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [th0L_zero Λ ht']
    · rw [iteratedDeriv_th0L_succ Λ ht' n]
      refine R.sum_mem fun i hi => R.mul_mem (R.mul_mem (by exact_mod_cast natCast_mem R _)
        (ih i (by simp at hi; omega))) (iteratedDeriv_logDer_mem hL hor ht ht' h2 hp hs _)

/-- **The jets of `th0` lie in `ℤ[g₂/2, ℘(t), s₂]`** (the subring these generate). -/
theorem th0_jets_mem_closure (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 ∈ Subring.closure {Λ.g₂ / 2, Λ.weierstrassP t, s2 Λ} :=
  th0_jets_mem hL Λ hor t ht ht' (Subring.subset_closure (by simp)) (Subring.subset_closure (by simp))
    (Subring.subset_closure (by simp)) n

/-! ## The Hurwitz formula -/

/-- **The exponent series** `−s₂z²/2 − Σ_{n≥0} ℘^{(n)}(t)·z^{n+2}/(n+2)!` of `th0`. -/
def logTh0 (Λ : PeriodPair) (t : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    (if n = 2 then -s2 Λ / 2 else 0) -
      (if 2 ≤ n then iteratedDeriv (n - 2) Λ.weierstrassP t / (n.factorial : ℂ) else 0)

variable {Λ} in
/-- **The Hurwitz coefficients of `logTh0` are the derivatives of `logDer`**:
`(j + 1)!·[z^{j+1}]logTh0 = ∂^j logDer(0)`. -/
theorem hurwitz_logTh0 (hL : Legendre) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {t : ℂ} (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) (j : ℕ) :
    ((j + 1).factorial : ℂ) * PowerSeries.coeff (j + 1) (logTh0 Λ t) = iteratedDeriv j (logDer Λ t) 0 := by
  rcases j with _ | m
  · simp [logTh0, logDer_zero hL hor ht ht']
  · have h2 : 2 ≤ m + 1 + 1 := by omega
    rw [iteratedDeriv_logDer_succ Λ ht', logTh0, PowerSeries.coeff_mk, show m + 1 + 1 - 2 = m by omega]
    simp only [h2, ite_true]
    have hf : ((m + 1 + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (m + 1 + 1).factorial_ne_zero
    rcases m with _ | m
    · simp; ring
    · simp only [show m + 1 + 1 + 1 ≠ 2 by omega, ite_false, show m + 1 ≠ 0 by omega]
      field_simp
      ring

/-- **The Hurwitz formula for `th0`** (D1a's core identity): `th0 = exp(logTh0)` as Taylor series at `0`, i.e.
`∂^n th0(0) = n!·[zⁿ]exp(logTh0)`. -/
theorem th0_taylor (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 =
      (n.factorial : ℂ) * PowerSeries.coeff n ((PowerSeries.exp ℂ).subst (logTh0 Λ t)) := by
  set E := (PowerSeries.exp ℂ).subst (logTh0 Λ t) with hE
  have h0 : PowerSeries.constantCoeff (logTh0 Λ t) = 0 := by
    simp [logTh0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hsub : PowerSeries.HasSubst (logTh0 Λ t) := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hder : PowerSeries.derivative E = E * PowerSeries.derivative (logTh0 Λ t) := by
    rw [hE, PowerSeries.derivative_subst hsub, PowerSeries.derivative_exp]
  have hE0 : PowerSeries.coeff 0 E = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE]
    exact (PowerSeries.constantCoeff_subst_of_constantCoeff_zero h0 (PowerSeries.exp ℂ)).trans (by simp)
  have hrec : ∀ n : ℕ, PowerSeries.coeff (n + 1) E * ((n : ℂ) + 1) = ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff i E * (PowerSeries.coeff (n - i + 1) (logTh0 Λ t) * ((n - i : ℕ) + 1 : ℂ)) := by
    intro n
    have := congrArg (PowerSeries.coeff n) hder
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_derivative]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [th0L_zero Λ ht', hE0]
    · rw [iteratedDeriv_th0L_succ Λ ht' n, show ((n + 1).factorial : ℂ) * PowerSeries.coeff (n + 1) E =
          n.factorial * (PowerSeries.coeff (n + 1) E * ((n : ℂ) + 1)) by push_cast [Nat.factorial_succ]; ring,
        hrec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi : i ≤ n := by simp at hi; omega
      rw [ih i (by omega), ← hurwitz_logTh0 hL hor ht ht', show n - i + 1 = (n - i) + 1 from rfl]
      rw [← Nat.choose_mul_factorial_mul_factorial hi, Nat.factorial_succ (n - i)]
      push_cast
      ring

/-! ## Consequences: `σ₀`-rationality, algebraicity, `ℓ`-integrality -/

/-- **The jets of `th0` lie in `σ₀(K)`** when `g₂`, `℘(t)`, `s₂` do (the shape of `Data.JetsRat`). -/
theorem th0_jets_mem_range (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) {K : Type*} [Field K] (σ₀ : K →+* ℂ)
    (h2 : Λ.g₂ ∈ Set.range σ₀) (hp : Λ.weierstrassP t ∈ Set.range σ₀) (hs : s2 Λ ∈ Set.range σ₀) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 ∈ Set.range σ₀ := by
  have hmem : ∀ x, x ∈ σ₀.fieldRange.toSubring ↔ x ∈ Set.range σ₀ := fun x => RingHom.mem_fieldRange
  rw [← hmem] at h2 hp hs ⊢
  refine th0_jets_mem hL Λ hor t ht ht' ?_ hp hs n
  exact σ₀.fieldRange.div_mem h2 (by simp)

/-- **The jets of `th0` are algebraic** when `g₂`, `℘(t)`, `s₂` are. -/
theorem th0_jets_isAlgebraic (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) (h2 : IsAlgebraic ℚ Λ.g₂)
    (hp : IsAlgebraic ℚ (Λ.weierstrassP t)) (hs : IsAlgebraic ℚ (s2 Λ)) (n : ℕ) :
    IsAlgebraic ℚ (iteratedDeriv n (th0L Λ t) 0) := by
  refine th0_jets_mem hL Λ hor t ht ht' (R := (Subalgebra.algebraicClosure ℚ ℂ).toSubring) ?_ hp hs n
  rw [div_eq_mul_inv, show (2⁻¹ : ℂ) = algebraMap ℚ ℂ 2⁻¹ by simp]
  exact Subalgebra.mul_mem _ h2 (Subalgebra.algebraMap_mem _ _)

section Int

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The `ι`-integral numbers** `{x : ‖ι x‖ ≤ 1}`, a subring of `ℂ` (for `ι` into a nonarchimedean field). -/
def intSub (ι : ℂ →+* K) : Subring ℂ where
  carrier := {x | ‖ι x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, norm_mul] at ha hb ⊢
    exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans (by norm_num)
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/-- **Membership in `intSub`.** -/
theorem mem_intSub {ι : ℂ →+* K} {x : ℂ} : x ∈ intSub ι ↔ ‖ι x‖ ≤ 1 := Iff.rfl

/-- **A root of a monic integer polynomial has norm `≤ 1`** in a nonarchimedean field. -/
theorem norm_le_one_of_monic {x : K} {p : Polynomial ℤ} (hpm : p.Monic)
    (hpx : Polynomial.eval₂ (Int.castRingHom K) x p = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  rw [hpm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hpx
  set n := p.natDegree
  have hb : ‖∑ i ∈ Finset.range n, Polynomial.eval₂ (Int.castRingHom K) x (Polynomial.C (p.coeff i) *
      Polynomial.X ^ i)‖ ≤ ‖x‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow, eq_intCast]
    have hi' : i ≤ n - 1 := by simp at hi; omega
    calc ‖((p.coeff i : ℤ) : K)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) := by
          gcongr
          · exact IsUltrametricDist.norm_intCast_le_one K _
          · exact hlt.le
    _ = ‖x‖ ^ (n - 1) := one_mul _
  have heq : ‖x‖ ^ n = ‖∑ i ∈ Finset.range n, Polynomial.eval₂ (Int.castRingHom K) x (Polynomial.C (p.coeff i) *
      Polynomial.X ^ i)‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left hpx, norm_neg]
  rcases hn : n with _ | m
  · rw [hn] at hpx; simp at hpx
  · rw [hn] at heq hb
    have := pow_lt_pow_right₀ hlt (lt_add_one m)
    simp only [Nat.add_sub_cancel] at hb
    linarith

/-- **An algebraic integer is `ι`-integral** for every ring map `ι` from `ℂ` to a nonarchimedean field. -/
theorem norm_le_one_of_isIntegral (ι : ℂ →+* K) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨p, hpm, hpx⟩ := hx
  refine norm_le_one_of_monic hpm ?_
  have := congrArg ι hpx
  rwa [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (ι.comp (algebraMap ℤ ℂ)) (Int.castRingHom K)] at this

/-- **`‖n‖ = 1` in `ℂ_ℓ`** for `n` prime to `ℓ`. -/
theorem norm_natCast_padicComplex {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (h : ℓ.Coprime n) : ‖(n : ℂ_[ℓ])‖ = 1 := by
  have := PadicComplex.norm_extends' ℓ (n : ℚ_[ℓ])
  rw [map_natCast, PadicComplex.coe_natCast] at this
  rw [this, Padic.norm_natCast_eq_one_iff]
  exact h

end Int

/-- **The jets of `th0` are `ℓ`-integral** at every prime `ℓ ≠ 2` where `g₂`, `℘(t)`, `s₂` are, for any ring map
`ι : ℂ → ℂ_ℓ` (the generic row and C1's integrality, one variable). -/
theorem th0_jets_int (hL : Legendre) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ)
    (ht : 2 * t ∈ Λ.lattice) (ht' : t ∉ Λ.lattice) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {F : Type*}
    [FunLike F ℂ ℂ_[ℓ]] [RingHomClass F ℂ ℂ_[ℓ]] (ι : F) (h2 : ‖ι Λ.g₂‖ ≤ 1)
    (hp : ‖ι (Λ.weierstrassP t)‖ ≤ 1) (hs : ‖ι (s2 Λ)‖ ≤ 1) (n : ℕ) :
    ‖ι (iteratedDeriv n (th0L Λ t) 0)‖ ≤ 1 := by
  have h2' : ‖((2 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    norm_natCast_padicComplex ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hℓ)
  refine th0_jets_mem hL Λ hor t ht ht' (R := intSub (ι : ℂ →+* ℂ_[ℓ])) ?_
    (mem_intSub.mpr (by simpa using hp)) (mem_intSub.mpr (by simpa using hs)) n
  have e2 : ι 2 = ((2 : ℕ) : ℂ_[ℓ]) := by rw [map_ofNat, Nat.cast_ofNat]
  rw [mem_intSub, RingHom.coe_coe, map_div₀, norm_div, e2, h2', div_one]
  exact h2

/-! ## The canonical CM lattice -/

/-- **`sd = √d/2 > 0`** for `d ≡ 3 (mod 4)`. -/
theorem sd_pos {d : ℕ} (hd4 : d % 4 = 3) {sd : ℝ} (hsd : sd = Real.sqrt d / 2) : 0 < sd := by
  have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [hsd]; positivity

/-- **The canonical lattice has CM**: `ω·Lc ⊆ Lc` for `ω = (1 + √−d)/2`, as `ω² = ω − (d + 1)/4`. -/
theorem hasCM_cmLat {d : ℕ} (hd4 : d % 4 = 3) {sd : ℝ} (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) : HasCM d (cmLat sd) := by
  obtain ⟨h1, h2⟩ := cmLat_ω (sd_pos hd4 hsd).ne' hΔ
  have hsq : (sd : ℂ) ^ 2 * 4 = d := by
    have : sd ^ 2 * 4 = d := by rw [hsd, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; ring
    exact_mod_cast this
  obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
  have hk' : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  have hω : (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 = omegaD sd := by
    simp only [omegaD, hsd]; push_cast; ring
  have hle : (cmLat sd).lattice ≤ (cmLat sd).lattice.comap (LinearMap.mulLeft ℤ (omegaD sd)) := by
    conv_lhs => rw [PeriodPair.lattice]
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, h1]
      rw [mul_comm, ← h2]; exact (cmLat sd).ω₂_mem_lattice
    · simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, h2]
      have : omegaD sd * (deltaC sd * omegaD sd) = (cmLat sd).ω₂ - (k : ℤ) • (cmLat sd).ω₁ := by
        rw [h1, h2, zsmul_eq_mul, omegaD]
        push_cast
        linear_combination (deltaC sd * sd ^ 2) * Complex.I_sq - (deltaC sd / 4) * hk' - (deltaC sd / 4) * hsq
      rw [this]
      exact sub_mem (cmLat sd).ω₂_mem_lattice (zsmul_mem (cmLat sd).ω₁_mem_lattice _)
  intro z hz
  rw [hω]
  exact hle hz

/-- **The canonical lattice and point satisfy the hypotheses of the Hurwitz formula**: `Im(ω₂/ω₁) > 0`, `t = δ/2` is a
half-period off the lattice, and `Δ(Lc) = 1`. -/
theorem canon_data {sd : ℝ} (hsd : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) :
    0 < ((cmLat sd).ω₂ / (cmLat sd).ω₁).im ∧ 2 * tC sd ∈ (cmLat sd).lattice ∧ tC sd ∉ (cmLat sd).lattice ∧
      (cmLat sd).g₂ ^ 3 - 27 * (cmLat sd).g₃ ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := cmLat_ω hsd.ne' hΔ
  refine ⟨?_, (tC_spec hsd.ne' hΔ).1, ?_, discr_cmLat hsd.ne' hΔ⟩
  · rw [h1, h2, mul_div_cancel_left₀ _ (deltaC_ne_zero hΔ)]
    simpa [omegaD] using hsd
  · have := (cmLat sd).ω₁_div_two_notMem_lattice
    rwa [h1] at this

section Alg

/-- **A root of `4X³ − aX − b` with `a`, `b` algebraic is algebraic.** -/
theorem isAlgebraic_root {a b p : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (h : 4 * p ^ 3 - a * p - b = 0) : IsAlgebraic ℚ p := by
  let S := Subalgebra.algebraicClosure ℚ ℂ
  let q : Polynomial S := 4 * Polynomial.X ^ 3 - Polynomial.C ⟨a, ha⟩ * Polynomial.X -
    Polynomial.C ⟨b, hb⟩
  have hq : q.coeff 3 = 4 := by simp [q]
  refine IsAlgebraic.restrictScalars (R := ℚ) (S := S) ⟨q, fun h0 => ?_, ?_⟩
  · rw [h0, Polynomial.coeff_zero] at hq
    exact absurd hq.symm (by norm_num)
  · simpa [q, map_ofNat (Polynomial.aeval p) 4] using h

/-- **A root of `4X³ − aX − b` is integral** when `a`, `b` are and `‖4‖ = 1` (nonarchimedean). -/
theorem norm_root_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {a b p : K} (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) (h4 : ‖(4 : K)‖ = 1) (h : 4 * p ^ 3 - a * p - b = 0) : ‖p‖ ≤ 1 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have heq : 4 * p ^ 3 = a * p + b := by linear_combination h
  have h1 : ‖4 * p ^ 3‖ = ‖p‖ ^ 3 := by rw [norm_mul, h4, one_mul, norm_pow]
  have h2 : ‖a * p + b‖ ≤ ‖p‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hb.trans hlt.le))
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg p]
  have h3 : ‖p‖ < ‖p‖ ^ 3 := by
    calc ‖p‖ = ‖p‖ ^ 1 := (pow_one _).symm
    _ < ‖p‖ ^ 3 := pow_lt_pow_right₀ hlt (by norm_num)
  rw [heq] at h1
  linarith

/-- **A prime `ℓ ≥ 5` is prime to `2^a·3^b`.** -/
theorem coprime_two_three {ℓ : ℕ} (hp : ℓ.Prime) (hℓ : 5 ≤ ℓ) (a b : ℕ) : ℓ.Coprime (2 ^ a * 3 ^ b) :=
  Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two |>.mpr (by omega)).pow_right _)
    ((Nat.coprime_primes hp Nat.prime_three |>.mpr (by omega)).pow_right _)

end Alg

/-- **The canonical jets are algebraic** (from Legendre, CM-c and CM-d): every `∂^n th0(0)` of the canonical
one-variable theta at `t = δ/2` is an algebraic number (`g₂`, `g₃` from `j` and `Δ = 1`, and `℘(t)` a root of
`4X³ − g₂X − g₃`). -/
theorem canon_jets_isAlgebraic (hL : Legendre) (hj : CMjIntegral) (hs : CMs2) {d : ℕ} (hd : Squarefree d)
    (hd4 : d % 4 = 3) {sd : ℝ} (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (n : ℕ) :
    IsAlgebraic ℚ (iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0) := by
  obtain ⟨hor, ht, ht', h1⟩ := canon_data (sd_pos hd4 hsd) hΔ
  have hCM := hasCM_cmLat hd4 hsd hΔ
  set Λ := cmLat sd
  let A := Subalgebra.algebraicClosure ℚ ℂ
  have hjΛ : IsIntegral ℤ (1728 * Λ.g₂ ^ 3) := by simpa [h1] using hj d Λ hd hd4 hCM
  have hjA : 1728 * Λ.g₂ ^ 3 ∈ A := (hjΛ.tower_top (A := ℚ)).isAlgebraic
  have hg2 : Λ.g₂ ∈ A := by
    refine IsAlgebraic.of_pow (n := 3) (by norm_num) ?_
    rw [show Λ.g₂ ^ 3 = 1728 * Λ.g₂ ^ 3 * algebraMap ℚ ℂ (1728⁻¹) by simp; ring]
    exact A.mul_mem hjA (A.algebraMap_mem _)
  have hg3 : Λ.g₃ ∈ A := by
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rw [show Λ.g₃ ^ 2 = (Λ.g₂ ^ 3 - 1) * algebraMap ℚ ℂ (27⁻¹) by simp; linear_combination -h1 / 27]
    exact A.mul_mem (A.sub_mem (A.pow_mem hg2 3) A.one_mem) (A.algebraMap_mem _)
  have hp : IsAlgebraic ℚ (Λ.weierstrassP (tC sd)) :=
    isAlgebraic_root hg2 hg3 (weierstrassP_half_root Λ ht ht')
  exact th0_jets_isAlgebraic hL Λ hor (tC sd) ht ht' hg2 hp (hs d Λ hd hd4 hCM h1).1 n

/-- **The canonical jets are `ℓ`-integral** at every prime `ℓ ≥ 5`, `ℓ ∤ d` (from Legendre, CM-c and CM-d: `1728g₂³ = j`
and `46656g₃² = j − 1728` are integral and `1728`, `46656` are `ℓ`-units). -/
theorem canon_jets_int (hL : Legendre) (hj : CMjIntegral) (hs : CMs2) {d : ℕ} (hd : Squarefree d)
    (hd4 : d % 4 = 3) {sd : ℝ} (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hℓd : ¬ ℓ ∣ d) (ι : ℂ ≃+* ℂ_[ℓ]) (n : ℕ) :
    ‖ι (iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0)‖ ≤ 1 := by
  obtain ⟨hor, ht, ht', h1⟩ := canon_data (sd_pos hd4 hsd) hΔ
  have hCM := hasCM_cmLat hd4 hsd hΔ
  set Λ := cmLat sd
  have hpr : ℓ.Prime := Fact.out
  have hjΛ : IsIntegral ℤ (1728 * Λ.g₂ ^ 3) := by simpa [h1] using hj d Λ hd hd4 hCM
  have hjι : ‖ι (1728 * Λ.g₂ ^ 3)‖ ≤ 1 := norm_le_one_of_isIntegral (ι : ℂ →+* ℂ_[ℓ]) hjΛ
  have hn1728 : ‖((1728 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    norm_natCast_padicComplex (by simpa using coprime_two_three hpr hℓ 6 3)
  have hn46656 : ‖((46656 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    norm_natCast_padicComplex (by simpa using coprime_two_three hpr hℓ 6 6)
  have hn4 : ‖((4 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    norm_natCast_padicComplex (by simpa using coprime_two_three hpr hℓ 2 0)
  have e1728 : ι 1728 = ((1728 : ℕ) : ℂ_[ℓ]) := by rw [map_ofNat ι 1728, Nat.cast_ofNat]
  have hg2 : ‖ι Λ.g₂‖ ≤ 1 := by
    rw [map_mul, map_pow, norm_mul, norm_pow, e1728, hn1728, one_mul] at hjι
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hjι
  have hg3 : ‖ι Λ.g₃‖ ≤ 1 := by
    have heq : ι (46656 * Λ.g₃ ^ 2) = ι (1728 * Λ.g₂ ^ 3) - ((1728 : ℕ) : ℂ_[ℓ]) := by
      rw [show (46656 : ℂ) * Λ.g₃ ^ 2 = 1728 * Λ.g₂ ^ 3 - 1728 by linear_combination -1728 * h1, map_sub,
        e1728]
    have hle : ‖ι (46656 * Λ.g₃ ^ 2)‖ ≤ 1 := by
      rw [heq]
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hjι (by rw [norm_neg]; exact hn1728.le))
    have e46656 : ι 46656 = ((46656 : ℕ) : ℂ_[ℓ]) := by rw [map_ofNat ι 46656, Nat.cast_ofNat]
    rw [map_mul, map_pow, norm_mul, norm_pow, e46656, hn46656, one_mul] at hle
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hle
  have hp : ‖ι (Λ.weierstrassP (tC sd))‖ ≤ 1 := by
    refine norm_root_le_one hg2 hg3 (by simpa using hn4) ?_
    have := congrArg ι (weierstrassP_half_root Λ ht ht')
    simpa [map_ofNat ι 4] using this
  exact th0_jets_int hL Λ hor (tC sd) ht ht' ℓ (by omega) ι hg2 hp (((hs d Λ hd hd4 hCM h1).2 ℓ hℓ ι).1 hℓd) n

/-- **The canonical jets lie in `σ₀(K)`** when `g₂`, `℘(t)` and `s₂` of the canonical lattice do (the shape of
`Data.JetsRat`). -/
theorem canon_jets_mem_range (hL : Legendre) {sd : ℝ} (hsd : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) {K : Type*}
    [Field K] (σ₀ : K →+* ℂ) (h2 : (cmLat sd).g₂ ∈ Set.range σ₀)
    (hp : (cmLat sd).weierstrassP (tC sd) ∈ Set.range σ₀) (hs : s2 (cmLat sd) ∈ Set.range σ₀) (n : ℕ) :
    iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0 ∈ Set.range σ₀ := by
  obtain ⟨hor, ht, ht', -⟩ := canon_data hsd hΔ
  exact th0_jets_mem_range hL (cmLat sd) hor (tC sd) ht ht' σ₀ h2 hp hs n

end

end CMThetaOne
