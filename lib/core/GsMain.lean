import Mathlib
import GsUpper
import OddMargin2
import WeilGen

/-! # The ground state of the Weil form at `L = 1/2` (min-max form)

`v = fx 10 xv` (explicit even Legendre mode sum, rational data). On the test class `WeilGen.TestFn`
(`C¹` functions supported in `[−1/2, 1/2]`):

* `Q(v) ≤ μ₁‖v‖²` with `μ₁ = 2·10⁻⁵` (`GsUpper.trial_upper`);
* `Q(f) + c·⟨f, v⟩² ≥ μ₂‖f‖²` for every test function `f`, `μ₂ = 4·10⁻⁵`, `c = cg ≈ 0.62`;
  in particular `Q(f) ≥ μ₂‖f‖²` for `f ⊥ v`, and for every odd `f`;
* hence (min-max) every two-dimensional span of test functions contains `h ≠ 0`-direction with `Q(h) ≥ μ₂‖h‖²`.

Here `Q = weilQg (1/2)`, `‖f‖² = ∫ f²`, `⟨f, v⟩ = ∫ f v`. -/

namespace GsMain

open Real Finset MeasureTheory Filter Topology WeilForm WeilPlanch WeilTail WeilTailB WeilHead GsGap

noncomputable def v : ℝ → ℝ := fx 10 xv

noncomputable def μ₁ : ℝ := 2 / 10 ^ 5
noncomputable def μ₂ : ℝ := 4 / 10 ^ 5

noncomputable def ip (f g : ℝ → ℝ) : ℝ := ∫ t, f t * g t

lemma μ₁_lt_μ₂ : μ₁ < μ₂ := by unfold μ₁ μ₂; norm_num

/-- the even gap without the orthogonality constraint -/
lemma even_gap' (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    (6 / 1000 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ WeilZhuRed.QF 0 1 N x + (cg : ℝ) * (∑ i ∈ range N, x i * xv i) ^ 2 := by
  have hm := sector_margin_gen 0 (by norm_num) (by norm_num) Rg Rg_symm Rg_out GMn GDn (δg : ℝ) (1 / 10 ^ 8)
    (6 / 1000) (5 / 10 ^ 25) GDn_nonneg (by norm_num) gapHead b56_le
    (by unfold δg; norm_num) (by norm_num) (by unfold δg; norm_num) N hN x
  rw [qf_Rg] at hm
  have := WeilZhuRed.QF_ge_R 0 1 (WeilPlanch.modePlancherel_of WeilModes.modeDecay 0
    (WeilFourier.modeOrth (by norm_num))) N x
  linarith

lemma legT_mul (n m : ℕ) : (fun t => legT n t * legT m t) = WeilFourier.cut (fun t => WeilFourier.P n t * WeilFourier.P m t) := by
  funext t; rw [WeilFourier.legT_eq, WeilFourier.legT_eq]; unfold WeilFourier.cut Set.indicator
  split_ifs <;> simp

lemma legT_mul_int (n m : ℕ) : Integrable (fun t => legT n t * legT m t) := by
  rw [legT_mul]
  exact ((WeilFourier.P_cont n).mul (WeilFourier.P_cont m)).integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma xv_out {i : ℕ} (hi : 10 ≤ i) : xv i = 0 := by unfold xv; rw [if_neg (by omega)]

lemma ip_hx_v (N : ℕ) (hN : 10 ≤ N) (x y : ℕ → ℝ) : ip (WeilOdd.hx N x y) v = ∑ i ∈ range N, x i * xv i := by
  unfold ip
  have e : (fun t => WeilOdd.hx N x y t * v t)
      = fun t => ∑ i ∈ range N, ∑ j ∈ range 10, (x i * xv j * (legT (2 * i) t * legT (2 * j) t)
          + y i * xv j * (legT (2 * i + 1) t * legT (2 * j) t)) := by
    funext t; unfold WeilOdd.hx WeilOdd.gx v fx
    rw [add_mul, sum_mul, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun j _ => ?_); ring
  rw [e, integral_finsetSum]
  swap
  · intro i _; exact integrable_finsetSum _ (fun j _ => ((legT_mul_int _ _).const_mul _).add ((legT_mul_int _ _).const_mul _))
  refine sum_congr rfl (fun i hi => ?_)
  rw [integral_finsetSum]
  swap
  · intro j _; exact ((legT_mul_int _ _).const_mul _).add ((legT_mul_int _ _).const_mul _)
  simp_rw [integral_add ((legT_mul_int _ _).const_mul _) ((legT_mul_int _ _).const_mul _), integral_const_mul,
    WeilFourier.legT_orth]
  have h1 : ∀ j, (2 * i + 1 = 2 * j) ↔ False := fun j => by constructor <;> intro h <;> [omega; exact h.elim]
  simp only [h1, if_false, mul_zero, add_zero]
  by_cases hi10 : i < 10
  · rw [sum_eq_single i (fun j _ hj => by rw [if_neg (by omega)]; ring) (fun h => absurd (mem_range.2 hi10) h)]
    simp
  · rw [xv_out (by omega)]
    simp only [mul_zero]
    exact sum_eq_zero (fun j hj => by rw [if_neg (by have := mem_range.1 hj; omega)]; ring)

/-- pad a mode sum to at least `28` modes -/
lemma pad (N : ℕ) (x y : ℕ → ℝ) : ∃ x' y' : ℕ → ℝ, WeilOdd.hx N x y = WeilOdd.hx (N + 28) x' y' := by
  refine ⟨fun i => if i < N then x i else 0, fun i => if i < N then y i else 0, ?_⟩
  funext u
  unfold WeilOdd.hx fx WeilOdd.gx
  rw [sum_range_add, sum_range_add]
  have a1 : ∀ k ∈ range 28, (if N + k < N then x (N + k) else 0) * legT (2 * (N + k)) u = 0 :=
    fun k _ => by rw [if_neg (by omega)]; ring
  have a2 : ∀ k ∈ range 28, (if N + k < N then y (N + k) else 0) * legT (2 * (N + k) + 1) u = 0 :=
    fun k _ => by rw [if_neg (by omega)]; ring
  rw [sum_eq_zero a1, sum_eq_zero a2]
  have b1 : ∑ i ∈ range N, (if i < N then x i else 0) * legT (2 * i) u = ∑ i ∈ range N, x i * legT (2 * i) u :=
    sum_congr rfl (fun i hi => by rw [if_pos (mem_range.1 hi)])
  have b2 : ∑ i ∈ range N, (if i < N then y i else 0) * legT (2 * i + 1) u = ∑ i ∈ range N, y i * legT (2 * i + 1) u :=
    sum_congr rfl (fun i hi => by rw [if_pos (mem_range.1 hi)])
  rw [b1, b2]; ring

/-- the gap inequality on mode sums -/
lemma mode_gap (N : ℕ) (x y : ℕ → ℝ) :
    μ₂ * normSq (WeilOdd.hx N x y) ≤ weilQg (1 / 2) (WeilOdd.hx N x y) + (cg : ℝ) * ip (WeilOdd.hx N x y) v ^ 2 := by
  obtain ⟨x', y', h⟩ := pad N x y
  rw [h, WeilCoer.normSq_hx, WeilOdd.weilQg_hx, ip_hx_v _ (by omega)]
  have he := even_gap' (N + 28) (by omega) x'
  have ho := OddMargin2.odd_margin2 (N + 28) (by omega) y'
  have hs : 0 ≤ ∑ i ∈ range (N + 28), x' i ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  unfold μ₂; nlinarith

lemma v_int : Integrable v := by
  have := (WeilOdd.fxC_int 10 xv).re
  simpa [v] using this

lemma tendsto_ip {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, WeilCont.Good B M (g k)) (hf : WeilCont.Good B M f)
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => ip (g k) v) atTop (𝓝 (ip f v)) := by
  unfold ip
  refine tendsto_integral_of_dominated_convergence (fun t => B * |v t|)
    (fun k => (hg k).meas.aestronglyMeasurable.mul v_int.aestronglyMeasurable) (v_int.abs.const_mul B)
    (fun k => Filter.Eventually.of_forall (fun t => ?_)) (Filter.Eventually.of_forall (fun t => (hlim t).mul_const _))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hg k).bd t) (abs_nonneg _)

/-- **Gap on the test class**: `Q(f) + c⟨f,v⟩² ≥ μ₂‖f‖²`. -/
theorem gap_general {f : ℝ → ℝ} (hf : WeilGen.TestFn f) :
    μ₂ * normSq f ≤ weilQg (1 / 2) f + (cg : ℝ) * ip f v ^ 2 := by
  obtain ⟨B, M, g, hg, hfg, hlim, hp⟩ := WeilGen.approx hf
  refine le_of_tendsto_of_tendsto' ((WeilCont.tendsto_normSq hg hlim).const_mul _)
    ((WeilCont.tendsto_weilQg hg hfg hlim).add (((tendsto_ip hg hfg hlim).pow 2).const_mul _)) fun k => ?_
  obtain ⟨p, hpk⟩ := hp k
  obtain ⟨N, x, y, hxy⟩ := LegSpan.poly_hx p
  rw [hpk, ← hxy]; exact mode_gap N x y

theorem gap_perp {f : ℝ → ℝ} (hf : WeilGen.TestFn f) (hv : ip f v = 0) : μ₂ * normSq f ≤ weilQg (1 / 2) f := by
  have := gap_general hf; rw [hv] at this; simpa using this

lemma v_even (u : ℝ) : v (-u) = v u := by
  unfold v fx; refine sum_congr rfl (fun i _ => ?_)
  rw [WeilOdd.legT_neg, pow_mul]; norm_num

lemma ip_odd {f : ℝ → ℝ} (ho : ∀ u, f (-u) = -f u) : ip f v = 0 := by
  unfold ip
  have h := integral_neg_eq_self (fun t => f t * v t) volume
  simp only [ho, v_even, neg_mul] at h
  rw [integral_neg] at h
  linarith

/-- **Odd sector**: `Q(f) ≥ μ₂‖f‖² > μ₁‖f‖²` for odd test functions. -/
theorem odd_sector {f : ℝ → ℝ} (hf : WeilGen.TestFn f) (ho : ∀ u, f (-u) = -f u) :
    μ₂ * normSq f ≤ weilQg (1 / 2) f := gap_perp hf (ip_odd ho)

theorem v_upper : weilQg (1 / 2) v ≤ μ₁ * normSq v := GsUpper.trial_upper

lemma nq_pos : (0 : ℚ) < GsUpper.nq := by decide +kernel

lemma v_normSq_pos : 0 < normSq v := by
  unfold v; rw [GsUpper.normSq_v]; exact_mod_cast nq_pos

/-- test functions are closed under linear combinations -/
lemma testFn_comb {f g : ℝ → ℝ} (hf : WeilGen.TestFn f) (hg : WeilGen.TestFn g) (a b : ℝ) :
    WeilGen.TestFn (fun u => a * f u + b * g u) :=
  ⟨(contDiff_const.mul hf.1).add (contDiff_const.mul hg.1), fun u hu => by simp only [hf.2 u hu, hg.2 u hu]; ring⟩

lemma testFn_ip_int {f : ℝ → ℝ} (hf : WeilGen.TestFn f) : Integrable (fun t => f t * v t) := by
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(1/2)) (b := 1/2)) fun t ht => ?_
    have : 1 / 2 < |t| := by
      by_contra h; push_neg at h; exact ht (WeilGen.mem_Icc_of_abs h)
    exact hf.2 t this
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hcs
  exact v_int.bdd_mul hf.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma ip_comb {f g : ℝ → ℝ} (hf : WeilGen.TestFn f) (hg : WeilGen.TestFn g) (a b : ℝ) :
    ip (fun u => a * f u + b * g u) v = a * ip f v + b * ip g v := by
  unfold ip
  have e : (fun t => (a * f t + b * g t) * v t) = fun t => a * (f t * v t) + b * (g t * v t) := by
    funext t; ring
  rw [e, integral_add ((testFn_ip_int hf).const_mul a) ((testFn_ip_int hg).const_mul b), integral_const_mul,
    integral_const_mul]

/-- **Min-max, second level**: every two-dimensional family of test functions contains a nontrivial combination
`h = a f₁ + b f₂` with `Q(h) ≥ μ₂‖h‖²`. Together with `v_upper` (`Q(v) ≤ μ₁‖v‖²`, `μ₁ < μ₂`) this is the
min-max statement `λ₁ ≤ μ₁ < μ₂ ≤ λ₂`. -/
theorem minmax2 {f₁ f₂ : ℝ → ℝ} (h₁ : WeilGen.TestFn f₁) (h₂ : WeilGen.TestFn f₂) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      μ₂ * normSq (fun u => a * f₁ u + b * f₂ u) ≤ weilQg (1 / 2) (fun u => a * f₁ u + b * f₂ u) := by
  by_cases h : ip f₂ v = 0 ∧ ip f₁ v = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, gap_perp (testFn_comb h₁ h₂ 1 0) ?_⟩
    rw [ip_comb h₁ h₂, h.2]; ring
  · refine ⟨ip f₂ v, -ip f₁ v, ?_, gap_perp (testFn_comb h₁ h₂ _ _) ?_⟩
    · by_contra hc; push_neg at hc; exact h ⟨hc.1, neg_eq_zero.1 hc.2⟩
    · rw [ip_comb h₁ h₂]; ring

/-- **Ground state at `L = 1/2`** (min-max form). There is an explicit even `v ≠ 0` (a Legendre mode sum, in the
closure of the test class) with `Q(v) ≤ μ₁‖v‖²`, while `Q(f) ≥ μ₂‖f‖²` on the test functions orthogonal to `v`
and on all odd test functions, with `μ₁ = 2·10⁻⁵ < μ₂ = 4·10⁻⁵`. -/
theorem ground_state :
    (∀ u, v (-u) = v u) ∧ 0 < normSq v ∧ weilQg (1 / 2) v ≤ μ₁ * normSq v ∧ μ₁ < μ₂ ∧
    (∀ f, WeilGen.TestFn f → μ₂ * normSq f ≤ weilQg (1 / 2) f + (cg : ℝ) * ip f v ^ 2) ∧
    (∀ f, WeilGen.TestFn f → ip f v = 0 → μ₂ * normSq f ≤ weilQg (1 / 2) f) ∧
    (∀ f, WeilGen.TestFn f → (∀ u, f (-u) = -f u) → μ₂ * normSq f ≤ weilQg (1 / 2) f) :=
  ⟨v_even, v_normSq_pos, v_upper, μ₁_lt_μ₂, fun _ hf => gap_general hf, fun _ hf hv => gap_perp hf hv,
    fun _ hf ho => odd_sector hf ho⟩

/-! ## The trial vector is itself a test function -/

lemma cutp_cont {g : ℝ → ℝ} (hg : Continuous g) (h1 : g (1/2) = 0) (h2 : g (-(1/2)) = 0) :
    Continuous (LegSpan.cutp g) := by
  unfold LegSpan.cutp
  refine Continuous.if_le hg continuous_const continuous_abs continuous_const (fun x hx => ?_)
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.1 hx with h | h <;> rw [h] <;> assumption

lemma cutp_hasDerivAt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (h1 : φ (1/2) = 0) (h2 : φ (-(1/2)) = 0)
    (d1 : deriv φ (1/2) = 0) (d2 : deriv φ (-(1/2)) = 0) (u : ℝ) :
    HasDerivAt (LegSpan.cutp φ) (LegSpan.cutp (deriv φ) u) u := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  rcases lt_trichotomy |u| (1/2) with hu | hu | hu
  · have ev : LegSpan.cutp φ =ᶠ[𝓝 u] φ := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hu] with t ht
      unfold LegSpan.cutp; rw [if_pos (le_of_lt ht)]
    have : LegSpan.cutp (deriv φ) u = deriv φ u := by unfold LegSpan.cutp; rw [if_pos hu.le]
    rw [this]; exact (hd u).hasDerivAt.congr_of_eventuallyEq ev
  · -- endpoints
    have hz : LegSpan.cutp (deriv φ) u = 0 := by
      unfold LegSpan.cutp; rw [if_pos hu.le]
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.1 hu with h | h <;> rw [h] <;> assumption
    rw [hz]
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.1 hu with h | h <;> subst h
    · have L : HasDerivWithinAt (LegSpan.cutp φ) 0 (Set.Iic (1/2)) (1/2) := by
        have := (hd (1/2)).hasDerivAt.hasDerivWithinAt (s := Set.Iic (1/2))
        rw [d1] at this
        refine this.congr_of_eventuallyEq ?_ (by unfold LegSpan.cutp; rw [if_pos (by norm_num)])
        filter_upwards [self_mem_nhdsWithin, inter_mem_nhdsWithin (Set.Iic (1/2:ℝ))
          (Ioi_mem_nhds (by norm_num : (-(1/2):ℝ) < 1/2))] with t ht ht'
        unfold LegSpan.cutp; rw [if_pos (abs_le.2 ⟨ht'.2.le, ht⟩)]
      have R : HasDerivWithinAt (LegSpan.cutp φ) 0 (Set.Ici (1/2)) (1/2) := by
        refine (hasDerivWithinAt_const (1/2:ℝ) (Set.Ici (1/2)) (0:ℝ)).congr (fun t ht => ?_) ?_
        · unfold LegSpan.cutp; split_ifs with h
          · have : t = 1/2 := le_antisymm (abs_le.1 h).2 ht
            rw [this, h1]
          · rfl
        · unfold LegSpan.cutp; rw [if_pos (by norm_num), h1]
      have := L.union R
      rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have R : HasDerivWithinAt (LegSpan.cutp φ) 0 (Set.Ici (-(1/2))) (-(1/2)) := by
        have := (hd (-(1/2))).hasDerivAt.hasDerivWithinAt (s := Set.Ici (-(1/2)))
        rw [d2] at this
        refine this.congr_of_eventuallyEq ?_ (by unfold LegSpan.cutp; rw [if_pos (by norm_num)])
        filter_upwards [self_mem_nhdsWithin, inter_mem_nhdsWithin (Set.Ici (-(1/2):ℝ))
          (Iio_mem_nhds (by norm_num : (-(1/2):ℝ) < 1/2))] with t ht ht'
        unfold LegSpan.cutp; rw [if_pos (abs_le.2 ⟨ht, ht'.2.le⟩)]
      have L : HasDerivWithinAt (LegSpan.cutp φ) 0 (Set.Iic (-(1/2))) (-(1/2)) := by
        refine (hasDerivWithinAt_const (-(1/2):ℝ) (Set.Iic (-(1/2))) (0:ℝ)).congr (fun t ht => ?_) ?_
        · unfold LegSpan.cutp; split_ifs with h
          · have : t = -(1/2) := le_antisymm ht (abs_le.1 h).1
            rw [this, h2]
          · rfl
        · unfold LegSpan.cutp; rw [if_pos (by norm_num), h2]
      have := L.union R
      rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have ev : LegSpan.cutp φ =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hu] with t ht
      unfold LegSpan.cutp; rw [if_neg (not_le.2 ht)]
    have : LegSpan.cutp (deriv φ) u = 0 := by unfold LegSpan.cutp; rw [if_neg (not_le.2 hu)]
    rw [this]; exact (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq ev

/-- a `C¹` function vanishing to first order at `±1/2`, cut to `[−1/2, 1/2]`, is a test function -/
theorem cutp_testFn {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (h1 : φ (1/2) = 0) (h2 : φ (-(1/2)) = 0)
    (d1 : deriv φ (1/2) = 0) (d2 : deriv φ (-(1/2)) = 0) : WeilGen.TestFn (LegSpan.cutp φ) := by
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun u => (cutp_hasDerivAt hφ h1 h2 d1 d2 u).differentiableAt, ?_⟩, ?_⟩
  · have e : deriv (LegSpan.cutp φ) = LegSpan.cutp (deriv φ) := funext fun u => (cutp_hasDerivAt hφ h1 h2 d1 d2 u).deriv
    rw [e]; exact cutp_cont (hφ.continuous_deriv le_rfl) d1 d2
  · intro u hu; unfold LegSpan.cutp; rw [if_neg (not_le.2 hu)]

theorem v_testFn : WeilGen.TestFn v := by
  have hv : v = LegSpan.cutp (fun u => (GsUpper.lp GsUpper.c0).eval (u + 1 / 2)) := GsUpper.fx_cutp
  have hb := GsUpper.bc_chk
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hb
  have ev0 : ∀ j r, (GsUpper.ev (GsUpper.cj j) r = 0) → (GsUpper.lp (GsUpper.cj j)).eval (r : ℝ) = 0 := by
    intro j r h; rw [GsUpper.eval_lp_q, h]; simp
  have D1 : Polynomial.derivative (GsUpper.lp GsUpper.c0) = GsUpper.lp (GsUpper.cj 1) := by
    have := GsUpper.D_lp 1; simpa [GsFourier.D] using this
  have hder : deriv (fun u => (GsUpper.lp GsUpper.c0).eval (u + 1 / 2))
      = fun u => (GsUpper.lp (GsUpper.cj 1)).eval (u + 1 / 2) := by
    funext u
    rw [← D1]
    exact ((GsUpper.lp GsUpper.c0).hasDerivAt (u + 1/2)).comp_add_const u (1/2) |>.deriv
  rw [hv]
  have hcd : ContDiff ℝ 1 (fun u : ℝ => (GsUpper.lp GsUpper.c0).eval (u + 1 / 2)) := by
    have := (Polynomial.contDiff_aeval (𝕜 := ℝ) (GsUpper.lp GsUpper.c0) 1).comp (contDiff_id.add (contDiff_const (c := (1/2:ℝ))))
    simpa [Function.comp_def, Polynomial.aeval_def] using this
  refine cutp_testFn hcd ?_ ?_ ?_ ?_
  · have := ev0 0 1 hb.1.1; norm_num at this ⊢; simpa [GsUpper.cj] using this
  · have := ev0 0 0 hb.1.2; norm_num at this ⊢; simpa [GsUpper.cj] using this
  · rw [hder]; have := ev0 1 1 hb.2.1.1; norm_num at this ⊢; exact this
  · rw [hder]; have := ev0 1 0 hb.2.1.2; norm_num at this ⊢; exact this

/-- **Rayleigh quotients on the test class**: the infimum is `≤ μ₁` (attained below by `v`), while every
two-dimensional subspace reaches `≥ μ₂`. -/
theorem ground_state_testFn :
    WeilGen.TestFn v ∧ (∀ u, v (-u) = v u) ∧ 0 < normSq v ∧ weilQg (1 / 2) v ≤ μ₁ * normSq v ∧ μ₁ < μ₂ ∧
    (∀ f₁ f₂, WeilGen.TestFn f₁ → WeilGen.TestFn f₂ → ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      μ₂ * normSq (fun u => a * f₁ u + b * f₂ u) ≤ weilQg (1 / 2) (fun u => a * f₁ u + b * f₂ u)) :=
  ⟨v_testFn, v_even, v_normSq_pos, v_upper, μ₁_lt_μ₂, fun _ _ h₁ h₂ => minmax2 h₁ h₂⟩

end GsMain
