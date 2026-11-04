import Mathlib
import V3Log
import WeilOdd

/-! # Rescaling `[−1/2, 1/2]` to `[−L*, L*]`, `L* = log 3 / 2`

Write `λ = log 3 = 2L*` and `f = sc g`, `f(u) = g(u/λ)/√λ`. For a mode sum `g = hx N x y` on `[−1/2, 1/2]`
(`WeilOdd.hx`), the general Weil form at support `L*` is

  `weilQg L* f = 2·poleR f L*·poleL f L* + (1/π) ∫₀^∞ Ψ(t/λ)·S(t) dt`  (`weilQg_sc`),

where `Ψ = WeilTailB.Psi` is the frequency weight of the window `L = 1/2` and `S = F₀² + F₁²` is the spectral density
of `g` (`WeilOdd.S`). Two facts make `Ψ` the right weight: at support `L*` the only prime power with `log n < 2L*` is
`n = 2` (`n = 3` sits on the boundary, where the autocorrelation of a function supported in `[−1/2, 1/2]` vanishes),
and the rescaling turns the archimedean frequency `t` into `t/λ`. -/

namespace V3Scale

open Real Finset MeasureTheory Set WeilTailB WeilPlanch WeilModes WeilFourier WeilArch WeilOdd

/-- `λ = log 3`, twice the support `L* = log 3 / 2`. -/
noncomputable def lam : ℝ := Real.log 3

lemma lam_bounds : (V3Log.l3lo : ℝ) ≤ lam ∧ lam ≤ V3Log.l3hi := V3Log.log_three_mem

lemma one_lt_lam : 1 < lam := by
  have := lam_bounds.1; unfold V3Log.l3lo at this; push_cast at this; linarith

lemma lam_pos : 0 < lam := by linarith [one_lt_lam]

lemma lam_lt : lam < 11 / 10 := by
  have := lam_bounds.2; unfold V3Log.l3hi at this; push_cast at this; linarith

lemma sqrt_lam_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt lam_pos.le

lemma sqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr lam_pos

/-- The rescaling `f(u) = g(u/λ)/√λ`: support `[−1/2, 1/2]` becomes `[−L*, L*]` and the `L²` norm is kept. -/
noncomputable def sc (g : ℝ → ℝ) (u : ℝ) : ℝ := g (u / lam) / Real.sqrt lam

theorem normSq_sc (g : ℝ → ℝ) : WeilForm.normSq (sc g) = WeilForm.normSq g := by
  unfold WeilForm.normSq sc
  have e : (fun t => (g (t / lam) / Real.sqrt lam) ^ 2) = fun t => lam⁻¹ * (fun s => g s ^ 2) (t / lam) := by
    funext t; rw [div_pow, sqrt_lam_sq]; ring
  rw [e, integral_const_mul, Measure.integral_comp_div (fun s => g s ^ 2) lam, abs_of_pos lam_pos, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ lam_pos.ne', one_mul]

theorem autocorr_sc (g : ℝ → ℝ) (u : ℝ) : WeilForm.autocorr (sc g) u = WeilForm.autocorr g (u / lam) := by
  unfold WeilForm.autocorr sc
  have e : (fun t => g (t / lam) / Real.sqrt lam * (g ((t + u) / lam) / Real.sqrt lam))
      = fun t => lam⁻¹ * (fun s => g s * g (s + u / lam)) (t / lam) := by
    funext t
    rw [show (t + u) / lam = t / lam + u / lam by ring, div_mul_div_comm, ← sq, sqrt_lam_sq]; ring
  rw [e, integral_const_mul, Measure.integral_comp_div (fun s => g s * g (s + u / lam)) lam, abs_of_pos lam_pos,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ lam_pos.ne', one_mul]

/-- The pole integrals of `f = sc g` over `[−L*, L*]`, in terms of `g`. -/
theorem poleR_sc (g : ℝ → ℝ) : WeilForm.poleR (sc g) (lam / 2)
    = Real.sqrt lam * ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (-(lam * y / 2)) := by
  have hl : lam ≠ 0 := lam_pos.ne'
  have key := intervalIntegral.integral_comp_div (a := -(lam / 2)) (b := lam / 2)
    (fun y => g y * Real.exp (-(lam * y / 2)) / Real.sqrt lam) hl
  have e1 : -(lam / 2) / lam = -(1 / 2) := by field_simp
  have e2 : lam / 2 / lam = 1 / 2 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  unfold WeilForm.poleR sc
  have e : (fun u => g (u / lam) / Real.sqrt lam * Real.exp (-(u / 2)))
      = fun u => g (u / lam) * Real.exp (-(lam * (u / lam) / 2)) / Real.sqrt lam := by
    funext u; rw [mul_div_cancel₀ u hl]; ring
  rw [e, key, intervalIntegral.integral_div]
  have hs : lam / Real.sqrt lam = Real.sqrt lam := by
    rw [div_eq_iff sqrt_lam_pos.ne', ← sq, sqrt_lam_sq]
  set I := ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (-(lam * y / 2))
  calc lam * (I / Real.sqrt lam) = (lam / Real.sqrt lam) * I := by ring
    _ = Real.sqrt lam * I := by rw [hs]

theorem poleL_sc (g : ℝ → ℝ) : WeilForm.poleL (sc g) (lam / 2)
    = Real.sqrt lam * ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (lam * y / 2) := by
  have hl : lam ≠ 0 := lam_pos.ne'
  have key := intervalIntegral.integral_comp_div (a := -(lam / 2)) (b := lam / 2)
    (fun y => g y * Real.exp (lam * y / 2) / Real.sqrt lam) hl
  have e1 : -(lam / 2) / lam = -(1 / 2) := by field_simp
  have e2 : lam / 2 / lam = 1 / 2 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  unfold WeilForm.poleL sc
  have e : (fun u => g (u / lam) / Real.sqrt lam * Real.exp (u / 2))
      = fun u => g (u / lam) * Real.exp (lam * (u / lam) / 2) / Real.sqrt lam := by
    funext u; rw [mul_div_cancel₀ u hl]; ring
  rw [e, key, intervalIntegral.integral_div]
  have hs : lam / Real.sqrt lam = Real.sqrt lam := by
    rw [div_eq_iff sqrt_lam_pos.ne', ← sq, sqrt_lam_sq]
  set I := ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (lam * y / 2)
  calc lam * (I / Real.sqrt lam) = (lam / Real.sqrt lam) * I := by ring
    _ = Real.sqrt lam * I := by rw [hs]

/-! ## The prime sum: only `n = 2`, with `n = 3` on the boundary -/

/-- The autocorrelation of a mode sum vanishes for `|u| ≥ 1`; at `|u| = 1` the overlap is the single point `−u/2`. -/
lemma autocorr_hx_zero (N : ℕ) (x y : ℕ → ℝ) {u : ℝ} (hu : 1 ≤ |u|) : WeilForm.autocorr (hx N x y) u = 0 := by
  unfold WeilForm.autocorr
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(Set.countable_singleton (-u / 2)).ae_notMem volume] with t ht
  simp only [Set.mem_singleton_iff] at ht
  by_cases h1 : 1 / 2 < |t|
  · simp [hx_supp N x y h1]
  · by_cases h2 : 1 / 2 < |t + u|
    · simp [hx_supp N x y h2]
    · exfalso; push Not at h1 h2
      rcases abs_le.mp h1 with ⟨a1, a2⟩
      rcases abs_le.mp h2 with ⟨b1, b2⟩
      rcases le_abs'.mp hu with h | h
      · exact ht (by linarith)
      · exact ht (by linarith)

theorem primeS_sc (N : ℕ) (x y : ℕ → ℝ) :
    WeilForm.primeS (sc (hx N x y))
      = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * WeilForm.autocorr (hx N x y) (Real.log 2 / lam) := by
  unfold WeilForm.primeS
  simp_rw [autocorr_sc]
  rw [tsum_eq_single (2:ℕ)]
  · push_cast; ring
  · intro n hn
    by_cases hl : ArithmeticFunction.vonMangoldt n = 0
    · simp [hl]
    · have h2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h' | h'
        · interval_cases n <;> simp at hl
        · exact h'
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hlog : lam ≤ Real.log n := Real.log_le_log (by norm_num) h3
      have : 1 ≤ |Real.log n / lam| := by
        rw [abs_of_nonneg (div_nonneg (by linarith [lam_pos]) lam_pos.le), le_div_iff₀ lam_pos]; linarith
      rw [autocorr_hx_zero N x y this, mul_zero]

/-! ## The archimedean term at frequency `t/λ` -/

/-- Integrability of `w·T̂ᵢT̂ⱼ` on `(0, ∞)` for any continuous weight with `|w(t)| ≤ 21√(1+t)` (as for `Psi`). -/
lemma int_weight (par : ℕ) (w : ℝ → ℝ) (hwc : Continuous w) (hwg : ∀ t, 0 ≤ t → |w t| ≤ 21 * Real.sqrt (1 + t))
    (i j : ℕ) : IntegrableOn (fun t => w t * WeilZhuRed.G par i j t) (Ioi 0) := by
  obtain ⟨C1, hC1, h1⟩ := modeDecay (2 * i + par)
  obtain ⟨C2, hC2, h2⟩ := modeDecay (2 * j + par)
  have hGc : Continuous (WeilZhuRed.G par i j) := by unfold WeilZhuRed.G; exact (That_cont _).mul (That_cont _)
  refine Integrable.mono' (maj_int (21 * (C1 * C2))) (hwc.mul hGc).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_))
  have hb : |WeilZhuRed.G par i j t| ≤ C1 * C2 / (1 + t) ^ 2 := by
    unfold WeilZhuRed.G; rw [abs_mul]
    calc |That (2 * i + par) t| * |That (2 * j + par) t| ≤ C1 / (1 + t) * (C2 / (1 + t)) :=
          mul_le_mul (h1 t ht.le) (h2 t ht.le) (abs_nonneg _) (div_nonneg hC1 (by linarith))
      _ = C1 * C2 / (1 + t) ^ 2 := by rw [div_mul_div_comm, sq]
  rw [Real.norm_eq_abs, abs_mul]
  have e := (rpow_facts ht.le).2
  calc |w t| * |WeilZhuRed.G par i j t| ≤ (21 * Real.sqrt (1 + t)) * (C1 * C2 / (1 + t) ^ 2) :=
        mul_le_mul (hwg t ht.le) hb (abs_nonneg _) (by positivity)
    _ = 21 * (C1 * C2) * (Real.sqrt (1 + t) / (1 + t) ^ 2) := by ring
    _ = _ := by rw [e]

/-- The rescaled weight `Ψ̃(t) = Ψ(t/λ)`. -/
noncomputable def Psi3 (t : ℝ) : ℝ := Psi (t / lam)

lemma Psi3_cont : Continuous Psi3 := Psi_cont.comp (continuous_id.div_const _)

lemma Psi3_growth {t : ℝ} (h0 : 0 ≤ t) : |Psi3 t| ≤ 21 * Real.sqrt (1 + t) := by
  unfold Psi3
  have h1 : 0 ≤ t / lam := div_nonneg h0 lam_pos.le
  have h2 : t / lam ≤ t := div_le_self h0 one_lt_lam.le
  calc |Psi (t / lam)| ≤ 21 * Real.sqrt (1 + t / lam) := Psi_growth h1
    _ ≤ 21 * Real.sqrt (1 + t) := by gcongr

lemma int_Psi3 (par : ℕ) (i j : ℕ) : IntegrableOn (fun t => Psi3 t * WeilZhuRed.G par i j t) (Ioi 0) :=
  int_weight par Psi3 Psi3_cont (fun t ht => Psi3_growth ht) i j

theorem arch_sc (N : ℕ) (x y : ℕ → ℝ) :
    WeilForm.weilConst * WeilForm.normSq (sc (hx N x y)) + WeilForm.archE (sc (hx N x y))
      = (1 / π) * ∫ t in Ioi 0, ((Complex.digamma (1 / 4 + ((t / lam) / 2 : ℝ) * Complex.I)).re - Real.log π)
          * S N x y t := by
  set F := S N x y with hFdef
  have hc : Continuous F := ((F_cont 0 N x).pow 2).add ((F_cont 1 N y).pow 2)
  have P0 := modePlancherel_of modeDecay 0 (modeOrth (by norm_num))
  have P1 := modePlancherel_of modeDecay 1 (modeOrth (by norm_num))
  have hF2 : IntegrableOn F (Ioi 0) := by
    have a := (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
    have b := (WeilZhuRed.expand_int 1 N y (fun _ => 1) (Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
    simp only [one_mul] at a b
    exact a.add b
  have hPs : IntegrableOn (fun t => Psi3 t * F t) (Ioi 0) := by
    have a := (WeilZhuRed.expand_int 0 N x Psi3 (Ioi 0) (int_Psi3 0)).1
    have b := (WeilZhuRed.expand_int 1 N y Psi3 (Ioi 0) (int_Psi3 1)).1
    refine (a.add b).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hFdef, S, Pi.add_apply]; ring
  have hcos : ∀ v : ℝ, IntegrableOn (fun t => Real.cos (t * v) * F t) (Ioi 0) := by
    intro v
    refine hF2.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hDF : IntegrableOn (fun t => D (t / lam) * F t) (Ioi 0) := by
    have e : (fun t => D (t / lam) * F t) = fun t => Psi3 t * F t
        + ((Real.log π - (Complex.digamma (1 / 4)).re) * F t
        + Real.sqrt 2 * Real.log 2 * (Real.cos (t * (Real.log 2 / lam)) * F t)) := by
      funext t; unfold D Psi3 Psi
      rw [show t / lam * Real.log 2 = t * (Real.log 2 / lam) by ring]; ring
    rw [e]; exact hPs.add ((hF2.const_mul _).add ((hcos _).const_mul _))
  have hF0 : ∀ t, 0 ≤ F t := fun t => by simp only [hFdef, S]; positivity
  set φ : ℝ → ℝ → ℝ := fun t u => F t * ((1 - Real.cos (t / lam * u)) * K u)
  have hKm : Measurable K := by unfold K; fun_prop
  have hFm : Measurable F := hc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have : Measurable (Function.uncurry φ) := by
      show Measurable fun p : ℝ × ℝ => F p.1 * ((1 - Real.cos (p.1 / lam * p.2)) * K p.2)
      fun_prop
    exact this.aestronglyMeasurable
  have hinner : ∀ t, ∫ u in Ioi (0:ℝ), φ t u = D (t / lam) * F t := by
    intro t
    simp only [φ]
    rw [integral_const_mul, (kerD (t / lam)).2]; ring
  have hint : Integrable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun t => ((kerD (t / lam)).1.const_mul (F t)), ?_⟩
    refine (show Integrable (fun t => D (t / lam) * F t) (volume.restrict (Ioi 0)) from hDF).congr ?_
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [Function.uncurry_apply_pair]
    rw [← hinner t]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have : 0 ≤ φ t u := by
      simp only [φ]
      exact mul_nonneg (hF0 t) (mul_nonneg (by linarith [Real.cos_le_one (t / lam * u)]) (K_pos hu).le)
    rw [Real.norm_eq_abs, abs_of_nonneg this]
  have hswap := integral_integral_swap hint
  have hh : ∀ v : ℝ, |v| ≠ 1 → WeilForm.autocorr (hx N x y) v = (1 / π) * ∫ t in Ioi 0, Real.cos (t * v) * F t :=
    fun v hv => acorr_hx N x y hv
  have h0 : WeilForm.autocorr (hx N x y) 0 = (1 / π) * ∫ t in Ioi 0, F t := by
    have := hh 0 (by norm_num); simpa using this
  have hmain : WeilForm.archE (sc (hx N x y)) = (1 / π) * ∫ t in Ioi 0, D (t / lam) * F t := by
    unfold WeilForm.archE
    have e1 : ∫ t in Ioi (0:ℝ), D (t / lam) * F t = ∫ t in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), φ t u := by
      congr 1; funext t; rw [hinner]
    rw [e1, hswap, ← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [(Set.countable_singleton lam).ae_notMem volume] with u hu1 hu
    have hu' : |u / lam| ≠ 1 := by
      rw [abs_of_pos (div_pos hu lam_pos)]
      intro h; apply hu1; simp only [Set.mem_singleton_iff]
      rw [div_eq_one_iff_eq lam_pos.ne'] at h; exact h
    have e2 : ∫ t in Ioi (0:ℝ), φ t u = K u * ((∫ t in Ioi 0, F t) - ∫ t in Ioi 0, Real.cos (t * (u / lam)) * F t) := by
      rw [← integral_sub hF2 (hcos (u / lam)), ← integral_const_mul]
      congr 1; funext t; simp only [φ]; rw [show t / lam * u = t * (u / lam) by ring]; ring
    rw [e2]
    unfold WeilForm.archIntegrand
    rw [autocorr_sc, autocorr_sc, zero_div, h0, hh (u / lam) hu']
    unfold K; ring
  have hn : WeilForm.normSq (hx N x y) = WeilForm.autocorr (hx N x y) 0 := by
    unfold WeilForm.normSq WeilForm.autocorr; congr 1; funext t; rw [add_zero, sq]
  have e3 : (fun t => ((Complex.digamma (1 / 4 + ((t / lam) / 2 : ℝ) * Complex.I)).re - Real.log π) * F t)
      = fun t => D (t / lam) * F t + ((Complex.digamma (1 / 4)).re - Real.log π) * F t := by
    funext t; unfold D; ring
  rw [e3, integral_add hDF (hF2.const_mul _), integral_const_mul, hmain, normSq_sc, hn, h0]
  unfold WeilForm.weilConst
  ring

/-! ## The identity -/

/-- The rescaled frequency form of one parity sector: `(1/π) ∫₀^∞ Ψ(t/λ) F_par(t)² dt`. -/
noncomputable def QF3 (par N : ℕ) (x : ℕ → ℝ) : ℝ :=
  (1 / π) * ∫ t in Ioi 0, Psi3 t * WeilZhuRed.Fx par N x t ^ 2

/-- **The Weil form at support `log 3 / 2` of a rescaled mode sum.** -/
theorem weilQg_sc (N : ℕ) (x y : ℕ → ℝ) :
    WeilForm.weilQg (lam / 2) (sc (hx N x y))
      = 2 * WeilForm.poleR (sc (hx N x y)) (lam / 2) * WeilForm.poleL (sc (hx N x y)) (lam / 2)
        + QF3 0 N x + QF3 1 N y := by
  have P0 := modePlancherel_of modeDecay 0 (modeOrth (by norm_num))
  have P1 := modePlancherel_of modeDecay 1 (modeOrth (by norm_num))
  have a0 := (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
  have a1 := (WeilZhuRed.expand_int 1 N y (fun _ => 1) (Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
  simp only [one_mul] at a0 a1
  have p0 := (WeilZhuRed.expand_int 0 N x Psi3 (Ioi 0) (int_Psi3 0)).1
  have p1 := (WeilZhuRed.expand_int 1 N y Psi3 (Ioi 0) (int_Psi3 1)).1
  have hS : IntegrableOn (S N x y) (Ioi 0) := a0.add a1
  have hcos : IntegrableOn (fun t => Real.cos (t * (Real.log 2 / lam)) * S N x y t) (Ioi 0) := by
    refine hS.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hl2 : |Real.log 2 / lam| ≠ 1 := by
    have hl : Real.log 2 < lam := Real.log_lt_log (by norm_num) (by norm_num)
    rw [abs_of_pos (div_pos (Real.log_pos (by norm_num)) lam_pos)]
    exact (div_lt_one lam_pos |>.mpr hl).ne
  have hsplit : (∫ t in Ioi 0, ((Complex.digamma (1 / 4 + ((t / lam) / 2 : ℝ) * Complex.I)).re - Real.log π)
        * S N x y t)
      = (∫ t in Ioi 0, Psi3 t * WeilZhuRed.Fx 0 N x t ^ 2) + (∫ t in Ioi 0, Psi3 t * WeilZhuRed.Fx 1 N y t ^ 2)
        + Real.sqrt 2 * Real.log 2 * ∫ t in Ioi 0, Real.cos (t * (Real.log 2 / lam)) * S N x y t := by
    have e : (fun t => ((Complex.digamma (1 / 4 + ((t / lam) / 2 : ℝ) * Complex.I)).re - Real.log π)
          * S N x y t)
        = fun t => (Psi3 t * WeilZhuRed.Fx 0 N x t ^ 2 + Psi3 t * WeilZhuRed.Fx 1 N y t ^ 2)
          + Real.sqrt 2 * Real.log 2 * (Real.cos (t * (Real.log 2 / lam)) * S N x y t) := by
      funext t; unfold Psi3 Psi S
      rw [show t / lam * Real.log 2 = t * (Real.log 2 / lam) by ring]; ring
    have h1 : IntegrableOn (fun t => Psi3 t * WeilZhuRed.Fx 0 N x t ^ 2 + Psi3 t * WeilZhuRed.Fx 1 N y t ^ 2)
        (Ioi 0) := p0.add p1
    rw [e, integral_add h1 (hcos.const_mul _), integral_add p0 p1, integral_const_mul]
  have hW : WeilForm.weilQg (lam / 2) (sc (hx N x y))
      = 2 * WeilForm.poleR (sc (hx N x y)) (lam / 2) * WeilForm.poleL (sc (hx N x y)) (lam / 2)
        + (WeilForm.weilConst * WeilForm.normSq (sc (hx N x y)) + WeilForm.archE (sc (hx N x y)))
        - 2 * WeilForm.primeS (sc (hx N x y)) := by
    unfold WeilForm.weilQg; ring
  rw [hW, arch_sc, primeS_sc, acorr_hx N x y hl2, hsplit]
  unfold QF3
  have hc2 := WeilZhuRed.prime_coeff_L05
  have : ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 = Real.sqrt 2 * Real.log 2 / 2 := by
    rw [← hc2]; ring
  rw [this]; ring

end V3Scale
