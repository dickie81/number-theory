import Mathlib
import CmWProof

/-! # Global part of the model and the pointwise bound for `wψ(30 s)` -/

namespace CmGlob

open Real Finset CmPoly CmBessel CmW WeilConst CmWProof WeilTailB

/-! ## Constants -/

theorem const_chk : (decide (|xA| < 1) && decide (|xP1| < 1) && decide (|xP2| < 1) && decide (0 ≤ kap)
    && decide (0 < phi) && decide (kv < 1) && decide (0 ≤ kv) && decide (s2lo ^ 2 ≤ 2) && decide (2 ≤ s2hi ^ 2)
    && decide (0 ≤ s2hi) && decide (0 ≤ L2lo) && decide (0 ≤ s2lo)
    && decide (|30 * lam| ≤ (2 * K2 + 1) / 2) && decide (0 ≤ lam)) = true := by decide +kernel

lemma cc : |xA| < 1 ∧ |xP1| < 1 ∧ |xP2| < 1 ∧ 0 ≤ kap ∧ 0 < phi ∧ kv < 1 ∧ 0 ≤ kv ∧ s2lo ^ 2 ≤ 2
    ∧ 2 ≤ s2hi ^ 2 ∧ 0 ≤ s2hi ∧ 0 ≤ L2lo ∧ 0 ≤ s2lo ∧ |30 * lam| ≤ (2 * K2 + 1) / 2 ∧ 0 ≤ lam := by
  have h := const_chk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

lemma log2_b : (L2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (L2hi : ℝ) := by
  have h2 := log_enc (1/2) (by norm_num) 50
  have e2 : Real.log (1 - ((1/2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1:ℝ) - ((1/2 : ℚ) : ℝ) = 2⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [e2, abs_le] at h2
  constructor
  · unfold L2lo; push_cast; linarith [h2.2]
  · unfold L2hi; push_cast; linarith [h2.1]

lemma pi_b : (plo : ℝ) < π ∧ π < (phi : ℝ) := by
  constructor
  · unfold plo; have := Real.pi_gt_d20; push_cast; norm_num at this ⊢; linarith
  · unfold phi; have := Real.pi_lt_d20; push_cast; norm_num at this ⊢; linarith

lemma sqrt2_b : (s2lo : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (s2hi : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2, h3, -⟩ := cc
  refine ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast h1), ?_⟩
  rw [Real.sqrt_le_left (by exact_mod_cast h3)]; exact_mod_cast h2

lemma lam_err : |Real.log 2 - (lam : ℝ)| ≤ (elam : ℝ) := by
  have h := rnd_err 64 L2lo
  obtain ⟨a, b⟩ := log2_b
  unfold elam lam; push_cast
  rw [abs_le] at h ⊢; constructor <;> push_cast at h <;> linarith [h.1, h.2]

lemma kap_err : |Real.sqrt 2 * Real.log 2 - (kap : ℝ)| ≤ (ekap : ℝ) := by
  have h := rnd_err 64 (s2lo * L2lo)
  obtain ⟨a, b⟩ := log2_b
  obtain ⟨c, d⟩ := sqrt2_b
  obtain ⟨-, -, -, -, -, -, -, -, -, h3, h4, h5, -⟩ := cc
  have h4' : (0:ℝ) ≤ L2lo := by exact_mod_cast h4
  have h5' : (0:ℝ) ≤ s2lo := by exact_mod_cast h5
  have pr1 : (s2lo : ℝ) * L2lo ≤ Real.sqrt 2 * Real.log 2 := mul_le_mul c a h4' (Real.sqrt_nonneg 2)
  have pr2 : Real.sqrt 2 * Real.log 2 ≤ (s2hi : ℝ) * L2hi := mul_le_mul d b (by linarith) (by exact_mod_cast h3)
  unfold ekap kap; push_cast
  rw [abs_le] at h ⊢; push_cast at h; constructor <;> linarith [h.1, h.2]

noncomputable def K0 : ℝ := Real.log (aN : ℝ) - Real.log π - βs

lemma K0_err : |K0 - (K0h : ℝ)| ≤ (eK : ℝ) := by
  obtain ⟨hxA, hxP1, hxP2, -, hphi, -⟩ := cc
  obtain ⟨l1, l2⟩ := log2_b
  obtain ⟨p1, p2⟩ := pi_b
  obtain ⟨b1, b2⟩ := beta_bounds
  -- log aN
  have ha := log_enc xA hxA 60
  have ea : Real.log (aN : ℝ) = 5 * Real.log 2 + Real.log (1 - (xA : ℝ)) := by
    rw [show (1:ℝ) - (xA : ℝ) = 193 / 128 by unfold xA; push_cast; norm_num,
      show (aN : ℝ) = 2 ^ 5 * (193 / 128) by unfold aN; push_cast; norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  rw [abs_le] at ha
  -- log π
  have hplo : (0:ℝ) < plo := by unfold plo; norm_num
  have hphi' : (0:ℝ) < phi := by exact_mod_cast hphi
  have hq1 := log_enc xP1 hxP1 70
  have hq2 := log_enc xP2 hxP2 70
  have e1 : (1:ℝ) - (xP1 : ℝ) = plo / 2 := by unfold xP1; push_cast; ring
  have e2 : (1:ℝ) - (xP2 : ℝ) = phi / 2 := by unfold xP2; push_cast; ring
  rw [e1, abs_le] at hq1; rw [e2, abs_le] at hq2
  have m1 : Real.log ((plo : ℝ) / 2) ≤ Real.log (π / 2) := Real.log_le_log (by positivity) (by linarith)
  have m2 : Real.log (π / 2) ≤ Real.log ((phi : ℝ) / 2) := Real.log_le_log (by positivity) (by linarith)
  have epi : Real.log π = Real.log 2 + Real.log (π / 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  have hr := rnd_err P K0lo
  rw [abs_le] at hr
  unfold K0 eK K0h K0lo K0hi la_lo la_hi lp_lo lp_hi at *
  push_cast at *
  rw [ea, epi, abs_le]
  constructor <;> linarith

/-! ## Global polynomials -/

lemma hev_map_range (L : ℕ) (f : ℕ → ℚ) (x : ℝ) :
    hev ((List.range L).map f) x = ∑ i ∈ range L, ((f i : ℚ) : ℝ) * x ^ i := by
  rw [hev_sum]; simp only [List.length_map, List.length_range]
  apply sum_congr rfl; intro i hi
  rw [List.getD_eq_getElem?_getD]; simp [mem_range.1 hi]

lemma glog_err {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |(1 / 2) * Real.log (1 + kv * u) - hev glog u| ≤ (1 / 2) * (kv : ℝ) ^ (L1 + 1) / (1 - kv) := by
  obtain ⟨-, -, -, -, -, hkv1, hkv0, -⟩ := cc
  have hk1 : (kv : ℝ) < 1 := by exact_mod_cast hkv1
  have hk0 : (0 : ℝ) ≤ kv := by exact_mod_cast hkv0
  set v : ℝ := kv * u
  have hv0 : 0 ≤ v := mul_nonneg hk0 h0
  have hv1 : v ≤ kv := by simp only [v]; nlinarith
  have hx : |(-v)| < 1 := by rw [abs_neg, abs_of_nonneg hv0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx L1
  rw [sub_neg_eq_add, abs_neg, abs_of_nonneg hv0] at h
  have hg : hev glog u = -(1 / 2) * ∑ i ∈ range L1, (-v) ^ (i + 1) / (i + 1) := by
    unfold glog; rw [hev, hev_map_range]; push_cast; rw [zero_add, mul_sum, mul_sum]
    apply sum_congr rfl; intro i _; simp only [v]
    rw [show -((kv:ℝ) * u) = (-(kv:ℝ)) * u by ring, mul_pow, pow_succ u]; ring
  rw [hg]
  have hb : v ^ (L1 + 1) / (1 - v) ≤ (kv : ℝ) ^ (L1 + 1) / (1 - kv) := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hv0 hv1 _) (by linarith) (by linarith)
  calc _ = (1 / 2) * |∑ i ∈ range L1, (-v) ^ (i + 1) / (i + 1) + Real.log (1 + v)| := by
        rw [← abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), ← abs_mul]; congr 1; ring
    _ ≤ (1 / 2) * ((kv : ℝ) ^ (L1 + 1) / (1 - kv)) := by gcongr; exact h.trans hb
    _ = _ := by ring

lemma ginv_err {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |(1 / (12 * (aN : ℝ) ^ 2)) * ((1 - kv * u) / (1 + kv * u) ^ 2) - hev ginv u|
      ≤ 5 * (kv : ℝ) ^ L3 / (12 * aN ^ 2) := by
  obtain ⟨-, -, -, -, -, hkv1, hkv0, -⟩ := cc
  have hk1 : (kv : ℝ) < 1 := by exact_mod_cast hkv1
  have hk0 : (0 : ℝ) ≤ kv := by exact_mod_cast hkv0
  set v : ℝ := kv * u
  have hv0 : 0 ≤ v := mul_nonneg hk0 h0
  have hv1 : v ≤ kv := by simp only [v]; nlinarith
  have hgv : hev gv u = ∑ i ∈ range L3, (-v) ^ i := by
    unfold gv; rw [hev_map_range]; push_cast
    apply sum_congr rfl; intro i _; simp only [v]; rw [neg_mul_eq_neg_mul, mul_pow]
  have hgi : hev ginv u = (1 / (12 * (aN : ℝ) ^ 2)) * ((1 - v) * (hev gv u) ^ 2) := by
    unfold ginv; rw [hev_psc, hev_pmul, hev_pmul]; simp only [hev, v]; push_cast; ring
  rw [hgi, ← mul_sub, abs_mul, abs_of_pos (by unfold aN; positivity)]
  have h1v : (0:ℝ) < 1 + v := by linarith
  set g := hev gv u
  have hgeom : g = (1 - (-v) ^ L3) / (1 + v) := by
    rw [hgv, geom_sum_eq (by linarith : (-v) ≠ 1), div_eq_div_iff (by linarith) (by linarith)]; ring
  set R : ℝ := (-v) ^ L3 / (1 + v)
  have hR : |R| ≤ v ^ L3 := by
    simp only [R]; rw [abs_div, abs_pow, abs_neg, abs_of_nonneg hv0, abs_of_pos h1v]
    exact div_le_self (by positivity) (by linarith)
  have hvL : v ^ L3 ≤ 1 := pow_le_one₀ hv0 (by linarith)
  have e : (1 - v) / (1 + v) ^ 2 - (1 - v) * g ^ 2 = (1 - v) * R * (2 / (1 + v) - R) := by
    rw [hgeom]; simp only [R]; field_simp; ring
  rw [e, abs_mul, abs_mul]
  have a1 : |1 - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have a2 : |2 / (1 + v) - R| ≤ 3 := by
    have : 2 / (1 + v) ≤ 2 := by rw [div_le_iff₀ h1v]; linarith
    have : 0 ≤ 2 / (1 + v) := by positivity
    rw [abs_le]; constructor <;> linarith [abs_le.1 (hR.trans hvL)]
  have hb : |1 - v| * |R| * |2 / (1 + v) - R| ≤ 5 * (kv : ℝ) ^ L3 := by
    calc |1 - v| * |R| * |2 / (1 + v) - R| ≤ 1 * v ^ L3 * 3 := by gcongr
      _ ≤ 5 * (kv : ℝ) ^ L3 := by nlinarith [pow_le_pow_left₀ hv0 hv1 L3, pow_nonneg hv0 L3]
  calc 1 / (12 * (aN : ℝ) ^ 2) * (|1 - v| * |R| * |2 / (1 + v) - R|)
      ≤ 1 / (12 * (aN : ℝ) ^ 2) * (5 * (kv : ℝ) ^ L3) := by gcongr
    _ = _ := by ring

lemma gcos_eq (s : ℝ) : hev gcos (s ^ 2) = CmBessel.Tc K2 (30 * lam * s) := by
  unfold gcos CmBessel.Tc; rw [hev_map_range]; push_cast
  apply sum_congr rfl; intro k _; rw [mul_pow, mul_pow, pow_mul, pow_mul, pow_mul]; ring

lemma cos_err {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |Real.sqrt 2 * Real.log 2 * Real.cos (30 * s * Real.log 2) - (kap : ℝ) * hev gcos (s ^ 2)|
      ≤ (ekap : ℝ) + kap * (30 * elam + 2 * (30 * lam) ^ (2 * K2) / ((2 * K2).factorial : ℝ)) := by
  obtain ⟨-, -, -, hk, -, -, -, -, -, -, -, -, hl, hl0⟩ := cc
  have hk' : (0:ℝ) ≤ kap := by exact_mod_cast hk
  have hl0' : (0:ℝ) ≤ lam := by exact_mod_cast hl0
  rw [gcos_eq]
  have c1 := kap_err
  have c2 : |Real.cos (30 * s * Real.log 2) - Real.cos (30 * lam * s)| ≤ 30 * elam := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [show 30 * s * Real.log 2 - 30 * lam * s = 30 * s * (Real.log 2 - lam) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    have := lam_err
    calc 30 * s * |Real.log 2 - lam| ≤ 30 * 1 * elam := by gcongr
      _ = _ := by ring
  have hy : |30 * (lam:ℝ) * s| ≤ (2 * K2 + 1) / 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : (30 * (lam:ℝ)) ≤ (2 * K2 + 1) / 2 := by
      have hl' := (abs_le.1 hl).2
      have : ((30 * lam : ℚ) : ℝ) ≤ (((2 * K2 + 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hl'
      push_cast at this; exact this
    nlinarith
  have c3 := cos_tay K2 hy
  have c3' : 2 * |30 * (lam:ℝ) * s| ^ (2 * K2) / ((2 * K2).factorial : ℝ)
      ≤ 2 * (30 * lam) ^ (2 * K2) / ((2 * K2).factorial : ℝ) := by
    have hm : (30 * (lam:ℝ) * s) ^ (2 * K2) ≤ (30 * lam) ^ (2 * K2) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hm (by norm_num)
  have hc1 : |Real.cos (30 * s * Real.log 2)| ≤ 1 := Real.abs_cos_le_one _
  calc _ = |(Real.sqrt 2 * Real.log 2 - kap) * Real.cos (30 * s * Real.log 2)
        + kap * (Real.cos (30 * s * Real.log 2) - Real.cos (30 * lam * s))
        + kap * (Real.cos (30 * lam * s) - CmBessel.Tc K2 (30 * lam * s))| := by congr 1; ring
    _ ≤ |Real.sqrt 2 * Real.log 2 - kap| * 1 + kap * (30 * elam)
        + kap * (2 * (30 * lam) ^ (2 * K2) / ((2 * K2).factorial : ℝ)) := by
        refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
        · rw [abs_mul, abs_of_nonneg hk']; exact mul_le_mul_of_nonneg_left c2 hk'
        · rw [abs_mul, abs_of_nonneg hk']; exact mul_le_mul_of_nonneg_left (c3.trans c3') hk'
    _ ≤ _ := by nlinarith

/-! ## The pointwise model bound -/

lemma lsumR (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma locR_taus (b : ℝ) : locR taus b = (1 / 2) * ((aN : ℝ) / ((aN : ℝ) ^ 2 + b ^ 2))
    + ∑ k ∈ range 48, ((k:ℝ) + 1 / 4) / (((k:ℝ) + 1 / 4) ^ 2 + b ^ 2) := by
  unfold locR taus
  rw [List.map_cons, List.sum_cons, List.map_map]
  congr 1
  · push_cast; ring
  · rw [lsumR]; apply sum_congr rfl; intro k _; simp

lemma psiApx_split (s : ℝ) : DigammaStirling.psiApx 48 (15 * s) = Real.log (aN : ℝ)
    + (1 / 2) * Real.log (1 + kv * s ^ 2) - (1 / (12 * (aN : ℝ) ^ 2)) * ((1 - kv * s ^ 2) / (1 + kv * s ^ 2) ^ 2)
    - locR taus (15 * s) := by
  have ha : (((48:ℕ):ℝ) + 1 / 4) = (aN : ℝ) := by unfold aN; push_cast; norm_num
  have haN : (0:ℝ) < aN := by unfold aN; norm_num
  have hkv : (kv : ℝ) * s ^ 2 = (15 * s) ^ 2 / (aN : ℝ) ^ 2 := by unfold kv; push_cast; ring
  have h1 : (0:ℝ) < 1 + kv * s ^ 2 := by rw [hkv]; positivity
  unfold DigammaStirling.psiApx
  simp only
  rw [ha, locR_taus]
  have hr : (aN : ℝ) ^ 2 + (15 * s) ^ 2 = (aN : ℝ) ^ 2 * (1 + kv * s ^ 2) := by rw [hkv]; field_simp
  rw [hr, Real.log_mul (by positivity) h1.ne', Real.log_pow]
  rw [hkv]
  field_simp
  ring

theorem w_model (p : ℕ) (hp : p < NP) {s : ℝ} (h1 : (p:ℝ) / NP ≤ s) (h2 : s ≤ ((p:ℝ) + 1) / NP) :
    |wψ (30 * s) - (hev Gh (s ^ 2) - hev (Lh p) s)| ≤ (epw p : ℝ) := by
  have hNP : (NP:ℝ) = 128 := by norm_num [NP]
  have hp' : (p:ℝ) + 1 ≤ NP := by exact_mod_cast hp
  have hs0 : 0 ≤ s := le_trans (by positivity) h1
  have hs1 : s ≤ 1 := h2.trans (by rw [div_le_one (by rw [hNP]; norm_num)]; exact hp')
  have hu0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hu1 : s ^ 2 ≤ 1 := by nlinarith
  -- global polynomial
  have hGu : hev Gu (s ^ 2) = K0h + hev glog (s ^ 2) - hev ginv (s ^ 2) - kap * hev gcos (s ^ 2) := by
    unfold Gu; simp only [hev_padd, hev_psc, hev]; push_cast; ring
  have hGr := hev_rnd P Gu (x := s ^ 2) (by rw [abs_of_nonneg hu0]; exact hu1)
  have e1 := glog_err hu0 hu1
  have e2 := ginv_err hu0 hu1
  have e3 := cos_err hs0 hs1
  have e4 := K0_err
  have e5 := loc_err p hp h1 h2
  have e6 := DigammaStirling.re_digamma_quarter 48 (15 * s)
  have hE : (1:ℝ) / (120 * (((48:ℕ):ℝ) + 1 / 4) ^ 4) = (E48 : ℝ) := by unfold E48 aN; push_cast; norm_num
  rw [hE, psiApx_split] at e6
  have hw : wψ (30 * s) = (Complex.digamma (1 / 4 + ((15 * s : ℝ) : ℂ) * Complex.I)).re - Real.log π
      - Real.sqrt 2 * Real.log 2 * Real.cos (30 * s * Real.log 2) - βs := by
    unfold wψ Psi; rw [show 30 * s / 2 = 15 * s by ring]
  rw [hw]
  unfold Gh at hGr ⊢
  unfold epw eG
  rw [hGu] at hGr
  unfold K0 at e4
  push_cast at hGr e4 e6 ⊢
  rw [abs_le] at e1 e2 e3 e4 e5 e6 hGr ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, hGr.1, hGr.2]

end CmGlob
