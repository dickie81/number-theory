import Mathlib
import RandModel

/-!
# The random model has no atoms

`RandModel.X = Σ_p g(p, X(p))` is a convergent sum of independent three-valued variables. Along a sparse set `J` of
`K` primes, where each gap `|g(p, -1)|` exceeds the total spread `Σ_{q > p} β(q)` of the later ones, the partial sum
over `J` determines `(X(p))_{p ∈ J}`, so it lies in any interval of length `2δ` with probability at most `2^{-K}`.
Independence of the rest and a.s. convergence give `P(X = t) ≤ 2^{-K}` for every `K`. Unconditional.

* `NoAtoms.atom_zero`: `P(X = t) = 0` for every `t`.
* `NoAtoms.ν_singleton`: `RandModel.ν {t} = 0` for every `t`.

See `formalisations/d2-density.md`.
-/

namespace NoAtoms
open MeasureTheory ProbabilityTheory Filter Topology Finset RandModel
open scoped ENNReal

/-- The values of the coordinates. -/
def tri (y : ℝ) : Prop := y = -1 ∨ y = 0 ∨ y = 1

/-- The gap `|g(n, -1)|`. -/
noncomputable def G (n : ℕ) : ℝ := |g n (-1)|

theorem β_nonneg (n : ℕ) : 0 ≤ β n := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem vals {p : ℕ} (hp : p.Prime) :
    ∃ a b : ℝ, 0 < b ∧ b ≤ a ∧ g p 1 = -a ∧ g p (-1) = b ∧ β p = a + b ∧ G p = b := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have e1 : g p 1 = -(Real.log p / (p - 1)) := by simp only [g]; ring
  have e2 : g p (-1) = Real.log p / (p + 1) := by simp only [g]; rw [sub_neg_eq_add]; ring
  have ha : 0 < Real.log p / (p - 1) := div_pos hl (by linarith)
  have hb : 0 < Real.log p / (p + 1) := div_pos hl (by linarith)
  refine ⟨_, _, hb, div_le_div_of_nonneg_left hl.le (by linarith) (by linarith), e1, e2, ?_, ?_⟩
  · rw [β, e1, e2, abs_neg, abs_of_pos ha, abs_of_pos hb]
  · rw [G, e2, abs_of_pos hb]

theorem sep {p : ℕ} (hp : p.Prime) {y y' : ℝ} (hy : tri y) (hy' : tri y') (h : y ≠ y') :
    G p ≤ |g p y - g p y'| := by
  obtain ⟨a, b, hb, hab, e1, e2, -, eG⟩ := vals hp
  rw [eG]
  rcases hy with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
    simp only [e1, e2, g_zero] at * <;> first
      | exact absurd rfl h
      | exact le_abs.2 (Or.inl (by linarith))
      | exact le_abs.2 (Or.inr (by linarith))

theorem diff_le {p : ℕ} (hp : p.Prime) {y y' : ℝ} (hy : tri y) (hy' : tri y') :
    |g p y - g p y'| ≤ β p := by
  obtain ⟨a, b, hb, hab, e1, e2, eβ, -⟩ := vals hp
  rw [eβ]
  rcases hy with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
    simp only [e1, e2, g_zero] <;> exact abs_le.2 ⟨by linarith, by linarith⟩

theorem sep_sum (δ : ℝ) (J : Finset ℕ) : (∀ p ∈ J, p.Prime) →
    (∀ p ∈ J, 2 * δ + ∑ q ∈ J.filter (p < ·), β q < G p) → ∀ ω ω' : Ω, (∀ p ∈ J, tri (ω p)) →
    (∀ p ∈ J, tri (ω' p)) → |∑ p ∈ J, g p (ω p) - ∑ p ∈ J, g p (ω' p)| ≤ 2 * δ → ∀ p ∈ J, ω p = ω' p := by
  induction J using Finset.induction_on_min with
  | empty => intro _ _ _ _ _ _ _ p hp; simp at hp
  | insert a s has ih =>
    intro hJ hc ω ω' hω hω' hsum
    have ha : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [sum_insert ha, sum_insert ha] at hsum
    have hfa : (insert a s).filter (a < ·) = s := by
      rw [filter_insert, if_neg (lt_irrefl a), filter_true_of_mem fun x hx => has x hx]
    have hca := hc a (mem_insert_self a s)
    rw [hfa] at hca
    have hrest : |∑ p ∈ s, g p (ω p) - ∑ p ∈ s, g p (ω' p)| ≤ ∑ q ∈ s, β q := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
      exact diff_le (hJ q (mem_insert_of_mem hq)) (hω q (mem_insert_of_mem hq)) (hω' q (mem_insert_of_mem hq))
    have hδ : 0 ≤ 2 * δ := (abs_nonneg _).trans hsum
    have heq : ω a = ω' a := by
      by_contra hne
      have := sep (hJ a (mem_insert_self a s)) (hω a (mem_insert_self a s)) (hω' a (mem_insert_self a s)) hne
      have e : g a (ω a) - g a (ω' a) = (g a (ω a) + ∑ p ∈ s, g p (ω p) - (g a (ω' a) + ∑ p ∈ s, g p (ω' p))) -
          (∑ p ∈ s, g p (ω p) - ∑ p ∈ s, g p (ω' p)) := by ring
      have := abs_sub _ _ |>.trans_eq' (congrArg abs e).symm
      linarith
    have hs : |∑ p ∈ s, g p (ω p) - ∑ p ∈ s, g p (ω' p)| ≤ 2 * δ := by
      rw [heq] at hsum; ring_nf at hsum ⊢; linarith
    intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · exact heq
    refine ih (fun q hq => hJ q (mem_insert_of_mem hq)) (fun q hq => ?_) ω ω'
      (fun q hq => hω q (mem_insert_of_mem hq)) (fun q hq => hω' q (mem_insert_of_mem hq)) hs p hp
    have := hc q (mem_insert_of_mem hq)
    rwa [filter_insert, if_neg (not_lt.2 (has q hq).le)] at this

theorem law_le {p : ℕ} (hp : p.Prime) (y : ℝ) : law p {y} ≤ 2⁻¹ := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hr : r p = p / (2 * (p + 1)) := by simp [r, hp]
  have hr2 : r p ≤ 1 / 2 := r_le p
  have hr0 : 1 - 2 * r p ≤ 1 / 2 := by
    have : (1:ℝ) / 4 ≤ (p:ℝ) / (2 * ((p:ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    rw [hr]; linarith
  have hhalf : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]; simp
  rw [← hhalf]
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul]
  split_ifs with ha hb hc hc hb hc hc
  all_goals first
    | (exfalso; subst_vars; norm_num at *; done)
    | (simp only [mul_one, mul_zero, add_zero, zero_add]
       first | exact ENNReal.ofReal_le_ofReal (by linarith) | exact bot_le)

theorem cyl_le (J : Finset ℕ) (hJ : ∀ p ∈ J, p.Prime) (y : Ω) :
    P {ω | ∀ p ∈ J, ω p = y p} ≤ 2⁻¹ ^ J.card := by
  have : {ω : Ω | ∀ p ∈ J, ω p = y p} = (↑J : Set ℕ).pi fun p => {y p} := by
    ext ω; simp [Set.mem_pi]
  rw [this, P, Measure.infinitePi_pi _ fun i _ => measurableSet_singleton _]
  calc ∏ i ∈ J, law i {y i} ≤ ∏ _i ∈ J, (2⁻¹ : ℝ≥0∞) := prod_le_prod' fun i hi => law_le (hJ i hi) _
    _ = _ := prod_const _

/-- The partial sum over `J`. -/
noncomputable def F (J : Finset ℕ) (ω : Ω) : ℝ := ∑ p ∈ J, g p (ω p)

theorem measurable_F (J : Finset ℕ) : Measurable (F J) :=
  Finset.measurable_sum J fun p _ => (measurable_g p).comp (measurable_pi_apply p)

theorem ball_le (J : Finset ℕ) (hJ : ∀ p ∈ J, p.Prime) {δ : ℝ}
    (hc : ∀ p ∈ J, 2 * δ + ∑ q ∈ J.filter (p < ·), β q < G p) (c : ℝ) :
    P {ω | |F J ω - c| ≤ δ} ≤ 2⁻¹ ^ J.card := by
  have good : ∀ᵐ ω ∂P, ∀ n, tri (ω n) := ae_all_iff.2 ae_coord
  by_cases hne : ∃ ω0 : Ω, (∀ n, tri (ω0 n)) ∧ |F J ω0 - c| ≤ δ
  · obtain ⟨ω0, h0, hb0⟩ := hne
    refine (measure_mono_ae ?_).trans (cyl_le J hJ ω0)
    filter_upwards [good] with ω hω hb
    exact sep_sum δ J hJ hc ω ω0 (fun p _ => hω p) (fun p _ => h0 p) (by
      have := abs_sub_le (F J ω) c (F J ω0); rw [abs_sub_comm c] at this; unfold F at *; linarith)
  · have : P {ω | |F J ω - c| ≤ δ} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [good] with ω hω hb
      exact hne ⟨ω, hω, hb⟩
    rw [this]; exact bot_le

theorem indep_bound {F R : Ω → ℝ} (hF : Measurable F) (hR : Measurable R) (hind : IndepFun F R P)
    {δ : ℝ} {B : ℝ≥0∞} (hB : ∀ c, P {ω | |F ω - c| ≤ δ} ≤ B) (t : ℝ) :
    P {ω | |F ω + R ω - t| ≤ δ} ≤ B := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hF.aemeasurable).1 hind.symm
  set s : Set (ℝ × ℝ) := {q | |q.2 + q.1 - t| ≤ δ}
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) measurable_const
  have hpre : {ω | |F ω + R ω - t| ≤ δ} = (fun ω => (R ω, F ω)) ⁻¹' s := rfl
  have : IsProbabilityMeasure (P.map R) := (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  rw [hpre, ← Measure.map_apply (hR.prodMk hF) hs, hmap, Measure.prod_apply hs]
  calc ∫⁻ r, P.map F (Prod.mk r ⁻¹' s) ∂(P.map R) ≤ ∫⁻ _r, B ∂(P.map R) := by
        refine lintegral_mono fun r => ?_
        rw [Measure.map_apply hF (measurable_prodMk_left hs)]
        convert hB (t - r) using 2
        ext ω; simp only [s, Set.mem_preimage, Set.mem_ofPred_eq]; ring_nf
    _ = B := by simp

/-- The rest of the partial sum. -/
noncomputable def R (N : ℕ) (J : Finset ℕ) (ω : Ω) : ℝ := ∑ n ∈ range N \ J, g n (ω n)

theorem indep_FR (N : ℕ) (J : Finset ℕ) : IndepFun (F J) (R N J) P := by
  have hi : iIndepFun (fun i (ω : Ω) => ω i) P := by
    unfold P; exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have h := hi.indepFun_finset J (range N \ J) disjoint_sdiff (fun i => measurable_pi_apply i)
  have h2 := h.comp (φ := fun x : J → ℝ => ∑ i : J, g i (x i)) (ψ := fun x : ↥(range N \ J) → ℝ => ∑ i : ↥(range N \ J), g i (x i))
    (Finset.measurable_sum _ fun i _ => (measurable_g i).comp (measurable_pi_apply i))
    (Finset.measurable_sum _ fun i _ => (measurable_g i).comp (measurable_pi_apply i))
  convert h2 using 1
  · funext ω; simp only [Function.comp, F]; exact (Finset.sum_coe_sort J fun p => g p (ω p)).symm
  · funext ω; simp only [Function.comp, R]; exact (Finset.sum_coe_sort _ fun p => g p (ω p)).symm

theorem T_eq {N : ℕ} {J : Finset ℕ} (h : J ⊆ range N) (ω : Ω) : T N ω = F J ω + R N J ω := by
  rw [T, F, R, add_comm, sum_sdiff h]

theorem tendsto_β : Tendsto β atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp summable_β_sq.tendsto_atTop_zero
  simp only [Real.sqrt_zero] at h
  exact h.congr fun n => by simp [Function.comp, Real.sqrt_sq (β_nonneg n)]

theorem exists_J (K : ℕ) : ∃ J : Finset ℕ, J.card = K ∧ (∀ p ∈ J, p.Prime) ∧
    ∃ δ > 0, ∀ p ∈ J, 2 * δ + ∑ q ∈ J.filter (p < ·), β q < G p := by
  induction K with
  | zero => exact ⟨∅, rfl, by simp, 1, one_pos, by simp⟩
  | succ K ih =>
    obtain ⟨J, hK, hJ, δ, hδ, hc⟩ := ih
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (tendsto_β.eventually (gt_mem_nhds hδ))
    obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N0 (J.sup id + 1))
    have hlt : ∀ q ∈ J, q < p := fun q hq =>
      lt_of_lt_of_le (Nat.lt_succ_of_le (le_sup (f := id) hq)) (le_of_max_le_right hpN)
    have hpJ : p ∉ J := fun h => lt_irrefl p (hlt p h)
    have hβp : β p < δ := hN0 p (le_of_max_le_left hpN)
    obtain ⟨a, b, hb, -, -, -, -, eG⟩ := vals hp
    refine ⟨insert p J, by rw [card_insert_of_notMem hpJ, hK], fun q hq => ?_, min (δ / 2) (G p / 4),
      lt_min (by linarith) (by rw [eG]; linarith), fun q hq => ?_⟩
    · rcases mem_insert.1 hq with rfl | hq
      exacts [hp, hJ q hq]
    have hm1 := min_le_left (δ / 2) (G p / 4)
    have hm2 := min_le_right (δ / 2) (G p / 4)
    rcases mem_insert.1 hq with rfl | hq
    · rw [filter_insert, if_neg (lt_irrefl _), filter_false_of_mem fun x hx => not_lt.2 (hlt x hx).le]
      rw [eG] at hm2 ⊢; simp; linarith
    · rw [filter_insert, if_pos (hlt q hq), sum_insert (fun h => hpJ (mem_filter.1 h).1)]
      have := hc q hq; linarith

theorem atom_zero (t : ℝ) : P {ω | X ω = t} = 0 := by
  have hTm : TendstoInMeasure P T atTop X :=
    tendstoInMeasure_of_tendsto_ae (fun N => (measurable_T N).aestronglyMeasurable) ae_tendsto_X
  have hK : ∀ K : ℕ, P {ω | X ω = t} ≤ 2⁻¹ ^ K := by
    intro K
    obtain ⟨J, hcard, hJ, δ, hδ, hc⟩ := exists_J K
    have hlim := hTm (ENNReal.ofReal δ) (by simpa using hδ)
    have hev : ∀ᶠ N in atTop, P {ω | X ω = t} ≤ 2⁻¹ ^ K + P {ω | ENNReal.ofReal δ ≤ edist (T N ω) (X ω)} := by
      filter_upwards [eventually_ge_atTop (J.sup id + 1)] with N hN
      have hJN : J ⊆ range N := fun q hq => mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_of_le (le_sup (f := id) hq)) hN)
      have hA : P {ω | |T N ω - t| ≤ δ} ≤ 2⁻¹ ^ K := by
        simp only [T_eq hJN]
        rw [← hcard]
        exact indep_bound (measurable_F J) (Finset.measurable_sum _ fun n _ => (measurable_g n).comp
          (measurable_pi_apply n)) (indep_FR N J) (ball_le J hJ hc) t
      refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add hA le_rfl))
      intro ω (hω : X ω = t)
      by_cases h : ENNReal.ofReal δ ≤ edist (T N ω) (X ω)
      · exact Or.inr h
      · left
        have h' := edist_lt_ofReal.1 (not_le.1 h)
        rw [Real.dist_eq, hω] at h'; exact h'.le
    have := ge_of_tendsto (tendsto_const_nhds.add hlim) hev
    rwa [add_zero] at this
  exact le_zero_iff.1 (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) hK)

/-- **No atoms.** `RandModel.ν {t} = 0` for every `t`. -/
theorem ν_singleton (t : ℝ) : (RandModel.ν : Measure ℝ) {t} = 0 := by
  rw [RandModel.ν, ProbabilityMeasure.coe_mk,
    Measure.map_apply_of_aemeasurable RandModel.aemeasurable_X (measurableSet_singleton t)]
  exact atom_zero t

end NoAtoms
