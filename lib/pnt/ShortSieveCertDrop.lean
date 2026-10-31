import ShortSieveCertDec
import ShortSieveDrop

/-!
# The certificate's dropped boxes

A standard node with positive sign may be dropped: its count in `(x − y, x]` is at least `0`, and in the comparison
interval it is at most `ω*` times Mertens' bound for its box (`ShortSieveDrop.count_le_drop1`).

* `log_le_trB`: the trapezoid bound `trB lo hi = (hi − lo)(hi + lo)/(2 lo hi)` of `log(hi/lo)`.
* `Sound.OK_of_drop`: on a sound standard node, with `Ω` a bound for `ω*` on the box's range of
  `u = log(x/∏p)/log p_k`, the node is `OK` for `σ = 1` with loss `Ω ∏_{j<k} trB_j · DEN(1/lo_k − 1/hi_k)`.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree

open Classical

/-- The trapezoid bound `(hi − lo)(hi + lo)/(2 lo hi)` of `log(hi/lo)`. -/
noncomputable def trB (lo hi : ℝ) : ℝ := (hi - lo) * (hi + lo) / (2 * lo * hi)

theorem log_le_trB {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) : Real.log hi - Real.log lo ≤ trB lo hi := by
  have hhi : 0 < hi := by linarith
  have h := SieveOmegaB.log_le_half_sub_inv ((one_le_div hlo).2 hlohi)
  rw [Real.log_div hhi.ne' hlo.ne'] at h
  calc Real.log hi - Real.log lo ≤ (hi / lo - (hi / lo)⁻¹) / 2 := h
    _ = trB lo hi := by unfold trB; field_simp; ring

/-- The form `DEN − Σ_{j ≤ k} X_j`, `DEN log(x/∏p)/log x` at a pair's coordinates. -/
def numF (k : ℕ) : LF := ⟨DEN, List.replicate (k + 1) (-1), 0⟩

theorem val_numF (k : ℕ) (X : ℕ → ℝ) (H : ℝ) : (numF k).val X H = DEN - ∑ j ∈ range (k + 1), X j := by
  unfold numF LF.val
  rw [dotR_replicate_neg_one]
  push_cast
  ring

/-- `x^a ≤ p` when `a ≤ log p/log x`. -/
theorem rpow_le_of_le_div {x a : ℝ} (hx : 1 < x) {p : ℝ} (hp : 0 < p) (h : a ≤ Real.log p / Real.log x) :
    x ^ a ≤ p := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos (by linarith), ← Real.le_log_iff_exp_le hp]
  rw [le_div_iff₀ hlx] at h
  linarith

/-- `p < x^a` when `log p/log x < a`. -/
theorem lt_rpow_of_div_lt {x a : ℝ} (hx : 1 < x) {p : ℝ} (hp : 0 < p) (h : Real.log p / Real.log x < a) :
    p < x ^ a := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos (by linarith), ← Real.log_lt_iff_lt_exp hp]
  rw [div_lt_iff₀ hlx] at h
  linarith


/-- Mertens' sum over a box of prime tuples, the last prime weighted by `log x/(p log p)`. -/
theorem evLe_std_box {k : ℕ} (lo hi : Fin (k + 1) → ℝ) (hlo : ∀ j, 0 < lo j) (hlohi : ∀ j, lo j ≤ hi j) :
    SieveRough.EvLe (fun x => ∑ p ∈ Fintype.piFinset fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j),
      Real.log x / ((∏ j, (p j : ℝ)) * Real.log (p (Fin.last k))))
      (∏ j, if j ∈ ({Fin.last k} : Finset (Fin (k + 1))) then 1 / lo j - 1 / hi j
        else Real.log (hi j) - Real.log (lo j)) := by
  intro δ hδ
  filter_upwards [ShortSieveDrop.evLe_box lo hi hlo hlohi {Fin.last k} δ hδ] with x hx
  refine le_trans (le_of_eq (sum_congr rfl fun p _ => ?_)) hx
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [mem_singleton, Fin.castSucc_ne_last, ite_false, ite_true, prod_div_distrib, prod_const_one]
  ring

/-- **A dropped standard node.** On a sound standard node whose box has positive lower ends, with
`0 ≤ min(DEN − Σ_j X_j)` and `Ω` a bound for `ω*` on `[min(DEN − Σ_j X_j)/hi_k, max(DEN − Σ_j X_j)/lo_k]`, the node
is `OK` for `σ = 1` with loss `Ω ∏_{j<k} trB(lo_j, hi_j) · DEN(1/lo_k − 1/hi_k)`. -/
theorem Sound.OK_of_drop {k : ℕ} {conds : List (Cond (k + 1) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std k conds) (stdRows (k + 1)) E Γ B) (hE : 0 < E) (hinv : StdInv k conds)
    (hlen : k + 1 ≤ B.length) (hlo : ∀ j < k + 1, 0 < (B.getD j (0, 0)).1)
    (hlohi : ∀ j < k + 1, (B.getD j (0, 0)).1 ≤ (B.getD j (0, 0)).2)
    {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    (hn0 : 0 ≤ (numF k).minD B E acts) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hω : ∀ u : ℝ, ((numF k).minD B E acts : ℝ) / (B.getD k (0, 0)).2 ≤ u →
      u ≤ ((numF k).maxD B E acts : ℝ) / (B.getD k (0, 0)).1 → SieveCert.omegaC u ≤ Ω)
    {θ ρ : ℝ} (hρ : 0 < ρ) (hρ25 : 12 * ρ < 1 / 25) :
    OK θ ρ 1 (fun x y => ((std k conds).count x y : ℝ))
      (Ω * ∏ j : Fin (k + 1), if j = Fin.last k then (DEN : ℝ) / (B.getD j (0, 0)).1 - DEN / (B.getD j (0, 0)).2
        else trB (B.getD j (0, 0)).1 (B.getD j (0, 0)).2) := by
  have hD := DEN_pos
  set lo : Fin (k + 1) → ℝ := fun j => ((B.getD j (0, 0)).1 : ℝ) / DEN with hlo_def
  set hi : Fin (k + 1) → ℝ := fun j => ((B.getD j (0, 0)).2 : ℝ) / DEN with hhi_def
  have hloR : ∀ j : Fin (k + 1), (0 : ℝ) < (B.getD j (0, 0)).1 := fun j => by exact_mod_cast hlo j j.isLt
  have hlohiR : ∀ j : Fin (k + 1), ((B.getD j (0, 0)).1 : ℝ) ≤ (B.getD j (0, 0)).2 := fun j => by
    exact_mod_cast hlohi j j.isLt
  have hlo0 : ∀ j, 0 < lo j := fun j => div_pos (hloR j) hD
  have hlohi' : ∀ j, lo j ≤ hi j := fun j => div_le_div_of_nonneg_right (hlohiR j) hD.le
  set P : ℝ := ∏ j, if j ∈ ({Fin.last k} : Finset (Fin (k + 1))) then 1 / lo j - 1 / hi j
    else Real.log (hi j) - Real.log (lo j) with hP_def
  have hP0 : 0 ≤ P := prod_nonneg fun j _ => by
    split_ifs
    · have := one_div_le_one_div_of_le (hlo0 j) (hlohi' j); linarith
    · have := Real.log_le_log (hlo0 j) (hlohi' j); linarith
  -- the node's terms in the comparison interval
  have hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs (k + 1) 1 ⌊x⌋₊, SieveTree.rough (v.1 (Fin.last k)) (v.2 0) →
      (std k conds).InI x (x ^ (1 - ρ)) v.1 v.2 →
        v.1 ∈ (Fintype.piFinset fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j)) ∧
          x ^ (1 / 25 : ℝ) ≤ v.1 (Fin.last k) ∧ (v.1 (Fin.last k) : ℝ) ≤ v.2 0 ∧
          SieveCert.omegaC (Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log (v.1 (Fin.last k))) ≤ Ω := by
    filter_upwards [abs_slack_le hE (k + 1) 1, eventually_gt_atTop 1,
      (tendsto_rpow_atTop hρ).eventually_ge_atTop 2] with x hsl hx1 hxr v hv _ hI
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx1
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hv
    have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
    have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ' i).1
    have hyx : x ^ (1 - ρ) ≤ x / 2 := by
      have e : x ^ (1 - ρ) * x ^ ρ = x := by rw [← Real.rpow_add hx0]; simp
      have : x ^ (1 - ρ) * 2 ≤ x := by
        calc x ^ (1 - ρ) * 2 ≤ x ^ (1 - ρ) * x ^ ρ := mul_le_mul_of_nonneg_left hxr (Real.rpow_nonneg hx0.le _)
          _ = x := e
      linarith
    obtain ⟨hcI, h1, h2⟩ := hI
    have hH := hsl v hv1 hv2 (by linarith) (by linarith)
    obtain ⟨hB, hΓ⟩ := h x hx1 v hv1 hv2 hcI hH
    obtain ⟨hall, hge⟩ := hinv x hx1 v hv1 hv2 hcI
    have hbox : ∀ j : Fin (k + 1), ((B.getD j (0, 0)).1 : ℝ) ≤ DEN * (Real.log (v.1 j) / Real.log x) ∧
        DEN * (Real.log (v.1 j) / Real.log x) < (B.getD j (0, 0)).2 := fun j => by
      rw [← coords_std x v j]
      exact inBox_getD B _ j hB (by have := j.isLt; omega)
    have hpj : ∀ j, (0 : ℝ) < v.1 j := fun j => by exact_mod_cast hv1 j
    refine ⟨Fintype.mem_piFinset.2 fun j => SieveRough.mem_primesIn.2 ⟨(hp j).2, ?_, ?_⟩, hall (Fin.last k),
      by exact_mod_cast hge, ?_⟩
    · refine rpow_le_of_le_div hx1 (hpj j) ?_
      rw [hlo_def, div_le_iff₀ hD]
      linarith [(hbox j).1]
    · refine lt_rpow_of_div_lt hx1 (hpj j) ?_
      rw [hhi_def, lt_div_iff₀ hD]
      linarith [(hbox j).2]
    -- `u = (DEN − Σ_j X_j)/X_k`
    have hacts' : ∀ g ∈ acts, g.val (coords (stdRows (k + 1)) x v) (slack x v) ≤ 0 := fun g hg => by
      obtain ⟨c, hc', rfl⟩ := hacts g hg
      exact Con.val_le (hΓ c hc')
    have hfit : (numF k).c.length ≤ B.length := by simpa [numF] using hlen
    have hmin := (numF k).minD_le acts (inBoxC_of_inBox hB) hH hacts' hfit hfa
    have hmax := (numF k).le_maxD acts (inBoxC_of_inBox hB) hH hacts' hfit hfa
    set Nv := (numF k).val (coords (stdRows (k + 1)) x v) (slack x v) with hNv
    set D := DEN * (Real.log (v.1 (Fin.last k)) / Real.log x) with hD_def
    have hlogP : Real.log (∏ j, (v.1 j : ℝ)) = ∑ j, Real.log (v.1 j) :=
      Real.log_prod fun j _ => (hpj j).ne'
    have eN : Nv = DEN * (Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log x) := by
      rw [hNv, val_numF, Real.log_div hx0.ne' (prod_pos fun j _ => hpj j).ne', hlogP,
        ← Fin.sum_univ_eq_sum_range (fun j => coords (stdRows (k + 1)) x v j)]
      simp only [coords_std]
      rw [← mul_sum, ← sum_div]
      field_simp
    have hDpos : 0 < D := lt_of_lt_of_le (hloR (Fin.last k)) (by simpa using (hbox (Fin.last k)).1)
    have hu : Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log (v.1 (Fin.last k)) = Nv / D := by
      rw [eN, hD_def]
      have hlp : 0 < Real.log (v.1 (Fin.last k)) := by
        have := hDpos
        rw [hD_def] at this
        have h3 := pos_of_mul_pos_right this hD.le
        exact (div_pos_iff_of_pos_right hlx).1 h3
      field_simp
    rw [hu]
    have hDhi : D < (B.getD k (0, 0)).2 := by simpa using (hbox (Fin.last k)).2
    have hDlo : ((B.getD k (0, 0)).1 : ℝ) ≤ D := by simpa using (hbox (Fin.last k)).1
    have hn0' : (0 : ℝ) ≤ (numF k).minD B E acts := by exact_mod_cast hn0
    refine hω _ ?_ ?_
    · exact div_le_div₀ (hn0'.trans hmin) hmin hDpos hDhi.le
    · exact div_le_div₀ ((hn0'.trans hmin).trans hmax) hmax (hloR (Fin.last k)) (by simpa using hDlo)
  -- the bound in the comparison interval, and the loss
  have hdrop : OK θ ρ 1 (fun x y => ((std k conds).count x y : ℝ)) (Ω * P) :=
    ShortSieveTree.OK_of_drop (fun x y => Nat.cast_nonneg _) fun δ hδ =>
      ShortSieveDrop.count_le_drop1 (fun _ => Fin.last k) conds (lo := 1 / 25) (by norm_num) hρ hρ25 hΩ hP0 _
        hterm (evLe_std_box lo hi hlo0 hlohi') hδ
  refine OK_mono (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_) hΩ) hdrop
  · split_ifs
    · have := one_div_le_one_div_of_le (hlo0 j) (hlohi' j); linarith
    · have := Real.log_le_log (hlo0 j) (hlohi' j); linarith
  · by_cases hj : j = Fin.last k
    · simp only [mem_singleton, hj, ite_true, hlo_def, hhi_def, one_div_div]
      exact le_rfl
    · simp only [mem_singleton, hj, ite_false, hlo_def, hhi_def]
      rw [Real.log_div (by linarith [hloR j, hlohiR j]) hD.ne', Real.log_div (hloR j).ne' hD.ne']
      have := log_le_trB (hloR j) (hlohiR j)
      linarith


/-! ### The bound `ω*` on a range -/

/-- `K = 2^60` times an upper bound for `ω*` on `[an/ad, bn/bd]`, rounded up: `0` if the range is below `1`; otherwise
the largest of `1/max(a, 1)` (if `a < 2`), the bound on `[2, 3]` (if `b ≥ 2` and `a ≤ 3`) and `0.565073` (if `b > 3`).
On `[2, 3]` it is Buchstab's `ω` at `b` if `b ≤ 2.76`, where `ω` increases, at `a` if `a ≥ 2.77`, where it decreases,
and its maximum `0.5671433` otherwise (`SieveCert.omF`, as in the Linnik certificate's `SieveCert.omKw`). -/
def omUpK (an ad bn bd : ℕ) : ℕ :=
  if bn < bd then 0
  else max (max (if an < 2 * ad then (if ad ≤ an then SieveCert.cdiv (SieveCert.K * ad) an else SieveCert.K) else 0)
      (if 2 * bd ≤ bn ∧ an ≤ 3 * ad then
        (if 100 * bn ≤ 276 * bd then SieveCert.omF bn bd
          else if 277 * ad ≤ 100 * an then SieveCert.omF an ad else SieveCert.w1K)
        else 0))
    (if 3 * bd < bn then SieveCert.topK else 0)

/-- **`omUpK` bounds `ω*`** on `[an/ad, bn/bd]`. -/
theorem omegaC_le_omUpK {an ad bn bd : ℕ} (had : 0 < ad) (hbd : 0 < bd) {u : ℝ} (hau : (an : ℝ) / ad ≤ u)
    (hub : u ≤ (bn : ℝ) / bd) : SieveCert.omegaC u ≤ (omUpK an ad bn bd : ℝ) / SieveCert.K := by
  have hK := SieveCert.K_pos'
  have had' : (0 : ℝ) < ad := by exact_mod_cast had
  have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
  -- the range's ends against integers
  have hb : ∀ c : ℕ, (c : ℝ) ≤ u → c * bd ≤ bn := fun c hc => by
    have : (c : ℝ) ≤ bn / bd := hc.trans hub
    rw [le_div_iff₀ hbd'] at this
    exact_mod_cast this
  have ha : ∀ c : ℕ, u < c → an < c * ad := fun c hc => by
    have : (an : ℝ) / ad < c := lt_of_le_of_lt hau hc
    rw [div_lt_iff₀ had'] at this
    exact_mod_cast this
  have hpiece : ∀ n : ℕ, n ≤ omUpK an ad bn bd → (n : ℝ) / SieveCert.K ≤ (omUpK an ad bn bd : ℝ) / SieveCert.K :=
    fun n hn => div_le_div_of_nonneg_right (by exact_mod_cast hn) hK.le
  unfold SieveCert.omegaC
  split_ifs with h1 h2 h3
  · positivity
  · -- `1/u` on `[1, 2)`
    have hnb : ¬bn < bd := by have := hb 1 (by simpa using not_lt.1 h1); omega
    have han : an < 2 * ad := ha 2 (by simpa using h2)
    have hu1 : 1 ≤ u := not_lt.1 h1
    by_cases hadan : ad ≤ an
    · have hn : SieveCert.cdiv (SieveCert.K * ad) an ≤ omUpK an ad bn bd := by
        unfold omUpK
        rw [ite_eq_right hnb, ite_eq_left han, ite_eq_left hadan]
        exact le_max_of_le_left (le_max_left _ _)
      have han0 : 0 < an := lt_of_lt_of_le had hadan
      have han' : (0 : ℝ) < an := by exact_mod_cast han0
      refine le_trans ?_ (hpiece _ hn)
      have hc := SieveOmegaB.div_le_cdiv (SieveCert.K * ad) an han0
      push_cast at hc
      have hau' : (an : ℝ) / ad ≤ u := hau
      calc 1 / u ≤ 1 / ((an : ℝ) / ad) := one_div_le_one_div_of_le (div_pos han' had') hau'
        _ = (SieveCert.K * ad : ℝ) / an / SieveCert.K := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hc hK.le
    · have hn : SieveCert.K ≤ omUpK an ad bn bd := by
        unfold omUpK
        rw [ite_eq_right hnb, ite_eq_left han, ite_eq_right hadan]
        exact le_max_of_le_left (le_max_left _ _)
      refine le_trans ?_ (hpiece _ hn)
      rw [div_self hK.ne']
      exact (div_le_one (by linarith)).2 hu1
  · -- Buchstab's `ω` on `[2, 3]`
    have hu2 : 2 ≤ u := not_lt.1 h2
    have hnb : ¬bn < bd := by have := hb 1 (by norm_num; linarith); omega
    have h2b : 2 * bd ≤ bn := hb 2 (by simpa using hu2)
    have ha3 : an ≤ 3 * ad := by
      have : (an : ℝ) / ad ≤ 3 := hau.trans h3
      rw [div_le_iff₀ had'] at this
      exact_mod_cast this
    have hsel : (if 100 * bn ≤ 276 * bd then SieveCert.omF bn bd
        else if 277 * ad ≤ 100 * an then SieveCert.omF an ad else SieveCert.w1K) ≤ omUpK an ad bn bd := by
      unfold omUpK
      rw [ite_eq_right hnb, ite_eq_left (And.intro h2b ha3)]
      exact le_max_of_le_left (le_max_right _ _)
    refine le_trans ?_ (hpiece _ hsel)
    split_ifs with hb76 ha77
    · -- increasing: `ω(u) ≤ ω(b)`
      have hb76' : (bn : ℝ) / bd ≤ 276 / 100 := by
        rw [div_le_div_iff₀ hbd' (by norm_num)]
        have : ((100 * bn : ℕ) : ℝ) ≤ ((276 * bd : ℕ) : ℝ) := by exact_mod_cast hb76
        push_cast at this
        linarith
      have hb3 : bn ≤ 3 * bd := by omega
      exact (SieveOmegaB.omB_mono hu2 hub hb76').trans (SieveOmegaB.omF_ge hbd h2b hb3)
    · -- decreasing: `ω(u) ≤ ω(a)`
      have ha77' : 277 / 100 ≤ (an : ℝ) / ad := by
        rw [div_le_div_iff₀ (by norm_num) had']
        have : ((277 * ad : ℕ) : ℝ) ≤ ((100 * an : ℕ) : ℝ) := by exact_mod_cast ha77
        push_cast at this
        linarith
      have h2a : 2 * ad ≤ an := by omega
      exact (SieveOmegaB.omB_anti ha77' hau).trans (SieveOmegaB.omF_ge had h2a ha3)
    · exact (SieveOmegaB.omB_le_w1 (by linarith)).trans SieveCert.w1K_ge
  · -- above `3`
    have h3b : 3 * bd < bn := by
      have : (3 : ℝ) < bn / bd := lt_of_lt_of_le (not_le.1 h3) hub
      rw [lt_div_iff₀ hbd'] at this
      exact_mod_cast this
    have hnb : ¬bn < bd := by omega
    have hn : SieveCert.topK ≤ omUpK an ad bn bd := by
      unfold omUpK
      rw [ite_eq_right hnb, ite_eq_left h3b]
      exact le_max_right _ _
    exact SieveCert.topK_ge.trans (hpiece _ hn)

end ShortSieveCert

#print axioms ShortSieveCert.Sound.OK_of_drop
