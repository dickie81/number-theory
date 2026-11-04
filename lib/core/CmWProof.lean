import Mathlib
import CmNu

/-! # The pointwise error of the piecewise model of `wψ(30 s)` -/

namespace CmWProof

open Real Finset CmPoly CmBessel CmW WeilConst

/-! ## Local part: geometric expansion of `Re 1/(c + i b)` -/

def cG (u : ℚ × ℚ) : ℂ := (u.1 : ℂ) + (u.2 : ℂ) * Complex.I

lemma cG_mul (x y : ℚ × ℚ) : cG (mulG x y) = cG x * cG y := by
  unfold cG mulG; push_cast; ring_nf; rw [Complex.I_sq]; ring

lemma hev_glist (m : ℚ × ℚ) (d : ℕ) : ∀ (u : ℚ × ℚ) (δ : ℝ),
    hev (glist m u d) δ = (∑ j ∈ range d, cG u * cG m ^ j * (δ : ℂ) ^ j).re := by
  induction d with
  | zero => intro u δ; simp [glist, hev]
  | succ d ih =>
    intro u δ
    rw [glist, hev, ih, sum_range_succ']
    simp only [pow_zero, mul_one, Complex.add_re]
    rw [add_comm]; congr 1
    · rw [← Complex.re_ofReal_mul, mul_sum]; congr 1; apply sum_congr rfl; intro j _
      rw [cG_mul]; ring
    · simp [cG]

lemma geom_core (c b0 δ : ℝ) (hc : 0 < c) (d : ℕ) :
    ‖1 / ((c : ℂ) + (b0 + δ : ℝ) * Complex.I)
      - ∑ j ∈ range d, (1 / ((c : ℂ) + b0 * Complex.I)) * (-Complex.I / ((c : ℂ) + b0 * Complex.I)) ^ j * (δ : ℂ) ^ j‖
      ≤ |δ| ^ d / (‖(c : ℂ) + b0 * Complex.I‖ ^ d * c) := by
  set z0 : ℂ := (c : ℂ) + b0 * Complex.I
  set w : ℂ := (c : ℂ) + (b0 + δ : ℝ) * Complex.I
  have hz0re : z0.re = c := by simp [z0]
  have hwre : w.re = c := by simp [w]
  have hz0 : z0 ≠ 0 := fun h => by rw [h] at hz0re; simp at hz0re; linarith
  have hw : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre; linarith
  set q : ℂ := -Complex.I * δ / z0
  have hwq : w = z0 * (1 - q) := by
    have : z0 * (1 - q) = z0 + Complex.I * δ := by
      simp only [q]; rw [mul_sub, mul_one, mul_div_assoc', mul_comm z0, mul_div_assoc, div_self hz0]; ring
    rw [this]; simp only [w, z0]; push_cast; ring
  have hq1 : q ≠ 1 := by intro h; rw [h, sub_self, mul_zero] at hwq; exact hw hwq
  have hsum : ∑ j ∈ range d, 1 / z0 * (-Complex.I / z0) ^ j * (δ : ℂ) ^ j = (1 / z0) * ∑ j ∈ range d, q ^ j := by
    rw [mul_sum]; apply sum_congr rfl; intro j _; simp only [q]; rw [mul_assoc, ← mul_pow]; ring
  rw [hsum, geom_sum_eq hq1]
  have e : 1 / w - 1 / z0 * ((q ^ d - 1) / (q - 1)) = q ^ d / w := by
    rw [hwq]; have : (1:ℂ) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
    have : q - 1 ≠ 0 := sub_ne_zero.2 hq1
    field_simp; ring
  rw [e, norm_div, norm_pow]
  have hqn : ‖q‖ = |δ| / ‖z0‖ := by simp [q, norm_div, norm_mul]
  rw [hqn, div_pow]
  have hwn : c ≤ ‖w‖ := by rw [← hwre]; exact Complex.re_le_norm w
  have hz0n : 0 < ‖z0‖ := norm_pos_iff.2 hz0
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left hwn (by positivity)

/-- For `c > 0`, `d` even, `|δ| ≤ r`: `|c/(c² + (b₀+δ)²) − gterm(δ)| ≤ rᵈ / ((c² + b₀²)^{d/2} c)`. -/
theorem gterm_err (c b0 : ℚ) (hc : 0 < c) (d : ℕ) (hd : d = dd) {δ : ℝ} {r : ℚ} (hr : |δ| ≤ r) :
    |(c : ℝ) / ((c : ℝ) ^ 2 + ((b0 : ℝ) + δ) ^ 2) - hev (gterm c b0) δ|
      ≤ (r : ℝ) ^ d / ((nrm c b0 : ℝ) ^ (d / 2) * c) := by
  subst hd
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hN : (0:ℝ) < nrm c b0 := by unfold nrm; push_cast; positivity
  set z0 : ℂ := ((c:ℝ) : ℂ) + ((b0:ℝ) : ℂ) * Complex.I
  have hz0 : z0 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [z0] at this; linarith
  have hU : cG (c / nrm c b0, -b0 / nrm c b0) = 1 / z0 := by
    rw [eq_div_iff hz0]; unfold cG nrm; simp only [z0]; push_cast
    have : ((c:ℂ) ^ 2 + (b0:ℂ) ^ 2) ≠ 0 := by exact_mod_cast (ne_of_gt (by unfold nrm at hN; push_cast at hN; exact_mod_cast hN))
    field_simp; ring_nf; rw [Complex.I_sq]; ring
  have hM : cG (-b0 / nrm c b0, -c / nrm c b0) = -Complex.I / z0 := by
    rw [eq_div_iff hz0]; unfold cG nrm; simp only [z0]; push_cast
    have : ((c:ℂ) ^ 2 + (b0:ℂ) ^ 2) ≠ 0 := by exact_mod_cast (ne_of_gt (by unfold nrm at hN; push_cast at hN; exact_mod_cast hN))
    field_simp; ring_nf; rw [Complex.I_sq]; ring
  unfold gterm
  rw [hev_glist, hU, hM]
  have hre : (c : ℝ) / ((c : ℝ) ^ 2 + ((b0 : ℝ) + δ) ^ 2)
      = (1 / (((c:ℝ) : ℂ) + (((b0:ℝ) + δ : ℝ) : ℂ) * Complex.I)).re := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]; simp; ring
  rw [hre, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ((geom_core c b0 δ hc' dd).trans ?_)
  have hz0n : ‖z0‖ ^ 2 = (nrm c b0 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z0, nrm]; ring
  have hpow : ‖z0‖ ^ dd = (nrm c b0 : ℝ) ^ (dd / 2) := by
    rw [show dd = 2 * (dd / 2) by rfl, pow_mul, hz0n]; rfl
  rw [hpow]
  gcongr

lemma glist_length (m : ℚ × ℚ) (d : ℕ) : ∀ u, (glist m u d).length = d := by
  induction d with
  | zero => intro u; rfl
  | succ d ih => intro u; simp [glist, ih]

lemma gterm_length (c b0 : ℚ) : (gterm c b0).length = dd := glist_length _ _ _

noncomputable def locR (τs : List (ℚ × ℚ)) (b : ℝ) : ℝ :=
  (τs.map fun τ => (τ.1 : ℝ) * ((τ.2 : ℝ) / ((τ.2 : ℝ) ^ 2 + b ^ 2))).sum

lemma lex_err (τs : List (ℚ × ℚ)) (hpos : ∀ τ ∈ τs, 0 < τ.2 ∧ 0 ≤ τ.1) (b0 : ℚ) {δ : ℝ} (hδ : |δ| ≤ rr) :
    |locR τs ((b0 : ℝ) + δ) - hev (τs.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 b0)).map (rnd P)) acc) []) δ|
      ≤ (((τs.map fun τ => τ.1 * rr ^ dd / (nrm τ.2 b0 ^ (dd / 2) * τ.2)).sum + τs.length * dd / 2 ^ P : ℚ) : ℝ) := by
  have hδ1 : |δ| ≤ 1 := hδ.trans (by unfold rr NP; norm_num)
  induction τs with
  | nil => simp [locR, hev]
  | cons τ τs ih =>
    have h1 := hpos τ (by simp)
    have ih' := ih (fun τ' h => hpos τ' (by simp [h]))
    simp only [locR, List.map_cons, List.sum_cons, List.foldr_cons, hev_padd, List.length_cons] at ih' ⊢
    have ge := gterm_err τ.2 b0 h1.1 dd rfl hδ
    have hr := hev_rnd P (psc τ.1 (gterm τ.2 b0)) hδ1
    rw [show (psc τ.1 (gterm τ.2 b0)).length = dd by simp [psc, gterm_length]] at hr
    rw [hev_psc] at hr
    have hw : (0:ℝ) ≤ τ.1 := by exact_mod_cast h1.2
    have e1 : |(τ.1 : ℝ) * ((τ.2 : ℝ) / ((τ.2 : ℝ) ^ 2 + ((b0:ℝ) + δ) ^ 2)) - (τ.1 : ℝ) * hev (gterm τ.2 b0) δ|
        ≤ (τ.1 : ℝ) * ((rr : ℝ) ^ dd / ((nrm τ.2 b0 : ℝ) ^ (dd / 2) * τ.2)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]; exact mul_le_mul_of_nonneg_left ge hw
    push_cast at ih' ⊢
    calc _ = |((τ.1 : ℝ) * ((τ.2 : ℝ) / ((τ.2 : ℝ) ^ 2 + ((b0:ℝ) + δ) ^ 2)) - (τ.1 : ℝ) * hev (gterm τ.2 b0) δ)
          + ((τ.1 : ℝ) * hev (gterm τ.2 b0) δ - hev ((psc τ.1 (gterm τ.2 b0)).map (rnd P)) δ)
          + ((τs.map fun τ => (τ.1 : ℝ) * ((τ.2 : ℝ) / ((τ.2 : ℝ) ^ 2 + ((b0:ℝ) + δ) ^ 2))).sum
            - hev (τs.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 b0)).map (rnd P)) acc) []) δ)| := by
          congr 1; ring
      _ ≤ _ := by
          refine (abs_add_three _ _ _).trans ?_
          have := add_le_add (add_le_add e1 hr) ih'
          refine this.trans (le_of_eq ?_); ring

lemma taus_pos : ∀ τ ∈ taus, 0 < τ.2 ∧ 0 ≤ τ.1 := by
  intro τ h
  simp only [taus, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with h | ⟨k, _, h⟩
  · subst h; simp [aN]
  · subst h; exact ⟨show (0:ℚ) < (k:ℚ) + 1 / 4 by positivity, show (0:ℚ) ≤ 1 by norm_num⟩

theorem loc_err (p : ℕ) (hp : p < NP) {s : ℝ} (h1 : (p:ℝ) / NP ≤ s) (h2 : s ≤ ((p:ℝ) + 1) / NP) :
    |locR taus (15 * s) - hev (Lh p) s| ≤ (eL p : ℝ) := by
  have hNP : (NP:ℝ) = 128 := by norm_num [NP]
  have hp' : (p:ℝ) + 1 ≤ NP := by exact_mod_cast hp
  have hs0 : 0 ≤ s := le_trans (by positivity) h1
  have hs1 : s ≤ 1 := h2.trans (by rw [div_le_one (by rw [hNP]; norm_num)]; exact hp')
  set δ : ℝ := -15 * (s0 p : ℝ) + 15 * s
  have hδ : |δ| ≤ rr := by
    rw [abs_le]; simp only [δ, rr, s0]; push_cast
    rw [hNP] at h1 h2 ⊢
    constructor <;> nlinarith
  have hb : ((15 * s0 p : ℚ) : ℝ) + δ = 15 * s := by simp only [δ]; push_cast; ring
  have hl := lex_err taus taus_pos (15 * s0 p) hδ
  rw [hb] at hl
  have hr := hev_rnd P (paff (-15 * s0 p) 15 (CmW.Lex p)) (x := s) (by rw [abs_le]; constructor <;> linarith)
  rw [hev_paff] at hr
  have e : ((-15 * s0 p : ℚ) : ℝ) + ((15:ℚ):ℝ) * s = δ := by simp only [δ]; push_cast; ring
  rw [e] at hr
  unfold Lh eL
  unfold CmW.Lex at hr ⊢
  calc _ ≤ |locR taus (15 * s) - hev (taus.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 (15 * s0 p))).map (rnd P)) acc) []) δ|
        + |hev (taus.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 (15 * s0 p))).map (rnd P)) acc) []) δ
          - hev ((paff (-15 * s0 p) 15 (taus.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 (15 * s0 p))).map (rnd P)) acc) [])).map (rnd P)) s| :=
        abs_sub_le _ _ _
    _ ≤ _ := by
        have := add_le_add hl hr
        refine this.trans (le_of_eq ?_); push_cast; ring

end CmWProof
