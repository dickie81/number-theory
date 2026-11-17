/-
# The resonant window's test at the two corners of a box, sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTest.resX` tests the window's condition at a corner that is no point of the box: the rest's lower ends with
the variable that the rest's upper ends leave. `SieveResTest.resY` (`SieveResTestYDefs.lean`) tests the two corners
that are points of the box, and the record of an interval names the clamp's line and each term's bound, so that the
kernel does not look for them. This file proves that it gives `SieveTypeIIHM.ResBoxT`, the condition with the
variable tied to the rest.

* `LVok`, `GoalAtV`: the bound at `γ` for a list of terms, the large values' terms as hypotheses on the class.
  `intv3_sound`, `runI3_sound`, `resTM3_sound`: **the test with the bounds named is sound**, for any terms whose
  lines are `mkTm`'s.
* `lvok_mkTv`: the large values' terms of `mkTv ub lo` hold for a class at `lo/S ≤ s ≤ (ub + lo)/S`.
* `mom_carry`, `lvok_carry`: **a class at `s` carried to the upper end `s′`** of its cell, the sizes
  `t′ = 1/2 + (s/s′)(t − 1/2)`: the moments' conditions hold at `s′`, and so do the large values' terms of
  `mkTvH lo hi`, whose thresholds are the cell's.
* `two_corner`: **the two corners give the box**: the bound at the upper corner, the variable shorter by `1/11`
  of the box's width, and the bound with no clamp at the lower corner, give the bound at every point of the box
  with the variable tied to the rest.
* `resY_sound`: **`resY` gives `ResBoxT`** on the cells' exponents with the margin `2·10⁻⁵`.

* `resY_room`: `resY` leaves the variable room: the cells are in order and their upper ends' exponents sum to at
  most `L − 2·10⁻⁵`; `resYH_eq`: `resYH` is `resY` at the hints that it unpacks.

The file imports `SieveResLVTest.lean`, `SieveResTestYDefs.lean` and `SieveResTight.lean`.
-/
import SieveResLVTest
import SieveResTestYDefs
import SieveResTight

open Real Finset

namespace SieveResTest

open SieveTypeIIHM SieveCurveHx

attribute [local irreducible] lvVal lvG lvU

/-! ### The test with the bounds named -/

/-- **The large values' terms of `v` bound the term** `s(t − 1) − sτ` of a class with count exponent `γ`: between
the ends of an interval `[a, b]`, at `γ = (1 − λ)a/S + λb/S`, each of the two is above it. -/
def LVok (v : Tv) (s t γ : ℝ) : Prop :=
  ∀ (a b : ℕ) (lam : ℝ), a ≤ b → b ≤ S → 0 ≤ lam → lam ≤ 1 → γ = (1 - lam) * (a / S) + lam * (b / S) →
    s * (t - 1) - s * (1 / 10 ^ 6) ≤
        ((1 - lam) * (lvU v.t.lo v.k1 v.g1 a a : ℕ) + lam * (lvU v.t.lo v.k1 v.g1 a b : ℕ) - OFF) / S ∧
      s * (t - 1) - s * (1 / 10 ^ 6) ≤
        ((1 - lam) * (lvU v.t.lo v.k2 v.g2 a a : ℕ) + lam * (lvU v.t.lo v.k2 v.g2 a b : ℕ) - OFF) / S

/-- **The bound at `γ` for the terms `vs`**: for exponents `s j ≥ lo_j/S` (`lo_j` the terms') with sum at most `L`,
the variable's `m ≥ mlo/S` and a class with the moments' conditions and the large values' terms,
`Σ_j s_j(t_j − 1) + γ/2 + clamp ≤ −1/25000`. -/
def GoalAtV (L : ℝ) (vs : List Tv) (mlo : ℕ) (γ : ℝ) : Prop :=
  ∀ (β m : ℝ) (s t : ℕ → ℝ), 1 / 2 ≤ β → β ≤ 11 / 12 → γ ≤ ghx β → (∀ j < vs.length, t j ≤ β + 4 / 10 ^ 6) →
    (∀ j < vs.length, ∀ k : ℕ, 1 ≤ k → γ ≤ momExp k (s j) (t j - 1 / 10 ^ 6)) →
    (∀ j (hj : j < vs.length), LVok vs[j] (s j) (t j) γ) → (mlo : ℝ) / S ≤ m →
    (∀ j (hj : j < vs.length), (vs[j].t.lo : ℝ) / S ≤ s j) → ∑ j ∈ range vs.length, s j ≤ L →
    ∑ j ∈ range vs.length, s j * (t j - 1) + γ / 2 + clampR γ m ≤ -(1 / 25000)

set_option maxHeartbeats 1600000 in
/-- **One interval with its bounds named is sound**: `intv3` on `[a, b]` with `a` in the piece `pa` gives `b`'s piece
and the bound at every `γ ∈ [a/S, b/S]`, for terms whose lines are `mkTm`'s: any named bound is a bound. -/
lemma intv3_sound {L : ℝ} {vs : List Tv} (hvt : ∀ v ∈ vs, v.t = mkTm v.t.lo)
    {mlo c1 yuP yuN ydP ydN ltm a pa r : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (h : intv3 vs c1 yuP yuN ydP ydN ltm a pa r = true) (hpa : pa ≤ 17)
    (hlo : pa = 0 ∨ tops (pa - 1) * S < a) (hhi : pa ≤ 16 → (a : ℝ) ≤ tops pa * S) :
    pieceOf (bOf r) ≤ 17 ∧ (pieceOf (bOf r) = 0 ∨ tops (pieceOf (bOf r) - 1) * S < bOf r) ∧
      (pieceOf (bOf r) ≤ 16 → (bOf r : ℝ) ≤ tops (pieceOf (bOf r)) * S) ∧ a ≤ bOf r ∧
      ∀ γ, (a : ℝ) / S ≤ γ → γ ≤ (bOf r : ℝ) / S → GoalAtV L vs mlo γ := by
  have hS := S_pos
  unfold intv3 at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h17, hlt⟩, hle⟩, hab⟩, hchk⟩ := h
  -- the bounds that the record names: any choice is a bound
  generalize hccdef : Nat.land (Nat.shiftRight r 13) 3 = cc at hchk
  generalize hchdef : Nat.shiftRight r 15 = ch at hchk
  generalize hbdef : bOf r = b at h17 hlt hle hab hchk ⊢
  generalize hpbdef : pieceOf b = pb at h17 hlt hle hchk ⊢
  have hFTm := get_tFTm pb (by omega)
  have hFT := get_tFT pb (by omega)
  have hblo : pb = 0 ∨ tops (pb - 1) * S < b := by
    rcases Nat.eq_zero_or_pos pb with h0 | h0
    · exact Or.inl h0
    · right
      rw [hFTm, ite_eq_right (by omega)] at hlt
      have h1 := ft_gt (pb - 1) (by omega)
      have h2 : (ftN (pb - 1) : ℝ) + 1 ≤ b := by exact_mod_cast hlt
      linarith
  have hbhi : pb ≤ 16 → (b : ℝ) ≤ tops pb * S := fun h16 => by
    rw [hFT] at hle
    have h1 := ft_le pb h16
    have h2 : (b : ℝ) ≤ ftN pb := by exact_mod_cast hle
    linarith
  have hbS : b ≤ S := hle.trans (get_tFT_le pb (by omega))
  refine ⟨h17, hblo, hbhi, hab, ?_⟩
  intro γ hγa hγb β m s t h1 h2 hγ ht hk hlv hm hs hsum
  -- the ends in the reals
  have hlo' : pa = 0 ∨ tops (pa - 1) < a / S := by
    rcases hlo with h0 | h0
    · exact Or.inl h0
    · right; rw [lt_div_iff₀ hS]; exact h0
  have hhi' : pa ≤ 16 → (a : ℝ) / S ≤ tops pa := fun h16 => by rw [div_le_iff₀ hS]; exact hhi h16
  have hbhi' : pb ≤ 16 → (b : ℝ) / S ≤ tops pb := fun h16 => by rw [div_le_iff₀ hS]; exact hbhi h16
  have hab' : (a : ℝ) / S ≤ b / S := div_le_div_of_nonneg_right (by exact_mod_cast hab) hS.le
  have hγ0 : 0 ≤ γ := le_trans (div_nonneg (Nat.cast_nonneg _) hS.le) hγa
  obtain ⟨lam, hlam0, hlam1, hγlam⟩ := exists_lam hγa hγb
  have hC := line_C hpa hlo' hhi' hγa h1 h2 hγ
  have hW := line_W hpa hlo' hbhi' hab' h17 hγa hγb hγ0 h1 h2 hγ
  -- the terms
  generalize hdS : maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC) = dS at hC hchk
  generalize hiax : minN (get tIA pa) (get tIA pb) = iax at hW hchk
  have hv : ∀ i (hi : i < vs.length), ∀ c,
      s i * (t i - 1) - s i * (1 / 10 ^ 6) ≤ tline2 vs[i] dS iax a b c lam γ := by
    intro i hi c
    rcases Nat.lt_or_ge c 4 with hc3 | hc4
    · rw [tline2_le3 _ _ _ _ _ (by omega), hvt _ (List.getElem_mem hi)]
      exact term_le vs[i].t.lo dS iax c (hs i hi) (ht i hi) h2 hγ0 (hk i hi) hC hW
    · rcases Nat.eq_or_lt_of_le hc4 with hc | hc
      · rw [← hc, tline2_4]
        exact (hlv i hi a b lam hab hbS hlam0 hlam1 hγlam).1
      · rw [tline2_ge5 _ _ _ _ _ (by omega)]
        exact (hlv i hi a b lam hab hbS hlam0 hlam1 hγlam).2
  generalize hcl : clampL c1 yuP yuN ydP ydN a b cc = cl at hchk
  have hclb := clampL_sound hok a b cc hm hγa hγb
  rw [hcl] at hclb
  have hT := addTerms2_sound dS iax a b lam γ vs ch (Nat.add ltm cl.1) cl.2.2 0 0 0
    (fun j => s j * (t j - 1) - s j * (1 / 10 ^ 6)) hv
  -- the check at the ends
  unfold chkI2 at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨hca, hcb⟩ := hchk
  have la := le0_sound hca
  have lb := le0_sound hcb
  generalize hR : addTerms2 dS iax a b vs ch (Nat.add ltm cl.1) cl.2.2 0 0 0 = R at hT la lb
  unfold lv at la lb
  simp only [Nat.add_eq] at la lb hT
  push_cast at la lb hT
  rw [H_real] at la lb
  rw [div_nonpos_iff] at la lb
  rcases la with ⟨_, hneg⟩ | ⟨la, _⟩
  · exact absurd hneg (not_le.mpr hS)
  rcases lb with ⟨_, hneg⟩ | ⟨lb, _⟩
  · exact absurd hneg (not_le.mpr hS)
  -- the check between the ends: the mean of the two
  have lγ : (R.1 : ℝ) + ((1 - lam) * R.2.2.2.1 + lam * R.2.2.2.2) + (S / 2 + cl.2.1) * γ - R.2.1 - R.2.2.1 * γ ≤
      0 := by
    rw [hγlam]
    exact line_mean hlam0 hlam1 la lb
  have hT' : (∑ j ∈ range vs.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6))) * S +
      ((ltm : ℝ) + cl.1 - cl.2.2 - 0 * γ) ≤
      (R.1 : ℝ) + ((1 - lam) * R.2.2.2.1 + lam * R.2.2.2.2) - R.2.1 - R.2.2.1 * γ := by
    have h := mul_le_mul_of_nonneg_right hT hS.le
    rw [add_mul, div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at h
    linarith
  have hX : ∑ j ∈ range vs.length, s j * (t j - 1) =
      ∑ j ∈ range vs.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6)) +
        1 / 10 ^ 6 * ∑ j ∈ range vs.length, s j := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_comm (1 / 10 ^ 6 : ℝ)]
    ring
  exact goal_of_lines hS hX hsum (by rwa [le_div_iff₀ hS] at hltm) hT' lγ hclb

lemma runI3_zero (vs : List Tv) (w c1 yuP yuN ydP ydN ltm a pa h : ℕ) :
    runI3 vs w c1 yuP yuN ydP ydN ltm 0 a pa h = Nat.beq a S := rfl

lemma runI3_succ (vs : List Tv) (w c1 yuP yuN ydP ydN ltm k a pa h : ℕ) :
    runI3 vs w c1 yuP yuN ydP ydN ltm (k + 1) a pa h =
      (intv3 vs c1 yuP yuN ydP ydN ltm a pa (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) &&
        runI3 vs w c1 yuP yuN ydP ydN ltm k (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))
          (pieceOf (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))) (Nat.shiftRight h w)) := rfl

/-- **The intervals with their bounds named are sound**: `runI3` from `a` in the piece `pa` gives the bound at every
`γ ∈ (a/S, 1]`. -/
lemma runI3_sound {L : ℝ} {vs : List Tv} (hvt : ∀ v ∈ vs, v.t = mkTm v.t.lo)
    {mlo c1 yuP yuN ydP ydN ltm w : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) :
    ∀ (k a pa h : ℕ), runI3 vs w c1 yuP yuN ydP ydN ltm k a pa h = true → pa ≤ 17 →
      (pa = 0 ∨ tops (pa - 1) * S < a) → (pa ≤ 16 → (a : ℝ) ≤ tops pa * S) →
      ∀ γ, (a : ℝ) / S < γ → γ ≤ 1 → GoalAtV L vs mlo γ
  | 0, a, pa, h, hr, _, _, _, γ, hγa, hγ1 => by
    rw [runI3_zero] at hr
    have ha : a = S := Nat.eq_of_beq_eq_true hr
    subst ha
    rw [div_self S_pos.ne'] at hγa
    linarith
  | k + 1, a, pa, h, hr, hpa, hlo, hhi, γ, hγa, hγ1 => by
    rw [runI3_succ] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hi, hr⟩ := hr
    obtain ⟨h17, hblo, hbhi, hab, hgoal⟩ := intv3_sound hvt hok hltm hi hpa hlo hhi
    rcases le_or_gt γ ((bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) : ℕ) / S) with hγb | hγb
    · exact hgoal γ hγa.le hγb
    · exact runI3_sound hvt hok hltm k _ _ _ hr h17 hblo hbhi γ hγb hγ1

/-- The half-plane's sum of the terms is `hpSum`'s of their lower ends. -/
lemma hpSum2_lo : ∀ vs : List Tv, hpSum2 vs = hpSum ((vs.map fun v => v.t.lo).map mkTm)
  | [] => rfl
  | v :: vs => by
    rw [List.map_cons, List.map_cons]
    show Nat.add (mulF v.t.lo HP) (hpSum2 vs) =
      Nat.add (mulF (mkTm v.t.lo).lo HP) (hpSum ((vs.map fun v => v.t.lo).map mkTm))
    rw [hpSum2_lo vs, mkTm_lo]

/-- **The test with the bounds named is sound**: the bound at every `γ`, for terms whose lines are `mkTm`'s. -/
theorem resTM3_sound {L : ℝ} (hL : 0 ≤ L) {vs : List Tv} (hvt : ∀ v ∈ vs, v.t = mkTm v.t.lo) {mlo ltm k h : ℕ}
    (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (hT : resTM3 vs mlo ltm k h = true) : ∀ γ, GoalAtV L vs mlo γ := by
  have hS := S_pos
  unfold resTM3 at hT
  simp only [shrN, Nat.add_eq, Nat.sub_eq, Bool.and_eq_true, Nat.ble_eq, minN_eq] at hT
  obtain ⟨hhp, hrun⟩ := hT
  rw [hpSum2_lo] at hhp
  have hok := clampOK_of' mlo
  intro γ β m s t h1 h2 hγ ht hk hlv hm hs hsum
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · -- the half-plane
    have hlen : (vs.map fun v => v.t.lo).length = vs.length := List.length_map _
    have hX := hpSum_le h2 (vs.map fun v => v.t.lo) s t (by rw [hlen]; exact ht)
      (fun j hj => by
        rw [List.getElem_map]
        exact hs j (by rw [hlen] at hj; exact hj))
    rw [hlen] at hX
    have hc1 := clampR_anti (γ := γ) hm
    have hc2 := clampR_mono (m := (mlo : ℝ) / S) hγ0
    have hc3 : clampR 0 ((mlo : ℝ) / S) * S ≤ (min ((S - mlo + 1) / 2) ((K1U - mulF mlo M1D + 1) / 2) : ℕ) := by
      rw [Nat.cast_min]
      unfold clampR
      rw [min_mul_of_nonneg _ _ hS.le]
      apply min_le_min hok.c1
      rw [max_mul_of_nonneg _ _ hS.le, zero_mul]
      apply max_le (Nat.cast_nonneg _)
      have := hok.yu
      have : (0 : ℝ) ≤ (((mulF mlo M1D - K1U) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [zero_div, zero_add]
      linarith
    have hhp' : (ltm : ℝ) + (min ((S - mlo + 1) / 2) ((K1U - mulF mlo M1D + 1) / 2) : ℕ) ≤
        (hpSum ((vs.map fun v => v.t.lo).map mkTm) : ℕ) := by exact_mod_cast hhp
    have hltm' : (L * (1 / 10 ^ 6) + 1 / 25000) * S ≤ ltm := by rwa [le_div_iff₀ hS] at hltm
    have key : (∑ j ∈ range vs.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000) * S ≤ 0 := by
      have hXS : (∑ j ∈ range vs.length, s j * (t j - 1)) * S ≤
          -((hpSum ((vs.map fun v => v.t.lo).map mkTm) : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hX hS.le
        rwa [div_mul_cancel₀ _ hS.ne'] at this
      have hcS : clampR γ m * S ≤ clampR 0 ((mlo : ℝ) / S) * S :=
        mul_le_mul_of_nonneg_right (hc1.trans hc2) hS.le
      have hγS : γ / 2 * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
      have hLS : 0 ≤ L * (1 / 10 ^ 6) * S := by positivity
      nlinarith
    by_contra hcon
    have := mul_pos (show 0 < ∑ j ∈ range vs.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000 by
      linarith) hS
    linarith
  · -- the intervals
    have hγ1 : γ ≤ 1 := hγ.trans (ghx_le_one β)
    exact runI3_sound hvt hok hltm k 0 0 h hrun (by norm_num) (Or.inl rfl)
      (fun _ => by rw [Nat.cast_zero]; exact mul_nonneg (tops_pos 0 (by norm_num)).le hS.le) γ
      (by rw [Nat.cast_zero, zero_div]; exact hγ0) hγ1 β m s t h1 h2 hγ ht hk hlv hm hs hsum

/-! ### The large values' terms of the test's two kinds of terms -/

/-- The large values' terms of `mkTv ub lo` bound the term of a class at `lo/S ≤ s ≤ (ub + lo)/S`. -/
lemma lvok_mkTv {lo ub : ℕ} {s t β γ : ℝ} (hs : (lo : ℝ) / S ≤ s) (hhi : s ≤ ((ub + lo : ℕ) : ℝ) / S)
    (ht : t ≤ β + 4 / 10 ^ 6) (hβ : β ≤ 11 / 12)
    (hlv : ∀ k : ℕ, 1 ≤ k → γ ≤ lvExp k s (t - 1 / 10 ^ 6)) : LVok (mkTv ub lo) s t γ := by
  intro a b lam hab hbS hlam0 hlam1 hγ
  rw [mkTv_t, mkTm_lo, mkTv_k1, mkTv_g1, mkTv_k2, mkTv_g2]
  exact ⟨lvU_le hab hbS hs hhi ht hβ hlam0 hlam1 hγ hlv, lvU_le hab hbS hs hhi ht hβ hlam0 hlam1 hγ hlv⟩

/-- The bound's four values at `γ` between the ends of `[a, b]`: at most the mean of numbers above them at the ends
(as `lvVal_ge` gives them). -/
lemma lv_mean_le {lo k a b : ℕ} {γ lam Va Vb : ℝ} (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ = (1 - lam) * (a / S) + lam * (b / S))
    (f0a : (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ Va) (f1a : (OFF : ℝ) + (lvE * S - a) / (2 * k) ≤ Va)
    (f2a : (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - a) / (4 * k) ≤ Va)
    (f3a : (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - a) / (4 * k) ≤ Va)
    (f0b : (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ Vb) (f1b : (OFF : ℝ) + (lvE * S - b) / (2 * k) ≤ Vb)
    (f2b : (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - b) / (4 * k) ≤ Vb)
    (f3b : (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - b) / (4 * k) ≤ Vb) :
    max (max (-((lo : ℝ) / S * (3 / 10 - lvE))) ((lvE - γ) / (2 * k)))
        (max ((1 / 2 + lvE - γ - k * ((lo : ℝ) / S)) / (4 * k))
          ((4 / 3 + lvE - γ - 2 * k * ((lo : ℝ) / S)) / (4 * k))) ≤
      ((1 - lam) * Va + lam * Vb - OFF) / S := by
  have hS := S_pos
  have h1lam : 0 ≤ 1 - lam := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hγS : γ * S = (1 - lam) * a + lam * b := by
    rw [hγ]; field_simp
  have h2k : (0 : ℝ) < 2 * k := by linarith
  have h4k : (0 : ℝ) < 4 * k := by linarith
  have hloS : (lo : ℝ) / S * S = lo := div_mul_cancel₀ _ hS.ne'
  have t0 : -((lo : ℝ) / S * (3 / 10 - lvE)) ≤ ((1 - lam) * Va + lam * Vb - OFF) / S := by
    rw [le_div_iff₀ hS]
    have e : -((lo : ℝ) / S * (3 / 10 - lvE)) * S = -(lo * (3 / 10 - lvE)) := by
      linear_combination (-(3 / 10 - lvE)) * hloS
    rw [e]
    have e1 := mul_nonneg h1lam (sub_nonneg.2 f0a)
    have e2 := mul_nonneg hlam0 (sub_nonneg.2 f0b)
    nlinarith
  have t1 : (lvE - γ) / (2 * k) ≤ ((1 - lam) * Va + lam * Vb - OFF) / S := by
    rw [le_div_iff₀ hS]
    have e : (lvE - γ) / (2 * k) * S = (lvE * S - γ * S) / (2 * k) := by ring
    rw [e]
    exact conv_le h2k hlam0 hlam1 hγS f1a f1b
  have t2 : (1 / 2 + lvE - γ - k * ((lo : ℝ) / S)) / (4 * k) ≤ ((1 - lam) * Va + lam * Vb - OFF) / S := by
    rw [le_div_iff₀ hS]
    have e : (1 / 2 + lvE - γ - k * ((lo : ℝ) / S)) / (4 * k) * S =
        ((1 / 2 + lvE) * S - k * lo - γ * S) / (4 * k) := by
      rw [div_mul_eq_mul_div]
      congr 1
      linear_combination (-(k : ℝ)) * hloS
    rw [e]
    exact conv_le h4k hlam0 hlam1 hγS f2a f2b
  have t3 : (4 / 3 + lvE - γ - 2 * k * ((lo : ℝ) / S)) / (4 * k) ≤ ((1 - lam) * Va + lam * Vb - OFF) / S := by
    rw [le_div_iff₀ hS]
    have e : (4 / 3 + lvE - γ - 2 * k * ((lo : ℝ) / S)) / (4 * k) * S =
        ((4 / 3 + lvE) * S - 2 * k * lo - γ * S) / (4 * k) := by
      rw [div_mul_eq_mul_div]
      congr 1
      linear_combination (-(2 * (k : ℝ))) * hloS
    rw [e]
    exact conv_le h4k hlam0 hlam1 hγS f3a f3b
  exact max_le (max_le t0 t1) (max_le t2 t3)

/-! ### A class carried to the upper end of its cell -/

/-- **The moments' condition carried to a longer sum**: with `s ≤ s′` and the size `t′ = 1/2 + (s/s′)(t − 1/2)`,
the count exponent that the moments allow at `(s, t)` is allowed at `(s′, t′)`. -/
lemma mom_carry {k : ℕ} {s s' t γ : ℝ} (hss : s ≤ s') (hs' : 0 < s')
    (h : γ ≤ momExp k s (t - 1 / 10 ^ 6)) : γ ≤ momExp k s' (1 / 2 + s / s' * (t - 1 / 2) - 1 / 10 ^ 6) := by
  unfold momExp at h ⊢
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have e : s' * (s / s' * (t - 1 / 2)) = s * (t - 1 / 2) := by field_simp
  have h1 : max 1 ((k : ℝ) * s) ≤ max 1 (k * s') := max_le_max le_rfl (mul_le_mul_of_nonneg_left hss hk0)
  have h2 : (k : ℝ) * s' * (1 - 2 * (1 / 2 + s / s' * (t - 1 / 2) - 1 / 10 ^ 6)) =
      k * s * (1 - 2 * t) + 2 / 10 ^ 6 * (k * s') := by
    linear_combination (-2 * (k : ℝ)) * e
  have h3 : (k : ℝ) * s ≤ k * s' := mul_le_mul_of_nonneg_left hss hk0
  rw [h2]
  have h4 : (k : ℝ) * s * (1 - 2 * (t - 1 / 10 ^ 6)) = k * s * (1 - 2 * t) + 2 / 10 ^ 6 * (k * s) := by ring
  rw [h4] at h
  nlinarith

/-- The carried size is at most the zero's real part, as the size is. -/
lemma carry_le {s s' t β : ℝ} (hs0 : 0 ≤ s) (hss : s ≤ s') (hs' : 0 < s') (hβ : 1 / 2 ≤ β)
    (ht : t ≤ β + 4 / 10 ^ 6) : 1 / 2 + s / s' * (t - 1 / 2) ≤ β + 4 / 10 ^ 6 := by
  have h0 : 0 ≤ s / s' := div_nonneg hs0 hs'.le
  have h1 : s / s' ≤ 1 := (div_le_one hs').2 hss
  rcases le_total (1 / 2) t with h | h
  · have : s / s' * (t - 1 / 2) ≤ 1 * (t - 1 / 2) := mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  · have : s / s' * (t - 1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
    linarith

/-- The carried term: `s′(t′ − 1) = s(t − 1) − (s′ − s)/2`. -/
lemma carry_term {s s' t : ℝ} (hs' : 0 < s') :
    s' * (1 / 2 + s / s' * (t - 1 / 2) - 1) = s * (t - 1) - (s' - s) / 2 := by
  have e : s' * (s / s' * (t - 1 / 2)) = s * (t - 1 / 2) := by field_simp
  linear_combination e

/-- The bound's four values fall by at least half of what the exponent gains. -/
lemma max4_shift {k : ℕ} (hk : 1 ≤ k) {s s' γ : ℝ} (hss : s ≤ s') :
    max (max (-(s * (3 / 10 - lvE))) ((lvE - γ) / (2 * k)))
        (max ((1 / 2 + lvE - γ - k * s) / (4 * k)) ((4 / 3 + lvE - γ - 2 * k * s) / (4 * k))) - (s' - s) / 2 ≤
      max (max (-(s' * (3 / 10 - lvE))) ((lvE - γ) / (2 * k)))
        (max ((1 / 2 + lvE - γ - k * s') / (4 * k)) ((4 / 3 + lvE - γ - 2 * k * s') / (4 * k))) := by
  have hE : lvE = 1 / 10 ^ 5 := rfl
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h4k : (0 : ℝ) < 4 * k := by linarith
  have hd : 0 ≤ s' - s := by linarith
  rw [sub_le_iff_le_add]
  generalize hM : max (max (-(s' * (3 / 10 - lvE))) ((lvE - γ) / (2 * k)))
      (max ((1 / 2 + lvE - γ - k * s') / (4 * k)) ((4 / 3 + lvE - γ - 2 * k * s') / (4 * k))) = M
  have m1 : -(s' * (3 / 10 - lvE)) ≤ M := by
    rw [← hM]; exact (le_max_left _ _).trans (le_max_left _ _)
  have m2 : (lvE - γ) / (2 * k) ≤ M := by
    rw [← hM]; exact (le_max_right _ _).trans (le_max_left _ _)
  have m3 : (1 / 2 + lvE - γ - k * s') / (4 * k) ≤ M := by
    rw [← hM]; exact (le_max_left _ _).trans (le_max_right _ _)
  have m4 : (4 / 3 + lvE - γ - 2 * k * s') / (4 * k) ≤ M := by
    rw [← hM]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · have : (s' - s) * (3 / 10 - lvE) ≤ (s' - s) * (1 / 2) := mul_le_mul_of_nonneg_left (by rw [hE]; norm_num) hd
    linarith
  · linarith
  · have e : (1 / 2 + lvE - γ - k * s) / (4 * k) = (1 / 2 + lvE - γ - k * s') / (4 * k) + (s' - s) / 4 := by
      field_simp
      ring
    rw [e]
    linarith
  · have e : (4 / 3 + lvE - γ - 2 * k * s) / (4 * k) = (4 / 3 + lvE - γ - 2 * k * s') / (4 * k) + (s' - s) / 2 := by
      field_simp
      ring
    rw [e]
    linarith

/-- **The large values' term at the upper end bounds a carried class**: for a cell `lo/S ≤ s ≤ hi/S`, a class at
`s` with the counts by large values, and a size `t′ ≤ β + w` with `(hi/S)(t′ − 1) = s(t − 1) − (hi/S − s)/2`, the
term of the power `k` at `hi`, with the cell's threshold `lvG lo hi k`, bounds `(hi/S)(t′ − 1) − (hi/S)τ` between
the ends of an interval. -/
lemma lvU_carry {lo hi k a b : ℕ} {s t t' β γ lam : ℝ} (hab : a ≤ b) (hbS : b ≤ S) (hs : (lo : ℝ) / S ≤ s)
    (hhi : s ≤ (hi : ℝ) / S) (ht' : t' ≤ β + 4 / 10 ^ 6) (hβ : β ≤ 11 / 12)
    (hcarry : (hi : ℝ) / S * (t' - 1) = s * (t - 1) - ((hi : ℝ) / S - s) / 2)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ = (1 - lam) * (a / S) + lam * (b / S))
    (hlv : ∀ k : ℕ, 1 ≤ k → γ ≤ lvExp k s (t - 1 / 10 ^ 6)) :
    (hi : ℝ) / S * (t' - 1) - (hi : ℝ) / S * (1 / 10 ^ 6) ≤
      ((1 - lam) * (lvU hi k (lvG lo hi k) a a : ℕ) + lam * (lvU hi k (lvG lo hi k) a b : ℕ) - OFF) / S := by
  have hS := S_pos
  have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
  have hs0 : 0 ≤ s := hlo0.trans hs
  have hhi0 : (0 : ℝ) ≤ hi / S := hs0.trans hhi
  by_cases hg : lvG lo hi k < a
  · rw [lvU_of_lt hg, lvU_of_lt hg]
    obtain ⟨hk, hE23, hgv⟩ := lvG_lt (hab.trans hbS) hg
    obtain ⟨f0a, f1a, f2a, f3a⟩ := lvVal_ge (lo := hi) (x := a) hk
    obtain ⟨f0b, f1b, f2b, f3b⟩ := lvVal_ge (lo := hi) (x := b) hk
    refine le_trans ?_ (lv_mean_le hk hlam0 hlam1 hγ f0a f1a f2a f3a f0b f1b f2b f3b)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hE : lvE = 1 / 10 ^ 5 := rfl
    -- `γ·S ≥ a`
    have hγS : γ * S = (1 - lam) * a + lam * b := by
      rw [hγ]; field_simp
    have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hγa : (a : ℝ) ≤ γ * S := by
      rw [hγS]
      have := mul_nonneg hlam0 (sub_nonneg.2 habr)
      linarith
    -- `k·s ≥ 2/3 + lvE`
    have hklo : 2 / 3 + lvE ≤ k * ((lo : ℝ) / S) := by
      have h1 := E23_ge
      have h2 : (E23 : ℝ) ≤ k * lo := by exact_mod_cast hE23
      rw [mul_div_assoc', le_div_iff₀ hS]
      linarith
    have hks : (k : ℝ) * ((lo : ℝ) / S) ≤ k * s := mul_le_mul_of_nonneg_left hs hk0.le
    -- the threshold at `s` is below the cell's, which is below `γ`
    have hΓ0 : lvE + max (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))
        (max (1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE)) (4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE))) <
        γ := by
      have h2 : ((lvGv lo hi k : ℕ) : ℝ) < a := by exact_mod_cast hgv
      exact lt_of_mul_lt_mul_right (lt_of_le_of_lt (lvGv_ge lo hi k) (lt_of_lt_of_le h2 hγa)) hS.le
    have hΓ : lvE + max (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))
        (max (1 / 2 - k * s * (1 / 5 - 4 * lvE)) (4 / 3 - k * s * (6 / 5 - 4 * lvE))) < γ := by
      have h2 : 1 / 2 - k * s * (1 / 5 - 4 * lvE) ≤ 1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE) := by
        have := mul_le_mul_of_nonneg_right hks (by rw [hE]; norm_num : (0 : ℝ) ≤ 1 / 5 - 4 * lvE)
        linarith
      have h3 : 4 / 3 - k * s * (6 / 5 - 4 * lvE) ≤ 4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE) := by
        have := mul_le_mul_of_nonneg_right hks (by rw [hE]; norm_num : (0 : ℝ) ≤ 6 / 5 - 4 * lvE)
        linarith
      have hmax := max_le_max (le_refl (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))) (max_le_max h2 h3)
      linarith
    have hbd := lv_bound hk hs0 le_rfl hhi (hklo.trans hks) hΓ (hlv k hk)
    have hsh := max4_shift hk (γ := γ) hhi
    have hτ : s * (1 / 10 ^ 6) ≤ (hi : ℝ) / S * (1 / 10 ^ 6) := mul_le_mul_of_nonneg_right hhi (by norm_num)
    rw [hcarry]
    linarith
  · -- the term does not apply: the bound `0`
    rw [lvU_of_not_lt hg, lvU_of_not_lt hg]
    have h1 : (hi : ℝ) / S * (t' - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hhi0 (by linarith)
    have h2 : 0 ≤ (hi : ℝ) / S * (1 / 10 ^ 6) := by positivity
    have e : ((1 - lam) * (OFF : ℝ) + lam * (OFF : ℝ) - OFF) / S = 0 := by ring
    rw [e]
    linarith

lemma mkTvH_t (lo hi : ℕ) : (mkTvH lo hi).t = mkTm hi := rfl

lemma mkTvH_k1 (lo hi : ℕ) : (mkTvH lo hi).k1 = (S + (hi - 1)) / hi - 1 := rfl

lemma mkTvH_g1 (lo hi : ℕ) : (mkTvH lo hi).g1 = lvG lo hi ((S + (hi - 1)) / hi - 1) := rfl

lemma mkTvH_k2 (lo hi : ℕ) : (mkTvH lo hi).k2 = (S + (hi - 1)) / hi - 2 := rfl

lemma mkTvH_g2 (lo hi : ℕ) : (mkTvH lo hi).g2 = lvG lo hi ((S + (hi - 1)) / hi - 2) := rfl

/-- **The large values' terms of `mkTvH lo hi` bound a class carried to the upper end** `hi/S` of its cell. -/
lemma lvok_carry {lo hi : ℕ} {s t t' β γ : ℝ} (hs : (lo : ℝ) / S ≤ s) (hhi : s ≤ (hi : ℝ) / S)
    (ht' : t' ≤ β + 4 / 10 ^ 6) (hβ : β ≤ 11 / 12)
    (hcarry : (hi : ℝ) / S * (t' - 1) = s * (t - 1) - ((hi : ℝ) / S - s) / 2)
    (hlv : ∀ k : ℕ, 1 ≤ k → γ ≤ lvExp k s (t - 1 / 10 ^ 6)) : LVok (mkTvH lo hi) ((hi : ℝ) / S) t' γ := by
  intro a b lam hab hbS hlam0 hlam1 hγ
  rw [mkTvH_t, mkTm_lo, mkTvH_k1, mkTvH_g1, mkTvH_k2, mkTvH_g2]
  exact ⟨lvU_carry hab hbS hs hhi ht' hβ hcarry hlam0 hlam1 hγ hlv,
    lvU_carry hab hbS hs hhi ht' hβ hcarry hlam0 hlam1 hγ hlv⟩

/-! ### The two corners -/

lemma clampR_nonneg (γ m : ℝ) : 0 ≤ clampR γ m := by
  unfold clampR
  exact le_min (div_nonneg (le_max_right _ _) (by norm_num)) (le_max_left _ _)

/-- **The clamp between the corners**: if the bound holds with the clamp at `μ` and the terms lowered by `D/2`, and
holds with no clamp, it holds with the clamp at any `m ≥ μ + (12/11)D`: the clamp's first line falls by half of what
`m` gains, its second by `(11/12 + d)/2` of it. -/
lemma clamp_step {γ μ m D X c : ℝ} (hD : 0 ≤ D) (hm : μ + 12 / 11 * D ≤ m)
    (hstar : X - D / 2 + γ / 2 + clampR γ μ ≤ c) (hdia : X + γ / 2 ≤ c) : X + γ / 2 + clampR γ m ≤ c := by
  unfold clampR y0R at hstar ⊢
  have hA := min_le_left (max (1 - m) 0 / 2)
    (max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2))
  have hB := min_le_right (max (1 - m) 0 / 2)
    (max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2))
  have h1 : max (1 - m) 0 / 2 ≤ max (max (1 - μ) 0 / 2 - D / 2) 0 := by
    rcases le_total (1 - m) 0 with h | h
    · rw [max_eq_right h]
      exact le_trans (by norm_num) (le_max_right _ _)
    · rw [max_eq_left h]
      have := le_max_left (1 - μ) 0
      exact le_trans (by linarith) (le_max_left _ _)
  have h2 : max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2) ≤
      max (max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - μ * (11 / 12 + 1 / 1000)) / 2) - D / 2) 0 := by
    rcases le_total (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2) 0 with h | h
    · rw [max_eq_left h]
      exact le_max_right _ _
    · rw [max_eq_right h]
      have := le_max_right 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - μ * (11 / 12 + 1 / 1000)) / 2)
      exact le_trans (by linarith) (le_max_left _ _)
  rcases min_choice (max (1 - μ) 0 / 2)
      (max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - μ * (11 / 12 + 1 / 1000)) / 2)) with hmin | hmin
  · rw [hmin] at hstar
    rcases le_max_iff.1 h1 with h | h <;> linarith
  · rw [hmin] at hstar
    rcases le_max_iff.1 h2 with h | h <;> linarith

/-- The entries of a list of pairs' image, read by index. -/
lemma getD_map_eq {α : Type} (f : α → ℕ) (ps : List α) {j : ℕ} (hj : j < ps.length) :
    (ps.map f).getD j 0 = f ps[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map]

/-- The sum of a list's image, in the reals, by index. -/
lemma sum_map_eq {α : Type} (f : α → ℕ) (ps : List α) :
    ∑ j ∈ range ps.length, (((ps.map f).getD j 0 : ℕ) : ℝ) = (sumN (ps.map f) : ℕ) := by
  have h := sum_getD_eq (ps.map f)
  rwa [List.length_map] at h

set_option maxHeartbeats 1600000 in
/-- **The two corners give the box.** For cells `(lo_j, hi_j)` in the fixed point, `lo_j ≤ hi_j`, `0 < hi_j`,
`hi_j ≤ ub + lo_j`: if the bound holds at the upper corner (the terms `mkTvH lo hi`) with the variable at least
`mH/S`, where `mH + (Σhi − Σlo)/11 + Σhi + w·S ≤ L·S`, and at the lower corner (the terms `mkTv ub lo`) with the
variable at least `1`, then the window's condition holds at every exponents `lo_j/S ≤ s_j ≤ hi_j/S` of the rest and
every `m ≥ L − w − Σ_j s_j`: a class at `s` is carried to the upper corner, where its terms are lower by half of
`D = Σ(hi_j/S − s_j)` and the variable is shorter by `(12/11)D` at least (`clamp_step`). -/
theorem two_corner {L w : ℝ} (hw : 0 ≤ w) {ps : List (ℕ × ℕ)} {mH ub : ℕ}
    (hps : ∀ p ∈ ps, p.1 ≤ p.2 ∧ 0 < p.2) (hub : ∀ p ∈ ps, p.2 ≤ ub + p.1)
    (hH : ∀ γ, GoalAtV L (ps.map fun p => mkTvH p.1 p.2) mH γ)
    (hLo : ∀ γ, GoalAtV L (ps.map fun p => mkTv ub p.1) S γ)
    (hmH : (mH : ℝ) + (((sumN (ps.map fun p => p.2) : ℕ) : ℝ) - (sumN (ps.map fun p => p.1) : ℕ)) / 11 +
        (sumN (ps.map fun p => p.2) : ℕ) + w * S ≤ L * S)
    {m : ℝ} {s : ℕ → ℝ}
    (hs : ∀ j (hj : j < ps.length), (ps[j].1 : ℝ) / S ≤ s j ∧ s j ≤ (ps[j].2 : ℝ) / S)
    (hm : L - w ≤ ∑ j ∈ range ps.length, s j + m) : ResCond ghx L ps.length m s := by
  have hS := S_pos
  intro β γ t h1 h2 hγ ht hk hlv
  refine binOK_of ?_
  -- the upper corner and the carried sizes
  obtain ⟨s', hs'def⟩ : ∃ s' : ℕ → ℝ, s' = fun j => (((ps.map fun p => p.2).getD j 0 : ℕ) : ℝ) / S := ⟨_, rfl⟩
  obtain ⟨t', ht'def⟩ : ∃ t' : ℕ → ℝ, t' = fun j => 1 / 2 + s j / s' j * (t j - 1 / 2) := ⟨_, rfl⟩
  have hs'j : ∀ j (hj : j < ps.length), s' j = (ps[j].2 : ℝ) / S := fun j hj => by
    rw [hs'def]
    show (((ps.map fun p => p.2).getD j 0 : ℕ) : ℝ) / S = _
    rw [getD_map_eq (fun p => p.2) ps hj]
  have hpos : ∀ j (hj : j < ps.length), 0 < s' j := fun j hj => by
    rw [hs'j j hj]
    exact div_pos (by exact_mod_cast (hps _ (List.getElem_mem hj)).2) hS
  have hs0 : ∀ j (hj : j < ps.length), 0 ≤ s j := fun j hj =>
    le_trans (div_nonneg (Nat.cast_nonneg _) hS.le) (hs j hj).1
  have hss : ∀ j (hj : j < ps.length), s j ≤ s' j := fun j hj => by rw [hs'j j hj]; exact (hs j hj).2
  have ht'j : ∀ j, t' j = 1 / 2 + s j / s' j * (t j - 1 / 2) := fun j => by rw [ht'def]
  have hlenH : (ps.map fun p => mkTvH p.1 p.2).length = ps.length := List.length_map _
  have hlenL : (ps.map fun p => mkTv ub p.1).length = ps.length := List.length_map _
  -- the sums
  have hsum' : ∑ j ∈ range ps.length, s' j = ((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S := by
    rw [hs'def, ← sum_map_eq (fun p => p.2) ps, Finset.sum_div]
  have hsumlo : ((sumN (ps.map fun p => p.1) : ℕ) : ℝ) / S ≤ ∑ j ∈ range ps.length, s j := by
    rw [← sum_map_eq (fun p => p.1) ps, Finset.sum_div]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [getD_map_eq (fun p => p.1) ps hj']
    exact (hs j hj').1
  have hsums : ∑ j ∈ range ps.length, s j ≤ ∑ j ∈ range ps.length, s' j :=
    Finset.sum_le_sum fun j hj => hss j (Finset.mem_range.1 hj)
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ∑ j ∈ range ps.length, s' j - ∑ j ∈ range ps.length, s j := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; linarith
  have hmH' : (mH : ℝ) / S + (((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S -
      ((sumN (ps.map fun p => p.1) : ℕ) : ℝ) / S) / 11 + ((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S + w ≤ L := by
    have h := div_le_div_of_nonneg_right hmH hS.le
    rw [mul_div_assoc, div_self hS.ne', mul_one] at h
    have e : ((mH : ℝ) + (((sumN (ps.map fun p => p.2) : ℕ) : ℝ) - (sumN (ps.map fun p => p.1) : ℕ)) / 11 +
        (sumN (ps.map fun p => p.2) : ℕ) + w * S) / S =
        (mH : ℝ) / S + (((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S -
          ((sumN (ps.map fun p => p.1) : ℕ) : ℝ) / S) / 11 + ((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S + w := by
      field_simp
    rw [e] at h
    exact h
  have hmH0 : (0 : ℝ) ≤ (mH : ℝ) / S := div_nonneg (Nat.cast_nonneg _) hS.le
  have hDmax : D ≤ ((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S - ((sumN (ps.map fun p => p.1) : ℕ) : ℝ) / S := by
    rw [hDdef, hsum']
    linarith
  -- the lower corner: no clamp
  have hdia : ∑ j ∈ range ps.length, s j * (t j - 1) + γ / 2 ≤ -(1 / 25000) := by
    have h := hLo γ β 1 s t h1 h2 hγ (by rw [hlenL]; exact ht) (by rw [hlenL]; exact hk)
      (fun j hj => by
        have hj' : j < ps.length := by rw [hlenL] at hj; exact hj
        rw [List.getElem_map]
        refine lvok_mkTv (hs j hj').1 ?_ (ht j hj') h2 (hlv j hj')
        refine (hs j hj').2.trans (div_le_div_of_nonneg_right ?_ hS.le)
        exact_mod_cast hub _ (List.getElem_mem hj'))
      (by rw [div_self hS.ne'])
      (fun j hj => by
        have hj' : j < ps.length := by rw [hlenL] at hj; exact hj
        rw [List.getElem_map, mkTv_t, mkTm_lo]
        exact (hs j hj').1)
      (by rw [hlenL]; linarith)
    rw [hlenL] at h
    have := clampR_nonneg γ 1
    linarith
  -- the upper corner, with the carried class
  have hstar : ∑ j ∈ range ps.length, s' j * (t' j - 1) + γ / 2 + clampR γ ((mH : ℝ) / S) ≤ -(1 / 25000) := by
    have h := hH γ β ((mH : ℝ) / S) s' t' h1 h2 hγ
      (fun j hj => by
        have hj' : j < ps.length := by rw [hlenH] at hj; exact hj
        rw [ht'j]
        exact carry_le (hs0 j hj') (hss j hj') (hpos j hj') h1 (ht j hj'))
      (fun j hj k hk1 => by
        have hj' : j < ps.length := by rw [hlenH] at hj; exact hj
        rw [ht'j]
        exact mom_carry (hss j hj') (hpos j hj') (hk j hj' k hk1))
      (fun j hj => by
        have hj' : j < ps.length := by rw [hlenH] at hj; exact hj
        rw [List.getElem_map, hs'j j hj']
        refine lvok_carry (hs j hj').1 (hs j hj').2 ?_ h2 ?_ (hlv j hj')
        · rw [ht'j]
          exact carry_le (hs0 j hj') (hss j hj') (hpos j hj') h1 (ht j hj')
        · rw [ht'j, hs'j j hj']
          exact carry_term (by rw [← hs'j j hj']; exact hpos j hj'))
      le_rfl
      (fun j hj => by
        have hj' : j < ps.length := by rw [hlenH] at hj; exact hj
        rw [List.getElem_map, mkTvH_t, mkTm_lo, hs'j j hj'])
      (by rw [hlenH, hsum']; linarith)
    rw [hlenH] at h
    exact h
  have hXD : ∑ j ∈ range ps.length, s' j * (t' j - 1) =
      ∑ j ∈ range ps.length, s j * (t j - 1) - D / 2 := by
    have e : ∀ j ∈ range ps.length, s' j * (t' j - 1) = s j * (t j - 1) - (s' j - s j) / 2 := fun j hj => by
      rw [ht'j]
      exact carry_term (hpos j (Finset.mem_range.1 hj))
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, hDdef]
  have hm' : (mH : ℝ) / S + 12 / 11 * D ≤ m := by
    have e : ∑ j ∈ range ps.length, s j = ((sumN (ps.map fun p => p.2) : ℕ) : ℝ) / S - D := by
      rw [hDdef, hsum']; ring
    rw [e] at hm
    linarith
  rw [hXD] at hstar
  exact clamp_step hD0 hm' (by linarith) hdia

/-! ### `resY` -/

lemma W2_ge : 2 / 10 ^ 5 * (S : ℝ) ≤ W2 := by rw [S_real]; norm_num [W2]

/-- A positive `loW` is at most the cell's lower end less the margin, in the fixed point. -/
lemma loW_le {Lnum Lden c : ℕ} (hLd : 0 < Lden) (h : 0 < loW Lnum Lden c) :
    (loW Lnum Lden c : ℝ) / S ≤ (Lnum : ℝ) / Lden / DEN * c - 2 / 10 ^ 5 := by
  have hS := S_pos
  have hD : (0 : ℝ) < DEN := by norm_num [DEN]
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have e0 : loW Lnum Lden c = Lnum * c * S / (Lden * DEN) - W2 := rfl
  rw [e0] at h ⊢
  have hlt : W2 ≤ Lnum * c * S / (Lden * DEN) := by omega
  rw [Nat.cast_sub hlt, div_le_iff₀ hS]
  have h1 := div_cast_le (Lnum * c * S) (Lden * DEN)
  push_cast at h1
  have h2 := W2_ge
  have e2 : (Lnum : ℝ) * c * S / (Lden * DEN) = (Lnum : ℝ) / Lden / DEN * c * S := by field_simp
  rw [e2] at h1
  have e3 : ((Lnum : ℝ) / Lden / DEN * c - 2 / 10 ^ 5) * S = (Lnum : ℝ) / Lden / DEN * c * S - 2 / 10 ^ 5 * S := by
    ring
  rw [e3]
  linarith

/-- `hiW` is at least the cell's upper end with the margin, in the fixed point. -/
lemma hiW_ge {Lnum Lden d : ℕ} (hLd : 0 < Lden) :
    (Lnum : ℝ) / Lden / DEN * d + 2 / 10 ^ 5 ≤ (hiW Lnum Lden d : ℝ) / S := by
  have hS := S_pos
  have hD : (0 : ℝ) < DEN := by norm_num [DEN]
  have hDn : 0 < DEN := by norm_num [DEN]
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have e0 : hiW Lnum Lden d = (Lnum * d * S + (Lden * DEN - 1)) / (Lden * DEN) + W2 := rfl
  rw [e0, le_div_iff₀ hS]
  have hd : 0 < Lden * DEN := Nat.mul_pos hLd hDn
  have h1 := le_cdiv_mul (Lnum * d * S) (Lden * DEN) hd
  have h1' : ((Lnum * d * S : ℕ) : ℝ) ≤
      (((Lnum * d * S + (Lden * DEN - 1)) / (Lden * DEN) : ℕ) : ℝ) * ((Lden * DEN : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2 := W2_ge
  have h3 : (Lnum : ℝ) / Lden / DEN * d * S ≤ (((Lnum * d * S + (Lden * DEN - 1)) / (Lden * DEN) : ℕ) : ℝ) := by
    have e : (Lnum : ℝ) / Lden / DEN * d * S = ((Lnum * d * S : ℕ) : ℝ) / ((Lden * DEN : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e, div_le_iff₀ (by exact_mod_cast hd)]
    exact h1'
  push_cast
  have e3 : ((Lnum : ℝ) / Lden / DEN * d + 2 / 10 ^ 5) * S = (Lnum : ℝ) / Lden / DEN * d * S + 2 / 10 ^ 5 * S := by
    ring
  rw [e3]
  linarith

/-- The lower end of a cell is below the upper end of a larger one, in the fixed point. -/
lemma loW_le_hiW {Lnum Lden c d : ℕ} (hcd : c ≤ d) : loW Lnum Lden c ≤ hiW Lnum Lden d := by
  have e0 : loW Lnum Lden c = Lnum * c * S / (Lden * DEN) - W2 := rfl
  have e1 : hiW Lnum Lden d = (Lnum * d * S + (Lden * DEN - 1)) / (Lden * DEN) + W2 := rfl
  rw [e0, e1]
  have h1 : Lnum * c * S / (Lden * DEN) ≤ (Lnum * d * S + (Lden * DEN - 1)) / (Lden * DEN) :=
    Nat.div_le_div_right
      (le_trans (Nat.mul_le_mul_right S (Nat.mul_le_mul_left Lnum hcd)) (Nat.le_add_right _ _))
  omega

attribute [local irreducible] loW hiW

/-- What `okY` checks of each cell. -/
lemma okY_mem {Lnum Lden : ℕ} : ∀ {cells : List (ℕ × ℕ)}, okY Lnum Lden cells = true →
    ∀ c ∈ cells, c.1 ≤ c.2 ∧ 0 < loW Lnum Lden c.1
  | [], _, c, hc => absurd hc List.not_mem_nil
  | x :: xs, h, c, hc => by
    have e : okY Lnum Lden (x :: xs) =
        (Nat.ble x.1 x.2 && Nat.blt 0 (loW Lnum Lden x.1) && okY Lnum Lden xs) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact ⟨h.1.1, h.1.2⟩
    · exact okY_mem h.2 c hc'

lemma sumN_cons (x : ℕ) (xs : List ℕ) : sumN (x :: xs) = x + sumN xs := rfl

/-- With `lo ≤ hi` for each pair, the lower ends sum to at most the upper ends. -/
lemma sum_fst_le : ∀ {ps : List (ℕ × ℕ)}, (∀ p ∈ ps, p.1 ≤ p.2) →
    sumN (ps.map fun p => p.1) ≤ sumN (ps.map fun p => p.2)
  | [], _ => le_rfl
  | x :: xs, h => by
    rw [List.map_cons, List.map_cons, sumN_cons, sumN_cons]
    have h1 := h x (List.mem_cons_self)
    have h2 := sum_fst_le (ps := xs) fun p hp => h p (List.mem_cons_of_mem _ hp)
    omega

/-- With `lo ≤ hi` for each pair, a pair's width is at most the sum of the widths. -/
lemma width_le : ∀ {ps : List (ℕ × ℕ)}, (∀ p ∈ ps, p.1 ≤ p.2) → ∀ p ∈ ps,
    p.2 + sumN (ps.map fun p => p.1) ≤ sumN (ps.map fun p => p.2) + p.1
  | [], _, p, hp => absurd hp List.not_mem_nil
  | x :: xs, h, p, hp => by
    rw [List.map_cons, List.map_cons, sumN_cons, sumN_cons]
    have h1 := h x (List.mem_cons_self)
    have h2 := sum_fst_le (ps := xs) fun p hp => h p (List.mem_cons_of_mem _ hp)
    rcases List.mem_cons.1 hp with rfl | hp'
    · omega
    · have h3 := width_le (ps := xs) (fun p hp => h p (List.mem_cons_of_mem _ hp)) p hp'
      omega

set_option maxHeartbeats 1600000 in
/-- **`resY` is sound**: at `L = Lnum/Lden`, with `κ = L/DEN`, the test on the cells `(c_j, d_j)` gives the window's
condition with the variable tied to the rest, `SieveTypeIIHM.ResBoxT`, on the exponents
`κ·c_j − 2·10⁻⁵ ≤ s_j ≤ κ·d_j + 2·10⁻⁵` with `Σ_j s_j + m ≥ L − 2·10⁻⁵`. -/
theorem resY_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cells : List (ℕ × ℕ)} {kH hH kL hL : ℕ}
    (hT : resY Lnum Lden cells kH hH kL hL = true) :
    ResBoxT ghx ((Lnum : ℝ) / Lden) cells.length
      (fun j => (Lnum : ℝ) / Lden / DEN * ((cells.getD j (0, 0)).1 : ℕ) - 2 / 10 ^ 5)
      (fun j => (Lnum : ℝ) / Lden / DEN * ((cells.getD j (0, 0)).2 : ℕ) + 2 / 10 ^ 5) (2 / 10 ^ 5) := by
  have hS := S_pos
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  unfold resY at hT
  dsimp only at hT
  simp only [Bool.and_eq_true, Nat.ble_eq] at hT
  obtain ⟨⟨⟨hok, hneed⟩, hTH⟩, hTL⟩ := hT
  obtain ⟨ps, hpsdef⟩ : ∃ ps : List (ℕ × ℕ), ps = cells.map fun c => (loW Lnum Lden c.1, hiW Lnum Lden c.2) :=
    ⟨_, rfl⟩
  rw [← hpsdef] at hneed hTH hTL
  have hL : (0 : ℝ) ≤ (Lnum : ℝ) / Lden := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcells := okY_mem hok
  have hlen : ps.length = cells.length := by rw [hpsdef, List.length_map]
  have hget : ∀ j (hj : j < ps.length) (hj' : j < cells.length),
      ps[j] = (loW Lnum Lden cells[j].1, hiW Lnum Lden cells[j].2) := by
    subst hpsdef
    intro j hj hj'
    rw [List.getElem_map]
  have hps : ∀ p ∈ ps, p.1 ≤ p.2 ∧ 0 < p.2 := by
    intro p hp
    rw [hpsdef] at hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    have h1 := loW_le_hiW (Lnum := Lnum) (Lden := Lden) (hcells c hc).1
    have h2 : 0 < loW Lnum Lden c.1 := (hcells c hc).2
    refine ⟨?_, ?_⟩
    · show loW Lnum Lden c.1 ≤ hiW Lnum Lden c.2
      exact h1
    · show 0 < hiW Lnum Lden c.2
      exact Nat.lt_of_lt_of_le h2 h1
  have hsl := sum_fst_le fun p hp => (hps p hp).1
  have hub : ∀ p ∈ ps, p.2 ≤ Nat.sub (sumN (ps.map fun p => p.2)) (sumN (ps.map fun p => p.1)) + p.1 := by
    intro p hp
    have h1 := width_le (fun p hp => (hps p hp).1) p hp
    show p.2 ≤ sumN (ps.map fun p => p.2) - sumN (ps.map fun p => p.1) + p.1
    omega
  have hvtH : ∀ v ∈ ps.map (fun p => mkTvH p.1 p.2), v.t = mkTm v.t.lo := by
    intro v hv
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
    rw [mkTvH_t, mkTm_lo]
  have hvtL : ∀ v ∈ ps.map (fun p => mkTv (Nat.sub (sumN (ps.map fun p => p.2)) (sumN (ps.map fun p => p.1))) p.1),
      v.t = mkTm v.t.lo := by
    intro v hv
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
    rw [mkTv_t, mkTm_lo]
  have gH := resTM3_sound hL hvtH (ltm_ok hLd) hTH
  have gL := resTM3_sound hL hvtL (ltm_ok hLd) hTL
  -- the variable at the upper corner
  generalize hsh : sumN (ps.map fun p => p.2) = sh at hneed gH gL hsl hub
  generalize hslv : sumN (ps.map fun p => p.1) = sl at hneed gH gL hsl hub
  have hmH : ((Nat.sub (Nat.div (Nat.mul Lnum S) Lden) (Nat.add (Nat.add (Nat.add sh W2) (Nat.div (Nat.sub sh sl) 11)) 2)
      : ℕ) : ℝ) + ((sh : ℝ) - sl) / 11 + sh + 2 / 10 ^ 5 * S ≤ (Lnum : ℝ) / Lden * S := by
    have e : ((Nat.sub (Nat.div (Nat.mul Lnum S) Lden)
        (Nat.add (Nat.add (Nat.add sh W2) (Nat.div (Nat.sub sh sl) 11)) 2) : ℕ) : ℝ) =
        ((Lnum * S / Lden : ℕ) : ℝ) - ((sh : ℝ) + W2 + (((sh - sl) / 11 : ℕ) : ℝ) + 2) := by
      show ((Lnum * S / Lden - (sh + W2 + (sh - sl) / 11 + 2) : ℕ) : ℝ) = _
      have hneed' : sh + W2 + (sh - sl) / 11 + 2 ≤ Lnum * S / Lden := hneed
      rw [Nat.cast_sub hneed']
      push_cast
      ring
    rw [e]
    have h1 := div_cast_le (Lnum * S) Lden
    push_cast at h1
    have e1 : (Lnum : ℝ) * S / Lden = (Lnum : ℝ) / Lden * S := by field_simp
    rw [e1] at h1
    have h2 := W2_ge
    have h3 : ((sh : ℝ) - sl) / 11 ≤ (((sh - sl) / 11 : ℕ) : ℝ) + 1 := by
      have h4 : sh - sl < 11 * ((sh - sl) / 11) + 11 := by omega
      have h5 : ((sh - sl : ℕ) : ℝ) < 11 * (((sh - sl) / 11 : ℕ) : ℝ) + 11 := by exact_mod_cast h4
      rw [Nat.cast_sub hsl] at h5
      linarith
    linarith
  intro m s hs hsum1 _
  have key := two_corner (L := (Lnum : ℝ) / Lden) (w := 2 / 10 ^ 5) (by norm_num) hps hub gH gL
    (by rw [hsh, hslv]; exact hmH) (m := m) (s := s)
    (fun j hj => by
      have hj' : j < cells.length := by rw [← hlen]; exact hj
      have h1 := hs j hj'
      simp only at h1
      rw [List.getD_eq_getElem _ _ hj'] at h1
      rw [hget j hj hj']
      have hc := hcells _ (List.getElem_mem hj')
      exact ⟨(loW_le hLd hc.2).trans h1.1, h1.2.trans (hiW_ge hLd)⟩)
    (by rw [hlen]; exact hsum1)
  rw [hlen] at key
  exact key

/-- The cells' upper ends, as exponents, sum to at most the sum of their fixed-point ends. -/
lemma sum_getD_le {Lnum Lden : ℕ} (hLd : 0 < Lden) : ∀ cells : List (ℕ × ℕ),
    ∑ j ∈ Finset.range cells.length, (Lnum : ℝ) / Lden / DEN * ((cells.getD j (0, 0)).2 : ℕ) ≤
      ((sumN ((cells.map fun c => (loW Lnum Lden c.1, hiW Lnum Lden c.2)).map fun p => p.2) : ℕ) : ℝ) / S
  | [] => by
    rw [List.length_nil, Finset.sum_range_zero]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  | x :: xs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.map_cons, sumN_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have h1 := sum_getD_le (Lnum := Lnum) hLd xs
    have h2 := hiW_ge (Lnum := Lnum) (Lden := Lden) (d := x.2) hLd
    push_cast
    rw [add_div]
    linarith

/-- **`resY` leaves the variable room**: the cells are in order, and their upper ends' exponents sum to at most
`L − 2·10⁻⁵`. -/
theorem resY_room {Lnum Lden : ℕ} (hLd : 0 < Lden) {cells : List (ℕ × ℕ)} {kH hH kL hL : ℕ}
    (hT : resY Lnum Lden cells kH hH kL hL = true) :
    (∀ c ∈ cells, c.1 ≤ c.2) ∧
      ∑ j ∈ Finset.range cells.length, (Lnum : ℝ) / Lden / DEN * ((cells.getD j (0, 0)).2 : ℕ) + 2 / 10 ^ 5 ≤
        (Lnum : ℝ) / Lden := by
  have hS := S_pos
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  unfold resY at hT
  dsimp only at hT
  simp only [Bool.and_eq_true, Nat.ble_eq] at hT
  obtain ⟨⟨⟨hok, hneed⟩, -⟩, -⟩ := hT
  refine ⟨fun c hc => (okY_mem hok c hc).1, ?_⟩
  have h0 := sum_getD_le (Lnum := Lnum) hLd cells
  generalize sumN ((cells.map fun c => (loW Lnum Lden c.1, hiW Lnum Lden c.2)).map fun p => p.2) = sh at hneed h0
  generalize sumN ((cells.map fun c => (loW Lnum Lden c.1, hiW Lnum Lden c.2)).map fun p => p.1) = sl at hneed
  have hneed' : sh + W2 + (sh - sl) / 11 + 2 ≤ Lnum * S / Lden := hneed
  have h1 : ((sh + W2 : ℕ) : ℝ) ≤ ((Lnum * S / Lden : ℕ) : ℝ) := by
    exact_mod_cast (by omega : sh + W2 ≤ Lnum * S / Lden)
  have h2 := div_cast_le (Lnum * S) Lden
  push_cast at h1 h2
  have e1 : (Lnum : ℝ) * S / Lden = (Lnum : ℝ) / Lden * S := by field_simp
  rw [e1] at h2
  have h3 := W2_ge
  have h4 : (sh : ℝ) / S + 2 / 10 ^ 5 ≤ (Lnum : ℝ) / Lden := by
    rw [div_add' _ _ _ hS.ne', div_le_iff₀ hS]
    linarith
  linarith

/-- `resYH` is `resY` at the hints that it unpacks. -/
theorem resYH_eq (Lnum Lden : ℕ) (cells : List (ℕ × ℕ)) (s : ℕ) :
    ∃ kH hH kL hL, resYH Lnum Lden cells s = resY Lnum Lden cells kH hH kL hL := ⟨_, _, _, _, rfl⟩

end SieveResTest

#print axioms SieveResTest.resTM3_sound
#print axioms SieveResTest.two_corner
#print axioms SieveResTest.resY_sound
#print axioms SieveResTest.resY_room
