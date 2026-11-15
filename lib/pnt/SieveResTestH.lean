/-
# The resonant window's test with the lines named by the hint is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTestHDefs.lean`'s `resXH` is `resX` (`SieveResTestDefs.lean`) with each interval's lines named by the hint in
place of those `resX` picks at the interval's midpoint, and the piece of an interval's end found by bisection. The
proofs of `resX`'s soundness hold for any choice of the lines and use of the piece only the bounds that the test
checks, so they are those of `SieveResTest.lean` and `SieveResLVTest.lean` with the choices read from the record:

* `intvH_sound`, `runIH_sound`, `resTMH_sound`, `resTH_sound`, `resTH_hs`: the test with the four lines.
* `intv2H_sound`, `runI2H_sound`, `resTM2H_sound`, `resT2H_sound`, `resT2H_hs`: the test with the large values'
  terms as two more choices.
* `resXH_sound`, `resXH_hs`, `resXH_sound_cells`: **the test in either form is sound**, in the cells' units, as
  `SieveResTest.resX_sound_cells`.

The file imports `SieveResLVTest.lean` and `SieveResTestHDefs.lean`.
-/
import SieveResLVTest
import SieveResTestHDefs

open Real Finset

noncomputable section

namespace SieveResTest

open SieveTypeIIHM SieveCurveHx

-- the unifier must not compute through the kernel's fixed-point definitions
attribute [local irreducible] lvVal lvG lvU

/-! ### The test with the four lines -/

lemma intvH_sound {L : ℝ} {los : List ℕ} {mlo c1 yuP yuN ydP ydN ltm a pa r : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (h : intvH (los.map mkTm) c1 yuP yuN ydP ydN ltm a pa r = true) (hpa : pa ≤ 17)
    (hlo : pa = 0 ∨ tops (pa - 1) * S < a) (hhi : pa ≤ 16 → (a : ℝ) ≤ tops pa * S) :
    pieceC (bOf r) ≤ 17 ∧ (pieceC (bOf r) = 0 ∨ tops (pieceC (bOf r) - 1) * S < bOf r) ∧
      (pieceC (bOf r) ≤ 16 → (bOf r : ℝ) ≤ tops (pieceC (bOf r)) * S) ∧ a ≤ bOf r ∧
      ∀ γ, (a : ℝ) / S ≤ γ → γ ≤ (bOf r : ℝ) / S → GoalAt L los mlo γ := by
  have hS := S_pos
  unfold intvH at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h17, hlt⟩, hle⟩, hab⟩, hchk⟩ := h
  generalize hbdef : bOf r = b at h17 hlt hle hab hchk ⊢
  generalize hpbdef : pieceC b = pb at h17 hlt hle hchk ⊢
  -- the lines that the hint names: any choice is a bound
  generalize hccdef : Nat.land (Nat.shiftRight r 13) 3 = cc at hchk
  generalize hchdef : Nat.shiftRight r 15 = ch at hchk
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
  refine ⟨h17, hblo, hbhi, hab, ?_⟩
  intro γ hγa hγb β m s t h1 h2 hγ ht hk hm hs hsum
  -- the ends in the reals
  have hlo' : pa = 0 ∨ tops (pa - 1) < a / S := by
    rcases hlo with h0 | h0
    · exact Or.inl h0
    · right; rw [lt_div_iff₀ hS]; exact h0
  have hhi' : pa ≤ 16 → (a : ℝ) / S ≤ tops pa := fun h16 => by rw [div_le_iff₀ hS]; exact hhi h16
  have hbhi' : pb ≤ 16 → (b : ℝ) / S ≤ tops pb := fun h16 => by rw [div_le_iff₀ hS]; exact hbhi h16
  have hab' : (a : ℝ) / S ≤ b / S := div_le_div_of_nonneg_right (by exact_mod_cast hab) hS.le
  have hγ0 : 0 ≤ γ := le_trans (div_nonneg (Nat.cast_nonneg _) hS.le) hγa
  have hC := line_C hpa hlo' hhi' hγa h1 h2 hγ
  have hW := line_W hpa hlo' hbhi' hab' h17 hγa hγb hγ0 h1 h2 hγ
  -- the terms
  generalize hdS : maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC) = dS at hC hchk
  generalize hiax : minN (get tIA pa) (get tIA pb) = iax at hW hchk
  have hv : ∀ i (hi : i < (los.map mkTm).length), ∀ c,
      s i * (t i - 1) - s i * (1 / 10 ^ 6) ≤ tline (los.map mkTm)[i] dS iax c γ := by
    intro i hi c
    rw [List.length_map] at hi
    rw [List.getElem_map]
    exact term_le los[i] dS iax c (hs i hi) (ht i hi) h2 hγ0 (hk i hi) hC hW
  generalize hcl : clampL c1 yuP yuN ydP ydN a b cc = cl at hchk
  have hclb := clampL_sound hok a b cc hm hγa hγb
  rw [hcl] at hclb
  have hT := addTerms_sound dS iax γ (los.map mkTm) ch (Nat.add ltm cl.1) cl.2.2 0
    (fun j => s j * (t j - 1) - s j * (1 / 10 ^ 6)) hv
  -- the check at the ends
  rw [chkI_eq] at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨hca, hcb⟩ := hchk
  have lγ := lv_interval (le0_sound hca) (le0_sound hcb) hγa hγb
  unfold lv at lγ
  rw [List.length_map] at hT
  simp only [Nat.add_eq] at lγ hT
  push_cast at lγ hT
  rw [H_real] at lγ
  rw [div_nonpos_iff] at lγ
  rcases lγ with ⟨_, hneg⟩ | ⟨lγ, _⟩
  · exact absurd hneg (not_le.mpr hS)
  have hT' : (∑ j ∈ range los.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6))) * S +
      ((ltm : ℝ) + cl.1 - cl.2.2 - 0 * γ) ≤
      (addTerms dS iax (List.map mkTm los) ch (ltm + cl.1) cl.2.2 0).1 -
        (addTerms dS iax (List.map mkTm los) ch (ltm + cl.1) cl.2.2 0).2.1 -
        (addTerms dS iax (List.map mkTm los) ch (ltm + cl.1) cl.2.2 0).2.2 * γ := by
    have h := mul_le_mul_of_nonneg_right hT hS.le
    rw [add_mul, div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at h
    exact h
  have hX : ∑ j ∈ range los.length, s j * (t j - 1) =
      ∑ j ∈ range los.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6)) +
        1 / 10 ^ 6 * ∑ j ∈ range los.length, s j := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_comm (1 / 10 ^ 6 : ℝ)]
    ring
  exact goal_of_lines hS hX hsum (by rwa [le_div_iff₀ hS] at hltm) hT' lγ hclb

/-! ### Its intervals and the test -/

lemma runIH_zero (ts : List Tm) (w c1 yuP yuN ydP ydN ltm a pa h : ℕ) :
    runIH ts w c1 yuP yuN ydP ydN ltm 0 a pa h = Nat.beq a S := rfl

lemma runIH_succ (ts : List Tm) (w c1 yuP yuN ydP ydN ltm k a pa h : ℕ) :
    runIH ts w c1 yuP yuN ydP ydN ltm (k + 1) a pa h =
      (intvH ts c1 yuP yuN ydP ydN ltm a pa (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) &&
        runIH ts w c1 yuP yuN ydP ydN ltm k (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))
          (pieceC (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))) (Nat.shiftRight h w)) := rfl

/-- **The intervals are sound**: `runIH` from `a` in the piece `pa` gives the bound at every `γ ∈ (a/S, 1]`. -/
lemma runIH_sound {L : ℝ} {los : List ℕ} {mlo c1 yuP yuN ydP ydN ltm w : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) :
    ∀ (k a pa h : ℕ), runIH (los.map mkTm) w c1 yuP yuN ydP ydN ltm k a pa h = true → pa ≤ 17 →
      (pa = 0 ∨ tops (pa - 1) * S < a) → (pa ≤ 16 → (a : ℝ) ≤ tops pa * S) →
      ∀ γ, (a : ℝ) / S < γ → γ ≤ 1 → GoalAt L los mlo γ
  | 0, a, pa, h, hr, _, _, _, γ, hγa, hγ1 => by
    rw [runIH_zero] at hr
    have ha : a = S := Nat.eq_of_beq_eq_true hr
    subst ha
    rw [div_self S_pos.ne'] at hγa
    linarith
  | k + 1, a, pa, h, hr, hpa, hlo, hhi, γ, hγa, hγ1 => by
    rw [runIH_succ] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hi, hr⟩ := hr
    obtain ⟨h17, hblo, hbhi, hab, hgoal⟩ := intvH_sound hok hltm hi hpa hlo hhi
    rcases le_or_gt γ ((bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) : ℕ) / S) with hγb | hγb
    · exact hgoal γ hγa.le hγb
    · exact runIH_sound hok hltm k _ _ _ hr h17 hblo hbhi γ hγb hγ1

/-- **The test with the lines named by the hint, `m` and `Lτ + MARG` given, is sound**: the bound at every
`γ`. -/
theorem resTMH_sound {L : ℝ} (hL : 0 ≤ L) {los : List ℕ} {mlo ltm k h : ℕ}
    (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) (hT : resTMH (los.map mkTm) mlo ltm k h = true) :
    ∀ γ, GoalAt L los mlo γ := by
  have hS := S_pos
  unfold resTMH at hT
  simp only [shrN, Nat.add_eq, Nat.sub_eq, Bool.and_eq_true, Nat.ble_eq, minN_eq] at hT
  obtain ⟨hhp, hrun⟩ := hT
  have hok := clampOK_of' mlo
  intro γ β m s t h1 h2 hγ ht hk hm hs hsum
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · -- the half-plane
    have hX := hpSum_le h2 los s t ht hs
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
        (hpSum (los.map mkTm) : ℕ) := by exact_mod_cast hhp
    have hltm' : (L * (1 / 10 ^ 6) + 1 / 25000) * S ≤ ltm := by rwa [le_div_iff₀ hS] at hltm
    have key : (∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000) * S ≤ 0 := by
      have hXS : (∑ j ∈ range los.length, s j * (t j - 1)) * S ≤ -((hpSum (los.map mkTm) : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hX hS.le
        rwa [div_mul_cancel₀ _ hS.ne'] at this
      have hcS : clampR γ m * S ≤ clampR 0 ((mlo : ℝ) / S) * S :=
        mul_le_mul_of_nonneg_right (hc1.trans hc2) hS.le
      have hγS : γ / 2 * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
      have hLS : 0 ≤ L * (1 / 10 ^ 6) * S := by positivity
      nlinarith
    by_contra hcon
    have := mul_pos (show 0 < ∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000 by
      linarith) hS
    linarith
  · -- the intervals
    have hγ1 : γ ≤ 1 := hγ.trans (ghx_le_one β)
    exact runIH_sound hok hltm k 0 0 h hrun (by norm_num) (Or.inl rfl)
      (fun _ => by rw [Nat.cast_zero]; exact mul_nonneg (tops_pos 0 (by norm_num)).le hS.le) γ
      (by rw [Nat.cast_zero, zero_div]; exact hγ0) hγ1 β m s t h1 h2 hγ ht hk hm hs hsum

/-- **The test with the lines named by the hint is sound**: `resTH` gives `ResBox ghx L K m lo` at `L = Lnum/Lden` with
the fixed point's `m = ⌊L(DEN − hs − 1)S/DEN⌋/S` and `lo_j = ⌊L(c_j − 1)S/DEN⌋/S`. -/
theorem resTH_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resTH Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  unfold resTH at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨_, hT⟩ := hT
  have hmap : (cs.map fun c => mkTm (loOf Lnum Lden c)) = (cs.map (loOf Lnum Lden)).map mkTm := by
    rw [List.map_map]
    rfl
  rw [hmap] at hT
  have hL : (0 : ℝ) ≤ (Lnum : ℝ) / Lden := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hgoal := resTMH_sound hL (ltm_ok hLd) hT
  intro m s hm hs hsum _ β γ t h1 h2 hγ ht hk _
  have hlen : (cs.map (loOf Lnum Lden)).length = cs.length := List.length_map _
  have hg := hgoal γ β m s t h1 h2 hγ (by rw [hlen]; exact ht) (by rw [hlen]; exact hk) hm
    (fun j hj => by
      rw [List.getElem_map]
      have hj' : j < cs.length := by rw [hlen] at hj; exact hj
      have := hs j hj'
      simp only at this
      rw [List.getD_eq_getElem _ _ hj'] at this
      exact this) (by rw [hlen]; exact hsum)
  rw [hlen] at hg
  exact binOK_of hg

/-- `resTH` passes only with `hs + 1 < DEN`. -/
theorem resTH_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resTH Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  unfold resTH at hT
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hT
  exact hT.1

/-! ### The test with the large values' terms -/

lemma intv2H_sound {L : ℝ} {los : List ℕ} {mlo ub c1 yuP yuN ydP ydN ltm a pa r : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (h : intv2H (los.map (mkTv ub)) c1 yuP yuN ydP ydN ltm a pa r = true) (hpa : pa ≤ 17)
    (hlo : pa = 0 ∨ tops (pa - 1) * S < a) (hhi : pa ≤ 16 → (a : ℝ) ≤ tops pa * S) :
    pieceC (bOf r) ≤ 17 ∧ (pieceC (bOf r) = 0 ∨ tops (pieceC (bOf r) - 1) * S < bOf r) ∧
      (pieceC (bOf r) ≤ 16 → (bOf r : ℝ) ≤ tops (pieceC (bOf r)) * S) ∧ a ≤ bOf r ∧
      ∀ γ, (a : ℝ) / S ≤ γ → γ ≤ (bOf r : ℝ) / S → GoalAt2 L los mlo ub γ := by
  have hS := S_pos
  unfold intv2H at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h17, hlt⟩, hle⟩, hab⟩, hchk⟩ := h
  generalize hbdef : bOf r = b at h17 hlt hle hab hchk ⊢
  generalize hpbdef : pieceC b = pb at h17 hlt hle hchk ⊢
  -- the bounds that the hint names: any choice is a bound
  generalize hccdef : Nat.land (Nat.shiftRight r 13) 3 = cc at hchk
  generalize hchdef : Nat.shiftRight r 15 = ch at hchk
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
  intro γ hγa hγb β m s t h1 h2 hγ ht hk hlv hm hs hup hsum
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
  have hv : ∀ i (hi : i < (los.map (mkTv ub)).length), ∀ c,
      s i * (t i - 1) - s i * (1 / 10 ^ 6) ≤ tline2 (los.map (mkTv ub))[i] dS iax a b c lam γ := by
    intro i hi c
    rw [List.length_map] at hi
    rw [List.getElem_map]
    rcases Nat.lt_or_ge c 4 with hc3 | hc4
    · rw [tline2_le3 _ _ _ _ _ (by omega), mkTv_t]
      exact term_le los[i] dS iax c (hs i hi) (ht i hi) h2 hγ0 (hk i hi) hC hW
    · rcases Nat.eq_or_lt_of_le hc4 with hc | hc
      · rw [← hc, tline2_4, mkTv_t, mkTm_lo, mkTv_k1, mkTv_g1]
        exact lvU_le hab hbS (hs i hi) (hup i hi) (ht i hi) h2 hlam0 hlam1 hγlam (hlv i hi)
      · rw [tline2_ge5 _ _ _ _ _ (by omega), mkTv_t, mkTm_lo, mkTv_k2, mkTv_g2]
        exact lvU_le hab hbS (hs i hi) (hup i hi) (ht i hi) h2 hlam0 hlam1 hγlam (hlv i hi)
  generalize hcl : clampL c1 yuP yuN ydP ydN a b cc = cl at hchk
  have hclb := clampL_sound hok a b cc hm hγa hγb
  rw [hcl] at hclb
  have hT := addTerms2_sound dS iax a b lam γ (los.map (mkTv ub)) ch (Nat.add ltm cl.1) cl.2.2 0 0 0
    (fun j => s j * (t j - 1) - s j * (1 / 10 ^ 6)) hv
  -- the check at the ends
  unfold chkI2 at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨hca, hcb⟩ := hchk
  have la := le0_sound hca
  have lb := le0_sound hcb
  generalize hR : addTerms2 dS iax a b (los.map (mkTv ub)) ch (Nat.add ltm cl.1) cl.2.2 0 0 0 = R at hT la lb
  unfold lv at la lb
  rw [List.length_map] at hT
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
  have hT' : (∑ j ∈ range los.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6))) * S +
      ((ltm : ℝ) + cl.1 - cl.2.2 - 0 * γ) ≤
      (R.1 : ℝ) + ((1 - lam) * R.2.2.2.1 + lam * R.2.2.2.2) - R.2.1 - R.2.2.1 * γ := by
    have h := mul_le_mul_of_nonneg_right hT hS.le
    rw [add_mul, div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at h
    linarith
  have hX : ∑ j ∈ range los.length, s j * (t j - 1) =
      ∑ j ∈ range los.length, (s j * (t j - 1) - s j * (1 / 10 ^ 6)) +
        1 / 10 ^ 6 * ∑ j ∈ range los.length, s j := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_comm (1 / 10 ^ 6 : ℝ)]
    ring
  exact goal_of_lines hS hX hsum (by rwa [le_div_iff₀ hS] at hltm) hT' lγ hclb

lemma runI2H_zero (vs : List Tv) (w c1 yuP yuN ydP ydN ltm a pa h : ℕ) :
    runI2H vs w c1 yuP yuN ydP ydN ltm 0 a pa h = Nat.beq a S := rfl

lemma runI2H_succ (vs : List Tv) (w c1 yuP yuN ydP ydN ltm k a pa h : ℕ) :
    runI2H vs w c1 yuP yuN ydP ydN ltm (k + 1) a pa h =
      (intv2H vs c1 yuP yuN ydP ydN ltm a pa (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) &&
        runI2H vs w c1 yuP yuN ydP ydN ltm k (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))
          (pieceC (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))) (Nat.shiftRight h w)) := rfl

/-- **The intervals are sound**: `runI2H` from `a` in the piece `pa` gives the bound at every `γ ∈ (a/S, 1]`. -/
lemma runI2H_sound {L : ℝ} {los : List ℕ} {mlo ub c1 yuP yuN ydP ydN ltm w : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) :
    ∀ (k a pa h : ℕ), runI2H (los.map (mkTv ub)) w c1 yuP yuN ydP ydN ltm k a pa h = true → pa ≤ 17 →
      (pa = 0 ∨ tops (pa - 1) * S < a) → (pa ≤ 16 → (a : ℝ) ≤ tops pa * S) →
      ∀ γ, (a : ℝ) / S < γ → γ ≤ 1 → GoalAt2 L los mlo ub γ
  | 0, a, pa, h, hr, _, _, _, γ, hγa, hγ1 => by
    rw [runI2H_zero] at hr
    have ha : a = S := Nat.eq_of_beq_eq_true hr
    subst ha
    rw [div_self S_pos.ne'] at hγa
    linarith
  | k + 1, a, pa, h, hr, hpa, hlo, hhi, γ, hγa, hγ1 => by
    rw [runI2H_succ] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hi, hr⟩ := hr
    obtain ⟨h17, hblo, hbhi, hab, hgoal⟩ := intv2H_sound hok hltm hi hpa hlo hhi
    rcases le_or_gt γ ((bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) : ℕ) / S) with hγb | hγb
    · exact hgoal γ hγa.le hγb
    · exact runI2H_sound hok hltm k _ _ _ hr h17 hblo hbhi γ hγb hγ1

/-- **The test with the large values' terms and the lines named by the hint, `m` and `Lτ + MARG` given, is
sound**: the bound at every `γ`. -/
theorem resTM2H_sound {L : ℝ} (hL : 0 ≤ L) {los : List ℕ} {mlo ub ltm k h : ℕ}
    (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (hT : resTM2H (los.map (mkTv ub)) mlo ltm k h = true) : ∀ γ, GoalAt2 L los mlo ub γ := by
  have hS := S_pos
  unfold resTM2H at hT
  simp only [shrN, Nat.add_eq, Nat.sub_eq, Bool.and_eq_true, Nat.ble_eq, minN_eq] at hT
  obtain ⟨hhp, hrun⟩ := hT
  rw [hpSum2_eq] at hhp
  have hok := clampOK_of' mlo
  intro γ β m s t h1 h2 hγ ht hk hlv hm hs hup hsum
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · -- the half-plane
    have hX := hpSum_le h2 los s t ht hs
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
        (hpSum (los.map mkTm) : ℕ) := by exact_mod_cast hhp
    have hltm' : (L * (1 / 10 ^ 6) + 1 / 25000) * S ≤ ltm := by rwa [le_div_iff₀ hS] at hltm
    have key : (∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000) * S ≤ 0 := by
      have hXS : (∑ j ∈ range los.length, s j * (t j - 1)) * S ≤ -((hpSum (los.map mkTm) : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hX hS.le
        rwa [div_mul_cancel₀ _ hS.ne'] at this
      have hcS : clampR γ m * S ≤ clampR 0 ((mlo : ℝ) / S) * S :=
        mul_le_mul_of_nonneg_right (hc1.trans hc2) hS.le
      have hγS : γ / 2 * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
      have hLS : 0 ≤ L * (1 / 10 ^ 6) * S := by positivity
      nlinarith
    by_contra hcon
    have := mul_pos (show 0 < ∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m + 1 / 25000 by
      linarith) hS
    linarith
  · -- the intervals
    have hγ1 : γ ≤ 1 := hγ.trans (ghx_le_one β)
    exact runI2H_sound hok hltm k 0 0 h hrun (by norm_num) (Or.inl rfl)
      (fun _ => by rw [Nat.cast_zero]; exact mul_nonneg (tops_pos 0 (by norm_num)).le hS.le) γ
      (by rw [Nat.cast_zero, zero_div]; exact hγ0) hγ1 β m s t h1 h2 hγ ht hk hlv hm hs hup hsum


/-- **The test with the large values' terms and the lines named by the hint is sound**: `resT2H` gives
`ResBox ghx L K m lo` at `L = Lnum/Lden`, with `resTH_sound`'s `m` and `lo_j`. -/
theorem resT2H_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resT2H Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  unfold resT2H at hT
  dsimp only at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨_, hT⟩ := hT
  have hL : (0 : ℝ) ≤ (Lnum : ℝ) / Lden := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hgoal := resTM2H_sound hL (ltm_ok hLd) hT
  intro m s hm hs' hsum hsum2 β γ t h1 h2 hγ ht hk hlv
  have hlen : (cs.map (loOf Lnum Lden)).length = cs.length := List.length_map _
  have hs'' : ∀ j (hj : j < (cs.map (loOf Lnum Lden)).length),
      (((cs.map (loOf Lnum Lden))[j] : ℕ) : ℝ) / S ≤ s j := fun j hj => by
    rw [List.getElem_map]
    have hj' : j < cs.length := by rw [hlen] at hj; exact hj
    have := hs' j hj'
    simp only at this
    rw [List.getD_eq_getElem _ _ hj'] at this
    exact this
  have hup := upper_end (ls5_ok hLd) hm hs'' (by rw [hlen]; exact hsum2)
  have hg := hgoal γ β m s t h1 h2 hγ (by rw [hlen]; exact ht) (by rw [hlen]; exact hk) (by rw [hlen]; exact hlv)
    hm hs'' hup (by rw [hlen]; exact hsum)
  rw [hlen] at hg
  exact binOK_of hg

/-- `resT2H` passes only with `hs + 1 < DEN`. -/
theorem resT2H_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resT2H Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  unfold resT2H at hT
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hT
  exact hT.1

/-! ### Either form -/

/-- `resXH` is `resT2H` at `k = 0` and `resTH` elsewhere. -/
lemma resXH_cases {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resXH Lnum Lden cs hs k h = true) :
    resT2H Lnum Lden cs hs (Nat.land h 15) (Nat.shiftRight h 4) = true ∨ resTH Lnum Lden cs hs k h = true := by
  unfold resXH at hT
  cases hk : Nat.beq k 0 with
  | true =>
    rw [hk, Bool.cond_true] at hT
    exact Or.inl hT
  | false =>
    rw [hk, Bool.cond_false] at hT
    exact Or.inr hT

/-- **The test in either form is sound**: `resXH` gives `ResBox ghx L K m lo`, as `resTH_sound`. -/
theorem resXH_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resXH Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  rcases resXH_cases hT with h2 | h1
  · exact resT2H_sound hLd h2
  · exact resTH_sound hLd h1

/-- `resXH` passes only with `hs + 1 < DEN`. -/
theorem resXH_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resXH Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  rcases resXH_cases hT with h2 | h1
  · exact resT2H_hs h2
  · exact resTH_hs h1

/-- **The test with the lines named by the hint, in either form, is sound, in the cells' units**: with `κ = L/DEN`,
`L = Lnum/Lden`, cells `c_j ≥ 1` and `hs + 1 < DEN`, `resXH` gives `ResBox ghx L K (L − κ·hs − κ) (κ·c_j − κ)`. -/
theorem resXH_sound_cells {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hc : ∀ c ∈ cs, 1 ≤ c) (hT : resXH Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      ((Lnum : ℝ) / Lden - (Lnum : ℝ) / Lden / DEN * hs - (Lnum : ℝ) / Lden / DEN)
      (fun j => (Lnum : ℝ) / Lden / DEN * (cs.getD j 0) - (Lnum : ℝ) / Lden / DEN) := by
  have hS := S_pos
  have hD : (0 : ℝ) < DEN := by norm_num [DEN]
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have hhs : hs + 1 < DEN := resXH_hs hT
  refine resBox_mono (resXH_sound hLd hT) ?_ ?_
  · -- `⌊Lnum(DEN − hs − 1)S/(Lden·DEN)⌋/S ≤ κ(DEN − hs − 1)`
    have h1 := div_cast_le (Lnum * (DEN - hs - 1) * S) (Lden * DEN)
    have e : ((DEN - hs - 1 : ℕ) : ℝ) = DEN - hs - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    push_cast at h1
    rw [e] at h1
    rw [div_le_iff₀ hS]
    calc _ ≤ (Lnum : ℝ) * (DEN - hs - 1) * S / (Lden * DEN) := h1
      _ = ((Lnum : ℝ) / Lden - (Lnum : ℝ) / Lden / DEN * hs - (Lnum : ℝ) / Lden / DEN) * S := by
        field_simp
  · intro j hj
    have hcj : 1 ≤ cs.getD j 0 := by
      rw [List.getD_eq_getElem _ _ hj]
      exact hc _ (List.getElem_mem hj)
    have h1 := div_cast_le (Lnum * (cs.getD j 0 - 1) * S) (Lden * DEN)
    have e : ((cs.getD j 0 - 1 : ℕ) : ℝ) = (cs.getD j 0 : ℝ) - 1 := by
      rw [Nat.cast_sub hcj, Nat.cast_one]
    push_cast at h1
    rw [e] at h1
    show ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S ≤ _
    have e2 : loOf Lnum Lden (cs.getD j 0) = Lnum * (cs.getD j 0 - 1) * S / (Lden * DEN) := rfl
    rw [e2, div_le_iff₀ hS]
    calc _ ≤ (Lnum : ℝ) * ((cs.getD j 0 : ℝ) - 1) * S / (Lden * DEN) := h1
      _ = ((Lnum : ℝ) / Lden / DEN * (cs.getD j 0) - (Lnum : ℝ) / Lden / DEN) * S := by
        field_simp

end SieveResTest

end
