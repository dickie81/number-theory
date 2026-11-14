/-
# The resonant window's test on a box is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTestDefs.lean`'s `resT` checks the condition `SieveTypeIIHM.ResBox` of a box's rest on the curve
`SieveCurveHx.ghx`, led by a hint. This file proves it sound (`resT_sound`).

* The curve's steps from the top: `pLo`, `pHi`, `pA` and `tops p = A(1 − lo)`, the largest count exponent of the step
  `p`; `ghx_piece`: a zero's real part `β ∈ [1/2, 11/12]` with count exponent `γ ≤ ghx β` is below `7789/10000` or
  in a step `p` with `γ ≤ A_p(1 − β)`. `bmax_C`, `bmax_W`: the bounds of `β` that the test's lines `C` and `W` use.
* The tables: `ftN`, `iaN`, `dhN` and the kernel's packed `tFT`, `tFTm`, `tIA`, `tDH`.

The file imports `SieveResTestDefs.lean`, `SieveResFull.lean` (for `ResBox`) and `SieveCurveHx.lean` (for `ghx`).
-/
import SieveResTestDefs
import SieveResFull
import SieveCurveHx

open Real Finset

noncomputable section

namespace SieveResTest

open SieveTypeIIHM SieveCurveHx

/-! ### The curve's steps -/

/-- The lower end of the step `p` of `ghx`, from the top. -/
def pLo : ℕ → ℝ
  | 0 => 5/6
  | 1 => 697/840
  | 2 => 347/420
  | 3 => 691/840
  | 4 => 86/105
  | 5 => 137/168
  | 6 => 341/420
  | 7 => 97/120
  | 8 => 169/210
  | 9 => 673/840
  | 10 => 67/84
  | 11 => 667/840
  | 12 => 83/105
  | 13 => 661/840
  | 14 => 47/60
  | 15 => 131/168
  | 16 => 7789/10000
  | _ => 1 / 2

/-- The upper end of the step `p` (`11/12` for the top step; `7789/10000` for the trivial count, `p = 17`). -/
def pHi : ℕ → ℝ
  | 0 => 11/12
  | 1 => 5/6
  | 2 => 697/840
  | 3 => 347/420
  | 4 => 691/840
  | 5 => 86/105
  | 6 => 137/168
  | 7 => 341/420
  | 8 => 97/120
  | 9 => 169/210
  | 10 => 673/840
  | 11 => 67/84
  | 12 => 667/840
  | 13 => 83/105
  | 14 => 661/840
  | 15 => 47/60
  | 16 => 131/168
  | _ => 7789 / 10000

/-- The exponent's factor `A` of the step `p`. -/
def pA : ℕ → ℝ
  | 0 => 101/50
  | 1 => 560139/278000
  | 2 => 280069/138000
  | 3 => 560137/274000
  | 4 => 70017/34000
  | 5 => 112027/54000
  | 6 => 280067/134000
  | 7 => 80019/38000
  | 8 => 140033/66000
  | 9 => 560131/262000
  | 10 => 56013/26000
  | 11 => 560129/258000
  | 12 => 547/250
  | 13 => 560127/254000
  | 14 => 40009/18000
  | 15 => 4481/2000
  | 16 => 7014/3125
  | _ => 1

/-- `⌊tops p · S⌋` by step; `S` from `17` on. -/
def ftN : ℕ → ℕ
  | 0 => 6210403838148882377
  | 1 => 6327432045883067909
  | 2 => 6506976623818538820
  | 3 => 6689141809598112703
  | 4 => 6873985410747762418
  | 5 => 7061566947609045205
  | 6 => 7251947717250131954
  | 7 => 7445190860260040799
  | 8 => 7641361430578972243
  | 9 => 7840526468526980238
  | 10 => 8042755077203197321
  | 11 => 8248118502438512073
  | 12 => 8456690216496028348
  | 13 => 8668546005725876889
  | 14 => 8883764062394065609
  | 15 => 9102425080919114670
  | 16 => 9154280273435530746
  | _ => 18446744073709551616

/-- `⌊S/A⌋` by step; `0` from `17` on. -/
def iaN : ℕ → ℕ
  | 0 => 9132051521638391889
  | 1 => 9155218352036289830
  | 2 => 9089369698795361582
  | 3 => 9023520810438191268
  | 4 => 8957671686963519644
  | 5 => 8891822328370087454
  | 6 => 8825972734656635435
  | 7 => 8760122905821904315
  | 8 => 8694272841864634812
  | 9 => 8628422542783567635
  | 10 => 8562572008577443486
  | 11 => 8496721239245003056
  | 12 => 8430870234784987027
  | 13 => 8365018995196136073
  | 14 => 8299167520477190859
  | 15 => 8233315810626892040
  | 16 => 8218716171990639977
  | _ => 0

/-- `⌊(1 − w − hi)·S⌋` by step; with `hi = 7789/10000` from `17` on. -/
def dhN : ℕ → ℕ
  | 0 => 1537154885832834463
  | 1 => 3074383558641963764
  | 2 => 3140264787476640734
  | 3 => 3206146016311317704
  | 4 => 3272027245145994674
  | 5 => 3337908473980671644
  | 6 => 3403789702815348614
  | 7 => 3469670931650025584
  | 8 => 3535552160484702554
  | 9 => 3601433389319379524
  | 10 => 3667314618154056494
  | 11 => 3733195846988733465
  | 12 => 3799077075823410435
  | 13 => 3864958304658087405
  | 14 => 3930839533492764375
  | 15 => 3996720762327441345
  | 16 => 4062601991162118315
  | _ => 4078501327720887024

/-- The largest count exponent of the step `p`: `A(1 − lo)`. -/
def tops (p : ℕ) : ℝ := pA p * (1 - pLo p)

/-- **The step of a zero**: for `β ∈ [1/2, 11/12]` with count exponent `γ ≤ ghx β`, `β < 7789/10000` or `β` is in a
step `p ≤ 16` with `γ ≤ A_p(1 − β)`. -/
lemma ghx_piece {β γ : ℝ} (h1 : 1 / 2 ≤ β) (h2 : β ≤ 11 / 12) (hγ : γ ≤ ghx β) :
    β < 7789 / 10000 ∨ ∃ p ≤ 16, pLo p ≤ β ∧ β ≤ pHi p ∧ γ ≤ pA p * (1 - β) := by
  unfold ghx at hγ
  by_cases h0 : β < 7789 / 10000
  · exact Or.inl h0
  rw [ite_eq_right h0] at hγ
  by_cases h1 : β < 131 / 168
  · rw [ite_eq_left h1] at hγ
    exact Or.inr ⟨16, by norm_num, by simp only [pLo]; linarith [not_lt.mp h0], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h1] at hγ
  by_cases h2 : β < 47 / 60
  · rw [ite_eq_left h2] at hγ
    exact Or.inr ⟨15, by norm_num, by simp only [pLo]; linarith [not_lt.mp h1], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h2] at hγ
  by_cases h3 : β < 661 / 840
  · rw [ite_eq_left h3] at hγ
    exact Or.inr ⟨14, by norm_num, by simp only [pLo]; linarith [not_lt.mp h2], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h3] at hγ
  by_cases h4 : β < 83 / 105
  · rw [ite_eq_left h4] at hγ
    exact Or.inr ⟨13, by norm_num, by simp only [pLo]; linarith [not_lt.mp h3], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h4] at hγ
  by_cases h5 : β < 667 / 840
  · rw [ite_eq_left h5] at hγ
    exact Or.inr ⟨12, by norm_num, by simp only [pLo]; linarith [not_lt.mp h4], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h5] at hγ
  by_cases h6 : β < 67 / 84
  · rw [ite_eq_left h6] at hγ
    exact Or.inr ⟨11, by norm_num, by simp only [pLo]; linarith [not_lt.mp h5], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h6] at hγ
  by_cases h7 : β < 673 / 840
  · rw [ite_eq_left h7] at hγ
    exact Or.inr ⟨10, by norm_num, by simp only [pLo]; linarith [not_lt.mp h6], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h7] at hγ
  by_cases h8 : β < 169 / 210
  · rw [ite_eq_left h8] at hγ
    exact Or.inr ⟨9, by norm_num, by simp only [pLo]; linarith [not_lt.mp h7], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h8] at hγ
  by_cases h9 : β < 97 / 120
  · rw [ite_eq_left h9] at hγ
    exact Or.inr ⟨8, by norm_num, by simp only [pLo]; linarith [not_lt.mp h8], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h9] at hγ
  by_cases h10 : β < 341 / 420
  · rw [ite_eq_left h10] at hγ
    exact Or.inr ⟨7, by norm_num, by simp only [pLo]; linarith [not_lt.mp h9], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h10] at hγ
  by_cases h11 : β < 137 / 168
  · rw [ite_eq_left h11] at hγ
    exact Or.inr ⟨6, by norm_num, by simp only [pLo]; linarith [not_lt.mp h10], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h11] at hγ
  by_cases h12 : β < 86 / 105
  · rw [ite_eq_left h12] at hγ
    exact Or.inr ⟨5, by norm_num, by simp only [pLo]; linarith [not_lt.mp h11], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h12] at hγ
  by_cases h13 : β < 691 / 840
  · rw [ite_eq_left h13] at hγ
    exact Or.inr ⟨4, by norm_num, by simp only [pLo]; linarith [not_lt.mp h12], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h13] at hγ
  by_cases h14 : β < 347 / 420
  · rw [ite_eq_left h14] at hγ
    exact Or.inr ⟨3, by norm_num, by simp only [pLo]; linarith [not_lt.mp h13], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h14] at hγ
  by_cases h15 : β < 697 / 840
  · rw [ite_eq_left h15] at hγ
    exact Or.inr ⟨2, by norm_num, by simp only [pLo]; linarith [not_lt.mp h14], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h15] at hγ
  by_cases h16 : β < 5 / 6
  · rw [ite_eq_left h16] at hγ
    exact Or.inr ⟨1, by norm_num, by simp only [pLo]; linarith [not_lt.mp h15], by simp only [pHi]; linarith,
      by simpa only [pA] using hγ⟩
  rw [ite_eq_right h16] at hγ
  exact Or.inr ⟨0, by norm_num, by simp only [pLo]; linarith [not_lt.mp h16], by simp only [pHi]; linarith,
    by simpa only [pA] using hγ⟩

lemma tops_succ : ∀ p < 16, tops p ≤ tops (p + 1) := by
  intro p hp
  interval_cases p <;> norm_num [tops, pA, pLo]

lemma tops_mono {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ 16) : tops p ≤ tops q := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_refl _
  | succ n hpn ih => exact (ih (by omega)).trans (tops_succ n (by omega))

lemma pLo_succ : ∀ p < 16, pLo (p + 1) ≤ pLo p := by
  intro p hp
  interval_cases p <;> norm_num [pLo]

lemma pHi_succ : ∀ p < 16, pHi (p + 1) = pLo p := by
  intro p hp
  interval_cases p <;> norm_num [pLo, pHi]

lemma pLo_anti {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ 16) : pLo q ≤ pLo p := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_refl _
  | succ n hpn ih => exact (pLo_succ n (by omega)).trans (ih (by omega))

/-- The steps below `p` end below its lower end. -/
lemma pHi_le_pLo {p q : ℕ} (hpq : p < q) (hq : q ≤ 16) : pHi q ≤ pLo p := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  rw [pHi_succ n (by omega)]
  exact pLo_anti (by omega) (by omega)

lemma pA_succ : ∀ p, 1 ≤ p → p < 16 → pA p ≤ pA (p + 1) := by
  intro p hp1 hp
  interval_cases p <;> norm_num [pA]

lemma pA_mono {p q : ℕ} (h1 : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 16) : pA p ≤ pA q := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_refl _
  | succ n hpn ih => exact (ih (by omega)).trans (pA_succ n (by omega) (by omega))

/-- The steps' `A` fall then rise, so on a range of steps it is largest at an end. -/
lemma pA_le_max {pa q pb : ℕ} (h1 : pa ≤ q) (h2 : q ≤ pb) (h3 : pb ≤ 16) : pA q ≤ max (pA pa) (pA pb) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have : pa = 0 := by omega
    subst this
    exact le_max_left _ _
  · exact (pA_mono hq h2 h3).trans (le_max_right _ _)

lemma pA_pos : ∀ p ≤ 16, 2 ≤ pA p := by
  intro p hp
  interval_cases p <;> norm_num [pA]

lemma pLo_ge : ∀ p ≤ 16, 7789 / 10000 ≤ pLo p := by
  intro p hp
  interval_cases p <;> norm_num [pLo]

lemma pLo_le_pHi : ∀ p ≤ 16, pLo p ≤ pHi p := by
  intro p hp
  interval_cases p <;> norm_num [pLo, pHi]

lemma pHi_le : ∀ p ≤ 16, pHi p ≤ 11 / 12 := by
  intro p hp
  interval_cases p <;> norm_num [pHi]

lemma tops_pos : ∀ p ≤ 16, 0 < tops p := by
  intro p hp
  interval_cases p <;> norm_num [tops, pA, pLo]

/-- A step's largest count exponent is its `A(1 − lo)`: below it, `1 − γ/A ≥ lo`. -/
lemma pLo_le_of_tops {p : ℕ} (hp : p ≤ 16) {x : ℝ} (hx : x ≤ tops p) : pLo p ≤ 1 - x / pA p := by
  have hA := pA_pos p hp
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
  unfold tops at hx
  linarith

/-- **The bound of the line `C`**: on `[a, …]` with `a` in the step `pa` (above the step up's largest exponent, at
most its own), a zero with count exponent `γ ≥ a` has `β ≤ min(hi_pa, 1 − a/A_pa)` (`β < 7789/10000` for `pa = 17`). -/
lemma bmax_C {pa : ℕ} (hpa : pa ≤ 17) {a γ β : ℝ} (hlo : pa = 0 ∨ tops (pa - 1) < a)
    (hhi : pa ≤ 16 → a ≤ tops pa) (haγ : a ≤ γ) (h1 : 1 / 2 ≤ β) (h2 : β ≤ 11 / 12) (hγ : γ ≤ ghx β) :
    (pa ≤ 16 → β ≤ pHi pa ∧ β ≤ 1 - a / pA pa) ∧ (pa = 17 → β ≤ 7789 / 10000) := by
  rcases ghx_piece h1 h2 hγ with hb | ⟨q, hq, hql, hqh, hqγ⟩
  · refine ⟨fun h16 => ?_, fun _ => hb.le⟩
    have hl := pLo_ge pa h16
    exact ⟨by linarith [pLo_le_pHi pa h16], by linarith [pLo_le_of_tops h16 (hhi h16)]⟩
  · have hγq : γ ≤ tops q := by
      unfold tops
      have := pA_pos q hq
      nlinarith
    -- a step above `pa` cannot have a count exponent `≥ a`
    have hqa : pa ≤ q := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      rcases hlo with h0 | hlo
      · omega
      · have := tops_mono (show q ≤ pa - 1 by omega) (by omega)
        linarith
    refine ⟨fun h16 => ?_, fun h17 => by omega⟩
    rcases hqa.lt_or_eq with hlt | heq
    · have := pHi_le_pLo hlt hq
      exact ⟨by linarith [pLo_le_pHi pa h16], by linarith [pLo_le_of_tops h16 (hhi h16)]⟩
    · subst heq
      have hA := pA_pos pa h16
      refine ⟨hqh, ?_⟩
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
      nlinarith

/-- **The bound of the line `W`**: on `[a, b]` with `a` in the step `pa` and `b` in the step `pb ≤ 16`, a zero with
count exponent `γ ∈ [a, b]`, `γ ≥ 0`, has `β ≤ 1 − γ/max(A_pa, A_pb)`. -/
lemma bmax_W {pa pb : ℕ} (hpa : pa ≤ 17) (hpb : pb ≤ 16) {a b γ β : ℝ} (hlo : pa = 0 ∨ tops (pa - 1) < a)
    (hbhi : b ≤ tops pb) (hab : a ≤ b) (haγ : a ≤ γ) (hγb : γ ≤ b) (hγ0 : 0 ≤ γ) (h1 : 1 / 2 ≤ β)
    (h2 : β ≤ 11 / 12) (hγ : γ ≤ ghx β) : β ≤ 1 - γ / max (pA pa) (pA pb) := by
  have hApb := pA_pos pb hpb
  have hmax : 2 ≤ max (pA pa) (pA pb) := hApb.trans (le_max_right _ _)
  -- `1 − γ/max ≥ 1 − γ/A_pb ≥ lo_pb`
  have hmid : pLo pb ≤ 1 - γ / max (pA pa) (pA pb) := by
    have h := pLo_le_of_tops hpb (hγb.trans hbhi)
    have : γ / max (pA pa) (pA pb) ≤ γ / pA pb :=
      div_le_div_of_nonneg_left hγ0 (by linarith) (le_max_right _ _)
    linarith
  -- `pa ≤ pb`
  have hpab : pa ≤ pb := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    rcases hlo with h0 | hlo
    · omega
    · have := tops_mono (show pb ≤ pa - 1 by omega) (by omega)
      linarith
  rcases ghx_piece h1 h2 hγ with hb | ⟨q, hq, hql, hqh, hqγ⟩
  · linarith [pLo_ge pb hpb]
  · have hγq : γ ≤ tops q := by
      unfold tops
      have := pA_pos q hq
      nlinarith
    have hqa : pa ≤ q := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      rcases hlo with h0 | hlo
      · omega
      · have := tops_mono (show q ≤ pa - 1 by omega) (by omega)
        linarith
    rcases le_or_gt q pb with hqb | hqb
    · have hAq := pA_le_max hqa hqb hpb
      have hAq0 := pA_pos q hq
      have hβ : β ≤ 1 - γ / pA q := by
        rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
        nlinarith
      have : γ / max (pA pa) (pA pb) ≤ γ / pA q := div_le_div_of_nonneg_left hγ0 (by linarith) hAq
      linarith
    · linarith [pHi_le_pLo hqb hq]

/-! ### The tables and the fixed point -/

lemma get_tFT : ∀ p < 18, get tFT p = ftN p := by decide +kernel

lemma get_tFTm : ∀ p < 18, get tFTm p = if p = 0 then 0 else ftN (p - 1) := by decide +kernel

lemma get_tIA : ∀ p < 18, get tIA p = iaN p := by decide +kernel

lemma get_tDH : ∀ p < 18, get tDH p = dhN p := by decide +kernel

lemma S_real : (S : ℝ) = 18446744073709551616 := by norm_num [S]

lemma S_pos : (0 : ℝ) < S := by rw [S_real]; norm_num

lemma H_real : (H : ℝ) = S / 2 := by rw [S_real]; norm_num [H]

lemma ft_le : ∀ p ≤ 16, (ftN p : ℝ) ≤ tops p * S := by
  intro p hp
  rw [S_real]
  interval_cases p <;> norm_num [ftN, tops, pA, pLo]

lemma ft_gt : ∀ p ≤ 16, tops p * S < ftN p + 1 := by
  intro p hp
  rw [S_real]
  interval_cases p <;> norm_num [ftN, tops, pA, pLo]

lemma ia_le : ∀ p ≤ 16, (iaN p : ℝ) * pA p ≤ S := by
  intro p hp
  rw [S_real]
  interval_cases p <;> norm_num [iaN, pA]

lemma dh_le : ∀ p ≤ 16, (dhN p : ℝ) ≤ (1 - 4 / 10 ^ 6 - pHi p) * S := by
  intro p hp
  rw [S_real]
  interval_cases p <;> norm_num [dhN, pHi]

lemma dh_le17 : (dhN 17 : ℝ) ≤ (1 - 4 / 10 ^ 6 - 7789 / 10000) * S := by
  rw [S_real]; norm_num [dhN]

lemma WC_ge : 4 / 10 ^ 6 * (S : ℝ) ≤ WC := by rw [S_real]; norm_num [WC]

lemma MG_ge : (S : ℝ) / 25000 ≤ MG := by rw [S_real]; norm_num [MG]

lemma K1U_ge : (5 / 12 + 1 / 1000 + 2 * (1 / 1000)) * (S : ℝ) ≤ K1U := by rw [S_real]; norm_num [K1U]

lemma K1D_le : (K1D : ℝ) ≤ (5 / 12 + 1 / 1000 + 2 * (1 / 1000)) * S := by rw [S_real]; norm_num [K1D]

lemma M1U_ge : (11 / 12 + 1 / 1000) * (S : ℝ) ≤ M1U := by rw [S_real]; norm_num [M1U]

lemma M1D_le : (M1D : ℝ) ≤ (11 / 12 + 1 / 1000) * S := by rw [S_real]; norm_num [M1D]

lemma HP_le : (HP : ℝ) ≤ (1 - 4 / 10 ^ 6 - 11 / 12) * S := by rw [S_real]; norm_num [HP]

lemma S_eq_pow : S = 2 ^ 64 := by norm_num [S]

lemma SM_eq : SM = S - 1 := by norm_num [SM, S]

lemma mulF_eq (x y : ℕ) : mulF x y = x * y / S := by
  show (x * y) >>> 64 = x * y / S
  rw [Nat.shiftRight_eq_div_pow, S_eq_pow]

lemma mulC_eq (x y : ℕ) : mulC x y = (x * y + (S - 1)) / S := by
  show (x * y + SM) >>> 64 = (x * y + (S - 1)) / S
  rw [Nat.shiftRight_eq_div_pow, SM_eq, S_eq_pow]

/-- `n ≤ ⌈n/d⌉·d`. -/
lemma le_cdiv_mul (n d : ℕ) (hd : 0 < d) : n ≤ (n + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (n + (d - 1)) d
  have h2 := Nat.mod_lt (n + (d - 1)) hd
  have : n + (d - 1) < (n + (d - 1)) / d * d + d := by
    calc n + (d - 1) = d * ((n + (d - 1)) / d) + (n + (d - 1)) % d := h1.symm
      _ < d * ((n + (d - 1)) / d) + d := by omega
      _ = (n + (d - 1)) / d * d + d := by ring
  omega

/-- `⌊n/d⌋ ≤ n/d` in the reals. -/
lemma div_cast_le (n d : ℕ) : ((n / d : ℕ) : ℝ) ≤ n / d := Nat.cast_div_le

/-- `mulF x y = ⌊xy/S⌋ ≤ xy/S`. -/
lemma mulF_le (x y : ℕ) : (mulF x y : ℝ) ≤ x * y / S := by
  rw [mulF_eq]
  have := div_cast_le (x * y) S
  push_cast at this
  exact this

/-- `mulC x y = ⌈xy/S⌉ ≥ xy/S`. -/
lemma mulC_ge (x y : ℕ) : (x : ℝ) * y / S ≤ mulC x y := by
  rw [mulC_eq, div_le_iff₀ S_pos]
  have key := le_cdiv_mul (x * y) S (by norm_num [S])
  exact_mod_cast key

/-- A truncated difference is at least the difference. -/
lemma sub_le_tsub (a b : ℕ) : (a : ℝ) - b ≤ (Nat.sub a b : ℕ) := by
  rcases le_total b a with h | h
  · rw [show Nat.sub a b = a - b from rfl, Nat.cast_sub h]
  · rw [show Nat.sub a b = a - b from rfl, Nat.sub_eq_zero_of_le h]
    simp only [Nat.cast_zero, sub_nonpos]
    exact_mod_cast h

lemma ble_false {a b : ℕ} (h : ¬a ≤ b) : Nat.ble a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.le_of_ble_eq_true h')

lemma minN_eq (a b : ℕ) : minN a b = min a b := by
  unfold minN
  by_cases hab : a ≤ b
  · rw [Nat.ble_eq_true_of_le hab, Bool.cond_true, min_eq_left hab]
  · rw [ble_false hab, Bool.cond_false, min_eq_right (by omega)]

lemma maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  by_cases hab : a ≤ b
  · rw [Nat.ble_eq_true_of_le hab, Bool.cond_true, max_eq_right hab]
  · rw [ble_false hab, Bool.cond_false, max_eq_left (by omega)]

/-- The value of the line `(P0 + P1·γ − N0 − N1·γ)/S`. -/
def lv (p0 p1 n0 n1 : ℕ) (γ : ℝ) : ℝ := ((p0 : ℝ) + p1 * γ - n0 - n1 * γ) / S

/-- `le0` at `x`: the line is at most `0` at `x/S`. -/
lemma le0_sound {p0 p1 n0 n1 x : ℕ} (h : le0 p0 p1 n0 n1 x = true) : lv p0 p1 n0 n1 (x / S) ≤ 0 := by
  simp only [le0, Nat.ble_eq, Nat.add_eq] at h
  have h' : ((p0 + mulC p1 x : ℕ) : ℝ) ≤ ((n0 + mulF n1 x : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have h1 := mulC_ge p1 x
  have h2 := mulF_le n1 x
  unfold lv
  rw [div_nonpos_iff]
  right
  refine ⟨?_, S_pos.le⟩
  have e1 : (p1 : ℝ) * (x / S) = p1 * x / S := by ring
  have e2 : (n1 : ℝ) * (x / S) = n1 * x / S := by ring
  rw [e1, e2]
  linarith

/-- A line at most `0` at both ends of an interval is at most `0` on it. -/
lemma lv_interval {p0 p1 n0 n1 : ℕ} {a b γ : ℝ} (ha : lv p0 p1 n0 n1 a ≤ 0) (hb : lv p0 p1 n0 n1 b ≤ 0)
    (h1 : a ≤ γ) (h2 : γ ≤ b) : lv p0 p1 n0 n1 γ ≤ 0 := by
  unfold lv at *
  rw [div_nonpos_iff] at ha hb ⊢
  right
  refine ⟨?_, S_pos.le⟩
  rcases ha with ⟨_, h⟩ | ⟨ha, _⟩
  · exact absurd h (not_le.mpr S_pos)
  rcases hb with ⟨_, h⟩ | ⟨hb, _⟩
  · exact absurd h (not_le.mpr S_pos)
  rcases le_total (p1 : ℝ) n1 with hs | hs
  · nlinarith
  · nlinarith

/-! ### The terms' lines -/

/-- `s(t − 1) − sτ ≤ (max(1 − ks, 0) − γ)/(2k)` from the moment's condition at `k`. -/
lemma mom_bound {k : ℕ} (hk : 1 ≤ k) {s t γ : ℝ} (h : γ ≤ momExp k s (t - 1 / 10 ^ 6)) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤ (max (1 - k * s) 0 - γ) / (2 * k) := by
  unfold momExp at h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < 2 * k := by linarith
  rw [le_div_iff₀ hk0]
  have hm : max 1 ((k : ℝ) * s) - k * s = max (1 - k * s) 0 := by
    rcases le_total 1 ((k : ℝ) * s) with h1 | h1
    · rw [max_eq_right h1, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_left (by linarith)]
  nlinarith

/-- The value of the term's line `c` at `γ`: the lines of `k₀ − 1` (`0`) and `k₀` (`1`), `C` (`2`), `W` (else). -/
def tline (t : Tm) (dS iax c : ℕ) (γ : ℝ) : ℝ :=
  if c = 0 then ((t.a0 : ℝ) - t.a1 * γ) / S
  else if c = 1 then -(t.b1 * γ) / S
  else if c = 2 then -(mulF t.lo dS : ℝ) / S
  else ((t.lw : ℝ) - mulF t.lo iax * γ) / S

lemma tm_small {lo k0 : ℕ} (h : k0 ≤ 1) : (mkTmK lo k0).a0 = SS ∧ (mkTmK lo k0).a1 = 0 := by
  have hb : Nat.ble k0 1 = true := Nat.ble_eq_true_of_le h
  constructor
  · show cond (Nat.ble k0 1) SS _ = SS
    rw [hb, Bool.cond_true]
  · show cond (Nat.ble k0 1) 0 _ = 0
    rw [hb, Bool.cond_true]

lemma SS_real : (SS : ℝ) = S * S := by norm_num [SS, S]

lemma tm_big {lo k0 : ℕ} (h : 2 ≤ k0) :
    (mkTmK lo k0).a0 = (S - (k0 - 1) * lo + (2 * (k0 - 1) - 1)) / (2 * (k0 - 1)) ∧
      (mkTmK lo k0).a1 = S / (2 * (k0 - 1)) := by
  have hb := ble_false (show ¬k0 ≤ 1 by omega)
  constructor
  · show cond (Nat.ble k0 1) SS _ = _
    rw [hb, Bool.cond_false]
    rfl
  · show cond (Nat.ble k0 1) 0 _ = _
    rw [hb, Bool.cond_false]
    rfl

lemma tm_b1 (lo k0 : ℕ) : (mkTmK lo k0).b1 = S / (2 * k0) := rfl

lemma tm_lw (lo k0 : ℕ) : (mkTmK lo k0).lw = mulC lo WC := rfl

lemma tm_lo (lo k0 : ℕ) : (mkTmK lo k0).lo = lo := rfl

lemma mkTm_eq (lo : ℕ) : mkTm lo = mkTmK lo ((S + (lo - 1)) / lo) := rfl

/-- The moments' line for `k` bounds the term: `s(t − 1) − sτ ≤ (⌈(S − k·lo)⁺/(2k)⌉ − ⌊S/(2k)⌋γ)/S`. -/
lemma kline_le {lo k : ℕ} (hk : 1 ≤ k) {s t γ : ℝ} (hs : (lo : ℝ) / S ≤ s) (hγ0 : 0 ≤ γ)
    (hm : γ ≤ momExp k s (t - 1 / 10 ^ 6)) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤
      ((((S - k * lo + (2 * k - 1)) / (2 * k) : ℕ) : ℝ) - ((S / (2 * k) : ℕ) : ℝ) * γ) / S := by
  have hS := S_pos
  have hmb := mom_bound hk hm
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℝ) < 2 * k := by linarith
  have h2k : 0 < 2 * k := by omega
  -- `a0 ≥ (S − k·lo)⁺/(2k)`
  have ha0 : (((S - k * lo : ℕ)) : ℝ) / (2 * k) ≤ (((S - k * lo + (2 * k - 1)) / (2 * k) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hK]
    have key := le_cdiv_mul (S - k * lo) (2 * k) h2k
    have := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at this
    linarith
  have ha1 : ((S / (2 * k) : ℕ) : ℝ) ≤ S / (2 * k) := by
    have := div_cast_le S (2 * k)
    push_cast at this
    exact this
  have hsub : (S : ℝ) - k * lo ≤ ((S - k * lo : ℕ) : ℝ) := by
    have := sub_le_tsub S (k * lo)
    push_cast at this
    exact this
  have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
  have hmx : max (1 - (k : ℝ) * s) 0 ≤ ((S - k * lo : ℕ) : ℝ) / S := by
    apply max_le
    · have : (k : ℝ) * (lo / S) ≤ k * s := mul_le_mul_of_nonneg_left hs (by linarith)
      have e : (1 : ℝ) - k * (lo / S) = (S - k * lo) / S := by field_simp
      have : (S - k * lo) / S ≤ ((S - k * lo : ℕ) : ℝ) / S := div_le_div_of_nonneg_right hsub hS.le
      linarith
    · positivity
  have hγa1 : γ * ((S / (2 * k) : ℕ) : ℝ) ≤ γ * (S / (2 * k)) := mul_le_mul_of_nonneg_left ha1 hγ0
  calc s * (t - 1) - s * (1 / 10 ^ 6) ≤ (max (1 - k * s) 0 - γ) / (2 * k) := hmb
    _ ≤ (((S - k * lo : ℕ) : ℝ) / S - γ) / (2 * k) := by
      apply div_le_div_of_nonneg_right _ hK.le; linarith
    _ = (((S - k * lo : ℕ) : ℝ) / (2 * k) - γ * (S / (2 * k))) / S := by
      field_simp
    _ ≤ ((((S - k * lo + (2 * k - 1)) / (2 * k) : ℕ) : ℝ) - ((S / (2 * k) : ℕ) : ℝ) * γ) / S := by
      apply div_le_div_of_nonneg_right _ hS.le; linarith

/-- **Each term's line bounds the term**: for `s ≥ lo/S`, `t ≤ β + w`, `β ≤ 11/12`, `γ ≥ 0`, the moments' conditions,
`dS ≤ (1 − w − β)S` (for `C`) and `γ·iax ≤ (1 − β)S` (for `W`), `s(t − 1) − sτ` is at most each line at `γ`. -/
lemma term_le (lo dS iax c : ℕ) {s t β γ : ℝ} (hs : (lo : ℝ) / S ≤ s) (ht : t ≤ β + 4 / 10 ^ 6)
    (hβ : β ≤ 11 / 12) (hγ0 : 0 ≤ γ) (hk : ∀ k : ℕ, 1 ≤ k → γ ≤ momExp k s (t - 1 / 10 ^ 6))
    (hC : (dS : ℝ) ≤ (1 - 4 / 10 ^ 6 - β) * S) (hW : γ * iax ≤ (1 - β) * S) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤ tline (mkTm lo) dS iax c γ := by
  have hS := S_pos
  have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
  have hs0 : 0 ≤ s := hlo0.trans hs
  -- the half-plane: `s(t − 1) ≤ (lo/S)(β + w − 1)`
  have hP : s * (t - 1) ≤ lo / S * (β + 4 / 10 ^ 6 - 1) := by
    have h1 : t - 1 ≤ β + 4 / 10 ^ 6 - 1 := by linarith
    have h2 : β + 4 / 10 ^ 6 - 1 ≤ 0 := by linarith
    nlinarith
  have hτ : 0 ≤ s * (1 / 10 ^ 6) := by positivity
  have hneg : s * (t - 1) ≤ 0 := by
    have : lo / S * (β + 4 / 10 ^ 6 - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlo0 (by linarith)
    linarith
  rw [mkTm_eq]
  set k0 := (S + (lo - 1)) / lo with hk0
  unfold tline
  by_cases c0 : c = 0
  · simp only [c0, ite_true]
    rcases le_or_gt k0 1 with hk1 | hk1
    · rw [(tm_small hk1).1, (tm_small hk1).2, SS_real]
      push_cast
      rw [show (S : ℝ) * S - 0 * γ = S * S by ring, mul_div_assoc, div_self hS.ne', mul_one]
      linarith
    · rw [(tm_big hk1).1, (tm_big hk1).2]
      exact kline_le (by omega) hs hγ0 (hk _ (by omega))
  by_cases c1 : c = 1
  · simp only [c1, one_ne_zero, ite_false, ite_true, tm_b1]
    rcases Nat.eq_zero_or_pos lo with hl | hl
    · -- `lo = 0`: the line is `0`
      have : k0 = 0 := by simp [hk0, hl]
      rw [this]
      simp only [Nat.mul_zero, Nat.div_zero, Nat.cast_zero, zero_mul, neg_zero, zero_div]
      linarith
    · have hk0lo : S ≤ k0 * lo := by
        have := le_cdiv_mul S lo hl
        simpa [hk0] using this
      have hk01 : 1 ≤ k0 := by
        rcases Nat.eq_zero_or_pos k0 with h0 | h0
        · rw [h0] at hk0lo; norm_num [S] at hk0lo
        · exact h0
      have hmb := mom_bound hk01 (hk k0 hk01)
      have hkr : (1 : ℝ) ≤ k0 := by exact_mod_cast hk01
      have hK : (0 : ℝ) < 2 * k0 := by linarith
      -- `k₀ s ≥ k₀ lo/S ≥ 1`
      have hks : 1 ≤ (k0 : ℝ) * s := by
        have h1 : (S : ℝ) ≤ k0 * lo := by exact_mod_cast hk0lo
        have h2 : (1 : ℝ) ≤ k0 * (lo / S) := by
          rw [mul_div_assoc', le_div_iff₀ hS]; linarith
        have h3 : (k0 : ℝ) * (lo / S) ≤ k0 * s := mul_le_mul_of_nonneg_left hs (by linarith)
        linarith
      have hmx : max (1 - (k0 : ℝ) * s) 0 = 0 := max_eq_right (by linarith)
      rw [hmx] at hmb
      have hb1 : ((S / (2 * k0) : ℕ) : ℝ) ≤ S / (2 * k0) := by
        have := div_cast_le S (2 * k0)
        push_cast at this
        exact this
      have : γ * ((S / (2 * k0) : ℕ) : ℝ) ≤ γ * (S / (2 * k0)) := mul_le_mul_of_nonneg_left hb1 hγ0
      calc s * (t - 1) - s * (1 / 10 ^ 6) ≤ (0 - γ) / (2 * k0) := hmb
        _ = -(γ * (S / (2 * k0))) / S := by field_simp; ring
        _ ≤ -(((S / (2 * k0) : ℕ) : ℝ) * γ) / S := by
          apply div_le_div_of_nonneg_right _ hS.le; linarith
  by_cases c2 : c = 2
  · simp only [c2, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ite_false, ite_true, tm_lo]
    have hF := mulF_le lo dS
    have hd : (lo : ℝ) * dS / S ≤ -(lo / S * (β + 4 / 10 ^ 6 - 1)) * S := by
      have e : -(lo / S * (β + 4 / 10 ^ 6 - 1)) * S = lo * ((1 - 4 / 10 ^ 6 - β) * S) / S := by
        field_simp
        ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg lo)
    have h3 : lo / S * (β + 4 / 10 ^ 6 - 1) ≤ -(mulF lo dS : ℝ) / S := by
      rw [le_div_iff₀ hS]
      linarith
    linarith
  · simp only [c0, c1, c2, ite_false, tm_lo, tm_lw]
    have hF := mulF_le lo iax
    have hC' := mulC_ge lo WC
    have hW' := WC_ge
    -- `lw ≥ lo·w·S/S`, `mulF lo iax·γ ≤ (lo/S)(1 − β)S`
    have h1 : (lo : ℝ) / S * (4 / 10 ^ 6) * S ≤ mulC lo WC := by
      have e : (lo : ℝ) / S * (4 / 10 ^ 6) * S = lo * (4 / 10 ^ 6 * S) / S := by field_simp
      rw [e]
      calc (lo : ℝ) * (4 / 10 ^ 6 * S) / S ≤ lo * WC / S := by
            apply div_le_div_of_nonneg_right _ hS.le
            exact mul_le_mul_of_nonneg_left hW' (Nat.cast_nonneg _)
        _ ≤ mulC lo WC := hC'
    have h2 : (mulF lo iax : ℝ) * γ ≤ lo / S * ((1 - β) * S) := by
      calc (mulF lo iax : ℝ) * γ ≤ lo * iax / S * γ := mul_le_mul_of_nonneg_right hF hγ0
        _ = lo / S * (γ * iax) := by ring
        _ ≤ lo / S * ((1 - β) * S) := mul_le_mul_of_nonneg_left hW hlo0
    have h3 : lo / S * (β + 4 / 10 ^ 6 - 1) ≤ ((mulC lo WC : ℝ) - mulF lo iax * γ) / S := by
      rw [le_div_iff₀ hS]
      nlinarith
    linarith

/-- **The terms' sum**: `addTerms` adds to `(P0, N0, N1)` lines above the terms `v i` (each above every line of its
term). -/
lemma addTerms_sound (dS iax : ℕ) (γ : ℝ) : ∀ (ts : List Tm) (h p0 n0 n1 : ℕ) (v : ℕ → ℝ),
    (∀ i (hi : i < ts.length), ∀ c, v i ≤ tline ts[i] dS iax c γ) →
    (∑ i ∈ range ts.length, v i) + ((p0 : ℝ) - n0 - n1 * γ) / S ≤
      (((addTerms dS iax ts h p0 n0 n1).1 : ℝ) - (addTerms dS iax ts h p0 n0 n1).2.1 -
        (addTerms dS iax ts h p0 n0 n1).2.2 * γ) / S
  | [], h, p0, n0, n1, v, _ => by simp [addTerms]
  | t :: ts, h, p0, n0, n1, v, hv => by
    have hv0 := hv 0 (by simp)
    have hv' : ∀ i (hi : i < ts.length), ∀ c, v (i + 1) ≤ tline ts[i] dS iax c γ := fun i hi c =>
      hv (i + 1) (by simp; omega) c
    rw [List.length_cons, Finset.sum_range_succ']
    have hS := S_pos
    simp only [List.getElem_cons_zero] at hv0
    have hc : Nat.land h 3 < 4 := Nat.lt_succ_of_le (Nat.and_le_right)
    simp only [addTerms]
    generalize Nat.land h 3 = c at hc
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · have ih := addTerms_sound dS iax γ ts (Nat.shiftRight h 2) (Nat.add p0 t.a0) n0 (Nat.add n1 t.a1)
        (fun i => v (i + 1)) hv'
      have h0 := hv0 0
      simp only [tline, ite_true] at h0
      simp only [show Nat.beq 0 0 = true from rfl, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + t.a0 - n0 - (n1 + t.a1) * γ) / S = (p0 - n0 - n1 * γ) / S + (t.a0 - t.a1 * γ) / S := by
        ring
      rw [e] at ih
      linarith
    · have ih := addTerms_sound dS iax γ ts (Nat.shiftRight h 2) p0 n0 (Nat.add n1 t.b1) (fun i => v (i + 1)) hv'
      have h0 := hv0 1
      simp only [tline, one_ne_zero, ite_false, ite_true] at h0
      simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, Bool.cond_false, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) - n0 - (n1 + t.b1) * γ) / S = (p0 - n0 - n1 * γ) / S + -(t.b1 * γ) / S := by ring
      rw [e] at ih
      linarith
    · have ih := addTerms_sound dS iax γ ts (Nat.shiftRight h 2) p0 (Nat.add n0 (mulF t.lo dS)) n1
        (fun i => v (i + 1)) hv'
      have h0 := hv0 2
      simp only [tline, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ite_false, ite_true] at h0
      simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
        show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) - (n0 + mulF t.lo dS) - n1 * γ) / S = (p0 - n0 - n1 * γ) / S + -(mulF t.lo dS : ℝ) / S := by
        ring
      rw [e] at ih
      linarith
    · have ih := addTerms_sound dS iax γ ts (Nat.shiftRight h 2) (Nat.add p0 t.lw) n0 (Nat.add n1 (mulF t.lo iax))
        (fun i => v (i + 1)) hv'
      have h0 := hv0 3
      simp only [tline, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
        ite_false] at h0
      simp only [show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
        show Nat.beq 3 2 = false from rfl, Bool.cond_false]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + t.lw - n0 - (n1 + mulF t.lo iax) * γ) / S =
          (p0 - n0 - n1 * γ) / S + (t.lw - mulF t.lo iax * γ) / S := by ring
      rw [e] at ih
      linarith

/-! ### The clamp -/

/-- `y₀(m) = (5/12 + d + 2e − m(11/12 + d))/2`, the clamp's `y` at `γ = 0` (`d = e = 1/1000`). -/
def y0R (m : ℝ) : ℝ := (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2

/-- The clamp of `ResBinOK`: `min(max(1 − m, 0)/2, max(0, γ/2 + y₀(m)))`. -/
def clampR (γ m : ℝ) : ℝ := min (max (1 - m) 0 / 2) (max 0 (γ / 2 + y0R m))

/-- The clamp does not increase with `m`. -/
lemma clampR_anti {γ m m' : ℝ} (h : m' ≤ m) : clampR γ m ≤ clampR γ m' := by
  unfold clampR y0R
  apply min_le_min
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact max_le_max (by linarith) le_rfl
  · apply max_le_max le_rfl
    have : m' * (11 / 12 + 1 / 1000) ≤ m * (11 / 12 + 1 / 1000) := by nlinarith
    linarith

/-- The clamp does not decrease with `γ`. -/
lemma clampR_mono {γ γ' m : ℝ} (h : γ ≤ γ') : clampR γ m ≤ clampR γ' m := by
  unfold clampR
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  linarith

/-- The clamp's constants are right: `c1 ≥ max(1 − mlo/S, 0)/2·S` and `ydP − ydN ≤ y₀(mlo/S)·S ≤ yuP − yuN`. -/
structure ClampOK (mlo c1 yuP yuN ydP ydN : ℕ) : Prop where
  c1 : max (1 - (mlo : ℝ) / S) 0 / 2 * S ≤ c1
  yu : y0R (mlo / S) * S ≤ (yuP : ℝ) - yuN
  yd : (ydP : ℝ) - ydN ≤ y0R (mlo / S) * S

/-- `⌈x/2⌉ ≥ x/2`. -/
lemma half_up (x : ℕ) : (x : ℝ) / 2 ≤ ((x + 1) / 2 : ℕ) := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : x ≤ (x + 1) / 2 * 2 := by omega
  exact_mod_cast this

/-- `⌊x/2⌋ ≤ x/2`. -/
lemma half_dn (x : ℕ) : ((x / 2 : ℕ) : ℝ) ≤ x / 2 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : x / 2 * 2 ≤ x := Nat.div_mul_le_self x 2
  exact_mod_cast this

lemma shr1 (x : ℕ) : x >>> 1 = x / 2 := by rw [Nat.shiftRight_eq_div_pow, pow_one]

/-- A truncated difference is at least the difference (standard notation). -/
lemma sub_le_tsub' (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := sub_le_tsub a b

/-- The resonant test's clamp constants from `mlo` are right (in standard notation). -/
lemma clampOK_of' (mlo : ℕ) :
    ClampOK mlo ((S - mlo + 1) / 2) ((K1U - mulF mlo M1D + 1) / 2) ((mulF mlo M1D - K1U) / 2)
      ((K1D - mulC mlo M1U) / 2) ((mulC mlo M1U - K1D + 1) / 2) := by
  have hS := S_pos
  have hF := mulF_le mlo M1D
  have hC := mulC_ge mlo M1U
  have hM1D := M1D_le
  have hM1U := M1U_ge
  have hK1U := K1U_ge
  have hK1D := K1D_le
  -- `mtd ≤ (mlo/S)(11/12 + d)S ≤ mtu`
  have htd : (mulF mlo M1D : ℝ) ≤ (mlo : ℝ) / S * (11 / 12 + 1 / 1000) * S := by
    calc (mulF mlo M1D : ℝ) ≤ mlo * M1D / S := hF
      _ ≤ mlo * ((11 / 12 + 1 / 1000) * S) / S := by
        apply div_le_div_of_nonneg_right _ hS.le
        exact mul_le_mul_of_nonneg_left hM1D (Nat.cast_nonneg _)
      _ = (mlo : ℝ) / S * (11 / 12 + 1 / 1000) * S := by field_simp
  have htu : (mlo : ℝ) / S * (11 / 12 + 1 / 1000) * S ≤ mulC mlo M1U := by
    calc (mlo : ℝ) / S * (11 / 12 + 1 / 1000) * S = mlo * ((11 / 12 + 1 / 1000) * S) / S := by field_simp
      _ ≤ mlo * M1U / S := by
        apply div_le_div_of_nonneg_right _ hS.le
        exact mul_le_mul_of_nonneg_left hM1U (Nat.cast_nonneg _)
      _ ≤ mulC mlo M1U := hC
  have hy0 : y0R ((mlo : ℝ) / S) * S =
      ((5 / 12 + 1 / 1000 + 2 * (1 / 1000)) * S - (mlo : ℝ) / S * (11 / 12 + 1 / 1000) * S) / 2 := by
    unfold y0R; ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 := half_up (S - mlo)
    have h2 := sub_le_tsub' S mlo
    have h3 : (0 : ℝ) ≤ ((S - mlo : ℕ) : ℝ) := Nat.cast_nonneg _
    have e : max (1 - (mlo : ℝ) / S) 0 / 2 * S = max ((S : ℝ) - mlo) 0 / 2 := by
      rw [show (1 : ℝ) - mlo / S = (S - mlo) / S by field_simp]
      rcases le_total ((S : ℝ) - mlo) 0 with h | h
      · rw [max_eq_right h, max_eq_right (div_nonpos_of_nonpos_of_nonneg h hS.le)]; ring
      · rw [max_eq_left h, max_eq_left (div_nonneg h hS.le)]; field_simp
    rw [e]
    have : max ((S : ℝ) - mlo) 0 ≤ ((S - mlo : ℕ) : ℝ) := max_le h2 h3
    linarith
  · -- `yuP − yuN ≥ (K1U − mtd)/2 ≥ y₀·S`
    have key : ((K1U : ℝ) - mulF mlo M1D) / 2 ≤
        (((K1U - mulF mlo M1D + 1) / 2 : ℕ) : ℝ) - (((mulF mlo M1D - K1U) / 2 : ℕ) : ℝ) := by
      rcases le_total (mulF mlo M1D) K1U with h | h
      · have h1 := half_up (K1U - mulF mlo M1D)
        rw [Nat.cast_sub h] at h1
        rw [Nat.sub_eq_zero_of_le h]
        simp only [Nat.zero_div, Nat.cast_zero, sub_zero]
        exact h1
      · have h1 := half_dn (mulF mlo M1D - K1U)
        rw [Nat.cast_sub h] at h1
        rw [Nat.sub_eq_zero_of_le h]
        norm_num
        linarith
    rw [hy0]
    linarith
  · -- `ydP − ydN ≤ (K1D − mtu)/2 ≤ y₀·S`
    have key : (((K1D - mulC mlo M1U) / 2 : ℕ) : ℝ) - (((mulC mlo M1U - K1D + 1) / 2 : ℕ) : ℝ) ≤
        ((K1D : ℝ) - mulC mlo M1U) / 2 := by
      rcases le_total (mulC mlo M1U) K1D with h | h
      · have h1 := half_dn (K1D - mulC mlo M1U)
        rw [Nat.cast_sub h] at h1
        rw [Nat.sub_eq_zero_of_le h]
        norm_num
        linarith
      · have h1 := half_up (mulC mlo M1U - K1D)
        rw [Nat.cast_sub h] at h1
        rw [Nat.sub_eq_zero_of_le h]
        simp only [Nat.zero_div, Nat.cast_zero, zero_sub]
        linarith
    rw [hy0]
    linarith

/-- The clamp's line `0`: `max(0, ⌈b/2⌉ + yuP − yuN)`. -/
lemma clampL_0 (c1 yuP yuN ydP ydN a b : ℕ) :
    clampL c1 yuP yuN ydP ydN a b 0 = ((b + 1) / 2 + yuP - yuN, 0, 0) := by
  show (Nat.sub (Nat.add (Nat.shiftRight (Nat.add b 1) 1) yuP) yuN, 0, 0) = _
  rw [show Nat.shiftRight (Nat.add b 1) 1 = (b + 1) / 2 from shr1 (b + 1)]
  rfl

/-- The clamp's line `1`: `y + max(0, −y(a))`. -/
lemma clampL_1 (c1 yuP yuN ydP ydN a b : ℕ) :
    clampL c1 yuP yuN ydP ydN a b 1 = (yuP + (ydN - (a / 2 + ydP)), H, yuN) := by
  show (Nat.add yuP (Nat.sub ydN (Nat.add (Nat.shiftRight a 1) ydP)), H, yuN) = _
  rw [show Nat.shiftRight a 1 = a / 2 from shr1 a]
  rfl

/-- The clamp's line `c₁` for the other codes. -/
lemma clampL_2 (c1 yuP yuN ydP ydN a b cc : ℕ) (h0 : cc ≠ 0) (h1 : cc ≠ 1) :
    clampL c1 yuP yuN ydP ydN a b cc = (c1, 0, 0) := by
  unfold clampL
  rw [Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h)), Bool.cond_false,
    Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h)), Bool.cond_false]

/-- **The clamp's line bounds the clamp** on `[a/S, b/S]` for `m ≥ mlo/S`: `max(0, y(b))`, `y + max(0, −y(a))`, `c₁`. -/
lemma clampL_sound {mlo c1 yuP yuN ydP ydN : ℕ} (hok : ClampOK mlo c1 yuP yuN ydP ydN) (a b cc : ℕ) {γ m : ℝ}
    (hm : (mlo : ℝ) / S ≤ m) (ha : (a : ℝ) / S ≤ γ) (hb : γ ≤ (b : ℝ) / S) :
    clampR γ m * S ≤ ((clampL c1 yuP yuN ydP ydN a b cc).1 : ℝ) + (clampL c1 yuP yuN ydP ydN a b cc).2.1 * γ -
      (clampL c1 yuP yuN ydP ydN a b cc).2.2 := by
  have hS := S_pos
  have hc := clampR_anti (γ := γ) hm
  have hcl : clampR γ ((mlo : ℝ) / S) ≤ max (1 - (mlo : ℝ) / S) 0 / 2 := min_le_left _ _
  have hcr : clampR γ ((mlo : ℝ) / S) ≤ max 0 (γ / 2 + y0R ((mlo : ℝ) / S)) := min_le_right _ _
  have hy := hok.yu
  have hγb : γ * S ≤ b := by rwa [le_div_iff₀ hS] at hb
  have hγa : (a : ℝ) ≤ γ * S := by rwa [div_le_iff₀ hS] at ha
  have hcS : clampR γ m * S ≤ clampR γ ((mlo : ℝ) / S) * S := mul_le_mul_of_nonneg_right hc hS.le
  by_cases c0 : cc = 0
  · subst c0
    rw [clampL_0]
    simp only [Nat.cast_zero, zero_mul, add_zero, sub_zero]
    have h1 := half_up b
    have h2 := sub_le_tsub' ((b + 1) / 2 + yuP) yuN
    have h3 : (0 : ℝ) ≤ (((b + 1) / 2 + yuP - yuN : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at h2
    have hmx : max 0 (γ / 2 + y0R ((mlo : ℝ) / S)) * S ≤ (((b + 1) / 2 + yuP - yuN : ℕ) : ℝ) := by
      rw [max_mul_of_nonneg _ _ hS.le, zero_mul]
      apply max_le h3
      have e : (γ / 2 + y0R ((mlo : ℝ) / S)) * S = γ * S / 2 + y0R ((mlo : ℝ) / S) * S := by ring
      rw [e]
      linarith
    have := mul_le_mul_of_nonneg_right hcr hS.le
    linarith
  by_cases c1' : cc = 1
  · subst c1'
    rw [clampL_1, H_real]
    have h1 := half_dn a
    have h2 := sub_le_tsub' ydN (a / 2 + ydP)
    have h3 : (0 : ℝ) ≤ ((ydN - (a / 2 + ydP) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hyd := hok.yd
    push_cast at h2 ⊢
    have hmx : max 0 (γ / 2 + y0R ((mlo : ℝ) / S)) * S ≤
        (yuP : ℝ) + ((ydN - (a / 2 + ydP) : ℕ) : ℝ) + S / 2 * γ - yuN := by
      rw [max_mul_of_nonneg _ _ hS.le, zero_mul]
      apply max_le
      · nlinarith
      · have e : (γ / 2 + y0R ((mlo : ℝ) / S)) * S = γ * S / 2 + y0R ((mlo : ℝ) / S) * S := by ring
        rw [e]
        nlinarith
    have := mul_le_mul_of_nonneg_right hcr hS.le
    linarith
  · rw [clampL_2 _ _ _ _ _ _ _ _ c0 c1']
    simp only [Nat.cast_zero, zero_mul, add_zero, sub_zero]
    have := hok.c1
    have := mul_le_mul_of_nonneg_right hcl hS.le
    linarith

/-! ### An interval -/

/-- **The bound at `γ`**: for the rest's lower ends `los` (exponents `s j ≥ los_j/S` with sum at most `L`), the
variable's exponent `m ≥ mlo/S` and a zero's real part `β` with the classes' conditions,
`Σ_j s_j(t_j − 1) + γ/2 + clamp ≤ −1/25000`. -/
def GoalAt (L : ℝ) (los : List ℕ) (mlo : ℕ) (γ : ℝ) : Prop :=
  ∀ (β m : ℝ) (s t : ℕ → ℝ), 1 / 2 ≤ β → β ≤ 11 / 12 → γ ≤ ghx β → (∀ j < los.length, t j ≤ β + 4 / 10 ^ 6) →
    (∀ j < los.length, ∀ k : ℕ, 1 ≤ k → γ ≤ momExp k (s j) (t j - 1 / 10 ^ 6)) → (mlo : ℝ) / S ≤ m →
    (∀ j (hj : j < los.length), (los[j] : ℝ) / S ≤ s j) → ∑ j ∈ range los.length, s j ≤ L →
    ∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m ≤ -(1 / 25000)

/-- The pieces are in order along `γ`: an interval's ends' pieces `pa ≤ pb`. -/
lemma piece_order {pa pb : ℕ} (hpa : pa ≤ 17) (hpb : pb ≤ 17) {a b : ℝ} (hlo : pa = 0 ∨ tops (pa - 1) < a)
    (hbhi : pb ≤ 16 → b ≤ tops pb) (hab : a ≤ b) : pa ≤ pb := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  rcases hlo with h0 | hlo
  · omega
  · have := tops_mono (show pb ≤ pa - 1 by omega) (by omega)
    have := hbhi (by omega)
    linarith

lemma intv_eq (ts : List Tm) (c1 yuP yuN ydP ydN ltm a pa r : ℕ) :
    intv ts c1 yuP yuN ydP ydN ltm a pa r =
      (Nat.ble (pieceOf (bOf r)) 17 && Nat.blt (get tFTm (pieceOf (bOf r))) (bOf r) &&
        Nat.ble (bOf r) (get tFT (pieceOf (bOf r))) && Nat.ble a (bOf r) &&
        chkI ts ltm (maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC))
          (minN (get tIA pa) (get tIA (pieceOf (bOf r)))) a (bOf r)
          (chMid (maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC))
            (minN (get tIA pa) (get tIA (pieceOf (bOf r)))) (Nat.shiftRight (Nat.add a (bOf r)) 1) ts)
          (clampL c1 yuP yuN ydP ydN a (bOf r)
            (pickC c1 yuP yuN ydP ydN a (bOf r) (Nat.shiftRight (Nat.add a (bOf r)) 1)))) := rfl

lemma chkI_eq (ts : List Tm) (ltm dS iax a b ch : ℕ) (cl : ℕ × ℕ × ℕ) :
    chkI ts ltm dS iax a b ch cl =
      (le0 (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).1 (Nat.add H cl.2.1)
          (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).2.1
          (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).2.2 a &&
        le0 (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).1 (Nat.add H cl.2.1)
          (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).2.1
          (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0).2.2 b) :=
  rfl

/-- The bound at `γ` from the sum's line: the terms' and the clamp's lines and the check at `γ`. -/
lemma goal_of_lines {L X sv ss γ c tm cl0 cl1 cl2 P0 N0 N1 : ℝ} (hS : 0 < (S : ℝ))
    (hX : X = sv + 1 / 10 ^ 6 * ss) (hss : ss ≤ L) (hltm : (L * (1 / 10 ^ 6) + 1 / 25000) * S ≤ tm)
    (hT : sv * S + (tm + cl0 - cl2 - 0 * γ) ≤ P0 - N0 - N1 * γ)
    (hγ : P0 + (S / 2 + cl1) * γ - N0 - N1 * γ ≤ 0) (hc : c * S ≤ cl0 + cl1 * γ - cl2) :
    X + γ / 2 + c ≤ -(1 / 25000) := by
  have hτ : 1 / 10 ^ 6 * ss * S ≤ L * (1 / 10 ^ 6) * S := by nlinarith
  have key : (X + γ / 2 + c + 1 / 25000) * S ≤ 0 := by
    rw [hX]
    nlinarith
  by_contra hcon
  have := mul_pos (show 0 < X + γ / 2 + c + 1 / 25000 by linarith) hS
  linarith


/-- **The line `C`'s condition**: `dS = max(DH_pa, (⌊a·IA_pa/S⌋ − WC)⁺) ≤ (1 − w − β)·S` for a zero with count exponent
`γ ≥ a/S`. -/
lemma line_C {pa : ℕ} (hpa : pa ≤ 17) {a : ℕ} {γ β : ℝ} (hlo' : pa = 0 ∨ tops (pa - 1) < a / S)
    (hhi' : pa ≤ 16 → (a : ℝ) / S ≤ tops pa) (hγa : (a : ℝ) / S ≤ γ) (h1 : 1 / 2 ≤ β) (h2 : β ≤ 11 / 12)
    (hγ : γ ≤ ghx β) :
    ((maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC) : ℕ) : ℝ) ≤ (1 - 4 / 10 ^ 6 - β) * S := by
  have hS := S_pos
  rw [maxN_eq, get_tDH pa (by omega), get_tIA pa (by omega)]
  have hC' := bmax_C hpa hlo' hhi' hγa h1 h2 hγ
  rw [Nat.cast_max]
  apply max_le
  · rcases Nat.lt_or_ge pa 17 with h16 | h17'
    · have h3 := dh_le pa (by omega)
      have h4 := (hC'.1 (by omega)).1
      have : (1 - 4 / 10 ^ 6 - pHi pa) * S ≤ (1 - 4 / 10 ^ 6 - β) * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS.le
      linarith
    · have hp : pa = 17 := by omega
      subst hp
      have h3 := dh_le17
      have h4 := hC'.2 rfl
      have : (1 - 4 / 10 ^ 6 - 7789 / 10000) * S ≤ (1 - 4 / 10 ^ 6 - β) * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS.le
      linarith
  · have hpos : (0 : ℝ) ≤ (1 - 4 / 10 ^ 6 - β) * S := mul_nonneg (by linarith) hS.le
    rcases le_total WC (mulF a (iaN pa)) with hw | hw
    · rw [show Nat.sub (mulF a (iaN pa)) WC = mulF a (iaN pa) - WC from rfl, Nat.cast_sub hw]
      rcases Nat.lt_or_ge pa 17 with h16 | h17'
      · have hia := ia_le pa (by omega)
        have hA := pA_pos pa (by omega)
        have hβ := (hC'.1 (by omega)).2
        have hF := mulF_le a (iaN pa)
        have hW := WC_ge
        -- `mulF a ia ≤ a·ia/S ≤ a/A = (a/S/A)·S ≤ (1 − β)·S`
        have h3 : (a : ℝ) * iaN pa / S ≤ a / pA pa := by
          rw [div_le_div_iff₀ hS (by linarith)]
          have := mul_le_mul_of_nonneg_left hia (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
          linarith
        have h4 : (a : ℝ) / pA pa = a / S / pA pa * S := by field_simp
        have h5 : a / S / pA pa * S ≤ (1 - β) * S := by
          apply mul_le_mul_of_nonneg_right _ hS.le; linarith
        have h6 : (1 - β) * S - 4 / 10 ^ 6 * S = (1 - 4 / 10 ^ 6 - β) * S := by ring
        linarith
      · have hp : pa = 17 := by omega
        subst hp
        have : mulF a (iaN 17) = 0 := by rw [mulF_eq]; simp [iaN]
        rw [this] at hw ⊢
        have : WC = 0 := by omega
        simp [this] at hpos ⊢
        exact hpos
    · rw [show Nat.sub (mulF a (iaN pa)) WC = mulF a (iaN pa) - WC from rfl, Nat.sub_eq_zero_of_le hw,
        Nat.cast_zero]
      exact hpos

/-- **The line `W`'s condition**: `γ·min(IA_pa, IA_pb) ≤ (1 − β)·S` for a zero with count exponent `γ ∈ [a/S, b/S]`. -/
lemma line_W {pa pb : ℕ} (hpa : pa ≤ 17) {a b : ℕ} {γ β : ℝ} (hlo' : pa = 0 ∨ tops (pa - 1) < a / S)
    (hbhi' : pb ≤ 16 → (b : ℝ) / S ≤ tops pb) (hab' : (a : ℝ) / S ≤ b / S) (hpb : pb ≤ 17)
    (hγa : (a : ℝ) / S ≤ γ) (hγb : γ ≤ b / S) (hγ0 : 0 ≤ γ) (h1 : 1 / 2 ≤ β) (h2 : β ≤ 11 / 12)
    (hγ : γ ≤ ghx β) : γ * ((minN (get tIA pa) (get tIA pb) : ℕ) : ℝ) ≤ (1 - β) * S := by
  have hS := S_pos
  rw [minN_eq, get_tIA pa (by omega), get_tIA pb (by omega)]
  have hpos : (0 : ℝ) ≤ (1 - β) * S := mul_nonneg (by linarith) hS.le
  rcases Nat.lt_or_ge pb 17 with h16 | h17'
  · have hpab := piece_order hpa hpb hlo' hbhi' hab'
    have hW' := bmax_W hpa (by omega) hlo' (hbhi' (by omega)) hab' hγa hγb hγ0 h1 h2 hγ
    have hAb := pA_pos pb (by omega)
    have hmax : 2 ≤ max (pA pa) (pA pb) := hAb.trans (le_max_right _ _)
    -- `iax·max(A_pa, A_pb) ≤ S`
    have hia : ((min (iaN pa) (iaN pb) : ℕ) : ℝ) * max (pA pa) (pA pb) ≤ S := by
      rw [Nat.cast_min]
      rcases le_total (pA pa) (pA pb) with hab2 | hab2
      · rw [max_eq_right hab2]
        have h3 := ia_le pb (by omega)
        have h4 : (min (iaN pa : ℝ) (iaN pb)) ≤ iaN pb := min_le_right _ _
        have h5 : (min (iaN pa : ℝ) (iaN pb)) * pA pb ≤ iaN pb * pA pb :=
          mul_le_mul_of_nonneg_right h4 (by linarith)
        linarith
      · rw [max_eq_left hab2]
        have h3 := ia_le pa (by omega)
        have hAa := pA_pos pa (by omega)
        have h4 : (min (iaN pa : ℝ) (iaN pb)) ≤ iaN pa := min_le_left _ _
        have h5 : (min (iaN pa : ℝ) (iaN pb)) * pA pa ≤ iaN pa * pA pa :=
          mul_le_mul_of_nonneg_right h4 (by linarith)
        linarith
    have h3 : γ / max (pA pa) (pA pb) ≤ 1 - β := by linarith
    have h4 : γ * ((min (iaN pa) (iaN pb) : ℕ) : ℝ) ≤ γ / max (pA pa) (pA pb) * S := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hia hγ0
      linarith
    have h5 : γ / max (pA pa) (pA pb) * S ≤ (1 - β) * S := mul_le_mul_of_nonneg_right h3 hS.le
    linarith
  · have hp : pb = 17 := by omega
    rw [hp]
    have : min (iaN pa) (iaN 17) = 0 := by simp [iaN]
    rw [this, Nat.cast_zero, mul_zero]
    exact hpos

set_option maxHeartbeats 1000000 in
/-- **One interval is sound**: `intv` on `[a, b]` with `a` in the piece `pa` gives `b`'s piece and the bound at every
`γ ∈ [a/S, b/S]`. -/
lemma intv_sound {L : ℝ} {los : List ℕ} {mlo c1 yuP yuN ydP ydN ltm a pa r : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (h : intv (los.map mkTm) c1 yuP yuN ydP ydN ltm a pa r = true) (hpa : pa ≤ 17)
    (hlo : pa = 0 ∨ tops (pa - 1) * S < a) (hhi : pa ≤ 16 → (a : ℝ) ≤ tops pa * S) :
    pieceOf (bOf r) ≤ 17 ∧ (pieceOf (bOf r) = 0 ∨ tops (pieceOf (bOf r) - 1) * S < bOf r) ∧
      (pieceOf (bOf r) ≤ 16 → (bOf r : ℝ) ≤ tops (pieceOf (bOf r)) * S) ∧ a ≤ bOf r ∧
      ∀ γ, (a : ℝ) / S ≤ γ → γ ≤ (bOf r : ℝ) / S → GoalAt L los mlo γ := by
  have hS := S_pos
  rw [intv_eq] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h17, hlt⟩, hle⟩, hab⟩, hchk⟩ := h
  generalize hbdef : bOf r = b at h17 hlt hle hab hchk ⊢
  generalize hpbdef : pieceOf b = pb at h17 hlt hle hchk ⊢
  -- the lines that the test picks at the midpoint: any choice is a bound
  generalize hccdef : pickC c1 yuP yuN ydP ydN a b (Nat.shiftRight (Nat.add a b) 1) = cc at hchk
  generalize hchdef : chMid (maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC)) (minN (get tIA pa) (get tIA pb))
    (Nat.shiftRight (Nat.add a b) 1) (los.map mkTm) = ch at hchk
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

/-! ### The intervals and the test -/

lemma runI_zero (ts : List Tm) (w c1 yuP yuN ydP ydN ltm a pa h : ℕ) :
    runI ts w c1 yuP yuN ydP ydN ltm 0 a pa h = Nat.beq a S := rfl

lemma runI_succ (ts : List Tm) (w c1 yuP yuN ydP ydN ltm k a pa h : ℕ) :
    runI ts w c1 yuP yuN ydP ydN ltm (k + 1) a pa h =
      (intv ts c1 yuP yuN ydP ydN ltm a pa (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) &&
        runI ts w c1 yuP yuN ydP ydN ltm k (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))
          (pieceOf (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))) (Nat.shiftRight h w)) := rfl

/-- **The intervals are sound**: `runI` from `a` in the piece `pa` gives the bound at every `γ ∈ (a/S, 1]`. -/
lemma runI_sound {L : ℝ} {los : List ℕ} {mlo c1 yuP yuN ydP ydN ltm w : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) :
    ∀ (k a pa h : ℕ), runI (los.map mkTm) w c1 yuP yuN ydP ydN ltm k a pa h = true → pa ≤ 17 →
      (pa = 0 ∨ tops (pa - 1) * S < a) → (pa ≤ 16 → (a : ℝ) ≤ tops pa * S) →
      ∀ γ, (a : ℝ) / S < γ → γ ≤ 1 → GoalAt L los mlo γ
  | 0, a, pa, h, hr, _, _, _, γ, hγa, hγ1 => by
    rw [runI_zero] at hr
    have ha : a = S := Nat.eq_of_beq_eq_true hr
    subst ha
    rw [div_self S_pos.ne'] at hγa
    linarith
  | k + 1, a, pa, h, hr, hpa, hlo, hhi, γ, hγa, hγ1 => by
    rw [runI_succ] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hi, hr⟩ := hr
    obtain ⟨h17, hblo, hbhi, hab, hgoal⟩ := intv_sound hok hltm hi hpa hlo hhi
    rcases le_or_gt γ ((bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) : ℕ) / S) with hγb | hγb
    · exact hgoal γ hγa.le hγb
    · exact runI_sound hok hltm k _ _ _ hr h17 hblo hbhi γ hγb hγ1

/-- The half-plane's sum bounds the rest: `Σ s_j(t_j − 1) ≤ −hpSum/S` for `β ≤ 11/12`. -/
lemma hpSum_le {β : ℝ} (hβ : β ≤ 11 / 12) : ∀ (los : List ℕ) (s t : ℕ → ℝ),
    (∀ j < los.length, t j ≤ β + 4 / 10 ^ 6) → (∀ j (hj : j < los.length), (los[j] : ℝ) / S ≤ s j) →
    ∑ j ∈ range los.length, s j * (t j - 1) ≤ -((hpSum (los.map mkTm) : ℕ) : ℝ) / S
  | [], s, t, _, _ => by simp [hpSum]
  | lo :: los, s, t, ht, hs => by
    have hS := S_pos
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons]
    have ih := hpSum_le hβ los (fun j => s (j + 1)) (fun j => t (j + 1))
      (fun j hj => ht (j + 1) (by simp; omega)) (fun j hj => by
        have := hs (j + 1) (by simp; omega)
        simpa using this)
    have h0 := hs 0 (by simp)
    have ht0 := ht 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have e : hpSum (mkTm lo :: los.map mkTm) = mulF lo HP + hpSum (los.map mkTm) := rfl
    rw [e]
    push_cast
    -- the head: `s₀(t₀ − 1) ≤ (lo/S)(β + w − 1) ≤ −(lo/S)(1 − w − 11/12) ≤ −mulF lo HP/S`
    have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
    have hs0 : 0 ≤ s 0 := hlo0.trans h0
    have hP : s 0 * (t 0 - 1) ≤ lo / S * (β + 4 / 10 ^ 6 - 1) := by
      have h1 : t 0 - 1 ≤ β + 4 / 10 ^ 6 - 1 := by linarith
      have h2 : β + 4 / 10 ^ 6 - 1 ≤ 0 := by linarith
      nlinarith
    have hP2 : lo / S * (β + 4 / 10 ^ 6 - 1) ≤ lo / S * (11 / 12 + 4 / 10 ^ 6 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hlo0
    have hF := mulF_le lo HP
    have hHP := HP_le
    have hF2 : (mulF lo HP : ℝ) / S ≤ lo / S * (1 - 4 / 10 ^ 6 - 11 / 12) := by
      rw [div_le_iff₀ hS]
      calc (mulF lo HP : ℝ) ≤ lo * HP / S := hF
        _ ≤ lo * ((1 - 4 / 10 ^ 6 - 11 / 12) * S) / S := by
          apply div_le_div_of_nonneg_right _ hS.le
          exact mul_le_mul_of_nonneg_left hHP (Nat.cast_nonneg _)
        _ = lo / S * (1 - 4 / 10 ^ 6 - 11 / 12) * S := by field_simp
    have e2 : -((mulF lo HP : ℝ) + hpSum (los.map mkTm)) / S =
        -(mulF lo HP : ℝ) / S + -(hpSum (los.map mkTm) : ℝ) / S := by ring
    rw [e2]
    have e3 : -(mulF lo HP : ℝ) / S = -((mulF lo HP : ℝ) / S) := by ring
    linarith

lemma shrN (x : ℕ) : Nat.shiftRight x 1 = x / 2 := shr1 x

/-- **The test with `m` and `Lτ + MARG` given is sound**: the bound at every `γ`. -/
theorem resTM_sound {L : ℝ} (hL : 0 ≤ L) {los : List ℕ} {mlo ltm k h : ℕ}
    (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) (hT : resTM (los.map mkTm) mlo ltm k h = true) :
    ∀ γ, GoalAt L los mlo γ := by
  have hS := S_pos
  unfold resTM at hT
  simp only [shrN, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Bool.and_eq_true, Nat.ble_eq, minN_eq] at hT
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
    exact runI_sound hok hltm k 0 0 h hrun (by norm_num) (Or.inl rfl)
      (fun _ => by rw [Nat.cast_zero]; exact mul_nonneg (tops_pos 0 (by norm_num)).le hS.le) γ
      (by rw [Nat.cast_zero, zero_div]; exact hγ0) hγ1 β m s t h1 h2 hγ ht hk hm hs hsum

/-- `ResBinOK` from the bound with the clamp. -/
lemma binOK_of {L X γ m : ℝ} (h : X + γ / 2 + clampR γ m ≤ -(1 / 25000)) :
    ResBinOK L (1 / 1000) (1 / 1000) (X + L - m) γ m := by
  unfold ResBinOK
  unfold clampR y0R at h
  rcases min_choice (max (1 - m) 0 / 2)
      (max 0 (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2)) with hmin | hmin
  · left
    rw [hmin] at h
    have e : (m + max m 1) / 2 - m = max (1 - m) 0 / 2 := by
      rcases le_total m 1 with hm | hm
      · rw [max_eq_right hm, max_eq_left (by linarith)]; ring
      · rw [max_eq_left hm, max_eq_right (by linarith)]; ring
    linarith
  · right
    rw [hmin] at h
    have hB0 := le_max_left (0 : ℝ) (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2)
    have hB1 := le_max_right (0 : ℝ) (γ / 2 + (5 / 12 + 1 / 1000 + 2 * (1 / 1000) - m * (11 / 12 + 1 / 1000)) / 2)
    constructor
    · linarith
    · linarith

/-- `⌈Lnum·S/(Lden·10⁶)⌉ + MG ≥ (Lτ + MARG)·S`. -/
lemma ltm_ok {Lnum Lden : ℕ} (hLd : 0 < Lden) :
    (Lnum : ℝ) / Lden * (1 / 10 ^ 6) + 1 / 25000 ≤
      (((Lnum * S + (Lden * 1000000 - 1)) / (Lden * 1000000) + MG : ℕ) : ℝ) / S := by
  have hS := S_pos
  have hd : 0 < Lden * 1000000 := by positivity
  have h1 := le_cdiv_mul (Lnum * S) (Lden * 1000000) hd
  have h2 : (Lnum : ℝ) * S ≤ (((Lnum * S + (Lden * 1000000 - 1)) / (Lden * 1000000) : ℕ) : ℝ) * (Lden * 1000000) := by
    exact_mod_cast h1
  have hMG := MG_ge
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  rw [le_div_iff₀ hS]
  push_cast
  have e : ((Lnum : ℝ) / Lden * (1 / 10 ^ 6) + 1 / 25000) * S = Lnum * S / (Lden * 1000000) + S / 25000 := by
    field_simp
    ring
  rw [e]
  have h3 : (Lnum : ℝ) * S / (Lden * 1000000) ≤ (((Lnum * S + (Lden * 1000000 - 1)) / (Lden * 1000000) : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    exact h2
  linarith

/-- **The test is sound**: `resT` gives `ResBox ghx L K m lo` at `L = Lnum/Lden` with the fixed point's
`m = ⌊L(DEN − hs − 1)S/DEN⌋/S` and `lo_j = ⌊L(c_j − 1)S/DEN⌋/S`. -/
theorem resT_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resT Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  unfold resT at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨_, hT⟩ := hT
  have hmap : (cs.map fun c => mkTm (loOf Lnum Lden c)) = (cs.map (loOf Lnum Lden)).map mkTm := by
    rw [List.map_map]
    rfl
  rw [hmap] at hT
  have hL : (0 : ℝ) ≤ (Lnum : ℝ) / Lden := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hgoal := resTM_sound hL (ltm_ok hLd) hT
  intro m s hm hs hsum β γ t h1 h2 hγ ht hk
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

/-- The test passes only with `hs + 1 < DEN`. -/
theorem resT_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resT Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  unfold resT at hT
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hT
  exact hT.1

/-- `ResBox` holds for larger lower bounds. -/
lemma resBox_mono {g : ℝ → ℝ} {L : ℝ} {K : ℕ} {mlo mlo' : ℝ} {lo lo' : ℕ → ℝ} (h : ResBox g L K mlo lo)
    (hm : mlo ≤ mlo') (hl : ∀ j < K, lo j ≤ lo' j) : ResBox g L K mlo' lo' :=
  fun m s hm' hs hsum => h m s (hm.trans hm') (fun j hj => (hl j hj).trans (hs j hj)) hsum

/-- **The test is sound, in the cells' units**: with `κ = L/DEN`, `L = Lnum/Lden`, cells `c_j ≥ 1` and `hs + 1 < DEN`,
`resT` gives `ResBox ghx L K (L − κ·hs − κ) (κ·c_j − κ)`. -/
theorem resT_sound_cells {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hc : ∀ c ∈ cs, 1 ≤ c) (hT : resT Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      ((Lnum : ℝ) / Lden - (Lnum : ℝ) / Lden / DEN * hs - (Lnum : ℝ) / Lden / DEN)
      (fun j => (Lnum : ℝ) / Lden / DEN * (cs.getD j 0) - (Lnum : ℝ) / Lden / DEN) := by
  have hS := S_pos
  have hD : (0 : ℝ) < DEN := by norm_num [DEN]
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have hhs : hs + 1 < DEN := by
    unfold resT at hT
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hT
    exact hT.1
  refine resBox_mono (resT_sound hLd hT) ?_ ?_
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
