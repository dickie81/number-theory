/-
# The resonant window's test with the large values of the powers is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTestDefs.lean`'s `resT2` is `resT` with one more bound for each term of the rest: a class of characters with
count exponent `γ` at which the prime sum of length `q^s` has the size `t` satisfies `γ ≤ lvExp k s (t − τ)` for
every `k` (`SieveTypeIIHM.ResCond`, from Chen, Gupta and Li's Proposition 3.1 for the `k`-th power of the sum), and
for `lo ≤ s ≤ hi`, `k·lo ≥ 2/3 + lvE` and `γ` above
`Γ = lvE + max(2k·hi(1/5 + lvE), 1/2 − k·lo(1/5 − 4lvE), 4/3 − k·lo(6/5 − 4lvE))` this gives
`s(t − 1) − sτ ≤ max(−lo(3/10 − lvE), (lvE − γ)/(2k), (1/2 + lvE − γ − k·lo)/(4k), (4/3 + lvE − γ − 2k·lo)/(4k))`
(`lv_bound`). The bound is convex in `γ`, so the sum of the lines and of such terms that is at most `0` at the two
ends of an interval is at most `0` on it. The upper end `hi` of a term is what `SieveTypeIIHM.ResBox` gives: the
rest's exponents and the variable's sum to at most `L + 10⁻⁵`.

* `cdiv_sub_ge`: `(A − x)/d ≤ ⌊(A + (d − 1) − x)/d⌋`, the difference truncated.
* `lv_bound`: the bound of a term, in the reals.
* `lvVal_ge`: `lvVal` is above `OFF` plus `S` times each of the bound's four values.
* `conv_le`: a value affine in `γ` that is below two numbers at the ends is below their mean between the ends.
* `lvGv`, `lvG_lt`, `lvGv_ge`: the threshold of a term that applies, and the real one below it.
* `lv_term_le`, `lvU_le`: **the kernel's term bounds the term** between the ends of an interval.
* `tline2`, `addTerms2_sound`: the sum of the terms' bounds.
* `GoalAt2`, `intv2_sound`, `runI2_sound`, `resTM2_sound`, `resT2_sound`: **the test is sound**: `ResBox ghx`.
* `resX_sound`, `resX_hs`, `resX_sound_cells`: **the test in either form is sound**, in the cells' units.

The file imports `SieveResTest.lean`.
-/
import SieveResTest

open Real Finset

noncomputable section

namespace SieveResTest

open SieveTypeIIHM SieveCurveHx

-- the unifier must not compute through the kernel's fixed-point definitions
attribute [local irreducible] lvVal lvG lvU

/-! ### The constants -/

lemma LVE_ge : lvE * (S : ℝ) ≤ LVE := by rw [S_real]; norm_num [lvE, LVE]

lemma E23_ge : (2 / 3 + lvE) * (S : ℝ) ≤ E23 := by rw [S_real]; norm_num [lvE, E23]

lemma C310_le : (C310 : ℝ) ≤ (3 / 10 - lvE) * S := by rw [S_real]; norm_num [lvE, C310]

lemma C15U_ge : (1 / 5 + lvE) * (S : ℝ) ≤ C15U := by rw [S_real]; norm_num [lvE, C15U]

lemma C15D_le : (C15D : ℝ) ≤ (1 / 5 - 4 * lvE) * S := by rw [S_real]; norm_num [lvE, C15D]

lemma C65D_le : (C65D : ℝ) ≤ (6 / 5 - 4 * lvE) * S := by rw [S_real]; norm_num [lvE, C65D]

lemma C43_ge : 4 / 3 * (S : ℝ) ≤ C43 := by rw [S_real]; norm_num [C43]

lemma S_lt_SS : S < SS := by norm_num [S, SS]

/-- The pieces' tops are at most `S`. -/
lemma get_tFT_le : ∀ p < 18, get tFT p ≤ S := by decide +kernel

/-- `(A − x)/d ≤ ⌊(A + (d − 1) − x)/d⌋`, the difference truncated at `0`. -/
lemma cdiv_sub_ge (A x d : ℕ) (hd : 0 < d) : ((A : ℝ) - x) / d ≤ (((A + (d - 1) - x) / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rcases le_or_gt x A with h | h
  · have key := le_cdiv_mul (A - x) d hd
    have e : A + (d - 1) - x = A - x + (d - 1) := by omega
    rw [e, div_le_iff₀ hd']
    have h2 : ((A - x : ℕ) : ℝ) ≤ (((A - x + (d - 1)) / d * d : ℕ) : ℝ) := by exact_mod_cast key
    rw [Nat.cast_sub h] at h2
    push_cast at h2
    exact h2
  · have h1 : (A : ℝ) - x ≤ 0 := by
      have : (A : ℝ) < x := by exact_mod_cast h
      linarith
    exact le_trans (div_nonpos_of_nonpos_of_nonneg h1 hd'.le) (Nat.cast_nonneg _)

/-! ### The bound of a term, in the reals -/

/-- **The large values' bound of a term.** For `k ≥ 1`, `lo ≤ s ≤ hi`, `k·lo ≥ 2/3 + lvE` and
`γ > lvE + max(2k·hi(1/5 + lvE), 1/2 − k·lo(1/5 − 4lvE), 4/3 − k·lo(6/5 − 4lvE))`, the count `γ ≤ lvExp k s (t − τ)`
gives `s(t − 1) − sτ ≤ max(−lo(3/10 − lvE), (lvE − γ)/(2k), (1/2 + lvE − γ − k·lo)/(4k), (4/3 + lvE − γ − 2k·lo)/(4k))`:
the size `t − τ` is below `7/10 + lvE` (the first value), or at most `4/5 − lvE`, where one of the count's three
exponents is at least `γ − lvE` (the other three); above `4/5 − lvE` the count is below `γ`. -/
lemma lv_bound {k : ℕ} (hk : 1 ≤ k) {s t γ lo hi : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ≤ s) (hhi : s ≤ hi)
    (hklo : 2 / 3 + lvE ≤ k * lo)
    (hΓ : lvE + max (2 * k * hi * (1 / 5 + lvE))
      (max (1 / 2 - k * lo * (1 / 5 - 4 * lvE)) (4 / 3 - k * lo * (6 / 5 - 4 * lvE))) < γ)
    (hlv : γ ≤ lvExp k s (t - 1 / 10 ^ 6)) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤
      max (max (-(lo * (3 / 10 - lvE))) ((lvE - γ) / (2 * k)))
        (max ((1 / 2 + lvE - γ - k * lo) / (4 * k)) ((4 / 3 + lvE - γ - 2 * k * lo) / (4 * k))) := by
  have hE : lvE = 1 / 10 ^ 5 := rfl
  have hE0 : (0 : ℝ) < lvE := by rw [hE]; norm_num
  have hE1 : lvE ≤ 1 / 100 := by rw [hE]; norm_num
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hs0 : 0 ≤ s := hlo0.trans hlo
  have hks : (k : ℝ) * lo ≤ k * s := mul_le_mul_of_nonneg_left hlo hk0.le
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t - 1 / 10 ^ 6 := ⟨_, rfl⟩
  rw [← hu] at hlv
  have hX : s * (t - 1) - s * (1 / 10 ^ 6) = s * (u - 1) := by rw [hu]; ring
  rw [hX]
  by_cases hu7 : u < 7 / 10 + lvE
  · -- below the range of sizes
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_left _ _))
    have h1 : u - 1 ≤ -(3 / 10 - lvE) := by linarith
    have h2 : s * (u - 1) ≤ s * (-(3 / 10 - lvE)) := mul_le_mul_of_nonneg_left h1 hs0
    have h3 : lo * (3 / 10 - lvE) ≤ s * (3 / 10 - lvE) := mul_le_mul_of_nonneg_right hlo (by linarith)
    linarith
  · have hu7' : 7 / 10 + lvE ≤ u := not_lt.1 hu7
    have hc : 2 / 3 + lvE ≤ (k : ℝ) * s ∧ 7 / 10 + lvE ≤ u := ⟨hklo.trans hks, hu7'⟩
    unfold lvExp at hlv
    rw [ite_eq_left hc] at hlv
    have hlv' : γ ≤ lvRaw k s (min u (4 / 5 - lvE)) + lvE := hlv.trans (min_le_right _ _)
    have h4k : (0 : ℝ) < 4 * k := by linarith
    have h2k : (0 : ℝ) < 2 * k := by linarith
    by_cases hu8 : u ≤ 4 / 5 - lvE
    · rw [min_eq_left hu8] at hlv'
      unfold lvRaw at hlv'
      have hγ' : γ - lvE ≤ max (2 * ((k : ℝ) * s) * (1 - u))
          (max (1 / 2 + (k : ℝ) * s * (3 - 4 * u)) (4 / 3 + (k : ℝ) * s * (2 - 4 * u))) := by linarith
      rcases le_max_iff.1 hγ' with h | h
      · refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
        rw [le_div_iff₀ h2k]
        linarith
      · rcases le_max_iff.1 h with h | h
        · refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
          rw [le_div_iff₀ h4k]
          linarith
        · refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
          rw [le_div_iff₀ h4k]
          linarith
    · -- above `4/5 − lvE` the count is below `γ`
      exfalso
      have hu8' : 4 / 5 - lvE < u := not_le.1 hu8
      rw [min_eq_right hu8'.le] at hlv'
      unfold lvRaw at hlv'
      have hkhi : (k : ℝ) * s ≤ k * hi := mul_le_mul_of_nonneg_left hhi hk0.le
      have h1 : 2 * ((k : ℝ) * s) * (1 - (4 / 5 - lvE)) ≤ 2 * k * hi * (1 / 5 + lvE) := by
        have := mul_le_mul_of_nonneg_right hkhi (by linarith : (0 : ℝ) ≤ 1 / 5 + lvE)
        linarith
      have h2 : 1 / 2 + (k : ℝ) * s * (3 - 4 * (4 / 5 - lvE)) ≤ 1 / 2 - k * lo * (1 / 5 - 4 * lvE) := by
        have := mul_le_mul_of_nonneg_right hks (by linarith : (0 : ℝ) ≤ 1 / 5 - 4 * lvE)
        linarith
      have h3 : 4 / 3 + (k : ℝ) * s * (2 - 4 * (4 / 5 - lvE)) ≤ 4 / 3 - k * lo * (6 / 5 - 4 * lvE) := by
        have := mul_le_mul_of_nonneg_right hks (by linarith : (0 : ℝ) ≤ 6 / 5 - 4 * lvE)
        linarith
      have h4 := max_le_max h1 (max_le_max h2 h3)
      linarith

/-! ### The kernel's value of the bound -/

/-- **`lvVal` is above the bound's four values**, each with the offset `OFF` and times `S`, at `γ = x/S`. -/
lemma lvVal_ge {lo k x : ℕ} (hk : 1 ≤ k) :
    (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ lvVal lo k x ∧
      (OFF : ℝ) + (lvE * S - x) / (2 * k) ≤ lvVal lo k x ∧
      (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - x) / (4 * k) ≤ lvVal lo k x ∧
      (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - x) / (4 * k) ≤ lvVal lo k x := by
  have hS := S_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2k : 0 < 2 * k := by omega
  have h4k : 0 < 4 * k := by omega
  have h2k' : (0 : ℝ) < 2 * k := by linarith
  have h4k' : (0 : ℝ) < 4 * k := by linarith
  obtain ⟨n0, hn0⟩ : ∃ n : ℕ, n = OFF - mulF lo C310 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ : ∃ n : ℕ, n = (2 * k * OFF + LVE + (2 * k - 1) - x) / (2 * k) := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n : ℕ, n = (4 * k * OFF + (H + LVE) + (4 * k - 1) - (x + k * lo)) / (4 * k) := ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ n : ℕ, n = (4 * k * OFF + (C43 + LVE) + (4 * k - 1) - (x + 2 * k * lo)) / (4 * k) :=
    ⟨_, rfl⟩
  have e : lvVal lo k x = max (max n0 n1) (max n2 n3) := by
    unfold lvVal
    rw [maxN_eq, maxN_eq, maxN_eq, hn0, hn1, hn2, hn3]
    rfl
  have c0 : (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ n0 := by
    rw [hn0]
    have h1 := mulF_le lo C310
    have h2 := C310_le
    have h3 : (lo : ℝ) * C310 / S ≤ lo * (3 / 10 - lvE) := by
      rw [div_le_iff₀ hS]
      have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg lo : (0 : ℝ) ≤ lo)
      linarith
    have h4 := sub_le_tsub' OFF (mulF lo C310)
    linarith
  have c1 : (OFF : ℝ) + (lvE * S - x) / (2 * k) ≤ n1 := by
    rw [hn1]
    have h1 := cdiv_sub_ge (2 * k * OFF + LVE) x (2 * k) h2k
    push_cast at h1
    rw [div_le_iff₀ h2k'] at h1
    have h2 := LVE_ge
    rw [← le_sub_iff_add_le', div_le_iff₀ h2k']
    linarith
  have c2 : (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - x) / (4 * k) ≤ n2 := by
    rw [hn2]
    have h1 := cdiv_sub_ge (4 * k * OFF + (H + LVE)) (x + k * lo) (4 * k) h4k
    push_cast at h1
    rw [div_le_iff₀ h4k'] at h1
    have h2 := LVE_ge
    have h3 := H_real
    rw [← le_sub_iff_add_le', div_le_iff₀ h4k']
    linarith
  have c3 : (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - x) / (4 * k) ≤ n3 := by
    rw [hn3]
    have h1 := cdiv_sub_ge (4 * k * OFF + (C43 + LVE)) (x + 2 * k * lo) (4 * k) h4k
    push_cast at h1
    rw [div_le_iff₀ h4k'] at h1
    have h2 := LVE_ge
    have h3 := C43_ge
    rw [← le_sub_iff_add_le', div_le_iff₀ h4k']
    linarith
  rw [e]
  push_cast
  exact ⟨c0.trans ((le_max_left _ _).trans (le_max_left _ _)),
    c1.trans ((le_max_right _ _).trans (le_max_left _ _)),
    c2.trans ((le_max_left _ _).trans (le_max_right _ _)),
    c3.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- A value `(c − γ)/d` affine in `γ` that is at most `Va − O` at `a` and `Vb − O` at `b` is at most
`(1 − λ)Va + λVb − O` at `γ = (1 − λ)a + λb`, `0 ≤ λ ≤ 1`. -/
lemma conv_le {c d a b Va Vb O lam γ : ℝ} (hd : 0 < d) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hγ : γ = (1 - lam) * a + lam * b) (ha : O + (c - a) / d ≤ Va) (hb : O + (c - b) / d ≤ Vb) :
    (c - γ) / d ≤ (1 - lam) * Va + lam * Vb - O := by
  rw [div_le_iff₀ hd]
  have ha' : c - a ≤ (Va - O) * d := by
    rw [← le_sub_iff_add_le', div_le_iff₀ hd] at ha
    exact ha
  have hb' : c - b ≤ (Vb - O) * d := by
    rw [← le_sub_iff_add_le', div_le_iff₀ hd] at hb
    exact hb
  have e1 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha')
  have e2 := mul_nonneg h0 (sub_nonneg.2 hb')
  rw [hγ]
  nlinarith

/-! ### The threshold -/

/-- The threshold of the large values' term where it applies: `LVE + max(⌈2k·hi(1/5 + lvE)⌉, S/2 − ⌊k·lo(1/5 − 4lvE)⌋,
C43 − ⌊k·lo(6/5 − 4lvE)⌋)`. -/
def lvGv (lo hi k : ℕ) : ℕ :=
  LVE + max (mulC (2 * k * hi) C15U) (max (H - mulF (k * lo) C15D) (C43 - mulF (k * lo) C65D))

attribute [local irreducible] lvGv

lemma lvG_eq (lo hi k : ℕ) :
    lvG lo hi k = cond (Nat.ble 1 k && Nat.ble E23 (Nat.mul k lo)) (lvGv lo hi k) SS := by
  unfold lvG lvGv
  rw [maxN_eq, maxN_eq]
  rfl

lemma cond_lt {c : Bool} {x y a : ℕ} (h : cond c x y < a) (hy : ¬y < a) : c = true ∧ x < a := by
  cases c
  · exact absurd h hy
  · exact ⟨rfl, h⟩

/-- A threshold below `a ≤ S` is a term's that applies: `k ≥ 1`, `k·lo ≥ E23`, and its value. -/
lemma lvG_lt {lo hi k a : ℕ} (ha : a ≤ S) (hg : lvG lo hi k < a) : 1 ≤ k ∧ E23 ≤ k * lo ∧ lvGv lo hi k < a := by
  have h1 : cond (Nat.ble 1 k && Nat.ble E23 (Nat.mul k lo)) (lvGv lo hi k) SS < a := lvG_eq lo hi k ▸ hg
  obtain ⟨hc, hx⟩ := cond_lt h1 (not_lt.2 (ha.trans S_lt_SS.le))
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  exact ⟨hc.1, hc.2, hx⟩

/-- The threshold is above the real one, times `S`. -/
lemma lvGv_ge (lo hi k : ℕ) :
    (lvE + max (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))
        (max (1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE)) (4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE)))) * S ≤
      (lvGv lo hi k : ℕ) := by
  have hS := S_pos
  have e : ((lvGv lo hi k : ℕ) : ℝ) = (LVE : ℝ) + max ((mulC (2 * k * hi) C15U : ℕ) : ℝ)
      (max ((H - mulF (k * lo) C15D : ℕ) : ℝ) ((C43 - mulF (k * lo) C65D : ℕ) : ℝ)) := by
    unfold lvGv
    rw [Nat.cast_add, Nat.cast_max, Nat.cast_max]
  rw [e]
  have m1 : 2 * (k : ℝ) * ((hi : ℝ) / S) * (1 / 5 + lvE) * S ≤ ((mulC (2 * k * hi) C15U : ℕ) : ℝ) := by
    have h1 := mulC_ge (2 * k * hi) C15U
    have h2 := C15U_ge
    push_cast at h1
    have h3 : 2 * (k : ℝ) * ((hi : ℝ) / S) * (1 / 5 + lvE) * S = 2 * k * hi * ((1 / 5 + lvE) * S) / S := by
      field_simp
    rw [h3]
    refine le_trans (div_le_div_of_nonneg_right ?_ hS.le) h1
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hF1 : ((mulF (k * lo) C15D : ℕ) : ℝ) ≤ k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE) * S := by
    have h1 := mulF_le (k * lo) C15D
    have h2 := C15D_le
    push_cast at h1
    have h3 : (k : ℝ) * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE) * S = k * lo * ((1 / 5 - 4 * lvE) * S) / S := by
      field_simp
    rw [h3]
    refine le_trans h1 (div_le_div_of_nonneg_right ?_ hS.le)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hF2 : ((mulF (k * lo) C65D : ℕ) : ℝ) ≤ k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE) * S := by
    have h1 := mulF_le (k * lo) C65D
    have h2 := C65D_le
    push_cast at h1
    have h3 : (k : ℝ) * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE) * S = k * lo * ((6 / 5 - 4 * lvE) * S) / S := by
      field_simp
    rw [h3]
    refine le_trans h1 (div_le_div_of_nonneg_right ?_ hS.le)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have m2 : (1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE)) * S ≤ ((H - mulF (k * lo) C15D : ℕ) : ℝ) := by
    have h1 := sub_le_tsub' H (mulF (k * lo) C15D)
    have h2 := H_real
    linarith
  have m3 : (4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE)) * S ≤ ((C43 - mulF (k * lo) C65D : ℕ) : ℝ) := by
    have h1 := sub_le_tsub' C43 (mulF (k * lo) C65D)
    have h2 := C43_ge
    linarith
  have hL := LVE_ge
  rw [add_mul, max_mul_of_nonneg _ _ hS.le, max_mul_of_nonneg _ _ hS.le]
  exact add_le_add hL (max_le_max m1 (max_le_max m2 m3))

/-! ### The kernel's term -/

/-- The bound of a term between the ends of an interval, from four values at each end: for `lo/S ≤ s ≤ hi/S`,
`k ≥ 1`, `k·lo ≥ E23`, the threshold `g` with the real one times `S` at most `g < a`, and
`γ = (1 − λ)a/S + λb/S`, if `Va` and `Vb` are above the bound's four values at `a` and at `b` (as `lvVal_ge` gives
them), `s(t − 1) − sτ ≤ ((1 − λ)Va + λVb − OFF)/S`. -/
lemma lv_term_le {lo hi k a b g : ℕ} {s t γ lam Va Vb : ℝ} (hk : 1 ≤ k) (hE23 : E23 ≤ k * lo)
    (hgv : (lvE + max (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))
        (max (1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE)) (4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE)))) * S ≤
      (g : ℝ))
    (hga : g < a) (hab : a ≤ b) (hs : (lo : ℝ) / S ≤ s) (hhi : s ≤ (hi : ℝ) / S)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ = (1 - lam) * (a / S) + lam * (b / S))
    (hlv : γ ≤ lvExp k s (t - 1 / 10 ^ 6))
    (f0a : (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ Va) (f1a : (OFF : ℝ) + (lvE * S - a) / (2 * k) ≤ Va)
    (f2a : (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - a) / (4 * k) ≤ Va)
    (f3a : (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - a) / (4 * k) ≤ Va)
    (f0b : (OFF : ℝ) - lo * (3 / 10 - lvE) ≤ Vb) (f1b : (OFF : ℝ) + (lvE * S - b) / (2 * k) ≤ Vb)
    (f2b : (OFF : ℝ) + ((1 / 2 + lvE) * S - k * lo - b) / (4 * k) ≤ Vb)
    (f3b : (OFF : ℝ) + ((4 / 3 + lvE) * S - 2 * k * lo - b) / (4 * k) ≤ Vb) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤ ((1 - lam) * Va + lam * Vb - OFF) / S := by
  have hS := S_pos
  have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
  have h1lam : 0 ≤ 1 - lam := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  -- `γ ≥ a/S`, and `γ·S = (1 − λ)a + λb`
  have hγS : γ * S = (1 - lam) * a + lam * b := by
    rw [hγ]; field_simp
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hγa : (a : ℝ) ≤ γ * S := by
    rw [hγS]
    have := mul_nonneg hlam0 (sub_nonneg.2 habr)
    linarith
  -- `k·lo ≥ 2/3 + lvE`
  have hklo : 2 / 3 + lvE ≤ k * ((lo : ℝ) / S) := by
    have h1 := E23_ge
    have h2 : (E23 : ℝ) ≤ k * lo := by exact_mod_cast hE23
    rw [mul_div_assoc', le_div_iff₀ hS]
    linarith
  -- the threshold in the reals
  have hΓ : lvE + max (2 * k * ((hi : ℝ) / S) * (1 / 5 + lvE))
      (max (1 / 2 - k * ((lo : ℝ) / S) * (1 / 5 - 4 * lvE)) (4 / 3 - k * ((lo : ℝ) / S) * (6 / 5 - 4 * lvE))) <
      γ := by
    have h2 : (g : ℝ) < a := by exact_mod_cast hga
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hgv (lt_of_lt_of_le h2 hγa)) hS.le
  -- the bound in the reals, then its values at the ends
  have hbd := lv_bound hk hlo0 hs hhi hklo hΓ hlv
  refine hbd.trans ?_
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

/-- `lvU` where the threshold is below `a`. -/
lemma lvU_of_lt {lo k g a x : ℕ} (hg : g < a) : lvU lo k g a x = lvVal lo k x := by
  have hb : Nat.blt g a = true := by rw [Nat.blt_eq]; exact hg
  unfold lvU
  rw [hb, Bool.cond_true]

/-- `lvU` where the threshold is not below `a`. -/
lemma lvU_of_not_lt {lo k g a x : ℕ} (hg : ¬g < a) : lvU lo k g a x = OFF := by
  have hb : Nat.blt g a = false := by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hg
  unfold lvU
  rw [hb, Bool.cond_false]

/-- **The kernel's term bounds the term** between the ends: for a term with `lo/S ≤ s ≤ (ub + lo)/S`, a power `k`
and `γ = (1 − λ)a/S + λb/S`, `a ≤ b ≤ S`, the class's conditions give
`s(t − 1) − sτ ≤ ((1 − λ)·lvU(a) + λ·lvU(b) − OFF)/S`, `lvU` at the threshold `lvG lo (ub + lo) k`: where the
threshold is below `a`, by `lv_term_le` with `lvVal_ge`; elsewhere the bound is `0`. -/
lemma lvU_le {lo ub k a b : ℕ} {s t β γ lam : ℝ} (hab : a ≤ b) (hbS : b ≤ S) (hs : (lo : ℝ) / S ≤ s)
    (hhi : s ≤ ((ub + lo : ℕ) : ℝ) / S) (ht : t ≤ β + 4 / 10 ^ 6) (hβ : β ≤ 11 / 12)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ = (1 - lam) * (a / S) + lam * (b / S))
    (hlv : ∀ k : ℕ, 1 ≤ k → γ ≤ lvExp k s (t - 1 / 10 ^ 6)) :
    s * (t - 1) - s * (1 / 10 ^ 6) ≤
      ((1 - lam) * (lvU lo k (lvG lo (ub + lo) k) a a : ℕ) + lam * (lvU lo k (lvG lo (ub + lo) k) a b : ℕ) - OFF) /
        S := by
  have hS := S_pos
  by_cases hg : lvG lo (ub + lo) k < a
  · rw [lvU_of_lt hg, lvU_of_lt hg]
    obtain ⟨hk, hE23, hgv⟩ := lvG_lt (hab.trans hbS) hg
    obtain ⟨f0a, f1a, f2a, f3a⟩ := lvVal_ge (lo := lo) (x := a) hk
    obtain ⟨f0b, f1b, f2b, f3b⟩ := lvVal_ge (lo := lo) (x := b) hk
    exact lv_term_le hk hE23 (lvGv_ge lo (ub + lo) k) hgv hab hs hhi hlam0 hlam1 hγ (hlv k hk) f0a f1a f2a f3a
      f0b f1b f2b f3b
  · -- the term does not apply: the bound `0`
    rw [lvU_of_not_lt hg, lvU_of_not_lt hg]
    have hlo0 : (0 : ℝ) ≤ lo / S := div_nonneg (Nat.cast_nonneg _) hS.le
    have hs0 : 0 ≤ s := hlo0.trans hs
    have h1 : s * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (by linarith)
    have h2 : 0 ≤ s * (1 / 10 ^ 6) := by positivity
    have e : ((1 - lam) * (OFF : ℝ) + lam * (OFF : ℝ) - OFF) / S = 0 := by ring
    rw [e]
    linarith

/-! ### The terms' sum -/

/-- The value of the term's bound `c` between the ends of `[a, b]`, at `γ = (1 − λ)a/S + λb/S`: the lines of
`tline` for `c ≤ 3`; the large values' term of `k1` (`4`) or `k2` (above), the mean of its values at the ends. -/
def tline2 (v : Tv) (dS iax a b c : ℕ) (lam γ : ℝ) : ℝ :=
  if c ≤ 3 then tline v.t dS iax c γ
  else if c = 4 then
    ((1 - lam) * (lvU v.t.lo v.k1 v.g1 a a : ℕ) + lam * (lvU v.t.lo v.k1 v.g1 a b : ℕ) - OFF) / S
  else ((1 - lam) * (lvU v.t.lo v.k2 v.g2 a a : ℕ) + lam * (lvU v.t.lo v.k2 v.g2 a b : ℕ) - OFF) / S

lemma tline2_le3 (v : Tv) (dS iax a b : ℕ) {c : ℕ} (hc : c ≤ 3) (lam γ : ℝ) :
    tline2 v dS iax a b c lam γ = tline v.t dS iax c γ := by
  unfold tline2
  rw [ite_eq_left hc]

lemma tline2_4 (v : Tv) (dS iax a b : ℕ) (lam γ : ℝ) :
    tline2 v dS iax a b 4 lam γ =
      ((1 - lam) * (lvU v.t.lo v.k1 v.g1 a a : ℕ) + lam * (lvU v.t.lo v.k1 v.g1 a b : ℕ) - OFF) / S := by
  unfold tline2
  rw [ite_eq_right (by norm_num), ite_eq_left rfl]

lemma tline2_ge5 (v : Tv) (dS iax a b : ℕ) {c : ℕ} (hc : 5 ≤ c) (lam γ : ℝ) :
    tline2 v dS iax a b c lam γ =
      ((1 - lam) * (lvU v.t.lo v.k2 v.g2 a a : ℕ) + lam * (lvU v.t.lo v.k2 v.g2 a b : ℕ) - OFF) / S := by
  unfold tline2
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma beq_false {c n : ℕ} (h : c ≠ n) : Nat.beq c n = false := by
  rw [Bool.eq_false_iff]
  exact fun hb => h (Nat.eq_of_beq_eq_true hb)

set_option maxHeartbeats 1600000 in
/-- **The terms' sum**: `addTerms2` adds to `(P0, N0, N1, VA, VB)` bounds of the terms `v i` (each below every bound
of its term), at `γ = (1 − λ)a/S + λb/S`: the lines, and the mean `(1 − λ)VA + λVB` of the large values' terms. -/
lemma addTerms2_sound (dS iax a b : ℕ) (lam γ : ℝ) : ∀ (vs : List Tv) (h p0 n0 n1 va vb : ℕ) (v : ℕ → ℝ),
    (∀ i (hi : i < vs.length), ∀ c, v i ≤ tline2 vs[i] dS iax a b c lam γ) →
    (∑ i ∈ range vs.length, v i) + ((p0 : ℝ) + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S ≤
      (((addTerms2 dS iax a b vs h p0 n0 n1 va vb).1 : ℝ) +
          ((1 - lam) * (addTerms2 dS iax a b vs h p0 n0 n1 va vb).2.2.2.1 +
            lam * (addTerms2 dS iax a b vs h p0 n0 n1 va vb).2.2.2.2) -
          (addTerms2 dS iax a b vs h p0 n0 n1 va vb).2.1 -
          (addTerms2 dS iax a b vs h p0 n0 n1 va vb).2.2.1 * γ) / S
  | [], h, p0, n0, n1, va, vb, v, _ => by simp [addTerms2]
  | t :: ts, h, p0, n0, n1, va, vb, v, hv => by
    have hv0 := hv 0 (by simp)
    have hv' : ∀ i (hi : i < ts.length), ∀ c, v (i + 1) ≤ tline2 ts[i] dS iax a b c lam γ := fun i hi c =>
      hv (i + 1) (by simp; omega) c
    rw [List.length_cons, Finset.sum_range_succ']
    have hS := S_pos
    simp only [List.getElem_cons_zero] at hv0
    have hc : Nat.land h 7 < 8 := Nat.lt_succ_of_le (Nat.and_le_right)
    simp only [addTerms2]
    generalize Nat.land h 7 = c at hc
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ 5 ≤ c) with rfl | rfl | rfl | rfl | rfl | h5
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) (Nat.add p0 t.t.a0) n0
        (Nat.add n1 t.t.a1) va vb (fun i => v (i + 1)) hv'
      have h0 := hv0 0
      rw [tline2_le3 _ _ _ _ _ (by norm_num)] at h0
      simp only [tline, ite_true] at h0
      simp only [show Nat.beq 0 0 = true from rfl, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + t.t.a0 + ((1 - lam) * va + lam * vb) - n0 - (n1 + t.t.a1) * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S + (t.t.a0 - t.t.a1 * γ) / S := by ring
      rw [e] at ih
      linarith
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) p0 n0 (Nat.add n1 t.t.b1) va vb
        (fun i => v (i + 1)) hv'
      have h0 := hv0 1
      rw [tline2_le3 _ _ _ _ _ (by norm_num)] at h0
      simp only [tline, one_ne_zero, ite_false, ite_true] at h0
      simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, Bool.cond_false,
        Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + ((1 - lam) * va + lam * vb) - n0 - (n1 + t.t.b1) * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S + -(t.t.b1 * γ) / S := by ring
      rw [e] at ih
      linarith
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) p0 (Nat.add n0 (mulF t.t.lo dS)) n1
        va vb (fun i => v (i + 1)) hv'
      have h0 := hv0 2
      rw [tline2_le3 _ _ _ _ _ (by norm_num)] at h0
      simp only [tline, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ite_false, ite_true] at h0
      simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
        show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + ((1 - lam) * va + lam * vb) - (n0 + mulF t.t.lo dS) - n1 * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S + -(mulF t.t.lo dS : ℝ) / S := by ring
      rw [e] at ih
      linarith
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) (Nat.add p0 t.t.lw) n0
        (Nat.add n1 (mulF t.t.lo iax)) va vb (fun i => v (i + 1)) hv'
      have h0 := hv0 3
      rw [tline2_le3 _ _ _ _ _ (by norm_num)] at h0
      simp only [tline, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
        ite_false] at h0
      simp only [show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
        show Nat.beq 3 2 = false from rfl, show Nat.beq 3 3 = true from rfl, Bool.cond_false, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + t.t.lw + ((1 - lam) * va + lam * vb) - n0 - (n1 + mulF t.t.lo iax) * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S + (t.t.lw - mulF t.t.lo iax * γ) / S := by ring
      rw [e] at ih
      linarith
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) p0 (Nat.add n0 OFF) n1
        (Nat.add va (lvU t.t.lo t.k1 t.g1 a a)) (Nat.add vb (lvU t.t.lo t.k1 t.g1 a b)) (fun i => v (i + 1)) hv'
      have h0 := hv0 4
      rw [tline2_4] at h0
      simp only [show Nat.beq 4 0 = false from rfl, show Nat.beq 4 1 = false from rfl,
        show Nat.beq 4 2 = false from rfl, show Nat.beq 4 3 = false from rfl, show Nat.beq 4 4 = true from rfl,
        Bool.cond_false, Bool.cond_true]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + ((1 - lam) * (va + (lvU t.t.lo t.k1 t.g1 a a : ℕ)) +
            lam * (vb + (lvU t.t.lo t.k1 t.g1 a b : ℕ))) - (n0 + OFF) - n1 * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S +
            ((1 - lam) * (lvU t.t.lo t.k1 t.g1 a a : ℕ) + lam * (lvU t.t.lo t.k1 t.g1 a b : ℕ) - OFF) / S := by
        ring
      rw [e] at ih
      linarith
    · have ih := addTerms2_sound dS iax a b lam γ ts (Nat.shiftRight h 3) p0 (Nat.add n0 OFF) n1
        (Nat.add va (lvU t.t.lo t.k2 t.g2 a a)) (Nat.add vb (lvU t.t.lo t.k2 t.g2 a b)) (fun i => v (i + 1)) hv'
      have h0 := hv0 c
      rw [tline2_ge5 _ _ _ _ _ h5] at h0
      simp only [beq_false (show c ≠ 0 by omega), beq_false (show c ≠ 1 by omega),
        beq_false (show c ≠ 2 by omega), beq_false (show c ≠ 3 by omega), beq_false (show c ≠ 4 by omega),
        Bool.cond_false]
      simp only [Nat.add_eq] at ih ⊢
      push_cast at ih ⊢
      have e : ((p0 : ℝ) + ((1 - lam) * (va + (lvU t.t.lo t.k2 t.g2 a a : ℕ)) +
            lam * (vb + (lvU t.t.lo t.k2 t.g2 a b : ℕ))) - (n0 + OFF) - n1 * γ) / S =
          (p0 + ((1 - lam) * va + lam * vb) - n0 - n1 * γ) / S +
            ((1 - lam) * (lvU t.t.lo t.k2 t.g2 a a : ℕ) + lam * (lvU t.t.lo t.k2 t.g2 a b : ℕ) - OFF) / S := by
        ring
      rw [e] at ih
      linarith

/-! ### An interval -/

lemma mkTv_t (ub lo : ℕ) : (mkTv ub lo).t = mkTm lo := rfl

lemma mkTm_lo (lo : ℕ) : (mkTm lo).lo = lo := rfl

lemma mkTv_k1 (ub lo : ℕ) : (mkTv ub lo).k1 = (S + (lo - 1)) / lo - 1 := rfl

lemma mkTv_g1 (ub lo : ℕ) : (mkTv ub lo).g1 = lvG lo (ub + lo) ((S + (lo - 1)) / lo - 1) := rfl

lemma mkTv_k2 (ub lo : ℕ) : (mkTv ub lo).k2 = (S + (lo - 1)) / lo - 2 := rfl

lemma mkTv_g2 (ub lo : ℕ) : (mkTv ub lo).g2 = lvG lo (ub + lo) ((S + (lo - 1)) / lo - 2) := rfl

/-- **The bound at `γ`, with the large values**: `GoalAt` with the counts by large values and the upper ends
`s j ≤ (ub + los_j)/S` among the conditions. -/
def GoalAt2 (L : ℝ) (los : List ℕ) (mlo ub : ℕ) (γ : ℝ) : Prop :=
  ∀ (β m : ℝ) (s t : ℕ → ℝ), 1 / 2 ≤ β → β ≤ 11 / 12 → γ ≤ ghx β → (∀ j < los.length, t j ≤ β + 4 / 10 ^ 6) →
    (∀ j < los.length, ∀ k : ℕ, 1 ≤ k → γ ≤ momExp k (s j) (t j - 1 / 10 ^ 6)) →
    (∀ j < los.length, ∀ k : ℕ, 1 ≤ k → γ ≤ lvExp k (s j) (t j - 1 / 10 ^ 6)) → (mlo : ℝ) / S ≤ m →
    (∀ j (hj : j < los.length), (los[j] : ℝ) / S ≤ s j) →
    (∀ j (hj : j < los.length), s j ≤ ((ub + los[j] : ℕ) : ℝ) / S) → ∑ j ∈ range los.length, s j ≤ L →
    ∑ j ∈ range los.length, s j * (t j - 1) + γ / 2 + clampR γ m ≤ -(1 / 25000)

/-- A point of an interval is a mean of its ends. -/
lemma exists_lam {A B γ : ℝ} (h1 : A ≤ γ) (h2 : γ ≤ B) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ γ = (1 - lam) * A + lam * B := by
  rcases eq_or_lt_of_le (h1.trans h2) with hAB | hAB
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    have : γ = A := le_antisymm (hAB ▸ h2) h1
    rw [this]; ring
  · have hd : 0 < B - A := by linarith
    refine ⟨(γ - A) / (B - A), div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith), ?_⟩
    have h : (γ - A) / (B - A) * (B - A) = γ - A := div_mul_cancel₀ _ hd.ne'
    linear_combination (-1 : ℝ) * h

/-- A sum of a line and of numbers `VA`, `VB` at the ends that is at most `0` at both ends is at most `0` at a mean
of the ends, with the mean of the numbers. -/
lemma line_mean {P VA VB p1 N0 N1 A B lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (ha : P + VA + p1 * A - N0 - N1 * A ≤ 0) (hb : P + VB + p1 * B - N0 - N1 * B ≤ 0) :
    P + ((1 - lam) * VA + lam * VB) + p1 * ((1 - lam) * A + lam * B) - N0 - N1 * ((1 - lam) * A + lam * B) ≤ 0 := by
  have e1 := mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 ha)
  have e2 := mul_nonneg h0 (neg_nonneg.2 hb)
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **One interval is sound**: `intv2` on `[a, b]` with `a` in the piece `pa` gives `b`'s piece and the bound at
every `γ ∈ [a/S, b/S]`: the lines as in `intv_sound`, the large values' terms by their convexity. -/
lemma intv2_sound {L : ℝ} {los : List ℕ} {mlo ub c1 yuP yuN ydP ydN ltm a pa r : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (h : intv2 (los.map (mkTv ub)) c1 yuP yuN ydP ydN ltm a pa r = true) (hpa : pa ≤ 17)
    (hlo : pa = 0 ∨ tops (pa - 1) * S < a) (hhi : pa ≤ 16 → (a : ℝ) ≤ tops pa * S) :
    pieceOf (bOf r) ≤ 17 ∧ (pieceOf (bOf r) = 0 ∨ tops (pieceOf (bOf r) - 1) * S < bOf r) ∧
      (pieceOf (bOf r) ≤ 16 → (bOf r : ℝ) ≤ tops (pieceOf (bOf r)) * S) ∧ a ≤ bOf r ∧
      ∀ γ, (a : ℝ) / S ≤ γ → γ ≤ (bOf r : ℝ) / S → GoalAt2 L los mlo ub γ := by
  have hS := S_pos
  unfold intv2 at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h17, hlt⟩, hle⟩, hab⟩, hchk⟩ := h
  generalize hbdef : bOf r = b at h17 hlt hle hab hchk ⊢
  generalize hpbdef : pieceOf b = pb at h17 hlt hle hchk ⊢
  -- the bounds that the test picks at the midpoint: any choice is a bound
  generalize hccdef : pickC c1 yuP yuN ydP ydN a b (Nat.shiftRight (Nat.add a b) 1) = cc at hchk
  generalize hchdef : chMid2 (maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC)) (minN (get tIA pa) (get tIA pb))
    a (Nat.shiftRight (Nat.add a b) 1) (los.map (mkTv ub)) = ch at hchk
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

/-! ### The intervals and the test -/

lemma runI2_zero (vs : List Tv) (w c1 yuP yuN ydP ydN ltm a pa h : ℕ) :
    runI2 vs w c1 yuP yuN ydP ydN ltm 0 a pa h = Nat.beq a S := rfl

lemma runI2_succ (vs : List Tv) (w c1 yuP yuN ydP ydN ltm k a pa h : ℕ) :
    runI2 vs w c1 yuP yuN ydP ydN ltm (k + 1) a pa h =
      (intv2 vs c1 yuP yuN ydP ydN ltm a pa (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) &&
        runI2 vs w c1 yuP yuN ydP ydN ltm k (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))
          (pieceOf (bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))) (Nat.shiftRight h w)) := rfl

/-- **The intervals are sound**: `runI2` from `a` in the piece `pa` gives the bound at every `γ ∈ (a/S, 1]`. -/
lemma runI2_sound {L : ℝ} {los : List ℕ} {mlo ub c1 yuP yuN ydP ydN ltm w : ℕ}
    (hok : ClampOK mlo c1 yuP yuN ydP ydN) (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S) :
    ∀ (k a pa h : ℕ), runI2 (los.map (mkTv ub)) w c1 yuP yuN ydP ydN ltm k a pa h = true → pa ≤ 17 →
      (pa = 0 ∨ tops (pa - 1) * S < a) → (pa ≤ 16 → (a : ℝ) ≤ tops pa * S) →
      ∀ γ, (a : ℝ) / S < γ → γ ≤ 1 → GoalAt2 L los mlo ub γ
  | 0, a, pa, h, hr, _, _, _, γ, hγa, hγ1 => by
    rw [runI2_zero] at hr
    have ha : a = S := Nat.eq_of_beq_eq_true hr
    subst ha
    rw [div_self S_pos.ne'] at hγa
    linarith
  | k + 1, a, pa, h, hr, hpa, hlo, hhi, γ, hγa, hγ1 => by
    rw [runI2_succ] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hi, hr⟩ := hr
    obtain ⟨h17, hblo, hbhi, hab, hgoal⟩ := intv2_sound hok hltm hi hpa hlo hhi
    rcases le_or_gt γ ((bOf (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)) : ℕ) / S) with hγb | hγb
    · exact hgoal γ hγa.le hγb
    · exact runI2_sound hok hltm k _ _ _ hr h17 hblo hbhi γ hγb hγ1

/-- The half-plane's sum of the terms with the large values' constants is `hpSum`'s. -/
lemma hpSum2_eq (ub : ℕ) : ∀ los : List ℕ, hpSum2 (los.map (mkTv ub)) = hpSum (los.map mkTm)
  | [] => rfl
  | lo :: los => by
    rw [List.map_cons, List.map_cons]
    show Nat.add (mulF (mkTv ub lo).t.lo HP) (hpSum2 (los.map (mkTv ub))) =
      Nat.add (mulF (mkTm lo).lo HP) (hpSum (los.map mkTm))
    rw [hpSum2_eq ub los, mkTv_t]

/-- **The test with `m` and `Lτ + MARG` given is sound**: the bound at every `γ`. -/
theorem resTM2_sound {L : ℝ} (hL : 0 ≤ L) {los : List ℕ} {mlo ub ltm k h : ℕ}
    (hltm : L * (1 / 10 ^ 6) + 1 / 25000 ≤ (ltm : ℝ) / S)
    (hT : resTM2 (los.map (mkTv ub)) mlo ltm k h = true) : ∀ γ, GoalAt2 L los mlo ub γ := by
  have hS := S_pos
  unfold resTM2 at hT
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
    exact runI2_sound hok hltm k 0 0 h hrun (by norm_num) (Or.inl rfl)
      (fun _ => by rw [Nat.cast_zero]; exact mul_nonneg (tops_pos 0 (by norm_num)).le hS.le) γ
      (by rw [Nat.cast_zero, zero_div]; exact hγ0) hγ1 β m s t h1 h2 hγ ht hk hlv hm hs hup hsum

/-! ### The upper ends -/

/-- The sum of a list, in the reals. -/
lemma sum_getD_eq : ∀ los : List ℕ, ∑ j ∈ range los.length, ((los.getD j 0 : ℕ) : ℝ) = (sumN los : ℕ)
  | [] => by simp [sumN]
  | x :: xs => by
    rw [List.length_cons, Finset.sum_range_succ']
    have e : sumN (x :: xs) = x + sumN xs := rfl
    rw [e]
    push_cast
    rw [← sum_getD_eq xs]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- `⌊(Lnum·10⁵ + Lden)S/(Lden·10⁵)⌋ + 1 ≥ (L + 10⁻⁵)S`. -/
lemma ls5_ok {Lnum Lden : ℕ} (hLd : 0 < Lden) :
    ((Lnum : ℝ) / Lden + 1 / 10 ^ 5) * S ≤ (((Lnum * 100000 + Lden) * S / (Lden * 100000) + 1 : ℕ) : ℝ) := by
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have hd : 0 < Lden * 100000 := by positivity
  have h1 := Nat.div_add_mod ((Lnum * 100000 + Lden) * S) (Lden * 100000)
  have h2 := Nat.mod_lt ((Lnum * 100000 + Lden) * S) hd
  have h3 : (Lnum * 100000 + Lden) * S < ((Lnum * 100000 + Lden) * S / (Lden * 100000) + 1) * (Lden * 100000) := by
    calc (Lnum * 100000 + Lden) * S
        = Lden * 100000 * ((Lnum * 100000 + Lden) * S / (Lden * 100000)) +
            (Lnum * 100000 + Lden) * S % (Lden * 100000) := h1.symm
      _ < Lden * 100000 * ((Lnum * 100000 + Lden) * S / (Lden * 100000)) + Lden * 100000 := by omega
      _ = ((Lnum * 100000 + Lden) * S / (Lden * 100000) + 1) * (Lden * 100000) := by ring
  have h4 : (((Lnum * 100000 + Lden) * S : ℕ) : ℝ) <
      ((((Lnum * 100000 + Lden) * S / (Lden * 100000) + 1) * (Lden * 100000) : ℕ) : ℝ) := by exact_mod_cast h3
  push_cast at h4 ⊢
  have e : ((Lnum : ℝ) / Lden + 1 / 10 ^ 5) * S = ((Lnum : ℝ) * 100000 + Lden) * S / (Lden * 100000) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  exact h4.le

/-- **The upper ends of a box**: where the rest's exponents `s j ≥ los_j/S` and the variable's `m ≥ mlo/S` sum to at
most `L + 10⁻⁵ ≤ ls/S`, each `s j` is at most `(ls − (mlo + Σ_i los_i) + los_j)/S`. -/
lemma upper_end {los : List ℕ} {mlo ls : ℕ} {L m : ℝ} {s : ℕ → ℝ} (hls : (L + 1 / 10 ^ 5) * S ≤ ls)
    (hm : (mlo : ℝ) / S ≤ m) (hs : ∀ j (hj : j < los.length), (los[j] : ℝ) / S ≤ s j)
    (hsum2 : ∑ j ∈ range los.length, s j + m ≤ L + 1 / 10 ^ 5) :
    ∀ j (hj : j < los.length), s j ≤ ((ls - (mlo + sumN los) + los[j] : ℕ) : ℝ) / S := by
  have hS := S_pos
  intro j hj
  -- `s j − los_j/S ≤ Σ_i (s i − los_i/S) = Σ s − (Σ los)/S`
  have hnn : ∀ i ∈ range los.length, 0 ≤ s i - ((los.getD i 0 : ℕ) : ℝ) / S := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [List.getD_eq_getElem _ _ hi']
    linarith [hs i hi']
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.2 hj)
  rw [List.getD_eq_getElem _ _ hj, Finset.sum_sub_distrib, ← Finset.sum_div, sum_getD_eq] at h1
  have h2 := sub_le_tsub' ls (mlo + sumN los)
  push_cast at h2 ⊢
  rw [le_div_iff₀ hS]
  have h3 : (los[j] : ℝ) / S * S = los[j] := div_mul_cancel₀ _ hS.ne'
  have h4 : (sumN los : ℝ) / S * S = sumN los := div_mul_cancel₀ _ hS.ne'
  have h5 : (mlo : ℝ) / S * S = mlo := div_mul_cancel₀ _ hS.ne'
  have h6 : (s j - (los[j] : ℝ) / S) * S ≤ (∑ i ∈ range los.length, s i - (sumN los : ℝ) / S) * S :=
    mul_le_mul_of_nonneg_right h1 hS.le
  have h7 : (∑ i ∈ range los.length, s i + m) * S ≤ (L + 1 / 10 ^ 5) * S := mul_le_mul_of_nonneg_right hsum2 hS.le
  have h8 : (mlo : ℝ) / S * S ≤ m * S := mul_le_mul_of_nonneg_right hm hS.le
  nlinarith

/-! ### The test -/

/-- **The test with the large values' terms is sound**: `resT2` gives `ResBox ghx L K m lo` at `L = Lnum/Lden`,
with `resT_sound`'s `m` and `lo_j`. -/
theorem resT2_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resT2 Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  unfold resT2 at hT
  dsimp only at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨_, hT⟩ := hT
  have hL : (0 : ℝ) ≤ (Lnum : ℝ) / Lden := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hgoal := resTM2_sound hL (ltm_ok hLd) hT
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

/-- `resT2` passes only with `hs + 1 < DEN`. -/
theorem resT2_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resT2 Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  unfold resT2 at hT
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hT
  exact hT.1

/-- `resX` is `resT2` at `k = 0` and `resT` elsewhere. -/
lemma resX_cases {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resX Lnum Lden cs hs k h = true) :
    resT2 Lnum Lden cs hs (Nat.land h 15) (Nat.shiftRight h 4) = true ∨ resT Lnum Lden cs hs k h = true := by
  unfold resX at hT
  cases hk : Nat.beq k 0 with
  | true =>
    rw [hk, Bool.cond_true] at hT
    exact Or.inl hT
  | false =>
    rw [hk, Bool.cond_false] at hT
    exact Or.inr hT

/-- **The test in either form is sound**: `resX` gives `ResBox ghx L K m lo`, as `resT_sound`. -/
theorem resX_sound {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hT : resX Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      (((Lnum * (DEN - hs - 1) * S / (Lden * DEN) : ℕ) : ℝ) / S)
      (fun j => ((loOf Lnum Lden (cs.getD j 0) : ℕ) : ℝ) / S) := by
  rcases resX_cases hT with h2 | h1
  · exact resT2_sound hLd h2
  · exact resT_sound hLd h1

/-- `resX` passes only with `hs + 1 < DEN`. -/
theorem resX_hs {Lnum Lden : ℕ} {cs : List ℕ} {hs k h : ℕ} (hT : resX Lnum Lden cs hs k h = true) :
    hs + 1 < DEN := by
  rcases resX_cases hT with h2 | h1
  · exact resT2_hs h2
  · exact resT_hs h1

/-- **The test in either form is sound, in the cells' units**: with `κ = L/DEN`, `L = Lnum/Lden`, cells `c_j ≥ 1`
and `hs + 1 < DEN`, `resX` gives `ResBox ghx L K (L − κ·hs − κ) (κ·c_j − κ)`. -/
theorem resX_sound_cells {Lnum Lden : ℕ} (hLd : 0 < Lden) {cs : List ℕ} {hs k h : ℕ}
    (hc : ∀ c ∈ cs, 1 ≤ c) (hT : resX Lnum Lden cs hs k h = true) :
    ResBox ghx ((Lnum : ℝ) / Lden) cs.length
      ((Lnum : ℝ) / Lden - (Lnum : ℝ) / Lden / DEN * hs - (Lnum : ℝ) / Lden / DEN)
      (fun j => (Lnum : ℝ) / Lden / DEN * (cs.getD j 0) - (Lnum : ℝ) / Lden / DEN) := by
  have hS := S_pos
  have hD : (0 : ℝ) < DEN := by norm_num [DEN]
  have hLd' : (0 : ℝ) < Lden := by exact_mod_cast hLd
  have hhs : hs + 1 < DEN := resX_hs hT
  refine resBox_mono (resX_sound hLd hT) ?_ ?_
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

#print axioms SieveResTest.lvU_le
#print axioms SieveResTest.resX_sound_cells
