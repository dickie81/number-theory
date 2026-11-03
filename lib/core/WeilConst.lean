import Mathlib
import WeilHead

/-! # Rigorous enclosures of `β*` and of the pole values `pₙ` (kernel-checked over `ℚ`)

* `beta_enc`: `|β* − b̂| ≤ 10⁻¹²`, from Mathlib's 20-digit `π` bounds, the `log(1 − x)` series bound
  `Real.abs_log_sub_add_sum_range_le`, and rational `√2` bounds.
* `pole_enc`: `|p_{2i+par} − p̂ᵢ| ≤ 10⁻¹²` for `i < 28`, from the exact moments
  `∫_{−1}^{1} t^{2k}(1−t²)ⁿ dt` (integration by parts) and the cosh Taylor bound from `Real.exp_bound`.
-/

namespace WeilConst

open Real Finset WeilTailB WeilHead

/-! ## Rational helpers -/

def lsum (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

lemma lsum_cast (n : ℕ) (f : ℕ → ℚ) : ((lsum n f : ℚ) : ℝ) = ∑ k ∈ range n, (f k : ℝ) := cast_lsum n f

/-- Partial sum `Σ_{i<n} x^{i+1}/(i+1)` and remainder `|x|^{n+1}/(1−|x|)` of `−log(1−x)`. -/
def Ls (x : ℚ) (n : ℕ) : ℚ := lsum n fun i => x ^ (i + 1) / (i + 1)
def Lr (x : ℚ) (n : ℕ) : ℚ := |x| ^ (n + 1) / (1 - |x|)

lemma log_enc (x : ℚ) (hx : |x| < 1) (n : ℕ) :
    |((Ls x n : ℚ) : ℝ) + Real.log (1 - (x:ℝ))| ≤ ((Lr x n : ℚ) : ℝ) := by
  have hx' : |(x:ℝ)| < 1 := by exact_mod_cast hx
  have h := Real.abs_log_sub_add_sum_range_le hx' n
  unfold Ls Lr; rw [lsum_cast]; push_cast; convert h using 3

/-! ## `β*` -/

def plo : ℚ := 314159265358979323846 / 10 ^ 20
def phi : ℚ := 314159265358979323847 / 10 ^ 20
def s2lo : ℚ := 14142135623730950 / 10 ^ 16
def s2hi : ℚ := 14142135623730951 / 10 ^ 16
def xa : ℚ := 1 - 15 / (4 * phi)
def xb : ℚ := 1 - 15 / (4 * plo)
def L2lo : ℚ := Ls (1/2) 50 - Lr (1/2) 50
def L2hi : ℚ := Ls (1/2) 50 + Lr (1/2) 50
def βlo : ℚ := 2 * L2lo - (Ls xa 25 + Lr xa 25) - 1/30 - s2hi * L2hi
def βhi : ℚ := 2 * L2hi - (Ls xb 25 - Lr xb 25) - 1/30 - s2lo * L2lo

theorem beta_chk : (decide (|xa| < 1) && decide (|xb| < 1) && decide (0 ≤ L2lo) && decide (0 ≤ s2lo)
    && decide (s2lo ^ 2 ≤ 2) && decide (2 ≤ s2hi ^ 2) && decide (0 ≤ s2hi)) = true := by decide +kernel

theorem beta_win : (decide (EvenQ.bq - 1 / 10 ^ 12 ≤ βlo) && decide (βhi ≤ EvenQ.bq + 1 / 10 ^ 12)
    && decide (OddQ.bq = EvenQ.bq)) = true := by decide +kernel

theorem beta_bounds : (βlo : ℝ) ≤ βs ∧ βs ≤ (βhi : ℝ) := by
  have hc := beta_chk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hxa, hxb⟩, hL0⟩, hs0⟩, hs1⟩, hs2⟩, hs3⟩ := hc
  -- log 2
  have h2 := log_enc (1/2) (by norm_num) 50
  have e2 : Real.log (1 - ((1/2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1:ℝ) - ((1/2 : ℚ) : ℝ) = 2⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [e2, abs_le] at h2
  have l2lo : (L2lo : ℝ) ≤ Real.log 2 := by unfold L2lo; push_cast; linarith [h2.2]
  have l2hi : Real.log 2 ≤ (L2hi : ℝ) := by unfold L2hi; push_cast; linarith [h2.1]
  -- π
  have p1 : (plo : ℝ) < π := by unfold plo; have := Real.pi_gt_d20; push_cast; norm_num at this ⊢; linarith
  have p2 : π < (phi : ℝ) := by unfold phi; have := Real.pi_lt_d20; push_cast; norm_num at this ⊢; linarith
  have hplo : (0:ℝ) < plo := by unfold plo; norm_num
  -- log(15/(4π)) bounds
  have ha := log_enc xa hxa 25
  have hb := log_enc xb hxb 25
  have ea : (1:ℝ) - (xa:ℝ) = 15 / (4 * phi) := by unfold xa; push_cast; ring
  have eb : (1:ℝ) - (xb:ℝ) = 15 / (4 * plo) := by unfold xb; push_cast; ring
  rw [ea, abs_le] at ha; rw [eb, abs_le] at hb
  have hphi : (0:ℝ) < phi := by linarith
  have m1 : Real.log (15 / (4 * (phi:ℝ))) ≤ Real.log (15 / (4 * π)) :=
    Real.log_le_log (by positivity) (by gcongr)
  have m2 : Real.log (15 / (4 * π)) ≤ Real.log (15 / (4 * (plo:ℝ))) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hsplit : Real.log (30 / (2 * π)) = 2 * Real.log 2 + Real.log (15 / (4 * π)) := by
    rw [show (30:ℝ) / (2 * π) = 2 ^ 2 * (15 / (4 * π)) by field_simp; ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  -- √2
  have r1 : (s2lo : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by exact_mod_cast hs1)
  have r2 : Real.sqrt 2 ≤ (s2hi : ℝ) := by
    rw [Real.sqrt_le_left (by exact_mod_cast hs3)]; exact_mod_cast hs2
  have hL0' : (0:ℝ) ≤ L2lo := by exact_mod_cast hL0
  have hs0' : (0:ℝ) ≤ s2lo := by exact_mod_cast hs0
  have pr1 : (s2lo : ℝ) * L2lo ≤ Real.sqrt 2 * Real.log 2 := mul_le_mul r1 l2lo hL0' (Real.sqrt_nonneg 2)
  have pr2 : Real.sqrt 2 * Real.log 2 ≤ (s2hi : ℝ) * L2hi :=
    mul_le_mul r2 l2hi (by linarith) (by exact_mod_cast hs3)
  unfold βs
  rw [hsplit]
  constructor
  · unfold βlo; push_cast; linarith [ha.1, ha.2]
  · unfold βhi; push_cast; linarith [hb.1, hb.2]

theorem beta_enc (q : ℚ) (hq : q = EvenQ.bq) : |βs - (q : ℝ)| ≤ 1 / 10 ^ 12 := by
  subst hq
  have hc := beta_win
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have h1 : ((EvenQ.bq - 1 / 10 ^ 12 : ℚ) : ℝ) ≤ βlo := by exact_mod_cast hc.1.1
  have h2 : (βhi : ℝ) ≤ ((EvenQ.bq + 1 / 10 ^ 12 : ℚ) : ℝ) := by exact_mod_cast hc.1.2
  push_cast at h1 h2
  obtain ⟨b1, b2⟩ := beta_bounds
  rw [abs_le]; constructor <;> linarith

theorem beta_enc_even : |βs - (EvenQ.bq : ℝ)| ≤ 1 / 10 ^ 12 := beta_enc _ rfl
theorem beta_enc_odd : |βs - (OddQ.bq : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hc := beta_win
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact beta_enc _ hc.2

/-! ## Pole values -/

/-- Moments `J k n = ∫_{−1}^{1} t^{2k}(1−t²)ⁿ dt`. -/
noncomputable def J (k n : ℕ) : ℝ := ∫ t in (-1:ℝ)..1, t ^ (2 * k) * (1 - t ^ 2) ^ n

lemma J_zero (k : ℕ) : J k 0 = 2 / (2 * k + 1) := by
  unfold J
  simp only [pow_zero, mul_one, integral_pow]
  rw [show (-1:ℝ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
  push_cast; ring

lemma J_succ (k n : ℕ) : J k (n + 1) = J k n - J (k + 1) n := by
  unfold J
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  apply intervalIntegral.integral_congr; intro t _
  simp only; rw [show 2 * (k + 1) = 2 * k + 2 by ring]; ring

def W : ℕ := 62
def row0 : List ℚ := (List.range W).map fun k : ℕ => (2:ℚ) / (2 * (k:ℚ) + 1)
def row : ℕ → List ℚ
  | 0 => row0
  | n + 1 => List.zipWith (· - ·) (row n) (row n).tail

lemma row_spec (n : ℕ) : ∀ k, k + n < W → ∃ q, (row n)[k]? = some q ∧ (q : ℝ) = J k n := by
  induction n with
  | zero =>
    intro k hk
    refine ⟨2 / (2 * k + 1), ?_, ?_⟩
    · have hk' : k < W := by omega
      simp [row, row0, hk']
    · rw [J_zero]; push_cast; ring
  | succ n ih =>
    intro k hk
    obtain ⟨a, ha, ea⟩ := ih k (by omega)
    obtain ⟨b, hb, eb⟩ := ih (k + 1) (by omega)
    refine ⟨a - b, ?_, ?_⟩
    · simp only [row, List.getElem?_zipWith, List.getElem?_tail, ha, hb]
    · rw [J_succ, ← ea, ← eb]; exact Rat.cast_sub a b

lemma row_getD (n k : ℕ) (h : k + n < W) : (((row n).getD k 0 : ℚ) : ℝ) = J k n := by
  obtain ⟨q, hq, e⟩ := row_spec n k h
  rw [List.getD_eq_getElem?_getD, hq]; exact e

/-- Even Taylor polynomial of cosh, degree 10, and its remainder for `|y| ≤ 1/4`. -/
noncomputable def Tc (y : ℝ) : ℝ := ∑ k ∈ range 6, y ^ (2 * k) / ((2 * k).factorial : ℝ)
def Eq' : ℚ := (1/4) ^ 12 * (13 / ((Nat.factorial 12 : ℚ) * 12))

lemma cosh_tay (y : ℝ) (hy : |y| ≤ 1/4) : |Real.cosh y - Tc y| ≤ (Eq' : ℝ) := by
  have h1 := Real.exp_bound (x := y) (by linarith) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rw [abs_neg]; linarith) (n := 12) (by norm_num)
  have ee : Tc y = ((∑ m ∈ range 12, y ^ m / (m.factorial : ℝ)) +
      ∑ m ∈ range 12, (-y) ^ m / (m.factorial : ℝ)) / 2 := by
    unfold Tc; simp only [sum_range_succ, sum_range_zero]; ring
  rw [Real.cosh_eq, ee]
  rw [abs_neg] at h2
  have hp : |y| ^ 12 ≤ (1/4 : ℝ) ^ 12 := pow_le_pow_left₀ (abs_nonneg y) hy 12
  have hc : (0:ℝ) ≤ (Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12) := by positivity
  have hE : |y| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ (Eq' : ℝ) := by
    unfold Eq'; push_cast; exact mul_le_mul_of_nonneg_right hp (by norm_num)
  have a1 := abs_le.1 h1; have a2 := abs_le.1 h2
  rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

def cq (k : ℕ) : ℚ := (1/4) ^ (2 * k) / ((2 * k).factorial : ℚ)
def Aq (n : ℕ) : ℚ := lsum 6 fun k => cq k * (row n).getD k 0
def Cq (n : ℕ) : ℚ := (1/4) ^ n / (2 ^ (n + 1) * (n.factorial : ℚ))
def Xlo (n : ℕ) : ℚ := Cq n * (Aq n - Eq' * (row n).getD 0 0)
def Xhi (n : ℕ) : ℚ := Cq n * (Aq n + Eq' * (row n).getD 0 0)

lemma int_T (n : ℕ) : ∫ t in (-1:ℝ)..1, Tc ((1/4) * t) * (1 - t ^ 2) ^ n
    = ∑ k ∈ range 6, (cq k : ℝ) * J k n := by
  unfold Tc
  simp only [sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  apply sum_congr rfl; intro k _
  unfold J cq
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro t _
  simp only; push_cast; rw [mul_pow]; ring

lemma iP_enc (n : ℕ) (hn : 5 + n < W) : (Xlo n : ℝ) ≤ iP n (1/4) ∧ iP n (1/4) ≤ (Xhi n : ℝ) := by
  have hA : ((Aq n : ℚ) : ℝ) = ∑ k ∈ range 6, (cq k : ℝ) * J k n := by
    unfold Aq; rw [lsum_cast]; apply sum_congr rfl; intro k hk
    have := mem_range.1 hk; push_cast; rw [row_getD n k (by omega)]
  have h0 : (((row n).getD 0 0 : ℚ) : ℝ) = J 0 n := row_getD n 0 (by omega)
  have hJ0 : J 0 n = ∫ t in (-1:ℝ)..1, (1 - t ^ 2) ^ n := by unfold J; simp
  have hC : ((Cq n : ℚ) : ℝ) = (1/4 : ℝ) ^ n / (2 ^ (n + 1) * n.factorial) := by unfold Cq; push_cast; ring
  have hCp : (0:ℝ) < (1/4 : ℝ) ^ n / (2 ^ (n + 1) * n.factorial) := by positivity
  have ci : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume (-1) 1 :=
    fun g hg => hg.intervalIntegrable _ _
  have cT : Continuous fun t : ℝ => Tc ((1/4) * t) * (1 - t ^ 2) ^ n := by unfold Tc; fun_prop
  have cw : Continuous fun t : ℝ => (1 - t ^ 2) ^ n := by fun_prop
  have cc : Continuous fun t : ℝ => Real.cosh ((1/4) * t) * (1 - t ^ 2) ^ n := by fun_prop
  have pt : ∀ t ∈ Set.Icc (-1:ℝ) 1, |Real.cosh ((1/4) * t) - Tc ((1/4) * t)| ≤ (Eq' : ℝ) := by
    intro t ht; apply cosh_tay; rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
    have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    linarith
  have wn : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ (1 - t ^ 2) ^ n := by
    intro t ht; apply pow_nonneg; nlinarith [ht.1, ht.2]
  have lo : ∫ t in (-1:ℝ)..1, (Tc ((1/4) * t) * (1 - t ^ 2) ^ n - (Eq' : ℝ) * (1 - t ^ 2) ^ n)
      ≤ ∫ t in (-1:ℝ)..1, Real.cosh ((1/4) * t) * (1 - t ^ 2) ^ n := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ (by fun_prop)) (ci _ cc)
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).1 (wn t ht)]
  have hi : ∫ t in (-1:ℝ)..1, Real.cosh ((1/4) * t) * (1 - t ^ 2) ^ n
      ≤ ∫ t in (-1:ℝ)..1, (Tc ((1/4) * t) * (1 - t ^ 2) ^ n + (Eq' : ℝ) * (1 - t ^ 2) ^ n) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ cc) (ci _ (by fun_prop))
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).2 (wn t ht)]
  rw [intervalIntegral.integral_sub (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_T, ← hJ0] at lo
  rw [intervalIntegral.integral_add (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_T, ← hJ0] at hi
  unfold iP Xlo Xhi
  push_cast
  rw [hC, hA, h0]
  constructor
  · exact mul_le_mul_of_nonneg_left lo hCp.le
  · exact mul_le_mul_of_nonneg_left hi hCp.le

lemma pole_eq (n : ℕ) : pole n = Real.sqrt (2 * n + 1) * iP n (1/4) := by
  unfold pole
  congr 1
  rw [show (2 * n + 1 : ℝ) = 2 ^ 2 * ((1 / 2) * (n + 1 / 2)) by ring,
    Real.sqrt_mul (show (0:ℝ) ≤ 2 ^ 2 by norm_num) ((1/2) * (n + 1/2)), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- Bool test that `√a · [xl, xh] ⊆ [p − ε, p + ε]`. -/
def pt1 (a xl xh p ε : ℚ) : Bool :=
  decide (0 ≤ xl) && decide (a * xh ^ 2 ≤ (p + ε) ^ 2) && decide (0 ≤ p + ε)
    && (decide (p - ε ≤ 0) || decide ((p - ε) ^ 2 ≤ a * xl ^ 2))

lemma pt1_spec (a xl xh p ε : ℚ) (ha : 0 ≤ a) (h : pt1 a xl xh p ε = true) (X : ℝ)
    (h1 : (xl:ℝ) ≤ X) (h2 : X ≤ xh) : |Real.sqrt a * X - p| ≤ ε := by
  unfold pt1 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hxl, hu⟩, hpe⟩, hl⟩ := h
  have hxl' : (0:ℝ) ≤ xl := by exact_mod_cast hxl
  have hX : 0 ≤ X := le_trans hxl' h1
  have ha' : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hs := Real.sqrt_nonneg (a:ℝ)
  have up : Real.sqrt a * X ≤ p + ε := by
    have : Real.sqrt a * X ≤ Real.sqrt a * xh := mul_le_mul_of_nonneg_left h2 hs
    have e : Real.sqrt a * xh = Real.sqrt (a * xh ^ 2) := by
      rw [Real.sqrt_mul ha', Real.sqrt_sq (by linarith)]
    have : Real.sqrt ((a:ℝ) * xh ^ 2) ≤ Real.sqrt (((p + ε : ℚ) : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hu)
    rw [Real.sqrt_sq (by exact_mod_cast hpe)] at this
    push_cast at this; linarith
  have dn : (p:ℝ) - ε ≤ Real.sqrt a * X := by
    rcases hl with hl | hl
    · have : ((p - ε : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hl
      push_cast at this; nlinarith
    · have : Real.sqrt a * xl ≤ Real.sqrt a * X := mul_le_mul_of_nonneg_left h1 hs
      have e : Real.sqrt a * xl = Real.sqrt (a * xl ^ 2) := by
        rw [Real.sqrt_mul ha', Real.sqrt_sq hxl']
      have := Real.le_sqrt_of_sq_le (show (((p - ε : ℚ) : ℝ)) ^ 2 ≤ (a:ℝ) * xl ^ 2 by exact_mod_cast hl)
      push_cast at this; linarith
  rw [abs_le]; constructor <;> linarith

def pchkC (par : ℕ) (pq : List ℚ) (ε : ℚ) : Bool :=
  (List.range 28).all fun i => pt1 (2 * (2 * i + par : ℕ) + 1) (Xlo (2 * i + par)) (Xhi (2 * i + par)) (pq.getD i 0) ε

lemma pole_of (par : ℕ) (hp : par ≤ 1) (pq : List ℚ) (ε : ℚ) (h : pchkC par pq ε = true) :
    ∀ i < 28, |pole (2 * i + par) - ((pq.getD i 0 : ℚ) : ℝ)| ≤ (ε : ℝ) := by
  intro i hi
  unfold pchkC at h
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  obtain ⟨l, u⟩ := iP_enc (2 * i + par) (by unfold W; omega)
  rw [pole_eq]
  have := pt1_spec _ _ _ _ _ (by positivity) h1 _ l u
  push_cast at this ⊢; exact this

theorem pole_chk_even : pchkC 0 EvenQ.pq (1 / 10 ^ 12) = true := by decide +kernel
theorem pole_chk_odd : pchkC 1 OddQ.pq (1 / 10 ^ 12) = true := by decide +kernel

theorem pole_enc_even : ∀ i < 28, |pole (2 * i + 0) - ((EvenQ.pq.getD i 0 : ℚ) : ℝ)| ≤ 1 / 10 ^ 12 := by
  have := pole_of 0 (by norm_num) _ _ pole_chk_even; push_cast at this; exact this
theorem pole_enc_odd : ∀ i < 28, |pole (2 * i + 1) - ((OddQ.pq.getD i 0 : ℚ) : ℝ)| ≤ 1 / 10 ^ 12 := by
  have := pole_of 1 (by norm_num) _ _ pole_chk_odd; push_cast at this; exact this

/-! ## Narrowed residual: only the digamma-weighted Bessel integrals -/

/-- **Sole remaining named hypothesis**: entrywise enclosure of `C^ψ` (`(1/π)∫₀³⁰ wψ T̂ₙ T̂ₘ`). -/
def CmEnc (par : ℕ) (cq : List (List ℚ)) (εc : ℝ) : Prop :=
  ∀ i < 28, ∀ j < 28, |Cm wψ (2 * i + par) (2 * j + par) - ((WeilTail.getq cq i j : ℚ) : ℝ)| ≤ εc

theorem L05_even (H : CmEnc 0 EvenQ.cq (6/10^9)) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilForm.weilQ (1 / 2) (WeilPlanch.fx N x) :=
  WeilHead.L05_even ⟨beta_enc_even, by have := pole_enc_even; simpa using this, H⟩ N hN x hx

theorem L05_odd (H : CmEnc 1 OddQ.cq (13/10^7)) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilZhuRed.QF 1 (-1) N x :=
  WeilHead.L05_odd ⟨beta_enc_odd.trans (by norm_num),
    fun i hi => (pole_enc_odd i hi).trans (by norm_num), H⟩ N hN x hx

end WeilConst
