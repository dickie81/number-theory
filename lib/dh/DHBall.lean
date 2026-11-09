import Mathlib
import DHBallDefs

/-!
# A fixed-point evaluator for Dirichlet polynomials at a complex point: the proofs

`DHBallDefs` defines integer arithmetic on balls; this file proves that each operation encloses what it should.

* `B.has b x`: the ball `b` holds the real `x`; `CB.has b z`: the complex ball `b` holds `z`.
* `has_add`, `has_sub`, `has_neg`, `has_mul`, `has_divNat`, `has_mulRat`, and the same for complex balls;
  `bounds_of_has`: what a ball says in real numbers.
* `has_term`: `term L` holds `n^{-c}` if `L` holds `log n`.
* `has_logStep`: `logStep n` holds `log (n + 1) − log n`.
* `Inv m st`: the state `st` holds the sums over the blocks before `m`; `inv_run`: `run` keeps it.
-/

open Real Finset

namespace DHBall

/-- The ball `b` holds `x`: `|x·S − c| ≤ e`. -/
def B.has (b : B) (x : ℝ) : Prop := |x * (S : ℝ) - (b.c : ℝ)| ≤ (b.e : ℝ)

/-- The complex ball `b` holds `z`. -/
def CB.has (b : CB) (z : ℂ) : Prop := b.re.has z.re ∧ b.im.has z.im

theorem S_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]

theorem S_pos' : 0 < S := by norm_num [S]

/-! ## Floors -/

theorem ediv_le (a : ℤ) {k : ℕ} (hk : 0 < k) : ((a / (k : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  have h := Int.ediv_mul_le a (show (k : ℤ) ≠ 0 by exact_mod_cast hk.ne')
  exact_mod_cast h

theorem lt_ediv_add_one (a : ℤ) {k : ℕ} (hk : 0 < k) : (a : ℝ) / k < ((a / (k : ℤ) : ℤ) : ℝ) + 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_lt_iff₀ hk']
  have h := Int.lt_ediv_add_one_mul_self a (show (0 : ℤ) < k by exact_mod_cast hk)
  exact_mod_cast h

theorem natdiv_le (a : ℕ) {k : ℕ} (hk : 0 < k) : ((a / k : ℕ) : ℝ) ≤ (a : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  exact_mod_cast Nat.div_mul_le_self a k

theorem lt_natdiv_add_one (a : ℕ) {k : ℕ} (hk : 0 < k) : (a : ℝ) / k < ((a / k : ℕ) : ℝ) + 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_lt_iff₀ hk']
  have h := Nat.lt_div_mul_add hk (a := a)
  have : (a : ℝ) < ((a / k : ℕ) : ℝ) * k + k := by exact_mod_cast h
  linarith

/-- The distance from `a / k` to its floor is at most `1`. -/
theorem abs_div_sub_ediv (a : ℤ) {k : ℕ} (hk : 0 < k) :
    |(a : ℝ) / k - ((a / (k : ℤ) : ℤ) : ℝ)| ≤ 1 := by
  have h1 := ediv_le a hk
  have h2 := lt_ediv_add_one a hk
  rw [abs_le]
  constructor <;> linarith

theorem natAbs_cast (a : ℤ) : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-! ## Real balls -/

theorem has_add {a b : B} {x y : ℝ} (ha : a.has x) (hb : b.has y) : (a.add b).has (x + y) := by
  unfold B.has at *
  simp only [B.add]
  push_cast
  have e : (x + y) * (S : ℝ) - ((a.c : ℝ) + b.c) = (x * S - a.c) + (y * S - b.c) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem has_sub {a b : B} {x y : ℝ} (ha : a.has x) (hb : b.has y) : (a.sub b).has (x - y) := by
  unfold B.has at *
  simp only [B.sub]
  push_cast
  have e : (x - y) * (S : ℝ) - ((a.c : ℝ) - b.c) = (x * S - a.c) - (y * S - b.c) := by ring
  rw [e]
  exact (abs_sub _ _).trans (add_le_add ha hb)

theorem has_neg {a : B} {x : ℝ} (ha : a.has x) : (a.neg).has (-x) := by
  unfold B.has at *
  simp only [B.neg]
  push_cast
  have e : -x * (S : ℝ) - -(a.c : ℝ) = -(x * S - a.c) := by ring
  rw [e, abs_neg]
  exact ha

theorem has_mul {a b : B} {x y : ℝ} (ha : a.has x) (hb : b.has y) : (a.mul b).has (x * y) := by
  unfold B.has at *
  simp only [B.mul]
  have hS := S_pos
  have h1 := abs_div_sub_ediv (a.c * b.c) S_pos'
  have h2 := lt_natdiv_add_one (a.c.natAbs * b.e + b.c.natAbs * a.e + a.e * b.e) S_pos'
  push_cast at h1 h2 ⊢
  rw [natAbs_cast, natAbs_cast] at h2
  set X := x * (S : ℝ) with hX
  set Y := y * (S : ℝ) with hY
  have key : |X * Y - (a.c : ℝ) * b.c| ≤ |(a.c : ℝ)| * b.e + |(b.c : ℝ)| * a.e + (a.e : ℝ) * b.e := by
    have e : X * Y - (a.c : ℝ) * b.c =
        (X - a.c) * (Y - b.c) + (a.c : ℝ) * (Y - b.c) + (b.c : ℝ) * (X - a.c) := by ring
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul]
    have := mul_le_mul ha hb (abs_nonneg _) (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hb (abs_nonneg (a.c : ℝ))
    have := mul_le_mul_of_nonneg_left ha (abs_nonneg (b.c : ℝ))
    linarith
  have e2 : x * y * (S : ℝ) = X * Y / S := by
    rw [hX, hY]; field_simp
  have e3 : X * Y / (S : ℝ) - ((a.c * b.c / (S : ℤ) : ℤ) : ℝ) =
      (X * Y - (a.c : ℝ) * b.c) / S + ((a.c : ℝ) * b.c / S - ((a.c * b.c / (S : ℤ) : ℤ) : ℝ)) := by
    field_simp; ring
  rw [e2, e3]
  refine (abs_add_le _ _).trans ?_
  have h3 : |(X * Y - (a.c : ℝ) * b.c) / (S : ℝ)| ≤
      (|(a.c : ℝ)| * b.e + |(b.c : ℝ)| * a.e + (a.e : ℝ) * b.e) / S := by
    rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right key hS.le
  linarith

theorem has_divNat {a : B} {x : ℝ} (ha : a.has x) {k : ℕ} (hk : 0 < k) :
    (a.divNat k).has (x / k) := by
  unfold B.has at *
  simp only [B.divNat]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := abs_div_sub_ediv a.c hk
  have h2 := lt_natdiv_add_one a.e hk
  push_cast
  have e : x / (k : ℝ) * (S : ℝ) - ((a.c / (k : ℤ) : ℤ) : ℝ) =
      (x * S - a.c) / k + ((a.c : ℝ) / k - ((a.c / (k : ℤ) : ℤ) : ℝ)) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h3 : |(x * (S : ℝ) - a.c) / (k : ℝ)| ≤ (a.e : ℝ) / k := by
    rw [abs_div, abs_of_pos hk']
    exact div_le_div_of_nonneg_right ha hk'.le
  linarith

theorem has_mulRat {a : B} {x : ℝ} (ha : a.has x) (p : ℕ) {q : ℕ} (hq : 0 < q) :
    (a.mulRat p q).has (x * ((p : ℝ) / q)) := by
  unfold B.has at *
  simp only [B.mulRat]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := abs_div_sub_ediv (a.c * (p : ℤ)) hq
  have h2 := lt_natdiv_add_one (a.e * p) hq
  push_cast at h1 h2 ⊢
  have e : x * ((p : ℝ) / q) * (S : ℝ) - ((a.c * (p : ℤ) / (q : ℤ) : ℤ) : ℝ) =
      (x * S - a.c) * p / q + ((a.c : ℝ) * p / q - ((a.c * (p : ℤ) / (q : ℤ) : ℤ) : ℝ)) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h3 : |(x * (S : ℝ) - a.c) * p / (q : ℝ)| ≤ (a.e : ℝ) * p / q := by
    rw [abs_div, abs_of_pos hq', abs_mul, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ))]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg p)) hq'.le
  linarith

/-- A ball holds only reals of absolute value at most `(|c| + e) / S`. -/
theorem abs_le_of_has {a : B} {x : ℝ} (ha : a.has x) :
    |x| * (S : ℝ) ≤ ((a.c.natAbs + a.e : ℕ) : ℝ) := by
  unfold B.has at ha
  push_cast
  rw [natAbs_cast]
  have hS := S_pos
  have e : |x| * (S : ℝ) = |x * S| := by rw [abs_mul, abs_of_pos hS]
  rw [e]
  have h := abs_sub_abs_le_abs_sub (x * (S : ℝ)) (a.c : ℝ)
  linarith

/-- The reals that a ball holds lie between `(c − e)/S` and `(c + e)/S`. -/
theorem bounds_of_has {a : B} {x : ℝ} (ha : a.has x) :
    ((a.c : ℝ) - a.e) / (S : ℝ) ≤ x ∧ x ≤ ((a.c : ℝ) + a.e) / (S : ℝ) := by
  have hS := S_pos
  unfold B.has at ha
  rw [abs_le] at ha
  rw [div_le_iff₀ hS, le_div_iff₀ hS]
  constructor <;> linarith [ha.1, ha.2]

/-! ## Complex balls -/

theorem chas_add {a b : CB} {z w : ℂ} (ha : a.has z) (hb : b.has w) : (a.add b).has (z + w) :=
  ⟨by simpa [CB.add] using has_add ha.1 hb.1, by simpa [CB.add] using has_add ha.2 hb.2⟩

theorem chas_sub {a b : CB} {z w : ℂ} (ha : a.has z) (hb : b.has w) : (a.sub b).has (z - w) :=
  ⟨by simpa [CB.sub] using has_sub ha.1 hb.1, by simpa [CB.sub] using has_sub ha.2 hb.2⟩

theorem chas_mul {a b : CB} {z w : ℂ} (ha : a.has z) (hb : b.has w) : (a.mul b).has (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]
    exact has_sub (has_mul ha.1 hb.1) (has_mul ha.2 hb.2)
  · rw [Complex.mul_im]
    exact has_add (has_mul ha.1 hb.2) (has_mul ha.2 hb.1)

theorem chas_divNat {a : CB} {z : ℂ} (ha : a.has z) {k : ℕ} (hk : 0 < k) :
    (a.divNat k).has (z / (k : ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.div_natCast_re]
    exact has_divNat ha.1 hk
  · rw [Complex.div_natCast_im]
    exact has_divNat ha.2 hk

theorem chas_smul {l : B} {a : CB} {x : ℝ} {z : ℂ} (hl : l.has x) (ha : a.has z) :
    (CB.smul l a).has ((x : ℂ) * z) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.re_ofReal_mul]
    exact has_mul hl ha.1
  · rw [Complex.im_ofReal_mul]
    exact has_mul hl ha.2

theorem chas_one : one.has 1 := by
  refine ⟨?_, ?_⟩ <;> simp [one, B.has]

theorem chas_zero : zero.has 0 := by
  refine ⟨?_, ?_⟩ <;> simp [zero, B.has]

/-! ## The exponential -/

theorem has_expLoop {v : CB} {z : ℂ} (hv : v.has z) :
    ∀ (fuel m : ℕ) (term sum : CB), term.has (z ^ m / (m.factorial : ℂ)) →
      sum.has (∑ j ∈ range m, z ^ j / (j.factorial : ℂ)) →
      (expLoop v m fuel term sum).has (∑ j ∈ range (m + fuel), z ^ j / (j.factorial : ℂ)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m term sum _ hs
    simpa [expLoop] using hs
  | succ f ih =>
    intro m term sum ht hs
    rw [expLoop]
    have e : m + (f + 1) = (m + 1) + f := by ring
    rw [e]
    refine ih (m + 1) _ _ ?_ ?_
    · have h := chas_divNat (chas_mul ht hv) (Nat.succ_pos m)
      have hm : ((m.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
      have e2 : z ^ m / (m.factorial : ℂ) * z / ((m + 1 : ℕ) : ℂ) =
          z ^ (m + 1) / ((m + 1).factorial : ℂ) := by
        rw [Nat.factorial_succ, pow_succ]
        push_cast at hm1 ⊢
        field_simp
      rw [← e2]
      exact h
    · rw [sum_range_succ]
      exact chas_add hs ht

theorem exp_rem : (15 : ℝ) / ((Nat.factorial 14 : ℝ) * 14) * (S : ℝ) ≤ (expRem : ℝ) := by
  norm_num [S, expRem, Nat.factorial]

theorem has_widen_exp {v : CB} {z : ℂ} (hv : v.has z) (hz : ‖z‖ ≤ 1) :
    (widen (expLoop v 0 14 one zero)).has (Complex.exp z) := by
  have hp := has_expLoop hv 14 0 one zero (by simpa using chas_one) (by simpa using chas_zero)
  rw [zero_add] at hp
  have hb := Complex.exp_bound hz (n := 14) (by norm_num)
  have hS := S_pos
  have hd : ‖Complex.exp z - ∑ m ∈ range 14, z ^ m / (m.factorial : ℂ)‖ * (S : ℝ) ≤ (expRem : ℝ) := by
    refine le_trans ?_ exp_rem
    refine mul_le_mul_of_nonneg_right (hb.trans ?_) hS.le
    have h1 : ‖z‖ ^ 14 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    have h0 : (0 : ℝ) ≤ ((Nat.succ 14 : ℕ) : ℝ) * ((Nat.factorial 14 : ℝ) * (14 : ℕ))⁻¹ := by positivity
    calc ‖z‖ ^ 14 * (((Nat.succ 14 : ℕ) : ℝ) * ((Nat.factorial 14 : ℝ) * (14 : ℕ))⁻¹)
        ≤ 1 * (((Nat.succ 14 : ℕ) : ℝ) * ((Nat.factorial 14 : ℝ) * (14 : ℕ))⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h0
      _ = 15 / ((Nat.factorial 14 : ℝ) * 14) := by push_cast; ring
  set P := ∑ m ∈ range 14, z ^ m / (m.factorial : ℂ) with hP
  set p := expLoop v 0 14 one zero with hpdef
  have hre : |(Complex.exp z - P).re| ≤ ‖Complex.exp z - P‖ := Complex.abs_re_le_norm _
  have him : |(Complex.exp z - P).im| ≤ ‖Complex.exp z - P‖ := Complex.abs_im_le_norm _
  refine ⟨?_, ?_⟩
  · have h1 := hp.1
    unfold B.has at h1 ⊢
    simp only [widen]
    push_cast
    have e : (Complex.exp z).re * (S : ℝ) - (p.re.c : ℝ) =
        (P.re * S - p.re.c) + (Complex.exp z - P).re * S := by
      rw [Complex.sub_re]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2 : |(Complex.exp z - P).re * (S : ℝ)| ≤ (expRem : ℝ) := by
      rw [abs_mul, abs_of_pos hS]
      exact (mul_le_mul_of_nonneg_right hre hS.le).trans hd
    linarith
  · have h1 := hp.2
    unfold B.has at h1 ⊢
    simp only [widen]
    push_cast
    have e : (Complex.exp z).im * (S : ℝ) - (p.im.c : ℝ) =
        (P.im * S - p.im.c) + (Complex.exp z - P).im * S := by
      rw [Complex.sub_im]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2 : |(Complex.exp z - P).im * (S : ℝ)| ≤ (expRem : ℝ) := by
      rw [abs_mul, abs_of_pos hS]
      exact (mul_le_mul_of_nonneg_right him hS.le).trans hd
    linarith

theorem has_sqLoop : ∀ (j : ℕ) {b : CB} {z : ℂ}, b.has z → (sqLoop j b).has (z ^ 2 ^ j)
  | 0, b, z, h => by simpa [sqLoop] using h
  | j + 1, b, z, h => by
    have h2 := has_sqLoop j (chas_mul h h)
    have e : z ^ 2 ^ (j + 1) = (z * z) ^ 2 ^ j := by
      rw [pow_succ', pow_mul, pow_two]
    rw [sqLoop, e]
    exact h2

/-- `expBall v` holds `exp(z)^16` if `v` holds `z` and `exp(z)^16` has modulus at most `1`. -/
theorem has_expBall {v : CB} {z : ℂ} (hv : v.has z) (h1 : ‖Complex.exp z ^ 16‖ ≤ 1) :
    (expBall v).has (Complex.exp z ^ 16) := by
  have hS := S_pos
  unfold expBall
  split_ifs with hc
  · have hz : ‖z‖ ≤ 1 := by
      have ha := abs_le_of_has hv.1
      have hb := abs_le_of_has hv.2
      have hc' : (((v.re.c.natAbs + v.re.e : ℕ) : ℝ)) ^ 2 + (((v.im.c.natAbs + v.im.e : ℕ) : ℝ)) ^ 2 ≤
          (S : ℝ) ^ 2 := by exact_mod_cast hc
      have h3 : (|z.re| * (S : ℝ)) ^ 2 ≤ (((v.re.c.natAbs + v.re.e : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ha 2
      have h4 : (|z.im| * (S : ℝ)) ^ 2 ≤ (((v.im.c.natAbs + v.im.e : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hb 2
      have h5 : ‖z‖ ^ 2 * (S : ℝ) ^ 2 ≤ 1 * (S : ℝ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have e : (z.re * z.re + z.im * z.im) * (S : ℝ) ^ 2 =
            (|z.re| * (S : ℝ)) ^ 2 + (|z.im| * (S : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
        rw [e]; linarith
      have h6 : ‖z‖ ^ 2 ≤ 1 := le_of_mul_le_mul_right h5 (by positivity)
      exact (sq_le_one_iff₀ (norm_nonneg z)).1 h6
    have h := has_sqLoop 4 (has_widen_exp hv hz)
    norm_num at h
    exact h
  · refine ⟨?_, ?_⟩
    · unfold B.has
      push_cast
      rw [sub_zero, abs_mul, abs_of_pos hS]
      have := (Complex.abs_re_le_norm (Complex.exp z ^ 16)).trans h1
      nlinarith
    · unfold B.has
      push_cast
      rw [sub_zero, abs_mul, abs_of_pos hS]
      have := (Complex.abs_im_le_norm (Complex.exp z ^ 16)).trans h1
      nlinarith

/-! ## The term `n^{-c}` -/

/-- The centre `c = reN/reD + i·imN/imD`. -/
noncomputable def c : ℂ := ⟨(reN : ℝ) / reD, (imN : ℝ) / imD⟩

theorem has_twoPi : twoPi.has (2 * π) := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  unfold B.has twoPi
  simp only [S]
  push_cast
  rw [abs_le]
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- The argument `t·log n`, less `k` turns. -/
theorem has_theta {L : B} {n : ℕ} (hL : L.has (Real.log n)) (k : ℤ) :
    (⟨(L.mulRat imN imD).c - k * twoPi.c, (L.mulRat imN imD).e + k.natAbs * twoPi.e⟩ : B).has
      (Real.log n * ((imN : ℝ) / imD) - k * (2 * π)) := by
  have hy := has_mulRat hL imN (q := imD) (by norm_num [imD])
  have hp := has_twoPi
  unfold B.has at hy hp ⊢
  push_cast
  rw [natAbs_cast]
  have e : (Real.log n * ((imN : ℝ) / imD) - k * (2 * π)) * (S : ℝ) -
      (((L.mulRat imN imD).c : ℝ) - k * twoPi.c) =
      (Real.log n * ((imN : ℝ) / imD) * S - (L.mulRat imN imD).c) - k * (2 * π * S - twoPi.c) := by
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have := mul_le_mul_of_nonneg_left hp (abs_nonneg (k : ℝ))
  linarith

/-- `exp` of the reduced exponent, to the power `16`, is `n^{-c}`. -/
theorem exp_red_pow {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    Complex.exp (⟨-(Real.log n * ((reN : ℝ) / reD)) / ((16 : ℕ) : ℝ),
      -(Real.log n * ((imN : ℝ) / imD) - k * (2 * π)) / ((16 : ℕ) : ℝ)⟩ : ℂ) ^ 16 = (n : ℂ) ^ (-c) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← Complex.exp_nat_mul, Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  have e : ((16 : ℕ) : ℂ) * (⟨-(Real.log n * ((reN : ℝ) / reD)) / ((16 : ℕ) : ℝ),
        -(Real.log n * ((imN : ℝ) / imD) - k * (2 * π)) / ((16 : ℕ) : ℝ)⟩ : ℂ) =
      (Real.log n : ℂ) * (-c) + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
        Complex.im_ofNat, c]
      push_cast
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
        Complex.im_ofNat, c]
      push_cast
      ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `redArg L` holds a `z` with `exp(z)^16 = n^{-c}`, if `L` holds `log n`. -/
theorem has_redArg {L : B} {n : ℕ} (hn : 1 ≤ n) (hL : L.has (Real.log n)) :
    ∃ z : ℂ, (redArg L).has z ∧ Complex.exp z ^ 16 = (n : ℂ) ^ (-c) := by
  have hx := has_mulRat hL reN (q := reD) (by norm_num [reD])
  refine ⟨_, ⟨?_, ?_⟩, exp_red_pow hn ((2 * (L.mulRat imN imD).c + twoPi.c) / (2 * twoPi.c))⟩
  · exact has_divNat (has_neg hx) (by norm_num)
  · exact has_divNat (has_neg (has_theta hL _)) (by norm_num)

theorem norm_natCast_cpow_neg_c_le {n : ℕ} (hn : 1 ≤ n) : ‖(n : ℂ) ^ (-c)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re, c, Left.neg_nonpos_iff]
  positivity

/-- `term L` holds `n^{-c}`, if `L` holds `log n`. -/
theorem has_term {L : B} {n : ℕ} (hn : 1 ≤ n) (hL : L.has (Real.log n)) :
    (term L).has ((n : ℂ) ^ (-c)) := by
  obtain ⟨z, hz, he⟩ := has_redArg hn hL
  have h := has_expBall hz (by rw [he]; exact norm_natCast_cpow_neg_c_le hn)
  rw [he] at h
  exact h

/-! ## The logarithm -/

theorem has_logSum (n1 : ℕ) (hn1 : 1 ≤ n1) :
    ∀ (fuel i acc : ℕ),
      ((logSum n1 fuel i (n1 ^ i) acc : ℕ) : ℝ) ≤
          acc + (S : ℝ) * ∑ j ∈ range fuel, ((1 : ℝ) / n1) ^ (i + j + 1) / ((i + j : ℕ) + 1) ∧
        (acc : ℝ) + (S : ℝ) * ∑ j ∈ range fuel, ((1 : ℝ) / n1) ^ (i + j + 1) / ((i + j : ℕ) + 1) -
          2 * fuel ≤ ((logSum n1 fuel i (n1 ^ i) acc : ℕ) : ℝ) := by
  have hn1' : (0 : ℝ) < n1 := by exact_mod_cast hn1
  intro fuel
  induction fuel with
  | zero =>
    intro i acc
    simp [logSum]
  | succ f ih =>
    intro i acc
    rw [logSum, ← pow_succ]
    obtain ⟨h1, h2⟩ := ih (i + 1) (acc + S / n1 ^ (i + 1) / (i + 1))
    have hpow : 0 < n1 ^ (i + 1) := pow_pos hn1 _
    have q1 := natdiv_le S hpow
    have q2 := lt_natdiv_add_one S hpow
    have t1 := natdiv_le (S / n1 ^ (i + 1)) (Nat.succ_pos i)
    have t2 := lt_natdiv_add_one (S / n1 ^ (i + 1)) (Nat.succ_pos i)
    have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hi1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
    -- the first term of the sum
    have e0 : (S : ℝ) * (((1 : ℝ) / n1) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) =
        (S : ℝ) / ((n1 ^ (i + 1) : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) := by
      push_cast
      rw [one_div, inv_pow]
      field_simp
    have es : ∑ j ∈ range (f + 1), ((1 : ℝ) / n1) ^ (i + j + 1) / ((i + j : ℕ) + 1) =
        ((1 : ℝ) / n1) ^ (i + 1) / ((i + 1 : ℕ) : ℝ) +
          ∑ j ∈ range f, ((1 : ℝ) / n1) ^ (i + 1 + j + 1) / ((i + 1 + j : ℕ) + 1) := by
      rw [sum_range_succ']
      rw [add_comm]
      congr 1
      · push_cast; simp
      · refine sum_congr rfl fun j _ => ?_
        have e1 : i + (j + 1) + 1 = i + 1 + j + 1 := by ring
        have e2 : i + (j + 1) = i + 1 + j := by ring
        rw [e1, e2]
    have ub : (((S / n1 ^ (i + 1) / (i + 1) : ℕ)) : ℝ) ≤
        (S : ℝ) / ((n1 ^ (i + 1) : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) :=
      t1.trans (div_le_div_of_nonneg_right q1 hi.le)
    have lb : (S : ℝ) / ((n1 ^ (i + 1) : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) - 2 ≤
        (((S / n1 ^ (i + 1) / (i + 1) : ℕ)) : ℝ) := by
      have h3 : (S : ℝ) / ((n1 ^ (i + 1) : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) ≤
          (((S / n1 ^ (i + 1) : ℕ) : ℝ) + 1) / ((i + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right q2.le hi.le
      have h4 : (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hi]; exact hi1
      have h5 : (((S / n1 ^ (i + 1) : ℕ) : ℝ) + 1) / ((i + 1 : ℕ) : ℝ) =
          ((S / n1 ^ (i + 1) : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) + 1 / ((i + 1 : ℕ) : ℝ) := by ring
      linarith
    rw [es, mul_add, e0]
    push_cast at h1 h2 ub lb ⊢
    constructor <;> linarith

/-- `logStep n` holds `log (n + 1) − log n`. -/
theorem has_logStep {n : ℕ} (hn : 1 ≤ n) :
    (logStep n).has (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
  have hS := S_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨N, hN⟩ : ∃ N, N = logTerms n := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1x : 1 - x = (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    rw [hx]; push_cast; field_simp; ring
  have hx1 : x < 1 := by
    have : 0 < (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hser := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_pos hx0]; exact hx1) N
  have hlog : Real.log (1 - x) = Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [h1x, Real.log_div hn0.ne' hn1.ne']
  have htail : |x| ^ (N + 1) / (1 - |x|) = 1 / ((((n + 1) ^ N * n : ℕ)) : ℝ) := by
    rw [abs_of_pos hx0, h1x, hx, one_div, inv_pow]
    push_cast
    field_simp
    ring
  rw [hlog, htail] at hser
  obtain ⟨s1, s2⟩ := has_logSum (n + 1) (Nat.succ_pos n) N 0 0
  simp only [zero_add, pow_zero] at s1 s2
  rw [← hx] at s1 s2
  have hden : 0 < (n + 1) ^ N * n := Nat.mul_pos (pow_pos (Nat.succ_pos n) _) hn
  have t2 := lt_natdiv_add_one S hden
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑ i ∈ range N, x ^ (i + 1) / ((i : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hSg] at hser s1 s2
  rw [abs_le] at hser
  obtain ⟨l1, l2⟩ := hser
  have l1' := mul_le_mul_of_nonneg_left l1 hS.le
  have l2' := mul_le_mul_of_nonneg_left l2 hS.le
  have hmul : (S : ℝ) * (1 / ((((n + 1) ^ N * n : ℕ)) : ℝ)) = (S : ℝ) / ((((n + 1) ^ N * n : ℕ)) : ℝ) := by
    ring
  rw [hmul] at l2'
  rw [mul_neg, hmul] at l1'
  unfold B.has logStep
  rw [← hN]
  push_cast at s1 s2 t2 l1' l2' ⊢
  rw [abs_le]
  constructor <;> linarith

theorem has_log_succ {L : B} {n : ℕ} (hn : 1 ≤ n) (hL : L.has (Real.log (n : ℝ))) :
    (L.add (logStep n)).has (Real.log ((n + 1 : ℕ) : ℝ)) := by
  have h := has_add hL (has_logStep hn)
  rwa [add_sub_cancel] at h

/-! ## The sums -/

/-- `n^{-c}`. -/
noncomputable def T (n : ℕ) : ℂ := (n : ℂ) ^ (-c)

/-- `Σ_{k<m} ((5k+1)^{-c} − (5k+4)^{-c})`. -/
noncomputable def SA (m : ℕ) : ℂ := ∑ k ∈ range m, (T (5 * k + 1) - T (5 * k + 4))

/-- `Σ_{k<m} ((5k+2)^{-c} − (5k+3)^{-c})`. -/
noncomputable def SB (m : ℕ) : ℂ := ∑ k ∈ range m, (T (5 * k + 2) - T (5 * k + 3))

/-- `Σ_{k<m} (log(5k+4)·(5k+4)^{-c} − log(5k+1)·(5k+1)^{-c})`. -/
noncomputable def SA1 (m : ℕ) : ℂ :=
  ∑ k ∈ range m, ((Real.log ((5 * k + 4 : ℕ) : ℝ) : ℂ) * T (5 * k + 4) -
    (Real.log ((5 * k + 1 : ℕ) : ℝ) : ℂ) * T (5 * k + 1))

/-- `Σ_{k<m} (log(5k+3)·(5k+3)^{-c} − log(5k+2)·(5k+2)^{-c})`. -/
noncomputable def SB1 (m : ℕ) : ℂ :=
  ∑ k ∈ range m, ((Real.log ((5 * k + 3 : ℕ) : ℝ) : ℂ) * T (5 * k + 3) -
    (Real.log ((5 * k + 2 : ℕ) : ℝ) : ℂ) * T (5 * k + 2))

/-- `Σ_{k<m} (log²(5k+1)·|(5k+1)^{-c}| + log²(5k+4)·|(5k+4)^{-c}|)`. -/
noncomputable def D2A (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (Real.log ((5 * k + 1 : ℕ) : ℝ) ^ 2 * ‖T (5 * k + 1)‖ +
    Real.log ((5 * k + 4 : ℕ) : ℝ) ^ 2 * ‖T (5 * k + 4)‖)

/-- `Σ_{k<m} (log²(5k+2)·|(5k+2)^{-c}| + log²(5k+3)·|(5k+3)^{-c}|)`. -/
noncomputable def D2B (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (Real.log ((5 * k + 2 : ℕ) : ℝ) ^ 2 * ‖T (5 * k + 2)‖ +
    Real.log ((5 * k + 3 : ℕ) : ℝ) ^ 2 * ‖T (5 * k + 3)‖)

/-- `up L T'` bounds `x²·|z|·S`, if `L` holds `x` and `T'` holds `z`. -/
theorem up_le {L : B} {T' : CB} {x : ℝ} {z : ℂ} (hL : L.has x) (hT : T'.has z) :
    x ^ 2 * ‖z‖ * (S : ℝ) ≤ (up L T' : ℕ) := by
  have hS := S_pos
  have h1 := abs_le_of_has hL
  have h2 := abs_le_of_has hT.1
  have h3 := abs_le_of_has hT.2
  have h4 : ‖z‖ * (S : ℝ) ≤ ((T'.re.c.natAbs + T'.re.e + T'.im.c.natAbs + T'.im.e : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right (Complex.norm_le_abs_re_add_abs_im z) hS.le
    push_cast at h2 h3 ⊢
    linarith
  have hSS : 0 < S * S := Nat.mul_pos S_pos' S_pos'
  have h5 := lt_natdiv_add_one
    ((L.c.natAbs + L.e) ^ 2 * (T'.re.c.natAbs + T'.re.e + T'.im.c.natAbs + T'.im.e)) hSS
  have h6 : (|x| * (S : ℝ)) ^ 2 * (‖z‖ * (S : ℝ)) ≤
      (((L.c.natAbs + L.e : ℕ) : ℝ)) ^ 2 *
        ((T'.re.c.natAbs + T'.re.e + T'.im.c.natAbs + T'.im.e : ℕ) : ℝ) :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) h4 (by positivity) (by positivity)
  have e : x ^ 2 * ‖z‖ * (S : ℝ) = (|x| * (S : ℝ)) ^ 2 * (‖z‖ * (S : ℝ)) / ((S * S : ℕ) : ℝ) := by
    rw [mul_pow, sq_abs]
    push_cast
    field_simp
  rw [e]
  unfold up
  have h7 : (|x| * (S : ℝ)) ^ 2 * (‖z‖ * (S : ℝ)) / ((S * S : ℕ) : ℝ) ≤
      ((((L.c.natAbs + L.e) ^ 2 * (T'.re.c.natAbs + T'.re.e + T'.im.c.natAbs + T'.im.e) : ℕ)) : ℝ) /
        ((S * S : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast at h6 ⊢
    exact h6
  push_cast at h5 h7 ⊢
  linarith

/-- The state `st` holds the sums over the blocks before `m`. -/
structure Inv (m : ℕ) (st : St) : Prop where
  /-- The logarithm of the next integer. -/
  L : st.L.has (Real.log ((5 * m + 1 : ℕ) : ℝ))
  /-- The sum over the classes `1` and `4`. -/
  A : st.A.has (SA m)
  /-- The sum over the classes `2` and `3`. -/
  B : st.B'.has (SB m)
  /-- The derivative's sum over the classes `1` and `4`. -/
  A1 : st.A1.has (SA1 m)
  /-- The derivative's sum over the classes `2` and `3`. -/
  B1 : st.B1.has (SB1 m)
  /-- The bound for the second derivative, classes `1` and `4`. -/
  d2a : D2A m * (S : ℝ) ≤ (st.d2a : ℝ)
  /-- The bound for the second derivative, classes `2` and `3`. -/
  d2b : D2B m * (S : ℝ) ≤ (st.d2b : ℝ)

theorem inv_init : Inv 0 init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [init, B.has]
  · simpa [init, SA] using chas_zero
  · simpa [init, SB] using chas_zero
  · simpa [init, SA1] using chas_zero
  · simpa [init, SB1] using chas_zero
  · simp [init, D2A]
  · simp [init, D2B]

theorem inv_step {m : ℕ} {st : St} (h : Inv m st) : Inv (m + 1) (step m st) := by
  have hL1 := h.L
  have hT1 : (term st.L).has (T (5 * m + 1)) := has_term (by omega) hL1
  have hL2 := has_log_succ (n := 5 * m + 1) (by omega) hL1
  have hT2 : (term (st.L.add (logStep (5 * m + 1)))).has (T (5 * m + 2)) := has_term (by omega) hL2
  have hL3 := has_log_succ (n := 5 * m + 2) (by omega) hL2
  have hT3 : (term ((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2)))).has (T (5 * m + 3)) :=
    has_term (by omega) hL3
  have hL4 := has_log_succ (n := 5 * m + 3) (by omega) hL3
  have hT4 : (term (((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2))).add
      (logStep (5 * m + 3)))).has (T (5 * m + 4)) := has_term (by omega) hL4
  have hL5 := has_log_succ (n := 5 * m + 4) (by omega) hL4
  have hL6 := has_log_succ (n := 5 * m + 5) (by omega) hL5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hL6
  · have := chas_sub (chas_add h.A hT1) hT4
    rw [SA, sum_range_succ, ← SA]
    have e : SA m + (T (5 * m + 1) - T (5 * m + 4)) = SA m + T (5 * m + 1) - T (5 * m + 4) := by ring
    rw [e]
    exact this
  · have := chas_sub (chas_add h.B hT2) hT3
    rw [SB, sum_range_succ, ← SB]
    have e : SB m + (T (5 * m + 2) - T (5 * m + 3)) = SB m + T (5 * m + 2) - T (5 * m + 3) := by ring
    rw [e]
    exact this
  · have := chas_add (chas_sub h.A1 (chas_smul hL1 hT1)) (chas_smul hL4 hT4)
    rw [SA1, sum_range_succ, ← SA1]
    have e : SA1 m + ((Real.log ((5 * m + 4 : ℕ) : ℝ) : ℂ) * T (5 * m + 4) -
        (Real.log ((5 * m + 1 : ℕ) : ℝ) : ℂ) * T (5 * m + 1)) =
        SA1 m - (Real.log ((5 * m + 1 : ℕ) : ℝ) : ℂ) * T (5 * m + 1) +
          (Real.log ((5 * m + 4 : ℕ) : ℝ) : ℂ) * T (5 * m + 4) := by ring
    rw [e]
    exact this
  · have := chas_add (chas_sub h.B1 (chas_smul hL2 hT2)) (chas_smul hL3 hT3)
    rw [SB1, sum_range_succ, ← SB1]
    have e : SB1 m + ((Real.log ((5 * m + 3 : ℕ) : ℝ) : ℂ) * T (5 * m + 3) -
        (Real.log ((5 * m + 2 : ℕ) : ℝ) : ℂ) * T (5 * m + 2)) =
        SB1 m - (Real.log ((5 * m + 2 : ℕ) : ℝ) : ℂ) * T (5 * m + 2) +
          (Real.log ((5 * m + 3 : ℕ) : ℝ) : ℂ) * T (5 * m + 3) := by ring
    rw [e]
    exact this
  · have u1 : Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 1)‖ * (S : ℝ) ≤ _ := up_le hL1 hT1
    have u4 : Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 4)‖ * (S : ℝ) ≤ _ := up_le hL4 hT4
    have h0 := h.d2a
    have key : D2A (m + 1) * (S : ℝ) ≤ (st.d2a : ℝ) + (up st.L (term st.L) : ℕ) +
        (up (((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2))).add (logStep (5 * m + 3)))
          (term (((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2))).add
            (logStep (5 * m + 3)))) : ℕ) := by
      rw [D2A, sum_range_succ, ← D2A]
      linarith
    refine key.trans (le_of_eq ?_)
    simp only [step, Nat.cast_add]
  · have u2 : Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 2)‖ * (S : ℝ) ≤ _ := up_le hL2 hT2
    have u3 : Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 3)‖ * (S : ℝ) ≤ _ := up_le hL3 hT3
    have h0 := h.d2b
    have key : D2B (m + 1) * (S : ℝ) ≤ (st.d2b : ℝ) +
        (up (st.L.add (logStep (5 * m + 1))) (term (st.L.add (logStep (5 * m + 1)))) : ℕ) +
        (up ((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2)))
          (term ((st.L.add (logStep (5 * m + 1))).add (logStep (5 * m + 2)))) : ℕ) := by
      rw [D2B, sum_range_succ, ← D2B]
      linarith
    refine key.trans (le_of_eq ?_)
    simp only [step, Nat.cast_add]

theorem inv_run : ∀ (n m : ℕ) (st : St), Inv m st → Inv (m + n) (run m n st)
  | 0, m, st, h => by simpa [run] using h
  | n + 1, m, st, h => by
    have h2 := inv_run n (m + 1) (step m st) (inv_step h)
    have e : m + (n + 1) = m + 1 + n := by ring
    rw [run_succ, e]
    exact h2

end DHBall
