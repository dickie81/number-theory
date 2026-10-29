/-
# Guth and Maynard's exponent for `ζ` on `7/10 + η ≤ σ ≤ 4/5`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `0 < η ≤ 1/100` there is `C ≥ 0` with `N(σ, T) ≤ C T^{(30/13)(1−σ)+9η}(log T)^{12}` for
`T ≥ 2` and `7/10 + η ≤ σ ≤ 4/5` (`nx_gm`). A window `U ≤ |γ| ≤ 2U` (`window_count_gm`) is counted with the detector
of `InghamDensity` at `X = ⌊U^{1/100}⌋`, `Y = U^{1/2}` (`ZetaHuxley.trichotomy7`). Its integral class is counted as
in `ZetaHuxley` (`class3_count_small` at `δ = 1/5`; exponent `2 − 2σ + 1/25`). Its polynomial classes are counted
with Guth and Maynard's large values estimate (`ZetaGMLV.gm_large_values`).
* `taylor_pick_dp`: a zero `β + iγ`, `β ≥ σ`, is moved to the line `Re s = σ`: `j^{−β} = P^{−δ}e^{−δ log(j/P)}j^{−σ}`,
  `δ = β − σ`, and the Taylor polynomial of degree `L − 1` (`Real.exp_bound`) leaves some
  `Σ_j b_j log(j/P)^l j^{−σ−iγ}`, `l < L`, at least a quarter of the block.
* `choose_m100`, `pow_piece_pick`: a power `m ≤ 77` of the block with `U^{10/13} ≤ (2P)^m ≤ U^{15/13}`, and a piece
  `(P^m(3/2)^i, P^m(3/2)^{i+1}]`, `i < 2m`, of its support, the shape `(6N/5, 9N/5]` of Guth and Maynard's key
  proposition.
* `piece_exp`, `piece_count`: on a piece of length `N`, `U^{10/13−η} ≤ N ≤ U^{15/13}`, Guth and Maynard's estimate
  at `σ − η` when `N^{18/5−4σ} ≤ U^{(30/13)(1−σ)}`, and otherwise the mean value theorem at well-spaced points
  (`LinnikPoints.large_values_points`), since `18/5 − 4σ ≤ (30/13)(1 − σ)(13/5 − 2σ)`. Both give
  `U^{(30/13)(1−σ)+8η}`.
* `poly_count_gm`, `class_poly_gm`: the coefficients of a piece are at most `d(n)^{2m}` (`LinnikPower.norm_powCo_le`),
  divided out with the divisor bound at `η/1000`; the blocks, Taylor terms and pieces number `O(log² U)`.
* `window_classes_gm`, `window_count_gm`: as `ZetaHuxley.window_classes_huxley` and `window_count_huxley`, for all
  large `U` (`eventually_gm`, with `ev_log_pow`).

The file imports `LinnikCGLLV.lean`, `ZetaHuxley.lean` and `ZetaGMLV.lean`.
-/import LinnikCGLLV
import ZetaHuxley
import ZetaGMLV

open Complex Real Finset Filter

noncomputable section

namespace ZetaGMWin

open DirMean LinnikCGLLV LinnikPower ZetaFourth ZetaKernel InghamDensity ShortWeil PsiOmega WeilForm WeilTest
  ZetaIngham LinnikHuxley ZetaHuxley


/-- **A block off the line.** For `S ⊆ (P, 2P]`, `0 ≤ δ ≤ 1`, `V > 0` and `L ≥ 1` with
`2Σ_{j∈S}|b_j|j^{−σ} ≤ (V/4)L!`, if `|Σ_{j∈S} b_jj^{−σ−δ}j^{−iγ}| ≥ V` then
`|Σ_{j∈S} b_j log(j/P)^l j^{−σ}j^{−iγ}| ≥ V/4` for some `l < L`. -/
theorem taylor_pick_dp {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) (b : ℕ → ℂ) {σ δ γ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {V : ℝ} (hV : 0 < V) {L : ℕ} (hL : 1 ≤ L)
    (htail : 2 * ∑ j ∈ S, ‖b j‖ * (j : ℝ) ^ (-σ) ≤ V / 4 * L.factorial)
    (hbig : V ≤ ‖dp S (fun j => b j * (((j : ℝ) ^ (-(σ + δ)) : ℝ) : ℂ)) γ‖) :
    ∃ l < L, V / 4 ≤ ‖dp S (fun j => b j * ((Real.log ((j : ℝ) / P) ^ l : ℝ) : ℂ) *
      (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖ := by
  classical
  by_contra hcon
  push Not at hcon
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hSpos : ∀ j ∈ S, 0 < j := fun j hj => by have := (mem_Ioc.1 (hS hj)).1; omega
  set x : ℕ → ℝ := fun j => Real.log ((j : ℝ) / P) with hxdef
  have hx : ∀ j ∈ S, 0 ≤ x j ∧ x j ≤ 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Ioc.1 (hS hj)
    have hj1 : (P : ℝ) < j := by exact_mod_cast h1
    have hj2 : (j : ℝ) ≤ 2 * P := by exact_mod_cast h2
    have hjpos : (0 : ℝ) < j := by linarith
    constructor
    · exact Real.log_nonneg (by rw [le_div_iff₀ hPpos]; linarith)
    · calc x j ≤ Real.log 2 := Real.log_le_log (div_pos hjpos hPpos) (by rw [div_le_iff₀ hPpos]; linarith)
        _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
  -- the kernel `u_j = b_jj^{−σ}e^{−iγ log j}`
  set e : ℕ → ℂ := fun j => Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) with hedef
  have he1 : ∀ j, ‖e j‖ = 1 := fun j => norm_exp_neg_I_mul _
  set u : ℕ → ℂ := fun j => b j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ) * e j with hudef
  have hu : ∀ j, ‖u j‖ = ‖b j‖ * (j : ℝ) ^ (-σ) := fun j => by
    rw [hudef, norm_mul, norm_mul, he1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  -- the factor `P^{−δ}`, at most `1`
  set c : ℝ := (P : ℝ) ^ (-δ) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hP) (by linarith)
  -- the Taylor polynomial and its remainder
  set Q : ℕ → ℝ := fun j => ∑ l ∈ range L, (-δ * x j) ^ l / l.factorial with hQdef
  set r : ℕ → ℝ := fun j => Real.exp (-δ * x j) - Q j with hrdef
  have hr : ∀ j ∈ S, |r j| ≤ 2 / L.factorial := by
    intro j hj
    have hxj := hx j hj
    have hy : |-δ * x j| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have hb := Real.exp_bound hy (n := L) (by omega)
    have hL' : ((L.succ : ℕ) : ℝ) / ((L.factorial : ℕ) * L) ≤ 2 / L.factorial := by
      have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hf : (0 : ℝ) < (L.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos L
      rw [div_le_div_iff₀ (by positivity) hf]
      push_cast
      nlinarith
    calc |r j| ≤ |-δ * x j| ^ L * ((L.succ : ℕ) / ((L.factorial : ℕ) * L : ℝ)) := by
          simpa [hrdef, hQdef] using hb
      _ ≤ 1 * (2 / L.factorial) :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hy) hL' (by positivity) zero_le_one
      _ = 2 / L.factorial := one_mul _
  -- the sum, rewritten
  have hsplit : ∀ j ∈ S, b j * (((j : ℝ) ^ (-(σ + δ)) : ℝ) : ℂ) * e j =
      (c : ℂ) * (((Q j : ℝ) : ℂ) * u j + ((r j : ℝ) : ℂ) * u j) := by
    intro j hj
    have hjr : (0 : ℝ) < j := by exact_mod_cast hSpos j hj
    have h1 : (j : ℝ) ^ (-(σ + δ)) = (j : ℝ) ^ (-σ) * (j : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hjr]; ring_nf
    rw [h1, rpow_neg_split (hSpos j hj) (by omega : 0 < P) δ]
    have hexp : Real.exp (-δ * Real.log ((j : ℝ) / P)) = Q j + r j := by simp [hrdef, hxdef]
    rw [hexp]; simp only [hudef, hcdef]; push_cast; ring
  have hsum : dp S (fun j => b j * (((j : ℝ) ^ (-(σ + δ)) : ℝ) : ℂ)) γ =
      (c : ℂ) * (∑ l ∈ range L, (((-δ) ^ l / l.factorial : ℝ) : ℂ) *
        dp S (fun j => b j * ((Real.log ((j : ℝ) / P) ^ l : ℝ) : ℂ) * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ +
        ∑ j ∈ S, ((r j : ℝ) : ℂ) * u j) := by
    have hQ : ∀ j, ((Q j : ℝ) : ℂ) * u j = ∑ l ∈ range L, (((-δ) ^ l / l.factorial : ℝ) : ℂ) *
        (b j * ((Real.log ((j : ℝ) / P) ^ l : ℝ) : ℂ) * (((j : ℝ) ^ (-σ) : ℝ) : ℂ) * e j) := by
      intro j
      simp only [hQdef, hudef, hxdef]
      push_cast
      rw [sum_mul]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_pow]; ring
    unfold dp
    rw [sum_congr rfl hsplit, ← mul_sum, sum_add_distrib, sum_congr rfl fun j _ => hQ j, sum_comm]
    congr 2
    exact sum_congr rfl fun l _ => by rw [mul_sum]
  -- the bounds
  have hD : ∀ l ∈ range L, ‖(((-δ) ^ l / l.factorial : ℝ) : ℂ) *
      dp S (fun j => b j * ((Real.log ((j : ℝ) / P) ^ l : ℝ) : ℂ) * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖ ≤
      δ ^ l / l.factorial * (V / 4) := by
    intro l hl
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_nonneg hδ0,
      Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hcon l (mem_range.1 hl)).le (by positivity)
  have hexp : ∑ l ∈ range L, δ ^ l / l.factorial ≤ 11 / 4 := by
    have h1 := Real.sum_le_exp_of_nonneg hδ0 L
    have h2 : Real.exp δ ≤ Real.exp 1 := Real.exp_le_exp.2 hδ1
    have h3 := Real.exp_one_lt_d9
    linarith
  have hT1 : ‖∑ l ∈ range L, (((-δ) ^ l / l.factorial : ℝ) : ℂ) *
      dp S (fun j => b j * ((Real.log ((j : ℝ) / P) ^ l : ℝ) : ℂ) * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖ ≤
      11 / 4 * (V / 4) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum hD).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right hexp (by positivity)
  have hT2 : ‖∑ j ∈ S, ((r j : ℝ) : ℂ) * u j‖ ≤ V / 4 := by
    refine (norm_sum_le _ _).trans ?_
    have hf : (0 : ℝ) < L.factorial := by exact_mod_cast Nat.factorial_pos L
    calc ∑ j ∈ S, ‖((r j : ℝ) : ℂ) * u j‖ ≤ ∑ j ∈ S, 2 / L.factorial * (‖b j‖ * (j : ℝ) ^ (-σ)) := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hu]
          exact mul_le_mul_of_nonneg_right (hr j hj) (by positivity)
      _ = 2 * (∑ j ∈ S, ‖b j‖ * (j : ℝ) ^ (-σ)) / L.factorial := by rw [← mul_sum]; ring
      _ ≤ V / 4 * L.factorial / L.factorial := by gcongr
      _ = V / 4 := by field_simp
  have hfinal : ‖dp S (fun j => b j * (((j : ℝ) ^ (-(σ + δ)) : ℝ) : ℂ)) γ‖ ≤ 15 / 16 * V := by
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc c * ‖_ + _‖ ≤ 1 * (11 / 4 * (V / 4) + V / 4) :=
          mul_le_mul hc1 ((norm_add_le _ _).trans (add_le_add hT1 hT2)) (norm_nonneg _) zero_le_one
      _ = 15 / 16 * V := by ring
  linarith


/-- **The power of a block** for `x ≥ Q^{1/100}`: for `0 < a ≤ 77/100` some `m` with `Q^a ≤ x^m` has `1 ≤ m ≤ 77`
and `x^m ≤ max(x², Q^{3a/2})` (`LinnikHuxley.choose_m` with `1/100` in place of `1/25`). -/
lemma choose_m100 {Q a x : ℝ} (hQ : 1 < Q) (ha : 0 < a) (ha77 : a ≤ 77 / 100) (hx : Q ^ (1 / 100 : ℝ) ≤ x) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 77 ∧ Q ^ a ≤ x ^ m ∧ x ^ m ≤ max (x ^ 2) (Q ^ (3 * a / 2)) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hQ.le (by norm_num)) hx
  have h77 : Q ^ a ≤ x ^ 77 := by
    calc Q ^ a ≤ Q ^ (77 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ.le ha77
      _ = (Q ^ (1 / 100 : ℝ)) ^ (77 : ℕ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
      _ ≤ x ^ 77 := pow_le_pow_left₀ (by positivity) hx 77
  have hex : ∃ m : ℕ, Q ^ a ≤ x ^ m := ⟨77, h77⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex h77, Nat.find_spec hex, ?_⟩
  · by_contra h0
    have hm0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hm0, pow_zero] at this
    exact absurd this (not_le.2 (Real.one_lt_rpow hQ ha))
  · set m := Nat.find hex with hm
    rcases le_or_gt m 2 with h2 | h3
    · exact le_max_of_le_left (pow_le_pow_right₀ hx1 h2)
    · refine le_max_of_le_right ?_
      have h1 : x ^ (m - 1) < Q ^ a := not_le.1 (Nat.find_min hex (by omega : m - 1 < m))
      have h2 : x ^ 2 ≤ x ^ (m - 1) := pow_le_pow_right₀ hx1 (by omega)
      have e1 : (x ^ m) ^ 2 = (x ^ (m - 1)) ^ 2 * x ^ 2 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
      have e2 : (Q ^ (3 * a / 2)) ^ 2 = (Q ^ a) ^ 2 * Q ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast (Q ^ a), ← Real.rpow_mul hQ0.le,
          ← Real.rpow_add hQ0]
        congr 1; push_cast; ring
      have h3 : (x ^ m) ^ 2 ≤ (Q ^ (3 * a / 2)) ^ 2 := by
        rw [e1, e2]
        have hxm0 : 0 ≤ x ^ (m - 1) := by positivity
        exact mul_le_mul (pow_le_pow_left₀ hxm0 h1.le 2) (h2.trans h1.le) (by positivity) (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h3

/-- `Σ_{j∈S} c_jj^{−σ}j^{−iγ}` is `pv S c χ₁ (σ + iγ)` for `S` of positive integers. -/
lemma dp_eq_pv (S : Finset ℕ) (hS : ∀ j ∈ S, 0 < j) (c : ℕ → ℂ) (σ γ : ℝ) :
    dp S (fun j => c j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ = pv S c χ₁ ((σ : ℂ) + γ * I) := by
  unfold dp pv
  refine sum_congr rfl fun j hj => ?_
  have hn0 : (j : ℂ) ≠ 0 := by exact_mod_cast (hS j hj).ne'
  have hnr : (0 : ℝ) < j := by exact_mod_cast hS j hj
  have hc : (j : ℂ) ^ (-((σ : ℂ) + γ * I))
      = (((j : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
    have hlog : Complex.log (j : ℂ) = (Real.log j : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
    rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hc, χ₁_apply]; ring

/-! ### The pieces of a power -/

open Classical in
/-- The index of the piece `(P^m(3/2)^i, P^m(3/2)^{i+1}]` holding `n`. -/
def pieceIdx (P m n : ℕ) : ℕ :=
  if h : ∃ i : ℕ, (n : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ (i + 1) then Nat.find h else 0

lemma pieceIdx_exists {P m : ℕ} (hP : 1 ≤ P) (n : ℕ) :
    ∃ i : ℕ, (n : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ (i + 1) := by
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (n : ℝ) (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨i, ?_⟩
  have hPm : (1 : ℝ) ≤ (P : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hP)
  have h1 : (3 / 2 : ℝ) ^ i ≤ (3 / 2) ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℝ) ≤ (3 / 2) ^ (i + 1) := by positivity
  nlinarith

/-- The piece of `n`: `n ≤ P^m(3/2)^{i+1}`, and `n > P^m(3/2)^i` when `i ≥ 1`. -/
lemma pieceIdx_spec {P m : ℕ} (hP : 1 ≤ P) (n : ℕ) :
    (n : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ (pieceIdx P m n + 1) ∧
      (1 ≤ pieceIdx P m n → (P : ℝ) ^ m * (3 / 2) ^ pieceIdx P m n < n) := by
  have hex := pieceIdx_exists (m := m) hP n
  have hidx : pieceIdx P m n = Nat.find hex := by unfold pieceIdx; rw [dite_eq_left hex]
  rw [hidx]
  refine ⟨Nat.find_spec hex, fun h1 => ?_⟩
  have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
  exact not_le.1 hmin

/-- Up to `(2P)^m` there are at most `2m` pieces: `(2P)^m ≤ P^m(9/4)^m = P^m(3/2)^{2m}`. -/
lemma pieceIdx_lt {P m n : ℕ} (hP : 1 ≤ P) (hm : 1 ≤ m) (hn : n ≤ (2 * P) ^ m) : pieceIdx P m n < 2 * m := by
  have hex := pieceIdx_exists (m := m) hP n
  have hidx : pieceIdx P m n = Nat.find hex := by unfold pieceIdx; rw [dite_eq_left hex]
  rw [hidx]
  have hle : Nat.find hex ≤ 2 * m - 1 := Nat.find_le (by
    rw [show 2 * m - 1 + 1 = 2 * m by omega]
    have h1 : (n : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ m := by exact_mod_cast hn
    have h2 : ((2 * P : ℕ) : ℝ) ^ m ≤ (P : ℝ) ^ m * (3 / 2) ^ (2 * m) := by
      rw [pow_mul, show ((3 : ℝ) / 2) ^ 2 = 9 / 4 by norm_num, ← mul_pow]
      push_cast
      have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) m
    linarith)
  omega

/-- The `i`-th piece of the support of the `m`-th power. -/
def pieceS (S : Finset ℕ) (P m i : ℕ) : Finset ℕ := (powSupp S m).filter fun n => pieceIdx P m n = i

/-- A member `n` of the `i`-th piece has `P^m(3/2)^i < n ≤ P^m(3/2)^{i+1}` and `n ≤ (2P)^m`. -/
lemma mem_pieceS {S : Finset ℕ} {P m i n : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) (hm : 1 ≤ m)
    (hn : n ∈ pieceS S P m i) :
    (P : ℝ) ^ m * (3 / 2) ^ i < n ∧ (n : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ (i + 1) ∧
      (n : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ m := by
  obtain ⟨hn1, hn2⟩ := mem_filter.1 hn
  have hI := mem_Ioc.1 (powSupp_sub hS hm hn1)
  have hspec := pieceIdx_spec (m := m) hP n
  rw [hn2] at hspec
  refine ⟨?_, hspec.1, by exact_mod_cast hI.2⟩
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    rw [pow_zero, mul_one]
    exact_mod_cast hI.1
  · exact hspec.2 h1

/-- **A piece of a power.** For `S ⊆ (P, 2P]`, `m ≥ 1` and `V > 0`, if `|Σ_{j∈S}c_jj^{−σ}j^{−iγ}| ≥ V` then
`|Σ_{n∈S_i}c^{(m)}_nn^{−σ}n^{−iγ}| ≥ V^m/(2m)` for some piece `S_i` of the support of the `m`-th power, `i < 2m`. -/
lemma pow_piece_pick {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) (c : ℕ → ℂ) {m : ℕ}
    (hm : 1 ≤ m) (σ γ : ℝ) {V : ℝ} (hV : 0 < V)
    (hbig : V ≤ ‖dp S (fun j => c j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖) :
    ∃ i < 2 * m, V ^ m / (2 * m) ≤
      ‖dp (pieceS S P m i) (fun n => powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖ := by
  have hSpos : ∀ j ∈ S, 0 < j := fun j hj => by have := (mem_Ioc.1 (hS hj)).1; omega
  have hTpos : ∀ n ∈ powSupp S m, 0 < n := fun n hn => by
    have := (mem_Ioc.1 (powSupp_sub hS hm hn)).1
    have : 1 ≤ P ^ m := Nat.one_le_pow _ _ (by omega)
    omega
  have hpow : dp S (fun j => c j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ ^ m =
      ∑ i ∈ range (2 * m), dp (pieceS S P m i) (fun n => powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) γ := by
    rw [dp_eq_pv S hSpos, pv_pow, ← dp_eq_pv _ hTpos]
    unfold dp pieceS
    refine (sum_fiberwise_of_maps_to (fun n hn => mem_range.2 (pieceIdx_lt hP hm ?_)) _).symm
    exact (mem_Ioc.1 (powSupp_sub hS hm hn)).2
  by_contra hcon
  push Not at hcon
  have h1 : V ^ m ≤ ‖dp S (fun j => c j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) γ ^ m‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ hV.le hbig m
  rw [hpow] at h1
  have h2 : ‖∑ i ∈ range (2 * m), dp (pieceS S P m i)
      (fun n => powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) γ‖ < ∑ _i ∈ range (2 * m), V ^ m / (2 * m) :=
    (norm_sum_le _ _).trans_lt
      (sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun i hi => hcon i (mem_range.1 hi))
  rw [sum_const, card_range, nsmul_eq_mul] at h2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : ((2 * m : ℕ) : ℝ) * (V ^ m / (2 * m)) = V ^ m := by push_cast; field_simp
  linarith


/-- **The exponents of one piece.** For `0 < η ≤ 1/100`, `7/10 + η ≤ σ ≤ 4/5`, `U ≥ 1` and
`U^{10/13−η} ≤ N ≤ U^{15/13}`, with `σ′ = σ − η` and `E = (30/13)(1 − σ)`: either
`UN^{12/5−4σ′} + N^{18/5−4σ′} ≤ 2U^{E+6η}` (when `N^{18/5−4σ} ≤ U^E`), or `(U + N)N^{1−2σ′} ≤ 2U^{E+6η}`
(otherwise, since `(18/5 − 4σ) ≤ E(13/5 − 2σ)`). -/
lemma piece_exp {η σ U N : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) (hσ : 7 / 10 + η ≤ σ) (hσ1 : σ ≤ 4 / 5)
    (hU : 1 ≤ U) (hN1 : U ^ (10 / 13 - η) ≤ N) (hN2 : N ≤ U ^ (15 / 13 : ℝ)) :
    U * N ^ (12 / 5 - 4 * (σ - η)) + N ^ (18 / 5 - 4 * (σ - η)) ≤ 2 * U ^ (30 / 13 * (1 - σ) + 6 * η) ∨
      (U + N) * N ^ (1 - 2 * (σ - η)) ≤ 2 * U ^ (30 / 13 * (1 - σ) + 6 * η) := by
  have hU0 : 0 < U := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hU0 _) hN1
  set E := 30 / 13 * (1 - σ) with hE
  have hNx : ∀ x : ℝ, 0 ≤ x → N ^ x ≤ U ^ (15 / 13 * x) := fun x hx => by
    calc N ^ x ≤ (U ^ (15 / 13 : ℝ)) ^ x := Real.rpow_le_rpow hN0.le hN2 hx
      _ = U ^ (15 / 13 * x) := by rw [← Real.rpow_mul hU0.le]
  have hmono : ∀ a b : ℝ, a ≤ b → U ^ a ≤ U ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le hU h
  rcases le_or_gt (N ^ (18 / 5 - 4 * σ)) (U ^ E) with hA | hB
  · left
    have h4η : N ^ (4 * η) ≤ U ^ (60 / 13 * η) := by
      have := hNx (4 * η) (by positivity)
      rwa [show 15 / 13 * (4 * η) = 60 / 13 * η by ring] at this
    -- `N^{12/5−4σ} ≤ U^{(10/13−η)(12/5−4σ)}`: `N ≥ U^{10/13−η}` and `12/5 − 4σ < 0`
    have h12 : N ^ (12 / 5 - 4 * σ) ≤ U ^ ((10 / 13 - η) * (12 / 5 - 4 * σ)) := by
      calc N ^ (12 / 5 - 4 * σ) ≤ (U ^ (10 / 13 - η)) ^ (12 / 5 - 4 * σ) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU0 _) hN1 (by linarith)
        _ = U ^ ((10 / 13 - η) * (12 / 5 - 4 * σ)) := by rw [← Real.rpow_mul hU0.le]
    have hexp1 : 1 + (10 / 13 - η) * (12 / 5 - 4 * σ) + 60 / 13 * η ≤ E + 6 * η := by
      rw [hE]; nlinarith [mul_le_mul_of_nonneg_left hσ1 hη.le]
    have t1 : U * N ^ (12 / 5 - 4 * (σ - η)) ≤ U ^ (E + 6 * η) := by
      rw [show 12 / 5 - 4 * (σ - η) = (12 / 5 - 4 * σ) + 4 * η by ring, Real.rpow_add hN0]
      calc U * (N ^ (12 / 5 - 4 * σ) * N ^ (4 * η))
          ≤ U ^ (1 : ℝ) * (U ^ ((10 / 13 - η) * (12 / 5 - 4 * σ)) * U ^ (60 / 13 * η)) := by
            rw [Real.rpow_one]; gcongr
        _ = U ^ (1 + (10 / 13 - η) * (12 / 5 - 4 * σ) + 60 / 13 * η) := by
            rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, add_assoc]
        _ ≤ U ^ (E + 6 * η) := hmono _ _ hexp1
    have t2 : N ^ (18 / 5 - 4 * (σ - η)) ≤ U ^ (E + 6 * η) := by
      rw [show 18 / 5 - 4 * (σ - η) = (18 / 5 - 4 * σ) + 4 * η by ring, Real.rpow_add hN0]
      calc N ^ (18 / 5 - 4 * σ) * N ^ (4 * η) ≤ U ^ E * U ^ (60 / 13 * η) := by gcongr
        _ = U ^ (E + 60 / 13 * η) := by rw [← Real.rpow_add hU0]
        _ ≤ U ^ (E + 6 * η) := hmono _ _ (by linarith)
    linarith
  · right
    set a := 18 / 5 - 4 * σ with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have hE0 : 0 < U ^ E := Real.rpow_pos_of_pos hU0 _
    have hr : N ^ (1 - 2 * σ) = (N ^ a) ^ (-(2 * σ - 1) / a) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; field_simp; ring
    have h1 : (N ^ a) ^ (-(2 * σ - 1) / a) ≤ (U ^ E) ^ (-(2 * σ - 1) / a) :=
      Real.rpow_le_rpow_of_nonpos hE0 hB.le (div_nonpos_of_nonpos_of_nonneg (by linarith) ha0.le)
    have key : a ≤ E * (a + (2 * σ - 1)) := by
      rw [hE, ha]; nlinarith [sq_nonneg (σ - 43 / 60)]
    have hexp : 1 + E * (-(2 * σ - 1) / a) ≤ E := by
      calc 1 + E * (-(2 * σ - 1) / a) = (a - E * (2 * σ - 1)) / a := by field_simp; ring
        _ ≤ E := (div_le_iff₀ ha0).2 (by linarith)
    have t1 : U * N ^ (1 - 2 * σ) ≤ U ^ E := by
      rw [hr]
      calc U * (N ^ a) ^ (-(2 * σ - 1) / a) ≤ U ^ (1 : ℝ) * (U ^ E) ^ (-(2 * σ - 1) / a) := by
            rw [Real.rpow_one]; gcongr
        _ = U ^ (1 + E * (-(2 * σ - 1) / a)) := by rw [← Real.rpow_mul hU0.le, ← Real.rpow_add hU0]
        _ ≤ U ^ E := hmono _ _ hexp
    have t2 : N * N ^ (1 - 2 * σ) ≤ U ^ E := by
      have e : N * N ^ (1 - 2 * σ) = N ^ (2 - 2 * σ) := by
        rw [show (2 : ℝ) - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hN0, Real.rpow_one]
      rw [e]
      calc N ^ (2 - 2 * σ) ≤ U ^ (15 / 13 * (2 - 2 * σ)) := hNx _ (by linarith)
        _ = U ^ E := by rw [hE]; congr 1; ring
    have h2η : N ^ (2 * η) ≤ U ^ (30 / 13 * η) := by
      have := hNx (2 * η) (by positivity)
      rwa [show 15 / 13 * (2 * η) = 30 / 13 * η by ring] at this
    have hs : N ^ (1 - 2 * (σ - η)) = N ^ (1 - 2 * σ) * N ^ (2 * η) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hUE : U ^ E * U ^ (30 / 13 * η) ≤ U ^ (E + 6 * η) := by
      rw [← Real.rpow_add hU0]; exact hmono _ _ (by linarith)
    rw [hs]
    have hN2η : 0 ≤ N ^ (2 * η) := by positivity
    calc (U + N) * (N ^ (1 - 2 * σ) * N ^ (2 * η))
        = (U * N ^ (1 - 2 * σ) + N * N ^ (1 - 2 * σ)) * N ^ (2 * η) := by ring
      _ ≤ (U ^ E + U ^ E) * U ^ (30 / 13 * η) := by gcongr
      _ = 2 * (U ^ E * U ^ (30 / 13 * η)) := by ring
      _ ≤ 2 * U ^ (E + 6 * η) := by gcongr

/-- The bound of `ZetaGMLV.gm_large_values` with constant `C` at exponent `η`. -/
def GMBound (C η : ℝ) : Prop :=
  ∀ {ι : Type} (R : Finset ι) (x : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (c : ℕ → ℂ),
    0 ≤ T → 1 ≤ N → 7 / 10 ≤ σ → σ ≤ 4 / 5 → (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) →
    (∀ n, ‖c n‖ ≤ 1) → (∀ r ∈ R, |x r| ≤ T) → (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |x r - x r'|) →
    (∀ r ∈ R, N ^ σ / 6 ≤ ‖dp S c (x r)‖) →
    (R.card : ℝ) ≤ C * N ^ η * (T * N ^ (12 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ))

/-- **One piece.** Given the constant `C₁` of `ZetaGMLV.gm_large_values` at `0 < η ≤ 1/100`: for
`7/10 + η ≤ σ ≤ 4/5`, `U ≥ 1`, `U^{10/13−η} ≤ N ≤ U^{15/13}`, `N ≥ 10/3`, `(1 + log 4N)(2 + log²4N) ≤ U^η`,
`S ⊆ (6N/5, 9N/5]`, `|c_n| ≤ 1` and points `|x_r| ≤ 2U` at least `1` apart with `|Σ_{n∈S}c_nn^{−ix_r}| ≥ N^{σ−η}/6`,
`|R| ≤ (4C₁ + 864)U^{(30/13)(1−σ)+8η}`: Guth and Maynard's estimate when `N^{18/5−4σ} ≤ U^{(30/13)(1−σ)}`, and
otherwise the mean value theorem (`LinnikPoints.large_values_points`), by `piece_exp`. -/
lemma piece_count {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : GMBound C₁ η)
    {σ U N : ℝ} (hσ : 7 / 10 + η ≤ σ) (hσ1 : σ ≤ 4 / 5) (hU : 1 ≤ U) (hN1 : U ^ (10 / 13 - η) ≤ N)
    (hN2 : N ≤ U ^ (15 / 13 : ℝ)) (hN3 : 10 / 3 ≤ N)
    (hLg : (1 + Real.log (4 * N)) * (2 + Real.log (4 * N) ^ 2) ≤ U ^ η)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 6 / 5 * N < (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1)
    {ι : Type} (R : Finset ι) (x : ι → ℝ) (hx : ∀ r ∈ R, |x r| ≤ 2 * U)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |x r - x r'|)
    (hbig : ∀ r ∈ R, N ^ (σ - η) / 6 ≤ ‖dp S c (x r)‖) :
    (R.card : ℝ) ≤ (4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η) := by
  have hU0 : 0 < U := by linarith
  have hN0 : 0 < N := by linarith
  set E := 30 / 13 * (1 - σ) with hE
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hUE8 : 0 ≤ U ^ (E + 8 * η) := by positivity
  rcases piece_exp hη hη1 hσ hσ1 hU hN1 hN2 with hA | hB
  · -- Guth and Maynard
    have hNη : N ^ η ≤ U ^ (2 * η) := by
      calc N ^ η ≤ (U ^ (15 / 13 : ℝ)) ^ η := Real.rpow_le_rpow hN0.le hN2 hη.le
        _ = U ^ (15 / 13 * η) := by rw [← Real.rpow_mul hU0.le]
        _ ≤ U ^ (2 * η) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    have h := hC₁ R x (2 * U) N (σ - η) S c (by positivity) (by linarith) (by linarith) (by linarith)
      (fun n hn => ⟨(hS n hn).1.le, (hS n hn).2⟩) hc hx hsep hbig
    have hb0 : 0 ≤ N ^ (18 / 5 - 4 * (σ - η)) := by positivity
    calc (R.card : ℝ) ≤ C₁ * N ^ η * (2 * U * N ^ (12 / 5 - 4 * (σ - η)) + N ^ (18 / 5 - 4 * (σ - η))) := h
      _ ≤ C₁ * U ^ (2 * η) * (2 * (U * N ^ (12 / 5 - 4 * (σ - η)) + N ^ (18 / 5 - 4 * (σ - η)))) := by
          gcongr; linarith
      _ ≤ C₁ * U ^ (2 * η) * (2 * (2 * U ^ (E + 6 * η))) := by gcongr
      _ = 4 * C₁ * (U ^ (2 * η) * U ^ (E + 6 * η)) := by ring
      _ = 4 * C₁ * U ^ (E + 8 * η) := by rw [← Real.rpow_add hU0]; congr 2; ring
      _ ≤ (4 * C₁ + 864) * U ^ (E + 8 * η) := by gcongr; linarith
  · -- the mean value theorem
    set P' := ⌊6 / 5 * N⌋₊ with hP'
    have hP'le : (P' : ℝ) ≤ 6 / 5 * N := Nat.floor_le (by positivity)
    have hP'gt : 6 / 5 * N - 1 < P' := by have := Nat.lt_floor_add_one (6 / 5 * N); linarith
    have hP'1 : (1 : ℝ) ≤ P' := by linarith
    have hSsub : S ⊆ Ioc P' (2 * P') := by
      intro n hn
      obtain ⟨h1, h2⟩ := hS n hn
      refine mem_Ioc.2 ⟨by exact_mod_cast (show (P' : ℝ) < n by linarith), ?_⟩
      have : (n : ℝ) ≤ ((2 * P' : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hlv := LinnikPoints.large_values_points hSsub c 1 (lo := -(2 * U) - 1 / 2) (hi := 2 * U + 1 / 2)
      (by linarith) R (fun _ => 1) x (fun r hr => by
        have := abs_le.1 (hx r hr); constructor <;> linarith)
      (fun r hr r' hr' hne _ => hsep r hr r' hr' hne)
    simp only [ZetaGMLV.one_apply_one, mul_one, Nat.cast_one, one_mul] at hlv
    have hcS : ∑ j ∈ S, ‖c j‖ ^ 2 ≤ 6 / 5 * N := by
      calc ∑ j ∈ S, ‖c j‖ ^ 2 ≤ ∑ _j ∈ S, (1 : ℝ) := sum_le_sum fun j _ => by
            have h1 := hc j
            have h2 := norm_nonneg (c j)
            nlinarith
        _ = (S.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ((Ioc P' (2 * P')).card : ℝ) := by exact_mod_cast card_le_card hSsub
        _ = (P' : ℝ) := by rw [Nat.card_Ioc, show 2 * P' - P' = P' by omega]
        _ ≤ 6 / 5 * N := hP'le
    have hl4 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    have hlP : Real.log P' ≤ Real.log (4 * N) := Real.log_le_log (by linarith) (by linarith)
    have hlP0 : 0 ≤ Real.log P' := Real.log_nonneg hP'1
    have hl2P : Real.log (2 * P') ≤ Real.log (4 * N) := Real.log_le_log (by linarith) (by linarith)
    have hl2P0 : 0 ≤ Real.log (2 * P') := Real.log_nonneg (by linarith)
    have hA1 : 2 * U + 1 / 2 - (-(2 * U) - 1 / 2) + 8 * P' * (1 + Real.log P') ≤
        (5 * U + 10 * N) * (1 + Real.log (4 * N)) := by
      have h1 : 8 * (P' : ℝ) * (1 + Real.log P') ≤ 10 * N * (1 + Real.log (4 * N)) := by
        have := mul_le_mul (show 8 * (P' : ℝ) ≤ 10 * N by linarith) (show 1 + Real.log P' ≤ 1 + Real.log (4 * N) by
          linarith) (by linarith) (by linarith)
        linarith
      have h2 : 4 * U + 1 ≤ 5 * U * (1 + Real.log (4 * N)) := by nlinarith
      nlinarith
    have hA2 : 2 + Real.log (2 * P') ^ 2 ≤ 2 + Real.log (4 * N) ^ 2 := by
      have := pow_le_pow_left₀ hl2P0 hl2P 2
      linarith
    have hlow : (R.card : ℝ) * (N ^ (σ - η) / 6) ^ 2 ≤ ∑ r ∈ R, ‖dp S c (x r)‖ ^ 2 := by
      calc (R.card : ℝ) * (N ^ (σ - η) / 6) ^ 2 = ∑ _r ∈ R, (N ^ (σ - η) / 6) ^ 2 := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ r ∈ R, ‖dp S c (x r)‖ ^ 2 :=
            sum_le_sum fun r hr => pow_le_pow_left₀ (by positivity) (hbig r hr) 2
    have hkey : (R.card : ℝ) * (N ^ (σ - η)) ^ 2 ≤ 432 * U ^ η * ((U + N) * N) := by
      have h1 := hlow.trans hlv
      have hB0 : 0 ≤ 2 * U + 1 / 2 - (-(2 * U) - 1 / 2) + 8 * P' * (1 + Real.log P') := by
        have : 0 ≤ 8 * (P' : ℝ) * (1 + Real.log P') := by positivity
        linarith
      have h2 : (2 * U + 1 / 2 - (-(2 * U) - 1 / 2) + 8 * P' * (1 + Real.log P')) * (2 + Real.log (2 * P') ^ 2) *
          ∑ j ∈ S, ‖c j‖ ^ 2 ≤ (5 * U + 10 * N) * ((1 + Real.log (4 * N)) * (2 + Real.log (4 * N) ^ 2)) *
            (6 / 5 * N) := by
        calc (2 * U + 1 / 2 - (-(2 * U) - 1 / 2) + 8 * P' * (1 + Real.log P')) * (2 + Real.log (2 * P') ^ 2) *
              ∑ j ∈ S, ‖c j‖ ^ 2 ≤ ((5 * U + 10 * N) * (1 + Real.log (4 * N))) * (2 + Real.log (4 * N) ^ 2) *
                (6 / 5 * N) := by gcongr
          _ = (5 * U + 10 * N) * ((1 + Real.log (4 * N)) * (2 + Real.log (4 * N) ^ 2)) * (6 / 5 * N) := by ring
      have h3 : (5 * U + 10 * N) * ((1 + Real.log (4 * N)) * (2 + Real.log (4 * N) ^ 2)) * (6 / 5 * N) ≤
          (5 * U + 10 * N) * U ^ η * (6 / 5 * N) := by gcongr
      have h4 : (R.card : ℝ) * (N ^ (σ - η) / 6) ^ 2 = (R.card : ℝ) * (N ^ (σ - η)) ^ 2 / 36 := by ring
      have h5 : (5 * U + 10 * N) * U ^ η * (6 / 5 * N) ≤ 12 * U ^ η * ((U + N) * N) := by
        have h0 : 0 ≤ U ^ η := by positivity
        have h6 : 6 * (U * N) + 12 * (N * N) ≤ 12 * ((U + N) * N) := by
          have := mul_nonneg hU0.le hN0.le
          linarith only [this]
        calc (5 * U + 10 * N) * U ^ η * (6 / 5 * N) = U ^ η * (6 * (U * N) + 12 * (N * N)) := by ring
          _ ≤ U ^ η * (12 * ((U + N) * N)) := mul_le_mul_of_nonneg_left h6 h0
          _ = 12 * U ^ η * ((U + N) * N) := by ring
      linarith only [h1, h2, h3, h4, h5]
    have hNs : (N ^ (σ - η)) ^ 2 * N ^ (1 - 2 * (σ - η)) = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
        show (σ - η) * ((2 : ℕ) : ℝ) + (1 - 2 * (σ - η)) = 1 by push_cast; ring, Real.rpow_one]
    have hNs0 : 0 < (N ^ (σ - η)) ^ 2 := by positivity
    have hcard : (R.card : ℝ) ≤ 432 * U ^ η * ((U + N) * N ^ (1 - 2 * (σ - η))) := by
      have e : 432 * U ^ η * ((U + N) * N ^ (1 - 2 * (σ - η))) * (N ^ (σ - η)) ^ 2 =
          432 * U ^ η * ((U + N) * N) := by
        calc 432 * U ^ η * ((U + N) * N ^ (1 - 2 * (σ - η))) * (N ^ (σ - η)) ^ 2
            = 432 * U ^ η * (U + N) * ((N ^ (σ - η)) ^ 2 * N ^ (1 - 2 * (σ - η))) := by ring
          _ = 432 * U ^ η * ((U + N) * N) := by rw [hNs]; ring
      rw [← e] at hkey
      exact le_of_mul_le_mul_right hkey hNs0
    calc (R.card : ℝ) ≤ 432 * U ^ η * ((U + N) * N ^ (1 - 2 * (σ - η))) := hcard
      _ ≤ 432 * U ^ η * (2 * U ^ (E + 6 * η)) := by gcongr
      _ = 864 * (U ^ η * U ^ (E + 6 * η)) := by ring
      _ = 864 * U ^ (E + 7 * η) := by rw [← Real.rpow_add hU0]; congr 2; ring
      _ ≤ 864 * U ^ (E + 8 * η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) (by norm_num)
      _ ≤ (4 * C₁ + 864) * U ^ (E + 8 * η) := by gcongr; linarith


set_option maxHeartbeats 1000000 in
/-- **One polynomial.** Given `C₁` with `GMBound C₁ η`, `0 < η ≤ 1/100`: for `7/10 + η ≤ σ ≤ 4/5`, `S ⊆ (P, 2P]` with
`U^{1/100} ≤ 2P` and `(2P)² ≤ U^{15/13}`, `|c_j| ≤ d(j)` on `S`, `0 < V ≤ 1`, and `U` large in the sense of `hW`,
`hc0`, `hN3` and `hLg`, points `|γ_r| ≤ 2U` at least `1` apart with `|Σ_{j∈S}c_jj^{−σ}j^{−iγ_r}| ≥ V` number at
most `154(4C₁ + 864)U^{(30/13)(1−σ)+8η}`: a power `m ≤ 77` with `U^{10/13} ≤ (2P)^m ≤ U^{15/13}` (`choose_m100`), a
piece of it (`pow_piece_pick`), the coefficients `c^{(m)}_nn^{−σ}` divided by
`C(η/1000)^{2m}((2P)^m)^{2mη/1000}(P^m(3/2)^i)^{−σ}` (`norm_powCo_le`, `card_divisors_le`), and `piece_count` at
`N = (5/6)P^m(3/2)^i`. -/
lemma poly_count_gm {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : GMBound C₁ η)
    {σ U : ℝ} (hσ : 7 / 10 + η ≤ σ) (hσ1 : σ ≤ 4 / 5) (hU : 1 < U)
    {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) (hPU : U ^ (1 / 100 : ℝ) ≤ ((2 * P : ℕ) : ℝ))
    (hPU2 : ((2 * P : ℕ) : ℝ) ^ 2 ≤ U ^ (15 / 13 : ℝ)) {c : ℕ → ℂ}
    (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ)) {V : ℝ} (hV : 0 < V) (hV1 : V ≤ 1)
    (hW : 154 * Cdiv (η / 1000) ^ 154 ≤ 6 * V ^ 77 * (5 / 6 * (1 / 2) ^ 77) ^ η * U ^ (η / 2))
    (hc0 : 6 / 5 * 2 ^ 77 ≤ U ^ η) (hN3 : 10 / 3 ≤ 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ))
    (hLg : (3 + 2 * Real.log U) * (2 + (2 + 2 * Real.log U) ^ 2) ≤ U ^ η)
    {ι : Type} (Rs : Finset ι) (γ : ι → ℝ) (hγ : ∀ r ∈ Rs, |γ r| ≤ 2 * U)
    (hsep : ∀ r ∈ Rs, ∀ r' ∈ Rs, r ≠ r' → 1 ≤ |γ r - γ r'|)
    (hbig : ∀ r ∈ Rs, V ≤ ‖dp S (fun j => c j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) (γ r)‖) :
    (Rs.card : ℝ) ≤ 154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)) := by
  classical
  have hU0 : 0 < U := by linarith
  set E := 30 / 13 * (1 - σ) with hE
  obtain ⟨m, hm1, hm77, hΛlo, hΛhi⟩ := choose_m100 hU (by norm_num : (0 : ℝ) < 10 / 13) (by norm_num) hPU
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have hΛ : Λ ≤ U ^ (15 / 13 : ℝ) := by
    refine hΛhi.trans (max_le hPU2 ?_)
    rw [show 3 * (10 / 13 : ℝ) / 2 = 15 / 13 by norm_num]
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by push_cast; linarith)
  set εd : ℝ := η / 1000 with hεd
  have hεd0 : 0 < εd := by positivity
  have hεd1 : εd ≤ 1 := by rw [hεd]; linarith
  have hCd := one_le_Cdiv hεd0 hεd1
  have hS0 : 0 ∉ S := fun h => by have := (mem_Ioc.1 (hS h)).1; omega
  -- the classes by piece
  set Ri : ℕ → Finset ι := fun i => Rs.filter fun r => V ^ m / (2 * m) ≤
    ‖dp (pieceS S P m i) (fun n => powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) (γ r)‖ with hRi
  have hcover : Rs ⊆ (range (2 * m)).biUnion Ri := by
    intro r hr
    obtain ⟨i, hi, hbi⟩ := pow_piece_pick hP hS c hm1 σ (γ r) hV (hbig r hr)
    exact mem_biUnion.2 ⟨i, mem_range.2 hi, mem_filter.2 ⟨hr, hbi⟩⟩
  have hE8 : 0 ≤ (4 * C₁ + 864) * U ^ (E + 8 * η) := by positivity
  have hRi_le : ∀ i ∈ range (2 * m), ((Ri i).card : ℝ) ≤ (4 * C₁ + 864) * U ^ (E + 8 * η) := by
    intro i _
    rcases (Ri i).eq_empty_or_nonempty with he | ⟨r0, hr0⟩
    · rw [he, card_empty, Nat.cast_zero]; exact hE8
    set Mi : ℝ := (P : ℝ) ^ m * (3 / 2) ^ i with hMi
    have hMi1 : 1 ≤ Mi := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPr) (one_le_pow₀ (by norm_num))
    have hMi0 : 0 < Mi := by linarith
    set N : ℝ := 5 / 6 * Mi with hN
    have hNM : 6 / 5 * N = Mi := by rw [hN]; ring
    have hN0 : 0 < N := by positivity
    -- the piece lies in `(6N/5, 9N/5]`
    have hS' : ∀ n ∈ pieceS S P m i, 6 / 5 * N < (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N := by
      intro n hn
      obtain ⟨h1, h2, -⟩ := mem_pieceS hP hS hm1 hn
      refine ⟨by rw [hNM]; exact h1, ?_⟩
      calc (n : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ (i + 1) := h2
        _ = 9 / 5 * N := by rw [hN, hMi, pow_succ]; ring
    -- the normalization
    set B : ℝ := Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd) * Mi ^ (-σ) with hB
    have hB0 : 0 < B := by positivity
    set c' : ℕ → ℂ := fun n => if n ∈ pieceS S P m i then
      powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) / B else 0 with hc'
    have hc'1 : ∀ n, ‖c' n‖ ≤ 1 := by
      intro n
      simp only [hc']
      split_ifs with hn
      · obtain ⟨h1, -, h3⟩ := mem_pieceS hP hS hm1 hn
        have hnsupp : n ∈ powSupp S m := (mem_filter.1 hn).1
        have hn0 : (0 : ℝ) < n := lt_trans hMi0 h1
        have hco := norm_powCo_le hS0 hc m hnsupp
        have hdiv : (n.divisors.card : ℝ) ≤ Cdiv εd * Λ ^ εd :=
          (card_divisors_le hεd0 hεd1 n).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le h3 hεd0.le) (by linarith))
        have hpow : (n.divisors.card : ℝ) ^ (2 * m) ≤ Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd) := by
          calc (n.divisors.card : ℝ) ^ (2 * m) ≤ (Cdiv εd * Λ ^ εd) ^ (2 * m) :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv _
            _ = Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd) := by
                rw [mul_pow, ← Real.rpow_natCast (Λ ^ εd), ← Real.rpow_mul (by linarith)]
                push_cast; ring_nf
        have hσn : (n : ℝ) ^ (-σ) ≤ Mi ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hMi0 h1.le (by linarith)
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0, div_le_one hB0, hB]
        calc ‖powCo S c m n‖ * (n : ℝ) ^ (-σ) ≤ (n.divisors.card : ℝ) ^ (2 * m) * Mi ^ (-σ) :=
              mul_le_mul hco hσn (by positivity) (by positivity)
          _ ≤ Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd) * Mi ^ (-σ) :=
              mul_le_mul_of_nonneg_right hpow (by positivity)
      · simp
    have hdp : ∀ t, dp (pieceS S P m i) c' t =
        dp (pieceS S P m i) (fun n => powCo S c m n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) t / B := by
      intro t
      unfold dp
      rw [sum_div]
      refine sum_congr rfl fun n hn => ?_
      simp only [hc']
      rw [ite_eq_left hn]
      ring
    -- the length of the piece
    have hPm : (P : ℝ) ^ m = Λ * (1 / 2) ^ m := by
      rw [hΛdef, ← mul_pow]; push_cast; ring_nf
    have h12 : (1 / 2 : ℝ) ^ 77 ≤ (1 / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm77
    have hPm_lo : (1 / 2 : ℝ) ^ 77 * U ^ (10 / 13 : ℝ) ≤ (P : ℝ) ^ m := by
      rw [hPm, mul_comm Λ]
      exact mul_le_mul h12 hΛlo (by positivity) (by positivity)
    have hMi_lo : (P : ℝ) ^ m ≤ Mi := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    have hNlo : 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ) ≤ N := by
      calc 5 / 6 * (1 / 2 : ℝ) ^ 77 * U ^ (10 / 13 : ℝ) = 5 / 6 * ((1 / 2) ^ 77 * U ^ (10 / 13 : ℝ)) := by ring
        _ ≤ 5 / 6 * Mi := by gcongr; exact hPm_lo.trans hMi_lo
    have hN1 : U ^ (10 / 13 - η) ≤ N := by
      have hc01 : (5 / 6 * (1 / 2 : ℝ) ^ 77) * (6 / 5 * 2 ^ 77) = 1 := by norm_num
      have hsplit : U ^ (10 / 13 - η) * U ^ η = U ^ (10 / 13 : ℝ) := by
        rw [← Real.rpow_add hU0]; ring_nf
      calc U ^ (10 / 13 - η) = (5 / 6 * (1 / 2 : ℝ) ^ 77) * (6 / 5 * 2 ^ 77) * U ^ (10 / 13 - η) := by
            rw [hc01, one_mul]
        _ ≤ (5 / 6 * (1 / 2 : ℝ) ^ 77) * U ^ η * U ^ (10 / 13 - η) := by gcongr
        _ = 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ) := by rw [← hsplit]; ring
        _ ≤ N := hNlo
    have hne : (pieceS S P m i).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h := (mem_filter.1 hr0).2
      rw [hemp] at h
      simp only [dp, sum_empty, norm_zero] at h
      have : 0 < V ^ m / (2 * m) := by positivity
      linarith
    obtain ⟨n0, hn0⟩ := hne
    obtain ⟨hn01, -, hn03⟩ := mem_pieceS hP hS hm1 hn0
    have hNhi : N ≤ U ^ (15 / 13 : ℝ) := by
      have : N ≤ Mi := by rw [hN]; linarith
      linarith
    have hN3' : 10 / 3 ≤ N := hN3.trans hNlo
    have hlU : 0 ≤ Real.log U := Real.log_nonneg hU.le
    have hl4N : Real.log (4 * N) ≤ 2 + 2 * Real.log U := by
      have h1 : Real.log (4 * N) ≤ Real.log (4 * U ^ (15 / 13 : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : U ^ (15 / 13 : ℝ) ≠ 0),
        Real.log_rpow hU0] at h1
      have h4 : Real.log 4 < 2 := by
        have := Real.log_two_lt_d9
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
      linarith
    have hl4N0 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    have hLg' : (1 + Real.log (4 * N)) * (2 + Real.log (4 * N) ^ 2) ≤ U ^ η := by
      refine le_trans ?_ hLg
      exact mul_le_mul (by linarith) (by have := pow_le_pow_left₀ hl4N0 hl4N 2; linarith) (by positivity)
        (by positivity)
    -- the threshold
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hD : 2 * (m : ℝ) * (Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd)) ≤ 6 * V ^ m * N ^ η := by
      have hm77r : (m : ℝ) ≤ 77 := by exact_mod_cast hm77
      have h2m : 2 * (m : ℝ) ≤ 154 := by linarith
      have hCm : Cdiv εd ^ (2 * m) ≤ Cdiv εd ^ 154 := pow_le_pow_right₀ hCd (by omega)
      have hΛm : Λ ^ (2 * m * εd) ≤ U ^ (η / 4) := by
        calc Λ ^ (2 * m * εd) ≤ (U ^ (15 / 13 : ℝ)) ^ (2 * m * εd) :=
              Real.rpow_le_rpow (by linarith) hΛ (by positivity)
          _ = U ^ (15 / 13 * (2 * m * εd)) := by rw [← Real.rpow_mul hU0.le]
          _ ≤ U ^ (η / 4) := by
              refine Real.rpow_le_rpow_of_exponent_le hU.le ?_
              have h1 : 2 * (m : ℝ) * εd ≤ 154 * εd := mul_le_mul_of_nonneg_right h2m hεd0.le
              have h2 : 154 * εd = 154 / 1000 * η := by rw [hεd]; ring
              linarith only [h1, h2, hη]
      have hVm : V ^ 77 ≤ V ^ m := pow_le_pow_of_le_one hV.le hV1 hm77
      have hNη : (5 / 6 * (1 / 2 : ℝ) ^ 77) ^ η * U ^ (10 / 13 * η) ≤ N ^ η := by
        calc (5 / 6 * (1 / 2 : ℝ) ^ 77) ^ η * U ^ (10 / 13 * η)
            = (5 / 6 * (1 / 2 : ℝ) ^ 77) ^ η * (U ^ (10 / 13 : ℝ)) ^ η := by rw [← Real.rpow_mul hU0.le]
          _ = (5 / 6 * (1 / 2 : ℝ) ^ 77 * U ^ (10 / 13 : ℝ)) ^ η :=
              (Real.mul_rpow (by positivity) (by positivity)).symm
          _ ≤ N ^ η := Real.rpow_le_rpow (by positivity) hNlo hη.le
      have hUη : U ^ (η / 2) * U ^ (η / 4) ≤ U ^ (10 / 13 * η) := by
        rw [← Real.rpow_add hU0]
        exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
      calc 2 * (m : ℝ) * (Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd))
          ≤ 154 * (Cdiv εd ^ 154 * U ^ (η / 4)) := by gcongr
        _ = (154 * Cdiv εd ^ 154) * U ^ (η / 4) := by ring
        _ ≤ (6 * V ^ 77 * (5 / 6 * (1 / 2) ^ 77) ^ η * U ^ (η / 2)) * U ^ (η / 4) := by gcongr
        _ = 6 * V ^ 77 * ((5 / 6 * (1 / 2) ^ 77) ^ η * (U ^ (η / 2) * U ^ (η / 4))) := by ring
        _ ≤ 6 * V ^ m * ((5 / 6 * (1 / 2) ^ 77) ^ η * U ^ (10 / 13 * η)) := by gcongr
        _ ≤ 6 * V ^ m * N ^ η := by gcongr
    have hbig' : ∀ r ∈ Ri i, N ^ (σ - η) / 6 ≤ ‖dp (pieceS S P m i) c' (γ r)‖ := by
      intro r hr
      have hv := (mem_filter.1 hr).2
      rw [hdp, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
      refine le_trans ?_ (div_le_div_of_nonneg_right hv hB0.le)
      rw [le_div_iff₀ hB0, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      have hNσ : N ^ σ ≤ Mi ^ σ := Real.rpow_le_rpow hN0.le (by rw [hN]; linarith) (by linarith)
      have hNση : N ^ (σ - η) * N ^ η = N ^ σ := by rw [← Real.rpow_add hN0]; ring_nf
      have hMiσ : Mi ^ σ * Mi ^ (-σ) = 1 := by rw [← Real.rpow_add hMi0]; simp
      have hpos1 : 0 ≤ N ^ (σ - η) * Mi ^ (-σ) := by positivity
      calc N ^ (σ - η) * B * (2 * m) = (2 * (m : ℝ) * (Cdiv εd ^ (2 * m) * Λ ^ (2 * m * εd))) *
            (N ^ (σ - η) * Mi ^ (-σ)) := by rw [hB]; ring
        _ ≤ (6 * V ^ m * N ^ η) * (N ^ (σ - η) * Mi ^ (-σ)) := mul_le_mul_of_nonneg_right hD hpos1
        _ = 6 * V ^ m * ((N ^ (σ - η) * N ^ η) * Mi ^ (-σ)) := by ring
        _ ≤ 6 * V ^ m * (Mi ^ σ * Mi ^ (-σ)) := by rw [hNση]; gcongr
        _ = V ^ m * 6 := by rw [hMiσ]; ring
    exact piece_count hη hη1 hC₁0 hC₁ hσ hσ1 hU.le hN1 hNhi hN3' hLg' hS' hc'1 (Ri i) γ
      (fun r hr => hγ r (mem_filter.1 hr).1)
      (fun r hr r' hr' hne => hsep r (mem_filter.1 hr).1 r' (mem_filter.1 hr').1 hne) hbig'
  have h2m : ((2 * m : ℕ) : ℝ) ≤ 154 := by exact_mod_cast (by omega : 2 * m ≤ 154)
  calc (Rs.card : ℝ) ≤ (((range (2 * m)).biUnion Ri).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ i ∈ range (2 * m), ((Ri i).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _i ∈ range (2 * m), (4 * C₁ + 864) * U ^ (E + 8 * η) := sum_le_sum hRi_le
    _ = ((2 * m : ℕ) : ℝ) * ((4 * C₁ + 864) * U ^ (E + 8 * η)) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 154 * ((4 * C₁ + 864) * U ^ (E + 8 * η)) := by gcongr


set_option maxHeartbeats 1000000 in
/-- **The polynomial class on `7/10 + η ≤ σ ≤ 4/5`.** Given `C₁` with `GMBound C₁ η`, `0 < η ≤ 1/100`: points
`β_r + iγ_r`, `σ ≤ β_r < 1`, with 1-separated heights `|γ_r| ≤ 2U`, at which `|P_b(β_r, γ_r)| ≥ ¼` (`|b_j| ≤ d(j)`),
number at most `KL·154(4C₁ + 864)U^{(30/13)(1−σ)+8η}`, `K = ⌊log₂ N⌋ + 1`, for `L ≥ 1` with `16K(2XN)² ≤ L!`, when
`U^{1/100} ≤ 2X`, `(2XN)² ≤ U^{15/13}` and `U` is large in the sense of `hW`, `hc0`, `hN3` and `hLg`: some dyadic
block is at least `1/(4K)` (`InghamDensity.Pv_eq_blocks`); in it some `Σ_j b_j log(j/P)^l j^{−σ}j^{−iγ}`, `l < L`,
is at least `1/(16K)` (`taylor_pick_dp` at `δ = β − σ`); and `poly_count_gm` for each block and each `l`. -/
theorem class_poly_gm {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : GMBound C₁ η)
    (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {σ U : ℝ} (hσ : 7 / 10 + η ≤ σ) (hσ1 : σ ≤ 4 / 5)
    (hU : 1 < U) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXU : U ^ (1 / 100 : ℝ) ≤ 2 * X)
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ)) {L : ℕ} (hL : 1 ≤ L)
    (htail : 16 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ L.factorial)
    (hW : 154 * Cdiv (η / 1000) ^ 154 ≤
      6 * (1 / (16 * ((Nat.log 2 N + 1 : ℕ) : ℝ))) ^ 77 * (5 / 6 * (1 / 2) ^ 77) ^ η * U ^ (η / 2))
    (hc0 : 6 / 5 * 2 ^ 77 ≤ U ^ η) (hN3 : 10 / 3 ≤ 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ))
    (hLg : (3 + 2 * Real.log U) * (2 + (2 + 2 * Real.log U) ^ 2) ≤ U ^ η)
    {ι : Type} (Rs : Finset ι) (β γ : ι → ℝ) (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r < 1)
    (hγ : ∀ r ∈ Rs, |γ r| ≤ 2 * U) (hsep : ∀ r ∈ Rs, ∀ r' ∈ Rs, r ≠ r' → 1 ≤ |γ r - γ r'|)
    (hbig : ∀ r ∈ Rs, 1 / 4 ≤ ‖Pv b X N (β r) (γ r)‖) :
    (Rs.card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * L *
      (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η))) := by
  classical
  set K := Nat.log 2 N + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  have hV4 : V / 4 = 1 / (16 * (K : ℝ)) := by rw [hV]; field_simp; ring
  have hσ0 : 0 ≤ σ := by linarith
  set B := 154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)) with hB
  -- some dyadic block of each point is at least `V`
  have hlarge : ∀ r ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkb b X N k (β r) (γ r)‖ := by
    intro r hr
    by_contra hcon
    push Not at hcon
    have h1 := hbig r hr
    rw [Pv_eq_blocks b X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkb b X N k (β r) (γ r)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkb b X N k (β r) (γ r)).trans_lt (h3 ▸ h2)]
  -- the block `k` lies in `(P, 2P]`, `P = 2^kX`
  set Sk : ℕ → Finset ℕ := fun k => (Ioc X (X * N)).filter (fun j => blk X j = k) with hSk
  have hP : ∀ k, 1 ≤ 2 ^ k * X := fun k => Nat.one_le_iff_ne_zero.2 (by positivity)
  have hSsub : ∀ k, Sk k ⊆ Ioc (2 ^ k * X) (2 * (2 ^ k * X)) := fun k => block_sub hX
  -- the Taylor tail
  have hXN1 : (1 : ℝ) ≤ ((X * N : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have htail' : ∀ k, 2 * ∑ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ) ≤ V / 4 * L.factorial := by
    intro k
    have hj : ∀ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ) ≤ ((X * N : ℕ) : ℝ) := by
      intro j hj
      have hjI := mem_Ioc.1 (mem_filter.1 hj).1
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
      have hd : ‖b j‖ ≤ j := (hb j).trans (by exact_mod_cast Nat.card_divisors_le_self j)
      have hr : (j : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1 (by linarith)
      have hjXN : (j : ℝ) ≤ ((X * N : ℕ) : ℝ) := by exact_mod_cast hjI.2
      calc ‖b j‖ * (j : ℝ) ^ (-σ) ≤ j * 1 := mul_le_mul hd hr (by positivity) (by positivity)
        _ ≤ ((X * N : ℕ) : ℝ) := by linarith
    have hcard : ((Sk k).card : ℝ) ≤ ((X * N : ℕ) : ℝ) := by
      have h1 : (Sk k).card ≤ (Ioc X (X * N)).card := card_filter_le _ _
      have h2 : (Ioc X (X * N)).card ≤ X * N := by rw [Nat.card_Ioc]; omega
      exact_mod_cast h1.trans h2
    have hsum : ∑ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ) ≤ ((X * N : ℕ) : ℝ) * ((X * N : ℕ) : ℝ) := by
      calc ∑ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ) ≤ ∑ _j ∈ Sk k, ((X * N : ℕ) : ℝ) := sum_le_sum hj
        _ = ((Sk k).card : ℝ) * ((X * N : ℕ) : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ((X * N : ℕ) : ℝ) * ((X * N : ℕ) : ℝ) := by gcongr
    have h1 : 2 * (∑ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ)) * (16 * K) ≤ L.factorial := by
      have e : 16 * (K : ℝ) * (2 * ((X * N : ℕ) : ℝ)) ^ 2 =
          2 * (2 * (((X * N : ℕ) : ℝ) * ((X * N : ℕ) : ℝ)) * (16 * K)) := by ring
      have h0 : 0 ≤ 2 * (((X * N : ℕ) : ℝ) * ((X * N : ℕ) : ℝ)) * (16 * K) := by positivity
      calc 2 * (∑ j ∈ Sk k, ‖b j‖ * (j : ℝ) ^ (-σ)) * (16 * K) ≤
            2 * (((X * N : ℕ) : ℝ) * ((X * N : ℕ) : ℝ)) * (16 * K) := by gcongr
        _ ≤ 16 * K * (2 * ((X * N : ℕ) : ℝ)) ^ 2 := by rw [e]; linarith
        _ ≤ L.factorial := htail
    rw [hV4, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    exact h1
  -- the classes by block and Taylor term
  set ck : ℕ → ℕ → ℕ → ℂ := fun k l j => b j * ((Real.log ((j : ℝ) / ((2 ^ k * X : ℕ) : ℝ)) ^ l : ℝ) : ℂ)
    with hck
  set Ckl : ℕ → ℕ → Finset ι := fun k l => Rs.filter fun r =>
    1 / (16 * (K : ℝ)) ≤ ‖dp (Sk k) (fun j => ck k l j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ)) (γ r)‖ with hCkl
  have hcover : Rs ⊆ (range K).biUnion fun k => (range L).biUnion fun l => Ckl k l := by
    intro r hr
    obtain ⟨k, hk, hbk⟩ := hlarge r hr
    have hβr := hβ r hr
    have hbk' : V ≤ ‖dp (Sk k) (fun j => b j * (((j : ℝ) ^ (-(σ + (β r - σ))) : ℝ) : ℂ)) (γ r)‖ := by
      rw [show σ + (β r - σ) = β r by ring]; exact hbk
    obtain ⟨l, hl, hbl⟩ := taylor_pick_dp (hP k) (hSsub k) b (by linarith : 0 ≤ β r - σ)
      (by linarith : β r - σ ≤ 1) hV0 hL (htail' k) hbk'
    rw [hV4] at hbl
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨l, mem_range.2 hl, mem_filter.2 ⟨hr, hbl⟩⟩⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hCkl_le : ∀ k ∈ range K, ∀ l ∈ range L, ((Ckl k l).card : ℝ) ≤ B := by
    intro k hk l _
    have hPN : 2 ^ k * X ≤ X * N := by
      rw [mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ 2 ^ k * X := Nat.le_mul_of_pos_left X (by positivity)
    have hPU : U ^ (1 / 100 : ℝ) ≤ ((2 * (2 ^ k * X) : ℕ) : ℝ) := by
      have : ((2 * X : ℕ) : ℝ) ≤ ((2 * (2 ^ k * X) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * X ≤ 2 * (2 ^ k * X))
      push_cast at this ⊢; linarith
    have hPU2 : ((2 * (2 ^ k * X) : ℕ) : ℝ) ^ 2 ≤ U ^ (15 / 13 : ℝ) := by
      refine le_trans (pow_le_pow_left₀ (by positivity) ?_ 2) hXN
      have : ((2 * (2 ^ k * X) : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega)
      push_cast at this ⊢; linarith
    have hc : ∀ j ∈ Sk k, ‖ck k l j‖ ≤ (j.divisors.card : ℝ) := by
      intro j hj
      have hjI := mem_Ioc.1 (hSsub k hj)
      have hPr : (0 : ℝ) < ((2 ^ k * X : ℕ) : ℝ) := by exact_mod_cast hP k
      have hj1 : (((2 ^ k * X : ℕ) : ℝ)) < j := by exact_mod_cast hjI.1
      have hj2 : (j : ℝ) ≤ 2 * ((2 ^ k * X : ℕ) : ℝ) := by exact_mod_cast hjI.2
      have hl0 : 0 ≤ Real.log ((j : ℝ) / ((2 ^ k * X : ℕ) : ℝ)) :=
        Real.log_nonneg (by rw [le_div_iff₀ hPr]; linarith)
      have hl1 : Real.log ((j : ℝ) / ((2 ^ k * X : ℕ) : ℝ)) ≤ 1 := by
        calc Real.log ((j : ℝ) / ((2 ^ k * X : ℕ) : ℝ)) ≤ Real.log 2 :=
              Real.log_le_log (div_pos (by linarith) hPr) (by rw [div_le_iff₀ hPr]; linarith)
          _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
      simp only [hck]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl0 l)]
      calc ‖b j‖ * Real.log ((j : ℝ) / ((2 ^ k * X : ℕ) : ℝ)) ^ l ≤ (j.divisors.card : ℝ) * 1 :=
            mul_le_mul (hb j) (pow_le_one₀ hl0 hl1) (by positivity) (by positivity)
        _ = (j.divisors.card : ℝ) := mul_one _
    have hV41 : 1 / (16 * (K : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    exact poly_count_gm hη hη1 hC₁0 hC₁ hσ hσ1 hU (hP k) (hSsub k) hPU hPU2 hc (by positivity) hV41 hW hc0 hN3
      hLg (Ckl k l) γ (fun r hr => hγ r (mem_filter.1 hr).1)
      (fun r hr r' hr' hne => hsep r (mem_filter.1 hr).1 r' (mem_filter.1 hr').1 hne)
      (fun r hr => (mem_filter.1 hr).2)
  calc (Rs.card : ℝ) ≤ (((range K).biUnion fun k => (range L).biUnion fun l => Ckl k l).card : ℝ) := by
        exact_mod_cast card_le_card hcover
    _ ≤ ∑ k ∈ range K, (((range L).biUnion fun l => Ckl k l).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ l ∈ range L, ((Ckl k l).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ l ∈ range L, B := by
        gcongr with k hk l hl; exact hCkl_le k hk l hl
    _ = (K : ℝ) * L * B := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### One window -/

/-- **The three classes in one window on `7/10 + η ≤ σ ≤ 4/5`**: `ZetaHuxley.trichotomy7`, then `class_poly_gm` for
the two polynomial classes and `ZetaHuxley.class3_count_small` (at `δ = 1/5`) for the integral class, over the parity
classes of the unit windows (`InghamDensity.card_le_of_classes`). -/
theorem window_classes_gm {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : GMBound C₁ η)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + η))
    {σ U Y : ℝ} (hσ : 7 / 10 + η ≤ σ) (hσ1 : σ ≤ 4 / 5) (hU : 2 ≤ U) (hY : 8 ≤ Y) (hUY : 36864 * U ≤ Y ^ 7)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hXU : U ^ (1 / 100 : ℝ) ≤ 2 * X) (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ)) {L : ℕ} (hL : 1 ≤ L)
    (htail : 16 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ L.factorial)
    (hW : 154 * Cdiv (η / 1000) ^ 154 ≤
      6 * (1 / (16 * ((Nat.log 2 N + 1 : ℕ) : ℝ))) ^ 77 * (5 / 6 * (1 / 2) ^ 77) ^ η * U ^ (η / 2))
    (hc0 : 6 / 5 * 2 ^ 77 ≤ U ^ η) (hN3 : 10 / 3 ≤ 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ))
    (hLg : (3 + 2 * Real.log U) * (2 + (2 + 2 * Real.log U) ^ 2) ≤ U ^ η)
    (Z : Finset (ZeroIdx (sqF Xi))) (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 N + 1 : ℕ) : ℝ) * L *
        (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)))) +
      27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + η))) := by
  classical
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  set B1 := ((Nat.log 2 N + 1 : ℕ) : ℝ) * L * (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)))
    with hB1
  set B3 := 27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + η)) with hB3
  have hB10 : 0 ≤ B1 := by positivity
  have hB30 : 0 ≤ B3 := by have := KG_pos; positivity
  have htri : ∀ i ∈ Z, 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
      ∨ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖ := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hZ i hi
    exact trichotomy7 hX hN hY hU hUY hM (by linarith) (βs_lt_one i) (by rw [abs_γs]; exact h1)
      (by rw [abs_γs]; exact h2) (DetectCore.zeta_βsγs i)
  set Z1 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖
  set Z2 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
  set Z3 := Z.filter fun i => U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖
  have hcover : Z ⊆ Z1 ∪ Z2 ∪ Z3 := by
    intro i hi
    rcases htri i hi with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hpoly : ∀ b : ℕ → ℂ, (∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) → ∀ (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi)),
      (∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n) →
      (∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1) →
      (∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ (σ ≤ βs (rep n) ∧ 1 / 4 ≤ ‖Pv b X N (βs (rep n)) (γs (rep n))‖)) →
      (C.card : ℝ) ≤ B1 := by
    intro b hb C rep hC hwin hdet
    exact class_poly_gm hη hη1 hC₁0 hC₁ b hb hσ hσ1 (by linarith) hX hN hXU hXN hL htail hW hc0 hN3 hLg C
      (fun n => βs (rep n)) (fun n => γs (rep n)) (fun n hn => ⟨(hdet n hn).2.1, βs_lt_one _⟩)
      (fun n hn => by rw [abs_γs]; exact (hdet n hn).1) (sep_of_windows C rep hC hwin)
      (fun n hn => (hdet n hn).2.2)
  have hZ1 : (Z1.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖) Z1
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b1 X Y) (norm_b1_le X hY0) C rep hC hwin hdet
  have hZ2 : (Z2.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖) Z2
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b2 X Y) (norm_b2_le X hY0) C rep hC hwin hdet
  have hZ3 : (Z3.card : ℝ) ≤ 2 * B3 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖) Z3
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB30 fun C rep hC hwin hdet =>
        class3_count_small hη.le (by linarith) hC₄ h4 hX (δ := 1 / 5) (by norm_num) (by linarith) hU
          (by linarith) C rep hC hwin hdet
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2 ∪ Z3).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card + Z3.card := by
        have h1 := card_union_le (Z1 ∪ Z2) Z3
        have h2 := card_union_le Z1 Z2
        exact_mod_cast h1.trans (by omega)
    _ ≤ 2 * B1 * Kloc (2 * U + 1) + 2 * B1 * Kloc (2 * U + 1) + 2 * B3 * Kloc (2 * U + 1) := by
        linarith
    _ = 2 * Kloc (2 * U + 1) * (2 * B1 + B3) := by ring

/-- **The integral class at `Y = U^{1/2}`, `X ≤ U^{1/100}`, `δ = 1/5`**: `27(15KG)⁴Y^{2−4σ}X⁴C₄(2U + 2)^{1+η} ≤
243(15KG)⁴C₄U^{(30/13)(1−σ)+9η}` for `σ ≤ 4/5`: the exponent is `2 − 2σ + 1/25 + η`, and
`(30/13)(1 − σ) − (51/25 − 2σ) ≥ 30/13 − 51/25 − (4/13)(4/5) > 0`. -/
lemma class3_bound_gm {η C₄ σ U : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) (hC₄ : 0 ≤ C₄) (hσ1 : σ ≤ 4 / 5)
    (hU : 8 ≤ U)
    {X : ℕ} (hXU : (X : ℝ) ≤ U ^ (1 / 100 : ℝ)) :
    27 * (3 * KG * (U ^ (1 / 2 : ℝ)) ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + η))
      ≤ 243 * (15 * KG) ^ 4 * C₄ * U ^ (30 / 13 * (1 - σ) + 9 * η) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hKG := KG_pos
  have hY : ((U ^ (1 / 2 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = U ^ (2 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ U ^ (1 / 25 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (U ^ (1 / 100 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXU 4
      _ = U ^ (1 / 25 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  have hM : (2 * U + 2) ^ (1 + η) ≤ 9 * U ^ (1 + η) := by
    calc (2 * U + 2) ^ (1 + η) ≤ (3 * U) ^ (1 + η) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + η) * U ^ (1 + η) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + η) := by
          gcongr
          calc (3 : ℝ) ^ (1 + η) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have hexp : 2 * (1 / 2 - σ) + 1 / 25 + (1 + η) ≤ 30 / 13 * (1 - σ) + 9 * η := by linarith
  calc 27 * (3 * KG * (U ^ (1 / 2 : ℝ)) ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + η))
      = 27 * (15 * KG) ^ 4 * C₄ * (((U ^ (1 / 2 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 * (2 * U + 2) ^ (1 + η)) := by
        ring
    _ ≤ 27 * (15 * KG) ^ 4 * C₄ * (U ^ (2 * (1 / 2 - σ)) * U ^ (1 / 25 : ℝ) * (9 * U ^ (1 + η))) := by
        rw [hY]; gcongr
    _ = 243 * (15 * KG) ^ 4 * C₄ * (U ^ (2 * (1 / 2 - σ)) * U ^ (1 / 25 : ℝ) * U ^ (1 + η)) := by ring
    _ = 243 * (15 * KG) ^ 4 * C₄ * U ^ (2 * (1 / 2 - σ) + 1 / 25 + (1 + η)) := by
        rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
    _ ≤ 243 * (15 * KG) ^ 4 * C₄ * U ^ (30 / 13 * (1 - σ) + 9 * η) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 hexp) (by positivity)

/-- `(a + b log U)^n ≤ U^θ` for all large `U`, for `a, b ≥ 0`, `θ > 0`: `log U ≤ U^r/r` at `r = θ/(2(n + 1))`
(`Real.log_le_rpow_div`). -/
lemma ev_log_pow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 < θ) (n : ℕ) :
    ∀ᶠ U : ℝ in atTop, (a + b * Real.log U) ^ n ≤ U ^ θ := by
  set r := θ / (2 * (n + 1)) with hr
  have hr0 : 0 < r := by positivity
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by positivity : 0 < θ / 2)).eventually_ge_atTop ((a + b / r) ^ n)] with U hU1 hU2
  have hU0 : 0 < U := by linarith
  have hl : Real.log U ≤ U ^ r / r := Real.log_le_rpow_div hU0.le hr0
  have hl0 : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hUr : 1 ≤ U ^ r := Real.one_le_rpow hU1 hr0.le
  have h1 : a + b * Real.log U ≤ (a + b / r) * U ^ r := by
    have e : b * (U ^ r / r) = b / r * U ^ r := by ring
    have h2 : a ≤ a * U ^ r := le_mul_of_one_le_right ha hUr
    calc a + b * Real.log U ≤ a + b * (U ^ r / r) := by gcongr
      _ ≤ a * U ^ r + b / r * U ^ r := by rw [e]; linarith
      _ = (a + b / r) * U ^ r := by ring
  have hrn : r * n ≤ θ / 2 := by
    rw [hr, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc (a + b * Real.log U) ^ n ≤ ((a + b / r) * U ^ r) ^ n := pow_le_pow_left₀ (by positivity) h1 n
    _ = (a + b / r) ^ n * U ^ (r * n) := by rw [mul_pow, ← Real.rpow_natCast (U ^ r), ← Real.rpow_mul hU0.le]
    _ ≤ U ^ (θ / 2) * U ^ (θ / 2) :=
        mul_le_mul hU2 (Real.rpow_le_rpow_of_exponent_le hU1 hrn) (by positivity) (by positivity)
    _ = U ^ θ := by rw [← Real.rpow_add hU0]; ring_nf


/-- The conditions on `U` used on `7/10 + η ≤ σ ≤ 4/5` hold for all large `U` (`ev_log_pow`, and `c ≤ U^θ`
eventually). -/
lemma eventually_gm {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∀ᶠ U : ℝ in atTop, (8 : ℝ) ^ 100 ≤ U ∧
      (2 * (23 * U ^ (1 / 2 : ℝ) * Real.log (U ^ (1 / 2 : ℝ)))) ^ 2 ≤ U ^ (15 / 13 : ℝ) ∧
      23 * U ^ (1 / 2 : ℝ) * Real.log (U ^ (1 / 2 : ℝ)) ≤ U ∧
      16 * (1 + 2 * Real.log U) * U ^ (15 / 13 : ℝ) ≤ U ^ (5 / 2 : ℝ) ∧
      A * (16 * (1 + 2 * Real.log U)) ^ 77 ≤ U ^ (η / 2) ∧
      6 / 5 * 2 ^ 77 ≤ U ^ η ∧
      10 / 3 ≤ 5 / 6 * (1 / 2) ^ 77 * U ^ (10 / 13 : ℝ) ∧
      (3 + 2 * Real.log U) * (2 + (2 + 2 * Real.log U) ^ 2) ≤ U ^ η ∧
      (1 + 2 * Real.log U) * (4 * Real.log U + 2) ≤ U ^ η := by
  have hev : ∀ c θ : ℝ, 0 < θ → ∀ᶠ U : ℝ in atTop, c ≤ U ^ θ := fun c θ hθ =>
    (tendsto_rpow_atTop hθ).eventually_ge_atTop c
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 100),
    ev_log_pow (a := 0) (b := 23) le_rfl (by norm_num) (by norm_num : (0 : ℝ) < 2 / 13) 2,
    ev_log_pow (a := 0) (b := 23 / 2) le_rfl (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) 1,
    ev_log_pow (a := 16) (b := 32) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1) 1,
    ev_log_pow (a := 16) (b := 32) (by norm_num) (by norm_num) (by positivity : (0 : ℝ) < η / 4) 77,
    hev A (η / 4) (by positivity), hev (6 / 5 * 2 ^ 77) η hη,
    hev (10 / 3 / (5 / 6 * (1 / 2) ^ 77)) (10 / 13) (by norm_num),
    ev_log_pow (a := 3) (b := 2) (by norm_num) (by norm_num) hη 3,
    ev_log_pow (a := 2) (b := 4) (by norm_num) (by norm_num) hη 2]
    with U h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hU1 : 1 ≤ U := le_trans (by norm_num) h1
  have hU0 : 0 < U := by linarith
  have hl0 : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hlog : Real.log (U ^ (1 / 2 : ℝ)) = 1 / 2 * Real.log U := Real.log_rpow hU0 _
  have e1 : (U ^ (1 / 2 : ℝ)) ^ 2 = U := by rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  refine ⟨h1, ?_, ?_, ?_, ?_, h7, ?_, ?_, ?_⟩
  · calc (2 * (23 * U ^ (1 / 2 : ℝ) * Real.log (U ^ (1 / 2 : ℝ)))) ^ 2
          = (U ^ (1 / 2 : ℝ)) ^ 2 * (0 + 23 * Real.log U) ^ 2 := by rw [hlog]; ring
      _ ≤ U * U ^ (2 / 13 : ℝ) := by rw [e1]; gcongr
      _ = U ^ (15 / 13 : ℝ) := by rw [← Real.rpow_one_add' (y := 2 / 13) hU0.le (by norm_num)]; norm_num
  · have h3' : 23 / 2 * Real.log U ≤ U ^ (1 / 2 : ℝ) := by
      have := h3; rw [zero_add, pow_one] at this; exact this
    calc 23 * U ^ (1 / 2 : ℝ) * Real.log (U ^ (1 / 2 : ℝ)) = U ^ (1 / 2 : ℝ) * (23 / 2 * Real.log U) := by
          rw [hlog]; ring
      _ ≤ U ^ (1 / 2 : ℝ) * U ^ (1 / 2 : ℝ) := by gcongr
      _ = U := by rw [← Real.rpow_add hU0]; norm_num
  · have h4' : 16 * (1 + 2 * Real.log U) ≤ U := by
      have := h4; rw [pow_one, Real.rpow_one] at this
      calc 16 * (1 + 2 * Real.log U) = 16 + 32 * Real.log U := by ring
        _ ≤ U := this
    calc 16 * (1 + 2 * Real.log U) * U ^ (15 / 13 : ℝ) ≤ U * U ^ (15 / 13 : ℝ) := by gcongr
      _ = U ^ (28 / 13 : ℝ) := by rw [← Real.rpow_one_add' (y := 15 / 13) hU0.le (by norm_num)]; norm_num
      _ ≤ U ^ (5 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
  · have e : 16 * (1 + 2 * Real.log U) = 16 + 32 * Real.log U := by ring
    calc A * (16 * (1 + 2 * Real.log U)) ^ 77 ≤ U ^ (η / 4) * U ^ (η / 4) := by
          rw [e]; exact mul_le_mul h6 h5 (pow_nonneg (by linarith) _) (by positivity)
      _ = U ^ (η / 2) := by rw [← Real.rpow_add hU0]; ring_nf
  · have hc : (0 : ℝ) < 5 / 6 * (1 / 2) ^ 77 := by norm_num
    have := mul_le_mul_of_nonneg_left h8 hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  · calc (3 + 2 * Real.log U) * (2 + (2 + 2 * Real.log U) ^ 2) ≤ (3 + 2 * Real.log U) ^ 3 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + 2 * Real.log U)
            (by linarith : (0 : ℝ) ≤ 3 + 4 * Real.log U)]
      _ ≤ U ^ η := h9
  · calc (1 + 2 * Real.log U) * (4 * Real.log U + 2) ≤ (2 + 4 * Real.log U) ^ 2 := by
          nlinarith [sq_nonneg (1 + 2 * Real.log U)]
      _ ≤ U ^ η := h10

set_option maxHeartbeats 1000000 in
/-- **One window on `7/10 + η ≤ σ ≤ 4/5`**: for every `0 < η ≤ 1/100` there is `Cw` such that for
`7/10 + η ≤ σ ≤ 4/5` and `U ≥ 8` at most `Cw(log U)^{11}U^{(30/13)(1−σ)+9η}` zeros have `U ≤ |γ| ≤ 2U` and `β ≥ σ`.
For `U ≥ U₁` (`eventually_gm`), `window_classes_gm` at `X = ⌊U^{1/100}⌋`, `Y = U^{1/2}`, `N = ⌊22Y log Y/X⌋ + 1`
(`Xw`, `Yw`, `Nw` at `U^{1/100}`, `c = 49/2`) and `L = ⌈4 log U⌉ + 1`, with `L! ≥ 2^{L−1} ≥ U^{4 log 2}`; below `U₁`
the zeros with `|γ| ≤ 2U₁`. -/
theorem window_count_gm {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ σ : ℝ, 7 / 10 + η ≤ σ → σ ≤ 4 / 5 → ∀ U : ℝ, 8 ≤ U → ∀ Z : Finset (ZeroIdx (sqF Xi)),
      (∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) →
        (Z.card : ℝ) ≤ Cw * Real.log U ^ 11 * U ^ (30 / 13 * (1 - σ) + 9 * η) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ZetaGMLV.gm_large_values hη
  obtain ⟨C₄', hC₄'⟩ := zeta_fourth_moment (ε := η) hη (by linarith)
  set C₄ := max C₄' 0 with hC₄def
  have hC₄0 : 0 ≤ C₄ := le_max_right _ _
  have h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + η) := by
    intro C' t hsep T hT ht
    refine (hC₄' C' t hsep T hT ht).trans ?_
    gcongr
    exact le_max_left _ _
  have hCd := one_le_Cdiv (ε := η / 1000) (by positivity) (by linarith)
  set c₀ : ℝ := (5 / 6 * (1 / 2) ^ 77) ^ η with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set A : ℝ := 154 * Cdiv (η / 1000) ^ 154 / (6 * c₀) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (eventually_gm hη A)
  set U₁ := max U₀ ((8 : ℝ) ^ 100) with hU₁
  set Cfin : ℝ := ((finite_re_le (2 * U₁)).toFinset.card : ℝ) with hCfin
  have hKG := KG_pos
  have hKc := Kc_nonneg
  set Cmain : ℝ := 2 * Kc * (2 * (154 * (4 * C₁ + 864)) + 243 * (15 * KG) ^ 4 * C₄) with hCmain
  have hCmain0 : 0 ≤ Cmain := by positivity
  have hCf : 0 ≤ Cfin := Nat.cast_nonneg _
  refine ⟨Cfin + Cmain, by positivity, fun σ hσ hσ1 U hU Z hZ => ?_⟩
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  set E := 30 / 13 * (1 - σ) + 9 * η with hE
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hUE : 1 ≤ U ^ E := Real.one_le_rpow hU1 hE0
  have hL := log_ge_two hU
  have hL11 : 1 ≤ Real.log U ^ 11 := one_le_pow₀ (by linarith)
  rcases lt_or_ge U U₁ with hsmall | hlarge
  · -- below `U₁`: every zero counted has `|γ| ≤ 2U₁`
    have hsub : Z ⊆ (finite_re_le (2 * U₁)).toFinset := fun i hi => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      linarith [(hZ i hi).2.1]
    have hc : (Z.card : ℝ) ≤ Cfin := by rw [hCfin]; exact_mod_cast card_le_card hsub
    have h1 : 1 ≤ Real.log U ^ 11 * U ^ E := one_le_mul_of_one_le_of_one_le hL11 hUE
    have h2 : 0 ≤ Cmain * (Real.log U ^ 11 * U ^ E) := by positivity
    calc (Z.card : ℝ) ≤ Cfin := hc
      _ ≤ Cfin * (Real.log U ^ 11 * U ^ E) := le_mul_of_one_le_right hCf h1
      _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by nlinarith
  obtain ⟨h1, h2, h3, h4', h5, h6, h7, h8, h9⟩ := hU₀ U (le_trans (le_max_left _ _) hlarge)
  -- the parameters
  set U' : ℝ := U ^ (1 / 100 : ℝ) with hU'
  have hU'8 : 8 ≤ U' := by
    rw [hU']
    calc (8 : ℝ) = ((8 : ℝ) ^ 100) ^ (1 / 100 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ U ^ (1 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYU : Yw (49 / 2) U' = U ^ (1 / 2 : ℝ) := by
    rw [hU']; unfold Yw; rw [← Real.rpow_mul hU0.le]; norm_num
  have hX : 1 ≤ Xw U' := Xw_one hU'8
  have hN : 1 ≤ Nw (49 / 2) U' := Nw_one
  have hY8 : 8 ≤ Yw (49 / 2) U' := le_trans hU'8 (Yw_ge (by norm_num) hU'8)
  have hM : 22 * Yw (49 / 2) U' * Real.log (Yw (49 / 2) U') ≤ ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ) := XN_ge hU'8
  have hXNle : ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ) ≤ 23 * Yw (49 / 2) U' * Real.log (Yw (49 / 2) U') :=
    XN_le (by norm_num) hU'8
  have hXU' : (Xw U' : ℝ) ≤ U ^ (1 / 100 : ℝ) := Xw_le hU'8
  have hXU2 : U ^ (1 / 100 : ℝ) ≤ 2 * (Xw U' : ℝ) := by have := Xw_half hU'8; rw [← hU']; linarith
  have hXr : (1 : ℝ) ≤ Xw U' := by exact_mod_cast hX
  have hUY : 36864 * U ≤ (Yw (49 / 2) U') ^ 7 := by
    rw [hYU, ← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    have e : U ^ ((1 / 2 : ℝ) * ((7 : ℕ) : ℝ)) = U ^ (5 / 2 : ℝ) * U := by
      rw [← Real.rpow_add_one hU0.ne']; norm_num
    rw [e]
    have h36 : (36864 : ℝ) ≤ U ^ (5 / 2 : ℝ) := by
      calc (36864 : ℝ) ≤ ((8 : ℝ) ^ 100) ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ U ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact mul_le_mul_of_nonneg_right h36 hU0.le
  rw [hYU] at hXNle
  have hNU : (Nw (49 / 2) U' : ℝ) ≤ U := by
    have h1' : (Nw (49 / 2) U' : ℝ) ≤ ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    linarith
  set K : ℝ := ((Nat.log 2 (Nw (49 / 2) U') + 1 : ℕ) : ℝ) with hKdef
  have hK : K ≤ 1 + 2 * Real.log U := log_blocks_le hN hNU
  have hK1 : 1 ≤ K := by rw [hKdef]; exact_mod_cast (by omega : 1 ≤ Nat.log 2 (Nw (49 / 2) U') + 1)
  have hXN : (2 * ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ) :=
    le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 2) h2
  -- the Taylor length
  set L := ⌈4 * Real.log U⌉₊ + 1 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hLle : (L : ℝ) ≤ 4 * Real.log U + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.log U by positivity)
    rw [hLdef]; push_cast; linarith
  have htail : 16 * K * (2 * ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ)) ^ 2 ≤ L.factorial := by
    have hc : 4 * Real.log U ≤ ((⌈4 * Real.log U⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2pow : (2 : ℝ) ^ (4 * Real.log U) ≤ (2 : ℝ) ^ (⌈4 * Real.log U⌉₊) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hc
    have e : (2 : ℝ) ^ (4 * Real.log U) = U ^ (4 * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hU0]; ring_nf
    have h52 : U ^ (5 / 2 : ℝ) ≤ U ^ (4 * Real.log 2) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by have := Real.log_two_gt_d9; linarith)
    have hf : 2 ^ ⌈4 * Real.log U⌉₊ ≤ L.factorial := by
      have := Nat.factorial_mul_pow_le_factorial (m := 1) (n := ⌈4 * Real.log U⌉₊)
      rw [Nat.factorial_one, one_mul, show 1 + 1 = 2 by rfl, add_comm] at this
      exact this
    have hfr : (2 : ℝ) ^ ⌈4 * Real.log U⌉₊ ≤ L.factorial := by exact_mod_cast hf
    calc 16 * K * (2 * ((Xw U' * Nw (49 / 2) U' : ℕ) : ℝ)) ^ 2 ≤ 16 * (1 + 2 * Real.log U) * U ^ (15 / 13 : ℝ) := by
          gcongr
      _ ≤ U ^ (5 / 2 : ℝ) := h4'
      _ ≤ U ^ (4 * Real.log 2) := h52
      _ = (2 : ℝ) ^ (4 * Real.log U) := e.symm
      _ ≤ (2 : ℝ) ^ (⌈4 * Real.log U⌉₊) := h2pow
      _ ≤ L.factorial := hfr
  have hW : 154 * Cdiv (η / 1000) ^ 154 ≤ 6 * (1 / (16 * K)) ^ 77 * c₀ * U ^ (η / 2) := by
    have hK16 : (16 * K) ^ 77 ≤ (16 * (1 + 2 * Real.log U)) ^ 77 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 77
    have hAD : A * (16 * K) ^ 77 ≤ U ^ (η / 2) := (mul_le_mul_of_nonneg_left hK16 hA0).trans h5
    have hD0 : 0 < (16 * K) ^ 77 := by positivity
    have e1 : 154 * Cdiv (η / 1000) ^ 154 = 6 * c₀ * A := by rw [hA]; field_simp
    rw [e1, one_div_pow, show 6 * (1 / (16 * K) ^ 77) * c₀ * U ^ (η / 2) = 6 * c₀ * (U ^ (η / 2) / (16 * K) ^ 77) by
      ring]
    gcongr
    rw [le_div_iff₀ hD0]; exact hAD
  have hwc := window_classes_gm hη hη1 hC₁0 hC₁ hC₄0 h4 hσ hσ1 (by linarith) hY8 hUY hX hN hM hXU2 hXN hL1 htail
    hW h6 h7 h8 Z hZ
  rw [hYU] at hwc
  refine hwc.trans ?_
  -- the classes as powers of `U`
  have hKL : K * L ≤ U ^ η := by
    calc K * L ≤ (1 + 2 * Real.log U) * (4 * Real.log U + 2) :=
          mul_le_mul hK hLle (by positivity) (by positivity)
      _ ≤ U ^ η := h9
  have hpow : U ^ η * U ^ (30 / 13 * (1 - σ) + 8 * η) = U ^ E := by
    rw [← Real.rpow_add hU0, hE]; congr 1; ring
  have hpart1 : 2 * (K * L * (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)))) ≤
      2 * (154 * (4 * C₁ + 864)) * U ^ E := by
    calc 2 * (K * L * (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η))))
        = 2 * (154 * (4 * C₁ + 864)) * ((K * L) * U ^ (30 / 13 * (1 - σ) + 8 * η)) := by ring
      _ ≤ 2 * (154 * (4 * C₁ + 864)) * (U ^ η * U ^ (30 / 13 * (1 - σ) + 8 * η)) := by gcongr
      _ = 2 * (154 * (4 * C₁ + 864)) * U ^ E := by rw [hpow]
  have hpart3 := class3_bound_gm (σ := σ) hη hη1 hC₄0 hσ1 (by linarith : 8 ≤ U) hXU'
  rw [← hE] at hpart3
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have hlogU : Real.log U ≤ Real.log U ^ 11 := by
    calc Real.log U = Real.log U ^ 1 := (pow_one _).symm
      _ ≤ Real.log U ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hUE0 : 0 ≤ U ^ E := by positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (K * L * (154 * ((4 * C₁ + 864) * U ^ (30 / 13 * (1 - σ) + 8 * η)))) +
        27 * (3 * KG * (U ^ (1 / 2 : ℝ)) ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * ((Xw U' : ℕ) : ℝ) ^ 4 *
          (C₄ * (2 * U + 2) ^ (1 + η)))
      ≤ 2 * (Kc * Real.log U) * (2 * (154 * (4 * C₁ + 864)) * U ^ E + 243 * (15 * KG) ^ 4 * C₄ * U ^ E) := by
        gcongr
    _ = Cmain * Real.log U * U ^ E := by rw [hCmain]; ring
    _ ≤ Cmain * Real.log U ^ 11 * U ^ E := by gcongr
    _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by gcongr; linarith


/-- **The density estimate with Guth and Maynard's exponent on `7/10 + η ≤ σ ≤ 4/5`**: for every `0 < η ≤ 1/100`
there is `C ≥ 0` with `N(σ, T) ≤ C T^{(30/13)(1−σ)+9η}(log T)^{12}` for `T ≥ 2` (`ZetaIngham.nx_le_of_windows` with
`window_count_gm`). -/
theorem nx_gm {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 100) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 7 / 10 + η ≤ σ → σ ≤ 4 / 5 →
      (NX (σ - 1 / 2) T : ℝ) ≤ C * T ^ (30 / 13 * (1 - σ) + 9 * η) * Real.log T ^ 12 := by
  obtain ⟨Cw, hCw0, hCw⟩ := window_count_gm hη hη1
  refine ⟨((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw, by positivity, fun T hT σ hσ hσ1 => ?_⟩
  have he0 : 0 ≤ 30 / 13 * (1 - σ) + 9 * η := by nlinarith
  exact nx_le_of_windows he0 hCw0 (fun U hU Z hZ => hCw σ hσ hσ1 U hU Z hZ) hT

end ZetaGMWin

#print axioms ZetaGMWin.taylor_pick_dp
#print axioms ZetaGMWin.choose_m100
#print axioms ZetaGMWin.dp_eq_pv
#print axioms ZetaGMWin.pieceIdx_spec
#print axioms ZetaGMWin.pieceIdx_lt
#print axioms ZetaGMWin.mem_pieceS
#print axioms ZetaGMWin.pow_piece_pick
#print axioms ZetaGMWin.piece_exp
#print axioms ZetaGMWin.piece_count
#print axioms ZetaGMWin.poly_count_gm
#print axioms ZetaGMWin.class_poly_gm
#print axioms ZetaGMWin.window_classes_gm
#print axioms ZetaGMWin.class3_bound_gm
#print axioms ZetaGMWin.ev_log_pow
#print axioms ZetaGMWin.eventually_gm
#print axioms ZetaGMWin.window_count_gm
#print axioms ZetaGMWin.nx_gm
