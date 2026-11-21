/-
# The exponents of Chen, Gupta and Li's count of large values

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResProd.lean` counts the characters at which a product of smoothed prime sums is large by Chen, Gupta and Li's
large-values estimate (their Proposition 3.1, at one point per character: `LinnikCGLLV.cgl_all`) for a power of the
product, a polynomial of length about `M^k` for a product of length `M`: where `M^k ≥ q^{2/3}` and the size is
between the powers `7/10` and `4/5` of the length, the characters are at most

`q^ε (M^{2k(1−u)} + q^{1/2} M^{k(3−4u)} + q^{4/3} M^{k(2−4u)})`

up to a constant. For `M^k` between `q^{5/6}` and `q` and `u = 3/4` that is `q^{1/2+ε}`, the count of the density
hypothesis, where the moment gives `q^{1 − ks/2}`. This file has the bound, its exponents and the facts that the
count reads from them.

* `sum_Ioc_dyadic`, `exists_large_of_sum`: a sum over `(M, M·2^J]` is the sum of its `J` dyadic blocks, one of which
  has at least a `J`-th of its size.
* `lvB q X V = X²/V² + q^{1/2}X³/V⁴ + q^{4/3}X²/V⁴`, Proposition 3.1's bound at the length `X`.
* `lvRaw k s u = max(2ks(1 − u), 1/2 + ks(3 − 4u), 4/3 + ks(2 − 4u))`, the count's exponent for a sum of length
  `q^s` at the size `u`; `lvExp k s u`, the same with its range and margins (`lvE = 10⁻⁵`): `lvRaw` at
  `min(u, 4/5 − lvE)` plus `lvE` where `ks ≥ 2/3 + lvE` and `u ≥ 7/10 + lvE`, at most `1`, and `1` elsewhere;
  `lvExp_anti`, `lvExp_nonneg`, `lvExp_of_lt`, `lvExp_of_big`.
* `lv_conds`, `lv_fac`, `lvB_le`, `lvB_nonneg`: Proposition 3.1's conditions at `Q^k = q^m`, and its factor and
  bound in exponents.

The file imports `SieveResCount.lean`, `LinnikCGLLV.lean` and `LinnikDensity.lean`.
-/
import SieveResCount
import LinnikCGLLV
import LinnikDensity

open Complex Finset

noncomputable section

namespace SieveTypeIIHM

open DirMean SieveTypeII DirichletCharacter

variable {q : ℕ}

/-! ### Dyadic blocks -/

/-- A sum over `(M, M·2^J]` is the sum of its `J` dyadic blocks. -/
lemma sum_Ioc_dyadic (g : ℕ → ℂ) (M J : ℕ) :
    ∑ n ∈ Finset.Ioc M (M * 2 ^ J), g n =
      ∑ i ∈ Finset.range J, ∑ n ∈ Finset.Ioc (M * 2 ^ i) (M * 2 ^ (i + 1)), g n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ioc_consecutive g (Nat.le_mul_of_pos_right M (by positivity))
      (Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)))).symm

/-- Of `J ≥ 1` numbers whose sum has modulus at least `V`, one has modulus at least `V/J`. -/
lemma exists_large_of_sum {J : ℕ} (hJ : 0 < J) (b : ℕ → ℂ) {V : ℝ} (hV : V ≤ ‖∑ i ∈ Finset.range J, b i‖) :
    ∃ i < J, V / J ≤ ‖b i‖ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have h1 : ‖∑ i ∈ Finset.range J, b i‖ ≤ ∑ i ∈ Finset.range J, ‖b i‖ := norm_sum_le _ _
  have h2 : ∑ i ∈ Finset.range J, ‖b i‖ < ∑ _i ∈ Finset.range J, V / J :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hJ.ne')
      fun i hi => hcon i (Finset.mem_range.1 hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hJ0.ne'] at h2
  linarith

/-! ### Chen, Gupta and Li's bound -/

/-- Chen, Gupta and Li's bound of Proposition 3.1 at a length `X` and a size `V`, with `T = 1`:
`X²/V² + q^{1/2}X³/V⁴ + q^{4/3}X²/V⁴`. -/
def lvB (q : ℕ) (X V : ℝ) : ℝ :=
  X ^ 2 / V ^ 2 + (q : ℝ) ^ (1 / 2 : ℝ) * X ^ 3 / V ^ 4 + (q : ℝ) ^ (4 / 3 : ℝ) * X ^ 2 / V ^ 4

/-! ### The exponents -/

/-- The exponent of the count for the `k`-th power of a sum of length `q^s` at the size `u` of the sum:
`max(2ks(1 − u), 1/2 + ks(3 − 4u), 4/3 + ks(2 − 4u))`. -/
def lvRaw (k : ℕ) (s u : ℝ) : ℝ :=
  max (2 * (k * s) * (1 - u)) (max (1 / 2 + k * s * (3 - 4 * u)) (4 / 3 + k * s * (2 - 4 * u)))

/-- The margin of the count by large values: `10⁻⁵`. -/
def lvE : ℝ := 1 / 10 ^ 5

/-- **The exponent of the count by large values, with its range**: where `ks ≥ 2/3 + 10⁻⁵` and `u ≥ 7/10 + 10⁻⁵`,
`lvRaw` at `min(u, 4/5 − 10⁻⁵)` plus `10⁻⁵`, and at most `1`; `1` elsewhere. -/
def lvExp (k : ℕ) (s u : ℝ) : ℝ :=
  if 2 / 3 + lvE ≤ k * s ∧ 7 / 10 + lvE ≤ u then min 1 (lvRaw k s (min u (4 / 5 - lvE)) + lvE) else 1

/-- `lvRaw k s u` does not increase in `u`, for `s ≥ 0`. -/
lemma lvRaw_anti {k : ℕ} {s u u' : ℝ} (hs : 0 ≤ s) (hu : u ≤ u') : lvRaw k s u' ≤ lvRaw k s u := by
  unfold lvRaw
  have hks : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg k) hs
  have h1 : 2 * ((k : ℝ) * s) * (1 - u') ≤ 2 * ((k : ℝ) * s) * (1 - u) := by nlinarith
  have h2 : 1 / 2 + (k : ℝ) * s * (3 - 4 * u') ≤ 1 / 2 + (k : ℝ) * s * (3 - 4 * u) := by nlinarith
  have h3 : 4 / 3 + (k : ℝ) * s * (2 - 4 * u') ≤ 4 / 3 + (k : ℝ) * s * (2 - 4 * u) := by nlinarith
  exact max_le_max h1 (max_le_max h2 h3)

/-- `lvExp k s u ≤ 1`. -/
lemma lvExp_le_one (k : ℕ) (s u : ℝ) : lvExp k s u ≤ 1 := by
  unfold lvExp
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `lvExp k s u ≥ 0`, for `s ≥ 0`. -/
lemma lvExp_nonneg {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : ℝ) : 0 ≤ lvExp k s u := by
  unfold lvExp
  split_ifs with h
  · refine le_min zero_le_one ?_
    have h1 : min u (4 / 5 - lvE) ≤ 4 / 5 - lvE := min_le_right _ _
    have h2 : 2 * ((k : ℝ) * s) * (1 - min u (4 / 5 - lvE)) ≤ lvRaw k s (min u (4 / 5 - lvE)) := le_max_left _ _
    have hE : (0 : ℝ) < lvE := by unfold lvE; norm_num
    have hks : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg k) hs
    nlinarith
  · exact zero_le_one

/-- `lvExp k s u = 1` below the range of sizes. -/
lemma lvExp_of_lt {k : ℕ} {s u : ℝ} (hu : u < 7 / 10 + lvE) : lvExp k s u = 1 := by
  unfold lvExp
  exact ite_eq_right fun h => absurd h.2 (not_le.2 hu)

/-- `lvExp k s u = 1` for `ks ≥ 5/2`. -/
lemma lvExp_of_big {k : ℕ} {s u : ℝ} (hks : 5 / 2 ≤ (k : ℝ) * s) : lvExp k s u = 1 := by
  unfold lvExp
  split_ifs with h
  · refine min_eq_left ?_
    have h1 : min u (4 / 5 - lvE) ≤ 4 / 5 - lvE := min_le_right _ _
    have h2 : 2 * ((k : ℝ) * s) * (1 - min u (4 / 5 - lvE)) ≤ lvRaw k s (min u (4 / 5 - lvE)) := le_max_left _ _
    have hE : (0 : ℝ) < lvE := by unfold lvE; norm_num
    nlinarith
  · rfl

/-- `lvExp k s u` does not increase in `u`, for `s ≥ 0`. -/
lemma lvExp_anti {k : ℕ} {s u u' : ℝ} (hs : 0 ≤ s) (hu : u ≤ u') : lvExp k s u' ≤ lvExp k s u := by
  by_cases h : 2 / 3 + lvE ≤ (k : ℝ) * s ∧ 7 / 10 + lvE ≤ u
  · have h' : 2 / 3 + lvE ≤ (k : ℝ) * s ∧ 7 / 10 + lvE ≤ u' := ⟨h.1, h.2.trans hu⟩
    unfold lvExp
    rw [ite_eq_left h, ite_eq_left h']
    have h1 := lvRaw_anti (k := k) hs (min_le_min hu (le_refl (4 / 5 - lvE)))
    exact min_le_min le_rfl (by linarith)
  · have h1 : lvExp k s u = 1 := by unfold lvExp; exact ite_eq_right h
    rw [h1]
    exact lvExp_le_one _ _ _

/-- The conditions of Chen, Gupta and Li's count for a power (`SieveTypeIIHM.card_prodSp_pow_large`) at `Q^k = q^m`
and `V = q^{mu}`, for `m ≥ 2/3 + 10⁻⁵`, `7/10 + 10⁻⁵ ≤ u ≤ 4/5 − 10⁻⁵` and `4·2^k·D ≤ q^{10⁻⁵/2}`. -/
lemma lv_conds {q : ℕ} {Q m u D : ℝ} {k : ℕ} (hq1 : 1 < (q : ℝ)) (hQk : Q ^ k = (q : ℝ) ^ m)
    (hm : 2 / 3 + lvE ≤ m) (hu0 : 7 / 10 + lvE ≤ u) (hu1 : u ≤ 4 / 5 - lvE) (hD1 : 1 ≤ D)
    (hB : 4 * 2 ^ k * D ≤ (q : ℝ) ^ (lvE / 2)) :
    2 * (q : ℝ) ^ (2 / 3 : ℝ) + 2 ≤ (Q / 2) ^ k ∧ ((2 * Q) ^ k) ^ (7 / 10 : ℝ) * D ≤ (q : ℝ) ^ (m * u) ∧
      (q : ℝ) ^ (m * u) ≤ ((Q / 2) ^ k / 2) ^ (4 / 5 : ℝ) := by
  have hE0 : (0 : ℝ) < lvE := by unfold lvE; norm_num
  have hq0 : (0 : ℝ) < q := by linarith
  have h2k1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
  have hqm0 : 0 < (q : ℝ) ^ m := Real.rpow_pos_of_pos hq0 _
  have h2Qk : (2 * Q) ^ k = 2 ^ k * (q : ℝ) ^ m := by rw [mul_pow, hQk]
  have hQ2k : (Q / 2) ^ k = (q : ℝ) ^ m / 2 ^ k := by rw [div_pow, hQk]
  have hqE : (q : ℝ) ^ (lvE / 2) ≤ (q : ℝ) ^ lvE := Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  have hV0 : 0 < (q : ℝ) ^ (m * u) := Real.rpow_pos_of_pos hq0 _
  -- `4·2^k`, `2^k·D` and `2^k·2` are at most `q^{lvE/2}`
  have hb1 : 4 * (2 : ℝ) ^ k ≤ (q : ℝ) ^ (lvE / 2) := by
    have h5 : (4 : ℝ) * 2 ^ k * 1 ≤ 4 * 2 ^ k * D := mul_le_mul_of_nonneg_left hD1 (by positivity)
    linarith
  have hb2 : (2 : ℝ) ^ k * D ≤ (q : ℝ) ^ (lvE / 2) := by
    have h5 : (0 : ℝ) ≤ 2 ^ k * D := by positivity
    linarith
  have hb3 : (2 : ℝ) ^ k * 2 ≤ (q : ℝ) ^ (lvE / 2) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ2k, le_div_iff₀ h2k0]
    have h1 : (q : ℝ) ^ (2 / 3 : ℝ) * (q : ℝ) ^ lvE ≤ (q : ℝ) ^ m := by
      rw [← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq1.le hm
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hq1.le (by norm_num)
    have h4 : 1 * (2 : ℝ) ^ k ≤ (q : ℝ) ^ (2 / 3 : ℝ) * 2 ^ k := mul_le_mul_of_nonneg_right h2 h2k0.le
    calc (2 * (q : ℝ) ^ (2 / 3 : ℝ) + 2) * 2 ^ k ≤ (q : ℝ) ^ (2 / 3 : ℝ) * (4 * 2 ^ k) := by linarith
      _ ≤ (q : ℝ) ^ (2 / 3 : ℝ) * (q : ℝ) ^ lvE :=
          mul_le_mul_of_nonneg_left (hb1.trans hqE) (by positivity)
      _ ≤ (q : ℝ) ^ m := h1
  · rw [h2Qk, Real.mul_rpow h2k0.le hqm0.le, ← Real.rpow_mul hq0.le]
    have h1 : ((2 : ℝ) ^ k) ^ (7 / 10 : ℝ) ≤ 2 ^ k := by
      conv_rhs => rw [← Real.rpow_one ((2 : ℝ) ^ k)]
      exact Real.rpow_le_rpow_of_exponent_le h2k1 (by norm_num)
    have h2 : (q : ℝ) ^ (lvE / 2) * (q : ℝ) ^ (m * (7 / 10)) ≤ (q : ℝ) ^ (m * u) := by
      rw [← Real.rpow_add hq0]
      refine Real.rpow_le_rpow_of_exponent_le hq1.le ?_
      nlinarith
    have hq7 : 0 ≤ (q : ℝ) ^ (m * (7 / 10)) := Real.rpow_nonneg hq0.le _
    have hD0 : 0 ≤ D := by linarith
    calc ((2 : ℝ) ^ k) ^ (7 / 10 : ℝ) * (q : ℝ) ^ (m * (7 / 10)) * D
        ≤ 2 ^ k * (q : ℝ) ^ (m * (7 / 10)) * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hq7) hD0
      _ = 2 ^ k * D * (q : ℝ) ^ (m * (7 / 10)) := by ring
      _ ≤ (q : ℝ) ^ (lvE / 2) * (q : ℝ) ^ (m * (7 / 10)) := mul_le_mul_of_nonneg_right hb2 hq7
      _ ≤ (q : ℝ) ^ (m * u) := h2
  · have h1 : (Q / 2) ^ k / 2 = (q : ℝ) ^ m / (2 ^ k * 2) := by rw [hQ2k, div_div]
    rw [h1, Real.div_rpow hqm0.le (by positivity), ← Real.rpow_mul hq0.le, le_div_iff₀ (by positivity)]
    have h2 : ((2 : ℝ) ^ k * 2) ^ (4 / 5 : ℝ) ≤ 2 ^ k * 2 := by
      conv_rhs => rw [← Real.rpow_one ((2 : ℝ) ^ k * 2)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h4 : (q : ℝ) ^ (m * u) * (q : ℝ) ^ (lvE / 2) ≤ (q : ℝ) ^ (m * (4 / 5)) := by
      rw [← Real.rpow_add hq0]
      refine Real.rpow_le_rpow_of_exponent_le hq1.le ?_
      nlinarith
    calc (q : ℝ) ^ (m * u) * ((2 : ℝ) ^ k * 2) ^ (4 / 5 : ℝ) ≤ (q : ℝ) ^ (m * u) * (q : ℝ) ^ (lvE / 2) :=
          mul_le_mul_of_nonneg_left (h2.trans hb3) hV0.le
      _ ≤ (q : ℝ) ^ (m * (4 / 5)) := h4

/-- The factor `q^ε(q(2Q)^k)^ε` at `ε = 10⁻⁵/5` is at most `2^k q^{10⁻⁵}`, for `Q^k = q^m` with `m ≤ 5/2`. -/
lemma lv_fac {q : ℕ} {Q m : ℝ} {k : ℕ} (hq1 : 1 < (q : ℝ)) (hQk : Q ^ k = (q : ℝ) ^ m) (hm : m ≤ 5 / 2) :
    (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q) ^ k) ^ (lvE / 5) ≤ 2 ^ k * (q : ℝ) ^ lvE := by
  have hE0 : (0 : ℝ) < lvE := by unfold lvE; norm_num
  have hE1 : lvE ≤ 1 := by unfold lvE; norm_num
  have hq0 : (0 : ℝ) < q := by linarith
  have h2k1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
  have h2Qk : (2 * Q) ^ k = 2 ^ k * (q : ℝ) ^ m := by rw [mul_pow, hQk]
  rw [h2Qk]
  have h1 : (q : ℝ) * (2 ^ k * (q : ℝ) ^ m) = 2 ^ k * (q : ℝ) ^ (1 + m) := by
    rw [Real.rpow_add hq0, Real.rpow_one]; ring
  rw [h1, Real.mul_rpow h2k0.le (Real.rpow_nonneg hq0.le _), ← Real.rpow_mul hq0.le]
  have h2 : ((2 : ℝ) ^ k) ^ (lvE / 5) ≤ 2 ^ k := by
    conv_rhs => rw [← Real.rpow_one ((2 : ℝ) ^ k)]
    exact Real.rpow_le_rpow_of_exponent_le h2k1 (by linarith)
  have h3 : (q : ℝ) ^ (lvE / 5) * (q : ℝ) ^ ((1 + m) * (lvE / 5)) ≤ (q : ℝ) ^ lvE := by
    rw [← Real.rpow_add hq0]
    refine Real.rpow_le_rpow_of_exponent_le hq1.le ?_
    have h4 : m * lvE ≤ 5 / 2 * lvE := mul_le_mul_of_nonneg_right hm hE0.le
    linarith
  have hq5 : 0 ≤ (q : ℝ) ^ (lvE / 5) := Real.rpow_nonneg hq0.le _
  have hq6 : 0 ≤ (q : ℝ) ^ ((1 + m) * (lvE / 5)) := Real.rpow_nonneg hq0.le _
  calc (q : ℝ) ^ (lvE / 5) * (((2 : ℝ) ^ k) ^ (lvE / 5) * (q : ℝ) ^ ((1 + m) * (lvE / 5)))
      = ((2 : ℝ) ^ k) ^ (lvE / 5) * ((q : ℝ) ^ (lvE / 5) * (q : ℝ) ^ ((1 + m) * (lvE / 5))) := by ring
    _ ≤ 2 ^ k * (q : ℝ) ^ lvE := mul_le_mul h2 h3 (mul_nonneg hq5 hq6) (by positivity)

/-- `lvB` at the length `(2Q)^k = 2^k q^m` and the size `q^{mu}/D`, `D ≥ 1`, is at most `3D⁴8^k q^R` when the three
exponents `2m(1 − u)`, `1/2 + m(3 − 4u)` and `4/3 + m(2 − 4u)` are at most `R`. -/
lemma lvB_le {q : ℕ} {Q m u D R : ℝ} {k : ℕ} (hq1 : 1 < (q : ℝ)) (hQk : Q ^ k = (q : ℝ) ^ m) (hD1 : 1 ≤ D)
    (h1 : 2 * m * (1 - u) ≤ R) (h2 : 1 / 2 + m * (3 - 4 * u) ≤ R) (h3 : 4 / 3 + m * (2 - 4 * u) ≤ R) :
    lvB q ((2 * Q) ^ k) ((q : ℝ) ^ (m * u) / D) ≤ 3 * (D ^ 4 * 8 ^ k) * (q : ℝ) ^ R := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hD0 : 0 < D := by linarith
  have h2Qk : (2 * Q) ^ k = 2 ^ k * (q : ℝ) ^ m := by rw [mul_pow, hQk]
  unfold lvB
  rw [h2Qk]
  have hV2 : ((q : ℝ) ^ (m * u)) ^ 2 = (q : ℝ) ^ (2 * (m * u)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  have hV4 : ((q : ℝ) ^ (m * u)) ^ 4 = (q : ℝ) ^ (4 * (m * u)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  have hm2 : ((q : ℝ) ^ m) ^ 2 = (q : ℝ) ^ (2 * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  have hm3 : ((q : ℝ) ^ m) ^ 3 = (q : ℝ) ^ (3 * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  have hD2 : D ^ 2 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
  have h4k : ((2 : ℝ) ^ k) ^ 2 ≤ 8 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h8k : ((2 : ℝ) ^ k) ^ 3 = 8 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hD4 : (0 : ℝ) ≤ D ^ 4 := by positivity
  have h8 : (0 : ℝ) ≤ 8 ^ k := by positivity
  have hR0 : 0 < (q : ℝ) ^ R := Real.rpow_pos_of_pos hq0 _
  have t1 : (2 ^ k * (q : ℝ) ^ m) ^ 2 / ((q : ℝ) ^ (m * u) / D) ^ 2 ≤ D ^ 4 * 8 ^ k * (q : ℝ) ^ R := by
    rw [div_pow, mul_pow, hV2, hm2, div_div_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
    have hx : (q : ℝ) ^ (2 * m) ≤ (q : ℝ) ^ R * (q : ℝ) ^ (2 * (m * u)) := by
      rw [← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
    calc ((2 : ℝ) ^ k) ^ 2 * (q : ℝ) ^ (2 * m) * D ^ 2
        = D ^ 2 * ((2 : ℝ) ^ k) ^ 2 * (q : ℝ) ^ (2 * m) := by ring
      _ ≤ D ^ 4 * 8 ^ k * ((q : ℝ) ^ R * (q : ℝ) ^ (2 * (m * u))) :=
          mul_le_mul (mul_le_mul hD2 h4k (by positivity) hD4) hx (by positivity) (by positivity)
      _ = D ^ 4 * 8 ^ k * (q : ℝ) ^ R * (q : ℝ) ^ (2 * (m * u)) := by ring
  have t2 : (q : ℝ) ^ (1 / 2 : ℝ) * (2 ^ k * (q : ℝ) ^ m) ^ 3 / ((q : ℝ) ^ (m * u) / D) ^ 4 ≤
      D ^ 4 * 8 ^ k * (q : ℝ) ^ R := by
    rw [div_pow, mul_pow, hV4, hm3, h8k, div_div_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
    have hx : (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (3 * m) ≤ (q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u)) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
    calc (q : ℝ) ^ (1 / 2 : ℝ) * ((8 : ℝ) ^ k * (q : ℝ) ^ (3 * m)) * D ^ 4
        = D ^ 4 * 8 ^ k * ((q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (3 * m)) := by ring
      _ ≤ D ^ 4 * 8 ^ k * ((q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u))) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = D ^ 4 * 8 ^ k * (q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u)) := by ring
  have t3 : (q : ℝ) ^ (4 / 3 : ℝ) * (2 ^ k * (q : ℝ) ^ m) ^ 2 / ((q : ℝ) ^ (m * u) / D) ^ 4 ≤
      D ^ 4 * 8 ^ k * (q : ℝ) ^ R := by
    rw [div_pow, mul_pow, hV4, hm2, div_div_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
    have hx : (q : ℝ) ^ (4 / 3 : ℝ) * (q : ℝ) ^ (2 * m) ≤ (q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u)) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
    calc (q : ℝ) ^ (4 / 3 : ℝ) * (((2 : ℝ) ^ k) ^ 2 * (q : ℝ) ^ (2 * m)) * D ^ 4
        = D ^ 4 * ((2 : ℝ) ^ k) ^ 2 * ((q : ℝ) ^ (4 / 3 : ℝ) * (q : ℝ) ^ (2 * m)) := by ring
      _ ≤ D ^ 4 * 8 ^ k * ((q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h4k hD4) hx (by positivity) (by positivity)
      _ = D ^ 4 * 8 ^ k * (q : ℝ) ^ R * (q : ℝ) ^ (4 * (m * u)) := by ring
  linarith

/-- `lvB` is nonnegative at a nonnegative length. -/
lemma lvB_nonneg (q : ℕ) {X : ℝ} (hX : 0 ≤ X) (V : ℝ) : 0 ≤ lvB q X V := by
  unfold lvB
  have hq12 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hq43 : (0 : ℝ) ≤ (q : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  positivity

end SieveTypeIIHM

