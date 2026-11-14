/-
# The characters at which a smoothed prime sum is large, by the large values of its powers

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResCount.card_Sp_large` counts the characters at which a smoothed prime sum `Sp χ f0 Q y` is at least `Q^u` by
the `2k`-th moment. This file counts them by Chen, Gupta and Li's large-values estimate (their Proposition 3.1, at
one point per character: `LinnikCGLLV.cgl_all`) for the `k`-th power of the sum, a polynomial of length about `Q^k`
whose coefficients are at most `k^k F₀^k`: where `Q^k ≥ q^{2/3}` and the size is between the powers `7/10` and `4/5`
of the length, the characters are at most

`q^ε (Q^{2k(1−u)} + q^{1/2} Q^{k(3−4u)} + q^{4/3} Q^{k(2−4u)})`

up to a constant. For `Q^k` between `q^{5/6}` and `q` and `u = 3/4` that is `q^{1/2+ε}`, the count of the density
hypothesis, where the moment gives `q^{1 − ks/2}`.

* `norm_powCoeff_le`, `powCoeff_eq_zero`: the coefficients of a `k`-th power are at most `F·B^k`, and vanish outside
  `[lo^k, hi^k]` when the polynomial's own vanish outside `[lo, hi]`.
* `sum_Ioc_dyadic`, `exists_large_of_sum`: a sum over `(M, M·2^J]` is the sum of its `J` dyadic blocks, one of which
  has at least a `J`-th of its size.
* `lvB q X V = X²/V² + q^{1/2}X³/V⁴ + q^{4/3}X²/V⁴`, Proposition 3.1's bound at the length `X`.
* `card_Sp_pow_large`, **the count for a power**: for `Q ≥ 4`, `k ≥ 1`, `(Q/2)^k ≥ 2q^{2/3} + 2` and
  `((2Q)^k)^{7/10}·D ≤ V ≤ ((Q/2)^k/2)^{4/5}` with `D = (2k+1)k^k F₁^k`,
  `#{χ : V ≤ |Sp χ f0 Q y|^k} ≤ (2k+1)·C·q^ε(q(2Q)^k)^ε·lvB q ((2Q)^k) (V/D)`.

* `lvRaw k s u = max(2ks(1 − u), 1/2 + ks(3 − 4u), 4/3 + ks(2 − 4u))`, the count's exponent for a sum of length
  `q^s` at the size `u`; `lvExp k s u`, the same with its range and margins (`lvE = 10⁻⁵`): `lvRaw` at
  `min(u, 4/5 − lvE)` plus `lvE` where `ks ≥ 2/3 + lvE` and `u ≥ 7/10 + lvE`, at most `1`, and `1` elsewhere;
  `lvExp_anti`, `lvExp_nonneg`, `lvExp_of_lt`, `lvExp_of_big`.
* `card_Sp_large_lv`, **the count in exponents**: for `q` large, `Q ≥ 4` and `1 ≤ k ≤ k_max`,
  `#{χ : Q^u ≤ |Sp χ f0 Q y|} ≤ C q^{lvExp k s u}`, `s = log_q Q` (`lv_conds`, `lv_fac`, `lvB_le`).

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

/-! ### The coefficients of a power -/

/-- `|c_n| ≤ F·B^k` for the coefficients `c = powCoeff S k a` of a `k`-th power, when every `n` is the product of
at most `F` tuples of `k` elements of `S` and `|a_j| ≤ B` on `S`. -/
lemma norm_powCoeff_le {S : Finset ℕ} (k : ℕ) (a : ℕ → ℂ) {F B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j ∈ S, ‖a j‖ ≤ B)
    (hF : ∀ n, (((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card : ℝ) ≤ F) (n : ℕ) :
    ‖powCoeff S k a n‖ ≤ F * B ^ k := by
  classical
  unfold powCoeff
  set fib := (Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n with hfib
  have hterm : ∀ x ∈ fib, ‖∏ i, a (x i)‖ ≤ B ^ k := by
    intro x hx
    have hxS : ∀ i, x i ∈ S := fun i => Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i
    rw [norm_prod]
    calc ∏ i, ‖a (x i)‖ ≤ ∏ _i : Fin k, B :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hB _ (hxS i))
      _ = B ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖∑ x ∈ fib, ∏ i, a (x i)‖ ≤ ∑ x ∈ fib, ‖∏ i, a (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ fib, B ^ k := Finset.sum_le_sum hterm
    _ = (fib.card : ℝ) * B ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ F * B ^ k := mul_le_mul_of_nonneg_right (hF n) (pow_nonneg hB0 k)

/-- The coefficients of a `k`-th power vanish outside `[lo^k, hi^k]` when the polynomial's own vanish outside
`[lo, hi]`, for `lo ≥ 0`. -/
lemma powCoeff_eq_zero {S : Finset ℕ} (k : ℕ) (a : ℕ → ℂ) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (ha : ∀ j ∈ S, ((j : ℝ) < lo ∨ hi < (j : ℝ)) → a j = 0) {n : ℕ}
    (hn : (n : ℝ) < lo ^ k ∨ hi ^ k < (n : ℝ)) : powCoeff S k a n = 0 := by
  classical
  unfold powCoeff
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
  have hxS' : ∀ i, x i ∈ S := fun i => Fintype.mem_piFinset.1 hxS i
  by_contra hne
  have hall : ∀ i, lo ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ hi := by
    intro i
    by_contra hcon
    have h0 : a (x i) = 0 := by
      refine ha (x i) (hxS' i) ?_
      rcases not_and_or.1 hcon with h | h
      · exact Or.inl (not_le.1 h)
      · exact Or.inr (not_le.1 h)
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hprod : (n : ℝ) = ∏ i, (x i : ℝ) := by rw [← hxn]; push_cast; rfl
  have h1 : lo ^ k ≤ (n : ℝ) := by
    rw [hprod]
    calc lo ^ k = ∏ _i : Fin k, lo := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, (x i : ℝ) := Finset.prod_le_prod₀ (fun _ _ => hlo) (fun i _ => (hall i).1)
  have h2 : (n : ℝ) ≤ hi ^ k := by
    rw [hprod]
    calc ∏ i, (x i : ℝ) ≤ ∏ _i : Fin k, hi :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => (hall i).2)
      _ = hi ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rcases hn with h | h <;> linarith

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

/-! ### The count for a power -/

/-- Chen, Gupta and Li's bound of Proposition 3.1 at a length `X` and a size `V`, with `T = 1`:
`X²/V² + q^{1/2}X³/V⁴ + q^{4/3}X²/V⁴`. -/
def lvB (q : ℕ) (X V : ℝ) : ℝ :=
  X ^ 2 / V ^ 2 + (q : ℝ) ^ (1 / 2 : ℝ) * X ^ 3 / V ^ 4 + (q : ℝ) ^ (4 / 3 : ℝ) * X ^ 2 / V ^ 4

/-- **The characters at which a power of a smoothed prime sum is large, by Chen, Gupta and Li's Proposition 3.1.**
Given the proposition (`hP`) and `0 < ε ≤ 1`, there is `C ≥ 0` such that, for `f0` with `|f0| ≤ F₁`, `F₁ ≥ 1`, and
support in `[1/2, 2]`, `Q ≥ 4`, `k ≥ 1`, `(Q/2)^k ≥ 2q^{2/3} + 2` and
`((2Q)^k)^{7/10}·D ≤ V ≤ ((Q/2)^k/2)^{4/5}`, `D = (2k+1)k^k F₁^k`:
`#{χ : V ≤ |Sp χ f0 Q y|^k} ≤ (2k+1)·C·q^ε·(q(2Q)^k)^ε·lvB q ((2Q)^k) (V/D)`. The power is a polynomial over the
products of `k` primes, with coefficients at most `k^k F₁^k`, supported in `[(Q/2)^k, (2Q)^k]`; that range is cut in
`2k + 1` dyadic blocks, and the proposition counts the characters at which a block has a `(2k+1)`-th of the size. -/
theorem card_Sp_pow_large (hP : LinnikCGLLV.CGLProp31) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (f0 : ℝ → ℝ) (F₁ : ℝ), 1 ≤ F₁ → (∀ u, |f0 u| ≤ F₁) →
      Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (Q y : ℝ) (k : ℕ) (V : ℝ), 1 ≤ k → 4 ≤ Q →
      2 * (q : ℝ) ^ (2 / 3 : ℝ) + 2 ≤ (Q / 2) ^ k →
      ((2 * Q) ^ k) ^ (7 / 10 : ℝ) * ((2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k) ≤ V →
      V ≤ ((Q / 2) ^ k / 2) ^ (4 / 5 : ℝ) →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k).card : ℝ) ≤
        (2 * (k : ℝ) + 1) * (C * (q : ℝ) ^ ε * ((q : ℝ) * (2 * Q) ^ k) ^ ε *
          lvB q ((2 * Q) ^ k) (V / ((2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k))) := by
  obtain ⟨C, hC0, hC⟩ := LinnikCGLLV.cgl_all hP hε hε1
  refine ⟨C, hC0, fun q _ f0 F₁ hF1 hF₀ hsupp Q y k V hk hQ h23 hV1 hV2 => ?_⟩
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ0 : 0 < Q := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hF10 : 0 ≤ F₁ := by linarith
  -- the constants
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (k : ℝ) ^ k * F₁ ^ k := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hE]
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hk)
    have h2 : (1 : ℝ) ≤ F₁ ^ k := one_le_pow₀ hF1
    nlinarith
  have hE0 : 0 < E := by linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = 2 * k + 1 := ⟨_, rfl⟩
  have hJpos : 0 < J := by omega
  have hJr : (J : ℝ) = 2 * (k : ℝ) + 1 := by rw [hJ]; push_cast; ring
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
  have hD : (2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k = J * E := by rw [hJr, hE]; ring
  rw [hD] at hV1 ⊢
  have hJE0 : (0 : ℝ) < J * E := by positivity
  have hJE1 : (1 : ℝ) ≤ J * E := by nlinarith
  -- the sizes of the power's range
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 * Q) ^ k := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (Q / 2) ^ k := ⟨_, rfl⟩
  rw [← hX] at hV1 ⊢
  rw [← hY] at h23 hV2
  have hXY : X = 4 ^ k * Y := by
    rw [hX, hY, ← mul_pow]; congr 1; ring
  have hY2 : 2 ≤ Y := by
    have h1 : (0 : ℝ) ≤ (q : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
    linarith
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := by rw [hXY]; positivity
  have hV0 : 0 < V := by
    have h1 : 0 < X ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hX0 _
    exact lt_of_lt_of_le (mul_pos h1 hJE0) hV1
  -- the lower end of the blocks
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈Y⌉₊ - 1 := ⟨_, rfl⟩
  have hceil2 : 2 ≤ ⌈Y⌉₊ := by
    have h1 : ((2 : ℕ) : ℝ) ≤ Y := by exact_mod_cast hY2
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil Y))
  have hM1 : 1 ≤ M := by omega
  have hMceil : M + 1 = ⌈Y⌉₊ := by omega
  have hMlt : (M : ℝ) < Y := by
    have h1 : M < ⌈Y⌉₊ := by omega
    exact Nat.lt_ceil.1 h1
  have hMge : Y - 1 ≤ (M : ℝ) := by
    have h1 : ((⌈Y⌉₊ : ℕ) : ℝ) = (M : ℝ) + 1 := by rw [← hMceil]; push_cast; ring
    have h2 : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
    linarith
  have hMhalf : Y / 2 ≤ (M : ℝ) := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  -- the power's coefficients
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = spSet Q := ⟨_, rfl⟩
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => by rw [hS] at hp; exact (Finset.mem_filter.1 hp).2
  have hS0 : 0 ∉ S := fun h => Nat.not_prime_zero (hSprime 0 h)
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = powCoeff S k (spCoeff f0 Q y) := ⟨_, rfl⟩
  have hnormsp : ∀ j ∈ S, ‖spCoeff f0 Q y j‖ ≤ F₁ := by
    intro j hj
    have hj0 : (0 : ℝ) < (j : ℝ) / Q := div_pos (by exact_mod_cast (hSprime j hj).pos) hQ0
    have h1 : ‖(((j : ℝ) / Q : ℝ) : ℂ) ^ (-(y : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hj0]
      simp
    unfold spCoeff
    rw [norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hF₀ _
  have hcE : ∀ n, ‖c n‖ ≤ E := by
    intro n
    rw [hc, hE]
    exact norm_powCoeff_le k _ hF10 hnormsp
      (fun m => by exact_mod_cast card_tuples_primes_le hSprime k m) n
  have hzsp : ∀ j ∈ S, ((j : ℝ) < Q / 2 ∨ 2 * Q < (j : ℝ)) → spCoeff f0 Q y j = 0 := by
    intro j _ hj
    have hf : f0 ((j : ℝ) / Q) = 0 := by
      by_contra hne
      have hmem := hsupp (Function.mem_support.2 hne)
      rw [Set.mem_Icc] at hmem
      rcases hj with h | h
      · have : (j : ℝ) / Q < 1 / 2 := by rw [div_lt_iff₀ hQ0]; linarith
        linarith [hmem.1]
      · have : 2 < (j : ℝ) / Q := by rw [lt_div_iff₀ hQ0]; linarith
        linarith [hmem.2]
    unfold spCoeff
    rw [hf, Complex.ofReal_zero, mul_zero]
  have hczero : ∀ n : ℕ, n ∉ Finset.Ioc M (M * 2 ^ J) → c n = 0 := by
    intro n hn
    rw [hc]
    refine powCoeff_eq_zero k _ (by linarith : (0 : ℝ) ≤ Q / 2) hzsp ?_
    rw [← hY, ← hX]
    rw [Finset.mem_Ioc, not_and_or] at hn
    rcases hn with h | h
    · left
      have h1 : (n : ℝ) ≤ M := by exact_mod_cast not_lt.1 h
      linarith
    · right
      have h1 : M * 2 ^ J < n := not_le.1 h
      have h2 : ((M * 2 ^ J : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast h1
      have h3 : X ≤ ((M * 2 ^ J : ℕ) : ℝ) := by
        push_cast
        have h4 : (2 : ℝ) ^ J = 2 * 4 ^ k := by
          rw [hJ, pow_succ, pow_mul]; norm_num; ring
        rw [hXY, h4]
        have h5 : (0 : ℝ) < 4 ^ k := by positivity
        nlinarith
      linarith
  -- the normalised coefficients, and the power as a sum over the blocks
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n => if n ∈ powSet S k then c n / (E : ℂ) else 0 := ⟨_, rfl⟩
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    rw [ha]
    by_cases hn : n ∈ powSet S k
    · simp only [hn, ite_true]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0, div_le_one hE0]
      exact hcE n
    · simp only [hn, ite_false, norm_zero]
      exact zero_le_one
  obtain ⟨blk, hblk⟩ : ∃ blk : DirichletCharacter ℂ q → ℕ → ℂ, blk = fun χ i =>
      ∑ n ∈ Finset.Ioc (M * 2 ^ i) (M * 2 ^ (i + 1)), a n * χ n := ⟨_, rfl⟩
  have hpow : ∀ χ : DirichletCharacter ℂ q,
      SieveWeight.Sp χ f0 Q y ^ k = (E : ℂ) * ∑ i ∈ Finset.range J, blk χ i := by
    intro χ
    have h1 : SieveWeight.Sp χ f0 Q y ^ k = ∑ n ∈ powSet S k, c n * χ n := by
      rw [Sp_eq_dp, ← hS, dp_pow_eq hS0, ← hc]
      unfold dp
      refine Finset.sum_congr rfl fun n _ => ?_
      simp
    have h2 : ∑ n ∈ powSet S k, c n * χ n = ∑ n ∈ powSet S k ∩ Finset.Ioc M (M * 2 ^ J), c n * χ n := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left fun n hn hnot => ?_
      have hnI : n ∉ Finset.Ioc M (M * 2 ^ J) := fun h => hnot (Finset.mem_inter.2 ⟨hn, h⟩)
      rw [hczero n hnI, zero_mul]
    have h3 : (E : ℂ) * ∑ n ∈ Finset.Ioc M (M * 2 ^ J), a n * χ n =
        ∑ n ∈ powSet S k ∩ Finset.Ioc M (M * 2 ^ J), c n * χ n := by
      rw [Finset.mul_sum, Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ha]
      by_cases hn : n ∈ powSet S k
      · simp only [hn, ite_true]
        have hEc : (E : ℂ) ≠ 0 := by exact_mod_cast hE0.ne'
        field_simp
      · simp only [hn, ite_false, zero_mul, mul_zero]
    rw [h1, h2, ← h3, sum_Ioc_dyadic, hblk]
  -- the characters at which a block is large
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Finset (DirichletCharacter ℂ q), R = fun i =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ q => V / (J * E) ≤ ‖blk χ i‖ := ⟨_, rfl⟩
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k) ⊆
      (Finset.range J).biUnion R := by
    intro χ hχ
    have hχV : V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k := (Finset.mem_filter.1 hχ).2
    rw [← norm_pow, hpow χ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0] at hχV
    have h1 : V / E ≤ ‖∑ i ∈ Finset.range J, blk χ i‖ := by
      rw [div_le_iff₀ hE0]; linarith
    obtain ⟨i, hi, hbi⟩ := exists_large_of_sum hJpos (blk χ) h1
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, ?_⟩
    rw [hR]
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have h2 : V / (J * E) = V / E / J := by field_simp
    rw [h2]; exact hbi
  -- Chen, Gupta and Li's count for each block
  have hblock : ∀ i < J, ((R i).card : ℝ) ≤
      C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) := by
    intro i hi
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M * 2 ^ i := ⟨_, rfl⟩
    have h2N : 2 * N = M * 2 ^ (i + 1) := by rw [hN, pow_succ]; ring
    have hNM : (M : ℝ) ≤ N := by
      rw [hN]; push_cast
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hNX : (N : ℝ) ≤ X := by
      have h1 : (2 : ℝ) ^ i ≤ 4 ^ k := by
        have h2 : i ≤ 2 * k := by omega
        calc (2 : ℝ) ^ i ≤ 2 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) h2
          _ = 4 ^ k := by rw [pow_mul]; norm_num
      rw [hN, hXY]; push_cast
      have h3 : (0 : ℝ) ≤ 2 ^ i := by positivity
      nlinarith
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hNM
    have hcount := hC q (R i) (fun _ => 0) 1 N (V / (J * E)) a le_rfl
      (by
        rw [mul_one]
        have h1 : (q : ℝ) ^ (2 / 3 : ℝ) ≤ Y - 1 := by
          have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
          linarith
        linarith)
      (by
        have h1 : (N : ℝ) ^ (7 / 10 : ℝ) ≤ X ^ (7 / 10 : ℝ) :=
          Real.rpow_le_rpow hN0.le hNX (by norm_num)
        rw [le_div_iff₀ hJE0]
        exact (mul_le_mul_of_nonneg_right h1 hJE0.le).trans hV1)
      (by
        have h1 : V / (J * E) ≤ V := div_le_self hV0.le hJE1
        have h2 : (Y / 2) ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (hMhalf.trans hNM) (by norm_num)
        linarith)
      ha1 (fun _ _ => by simp)
      (by
        intro χ hχ
        rw [hR] at hχ
        have hb : V / (J * E) ≤ ‖blk χ i‖ := (Finset.mem_filter.1 hχ).2
        rw [hblk] at hb
        rw [h2N, hN]
        refine hb.trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        simp)
    have hlv : LinnikCGLLV.p31B q 1 N (V / (J * E)) ≤ lvB q X (V / (J * E)) := by
      unfold LinnikCGLLV.p31B lvB
      rw [mul_one]
      have hq12 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hq0.le _
      have hq43 : (0 : ℝ) ≤ (q : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
      gcongr
    have hqN : ((q : ℝ) * 1 * N) ^ ε ≤ ((q : ℝ) * X) ^ ε := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hNX hq0.le) hε.le
    have hlv0 : 0 ≤ LinnikCGLLV.p31B q 1 N (V / (J * E)) := LinnikCGLLV.p31B_nonneg q zero_le_one N _
    calc ((R i).card : ℝ) ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * 1 * N) ^ ε * LinnikCGLLV.p31B q 1 N (V / (J * E)) :=
          hcount
      _ ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) := by
          have hCq : 0 ≤ C * (q : ℝ) ^ ε := mul_nonneg hC0 (Real.rpow_nonneg hq0.le _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hqN hCq) hlv hlv0
            (mul_nonneg hCq (Real.rpow_nonneg (by positivity) _))
  -- the union of the blocks' sets
  calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k).card : ℝ)
      ≤ (((Finset.range J).biUnion R).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range J, ((R i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range J, C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) :=
        Finset.sum_le_sum fun i hi => hblock i (Finset.mem_range.1 hi)
    _ = (2 * (k : ℝ) + 1) * (C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hJr]

/-! ### The count in exponents -/

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

/-- The conditions of `card_Sp_pow_large` at `Q^k = q^m` and `V = q^{mu}`, for `m ≥ 2/3 + 10⁻⁵`,
`7/10 + 10⁻⁵ ≤ u ≤ 4/5 − 10⁻⁵` and `4·2^k·D ≤ q^{10⁻⁵/2}`. -/
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

/-- **The characters at which a smoothed prime sum is large, by the large values of its powers, in exponents.**
Given Chen, Gupta and Li's Proposition 3.1 (`hP`), a bound `k_max` and `F₁ ≥ 1`, there are `C ≥ 1` and `q₀` such
that, for `q ≥ q₀`, `f0` with `|f0| ≤ F₁` and support in `[1/2, 2]`, `Q ≥ 4` and `1 ≤ k ≤ k_max`:
`#{χ : Q^u ≤ |Sp χ f0 Q y|} ≤ C q^{lvExp k s u}`, `s = log_q Q`. -/
theorem card_Sp_large_lv (hP : LinnikCGLLV.CGLProp31) (kmax : ℕ) {F₁ : ℝ} (hF1 : 1 ≤ F₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (f0 : ℝ → ℝ), (∀ u, |f0 u| ≤ F₁) →
      Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (Q y : ℝ) (k : ℕ) (u : ℝ), 1 ≤ k → k ≤ kmax → 4 ≤ Q →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖).card : ℝ) ≤
        C * (q : ℝ) ^ lvExp k (Real.logb q Q) u := by
  have hE0 : (0 : ℝ) < lvE := by unfold lvE; norm_num
  have hE1 : lvE = 1 / 10 ^ 5 := rfl
  obtain ⟨C₀, hC₀0, hC₀⟩ := card_Sp_pow_large hP (ε := lvE / 5) (by positivity) (by rw [hE1]; norm_num)
  -- the constants
  obtain ⟨Dm, hDm⟩ : ∃ D : ℝ, D = (2 * (kmax : ℝ) + 1) * (kmax : ℝ) ^ kmax * F₁ ^ kmax := ⟨_, rfl⟩
  have hDk : ∀ k : ℕ, 1 ≤ k → k ≤ kmax →
      1 ≤ (2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k ∧ (2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k ≤ Dm := by
    intro k hk1 hk2
    have hkk : (k : ℝ) ≤ kmax := by exact_mod_cast hk2
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ k := one_le_pow₀ hk1'
    have h2 : (1 : ℝ) ≤ F₁ ^ k := one_le_pow₀ hF1
    have h3 : (k : ℝ) ^ k ≤ (kmax : ℝ) ^ kmax :=
      (pow_le_pow_left₀ (by positivity) hkk k).trans (pow_le_pow_right₀ (by linarith) hk2)
    have h4 : F₁ ^ k ≤ F₁ ^ kmax := pow_le_pow_right₀ hF1 hk2
    constructor
    · have h5 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k :=
            mul_le_mul (mul_le_mul h5 h1 zero_le_one (by linarith)) h2 zero_le_one (by positivity)
    · rw [hDm]
      exact mul_le_mul (mul_le_mul (by linarith) h3 (by positivity) (by positivity)) h4 (by positivity)
        (by positivity)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 ((2 * (kmax : ℝ) + 1) * (C₀ * 2 ^ kmax * (3 * (Dm ^ 4 * 8 ^ kmax)))) :=
    ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hev : ∀ᶠ q : ℕ in Filter.atTop, 4 * 2 ^ kmax * Dm ≤ (q : ℝ) ^ (lvE / 2) ∧ 2 ≤ q :=
    ((((tendsto_rpow_atTop (by positivity : 0 < lvE / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * 2 ^ kmax * Dm))).and (Filter.eventually_ge_atTop 2)
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨C, hC1, q₀, fun q _ hq f0 hF₀ hsupp Q y k u hk hkm hQ => ?_⟩
  obtain ⟨hqB, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ0 : 0 < Q := by linarith
  -- the trivial count
  have htriv : ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖).card : ℝ) ≤
      C * (q : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have h1 := LinnikDensity.card_chars_le
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖)
    have h2 : 1 * (q : ℝ) ≤ C * q := mul_le_mul_of_nonneg_right hC1 hq0.le
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.logb q Q := ⟨_, rfl⟩
  rw [← hs]
  have hQs : Q = (q : ℝ) ^ s := by rw [hs, Real.rpow_logb hq0 hq1.ne' hQ0]
  by_cases hc : 2 / 3 + lvE ≤ (k : ℝ) * s ∧ 7 / 10 + lvE ≤ u
  swap
  · have h1 : lvExp k s u = 1 := by unfold lvExp; exact ite_eq_right hc
    rw [h1]; exact htriv
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ, u' = min u (4 / 5 - lvE) := ⟨_, rfl⟩
  have hlvE : lvExp k s u = min 1 (lvRaw k s u' + lvE) := by unfold lvExp; rw [ite_eq_left hc, hu']
  rw [hlvE]
  by_cases h1 : 1 ≤ lvRaw k s u' + lvE
  · rw [min_eq_left h1]; exact htriv
  rw [min_eq_right (not_le.1 h1).le]
  have hlt : lvRaw k s u' + lvE < 1 := not_le.1 h1
  have hu'1 : u' ≤ 4 / 5 - lvE := hu' ▸ min_le_right _ _
  have hu'u : u' ≤ u := hu' ▸ min_le_left _ _
  have hu'0 : 7 / 10 + lvE ≤ u' := by
    rw [hu']; exact le_min hc.2 (by rw [hE1]; norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (k : ℝ) * s := ⟨_, rfl⟩
  have hm23 : 2 / 3 + lvE ≤ m := hm ▸ hc.1
  have hraw : lvRaw k s u' = max (2 * m * (1 - u')) (max (1 / 2 + m * (3 - 4 * u')) (4 / 3 + m * (2 - 4 * u'))) := by
    unfold lvRaw; rw [hm]
  have hr1 : 2 * m * (1 - u') ≤ lvRaw k s u' := by rw [hraw]; exact le_max_left _ _
  have hr2 : 1 / 2 + m * (3 - 4 * u') ≤ lvRaw k s u' := by
    rw [hraw]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hr3 : 4 / 3 + m * (2 - 4 * u') ≤ lvRaw k s u' := by
    rw [hraw]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hm52 : m ≤ 5 / 2 := by nlinarith
  have hQk : Q ^ k = (q : ℝ) ^ m := by
    rw [hQs, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, hm, mul_comm]
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (q : ℝ) ^ (m * u') := ⟨_, rfl⟩
  have hVQ : V = (Q ^ u') ^ k := by
    rw [hV, hQs, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, hm]
    congr 1; ring
  obtain ⟨hD1, hDle⟩ := hDk k hk hkm
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (2 * (k : ℝ) + 1) * (k : ℝ) ^ k * F₁ ^ k := ⟨_, rfl⟩
  rw [← hD] at hD1 hDle
  have hD0 : 0 < D := by linarith
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ kmax := pow_le_pow_right₀ (by norm_num) hkm
  have h8k : (8 : ℝ) ^ k ≤ 8 ^ kmax := pow_le_pow_right₀ (by norm_num) hkm
  have hBk : 4 * 2 ^ k * D ≤ (q : ℝ) ^ (lvE / 2) := by
    have h5 : (4 : ℝ) * 2 ^ k * D ≤ 4 * 2 ^ kmax * Dm :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2k (by norm_num)) hDle hD0.le (by positivity)
    linarith
  obtain ⟨hc1, hc2, hc3⟩ := lv_conds hq1 hQk hm23 hu'0 hu'1 hD1 hBk
  rw [← hV] at hc2 hc3
  -- the count for the power
  have hcount := hC₀ q f0 F₁ hF1 hF₀ hsupp Q y k V hk hQ hc1 (by rw [← hD]; exact hc2) hc3
  rw [← hD] at hcount
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖) ⊆
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k) := by
    intro χ hχ
    have h1 : Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖ := (Finset.mem_filter.1 hχ).2
    have h2 : Q ^ u' ≤ Q ^ u := Real.rpow_le_rpow_of_exponent_le (by linarith) hu'u
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hVQ]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hQ0.le _) (h2.trans h1) k
  have hfac := lv_fac hq1 hQk hm52
  have hlvB := lvB_le (u := u') hq1 hQk hD1 hr1 hr2 hr3
  rw [← hV] at hlvB
  have hlvB0 : 0 ≤ lvB q ((2 * Q) ^ k) (V / D) := lvB_nonneg q (by positivity) _
  have hkk : 2 * (k : ℝ) + 1 ≤ 2 * (kmax : ℝ) + 1 := by
    have : (k : ℝ) ≤ kmax := by exact_mod_cast hkm
    linarith
  have hqR : (q : ℝ) ^ lvE * (q : ℝ) ^ lvRaw k s u' = (q : ℝ) ^ (lvRaw k s u' + lvE) := by
    rw [← Real.rpow_add hq0, add_comm]
  have hqE0 : 0 ≤ (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q) ^ k) ^ (lvE / 5) :=
    mul_nonneg (Real.rpow_nonneg hq0.le _) (Real.rpow_nonneg (by positivity) _)
  have hfac' : (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q) ^ k) ^ (lvE / 5) ≤ 2 ^ kmax * (q : ℝ) ^ lvE :=
    hfac.trans (mul_le_mul_of_nonneg_right h2k (Real.rpow_nonneg hq0.le _))
  have hlvB' : lvB q ((2 * Q) ^ k) (V / D) ≤ 3 * (Dm ^ 4 * 8 ^ kmax) * (q : ℝ) ^ lvRaw k s u' := by
    refine hlvB.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq0.le _))
    have hD4 : D ^ 4 ≤ Dm ^ 4 := pow_le_pow_left₀ hD0.le hDle 4
    have h6 : D ^ 4 * 8 ^ k ≤ Dm ^ 4 * 8 ^ kmax := mul_le_mul hD4 h8k (by positivity) (by positivity)
    linarith
  calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖).card : ℝ)
      ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖SieveWeight.Sp χ f0 Q y‖ ^ k).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (2 * (k : ℝ) + 1) * (C₀ * (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q) ^ k) ^ (lvE / 5) *
          lvB q ((2 * Q) ^ k) (V / D)) := hcount
    _ = (2 * (k : ℝ) + 1) * (C₀ * ((q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q) ^ k) ^ (lvE / 5)) *
          lvB q ((2 * Q) ^ k) (V / D)) := by ring
    _ ≤ (2 * (kmax : ℝ) + 1) * (C₀ * (2 ^ kmax * (q : ℝ) ^ lvE) *
          (3 * (Dm ^ 4 * 8 ^ kmax) * (q : ℝ) ^ lvRaw k s u')) := by
        refine mul_le_mul hkk ?_ (mul_nonneg (mul_nonneg hC₀0 hqE0) hlvB0) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hfac' hC₀0) hlvB' hlvB0
          (mul_nonneg hC₀0 (by positivity))
    _ = (2 * (kmax : ℝ) + 1) * (C₀ * 2 ^ kmax * (3 * (Dm ^ 4 * 8 ^ kmax))) *
          ((q : ℝ) ^ lvE * (q : ℝ) ^ lvRaw k s u') := by ring
    _ ≤ C * (q : ℝ) ^ (lvRaw k s u' + lvE) := by
        rw [hqR]
        exact mul_le_mul_of_nonneg_right (hC ▸ le_max_right _ _) (Real.rpow_nonneg hq0.le _)

end SieveTypeIIHM

#print axioms SieveTypeIIHM.card_Sp_pow_large
#print axioms SieveTypeIIHM.card_Sp_large_lv
