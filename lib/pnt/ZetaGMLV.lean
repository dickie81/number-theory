/-
# Guth–Maynard's large values estimate at `1`-separated points

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Guth and Maynard's Theorem 1.1: "Suppose (b_n) is a sequence of complex numbers with |b_n| ≤ 1, and (t_r)_{r≤R} is a
sequence of 1-separated points in [0,T] such that |Σ_{n=N}^{2N} b_n n^{it_r}| ≥ V for all r ≤ R. Then we have
R ≤ T^{o(1)}(N²V^{−2} + N^{18/5}V^{−4} + TN^{12/5}V^{−4})." Their proof from their Proposition 3.1 (the key
proposition) divides the points into `⌈T/N^{6/5}⌉` intervals of length `N^{6/5}` and chooses a `T^η`-separated subset
of each. This file does the same with `ZetaGMProp.GMProp31` (`gm_large_values`), for `V = N^σ/6`, `7/10 ≤ σ ≤ 4/5`, and
coefficients supported in `[6N/5, 9N/5]`, the form their key proposition takes after their splitting of `(N, 2N]`.
* The intervals: a point `x` lies in the interval of index `⌊(x + T)/T′⌋`, `T′ = N^{6/5}`, whose centre `a` gives
  `D(x) = D′(x − a)` with the coefficients `c_n n^{−ia}` (`dp_shift`), of modulus `|c_n|`.
* The classes: `1`-separated points with one value of `⌊x + T⌋` mod `M = ⌈T′^{ε′}⌉ + 1` are more than `M − 1 ≥ T′^{ε′}`
  apart (`sep_of_mod`).
* Each interval and class is `GMProp31` at height `T′`, where `T′^{1/2}N^{3−4σ} = T′^{4/3}N^{2−4σ} = N^{18/5−4σ}`.
  There are at most `2T/T′ + 1` intervals and `3T′^{ε′}` classes, and `(T′N)^{ε′}T′^{ε′} = N^{17ε′/5}`.

Plain statements, with `D(x) = Σ_{n∈S}c_nn^{−ix}` (`DirMean.dp`).
* `one_apply_one`, `dp_eq_sum`: the character mod `1` is `1`; and `D(x) = Σ_nc_n·1·n^{i(−x)}`, the form of `GMProp31`.
* `dp_shift`: `D(x) = D′(x − a)` with `c′_n = c_ne^{−ia log n}`.
* `sep_of_mod`: for `x, x′` at least `1` apart with `⌊x + T⌋ ≡ ⌊x′ + T⌋` mod `M`, `M − 1 < |x − x′|`.
* `gm_prop31_one`: `GMProp31`, from `LinnikCGLP81.cglp81` and `LinnikCGLHB101.cglt101`.
* `gm_large_values`: for every `ε > 0` there is `C ≥ 0` such that, for `T ≥ 0`, `N ≥ 1`, `7/10 ≤ σ ≤ 4/5`,
  `S ⊆ [6N/5, 9N/5]`, `|c_n| ≤ 1` and `1`-separated points `|x_r| ≤ T` with `|D(x_r)| ≥ N^σ/6`,
  `|R| ≤ CN^ε(TN^{12/5−4σ} + N^{18/5−4σ})`.

The file imports `ZetaGMProp.lean`.
-/
import ZetaGMProp

open Complex Real Finset

noncomputable section

namespace ZetaGMLV

open DirMean ZetaGMProp ZetaGMS3

/-- The character mod `1` is `1` at every `n`. -/
lemma one_apply_one (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

/-- `D(x) = Σ_nc_n·1·n^{i(−x)}`, the form of `GMProp31`, for `S` of positive integers. -/
lemma dp_eq_sum (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ) (x : ℝ) :
    dp S c x = ∑ n ∈ S, c n * (1 : DirichletCharacter ℂ 1) n * (n : ℂ) ^ (((-x : ℝ) : ℂ) * I) := by
  unfold dp
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [one_apply_one, mul_one, LinnikCGLMat.natCast_cpow_I (hS n hn), neg_neg]

/-- **A shift of the points**: `D(x) = D′(x − a)` with `c′_n = c_ne^{−ia log n}`. -/
lemma dp_shift (S : Finset ℕ) (c : ℕ → ℂ) (x a : ℝ) :
    dp S c x = dp S (fun n => c n * Complex.exp (-(I * ((a * Real.log n : ℝ) : ℂ)))) (x - a) := by
  unfold dp
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The classes are separated**: for `x, x′ ≥ −T` at least `1` apart with `⌊x + T⌋ ≡ ⌊x′ + T⌋` mod `M`,
`M − 1 < |x − x′|`. -/
lemma sep_of_mod {x x' T : ℝ} {M : ℕ} (hx : 0 ≤ x + T) (hx' : 0 ≤ x' + T) (h1 : 1 ≤ |x - x'|)
    (hmod : ⌊x + T⌋₊ % M = ⌊x' + T⌋₊ % M) : (M : ℝ) - 1 < |x - x'| := by
  have hne : ⌊x + T⌋₊ ≠ ⌊x' + T⌋₊ := by
    intro h
    have a1 := Nat.floor_le hx
    have a2 := Nat.lt_floor_add_one (x + T)
    have b1 := Nat.floor_le hx'
    have b2 := Nat.lt_floor_add_one (x' + T)
    rw [h] at a1 a2
    have : |x - x'| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have hM : M ≤ (⌊x + T⌋₊ : ℤ) - ⌊x' + T⌋₊ ∨ M ≤ (⌊x' + T⌋₊ : ℤ) - ⌊x + T⌋₊ := by
    have hz : ((⌊x + T⌋₊ : ℤ) - ⌊x' + T⌋₊) % M = 0 := by
      rw [Int.sub_emod, ← Int.natCast_mod, ← Int.natCast_mod, hmod, sub_self, Int.zero_emod]
    have hdvd : (M : ℤ) ∣ (⌊x + T⌋₊ : ℤ) - ⌊x' + T⌋₊ := Int.dvd_of_emod_eq_zero hz
    have hne' : (⌊x + T⌋₊ : ℤ) - ⌊x' + T⌋₊ ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
    rcases le_or_gt 0 ((⌊x + T⌋₊ : ℤ) - ⌊x' + T⌋₊) with h | h
    · left
      exact Int.le_of_dvd (lt_of_le_of_ne h (Ne.symm hne')) hdvd
    · right
      have h' : 0 < (⌊x' + T⌋₊ : ℤ) - ⌊x + T⌋₊ := by linarith
      exact Int.le_of_dvd h' (by rw [← neg_sub]; exact (dvd_neg).2 hdvd)
  have a1 := Nat.floor_le hx
  have a2 := Nat.lt_floor_add_one (x + T)
  have b1 := Nat.floor_le hx'
  have b2 := Nat.lt_floor_add_one (x' + T)
  rcases hM with h | h
  · have h' : (M : ℝ) ≤ (⌊x + T⌋₊ : ℝ) - ⌊x' + T⌋₊ := by exact_mod_cast h
    have : (M : ℝ) - 1 < x - x' := by linarith
    exact this.trans_le (le_abs_self _)
  · have h' : (M : ℝ) ≤ (⌊x' + T⌋₊ : ℝ) - ⌊x + T⌋₊ := by exact_mod_cast h
    have : (M : ℝ) - 1 < x' - x := by linarith
    rw [abs_sub_comm]
    exact this.trans_le (le_abs_self _)

/-- **Guth and Maynard's key proposition at `q = 1`**, with no hypothesis: `ZetaGMProp.gm_prop31_pt` with
`LinnikCGLP81.cglp81` and `LinnikCGLHB101.cglt101`. -/
theorem gm_prop31_one : GMProp31 := gm_prop31_pt LinnikCGLP81.cglp81 LinnikCGLHB101.cglt101

/-- **Guth and Maynard's large values estimate** at `1`-separated points, from their key proposition
(`gm_prop31_one`): for every `ε > 0` there is `C ≥ 0` such that, for `T ≥ 0`, `N ≥ 1`, `7/10 ≤ σ ≤ 4/5`,
`S ⊆ [6N/5, 9N/5]`, `|c_n| ≤ 1` and points `|x_r| ≤ T` at least `1` apart with `|Σ_{n∈S}c_nn^{−ix_r}| ≥ N^σ/6`,
`|R| ≤ CN^ε(TN^{12/5−4σ} + N^{18/5−4σ})`. -/
theorem gm_large_values {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (R : Finset ι) (x : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (c : ℕ → ℂ),
      0 ≤ T → 1 ≤ N → 7 / 10 ≤ σ → σ ≤ 4 / 5 → (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) →
      (∀ n, ‖c n‖ ≤ 1) → (∀ r ∈ R, |x r| ≤ T) → (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |x r - x r'|) →
      (∀ r ∈ R, N ^ σ / 6 ≤ ‖dp S c (x r)‖) →
      (R.card : ℝ) ≤ C * N ^ ε * (T * N ^ (12 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := by
  obtain ⟨C, hC0, hC⟩ := gm_prop31_one (ε / 4) (by positivity)
  refine ⟨18 * C, by positivity, ?_⟩
  intro ι R x T N σ S c hT hN hσ1 hσ2 hS hc hx hsep hbig
  classical
  have hN0 : 0 < N := by linarith
  -- the height `T′ = N^{6/5}`, the intervals and the classes
  set T' := N ^ (6 / 5 : ℝ) with hT'
  have hT'1 : 1 ≤ T' := Real.one_le_rpow hN (by norm_num)
  have hT'0 : 0 < T' := by linarith
  set e := ε / 4 with he
  have he0 : 0 < e := by positivity
  set K := ⌊2 * T / T'⌋₊ + 1 with hK
  set M := ⌈T' ^ e⌉₊ + 1 with hM
  have hTe1 : 1 ≤ T' ^ e := Real.one_le_rpow hT'1 he0.le
  have hM1 : 1 ≤ M := by omega
  have hMe : ((M : ℕ) : ℝ) - 1 ≥ T' ^ e := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (T' ^ e)]
  have hMle : (M : ℝ) ≤ 3 * T' ^ e := by
    rw [hM]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ T' ^ e by positivity)
    linarith
  set kidx : ι → ℕ := fun r => ⌊(x r + T) / T'⌋₊ with hkidx
  set jidx : ι → ℕ := fun r => ⌊x r + T⌋₊ % M with hjidx
  set Rkj : ℕ → ℕ → Finset ι := fun k j => R.filter fun r => kidx r = k ∧ jidx r = j with hRkj
  have hcover : R ⊆ (range K).biUnion fun k => (range M).biUnion fun j => Rkj k j := by
    intro r hr
    have hxr := abs_le.1 (hx r hr)
    have hk : kidx r < K := by
      rw [hK]
      refine Nat.lt_succ_of_le (Nat.floor_mono ?_)
      exact div_le_div_of_nonneg_right (by linarith) hT'0.le
    have hj : jidx r < M := Nat.mod_lt _ (by omega)
    exact mem_biUnion.2 ⟨kidx r, mem_range.2 hk, mem_biUnion.2 ⟨jidx r, mem_range.2 hj,
      mem_filter.2 ⟨hr, rfl, rfl⟩⟩⟩
  -- one interval and one class
  set W := 3 * C * N ^ (11 / 5 * e) * N ^ (18 / 5 - 4 * σ) with hW
  have hpiece : ∀ k ∈ range K, ∀ j ∈ range M, ((Rkj k j).card : ℝ) ≤ W := by
    intro k _ j _
    set a := -T + k * T' + T' / 2 with ha
    set c' : ℕ → ℂ := fun n => c n * Complex.exp (-(I * ((a * Real.log n : ℝ) : ℂ))) with hc'
    have hc'1 : ∀ n, ‖c' n‖ ≤ 1 := fun n => by
      rw [hc', norm_mul, norm_exp_neg_I_mul, mul_one]; exact hc n
    have hSpos : ∀ n ∈ S, 0 < n := fun n hn => by
      have := (hS n hn).1
      exact_mod_cast (show (0 : ℝ) < n by nlinarith)
    -- the points of the interval, centred
    have hloc : ∀ r ∈ Rkj k j, |a - x r| ≤ T' := by
      intro r hr
      obtain ⟨hrR, hkr, -⟩ := mem_filter.1 hr
      have hxr := abs_le.1 (hx r hrR)
      have h0 : 0 ≤ (x r + T) / T' := div_nonneg (by linarith) hT'0.le
      have a1 := Nat.floor_le h0
      have a2 := Nat.lt_floor_add_one ((x r + T) / T')
      have hkr' : (⌊(x r + T) / T'⌋₊ : ℝ) = k := by exact_mod_cast hkr
      rw [hkr'] at a1 a2
      rw [le_div_iff₀ hT'0] at a1
      rw [div_lt_iff₀ hT'0] at a2
      rw [abs_le, ha]
      constructor <;> nlinarith
    have hsepkj : ∀ r ∈ Rkj k j, ∀ r' ∈ Rkj k j, r ≠ r' → T' ^ e ≤ |(a - x r) - (a - x r')| := by
      intro r hr r' hr' hne
      obtain ⟨hrR, -, hjr⟩ := mem_filter.1 hr
      obtain ⟨hrR', -, hjr'⟩ := mem_filter.1 hr'
      have h1 := hsep r hrR r' hrR' hne
      have hxr := abs_le.1 (hx r hrR)
      have hxr' := abs_le.1 (hx r' hrR')
      have hmod : ⌊x r + T⌋₊ % M = ⌊x r' + T⌋₊ % M := by
        have := hjr.trans hjr'.symm
        exact this
      have h2 := sep_of_mod (M := M) (by linarith) (by linarith) h1 hmod
      rw [show (a - x r) - (a - x r') = -(x r - x r') by ring, abs_neg]
      linarith
    have hbigkj : ∀ r ∈ Rkj k j, N ^ σ / 6 ≤
        ‖∑ n ∈ S, c' n * (1 : DirichletCharacter ℂ 1) n * (n : ℂ) ^ (((a - x r : ℝ) : ℂ) * I)‖ := by
      intro r hr
      have h := hbig r (mem_filter.1 hr).1
      rw [dp_shift S c (x r) a, dp_eq_sum S hSpos] at h
      rwa [show -(x r - a) = a - x r by ring] at h
    have hGr := hC (Rkj k j) (fun _ => 1) (fun r => a - x r) T' N σ S c' hsepkj hT'1 hσ1 hσ2
      (by
        rw [hT', ← Real.rpow_mul hN0.le]
        have : N ^ (6 / 5 * (2 / 3) : ℝ) ≤ N := by
          calc N ^ (6 / 5 * (2 / 3) : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
            _ = N := Real.rpow_one N
        linarith)
      hS hc'1 hloc hbigkj
    -- the bound at height `T′ = N^{6/5}`
    have e1 : T' ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) = N ^ (18 / 5 - 4 * σ) := by
      rw [hT', ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; norm_num; ring_nf
    have e2 : T' ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) = N ^ (18 / 5 - 4 * σ) := by
      rw [hT', ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; norm_num; ring_nf
    have e3 : N ^ (2 - 2 * σ) ≤ N ^ (18 / 5 - 4 * σ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have e4 : (T' * N) ^ (ε / 4) = N ^ (11 / 5 * e) := by
      rw [hT', ← Real.rpow_add_one hN0.ne', ← Real.rpow_mul hN0.le, he]
      congr 1
      ring
    rw [e1, e2, e4] at hGr
    calc ((Rkj k j).card : ℝ) ≤ C * N ^ (11 / 5 * e) *
          (N ^ (2 - 2 * σ) + N ^ (18 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := hGr
      _ ≤ C * N ^ (11 / 5 * e) * (3 * N ^ (18 / 5 - 4 * σ)) := by gcongr; linarith
      _ = W := by rw [hW]; ring
  -- the sum over the intervals and classes
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hcount : (R.card : ℝ) ≤ K * (M * W) := by
    calc (R.card : ℝ) ≤ (((range K).biUnion fun k => (range M).biUnion fun j => Rkj k j).card : ℝ) := by
          exact_mod_cast card_le_card hcover
      _ ≤ ∑ k ∈ range K, (((range M).biUnion fun j => Rkj k j).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ k ∈ range K, ∑ j ∈ range M, ((Rkj k j).card : ℝ) := by
          gcongr with k
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ k ∈ range K, ∑ j ∈ range M, W :=
          sum_le_sum fun k hk => sum_le_sum fun j hj => hpiece k hk j hj
      _ = K * (M * W) := by simp
  have hK' : (K : ℝ) ≤ 2 * T / T' + 1 := by
    rw [hK]; push_cast
    have := Nat.floor_le (show 0 ≤ 2 * T / T' by positivity)
    linarith
  -- the powers of `N`
  have hNe : T' ^ e * N ^ (11 / 5 * e) ≤ N ^ ε := by
    rw [hT', ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by rw [he]; linarith)
  have hTT : 2 * T / T' * N ^ (18 / 5 - 4 * σ) = 2 * T * N ^ (12 / 5 - 4 * σ) := by
    have : N ^ (18 / 5 - 4 * σ) = T' * N ^ (12 / 5 - 4 * σ) := by
      rw [hT', ← Real.rpow_add hN0]; ring_nf
    rw [this]; field_simp
  calc (R.card : ℝ) ≤ K * (M * W) := hcount
    _ ≤ (2 * T / T' + 1) * (3 * T' ^ e * W) :=
        mul_le_mul hK' (mul_le_mul_of_nonneg_right hMle hW0) (by positivity) (by positivity)
    _ = 9 * C * (T' ^ e * N ^ (11 / 5 * e)) * (2 * T / T' * N ^ (18 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := by
        rw [hW]; ring
    _ ≤ 9 * C * N ^ ε * (2 * T / T' * N ^ (18 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := by gcongr
    _ = 9 * C * N ^ ε * (2 * T * N ^ (12 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := by rw [hTT]
    _ ≤ 18 * C * N ^ ε * (T * N ^ (12 / 5 - 4 * σ) + N ^ (18 / 5 - 4 * σ)) := by
        have h0 : 0 ≤ 9 * C * N ^ ε := by positivity
        have h1 : 0 ≤ T * N ^ (12 / 5 - 4 * σ) := by positivity
        have h2 : 0 ≤ N ^ (18 / 5 - 4 * σ) := by positivity
        nlinarith

end ZetaGMLV

#print axioms ZetaGMLV.dp_eq_sum
#print axioms ZetaGMLV.dp_shift
#print axioms ZetaGMLV.sep_of_mod
#print axioms ZetaGMLV.gm_prop31_one
#print axioms ZetaGMLV.gm_large_values
