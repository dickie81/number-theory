/-
# The Type II estimate of the sieve route at small heights (Proposition 3′, pointwise in the heights)

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`typeII_step`). Let `L = 2333/1000`, `f0` smooth and real with support in `[1/2, 2]`, `K₀ ≥ 0`,
`e₁ > 0` and `0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with `q^{(401/1000)L} ≤ P ≤ q^{(485/1000)L}`, every
`S ⊆ (P, 2P]`, `a_m` and `h₀`, every `K ≤ K₀`, and every `Q_j ≥ q^{e₁}` and `|h_j| ≤ q^η` (`j < K`) with
`∏_j Q_j ≤ 2^{K₀}q^L/P`:
`Σ_{χ≠1} |Σ_{m∈S} a_mχ(m)m^{−ih₀}||∏_{j<K} Σ_{p≤2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)|` is at most
`q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`.

This is Proposition 3′ for the curve step, on the window
`[401/1000, 485/1000]` inside the step's proved window, pointwise in the heights. The bins of the characters do not
depend on the heights. In each bin Lemma 1 (`SieveWeight.norm_Sp_le`) bounds the prime sums, (H2′) counts the characters
(`LinnikTwelve.charDensity_twelve_fifths`, `LinnikStep.charDensity_step`, and at most `q` characters), and
Cauchy–Schwarz with orthogonality (T1) bounds the sum.

* `card_class_le`, `sum_chars_dp_sq_le`: (T1), `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (P + q)Σ_{j∈S} |c_j|²` for
  `S ⊆ (P, 2P]` (`LinnikHybrid.sum_chars_norm_sq_le` with `dp_twist_eq`, and Cauchy–Schwarz in each class).
* `sum_bins_le`: if `|B(a)| ≤ M_i` on the bin `i` of a partition of `s`, then
  `Σ_{a∈s} |W(a)||B(a)| ≤ Σ_i M_i(#bin i)^{1/2}(Σ_{a∈s} |W(a)|²)^{1/2}`.
* `bin`, `bin_rect`, `card_bin_le`, `sum_typeII_bins`: the bin of `χ` is the largest `i` with a zero in
  `Re s > β_i`, `|Im s| ≤ T`; above it lies the zero-free rectangle of Lemma 1, and in it a zero counted by (H2′).
* `typeII_pointwise`: the bound by bins, with Lemma 1 and (T1).
* `card_zero_step`: the counts of the curve step, `C(qT)^{g(σ)}(1 + log qT)^{10}`.
* `MB_le`: for all large `q`, Lemma 1's bound is at most `2Q^{θ+2δ}`.
* `exponent_le`: the exponents on the window, at most `L − 1/25000`. Before the width they lie at least `5.5·10⁻⁵`
  below `L` and `1.5·10⁻⁵` below `L − 1/25000`, least at `β = 11/12`.
* `qpow_combine`, `bin_bound`, `prod_MB_le`, `card_bin_step`: one bin.
* `typeII_step`: the sum over the 500000 bins of width `1/1200000`.
-/
import LinnikStep
import SieveWeight

open Complex Finset

noncomputable section

namespace SieveTypeII

open DirMean LinnikHybrid DirichletCharacter

/-! ### Orthogonality (T1) -/

/-- **A residue class in `(P, 2P]`**: at most `P/q + 1` elements. The map `j ↦ ⌊(j − P − 1)/q⌋` is injective on
the class and takes values in `[0, P/q]`. -/
lemma card_class_le {P q : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ZMod q) :
    ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ P / q + 1 := by
  have hmaps : Set.MapsTo (fun j => (j - (P + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a)
      (Finset.range (P / q + 1)) := by
    intro j hj
    have hjS := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hjS)
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun j => (j - (P + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a) := by
    intro j hj j' hj' hjj'
    have hj1 := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
    have hj1' := Finset.mem_filter.1 (Finset.mem_coe.1 hj')
    have hlo := (Finset.mem_Ioc.1 (hS hj1.1)).1
    have hlo' := (Finset.mem_Ioc.1 (hS hj1'.1)).1
    have hmod : j % q = j' % q := by
      have h : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q) := hj1.2.trans hj1'.2.symm
      exact (ZMod.natCast_eq_natCast_iff' j j' q).1 h
    have hmod' : (j - (P + 1)) % q = (j' - (P + 1)) % q := by
      have e1 : j = (j - (P + 1)) + (P + 1) := by omega
      have e2 : j' = (j' - (P + 1)) + (P + 1) := by omega
      have h : (j - (P + 1)) + (P + 1) ≡ (j' - (P + 1)) + (P + 1) [MOD q] := by
        rw [← e1, ← e2]; exact hmod
      exact Nat.ModEq.add_right_cancel' (P + 1) h
    have hdiv : (j - (P + 1)) / q = (j' - (P + 1)) / q := hjj'
    have e : j - (P + 1) = j' - (P + 1) := by
      rw [← Nat.div_add_mod (j - (P + 1)) q, ← Nat.div_add_mod (j' - (P + 1)) q, hdiv, hmod']
    omega
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hc
  calc ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ ((P / q + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ((P / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ P / q + 1 := by gcongr; exact Nat.cast_div_le

/-- **Orthogonality (T1)**: `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (P + q)Σ_{j∈S} |c_j|²` for `S ⊆ (P, 2P]`. The sum
over `χ` is at most `φ(q)Σ_a |D_a|²` over the classes `a` mod `q` (`sum_chars_norm_sq_le`, `dp_twist_eq`), and
`|D_a|² ≤ (P/q + 1)Σ_{j≡a} |c_j|²` by Cauchy–Schwarz (`card_class_le`). -/
theorem sum_chars_dp_sq_le {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] (t : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤ (P + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set Sa : ZMod q → Finset ℕ := fun a => S.filter (fun j : ℕ => (j : ZMod q) = a) with hSa
  have h1 : ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤
      q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := by
    have e : ∀ χ : DirichletCharacter ℂ q, dp S (fun j => c j * χ j) t = ∑ a, χ a * dp (Sa a) c t :=
      fun χ => dp_twist_eq q S c χ t
    simp_rw [e]
    exact sum_chars_norm_sq_le q (fun a => dp (Sa a) c t)
  have h2 : ∀ a, ‖dp (Sa a) c t‖ ^ 2 ≤ (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
    intro a
    have hn : ‖dp (Sa a) c t‖ ≤ ∑ j ∈ Sa a, ‖c j‖ := by
      unfold dp
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul, norm_exp_neg_I_mul, mul_one]
    have hcs : (∑ j ∈ Sa a, ‖c j‖) ^ 2 ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    have hcard := card_class_le (q := q) hS a
    calc ‖dp (Sa a) c t‖ ^ 2 ≤ (∑ j ∈ Sa a, ‖c j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := hcs
      _ ≤ (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
          gcongr
  have hfib : ∑ a : ZMod q, ∑ j ∈ Sa a, ‖c j‖ ^ 2 = ∑ j ∈ S, ‖c j‖ ^ 2 :=
    Finset.sum_fiberwise S (fun j => (j : ZMod q)) fun j => ‖c j‖ ^ 2
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  calc ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := h1
    _ ≤ q.totient * ∑ a, (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
        gcongr with a; exact h2 a
    _ = q.totient * (P / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by rw [← Finset.mul_sum, hfib]; ring
    _ ≤ q * (P / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by gcongr
    _ = (P + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by field_simp

/-! ### The bins of characters -/

section Bins

open scoped Classical ContDiff

variable {q : ℕ} [NeZero q]

/-- **The bin of `χ`**: the largest `i < N` such that `i = 0` or `L(·, χ)` has a zero with `Re s > β i` and
`|Im s| ≤ T`. It depends on `T`, not on the heights of the prime sums. -/
noncomputable def bin (β : ℕ → ℝ) (N : ℕ) (T : ℝ) (χ : DirichletCharacter ℂ q) : ℕ :=
  ((Finset.range N).filter (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)).sup id

lemma mem_binSet {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} {i : ℕ} :
    i ∈ (Finset.range N).filter (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ↔
      i < N ∧ (i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
  rw [Finset.mem_filter, Finset.mem_range]

lemma bin_lt {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) (χ : DirichletCharacter ℂ q) : bin β N T χ < N := by
  unfold bin
  exact (Finset.sup_lt_iff (by simpa using hN)).2 fun i hi => (mem_binSet.1 hi).1

lemma le_bin {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} {i : ℕ} (hi : i < N)
    (hz : ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) : i ≤ bin β N T χ :=
  Finset.le_sup (f := id) (mem_binSet.2 ⟨hi, Or.inr hz⟩)

/-- Above its bin, `χ` has no zero: none with `Re s > β (bin + 1)` and `|Im s| ≤ T`. -/
lemma bin_zeroFree {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (h : bin β N T χ + 1 < N) :
    ∀ s : ℂ, β (bin β N T χ + 1) < s.re → |s.im| ≤ T → LFunction χ s ≠ 0 := by
  intro s hs hT h0
  have := le_bin h ⟨s, hs, hT, h0⟩
  omega

/-- In a bin `i > 0`, `χ` has a zero with `Re s > β i` and `|Im s| ≤ T`. -/
lemma bin_zero {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (hN : 0 < N) (h : 0 < bin β N T χ) :
    ∃ s : ℂ, β (bin β N T χ) < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  have hne : ((Finset.range N).filter
      (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)).Nonempty :=
    ⟨0, mem_binSet.2 ⟨hN, Or.inl rfl⟩⟩
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hb : bin β N T χ = i := by unfold bin; rw [hieq]; rfl
  rw [hb] at h ⊢
  rcases (mem_binSet.1 hi).2 with h0 | hz
  · omega
  · exact hz

/-- **The rectangle of Lemma 1.** If `β N = 11/12`, `χ ≠ 1` and `|y| + H + 1 ≤ T`, then `L(·, χ)` has no zero with
`Re s > β (bin + 1)` and `|Im s − y| < H + 1`: below `N` by `bin_zeroFree`, and at `N` by the zero-free half-plane
`Re s > 11/12` (`Eis.LFunction_ne_zero_of_re_gt`). -/
lemma bin_rect {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (hβN : β N = 11 / 12) (hχ : χ ≠ 1)
    (hN : 0 < N) {y H : ℝ} (hyT : |y| + H + 1 ≤ T) :
    ∀ s : ℂ, β (bin β N T χ + 1) < s.re → |s.im - y| < H + 1 → LFunction χ s ≠ 0 := by
  intro s hs him
  have hb := bin_lt (β := β) hN T χ
  rcases Nat.lt_or_ge (bin β N T χ + 1) N with h | h
  · refine bin_zeroFree h s hs ?_
    have h1 : |s.im| ≤ |s.im - y| + |y| := by
      have := abs_add_le (s.im - y) y
      rwa [sub_add_cancel] at this
    linarith
  · have e : bin β N T χ + 1 = N := by omega
    rw [e, hβN] at hs
    exact Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)

/-- **The count of a bin `i > 0`**: its characters have a zero with `Re s ≥ β i` and `|Im s| ≤ T`. -/
lemma card_bin_le {β : ℕ → ℝ} {N : ℕ} {T : ℝ} (hN : 0 < N) {i : ℕ} (hi : 0 < i) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card ≤
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, β i ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card := by
  refine Finset.card_le_card fun χ hχ => ?_
  have h := (Finset.mem_filter.1 hχ).2
  obtain ⟨s, hs, hT, h0⟩ := bin_zero (χ := χ) hN (h.2 ▸ hi)
  rw [h.2] at hs
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s, hs.le, hT, h0⟩

/-- The bound of `SieveWeight.norm_Sp_le` for one prime sum at scale `Q` and height `y`, with `θ`, `δ`, `H`, the
decay `Kd` and its constants `Bc`, `Cc`. -/
noncomputable def MB (q : ℕ) (Bc Cc : ℝ) (Kd : ℕ) (θ δ H Q y : ℝ) : ℝ :=
  (Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ)) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
      (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) / Real.log Q +
    Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1))

/-! ### Lemma 1's bound, eventually -/

/-- `log(q + 2) + log(|y| + 4) + 1 ≤ 4 + 2 log q` for `q ≥ 1`, `|y| ≤ q^η`, `0 < η ≤ 1`. -/
lemma logs_le {q : ℕ} {y η : ℝ} (hq : 1 ≤ (q : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1) (hy : |y| ≤ (q : ℝ) ^ η) :
    Real.log (q + 2) + Real.log (|y| + 4) + 1 ≤ 4 + 2 * Real.log q := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have h1 : Real.log (q + 2) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) hq0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hqη : 1 ≤ (q : ℝ) ^ η := Real.one_le_rpow hq hη.le
  have h2 : Real.log (|y| + 4) ≤ Real.log 5 + η * Real.log q := by
    rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h15 : Real.log 3 + Real.log 5 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]; nlinarith
  have hηl : η * Real.log q ≤ Real.log q := by nlinarith
  linarith

/-- `⌊√⌊2Q⌋⌋ + 1 ≤ 3√Q` for `Q ≥ 1`. -/
lemma sqrt_floor_le {Q : ℝ} (hQ : 1 ≤ Q) : (Nat.sqrt ⌊2 * Q⌋₊ : ℝ) + 1 ≤ 3 * Real.sqrt Q := by
  have hfl : (⌊2 * Q⌋₊ : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have h1 : (Nat.sqrt ⌊2 * Q⌋₊ : ℝ) ≤ Real.sqrt (⌊2 * Q⌋₊ : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt (⌊2 * Q⌋₊ : ℝ) ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt hfl
  have h3 : Real.sqrt (2 * Q) = Real.sqrt 2 * Real.sqrt Q := Real.sqrt_mul (by norm_num) Q
  have h4 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h5 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.2 hQ
  have h7 : Real.sqrt 2 * Real.sqrt Q ≤ 2 * Real.sqrt Q := mul_le_mul_of_nonneg_right h4 (by linarith)
  linarith

/-- `⌊log₂⌊2Q⌋⌋ + 1 ≤ 3(1 + log Q)` for `Q ≥ 1`. -/
lemma log_floor_le {Q : ℝ} (hQ : 1 ≤ Q) : (Nat.log 2 ⌊2 * Q⌋₊ : ℝ) + 1 ≤ 3 * (1 + Real.log Q) := by
  have hQ0 : 0 < Q := by linarith
  have hfl : (⌊2 * Q⌋₊ : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have hfl1 : (1 : ℝ) ≤ ⌊2 * Q⌋₊ := by exact_mod_cast Nat.le_floor (by push_cast; linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Nat.log 2 ⌊2 * Q⌋₊ : ℝ) ≤ Real.logb 2 (⌊2 * Q⌋₊ : ℝ) := by
    have h := Real.natLog_le_logb ⌊2 * Q⌋₊ 2
    simpa using h
  have h2 : Real.logb 2 (⌊2 * Q⌋₊ : ℝ) ≤ Real.logb 2 (2 * Q) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hfl
  have h3 : Real.logb 2 (2 * Q) = 1 + Real.log Q / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hQ0.ne', add_div, div_self hl2.ne']
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hl2' : 1 / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h4 : Real.log Q / Real.log 2 ≤ 2 * Real.log Q := by
    rw [div_le_iff₀ hl2]
    have : Real.log Q * (1 / 2) ≤ Real.log Q * Real.log 2 := mul_le_mul_of_nonneg_left hl2' hlQ
    linarith
  linarith

/-- The prime powers' term of `SieveWeight.norm_Sp_le`: at most `Q^{1/2+δ}` once `9C(1 + log Q) ≤ Q^δ`. -/
lemma primePow_term_le {Cc δ Q : ℝ} (hCc : 0 ≤ Cc) (hQ : 1 ≤ Q) (hev : 9 * Cc * (1 + Real.log Q) ≤ Q ^ δ) :
    Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1)) ≤ Q ^ (1 / 2 + δ) := by
  have hQ0 : 0 < Q := by linarith
  have hs := sqrt_floor_le hQ
  have hl := log_floor_le hQ
  have h0 : (0 : ℝ) ≤ Nat.log 2 ⌊2 * Q⌋₊ + 1 := by positivity
  have h0' : (0 : ℝ) ≤ Nat.sqrt ⌊2 * Q⌋₊ + 1 := by positivity
  calc Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1))
      ≤ Cc * (3 * Real.sqrt Q * (3 * (1 + Real.log Q))) := by
        apply mul_le_mul_of_nonneg_left _ hCc
        exact mul_le_mul hs hl h0 (by positivity)
    _ = 9 * Cc * (1 + Real.log Q) * Real.sqrt Q := by ring
    _ ≤ Q ^ δ * Q ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_right hev (by positivity)
    _ = Q ^ (1 / 2 + δ) := by rw [← Real.rpow_add hQ0]; ring_nf

/-- **Lemma 1's bound, eventually.** Let `η·Kd ≥ 5U/12`. For all large `q`, every `θ ∈ [1/2, 11/12]` with
`KL(θ, θ + δ) ≤ KLmax`, every scale `q^{e₁} ≤ Q ≤ q^U` and every height `|y| ≤ q^η`, the bound of
`SieveWeight.norm_Sp_le` with `H = q^η` is at most `2Q^{θ+2δ}`. -/
lemma MB_le {Bc Cc KLmax δ e₁ η U : ℝ} {Kd : ℕ} (hBc : 0 ≤ Bc) (hCc : 0 ≤ Cc) (hKL : 0 ≤ KLmax) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 24) (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1) (hKd : 5 * U / 12 ≤ η * Kd) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ θ Q y : ℝ, 1 / 2 ≤ θ → θ ≤ 11 / 12 → Linnik.KL θ (θ + δ) ≤ KLmax →
      (q : ℝ) ^ e₁ ≤ Q → Q ≤ (q : ℝ) ^ U → |y| ≤ (q : ℝ) ^ η →
      MB q Bc Cc Kd θ δ ((q : ℝ) ^ η) Q y ≤ 2 * Q ^ (θ + 2 * δ) := by
  set KLg := Linnik.KL (11 / 12) (11 / 12 + δ) with hKLg
  have hKLg0 : 0 ≤ KLg := (Linnik.KL_pos (by linarith) (by linarith)).le
  set c₀ := (KLmax + KLg) * Bc * 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₃ := c₀ * (4 / Real.log 2 + 2) / e₁ + 1 with hc₃
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.1 (LinnikTwelve.ev_log_pow (9 * Cc) δ 1 hδ)
  have hev : ∀ᶠ q : ℕ in Filter.atTop, c₃ ≤ (q : ℝ) ^ (e₁ * δ) ∧ max Q₁ 1 ≤ (q : ℝ) ^ e₁ ∧ 2 ≤ q :=
    (((tendsto_rpow_atTop (by positivity : 0 < e₁ * δ)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      c₃).and ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (max Q₁ 1)).and (Filter.eventually_ge_atTop 2))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q hq θ Q y hθ hθ1 hKLθ hQ1 hQ2 hy => ?_⟩
  obtain ⟨hc₃q, hQ₁q, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2'
  have hlq0 : 0 < Real.log q := by linarith
  have hQge1 : 1 ≤ Q := le_trans (le_max_right _ _) (hQ₁q.trans hQ1)
  have hQ0 : 0 < Q := by linarith
  have hlQ : e₁ * Real.log q ≤ Real.log Q := by
    rw [← Real.log_rpow hq0]; exact Real.log_le_log (by positivity) hQ1
  have hlQ0 : 0 < Real.log Q := lt_of_lt_of_le (by positivity) hlQ
  -- the tail term
  set H := (q : ℝ) ^ η with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hq1 hη.le
  have htail : Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹ ≤ Q ^ (θ + δ) := by
    have hpos : 0 < (1 + H) ^ Kd := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have e : Q ^ (11 / 12 + δ) = Q ^ (θ + δ) * Q ^ (11 / 12 - θ) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    rw [e]
    gcongr
    calc Q ^ (11 / 12 - θ) ≤ Q ^ (5 / 12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
      _ ≤ ((q : ℝ) ^ U) ^ (5 / 12 : ℝ) := Real.rpow_le_rpow hQ0.le hQ2 (by norm_num)
      _ = (q : ℝ) ^ (5 * U / 12) := by rw [← Real.rpow_mul hq0.le]; ring_nf
      _ ≤ (q : ℝ) ^ (η * Kd) := Real.rpow_le_rpow_of_exponent_le hq1 hKd
      _ = H ^ Kd := by rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      _ ≤ (1 + H) ^ Kd := pow_le_pow_left₀ (by linarith) (by linarith) Kd
  -- the first term
  have hlogs := logs_le hq1 hη hη1 hy
  have hl0 : 0 ≤ Real.log (q + 2) + Real.log (|y| + 4) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q + 2)
    have := Real.log_nonneg (by linarith [abs_nonneg y] : (1 : ℝ) ≤ |y| + 4)
    linarith
  have hfirst : (Linnik.KL θ (θ + δ) + KLg) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
      (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) / Real.log Q ≤ Q ^ (θ + 2 * δ) := by
    have hKLθ0 : 0 ≤ Linnik.KL θ (θ + δ) := (Linnik.KL_pos (by linarith) (by linarith)).le
    have hQθ : 0 ≤ Q ^ (θ + δ) := by positivity
    have hstep1 : (Linnik.KL θ (θ + δ) + KLg) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
        (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) ≤ c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) := by
      calc _ ≤ (KLmax + KLg) * (4 + 2 * Real.log q) * Bc * (Q ^ (θ + δ) + Q ^ (θ + δ)) := by gcongr
        _ = c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) := by rw [hc₀]; ring
    have hstep2 : c₀ * (4 + 2 * Real.log q) / Real.log Q ≤ c₃ := by
      rw [div_le_iff₀ hlQ0]
      have h1 : c₀ * (4 + 2 * Real.log q) ≤ c₀ * (4 / Real.log 2 + 2) * Real.log q := by
        have : 4 ≤ 4 / Real.log 2 * Real.log q := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
        nlinarith
      have h2 : c₀ * (4 / Real.log 2 + 2) * Real.log q = c₀ * (4 / Real.log 2 + 2) / e₁ * (e₁ * Real.log q) := by
        field_simp
      have h3 : 0 ≤ c₀ * (4 / Real.log 2 + 2) / e₁ := by positivity
      calc c₀ * (4 + 2 * Real.log q) ≤ c₀ * (4 / Real.log 2 + 2) / e₁ * (e₁ * Real.log q) := by linarith
        _ ≤ c₀ * (4 / Real.log 2 + 2) / e₁ * Real.log Q := by gcongr
        _ ≤ c₃ * Real.log Q := by gcongr; rw [hc₃]; linarith
    have hstep3 : c₃ ≤ Q ^ δ := by
      calc c₃ ≤ (q : ℝ) ^ (e₁ * δ) := hc₃q
        _ = ((q : ℝ) ^ e₁) ^ δ := by rw [← Real.rpow_mul hq0.le]
        _ ≤ Q ^ δ := Real.rpow_le_rpow (by positivity) hQ1 hδ.le
    calc _ ≤ c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) / Real.log Q := by gcongr
      _ = c₀ * (4 + 2 * Real.log q) / Real.log Q * Q ^ (θ + δ) := by ring
      _ ≤ Q ^ δ * Q ^ (θ + δ) := by gcongr; exact hstep2.trans hstep3
      _ = Q ^ (θ + 2 * δ) := by rw [← Real.rpow_add hQ0]; ring_nf
  -- the prime powers
  have hsecond : Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1)) ≤ Q ^ (θ + 2 * δ) := by
    have hQQ₁ : Q₁ ≤ Q := le_trans (le_max_left _ _) (hQ₁q.trans hQ1)
    have hev := hQ₁ Q hQQ₁
    rw [pow_one] at hev
    calc _ ≤ Q ^ (1 / 2 + δ) := primePow_term_le hCc hQge1 hev
      _ ≤ Q ^ (θ + 2 * δ) := Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
  unfold MB
  have hKLθ : Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ) = Linnik.KL θ (θ + δ) + KLg := by rw [hKLg]
  rw [hKLθ]
  linarith

/-! ### The exponents on the window -/

/-- **The factors as powers of `q`.** With `P = q^m`, `1 ≤ T ≤ 3q^η` and `g ≤ 1`:
`(q^L/P)^{θ′}((qT)^g)^{1/2}((P + q)V)^{1/2} ≤ 2√3·q^{(L−m)θ′ + g/2 + t + η/2}(V/P)^{1/2}`, where `t = (1 + m)/2` if
`m ≤ 1` and `t = m` if `m ≥ 1`, for `q > 1`. -/
lemma qpow_combine {q P V T η g θ' L m : ℝ} (hq : 1 < q) (hPm : P = q ^ m) (hT1 : 1 ≤ T)
    (hT : T ≤ 3 * q ^ η) (hg1 : g ≤ 1) :
    (m ≤ 1 → (q ^ L / P) ^ θ' * Real.sqrt ((q * T) ^ g) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ ((L - m) * θ' + g / 2 + (1 + m) / 2 + η / 2) * Real.sqrt (V / P)) ∧
    (1 ≤ m → (q ^ L / P) ^ θ' * Real.sqrt ((q * T) ^ g) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ ((L - m) * θ' + g / 2 + m + η / 2) * Real.sqrt (V / P)) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  -- the first factor
  have h1 : (q ^ L / P) ^ θ' = q ^ ((L - m) * θ') := by
    rw [hPm, ← Real.rpow_sub hq0, ← Real.rpow_mul hq0.le]
  -- the second factor
  have h2 : Real.sqrt ((q * T) ^ g) ≤ Real.sqrt 3 * q ^ (g / 2 + η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.mul_rpow hq0.le hT0.le]
    have hTg : T ^ (g * (1 / 2)) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
    have hT3 : T ^ (1 / 2 : ℝ) ≤ (3 * q ^ η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hT0.le hT (by norm_num)
    have e3 : (3 * q ^ η) ^ (1 / 2 : ℝ) = Real.sqrt 3 * q ^ (η / 2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; ring_nf
    have eq : q ^ (g * (1 / 2)) * q ^ (η / 2) = q ^ (g / 2 + η / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    calc q ^ (g * (1 / 2)) * T ^ (g * (1 / 2)) ≤ q ^ (g * (1 / 2)) * (Real.sqrt 3 * q ^ (η / 2)) := by
          gcongr; exact (hTg.trans hT3).trans e3.le
      _ = Real.sqrt 3 * q ^ (g / 2 + η / 2) := by rw [← eq]; ring
  -- the third factor
  have hsplit : Real.sqrt ((P + q) * V) = Real.sqrt ((P + q) * P) * Real.sqrt (V / P) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA : 0 ≤ q ^ ((L - m) * θ') := by positivity
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  constructor
  · intro hm1
    have hPq : P ≤ q := by
      rw [hPm]; calc q ^ m ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le hm1
        _ = q := Real.rpow_one q
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ ((1 + m) / 2) := by
      have hb : (P + q) * P ≤ 2 * q ^ (1 + m) := by
        rw [Real.rpow_add hq0, Real.rpow_one, ← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * q ^ (1 + m)) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ ((1 + m) / 2) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (q ^ (1 + m)), ← Real.rpow_mul hq0.le]; ring_nf
        _ ≤ 2 * q ^ ((1 + m) / 2) := by gcongr
    have eq : q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ ((1 + m) / 2) =
        q ^ ((L - m) * θ' + g / 2 + (1 + m) / 2 + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [h1, hsplit]
    calc q ^ ((L - m) * θ') * Real.sqrt ((q * T) ^ g) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ ((L - m) * θ') * (Real.sqrt 3 * q ^ (g / 2 + η / 2)) * (2 * q ^ ((1 + m) / 2) * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ ((1 + m) / 2)) * Real.sqrt (V / P) := by
          ring
      _ = _ := by rw [eq]
  · intro hm1
    have hPq : q ≤ P := by
      rw [hPm]; calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ m := Real.rpow_le_rpow_of_exponent_le hq.le hm1
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ m := by
      have hb : (P + q) * P ≤ 2 * (q ^ m) ^ 2 := by rw [← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * (q ^ m) ^ 2) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ m := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        _ ≤ 2 * q ^ m := by gcongr
    have eq : q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ m =
        q ^ ((L - m) * θ' + g / 2 + m + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [h1, hsplit]
    calc q ^ ((L - m) * θ') * Real.sqrt ((q * T) ^ g) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ ((L - m) * θ') * (Real.sqrt 3 * q ^ (g / 2 + η / 2)) * (2 * q ^ m * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ m) * Real.sqrt (V / P) := by ring
      _ = _ := by rw [eq]

/-! ### Proposition 3′ for the curve step -/

/-- The grid of the bins: `β_i = 1/2 + (5/12)(i/500000)`, of width `1/1200000`. -/
noncomputable def βg (i : ℕ) : ℝ := 1 / 2 + 5 / 12 * ((i : ℝ) / 500000)

lemma βg_range {i : ℕ} (hi : i ≤ 500000) : 1 / 2 ≤ βg i ∧ βg i ≤ 11 / 12 := by
  have h : (i : ℝ) ≤ 500000 := by exact_mod_cast hi
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold βg
  constructor
  · have : 0 ≤ 5 / 12 * ((i : ℝ) / 500000) := by positivity
    linarith
  · have : (i : ℝ) / 500000 ≤ 1 := by rw [div_le_one (by norm_num)]; exact h
    nlinarith

lemma βg_top : βg 500000 = 11 / 12 := by unfold βg; norm_num

lemma βg_zero : βg 0 = 1 / 2 := by unfold βg; norm_num

lemma βg_succ (i : ℕ) : βg (i + 1) = βg i + 1 / 1200000 := by unfold βg; push_cast; ring

lemma MB_nonneg {q : ℕ} {Bc Cc : ℝ} {Kd : ℕ} {θ δ H Q y : ℝ} (hBc : 0 ≤ Bc) (hCc : 0 ≤ Cc)
    (hθ1 : θ ≤ 11 / 12) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hH : 0 ≤ H) (hQ : 1 < Q) :
    0 ≤ MB q Bc Cc Kd θ δ H Q y := by
  unfold MB
  have h1 := Linnik.KL_pos (θ := θ) (θ' := θ + δ) (by linarith) (by linarith)
  have h2 := Linnik.KL_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  have h4 : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by have := abs_nonneg y; linarith)
  have h5 : 0 < Real.log Q := Real.log_pos hQ
  have hQ0 : 0 < Q := by linarith
  positivity

end Bins

end SieveTypeII

#print axioms SieveTypeII.card_class_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeII.bin_rect
#print axioms SieveTypeII.card_bin_le
#print axioms SieveTypeII.MB_le
#print axioms SieveTypeII.qpow_combine
