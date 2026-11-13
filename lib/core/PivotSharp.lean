import Mathlib
import PivotTop
import PivotMinorFT
import PivotCert

/-! # The pivot inequality `d_k ≥ d_1` for every `k`, from the explicit formula with `φ(t/N)/N²`

Plain statement. `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn)·K_H(m/n)` is the orbit form (`BallWeil.form`) and
`d_N = min{Q_N(x) : x_N = 1}` its `N`-th pivot. **RH holds if and only if the orbit-lattice conjecture of
`docs/ball-conjecture.md` does** (`rh_iff_orbitLattice`): under RH `d_N ≥ 0.0577 > d_1` for every `N ≥ 2`
(`pivot_ge_rh`), so `d_k ≥ d_1` for every `k` (`orbitLattice_of_rh`), and the converse is `BallWeil.rh_of_pivots`.

The theorems are first proved from RH and the minorant inequality `MuLe`: `μ(s) ≤ φ(s)(L(Ns) − log N)` for every
`N ≥ 2` and real `s`, with `L(t) = Re ψ(¼ + it/2) − log π` and `μ`, `φ` of `PivotMinor`, `PivotPhi`; `PivotCert.mu_le`
proves it (`muLe`).

* `form_ge`: for `N ≥ 2` and every real `x`, with `c_n = x_n√n`,
  `Q_N(x) ≥ (φ̂(0)/2πN)((log N + 7/8)Σc_n² − L(c)) − Σc_n²/(6000N)`, `L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}`
  Landau's form and `φ̂(0) = (999/1000)·4π/45`.
* `pivot_ge`: `Q_N(x) ≥ (999/1000)(2/45)(13/10)·x_N² ≥ 0.0577·x_N²`, so `d_N ≥ 0.0577` for every `N ≥ 2`.
* `orbitLattice_of_mu`: the pivot inequality `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)` for every `k ≥ 1` and all real `c`,
  as `d_1 = K_H(1) < 0.0539` (`WeilTest.hadamard_const_lt`).
* `rh_iff_orbitLattice_of_mu`: given `MuLe`, RH holds if and only if the orbit-lattice conjecture of
  `docs/ball-conjecture.md` does (the converse is `BallWeil.rh_of_pivots`).

The proof is the explicit formula (`weilExplicit_zeta`) for `h = |D|²Φ_N`, `D(t) = Σ_{n ≤ N}c_n n^{−it}`,
`Φ_N(t) = φ(t/N)/N²`.

- **The zero side.** Under RH `h(γ) = |V_x(ρ)|²Φ_N(γ)` (`zero_term`), and `φ(s)(s² + 1/16) ≤ 1` gives
  `Φ_N(γ) ≤ 1/(¼ + γ²)` for `N ≥ 2` (`phiN_le`): the zero side is at most `Q_N(x)` (`zero_side_le`).
- **The prime side is exact.** `Φ_N`'s transform is `φ̂(Nv)/N`, zero for `|v| ≥ 4/(5N)`, and every near miss `jn ≠ j'`
  has `|log(jn) − log j'| ≥ log(1 + 1/N) ≥ 2/(2N + 1) ≥ 4/(5N)` (`sep_log'`, from `log((1 + u)/(1 − u)) ≥ 2u`): the
  prime side is `(φ̂(0)/2πN)L(c)` exactly (`prime_eq`).
- **The archimedean term.** `MuLe` at `s = t/N` gives `Φ_N(t)(L(t)) ≥ (μ(t/N) + φ(t/N)log N)/N²`; `μ̂` vanishes for
  `|v| ≥ 1` and distinct frequencies are `1/N` apart (`sep_diag`), so `∫|D|²μ(t/N)/N² = (μ̂(0)/N)Σc_n²` exactly
  (`integral_Kc_muN`), with `μ̂(0) ≥ (7/8)φ̂(0)` (`PivotMinorFT.integral_mu_ge`); likewise the diagonal
  `∫|D|²Φ_N = (φ̂(0)/N)Σc_n²` (`integral_Kc_phiN`). So the term is at least `(φ̂(0)/2πN)(log N + 7/8)Σc_n²`
  (`arch_ge`).
- **The pole.** `‖φ_ℂ(i/2N)‖ ≤ 1/(12000N²)` (`PivotPhi.norm_phiE_I_le`), so the pole costs at most `Σc_n²/(6000N)`
  (`pole_ge`), `5/1332` of the mass.
- **The top vertex.** `PivotTop.top_bound` at `d = 7/8 − 5/1332 ≥ 17/20` gives
  `(log N + d)Σc_n² − L(c) ≥ (13/10)c_N²`, and `c_N² = N x_N²`.
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil BallCutoff
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace PivotSharp

/-! ## Separation of the frequencies -/

/-- `log(a + 1) − log a ≥ 2/(2a + 1)`: `log((1 + u)/(1 − u)) ≥ 2u` at `u = 1/(2a + 1)`. -/
lemma log_succ_sub_ge {a : ℝ} (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (a + 1) - Real.log a := by
  set u : ℝ := 1 / (2 * a + 1) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one (by linarith)]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := u) (by rw [abs_of_nonneg hu0]; exact hu1)
  have h0 := le_hasSum hs 0 (fun k _ => by positivity)
  have h2a : 2 * a + 1 ≠ 0 := by positivity
  have e1 : 1 + u = 2 * (a + 1) / (2 * a + 1) := by rw [hu]; field_simp; ring
  have e2 : 1 - u = 2 * a / (2 * a + 1) := by rw [hu]; field_simp; ring
  have hl : Real.log (1 + u) - Real.log (1 - u) = Real.log (a + 1) - Real.log a := by
    rw [e1, e2, Real.log_div (x := 2 * (a + 1)) (y := 2 * a + 1) (by positivity) (by positivity),
      Real.log_div (x := 2 * a) (y := 2 * a + 1) (by positivity) (by positivity),
      Real.log_mul (x := 2) (y := a + 1) (by norm_num) (by positivity),
      Real.log_mul (x := 2) (y := a) (by norm_num) (by positivity)]
    ring
  have e3 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * u ^ (2 * 0 + 1) = 2 / (2 * a + 1) := by
    rw [hu]; push_cast; ring
  rw [hl, e3] at h0
  exact h0

/-- For integers `1 ≤ a < b`: `log b − log a ≥ 2/(2a + 1)`. -/
lemma log_gap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : 2 / (2 * (a : ℝ) + 1) ≤ Real.log b - Real.log a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 := log_succ_sub_ge ha0
  have hb : (a : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt hab
  have h2 : Real.log ((a : ℝ) + 1) ≤ Real.log b := Real.log_le_log (by positivity) hb
  linarith

/-- **Near misses at scale `N`**: for `j, j' ∈ [1, N]`, `n ≥ 1` and `jn ≠ j'`, `|log(jn) − log j'| ≥ 2/(2N + 1)`. -/
lemma sep_log' {N j j' n : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hn : 1 ≤ n) (hne : j * n ≠ j') :
    2 / (2 * (N : ℝ) + 1) ≤ |Real.log ((j * n : ℕ) : ℝ) - Real.log j'| := by
  obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
  obtain ⟨hj'1, hj'N⟩ := Finset.mem_Icc.1 hj'
  have hjn1 : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := log_gap hjn1 hlt
    have hle : ((j * n : ℕ) : ℝ) ≤ N := by exact_mod_cast (hlt.le.trans hj'N)
    have hmono : 2 / (2 * (N : ℝ) + 1) ≤ 2 / (2 * ((j * n : ℕ) : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hpos : 0 < 2 / (2 * ((j * n : ℕ) : ℝ) + 1) := by positivity
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h := log_gap hj'1 hgt
    have hle : (j' : ℝ) ≤ N := by exact_mod_cast hj'N
    have hmono : 2 / (2 * (N : ℝ) + 1) ≤ 2 / (2 * (j' : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hpos : 0 < 2 / (2 * (j' : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **Distinct frequencies**: for `j ≠ j'` in `[1, N]`, `|log j' − log j| ≥ 1/N`. -/
lemma sep_diag {N j j' : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hne : j ≠ j') :
    1 / (N : ℝ) ≤ |Real.log j' - Real.log j| := by
  obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
  obtain ⟨hj'1, hj'N⟩ := Finset.mem_Icc.1 hj'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := log_gap hj1 hlt
    have hjN' : (j : ℝ) + 1 ≤ N := by exact_mod_cast (show j + 1 ≤ N by omega)
    have hmono : 1 / (N : ℝ) ≤ 2 / (2 * (j : ℝ) + 1) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]; linarith
    have hpos : 0 < 2 / (2 * (j : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h := log_gap hj'1 hgt
    have hjN' : (j' : ℝ) + 1 ≤ N := by exact_mod_cast (show j' + 1 ≤ N by omega)
    have hmono : 1 / (N : ℝ) ≤ 2 / (2 * (j' : ℝ) + 1) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]; linarith
    have hpos : 0 < 2 / (2 * (j' : ℝ) + 1) := by positivity
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith

lemma four_fifths_le {N : ℕ} (hN : 2 ≤ N) : 4 / (5 * (N : ℝ)) ≤ 2 / (2 * (N : ℝ) + 1) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Exactness**: if `F(v) = 0` for `|v| ≥ δ` and every near miss `jn ≠ j'` has `|log(jn) − log j'| ≥ δ`, then
`Σ_{j,j'}c_j c_{j'}F(log j' − log j − log n) = F(0)e_n`. -/
lemma sum_exact_of {N : ℕ} (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {F : ℝ → ℝ} {δ : ℝ}
    (hF : ∀ v, δ ≤ |v| → F v = 0)
    (hsep : ∀ j ∈ Icc 1 N, ∀ j' ∈ Icc 1 N, j * n ≠ j' → δ ≤ |Real.log ((j * n : ℕ) : ℝ) - Real.log j'|) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * F (Real.log j' - Real.log j - Real.log n) = F 0 * ex N c n := by
  rw [← sum_exact N c hn (F 0)]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  congr 1
  by_cases h : j * n = j'
  · rw [ite_eq_left h, ← h, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      show Real.log j + Real.log n - Real.log j - Real.log n = 0 by ring]
  · rw [ite_eq_right h]
    apply hF
    have hs := hsep j hj j' hj' h
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at hs
    rw [show Real.log j' - Real.log j - Real.log n = -(Real.log j + Real.log n - Real.log j') by ring, abs_neg]
    exact hs

/-! ## The weight and the minorant at scale `N` -/

/-- `Φ_N(t) = φ(t/N)/N²`. -/
def phiN (N : ℕ) (t : ℝ) : ℝ := PivotPhi.phi (t / N) / (N : ℝ) ^ 2

/-- `M_N(t) = μ(t/N)/N²`. -/
def muN (N : ℕ) (t : ℝ) : ℝ := PivotMinor.mu (t / N) / (N : ℝ) ^ 2

/-- `μ̂(v) = ∫μ(s)cos(sv) ds`. -/
def muT (v : ℝ) : ℝ := ∫ s, PivotMinor.mu s * Real.cos (s * v)

lemma muT_neg (v : ℝ) : muT (-v) = muT v := by
  unfold muT; simp_rw [mul_neg, Real.cos_neg]

lemma muT_eq_zero {v : ℝ} (hv : 1 ≤ |v|) : muT v = 0 := PivotMinorFT.integral_mu_cos_eq_zero hv

lemma muT_zero_ge : 7 / 8 * PivotPhi.phiT 0 ≤ muT 0 := by
  have h := PivotMinorFT.integral_mu_ge
  unfold muT; simp only [mul_zero, Real.cos_zero, mul_one]; exact h

lemma scale_eq {N : ℕ} (hN : 1 ≤ N) (v t : ℝ) : t / N * (N * v) = t * v := by
  have hN0 : (N : ℝ) ≠ 0 := (show (0 : ℝ) < N by exact_mod_cast hN).ne'
  calc t / N * (N * v) = t * v * ((N : ℝ) / N) := by ring
    _ = t * v := by rw [div_self hN0, mul_one]

lemma integrable_scale_cos {N : ℕ} (hN : 1 ≤ N) {f : ℝ → ℝ} (hf : ∀ v, Integrable fun s => f s * Real.cos (s * v))
    (v : ℝ) : Integrable fun t => f (t / N) / (N : ℝ) ^ 2 * Real.cos (t * v) := by
  have hN0 : (N : ℝ) ≠ 0 := (show (0 : ℝ) < N by exact_mod_cast hN).ne'
  refine (((hf (N * v)).comp_div hN0).const_mul (1 / (N : ℝ) ^ 2)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [scale_eq hN]
  ring

lemma integral_scale_cos {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (v : ℝ) :
    ∫ t, f (t / N) / (N : ℝ) ^ 2 * Real.cos (t * v) = (∫ s, f s * Real.cos (s * (N * v))) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (fun t => f (t / N) / (N : ℝ) ^ 2 * Real.cos (t * v)) =
      fun t => 1 / (N : ℝ) ^ 2 * (fun s => f s * Real.cos (s * (N * v))) (t / N) := by
    funext t; simp only; rw [scale_eq hN]; ring
  rw [e, integral_const_mul, Measure.integral_comp_div (fun s => f s * Real.cos (s * (N * v))) (N : ℝ),
    abs_of_pos hN0, smul_eq_mul]
  have hN0' : (N : ℝ) ≠ 0 := hN0.ne'
  have hI : ∀ I : ℝ, 1 / (N : ℝ) ^ 2 * (N * I) = I / N := fun I => by
    rw [one_div, ← div_eq_inv_mul, pow_two, mul_comm (N : ℝ) I, mul_div_mul_right _ _ hN0']
  exact hI _

lemma integrable_phiN_cos {N : ℕ} (hN : 1 ≤ N) (v : ℝ) : Integrable fun t => phiN N t * Real.cos (t * v) :=
  integrable_scale_cos hN PivotPhi.integrable_phi_cos v

lemma integral_phiN_cos {N : ℕ} (hN : 1 ≤ N) (v : ℝ) :
    ∫ t, phiN N t * Real.cos (t * v) = PivotPhi.phiT (N * v) / N := by
  unfold phiN; rw [integral_scale_cos hN, PivotPhi.integral_phi_cos]

lemma integrable_muN_cos {N : ℕ} (hN : 1 ≤ N) (v : ℝ) : Integrable fun t => muN N t * Real.cos (t * v) :=
  integrable_scale_cos hN PivotMinorFT.integrable_mu_cos v

lemma integral_muN_cos {N : ℕ} (hN : 1 ≤ N) (v : ℝ) : ∫ t, muN N t * Real.cos (t * v) = muT (N * v) / N := by
  unfold muN; rw [integral_scale_cos hN]; rfl


/-! ## `|D|²` against the weights: the prime side and the diagonal are exact -/

/-- `∫|D(t)|²Φ_N(t)cos(t log n) dt = (φ̂(0)/N)e_n` for `N ≥ 2`, `n ≥ 1`. -/
lemma integral_Kc_phiN_log {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t, Kc N c t * phiN N t * Real.cos (t * Real.log n) = PivotPhi.phiT 0 / N * ex N c n := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [integral_Kc_mul_cos N c (integrable_phiN_cos hN1) (integral_phiN_cos hN1),
    sum_symm_of_even N c (φh := fun v => PivotPhi.phiT (N * v) / N)
      (fun v => by simp only [mul_neg, PivotPhi.phihat_neg])]
  have h := sum_exact_of (N := N) c hn (F := fun v => PivotPhi.phiT (N * v) / N) (δ := 4 / (5 * N)) ?_ ?_
  · simp only [mul_zero] at h
    exact h
  · intro v hv
    have hv' : 4 / 5 ≤ |(N : ℝ) * v| := by
      rw [abs_mul, abs_of_pos hN0]
      rw [div_le_iff₀ (by positivity)] at hv
      linarith
    rw [PivotPhi.phiT_eq_zero hv', zero_div]
  · intro j hj j' hj' hne
    exact le_trans (four_fifths_le hN) (sep_log' hj hj' hn hne)

/-- **The diagonal**: `∫|D|²Φ_N = (φ̂(0)/N)Σc_n²`. -/
lemma integral_Kc_phiN {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    ∫ t, Kc N c t * phiN N t = PivotPhi.phiT 0 / N * S2 N c := by
  have h := integral_Kc_phiN_log hN c (n := 1) le_rfl
  simp only [Nat.cast_one, Real.log_one, mul_zero, Real.cos_zero, mul_one, ex_one] at h
  exact h

/-- **The minorant's diagonal**: `∫|D|²M_N = (μ̂(0)/N)Σc_n²`, as `μ̂` vanishes beyond `1` and distinct frequencies are
`1/N` apart. -/
lemma integral_Kc_muN {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    ∫ t, Kc N c t * muN N t = muT 0 / N * S2 N c := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : ∫ t, Kc N c t * muN N t = ∫ t, Kc N c t * muN N t * Real.cos (t * 0) := by
    simp only [mul_zero, Real.cos_zero, mul_one]
  rw [e, integral_Kc_mul_cos N c (integrable_muN_cos hN1) (integral_muN_cos hN1),
    sum_symm_of_even N c (φh := fun v => muT (N * v) / N) (fun v => by simp only [mul_neg, muT_neg])]
  have hx := sum_exact_of (N := N) c (n := 1) le_rfl (F := fun v => muT (N * v) / N) (δ := 1 / N) ?_ ?_
  · simp only [Nat.cast_one, Real.log_one, sub_zero, mul_zero, ex_one] at hx
    simp only [sub_zero]
    exact hx
  · intro v hv
    have hv' : 1 ≤ |(N : ℝ) * v| := by
      rw [abs_mul, abs_of_pos hN0]
      rw [div_le_iff₀ hN0] at hv
      linarith
    rw [muT_eq_zero hv', zero_div]
  · intro j hj j' hj' hne
    rw [Nat.mul_one] at hne ⊢
    rw [abs_sub_comm]
    exact sep_diag hj hj' hne

/-! ## The test function and the explicit formula -/

/-- `Φ_N` on `ℂ`: `φ_ℂ(z/N)/N²`. -/
def phiEN (N : ℕ) (z : ℂ) : ℂ := PivotPhi.phiE (z / (N : ℂ)) / (N : ℂ) ^ 2

/-- `h(z) = D(z)D(−z)Φ_N(z)`. -/
def htP (N : ℕ) (c : ℕ → ℝ) (z : ℂ) : ℂ := DC N c z * DC N c (-z) * phiEN N z

/-- `h` on `ℝ`: `|D(t)|²Φ_N(t)`. -/
def hRP (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ := Kc N c t * phiN N t

lemma phiEN_ofReal (N : ℕ) (t : ℝ) : phiEN N t = (phiN N t : ℂ) := by
  unfold phiEN phiN
  have e : (t : ℂ) / (N : ℂ) = ((t / N : ℝ) : ℂ) := by push_cast; rfl
  rw [e, PivotPhi.phiE_ofReal]
  push_cast
  rfl

lemma phiEN_neg (N : ℕ) (z : ℂ) : phiEN N (-z) = phiEN N z := by
  unfold phiEN; rw [neg_div, PivotPhi.phiE_neg]

lemma htP_ofReal (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : htP N c t = (hRP N c t : ℂ) := by
  unfold htP hRP
  rw [DC_ofReal, DC_neg_ofReal, phiEN_ofReal, Kc_eq]
  push_cast
  linear_combination (-(Bc N c t : ℂ) ^ 2 * (phiN N t : ℂ)) * Complex.I_sq

lemma htP_even (N : ℕ) (c : ℕ → ℝ) (z : ℂ) : htP N c (-z) = htP N c z := by
  unfold htP; rw [neg_neg, phiEN_neg]; ring

lemma striptest_htP {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z ∈ WeilStrip.strip (-1) 1, ‖PivotPhi.phiE z‖ ≤ K / (1 + z.re ^ 2)) :
    WeilStrip.StripTest (htP N c) ((N * S1 N c) ^ 2 * K) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨?_, fun t ht => ?_⟩
  · have hd : Differentiable ℂ (phiEN N) := by
      unfold phiEN
      exact (PivotPhi.differentiable_phiE.comp (differentiable_id.div_const _)).div_const _
    exact (((differentiable_DC N c).mul ((differentiable_DC N c).comp differentiable_neg)).mul hd).differentiableOn
  · have him : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    have hz : t / (N : ℂ) ∈ WeilStrip.strip (-1) 1 := by
      have e : (t / (N : ℂ)).im = t.im / N := Complex.div_natCast_im t N
      have h1 : -1 ≤ t.im / N := by
        rw [le_div_iff₀ hN0]; nlinarith [ht.1]
      have h2 : t.im / N ≤ 1 := by
        rw [div_le_iff₀ hN0]; nlinarith [ht.2]
      exact ⟨by rw [e]; exact h1, by rw [e]; exact h2⟩
    have h3 := hK _ hz
    rw [Complex.div_natCast_re] at h3
    have h4 : ‖phiEN N t‖ ≤ K / (1 + t.re ^ 2) := by
      unfold phiEN
      rw [norm_div, norm_pow, Complex.norm_natCast]
      have e : (1 + (t.re / N) ^ 2) * (N : ℝ) ^ 2 = N ^ 2 + t.re ^ 2 := by field_simp
      calc ‖PivotPhi.phiE (t / (N : ℂ))‖ / (N : ℝ) ^ 2 ≤ K / (1 + (t.re / N) ^ 2) / (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right h3 (by positivity)
        _ = K / (N ^ 2 + t.re ^ 2) := by rw [div_div, e]
        _ ≤ K / (1 + t.re ^ 2) :=
            div_le_div_of_nonneg_left hK0 (by positivity) (by nlinarith)
    have h1 := norm_DC_le N c him
    have h2 := norm_DC_le N c (z := -t) (by rwa [Complex.neg_im, abs_neg])
    have hS := S1_nonneg N c
    unfold htP
    rw [norm_mul, norm_mul]
    calc ‖DC N c t‖ * ‖DC N c (-t)‖ * ‖phiEN N t‖ ≤ (N * S1 N c) * (N * S1 N c) * (K / (1 + t.re ^ 2)) := by
          gcongr
      _ = (N * S1 N c) ^ 2 * K / (1 + t.re ^ 2) := by ring

/-- **Weil's explicit formula for `|D|²Φ_N`** (`weilExplicit_zeta`, no RH input). -/
lemma weil_htP {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) : WeilExplicit zetaZeroFamily (htP N c) (hRP N c) := by
  obtain ⟨K, hK0, hK⟩ := PivotPhi.phiE_strip
  exact weilExplicit_zeta (striptest_htP hN c hK0 hK) (htP_even N c) (htP_ofReal N c)


/-! ## The zero side, the pole and the prime side -/

/-- Under RH, `h(t_ρ) = |V_x(ρ)|²Φ_N(γ)` with the coefficients `c_n = x_n√n`. -/
lemma zero_term (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) :
    htP N (fun n => x n * Real.sqrt n) ((zetaZeroFamily q - 1 / 2) / I) =
      ((‖BallRate.dpoly N x q‖ ^ 2 * phiN N (zetaZeroFamily q).im : ℝ) : ℂ) := by
  have ht : (zetaZeroFamily q - 1 / 2) / I = ((zetaZeroFamily q).im : ℂ) := by
    rw [BallHadamard.zZF_sub_half hRH q, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  rw [ht, htP_ofReal]
  congr 1
  unfold hRP
  rw [BallSampling.dpoly_eq_conj hRH, Complex.norm_conj, dp_eq_DC, norm_DC_ofReal_sq]

/-- `Φ_N(γ) ≤ 1/(¼ + γ²)` for `N ≥ 2`: from `φ(s)(s² + 1/16) ≤ 1`. -/
lemma phiN_le {N : ℕ} (hN : 2 ≤ N) (γ : ℝ) : phiN N γ ≤ 1 / (1 / 4 + γ ^ 2) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN0' : (N : ℝ) ≠ 0 := hN0.ne'
  have h := PivotPhi.phi_mul_le (γ / N)
  have hφ := PivotPhi.phi_nonneg (γ / N)
  unfold phiN
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have e : (γ / N) ^ 2 * (N : ℝ) ^ 2 = γ ^ 2 := by field_simp
  have hN4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h3 : 1 / 4 + γ ^ 2 ≤ ((γ / N) ^ 2 + 1 / 16) * (N : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hφ, mul_le_mul_of_nonneg_right h (sq_nonneg (N : ℝ))]

/-- **The zero side**: `Σ_ρ |V_x(ρ)|²Φ_N(γ) ≤ Q_N(x)` under RH. -/
lemma zero_side_le (hRH : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) {Z : ℝ}
    (hZ : HasSum (fun q => ‖BallRate.dpoly N x q‖ ^ 2 * phiN N (zetaZeroFamily q).im) Z) :
    Z ≤ BallWeil.form N x := by
  refine hasSum_le (fun q => ?_) hZ (BallRate.hasSum_form hRH N x)
  have h := phiN_le hN (zetaZeroFamily q).im
  calc ‖BallRate.dpoly N x q‖ ^ 2 * phiN N (zetaZeroFamily q).im
      ≤ ‖BallRate.dpoly N x q‖ ^ 2 * (1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

/-- **The pole**: `Re(h(i/2) + h(−i/2)) ≥ −Σc_n²/(6000N)` for `N ≥ 2`. -/
lemma pole_ge {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    -(S2 N c / (6000 * N)) ≤ (htP N c (I / 2) + htP N c (-(I / 2))).re := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [htP_even, ← two_mul]
  have hphi : ‖phiEN N (I / 2)‖ ≤ 1 / (12000 * (N : ℝ) ^ 4) := by
    unfold phiEN
    have e : I / 2 / (N : ℂ) = I * ((1 / (2 * N) : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_pow, Complex.norm_natCast]
    have hy : 1 / (2 * (N : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h1 := PivotPhi.norm_phiE_I_le (y := 1 / (2 * N)) (by positivity) hy
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖PivotPhi.phiE (I * ((1 / (2 * N) : ℝ) : ℂ))‖ * (12000 * (N : ℝ) ^ 4)
        ≤ (1 / (2 * N)) ^ 2 / 3000 * (12000 * (N : ℝ) ^ 4) := by gcongr
      _ = 1 * (N : ℝ) ^ 2 := by field_simp; ring
  have h1 : ‖htP N c (I / 2)‖ ≤ (N * S1 N c) ^ 2 * (1 / (12000 * (N : ℝ) ^ 4)) := by
    unfold htP
    rw [norm_mul, norm_mul]
    have hd1 := norm_DC_le N c (z := I / 2) (by norm_num)
    have hd2 := norm_DC_le N c (z := -(I / 2)) (by norm_num)
    have hS := S1_nonneg N c
    calc ‖DC N c (I / 2)‖ * ‖DC N c (-(I / 2))‖ * ‖phiEN N (I / 2)‖
        ≤ (N * S1 N c) * (N * S1 N c) * (1 / (12000 * (N : ℝ) ^ 4)) := by gcongr
      _ = _ := by ring
  have hS1 := BallCutoff.S1_sq_le N c
  have h2 : (N * S1 N c) ^ 2 * (1 / (12000 * (N : ℝ) ^ 4)) ≤ S2 N c / (12000 * N) := by
    rw [mul_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hS1 (show (0 : ℝ) ≤ 12000 * (N : ℝ) ^ 3 by positivity)
    nlinarith
  have h3 := Complex.abs_re_le_norm (2 * htP N c (I / 2))
  rw [norm_mul, Complex.norm_two] at h3
  have h4 := neg_abs_le (2 * htP N c (I / 2)).re
  have e2 : S2 N c / (6000 * N) = 2 * (S2 N c / (12000 * N)) := by field_simp; ring
  linarith

/-- **The prime side is Landau's form**, exactly: `2Σ_n Λ(n)n^{−1/2}g_h(log n) = (φ̂(0)/2πN)·L(c)`. -/
lemma prime_eq {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (hRP N c) (Real.log n) =
      PivotPhi.phiT 0 / (2 * π * N) * (2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n) := by
  have hgh : ∀ n : ℕ, 1 ≤ n → gh (hRP N c) (Real.log n) = PivotPhi.phiT 0 / (2 * π * N) * ex N c n := by
    intro n hn
    unfold gh hRP
    rw [integral_Kc_phiN_log hN c hn]
    ring
  have h0 : ∀ n ∉ Icc 1 N, Λ n / Real.sqrt n * gh (hRP N c) (Real.log n) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have : N < n := by
        by_contra h
        push Not at h
        exact hn (Finset.mem_Icc.2 ⟨hn0, h⟩)
      rw [hgh n hn0, ex_eq_zero N c this, mul_zero, mul_zero]
  rw [tsum_eq_sum h0]
  have e : ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * gh (hRP N c) (Real.log n) =
      PivotPhi.phiT 0 / (2 * π * N) * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hgh n (Finset.mem_Icc.1 hn).1]; ring
  rw [e]; ring

/-! ## The archimedean term -/

/-- **The minorant inequality** `μ(s) ≤ φ(s)(L(Ns) − log N)` for every `N ≥ 2`, with `L(t) = Re ψ(¼ + it/2) − log π`:
the hypothesis of `form_ge`, `pivot_ge` and `orbitLattice_of_mu`, besides RH. `PivotCert.mu_le` proves it (`muLe`). -/
def MuLe : Prop := ∀ N : ℕ, 2 ≤ N → ∀ s : ℝ,
  PivotMinor.mu s ≤ PivotPhi.phi s * (psiRe ((N : ℝ) * s) - Real.log π - Real.log N)

lemma integrable_hRP {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) : Integrable (hRP N c) := by
  have h := integrable_Kc_mul_cos N c (integrable_phiN_cos hN) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integrable_Kc_muN {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) : Integrable fun t => Kc N c t * muN N t := by
  have h := integrable_Kc_mul_cos N c (integrable_muN_cos hN) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integrable_hRP_psi {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) : Integrable (fun r => hRP N c r * psiRe r) := by
  obtain ⟨K, hK0, hK⟩ := PivotPhi.phiE_strip
  refine (integrable_psi_real (striptest_htP hN c hK0 hK)).re.congr (Filter.Eventually.of_forall fun r => ?_)
  show RCLike.re (htP N c r * Complex.digamma (zB r)) = hRP N c r * psiRe r
  rw [htP_ofReal]
  simp [psiRe]

/-- **The archimedean term**: `−g_h(0)log π + (1/2π)∫h Re ψ ≥ (1/2π)(μ̂(0) + φ̂(0)log N)Σc_n²/N`. -/
lemma arch_ge (hmu : MuLe) {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    1 / (2 * π) * ((muT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c) ≤
      -(gh (hRP N c) 0 * Real.log π) + 1 / (2 * π) * ∫ r, hRP N c r * psiRe r := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN0' : (N : ℝ) ≠ 0 := hN0.ne'
  have hiR := integrable_hRP hN1 c
  have hiP := integrable_hRP_psi hN1 c
  have hiM := integrable_Kc_muN hN1 c
  have hpt : ∀ r, Kc N c r * muN N r + Real.log N * hRP N c r ≤
      hRP N c r * psiRe r - Real.log π * hRP N c r := by
    intro r
    have h1 := hmu N hN (r / N)
    rw [show (N : ℝ) * (r / N) = r by field_simp] at h1
    have hK := Kc_nonneg N c r
    have h2 : PivotMinor.mu (r / N) / (N : ℝ) ^ 2 ≤
        PivotPhi.phi (r / N) / (N : ℝ) ^ 2 * (psiRe r - Real.log π - Real.log N) := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    unfold hRP muN phiN
    nlinarith
  have hint : ∫ r, (Kc N c r * muN N r + Real.log N * hRP N c r) ≤
      ∫ r, (hRP N c r * psiRe r - Real.log π * hRP N c r) :=
    integral_mono (hiM.add (hiR.const_mul (Real.log N))) (hiP.sub (hiR.const_mul (Real.log π))) hpt
  rw [integral_add hiM (hiR.const_mul _), integral_sub hiP (hiR.const_mul _), integral_const_mul,
    integral_const_mul, integral_Kc_muN hN c] at hint
  have hR : ∫ r, hRP N c r = PivotPhi.phiT 0 / N * S2 N c := integral_Kc_phiN hN c
  rw [hR] at hint
  have hgh0 : gh (hRP N c) 0 = 1 / (2 * π) * ∫ r, hRP N c r := by
    unfold gh; simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hgh0, hR]
  have hpi : 0 < 1 / (2 * π) := by positivity
  have := mul_le_mul_of_nonneg_left hint hpi.le
  have e : (muT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c =
      muT 0 / N * S2 N c + Real.log N * (PivotPhi.phiT 0 / N * S2 N c) := by ring
  rw [e]
  linarith


/-! ## The theorem -/

/-- **The explicit-formula bound** (RH, with the minorant): for `N ≥ 2` and every real `x`, with `c_n = x_n√n`,
`Q_N(x) ≥ (φ̂(0)/2πN)((log N + 7/8)Σc_n² − L(c)) − Σc_n²/(6000N)`, where `L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}e_n` is
Landau's form. -/
theorem form_ge (hRH : RiemannHypothesis) (hmu : MuLe) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    PivotPhi.phiT 0 / (2 * π * N) * ((Real.log N + 7 / 8) * S2 N (fun n => x n * Real.sqrt n) -
      2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun n => x n * Real.sqrt n) n) -
      S2 N (fun n => x n * Real.sqrt n) / (6000 * N) ≤ BallWeil.form N x := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  have hsum := (weil_htP hN1 c).2
  have hre := Complex.hasSum_re hsum
  have hterm : ∀ q, (htP N c ((zetaZeroFamily q - 1 / 2) / I)).re =
      ‖BallRate.dpoly N x q‖ ^ 2 * phiN N (zetaZeroFamily q).im := fun q => by
    rw [hc, zero_term hRH N x q, Complex.ofReal_re]
  simp only [hterm] at hre
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hZ := zero_side_le hRH hN x hre
  have hpole := pole_ge hN c
  have harch := arch_ge hmu hN c
  have hprime := prime_eq hN c
  have hmuT := muT_zero_ge
  have hS2 := S2_nonneg N c
  have hlow : PivotPhi.phiT 0 / (2 * π * N) * ((Real.log N + 7 / 8) * S2 N c) ≤
      1 / (2 * π) * ((muT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c) := by
    have h1 : (7 / 8 * PivotPhi.phiT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c ≤
        (muT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c := by
      apply mul_le_mul_of_nonneg_right _ hS2
      apply div_le_div_of_nonneg_right _ hN0.le
      linarith
    have e : PivotPhi.phiT 0 / (2 * π * N) * ((Real.log N + 7 / 8) * S2 N c) =
        1 / (2 * π) * ((7 / 8 * PivotPhi.phiT 0 + Real.log N * PivotPhi.phiT 0) / N * S2 N c) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith [hZ, hpole, harch, hprime, hlow]

/-- **The pivots clear `d_1`** (RH, with the minorant): for `N ≥ 2` and every real `x`,
`Q_N(x) ≥ (999/1000)(2/45)(13/10)·x_N² = 0.0577·x_N²`. The explicit-formula bound with `PivotTop.top_bound` at
`d = 7/8 − 5/1332 ≥ 17/20`: the pole costs `5/1332` of the mass. -/
theorem pivot_ge (hRH : RiemannHypothesis) (hmu : MuLe) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    999 / 1000 * (2 / 45) * (13 / 10) * x N ^ 2 ≤ BallWeil.form N x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0' : (N : ℝ) ≠ 0 := hN0.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h := form_ge hRH hmu hN x
  have ht := PivotTop.top_bound hN (show (17 : ℝ) / 20 ≤ 7 / 8 - 5 / 1332 by norm_num)
    (fun n => x n * Real.sqrt n)
  have hcN : (x N * Real.sqrt N) ^ 2 = x N ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN0.le]
  simp only [hcN] at ht
  rw [PivotPhi.phihat_zero] at h
  set S := S2 N (fun n => x n * Real.sqrt n)
  set L := 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun n => x n * Real.sqrt n) n
  have hw : 0 ≤ 999 / 1000 * (4 * π / 45) / (2 * π * N) := by positivity
  have hm := mul_le_mul_of_nonneg_left ht hw
  have e1 : 999 / 1000 * (4 * π / 45) / (2 * π * N) * ((Real.log N + (7 / 8 - 5 / 1332)) * S - L) =
      999 / 1000 * (4 * π / 45) / (2 * π * N) * ((Real.log N + 7 / 8) * S - L) - S / (6000 * N) := by
    field_simp; ring
  have e2 : 999 / 1000 * (4 * π / 45) / (2 * π * N) * (13 / 10 * (x N ^ 2 * N)) =
      999 / 1000 * (2 / 45) * (13 / 10) * x N ^ 2 := by
    field_simp; ring
  linarith

/-- `d_1 = Q_1(δ_1) = K_H(1) < 0.0539`. -/
lemma gram_one_lt : BallWeil.gram 1 1 < 0.0539 := by
  rw [BallWeil.gram_self, BallWeil.kψ_one]
  simpa using WeilTest.hadamard_const_lt

/-- **The pivot inequality for every `k`** (RH, with the minorant): `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)` for every
`k ≥ 1` and all real `c`. At `k = 1` it is an equality; for `k ≥ 2` the pivot is at least `0.0577 > 0.0539 > d_1`. -/
theorem orbitLattice_of_mu (hRH : RiemannHypothesis) (hmu : MuLe) (k : ℕ) (c : ℕ → ℝ) (hk : 1 ≤ k) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    unfold BallWeil.form
    simp
  · have h := pivot_ge hRH hmu hk2 (fun n => if n = k then 1 else -c n)
    simp only [↓reduceIte, one_pow, mul_one] at h
    have hg := gram_one_lt
    norm_num at h
    linarith

/-- **RH ⟺ the orbit-lattice conjecture**, given the minorant inequality. -/
theorem rh_iff_orbitLattice_of_mu (hmu : MuLe) :
    RiemannHypothesis ↔ ∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k →
      BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  ⟨fun hRH k c hk => orbitLattice_of_mu hRH hmu k c hk, BallWeil.rh_of_pivots⟩

/-! ## Without the hypothesis -/

/-- The minorant inequality holds (`PivotCert.mu_le`). -/
theorem muLe : MuLe := fun _ hN s => PivotCert.mu_le hN s

/-- **Under RH every pivot clears `d_1`**: `Q_N(x) ≥ (999/1000)(2/45)(13/10)·x_N² ≥ 0.0577·x_N²` for every `N ≥ 2` and
every real `x`; so `d_N ≥ 0.0577 = 1.249·d_1`. -/
theorem pivot_ge_rh (hRH : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    999 / 1000 * (2 / 45) * (13 / 10) * x N ^ 2 ≤ BallWeil.form N x :=
  pivot_ge hRH muLe hN x

/-- **The orbit-lattice conjecture holds under RH**: `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)` for every `k ≥ 1` and all
real `c`. -/
theorem orbitLattice_of_rh (hRH : RiemannHypothesis) (k : ℕ) (c : ℕ → ℝ) (hk : 1 ≤ k) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  orbitLattice_of_mu hRH muLe k c hk

/-- **RH ⟺ the orbit-lattice conjecture**: RH holds if and only if `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)` for every
`k ≥ 1` and all real `c`, where `Q` is the form of the Gram matrix `√(mn)·K_H(m/n)` of the orbit, computed from the
primes. -/
theorem rh_iff_orbitLattice :
    RiemannHypothesis ↔ ∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k →
      BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  rh_iff_orbitLattice_of_mu muLe

/-! ## The orbit lattice: `w_1` is a shortest vector -/

/-- An integer vector supported at `1` has `Q_N(a) = a_1²·K_H(1)`. -/
lemma form_of_support_one {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℤ) (h : ∀ n ∈ Icc 2 N, a n = 0) :
    BallWeil.form N (fun n => (a n : ℝ)) = (a 1 : ℝ) ^ 2 * BallWeil.gram 1 1 := by
  rw [BallPivot.form_of_zero_above hN fun n h1 hnN => by
    rw [h n (Finset.mem_Icc.2 ⟨by omega, hnN⟩), Int.cast_zero]]
  unfold BallWeil.form
  simp only [Finset.Icc_self, Finset.sum_singleton]
  ring

lemma gram_one_pos : 0 < BallWeil.gram 1 1 := by
  rw [BallWeil.gram_self]
  simpa using BallWeil.kψ_one_pos

lemma one_le_sq_of_ne {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ z ^ 2 := by
    have := pow_pos (abs_pos.2 hz) 2
    rw [sq_abs] at this
    omega
  exact_mod_cast h1

/-- **Away from `±δ_1` the lattice is longer** (RH): an integer vector with a nonzero coefficient at some
`2 ≤ k ≤ N` has `Q_N(a) ≥ (999/1000)(2/45)(13/10) ≥ 0.0577`, by the pivot at its last nonzero coefficient. -/
theorem lattice_gap (hRH : RiemannHypothesis) {N : ℕ} (a : ℕ → ℤ) (h : ∃ n ∈ Icc 2 N, a n ≠ 0) :
    999 / 1000 * (2 / 45) * (13 / 10) ≤ BallWeil.form N (fun n => (a n : ℝ)) := by
  classical
  obtain ⟨n₀, hn₀, han₀⟩ := h
  set S := (Icc 2 N).filter (fun n => a n ≠ 0) with hS
  have hSne : S.Nonempty := ⟨n₀, Finset.mem_filter.2 ⟨hn₀, han₀⟩⟩
  have hkS : S.max' hSne ∈ S := Finset.max'_mem S hSne
  set k := S.max' hSne with hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hkS).1).1
  have hkN : k ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hkS).1).2
  have hak : a k ≠ 0 := (Finset.mem_filter.1 hkS).2
  have hzero : ∀ n, k < n → n ≤ N → a n = 0 := by
    intro n hkn hnN
    by_contra hne
    have hmem : n ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hnN⟩, hne⟩
    have := Finset.le_max' S n hmem
    omega
  rw [BallPivot.form_of_zero_above hkN fun n hkn hnN => by rw [hzero n hkn hnN, Int.cast_zero]]
  have hp := pivot_ge_rh hRH hk2 (fun n => (a n : ℝ))
  have hsq := one_le_sq_of_ne hak
  have hc : (0 : ℝ) ≤ 999 / 1000 * (2 / 45) * (13 / 10) := by norm_num
  calc (999 / 1000 * (2 / 45) * (13 / 10) : ℝ) = 999 / 1000 * (2 / 45) * (13 / 10) * 1 := (mul_one _).symm
    _ ≤ 999 / 1000 * (2 / 45) * (13 / 10) * ((a k : ℤ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hc
    _ ≤ BallWeil.form k (fun n => (a n : ℝ)) := hp

/-- **Under RH, `w_1` is a shortest vector of the orbit lattice**: every nonzero integer vector has
`Q_N(a) ≥ Q_1(δ_1) = K_H(1)`. In a realization `Q_N(a) = ‖Σ_n a_n w_n‖²` (`BallWeil.form_eq_norm_sq`). -/
theorem shortest_of_rh (hRH : RiemannHypothesis) {N : ℕ} (a : ℕ → ℤ) (h : ∃ n ∈ Icc 1 N, a n ≠ 0) :
    BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ)) := by
  by_cases h2 : ∃ n ∈ Icc 2 N, a n ≠ 0
  · have hg := gram_one_lt
    have hl := lattice_gap hRH a h2
    have hn : (0.0539 : ℝ) ≤ 999 / 1000 * (2 / 45) * (13 / 10) := by norm_num
    linarith
  · push Not at h2
    obtain ⟨n₀, hn₀, han₀⟩ := h
    obtain ⟨h1N, hN0⟩ := Finset.mem_Icc.1 hn₀
    have hN : 1 ≤ N := h1N.trans hN0
    have ha1 : a 1 ≠ 0 := by
      rcases Nat.lt_or_ge 1 n₀ with h1 | h1
      · exact absurd (h2 n₀ (Finset.mem_Icc.2 ⟨h1, hN0⟩)) han₀
      · have : n₀ = 1 := by omega
        rwa [this] at han₀
    rw [form_of_support_one hN a h2]
    have hsq := one_le_sq_of_ne ha1
    have hg := gram_one_pos
    nlinarith

/-- **Under RH the shortest vectors are `±δ_1` alone**: a nonzero integer vector with `Q_N(a) ≤ K_H(1)` has
`a_1 = ±1` and `a_n = 0` for `2 ≤ n ≤ N`. -/
theorem shortest_unique (hRH : RiemannHypothesis) {N : ℕ} (a : ℕ → ℤ) (h : ∃ n ∈ Icc 1 N, a n ≠ 0)
    (hle : BallWeil.form N (fun n => (a n : ℝ)) ≤ BallWeil.gram 1 1) :
    (a 1 = 1 ∨ a 1 = -1) ∧ ∀ n ∈ Icc 2 N, a n = 0 := by
  have h2 : ∀ n ∈ Icc 2 N, a n = 0 := by
    by_contra hc
    push Not at hc
    have hl := lattice_gap hRH a hc
    have hg := gram_one_lt
    have hn : (0.0539 : ℝ) ≤ 999 / 1000 * (2 / 45) * (13 / 10) := by norm_num
    linarith
  refine ⟨?_, h2⟩
  obtain ⟨n₀, hn₀, han₀⟩ := h
  obtain ⟨h1N, hN0⟩ := Finset.mem_Icc.1 hn₀
  have hN : 1 ≤ N := h1N.trans hN0
  have ha1 : a 1 ≠ 0 := by
    rcases Nat.lt_or_ge 1 n₀ with h1 | h1
    · exact absurd (h2 n₀ (Finset.mem_Icc.2 ⟨h1, hN0⟩)) han₀
    · have : n₀ = 1 := by omega
      rwa [this] at han₀
  rw [form_of_support_one hN a h2] at hle
  have hg := gram_one_pos
  have hsq : ((a 1 : ℤ) : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hsqZ : a 1 ^ 2 ≤ 1 := by exact_mod_cast hsq
  have hlo : -1 ≤ a 1 := by nlinarith
  have hhi : a 1 ≤ 1 := by nlinarith
  omega

/-- **RH ⟺ `w_1` is a shortest vector of the orbit lattice**: RH holds if and only if, for every `N`, every nonzero
integer vector `a` has `Q_N(a) ≥ Q_1(δ_1) = K_H(1)`, where `Q_N` is the form of the Gram matrix `√(mn)·K_H(m/n)`
computed from the primes. Nonnegativity at the integer vectors is already RH (`BallWeil.rh_iff_form`). -/
theorem rh_iff_shortest :
    RiemannHypothesis ↔ ∀ (N : ℕ) (a : ℕ → ℤ), (∃ n ∈ Icc 1 N, a n ≠ 0) →
      BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ)) := by
  refine ⟨fun hRH N a h => shortest_of_rh hRH a h, fun h => BallWeil.rh_iff_form.2 fun N x => ?_⟩
  by_cases hx : ∃ n ∈ Icc 1 N, x n ≠ 0
  · exact gram_one_pos.le.trans (h N x hx)
  · push Not at hx
    have h0 : BallWeil.form N (fun n => (x n : ℝ)) = 0 := by
      unfold BallWeil.form
      refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n _ => ?_
      simp only [hx m hm, Int.cast_zero, zero_mul]
    rw [h0]

end PivotSharp
