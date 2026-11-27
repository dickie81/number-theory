import CMFormalBiadd

/-!
# The class `HClass(h)`: coefficients `Σ_i ℓ^{−i}·[hⁱ·g_i]` with `g_i` integral

D1b-7 of the D1b plan. For a series `h` over `ℂ_ℓ` without constant term, `F ∈ HClass(h)` (`HClass`) when every
coefficient of `F` is `F_n = Σ_{i ≤ |n|} ℓ^{−i}·[hⁱ·g_i]_n` for integral series `g_i` (`|n|` the total degree of
the exponent `n`; the terms with `i > |n|` vanish, as `hⁱ` has order `≥ i`). This is the shape of the step theta at
an inert prime in frame coordinates (D1b-8), and the form D2 consumes.

**Small exponentials** (`isIntK_expMv_of_small`). For `ϖ^{ℓ²−1} = ℓ`, `exp(f)` is integral as soon as every
coefficient of `f` has norm at most `‖ϖ‖^{ℓ+1} = ℓ^{−1/(ℓ−1)}`: the `k`-th term has norm at most
`‖ϖ^{(ℓ+1)k}/k!‖ ≤ 1` (`norm_pow_root_div_factorial_le`; Legendre: `(ℓ−1)·v(k!) ≤ k`).

**The class of a Gaussian** (`hClass_exp`). `exp(−(ϖ^{ℓ+1}/ℓ)·h) ∈ HClass(h)`, with the integral constants
`g_i = (−1)ⁱ·ϖ^{(ℓ+1)i}/i!`.

**Integral multiples** (`HClass.mul`). `F ∈ HClass(h)` and `V` integral give `F·V ∈ HClass(h)`, with `g_i·V`.

**Changing `h` modulo `ℓ`** (`HClass.change`). `HClass(h) ⊆ HClass(h + ℓY)` for integral `Y` without constant
term: `ℓ^{−i}hⁱ = Σ_{j ≤ i} C(i,j)·ℓ^{−j}(h + ℓY)ʲ(−Y)^{i−j}`, so `g′_j = Σ_{t ≥ 0} C(j+t,j)·(−Y)ᵗ·g_{j+t}`, a sum
that converges as `Y` has no constant term (built coefficientwise: `chg`, from the partial sums `chgT`).

**Main declarations:** `HClass`, `isIntK_expMv_of_small`, `hClass_exp`, `HClass.mul`, `HClass.change`.
-/

namespace ThetaHClass

open CMFormalInert CMFormalBiadd Finset

noncomputable section

/-! ## Orders and degrees -/

section Order

variable {σ : Type} {K : Type} [CommRing K]

/-- **Degrees along an antidiagonal**: `|a| ≤ |n|` for `a + b = n`. -/
theorem deg_fst_le [DecidableEq σ] {n : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} (hp : p ∈ antidiagonal n) :
    (p.1.sum fun _ e => e) ≤ n.sum fun _ e => e := by
  have h := mem_antidiagonal.1 hp
  change Finsupp.degree p.1 ≤ Finsupp.degree n
  rw [← h, map_add]
  exact Nat.le_add_right _ _

/-- **Degrees along an antidiagonal**: `|b| ≤ |n|` for `a + b = n`. -/
theorem deg_snd_le [DecidableEq σ] {n : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} (hp : p ∈ antidiagonal n) :
    (p.2.sum fun _ e => e) ≤ n.sum fun _ e => e := by
  have h := mem_antidiagonal.1 hp
  change Finsupp.degree p.2 ≤ Finsupp.degree n
  rw [← h, map_add]
  exact Nat.le_add_left _ _

/-- **Vanishing below the order**: `[Xⁿ](Aʲ·(Bᵗ·G)) = 0` for `|n| < j + t` when `A` and `B` have no constant
term. -/
theorem coeff_pow_mul_pow_mul_eq_zero {A B : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (G : MvPowerSeries σ K) {j t : ℕ} {n : σ →₀ ℕ}
    (hn : (n.sum fun _ e => e) < j + t) : MvPowerSeries.coeff n (A ^ j * (B ^ t * G)) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  have h1 := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero j hA
  have h2 := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero t hB
  calc ((Finsupp.degree n : ℕ) : ℕ∞) < ((j + t : ℕ) : ℕ∞) := by exact_mod_cast hn
    _ ≤ (A ^ j).order + ((B ^ t).order + G.order) := by
        push_cast
        exact add_le_add h1 (h2.trans le_self_add)
    _ ≤ (A ^ j).order + (B ^ t * G).order := by gcongr; exact MvPowerSeries.le_order_mul
    _ ≤ (A ^ j * (B ^ t * G)).order := MvPowerSeries.le_order_mul

/-- **Vanishing below the order**: `[Xⁿ](Aʲ·G) = 0` for `|n| < j` when `A` has no constant term. -/
theorem coeff_pow_mul_eq_zero {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (G : MvPowerSeries σ K) {j : ℕ} {n : σ →₀ ℕ} (hn : (n.sum fun _ e => e) < j) :
    MvPowerSeries.coeff n (A ^ j * G) = 0 := by
  have h := coeff_pow_mul_pow_mul_eq_zero hA hA G (j := j) (t := 0) (n := n) (by omega)
  rwa [pow_zero, one_mul] at h

end Order

/-! ## Small coefficients -/

section Norm

variable {σ : Type}

/-- **Powers of a series with small coefficients**: `‖[X^α] fᵏ‖ ≤ rᵏ` when every coefficient of `f` has norm at
most `r`. -/
theorem norm_coeff_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {f : MvPowerSeries σ K} {r : ℝ}
    (hr : 0 ≤ r) (hf : ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ r) (k : ℕ) (α : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff α (f ^ k)‖ ≤ r ^ k := by
  classical
  induction k generalizing α with
  | zero =>
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul, pow_succ]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (ih _) (hf _) (norm_nonneg _) (by positivity)

/-- **A finite sum of integral series is integral.** -/
theorem isIntK_finsum {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} (s : Finset κ)
    {f : κ → MvPowerSeries σ K} (hf : ∀ i ∈ s, IsIntK (f i)) : IsIntK (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => hf i hi n

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`ϖ^{(ℓ+1)k}/k!` is integral** for `ϖ^{ℓ²−1} = ℓ`: its `(ℓ−1)`-th power has norm `ℓ^{−k}·ℓ^{(ℓ−1)·v(k!)}`,
and `(ℓ−1)·v(k!) ≤ k` (Legendre). -/
theorem norm_pow_root_div_factorial_le {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (k : ℕ) :
    ‖ϖ ^ ((ℓ + 1) * k) / (k.factorial : ℂ_[ℓ])‖ ≤ 1 := by
  have h2 := hℓp.out.two_le
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.out.one_le
  have hn : ℓ - 1 ≠ 0 := by omega
  have he : (ℓ + 1) * k * (ℓ - 1) = (ℓ ^ 2 - 1) * k := by
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring, Nat.add_sub_cancel]
    ring
  have hv : (ℓ - 1) * padicValNat ℓ k.factorial ≤ k := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hv' : ((ℓ - 1 : ℕ) : ℤ) * (padicValNat ℓ k.factorial : ℤ) ≤ k := by exact_mod_cast hv
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hn, ← norm_pow, div_pow, ← pow_mul, he, pow_mul, hϖ,
    norm_div, norm_pow, norm_pow, norm_ell_padicC, norm_natCast_padicC _ (Nat.factorial_ne_zero k),
    div_le_one (by positivity), inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
  exact zpow_le_zpow_right₀ hℓ1 (by linarith)

/-- **`exp` of a series with small coefficients is integral**: for `ϖ^{ℓ²−1} = ℓ` and every coefficient of `f` of
norm at most `‖ϖ‖^{ℓ+1}` (valuation `≥ 1/(ℓ−1)`), `exp(f)` is integral. -/
theorem isIntK_expMv_of_small {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) {f : MvPowerSeries σ ℂ_[ℓ]}
    (hf : ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ ‖ϖ‖ ^ (ℓ + 1)) : IsIntK (expMv f) := fun α => by
  rw [coeff_expMv]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  calc ‖MvPowerSeries.coeff α (f ^ k) / (k.factorial : ℂ_[ℓ])‖
      ≤ (‖ϖ‖ ^ (ℓ + 1)) ^ k / ‖(k.factorial : ℂ_[ℓ])‖ := by
        rw [norm_div]
        gcongr
        exact norm_coeff_pow_le (by positivity) hf k α
    _ = ‖ϖ ^ ((ℓ + 1) * k) / (k.factorial : ℂ_[ℓ])‖ := by rw [norm_div, norm_pow, pow_mul]
    _ ≤ 1 := norm_pow_root_div_factorial_le hϖ k

end Norm

/-! ## The class -/

section Class

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **The class `HClass(h)`**: every coefficient of `F` is `Σ_{i ≤ |n|} ℓ^{−i}·[hⁱ·g_i]_n` with `g_i` integral
(`|n|` the total degree of `n`). -/
def HClass (hh F : MvPowerSeries σ ℂ_[ℓ]) : Prop :=
  ∃ g : ℕ → MvPowerSeries σ ℂ_[ℓ], (∀ i, IsIntK (g i)) ∧ ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n F =
    ∑ i ∈ range ((n.sum fun _ e => e) + 1), ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * g i)

/-- **The defining sum may run further**: for `N ≥ |n|` the terms `i ∈ (|n|, N]` vanish (`h` without constant
term). -/
theorem sum_range_eq_of_le {hh : MvPowerSeries σ ℂ_[ℓ]} (h0 : MvPowerSeries.constantCoeff hh = 0)
    (g : ℕ → MvPowerSeries σ ℂ_[ℓ]) {n : σ →₀ ℕ} {N : ℕ} (hN : (n.sum fun _ e => e) ≤ N) :
    ∑ i ∈ range ((n.sum fun _ e => e) + 1), ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * g i) =
      ∑ i ∈ range (N + 1), ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * g i) := by
  refine sum_subset (range_subset_range.2 (by omega)) fun i hi hni => ?_
  rw [mem_range] at hi hni
  rw [coeff_pow_mul_eq_zero h0 _ (by omega), mul_zero]

/-- **The class of a Gaussian**: `exp(−(ϖ^{ℓ+1}/ℓ)·h) ∈ HClass(h)` for `ϖ^{ℓ²−1} = ℓ`, with the integral constants
`g_i = (−1)ⁱ·ϖ^{(ℓ+1)i}/i!` (`norm_pow_root_div_factorial_le`). -/
theorem hClass_exp {ϖ : ℂ_[ℓ]} (hϖ : ϖ ^ (ℓ ^ 2 - 1) = ℓ) (hh : MvPowerSeries σ ℂ_[ℓ]) :
    HClass hh (expMv (-(MvPowerSeries.C (ϖ ^ (ℓ + 1) / ℓ) * hh))) := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hℓp.out.ne_zero
  refine ⟨fun i => MvPowerSeries.C ((-1) ^ i * (ϖ ^ ((ℓ + 1) * i) / (i.factorial : ℂ_[ℓ]))), fun i => ?_,
    fun n => ?_⟩
  · refine isIntK_C ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact norm_pow_root_div_factorial_le hϖ i
  · rw [coeff_expMv]
    refine sum_congr rfl fun k _ => ?_
    rw [← neg_mul, ← map_neg, mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul_C,
      neg_pow, div_pow, ← pow_mul]
    have hf : (k.factorial : ℂ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    field_simp

/-- **Integral multiples stay in the class**: `F ∈ HClass(h)`, `V` integral give `F·V ∈ HClass(h)` (with `g_i·V`;
`h` without constant term, so that `[F]_a` uses only `i ≤ |a| ≤ |n|`). -/
theorem HClass.mul {hh F V : MvPowerSeries σ ℂ_[ℓ]} (hF : HClass hh F) (h0 : MvPowerSeries.constantCoeff hh = 0)
    (hV : IsIntK V) : HClass hh (F * V) := by
  classical
  obtain ⟨g, hg, hFg⟩ := hF
  refine ⟨fun i => g i * V, fun i => (hg i).mul hV, fun n => ?_⟩
  rw [MvPowerSeries.coeff_mul]
  calc ∑ p ∈ antidiagonal n, MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 V
      = ∑ p ∈ antidiagonal n, ∑ i ∈ range ((n.sum fun _ e => e) + 1), ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ *
          (MvPowerSeries.coeff p.1 (hh ^ i * g i) * MvPowerSeries.coeff p.2 V) := by
        refine sum_congr rfl fun p hp => ?_
        rw [hFg, sum_range_eq_of_le h0 g (deg_fst_le hp), sum_mul]
        simp_rw [mul_assoc]
    _ = ∑ i ∈ range ((n.sum fun _ e => e) + 1), ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ *
          MvPowerSeries.coeff n (hh ^ i * (g i * V)) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, MvPowerSeries.coeff_mul, mul_sum]

/-- **The partial sums** `Σ_{t < K} C(j+t, j)·(−Y)ᵗ·g_{j+t}` of the new coefficient series `chg`. -/
def chgT (Y : MvPowerSeries σ ℂ_[ℓ]) (g : ℕ → MvPowerSeries σ ℂ_[ℓ]) (j K : ℕ) : MvPowerSeries σ ℂ_[ℓ] :=
  ∑ t ∈ range K, MvPowerSeries.C (((j + t).choose j : ℕ) : ℂ_[ℓ]) * ((-Y) ^ t * g (j + t))

/-- **The new coefficient series** `g′_j = Σ_{t ≥ 0} C(j+t, j)·(−Y)ᵗ·g_{j+t}` of `HClass.change`, coefficientwise:
at `X^m` the partial sum up to `t = |m|` (the later terms vanish there when `Y` has no constant term). -/
def chg (Y : MvPowerSeries σ ℂ_[ℓ]) (g : ℕ → MvPowerSeries σ ℂ_[ℓ]) (j : ℕ) : MvPowerSeries σ ℂ_[ℓ] :=
  fun m => MvPowerSeries.coeff m (chgT Y g j ((m.sum fun _ e => e) + 1))

/-- **The partial sums are integral.** -/
theorem isIntK_chgT {Y : MvPowerSeries σ ℂ_[ℓ]} (hY : IsIntK Y) {g : ℕ → MvPowerSeries σ ℂ_[ℓ]}
    (hg : ∀ i, IsIntK (g i)) (j K : ℕ) : IsIntK (chgT Y g j K) :=
  isIntK_finsum _ fun _ _ =>
    (isIntK_C (IsUltrametricDist.norm_natCast_le_one ℂ_[ℓ] _)).mul ((hY.neg.pow _).mul (hg _))

/-- **The new coefficient series is integral.** -/
theorem isIntK_chg {Y : MvPowerSeries σ ℂ_[ℓ]} (hY : IsIntK Y) {g : ℕ → MvPowerSeries σ ℂ_[ℓ]}
    (hg : ∀ i, IsIntK (g i)) (j : ℕ) : IsIntK (chg Y g j) :=
  fun m => isIntK_chgT hY hg j _ m

/-- **`chg` agrees with its partial sums** at `X^m` from `K = |m| + 1` on. -/
theorem coeff_chg {Y : MvPowerSeries σ ℂ_[ℓ]} (hY0 : MvPowerSeries.constantCoeff Y = 0)
    (g : ℕ → MvPowerSeries σ ℂ_[ℓ]) (j : ℕ) {m : σ →₀ ℕ} {K : ℕ} (hK : (m.sum fun _ e => e) + 1 ≤ K) :
    MvPowerSeries.coeff m (chg Y g j) = MvPowerSeries.coeff m (chgT Y g j K) := by
  have hY0' : MvPowerSeries.constantCoeff (-Y) = 0 := by rw [map_neg, hY0, neg_zero]
  change MvPowerSeries.coeff m (chgT Y g j ((m.sum fun _ e => e) + 1)) = _
  simp only [chgT, map_sum]
  refine sum_subset (range_subset_range.2 hK) fun t _ ht => ?_
  rw [mem_range] at ht
  rw [MvPowerSeries.coeff_C_mul, coeff_pow_mul_eq_zero hY0' _ (by omega), mul_zero]

/-- **Changing `h` modulo `ℓ`**: `HClass(h) ⊆ HClass(h + ℓY)` for integral `Y` without constant term
(`ℓ^{−i}hⁱ = Σ_{j ≤ i} C(i,j)·ℓ^{−j}(h + ℓY)ʲ(−Y)^{i−j}`; new coefficients `chg`). -/
theorem HClass.change {hh F Y : MvPowerSeries σ ℂ_[ℓ]} (hF : HClass hh F)
    (h0 : MvPowerSeries.constantCoeff hh = 0) (hY : IsIntK Y) (hY0 : MvPowerSeries.constantCoeff Y = 0) :
    HClass (hh + MvPowerSeries.C (ℓ : ℂ_[ℓ]) * Y) F := by
  classical
  obtain ⟨g, hg, hFg⟩ := hF
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hℓp.out.ne_zero
  set h' := hh + MvPowerSeries.C (ℓ : ℂ_[ℓ]) * Y with hh'
  have h'0 : MvPowerSeries.constantCoeff h' = 0 := by
    rw [hh', map_add, map_mul, h0, hY0, mul_zero, add_zero]
  have hY0' : MvPowerSeries.constantCoeff (-Y) = 0 := by rw [map_neg, hY0, neg_zero]
  have hhh : hh = h' + MvPowerSeries.C (ℓ : ℂ_[ℓ]) * (-Y) := by rw [hh']; ring
  refine ⟨chg Y g, isIntK_chg hY hg, fun n => ?_⟩
  set N := (n.sum fun _ e => e) + 1 with hN
  -- the terms of the double sum
  set f : ℕ → ℕ → ℂ_[ℓ] := fun k t => ((ℓ : ℂ_[ℓ]) ^ k)⁻¹ * MvPowerSeries.coeff n
    (h' ^ k * (MvPowerSeries.C (((k + t).choose k : ℕ) : ℂ_[ℓ]) * ((-Y) ^ t * g (k + t)))) with hf
  have hterm : ∀ i, ((ℓ : ℂ_[ℓ]) ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * g i) =
      ∑ k ∈ range (i + 1), f k (i - k) := by
    intro i
    rw [hhh, add_pow, sum_mul, map_sum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨t, rfl⟩ : ∃ t, i = k + t := ⟨i - k, by rw [mem_range] at hk; omega⟩
    rw [Nat.add_sub_cancel_left, hf, mul_pow, ← map_pow, ← map_natCast (MvPowerSeries.C (σ := σ) (R := ℂ_[ℓ])),
      show h' ^ k * (MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ t) * (-Y) ^ t) *
          MvPowerSeries.C (((k + t).choose k : ℕ) : ℂ_[ℓ]) * g (k + t) =
        MvPowerSeries.C ((ℓ : ℂ_[ℓ]) ^ t) * (h' ^ k * (MvPowerSeries.C (((k + t).choose k : ℕ) : ℂ_[ℓ]) *
          ((-Y) ^ t * g (k + t)))) by ring,
      MvPowerSeries.coeff_C_mul, pow_add]
    field_simp
  rw [hFg n, sum_congr rfl fun i _ => hterm i, sum_range_diag_flip]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  -- the inner sum is a partial sum of `chg`, and the partial sum may run up to `N`
  have h1 : ∑ t ∈ range (N - k), f k t =
      ((ℓ : ℂ_[ℓ]) ^ k)⁻¹ * MvPowerSeries.coeff n (h' ^ k * chgT Y g k (N - k)) := by
    rw [hf, chgT, mul_sum, map_sum, mul_sum]
  have h2 : MvPowerSeries.coeff n (h' ^ k * chgT Y g k (N - k)) =
      MvPowerSeries.coeff n (h' ^ k * chgT Y g k N) := by
    simp only [chgT, mul_sum, map_sum]
    refine sum_subset (range_subset_range.2 (Nat.sub_le N k)) fun t _ ht => ?_
    rw [mem_range] at ht
    rw [mul_left_comm, MvPowerSeries.coeff_C_mul, coeff_pow_mul_pow_mul_eq_zero h'0 hY0' _ (by omega), mul_zero]
  have h3 : MvPowerSeries.coeff n (h' ^ k * chgT Y g k N) = MvPowerSeries.coeff n (h' ^ k * chg Y g k) := by
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [coeff_chg hY0 g k (K := N) (by have := deg_snd_le hp; omega)]
  rw [h1, h2, h3]

end Class

end

end ThetaHClass
