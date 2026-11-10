/-
# Tuples of primes as the two variables of the Type II estimate

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `primesLe Y` is the set of primes up to `Y` (`SieveTypeIIU.primesLe`); `BilBd`, `Cross` and `kern`
are `SieveTwoCross`'s.

* `padded T Y`: the `K`-tuples that are primes up to `Y` at the indices of `T` and `1` elsewhere. `sum_padded_mul`:
  for `T` and `T′` disjoint, a sum over `padded (T ∪ T′) Y` is a double sum over `i ∈ padded T Y` and
  `j ∈ padded T′ Y` at the pointwise product `i·j`.
* `pad σ x`: a tuple `x` on `Fin n`, moved to the indices of `R` by `σ : Fin n ≃ R` and extended by `1`.
  `sum_padded_fin`: a sum over `padded R Y` is a sum over the `n`-tuples of primes up to `Y` at `pad σ x`.
  `prod_pad`, `sum_pad`: products and sums of logarithms over `pad σ x` are those over `x`.
* `card_fiber_le`: at most `(K + 1)^K` tuples of `padded T Y` have a given product.
* `bilBd_of_typeII`: **the estimate for two polynomials, as a bound on tuples.** Suppose that for all
  `S_i ⊆ (P_i, 2P_i]` and coefficients `a`, `b`, the sum over `χ ≠ 1` of `|Σ_{S₁} a_mχ(m)||Σ_{S₂} b_mχ(m)|W(χ)` is at
  most `B(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`. Let `X₁`, `X₂` be finite sets with values `nv₁(i) ∈ (P₁, 2P₁]` and
  `nv₂(j) ∈ (P₂, 2P₂]`, at most `D` elements for each value. Then the constant kernel `1` keeps the bound
  `B(D/P₁)^{1/2}(D/P₂)^{1/2}` for the sums `Σ_i f_iχ(nv₁ i)` and `Σ_j g_jχ(nv₂ j)`.
* `box_cross`: with coefficients of absolute value at most `1`, `k` conditions between `i` and `j` and
  `|X₂| < 2^N`, the sum over `χ ≠ 1` of `|Σ_{i,j} f_i g_j kern(i, j) χ(nv₁ i)χ(nv₂ j)|W(χ)` is at most
  `(N + 1)^k D²B`.

The proof of `bilBd_of_typeII`: the polynomial of `X₁` is `Σ_m a_mχ(m)` with `a_m` the sum of `f` over the elements of
value `m`, and `|a_m|² ≤ D·Σ|f_i|²` over those elements. `box_cross` is `BilBd.cmp_list` with `|X_i| ≤ DP_i`.

The file imports `SieveTwoCross.lean` and `SieveUnwTwo.lean`.
-/
import SieveTwoCross
import SieveUnwTwo

open Finset SieveTwoCross SieveTypeIIU

namespace SieveTwoTuples

variable {K : ℕ}

/-! ### Tuples that are `1` off a set of indices -/

/-- The `K`-tuples that are primes up to `Y` at the indices of `T` and `1` elsewhere. -/
def padded (T : Finset (Fin K)) (Y : ℕ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset (fun t => if t ∈ T then primesLe Y else {1})

theorem mem_padded {T : Finset (Fin K)} {Y : ℕ} {z : Fin K → ℕ} :
    z ∈ padded T Y ↔ (∀ t ∈ T, z t ∈ primesLe Y) ∧ ∀ t ∉ T, z t = 1 := by
  rw [padded, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := h t
      rwa [ite_eq_left ht] at this
    · have := h t
      rw [ite_eq_right ht] at this
      simpa using this
  · rintro ⟨h1, h2⟩ t
    by_cases ht : t ∈ T
    · rw [ite_eq_left ht]
      exact h1 t ht
    · rw [ite_eq_right ht]
      simpa using h2 t ht

/-- The entries of a padded tuple are at least `1`. -/
theorem padded_pos {T : Finset (Fin K)} {Y : ℕ} {z : Fin K → ℕ} (hz : z ∈ padded T Y) (t : Fin K) : 1 ≤ z t := by
  by_cases ht : t ∈ T
  · exact ((mem_primesLe.1 ((mem_padded.1 hz).1 t ht)).2).one_lt.le
  · rw [(mem_padded.1 hz).2 t ht]

/-- Padded on every index: the tuples of primes up to `Y`. -/
theorem padded_univ (Y : ℕ) :
    padded (Finset.univ : Finset (Fin K)) Y = Fintype.piFinset (fun _ : Fin K => primesLe Y) := by
  unfold padded
  simp

/-- **A sum over `padded (T ∪ T′) Y`, for `T` and `T′` disjoint, is a double sum** over `i ∈ padded T Y` and
`j ∈ padded T′ Y` at the pointwise product `i·j`. -/
theorem sum_padded_mul {M : Type*} [AddCommMonoid M] {T T' : Finset (Fin K)} (h : Disjoint T T') (Y : ℕ)
    (F : (Fin K → ℕ) → M) :
    ∑ z ∈ padded (T ∪ T') Y, F z = ∑ i ∈ padded T Y, ∑ j ∈ padded T' Y, F (i * j) := by
  have hglue : ∀ z ∈ padded (T ∪ T') Y,
      (fun t => if t ∈ T then z t else 1) * (fun t => if t ∈ T' then z t else 1) = z := by
    intro z hz
    obtain ⟨-, h2⟩ := mem_padded.1 hz
    funext t
    by_cases ht : t ∈ T
    · have : t ∉ T' := Finset.disjoint_left.1 h ht
      simp [ht, this]
    · by_cases ht' : t ∈ T'
      · simp [ht, ht']
      · have := h2 t (by rw [Finset.mem_union, not_or]; exact ⟨ht, ht'⟩)
        simp [ht, ht', this]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun z => (fun t => if t ∈ T then z t else 1, fun t => if t ∈ T' then z t else 1))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨h1, -⟩ := mem_padded.1 hz
    refine Finset.mem_product.2 ⟨mem_padded.2 ⟨fun t ht => ?_, fun t ht => ?_⟩,
      mem_padded.2 ⟨fun t ht => ?_, fun t ht => ?_⟩⟩
    · simp only [ite_eq_left ht]
      exact h1 t (Finset.mem_union_left _ ht)
    · simp only [ite_eq_right ht]
    · simp only [ite_eq_left ht]
      exact h1 t (Finset.mem_union_right _ ht)
    · simp only [ite_eq_right ht]
  · intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hi1, hi2⟩ := mem_padded.1 hi
    obtain ⟨hj1, hj2⟩ := mem_padded.1 hj
    refine mem_padded.2 ⟨fun t ht => ?_, fun t ht => ?_⟩
    · show p.1 t * p.2 t ∈ primesLe Y
      rcases Finset.mem_union.1 ht with ht | ht
      · have : t ∉ T' := Finset.disjoint_left.1 h ht
        rw [hj2 t this, mul_one]
        exact hi1 t ht
      · have : t ∉ T := Finset.disjoint_right.1 h ht
        rw [hi2 t this, one_mul]
        exact hj1 t ht
    · show p.1 t * p.2 t = 1
      rw [Finset.mem_union, not_or] at ht
      rw [hi2 t ht.1, hj2 t ht.2, mul_one]
  · intro z hz
    exact hglue z hz
  · intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨-, hi2⟩ := mem_padded.1 hi
    obtain ⟨-, hj2⟩ := mem_padded.1 hj
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
    · show (if t ∈ T then p.1 t * p.2 t else 1) = p.1 t
      by_cases ht : t ∈ T
      · have : t ∉ T' := Finset.disjoint_left.1 h ht
        rw [ite_eq_left ht, hj2 t this, mul_one]
      · rw [ite_eq_right ht, hi2 t ht]
    · show (if t ∈ T' then p.1 t * p.2 t else 1) = p.2 t
      by_cases ht : t ∈ T'
      · have : t ∉ T := Finset.disjoint_right.1 h ht
        rw [ite_eq_left ht, hi2 t this, one_mul]
      · rw [ite_eq_right ht, hj2 t ht]
  · intro z hz
    simp only [hglue z hz]

/-! ### A tuple on an enumerated set of indices -/

/-- A tuple `x` on `Fin n`, moved to the indices of `R` by `σ : Fin n ≃ R` and extended by `1`. -/
def pad {R : Finset (Fin K)} {n : ℕ} (σ : Fin n ≃ {t // t ∈ R}) (x : Fin n → ℕ) : Fin K → ℕ :=
  fun t => if h : t ∈ R then x (σ.symm ⟨t, h⟩) else 1

variable {R : Finset (Fin K)} {n : ℕ}

theorem pad_apply (σ : Fin n ≃ {t // t ∈ R}) (x : Fin n → ℕ) (i : Fin n) : pad σ x (σ i) = x i := by
  unfold pad
  rw [dite_eq_left (σ i).2]
  simp

theorem pad_of_notMem (σ : Fin n ≃ {t // t ∈ R}) (x : Fin n → ℕ) {t : Fin K} (ht : t ∉ R) : pad σ x t = 1 :=
  dite_eq_right ht

theorem pad_mem_padded (σ : Fin n ≃ {t // t ∈ R}) {x : Fin n → ℕ} {Y : ℕ} (hx : ∀ i, x i ∈ primesLe Y) :
    pad σ x ∈ padded R Y :=
  mem_padded.2 ⟨fun t ht => by unfold pad; rw [dite_eq_left ht]; exact hx _, fun _ ht => pad_of_notMem σ x ht⟩

/-- Reading a padded tuple on `R` along `σ` and padding it again gives it back. -/
theorem pad_read (σ : Fin n ≃ {t // t ∈ R}) {w : Fin K → ℕ} (hw : ∀ t ∉ R, w t = 1) :
    pad σ (fun i => w (σ i)) = w := by
  funext t
  by_cases ht : t ∈ R
  · unfold pad
    rw [dite_eq_left ht]
    simp
  · rw [pad_of_notMem σ _ ht, hw t ht]

/-- **A sum over `padded R Y` is a sum over the `n`-tuples of primes up to `Y`**, at `pad σ x`. -/
theorem sum_padded_fin {M : Type*} [AddCommMonoid M] (σ : Fin n ≃ {t // t ∈ R}) (Y : ℕ)
    (F : (Fin K → ℕ) → M) :
    ∑ w ∈ padded R Y, F w = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => primesLe Y), F (pad σ x) := by
  refine Finset.sum_nbij' (fun w i => w (σ i)) (pad σ) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    exact Fintype.mem_piFinset.2 fun i => (mem_padded.1 hw).1 _ (σ i).2
  · intro x hx
    exact pad_mem_padded σ (Fintype.mem_piFinset.1 hx)
  · intro w hw
    exact pad_read σ (mem_padded.1 hw).2
  · intro x _
    funext i
    exact pad_apply σ x i
  · intro w hw
    simp only [pad_read σ (mem_padded.1 hw).2]

/-- The product of `pad σ x` is the product of `x`. -/
theorem prod_pad (σ : Fin n ≃ {t // t ∈ R}) (x : Fin n → ℕ) : ∏ t, pad σ x t = ∏ i, x i := by
  have h1 : ∏ t, pad σ x t = ∏ t ∈ R, pad σ x t :=
    (Finset.prod_subset (Finset.subset_univ R) fun t _ ht => pad_of_notMem σ x ht).symm
  rw [h1, ← Finset.prod_coe_sort R (fun t => pad σ x t), ← Equiv.prod_comp σ]
  exact Finset.prod_congr rfl fun i _ => pad_apply σ x i

/-- A sum of logarithms over `pad σ x` is the sum over `x`. -/
theorem sum_pad (σ : Fin n ≃ {t // t ∈ R}) (x : Fin n → ℕ) (c : Fin K → ℝ) :
    ∑ t, c t * Real.log (pad σ x t) = ∑ i, c (σ i) * Real.log (x i) := by
  have h1 : ∑ t, c t * Real.log (pad σ x t) = ∑ t ∈ R, c t * Real.log (pad σ x t) :=
    (Finset.sum_subset (Finset.subset_univ R) fun t _ ht => by
      rw [pad_of_notMem σ x ht]; simp).symm
  rw [h1, ← Finset.sum_coe_sort R (fun t => c t * Real.log (pad σ x t)), ← Equiv.sum_comp σ]
  exact Finset.sum_congr rfl fun i _ => by rw [pad_apply σ x i]

/-- **At most `(K + 1)^K` tuples of `padded T Y` have a given product.** -/
theorem card_fiber_le (T : Finset (Fin K)) (Y m : ℕ) :
    ((padded T Y).filter (fun i => ∏ t, i t = m)).card ≤ (K + 1) ^ K := by
  rcases ((padded T Y).filter (fun i => ∏ t, i t = m)).eq_empty_or_nonempty with h0 | ⟨i₀, hi₀⟩
  · rw [h0]
    simp
  have hsub : (padded T Y).filter (fun i => ∏ t, i t = m) ⊆
      Fintype.piFinset (fun _ : Fin K => insert 1 m.primeFactors) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
    refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ T
    · have hp := (mem_primesLe.1 ((mem_padded.1 hi1).1 t ht)).2
      refine Finset.mem_insert_of_mem (Nat.mem_primeFactors.2 ⟨hp, ?_, ?_⟩)
      · rw [← hi2]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
      · rw [← hi2]
        exact (Finset.prod_pos fun s _ => padded_pos hi1 s).ne'
    · rw [(mem_padded.1 hi1).2 t ht]
      exact Finset.mem_insert_self _ _
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi₀
  have hpf : m.primeFactors ⊆ Finset.univ.image i₀ := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
    rw [← hi2] at hpd
    obtain ⟨t, -, ht⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hpd
    refine Finset.mem_image.2 ⟨t, Finset.mem_univ _, ?_⟩
    by_cases htT : t ∈ T
    · exact ((Nat.prime_dvd_prime_iff_eq hpp (mem_primesLe.1 ((mem_padded.1 hi1).1 t htT)).2).1 ht).symm
    · rw [(mem_padded.1 hi1).2 t htT] at ht
      exact absurd (Nat.dvd_one.1 ht) hpp.ne_one
  have hcard : (insert 1 m.primeFactors).card ≤ K + 1 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 := (Finset.card_le_card hpf).trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  calc ((padded T Y).filter (fun i => ∏ t, i t = m)).card
      ≤ (Fintype.piFinset (fun _ : Fin K => insert 1 m.primeFactors)).card := Finset.card_le_card hsub
    _ = (insert 1 m.primeFactors).card ^ K := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (K + 1) ^ K := Nat.pow_le_pow_left hcard K

/-! ### The estimate for two polynomials on tuples -/

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- A polynomial over a finite set `X` with values `nv`, as a polynomial over the values: the coefficient of `m` is
the sum of `f` over the elements of value `m`. -/
theorem dp_image {ι : Type*} (X : Finset ι) (nv : ι → ℕ) (f : ι → ℂ) (χ : DirichletCharacter ℂ q) :
    DirMean.dp (X.image nv) (fun m => (∑ i ∈ X.filter (fun i => nv i = m), f i) * χ m) 0 =
      ∑ i ∈ X, f i * χ ((nv i : ℕ) : ZMod q) := by
  have h0 : DirMean.dp (X.image nv) (fun m => (∑ i ∈ X.filter (fun i => nv i = m), f i) * χ m) 0 =
      ∑ m ∈ X.image nv, (∑ i ∈ X.filter (fun i => nv i = m), f i) * χ m := by
    rw [DirMean.dp]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  rw [h0, ← Finset.sum_fiberwise_of_maps_to (g := nv) (t := X.image nv)
    (fun i hi => Finset.mem_image_of_mem nv hi)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- The mean square of the sums of `f` over the elements of each value is at most `D` times the mean square of `f`,
when each value has at most `D` elements. -/
theorem mean_fiber_le {ι : Type*} (X : Finset ι) (nv : ι → ℕ) (f : ι → ℂ) {D : ℕ}
    (hD : ∀ m, (X.filter (fun i => nv i = m)).card ≤ D) :
    ∑ m ∈ X.image nv, ‖∑ i ∈ X.filter (fun i => nv i = m), f i‖ ^ 2 ≤ D * ∑ i ∈ X, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := nv) (t := X.image nv)
    (fun i hi => Finset.mem_image_of_mem nv hi) (fun i => ‖f i‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hnn : 0 ≤ ∑ i ∈ X.filter (fun i => nv i = m), ‖f i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ‖∑ i ∈ X.filter (fun i => nv i = m), f i‖ ^ 2
      ≤ (∑ i ∈ X.filter (fun i => nv i = m), ‖f i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (X.filter (fun i => nv i = m)).card * ∑ i ∈ X.filter (fun i => nv i = m), ‖f i‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ D * ∑ i ∈ X.filter (fun i => nv i = m), ‖f i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hD m) hnn

/-- The root mean square of the fibre sums. -/
theorem sqrt_fiber_le {ι : Type*} (X : Finset ι) (nv : ι → ℕ) (f : ι → ℂ) {D : ℕ} {P : ℝ} (hP : 0 < P)
    (hD : ∀ m, (X.filter (fun i => nv i = m)).card ≤ D) :
    Real.sqrt ((∑ m ∈ X.image nv, ‖∑ i ∈ X.filter (fun i => nv i = m), f i‖ ^ 2) / P) ≤
      Real.sqrt (D / P) * Real.sqrt (∑ i ∈ X, ‖f i‖ ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (mean_fiber_le X nv f hD) hP.le

/-- A set with values in `(P, 2P]`, at most `D` elements for each value, has at most `DP` elements. -/
theorem card_le_of_fibers {ι : Type*} (X : Finset ι) (nv : ι → ℕ) {P D : ℕ}
    (hX : ∀ i ∈ X, nv i ∈ Finset.Ioc P (2 * P)) (hD : ∀ m, (X.filter (fun i => nv i = m)).card ≤ D) :
    X.card ≤ D * P := by
  have hS : X.image nv ⊆ Finset.Ioc P (2 * P) := fun m hm => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
    exact hX i hi
  rw [Finset.card_eq_sum_card_fiberwise (f := nv) (t := X.image nv)
    (fun i hi => Finset.mem_image_of_mem nv hi)]
  calc ∑ m ∈ X.image nv, (X.filter (fun i => nv i = m)).card
      ≤ ∑ _m ∈ X.image nv, D := Finset.sum_le_sum fun m _ => hD m
    _ = (X.image nv).card * D := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ P * D := Nat.mul_le_mul_right D (by
        have := Finset.card_le_card hS
        rwa [Nat.card_Ioc, show 2 * P - P = P by omega] at this)
    _ = D * P := Nat.mul_comm _ _

/-- The root of the mean square of coefficients of absolute value at most `1` on such a set. -/
theorem sqrt_sum_le {ι : Type*} (X : Finset ι) (nv : ι → ℕ) (f : ι → ℂ) {P D : ℕ}
    (hX : ∀ i ∈ X, nv i ∈ Finset.Ioc P (2 * P)) (hD : ∀ m, (X.filter (fun i => nv i = m)).card ≤ D)
    (hf : ∀ i ∈ X, ‖f i‖ ≤ 1) : Real.sqrt (∑ i ∈ X, ‖f i‖ ^ 2) ≤ Real.sqrt (D * P) := by
  have hc : (X.card : ℝ) ≤ D * P := by exact_mod_cast card_le_of_fibers X nv hX hD
  refine Real.sqrt_le_sqrt (le_trans ?_ hc)
  calc ∑ i ∈ X, ‖f i‖ ^ 2 ≤ ∑ _i ∈ X, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => pow_le_one₀ (norm_nonneg _) (hf i hi)
    _ = X.card := by simp

variable {ι₁ ι₂ : Type*}

open Classical in
/-- **The estimate for two polynomials, as a bound on tuples.** Suppose that for all `S_i ⊆ (P_i, 2P_i]` and all
coefficients `a` and `b`, the sum over `χ ≠ 1` of `|Σ_{S₁} a_mχ(m)||Σ_{S₂} b_mχ(m)|W(χ)` is at most
`B(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}` (`hII`). Let `X₁` and `X₂` be finite sets with values `nv₁(i) ∈ (P₁, 2P₁]` and
`nv₂(j) ∈ (P₂, 2P₂]`, at most `D` elements for each value. Then the constant kernel keeps the bound
`B(D/P₁)^{1/2}(D/P₂)^{1/2}` for the sums `Σ_i f_iχ(nv₁ i)` and `Σ_j g_jχ(nv₂ j)`. -/
theorem bilBd_of_typeII {P₁ P₂ : ℕ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) {W : DirichletCharacter ℂ q → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hII : ∀ (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      ∀ a b : ℕ → ℂ,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a m * χ m) 0‖ * ‖DirMean.dp S₂ (fun m => b m * χ m) 0‖ * W χ ≤
        B * (Real.sqrt ((∑ m ∈ S₁, ‖a m‖ ^ 2) / P₁) * Real.sqrt ((∑ m ∈ S₂, ‖b m‖ ^ 2) / P₂)))
    (X₁ : Finset ι₁) (X₂ : Finset ι₂) (nv₁ : ι₁ → ℕ) (nv₂ : ι₂ → ℕ)
    (h₁ : ∀ i ∈ X₁, nv₁ i ∈ Finset.Ioc P₁ (2 * P₁)) (h₂ : ∀ j ∈ X₂, nv₂ j ∈ Finset.Ioc P₂ (2 * P₂)) (D : ℕ)
    (hD₁ : ∀ m, (X₁.filter (fun i => nv₁ i = m)).card ≤ D)
    (hD₂ : ∀ m, (X₂.filter (fun j => nv₂ j = m)).card ≤ D) :
    BilBd (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)) W
      (fun χ i => χ ((nv₁ i : ℕ) : ZMod q)) (fun χ j => χ ((nv₂ j : ℕ) : ZMod q)) X₁ X₂
      (B * (Real.sqrt (D / P₁) * Real.sqrt (D / P₂))) (fun _ _ => 1) := by
  intro f g
  have hP₁' : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hP₂' : (0 : ℝ) < P₂ := by exact_mod_cast hP₂
  have hS₁ : X₁.image nv₁ ⊆ Finset.Ioc P₁ (2 * P₁) := fun m hm => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
    exact h₁ i hi
  have hS₂ : X₂.image nv₂ ⊆ Finset.Ioc P₂ (2 * P₂) := fun m hm => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
    exact h₂ j hj
  have h := hII (X₁.image nv₁) (X₂.image nv₂) hS₁ hS₂
    (fun m => ∑ i ∈ X₁.filter (fun i => nv₁ i = m), f i) (fun m => ∑ j ∈ X₂.filter (fun j => nv₂ j = m), g j)
  have hprod : ∀ χ : DirichletCharacter ℂ q,
      ∑ i ∈ X₁, ∑ j ∈ X₂, f i * g j * 1 * (χ ((nv₁ i : ℕ) : ZMod q) * χ ((nv₂ j : ℕ) : ZMod q)) =
        DirMean.dp (X₁.image nv₁) (fun m => (∑ i ∈ X₁.filter (fun i => nv₁ i = m), f i) * χ m) 0 *
          DirMean.dp (X₂.image nv₂) (fun m => (∑ j ∈ X₂.filter (fun j => nv₂ j = m), g j) * χ m) 0 := by
    intro χ
    rw [dp_image X₁ nv₁ f χ, dp_image X₂ nv₂ g χ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ i ∈ X₁, ∑ j ∈ X₂, f i * g j * 1 * (χ ((nv₁ i : ℕ) : ZMod q) * χ ((nv₂ j : ℕ) : ZMod q))‖ * W χ
      = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp (X₁.image nv₁) (fun m => (∑ i ∈ X₁.filter (fun i => nv₁ i = m), f i) * χ m) 0‖ *
            ‖DirMean.dp (X₂.image nv₂) (fun m => (∑ j ∈ X₂.filter (fun j => nv₂ j = m), g j) * χ m) 0‖ *
            W χ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hprod χ, norm_mul]
    _ ≤ B * (Real.sqrt ((∑ m ∈ X₁.image nv₁, ‖∑ i ∈ X₁.filter (fun i => nv₁ i = m), f i‖ ^ 2) / P₁) *
          Real.sqrt ((∑ m ∈ X₂.image nv₂, ‖∑ j ∈ X₂.filter (fun j => nv₂ j = m), g j‖ ^ 2) / P₂)) := h
    _ ≤ B * ((Real.sqrt (D / P₁) * Real.sqrt (∑ i ∈ X₁, ‖f i‖ ^ 2)) *
          (Real.sqrt (D / P₂) * Real.sqrt (∑ j ∈ X₂, ‖g j‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (sqrt_fiber_le X₁ nv₁ f hP₁' hD₁) (sqrt_fiber_le X₂ nv₂ g hP₂' hD₂) (Real.sqrt_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hB
    _ = B * (Real.sqrt (D / P₁) * Real.sqrt (D / P₂)) *
          (Real.sqrt (∑ i ∈ X₁, ‖f i‖ ^ 2) * Real.sqrt (∑ j ∈ X₂, ‖g j‖ ^ 2)) := by ring

open Classical in
/-- **The estimate for two polynomials on tuples, with conditions between them.** In the setting of
`bilBd_of_typeII`, with `W ≥ 0`, coefficients `|f_i| ≤ 1` and `|g_j| ≤ 1`, a list `l` of conditions between `i` and
`j` and `|X₂| < 2^N`: the sum over `χ ≠ 1` of `|Σ_{i,j} f_i g_j kern(i, j) χ(nv₁ i)χ(nv₂ j)|W(χ)` is at most
`(N + 1)^{|l|} D²B`. -/
theorem box_cross {P₁ P₂ : ℕ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) {W : DirichletCharacter ℂ q → ℝ} (hW : ∀ χ, 0 ≤ W χ)
    {B : ℝ} (hB : 0 ≤ B)
    (hII : ∀ (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      ∀ a b : ℕ → ℂ,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a m * χ m) 0‖ * ‖DirMean.dp S₂ (fun m => b m * χ m) 0‖ * W χ ≤
        B * (Real.sqrt ((∑ m ∈ S₁, ‖a m‖ ^ 2) / P₁) * Real.sqrt ((∑ m ∈ S₂, ‖b m‖ ^ 2) / P₂)))
    (X₁ : Finset ι₁) (X₂ : Finset ι₂) (nv₁ : ι₁ → ℕ) (nv₂ : ι₂ → ℕ)
    (h₁ : ∀ i ∈ X₁, nv₁ i ∈ Finset.Ioc P₁ (2 * P₁)) (h₂ : ∀ j ∈ X₂, nv₂ j ∈ Finset.Ioc P₂ (2 * P₂)) (D : ℕ)
    (hD₁ : ∀ m, (X₁.filter (fun i => nv₁ i = m)).card ≤ D)
    (hD₂ : ∀ m, (X₂.filter (fun j => nv₂ j = m)).card ≤ D) (l : List (Cross ι₁ ι₂)) {N : ℕ}
    (hN : X₂.card < 2 ^ N) (f : ι₁ → ℂ) (g : ι₂ → ℂ) (hf : ∀ i ∈ X₁, ‖f i‖ ≤ 1) (hg : ∀ j ∈ X₂, ‖g j‖ ≤ 1) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ i ∈ X₁, ∑ j ∈ X₂, f i * g j * kern l i j *
          (χ ((nv₁ i : ℕ) : ZMod q) * χ ((nv₂ j : ℕ) : ZMod q))‖ * W χ ≤
      ((N + 1 : ℕ) : ℝ) ^ l.length * (D : ℝ) ^ 2 * B := by
  have hP₁' : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hP₂' : (0 : ℝ) < P₂ := by exact_mod_cast hP₂
  have hbase := bilBd_of_typeII hP₁ hP₂ hB hII X₁ X₂ nv₁ nv₂ h₁ h₂ D hD₁ hD₂
  have hC : 0 ≤ B * (Real.sqrt (D / P₁) * Real.sqrt (D / P₂)) :=
    mul_nonneg hB (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hk := (hbase.cmp_list (fun χ _ => hW χ) hC hN l) f g
  simp only [one_mul] at hk
  refine hk.trans ?_
  have he : ∀ {P : ℝ}, 0 < P → Real.sqrt (D / P) * Real.sqrt (D * P) = D := by
    intro P hP
    rw [← Real.sqrt_mul (by positivity)]
    have : (D : ℝ) / P * (D * P) = D * D := by field_simp
    rw [this, Real.sqrt_mul_self (Nat.cast_nonneg D)]
  have hpow : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ l.length := pow_nonneg (Nat.cast_nonneg _) _
  calc ((N + 1 : ℕ) : ℝ) ^ l.length * (B * (Real.sqrt (D / P₁) * Real.sqrt (D / P₂))) *
        (Real.sqrt (∑ i ∈ X₁, ‖f i‖ ^ 2) * Real.sqrt (∑ j ∈ X₂, ‖g j‖ ^ 2))
      ≤ ((N + 1 : ℕ) : ℝ) ^ l.length * (B * (Real.sqrt (D / P₁) * Real.sqrt (D / P₂))) *
          (Real.sqrt (D * P₁) * Real.sqrt (D * P₂)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (sqrt_sum_le X₁ nv₁ f h₁ hD₁ hf) (sqrt_sum_le X₂ nv₂ g h₂ hD₂ hg) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _))
          (mul_nonneg hpow hC)
    _ = ((N + 1 : ℕ) : ℝ) ^ l.length * B *
          ((Real.sqrt (D / P₁) * Real.sqrt (D * P₁)) * (Real.sqrt (D / P₂) * Real.sqrt (D * P₂))) := by ring
    _ = ((N + 1 : ℕ) : ℝ) ^ l.length * (D : ℝ) ^ 2 * B := by
        rw [he hP₁', he hP₂']
        ring

end SieveTwoTuples

#print axioms SieveTwoTuples.sum_padded_mul
#print axioms SieveTwoTuples.sum_padded_fin
#print axioms SieveTwoTuples.card_fiber_le
#print axioms SieveTwoTuples.box_cross
