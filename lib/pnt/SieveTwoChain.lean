/-
# Chains of primes with two Type II variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The paper's Lemma 4.6 (`SieveChain.chainTL_bound`, `SieveChainR.chainTR_bound`) evaluates a family of chains of
primes when the product of some of them lies in the window. This file is the same with the Type II estimate in two
variables (`SieveFamilyTwo.TypeIITwoAt`): two disjoint sets of the chain's primes form the two variables, and the
other primes are the rest.

Plain statements. A `GCmp` is a comparison `0 ≤ c + Σ_i e_i log z_i` (or `0 <`) with coefficients in `{−1, 0, 1}`;
`RTg K Y Ω` is the set of `K`-tuples of primes up to `Y` that satisfy the comparisons `Ω` (both are `SieveChain`'s).

* `chain_two`: **families of tuples of primes with two Type II variables.** Assume Proposition 3′ in two variables
  at `L` on a region `Rg` and `0 < L ≤ 5/2`. Fix `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such
  that for `q ≥ q₀` and a unit `a` mod `q`: let `S₁` and `S₂` be disjoint sets of indices that leave at least one
  index out, and let `z` run over the `K`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω`
  with constants at most `Λ₁ log q`. Suppose that every such tuple has its entries at least `q^{e₀}`,
  `P₁ < ∏_{S₁} z ≤ P₁′`, `P₂ < ∏_{S₂} z ≤ P₂′`, `Mlo < ∏_{S₁} z·∏_{S₂} z ≤ Mhi` and `∏ z ≤ 2q^L`, and that `Rg u v`
  holds for `u ∈ [log_q P₁, log_q P₁′]` and `v ∈ [log_q P₂, log_q P₂′]` with `Mlo ≤ 4q^{u+v}` and `q^{u+v} ≤ Mhi`: on
  the rectangle of the two products' exponents, cut by the band of their sum that the rest leaves. Then
  `|Σ_z (1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)`. `chain_two_core` is the same with the band given by
  the comparisons with no prime of the rest; `chain_two` adds the band to the comparisons.

The comparisons are of any kind. One that involves a prime of the rest has it as a pivot, and goes into
`SieveUnwGen.unw_gen` with the pairs of tuples `(z|S₁, z|S₂)` as the polynomial part. One that involves no prime of
the rest is a condition between the two variables, `u(z|S₁) ≤ v(z|S₂)` (or `<`); `SieveTwoCross.BilBd.cmp_list` keeps
the Type II estimate under `J₀` such conditions at the cost of a power of `log q` (`SieveTwoTuples.box_cross`).
A tuple of primes is recovered from its product up to `(K + 1)^K` choices, so the polynomials of tuples are
polynomials of integers with coefficients bounded in mean square.

The proof of `chain_two`: `z = i·j·pad σ x` with `i`, `j` and `x` the parts of `z` on `S₁`, `S₂` and the rest
(`SieveTwoTuples.sum_padded_mul`, `sum_padded_fin`). The blocks are the pairs of dyadic blocks of `(∏i, ∏j)`
(`block_sum`); on a block the sum over the pairs with the conditions is `box_cross`'s, with the rectangle giving
`Rg` at the block's base.

The file imports `SieveTwoTuples.lean` and `SieveP6Chain.lean`.
-/
import SieveTwoTuples
import SieveP6Chain

open Real Finset Filter SieveFamily SieveTypeIIU SieveUnwGen SieveFamilyTwo SieveTwoCross SieveTwoTuples SieveChain
  SieveP6Chain

namespace SieveTwoChain

variable {K : ℕ}

/-! ### A comparison on a product of tuples -/

/-- The linear part of a comparison's form on a tuple: `Σ_t e_t log z_t`. -/
noncomputable def lin (C : GCmp K) (z : Fin K → ℕ) : ℝ := ∑ t, C.e t * Real.log (z t)

theorem form_eq (C : GCmp K) (m : ℕ) (z : Fin K → ℕ) : C.form m z = C.c m + lin C z := rfl

/-- The linear part is additive on pointwise products of tuples with entries at least `1`. -/
theorem lin_mul (C : GCmp K) {u w : Fin K → ℕ} (hu : ∀ t, 1 ≤ u t) (hw : ∀ t, 1 ≤ w t) :
    lin C (u * w) = lin C u + lin C w := by
  unfold lin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ((u t : ℕ) : ℝ) ≠ 0 := by have := hu t; positivity
  have h2 : ((w t : ℕ) : ℝ) ≠ 0 := by have := hw t; positivity
  rw [Pi.mul_apply, Nat.cast_mul, Real.log_mul h1 h2, mul_add]

/-- The linear part vanishes on a tuple that is `1` off `Rs`, for a comparison with no coefficient on `Rs`. -/
theorem lin_eq_zero {Rs : Finset (Fin K)} {C : GCmp K} (hC : ∀ t ∈ Rs, C.e t = 0) {w : Fin K → ℕ}
    (hw : ∀ t ∉ Rs, w t = 1) : lin C w = 0 := by
  unfold lin
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : t ∈ Rs
  · rw [hC t ht, zero_mul]
  · rw [hw t ht]
    simp

variable {Rs : Finset (Fin K)} {n : ℕ}

theorem pad_pos (σ : Fin n ≃ {t // t ∈ Rs}) {x : Fin n → ℕ} (hx : ∀ i, 1 ≤ x i) (t : Fin K) : 1 ≤ pad σ x t := by
  unfold pad
  split_ifs
  · exact hx _
  · exact le_rfl

/-- A comparison at the product of a polynomial part `z` and a rest `x`, as a condition on the two. -/
def PrOf (C : GCmp K) (σ : Fin n ≃ {t // t ∈ Rs}) (z : Fin K → ℕ) (x : Fin n → ℕ) : Prop :=
  if C.strict then 0 < C.c 0 + lin C z + ∑ i, C.e (σ i) * Real.log (x i)
  else 0 ≤ C.c 0 + lin C z + ∑ i, C.e (σ i) * Real.log (x i)

theorem PrOf_iff (C : GCmp K) (σ : Fin n ≃ {t // t ∈ Rs}) {z : Fin K → ℕ} {x : Fin n → ℕ} (hz : ∀ t, 1 ≤ z t)
    (hx : ∀ i, 1 ≤ x i) : PrOf C σ z x ↔ C.holds 0 (z * pad σ x) := by
  unfold PrOf GCmp.holds
  rw [form_eq, lin_mul C hz (pad_pos σ hx), ← add_assoc]
  unfold lin
  rw [sum_pad σ x C.e]

theorem PrOf_spec (C : GCmp K) (σ : Fin n ≃ {t // t ∈ Rs}) (z : Fin K → ℕ) (x : Fin n → ℕ) :
    (0 < C.c 0 + lin C z + ∑ i, C.e (σ i) * Real.log (x i) → PrOf C σ z x) ∧
      (PrOf C σ z x → 0 ≤ C.c 0 + lin C z + ∑ i, C.e (σ i) * Real.log (x i)) := by
  unfold PrOf
  cases C.strict
  · simp only [Bool.false_eq_true, ite_false]
    exact ⟨fun h => h.le, fun h => h⟩
  · simp only [ite_true]
    exact ⟨fun h => h, fun h => h.le⟩

/-- A comparison as a condition between two tuples: `−(c + Σ_t e_t log i_t)` against `Σ_t e_t log j_t`. -/
noncomputable def crossOf (C : GCmp K) : Cross (Fin K → ℕ) (Fin K → ℕ) where
  u := fun i => -(C.c 0 + lin C i)
  v := fun j => lin C j
  strict := C.strict

theorem crossOf_holds (C : GCmp K) {i j : Fin K → ℕ} (hi : ∀ t, 1 ≤ i t) (hj : ∀ t, 1 ≤ j t) :
    (crossOf C).holds i j ↔ C.holds 0 (i * j) := by
  show (if C.strict then -(C.c 0 + lin C i) < lin C j else -(C.c 0 + lin C i) ≤ lin C j) ↔
    (if C.strict then 0 < C.form 0 (i * j) else 0 ≤ C.form 0 (i * j))
  rw [form_eq, lin_mul C hi hj]
  cases C.strict
  · simp only [Bool.false_eq_true, ite_false]
    constructor <;> intro h <;> linarith
  · simp only [ite_true]
    constructor <;> intro h <;> linarith

/-! ### The parts of a tuple -/

/-- On `T`, the product of `i·j` is the product of `i`, for `i` padded on `T` and `j` on a disjoint `T′`. -/
theorem prod_on_left {T T' : Finset (Fin K)} (h : Disjoint T T') {Y : ℕ} {i j : Fin K → ℕ} (hi : i ∈ padded T Y)
    (hj : j ∈ padded T' Y) : ∏ t ∈ T, (i * j) t = ∏ t, i t := by
  have h1 : ∏ t ∈ T, (i * j) t = ∏ t ∈ T, i t := Finset.prod_congr rfl fun t ht => by
    rw [Pi.mul_apply, (mem_padded.1 hj).2 t (Finset.disjoint_left.1 h ht), mul_one]
  rw [h1]
  exact Finset.prod_subset (Finset.subset_univ T) fun t _ ht => (mem_padded.1 hi).2 t ht

/-- On `T′`, the product of `i·j` is the product of `j`. -/
theorem prod_on_right {T T' : Finset (Fin K)} (h : Disjoint T T') {Y : ℕ} {i j : Fin K → ℕ} (hi : i ∈ padded T Y)
    (hj : j ∈ padded T' Y) : ∏ t ∈ T', (i * j) t = ∏ t, j t := by
  have h1 : ∏ t ∈ T', (i * j) t = ∏ t ∈ T', j t := Finset.prod_congr rfl fun t ht => by
    rw [Pi.mul_apply, (mem_padded.1 hi).2 t (Finset.disjoint_right.1 h ht), one_mul]
  rw [h1]
  exact Finset.prod_subset (Finset.subset_univ T') fun t _ ht => (mem_padded.1 hj).2 t ht

/-- On a set disjoint from `Rs`, the product of `z·w` is that of `z`, for `w` equal to `1` off `Rs`. -/
theorem prod_part_mul {T : Finset (Fin K)} (h : Disjoint T Rs) (z : Fin K → ℕ) {w : Fin K → ℕ}
    (hw : ∀ t ∉ Rs, w t = 1) : ∏ t ∈ T, (z * w) t = ∏ t ∈ T, z t :=
  Finset.prod_congr rfl fun t ht => by rw [Pi.mul_apply, hw t (Finset.disjoint_left.1 h ht), mul_one]

open Classical in
/-- The polynomial parts of a family: the tuples padded on `S₁ ∪ S₂` with `P₁ < ∏_{S₁} ≤ min(P₁′, Y)`,
`P₂ < ∏_{S₂} ≤ min(P₂′, Y)` and the comparisons of `lf`. -/
noncomputable def polySet (S₁ S₂ : Finset (Fin K)) (Y P₁ P₁' P₂ P₂' : ℕ) (lf : List (GCmp K)) :
    Finset (Fin K → ℕ) :=
  (padded (S₁ ∪ S₂) Y).filter (fun z =>
    (P₁ < ∏ t ∈ S₁, z t ∧ ∏ t ∈ S₁, z t ≤ P₁' ∧ ∏ t ∈ S₁, z t ≤ Y) ∧
      (P₂ < ∏ t ∈ S₂, z t ∧ ∏ t ∈ S₂, z t ≤ P₂' ∧ ∏ t ∈ S₂, z t ≤ Y) ∧ ∀ C ∈ lf, C.holds 0 z)

/-- The tuples of one variable in a dyadic block: padded on `T`, with `P < ∏ ≤ min(P′, Y)` and the block `b`. -/
def blockSet (T : Finset (Fin K)) (Y P P' b : ℕ) : Finset (Fin K → ℕ) :=
  (padded T Y).filter (fun i =>
    P < ∏ t, i t ∧ ∏ t, i t ≤ P' ∧ ∏ t, i t ≤ Y ∧ Nat.log 2 ((∏ t, i t - 1) / P) = b)

/-- The values of a block are in its dyadic interval. -/
theorem blockSet_val {T : Finset (Fin K)} {Y P P' b : ℕ} (hP : 1 ≤ P) {i : Fin K → ℕ}
    (hi : i ∈ blockSet T Y P P' b) : ∏ t, i t ∈ Finset.Ioc (P * 2 ^ b) (2 * (P * 2 ^ b)) := by
  obtain ⟨-, h1, -, -, h4⟩ := Finset.mem_filter.1 hi
  obtain ⟨h5, h6⟩ := blk_spec hP h1
  rw [h4] at h5 h6
  exact Finset.mem_Ioc.2 ⟨h5, h6⟩

/-- A block has at most `(K + 1)^K` tuples of each value. -/
theorem blockSet_fiber (T : Finset (Fin K)) (Y P P' b m : ℕ) :
    ((blockSet T Y P P' b).filter (fun i => ∏ t, i t = m)).card ≤ (K + 1) ^ K :=
  (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (card_fiber_le T Y m)

open Classical in
/-- **A block of the polynomial parts, as pairs.** A sum over the tuples of `polySet` in the block `(b₁, b₂)` is a
double sum over the blocks of the two variables, at the product `i·j`, restricted by the comparisons of `lf`. -/
theorem block_sum {M : Type*} [AddCommMonoid M] {S₁ S₂ : Finset (Fin K)} (hdisj : Disjoint S₁ S₂)
    (Y P₁ P₁' P₂ P₂' : ℕ) (lf : List (GCmp K)) (b₁ b₂ : ℕ) (G : (Fin K → ℕ) → M) :
    ∑ z ∈ (polySet S₁ S₂ Y P₁ P₁' P₂ P₂' lf).filter (fun z =>
        (Nat.log 2 ((∏ t ∈ S₁, z t - 1) / P₁), Nat.log 2 ((∏ t ∈ S₂, z t - 1) / P₂)) = (b₁, b₂)), G z =
      ∑ i ∈ blockSet S₁ Y P₁ P₁' b₁, ∑ j ∈ blockSet S₂ Y P₂ P₂' b₂,
        if ∀ C ∈ lf, C.holds 0 (i * j) then G (i * j) else 0 := by
  rw [polySet, Finset.filter_filter, Finset.sum_filter, sum_padded_mul hdisj, blockSet, blockSet,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_filter]
  by_cases h1 : P₁ < ∏ t, i t ∧ ∏ t, i t ≤ P₁' ∧ ∏ t, i t ≤ Y ∧ Nat.log 2 ((∏ t, i t - 1) / P₁) = b₁
  · rw [ite_eq_left h1]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [prod_on_left hdisj hi hj, prod_on_right hdisj hi hj]
    by_cases h2 : P₂ < ∏ t, j t ∧ ∏ t, j t ≤ P₂' ∧ ∏ t, j t ≤ Y ∧ Nat.log 2 ((∏ t, j t - 1) / P₂) = b₂
    · by_cases h3 : ∀ C ∈ lf, C.holds 0 (i * j)
      · rw [ite_eq_left ⟨⟨⟨h1.1, h1.2.1, h1.2.2.1⟩, ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩,
          Prod.ext h1.2.2.2 h2.2.2.2⟩, ite_eq_left h2, ite_eq_left h3]
      · rw [ite_eq_right (fun h => h3 h.1.2.2), ite_eq_left h2, ite_eq_right h3]
    · rw [ite_eq_right (fun h => h2 ⟨h.1.2.1.1, h.1.2.1.2.1, h.1.2.1.2.2, (Prod.ext_iff.1 h.2).2⟩), ite_eq_right h2]
  · rw [ite_eq_right h1]
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [prod_on_left hdisj hi hj, prod_on_right hdisj hi hj]
    exact ite_eq_right (fun h => h1 ⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2, (Prod.ext_iff.1 h.2).1⟩)

/-! ### The theorem -/

open Classical in
set_option maxHeartbeats 3200000 in
/-- **Families of tuples of primes with two Type II variables, the product of the two in a band.** `chain_two` with
the band given by the comparisons themselves (`hband`): the comparisons with no prime of the rest force
`Mlo < ∏_{S₁} z·∏_{S₂} z ≤ Mhi` on the tuples with entries at least `1`. -/
theorem chain_two_core {L : ℝ} {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (hL0 : 0 < L) (hL : L ≤ 5 / 2)
    {e₀ : ℝ} (he₀ : 0 < e₀) (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S₁ S₂ : Finset (Fin K)), Disjoint S₁ S₂ → (S₁ ∪ S₂)ᶜ.Nonempty →
      ∀ (Ω : List (GCmp K)), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      ∀ (P₁ P₁' P₂ P₂' Mlo Mhi : ℕ), 1 ≤ P₁ → 1 ≤ P₂ →
      (∀ u v : ℝ, Real.logb q P₁ ≤ u → u ≤ Real.logb q P₁' → Real.logb q P₂ ≤ v → v ≤ Real.logb q P₂' →
        (Mlo : ℝ) ≤ 4 * (q : ℝ) ^ (u + v) → (q : ℝ) ^ (u + v) ≤ Mhi → Rg u v) →
      (∀ z₀ : Fin K → ℕ, (∀ t, 1 ≤ z₀ t) → (∀ C ∈ Ω, (∀ t ∈ (S₁ ∪ S₂)ᶜ, C.e t = 0) → C.holds 0 z₀) →
        Mlo < (∏ t ∈ S₁, z₀ t) * ∏ t ∈ S₂, z₀ t ∧ (∏ t ∈ S₁, z₀ t) * ∏ t ∈ S₂, z₀ t ≤ Mhi) →
      (∀ z : Fin K → ℕ, (∀ t, (z t).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ t, (q : ℝ) ^ e₀ ≤ z t) ∧ P₁ < ∏ t ∈ S₁, z t ∧ ∏ t ∈ S₁, z t ≤ P₁' ∧
          P₂ < ∏ t ∈ S₂, z t ∧ ∏ t ∈ S₂, z t ≤ P₂' ∧ ((∏ t, z t : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ t, z t)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (K + 1) ^ K := ⟨_, rfl⟩
  obtain ⟨cD, hcD⟩ : ∃ c : ℕ, c = Nat.log 2 D + 5 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ (by omega)
  have he₁ : 0 < e₀ / 2 := half_pos he₀
  have hΛ' : 0 ≤ Λ₁ + K * (L + 1) := by positivity
  obtain ⟨δ, hδ, q₁, hq₁⟩ := unw_gen (ι := Fin K → ℕ) (κ := ℕ × ℕ) K J₀ 2 hL0 hL he₁ zero_le_one hΛ'
  obtain ⟨q₂, hq₂⟩ := hII (f0 := SieveDyadic.bump) (SieveDyadic.contDiff_bump (n := ⊤))
    SieveDyadic.bump_support (K + 1) he₁ (η := 1 / 100000) (by norm_num) (by norm_num)
  have hev1 := (tendsto_rpow_atTop he₁).eventually_ge_atTop (2 : ℝ)
  have hev2 := ev_log_pow_le J₀ (show (0 : ℝ) < δ / 4 by positivity)
  have hev3 := (tendsto_rpow_atTop (show (0 : ℝ) < δ / 4 by positivity)).eventually_ge_atTop
    ((D : ℝ) ^ 2 * (cD : ℝ) ^ J₀)
  obtain ⟨q₃, hq₃⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hev1.and (hev2.and hev3)))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) (max q₃ 2), ?_⟩
  intro q _ hq a ha S₁ S₂ hdisj hne Ω hΩlen hΩc P₁ P₁' P₂ P₂' Mlo Mhi hP₁ hP₂ hR hband hreg
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  obtain ⟨hqe, hqlog, hqD⟩ := hq₃ q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq)
  have hq3 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
  have hlogq0 : 0 ≤ Real.log q := by linarith
  have hqL0 : 0 < (q : ℝ) ^ L := Real.rpow_pos_of_pos hq0 _
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) hL0.le
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have h1 : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [h1]
    have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = ⌊2 * (q : ℝ) ^ L⌋₊ := ⟨_, rfl⟩
  rw [← hY]
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.le_floor (by push_cast; linarith)
  have hY0 : Y ≠ 0 := by omega
  have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ L := by rw [hY]; exact Nat.floor_le (by positivity)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.log 2 Y + 1 := ⟨_, rfl⟩
  have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ L) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    refine le_of_mul_le_mul_right ?_ hlog2
    nlinarith [hL, hL0]
  have hMle : (M : ℝ) ≤ 3 + 4 * Real.log q := by rw [hM]; push_cast; linarith
  -- logarithms of the entries
  have hlogY : ∀ m : ℕ, 1 ≤ m → m ≤ Y → Real.log (m : ℝ) ≤ (L + 1) * Real.log q := by
    intro m hm1 hmY
    have h1 : (m : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      have h2 : (m : ℝ) ≤ Y := by exact_mod_cast hmY
      nlinarith
    have h3 := Real.log_le_log (by exact_mod_cast hm1) h1
    rwa [Real.log_rpow hq0] at h3
  -- the rest
  obtain ⟨Rs, hRs⟩ : ∃ Rs : Finset (Fin K), Rs = (S₁ ∪ S₂)ᶜ := ⟨_, rfl⟩
  have hRs_ne : Rs.Nonempty := hRs ▸ hne
  rw [← hRs] at hband
  obtain ⟨n, hn⟩ : ∃ n, Rs.card = n + 1 := ⟨Rs.card - 1, by have := Finset.card_pos.2 hRs_ne; omega⟩
  obtain ⟨σ⟩ : Nonempty (Fin (n + 1) ≃ {t // t ∈ Rs}) :=
    ⟨(Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hn])).symm⟩
  have hnK : n + 1 ≤ K := by
    have := Finset.card_le_univ Rs
    rw [Fintype.card_fin] at this
    omega
  have hSR : Disjoint (S₁ ∪ S₂) Rs := by rw [hRs]; exact disjoint_compl_right
  have hSRu : (S₁ ∪ S₂) ∪ Rs = Finset.univ := by rw [hRs]; exact Finset.union_compl _
  have hS₁R : Disjoint S₁ Rs := hSR.mono_left Finset.subset_union_left
  have hS₂R : Disjoint S₂ Rs := hSR.mono_left Finset.subset_union_right
  have hnotRs : ∀ t, t ∉ Rs → t ∈ S₁ ∪ S₂ := fun t ht => by
    rw [hRs, Finset.mem_compl, not_not] at ht
    exact ht
  have hinRs : ∀ t, t ∈ Rs → t ∉ S₁ ∪ S₂ := fun t ht => by
    rw [hRs, Finset.mem_compl] at ht
    exact ht
  -- the comparisons with a prime of the rest, and those without
  obtain ⟨lp, hlp⟩ : ∃ l : List (GCmp K), l = Ω.filter (fun C => decide (∃ t ∈ Rs, C.e t ≠ 0)) := ⟨_, rfl⟩
  obtain ⟨lf, hlf⟩ : ∃ l : List (GCmp K), l = Ω.filter (fun C => decide (∀ t ∈ Rs, C.e t = 0)) := ⟨_, rfl⟩
  have hmem_lp : ∀ C, C ∈ lp ↔ C ∈ Ω ∧ ∃ t ∈ Rs, C.e t ≠ 0 := fun C => by
    rw [hlp, List.mem_filter, decide_eq_true_eq]
  have hmem_lf : ∀ C, C ∈ lf ↔ C ∈ Ω ∧ ∀ t ∈ Rs, C.e t = 0 := fun C => by
    rw [hlf, List.mem_filter, decide_eq_true_eq]
  have hlp_len : lp.length ≤ J₀ := by rw [hlp]; exact (List.length_filter_le _ _).trans hΩlen
  have hlf_len : lf.length ≤ J₀ := by rw [hlf]; exact (List.length_filter_le _ _).trans hΩlen
  have hex : ∀ j : Fin lp.length, ∃ i : Fin (n + 1), (lp.get j).e (σ i) = 1 ∨ (lp.get j).e (σ i) = -1 := by
    intro j
    obtain ⟨-, t, ht, hne'⟩ := (hmem_lp _).1 (List.get_mem lp j)
    refine ⟨σ.symm ⟨t, ht⟩, ?_⟩
    rw [Equiv.apply_symm_apply]
    rcases (lp.get j).he t with h | h | h
    · exact Or.inr h
    · exact absurd h hne'
    · exact Or.inl h
  choose piv hpiv using hex
  -- a comparison with no prime of the rest, at a product with the rest
  have hfree : ∀ C : GCmp K, (∀ t ∈ Rs, C.e t = 0) → ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ),
      (∀ t, 1 ≤ z t) → (∀ i, 1 ≤ x i) → (C.holds 0 (z * pad σ x) ↔ C.holds 0 z) := by
    intro C hC z x hz1 hx1
    unfold GCmp.holds
    rw [form_eq, form_eq, lin_mul C hz1 (pad_pos σ hx1),
      lin_eq_zero hC (fun t ht => pad_of_notMem σ x ht), add_zero]
  have hΩiff : ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ), (∀ t, 1 ≤ z t) → (∀ i, 1 ≤ x i) →
      ((∀ C ∈ Ω, C.holds 0 (z * pad σ x)) ↔
        (∀ C ∈ lf, C.holds 0 z) ∧ ∀ j : Fin lp.length, PrOf (lp.get j) σ z x) := by
    intro z x hz1 hx1
    constructor
    · intro h
      refine ⟨fun C hC => ?_, fun j => ?_⟩
      · obtain ⟨hCΩ, hCf⟩ := (hmem_lf C).1 hC
        exact (hfree C hCf z x hz1 hx1).1 (h C hCΩ)
      · exact (PrOf_iff _ σ hz1 hx1).2 (h _ ((hmem_lp _).1 (List.get_mem lp j)).1)
    · rintro ⟨h1, h2⟩ C hC
      by_cases hCp : ∃ t ∈ Rs, C.e t ≠ 0
      · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 ((hmem_lp C).2 ⟨hC, hCp⟩)
        exact (PrOf_iff _ σ hz1 hx1).1 (h2 j)
      · have hCf : ∀ t ∈ Rs, C.e t = 0 := fun t ht => by
          by_contra hne'
          exact hCp ⟨t, ht, hne'⟩
        exact (hfree C hCf z x hz1 hx1).2 (h1 C ((hmem_lf C).2 ⟨hC, hCf⟩))
  -- the polynomial parts
  obtain ⟨Xs, hXs⟩ : ∃ X : Finset (Fin K → ℕ), X = polySet S₁ S₂ Y P₁ P₁' P₂ P₂' lf := ⟨_, rfl⟩
  have hmemXs : ∀ z, z ∈ Xs ↔ z ∈ padded (S₁ ∪ S₂) Y ∧
      ((P₁ < ∏ t ∈ S₁, z t ∧ ∏ t ∈ S₁, z t ≤ P₁' ∧ ∏ t ∈ S₁, z t ≤ Y) ∧
        (P₂ < ∏ t ∈ S₂, z t ∧ ∏ t ∈ S₂, z t ≤ P₂' ∧ ∏ t ∈ S₂, z t ≤ Y) ∧ ∀ C ∈ lf, C.holds 0 z) := fun z => by
    rw [hXs, polySet, Finset.mem_filter]
  have hprodS : ∀ z ∈ padded (S₁ ∪ S₂) Y, ∏ t, z t = (∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t := by
    intro z hz
    rw [← Finset.prod_union hdisj]
    exact (Finset.prod_subset (Finset.subset_univ _) fun t _ ht => (mem_padded.1 hz).2 t ht).symm
  -- the full tuple of a polynomial part and a rest
  have hprime : ∀ z ∈ padded (S₁ ∪ S₂) Y, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) →
      ∀ t, ((z * pad σ x) t).Prime := by
    intro z hzp x hx t
    by_cases ht : t ∈ Rs
    · have hzt : z t = 1 := (mem_padded.1 hzp).2 t (hinRs t ht)
      rw [Pi.mul_apply, hzt, one_mul]
      unfold pad
      rw [dite_eq_left ht]
      exact hx _
    · rw [Pi.mul_apply, pad_of_notMem σ x ht, mul_one]
      exact (mem_primesLe.1 ((mem_padded.1 hzp).1 t (hnotRs t ht))).2
  have hprodw : ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ), ∏ t, (z * pad σ x) t = (∏ t, z t) * ∏ i, x i := by
    intro z x
    rw [← prod_pad σ x, ← Finset.prod_mul_distrib]
    rfl
  -- the dyadic blocks
  have hblk : ∀ {P m : ℕ}, 1 ≤ P → P < m → m ≤ Y → Nat.log 2 ((m - 1) / P) ∈ Finset.range M := by
    intro P m hP1 hPm hmY
    obtain ⟨h1, -⟩ := blk_spec hP1 hPm
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact le_trans (Nat.le_mul_of_pos_left _ hP1) (le_trans h1.le hmY)
  have hpos : ∀ (P b : ℕ), 1 ≤ P → 0 < P * 2 ^ b := fun P b hP1 => Nat.mul_pos hP1 (by positivity)
  have hcardB : ∀ (T : Finset (Fin K)) (P P' b : ℕ), 1 ≤ P → (blockSet T Y P P' b).card ≤ D * (P * 2 ^ b) :=
    fun T P P' b hP1 => card_le_of_fibers (blockSet T Y P P' b) (fun i => ∏ t, i t)
      (fun i hi => blockSet_val hP1 hi) (fun m => hD ▸ blockSet_fiber T Y P P' b m)
  -- the constant
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.log 2 (D * Y) + 1 := ⟨_, rfl⟩
  have hDY : D * Y < 2 ^ N := by rw [hN]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  obtain ⟨A₀, hA₀⟩ : ∃ A : ℝ, A = ((N + 1 : ℕ) : ℝ) ^ J₀ * (D : ℝ) ^ 2 := ⟨_, rfl⟩
  have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hA₀nn : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hA₀D : (D : ℝ) ^ 2 ≤ A₀ := by
    rw [hA₀]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hN1)
  have hA₀le : A₀ ≤ (q : ℝ) ^ (δ / 2) := by
    have h1 : Nat.log 2 (D * Y) < Nat.log 2 D + Nat.log 2 Y + 2 := by
      refine Nat.log_lt_of_lt_pow (Nat.mul_ne_zero (by omega) hY0) ?_
      have hd := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) D
      have hy := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) Y
      calc D * Y < 2 ^ (Nat.log 2 D).succ * 2 ^ (Nat.log 2 Y).succ := Nat.mul_lt_mul'' hd hy
        _ = 2 ^ (Nat.log 2 D + Nat.log 2 Y + 2) := by rw [← pow_add]; congr 1; omega
    have h2 : ((N + 1 : ℕ) : ℝ) ≤ (cD : ℝ) * (3 + 4 * Real.log q) := by
      have h3 : N + 1 ≤ Nat.log 2 D + Nat.log 2 Y + 3 := by rw [hN]; omega
      have h4 : ((N + 1 : ℕ) : ℝ) ≤ (Nat.log 2 D : ℝ) + (Nat.log 2 Y : ℝ) + 3 := by exact_mod_cast h3
      have h5 : (cD : ℝ) = (Nat.log 2 D : ℝ) + 5 := by rw [hcD]; push_cast; ring
      have h6 : (0 : ℝ) ≤ (Nat.log 2 D : ℝ) := Nat.cast_nonneg _
      rw [h5]
      nlinarith
    have h7 : (0 : ℝ) ≤ (cD : ℝ) * (3 + 4 * Real.log q) := by positivity
    calc A₀ = ((N + 1 : ℕ) : ℝ) ^ J₀ * (D : ℝ) ^ 2 := hA₀
      _ ≤ ((cD : ℝ) * (3 + 4 * Real.log q)) ^ J₀ * (D : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 _) (by positivity)
      _ = ((D : ℝ) ^ 2 * (cD : ℝ) ^ J₀) * (3 + 4 * Real.log q) ^ J₀ := by rw [mul_pow]; ring
      _ ≤ (q : ℝ) ^ (δ / 4) * (q : ℝ) ^ (δ / 4) :=
          mul_le_mul hqD hqlog (by positivity) (by positivity)
      _ = (q : ℝ) ^ (δ / 2) := by rw [← Real.rpow_add hq0]; congr 1; ring
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (2 * π * Complex.I * (r : ℂ))‖ = 1 := fun r => by
    have : 2 * π * Complex.I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  -- the family as a family with an abstract polynomial part
  have hkey : ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
      (fun mx => (∏ t, mx.1 t) * ∏ i, mx.2 i)
      (fun mx => (1 : ℂ) *
        ∏ j : Fin lp.length, ((if PrOf (lp.get j) σ mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ)) := by
    rw [hY]
    rw [hY] at hmemXs hprodS hprime hblk hcardB hDY hlogY
    refine hq₁ q hq1 a ha Xs (fun z => ∏ t, z t) (fun _ => (1 : ℂ)) A₀ hA₀nn
      (fun z => (Nat.log 2 ((∏ t ∈ S₁, z t - 1) / P₁), Nat.log 2 ((∏ t ∈ S₂, z t - 1) / P₂)))
      (Finset.range M ×ˢ Finset.range M)
      (fun b => ((P₁ * 2 ^ b.1 : ℕ) : ℝ) * ((P₂ * 2 ^ b.2 : ℕ) : ℝ)) ?_ ?_ ?_ ?_ ?_ n hnK hlp_len
      (fun j z => (lp.get j).c 0 + lin (lp.get j) z) (fun j i => (lp.get j).e (σ i))
      (fun j z x => PrOf (lp.get j) σ z x) ?_ (fun j z x => PrOf_spec (lp.get j) σ z x) ?_ piv hpiv ?_ ?_
    · -- the labels
      intro z hz
      obtain ⟨-, ⟨h1, -, h1Y⟩, ⟨h2, -, h2Y⟩, -⟩ := (hmemXs z).1 hz
      exact Finset.mem_product.2 ⟨hblk hP₁ h1 h1Y, hblk hP₂ h2 h2Y⟩
    · -- their number
      rw [Finset.card_product, Finset.card_range]
      push_cast
      calc (M : ℝ) * M ≤ (3 + 4 * Real.log q) * (3 + 4 * Real.log q) :=
            mul_le_mul hMle hMle (Nat.cast_nonneg _) (by linarith)
        _ = (3 + 4 * Real.log q) ^ 2 := by ring
    · -- the sizes are positive
      intro b _
      have h1 : (0 : ℝ) < ((P₁ * 2 ^ b.1 : ℕ) : ℝ) := by exact_mod_cast hpos P₁ b.1 hP₁
      have h2 : (0 : ℝ) < ((P₂ * 2 ^ b.2 : ℕ) : ℝ) := by exact_mod_cast hpos P₂ b.2 hP₂
      exact mul_pos h1 h2
    · -- a tuple is above the size of its block
      intro z hz
      obtain ⟨hzp, ⟨h1, -, -⟩, ⟨h2, -, -⟩, -⟩ := (hmemXs z).1 hz
      obtain ⟨h1', -⟩ := blk_spec hP₁ h1
      obtain ⟨h2', -⟩ := blk_spec hP₂ h2
      have h3 := Nat.mul_lt_mul'' h1' h2'
      rw [← hprodS z hzp] at h3
      exact_mod_cast h3
    · -- the number of tuples of a block
      rintro ⟨b₁, b₂⟩ -
      have h1 : ∑ z ∈ Xs.filter (fun z => (Nat.log 2 ((∏ t ∈ S₁, z t - 1) / P₁),
          Nat.log 2 ((∏ t ∈ S₂, z t - 1) / P₂)) = (b₁, b₂)), ‖(1 : ℂ)‖ =
          ∑ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁, ∑ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂,
            if ∀ C ∈ lf, C.holds 0 (i * j) then ‖(1 : ℂ)‖ else 0 := by
        rw [hXs, hY]
        exact block_sum hdisj _ P₁ P₁' P₂ P₂' lf b₁ b₂ (fun _ => ‖(1 : ℂ)‖)
      rw [h1]
      have hc₁ : ((blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁).card : ℝ) ≤ (D : ℝ) * ((P₁ * 2 ^ b₁ : ℕ) : ℝ) := by
        exact_mod_cast hcardB S₁ P₁ P₁' b₁ hP₁
      have hc₂ : ((blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂).card : ℝ) ≤ (D : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ) := by
        exact_mod_cast hcardB S₂ P₂ P₂' b₂ hP₂
      have hp₁ : (0 : ℝ) ≤ ((P₁ * 2 ^ b₁ : ℕ) : ℝ) := Nat.cast_nonneg _
      have hp₂ : (0 : ℝ) ≤ ((P₂ * 2 ^ b₂ : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ∑ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁, ∑ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂,
            (if ∀ C ∈ lf, C.holds 0 (i * j) then ‖(1 : ℂ)‖ else 0)
          ≤ ∑ _i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁,
              ∑ _j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp
        _ = ((blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁).card : ℝ) *
              ((blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂).card : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ((D : ℝ) * ((P₁ * 2 ^ b₁ : ℕ) : ℝ)) * ((D : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ)) :=
            mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _) (by positivity)
        _ = ((P₁ * 2 ^ b₁ : ℕ) : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ) * (D : ℝ) ^ 2 := by ring
        _ ≤ ((P₁ * 2 ^ b₁ : ℕ) : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ) * A₀ :=
            mul_le_mul_of_nonneg_left hA₀D (mul_nonneg hp₁ hp₂)
    · -- the coefficients of the forms
      intro j i
      rcases (lp.get j).he (σ i) with h | h | h <;> rw [h] <;> norm_num
    · -- the polynomial parts of the forms
      intro j z hz
      have h1 := hΩc _ ((hmem_lp _).1 (List.get_mem lp j)).1
      obtain ⟨hzp, -⟩ := (hmemXs z).1 hz
      have h2 : lin (lp.get j) z ≤ K * ((L + 1) * Real.log q) := by
        unfold lin
        calc ∑ t, (lp.get j).e t * Real.log (z t) ≤ ∑ _t : Fin K, (L + 1) * Real.log q := by
              refine Finset.sum_le_sum fun t _ => ?_
              have hz1 : (1 : ℝ) ≤ z t := by exact_mod_cast padded_pos hzp t
              have hlz0 : 0 ≤ Real.log (z t) := Real.log_nonneg hz1
              have hzY : z t ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by
                by_cases ht : t ∈ S₁ ∪ S₂
                · exact (mem_primesLe.1 ((mem_padded.1 hzp).1 t ht)).1
                · rw [(mem_padded.1 hzp).2 t ht]
                  exact hY ▸ hY1
              have hlz := hlogY (z t) (padded_pos hzp t) hzY
              have hLq : 0 ≤ (L + 1) * Real.log q := by positivity
              rcases (lp.get j).he t with h | h | h <;> rw [h] <;> nlinarith
          _ = K * ((L + 1) * Real.log q) := by simp
      show (lp.get j).c 0 + lin (lp.get j) z ≤ (Λ₁ + K * (L + 1)) * Real.log q
      nlinarith
    · -- the primes of the rest and the product
      intro z hz x hx hall
      obtain ⟨hzp, -, -, hzf⟩ := (hmemXs z).1 hz
      have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      have hwΩ : ∀ C ∈ Ω, C.holds 0 (z * pad σ x) := (hΩiff z x hz1 hx1).2 ⟨hzf, hall⟩
      obtain ⟨hge, -, -, -, -, hprod⟩ := hreg _ (hprime z hzp x hx) hwΩ
      refine ⟨fun i => ?_, ?_⟩
      · have h1 := hge (σ i)
        have hzt : z (σ i) = 1 := (mem_padded.1 hzp).2 _ (hinRs _ (σ i).2)
        rw [Pi.mul_apply, hzt, one_mul, pad_apply] at h1
        linarith
      · rw [hprodw z x] at hprod
        exact_mod_cast hprod
    · -- the estimate on a block
      rintro ⟨b₁, b₂⟩ - Q hQ hQP c' hc' ξ κ' hh hhh
      have hc1 : c' = fun _ => (1 : ℂ) := by
        rcases hc' with rfl | rfl
        · rfl
        · funext z
          simp
      rw [hc1]
      have hbound0 : (0 : ℝ) ≤ A₀ * (q : ℝ) ^ (L - 1 / 50000) :=
        mul_nonneg hA₀nn (Real.rpow_nonneg hq0.le _)
      -- the conditions between the two variables, on a block
      have hkern : ∀ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁, ∀ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂,
          kern (lf.map crossOf) i j = if ∀ C ∈ lf, C.holds 0 (i * j) then 1 else 0 := by
        intro i hi j hj
        have hi1 : ∀ t, 1 ≤ i t := padded_pos (Finset.mem_filter.1 hi).1
        have hj1 : ∀ t, 1 ≤ j t := padded_pos (Finset.mem_filter.1 hj).1
        have hiff : (∀ c ∈ lf.map crossOf, c.holds i j) ↔ ∀ C ∈ lf, C.holds 0 (i * j) := by
          rw [List.forall_mem_map]
          exact forall₂_congr fun C _ => crossOf_holds C hi1 hj1
        rw [kern_eq]
        by_cases h : ∀ C ∈ lf, C.holds 0 (i * j)
        · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h'))]
      -- the block's sum as a sum over the pairs
      have hsum : ∀ χ : DirichletCharacter ℂ q,
          ∑ z ∈ Xs.filter (fun z => (Nat.log 2 ((∏ t ∈ S₁, z t - 1) / P₁),
              Nat.log 2 ((∏ t ∈ S₂, z t - 1) / P₂)) = (b₁, b₂)),
            (1 : ℂ) * Complex.exp (2 * π * Complex.I *
              ((κ' + ∑ j : Fin lp.length, ξ j * ((lp.get j).c 0 + lin (lp.get j) z) : ℝ) : ℂ)) *
              χ ((∏ t, z t : ℕ) : ZMod q) =
          ∑ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁, ∑ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂,
            Complex.exp (2 * π * Complex.I *
              ((κ' + ∑ j' : Fin lp.length, ξ j' * ((lp.get j').c 0 + lin (lp.get j') i) : ℝ) : ℂ)) *
            Complex.exp (2 * π * Complex.I * ((∑ j' : Fin lp.length, ξ j' * lin (lp.get j') j : ℝ) : ℂ)) *
            kern (lf.map crossOf) i j *
            (χ ((∏ t, i t : ℕ) : ZMod q) * χ ((∏ t, j t : ℕ) : ZMod q)) := by
        intro χ
        rw [hXs, hY, block_sum hdisj _ P₁ P₁' P₂ P₂' lf b₁ b₂]
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        have hi1 : ∀ t, 1 ≤ i t := padded_pos (Finset.mem_filter.1 hi).1
        have hj1 : ∀ t, 1 ≤ j t := padded_pos (Finset.mem_filter.1 hj).1
        rw [hkern i hi j hj]
        by_cases h : ∀ C ∈ lf, C.holds 0 (i * j)
        · rw [ite_eq_left h, ite_eq_left h, mul_one, one_mul]
          have hsplit : (κ' + ∑ j' : Fin lp.length, ξ j' * ((lp.get j').c 0 + lin (lp.get j') (i * j)) : ℝ) =
              (κ' + ∑ j' : Fin lp.length, ξ j' * ((lp.get j').c 0 + lin (lp.get j') i)) +
                ∑ j' : Fin lp.length, ξ j' * lin (lp.get j') j := by
            rw [add_assoc, ← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [lin_mul _ hi1 hj1]
            ring
          rw [hsplit, Complex.ofReal_add, mul_add, Complex.exp_add]
          have hpr : ((∏ t, (i * j) t : ℕ) : ZMod q) = ((∏ t, i t : ℕ) : ZMod q) * ((∏ t, j t : ℕ) : ZMod q) := by
            rw [← Nat.cast_mul, ← Finset.prod_mul_distrib]
            rfl
          rw [hpr, map_mul]
        · rw [ite_eq_right h, ite_eq_right h, mul_zero, zero_mul]
      simp only [hsum]
      by_cases hex : ∃ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁,
          ∃ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂, ∀ C ∈ lf, C.holds 0 (i * j)
      swap
      · -- no pair of the block satisfies the conditions
        have hz : ∀ χ : DirichletCharacter ℂ q,
            ∑ i ∈ blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁, ∑ j ∈ blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂,
              Complex.exp (2 * π * Complex.I *
                ((κ' + ∑ j' : Fin lp.length, ξ j' * ((lp.get j').c 0 + lin (lp.get j') i) : ℝ) : ℂ)) *
              Complex.exp (2 * π * Complex.I * ((∑ j' : Fin lp.length, ξ j' * lin (lp.get j') j : ℝ) : ℂ)) *
              kern (lf.map crossOf) i j *
              (χ ((∏ t, i t : ℕ) : ZMod q) * χ ((∏ t, j t : ℕ) : ZMod q)) = 0 := fun χ =>
          Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => by
            rw [hkern i hi j hj, ite_eq_right (fun h => hex ⟨i, hi, j, hj, h⟩), mul_zero, zero_mul]
        simp only [hz, norm_zero, zero_mul, Finset.sum_const_zero]
        exact hbound0
      obtain ⟨i₀, hi₀, j₀, hj₀, hlf₀⟩ := hex
      -- the base of the block is in the rectangle
      have hbase : ∀ {T : Finset (Fin K)} {P P' b : ℕ} {i : Fin K → ℕ}, 1 ≤ P →
          i ∈ blockSet T ⌊2 * (q : ℝ) ^ L⌋₊ P P' b →
          Real.logb q P ≤ Real.logb q ((P * 2 ^ b : ℕ) : ℝ) ∧ Real.logb q ((P * 2 ^ b : ℕ) : ℝ) ≤ Real.logb q P' := by
        intro T P P' b i hP1 hi
        have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
        have hPb0 : (0 : ℝ) < ((P * 2 ^ b : ℕ) : ℝ) := by exact_mod_cast hpos P b hP1
        have h1 : (P : ℝ) ≤ ((P * 2 ^ b : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_right P (show 0 < 2 ^ b by positivity)
        have h2 : ((P * 2 ^ b : ℕ) : ℝ) ≤ P' := by
          have hlt := (Finset.mem_Ioc.1 (blockSet_val hP1 hi)).1
          have hle := (Finset.mem_filter.1 hi).2.2.1
          exact_mod_cast hlt.le.trans hle
        exact ⟨Real.logb_le_logb_of_le hq1' hP0 h1, Real.logb_le_logb_of_le hq1' hPb0 h2⟩
      obtain ⟨hu₁, hu₂⟩ := hbase hP₁ hi₀
      obtain ⟨hv₁, hv₂⟩ := hbase hP₂ hj₀
      -- the base of the block is in the band
      have hi₀p := (Finset.mem_filter.1 hi₀).1
      have hj₀p := (Finset.mem_filter.1 hj₀).1
      obtain ⟨hbl, hbh⟩ := hband (i₀ * j₀) (fun t => Nat.mul_pos (padded_pos hi₀p t) (padded_pos hj₀p t))
        (fun C hC hCf => hlf₀ C ((hmem_lf C).2 ⟨hC, hCf⟩))
      rw [prod_on_left hdisj hi₀p hj₀p, prod_on_right hdisj hi₀p hj₀p] at hbl hbh
      have hval₁ := Finset.mem_Ioc.1 (blockSet_val hP₁ hi₀)
      have hval₂ := Finset.mem_Ioc.1 (blockSet_val hP₂ hj₀)
      have hpow : (q : ℝ) ^ (Real.logb q ((P₁ * 2 ^ b₁ : ℕ) : ℝ) + Real.logb q ((P₂ * 2 ^ b₂ : ℕ) : ℝ)) =
          ((P₁ * 2 ^ b₁ : ℕ) : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ) := by
        rw [Real.rpow_add hq0, Real.rpow_logb hq0 hq1'.ne' (by exact_mod_cast hpos P₁ b₁ hP₁),
          Real.rpow_logb hq0 hq1'.ne' (by exact_mod_cast hpos P₂ b₂ hP₂)]
      have hlo4 : Mlo ≤ 4 * ((P₁ * 2 ^ b₁) * (P₂ * 2 ^ b₂)) :=
        calc Mlo ≤ (∏ t, i₀ t) * ∏ t, j₀ t := hbl.le
          _ ≤ (2 * (P₁ * 2 ^ b₁)) * (2 * (P₂ * 2 ^ b₂)) := Nat.mul_le_mul hval₁.2 hval₂.2
          _ = 4 * ((P₁ * 2 ^ b₁) * (P₂ * 2 ^ b₂)) := by ring
      have hhi4 : (P₁ * 2 ^ b₁) * (P₂ * 2 ^ b₂) ≤ Mhi :=
        (Nat.mul_le_mul hval₁.1.le hval₂.1.le).trans hbh
      have hRb := hR _ _ hu₁ hu₂ hv₁ hv₂ (by rw [hpow]; exact_mod_cast hlo4) (by rw [hpow]; exact_mod_cast hhi4)
      have hb := box_cross (q := q) (hpos P₁ b₁ hP₁) (hpos P₂ b₂ hP₂)
        (W := fun χ => ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ SieveDyadic.bump (Q j) (hh j)‖)
        (fun χ => norm_nonneg _) (B := (q : ℝ) ^ (L - 1 / 50000)) (Real.rpow_nonneg hq0.le _)
        (fun T₁ T₂ hT₁ hT₂ a' b' => hq₂ q hq2 (P₁ * 2 ^ b₁) (P₂ * 2 ^ b₂) T₁ T₂ hT₁ hT₂ (hpos P₁ b₁ hP₁)
          (hpos P₂ b₂ hP₂) hRb a' b' 0 0 (n + 1) (by omega) Q hh (fun j hj => ⟨hQ j hj, hhh j hj⟩) hQP)
        (blockSet S₁ ⌊2 * (q : ℝ) ^ L⌋₊ P₁ P₁' b₁) (blockSet S₂ ⌊2 * (q : ℝ) ^ L⌋₊ P₂ P₂' b₂)
        (fun i => ∏ t, i t) (fun j => ∏ t, j t) (fun i hi => blockSet_val hP₁ hi)
        (fun j hj => blockSet_val hP₂ hj) D (fun m => hD ▸ blockSet_fiber S₁ _ P₁ P₁' b₁ m)
        (fun m => hD ▸ blockSet_fiber S₂ _ P₂ P₂' b₂ m) (lf.map crossOf) (N := N)
        (lt_of_le_of_lt ((hcardB S₂ P₂ P₂' b₂ hP₂).trans (Nat.mul_le_mul_left D
          ((Finset.mem_Ioc.1 (blockSet_val hP₂ hj₀)).1.le.trans (Finset.mem_filter.1 hj₀).2.2.2.1))) hDY)
        (fun i => Complex.exp (2 * π * Complex.I *
          ((κ' + ∑ j' : Fin lp.length, ξ j' * ((lp.get j').c 0 + lin (lp.get j') i) : ℝ) : ℂ)))
        (fun j => Complex.exp (2 * π * Complex.I * ((∑ j' : Fin lp.length, ξ j' * lin (lp.get j') j : ℝ) : ℂ)))
        (fun i _ => (hexp1 _).le) (fun j _ => (hexp1 _).le)
      refine hb.trans ?_
      rw [List.length_map, hA₀]
      have h3 : ((N + 1 : ℕ) : ℝ) ^ lf.length ≤ ((N + 1 : ℕ) : ℝ) ^ J₀ := pow_le_pow_right₀ hN1 hlf_len
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (by positivity))
        (Real.rpow_nonneg hq0.le _)
  -- the family's sum is that family's
  have hident : ∑ z ∈ RTg K Y Ω, dw q a (∏ t, z t) =
      Dsum q a (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => (∏ t, mx.1 t) * ∏ i, mx.2 i)
        (fun mx => (1 : ℂ) *
          ∏ j : Fin lp.length, ((if PrOf (lp.get j) σ mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) := by
    unfold Dsum
    have hpu : padded (Finset.univ : Finset (Fin K)) Y = padded ((S₁ ∪ S₂) ∪ Rs) Y := by rw [hSRu]
    rw [RTg, Finset.sum_filter, ← padded_univ, hpu, sum_padded_mul hSR, Finset.sum_product]
    have hXsub : Xs ⊆ padded (S₁ ∪ S₂) Y := by rw [hXs]; exact Finset.filter_subset _ _
    have h0 : ∀ z ∈ padded (S₁ ∪ S₂) Y, z ∉ Xs →
        ∑ w ∈ padded Rs Y, (if ∀ C ∈ Ω, C.holds 0 (z * w) then dw q a (∏ t, (z * w) t) else 0) = 0 := by
      intro z hzp hzX
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [ite_eq_right]
      intro hall
      exfalso
      apply hzX
      obtain ⟨x, hxw, hxp⟩ : ∃ x : Fin (n + 1) → ℕ, pad σ x = w ∧ ∀ i, (x i).Prime :=
        ⟨fun i => w (σ i), pad_read σ (mem_padded.1 hw).2,
          fun i => (mem_primesLe.1 ((mem_padded.1 hw).1 _ (σ i).2)).2⟩
      rw [← hxw] at hall
      have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hxp i).one_lt.le
      obtain ⟨-, h1, h2, h3, h4, h5⟩ := hreg _ (hprime z hzp x hxp) hall
      have hw1 : ∀ t ∉ Rs, pad σ x t = 1 := fun t ht => pad_of_notMem σ x ht
      rw [prod_part_mul hS₁R z hw1] at h1 h2
      rw [prod_part_mul hS₂R z hw1] at h3 h4
      have hle : ∏ t, (z * pad σ x) t ≤ Y := by rw [hY]; exact Nat.le_floor h5
      rw [hprodw z x, hprodS z hzp] at hle
      have hx0 : 0 < ∏ i, x i := Finset.prod_pos fun i _ => hx1 i
      have hm₁0 : 0 < ∏ t ∈ S₁, z t := Finset.prod_pos fun t _ => hz1 t
      have hm₂0 : 0 < ∏ t ∈ S₂, z t := Finset.prod_pos fun t _ => hz1 t
      have hY₁ : ∏ t ∈ S₁, z t ≤ Y :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hm₂0 hx0)) (by rw [← mul_assoc]; exact hle)
      have hY₂ : ∏ t ∈ S₂, z t ≤ Y :=
        le_trans (Nat.le_mul_of_pos_left _ hm₁0) (le_trans (Nat.le_mul_of_pos_right _ hx0) hle)
      exact (hmemXs z).2 ⟨hzp, ⟨h1, h2, hY₁⟩, ⟨h3, h4, hY₂⟩, ((hΩiff z x hz1 hx1).1 hall).1⟩
    rw [← Finset.sum_subset hXsub h0]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [sum_padded_fin σ]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hzp, -, -, hzf⟩ := (hmemXs z).1 hz
    have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
    have hx1 : ∀ i, 1 ≤ x i := fun i => (mem_primesLe.1 (Fintype.mem_piFinset.1 hx i)).2.one_lt.le
    have hcast : ∀ j : Fin lp.length, (((if PrOf (lp.get j) σ z x then 1 else 0 : ℝ)) : ℂ) =
        if PrOf (lp.get j) σ z x then 1 else 0 := fun j => by split_ifs <;> simp
    simp only [hcast]
    rw [Finset.prod_boole, hprodw z x]
    by_cases hall : ∀ C ∈ Ω, C.holds 0 (z * pad σ x)
    · rw [ite_eq_left hall, ite_eq_left (fun j _ => ((hΩiff z x hz1 hx1).1 hall).2 j), one_mul, one_mul]
    · rw [ite_eq_right hall,
        ite_eq_right (fun h' => hall ((hΩiff z x hz1 hx1).2 ⟨hzf, fun j => h' j (Finset.mem_univ _)⟩)),
        mul_zero, zero_mul]
  rw [hident]
  refine hkey.trans ?_
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))
      ≤ (q.totient : ℝ)⁻¹ * ((q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (L - δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA₀le (Real.rpow_nonneg hq0.le _)) hφ0
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ / 2) := by
        rw [← Real.rpow_add hq0]
        congr 2
        ring

open Classical in
/-- **Families of tuples of primes with two Type II variables (Lemma 4.6 in two variables).** Assume Proposition 3′
in two variables at `L` on `Rg` (`hII`) and `0 < L ≤ 5/2`. Fix `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and
`q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `S₁` and `S₂` be disjoint sets of indices that leave at least
one index out, and let `z` run over the `K`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω`
with constants at most `Λ₁ log q`. Suppose that every tuple of primes satisfying `Ω` has its entries at least
`q^{e₀}`, `P₁ < ∏_{S₁} z ≤ P₁′`, `P₂ < ∏_{S₂} z ≤ P₂′`, `Mlo < ∏_{S₁} z·∏_{S₂} z ≤ Mhi` and `∏ z ≤ 2q^L`, with
`P_i ≥ 1`, `Mlo ≥ 1` and `Mhi ≤ 2q^L`, and that `Rg u v` holds for the exponents `u ∈ [log_q P₁, log_q P₁′]` and
`v ∈ [log_q P₂, log_q P₂′]` with `Mlo ≤ 4q^{u+v}` and `q^{u+v} ≤ Mhi`. Then the sum over `z` of
`1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` is at most `q^{L−δ}/φ(q)` in absolute value.

The band `(Mlo, Mhi]` of the product of the two variables is the range of `n` over the rest: a rest in
`[q^{ρ₁}, q^{ρ₂}]` puts the product between `q^{L−ρ₂}` and `2q^{L−ρ₁}`, so the region is asked for on the part of the
rectangle where the rest has its true size. -/
theorem chain_two {L : ℝ} {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ}
    (he₀ : 0 < e₀) (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S₁ S₂ : Finset (Fin K)), Disjoint S₁ S₂ → (S₁ ∪ S₂)ᶜ.Nonempty →
      ∀ (Ω : List (GCmp K)), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      ∀ (P₁ P₁' P₂ P₂' Mlo Mhi : ℕ), 1 ≤ P₁ → 1 ≤ P₂ → 1 ≤ Mlo → (Mhi : ℝ) ≤ 2 * (q : ℝ) ^ L →
      (∀ u v : ℝ, Real.logb q P₁ ≤ u → u ≤ Real.logb q P₁' → Real.logb q P₂ ≤ v → v ≤ Real.logb q P₂' →
        (Mlo : ℝ) ≤ 4 * (q : ℝ) ^ (u + v) → (q : ℝ) ^ (u + v) ≤ Mhi → Rg u v) →
      (∀ z : Fin K → ℕ, (∀ t, (z t).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ t, (q : ℝ) ^ e₀ ≤ z t) ∧ P₁ < ∏ t ∈ S₁, z t ∧ ∏ t ∈ S₁, z t ≤ P₁' ∧
          P₂ < ∏ t ∈ S₂, z t ∧ ∏ t ∈ S₂, z t ≤ P₂' ∧
          Mlo < (∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t ∧ (∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t ≤ Mhi ∧
          ((∏ t, z t : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ t, z t)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith
  obtain ⟨δ, hδ, q₀, H⟩ := chain_two_core hII hL0 hL he₀ K (J₀ + 2) hΛ'
  refine ⟨δ, hδ, max q₀ 2, ?_⟩
  intro q _ hq a ha S₁ S₂ hdisj hne Ω hΩlen hΩc P₁ P₁' P₂ P₂' Mlo Mhi hP₁ hP₂ hMlo hMhi hR hreg
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hprimes : ∀ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (∀ t, (z t).Prime) ∧ ∀ C ∈ Ω, C.holds 0 z := by
    intro z hz
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
    exact ⟨fun t => (mem_primesLe.1 (hz.1 t)).2, hz.2⟩
  rcases Nat.eq_zero_or_pos Mhi with h0 | hMhi0
  · -- no tuple: the product of the two variables is at least `1`
    rw [Finset.sum_eq_zero, norm_zero]
    · positivity
    intro z hz
    exfalso
    obtain ⟨hzp, hzΩ⟩ := hprimes z hz
    obtain ⟨-, -, -, -, -, hlo, hhi, -⟩ := hreg z hzp hzΩ
    omega
  have hMlo0 : (0 : ℝ) < Mlo := by exact_mod_cast hMlo
  have hMhi0' : (0 : ℝ) < Mhi := by exact_mod_cast hMhi0
  -- the band as two comparisons
  have hunion : ∀ z : Fin K → ℕ, ∏ t ∈ S₁ ∪ S₂, (z t : ℝ) = (((∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t : ℕ) : ℝ) := by
    intro z
    rw [Finset.prod_union hdisj]
    push_cast
    rfl
  have hbandC : ∀ z : Fin K → ℕ, (∀ t, 1 ≤ z t) →
      ((gDown (S₁ ∪ S₂) (Mlo : ℝ) true).holds 0 z ∧ (gUp (S₁ ∪ S₂) (Mhi : ℝ) false).holds 0 z ↔
        Mlo < (∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t ∧ (∏ t ∈ S₁, z t) * ∏ t ∈ S₂, z t ≤ Mhi) := by
    intro z hz1
    rw [gDown_holds _ hMlo0 true 0 hz1, gUp_holds _ hMhi0' false 0 hz1, hunion z]
    simp only [ite_true, Bool.false_eq_true, ite_false, Nat.cast_lt, Nat.cast_le]
  have hfam : RTg K ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gDown (S₁ ∪ S₂) (Mlo : ℝ) true, gUp (S₁ ∪ S₂) (Mhi : ℝ) false]) =
      RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω := by
    ext z
    simp only [RTg, Finset.mem_filter, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · intro h
      have hzp : ∀ t, (z t).Prime := fun t => (mem_primesLe.1 (Fintype.mem_piFinset.1 h.1 t)).2
      obtain ⟨-, -, -, -, -, hlo, hhi, -⟩ := hreg z hzp h.2
      exact ⟨h.1, h.2, (hbandC z (fun t => (hzp t).one_lt.le)).2 ⟨hlo, hhi⟩⟩
  rw [← hfam]
  refine H q (le_trans (le_max_left _ _) hq) a ha S₁ S₂ hdisj hne _ ?_ ?_ P₁ P₁' P₂ P₂' Mlo Mhi hP₁ hP₂ hR ?_ ?_
  · rw [List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · -- the constants
    intro C hC
    have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
    have hLl : 0 ≤ (L + 1) * Real.log q := mul_nonneg (by linarith) hlogq
    have hsplit : (Λ₁ + L + 1) * Real.log q = Λ₁ * Real.log q + (L + 1) * Real.log q := by ring
    rw [hsplit]
    rcases List.mem_append.1 hC with h | h
    · linarith [hΩc C h]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · show -Real.log (Mlo : ℝ) ≤ _
        have : 0 ≤ Real.log (Mlo : ℝ) := Real.log_nonneg (by exact_mod_cast hMlo)
        linarith
      · show Real.log (Mhi : ℝ) ≤ _
        have h1 : (Mhi : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
          rw [Real.rpow_add hq0, Real.rpow_one]
          have : (0 : ℝ) < (q : ℝ) ^ L := by positivity
          nlinarith
        have h2 := Real.log_le_log hMhi0' h1
        rw [Real.log_rpow hq0] at h2
        linarith
  · -- the band, from the comparisons with no prime of the rest
    intro z₀ hz1 hfree
    refine (hbandC z₀ hz1).1 ⟨hfree _ (by simp) ?_, hfree _ (by simp) ?_⟩
    · intro t ht
      show (if t ∈ S₁ ∪ S₂ then (1 : ℝ) else 0) = 0
      rw [ite_eq_right (Finset.mem_compl.1 ht)]
    · intro t ht
      show -(if t ∈ S₁ ∪ S₂ then (1 : ℝ) else 0) = 0
      rw [ite_eq_right (Finset.mem_compl.1 ht), neg_zero]
  · intro z hz hzΩ
    have hzΩ' : ∀ C ∈ Ω, C.holds 0 z := fun C hC => hzΩ C (List.mem_append_left _ hC)
    obtain ⟨h1, h2, h3, h4, h5, -, -, h8⟩ := hreg z hz hzΩ'
    exact ⟨h1, h2, h3, h4, h5, h8⟩

end SieveTwoChain

#print axioms SieveTwoChain.chain_two
