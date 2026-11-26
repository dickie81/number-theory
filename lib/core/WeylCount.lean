import Mathlib

/-!
# Weyl dimensions as Gelfand–Tsetlin counts

Module 3 of the L5/L6 plan (toolkit T1): the classical `GL_n` counts, as pure combinatorics. Weights are integer
vectors `μ ∈ ℤ^n` (antitone when dominant, as `lam0 s` in `LocalLattice`).

**Gelfand–Tsetlin patterns.** `κ ∈ ℤ^n` interlaces `μ ∈ ℤ^{n+1}` when `μ_{i+1} ≤ κ_i ≤ μ_i` (`interlace μ`, a box).
The Weyl dimension `dimW n μ` is *defined* as the number of Gelfand–Tsetlin patterns with top row `μ`, through the
branching recursion `dimW_{n+1}(μ) = Σ_{κ interlacing μ} dimW_n(κ)` (`dimW_succ`, by definition); it is `0` when `μ`
is not antitone (for `n ≥ 2`). An interlacing row is antitone (`antitone_of_mem_interlace`).

**The Weyl dimension formula** (`dimW_mul_prod`, `dimW_eq_prod`): for antitone `μ`,
`dimW n μ·∏_{i<j}(j − i) = ∏_{i<j}(μ_i − μ_j + j − i)`. Proof: in the increasing coordinates
`x_i = μ_{n−1−i} + i` (`incr`), `dimW n μ = det[C(x_i, j)]_{i,j<n}` (`dimW_eq_binDet`, by induction: the
interlacing box is a product, the determinant is multilinear in the rows, the row sums are hockey sticks
`Σ_{a ≤ y ≤ b} C(y + s, j) = C(b + s + 1, j + 1) − C(a + s, j + 1)` (`sum_choose_Icc`), and subtracting consecutive
rows of the `(n+1)`-matrix gives the `n`-matrix of differences (`binDet_succ`)); and
`det[C(x_i, j)]·∏_j j! = ∏_{i<j}(x_j − x_i)` (`binDet_mul_prod`: the columns `j!·C(x, j)` are the monic
`descPochhammer` polynomials, so Mathlib's Vandermonde applies). Consequences: translation invariance
(`dimW_add_const`) and duality `dimW(−μ ∘ rev) = dimW(μ)` (`dimW_dual`).

**Pieri** (count form, `dimW_mul_choose`): in `n + 1` coordinates,
`dimW(ν)·C(b + n, n) = Σ_{μ/ν horizontal b-strip} dimW(μ)`, where `μ/ν` is a horizontal `b`-strip when
`μ_0 ≥ ν_0 ≥ μ_1 ≥ … ≥ μ_n ≥ ν_n` and `|μ| = |ν| + b` (`strip`). By induction through branching: both sides become
sums of `dimW_n(κ)` over pairs, `(ℓ ≺ ν, κ/ℓ a strip of size ≤ b)` on the left (hockey stick in `b`) and
`(μ/ν a b-strip, κ ≺ μ)` on the right; the free coordinates `ℓ` and `(μ_1, …, μ_n)` fill the same box
`max(ν_{i+1}, κ̃_{i+1}) ≤ · ≤ min(ν_i, κ_i)` (`κ̃ = (κ, ν_n)`, `kext`), and the size conditions correspond under the
reflection `x ↦ c − x` of the box (`ctr`, `sum_ctr`, `up`, `down`, `up_mem`, `down_mem`).

**Flat weights and `Har_m`** (A-N10). For `GL_{m+1}`, `m ≥ 1`: the horizontal `α`-strips over the column
`(β, …, β, 0)` are the `fl(α − j, β − j) + β`, `j ≤ min(α, β)`, where `fl(α, β) = (α, 0, …, 0, −β)` (`flatW`,
`sum_strip_colW`). Pieri over the trivial weight gives the row `dimW(α, 0, …, 0) = C(α + m, m)` (`dimW_flatW_zero`),
hence the column (`dimW_colW`, by duality); Pieri over the column gives the flat sum
`Σ_{j ≤ min(α,β)} dimW fl(α − j, β − j) = C(α + m, m)·C(β + m, m)` (`sum_dimW_flatW`), and telescoping gives
`dimW fl(α, β) = Har_m(α, β) = C(α+m, m)C(β+m, m) − C(α−1+m, m)C(β−1+m, m)` (`har`, `dimW_flatW`), so
`Σ_{j ≤ min(α,β)} Har_m(α − j, β − j) = C(α + m, m)·C(β + m, m)` (`sum_har`) and its product over the tops
(`sum_prod_har`).

**Subspace counts** (the Gaussian-binomial bound `[k, r]_q ≥ q^{r(k−r)}`, L6 N1(d)). Over a finite field of `q`
elements, a `k`-dimensional space has `≥ q^{r(k−r)}` subspaces of dimension `r` (`pow_le_card_finrank`: the graphs of
the linear maps `F^r → F^{k−r}`, transported by a linear equivalence) and of codimension `r` (`pow_le_card_codim`), and
exactly `(q^k − 1)/(q − 1)` hyperplanes (`card_hyperplanes`: the lines of the dual space, `Projectivization.card`).
The Gaussian binomial itself is not needed.
-/

namespace WeylCount

open Finset

/-! ## Gelfand–Tsetlin patterns -/

/-- **The rows interlacing `μ`**: the `κ ∈ ℤ^n` with `μ_{i+1} ≤ κ_i ≤ μ_i` for `μ ∈ ℤ^{n+1}` (a box). -/
def interlace {n : ℕ} (μ : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Icc (μ i.succ) (μ i.castSucc)

/-- **The Weyl dimension** `dimW n μ` of `μ ∈ ℤ^n`: the number of Gelfand–Tsetlin patterns with top row `μ`,
counted by the branching recursion (`0` unless `μ` is antitone, for `n ≥ 2`). -/
def dimW : (n : ℕ) → (Fin n → ℤ) → ℕ
  | 0, _ => 1
  | n + 1, μ => ∑ κ ∈ interlace μ, dimW n κ

/-- **Branching** (`GL_{n+1} ↓ GL_n`): `dimW_{n+1}(μ) = Σ_{κ interlacing μ} dimW_n(κ)`. -/
theorem dimW_succ {n : ℕ} (μ : Fin (n + 1) → ℤ) : dimW (n + 1) μ = ∑ κ ∈ interlace μ, dimW n κ := rfl

/-- **Membership in the interlacing box.** -/
theorem mem_interlace {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} :
    κ ∈ interlace μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  simp [interlace]

/-- **Interlacing rows are antitone**: `κ_{i+1} ≤ μ_{i+1} ≤ κ_i`. -/
theorem antitone_of_mem_interlace {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hκ : κ ∈ interlace μ) :
    Antitone κ := by
  rw [mem_interlace] at hκ
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h := (hκ i.castSucc).1
    rw [Fin.succ_castSucc] at h
    exact (hκ i.succ).2.trans h

/-! ## The binomial determinant -/

/-- **Increasing coordinates** `x_i = μ_{n−1−i} + i` of `μ ∈ ℤ^n` (strictly increasing when `μ` is antitone). -/
def incr {n : ℕ} (μ : Fin n → ℤ) : Fin n → ℤ := fun i => μ i.rev + (i : ℕ)

/-- **The binomial determinant** `det[C(x_i, j)]_{i,j<n}`. -/
def binDet {n : ℕ} (x : Fin n → ℤ) : ℤ := (Matrix.of fun i j : Fin n => Ring.choose (x i) (j : ℕ)).det

/-- **Hockey stick over `ℤ`**: `Σ_{a ≤ y ≤ b} C(y + s, j) = C(b + s + 1, j + 1) − C(a + s, j + 1)` for `a ≤ b + 1`. -/
theorem sum_choose_Icc (s : ℤ) (j : ℕ) {a b : ℤ} (h : a ≤ b + 1) :
    ∑ y ∈ Icc a b, Ring.choose (y + s) j = Ring.choose (b + s + 1) (j + 1) - Ring.choose (a + s) (j + 1) := by
  have key : ∀ c : ℤ, a ≤ c → ∑ y ∈ Icc a (c - 1), Ring.choose (y + s) j =
      Ring.choose (c + s) (j + 1) - Ring.choose (a + s) (j + 1) := by
    intro c hc
    induction c, hc using Int.leInduction with
    | base => simp
    | succ c hc ih =>
      have e : Icc a (c + 1 - 1) = insert c (Icc a (c - 1)) := by
        simpa using (Finset.insert_Icc_right_eq_Icc_add_one (a := a) (b := c - 1) (by omega)).symm
      rw [e, Finset.sum_insert (by simp), ih, show c + 1 + s = (c + s) + 1 by ring, Ring.choose_succ_succ]
      ring
  have := key (b + 1) h
  rwa [add_sub_cancel_right, show b + 1 + s = b + s + 1 by ring] at this

/-- **Row reduction of the binomial determinant**: subtracting consecutive rows,
`det[C(x_i, j)]_{i,j≤n} = det[C(x_{i+1}, j+1) − C(x_i, j+1)]_{i,j<n}`. -/
theorem binDet_succ {n : ℕ} (x : Fin (n + 1) → ℤ) :
    binDet x = (Matrix.of fun i j : Fin n =>
      Ring.choose (x i.succ) ((j : ℕ) + 1) - Ring.choose (x i.castSucc) ((j : ℕ) + 1)).det := by
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => Ring.choose (x i) (j : ℕ)
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of (Fin.cons (A 0) fun i => A i.succ - A i.castSucc)
  have hAB : A.det = B.det := Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => by simp [B])
    (fun i j => by simp [B])
  rw [binDet, hAB, Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · simp only [Fin.val_zero, pow_zero, Fin.succAbove_zero, one_mul]
    have h0 : B 0 0 = 1 := by simp [B, A]
    rw [h0, one_mul]
    congr 1
  · intro i _
    simp [B, A]

/-- **Weyl dimension as a binomial determinant**: `dimW n μ = det[C(x_i, j)]` with `x = incr μ` (antitone `μ`). -/
theorem dimW_eq_binDet {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) : (dimW n μ : ℤ) = binDet (incr μ) := by
  induction n with
  | zero => simp [dimW, binDet]
  | succ n ih =>
    rw [dimW_succ, Nat.cast_sum, Finset.sum_congr rfl fun κ hκ => ih (antitone_of_mem_interlace hκ)]
    set g : (i : Fin n) → ℤ → Fin n → ℤ := fun i y j => Ring.choose (y + (i : ℕ)) (j : ℕ)
    have h1 : ∀ κ : Fin n → ℤ, binDet (incr κ) = Matrix.detRowAlternating fun i => g i (κ i.rev) := fun κ => rfl
    simp_rw [h1]
    have h2 : ∑ κ ∈ interlace μ, Matrix.detRowAlternating (fun i => g i (κ i.rev)) =
        ∑ r ∈ Fintype.piFinset (fun i : Fin n => Icc (μ i.rev.succ) (μ i.rev.castSucc)),
          Matrix.detRowAlternating (fun i => g i (r i)) := by
      refine Finset.sum_nbij' (fun κ i => κ i.rev) (fun r i => r i.rev) ?_ ?_ ?_ ?_ ?_
      · intro κ hκ
        simp only [interlace, Fintype.mem_piFinset] at hκ ⊢
        exact fun i => hκ i.rev
      · intro r hr
        simp only [interlace, Fintype.mem_piFinset] at hr ⊢
        intro i
        simpa using hr i.rev
      · intro κ _
        simp
      · intro r _
        simp
      · intro κ _
        rfl
    have h3 := MultilinearMap.map_sum_finset (Matrix.detRowAlternating (n := Fin n) (R := ℤ)).toMultilinearMap g
      (fun i => Icc (μ i.rev.succ) (μ i.rev.castSucc))
    simp only [AlternatingMap.coe_multilinearMap] at h3
    rw [h2, ← h3, binDet_succ]
    congr 1
    ext i j
    simp only [Finset.sum_apply, g, Matrix.of_apply]
    rw [sum_choose_Icc _ _ (by have := hμ (Fin.castSucc_le_succ i.rev); omega)]
    simp only [incr, Fin.rev_succ, Fin.rev_castSucc, Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring_nf

/-- **Binomial Vandermonde**: `det[C(x_i, j)]·∏_{j<n} j! = ∏_{i<j} (x_j − x_i)`. -/
theorem binDet_mul_prod {n : ℕ} (x : Fin n → ℤ) :
    binDet x * ∏ j : Fin n, ((j : ℕ).factorial : ℤ) = ∏ i, ∏ j ∈ Ioi i, (x j - x i) := by
  rw [← Matrix.det_vandermonde, Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x
    (fun j => descPochhammer ℤ j) (fun j => descPochhammer_natDegree ℤ j) (fun j => monic_descPochhammer ℤ j),
    binDet, mul_comm, ← Matrix.det_mul_row]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose,
    nsmul_eq_mul]

/-- **The pair product in increasing coordinates**: `∏_{i<j} (x_j − x_i) = ∏_{i<j} (μ_i − μ_j + j − i)`
for `x = incr μ`. -/
theorem prod_incr {n : ℕ} (μ : Fin n → ℤ) :
    ∏ i, ∏ j ∈ Ioi i, (incr μ j - incr μ i) =
      ∏ i : Fin n, ∏ j ∈ Ioi i, (μ i - μ j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by
  have hrev : ∀ a : Fin n, (((a.rev : ℕ)) : ℤ) = n - 1 - a := fun a => by rw [Fin.val_rev]; omega
  rw [← Equiv.prod_comp Fin.revPerm]
  have h1 : ∀ b : Fin n, ∏ j ∈ Ioi (Fin.revPerm b), (incr μ j - incr μ (Fin.revPerm b)) =
      ∏ a ∈ Iio b, (μ a - μ b + ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
    intro b
    rw [Fin.revPerm_apply, ← Fin.map_revPerm_Iio, Finset.prod_map]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Equiv.coe_toEmbedding, Fin.revPerm_apply, incr, Fin.rev_rev, hrev]
    ring
  simp_rw [h1]
  exact Finset.prod_comm' fun b a => by simp

/-- **The trivial weight** has one Gelfand–Tsetlin pattern. -/
theorem dimW_zero (n : ℕ) : dimW n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : interlace (0 : Fin (n + 1) → ℤ) = {0} := by
      simp only [interlace, Pi.zero_apply, Icc_self]
      exact Fintype.piFinset_singleton (0 : Fin n → ℤ)
    rw [dimW_succ, h, sum_singleton, ih]

/-- **The Weyl denominator** `∏_{i<j} (j − i)` is nonzero. -/
theorem prod_sub_ne_zero (n : ℕ) : ∏ i : Fin n, ∏ j ∈ Ioi i, (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) ≠ 0 :=
  prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj => by
    have : (i : ℕ) < j := Fin.lt_def.1 (mem_Ioi.1 hj)
    omega

/-- **The Weyl dimension formula**: `dimW n μ·∏_{i<j} (j − i) = ∏_{i<j} (μ_i − μ_j + j − i)` for antitone `μ`. -/
theorem dimW_mul_prod {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) :
    (dimW n μ : ℤ) * ∏ i : Fin n, ∏ j ∈ Ioi i, (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) =
      ∏ i : Fin n, ∏ j ∈ Ioi i, (μ i - μ j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by
  have h0 := binDet_mul_prod (incr (0 : Fin n → ℤ))
  rw [← dimW_eq_binDet (fun _ _ _ => le_rfl), dimW_zero, prod_incr] at h0
  simp only [Pi.zero_apply, sub_self, zero_add, Nat.cast_one, one_mul] at h0
  rw [← h0, dimW_eq_binDet hμ, binDet_mul_prod, prod_incr]

/-- **The Weyl dimension formula**, rational form: `dimW n μ = ∏_{i<j} (μ_i − μ_j + j − i)/(j − i)`. -/
theorem dimW_eq_prod {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) :
    (dimW n μ : ℚ) = ∏ i : Fin n, ∏ j ∈ Ioi i,
      ((μ i - μ j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℚ) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (dimW_mul_prod hμ)
  have hne := prod_sub_ne_zero n
  simp_rw [Finset.prod_div_distrib]
  rw [eq_div_iff (by exact_mod_cast hne)]
  push_cast at h ⊢
  exact h

/-- **Translation invariance**: `dimW n (μ + c) = dimW n μ` for antitone `μ`. -/
theorem dimW_add_const {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (c : ℤ) :
    dimW n (fun i => μ i + c) = dimW n μ := by
  have h1 := dimW_mul_prod (μ := fun i => μ i + c) fun a b h => by simpa using hμ h
  have h2 := dimW_mul_prod hμ
  have : (dimW n (fun i => μ i + c) : ℤ) = dimW n μ := by
    refine mul_right_cancel₀ (prod_sub_ne_zero n) ?_
    rw [h1, h2]
    exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
  exact_mod_cast this

/-- **Duality**: `dimW n (−μ ∘ rev) = dimW n μ` for antitone `μ` (the dual representation). -/
theorem dimW_dual {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) : dimW n (fun i => -μ i.rev) = dimW n μ := by
  have h1 := dimW_mul_prod (μ := fun i => -μ i.rev) fun a b h => by
    simpa using hμ (Fin.rev_le_rev.2 h)
  have h2 := dimW_mul_prod hμ
  have : (dimW n (fun i => -μ i.rev) : ℤ) = dimW n μ := by
    refine mul_right_cancel₀ (prod_sub_ne_zero n) ?_
    rw [h1, h2, ← prod_incr]
    exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by simp only [incr, Fin.rev_rev]; ring
  exact_mod_cast this

/-! ## Pieri -/

/-- **Horizontal strips** of size `b` over `ν ∈ ℤ^{n+1}`: the `μ` with `μ_0 ≥ ν_0 ≥ μ_1 ≥ ν_1 ≥ … ≥ μ_n ≥ ν_n` and
`|μ| = |ν| + b` (then `μ_0 ≤ ν_0 + b`, which makes the set finite). -/
def strip {n : ℕ} (ν : Fin (n + 1) → ℤ) (b : ℕ) : Finset (Fin (n + 1) → ℤ) :=
  (Fintype.piFinset fun i =>
      Icc (ν i) ((Fin.cons (ν 0 + b) fun i : Fin n => ν i.castSucc : Fin (n + 1) → ℤ) i)).filter
    fun μ => ∑ i, μ i = ∑ i, ν i + b

/-- **Membership in the strips.** -/
theorem mem_strip {n : ℕ} {ν μ : Fin (n + 1) → ℤ} {b : ℕ} :
    μ ∈ strip ν b ↔ (ν 0 ≤ μ 0 ∧ μ 0 ≤ ν 0 + b) ∧
      (∀ i : Fin n, ν i.succ ≤ μ i.succ ∧ μ i.succ ≤ ν i.castSucc) ∧ ∑ i, μ i = ∑ i, ν i + b := by
  simp [strip, Fin.forall_fin_succ, and_assoc]

section PieriStep

variable {n : ℕ} (ν : Fin (n + 2) → ℤ) (κ : Fin (n + 1) → ℤ)

/-- **The extended row** `κ̃ = (κ_0, …, κ_n, ν_{n+1})`. -/
def kext : Fin (n + 2) → ℤ := Fin.snoc κ (ν (Fin.last _))

/-- **The reflection centres** `c_i = max(ν_{i+1}, κ̃_{i+1}) + min(ν_i, κ_i)`: the rows `ℓ` with `ℓ ≺ ν` and `κ/ℓ`
a horizontal strip, and the tails of the `μ` with `μ/ν` a horizontal strip and `κ ≺ μ`, fill the same box
`max(ν_{i+1}, κ̃_{i+1}) ≤ · ≤ min(ν_i, κ_i)`, exchanged by `x ↦ c − x`. -/
def ctr (i : Fin (n + 1)) : ℤ := max (ν i.succ) (kext ν κ i.succ) + min (ν i.castSucc) (κ i)

/-- **The extended row inside**: `κ̃_{i+1} = κ_{i+1}` for `i < n`. -/
theorem kext_castSucc_succ (i : Fin n) : kext ν κ i.castSucc.succ = κ i.succ := by
  rw [Fin.succ_castSucc, kext, Fin.snoc_castSucc]

/-- **The extended row at the end**: `κ̃_{n+1} = ν_{n+1}`. -/
theorem kext_last_succ : kext ν κ (Fin.last n).succ = ν (Fin.last n).succ := by
  rw [Fin.succ_last, kext, Fin.snoc_last]

/-- **The centre sum**: `Σ_i c_i = |ν| + |κ| − max(ν_0, κ_0)`. -/
theorem sum_ctr : ∑ i, ctr ν κ i = ∑ i, ν i + ∑ i, κ i - max (ν 0) (κ 0) := by
  have h1 := Fin.sum_univ_succ (fun i => max (ν i) (kext ν κ i))
  have h2 := Fin.sum_univ_castSucc (fun i => min (ν i) (kext ν κ i))
  have h3 := Fin.sum_univ_castSucc (kext ν κ)
  have h4 : ∑ i, (max (ν i) (kext ν κ i) + min (ν i) (kext ν κ i)) = ∑ i, (ν i + kext ν κ i) :=
    sum_congr rfl fun i _ => by omega
  have e0 : kext ν κ 0 = κ 0 := by rw [← Fin.castSucc_zero, kext, Fin.snoc_castSucc]
  have ec : ∀ i, kext ν κ i.castSucc = κ i := fun i => by rw [kext, Fin.snoc_castSucc]
  have el : kext ν κ (Fin.last _) = ν (Fin.last _) := by rw [kext, Fin.snoc_last]
  simp only [ec, el, e0, min_self] at h1 h2 h3
  rw [sum_add_distrib, sum_add_distrib] at h4
  simp only [ctr, sum_add_distrib]
  linarith

/-- **The strip matched with a row**: `μ = (|ν| + b − Σ_i (c_i − ℓ_i), c − ℓ)`. -/
def up (b : ℕ) (l : Fin (n + 1) → ℤ) : Fin (n + 2) → ℤ :=
  Fin.cons (∑ i, ν i + b - ∑ i, (ctr ν κ i - l i)) fun i => ctr ν κ i - l i

/-- **The row matched with a strip**: `ℓ = c − (μ_1, …, μ_{n+1})`. -/
def down (μ : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ := fun i => ctr ν κ i - μ i.succ

variable {ν κ}

/-- **`up` lands in the right-hand pairs**: if `ℓ ≺ ν` and `κ/ℓ` is a `b′`-strip with `b′ ≤ b`, then `up ℓ` is a
`b`-strip over `ν` and `κ ≺ up ℓ`. -/
theorem up_mem {b b' : ℕ} {l : Fin (n + 1) → ℤ} (hl : l ∈ interlace ν) (hb : b' ≤ b) (hκ : κ ∈ strip l b') :
    up ν κ b l ∈ strip ν b ∧ κ ∈ interlace (up ν κ b l) := by
  rw [mem_interlace] at hl ⊢
  rw [mem_strip] at hκ ⊢
  obtain ⟨⟨h0a, h0b⟩, hs, hsum⟩ := hκ
  have hc := sum_ctr ν κ
  have hsl : ∑ i, (ctr ν κ i - l i) = ∑ i, ctr ν κ i - ∑ i, l i := sum_sub_distrib _ _
  have hlo : ∀ i : Fin (n + 1), max (ν i.succ) (kext ν κ i.succ) ≤ l i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [kext_castSucc_succ]; exact max_le (hl _).1 (hs i').2
    · rw [kext_last_succ]; exact max_le (hl _).1 (hl _).1
  have hlk : ∀ i, l i ≤ κ i := Fin.cases h0a fun i => (hs i).1
  have hhi : ∀ i, l i ≤ min (ν i.castSucc) (κ i) := fun i => le_min (hl i).2 (hlk i)
  have hν0 := (hl 0).2
  simp only [Fin.castSucc_zero] at hν0
  have hk0 : κ 0 ≤ max (ν 0) (κ 0) := le_max_right _ _
  have hn0 : ν 0 ≤ max (ν 0) (κ 0) := le_max_left _ _
  have hm0 : max (ν 0) (κ 0) ≤ ν 0 ∨ max (ν 0) (κ 0) ≤ κ 0 := by omega
  refine ⟨⟨⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · simp only [up, Fin.cons_zero]; omega
  · simp only [up, Fin.cons_zero]; omega
  · simp only [up, Fin.cons_succ, ctr]; have := hhi i; omega
  · simp only [up, Fin.cons_succ, ctr]; have := hlo i; omega
  · simp only [up, Fin.sum_cons]; ring
  · simp only [up, Fin.cons_succ, ctr]; have := hlo i; omega
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.castSucc_zero, up, Fin.cons_zero]; omega
    · rw [← Fin.succ_castSucc]
      simp only [up, Fin.cons_succ, ctr]
      have := hhi i.castSucc
      rw [kext_castSucc_succ]
      omega

/-- **`down` lands in the left-hand pairs**: if `μ/ν` is a `b`-strip and `κ ≺ μ`, then `down μ ≺ ν` and `κ/down μ`
is a strip of size `|κ| − |down μ| ≤ b`. -/
theorem down_mem {b : ℕ} {μ : Fin (n + 2) → ℤ} (hμ : μ ∈ strip ν b) (hκ : κ ∈ interlace μ) :
    down ν κ μ ∈ interlace ν ∧ (∑ i, κ i - ∑ i, down ν κ μ i).toNat ≤ b ∧
      κ ∈ strip (down ν κ μ) (∑ i, κ i - ∑ i, down ν κ μ i).toNat := by
  rw [mem_interlace] at hκ ⊢
  rw [mem_strip] at hμ ⊢
  obtain ⟨⟨h0a, h0b⟩, hs, hsum⟩ := hμ
  have hc := sum_ctr ν κ
  have hsd : ∑ i, down ν κ μ i = ∑ i, ctr ν κ i - ∑ i : Fin (n + 1), μ i.succ := sum_sub_distrib _ _
  have hμs := Fin.sum_univ_succ μ
  have hlo : ∀ i : Fin (n + 1), max (ν i.succ) (kext ν κ i.succ) ≤ μ i.succ := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [kext_castSucc_succ]
      refine max_le (hs _).1 ?_
      have := (hκ i'.succ).2
      rwa [← Fin.succ_castSucc] at this
    · rw [kext_last_succ]; exact max_le (hs _).1 (hs _).1
  have hhi : ∀ i : Fin (n + 1), μ i.succ ≤ min (ν i.castSucc) (κ i) := fun i => le_min (hs i).2 (hκ i).1
  have hk0 := (hκ 0).2
  simp only [Fin.castSucc_zero] at hk0
  have hdk : ∀ i : Fin (n + 1), down ν κ μ i ≤ κ i := fun i => by
    simp only [down, ctr]; have := hlo i; have := hhi i; omega
  have hpos : 0 ≤ ∑ i, κ i - ∑ i, down ν κ μ i := by
    rw [← sum_sub_distrib]; exact sum_nonneg fun i _ => by have := hdk i; omega
  have hd0 : κ 0 - down ν κ μ 0 ≤ ∑ i, κ i - ∑ i, down ν κ μ i := by
    rw [← sum_sub_distrib, Fin.sum_univ_succ]
    have : 0 ≤ ∑ i : Fin n, (κ i.succ - down ν κ μ i.succ) :=
      sum_nonneg fun (i : Fin n) _ => by have := hdk i.succ; omega
    linarith
  have hD := Int.toNat_of_nonneg hpos
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ⟨⟨hdk 0, ?_⟩, fun i => ⟨hdk _, ?_⟩, ?_⟩⟩
  · simp only [down, ctr]; have := hhi i; omega
  · simp only [down, ctr]; have := hlo i; omega
  · have hm : max (ν 0) (κ 0) ≤ μ 0 := max_le h0a hk0
    rw [← Int.ofNat_le, hD]
    linarith
  · omega
  · simp only [down, ctr]
    have := hhi i.castSucc
    rw [kext_castSucc_succ]
    omega
  · omega

end PieriStep

/-- **Pieri** (count form): `dimW(ν)·C(b + n, n) = Σ_{μ/ν horizontal b-strip} dimW(μ)` in `n + 1` coordinates
(`C(b + n, n) = dim Sym^b`). By induction on `n` through the branching rule: both sides become sums of
`dimW_n(κ)` over pairs, and the pairs `(ℓ ≺ ν, κ/ℓ a strip of size ≤ b)` and `(μ/ν a b-strip, κ ≺ μ)` are matched by
the reflection `ℓ ↔ c − (μ_1, …, μ_n)` of a common box (`up`, `down`). -/
theorem dimW_mul_choose {n : ℕ} (ν : Fin (n + 1) → ℤ) (b : ℕ) :
    dimW (n + 1) ν * (b + n).choose n = ∑ μ ∈ strip ν b, dimW (n + 1) μ := by
  induction n generalizing b with
  | zero =>
    have h1 : ∀ κ : Fin 1 → ℤ, dimW 1 κ = 1 := fun κ => by simp [interlace, dimW]
    have h2 : strip ν b = {fun _ => ν 0 + b} := by
      ext μ
      rw [mem_strip, mem_singleton]
      constructor
      · rintro ⟨-, -, h⟩
        funext i
        fin_cases i
        simpa using h
      · rintro rfl
        simp
    simp [h1, h2]
  | succ n ih =>
    have hc : (b + (n + 1)).choose (n + 1) = ∑ b' ∈ range (b + 1), (b' + n).choose n := by
      rw [Nat.sum_range_add_choose]; ring_nf
    have hL : dimW (n + 2) ν * (b + (n + 1)).choose (n + 1) =
        ∑ x ∈ (interlace ν).sigma fun l => (range (b + 1)).sigma fun b' => strip l b', dimW (n + 1) x.2.2 := by
      rw [dimW_succ, sum_mul, sum_sigma]
      refine sum_congr rfl fun l _ => ?_
      rw [hc, mul_sum, sum_sigma]
      exact sum_congr rfl fun b' _ => ih l b'
    have hR : ∑ μ ∈ strip ν b, dimW (n + 2) μ = ∑ y ∈ (strip ν b).sigma interlace, dimW (n + 1) y.2 := by
      rw [sum_sigma]; rfl
    rw [hL, hR]
    refine sum_nbij' (fun x => ⟨up ν x.2.2 b x.1, x.2.2⟩)
      (fun y => ⟨down ν y.2 y.1, ⟨(∑ i, y.2 i - ∑ i, down ν y.2 y.1 i).toNat, y.2⟩⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨l, b', κ⟩ hx
      simp only [mem_sigma, mem_range] at hx ⊢
      exact up_mem hx.1 (by omega) hx.2.2
    · rintro ⟨μ, κ⟩ hy
      simp only [mem_sigma, mem_range] at hy ⊢
      obtain ⟨h1, h2, h3⟩ := down_mem hy.1 hy.2
      exact ⟨h1, by omega, h3⟩
    · rintro ⟨l, b', κ⟩ hx
      simp only [mem_sigma, mem_range] at hx
      have hd : down ν κ (up ν κ b l) = l := funext fun i => by simp [down, up]
      have hs := (mem_strip.1 hx.2.2).2.2
      simp only [hd, hs, add_sub_cancel_left, Int.toNat_natCast]
    · rintro ⟨μ, κ⟩ hy
      simp only [mem_sigma] at hy
      have hs := (mem_strip.1 hy.1).2.2
      have hμs := Fin.sum_univ_succ μ
      have hu : up ν κ b (down ν κ μ) = μ := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [up, down, Fin.cons_zero, sub_sub_cancel]
          linarith
        · simp [up, down]
      simp only [hu]
    · intro x _
      rfl

/-! ## Flat weights and `Har_m` -/

/-- **The flat weight** `fl(α, β) = (α, 0, …, 0, −β) ∈ ℤ^{m+1}`. -/
def flatW (m α β : ℕ) : Fin (m + 1) → ℤ := fun i => if (i : ℕ) = 0 then α else if (i : ℕ) = m then -β else 0

/-- **The column weight** `(β, …, β, 0) ∈ ℤ^{m+1}` (`Sym^β` of the dual, shifted by `β`). -/
def colW (m β : ℕ) : Fin (m + 1) → ℤ := fun i => if (i : ℕ) = m then 0 else β

/-- **`Har_m(α, β) = C(α+m, m)·C(β+m, m) − C(α−1+m, m)·C(β−1+m, m)`**, the dimension of `fl(α, β)` for `GL_{m+1}`
(`dimW_flatW`; for `m ≥ 1` the second term is `0` when `α = 0` or `β = 0`). -/
def har (m α β : ℕ) : ℕ := (α + m).choose m * (β + m).choose m - (α + m - 1).choose m * (β + m - 1).choose m

/-- **Flat weights are dominant.** -/
theorem antitone_flatW (m α β : ℕ) : Antitone (flatW m α β) := fun i j (h : (i : ℕ) ≤ j) => by
  have := j.isLt
  simp only [flatW]
  split_ifs <;> omega

/-- **`|fl(α, β)| = α − β`** (`m ≥ 1`). -/
theorem sum_flatW {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) : ∑ i, flatW m α β i = (α : ℤ) - β := by
  rw [Fintype.sum_eq_add 0 (Fin.last m) (by simp [Fin.ext_iff]; omega) fun i hi => by
    have h1 : (i : ℕ) ≠ 0 := fun h => hi.1 (Fin.ext h)
    have h2 : (i : ℕ) ≠ m := fun h => hi.2 (Fin.ext h)
    simp [flatW, h1, h2]]
  simp [flatW, show m ≠ 0 by omega]
  ring

/-- **`|(β, …, β, 0)| = m·β`.** -/
theorem sum_colW (m β : ℕ) : ∑ i, colW m β i = m * (β : ℤ) := by
  rw [Fin.sum_univ_castSucc]
  simp [colW, Fin.val_castSucc, Fin.val_last, (Fin.is_lt _).ne]

/-- **The strips over a column**: the horizontal `α`-strips over `(β, …, β, 0)` are the `fl(α − j, β − j) + β`,
`j ≤ min(α, β)`. -/
theorem sum_strip_colW {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) :
    ∑ μ ∈ strip (colW m β) α, dimW (m + 1) μ =
      ∑ j ∈ range (min α β + 1), dimW (m + 1) (flatW m (α - j) (β - j)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsc := sum_colW (m + 1) β
  have key : ∀ μ ∈ strip (colW (m + 1) β) α, (∀ i : Fin (m + 2), (i : ℕ) ≠ 0 → (i : ℕ) ≠ m + 1 → μ i = β) ∧
      0 ≤ μ (Fin.last _) ∧ μ (Fin.last _) ≤ β ∧ μ 0 + μ (Fin.last _) = α + β ∧ (β : ℤ) ≤ μ 0 := by
    intro μ hμ
    obtain ⟨⟨h0a, -⟩, hs, hsum⟩ := mem_strip.1 hμ
    simp only [colW, Fin.val_zero, show (0 : ℕ) ≠ m + 1 by omega, ↓reduceIte] at h0a
    have hmid : ∀ i : Fin (m + 2), (i : ℕ) ≠ 0 → (i : ℕ) ≠ m + 1 → μ i = β := by
      intro i h0 hl
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (Fin.ext_iff.not.2 h0)
      have := hs i
      have hi := i.isLt
      simp only [colW, Fin.val_succ, Fin.val_castSucc] at this hl
      simp only [hl, ↓reduceIte, show (i : ℕ) ≠ m + 1 by omega] at this
      omega
    have hlast := hs (Fin.last m)
    simp only [colW, Fin.succ_last, Fin.val_last, Fin.val_castSucc, ↓reduceIte,
      show m ≠ m + 1 by omega] at hlast
    have hD : ∑ i, (μ i - colW (m + 1) β i) = μ 0 - β + μ (Fin.last _) := by
      rw [Fintype.sum_eq_add 0 (Fin.last _) (by simp [Fin.ext_iff]) fun i hi => by
        have h1 : (i : ℕ) ≠ 0 := fun h => hi.1 (Fin.ext h)
        have h2 : (i : ℕ) ≠ m + 1 := fun h => hi.2 (Fin.ext h)
        simp [colW, hmid i h1 h2, h2]]
      simp [colW]
    rw [sum_sub_distrib, hsum] at hD
    exact ⟨hmid, hlast.1, hlast.2, by linarith, h0a⟩
  symm
  refine sum_nbij' (fun j i => flatW (m + 1) (α - j) (β - j) i + β) (fun μ => (μ (Fin.last _)).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_range] at hj
    have hj' : j ≤ α ∧ j ≤ β := by omega
    have e1 : ((α - j : ℕ) : ℤ) = α - j := Nat.cast_sub hj'.1
    have e2 : ((β - j : ℕ) : ℤ) = β - j := Nat.cast_sub hj'.2
    rw [mem_strip]
    refine ⟨⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_⟩
    · simp only [flatW, colW, Fin.val_zero, ↓reduceIte, e1]; omega
    · simp only [flatW, colW, Fin.val_zero, ↓reduceIte, e1]; omega
    · have := i.isLt
      simp only [flatW, colW, Fin.val_succ, e1, e2]
      split_ifs <;> first | contradiction | omega
    · have := i.isLt
      simp only [flatW, colW, Fin.val_succ, Fin.val_castSucc, e1, e2]
      split_ifs <;> first | contradiction | omega
    · rw [sum_add_distrib, sum_flatW (by omega), hsc]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, e1, e2]
      push_cast
      ring
  · intro μ hμ
    obtain ⟨-, h1, h2, h3, h4⟩ := key μ hμ
    rw [mem_range]
    omega
  · intro j hj
    rw [mem_range] at hj
    have e2 : ((β - j : ℕ) : ℤ) = β - j := Nat.cast_sub (by omega)
    simp only [flatW, Fin.val_last, show m + 1 ≠ 0 by omega, ↓reduceIte, e2]
    omega
  · intro μ hμ
    obtain ⟨hmid, h1, h2, h3, h4⟩ := key μ hμ
    have hj := Int.toNat_of_nonneg h1
    have e1 : ((α - (μ (Fin.last _)).toNat : ℕ) : ℤ) = α - (μ (Fin.last _)).toNat := Nat.cast_sub (by omega)
    have e2 : ((β - (μ (Fin.last _)).toNat : ℕ) : ℤ) = β - (μ (Fin.last _)).toNat := Nat.cast_sub (by omega)
    funext i
    simp only [flatW, e1, e2, hj]
    split_ifs with ha hb
    · rw [show i = 0 from Fin.ext ha]; omega
    · rw [show i = Fin.last _ from Fin.ext hb]; omega
    · rw [hmid i ha hb]; ring
  · intro j _
    exact (dimW_add_const (antitone_flatW _ _ _) β).symm

/-- **The one-row weight**: `dimW(α, 0, …, 0) = C(α + m, m)` (`Sym^α`; Pieri over the trivial weight). -/
theorem dimW_flatW_zero {m : ℕ} (hm : 1 ≤ m) (α : ℕ) : dimW (m + 1) (flatW m α 0) = (α + m).choose m := by
  have h := dimW_mul_choose (colW m 0) α
  have h0 : colW m 0 = 0 := funext fun i => by simp [colW]
  rw [sum_strip_colW hm, h0, dimW_zero, one_mul] at h
  simpa using h.symm

/-- **The column weight**: `dimW(β, …, β, 0) = C(β + m, m)` (duality and translation from the row). -/
theorem dimW_colW {m : ℕ} (hm : 1 ≤ m) (β : ℕ) : dimW (m + 1) (colW m β) = (β + m).choose m := by
  have e : colW m β = fun i => -flatW m β 0 i.rev + β := funext fun i => by
    have := i.isLt
    simp only [colW, flatW, Fin.val_rev]
    split_ifs <;> omega
  rw [e, dimW_add_const (fun a b h => by simpa using antitone_flatW m β 0 (Fin.rev_le_rev.2 h)) β,
    dimW_dual (antitone_flatW m β 0), dimW_flatW_zero hm]

/-- **The flat sum** (`Sym^α ⊗ Sym^β∨ = ⊕_j V(fl(α − j, β − j))`):
`Σ_{j ≤ min(α, β)} dimW fl(α − j, β − j) = C(α + m, m)·C(β + m, m)`. -/
theorem sum_dimW_flatW {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) :
    ∑ j ∈ range (min α β + 1), dimW (m + 1) (flatW m (α - j) (β - j)) =
      (α + m).choose m * (β + m).choose m := by
  rw [← sum_strip_colW hm, ← dimW_mul_choose, dimW_colW hm, mul_comm]

/-- **`dim fl(α, β) = Har_m(α, β)`** (A-N10; `m + 1 = k ≥ 2`). -/
theorem dimW_flatW {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) : dimW (m + 1) (flatW m α β) = har m α β := by
  have hS := sum_dimW_flatW hm α β
  rw [har]
  by_cases h : α = 0 ∨ β = 0
  · rw [show min α β = 0 by omega, zero_add, sum_range_one] at hS
    simp only [Nat.sub_zero] at hS
    have h0 : (α + m - 1).choose m * (β + m - 1).choose m = 0 := by
      rcases h with rfl | rfl
      · rw [Nat.choose_eq_zero_of_lt (show 0 + m - 1 < m by omega), zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (show 0 + m - 1 < m by omega), mul_zero]
    rw [h0, Nat.sub_zero, hS]
  · obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    rw [show min (a + 1) (b + 1) + 1 = (min a b + 1) + 1 by omega, sum_range_succ'] at hS
    simp only [Nat.add_sub_add_right, Nat.sub_zero, sum_dimW_flatW hm a b] at hS
    rw [show a + 1 + m - 1 = a + m by omega, show b + 1 + m - 1 = b + m by omega, ← hS, Nat.add_sub_cancel_left]

/-- **The `Har` sum**: `Σ_{j ≤ min(α, β)} Har_m(α − j, β − j) = C(α + m, m)·C(β + m, m)`. -/
theorem sum_har {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) :
    ∑ j ∈ range (min α β + 1), har m (α - j) (β - j) = (α + m).choose m * (β + m).choose m := by
  simp_rw [← dimW_flatW hm]
  exact sum_dimW_flatW hm α β

/-- **The `Har` sum over the tops** (A-N10): `Σ_{j ∈ J(A, B)} ∏_s Har_m(A_s − j_s, B_s − j_s) = dim H(A, B) =
∏_s C(A_s + m, m)·C(B_s + m, m)`, `J(A, B) = ∏_s [0, min(A_s, B_s)]`. -/
theorem sum_prod_har {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m) (A B : ι → ℕ) :
    ∑ j ∈ Fintype.piFinset (fun s => range (min (A s) (B s) + 1)), ∏ s, har m (A s - j s) (B s - j s) =
      ∏ s, (A s + m).choose m * (B s + m).choose m := by
  rw [← Finset.prod_univ_sum (fun s => range (min (A s) (B s) + 1)) fun s y => har m (A s - y) (B s - y)]
  exact prod_congr rfl fun s _ => sum_har hm (A s) (B s)

/-! ## Subspace counts over a finite field -/

section Subspaces

open Module

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **`q^{r(k−r)}` subspaces of dimension `r`** in `F_q^k` (the graphs of the linear maps `F^r → F^{k−r}`, the big
cell of the Grassmannian; `[k, r]_q ≥ q^{r(k−r)}`). -/
theorem pow_le_card_finrank {r : ℕ} (hr : r ≤ finrank F V) :
    Nat.card F ^ (r * (finrank F V - r)) ≤ Nat.card {U : Submodule F V // finrank F U = r} := by
  set k := finrank F V
  have hP : finrank F ((Fin r → F) × (Fin (k - r) → F)) = k := by simp; omega
  let e := LinearEquiv.ofFinrankEq _ V hP
  let G : ((Fin r → F) →ₗ[F] (Fin (k - r) → F)) → {U : Submodule F V // finrank F U = r} := fun A =>
    ⟨(LinearMap.range (LinearMap.id.prod A)).map e.toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj fun x y h => congrArg Prod.fst h]
      simp⟩
  have hG : Function.Injective G := by
    intro A B h
    have h2 : LinearMap.range (LinearMap.id.prod A) = LinearMap.range (LinearMap.id.prod B) :=
      Submodule.map_injective_of_injective e.injective (congrArg Subtype.val h)
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, hy⟩ : (x, A x) ∈ LinearMap.range (LinearMap.id.prod B) := h2 ▸ ⟨x, rfl⟩
    have h1 : y = x := congrArg Prod.fst hy
    have h2 : B y = A x := congrArg Prod.snd hy
    rw [← h2, h1]
  have : Finite V := Module.finite_of_finite F
  calc Nat.card F ^ (r * (k - r)) = Nat.card ((Fin r → F) →ₗ[F] (Fin (k - r) → F)) := by
        rw [Nat.card_congr LinearMap.toMatrix'.toEquiv, Matrix, Nat.card_fun, Nat.card_fun]
        simp [pow_mul]
    _ ≤ _ := Nat.card_le_card_of_injective G hG

/-- **`q^{r(k−r)}` subspaces of codimension `r`** in `F_q^k` (the count of the edges of type `r`, L6 N1(d)). -/
theorem pow_le_card_codim {r : ℕ} (hr : r ≤ finrank F V) :
    Nat.card F ^ (r * (finrank F V - r)) ≤ Nat.card {U : Submodule F V // finrank F U + r = finrank F V} := by
  have h := pow_le_card_finrank (F := F) (V := V) (r := finrank F V - r) (by omega)
  rw [show finrank F V - (finrank F V - r) = r by omega, mul_comm] at h
  exact h.trans_eq (Nat.card_congr (Equiv.subtypeEquivRight fun U => by omega))

omit [Finite F] in
/-- **The hyperplane count** `#{U : codim U = 1}·(q − 1) = q^k − 1` (by duality, the lines of the dual space). -/
theorem card_hyperplanes :
    Nat.card {U : Submodule F V // finrank F U + 1 = finrank F V} * (Nat.card F - 1) =
      Nat.card F ^ finrank F V - 1 := by
  have e : {U : Submodule F V // finrank F U + 1 = finrank F V} ≃
      {W : Submodule F (Dual F V) // finrank F W = 1} :=
    (Subspace.orderIsoFiniteDimensional.toEquiv.trans OrderDual.ofDual).subtypeEquiv fun U => by
      have := Subspace.finrank_add_finrank_dualAnnihilator_eq U
      change _ ↔ finrank F U.dualAnnihilator = 1
      omega
  rw [Nat.card_congr (e.trans (Projectivization.equivSubmodule F (Dual F V)).symm),
    ← Projectivization.card, Module.natCard_eq_pow_finrank (K := F), Subspace.dual_finrank_eq]

end Subspaces

end WeylCount
