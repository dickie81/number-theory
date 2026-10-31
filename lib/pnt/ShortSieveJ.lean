import ShortSieveRel
import ShortSieveExpand

/-!
# Type I terms: tuples of primes with a sifted cofactor, cut out by log-linear conditions

A Type I term of Li's decomposition sums `S(A_{∏g}, x^ν)` over tuples `g` of primes: the `v ≤ x` free of primes below
`x^ν` with `∏ g · v ∈ (x − y, x]`. Li's Lemmas 3.1 and 3.2 give its asymptotic formula for `g` in a box (the
products of its groups decomposable), summed over all `v`. This module turns such a per-box estimate into the
asymptotic formula for the pairs `(g, v)` cut out by conditions `Σ_j e_j log g_j + f log v ≤ b` (`JAtom`): the
boxes are those of `g` alone, and a box that straddles a condition has its pairs near the boundary, which is thin in
the comparison interval once `v` is written as its tuple of primes (`card_nearJ_le`, from
`ShortSieveTerm.near_uniform`).
-/

open Finset Real Filter

namespace ShortSieveJ

open ShortSieveBoxes ShortSieveTerm ShortSieveExpand ShortSieveRel

open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Conditions on a tuple of primes and a sifted cofactor -/

/-- A log-linear condition on a tuple `g` of primes and a cofactor `v`: `Σ_j e_j log g_j + f log v ≤ b(x)`, or
`< b(x)` when `strict`. -/
structure JAtom (ι : Type*) where
  e : ι → ℝ
  f : ℝ
  b : ℝ → ℝ
  strict : Bool

/-- The value `Σ_j e_j log g_j + f log v`. -/
noncomputable def JAtom.val (A : JAtom ι) (g : ι → ℕ) (v : ℕ) : ℝ :=
  ∑ j, A.e j * Real.log (g j) + A.f * Real.log v

/-- The condition holds at `(g, v)`. -/
def JAtom.Holds (A : JAtom ι) (x : ℝ) (g : ι → ℕ) (v : ℕ) : Prop :=
  if A.strict then A.val g v < A.b x else A.val g v ≤ A.b x

/-- The pairs `(g, v)`: `g` a tuple of primes in `(x^c, x²)`, `v ≤ x` free of primes below `x^ν`, with the
conditions. -/
noncomputable def jcut (c ν : ℝ) (atoms : List (JAtom ι)) (x : ℝ) : Finset ((ι → ℕ) × ℕ) :=
  ((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime) ×ˢ Icc 1 ⌊x⌋₊).filter
    fun w => SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧ ∀ A ∈ atoms, A.Holds x w.1 w.2

/-- `S(A_{∏g}, x^ν)` for `A = (x − y, x]`: the `v ≤ x` free of primes below `x^ν` with `∏ g · v ∈ (x − y, x]`. -/
noncomputable def sA (ν x y : ℝ) (g : ι → ℕ) : ℕ :=
  #{v ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough ⌈x ^ ν⌉₊ v ∧ x - y < (((∏ j, g j) * v : ℕ) : ℝ) ∧
    (((∏ j, g j) * v : ℕ) : ℝ) ≤ x}

/-! ### The boundary of a condition, from the tuples of primes -/

/-- The condition on the tuple of `g` and the prime factors of `v`: `f` on each of them. -/
def JAtom.lift (A : JAtom ι) (r : ℕ) : LAtom (ι ⊕ Fin r) :=
  ⟨Sum.elim A.e fun _ => A.f, A.b, A.strict⟩

/-- The tuple of a pair: `g`, then the first `r` prime factors of `v`. -/
def jexpand (r : ℕ) (w : (ι → ℕ) × ℕ) : ι ⊕ Fin r → ℕ := Sum.elim w.1 fun i => fac w.2 i

/-- A position below the number of prime factors holds a prime factor. -/
theorem fac_mem {v r : ℕ} (hr : v.primeFactorsList.length = r) (i : Fin r) : fac v i ∈ v.primeFactorsList := by
  rw [fac, List.getD_eq_getElem _ _ (by rw [hr]; exact i.2)]
  exact List.getElem_mem _

omit [DecidableEq ι] in
theorem prod_jexpand {r : ℕ} {w : (ι → ℕ) × ℕ} (hv : w.2 ≠ 0) (hr : w.2.primeFactorsList.length = r) :
    ∏ t, jexpand r w t = (∏ j, w.1 j) * w.2 := by
  rw [Fintype.prod_sum_type]
  simp only [jexpand, Sum.elim_inl, Sum.elim_inr]
  rw [prod_fac hv hr]

omit [DecidableEq ι] in
theorem lift_val (A : JAtom ι) {r : ℕ} {w : (ι → ℕ) × ℕ} (hv : w.2 ≠ 0) (hr : w.2.primeFactorsList.length = r) :
    (A.lift r).val (jexpand r w) = A.val w.1 w.2 := by
  unfold LAtom.val JAtom.lift JAtom.val jexpand
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [← mul_sum, ← Real.log_prod (fun i _ => by
    exact_mod_cast (Nat.prime_of_mem_primeFactorsList (fac_mem hr i)).ne_zero), ← Nat.cast_prod, prod_fac hv hr]

/-- A number up to `x` all of whose prime factors are at least `x^ν` has at most `1/ν` of them, with multiplicity. -/
theorem length_primeFactorsList_le {n : ℕ} {x ν : ℝ} (hx : 1 < x) (hν : 0 < ν) (hn0 : n ≠ 0) (hn : (n : ℝ) ≤ x)
    (hpf : ∀ p ∈ n.primeFactorsList, x ^ ν ≤ p) : (n.primeFactorsList.length : ℝ) ≤ 1 / ν := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hpow : ∀ l : List ℕ, (∀ p ∈ l, x ^ ν ≤ (p : ℝ)) → (x ^ ν) ^ l.length ≤ (l.prod : ℝ) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ]
      rw [mul_comm]
      exact mul_le_mul (hl a List.mem_cons_self) (ih fun p hp => hl p (List.mem_cons_of_mem a hp))
        (pow_nonneg (Real.rpow_pos_of_pos hx0 ν).le _) (Nat.cast_nonneg _)
  have hprod : ((n.primeFactorsList.prod : ℕ) : ℝ) = n := by rw [Nat.prod_primeFactorsList hn0]
  have h := ((hpow _ hpf).trans hprod.le).trans hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h
  have h' := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) h
  rw [Real.log_rpow hx0] at h'
  rw [le_div_iff₀ hν]
  nlinarith

/-- The pairs near the boundary of a condition: `v ≥ 2` free of primes below `x^ν`, product in the comparison
interval. -/
noncomputable def nearJ (c ν ρ D : ℝ) (A : JAtom ι) (x : ℝ) : Finset ((ι → ℕ) × ℕ) :=
  ((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime) ×ˢ Icc 1 ⌊x⌋₊).filter fun w =>
    SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧ 2 ≤ w.2 ∧ |A.val w.1 w.2 - A.b x| ≤ D ∧
      x - x ^ (1 - ρ) < (((∏ j, w.1 j) * w.2 : ℕ) : ℝ) ∧ (((∏ j, w.1 j) * w.2 : ℕ) : ℝ) ≤ x

/-- **The boundary of a condition on pairs is thin.** For conditions with `e_j ≠ f` for some `j`, the pairs within `D`
of a boundary number at most `C x^{1−ρ}/log² x`: with `r` the number of prime factors of `v` (at most `1/ν`), the
tuple of `g` and the prime factors of `v` lies within `D` of the lifted condition's boundary
(`ShortSieveTerm.near_uniform` on `ι ⊕ Fin r`). -/
theorem card_nearJ_le {c ν ρ D : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hν : 0 < ν) (hρ : 0 < ρ) (hρc : 12 * ρ < c)
    (hρν : 12 * ρ < ν) (hD : 0 ≤ D) (atoms : List (JAtom ι)) (hatoms : ∀ A ∈ atoms, ∃ j, A.e j ≠ A.f) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ A ∈ atoms, ∀ x : ℝ, x₀ ≤ x →
      ((nearJ c ν ρ D A x).card : ℝ) ≤ C * x ^ (1 - ρ) / Real.log x ^ 2 := by
  set c' := min c ν with hc'
  have hc'0 : 0 < c' := lt_min hc hν
  have hc'1 : c' ≤ 1 := (min_le_left _ _).trans hc1
  have hρc' : 12 * ρ < c' := lt_min hρc hρν
  set R := ⌊1 / ν⌋₊ with hR
  -- the thin boundaries of the lifted conditions, for each number of prime factors
  have hr : ∀ r ∈ Icc 1 R, ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ A ∈ atoms, ∀ x : ℝ, x₀ ≤ x →
      ((near c' ρ D (A.lift r) x).card : ℝ) ≤ C * x ^ (1 - ρ) / Real.log x ^ 2 := by
    intro r hr
    have hr1 : 0 < r := (mem_Icc.1 hr).1
    obtain ⟨C, x₀, hC0, hC⟩ := near_uniform (ι := ι ⊕ Fin r) (Sum.inr ⟨0, hr1⟩) hc'0 hc'1 hρ hρc'
      (fun _ => D) (fun _ => hD) (atoms.map (·.lift r)) (by
        intro A' hA'
        obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
        obtain ⟨j, hj⟩ := hatoms A hA
        exact ⟨Sum.inl j, Sum.inl_ne_inr, hj⟩)
    exact ⟨C, x₀, hC0, fun A hA x hx => hC _ (List.mem_map.2 ⟨A, hA, rfl⟩) x hx⟩
  choose! Cr xr hCr0 hCr using hr
  refine ⟨∑ r ∈ Icc 1 R, Cr r, max (∑ r ∈ Icc 1 R, |xr r|) 2, sum_nonneg fun r hr => hCr0 r hr,
    fun A hA x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : ∀ r ∈ Icc 1 R, xr r ≤ x := fun r hr =>
    le_trans (le_abs_self _) (le_trans (single_le_sum (fun r _ => abs_nonneg (xr r)) hr)
      (le_trans (le_max_left _ _) hx))
  -- the number of prime factors of `v` lies in `[1, R]`
  have hmaps : ∀ w ∈ nearJ c ν ρ D A x, w.2.primeFactorsList.length ∈ Icc 1 R := by
    intro w hw
    obtain ⟨hwp, hr, h2, -, -, h4⟩ := mem_filter.1 hw
    have hv0 : w.2 ≠ 0 := by omega
    refine mem_Icc.2 ⟨?_, ?_⟩
    · have : w.2.primeFactorsList ≠ [] := by
        intro h
        rw [Nat.primeFactorsList_eq_nil] at h
        omega
      exact List.length_pos_of_ne_nil this
    · refine Nat.le_floor (length_primeFactorsList_le hx1 hν hv0 ?_ fun p hp => ?_)
      · have hv : w.2 ≤ ⌊x⌋₊ := (mem_Icc.1 (mem_product.1 hwp).2).2
        exact le_trans (by exact_mod_cast hv) (Nat.floor_le hx0.le)
      · have hpge : ⌈x ^ ν⌉₊ ≤ p := by
          by_contra hlt
          exact hr p (not_le.1 hlt) (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
        exact le_trans (Nat.le_ceil _) (by exact_mod_cast hpge)
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  rw [sum_mul, sum_div]
  refine sum_le_sum fun r hr => le_trans ?_ (hCr r hr A hA x (hxr r hr))
  -- one number of prime factors: the tuples of primes
  refine Nat.cast_le.2 (card_le_card_of_injOn (jexpand r) (fun w hw => ?_) (fun w hw w' hw' h => ?_))
  · rw [mem_coe, mem_filter] at hw
    obtain ⟨hwN, hwr⟩ := hw
    obtain ⟨hwp, hrough, h2, hval, h3, h4⟩ := mem_filter.1 hwN
    obtain ⟨hg, hv⟩ := mem_product.1 hwp
    have hv0 : w.2 ≠ 0 := by omega
    have hprod := prod_jexpand hv0 hwr
    have hcast : ((∏ t, jexpand r w t : ℕ) : ℝ) = (((∏ j, w.1 j) * w.2 : ℕ) : ℝ) := by rw [hprod]
    -- every entry is at most the product, hence at most `x`
    have hpos : ∀ t, 0 < jexpand r w t := by
      intro t
      rcases t with j | i
      · exact (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).2.pos
      · exact (Nat.prime_of_mem_primeFactorsList (fac_mem hwr i)).pos
    have hle : ∀ t, (jexpand r w t : ℝ) ≤ x := fun t => by
      have := Nat.le_of_dvd (prod_pos fun t _ => hpos t) (dvd_prod_of_mem _ (mem_univ t))
      calc (jexpand r w t : ℝ) ≤ ((∏ t, jexpand r w t : ℕ) : ℝ) := by exact_mod_cast this
        _ = _ := hcast
        _ ≤ x := h4
    have hx2' : x < x ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 hx1
    rw [mem_coe]
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => SieveRough.mem_primesIn.2 ⟨?_, ?_, ?_⟩,
      ?_, by rw [hcast]; exact h3, by rw [hcast]; exact h4⟩
    · rcases t with j | i
      · exact (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).2
      · exact Nat.prime_of_mem_primeFactorsList (fac_mem hwr i)
    · rcases t with j | i
      · have h1 := (mem_Ioo.1 (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).1).1
        have h5 : x ^ c < (w.1 j : ℝ) := by
          have := Nat.lt_floor_add_one (x ^ c)
          have h6 : ((⌊x ^ c⌋₊ : ℕ) : ℝ) + 1 ≤ w.1 j := by exact_mod_cast h1
          linarith
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (min_le_left _ _)) h5.le
      · have hp := fac_mem hwr i
        have hpge : ⌈x ^ ν⌉₊ ≤ fac w.2 i := by
          by_contra hlt
          exact hrough _ (not_le.1 hlt) (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (min_le_right _ _))
          (le_trans (Nat.le_ceil _) (by exact_mod_cast hpge))
    · exact lt_of_le_of_lt (hle t) hx2'
    · rw [lift_val A hv0 hwr]; exact hval
  · -- the tuple determines the pair
    rw [mem_coe, mem_filter] at hw hw'
    have hv0 : w.2 ≠ 0 := by have := (mem_filter.1 hw.1).2.2.1; omega
    have hv0' : w'.2 ≠ 0 := by have := (mem_filter.1 hw'.1).2.2.1; omega
    have h1 : w.1 = w'.1 := funext fun j => congrFun h (Sum.inl j)
    have h2 : w.2 = w'.2 := by
      rw [← prod_fac hv0 hw.2, ← prod_fac hv0' hw'.2]
      exact prod_congr rfl fun i _ => congrFun h (Sum.inr i)
    exact Prod.ext h1 h2


/-! ### The pairs of a box -/

/-- The product `∏ g · v` of a pair. -/
def jprod (w : (ι → ℕ) × ℕ) : ℕ := (∏ j, w.1 j) * w.2

omit [DecidableEq ι] in
/-- **The pairs of a box are the box's Type I sums.** For `y ≤ x/2`, the pairs `(g, v)`, `g ∈ T`, `v ≤ x` free of primes
below `x^ν`, with product in `(x/2, x]`, have `Σ [x − y < ∏g·v ≤ x] = Σ_{g ∈ T} S(A_{∏g}, x^ν)`. -/
theorem sum_full_eq (T : Finset (ι → ℕ)) (ν : ℝ) {x y : ℝ} (hy : y ≤ x / 2) :
    ∑ w ∈ (T ×ˢ Icc 1 ⌊x⌋₊).filter (fun w : (ι → ℕ) × ℕ => SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧
        x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x),
      (if x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x then (1 : ℝ) else 0) = ∑ g ∈ T, (sA ν x y g : ℝ) := by
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun g _ => ?_
  rw [sA, natCast_card_filter]
  refine sum_congr rfl fun v _ => ?_
  simp only [jprod]
  by_cases h1 : SieveTree.rough ⌈x ^ ν⌉₊ v
  · by_cases h2 : x - y < (((∏ j, g j) * v : ℕ) : ℝ) ∧ (((∏ j, g j) * v : ℕ) : ℝ) ≤ x
    · have h3 : x / 2 < (((∏ j, g j) * v : ℕ) : ℝ) := by linarith [h2.1]
      rw [ite_eq_left ⟨h1, h3, h2.2⟩, ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
    · rw [ite_eq_right h2, ite_self, ite_eq_right (fun h : SieveTree.rough ⌈x ^ ν⌉₊ v ∧ _ => h2 h.2)]
  · simp [h1]

omit [DecidableEq ι] in
/-- **The variation of a condition over a box.** For pairs whose `g`'s are within ratio `r²` coordinatewise and whose
products lie in `(x/2, x]`, the condition's values differ by at most
`Σ_j |e_j|·2 log r + |f|(log 2 + 2d log r)`. -/
theorem abs_jval_sub_le (A : JAtom ι) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) {w w' : (ι → ℕ) × ℕ}
    (hg : ∀ j, 0 < w.1 j) (hg' : ∀ j, 0 < w'.1 j) (hv : 0 < w.2) (hv' : 0 < w'.2)
    (h1 : ∀ j, (w.1 j : ℝ) ≤ r ^ 2 * w'.1 j) (h2 : ∀ j, (w'.1 j : ℝ) ≤ r ^ 2 * w.1 j)
    (hP : x / 2 < (jprod w : ℝ)) (hP1 : (jprod w : ℝ) ≤ x) (hP' : x / 2 < (jprod w' : ℝ)) (hP1' : (jprod w' : ℝ) ≤ x) :
    |A.val w.1 w.2 - A.val w'.1 w'.2| ≤
      (∑ j, |A.e j|) * (2 * Real.log r) + |A.f| * (Real.log 2 + Fintype.card ι * (2 * Real.log r)) := by
  have hpos : ∀ j, (0 : ℝ) < w.1 j := fun j => by exact_mod_cast hg j
  have hpos' : ∀ j, (0 : ℝ) < w'.1 j := fun j => by exact_mod_cast hg' j
  -- each coordinate's `log` moves by at most `2 log r`
  have hlog : ∀ j, |Real.log (w.1 j) - Real.log (w'.1 j)| ≤ 2 * Real.log r := by
    intro j
    have e : 2 * Real.log r = Real.log (r ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e, abs_le]
    constructor
    · have := Real.log_le_log (hpos' j) (h2 j)
      rw [Real.log_mul (by positivity) (hpos j).ne'] at this
      linarith
    · have := Real.log_le_log (hpos j) (h1 j)
      rw [Real.log_mul (by positivity) (hpos' j).ne'] at this
      linarith
  -- the products' `log`s move by at most `log 2`
  have hjp : ∀ w : (ι → ℕ) × ℕ, (∀ j, 0 < w.1 j) → 0 < w.2 →
      Real.log (jprod w) = ∑ j, Real.log (w.1 j) + Real.log w.2 := by
    intro w hg hv
    simp only [jprod]
    push_cast
    rw [Real.log_mul (prod_pos fun j _ => by exact_mod_cast hg j).ne' (by exact_mod_cast hv.ne'),
      Real.log_prod fun j _ => by exact_mod_cast (hg j).ne']
  have hPw : |Real.log (jprod w) - Real.log (jprod w')| ≤ Real.log 2 := by
    have hp0 : (0 : ℝ) < jprod w := by linarith
    have hp0' : (0 : ℝ) < jprod w' := by linarith
    rw [abs_le]
    constructor
    · have : (jprod w' : ℝ) ≤ 2 * jprod w := by linarith
      have := Real.log_le_log hp0' this
      rw [Real.log_mul (by norm_num) hp0.ne'] at this
      linarith
    · have : (jprod w : ℝ) ≤ 2 * jprod w' := by linarith
      have := Real.log_le_log hp0 this
      rw [Real.log_mul (by norm_num) hp0'.ne'] at this
      linarith
  have hsum : |∑ j, Real.log (w.1 j) - ∑ j, Real.log (w'.1 j)| ≤ Fintype.card ι * (2 * Real.log r) := by
    rw [← sum_sub_distrib]
    calc |∑ j, (Real.log (w.1 j) - Real.log (w'.1 j))| ≤ ∑ j, |Real.log (w.1 j) - Real.log (w'.1 j)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, 2 * Real.log r := sum_le_sum fun j _ => hlog j
      _ = Fintype.card ι * (2 * Real.log r) := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hvlog : |Real.log w.2 - Real.log w'.2| ≤ Real.log 2 + Fintype.card ι * (2 * Real.log r) := by
    have e1 := hjp w hg hv
    have e2 := hjp w' hg' hv'
    have : Real.log w.2 - Real.log w'.2 = (Real.log (jprod w) - Real.log (jprod w')) -
        (∑ j, Real.log (w.1 j) - ∑ j, Real.log (w'.1 j)) := by rw [e1, e2]; ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add hPw hsum)
  unfold JAtom.val
  have : (∑ j, A.e j * Real.log (w.1 j) + A.f * Real.log w.2) - (∑ j, A.e j * Real.log (w'.1 j) +
      A.f * Real.log w'.2) = ∑ j, A.e j * (Real.log (w.1 j) - Real.log (w'.1 j)) +
        A.f * (Real.log w.2 - Real.log w'.2) := by
    have hs : ∑ j, A.e j * (Real.log (w.1 j) - Real.log (w'.1 j)) =
        ∑ j, A.e j * Real.log (w.1 j) - ∑ j, A.e j * Real.log (w'.1 j) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    rw [hs]; ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · calc |∑ j, A.e j * (Real.log (w.1 j) - Real.log (w'.1 j))|
        ≤ ∑ j, |A.e j * (Real.log (w.1 j) - Real.log (w'.1 j))| := abs_sum_le_sum_abs _ _
      _ = ∑ j, |A.e j| * |Real.log (w.1 j) - Real.log (w'.1 j)| := by simp only [abs_mul]
      _ ≤ ∑ j, |A.e j| * (2 * Real.log r) := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hlog j) (abs_nonneg _)
      _ = (∑ j, |A.e j|) * (2 * Real.log r) := by rw [sum_mul]
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hvlog (abs_nonneg _)


/-! ### The asymptotic formula -/

/-- **Type I terms cut out by log-linear conditions, from a relative estimate on boxes.** Let `0 < c ≤ 1`, `ν, ρ > 0`
with `12ρ < c` and `12ρ < ν`, conditions each with `e_j ≠ f` for some `j`, and `η > 0` such that for large `x` the
pairs of the cut with product in `(x/2, x]` have `∏ g ≤ x^{1−η}`. Suppose that for every `ε > 0`, for large `x` and
`x^θ ≤ y ≤ x^{1−ρ}`, every box `(N_j, M_j]` (`N_j ≥ x^{c/2}`, `M_j ≤ 2^{1/d} N_j`) that holds the `g` of a pair of the
cut with product in `(x/2, x]` has `Σ_g S(A_{∏g}, x^ν)` within `ε` of `(y/x^{1−ρ}) Σ_g S(B_{∏g}, x^ν)`, relatively
(Li's Lemmas 3.1 and 3.2). Then there is `C` such that for `ε ∈ (0, 1]`, large `x` and `x^θ ≤ y ≤ x^{1−ρ}`, the cut's
pairs with product in `(x − y, x]` number `(y/x^{1−ρ})` times those in `(x − x^{1−ρ}, x]`, up to `ε` relatively and
`C y/log² x`.

The boxes are those of `g` (`ShortSieveTerm.grid`); a box's pairs with product in `(x/2, x]` give its Type I sums
(`sum_full_eq`), and a box that straddles a condition has its pairs near the boundary (`abs_jval_sub_le`, with
`v ≥ x^η/4` from the bound on `∏ g`), which is thin (`card_nearJ_le`). -/
theorem abs_card_jcut_sub_le (v₀ : ι) {c ν θ ρ η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hν : 0 < ν)
    (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hρν : 12 * ρ < ν) (hη : 0 < η)
    (atoms : List (JAtom ι)) (hatoms : ∀ A ∈ atoms, ∃ j, A.e j ≠ A.f)
    (hsmall : ∀ᶠ x in atTop, ∀ w ∈ jcut c ν atoms x, x / 2 < (jprod w : ℝ) → (jprod w : ℝ) ≤ x →
      ((∏ j, w.1 j : ℕ) : ℝ) ≤ x ^ (1 - η))
    (hbox : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ N M : ι → ℕ,
      (∀ j, x ^ (c / 2) ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ j, (M j : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / Fintype.card ι) * N j) →
      (∃ w ∈ jcut c ν atoms x, x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x ∧ w.1 ∈ ShortSieveTypeII.tuples N M) →
      |∑ g ∈ ShortSieveTypeII.tuples N M, (sA ν x y g : ℝ) -
        y / x ^ (1 - ρ) * ∑ g ∈ ShortSieveTypeII.tuples N M, (sA ν x (x ^ (1 - ρ)) g : ℝ)| ≤
        ε * (y / x ^ (1 - ρ)) * ∑ g ∈ ShortSieveTypeII.tuples N M, (sA ν x (x ^ (1 - ρ)) g : ℝ)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(#{w ∈ jcut c ν atoms x | x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{w ∈ jcut c ν atoms x | x - x ^ (1 - ρ) < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) * #{w ∈ jcut c ν atoms x | x - x ^ (1 - ρ) < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} +
          C * y / Real.log x ^ 2 := by
  classical
  set d : ℕ := Fintype.card ι with hd_def
  have hd : 0 < d := Fintype.card_pos_iff.2 ⟨v₀⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the grid's ratio `r = 2^{1/(2d)}`, with `(r²)^d = 2`
  set r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (2 * d)) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have hr2 : r ≤ 2 := by
    calc r ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          rw [div_le_one (by positivity)]; linarith)
      _ = 2 := Real.rpow_one 2
  have hrd : (r ^ 2) ^ d = 2 := by
    rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  have hr0 : 0 < r := by linarith
  have hr21 : 1 ≤ r ^ 2 := one_le_pow₀ hr1.le
  have hlr : 0 < Real.log r := Real.log_pos hr1
  have hr2d : r ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / d) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    field_simp
  -- the boundaries of the conditions
  set DA : JAtom ι → ℝ := fun A =>
    (∑ j, |A.e j|) * (2 * Real.log r) + |A.f| * (Real.log 2 + d * (2 * Real.log r)) with hDA
  have hDA0 : ∀ A, 0 ≤ DA A := fun A =>
    add_nonneg (mul_nonneg (sum_nonneg fun j _ => abs_nonneg _) (by positivity))
      (mul_nonneg (abs_nonneg _) (add_nonneg (Real.log_nonneg (by norm_num)) (by positivity)))
  set D₀ : ℝ := 2 * ∑ A ∈ atoms.toFinset, DA A with hD₀
  have hD₀0 : 0 ≤ D₀ := mul_nonneg (by norm_num) (sum_nonneg fun A _ => hDA0 A)
  have hDle : ∀ A ∈ atoms, 2 * DA A ≤ D₀ := fun A hA =>
    mul_le_mul_of_nonneg_left (single_le_sum (fun A _ => hDA0 A) (List.mem_toFinset.2 hA)) (by norm_num)
  obtain ⟨Cn, xn, hCn, hnear⟩ := card_nearJ_le hc hc1 hν hρ hρc hρν hD₀0 atoms hatoms
  refine ⟨2 * atoms.length * Cn, fun ε hε hε1 => ?_⟩
  -- the conditions on `x`
  have ev4 : ∀ᶠ x : ℝ in atTop, 2 / (r - 1) ≤ x ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop _
  have ev5 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (c / 2) := (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev7 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ ρ := (tendsto_rpow_atTop hρ).eventually_ge_atTop _
  have ev8 : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ η := (tendsto_rpow_atTop hη).eventually_ge_atTop _
  filter_upwards [hbox ε hε, hsmall, eventually_ge_atTop xn, eventually_ge_atTop (3 : ℝ), ev4, ev5, ev7, ev8]
    with x hboxx hsmallx hxn hx3 hx4 hx5 hx7 hx8
  intro y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 θ) hy1
  set y₁ : ℝ := x ^ (1 - ρ) with hy₁
  have hy₁0 : 0 < y₁ := Real.rpow_pos_of_pos hx0 _
  have hy₁x : y₁ ≤ x / 2 := by
    have e : y₁ = x / x ^ ρ := by rw [hy₁, Real.rpow_sub hx0, Real.rpow_one]
    rw [e]; exact div_le_div_of_nonneg_left hx0.le (by norm_num) hx7
  have hyx : y ≤ x / 2 := hy2.trans hy₁x
  have hxc0 : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  have hxc_half : x ^ c = x ^ (c / 2) * x ^ (c / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  have ha : 2 ≤ x ^ c * (r - 1) := by
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)).1 hx4; linarith
  have hx2 : x < x ^ (2 : ℝ) := by
    rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 (by linarith)
  -- the grid
  set I : ℕ := ⌈2 * Real.log x / Real.log r⌉₊ with hI
  set G := grid (x ^ c) r I with hG
  have hbot : ⌊x ^ c⌋₊ ∈ G := mem_grid.2 ⟨0, Nat.zero_le _, by simp⟩
  have hGge : ∀ e ∈ G, ⌊x ^ c⌋₊ ≤ e := fun e he => by
    obtain ⟨i, -, rfl⟩ := mem_grid.1 he
    exact Nat.floor_le_floor (le_mul_of_one_le_right hxc0.le (one_le_pow₀ hr1.le))
  have htop : x ^ (2 : ℝ) ≤ x ^ c * r ^ I := by
    have hrI : x ^ (2 : ℝ) ≤ r ^ I := by
      rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 _), ← Real.exp_log (pow_pos hr0 I), Real.log_rpow hx0,
        Real.log_pow]
      refine Real.exp_le_exp.2 ?_
      have h := Nat.le_ceil (2 * Real.log x / Real.log r)
      rw [← hI, div_le_iff₀ hlr] at h
      linarith
    calc x ^ (2 : ℝ) ≤ r ^ I := hrI
      _ ≤ x ^ c * r ^ I := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hx1 hc.le)
  have htopG : ⌊x ^ c * r ^ I⌋₊ ∈ G := mem_grid.2 ⟨I, le_rfl, rfl⟩
  have hfloor : x ^ (c / 2) ≤ (⌊x ^ c⌋₊ : ℝ) := by
    have h1 : x ^ c - 1 < ⌊x ^ c⌋₊ := Nat.sub_one_lt_floor _
    nlinarith
  -- the pairs with product in `(x/2, x]`
  set S := (jcut c ν atoms x).filter (fun w => x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x) with hS
  have hSmem : ∀ w ∈ S, (∀ j, ⌊x ^ c⌋₊ < w.1 j ∧ (w.1 j : ℝ) < x ^ (2 : ℝ) ∧ (w.1 j).Prime) ∧
      w.2 ∈ Icc 1 ⌊x⌋₊ ∧ SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧ (∀ A ∈ atoms, A.Holds x w.1 w.2) ∧
      x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x := by
    intro w hw
    obtain ⟨hwc, h1, h2⟩ := mem_filter.1 hw
    obtain ⟨hwp, hr', hat⟩ := mem_filter.1 hwc
    obtain ⟨hg, hv⟩ := mem_product.1 hwp
    refine ⟨fun j => ?_, hv, hr', hat, h1, h2⟩
    obtain ⟨hIoo, hp⟩ := mem_filter.1 (Fintype.mem_piFinset.1 hg j)
    obtain ⟨h3, h4⟩ := mem_Ioo.1 hIoo
    exact ⟨h3, Nat.lt_ceil.1 h4, hp⟩
  set Js := Fintype.piFinset fun _ : ι => G with hJs
  set box : (ι → ℕ) × ℕ → (ι → ℕ) := fun w j => idxG G (w.1 j) with hbox
  have hlo : ∀ w ∈ S, ∀ j, ∃ e ∈ G, e < w.1 j := fun w hw j => ⟨_, hbot, ((hSmem w hw).1 j).1⟩
  have hhi : ∀ w ∈ S, ∀ j, ∃ e ∈ G, w.1 j ≤ e := fun w hw j => by
    refine ⟨_, htopG, Nat.le_floor ?_⟩
    exact (((hSmem w hw).1 j).2.1.le).trans htop
  have hboxJs : ∀ w ∈ S, box w ∈ Js := fun w hw =>
    Fintype.mem_piFinset.2 fun j => (idxG_mem (hlo w hw j)).1
  set full : (ι → ℕ) → Finset ((ι → ℕ) × ℕ) := fun J =>
    ((ShortSieveTypeII.tuples J fun j => nextG G (J j)) ×ˢ Icc 1 ⌊x⌋₊).filter fun w =>
      SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧ x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x with hfull_def
  have hfull : ∀ w ∈ S, w ∈ full (box w) := by
    intro w hw
    obtain ⟨hg, hv, hr', -, h1, h2⟩ := hSmem w hw
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_tuples_idxG (fun j => (hg j).2.2) (hlo w hw) (hhi w hw), hv⟩,
      hr', h1, h2⟩
  have hmemfull : ∀ J w, w ∈ full J → w.1 ∈ ShortSieveTerm.full G J ∧ w.2 ∈ Icc 1 ⌊x⌋₊ ∧
      SieveTree.rough ⌈x ^ ν⌉₊ w.2 ∧ x / 2 < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x := by
    intro J w hw
    obtain ⟨hwp, hr', h1, h2⟩ := mem_filter.1 hw
    obtain ⟨hg, hv⟩ := mem_product.1 hwp
    exact ⟨hg, hv, hr', h1, h2⟩
  -- the weights
  set fA : (ι → ℕ) × ℕ → ℝ := fun w => if x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x then 1 else 0 with hfA
  set fB : (ι → ℕ) × ℕ → ℝ := fun w => if x - y₁ < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x then 1 else 0 with hfB
  have hfA0 : ∀ w, 0 ≤ fA w := fun w => by simp only [hfA]; split_ifs <;> norm_num
  have hfB0 : ∀ w, 0 ≤ fB w := fun w => by simp only [hfB]; split_ifs <;> norm_num
  have hJG : ∀ J ∈ Js, ∀ j, J j ∈ G := fun J hJ j => (Fintype.mem_piFinset.1 hJ) j
  -- the entries of a pair of a box are positive
  have hpos : ∀ J w, w ∈ full J → (∀ j, 0 < w.1 j) ∧ 0 < w.2 := fun J w hw => by
    obtain ⟨hg, hv, -⟩ := hmemfull J w hw
    exact ⟨fun j => (mem_full.1 hg j).2.2.pos, (mem_Icc.1 hv).1⟩
  -- the products of the `g`'s of two pairs of a box are within factor `2`
  have hprod2 : ∀ J ∈ Js, ∀ w ∈ full J, ∀ w' ∈ full J, ((∏ j, w.1 j : ℕ) : ℝ) ≤ 2 * ((∏ j, w'.1 j : ℕ) : ℝ) := by
    intro J hJ w hw w' hw'
    push_cast
    calc ∏ j, (w.1 j : ℝ) ≤ ∏ j, (r ^ 2 * w'.1 j) :=
          prod_le_prod₀ (fun j _ => by positivity) fun j _ =>
            le_of_mem_full hr1 hr2 ha (hJG J hJ) (hmemfull J w hw).1 (hmemfull J w' hw').1 j
      _ = (r ^ 2) ^ d * ∏ j, (w'.1 j : ℝ) := by rw [prod_mul_distrib, prod_const, card_univ]
      _ = 2 * ∏ j, (w'.1 j : ℝ) := by rw [hrd]
  -- the relative estimate on a box that meets the pairs
  have hE : ∀ J ∈ Js, (∃ w ∈ S, box w = J) →
      |∑ w ∈ full J, fA w - y / y₁ * ∑ w ∈ full J, fB w| ≤ ε * (y / y₁) * ∑ w ∈ full J, fB w := by
    rintro J hJ ⟨w₀, hw₀S, hw₀J⟩
    have hw₀ : w₀ ∈ full J := hw₀J ▸ hfull w₀ hw₀S
    rw [hfull_def, sum_full_eq _ ν hyx, sum_full_eq _ ν hy₁x]
    have hboxne : ∀ j, ∃ e' ∈ G, J j < e' := fun j =>
      exists_above_of_lt (mem_full.1 (hmemfull J w₀ hw₀).1 j).1 (mem_full.1 (hmemfull J w₀ hw₀).1 j).2.1
    have hnext : ∀ j, (nextG G (J j) : ℝ) ≤ r ^ 2 * J j := fun j =>
      nextG_grid_le hr1 hr2 ha (hJG J hJ j) (hboxne j)
    obtain ⟨-, -, -, -, h1, h2⟩ := hSmem w₀ hw₀S
    refine hboxx y hy1 hy2 J (fun j => nextG G (J j)) (fun j => ?_) (fun j => ?_) (fun j => ?_)
      ⟨w₀, (mem_filter.1 hw₀S).1, h1, h2, (hmemfull J w₀ hw₀).1⟩
    · exact hfloor.trans (by exact_mod_cast hGge _ (hJG J hJ j))
    · exact (nextG_spec (hboxne j)).2.1.le
    · rw [← hr2d]; exact hnext j
  -- a box that straddles the conditions has its pairs in the comparison interval near a boundary
  have hstrad : ∀ J ∈ Js, (∃ w ∈ S, box w = J) → (∃ w ∈ full J, ¬ (w ∈ S ∧ box w = J)) →
      ∑ w ∈ full J, fB w ≤ ∑ A ∈ atoms.toFinset, (((full J).filter (· ∈ nearJ c ν ρ D₀ A x)).card : ℝ) := by
    rintro J hJ ⟨w₀, hw₀S, hw₀J⟩ ⟨w', hw', hw'n⟩
    have hw₀ : w₀ ∈ full J := hw₀J ▸ hfull w₀ hw₀S
    obtain ⟨hg', hv', hr', hP', hP1'⟩ := hmemfull J w' hw'
    have hw'J : box w' = J := idx_eq_of_mem_full (hJG J hJ) hg'
    have hw'S : w' ∉ S := fun h => hw'n ⟨h, hw'J⟩
    -- the `g` of a pair of the box is a tuple of primes in `(x^c, x²)`
    have hgrange : ∀ w ∈ full J, w.1 ∈ Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime :=
      by
      intro w hw
      obtain ⟨hg, hv, -, -, hP1⟩ := hmemfull J w hw
      obtain ⟨hgpos, hvpos⟩ := hpos J w hw
      refine Fintype.mem_piFinset.2 fun j => mem_filter.2 ⟨mem_Ioo.2 ⟨?_, ?_⟩, (mem_full.1 hg j).2.2⟩
      · exact lt_of_le_of_lt (hGge _ (hJG J hJ j)) (mem_full.1 hg j).1
      · have hle : w.1 j ≤ jprod w := by
          simp only [jprod]
          exact le_trans (Nat.le_of_dvd (prod_pos fun j _ => hgpos j) (dvd_prod_of_mem _ (mem_univ j)))
            (Nat.le_mul_of_pos_right _ hvpos)
        have : (w.1 j : ℝ) < x ^ (2 : ℝ) := lt_of_le_of_lt (le_trans (by exact_mod_cast hle) hP1) hx2
        exact Nat.lt_ceil.2 this
    -- some condition fails at `w'`
    have hnot : ¬ ∀ A ∈ atoms, A.Holds x w'.1 w'.2 := by
      intro hall
      exact hw'S (mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨hgrange w' hw', hv'⟩, hr', hall⟩, hP', hP1'⟩)
    push Not at hnot
    obtain ⟨A, hA, hA'⟩ := hnot
    have hA₀ : A.Holds x w₀.1 w₀.2 := (hSmem w₀ hw₀S).2.2.2.1 A hA
    obtain ⟨hg₀pos, hv₀pos⟩ := hpos J w₀ hw₀
    obtain ⟨hg'pos, hv'pos⟩ := hpos J w' hw'
    obtain ⟨-, -, -, hP₀, hP1₀⟩ := hmemfull J w₀ hw₀
    have hvar : ∀ w ∈ full J, |A.val w.1 w.2 - A.val w₀.1 w₀.2| ≤ DA A := by
      intro w hw
      obtain ⟨hgpos, hvpos⟩ := hpos J w hw
      obtain ⟨hg, -, -, hP, hP1⟩ := hmemfull J w hw
      exact abs_jval_sub_le A hr0 hx0 hgpos hg₀pos hvpos hv₀pos
        (fun j => le_of_mem_full hr1 hr2 ha (hJG J hJ) hg (hmemfull J w₀ hw₀).1 j)
        (fun j => le_of_mem_full hr1 hr2 ha (hJG J hJ) (hmemfull J w₀ hw₀).1 hg j) hP hP1 hP₀ hP1₀
    -- the boundary lies within `DA` above the value at `w₀`
    have hb : |A.val w₀.1 w₀.2 - A.b x| ≤ DA A := by
      have h1 := hvar w' hw'
      unfold JAtom.Holds at hA₀ hA'
      rw [abs_le] at h1 ⊢
      split_ifs at hA₀ hA'
      · have h2 := not_lt.1 hA'
        constructor <;> linarith only [h1.1, h1.2, hA₀, h2]
      · have h2 := not_le.1 hA'
        constructor <;> linarith only [h1.1, h1.2, hA₀, h2]
    have hDA := hDle A hA
    refine le_trans ?_ (single_le_sum (f := fun A => (((full J).filter (· ∈ nearJ c ν ρ D₀ A x)).card : ℝ))
      (fun A _ => Nat.cast_nonneg _) (List.mem_toFinset.2 hA))
    simp only [hfB]
    rw [sum_boole]
    refine Nat.cast_le.2 (card_le_card fun w hw => ?_)
    obtain ⟨hwf, hB1, hB2⟩ := mem_filter.1 hw
    obtain ⟨hg, hv, hrw, hP, hP1⟩ := hmemfull J w hwf
    obtain ⟨hgpos, hvpos⟩ := hpos J w hwf
    -- `v ≥ 2`: the product of `g` is at most `2x^{1−η} ≤ x/4`
    have hv2 : 2 ≤ w.2 := by
      by_contra hlt
      have hv1 : w.2 = 1 := by have := (mem_Icc.1 hv).1; omega
      have hsm := hsmallx w₀ (mem_filter.1 hw₀S).1 hP₀ hP1₀
      have hp2 := hprod2 J hJ w hwf w₀ hw₀
      have hjp : (jprod w : ℝ) = ((∏ j, w.1 j : ℕ) : ℝ) := by simp only [jprod, hv1, mul_one]
      have hxη : x ^ (1 - η) * 8 ≤ x := by
        have e : x ^ (1 - η) = x / x ^ η := by rw [Real.rpow_sub hx0, Real.rpow_one]
        rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hx8 hx0.le
      linarith only [hP, hjp, hp2, hsm, hxη, hx0]
    refine mem_filter.2 ⟨hwf, mem_filter.2 ⟨mem_product.2 ⟨hgrange w hwf, hv⟩, hrw, hv2, ?_, hB1, hB2⟩⟩
    have h1 := hvar w hwf
    calc |A.val w.1 w.2 - A.b x| ≤ |A.val w.1 w.2 - A.val w₀.1 w₀.2| + |A.val w₀.1 w₀.2 - A.b x| :=
          abs_sub_le _ _ _
      _ ≤ DA A + DA A := add_le_add h1 hb
      _ ≤ D₀ := by linarith only [hDA]
  -- the boxes are disjoint
  have hfib : ∀ N : Finset ((ι → ℕ) × ℕ), ∑ J ∈ Js, (((full J).filter (· ∈ N)).card : ℝ) ≤ N.card := by
    intro N
    have h1 : ∀ J ∈ Js, (full J).filter (· ∈ N) ⊆ N.filter (fun w => box w = J) := fun J hJ w hw => by
      obtain ⟨hwf, hwN⟩ := mem_filter.1 hw
      exact mem_filter.2 ⟨hwN, idx_eq_of_mem_full (hJG J hJ) (hmemfull J w hwf).1⟩
    calc ∑ J ∈ Js, (((full J).filter (· ∈ N)).card : ℝ) ≤
          ∑ J ∈ Js, ((N.filter (fun w => box w = J)).card : ℝ) :=
          sum_le_sum fun J hJ => by exact_mod_cast card_le_card (h1 J hJ)
      _ = ((N.filter fun w => box w ∈ Js).card : ℝ) := by
          exact_mod_cast sum_card_fiberwise_eq_card_filter N Js box
      _ ≤ N.card := by exact_mod_cast card_filter_le _ _
  -- the straddling boxes
  set t : (ι → ℕ) → ℝ := fun J =>
    ∑ A ∈ atoms.toFinset, (((full J).filter (· ∈ nearJ c ν ρ D₀ A x)).card : ℝ) with ht
  have ht0 : ∀ J ∈ Js, 0 ≤ t J := fun J _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hT : ∑ J ∈ Js, t J ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) := by
    calc ∑ J ∈ Js, t J
        = ∑ A ∈ atoms.toFinset, ∑ J ∈ Js, (((full J).filter (· ∈ nearJ c ν ρ D₀ A x)).card : ℝ) := sum_comm
      _ ≤ ∑ A ∈ atoms.toFinset, ((nearJ c ν ρ D₀ A x).card : ℝ) := sum_le_sum fun A _ => hfib _
      _ ≤ ∑ _A ∈ atoms.toFinset, Cn * y₁ / Real.log x ^ 2 :=
          sum_le_sum fun A hA => hnear A (List.mem_toFinset.1 hA) x hxn
      _ = atoms.toFinset.card * (Cn * y₁ / Real.log x ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le atoms) (by positivity)
  -- the box sandwich
  have hsand := abs_sum_sub_le_boxes_rel S Js box hboxJs full hfull hfA0 hfB0 (div_nonneg hy0.le hy₁0.le)
    hε.le hE t ht0 hstrad
  have hgA : (#{w ∈ jcut c ν atoms x | x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ) = ∑ w ∈ S, fA w := by
    simp only [hfA, sum_boole, hS, filter_filter]
    congr 2
    ext w
    simp only [mem_filter]
    constructor
    · rintro ⟨hw, h1, h2⟩; exact ⟨hw, ⟨by linarith only [h1, hyx], h2⟩, h1, h2⟩
    · rintro ⟨hw, -, h1, h2⟩; exact ⟨hw, h1, h2⟩
  have hgB : (#{w ∈ jcut c ν atoms x | x - y₁ < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ) = ∑ w ∈ S, fB w := by
    simp only [hfB, sum_boole, hS, filter_filter]
    congr 2
    ext w
    simp only [mem_filter]
    constructor
    · rintro ⟨hw, h1, h2⟩; exact ⟨hw, ⟨by linarith only [h1, hy₁x], h2⟩, h1, h2⟩
    · rintro ⟨hw, -, h1, h2⟩; exact ⟨hw, h1, h2⟩
  rw [hgA, hgB]
  have hT0 : 0 ≤ ∑ J ∈ Js, t J := sum_nonneg ht0
  have hc0 : 0 ≤ y / y₁ := div_nonneg hy0.le hy₁0.le
  have h1e : 1 + ε ≤ 2 := by linarith
  have h2a : (1 + ε) * (y / y₁) * ∑ J ∈ Js, t J ≤ 2 * (y / y₁) * ∑ J ∈ Js, t J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1e hc0) hT0
  have h2b : 2 * (y / y₁) * ∑ J ∈ Js, t J ≤ 2 * (y / y₁) * (atoms.length * (Cn * y₁ / Real.log x ^ 2)) :=
    mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num) hc0)
  rw [two_mul_div_mul_eq y Cn (Real.log x ^ 2) (atoms.length : ℝ) hy₁0.ne'] at h2b
  exact hsand.trans (add_le_add le_rfl (h2a.trans h2b))

end ShortSieveJ

#print axioms ShortSieveJ.card_nearJ_le
#print axioms ShortSieveJ.sum_full_eq
#print axioms ShortSieveJ.abs_jval_sub_le
#print axioms ShortSieveJ.abs_card_jcut_sub_le
