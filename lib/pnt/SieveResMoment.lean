/-
# The 2k-th moment of a short polynomial over the characters

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoFourth` bounds the fourth moment of a polynomial `W(χ) = Σ_{j∈S} a_jχ(j)j^{−it}` over the characters by
orthogonality on the polynomial of the products of two elements of `S`. This file is the same for the `2k`-th
moment: `W(χ)^k` is the polynomial of the products of `k` elements of `S`, so orthogonality on an interval gives
`Σ_χ |W(χ)|^{2k} ≤ (B^k − A^k + q)·F·(Σ|a|²)^k` for `S ⊆ (A, B]`, where `F` bounds the number of `k`-tuples of
elements of `S` with a given product; and a tuple with product `n` is a tuple of divisors of `n`, so `F` is at most
the `k`-th power of the number of divisors. With Markov's inequality this counts the characters at which `W` is
large: at most `V^{−2k}` times the moment have `|W(χ)| ≥ V`. For a prime sum of length `q^s` at `k` with `ks ≥ 1`,
the count of the characters at which it exceeds `q^{st}` is about `q^{2ks(1−t)}`: at the lengths `q^{1/k}` the
density hypothesis's count. These are the counts of the bins of the resonant window.

* `powSet S k`, `powCoeff S k a`: the products of `k` elements of `S`, and the coefficients of the `k`-th power.
* `dp_pow_eq`: `(dp S (aχ) t)^k = dp (powSet S k) (cχ) t` with `c = powCoeff S k a`.
* `powSet_subset`: `powSet S k ⊆ (A^k, B^k]` for `S ⊆ (A, B]` and `k ≥ 1`.
* `sum_powCoeff_sq_le`: `Σ_n |c_n|² ≤ F(Σ|a|²)^k` when no `n` has more than `F` tuples.
* `card_tuples_le`: the `k`-tuples of elements of `S` with product `n ≥ 1` number at most `d(n)^k`.
* `sum_chars_dp_pow_le`, **the `2k`-th moment**: `Σ_χ |dp S (aχ) t|^{2k} ≤ (B^k − A^k + q)·F·(Σ|a|²)^k`.
* `card_large_le`, **the count of the large values**: `V^{2k}·#{χ : V ≤ |dp S (aχ) t|} ≤ Σ_χ |dp S (aχ) t|^{2k}`.

The file imports `SieveTwoFourth.lean`.
-/
import SieveTwoFourth

open Complex Finset

noncomputable section

namespace SieveTypeIIHM

open DirMean SieveTypeII DirichletCharacter

variable {q : ℕ}

/-- The products of `k` elements of `S`. -/
def powSet (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Fintype.piFinset fun _ : Fin k => S).image fun x => ∏ i, x i

/-- The coefficient of `n` in the `k`-th power of `Σ_{j∈S} a_j j^{−s}`: the sum of `∏_i a_{x_i}` over the
`k`-tuples `x` of elements of `S` with product `n`. -/
def powCoeff (S : Finset ℕ) (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ (Fintype.piFinset fun _ : Fin k => S).filter (fun x => ∏ i, x i = n), ∏ i, a (x i)

/-- **The `k`-th power of a twisted polynomial** is the twisted polynomial of the products: for `0 ∉ S`,
`(Σ_{j∈S} a_jχ(j)j^{−it})^k = Σ_{n ∈ powSet S k} c_nχ(n)n^{−it}` with `c = powCoeff S k a`. -/
lemma dp_pow_eq {S : Finset ℕ} (hS0 : 0 ∉ S) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ) :
    dp S (fun j => a j * χ j) t ^ k = dp (powSet S k) (fun n => powCoeff S k a n * χ n) t := by
  classical
  unfold dp powSet powCoeff
  rw [← Fin.prod_const k, Finset.prod_univ_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin k → ℕ => ∏ i, x i)
    (t := (Fintype.piFinset fun _ : Fin k => S).image fun x => ∏ i, x i)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
  have hxi : ∀ i, x i ∈ S := fun i => Fintype.mem_piFinset.1 hxS i
  have hx0 : ∀ i, ((x i : ℕ) : ℝ) ≠ 0 := fun i => Nat.cast_ne_zero.2 fun h => hS0 (h ▸ hxi i)
  subst hxn
  have hχ : χ (((∏ i, x i : ℕ)) : ZMod q) = ∏ i, χ ((x i : ℕ) : ZMod q) := by
    rw [Nat.cast_prod, map_prod]
  have hlog : Real.log ((∏ i, x i : ℕ) : ℝ) = ∑ i, Real.log (x i) := by
    rw [Nat.cast_prod, Real.log_prod fun i _ => hx0 i]
  have hexp : Complex.exp (-(I * ((t * Real.log ((∏ i, x i : ℕ) : ℝ) : ℝ) : ℂ))) =
      ∏ i, Complex.exp (-(I * ((t * Real.log (x i) : ℝ) : ℂ))) := by
    rw [← Complex.exp_sum, hlog, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hχ, hexp, Finset.prod_mul_distrib, Finset.prod_mul_distrib]

/-- `powSet S k ⊆ (A^k, B^k]` for `S ⊆ (A, B]` and `k ≥ 1`. -/
lemma powSet_subset {A B k : ℕ} (hk : 1 ≤ k) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A B) :
    powSet S k ⊆ Finset.Ioc (A ^ k) (A ^ k + (B ^ k - A ^ k)) := by
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
  have hxi : ∀ i, A < x i ∧ x i ≤ B := fun i => Finset.mem_Ioc.1 (hS (Fintype.mem_piFinset.1 hx i))
  have hle : ∏ i, x i ≤ B ^ k := by
    calc ∏ i, x i ≤ ∏ _i : Fin k, B := Finset.prod_le_prod fun i _ => (hxi i).2
      _ = B ^ k := Fin.prod_const k B
  have hlt : A ^ k < ∏ i, x i := by
    calc A ^ k < (A + 1) ^ k := Nat.pow_lt_pow_left (Nat.lt_succ_self A) (by omega)
      _ = ∏ _i : Fin k, (A + 1) := (Fin.prod_const k (A + 1)).symm
      _ ≤ ∏ i, x i := Finset.prod_le_prod fun i _ => (hxi i).1
  have hAB : A ^ k ≤ B ^ k := hlt.le.trans hle
  rw [Finset.mem_Ioc]
  omega

/-- `Σ_n |c_n|² ≤ F(Σ|a|²)^k`, when every `n` is the product of at most `F` tuples of `k` elements of `S`. -/
lemma sum_powCoeff_sq_le {S : Finset ℕ} (k : ℕ) (a : ℕ → ℂ) {F : ℝ}
    (hF : ∀ n, (((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card : ℝ) ≤ F) :
    ∑ n ∈ powSet S k, ‖powCoeff S k a n‖ ^ 2 ≤ F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ k := by
  classical
  set T := Fintype.piFinset fun _ : Fin k => S with hT
  have hpt : ∀ n, ‖powCoeff S k a n‖ ^ 2 ≤
      F * ∑ x ∈ T.filter (fun x => ∏ i, x i = n), ∏ i, ‖a (x i)‖ ^ 2 := by
    intro n
    set fib := T.filter (fun x => ∏ i, x i = n)
    have hn : ‖powCoeff S k a n‖ ≤ ∑ x ∈ fib, ∏ i, ‖a (x i)‖ := by
      unfold powCoeff
      exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_prod _ _))
    have hcs : (∑ x ∈ fib, ∏ i, ‖a (x i)‖) ^ 2 ≤ fib.card * ∑ x ∈ fib, (∏ i, ‖a (x i)‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : 0 ≤ ∑ x ∈ fib, (∏ i, ‖a (x i)‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc ‖powCoeff S k a n‖ ^ 2 ≤ (∑ x ∈ fib, ∏ i, ‖a (x i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ fib.card * ∑ x ∈ fib, (∏ i, ‖a (x i)‖) ^ 2 := hcs
      _ ≤ F * ∑ x ∈ fib, (∏ i, ‖a (x i)‖) ^ 2 := mul_le_mul_of_nonneg_right (hF n) hsum0
      _ = F * ∑ x ∈ fib, ∏ i, ‖a (x i)‖ ^ 2 := by simp_rw [Finset.prod_pow]
  calc ∑ n ∈ powSet S k, ‖powCoeff S k a n‖ ^ 2
      ≤ ∑ n ∈ powSet S k, F * ∑ x ∈ T.filter (fun x => ∏ i, x i = n), ∏ i, ‖a (x i)‖ ^ 2 :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = F * ∑ x ∈ T, ∏ i, ‖a (x i)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (g := fun x : Fin k → ℕ => ∏ i, x i)
          (t := powSet S k) (fun x hx => Finset.mem_image_of_mem _ hx)]
    _ = F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ k := by
        rw [hT, ← Fin.prod_const k (∑ j ∈ S, ‖a j‖ ^ 2), Finset.prod_univ_sum]

/-- **The tuples with a given product**: for `n ≥ 1`, the `k`-tuples of elements of `S` with product `n` number at
most `d(n)^k`, each entry being a divisor of `n`. -/
lemma card_tuples_le {S : Finset ℕ} (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card ≤ n.divisors.card ^ k := by
  classical
  calc ((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card
      ≤ (Fintype.piFinset fun _ : Fin k => n.divisors).card := by
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨_, hxn⟩ := Finset.mem_filter.1 hx
        refine Fintype.mem_piFinset.2 fun i => Nat.mem_divisors.2 ⟨?_, hn⟩
        rw [← hxn]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    _ = n.divisors.card ^ k := by rw [Fintype.card_piFinset, Fin.prod_const]

/-- **The `2k`-th moment of a polynomial over the characters.** For `S ⊆ (A, B]`, `k ≥ 1` and `F` such that every
`n` is the product of at most `F` tuples of `k` elements of `S`:
`Σ_χ |dp S (aχ) t|^{2k} ≤ (B^k − A^k + q)·F·(Σ_{j∈S}|a_j|²)^k`. -/
theorem sum_chars_dp_pow_le [NeZero q] {A B k : ℕ} (hk : 1 ≤ k) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A B)
    (a : ℕ → ℂ) (t : ℝ) {F : ℝ}
    (hF : ∀ n, (((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card : ℝ) ≤ F) :
    ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ (2 * k) ≤
      ((B ^ k - A ^ k : ℕ) + q) * F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ k := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Ioc.1 (hS h)).1; omega
  have hk' : ∀ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ (2 * k) =
      ‖dp (powSet S k) (fun n => powCoeff S k a n * χ n) t‖ ^ 2 := by
    intro χ
    rw [← dp_pow_eq hS0 a χ t k, norm_pow, ← pow_mul, mul_comm k 2]
  simp_rw [hk']
  have hF0 : 0 ≤ F := le_trans (Nat.cast_nonneg _) (hF 0)
  have horth := sum_chars_dp_sq_le_Ioc (powSet_subset hk hS) (powCoeff S k a) q t
  calc ∑ χ : DirichletCharacter ℂ q, ‖dp (powSet S k) (fun n => powCoeff S k a n * χ n) t‖ ^ 2
      ≤ ((B ^ k - A ^ k : ℕ) + q) * ∑ n ∈ powSet S k, ‖powCoeff S k a n‖ ^ 2 := horth
    _ ≤ ((B ^ k - A ^ k : ℕ) + q) * (F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ k) := by
        gcongr
        exact sum_powCoeff_sq_le k a hF
    _ = ((B ^ k - A ^ k : ℕ) + q) * F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ k := by ring

/-- **The count of the large values**: `V^{2k}` times the number of characters at which `|dp S (aχ) t| ≥ V` is at
most the `2k`-th moment (Markov's inequality), for `V ≥ 0`. -/
theorem card_large_le (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) (k : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    V ^ (2 * k) * ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        V ≤ ‖dp S (fun j => a j * χ j) t‖).card : ℝ) ≤
      ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ (2 * k) := by
  classical
  calc V ^ (2 * k) * ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          V ≤ ‖dp S (fun j => a j * χ j) t‖).card : ℝ)
      = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => V ≤ ‖dp S (fun j => a j * χ j) t‖),
          V ^ (2 * k) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => V ≤ ‖dp S (fun j => a j * χ j) t‖),
          ‖dp S (fun j => a j * χ j) t‖ ^ (2 * k) :=
        Finset.sum_le_sum fun χ hχ => pow_le_pow_left₀ hV (Finset.mem_filter.1 hχ).2 _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ (2 * k) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity

end SieveTypeIIHM
