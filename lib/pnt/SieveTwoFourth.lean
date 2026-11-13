/-
# The fourth moment of a short polynomial over the characters, and a third bound for a bin

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoBins.sum_bin_two` bounds the mean square of a polynomial `W(χ) = dp S (aχ) h₀` over a bin `R` of characters
by orthogonality, `(P + q)Σ|a|²`, or by the Halász–Montgomery inequality, `e·Σ|a|²·(2P + |R|·B)`. A polynomial shorter
than `√q` has a third bound, by its fourth moment over all the characters. `W(χ)²` is the polynomial of the products
`jk` of two elements of `S`, which lie in `(P², 4P²]`, so orthogonality gives
`Σ_χ |W(χ)|⁴ ≤ (3P² + q)·F·(Σ|a|²)²`, where `F` bounds the number of ways of writing an integer as such a product;
and Cauchy–Schwarz over the bin gives `Σ_{χ∈R} |W(χ)|² ≤ |R|^{1/2}((3P² + q)F)^{1/2}Σ|a|²`. For `3P² ≤ q` this is
about `(|R|q)^{1/2}Σ|a|²` against orthogonality's `qΣ|a|²`: it wins as soon as the bin has fewer than `q` characters,
whatever their zeros. It is the case `r = 2` of the moments of Burgess's method, and what lets a variable shorter
than `√q`, such as the cofactor of a leaf of Buchstab's tree, be a variable of the Type II estimate.

* `card_class_le_Ioc`, `sum_chars_dp_sq_le_Ioc`: orthogonality (T1) for `S ⊆ (A, A + M]`,
  `Σ_χ |dp S (cχ) t|² ≤ (M + q)Σ|c|²` (`SieveTypeII.sum_chars_dp_sq_le` on any interval).
* `dp_sq_eq`: `(dp S (aχ) t)² = dp (S·S) (cχ) t` with `c n = Σ_{(j,k) ∈ S², jk = n} a_j a_k`.
* `sum_chars_dp_four_le`, **the fourth moment**: for `S ⊆ (P, 2P]` and `F` bounding, for every `n`, the number of
  pairs `(j, k) ∈ S²` with `jk = n`: `Σ_χ |dp S (aχ) t|⁴ ≤ (3P² + q)·F·(Σ|a|²)²`.
* `sum_bin_four_le`, **the third bound for a bin**: `Σ_{χ∈R} |dp S (aχ) t|² ≤ |R|^{1/2}((3P² + q)F)^{1/2}Σ|a|²`.
* `sqTerm4`, the least of the three bounds, and `sum_bin_sq_le4`, `sum_bin_two4`, `sum_typeII_two_bins4`:
  `SieveTwoBins`' bounds for one bin, for two variables in one bin and by bins, with the third bound.

The file imports `SieveTwoBins.lean`.
-/
import SieveTwoBins

open Complex Finset

noncomputable section

namespace SieveTypeIIHM

open DirMean LinnikHybrid LinnikPower SieveTypeII DirichletCharacter

variable {q : ℕ}

/-! ### Orthogonality on an interval -/

/-- **A residue class in `(A, A + M]`**: at most `M/q + 1` elements. The map `j ↦ ⌊(j − A − 1)/q⌋` is injective on
the class and takes values in `[0, M/q]`. -/
lemma card_class_le_Ioc {A M q : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A (A + M)) (a : ZMod q) :
    ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ M / q + 1 := by
  have hmaps : Set.MapsTo (fun j => (j - (A + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a)
      (Finset.range (M / q + 1)) := by
    intro j hj
    have hjS := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hjS)
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun j => (j - (A + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a) := by
    intro j hj j' hj' hjj'
    have hj1 := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
    have hj1' := Finset.mem_filter.1 (Finset.mem_coe.1 hj')
    have hlo := (Finset.mem_Ioc.1 (hS hj1.1)).1
    have hlo' := (Finset.mem_Ioc.1 (hS hj1'.1)).1
    have hmod : j % q = j' % q := by
      have h : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q) := hj1.2.trans hj1'.2.symm
      exact (ZMod.natCast_eq_natCast_iff' j j' q).1 h
    have hmod' : (j - (A + 1)) % q = (j' - (A + 1)) % q := by
      have e1 : j = (j - (A + 1)) + (A + 1) := by omega
      have e2 : j' = (j' - (A + 1)) + (A + 1) := by omega
      have h : (j - (A + 1)) + (A + 1) ≡ (j' - (A + 1)) + (A + 1) [MOD q] := by
        rw [← e1, ← e2]; exact hmod
      exact Nat.ModEq.add_right_cancel' (A + 1) h
    have hdiv : (j - (A + 1)) / q = (j' - (A + 1)) / q := hjj'
    have e : j - (A + 1) = j' - (A + 1) := by
      rw [← Nat.div_add_mod (j - (A + 1)) q, ← Nat.div_add_mod (j' - (A + 1)) q, hdiv, hmod']
    omega
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hc
  calc ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ((M / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ M / q + 1 := by gcongr; exact Nat.cast_div_le

/-- **Orthogonality (T1) on an interval**: `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (M + q)Σ_{j∈S} |c_j|²` for
`S ⊆ (A, A + M]`, as `SieveTypeII.sum_chars_dp_sq_le` for `(P, 2P]`. -/
theorem sum_chars_dp_sq_le_Ioc {A M : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A (A + M)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] (t : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤ (M + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set Sa : ZMod q → Finset ℕ := fun a => S.filter (fun j : ℕ => (j : ZMod q) = a) with hSa
  have h1 : ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤
      q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := by
    have e : ∀ χ : DirichletCharacter ℂ q, dp S (fun j => c j * χ j) t = ∑ a, χ a * dp (Sa a) c t :=
      fun χ => dp_twist_eq q S c χ t
    simp_rw [e]
    exact sum_chars_norm_sq_le q (fun a => dp (Sa a) c t)
  have h2 : ∀ a, ‖dp (Sa a) c t‖ ^ 2 ≤ (M / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
    intro a
    have hn : ‖dp (Sa a) c t‖ ≤ ∑ j ∈ Sa a, ‖c j‖ := by
      unfold dp
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul, norm_exp_neg_I_mul, mul_one]
    have hcs : (∑ j ∈ Sa a, ‖c j‖) ^ 2 ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    have hcard := card_class_le_Ioc (q := q) hS a
    calc ‖dp (Sa a) c t‖ ^ 2 ≤ (∑ j ∈ Sa a, ‖c j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := hcs
      _ ≤ (M / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
          gcongr
  have hfib : ∑ a : ZMod q, ∑ j ∈ Sa a, ‖c j‖ ^ 2 = ∑ j ∈ S, ‖c j‖ ^ 2 :=
    Finset.sum_fiberwise S (fun j => (j : ZMod q)) fun j => ‖c j‖ ^ 2
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  calc ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := h1
    _ ≤ q.totient * ∑ a, (M / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
        gcongr with a; exact h2 a
    _ = q.totient * (M / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by rw [← Finset.mul_sum, hfib]; ring
    _ ≤ q * (M / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by gcongr
    _ = (M + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by field_simp

/-! ### The fourth moment -/

/-- The products `jk` of two elements of `S`. -/
def prodSet (S : Finset ℕ) : Finset ℕ := (S ×ˢ S).image fun p => p.1 * p.2

/-- The coefficient of `n` in the square of `Σ_{j∈S} a_j j^{−s}`: `Σ_{(j,k) ∈ S², jk = n} a_j a_k`. -/
def sqCoeff (S : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = n), a p.1 * a p.2

/-- **The square of a twisted polynomial** is the twisted polynomial of the products: for `0 ∉ S`,
`(Σ_{j∈S} a_jχ(j)j^{−it})² = Σ_{n ∈ S·S} c_nχ(n)n^{−it}` with `c_n = Σ_{jk = n} a_j a_k`. -/
lemma dp_sq_eq {S : Finset ℕ} (hS0 : 0 ∉ S) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    dp S (fun j => a j * χ j) t ^ 2 = dp (prodSet S) (fun n => sqCoeff S a n * χ n) t := by
  classical
  unfold dp prodSet sqCoeff
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product' (f := fun j k => a j * χ j *
      Complex.exp (-(I * ((t * Real.log j : ℝ) : ℂ))) * (a k * χ k * Complex.exp (-(I * ((t * Real.log k : ℝ) : ℂ)))))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := (S ×ˢ S).image fun p => p.1 * p.2)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpS, hpn⟩ := Finset.mem_filter.1 hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpS
  have hp1 : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hS0 (h ▸ h1)
  have hp2 : (p.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hS0 (h ▸ h2)
  subst hpn
  have hχ : χ ((p.1 * p.2 : ℕ) : ZMod q) = χ (p.1 : ZMod q) * χ (p.2 : ZMod q) := by
    rw [Nat.cast_mul, map_mul]
  have hlog : Real.log ((p.1 * p.2 : ℕ) : ℝ) = Real.log p.1 + Real.log p.2 := by
    rw [Nat.cast_mul, Real.log_mul hp1 hp2]
  rw [hχ, hlog, show (t * (Real.log p.1 + Real.log p.2) : ℝ) = t * Real.log p.1 + t * Real.log p.2 by ring,
    Complex.ofReal_add, mul_add, neg_add, Complex.exp_add]
  ring

/-- `S·S ⊆ (P², 4P²]` for `S ⊆ (P, 2P]`. -/
lemma prodSet_subset {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) :
    prodSet S ⊆ Finset.Ioc (P ^ 2) (P ^ 2 + 3 * P ^ 2) := by
  intro n hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
  obtain ⟨a1, b1⟩ := Finset.mem_Ioc.1 (hS h1)
  obtain ⟨a2, b2⟩ := Finset.mem_Ioc.1 (hS h2)
  rw [Finset.mem_Ioc]
  constructor <;> nlinarith

/-- `Σ_n |c_n|² ≤ F(Σ|a|²)²`, when every `n` is the product `jk` of at most `F` pairs `(j, k) ∈ S²`. -/
lemma sum_sqCoeff_le {S : Finset ℕ} (a : ℕ → ℂ) {F : ℝ}
    (hF : ∀ n, (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F) :
    ∑ n ∈ prodSet S, ‖sqCoeff S a n‖ ^ 2 ≤ F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2 := by
  classical
  have hpt : ∀ n, ‖sqCoeff S a n‖ ^ 2 ≤
      F * ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = n), ‖a p.1‖ ^ 2 * ‖a p.2‖ ^ 2 := by
    intro n
    set fib := (S ×ˢ S).filter (fun p => p.1 * p.2 = n)
    have hn : ‖sqCoeff S a n‖ ≤ ∑ p ∈ fib, ‖a p.1‖ * ‖a p.2‖ := by
      unfold sqCoeff
      exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => norm_mul _ _))
    have hcs : (∑ p ∈ fib, ‖a p.1‖ * ‖a p.2‖) ^ 2 ≤ fib.card * ∑ p ∈ fib, (‖a p.1‖ * ‖a p.2‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : 0 ≤ ∑ p ∈ fib, (‖a p.1‖ * ‖a p.2‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc ‖sqCoeff S a n‖ ^ 2 ≤ (∑ p ∈ fib, ‖a p.1‖ * ‖a p.2‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ fib.card * ∑ p ∈ fib, (‖a p.1‖ * ‖a p.2‖) ^ 2 := hcs
      _ ≤ F * ∑ p ∈ fib, (‖a p.1‖ * ‖a p.2‖) ^ 2 := mul_le_mul_of_nonneg_right (hF n) hsum0
      _ = F * ∑ p ∈ fib, ‖a p.1‖ ^ 2 * ‖a p.2‖ ^ 2 := by simp_rw [mul_pow]
  calc ∑ n ∈ prodSet S, ‖sqCoeff S a n‖ ^ 2
      ≤ ∑ n ∈ prodSet S, F * ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = n), ‖a p.1‖ ^ 2 * ‖a p.2‖ ^ 2 :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = F * ∑ p ∈ S ×ˢ S, ‖a p.1‖ ^ 2 * ‖a p.2‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2)
          (t := prodSet S) (fun p hp => Finset.mem_image_of_mem _ hp)]
    _ = F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2 := by
        rw [Finset.sum_product, sq, Finset.sum_mul_sum]

/-- **The fourth moment of a polynomial over the characters.** For `S ⊆ (P, 2P]` and `F` such that every `n` is the
product `jk` of at most `F` pairs `(j, k) ∈ S²`: `Σ_χ |dp S (aχ) t|⁴ ≤ (3P² + q)·F·(Σ_{j∈S}|a_j|²)²`. -/
theorem sum_chars_dp_four_le [NeZero q] {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ)
    (t : ℝ) {F : ℝ} (hF : ∀ n, (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F) :
    ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ 4 ≤
      (3 * P ^ 2 + q) * F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2 := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Ioc.1 (hS h)).1; omega
  have h4 : ∀ χ : DirichletCharacter ℂ q, ‖dp S (fun j => a j * χ j) t‖ ^ 4 =
      ‖dp (prodSet S) (fun n => sqCoeff S a n * χ n) t‖ ^ 2 := by
    intro χ
    rw [← dp_sq_eq hS0 a χ t, norm_pow]
    ring
  simp_rw [h4]
  have hF0 : 0 ≤ F := le_trans (Nat.cast_nonneg _) (hF 0)
  have horth := sum_chars_dp_sq_le_Ioc (prodSet_subset hS) (sqCoeff S a) q t
  have hc := sum_sqCoeff_le a hF
  have hM : ((3 * P ^ 2 : ℕ) : ℝ) = 3 * (P : ℝ) ^ 2 := by push_cast; ring
  rw [hM] at horth
  calc ∑ χ : DirichletCharacter ℂ q, ‖dp (prodSet S) (fun n => sqCoeff S a n * χ n) t‖ ^ 2
      ≤ (3 * (P : ℝ) ^ 2 + q) * ∑ n ∈ prodSet S, ‖sqCoeff S a n‖ ^ 2 := horth
    _ ≤ (3 * (P : ℝ) ^ 2 + q) * (F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (3 * P ^ 2 + q) * F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2 := by ring

/-- **The third bound for a bin**, by the fourth moment and Cauchy–Schwarz over the bin: for `S ⊆ (P, 2P]`, `F` as
in `sum_chars_dp_four_le` and a set `R` of characters,
`Σ_{χ∈R} |dp S (aχ) t|² ≤ |R|^{1/2}((3P² + q)F)^{1/2}Σ_{j∈S}|a_j|²`. -/
theorem sum_bin_four_le [NeZero q] {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (t : ℝ)
    (R : Finset (DirichletCharacter ℂ q)) {F : ℝ}
    (hF : ∀ n, (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F) :
    ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) t‖ ^ 2 ≤
      Real.sqrt R.card * Real.sqrt ((3 * P ^ 2 + q) * F) * ∑ j ∈ S, ‖a j‖ ^ 2 := by
  set W : DirichletCharacter ℂ q → ℝ := fun χ => ‖dp S (fun j => a j * χ j) t‖ with hW
  have hF0 : 0 ≤ F := le_trans (Nat.cast_nonneg _) (hF 0)
  have hV0 : 0 ≤ ∑ j ∈ S, ‖a j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt R (fun _ => (1 : ℝ)) (fun χ => W χ ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have h4R : ∑ χ ∈ R, (W χ ^ 2) ^ 2 ≤ ∑ χ : DirichletCharacter ℂ q, W χ ^ 4 := by
    calc ∑ χ ∈ R, (W χ ^ 2) ^ 2 = ∑ χ ∈ R, W χ ^ 4 := Finset.sum_congr rfl fun χ _ => by ring
      _ ≤ ∑ χ : DirichletCharacter ℂ q, W χ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun _ _ _ => by positivity
  have h4 := sum_chars_dp_four_le (q := q) hS a t hF
  calc ∑ χ ∈ R, W χ ^ 2 ≤ Real.sqrt R.card * Real.sqrt (∑ χ ∈ R, (W χ ^ 2) ^ 2) := hcs
    _ ≤ Real.sqrt R.card * Real.sqrt ((3 * P ^ 2 + q) * F * (∑ j ∈ S, ‖a j‖ ^ 2) ^ 2) := by
        gcongr
        exact h4R.trans h4
    _ = Real.sqrt R.card * Real.sqrt ((3 * P ^ 2 + q) * F) * ∑ j ∈ S, ‖a j‖ ^ 2 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hV0]
        ring

/-! ### The bins with the third bound -/

/-- The least of the three bounds for the mean square of a polynomial over a bin of `cnt` characters:
orthogonality's `(P + q)V`, Halász–Montgomery's `e·V·(2P + cnt·B)` and the fourth moment's
`cnt^{1/2}((3P² + q)F)^{1/2}V`. -/
noncomputable def sqTerm4 (cnt P q V B F : ℝ) : ℝ :=
  min (sqTerm cnt P q V B) (Real.sqrt cnt * Real.sqrt ((3 * P ^ 2 + q) * F) * V)

/-- The mean square of a polynomial over a bin is at most `sqTerm4`. -/
theorem sum_bin_sq_le4 [NeZero q] {P : ℕ} (hP : 0 < P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (a : ℕ → ℂ) (h₀ : ℝ) (R : Finset (DirichletCharacter ℂ q)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) {F : ℝ}
    (hF : ∀ n, (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F) :
    ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 ≤ sqTerm4 R.card P q (∑ j ∈ S, ‖a j‖ ^ 2) B F :=
  le_min (sum_bin_sq_le hP hS a h₀ R hB0 hB) (sum_bin_four_le hS a h₀ R hF)

/-- **One bin in two variables, with the third bound**: `SieveTwoBins.sum_bin_two` with `sqTerm4`. -/
theorem sum_bin_two4 [NeZero q] {P₁ P₂ : ℕ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) {S₁ S₂ : Finset ℕ}
    (hS₁ : S₁ ⊆ Finset.Ioc P₁ (2 * P₁)) (hS₂ : S₂ ⊆ Finset.Ioc P₂ (2 * P₂)) (a b : ℕ → ℂ) (h₁ h₂ : ℝ)
    (R : Finset (DirichletCharacter ℂ q)) {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hK₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₁) 0 n‖ ≤ B₁)
    (hK₂ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₂) 0 n‖ ≤ B₂) {F₁ F₂ : ℝ}
    (hF₁ : ∀ n, (((S₁ ×ˢ S₁).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₁)
    (hF₂ : ∀ n, (((S₂ ×ˢ S₂).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₂) :
    ∑ χ ∈ R, ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ ≤
      Real.sqrt (sqTerm4 R.card P₁ q (∑ j ∈ S₁, ‖a j‖ ^ 2) B₁ F₁) *
        Real.sqrt (sqTerm4 R.card P₂ q (∑ j ∈ S₂, ‖b j‖ ^ 2) B₂ F₂) := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt R _ _).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt (sum_bin_sq_le4 hP₁ hS₁ a h₁ R hB₁0 hK₁ hF₁))
    (Real.sqrt_le_sqrt (sum_bin_sq_le4 hP₂ hS₂ b h₂ R hB₂0 hK₂ hF₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **The Type II estimate in two variables, by bins, with the third bound**: `SieveTwoBins.sum_typeII_two_bins`
with `sqTerm4`. -/
theorem sum_typeII_two_bins4 [NeZero q] {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) {P₁ P₂ : ℕ} (hP₁ : 0 < P₁)
    (hP₂ : 0 < P₂) {S₁ S₂ : Finset ℕ} (hS₁ : S₁ ⊆ Finset.Ioc P₁ (2 * P₁)) (hS₂ : S₂ ⊆ Finset.Ioc P₂ (2 * P₂))
    (a b : ℕ → ℂ) (h₁ h₂ : ℝ) (Bf : DirichletCharacter ℂ q → ℂ) (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖Bf χ‖ ≤ M (bin β N T χ))
    {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hK₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₁) 0 n‖ ≤ B₁)
    (hK₂ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₂) 0 n‖ ≤ B₂) {F₁ F₂ : ℝ}
    (hF₁ : ∀ n, (((S₁ ×ˢ S₁).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₁)
    (hF₂ : ∀ n, (((S₂ ×ˢ S₂).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₂) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        (Real.sqrt (sqTerm4 ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card)
            P₁ q (∑ j ∈ S₁, ‖a j‖ ^ 2) B₁ F₁) *
          Real.sqrt (sqTerm4 ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card)
            P₂ q (∑ j ∈ S₂, ‖b j‖ ^ 2) B₂ F₂)) := by
  classical
  set W : DirichletCharacter ℂ q → ℝ :=
    fun χ => ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ with hW
  have hW0 : ∀ χ, 0 ≤ W χ := fun χ => by rw [hW]; positivity
  have hsplit : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), W χ := by
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * ‖Bf χ‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * M (bin β N T χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          exact mul_le_mul_of_nonneg_left (hB χ (Finset.mem_filter.1 hχ).2) (hW0 χ)
      _ = ∑ i ∈ Finset.range N, ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
            bin β N T χ = i), W χ * M i := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := bin β N T) (t := Finset.range N)
            (fun χ _ => Finset.mem_range.2 (bin_lt hN T χ))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.filter_filter]
          exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2.2]
      _ = ∑ i ∈ Finset.range N, M i *
            ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), W χ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine hsplit.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hM i))
  exact sum_bin_two4 hP₁ hP₂ hS₁ hS₂ a b h₁ h₂ _ hB₁0 hB₂0 hK₁ hK₂ hF₁ hF₂

/-! ### The divisor bound for the pairs -/

/-- At most `d(n)` pairs `(j, k) ∈ S²` have the product `n`, for `0 ∉ S`: `(j, k) ↦ j` is injective on them, into
the divisors of `n`. -/
lemma card_fiber_le_divisors {S : Finset ℕ} (hS0 : 0 ∉ S) (n : ℕ) :
    ((S ×ˢ S).filter fun p => p.1 * p.2 = n).card ≤ n.divisors.card := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (S ×ˢ S).filter (fun p => p.1 * p.2 = 0) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun p hp h0 => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      rcases Nat.mul_eq_zero.1 h0 with h | h
      · exact hS0 (h ▸ h1)
      · exact hS0 (h ▸ h2)
    rw [h, Finset.card_empty]
    exact Nat.zero_le _
  · have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.1) ((S ×ˢ S).filter fun p => p.1 * p.2 = n) n.divisors := by
      intro p hp
      obtain ⟨_, hpn⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨⟨p.2, hpn.symm⟩, hn.ne'⟩)
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1) ((S ×ˢ S).filter fun p => p.1 * p.2 = n) := by
      intro p hp p' hp' h
      obtain ⟨hpS, hpn⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      obtain ⟨_, hpn'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp')
      have h1 : p.1 ≠ 0 := fun h0 => hS0 (h0 ▸ (Finset.mem_product.1 hpS).1)
      have h' : p.1 = p'.1 := h
      have h2 : p.2 = p'.2 := by
        have e : p.1 * p.2 = p.1 * p'.2 := by rw [hpn]; rw [h']; exact hpn'.symm
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) e
      exact Prod.ext h' h2
    exact Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The divisor bound for the pairs**: for `S ⊆ (P, 2P]` and `0 < ε ≤ 1`, every `n` is the product of at most
`C_ε(4P²)^ε` pairs `(j, k) ∈ S²` (`LinnikPower.card_divisors_le`, and `n ≤ 4P²` when there is one). -/
lemma card_fiber_le_pow {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (n : ℕ) :
    (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ Cdiv ε * (4 * (P : ℝ) ^ 2) ^ ε := by
  classical
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Ioc.1 (hS h)).1; omega
  have hC := one_le_Cdiv hε hε1
  by_cases hne : ((S ×ˢ S).filter fun p => p.1 * p.2 = n).Nonempty
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨hpS, hpn⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpS
    have b1 : (p.1 : ℝ) ≤ 2 * P := by exact_mod_cast (Finset.mem_Ioc.1 (hS h1)).2
    have b2 : (p.2 : ℝ) ≤ 2 * P := by exact_mod_cast (Finset.mem_Ioc.1 (hS h2)).2
    have hn4 : (n : ℝ) ≤ 4 * (P : ℝ) ^ 2 := by
      rw [← hpn]
      push_cast
      have := Nat.cast_nonneg (α := ℝ) p.1
      have := Nat.cast_nonneg (α := ℝ) p.2
      nlinarith
    calc (((S ×ˢ S).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ n.divisors.card := by
          exact_mod_cast card_fiber_le_divisors hS0 n
      _ ≤ Cdiv ε * (n : ℝ) ^ ε := card_divisors_le hε hε1 n
      _ ≤ Cdiv ε * (4 * (P : ℝ) ^ 2) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hn4 hε.le) (by linarith)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ (4 * (P : ℝ) ^ 2) ^ ε := by positivity
    nlinarith

end SieveTypeIIHM

#print axioms SieveTypeIIHM.sum_chars_dp_four_le
#print axioms SieveTypeIIHM.sum_bin_four_le
#print axioms SieveTypeIIHM.sum_typeII_two_bins4
