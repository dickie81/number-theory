/-
# The characters at which a product of smoothed prime sums is large

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResCount.card_Sp_large` counts the characters at which one smoothed prime sum is large, by its moments. This
file counts them for a product `G(χ) = ∏_{i<t} Sp(χ, Q_i, y_i)` of such sums, taken as one polynomial of length
`M = ∏Q_i`: a part of the resonant window's rest can then be a product of primes (a sifted cofactor written out as
its primes), counted by its own sums as a prime sum of length `M` is. A product of prime sums over a finite index
set `κ` is the polynomial of the products of one prime from each range, with coefficients at most `K^K F₀^K` for
`K = |κ|` (a tuple of primes with a given product is a tuple of its prime factors), supported in `[∏Q_i/2, ∏2Q_i]`;
and `G^k` is the product of the `kt` sums indexed by `Fin k × Fin t`. So:

* by orthogonality, `Σ_χ |G|^{2k} ≤ ((2^tM)^k + q)(kt)^{kt}(3F₀²)^{kt}M^k`, and the characters at which `|G| ≥ M^u`
  number at most `C q^{momExp k s u}` with `s = log_q M`, the count of one prime sum of length `M`;
* by Chen, Gupta and Li's Proposition 3.1 for `G^k`, whose range `[(M/2^t)^k, (2^tM)^k]` is `[(Q'/2)^{kt}, (2Q')^{kt}]`
  for `Q' = M^{1/t}`: the characters number at most `C q^{lvExp k s u}`, again the count of one prime sum.

* `spProdSet`, `spProdCoeff`, `prod_Sp_eq_dp`: `∏_i Sp χ f0 (Q i) (y i) = dp (spProdSet Q) (spProdCoeff f0 Q y · χ) 0`.
* `card_tuples_primes_le'`: the tuples of primes indexed by `κ` with a given product number at most `|κ|^{|κ|}`.
* `norm_spProdCoeff_le`, `spProdCoeff_eq_zero`, `sum_spProdCoeff_sq_le`: the coefficients' bound, support and mean square.
* `sum_chars_prod_Sp_sq_le`: `Σ_χ |∏_i Sp_i|² ≤ (∏⌊2Q_i⌋ + q)K^K F₀^K ∏F₀(2Q_i + 1)`.
* `card_prodSp_large`, **the count by the moment**: `#{χ : M^u ≤ |G|} ≤ (2^{tk} + 1)(kt)^{kt}(3F₀²)^{kt} q^{momExp k s u}`.
* `card_prodSp_pow_large`, **Chen, Gupta and Li's count for a product**: Proposition 3.1 for `∏_{i∈κ} Sp_i`, a
  polynomial cut in `(2K + 1)` dyadic blocks (`SieveResLV.lean`'s `lvB`).
* `card_prodSp_large_lv`, **the count in exponents**: for `q` large, `#{χ : M^u ≤ |G|} ≤ C q^{lvExp k s u}`.

The file imports `SieveResLV.lean`.
-/
import SieveResLV

open Complex Finset

noncomputable section

namespace SieveTypeIIHM

open DirMean SieveTypeII DirichletCharacter

variable {q : ℕ}

/-! ### A product of prime sums as one polynomial -/

/-- The products of one prime from each range `spSet (Q i)`. -/
def spProdSet {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : κ → ℝ) : Finset ℕ :=
  (Fintype.piFinset fun i => spSet (Q i)).image fun x => ∏ i, x i

/-- The coefficient of `n` in a product of prime sums: `Σ_{x : ∏x = n} ∏_i spCoeff f0 (Q i) (y i) (x i)`. -/
def spProdCoeff {κ : Type*} [Fintype κ] [DecidableEq κ] (f0 : ℝ → ℝ) (Q y : κ → ℝ) (n : ℕ) : ℂ :=
  ∑ x ∈ (Fintype.piFinset fun i => spSet (Q i)).filter (fun x => ∏ i, x i = n), ∏ i, spCoeff f0 (Q i) (y i) (x i)

/-- `dp S c 0 = Σ_{j∈S} c j`. -/
lemma dp_zero (S : Finset ℕ) (c : ℕ → ℂ) : dp S c 0 = ∑ j ∈ S, c j := by
  unfold dp
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- **A product of prime sums is one polynomial**: `∏_i Sp χ f0 (Q i) (y i) = dp (spProdSet Q) (spProdCoeff · χ) 0`. -/
theorem prod_Sp_eq_dp [NeZero q] {κ : Type*} [Fintype κ] [DecidableEq κ] (χ : DirichletCharacter ℂ q)
    (f0 : ℝ → ℝ) (Q y : κ → ℝ) :
    ∏ i, SieveWeight.Sp χ f0 (Q i) (y i) = dp (spProdSet Q) (fun n => spProdCoeff f0 Q y n * χ n) 0 := by
  have h1 : ∀ i, SieveWeight.Sp χ f0 (Q i) (y i) = ∑ p ∈ spSet (Q i), spCoeff f0 (Q i) (y i) p * χ p := by
    intro i
    rw [Sp_eq_dp, dp_zero]
  simp_rw [h1]
  rw [Finset.prod_univ_sum, dp_zero]
  have h2 : ∀ x ∈ Fintype.piFinset (fun i => spSet (Q i)),
      ∏ i, spCoeff f0 (Q i) (y i) (x i) * χ (x i) =
        (∏ i, spCoeff f0 (Q i) (y i) (x i)) * χ ((∏ i, x i : ℕ) : ZMod q) := by
    intro x _
    rw [Finset.prod_mul_distrib, Nat.cast_prod, map_prod]
  rw [Finset.sum_congr rfl h2]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset fun i => spSet (Q i)) (t := spProdSet Q)
    (g := fun x => ∏ i, x i) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold spProdCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- **The tuples of primes with a given product**, indexed by a finite type `κ`: for `S` of primes, the tuples of
elements of `S` with product `n` number at most `|κ|^{|κ|}`: their entries are among one tuple's. -/
theorem card_tuples_primes_le' {κ : Type*} [Fintype κ] [DecidableEq κ] {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) :
    ((Fintype.piFinset fun _ : κ => S).filter fun x => ∏ i, x i = n).card ≤
      Fintype.card κ ^ Fintype.card κ := by
  classical
  set T := (Fintype.piFinset fun _ : κ => S).filter fun x => ∏ i, x i = n with hT
  rcases T.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h, Finset.card_empty]; exact Nat.zero_le _
  obtain ⟨hx₀S, hx₀n⟩ := Finset.mem_filter.1 hx₀
  have hx₀p : ∀ i, (x₀ i).Prime := fun i => hS _ (Fintype.mem_piFinset.1 hx₀S i)
  have hent : ∀ x ∈ T, ∀ i, x i ∈ Finset.univ.image x₀ := by
    intro x hx i
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
    have hp : (x i).Prime := hS _ (Fintype.mem_piFinset.1 hxS i)
    have hdvd : x i ∣ ∏ j, x₀ j := by
      rw [hx₀n, ← hxn]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, ((Nat.prime_dvd_prime_iff_eq hp (hx₀p j)).1 hj).symm⟩
  calc T.card ≤ (Fintype.piFinset fun _ : κ => Finset.univ.image x₀).card :=
        Finset.card_le_card fun x hx => Fintype.mem_piFinset.2 (hent x hx)
    _ = (Finset.univ.image x₀).card ^ Fintype.card κ := by rw [Fintype.card_piFinset, Finset.prod_const,
          Finset.card_univ]
    _ ≤ Fintype.card κ ^ Fintype.card κ := by
        refine Nat.pow_le_pow_left ?_ _
        calc (Finset.univ.image x₀).card ≤ (Finset.univ : Finset κ).card := Finset.card_image_le
          _ = Fintype.card κ := Finset.card_univ

/-- The tuples `x` of the ranges `spSet (Q i)` with product `n` number at most `|κ|^{|κ|}`. -/
lemma card_fib_le {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : κ → ℝ) (n : ℕ) :
    ((Fintype.piFinset fun i => spSet (Q i)).filter (fun x => ∏ i, x i = n)).card ≤
      Fintype.card κ ^ Fintype.card κ := by
  classical
  set S : Finset ℕ := Finset.univ.biUnion fun i => spSet (Q i) with hS
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hp
    exact (Finset.mem_filter.1 hi).2
  refine le_trans (Finset.card_le_card ?_) (card_tuples_primes_le' (κ := κ) hSp n)
  intro x hx
  obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hxn⟩
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.1 hxS i⟩

/-- `|spCoeff f0 Q y p| ≤ F₀` at a prime `p` and `Q > 0`, for `|f0| ≤ F₀`. -/
lemma norm_spCoeff_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : ℝ} (hQ : 0 < Q) (y : ℝ) {p : ℕ}
    (hp : 0 < p) : ‖spCoeff f0 Q y p‖ ≤ F₀ := by
  have hp0 : (0 : ℝ) < (p : ℝ) / Q := div_pos (by exact_mod_cast hp) hQ
  have h1 : ‖(((p : ℝ) / Q : ℝ) : ℂ) ^ (-(y : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  unfold spCoeff
  rw [norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact hF₀ _

/-- **The coefficients of a product of prime sums** are at most `K^K F₀^K`, `K = |κ|`, for `|f0| ≤ F₀` and `Q > 0`. -/
theorem norm_spProdCoeff_le {κ : Type*} [Fintype κ] [DecidableEq κ] {f0 : ℝ → ℝ} {F₀ : ℝ}
    (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : κ → ℝ} (hQ : ∀ i, 0 < Q i) (y : κ → ℝ) (n : ℕ) :
    ‖spProdCoeff f0 Q y n‖ ≤ (Fintype.card κ : ℝ) ^ Fintype.card κ * F₀ ^ Fintype.card κ := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  unfold spProdCoeff
  set fib := (Fintype.piFinset fun i => spSet (Q i)).filter (fun x => ∏ i, x i = n) with hfib
  have hterm : ∀ x ∈ fib, ‖∏ i, spCoeff f0 (Q i) (y i) (x i)‖ ≤ F₀ ^ Fintype.card κ := by
    intro x hx
    have hxS := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1
    rw [norm_prod]
    calc ∏ i, ‖spCoeff f0 (Q i) (y i) (x i)‖ ≤ ∏ _i : κ, F₀ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
            norm_spCoeff_le hF₀ (hQ i) (y i) (Finset.mem_filter.1 (hxS i)).2.pos
      _ = F₀ ^ Fintype.card κ := by rw [Finset.prod_const, Finset.card_univ]
  have hcard : (fib.card : ℝ) ≤ (Fintype.card κ : ℝ) ^ Fintype.card κ := by
    exact_mod_cast card_fib_le Q n
  calc ‖∑ x ∈ fib, ∏ i, spCoeff f0 (Q i) (y i) (x i)‖ ≤ ∑ x ∈ fib, ‖∏ i, spCoeff f0 (Q i) (y i) (x i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ fib, F₀ ^ Fintype.card κ := Finset.sum_le_sum hterm
    _ = fib.card * F₀ ^ Fintype.card κ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card κ : ℝ) ^ Fintype.card κ * F₀ ^ Fintype.card κ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **The support of a product of prime sums**: for `f0` with support in `[1/2, 2]` and `Q > 0`, the coefficient of
`n` vanishes unless `∏(Q_i/2) ≤ n ≤ ∏2Q_i`. -/
theorem spProdCoeff_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ] {f0 : ℝ → ℝ}
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) {Q : κ → ℝ} (hQ : ∀ i, 0 < Q i) (y : κ → ℝ) {n : ℕ}
    (hn : (n : ℝ) < ∏ i, Q i / 2 ∨ ∏ i, 2 * Q i < (n : ℝ)) : spProdCoeff f0 Q y n = 0 := by
  unfold spProdCoeff
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
  have hxS' := Fintype.mem_piFinset.1 hxS
  by_contra hne
  have hall : ∀ i, Q i / 2 ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 2 * Q i := by
    intro i
    have hi : spCoeff f0 (Q i) (y i) (x i) ≠ 0 := fun h0 =>
      hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have hf : f0 ((x i : ℝ) / Q i) ≠ 0 := by
      intro hf
      apply hi
      unfold spCoeff
      rw [hf, Complex.ofReal_zero, mul_zero]
    have hmem := hsupp (Function.mem_support.2 hf)
    rw [Set.mem_Icc] at hmem
    constructor
    · have := hmem.1
      rw [le_div_iff₀ (hQ i)] at this
      linarith
    · have := hmem.2
      rw [div_le_iff₀ (hQ i)] at this
      linarith
  have hn' : (n : ℝ) = ∏ i, (x i : ℝ) := by rw [← hxn]; push_cast; rfl
  rcases hn with h | h
  · have hle : ∏ i, Q i / 2 ≤ ∏ i, (x i : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => by have := hQ i; positivity) fun i _ => (hall i).1
    linarith
  · have hle : ∏ i, (x i : ℝ) ≤ ∏ i, 2 * Q i :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hall i).2
    linarith

/-- `spProdSet Q ⊆ (0, ∏⌊2Q_i⌋]`. -/
theorem spProdSet_subset {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : κ → ℝ) :
    spProdSet Q ⊆ Finset.Ioc 0 (∏ i, ⌊2 * Q i⌋₊) := by
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
  have hx' := Fintype.mem_piFinset.1 hx
  refine Finset.mem_Ioc.2 ⟨Finset.prod_pos fun i _ => (Finset.mem_filter.1 (hx' i)).2.pos, ?_⟩
  exact Finset.prod_le_prod fun i _ => (Finset.mem_Ioc.1 (spSet_subset (Q i) (hx' i))).2

/-- **The mean square of a product's coefficients**: `Σ_n |spProdCoeff n|² ≤ K^K F₀^K ∏_i F₀(2Q_i + 1)` for `Q > 0`. -/
theorem sum_spProdCoeff_sq_le {κ : Type*} [Fintype κ] [DecidableEq κ] {f0 : ℝ → ℝ} {F₀ : ℝ}
    (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : κ → ℝ} (hQ : ∀ i, 0 < Q i) (y : κ → ℝ) :
    ∑ n ∈ spProdSet Q, ‖spProdCoeff f0 Q y n‖ ^ 2 ≤
      (Fintype.card κ : ℝ) ^ Fintype.card κ * F₀ ^ Fintype.card κ * ∏ i, (F₀ * (2 * Q i + 1)) := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  set B : ℝ := (Fintype.card κ : ℝ) ^ Fintype.card κ * F₀ ^ Fintype.card κ with hB
  have hB0 : 0 ≤ B := by positivity
  set X := Fintype.piFinset fun i => spSet (Q i) with hX
  -- `|c_n|² ≤ B|c_n|`, and `Σ_n |c_n| ≤ Σ_x ∏_i |spCoeff (x i)|`
  have h1 : ∀ n, ‖spProdCoeff f0 Q y n‖ ^ 2 ≤ B * ‖spProdCoeff f0 Q y n‖ := by
    intro n
    rw [sq]
    exact mul_le_mul_of_nonneg_right (norm_spProdCoeff_le hF₀ hQ y n) (norm_nonneg _)
  have h2 : ∑ n ∈ spProdSet Q, ‖spProdCoeff f0 Q y n‖ ≤ ∑ x ∈ X, ∏ i, ‖spCoeff f0 (Q i) (y i) (x i)‖ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := X) (t := spProdSet Q) (g := fun x => ∏ i, x i)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_le_sum fun n _ => ?_
    unfold spProdCoeff
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_prod]
  have h3 : ∑ x ∈ X, ∏ i, ‖spCoeff f0 (Q i) (y i) (x i)‖ = ∏ i, ∑ p ∈ spSet (Q i), ‖spCoeff f0 (Q i) (y i) p‖ := by
    rw [hX, Finset.prod_univ_sum]
  have h4 : ∀ i, ∑ p ∈ spSet (Q i), ‖spCoeff f0 (Q i) (y i) p‖ ≤ F₀ * (2 * Q i + 1) := by
    intro i
    have hcard : ((spSet (Q i)).card : ℝ) ≤ 2 * Q i + 1 := by
      have h1 : (spSet (Q i)).card ≤ ⌊2 * Q i⌋₊ + 1 := by
        calc (spSet (Q i)).card ≤ (Finset.range (⌊2 * Q i⌋₊ + 1)).card := Finset.card_filter_le _ _
          _ = ⌊2 * Q i⌋₊ + 1 := Finset.card_range _
      have h2 : ((⌊2 * Q i⌋₊ : ℕ) : ℝ) ≤ 2 * Q i := Nat.floor_le (by linarith [hQ i])
      have h3 : ((spSet (Q i)).card : ℝ) ≤ ((⌊2 * Q i⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h3
      linarith
    calc ∑ p ∈ spSet (Q i), ‖spCoeff f0 (Q i) (y i) p‖ ≤ ∑ _p ∈ spSet (Q i), F₀ :=
          Finset.sum_le_sum fun p hp => norm_spCoeff_le hF₀ (hQ i) (y i) (Finset.mem_filter.1 hp).2.pos
      _ = (spSet (Q i)).card * F₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Q i + 1) * F₀ := mul_le_mul_of_nonneg_right hcard hF0
      _ = F₀ * (2 * Q i + 1) := by ring
  calc ∑ n ∈ spProdSet Q, ‖spProdCoeff f0 Q y n‖ ^ 2 ≤ ∑ n ∈ spProdSet Q, B * ‖spProdCoeff f0 Q y n‖ :=
        Finset.sum_le_sum fun n _ => h1 n
    _ = B * ∑ n ∈ spProdSet Q, ‖spProdCoeff f0 Q y n‖ := by rw [Finset.mul_sum]
    _ ≤ B * ∏ i, (F₀ * (2 * Q i + 1)) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) hB0
        rw [h3]
        exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) fun i _ => h4 i

/-- **Orthogonality for a product of prime sums**: `Σ_χ |∏_i Sp_i|² ≤ (∏⌊2Q_i⌋ + q)K^K F₀^K ∏_i F₀(2Q_i + 1)`. -/
theorem sum_chars_prod_Sp_sq_le [NeZero q] {κ : Type*} [Fintype κ] [DecidableEq κ] {f0 : ℝ → ℝ} {F₀ : ℝ}
    (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : κ → ℝ} (hQ : ∀ i, 0 < Q i) (y : κ → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ ^ 2 ≤
      (((∏ i, ⌊2 * Q i⌋₊ : ℕ) : ℝ) + q) *
        ((Fintype.card κ : ℝ) ^ Fintype.card κ * F₀ ^ Fintype.card κ * ∏ i, (F₀ * (2 * Q i + 1))) := by
  simp_rw [prod_Sp_eq_dp]
  have hsub : spProdSet Q ⊆ Finset.Ioc 0 (0 + ∏ i, ⌊2 * Q i⌋₊) := by
    rw [zero_add]; exact spProdSet_subset Q
  refine (sum_chars_dp_sq_le_Ioc hsub (spProdCoeff f0 Q y) q 0).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_spProdCoeff_sq_le hF₀ hQ y) (by positivity)

/-! ### The count by the moment -/

/-- The `k`-th power of a product over `Fin t` is the product over `Fin k × Fin t`. -/
lemma prod_pow_eq_prod_prod {t k : ℕ} (f : Fin t → ℂ) : (∏ i, f i) ^ k = ∏ p : Fin k × Fin t, f p.2 := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The characters at which a product of prime sums is large, by its moment.** For `q > 1`, `|f0| ≤ F₀`, `t`
scales `Q_i ≥ 1` with product `M` and `k ≥ 1`: `#{χ : M^u ≤ |∏_i Sp χ f0 (Q i) (y i)|} ≤
(2^{tk} + 1)(kt)^{kt}(3F₀²)^{kt} q^{momExp k s u}`, `s = log_q M`: the count of one prime sum of length `M`. -/
theorem card_prodSp_large [NeZero q] (hq : 1 < (q : ℝ)) {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀) {t : ℕ}
    {Q : Fin t → ℝ} (hQ : ∀ i, 1 ≤ Q i) (y : Fin t → ℝ) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        (∏ i, Q i) ^ u ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖).card : ℝ) ≤
      (2 ^ (t * k) + 1) * ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) *
        (q : ℝ) ^ (momExp k (Real.logb q (∏ i, Q i)) u) := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ0 : ∀ i, 0 < Q i := fun i => by linarith [hQ i]
  set M : ℝ := ∏ i, Q i with hMdef
  have hM1 : 1 ≤ M := Finset.one_le_prod₀ fun i _ => hQ i
  have hM0 : 0 < M := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.logb q M := ⟨_, rfl⟩
  rw [← hs]
  have hMs : M = (q : ℝ) ^ s := by rw [hs, Real.rpow_logb hq0 hq.ne' hM0]
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.logb_nonneg hq hM1
  -- the moment: `Σ_χ |G|^{2k} = Σ_χ |∏_{(j,i)} Sp|²`
  set Q' : Fin k × Fin t → ℝ := fun p => Q p.2 with hQ'
  set y' : Fin k × Fin t → ℝ := fun p => y p.2 with hy'
  have hQ'0 : ∀ p, 0 < Q' p := fun p => hQ0 p.2
  have hpow : ∀ χ : DirichletCharacter ℂ q, ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ ^ (2 * k) =
      ‖∏ p, SieveWeight.Sp χ f0 (Q' p) (y' p)‖ ^ 2 := by
    intro χ
    rw [mul_comm 2 k, pow_mul, ← norm_pow, prod_pow_eq_prod_prod]
  have hmom := sum_chars_prod_Sp_sq_le (q := q) hF₀ hQ'0 y'
  have hcardκ : Fintype.card (Fin k × Fin t) = k * t := by simp
  rw [hcardκ] at hmom
  -- the moment's three factors
  have hfl : (((∏ p, ⌊2 * Q' p⌋₊ : ℕ) : ℝ)) ≤ (2 ^ t) ^ k * M ^ k := by
    push_cast
    calc ∏ p : Fin k × Fin t, ((⌊2 * Q' p⌋₊ : ℕ) : ℝ) ≤ ∏ p : Fin k × Fin t, (2 * Q' p) :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun p _ => Nat.floor_le (by linarith [hQ'0 p])
      _ = (∏ i, 2 * Q i) ^ k := by
          rw [hQ', Fintype.prod_prod_type]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (2 ^ t) ^ k * M ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  have hpr : ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1)) ≤ (3 * F₀) ^ (k * t) * M ^ k := by
    calc ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1)) ≤ ∏ p : Fin k × Fin t, (3 * F₀ * Q' p) :=
          Finset.prod_le_prod₀ (fun p _ => by have := hQ'0 p; positivity) fun p _ => by
            have := hQ (p.2); simp only [hQ']; nlinarith
      _ = (3 * F₀) ^ (k * t) * M ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardκ, hQ', Fintype.prod_prod_type]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rfl
  -- Markov
  set c : ℝ := ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
    M ^ u ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖).card : ℝ) with hc
  have hV0 : 0 < M ^ u := Real.rpow_pos_of_pos hM0 u
  have hmarkov : (M ^ u) ^ (2 * k) * c ≤ ∑ χ : DirichletCharacter ℂ q, ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ ^ (2 * k) := by
    rw [hc, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    calc ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖),
          (M ^ u) ^ (2 * k)
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖),
          ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ ^ (2 * k) :=
          Finset.sum_le_sum fun χ hχ => pow_le_pow_left₀ hV0.le (Finset.mem_filter.1 hχ).2 _
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ ^ (2 * k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
  simp_rw [hpow] at hmarkov
  -- the powers of `q`
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hMk : M ^ k = (q : ℝ) ^ (k * s) := by
    rw [hMs, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, mul_comm]
  have hVk : (M ^ u) ^ (2 * k) = (q : ℝ) ^ (2 * (k * s * u)) := by
    rw [hMs, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hmax1 : (q : ℝ) ^ (k * s) ≤ (q : ℝ) ^ (max 1 ((k : ℝ) * s)) :=
    Real.rpow_le_rpow_of_exponent_le hq.le (le_max_right _ _)
  have hmax2 : (q : ℝ) ≤ (q : ℝ) ^ (max 1 ((k : ℝ) * s)) := by
    conv_lhs => rw [← Real.rpow_one (q : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (le_max_left _ _)
  have h2tk : ((2 : ℝ) ^ t) ^ k = 2 ^ (t * k) := by rw [← pow_mul]
  have hfirst : (((∏ p, ⌊2 * Q' p⌋₊ : ℕ) : ℝ)) + q ≤ (2 ^ (t * k) + 1) * (q : ℝ) ^ (max 1 ((k : ℝ) * s)) := by
    have h2k : (0 : ℝ) ≤ 2 ^ (t * k) := by positivity
    have := hfl
    rw [h2tk, hMk] at this
    nlinarith [mul_le_mul_of_nonneg_left hmax1 h2k]
  have hsecond : ((k * t : ℕ) : ℝ) ^ (k * t) * F₀ ^ (k * t) * ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1)) ≤
      ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) * (q : ℝ) ^ (k * s) := by
    have h1 : F₀ ^ (k * t) * ((3 * F₀) ^ (k * t) * M ^ k) = (3 * F₀ ^ 2) ^ (k * t) * M ^ k := by
      rw [← mul_assoc, ← mul_pow]; ring_nf
    calc ((k * t : ℕ) : ℝ) ^ (k * t) * F₀ ^ (k * t) * ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1))
        ≤ ((k * t : ℕ) : ℝ) ^ (k * t) * F₀ ^ (k * t) * ((3 * F₀) ^ (k * t) * M ^ k) :=
          mul_le_mul_of_nonneg_left hpr (by positivity)
      _ = ((k * t : ℕ) : ℝ) ^ (k * t) * (F₀ ^ (k * t) * ((3 * F₀) ^ (k * t) * M ^ k)) := by ring
      _ = ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) * (q : ℝ) ^ (k * s) := by rw [h1, hMk]; ring
  have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (k * s * u)) := Real.rpow_pos_of_pos hq0 _
  have hexp : (q : ℝ) ^ (max 1 ((k : ℝ) * s)) * (q : ℝ) ^ (k * s) =
      (q : ℝ) ^ (momExp k s u) * (q : ℝ) ^ (2 * (k * s * u)) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
    unfold momExp
    congr 1; ring
  have hmain : c * (q : ℝ) ^ (2 * (k * s * u)) ≤
      (2 ^ (t * k) + 1) * ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) *
        ((q : ℝ) ^ (momExp k s u) * (q : ℝ) ^ (2 * (k * s * u))) := by
    rw [← hexp]
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    have hA0 : 0 ≤ ((k * t : ℕ) : ℝ) ^ (k * t) * F₀ ^ (k * t) * ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1)) := by
      have : ∀ p : Fin k × Fin t, 0 ≤ F₀ * (2 * Q' p + 1) := fun p => by have := hQ'0 p; positivity
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p _ => this p)
    calc c * (q : ℝ) ^ (2 * (k * s * u)) = (M ^ u) ^ (2 * k) * c := by rw [hVk]; ring
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∏ p, SieveWeight.Sp χ f0 (Q' p) (y' p)‖ ^ 2 := hmarkov
      _ ≤ (((∏ p, ⌊2 * Q' p⌋₊ : ℕ) : ℝ) + q) *
            (((k * t : ℕ) : ℝ) ^ (k * t) * F₀ ^ (k * t) * ∏ p : Fin k × Fin t, (F₀ * (2 * Q' p + 1))) := by
          refine hmom.trans (le_of_eq ?_)
          push_cast
          ring
      _ ≤ ((2 ^ (t * k) + 1) * (q : ℝ) ^ (max 1 ((k : ℝ) * s))) *
            (((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) * (q : ℝ) ^ (k * s)) :=
          mul_le_mul hfirst hsecond hA0 (by positivity)
      _ = (2 ^ (t * k) + 1) * ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) *
            ((q : ℝ) ^ (max 1 ((k : ℝ) * s)) * (q : ℝ) ^ (k * s)) := by ring
  have hmain' : c * (q : ℝ) ^ (2 * (k * s * u)) ≤
      (2 ^ (t * k) + 1) * ((k * t : ℕ) : ℝ) ^ (k * t) * (3 * F₀ ^ 2) ^ (k * t) * (q : ℝ) ^ (momExp k s u) *
        (q : ℝ) ^ (2 * (k * s * u)) := by
    linarith [hmain]
  exact le_of_mul_le_mul_right hmain' hpos

/-! ### The count by the large values of a power -/

/-- **The characters at which a product of smoothed prime sums is large, by Chen, Gupta and Li's Proposition 3.1.**
For a product `∏_{i∈κ} Sp χ f0 (Q i) (y i)` of `K = |κ| ≥ 1` sums with `Q_i > 0`: given the proposition and
`0 < ε ≤ 1` there is `C ≥ 0` such that, with `X = ∏2Q_i` and `Y = ∏(Q_i/2)`, for `Y ≥ 2q^{2/3} + 2` and
`X^{7/10}·D ≤ V ≤ (Y/2)^{4/5}`, `D = (2K+1)K^K F₁^K`, `#{χ : V ≤ |∏_i Sp_i|} ≤ (2K+1)·C·q^ε(qX)^ε·lvB q X (V/D)`.
The product is a polynomial with coefficients at most `K^K F₁^K` supported in `[Y, X]`, `X = 4^K Y`, cut in `2K + 1`
dyadic blocks. -/
theorem card_prodSp_pow_large (hP : LinnikCGLLV.CGLProp31) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (f0 : ℝ → ℝ) (F₁ : ℝ), 1 ≤ F₁ → (∀ u, |f0 u| ≤ F₁) →
      Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (Q y : κ → ℝ) (V : ℝ),
      1 ≤ Fintype.card κ → (∀ i, 0 < Q i) →
      2 * (q : ℝ) ^ (2 / 3 : ℝ) + 2 ≤ ∏ i, Q i / 2 →
      (∏ i, 2 * Q i) ^ (7 / 10 : ℝ) *
          ((2 * (Fintype.card κ : ℝ) + 1) * (Fintype.card κ : ℝ) ^ Fintype.card κ * F₁ ^ Fintype.card κ) ≤ V →
      V ≤ ((∏ i, Q i / 2) / 2) ^ (4 / 5 : ℝ) →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          V ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖).card : ℝ) ≤
        (2 * (Fintype.card κ : ℝ) + 1) * (C * (q : ℝ) ^ ε * ((q : ℝ) * ∏ i, 2 * Q i) ^ ε *
          lvB q (∏ i, 2 * Q i) (V / ((2 * (Fintype.card κ : ℝ) + 1) * (Fintype.card κ : ℝ) ^ Fintype.card κ *
            F₁ ^ Fintype.card κ))) := by
  obtain ⟨C, hC0, hC⟩ := LinnikCGLLV.cgl_all hP hε hε1
  refine ⟨C, hC0, fun q _ f0 F₁ hF1 hF₀ hsupp κ _ _ Q y V hK hQ h23 hV1 hV2 => ?_⟩
  classical
  set K : ℕ := Fintype.card κ with hKdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hF10 : 0 ≤ F₁ := by linarith
  -- the constants
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (K : ℝ) ^ K * F₁ ^ K := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hE]
    have h1 : (1 : ℝ) ≤ (K : ℝ) ^ K := one_le_pow₀ (by exact_mod_cast hK)
    have h2 : (1 : ℝ) ≤ F₁ ^ K := one_le_pow₀ hF1
    nlinarith
  have hE0 : 0 < E := by linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = 2 * K + 1 := ⟨_, rfl⟩
  have hJpos : 0 < J := by omega
  have hJr : (J : ℝ) = 2 * (K : ℝ) + 1 := by rw [hJ]; push_cast; ring
  have hD : (2 * (K : ℝ) + 1) * (K : ℝ) ^ K * F₁ ^ K = J * E := by rw [hJr, hE]; ring
  rw [hD] at hV1 ⊢
  have hJE0 : (0 : ℝ) < J * E := by positivity
  have hJE1 : (1 : ℝ) ≤ J * E := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
    nlinarith
  -- the sizes of the product's range
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∏ i, 2 * Q i := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∏ i, Q i / 2 := ⟨_, rfl⟩
  rw [← hX] at hV1 ⊢
  rw [← hY] at h23 hV2
  have hXY : X = 4 ^ K * Y := by
    have h1 : ∀ i, 2 * Q i = 4 * (Q i / 2) := fun i => by ring
    rw [hX, hY, Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hY2 : 2 ≤ Y := by
    have h1 : (0 : ℝ) ≤ (q : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
    linarith
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := by rw [hXY]; positivity
  have hV0 : 0 < V := by
    have h1 : 0 < X ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hX0 _
    exact lt_of_lt_of_le (mul_pos h1 hJE0) hV1
  -- the lower end of the blocks
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈Y⌉₊ - 1 := ⟨_, rfl⟩
  have hceil2 : 2 ≤ ⌈Y⌉₊ := by
    have h1 : ((2 : ℕ) : ℝ) ≤ Y := by exact_mod_cast hY2
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil Y))
  have hM1 : 1 ≤ M := by omega
  have hMceil : M + 1 = ⌈Y⌉₊ := by omega
  have hMlt : (M : ℝ) < Y := by
    have h1 : M < ⌈Y⌉₊ := by omega
    exact Nat.lt_ceil.1 h1
  have hMge : Y - 1 ≤ (M : ℝ) := by
    have h1 : ((⌈Y⌉₊ : ℕ) : ℝ) = (M : ℝ) + 1 := by rw [← hMceil]; push_cast; ring
    have h2 : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
    linarith
  have hMhalf : Y / 2 ≤ (M : ℝ) := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  -- the product's coefficients
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = spProdSet Q := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = spProdCoeff f0 Q y := ⟨_, rfl⟩
  have hcE : ∀ n, ‖c n‖ ≤ E := by
    intro n
    rw [hc, hE]
    exact norm_spProdCoeff_le hF₀ hQ y n
  have hczero : ∀ n : ℕ, n ∉ Finset.Ioc M (M * 2 ^ J) → c n = 0 := by
    intro n hn
    rw [hc]
    refine spProdCoeff_eq_zero hsupp hQ y ?_
    rw [← hY, ← hX]
    rw [Finset.mem_Ioc, not_and_or] at hn
    rcases hn with h | h
    · left
      have h1 : (n : ℝ) ≤ M := by exact_mod_cast not_lt.1 h
      linarith
    · right
      have h1 : M * 2 ^ J < n := not_le.1 h
      have h2 : ((M * 2 ^ J : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast h1
      have h3 : X ≤ ((M * 2 ^ J : ℕ) : ℝ) := by
        push_cast
        have h4 : (2 : ℝ) ^ J = 2 * 4 ^ K := by
          rw [hJ, pow_succ, pow_mul]; norm_num; ring
        rw [hXY, h4]
        have h5 : (0 : ℝ) < 4 ^ K := by positivity
        nlinarith
      linarith
  -- the normalised coefficients, and the product as a sum over the blocks
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n => if n ∈ S then c n / (E : ℂ) else 0 := ⟨_, rfl⟩
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    rw [ha]
    by_cases hn : n ∈ S
    · simp only [hn, ite_true]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0, div_le_one hE0]
      exact hcE n
    · simp only [hn, ite_false, norm_zero]
      exact zero_le_one
  obtain ⟨blk, hblk⟩ : ∃ blk : DirichletCharacter ℂ q → ℕ → ℂ, blk = fun χ i =>
      ∑ n ∈ Finset.Ioc (M * 2 ^ i) (M * 2 ^ (i + 1)), a n * χ n := ⟨_, rfl⟩
  have hpow : ∀ χ : DirichletCharacter ℂ q,
      ∏ i, SieveWeight.Sp χ f0 (Q i) (y i) = (E : ℂ) * ∑ i ∈ Finset.range J, blk χ i := by
    intro χ
    have h1 : ∏ i, SieveWeight.Sp χ f0 (Q i) (y i) = ∑ n ∈ S, c n * χ n := by
      rw [prod_Sp_eq_dp, dp_zero, ← hS, ← hc]
    have h2 : ∑ n ∈ S, c n * χ n = ∑ n ∈ S ∩ Finset.Ioc M (M * 2 ^ J), c n * χ n := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left fun n hn hnot => ?_
      have hnI : n ∉ Finset.Ioc M (M * 2 ^ J) := fun h => hnot (Finset.mem_inter.2 ⟨hn, h⟩)
      rw [hczero n hnI, zero_mul]
    have h3 : (E : ℂ) * ∑ n ∈ Finset.Ioc M (M * 2 ^ J), a n * χ n =
        ∑ n ∈ S ∩ Finset.Ioc M (M * 2 ^ J), c n * χ n := by
      rw [Finset.mul_sum, Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ha]
      by_cases hn : n ∈ S
      · simp only [hn, ite_true]
        have hEc : (E : ℂ) ≠ 0 := by exact_mod_cast hE0.ne'
        field_simp
      · simp only [hn, ite_false, zero_mul, mul_zero]
    rw [h1, h2, ← h3, sum_Ioc_dyadic, hblk]
  -- the characters at which a block is large
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Finset (DirichletCharacter ℂ q), R = fun i =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ q => V / (J * E) ≤ ‖blk χ i‖ := ⟨_, rfl⟩
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      V ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖) ⊆ (Finset.range J).biUnion R := by
    intro χ hχ
    have hχV : V ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖ := (Finset.mem_filter.1 hχ).2
    rw [hpow χ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0] at hχV
    have h1 : V / E ≤ ‖∑ i ∈ Finset.range J, blk χ i‖ := by
      rw [div_le_iff₀ hE0]; linarith
    obtain ⟨i, hi, hbi⟩ := exists_large_of_sum hJpos (blk χ) h1
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, ?_⟩
    rw [hR]
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have h2 : V / (J * E) = V / E / J := by field_simp
    rw [h2]; exact hbi
  -- Chen, Gupta and Li's count for each block
  have hblock : ∀ i < J, ((R i).card : ℝ) ≤
      C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) := by
    intro i hi
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M * 2 ^ i := ⟨_, rfl⟩
    have h2N : 2 * N = M * 2 ^ (i + 1) := by rw [hN, pow_succ]; ring
    have hNM : (M : ℝ) ≤ N := by
      rw [hN]; push_cast
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hNX : (N : ℝ) ≤ X := by
      have h1 : (2 : ℝ) ^ i ≤ 4 ^ K := by
        have h2 : i ≤ 2 * K := by omega
        calc (2 : ℝ) ^ i ≤ 2 ^ (2 * K) := pow_le_pow_right₀ (by norm_num) h2
          _ = 4 ^ K := by rw [pow_mul]; norm_num
      rw [hN, hXY]; push_cast
      have h3 : (0 : ℝ) ≤ 2 ^ i := by positivity
      nlinarith
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hNM
    have hcount := hC q (R i) (fun _ => 0) 1 N (V / (J * E)) a le_rfl
      (by
        rw [mul_one]
        have h1 : (q : ℝ) ^ (2 / 3 : ℝ) ≤ Y - 1 := by
          have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
          linarith
        linarith)
      (by
        have h1 : (N : ℝ) ^ (7 / 10 : ℝ) ≤ X ^ (7 / 10 : ℝ) :=
          Real.rpow_le_rpow hN0.le hNX (by norm_num)
        rw [le_div_iff₀ hJE0]
        exact (mul_le_mul_of_nonneg_right h1 hJE0.le).trans hV1)
      (by
        have h1 : V / (J * E) ≤ V := div_le_self hV0.le hJE1
        have h2 : (Y / 2) ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (hMhalf.trans hNM) (by norm_num)
        linarith)
      ha1 (fun _ _ => by simp)
      (by
        intro χ hχ
        rw [hR] at hχ
        have hb : V / (J * E) ≤ ‖blk χ i‖ := (Finset.mem_filter.1 hχ).2
        rw [hblk] at hb
        rw [h2N, hN]
        refine hb.trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        simp)
    have hlv : LinnikCGLLV.p31B q 1 N (V / (J * E)) ≤ lvB q X (V / (J * E)) := by
      unfold LinnikCGLLV.p31B lvB
      rw [mul_one]
      have hq12 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hq0.le _
      have hq43 : (0 : ℝ) ≤ (q : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg hq0.le _
      gcongr
    have hqN : ((q : ℝ) * 1 * N) ^ ε ≤ ((q : ℝ) * X) ^ ε := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hNX hq0.le) hε.le
    have hlv0 : 0 ≤ LinnikCGLLV.p31B q 1 N (V / (J * E)) := LinnikCGLLV.p31B_nonneg q zero_le_one N _
    calc ((R i).card : ℝ) ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * 1 * N) ^ ε * LinnikCGLLV.p31B q 1 N (V / (J * E)) :=
          hcount
      _ ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) := by
          have hCq : 0 ≤ C * (q : ℝ) ^ ε := mul_nonneg hC0 (Real.rpow_nonneg hq0.le _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hqN hCq) hlv hlv0
            (mul_nonneg hCq (Real.rpow_nonneg (by positivity) _))
  -- the union of the blocks' sets
  calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        V ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖).card : ℝ)
      ≤ (((Finset.range J).biUnion R).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range J, ((R i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range J, C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E)) :=
        Finset.sum_le_sum fun i hi => hblock i (Finset.mem_range.1 hi)
    _ = (2 * (K : ℝ) + 1) * (C * (q : ℝ) ^ ε * ((q : ℝ) * X) ^ ε * lvB q X (V / (J * E))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hJr]

/-- `(M^{1/t})^{tk} = M^k` for `M ≥ 0` and `t ≥ 1`. -/
lemma rpow_inv_pow_mul {M : ℝ} (hM : 0 ≤ M) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    (M ^ (1 / (t : ℝ))) ^ (t * k) = M ^ k := by
  have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [pow_mul, ← Real.rpow_natCast (M ^ (1 / (t : ℝ))) t, ← Real.rpow_mul hM, one_div_mul_cancel ht0,
    Real.rpow_one]

/-- **The characters at which a product of prime sums is large, by the large values of its powers, in exponents.**
Given Chen, Gupta and Li's Proposition 3.1 (`hP`), bounds `k_max` and `t_max` and `F₁ ≥ 1`, there are `C ≥ 1` and
`q₀` such that for `q ≥ q₀`, `f0` with `|f0| ≤ F₁` and support in `[1/2, 2]`, `1 ≤ t ≤ t_max` scales `Q_i ≥ 4` with
product `M` and `1 ≤ k ≤ k_max`: `#{χ : M^u ≤ |∏_i Sp χ f0 (Q i) (y i)|} ≤ C q^{lvExp k s u}`, `s = log_q M`, the
count of one prime sum of length `M`. The power `G^k` is the product of `kt` sums (`card_prodSp_pow_large`), whose
range is `[(Q'/2)^{kt}, (2Q')^{kt}]` for `Q' = M^{1/t}`, so the margins `lv_conds`, `lv_fac` and `lvB_le` apply at
`Q'` and `kt`. -/
theorem card_prodSp_large_lv (hP : LinnikCGLLV.CGLProp31) (kmax tmax : ℕ) {F₁ : ℝ} (hF1 : 1 ≤ F₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (f0 : ℝ → ℝ), (∀ u, |f0 u| ≤ F₁) →
      Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (t : ℕ) (Q y : Fin t → ℝ) (k : ℕ) (u : ℝ), 1 ≤ t → t ≤ tmax →
      1 ≤ k → k ≤ kmax → (∀ i, 4 ≤ Q i) →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          (∏ i, Q i) ^ u ≤ ‖∏ i, SieveWeight.Sp χ f0 (Q i) (y i)‖).card : ℝ) ≤
        C * (q : ℝ) ^ lvExp k (Real.logb q (∏ i, Q i)) u := by
  have hE0 : (0 : ℝ) < lvE := by unfold lvE; norm_num
  have hE1 : lvE = 1 / 10 ^ 5 := rfl
  obtain ⟨C₀, hC₀0, hC₀⟩ := card_prodSp_pow_large hP (ε := lvE / 5) (by positivity) (by rw [hE1]; norm_num)
  -- the constants, at the number `K = tk ≤ K_max` of sums in the power
  obtain ⟨Kmax, hKmax⟩ : ∃ K : ℕ, K = tmax * kmax := ⟨_, rfl⟩
  obtain ⟨Dm, hDm⟩ : ∃ D : ℝ, D = (2 * (Kmax : ℝ) + 1) * (Kmax : ℝ) ^ Kmax * F₁ ^ Kmax := ⟨_, rfl⟩
  have hDk : ∀ K : ℕ, 1 ≤ K → K ≤ Kmax →
      1 ≤ (2 * (K : ℝ) + 1) * (K : ℝ) ^ K * F₁ ^ K ∧ (2 * (K : ℝ) + 1) * (K : ℝ) ^ K * F₁ ^ K ≤ Dm := by
    intro K hk1 hk2
    have hkk : (K : ℝ) ≤ Kmax := by exact_mod_cast hk2
    have hk1' : (1 : ℝ) ≤ K := by exact_mod_cast hk1
    have h1 : (1 : ℝ) ≤ (K : ℝ) ^ K := one_le_pow₀ hk1'
    have h2 : (1 : ℝ) ≤ F₁ ^ K := one_le_pow₀ hF1
    have h3 : (K : ℝ) ^ K ≤ (Kmax : ℝ) ^ Kmax :=
      (pow_le_pow_left₀ (by positivity) hkk K).trans (pow_le_pow_right₀ (by linarith) hk2)
    have h4 : F₁ ^ K ≤ F₁ ^ Kmax := pow_le_pow_right₀ hF1 hk2
    constructor
    · have h5 : (1 : ℝ) ≤ 2 * (K : ℝ) + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (2 * (K : ℝ) + 1) * (K : ℝ) ^ K * F₁ ^ K :=
            mul_le_mul (mul_le_mul h5 h1 zero_le_one (by linarith)) h2 zero_le_one (by positivity)
    · rw [hDm]
      exact mul_le_mul (mul_le_mul (by linarith) h3 (by positivity) (by positivity)) h4 (by positivity)
        (by positivity)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 ((2 * (Kmax : ℝ) + 1) * (C₀ * 2 ^ Kmax * (3 * (Dm ^ 4 * 8 ^ Kmax)))) :=
    ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hev : ∀ᶠ q : ℕ in Filter.atTop, 4 * 2 ^ Kmax * Dm ≤ (q : ℝ) ^ (lvE / 2) ∧ 2 ≤ q :=
    ((((tendsto_rpow_atTop (by positivity : 0 < lvE / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * 2 ^ Kmax * Dm))).and (Filter.eventually_ge_atTop 2)
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨C, hC1, q₀, fun q _ hq f0 hF₀ hsupp t Q y k u ht htm hk hkm hQ => ?_⟩
  obtain ⟨hqB, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ0 : ∀ i, 0 < Q i := fun i => by linarith [hQ i]
  set G : DirichletCharacter ℂ q → ℂ := fun χ => ∏ i, SieveWeight.Sp χ f0 (Q i) (y i) with hGdef
  set M : ℝ := ∏ i, Q i with hMdef
  have hM1 : 1 ≤ M := Finset.one_le_prod₀ fun i _ => by linarith [hQ i]
  have hM0 : 0 < M := by linarith
  -- the trivial count
  have htriv : ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖G χ‖).card : ℝ) ≤
      C * (q : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have h1 := LinnikDensity.card_chars_le (Finset.univ.filter fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖G χ‖)
    have h2 : 1 * (q : ℝ) ≤ C * q := mul_le_mul_of_nonneg_right hC1 hq0.le
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.logb q M := ⟨_, rfl⟩
  rw [← hs]
  have hMs : M = (q : ℝ) ^ s := by rw [hs, Real.rpow_logb hq0 hq1.ne' hM0]
  by_cases hc : 2 / 3 + lvE ≤ (k : ℝ) * s ∧ 7 / 10 + lvE ≤ u
  swap
  · have h1 : lvExp k s u = 1 := by unfold lvExp; exact ite_eq_right hc
    rw [h1]; exact htriv
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ, u' = min u (4 / 5 - lvE) := ⟨_, rfl⟩
  have hlvE : lvExp k s u = min 1 (lvRaw k s u' + lvE) := by unfold lvExp; rw [ite_eq_left hc, hu']
  rw [hlvE]
  by_cases h1 : 1 ≤ lvRaw k s u' + lvE
  · rw [min_eq_left h1]; exact htriv
  rw [min_eq_right (not_le.1 h1).le]
  have hlt : lvRaw k s u' + lvE < 1 := not_le.1 h1
  have hu'1 : u' ≤ 4 / 5 - lvE := hu' ▸ min_le_right _ _
  have hu'u : u' ≤ u := hu' ▸ min_le_left _ _
  have hu'0 : 7 / 10 + lvE ≤ u' := by
    rw [hu']; exact le_min hc.2 (by rw [hE1]; norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (k : ℝ) * s := ⟨_, rfl⟩
  have hm23 : 2 / 3 + lvE ≤ m := hm ▸ hc.1
  have hraw : lvRaw k s u' = max (2 * m * (1 - u')) (max (1 / 2 + m * (3 - 4 * u')) (4 / 3 + m * (2 - 4 * u'))) := by
    unfold lvRaw; rw [hm]
  have hr1 : 2 * m * (1 - u') ≤ lvRaw k s u' := by rw [hraw]; exact le_max_left _ _
  have hr2 : 1 / 2 + m * (3 - 4 * u') ≤ lvRaw k s u' := by
    rw [hraw]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hr3 : 4 / 3 + m * (2 - 4 * u') ≤ lvRaw k s u' := by
    rw [hraw]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hm52 : m ≤ 5 / 2 := by nlinarith
  -- the power as `kt` sums at the scale `Q' = M^{1/t}`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = t * k := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hKm : K ≤ Kmax := by rw [hK, hKmax]; exact Nat.mul_le_mul htm hkm
  obtain ⟨Q', hQ'⟩ : ∃ Q' : ℝ, Q' = M ^ (1 / (t : ℝ)) := ⟨_, rfl⟩
  have hQ'0 : 0 < Q' := by rw [hQ']; exact Real.rpow_pos_of_pos hM0 _
  have hQ'K : Q' ^ K = (q : ℝ) ^ m := by
    rw [hQ', hK, rpow_inv_pow_mul hM0.le ht, hMs, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, hm, mul_comm]
  have hQ't : Q' ^ t = M := by
    have := rpow_inv_pow_mul hM0.le ht 1
    rw [mul_one, pow_one] at this
    rw [hQ', this]
  set Qp : Fin k × Fin t → ℝ := fun p => Q p.2 with hQp
  set yp : Fin k × Fin t → ℝ := fun p => y p.2 with hyp
  have hcardp : Fintype.card (Fin k × Fin t) = K := by rw [hK]; simp [mul_comm]
  have hXp : ∏ p, 2 * Qp p = (2 * Q') ^ K := by
    rw [hQp, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hMdef, ← hQ't, hK,
      ← mul_pow, pow_mul]
  have hYp : ∏ p, Qp p / 2 = (Q' / 2) ^ K := by
    rw [hQp, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hMdef, ← hQ't, hK,
      ← div_pow, pow_mul]
  have hGp : ∀ χ : DirichletCharacter ℂ q, ‖∏ p, SieveWeight.Sp χ f0 (Qp p) (yp p)‖ = ‖G χ‖ ^ k := by
    intro χ
    rw [hGdef, ← norm_pow, prod_pow_eq_prod_prod]
  -- the size and the constants
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (q : ℝ) ^ (m * u') := ⟨_, rfl⟩
  have hVM : V = (M ^ u') ^ k := by
    rw [hV, hMs, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, hm]
    congr 1; ring
  obtain ⟨hD1, hDle⟩ := hDk K hK1 hKm
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (2 * (K : ℝ) + 1) * (K : ℝ) ^ K * F₁ ^ K := ⟨_, rfl⟩
  rw [← hD] at hD1 hDle
  have hD0 : 0 < D := by linarith
  have h2k : (2 : ℝ) ^ K ≤ 2 ^ Kmax := pow_le_pow_right₀ (by norm_num) hKm
  have h8k : (8 : ℝ) ^ K ≤ 8 ^ Kmax := pow_le_pow_right₀ (by norm_num) hKm
  have hBk : 4 * 2 ^ K * D ≤ (q : ℝ) ^ (lvE / 2) := by
    have h5 : (4 : ℝ) * 2 ^ K * D ≤ 4 * 2 ^ Kmax * Dm :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2k (by norm_num)) hDle hD0.le (by positivity)
    linarith
  obtain ⟨hc1, hc2, hc3⟩ := lv_conds hq1 hQ'K hm23 hu'0 hu'1 hD1 hBk
  rw [← hV] at hc2 hc3
  -- the count for the power
  have hcount := hC₀ q f0 F₁ hF1 hF₀ hsupp (κ := Fin k × Fin t) Qp yp V (by rw [hcardp]; exact hK1)
    (fun p => hQ0 p.2) (by rw [hYp]; exact hc1) (by rw [hXp, hcardp, ← hD]; exact hc2) (by rw [hYp]; exact hc3)
  rw [hcardp, ← hD, hXp] at hcount
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖G χ‖) ⊆
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => V ≤ ‖∏ p, SieveWeight.Sp χ f0 (Qp p) (yp p)‖) := by
    intro χ hχ
    have h1 : M ^ u ≤ ‖G χ‖ := (Finset.mem_filter.1 hχ).2
    have h2 : M ^ u' ≤ M ^ u := Real.rpow_le_rpow_of_exponent_le hM1 hu'u
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hGp, hVM]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hM0.le _) (h2.trans h1) k
  have hfac := lv_fac hq1 hQ'K hm52
  have hlvB := lvB_le (u := u') hq1 hQ'K hD1 hr1 hr2 hr3
  rw [← hV] at hlvB
  have hlvB0 : 0 ≤ lvB q ((2 * Q') ^ K) (V / D) := lvB_nonneg q (by positivity) _
  have hkk : 2 * (K : ℝ) + 1 ≤ 2 * (Kmax : ℝ) + 1 := by
    have : (K : ℝ) ≤ Kmax := by exact_mod_cast hKm
    linarith
  have hqR : (q : ℝ) ^ lvE * (q : ℝ) ^ lvRaw k s u' = (q : ℝ) ^ (lvRaw k s u' + lvE) := by
    rw [← Real.rpow_add hq0, add_comm]
  have hqE0 : 0 ≤ (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q') ^ K) ^ (lvE / 5) :=
    mul_nonneg (Real.rpow_nonneg hq0.le _) (Real.rpow_nonneg (by positivity) _)
  have hfac' : (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q') ^ K) ^ (lvE / 5) ≤ 2 ^ Kmax * (q : ℝ) ^ lvE :=
    hfac.trans (mul_le_mul_of_nonneg_right h2k (Real.rpow_nonneg hq0.le _))
  have hlvB' : lvB q ((2 * Q') ^ K) (V / D) ≤ 3 * (Dm ^ 4 * 8 ^ Kmax) * (q : ℝ) ^ lvRaw k s u' := by
    refine hlvB.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq0.le _))
    have hD4 : D ^ 4 ≤ Dm ^ 4 := pow_le_pow_left₀ hD0.le hDle 4
    have h6 : D ^ 4 * 8 ^ K ≤ Dm ^ 4 * 8 ^ Kmax := mul_le_mul hD4 h8k (by positivity) (by positivity)
    linarith
  calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => M ^ u ≤ ‖G χ‖).card : ℝ)
      ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          V ≤ ‖∏ p, SieveWeight.Sp χ f0 (Qp p) (yp p)‖).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (2 * (K : ℝ) + 1) * (C₀ * (q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q') ^ K) ^ (lvE / 5) *
          lvB q ((2 * Q') ^ K) (V / D)) := hcount
    _ = (2 * (K : ℝ) + 1) * (C₀ * ((q : ℝ) ^ (lvE / 5) * ((q : ℝ) * (2 * Q') ^ K) ^ (lvE / 5)) *
          lvB q ((2 * Q') ^ K) (V / D)) := by ring
    _ ≤ (2 * (Kmax : ℝ) + 1) * (C₀ * (2 ^ Kmax * (q : ℝ) ^ lvE) *
          (3 * (Dm ^ 4 * 8 ^ Kmax) * (q : ℝ) ^ lvRaw k s u')) := by
        refine mul_le_mul hkk ?_ (mul_nonneg (mul_nonneg hC₀0 hqE0) hlvB0) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hfac' hC₀0) hlvB' hlvB0
          (mul_nonneg hC₀0 (by positivity))
    _ = (2 * (Kmax : ℝ) + 1) * (C₀ * 2 ^ Kmax * (3 * (Dm ^ 4 * 8 ^ Kmax))) *
          ((q : ℝ) ^ lvE * (q : ℝ) ^ lvRaw k s u') := by ring
    _ ≤ C * (q : ℝ) ^ (lvRaw k s u' + lvE) := by
        rw [hqR]
        exact mul_le_mul_of_nonneg_right (hC ▸ le_max_right _ _) (Real.rpow_nonneg hq0.le _)

/-! ### The counts for a part: a product over a finite set of indices -/

/-- A product over a finite set of naturals is the product over `Fin` of its size, through `s.equivFin`. -/
lemma prod_finset_eq_prod_fin {M : Type*} [CommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ∏ j ∈ s, f j = ∏ i : Fin s.card, f (s.equivFin.symm i) := by
  rw [← Finset.prod_coe_sort s f]
  exact Fintype.prod_equiv s.equivFin _ _ fun x => by simp

/-- **The count by the moment, for a part** `∏_{j∈s} Sp χ f0 (Q j) (h j)` with each `Q_j ≥ 1`: `card_prodSp_large`
with the members enumerated. -/
theorem card_part_large [NeZero q] (hq : 1 < (q : ℝ)) {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀)
    (s : Finset ℕ) {Q : ℕ → ℝ} (hQ : ∀ j ∈ s, 1 ≤ Q j) (h : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        (∏ j ∈ s, Q j) ^ u ≤ ‖∏ j ∈ s, SieveWeight.Sp χ f0 (Q j) (h j)‖).card : ℝ) ≤
      (2 ^ (s.card * k) + 1) * ((k * s.card : ℕ) : ℝ) ^ (k * s.card) * (3 * F₀ ^ 2) ^ (k * s.card) *
        (q : ℝ) ^ (momExp k (Real.logb q (∏ j ∈ s, Q j)) u) := by
  have e1 : ∏ j ∈ s, Q j = ∏ i : Fin s.card, Q (s.equivFin.symm i) := prod_finset_eq_prod_fin s Q
  have e2 : ∀ χ : DirichletCharacter ℂ q, ∏ j ∈ s, SieveWeight.Sp χ f0 (Q j) (h j) =
      ∏ i : Fin s.card, SieveWeight.Sp χ f0 (Q (s.equivFin.symm i)) (h (s.equivFin.symm i)) :=
    fun χ => prod_finset_eq_prod_fin s _
  simp_rw [e2]
  rw [e1]
  exact card_prodSp_large hq hF₀ (fun i => hQ _ (s.equivFin.symm i).2) _ hk u

/-- **The count by the large values, for a part**: `card_prodSp_large_lv` for `∏_{j∈s} Sp χ f0 (Q j) (h j)` with
`1 ≤ |s| ≤ t_max` members, each `Q_j ≥ 4`. -/
theorem card_part_large_lv (hP : LinnikCGLLV.CGLProp31) (kmax tmax : ℕ) {F₁ : ℝ} (hF1 : 1 ≤ F₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (f0 : ℝ → ℝ), (∀ u, |f0 u| ≤ F₁) →
      Function.support f0 ⊆ Set.Icc (1 / 2) 2 → ∀ (s : Finset ℕ) (Q h : ℕ → ℝ) (k : ℕ) (u : ℝ), 1 ≤ s.card →
      s.card ≤ tmax → 1 ≤ k → k ≤ kmax → (∀ j ∈ s, 4 ≤ Q j) →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          (∏ j ∈ s, Q j) ^ u ≤ ‖∏ j ∈ s, SieveWeight.Sp χ f0 (Q j) (h j)‖).card : ℝ) ≤
        C * (q : ℝ) ^ lvExp k (Real.logb q (∏ j ∈ s, Q j)) u := by
  obtain ⟨C, hC1, q₀, hC⟩ := card_prodSp_large_lv hP kmax tmax hF1
  refine ⟨C, hC1, q₀, fun q _ hq f0 hF₀ hsupp s Q h k u hs1 hst hk hkm hQ => ?_⟩
  have e1 : ∏ j ∈ s, Q j = ∏ i : Fin s.card, Q (s.equivFin.symm i) := prod_finset_eq_prod_fin s Q
  have e2 : ∀ χ : DirichletCharacter ℂ q, ∏ j ∈ s, SieveWeight.Sp χ f0 (Q j) (h j) =
      ∏ i : Fin s.card, SieveWeight.Sp χ f0 (Q (s.equivFin.symm i)) (h (s.equivFin.symm i)) :=
    fun χ => prod_finset_eq_prod_fin s _
  simp_rw [e2]
  rw [e1]
  exact hC q hq f0 hF₀ hsupp s.card _ _ k u hs1 hst hk hkm fun i => hQ _ (s.equivFin.symm i).2

end SieveTypeIIHM
