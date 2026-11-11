/-
# The frozen part of a reversal as tuples of primes

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The frozen part of a reversal through the largest prime (`SieveAd.frozS`) is the set of pairs
of a tuple `a` of the box `βx` and a cofactor `m`, rough at the last prime of `a`, with `∏a·m` in a slab. The
estimates of the library are for tuples of primes, so the cofactor is written out as its primes: a number rough at
`z ≥ 2` and below `z^{T+1}` is the product of a unique non-increasing tuple of at most `T` primes at least `z`
(`SieveChain.sum_rough_tuples`).

* `frozP q e₁ e₂ βx t`: the frozen part with a cofactor of `t` primes: the tuples of `s + 1 + t` primes up to `N₂`
  whose first `s + 1` entries are a tuple of `βx`, whose last `t` do not increase and are at least the last of the
  first, and whose product (`prodR`) lies in `(x^{e₁/DEN}, x^{e₂/DEN}]` (`mem_frozP`).
* `sum_frozS_eq`: for `e₂ ≤ DEN` and `(T + 1)·lo_s ≥ DEN + 1`, at a large modulus, **a sum over the frozen part of
  a function of `∏a·m` is the sum over `t ≤ T` of the sums over `frozP q e₁ e₂ βx t` of the function of the
  product**. `dIF_frozS_eq`, `dJF_frozS_eq`: so for the terms over the frozen part.
* `evIF_frozS`, `evJF_frozS`: **the terms over the frozen part are evaluated when those over each `frozP … t`,
  `t ≤ T`, are**; `evIF_frozS_at`, `evJF_frozS_at` with the route as a variable.

The file imports `SieveAdFlip.lean`.
-/
import SieveAdFlip

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### Tuples in two parts -/

/-- The product of a tuple. -/
def prodR {n : ℕ} (u : Fin n → ℕ) : ℕ := ∏ i, u i

theorem append_castAdd {m n : ℕ} (a : Fin m → ℕ) (y : Fin n → ℕ) :
    (fun i => Fin.append a y (Fin.castAdd n i)) = a := funext fun i => Fin.append_left a y i

theorem append_natAdd {m n : ℕ} (a : Fin m → ℕ) (y : Fin n → ℕ) :
    (fun j => Fin.append a y (Fin.natAdd m j)) = y := funext fun j => Fin.append_right a y j

theorem append_parts {m n : ℕ} (u : Fin (m + n) → ℕ) :
    Fin.append (fun i => u (Fin.castAdd n i)) (fun j => u (Fin.natAdd m j)) = u := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
  · rw [Fin.append_right]

/-- The product of a tuple is the product of those of its two parts. -/
theorem prodR_split {m n : ℕ} (u : Fin (m + n) → ℕ) :
    prodR u = prodR (fun i => u (Fin.castAdd n i)) * prodR (fun j => u (Fin.natAdd m j)) :=
  Fin.prod_univ_add u

theorem prodR_append {m n : ℕ} (a : Fin m → ℕ) (y : Fin n → ℕ) : prodR (Fin.append a y) = prodR a * prodR y := by
  rw [prodR_split, append_castAdd, append_natAdd]

/-- The non-increasing tuples of primes at least `z` with product at most `Y`. -/
theorem mem_tuples {z Y n : ℕ} {y : Fin n → ℕ} : y ∈ SieveRoughTuple.tuples z Y n ↔
    (∀ i, y i ≤ Y ∧ (y i).Prime) ∧ Antitone y ∧ (∀ i, z ≤ y i) ∧ ∏ i, y i ≤ Y := by
  unfold SieveRoughTuple.tuples
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => ?_, fun i j hij => h2 i j hij, h3, h4⟩
    have := h1 i
    rw [Finset.mem_filter, Finset.mem_range] at this
    exact ⟨Nat.lt_succ_iff.1 this.1, this.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => ?_, fun i j hij => h2 hij, h3, h4⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.2 (h1 i).1, (h1 i).2⟩

variable [Route]

/-- `(x^{a/DEN})^n = x^{na/DEN}`. -/
theorem Xe_pow_mul {q : ℕ} (hx0 : 0 < xq q) (a n : ℕ) : Xe q a ^ n = Xe q (n * a) := by
  unfold Xe
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  congr 1
  push_cast
  ring

/-! ### The frozen part with a cofactor of `t` primes -/

/-- The frozen part with a cofactor of `t` primes: the tuples of `s + 1 + t` primes up to `N₂` whose first `s + 1`
entries are a tuple of the box `βx`, whose last `t` do not increase and are at least the last of the first, and
whose product lies in `(x^{e₁/DEN}, x^{e₂/DEN}]`. -/
noncomputable def frozP (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) : Finset (Fin (s + 1 + t) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (s + 1 + t) => SieveTypeIIU.primesLe (N2 q)).filter fun u =>
    (fun i => u (Fin.castAdd t i)) ∈ famB q βx ∧ Antitone (fun j => u (Fin.natAdd (s + 1) j)) ∧
      (∀ j, u (Fin.castAdd t (Fin.last s)) ≤ u (Fin.natAdd (s + 1) j)) ∧
      Xe q e₁ < (prodR u : ℝ) ∧ (prodR u : ℝ) ≤ Xe q e₂

theorem mem_frozP {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {t : ℕ} {u : Fin (s + 1 + t) → ℕ} :
    u ∈ frozP q e₁ e₂ βx t ↔ (∀ i, u i ≤ N2 q ∧ (u i).Prime) ∧ (fun i => u (Fin.castAdd t i)) ∈ famB q βx ∧
      Antitone (fun j => u (Fin.natAdd (s + 1) j)) ∧
      (∀ j, u (Fin.castAdd t (Fin.last s)) ≤ u (Fin.natAdd (s + 1) j)) ∧
      Xe q e₁ < (prodR u : ℝ) ∧ (prodR u : ℝ) ≤ Xe q e₂ := by
  rw [frozP, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- The last prime of the box's part is the least entry of a tuple of the frozen part. -/
theorem frozP_last_le {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {t : ℕ} {u : Fin (s + 1 + t) → ℕ}
    (hu : u ∈ frozP q e₁ e₂ βx t) (i : Fin (s + 1 + t)) : u (Fin.castAdd t (Fin.last s)) ≤ u i := by
  obtain ⟨-, ha, -, hz, -⟩ := mem_frozP.1 hu
  obtain ⟨-, hsa, -⟩ := mem_famB.1 ha
  refine Fin.addCases (fun i' => ?_) (fun j => hz j) i
  exact hsa.antitone (Fin.le_last i')

/-- The pairs of a tuple of the box and a non-increasing tuple of `t` primes at least its last prime, with the
product in the slab, are the tuples of `frozP`. -/
theorem sum_frozP_eq {q e₁ e₂ s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) (hN : Xe q e₂ ≤ (N2 q : ℝ)) (G : ℕ → ℝ) :
    ∑ a ∈ famB q βx, ∑ y ∈ SieveRoughTuple.tuples (a (Fin.last s)) (N2 q) t,
        (if Xe q e₁ < ((prodR a * prodR y : ℕ) : ℝ) ∧ ((prodR a * prodR y : ℕ) : ℝ) ≤ Xe q e₂ then
          G (prodR a * prodR y) else 0) =
      ∑ u ∈ frozP q e₁ e₂ βx t, G (prodR u) := by
  have hl : ∀ a ∈ famB q βx, ∑ y ∈ SieveRoughTuple.tuples (a (Fin.last s)) (N2 q) t,
      (if Xe q e₁ < ((prodR a * prodR y : ℕ) : ℝ) ∧ ((prodR a * prodR y : ℕ) : ℝ) ≤ Xe q e₂ then
        G (prodR a * prodR y) else 0) =
      ∑ y ∈ (SieveRoughTuple.tuples (a (Fin.last s)) (N2 q) t).filter (fun y =>
        Xe q e₁ < ((prodR a * prodR y : ℕ) : ℝ) ∧ ((prodR a * prodR y : ℕ) : ℝ) ≤ Xe q e₂),
        G (prodR a * prodR y) := fun a _ => (Finset.sum_filter _ _).symm
  rw [Finset.sum_congr rfl hl, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => Fin.append x.1 x.2)
    (fun u => ⟨fun i => u (Fin.castAdd t i), fun j => u (Fin.natAdd (s + 1) j)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, y⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, mem_tuples] at hx
    obtain ⟨ha, ⟨hyp, hyanti, hyz, -⟩, hslab⟩ := hx
    obtain ⟨hap, -, -⟩ := mem_famB.1 ha
    show Fin.append a y ∈ frozP q e₁ e₂ βx t
    rw [mem_frozP, append_castAdd, append_natAdd, prodR_append]
    refine ⟨fun i => ?_, ha, hyanti, fun j => ?_, hslab⟩
    · refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact hap i'
      · rw [Fin.append_right]
        exact hyp j
    · rw [Fin.append_left, Fin.append_right]
      exact hyz j
  · intro u hu
    obtain ⟨hp, ha, hanti, hz, hslab⟩ := mem_frozP.1 hu
    have hsplit := prodR_split u
    simp only [Finset.mem_sigma, Finset.mem_filter, mem_tuples]
    refine ⟨ha, ⟨fun j => hp _, hanti, hz, ?_⟩, ?_⟩
    · have h1 : (prodR u : ℝ) ≤ N2 q := hslab.2.trans hN
      have h2 : prodR u ≤ N2 q := by exact_mod_cast h1
      have h3 : 0 < prodR (fun i => u (Fin.castAdd t i)) := Finset.prod_pos fun i _ => (hp _).2.pos
      calc ∏ j, u (Fin.natAdd (s + 1) j) = 1 * prodR (fun j => u (Fin.natAdd (s + 1) j)) := (one_mul _).symm
        _ ≤ prodR (fun i => u (Fin.castAdd t i)) * prodR (fun j => u (Fin.natAdd (s + 1) j)) :=
            Nat.mul_le_mul_right _ h3
        _ = prodR u := hsplit.symm
        _ ≤ N2 q := h2
    · rw [← hsplit]
      exact hslab
  · rintro ⟨a, y⟩ _
    exact Sigma.ext (append_castAdd a y) (heq_of_eq (append_natAdd a y))
  · intro u _
    exact append_parts u
  · rintro ⟨a, y⟩ _
    show G (prodR a * prodR y) = G (prodR (Fin.append a y))
    rw [prodR_append]

/-- **A sum over the frozen part, with the cofactor written out as its primes.** For `e₂ ≤ DEN` and
`(T + 1)·lo_s ≥ DEN + 1`, `lo_s` the lower end of the last cell of `βx`, at a modulus as in `Big`: the sum over the
frozen part of a function of `∏a·m` is the sum over `t ≤ T` of the sums over `frozP q e₁ e₂ βx t` of the function
of the product. -/
theorem sum_frozS_eq [RouteOK] {q : ℕ} (hq : Big q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (he₂ : e₂ ≤ DEN)
    {T : ℕ} (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) (G : ℕ → ℝ) :
    ∑ am ∈ frozS q e₁ e₂ βx, G (frozR am) =
      ∑ t ∈ Finset.range (T + 1), ∑ u ∈ frozP q e₁ e₂ βx t, G (prodR u) := by
  obtain ⟨-, hx3, -, hN2', -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hN2 : (N2 q : ℝ) < Xe q (DEN + 1) := by
    unfold Xe
    push_cast
    exact hN2'
  have hfl : 2 * xq q - 1 < (N2 q : ℝ) := Nat.sub_one_lt_floor _
  have hxN : Xe q e₂ ≤ (N2 q : ℝ) := by
    have h1 : Xe q e₂ ≤ xq q := (Xe_mono hx1 he₂).trans (Xe_DEN q).le
    linarith
  have hY : 1 ≤ N2 q := by
    have : (1 : ℝ) ≤ N2 q := by linarith
    exact_mod_cast this
  have h1 : ∑ am ∈ frozS q e₁ e₂ βx, G (frozR am) = ∑ a ∈ famB q βx,
      ∑ m ∈ ((Finset.Icc 1 (N2 q)).filter (fun k => ∀ p < a (Fin.last s), p.Prime → ¬ p ∣ k)).filter
        (fun m => Xe q e₁ < ((prodR a * m : ℕ) : ℝ) ∧ ((prodR a * m : ℕ) : ℝ) ≤ Xe q e₂),
        G (prodR a * m) := by
    refine Finset.sum_finset_product (frozS q e₁ e₂ βx) (famB q βx) _ (fun p => ?_)
    rw [mem_frozS]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨ha, h1, h2⟩, hr, hs⟩
      exact ⟨ha, ⟨⟨h1, h2⟩, hr⟩, hs⟩
    · rintro ⟨ha, ⟨⟨h1, h2⟩, hr⟩, hs⟩
      exact ⟨⟨ha, h1, h2⟩, hr, hs⟩
  rw [h1]
  have h2 : ∀ a ∈ famB q βx,
      ∑ m ∈ ((Finset.Icc 1 (N2 q)).filter (fun k => ∀ p < a (Fin.last s), p.Prime → ¬ p ∣ k)).filter
        (fun m => Xe q e₁ < ((prodR a * m : ℕ) : ℝ) ∧ ((prodR a * m : ℕ) : ℝ) ≤ Xe q e₂),
        G (prodR a * m) =
      ∑ t ∈ Finset.range (T + 1), ∑ y ∈ SieveRoughTuple.tuples (a (Fin.last s)) (N2 q) t,
        (if Xe q e₁ < ((prodR a * prodR y : ℕ) : ℝ) ∧ ((prodR a * prodR y : ℕ) : ℝ) ≤ Xe q e₂ then
          G (prodR a * prodR y) else 0) := by
    intro a ha
    obtain ⟨hp, -, hc⟩ := mem_famB.1 ha
    have hz : 2 ≤ a (Fin.last s) := (hp _).2.two_le
    have hK : N2 q < a (Fin.last s) ^ (T + 1) := by
      have h1 : Xe q (βx (Fin.last s)).1 ≤ a (Fin.last s) := (hc _).1
      have h2 : Xe q (DEN + 1) ≤ Xe q ((T + 1) * (βx (Fin.last s)).1) := Xe_mono hx1 hT
      have h3 : Xe q ((T + 1) * (βx (Fin.last s)).1) ≤ (a (Fin.last s) : ℝ) ^ (T + 1) := by
        rw [← Xe_pow_mul hx0]
        exact pow_le_pow_left₀ (Xe_pos hx0 _).le h1 _
      have h4 : (N2 q : ℝ) < ((a (Fin.last s) ^ (T + 1) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h4
    rw [Finset.sum_filter]
    exact SieveChain.sum_rough_tuples hz hY
      (fun m => if Xe q e₁ < ((prodR a * m : ℕ) : ℝ) ∧ ((prodR a * m : ℕ) : ℝ) ≤ Xe q e₂ then
        G (prodR a * m) else 0) T hK
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => sum_frozP_eq βx t hxN G

/-- The term of a chain's box over the frozen part, by the number of primes of the cofactor. -/
theorem dIF_frozS_eq [RouteOK] {q : ℕ} (hq : Big q) (a : ZMod q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (he₂ : e₂ ≤ DEN) {T : ℕ} (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) :
    dIF q a (frozS q e₁ e₂ βx) frozR bx =
      ∑ t ∈ Finset.range (T + 1), dIF q a (frozP q e₁ e₂ βx t) prodR bx :=
  sum_frozS_eq hq he₂ hT fun R =>
    famIR (gA q a) (N1 q) (N2 q) R (famB q bx) - famIR (gB q) (N1 q) (N2 q) R (famB q bx)

/-- The terms at a floor of a chain's box over the frozen part, by the number of primes of the cofactor. -/
theorem dJF_frozS_eq [RouteOK] {q : ℕ} (hq : Big q) (a : ZMod q) (f : ℕ) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (he₂ : e₂ ≤ DEN) {T : ℕ} (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k : ℕ} (bx : Fin k → Cell) :
    dJF q a f (frozS q e₁ e₂ βx) frozR bx =
      ∑ t ∈ Finset.range (T + 1), dJF q a f (frozP q e₁ e₂ βx t) prodR bx :=
  sum_frozS_eq hq he₂ hT fun R =>
    famJR (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ R (famB q bx) -
      famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ R (famB q bx)

/-- **The term of a chain's box over the frozen part is evaluated when it is over each `frozP … t`, `t ≤ T`.** -/
theorem evIF_frozS [RouteOK] {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k' : ℕ} {bx : Fin (k' + 1) → Cell}
    (h : ∀ t ≤ T, EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  intro η hη
  have hT0 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hall : ∀ᶠ q : ℕ in atTop, ∀ t ∈ Finset.range (T + 1), ∀ a : ZMod q, IsUnit a →
      |dIF q a (frozP q e₁ e₂ βx t) prodR bx| ≤ (q.totient : ℝ)⁻¹ * (η / (T + 1) * Xq q) := by
    rw [Filter.eventually_all_finset]
    intro t ht
    exact h t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) (η / (T + 1)) (by positivity)
  filter_upwards [hall, big_ev] with q hq hbig a ha
  show |dIF q a (frozS q e₁ e₂ βx) frozR bx| ≤ _
  rw [dIF_frozS_eq hbig a he₂ hT bx]
  calc |∑ t ∈ Finset.range (T + 1), dIF q a (frozP q e₁ e₂ βx t) prodR bx|
      ≤ ∑ t ∈ Finset.range (T + 1), |dIF q a (frozP q e₁ e₂ βx t) prodR bx| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range (T + 1), (q.totient : ℝ)⁻¹ * (η / (T + 1) * Xq q) :=
        Finset.sum_le_sum fun t ht => hq t ht a ha
    _ = (q.totient : ℝ)⁻¹ * (η * Xq q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-- **The terms at a floor of a chain's box over the frozen part are evaluated when they are over each
`frozP … t`, `t ≤ T`.** -/
theorem evJF_frozS [RouteOK] {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {f k : ℕ} {bx : Fin k → Cell}
    (h : ∀ t ≤ T, EvJF (fun q => frozP q e₁ e₂ βx t) prodR f bx) :
    EvJF (fun q => frozS q e₁ e₂ βx) frozR f bx := by
  intro η hη
  have hT0 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hall : ∀ᶠ q : ℕ in atTop, ∀ t ∈ Finset.range (T + 1), ∀ a : ZMod q, IsUnit a →
      |dJF q a f (frozP q e₁ e₂ βx t) prodR bx| ≤ (q.totient : ℝ)⁻¹ * (η / (T + 1) * Xq q) := by
    rw [Filter.eventually_all_finset]
    intro t ht
    exact h t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) (η / (T + 1)) (by positivity)
  filter_upwards [hall, big_ev] with q hq hbig a ha
  show |dJF q a f (frozS q e₁ e₂ βx) frozR bx| ≤ _
  rw [dJF_frozS_eq hbig a f he₂ hT bx]
  calc |∑ t ∈ Finset.range (T + 1), dJF q a f (frozP q e₁ e₂ βx t) prodR bx|
      ≤ ∑ t ∈ Finset.range (T + 1), |dJF q a f (frozP q e₁ e₂ βx t) prodR bx| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range (T + 1), (q.totient : ℝ)⁻¹ * (η / (T + 1) * Xq q) :=
        Finset.sum_le_sum fun t ht => hq t ht a ha
    _ = (q.totient : ℝ)⁻¹ * (η * Xq q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

omit [Route] in
/-- **The term over the frozen part by the primes of the cofactor, for any route**: `evIF_frozS` with the route
as a variable. -/
theorem evIF_frozS_at (Rt : Route) (hRt : @RouteOK Rt) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (he₂ : e₂ ≤ DEN)
    {T : ℕ} (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k' : ℕ} {bx : Fin (k' + 1) → Cell}
    (h : ∀ t ≤ T, @EvIF Rt _ (fun q => @frozP Rt q e₁ e₂ s βx t) prodR k' bx) :
    @EvIF Rt _ (fun q => @frozS Rt q e₁ e₂ s βx) frozR k' bx :=
  @evIF_frozS Rt hRt e₁ e₂ s βx he₂ T hT k' bx h

omit [Route] in
/-- **The terms at a floor over the frozen part by the primes of the cofactor, for any route**: `evJF_frozS` with
the route as a variable. -/
theorem evJF_frozS_at (Rt : Route) (hRt : @RouteOK Rt) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (he₂ : e₂ ≤ DEN)
    {T : ℕ} (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {f k : ℕ} {bx : Fin k → Cell}
    (h : ∀ t ≤ T, @EvJF Rt _ (fun q => @frozP Rt q e₁ e₂ s βx t) prodR f k bx) :
    @EvJF Rt _ (fun q => @frozS Rt q e₁ e₂ s βx) frozR f k bx :=
  @evJF_frozS Rt hRt e₁ e₂ s βx he₂ T hT f k bx h

end SieveAd

#print axioms SieveAd.evIF_frozS_at
#print axioms SieveAd.evJF_frozS_at
