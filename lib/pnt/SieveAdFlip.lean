/-
# Role reversal through the largest prime, as an identity: the two inclusions

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A box of primes `p₁ > a₁ > ⋯ > a_{s+1}`, the cell of `p₁` being `ctx = (l₁, h₁)` and the others'
`βx`, has the term `Σ S(·_{p₁a₁⋯a_{s+1}}, a_{s+1})`: its numbers are `n = p₁·a₁⋯a_{s+1}·m` with `m` free of primes
below `a_{s+1}`. Role reversal sums over `R = a₁⋯a_{s+1}·m` instead and sieves `n/R` for the prime `p₁`. Here `m`
is kept as one number, whatever its prime factors, and `n/R` is sifted at a level `Z = ⌈x^{t/DEN}⌉` with
`l₁ ≥ t ≥ h₁/2`, at which a number of the size of `p₁` with no prime factor below `Z` is prime: so the term of the
box lies between the terms at the level `Z` of two frozen parts (`SieveAdFroz.lean`), which differ in the `R`
within `x^{1/DEN}` of the two ends of the range of `x/p₁`.

* `frozS q e₁ e₂ βx`, `frozR`: the frozen part: the pairs of a tuple `a` of the box `βx` and a number `m ≤ N₂`
  free of primes below `a`'s last, with `R = ∏a·m` in `(x^{e₁/DEN}, x^{e₂/DEN}]`. `inSlab_frozS`,
  `inSlab_frozS_inner`: it lies in the range of `r'` for `ctx`, with `(e₁, e₂) = (DEN − h₁, DEN − l₁ + 1)` and with
  `(DEN − h₁ + 1, DEN − l₁)`.
* `famJR_zero`: the terms at a level of the chain with no prime, on the multiples of `R`: the `n` with `R ∣ n` and
  `n/R` free of primes below the level.
* `flip_cover_pt`, `flip_cover`: **every tuple is reached.** For `t ≤ l₁`: the tuples of the box that count `n`
  inject into the pairs of the wider frozen part with `R ∣ n` and `n/R` free of primes below `Z`, by
  `(p₁, a) ↦ (a, n/(p₁∏a))`; so, with weights `g ≥ 0`, the term of the box is at most the terms at the level `Z`
  over the wider frozen part.
* `flip_inject_pt`, `flip_inject`: **and no more.** For `t ≤ l₁`, `h₁ ≤ 2t` and the first cell of `βx` below
  `x^{l₁/DEN}`: the pairs of the narrower frozen part with `R ∣ n` and `n/R` free of primes below `Z` inject into
  the tuples of the box that count `n`, by `(a, m) ↦ (n/R, a)`, since `n/R` is then a prime of the cell `ctx`; so
  the terms at the level `Z` over the narrower frozen part are at most the term of the box.

The file imports `SieveAdFrozTree.lean` and `SieveAdRevLemma.lean`.
-/
import SieveAdFrozTree
import SieveAdRevLemma

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### Tuples with one more prime in front -/

/-- A strictly decreasing tuple with a larger number in front is strictly decreasing. -/
theorem strictAnti_cons {n p : ℕ} {a : Fin (n + 1) → ℕ} (ha : StrictAnti a) (hp : a 0 < p) :
    StrictAnti (Fin.cons (α := fun _ => ℕ) p a) := by
  intro i j hij
  induction j using Fin.cases with
  | zero => exact absurd hij (Fin.not_lt_zero _)
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact lt_of_le_of_lt (ha.antitone (Fin.zero_le j)) hp
    | succ i =>
      simp only [Fin.cons_succ]
      exact ha (Fin.succ_lt_succ_iff.1 hij)

/-- A product of numbers with no prime factor below `z` has none. -/
theorem rough_prod {z k : ℕ} {a : Fin k → ℕ} (h : ∀ i, SieveTree.rough z (a i)) : SieveTree.rough z (∏ i, a i) := by
  refine Finset.prod_induction a (fun x => SieveTree.rough z x) (fun x y hx hy => SieveP6Leaves.rough_mul hx hy)
    (fun _ _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)) fun i _ => h i

/-- A prime at least `z` has no prime factor below `z`. -/
theorem rough_prime {z p : ℕ} (hp : p.Prime) (hz : z ≤ p) : SieveTree.rough z p := by
  intro p' hp' hpr hd
  have := (Nat.prime_dvd_prime_iff_eq hpr hp).1 hd
  omega

/-- A divisor of a number with no prime factor below `z` has none. -/
theorem rough_of_dvd {z d n : ℕ} (h : SieveTree.rough z n) (hd : d ∣ n) : SieveTree.rough z d :=
  fun p hp hpr hpd => h p hp hpr (hpd.trans hd)

/-- A number at least `2` and below `z²` with no prime factor below `z` is prime. -/
theorem prime_of_rough {z P : ℕ} (hP : 2 ≤ P) (hr : SieveTree.rough z P) (hz : P < z * z) : P.Prime := by
  by_contra hnp
  have h1 : P.minFac ^ 2 ≤ P := Nat.minFac_sq_le_self (by omega) hnp
  have h2 : P.minFac.Prime := Nat.minFac_prime (by omega)
  have h3 : z ≤ P.minFac := by
    by_contra hlt
    exact hr _ (not_le.1 hlt) h2 (Nat.minFac_dvd P)
  have h4 : z * z ≤ P.minFac ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul h3 h3
  omega

variable [Route]

/-! ### The frozen part of a box reversed through its largest prime -/

/-- The number `R = ∏a·m` of a pair. -/
def frozR {s : ℕ} (am : (Fin (s + 1) → ℕ) × ℕ) : ℕ := (∏ i, am.1 i) * am.2

/-- **The frozen part**: the pairs of a tuple `a` of the box `βx` and a number `m ≤ N₂` free of primes below the
last prime of `a`, with `∏a·m` in `(x^{e₁/DEN}, x^{e₂/DEN}]`. -/
noncomputable def frozS (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) : Finset ((Fin (s + 1) → ℕ) × ℕ) :=
  ((famB q βx) ×ˢ (Finset.Icc 1 (N2 q))).filter fun am =>
    SieveTree.rough (am.1 (Fin.last s)) am.2 ∧ xq q ^ ((e₁ : ℝ) / DEN) < (frozR am : ℝ) ∧
      (frozR am : ℝ) ≤ xq q ^ ((e₂ : ℝ) / DEN)

theorem mem_frozS {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {am : (Fin (s + 1) → ℕ) × ℕ} :
    am ∈ frozS q e₁ e₂ βx ↔ (am.1 ∈ famB q βx ∧ 1 ≤ am.2 ∧ am.2 ≤ N2 q) ∧
      SieveTree.rough (am.1 (Fin.last s)) am.2 ∧ xq q ^ ((e₁ : ℝ) / DEN) < (frozR am : ℝ) ∧
        (frozR am : ℝ) ≤ xq q ^ ((e₂ : ℝ) / DEN) := by
  rw [frozS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]

/-- The number of a pair of the frozen part is positive. -/
theorem frozR_pos {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {am : (Fin (s + 1) → ℕ) × ℕ}
    (h : am ∈ frozS q e₁ e₂ βx) : 0 < frozR am := by
  obtain ⟨⟨ha, hm1, -⟩, -⟩ := mem_frozS.1 h
  exact Nat.mul_pos (Finset.prod_pos fun i _ => ((mem_famB.1 ha).1 i).2.pos) hm1

/-- The frozen part lies in the range of `r'` for the cell `ctx`. -/
theorem inSlab_frozS (ctx : Cell) {s : ℕ} (βx : Fin (s + 1) → Cell) :
    InSlab (fun q => frozS q (e1 ctx) (e2 ctx) βx) frozR ctx :=
  Filter.Eventually.of_forall fun _ _ ham => (mem_frozS.1 ham).2.2

/-- The narrower frozen part lies in the range of `r'` for the cell `ctx`. -/
theorem inSlab_frozS_inner [RouteOK] (ctx : Cell) {s : ℕ} (βx : Fin (s + 1) → Cell) :
    InSlab (fun q => frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ctx := by
  filter_upwards [big_ev] with q hq am ham
  obtain ⟨-, hx3, -⟩ := big_facts hq
  have hx1 : 1 ≤ xq q := by linarith
  obtain ⟨-, -, hlo, hhi⟩ := mem_frozS.1 ham
  exact ⟨lt_of_le_of_lt (pow_mono hx1 (Nat.le_succ _)) hlo, hhi.trans (pow_mono hx1 (Nat.sub_le _ _))⟩

/-- **The terms at a level of the chain with no prime, on the multiples of `R`**: the `n` with `R ∣ n` and `n/R`
free of primes below the level. -/
theorem famJR_zero (g : ℕ → ℝ) (N₁ N₂ z : ℕ) {R : ℕ} (hR : 0 < R) (q : ℕ) :
    famJR g N₁ N₂ z R (famB q (boxFn [] 0 rfl)) =
      ∑ n ∈ Ioc N₁ N₂, g n * (if R ∣ n ∧ SieveTree.rough z (n / R) then 1 else 0) := by
  rw [famJR_eq g N₁ N₂ z hR, famB_zero, Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]

/-! ### Every tuple is reached -/

/-- **Every tuple is reached.** At a large modulus, for `l₁ ≤ h₁ ≤ DEN` and `t ≤ l₁`: the tuples `(p₁, a)` of the
box that count `n ∈ (N₁, N₂]` inject into the pairs `(a, m)` of the frozen part of `ctx` with `R ∣ n` and `n/R`
free of primes below `⌈x^{t/DEN}⌉`. -/
theorem flip_cover_pt [RouteOK] {q : ℕ} (hq : Big q) {ctx : Cell} (hctx : ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) {t : ℕ}
    (ht : t ≤ ctx.1) {s : ℕ} (βx : Fin (s + 1) → Cell) {n : ℕ} (hn : n ∈ Ioc (N1 q) (N2 q)) :
    ((famB q (Fin.cons (α := fun _ => Cell) ctx βx)).filter fun rt =>
        (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last (s + 1))) n).card ≤
      ((frozS q (e1 ctx) (e2 ctx) βx).filter fun am =>
        frozR am ∣ n ∧ SieveTree.rough ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (n / frozR am)).card := by
  obtain ⟨-, hx3, -, -, h3⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hD := DEN_pos'
  rw [Finset.mem_Ioc] at hn
  have hnx : xq q < n := Nat.lt_of_floor_lt hn.1
  have hn2 : (n : ℝ) ≤ 2 * xq q := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by positivity))
  have hn0 : 0 < n := by omega
  have hX1 : (3 : ℝ) ≤ Xe q 1 := by unfold Xe; rw [Nat.cast_one]; exact h3
  have hxlo : Xe q ctx.2 * Xe q (e1 ctx) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    unfold e1
    omega
  have hxhi : Xe q ctx.1 * Xe q (DEN - ctx.1) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    omega
  have he2 : Xe q (e2 ctx) = Xe q (DEN - ctx.1) * Xe q 1 := by
    rw [← Xe_add hx0]
    rfl
  -- the facts of one tuple
  have key : ∀ rt ∈ (famB q (Fin.cons (α := fun _ => Cell) ctx βx)).filter fun rt =>
      (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last (s + 1))) n,
      ∃ m : ℕ, n = rt 0 * ((∏ i, Fin.tail rt i) * m) ∧ 0 < rt 0 ∧ 0 < (∏ i, Fin.tail rt i) * m ∧
        ((Fin.tail rt, m) ∈ (frozS q (e1 ctx) (e2 ctx) βx).filter fun am =>
          frozR am ∣ n ∧ SieveTree.rough ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (n / frozR am)) := by
    intro rt hrt
    rw [Finset.mem_filter] at hrt
    obtain ⟨hfam, ⟨m, hm⟩, hr⟩ := hrt
    obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hfam
    have hprod : ∏ i, rt i = rt 0 * ∏ i, Fin.tail rt i := Fin.prod_univ_succ _
    have hP := hp 0
    have hP0 : 0 < rt 0 := hP.2.pos
    have hA0 : 0 < ∏ i, Fin.tail rt i := Finset.prod_pos fun i _ => (hp i.succ).2.pos
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, Nat.mul_zero] at hm; omega
      · exact h
    have hnm : n = rt 0 * ((∏ i, Fin.tail rt i) * m) := by rw [hm, hprod, Nat.mul_assoc]
    have hc0 := hc 0
    simp only [Fin.cons_zero] at hc0
    have hta : Fin.tail rt ∈ famB q βx := by
      refine mem_famB.2 ⟨fun i => hp i.succ, fun i j hij => hsa (Fin.succ_lt_succ_iff.2 hij), fun i => ?_⟩
      have := hc i.succ
      simp only [Fin.cons_succ] at this
      exact this
    have hlast : Fin.tail rt (Fin.last s) = rt (Fin.last (s + 1)) := by
      simp only [Fin.tail, Fin.succ_last]
    have hR0 : 0 < (∏ i, Fin.tail rt i) * m := Nat.mul_pos hA0 hm0
    have hPr : (0 : ℝ) < rt 0 := by exact_mod_cast hP0
    have hRr : (0 : ℝ) < (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ) := by exact_mod_cast hR0
    have hnr : (n : ℝ) = (rt 0 : ℝ) * (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ) := by rw [hnm]; push_cast; ring
    refine ⟨m, hnm, hP0, hR0, ?_⟩
    rw [Finset.mem_filter, mem_frozS]
    have hdiv : frozR (Fin.tail rt, m) ∣ n := ⟨rt 0, by rw [hnm]; unfold frozR; ring⟩
    have hquot : n / frozR (Fin.tail rt, m) = rt 0 := by
      unfold frozR
      rw [hnm]
      exact Nat.mul_div_cancel _ hR0
    refine ⟨⟨⟨hta, hm0, ?_⟩, ?_, ?_, ?_⟩, hdiv, ?_⟩
    · have : m ≤ n := Nat.le_of_dvd hn0 ⟨rt 0 * ∏ i, Fin.tail rt i, by rw [hnm]; ring⟩
      omega
    · show SieveTree.rough (Fin.tail rt (Fin.last s)) m
      rw [hlast]
      exact rough_of_dvd hr ⟨rt 0 * ∏ i, Fin.tail rt i, by rw [hnm]; ring⟩
    · -- `R > x^{(DEN − h₁)/DEN}`, since `p₁ < x^{h₁/DEN}` and `n > x`
      show Xe q (e1 ctx) < (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ)
      by_contra hle
      rw [not_lt] at hle
      have h1 : (n : ℝ) < Xe q ctx.2 * Xe q (e1 ctx) := by
        rw [hnr]
        calc (rt 0 : ℝ) * (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ) ≤ (rt 0 : ℝ) * Xe q (e1 ctx) :=
              mul_le_mul_of_nonneg_left hle hPr.le
          _ < Xe q ctx.2 * Xe q (e1 ctx) := mul_lt_mul_of_pos_right hc0.2 (Xe_pos hx0 _)
      rw [hxlo] at h1
      linarith
    · -- `R ≤ x^{(DEN − l₁ + 1)/DEN}`, since `p₁ ≥ x^{l₁/DEN}` and `n ≤ 2x`
      show (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ) ≤ Xe q (e2 ctx)
      have h1 : (rt 0 : ℝ) * (((∏ i, Fin.tail rt i) * m : ℕ) : ℝ) ≤ (rt 0 : ℝ) * (2 * Xe q (DEN - ctx.1)) := by
        rw [← hnr]
        calc (n : ℝ) ≤ 2 * xq q := hn2
          _ = Xe q ctx.1 * (2 * Xe q (DEN - ctx.1)) := by rw [← hxhi]; ring
          _ ≤ (rt 0 : ℝ) * (2 * Xe q (DEN - ctx.1)) :=
              mul_le_mul_of_nonneg_right hc0.1 (by have := Xe_pos hx0 (DEN - ctx.1); linarith)
      have h2 := le_of_mul_le_mul_left h1 hPr
      rw [he2]
      have := Xe_pos hx0 (DEN - ctx.1)
      nlinarith
    · rw [hquot]
      refine rough_prime hP.2 (Nat.ceil_le.2 ((pow_mono hx1 ht).trans hc0.1))
  refine Finset.card_le_card_of_injOn (fun rt => (Fin.tail rt, n / ∏ i, rt i)) ?_ ?_
  · intro rt hrt
    rw [Finset.mem_coe] at hrt ⊢
    obtain ⟨m, hnm, hP0, -, hmem⟩ := key rt hrt
    have hprod : ∏ i, rt i = rt 0 * ∏ i, Fin.tail rt i := Fin.prod_univ_succ _
    have hq' : n / ∏ i, rt i = m := by
      rw [hprod, hnm, ← Nat.mul_assoc]
      exact Nat.mul_div_cancel_left m (Nat.mul_pos hP0 (Nat.pos_of_ne_zero fun h0 => by
        rw [h0, Nat.zero_mul, Nat.mul_zero] at hnm; omega))
    show (Fin.tail rt, n / ∏ i, rt i) ∈ _
    rw [hq']
    exact hmem
  · intro rt hrt rt' hrt' heq
    rw [Finset.mem_coe] at hrt hrt'
    obtain ⟨m, hnm, hP0, hR0, -⟩ := key rt hrt
    obtain ⟨m', hnm', hP0', hR0', -⟩ := key rt' hrt'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨htl, hdv⟩ := heq
    have hprod : ∏ i, rt i = rt 0 * ∏ i, Fin.tail rt i := Fin.prod_univ_succ _
    have hprod' : ∏ i, rt' i = rt' 0 * ∏ i, Fin.tail rt' i := Fin.prod_univ_succ _
    have hA0 : 0 < ∏ i, Fin.tail rt i := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hR0; omega
    have hA0' : 0 < ∏ i, Fin.tail rt' i := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hR0'; omega
    have hq1 : n / ∏ i, rt i = m := by
      rw [hprod, hnm, ← Nat.mul_assoc]
      exact Nat.mul_div_cancel_left m (Nat.mul_pos hP0 hA0)
    have hq2 : n / ∏ i, rt' i = m' := by
      rw [hprod', hnm', ← Nat.mul_assoc]
      exact Nat.mul_div_cancel_left m' (Nat.mul_pos hP0' hA0')
    have hmm : m = m' := by rw [← hq1, ← hq2]; exact hdv
    have h0 : rt 0 = rt' 0 := by
      have e : rt 0 * ((∏ i, Fin.tail rt i) * m) = rt' 0 * ((∏ i, Fin.tail rt i) * m) := by
        rw [← hnm]
        rw [htl, hmm]
        exact hnm'
      exact Nat.eq_of_mul_eq_mul_right hR0 e
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrFun htl i

/-- **The term of the box is at most the terms at the level over the frozen part**, for weights `g ≥ 0`. -/
theorem flip_cover [RouteOK] {q : ℕ} (hq : Big q) {ctx : Cell} (hctx : ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) {t : ℕ}
    (ht : t ≤ ctx.1) {s : ℕ} (βx : Fin (s + 1) → Cell) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    famI g (N1 q) (N2 q) (famB q (Fin.cons (α := fun _ => Cell) ctx βx)) ≤
      ∑ am ∈ frozS q (e1 ctx) (e2 ctx) βx,
        famJR g (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl)) := by
  rw [famI_eq_sum_card]
  have e : ∑ am ∈ frozS q (e1 ctx) (e2 ctx) βx,
      famJR g (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl)) =
        ∑ n ∈ Ioc (N1 q) (N2 q), g n * (((frozS q (e1 ctx) (e2 ctx) βx).filter fun am =>
          frozR am ∣ n ∧ SieveTree.rough ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (n / frozR am)).card : ℝ) := by
    rw [Finset.sum_congr rfl fun am ham => famJR_zero g _ _ _ (frozR_pos ham) q, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [e]
  refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (hg n)
  exact_mod_cast flip_cover_pt hq hctx ht βx hn

/-! ### And no more -/

/-- **And no more.** At a large modulus, for `0 < l₁ ≤ h₁ ≤ DEN`, `t ≤ l₁`, `h₁ ≤ 2t` and the first cell of `βx`
below `x^{l₁/DEN}`: the pairs `(a, m)` of the narrower frozen part with `R ∣ n` and `n/R` free of primes below
`⌈x^{t/DEN}⌉` inject into the tuples of the box that count `n ∈ (N₁, N₂]`: `n/R` is a prime of the cell `ctx`. -/
theorem flip_inject_pt [RouteOK] {q : ℕ} (hq : Big q) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN)
    {t : ℕ} (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) {s : ℕ} (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1)
    {n : ℕ} (hn : n ∈ Ioc (N1 q) (N2 q)) :
    ((frozS q (e1 ctx + 1) (e2 ctx - 1) βx).filter fun am =>
        frozR am ∣ n ∧ SieveTree.rough ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (n / frozR am)).card ≤
      ((famB q (Fin.cons (α := fun _ => Cell) ctx βx)).filter fun rt =>
        (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last (s + 1))) n).card := by
  obtain ⟨-, hx3, -, -, h3⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hD := DEN_pos'
  rw [Finset.mem_Ioc] at hn
  have hnx : xq q < n := Nat.lt_of_floor_lt hn.1
  have hn2 : (n : ℝ) ≤ 2 * xq q := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by positivity))
  have hn0 : 0 < n := by omega
  have hX1 : (3 : ℝ) ≤ Xe q 1 := by unfold Xe; rw [Nat.cast_one]; exact h3
  have hxhi : Xe q ctx.1 * Xe q (e2 ctx - 1) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    unfold e2
    omega
  have hxlo : Xe q (ctx.2 - 1) * Xe q (e1 ctx + 1) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    unfold e1
    omega
  have hh1 : Xe q ctx.2 = Xe q (ctx.2 - 1) * Xe q 1 := by
    rw [← Xe_add hx0]
    congr 1
    omega
  set Z := ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ with hZ
  have hZt : Xe q t ≤ Z := Nat.le_ceil _
  have hZ2 : Xe q ctx.2 ≤ (Z : ℝ) * Z := by
    have h1 : Xe q ctx.2 ≤ Xe q (t + t) := Xe_mono hx1 (by omega)
    rw [Xe_add hx0] at h1
    exact h1.trans (mul_le_mul hZt hZt (Xe_pos hx0 t).le (Nat.cast_nonneg _))
  -- the facts of one pair
  have key : ∀ am ∈ (frozS q (e1 ctx + 1) (e2 ctx - 1) βx).filter fun am =>
      frozR am ∣ n ∧ SieveTree.rough Z (n / frozR am),
      n = frozR am * (n / frozR am) ∧ 0 < frozR am ∧ 0 < ∏ i, am.1 i ∧
        ((Fin.cons (α := fun _ => ℕ) (n / frozR am) am.1) ∈
          (famB q (Fin.cons (α := fun _ => Cell) ctx βx)).filter fun rt =>
            (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last (s + 1))) n) := by
    intro am ham
    rw [Finset.mem_filter] at ham
    obtain ⟨hfz, hdiv, hr⟩ := ham
    have hR0 := frozR_pos hfz
    obtain ⟨⟨ha, hm1, hm2⟩, hrm, hlo, hhi⟩ := mem_frozS.1 hfz
    obtain ⟨hp, hsa, hc⟩ := mem_famB.1 ha
    have hA0 : 0 < ∏ i, am.1 i := Finset.prod_pos fun i _ => (hp i).2.pos
    obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = n / frozR am := ⟨_, rfl⟩
    have hnP : n = frozR am * P := by rw [hPdef]; exact (Nat.mul_div_cancel' hdiv).symm
    rw [← hPdef] at hr ⊢
    have hP0 : 0 < P := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hnP; omega
    have hRr : (0 : ℝ) < frozR am := by exact_mod_cast hR0
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
    have hnr : (n : ℝ) = (frozR am : ℝ) * P := by rw [hnP]; push_cast; ring
    -- `P > x^{l₁/DEN}`
    have hPlo : Xe q ctx.1 < P := by
      have h1 : (frozR am : ℝ) * Xe q ctx.1 < (frozR am : ℝ) * P := by
        rw [← hnr]
        calc (frozR am : ℝ) * Xe q ctx.1 ≤ Xe q (e2 ctx - 1) * Xe q ctx.1 :=
              mul_le_mul_of_nonneg_right hhi (Xe_pos hx0 _).le
          _ = xq q := by rw [mul_comm, hxhi]
          _ < n := hnx
      exact lt_of_mul_lt_mul_left h1 hRr.le
    -- `P < x^{h₁/DEN}`
    have hPhi : (P : ℝ) < Xe q ctx.2 := by
      have h1 : (frozR am : ℝ) * P ≤ (frozR am : ℝ) * (2 * Xe q (ctx.2 - 1)) := by
        rw [← hnr]
        calc (n : ℝ) ≤ 2 * xq q := hn2
          _ = Xe q (e1 ctx + 1) * (2 * Xe q (ctx.2 - 1)) := by rw [← hxlo]; ring
          _ ≤ (frozR am : ℝ) * (2 * Xe q (ctx.2 - 1)) :=
              mul_le_mul_of_nonneg_right hlo.le (by have := Xe_pos hx0 (ctx.2 - 1); linarith)
      have h2 := le_of_mul_le_mul_left h1 hRr
      rw [hh1]
      have := Xe_pos hx0 (ctx.2 - 1)
      nlinarith
    have hP2 : 2 ≤ P := by
      have h1 : (1 : ℝ) < P := lt_of_le_of_lt (Real.one_le_rpow hx1 (by positivity)) hPlo
      exact_mod_cast h1
    have hPZ : P < Z * Z := by
      have h1 : (P : ℝ) < (Z : ℝ) * Z := lt_of_lt_of_le hPhi hZ2
      exact_mod_cast h1
    have hPp : P.Prime := prime_of_rough hP2 hr hPZ
    have hPn : P ≤ n := Nat.le_of_dvd hn0 ⟨frozR am, by rw [hnP]; ring⟩
    have ha0 : am.1 0 < P := by
      have h1 : ((am.1 0 : ℕ) : ℝ) < P :=
        lt_of_lt_of_le (hc 0).2 ((pow_mono hx1 hβ).trans hPlo.le)
      exact_mod_cast h1
    refine ⟨hnP, hR0, hA0, ?_⟩
    rw [Finset.mem_filter, mem_famB]
    refine ⟨⟨fun i => ?_, strictAnti_cons hsa ha0, fun i => ?_⟩, ?_, ?_⟩
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact ⟨by omega, hPp⟩
      | succ i =>
        simp only [Fin.cons_succ]
        exact hp i
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact ⟨hPlo.le, hPhi⟩
      | succ i =>
        simp only [Fin.cons_succ]
        exact hc i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact ⟨am.2, by rw [hnP]; unfold frozR; ring⟩
    · have hlast : (Fin.cons (α := fun _ => ℕ) P am.1 : Fin (s + 2) → ℕ) (Fin.last (s + 1)) = am.1 (Fin.last s) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      rw [hlast, hnP]
      have hz : am.1 (Fin.last s) ≤ P := (hsa.antitone (Fin.zero_le _)).trans ha0.le
      exact SieveP6Leaves.rough_mul (SieveP6Leaves.rough_mul
        (rough_prod fun i => rough_prime (hp i).2 (hsa.antitone (Fin.le_last i))) hrm) (rough_prime hPp hz)
  refine Finset.card_le_card_of_injOn (fun am => Fin.cons (α := fun _ => ℕ) (n / frozR am) am.1) ?_ ?_
  · intro am ham
    rw [Finset.mem_coe] at ham ⊢
    exact (key am ham).2.2.2
  · intro am ham am' ham' heq
    rw [Finset.mem_coe] at ham ham'
    obtain ⟨hnP, hR0, hA0, -⟩ := key am ham
    obtain ⟨hnP', hR0', -, -⟩ := key am' ham'
    have h0 : n / frozR am = n / frozR am' := by
      have := congrFun heq 0
      simpa only [Fin.cons_zero] using this
    have htl : am.1 = am'.1 := by
      funext i
      have := congrFun heq i.succ
      simpa only [Fin.cons_succ] using this
    have hP0 : 0 < n / frozR am := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hnP; omega
    have hRR : frozR am = frozR am' := by
      have e : frozR am * (n / frozR am) = frozR am' * (n / frozR am) := by
        rw [← hnP]
        rw [h0]
        exact hnP'
      exact Nat.eq_of_mul_eq_mul_right hP0 e
    have hm : am.2 = am'.2 := by
      unfold frozR at hRR
      rw [← htl] at hRR
      exact Nat.eq_of_mul_eq_mul_left hA0 hRR
    exact Prod.ext htl hm

/-- **The terms at the level over the narrower frozen part are at most the term of the box**, for weights
`g ≥ 0`. -/
theorem flip_inject [RouteOK] {q : ℕ} (hq : Big q) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN)
    {t : ℕ} (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) {s : ℕ} (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    ∑ am ∈ frozS q (e1 ctx + 1) (e2 ctx - 1) βx,
        famJR g (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl)) ≤
      famI g (N1 q) (N2 q) (famB q (Fin.cons (α := fun _ => Cell) ctx βx)) := by
  rw [famI_eq_sum_card]
  have e : ∑ am ∈ frozS q (e1 ctx + 1) (e2 ctx - 1) βx,
      famJR g (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl)) =
        ∑ n ∈ Ioc (N1 q) (N2 q), g n * (((frozS q (e1 ctx + 1) (e2 ctx - 1) βx).filter fun am =>
          frozR am ∣ n ∧ SieveTree.rough ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (n / frozR am)).card : ℝ) := by
    rw [Finset.sum_congr rfl fun am ham => famJR_zero g _ _ _ (frozR_pos ham) q, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [e]
  refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (hg n)
  exact_mod_cast flip_inject_pt hq hctx ht ht2 βx hβ hn

omit [Route] in
/-- The frozen part lies in the range of `r'`, for any route: `inSlab_frozS` with the route as a variable. -/
theorem inSlab_frozS_at (Rt : Route) (ctx : Cell) {s : ℕ} (βx : Fin (s + 1) → Cell) :
    @InSlab Rt _ (fun q => @frozS Rt q (e1 ctx) (e2 ctx) s βx) frozR ctx :=
  @inSlab_frozS Rt ctx s βx

omit [Route] in
/-- The narrower frozen part lies in the range of `r'`, for any route: `inSlab_frozS_inner` with the route as a
variable. -/
theorem inSlab_frozS_inner_at (Rt : Route) (hRt : @RouteOK Rt) (ctx : Cell) {s : ℕ} (βx : Fin (s + 1) → Cell) :
    @InSlab Rt _ (fun q => @frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR ctx :=
  @inSlab_frozS_inner Rt hRt ctx s βx

end SieveAd

#print axioms SieveAd.flip_cover
#print axioms SieveAd.flip_inject
