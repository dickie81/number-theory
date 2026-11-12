/-
# The term of a chain's box over the frozen part, by the estimate in two variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The term of a chain's box over the frozen part of a reversal is a sum over a frozen number
`R = ∏a·m`, a chain `c` of primes of `n/R` and the `n` with `R·∏c ∣ n` and `n/R` rough at the last prime of the
chain. With the cofactor `m` written out as its primes `y` (`SieveAdFrozP.lean`) and the cofactor of `n/R` over the
chain written out as its primes `y'`, it is a sum over the tuples `(a, y, c, y')` with product `n ∈ (N₁, N₂]`:
the tuples of `frozW` followed by a non-increasing tuple of primes at least their last entry, which is the last
prime of the chain. They are a family of comparisons, in no order between `a`, `y` and `c`, and the estimate in two
variables on tuples with a given product (`SieveAdFull.lean`) asks for none.

* `sum_mult_froz`: the multiples `n ∈ (N₁, N₂]` of `R·W`, `W` rough at `p`, with `n/R` rough at `p`, are the
  `R·W·k` with `k ∈ [1, N₂]` rough at `p`.
* `frozΩ`: the comparisons of the tuples of `frozW` (`frozΩ_holds`, `frozΩ_length`, `frozΩ_c`);
  `frozW_eq_RTg`: `frozW` is their family.
* `dIF_frozP_eq`: the term of the chain's box over `frozP … t` is the sum over `t' ≤ DEN` of the sums, over the
  tuples of primes that satisfy `SieveChain.fullTL` of `frozΩ`, of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)`.
* `loRole_le_hiRole`; `evIF_frozP_two`: **the term over `frozP … t` is evaluated** when the exponents of two
  disjoint role sets, the first variable's and the rest's, pass `coreI2`.
* `evIF_froz_two`: **so is the term over the frozen part**; `evIF_froz_two_at` with the route and its exponent as
  variables.

The file imports `SieveAdFrozRole.lean` and `SieveAdFull.lean`.
-/
import SieveAdFrozRole
import SieveAdFull

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-- The multiples `n ∈ (N₁, N₂]` of `R·W`, for `R > 0` and `W > 0` rough at `p`, with `n/R` rough at `p`, are the
`R·W·k` with `k ∈ [1, N₂]` rough at `p`. -/
theorem sum_mult_froz (f : ℕ → ℝ) {R W p N₁ N₂ : ℕ} (hR : 0 < R) (hW : 0 < W) (hWp : SieveTree.rough p W) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if R * W ∣ n ∧ SieveTree.rough p (n / R) then 1 else 0) =
      ∑ k ∈ (Finset.Icc 1 N₂).filter (fun k => ∀ p' < p, p'.Prime → ¬ p' ∣ k),
        (if N₁ < R * W * k ∧ R * W * k ≤ N₂ then f (R * W * k) else 0) := by
  rw [show (∑ n ∈ Finset.Ioc N₁ N₂, f n * (if R * W ∣ n ∧ SieveTree.rough p (n / R) then 1 else 0)) =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => R * W ∣ n ∧ SieveTree.rough p (n / R)), f n by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  have hRW : 0 < R * W := Nat.mul_pos hR hW
  have e : ∀ c : ℕ, R * W * c / R = W * c := fun c => by rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hR]
  refine Finset.sum_nbij' (fun n => n / (R * W)) (fun k => R * W * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Nat.mul_div_cancel_left c hRW]
    rw [e] at hr
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · omega
    exact ⟨⟨⟨hc1, le_trans (Nat.le_mul_of_pos_left c hRW) hn2⟩,
      fun p' hp' hpp hpd => hr p' hp' hpp (dvd_mul_of_dvd_right hpd W)⟩, hn1, hn2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨-, hr⟩, h1, h2⟩ := hk
    refine ⟨⟨h1, h2⟩, dvd_mul_right (R * W) k, ?_⟩
    rw [e]
    intro p' hp' hpp hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hWp p' hp' hpp h
    · exact hr p' hp' hpp h
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hRW
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2.1]

/-- The lower exponent of a role set is at most the upper one, for cells with `lo ≤ hi` and `e₁ ≤ e₂`. -/
theorem loRole_le_hiRole {s k : ℕ} {βx : Fin (s + 1) → Cell} {bx : Fin k → Cell} (hβ : ∀ i, (βx i).1 ≤ (βx i).2)
    (hb : ∀ j, (bx j).1 ≤ (bx j).2) {e₁ e₂ : ℕ} (he : e₁ ≤ e₂) (A : Finset (Fin (s + 1))) (my : Bool)
    (C : Finset (Fin k)) : loRole βx bx e₁ A my C ≤ hiRole βx bx e₂ A my C := by
  unfold loRole hiRole
  have h1 : ∑ i ∈ A, (βx i).1 ≤ ∑ i ∈ A, (βx i).2 := Finset.sum_le_sum fun i _ => hβ i
  have h2 : ∑ i ∈ Aᶜ, (βx i).1 ≤ ∑ i ∈ Aᶜ, (βx i).2 := Finset.sum_le_sum fun i _ => hβ i
  have h3 : ∑ j ∈ C, (bx j).1 ≤ ∑ j ∈ C, (bx j).2 := Finset.sum_le_sum fun j _ => hb j
  cases my
  · simp only [Bool.cond_false]
    omega
  · simp only [Bool.cond_true]
    omega

variable [Route]

/-- A sum over the pairs of a tuple of `frozP` and a tuple of the chain's box is a sum over `frozW`. -/
theorem sum_frozW_pair {q e₁ e₂ s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell)
    (G : (Fin (s + 1 + t) → ℕ) → (Fin k → ℕ) → ℝ) :
    ∑ u ∈ frozP q e₁ e₂ βx t, ∑ c ∈ famB q bx, G u c =
      ∑ w ∈ frozW q e₁ e₂ βx t bx,
        G (fun i => w (Fin.castAdd k i)) (fun j => w (Fin.natAdd (s + 1 + t) j)) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => Fin.append x.1 x.2)
    (fun w => (fun i => w (Fin.castAdd k i), fun j => w (Fin.natAdd (s + 1 + t) j))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, c⟩ hx
    rw [Finset.mem_product] at hx
    show Fin.append u c ∈ frozW q e₁ e₂ βx t bx
    rw [mem_frozW, append_castAdd, append_natAdd]
    refine ⟨fun i => ?_, hx.1, hx.2⟩
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact (mem_frozP.1 hx.1).1 i'
    · rw [Fin.append_right]
      exact (mem_famB.1 hx.2).1 j
  · intro w hw
    rw [mem_frozW] at hw
    exact Finset.mem_product.2 ⟨hw.2.1, hw.2.2⟩
  · rintro ⟨u, c⟩ _
    exact Prod.ext (append_castAdd u c) (append_natAdd u c)
  · intro w _
    exact append_parts w
  · rintro ⟨u, c⟩ _
    show G u c = G (fun i => Fin.append u c (Fin.castAdd k i)) (fun j => Fin.append u c (Fin.natAdd (s + 1 + t) j))
    rw [append_castAdd, append_natAdd]

/-! ### The tuples of `frozW` as a family of comparisons -/

/-- The comparisons of the tuples of `frozW`: the atoms of `frozA`, `y` non-increasing and at least the last prime
of `a`. -/
noncomputable def frozΩ (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    List (GCmp (s + 1 + t + k)) :=
  (frozA q e₁ e₂ βx t bx).map Atom.toG ++
    (((Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).toList.map fun p =>
        ggeVar (posY s t k p.1) (posY s t k p.2)) ++
      List.ofFn fun j : Fin t => ggeVar (posY s t k j) (posA s t k (Fin.last s)))

/-- The comparisons number at most `3(s + 1) + 3k + 2 + t² + t`. -/
theorem frozΩ_length (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    (frozΩ q e₁ e₂ βx t bx).length ≤ 3 * (s + 1) + 3 * k + 2 + t * t + t := by
  unfold frozΩ
  simp only [List.length_append, List.length_map, List.length_ofFn, Finset.length_toList]
  have h1 := frozA_length q e₁ e₂ βx t bx
  have h3 : (Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).card ≤ t * t := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

variable [RouteOK]

/-- What the comparisons say of a tuple of primes. -/
theorem frozΩ_holds {q : ℕ} (hq : 1 ≤ q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {w : Fin (s + 1 + t + k) → ℕ}
    (hp : ∀ i, (w i).Prime) :
    (∀ C ∈ frozΩ q e₁ e₂ βx t bx, C.holds 0 w) ↔ (∀ A ∈ frozA q e₁ e₂ βx t bx, A.sem w) ∧
      Antitone (w ∘ posY s t k) ∧ ∀ j, w (posA s t k (Fin.last s)) ≤ w (posY s t k j) := by
  have hw1 : ∀ i, 1 ≤ w i := fun i => (hp i).one_lt.le
  have hY : (∀ C ∈ ((Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).toList.map fun p =>
      ggeVar (posY s t k p.1) (posY s t k p.2)), C.holds 0 w) ↔ Antitone (w ∘ posY s t k) := by
    rw [List.forall_mem_map]
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, ggeVar_holds _ _ 0 hw1]
    constructor
    · intro h i j hij
      rcases lt_or_eq_of_le hij with h' | h'
      · exact h (i, j) h'
      · subst h'
        exact le_refl _
    · intro h p hp'
      exact h hp'.le
  have hL : (∀ C ∈ (List.ofFn fun j : Fin t => ggeVar (posY s t k j) (posA s t k (Fin.last s))),
      C.holds 0 w) ↔ ∀ j, w (posA s t k (Fin.last s)) ≤ w (posY s t k j) := by
    simp only [List.forall_mem_ofFn_iff, ggeVar_holds _ _ 0 hw1]
  unfold frozΩ
  rw [List.forall_mem_append, List.forall_mem_append, holds_iff_sem (thrOK_frozA hq hβ t hb he₁ he₂) hp]
  exact and_congr Iff.rfl (and_congr hY hL)

/-- The comparisons' constants are at most `(L + 1) log q`. -/
theorem frozΩ_c {q : ℕ} (hq : 1 ≤ q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) :
    ∀ C ∈ frozΩ q e₁ e₂ βx t bx, C.c 0 ≤ (L + 1) * Real.log q := by
  have hL0 : 0 < L := L_pos
  have hlog : 0 ≤ (L + 1) * Real.log q :=
    mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast hq))
  intro C hC
  unfold frozΩ at hC
  rcases List.mem_append.1 hC with h | h
  · exact c_le_of_thrOK hq (thrOK_frozA hq hβ t hb he₁ he₂) C h
  · rcases List.mem_append.1 h with h' | h'
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h'
      exact hlog
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 h'
      exact hlog

/-- **The tuples of `frozW` are a family of comparisons.** -/
theorem frozW_eq_RTg {q : ℕ} (hq : 1 ≤ q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) :
    frozW q e₁ e₂ βx t bx = RTg (s + 1 + t + k) (N2 q) (frozΩ q e₁ e₂ βx t bx) := by
  ext w
  rw [frozW_iff, RTg, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨fun i => SieveTypeIIU.mem_primesLe.2 (hp i),
      (frozΩ_holds hq hβ t hb he₁ he₂ fun i => (hp i).2).2 h⟩
  · rintro ⟨hp, h⟩
    have hp' : ∀ i, w i ≤ N2 q ∧ (w i).Prime := fun i => SieveTypeIIU.mem_primesLe.1 (hp i)
    exact ⟨hp', (frozΩ_holds hq hβ t hb he₁ he₂ fun i => (hp' i).2).1 h⟩

/-! ### The term as a sum over full tuples -/

/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, as a sum over full tuples.**
At a modulus as in `Big`, for cells with ends at most `DEN`, the chain's with `lo ≥ 1`, and `e₁, e₂ ≤ DEN`: the
term of the chain's box over `frozP … t` is the sum over `t' ≤ DEN` of the sums, over the tuples of
`s + 1 + t + k' + 1 + t'` primes up to `N₂` that satisfy `fullTL` of the comparisons of `frozW` (a tuple of
`frozW`, then `t'` primes that do not increase and are at least the last prime of the chain, the product in
`(N₁, N₂]`), of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)`. -/
theorem dIF_frozP_eq {q : ℕ} (hq : Big q) (a : ZMod q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) (t : ℕ) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) :
    dIF q a (frozP q e₁ e₂ βx t) prodR bx =
      ∑ t' ∈ Finset.range (DEN + 1),
        ∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
            (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
          (gA q a (∏ i, z i) - gB q (∏ i, z i)) := by
  obtain ⟨hq2, hx3, -, hN2', -⟩ := big_facts hq
  obtain ⟨-, hXe1, -⟩ := big_n hq
  have hq1 : 1 ≤ q := by omega
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hN2 : (N2 q : ℝ) < Xe q (DEN + 1) := by
    unfold Xe
    push_cast
    exact hN2'
  have hN1 : 1 ≤ N1 q := Nat.le_floor (by push_cast; linarith)
  have hN12 : N1 q ≤ N2 q := Nat.floor_le_floor (by linarith)
  have hY : 1 ≤ N2 q := hN1.trans hN12
  unfold dIF
  have hterm : ∀ u ∈ frozP q e₁ e₂ βx t,
      famIR (gA q a) (N1 q) (N2 q) (prodR u) (famB q bx) - famIR (gB q) (N1 q) (N2 q) (prodR u) (famB q bx) =
        ∑ c ∈ famB q bx, ∑ t' ∈ Finset.range (DEN + 1),
          ∑ y ∈ SieveRoughTuple.tuples (c (Fin.last k')) (N2 q) t',
            (if N1 q < prodR u * prodR c * prodR y ∧ prodR u * prodR c * prodR y ≤ N2 q then
              gA q a (prodR u * prodR c * prodR y) - gB q (prodR u * prodR c * prodR y) else 0) := by
    intro u hu
    have hup : ∀ i, (u i).Prime := fun i => ((mem_frozP.1 hu).1 i).2
    have hR0 : 0 < prodR u := Finset.prod_pos fun i _ => (hup i).pos
    rw [famIR_eq _ _ _ hR0, famIR_eq _ _ _ hR0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨hcp, hsc, hcc⟩ := mem_famB.1 hc
    have hW0 : 0 < prodR c := Finset.prod_pos fun i _ => (hcp i).2.pos
    have hWr : SieveTree.rough (c (Fin.last k')) (prodR c) :=
      rough_prod fun i => rough_prime (hcp i).2 (hsc.antitone (Fin.le_last i))
    have hK : N2 q < c (Fin.last k') ^ (DEN + 1) := by
      have h1 : Xe q 1 ≤ (c (Fin.last k') : ℝ) := (Xe_mono hx1 (hb _).1).trans (hcc _).1
      have h2 : Xe q 1 ^ (DEN + 1) = Xe q (DEN + 1) := Xe_pow hx0 (DEN + 1)
      have h3 : Xe q 1 ^ (DEN + 1) ≤ (c (Fin.last k') : ℝ) ^ (DEN + 1) :=
        pow_le_pow_left₀ (Xe_pos hx0 1).le h1 _
      have h4 : (N2 q : ℝ) < ((c (Fin.last k') ^ (DEN + 1) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h4
    rw [← Finset.sum_sub_distrib]
    refine ((Finset.sum_congr rfl fun n _ => ?_).trans
      (sum_mult_froz (fun n => gA q a n - gB q n) hR0 hW0 hWr)).trans ?_
    · show gA q a n * (if prodR u * prodR c ∣ n ∧ SieveTree.rough (c (Fin.last k')) (n / prodR u) then 1 else 0) -
        gB q n * (if prodR u * prodR c ∣ n ∧ SieveTree.rough (c (Fin.last k')) (n / prodR u) then 1 else 0) =
        (gA q a n - gB q n) *
          (if prodR u * prodR c ∣ n ∧ SieveTree.rough (c (Fin.last k')) (n / prodR u) then 1 else 0)
      ring
    · exact sum_rough_tuples (hcp _).2.two_le hY
        (fun m => if N1 q < prodR u * prodR c * m ∧ prodR u * prodR c * m ≤ N2 q then
          gA q a (prodR u * prodR c * m) - gB q (prodR u * prodR c * m) else 0) DEN hK
  refine (Finset.sum_congr rfl hterm).trans ((sum_frozW_pair βx t bx _).trans ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [frozW_eq_RTg hq1 hβ t (fun j => (hb j).2) he₁ he₂]
  refine Eq.trans ?_ (SieveTwoTerm.sum_full_eq (k' := s + 1 + t + k') (frozΩ q e₁ e₂ βx t bx) (Y := N2 q)
    (N₁ := N1 q) (N₂ := N2 q) t' hN1 hN12 le_rfl (fun n => gA q a n - gB q n))
  refine Finset.sum_congr rfl fun w _ => ?_
  have hprod : prodR (fun i => w (Fin.castAdd (k' + 1) i)) * prodR (fun j => w (Fin.natAdd (s + 1 + t) j)) =
      ∏ i, w i := (prodR_split w).symm
  rw [hprod]
  rfl

/-! ### The term is evaluated -/

variable [SieveCert.IBPar] [IBFits]

/-- **The term of a chain's box over the frozen part with a cofactor of `t` primes, by the estimate in two
variables.** Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, and `e₁ ≤ e₂ ≤ DEN`. Let
`(A₀, my₀, C₀)` be the parts of the first variable and `(Ar, myr, Cr)` those of the rest, disjoint, the rest's
exponent with a positive lower bound. If the exponents of the two role sets pass `coreI2`, the term of the chain's
box over `frozP … t` is evaluated. -/
theorem evIF_frozP_two {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he : e₁ ≤ e₂) (he₂ : e₂ ≤ DEN) (t : ℕ)
    {k' : ℕ} {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (A₀ Ar : Finset (Fin (s + 1))) (my₀ myr : Bool) (C₀ Cr : Finset (Fin (k' + 1)))
    (hdA : Disjoint A₀ Ar) (hdmy : (my₀ && myr) = false) (hdC : Disjoint C₀ Cr)
    (hρ : 0 < loRole βx bx e₁ Ar myr Cr)
    (hok : coreI2 (loRole βx bx e₁ A₀ my₀ C₀) (hiRole βx bx e₂ A₀ my₀ C₀) (loRole βx bx e₁ Ar myr Cr)
      (hiRole βx bx e₂ Ar myr Cr) = true) :
    EvIF (fun q => frozP q e₁ e₂ βx t) prodR bx := by
  have he₁ : e₁ ≤ DEN := he.trans he₂
  have hβD : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN := fun i => ⟨(hβ i).2.1.trans (hβ i).2.2, (hβ i).2.2⟩
  have hbD : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).2.1.trans (hb j).2.2, (hb j).2.2⟩
  have hbD1 : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN := fun j => ⟨(hb j).1, hbD j⟩
  have huv := loRole_le_hiRole (fun i => (hβ i).2.1) (fun j => (hb j).2.1) he A₀ my₀ C₀
  have hρ12 := loRole_le_hiRole (fun i => (hβ i).2.1) (fun j => (hb j).2.1) he Ar myr Cr
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  intro η hη
  have hcore := fun t' : ℕ => full2_core _ _ _ _ hok huv hρ12 (s + 1 + t + k' + 1 + t')
    (3 * (s + 1) + 3 * (k' + 1) + 2 + t * t + t + t' * t' + t' + 2)
  choose δf hδf q₀f hq₀f using hcore
  have hall : ∀ᶠ q : ℕ in atTop, ∀ t' ∈ Finset.range (DEN + 1),
      q₀f t' ≤ q ∧ (q : ℝ) ^ (L - δf t') ≤ η / ((DEN : ℝ) + 1) * Xq q := by
    rw [Filter.eventually_all_finset]
    intro t' _
    exact (eventually_ge_atTop (q₀f t')).and (le_Xq (hδf t') (by positivity))
  filter_upwards [hall, big_ev] with q hq hbig a ha
  obtain ⟨hq2, hx3, -, hN2', -⟩ := big_facts hbig
  have hq1 : 1 ≤ q := by omega
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqn : NeZero q := ⟨by omega⟩
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hx1' : 1 < xq q := by linarith
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hN1 : 1 ≤ N1 q := Nat.le_floor (by push_cast; linarith)
  have hN12 : N1 q ≤ N2 q := Nat.floor_le_floor (by linarith)
  have hY : 1 ≤ N2 q := hN1.trans hN12
  have hlogN₂ : Real.log (N2 q : ℝ) ≤ (L + 1) * Real.log q := by
    have hq0 : (0 : ℝ) < q := by linarith
    have h1 : (N2 q : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      have h2 : (N2 q : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
      have h3 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      have h4 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
      rw [Real.rpow_add hq0, Real.rpow_one]
      nlinarith
    have h2 := Real.log_le_log (by exact_mod_cast hY) h1
    rwa [Real.log_rpow hq0] at h2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1'
  show |dIF q a (frozP q e₁ e₂ βx t) prodR bx| ≤ _
  rw [dIF_frozP_eq hbig a hβD he₁ he₂ t hbD1]
  have hbound : ∀ t' ∈ Finset.range (DEN + 1),
      |∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
          (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))| ≤ (q.totient : ℝ)⁻¹ * (η / ((DEN : ℝ) + 1) * Xq q) := by
    intro t' ht'
    obtain ⟨hq0', hXle⟩ := hq t' ht'
    have hcast : ∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)), dw q a (∏ i, z i) =
        ((∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
          (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
          (gA q a (∏ i, z i) - gB q (∏ i, z i)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun z _ => dw_eq q a _
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast]
    -- what a tuple of the family satisfies
    have hfacts : ∀ z : Fin (s + 1 + t + k' + 1 + t') → ℕ, (∀ i, (z i).Prime) →
        (∀ C ∈ fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q), C.holds 0 z) →
        (∀ i, xq q ^ (((1 : ℕ) : ℝ) / DEN) ≤ z i) ∧
          xq q ^ ((loRole βx bx e₁ A₀ my₀ C₀ : ℝ) / DEN) ≤
            ((∏ i ∈ (roleSet s t (k' + 1) A₀ my₀ C₀).map (Fin.castAddEmb t'), z i : ℕ) : ℝ) ∧
          ((∏ i ∈ (roleSet s t (k' + 1) A₀ my₀ C₀).map (Fin.castAddEmb t'), z i : ℕ) : ℝ) ≤
            xq q ^ ((hiRole βx bx e₂ A₀ my₀ C₀ : ℝ) / DEN) ∧
          xq q ^ ((loRole βx bx e₁ Ar myr Cr : ℝ) / DEN) ≤
            ((∏ i ∈ (roleSet s t (k' + 1) Ar myr Cr).map (Fin.castAddEmb t'), z i : ℕ) : ℝ) ∧
          ((∏ i ∈ (roleSet s t (k' + 1) Ar myr Cr).map (Fin.castAddEmb t'), z i : ℕ) : ℝ) ≤
            xq q ^ ((hiRole βx bx e₂ Ar myr Cr : ℝ) / DEN) ∧ N1 q < ∏ i, z i ∧ ∏ i, z i ≤ N2 q := by
      intro z hz hzΩ
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd t' i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (s + 1 + t + k' + 1) b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlast, hlo, hhi⟩ := (SieveTwoTerm.fullTL_holds0 (k' := s + 1 + t + k') (t := t')
        (frozΩ q e₁ e₂ βx t bx)
        (by exact_mod_cast hN1) (by exact_mod_cast hY) _ _ hrt1 hy1).1 hzΩ
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd t' i)) * ∏ b, z (Fin.natAdd (s + 1 + t + k' + 1) b) :=
        Fin.prod_univ_add z
      have hlo' : N1 q < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
      have hhi' : ∏ i, z i ≤ N2 q := by rw [hprod]; exact_mod_cast hhi
      have hz0 : 0 < ∏ i, z i := by omega
      have hrtW : (fun i => z (Fin.castAdd t' i)) ∈ frozW q e₁ e₂ βx t bx := by
        rw [frozW_eq_RTg hq1 hβD t hbD he₁ he₂, RTg, Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun i => SieveTypeIIU.mem_primesLe.2 ⟨?_, hz _⟩, hΩ'⟩
        exact (Nat.le_of_dvd hz0 (Finset.dvd_prod_of_mem z (Finset.mem_univ _))).trans hhi'
      have hge := frozW_ge hx1 (f := 1) (hβ (Fin.last s)).1 (fun j => (hb j).1) hrtW
      have hsemA := (frozW_iff.1 hrtW).2.1
      have hw1 : ∀ i, 1 ≤ (fun i => z (Fin.castAdd t' i)) i := fun i => hrt1 i
      obtain ⟨h01, h02⟩ := role_bounds hx1' hw1 hsemA A₀ my₀ C₀
      obtain ⟨hr1, hr2⟩ := role_bounds hx1' hw1 hsemA Ar myr Cr
      have hmap : ∀ S : Finset (Fin (s + 1 + t + (k' + 1))),
          ((∏ i ∈ S.map (Fin.castAddEmb t'), z i : ℕ) : ℝ) = ∏ i ∈ S, ((z (Fin.castAdd t' i) : ℕ) : ℝ) := by
        intro S
        rw [Finset.prod_map, Nat.cast_prod]
        exact Finset.prod_congr rfl fun i _ => rfl
      rw [hmap, hmap]
      refine ⟨fun i => ?_, h01, h02, hr1, hr2, hlo', hhi'⟩
      refine Fin.addCases (fun i' => ?_) (fun b => ?_) i
      · exact hge i'
      · have h1 : Xe q 1 ≤ (z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) : ℝ) :=
          hge (Fin.last (s + 1 + t + k'))
        have h2 : (z (Fin.castAdd t' (Fin.last (s + 1 + t + k'))) : ℝ) ≤
            z (Fin.natAdd (s + 1 + t + k' + 1) b) := by exact_mod_cast hlast b
        exact h1.trans h2
    by_cases hSr : (roleSet s t (k' + 1) Ar myr Cr).Nonempty
    · refine (hq₀f t' q hq0' a ha ((roleSet s t (k' + 1) A₀ my₀ C₀).map (Fin.castAddEmb t'))
        ((roleSet s t (k' + 1) Ar myr Cr).map (Fin.castAddEmb t'))
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q))
        ((Finset.disjoint_map _).2 (roleSet_disjoint s t (k' + 1) hdA hdmy hdC)) (hSr.map) ?_ ?_ hfacts).trans
        (mul_le_mul_of_nonneg_left hXle hφ)
      · refine (length_fullTL_le (s + 1 + t + k') t' _ _ _).trans ?_
        have := frozΩ_length q e₁ e₂ βx t bx
        omega
      · intro C hC
        unfold fullTL at hC
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with ((⟨C', hC', rfl⟩ | hC) | hC) | rfl | rfl
        · show C'.c 0 ≤ _
          exact frozΩ_c hq1 hβD t hbD he₁ he₂ C' hC'
        · obtain ⟨a', b', -, rfl⟩ := mem_yPairs.1 hC
          show (0 : ℝ) ≤ _
          positivity
        · unfold yLast at hC
          obtain ⟨a', -, rfl⟩ := List.mem_map.1 hC
          show (0 : ℝ) ≤ _
          positivity
        · show Real.log ((0 : ℕ) : ℝ) - Real.log (N1 q : ℝ) ≤ _
          have h0 : 0 ≤ Real.log (N1 q : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
          have h1 : 0 ≤ (L + 1) * Real.log q := by positivity
          simp only [Nat.cast_zero, Real.log_zero]
          linarith
        · show Real.log (N2 q : ℝ) - Real.log ((0 : ℕ) : ℝ) ≤ _
          simp only [Nat.cast_zero, Real.log_zero]
          linarith
    · have hemp : ∀ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
          (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)), dw q a (∏ i, z i) = 0 := by
        intro z hz
        exfalso
        rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
        obtain ⟨-, -, -, h3, -⟩ := hfacts z (fun i => (SieveTypeIIU.mem_primesLe.1 (hz.1 i)).2) hz.2
        rw [Finset.not_nonempty_iff_eq_empty] at hSr
        rw [hSr, Finset.map_empty, Finset.prod_empty, Nat.cast_one] at h3
        have h4 : Xe q (loRole βx bx e₁ Ar myr Cr) ≤ Xe q 0 := by
          rw [Xe_zero]
          exact h3
        have h5 := (Xe_le_iff hx1').1 h4
        omega
      rw [Finset.sum_eq_zero hemp, norm_zero]
      positivity
  calc |∑ t' ∈ Finset.range (DEN + 1), ∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))|
      ≤ ∑ t' ∈ Finset.range (DEN + 1), |∑ z ∈ RTg (s + 1 + t + k' + 1 + t') (N2 q)
        (fullTL (s + 1 + t + k') t' (frozΩ q e₁ e₂ βx t bx) (N1 q) (N2 q)),
        (gA q a (∏ i, z i) - gB q (∏ i, z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t' ∈ Finset.range (DEN + 1), (q.totient : ℝ)⁻¹ * (η / ((DEN : ℝ) + 1) * Xq q) :=
        Finset.sum_le_sum hbound
    _ = (q.totient : ℝ)⁻¹ * (η * Xq q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-- **The term of a chain's box over the frozen part, by the estimate in two variables.** Let `βx` and the
chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, and `e₁ ≤ e₂ ≤ DEN`. Let `(A₀, my₀, C₀)` be the parts of the
first variable and `(Ar, myr, Cr)` those of the rest, disjoint, the rest's exponent with a positive lower bound.
If the exponents of the two role sets pass `coreI2`, the term of the chain's box over the frozen part is
evaluated. -/
theorem evIF_froz_two {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he : e₁ ≤ e₂) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (A₀ Ar : Finset (Fin (s + 1))) (my₀ myr : Bool) (C₀ Cr : Finset (Fin (k' + 1)))
    (hdA : Disjoint A₀ Ar) (hdmy : (my₀ && myr) = false) (hdC : Disjoint C₀ Cr)
    (hρ : 0 < loRole βx bx e₁ Ar myr Cr)
    (hok : coreI2 (loRole βx bx e₁ A₀ my₀ C₀) (hiRole βx bx e₂ A₀ my₀ C₀) (loRole βx bx e₁ Ar myr Cr)
      (hiRole βx bx e₂ Ar myr Cr) = true) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  have hT : DEN + 1 ≤ (DEN + 1) * (βx (Fin.last s)).1 := Nat.le_mul_of_pos_right _ (hβ _).1
  exact evIF_frozS he₂ hT fun t _ => evIF_frozP_two hβ he he₂ t hb A₀ Ar my₀ myr C₀ Cr hdA hdmy hdC hρ hok

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The term of a chain's box over the frozen part, by the estimate in two variables, for any route**:
`evIF_froz_two` with the route and its exponent as variables. -/
theorem evIF_froz_two_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr)
    {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN)
    (he : e₁ ≤ e₂) (he₂ : e₂ ≤ DEN) {k' : ℕ} {bx : Fin (k' + 1) → Cell}
    (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (A₀ Ar : Finset (Fin (s + 1))) (my₀ myr : Bool) (C₀ Cr : Finset (Fin (k' + 1)))
    (hdA : Disjoint A₀ Ar) (hdmy : (my₀ && myr) = false) (hdC : Disjoint C₀ Cr)
    (hρ : 0 < loRole βx bx e₁ Ar myr Cr)
    (hok : @coreI2 Pr (loRole βx bx e₁ A₀ my₀ C₀) (hiRole βx bx e₂ A₀ my₀ C₀) (loRole βx bx e₁ Ar myr Cr)
      (hiRole βx bx e₂ Ar myr Cr) = true) :
    @EvIF Rt _ (fun q => @frozS Rt q e₁ e₂ s βx) frozR k' bx :=
  @evIF_froz_two Rt hRt Pr hPr e₁ e₂ s βx hβ he he₂ k' bx hb A₀ Ar my₀ myr C₀ Cr hdA hdmy hdC hρ hok

end SieveAd

#print axioms SieveAd.evIF_froz_two_at
