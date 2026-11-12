/-
# The terms at a floor over the frozen part, as a family of tuples of distinct primes

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A term at a floor of the tree over the frozen part of a reversal is a sum over a frozen number
`R = ∏a·m`, a chain `c` of primes of `n/R` and the `n` with `R·∏c ∣ n` and `n/R` rough at the floor. With the
cofactor `m` written out as its primes (`SieveAdFrozP.lean`), and the floor at most the least prime of `R`, it is
a sum over tuples of primes `w = (a, y, c)` of the `n` that `∏w` divides and that are rough at the floor: `R` is
rough at the floor, so `n/R` is exactly when `n` is. The tuples of distinct primes are a family of atoms, in no
order between `a`, `y` and `c`; the others have a repeated prime, and the `n` that the square of a prime above the
floor divides weigh little.

* `rough_div_iff`: for `R ∣ n` rough at `Z`, `n/R` is rough at `Z` exactly when `n` is.
* `frozW q e₁ e₂ βx t bx`: the tuples of `frozP … t` followed by a tuple of the chain's box (`mem_frozW`).
  `dJF_frozP_eq`: for `f ≤ lo_s`, the terms at the floor `x^{f/DEN}` over `frozP … t` are the sum over `frozW` of
  `Σ_n (1[n ≡ a] − 1[(n, q) = 1]/φ(q))·1[∏w ∣ n, n rough at the floor]`.
* `posA`, `posY`, `posC`: the positions of the three parts, which are distinct (`posA_ne_posY`, `posA_ne_posC`,
  `posY_ne_posC`); `frozE q e₁ e₂ βx t bx`: the atoms of the tuples of
  `frozW` (`frozA`: the cells, the two orders and the slab; `frozW_iff`) with `y` strictly decreasing and above
  the last prime of `a` (`sem_frozA`, `sem_frozE`, `frozE_length`, `thrOK_frozE`). `frozW_inj_eq`: the injective
  tuples of `frozW` are those of the family of `frozE`.
* `sq_small_B`: the `n` of `(N₁, N₂]` that the square of a prime at least `⌈x^{y/DEN}⌉` divides weigh little in
  the comparison set. `frozW_noninj_le`: the tuples of `frozW` with a repeated prime contribute at most
  `(DEN + 1)^K` times the weight of those `n` in the two sets.
* `evJF_frozP`: **the terms at a floor over `frozP … t` are evaluated when those of the injective tuples of the
  family of `frozE` are**; `evJF_frozP_at` with the route as a variable.

The file imports `SieveAdFrozP.lean`, `SieveAdFamSet.lean` and `SieveAdRevSum.lean`.
-/
import SieveAdFrozP
import SieveAdFamSet
import SieveAdRevSum

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-- For `R ∣ n` with `R` rough at `Z`: `n/R` is rough at `Z` exactly when `n` is. -/
theorem rough_div_iff {Z R n : ℕ} (hR : SieveTree.rough Z R) (hd : R ∣ n) :
    SieveTree.rough Z (n / R) ↔ SieveTree.rough Z n := by
  constructor
  · intro h p hp hpp hpn
    rw [← Nat.mul_div_cancel' hd] at hpn
    rcases (Nat.Prime.dvd_mul hpp).1 hpn with h1 | h1
    · exact hR p hp hpp h1
    · exact h p hp hpp h1
  · intro h
    exact rough_of_dvd h (Nat.div_dvd_of_dvd hd)

/-- A tuple that is not injective has the square of an entry dividing its product. -/
theorem sq_dvd_prodR {n : ℕ} {w : Fin n → ℕ} (hni : ¬ Function.Injective w) : ∃ i, w i ^ 2 ∣ prodR w := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hni
  refine ⟨i, ?_⟩
  have h1 : w i * ∏ l ∈ Finset.univ.erase i, w l = ∏ l, w l := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have h2 : w j ∣ ∏ l ∈ Finset.univ.erase i, w l :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ j⟩)
  have h3 : w i ∣ ∏ l ∈ Finset.univ.erase i, w l := by
    rw [hij]
    exact h2
  unfold prodR
  rw [← h1, pow_two]
  exact Nat.mul_dvd_mul_left _ h3

/-! ### The positions of the three parts -/

/-- The positions of the box's part in a tuple `(a, y, c)`. -/
def posA (s t k : ℕ) : Fin (s + 1) ↪ Fin (s + 1 + t + k) := (Fin.castAddEmb t).trans (Fin.castAddEmb k)

/-- The positions of the cofactor's primes. -/
def posY (s t k : ℕ) : Fin t ↪ Fin (s + 1 + t + k) := (Fin.natAddEmb (s + 1)).trans (Fin.castAddEmb k)

/-- The positions of the chain. -/
def posC (s t k : ℕ) : Fin k ↪ Fin (s + 1 + t + k) := Fin.natAddEmb (s + 1 + t)

/-- The positions of the frozen number: the box's part and the cofactor's primes. -/
def posAY (s t k : ℕ) : Finset (Fin (s + 1 + t + k)) := Finset.univ.map (Fin.castAddEmb k)

theorem posA_ne_posY (s t k : ℕ) (i : Fin (s + 1)) (j : Fin t) : posA s t k i ≠ posY s t k j := by
  intro h
  have hv : (i : ℕ) = s + 1 + (j : ℕ) := congrArg Fin.val h
  have := i.isLt
  omega

theorem posA_ne_posC (s t k : ℕ) (i : Fin (s + 1)) (j : Fin k) : posA s t k i ≠ posC s t k j := by
  intro h
  have hv : (i : ℕ) = s + 1 + t + (j : ℕ) := congrArg Fin.val h
  have := i.isLt
  omega

theorem posY_ne_posC (s t k : ℕ) (i : Fin t) (j : Fin k) : posY s t k i ≠ posC s t k j := by
  intro h
  have hv : s + 1 + (i : ℕ) = s + 1 + t + (j : ℕ) := congrArg Fin.val h
  have := i.isLt
  omega

variable [Route]

/-! ### The tuples of a term -/

/-- The tuples of a term over the frozen part with a cofactor of `t` primes: a tuple of `frozP` and then a tuple
of the chain's box. -/
noncomputable def frozW (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    Finset (Fin (s + 1 + t + k) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (s + 1 + t + k) => SieveTypeIIU.primesLe (N2 q)).filter fun w =>
    (fun i => w (Fin.castAdd k i)) ∈ frozP q e₁ e₂ βx t ∧ (fun j => w (Fin.natAdd (s + 1 + t) j)) ∈ famB q bx

theorem mem_frozW {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {t k : ℕ} {bx : Fin k → Cell}
    {w : Fin (s + 1 + t + k) → ℕ} :
    w ∈ frozW q e₁ e₂ βx t bx ↔ (∀ i, w i ≤ N2 q ∧ (w i).Prime) ∧
      (fun i => w (Fin.castAdd k i)) ∈ frozP q e₁ e₂ βx t ∧ (fun j => w (Fin.natAdd (s + 1 + t) j)) ∈ famB q bx := by
  rw [frozW, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- The pairs of a tuple of `frozP` and a tuple of the chain's box are the tuples of `frozW`. -/
theorem sum_frozW_eq {q e₁ e₂ s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) (F : ℕ → ℝ) :
    ∑ u ∈ frozP q e₁ e₂ βx t, ∑ c ∈ famB q bx, F (prodR u * prodR c) =
      ∑ w ∈ frozW q e₁ e₂ βx t bx, F (prodR w) := by
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
    show F (prodR u * prodR c) = F (prodR (Fin.append u c))
    rw [prodR_append]

/-- Every prime of a tuple of `frozW` is at least `x^{f/DEN}`, for `f` at most the lower ends of the last cell of
`βx` and of the cells of the chain. -/
theorem frozW_ge {q : ℕ} (hx1 : 1 ≤ xq q) {f e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβf : f ≤ (βx (Fin.last s)).1) {t k : ℕ} {bx : Fin k → Cell} (hbf : ∀ j, f ≤ (bx j).1)
    {w : Fin (s + 1 + t + k) → ℕ} (hw : w ∈ frozW q e₁ e₂ βx t bx) (i : Fin (s + 1 + t + k)) :
    Xe q f ≤ w i := by
  obtain ⟨-, hu, hc⟩ := mem_frozW.1 hw
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · obtain ⟨-, ha, -⟩ := mem_frozP.1 hu
    obtain ⟨-, -, hca⟩ := mem_famB.1 ha
    have h1 : Xe q f ≤ Xe q (βx (Fin.last s)).1 := Xe_mono hx1 hβf
    have h2 : Xe q (βx (Fin.last s)).1 ≤ (w (Fin.castAdd k (Fin.castAdd t (Fin.last s))) : ℝ) :=
      (hca (Fin.last s)).1
    have h3 : w (Fin.castAdd k (Fin.castAdd t (Fin.last s))) ≤ w (Fin.castAdd k i') := frozP_last_le hu i'
    have h3' : (w (Fin.castAdd k (Fin.castAdd t (Fin.last s))) : ℝ) ≤ w (Fin.castAdd k i') := by
      exact_mod_cast h3
    linarith
  · obtain ⟨-, -, hcc⟩ := mem_famB.1 hc
    exact (Xe_mono hx1 (hbf j)).trans (hcc j).1

/-- **The terms at a floor over the frozen part with a cofactor of `t` primes, as a sum over tuples.** For `x ≥ 1`
and `f` at most the lower end of the last cell of `βx`: the terms at the floor `x^{f/DEN}` of the chain's box over
`frozP … t` are the sum over the tuples `w` of `frozW` of the `n` that `∏w` divides and that are rough at the
floor, in `𝒜` minus the comparison set. -/
theorem dJF_frozP_eq {q : ℕ} (hx1 : 1 ≤ xq q) (a : ZMod q) {f e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβf : f ≤ (βx (Fin.last s)).1) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    dJF q a f (frozP q e₁ e₂ βx t) prodR bx =
      ∑ w ∈ frozW q e₁ e₂ βx t bx, ∑ n ∈ Ioc (N1 q) (N2 q),
        (gA q a n - gB q n) * (if prodR w ∣ n ∧ SieveTree.rough ⌈Xe q f⌉₊ n then 1 else 0) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = ⌈Xe q f⌉₊ := ⟨_, rfl⟩
  have hZ' : ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ = Z := hZ.symm
  unfold dJF
  rw [hZ', ← hZ, ← sum_frozW_eq βx t bx (fun W => ∑ n ∈ Ioc (N1 q) (N2 q),
    (gA q a n - gB q n) * (if W ∣ n ∧ SieveTree.rough Z n then 1 else 0))]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hup : ∀ i, (u i).Prime := fun i => ((mem_frozP.1 hu).1 i).2
  have hR0 : 0 < prodR u := Finset.prod_pos fun i _ => (hup i).pos
  have hrR : SieveTree.rough Z (prodR u) := by
    refine rough_prod fun i => rough_prime (hup i) ?_
    rw [hZ]
    refine Nat.ceil_le.2 ?_
    obtain ⟨-, ha, -⟩ := mem_frozP.1 hu
    obtain ⟨-, -, hc⟩ := mem_famB.1 ha
    have h1 : Xe q f ≤ Xe q (βx (Fin.last s)).1 := Xe_mono hx1 hβf
    have h2 : Xe q (βx (Fin.last s)).1 ≤ (u (Fin.castAdd t (Fin.last s)) : ℝ) := (hc (Fin.last s)).1
    have h3 : (u (Fin.castAdd t (Fin.last s)) : ℝ) ≤ u i := by exact_mod_cast frozP_last_le hu i
    linarith
  rw [famJR_eq _ _ _ _ hR0, famJR_eq _ _ _ _ hR0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : prodR u * prodR c ∣ n ∧ SieveTree.rough Z n
  · have h' : prodR u * ∏ i, c i ∣ n ∧ SieveTree.rough Z (n / prodR u) :=
      ⟨h.1, (rough_div_iff hrR (Dvd.dvd.trans (Dvd.intro _ rfl) h.1)).2 h.2⟩
    rw [ite_eq_left h, ite_eq_left h']
    ring
  · have h' : ¬ (prodR u * ∏ i, c i ∣ n ∧ SieveTree.rough Z (n / prodR u)) := fun h' =>
      h ⟨h'.1, (rough_div_iff hrR (Dvd.dvd.trans (Dvd.intro _ rfl) h'.1)).1 h'.2⟩
    rw [ite_eq_right h, ite_eq_right h']
    ring

/-! ### The tuples of distinct primes as a family of atoms -/

omit [Route] in
/-- The product over the positions of the frozen number is the product of the first part. -/
theorem prod_posAY (s t k : ℕ) (w : Fin (s + 1 + t + k) → ℕ) :
    ∏ i ∈ posAY s t k, (w i : ℝ) = ((prodR fun i => w (Fin.castAdd k i) : ℕ) : ℝ) := by
  unfold posAY prodR
  rw [Finset.prod_map, Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => rfl

/-- The atoms of the tuples `(a, y, c)` of `frozW`: `a` in the box `βx` and `c` in the chain's box, each
decreasing, and the product of `a` and `y` in `(x^{e₁/DEN}, x^{e₂/DEN}]`. -/
noncomputable def frozA (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    List (Atom (s + 1 + t + k)) :=
  (specB q βx).map (Atom.emb (posA s t k)) ++ ((specB q bx).map (Atom.emb (posC s t k)) ++
    [Atom.prodGt (posAY s t k) (Xe q e₁), Atom.prodLe (posAY s t k) (Xe q e₂)])

/-- What the atoms of `frozA` say of a tuple. -/
theorem sem_frozA (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell)
    (w : Fin (s + 1 + t + k) → ℕ) :
    (∀ A ∈ frozA q e₁ e₂ βx t bx, A.sem w) ↔
      (StrictAnti (w ∘ posA s t k) ∧
        ∀ i, Xe q (βx i).1 ≤ w (posA s t k i) ∧ (w (posA s t k i) : ℝ) < Xe q (βx i).2) ∧
      (StrictAnti (w ∘ posC s t k) ∧
        ∀ j, Xe q (bx j).1 ≤ w (posC s t k j) ∧ (w (posC s t k j) : ℝ) < Xe q (bx j).2) ∧
      Xe q e₁ < ∏ i ∈ posAY s t k, (w i : ℝ) ∧ ∏ i ∈ posAY s t k, (w i : ℝ) ≤ Xe q e₂ := by
  have hA : (∀ A ∈ (specB q βx).map (Atom.emb (posA s t k)), A.sem w) ↔ StrictAnti (w ∘ posA s t k) ∧
      ∀ i, Xe q (βx i).1 ≤ w (posA s t k i) ∧ (w (posA s t k i) : ℝ) < Xe q (βx i).2 := by
    rw [List.forall_mem_map]
    simp only [Atom.emb_sem]
    exact sem_specB q βx (w ∘ posA s t k)
  have hC : (∀ A ∈ (specB q bx).map (Atom.emb (posC s t k)), A.sem w) ↔ StrictAnti (w ∘ posC s t k) ∧
      ∀ j, Xe q (bx j).1 ≤ w (posC s t k j) ∧ (w (posC s t k j) : ℝ) < Xe q (bx j).2 := by
    rw [List.forall_mem_map]
    simp only [Atom.emb_sem]
    exact sem_specB q bx (w ∘ posC s t k)
  have hS : (∀ A ∈ [Atom.prodGt (posAY s t k) (Xe q e₁), Atom.prodLe (posAY s t k) (Xe q e₂)], A.sem w) ↔
      Xe q e₁ < ∏ i ∈ posAY s t k, (w i : ℝ) ∧ ∏ i ∈ posAY s t k, (w i : ℝ) ≤ Xe q e₂ := by
    constructor
    · intro h
      exact ⟨h (Atom.prodGt (posAY s t k) (Xe q e₁)) (by simp), h (Atom.prodLe (posAY s t k) (Xe q e₂)) (by simp)⟩
    · rintro ⟨h1, h2⟩ A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact h1
      · exact h2
  unfold frozA
  rw [List.forall_mem_append, List.forall_mem_append]
  exact and_congr hA (and_congr hC hS)

/-- The atoms of `frozA` number at most `3(s + 1) + 3k + 2`. -/
theorem frozA_length (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    (frozA q e₁ e₂ βx t bx).length ≤ 3 * (s + 1) + 3 * k + 2 := by
  unfold frozA
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  have h1 := specB_length q βx
  have h2 := specB_length q bx
  omega

/-- For `q ≥ 1`, cells with ends at most `DEN` and `e₁, e₂ ≤ DEN`, the thresholds of `frozA` lie in
`[1, q^{L+1}]`. -/
theorem thrOK_frozA [RouteOK] {q : ℕ} (hq : 1 ≤ q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) :
    ThrOK q (frozA q e₁ e₂ βx t bx) := by
  have hL0 : 0 < L := L_pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1 hL0.le
  have hXe : ∀ e : ℕ, e ≤ DEN → 1 ≤ Xe q e ∧ Xe q e ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
    intro e he
    refine ⟨?_, ?_⟩
    · have := Xe_mono hx1 (Nat.zero_le e)
      rwa [Xe_zero] at this
    · have h1 : Xe q e ≤ xq q := (Xe_mono hx1 he).trans (Xe_DEN q).le
      have h2 : xq q ≤ (q : ℝ) ^ (L + 1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      linarith
  unfold frozA
  refine thrOK_append ?_ (thrOK_append ?_ ?_)
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := List.mem_map.1 hA
    rw [Atom.emb_thr]
    exact thrOK_specB hq hL0.le βx hβ A' hA'
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := List.mem_map.1 hA
    rw [Atom.emb_thr]
    exact thrOK_specB hq hL0.le bx hb A' hA'
  · intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · exact hXe e₁ he₁
    · exact hXe e₂ he₂

/-- **The tuples of `frozW`**: the tuples of primes up to `N₂` that satisfy the atoms of `frozA`, with `y`
non-increasing and at least the last prime of `a`. -/
theorem frozW_iff {q e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {t k : ℕ} {bx : Fin k → Cell}
    {w : Fin (s + 1 + t + k) → ℕ} :
    w ∈ frozW q e₁ e₂ βx t bx ↔ (∀ i, w i ≤ N2 q ∧ (w i).Prime) ∧ (∀ A ∈ frozA q e₁ e₂ βx t bx, A.sem w) ∧
      Antitone (w ∘ posY s t k) ∧ ∀ j, w (posA s t k (Fin.last s)) ≤ w (posY s t k j) := by
  rw [mem_frozW, sem_frozA, prod_posAY]
  constructor
  · rintro ⟨hp, hu, hc⟩
    obtain ⟨-, ha, hanti, hz, hslab⟩ := mem_frozP.1 hu
    obtain ⟨-, hsa, hca⟩ := mem_famB.1 ha
    obtain ⟨-, hsc, hcc⟩ := mem_famB.1 hc
    exact ⟨hp, ⟨⟨hsa, hca⟩, ⟨hsc, hcc⟩, hslab⟩, hanti, hz⟩
  · rintro ⟨hp, ⟨⟨hsa, hca⟩, ⟨hsc, hcc⟩, hslab⟩, hanti, hz⟩
    exact ⟨hp, mem_frozP.2 ⟨fun i => hp _, mem_famB.2 ⟨fun i => hp _, hsa, hca⟩, hanti, hz, hslab⟩,
      mem_famB.2 ⟨fun j => hp _, hsc, hcc⟩⟩

/-- The atoms of the tuples `(a, y, c)` of a term over the frozen part with a cofactor of `t` distinct primes: those
of `frozA`, and `y` strictly decreasing and above the last prime of `a`. -/
noncomputable def frozE (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    List (Atom (s + 1 + t + k)) :=
  frozA q e₁ e₂ βx t bx ++
    (((Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).toList.map fun p =>
        Atom.ltVar (posY s t k p.1) (posY s t k p.2)) ++
      List.ofFn fun j : Fin t => Atom.ltVar (posY s t k j) (posA s t k (Fin.last s)))

/-- What the atoms say of a tuple. -/
theorem sem_frozE (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell)
    (w : Fin (s + 1 + t + k) → ℕ) :
    (∀ A ∈ frozE q e₁ e₂ βx t bx, A.sem w) ↔
      (∀ A ∈ frozA q e₁ e₂ βx t bx, A.sem w) ∧ StrictAnti (w ∘ posY s t k) ∧
        ∀ j, w (posA s t k (Fin.last s)) < w (posY s t k j) := by
  have hY : (∀ A ∈ ((Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).toList.map fun p =>
      Atom.ltVar (posY s t k p.1) (posY s t k p.2)), A.sem w) ↔ StrictAnti (w ∘ posY s t k) := by
    rw [List.forall_mem_map]
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, Atom.sem_ltVar]
    constructor
    · intro h i j hij
      exact h (i, j) hij
    · intro h p hp
      exact h hp
  have hL : (∀ A ∈ (List.ofFn fun j : Fin t => Atom.ltVar (posY s t k j) (posA s t k (Fin.last s))),
      A.sem w) ↔ ∀ j, w (posA s t k (Fin.last s)) < w (posY s t k j) := by
    simp only [List.forall_mem_ofFn_iff, Atom.sem_ltVar]
  unfold frozE
  rw [List.forall_mem_append, List.forall_mem_append]
  exact and_congr Iff.rfl (and_congr hY hL)

/-- The atoms number at most `3(s + 1) + 3k + t² + t + 2`. -/
theorem frozE_length (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    (frozE q e₁ e₂ βx t bx).length ≤ 3 * (s + 1) + 3 * k + t * t + t + 2 := by
  unfold frozE
  simp only [List.length_append, List.length_map, List.length_ofFn, Finset.length_toList]
  have h1 := frozA_length q e₁ e₂ βx t bx
  have h3 : (Finset.univ.filter fun p : Fin t × Fin t => p.1 < p.2).card ≤ t * t := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

/-- For `q ≥ 1`, cells with ends at most `DEN` and `e₁, e₂ ≤ DEN`, the atoms' thresholds lie in `[1, q^{L+1}]`. -/
theorem thrOK_frozE [RouteOK] {q : ℕ} (hq : 1 ≤ q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) :
    ThrOK q (frozE q e₁ e₂ βx t bx) := by
  have hL0 : 0 < L := L_pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hone : (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := ⟨le_refl 1, Real.one_le_rpow hq1 (by linarith)⟩
  unfold frozE
  refine thrOK_append (thrOK_frozA hq hβ t hb he₁ he₂) (thrOK_append ?_ ?_)
  · intro A hA
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hA
    exact hone
  · intro A hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hA
    exact hone

/-- **The injective tuples of `frozW` are those of the family of `frozE`.** -/
theorem frozW_inj_eq (q e₁ e₂ : ℕ) {s : ℕ} (βx : Fin (s + 1) → Cell) (t : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    (frozW q e₁ e₂ βx t bx).filter Function.Injective =
      (famSet (s + 1 + t + k) (N2 q) (frozE q e₁ e₂ βx t bx)).filter Function.Injective := by
  ext w
  rw [Finset.mem_filter, Finset.mem_filter, frozW_iff, mem_famSet, sem_frozE]
  constructor
  · rintro ⟨⟨hp, hA, hanti, hz⟩, hinj⟩
    refine ⟨⟨hp, hA, ?_, ?_⟩, hinj⟩
    · intro i j hij
      have hle : w (posY s t k j) ≤ w (posY s t k i) := hanti hij.le
      have hne : w (posY s t k j) ≠ w (posY s t k i) := fun h =>
        hij.ne' ((posY s t k).injective (hinj h))
      exact lt_of_le_of_ne hle hne
    · intro j
      have hne : w (posA s t k (Fin.last s)) ≠ w (posY s t k j) := fun h =>
        posA_ne_posY s t k (Fin.last s) j (hinj h)
      exact lt_of_le_of_ne (hz j) hne
  · rintro ⟨⟨hp, hA, hsy, hay⟩, hinj⟩
    exact ⟨⟨hp, hA, hsy.antitone, fun j => (hay j).le⟩, hinj⟩

/-! ### The tuples with a repeated prime -/

/-- **The numbers with a square factor weigh little in the comparison set.** For `y > 0` and `η > 0`, at a large
modulus: the `n` of `(N₁, N₂]` that the square of a prime at least `⌈x^{y/DEN}⌉` divides have weight at most
`η·x/(φ(q) log x)` in the comparison set. -/
theorem sq_small_B [RouteOK] {y : ℕ} (hy : 0 < y) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop,
      ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ ⌈Xe q y⌉₊ ≤ s ∧ s ^ 2 ∣ n), gB q n ≤
        (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  filter_upwards [big_ev, le_Xq (δ := L / DEN) (by positivity) (show 0 < η / 6 by positivity),
    le_Xq (δ := L / 2) (by positivity) (show 0 < η / 4 by positivity)] with q hbig hX1 hX2
  obtain ⟨hq2, hx3, -, -, -⟩ := big_facts hbig
  obtain ⟨-, hXe1, -⟩ := big_n hbig
  have hq0 : 0 < q := by omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  obtain ⟨z, hz⟩ : ∃ z, z = ⌈Xe q y⌉₊ := ⟨_, rfl⟩
  rw [← hz]
  have hzge : Xe q 1 ≤ z := by rw [hz]; exact (Xe_mono hx1 hy).trans (Nat.le_ceil _)
  have hz3 : (3 : ℝ) ≤ z := hXe1.trans hzge
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ z := by linarith
    exact_mod_cast this
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hN12 : N1 q ≤ N2 q := Nat.floor_le_floor (by linarith)
  have hsub : Subsingleton (ZMod 1) := inferInstanceAs (Subsingleton (Fin 1))
  have hcard := card_sq_le (q := 1) one_pos (a := 0) (isUnit_of_subsingleton 0) hN12 hz2
  have hle : (((Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n)).card : ℝ) ≤
      ((N2 q : ℝ) - N1 q) / ((z : ℝ) - 1) + Nat.sqrt (N2 q) := by
    refine le_trans ?_ (hcard.trans (le_of_eq ?_))
    · exact_mod_cast Finset.card_le_card fun n hn => by
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, Subsingleton.elim _ _, hn.2⟩
    · simp
  have hNN : (N2 q : ℝ) - N1 q ≤ 2 * xq q := by
    have h1 : (N2 q : ℝ) ≤ 2 * xq q := Nat.floor_le (by positivity)
    have h2 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hzm : (2 / 3 : ℝ) * Xe q 1 ≤ (z : ℝ) - 1 := by linarith
  have hzm0 : (0 : ℝ) < (z : ℝ) - 1 := by linarith
  have ht1 : ((N2 q : ℝ) - N1 q) / ((z : ℝ) - 1) ≤ 3 * (q : ℝ) ^ (L - L / DEN) := by
    rw [div_le_iff₀ hzm0]
    have hpow : (q : ℝ) ^ (L - L / DEN) * Xe q 1 = xq q := by
      unfold Xe
      rw [Nat.cast_one, xpow, ← Real.rpow_add hq']
      congr 1
      ring
    have hp0 : 0 ≤ (q : ℝ) ^ (L - L / DEN) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hzm hp0
    nlinarith
  have ht2 : (Nat.sqrt (N2 q) : ℝ) ≤ 2 * (q : ℝ) ^ (L - L / 2) := by
    have h1 : ((Nat.sqrt (N2 q) : ℕ) : ℝ) ^ 2 ≤ (N2 q : ℝ) := by exact_mod_cast Nat.sqrt_le' (N2 q)
    have h2 : (N2 q : ℝ) ≤ 2 * xq q := Nat.floor_le (by positivity)
    have h3 : ((q : ℝ) ^ (L - L / 2)) ^ 2 = xq q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq'.le]
      congr 1
      push_cast
      ring
    have h4 : ((Nat.sqrt (N2 q) : ℕ) : ℝ) ^ 2 ≤ (2 * (q : ℝ) ^ (L - L / 2)) ^ 2 := by
      rw [mul_pow, h3]
      linarith
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 h4
  have hfin : ((N2 q : ℝ) - N1 q) / ((z : ℝ) - 1) + Nat.sqrt (N2 q) ≤ η * Xq q := by linarith
  calc ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n), gB q n
      ≤ ∑ _n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n),
          (q.totient : ℝ)⁻¹ := Finset.sum_le_sum fun n _ => SieveDrop.gB_le q n
    _ = (q.totient : ℝ)⁻¹ *
          (((Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (q.totient : ℝ)⁻¹ * (((N2 q : ℝ) - N1 q) / ((z : ℝ) - 1) + Nat.sqrt (N2 q)) :=
        mul_le_mul_of_nonneg_left hle hφ0
    _ ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := mul_le_mul_of_nonneg_left hfin hφ0

/-- **The tuples with a repeated prime weigh at most the numbers with a square factor.** At a modulus as in `Big`,
for `0 < f` at most the lower ends of the last cell of `βx` and of the cells of the chain: the tuples of `frozW`
that are not injective contribute at most `(DEN + 1)^K`, `K` their length, times the weight in the two sets of the
`n` that the square of a prime at least `⌈x^{f/DEN}⌉` divides. -/
theorem frozW_noninj_le [RouteOK] {q : ℕ} (hq : Big q) (a : ZMod q) {f : ℕ} (hf : 0 < f) {e₁ e₂ s : ℕ}
    {βx : Fin (s + 1) → Cell} (hβf : f ≤ (βx (Fin.last s)).1) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hbf : ∀ j, f ≤ (bx j).1) :
    |∑ w ∈ (frozW q e₁ e₂ βx t bx).filter (fun w => ¬ Function.Injective w), ∑ n ∈ Ioc (N1 q) (N2 q),
        (gA q a n - gB q n) * (if prodR w ∣ n ∧ SieveTree.rough ⌈Xe q f⌉₊ n then 1 else 0)| ≤
      (((DEN + 1) ^ (s + 1 + t + k) : ℕ) : ℝ) *
        ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ p : ℕ, p.Prime ∧ ⌈Xe q f⌉₊ ≤ p ∧ p ^ 2 ∣ n),
          (gA q a n + gB q n) := by
  obtain ⟨hx3, hXe1, hn⟩ := big_n hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = ⌈Xe q f⌉₊ := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨NI, hNI⟩ : ∃ NI : Finset (Fin (s + 1 + t + k) → ℕ),
      NI = (frozW q e₁ e₂ βx t bx).filter (fun w => ¬ Function.Injective w) := ⟨_, rfl⟩
  rw [← hNI]
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = (DEN + 1) ^ (s + 1 + t + k) := ⟨_, rfl⟩
  rw [← hC]
  have hgA : ∀ n, 0 ≤ gA q a n := gA_nonneg q a
  have hgB : ∀ n, 0 ≤ gB q n := SieveDrop.gB_nonneg q
  have hXf : Xe q 1 ≤ Xe q f := Xe_mono hx1 hf
  have hcount : ∀ n ∈ Ioc (N1 q) (N2 q),
      ((NI.filter fun w => prodR w ∣ n ∧ SieveTree.rough Z n).card : ℝ) ≤
        if (∃ p : ℕ, p.Prime ∧ Z ≤ p ∧ p ^ 2 ∣ n) then (C : ℝ) else 0 := by
    intro n hn'
    obtain ⟨hnx, hnX⟩ := hn n hn'
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := by linarith
      exact_mod_cast this
    by_cases hsq : ∃ p : ℕ, p.Prime ∧ Z ≤ p ∧ p ^ 2 ∣ n
    · rw [ite_eq_left hsq]
      have hP1 : 1 < Xe q f := by linarith
      have hnP : (n : ℝ) < Xe q f ^ (DEN + 1) := by
        have h1 : Xe q 1 ^ (DEN + 1) = Xe q (DEN + 1) := Xe_pow hx0 (DEN + 1)
        have h2 : Xe q 1 ^ (DEN + 1) ≤ Xe q f ^ (DEN + 1) := pow_le_pow_left₀ (Xe_pos hx0 1).le hXf _
        linarith
      have hcard := card_tuples_dvd_le (NI.filter fun w => prodR w ∣ n ∧ SieveTree.rough Z n) hn0 hP1 hnP
        (fun w hw i => by
          rw [Finset.mem_filter, hNI, Finset.mem_filter] at hw
          obtain ⟨⟨hwW, -⟩, hd, -⟩ := hw
          exact ⟨((mem_frozW.1 hwW).1 i).2, frozW_ge hx1 hβf hbf hwW i,
            (Finset.dvd_prod_of_mem w (Finset.mem_univ i)).trans hd⟩)
      rw [hC]
      exact_mod_cast hcard
    · rw [ite_eq_right hsq]
      have hemp : (NI.filter fun w => prodR w ∣ n ∧ SieveTree.rough Z n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hw hcond
        rw [hNI, Finset.mem_filter] at hw
        obtain ⟨i, hi⟩ := sq_dvd_prodR hw.2
        refine hsq ⟨w i, ((mem_frozW.1 hw.1).1 i).2, ?_, hi.trans hcond.1⟩
        rw [hZ]
        exact Nat.ceil_le.2 (frozW_ge hx1 hβf hbf hw.1 i)
      rw [hemp, Finset.card_empty, Nat.cast_zero]
  calc |∑ w ∈ NI, ∑ n ∈ Ioc (N1 q) (N2 q),
        (gA q a n - gB q n) * (if prodR w ∣ n ∧ SieveTree.rough Z n then 1 else 0)|
      ≤ ∑ w ∈ NI, ∑ n ∈ Ioc (N1 q) (N2 q),
          (gA q a n + gB q n) * (if prodR w ∣ n ∧ SieveTree.rough Z n then 1 else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        have h1 : |gA q a n - gB q n| ≤ gA q a n + gB q n :=
          abs_le.2 ⟨by linarith [hgA n, hgB n], by linarith [hgA n, hgB n]⟩
        have h0 : (0 : ℝ) ≤ (if prodR w ∣ n ∧ SieveTree.rough Z n then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        rw [abs_mul, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right h1 h0
    _ = ∑ n ∈ Ioc (N1 q) (N2 q),
          (gA q a n + gB q n) * ((NI.filter fun w => prodR w ∣ n ∧ SieveTree.rough Z n).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum]
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ ≤ ∑ n ∈ Ioc (N1 q) (N2 q),
          (gA q a n + gB q n) * (if (∃ p : ℕ, p.Prime ∧ Z ≤ p ∧ p ^ 2 ∣ n) then (C : ℝ) else 0) :=
        Finset.sum_le_sum fun n hn' =>
          mul_le_mul_of_nonneg_left (hcount n hn') (by linarith [hgA n, hgB n])
    _ = (C : ℝ) * ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ p : ℕ, p.Prime ∧ Z ≤ p ∧ p ^ 2 ∣ n),
          (gA q a n + gB q n) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> ring

/-! ### The terms are evaluated when the family's are -/

/-- **The terms at a floor over the frozen part with a cofactor of `t` primes are evaluated when those of the
family of tuples of distinct primes are.** For `0 < f` at most the lower ends of the last cell of `βx` and of the
cells of the chain: if the terms at the floor `x^{f/DEN}` of the injective tuples of the family of `frozE`, in
`𝒜` minus the comparison set, are evaluated, so are the terms at the floor of the chain's box over `frozP … t`. -/
theorem evJF_frozP [RouteOK] {f : ℕ} (hf : 0 < f) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβf : f ≤ (βx (Fin.last s)).1) (t : ℕ) {k : ℕ} {bx : Fin k → Cell} (hbf : ∀ j, f ≤ (bx j).1)
    (hfam : ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (N2 q) (frozE q e₁ e₂ βx t bx)).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (N2 q) (frozE q e₁ e₂ βx t bx)).filter Function.Injective)| ≤
        (q.totient : ℝ)⁻¹ * (η * Xq q)) :
    EvJF (fun q => frozP q e₁ e₂ βx t) prodR f bx := by
  intro η hη
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (((DEN + 1) ^ (s + 1 + t + k) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hC]
    exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos DEN)
  have hC0 : 0 < C := by linarith
  have hD1 : (1 : ℝ) ≤ ((DEN + 1 : ℕ) : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ ((DEN + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos DEN
    exact one_le_pow₀ this
  filter_upwards [hfam (η / 2) (by positivity), sq_small hf (show 0 < η / (4 * C) by positivity),
    sq_small_B hf (show 0 < η / (4 * C) by positivity), big_ev] with q h1 h2 h3 hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  have hx1 : 1 ≤ xq q := by linarith
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  show |dJF q a f (frozP q e₁ e₂ βx t) prodR bx| ≤ _
  rw [dJF_frozP_eq hx1 a hβf t bx,
    ← Finset.sum_filter_add_sum_filter_not (frozW q e₁ e₂ βx t bx) Function.Injective]
  have hinj : ∑ w ∈ (frozW q e₁ e₂ βx t bx).filter Function.Injective, ∑ n ∈ Ioc (N1 q) (N2 q),
      (gA q a n - gB q n) * (if prodR w ∣ n ∧ SieveTree.rough ⌈Xe q f⌉₊ n then 1 else 0) =
      famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (N2 q) (frozE q e₁ e₂ βx t bx)).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (N2 q) (frozE q e₁ e₂ βx t bx)).filter Function.Injective) := by
    rw [frozW_inj_eq]
    unfold famJ
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    show (gA q a n - gB q n) *
      (if (∏ i, w i) ∣ n ∧ SieveTree.rough ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ n then 1 else 0) = _
    ring
  rw [hinj]
  have hni := frozW_noninj_le hbig a hf hβf t hbf (e₁ := e₁) (e₂ := e₂)
  have hA := h2 a ha
  have hsA : 0 ≤ ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ p : ℕ, p.Prime ∧ ⌈Xe q f⌉₊ ≤ p ∧ p ^ 2 ∣ n),
      gA q a n := Finset.sum_nonneg fun n _ => gA_nonneg q a n
  have hA' : ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ p : ℕ, p.Prime ∧ ⌈Xe q f⌉₊ ≤ p ∧ p ^ 2 ∣ n),
      gA q a n ≤ (q.totient : ℝ)⁻¹ * (η / (4 * C) * Xq q) := by
    refine le_trans ?_ hA
    nlinarith
  have hsum : ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ p : ℕ, p.Prime ∧ ⌈Xe q f⌉₊ ≤ p ∧ p ^ 2 ∣ n),
      (gA q a n + gB q n) ≤ 2 * ((q.totient : ℝ)⁻¹ * (η / (4 * C) * Xq q)) := by
    rw [Finset.sum_add_distrib]
    linarith
  have hfin : C * (2 * ((q.totient : ℝ)⁻¹ * (η / (4 * C) * Xq q))) = (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by
    field_simp
    ring
  rw [← hC] at hni
  have hni' := hni.trans (mul_le_mul_of_nonneg_left hsum hC0.le)
  rw [hfin] at hni'
  have hJ := h1 a ha
  refine (abs_add_le _ _).trans ?_
  have e : (q.totient : ℝ)⁻¹ * (η * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by ring
  rw [e]
  exact add_le_add hJ hni'

omit [Route] in
/-- **The terms at a floor over the frozen part with a cofactor of `t` primes are evaluated when the family's
are, for any route**: `evJF_frozP` with the route as a variable. -/
theorem evJF_frozP_at (Rt : Route) (hRt : @RouteOK Rt) {f : ℕ} (hf : 0 < f) {e₁ e₂ s : ℕ}
    {βx : Fin (s + 1) → Cell} (hβf : f ≤ (βx (Fin.last s)).1) (t : ℕ) {k : ℕ} {bx : Fin k → Cell}
    (hbf : ∀ j, f ≤ (bx j).1)
    (hfam : ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (@N2 Rt q) (@frozE Rt q e₁ e₂ s βx t k bx)).filter Function.Injective) -
        famJ (gB q) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet (s + 1 + t + k) (@N2 Rt q) (@frozE Rt q e₁ e₂ s βx t k bx)).filter Function.Injective)| ≤
        (q.totient : ℝ)⁻¹ * (η * @Xq Rt q)) :
    @EvJF Rt _ (fun q => @frozP Rt q e₁ e₂ s βx t) prodR f k bx :=
  @evJF_frozP Rt hRt f hf e₁ e₂ s βx hβf t k bx hbf hfam

end SieveAd

#print axioms SieveAd.evJF_frozP_at
