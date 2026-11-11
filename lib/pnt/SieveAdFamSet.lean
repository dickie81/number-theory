/-
# The terms at a floor of a family of tuples of distinct primes, in any order

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The comparisons evaluate the terms at a floor of a box of cells, a family of strictly
decreasing tuples, under a few more atoms (`SieveAd.dJP`). The tuples of a reversed term are cut out by atoms
alone, with no order between the primes of `r'` and those of the chain, and some of their primes (the cofactor's)
have no cell. Such a family is still a union of boxes: each of its tuples of distinct primes lies in the box of
the cells of side `1/DEN` that hold its primes, in the one order in which it decreases. So its terms at a floor
are evaluated as soon as each of those boxes is.

* `Atom.emb ι`: the atom carried along an embedding `ι` of the indices: it says of `w` what the atom says of
  `w ∘ ι` (`Atom.emb_sem`), with the same threshold (`Atom.emb_thr`). `Atom.perm σ`: by a permutation: it says of
  `z` what the atom says of `z ∘ σ⁻¹` (`Atom.perm_sem`, `Atom.perm_thr`).
* `ucell q p`: the cell of side `1/DEN` of a number `p`: the greatest `v ≤ DEN` with `x^{v/DEN} ≤ p`
  (`ucell_spec`, `ucell_eq`, `le_ucell`). `ubox v`: the box of the cells `(v_i, v_i + 1)`.
* `ucell_sum_le`, `le_ucell_sum`: numbers whose product over a set of indices lies in `[x^{lo/DEN}, x^{hi/DEN}]`
  have cells whose lower ends sum to at most `hi` and whose upper ends sum to at least `lo` (`Xe_sum`,
  `Xe_le_iff`).
* `famJ_famSet_inj`: **the terms at a floor of the injective tuples of a family of atoms**, in `𝒜` minus the
  comparison set, are the sum over the boxes `ubox v` and the permutations `σ` of the terms of the box
  `ubox v ∘ σ` under the atoms carried by `σ`.
* `evJ_famSet`: **so they are evaluated** when, for a property `Good` of boxes under which the terms at the floor
  are evaluated under `m` atoms, every injective tuple `w` of the family has its box `ubox (ucell ∘ w) ∘ σ` good,
  `σ` its order; `evJ_famSet_at` with the route as a variable.

The file imports `SieveAdSort.lean` and `SieveAdRevLemma.lean`.
-/
import SieveAdSort
import SieveAdRevLemma

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveDecomp.Atom

variable {k : ℕ}

/-- The atom carried along an embedding of the indices: it says of `w` what the atom says of `w ∘ ι`. -/
def emb {K : ℕ} (ι : Fin k ↪ Fin K) : Atom k → Atom K
  | ge t b => ge (ι t) b
  | lt t b => lt (ι t) b
  | ltVar s t => ltVar (ι s) (ι t)
  | prodLe T b => prodLe (T.map ι) b
  | prodGt T b => prodGt (T.map ι) b

theorem emb_sem {K : ℕ} (ι : Fin k ↪ Fin K) (A : Atom k) (w : Fin K → ℕ) : (A.emb ι).sem w ↔ A.sem (w ∘ ι) := by
  cases A <;> simp [emb, sem, Finset.prod_map]

theorem emb_thr {K : ℕ} (ι : Fin k ↪ Fin K) (A : Atom k) : (A.emb ι).thr = A.thr := by
  cases A <;> rfl

/-- The atom carried by a permutation of the indices: it says of `z` what the atom says of `z ∘ σ⁻¹`. -/
def perm (σ : Equiv.Perm (Fin k)) (A : Atom k) : Atom k := A.emb σ.symm.toEmbedding

theorem perm_sem (σ : Equiv.Perm (Fin k)) (A : Atom k) (z : Fin k → ℕ) :
    (A.perm σ).sem z ↔ A.sem (z ∘ σ.symm) := emb_sem σ.symm.toEmbedding A z

theorem perm_thr (σ : Equiv.Perm (Fin k)) (A : Atom k) : (A.perm σ).thr = A.thr := emb_thr _ A

end SieveDecomp.Atom

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

variable [Route]

/-! ### The cells of side `1/DEN` -/

/-- The cell of side `1/DEN` of a number: the greatest `v ≤ DEN` with `x^{v/DEN} ≤ p`. -/
noncomputable def ucell (q p : ℕ) : ℕ := Nat.findGreatest (fun v => Xe q v ≤ (p : ℝ)) DEN

/-- For `1 ≤ p < x`: `x^{v/DEN} ≤ p < x^{(v+1)/DEN}` at `v = ucell q p`, and `v < DEN`. -/
theorem ucell_spec {q p : ℕ} (hp1 : 1 ≤ p) (hp : (p : ℝ) < Xe q DEN) :
    Xe q (ucell q p) ≤ p ∧ (p : ℝ) < Xe q (ucell q p + 1) ∧ ucell q p < DEN := by
  have h0 : Xe q 0 ≤ (p : ℝ) := by
    unfold Xe
    rw [Nat.cast_zero, zero_div, Real.rpow_zero]
    exact_mod_cast hp1
  have hs : Xe q (ucell q p) ≤ (p : ℝ) :=
    Nat.findGreatest_spec (P := fun v => Xe q v ≤ (p : ℝ)) (Nat.zero_le DEN) h0
  have hle : ucell q p ≤ DEN := Nat.findGreatest_le DEN
  have hlt : ucell q p < DEN := by
    rcases Nat.lt_or_ge (ucell q p) DEN with h | h
    · exact h
    · have e : ucell q p = DEN := le_antisymm hle h
      rw [e] at hs
      linarith
  refine ⟨hs, ?_, hlt⟩
  by_contra hge
  rw [not_lt] at hge
  exact Nat.findGreatest_is_greatest (P := fun v => Xe q v ≤ (p : ℝ)) (Nat.lt_succ_self _) hlt hge

/-- A number of the cell `(v, v + 1)`, `v < DEN`, has `ucell q p = v`. -/
theorem ucell_eq {q p v : ℕ} (hx1 : 1 ≤ xq q) (h1 : Xe q v ≤ p) (h2 : (p : ℝ) < Xe q (v + 1)) (hv : v < DEN) :
    ucell q p = v := by
  have hx0 : 0 < xq q := by linarith
  have hp1 : 1 ≤ p := by
    have h : (1 : ℝ) ≤ p := le_trans (Real.one_le_rpow hx1 (by positivity)) h1
    exact_mod_cast h
  have hp : (p : ℝ) < Xe q DEN := lt_of_lt_of_le h2 (Xe_mono hx1 hv)
  obtain ⟨s1, s2, -⟩ := ucell_spec hp1 hp
  rcases Nat.lt_trichotomy (ucell q p) v with h | h | h
  · have := Xe_mono hx1 (show ucell q p + 1 ≤ v from h)
    linarith
  · exact h
  · have := Xe_mono hx1 (show v + 1 ≤ ucell q p from h)
    linarith

/-- A number at least `x^{f/DEN}`, `f ≤ DEN`, has `f ≤ ucell q p`. -/
theorem le_ucell {q p f : ℕ} (hf : f ≤ DEN) (h : Xe q f ≤ p) : f ≤ ucell q p :=
  Nat.le_findGreatest (P := fun v => Xe q v ≤ (p : ℝ)) hf h

/-- `x^{·/DEN}` at a sum of exponents is the product. -/
theorem Xe_sum {q : ℕ} (hx0 : 0 < xq q) {ι : Type} (S : Finset ι) (v : ι → ℕ) :
    Xe q (∑ j ∈ S, v j) = ∏ j ∈ S, Xe q (v j) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, Xe_zero]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, Xe_add hx0, ih]

/-- For `x > 1`, `x^{a/DEN} ≤ x^{b/DEN}` exactly when `a ≤ b`. -/
theorem Xe_le_iff {q : ℕ} (hx1 : 1 < xq q) {a b : ℕ} : Xe q a ≤ Xe q b ↔ a ≤ b := by
  unfold Xe
  rw [Real.rpow_le_rpow_left_iff hx1, div_le_div_iff_of_pos_right DEN_pos']
  exact Nat.cast_le

/-- Numbers of `[1, x)` whose product over a set is at most `x^{hi/DEN}` have cells of side `1/DEN` with lower
ends of sum at most `hi`. -/
theorem ucell_sum_le {q : ℕ} (hx1 : 1 < xq q) {k : ℕ} {w : Fin k → ℕ} (S : Finset (Fin k))
    (hw : ∀ i ∈ S, 1 ≤ w i ∧ (w i : ℝ) < Xe q DEN) {hi : ℕ} (h : ∏ i ∈ S, (w i : ℝ) ≤ Xe q hi) :
    ∑ i ∈ S, ucell q (w i) ≤ hi := by
  have hx0 : 0 < xq q := by linarith
  rw [← Xe_le_iff hx1, Xe_sum hx0]
  refine le_trans (Finset.prod_le_prod₀ (fun i _ => (Xe_pos hx0 _).le) fun i hi' => ?_) h
  exact (ucell_spec (hw i hi').1 (hw i hi').2).1

/-- Numbers of `[1, x)` whose product over a set is at least `x^{lo/DEN}` have cells of side `1/DEN` with upper
ends of sum at least `lo`. -/
theorem le_ucell_sum {q : ℕ} (hx1 : 1 < xq q) {k : ℕ} {w : Fin k → ℕ} (S : Finset (Fin k))
    (hw : ∀ i ∈ S, 1 ≤ w i ∧ (w i : ℝ) < Xe q DEN) {lo : ℕ} (h : Xe q lo ≤ ∏ i ∈ S, (w i : ℝ)) :
    lo ≤ ∑ i ∈ S, (ucell q (w i) + 1) := by
  have hx0 : 0 < xq q := by linarith
  rw [← Xe_le_iff hx1, Xe_sum hx0]
  refine le_trans h (Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i hi' => ?_)
  exact (ucell_spec (hw i hi').1 (hw i hi').2).2.1.le

/-- The box of the cells `(v_i, v_i + 1)`. -/
def ubox {k : ℕ} (v : Fin k → ℕ) : Fin k → Cell := fun i => (v i, v i + 1)

/-! ### The terms at a floor of the injective tuples of a family -/

/-- **The terms at a floor of the injective tuples of a family of atoms**, in `𝒜` minus the comparison set: the sum
over the boxes of cells of side `1/DEN` and the permutations `σ` of the terms of the box `ubox v ∘ σ` under the
atoms carried by `σ`, when every injective tuple of the family has its entries below `x`. -/
theorem famJ_famSet_inj {q : ℕ} (hx1 : 1 ≤ xq q) (a : ZMod q) (f : ℕ) {k : ℕ} (E : List (Atom k))
    (hlt : ∀ w ∈ famSet k (N2 q) E, Function.Injective w → ∀ i, (w i : ℝ) < Xe q DEN) :
    famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ((famSet k (N2 q) E).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ((famSet k (N2 q) E).filter Function.Injective) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.range DEN), ∑ σ : Equiv.Perm (Fin k),
        dJP q a f (ubox v ∘ σ) (fun z => ∀ A ∈ E.map (Atom.perm σ), A.sem z) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : (Fin k → ℕ) → ℝ, Φ = fun w => ∑ n ∈ Ioc (N1 q) (N2 q),
      (gA q a n - gB q n) * (if (∏ i, w i) ∣ n ∧ SieveTree.rough Z n then 1 else 0) := ⟨_, rfl⟩
  have hΦ : ∀ F : Finset (Fin k → ℕ),
      famJ (gA q a) (N1 q) (N2 q) Z F - famJ (gB q) (N1 q) (N2 q) Z F = ∑ w ∈ F, Φ w := by
    intro F
    unfold famJ
    rw [← Finset.sum_sub_distrib, hΦdef]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hΦ]
  have hmaps : ∀ w ∈ (famSet k (N2 q) E).filter Function.Injective,
      (fun i => ucell q (w i)) ∈ Fintype.piFinset (fun _ : Fin k => Finset.range DEN) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact (ucell_spec ((mem_famSet.1 hw.1).1 i).2.one_lt.le (hlt w hw.1 hw.2 i)).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps Φ]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Fintype.mem_piFinset] at hv
  obtain ⟨P, hP⟩ : ∃ P : (Fin k → ℕ) → Prop, ∀ w, P w ↔ ∀ A ∈ E, A.sem w := ⟨_, fun _ => Iff.rfl⟩
  have hset : ((famSet k (N2 q) E).filter Function.Injective).filter (fun w => (fun i => ucell q (w i)) = v) =
      (famU q (ubox v)).filter P := by
    ext w
    simp only [Finset.mem_filter, mem_famSet, mem_famU, hP]
    constructor
    · rintro ⟨⟨⟨hp, hE⟩, hinj⟩, hu⟩
      refine ⟨⟨hp, hinj, fun i => ?_⟩, hE⟩
      obtain ⟨s1, s2, -⟩ := ucell_spec (hp i).2.one_lt.le
        (hlt w (mem_famSet.2 ⟨hp, hE⟩) hinj i)
      have hui : ucell q (w i) = v i := congrFun hu i
      rw [hui] at s1 s2
      refine ⟨s1, ?_⟩
      have e : (((ubox v i).2 : ℕ) : ℝ) = ((v i + 1 : ℕ) : ℝ) := rfl
      rw [e]
      exact s2
    · rintro ⟨⟨hp, hinj, hc⟩, hE⟩
      refine ⟨⟨⟨hp, hE⟩, hinj⟩, ?_⟩
      funext i
      exact ucell_eq hx1 (hc i).1 (hc i).2 (Finset.mem_range.1 (hv i))
  rw [hset, sum_famU_eq q (ubox v) P Φ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [dJP_congr (P' := fun z => P (z ∘ σ.symm)) fun z _ => by
    simp only [List.forall_mem_map, Atom.perm_sem, hP]]
  unfold dJP
  rw [← hZ, hΦ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hΦdef]
  simp only [Function.comp_apply]
  rw [Equiv.prod_comp σ.symm z]

/-! ### They are evaluated when their boxes are -/

/-- A box none of whose tuples satisfies the condition has no term at a floor under it. -/
theorem dJP_empty {q : ℕ} {a : ZMod q} {f k : ℕ} {bx : Fin k → Cell} {P : (Fin k → ℕ) → Prop}
    (h : ∀ z ∈ famB q bx, ¬ P z) : dJP q a f bx P = 0 := by
  unfold dJP
  rw [Finset.filter_eq_empty_iff.2 h]
  simp [famJ]

/-- **The terms at a floor of a family of tuples of distinct primes are evaluated when its boxes are.** Let
`Good` be a property of boxes under which the terms at the floor `x^{f/DEN}` are evaluated under `m` more atoms,
uniformly in the atoms. For a family of at most `m` atoms `E q` with thresholds as in `ThrOK`: if at a large
modulus every injective tuple `w` of the family has its entries below `x` and, `σ` being the order in which it
decreases, the box `ubox (ucell ∘ w) ∘ σ` good, then the terms at the floor of the injective tuples of the family
are evaluated. -/
theorem evJ_famSet [RouteOK] {k : ℕ} (f : ℕ) {m : ℕ} (Good : (Fin k → Cell) → Prop)
    (hGood : ∀ bx, Good bx → ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      ∀ E : List (Atom k), E.length ≤ m → ThrOK q E →
        |dJP q a f bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q))
    (E : ℕ → List (Atom k)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, ThrOK q (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet k (N2 q) (E q), Function.Injective w →
      (∀ i, (w i : ℝ) < Xe q DEN) ∧
        ∀ σ : Equiv.Perm (Fin k), StrictAnti (w ∘ σ) → Good (ubox (fun i => ucell q (w i)) ∘ σ)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet k (N2 q) (E q)).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet k (N2 q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  intro η hη
  obtain ⟨V, hV⟩ : ∃ V : Finset (Fin k → ℕ), V = Fintype.piFinset (fun _ : Fin k => Finset.range DEN) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((V.card * (Finset.univ : Finset (Equiv.Perm (Fin k))).card + 1 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hall : ∀ᶠ q : ℕ in atTop, ∀ p ∈ V ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k))),
      Good (ubox p.1 ∘ p.2) → ∀ a : ZMod q, IsUnit a → ∀ E' : List (Atom k), E'.length ≤ m → ThrOK q E' →
        |dJP q a f (ubox p.1 ∘ p.2) (fun rt => ∀ A ∈ E', A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η / N * Xq q) := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hG : Good (ubox p.1 ∘ p.2)
    · filter_upwards [hGood _ hG (η / N) (by positivity)] with q hq _
      exact hq
    · exact Filter.Eventually.of_forall fun q h => absurd h hG
  filter_upwards [hall, hEt, hfam, big_ev] with q hq hthr hfq hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  have hx1 : 1 ≤ xq q := by linarith
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  rw [famJ_famSet_inj hx1 a f (E q) fun w hw hinj => (hfq w hw hinj).1, ← hV]
  have hterm : ∀ v ∈ V, ∀ σ : Equiv.Perm (Fin k),
      |dJP q a f (ubox v ∘ σ) (fun z => ∀ A ∈ (E q).map (Atom.perm σ), A.sem z)| ≤
        (q.totient : ℝ)⁻¹ * (η / N * Xq q) := by
    intro v hv σ
    by_cases hne : ∃ z ∈ famB q (ubox v ∘ σ), ∀ A ∈ (E q).map (Atom.perm σ), A.sem z
    · obtain ⟨z, hzB, hzE⟩ := hne
      obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hzB
      have hwE : ∀ A ∈ E q, A.sem (z ∘ σ.symm) := by
        intro A hA
        exact (Atom.perm_sem σ A z).1 (hzE _ (List.mem_map_of_mem hA))
      have hwmem : z ∘ σ.symm ∈ famSet k (N2 q) (E q) := mem_famSet.2 ⟨fun i => hp (σ.symm i), hwE⟩
      have hwinj : Function.Injective (z ∘ σ.symm) := hsa.injective.comp σ.symm.injective
      have hzeq : (z ∘ σ.symm) ∘ σ = z := by
        funext i
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
      have hG := (hfq _ hwmem hwinj).2 σ (by rw [hzeq]; exact hsa)
      have hvv : (fun i => ucell q ((z ∘ σ.symm) i)) = v := by
        funext i
        rw [hV, Fintype.mem_piFinset] at hv
        have hci := hc (σ.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply, ubox] at hci
        exact ucell_eq hx1 hci.1 hci.2 (Finset.mem_range.1 (hv i))
      rw [hvv] at hG
      refine hq (v, σ) (Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩) hG a ha _
        (by rw [List.length_map]; exact hEl q) ?_
      intro A' hA'
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
      rw [Atom.perm_thr]
      exact hthr A hA
    · rw [dJP_empty fun z hz h => hne ⟨z, hz, h⟩, abs_zero]
      exact mul_nonneg hφ (mul_nonneg (div_pos hη hN0).le hX.le)
  calc |∑ v ∈ V, ∑ σ : Equiv.Perm (Fin k),
        dJP q a f (ubox v ∘ σ) (fun z => ∀ A ∈ (E q).map (Atom.perm σ), A.sem z)|
      ≤ ∑ v ∈ V, ∑ σ : Equiv.Perm (Fin k),
        |dJP q a f (ubox v ∘ σ) (fun z => ∀ A ∈ (E q).map (Atom.perm σ), A.sem z)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ v ∈ V, ∑ _σ : Equiv.Perm (Fin k), (q.totient : ℝ)⁻¹ * (η / N * Xq q) :=
        Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun σ _ => hterm v hv σ
    _ = ((V.card * (Finset.univ : Finset (Equiv.Perm (Fin k))).card : ℕ) : ℝ) *
          ((q.totient : ℝ)⁻¹ * (η / N * Xq q)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ N * ((q.totient : ℝ)⁻¹ * (η / N * Xq q)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hφ (mul_nonneg (div_pos hη hN0).le hX.le))
        rw [hN]
        push_cast
        linarith
    _ = (q.totient : ℝ)⁻¹ * (η * Xq q) := by
        field_simp

omit [Route] in
/-- **The terms at a floor of a family of tuples of distinct primes are evaluated when its boxes are, for any
route**: `evJ_famSet` with the route as a variable. -/
theorem evJ_famSet_at (Rt : Route) (hRt : @RouteOK Rt) {k : ℕ} (f : ℕ) {m : ℕ} (Good : (Fin k → Cell) → Prop)
    (hGood : ∀ bx, Good bx → ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      ∀ E : List (Atom k), E.length ≤ m → @ThrOK Rt q k E →
        |@dJP Rt q a f k bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q))
    (E : ℕ → List (Atom k)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, @ThrOK Rt q k (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet k (@N2 Rt q) (E q), Function.Injective w →
      (∀ i, (w i : ℝ) < @Xe Rt q DEN) ∧
        ∀ σ : Equiv.Perm (Fin k), StrictAnti (w ∘ σ) → Good (ubox (fun i => @ucell Rt q (w i)) ∘ σ)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet k (@N2 Rt q) (E q)).filter Function.Injective) -
        famJ (gB q) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet k (@N2 Rt q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q) :=
  @evJ_famSet Rt hRt k f m Good hGood E hEl hEt hfam

end SieveAd

#print axioms SieveAd.evJ_famSet_at
