/-
# The two comparisons at a floor over the frozen part, on the cells and the slab

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A tuple `(a, y, c)` of a term at a floor over the frozen part has `a` in the cells of `βx`, `c`
in the chain's cells and `∏a·∏y` in the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`; the cofactor's primes `y` have no cells.
A set of the tuple's indices made of some of `a`, all of `y` or none, and some of `c` still has its product
between two powers of `x` that the cells and the slab give: the cofactor's primes together are the slab over the
rest of `a`. So the comparisons for families (`SieveAdFamCore.lean`) apply, with the sets of indices given by
their parts.

* `roleSet s t k A my C`: the positions of the set `A` of `a`, of all of `y` if `my`, and of the set `C` of `c`
  (`mem_roleSet_A`, `mem_roleSet_Y`, `mem_roleSet_C`, `roleSet_cover`, `roleSet_disjoint`, `prod_roleSet`).
* `loRole`, `hiRole`: the exponents: without the cofactor the sums of the lower and upper ends; with it
  `e₁ − Σ_{a ∉ A} hi + Σ_C lo` and `e₂ − Σ_{a ∉ A} lo + Σ_C hi`. `role_bounds`: **the product of a tuple of the
  family over a role set lies in `[x^{loRole/DEN}, x^{hiRole/DEN}]`**.
* `frozW_lt`: every prime of a tuple of `frozW` is below `x`.
* `evJF_froz_fill`: **the comparison with the rest among the tree's primes evaluates the terms at a floor over
  the frozen part**, when the exponents of the role sets pass `coreJ3` with `Kb ≥ s + 1 + T + k` cells of room.
  `evJF_froz_two`: **the comparison with the rest among the tuple's primes**, with a role set for the rest and
  `coreJ2`. `evJF_froz_fill_at`, `evJF_froz_two_at`: with the route and its exponent as variables.

The file imports `SieveAdFrozJ.lean` and `SieveAdFamCore.lean`.
-/
import SieveAdFrozJ
import SieveAdFamCore

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### Products of numbers at least `1` -/

theorem one_le_prod_cast {ι : Type} (S : Finset ι) (g : ι → ℕ) (hg : ∀ i, 1 ≤ g i) :
    (1 : ℝ) ≤ ∏ i ∈ S, (g i : ℝ) := by
  have h : ∏ _i ∈ S, (1 : ℝ) ≤ ∏ i ∈ S, (g i : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by exact_mod_cast hg i
  rwa [Finset.prod_const_one] at h

theorem prod_cast_le_of_subset {ι : Type} {S T : Finset ι} (h : S ⊆ T) (g : ι → ℕ) (hg : ∀ i, 1 ≤ g i) :
    ∏ i ∈ S, (g i : ℝ) ≤ ∏ i ∈ T, (g i : ℝ) := by
  rw [← Finset.prod_sdiff h]
  exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) (one_le_prod_cast _ g hg)

/-! ### Sets of indices by their parts -/

/-- The positions of a set of the box's part, of the cofactor's primes or not, and of a set of the chain. -/
def roleSet (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k)) :
    Finset (Fin (s + 1 + t + k)) :=
  A.map (posA s t k) ∪ (cond my (Finset.univ.map (posY s t k)) ∅ ∪ C.map (posC s t k))

theorem mem_roleSet_A (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k)) (i : Fin (s + 1)) :
    posA s t k i ∈ roleSet s t k A my C ↔ i ∈ A := by
  unfold roleSet
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · rintro (h | h | h)
    · obtain ⟨a, ha, h'⟩ := Finset.mem_map.1 h
      rwa [← (posA s t k).injective h']
    · cases my
      · simp at h
      · obtain ⟨j, -, h'⟩ := Finset.mem_map.1 h
        exact absurd h'.symm (posA_ne_posY s t k i j)
    · obtain ⟨j, -, h'⟩ := Finset.mem_map.1 h
      exact absurd h'.symm (posA_ne_posC s t k i j)
  · intro h
    exact Or.inl (Finset.mem_map.2 ⟨i, h, rfl⟩)

theorem mem_roleSet_Y (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k)) (j : Fin t) :
    posY s t k j ∈ roleSet s t k A my C ↔ my = true := by
  unfold roleSet
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · rintro (h | h | h)
    · obtain ⟨a, -, h'⟩ := Finset.mem_map.1 h
      exact absurd h' (posA_ne_posY s t k a j)
    · cases my
      · simp at h
      · rfl
    · obtain ⟨j', -, h'⟩ := Finset.mem_map.1 h
      exact absurd h'.symm (posY_ne_posC s t k j j')
  · intro h
    subst h
    exact Or.inr (Or.inl (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩))

theorem mem_roleSet_C (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k)) (j : Fin k) :
    posC s t k j ∈ roleSet s t k A my C ↔ j ∈ C := by
  unfold roleSet
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · rintro (h | h | h)
    · obtain ⟨a, -, h'⟩ := Finset.mem_map.1 h
      exact absurd h' (posA_ne_posC s t k a j)
    · cases my
      · simp at h
      · obtain ⟨j', -, h'⟩ := Finset.mem_map.1 h
        exact absurd h' (posY_ne_posC s t k j' j)
    · obtain ⟨j', hj', h'⟩ := Finset.mem_map.1 h
      rwa [← (posC s t k).injective h']
  · intro h
    exact Or.inr (Or.inr (Finset.mem_map.2 ⟨j, h, rfl⟩))

/-- Every index is in a role set or in that of the other parts. -/
theorem roleSet_cover (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k))
    (i : Fin (s + 1 + t + k)) : i ∈ roleSet s t k A my C ∨ i ∈ roleSet s t k Aᶜ (!my) Cᶜ := by
  refine Fin.addCases (fun u => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun i' => ?_) (fun j => ?_) u
    · by_cases h : i' ∈ A
      · exact Or.inl ((mem_roleSet_A s t k A my C i').2 h)
      · exact Or.inr ((mem_roleSet_A s t k Aᶜ (!my) Cᶜ i').2 (Finset.mem_compl.2 h))
    · cases my
      · exact Or.inr ((mem_roleSet_Y s t k Aᶜ (!false) Cᶜ j).2 rfl)
      · exact Or.inl ((mem_roleSet_Y s t k A true C j).2 rfl)
  · by_cases h : j ∈ C
    · exact Or.inl ((mem_roleSet_C s t k A my C j).2 h)
    · exact Or.inr ((mem_roleSet_C s t k Aᶜ (!my) Cᶜ j).2 (Finset.mem_compl.2 h))

/-- Role sets with disjoint parts are disjoint. -/
theorem roleSet_disjoint (s t k : ℕ) {A A' : Finset (Fin (s + 1))} {my my' : Bool} {C C' : Finset (Fin k)}
    (hA : Disjoint A A') (hmy : (my && my') = false) (hC : Disjoint C C') :
    Disjoint (roleSet s t k A my C) (roleSet s t k A' my' C') := by
  rw [Finset.disjoint_left]
  intro i
  refine Fin.addCases (fun u => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun i' => ?_) (fun j => ?_) u
    · intro h1 h2
      exact Finset.disjoint_left.1 hA ((mem_roleSet_A s t k A my C i').1 h1)
        ((mem_roleSet_A s t k A' my' C' i').1 h2)
    · intro h1 h2
      have e1 := (mem_roleSet_Y s t k A my C j).1 h1
      have e2 := (mem_roleSet_Y s t k A' my' C' j).1 h2
      rw [e1, e2] at hmy
      exact absurd hmy (by decide)
  · intro h1 h2
    exact Finset.disjoint_left.1 hC ((mem_roleSet_C s t k A my C j).1 h1)
      ((mem_roleSet_C s t k A' my' C' j).1 h2)

/-- The product over a role set, by its parts. -/
theorem prod_roleSet (s t k : ℕ) (A : Finset (Fin (s + 1))) (my : Bool) (C : Finset (Fin k))
    (g : Fin (s + 1 + t + k) → ℝ) :
    ∏ i ∈ roleSet s t k A my C, g i =
      (∏ i ∈ A, g (posA s t k i)) * (cond my (∏ j, g (posY s t k j)) 1 * ∏ j ∈ C, g (posC s t k j)) := by
  have hd1 : Disjoint (A.map (posA s t k))
      (cond my (Finset.univ.map (posY s t k)) ∅ ∪ C.map (posC s t k)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hi
    rcases Finset.mem_union.1 hi' with h | h
    · cases my
      · simp at h
      · obtain ⟨j, -, hj⟩ := Finset.mem_map.1 h
        exact posA_ne_posY s t k a j hj.symm
    · obtain ⟨j, -, hj⟩ := Finset.mem_map.1 h
      exact posA_ne_posC s t k a j hj.symm
  have hd2 : Disjoint (cond my (Finset.univ.map (posY s t k)) ∅) (C.map (posC s t k)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    cases my
    · simp at hi
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
      obtain ⟨j', -, hj⟩ := Finset.mem_map.1 hi'
      exact posY_ne_posC s t k j j' hj.symm
  unfold roleSet
  rw [Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_map, Finset.prod_map]
  congr 2
  cases my
  · simp only [Bool.cond_false, Finset.prod_empty]
  · simp only [Bool.cond_true, Finset.prod_map]

/-! ### The exponents of a role set -/

/-- A lower bound for the exponent of the product over a role set: without the cofactor the sum of the lower
ends; with it the slab's lower end less the upper ends of the rest of the box's part. -/
def loRole {s k : ℕ} (βx : Fin (s + 1) → Cell) (bx : Fin k → Cell) (e₁ : ℕ) (A : Finset (Fin (s + 1))) (my : Bool)
    (C : Finset (Fin k)) : ℕ :=
  cond my (e₁ - ∑ i ∈ Aᶜ, (βx i).2) (∑ i ∈ A, (βx i).1) + ∑ j ∈ C, (bx j).1

/-- An upper bound for the exponent of the product over a role set: without the cofactor the sum of the upper
ends; with it the slab's upper end less the lower ends of the rest of the box's part. -/
def hiRole {s k : ℕ} (βx : Fin (s + 1) → Cell) (bx : Fin k → Cell) (e₂ : ℕ) (A : Finset (Fin (s + 1))) (my : Bool)
    (C : Finset (Fin k)) : ℕ :=
  cond my (e₂ - ∑ i ∈ Aᶜ, (βx i).1) (∑ i ∈ A, (βx i).2) + ∑ j ∈ C, (bx j).2

variable [Route]

/-- **The product of a tuple of the family over a role set.** For `x > 1` and a tuple of numbers at least `1`
that satisfies the atoms of `frozA`: its product over `roleSet s t k A my C` lies in
`[x^{loRole/DEN}, x^{hiRole/DEN}]`. -/
theorem role_bounds {q : ℕ} (hx1 : 1 < xq q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} {t k : ℕ}
    {bx : Fin k → Cell} {w : Fin (s + 1 + t + k) → ℕ} (hw1 : ∀ i, 1 ≤ w i)
    (hsem : ∀ A ∈ frozA q e₁ e₂ βx t bx, A.sem w) (A : Finset (Fin (s + 1))) (my : Bool)
    (C : Finset (Fin k)) :
    Xe q (loRole βx bx e₁ A my C) ≤ ∏ i ∈ roleSet s t k A my C, (w i : ℝ) ∧
      ∏ i ∈ roleSet s t k A my C, (w i : ℝ) ≤ Xe q (hiRole βx bx e₂ A my C) := by
  have hx0 : 0 < xq q := by linarith
  obtain ⟨⟨-, hca⟩, ⟨-, hcc⟩, hs1, hs2⟩ := (sem_frozA q e₁ e₂ βx t bx w).1 hsem
  have hPA : ∀ A' : Finset (Fin (s + 1)), Xe q (∑ i ∈ A', (βx i).1) ≤ ∏ i ∈ A', (w (posA s t k i) : ℝ) ∧
      ∏ i ∈ A', (w (posA s t k i) : ℝ) ≤ Xe q (∑ i ∈ A', (βx i).2) := by
    intro A'
    rw [Xe_sum hx0, Xe_sum hx0]
    exact ⟨Finset.prod_le_prod₀ (fun i _ => (Xe_pos hx0 _).le) fun i _ => (hca i).1,
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hca i).2.le⟩
  have hPC : Xe q (∑ j ∈ C, (bx j).1) ≤ ∏ j ∈ C, (w (posC s t k j) : ℝ) ∧
      ∏ j ∈ C, (w (posC s t k j) : ℝ) ≤ Xe q (∑ j ∈ C, (bx j).2) := by
    rw [Xe_sum hx0, Xe_sum hx0]
    exact ⟨Finset.prod_le_prod₀ (fun i _ => (Xe_pos hx0 _).le) fun i _ => (hcc i).1,
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hcc i).2.le⟩
  rw [prod_roleSet]
  obtain ⟨PC, hPCdef⟩ : ∃ PC : ℝ, PC = ∏ j ∈ C, (w (posC s t k j) : ℝ) := ⟨_, rfl⟩
  rw [← hPCdef] at hPC ⊢
  obtain ⟨hPC1, hPC2⟩ := hPC
  have hPC0 : 0 < PC := lt_of_lt_of_le (Xe_pos hx0 _) hPC1
  obtain ⟨PAa, hPAa⟩ : ∃ P : ℝ, P = ∏ i ∈ A, (w (posA s t k i) : ℝ) := ⟨_, rfl⟩
  rw [← hPAa]
  have hPAa1 : 1 ≤ PAa := by
    rw [hPAa]
    exact one_le_prod_cast A (fun i => w (posA s t k i)) fun i => hw1 _
  unfold loRole hiRole
  rw [Xe_add hx0, Xe_add hx0]
  cases my
  · simp only [Bool.cond_false, one_mul]
    obtain ⟨h1, h2⟩ := hPA A
    rw [← hPAa] at h1 h2
    exact ⟨mul_le_mul h1 hPC1 (Xe_pos hx0 _).le (by linarith),
      mul_le_mul h2 hPC2 hPC0.le (Xe_pos hx0 _).le⟩
  · simp only [Bool.cond_true]
    obtain ⟨PY, hPYdef⟩ : ∃ PY : ℝ, PY = ∏ j, (w (posY s t k j) : ℝ) := ⟨_, rfl⟩
    rw [← hPYdef]
    obtain ⟨PAc, hPAc⟩ : ∃ P : ℝ, P = ∏ i ∈ Aᶜ, (w (posA s t k i) : ℝ) := ⟨_, rfl⟩
    have hR : ∏ i ∈ posAY s t k, (w i : ℝ) = PAa * PAc * PY := by
      unfold posAY
      rw [Finset.prod_map, Fin.prod_univ_add, hPAa, hPAc, Finset.prod_mul_prod_compl A, hPYdef]
      rfl
    rw [hR] at hs1 hs2
    obtain ⟨hc1, hc2⟩ := hPA Aᶜ
    rw [← hPAc] at hc1 hc2
    have hPY1 : 1 ≤ PY := by
      rw [hPYdef]
      exact one_le_prod_cast Finset.univ (fun j => w (posY s t k j)) fun j => hw1 _
    have hP1 : 1 ≤ PAa * PY := one_le_mul_of_one_le_of_one_le hPAa1 hPY1
    have hXH := Xe_pos hx0 (∑ i ∈ Aᶜ, (βx i).2)
    have hXL := Xe_pos hx0 (∑ i ∈ Aᶜ, (βx i).1)
    have hlo : Xe q (e₁ - ∑ i ∈ Aᶜ, (βx i).2) ≤ PAa * PY := by
      rcases Nat.le_total (∑ i ∈ Aᶜ, (βx i).2) e₁ with h | h
      · have e : Xe q e₁ = Xe q (e₁ - ∑ i ∈ Aᶜ, (βx i).2) * Xe q (∑ i ∈ Aᶜ, (βx i).2) := by
          rw [← Xe_add hx0, Nat.sub_add_cancel h]
        have h3 : PAa * PAc * PY ≤ PAa * PY * Xe q (∑ i ∈ Aᶜ, (βx i).2) := by
          have e' : PAa * PAc * PY = PAa * PY * PAc := by ring
          rw [e']
          exact mul_le_mul_of_nonneg_left hc2 (by linarith)
        rw [e] at hs1
        exact (lt_of_mul_lt_mul_right (lt_of_lt_of_le hs1 h3) hXH.le).le
      · rw [Nat.sub_eq_zero_of_le h, Xe_zero]
        exact hP1
    have hhi : PAa * PY ≤ Xe q (e₂ - ∑ i ∈ Aᶜ, (βx i).1) := by
      have h3 : PAa * PY * Xe q (∑ i ∈ Aᶜ, (βx i).1) ≤ PAa * PAc * PY := by
        have e' : PAa * PAc * PY = PAa * PY * PAc := by ring
        rw [e']
        exact mul_le_mul_of_nonneg_left hc1 (by linarith)
      rcases Nat.lt_or_ge e₂ (∑ i ∈ Aᶜ, (βx i).1) with h | h
      · exfalso
        have h4 : Xe q (∑ i ∈ Aᶜ, (βx i).1) ≤ Xe q e₂ := by
          have h5 : Xe q (∑ i ∈ Aᶜ, (βx i).1) ≤ PAa * PY * Xe q (∑ i ∈ Aᶜ, (βx i).1) :=
            le_mul_of_one_le_left hXL.le hP1
          linarith
        have h6 := (Xe_le_iff hx1).1 h4
        omega
      · have e : Xe q e₂ = Xe q (e₂ - ∑ i ∈ Aᶜ, (βx i).1) * Xe q (∑ i ∈ Aᶜ, (βx i).1) := by
          rw [← Xe_add hx0, Nat.sub_add_cancel h]
        rw [e] at hs2
        exact le_of_mul_le_mul_right (h3.trans hs2) hXL
    have e3 : PAa * (PY * PC) = PAa * PY * PC := by ring
    rw [e3]
    exact ⟨mul_le_mul hlo hPC1 (Xe_pos hx0 _).le (by linarith),
      mul_le_mul hhi hPC2 hPC0.le (Xe_pos hx0 _).le⟩

/-- Every prime of a tuple of `frozW` is below `x`, for cells with upper ends at most `DEN` and `e₂ ≤ DEN`. -/
theorem frozW_lt {q : ℕ} (hx1 : 1 ≤ xq q) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell} (hβD : ∀ i, (βx i).2 ≤ DEN)
    (he₂ : e₂ ≤ DEN) {t k : ℕ} {bx : Fin k → Cell} (hbD : ∀ j, (bx j).2 ≤ DEN) {w : Fin (s + 1 + t + k) → ℕ}
    (hw : w ∈ frozW q e₁ e₂ βx t bx) (i : Fin (s + 1 + t + k)) : (w i : ℝ) < Xe q DEN := by
  obtain ⟨-, hu, hc⟩ := mem_frozW.1 hw
  obtain ⟨hup, ha, -, -, -, hslab⟩ := mem_frozP.1 hu
  refine Fin.addCases (fun u => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun i' => ?_) (fun j => ?_) u
    · obtain ⟨-, -, hca⟩ := mem_famB.1 ha
      exact lt_of_lt_of_le (hca i').2 (Xe_mono hx1 (hβD i'))
    · obtain ⟨hap, -, -⟩ := mem_famB.1 ha
      have hsplit := prodR_split (m := s + 1) (n := t) (fun i => w (Fin.castAdd k i))
      have h1 : w (Fin.castAdd k (Fin.natAdd (s + 1) j)) ∣
          prodR (fun j => w (Fin.castAdd k (Fin.natAdd (s + 1) j))) :=
        Finset.dvd_prod_of_mem (fun j => w (Fin.castAdd k (Fin.natAdd (s + 1) j))) (Finset.mem_univ j)
      have h2 : w (Fin.castAdd k (Fin.castAdd t (Fin.last s))) ∣
          prodR (fun i => w (Fin.castAdd k (Fin.castAdd t i))) :=
        Finset.dvd_prod_of_mem (fun i => w (Fin.castAdd k (Fin.castAdd t i))) (Finset.mem_univ (Fin.last s))
      have hpa : 0 < prodR (fun i => w (Fin.castAdd k (Fin.castAdd t i))) :=
        Finset.prod_pos fun i _ => (hap i).2.pos
      have hpy : 0 < prodR (fun j => w (Fin.castAdd k (Fin.natAdd (s + 1) j))) :=
        Finset.prod_pos fun j _ => (hup _).2.pos
      have h3 : 2 ≤ prodR (fun i => w (Fin.castAdd k (Fin.castAdd t i))) :=
        (hap (Fin.last s)).2.two_le.trans (Nat.le_of_dvd hpa h2)
      have h4 : w (Fin.castAdd k (Fin.natAdd (s + 1) j)) ≤
          prodR (fun j => w (Fin.castAdd k (Fin.natAdd (s + 1) j))) := Nat.le_of_dvd hpy h1
      have h5 : 2 * w (Fin.castAdd k (Fin.natAdd (s + 1) j)) ≤ prodR (fun i => w (Fin.castAdd k i)) := by
        rw [hsplit]
        exact Nat.mul_le_mul h3 h4
      have h6 : (2 : ℝ) * w (Fin.castAdd k (Fin.natAdd (s + 1) j)) ≤ Xe q DEN := by
        have h7 : ((2 * w (Fin.castAdd k (Fin.natAdd (s + 1) j)) : ℕ) : ℝ) ≤
            (prodR (fun i => w (Fin.castAdd k i)) : ℝ) := by exact_mod_cast h5
        push_cast at h7
        exact h7.trans (hslab.trans (Xe_mono hx1 he₂))
      have h8 : (0 : ℝ) < w (Fin.castAdd k (Fin.natAdd (s + 1) j)) := by exact_mod_cast (hup _).2.pos
      linarith
  · obtain ⟨-, -, hcc⟩ := mem_famB.1 hc
    exact lt_of_lt_of_le (hcc j).2 (Xe_mono hx1 (hbD j))

variable [RouteOK] [SieveCert.IBPar] [IBFits]

/-! ### The two comparisons over the frozen part -/

/-- **The comparison with the rest among the tree's primes, over the frozen part.** Let `βx` and the chain's box
`bx` have cells with `f ≤ lo` and ends at most `DEN`, `0 < f ≤ DEN`, `e₁, e₂ ≤ DEN` and `(T + 1)·lo_s ≥ DEN + 1`.
Let `(A₀, my₀, C₀)` be the parts of the set that enters the window and `(A₁, my₁, C₁)` those of the first side of
the leaves. If the exponents of the role sets pass `coreJ3` at the floor `f` with `Kb ≥ s + 1 + T + k` cells of
room, the terms at the floor `x^{f/DEN}` of the chain's box over the frozen part are evaluated. -/
theorem evJF_froz_fill {f : ℕ} (hf : 0 < f) (hfD : f ≤ DEN) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, f ≤ (βx i).1 ∧ (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, f ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN)
    (A₀ A₁ : Finset (Fin (s + 1))) (my₀ my₁ : Bool) (C₀ C₁ : Finset (Fin k)) (e : Bool)
    (u v tt r1 r2 Kb : ℕ) (hKb : s + 1 + T + k ≤ Kb)
    (hok : coreJ3 f e u v tt r1 r2 (loRole βx bx e₁ A₀ my₀ C₀ - Kb) (hiRole βx bx e₂ A₀ my₀ C₀ + Kb)
      (hiRole βx bx e₂ A₁ my₁ C₁ + Kb) (hiRole βx bx e₂ A₁ᶜ (!my₁) C₁ᶜ + Kb) = true) :
    EvJF (fun q => frozS q e₁ e₂ βx) frozR f bx := by
  refine evJF_frozS he₂ hT fun t ht => evJF_frozP hf (hβ (Fin.last s)).1 t (fun j => (hb j).1) ?_
  refine evJ_fam_fill f hfD (roleSet s t k A₀ my₀ C₀) (roleSet s t k A₁ my₁ C₁) e u v tt r1 r2 _ _ _ _ Kb
    (by omega) hok (fun q => frozE q e₁ e₂ βx t bx) (fun q => frozE_length q e₁ e₂ βx t bx) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with q hq
    exact thrOK_frozE hq (fun i => (hβ i).2) t (fun j => (hb j).2) he₁ he₂
  · filter_upwards [big_ev] with q hbig w hw hinj
    obtain ⟨-, hx3, -⟩ := big_facts hbig
    have hx1 : 1 ≤ xq q := by linarith
    have hx1' : 1 < xq q := by linarith
    have hwW : w ∈ frozW q e₁ e₂ βx t bx := by
      have h : w ∈ (frozW q e₁ e₂ βx t bx).filter Function.Injective := by
        rw [frozW_inj_eq]
        exact Finset.mem_filter.2 ⟨hw, hinj⟩
      exact (Finset.mem_filter.1 h).1
    have hge := frozW_ge hx1 (hβ (Fin.last s)).1 (fun j => (hb j).1) hwW
    have hlt := frozW_lt hx1 (fun i => (hβ i).2.2) he₂ (fun j => (hb j).2.2) hwW
    have hw1 : ∀ i, 1 ≤ w i := fun i => ((mem_famSet.1 hw).1 i).2.one_lt.le
    have hsem := ((sem_frozE q e₁ e₂ βx t bx w).1 (mem_famSet.1 hw).2).1
    obtain ⟨h01, h02⟩ := role_bounds hx1' hw1 hsem A₀ my₀ C₀
    obtain ⟨-, h1⟩ := role_bounds hx1' hw1 hsem A₁ my₁ C₁
    obtain ⟨-, h2⟩ := role_bounds hx1' hw1 hsem A₁ᶜ (!my₁) C₁ᶜ
    refine ⟨fun i => ⟨hge i, hlt i⟩, h01, h02, h1, le_trans ?_ h2⟩
    refine prod_cast_le_of_subset (fun i hi => ?_) w hw1
    exact (roleSet_cover s t k A₁ my₁ C₁ i).resolve_left (Finset.mem_compl.1 hi)

/-- **The comparison with the rest among the tuple's primes, over the frozen part.** As `evJF_froz_fill`, with
the parts `(Ar, myr, Cr)` of the rest's set, disjoint from those of the set that enters the window, whose
exponent has a positive lower bound, and the checks `coreJ2`. -/
theorem evJF_froz_two {f : ℕ} (hf : 0 < f) (hfD : f ≤ DEN) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, f ≤ (βx i).1 ∧ (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, f ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN)
    (A₀ Ar A₁ : Finset (Fin (s + 1))) (my₀ myr my₁ : Bool) (C₀ Cr C₁ : Finset (Fin k))
    (hdA : Disjoint A₀ Ar) (hdmy : (my₀ && myr) = false) (hdC : Disjoint C₀ Cr) (e : Bool)
    (u v tt Kb : ℕ) (hKb : s + 1 + T + k ≤ Kb) (hρ : 0 < loRole βx bx e₁ Ar myr Cr)
    (hok : coreJ2 f e u v tt (loRole βx bx e₁ Ar myr Cr - Kb) (hiRole βx bx e₂ Ar myr Cr + Kb)
      (loRole βx bx e₁ A₀ my₀ C₀ - Kb) (hiRole βx bx e₂ A₀ my₀ C₀ + Kb)
      (hiRole βx bx e₂ A₁ my₁ C₁ + Kb) (hiRole βx bx e₂ A₁ᶜ (!my₁) C₁ᶜ + Kb) = true) :
    EvJF (fun q => frozS q e₁ e₂ βx) frozR f bx := by
  refine evJF_frozS he₂ hT fun t ht => evJF_frozP hf (hβ (Fin.last s)).1 t (fun j => (hb j).1) ?_
  refine evJ_fam_two f hfD (roleSet s t k A₀ my₀ C₀) (roleSet s t k Ar myr Cr) (roleSet s t k A₁ my₁ C₁)
    (roleSet_disjoint s t k hdA hdmy hdC) e u v tt _ _ _ _ _ _ Kb (by omega) hρ hok
    (fun q => frozE q e₁ e₂ βx t bx) (fun q => frozE_length q e₁ e₂ βx t bx) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with q hq
    exact thrOK_frozE hq (fun i => (hβ i).2) t (fun j => (hb j).2) he₁ he₂
  · filter_upwards [big_ev] with q hbig w hw hinj
    obtain ⟨-, hx3, -⟩ := big_facts hbig
    have hx1 : 1 ≤ xq q := by linarith
    have hx1' : 1 < xq q := by linarith
    have hwW : w ∈ frozW q e₁ e₂ βx t bx := by
      have h : w ∈ (frozW q e₁ e₂ βx t bx).filter Function.Injective := by
        rw [frozW_inj_eq]
        exact Finset.mem_filter.2 ⟨hw, hinj⟩
      exact (Finset.mem_filter.1 h).1
    have hge := frozW_ge hx1 (hβ (Fin.last s)).1 (fun j => (hb j).1) hwW
    have hlt := frozW_lt hx1 (fun i => (hβ i).2.2) he₂ (fun j => (hb j).2.2) hwW
    have hw1 : ∀ i, 1 ≤ w i := fun i => ((mem_famSet.1 hw).1 i).2.one_lt.le
    have hsem := ((sem_frozE q e₁ e₂ βx t bx w).1 (mem_famSet.1 hw).2).1
    obtain ⟨hr1, hr2⟩ := role_bounds hx1' hw1 hsem Ar myr Cr
    obtain ⟨h01, h02⟩ := role_bounds hx1' hw1 hsem A₀ my₀ C₀
    obtain ⟨-, h1⟩ := role_bounds hx1' hw1 hsem A₁ my₁ C₁
    obtain ⟨-, h2⟩ := role_bounds hx1' hw1 hsem A₁ᶜ (!my₁) C₁ᶜ
    refine ⟨fun i => ⟨hge i, hlt i⟩, hr1, hr2, h01, h02, h1, le_trans ?_ h2⟩
    refine prod_cast_le_of_subset (fun i hi => ?_) w hw1
    exact (roleSet_cover s t k A₁ my₁ C₁ i).resolve_left (Finset.mem_compl.1 hi)

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison with the rest among the tree's primes, over the frozen part, for any route**:
`evJF_froz_fill` with the route and its exponent as variables. -/
theorem evJF_froz_fill_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {f : ℕ}
    (hf : 0 < f) (hfD : f ≤ DEN) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, f ≤ (βx i).1 ∧ (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, f ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN)
    (A₀ A₁ : Finset (Fin (s + 1))) (my₀ my₁ : Bool) (C₀ C₁ : Finset (Fin k)) (e : Bool)
    (u v tt r1 r2 Kb : ℕ) (hKb : s + 1 + T + k ≤ Kb)
    (hok : @coreJ3 Pr f e u v tt r1 r2 (loRole βx bx e₁ A₀ my₀ C₀ - Kb) (hiRole βx bx e₂ A₀ my₀ C₀ + Kb)
      (hiRole βx bx e₂ A₁ my₁ C₁ + Kb) (hiRole βx bx e₂ A₁ᶜ (!my₁) C₁ᶜ + Kb) = true) :
    @EvJF Rt _ (fun q => @frozS Rt q e₁ e₂ s βx) frozR f k bx :=
  @evJF_froz_fill Rt hRt Pr hPr f hf hfD e₁ e₂ s βx hβ he₁ he₂ T hT k bx hb A₀ A₁ my₀ my₁ C₀ C₁ e u v tt r1 r2 Kb
    hKb hok

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison with the rest among the tuple's primes, over the frozen part, for any route**:
`evJF_froz_two` with the route and its exponent as variables. -/
theorem evJF_froz_two_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {f : ℕ}
    (hf : 0 < f) (hfD : f ≤ DEN) {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, f ≤ (βx i).1 ∧ (βx i).1 ≤ DEN ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {T : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (βx (Fin.last s)).1) {k : ℕ} {bx : Fin k → Cell}
    (hb : ∀ j, f ≤ (bx j).1 ∧ (bx j).1 ≤ DEN ∧ (bx j).2 ≤ DEN)
    (A₀ Ar A₁ : Finset (Fin (s + 1))) (my₀ myr my₁ : Bool) (C₀ Cr C₁ : Finset (Fin k))
    (hdA : Disjoint A₀ Ar) (hdmy : (my₀ && myr) = false) (hdC : Disjoint C₀ Cr) (e : Bool)
    (u v tt Kb : ℕ) (hKb : s + 1 + T + k ≤ Kb) (hρ : 0 < loRole βx bx e₁ Ar myr Cr)
    (hok : @coreJ2 Pr f e u v tt (loRole βx bx e₁ Ar myr Cr - Kb) (hiRole βx bx e₂ Ar myr Cr + Kb)
      (loRole βx bx e₁ A₀ my₀ C₀ - Kb) (hiRole βx bx e₂ A₀ my₀ C₀ + Kb)
      (hiRole βx bx e₂ A₁ my₁ C₁ + Kb) (hiRole βx bx e₂ A₁ᶜ (!my₁) C₁ᶜ + Kb) = true) :
    @EvJF Rt _ (fun q => @frozS Rt q e₁ e₂ s βx) frozR f k bx :=
  @evJF_froz_two Rt hRt Pr hPr f hf hfD e₁ e₂ s βx hβ he₁ he₂ T hT k bx hb A₀ Ar A₁ my₀ myr my₁ C₀ Cr C₁ hdA hdmy
    hdC e u v tt Kb hKb hρ hok

end SieveAd

#print axioms SieveAd.evJF_froz_fill_at
#print axioms SieveAd.evJF_froz_two_at
