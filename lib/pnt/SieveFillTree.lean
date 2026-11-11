/-
# Buchstab's tree below a chain's last entry

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveP6Tree.tree_chains` is Buchstab's tree on a family of chains sifted at a level `z₀` that lies below all their
entries. This file is the same for a family sifted at each chain's own last entry, so that the tree's primes lie
below that entry: it is what a second phase of a comparison needs, on the stops of the first. The rule is that of
`SieveP6Tree.tree_split` with `c = 1`: a branch `P` stops when `∏P` reaches `E`.

Plain statements. `GCmp`, `RTg` and `liftChain` are `SieveChain`'s; `gUp`, `gDown`, `gltVar`, `Pblock` and
`sum_chain` are `SieveP6Chain`'s; `leafCmps`, `stopCmps`, `idxAll` and `idxInit` are `SieveP6Tree`'s; `rough z n` and
`primesIco w z` are `SieveTree`'s.

* `tree_split_below`: `SieveP6Tree.tree_split` at the level `b` and `c = 1`, with its sets of primes taken in
  `[w, Z)` for a `Z ≥ b`, under the condition that they lie below `b`.
* `belowL`, `leafCmpsL`, `stopCmpsL`: the comparisons of the leaves and of the stops, `SieveP6Tree.leafCmps` and
  `stopCmps` at `S₀ = ∅` and `z₀ = Z`, with each entry of the block below the last entry of the first part.
* `leafCmpsL_holds`, `stopCmpsL_holds`, `leafCmpsL_c_le`, `stopCmpsL_c_le`, `length_leafCmpsL_le`,
  `length_stopCmpsL_le`: what the comparisons say, their `m`-parts and their number.
* `tree_last`: **the tree below the last entry, as chains.** For `1 ≤ w ≤ Y + 1`, `E > 1` and a family
  `RTg (k′ + 1) Y Ω` of strictly decreasing tuples with last entry at least `w`: the multiples of `∏rt` with no
  prime factor below `rt`'s last entry are the leaves of the sizes `s`, the chains of `leafCmpsL` (with the sign
  `(−1)^s`, sifted at `w`), plus the stops, the chains of `stopCmpsL` (with the sign `(−1)^{s+1}`, sifted at their
  last entry).

The file imports `SieveP6Tree.lean`.
-/
import SieveP6Tree

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain SieveP6Tree

namespace SieveFillTree

open Classical

/-! ### The tree at one chain, with its primes taken in a larger range -/

/-- A sum over the subsets of the elements of `T` below `b` is a sum over the subsets of `T` that lie below `b`. -/
theorem sum_powerset_below (T : Finset ℕ) (b : ℕ) (F : Finset ℕ → ℂ) :
    ∑ P ∈ (T.filter (· < b)).powerset, F P = ∑ P ∈ T.powerset, if (∀ p ∈ P, p < b) then F P else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
  exact ⟨fun h => ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩, fun h p hp => ⟨h.1 hp, h.2 p hp⟩⟩

/-- The primes of `[a, b)` are those of `[a, Z)` below `b`, for `b ≤ Z`. -/
theorem primesIco_below {a b Z : ℕ} (hbZ : b ≤ Z) : primesIco a b = (primesIco a Z).filter (· < b) := by
  ext p
  simp only [mem_primesIco, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by omega, h3⟩, h2⟩
  · rintro ⟨⟨h1, -, h3⟩, h2⟩
    exact ⟨h1, h2, h3⟩

/-- **Buchstab's tree below `b` with the rule `E ≤ ∏P`, its primes taken in `[w, Z)`.** For `1 ≤ w ≤ b ≤ Z`, `r`
with every prime factor at least `b`, and `E > 1`: `Σ_{n∈C} f(n)[r ∣ n, rough b n]` is the leaves' sum over the
`P ⊆ [w, Z)` below `b` with `∏P < E`, plus the stops' sum over `p ∈ [w, Z)` and `P ⊆ (p, Z)`, below `b`, with
`∏P < E ≤ ∏P·p`. -/
theorem tree_split_below (C : Finset ℕ) (f : ℕ → ℂ) {r w b Z : ℕ} (hw : 1 ≤ w) (hwb : w ≤ b) (hbZ : b ≤ Z)
    (hr : ∀ p : ℕ, p.Prime → p ∣ r → b ≤ p) {E : ℝ} (hE : 1 < E) :
    ∑ n ∈ C, f n * (if r ∣ n ∧ rough b n then 1 else 0) =
      ∑ P ∈ (primesIco w Z).powerset, (-1 : ℂ) ^ P.card *
          (if (∀ p ∈ P, p < b) ∧ ((∏ p ∈ P, p : ℕ) : ℝ) < E then
            ∑ n ∈ C, f n * (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w Z, ∑ P ∈ (primesIco (p + 1) Z).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if (p < b ∧ ∀ p' ∈ P, p' < b) ∧ ((∏ p' ∈ P, p' : ℕ) : ℝ) < E ∧
              E ≤ ((∏ p' ∈ P, p' : ℕ) : ℝ) * p then
            ∑ n ∈ C, f n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  rw [tree_split C f hw hwb hr zero_le_one hE]
  simp only [one_mul]
  congr 1
  · rw [primesIco_below hbZ, sum_powerset_below]
    refine Finset.sum_congr rfl fun P _ => ?_
    by_cases h1 : ∀ p ∈ P, p < b
    · rw [ite_eq_left h1]
      by_cases h2 : ((∏ p ∈ P, p : ℕ) : ℝ) < E
      · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
      · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.2]
    · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1, mul_zero]
  · rw [primesIco_below hbZ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p < b
    · rw [ite_eq_left hp, primesIco_below hbZ, sum_powerset_below]
      refine Finset.sum_congr rfl fun P _ => ?_
      by_cases h1 : ∀ p' ∈ P, p' < b
      · rw [ite_eq_left h1]
        by_cases h2 : ((∏ p' ∈ P, p' : ℕ) : ℝ) < E ∧ E ≤ ((∏ p' ∈ P, p' : ℕ) : ℝ) * p
        · rw [ite_eq_left h2, ite_eq_left ⟨⟨hp, h1⟩, h2⟩]
        · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.2]
      · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1.2, mul_zero]
    · rw [ite_eq_right hp]
      exact (Finset.sum_eq_zero fun P _ => by rw [ite_eq_right fun h => hp h.1.1, mul_zero]).symm

/-! ### The comparisons of the leaves and of the stops -/

section Cmps

variable {k' : ℕ}

/-- Every entry of the block below the last entry of the first part, on `Fin (k′ + 1 + s)`. -/
noncomputable def belowL (k' s : ℕ) : List (GCmp (k' + 1 + s)) :=
  (List.finRange s).map fun u => gltVar (Fin.castAdd s (Fin.last k')) (Fin.natAdd (k' + 1) u)

theorem length_belowL (k' s : ℕ) : (belowL k' s).length = s := by
  simp [belowL]

theorem belowL_holds {s : ℕ} (m : ℕ) {x : Fin (k' + 1 + s) → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (∀ C ∈ belowL k' s, C.holds m x) ↔
      ∀ u : Fin s, x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd s (Fin.last k')) := by
  simp only [belowL, List.forall_mem_map, List.mem_finRange, true_implies, gltVar_holds _ _ m hx]

/-- The comparisons of a leaf below the last entry, with a block of size `s`: the family's on the first part, the
block's (in `[w, Z)`, strictly decreasing), `∏y < E`, and the block below the first part's last entry. -/
noncomputable def leafCmpsL (Ω : List (GCmp (k' + 1))) (E w Z : ℝ) (s : ℕ) : List (GCmp (k' + 1 + s)) :=
  leafCmps Ω ∅ E w Z s ++ belowL k' s

/-- The comparisons of a stop below the last entry, with a block `y` of size `s + 1`: the family's on the first
part, the block's, `∏y' < E ≤ ∏y` with `y'` the block without its last entry, and the block below the first part's
last entry. -/
noncomputable def stopCmpsL (Ω : List (GCmp (k' + 1))) (E w Z : ℝ) (s : ℕ) : List (GCmp (k' + 1 + (s + 1))) :=
  stopCmps Ω ∅ E w Z s ++ belowL k' (s + 1)

/-- What the comparisons of a leaf below the last entry say. -/
theorem leafCmpsL_holds (Ω : List (GCmp (k' + 1))) {E : ℝ} (hE : 0 < E) {w Z : ℝ} (hw : 0 < w) (hZ : 0 < Z)
    {s : ℕ} {x : Fin (k' + 1 + s) → ℕ} (hx1 : ∀ i, 1 ≤ x i) :
    (∀ C ∈ leafCmpsL Ω E w Z s, C.holds 0 x) ↔
      ((∀ C ∈ Ω, C.holds 0 (fun i => x (Fin.castAdd s i))) ∧
        (StrictAnti (fun u : Fin s => x (Fin.natAdd (k' + 1) u)) ∧
          ∀ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) < Z ∧ w ≤ (x (Fin.natAdd (k' + 1) u) : ℝ)) ∧
        ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) < E) ∧
      ∀ u : Fin s, x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd s (Fin.last k')) := by
  rw [leafCmpsL, List.forall_mem_append, leafCmps_holds Ω ∅ hE hw hZ hx1, belowL_holds 0 hx1, prod_idxAll,
    Finset.prod_empty, one_mul]

/-- What the comparisons of a stop below the last entry say. -/
theorem stopCmpsL_holds (Ω : List (GCmp (k' + 1))) {E : ℝ} (hE : 0 < E) {w Z : ℝ} (hw : 0 < w) (hZ : 0 < Z)
    {s : ℕ} {x : Fin (k' + 1 + (s + 1)) → ℕ} (hx1 : ∀ i, 1 ≤ x i) :
    (∀ C ∈ stopCmpsL Ω E w Z s, C.holds 0 x) ↔
      ((∀ C ∈ Ω, C.holds 0 (fun i => x (Fin.castAdd (s + 1) i))) ∧
        (StrictAnti (fun u : Fin (s + 1) => x (Fin.natAdd (k' + 1) u)) ∧
          ∀ u : Fin (s + 1), (x (Fin.natAdd (k' + 1) u) : ℝ) < Z ∧ w ≤ (x (Fin.natAdd (k' + 1) u) : ℝ)) ∧
        ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u.castSucc) : ℝ) < E ∧
          E ≤ ∏ u : Fin (s + 1), (x (Fin.natAdd (k' + 1) u) : ℝ)) ∧
      ∀ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd (s + 1) (Fin.last k')) := by
  rw [stopCmpsL, List.forall_mem_append, stopCmps_holds Ω ∅ hE hw hZ hx1, belowL_holds 0 hx1, prod_idxAll,
    prod_idxInit, Finset.prod_empty, one_mul, one_mul]

/-- A tuple of a family of leaves or stops below the last entry is strictly decreasing, when its first part is. -/
theorem strictAnti_chainL {t : ℕ} {x : Fin (k' + 1 + t) → ℕ}
    (h1 : StrictAnti (fun i => x (Fin.castAdd t i))) (h2 : StrictAnti (fun u => x (Fin.natAdd (k' + 1) u)))
    (h3 : ∀ u : Fin t, x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd t (Fin.last k'))) : StrictAnti x := by
  have e : x = Fin.append (fun i => x (Fin.castAdd t i)) (fun u => x (Fin.natAdd (k' + 1) u)) :=
    (Fin.append_castAdd_natAdd (f := x)).symm
  rw [e]
  exact strictAnti_append h1 h2 fun i u => lt_of_lt_of_le (h3 u) (h1.antitone (Fin.le_last i))

theorem belowL_c_le {s : ℕ} {B : ℝ} (hB : 0 ≤ B) : ∀ C ∈ belowL k' s, C.c 0 ≤ B := by
  intro C hC
  simp only [belowL, List.mem_map, List.mem_finRange, true_and] at hC
  obtain ⟨u, rfl⟩ := hC
  exact hB

/-- The `m`-parts of the comparisons of a leaf below the last entry are at most `B`. -/
theorem leafCmpsL_c_le {Ω : List (GCmp (k' + 1))} {E w Z B : ℝ} {s : ℕ} (hB : 0 ≤ B)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ B) (hZ : Real.log Z ≤ B) (hE : Real.log E ≤ B) (hw : 1 ≤ w) :
    ∀ C ∈ leafCmpsL Ω E w Z s, C.c 0 ≤ B := by
  intro C hC
  simp only [leafCmpsL, leafCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at hC
  rcases hC with ((⟨C', hC', rfl⟩ | hC) | rfl) | hC
  · exact hc C' hC'
  · exact Pblock_c_le hB hZ hw C hC
  · exact hE
  · exact belowL_c_le hB C hC

/-- The `m`-parts of the comparisons of a stop below the last entry are at most `B`. -/
theorem stopCmpsL_c_le {Ω : List (GCmp (k' + 1))} {E w Z B : ℝ} {s : ℕ} (hB : 0 ≤ B)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ B) (hZ : Real.log Z ≤ B) (hE : Real.log E ≤ B) (hE1 : 1 ≤ E) (hw : 1 ≤ w) :
    ∀ C ∈ stopCmpsL Ω E w Z s, C.c 0 ≤ B := by
  intro C hC
  simp only [stopCmpsL, stopCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at hC
  rcases hC with ((⟨C', hC', rfl⟩ | hC) | rfl | rfl) | hC
  · exact hc C' hC'
  · exact Pblock_c_le hB hZ hw C hC
  · exact hE
  · show -Real.log E ≤ B
    have := Real.log_nonneg hE1
    linarith
  · exact belowL_c_le hB C hC

theorem length_leafCmpsL_le (Ω : List (GCmp (k' + 1))) (E w Z : ℝ) (s : ℕ) :
    (leafCmpsL Ω E w Z s).length ≤ Ω.length + s * s + 3 * s + 1 := by
  have := length_Pblock_le (k' + 1) s w Z
  simp only [leafCmpsL, leafCmps, List.length_append, List.length_map, List.length_singleton, length_belowL]
  omega

theorem length_stopCmpsL_le (Ω : List (GCmp (k' + 1))) (E w Z : ℝ) (s : ℕ) :
    (stopCmpsL Ω E w Z s).length ≤ Ω.length + (s + 1) * (s + 1) + 3 * (s + 1) + 2 := by
  have := length_Pblock_le (k' + 1) (s + 1) w Z
  simp only [stopCmpsL, stopCmps, List.length_append, List.length_map, List.length_cons, List.length_nil,
    length_belowL]
  omega

/-! ### The branches as chains -/

/-- **The leaves of size `s` below the last entry, as chains.** -/
theorem sum_leaves_chainL {M : Type*} [AddCommMonoid M] (Ω : List (GCmp (k' + 1))) {E : ℝ} (hE : 0 < E)
    {Y w : ℕ} (s : ℕ) (hw : 1 ≤ w) (hwY : w ≤ Y + 1) (G : ℕ → M) :
    ∑ rt ∈ RTg (k' + 1) Y Ω,
        ∑ y ∈ (Fintype.piFinset fun _ : Fin s => primesIco w (Y + 1)).filter StrictAnti,
          (if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u, y u : ℕ) : ℝ) < E then G ((∏ i, rt i) * ∏ u, y u)
            else 0) =
      ∑ x ∈ RTg (k' + 1 + s) Y (leafCmpsL Ω E w ((Y + 1 : ℕ) : ℝ) s), G (∏ i, x i) := by
  rw [sum_chain (k' + 1) s Ω hw hwY le_rfl (fun rt y =>
    if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u, y u : ℕ) : ℝ) < E then G ((∏ i, rt i) * ∏ u, y u) else 0)]
  rw [leafCmpsL, leafCmps, List.append_assoc,
    RTg_append (k' + 1 + s) Y (Ω.map liftChain ++ Pblock (k' + 1) s w ((Y + 1 : ℕ) : ℝ)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 := one_le_of_mem_RTg hx
  have hcond : (∀ C ∈ [gUp (idxAll (∅ : Finset (Fin (k' + 1))) s) E true] ++ belowL k' s, C.holds 0 x) ↔
      (∀ u : Fin s, x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd s (Fin.last k'))) ∧
        ((∏ u, x (Fin.natAdd (k' + 1) u) : ℕ) : ℝ) < E := by
    rw [List.forall_mem_append, belowL_holds 0 hx1]
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    rw [gUp_holds _ hE true 0 hx1, prod_idxAll, Finset.prod_empty, one_mul, ite_eq_left rfl]
    push_cast
    exact and_comm
  have hprod : (∏ i, x (Fin.castAdd s i)) * ∏ u, x (Fin.natAdd (k' + 1) u) = ∏ i, x i :=
    (Fin.prod_univ_add x).symm
  by_cases h : (∀ u : Fin s, x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd s (Fin.last k'))) ∧
      ((∏ u, x (Fin.natAdd (k' + 1) u) : ℕ) : ℝ) < E
  · rw [ite_eq_left h, ite_eq_left (hcond.2 h), hprod]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hcond.1 h')]

/-- **The stops of size `s + 1` below the last entry, as chains.** -/
theorem sum_stops_chainL {M : Type*} [AddCommMonoid M] (Ω : List (GCmp (k' + 1))) {E : ℝ} (hE : 0 < E)
    {Y w : ℕ} (s : ℕ) (hw : 1 ≤ w) (hwY : w ≤ Y + 1) (G : ℕ → ℕ → M) :
    ∑ rt ∈ RTg (k' + 1) Y Ω,
        ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => primesIco w (Y + 1)).filter StrictAnti,
          (if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
              E ≤ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
            G ((∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s)) (y (Fin.last s)) else 0) =
      ∑ x ∈ RTg (k' + 1 + (s + 1)) Y (stopCmpsL Ω E w ((Y + 1 : ℕ) : ℝ) s),
        G (∏ i, x i) (x (Fin.natAdd (k' + 1) (Fin.last s))) := by
  rw [sum_chain (k' + 1) (s + 1) Ω hw hwY le_rfl (fun rt y =>
    if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
        E ≤ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
      G ((∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s)) (y (Fin.last s)) else 0)]
  rw [stopCmpsL, stopCmps, List.append_assoc,
    RTg_append (k' + 1 + (s + 1)) Y (Ω.map liftChain ++ Pblock (k' + 1) (s + 1) w ((Y + 1 : ℕ) : ℝ)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 := one_le_of_mem_RTg hx
  have hall : ∏ u : Fin (s + 1), (x (Fin.natAdd (k' + 1) u) : ℝ) =
      (∏ u : Fin s, (x (Fin.natAdd (k' + 1) u.castSucc) : ℝ)) * x (Fin.natAdd (k' + 1) (Fin.last s)) :=
    Fin.prod_univ_castSucc _
  have hcond : (∀ C ∈ [gUp (idxInit (∅ : Finset (Fin (k' + 1))) s) E true,
        gDown (idxAll (∅ : Finset (Fin (k' + 1))) (s + 1)) E false] ++ belowL k' (s + 1), C.holds 0 x) ↔
      (∀ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd (s + 1) (Fin.last k'))) ∧
        ((∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) : ℕ) : ℝ) < E ∧
          E ≤ ((∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) : ℕ) : ℝ) *
            (x (Fin.natAdd (k' + 1) (Fin.last s)) : ℝ) := by
    rw [List.forall_mem_append, belowL_holds 0 hx1]
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    rw [gUp_holds _ hE true 0 hx1, gDown_holds _ hE false 0 hx1, prod_idxInit, prod_idxAll, hall,
      Finset.prod_empty, one_mul, one_mul, ite_eq_left rfl]
    push_cast
    exact and_comm
  have hprod : (∏ i, x (Fin.castAdd (s + 1) i)) * (∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc)) *
      x (Fin.natAdd (k' + 1) (Fin.last s)) = ∏ i, x i := by
    rw [Fin.prod_univ_add x, Fin.prod_univ_castSucc (fun u => x (Fin.natAdd (k' + 1) u)), mul_assoc]
  by_cases h : (∀ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) < x (Fin.castAdd (s + 1) (Fin.last k'))) ∧
      ((∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) : ℕ) : ℝ) < E ∧
        E ≤ ((∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) : ℕ) : ℝ) *
          (x (Fin.natAdd (k' + 1) (Fin.last s)) : ℝ)
  · rw [ite_eq_left h, ite_eq_left (hcond.2 h), hprod]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hcond.1 h')]

/-- **Buchstab's tree below the last entry, as chains.** For `1 ≤ w ≤ Y + 1`, `E > 1` and a family
`RTg (k′ + 1) Y Ω` whose tuples are strictly decreasing with last entry at least `w`: the multiples of `∏rt` with no
prime factor below `rt`'s last entry are the leaves of the sizes `s ≤ |[w, Y]|`, the chains of `leafCmpsL` (with the
sign `(−1)^s`, sifted at `w`), plus the stops, the chains of `stopCmpsL` (with the sign `(−1)^{s+1}`, sifted at their
last entry). -/
theorem tree_last (C : Finset ℕ) (f : ℕ → ℂ) (Ω : List (GCmp (k' + 1))) {E : ℝ} (hE : 1 < E) {Y w : ℕ}
    (hw : 1 ≤ w) (hwY : w ≤ Y + 1)
    (hfam : ∀ rt ∈ RTg (k' + 1) Y Ω, StrictAnti rt ∧ w ≤ rt (Fin.last k')) :
    ∑ rt ∈ RTg (k' + 1) Y Ω,
        ∑ n ∈ C, f n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
      ∑ s ∈ range ((primesIco w (Y + 1)).card + 1), (-1 : ℂ) ^ s *
          ∑ x ∈ RTg (k' + 1 + s) Y (leafCmpsL Ω E w ((Y + 1 : ℕ) : ℝ) s),
            ∑ n ∈ C, f n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0) +
        ∑ s ∈ range ((primesIco w (Y + 1)).card + 1), (-1 : ℂ) ^ (s + 1) *
          ∑ x ∈ RTg (k' + 1 + (s + 1)) Y (stopCmpsL Ω E w ((Y + 1 : ℕ) : ℝ) s),
            ∑ n ∈ C, f n *
              (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd (k' + 1) (Fin.last s))) n then 1 else 0) := by
  set T := primesIco w (Y + 1) with hT
  have hE0 : (0 : ℝ) < E := by linarith
  have hrt : ∀ rt ∈ RTg (k' + 1) Y Ω,
      ∑ n ∈ C, f n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ s ∈ range (T.card + 1), (-1 : ℂ) ^ s *
          ∑ y ∈ (Fintype.piFinset fun _ : Fin s => T).filter StrictAnti,
            (if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u, y u : ℕ) : ℝ) < E then
              ∑ n ∈ C, f n * (if (∏ i, rt i) * (∏ u, y u) ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ s ∈ range (T.card + 1), (-1 : ℂ) ^ (s + 1) *
          ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => T).filter StrictAnti,
            (if (∀ u, y u < rt (Fin.last k')) ∧ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
                E ≤ ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
              ∑ n ∈ C, f n * (if (∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s) ∣ n ∧
                rough (y (Fin.last s)) n then 1 else 0) else 0) := by
    intro rt hrt
    obtain ⟨hanti, hwl⟩ := hfam rt hrt
    have hmem : ∀ i, rt i ≤ Y ∧ (rt i).Prime := fun i =>
      SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)
    have hr : ∀ p : ℕ, p.Prime → p ∣ ∏ i, rt i → rt (Fin.last k') ≤ p := by
      intro p hp hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hp (hmem i).2).1 hi]
      exact hanti.antitone (Fin.le_last i)
    have hbZ : rt (Fin.last k') ≤ Y + 1 := by have := (hmem (Fin.last k')).1; omega
    rw [tree_split_below C f hw hwl hbZ hr hE, sum_powerset_desc, sum_stops_by_size]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hinj := (Finset.mem_filter.1 hy).2.injective
      have hall : (∀ p ∈ Finset.univ.image y, p < rt (Fin.last k')) ↔ ∀ u, y u < rt (Fin.last k') :=
        ⟨fun h u => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ u)), fun h p hp => by
          obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
          exact h u⟩
      rw [Finset.prod_image fun u _ v _ h => hinj h]
      simp only [hall]
    · refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hinj : Function.Injective fun u : Fin s => y u.castSucc :=
        fun u v h => Fin.castSucc_injective _ ((Finset.mem_filter.1 hy).2.injective h)
      have hall : (y (Fin.last s) < rt (Fin.last k') ∧
          ∀ p' ∈ Finset.univ.image (fun u : Fin s => y u.castSucc), p' < rt (Fin.last k')) ↔
            ∀ u, y u < rt (Fin.last k') := by
        constructor
        · rintro ⟨h1, h2⟩ u
          induction u using Fin.lastCases with
          | last => exact h1
          | cast u => exact h2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
        · intro h
          refine ⟨h _, fun p hp => ?_⟩
          obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
          exact h _
      rw [Finset.prod_image fun u _ v _ h => hinj h]
      simp only [hall]
  rw [Finset.sum_congr rfl hrt, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, sum_leaves_chainL Ω hE0 s hw hwY
      (fun d => ∑ n ∈ C, f n * (if d ∣ n ∧ rough w n then 1 else 0))]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, sum_stops_chainL Ω hE0 s hw hwY
      (fun d p => ∑ n ∈ C, f n * (if d ∣ n ∧ rough p n then 1 else 0))]

end Cmps

end SieveFillTree

#print axioms SieveFillTree.tree_last
