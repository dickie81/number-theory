/-
# Proposition 6 with the bilinear estimate: a family of chains split into two blocks

Plain statements. `GCmp`, `RTg`, `eS` and `merge` are `SieveChain`'s; `primesIco w z` is `SieveTree`'s. `DT n w Y` is
the set of strictly decreasing `n`-tuples of primes of `[w, Y]`.

* `sum_RTg_split`: if the chains of `RTg K Y Ω` are strictly decreasing with entries at least `w`, a sum over them is a
  sum over the pairs `(y₁, y₂) ∈ DT |S| w Y × DT |Sᶜ| w Y` whose merge satisfies `Ω`.
* `form_merge`: a comparison of the merge is `c + Σ_u e(u) log y₁(u) + Σ_v e(v) log y₂(v)`.
* `ite_forall_eq_prod`: `[every comparison of a list holds]` is the product of the indicators of its entries.
* `RTg_nz`: dropping the comparisons with no nonzero coefficient leaves a family empty or the same.
* `form_le`: a comparison's form at a tuple with entries in `[1, Y]` is at most `c + K log Y`.

The file imports `SieveP6Tree.lean`.
-/
import SieveP6Tree

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain

namespace SieveP6Split

open Classical

/-- The strictly decreasing `n`-tuples of primes of `[w, Y]`. -/
noncomputable def DT (n w Y : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => primesIco w (Y + 1)).filter StrictAnti

theorem mem_DT {n w Y : ℕ} {y : Fin n → ℕ} :
    y ∈ DT n w Y ↔ StrictAnti y ∧ ∀ i, (y i).Prime ∧ w ≤ y i ∧ y i ≤ Y := by
  simp only [DT, Finset.mem_filter, Fintype.mem_piFinset, mem_primesIco]
  constructor
  · rintro ⟨h, ha⟩
    exact ⟨ha, fun i => ⟨(h i).2.2, (h i).1, by have := (h i).2.1; omega⟩⟩
  · rintro ⟨ha, h⟩
    exact ⟨fun i => ⟨(h i).2.1, by have := (h i).2.2; omega, (h i).1⟩, ha⟩

section Split

variable {K : ℕ} (S : Finset (Fin K))

/-- **A family of chains split into two blocks.** If the chains of `RTg K Y Ω` are strictly decreasing with entries at
least `w`, a sum over them is a sum over the pairs of strictly decreasing tuples of primes of `[w, Y]` on `S` and on
`Sᶜ` whose merge satisfies `Ω`. -/
theorem sum_RTg_split {M : Type*} [AddCommMonoid M] {Y w : ℕ} (Ω : List (GCmp K))
    (hreg : ∀ x ∈ RTg K Y Ω, StrictAnti x ∧ ∀ i, w ≤ x i) (F : (Fin K → ℕ) → M) :
    ∑ x ∈ RTg K Y Ω, F x = ∑ y₁ ∈ DT S.card w Y, ∑ y₂ ∈ DT Sᶜ.card w Y,
      if (∀ C ∈ Ω, C.holds 0 (merge S y₁ y₂)) then F (merge S y₁ y₂) else 0 := by
  rw [RTg, Finset.sum_filter, SieveChainR.sum_pi_merge S (SieveTypeIIU.primesLe Y)]
  have hsub : ∀ n, DT n w Y ⊆ Fintype.piFinset (fun _ : Fin n => SieveTypeIIU.primesLe Y) := fun n y hy => by
    obtain ⟨-, h⟩ := mem_DT.1 hy
    exact Fintype.mem_piFinset.2 fun i => SieveTypeIIU.mem_primesLe.2 ⟨(h i).2.2, (h i).1⟩
  -- a merge satisfying `Ω` has both parts in `DT`
  have hparts : ∀ y₁ ∈ Fintype.piFinset (fun _ : Fin S.card => SieveTypeIIU.primesLe Y),
      ∀ y₂ ∈ Fintype.piFinset (fun _ : Fin Sᶜ.card => SieveTypeIIU.primesLe Y),
      (∀ C ∈ Ω, C.holds 0 (merge S y₁ y₂)) → y₁ ∈ DT S.card w Y ∧ y₂ ∈ DT Sᶜ.card w Y := by
    intro y₁ hy₁ y₂ hy₂ hΩ
    have hmem : merge S y₁ y₂ ∈ RTg K Y Ω := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hΩ⟩
      obtain ⟨t, rfl⟩ := (eS S).surjective i
      rcases t with u | v
      · rw [merge_inl]; exact Fintype.mem_piFinset.1 hy₁ u
      · rw [merge_inr]; exact Fintype.mem_piFinset.1 hy₂ v
    obtain ⟨ha, hw⟩ := hreg _ hmem
    have h1 : y₁ = fun u => merge S y₁ y₂ (eS S (Sum.inl u)) := funext fun u => (merge_inl _ _ u).symm
    have h2 : y₂ = fun v => merge S y₁ y₂ (eS S (Sum.inr v)) := funext fun v => (merge_inr _ _ v).symm
    refine ⟨mem_DT.2 ⟨?_, fun u => ?_⟩, mem_DT.2 ⟨?_, fun v => ?_⟩⟩
    · rw [h1]; exact ha.comp_strictMono eS_inl_strictMono
    · have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hy₁ u)
      refine ⟨this.2, ?_, this.1⟩
      rw [h1]; exact hw _
    · rw [h2]; exact ha.comp_strictMono SieveChainR.eS_inr_strictMono
    · have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hy₂ v)
      refine ⟨this.2, ?_, this.1⟩
      rw [h2]; exact hw _
  rw [← Finset.sum_subset (hsub S.card) fun y₁ hy₁ hn => Finset.sum_eq_zero fun y₂ hy₂ =>
    ite_eq_right fun hΩ => hn (hparts y₁ hy₁ y₂ hy₂ hΩ).1]
  refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
  exact (Finset.sum_subset (hsub Sᶜ.card) fun y₂ hy₂ hn =>
    ite_eq_right fun hΩ => hn (hparts y₁ (hsub _ hy₁) y₂ hy₂ hΩ).2).symm

/-- A comparison of the merge, as `c + Σ_u e₁(u) log y₁(u) + Σ_v e₂(v) log y₂(v)`. -/
theorem form_merge (C : GCmp K) (m : ℕ) (y₁ : Fin S.card → ℕ) (y₂ : Fin Sᶜ.card → ℕ) :
    C.form m (merge S y₁ y₂) = C.c m + ∑ u, C.e (eS S (Sum.inl u)) * Real.log (y₁ u) +
      ∑ v, C.e (eS S (Sum.inr v)) * Real.log (y₂ v) := by
  unfold GCmp.form
  rw [sum_split (S := S) (fun i => C.e i * Real.log (merge S y₁ y₂ i))]
  simp only [merge_inl, merge_inr]
  ring

end Split

/-- The comparisons of a list, as an indexed family: all hold iff each does. -/
theorem forall_mem_iff_get {α : Type*} {P : α → Prop} {l : List α} :
    (∀ x ∈ l, P x) ↔ ∀ j : Fin l.length, P (l.get j) := by
  rw [List.forall_mem_iff_forall_getElem]
  constructor
  · intro h j
    exact h j j.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

/-- `[all of the comparisons hold] = ∏_j [the j-th holds]`. -/
theorem ite_forall_eq_prod {α M : Type*} [CommMonoidWithZero M] (P : α → Prop) (l : List α) (F : M) :
    (if ∀ x ∈ l, P x then F else 0) = (∏ j : Fin l.length, if P (l.get j) then (1 : M) else 0) * F := by
  rw [Fintype.prod_boole]
  by_cases h : ∀ x ∈ l, P x
  · rw [ite_eq_left h, ite_eq_left (forall_mem_iff_get.1 h), one_mul]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (forall_mem_iff_get.2 h')), zero_mul]

/-! ### Constant comparisons and the size of a form -/

/-- A comparison with no nonzero coefficient holds at every tuple or at none. -/
theorem holds_of_zero {K : ℕ} {C : GCmp K} (h : ∀ i, C.e i = 0) (m : ℕ) (x x' : Fin K → ℕ) :
    C.holds m x ↔ C.holds m x' := by
  unfold GCmp.holds GCmp.form
  simp [h]

/-- Dropping the comparisons with no nonzero coefficient leaves the family empty or the same. -/
theorem RTg_nz (K Y : ℕ) (Ω : List (GCmp K)) :
    RTg K Y Ω = ∅ ∨ RTg K Y Ω = RTg K Y (Ω.filter fun C => decide (∃ i, C.e i ≠ 0)) := by
  by_cases h : ∀ C ∈ Ω, (∀ i, C.e i = 0) → C.holds 0 (fun _ => 1)
  · right
    unfold RTg
    refine Finset.filter_congr fun x _ => ⟨fun hx C hC => hx C (List.mem_filter.1 hC).1, fun hx C hC => ?_⟩
    by_cases hz : ∃ i, C.e i ≠ 0
    · exact hx C (List.mem_filter.2 ⟨hC, decide_eq_true hz⟩)
    · push Not at hz
      exact (holds_of_zero hz 0 _ _).1 (h C hC hz)
  · left
    push Not at h
    obtain ⟨C, hC, hz, hf⟩ := h
    refine Finset.eq_empty_of_forall_notMem fun x hx => hf ?_
    exact (holds_of_zero hz 0 _ _).1 ((Finset.mem_filter.1 hx).2 C hC)

/-- A comparison's form at a tuple with entries in `[1, Y]` is at most `c + K log Y`. -/
theorem form_le {K : ℕ} (C : GCmp K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ i, 1 ≤ x i) {Y : ℝ}
    (hY : ∀ i, (x i : ℝ) ≤ Y) : C.form m x ≤ C.c m + K * Real.log Y := by
  unfold GCmp.form
  have h : ∀ i, C.e i * Real.log (x i) ≤ Real.log Y := fun i => by
    have h1 : (1 : ℝ) ≤ x i := by exact_mod_cast hx i
    have h2 : 0 ≤ Real.log (x i) := Real.log_nonneg h1
    have h3 : Real.log (x i) ≤ Real.log Y := Real.log_le_log (by linarith) (hY i)
    rcases C.he i with he | he | he <;> rw [he] <;> linarith
  have := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin K))) => h i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

end SieveP6Split
