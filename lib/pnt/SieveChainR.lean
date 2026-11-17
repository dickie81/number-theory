/-
# Splitting a tuple by a set of its indices

Plain statements. `eS` and `merge` are `SieveChain`'s: for a set `S` of indices of `Fin k`, `eS S` is the equivalence
`Fin |S| ⊕ Fin |Sᶜ| ≃ Fin k`, increasing on each part, and `merge S a b` is the tuple with `a` on `S` and `b` on `Sᶜ`.

* `eS_inr_strictMono`: `eS S` is strictly increasing on the part `Sᶜ`.
* `sum_pi_merge`: a sum over the tuples on `Fin k` with entries in `A` is a sum over their parts on `S` and on `Sᶜ`,
  each with entries in `A`, through `merge`.

The file imports `SieveChain.lean`.
-/
import SieveChain

open Real Finset SieveFamily SieveTree SieveRoute SieveChain

namespace SieveChainR

/-! ### Splitting a chain by a set of its indices -/

theorem eS_inr_strictMono {k : ℕ} {S : Finset (Fin k)} : StrictMono (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) := by
  have e : (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) = Sᶜ.orderEmbOfFin rfl := by
    funext v
    exact finSumEquivOfFinset_inr rfl rfl v
  rw [e]
  exact (Sᶜ.orderEmbOfFin rfl).strictMono

/-- A sum over tuples on `Fin k` is a sum over their parts on `S` and on `Sᶜ`. -/
theorem sum_pi_merge {M : Type*} [AddCommMonoid M] {k : ℕ} (S : Finset (Fin k)) (A : Finset ℕ)
    (f : (Fin k → ℕ) → M) :
    ∑ rt ∈ Fintype.piFinset (fun _ : Fin k => A), f rt =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin S.card => A), ∑ b ∈ Fintype.piFinset (fun _ : Fin Sᶜ.card => A),
        f (merge S x b) := by
  rw [← Finset.sum_product' (f := fun x b => f (merge S x b))]
  refine Finset.sum_nbij' (fun rt => (fun u => rt (eS S (Sum.inl u)), fun v => rt (eS S (Sum.inr v))))
    (fun p => merge S p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro rt hrt
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hrt ⊢
    exact ⟨fun u => hrt _, fun v => hrt _⟩
  · rintro ⟨x, b⟩ hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro i
    obtain ⟨y, rfl⟩ := (eS S).surjective i
    rcases y with u | v
    · rw [merge_inl]; exact hp.1 u
    · rw [merge_inr]; exact hp.2 v
  · intro rt _
    exact merge_split rt
  · rintro ⟨x, b⟩ _
    simp only [merge_inl, merge_inr]
  · intro rt _
    simp only [merge_split]

end SieveChainR
