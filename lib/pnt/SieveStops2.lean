/-
# Finite sets of naturals in decreasing order, and roughness

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements.

* `desc s P`: the elements of `P` in decreasing order, as an `s`-tuple, when `P` has `s` elements (`0` otherwise).
  `desc_eq`: it is `P.orderEmbOfFin` read backwards; `desc_strictAnti`, `desc_mem`: it is strictly decreasing with
  values in `P`. `image_desc`: its image is `P`; `desc_image`: a strictly decreasing `s`-tuple is `desc` of its image.
* `rough_iff_le_minFac`: for `k ≥ 2`, `k` has no prime factor below `p` iff `p ≤ minFac k`.

The file imports `SieveCmp.lean` and `SieveStops1.lean`.
-/
import SieveCmp
import SieveStops1

open Real Finset SieveFamily SieveTree SieveCmp SieveRoute

namespace SieveStops2

/-! ### A set of `s` naturals as a strictly decreasing `s`-tuple -/

/-- The elements of `P` in decreasing order, when `P` has `s` elements. -/
noncomputable def desc (s : ℕ) (P : Finset ℕ) : Fin s → ℕ :=
  fun u => if h : P.card = s then P.orderEmbOfFin h (Fin.rev u) else 0

theorem desc_eq {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) :
    desc s P u = P.orderEmbOfFin h (Fin.rev u) := by
  simp [desc, h]

theorem desc_strictAnti {s : ℕ} {P : Finset ℕ} (h : P.card = s) : StrictAnti (desc s P) := by
  intro u v huv
  rw [desc_eq h, desc_eq h]
  exact (P.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.2 huv)

theorem desc_mem {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) : desc s P u ∈ P := by
  rw [desc_eq h]
  exact P.orderEmbOfFin_mem h _

theorem image_desc {s : ℕ} {P : Finset ℕ} (h : P.card = s) : Finset.univ.image (desc s P) = P := by
  conv_rhs => rw [← P.image_orderEmbOfFin_univ h]
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, (desc_eq h u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, by rw [desc_eq h, Fin.rev_rev]⟩

theorem desc_image {s : ℕ} {y : Fin s → ℕ} (hy : StrictAnti y) : desc s (Finset.univ.image y) = y := by
  have hc : (Finset.univ.image y).card = s := by
    rw [Finset.card_image_of_injective _ hy.injective, Finset.card_univ, Fintype.card_fin]
  have hu := Finset.orderEmbOfFin_unique hc (f := y ∘ Fin.rev)
    (fun u => Finset.mem_image_of_mem _ (Finset.mem_univ _)) (hy.comp Fin.rev_strictAnti)
  funext u
  rw [desc_eq hc, ← hu]
  simp [Fin.rev_rev]

variable {j s : ℕ}

/-! ### Roughness and the least prime factor -/

theorem rough_iff_le_minFac {p k : ℕ} (hk : 2 ≤ k) : (∀ p' < p, p'.Prime → ¬ p' ∣ k) ↔ p ≤ Nat.minFac k := by
  constructor
  · intro h
    by_contra hlt
    exact h _ (not_le.1 hlt) (Nat.minFac_prime (by omega)) (Nat.minFac_dvd k)
  · intro h p' hp' hpp hd
    have := Nat.minFac_le_of_dvd hpp.two_le hd
    omega

end SieveStops2
