/-
# The chain's sifted cofactor over the frozen part, in the rest of an estimate given as a hypothesis

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozResCof.lean` evaluates the term of a chain's box over the frozen part of a reversal with
the chain's cofactor in the rest, one part whatever its number of primes, given for each number of the cofactor's
primes an estimate `SieveTypeIIHM.FullEst` of the full tuples (`evIF_froz_sif`). The estimate on a box of cells is
one:

* `evIF_froz_genC`: **the term over the frozen part is evaluated with the chain's cofactor in the rest**, given for
  each number `u ≥ 1` of the cofactor's primes `FullEst L κ (n + u)` for the region with the rest's primes in their
  cells, `q^{lo i} ≤ x_i ≤ q^{hi i}`, and the cofactor's product in its, `lo`, `hi` the ends of the cells of a rest
  at injective positions `r` of the box and of the cofactor's cell after them.

The file imports `SieveAdFrozResCof.lean`.
-/
import SieveAdFrozResCof

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK]

/-- **The term of a chain's box over the frozen part, by an estimate of the tuples with the chain's cofactor in the
rest.** Let `βx` and the chain's box `bx` have cells with `1 ≤ lo ≤ hi ≤ DEN`, `e₁, e₂ ≤ DEN`, and the chain's upper
ends with `e₂` sum to at most `DEN − 2`. Let the rest be at the injective positions `r` of the box (frozen primes
first, then the chain's) and the chain's cofactor, with `lo j = κ·lo(r j)`, `hi j = κ·hi(r j)`,
`lo (n + 1) = κ·max(DEN − e₂ − Σhi − 1, lo₀)` and `hi (n + 1) = κ·(DEN − e₁ − Σlo + 1)`, for `κ = L/DEN`. If for each
number `u ≥ 1` of the cofactor's primes `FullEst L κ (n + u)` holds for the region with the rest's primes in their
cells and the cofactor's product in its, the term of the chain's box over the frozen part is evaluated
(`evIF_froz_sif`). -/
theorem evIF_froz_genC {e₁ e₂ s : ℕ} {βx : Fin (s + 1) → Cell}
    (hβ : ∀ i, 1 ≤ (βx i).1 ∧ (βx i).1 ≤ (βx i).2 ∧ (βx i).2 ≤ DEN) (he₁ : e₁ ≤ DEN) (he₂ : e₂ ≤ DEN) {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (hb : ∀ j, 1 ≤ (bx j).1 ∧ (bx j).1 ≤ (bx j).2 ∧ (bx j).2 ≤ DEN)
    (hshi : e₂ + ∑ j, (bx j).2 + 2 ≤ DEN)
    {κ : ℝ} (hκ : κ = L / DEN) {n : ℕ} (r : Fin (n + 1) → Fin (s + 1 + (k' + 1))) (hr : Function.Injective r)
    (lo hi : ℕ → ℝ) (hlo : ∀ j : Fin (n + 1), lo j = κ * ((Fin.append βx bx (r j)).1 : ℝ))
    (hhi : ∀ j : Fin (n + 1), hi j = κ * ((Fin.append βx bx (r j)).2 : ℝ))
    (hlon : lo (n + 1) = κ * ((maxN (DEN - e₂ - ∑ j, (bx j).2 - 1) (bx (Fin.last k')).1 : ℕ) : ℝ))
    (hhin : hi (n + 1) = κ * ((DEN - e₁ - ∑ j, (bx j).1 + 1 : ℕ) : ℝ))
    (hfull : ∀ u : ℕ, 1 ≤ u → SieveTypeIIHM.FullEst L κ (n + u) (fun q x =>
      (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x (Fin.castLE (by omega) i) ∧
        (x (Fin.castLE (by omega) i) : ℝ) ≤ (q : ℝ) ^ hi i) ∧
      (q : ℝ) ^ lo (n + 1) ≤
          ((∏ i ∈ Finset.univ.filter (fun i : Fin (n + u + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i : ℕ) : ℝ) ∧
        ((∏ i ∈ Finset.univ.filter (fun i : Fin (n + u + 1) => SieveTypeIIHM.sifGrp n i = n + 1), x i : ℕ) : ℝ) ≤
          (q : ℝ) ^ hi (n + 1))) :
    EvIF (fun q => frozS q e₁ e₂ βx) frozR bx := by
  refine evIF_froz_sif hβ he₁ he₂ hb hshi hκ r hr
    (Reg := fun q xs m => (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ xs i ∧ (xs i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
      (q : ℝ) ^ lo (n + 1) ≤ m ∧ (m : ℝ) ≤ (q : ℝ) ^ hi (n + 1)) ?_ hfull
  intro q _ xs m hxs hm1 hm2
  have hqx : ∀ e : ℕ, (q : ℝ) ^ (κ * (e : ℝ)) = Xe q e := fun e => by rw [hκ, qpow_eq]; rfl
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [hlo i, hhi i, hqx, hqx]
    exact ⟨(hxs i).1, (hxs i).2.le⟩
  · rw [hlon, hqx]
    exact hm1
  · rw [hhin, hqx]
    exact hm2

end SieveAd

#print axioms SieveAd.evIF_froz_genC
