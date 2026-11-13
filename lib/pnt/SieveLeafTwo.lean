/-
# The leaves by the Type II estimate in two variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

A leaf of the sieve's tree is a family of tuples `x` of primes at least `w`, and its term is the sum over `x` of
the `w`-rough multiples `n ∈ (N₁, N₂]` of `∏x` (`SieveP6TreeLeaves`). This file evaluates such a term by the estimate
in two variables, with the cofactor `n/∏x` as one of the two variables: the first variable is the product of the
primes of `x` on a set `S`, the rest is the product of those on a set `Sr`, and the second variable is all the rest
of `n`, the cofactor (and the primes of `x` off `S ∪ Sr`, if any).

Plain statements. `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `fullLW`: the comparisons of the full tuple `(x, y)`: the region `Ω` of `x`, `y` non-increasing and at least `w`,
  and the range `N₁ < ∏x·∏y ≤ N₂`; `fullLW_holds0` says so, and `sum_fullLW_eq` puts the pairs `(x, y)` as the
  tuples of `fullLW`.
* `leaf2_bound`: **leaves with two marked products.** Assume Proposition 3′ in two variables at `L` on `Rg` and
  `0 < L ≤ 5/2`. Fix `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀`, a unit `a`
  mod `q` and `w ≥ 2` with `q^{e₀} ≤ w`: let `x` run over the `K`-tuples of primes up to `N₂` that satisfy at most
  `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such tuple with entries at least `w`,
  `A < ∏_{i∈S} x_i ≤ B` and `Ar < ∏_{i∈Sr} x_i ≤ Br`, where `S` and `Sr ≠ ∅` are disjoint, `A, B, Br ≥ 1`,
  `B·Br ≤ N₁` and `Rg u v` holds for `u ∈ [log_q A, log_q B]` with `⌊N₁/Br⌋ ≤ 4q^{u+v}` and
  `q^{u+v} ≤ ⌊N₂/(Ar + 1)⌋`. Then the `w`-rough multiples `n ∈ (N₁, N₂]` of `∏x`, summed over `x`, have
  `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `typeIITwoAt_leaf`: Proposition 3′ in two variables on the leaves' region `SieveTypeIIHM.LeafZone L`, from the
  fourth moment (`SieveTypeIIHM.typeII_two_gen4`, `SieveTypeIIHM.zone_leaf`) and the curve `g7d`.

The proof of `leaf2_bound` is that of `SieveTwoTerm.chain2_bound` with the cofactor rough at `w` in place of the
chain's last entry: the cofactor is the product of a non-increasing tuple `y` of at most `K_max = ⌈(L + 1)/e₀⌉`
primes at least `w` (`SieveChain.sum_mult_eq`, `sum_rough_tuples`); for each length, `sum_fullLW_eq` and
`SieveTwoChain.chain_two` on the tuples `(x, y)`.

The file imports `SieveTwoTerm.lean` and `SieveLeafZone.lean`.
-/
import SieveTwoTerm
import SieveLeafZone

open Real Finset Filter SieveFamily SieveTree SieveChain SieveP6Chain SieveFamilyTwo SieveTwoChain

namespace SieveLeafTwo

open Classical

/-! ### The full tuples of a leaf -/

/-- `y ≥ w`, on the full tuple `(x, y)`. -/
noncomputable def yLow (K t : ℕ) (w : ℝ) : List (GCmp (K + t)) :=
  (List.finRange t).map fun a => gDown {Fin.natAdd K a} w false

theorem yLow_holds {K t : ℕ} {w : ℝ} (hw : 0 < w) (m : ℕ) {z : Fin (K + t) → ℕ} (hz : ∀ i, 1 ≤ z i) :
    (∀ C ∈ yLow K t w, C.holds m z) ↔ ∀ a : Fin t, w ≤ (z (Fin.natAdd K a) : ℝ) := by
  unfold yLow
  simp only [List.forall_mem_map, List.mem_finRange, true_implies]
  refine forall_congr' fun a => ?_
  rw [gDown_holds _ hw false m hz]
  simp only [Bool.false_eq_true, ite_false, Finset.prod_singleton]

/-- The comparisons of the full tuple `(x, y)` of a leaf: the region `Ω` of `x`, `y` non-increasing and at least
`w`, and the range `N₁ < ∏x·∏y ≤ N₂`. -/
noncomputable def fullLW (K t : ℕ) (Ω : List (GCmp K)) (w N₁ N₂ : ℝ) : List (GCmp (K + t)) :=
  Ω.map (liftChain (t := t)) ++ yPairs K t ++ yLow K t w ++ [grangeLo N₁, grangeHi N₂]

theorem length_fullLW_le (K t : ℕ) (Ω : List (GCmp K)) (w N₁ N₂ : ℝ) :
    (fullLW K t Ω w N₁ N₂).length ≤ Ω.length + t * t + t + 2 := by
  unfold fullLW yLow
  simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons, List.length_nil]
  have := length_yPairs_le K t
  omega

/-- The comparisons of the full tuple have the same constant at `m = 0` and at `m = 1`. -/
theorem fullLW_c {K t : ℕ} (Ω : List (GCmp K)) (w N₁ N₂ : ℝ) :
    ∀ C ∈ fullLW K t Ω w N₁ N₂, C.c 0 = C.c 1 := by
  intro C hC
  unfold fullLW at hC
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with ((⟨C', -, rfl⟩ | hC) | hC) | rfl | rfl
  · rfl
  · obtain ⟨a, b, -, rfl⟩ := mem_yPairs.1 hC
    rfl
  · unfold yLow at hC
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hC
    rfl
  · show Real.log ((0 : ℕ) : ℝ) - Real.log N₁ = Real.log ((1 : ℕ) : ℝ) - Real.log N₁
    simp
  · show Real.log N₂ - Real.log ((0 : ℕ) : ℝ) = Real.log N₂ - Real.log ((1 : ℕ) : ℝ)
    simp

theorem fullLW_holds {K t : ℕ} (Ω : List (GCmp K)) {w N₁ N₂ : ℝ} (hw : 0 < w) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (x : Fin K → ℕ) (y : Fin t → ℕ) (hx : ∀ i, 1 ≤ x i) (hy : ∀ a, 1 ≤ y a) :
    (∀ C ∈ fullLW K t Ω w N₁ N₂, C.holds 1 (Fin.append x y)) ↔
      (∀ C ∈ Ω, C.holds 0 x) ∧ (∀ a b : Fin t, a ≤ b → y b ≤ y a) ∧ (∀ a, w ≤ (y a : ℝ)) ∧
        N₁ < (∏ i, (x i : ℝ)) * ∏ a, (y a : ℝ) ∧ (∏ i, (x i : ℝ)) * ∏ a, (y a : ℝ) ≤ N₂ := by
  have hz : ∀ i, 1 ≤ Fin.append x y i := fun i => by
    refine Fin.addCases (fun i => ?_) (fun a => ?_) i
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hy a
  have hprod : ∏ i, ((Fin.append x y i : ℕ) : ℝ) = (∏ i, (x i : ℝ)) * ∏ a, (y a : ℝ) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  unfold fullLW
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true]
  rw [yPairs_holds 1 hz, yLow_holds hw 1 hz, grangeLo_holds hN₁ le_rfl hz, grangeHi_holds hN₂ le_rfl hz]
  simp only [Fin.append_right, Nat.cast_one, one_mul, hprod]
  have hlc : (∀ C ∈ Ω, (liftChain (t := t) C).holds 1 (Fin.append x y)) ↔ ∀ C ∈ Ω, C.holds 0 x := by
    refine forall₂_congr fun C _ => ?_
    rw [liftChain_holds]
    simp only [Fin.append_left]
  rw [hlc]
  tauto

/-- `fullLW_holds` at `m = 0`. -/
theorem fullLW_holds0 {K t : ℕ} (Ω : List (GCmp K)) {w N₁ N₂ : ℝ} (hw : 0 < w) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (x : Fin K → ℕ) (y : Fin t → ℕ) (hx : ∀ i, 1 ≤ x i) (hy : ∀ a, 1 ≤ y a) :
    (∀ C ∈ fullLW K t Ω w N₁ N₂, C.holds 0 (Fin.append x y)) ↔
      (∀ C ∈ Ω, C.holds 0 x) ∧ (∀ a b : Fin t, a ≤ b → y b ≤ y a) ∧ (∀ a, w ≤ (y a : ℝ)) ∧
        N₁ < (∏ i, (x i : ℝ)) * ∏ a, (y a : ℝ) ∧ (∏ i, (x i : ℝ)) * ∏ a, (y a : ℝ) ≤ N₂ := by
  rw [← fullLW_holds Ω hw hN₁ hN₂ x y hx hy]
  exact forall₂_congr fun C hC => SieveTwoTerm.holds_zero_iff_one C (fullLW_c Ω w N₁ N₂ C hC) _

/-- **The leaves with their cofactor's tuples are the full tuples.** For `w ≥ 1` and `1 ≤ N₁ ≤ N₂ ≤ Y`: the tuples
`x` of the region `Ω` times the non-increasing `t`-tuples `y` of primes at least `w`, with `N₁ < ∏x·∏y ≤ N₂`, are
the `(K + t)`-tuples of primes up to `Y` that satisfy `fullLW`. -/
theorem sum_fullLW_eq {M : Type*} [AddCommMonoid M] {K : ℕ} (Ω : List (GCmp K)) {w Y N₁ N₂ : ℕ} (t : ℕ)
    (hw : 1 ≤ w) (hN₁ : 1 ≤ N₁) (hN₁₂ : N₁ ≤ N₂) (hN₂ : N₂ ≤ Y) (F : ℕ → M) :
    ∑ x ∈ RTg K Y Ω, ∑ y ∈ SieveRoughTuple.tuples w Y t,
        (if N₁ < (∏ i, x i) * ∏ a, y a ∧ (∏ i, x i) * ∏ a, y a ≤ N₂ then F ((∏ i, x i) * ∏ a, y a) else 0) =
      ∑ z ∈ RTg (K + t) Y (fullLW K t Ω w N₁ N₂), F (∏ i, z i) := by
  set D := ((RTg K Y Ω) ×ˢ (Fintype.piFinset (fun _ : Fin t => SieveTypeIIU.primesLe Y))).filter
    (fun p => ((∀ i j : Fin t, i ≤ j → p.2 j ≤ p.2 i) ∧ (∀ i, w ≤ p.2 i) ∧ ∏ a, p.2 a ≤ Y) ∧
      (N₁ < (∏ i, p.1 i) * ∏ a, p.2 a ∧ (∏ i, p.1 i) * ∏ a, p.2 a ≤ N₂)) with hD
  have hL : ∑ x ∈ RTg K Y Ω, ∑ y ∈ SieveRoughTuple.tuples w Y t,
      (if N₁ < (∏ i, x i) * ∏ a, y a ∧ (∏ i, x i) * ∏ a, y a ≤ N₂ then F ((∏ i, x i) * ∏ a, y a) else 0) =
      ∑ p ∈ D, F ((∏ i, p.1 i) * ∏ a, p.2 a) := by
    rw [hD, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [SieveRoughTuple.tuples, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    simp only [ite_and]
  rw [hL]
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast (show 0 < N₂ by omega)
  refine Finset.sum_nbij' (fun p => Fin.append p.1 p.2)
    (fun z => (fun i => z (Fin.castAdd t i), fun a => z (Fin.natAdd K a))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hxY, hxΩ⟩, hyY⟩, ⟨hanti, hlow, -⟩, hlo, hhi⟩ := hp
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hxY i)).2.one_lt.le
    have hy1 : ∀ a, 1 ≤ y a := fun a => (SieveTypeIIU.mem_primesLe.1 (hyY a)).2.one_lt.le
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, (fullLW_holds0 Ω hw0 hN₁0 hN₂0 x y hx1 hy1).2
      ⟨hxΩ, hanti, fun a => by exact_mod_cast hlow a, ?_, ?_⟩⟩
    · refine Fin.addCases (fun i => ?_) (fun a => ?_) i
      · rw [Fin.append_left]
        exact hxY i
      · rw [Fin.append_right]
        exact hyY a
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · intro z hz
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
    obtain ⟨hzY, hzΩ⟩ := hz
    have hx1 : ∀ i, 1 ≤ z (Fin.castAdd t i) := fun i => (SieveTypeIIU.mem_primesLe.1 (hzY _)).2.one_lt.le
    have hy1 : ∀ a, 1 ≤ z (Fin.natAdd K a) := fun a => (SieveTypeIIU.mem_primesLe.1 (hzY _)).2.one_lt.le
    rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
    obtain ⟨hΩ', hanti, hlow, hlo, hhi⟩ := (fullLW_holds0 Ω hw0 hN₁0 hN₂0 _ _ hx1 hy1).1 hzΩ
    have hlo' : N₁ < (∏ i, z (Fin.castAdd t i)) * ∏ a, z (Fin.natAdd K a) := by exact_mod_cast hlo
    have hhi' : (∏ i, z (Fin.castAdd t i)) * ∏ a, z (Fin.natAdd K a) ≤ N₂ := by exact_mod_cast hhi
    have hpos : 0 < ∏ i, z (Fin.castAdd t i) := Finset.prod_pos fun i _ => hx1 i
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset]
    exact ⟨⟨⟨fun i => hzY _, hΩ'⟩, fun a => hzY _⟩,
      ⟨hanti, fun a => by exact_mod_cast hlow a, le_trans (Nat.le_mul_of_pos_left _ hpos) (hhi'.trans hN₂)⟩,
      hlo', hhi'⟩
  · rintro ⟨x, y⟩ _
    refine Prod.ext (funext fun i => ?_) (funext fun a => ?_)
    · exact Fin.append_left x y i
    · exact Fin.append_right x y a
  · intro z _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨x, y⟩ _
    have hprod : ∏ i, Fin.append x y i = (∏ i, x i) * ∏ a, y a := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    show F ((∏ i, x i) * ∏ a, y a) = F (∏ i, Fin.append x y i)
    rw [hprod]

/-! ### Leaves with two marked products -/

set_option maxHeartbeats 1600000 in
/-- **Leaves with two marked products.** Assume Proposition 3′ in two variables at `L` on `Rg` (`hII`) and
`0 < L ≤ 5/2`. Fix `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀`, a unit `a`
mod `q` and `w ≥ 2` with `q^{e₀} ≤ w`: let `x` run over the `K`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at
most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such tuple with entries at least `w`,
`A < ∏_{i∈S} x_i ≤ B` and `Ar < ∏_{i∈Sr} x_i ≤ Br`, where `S` and `Sr ≠ ∅` are disjoint, `A, B, Br ≥ 1`,
`B·Br ≤ N₁ = ⌊q^L⌋` and `Rg u v` holds for `u ∈ [log_q A, log_q B]` with `⌊N₁/Br⌋ ≤ 4q^{u+v}` and
`q^{u+v} ≤ ⌊N₂/(Ar + 1)⌋`. Then the `w`-rough multiples `n ∈ (N₁, N₂]` of `∏x`, summed over `x`, have
`|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. The second variable is the cofactor `n/∏x` (with the primes of `x` off
`S ∪ Sr`). -/
theorem leaf2_bound {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 5 / 2) {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) {e₀ : ℝ}
    (he₀ : 0 < e₀) (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a → ∀ w : ℕ, 2 ≤ w →
      (q : ℝ) ^ e₀ ≤ w →
      ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)) (A B Ar Br : ℕ), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) → 1 ≤ A → 1 ≤ B → 1 ≤ Br →
      B * Br ≤ ⌊(q : ℝ) ^ L⌋₊ →
      (∀ u v : ℝ, Real.logb q A ≤ u → u ≤ Real.logb q B →
        ((⌊(q : ℝ) ^ L⌋₊ / Br : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u + v) →
        (q : ℝ) ^ (u + v) ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (Ar + 1) : ℕ) : ℝ) → Rg u v) →
      (∀ x : Fin K → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ Ω, C.holds 0 x) →
        (∀ i, w ≤ x i) ∧ A < ∏ i ∈ S, x i ∧ ∏ i ∈ S, x i ≤ B ∧
          Ar < ∏ i ∈ Sr, x i ∧ ∏ i ∈ Sr, x i ≤ Br) →
      ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith
  have H := fun t : ℕ => chain_two hII hL0 hL he₀ (K + t) (J₀ + Kmax * Kmax + Kmax + 2) hΛ'
  choose δf hδf q₀f hq₀f using H
  have hne : (Finset.range (Kmax + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = (Finset.range (Kmax + 1)).inf' hne δf := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact (Finset.lt_inf'_iff hne).2 fun t _ => hδf t
  have hδ₀le : ∀ t ≤ Kmax, δ₀ ≤ δf t := fun t ht => by
    rw [hδ₀def]
    exact Finset.inf'_le δf (Finset.mem_range.2 (by omega))
  have hev := (tendsto_rpow_atTop (half_pos hδ₀)).eventually_ge_atTop ((Kmax : ℝ) + 1)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀ / 2, half_pos hδ₀, max (max ((Finset.range (Kmax + 1)).sup q₀f) q₂) 3, ?_⟩
  intro q _ hq a ha w hw2 hwq S Sr Ω A B Ar Br hdisj hSr hΩlen hΩc hA hB1 hBr1 hBBr hR hreg
  have hqK := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (1 : ℝ) ≤ q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1' hL0.le
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
  -- the tuples' length
  have hpK : ∀ p : ℕ, (q : ℝ) ^ e₀ ≤ p → N₂ < p ^ (Kmax + 1) := by
    intro p hp
    have hK : (L + 1 : ℝ) ≤ e₀ * (Kmax + 1) := by
      have := Nat.le_ceil ((L + 1) / e₀)
      rw [← hKmax, div_le_iff₀ he₀] at this
      nlinarith
    have hpow : (q : ℝ) ^ (L + 1 : ℝ) ≤ (p : ℝ) ^ (Kmax + 1) := by
      calc (q : ℝ) ^ (L + 1 : ℝ) ≤ (q : ℝ) ^ (e₀ * (Kmax + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hK
        _ = ((q : ℝ) ^ e₀) ^ (Kmax + 1) := by rw [Real.rpow_mul hq0.le, ← Real.rpow_natCast]; push_cast; ring_nf
        _ ≤ (p : ℝ) ^ (Kmax + 1) := pow_le_pow_left₀ (by positivity) hp _
    have hlt : (N₂ : ℝ) < (q : ℝ) ^ (L + 1 : ℝ) := by
      calc (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := hN₂le
        _ < 3 * (q : ℝ) ^ L := by linarith
        _ ≤ (q : ℝ) * (q : ℝ) ^ L := by nlinarith
        _ = (q : ℝ) ^ (L + 1 : ℝ) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
    exact_mod_cast lt_of_lt_of_le hlt hpow
  -- each tuple: its multiples as cofactor tuples
  have hRT : ∀ x ∈ RTg K N₂ Ω, (∀ i, (x i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 x) := by
    intro x hx
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hx
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hx.1 i)).2, hx.2⟩
  have hterm : ∀ x ∈ RTg K N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0) =
        ∑ t ∈ Finset.range (Kmax + 1), ∑ y ∈ SieveRoughTuple.tuples w N₂ t,
          (if N₁ < (∏ i, x i) * ∏ a, y a ∧ (∏ i, x i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, x i) * ∏ a, y a) else 0) := by
    intro x hx
    obtain ⟨hxp, hxΩ⟩ := hRT x hx
    obtain ⟨hge, -⟩ := hreg x hxp hxΩ
    have hW0 : 0 < ∏ i, x i := Finset.prod_pos fun i _ => (hxp i).pos
    have hWr : rough w (∏ i, x i) := by
      intro ℓ hℓw hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hxp i)).1 hi] at hℓw
      have := hge i
      omega
    rw [sum_mult_eq (dw q a) hW0 hWr]
    exact sum_rough_tuples hw2 hN₂1
      (fun k => if N₁ < (∏ i, x i) * k ∧ (∏ i, x i) * k ≤ N₂ then dw q a ((∏ i, x i) * k) else 0) Kmax
      (hpK _ hwq)
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hBBr0 : 0 < B * Br := Nat.mul_pos hB1 hBr1
  have hlogN₂ : Real.log (N₂ : ℝ) ≤ (L + 1) * Real.log q := by
    have h1 : (N₂ : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      nlinarith
    have h2 := Real.log_le_log (by exact_mod_cast hN₂1) h1
    rwa [Real.log_rpow hq0] at h2
  -- each size `t`
  have hbound : ∀ t ∈ Finset.range (Kmax + 1),
      ‖∑ x ∈ RTg K N₂ Ω, ∑ y ∈ SieveRoughTuple.tuples w N₂ t,
          (if N₁ < (∏ i, x i) * ∏ a, y a ∧ (∏ i, x i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, x i) * ∏ a, y a) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀) := by
    intro t ht
    have htK : t ≤ Kmax := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    rw [sum_fullLW_eq Ω t (by omega) hN₁1 hN₁N₂ le_rfl (dw q a)]
    have hq' : q₀f t ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_range.2 (by omega)))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    obtain ⟨S₁, hS₁⟩ : ∃ T : Finset (Fin (K + t)), T = S.map (Fin.castAddEmb t) := ⟨_, rfl⟩
    obtain ⟨Sr', hSr'⟩ : ∃ T : Finset (Fin (K + t)), T = Sr.map (Fin.castAddEmb t) := ⟨_, rfl⟩
    have hd' : Disjoint S₁ Sr' := by rw [hS₁, hSr']; exact (Finset.disjoint_map _).2 hdisj
    have hd12 : Disjoint S₁ (S₁ ∪ Sr')ᶜ :=
      Finset.disjoint_left.2 fun i hi hic => (Finset.mem_compl.1 hic) (Finset.mem_union_left _ hi)
    have hrest : (S₁ ∪ (S₁ ∪ Sr')ᶜ)ᶜ.Nonempty := by
      obtain ⟨i, hi⟩ := hSr
      refine ⟨Fin.castAdd t i, ?_⟩
      have hiS : Fin.castAdd t i ∈ Sr' := by rw [hSr']; exact Finset.mem_map_of_mem _ hi
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.1 hd' hiS, fun h => (Finset.mem_compl.1 h) (Finset.mem_union_right _ hiS)⟩
    have hprodAll : ∀ z : Fin (K + t) → ℕ,
        ∏ i, z i = (∏ i ∈ S₁, z i) * (∏ i ∈ Sr', z i) * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i := fun z => by
      rw [← Finset.prod_union hd', Finset.prod_mul_prod_compl]
    have hBrN : Br ≤ N₁ := le_trans (Nat.le_mul_of_pos_left Br hB1) hBBr
    refine (hq₀f t q hq' a ha S₁ (S₁ ∪ Sr')ᶜ hd12 hrest (fullLW K t Ω w N₁ N₂) ?_ ?_ A B (N₁ / (B * Br))
      (N₂ / ((A + 1) * (Ar + 1))) (N₁ / Br) (N₂ / (Ar + 1)) hA (Nat.div_pos hBBr hBBr0) (Nat.div_pos hBrN hBr1)
      ((Nat.cast_le.2 (Nat.div_le_self _ _)).trans hN₂le) (fun u v h1 h2 _ _ h5 h6 => hR u v h1 h2 h5 h6)
      ?_).trans ?_
    · refine (length_fullLW_le K t Ω w N₁ N₂).trans ?_
      have : t * t ≤ Kmax * Kmax := Nat.mul_le_mul htK htK
      omega
    · -- the constants
      intro C hC
      have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
      have hLl : 0 ≤ (L + 1) * Real.log q := mul_nonneg (by linarith) hlogq.le
      have hsplit : (Λ₁ + L + 1) * Real.log q = Λ₁ * Real.log q + (L + 1) * Real.log q := by ring
      rw [hsplit]
      unfold fullLW at hC
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with ((⟨C', hC', rfl⟩ | hC) | hC) | rfl | rfl
      · have := hΩc C' hC'
        show C'.c 0 ≤ _
        linarith
      · obtain ⟨a', b', -, rfl⟩ := mem_yPairs.1 hC
        show (0 : ℝ) ≤ _
        linarith
      · unfold yLow at hC
        obtain ⟨a', -, rfl⟩ := List.mem_map.1 hC
        show -Real.log (w : ℝ) ≤ _
        have : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw1
        linarith
      · show Real.log ((0 : ℕ) : ℝ) - Real.log (N₁ : ℝ) ≤ _
        have : 0 ≤ Real.log (N₁ : ℝ) := Real.log_nonneg (by exact_mod_cast hN₁1)
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
      · show Real.log (N₂ : ℝ) - Real.log ((0 : ℕ) : ℝ) ≤ _
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
    · -- the region
      intro z hz hzΩ
      have hx1 : ∀ i, 1 ≤ z (Fin.castAdd t i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd K b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlow, hlo, hhi⟩ := (fullLW_holds0 Ω (by linarith) (by exact_mod_cast hN₁1)
        (by exact_mod_cast hN₂1) _ _ hx1 hy1).1 hzΩ
      obtain ⟨hge, hSlo, hShi, hrlo, hrhi⟩ := hreg _ (fun i => hz _) hΩ'
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd t i)) * ∏ b, z (Fin.natAdd K b) := Fin.prod_univ_add z
      have hlo' : N₁ < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
      have hhi' : ∏ i, z i ≤ N₂ := by rw [hprod]; exact_mod_cast hhi
      have hm₁ : ∏ i ∈ S₁, z i = ∏ i ∈ S, z (Fin.castAdd t i) := by rw [hS₁, Finset.prod_map]; rfl
      have hρ : ∏ i ∈ Sr', z i = ∏ i ∈ Sr, z (Fin.castAdd t i) := by rw [hSr', Finset.prod_map]; rfl
      have hall := hprodAll z
      refine ⟨fun i => ?_, by rw [hm₁]; exact hSlo, by rw [hm₁]; exact hShi, ?_, ?_, ?_, ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun b => ?_) i
        · exact hwq.trans (by exact_mod_cast hge i)
        · exact hwq.trans (hlow b)
      · -- `N₁/(B·Br) < m₂`
        refine Nat.div_lt_of_lt_mul ?_
        calc N₁ < ∏ i, z i := hlo'
          _ = (∏ i ∈ S₁, z i) * (∏ i ∈ Sr', z i) * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i := hall
          _ ≤ B * Br * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul (by rw [hm₁]; exact hShi) (by rw [hρ]; exact hrhi))
      · -- `m₂ ≤ N₂/((A + 1)(Ar + 1))`
        refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
        calc (∏ i ∈ (S₁ ∪ Sr')ᶜ, z i) * ((A + 1) * (Ar + 1))
            ≤ (∏ i ∈ (S₁ ∪ Sr')ᶜ, z i) * ((∏ i ∈ S₁, z i) * ∏ i ∈ Sr', z i) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul (by rw [hm₁]; exact hSlo) (by rw [hρ]; exact hrlo))
          _ = ∏ i, z i := by rw [hall]; ring
          _ ≤ N₂ := hhi'
      · -- `N₁/Br < m₁m₂`
        refine Nat.div_lt_of_lt_mul ?_
        calc N₁ < ∏ i, z i := hlo'
          _ = (∏ i ∈ S₁, z i) * (∏ i ∈ Sr', z i) * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i := hall
          _ ≤ (∏ i ∈ S₁, z i) * Br * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by rw [hρ]; exact hrhi))
          _ = Br * ((∏ i ∈ S₁, z i) * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i) := by ring
      · -- `m₁m₂ ≤ N₂/(Ar + 1)`
        refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
        calc (∏ i ∈ S₁, z i) * (∏ i ∈ (S₁ ∪ Sr')ᶜ, z i) * (Ar + 1)
            ≤ (∏ i ∈ S₁, z i) * (∏ i ∈ (S₁ ∪ Sr')ᶜ, z i) * ∏ i ∈ Sr', z i :=
              Nat.mul_le_mul_left _ (by rw [hρ]; exact hrlo)
          _ = ∏ i, z i := by rw [hall]; ring
          _ ≤ N₂ := hhi'
      · exact le_trans (by exact_mod_cast hhi') hN₂le
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1' (by linarith [hδ₀le t htK]))
        (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [Finset.card_range, nsmul_eq_mul]
  calc ((Kmax + 1 : ℕ) : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀))
      ≤ (q : ℝ) ^ (δ₀ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀)) :=
        mul_le_mul_of_nonneg_right (by push_cast; exact hqK) (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀ / 2) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

/-! ### At one modulus, for every length up to a bound -/

/-- **The leaves by the estimate in two variables at `q`, for every length `K ≤ K₀`**: the conclusion of
`leaf2_bound` for the boxes `(A, B]` of the first variable's product and `(Ar, Br]` of the rest's, with the leaves'
roughness `w`. -/
def LeavesE (q : ℕ) (a : ZMod q) (L Λ₁ δ : ℝ) (J₀ K₀ w A B Ar Br : ℕ) : Prop :=
  ∀ K ≤ K₀, ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)), Disjoint S Sr → Sr.Nonempty →
    Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
    (∀ x : Fin K → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ Ω, C.holds 0 x) →
      (∀ i, w ≤ x i) ∧ A < ∏ i ∈ S, x i ∧ ∏ i ∈ S, x i ≤ B ∧ Ar < ∏ i ∈ Sr, x i ∧ ∏ i ∈ Sr, x i ≤ Br) →
    ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

theorem LeavesE.mono {q : ℕ} (hq : 1 ≤ q) {a : ZMod q} {L Λ₁ δ δ' : ℝ} {J₀ K₀ K₀' w A B Ar Br : ℕ}
    (h : LeavesE q a L Λ₁ δ J₀ K₀ w A B Ar Br) (hδ : δ' ≤ δ) (hK : K₀' ≤ K₀) :
    LeavesE q a L Λ₁ δ' J₀ K₀' w A B Ar Br := by
  intro K hK' S Sr Ω hd hne hΩ hc hreg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine (h K (hK'.trans hK) S Sr Ω hd hne hΩ hc hreg).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by positivity)

/-- `LeavesE` for large `q`, from `leaf2_bound` at each length up to `K₀`: given Proposition 3′ in two variables on
`Rg`, for boxes on whose window `Rg` holds. -/
theorem leavesE_of_zone {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 5 / 2) {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg)
    {e₀ : ℝ} (he₀ : 0 < e₀) (K₀ J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ w : ℕ, 2 ≤ w → (q : ℝ) ^ e₀ ≤ w →
      ∀ A B Ar Br : ℕ, 1 ≤ A → 1 ≤ B → 1 ≤ Br → B * Br ≤ ⌊(q : ℝ) ^ L⌋₊ →
        (∀ u v : ℝ, Real.logb q A ≤ u → u ≤ Real.logb q B →
          ((⌊(q : ℝ) ^ L⌋₊ / Br : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u + v) →
          (q : ℝ) ^ (u + v) ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (Ar + 1) : ℕ) : ℝ) → Rg u v) →
        LeavesE q a L Λ₁ δ J₀ K₀ w A B Ar Br := by
  induction K₀ with
  | zero =>
    obtain ⟨δ, hδ, q₀, H⟩ := leaf2_bound hL0 hL hII he₀ 0 J₀ hΛ₁
    refine ⟨δ, hδ, q₀, fun q _ hq a ha w hw2 hwq A B Ar Br hA hB hBr hBBr hR K hK S Sr Ω hd hne hΩ hc hreg => ?_⟩
    obtain rfl : K = 0 := by omega
    exact H q hq a ha w hw2 hwq S Sr Ω A B Ar Br hd hne hΩ hc hA hB hBr hBBr hR hreg
  | succ K ih =>
    obtain ⟨δ₁, hδ₁, q₁, H₁⟩ := ih
    obtain ⟨δ₂, hδ₂, q₂, H₂⟩ := leaf2_bound hL0 hL hII he₀ (K + 1) J₀ hΛ₁
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max q₁ q₂,
      fun q _ hq a ha w hw2 hwq A B Ar Br hA hB hBr hBBr hR K' hK' S Sr Ω hd hne hΩ hc hreg => ?_⟩
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    rcases Nat.lt_or_ge K' (K + 1) with h | h
    · exact (H₁ q (le_trans (le_max_left _ _) hq) a ha w hw2 hwq A B Ar Br hA hB hBr hBBr hR).mono hq1
        (min_le_left _ _) le_rfl K' (by omega) S Sr Ω hd hne hΩ hc hreg
    · obtain rfl : K' = K + 1 := by omega
      refine (H₂ q (le_trans (le_max_right _ _) hq) a ha w hw2 hwq S Sr Ω A B Ar Br hd hne hΩ hc hA hB hBr hBBr
        hR hreg).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
        (by linarith [min_le_right δ₁ δ₂])) (by positivity)

/-! ### The estimate on the leaves' region -/

/-- **Proposition 3′ in two variables on the leaves' region**, from the fourth moment of short polynomials over the
characters: the curve `g7d` (the trivial count, Ingham, Chen–Gupta–Li and Huxley) and the zone `zone_leaf`. -/
theorem typeIITwoAt_leaf (L : ℝ) : TypeIITwoAt L (SieveTypeIIHM.LeafZone L) :=
  fun hf0 hsupp K₀ _ _ he₁ hη hη1 => SieveTypeIIHM.typeII_two_gen4 SieveCurve7D.g7d_le_one SieveCurve7D.g7d_half
    SieveCurve7D.counts_7d (SieveTypeIIHM.zone_leaf L) hf0 hsupp K₀ he₁ hη hη1

/-! ### A cofactor longer than `√q` -/

open SieveTypeIIHM in
/-- An exponent for a polynomial of length `q^{1/2}` gives one for length `q^m`, `m ≥ 1/2`, larger by `m − 1/2`:
orthogonality, the Halász–Montgomery inequality and the fourth moment alike. -/
lemma sqExp4_shift {d e g M m : ℝ} (hd : 0 ≤ d) (h : SqExp4 d e g (1 / 2) M) (hm : 1 / 2 ≤ m) :
    SqExp4 d e g m (M + (m - 1 / 2)) := by
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
  · refine Or.inl (Or.inr ⟨by linarith, ?_⟩)
    nlinarith
  · refine Or.inr ⟨by linarith, ?_⟩
    rw [max_eq_left hm]
    rw [max_eq_left (le_refl _)] at h2
    linarith

open SieveTypeIIHM in
/-- `twoBound4` at a second variable of length `q^{1/2}` gives it at length `q^{m₂}`, `m₂ ≥ 1/2`, with the same
rest: the second variable's exponent grows with its length. -/
lemma twoBound4_shift {L d e g β m₁ m₂ w : ℝ} (hd : 0 ≤ d) (h : twoBound4 (L - m₂ + 1 / 2) d e g β m₁ (1 / 2) w)
    (hm : 1 / 2 ≤ m₂) : twoBound4 L d e g β m₁ m₂ w := by
  obtain ⟨M₁, M₂, h1, h2, h3⟩ := h
  refine ⟨M₁, M₂ + (m₂ - 1 / 2), h1, sqExp4_shift hd h2 hm, ?_⟩
  have hρ : L - m₁ - m₂ = L - m₂ + 1 / 2 - m₁ - 1 / 2 := by ring
  rw [hρ]
  linarith

/-- **The leaves' region with a cofactor of any length from `q^{2/5}`**: `LeafZone` below `m₂ = 1/2`, and above it
the slice `m₂ = 1/2` with the same rest `ρ = L − m₁ − m₂`. -/
def LeafZoneX (L m₁ m₂ : ℝ) : Prop :=
  (m₂ ≤ 1 / 2 ∧ SieveTypeIIHM.LeafZone L m₁ m₂) ∨ (1 / 2 ≤ m₂ ∧ SieveTypeIIHM.LeafZone (L - m₂ + 1 / 2) m₁ (1 / 2))

/-- The zone's exponents on `LeafZoneX L`: `zone_leaf` at `L`, and at `L − m₂ + 1/2` with the second exponent
shifted (`twoBound4_shift`). -/
theorem zone_leafX (L : ℝ) :
    SieveTypeIIHM.ZoneOK4 SieveCurve7D.g7d L (1 / 1000) (1 / 1000) (LeafZoneX L) := by
  intro β m₁ m₂ w hβ hβ1 hR hw hw1
  rcases hR with ⟨-, hR⟩ | ⟨hm, hR⟩
  · exact SieveTypeIIHM.zone_leaf L β m₁ m₂ w hβ hβ1 hR hw hw1
  · exact twoBound4_shift (by norm_num)
      (SieveTypeIIHM.zone_leaf (L - m₂ + 1 / 2) β m₁ (1 / 2) w hβ hβ1 hR hw hw1) hm

/-- **Proposition 3′ in two variables on `LeafZoneX L`.** -/
theorem typeIITwoAt_leafX (L : ℝ) : TypeIITwoAt L (LeafZoneX L) :=
  fun hf0 hsupp K₀ _ _ he₁ hη hη1 => SieveTypeIIHM.typeII_two_gen4 SieveCurve7D.g7d_le_one SieveCurve7D.g7d_half
    SieveCurve7D.counts_7d (zone_leafX L) hf0 hsupp K₀ he₁ hη hη1

end SieveLeafTwo
