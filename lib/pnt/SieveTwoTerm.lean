/-
# Chains with two marked products, by the Type II estimate in two variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoP6.ChainOK2` is the hypothesis of the comparison with stops in two variables: the bound `q^{L−δ}/φ(q)` for
chains `rt` with `A < ∏_{i∈S} rt_i ≤ B` and `Ar < ∏_{i∈Sr} rt_i ≤ Br`, sifted at their last entry. This file proves it
from Proposition 3′ in two variables (`SieveFamilyTwo.TypeIITwoAt`), through `SieveTwoChain.chain_two`.

Plain statements. `L` is a route's (`SieveRoute.Route`, with `RouteOK`), `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `sum_full_eq`: the chains `rt` of a region `Ω` times the non-increasing `t`-tuples `y` of primes at least `rt`'s
  last entry, with `N₁ < ∏rt·∏y ≤ N₂`, are the `(k′ + 1 + t)`-tuples of the region `SieveChain.fullTL`.
* `chain2_bound`: **chains with two marked products.** Assume Proposition 3′ in two variables at `L` on `Rg`. Fix
  `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt`
  run over the `(k′ + 1)`-tuples of primes up to `N₂` that satisfy at most `J₀` comparisons, each strictly
  decreasing with entries at least `q^{e₀}`, `A < ∏_S rt ≤ B` and `Ar < ∏_{Sr} rt ≤ Br`, for `S` and `Sr ≠ ∅`
  disjoint, with `A, B, Br ≥ 1` and `B·Br ≤ N₁`. If `Rg` holds on the rectangle
  `[log_q A, log_q B] × [log_q ⌊N₁/(B·Br)⌋, log_q ⌊N₂/((A + 1)(Ar + 1))⌋]`, then the multiples `n ∈ (N₁, N₂]` of
  `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`.
* `chainOK2_of_zone`: `ChainOK2` for every length up to `K₀ + 1`.

The first variable is `m₁ = ∏_S rt`, the rest is `∏_{Sr} rt`, and the second variable is all the rest of `n`: the
chain's other primes and the cofactor. So `m₂ = n/(m₁·∏_{Sr} rt)` lies in `(N₁/(B·Br), N₂/((A + 1)(Ar + 1))]`.

The proof of `chain2_bound`: the cofactor of `n` is the product of a non-increasing tuple `y` of at most
`K_max = ⌈(L + 1)/e₀⌉` primes (`SieveChain.sum_mult_eq`, `sum_rough_tuples`); for each length, `sum_full_eq` and
`chain_two` on the tuples `(rt, y)`, with `S` as the first set of indices and everything outside `S ∪ Sr` as the
second.

The file imports `SieveTwoChain.lean` and `SieveTwoP6.lean`.
-/
import SieveTwoChain
import SieveTwoP6

open Real Finset Filter SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6Tree SieveFamilyTwo
  SieveTwoChain SieveTwoP6

namespace SieveTwoTerm

open Classical

/-! ### The full tuples -/

theorem holds_zero_iff_one {K : ℕ} (C : GCmp K) (h : C.c 0 = C.c 1) (x : Fin K → ℕ) :
    C.holds 0 x ↔ C.holds 1 x := by
  unfold GCmp.holds GCmp.form
  rw [h]

/-- The comparisons of the full tuple have the same constant at `m = 0` and at `m = 1`. -/
theorem fullTL_c {k' t : ℕ} (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) :
    ∀ C ∈ fullTL k' t Ω N₁ N₂, C.c 0 = C.c 1 := by
  intro C hC
  unfold fullTL at hC
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with ((⟨C', -, rfl⟩ | hC) | hC) | rfl | rfl
  · rfl
  · obtain ⟨a, b, -, rfl⟩ := mem_yPairs.1 hC
    rfl
  · unfold yLast at hC
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hC
    rfl
  · show Real.log ((0 : ℕ) : ℝ) - Real.log N₁ = Real.log ((1 : ℕ) : ℝ) - Real.log N₁
    simp
  · show Real.log N₂ - Real.log ((0 : ℕ) : ℝ) = Real.log N₂ - Real.log ((1 : ℕ) : ℝ)
    simp

/-- `SieveChain.fullTL_holds` at `m = 0`. -/
theorem fullTL_holds0 {k' t : ℕ} (Ω : List (GCmp (k' + 1))) {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (rt : Fin (k' + 1) → ℕ) (y : Fin t → ℕ) (hrt : ∀ i, 1 ≤ rt i) (hy : ∀ a, 1 ≤ y a) :
    (∀ C ∈ fullTL k' t Ω N₁ N₂, C.holds 0 (Fin.append rt y)) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ (∀ a b : Fin t, a ≤ b → y b ≤ y a) ∧ (∀ a, rt (Fin.last k') ≤ y a) ∧
        N₁ < (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ∧ (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ≤ N₂ := by
  rw [← fullTL_holds Ω hN₁ hN₂ rt y hrt hy]
  exact forall₂_congr fun C hC => holds_zero_iff_one C (fullTL_c Ω N₁ N₂ C hC) _

/-- **The chains with their cofactor's tuples are the full tuples.** For `1 ≤ N₁ ≤ N₂ ≤ Y`: the chains `rt` of the
region `Ω` times the non-increasing `t`-tuples `y` of primes at least `rt`'s last entry, with `N₁ < ∏rt·∏y ≤ N₂`, are
the `(k′ + 1 + t)`-tuples of primes up to `Y` that satisfy `fullTL`. -/
theorem sum_full_eq {M : Type*} [AddCommMonoid M] {k' : ℕ} (Ω : List (GCmp (k' + 1))) {Y N₁ N₂ : ℕ} (t : ℕ)
    (hN₁ : 1 ≤ N₁) (hN₁₂ : N₁ ≤ N₂) (hN₂ : N₂ ≤ Y) (F : ℕ → M) :
    ∑ rt ∈ RTg (k' + 1) Y Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) Y t,
        (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂ then F ((∏ i, rt i) * ∏ a, y a) else 0) =
      ∑ z ∈ RTg (k' + 1 + t) Y (fullTL k' t Ω N₁ N₂), F (∏ i, z i) := by
  set D := ((RTg (k' + 1) Y Ω) ×ˢ (Fintype.piFinset (fun _ : Fin t => SieveTypeIIU.primesLe Y))).filter
    (fun p => ((∀ i j : Fin t, i ≤ j → p.2 j ≤ p.2 i) ∧ (∀ i, p.1 (Fin.last k') ≤ p.2 i) ∧ ∏ a, p.2 a ≤ Y) ∧
      (N₁ < (∏ i, p.1 i) * ∏ a, p.2 a ∧ (∏ i, p.1 i) * ∏ a, p.2 a ≤ N₂)) with hD
  have hL : ∑ rt ∈ RTg (k' + 1) Y Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) Y t,
      (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂ then F ((∏ i, rt i) * ∏ a, y a) else 0) =
      ∑ p ∈ D, F ((∏ i, p.1 i) * ∏ a, p.2 a) := by
    rw [hD, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [SieveRoughTuple.tuples, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    simp only [ite_and]
  rw [hL]
  have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast (show 0 < N₂ by omega)
  refine Finset.sum_nbij' (fun p => Fin.append p.1 p.2)
    (fun z => (fun i => z (Fin.castAdd t i), fun a => z (Fin.natAdd (k' + 1) a))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rt, y⟩ hp
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hrtY, hrtΩ⟩, hyY⟩, ⟨hanti, hlast, -⟩, hlo, hhi⟩ := hp
    have hrt1 : ∀ i, 1 ≤ rt i := fun i => (SieveTypeIIU.mem_primesLe.1 (hrtY i)).2.one_lt.le
    have hy1 : ∀ a, 1 ≤ y a := fun a => (SieveTypeIIU.mem_primesLe.1 (hyY a)).2.one_lt.le
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, (fullTL_holds0 Ω hN₁0 hN₂0 rt y hrt1 hy1).2 ⟨hrtΩ, hanti, hlast, ?_, ?_⟩⟩
    · refine Fin.addCases (fun i => ?_) (fun a => ?_) i
      · rw [Fin.append_left]
        exact hrtY i
      · rw [Fin.append_right]
        exact hyY a
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · intro z hz
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
    obtain ⟨hzY, hzΩ⟩ := hz
    have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd t i) := fun i => (SieveTypeIIU.mem_primesLe.1 (hzY _)).2.one_lt.le
    have hy1 : ∀ a, 1 ≤ z (Fin.natAdd (k' + 1) a) := fun a => (SieveTypeIIU.mem_primesLe.1 (hzY _)).2.one_lt.le
    rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
    obtain ⟨hΩ', hanti, hlast, hlo, hhi⟩ := (fullTL_holds0 Ω hN₁0 hN₂0 _ _ hrt1 hy1).1 hzΩ
    have hlo' : N₁ < (∏ i, z (Fin.castAdd t i)) * ∏ a, z (Fin.natAdd (k' + 1) a) := by exact_mod_cast hlo
    have hhi' : (∏ i, z (Fin.castAdd t i)) * ∏ a, z (Fin.natAdd (k' + 1) a) ≤ N₂ := by exact_mod_cast hhi
    have hpos : 0 < ∏ i, z (Fin.castAdd t i) := Finset.prod_pos fun i _ => hrt1 i
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset]
    exact ⟨⟨⟨fun i => hzY _, hΩ'⟩, fun a => hzY _⟩,
      ⟨hanti, hlast, le_trans (Nat.le_mul_of_pos_left _ hpos) (hhi'.trans hN₂)⟩, hlo', hhi'⟩
  · rintro ⟨rt, y⟩ _
    refine Prod.ext (funext fun i => ?_) (funext fun a => ?_)
    · exact Fin.append_left rt y i
    · exact Fin.append_right rt y a
  · intro z _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨rt, y⟩ _
    have hprod : ∏ i, Fin.append rt y i = (∏ i, rt i) * ∏ a, y a := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    show F ((∏ i, rt i) * ∏ a, y a) = F (∏ i, Fin.append rt y i)
    rw [hprod]

/-! ### Chains with two marked products -/

variable [Route]

set_option maxHeartbeats 1600000 in
/-- **Chains with two marked products.** Assume `RouteOK` and Proposition 3′ in two variables at `L` on `Rg`
(`hII`). Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod
`q`: let `rt` run over the `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω`
(with `m`-parts at most `Λ₁ log q` at `m = 0`), each such tuple strictly decreasing, with entries at least `q^{e₀}`,
`A < ∏_{i∈S} rt_i ≤ B` and `Ar < ∏_{i∈Sr} rt_i ≤ Br`, where `S` and `Sr ≠ ∅` are disjoint, `A, B, Br ≥ 1`,
`B·Br ≤ N₁ = ⌊q^L⌋` and `Rg` holds on the rectangle
`[log_q A, log_q B] × [log_q ⌊N₁/(B·Br)⌋, log_q ⌊N₂/((A + 1)(Ar + 1))⌋]`. Then the multiples `n ∈ (N₁, N₂]` of
`∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chain2_bound [RouteOK] {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ)
    {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))) (A B Ar Br : ℕ), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) → 1 ≤ A → 1 ≤ B → 1 ≤ Br →
      B * Br ≤ ⌊(q : ℝ) ^ L⌋₊ →
      (∀ u v : ℝ, Real.logb q A ≤ u → u ≤ Real.logb q B →
        Real.logb q ((⌊(q : ℝ) ^ L⌋₊ / (B * Br) : ℕ) : ℝ) ≤ v →
        v ≤ Real.logb q ((⌊2 * (q : ℝ) ^ L⌋₊ / ((A + 1) * (Ar + 1)) : ℕ) : ℝ) → Rg u v) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B ∧
          Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith [L_pos]
  have H := fun t : ℕ => chain_two hII L_pos L_le he₀ (k' + 1 + t) (J₀ + Kmax * Kmax + Kmax + 2) hΛ'
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
  intro q _ hq a ha S Sr Ω A B Ar Br hdisj hSr hΩlen hΩc hA hB1 hBr1 hBBr hR hreg
  have hqK := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (1 : ℝ) ≤ q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1' L_pos.le
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
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
  -- each chain: its multiples as cofactor tuples
  have hRT : ∀ rt ∈ RTg (k' + 1) N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 rt) := by
    intro rt hrt
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2, hrt.2⟩
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ t ∈ Finset.range (Kmax + 1), ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ t,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0) := by
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨hsa, hge, -⟩ := hreg rt hrtp hrtΩ
    have hW0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hWr : rough (rt (Fin.last k')) (∏ i, rt i) := by
      intro ℓ hℓp hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
      have := hsa.antitone (Fin.le_last i)
      omega
    rw [sum_mult_eq (dw q a) hW0 hWr]
    exact sum_rough_tuples (hrtp _).two_le hN₂1
      (fun k => if N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂ then dw q a ((∏ i, rt i) * k) else 0) Kmax
      (hpK _ (hge _))
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
      ‖∑ rt ∈ RTg (k' + 1) N₂ Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ t,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀) := by
    intro t ht
    have htK : t ≤ Kmax := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    rw [sum_full_eq Ω t hN₁1 hN₁N₂ le_rfl (dw q a)]
    have hq' : q₀f t ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_range.2 (by omega)))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    obtain ⟨S₁, hS₁⟩ : ∃ T : Finset (Fin (k' + 1 + t)), T = S.map (Fin.castAddEmb t) := ⟨_, rfl⟩
    obtain ⟨Sr', hSr'⟩ : ∃ T : Finset (Fin (k' + 1 + t)), T = Sr.map (Fin.castAddEmb t) := ⟨_, rfl⟩
    have hd' : Disjoint S₁ Sr' := by rw [hS₁, hSr']; exact (Finset.disjoint_map _).2 hdisj
    have hd12 : Disjoint S₁ (S₁ ∪ Sr')ᶜ :=
      Finset.disjoint_left.2 fun i hi hic => (Finset.mem_compl.1 hic) (Finset.mem_union_left _ hi)
    have hrest : (S₁ ∪ (S₁ ∪ Sr')ᶜ)ᶜ.Nonempty := by
      obtain ⟨i, hi⟩ := hSr
      refine ⟨Fin.castAdd t i, ?_⟩
      have hiS : Fin.castAdd t i ∈ Sr' := by rw [hSr']; exact Finset.mem_map_of_mem _ hi
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.1 hd' hiS, fun h => (Finset.mem_compl.1 h) (Finset.mem_union_right _ hiS)⟩
    have hprodAll : ∀ z : Fin (k' + 1 + t) → ℕ,
        ∏ i, z i = (∏ i ∈ S₁, z i) * (∏ i ∈ Sr', z i) * ∏ i ∈ (S₁ ∪ Sr')ᶜ, z i := fun z => by
      rw [← Finset.prod_union hd', Finset.prod_mul_prod_compl]
    refine (hq₀f t q hq' a ha S₁ (S₁ ∪ Sr')ᶜ hd12 hrest (fullTL k' t Ω N₁ N₂) ?_ ?_ A B (N₁ / (B * Br))
      (N₂ / ((A + 1) * (Ar + 1))) hA (Nat.div_pos hBBr hBBr0) hR ?_).trans ?_
    · refine (length_fullTL_le k' t Ω N₁ N₂).trans ?_
      have : t * t ≤ Kmax * Kmax := Nat.mul_le_mul htK htK
      omega
    · -- the constants
      intro C hC
      have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
      have hLl : 0 ≤ (L + 1) * Real.log q := mul_nonneg (by linarith [L_pos]) hlogq.le
      have hsplit : (Λ₁ + L + 1) * Real.log q = Λ₁ * Real.log q + (L + 1) * Real.log q := by ring
      rw [hsplit]
      unfold fullTL at hC
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with ((⟨C', hC', rfl⟩ | hC) | hC) | rfl | rfl
      · have := hΩc C' hC'
        show C'.c 0 ≤ _
        linarith
      · obtain ⟨a', b', -, rfl⟩ := mem_yPairs.1 hC
        show (0 : ℝ) ≤ _
        linarith
      · unfold yLast at hC
        obtain ⟨a', -, rfl⟩ := List.mem_map.1 hC
        show (0 : ℝ) ≤ _
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
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd t i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (k' + 1) b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlast, hlo, hhi⟩ := (fullTL_holds0 Ω (by exact_mod_cast hN₁1) (by exact_mod_cast hN₂1) _ _
        hrt1 hy1).1 hzΩ
      obtain ⟨-, hge, hSlo, hShi, hrlo, hrhi⟩ := hreg _ (fun i => hz _) hΩ'
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd t i)) * ∏ b, z (Fin.natAdd (k' + 1) b) := Fin.prod_univ_add z
      have hlo' : N₁ < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
      have hhi' : ∏ i, z i ≤ N₂ := by rw [hprod]; exact_mod_cast hhi
      have hm₁ : ∏ i ∈ S₁, z i = ∏ i ∈ S, z (Fin.castAdd t i) := by rw [hS₁, Finset.prod_map]; rfl
      have hρ : ∏ i ∈ Sr', z i = ∏ i ∈ Sr, z (Fin.castAdd t i) := by rw [hSr', Finset.prod_map]; rfl
      have hall := hprodAll z
      refine ⟨fun i => ?_, by rw [hm₁]; exact hSlo, by rw [hm₁]; exact hShi, ?_, ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun b => ?_) i
        · exact hge i
        · exact (hge (Fin.last k')).trans (by exact_mod_cast hlast b)
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

/-- **`ChainOK2` for every length up to `K₀ + 1`** (`chain2_bound`). -/
theorem chainOK2_of_zone [RouteOK] {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) {e₀ : ℝ} (he₀ : 0 < e₀)
    (K₀ J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ A B Ar Br : ℕ, 1 ≤ A → 1 ≤ B → 1 ≤ Br → B * Br ≤ ⌊(q : ℝ) ^ L⌋₊ →
        (∀ u v : ℝ, Real.logb q A ≤ u → u ≤ Real.logb q B →
          Real.logb q ((⌊(q : ℝ) ^ L⌋₊ / (B * Br) : ℕ) : ℝ) ≤ v →
          v ≤ Real.logb q ((⌊2 * (q : ℝ) ^ L⌋₊ / ((A + 1) * (Ar + 1)) : ℕ) : ℝ) → Rg u v) →
        ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br := by
  induction K₀ with
  | zero =>
    obtain ⟨δ, hδ, q₀, H⟩ := chain2_bound hII he₀ 0 J₀ hΛ₁
    refine ⟨δ, hδ, q₀, fun q _ hq a ha A B Ar Br hA hB hBr hBBr hR k' hk' S Sr Ω hd hne hΩ hc hreg => ?_⟩
    obtain rfl : k' = 0 := by omega
    exact H q hq a ha S Sr Ω A B Ar Br hd hne hΩ hc hA hB hBr hBBr hR hreg
  | succ K ih =>
    obtain ⟨δ₁, hδ₁, q₁, H₁⟩ := ih
    obtain ⟨δ₂, hδ₂, q₂, H₂⟩ := chain2_bound hII he₀ (K + 1) J₀ hΛ₁
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max q₁ q₂,
      fun q _ hq a ha A B Ar Br hA hB hBr hBBr hR k' hk' S Sr Ω hd hne hΩ hc hreg => ?_⟩
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    rcases Nat.lt_or_ge k' (K + 1) with h | h
    · exact (H₁ q (le_trans (le_max_left _ _) hq) a ha A B Ar Br hA hB hBr hBBr hR).mono hq1 (min_le_left _ _)
        le_rfl k' (by omega) S Sr Ω hd hne hΩ hc hreg
    · obtain rfl : k' = K + 1 := by omega
      refine (H₂ q (le_trans (le_max_right _ _) hq) a ha S Sr Ω A B Ar Br hd hne hΩ hc hA hB hBr hBBr hR
        hreg).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
        (by linarith [min_le_right δ₁ δ₂])) (by positivity)

end SieveTwoTerm

#print axioms SieveTwoTerm.sum_full_eq
#print axioms SieveTwoTerm.chain2_bound
#print axioms SieveTwoTerm.chainOK2_of_zone
