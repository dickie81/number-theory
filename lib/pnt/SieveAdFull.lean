/-
# The estimate in two variables on tuples of primes with a given product, in no order

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveTwoTerm.chain2_bound` bounds the term of a family of strictly decreasing chains: it
writes the cofactor of each multiple out as its primes, and applies `SieveTwoChain.chain_two` to the full tuples,
whose product is `n`. A reversed term's full tuples are not a chain with its cofactor: the primes of the frozen
number, those of the chain and those of the chain's cofactor are in no order. `chain_two` asks for none, so the
bound holds for any family of tuples of primes whose product lies in `(N₁, N₂]`:

* `full2_bound`: **tuples of primes with product in `(N₁, N₂]` and two marked products.** For a family of
  `K`-tuples of primes cut out by at most `J₀` comparisons, each with entries at least `q^{e₀}`, product in
  `(N₁, N₂]`, `A < ∏_S z ≤ B` and `Ar < ∏_{Sr} z ≤ Br` for disjoint sets `S` and `Sr ≠ ∅`, with the region on the
  rectangle as in `chain2_bound`: the sum over the family of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` is at most
  `q^{L−δ}/φ(q)` in absolute value.
* `full2_exp`: the same with the two products in ranges of exponents, as `SieveAd.chain2_exp`.
* `full2_core`: the same for the region `Zone7d` and exponents in units of `1/DEN` that pass `coreI2`
  (`SieveAdFullDefs.lean`); `full2_core_at` with the route and its exponent as variables.

The file imports `SieveAdTwo.lean` and `SieveAdFullDefs.lean`.
-/
import SieveAdTwo
import SieveAdFullDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK]

/-- **Tuples of primes with product in `(N₁, N₂]` and two marked products.** Assume Proposition 3′ in two
variables at `L` on `Rg` (`hII`). Fix `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
`q ≥ q₀` and a unit `a` mod `q`: let `z` run over the `K`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most
`J₀` comparisons `Ω` (with constants at most `Λ₁ log q`), each with entries at least `q^{e₀}`, product in
`(N₁, N₂]`, `A < ∏_{i∈S} z_i ≤ B` and `Ar < ∏_{i∈Sr} z_i ≤ Br`, where `S` and `Sr ≠ ∅` are disjoint,
`A, B, Br ≥ 1`, `B·Br ≤ N₁ = ⌊q^L⌋` and `Rg u v` holds for `u ∈ [log_q A, log_q B]` with `⌊N₁/Br⌋ ≤ 4q^{u+v}` and
`q^{u+v} ≤ ⌊N₂/(Ar + 1)⌋`. Then the sum over `z` of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` is at most `q^{L−δ}/φ(q)`
in absolute value. -/
theorem full2_bound {Rg : ℝ → ℝ → Prop} (hII : SieveFamilyTwo.TypeIITwoAt L Rg) {e₀ : ℝ} (he₀ : 0 < e₀)
    (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)) (A B Ar Br : ℕ), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) → 1 ≤ A → 1 ≤ B → 1 ≤ Br →
      B * Br ≤ ⌊(q : ℝ) ^ L⌋₊ →
      (∀ u v : ℝ, Real.logb q A ≤ u → u ≤ Real.logb q B →
        ((⌊(q : ℝ) ^ L⌋₊ / Br : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u + v) →
        (q : ℝ) ^ (u + v) ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (Ar + 1) : ℕ) : ℝ) → Rg u v) →
      (∀ z : Fin K → ℕ, (∀ i, (z i).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ i, (q : ℝ) ^ e₀ ≤ z i) ∧ A < ∏ i ∈ S, z i ∧ ∏ i ∈ S, z i ≤ B ∧
          Ar < ∏ i ∈ Sr, z i ∧ ∏ i ∈ Sr, z i ≤ Br ∧ ⌊(q : ℝ) ^ L⌋₊ < ∏ i, z i ∧
          ∏ i, z i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
      ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ i, z i)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, H⟩ := SieveTwoChain.chain_two hII L_pos L_le he₀ K J₀ hΛ₁
  refine ⟨δ, hδ, max q₀ 1, ?_⟩
  intro q _ hq a ha S Sr Ω A B Ar Br hdisj hSr hΩlen hΩc hA hB1 hBr1 hBBr hR hreg
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hBBr0 : 0 < B * Br := Nat.mul_pos hB1 hBr1
  have hd12 : Disjoint S (S ∪ Sr)ᶜ :=
    Finset.disjoint_left.2 fun i hi hic => (Finset.mem_compl.1 hic) (Finset.mem_union_left _ hi)
  have hrest : (S ∪ (S ∪ Sr)ᶜ)ᶜ.Nonempty := by
    obtain ⟨i, hi⟩ := hSr
    refine ⟨i, ?_⟩
    rw [Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨Finset.disjoint_right.1 hdisj hi, fun h => (Finset.mem_compl.1 h) (Finset.mem_union_right _ hi)⟩
  have hprodAll : ∀ z : Fin K → ℕ,
      ∏ i, z i = (∏ i ∈ S, z i) * (∏ i ∈ Sr, z i) * ∏ i ∈ (S ∪ Sr)ᶜ, z i := fun z => by
    rw [← Finset.prod_union hdisj, Finset.prod_mul_prod_compl]
  have hBrN : Br ≤ N₁ := le_trans (Nat.le_mul_of_pos_left Br hB1) hBBr
  refine H q (le_trans (le_max_left _ _) hq) a ha S (S ∪ Sr)ᶜ hd12 hrest Ω hΩlen hΩc A B (N₁ / (B * Br))
    (N₂ / ((A + 1) * (Ar + 1))) (N₁ / Br) (N₂ / (Ar + 1)) hA (Nat.div_pos hBBr hBBr0) (Nat.div_pos hBrN hBr1)
    ((Nat.cast_le.2 (Nat.div_le_self _ _)).trans hN₂le) (fun u v h1 h2 _ _ h5 h6 => hR u v h1 h2 h5 h6) ?_
  intro z hz hzΩ
  obtain ⟨hge, hSlo, hShi, hrlo, hrhi, hlo', hhi'⟩ := hreg z hz hzΩ
  have hall := hprodAll z
  refine ⟨hge, hSlo, hShi, ?_, ?_, ?_, ?_, ?_⟩
  · refine Nat.div_lt_of_lt_mul ?_
    calc N₁ < ∏ i, z i := hlo'
      _ = (∏ i ∈ S, z i) * (∏ i ∈ Sr, z i) * ∏ i ∈ (S ∪ Sr)ᶜ, z i := hall
      _ ≤ B * Br * ∏ i ∈ (S ∪ Sr)ᶜ, z i := Nat.mul_le_mul_right _ (Nat.mul_le_mul hShi hrhi)
  · refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
    calc (∏ i ∈ (S ∪ Sr)ᶜ, z i) * ((A + 1) * (Ar + 1))
        ≤ (∏ i ∈ (S ∪ Sr)ᶜ, z i) * ((∏ i ∈ S, z i) * ∏ i ∈ Sr, z i) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hSlo hrlo)
      _ = ∏ i, z i := by rw [hall]; ring
      _ ≤ N₂ := hhi'
  · refine Nat.div_lt_of_lt_mul ?_
    calc N₁ < ∏ i, z i := hlo'
      _ = (∏ i ∈ S, z i) * (∏ i ∈ Sr, z i) * ∏ i ∈ (S ∪ Sr)ᶜ, z i := hall
      _ ≤ (∏ i ∈ S, z i) * Br * ∏ i ∈ (S ∪ Sr)ᶜ, z i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrhi)
      _ = Br * ((∏ i ∈ S, z i) * ∏ i ∈ (S ∪ Sr)ᶜ, z i) := by ring
  · refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
    calc (∏ i ∈ S, z i) * (∏ i ∈ (S ∪ Sr)ᶜ, z i) * (Ar + 1)
        ≤ (∏ i ∈ S, z i) * (∏ i ∈ (S ∪ Sr)ᶜ, z i) * ∏ i ∈ Sr, z i := Nat.mul_le_mul_left _ hrlo
      _ = ∏ i, z i := by rw [hall]; ring
      _ ≤ N₂ := hhi'
  · exact le_trans (by exact_mod_cast hhi') hN₂le

/-- **Tuples of primes with product in `(N₁, N₂]`, the first variable and the rest in ranges of exponents.** Let
`Rg` be a region of `TypeIITwoAt L`, and let it hold at the `(m₁, m₂)` with `u − ε ≤ m₁ ≤ v` and
`L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − ρ₁ + ε`, for `0 < u ≤ v`, `0 ≤ ρ₁ ≤ ρ₂`, `v + ρ₂ ≤ L` and `ε > 0`. Let `z` run over the
`K`-tuples of primes up to `N₂` that satisfy at most `J₀` comparisons, each with entries at least `q^{e₀}`, product
in `(N₁, N₂]`, `q^u ≤ ∏_{i∈S} z_i ≤ q^v` and `q^{ρ₁} ≤ ∏_{i∈Sr} z_i ≤ q^{ρ₂}`, for disjoint sets `S` and
`Sr ≠ ∅`. Then the sum over `z` of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` is at most `q^{L−δ}/φ(q)` in absolute
value: `full2_bound` with the windows `(⌈q^u⌉ − 1, ⌊q^v⌋]` and `(⌈q^{ρ₁}⌉ − 1, ⌊q^{ρ₂}⌋]`. -/
theorem full2_exp {Rg : ℝ → ℝ → Prop} (hII : SieveFamilyTwo.TypeIITwoAt L Rg) {e₀ : ℝ} (he₀ : 0 < e₀)
    (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {u v ρ₁ ρ₂ ε : ℝ} (hu : 0 < u) (huv : u ≤ v) (hρ₁0 : 0 ≤ ρ₁)
    (hρ : ρ₁ ≤ ρ₂) (hvρ : v + ρ₂ ≤ L) (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u - ε ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - ρ₁ + ε → Rg m₁ m₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ z : Fin K → ℕ, (∀ i, (z i).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ i, (q : ℝ) ^ e₀ ≤ z i) ∧ (q : ℝ) ^ u ≤ ((∏ i ∈ S, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, z i : ℕ) : ℝ) ≤ (q : ℝ) ^ v ∧ (q : ℝ) ^ ρ₁ ≤ ((∏ i ∈ Sr, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ Sr, z i : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂ ∧ ⌊(q : ℝ) ^ L⌋₊ < ∏ i, z i ∧
          ∏ i, z i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
      ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ i, z i)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := full2_bound hII he₀ K J₀ hΛ₁
  have hLρ : 0 < L - ρ₂ := by linarith
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1 ((ev_rpow hε 8).and ((ev_rpow hLρ 2).and
    ((ev_rpow hu 2).and (Filter.eventually_ge_atTop 2))))
  refine ⟨δ, hδ, max q₀ q₁, fun q _ hq a ha S Sr Ω hdisj hSr hlen hc hreg => ?_⟩
  obtain ⟨h8ε, h2ρ, h2u, hq2⟩ := hq₁ q (le_trans (le_max_right _ _) hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := hq1'.le
  have h2ε : (2 : ℝ) ≤ (q : ℝ) ^ ε := by linarith
  have hqρ₂1 : (1 : ℝ) ≤ (q : ℝ) ^ ρ₂ := Real.one_le_rpow hq1 (by linarith)
  have hqv2 : (2 : ℝ) ≤ (q : ℝ) ^ v := h2u.trans (Real.rpow_le_rpow_of_exponent_le hq1 huv)
  have hP₁ge : (q : ℝ) ^ u ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := Nat.le_ceil _
  have hP₁2 : 2 ≤ ⌈(q : ℝ) ^ u⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := h2u.trans hP₁ge
    exact_mod_cast this
  have hP₂le : (⌊(q : ℝ) ^ v⌋₊ : ℝ) ≤ (q : ℝ) ^ v := Nat.floor_le (by positivity)
  have hBrle : (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ ρ₂ := Nat.floor_le (by positivity)
  have hP₂1 : 1 ≤ ⌊(q : ℝ) ^ v⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBr1 : 1 ≤ ⌊(q : ℝ) ^ ρ₂⌋₊ := Nat.le_floor (by exact_mod_cast hqρ₂1)
  have hAr1 : 1 ≤ ⌈(q : ℝ) ^ ρ₁⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hArge : (q : ℝ) ^ ρ₁ ≤ (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.le_ceil _
  have hN₂r : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hBBr : ⌊(q : ℝ) ^ v⌋₊ * ⌊(q : ℝ) ^ ρ₂⌋₊ ≤ ⌊(q : ℝ) ^ L⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    calc (⌊(q : ℝ) ^ v⌋₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ v * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hP₂le hBrle (Nat.cast_nonneg _) (by positivity)
      _ = (q : ℝ) ^ (v + ρ₂) := (Real.rpow_add hq0 _ _).symm
      _ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 hvρ
  -- `⌈q^u⌉ − 1 ≥ q^{u−ε}`
  have hAcast : ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) = (⌈(q : ℝ) ^ u⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hAge : (q : ℝ) ^ (u - ε) ≤ ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hAcast]
    have e : (q : ℝ) ^ u = (q : ℝ) ^ (u - ε) * (q : ℝ) ^ ε := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    have h0 : (0 : ℝ) < (q : ℝ) ^ (u - ε) := by positivity
    have h1 : (q : ℝ) ^ (u - ε) * 8 ≤ (q : ℝ) ^ u := by
      rw [e]
      exact mul_le_mul_of_nonneg_left h8ε h0.le
    linarith
  have hR : ∀ u' v' : ℝ, Real.logb q ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) ≤ u' →
      u' ≤ Real.logb q (⌊(q : ℝ) ^ v⌋₊ : ℝ) →
      ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u' + v') →
      (q : ℝ) ^ (u' + v') ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (⌈(q : ℝ) ^ ρ₁⌉₊ - 1 + 1) : ℕ) : ℝ) → Rg u' v' := by
    intro u' v' h1 h2 h5 h6
    have hlogb : ∀ y : ℝ, Real.logb q ((q : ℝ) ^ y) = y := fun y => Real.logb_rpow hq0 hq1'.ne'
    refine hzone u' v' ?_ ?_ ?_ ?_
    · exact le_trans ((hlogb (u - ε)).symm.le.trans (Real.logb_le_logb_of_le hq1' (by positivity) hAge)) h1
    · exact h2.trans ((Real.logb_le_logb_of_le hq1' (by exact_mod_cast hP₂1) hP₂le).trans (hlogb v).le)
    · refine (Real.rpow_le_rpow_left_iff hq1').1 ?_
      have hm0 : (0 : ℝ) < (q : ℝ) ^ (L - ρ₂ - ε) := by positivity
      have hprod : (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ε * (q : ℝ) ^ ρ₂ = (q : ℝ) ^ L := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
      have h8' : 8 * ((q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂) ≤ (q : ℝ) ^ L := by
        have h := mul_le_mul_of_nonneg_left h8ε (mul_nonneg hm0.le (Real.rpow_nonneg hq0.le ρ₂))
        calc 8 * ((q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂) = (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂ * 8 := by ring
          _ ≤ (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂ * (q : ℝ) ^ ε := h
          _ = (q : ℝ) ^ L := by rw [← hprod]; ring
      have h2' : 2 * (q : ℝ) ^ ρ₂ ≤ (q : ℝ) ^ L := by
        have e : (q : ℝ) ^ L = (q : ℝ) ^ (L - ρ₂) * (q : ℝ) ^ ρ₂ := by
          rw [← Real.rpow_add hq0]; congr 1; ring
        rw [e]
        exact mul_le_mul_of_nonneg_right h2ρ (by positivity)
      have hmle : ⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ ≤ ⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ := by
        refine (Nat.le_div_iff_mul_le hBr1).2 (Nat.le_floor ?_)
        push_cast
        have hc1 : (⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ : ℝ) < 4 * (q : ℝ) ^ (L - ρ₂ - ε) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h3 : (⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤
            (4 * (q : ℝ) ^ (L - ρ₂ - ε) + 1) * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hc1.le hBrle (Nat.cast_nonneg _) (by positivity)
        linarith
      have h9 : 4 * (q : ℝ) ^ (L - ρ₂ - ε) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hmle)
      linarith
    · refine (Real.rpow_le_rpow_left_iff hq1').1 (h6.trans ?_)
      rw [Nat.sub_add_cancel hAr1]
      calc ((⌊2 * (q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ ρ₁⌉₊ : ℕ) : ℝ)
          ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.cast_div_le
        _ ≤ (2 * (q : ℝ) ^ L) / (q : ℝ) ^ ρ₁ := div_le_div₀ (by positivity) hN₂r (by positivity) hArge
        _ = 2 * (q : ℝ) ^ (L - ρ₁) := by rw [mul_div_assoc, ← Real.rpow_sub hq0]
        _ ≤ (q : ℝ) ^ ε * (q : ℝ) ^ (L - ρ₁) := mul_le_mul_of_nonneg_right h2ε (by positivity)
        _ = (q : ℝ) ^ (L - ρ₁ + ε) := by rw [← Real.rpow_add hq0]; congr 1; ring
  refine hq₀ q (le_trans (le_max_left _ _) hq) a ha S Sr Ω (⌈(q : ℝ) ^ u⌉₊ - 1) ⌊(q : ℝ) ^ v⌋₊
    (⌈(q : ℝ) ^ ρ₁⌉₊ - 1) ⌊(q : ℝ) ^ ρ₂⌋₊ hdisj hSr hlen hc (by omega) hP₂1 hBr1 hBBr hR fun rt hp hΩ => ?_
  obtain ⟨hge, h1, h2, h3, h4, h5, h6⟩ := hreg rt hp hΩ
  refine ⟨hge, ?_, Nat.le_floor h2, ?_, Nat.le_floor h4, h5, h6⟩
  · have := Nat.ceil_le.2 h1
    omega
  · have := Nat.ceil_le.2 h3
    omega

variable [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

/-- **Tuples of primes with product in `(N₁, N₂]`, on exponents that pass the checks.** For numbers `u ≤ v` and
`ρ₁ ≤ ρ₂` that pass `coreI2`, and `K`, `J₀`: there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod
`q`, a family of `K`-tuples of primes up to `N₂` cut out by at most `J₀` comparisons with constants at most
`(L + 1) log q`, each with entries at least `x^{1/DEN}`, product in `(N₁, N₂]`,
`x^{u/DEN} ≤ ∏_{i∈S} z_i ≤ x^{v/DEN}` and `x^{ρ₁/DEN} ≤ ∏_{i∈Sr} z_i ≤ x^{ρ₂/DEN}`, for disjoint sets `S` and
`Sr ≠ ∅`, has the sum of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` at most `q^{L−δ}/φ(q)` in absolute value. -/
theorem full2_core (u v ρ₁ ρ₂ : ℕ) (hok : coreI2 u v ρ₁ ρ₂ = true) (huv0 : u ≤ v) (hρ12 : ρ₁ ≤ ρ₂) (K J₀ : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ (L + 1) * Real.log q) →
      (∀ z : Fin K → ℕ, (∀ i, (z i).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ i, xq q ^ (((1 : ℕ) : ℝ) / DEN) ≤ z i) ∧ xq q ^ ((u : ℝ) / DEN) ≤ ((∏ i ∈ S, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, z i : ℕ) : ℝ) ≤ xq q ^ ((v : ℝ) / DEN) ∧
          xq q ^ ((ρ₁ : ℝ) / DEN) ≤ ((∏ i ∈ Sr, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ Sr, z i : ℕ) : ℝ) ≤ xq q ^ ((ρ₂ : ℝ) / DEN) ∧ N1 q < ∏ i, z i ∧ ∏ i, z i ≤ N2 q) →
      ‖∑ z ∈ RTg K (N2 q) Ω, dw q a (∏ i, z i)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  simp only [coreI2, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩ := hok
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hκD : κ * DEN = L := by rw [hκdef]; field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (Lden : ℝ) * DEN := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hLnum' : (Lnum : ℝ) = M * κ := by rw [hMdef]; exact hLnum
  have cast : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) ≤ b := fun hab => by exact_mod_cast hab
  have conv : ∀ {A B : ℝ}, M * A ≤ M * B → A ≤ B := fun hAB => le_of_mul_le_mul_left hAB hM
  have Z1 : 1 + 2000 * κ ≤ 2000 * (κ * ρ₁) := conv (by
    have := cast z1
    push_cast at this
    rw [hLnum', ← hMdef] at this
    linarith)
  have Z2 : 2 + 3 * κ ≤ 3 * (κ * u) := conv (by
    have := cast z2
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z3 : 2 + 3 * (κ * (ρ₂ + 1 + v)) ≤ 3 * L := conv (by
    have := cast z3
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (3 * L) = 3 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z4 : 62505 + 90137 * κ ≤ 62500 * (κ * u) + 27637 * (κ * ρ₁) := conv (by
    have := cast z4
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z5 : 62505 + 62500 * (κ * v) + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z5
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z6 : 125005 + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z6
    push_cast at this
    rw [hLnum'] at this
    have e1 : (125005 : ℝ) * Lden * DEN = 125005 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) - κ ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (ρ₂ : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (ρ₁ : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨δ, hδ, q₀, hq₀⟩ := full2_exp (SieveFamilyTwo.typeIITwoAt_hx L) (e₀ := κ * ((1 : ℕ) : ℝ))
    (by positivity) K J₀ (Λ₁ := L + 1) (by linarith) (u := κ * (u : ℝ)) (v := κ * (v : ℝ)) (ρ₁ := κ * (ρ₁ : ℝ))
    (ρ₂ := κ * (ρ₂ : ℝ)) (ε := κ) (by linarith) (mul_le_mul_of_nonneg_left (cast huv0) hκ.le) (by positivity)
    (mul_le_mul_of_nonneg_left (cast hρ12) hκ.le) (by linarith) hκ hzone
  refine ⟨δ, hδ, q₀, fun q _ hq a ha S Sr Ω hdisj hSr hlen hc hreg => ?_⟩
  refine hq₀ q hq a ha S Sr Ω hdisj hSr hlen hc fun z hp hΩ => ?_
  obtain ⟨hge, h1, h2, h3, h4, h5, h6⟩ := hreg z hp hΩ
  rw [hκdef, qpow_eq, qpow_eq, qpow_eq, qpow_eq, qpow_eq]
  exact ⟨hge, h1, h2, h3, h4, h5, h6⟩

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **Tuples of primes with product in `(N₁, N₂]`, on exponents that pass the checks, for any route**:
`full2_core` with the route and its exponent as variables. -/
theorem full2_core_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr)
    (u v ρ₁ ρ₂ : ℕ) (hok : @coreI2 Pr u v ρ₁ ρ₂ = true) (huv0 : u ≤ v) (hρ12 : ρ₁ ≤ ρ₂) (K J₀ : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin K)) (Ω : List (GCmp K)), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ (@L Rt + 1) * Real.log q) →
      (∀ z : Fin K → ℕ, (∀ i, (z i).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ i, @xq Rt q ^ (((1 : ℕ) : ℝ) / DEN) ≤ z i) ∧
          @xq Rt q ^ ((u : ℝ) / DEN) ≤ ((∏ i ∈ S, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, z i : ℕ) : ℝ) ≤ @xq Rt q ^ ((v : ℝ) / DEN) ∧
          @xq Rt q ^ ((ρ₁ : ℝ) / DEN) ≤ ((∏ i ∈ Sr, z i : ℕ) : ℝ) ∧
          ((∏ i ∈ Sr, z i : ℕ) : ℝ) ≤ @xq Rt q ^ ((ρ₂ : ℝ) / DEN) ∧ @N1 Rt q < ∏ i, z i ∧
          ∏ i, z i ≤ @N2 Rt q) →
      ‖∑ z ∈ RTg K (@N2 Rt q) Ω, dw q a (∏ i, z i)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (@L Rt - δ) :=
  @full2_core Rt hRt Pr hPr u v ρ₁ ρ₂ hok huv0 hρ12 K J₀

end SieveAd

#print axioms SieveAd.full2_core_at
