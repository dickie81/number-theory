/-
# Chains with a sifted cofactor, the cofactor in the resonant window's rest as one part

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTerm.chain_res_exp` evaluates the term of a family of chains by the resonant window with the rest among the
chain's primes. This file puts the cofactor of the chain's multiples in the rest too, whatever its number of primes:
the multiples `n = ∏rt·m` with `m` free of primes below the chain's last entry, `m` written out as its `t` primes
(`SieveTwoTerm.sum_full_eq`), and for each `t ≥ 1` the full tuples `(rt, y)` are evaluated with the rest made of the
chain's rest primes, each its own part, and of all of `y`, one part. The cofactor is then counted by its own sums, as
a prime sum of its length is (`typeII_resG`). There is no multiple with `t = 0`, as `∏rt ≤ N₁`.

* `sifR t r`, `sifGrp n`: the rest's positions in the full tuple, and their parts (the chain's rest's `n + 1`, then
  the cofactor's); `sifR_injective`, `filter_sifGrp_lt`, `prod_filter_sifGrp_cof`, `prod_sifGrp_split`.
* `fullEst_of_res`: **the window's estimate on the full tuples as `FullEst`**: for `ResBox g L K′ (L − ρ₂ − ε)
  (lo − ε)` and parts `grp` of the rest, the region `q^{lo p} ≤ ∏_{grp i = p} x_i`, `∏x ≤ q^{ρ₂}`
  (`full_res_expG`); `fullEst_sif_of_res`: with the parts of a chain's rest and its sifted cofactor.
* `chain_res_sifG`: **chains with a sifted cofactor, by an estimate of the full tuples.** For `e₀ > 0`, `k′`, `J₀`,
  `Λ₁ ≥ 0` and, for each number `t ≥ 1` of the cofactor's primes, an estimate `FullEst` of the full tuples whose rest
  (the chain's rest primes, then the cofactor's) lies in a region `Reg` of the rest's primes and the cofactor's
  product, there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the
  `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons, each strictly decreasing with
  entries at least `q^{e₀}`, with `∏rt ≤ N₁ = ⌊q^L⌋`, and such that every `m` at least `rt`'s last entry with
  `N₁ < ∏rt·m ≤ N₂` is in `Reg` with the rest's primes. The multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor
  below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`.
* `chain_res_sif`: **chains with a sifted cofactor, by the resonant window with the cofactor in the rest**: for a
  curve `g ≤ 1` with `g(1/2) = 1` and its counts and `ResBox g L (n + 2) (L − ρ₂ − ε) (lo − ε)`, the region with the
  rest's primes at least `q^{lo i}`, the cofactor at least `q^{lo (n+1)}` and the rest's product at most `q^{ρ₂}`
  (`chain_res_sifG` on `fullEst_sif_of_res`).
-/
import SieveResTerm
import SieveResTight

open Real Finset Filter SieveFamily SieveTree SieveChain SieveRoute SieveTwoTerm

namespace SieveTypeIIHM

open Classical SieveTypeIIGen

/-- The rest's positions in the full tuple `(rt, y)` of a chain and `t` cofactor primes: the chain's rest at
`castAdd t ∘ r`, then every entry of `y`. -/
def sifR {n k' : ℕ} (t : ℕ) (r : Fin (n + 1) → Fin (k' + 1)) (j : Fin (n + t + 1)) : Fin (k' + 1 + t) :=
  if h : (j : ℕ) < n + 1 then Fin.castAdd t (r ⟨j, h⟩)
  else Fin.natAdd (k' + 1) ⟨(j : ℕ) - (n + 1), by have := j.isLt; omega⟩

/-- The rest's parts: its first `n + 1` positions (the chain's rest) are their own, the others (the cofactor's
primes) are the part `n + 1`. -/
def sifGrp (n j : ℕ) : ℕ := if j < n + 1 then j else n + 1

lemma sifR_injective {n k' t : ℕ} {r : Fin (n + 1) → Fin (k' + 1)} (hr : Function.Injective r) :
    Function.Injective (sifR t r) := by
  intro i j hij
  have hi2 := i.isLt
  have hj2 := j.isLt
  unfold sifR at hij
  by_cases hi : (i : ℕ) < n + 1 <;> by_cases hj : (j : ℕ) < n + 1
  · rw [dite_eq_left hi, dite_eq_left hj] at hij
    have h1 := hr (Fin.castAdd_injective _ _ hij)
    exact Fin.ext (by simpa using congrArg Fin.val h1)
  · rw [dite_eq_left hi, dite_eq_right hj] at hij
    have h1 := congrArg Fin.val hij
    have h2 := (r ⟨i, hi⟩).isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
    omega
  · rw [dite_eq_right hi, dite_eq_left hj] at hij
    have h1 := congrArg Fin.val hij
    have h2 := (r ⟨j, hj⟩).isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
    omega
  · rw [dite_eq_right hi, dite_eq_right hj] at hij
    have h1 := congrArg Fin.val hij
    simp only [Fin.val_natAdd] at h1
    exact Fin.ext (by omega)

/-- A part of the chain's rest is its one position. -/
lemma filter_sifGrp_lt {n t p : ℕ} (hp : p < n + 1) :
    Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = p) = {⟨p, by omega⟩} := by
  ext i
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    unfold sifGrp at h
    by_cases hi : (i : ℕ) < n + 1
    · rw [ite_eq_left hi] at h
      exact Fin.ext h
    · rw [ite_eq_right hi] at h
      omega
  · rintro rfl
    refine ⟨Finset.mem_univ _, ?_⟩
    show (if p < n + 1 then p else n + 1) = p
    rw [ite_eq_left hp]

/-- The cofactor's part is all of its primes. -/
lemma prod_filter_sifGrp_cof {M : Type*} [CommMonoid M] {n k' t : ℕ} (r : Fin (n + 1) → Fin (k' + 1))
    (z : Fin (k' + 1 + t) → M) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), z (sifR t r i) =
      ∏ b : Fin t, z (Fin.natAdd (k' + 1) b) := by
  have hge : ∀ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), n + 1 ≤ (i : ℕ) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have h := hi.2
    unfold sifGrp at h
    by_cases h' : (i : ℕ) < n + 1
    · rw [ite_eq_left h'] at h
      omega
    · omega
  symm
  refine Finset.prod_bij' (fun b _ => ⟨n + 1 + b, by have := b.isLt; omega⟩)
    (fun i hi => ⟨i - (n + 1), by have := i.isLt; have := hge i hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro b _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (if n + 1 + (b : ℕ) < n + 1 then n + 1 + (b : ℕ) else n + 1) = n + 1
    rw [ite_eq_right (by omega)]
  · intro i _
    exact Finset.mem_univ _
  · intro b _
    ext
    simp
  · intro i hi
    have := hge i hi
    ext
    simp only
    omega
  · intro b _
    unfold sifR
    rw [dite_eq_right (by simp only [not_lt]; omega)]
    congr 3
    ext
    simp

/-- The product of a tuple of the rest's primes and the cofactor's is the rest's primes' times the cofactor's. -/
lemma prod_sifGrp_split {M : Type*} [CommMonoid M] {n t : ℕ} (x : Fin (n + t + 1) → M) :
    ∏ i, x i = (∏ i : Fin (n + 1), x (Fin.castLE (by omega) i)) *
      ∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), x i := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin (n + t + 1) => sifGrp n i = n + 1),
    mul_comm]
  congr 1
  symm
  refine Finset.prod_bij' (fun i _ => Fin.castLE (by omega) i) (fun i hi => ⟨i, ?_⟩) ?_ ?_ ?_ ?_ ?_
  · rw [Finset.mem_filter] at hi
    have h := hi.2
    unfold sifGrp at h
    by_contra h'
    rw [ite_eq_right (by omega)] at h
    exact h rfl
  · intro i _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show ¬(if (i : ℕ) < n + 1 then (i : ℕ) else n + 1) = n + 1
    rw [ite_eq_left i.2]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro i _
    rfl
  · intro i _
    rfl
  · intro i _
    rfl

/-- **The window's estimate on the full tuples as `FullEst`.** For `ResBox g L K′ (L − ρ₂ − ε) (lo − ε)` and parts
`grp` of the rest, each nonempty, the full tuples whose rest's parts are at least `q^{lo p}` and whose rest's product
is at most `q^{ρ₂}` are estimated (`full_res_expG`). -/
theorem fullEst_of_res {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) {ρ₂ ε : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hε : 0 < ε)
    (hLρ : 0 < L - ρ₂ - ε) {n K' : ℕ} {grp : ℕ → ℕ} (hgrp : ∀ j < n + 1, grp j < K')
    (hne : ∀ p < K', ∃ j < n + 1, grp j = p) {lo : ℕ → ℝ}
    (hres : ResBox g L K' (L - ρ₂ - ε) (fun j => lo j - ε)) :
    FullEst L e₀ n (fun q x => (∀ p < K', (q : ℝ) ^ lo p ≤
        ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (x i : ℝ)) ∧
      ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) := by
  intro K J₀ Λ₁ hΛ₁
  obtain ⟨δ, hδ, q₀, H⟩ := full_res_expG hg1 hg0 hcnt hL0 hL he₀ K J₀ hΛ₁ hρ₂0 hε hLρ
  refine ⟨δ, hδ, q₀, fun q _ hq a ha r hr Ω hΩlen hΩc hreg =>
    H q hq a ha n r hr K' grp hgrp hne lo hres Ω 0 hΩlen hΩc fun z hz hzΩ => ?_⟩
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := hreg z hz hzΩ
  have himg : ∏ t ∈ Finset.univ.image r, z t = ∏ i, z (r i) := Finset.prod_image fun i _ j _ h => hr h
  refine ⟨h1, h2, ?_, ?_, h4, h5⟩
  · rw [Real.rpow_zero, himg]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_pos fun i _ => (hz (r i)).pos).ne'
  · rw [himg]
    exact h3

/-- **The window's estimate for a chain's rest with a sifted cofactor of `t ≥ 1` primes, one part**: for
`ResBox g L (n + 2) (L − ρ₂ − ε) (lo − ε)`, the full tuples whose rest's primes are at least `q^{lo i}`, whose
cofactor's product is at least `q^{lo (n + 1)}`, and whose rest's product with the cofactor's is at most `q^{ρ₂}`
are estimated (`fullEst_of_res` with the parts `sifGrp n`). -/
theorem fullEst_sif_of_res {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) {ρ₂ ε : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hε : 0 < ε)
    (hLρ : 0 < L - ρ₂ - ε) {n : ℕ} {lo : ℕ → ℝ} (hres : ResBox g L (n + 1 + 1) (L - ρ₂ - ε) (fun j => lo j - ε))
    (t : ℕ) (ht : 1 ≤ t) :
    FullEst L e₀ (n + t) (fun q x =>
      (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x (Fin.castLE (by omega) i)) ∧
      (q : ℝ) ^ lo (n + 1) ≤
        ((∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), x i : ℕ) : ℝ) ∧
      ((((∏ i : Fin (n + 1), x (Fin.castLE (by omega) i)) *
        ∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), x i : ℕ) : ℝ) ≤
          (q : ℝ) ^ ρ₂)) := by
  refine (fullEst_of_res hg1 hg0 hcnt hL0 hL he₀ hρ₂0 hε hLρ (n := n + t) (grp := sifGrp n) (fun j _ => ?_)
    (fun p hp => ?_) hres).mono ?_
  · unfold sifGrp
    split_ifs <;> omega
  · by_cases hp' : p < n + 1
    · exact ⟨p, by omega, by unfold sifGrp; rw [ite_eq_left hp']⟩
    · exact ⟨n + 1, by omega, by unfold sifGrp; rw [ite_eq_right (by omega)]; omega⟩
  · rintro q x ⟨hxlo, hmlo, hprod⟩
    refine ⟨fun p hp => ?_, ?_⟩
    · by_cases hp' : p < n + 1
      · rw [filter_sifGrp_lt hp', Finset.prod_singleton]
        exact hxlo ⟨p, hp'⟩
      · obtain rfl : p = n + 1 := by omega
        exact_mod_cast hmlo
    · rw [prod_sifGrp_split x]
      exact hprod

variable [Route]

set_option maxHeartbeats 1600000 in
/-- **Chains with a sifted cofactor, by an estimate of the tuples with the cofactor in the rest.** See the file's
docstring: the multiples `∏rt·m` are the full tuples `(rt, y)` of `t` cofactor primes (`sum_full_eq`), none with
`t = 0` as `∏rt ≤ N₁`, and for each `t ≥ 1` the estimate `FullEst` of the full tuples whose rest (the chain's rest
primes, then the cofactor's) lies in the region `Reg q (rt (r 0), …, rt (r n)) m` applies; the numbers of the
cofactor's primes are at most `⌈(L + 1)/e₀⌉`. The window's estimate (`fullEst_sif_of_res`, for `chain_res_sif`) and
the window's on a box with the variable tied to the rest (`fullEst_of_tightG`) are such estimates. -/
theorem chain_res_sifG [RouteOK] {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {n : ℕ}
    {Reg : ℕ → (Fin (n + 1) → ℕ) → ℕ → Prop}
    (hfull : ∀ t : ℕ, 1 ≤ t → FullEst L e₀ (n + t) (fun q x => Reg q (fun i => x (Fin.castLE (by omega) i))
      (∏ i ∈ Finset.univ.filter (fun i : Fin (n + t + 1) => sifGrp n i = n + 1), x i))) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (r : Fin (n + 1) → Fin (k' + 1)), Function.Injective r →
      ∀ (Ω : List (GCmp (k' + 1))), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ L⌋₊ ∧
          ∀ m : ℕ, rt (Fin.last k') ≤ m → ⌊(q : ℝ) ^ L⌋₊ < (∏ i, rt i) * m → (∏ i, rt i) * m ≤ ⌊2 * (q : ℝ) ^ L⌋₊ →
            Reg q (fun i => rt (r i)) m) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith [L_pos]
  -- the estimates at `t + 1` primes in the cofactor
  have H := fun t : ℕ => hfull (t + 1) (by omega) (k' + 1 + (t + 1)) (J₀ + Kmax * Kmax + Kmax + 2) (Λ₁ + L + 1) hΛ'
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
  intro q _ hq a ha r hr Ω hΩlen hΩc hreg
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
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · -- no cofactor: the chain's product is at most `N₁`
      subst ht0
      have hz : ∀ rt ∈ RTg (k' + 1) N₂ Ω, ∀ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ 0,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0) = 0 := by
        intro rt hrt y _
        obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
        obtain ⟨-, -, hNle, -⟩ := hreg rt hrtp hrtΩ
        rw [ite_eq_right]
        rintro ⟨h1, -⟩
        rw [Fin.prod_univ_zero, mul_one] at h1
        omega
      rw [Finset.sum_eq_zero fun rt hrt => Finset.sum_eq_zero fun y hy => hz rt hrt y hy, norm_zero]
      positivity
    obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨t - 1, by omega⟩
    rw [sum_full_eq Ω (u + 1) hN₁1 hN₁N₂ le_rfl (dw q a)]
    have hq' : q₀f u ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_range.2 (by omega)))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    refine (hq₀f u q hq' a ha (sifR (u + 1) r) (sifR_injective hr) (fullTL k' (u + 1) Ω N₁ N₂) ?_ ?_ ?_).trans ?_
    · refine (length_fullTL_le k' (u + 1) Ω N₁ N₂).trans ?_
      have : (u + 1) * (u + 1) ≤ Kmax * Kmax := Nat.mul_le_mul htK htK
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
      have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd (u + 1) i) := fun i => (hz _).one_lt.le
      have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (k' + 1) b) := fun b => (hz _).one_lt.le
      rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
      obtain ⟨hΩ', -, hlast, hlo, hhi⟩ := (fullTL_holds0 Ω (by exact_mod_cast hN₁1) (by exact_mod_cast hN₂1) _ _
        hrt1 hy1).1 hzΩ
      obtain ⟨-, hge, -, hm⟩ := hreg _ (fun i => hz _) hΩ'
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd (u + 1) i)) * ∏ b, z (Fin.natAdd (k' + 1) b) :=
        Fin.prod_univ_add z
      have hlo' : N₁ < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
      have hhi' : ∏ i, z i ≤ N₂ := by rw [hprod]; exact_mod_cast hhi
      have hylast : z (Fin.castAdd (u + 1) (Fin.last k')) ≤ ∏ b, z (Fin.natAdd (k' + 1) b) :=
        (hlast ⟨0, by omega⟩).trans (Finset.single_le_prod (fun b _ => hy1 b) (Finset.mem_univ _))
      have hReg := hm (∏ b, z (Fin.natAdd (k' + 1) b)) hylast (by exact_mod_cast hlo) (by exact_mod_cast hhi)
      refine ⟨fun i => ?_, ?_, hlo', hhi'⟩
      · refine Fin.addCases (fun i => ?_) (fun b => ?_) i
        · exact hge i
        · exact (hge (Fin.last k')).trans (by exact_mod_cast hlast b)
      · have e1 : (fun i : Fin (n + 1) => z (sifR (u + 1) r (Fin.castLE (by omega) i))) =
            fun i => z (Fin.castAdd (u + 1) (r i)) := by
          funext i
          simp only [sifR, Fin.val_castLE]
          rw [dite_eq_left i.isLt]
        have e2 : ∏ i ∈ Finset.univ.filter (fun i : Fin (n + (u + 1) + 1) => sifGrp n i = n + 1),
            z (sifR (u + 1) r i) = ∏ b, z (Fin.natAdd (k' + 1) b) := prod_filter_sifGrp_cof r z
        show Reg q (fun i : Fin (n + 1) => z (sifR (u + 1) r (Fin.castLE (by omega) i)))
          (∏ i ∈ Finset.univ.filter (fun i : Fin (n + (u + 1) + 1) => sifGrp n i = n + 1), z (sifR (u + 1) r i))
        rw [e1, e2]
        exact hReg
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1' (by linarith [hδ₀le u (by omega)]))
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


/-- **Chains with a sifted cofactor, by the resonant window with the cofactor in the rest.** For a curve `g ≤ 1`
with `g(1/2) = 1` and its counts, `e₀ > 0`, `k′`, `J₀`, `Λ₁ ≥ 0`, `ρ₂ ≥ 0` and `ε > 0` with `L − ρ₂ − ε > 0`, and
`ResBox g L (n + 2) (L − ρ₂ − ε) (lo − ε)`, there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`:
let `rt` run over the `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons, each
strictly decreasing with entries at least `q^{e₀}` and `rt (r i) ≥ q^{lo i}`, with `∏rt ≤ N₁ = ⌊q^L⌋`, and such that
every `m` at least `rt`'s last entry with `N₁ < ∏rt·m ≤ N₂` has `m ≥ q^{lo (n+1)}` and the rest's product
`∏_i rt (r i)·m` at most `q^{ρ₂}`. The multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last
entry, summed over `rt`, have `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`: `chain_res_sifG` on `fullEst_sif_of_res`. -/
theorem chain_res_sif [RouteOK] {g : ℝ → ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {ρ₂ ε : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hε : 0 < ε)
    (hLρ : 0 < L - ρ₂ - ε) {n : ℕ} {lo : ℕ → ℝ} (hres : ResBox g L (n + 1 + 1) (L - ρ₂ - ε) (fun j => lo j - ε)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (r : Fin (n + 1) → Fin (k' + 1)), Function.Injective r →
      ∀ (Ω : List (GCmp (k' + 1))), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ rt (r i)) ∧
          ∏ i, rt i ≤ ⌊(q : ℝ) ^ L⌋₊ ∧
          ∀ m : ℕ, rt (Fin.last k') ≤ m → ⌊(q : ℝ) ^ L⌋₊ < (∏ i, rt i) * m → (∏ i, rt i) * m ≤ ⌊2 * (q : ℝ) ^ L⌋₊ →
            (q : ℝ) ^ lo (n + 1) ≤ m ∧ (((∏ i ∈ Finset.univ.image r, rt i) * m : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, H⟩ := chain_res_sifG he₀ k' J₀ hΛ₁ (n := n)
    (Reg := fun q xs m => (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ xs i) ∧ (q : ℝ) ^ lo (n + 1) ≤ m ∧
      (((∏ i, xs i) * m : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂)
    (fullEst_sif_of_res hg1 hg0 hcnt L_pos L_le he₀ hρ₂0 hε hLρ hres)
  refine ⟨δ, hδ, q₀, fun q _ hq a ha r hr Ω hΩlen hΩc hreg => H q hq a ha r hr Ω hΩlen hΩc fun rt hp hΩ => ?_⟩
  obtain ⟨hsa, hge, hlor, hN, hm⟩ := hreg rt hp hΩ
  refine ⟨hsa, hge, hN, fun m h1 h2 h3 => ?_⟩
  obtain ⟨hcof, hρ⟩ := hm m h1 h2 h3
  refine ⟨hlor, hcof, ?_⟩
  rwa [Finset.prod_image fun i _ j _ h => hr h] at hρ

end SieveTypeIIHM

#print axioms SieveTypeIIHM.chain_res_sif
#print axioms SieveTypeIIHM.chain_res_sifG
