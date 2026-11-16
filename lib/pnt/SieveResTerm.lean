/-
# Chains with a rest, by the resonant window

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoTerm.chain2_bound` bounds the term of a family of strictly decreasing chains by the estimate in two
variables: it writes the cofactor of each multiple out as its primes and applies the estimate to the full tuples.
This file is the same with the resonant window's estimate (`SieveTypeIIHM.full_res_exp`): one variable, the product of
everything outside a rest of the chain's primes, the rest's primes `r 0, …, r n` each with its own lower bound.

* `chain_res_exp`: **chains with a rest, by the resonant window.** For a curve `g ≤ 1` with `g(1/2) = 1` and its
  counts, `e₀ > 0`, `k′`, `J₀`, `Λ₁ ≥ 0`, `ρ₂ ≥ 0` and `ε > 0` with `L − ρ₂ − ε > 0`, there are `δ > 0` and `q₀` such
  that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that
  satisfy at most `J₀` comparisons, each strictly decreasing with entries at least `q^{e₀}`, `rt (r i) ≥ q^{lo i}` and
  the rest's product `∏_i rt (r i)` in `[q^{ρ₁}, q^{ρ₂}]`. If `ResBox g L (n + 1) (L − ρ₂ − ε) (lo − ε)` holds, the
  multiples `n ∈ (⌊q^L⌋, N₂]` of `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have
  `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`.

The proof is `chain2_bound`'s: the cofactor of `n` is the product of a non-increasing tuple `y` of at most
`K_max = ⌈(L + 1)/e₀⌉` primes (`SieveChain.sum_mult_eq`, `sum_rough_tuples`); for each length `t`,
`SieveTwoTerm.sum_full_eq` and `full_res_exp` on the tuples `(rt, y)`, with the rest at the positions `r i` of `rt`.

The file imports `SieveResFull.lean` and `SieveTwoTerm.lean`.
-/
import SieveResFull
import SieveTwoTerm

open Real Finset Filter SieveFamily SieveTree SieveChain SieveRoute SieveTwoTerm

namespace SieveTypeIIHM

open Classical SieveTypeIIGen

variable [Route]

omit [Route] in
/-- The rest's product in the full tuple is the chain's. -/
lemma prod_image_castAdd {k' t n : ℕ} (r : Fin (n + 1) → Fin (k' + 1)) (z : Fin (k' + 1 + t) → ℕ) :
    ∏ x ∈ Finset.univ.image (fun i => Fin.castAdd t (r i)), z x =
      ∏ x ∈ Finset.univ.image r, z (Fin.castAdd t x) := by
  have e : Finset.univ.image (fun i => Fin.castAdd t (r i)) = (Finset.univ.image r).map (Fin.castAddEmb t) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map, Fin.castAddEmb_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨r i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [e, Finset.prod_map]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Chains with a rest, by the resonant window.** See the file's docstring. -/
theorem chain_res_exp [RouteOK] {g : ℝ → ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {ρ₂ ε : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hε : 0 < ε)
    (hLρ : 0 < L - ρ₂ - ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (n : ℕ) (r : Fin (n + 1) → Fin (k' + 1)), Function.Injective r → ∀ lo : ℕ → ℝ,
      ResBox g L (n + 1) (L - ρ₂ - ε) (fun j => lo j - ε) →
      ∀ (Ω : List (GCmp (k' + 1))) (ρ₁ : ℝ), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ rt (r i)) ∧
          (q : ℝ) ^ ρ₁ ≤ ((∏ i ∈ Finset.univ.image r, rt i : ℕ) : ℝ) ∧
          ((∏ i ∈ Finset.univ.image r, rt i : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith [L_pos]
  have H := fun t : ℕ => full_res_exp hg1 hg0 hcnt L_pos L_le he₀ (k' + 1 + t) (J₀ + Kmax * Kmax + Kmax + 2) hΛ'
    hρ₂0 hε hLρ
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
  intro q _ hq a ha n r hr lo hres Ω ρ₁ hΩlen hΩc hreg
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
    rw [sum_full_eq Ω t hN₁1 hN₁N₂ le_rfl (dw q a)]
    have hq' : q₀f t ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_range.2 (by omega)))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    have hr' : Function.Injective (fun i => Fin.castAdd t (r i)) := fun i j h =>
      hr (Fin.castAdd_injective _ _ h)
    refine (hq₀f t q hq' a ha n (fun i => Fin.castAdd t (r i)) hr' lo hres (fullTL k' t Ω N₁ N₂) ρ₁ ?_ ?_
      ?_).trans ?_
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
      obtain ⟨-, hge, hlor, hrlo, hrhi⟩ := hreg _ (fun i => hz _) hΩ'
      have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd t i)) * ∏ b, z (Fin.natAdd (k' + 1) b) := Fin.prod_univ_add z
      have hlo' : N₁ < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
      have hhi' : ∏ i, z i ≤ N₂ := by rw [hprod]; exact_mod_cast hhi
      have hρ := prod_image_castAdd r z
      refine ⟨fun i => ?_, fun i => hlor i, ?_, ?_, hlo', hhi'⟩
      · refine Fin.addCases (fun i => ?_) (fun b => ?_) i
        · exact hge i
        · exact (hge (Fin.last k')).trans (by exact_mod_cast hlast b)
      · rw [hρ]; exact hrlo
      · rw [hρ]; exact hrhi
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

end SieveTypeIIHM
