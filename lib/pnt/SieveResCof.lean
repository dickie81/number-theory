/-
# Chains whose cofactor is one prime, the cofactor in the resonant window's rest

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResTerm.chain_res_exp` evaluates the term of a family of chains by the resonant window, its rest among the
chains' primes and its variable everything else, the cofactor included. When every multiple's cofactor is one
prime, the cofactor can be in the rest too: the term is the sum over the full tuples `(rt, y)` of one cofactor prime
`y`, since no multiple is the chain's product itself (`∏rt ≤ N₁`) and two primes at least the chain's last would
overshoot `N₂` (`N₂ < ∏rt·p²` for the last prime `p`), and `y` is at least `q^{lo}` for the bound that
`N₁ < ∏rt·y` gives.

* `snocR r`: the rest's positions `r` in the full tuple with the cofactor's last (`snocR_injective`);
  `prod_image_snocR`: the rest's product is the chain's rest's times the cofactor.
* `chain_res_cof`: **chains whose cofactor is one prime, by the resonant window with the cofactor in the rest.**
  For a curve `g ≤ 1` with `g(1/2) = 1` and its counts, `e₀ > 0`, `k′`, `J₀`, `Λ₁ ≥ 0`, `ρ₂ ≥ 0` and `ε > 0` with
  `L − ρ₂ − ε > 0`, there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the
  `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons, each strictly decreasing
  with entries at least `q^{e₀}` and `rt (r i) ≥ q^{lo i}`, with `∏rt ≤ N₁ = ⌊q^L⌋` and `N₂ < ∏rt·p²` for its last
  prime `p`, and such that every `y ≥ p` with `N₁ < ∏rt·y ≤ N₂` has `y ≥ q^{lo (n+1)}` and the rest's product
  `∏_i rt (r i)·y` in `[q^{ρ₁}, q^{ρ₂}]`. If `ResBox g L (n + 2) (L − ρ₂ − ε) (lo − ε)` holds, the multiples
  `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `p`, summed over `rt`, have `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`.

The file imports `SieveResTerm.lean`.
-/
import SieveResTerm

open Real Finset Filter SieveFamily SieveTree SieveChain SieveRoute SieveTwoTerm

namespace SieveTypeIIHM

open Classical SieveTypeIIGen

/-- The rest's positions in the full tuple `(rt, y)` of one cofactor prime: the chain's at `castAdd 1 ∘ r`, the
cofactor's last. -/
def snocR {n k' : ℕ} (r : Fin (n + 1) → Fin (k' + 1)) : Fin (n + 1 + 1) → Fin (k' + 1 + 1) :=
  Fin.snoc (α := fun _ => Fin (k' + 1 + 1)) (fun i => Fin.castAdd 1 (r i)) (Fin.last (k' + 1))

lemma castAdd_ne_last {k' : ℕ} (x : Fin (k' + 1)) : Fin.castAdd 1 x ≠ Fin.last (k' + 1) := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_last] at this
  omega

lemma snocR_injective {n k' : ℕ} {r : Fin (n + 1) → Fin (k' + 1)} (hr : Function.Injective r) :
    Function.Injective (snocR r) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [snocR, Fin.snoc_last, Fin.snoc_castSucc] at hij
      exact absurd hij.symm (castAdd_ne_last _)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [snocR, Fin.snoc_last, Fin.snoc_castSucc] at hij
      exact absurd hij (castAdd_ne_last _)
    | cast j =>
      simp only [snocR, Fin.snoc_castSucc] at hij
      rw [hr (Fin.castAdd_injective _ _ hij)]

variable [Route]

omit [Route] in
/-- The rest's product with the cofactor: the chain's rest's times the cofactor. -/
lemma prod_image_snocR {n k' : ℕ} (r : Fin (n + 1) → Fin (k' + 1)) (z : Fin (k' + 1 + 1) → ℕ) :
    ∏ x ∈ Finset.univ.image (snocR r), z x =
      (∏ x ∈ Finset.univ.image r, z (Fin.castAdd 1 x)) * z (Fin.last (k' + 1)) := by
  have e : Finset.univ.image (snocR r) =
      insert (Fin.last (k' + 1)) (Finset.univ.image (fun i => Fin.castAdd 1 (r i))) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last => exact Or.inl (by simp [snocR])
      | cast i => exact Or.inr ⟨i, by simp [snocR]⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨Fin.last _, by simp [snocR]⟩
      · exact ⟨Fin.castSucc i, by simp [snocR]⟩
  have hnot : Fin.last (k' + 1) ∉ Finset.univ.image (fun i => Fin.castAdd 1 (r i)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i h => castAdd_ne_last _ h
  rw [e, Finset.prod_insert hnot, prod_image_castAdd r z, mul_comm]

set_option maxHeartbeats 1600000 in
/-- **Chains whose cofactor is one prime, by the resonant window with the cofactor in the rest.** See the file's
docstring. -/
theorem chain_res_cof [RouteOK] {g : ℝ → ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {ρ₂ ε : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hε : 0 < ε)
    (hLρ : 0 < L - ρ₂ - ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (n : ℕ) (r : Fin (n + 1) → Fin (k' + 1)), Function.Injective r → ∀ lo : ℕ → ℝ,
      ResBox g L (n + 1 + 1) (L - ρ₂ - ε) (fun j => lo j - ε) →
      ∀ (Ω : List (GCmp (k' + 1))) (ρ₁ : ℝ), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ rt (r i)) ∧
          ∏ i, rt i ≤ ⌊(q : ℝ) ^ L⌋₊ ∧
          ⌊2 * (q : ℝ) ^ L⌋₊ < (∏ i, rt i) * (rt (Fin.last k') * rt (Fin.last k')) ∧
          ∀ y : ℕ, rt (Fin.last k') ≤ y → ⌊(q : ℝ) ^ L⌋₊ < (∏ i, rt i) * y → (∏ i, rt i) * y ≤ ⌊2 * (q : ℝ) ^ L⌋₊ →
            (q : ℝ) ^ lo (n + 1) ≤ y ∧
              (q : ℝ) ^ ρ₁ ≤ (((∏ i ∈ Finset.univ.image r, rt i) * y : ℕ) : ℝ) ∧
              (((∏ i ∈ Finset.univ.image r, rt i) * y : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  have hΛ' : 0 ≤ Λ₁ + L + 1 := by linarith [L_pos]
  obtain ⟨δ, hδ, q₀, hq₀⟩ := full_res_exp hg1 hg0 hcnt L_pos L_le he₀ (k' + 1 + 1) (J₀ + 1 * 1 + 1 + 2) hΛ'
    hρ₂0 hε hLρ
  refine ⟨δ, hδ, max q₀ 3, ?_⟩
  intro q _ hq a ha n r hr lo hres Ω ρ₁ hΩlen hΩc hreg
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
  have hK1 : 1 ≤ Kmax := Nat.one_le_iff_ne_zero.2 fun h0 => by
    have := Nat.le_ceil ((L + 1) / e₀)
    rw [← hKmax, h0, Nat.cast_zero] at this
    have : 0 < (L + 1) / e₀ := div_pos (by linarith [L_pos]) he₀
    linarith
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
  -- the cofactor is one prime: the other numbers of primes give nothing
  rw [Finset.sum_eq_single 1]
  rotate_left
  · intro t _ ht1
    refine Finset.sum_eq_zero fun rt hrt => Finset.sum_eq_zero fun y hy => ite_eq_right ?_
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨-, -, -, h0, h2, -⟩ := hreg rt hrtp hrtΩ
    rintro ⟨hlo, hhi⟩
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · have ht0 : t = 0 := by omega
      subst ht0
      rw [Fin.prod_univ_zero, mul_one] at hlo
      omega
    · -- two primes at least the chain's last overshoot `N₂`
      unfold SieveRoughTuple.tuples at hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, -, hzy, -⟩ := hy
      have h01 : (⟨0, by omega⟩ : Fin t) ≠ ⟨1, by omega⟩ := by
        intro h
        simp [Fin.ext_iff] at h
      have hyy : rt (Fin.last k') * rt (Fin.last k') ≤ ∏ a, y a := by
        calc rt (Fin.last k') * rt (Fin.last k') ≤ y ⟨0, by omega⟩ * y ⟨1, by omega⟩ :=
              Nat.mul_le_mul (hzy _) (hzy _)
          _ = ∏ a ∈ {⟨0, by omega⟩, ⟨1, by omega⟩}, y a := by rw [Finset.prod_pair h01]
          _ ≤ ∏ a, y a := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
              fun i _ _ => ((hRT rt hrt).1 (Fin.last k')).one_lt.le.trans (hzy i)
      have := Nat.mul_le_mul_left (∏ i, rt i) hyy
      omega
  · intro h1
    exact absurd (Finset.mem_range.2 (by omega)) h1
  -- one cofactor prime: the window on the full tuples with the cofactor in the rest
  rw [sum_full_eq Ω 1 hN₁1 hN₁N₂ le_rfl (dw q a)]
  have hlogN₂ : Real.log (N₂ : ℝ) ≤ (L + 1) * Real.log q := by
    have h1 : (N₂ : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      nlinarith
    have h2 := Real.log_le_log (by exact_mod_cast hN₂1) h1
    rwa [Real.log_rpow hq0] at h2
  refine (hq₀ q (le_trans (le_max_left _ _) hq) a ha (n + 1) (snocR r) (snocR_injective hr) lo hres
    (fullTL k' 1 Ω N₁ N₂) ρ₁ ?_ ?_ ?_)
  · refine (length_fullTL_le k' 1 Ω N₁ N₂).trans ?_
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
    have hrt1 : ∀ i, 1 ≤ z (Fin.castAdd 1 i) := fun i => (hz _).one_lt.le
    have hy1 : ∀ b, 1 ≤ z (Fin.natAdd (k' + 1) b) := fun b => (hz _).one_lt.le
    rw [← Fin.append_castAdd_natAdd (f := z)] at hzΩ
    obtain ⟨hΩ', -, hlast, hlo, hhi⟩ := (fullTL_holds0 Ω (by exact_mod_cast hN₁1) (by exact_mod_cast hN₂1) _ _
      hrt1 hy1).1 hzΩ
    obtain ⟨-, hge, hlor, -, -, hcof⟩ := hreg _ (fun i => hz _) hΩ'
    have hprod : ∏ i, z i = (∏ i, z (Fin.castAdd 1 i)) * ∏ b, z (Fin.natAdd (k' + 1) b) := Fin.prod_univ_add z
    have hlo' : N₁ < ∏ i, z i := by rw [hprod]; exact_mod_cast hlo
    have hhi' : ∏ i, z i ≤ N₂ := by rw [hprod]; exact_mod_cast hhi
    have hy : ∏ b : Fin 1, z (Fin.natAdd (k' + 1) b) = z (Fin.last (k' + 1)) := by
      rw [Fin.prod_univ_one]
      rfl
    rw [hy] at hprod
    obtain ⟨hcy, hc1, hc2⟩ := hcof (z (Fin.last (k' + 1))) (hlast 0) (by rw [← hprod]; exact hlo')
      (by rw [← hprod]; exact hhi')
    have hρ := prod_image_snocR r z
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, hlo', hhi'⟩
    · refine Fin.addCases (fun i => ?_) (fun b => ?_) i
      · exact hge i
      · have h1 := hge (Fin.last k')
        have h2 : (z (Fin.castAdd 1 (Fin.last k')) : ℝ) ≤ z (Fin.natAdd (k' + 1) b) := by exact_mod_cast hlast b
        exact h1.trans h2
    · induction i using Fin.lastCases with
      | last =>
        show (q : ℝ) ^ lo (n + 1) ≤ z (snocR r (Fin.last (n + 1)))
        simp only [snocR, Fin.snoc_last]
        exact hcy
      | cast j =>
        show (q : ℝ) ^ lo (j : ℕ) ≤ z (snocR r (Fin.castSucc j))
        simp only [snocR, Fin.snoc_castSucc]
        exact hlor j
    · rw [hρ]
      exact hc1
    · rw [hρ]
      exact hc2

end SieveTypeIIHM

#print axioms SieveTypeIIHM.chain_res_cof
