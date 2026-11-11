/-
# The comparison in two variables with the rest among the tree's primes

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoComp.prop6_two` evaluates `Σ_r S(A_r, z₀)` over a family of chains in boxes when the rest of the estimate
in two variables is a product of the family's own primes. This file is the comparison for a family with no such
primes: the rest is a product of the primes of Buchstab's tree below `z₀` (`SieveFill.prop6_fill_core`).

Plain statement (`prop6_fill`). Let `L` be a route's exponent (`SieveRoute.Route`, with `RouteOK`), and assume
Proposition 3′ in two variables at `L` on a region `Rg`. Fix `j`, `J₀`, `Λ₁ ≥ 0`, the exponent `a₀ > 0` of
`z₀ = ⌈q^{a₀}⌉`, boxes `[q^{lo_i}, q^{hi_i}]` for the tuples' entries, a set `S₀` of indices whose product `c` enters
the window, a leaf split `(S₁, eIn₁)`, a growth `t ≥ 0`, and exponents with:

* the window `(u, v)` of the first variable: `0 < u`, `u + a₀ < v`, `u − Σ_{S₀} lo ≤ t` and `Σ_{S₀} hi < v`;
* the rest: `0 < τ`, `τ + a₀ < ρ₂` and `v + ρ₂ < L`;
* the zone: `Rg m₁ m₂` for `u ≤ m₁ ≤ v` and `L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − τ + ε`, for some `ε > 0`;
* the leaves: `D₁ < L − 1` and `max(D₁, 1) + D₁ + 2D₂ < 2L − 1`, where `D₁ = Σ_{S₁} hi + (t + ρ₂)·[eIn₁]` and
  `D₂ = Σ_{S₁ᶜ} hi + (t + ρ₂)·[¬eIn₁]`.

Then for every `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: for `rt` over the
`j`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q`)
forcing `rt` strictly decreasing, every `rt_i ≥ z₀` and `q^{lo_i} ≤ rt_i ≤ q^{hi_i}`,
`|Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))| ≤ ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)`.

The tree's primes are used twice. The first of them, the largest, join `c` until the product enters the window
`(⌈q^u⌉, ⌊q^v⌋]`; the next ones, below the last of those, are the rest, until their product reaches `⌈q^τ⌉`, so that
the rest lies in `[⌈q^τ⌉, ⌈q^τ⌉z₀) ⊂ [q^τ, q^{ρ₂}]`. A family with `c` in the window from the start has only the
second kind. The leaves have new primes of product at most `4q^{t+ρ₂}`. They pass through two trees, so the sums of
`1/d` over them carry two products `∏(1 + 1/p)`, at most `e·a₀/ε_w` and `e(L + 1)/ε_w`, and the level `k` is chosen
with `(2k + 4)³ζ(k)` small (`exists_k3`), where `SieveTwoComp.prop6_two` needs the square.

The file imports `SieveFill.lean` and `SieveTwoComp.lean`.
-/
import SieveFill
import SieveTwoComp

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6ib SieveFamilyTwo SieveTwoP6
  SieveTwoTerm SieveP6LeavesWide

namespace SieveFillComp

open Classical

/-! ### The level `k` -/

theorem cube_le_eight_pow (k : ℕ) : (((2 * k + 4 : ℕ) : ℝ)) ^ 3 ≤ 64 * 8 ^ k := by
  have h1 : k + 2 ≤ 2 ^ (k + 1) := by
    have := Nat.lt_two_pow_self (n := k + 1)
    omega
  have h2 : ((k : ℝ) + 2) ≤ 2 ^ (k + 1) := by exact_mod_cast h1
  have h3 : (((2 * k + 4 : ℕ) : ℝ)) = 2 * ((k : ℝ) + 2) := by push_cast; ring
  rw [h3, mul_pow, show (64 : ℝ) * 8 ^ k = 2 ^ 3 * (2 ^ (k + 1)) ^ 3 by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]; ring_nf]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 3) (by norm_num)

/-- For `C₀ ≥ 0`, `ε > 0` and `a₀ > 0` there is an even `k ≥ 2` with `2C₀² ≤ (k + 1)(k + 2)`,
`(2k + 4)³ζ(k) ≤ ε` and `c < (2k + 4)a₀`. -/
theorem exists_k3 {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {ε c a₀ : ℝ} (hε : 0 < ε) (ha₀ : 0 < a₀) :
    ∃ k : ℕ, Even k ∧ 2 ≤ k ∧ 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2) ∧
      (((2 * k + 4 : ℕ) : ℝ)) ^ 3 * SieveProp6.zeta C₀ k ≤ ε ∧ c < ((2 * k + 4 : ℕ) : ℝ) * a₀ := by
  set M : ℝ := 128 * Real.exp (2 * C₀ + 1) with hM
  have hM0 : 0 < M := by positivity
  set ε' : ℝ := ε / M with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hF := FloorSemiring.tendsto_pow_div_factorial_atTop (8 * C₀)
  have hG := (FloorSemiring.tendsto_pow_div_factorial_atTop C₀).comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hF.eventually (ge_mem_nhds hε'0))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (hG.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp (2 * C₀)) by positivity)))
  set m : ℕ := max (max N₁ N₂) (max (⌈2 * C₀ ^ 2⌉₊ + 1) (⌈c / a₀⌉₊ + 1)) with hm
  have hN1m : N₁ ≤ m := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hN2m : N₂ ≤ m := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hCm : ⌈2 * C₀ ^ 2⌉₊ + 1 ≤ m := le_trans (le_max_left _ (⌈c / a₀⌉₊ + 1)) (le_max_right _ _)
  have hcm : ⌈c / a₀⌉₊ + 1 ≤ m := le_trans (le_max_right (⌈2 * C₀ ^ 2⌉₊ + 1) _) (le_max_right _ _)
  refine ⟨2 * m, ⟨m, by ring⟩, by omega, ?_, ?_⟩
  · have h1 : (⌈2 * C₀ ^ 2⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hCm
    have h2 := Nat.le_ceil (2 * C₀ ^ 2)
    push_cast
    nlinarith
  have hk1 : N₁ ≤ 2 * m := by omega
  have hk2 : N₂ ≤ 2 * m := by omega
  have hF' : (8 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ ε' := hN₁ _ hk1
  have hG' : C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤ 1 / (2 * Real.exp (2 * C₀)) := hN₂ _ hk2
  have hexp : Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))) ≤
      Real.exp 1 := by
    apply Real.exp_le_exp.2
    have he : 0 < Real.exp (2 * C₀) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_left hG' (show (0 : ℝ) ≤ 2 * Real.exp (2 * C₀) by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    linarith
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 3 * SieveProp6.zeta C₀ (2 * m) ≤
      M * ((8 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
    unfold SieveProp6.zeta
    have h1 := cube_le_eight_pow (2 * m)
    have h2 : (0 : ℝ) ≤ Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) := by positivity
    calc (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 3 * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))))
        ≤ (64 * 8 ^ (2 * m)) * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp 1) := by
          apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hexp h2) (by positivity) (by positivity)
      _ = M * ((8 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
          rw [hM, mul_pow, Real.exp_add]
          ring
  have hzM : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 3 * SieveProp6.zeta C₀ (2 * m) ≤ ε := by
    calc _ ≤ M * ((8 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := hz
      _ ≤ M * ε' := mul_le_mul_of_nonneg_left hF' hM0.le
      _ = ε := by rw [hε']; field_simp
  refine ⟨hzM, ?_⟩
  · have h1 : (⌈c / a₀⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hcm
    have h2 := Nat.le_ceil (c / a₀)
    have h3 : c / a₀ < ((2 * (2 * m) + 4 : ℕ) : ℝ) := by push_cast; linarith
    rwa [div_lt_iff₀ ha₀] at h3

/-- The main term's coefficient with two products: for `E > 0`, `B > 0`, `K₁ ≥ 0`, `a₀ > 0`, `c > 0` and `η > 0`,
with `ε_w = c/(2k + 4)` and `(2k + 4)³Z ≤ ηc³/(4EB(K₁ + 1)a₀)`, the coefficient `4E(K₁B/ε_w)a₀Z/ε_w²` is at most
`η`. -/
theorem main_coef3 {E B K₁ a₀ Z εw c η : ℝ} {k : ℕ} (hE : 0 < E) (hB : 0 < B) (hK₁ : 0 ≤ K₁) (ha₀ : 0 < a₀)
    (hc : 0 < c) (hη : 0 < η) (hεw : εw = c / ((2 * k + 4 : ℕ) : ℝ))
    (hζε : ((2 * k + 4 : ℕ) : ℝ) ^ 3 * Z ≤ η * c ^ 3 / (4 * E * B * (K₁ + 1) * a₀)) :
    4 * E * (K₁ * (B / εw)) * a₀ * Z / εw ^ 2 ≤ η := by
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  have hA : 4 * E * (K₁ * (B / εw)) * a₀ * Z / εw ^ 2 =
      4 * E * B * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 3 * Z) / c ^ 3 := by
    rw [hεw]; field_simp
  have hB' : 4 * E * B * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 3 * Z) / c ^ 3 ≤
      4 * E * B * K₁ * a₀ * (η * c ^ 3 / (4 * E * B * (K₁ + 1) * a₀)) / c ^ 3 := by
    gcongr
  have hC : 4 * E * B * K₁ * a₀ * (η * c ^ 3 / (4 * E * B * (K₁ + 1) * a₀)) / c ^ 3 = η * (K₁ / (K₁ + 1)) := by
    field_simp
  have hD : η * (K₁ / (K₁ + 1)) ≤ η := by
    have : K₁ / (K₁ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  linarith

variable [Route]

set_option maxHeartbeats 6400000 in
/-- **The comparison in two variables with the rest among the tree's primes.** Assume `RouteOK` and Proposition 3′
in two variables at `L` on `Rg` (`hII`). Fix `j`, `J₀`, `Λ₁ ≥ 0`, the exponent `a₀ > 0` of `z₀ = ⌈q^{a₀}⌉`, boxes
`[q^{lo_i}, q^{hi_i}]`, a set `S₀` of indices, a leaf split `(S₁, eIn₁)`, a growth `t ≥ 0` and `η > 0`, with:
`0 < u`, `u + a₀ < v`, `u − Σ_{S₀} lo ≤ t`, `Σ_{S₀} hi < v`; `0 < τ`, `τ + a₀ < ρ₂`, `v + ρ₂ < L`; `Rg m₁ m₂` for
`u ≤ m₁ ≤ v` and `L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − τ + ε`, with `ε > 0`; `D₁ < L − 1` and
`max(D₁, 1) + D₁ + 2D₂ < 2L − 1`, where `D₁ = Σ_{S₁} hi + (t + ρ₂)·[eIn₁]` and
`D₂ = Σ_{S₁ᶜ} hi + (t + ρ₂)·[¬eIn₁]`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let
`rt` run over the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω` (taken at `m = 0`,
with `m`-parts `c(0)` at most `Λ₁ log q`) forcing `rt` strictly decreasing, every `rt_i ≥ z₀` and
`q^{lo_i} ≤ rt_i ≤ q^{hi_i}`. Then `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))`, `r = ∏rt`, is at most
`η q^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute value. -/
theorem prop6_fill [RouteOK] {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (j J₀ : ℕ) {Λ₁ a₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁)
    (ha₀ : 0 < a₀) (lo hi : Fin j → ℝ) (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool) {t u v τ ρ₂ ε : ℝ} (hu : 0 < u)
    (huv : u + a₀ < v) (hτ : 0 < τ) (hτρ : τ + a₀ < ρ₂) (hvρ : v + ρ₂ < L) (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - τ + ε → Rg m₁ m₂)
    (ht : 0 ≤ t) (hlo : u - ∑ i ∈ S₀, lo i ≤ t) (hhi : ∑ i ∈ S₀, hi i < v)
    (hD₁ : ∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0) < L - 1)
    (hD₂ : max (∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0)) 1 +
        (∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0)) +
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t + ρ₂)) < 2 * L - 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (GCmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) →
      ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  have hL2 := two_lt_L
  obtain ⟨C₀, hC₀1, hC⟩ := SieveRanges.rng_sum_le
  have hC₀ : 0 ≤ C₀ := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = t + ρ₂ := ⟨_, rfl⟩
  rw [← hTdef] at hD₁ hD₂
  have hρ₂0 : 0 < ρ₂ := by linarith
  -- the leaves' two blocks, and their margins
  obtain ⟨D₁, hD₁def⟩ : ∃ D₁ : ℝ, D₁ = ∑ i ∈ S₁, hi i + (if eIn₁ then T else 0) := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂def⟩ : ∃ D₂ : ℝ, D₂ = ∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T) := ⟨_, rfl⟩
  rw [← hD₁def] at hD₁ hD₂
  rw [← hD₂def] at hD₂
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = L - 1 - max D₁ 1 := ⟨_, rfl⟩
  have hA₀0 : 0 < A₀ := by
    rw [hA₀def]
    rcases le_total D₁ 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hA₀L : A₀ ≤ L - 2 := by rw [hA₀def]; linarith [le_max_right D₁ 1]
  have hA₀D : A₀ ≤ L - 1 - D₁ := by rw [hA₀def]; linarith [le_max_left D₁ 1]
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = L + A₀ - D₁ - 2 * D₂ := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσdef, hA₀def]; linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (1 / 32) (min (A₀ / 32) (σ / 32)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hc32 : c ≤ 1 / 32 := by rw [hcdef]; exact min_le_left _ _
  have hc16 : c ≤ 1 / 16 := by linarith
  have hcA : c ≤ A₀ / 32 := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcσ : c ≤ σ / 32 := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨AW, hAWdef⟩ : ∃ AW : ℝ, AW = A₀ - 2 * c := ⟨_, rfl⟩
  -- the sums of `1/d`, and `k` and `ε_w`
  have ha₀L : a₀ ≤ L := by linarith
  have ha₀L1 : a₀ ≤ L + 1 := by linarith
  have hL10 : (0 : ℝ) < L + 1 := by linarith
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = (Real.log (L + 1) - Real.log a₀ + 1) ^ j := ⟨_, rfl⟩
  have hlogpos : 0 ≤ Real.log (L + 1) - Real.log a₀ + 1 := by
    have := Real.log_le_log ha₀ ha₀L1
    linarith
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁def]; exact pow_nonneg hlogpos j
  obtain ⟨Bc, hBcdef⟩ : ∃ Bc : ℝ, Bc = 2 * Real.exp 1 * (L + 1) := ⟨_, rfl⟩
  have hBc0 : 0 < Bc := by rw [hBcdef]; positivity
  obtain ⟨k, hkev, hk2, hkC, hζε, hca⟩ := exists_k3 hC₀
    (ε := η * c ^ 3 / (4 * Real.exp 1 * Bc * (K₁ + 1) * a₀)) (c := c) (by positivity) ha₀
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  obtain ⟨εw, hεw⟩ : ∃ εw : ℝ, εw = c / ((2 * k + 4 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hεw0 : 0 < εw := by rw [hεw]; exact div_pos hc0 hk4
  have hεwa : εw < a₀ := by rw [hεw, div_lt_iff₀ hk4]; linarith
  have hεwL1 : εw ≤ L + 1 := by linarith
  have hεw7 : εw * ((2 * k + 7 : ℕ) : ℝ) ≤ 2 * c := by
    rw [hεw, div_mul_eq_mul_div, div_le_iff₀ hk4]
    push_cast
    nlinarith
  have hεwc : (2 * k + 4 : ℝ) * εw = c := by
    rw [hεw]
    push_cast
    field_simp
  -- the tree's depth, the comparisons' bound, and the chains' and leaves' `δ`
  obtain ⟨smax, hsmdef⟩ : ∃ smax : ℕ, smax = ⌈(L + 2) / εw⌉₊ := ⟨_, rfl⟩
  have hsm : L + 2 ≤ εw * smax := by
    have := Nat.le_ceil ((L + 2) / εw)
    rw [← hsmdef, div_le_iff₀ hεw0] at this
    linarith
  obtain ⟨Λ₁', hΛ₁'⟩ : ∃ Λ₁' : ℝ, Λ₁' = Λ₁ + L + 2 := ⟨_, rfl⟩
  have hΛ₁'0 : 0 ≤ Λ₁' := by rw [hΛ₁']; linarith
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = Λ₁' + ((j + 2 * smax : ℕ) : ℝ) * (L + 1) := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by
    have : (0 : ℝ) ≤ ((j + 2 * smax : ℕ) : ℝ) * (L + 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    rw [hΛ₀]; linarith
  obtain ⟨δ₁, hδ₁, q₁, hq₁⟩ :=
    chainOK2_of_zone hII hεw0 (j + 2 * smax) (J₀ + 1 + 2 * (smax * smax) + 5 * smax + 4) hΛ₁'0
  obtain ⟨δ₃, hδ₃, q₃, hq₃⟩ := leavesOK_wide two_lt_L (a := AW) (c := AW - 20 * c) (δ' := 4 * c) (κ := 16 * c)
    (by linarith) (by rw [hAWdef]; linarith) (by linarith) (by linarith) (by rw [hAWdef]; linarith) (by linarith)
    (by linarith) (by rw [hAWdef]; linarith) hεw0 hΛ₀0 (j + 2 * smax)
    (J₀ + 1 + 2 * (smax * smax) + 5 * smax + 4) hC₀ hC hkev (by omega) hkC (by rw [hεwc]; exact hc16)
  -- the bound of the sums of `1/d` over the leaves, the remainder's constant and the final `δ`
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = (K₁ * (Bc / εw)) * (Real.exp 1 * a₀ / εw) := ⟨_, rfl⟩
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  obtain ⟨Mrem, hMrem⟩ : ∃ Mrem : ℝ, Mrem = 24 * 2 ^ (2 * k + 7) * Kt := ⟨_, rfl⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (min c δ₁) δ₃ / 2 := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact half_pos (lt_min (lt_min hc0 hδ₁) hδ₃)
  have hm : 2 * δ₀ ≤ c ∧ 2 * δ₀ ≤ δ₁ ∧ 2 * δ₀ ≤ δ₃ := by
    have h1 := min_le_left (min c δ₁) δ₃
    have h2 := min_le_right (min c δ₁) δ₃
    have h3 := min_le_left c δ₁
    have h4 := min_le_right c δ₁
    rw [hδ₀]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- the conditions that hold for large `q`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧ 2 ≤ x ^ εw ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ a₀), 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 ∧
      ∑ p ∈ SieveRough.primesIn (x ^ a₀) (x ^ (L + 1 : ℝ)), 1 / (p : ℝ) ≤ Real.log (L + 1) - Real.log a₀ + 1 ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ (L + 1 : ℝ)), 1 / (p : ℝ) ≤ Real.log (L + 1) - Real.log εw + 1 ∧
      Mrem ≤ x ^ c ∧ 2 * (smax : ℝ) * smax + 3 * smax + 1 ≤ x ^ δ₀ ∧ 6 ≤ x ^ (v - u - a₀) ∧
      2 ≤ x ^ (v - ∑ i ∈ S₀, hi i) ∧ 8 ≤ x ^ ε ∧ 2 ≤ x ^ (L - ρ₂) ∧ 6 ≤ x ^ (ρ₂ - τ - a₀) ∧ 1 < x ^ τ ∧
      4 * 2 ^ (2 * k + 4) ≤ x ^ (L - 1 - AW - D₁ - c) ∧
      64 * 2 ^ (2 * k + 4) ≤ x ^ (L - -(AW - 20 * c) - D₁ - 2 * D₂ - c) :=
    (Filter.eventually_ge_atTop 3).and (((tendsto_rpow_atTop hεw0).eventually_ge_atTop _).and
      ((SieveRough.evLe_sum_inv hεw0 hεwa.le 1 one_pos).and ((SieveRough.evLe_sum_inv ha₀ ha₀L1 1 one_pos).and
      ((SieveRough.evLe_sum_inv hεw0 hεwL1 1 one_pos).and
      (((tendsto_rpow_atTop hc0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hδ₀0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hε).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hτ).eventually_gt_atTop _).and
      (((tendsto_rpow_atTop (by rw [hAWdef]; linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop (by rw [hσdef] at hcσ; rw [hAWdef]; linarith)).eventually_ge_atTop _))))))))))))))
  obtain ⟨q₄, hq₄⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀, hδ₀0, max q₁ (max q₃ q₄), ?_⟩
  intro q _ hq a ha Ω hΩlen hΩc hΩ
  obtain ⟨hx3, hxw, hM1, hM2, hM3, hMrem', hδ2, h6, h2hi, h8ε, h2ρ, h6ρ, h1τ, hsz₁, hsz₂⟩ :=
    hq₄ q (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq))
  have h2ε : 2 ≤ (q : ℝ) ^ ε := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hΩc' : ∀ C ∈ Ω, C.c 0 ≤ Λ₁' * Real.log q := fun C hC =>
    (hΩc C hC).trans (mul_le_mul_of_nonneg_right (by rw [hΛ₁']; linarith) hlogq.le)
  -- sizes against `x^{Λ₁'}` and `w^{s_max}`
  have hxL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 L_pos.le
  have h4L : 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 2) := by
    have h9 : (4 : ℝ) ≤ (q : ℝ) ^ (2 : ℝ) := by
      have h33 := mul_le_mul hx3 hx3 (by norm_num : (0 : ℝ) ≤ 3) hq0.le
      rw [Real.rpow_two, pow_two]
      linarith
    calc 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = (q : ℝ) ^ (L + 2) := by rw [Real.rpow_add hq0]; ring
  have hlogA : ∀ A : ℝ, 0 < A → A ≤ 4 * (q : ℝ) ^ L → Real.log A ≤ Λ₁' * Real.log q := fun A hA h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log hA (h.trans (h4L.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hΛ₁']; linarith))))
  have hw : (q : ℝ) ^ εw ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.le_ceil _
  have hsmA : ∀ A : ℝ, A ≤ 4 * (q : ℝ) ^ L → A ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax := fun A h =>
    calc A ≤ (q : ℝ) ^ (L + 2) := h.trans h4L
      _ ≤ (q : ℝ) ^ (εw * smax) := Real.rpow_le_rpow_of_exponent_le hq1 hsm
      _ = ((q : ℝ) ^ εw) ^ smax := by rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
      _ ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax := pow_le_pow_left₀ (by positivity) hw _
  -- `w` and `z₀`
  have hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := hxw.trans hw
    exact_mod_cast this
  have hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ εw by positivity)
    linarith
  have hza : (q : ℝ) ^ εw ≤ (q : ℝ) ^ a₀ := Real.rpow_le_rpow_of_exponent_le hq1 hεwa.le
  have hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌈(q : ℝ) ^ a₀⌉₊ := Nat.ceil_mono hza
  have hz0r : (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) < (q : ℝ) ^ a₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  have ha1 : (1 : ℝ) ≤ (q : ℝ) ^ a₀ := Real.one_le_rpow hq1 ha₀.le
  have hz₀2 : (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ a₀ := by linarith
  have haL : (q : ℝ) ^ a₀ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 ha₀L
  have hz₀ : ⌈(q : ℝ) ^ a₀⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1 :=
    (Nat.ceil_mono (by linarith : (q : ℝ) ^ a₀ ≤ 2 * (q : ℝ) ^ L)).trans (Nat.ceil_le_floor_add_one _)
  have hz1 : (0 : ℝ) < (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) := zero_lt_one.trans_le (Nat.one_le_cast.2 (by omega))
  have hlz := hlogA _ hz1 (by linarith)
  -- `N₁` and `N₂`
  have hN₂r : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hN₂1 : 1 ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hN₂0 : (0 : ℝ) < ⌊2 * (q : ℝ) ^ L⌋₊ := zero_lt_one.trans_le (Nat.one_le_cast.2 hN₂1)
  have hlN : Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ (L + 1) * Real.log q := by
    rw [← Real.log_rpow hq0]
    refine Real.log_le_log hN₂0 (hN₂r.trans ?_)
    calc 2 * (q : ℝ) ^ L ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (q : ℝ) ^ (L + 1) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
  have hΛ : Λ₁' * Real.log q + ((j + 2 * smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q := by
    have h1 := mul_le_mul_of_nonneg_left hlN (Nat.cast_nonneg (α := ℝ) (j + 2 * smax))
    have h2 := mul_le_mul_of_nonneg_right hΛ₀.symm.le hlogq.le
    linarith
  have hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁' * Real.log q := by
    refine hlogA _ (by positivity) ?_
    push_cast
    linarith only [hN₂r, hxL1]
  have hX : 1 ≤ (q : ℝ) ^ (L - 1 - 4 * c) := Real.one_le_rpow hq1 (by linarith)
  have hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.floor_mono (by linarith)
  -- the window `(P₁, P₂]` and the rest `(Ar, Br]`
  have hqu1 : (1 : ℝ) ≤ (q : ℝ) ^ u := Real.one_le_rpow hq1 hu.le
  have hqτ1 : (1 : ℝ) ≤ (q : ℝ) ^ τ := Real.one_le_rpow hq1 hτ.le
  have hqρ₂1 : (1 : ℝ) ≤ (q : ℝ) ^ ρ₂ := Real.one_le_rpow hq1 hρ₂0.le
  have hquv : 6 * (q : ℝ) ^ (u + a₀) ≤ (q : ℝ) ^ v := by
    have e : (q : ℝ) ^ v = (q : ℝ) ^ (v - u - a₀) * (q : ℝ) ^ (u + a₀) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  have hqτa : 6 * (q : ℝ) ^ (τ + a₀) ≤ (q : ℝ) ^ ρ₂ := by
    have e : (q : ℝ) ^ ρ₂ = (q : ℝ) ^ (ρ₂ - τ - a₀) * (q : ℝ) ^ (τ + a₀) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h6ρ (by positivity)
  have hqua1 : (1 : ℝ) ≤ (q : ℝ) ^ (u + a₀) := Real.one_le_rpow hq1 (by linarith)
  have hqv6 : (6 : ℝ) ≤ (q : ℝ) ^ v := by linarith
  have hP₁ge : (q : ℝ) ^ u ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := Nat.le_ceil _
  have hP₁lt : (⌈(q : ℝ) ^ u⌉₊ : ℝ) < (q : ℝ) ^ u + 1 := Nat.ceil_lt_add_one (by positivity)
  have hP₂le : (⌊(q : ℝ) ^ v⌋₊ : ℝ) ≤ (q : ℝ) ^ v := Nat.floor_le (by positivity)
  have hP₂gt : (q : ℝ) ^ v - 1 < (⌊(q : ℝ) ^ v⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hBrle : (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ ρ₂ := Nat.floor_le (by positivity)
  have hP₁1 : 1 ≤ ⌈(q : ℝ) ^ u⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hP₂1 : 1 ≤ ⌊(q : ℝ) ^ v⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBr1 : 1 ≤ ⌊(q : ℝ) ^ ρ₂⌋₊ := Nat.le_floor (by exact_mod_cast hqρ₂1)
  have hc2 : 2 ≤ ⌈(q : ℝ) ^ τ⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast h1τ)
  obtain ⟨Ar, hArdef⟩ : ∃ Ar : ℕ, Ar + 1 = ⌈(q : ℝ) ^ τ⌉₊ := ⟨⌈(q : ℝ) ^ τ⌉₊ - 1, by omega⟩
  have hAr1 : 1 ≤ Ar := by omega
  have hArR : (Ar : ℝ) + 1 = (⌈(q : ℝ) ^ τ⌉₊ : ℝ) := by exact_mod_cast hArdef
  have hArge : (q : ℝ) ^ τ ≤ (Ar : ℝ) + 1 := by rw [hArR]; exact Nat.le_ceil _
  have hArle : (Ar : ℝ) + 1 ≤ 2 * (q : ℝ) ^ τ := by
    rw [hArR]
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ τ by positivity)
    linarith
  have hτL : (q : ℝ) ^ τ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hAB : (⌈(q : ℝ) ^ u⌉₊ + 1) * ⌈(q : ℝ) ^ a₀⌉₊ ≤ ⌊(q : ℝ) ^ v⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    have e : (q : ℝ) ^ (u + a₀) = (q : ℝ) ^ u * (q : ℝ) ^ a₀ := Real.rpow_add hq0 _ _
    have h1 : ((⌈(q : ℝ) ^ u⌉₊ : ℝ) + 1) * (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) ≤ (3 * (q : ℝ) ^ u) * (2 * (q : ℝ) ^ a₀) :=
      mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg _) (by positivity)
    rw [e] at hquv
    linarith
  have hArB : (Ar + 1) * ⌈(q : ℝ) ^ a₀⌉₊ ≤ ⌊(q : ℝ) ^ ρ₂⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    have e : (q : ℝ) ^ (τ + a₀) = (q : ℝ) ^ τ * (q : ℝ) ^ a₀ := Real.rpow_add hq0 _ _
    have h1 : ((Ar : ℝ) + 1) * (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) ≤ (2 * (q : ℝ) ^ τ) * (2 * (q : ℝ) ^ a₀) :=
      mul_le_mul hArle hz₀2 (Nat.cast_nonneg _) (by positivity)
    have h2 : (0 : ℝ) < (q : ℝ) ^ (τ + a₀) := by positivity
    rw [e] at hqτa h2
    linarith only [h1, hqτa, h2, hBrle]
  have hBBr : ⌊(q : ℝ) ^ v⌋₊ * ⌊(q : ℝ) ^ ρ₂⌋₊ ≤ ⌊(q : ℝ) ^ L⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    calc (⌊(q : ℝ) ^ v⌋₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ v * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hP₂le hBrle (Nat.cast_nonneg _) (by positivity)
      _ = (q : ℝ) ^ (v + ρ₂) := (Real.rpow_add hq0 _ _).symm
      _ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 hvρ.le
  -- the zone where a stop's first variable is in its window and the rest has its size
  have hR : ∀ u' v' : ℝ, Real.logb q (⌈(q : ℝ) ^ u⌉₊ : ℝ) ≤ u' → u' ≤ Real.logb q (⌊(q : ℝ) ^ v⌋₊ : ℝ) →
      ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u' + v') →
      (q : ℝ) ^ (u' + v') ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (Ar + 1) : ℕ) : ℝ) → Rg u' v' := by
    intro u' v' h1 h2 h5 h6'
    have hlogb : ∀ y : ℝ, Real.logb q ((q : ℝ) ^ y) = y := fun y => Real.logb_rpow hq0 hq1'.ne'
    refine hzone u' v' ?_ ?_ ?_ ?_
    · exact le_trans ((hlogb u).symm.le.trans (Real.logb_le_logb_of_le hq1' (by positivity) hP₁ge)) h1
    · exact h2.trans ((Real.logb_le_logb_of_le hq1' (by exact_mod_cast hP₂1) hP₂le).trans (hlogb v).le)
    · -- `4q^{L−ρ₂−ε} ≤ ⌊N₁/Br⌋`
      refine (Real.rpow_le_rpow_left_iff hq1').1 ?_
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
    · -- `⌊N₂/⌈q^τ⌉⌋ ≤ q^{L−τ+ε}`
      refine (Real.rpow_le_rpow_left_iff hq1').1 (h6'.trans ?_)
      calc ((⌊2 * (q : ℝ) ^ L⌋₊ / (Ar + 1) : ℕ) : ℝ)
          ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / ((Ar + 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ (2 * (q : ℝ) ^ L) / (q : ℝ) ^ τ :=
            div_le_div₀ (by positivity) hN₂r (by positivity) (by push_cast; exact hArge)
        _ = 2 * (q : ℝ) ^ (L - τ) := by rw [mul_div_assoc, ← Real.rpow_sub hq0]
        _ ≤ (q : ℝ) ^ ε * (q : ℝ) ^ (L - τ) := mul_le_mul_of_nonneg_right h2ε (by positivity)
        _ = (q : ℝ) ^ (L - τ + ε) := by rw [← Real.rpow_add hq0]; congr 1; ring
  -- the chains and the leaves at `q`
  have hokC := hq₁ q (le_trans (le_max_left _ _) hq) a ha ⌈(q : ℝ) ^ u⌉₊ ⌊(q : ℝ) ^ v⌋₊ Ar
    ⌊(q : ℝ) ^ ρ₂⌋₊ hP₁1 hP₂1 hBr1 hBBr hR
  have hokL := hq₃ q (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hq)) a ha
  have hP₁4 : (⌈(q : ℝ) ^ u⌉₊ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ L := by
    have : (q : ℝ) ^ u ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    linarith
  have hAr4 : (Ar : ℝ) + 1 ≤ 4 * (q : ℝ) ^ L := by linarith only [hArle, hτL, hxL1]
  have hTτ : (q : ℝ) ^ τ ≤ (q : ℝ) ^ T := Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hTdef]; linarith)
  have hqT0 : (0 : ℝ) < (q : ℝ) ^ T := by positivity
  have hT1 : 4 * (q : ℝ) ^ t * (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) * ((Ar : ℝ) + 1) ≤ 4 * (q : ℝ) ^ T := by
    have hqt : (0 : ℝ) < (q : ℝ) ^ t := by positivity
    have h1 : 4 * (q : ℝ) ^ t * (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) * ((Ar : ℝ) + 1) ≤
        4 * (q : ℝ) ^ t * (2 * (q : ℝ) ^ a₀) * (2 * (q : ℝ) ^ τ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz₀2 (by positivity)) hArle (by positivity) (by positivity)
    have e1 : (q : ℝ) ^ (τ + a₀) = (q : ℝ) ^ τ * (q : ℝ) ^ a₀ := Real.rpow_add hq0 _ _
    have e2 : (q : ℝ) ^ T = (q : ℝ) ^ t * (q : ℝ) ^ ρ₂ := by rw [hTdef, Real.rpow_add hq0]
    have h2 : (q : ℝ) ^ t * (4 * ((q : ℝ) ^ τ * (q : ℝ) ^ a₀)) ≤ (q : ℝ) ^ t * (q : ℝ) ^ ρ₂ := by
      refine mul_le_mul_of_nonneg_left ?_ hqt.le
      rw [← e1]
      have : (0 : ℝ) < (q : ℝ) ^ (τ + a₀) := by positivity
      linarith only [hqτa, this]
    rw [e2]
    linarith only [h1, h2]
  have H := SieveFill.prop6_fill_core ha Ω S₀ S₁ eIn₁ lo hi hokL hokC hw2 hwle hwz hz₀ hΛ₁'0 hlz hlZ hΛ hX hN
    (by omega) le_rfl le_rfl hP₁1 hAr1 hAB hArB (hsmA _ hP₁4) (hsmA _ hAr4) (hlogA _ (by positivity) hP₁4)
    (hlogA _ (by positivity) hAr4)
    (fun s hs => by
      have e : (q : ℝ) ^ (t + ∑ i ∈ S₀, lo i) = (q : ℝ) ^ t * (q : ℝ) ^ (∑ i ∈ S₀, lo i) := Real.rpow_add hq0 _ _
      have h1 : (q : ℝ) ^ u ≤ (q : ℝ) ^ (t + ∑ i ∈ S₀, lo i) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      have h2 : (q : ℝ) ^ t * (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ (q : ℝ) ^ t * s :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      linarith)
    (by
      have e : (q : ℝ) ^ v = (q : ℝ) ^ (v - ∑ i ∈ S₀, hi i) * (q : ℝ) ^ (∑ i ∈ S₀, hi i) := by
        rw [← Real.rpow_add hq0]; congr 1; ring
      have h1 : 2 * (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ (q : ℝ) ^ v := by
        rw [e]
        exact mul_le_mul_of_nonneg_right h2hi (by positivity)
      have h2 : (0 : ℝ) < (q : ℝ) ^ (∑ i ∈ S₀, hi i) := by positivity
      linarith only [h1, h2, hP₂gt, hqv6])
    hT1 (by linarith only [hArle, hTτ, hqT0]) hεwc (by rw [← hD₁def]; exact hsz₁) (by rw [← hD₁def, ← hD₂def]; exact hsz₂) hC₀ hC hkev
    (by omega) hkC hΩc' hΩ
  -- the sums of `1/d` and of `1/p`
  have hprime : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∀ i, rt i ≤ ⌊2 * (q : ℝ) ^ L⌋₊ ∧ (rt i).Prime :=
    fun rt hrt i => SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)
  have h2L : 2 * (q : ℝ) ^ L < (q : ℝ) ^ (L + 1 : ℝ) := by
    have hX0 : 0 < (q : ℝ) ^ L := by positivity
    rw [Real.rpow_add hq0, Real.rpow_one]
    have := mul_lt_mul_of_pos_left (show (2 : ℝ) < q by linarith) hX0
    linarith
  have hsRT : ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ K₁ := by
    refine (SieveProp6.sum_RT_inv_le (s := SieveRough.primesIn ((q : ℝ) ^ a₀) ((q : ℝ) ^ (L + 1 : ℝ))) ?_).trans ?_
    · intro rt hrt
      rw [Fintype.mem_piFinset]
      intro i
      obtain ⟨-, hz, -⟩ := hΩ rt (fun i => (hprime rt hrt i).2) (Finset.mem_filter.1 hrt).2
      rw [SieveRough.mem_primesIn]
      refine ⟨(hprime rt hrt i).2, le_trans (Nat.le_ceil _) (by exact_mod_cast hz i), ?_⟩
      have h1 : (rt i : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (hprime rt hrt i).1
      linarith
    · rw [hK₁def]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => by positivity) hM2 j
  have hsP : ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ)) ≤ Real.exp 1 * a₀ / εw := by
    refine (SieveBrun.prod_one_add_le_exp _ _ fun p _ => by positivity).trans ?_
    have h : ∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 := hM1
    calc Real.exp (∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, 1 / (p : ℝ)) ≤
          Real.exp (Real.log a₀ - Real.log εw + 1) := Real.exp_le_exp.2 h
      _ = Real.exp 1 * a₀ / εw := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_log ha₀, Real.exp_log hεw0]
          ring
  have hsPN : 1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)) ≤ Bc / εw := by
    have hsub : primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1) ⊆
        SieveRough.primesIn ((q : ℝ) ^ εw) ((q : ℝ) ^ (L + 1 : ℝ)) := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := mem_primesIco.1 hp
      rw [SieveRough.mem_primesIn]
      refine ⟨h3, hw.trans (by exact_mod_cast h1), ?_⟩
      have h4 : (p : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (by omega : p ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
      linarith
    have h : ∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), 1 / (p : ℝ) ≤
        Real.log (L + 1) - Real.log εw + 1 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans hM3
    have h1 : ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)) ≤
        Real.exp 1 * (L + 1) / εw := by
      refine (SieveBrun.prod_one_add_le_exp _ _ fun p _ => by positivity).trans ?_
      calc Real.exp (∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), 1 / (p : ℝ)) ≤
            Real.exp (Real.log (L + 1) - Real.log εw + 1) := Real.exp_le_exp.2 h
        _ = Real.exp 1 * (L + 1) / εw := by
            rw [Real.exp_add, Real.exp_sub, Real.exp_log hL10, Real.exp_log hεw0]
            ring
    have h2 : 1 ≤ Real.exp 1 * (L + 1) / εw := by
      rw [le_div_iff₀ hεw0]
      have he : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith only [this]
      rw [one_mul]
      exact hεwL1.trans (le_mul_of_one_le_left hL10.le he)
    have e : Bc / εw = Real.exp 1 * (L + 1) / εw + Real.exp 1 * (L + 1) / εw := by rw [hBcdef]; ring
    rw [e]
    linarith only [h1, h2]
  have hsd : (∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
      ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ)) ≤ K₁ * (Real.exp 1 * a₀ / εw) :=
    mul_le_mul hsRT hsP (Finset.prod_nonneg fun p _ => by positivity) hK₁0
  have hsdt : ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
      ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ))) *
      (1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) ≤ Kt := by
    have h1 : (0 : ℝ) ≤ 1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)) :=
      add_nonneg zero_le_one (Finset.prod_nonneg fun p _ => by positivity)
    have h2 : (0 : ℝ) ≤ K₁ * (Real.exp 1 * a₀ / εw) := by positivity
    have := mul_le_mul hsd hsPN h1 h2
    rw [hKt]
    linarith only [this]
  -- `w`
  have hw1 : (1 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.one_le_cast.2 (by omega)
  have hlogw : εw * Real.log q ≤ Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log (by positivity) hw
  have hlogw0 : 0 < Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := lt_of_lt_of_le (mul_pos hεw0 hlogq) hlogw
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ q := Nat.cast_le.2 (Nat.totient_le q)
  have hζ := SieveProp6.zeta_nonneg hC₀ k
  -- the main term
  have hNN : ((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) ≤ (q : ℝ) ^ L + 1 := by
    have h2 : (q : ℝ) ^ L - 1 < (⌊(q : ℝ) ^ L⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hN0 : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
    have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
    linarith
  have hK1B0 : 0 ≤ K₁ * (Bc / εw) := by positivity
  have hmain : 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) * Kt ≤ η * (q : ℝ) ^ L / (q.totient * Real.log q) := by
    rw [hKt]
    refine le_trans ?_ (SieveProp6.main_term hζ hxL1 hφ hK1B0 (Real.exp_pos 1) ha₀ hεw0 hlogq hlogw
      (main_coef3 (Real.exp_pos 1) hBc0 hK₁0 ha₀ hc0 hη hεw hζε))
    have hdiv := div_le_div_of_nonneg_right hNN (mul_pos hφ hlogw0).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (by linarith)) (by positivity)
  -- the remainder
  have hJ := SieveProp6.Jw_spec hw2
  have hrem : 2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k *
      (q : ℝ) ^ (L - 1 - 4 * c) * Kt ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - c : ℝ) :=
    SieveProp6.rem_term hq1 hw1 hwle hεw7 le_rfl (by positivity) hKt0 hJ.2.1 hJ.2.2 hMrem hMrem' hφ hφq (by ring)
      (SieveProp6.rem_le hw1 _ k)
  -- the errors
  have hle : ∀ d : ℝ, 2 * δ₀ ≤ d → (q : ℝ) ^ (L - d) ≤ (q : ℝ) ^ (L - 2 * δ₀) :=
    fun d hd => Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hfin : (2 * (smax : ℝ) * smax + 3 * smax + 1) * (q : ℝ) ^ (L - 2 * δ₀) ≤ (q : ℝ) ^ (L - δ₀) := by
    have e : (q : ℝ) ^ (L - δ₀) = (q : ℝ) ^ δ₀ * (q : ℝ) ^ (L - 2 * δ₀) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right hδ2 (by positivity)
  have hφi : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hs0 : (0 : ℝ) ≤ (smax : ℝ) := Nat.cast_nonneg _
  obtain ⟨Mz, hMz⟩ : ∃ Mz : ℝ, Mz = 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := ⟨_, rfl⟩
  obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = 2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k *
      (q : ℝ) ^ (L - 1 - 4 * c) := ⟨_, rfl⟩
  have hMz0 : 0 ≤ Mz := by
    rw [hMz]
    exact mul_nonneg (mul_nonneg zero_le_two hζ) (div_nonneg hN0 (mul_pos hφ hlogw0).le)
  have hMr0 : 0 ≤ Mr := by
    rw [hMr]
    exact mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _)
  rw [← hMz, ← hMr] at H
  rw [← hMz] at hmain
  rw [← hMr] at hrem
  obtain ⟨SP, hSP⟩ : ∃ SP : ℝ, SP = ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
      ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ))) *
      (1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) := ⟨_, rfl⟩
  rw [← hSP] at H hsdt
  have h1 : (Mz + Mr) * SP ≤ (Mz + Mr) * Kt := mul_le_mul_of_nonneg_left hsdt (by linarith)
  have e₃ := mul_le_mul_of_nonneg_left (hle δ₃ hm.2.2) hφi
  have e₁ := mul_le_mul_of_nonneg_left (hle δ₁ hm.2.1) hφi
  have e₀ := mul_le_mul_of_nonneg_left (hle c hm.1) hφi
  have t3 := mul_le_mul_of_nonneg_left e₃ (by positivity : (0 : ℝ) ≤ 2 * (smax : ℝ) + smax * smax)
  have t1 := mul_le_mul_of_nonneg_left e₁ (by positivity : (0 : ℝ) ≤ (smax : ℝ) * smax + smax)
  have tf := mul_le_mul_of_nonneg_left hfin hφi
  have e5 : (q.totient : ℝ)⁻¹ * ((2 * (smax : ℝ) * smax + 3 * smax + 1) * (q : ℝ) ^ (L - 2 * δ₀)) =
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - 2 * δ₀) +
        (2 * (smax : ℝ) + smax * smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - 2 * δ₀)) +
        ((smax : ℝ) * smax + smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - 2 * δ₀)) := by ring
  have e6 : (Mz + Mr) * Kt = Mz * Kt + Mr * Kt := by ring
  linarith only [H, h1, e6, hmain, hrem, e₀, t3, t1, tf, e5]

omit [Route] in
/-- **The comparison in two variables with the rest among the tree's primes, for an exponent `2 < L ≤ 5/2`**:
`prop6_fill` with no route. -/
theorem prop6_fill_at {L : ℝ} (hL2 : 2 < L) (hL : L ≤ 5 / 2) {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (j J₀ : ℕ)
    {Λ₁ a₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁) (ha₀ : 0 < a₀) (lo hi : Fin j → ℝ) (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool)
    {t u v τ ρ₂ ε : ℝ} (hu : 0 < u) (huv : u + a₀ < v) (hτ : 0 < τ) (hτρ : τ + a₀ < ρ₂) (hvρ : v + ρ₂ < L)
    (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - τ + ε → Rg m₁ m₂)
    (ht : 0 ≤ t) (hlo : u - ∑ i ∈ S₀, lo i ≤ t) (hhi : ∑ i ∈ S₀, hi i < v)
    (hD₁ : ∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0) < L - 1)
    (hD₂ : max (∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0)) 1 +
        (∑ i ∈ S₁, hi i + (if eIn₁ then t + ρ₂ else 0)) +
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t + ρ₂)) < 2 * L - 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (GCmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) →
      ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  let _ : Route := SieveTwoTerm.routeOf L
  have _ : RouteOK := SieveTwoTerm.routeOK_of hL2 hL
  exact prop6_fill hII j J₀ hΛ₁ ha₀ lo hi S₀ S₁ eIn₁ hu huv hτ hτρ hvρ hε hzone ht hlo hhi hD₁ hD₂ hη

end SieveFillComp

#print axioms SieveFillComp.prop6_fill
#print axioms SieveFillComp.prop6_fill_at
