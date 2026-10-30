import ShortSieveLong

/-!
# Thin sets of prime tuples in the comparison interval

The boxes that straddle the boundary of a sieve term's region carry tuples of primes `g` whose coordinate `g_u` is
pinned, by the other coordinates, to an interval `[X, KX]` of bounded ratio. In the comparison interval
`(x − x^{1−ρ}, x]` such tuples are rare: one factor `1/log x` from the prime `g_v` that the product pins
(`ShortSieveLong.card_primes_short`), and one more from `Σ_{X ≤ g_u ≤ KX} 1/g_u`:

* `sum_inv_le_of_Icc`: Chebyshev, `Σ_{p ∈ F} 1/p ≤ K log 4/log X` for primes `F ⊆ [X, KX]`, `X ≥ 2`;
* `card_primes_comparison_le`: for `x` large, `Z ≥ x^c`, `12ρ < c`, `P ≥ 1`: the primes `b ≥ x^c` with
  `P b ∈ (x − x^{1−ρ}, x]` number at most `2x^{1−ρ}/(P c log x)`;
* `card_thin_le`: **the thin tuples.** For `d`-tuples of primes in `[x^c, x²)` with `g_u ∈ [X, KX]`, where `X`
  depends only on the coordinates other than `u` and `v ≠ u`, and with product in `(x − x^{1−ρ}, x]`: at most
  `C x^{1−ρ}/log² x` of them, with `C` depending on `d`, `c`, `K` only.
-/

open Finset Real
open scoped Chebyshev

namespace ShortSieveThin

/-- **Chebyshev's bound on `[X, KX]`.** For `X ≥ 2`, `K ≥ 1` and a set `F` of primes in `[X, KX]`:
`Σ_{p ∈ F} 1/p ≤ K log 4/log X`, from `#F · log X ≤ θ(KX) ≤ log 4 · KX`. -/
theorem sum_inv_le_of_Icc {X K : ℝ} (hX : 2 ≤ X) (hK : 1 ≤ K) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ X ≤ p ∧ (p : ℝ) ≤ K * X) :
    ∑ p ∈ F, 1 / (p : ℝ) ≤ K * Real.log 4 / Real.log X := by
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hsub : F ⊆ (Ioc 0 ⌊K * X⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, -, hpK⟩ := hF p hp
    exact mem_filter.2 ⟨mem_Ioc.2 ⟨hpp.pos, Nat.le_floor hpK⟩, hpp⟩
  have hlog : (F.card : ℝ) * Real.log X ≤ θ (K * X) := by
    rw [Chebyshev.theta]
    calc (F.card : ℝ) * Real.log X = ∑ p ∈ F, Real.log X := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ F, Real.log p := sum_le_sum fun p hp => Real.log_le_log hX0 (hF p hp).2.1
      _ ≤ ∑ p ∈ (Ioc 0 ⌊K * X⌋₊).filter Nat.Prime, Real.log p :=
          sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)
  have hθ : θ (K * X) ≤ Real.log 4 * (K * X) := Chebyshev.theta_le_log4_mul_x (by positivity)
  calc ∑ p ∈ F, 1 / (p : ℝ) ≤ ∑ _p ∈ F, 1 / X :=
        sum_le_sum fun p hp => one_div_le_one_div_of_le hX0 (hF p hp).2.1
    _ = F.card / X := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ K * Real.log 4 / Real.log X := by
        rw [div_le_div_iff₀ hX0 hlX]
        nlinarith

/-- **Primes pinned by a product in the comparison interval.** For `0 < c`, `12ρ < c` and `x` large: for every
natural `P ≥ 1`, the primes `b ≥ x^c` with `x − x^{1−ρ} < P b ≤ x` number at most `2x^{1−ρ}/(P · c log x)`. -/
theorem card_primes_comparison_le {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρc : 12 * ρ < c) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ P : ℕ, 0 < P → ∀ Q : Finset ℕ, (∀ b ∈ Q, b.Prime ∧ x ^ c ≤ b) →
      ((Q.filter fun b : ℕ => x - x ^ (1 - ρ) < (P : ℝ) * b ∧ (P : ℝ) * b ≤ x).card : ℝ) ≤
        2 * x ^ (1 - ρ) / (P * (c * Real.log x)) := by
  set σ : ℝ := (ρ / c + 1 / 12) / 2 with hσ
  have hρc' : ρ / c < 1 / 12 := by rw [div_lt_iff₀ hc]; linarith
  have hσ12 : σ < 1 / 12 := by rw [hσ]; linarith
  have hσρ : ρ / c < σ := by rw [hσ]; linarith
  have hσ0 : 0 < σ := lt_trans (div_pos hρ hc) hσρ
  have hcσ : ρ ≤ c * σ := by
    have := (div_lt_iff₀ hc).1 hσρ
    linarith
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.1 (ShortSieveLong.card_primes_short hσ12 (ε := 1) one_pos)
  -- `x` large: `x^c ≥ max Z₀ 2`, `x^ρ ≥ 2`, `x ≥ 2`
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hc).eventually_ge_atTop (max Z₀ 2))
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop hρ).eventually_ge_atTop (2 : ℝ))
  refine ⟨max (max x₁ x₂) 2, fun x hx P hP Q hQ => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxc : max Z₀ 2 ≤ x ^ c := hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have hxρ : 2 ≤ x ^ ρ := hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  set y₁ : ℝ := x ^ (1 - ρ) with hy₁
  have hy₁x : y₁ = x / x ^ ρ := by rw [hy₁, Real.rpow_sub hx0, Real.rpow_one]
  have hy₁0 : 0 < y₁ := by rw [hy₁]; positivity
  have hy₁le : y₁ ≤ x / 2 := by rw [hy₁x]; exact div_le_div_of_nonneg_left hx0.le (by norm_num) hxρ
  set Z : ℝ := x / P with hZ
  set H : ℝ := y₁ / P with hH
  have hZ0 : 0 < Z := by positivity
  have hH0 : 0 < H := by positivity
  by_cases hZc : x ^ c ≤ Z
  · -- the interval `((x − y₁)/P, x/P]`, of relative length `x^{−ρ} ≥ Z^{−σ}`
    have hZbig : Z₀ ≤ Z := le_trans (le_trans (le_max_left _ _) hxc) hZc
    have hZ1 : Z ^ (1 - σ) ≤ H := by
      -- `Z^{−σ} ≤ (x^c)^{−σ} ≤ x^{−ρ}`
      have hZσ : x ^ ρ ≤ Z ^ σ := by
        calc x ^ ρ ≤ x ^ (c * σ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hcσ
          _ = (x ^ c) ^ σ := by rw [Real.rpow_mul hx0.le]
          _ ≤ Z ^ σ := Real.rpow_le_rpow (by positivity) hZc hσ0.le
      have e1 : Z ^ (1 - σ) = Z / Z ^ σ := by rw [Real.rpow_sub hZ0, Real.rpow_one]
      have e2 : H = Z / x ^ ρ := by rw [hH, hZ, hy₁x]; field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_left hZ0.le (by positivity) hZσ
    have hZ2 : H ≤ Z / 2 := by
      calc H = y₁ / P := rfl
        _ ≤ (x / 2) / P := div_le_div_of_nonneg_right hy₁le hP0.le
        _ = Z / 2 := by rw [hZ]; ring
    have hcount := (hZ₀ Z hZbig H hZ1 hZ2).2
    have hsub : Q.filter (fun b : ℕ => x - y₁ < (P : ℝ) * b ∧ (P : ℝ) * b ≤ x) ⊆
        (Ioc ⌊Z - H⌋₊ ⌊Z⌋₊).filter Nat.Prime := by
      intro b hb
      obtain ⟨hbQ, hb1, hb2⟩ := mem_filter.1 hb
      refine mem_filter.2 ⟨?_, (hQ b hbQ).1⟩
      have hZH : Z - H = (x - y₁) / P := by rw [hZ, hH]; ring
      rw [ShortSieveLong.mem_Ioc_floor (by rw [hZH]; exact div_nonneg (by linarith) hP0.le) hH0.le, hZH, hZ,
        div_lt_iff₀ hP0, le_div_iff₀ hP0]
      constructor <;> linarith
    have hlZ : c * Real.log x ≤ Real.log Z := by
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log (by positivity) hZc
    have hcl : 0 < c * Real.log x := mul_pos hc hlx
    calc ((Q.filter fun b : ℕ => x - y₁ < (P : ℝ) * b ∧ (P : ℝ) * b ≤ x).card : ℝ)
        ≤ ((Ioc ⌊Z - H⌋₊ ⌊Z⌋₊).filter Nat.Prime).card := by exact_mod_cast card_le_card hsub
      _ ≤ (1 + 1) * H / Real.log Z := hcount
      _ ≤ 2 * H / (c * Real.log x) := by
          rw [show (1 + 1 : ℝ) = 2 by norm_num]
          exact div_le_div_of_nonneg_left (by positivity) hcl hlZ
      _ = 2 * y₁ / (P * (c * Real.log x)) := by rw [hH]; field_simp
  · -- no prime `b ≥ x^c` fits below `x/P`
    have hempty : Q.filter (fun b : ℕ => x - y₁ < (P : ℝ) * b ∧ (P : ℝ) * b ≤ x) = ∅ := by
      refine filter_eq_empty_iff.2 fun b hbQ hb => ?_
      have hbZ : (b : ℝ) ≤ Z := by rw [hZ, le_div_iff₀ hP0]; linarith [hb.2]
      exact hZc (le_trans (hQ b hbQ).2 hbZ)
    rw [hempty, card_empty, Nat.cast_zero]
    positivity

/-- A product over `Fin d` splits into the coordinates other than `u`, `v`, and `u`, `v`. -/
theorem prod_split {d : ℕ} {u v : Fin d} (huv : u ≠ v) (f : Fin d → ℝ) :
    ∏ j, f j = (∏ j : {j : Fin d // j ≠ u ∧ j ≠ v}, f j) * (f u * f v) := by
  rw [← prod_filter_mul_prod_filter_not univ (fun j => j ≠ u ∧ j ≠ v)]
  congr 1
  · exact prod_subtype _ (fun j => by simp) f
  · have e : univ.filter (fun j : Fin d => ¬ (j ≠ u ∧ j ≠ v)) = {u, v} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      tauto
    rw [e, prod_pair huv]

/-- **The thin tuples.** Let `0 < c ≤ 1`, `12ρ < c` and `K ≥ 1`. There are `C ≥ 0` and `x₀` such that for `x ≥ x₀`,
coordinates `u ≠ v` and any `X` of the coordinates other than `u` and `v`: the `d`-tuples `g` of primes in `[x^c, x²)`
with `X ≤ g_u ≤ KX` and `x − x^{1−ρ} < ∏g ≤ x` number at most `C x^{1−ρ}/log² x`. The prime `g_v` is pinned by the
product (`card_primes_comparison_le`, a factor `1/(c log x)`), and `Σ_{X ≤ g_u ≤ KX} 1/g_u ≤ K log 4/(c log x)`. -/
theorem card_thin_le (d : ℕ) {c K ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hρc : 12 * ρ < c) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ u v : Fin d, u ≠ v →
      ∀ X : ({j : Fin d // j ≠ u ∧ j ≠ v} → ℕ) → ℝ,
        (((Fintype.piFinset fun _ : Fin d => SieveRough.primesIn (x ^ c) (x ^ (2 : ℝ))).filter fun g =>
          X (fun j => g j) ≤ g u ∧ (g u : ℝ) ≤ K * X (fun j => g j) ∧
            x - x ^ (1 - ρ) < ∏ j, (g j : ℝ) ∧ ∏ j, (g j : ℝ) ≤ x).card : ℝ) ≤
          C * x ^ (1 - ρ) / Real.log x ^ 2 := by
  -- `Σ_{x^c ≤ p < x²} 1/p ≤ log 2 − log c + 1`
  set S₀ : ℝ := max (Real.log 2 - Real.log c + 1) 1 with hS₀
  have hS₀1 : 1 ≤ S₀ := le_max_right _ _
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (SieveRough.evLe_sum_inv hc (by linarith : c ≤ (2 : ℝ)) 1 one_pos)
  obtain ⟨x₂, hx₂⟩ := card_primes_comparison_le hc hρ hρc
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop hc).eventually_ge_atTop (2 : ℝ))
  refine ⟨2 / c * (K * Real.log 4 / c) * S₀ ^ d, max (max x₁ x₂) (max x₃ 2), by positivity,
    fun x hx u v huv X => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc2 : 2 ≤ x ^ c := hx₃ x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
  have hxx : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hcl : 0 < c * Real.log x := mul_pos hc hlx
  set Q := SieveRough.primesIn (x ^ c) (x ^ (2 : ℝ)) with hQ
  have hQp : ∀ b ∈ Q, b.Prime ∧ x ^ c ≤ b := fun b hb => by
    obtain ⟨h1, h2, -⟩ := SieveRough.mem_primesIn.1 hb
    exact ⟨h1, h2⟩
  have hS : ∑ p ∈ Q, 1 / (p : ℝ) ≤ S₀ := by
    have := hx₁ x hx1
    dsimp only at this
    exact this.trans (by rw [hS₀]; exact le_max_left _ _)
  have hS0 : 0 ≤ ∑ p ∈ Q, 1 / (p : ℝ) := sum_nonneg fun p _ => by positivity
  set y₁ : ℝ := x ^ (1 - ρ) with hy₁
  set T := Fintype.piFinset fun _ : Fin d => Q with hT
  set F := T.filter fun g => X (fun j => g j) ≤ g u ∧ (g u : ℝ) ≤ K * X (fun j => g j) ∧
    x - y₁ < ∏ j, (g j : ℝ) ∧ ∏ j, (g j : ℝ) ≤ x with hF
  set TR := Fintype.piFinset fun _ : {j : Fin d // j ≠ u ∧ j ≠ v} => Q with hTR
  set rest : (Fin d → ℕ) → ({j : Fin d // j ≠ u ∧ j ≠ v} → ℕ) := fun g j => g j with hrest
  -- one fiber `rest g = h, g u = a`: `g v` is pinned by the product
  have hfib : ∀ h ∈ TR, ∀ a ∈ Q, ((F.filter fun g => rest g = h ∧ g u = a).card : ℝ) ≤
      2 * y₁ / ((∏ j, (h j : ℝ)) * a * (c * Real.log x)) := by
    intro h hh a ha
    have hPpos : 0 < (∏ j, h j) * a := by
      refine Nat.mul_pos (prod_pos fun j _ => ?_) (hQp a ha).1.pos
      exact (hQp _ ((Fintype.mem_piFinset.1 hh) j)).1.pos
    have hcard := hx₂ x hx2 ((∏ j, h j) * a) hPpos Q hQp
    push_cast at hcard
    refine le_trans ?_ hcard
    have hmaps : ∀ g ∈ F.filter (fun g => rest g = h ∧ g u = a),
        g v ∈ Q.filter (fun b : ℕ => x - x ^ (1 - ρ) < (∏ i, (h i : ℝ)) * a * b ∧
          (∏ i, (h i : ℝ)) * a * b ≤ x) := by
      intro g hg
      obtain ⟨hgF, hgh, hga⟩ := mem_filter.1 hg
      obtain ⟨hgT, -, -, hp1, hp2⟩ := mem_filter.1 hgF
      have hsplit : ∏ j, (g j : ℝ) = (∏ j : {j : Fin d // j ≠ u ∧ j ≠ v}, (g j : ℝ)) * ((g u : ℝ) * (g v : ℝ)) :=
        prod_split huv (fun j => (g j : ℝ))
      have hrestprod : ∏ j : {j : Fin d // j ≠ u ∧ j ≠ v}, (g j : ℝ) = ∏ j, (h j : ℝ) := by
        rw [← hgh]
      rw [hsplit, hrestprod, hga, ← mul_assoc] at hp1 hp2
      exact mem_filter.2 ⟨(Fintype.mem_piFinset.1 hgT) v, by rw [← hy₁]; exact hp1, hp2⟩
    have hinj : Set.InjOn (fun g : Fin d → ℕ => g v) ↑(F.filter (fun g => rest g = h ∧ g u = a)) := by
      intro g hg g' hg' hgg'
      obtain ⟨-, hgh, hga⟩ := mem_filter.1 (mem_coe.1 hg)
      obtain ⟨-, hgh', hga'⟩ := mem_filter.1 (mem_coe.1 hg')
      funext j
      by_cases hju : j = u
      · rw [hju, hga, hga']
      by_cases hjv : j = v
      · rw [hjv]; exact hgg'
      exact congrFun (hgh.trans hgh'.symm) ⟨j, hju, hjv⟩
    exact_mod_cast card_le_card_of_injOn (fun g : Fin d → ℕ => g v) hmaps hinj
  -- the sum over `g_u ∈ [X, KX]`
  have hsumA : ∀ h : {j : Fin d // j ≠ u ∧ j ≠ v} → ℕ, ∑ a ∈ Q.filter (fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h), 1 / (a : ℝ) ≤
      K * Real.log 4 / (c * Real.log x) := by
    intro h
    set X' : ℝ := max (X h) (x ^ c) with hX'
    have hX'2 : 2 ≤ X' := le_trans hxc2 (le_max_right _ _)
    have hb := sum_inv_le_of_Icc hX'2 hK (Q.filter fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h) fun a ha => by
      obtain ⟨haQ, ha1, ha2⟩ := mem_filter.1 ha
      obtain ⟨hap, hac⟩ := hQp a haQ
      refine ⟨hap, max_le ha1 hac, ha2.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    refine hb.trans (div_le_div_of_nonneg_left (by positivity) hcl ?_)
    rw [← Real.log_rpow hx0]
    exact Real.log_le_log (by positivity) (le_max_right _ _)
  -- assemble: fibers over `rest`, then over `g_u`
  have hmaps : ∀ g ∈ F, rest g ∈ TR := fun g hg => by
    have hgT := (mem_filter.1 hg).1
    exact Fintype.mem_piFinset.2 fun j => (Fintype.mem_piFinset.1 hgT) j
  have hstep1 : (F.card : ℝ) = ∑ h ∈ TR, ((F.filter fun g => rest g = h).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_fiberwise hmaps
  have hstep2 : ∀ h ∈ TR, ((F.filter fun g => rest g = h).card : ℝ) ≤
      ∑ a ∈ Q.filter (fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h),
        ((F.filter fun g => rest g = h ∧ g u = a).card : ℝ) := by
    intro h hh
    have hmaps' : ∀ g ∈ F.filter (fun g => rest g = h),
        g u ∈ Q.filter (fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h) := by
      intro g hg
      obtain ⟨hgF, hgh⟩ := mem_filter.1 hg
      obtain ⟨hgT, h1, h2, -⟩ := mem_filter.1 hgF
      have e : (fun j : {j : Fin d // j ≠ u ∧ j ≠ v} => g j) = h := hgh
      rw [e] at h1 h2
      exact mem_filter.2 ⟨(Fintype.mem_piFinset.1 hgT) u, h1, h2⟩
    rw [card_eq_sum_card_fiberwise hmaps']
    push_cast
    refine le_of_eq (sum_congr rfl fun a _ => ?_)
    congr 2
    ext g
    simp only [mem_filter]
    tauto
  calc (F.card : ℝ) = ∑ h ∈ TR, ((F.filter fun g => rest g = h).card : ℝ) := hstep1
    _ ≤ ∑ h ∈ TR, ∑ a ∈ Q.filter (fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h),
          2 * y₁ / ((∏ j, (h j : ℝ)) * a * (c * Real.log x)) := by
        refine sum_le_sum fun h hh => (hstep2 h hh).trans (sum_le_sum fun a ha => ?_)
        exact hfib h hh a (mem_filter.1 ha).1
    _ = 2 * y₁ / (c * Real.log x) * ∑ h ∈ TR, (∏ j, (1 / (h j : ℝ))) *
          ∑ a ∈ Q.filter (fun a : ℕ => X h ≤ (a : ℝ) ∧ (a : ℝ) ≤ K * X h), 1 / (a : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun h hh => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun a ha => ?_
        rw [prod_div_distrib, prod_const_one]
        field_simp
    _ ≤ 2 * y₁ / (c * Real.log x) * ∑ h ∈ TR, (∏ j, (1 / (h j : ℝ))) * (K * Real.log 4 / (c * Real.log x)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun h _ => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (hsumA h) (prod_nonneg fun j _ => by positivity)
    _ = 2 * y₁ / (c * Real.log x) * (K * Real.log 4 / (c * Real.log x)) *
          ∏ _j : {j : Fin d // j ≠ u ∧ j ≠ v}, ∑ p ∈ Q, 1 / (p : ℝ) := by
        rw [← sum_mul, prod_univ_sum]
        ring
    _ ≤ 2 * y₁ / (c * Real.log x) * (K * Real.log 4 / (c * Real.log x)) * S₀ ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [prod_const]
        calc (∑ p ∈ Q, 1 / (p : ℝ)) ^ (univ : Finset {j : Fin d // j ≠ u ∧ j ≠ v}).card ≤ S₀ ^ (univ : Finset {j : Fin d // j ≠ u ∧ j ≠ v}).card :=
              pow_le_pow_left₀ hS0 hS _
          _ ≤ S₀ ^ d := by
              refine pow_le_pow_right₀ hS₀1 ?_
              calc (univ : Finset {j : Fin d // j ≠ u ∧ j ≠ v}).card = Fintype.card {j : Fin d // j ≠ u ∧ j ≠ v} := card_univ
                _ ≤ Fintype.card (Fin d) := Fintype.card_subtype_le _
                _ = d := Fintype.card_fin d
    _ = 2 / c * (K * Real.log 4 / c) * S₀ ^ d * x ^ (1 - ρ) / Real.log x ^ 2 := by
        rw [hy₁]
        field_simp

end ShortSieveThin

#print axioms ShortSieveThin.card_primes_comparison_le
#print axioms ShortSieveThin.card_thin_le
