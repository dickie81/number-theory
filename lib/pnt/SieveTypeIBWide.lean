/-
# The bilinear Type I estimate without the condition `2HDm < q`

Plain statements, in the notation of `SieveTypeIB.lean`: `e(x) = e^{2πix/q}`, `dw q a n = 1[n ≡ a] − 1[(n, q) =
1]/φ(q)`, `ŵ(h) = Σ_{k∈S} w(k)e(hk)` and `E_w` for a weight `w` on a finite set `S`, coefficients `α` on `D₁` and `β`
on `D₂`, sets of naturals prime to `q`.

`SieveTypeIB.typeIB_bound` asks that `2HDm < q`, where `D₂ ⊆ [1, Dm]` and `[−H, H]` holds the frequencies at which
`ŵ` is not small: then the congruence `td₂′ ≡ t′d₂ (mod q)` on the diagonal is an equation in the integers, and for
each `(t, d₂′)` the pairs `(t′, d₂)` number at most `F`, a bound for the number of divisors of the `|t|d`. Without
the condition the product `t′d₂` is one of the integers of `[−HDm, HDm]` in the class of `td₂′`, at most
`⌊2HDm/q⌋ + 1` of them, and each is `t′d₂` for at most `F` pairs. So the estimate holds for every `H` with `2H < q`,
with `F(⌊2HDm/q⌋ + 1)` in place of `F`.

* `card_Icc_cast_eq_le`: the integers of `[−M, M]` in one residue class mod `q` number at most `⌊2M/q⌋ + 1`.
* `card_fiber_cong_le`: for `J ⊆ [−H, H] ∖ {0}` and `D₂ ⊆ [1, Dm]`, if every `|t|d` (`t ∈ J`, `d ∈ D₂`) has at most
  `F` divisors, the pairs `(t′, d)` of `J × D₂` with `t′d` in a given class mod `q` number at most
  `F(⌊2HDm/q⌋ + 1)`.
* `diag_le_wide`: the diagonal sum of `SieveTypeIB.norm_sum_B_le` on the integer frequencies of `J` is at most
  `F(⌊2HDm/q⌋ + 1)(Σ_{t∈J}|c_t|²)(Σ_{d∈D₂}|β(d)|²)`.
* `typeIB_bound_wide`, **the estimate**: let `a` be a unit mod `q`, `D₂ ⊆ [1, Dm]`, `2H < q`, every residue the
  inverse of at most `m` elements of `D₁`, every `|t|d` with `0 < |t| ≤ H` and `d ∈ D₂` with at most `F` divisors,
  and `|ŵ(h)| ≤ W` at the frequencies `h ≠ 0` off the image of `[−H, H]`. Then
  `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k)|` is at most
  `(Σ|α|²)^{1/2}(mF(⌊2HDm/q⌋ + 1)(Σ|β|²)·q⁻¹Σ_h|ŵ(h)|²)^{1/2} + W(Σ|α|)(Σ|β|) + |(Σα)(Σβ)E_w/φ(q)|`.
  For `2HDm < q` the factor `⌊2HDm/q⌋ + 1` is `1`, and this is `SieveTypeIB.typeIB_bound`.
* `typeIB_spline_wide`: the same with a spline weight on its support, as `SieveSpline.typeIB_spline`.

The proof:

* `card_Icc_cast_eq_le`: `n ↦ ⌊(n + M)/q⌋` maps the class into `[0, ⌊2M/q⌋]`, and is injective on it, since two
  integers of the class with the same quotient have the same remainder.
* `card_fiber_cong_le`: the products `t′d` of the pairs lie in `[−HDm, HDm]` and in the class
  (`card_Icc_cast_eq_le`), and the pairs with a given product `t₀d₀` number at most the divisors of `|t₀|d₀`
  (`SieveTypeIB.card_fiber_le`).
* `diag_le_wide`: as `SieveTypeIB.diag_le`, on the congruence itself: `|c_t||β_d||c_{t′}||β_{d′}| ≤
  ½(|c_t|²|β_{d′}|² + |c_{t′}|²|β_d|²)`, the two halves are equal by the symmetry of the congruence, and for each
  `(t, d′)` the pairs `(t′, d)` are counted by `card_fiber_cong_le`.
* `typeIB_bound_wide`: `SieveTypeIB.sum_bilinear`; the frequencies `0 < |t| ≤ H` by `SieveTypeIB.norm_sum_B_le` and
  `diag_le_wide`, the others by `SieveTypeIB.norm_Bh_le`.

The file imports `SieveSpline.lean` (which imports `SieveTypeIB.lean`).
-/
import SieveSpline

open Finset Complex

namespace SieveTypeIB

variable {q : ℕ} [NeZero q]

/-! ### The count on the congruence -/

/-- The integers of `[−M, M]` in one residue class mod `q` number at most `⌊2M/q⌋ + 1`. -/
theorem card_Icc_cast_eq_le (M : ℕ) (ρ : ZMod q) :
    #((Finset.Icc (-(M : ℤ)) M).filter (fun n : ℤ => (n : ZMod q) = ρ)) ≤ 2 * M / q + 1 := by
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  rw [← Finset.card_range (2 * M / q + 1)]
  refine Finset.card_le_card_of_injOn (fun n : ℤ => ((n + M) / q).toNat) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, Finset.mem_range]
    have h0 : (0 : ℤ) ≤ (n + M) / q := Int.ediv_nonneg (by linarith [hn.1.1]) hq.le
    have h1 : (n + M) / q ≤ ((2 * M / q : ℕ) : ℤ) := by
      have h := Int.ediv_le_ediv hq (show n + (M : ℤ) ≤ ((2 * M : ℕ) : ℤ) by push_cast; linarith [hn.1.2])
      exact_mod_cast h
    have h2 : (((n + M) / q).toNat : ℤ) = (n + M) / q := Int.toNat_of_nonneg h0
    show ((n + M) / q).toNat < 2 * M / q + 1
    have h3 : (((n + M) / q).toNat : ℤ) < ((2 * M / q + 1 : ℕ) : ℤ) := by
      rw [h2, Nat.cast_add, Nat.cast_one]; linarith
    exact_mod_cast h3
  · intro n hn n' hn' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn hn'
    have h0 : (0 : ℤ) ≤ (n + M) / q := Int.ediv_nonneg (by linarith [hn.1.1]) hq.le
    have h0' : (0 : ℤ) ≤ (n' + M) / q := Int.ediv_nonneg (by linarith [hn'.1.1]) hq.le
    have hdiv : (n + M) / q = (n' + M) / q := by
      have h' : (((n + M) / q).toNat : ℤ) = (((n' + M) / q).toNat : ℤ) := congrArg (fun k : ℕ => (k : ℤ)) h
      rwa [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h0'] at h'
    -- the two integers differ by a multiple `qk` of `q`, and the quotients differ by `k`
    have hcong : (n : ZMod q) = (n' : ZMod q) := hn.2.trans hn'.2.symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcong
    obtain ⟨k, hk⟩ := hcong
    have e : n' + M = (n + M) + q * k := by linarith
    rw [e, Int.add_mul_ediv_left _ _ hq.ne'] at hdiv
    have hk0 : k = 0 := by linarith
    rw [hk0, mul_zero] at hk
    linarith

/-- **The pairs on the congruence.** For `J ⊆ [−H, H] ∖ {0}` and `D₂ ⊆ [1, Dm]`, if every `|t|d` (`t ∈ J`,
`d ∈ D₂`) has at most `F` divisors, the pairs `(t′, d)` of `J × D₂` with `t′d` in the class `ρ` mod `q` number at
most `F(⌊2HDm/q⌋ + 1)`. -/
theorem card_fiber_cong_le (J : Finset ℤ) (D₂ : Finset ℕ) {H Dm F : ℕ} (hD₂0 : ∀ d ∈ D₂, 0 < d)
    (hDm : ∀ d ∈ D₂, d ≤ Dm) (hJ : ∀ t ∈ J, t ≠ 0 ∧ t.natAbs ≤ H)
    (hF : ∀ t ∈ J, ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F) (ρ : ZMod q) :
    #((J ×ˢ D₂).filter (fun y : ℤ × ℕ => ((y.1 * (y.2 : ℤ) : ℤ) : ZMod q) = ρ)) ≤
      F * (2 * (H * Dm) / q + 1) := by
  classical
  set P := (J ×ˢ D₂).filter (fun y : ℤ × ℕ => ((y.1 * (y.2 : ℤ) : ℤ) : ZMod q) = ρ) with hP
  -- the pairs with a given product
  have hfib : ∀ n ∈ P.image (fun y : ℤ × ℕ => y.1 * (y.2 : ℤ)),
      #(P.filter (fun y : ℤ × ℕ => y.1 * (y.2 : ℤ) = n)) ≤ F := by
    intro n hn
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hn
    rw [hP, Finset.mem_filter, Finset.mem_product] at hy₀
    have h1 := card_fiber_le J D₂ (t := y₀.1) (d' := y₀.2) (hJ _ hy₀.1.1).1 (hD₂0 _ hy₀.1.2) hD₂0
    refine (Finset.card_le_card ?_).trans (h1.trans (hF _ hy₀.1.1 _ hy₀.1.2))
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    have hyP := hy.1
    rw [hP, Finset.mem_filter] at hyP
    exact ⟨hyP.1, hy.2⟩
  -- the products lie in `[−HDm, HDm]` and in the class
  have himg : P.image (fun y : ℤ × ℕ => y.1 * (y.2 : ℤ)) ⊆
      (Finset.Icc (-((H * Dm : ℕ) : ℤ)) (H * Dm : ℕ)).filter (fun n : ℤ => (n : ZMod q) = ρ) := by
    intro n hn
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hn
    rw [hP, Finset.mem_filter, Finset.mem_product] at hy
    rw [Finset.mem_filter, Finset.mem_Icc]
    have habs : |y.1 * (y.2 : ℤ)| ≤ ((H * Dm : ℕ) : ℤ) := by
      rw [abs_mul, Int.abs_natCast]
      have h1 : |y.1| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast (hJ _ hy.1.1).2
      have h2 : (y.2 : ℤ) ≤ (Dm : ℤ) := by exact_mod_cast hDm _ hy.1.2
      push_cast
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact ⟨abs_le.1 habs, hy.2⟩
  calc #P ≤ F * #(P.image (fun y : ℤ × ℕ => y.1 * (y.2 : ℤ))) := Finset.card_le_mul_card_image P F hfib
    _ ≤ F * (2 * (H * Dm) / q + 1) :=
        Nat.mul_le_mul_left _ ((Finset.card_le_card himg).trans (card_Icc_cast_eq_le _ ρ))

/-! ### The diagonal -/

/-- **The diagonal, on the congruence.** For integer frequencies `t ∈ J` with `0 < |t| ≤ H`, and `D₂ ⊆ [1, Dm]` prime
to `q`, if every `|t|d` (`t ∈ J`, `d ∈ D₂`) has at most `F` divisors, the diagonal sum of `norm_sum_B_le` at
`f = (·)` is at most `F(⌊2HDm/q⌋ + 1)(Σ_{t∈J}|c_t|²)(Σ_{d∈D₂}|β(d)|²)`. -/
theorem diag_le_wide (J : Finset ℤ) (c : ℤ → ℂ) (D₂ : Finset ℕ) (β : ℕ → ℂ) {H Dm F : ℕ}
    (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d) (hDm : ∀ d ∈ D₂, d ≤ Dm)
    (hJ : ∀ t ∈ J, t ≠ 0 ∧ t.natAbs ≤ H)
    (hF : ∀ t ∈ J, ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F) :
    ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
          ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0) ≤
      ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * ((∑ t ∈ J, ‖c t‖ ^ 2) * (∑ d ∈ D₂, ‖β d‖ ^ 2)) := by
  set g : ℤ → ℕ → ℝ := fun t d => ‖c t‖ ^ 2 * ‖β d‖ ^ 2 with hg
  have hg0 : ∀ t d, 0 ≤ g t d := fun t d => by rw [hg]; positivity
  -- each term is at most half the two squares
  have hterm : ∀ x ∈ J ×ˢ D₂, ∀ y ∈ J ×ˢ D₂,
      (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
        ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0) ≤
      (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g x.1 y.2 / 2
          else 0) +
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g y.1 x.2 / 2
          else 0) := by
    intro x _ y _
    by_cases h1 : ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
      have e : ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ = (‖c x.1‖ * ‖β y.2‖) * (‖c y.1‖ * ‖β x.2‖) := by
        rw [norm_mul, norm_mul]; ring
      rw [e, hg]
      nlinarith [sq_nonneg (‖c x.1‖ * ‖β y.2‖ - ‖c y.1‖ * ‖β x.2‖)]
    · simp only [ite_eq_right h1, add_zero, le_refl]
  -- the second half equals the first, by symmetry
  have hsym : ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g y.1 x.2 / 2
          else 0) =
      ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g x.1 y.2 / 2
          else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    exact if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl
  -- the fibres
  have hfib : ∀ t ∈ J, ∀ d' ∈ D₂, ∑ y ∈ J ×ˢ D₂,
      (if ((t : ZMod q)) * (y.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (d' : ZMod q)⁻¹ then g t d' else 0) ≤
        ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * g t d' := by
    intro t ht d' hd'
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hg0 t d')
    have hsub : (J ×ˢ D₂).filter
          (fun y : ℤ × ℕ => ((t : ZMod q)) * (y.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (d' : ZMod q)⁻¹) ⊆
        (J ×ˢ D₂).filter
          (fun y : ℤ × ℕ => ((y.1 * (y.2 : ℤ) : ℤ) : ZMod q) = ((t * (d' : ℤ) : ℤ) : ZMod q)) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨hy.1, ?_⟩
      have hu := hD₂ _ (Finset.mem_product.1 hy.1).2
      have hu' := hD₂ _ hd'
      push_cast
      calc (y.1 : ZMod q) * (y.2 : ZMod q)
          = ((y.1 : ZMod q) * (d' : ZMod q)⁻¹) * ((d' : ZMod q) * (y.2 : ZMod q)) := by
            rw [show (y.1 : ZMod q) * (d' : ZMod q)⁻¹ * ((d' : ZMod q) * (y.2 : ZMod q)) =
              (y.1 : ZMod q) * (y.2 : ZMod q) * ((d' : ZMod q)⁻¹ * (d' : ZMod q)) by ring,
              ZMod.inv_mul_of_unit _ hu', mul_one]
        _ = ((t : ZMod q) * (y.2 : ZMod q)⁻¹) * ((d' : ZMod q) * (y.2 : ZMod q)) := by rw [hy.2]
        _ = (t : ZMod q) * (d' : ZMod q) := by
            rw [show (t : ZMod q) * (y.2 : ZMod q)⁻¹ * ((d' : ZMod q) * (y.2 : ZMod q)) =
              (t : ZMod q) * (d' : ZMod q) * ((y.2 : ZMod q)⁻¹ * (y.2 : ZMod q)) by ring,
              ZMod.inv_mul_of_unit _ hu, mul_one]
    exact_mod_cast (Finset.card_le_card hsub).trans (card_fiber_cong_le J D₂ hD₂0 hDm hJ hF _)
  calc ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
          ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0)
      ≤ ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
          ((if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g x.1 y.2 / 2
              else 0) +
            (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g y.1 x.2 / 2
              else 0)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
    _ = ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
          (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then g x.1 y.2
            else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [hsym, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
    _ = ∑ t ∈ J, ∑ d' ∈ D₂, ∑ y ∈ J ×ˢ D₂,
          (if ((t : ZMod q)) * (y.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (d' : ZMod q)⁻¹ then g t d' else 0) :=
        sum_swap4 J D₂ (fun t d t' d' =>
          if ((t : ZMod q)) * (d : ZMod q)⁻¹ = ((t' : ZMod q)) * (d' : ZMod q)⁻¹ then g t d' else 0)
    _ ≤ ∑ t ∈ J, ∑ d' ∈ D₂, ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * g t d' :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun d' hd' => hfib t ht d' hd'
    _ = ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * ((∑ t ∈ J, ‖c t‖ ^ 2) * (∑ d ∈ D₂, ‖β d‖ ^ 2)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]

/-! ### The estimate -/

/-- **The bilinear Type I estimate without the condition `2HDm < q`.** Let `a` be a unit mod `q`, `D₁` and `D₂` sets
of naturals prime to `q`, `D₂ ⊆ [1, Dm]`, `2H < q`, every residue the inverse of at most `m` elements of `D₁`, every
`|t|d` with `0 < |t| ≤ H` and `d ∈ D₂` with at most `F` divisors, and `|ŵ(h)| ≤ W` at the other frequencies `h ≠ 0`.
Then `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k)|` is at most
`(Σ|α|²)^{1/2}(mF(⌊2HDm/q⌋ + 1)(Σ|β|²)·q⁻¹Σ_h|ŵ(h)|²)^{1/2} + W(Σ|α|)(Σ|β|) + |(Σα)(Σβ)E_w/φ(q)|`.

The proof: `sum_bilinear`; the frequencies `0 < |t| ≤ H` by `norm_sum_B_le` and `diag_le_wide`, the others by
`norm_Bh_le`. -/
theorem typeIB_bound_wide (a : ZMod q) (ha : IsUnit a) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ)
    (hD₁ : ∀ d ∈ D₁, IsUnit (d : ZMod q)) (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d)
    (S : Finset ℕ) (w : ℕ → ℂ) {H Dm F m : ℕ} {W : ℝ} (hW0 : 0 ≤ W)
    (hDm : ∀ d ∈ D₂, d ≤ Dm) (hq2 : 2 * H < q)
    (hm : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F)
    (hW : ∀ h : ZMod q, h ≠ 0 → h ∉ (Jset H).image (fun t : ℤ => (t : ZMod q)) → ‖what S w h‖ ≤ W) :
    ‖∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * ∑ k ∈ S, w k * SieveFamily.dw q a (d₁ * d₂ * k)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * (∑ d ∈ D₂, ‖β d‖ ^ 2) *
          ((q : ℝ)⁻¹ * ∑ h : ZMod q, ‖what S w h‖ ^ 2)) +
        W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) +
        ‖(∑ d ∈ D₁, α d) * (∑ d ∈ D₂, β d) * (Ew (q := q) S w / q.totient)‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set Fz := univ.filter (· ≠ (0 : ZMod q)) with hFz
  set I := (Jset H).image (fun t : ℤ => (t : ZMod q)) with hI
  set Y := ∑ h : ZMod q, ‖what S w h‖ ^ 2 with hY
  set Z := ∑ d ∈ D₂, ‖β d‖ ^ 2 with hZ
  set K : ℝ := ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  rw [sum_bilinear a D₁ D₂ α β hD₁ hD₂ S w]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  -- split the frequencies
  rw [← Finset.sum_filter_add_sum_filter_not Fz (· ∈ I), mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the small frequencies, as the integers of `Jset H`
    have hsub : Fz.filter (· ∈ I) = I := by
      ext h
      simp only [hFz, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hh => hh.2
      · intro hh
        refine ⟨?_, hh⟩
        rw [hI, Finset.mem_image] at hh
        obtain ⟨t, ht, rfl⟩ := hh
        exact cast_ne_zero hq2 ht
    rw [hsub, hI, Finset.sum_image (cast_injOn hq2)]
    have hB := norm_sum_B_le a ha D₁ D₂ α β (Jset H) (fun t : ℤ => (t : ZMod q))
      (fun t : ℤ => what S w (t : ZMod q)) hm
    have hD := diag_le_wide (q := q) (Jset H) (fun t : ℤ => what S w (t : ZMod q)) D₂ β hD₂ hD₂0 hDm
      (fun t ht => mem_Jset.1 ht) (fun t ht d hd => hF t (mem_Jset.1 ht).1 (mem_Jset.1 ht).2 d hd)
    have hJY : ∑ t ∈ Jset H, ‖what S w (t : ZMod q)‖ ^ 2 ≤ Y := by
      rw [hY, ← Finset.sum_image (f := fun h : ZMod q => ‖what S w h‖ ^ 2) (cast_injOn hq2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun h _ _ => by positivity
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun h _ => by positivity
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun d _ => by positivity
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (q : ℝ)⁻¹ * ‖∑ t ∈ Jset H, what S w (t : ZMod q) * Bh a D₁ D₂ α β (t : ZMod q)‖
        ≤ (q : ℝ)⁻¹ * (√(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * (q * (K * (Y * Z))))) := by
          refine mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
            (Real.sqrt_nonneg _))) (by positivity)
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD.trans ?_) hq0.le) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJY hZ0) hK0
      _ = √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * K * Z * ((q : ℝ)⁻¹ * Y)) := by
          rw [mul_left_comm]
          congr 1
          rw [show (m : ℝ) * (q * (K * (Y * Z))) = q ^ 2 * (m * K * Z * ((q : ℝ)⁻¹ * Y)) by
            field_simp]
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq0.le]
          field_simp
  · -- the other frequencies
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hcard : (#(Fz.filter (· ∉ I)) : ℝ) ≤ q := by
      have : #(Fz.filter (· ∉ I)) ≤ q := (Finset.card_le_univ _).trans (by rw [ZMod.card])
      exact_mod_cast this
    calc (q : ℝ)⁻¹ * ‖∑ h ∈ Fz.filter (· ∉ I), what S w h * Bh a D₁ D₂ α β h‖
        ≤ (q : ℝ)⁻¹ * ∑ h ∈ Fz.filter (· ∉ I), W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_))
            (by positivity)
          rw [Finset.mem_filter, hFz, Finset.mem_filter] at hh
          rw [norm_mul]
          exact mul_le_mul (hW h hh.1.2 hh.2) (norm_Bh_le a D₁ D₂ α β h) (norm_nonneg _) hW0
      _ ≤ W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
          have hX : 0 ≤ W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by positivity
          calc (q : ℝ)⁻¹ * #(Fz.filter (· ∉ I)) * (W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)))
              ≤ 1 * (W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖))) := by
                refine mul_le_mul_of_nonneg_right ?_ hX
                rw [inv_mul_le_iff₀ hq0, mul_one]; exact hcard
            _ = W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := one_mul _

end SieveTypeIB

namespace SieveSpline

open SieveTypeIB

variable {q : ℕ} [NeZero q]

/-- **The bilinear Type I estimate without `2HDm < q`, with a spline weight.** In `SieveTypeIB.typeIB_bound_wide`
take `S = (A, B + r(ℓ − 1)]` and `w` the spline (`ℓ ≥ 1`). Then `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_k w(k)dw(d₁d₂k)|` is at most
`(Σ|α|²)^{1/2}(mF(⌊2HDm/q⌋ + 1)(Σ|β|²)(⌊n/q⌋ + 1)n)^{1/2} + (B − A)(q/(2ℓ(H + 1)))^r(Σ|α|)(Σ|β|) +
|Σα||Σβ|d(q)/φ(q)`, with `n = B + r(ℓ − 1) − A`. -/
theorem typeIB_spline_wide (a : ZMod q) (ha : IsUnit a) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ)
    (hD₁ : ∀ d ∈ D₁, IsUnit (d : ZMod q)) (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d)
    (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hDm : ∀ d ∈ D₂, d ≤ Dm) (hq2 : 2 * H < q)
    (hm : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F) :
    ‖∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (d₁ * d₂ * k)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * (∑ d ∈ D₂, ‖β d‖ ^ 2) *
          ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ))) +
        ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) +
        ‖∑ d ∈ D₁, α d‖ * ‖∑ d ∈ D₂, β d‖ * (q.divisors.card / q.totient) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hb := typeIB_bound_wide a ha D₁ D₂ α β hD₁ hD₂ hD₂0 (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ))
    (H := H) (Dm := Dm) (F := F) (m := m) (W := ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r)
    (by positivity) hDm hq2 hm hF (fun h h0 hH => norm_what_spl_tail A B ℓ r H hℓ h h0 hH)
  refine hb.trans (add_le_add (add_le_add ?_ le_rfl) ?_)
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left (sum_norm_what_spl_le A B ℓ r hℓ) (by positivity)
  · rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (norm_Ew_spl_le A B ℓ r hℓ) hφ.le)
      (by positivity)

end SieveSpline

#print axioms SieveTypeIB.card_Icc_cast_eq_le
#print axioms SieveTypeIB.card_fiber_cong_le
#print axioms SieveTypeIB.diag_le_wide
#print axioms SieveTypeIB.typeIB_bound_wide
#print axioms SieveSpline.typeIB_spline_wide
