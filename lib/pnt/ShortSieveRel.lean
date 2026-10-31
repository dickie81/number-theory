import ShortSieveTerm

/-!
# Tuples of primes cut out by log-linear conditions, from a relative estimate on boxes

Li's Lemmas 3.1, 3.2 and 4.1 give asymptotic formulas `S(A) = (y/y₁)(1 + o(1))S(B)` for sums over products of primes
in dyadic boxes. This module turns such a relative estimate on boxes into the asymptotic formula for a cut of
tuples of primes, as `ShortSieveTerm.abs_card_cut_sub_le` does with the Type II estimate.

* `abs_sum_sub_le_boxes_rel`: the box sandwich with a relative error `ε c Σ_{full J} f_B` on each box that meets the
  set: the error is `ε c Σ_S f_B` plus `(1 + ε) c` times the straddling boxes' bounds.
* `card_tuples_le_psi`, `card_tuples_B_le`: the tuples of primes in `(x^c, x²)` with product in
  `(x − x^{1−ρ}, x]` number at most `C x^{1−ρ}/log x` (each product, free of primes up to `x^c`, has at most
  `⌊1/c⌋^d` such tuples, and `ShortSieveLong.psi_le_rpow` counts the products).
* `abs_card_cut_sub_le_rel`: from a relative estimate on every box (ratio `2^{1/d}`) that holds a tuple of the cut
  with product in `(x/4, 2x]`, the cut's tuples with product in `(x − y, x]` number `(y/x^{1−ρ})(1 + O(ε))` times
  those in `(x − x^{1−ρ}, x]`, up to `C y/log² x`.
-/

open Finset Real Filter

namespace ShortSieveRel

open ShortSieveBoxes ShortSieveTerm

open Classical

/-! ### The box sandwich with relative errors -/

/-- **The box sandwich with relative errors.** As `ShortSieveBoxes.abs_sum_sub_le_boxes`, with the estimate on a box
that meets `S` relative: `|Σ_{full J} f_A − c Σ_{full J} f_B| ≤ ε c Σ_{full J} f_B`. A box inside `S` contributes its
error, a straddling one at most `(1 + ε) c t_J`. -/
theorem abs_sum_sub_le_boxes_rel {α κ : Type*} (S : Finset α) (Js : Finset κ) (box : α → κ)
    (hbox : ∀ g ∈ S, box g ∈ Js) (full : κ → Finset α) (hfull : ∀ g ∈ S, g ∈ full (box g))
    {fA fB : α → ℝ} (hA : ∀ g, 0 ≤ fA g) (hB : ∀ g, 0 ≤ fB g) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hE : ∀ J ∈ Js, (∃ g ∈ S, box g = J) →
      |∑ g ∈ full J, fA g - c * ∑ g ∈ full J, fB g| ≤ ε * c * ∑ g ∈ full J, fB g)
    (t : κ → ℝ) (ht0 : ∀ J ∈ Js, 0 ≤ t J)
    (ht : ∀ J ∈ Js, (∃ g ∈ S, box g = J) → (∃ g ∈ full J, ¬ (g ∈ S ∧ box g = J)) →
      ∑ g ∈ full J, fB g ≤ t J) :
    |∑ g ∈ S, fA g - c * ∑ g ∈ S, fB g| ≤ ε * c * ∑ g ∈ S, fB g + (1 + ε) * c * ∑ J ∈ Js, t J := by
  set T : κ → Finset α := fun J => S.filter (box · = J) with hT
  have hTsub : ∀ J, T J ⊆ full J := fun J g hg => by
    obtain ⟨hgS, rfl⟩ := mem_filter.1 hg
    exact hfull g hgS
  have hsplit : ∀ f : α → ℝ, ∑ g ∈ S, f g = ∑ J ∈ Js, ∑ g ∈ T J, f g := fun f =>
    (sum_fiberwise_of_maps_to hbox f).symm
  have hεc : 0 ≤ ε * c := mul_nonneg hε hc
  -- the bound for one class
  have hone : ∀ J ∈ Js, |∑ g ∈ T J, fA g - c * ∑ g ∈ T J, fB g| ≤
      ε * c * ∑ g ∈ T J, fB g + (1 + ε) * c * t J := by
    intro J hJ
    have hB0 : 0 ≤ ∑ g ∈ T J, fB g := sum_nonneg fun g _ => hB g
    have hct : 0 ≤ (1 + ε) * c * t J := mul_nonneg (mul_nonneg (by linarith) hc) (ht0 J hJ)
    have hεB : 0 ≤ ε * c * ∑ g ∈ T J, fB g := mul_nonneg hεc hB0
    by_cases hmeet : ∃ g ∈ S, box g = J
    · by_cases hstr : ∃ g ∈ full J, ¬ (g ∈ S ∧ box g = J)
      · have hEJ := abs_le.1 (hE J hJ hmeet)
        have htJ := ht J hJ hmeet hstr
        have hAT : ∑ g ∈ T J, fA g ≤ ∑ g ∈ full J, fA g := sum_le_sum_of_subset_of_nonneg (hTsub J)
          fun g _ _ => hA g
        have hBT : ∑ g ∈ T J, fB g ≤ ∑ g ∈ full J, fB g := sum_le_sum_of_subset_of_nonneg (hTsub J)
          fun g _ _ => hB g
        have hA0 : 0 ≤ ∑ g ∈ T J, fA g := sum_nonneg fun g _ => hA g
        have hcB : c * ∑ g ∈ T J, fB g ≤ c * ∑ g ∈ full J, fB g := mul_le_mul_of_nonneg_left hBT hc
        have hcB' : c * ∑ g ∈ full J, fB g ≤ c * t J := mul_le_mul_of_nonneg_left htJ hc
        have hεB' : ε * (c * ∑ g ∈ full J, fB g) ≤ ε * (c * t J) := mul_le_mul_of_nonneg_left hcB' hε
        rw [abs_le]
        constructor <;> nlinarith [mul_nonneg hc hB0]
      · push Not at hstr
        have heq : T J = full J := by
          refine Subset.antisymm (hTsub J) fun g hg => ?_
          obtain ⟨hgS, hgJ⟩ := hstr g hg
          exact mem_filter.2 ⟨hgS, hgJ⟩
        rw [heq]
        rw [heq] at hεB
        exact (hE J hJ hmeet).trans (le_add_of_nonneg_right hct)
    · have h0 : T J = ∅ := by
        refine filter_eq_empty_iff.2 fun g hg hgJ => hmeet ⟨g, hg, hgJ⟩
      rw [h0]
      simpa using hct
  rw [hsplit fA, hsplit fB, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum hone).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-! ### Tuples of primes with product in the comparison interval -/

/-- A number up to `x` all of whose prime factors are at least `x^c` has at most `1/c` of them. -/
theorem card_primeFactors_le {n : ℕ} {x c : ℝ} (hx : 1 < x) (hc : 0 < c) (hn0 : n ≠ 0) (hn : (n : ℝ) ≤ x)
    (hpf : ∀ p ∈ n.primeFactors, x ^ c ≤ p) : (#n.primeFactors : ℝ) ≤ 1 / c := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hpow : (x ^ c) ^ #n.primeFactors ≤ ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => (Real.rpow_pos_of_pos hx0 c).le) fun p hp => hpf p hp
  have hprod : ∏ p ∈ n.primeFactors, (p : ℝ) ≤ n := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
  have h := (hpow.trans hprod).trans hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h
  have h' : c * #n.primeFactors * Real.log x ≤ 1 * Real.log x := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) h
    rw [Real.log_rpow hx0] at this
    linarith
  rw [le_div_iff₀ hc]
  nlinarith [le_of_mul_le_mul_right h' hlx]

/-- **Tuples of primes by their products.** The tuples of primes in `(x^c, x²)` with product in `(x − y₁, x]`
number at most `⌊1/c⌋^d Ψ(x, y₁; ⌈x^c⌉)`: the product is free of primes below `⌈x^c⌉`, and its tuples take their
coordinates among its at most `1/c` prime factors. -/
theorem card_tuples_le_psi (ι : Type*) [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : 0 < c) {x y₁ : ℝ} (hx : 1 < x)
    (hy₁ : y₁ ≤ x) :
    #((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
      fun g => x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) ≤
      ⌊1 / c⌋₊ ^ Fintype.card ι * ShortSieveLong.Psi x y₁ ⌈x ^ c⌉₊ := by
  classical
  have hx0 : 0 < x := by linarith
  refine card_le_mul_card_image_of_maps_to (f := fun g : ι → ℕ => ∏ j, g j) ?_ _ ?_
  · -- the product is a rough number of the interval
    intro g hg
    obtain ⟨hgQ, h1, h2⟩ := mem_filter.1 hg
    have hgj : ∀ j, ⌊x ^ c⌋₊ < g j ∧ (g j).Prime := fun j => by
      obtain ⟨hI, hp⟩ := mem_filter.1 (Fintype.mem_piFinset.1 hgQ j)
      exact ⟨(mem_Ioo.1 hI).1, hp⟩
    refine mem_filter.2 ⟨mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 h1, Nat.le_floor h2⟩, fun p hp => ?_⟩
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hpd
    rw [(Nat.prime_dvd_prime_iff_eq hpp (hgj j).2).1 hj]
    exact le_trans (Nat.ceil_le_floor_add_one _) (hgj j).1
  · -- a product has at most `⌊1/c⌋^d` tuples
    intro n hn
    obtain ⟨hnI, hnr⟩ := mem_filter.1 hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hnI
    have hn0 : n ≠ 0 := by omega
    have hpfc : #n.primeFactors ≤ ⌊1 / c⌋₊ := by
      refine Nat.le_floor (card_primeFactors_le hx hc hn0 ?_ fun p hp => ?_)
      · exact le_trans (by exact_mod_cast hn2) (Nat.floor_le hx0.le)
      · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnr p hp)
    calc #((((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
          fun g => x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x)).filter fun g => ∏ j, g j = n)
        ≤ #(Fintype.piFinset fun _ : ι => n.primeFactors) := by
          refine card_le_card fun g hg => ?_
          obtain ⟨hg', hgn⟩ := mem_filter.1 hg
          refine Fintype.mem_piFinset.2 fun j => Nat.mem_primeFactors.2 ⟨?_, ?_, hn0⟩
          · exact (mem_filter.1 (Fintype.mem_piFinset.1 (mem_filter.1 hg').1 j)).2
          · rw [← hgn]; exact dvd_prod_of_mem _ (mem_univ j)
      _ = #n.primeFactors ^ Fintype.card ι := by rw [Fintype.card_piFinset, prod_const, card_univ]
      _ ≤ ⌊1 / c⌋₊ ^ Fintype.card ι := Nat.pow_le_pow_left hpfc _

/-- **The tuples of primes with product in the comparison interval number `O(x^{1−ρ}/log x)`**, for `0 < c < 1`
and `12ρ < c` (`ShortSieveLong.psi_le_rpow` at the level `⌈x^c⌉`). -/
theorem card_tuples_B_le (ι : Type*) [Fintype ι] [DecidableEq ι] {c ρ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ)
    (hρc : 12 * ρ < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop,
      (#((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
        fun g => x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) : ℝ) ≤
        C * x ^ (1 - ρ) / Real.log x := by
  have hρU : ρ * (1 / c) < 1 / 12 := by rw [mul_one_div, div_lt_iff₀ hc]; linarith
  obtain ⟨z₀, hz₀⟩ := ShortSieveLong.psi_le_rpow (U := 1 / c) hρ hρU (ε := 1) one_pos
  refine ⟨(⌊1 / c⌋₊ ^ Fintype.card ι : ℕ) * 2 / c, by positivity, ?_⟩
  have ev1 : ∀ᶠ x : ℝ in atTop, (z₀ : ℝ) ≤ x ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop _
  have ev2 : ∀ᶠ x : ℝ in atTop, x ^ c + 1 ≤ x := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - c)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h, eventually_ge_atTop (2 : ℝ)] with x hx hx2
    have hx0 : 0 < x := by linarith
    have e : x ^ c = x ^ (-(1 - c)) * x := by
      rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
    rw [e]
    nlinarith
  filter_upwards [ev1, ev2, eventually_gt_atTop (1 : ℝ)] with x hx1 hx2 hx
  have hx0 : 0 < x := by linarith
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  set z := ⌈x ^ c⌉₊ with hz
  have hzc : x ^ c ≤ z := Nat.le_ceil _
  have hz1 : (z : ℝ) ≤ x := le_trans (Nat.ceil_lt_add_one hxc.le).le hx2
  have hzz₀ : z₀ ≤ z := by exact_mod_cast hx1.trans hzc
  have hlz : c * Real.log x ≤ Real.log z := by
    rw [← Real.log_rpow hx0]; exact Real.log_le_log hxc hzc
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlz0 : 0 < Real.log z := lt_of_lt_of_le (mul_pos hc hlx) hlz
  have hlog : Real.log x ≤ 1 / c * Real.log z := by
    rw [one_div_mul_eq_div, le_div_iff₀ hc]; linarith
  have hpsi := hz₀ z hzz₀ x hz1 hlog
  have hω := SieveRough.omegaC_le_one (Real.log x / Real.log z)
  have hy₁ : x ^ (1 - ρ) ≤ x := by
    calc x ^ (1 - ρ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      _ = x := Real.rpow_one x
  have hcard := card_tuples_le_psi ι hc hx hy₁
  have hy0 : 0 ≤ x ^ (1 - ρ) := Real.rpow_nonneg hx0.le _
  calc (#((Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
        fun g => x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) : ℝ)
      ≤ (⌊1 / c⌋₊ ^ Fintype.card ι : ℕ) * (ShortSieveLong.Psi x (x ^ (1 - ρ)) z : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (⌊1 / c⌋₊ ^ Fintype.card ι : ℕ) * ((SieveCert.omegaC (Real.log x / Real.log z) + 1) * x ^ (1 - ρ) /
        Real.log z) := mul_le_mul_of_nonneg_left hpsi (by positivity)
    _ ≤ (⌊1 / c⌋₊ ^ Fintype.card ι : ℕ) * (2 * x ^ (1 - ρ) / (c * Real.log x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (SieveCert.omegaC (Real.log x / Real.log z) + 1) * x ^ (1 - ρ) / Real.log z
            ≤ 2 * x ^ (1 - ρ) / Real.log z := by
              gcongr; linarith
          _ ≤ 2 * x ^ (1 - ρ) / (c * Real.log x) := by
              gcongr
    _ = (⌊1 / c⌋₊ ^ Fintype.card ι : ℕ) * 2 / c * x ^ (1 - ρ) / Real.log x := by
        field_simp


/-! ### The cut from a relative estimate on boxes -/

theorem two_mul_div_mul_eq (a c d L : ℝ) {b : ℝ} (hb : b ≠ 0) :
    2 * (a / b) * (L * (c * b / d)) = 2 * L * c * a / d := by
  field_simp

section cut

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Tuples of primes cut out by log-linear conditions, from a relative estimate on boxes.** Let `0 < c ≤ 1`,
`ρ > 0` with `12ρ < c`, a coordinate `v`, and conditions each with `e_u ≠ e_v` for some `u ≠ v`.
Suppose that for every `ε > 0`, for large `x` and `x^θ ≤ y ≤ x^{1−ρ}`, every box `(N_j, M_j]` with `N_j ≥ x^{c/2}`
and `M_j ≤ 2^{1/d} N_j` that holds a tuple of the cut with product in `(x/4, 2x]` has its tuples with product in
`(x − y, x]` within `ε` of `(y/x^{1−ρ})` times those in `(x − x^{1−ρ}, x]`, relatively. Then there is `C` such that
for every `ε ∈ (0, 1]`, for large `x` and `x^θ ≤ y ≤ x^{1−ρ}`, the cut's tuples with product in `(x − y, x]`
number `(y/x^{1−ρ})` times those in `(x − x^{1−ρ}, x]`, up to `ε` relatively and `C y/log² x`.

The boxes are those of `ShortSieveTerm.abs_card_cut_sub_le`, with the relative sandwich
(`abs_sum_sub_le_boxes_rel`) in place of the absolute one. -/
theorem abs_card_cut_sub_le_rel (v : ι) {c θ ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c)
    (atoms : List (LAtom ι)) (hatoms : ∀ A ∈ atoms, ∃ u, u ≠ v ∧ A.e u ≠ A.e v)
    (hbox : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ N M : ι → ℕ,
      (∀ j, x ^ (c / 2) ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ j, (M j : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / Fintype.card ι) * N j) →
      (∃ g ∈ cut c atoms x, x / 4 < ∏ j, (g j : ℝ) ∧ ∏ j, (g j : ℝ) ≤ 2 * x ∧
        g ∈ ShortSieveTypeII.tuples N M) →
      |(#{g ∈ ShortSieveTypeII.tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ ShortSieveTypeII.tuples N M | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) * #{g ∈ ShortSieveTypeII.tuples N M | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(#{g ∈ cut c atoms x | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ cut c atoms x | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) * #{g ∈ cut c atoms x | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x} + C * y / Real.log x ^ 2 := by
  classical
  set d : ℕ := Fintype.card ι with hd_def
  have hd : 0 < d := Fintype.card_pos_iff.2 ⟨v⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the grid's ratio `r = 2^{1/(2d)}`, with `(r²)^d = 2`
  set r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (2 * d)) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have hr2 : r ≤ 2 := by
    calc r ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          rw [div_le_one (by positivity)]; linarith)
      _ = 2 := Real.rpow_one 2
  have hrd : (r ^ 2) ^ d = 2 := by
    rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  have hr0 : 0 < r := by linarith
  have hr21 : 1 ≤ r ^ 2 := one_le_pow₀ hr1.le
  have hlr : 0 < Real.log r := Real.log_pos hr1
  -- powers of `r²` over at most `d = #ι` coordinates
  have hpowd : ∀ s : Finset ι, (r ^ 2) ^ s.card ≤ 2 := fun s => by
    rw [← hrd]; exact pow_le_pow_right₀ hr21 (card_le_univ s)
  -- the boundaries of the conditions
  set D : LAtom ι → ℝ := fun A => (∑ j, |A.e j|) * (2 * Real.log r) with hDdef
  have hD0 : ∀ A, 0 ≤ D A := fun A => mul_nonneg (sum_nonneg fun j _ => abs_nonneg _) (by positivity)
  obtain ⟨Cn, xn, hCn, hnear⟩ := near_uniform v hc hc1 hρ hρc D hD0 atoms hatoms
  -- the boxes' ratio `r² = 2^{1/d}`
  have hr2d : r ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / d) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    field_simp
  refine ⟨2 * atoms.length * Cn, fun ε hε hε1 => ?_⟩
  -- the conditions on `x`
  have ev4 : ∀ᶠ x : ℝ in atTop, 2 / (r - 1) ≤ x ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop _
  have ev5 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (c / 2) := (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev7 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ ρ := (tendsto_rpow_atTop hρ).eventually_ge_atTop _
  filter_upwards [hbox ε hε, eventually_ge_atTop xn, eventually_ge_atTop (3 : ℝ), ev4, ev5, ev7] with x hboxx hxn hx3
    hx4 hx5 hx7
  intro y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 θ) hy1
  set y₁ : ℝ := x ^ (1 - ρ) with hy₁
  have hy₁0 : 0 < y₁ := Real.rpow_pos_of_pos hx0 _
  have hy₁x : y₁ ≤ x / 2 := by
    have e : y₁ = x / x ^ ρ := by rw [hy₁, Real.rpow_sub hx0, Real.rpow_one]
    rw [e]; exact div_le_div_of_nonneg_left hx0.le (by norm_num) hx7
  have hxc0 : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  have hxc_half : x ^ c = x ^ (c / 2) * x ^ (c / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  have ha : 2 ≤ x ^ c * (r - 1) := by
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)).1 hx4; linarith
  -- the grid
  set I : ℕ := ⌈2 * Real.log x / Real.log r⌉₊ with hI
  set G := grid (x ^ c) r I with hG
  have hbot : ⌊x ^ c⌋₊ ∈ G := mem_grid.2 ⟨0, Nat.zero_le _, by simp⟩
  have hGge : ∀ e ∈ G, ⌊x ^ c⌋₊ ≤ e := fun e he => by
    obtain ⟨i, -, rfl⟩ := mem_grid.1 he
    exact Nat.floor_le_floor (le_mul_of_one_le_right hxc0.le (one_le_pow₀ hr1.le))
  have htop : x ^ (2 : ℝ) ≤ x ^ c * r ^ I := by
    have hrI : x ^ (2 : ℝ) ≤ r ^ I := by
      rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 _), ← Real.exp_log (pow_pos hr0 I), Real.log_rpow hx0,
        Real.log_pow]
      refine Real.exp_le_exp.2 ?_
      have h := Nat.le_ceil (2 * Real.log x / Real.log r)
      rw [← hI, div_le_iff₀ hlr] at h
      linarith
    calc x ^ (2 : ℝ) ≤ r ^ I := hrI
      _ ≤ x ^ c * r ^ I := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hx1 hc.le)
  have htopG : ⌊x ^ c * r ^ I⌋₊ ∈ G := mem_grid.2 ⟨I, le_rfl, rfl⟩
  -- the floor of `x^c` is at least `x^{c/2}`
  have hfloor : x ^ (c / 2) ≤ (⌊x ^ c⌋₊ : ℝ) := by
    have h1 : x ^ c - 1 < ⌊x ^ c⌋₊ := Nat.sub_one_lt_floor _
    nlinarith
  -- the cut's tuples lie in the boxes of their indices
  set S := cut c atoms x with hS
  have hSmem : ∀ g ∈ S, ∀ j, ⌊x ^ c⌋₊ < g j ∧ (g j : ℝ) < x ^ (2 : ℝ) ∧ (g j).Prime := by
    intro g hg j
    have h := (Fintype.mem_piFinset.1 (mem_filter.1 hg).1) j
    obtain ⟨hIoo, hp⟩ := mem_filter.1 h
    obtain ⟨h1, h2⟩ := mem_Ioo.1 hIoo
    exact ⟨h1, Nat.lt_ceil.1 h2, hp⟩
  set Js := Fintype.piFinset fun _ : ι => G with hJs
  set box : (ι → ℕ) → (ι → ℕ) := fun g j => idxG G (g j) with hbox
  have hlo : ∀ g ∈ S, ∀ j, ∃ e ∈ G, e < g j := fun g hg j => ⟨_, hbot, (hSmem g hg j).1⟩
  have hhi : ∀ g ∈ S, ∀ j, ∃ e ∈ G, g j ≤ e := fun g hg j => by
    refine ⟨_, htopG, Nat.le_floor ?_⟩
    exact ((hSmem g hg j).2.1.le).trans htop
  have hboxJs : ∀ g ∈ S, box g ∈ Js := fun g hg =>
    Fintype.mem_piFinset.2 fun j => (idxG_mem (hlo g hg j)).1
  have hfull : ∀ g ∈ S, g ∈ full G (box g) := fun g hg =>
    mem_tuples_idxG (fun j => (hSmem g hg j).2.2) (hlo g hg) (hhi g hg)
  -- the weights
  set fA : (ι → ℕ) → ℝ := fun g =>
    if x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x then 1 else 0 with hfA
  set fB : (ι → ℕ) → ℝ := fun g =>
    if x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x then 1 else 0 with hfB
  have hfA0 : ∀ g, 0 ≤ fA g := fun g => by simp only [hfA]; split_ifs <;> norm_num
  have hfB0 : ∀ g, 0 ≤ fB g := fun g => by simp only [hfB]; split_ifs <;> norm_num
  have hprodcast : ∀ g : ι → ℕ, ((∏ j, g j : ℕ) : ℝ) = ∏ j, (g j : ℝ) := fun g => by push_cast; rfl
  -- coordinates of tuples in the boxes of an index of the grid
  have hJG : ∀ J ∈ Js, ∀ j, J j ∈ G := fun J hJ j => (Fintype.mem_piFinset.1 hJ) j
  have hgt : ∀ J ∈ Js, ∀ g ∈ full G J, ∀ j, x ^ c < g j := by
    intro J hJ g hg j
    have h1 := (mem_full.1 hg j).1
    have h2 := hGge _ (hJG J hJ j)
    have h3 : x ^ c < (⌊x ^ c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊x ^ c⌋₊ : ℝ) + 1 ≤ g j := by exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt h2 h1)
    linarith
  -- the products of two tuples of the same boxes are within factor `2`
  have hprod2 : ∀ J ∈ Js, ∀ g ∈ full G J, ∀ g' ∈ full G J, ∏ j, (g j : ℝ) ≤ 2 * ∏ j, (g' j : ℝ) := by
    intro J hJ g hg g' hg'
    calc ∏ j, (g j : ℝ) ≤ ∏ j, (r ^ 2 * g' j) :=
          prod_le_prod₀ (fun j _ => by positivity) fun j _ => le_of_mem_full hr1 hr2 ha (hJG J hJ) hg hg' j
      _ = (r ^ 2) ^ d * ∏ j, (g' j : ℝ) := by rw [prod_mul_distrib, prod_const, card_univ]
      _ = 2 * ∏ j, (g' j : ℝ) := by rw [hrd]
  -- the relative estimate on a box tuple that meets the cut
  have hE : ∀ J ∈ Js, (∃ g ∈ S, box g = J) →
      |∑ g ∈ full G J, fA g - y / y₁ * ∑ g ∈ full G J, fB g| ≤ ε * (y / y₁) * ∑ g ∈ full G J, fB g := by
    rintro J hJ ⟨g₀, hg₀S, hg₀J⟩
    have hg₀ : g₀ ∈ full G J := hg₀J ▸ hfull g₀ hg₀S
    simp only [hfA, hfB, sum_boole]
    by_cases hBn : ∃ g₁ ∈ full G J, x - y₁ < ((∏ j, g₁ j : ℕ) : ℝ) ∧ ((∏ j, g₁ j : ℕ) : ℝ) ≤ x
    · obtain ⟨g₁, hg₁, hB1, hB2⟩ := hBn
      rw [hprodcast] at hB1 hB2
      have hP1 := hprod2 J hJ g₀ hg₀ g₁ hg₁
      have hP2 := hprod2 J hJ g₁ hg₁ g₀ hg₀
      have hboxne : ∀ j, ∃ e' ∈ G, J j < e' := fun j =>
        exists_above_of_lt (mem_full.1 hg₀ j).1 (mem_full.1 hg₀ j).2.1
      have hnext : ∀ j, (nextG G (J j) : ℝ) ≤ r ^ 2 * J j := fun j =>
        nextG_grid_le hr1 hr2 ha (hJG J hJ j) (hboxne j)
      refine hboxx y hy1 hy2 J (fun j => nextG G (J j)) (fun j => ?_) (fun j => ?_) (fun j => ?_)
        ⟨g₀, hg₀S, by linarith, by linarith, hg₀⟩
      · exact hfloor.trans (by exact_mod_cast hGge _ (hJG J hJ j))
      · exact (nextG_spec (hboxne j)).2.1.le
      · rw [← hr2d]; exact hnext j
    · push Not at hBn
      have hA0 : ∀ g ∈ full G J, ¬ (x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) := by
        rintro g hg ⟨h1, h2⟩
        exact absurd h2 (not_le.2 (hBn g hg (by linarith)))
      have hB0 : ∀ g ∈ full G J, ¬ (x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) := by
        rintro g hg ⟨h1, h2⟩
        exact absurd h2 (not_le.2 (hBn g hg h1))
      rw [filter_false_of_mem hA0, filter_false_of_mem hB0]
      simp
  -- a coordinate is at most the product
  have hcoord : ∀ g : ι → ℕ, (∀ j, 0 < g j) → ∀ j, (g j : ℝ) ≤ ((∏ j, g j : ℕ) : ℝ) := fun g hg j => by
    exact_mod_cast Nat.le_of_dvd (prod_pos fun j _ => hg j) (dvd_prod_of_mem _ (mem_univ j))
  have hr2le : r ^ 2 ≤ 2 := by
    calc r ^ 2 ≤ (r ^ 2) ^ d := le_self_pow₀ hr21 hd.ne'
      _ = 2 := hrd
  -- a box tuple that straddles the cut has its tuples in the comparison interval near a boundary
  have hstrad : ∀ J ∈ Js, (∃ g ∈ S, box g = J) → (∃ g ∈ full G J, ¬ (g ∈ S ∧ box g = J)) →
      ∑ g ∈ full G J, fB g ≤ ∑ A ∈ atoms.toFinset, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) := by
    rintro J hJ ⟨g₀, hg₀S, hg₀J⟩ ⟨g', hg', hg'n⟩
    have hg₀ : g₀ ∈ full G J := hg₀J ▸ hfull g₀ hg₀S
    have hg'J : box g' = J := idx_eq_of_mem_full (hJG J hJ) hg'
    have hg'S : g' ∉ S := fun h => hg'n ⟨h, hg'J⟩
    have hpos : ∀ g ∈ full G J, ∀ j, 0 < g j := fun g hg j => (mem_full.1 hg j).2.2.pos
    simp only [hfB, sum_boole]
    by_cases hbase : ∀ j, (g' j : ℝ) < x ^ (2 : ℝ)
    · -- some condition fails at `g'`
      have hnot : ¬ ∀ A ∈ atoms, A.Holds x g' := by
        intro hall
        refine hg'S (mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j =>
          mem_filter.2 ⟨mem_Ioo.2 ⟨?_, ?_⟩, (mem_full.1 hg' j).2.2⟩, hall⟩)
        · exact lt_of_le_of_lt (hGge _ (hJG J hJ j)) (mem_full.1 hg' j).1
        · exact Nat.lt_ceil.2 (hbase j)
      push Not at hnot
      obtain ⟨A, hA, hA'⟩ := hnot
      have hA₀ : A.Holds x g₀ := (mem_filter.1 hg₀S).2 A hA
      refine le_trans ?_ (single_le_sum (f := fun A => (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ))
        (fun A _ => Nat.cast_nonneg _) (List.mem_toFinset.2 hA))
      refine Nat.cast_le.2 (card_le_card fun g hg => ?_)
      obtain ⟨hgf, hB1, hB2⟩ := mem_filter.1 hg
      refine mem_filter.2 ⟨hgf, mem_filter.2 ⟨?_,
        abs_val_sub_le hr1 hr2 ha (hJG J hJ) hg₀ hg' hgf A hA₀ hA', hB1, hB2⟩⟩
      refine Fintype.mem_piFinset.2 fun j =>
        SieveRough.mem_primesIn.2 ⟨(mem_full.1 hgf j).2.2, (hgt J hJ g hgf j).le, ?_⟩
      have hx2 : x < x ^ (2 : ℝ) := by
        rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 (by linarith)
      exact lt_of_le_of_lt ((hcoord g (hpos g hgf) j).trans hB2) hx2
    · -- a coordinate of `g'` reaches `x²`: no tuple of these boxes has product at most `x`
      push Not at hbase
      obtain ⟨j₀, hj₀⟩ := hbase
      have hempty : (full G J).filter
          (fun g => x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) = ∅ := by
        refine filter_eq_empty_iff.2 fun g hg hgB => ?_
        have h2 := hgB.2
        have h1 := le_of_mem_full hr1 hr2 ha (hJG J hJ) hg' hg j₀
        have h3 := hcoord g (hpos g hg) j₀
        rw [Real.rpow_two, sq] at hj₀
        have h5 : x * x ≤ 2 * x := by
          calc x * x ≤ g' j₀ := hj₀
            _ ≤ r ^ 2 * g j₀ := h1
            _ ≤ 2 * g j₀ := mul_le_mul_of_nonneg_right hr2le (by positivity)
            _ ≤ 2 * x := by linarith
        have h6 : x ≤ 2 := le_of_mul_le_mul_right h5 hx0
        linarith
      rw [hempty, card_empty, Nat.cast_zero]
      exact sum_nonneg fun A _ => Nat.cast_nonneg _
  -- the boxes are disjoint
  have hfib : ∀ N : Finset (ι → ℕ), ∑ J ∈ Js, (((full G J).filter (· ∈ N)).card : ℝ) ≤ N.card := by
    intro N
    have h1 : ∀ J ∈ Js, (full G J).filter (· ∈ N) ⊆ N.filter (fun g => box g = J) := fun J hJ g hg => by
      obtain ⟨hgf, hgN⟩ := mem_filter.1 hg
      exact mem_filter.2 ⟨hgN, idx_eq_of_mem_full (hJG J hJ) hgf⟩
    calc ∑ J ∈ Js, (((full G J).filter (· ∈ N)).card : ℝ) ≤
          ∑ J ∈ Js, ((N.filter (fun g => box g = J)).card : ℝ) :=
          sum_le_sum fun J hJ => by exact_mod_cast card_le_card (h1 J hJ)
      _ = ((N.filter fun g => box g ∈ Js).card : ℝ) := by
          exact_mod_cast sum_card_fiberwise_eq_card_filter N Js box
      _ ≤ N.card := by exact_mod_cast card_filter_le _ _
  -- the straddling box tuples
  set t : (ι → ℕ) → ℝ := fun J =>
    ∑ A ∈ atoms.toFinset, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) with ht
  have ht0 : ∀ J ∈ Js, 0 ≤ t J := fun J _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hT : ∑ J ∈ Js, t J ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) := by
    calc ∑ J ∈ Js, t J
        = ∑ A ∈ atoms.toFinset, ∑ J ∈ Js, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) := sum_comm
      _ ≤ ∑ A ∈ atoms.toFinset, ((near c ρ (D A) A x).card : ℝ) := sum_le_sum fun A _ => hfib _
      _ ≤ ∑ _A ∈ atoms.toFinset, Cn * y₁ / Real.log x ^ 2 :=
          sum_le_sum fun A hA => hnear A (List.mem_toFinset.1 hA) x hxn
      _ = atoms.toFinset.card * (Cn * y₁ / Real.log x ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le atoms) (by positivity)
  -- the box sandwich
  have hsand := abs_sum_sub_le_boxes_rel S Js box hboxJs (full G) hfull hfA0 hfB0 (div_nonneg hy0.le hy₁0.le)
    hε.le hE t ht0 hstrad
  have hgA : (#{g ∈ S | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) = ∑ g ∈ S, fA g := by
    simp only [hfA, sum_boole]
  have hgB : (#{g ∈ S | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) = ∑ g ∈ S, fB g := by
    simp only [hfB, sum_boole]
  rw [hgA, hgB]
  have hlx : 0 < Real.log x ^ 2 := by
    have : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hT0 : 0 ≤ ∑ J ∈ Js, t J := sum_nonneg ht0
  have hc0 : 0 ≤ y / y₁ := div_nonneg hy0.le hy₁0.le
  have h1e : 1 + ε ≤ 2 := by linarith
  have h2a : (1 + ε) * (y / y₁) * ∑ J ∈ Js, t J ≤ 2 * (y / y₁) * ∑ J ∈ Js, t J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1e hc0) hT0
  have h2b : 2 * (y / y₁) * ∑ J ∈ Js, t J ≤ 2 * (y / y₁) * (atoms.length * (Cn * y₁ / Real.log x ^ 2)) :=
    mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num) hc0)
  rw [two_mul_div_mul_eq y Cn (Real.log x ^ 2) (atoms.length : ℝ) hy₁0.ne'] at h2b
  exact hsand.trans (add_le_add le_rfl (h2a.trans h2b))
end cut

end ShortSieveRel

#print axioms ShortSieveRel.abs_sum_sub_le_boxes_rel
#print axioms ShortSieveRel.card_tuples_le_psi
#print axioms ShortSieveRel.card_tuples_B_le
#print axioms ShortSieveRel.abs_card_cut_sub_le_rel
