import ShortSieveTop

/-!
# The lower bound from Li's identity

Li's identity (`ShortSieveTop.top_identity`) with `z₁ = ⌈x^{ν(0)}⌉`, `z₂ = ⌊√x⌋ + 1` and the levels
`L_p = ⌈x^{ν(log p/log x)}⌉` (`lev`), `ν = liNu θ γ`, splits `S(I, √x)` into the root terms, whose asymptotic formulas
are `ShortSieveRoot.abs_S1_sub_le` and `abs_S2_liNu_sub_le`, and the third sum `Σ₃` (`sThree`).

* `primes_lower`: if `Σ₃(A) ≥ (y/x^{1−ρ}) Σ₃(B) − (L + ε) y/log x` for every `ε > 0` (what the certificate
  provides), then the primes of `(x − y, x]` number at least `(1 − L − ε) y/log x` for every `ε > 0`, large `x` and
  `y ∈ [x^θ, x^{1−ρ}]`. The primes of `A` are at least `S(A, √x)`; those of `B` are at most `S(B, √x)` and at
  least `(1 − ε) x^{1−ρ}/log x` (`ShortSieveLong.primeCounting_short`). The prime `p = x^{ν(0)}`, when it is one,
  is in Li's range but not in `sTwo`'s, and costs at most `y x^{−ν(0)} + 1`.
-/

open Finset Real Filter

namespace ShortSieveLower

open ShortSieveTop ShortSieveRoot ShortSieveLi

open Classical

/-- The level of Li's second sum at `p`: `⌈x^{ν(log p/log x)}⌉`. -/
noncomputable def lev (θ γ x : ℝ) (p : ℕ) : ℕ := ⌈x ^ liNu θ γ (Real.log p / Real.log x)⌉₊

/-- Li's third sum: `Σ_{x^{ν(0)} ≤ p ≤ √x} Σ_{L_p ≤ q < p} S(I_{pq}, q)`. -/
noncomputable def sThree (θ γ x y : ℝ) : ℕ :=
  ∑ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1),
    ∑ q ∈ SieveTree.primesIco (lev θ γ x p) p, sD (p * q) q x y

/-- `S(I_d, z) ≤ y/d + 1` for `d ≥ 1` and `y ≥ 0`. -/
theorem sD_le {d z : ℕ} (hd : 1 ≤ d) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    (sD d z x y : ℝ) ≤ y / d + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sD
  have hsub : {m ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z m ∧ x - y < ((d * m : ℕ) : ℝ) ∧ ((d * m : ℕ) : ℝ) ≤ x} ⊆
      Ioc ⌊(x - y) / d⌋₊ ⌊x / d⌋₊ := by
    intro m hm
    rw [mem_filter] at hm
    obtain ⟨-, -, hlo, hhi⟩ := hm
    push_cast at hlo hhi
    rw [mem_Ioc]
    constructor
    · have h1 : (x - y) / d < m := by rw [div_lt_iff₀ hd0]; linarith
      have h2 : (⌊(x - y) / d⌋₊ : ℝ) < m := lt_of_le_of_lt (Nat.floor_le (div_nonneg (by linarith) hd0.le)) h1
      exact_mod_cast h2
    · apply Nat.le_floor; rw [le_div_iff₀ hd0]; linarith
  calc (#({m ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z m ∧ x - y < ((d * m : ℕ) : ℝ) ∧ ((d * m : ℕ) : ℝ) ≤ x}) : ℝ) ≤
      (#(Ioc ⌊(x - y) / d⌋₊ ⌊x / d⌋₊) : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (⌊x / d⌋₊ : ℝ) - ⌊(x - y) / d⌋₊ := by
        rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hd0.le))]
    _ ≤ y / d + 1 := by
        have h1 : (⌊x / d⌋₊ : ℝ) ≤ x / d := Nat.floor_le (div_nonneg (by linarith) hd0.le)
        have h2 : (x - y) / d - 1 < ⌊(x - y) / d⌋₊ := by
          have := Nat.lt_floor_add_one ((x - y) / d); linarith
        have h3 : x / d - (x - y) / d = y / d := by ring
        linarith

/-- The primes of `(x − y, x]` are free of primes up to `√x` when `x − y ≥ √x`. -/
theorem card_primes_le_sD {x y : ℝ} (hxy : Real.sqrt x ≤ x - y) :
    ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card ≤ sD 1 (⌊Real.sqrt x⌋₊ + 1) x y := by
  unfold sD
  refine card_le_card fun n hn => ?_
  rw [mem_filter, mem_Ioc] at hn
  obtain ⟨⟨hlo, hhi⟩, hp⟩ := hn
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlo' : x - y < n := Nat.lt_of_floor_lt hlo
  have hx0 : 0 ≤ x := by
    by_contra h
    have := Nat.floor_eq_zero.2 (by linarith : x < 1)
    have := hp.two_le
    omega
  have hhi' : (n : ℝ) ≤ x := le_trans (Nat.cast_le.2 hhi) (Nat.floor_le hx0)
  rw [mem_filter, mem_Icc, one_mul]
  refine ⟨⟨hp.one_lt.le, hhi⟩, fun r hr hrp hrd => ?_, hlo', hhi'⟩
  -- a prime factor of the prime `n` is `n > √x`
  have hrn : r = n := (Nat.prime_dvd_prime_iff_eq hrp hp).1 hrd
  subst hrn
  have : (r : ℝ) ≤ Real.sqrt x := by
    have h1 : r ≤ ⌊Real.sqrt x⌋₊ := Nat.lt_succ_iff.1 hr
    exact le_trans (Nat.cast_le.2 h1) (Nat.floor_le hs0)
  linarith

/-- Li's range of primes and `sTwo`'s differ at most by the prime `⌈t⌉`, `t = x^a`. -/
theorem sum_Ioc_le_sum_Ico (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (t s : ℝ) :
    ∑ p ∈ (Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime, f p ≤ ∑ p ∈ SieveTree.primesIco ⌈t⌉₊ (⌊s⌋₊ + 1), f p ∧
      ∑ p ∈ SieveTree.primesIco ⌈t⌉₊ (⌊s⌋₊ + 1), f p ≤
        ∑ p ∈ (Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime, f p + f ⌈t⌉₊ := by
  have hsub : (Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime ⊆ SieveTree.primesIco ⌈t⌉₊ (⌊s⌋₊ + 1) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    rw [SieveTree.primesIco, mem_filter, mem_Ico]
    refine ⟨⟨?_, by omega⟩, hp.2⟩
    exact Nat.ceil_le.2 (Nat.lt_of_floor_lt hp.1.1).le
  refine ⟨sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf p, ?_⟩
  have hsub' : SieveTree.primesIco ⌈t⌉₊ (⌊s⌋₊ + 1) ⊆ insert ⌈t⌉₊ ((Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime) := by
    intro p hp
    rw [SieveTree.primesIco, mem_filter, mem_Ico] at hp
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases hpt : p = ⌈t⌉₊
    · exact Or.inl hpt
    · refine Or.inr ⟨⟨?_, by omega⟩, hp.2⟩
      have h1 : ⌈t⌉₊ < p := lt_of_le_of_ne hp.1.1 (Ne.symm hpt)
      exact lt_of_le_of_lt (Nat.floor_le_ceil t) h1
  calc ∑ p ∈ SieveTree.primesIco ⌈t⌉₊ (⌊s⌋₊ + 1), f p ≤
      ∑ p ∈ insert ⌈t⌉₊ ((Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime), f p :=
        sum_le_sum_of_subset_of_nonneg hsub' fun p _ _ => hf p
    _ ≤ ∑ p ∈ (Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime, f p + f ⌈t⌉₊ := by
        by_cases ha : ⌈t⌉₊ ∈ (Ioc ⌊t⌋₊ ⌊s⌋₊).filter Nat.Prime
        · rw [insert_eq_of_mem ha]; linarith [hf ⌈t⌉₊]
        · rw [sum_insert ha]; linarith

/-- `x^{log p/log x} = p` for `x > 1`, `p > 0`. -/
theorem rpow_log_div_log {x : ℝ} (hx : 1 < x) {p : ℝ} (hp : 0 < p) : x ^ (Real.log p / Real.log x) = p := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos hx0, mul_div_cancel₀ _ hlx.ne', Real.exp_log hp]

/-- `log x ≤ δ x^r` for large `x`. -/
theorem eventually_log_le {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop, Real.log x ≤ δ * x ^ r := by
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound hδ, eventually_gt_atTop 1] with x hx hx1
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1.le),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  exact hx

/-- **The lower bound from Li's identity.** With Li's Lemma 3.1 (`1/2 < θ < 1`, `2θ − 1 ≤ γ < 1/2`, `12ρ < 2θ − 1`),
Li's levels below the primes (`ν(α) ≤ α` on `[ν(0), 1/2]`), and a lower bound
`Σ₃(A) ≥ (y/x^{1−ρ}) Σ₃(B) − (L + ε) y/log x` for every `ε > 0`: for every `ε > 0`, large `x` and
`y ∈ [x^θ, x^{1−ρ}]`, the primes of `(x − y, x]` number at least `(1 − L − ε) y/log x`. -/
theorem primes_lower {θ γ ρ L : ℝ} (hLi : LiLemma31 θ γ ρ) (hθ : 1 / 2 < θ) (hθ1 : θ < 1)
    (hγ : 2 * θ - 1 ≤ γ) (hγ2 : γ < 1 / 2) (hρ : 0 < ρ) (hρθ : 12 * ρ < 2 * θ - 1)
    (hν : ∀ α ∈ Set.Icc (liNu θ γ 0) (1 / 2), liNu θ γ α ≤ α)
    (h3 : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      y / x ^ (1 - ρ) * sThree θ γ x (x ^ (1 - ρ)) - (L + ε) * y / Real.log x ≤ sThree θ γ x y) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      (1 - L - ε) * y / Real.log x ≤ ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  set a₀ := liNu θ γ 0 with ha₀
  have ha₀lo : 2 * θ - 1 ≤ a₀ := ShortSieveTypeI.le_liNu hθ hγ (by norm_num)
  have ha₀hi : a₀ ≤ γ := min_le_right _ _
  have ha₀0 : 0 < a₀ := by linarith
  obtain ⟨C₁, hC₁⟩ := abs_S1_sub_le hLi (by linarith) hρ ha₀0 (by linarith) (by linarith) le_rfl
  obtain ⟨C₂, hC₂⟩ := abs_S2_liNu_sub_le hLi hθ hθ1.le hγ hγ2 hρ hρθ ha₀0 (by linarith)
  intro ε hε
  set ε₁ := min 1 (ε / (4 * (|C₁| + |C₂| + 1))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min one_pos (by positivity)
  have hε₁C : ε₁ * (|C₁| + |C₂|) ≤ ε / 4 := by
    have h1 : ε₁ ≤ ε / (4 * (|C₁| + |C₂| + 1)) := min_le_right _ _
    have h2 : 0 ≤ |C₁| + |C₂| := by positivity
    calc ε₁ * (|C₁| + |C₂|) ≤ ε / (4 * (|C₁| + |C₂| + 1)) * (|C₁| + |C₂| + 1) :=
          mul_le_mul h1 (by linarith) h2 (by positivity)
      _ = ε / 4 := by field_simp
  have hρ12 : ρ < 1 / 12 := by linarith
  filter_upwards [hC₁ ε₁ hε₁0 (min_le_left _ _), hC₂ ε₁ hε₁0 (min_le_left _ _), h3 (ε / 4) (by linarith),
    ShortSieveLong.primeCounting_short hρ hρ12 (ε := ε / 4) (by linarith), eventually_gt_atTop 1,
    eventually_log_le (r := a₀) (δ := ε / 8) ha₀0 (by linarith),
    eventually_log_le (r := θ) (δ := ε / 8) (by linarith) (by linarith),
    (tendsto_rpow_atTop hρ).eventually_ge_atTop 2]
    with x hS1 hS2 hS3 hπB hx1 hla hlθ hxρ2 y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hy₁0 : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx0 _
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy1
  have hc : 0 ≤ y / x ^ (1 - ρ) := div_nonneg hy0.le hy₁0.le
  have hcy : y / x ^ (1 - ρ) * x ^ (1 - ρ) = y := div_mul_cancel₀ _ hy₁0.ne'
  -- `x − x^{1−ρ} ≥ √x ≥ 1`
  have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hB : Real.sqrt x ≤ x - x ^ (1 - ρ) := by
    rw [hsq]
    have h1 : x ^ (1 - ρ) * 2 ≤ x := by
      calc x ^ (1 - ρ) * 2 ≤ x ^ (1 - ρ) * x ^ ρ := mul_le_mul_of_nonneg_left hxρ2 hy₁0.le
        _ = x := by rw [← Real.rpow_add hx0, show (1 - ρ + ρ : ℝ) = 1 by ring, Real.rpow_one]
    have h2 : x ^ (1 / 2 : ℝ) ≤ x ^ (1 - ρ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  have hsx1 : 1 ≤ Real.sqrt x := by rw [hsq]; exact Real.one_le_rpow hx1.le (by norm_num)
  have hA1 : 1 ≤ x - y := by linarith
  -- the levels are at most the primes
  have hlev : ∀ p ∈ SieveTree.primesIco ⌈x ^ a₀⌉₊ (⌊Real.sqrt x⌋₊ + 1), lev θ γ x p ≤ p := by
    intro p hp
    rw [SieveTree.primesIco, mem_filter, mem_Ico] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have h1 : x ^ a₀ ≤ p := Nat.ceil_le.1 hp.1.1
    have h2 : (p : ℝ) ≤ Real.sqrt x :=
      le_trans (Nat.cast_le.2 (Nat.lt_succ_iff.1 hp.1.2)) (Nat.floor_le (Real.sqrt_nonneg x))
    have hα : Real.log p / Real.log x ∈ Set.Icc a₀ (1 / 2) := by
      constructor
      · rw [le_div_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) h1
      · rw [div_le_iff₀ hlx, ← Real.log_rpow hx0, ← hsq]; exact Real.log_le_log hp0 h2
    unfold lev
    apply Nat.ceil_le.2
    calc x ^ liNu θ γ (Real.log p / Real.log x) ≤ x ^ (Real.log p / Real.log x) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (hν _ hα)
      _ = p := rpow_log_div_log hx1 hp0
  -- Li's identity in `A` and in `B`
  have hidA := top_identity (Nat.ceil_le.2 (by
      calc x ^ a₀ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = Real.sqrt x := hsq.symm
        _ ≤ ((⌊Real.sqrt x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact le_of_lt (Nat.lt_floor_add_one _)))
    (lev θ γ x) hlev x y
  have hidB := top_identity (Nat.ceil_le.2 (by
      calc x ^ a₀ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = Real.sqrt x := hsq.symm
        _ ≤ ((⌊Real.sqrt x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact le_of_lt (Nat.lt_floor_add_one _)))
    (lev θ γ x) hlev x (x ^ (1 - ρ))
  have hidA' : (sD 1 (⌊Real.sqrt x⌋₊ + 1) x y : ℝ) = sOne a₀ x y -
      ∑ p ∈ SieveTree.primesIco ⌈x ^ a₀⌉₊ (⌊Real.sqrt x⌋₊ + 1), (sD p (lev θ γ x p) x y : ℝ) +
        sThree θ γ x y := by
    rw [sOne_eq]
    have := congrArg (Int.cast : ℤ → ℝ) hidA
    push_cast at this
    rw [this]
    unfold sThree
    push_cast
    ring
  have hidB' : (sD 1 (⌊Real.sqrt x⌋₊ + 1) x (x ^ (1 - ρ)) : ℝ) = sOne a₀ x (x ^ (1 - ρ)) -
      ∑ p ∈ SieveTree.primesIco ⌈x ^ a₀⌉₊ (⌊Real.sqrt x⌋₊ + 1), (sD p (lev θ γ x p) x (x ^ (1 - ρ)) : ℝ) +
        sThree θ γ x (x ^ (1 - ρ)) := by
    rw [sOne_eq]
    have := congrArg (Int.cast : ℤ → ℝ) hidB
    push_cast at this
    rw [this]
    unfold sThree
    push_cast
    ring
  -- the second sums against `sTwo`
  have hT2 : ∀ y' : ℝ, ShortSieveRoot.sTwo (liNu θ γ) a₀ (1 / 2) x y' =
      ∑ p ∈ (Ioc ⌊x ^ a₀⌋₊ ⌊Real.sqrt x⌋₊).filter Nat.Prime, (sD p (lev θ γ x p) x y' : ℝ) := fun y' => by
    rw [sTwo_eq, hsq]
    rfl
  have hbA := sum_Ioc_le_sum_Ico (fun p => (sD p (lev θ γ x p) x y : ℝ)) (fun _ => Nat.cast_nonneg _)
    (x ^ a₀) (Real.sqrt x)
  have hbB := sum_Ioc_le_sum_Ico (fun p => (sD p (lev θ γ x p) x (x ^ (1 - ρ)) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (x ^ a₀) (Real.sqrt x)
  rw [← hT2] at hbA hbB
  -- the boundary prime
  have hxa : (1 : ℝ) ≤ x ^ a₀ := Real.one_le_rpow hx1.le ha₀0.le
  have hbd : (sD ⌈x ^ a₀⌉₊ (lev θ γ x ⌈x ^ a₀⌉₊) x y : ℝ) ≤ ε / 4 * y / Real.log x := by
    have h1 := sD_le (d := ⌈x ^ a₀⌉₊) (z := lev θ γ x ⌈x ^ a₀⌉₊) (Nat.one_le_iff_ne_zero.2 (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)) hy0.le (by
        calc y ≤ x ^ (1 - ρ) := hy2
          _ ≤ x := by
            calc x ^ (1 - ρ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
              _ = x := Real.rpow_one x)
    refine le_trans h1 ?_
    have hceil : x ^ a₀ ≤ (⌈x ^ a₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : y / (⌈x ^ a₀⌉₊ : ℝ) ≤ ε / 8 * y / Real.log x := by
      rw [div_le_div_iff₀ (by linarith) hlx]
      have h4 : Real.log x * y ≤ ε / 8 * x ^ a₀ * y := mul_le_mul_of_nonneg_right hla hy0.le
      have h5 : ε / 8 * y * x ^ a₀ ≤ ε / 8 * y * (⌈x ^ a₀⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by positivity)
      linarith
    have h3 : (1 : ℝ) ≤ ε / 8 * y / Real.log x := by
      rw [le_div_iff₀ hlx]
      have := mul_le_mul_of_nonneg_left hy1 (by linarith : (0 : ℝ) ≤ ε / 8)
      linarith
    have e : ε / 4 * y / Real.log x = 2 * (ε / 8 * y / Real.log x) := by ring
    rw [e]
    linarith
  -- assemble
  have hπA := card_primes_ge_sD hA1
  have hπB' := card_primes_le_sD hB
  have hS1' := abs_le.1 (hS1 y hy1 hy2)
  have hS2' := abs_le.1 (hS2 y hy1 hy2)
  have hS3' := hS3 y hy1 hy2
  have hπBlo := hπB.1
  rw [← ShortSieveLong.card_primes_Ioc (Nat.floor_le_floor (by linarith))] at hπBlo
  have hC₁ : ε₁ * C₁ ≤ ε₁ * |C₁| := mul_le_mul_of_nonneg_left (le_abs_self _) hε₁0.le
  have hC₂ : ε₁ * C₂ ≤ ε₁ * |C₂| := mul_le_mul_of_nonneg_left (le_abs_self _) hε₁0.le
  have hcB : y / x ^ (1 - ρ) * ((Ioc ⌊x - x ^ (1 - ρ)⌋₊ ⌊x⌋₊).filter Nat.Prime).card ≤
      y / x ^ (1 - ρ) * sD 1 (⌊Real.sqrt x⌋₊ + 1) x (x ^ (1 - ρ)) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hπB') hc
  have hcπ : (1 - ε / 4) * y / Real.log x ≤
      y / x ^ (1 - ρ) * ((Ioc ⌊x - x ^ (1 - ρ)⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
    have := mul_le_mul_of_nonneg_left hπBlo hc
    calc (1 - ε / 4) * y / Real.log x = y / x ^ (1 - ρ) * ((1 - ε / 4) * x ^ (1 - ρ) / Real.log x) := by
          field_simp
      _ ≤ _ := this
  have hcT2 : y / x ^ (1 - ρ) * ShortSieveRoot.sTwo (liNu θ γ) a₀ (1 / 2) x (x ^ (1 - ρ)) ≤
      y / x ^ (1 - ρ) * ∑ p ∈ SieveTree.primesIco ⌈x ^ a₀⌉₊ (⌊Real.sqrt x⌋₊ + 1),
        (sD p (lev θ γ x p) x (x ^ (1 - ρ)) : ℝ) := mul_le_mul_of_nonneg_left hbB.1 hc
  have hπA' : (sD 1 (⌊Real.sqrt x⌋₊ + 1) x y : ℝ) ≤ ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
    exact_mod_cast hπA
  -- everything in units of `u = y/log x`
  obtain ⟨u, hu⟩ : ∃ u, u = y / Real.log x := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hεsum : ε₁ * C₁ * u + ε₁ * C₂ * u ≤ ε / 4 * u := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hu0
  rw [hidA'] at hπA'
  rw [hidB', mul_add, mul_sub] at hcB
  have hS1lo := hS1'.1
  have hS2hi := hS2'.2
  simp only [mul_div_assoc, ← hu] at hS1lo hS2hi hS3' hbd hcπ ⊢
  have hfin : (1 - L - ε) * u = (1 - ε / 4) * u - ε / 4 * u - (L + ε / 4) * u - ε / 4 * u := by ring
  rw [hfin]
  linarith only [hπA', hbA.2, hbd, hS1lo, hS2hi, hS3', hcT2, hcB, hcπ, hεsum]

end ShortSieveLower

#print axioms ShortSieveLower.primes_lower
