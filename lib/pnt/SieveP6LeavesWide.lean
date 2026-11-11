/-
# The large leaves of a family on the wider region

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveP6Leaves.leaves_chain` evaluates the large leaves of a tree, with Brun's weights for the sifted cofactor, by
the paper's Lemma 4.3 (`SieveTypeIBAsym.leaves_ib`), on the region `d₁ ≤ q^{L−1−a}`, `d₁d₂² ≤ q^{L−b}`. This file is
the same with Lemma 4.3 on the wider region (`SieveTypeIBAsymWide.leaves_ib_wide`), `d₁d₂² ≤ q^{L+c}`.

* `leaves_chain_wide`: `leaves_chain` with `leaves_ib_wide`.
* `leavesOK_wide`: `SieveP6TreeLeaves.LeavesOK q a′ L a (−c) δ' εw Λ₀ C₀ δ k J₀ K_max` for large `q`: the hypothesis on
  the leaves of `SieveP6ib.prop6ib_core` and of `SieveTwoP6.prop6_two_core`, on the wider region.

The proofs are `leaves_chain`'s and `leavesOK_of`'s; the two lemmas on the leaves have the same conclusion.

The file imports `SieveP6TreeLeaves.lean` and `SieveTypeIBAsymWide.lean`.
-/
import SieveP6TreeLeaves
import SieveTypeIBAsymWide

open Real Finset SieveFamily SieveTree SieveChain SieveBrun SieveTypeIBLeaf SieveTypeIBBrun SieveP6Leaves
  SieveP6TreeLeaves

namespace SieveP6LeavesWide

open Classical Filter in
/-- **The large leaves of a family, with Brun's weights, on the wider region.** `SieveP6Leaves.leaves_chain` with
`SieveTypeIBAsymWide.leaves_ib_wide` in place of `SieveTypeIBAsym.leaves_ib`: let `L > 2`, `a ≤ L − 2`, a margin
`κ > 0`, `0 ≤ δ' ≤ min(κ/4, 1/8)`, `−L ≤ c ≤ a − δ' − κ` and `a − δ' − κ ≥ 0`, with `Λ₀`, `εw`, `k` and `C₀` as there.
There are `δ > 0` and `q₀` such that for `q ≥ q₀`, `a` a unit, `w = ⌈q^{εw}⌉`, and two sets `Y₁`, `Y₂` of decreasing
tuples of primes in `[w, ⌊2q^L⌋]` with comparisons `Pr` and the sizes `∏y₁·w^{2k+4} ≤ q^{L−1−a}`,
`∏y₁·w^{2k+4}·(∏y₂)² ≤ q^{L+c}`, `q^{L−1−δ'} ≤ ∏y₁∏y₂`: the leaves `d = ∏y₁∏y₂` total at most
`ζ(k)(N₂ − N₁)/(φ(q) log w)·Σ 1/d + q^{L−δ}/φ(q)` in absolute value. -/
theorem leaves_chain_wide {L : ℝ} (hL : 2 < L) {a c δ' κ εw Λ₀ : ℝ} (hδ' : 0 ≤ δ') (haL : a ≤ L - 2)
    (hκ : 0 < κ) (hκ1 : c ≤ a - δ' - κ) (hκ3 : 0 ≤ a - δ' - κ) (hδ1 : δ' ≤ κ / 4) (hδ2 : δ' ≤ 1 / 8)
    (hcL : -L ≤ c) (hεw : 0 < εw) (hΛ₀ : 0 ≤ Λ₀) (K₁ K₂ J₀ : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hεwk : (2 * k + 4) * εw ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
    ∀ (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)),
      (∀ y ∈ Y₁, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
      (∀ y ∈ Y₂, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
    ∀ {M : ℕ}, M ≤ J₀ → ∀ (cc : Fin M → ℝ) (e₁ : Fin M → Fin K₁ → ℝ) (e₂ : Fin M → Fin K₂ → ℝ)
      (Pr : Fin M → (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → Prop),
      (∀ j y₁ y₂, (0 < cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) → Pr j y₁ y₂) ∧
        (Pr j y₁ y₂ → 0 ≤ cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) →
      (∀ j, ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
        cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ₀ * Real.log q) →
      (∀ j, (∃ i, e₁ j i = 1 ∨ e₁ j i = -1) ∨ ∃ i, e₂ j i = 1 ∨ e₂ j i = -1) →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
        ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L + c) ∧
        (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) →
      ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℂ) else 0) *
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
            (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
        SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
            (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
          ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) +
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  -- the constants
  have hk4 : (4 : ℝ) ≤ 2 * k + 4 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hεw1 : εw ≤ 1 / 64 := by
    have : 4 * εw ≤ (2 * k + 4) * εw := mul_le_mul_of_nonneg_right hk4 hεw.le
    linarith
  set B : ℝ := Real.log (L + 1) - Real.log εw + 1 with hBdef
  have hB : 1 ≤ B := by
    have : Real.log εw ≤ Real.log (L + 1) := Real.log_le_log hεw (by linarith)
    linarith
  obtain ⟨hs0, -, -, -⟩ := SieveTypeIBAsymWide.sIBW_spec hκ hεw J₀
  set s := SieveTypeIBAsymWide.sIBW κ εw J₀ with hsdef
  set c₁ : ℝ := s / 8 with hc₁def
  have hc₁0 : 0 < c₁ := by positivity
  obtain ⟨δ, hδ, q₀, H⟩ := SieveTypeIBAsymWide.leaves_ib_wide hL hδ' haL hκ hκ1 hκ3 hδ1 hδ2 hcL hεw hΛ₀ hB K₁ K₂ J₀
    hc₁0.le
    (by rw [hc₁def]; linarith)
  -- the divisor bound's exponent
  set D : ℝ := (L + 1) * K₁ + (2 * k + 4) with hDdef
  have hD0 : 0 < D := by have : (0 : ℝ) ≤ (L + 1) * K₁ := by positivity
                         linarith
  set ε' : ℝ := min 1 (c₁ / (2 * D)) with hε'def
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'D : ε' * D ≤ c₁ / 2 := by
    have h := min_le_right 1 (c₁ / (2 * D))
    rw [← hε'def] at h
    calc ε' * D ≤ c₁ / (2 * D) * D := mul_le_mul_of_nonneg_right h hD0.le
      _ = c₁ / 2 := by field_simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, LinnikPower.Cdiv ε' ≤ 3 ^ n :=
    (pow_unbounded_of_one_lt _ (by norm_num : (1 : ℝ) < 3)).imp fun _ h => h.le
  set m := ⌈C₀ / Real.log 2⌉₊ with hmdef
  -- the eventual conditions
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 2 ≤ x ^ (1 - εw) ∧
      (∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ (L + 1)), 1 / (p : ℝ) ≤ B) ∧
      (3 + 4 * Real.log x) ^ (2 * m + 2) ≤ x ^ c₁ ∧ 24 * 2 ^ (2 * k + 7) ≤ x ^ (1 / 8 : ℝ) ∧
      (3 + 4 * Real.log x) ^ (n + 1) ≤ x ^ (c₁ / 2) := by
    have h1 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - εw)).eventually_ge_atTop 2
    have h2 := SieveRough.evLe_sum_inv hεw (by linarith : εw ≤ L + 1) 1 one_pos
    have h3 := SieveTypeIIU.ev_log_pow_le (2 * m + 2) hc₁0
    have h4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop
      (24 * 2 ^ (2 * k + 7) : ℝ)
    have h5 := SieveTypeIIU.ev_log_pow_le (n + 1) (by positivity : (0 : ℝ) < c₁ / 2)
    filter_upwards [eventually_ge_atTop (3 : ℝ), h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5 hx6
    exact ⟨hx1, hx2, by rw [hBdef]; linarith, hx4, hx5, hx6⟩
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ, hδ, max q₀ q₁, ?_⟩
  intro q _ hq a' ha' Y₁ Y₂ hY₁ hY₂ M hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo
  obtain ⟨hx3, hx1w, hsumB, hVx, hWx, hFx⟩ := hq₁ q (le_trans (le_max_right _ _) hq)
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq
  set x : ℝ := (q : ℝ) with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hxe1 : 1 ≤ x ^ εw := Real.one_le_rpow hx1 hεw.le
  set w : ℕ := ⌈x ^ εw⌉₊ with hwdef
  have hw2 : 2 ≤ w := Nat.lt_ceil.2 (by exact_mod_cast Real.one_lt_rpow (by linarith) hεw)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hwle : (w : ℝ) ≤ x ^ εw + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hxx : x ^ εw + 1 ≤ x := by
    have e : x ^ (1 - εw) * x ^ εw = x := by rw [← Real.rpow_add hx0]; simp
    calc x ^ εw + 1 ≤ 2 * x ^ εw := by linarith
      _ ≤ x ^ (1 - εw) * x ^ εw := mul_le_mul_of_nonneg_right hx1w (by positivity)
      _ = x := e
  have hwx : (w : ℝ) ≤ x := le_trans hwle hxx
  have hw2x : (w : ℝ) ≤ 2 * x ^ εw := by linarith
  have hxw : x ^ εw ≤ w := Nat.le_ceil _
  set J : ℕ := SieveProp6.Jw w with hJdef
  obtain ⟨hJw, h2J, hJ3⟩ := SieveProp6.Jw_spec hw2
  set N₁ : ℕ := ⌊x ^ L⌋₊ with hN₁def
  set N₂ : ℕ := ⌊2 * x ^ L⌋₊ with hN₂def
  have hxL : 0 ≤ x ^ L := by positivity
  have hN : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hxL1 : x ^ (L + 1) = x * x ^ L := by rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
  have hxL0 : 0 < x ^ L := by positivity
  have hN₂x' : (N₂ : ℝ) < x ^ (L + 1) := by
    have h1 : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
    have h2 := mul_lt_mul_of_pos_right (by linarith : (2 : ℝ) < x) hxL0
    rw [hxL1]
    linarith
  have hN₂x : (N₂ : ℝ) ≤ x ^ (L + 1) := hN₂x'.le
  -- the entries
  have hent : ∀ {K : ℕ} (Y : Finset (Fin K → ℕ)),
      (∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime ∧ w ≤ y i ∧ y i ≤ N₂) →
      Y ⊆ Fintype.piFinset fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)) := by
    intro K Y hY y hy
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨hp, hwy, hyN⟩ := (hY y hy).2 i
    have h1 : x ^ εw ≤ (y i : ℝ) := le_trans hxw (by exact_mod_cast hwy)
    have h2 : (y i : ℝ) ≤ N₂ := by exact_mod_cast hyN
    exact SieveRough.mem_primesIn.2 ⟨hp, h1, lt_of_le_of_lt h2 hN₂x'⟩
  have hYp₁ : ∀ y ∈ Y₁, StrictAnti y ∧ ∀ i, (y i).Prime := fun y hy => ⟨(hY₁ y hy).1, fun i => ((hY₁ y hy).2 i).1⟩
  have hYp₂ : ∀ y ∈ Y₂, StrictAnti y ∧ ∀ i, (y i).Prime := fun y hy => ⟨(hY₂ y hy).1, fun i => ((hY₂ y hy).2 i).1⟩
  -- the weights
  have hT : ∀ j, ∀ p ∈ SieveLeaf.T (w : ℝ) J j, p.Prime := fun j p hp => SieveLeaf.prime_of_mem_T hp
  have hdisj := SieveLeaf.T_disjoint hw1 J
  have hkk : ∀ j : Fin J, Even (lev k J j) := fun j => by
    rcases hk with ⟨r, hr⟩
    exact ⟨r + j, by rw [lev]; omega⟩
  have hkk1 : ∀ j : Fin J, 1 ≤ lev k J j := fun j => by rw [lev]; omega
  set fmax : ℝ := (w : ℝ) ^ ((2 * k + 4 : ℕ) : ℝ) with hfmaxdef
  have hfmax1 : 1 ≤ fmax := Real.one_le_rpow hw1 (by positivity)
  have hfmaxx : fmax ≤ x ^ ((2 * k + 4 : ℕ) : ℝ) := Real.rpow_le_rpow (by positivity) hwx (by positivity)
  have hS₁ : ∀ σ ∈ wS₁ (SieveLeaf.T (w : ℝ) J) (lev k J),
      ∀ j, σ j ∈ Ftr (SieveLeaf.T (w : ℝ) J j) (lev k J j) ∨ σ j ∈ Fes (SieveLeaf.T (w : ℝ) J j) (lev k J j) :=
    fun σ hσ j => Or.inl (Fintype.mem_piFinset.1 hσ j)
  -- the weights' bounds
  have hYP : ∀ y ∈ Y₁, ((∏ i, y i : ℕ) : ℝ) ≤ x ^ ((L + 1) * K₁) := fun y hy => by
    push_cast
    calc ∏ i, (y i : ℝ) ≤ ∏ _i : Fin K₁, x ^ (L + 1) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ =>
            le_trans (by exact_mod_cast ((hY₁ y hy).2 i).2.2) hN₂x
      _ = x ^ ((L + 1) * K₁) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]
  have hPD : x ^ ((L + 1) * K₁) * x ^ ((2 * k + 4 : ℕ) : ℝ) ≤ x ^ D := by
    rw [← Real.rpow_add hx0, hDdef]
    push_cast
    exact le_refl _
  obtain ⟨hMf₁, hMf₂⟩ := fibres_le_rpow hx1 (by omega : 1 ≤ w) hwx hε'0 hε'1 hε'D hn hFx Y₁ hYp₁ hYP hPD
  have hW := W_le_rpow hx1 hεw hεwk hWx hw2 hw2x
  have hV := V_le_rpow (by omega : 1 ≤ w) hwx hC₀ hC k hVx
  -- the estimate
  have hmain := H q hq₀ a' ha' (fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)))
    (fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)))
    (fun _ p hp => (SieveRough.mem_primesIn.1 hp).2.1) (fun _ p hp => (SieveRough.mem_primesIn.1 hp).2.1)
    (fun _ => hsumB) (fun _ => hsumB) Y₁ Y₂ (hent Y₁ fun y hy => ⟨(hY₁ y hy).1, (hY₁ y hy).2⟩)
    (hent Y₂ fun y hy => ⟨(hY₂ y hy).1, (hY₂ y hy).2⟩)
    (fun d => le_trans (by exact_mod_cast card_fibre_le_one Y₂ hYp₂ d) (Real.one_le_rpow hx1 hc₁0.le))
    hM cc e₁ e₂ Pr hPr hΛ hpiv (Rs (SieveLeaf.T (w : ℝ) J)) (wS₁ (SieveLeaf.T (w : ℝ) J) (lev k J)) wf wl₁
    (wS₂ (SieveLeaf.T (w : ℝ) J) (lev k J)) wf₂ wl₂ (fun σ hσ => one_le_wf hT (sub_of_mem_wS₁ hσ))
    (fun z hz => one_le_wf hT (sub_of_mem_wS₂ hz)) (R_le _ _ hkk hkk1 hT hdisj) (le_R _ _ hkk hkk1 hT hdisj)
    fmax hfmax1 (fun σ hσ => wf_le hw1 (hS₁ σ hσ)) (fun z hz => wf_le hw1 (mem_wS₂_cases hz)) hMf₁ hMf₂ hW
    hV (fun y₁ hy₁ y₂ hy₂ hP => by
      rw [hfmaxdef, Real.rpow_natCast]
      exact hgeo y₁ hy₁ y₂ hy₂ hP)
  -- the leaf counts
  have hconv : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough w n then 1 else 0) =
        ((∑ m ∈ Finset.range (N₂ + 1), rng N₁ N₂ ((∏ i, y₁ i) * ∏ i, y₂ i) m * Rs (SieveLeaf.T (w : ℝ) J) m *
          dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m) : ℝ) : ℂ) := by
    intro y₁ hy₁ y₂ hy₂
    have hp₁ := fun i => ((hY₁ y₁ hy₁).2 i).1
    have hp₂ := fun i => ((hY₂ y₂ hy₂).2 i).1
    have h1 := one_le_prod hp₁
    have h2 := one_le_prod hp₂
    exact count_eq_rsum q a' N₁ N₂ (Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))) (by omega) hJw
      (rough_mul (rough_prod hp₁ fun i => ((hY₁ y₁ hy₁).2 i).2.1) (rough_prod hp₂ fun i => ((hY₂ y₂ hy₂).2 i).2.1))
  have hLHS : (∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℂ) else 0) *
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough w n then 1 else 0)) =
      ((∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) *
        ∑ m ∈ Finset.range (N₂ + 1), rng N₁ N₂ ((∏ i, y₁ i) * ∏ i, y₂ i) m * Rs (SieveLeaf.T (w : ℝ) J) m *
          dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y₂ hy₂ => ?_
    rw [hconv y₁ hy₁ y₂ hy₂, Complex.ofReal_mul, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hLHS, Complex.norm_real, Real.norm_eq_abs]
  refine hmain.trans ?_
  -- the main term
  have hgap := abs_gap_le hw2 hJw (NeZero.pos q) hC₀ hC hk hk1 hkC
  have hsum : 0 ≤ ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
      (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      div_nonneg (Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num) (Nat.cast_nonneg _)
  have hNN : (0 : ℝ) ≤ (N₂ : ℝ) - N₁ := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast hw2)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hmt := mul_le_mul_of_nonneg_left hgap (div_nonneg hNN hx0.le)
  have e : ((N₂ : ℝ) - N₁) / x * (SieveProp6.zeta C₀ k * (x / (q.totient * Real.log w))) =
      SieveProp6.zeta C₀ k * (((N₂ : ℝ) - N₁) / (q.totient * Real.log w)) := by
    field_simp
  rw [e] at hmt
  have := mul_le_mul_of_nonneg_right hmt hsum
  linarith

/-- **`LeavesOK` on the wider region**: `leaves_chain_wide` for every pair of block sizes up to `K_max`, as
`SieveP6TreeLeaves.LeavesOK` with `b = −c`, so that its second size reads `∏y₁·w^{2k+4}·(∏y₂)² ≤ q^{L+c}`. -/
theorem leavesOK_wide {L : ℝ} (hL : 2 < L) {a c δ' κ εw Λ₀ : ℝ} (hδ' : 0 ≤ δ') (haL : a ≤ L - 2)
    (hκ : 0 < κ) (hκ1 : c ≤ a - δ' - κ) (hκ3 : 0 ≤ a - δ' - κ) (hδ1 : δ' ≤ κ / 4) (hδ2 : δ' ≤ 1 / 8)
    (hcL : -L ≤ c) (hεw : 0 < εw) (hΛ₀ : 0 ≤ Λ₀) (Kmax J₀ : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hεwk : (2 * k + 4) * εw ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
      LeavesOK q a' L a (-c) δ' εw Λ₀ C₀ δ k J₀ Kmax := by
  have H := fun K₁ K₂ : ℕ =>
    leaves_chain_wide hL hδ' haL hκ hκ1 hκ3 hδ1 hδ2 hcL hεw hΛ₀ K₁ K₂ J₀ hC₀ hC hk hk1 hkC hεwk
  choose δf hδf q₀f hq₀f using H
  set P : Finset (ℕ × ℕ) := (range (Kmax + 1)) ×ˢ (range (Kmax + 1)) with hPdef
  have hP : P.Nonempty := ⟨(0, 0), by simp [hPdef]⟩
  refine ⟨P.inf' hP (fun p => δf p.1 p.2), (Finset.lt_inf'_iff hP).2 fun p _ => hδf p.1 p.2,
    P.sup (fun p => q₀f p.1 p.2), ?_⟩
  intro q _ hq a' ha' K₁ K₂ hK₁ hK₂ Y₁ Y₂ hY₁ hY₂ M hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo
  have hmem : (K₁, K₂) ∈ P :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hq' : q₀f K₁ K₂ ≤ q := le_trans (Finset.le_sup (f := fun p : ℕ × ℕ => q₀f p.1 p.2) hmem) hq
  have hgeo' : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
      ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
      ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L + c) ∧
      (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) := fun y₁ hy₁ y₂ hy₂ hall => by
    have h := hgeo y₁ hy₁ y₂ hy₂ hall
    rwa [sub_neg_eq_add] at h
  refine (hq₀f K₁ K₂ q hq' a' ha' Y₁ Y₂ hY₁ hY₂ hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo').trans ?_
  have hδle : P.inf' hP (fun p => δf p.1 p.2) ≤ δf K₁ K₂ := Finset.inf'_le (fun p : ℕ × ℕ => δf p.1 p.2) hmem
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
    (by positivity))

end SieveP6LeavesWide

#print axioms SieveP6LeavesWide.leaves_chain_wide
#print axioms SieveP6LeavesWide.leavesOK_wide
