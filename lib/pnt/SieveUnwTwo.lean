/-
# Type II families in two variables with sharp prime ranges

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The paper's Lemma 4.5 (`SieveTypeIIU.typeII_unw`) is its Lemma 4.4 without the dyadic weights: the primes run over
all the primes up to `⌊2q^L⌋` and `m` over an interval of the window's range. This file is the same for two
polynomial variables, from `SieveUnwGen.unw_gen` and `SieveFamilyTwo.box_two`.

* `typeII_unw_two`, **Lemma 4.5 in two variables**: assume Proposition 3′ in two variables at `L` on a region `R`
  (`SieveFamilyTwo.TypeIITwoAt L R`), `0 < L ≤ 5/2`, and fix `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₁ ≥ 0`. There are
  `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `m₁` run over `S₁ ⊆ (P₁, P₁′]` and `m₂` over
  `S₂ ⊆ (P₂, P₂′]`, with `P_i ≥ 1`, `P_i′ ≤ 2q^L` and `R` on the rectangle
  `[log_q P₁, log_q P₁′] × [log_q P₂, log_q P₂′]`, with coefficients `|a_m| ≤ A₀` and `|b_m| ≤ B₀`, and let
  `n + 1 ≤ K₀` primes `x_i` run over the primes up to `⌊2q^L⌋`. Let `J ≤ J₀` sharp comparisons `P_j` hold when
  `ℓ_j = φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i > 0` and imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`,
  `φ_j(m₁) + ψ_j(m₂) ≤ Λ₁ log q` and for each `j` a pivot `i` with `e_{ji} = ±1`. If wherever all the comparisons hold
  each `x_i ≥ 2q^{e₁}` and `m₁m₂∏_i x_i ≤ 2q^L`, then the family's `|A − B/φ(q)|` is at most `A₀B₀q^{L−δ}/φ(q)`.

The blocks are the pairs of dyadic blocks `(P₁2^{b₁}, 2P₁2^{b₁}] × (P₂2^{b₂}, 2P₂2^{b₂}]`, at most
`(3 + 4 log q)²` of them; the base of a block that is not empty has its exponents in the rectangle, so
`box_two` is the estimate on it.

The file imports `SieveUnwGen.lean` and `SieveFamilyTwo.lean`.
-/
import SieveUnwGen
import SieveFamilyTwo

open Real Finset Filter Asymptotics SieveFamily SieveFamilyGen SieveTypeIIU SieveUnwGen SieveFamilyTwo

namespace SieveUnwTwo

open Classical in
/-- **Type II for families in two variables with sharp prime ranges (Lemma 4.5 in two variables).** Assume
Proposition 3′ in two variables at `L` on `R` (`hII`) and `0 < L ≤ 5/2`. Fix `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and
`Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `m₁` run over
`S₁ ⊆ (P₁, P₁′]` and `m₂` over `S₂ ⊆ (P₂, P₂′]`, with `P_i ≥ 1`, `P_i′ ≤ 2q^L` and `R` on the rectangle
`[log_q P₁, log_q P₁′] × [log_q P₂, log_q P₂′]`, with coefficients `|a_m| ≤ A₀` and `|b_m| ≤ B₀`, and let `n + 1 ≤ K₀`
primes `x_i` run over the primes up to `⌊2q^L⌋`. Let `J ≤ J₀` sharp comparisons `P_j` hold when
`ℓ_j = φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i > 0` and imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`,
`φ_j(m₁) + ψ_j(m₂) ≤ Λ₁ log q` on `S₁ × S₂` and for each `j` a pivot `i` with `e_{ji} = ±1`. If wherever all the
comparisons hold each `x_i ≥ 2q^{e₁}` and `m₁m₂∏_i x_i ≤ 2q^L`, then the family's `|A − B/φ(q)|` is at most
`A₀B₀q^{L−δ}/φ(q)`. -/
theorem typeII_unw_two {L : ℝ} {R : ℝ → ℝ → Prop} (hII : TypeIITwoAt L R) (hL0 : 0 < L) (hL : L ≤ 5 / 2)
    (K₀ J₀ : ℕ) {e₁ E₀ Λ₁ : ℝ} (he₁ : 0 < e₁) (hE₀ : 0 ≤ E₀) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₁' P₂ P₂' : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ P₁' → S₂ ⊆ Finset.Ioc P₂ P₂' →
      1 ≤ P₁ → 1 ≤ P₂ → (P₁' : ℝ) ≤ 2 * (q : ℝ) ^ L → (P₂' : ℝ) ≤ 2 * (q : ℝ) ^ L →
      (∀ u v : ℝ, Real.logb q P₁ ≤ u → u ≤ Real.logb q P₁' → Real.logb q P₂ ≤ v → v ≤ Real.logb q P₂' → R u v) →
      ∀ (ac bc : ℕ → ℂ) {A₀ B₀ : ℝ}, (∀ m, ‖ac m‖ ≤ A₀) → (∀ m, ‖bc m‖ ≤ B₀) →
      ∀ (n : ℕ), n + 1 ≤ K₀ →
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ ψ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ℕ × ℕ → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m.1 + ψ j m.2 + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m.1 + ψ j m.2 + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ S₁ ×ˢ S₂, φ j m.1 + ψ j m.2 ≤ Λ₁ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      (∀ m ∈ S₁ ×ˢ S₂, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ j, Pr j m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ ((m.1 * m.2 : ℕ) : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      ‖Dsum q a ((S₁ ×ˢ S₂) ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe ⌊2 * (q : ℝ) ^ L⌋₊))
          (fun mx => (mx.1.1 * mx.1.2) * ∏ i, mx.2 i)
          (fun mx => ac mx.1.1 * bc mx.1.2 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (A₀ * B₀ * (q : ℝ) ^ (L - δ)) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := unw_gen (ι := ℕ × ℕ) (κ := ℕ × ℕ) K₀ J₀ 2 hL0 hL he₁ hE₀ hΛ₁
  obtain ⟨q₂, hq₂⟩ := box_two hII (f0 := SieveDyadic.bump) (SieveDyadic.contDiff_bump (n := ⊤))
    SieveDyadic.bump_support (K₀ + 1) he₁
  refine ⟨δ, hδ, max (max q₁ q₂) 2, ?_⟩
  intro q _ hq a ha P₁ P₁' P₂ P₂' S₁ S₂ hS₁ hS₂ hP₁ hP₂ hP₁' hP₂' hR ac bc A₀ B₀ hA hB n hn J hJ φ ψ e Pr he hP hφ
    piv hpiv hsupp
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hB0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB 0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
  have hqL0 : 0 < (q : ℝ) ^ L := Real.rpow_pos_of_pos hq0 _
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) hL0.le
  set Y : ℕ := ⌊2 * (q : ℝ) ^ L⌋₊ with hY
  have hY0 : Y ≠ 0 := by
    have : 1 ≤ Y := Nat.le_floor (by push_cast; linarith)
    omega
  have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  set M : ℕ := Nat.log 2 Y + 1 with hM
  have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ L) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlq0 : 0 ≤ Real.log q := by linarith
    refine le_of_mul_le_mul_right ?_ hlog2
    nlinarith [hL, hL0]
  have hMle : (M : ℝ) ≤ 3 + 4 * Real.log q := by rw [hM]; push_cast; linarith
  -- the dyadic blocks of each variable
  have hblkM : ∀ {P P' : ℕ} {S : Finset ℕ}, S ⊆ Finset.Ioc P P' → 1 ≤ P → (P' : ℝ) ≤ 2 * (q : ℝ) ^ L →
      ∀ m ∈ S, Nat.log 2 ((m - 1) / P) ∈ Finset.range M := by
    intro P P' S hS hP1 hP' m hm
    have hmI := Finset.mem_Ioc.1 (hS hm)
    obtain ⟨h1, -⟩ := blk_spec hP1 hmI.1
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have hP'Y : P' ≤ Y := Nat.le_floor hP'
    exact le_trans (Nat.le_mul_of_pos_left _ hP1) (le_trans h1.le (le_trans hmI.2 hP'Y))
  have hblkI : ∀ {P P' : ℕ} {S : Finset ℕ}, S ⊆ Finset.Ioc P P' → 1 ≤ P → ∀ b : ℕ,
      S.filter (fun m => Nat.log 2 ((m - 1) / P) = b) ⊆ Finset.Ioc (P * 2 ^ b) (2 * (P * 2 ^ b)) := by
    intro P P' S hS hP1 b m hm
    obtain ⟨hmS, hmb⟩ := Finset.mem_filter.1 hm
    obtain ⟨h1, h2⟩ := blk_spec hP1 (Finset.mem_Ioc.1 (hS hmS)).1
    rw [hmb] at h1 h2
    exact Finset.mem_Ioc.2 ⟨h1, h2⟩
  have hfilt : ∀ b₁ b₂ : ℕ, (S₁ ×ˢ S₂).filter
      (fun m => (Nat.log 2 ((m.1 - 1) / P₁), Nat.log 2 ((m.2 - 1) / P₂)) = (b₁, b₂)) =
      S₁.filter (fun m => Nat.log 2 ((m - 1) / P₁) = b₁) ×ˢ S₂.filter (fun m => Nat.log 2 ((m - 1) / P₂) = b₂) := by
    intro b₁ b₂
    ext m
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto
  have hpos : ∀ (P b : ℕ), 1 ≤ P → 0 < P * 2 ^ b := fun P b hP1 => Nat.mul_pos hP1 (by positivity)
  refine hq₁ q hq1 a ha (S₁ ×ˢ S₂) (fun m => m.1 * m.2) (fun m => ac m.1 * bc m.2) (A₀ * B₀) (mul_nonneg hA0 hB0)
    (fun m => (Nat.log 2 ((m.1 - 1) / P₁), Nat.log 2 ((m.2 - 1) / P₂))) (Finset.range M ×ˢ Finset.range M)
    (fun b => ((P₁ * 2 ^ b.1 : ℕ) : ℝ) * ((P₂ * 2 ^ b.2 : ℕ) : ℝ)) ?_ ?_ ?_ ?_ ?_ n hn hJ
    (fun j m => φ j m.1 + ψ j m.2) e Pr he hP hφ piv hpiv hsupp ?_
  · -- the labels
    intro m hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_product.1 hm
    exact Finset.mem_product.2 ⟨hblkM hS₁ hP₁ hP₁' m.1 hm₁, hblkM hS₂ hP₂ hP₂' m.2 hm₂⟩
  · -- their number
    rw [Finset.card_product, Finset.card_range]
    push_cast
    calc (M : ℝ) * M ≤ (3 + 4 * Real.log q) * (3 + 4 * Real.log q) :=
          mul_le_mul hMle hMle (Nat.cast_nonneg _) (by linarith)
      _ = (3 + 4 * Real.log q) ^ 2 := by ring
  · -- the sizes are positive
    intro b _
    have h1 : (0 : ℝ) < ((P₁ * 2 ^ b.1 : ℕ) : ℝ) := by exact_mod_cast hpos P₁ b.1 hP₁
    have h2 : (0 : ℝ) < ((P₂ * 2 ^ b.2 : ℕ) : ℝ) := by exact_mod_cast hpos P₂ b.2 hP₂
    exact mul_pos h1 h2
  · -- a pair is above the size of its block
    intro m hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_product.1 hm
    obtain ⟨h1, -⟩ := blk_spec hP₁ (Finset.mem_Ioc.1 (hS₁ hm₁)).1
    obtain ⟨h2, -⟩ := blk_spec hP₂ (Finset.mem_Ioc.1 (hS₂ hm₂)).1
    exact_mod_cast Nat.mul_lt_mul'' h1 h2
  · -- the coefficients of a block
    rintro ⟨b₁, b₂⟩ -
    rw [hfilt b₁ b₂]
    have h1 := sum_norm_le (hblkI hS₁ hP₁ b₁) hA
    have h2 := sum_norm_le (hblkI hS₂ hP₂ b₂) hB
    calc ∑ m ∈ S₁.filter (fun m => Nat.log 2 ((m - 1) / P₁) = b₁) ×ˢ
          S₂.filter (fun m => Nat.log 2 ((m - 1) / P₂) = b₂), ‖ac m.1 * bc m.2‖
        = (∑ m ∈ S₁.filter (fun m => Nat.log 2 ((m - 1) / P₁) = b₁), ‖ac m‖) *
            ∑ m ∈ S₂.filter (fun m => Nat.log 2 ((m - 1) / P₂) = b₂), ‖bc m‖ := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
          refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => norm_mul _ _
      _ ≤ (((P₁ * 2 ^ b₁ : ℕ) : ℝ) * A₀) * (((P₂ * 2 ^ b₂ : ℕ) : ℝ) * B₀) :=
          mul_le_mul h1 h2 (Finset.sum_nonneg fun m _ => norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hA0)
      _ = ((P₁ * 2 ^ b₁ : ℕ) : ℝ) * ((P₂ * 2 ^ b₂ : ℕ) : ℝ) * (A₀ * B₀) := by ring
  · -- the estimate on a block
    rintro ⟨b₁, b₂⟩ - Q hQ hQP c' hc' ξ κ' hh hhh
    rw [hfilt b₁ b₂]
    have hbound0 : (0 : ℝ) ≤ A₀ * B₀ * (q : ℝ) ^ (L - 1 / 50000) :=
      mul_nonneg (mul_nonneg hA0 hB0) (Real.rpow_nonneg hq0.le _)
    rcases (S₁.filter (fun m => Nat.log 2 ((m - 1) / P₁) = b₁)).eq_empty_or_nonempty with h₁ | ⟨m₁, hm₁⟩
    · rw [h₁, Finset.empty_product]
      simp only [Finset.sum_empty, norm_zero, zero_mul, Finset.sum_const_zero]
      exact hbound0
    rcases (S₂.filter (fun m => Nat.log 2 ((m - 1) / P₂) = b₂)).eq_empty_or_nonempty with h₂ | ⟨m₂, hm₂⟩
    · rw [h₂, Finset.product_empty]
      simp only [Finset.sum_empty, norm_zero, zero_mul, Finset.sum_const_zero]
      exact hbound0
    -- the base of the block is in the rectangle
    have hI₁ := hblkI hS₁ hP₁ b₁
    have hI₂ := hblkI hS₂ hP₂ b₂
    have hbase : ∀ {P P' b m : ℕ} {S : Finset ℕ}, S ⊆ Finset.Ioc P P' → 1 ≤ P →
        m ∈ S.filter (fun m => Nat.log 2 ((m - 1) / P) = b) →
        Real.logb q P ≤ Real.logb q ((P * 2 ^ b : ℕ) : ℝ) ∧ Real.logb q ((P * 2 ^ b : ℕ) : ℝ) ≤ Real.logb q P' := by
      intro P P' b m S hS hP1 hm
      have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
      have hPb0 : (0 : ℝ) < ((P * 2 ^ b : ℕ) : ℝ) := by exact_mod_cast hpos P b hP1
      have h1 : (P : ℝ) ≤ ((P * 2 ^ b : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right P (show 0 < 2 ^ b by positivity)
      have h2 : ((P * 2 ^ b : ℕ) : ℝ) ≤ P' := by
        have hlt := (Finset.mem_Ioc.1 (hblkI hS hP1 b hm)).1
        have hle := (Finset.mem_Ioc.1 (hS (Finset.mem_filter.1 hm).1)).2
        exact_mod_cast hlt.le.trans hle
      exact ⟨Real.logb_le_logb_of_le hq1' hP0 h1, Real.logb_le_logb_of_le hq1' hPb0 h2⟩
    obtain ⟨hu₁, hu₂⟩ := hbase hS₁ hP₁ hm₁
    obtain ⟨hv₁, hv₂⟩ := hbase hS₂ hP₂ hm₂
    have hRb := hR _ _ hu₁ hu₂ hv₁ hv₂
    rcases hc' with rfl | rfl
    · exact hq₂ q hq2 (P₁ * 2 ^ b₁) (P₂ * 2 ^ b₂) _ _ hI₁ hI₂ (hpos P₁ b₁ hP₁) (hpos P₂ b₂ hP₂) hRb ac bc hA hB n
        (by omega) Q hQ hQP φ ψ ξ κ' hh hhh
    · have h := hq₂ q hq2 (P₁ * 2 ^ b₁) (P₂ * 2 ^ b₂) _ _ hI₁ hI₂ (hpos P₁ b₁ hP₁) (hpos P₂ b₂ hP₂) hRb
        (fun m => ((‖ac m‖ : ℝ) : ℂ)) (fun m => ((‖bc m‖ : ℝ) : ℂ)) (A₀ := A₀) (B₀ := B₀)
        (fun m => by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hA m)
        (fun m => by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hB m) n (by omega) Q hQ hQP φ ψ ξ κ'
        hh hhh
      simpa only [norm_mul, Complex.ofReal_mul] using h

end SieveUnwTwo

#print axioms SieveUnwTwo.typeII_unw_two
