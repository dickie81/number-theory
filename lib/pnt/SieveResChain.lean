/-
# The resonant window for a family and for the chains of primes times a rough cofactor

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveUnwGen.unw_gen_lo` evaluates a family with sharp prime ranges given the Type II estimate at each frequency
(`hbox`), on the scales of the primes' dyadic pieces that can have a term. For a polynomial over the integers, cut
into blocks `(P_b, 2P_b]`, with coefficients of modulus at most `1`, a frequency's twisted sum over a block is a
polynomial `dp` of the block with coefficients of modulus at most `1`, and the resonant window's estimate
(`SieveTypeIIHM.typeII_res`) bounds it wherever `ResCond` holds at the block's exponent and the scales'.

* `box_res`: the hypothesis `hbox` of `unw_gen_lo` with `A₀ = 1`, for the smooth weight `SieveDyadic.bump`, given
  `ResCond` at each block and each family of scales `Q_i ≥ q^{lo i}` with `∏Q_i ≤ 2^{K₀+1}q^L/P_b`.
* `typeII_gcmp_res`: `SieveChain.typeII_gcmp` by the resonant window: a family `Σ_m Σ_x 1[comparisons]c_m·dw(m∏x)`
  with `m` in `(P₁, P₂]`, cut into the dyadic blocks `(P₁2^b, P₁2^{b+1}]`, is evaluated by `unw_gen_lo` and `box_res`.
* `chainTU_res`: `SieveChain.chainTU_bound` by the resonant window: the chains of primes `rt` times a rough cofactor,
  with the cofactor as the variable and all of `rt` as the rest, each prime of `rt` at least `2q^{lo i}`, evaluated
  when `ResCond` holds at the cofactor's blocks and the primes' scales.

The file imports `SieveResTypeII.lean`, `SieveUnwLo.lean` and `SieveChain.lean`.
-/
import SieveResTypeII
import SieveUnwLo
import SieveChain

open Real Finset

namespace SieveTypeIIHM

open SieveTypeIIGen

/-- **The resonant estimate at each frequency, for a polynomial over the integers.** For a curve `g ≤ 1` with
`g(1/2) = 1` and its counts, `K₀` and `e₁ > 0`: for large `q`, a finite set `Xs` of integers cut by `blk` into
blocks with `P_b < m ≤ 2P_b`, coefficients `|c_m| ≤ 1`, `n + 1 ≤ K₀` and numbers `lo i`, if `ResCond` holds at each
block's exponent `log_q P_b` and the exponents of scales `Q_i ≥ q^{e₁}`, `Q_i ≥ q^{lo i}` with
`∏Q_i ≤ 2^{K₀+1}q^L/P_b` (`hR`), then at those scales, for `c′ = c` or `|c|`, every phase `κ + Σ_j ξ_jφ_j(m)` and
heights `|h_i| ≤ q^{1/100000}`, the sum over `χ ≠ 1` of the block's twisted sum times the prime sums (with the
weight `bump`) is at most `q^{L − 1/50000}`. -/
theorem box_res {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g) (K₀ : ℕ)
    {e₁ : ℝ} (he₁ : 0 < e₁) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (Xs : Finset ℕ) (cf : ℕ → ℂ), (∀ m, ‖cf m‖ ≤ 1) →
      ∀ (blk : ℕ → ℕ) (T : Finset ℕ) (Pn : ℕ → ℕ),
      (∀ m ∈ Xs, Pn (blk m) < m ∧ m ≤ 2 * Pn (blk m)) → (∀ b ∈ T, 0 < Pn b) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ (lo : ℕ → ℝ) {J : ℕ} (φ : Fin J → ℕ → ℝ),
      (∀ b ∈ T, ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) → (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ L / (Pn b : ℝ) →
        ResCond g L (n + 1) (Real.logb q (Pn b)) (fun j => Real.logb q (Q j))) →
      ∀ b ∈ T, ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) → (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ L / (Pn b : ℝ) →
        ∀ c' : ℕ → ℂ, (c' = cf ∨ c' = fun m => ((‖cf m‖ : ℝ) : ℂ)) → ∀ (ξ : Fin J → ℝ) (κ' : ℝ) (hh : ℕ → ℝ),
        (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ m ∈ Xs.filter (fun m => blk m = b),
              c' m * Complex.exp (2 * π * Complex.I * ((κ' + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ m‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ SieveDyadic.bump (Q j) (hh j)‖ ≤
          1 * (q : ℝ) ^ (L - 1 / 50000) := by
  obtain ⟨q₀, hq₀⟩ := typeII_res hg1 hg0 hcnt (f0 := SieveDyadic.bump) (SieveDyadic.contDiff_bump (n := ⊤))
    SieveDyadic.bump_support (K₀ + 1) he₁ (η := 1 / 100000) (by norm_num) le_rfl
  refine ⟨q₀, fun q _ hq Xs cf hcf blk T Pn hblk hPn n hn lo J φ hR b hb Q hQe hQlo hQprod c' hc' ξ κ' hh hhh => ?_⟩
  set S := Xs.filter (fun m => blk m = b) with hSdef
  have hS : S ⊆ Finset.Ioc (Pn b) (2 * Pn b) := by
    intro m hm
    obtain ⟨hmX, hmb⟩ := Finset.mem_filter.1 hm
    have h := hblk m hmX
    rw [hmb] at h
    exact Finset.mem_Ioc.2 h
  set a : ℕ → ℂ := fun m => c' m * Complex.exp (2 * π * Complex.I * ((κ' + ∑ j, ξ j * φ j m : ℝ) : ℂ)) with ha
  have hc'1 : ∀ m, ‖c' m‖ ≤ 1 := by
    rcases hc' with rfl | rfl
    · exact hcf
    · intro m
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact hcf m
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (2 * π * Complex.I * (r : ℂ))‖ = 1 := fun r => by
    have : 2 * π * Complex.I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have ha1 : ∀ m, ‖a m‖ ≤ 1 := fun m => by
    rw [ha]; dsimp only
    rw [norm_mul, hexp1, mul_one]
    exact hc'1 m
  -- the block's twisted sum is the polynomial `dp S (aχ) 0`
  have hdp : ∀ χ : DirichletCharacter ℂ q,
      ∑ m ∈ S, c' m * Complex.exp (2 * π * Complex.I * ((κ' + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ m =
        DirMean.dp S (fun m => a m * χ m) 0 := by
    intro χ
    unfold DirMean.dp
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [ha, zero_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  simp_rw [hdp]
  have hPpos : 0 < Pn b := hPn b hb
  have hmain := hq₀ q hq (Pn b) S hS hPpos a 0 (n + 1) (by omega) Q hh
    (fun j hj => ⟨hQe j hj, hhh j hj⟩) hQprod (hR b hb Q hQe hQlo hQprod)
  refine hmain.trans ?_
  -- `Σ_S |a|² ≤ |S| ≤ P`
  have hP0 : (0 : ℝ) < Pn b := by exact_mod_cast hPpos
  have hcardS : (S.card : ℝ) ≤ Pn b := by
    have h1 : S.card ≤ (Finset.Ioc (Pn b) (2 * Pn b)).card := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h1
    have h2 : 2 * Pn b - Pn b = Pn b := by omega
    rw [h2] at h1
    exact_mod_cast h1
  have hsum : ∑ m ∈ S, ‖a m‖ ^ 2 ≤ Pn b := by
    calc ∑ m ∈ S, ‖a m‖ ^ 2 ≤ ∑ _m ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun m _ => by
            have := ha1 m
            have h0 := norm_nonneg (a m)
            nlinarith
      _ = S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ Pn b := hcardS
  have hsq : Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / (Pn b : ℝ)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [div_le_one hP0]
    exact hsum
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (L - 1 / 50000) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / (Pn b : ℝ))
      ≤ (q : ℝ) ^ (L - 1 / 50000) * 1 := mul_le_mul_of_nonneg_left hsq hq0
    _ = 1 * (q : ℝ) ^ (L - 1 / 50000) := by ring

open Classical in
/-- **Type II with comparisons, for the resonant window.** `SieveChain.typeII_gcmp` with the resonant window's
estimate in place of the route's: for a curve `g ≤ 1` with `g(1/2) = 1` and its counts, `0 < L ≤ 5/2`, `K₀`, `J₀`,
`e₁ > 0` and `Λ₁ ≥ 0`, there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a`: let `m` run over
`S ⊆ (P₁, P₂]` with `1 ≤ P₁`, `P₂ ≤ ⌊2q^L⌋`, with coefficients `|c_m| ≤ 1`, and `x` over the `(n + 1)`-tuples of
primes up to `⌊2q^L⌋` with at most `J₀` comparisons `l` (`m`-parts at most `Λ₁ log q`), such that wherever they hold
each `x_i ≥ 2q^{e₁}`, `x_i ≥ 2q^{lo i}` and `m∏x_i ≤ 2q^L`; and let `ResCond` hold at `log_q P′` for `P′ ≥ P₁` and the
exponents of scales `Q_i ≥ q^{e₁}`, `Q_i ≥ q^{lo i}` with `∏Q_i ≤ 2^{K₀+1}q^L/P′`. Then
`|Σ_m Σ_x 1[l holds]c_m(1[m∏x ≡ a] − 1[(m∏x, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)`. The comparisons with no prime become
conditions on `m`; the others are pivoted (`SieveChain.pivoted`); `m` is cut into the dyadic blocks
`(P₁2^b, P₁2^{b+1}]` (`SieveTypeIIU.blk_spec`); and `SieveUnwGen.unw_gen_lo` applies with `box_res`. -/
theorem typeII_gcmp_res {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) (K₀ J₀ : ℕ) {e₁ Λ₁ : ℝ} (he₁ : 0 < e₁) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ → 1 ≤ P₁ → P₂ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) → ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ lo : ℕ → ℝ,
      ∀ (l : List (SieveChain.GCmp (n + 1))), l.length ≤ J₀ → (∀ C ∈ l, ∀ m ∈ S, C.c m ≤ Λ₁ * Real.log q) →
      (∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ l, C.holds m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (∀ i : Fin (n + 1), 2 * (q : ℝ) ^ lo i ≤ x i) ∧
          (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      (∀ P' : ℕ, P₁ ≤ P' → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
        (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ L / (P' : ℝ) →
        ResCond g L (n + 1) (Real.logb q P') (fun j => Real.logb q (Q j))) →
      ‖∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) => SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ L⌋₊),
          (if ∀ C ∈ l, C.holds m x then acoef m * SieveFamily.dw q a (m * ∏ i, x i) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := SieveUnwGen.unw_gen_lo (ι := ℕ) (κ := ℕ) K₀ J₀ 1 hL0 hL he₁ zero_le_one hΛ₁
  obtain ⟨q₂, hq₂⟩ := box_res hg1 hg0 hcnt K₀ he₁
  refine ⟨δ, hδ, max (max q₁ q₂) 2, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hn lo l hl hc hsupp hR
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  -- the comparisons with no prime become conditions on `m`
  set S' := S.filter (fun m => ∀ C ∈ l, (∀ i, C.e i = 0) → C.holds m (fun _ => 1)) with hS'
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hsum : ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
        SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ L⌋₊),
        (if ∀ C ∈ l, C.holds m x then acoef m * SieveFamily.dw q a (m * ∏ i, x i) else 0) =
      ∑ m ∈ S', ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
        SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ L⌋₊),
        (if ∀ C' ∈ SieveChain.pivoted l, C'.holds m x then acoef m * SieveFamily.dw q a (m * ∏ i, x i)
          else 0) := by
    rw [hS', Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · refine Finset.sum_congr rfl fun x _ => ?_
      have : (∀ C ∈ l, C.holds m x) ↔ ∀ C' ∈ SieveChain.pivoted l, C'.holds m x := by
        rw [SieveChain.holds_iff_pivoted]; tauto
      simp only [this]
    · refine Finset.sum_eq_zero fun x _ => ?_
      rw [ite_eq_right]
      intro h
      exact hm ((SieveChain.holds_iff_pivoted l m x).1 h).2
  rw [hsum]
  set l' := SieveChain.pivoted l with hl'
  have hl'len : l'.length ≤ J₀ := (SieveChain.length_pivoted_le l).trans hl
  have hget : ∀ (m : ℕ) (x : Fin (n + 1) → ℕ), (∀ C ∈ l', C.holds m x) ↔ ∀ t, (l'.get t).holds m x := by
    intro m x
    constructor
    · intro h t
      exact h _ (List.get_mem l' t)
    · intro h C hC
      obtain ⟨t, rfl⟩ := List.mem_iff_get.1 hC
      exact h t
  have hcl' : ∀ t : Fin l'.length, ∀ m ∈ S', (l'.get t).c m ≤ Λ₁ * Real.log q := by
    intro t m hm
    obtain ⟨C, hC, hCe, hCt⟩ := SieveChain.mem_pivoted.1 (List.get_mem l' t)
    rw [← hCt]
    exact hc C hC m (hS'S hm)
  -- the blocks of `m`
  set Y := ⌊2 * (q : ℝ) ^ L⌋₊ with hY
  set M := Nat.log 2 Y + 1 with hM
  have hY0 : Y ≠ 0 := by
    have : 1 ≤ Y := Nat.le_floor (by
      push_cast
      have := Real.one_le_rpow (show (1 : ℝ) ≤ q by linarith) hL0.le
      linarith)
    omega
  set blk : ℕ → ℕ := fun m => Nat.log 2 ((m - 1) / P₁) with hblkdef
  set Pn : ℕ → ℕ := fun b => P₁ * 2 ^ b with hPn
  have hspec : ∀ m ∈ S', Pn (blk m) < m ∧ m ≤ 2 * Pn (blk m) := fun m hm =>
    SieveTypeIIU.blk_spec hP₁ (Finset.mem_Ioc.1 (hS (hS'S hm))).1
  have hPnpos : ∀ b, 0 < Pn b := fun b => Nat.mul_pos (by omega) (by positivity)
  have hPnP₁ : ∀ b, P₁ ≤ Pn b := fun b => Nat.le_mul_of_pos_right _ (by positivity)
  have hblkT : ∀ m ∈ S', blk m ∈ Finset.range M := by
    intro m hm
    have hmP := Finset.mem_Ioc.1 (hS (hS'S hm))
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    have hd : (m - 1) / P₁ ≠ 0 := by
      have : 1 ≤ (m - 1) / P₁ := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
      omega
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    calc 2 ^ blk m ≤ (m - 1) / P₁ := Nat.pow_log_le_self 2 hd
      _ ≤ m := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
      _ ≤ Y := hmP.2.trans hP₂
  have hTcard : ((Finset.range M).card : ℝ) ≤ (3 + 4 * Real.log q) ^ 1 := by
    rw [Finset.card_range, pow_one, hM]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqL0 : 0 < (q : ℝ) ^ L := Real.rpow_pos_of_pos hq0 _
    have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ L) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
    have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
      refine le_of_mul_le_mul_right ?_ hlog2
      nlinarith [hL, hL0]
    push_cast
    linarith
  have hsumb : ∀ b ∈ Finset.range M, ∑ m ∈ S'.filter (fun m => blk m = b), ‖acoef m‖ ≤ (Pn b : ℝ) * 1 := by
    intro b _
    have hsub : S'.filter (fun m => blk m = b) ⊆ Finset.Ioc (Pn b) (2 * Pn b) := by
      intro m hm
      obtain ⟨hmS, hmb⟩ := Finset.mem_filter.1 hm
      have h := hspec m hmS
      rw [hmb] at h
      exact Finset.mem_Ioc.2 h
    have hcard : ((S'.filter (fun m => blk m = b)).card : ℝ) ≤ Pn b := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ioc, show 2 * Pn b - Pn b = Pn b by omega] at h1
      exact_mod_cast h1
    calc ∑ m ∈ S'.filter (fun m => blk m = b), ‖acoef m‖ ≤ ∑ _m ∈ S'.filter (fun m => blk m = b), (1 : ℝ) :=
          Finset.sum_le_sum fun m _ => hacoef m
      _ = (S'.filter (fun m => blk m = b)).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (Pn b : ℝ) * 1 := by rw [mul_one]; exact hcard
  have hbox := hq₂ q hq2 S' acoef hacoef blk (Finset.range M) Pn hspec (fun b _ => hPnpos b) n hn lo
    (φ := fun t : Fin l'.length => (l'.get t).c)
    (fun b _ Q hQe hQlo hQprod => hR (Pn b) (hPnP₁ b) Q hQe hQlo hQprod)
  have h := hq₁ q hq1 a ha S' id acoef 1 zero_le_one blk (Finset.range M) (fun b => (Pn b : ℝ)) hblkT hTcard
    (fun b _ => by exact_mod_cast hPnpos b) (fun m hm => by exact_mod_cast (hspec m hm).1) hsumb n hn lo
    (J := l'.length) hl'len (fun t => (l'.get t).c) (fun t => (l'.get t).e) (fun t => (l'.get t).holds)
    (fun t i => (l'.get t).he i) (fun t m x => (l'.get t).spec m x) (fun t m hm => hcl' t m hm)
    (fun t => (l'.get t).piv) (fun t => (l'.get t).hpiv)
    (fun m hm x hx hall => hsupp m (hS'S hm) x hx ((SieveChain.holds_iff_pivoted l m x).2
      ⟨(hget m x).2 hall, (Finset.mem_filter.1 hm).2⟩))
    (fun b hb Q hQe hQlo hQprod c' hc' ξ κ' hh hhh => hbox b hb Q hQe hQlo hQprod c' hc' ξ κ' hh hhh)
  rw [one_mul] at h
  convert h using 2
  unfold SieveFamily.Dsum
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
  have hcast : ∀ t : Fin l'.length, (((if (l'.get t).holds m x then 1 else 0 : ℝ)) : ℂ) =
      if (l'.get t).holds m x then 1 else 0 := fun t => by split_ifs <;> simp
  simp only [hcast, id]
  rw [Finset.prod_boole]
  by_cases hall : ∀ C ∈ l', C.holds m x
  · rw [ite_eq_left hall, ite_eq_left (fun t _ => (hget m x).1 hall t), mul_one]
  · rw [ite_eq_right hall, ite_eq_right (fun h' => hall ((hget m x).2 fun t => h' t (Finset.mem_univ _))),
      mul_zero, zero_mul]

section Chain

open SieveChain SieveRoute SieveTree SieveFamily SieveCmp Classical

/-- **Chains times a rough cofactor, by the resonant window.** `SieveChain.chainTU_bound` with the resonant window's
estimate: the cofactor `n/∏rt` is the variable, and all the chain's primes are the rest. For a curve `g ≤ 1` with
`g(1/2) = 1` and its counts, `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`, there are `δ > 0` and `q₀` such that for `q ≥ q₀` and
a unit `a`: let `rt` run over the `(k′ + 1)`-tuples of primes up to `⌊2q^L⌋` satisfying at most `J₀` comparisons `Ω`,
each with its entries at least `q^{e₀}` and `2q^{lo i}`, its last entry least, and `W₀ < ∏rt ≤ W₁ ≤ ⌊q^L⌋` with
`⌊q^L⌋/W₁ ≥ 1`; and let `ResCond` hold at `log_q P′` for every `P′ ≥ ⌊q^L⌋/W₁` and the exponents of scales
`Q_i ≥ q^{e₀/2}`, `Q_i ≥ q^{lo i}` with `∏Q_i ≤ 2^{k′+3}q^L/P′`. Then the multiples `n ∈ (⌊q^L⌋, ⌊2q^L⌋]` of `∏rt`
with no prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chainTU_res [Route] [RouteOK] {g : ℝ → ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1)
    (hcnt : CurveCounts g) {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (W₀ W₁ : ℕ) (Ω : List (GCmp (k' + 1))) (lo : ℕ → ℝ), Ω.length ≤ J₀ →
      (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (∀ i : Fin (k' + 1), 2 * (q : ℝ) ^ lo i ≤ rt i) ∧
          (∀ i, rt (Fin.last k') ≤ rt i) ∧ W₀ < ∏ i, rt i ∧ ∏ i, rt i ≤ W₁) →
      W₁ ≤ ⌊(q : ℝ) ^ L⌋₊ → 1 ≤ ⌊(q : ℝ) ^ L⌋₊ / W₁ →
      (∀ P' : ℕ, ⌊(q : ℝ) ^ L⌋₊ / W₁ ≤ P' → ∀ Q : ℕ → ℝ, (∀ j < k' + 1, (q : ℝ) ^ (e₀ / 2) ≤ Q j) →
        (∀ j < k' + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (k' + 1), Q j ≤ 2 ^ (k' + 2 + 1) * (q : ℝ) ^ L / (P' : ℝ) →
        ResCond g L (k' + 1) (Real.logb q P') (fun j => Real.logb q (Q j))) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_gcmp_res hg1 hg0 hcnt L_pos L_le (k' + 2) (J₀ + 3) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + L + 1 by linarith [L_pos])
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev1)
  refine ⟨δ, hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha W₀ W₁ Ω lo hΩlen hΩc hΩ hW₁ hP₁1 hRes
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqe : (2 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set S := Finset.Ioc (N₁ / W₁) (N₂ / (W₀ + 1)) with hSdef
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) (by route_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₁le : (N₁ : ℝ) ≤ (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- the tuples
  have hRT : ∀ rt ∈ RTg (k' + 1) N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 rt) := by
    intro rt hrt
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2, hrt.2⟩
  -- each tuple: its multiples as cofactors in the window
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ k ∈ S, (if rt (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
          then dw q a (k * ∏ i, rt i) else 0) := by
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨-, -, hlast, hlo, hhi⟩ := hΩ rt hrtp hrtΩ
    have hW0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hWr : rough (rt (Fin.last k')) (∏ i, rt i) := by
      intro ℓ hℓp hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
      have := hlast i
      omega
    rw [sum_cofactor_range (dw q a) hW0 hWr hlo hhi hW₁ hP₁1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (∏ i, rt i) k]
  have hsum : ∑ rt ∈ RTg (k' + 1) N₂ Ω, ∑ n ∈ Finset.Ioc N₁ N₂,
      dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
      ∑ k ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => SieveTypeIIU.primesLe N₂),
        (if ∀ C ∈ cmpsTU k' Ω N₁ N₂, C.holds k x then (fun _ => (1 : ℂ)) k * dw q a (k * ∏ i, x i) else 0) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    rw [RTg, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Fintype.mem_piFinset] at hx
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hx i)).2.one_lt.le
    have hiff : (∀ C ∈ cmpsTU k' Ω N₁ N₂, C.holds k x) ↔ (∀ C ∈ Ω, C.holds 0 x) ∧
        (x (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, x i) * k ∧ (∏ i, x i) * k ≤ N₂) := by
      have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁1
      have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
      have hc : ((∏ i, x i) * k : ℕ) = ((k : ℝ) * ∏ i, (x i : ℝ)) := by push_cast; ring
      unfold cmpsTU
      simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, and_true, GCmp.const_holds, grough_holds _ k hx1,
        grangeLo_holds hN₁0 hk1 hx1, grangeHi_holds hN₂0 hk1 hx1]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · have : (N₁ : ℝ) < ((∏ i, x i) * k : ℕ) := by rw [hc]; exact h3
          exact_mod_cast this
        · have : (((∏ i, x i) * k : ℕ) : ℝ) ≤ N₂ := by rw [hc]; exact h4
          exact_mod_cast this
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · rw [← hc]; exact_mod_cast h3
        · rw [← hc]; exact_mod_cast h4
    by_cases hΩx : ∀ C ∈ Ω, C.holds 0 x
    · rw [ite_eq_left hΩx]
      by_cases hc : x (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, x i) * k ∧ (∏ i, x i) * k ≤ N₂
      · rw [ite_eq_left hc, ite_eq_left (hiff.2 ⟨hΩx, hc⟩), one_mul]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h).2)]
    · rw [ite_eq_right hΩx, ite_eq_right (fun h => hΩx (hiff.1 h).1)]
  rw [hsum]
  -- the bound
  have hlog : ∀ (t c : ℝ), 0 < t → t ≤ (q : ℝ) ^ c → Real.log t ≤ c * Real.log q := fun t c ht h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log ht h
  have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
  have hB1 : L * Real.log q ≤ (Λ₁ + L + 1) * Real.log q := by
    rw [add_mul, add_mul, one_mul]
    linarith
  have hB2 : (L + 1 : ℝ) * Real.log q ≤ (Λ₁ + L + 1) * Real.log q := by
    rw [add_mul, add_mul, add_mul, one_mul]
    linarith
  have hB3 : Λ₁ * Real.log q ≤ (Λ₁ + L + 1) * Real.log q := by
    rw [add_mul, add_mul, one_mul]
    have : (0 : ℝ) ≤ L * Real.log q := by have := (L_pos : (0 : ℝ) < L); positivity
    linarith
  refine hq₁ q hq1 a ha (N₁ / W₁) (N₂ / (W₀ + 1)) S (subset_refl _) hP₁1 (Nat.div_le_self _ _) (fun _ => 1)
    (fun _ => by simp) k' (by omega) lo (cmpsTU k' Ω N₁ N₂) (by unfold cmpsTU; simp; omega) ?_ ?_
    (fun P' hP' Q hQe hQlo hQprod => hRes P' hP' Q hQe hQlo hQprod)
  · intro C hC m hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.1 hm).1
      omega
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmP : (m : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
      have h1 : (m : ℝ) ≤ ((N₂ / (W₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Ioc.1 hm).2
      have h2 : ((N₂ / (W₀ + 1) : ℕ) : ℝ) ≤ N₂ := by exact_mod_cast Nat.div_le_self _ _
      have h3 : 2 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
        rw [Real.rpow_add hq0, Real.rpow_one]
        have h0 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
        nlinarith
      linarith
    have hlm := (hlog m (L + 1) (by linarith) hmP).trans hB2
    have hlm0 : 0 ≤ Real.log m := Real.log_nonneg hm1'
    have hmf : Real.log (Nat.minFac m) ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast Nat.minFac_pos m) (by exact_mod_cast Nat.minFac_le (by omega))
    have hN₁l : 0 ≤ Real.log N₁ := Real.log_nonneg (by exact_mod_cast hN₁1)
    have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      have h0 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
      have h1 : 2 * (q : ℝ) ^ L ≤ (q : ℝ) ^ L * q := by
        have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
        linarith
      linarith
    have hlN₂ := (hlog N₂ (L + 1) (by exact_mod_cast hN₂1) hN₂q).trans hB2
    unfold cmpsTU at hC
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
    rcases hC with ⟨C₀, hC₀, rfl⟩ | rfl | rfl | rfl
    · exact (hΩc C₀ hC₀).trans hB3
    · show Real.log (Nat.minFac m) ≤ _
      linarith
    · show Real.log m - Real.log N₁ ≤ _
      linarith
    · show Real.log N₂ - Real.log m ≤ _
      linarith
  · intro m hm x hx hall
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.1 hm).1
      omega
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
    unfold cmpsTU at hall
    simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, GCmp.const_holds] at hall
    obtain ⟨hΩx, -, -, hhi⟩ := hall
    have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
    refine ⟨fun i => (hqe2.trans ((hΩ x hx hΩx).1 i)), fun i => (hΩ x hx hΩx).2.1 i, ?_⟩
    exact ((grangeHi_holds hN₂0 hm1 hx1).1 hhi).trans hN₂le

end Chain

end SieveTypeIIHM

#print axioms SieveTypeIIHM.box_res
#print axioms SieveTypeIIHM.typeII_gcmp_res
#print axioms SieveTypeIIHM.chainTU_res
