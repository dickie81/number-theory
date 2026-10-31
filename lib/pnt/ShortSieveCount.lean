import ShortSieveLevel
import ZetaGMWin

/-!
# Counts of large values of a Dirichlet polynomial through its powers

For `D(t) = Σ_{j∈S} c_j j^{−it}` with `S ⊆ (P, 2P]` and `|c_j| ≤ 1`, the large values of `D` are those of its
`m`-th power, which lies on `(P^m, (2P)^m]` and is cut into `2m` pieces `(P^m(3/2)^i, P^m(3/2)^{i+1}]`
(`ZetaGMWin.pow_piece_pick`). This module counts the `1`-separated points at which `|D| ≥ V` with the mean value
theorem (`DirMean.large_values`) applied to each piece, and with the Halász–Montgomery inequality for the power
(`ZetaKernel.power_count_pts`) in windows of height `T₀`:

* `pieceS_sub_Ioc`: a piece lies in a dyadic block `(Q, 2Q]`, `Q = ⌊P^m(3/2)^i⌋`, once `P^m ≥ 3`;
* `card_le_mv`: at most `(2m)³(b − a + 8Λ(1 + log Λ))(2 + log²(2Λ))G_m/V^{2m}` such points in
  `[a + 1/2, b − 1/2]`, with `Λ = (2P)^m` and `G_m` the mass bound of the `m`-th power
  (`LinnikHuxley.mass_pow_le`);
* `card_le_hux`: at most `((b − a)/T₀ + 1)·2e·G_mΛ(1 + KE(2 log Λ + 1))/V^{2m}` such points in `[a, b]`, given a
  kernel bound of the form of `ZetaKernel.norm_kz_le` and `2e·G_m(KE + C_KΛ^{1/12}(T₀ + 2)^{5/12+ε}) ≤ V^{2m}`.
-/

open Finset Real Complex DirMean LinnikPower LinnikHuxley ZetaGMWin

noncomputable section

namespace ShortSieveCount

/-- At `σ = 0` the weighted coefficients of `ZetaGMWin.pow_piece_pick` are the coefficients. -/
lemma coeff_rpow_zero (c : ℕ → ℂ) : (fun j : ℕ => c j * (((j : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ)) = c := by
  funext j
  simp

/-- A piece of the `m`-th power lies in a dyadic block `(Q, 2Q]`, `Q = ⌊P^m(3/2)^i⌋`, once `P^m ≥ 3`. -/
lemma pieceS_sub_Ioc {S : Finset ℕ} {P m i : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) (hm : 1 ≤ m)
    (hP3 : 3 ≤ P ^ m) :
    pieceS S P m i ⊆ Ioc ⌊(P : ℝ) ^ m * (3 / 2) ^ i⌋₊ (2 * ⌊(P : ℝ) ^ m * (3 / 2) ^ i⌋₊) := by
  intro n hn
  obtain ⟨h1, h2, -⟩ := mem_pieceS hP hS hm hn
  set X : ℝ := (P : ℝ) ^ m * (3 / 2) ^ i with hX
  have hPm : (3 : ℝ) ≤ (P : ℝ) ^ m := by exact_mod_cast hP3
  have hpow : (1 : ℝ) ≤ (3 / 2) ^ i := one_le_pow₀ (by norm_num)
  have hX3 : (3 : ℝ) ≤ X := by nlinarith
  have hQ : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hQ' : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
  have hQ3 : (3 : ℝ) ≤ ⌊X⌋₊ := by
    have : (3 : ℕ) ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX3)
    exact_mod_cast this
  have h2' : (n : ℝ) ≤ X * (3 / 2) := by rw [hX, mul_assoc, ← pow_succ]; exact h2
  refine mem_Ioc.2 ⟨?_, ?_⟩
  · exact_mod_cast lt_of_le_of_lt hQ h1
  · have : (n : ℝ) ≤ 2 * ⌊X⌋₊ := by nlinarith
    exact_mod_cast this

/-- **The mean value count for a power.** Let `S ⊆ (P, 2P]` with `P^m ≥ 3` and `|c_j| ≤ 1`, and let `R` be a set of
`1`-separated points of `[a + 1/2, b − 1/2]` at which `|Σ_{j∈S} c_j j^{−it}| ≥ V > 0`. Then
`|R| ≤ (2m)³(b − a + 8Λ(1 + log Λ))(2 + log²(2Λ))G_m/V^{2m}`, `Λ = (2P)^m`. -/
theorem card_le_mv {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ}
    (hc : ∀ j ∈ S, ‖c j‖ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (hP3 : 3 ≤ P ^ m) {a b : ℝ} (hab : a ≤ b)
    {V : ℝ} (hV : 0 < V) {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) (R : Finset ℝ)
    (hsep : ShortSieveLevel.Sep R) (hR : ∀ x ∈ R, a + 1 / 2 ≤ x ∧ x ≤ b - 1 / 2)
    (hbig : ∀ x ∈ R, V ≤ ‖dp S c x‖) :
    (R.card : ℝ) ≤ (2 * m) ^ 3 * ((b - a + 8 * ((2 * P : ℕ) : ℝ) ^ m * (1 + Real.log (((2 * P : ℕ) : ℝ) ^ m))) *
      (2 + Real.log (2 * ((2 * P : ℕ) : ℝ) ^ m) ^ 2) * Gm εd P m 0) / V ^ (2 * m) := by
  classical
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  set W : ℝ := V ^ m / (2 * m) with hW
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hW0 : 0 < W := by positivity
  set e : ℕ → ℂ := fun n => powCo S c m n * (((n : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ) with he
  have he' : e = powCo S c m := coeff_rpow_zero _
  -- each point lies on a large piece
  have hpick : ∀ x ∈ R, ∃ i < 2 * m, W ≤ ‖dp (pieceS S P m i) e x‖ := by
    intro x hx
    have hx' : V ≤ ‖dp S (fun j => c j * (((j : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ)) x‖ := by
      rw [coeff_rpow_zero]; exact hbig x hx
    exact pow_piece_pick hP hS c hm 0 x hV hx'
  choose! idx hidx hidxbig using hpick
  -- the mass of the power
  have hmass : ∑ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 ≤ Gm εd P m 0 := by
    have hc' : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ) := fun j hj => by
      have hj0 : 0 < j := by have := (mem_Ioc.1 (hS hj)).1; omega
      have : 1 ≤ j.divisors.card := card_pos.2 ⟨1, Nat.one_mem_divisors.2 hj0.ne'⟩
      exact (hc j hj).trans (by exact_mod_cast this)
    have := mass_pow_le hP hS hc' hm le_rfl hεd hεd1
    simpa using this
  -- one piece
  have hpiece : ∀ i < 2 * m, (((R.filter fun x => idx x = i).card : ℝ)) * W ^ 2 ≤
      (b - a + 8 * Λ * (1 + Real.log Λ)) * (2 + Real.log (2 * Λ) ^ 2) * Gm εd P m 0 := by
    intro i hi
    set Ri := R.filter fun x => idx x = i with hRi
    rcases Ri.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
    · rw [h0, card_empty, Nat.cast_zero, zero_mul]
      have hG0 : 0 ≤ Gm εd P m 0 := (sum_nonneg fun n _ => by positivity).trans hmass
      have hlog : 0 ≤ Real.log Λ := Real.log_nonneg (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P)))
      have hba : 0 ≤ b - a := by linarith
      positivity
    -- the piece is nonempty, so its block lies below `Λ`
    set Q : ℕ := ⌊(P : ℝ) ^ m * (3 / 2) ^ i⌋₊ with hQ
    have hsub : pieceS S P m i ⊆ Ioc Q (2 * Q) := pieceS_sub_Ioc hP hS hm hP3
    have hne : (pieceS S P m i).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      have := hidxbig x₀ (mem_filter.1 hx₀).1
      rw [(mem_filter.1 hx₀).2, hcon] at this
      simp [dp] at this
      linarith
    obtain ⟨n₀, hn₀⟩ := hne
    have hQn : (Q : ℝ) < n₀ := by exact_mod_cast (mem_Ioc.1 (hsub hn₀)).1
    have hn₀Λ : (n₀ : ℝ) ≤ Λ := (mem_pieceS hP hS hm hn₀).2.2
    have hQ1 : 1 ≤ Q := by
      have := (mem_Ioc.1 (hsub hn₀))
      have h3 : (3 : ℝ) ≤ (P : ℝ) ^ m * (3 / 2) ^ i := by
        have hPm : (3 : ℝ) ≤ (P : ℝ) ^ m := by exact_mod_cast hP3
        have hpow : (1 : ℝ) ≤ (3 / 2) ^ i := one_le_pow₀ (by norm_num)
        nlinarith
      exact Nat.le_floor (by norm_num; linarith)
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
    have hQΛ : (Q : ℝ) ≤ Λ := by linarith
    -- the mean value theorem on the piece
    have hlv := large_values hQ1 hsub e hab Ri (fun x hx y hy hxy => hsep x (mem_filter.1 hx).1 y
      (mem_filter.1 hy).1 hxy) (fun x hx => hR x (mem_filter.1 hx).1)
    have hlow : ((Ri.card : ℝ)) * W ^ 2 ≤ ∑ x ∈ Ri, ‖dp (pieceS S P m i) e x‖ ^ 2 := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun x hx => ?_
      have := hidxbig x (mem_filter.1 hx).1
      rw [(mem_filter.1 hx).2] at this
      exact pow_le_pow_left₀ hW0.le this 2
    have hmass_i : ∑ n ∈ pieceS S P m i, ‖e n‖ ^ 2 ≤ Gm εd P m 0 := by
      rw [he']
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity).trans hmass
    have hA : b - a + 8 * Q * (1 + Real.log Q) ≤ b - a + 8 * Λ * (1 + Real.log Λ) := by
      have hlogQ : Real.log Q ≤ Real.log Λ := Real.log_le_log hQ0 hQΛ
      have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
      nlinarith
    have hB : 2 + Real.log (2 * Q) ^ 2 ≤ 2 + Real.log (2 * Λ) ^ 2 := by
      have h1 : Real.log (2 * Q) ≤ Real.log (2 * Λ) := Real.log_le_log (by positivity) (by linarith)
      have h0 : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith [show (1 : ℝ) ≤ Q by exact_mod_cast hQ1])
      nlinarith
    have hA0 : 0 ≤ b - a + 8 * Q * (1 + Real.log Q) := by
      have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
      have : 0 ≤ b - a := by linarith
      positivity
    have hS0 : 0 ≤ ∑ n ∈ pieceS S P m i, ‖e n‖ ^ 2 := sum_nonneg fun _ _ => by positivity
    have hAΛ : 0 ≤ b - a + 8 * Λ * (1 + Real.log Λ) := hA0.trans hA
    calc ((Ri.card : ℝ)) * W ^ 2 ≤ ∑ x ∈ Ri, ‖dp (pieceS S P m i) e x‖ ^ 2 := hlow
      _ ≤ (b - a + 8 * Q * (1 + Real.log Q)) * (2 + Real.log (2 * Q) ^ 2) *
          ∑ n ∈ pieceS S P m i, ‖e n‖ ^ 2 := hlv
      _ ≤ (b - a + 8 * Λ * (1 + Real.log Λ)) * (2 + Real.log (2 * Λ) ^ 2) * Gm εd P m 0 :=
        mul_le_mul (mul_le_mul hA hB (by positivity) hAΛ) hmass_i hS0 (mul_nonneg hAΛ (by positivity))
  -- all pieces
  have hcard : (R.card : ℝ) = ∑ i ∈ range (2 * m), ((R.filter fun x => idx x = i).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := idx) (t := range (2 * m)) fun x hx => mem_range.2 (hidx x hx)]
    push_cast
    rfl
  set K : ℝ := (b - a + 8 * Λ * (1 + Real.log Λ)) * (2 + Real.log (2 * Λ) ^ 2) * Gm εd P m 0 with hK
  have hsum : (R.card : ℝ) * W ^ 2 ≤ 2 * m * K := by
    rw [hcard, sum_mul]
    calc ∑ i ∈ range (2 * m), ((R.filter fun x => idx x = i).card : ℝ) * W ^ 2
        ≤ ∑ _i ∈ range (2 * m), K := sum_le_sum fun i hi => hpiece i (mem_range.1 hi)
      _ = 2 * m * K := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hW2 : W ^ 2 = V ^ (2 * m) / (2 * m) ^ 2 := by
    rw [hW, div_pow, ← pow_mul, mul_comm m 2]
  rw [hW2] at hsum
  have hV2 : 0 < V ^ (2 * m) := by positivity
  rw [le_div_iff₀ hV2]
  have h2m : (0 : ℝ) < (2 * m) ^ 2 := by positivity
  calc (R.card : ℝ) * V ^ (2 * m) = (R.card : ℝ) * (V ^ (2 * m) / (2 * m) ^ 2) * (2 * m) ^ 2 := by
        field_simp
    _ ≤ 2 * m * K * (2 * m) ^ 2 := by gcongr
    _ = (2 * m) ^ 3 * K := by ring

/-- **The Halász–Montgomery count for a power, in windows.** Let `S ⊆ (P, 2P]` and `|c_j| ≤ 1`, and let `R` be a set
of `1`-separated points of `[a, b]` at which `|Σ_{j∈S} c_j j^{−it}| ≥ V > 0`. If the kernel of `ζ` is at most
`KE·Λe^{−|Im z|} + C_K Λ^{1/12}(|Im z| + 2)^{5/12+ε}` (`ZetaKernel.norm_kz_le`) and the window `T₀ > 0` has
`2e·G_m(KE + C_K Λ^{1/12}(T₀ + 2)^{5/12+ε}) ≤ V^{2m}`, then
`|R| ≤ ((b − a)/T₀ + 1)·2e·G_mΛ(1 + KE(2 log Λ + 1))/V^{2m}`, `Λ = (2P)^m`: `ZetaKernel.power_count_pts` in each
window of height `T₀`. -/
theorem card_le_hux {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ}
    (hc : ∀ j ∈ S, ‖c j‖ ≤ 1) {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (hab : a ≤ b) {V : ℝ} (hV : 0 < V)
    {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) {ε CK : ℝ} (hε : 0 ≤ ε) (hCK0 : 0 ≤ CK)
    (hCK : ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, LinnikPower.kTerm ZetaFourth.χ₁ Λ z n‖ ≤
        InghamDensity.KE * Λ * Real.exp (-|z.im|) + CK * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε))
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hfeas : 2 * Real.exp 1 * Gm εd P m 0 * (InghamDensity.KE +
      CK * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 : ℝ) * (T₀ + 2) ^ (5 / 12 + ε)) ≤ V ^ (2 * m))
    (R : Finset ℝ) (hsep : ShortSieveLevel.Sep R) (hR : ∀ x ∈ R, a ≤ x ∧ x ≤ b)
    (hbig : ∀ x ∈ R, V ≤ ‖dp S c x‖) :
    (R.card : ℝ) ≤ ((b - a) / T₀ + 1) * (2 * Real.exp 1 * Gm εd P m 0 * ((2 * P : ℕ) : ℝ) ^ m *
      (1 + InghamDensity.KE * (2 * Real.log (((2 * P : ℕ) : ℝ) ^ m) + 1)) / V ^ (2 * m)) := by
  classical
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P))
  set Bd : ℝ := 2 * Real.exp 1 * Gm εd P m 0 * Λ * (1 + InghamDensity.KE * (2 * Real.log Λ + 1)) /
    V ^ (2 * m) with hBd
  have hSpos : ∀ j ∈ S, 0 < j := fun j hj => by have := (mem_Ioc.1 (hS hj)).1; omega
  have hc' : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ) := fun j hj => by
    have : 1 ≤ j.divisors.card := card_pos.2 ⟨1, Nat.one_mem_divisors.2 (hSpos j hj).ne'⟩
    exact (hc j hj).trans (by exact_mod_cast this)
  set D : ℕ → Finset ℝ := fun l => R.filter fun x => ⌊(x - a) / T₀⌋₊ = l with hD
  have hsubD : R ⊆ (range (⌊(b - a) / T₀⌋₊ + 1)).biUnion D := by
    intro x hx
    refine mem_biUnion.2 ⟨⌊(x - a) / T₀⌋₊, mem_range.2 ?_, mem_filter.2 ⟨hx, rfl⟩⟩
    rw [Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [(hR x hx).2]) hT₀.le)
  have hDl : ∀ l, ((D l).card : ℝ) ≤ Bd := by
    intro l
    have hDsub : ∀ x ∈ D l, x ∈ R := fun x hx => (mem_filter.1 hx).1
    have hT : ∀ x ∈ D l, ∀ x' ∈ D l, |id x - id x'| ≤ T₀ := by
      intro x hx x' hx'
      have hl1 := (mem_filter.1 hx).2
      have hl2 := (mem_filter.1 hx').2
      have a1 : 0 ≤ (x - a) / T₀ := div_nonneg (by linarith [(hR x (hDsub x hx)).1]) hT₀.le
      have a2 : 0 ≤ (x' - a) / T₀ := div_nonneg (by linarith [(hR x' (hDsub x' hx')).1]) hT₀.le
      have f1 := Nat.floor_le a1
      have f2 := Nat.lt_floor_add_one ((x - a) / T₀)
      have f3 := Nat.floor_le a2
      have f4 := Nat.lt_floor_add_one ((x' - a) / T₀)
      rw [hl1] at f1 f2
      rw [hl2] at f3 f4
      rw [le_div_iff₀ hT₀] at f1 f3
      rw [div_lt_iff₀ hT₀] at f2 f4
      simp only [id]
      rw [abs_le]; constructor <;> nlinarith
    refine ZetaKernel.power_count_pts hP hS (c := c) hc' hm (σb := 0) le_rfl (fun _ => (0 : ℝ)) id
      (fun r _ => ⟨le_rfl, by norm_num⟩)
      (fun r hr r' hr' hne => hsep r (hDsub r hr) r' (hDsub r' hr') hne)
      hT hV (fun r hr => ?_) hεd hεd1 (B := CK * Λ ^ (1 / 12 : ℝ) * (T₀ + 2) ^ (5 / 12 + ε))
      (by positivity) (fun z hz0 hz1 hzT => ?_) hfeas
    · have h := hbig r (hDsub r hr)
      rw [← coeff_rpow_zero c, ZetaGMWin.dp_eq_pv S hSpos c 0 r] at h
      simpa using h
    · refine (hCK Λ hΛ1 z hz0 hz1).trans ?_
      gcongr
  calc (R.card : ℝ) ≤ ((range (⌊(b - a) / T₀⌋₊ + 1)).biUnion D).card := by
        exact_mod_cast card_le_card hsubD
    _ ≤ ∑ l ∈ range (⌊(b - a) / T₀⌋₊ + 1), ((D l).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _l ∈ range (⌊(b - a) / T₀⌋₊ + 1), Bd := sum_le_sum fun l _ => hDl l
    _ = ((⌊(b - a) / T₀⌋₊ : ℝ) + 1) * Bd := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((b - a) / T₀ + 1) * Bd := by
        have hBd0 : 0 ≤ Bd := le_trans (by positivity) (hDl 0)
        gcongr
        exact Nat.floor_le (div_nonneg (by linarith) hT₀.le)

end ShortSieveCount
