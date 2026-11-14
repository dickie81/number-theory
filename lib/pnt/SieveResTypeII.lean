/-
# The resonant window: Proposition 3′ with the characters classed by the sizes of the rest's prime sums

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIIHM.typeII_gen_hm` bounds `Σ_{χ≠1} |W(χ)|·|∏_j Sp_j(χ)|` by the bins of the characters' zeros: in the bin
of `β` each prime sum is at most `Q_j^{β+w}`, and the bin has at most `(qT)^{g(β)}` characters. The resonant window
classes the characters further, by the size of each prime sum: the level `ℓ_j` of `Sp_j(χ)` in steps of
`τ = 10⁻⁶` of `log_{Q_j}` (`SieveTypeIIHM.lev`, capped at `10⁶`). A class `(i, ℓ)` has its prime sums at most
`Q_j^{t_j}`, `t_j = min(β + w, τ(ℓ_j + 1))` (`β + w` at the cap), and at most as many characters as each prime sum
has at least `Q_j^{τℓ_j}`: by the `2k`-th moment, `C_k q^{momExp k s_j (τℓ_j)}` (`SieveTypeIIHM.card_Sp_large`). The
class's count exponent `γ` is the least of `g(β)` and these for `1 ≤ k ≤ k_max`, and `SieveTypeIIHM.bin_bound_exp`
bounds the class with the rest's exponent `Σ_j s_j(t_j − 1) + L − m` (the product of the scales is at most
`2^{K₀}q^L/P`). The condition on the exponents is `ResCond`, the large `k` being covered by `momExp_mono_k`.

* `ResCond g L K m s`: for the variable's exponent `m` and the rest's `s_0, …, s_{K−1}`, every `β ∈ [1/2, 11/12]`,
  `γ ≤ g(β)` and `t_j ≤ β + 4·10⁻⁶` with `γ ≤ momExp k s_j (t_j − 10⁻⁶)` for all `k ≥ 1` have
  `ResBinOK L (1/1000) (1/1000) (Σ_j s_j(t_j − 1) + L − m) γ m`.
* `typeII_res`, **Proposition 3′ for the resonant window, pointwise in the heights**: the conclusion of
  `typeII_gen_hm` for a curve with its counts, when `ResCond` holds at `m = log_q P` and `s_j = log_q Q_j`. The
  classes number `500000·(10⁶ + 1)^K`, a constant absorbed into `q^{1/100000}` as the bins are.

The file imports `SieveResBins.lean` and `SieveResCount.lean`.
-/
import SieveResBins
import SieveResCount

namespace SieveTypeIIHM

open Finset SieveTypeII SieveTypeIIGen

/-- **The resonant window's condition** at the variable's exponent `m` and the rest's exponents `s 0, …, s (K − 1)`,
for the curve `g` at `L`: every `β ∈ [1/2, 11/12]`, `γ ≤ g(β)` and sizes `t_j ≤ β + 4·10⁻⁶` whose prime sums' counts
allow `γ` (`γ ≤ momExp k s_j (t_j − 10⁻⁶)` for all `k ≥ 1`) fit `ResBinOK` with the rest's exponent
`Σ_j s_j(t_j − 1) + L − m`. -/
def ResCond (g : ℝ → ℝ) (L : ℝ) (K : ℕ) (m : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ (β γ : ℝ) (t : ℕ → ℝ), 1 / 2 ≤ β → β ≤ 11 / 12 → γ ≤ g β → (∀ j < K, t j ≤ β + 4 / 10 ^ 6) →
    (∀ j < K, ∀ k : ℕ, 1 ≤ k → γ ≤ momExp k (s j) (t j - 1 / 10 ^ 6)) →
    ResBinOK L (1 / 1000) (1 / 1000) (∑ j ∈ Finset.range K, s j * (t j - 1) + L - m) γ m

open scoped ContDiff in
/-- **Proposition 3′ for the resonant window, pointwise in the heights.** Hypotheses: a curve `g ≤ 1` (`hg1`) with
`g(1/2) = 1` (`hg0`) and its counts (`hcnt`), `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀ ≥ 0`,
`e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵` (`hη`, `hη1`). For large `q`, `S ⊆ (P, 2P]` with `P ≥ 1`, `K ≤ K₀` scales
`Q_j ≥ q^{e₁}` with heights `|h_j| ≤ q^η` and `∏_j Q_j ≤ 2^{K₀}q^L/P`, and `ResCond g L K (log_q P) (log_q Q_j)`:
`Σ_{χ≠1} |W(χ)|·|∏_j Sp(χ, Q_j, h_j)| ≤ q^{L−1/50000}(Σ|a|²/P)^{1/2}`. The proof: `sum_typeII_cls` with the
classes of the zeros' bin and the prime sums' levels, `bin_bound_exp` for each class, and the constants absorbed as
in `typeII_gen_hm`. -/
theorem typeII_res {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ η : ℝ}
    (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) → 0 < P →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / P →
      ResCond g L K (Real.logb q P) (fun j => Real.logb q (Q j)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) := by
  -- the parameters
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 10 ^ 6 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 1 + L := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℕ, Kd = ⌈5 * U / 12 / η⌉₊ := ⟨_, rfl⟩
  have hKdη : 5 * U / 12 ≤ η * Kd := by
    have h : 5 * U / 12 / η ≤ (Kd : ℝ) := hKd ▸ Nat.le_ceil (5 * U / 12 / η)
    rw [div_le_iff₀ hη] at h
    calc 5 * U / 12 ≤ (Kd : ℝ) * η := h
      _ = η * Kd := mul_comm _ _
  obtain ⟨Bc, Cc, hBc, hCc, hL1⟩ := SieveWeight.norm_Sp_le hf0 hsupp Kd
  obtain ⟨KLmax, hKLmax⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range 500001, Linnik.KL (βg i) (βg i + δ) := ⟨_, rfl⟩
  have hKLnn : ∀ i ≤ 500000, 0 ≤ Linnik.KL (βg i) (βg i + δ) := fun i hi =>
    (Linnik.KL_pos (by rw [hδ]; linarith) (by have := (βg_range hi).2; rw [hδ]; linarith)).le
  have hKLle : ∀ i ≤ 500000, Linnik.KL (βg i) (βg i + δ) ≤ KLmax := fun i hi => hKLmax ▸
    Finset.single_le_sum (f := fun i => Linnik.KL (βg i) (βg i + δ))
      (fun j hj => hKLnn j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (Finset.mem_range.2 (by omega))
  have hKLmax0 : 0 ≤ KLmax := (hKLnn 0 (by norm_num)).trans (hKLle 0 (by norm_num))
  -- `positivity` scans the hypotheses; the sum over `range 500001` would be unfolded there
  clear hKLmax
  obtain ⟨q₁, hMB⟩ := MB_le hBc hCc hKLmax0 (δ := δ) (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) he₁ hη
    (by linarith) hKdη
  obtain ⟨Cd, hCd0, hCd⟩ := hcnt
  obtain ⟨CK, hCK0, hCK⟩ := offK_bound
  -- the bound of `f0`, the moments' range and their constant
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : ℝ, ∀ u, |f0 u| ≤ F₀ := by
    have hc : HasCompactSupport f0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
    obtain ⟨C, hC⟩ := hf0.continuous.bounded_above_of_compact_support hc
    exact ⟨C, fun u => by simpa [Real.norm_eq_abs] using hC u⟩
  have hF00 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  obtain ⟨kmax, hkmax⟩ : ∃ k : ℕ, k = ⌈1 / e₁⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨Cm, hCm⟩ : ∃ C : ℝ, C = (2 ^ kmax + 1) * (kmax : ℝ) ^ kmax * (3 * F₀ ^ 2 + 1) ^ kmax := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  have hCmk : ∀ k : ℕ, 1 ≤ k → k ≤ kmax → (2 ^ k + 1) * (k : ℝ) ^ k * (3 * F₀ ^ 2) ^ k ≤ Cm := by
    intro k hk1 hk2
    rw [hCm]
    have hkk : (k : ℝ) ≤ kmax := by exact_mod_cast hk2
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have h1 : (2 : ℝ) ^ k + 1 ≤ 2 ^ kmax + 1 := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk2; linarith
    have h2 : (k : ℝ) ^ k ≤ (kmax : ℝ) ^ kmax :=
      (pow_le_pow_left₀ (by positivity) hkk k).trans (pow_le_pow_right₀ (by linarith) hk2)
    have h3 : (3 * F₀ ^ 2) ^ k ≤ (3 * F₀ ^ 2 + 1) ^ kmax :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans
        (pow_le_pow_right₀ (by nlinarith [sq_nonneg F₀]) hk2)
    exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
  obtain ⟨Cd', hCd'⟩ : ∃ C : ℝ, C = max (max Cd 1) Cm := ⟨_, rfl⟩
  have hCd'1 : max Cd 1 ≤ Cd' := hCd' ▸ le_max_left _ _
  have hCd'm : Cm ≤ Cd' := hCd' ▸ le_max_right _ _
  have hCd'0 : 0 ≤ Cd' := le_trans (le_trans zero_le_one (le_max_right Cd 1)) hCd'1
  -- the number of classes, and the constant
  obtain ⟨NC, hNC⟩ : ∃ N : ℕ, N = 500000 * (10 ^ 6 + 1) ^ K₀ := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * (2 ^ K₀ * 2 ^ K₀) *
      Real.sqrt Cd' + 3 * Real.sqrt (Real.exp 1) * (2 ^ K₀ * 2 ^ K₀) * Cd' * Real.sqrt CK * 2 :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1
    (LinnikTwelve.ev_log_pow (NC * C₁ * 3 ^ 10) (1 / 100000) 10 (by norm_num))
  have hev : ∀ᶠ q : ℕ in Filter.atTop, q₁ ≤ q ∧ (2 : ℝ) ^ K₀ ≤ q ∧ 4 ≤ (q : ℝ) ^ e₁ ∧ Q₂ ≤ (q : ℝ) ∧ 2 ≤ q :=
    (Filter.eventually_ge_atTop q₁).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop ((2 : ℝ) ^ K₀)).and
        ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4).and
          ((tendsto_natCast_atTop_atTop.eventually_ge_atTop Q₂).and (Filter.eventually_ge_atTop 2))))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q _ hq P S hS hPpos a h₀ K hK Q h hQh hprod hres => ?_⟩
  obtain ⟨hq₁, hq2K, hqe, hqQ₂, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hPge1 : (1 : ℝ) ≤ P := by exact_mod_cast hPpos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.logb q P := ⟨_, rfl⟩
  have hPm : (P : ℝ) = (q : ℝ) ^ m := by rw [hm]; exact (Real.rpow_logb hq0 hq1.ne' hP0).symm
  -- the heights
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (q : ℝ) ^ η := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := hH ▸ Real.one_le_rpow hq1.le hη.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * H + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hT3 : T ≤ 3 * (q : ℝ) ^ η := by rw [hT, ← hH]; linarith
  have hQh' : ∀ j < K, 4 ≤ Q j ∧ |h j| + H + 1 ≤ T := fun j hj =>
    ⟨hqe.trans (hQh j hj).1, by have := (hQh j hj).2; rw [hT, hH]; rw [hH] at hH1; linarith⟩
  -- each scale is at most `q^U`
  have hQ1 : ∀ j < K, 1 ≤ Q j := fun j hj => by linarith [(hQh' j hj).1]
  have hQU : ∀ j < K, Q j ≤ (q : ℝ) ^ U := by
    intro j hj
    have hjK : j ∈ Finset.range K := Finset.mem_range.2 hj
    have hrest : 1 ≤ ∏ k ∈ (Finset.range K).erase j, Q k := Finset.one_le_prod₀ fun k hk =>
      hQ1 k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
    have hQj := Finset.mul_prod_erase (Finset.range K) Q hjK
    have hQj0 : 0 ≤ Q j := by linarith [hQ1 j hj]
    have hqL : 0 ≤ (q : ℝ) ^ L := Real.rpow_nonneg hq0.le _
    calc Q j ≤ Q j * ∏ k ∈ (Finset.range K).erase j, Q k := le_mul_of_one_le_right hQj0 hrest
      _ = ∏ k ∈ Finset.range K, Q k := hQj
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L / P := hprod
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L := div_le_self (mul_nonneg (by norm_num) hqL) hPge1
      _ ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right hq2K hqL
      _ = (q : ℝ) ^ U := by rw [hU, Real.rpow_add hq0, Real.rpow_one]
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; norm_num
  -- the exponents of the scales
  set sv : ℕ → ℝ := fun j => Real.logb q (Q j) with hsv
  have hQs : ∀ j < K, Q j = (q : ℝ) ^ sv j := fun j hj =>
    (Real.rpow_logb hq0 hq1.ne' (by linarith [hQ1 j hj])).symm
  have hsve : ∀ j < K, e₁ ≤ sv j := fun j hj =>
    (Real.le_logb_iff_rpow_le hq1 (by linarith [hQ1 j hj])).2 (hQh j hj).1
  have hsv0 : ∀ j < K, 0 ≤ sv j := fun j hj => he₁.le.trans (hsve j hj)
  -- the kernel's bound at `Λ = 2P` (`offK_bound`)
  obtain ⟨Bk, hBk⟩ : ∃ B : ℝ, B = CK * (2 * (P : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := ⟨_, rfl⟩
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hKk : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑' n, LinnikPower.kTerm ψ (2 * (P : ℝ)) 0 n‖ ≤ Bk :=
    fun ψ hψ => by rw [hBk]; exact hCK q ψ hψ (2 * (P : ℝ)) (by linarith)
  have hBk' : Bk ≤ CK * (2 * (P : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) := by
    have e3 : (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) = 5 / 12 + 3 / 1000 := by norm_num
    rw [hBk, e3]
  -- the classes: the zeros' bin and the prime sums' levels
  -- (opaque names: unfolding `bin`'s `range 500000` must be avoided)
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin K → DirichletCharacter ℂ q → ℕ, lv = fun (j : Fin K) (χ : DirichletCharacter ℂ q) =>
      lev (10 ^ 6) (1 / 10 ^ 6) (Q j) ‖SieveWeight.Sp χ f0 (Q j) (h j)‖ := ⟨_, rfl⟩
  have hlvle : ∀ j χ, lv j χ ≤ 10 ^ 6 := fun j χ => by rw [hlv]; exact lev_le _ _ _ _
  obtain ⟨cl, hcl⟩ : ∃ cl : DirichletCharacter ℂ q → Fin 500000 × (Fin K → Fin (10 ^ 6 + 1)), cl = fun χ =>
      (⟨bin βg 500000 T χ, bin_lt (by norm_num) T χ⟩, fun j => ⟨lv j χ, Nat.lt_succ_of_le (hlvle j χ)⟩) :=
    ⟨_, rfl⟩
  have hcl1 : ∀ χ, ((cl χ).1 : ℕ) = bin βg 500000 T χ := fun χ => by rw [hcl]
  have hcl2 : ∀ χ j, ((cl χ).2 j : ℕ) = lv j χ := fun χ j => by rw [hcl]
  obtain ⟨bnd, hbnd⟩ : ∃ bnd : Fin K → ℕ → ℕ → ℝ, bnd = fun (j : Fin K) (i l : ℕ) =>
      if l < 10 ^ 6 then min (MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) (Q j ^ (1 / 10 ^ 6 * ((l : ℝ) + 1)))
      else MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Fin 500000 × (Fin K → Fin (10 ^ 6 + 1)) → ℝ,
      M = fun c => max (∏ j : Fin K, bnd j c.1 (c.2 j)) 0 := ⟨_, rfl⟩
  have hM0 : ∀ c, 0 ≤ M c := fun c => by rw [hM]; exact le_max_right _ _
  -- each prime sum within its class's bounds
  have hBχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤ M (cl χ) := by
    intro χ hχ
    have hb := bin_lt (β := βg) (by norm_num : 0 < 500000) T χ
    have hθ := βg_range (i := bin βg 500000 T χ + 1) (by omega)
    rw [hM]
    refine le_trans ?_ (le_max_left _ _)
    rw [norm_prod, ← Fin.prod_univ_eq_prod_range (fun j => ‖SieveWeight.Sp χ f0 (Q j) (h j)‖)]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
    have hj' := hQh' j j.isLt
    have hMBj : ‖SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤ MB q Bc Cc Kd (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j) :=
      hL1 q χ hχ (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j) hθ.1 hθ.2 hδ0 hδ1 (by linarith) hj'.1
        (bin_rect βg_top hχ (by norm_num) hj'.2)
    rw [hcl1, hcl2, hbnd]
    dsimp only
    split_ifs with hl
    · refine le_min hMBj ?_
      rw [hlv] at hl ⊢
      exact le_rpow_of_lev_lt (by norm_num) (by linarith [hj'.1]) (norm_nonneg _) hl
    · exact hMBj
  -- the bound by classes
  have hpt := sum_typeII_cls cl hPpos hS a h₀ (fun χ => ∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)) M
    hM0 hBχ hBk0 hKk
  refine hpt.trans ?_
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ m ∈ S, ‖a m‖ ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  -- each class
  have hcls : ∀ c : Fin 500000 × (Fin K → Fin (10 ^ 6 + 1)),
      M c * binTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c).card) P q V Bk ≤
        C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
    intro c
    obtain ⟨i, hic, hi'⟩ : ∃ i : ℕ, i = (c.1 : ℕ) ∧ i < 500000 := ⟨_, rfl, c.1.isLt⟩
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin K → ℕ, ℓ = fun j => ((c.2 j : Fin (10 ^ 6 + 1)) : ℕ) := ⟨_, rfl⟩
    have hℓle : ∀ j, ℓ j ≤ 10 ^ 6 := fun j => by rw [hℓ]; exact Nat.lt_succ_iff.1 (c.2 j).isLt
    have hβi := βg_range hi'.le
    have hβi1 := βg_range (Nat.succ_le_of_lt hi')
    have hw : βg (i + 1) + 2 * δ ≤ βg i + 4 / 10 ^ 6 := by rw [βg_succ, hδ]; linarith
    -- the sizes of the class's prime sums
    obtain ⟨t', ht'⟩ : ∃ t' : Fin K → ℝ, t' = fun j => if ℓ j < 10 ^ 6 then
        min (βg (i + 1) + 2 * δ) (1 / 10 ^ 6 * ((ℓ j : ℝ) + 1)) else βg (i + 1) + 2 * δ := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun j => if hj : j < K then t' ⟨j, hj⟩ else 0 := ⟨_, rfl⟩
    have htt : ∀ j : Fin K, t j = t' j := fun j => by rw [ht]; simp [j.isLt]
    have ht'le : ∀ j, t' j ≤ βg (i + 1) + 2 * δ := fun j => by
      rw [ht']; dsimp only; split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    -- the class's count exponent: the least of `g(β)` and the moments' exponents
    obtain ⟨Sjk, hSjk⟩ : ∃ T : Finset (Fin K × Fin kmax), T = Finset.univ.filter (fun jk => 1 ≤ ℓ jk.1) :=
      ⟨_, rfl⟩
    obtain ⟨fjk, hfjk⟩ : ∃ f : Fin K × Fin kmax → ℝ, f = fun jk =>
        momExp ((jk.2 : ℕ) + 1) (sv jk.1) (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) := ⟨_, rfl⟩
    obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = Sjk.fold min (g (βg i)) fjk := ⟨_, rfl⟩
    have hγle := (Finset.le_fold_min (s := Sjk) (b := g (βg i)) (f := fjk) γ).1 (le_of_eq hγ)
    have hγg : γ ≤ g (βg i) := hγle.1
    have hγf : ∀ jk ∈ Sjk, γ ≤ fjk jk := hγle.2
    have hγ1 : γ ≤ 1 := hγg.trans (hg1 _)
    -- the class's bound on the prime sums
    have hMc : M c = max (∏ j : Fin K, bnd j i (ℓ j)) 0 := by rw [hM, hic, hℓ]
    have hbnd0 : ∀ j : Fin K, 0 ≤ bnd j i (ℓ j) := by
      intro j
      have hMB0 : 0 ≤ MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j) :=
        MB_nonneg hBc hCc hβi1.2 hδ0 hδ1 (by linarith) (by linarith [(hQh' j j.isLt).1])
      rw [hbnd]; dsimp only; split_ifs
      · exact le_min hMB0 (Real.rpow_nonneg (by linarith [hQ1 j j.isLt]) _)
      · exact hMB0
    have hbnd2 : ∀ j : Fin K, bnd j i (ℓ j) ≤ 2 * Q j ^ t' j := by
      intro j
      have hQj0 : (0 : ℝ) ≤ Q j := by linarith [hQ1 j j.isLt]
      have hMBle : MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j) ≤ 2 * Q j ^ (βg (i + 1) + 2 * δ) := by
        rw [hH]
        exact hMB q hq₁ _ _ _ hβi1.1 hβi1.2 (hKLle (i + 1) (by omega)) (hQh j j.isLt).1 (hQU j j.isLt)
          (hQh j j.isLt).2
      rw [hbnd, ht']; dsimp only
      split_ifs with hl
      · rcases le_total (βg (i + 1) + 2 * δ) (1 / 10 ^ 6 * ((ℓ j : ℝ) + 1)) with hle | hle
        · rw [min_eq_left hle]; exact (min_le_left _ _).trans hMBle
        · rw [min_eq_right hle]
          have h0 := Real.rpow_nonneg hQj0 (1 / 10 ^ 6 * ((ℓ j : ℝ) + 1))
          have h1 := min_le_right (MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) (Q j ^ (1 / 10 ^ 6 * ((ℓ j : ℝ) + 1)))
          linarith
      · exact hMBle
    have hQt : ∏ j : Fin K, Q j ^ t' j = (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * t j) := by
      rw [Real.rpow_sum_of_pos hq0, ← Fin.prod_univ_eq_prod_range (fun j => (q : ℝ) ^ (sv j * t j))]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [htt j, Real.rpow_mul hq0.le, ← hQs j j.isLt]
    have hQsum : (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j) = ∏ j ∈ Finset.range K, Q j := by
      rw [Real.rpow_sum_of_pos hq0]
      exact Finset.prod_congr rfl fun j hj => (hQs j (Finset.mem_range.1 hj)).symm
    have hsplit : ∑ j ∈ Finset.range K, sv j * t j =
        (∑ j ∈ Finset.range K, sv j * (t j - 1)) + ∑ j ∈ Finset.range K, sv j := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    have hqLm : (q : ℝ) ^ L / P = (q : ℝ) ^ (L - m) := by rw [hPm, ← Real.rpow_sub hq0]
    have hprodQ0 : 0 ≤ ∏ j ∈ Finset.range K, Q j :=
      Finset.prod_nonneg fun j hj => by linarith [hQ1 j (Finset.mem_range.1 hj)]
    have hMp : M c ≤ (2 ^ K₀ * 2 ^ K₀) * (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1) + L - m) := by
      rw [hMc]
      refine max_le ?_ (by positivity)
      have h2K : (2 : ℝ) ^ K ≤ 2 ^ K₀ := pow_le_pow_right₀ (by norm_num) hK
      have hX0 : 0 ≤ (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1)) := Real.rpow_nonneg hq0.le _
      have e2 : (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1) + L - m) =
          (q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1)) * ((q : ℝ) ^ L / P) := by
        rw [hqLm, ← Real.rpow_add hq0, add_sub_assoc]
      rw [e2]
      calc ∏ j : Fin K, bnd j i (ℓ j) ≤ ∏ j : Fin K, (2 * Q j ^ t' j) :=
            Finset.prod_le_prod₀ (fun j _ => hbnd0 j) fun j _ => hbnd2 j
        _ = 2 ^ K * ∏ j : Fin K, Q j ^ t' j := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = 2 ^ K * ((q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1)) * ∏ j ∈ Finset.range K, Q j) := by
            rw [hQt, hsplit, Real.rpow_add hq0, hQsum]
        _ ≤ 2 ^ K₀ * ((q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1)) * (2 ^ K₀ * (q : ℝ) ^ L / P)) :=
            mul_le_mul h2K (mul_le_mul_of_nonneg_left hprod hX0) (mul_nonneg hX0 hprodQ0) (by positivity)
        _ = (2 ^ K₀ * 2 ^ K₀) * ((q : ℝ) ^ (∑ j ∈ Finset.range K, sv j * (t j - 1)) * ((q : ℝ) ^ L / P)) := by
            ring
    -- the class's count
    have hqT1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1.le hT1
    have hl10 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith [Real.log_nonneg hqT1])
    have hcnt' : ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c).card : ℝ) ≤
        Cd' * ((q : ℝ) * T) ^ γ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
      rcases (Finset.fold_min_le (s := Sjk) (b := g (βg i)) (f := fjk) γ).1 (le_of_eq hγ.symm) with hgγ |
        ⟨jk, hjkS, hjkγ⟩
      · -- the zeros' bin
        have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c) ⊆
            (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin βg 500000 T χ = i) := by
          intro χ hχ
          obtain ⟨hχ1, hχc⟩ := (Finset.mem_filter.1 hχ).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hχ1, ?_⟩
          rw [← hcl1 χ, hχc, hic]
        have hbin := card_bin_gen hg0 (q := q) (β := βg) (N := 500000) (by norm_num) βg_zero
          (fun k hk => ⟨(βg_range hk.le).1, by linarith [(βg_range hk.le).2]⟩) hT2
          (fun σ h1 h2 => hCd q σ T h1 h2 hT2) hi'
        have hpow : ((q : ℝ) * T) ^ g (βg i) ≤ ((q : ℝ) * T) ^ γ := Real.rpow_le_rpow_of_exponent_le hqT1 hgγ
        calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c).card : ℝ)
            ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin βg 500000 T χ = i).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ max Cd 1 * ((q : ℝ) * T) ^ g (βg i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hbin
          _ ≤ Cd' * ((q : ℝ) * T) ^ γ * (1 + Real.log ((q : ℝ) * T)) ^ 10 :=
              mul_le_mul_of_nonneg_right (mul_le_mul hCd'1 hpow (Real.rpow_nonneg (by linarith) _) hCd'0)
                (by linarith)
      · -- a prime sum at least `Q_j^{τℓ_j}`: its moment
        rw [hSjk] at hjkS
        have hℓ1 : 1 ≤ ℓ jk.1 := (Finset.mem_filter.1 hjkS).2
        have hQj1 : 1 < Q jk.1 := by linarith [(hQh' jk.1 jk.1.isLt).1]
        have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c) ⊆
            (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
              Q jk.1 ^ (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) ≤ ‖SieveWeight.Sp χ f0 (Q jk.1) (h jk.1)‖) := by
          intro χ hχ
          obtain ⟨-, hχc⟩ := (Finset.mem_filter.1 hχ).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          have hlev : lev (10 ^ 6) (1 / 10 ^ 6) (Q jk.1) ‖SieveWeight.Sp χ f0 (Q jk.1) (h jk.1)‖ = ℓ jk.1 := by
            have h1 := hcl2 χ jk.1
            rw [hχc, hlv] at h1
            rw [hℓ]; exact h1.symm
          have h2 := rpow_le_of_one_le_lev (N := 10 ^ 6) (by norm_num : (0 : ℝ) < 1 / 10 ^ 6) hQj1 (norm_nonneg _)
            (x := ‖SieveWeight.Sp χ f0 (Q jk.1) (h jk.1)‖) (by rw [hlev]; exact hℓ1)
          rwa [hlev] at h2
        have hu1 : 1 / 10 ^ 6 * (ℓ jk.1 : ℝ) ≤ 1 := by
          have : (ℓ jk.1 : ℝ) ≤ 10 ^ 6 := by exact_mod_cast hℓle jk.1
          calc 1 / 10 ^ 6 * (ℓ jk.1 : ℝ) ≤ 1 / 10 ^ 6 * 10 ^ 6 := mul_le_mul_of_nonneg_left this (by norm_num)
            _ = 1 := by norm_num
        have hk1 : 1 ≤ (jk.2 : ℕ) + 1 := by omega
        have hkm : (jk.2 : ℕ) + 1 ≤ kmax := jk.2.isLt
        have hlarge := card_Sp_large (q := q) hq1 hF₀ (Q := Q jk.1) hQj1.le (h jk.1) hk1 (1 / 10 ^ 6 * (ℓ jk.1 : ℝ))
        have hfj : fjk jk = momExp ((jk.2 : ℕ) + 1) (sv jk.1) (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) := by rw [hfjk]
        have hγ0 : 0 ≤ γ := le_trans (momExp_nonneg (hsv0 jk.1 jk.1.isLt) hu1) (hfj ▸ hjkγ)
        have hqγ : (q : ℝ) ^ momExp ((jk.2 : ℕ) + 1) (sv jk.1) (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) ≤ ((q : ℝ) * T) ^ γ :=
          (Real.rpow_le_rpow_of_exponent_le hq1.le (hfj ▸ hjkγ)).trans
            (Real.rpow_le_rpow hq0.le (le_mul_of_one_le_right hq0.le hT1) hγ0)
        have hCk := hCmk ((jk.2 : ℕ) + 1) hk1 hkm
        have hqTγ0 : 0 ≤ ((q : ℝ) * T) ^ γ := Real.rpow_nonneg (by linarith) _
        calc ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = c).card : ℝ)
            ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
                Q jk.1 ^ (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) ≤ ‖SieveWeight.Sp χ f0 (Q jk.1) (h jk.1)‖).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ (2 ^ ((jk.2 : ℕ) + 1) + 1) * (((jk.2 : ℕ) + 1 : ℕ) : ℝ) ^ ((jk.2 : ℕ) + 1) *
                (3 * F₀ ^ 2) ^ ((jk.2 : ℕ) + 1) *
                (q : ℝ) ^ momExp ((jk.2 : ℕ) + 1) (sv jk.1) (1 / 10 ^ 6 * (ℓ jk.1 : ℝ)) := hlarge
          _ ≤ Cm * ((q : ℝ) * T) ^ γ := mul_le_mul hCk hqγ (Real.rpow_nonneg hq0.le _) hCm0
          _ ≤ Cd' * ((q : ℝ) * T) ^ γ * 1 := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hCd'm hqTγ0
          _ ≤ Cd' * ((q : ℝ) * T) ^ γ * (1 + Real.log ((q : ℝ) * T)) ^ 10 :=
              mul_le_mul_of_nonneg_left hl10 (mul_nonneg hCd'0 hqTγ0)
    -- the condition at the class
    have hok : ResBinOK L (1 / 1000) (1 / 1000) (∑ j ∈ Finset.range K, sv j * (t j - 1) + L - m) γ m := by
      rw [hm]
      refine hres (βg i) γ t hβi.1 hβi.2 hγg (fun j hj => ?_) (fun j hj k hk => ?_)
      · rw [htt ⟨j, hj⟩]; exact (ht'le _).trans hw
      · have htj : t j = t' ⟨j, hj⟩ := htt ⟨j, hj⟩
        rw [htj]
        have hsvj : 0 ≤ sv j := hsv0 j hj
        show γ ≤ momExp k (sv j) (t' ⟨j, hj⟩ - 1 / 10 ^ 6)
        by_cases hl0 : ℓ ⟨j, hj⟩ = 0
        · have ht0 : t' ⟨j, hj⟩ ≤ 1 / 10 ^ 6 := by
            rw [ht']; dsimp only; rw [ite_eq_left (by rw [hl0]; norm_num), hl0]
            exact (min_le_right _ _).trans (by norm_num)
          exact hγg.trans ((hg1 _).trans (one_le_momExp hsvj (by linarith)))
        · have hl1 : 1 ≤ ℓ ⟨j, hj⟩ := Nat.one_le_iff_ne_zero.2 hl0
          have hu1 : 1 / 10 ^ 6 * (ℓ ⟨j, hj⟩ : ℝ) ≤ 1 := by
            have : (ℓ ⟨j, hj⟩ : ℝ) ≤ 10 ^ 6 := by exact_mod_cast hℓle ⟨j, hj⟩
            calc 1 / 10 ^ 6 * (ℓ ⟨j, hj⟩ : ℝ) ≤ 1 / 10 ^ 6 * 10 ^ 6 :=
                  mul_le_mul_of_nonneg_left this (by norm_num)
              _ = 1 := by norm_num
          have htu : t' ⟨j, hj⟩ - 1 / 10 ^ 6 ≤ 1 / 10 ^ 6 * (ℓ ⟨j, hj⟩ : ℝ) := by
            rw [ht']; dsimp only; split_ifs with hl
            · have := min_le_right (βg (i + 1) + 2 * δ) (1 / 10 ^ 6 * ((ℓ ⟨j, hj⟩ : ℝ) + 1))
              linarith only [this]
            · have hN : ℓ ⟨j, hj⟩ = 10 ^ 6 := le_antisymm (hℓle _) (not_lt.1 hl)
              have hβ1 := hβi1.2
              rw [hN, hδ]; push_cast; linarith only [hβ1]
          refine le_trans ?_ (momExp_anti hsvj htu)
          -- `γ ≤ momExp k s (τℓ)`: for `k ≤ k_max` by the class's exponent, beyond from `k₀ = ⌈1/s⌉`
          have hmem : ∀ k' : ℕ, 1 ≤ k' → k' ≤ kmax → γ ≤ momExp k' (sv j) (1 / 10 ^ 6 * (ℓ ⟨j, hj⟩ : ℝ)) := by
            intro k' hk'1 hk'2
            have hin : ((⟨j, hj⟩ : Fin K), (⟨k' - 1, by omega⟩ : Fin kmax)) ∈ Sjk := by
              rw [hSjk]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hl1⟩
            have h1 := hγf _ hin
            rw [hfjk] at h1
            simp only at h1
            rwa [Nat.sub_add_cancel hk'1] at h1
          by_cases hkk : k ≤ kmax
          · exact hmem k hk hkk
          · have hsvpos : 0 < sv j := he₁.trans_le (hsve j hj)
            obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈1 / sv j⌉₊ := ⟨_, rfl⟩
            have hk₀1 : 1 ≤ (k₀ : ℝ) * sv j := by
              have h1 : 1 / sv j ≤ k₀ := hk₀ ▸ Nat.le_ceil _
              rw [div_le_iff₀ hsvpos] at h1; linarith
            have hk₀pos : 1 ≤ k₀ := by
              rcases Nat.eq_zero_or_pos k₀ with h0 | h0
              · rw [h0] at hk₀1; simp at hk₀1; linarith
              · exact h0
            have hk₀max : k₀ ≤ kmax := by
              have h1 : 1 / sv j ≤ 1 / e₁ := one_div_le_one_div_of_le he₁ (hsve j hj)
              have h2 : k₀ ≤ ⌈1 / e₁⌉₊ := hk₀ ▸ Nat.ceil_le_ceil h1
              omega
            exact (hmem k₀ hk₀pos hk₀max).trans (momExp_mono_k hsvj hu1 hk₀1 (by omega))
    -- the class's bound
    have hb := bin_bound_exp (V := V) (L := L) (d := 1 / 1000) (e := 1 / 1000) (by norm_num) hq1 hPm hT1 hT3 hη.le
      hγ1 (by positivity : (0 : ℝ) ≤ 2 ^ K₀ * 2 ^ K₀) hCd'0 hCK0.le hMp (hM0 c) hcnt' (Nat.cast_nonneg _) hBk'
      hBk0 hok
    rw [hC₁]
    exact hb
  refine (Finset.sum_le_sum fun c _ => hcls c).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  have hNCK : ((500000 * (10 ^ 6 + 1) ^ K : ℕ) : ℝ) ≤ NC := by
    rw [hNC]
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hK)
  -- absorbing the constants
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1.le
  have hlogT : 1 + Real.log ((q : ℝ) * T) ≤ 3 * (1 + Real.log q) := by
    have hT0 : 0 < T := by linarith
    have h1 : Real.log ((q : ℝ) * T) = Real.log q + Real.log T := Real.log_mul hq0.ne' hT0.ne'
    have h2 : Real.log T ≤ Real.log 3 + η * Real.log q := by
      rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hq0 η).ne']
      exact Real.log_le_log hT0 hT3
    have h3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h4 : η * Real.log q ≤ Real.log q := by
      have : η ≤ 1 := by linarith
      exact mul_le_of_le_one_left hlq this
    linarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * T := mul_le_mul hq1.le hT1 zero_le_one hq0.le
  have hlq0 : 0 ≤ 1 + Real.log ((q : ℝ) * T) := by linarith [Real.log_nonneg hqT1]
  have habs : NC * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := by
    have h := hQ₂ (q : ℝ) hqQ₂
    calc (NC : ℝ) * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ NC * C₁ * (3 * (1 + Real.log q)) ^ 10 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq0 hlogT 10)
            (mul_nonneg (Nat.cast_nonneg _) hC₁0)
      _ = NC * C₁ * 3 ^ 10 * (1 + Real.log q) ^ 10 := by ring
      _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := h
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  have hE : 0 ≤ (q : ℝ) ^ (L - 1 / 25000 + η) := Real.rpow_nonneg hq0.le _
  have hfin : (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) ≤ (q : ℝ) ^ (L - 1 / 50000) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  have hC : 0 ≤ C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₁0 (pow_nonneg hlq0 10)) hE) hVP
  calc ((500000 * (10 ^ 6 + 1) ^ K : ℕ) : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 *
        (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P))
      ≤ (NC : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) *
          Real.sqrt (V / P)) := mul_le_mul_of_nonneg_right hNCK hC
    _ = (NC : ℝ) * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 *
        (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by ring
    _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hE) hVP
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt (V / P) :=
        mul_le_mul_of_nonneg_right hfin hVP

end SieveTypeIIHM

#print axioms SieveTypeIIHM.typeII_res
