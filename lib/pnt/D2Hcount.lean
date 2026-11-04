import Mathlib
import D2GS

/-!
# Quantitative `Hcount`: fundamental discriminants coprime to `r`, with an explicit error

Unconditional. `GSHcount.hcount_pos`, `GSHcount.hcount_neg`: for `r ≥ 1` and every `x`,
`|#{d < x : Q d} − (3/π²)∏_{p∣r} p/(p+1)·x| ≤ (16r + 3)(√x + 1)`, where `Q d` (`GSDens.Q CpPos r`, resp. `CpNeg`)
says that `d` (resp. `−d`) is a fundamental discriminant coprime to `r` (`GSLink.fundPos_iff`).

Proof: `[no odd square divides d] = Σ_{e odd, e² ∣ d} μ(e)` (`sum_w`, from `SquarefreeCount.sum_sq_dvd_moebius` at
the odd part); for each `e ≤ √x` the `d = e²k` are counted by a condition on `k` periodic mod `16r` (`term_bound`, error
`16r + 1`); the `e > √x` cost `x Σ_{e>√x} 1/e² ≤ 2(√x + 1)` (`tail_le`). The constant `κ = Σ μ(e)ρ_e/e²` is then
identified with `(3/π²)∏ p/(p+1)` through the density `GSNu.delta_pos_closed` (`kappa_eq`).
See `formalisations/d2-density.md`.
-/

namespace GSHcount
open Finset GSDens GSLink GSRatio GSDelta GSNu GSUncond

open Classical

/-- `Cp (d mod 16)` and `gcd(d, r) = 1`. -/
def A (Cp : ℕ → Prop) (r d : ℕ) : Prop := Cp (d % 16) ∧ Nat.Coprime d r

theorem A_periodic (Cp : ℕ → Prop) (r : ℕ) : Function.Periodic (A Cp r) (16 * r) := by
  intro d
  unfold A
  have h16 : (d + 16 * r) % 16 = d % 16 := by
    rw [Nat.add_mul_mod_self_left]
  rw [h16, show 16 * r = 16 * r by rfl]
  rw [show d + 16 * r = d + 16 * r by rfl, Nat.coprime_add_mul_right_left d r 16]

/-- `w(e) = μ(e)` for odd `e`, else `0`. -/
noncomputable def w (e : ℕ) : ℝ := if Odd e then (ArithmeticFunction.moebius e : ℝ) else 0

theorem Odf_iff_odd_part (d : ℕ) : ∀ v m, d = 2 ^ v * m → (Odf d ↔ Odf m) := by
  intro v
  induction v generalizing d with
  | zero => intro m h; rw [h]; simp
  | succ v ih =>
    intro m h
    rw [h, pow_succ', mul_assoc, Odf_two]
    exact ih _ m rfl

/-- `Σ_{e ≤ E, e odd, e² ∣ d} μ(e) = [Odf d]` for `0 < d`, `d ≤ E²`. -/
theorem sum_w (d E : ℕ) (hd : 0 < d) (hdE : ∀ e, e * e ≤ d → e ≤ E) :
    ∑ e ∈ range (E + 1), (if e ^ 2 ∣ d then w e else 0) = if Odf d then 1 else 0 := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  have hm0 : 0 < m := hm.pos
  have key := SquarefreeCount.sum_sq_dvd_moebius hm0
  rw [Odf_iff_odd_part _ v m rfl]
  have hsq : Squarefree m ↔ Odf m := by
    rw [sqf_iff]; constructor
    · exact fun h => h.2
    · intro h; refine ⟨fun h4 => ?_, h⟩
      have : 2 ∣ m := dvd_trans (by norm_num) h4
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)
  rw [← hsq]
  refine Eq.trans ?_ (by convert key)
  unfold w
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_congr
  · ext e
    simp only [mem_filter, mem_Ioc, mem_range]
    constructor
    · rintro ⟨⟨he0, hem⟩, hdv⟩
      have heo : Odd e := by
        rcases Nat.even_or_odd e with h | h
        · exfalso
          have : 2 ∣ m := dvd_trans (dvd_trans (even_iff_two_dvd.1 h) (dvd_pow_self e two_ne_zero)) hdv
          exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)
        · exact h
      have hd' : e ^ 2 ∣ 2 ^ v * m := Dvd.dvd.mul_left hdv _
      have hle : e ≤ E := hdE e (by have := Nat.le_of_dvd (by positivity) hd'; nlinarith)
      refine ⟨⟨by omega, hd'⟩, heo⟩
    · rintro ⟨⟨heE, hdv⟩, heo⟩
      have hc : Nat.Coprime (e ^ 2) (2 ^ v) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_two_right).2 heo)
      have hem : e ^ 2 ∣ m := hc.dvd_of_dvd_mul_left hdv
      have he0 : 0 < e := heo.pos
      refine ⟨⟨he0, ?_⟩, hem⟩
      have := Nat.le_of_dvd hm0 hem
      nlinarith
  · intro e he
    simp only [mem_filter] at he
    simp

theorem count_Q_eq (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r x : ℕ) :
    (Nat.count (Q Cp r) x : ℝ) =
      ∑ e ∈ range (Nat.sqrt x + 1), w e * Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x := by
  simp only [Nat.count_eq_card_filter_range, natCast_card_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [mem_range] at hd
  by_cases hA : A Cp r d
  · have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd hA.1 (by simpa using hC0)
      · exact h
    have := sum_w d (Nat.sqrt x) hd0 (fun e he => Nat.le_sqrt.2 (by omega))
    have hQ : Q Cp r d ↔ Odf d := ⟨fun h => h.2.2, fun h => ⟨hA.1, hA.2, h⟩⟩
    simp only [hQ, hA, true_and]
    rw [← this]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  · have hQ : ¬ Q Cp r d := fun h => hA ⟨h.1, h.2.1⟩
    simp [hQ, hA]

/-- `B_e(k) = A(e²k)`. -/
def Be (Cp : ℕ → Prop) (r e k : ℕ) : Prop := A Cp r (e ^ 2 * k)

/-- The density `ρ_e` of `B_e`. -/
noncomputable def rho (Cp : ℕ → Prop) (r e : ℕ) : ℝ := (Nat.count (Be Cp r e) (16 * r) : ℝ) / (16 * r : ℕ)

theorem rho_nonneg (Cp : ℕ → Prop) (r e : ℕ) : 0 ≤ rho Cp r e := by unfold rho; positivity

theorem rho_le_one (Cp : ℕ → Prop) (r e : ℕ) : rho Cp r e ≤ 1 := by
  unfold rho
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [div_le_one (by positivity)]; exact_mod_cast Nat.count_le _

theorem w_abs_le (e : ℕ) : |w e| ≤ 1 := by
  unfold w; split_ifs
  · have := ArithmeticFunction.abs_moebius_le_one (n := e)
    exact_mod_cast this
  · simp

/-- **One `e`.** `|#{d < x : A d, e² ∣ d} − ρ_e x/e²| ≤ 16r + 1`. -/
theorem term_bound (Cp : ℕ → Prop) (r : ℕ) (hr : 0 < r) (e : ℕ) (he : 0 < e) (x : ℕ) :
    |(Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) - x * rho Cp r e / (e ^ 2 : ℝ)| ≤ 16 * r + 1 := by
  have he2 : 0 < e ^ 2 := by positivity
  have hdil : Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x = Nat.count (Be Cp r e) ((x + e ^ 2 - 1) / e ^ 2) := by
    convert count_dilate (fun d => A Cp r d ∧ e ^ 2 ∣ d) (Be Cp r e) (e ^ 2) he2 (fun d => by
      unfold Be
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, by rwa [Nat.mul_div_cancel' h2]⟩
      · rintro ⟨h2, h1⟩; exact ⟨by rwa [Nat.mul_div_cancel' h2] at h1, h2⟩) x
  have hper : Function.Periodic (Be Cp r e) (16 * r) := by
    intro k
    unfold Be
    rw [mul_add]
    exact (A_periodic Cp r).nat_mul (e ^ 2) _
  set y := (x + e ^ 2 - 1) / e ^ 2 with hy
  have hp := periodic_dens (Be Cp r e) (16 * r) (by omega) hper y
  have hy1 : (x : ℝ) ≤ y * (e ^ 2 : ℝ) := by
    have : x ≤ y * e ^ 2 := by
      rw [hy]
      have h1 := Nat.div_add_mod (x + e ^ 2 - 1) (e ^ 2)
      have h2 := Nat.mod_lt (x + e ^ 2 - 1) he2
      rw [mul_comm] at h1
      generalize (x + e ^ 2 - 1) / e ^ 2 * e ^ 2 = Z at h1 ⊢
      generalize (x + e ^ 2 - 1) % e ^ 2 = R at h1 h2
      generalize e ^ 2 = P at h1 h2 he2 ⊢
      omega
    exact_mod_cast this
  have hy2 : (y : ℝ) * (e ^ 2 : ℝ) ≤ x + e ^ 2 := by
    have : y * e ^ 2 ≤ x + e ^ 2 := by
      rw [hy]
      have := Nat.div_mul_le_self (x + e ^ 2 - 1) (e ^ 2)
      omega
    exact_mod_cast this
  have he2r : (0:ℝ) < (e:ℝ) ^ 2 := by positivity
  have hyx : |(y : ℝ) - x / (e:ℝ) ^ 2| ≤ 1 := by
    have : (y : ℝ) - x / (e:ℝ) ^ 2 = ((y:ℝ) * (e:ℝ) ^ 2 - x) / (e:ℝ) ^ 2 := by field_simp
    rw [this, abs_le]; constructor
    · rw [le_div_iff₀ he2r]; nlinarith
    · rw [div_le_iff₀ he2r]; nlinarith
  have hρ0 := rho_nonneg Cp r e
  have hρ1 := rho_le_one Cp r e
  rw [hdil]
  have e1 : (Nat.count (Be Cp r e) y : ℝ) - x * rho Cp r e / (e:ℝ) ^ 2 =
      ((Nat.count (Be Cp r e) y : ℝ) - y * rho Cp r e) + (y - x / (e:ℝ) ^ 2) * rho Cp r e := by ring
  have hp' : |(Nat.count (Be Cp r e) y : ℝ) - y * rho Cp r e| ≤ 16 * r := by
    unfold rho; push_cast at hp ⊢; exact hp
  have h2 : |((y:ℝ) - x / (e:ℝ) ^ 2) * rho Cp r e| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]; nlinarith [abs_nonneg ((y:ℝ) - x / (e:ℝ) ^ 2)]
  rw [e1]
  exact (abs_add_le _ _).trans (add_le_add hp' h2)

/-- `f(e) = w(e)ρ_e/e²`. -/
noncomputable def f (Cp : ℕ → Prop) (r e : ℕ) : ℝ := w e * rho Cp r e / (e : ℝ) ^ 2

theorem f_abs_le (Cp : ℕ → Prop) (r e : ℕ) : |f Cp r e| ≤ ((e : ℝ) ^ 2)⁻¹ := by
  unfold f
  rw [abs_div, abs_mul, abs_of_nonneg (rho_nonneg Cp r e), abs_of_nonneg (by positivity : (0:ℝ) ≤ (e:ℝ) ^ 2),
    div_eq_mul_inv]
  have h1 := w_abs_le e
  have h2 := rho_le_one Cp r e
  have h3 := rho_nonneg Cp r e
  have h4 : (0:ℝ) ≤ ((e:ℝ) ^ 2)⁻¹ := by positivity
  have : |w e| * rho Cp r e ≤ 1 := by nlinarith [abs_nonneg (w e)]
  nlinarith

theorem f_summable (Cp : ℕ → Prop) (r : ℕ) : Summable (f Cp r) :=
  Summable.of_norm_bounded (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
    (fun e => by rw [Real.norm_eq_abs]; exact f_abs_le Cp r e)

/-- `κ = Σ_e w(e)ρ_e/e²`. -/
noncomputable def kappa (Cp : ℕ → Prop) (r : ℕ) : ℝ := ∑' e, f Cp r e

theorem tail_le (Cp : ℕ → Prop) (r E : ℕ) :
    |kappa Cp r - ∑ e ∈ range (E + 1), f Cp r e| ≤ 2 / (E + 1) := by
  have hs := f_summable Cp r
  have hsplit := hs.sum_add_tsum_nat_add (E + 1)
  unfold kappa
  rw [← hsplit, add_sub_cancel_left]
  have hg : Summable (fun i : ℕ => (((i + (E + 1) : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (E + 1)).2
      (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
  have hn : Summable (fun i => ‖f Cp r (i + (E + 1))‖) := ((summable_nat_add_iff (f := f Cp r) (E + 1)).2 hs).norm
  calc |∑' i, f Cp r (i + (E + 1))| = ‖∑' i, f Cp r (i + (E + 1))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖f Cp r (i + (E + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i : ℕ, (((i + (E + 1) : ℕ) : ℝ) ^ 2)⁻¹ :=
        hn.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact f_abs_le Cp r _) hg
    _ ≤ 2 / (E + 1) := by
        refine hg.tsum_le_of_sum_range_le fun n => ?_
        have h := sum_Ioo_inv_sq_le (α := ℝ) E (E + 1 + n)
        rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range,
          show E + 1 + n - (E + 1) = n by omega] at h
        calc ∑ i ∈ range n, (((i + (E + 1) : ℕ) : ℝ) ^ 2)⁻¹
            = ∑ k ∈ range n, ((((E + 1 + k : ℕ)) : ℝ) ^ 2)⁻¹ :=
              sum_congr rfl fun i _ => by rw [add_comm i]
          _ ≤ 2 / (E + 1) := h

/-- **Quantitative count.** `|#{d < x : Q d} − κ x| ≤ (16r + 3)(√x + 1)`. -/
theorem count_bound (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r : ℕ) (hr : 0 < r) (x : ℕ) :
    |(Nat.count (Q Cp r) x : ℝ) - kappa Cp r * x| ≤ (16 * r + 3) * (Real.sqrt x + 1) := by
  set E := Nat.sqrt x
  have hE : (E : ℝ) ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
  have hxE : (x : ℝ) ≤ (E + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' x
    exact_mod_cast this.le
  rw [count_Q_eq Cp hC0 r x]
  have e1 : ∑ e ∈ range (E + 1), w e * (Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) - kappa Cp r * x =
      ∑ e ∈ range (E + 1), w e * ((Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) - x * rho Cp r e / (e:ℝ) ^ 2)
        - (kappa Cp r - ∑ e ∈ range (E + 1), f Cp r e) * x := by
    have hs : ∑ e ∈ range (E + 1), w e * ((Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) -
        x * rho Cp r e / (e:ℝ) ^ 2) = ∑ e ∈ range (E + 1), w e * (Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ)
          - ∑ e ∈ range (E + 1), f Cp r e * x := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun e _ => by unfold f; ring
    rw [hs, sub_mul, sum_mul]; ring
  rw [e1]
  have h1 : |∑ e ∈ range (E + 1), w e * ((Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) -
      x * rho Cp r e / (e:ℝ) ^ 2)| ≤ (E + 1) * (16 * r + 1) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ e ∈ range (E + 1), |w e * ((Nat.count (fun d => A Cp r d ∧ e ^ 2 ∣ d) x : ℝ) -
        x * rho Cp r e / (e:ℝ) ^ 2)| ≤ 16 * r + 1 := by
      intro e _
      rw [abs_mul]
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp [w]; positivity
      · exact (mul_le_of_le_one_left (abs_nonneg _) (w_abs_le e)).trans (term_bound Cp r hr e he x)
    refine (sum_le_sum this).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]; push_cast; rfl
  have h2 : |(kappa Cp r - ∑ e ∈ range (E + 1), f Cp r e) * x| ≤ 2 * (E + 1) := by
    rw [abs_mul, Nat.abs_cast]
    have ht := tail_le Cp r E
    have hE1 : (0:ℝ) < E + 1 := by positivity
    calc _ ≤ 2 / ((E:ℝ) + 1) * (x:ℝ) := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg x)
      _ ≤ 2 / ((E:ℝ) + 1) * ((E:ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hxE (by positivity)
      _ = 2 * ((E:ℝ) + 1) := by field_simp
  calc _ ≤ _ := abs_sub _ _
    _ ≤ ((E:ℝ) + 1) * (16 * (r:ℝ) + 1) + 2 * ((E:ℝ) + 1) := add_le_add h1 h2
    _ = ((E:ℝ) + 1) * (16 * (r:ℝ) + 3) := by ring
    _ ≤ (Real.sqrt x + 1) * (16 * (r:ℝ) + 3) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

open Filter Topology in
theorem tendsto_of_bound (g : ℕ → ℝ) (κ C : ℝ) (h : ∀ x : ℕ, |g x - κ * x| ≤ C * (Real.sqrt x + 1)) :
    Tendsto (fun x : ℕ => g x / x) atTop (𝓝 κ) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 0); simp at this; linarith
  have hs : Tendsto (fun x : ℕ => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun x : ℕ => 2 * C / Real.sqrt x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hsx : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx1
  have hxx : (x:ℝ) = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by positivity)).symm
  have hxpos : (0:ℝ) < x := by linarith
  rw [Real.norm_eq_abs, show g x / x - κ = (g x - κ * x) / x by field_simp, abs_div,
    abs_of_pos hxpos, div_le_div_iff₀ hxpos (by linarith)]
  have := h x
  calc |g x - κ * x| * Real.sqrt x ≤ C * (Real.sqrt x + 1) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right this (by linarith)
    _ ≤ 2 * C * x := by
        have h1 := mul_le_mul_of_nonneg_left hsx (mul_nonneg hC (by linarith : (0:ℝ) ≤ Real.sqrt x))
        nlinarith [h1, hxx]

theorem kappa_eq (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r : ℕ) (hr : 0 < r) (δ : ℝ)
    (hδ : Filter.Tendsto (fun x : ℕ => (Nat.count (Q Cp r) x : ℝ) / x) Filter.atTop (nhds δ)) :
    kappa Cp r = δ :=
  tendsto_nhds_unique (tendsto_of_bound _ _ _ (count_bound Cp hC0 r hr)) hδ

/-- **Quantitative `Hcount`, positive discriminants.** The positive fundamental discriminants `d < x` coprime to
`r` number `(3/π²)∏_{p∣r} p/(p+1)·x` up to `(16r + 3)(√x + 1)`. Unconditional. -/
theorem hcount_pos (r : ℕ) (hr : 0 < r) (x : ℕ) :
    |(Nat.count (Q CpPos r) x : ℝ) - 3 / Real.pi ^ 2 * gfac r * x| ≤ (16 * r + 3) * (Real.sqrt x + 1) := by
  rw [← kappa_eq CpPos CpPos0 r hr _ (delta_pos_closed r hr)]
  exact count_bound CpPos CpPos0 r hr x

/-- **Quantitative `Hcount`, negative discriminants.** Unconditional. -/
theorem hcount_neg (r : ℕ) (hr : 0 < r) (x : ℕ) :
    |(Nat.count (Q CpNeg r) x : ℝ) - 3 / Real.pi ^ 2 * gfac r * x| ≤ (16 * r + 3) * (Real.sqrt x + 1) := by
  rw [← kappa_eq CpNeg CpNeg0 r hr _ (delta_neg_closed r hr)]
  exact count_bound CpNeg CpNeg0 r hr x

end GSHcount

