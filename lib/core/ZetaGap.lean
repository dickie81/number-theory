import Mathlib
import ZetaBalance

/-!
# From the inert-prime gap to the Riemann hypothesis

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 3): an upper bound on the gap
`Σ_t Σ_j [ASK(a_t, t, w_{u,j}) − MAIN(a_t, w_{u,j})]` of `ZetaBalance`, averaged over the translates `u ∈ A`, bounds the
error of `ζ`'s ramp sum, `Gz(x) = Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x`, by `7x^{1/2+3ε}`.

The weights are split by the thick classes `Θ(u) = {(−1, s·u) : s ∈ T2}`.

* **The thick part** (`Setting.Th`) is the part of the balance identity at `Θ(u)`, with every weight replaced by
  `a_t/x`. Its average over `u ∈ A` keeps only the characters trivial on `A` (`Setting.sum_Th`):
  `(a_t|T2|/2x)·Re(Gz + g_{χq} − g_{χd} − g_{χqχd})(x)`.
* **The analytic inputs**, two properties of the setting. It is *thin* at `X` (`Setting.Thin`) when every error is at
  most `θy` for `y ≥ X`, with `8|A|x²θ ≤ 1`. Its *twists* are small (`Setting.Twists`) when the three twists are at
  most `x^{1/2+ε}` at `x`.
* **Lemma T** (`Setting.Th_le`): the thick part is at most `ASK − MAIN + a_t/x²`. On thick classes the weights are
  within `δ` of `a_t/x`, and `w·g_χ(a/w)` is Lipschitz in `w` (`Setting.norm_mul_g_sub_le`, from Chebyshev). On thin
  classes `a_t/w ≥ X`, where the setting is thin.
* **Theorem Z** (`BalanceData.zeta_le`): take weights (`Weights`) with `m ≥ x^{1/2−ε}` words and `|T2| ≥ x^{−ε}|A|`,
  whose averaged gap is at most `x^ε Σ_t a_t` (`BalanceData`), in a setting thin at `X` with small twists. Then
  `Gz(x) ≤ 7x^{1/2+3ε}`.
* **Theorem E** (`zetaWindowBound_of_zetaBalanceBound`): such data on windows give `WindowGRH.ZetaWindowBound`, hence
  the Riemann hypothesis (`riemannHypothesis_of_zetaBalanceBound`).

The counting uses only that `G` has `4|A|` characters (`card_Dual`), each of norm `1` (`norm_eval`), and that
`|Φ| = 2|A|` (`card_Φ`).

Measuring the thick weights against `a_t/x`, rather than one `b` with `a_t/b` near `x`, evaluates the errors at `x`
itself. So no Lipschitz bound on `Gz` is needed, and no bound on `L'/L(1, χ)` for the twists.
-/

namespace ZetaBalance

open Complex ComplexConjugate ArithmeticFunction

/-! ## The characters of `G`: norms and number -/

/-- `|σ^α| = 1`. -/
theorem norm_sgnPow (α : Bool) (σ : ℤˣ) : ‖sgnPow α σ‖ = 1 := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> cases α <;> simp [sgnPow]

/-- `|χ(g)| = 1`. -/
theorem norm_eval {e : ℕ} (χ : Dual e) (g : G e) : ‖eval χ g‖ = 1 := by
  simp only [eval, norm_mul, norm_sgnPow, norm_apply, mul_one]

/-- `G` has `4|A|` characters. -/
theorem card_Dual (e : ℕ) : Fintype.card (Dual e) = 4 * Fintype.card (A e) := by
  simp only [Fintype.card_prod, Fintype.card_bool, card_dual]
  ring

/-- `|Φ| = 2|A|`. -/
theorem card_Φ (e : ℕ) : Fintype.card (Φ e) = 2 * Fintype.card (A e) := by
  rw [Fintype.card_prod, Fintype.card_units_int]

/-- `‖Σ_χ conj χ(g) f(χ)‖ ≤ 4|A|c` when every `‖f(χ)‖ ≤ c`. -/
theorem norm_sum_conj_eval_mul_le {e : ℕ} (g : G e) (f : Dual e → ℂ) {c : ℝ} (hf : ∀ χ, ‖f χ‖ ≤ c) :
    ‖∑ χ, conj (eval χ g) * f χ‖ ≤ 4 * Fintype.card (A e) * c := by
  calc _ ≤ ∑ _χ : Dual e, c := (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by simpa [norm_eval] using hf χ)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, card_Dual, nsmul_eq_mul]
      push_cast
      ring

namespace Setting

variable (S : Setting)

/-- `Re g_1(y) = Σ_{n ≤ y} Λ(n)(y/n − 1) − y log y + (1 + γ)y`, the error of `ζ`'s ramp sum. -/
theorem g_one_re (y : ℝ) : (S.g (false, false, 1) y).re =
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y := by
  have hD := (S.D_eq_one_iff (false, false, 1)).2 rfl
  have hv (n : ℕ) : (S.D (false, false, 1)).primitiveCharacter n = 1 := by
    rw [hD]
    exact prim_one_apply n
  rw [g, WindowGRH.rampErr, ite_eq_left ((prim_eq_one_iff _).2 hD), add_re, sub_re, ofReal_re, ofReal_re,
    RampLaplace.rampSum, re_sum]
  congr 2
  exact Finset.sum_congr rfl fun n _ => by rw [hv, mul_one, ← ofReal_mul, ofReal_re]

/-- **Lipschitz in the weight**: `‖w·g_χ(a/w) − w'·g_χ(a/w')‖ ≤ (log 4 + 5)·a·|w − w'|/min(w, w')`. The ramp sums
move by at most `ψ(a/min(w, w'))·|w − w'|`, and the main term by `a·|log w − log w'|`. -/
theorem norm_mul_g_sub_le (χ : Dual S.e) {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * S.g χ (a / w) - (w' : ℂ) * S.g χ (a / w')‖ ≤ (Real.log 4 + 5) * a * |w - w'| / min w w' := by
  have hm : 0 < min w w' := lt_min hw hw'
  have hK : ∀ {v}, min w w' ≤ v → ⌊a / v⌋₊ ≤ ⌊a / min w w'⌋₊ := fun hv =>
    Nat.floor_le_floor (div_le_div_of_nonneg_left ha hm hv)
  rw [S.mul_g χ hw (hK (min_le_left _ _)), S.mul_g χ hw' (hK (min_le_right _ _)), add_sub_add_comm,
    ← Finset.sum_sub_distrib, show (Real.log 4 + 5) * a * |w - w'| / min w w' =
      (Real.log 4 + 4) * (a / min w w') * |w - w'| + a * (|w - w'| / min w w') by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the ramp sums: each ramp moves by at most `|w − w'|`, and `ψ(y) ≤ (log 4 + 4)y`
    calc _ ≤ ∑ n ∈ Finset.Icc 1 ⌊a / min w w'⌋₊, Λ n * |w - w'| := (norm_sum_le _ _).trans <|
          Finset.sum_le_sum fun n _ => by
            rw [← mul_sub, ← ofReal_sub, norm_mul, norm_mul, norm_real, norm_real,
              Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_eq_abs]
            refine mul_le_mul (mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _))
              ((abs_max_sub_max_le_abs _ _ _).trans_eq ?_) (abs_nonneg _) vonMangoldt_nonneg
            rw [sub_sub_sub_cancel_left, abs_sub_comm]
      _ = Chebyshev.psi (a / min w w') * |w - w'| := by
          rw [← Finset.sum_mul, Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (by positivity)) (abs_nonneg _)
  · -- the main terms: `a·|log w − log w'|` for `χ* = 1`, and `0` otherwise
    have hlog {v v' : ℝ} (hv : 0 < v) (hv' : 0 < v') : Real.log v - Real.log v' ≤ (v - v') / v' := by
      rw [← Real.log_div hv.ne' hv'.ne', sub_div, div_self hv'.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hv hv')
    split_ifs
    · rcases ha.eq_or_lt with rfl | ha'
      · simp
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs]
      calc _ = |a * (Real.log w - Real.log w')| := by
            congr 1
            rw [Real.log_div ha'.ne' hw.ne', Real.log_div ha'.ne' hw'.ne']
            ring
        _ = a * |Real.log w - Real.log w'| := by rw [abs_mul, abs_of_pos ha']
        _ ≤ _ := mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
          ⟨(hlog hw hw').trans (div_le_div₀ (abs_nonneg _) (le_abs_self _) hm (min_le_right _ _)),
            (hlog hw' hw).trans (div_le_div₀ (abs_nonneg _) ((le_abs_self _).trans_eq (abs_sub_comm _ _)) hm
              (min_le_left _ _))⟩) ha
    · simp only [sub_self, norm_zero]
      positivity

/-- The thick classes `Θ(u) = {(−1, s·u) : s ∈ T2}`. -/
noncomputable def thickSet (T2 : Finset (A S.e)) (u : A S.e) : Finset (Φ S.e) :=
  T2.image fun s => (-1, s * u)

/-- **The thin scales**: the setting is thin at `X` for `x` when every error is at most `θy` for `y ≥ X`, with
`8|A|x²θ ≤ 1`. -/
def Thin (x X : ℝ) : Prop :=
  ∃ θ : ℝ, (∀ χ, ∀ y ≥ X, ‖S.g χ y‖ ≤ θ * y) ∧ 8 * Fintype.card (A S.e) * x ^ 2 * θ ≤ 1

/-- **The twists**: the three quadratic twists `g_{χq}`, `g_{χd}` and `g_{χqχd}` are at most `x^{1/2+ε}` at `x`. -/
def Twists (x ε : ℝ) : Prop :=
  ∀ α β : Bool, (α || β) = true → ‖S.g (α, β, 1) x‖ ≤ x ^ (1 / 2 + ε)

/-- The thick part of the balance identity at `(u, t)`: the classes `Θ(u)`, every weight replaced by `r`, the
errors evaluated at `y`. -/
noncomputable def Th (T2 : Finset (A S.e)) (u t : A S.e) (r y : ℝ) : ℝ :=
  ((Fintype.card (Φ S.e) : ℂ)⁻¹ * ∑ s ∈ T2, (r : ℂ) * ∑ χ, conj (eval χ (γ t (-1, s * u))) * S.g χ y).re

/-- **Lemma T**: the thick part, with weights `a/x` and errors at `x`, is at most `ASK − MAIN + a/x²`, when the thick
weights are within `δ` of `a/x` and every thin class has `a/W ≥ X`, where the setting is thin. -/
theorem Th_le (T2 : Finset (A S.e)) (u t : A S.e) {a x δ X : ℝ} (W : Φ S.e → ℝ) (hW : ∀ ρ, 0 < W ρ)
    (ha : 0 < a) (hx : 1 ≤ x) (hthick : ∀ s ∈ T2, |W (-1, s * u) - a / x| ≤ δ)
    (hδ : 64 * Fintype.card (A S.e) * x ^ 3 * δ ≤ a) (hthin : ∀ ρ ∉ S.thickSet T2 u, X ≤ a / W ρ)
    (hT : S.Thin x X) : S.Th T2 u t (a / x) x ≤ S.ASK a t W - S.MAIN a W + a / x ^ 2 := by
  obtain ⟨θ, hscale, hθ⟩ := hT
  have hx0 : 0 < x := by linarith
  have hA : (1 : ℝ) ≤ Fintype.card (A S.e) := Nat.one_le_cast.2 Fintype.card_pos
  rw [S.balance a t W hW, Th, ← sub_le_iff_le_add', ← sub_re, ← mul_sub]
  refine (re_le_norm _).trans ?_
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ (by positivity),
    ← Finset.sum_add_sum_compl (S.thickSet T2 u), thickSet,
    Finset.sum_image fun s _ s' _ h => mul_right_cancel (Prod.ext_iff.1 h).2, sub_add_eq_sub_sub,
    ← Finset.sum_sub_distrib]
  refine (norm_sub_le _ _).trans ((add_le_add
    ((norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ (a / x ^ 2) fun s hs => ?_))
    ((norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ (a / x ^ 2 / 2) fun ρ hρ => ?_))).trans ?_)
  · -- a thick class: the weight is within `δ` of `a/x`, so at least `a/2x`
    have hs := hthick s hs
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hs
    have hmin : a / (2 * x) ≤ min (a / x) (W (-1, s * u)) := by
      refine le_min (div_le_div_of_nonneg_left ha.le hx0 (by linarith)) ?_
      have h1 : δ ≤ a / (2 * x) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right (le_self_pow₀ hx (by norm_num : 3 ≠ 0)) hδ0,
          mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ x ^ 3 * δ)]
      have h2 : a / x = 2 * (a / (2 * x)) := by field_simp
      linarith [(abs_sub_le_iff.1 hs).2]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [mul_left_comm _ (conj _), ← mul_sub]
    refine (norm_sum_conj_eval_mul_le _ _ (c := 16 * x * δ) fun χ => ?_).trans ?_
    · have h := S.norm_mul_g_sub_le χ ha.le (div_pos ha hx0) (hW (-1, s * u))
      rw [div_div_cancel₀ ha.ne'] at h
      refine h.trans ((div_le_div₀ (c := 8 * a * δ) (by positivity) ?_ (by positivity) hmin).trans_eq
        (by field_simp; ring))
      have hlog : Real.log 4 + 5 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
      rw [abs_sub_comm]
      gcongr
    · rw [le_div_iff₀ (by positivity)]
      linarith
  · -- a thin class: `a/W ≥ X`, so each error is at most `θa/W`
    rw [norm_mul, norm_real, Real.norm_of_nonneg (hW ρ).le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_conj_eval_mul_le _ _ fun χ =>
      hscale χ _ (hthin ρ (Finset.mem_compl.1 hρ))) (hW ρ).le).trans ?_
    rw [show W ρ * (4 * Fintype.card (A S.e) * (θ * (a / W ρ))) = 4 * Fintype.card (A S.e) * θ * a by
      field_simp [(hW ρ).ne'], div_div, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hθ ha.le]
  · -- the count: `|T2| ≤ |A|` thick classes and `|Φ| = 2|A|` classes in all
    rw [nsmul_eq_mul, nsmul_eq_mul]
    calc _ ≤ (Fintype.card (A S.e) : ℝ) * (a / x ^ 2) + Fintype.card (Φ S.e) * (a / x ^ 2 / 2) := by
          gcongr <;> exact_mod_cast Finset.card_le_univ _
      _ = _ := by
          rw [card_Φ]
          push_cast
          ring

/-- **Lemma Avg**: averaged over the translates `u`, the thick part keeps only the characters trivial on `A`:
`Σ_u Th(u, t) = (r|T2|/2)·Re(g_1 + g_{χq} − g_{χd} − g_{χqχd})(y)`. -/
theorem sum_Th (T2 : Finset (A S.e)) (t : A S.e) (r y : ℝ) :
    ∑ u, S.Th T2 u t r y = r * T2.card / 2 *
      (S.g (false, false, 1) y + S.g (false, true, 1) y - S.g (true, false, 1) y - S.g (true, true, 1) y).re := by
  have h (s : A S.e) : ∑ u, ∑ χ, conj (eval χ (γ t (-1, s * u))) * S.g χ y = Fintype.card (A S.e) *
      (S.g (false, false, 1) y + S.g (false, true, 1) y - S.g (true, false, 1) y - S.g (true, true, 1) y) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, conj_eval_γ, mul_comm s, mul_assoc, ← Finset.mul_sum, sum_conj_apply_mul]
    simp [Fintype.sum_prod_type, sgnPow]
    ring
  have hA : (Fintype.card (A S.e) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [Th, ← re_sum, ← Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h s, Finset.sum_const, nsmul_eq_mul, card_Φ,
    show ∀ z : ℂ, ((2 * Fintype.card (A S.e) : ℕ) : ℂ)⁻¹ * ((r : ℂ) * (T2.card * (Fintype.card (A S.e) * z))) =
      ((r * T2.card / 2 : ℝ) : ℂ) * z from fun z => by push_cast; field_simp, re_ofReal_mul]

end Setting

/-- **The weights for `ζ` at `x`** in the setting `S`, with losses `x^ε` and thin classes beyond `X`: `m` words,
translates `TT`, thick classes `T2`, scales `a_t` and weights `w_{u,j}`. -/
structure Weights (S : Setting) (x ε X : ℝ) where
  /-- The number of words. -/
  m : ℕ
  /-- The translates `t`. -/
  TT : Finset (A S.e)
  /-- The thick classes, `Θ(u) = {(−1, s·u) : s ∈ T2}`. -/
  T2 : Finset (A S.e)
  /-- The scales `a_t`. -/
  a : A S.e → ℝ
  /-- The weights `w_{u,j}`. -/
  w : A S.e → Fin m → Φ S.e → ℝ
  /-- How far thick weights may be from `a_t/x`. -/
  δ : ℝ
  /-- The weights are positive. -/
  w_pos : ∀ u j ρ, 0 < w u j ρ
  /-- The scales are positive. -/
  a_pos : ∀ t ∈ TT, 0 < a t
  /-- On the thick classes, the weights are within `δ` of `a_t/x`. -/
  thick_near : ∀ t ∈ TT, ∀ u j, ∀ s ∈ T2, |w u j (-1, s * u) - a t / x| ≤ δ
  /-- `δ` is small: `64|A|x³δ ≤ a_t`. -/
  thick_small : ∀ t ∈ TT, 64 * Fintype.card (A S.e) * x ^ 3 * δ ≤ a t
  /-- On the thin classes, `a_t/w ≥ X`. -/
  thin_far : ∀ t ∈ TT, ∀ u j, ∀ ρ ∉ S.thickSet T2 u, X ≤ a t / w u j ρ
  /-- At least `x^{1/2−ε}` words. -/
  words : x ^ (1 / 2 - ε) ≤ m
  /-- At least `x^{−ε}|A|` thick classes. -/
  thick_card : x ^ (-ε) * Fintype.card (A S.e) ≤ T2.card
  /-- There is a translate. -/
  TT_nonempty : TT.Nonempty

/-- **The balance data for `ζ` at `x`**: weights whose gap, averaged over the translates `u`, is at most
`x^ε Σ_t a_t`. -/
structure BalanceData (S : Setting) (x ε X : ℝ) extends Weights S x ε X where
  /-- The gap, averaged over `u`, is at most `x^ε Σ_t a_t`. -/
  gap_le : ∑ u, S.gap TT m a w u ≤ Fintype.card (A S.e) * x ^ ε * ∑ t ∈ TT, a t

/-- **Theorem Z**: balance data at `x`, in a setting thin at `X` with small twists, bound the error of `ζ`'s ramp sum
by `7x^{1/2+3ε}`. -/
theorem BalanceData.zeta_le {S : Setting} {x ε X : ℝ} (D : BalanceData S x ε X) (hthin : S.Thin x X)
    (htw : S.Twists x ε) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x ≤
      7 * x ^ (1 / 2 + 3 * ε) := by
  obtain ⟨⟨m, TT, T2, a, w, δ, w_pos, a_pos, thick_near, thick_small, thin_far, words, thick_card, TT_nonempty⟩,
    gap_le⟩ := D
  have hx0 : 0 < x := by linarith
  -- Lemma T at every `u`, `j` and `t ∈ TT`, summed, with Lemma Avg on the left
  have key := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => Finset.sum_le_sum fun t ht =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => S.Th_le T2 u t (w u j) (w_pos u j) (a_pos t ht) hx
      (thick_near t ht u j) (thick_small t ht) (thin_far t ht u j) hthin
  have hL : ∑ u, ∑ t ∈ TT, (m : ℝ) * S.Th T2 u t (a t / x) x = m * T2.card / (2 * x) * (∑ t ∈ TT, a t) *
      (S.g (false, false, 1) x + S.g (false, true, 1) x - S.g (true, false, 1) x - S.g (true, true, 1) x).re := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by rw [← Finset.mul_sum, S.sum_Th]; ring
  have hs : ∑ t ∈ TT, (m : ℝ) * (a t / x ^ 2) = m * (∑ t ∈ TT, a t) / x ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL,
    hs] at key
  simp only [Setting.gap] at gap_le
  -- the arithmetic: `R ≤ 4x^{1/2+3ε}`, from `m ≥ x^{1/2−ε}` and `|T2| ≥ x^{−ε}|A|`
  have hm : (0 : ℝ) < m := (Real.rpow_pos_of_pos hx0 _).trans_le words
  have hP : 0 < ∑ t ∈ TT, a t := Finset.sum_pos a_pos TT_nonempty
  have hA1 : Fintype.card (A S.e) * x ^ ε * x ≤ m * T2.card * x ^ (1 / 2 + 3 * ε) := by
    have e : x ^ (1 / 2 - ε) * x ^ (-ε) * x ^ (1 / 2 + 3 * ε) = x ^ ε * x := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']
      ring_nf
    calc _ = x ^ (1 / 2 - ε) * (x ^ (-ε) * Fintype.card (A S.e)) * x ^ (1 / 2 + 3 * ε) := by
          linear_combination (-(Fintype.card (A S.e) : ℝ)) * e
      _ ≤ _ := by gcongr
  have hA2 : (Fintype.card (A S.e) : ℝ) ≤ T2.card * x ^ (1 / 2 + 3 * ε) := by
    calc _ = x ^ ε * (x ^ (-ε) * Fintype.card (A S.e)) := by
          rw [← mul_assoc, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ x ^ (1 / 2 + 3 * ε) * T2.card := by
          gcongr
          linarith
      _ = _ := mul_comm _ _
  have hR : (S.g (false, false, 1) x + S.g (false, true, 1) x - S.g (true, false, 1) x -
      S.g (true, true, 1) x).re ≤ 4 * x ^ (1 / 2 + 3 * ε) := by
    have hT : (0 : ℝ) < T2.card := (mul_pos (Real.rpow_pos_of_pos hx0 _) (by positivity)).trans_le thick_card
    refine le_of_mul_le_mul_left ?_ (mul_pos (div_pos (mul_pos hm hT) (by positivity : (0 : ℝ) < 2 * x)) hP)
    calc _ ≤ Fintype.card (A S.e) * x ^ ε * (∑ t ∈ TT, a t) +
          Fintype.card (A S.e) * (m * (∑ t ∈ TT, a t) / x ^ 2) := key.trans (by linarith)
      _ = (∑ t ∈ TT, a t) * (Fintype.card (A S.e) * x ^ ε * x + m * (Fintype.card (A S.e) / x)) / x := by
          field_simp
      _ ≤ (∑ t ∈ TT, a t) * (m * T2.card * x ^ (1 / 2 + 3 * ε) + m * (T2.card * x ^ (1 / 2 + 3 * ε))) / x := by
          gcongr
          exact (div_le_self (by positivity) hx).trans hA2
      _ = _ := by
          field_simp
          ring
  -- `Gz(x) = Re g_1(x) ≤ R + 3x^{1/2+ε}`, by the three twists
  rw [← S.g_one_re]
  simp only [add_re, sub_re] at hR
  linarith [neg_le_of_abs_le (abs_re_le_norm (S.g (false, true, 1) x)), re_le_norm (S.g (true, false, 1) x),
    re_le_norm (S.g (true, true, 1) x), htw false true rfl, htw true false rfl, htw true true rfl,
    Real.rpow_le_rpow_of_exponent_le hx (by linarith : 1 / 2 + ε ≤ 1 / 2 + 3 * ε)]

/-- **The frontier for `ζ` after step 3**: for every `ε > 0`, at every `x` of windows `[Y, Y^λ]` with `Y` arbitrarily
large, a setting thin at some `X`, with small twists, and balance data. -/
def ZetaBalanceBound : Prop :=
  ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam),
    ∃ (S : Setting) (X : ℝ), S.Thin x X ∧ S.Twists x ε ∧ Nonempty (BalanceData S x ε X)

/-- **Theorem E**: the frontier after step 3 gives the windowed bound for `ζ`. -/
theorem zetaWindowBound_of_zetaBalanceBound (h : ZetaBalanceBound) : WindowGRH.ZetaWindowBound := by
  intro θ hθ
  obtain ⟨lam, hlam, hY⟩ := h ((θ - 1 / 2) / 3) (by linarith)
  refine ⟨lam, by exact_mod_cast hlam, 7, fun Y₀ => ?_⟩
  obtain ⟨Y, hY₀, hYx⟩ := hY (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY₀, fun x hx => ?_⟩
  obtain ⟨S, X, hthin, htw, ⟨D⟩⟩ := hYx x (by simpa using hx)
  have := D.zeta_le hthin htw ((le_max_right _ _).trans (hY₀.trans hx.1)) (by linarith)
  rwa [show 1 / 2 + 3 * ((θ - 1 / 2) / 3) = θ by ring] at this

/-- **The Riemann hypothesis from balance data on windows.** -/
theorem riemannHypothesis_of_zetaBalanceBound (h : ZetaBalanceBound) : RiemannHypothesis :=
  WindowGRH.riemannHypothesis_of_zetaWindowBound (zetaWindowBound_of_zetaBalanceBound h)

end ZetaBalance

#print axioms ZetaBalance.BalanceData.zeta_le
#print axioms ZetaBalance.riemannHypothesis_of_zetaBalanceBound
