import Mathlib
import ZetaBalance

/-!
# From the inert-prime gap to the Riemann hypothesis for `ζ` and every Dirichlet `L`-function

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 3): an upper bound on the gap
`Σ_t Σ_j [ASK(a_t, t, w_{u,j}) − MAIN(a_t, w_{u,j})]` of `ZetaBalance`, averaged over the translates `u` in the kernel
`A₀` of a character `κ` of `A`, bounds the weighted error of the characters `κ^k`. For `κ = 1` that error is
`ζ`'s, `Gz(x) = Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x`; for `κ` lifting a primitive `χ` (`Setting.Lifts`) it is
`(WindowGRH.cyclic χ).G(x)`, the error of the cyclic family of `χ`.

The weights are split by the thick classes `Θ(u) = {(−1, s·u) : s ∈ T2}`, with `T2 ⊆ A₀`.

* **The characters trivial on `A₀`** (`sum_dual_sum_A₀`). For `κ` of order `o`, `1[κ(u) = 1] = o⁻¹ Σ_{k<o} κ(u)^k`,
  so by orthogonality a sum over the characters `ξ` weighted by `Σ_{u ∈ A₀} conj ξ(u)` keeps only `ξ = κ^k`, `k < o`,
  each with weight `|A|/o`. No count of the characters trivial on `A₀` is needed.
* **The thick part** (`Setting.Th`) is the part of the balance identity at `Θ(u)`, with every weight replaced by
  `a_t/x`. Its average over `u ∈ A₀` keeps only the characters `κ^k` (**Lemma Avg**, `Setting.sum_Th`):
  `(a_t|T2|/(2ox))·Re Σ_{k<o} κ(t)^k (g_{(0,0,κ^k)} + g_{(0,1,κ^k)} − g_{(1,0,κ^k)} − g_{(1,1,κ^k)})(x)`.
* **The analytic inputs**, properties of the setting. It is *thin* at `X` (`Setting.Thin`) when every error is at
  most `θy` for `y ≥ X`, with `8|A|x²θ ≤ 1`. Its *twists* are small (`Setting.Twists`) when the `3o` twists
  `g_{(α,β,κ^k)}`, `(α, β) ≠ (0, 0)` and `k < o`, are at most `x^{1/2+ε}` at `x`.
* **Lemma T** (`Setting.Th_le`): the thick part is at most `ASK − MAIN + a_t/x²`. On thick classes the weights are
  within `δ` of `a_t/x`, and `w·g_χ(a/w)` is Lipschitz in `w` (`Setting.norm_mul_g_sub_le`, from Chebyshev). On thin
  classes `a_t/w ≥ X`, where the setting is thin.
* **Theorem Z** (`BalanceData.cyclicG_le`): take weights (`Weights`) with `m ≥ x^{1/2−ε}` words,
  `|T2| ≥ x^{−ε}|A₀|`, and translates whose shares give the kept characters the weights of the cyclic family:
  `|Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)| ≤ x^{ε−1} Σ_t a_t` for `0 < k < o`. If their gap averaged over `A₀` is at most
  `x^ε Σ_t a_t` (`BalanceData`), in a setting thin at `X` with small twists, and the kept errors `g_{(0,0,κ^k)}(x)`
  are at most `x^{3/2+ε}`, then `Re g_{(0,0,1)}(x) + (3o + 1)⁻¹ Σ_{0<k<o} Re g_{(0,0,κ^k)}(x) ≤ (9o − 2)x^{1/2+3ε}`.
* **For `ζ`**, `κ = 1` and `o = 1`: no shares, no kept errors, and `Gz(x) ≤ 7x^{1/2+3ε}` (`BalanceData.zeta_le`).
  **Theorem E** (`zetaWindowBound_of_zetaBalanceBound`): such data on windows give `WindowGRH.ZetaWindowBound`, hence
  the Riemann hypothesis (`riemannHypothesis_of_zetaBalanceBound`).
* **For every primitive `χ`**: when `κ` lifts `χ`, the weighted error is `(WindowGRH.cyclic χ).G`
  (`Setting.Lifts.cyclicG_eq`), and the kept errors are eventually at most `x^{3/2+ε}` by a crude bound
  (`eventually_norm_rampErr_le`). So data for every primitive `χ` on windows (`BalanceBound`) give
  `WindowGRH.WindowBound` (`windowBound_of_balanceBound`), hence the Riemann hypothesis for `ζ` and every Dirichlet
  `L`-function (`rhAndGRH_of_balanceBound`).

The counting uses only that `G` has `4|A|` characters (`card_Dual`), each of norm `1` (`norm_eval`), and that
`|Φ| = 2|A|` (`card_Φ`).

Measuring the thick weights against `a_t/x`, rather than one `b` with `a_t/b` near `x`, evaluates the errors at `x`
itself. So no Lipschitz bound on the errors is needed, and no bound on `L'/L(1, χ)` for the twists.

**Coordinates.** Everything is in the coordinates of Lemma B, where `c = (−1, −1, 1)` and the partner of `n` is
`((−n/q), [n]_A t)`. For an odd `χ`, complex conjugation is `(−1, −1, [−1]_A)` with `κ([−1]_A) = χ(−1) = −1`;
coordinates built on it replace `t` by `[−1]_A t`, which multiplies the `k`-th share by `(−1)^k`. Neither Lemma B
nor Theorem Z needs the archive's twist of the Artin map, but the shares asked for are those of these coordinates,
which the twist provides.
-/

namespace ZetaBalance

open Complex ComplexConjugate ArithmeticFunction DirichletCharacter

/-! ## The characters of `G`: norms and number -/

/-- `|σ^α| = 1`. -/
theorem norm_sgnPow (α : Bool) (σ : ℤˣ) : ‖sgnPow α σ‖ = 1 := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> cases α <;> simp [sgnPow]

/-- `|χ(g)| = 1`. -/
theorem norm_eval {A : Type*} [CommGroup A] [Fintype A] (χ : Dual A) (g : G A) : ‖eval χ g‖ = 1 := by
  simp only [eval, norm_mul, norm_sgnPow, norm_apply, mul_one]

/-- `G` has `4|A|` characters. -/
theorem card_Dual {A : Type*} [CommGroup A] [Fintype A] [Fintype (A →* ℂˣ)] :
    Fintype.card (Dual A) = 4 * Fintype.card A := by
  simp only [Fintype.card_prod, Fintype.card_bool, card_dual]
  ring

/-- `|Φ| = 2|A|`. -/
theorem card_Φ {A : Type*} [Fintype A] : Fintype.card (Φ A) = 2 * Fintype.card A := by
  rw [Fintype.card_prod, Fintype.card_units_int]

/-- `‖Σ_χ conj χ(g) f(χ)‖ ≤ 4|A|c` when every `‖f(χ)‖ ≤ c`. -/
theorem norm_sum_conj_eval_mul_le {A : Type*} [CommGroup A] [Fintype A] [Fintype (A →* ℂˣ)] (g : G A)
    (f : Dual A → ℂ) {c : ℝ} (hf : ∀ χ, ‖f χ‖ ≤ c) :
    ‖∑ χ, conj (eval χ g) * f χ‖ ≤ 4 * Fintype.card A * c := by
  calc _ ≤ ∑ _χ : Dual A, c := (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by simpa [norm_eval] using hf χ)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, card_Dual, nsmul_eq_mul]
      push_cast
      ring

/-! ## The characters trivial on a kernel -/

section Kernel

variable {A : Type*} [CommGroup A] [Fintype A] [Fintype (A →* ℂˣ)]

/-- `A₀ = ker κ`, as a finset. -/
noncomputable def A₀ (κ : A →* ℂˣ) : Finset A := Finset.univ.filter fun u => κ u = 1

omit [Fintype (A →* ℂˣ)] in
/-- `u ∈ A₀` exactly when `κ(u) = 1`. -/
theorem mem_A₀ {κ : A →* ℂˣ} {u : A} : u ∈ A₀ κ ↔ κ u = 1 := by
  simp [A₀]

omit [Fintype (A →* ℂˣ)] in
/-- `1[κ(u) = 1] = o⁻¹ Σ_{k<o} κ(u)^k`, for `κ` of order `o`: `κ(u)` is an `o`-th root of unity. -/
theorem ite_eq_sum_pow (κ : A →* ℂˣ) (u : A) :
    (if κ u = 1 then 1 else 0 : ℂ) = (orderOf κ : ℂ)⁻¹ * ∑ k ∈ Finset.range (orderOf κ), (κ u : ℂ) ^ k := by
  have ho : (orderOf κ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (orderOf_pos κ).ne'
  split_ifs with h
  · simp [h, ho]
  · have h1 : (κ u : ℂ) ≠ 1 := fun h' => h (Units.ext h')
    rw [geom_sum_eq h1, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one]
    simp

/-- **The characters trivial on `A₀`**: weighting each character `ξ` by `Σ_{u ∈ A₀} conj ξ(u)` keeps only the
powers `κ^k`, `k < o`, each with weight `|A|/o`. -/
theorem sum_dual_sum_A₀ (κ : A →* ℂˣ) (F : (A →* ℂˣ) → ℂ) :
    ∑ ξ, (∑ u ∈ A₀ κ, conj (ξ u : ℂ)) * F ξ =
      Fintype.card A / orderOf κ * ∑ k ∈ Finset.range (orderOf κ), F (κ ^ k) := by
  -- orthogonality: `Σ_u ψ(u) conj ξ(u) = |A|·1[ψ = ξ]`
  have horth (ψ ξ : A →* ℂˣ) : ∑ u, (ψ u : ℂ) * conj (ξ u : ℂ) = if ψ = ξ then (Fintype.card A : ℂ) else 0 := by
    have e (u : A) : (ψ u : ℂ) * conj (ξ u : ℂ) = ((ψ * ξ⁻¹) u : ℂ) := by
      rw [conj_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
    have hiff : ψ * ξ⁻¹ = 1 ↔ ψ = ξ := by
      simp only [MonoidHom.ext_iff, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply, mul_inv_eq_one]
    simp only [e, sum_apply_dual]
    exact if_congr hiff rfl rfl
  have hA (ξ : A →* ℂˣ) : ∑ u ∈ A₀ κ, conj (ξ u : ℂ) =
      (orderOf κ : ℂ)⁻¹ * ∑ k ∈ Finset.range (orderOf κ), if κ ^ k = ξ then (Fintype.card A : ℂ) else 0 := by
    rw [A₀, Finset.sum_filter]
    simp only [← horth, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← mul_assoc, ← ite_eq_sum_pow, ite_mul, one_mul, zero_mul]
  simp only [hA, mul_assoc, ← Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  ring

end Kernel

/-! ## The thick part, Lemmas T and Avg -/

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
theorem norm_mul_g_sub_le (χ : Dual S.A) {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hw' : 0 < w') :
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
noncomputable def thickSet (T2 : Finset S.A) (u : S.A) : Finset (Φ S.A) :=
  T2.image fun s => (-1, s * u)

/-- **The thin scales**: the setting is thin at `X` for `x` when every error is at most `θy` for `y ≥ X`, with
`8|A|x²θ ≤ 1`. -/
def Thin (x X : ℝ) : Prop :=
  ∃ θ : ℝ, (∀ χ, ∀ y ≥ X, ‖S.g χ y‖ ≤ θ * y) ∧ 8 * Fintype.card S.A * x ^ 2 * θ ≤ 1

/-- **The twists** of the characters `κ^k`, `k < o`: the `3o` errors `g_{(α,β,κ^k)}` with `(α, β) ≠ (0, 0)` are at
most `x^{1/2+ε}` at `x`. For `κ = 1` they are the three quadratic twists `χ_q`, `χ_d` and `χ_qχ_d`. -/
def Twists (κ : S.A →* ℂˣ) (x ε : ℝ) : Prop :=
  ∀ α β : Bool, (α || β) = true → ∀ k < orderOf κ, ‖S.g (α, β, κ ^ k) x‖ ≤ x ^ (1 / 2 + ε)

/-- The four errors over `ξ`, signed by `(−1)^α`: `g_{(0,0,ξ)} + g_{(0,1,ξ)} − g_{(1,0,ξ)} − g_{(1,1,ξ)}`. -/
noncomputable def gsum (ξ : S.A →* ℂˣ) (y : ℝ) : ℂ :=
  S.g (false, false, ξ) y + S.g (false, true, ξ) y - S.g (true, false, ξ) y - S.g (true, true, ξ) y

/-- The thick part of the balance identity at `(u, t)`: the classes `Θ(u)`, every weight replaced by `r`, the
errors evaluated at `y`. -/
noncomputable def Th (T2 : Finset S.A) (u t : S.A) (r y : ℝ) : ℝ :=
  ((Fintype.card (Φ S.A) : ℂ)⁻¹ * ∑ s ∈ T2, (r : ℂ) * ∑ χ, conj (eval χ (γ t (-1, s * u))) * S.g χ y).re

/-- **Lemma T**: the thick part, with weights `a/x` and errors at `x`, is at most `ASK − MAIN + a/x²`, when the thick
weights are within `δ` of `a/x` and every thin class has `a/W ≥ X`, where the setting is thin. -/
theorem Th_le (T2 : Finset S.A) (u t : S.A) {a x δ X : ℝ} (W : Φ S.A → ℝ) (hW : ∀ ρ, 0 < W ρ)
    (ha : 0 < a) (hx : 1 ≤ x) (hthick : ∀ s ∈ T2, |W (-1, s * u) - a / x| ≤ δ)
    (hδ : 64 * Fintype.card S.A * x ^ 3 * δ ≤ a) (hthin : ∀ ρ ∉ S.thickSet T2 u, X ≤ a / W ρ)
    (hT : S.Thin x X) : S.Th T2 u t (a / x) x ≤ S.ASK a t W - S.MAIN a W + a / x ^ 2 := by
  obtain ⟨θ, hscale, hθ⟩ := hT
  have hx0 : 0 < x := by linarith
  have hA : (1 : ℝ) ≤ Fintype.card S.A := Nat.one_le_cast.2 Fintype.card_pos
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
    rw [show W ρ * (4 * Fintype.card S.A * (θ * (a / W ρ))) = 4 * Fintype.card S.A * θ * a by
      field_simp [(hW ρ).ne'], div_div, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hθ ha.le]
  · -- the count: `|T2| ≤ |A|` thick classes and `|Φ| = 2|A|` classes in all
    rw [nsmul_eq_mul, nsmul_eq_mul]
    calc _ ≤ (Fintype.card S.A : ℝ) * (a / x ^ 2) + Fintype.card (Φ S.A) * (a / x ^ 2 / 2) := by
          gcongr <;> exact_mod_cast Finset.card_le_univ _
      _ = _ := by
          rw [card_Φ]
          push_cast
          ring

/-- **Lemma Avg**: averaged over the translates `u ∈ A₀ = ker κ`, with `T2 ⊆ A₀`, the thick part keeps only the
characters `κ^k`, `k < o`: `Σ_{u ∈ A₀} Th(u, t) = (r|T2|/2o)·Re Σ_{k<o} κ(t)^k (g_{(0,0,κ^k)} + g_{(0,1,κ^k)} −
g_{(1,0,κ^k)} − g_{(1,1,κ^k)})(y)`. -/
theorem sum_Th (κ : S.A →* ℂˣ) {T2 : Finset S.A} (hT2 : T2 ⊆ A₀ κ) (t : S.A) (r y : ℝ) :
    ∑ u ∈ A₀ κ, S.Th T2 u t r y = r * T2.card / (2 * orderOf κ) *
      (∑ k ∈ Finset.range (orderOf κ), (κ t : ℂ) ^ k * S.gsum (κ ^ k) y).re := by
  have h (s : S.A) (hs : s ∈ T2) : ∑ u ∈ A₀ κ, ∑ χ, conj (eval χ (γ t (-1, s * u))) * S.g χ y =
      Fintype.card S.A / orderOf κ * ∑ k ∈ Finset.range (orderOf κ), (κ t : ℂ) ^ k * S.gsum (κ ^ k) y := by
    have hκs : κ s = 1 := mem_A₀.1 (hT2 hs)
    have hu (χ : Dual S.A) (u : S.A) : conj (eval χ (γ t (-1, s * u))) =
        conj (χ.2.2 u : ℂ) * (sgnPow χ.1 (-1) * conj (χ.2.2 (s * t⁻¹) : ℂ)) := by
      rw [conj_eval_γ, neg_neg, show sgnPow χ.2.1 1 = 1 by cases χ.2.1 <;> simp [sgnPow],
        mul_right_comm s u t⁻¹, map_mul, Units.val_mul, map_mul]
      ring
    have hk (k : ℕ) : conj ((κ ^ k) (s * t⁻¹) : ℂ) = (κ t : ℂ) ^ k := by
      rw [conj_apply, MonoidHom.pow_apply, mul_inv_rev, inv_inv, map_mul, map_inv, hκs, inv_one, mul_one,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_comm]
    simp only [hu, mul_assoc, ← Finset.sum_mul]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [sum_dual_sum_A₀, hk]
    rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [sgnPow, gsum, ite_true, Bool.false_eq_true, ite_false, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one]
    ring
  have hA : (Fintype.card S.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ho : (orderOf κ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (orderOf_pos κ).ne'
  simp only [Th, ← re_sum, ← Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s hs => h s hs, Finset.sum_const, nsmul_eq_mul, card_Φ,
    show ∀ z : ℂ, ((2 * Fintype.card S.A : ℕ) : ℂ)⁻¹ * ((r : ℂ) * (T2.card * (Fintype.card S.A / orderOf κ * z))) =
      ((r * T2.card / (2 * orderOf κ) : ℝ) : ℂ) * z from fun z => by push_cast; field_simp, re_ofReal_mul]

end Setting

/-! ## Theorem Z -/

/-- **The weights at `x`** in the setting `S`, for the kernel `A₀` of a character `κ` of order `o`, with losses `x^ε`
and thin classes beyond `X`: `m` words, translates `TT`, thick classes `T2 ⊆ A₀`, scales `a_t` and weights `w_{u,j}`.
The translates carry the shares of the cyclic family: `Σ_t a_t κ(t)^k` is within `x^{ε−1} Σ_t a_t` of
`Σ_t a_t/(3o + 1)` for `0 < k < o`. Only `u ∈ A₀` matters. -/
structure Weights (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) where
  /-- The number of words. -/
  m : ℕ
  /-- The translates `t`. -/
  TT : Finset S.A
  /-- The thick classes, `Θ(u) = {(−1, s·u) : s ∈ T2}`. -/
  T2 : Finset S.A
  /-- The scales `a_t`. -/
  a : S.A → ℝ
  /-- The weights `w_{u,j}`. -/
  w : S.A → Fin m → Φ S.A → ℝ
  /-- How far thick weights may be from `a_t/x`. -/
  δ : ℝ
  /-- The weights are positive. -/
  w_pos : ∀ u j ρ, 0 < w u j ρ
  /-- The scales are positive. -/
  a_pos : ∀ t ∈ TT, 0 < a t
  /-- On the thick classes, the weights are within `δ` of `a_t/x`. -/
  thick_near : ∀ t ∈ TT, ∀ u ∈ A₀ κ, ∀ j, ∀ s ∈ T2, |w u j (-1, s * u) - a t / x| ≤ δ
  /-- `δ` is small: `64|A|x³δ ≤ a_t`. -/
  thick_small : ∀ t ∈ TT, 64 * Fintype.card S.A * x ^ 3 * δ ≤ a t
  /-- On the thin classes, `a_t/w ≥ X`. -/
  thin_far : ∀ t ∈ TT, ∀ u ∈ A₀ κ, ∀ j, ∀ ρ ∉ S.thickSet T2 u, X ≤ a t / w u j ρ
  /-- At least `x^{1/2−ε}` words. -/
  words : x ^ (1 / 2 - ε) ≤ m
  /-- The thick classes lie in `A₀`. -/
  thick_sub : T2 ⊆ A₀ κ
  /-- At least `x^{−ε}|A₀|` thick classes. -/
  thick_card : x ^ (-ε) * (A₀ κ).card ≤ T2.card
  /-- The shares: `|Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)| ≤ x^{ε−1} Σ_t a_t` for `0 < k < o`. -/
  shares : ∀ k, 0 < k → k < orderOf κ → ‖∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k -
    (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, a t : ℝ) : ℂ)‖ ≤ x ^ (ε - 1) * ∑ t ∈ TT, a t
  /-- There is a translate. -/
  TT_nonempty : TT.Nonempty

/-- **The balance data at `x`**: weights whose gap, averaged over `u ∈ A₀`, is at most `x^ε Σ_t a_t`. -/
structure BalanceData (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) extends Weights S κ x ε X where
  /-- The gap, averaged over `u ∈ A₀`, is at most `x^ε Σ_t a_t`. -/
  gap_le : ∑ u ∈ A₀ κ, S.gap TT m a w u ≤ (A₀ κ).card * x ^ ε * ∑ t ∈ TT, a t

namespace Setting

variable (S : Setting)

/-- The weighted error of the characters `κ^k`, `k < o`: weight `1` for `κ^0 = 1` and `1/(3o + 1)` for the others.
For `κ` lifting a primitive `χ`, it is `(WindowGRH.cyclic χ).G` (`Setting.Lifts.cyclicG_eq`). -/
noncomputable def cyclicG (κ : S.A →* ℂˣ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (orderOf κ),
    (if κ ^ k = 1 then 1 else (3 * (orderOf κ : ℝ) + 1)⁻¹) * (S.g (false, false, κ ^ k) x).re

/-- The weighted error of `1` is `Re g_{(0,0,1)}`. -/
theorem cyclicG_one (x : ℝ) : S.cyclicG 1 x = (S.g (false, false, 1) x).re := by
  rw [cyclicG, orderOf_one, Finset.sum_range_one, show (1 : S.A →* ℂˣ) ^ 0 = 1 from pow_zero _,
    ite_eq_left rfl, one_mul]

end Setting

/-- **Theorem Z**: balance data at `x`, in a setting thin at `X` with small twists and kept errors at most
`x^{3/2+ε}`, bound the weighted error of the characters `κ^k` by `(9o − 2)x^{1/2+3ε}`, `o` the order of `κ`. -/
theorem BalanceData.cyclicG_le {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (D : BalanceData S κ x ε X)
    (hthin : S.Thin x X) (htw : S.Twists κ x ε)
    (hkept : ∀ k, 0 < k → k < orderOf κ → ‖S.g (false, false, κ ^ k) x‖ ≤ x ^ (3 / 2 + ε))
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    S.cyclicG κ x ≤ (9 * orderOf κ - 2) * x ^ (1 / 2 + 3 * ε) := by
  obtain ⟨⟨m, TT, T2, a, w, δ, w_pos, a_pos, thick_near, thick_small, thin_far, words, thick_sub, thick_card, shares,
    TT_nonempty⟩, gap_le⟩ := D
  have ho : 0 < orderOf κ := orderOf_pos κ
  have hinj : ∀ k < orderOf κ, κ ^ k = 1 → k = 0 := fun k hk h =>
    pow_injOn_Iio_orderOf (Set.mem_Iio.2 hk) (Set.mem_Iio.2 ho) (h.trans (pow_zero κ).symm)
  dsimp only at gap_le
  unfold Setting.Twists at htw
  obtain ⟨o, ho_def⟩ : ∃ o, orderOf κ = o := ⟨_, rfl⟩
  rw [ho_def] at htw hkept shares ho hinj ⊢
  set P := ∑ t ∈ TT, a t with hP_def
  set Y := x ^ (1 / 2 + 3 * ε)
  set s : ℕ → ℂ := fun k => ∑ t ∈ TT, (a t : ℂ) * (κ t : ℂ) ^ k with hs_def
  set R := (∑ k ∈ Finset.range o, s k * S.gsum (κ ^ k) x).re with hR_def
  have hx0 : 0 < x := by linarith
  have hP : 0 < P := Finset.sum_pos a_pos TT_nonempty
  have hc3 : 3 * (3 * (o : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ o := by exact_mod_cast ho
    linarith
  -- the powers of `x`
  have hY1 : x ^ (1 / 2 + ε) ≤ Y := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hY2 : x ^ (ε - 1) * x ^ (3 / 2 + ε) ≤ Y := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hY3 : x ^ (ε - 1) * x ^ (1 / 2 + ε) ≤ Y := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  -- Lemma T at every `u ∈ A₀`, `t ∈ TT` and `j`, summed, with Lemma Avg on the left
  have key := Finset.sum_le_sum fun u (hu : u ∈ A₀ κ) => Finset.sum_le_sum fun t ht =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => S.Th_le T2 u t (w u j) (w_pos u j) (a_pos t ht) hx
      (thick_near t ht u hu j) (thick_small t ht) (thin_far t ht u hu j) hthin
  have hRt : R = ∑ t ∈ TT, a t * (∑ k ∈ Finset.range o, (κ t : ℂ) ^ k * S.gsum (κ ^ k) x).re := by
    rw [hR_def]
    simp only [hs_def, Finset.sum_mul]
    rw [Finset.sum_comm, re_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← re_ofReal_mul, Finset.mul_sum]
    simp only [mul_assoc]
  have hL : ∑ u ∈ A₀ κ, ∑ t ∈ TT, ∑ _j : Fin m, S.Th T2 u t (a t / x) x = m * T2.card / (2 * o * x) * R := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, S.sum_Th κ thick_sub]
    rw [ho_def, hRt, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp
  have hRhs : ∑ u ∈ A₀ κ, ∑ t ∈ TT, ∑ j : Fin m,
      (S.ASK (a t) t (w u j) - S.MAIN (a t) (w u j) + a t / x ^ 2) =
      ∑ u ∈ A₀ κ, S.gap TT m a w u + (A₀ κ).card * (m * P / x ^ 2) := by
    simp only [Finset.sum_add_distrib, Setting.gap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hP_def, Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  -- the arithmetic: `R ≤ 4oPx^{1/2+3ε}`, from `m ≥ x^{1/2−ε}` and `|T2| ≥ x^{−ε}|A₀|`
  have hm : (0 : ℝ) < m := (Real.rpow_pos_of_pos hx0 _).trans_le words
  have hA0 : (0 : ℝ) < (A₀ κ).card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨1, mem_A₀.2 (map_one κ)⟩)
  have hT : (0 : ℝ) < T2.card := (mul_pos (Real.rpow_pos_of_pos hx0 _) hA0).trans_le thick_card
  have hA1 : (A₀ κ).card * x ^ ε * x ≤ m * T2.card * Y := by
    have e : x ^ (1 / 2 - ε) * x ^ (-ε) * x ^ (1 / 2 + 3 * ε) = x ^ ε * x := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']
      ring_nf
    calc _ = x ^ (1 / 2 - ε) * (x ^ (-ε) * (A₀ κ).card) * x ^ (1 / 2 + 3 * ε) := by
          linear_combination (-((A₀ κ).card : ℝ)) * e
      _ ≤ _ := by gcongr
  have hA2 : ((A₀ κ).card : ℝ) ≤ T2.card * Y := by
    calc _ = x ^ ε * (x ^ (-ε) * (A₀ κ).card) := by
          rw [← mul_assoc, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ Y * T2.card := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = _ := mul_comm _ _
  have hR : R ≤ 4 * o * Y * P := by
    refine le_of_mul_le_mul_left ?_ (div_pos (mul_pos hm hT) (by positivity : (0 : ℝ) < 2 * o * x))
    calc m * T2.card / (2 * o * x) * R ≤ (A₀ κ).card * x ^ ε * P + (A₀ κ).card * (m * P / x ^ 2) := by
          rw [← hL]
          refine key.trans ?_
          rw [hRhs]
          linarith
      _ = P * ((A₀ κ).card * x ^ ε * x + m * ((A₀ κ).card / x)) / x := by
          field_simp
      _ ≤ P * (m * T2.card * Y + m * (T2.card * Y)) / x := by
          gcongr
          exact (div_le_self (by positivity) hx).trans hA2
      _ = _ := by
          field_simp
          ring
  -- each `k`: the twists, the shares and the kept errors
  have hk (k : ℕ) (hk : k ∈ Finset.range o) :
      (if κ ^ k = 1 then 1 else (3 * (o : ℝ) + 1)⁻¹) * P * (S.g (false, false, κ ^ k) x).re ≤
        (s k * S.gsum (κ ^ k) x).re + P * (5 - 2 * if k = 0 then 1 else 0) * Y := by
    have hko := Finset.mem_range.1 hk
    have h1 := htw false true rfl k hko
    have h2 := htw true false rfl k hko
    have h3 := htw true true rfl k hko
    have hre : (S.g (false, false, κ ^ k) x).re - 3 * x ^ (1 / 2 + ε) ≤ (S.gsum (κ ^ k) x).re := by
      simp only [Setting.gsum, sub_re, add_re]
      linarith [neg_le_of_abs_le (abs_re_le_norm (S.g (false, true, κ ^ k) x)),
        re_le_norm (S.g (true, false, κ ^ k) x), re_le_norm (S.g (true, true, κ ^ k) x)]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · -- `k = 0`: no share, and `s 0 = Σ_t a_t`
      have hs0 : s 0 = (P : ℂ) := by simp [hs_def, hP_def]
      rw [ite_eq_left (pow_zero κ), hs0, re_ofReal_mul, ite_eq_left rfl]
      have := mul_le_mul_of_nonneg_left hre hP.le
      have := mul_le_mul_of_nonneg_left hY1 hP.le
      linarith
    · -- `0 < k < o`: `κ^k ≠ 1`, and `s k` is within `x^{ε−1}P` of `P/(3o + 1)`
      rw [ite_eq_right (fun h => hk0.ne' (hinj k hko h)), ite_eq_right hk0.ne']
      have hsh := shares k hk0 hko
      have hg := hkept k hk0 hko
      set c : ℝ := (3 * (o : ℝ) + 1)⁻¹
      set e := s k - ((c * P : ℝ) : ℂ) with he
      have hsplit : (s k * S.gsum (κ ^ k) x).re = c * P * (S.gsum (κ ^ k) x).re + (e * S.gsum (κ ^ k) x).re := by
        rw [show s k = ((c * P : ℝ) : ℂ) + e by rw [he]; ring, add_mul, add_re, re_ofReal_mul]
      have hnorm : ‖S.gsum (κ ^ k) x‖ ≤ x ^ (3 / 2 + ε) + 3 * x ^ (1 / 2 + ε) := by
        have n1 := norm_sub_le (S.g (false, false, κ ^ k) x + S.g (false, true, κ ^ k) x -
          S.g (true, false, κ ^ k) x) (S.g (true, true, κ ^ k) x)
        have n2 := norm_sub_le (S.g (false, false, κ ^ k) x + S.g (false, true, κ ^ k) x)
          (S.g (true, false, κ ^ k) x)
        have n3 := norm_add_le (S.g (false, false, κ ^ k) x) (S.g (false, true, κ ^ k) x)
        rw [Setting.gsum]
        linarith
      have he_re : -(x ^ (ε - 1) * P * (x ^ (3 / 2 + ε) + 3 * x ^ (1 / 2 + ε))) ≤
          (e * S.gsum (κ ^ k) x).re := by
        refine neg_le_of_abs_le ((abs_re_le_norm _).trans ?_)
        rw [norm_mul]
        exact mul_le_mul hsh hnorm (norm_nonneg _) (by positivity)
      have hc0 : 0 ≤ c * P := by positivity
      have hP3 : 3 * c * P * x ^ (1 / 2 + ε) ≤ P * Y := by
        calc 3 * c * P * x ^ (1 / 2 + ε) = P * (3 * c * x ^ (1 / 2 + ε)) := by ring
          _ ≤ P * (1 * Y) := mul_le_mul_of_nonneg_left (mul_le_mul hc3 hY1 (by positivity) zero_le_one) hP.le
          _ = P * Y := by ring
      have hP4 : x ^ (ε - 1) * P * (x ^ (3 / 2 + ε) + 3 * x ^ (1 / 2 + ε)) ≤ 4 * P * Y := by
        calc _ = P * (x ^ (ε - 1) * x ^ (3 / 2 + ε) + 3 * (x ^ (ε - 1) * x ^ (1 / 2 + ε))) := by ring
          _ ≤ P * (Y + 3 * Y) :=
            mul_le_mul_of_nonneg_left (add_le_add hY2 (mul_le_mul_of_nonneg_left hY3 (by norm_num))) hP.le
          _ = 4 * P * Y := by ring
      have := mul_le_mul_of_nonneg_left hre hc0
      linarith
  -- the sum over `k`
  have hsum : ∑ k ∈ Finset.range o, (5 - 2 * if k = 0 then (1 : ℝ) else 0) = 5 * o - 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' (Finset.range o) 0,
      ite_eq_left (Finset.mem_range.2 ho)]
    simp [mul_comm]
  have htot : P * S.cyclicG κ x ≤ R + P * (5 * o - 2) * Y := by
    have h := Finset.sum_le_sum hk
    rw [Finset.sum_add_distrib, ← re_sum, ← hR_def, ← Finset.sum_mul, ← Finset.mul_sum, hsum] at h
    rw [Setting.cyclicG, ho_def, Finset.mul_sum]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => by ring) h
  have : P * S.cyclicG κ x ≤ P * ((9 * o - 2) * Y) := by nlinarith
  exact le_of_mul_le_mul_left this hP

/-! ## `ζ` -/

/-- **Theorem Z for `ζ`** (`κ = 1`): balance data at `x`, in a setting thin at `X` with small twists, bound the error
of `ζ`'s ramp sum by `7x^{1/2+3ε}`. -/
theorem BalanceData.zeta_le {S : Setting} {x ε X : ℝ} (D : BalanceData S 1 x ε X) (hthin : S.Thin x X)
    (htw : S.Twists 1 x ε) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x ≤
      7 * x ^ (1 / 2 + 3 * ε) := by
  have h := D.cyclicG_le hthin htw (fun k hk hk' => absurd hk' (by rw [orderOf_one]; omega)) hx hε
  rwa [S.cyclicG_one, S.g_one_re, orderOf_one, Nat.cast_one, show (9 : ℝ) * 1 - 2 = 7 by norm_num] at h

/-- **The frontier for `ζ` after step 3**: for every `ε > 0`, at every `x` of windows `[Y, Y^λ]` with `Y` arbitrarily
large, a setting thin at some `X`, with small twists, and balance data for `κ = 1`. -/
def ZetaBalanceBound : Prop :=
  ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam),
    ∃ (S : Setting) (X : ℝ), S.Thin x X ∧ S.Twists 1 x ε ∧ Nonempty (BalanceData S 1 x ε X)

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

/-! ## Every primitive character -/

/-- Two characters with the same values, at levels that are equal only propositionally, have the same ramp error. -/
theorem rampErr_congr {M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M') {ψ : DirichletCharacter ℂ M}
    {ψ' : DirichletCharacter ℂ M'} (hv : ∀ n : ℕ, ψ n = ψ' n) (y : ℝ) :
    WindowGRH.rampErr ψ y = WindowGRH.rampErr ψ' y := by
  subst h
  obtain rfl : ψ = ψ' := MulChar.ext' fun x => by rw [← ZMod.natCast_zmod_val x]; exact hv x.val
  rfl

/-- The primitive character of `ψ` changed to a higher level has the ramp error of `ψ*`. -/
theorem rampErr_prim_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N) (ψ : DirichletCharacter ℂ M)
    (y : ℝ) : WindowGRH.rampErr (changeLevel h ψ).primitiveCharacter y = WindowGRH.rampErr ψ.primitiveCharacter y :=
  rampErr_congr (conductor_changeLevel ψ h) (prim_changeLevel h ψ) y

namespace Setting

variable (S : Setting)

/-- **`κ` lifts `χ`**: `f ∣ QS`, and `κ̃`, the character `n ↦ κ([n]_A)` mod `QS`, is `χ` at level `QS`. Such a `κ`
exists exactly when `K ⊆ ker χ`, as for the archive's `K = {u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`; its kernel is the
image of `ker χ`. -/
def Lifts (κ : S.A →* ℂˣ) {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) : Prop :=
  ∃ h : f ∣ S.QS, S.lift κ = changeLevel h χ

variable {S} {κ : S.A →* ℂˣ} {f : ℕ} [NeZero f] {χ : DirichletCharacter ℂ f}

/-- `κ^n = 1` exactly when `χ^n = 1`. -/
theorem Lifts.pow_eq_one_iff (hL : S.Lifts κ χ) (n : ℕ) : κ ^ n = 1 ↔ χ ^ n = 1 := by
  obtain ⟨h, hl⟩ := hL
  rw [← changeLevel_eq_one_iff h, map_pow, ← hl, ← S.lift_pow]
  exact ⟨fun e => by rw [e, S.lift_one], S.eq_one_of_lift_eq_one⟩

/-- `κ` and `χ` have the same order. -/
theorem Lifts.orderOf_eq (hL : S.Lifts κ χ) : orderOf κ = orderOf χ :=
  orderOf_eq_orderOf_iff.2 hL.pow_eq_one_iff

/-- `g_{(0,0,κ^k)} = E_{(χ^k)*}`: `D_{(0,0,κ^k)}` is `χ^k` at the level `N`. -/
theorem Lifts.g_pow (hL : S.Lifts κ χ) (k : ℕ) (y : ℝ) :
    S.g (false, false, κ ^ k) y = WindowGRH.rampErr (χ ^ k).primitiveCharacter y := by
  obtain ⟨h, hl⟩ := hL
  have hD : S.D (false, false, κ ^ k) = changeLevel (h.trans S.QS_dvd_N) (χ ^ k) := by
    rw [changeLevel_trans _ h S.QS_dvd_N, map_pow, ← hl, ← S.lift_pow]
    simp [D, legPow]
  rw [g]
  exact rampErr_congr (by rw [hD, conductor_changeLevel]) (fun n => by rw [hD, prim_changeLevel]) y

/-- **The cyclic family**: for `κ` lifting `χ`, the weighted error of the characters `κ^k` is
`(WindowGRH.cyclic χ).G`, the error of the cyclic family of `χ`. -/
theorem Lifts.cyclicG_eq (hL : S.Lifts κ χ) (x : ℝ) : S.cyclicG κ x = (WindowGRH.cyclic χ).G x := by
  rw [cyclicG, hL.orderOf_eq, ← Fin.sum_univ_eq_sum_range, WindowGRH.Family.G]
  refine Finset.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite χ)) (by simp) fun k _ => ?_
  change _ = (if χ ^ (k : ℕ) = 1 then 1 else (3 * (orderOf χ : ℝ) + 1)⁻¹) *
    (WindowGRH.rampErr (χ ^ (k : ℕ)).primitiveCharacter x).re
  simp only [hL.pow_eq_one_iff, hL.g_pow]

end Setting

/-- `‖R_f(x)‖ ≤ x log x (1 + log x)` for `‖f‖ ≤ 1` and `x ≥ 1`: `Λ(n) ≤ log x`, and `Σ_{n ≤ x} 1/n ≤ 1 + log x`. -/
theorem norm_rampSum_le_log {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖RampLaplace.rampSum f x‖ ≤ x * Real.log x * (1 + Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ‖RampLaplace.rampSum f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, x * Real.log x * (n : ℝ)⁻¹ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
        have h1' : (1 : ℝ) ≤ n := by exact_mod_cast h1
        have h2' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 h2
        have hΛ : Λ n ≤ Real.log x := vonMangoldt_le_log.trans (Real.log_le_log (by linarith) h2')
        have hr : 0 ≤ x / n - 1 := by rw [sub_nonneg, le_div_iff₀ (by linarith)]; linarith
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
          Real.norm_of_nonneg hr]
        calc Λ n * ‖f n‖ * (x / n - 1) ≤ Real.log x * 1 * (x / n) :=
              mul_le_mul (mul_le_mul hΛ (hf n) (norm_nonneg _) hl) (by linarith) hr (by positivity)
          _ = x * Real.log x * (n : ℝ)⁻¹ := by ring
    _ = x * Real.log x * harmonic ⌊x⌋₊ := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ x * Real.log x * (1 + Real.log x) := by
        have hfl : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.2 hx
        gcongr
        exact (harmonic_le_one_add_log _).trans (by gcongr; exact Nat.floor_le hx0)

/-- **A crude bound**: `‖E_ψ(x)‖ ≤ x^{3/2+ε}` for every large `x`. It comes from `‖R_ψ(x)‖ ≤ x log x (1 + log x)`
(`norm_rampSum_le_log`) and `log x ≤ 4x^{1/4}`; it bounds the kept errors in Theorem Z. -/
theorem eventually_norm_rampErr_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in Filter.atTop, ‖WindowGRH.rampErr ψ x‖ ≤ x ^ (3 / 2 + ε) := by
  set K := ‖logDeriv (LFunction ψ) 1‖
  filter_upwards [Filter.eventually_ge_atTop 1, (tendsto_rpow_atTop hε).eventually_ge_atTop (26 + K)] with x hx hxε
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hK : 0 ≤ K := norm_nonneg _
  set v := x ^ (1 / 4 : ℝ) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hx (by norm_num)
  have hlv : Real.log x ≤ 4 * v := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [hv]
    linarith
  have hv2 : x ^ (3 / 2 : ℝ) = x * v ^ 2 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_one_add' hx0.le (by norm_num)]
    norm_num
  -- `‖E_ψ(x)‖ ≤ ‖R_ψ(x)‖ + x log x + 2x + xK`, in both cases of `rampErr`
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hR := norm_rampSum_le_log (f := fun n => ψ n) (fun n => ψ.norm_le_one _) hx
  have hE : ‖WindowGRH.rampErr ψ x‖ ≤
      ‖RampLaplace.rampSum (fun n => ψ n) x‖ + x * Real.log x + 2 * x + x * K := by
    unfold WindowGRH.rampErr
    split_ifs
    · calc _ ≤ ‖RampLaplace.rampSum (fun n => ψ n) x‖ + ‖((x * Real.log x : ℝ) : ℂ)‖ +
            ‖(((1 + Real.eulerMascheroniConstant) * x : ℝ) : ℂ)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ _ := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
              Real.norm_of_nonneg (by positivity)]
            nlinarith
    · calc _ ≤ ‖RampLaplace.rampSum (fun n => ψ n) x‖ + ‖(x : ℂ) * logDeriv (LFunction ψ) 1‖ := norm_add_le _ _
        _ = ‖RampLaplace.rampSum (fun n => ψ n) x‖ + x * K := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
        _ ≤ _ := by nlinarith
  -- `log x (2 + log x) ≤ 24v²`, so `‖E_ψ(x)‖ ≤ (26 + K) x v² = (26 + K) x^{3/2}`
  have hlog2 : Real.log x * (2 + Real.log x) ≤ 24 * v ^ 2 := by
    have := mul_le_mul hlv (by linarith : 2 + Real.log x ≤ 2 + 4 * v) (by positivity) (by positivity)
    nlinarith
  have hxv : x ≤ x * v ^ 2 := le_mul_of_one_le_right hx0.le (one_le_pow₀ hv1)
  have h3 := mul_le_mul_of_nonneg_left hlog2 hx0.le
  calc ‖WindowGRH.rampErr ψ x‖ ≤ (26 + K) * x ^ (3 / 2 : ℝ) := by
        rw [hv2]
        nlinarith [mul_le_mul_of_nonneg_left hxv hK]
    _ ≤ x ^ ε * x ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right hxε (by positivity)
    _ = x ^ (3 / 2 + ε) := by rw [← Real.rpow_add hx0, add_comm]

/-- **The frontier for every primitive character after step 3**: for every primitive `χ` and `ε > 0`, at every `x`
of windows `[Y, Y^λ]` with `Y` arbitrarily large, a setting with a character `κ` of `A` lifting `χ`
(`Setting.Lifts`), thin at some `X`, with small twists, and balance data. For `χ = 1` it is `ZetaBalanceBound`. -/
def BalanceBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ,
    ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam), ∃ (S : Setting) (κ : S.A →* ℂˣ) (X : ℝ), S.Lifts κ χ ∧ S.Thin x X ∧
      S.Twists κ x ε ∧ Nonempty (BalanceData S κ x ε X)

/-- **Theorem E for every primitive character**: the frontier gives `WindowGRH.WindowBound`, with `C = 9o − 2`. -/
theorem windowBound_of_balanceBound (h : BalanceBound) : WindowGRH.WindowBound := by
  intro f _ χ hχ θ hθ
  have hε : 0 < (θ - 1 / 2) / 3 := by linarith
  obtain ⟨lam, hlam, hY⟩ := h f χ hχ _ hε
  -- the kept errors are eventually at most `x^{3/2+ε}`
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 fun k : Fin (orderOf χ) =>
    eventually_norm_rampErr_le (χ ^ (k : ℕ)).primitiveCharacter hε)
  refine ⟨lam, hlam, 9 * orderOf χ - 2, fun Y₀ => ?_⟩
  obtain ⟨Y, hY₀, hYx⟩ := hY (max Y₀ (max x₀ 1))
  refine ⟨Y, (le_max_left _ _).trans hY₀, fun x hx => ?_⟩
  have hYx' : max x₀ 1 ≤ x := (le_max_right _ _).trans (hY₀.trans hx.1)
  obtain ⟨S, κ, X, hL, hthin, htw, ⟨D⟩⟩ := hYx x hx
  have := D.cyclicG_le hthin htw (fun k _ hk => by
      rw [hL.g_pow]
      exact hx₀ x ((le_max_left _ _).trans hYx') ⟨k, hL.orderOf_eq ▸ hk⟩)
    ((le_max_right _ _).trans hYx') hε.le
  rwa [hL.cyclicG_eq, hL.orderOf_eq, show 1 / 2 + 3 * ((θ - 1 / 2) / 3) = θ by ring] at this

/-- **The Riemann hypothesis for `ζ` and every Dirichlet `L`-function from balance data on windows**, for every
primitive character. -/
theorem rhAndGRH_of_balanceBound (h : BalanceBound) : HalfPlaneGRH.RHandGRH :=
  WindowGRH.rhAndGRH_of_windowBound (windowBound_of_balanceBound h)

end ZetaBalance

#print axioms ZetaBalance.BalanceData.cyclicG_le
#print axioms ZetaBalance.BalanceData.zeta_le
#print axioms ZetaBalance.riemannHypothesis_of_zetaBalanceBound
#print axioms ZetaBalance.rhAndGRH_of_balanceBound
