import GainLoss2
import GainErrors

/-!
# The gain's numbers

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7d of the gain's numbers, the
assembly): `gain_numbers`, the inequality between the frontier's ask, the forced orders and the gain's exponents
that the certificate of the gain reads (`SharpObj.gain_of_cert`, through `log_norm_gain_map`), for every `κ`.

**The statement** (`gain_numbers`, the spec's). At an admissible design with parameters (`Adm`, `FamAt`), under the
2-adic structure `S.TwoAdic κ e`, the clause G1 (`FewBadTops`), the growth package `GainBig ε x` and error data
meeting `ErrOK`, for every real `col ≤ c_G/6`:
`Σ_t Σ_j ASK(a_t, t, w_{u,j}) − m(Σ_t a_t)·log(g₀g₁) + Fo − c_G ≤ Σ_ϖ n_ϖ·log N(ϖ) − col`.

**The chain.** With `lg = log(g₀g₁)`:
* `Σ_t Σ_j ASK = Σ_t Σ_j (Σ_{p ∈ askSupp} 2 log p·askU + log d·askAtD)` (`ask_eq_sum`, exact), and `askU = askE` at
  every `p ∈ askSupp` (`askU_eq_askE`, exact at every `κ`: the twisted tops);
* the losses: that is at most `Σ_{p ∈ inertPrimes(X″)} 2 log p·(Σ_j G_j(p) − τ_p) + c_G/4` (`losses_le`);
* the exponent sum: `Σ_{inertPrimes} 2 log p·(Σ_j G_j − τ) = Σ_ϖ s_ϖ·log N(ϖ) − Σ_ϖ F·log N + Σ_ϖ E·log N`
  (`sum_sExp_logN`), with `Σ_ϖ F·log N = Fo` (`sum_Fexp_eq_Fo`);
* the errors: `Σ_ϖ E·log N − m(Σ_t a_t)·lg ≤ c_G/4` (`errors_le`);
* the rounding: `Σ_ϖ s_ϖ·log N(ϖ) ≤ Σ_ϖ n_ϖ·log N(ϖ) + Σ_ϖ log N(ϖ)` (`sum_round_ge`) and `Σ_ϖ log N(ϖ) ≤ c_G/12`
  (`rounding_le`).
So the left side is at most `Σ_ϖ n_ϖ·log N(ϖ) − c_G + c_G/4 + c_G/4 + c_G/12 = Σ_ϖ n_ϖ·log N(ϖ) − 5c_G/12`, and
`col ≤ c_G/6 ≤ 5c_G/12` as `c_G ≥ 0` (`cG_le`).

**Against the spec.**
* No hypothesis `twA κ = 1`: the bridge `askU_eq_askE` holds at every `κ`, as the design puts the top data of the
  translate `t` at the place `(1, c·t)`, `c = twA κ` (twisted tops, `SharpAdm`).
* `Dg.m` and `Dg.R.m` are the same number (`Dg.hm`); the statement keeps the frontier's `Dg.m`.
-/

open Finset

namespace ZetaBalance

noncomputable section

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X}

/-- **The frontier's ask in the gain's coordinates**: `Σ_t Σ_j ASK(a_t, t, w_{u,j}) =
Σ_t Σ_j (Σ_{p ∈ askSupp} 2 log p·askE + log d·askAtD)` at an admissible design, for every `κ` (`ask_eq_sum`,
`askU_eq_askE`). -/
theorem ask_eq_sum_askE (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) :
    ∑ t ∈ Dg.TT, ∑ j, S.ASK (Dg.a t) t (Dg.w u j) =
      ∑ t ∈ Dg.TT, ∑ J, ((∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t) +
        Real.log S.d * Dg.askAtD u J t) := by
  rw [ask_eq_sum hA hF u]
  refine sum_congr rfl fun t _ => sum_congr rfl fun J _ => ?_
  congr 1
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨-, hp', hN, hcls⟩ := mem_filter.1 hp
  rw [Dg.askU_eq_askE u J hp' hN hcls t]

/-- **The gain's numbers** (M-G7d): at an admissible design, under `TwoAdic`, G1, `GainBig` and `ErrOK`, for every
`col ≤ c_G/6`, `Σ_t Σ_j ASK(a_t, t, w_{u,j}) − m(Σ_t a_t)·log(g₀g₁) + Fo − c_G ≤ Σ_ϖ n_ϖ·log N(ϖ) − col`, for every
`κ`: the ask in the gain's coordinates (`ask_eq_sum_askE`), the losses (`losses_le`), the exponent sum and the
forced orders (`sum_sExp_logN`, `sum_Fexp_eq_Fo`), the errors (`errors_le`) and the rounding (`sum_round_ge`,
`rounding_le`) leave `Σ_ϖ n_ϖ·log N(ϖ) − 5c_G/12`. -/
theorem gain_numbers (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) {e : ℕ} (h2 : S.TwoAdic κ e)
    (hG1 : Dg.FewBadTops) (hB : GainBig ε x) (u : S.A) (ED : ErrData S Dg.R) (hED : Dg.ErrOK u ED)
    {col : ℝ} (hcol : col ≤ S.cGform x ε / 6) :
    ∑ t ∈ Dg.TT, ∑ j, S.ASK (Dg.a t) t (Dg.w u j) - Dg.m * (∑ t ∈ Dg.TT, Dg.a t) * Real.log (Dg.g₀ * Dg.g₁) +
        Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) - S.cGform x ε ≤
      ∑ ϖ ∈ Dg.primeSet ED, (Dg.nExp pr u ED ϖ : ℝ) * Dg.logN u ϖ - col := by
  have hL := losses_le hA hF h2 hG1 hB u
  have hs := sum_sExp_logN (Dg := Dg) pr u ED
  have hFo := sum_Fexp_eq_Fo (Dg := Dg) u ED
  have hE := errors_le hA hF h2 hB u ED hED
  have hr := sum_round_ge (Dg := Dg) pr u ED
  have hR := rounding_le hA hB u ED hED
  have hc := (cG_le hA).1
  have hm : (Dg.m : ℝ) = Dg.R.m := by rw [Dg.hm]
  rw [ask_eq_sum_askE hA hF u, hm]
  linarith

end SharpDesign

end

end ZetaBalance
