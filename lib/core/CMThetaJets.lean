import CMThetaOne
import EllipticLegendre

/-!
# The jets of the one-variable CM theta, with Legendre's relation proved

`CMThetaOne` proves Masser's half-period identity, Hurwitz's formula and the rationality and integrality of the jets
of `th0` from Legendre's relation `η₁ω₂ − η₂ω₁ = 2πi` (`CMThetaOne.Legendre`), taken there as a hypothesis.
`EllipticLegendre.legendre` proves it, so each of those theorems holds without it; this module states them so.

**Unconditional.** Masser's half-period identity (`zetaW_half'`) and Hurwitz's formula (`th0_taylor'`); every jet of
`th0` at a half-period is a polynomial over `ℤ` in `g₂/2`, `℘(t)` and `s₂` (`th0_jets_mem'`, `th0_jets_mem_closure'`),
so it lies in `σ₀(K)`, is algebraic and is `ℓ`-integral for `ℓ ≠ 2` wherever these do or are
(`th0_jets_mem_range'`, `th0_jets_isAlgebraic'`, `th0_jets_int'`); at the construction's lattice and point
`t = δ/2`, the jets lie in `σ₀(K)` when `g₂`, `℘(t)` and `s₂` do (`canon_jets_mem_range'`).

**From the CM inputs alone.** With CM-c (`CMThetaOne.CMjIntegral`) and CM-d (`CMThetaOne.CMs2`), the jets at the
construction's lattice are algebraic and integral at every prime `ℓ ≥ 5`, `ℓ ∤ d` (`canon_jets_isAlgebraic'`,
`canon_jets_int'`).
-/

namespace CMThetaOne

noncomputable section

open PeriodPair ThetaChain ThetaNorm ChainCanon Complex
open EllipticLegendre (legendre)

/-- **Masser's half-period identity**: `ζ_W(t) − s₂t − (π/A)·t̄ = 0` at every half-period `t`, with the orientation
`Im(ω₂/ω₁) > 0`. -/
theorem zetaW_half' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) : zetaW Λ t - s2 Λ * t - (Real.pi / area Λ : ℝ) * (starRingEnd ℂ) t = 0 :=
  zetaW_half legendre Λ hor t ht ht'

/-- **The Hurwitz formula for `th0`**: `∂^n th0(0) = n!·[zⁿ]exp(logTh0)` at every half-period. -/
theorem th0_taylor' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 =
      (n.factorial : ℂ) * PowerSeries.coeff n ((PowerSeries.exp ℂ).subst (logTh0 Λ t)) :=
  th0_taylor legendre Λ hor t ht ht' n

/-- **The jets of `th0` are polynomials over `ℤ` in `g₂/2`, `℘(t)`, `s₂`**: at a half-period, every `∂^n th0(0)` lies in
every subring of `ℂ` containing these three numbers. -/
theorem th0_jets_mem' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) {R : Subring ℂ} (h2 : Λ.g₂ / 2 ∈ R) (hp : Λ.weierstrassP t ∈ R) (hs : s2 Λ ∈ R)
    (n : ℕ) : iteratedDeriv n (th0L Λ t) 0 ∈ R :=
  th0_jets_mem legendre Λ hor t ht ht' h2 hp hs n

/-- **The jets of `th0` lie in `ℤ[g₂/2, ℘(t), s₂]`.** -/
theorem th0_jets_mem_closure' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 ∈ Subring.closure {Λ.g₂ / 2, Λ.weierstrassP t, s2 Λ} :=
  th0_jets_mem_closure legendre Λ hor t ht ht' n

/-- **The jets of `th0` lie in `σ₀(K)`** when `g₂`, `℘(t)`, `s₂` do. -/
theorem th0_jets_mem_range' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) {K : Type*} [Field K] (σ₀ : K →+* ℂ) (h2 : Λ.g₂ ∈ Set.range σ₀)
    (hp : Λ.weierstrassP t ∈ Set.range σ₀) (hs : s2 Λ ∈ Set.range σ₀) (n : ℕ) :
    iteratedDeriv n (th0L Λ t) 0 ∈ Set.range σ₀ :=
  th0_jets_mem_range legendre Λ hor t ht ht' σ₀ h2 hp hs n

/-- **The jets of `th0` are algebraic** when `g₂`, `℘(t)`, `s₂` are. -/
theorem th0_jets_isAlgebraic' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) (h2 : IsAlgebraic ℚ Λ.g₂) (hp : IsAlgebraic ℚ (Λ.weierstrassP t))
    (hs : IsAlgebraic ℚ (s2 Λ)) (n : ℕ) : IsAlgebraic ℚ (iteratedDeriv n (th0L Λ t) 0) :=
  th0_jets_isAlgebraic legendre Λ hor t ht ht' h2 hp hs n

/-- **The jets of `th0` are `ℓ`-integral** at every prime `ℓ ≠ 2` where `g₂`, `℘(t)`, `s₂` are, for any ring map
`ι : ℂ → ℂ_ℓ`. -/
theorem th0_jets_int' (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (t : ℂ) (ht : 2 * t ∈ Λ.lattice)
    (ht' : t ∉ Λ.lattice) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {F : Type*} [FunLike F ℂ ℂ_[ℓ]]
    [RingHomClass F ℂ ℂ_[ℓ]] (ι : F) (h2 : ‖ι Λ.g₂‖ ≤ 1) (hp : ‖ι (Λ.weierstrassP t)‖ ≤ 1)
    (hs : ‖ι (s2 Λ)‖ ≤ 1) (n : ℕ) : ‖ι (iteratedDeriv n (th0L Λ t) 0)‖ ≤ 1 :=
  th0_jets_int legendre Λ hor t ht ht' ℓ hℓ ι h2 hp hs n

/-- **The canonical jets are algebraic** (from CM-c and CM-d): every `∂^n th0(0)` of the canonical one-variable theta
at `t = δ/2` is an algebraic number. -/
theorem canon_jets_isAlgebraic' (hj : CMjIntegral) (hs : CMs2) {d : ℕ} (hd : Squarefree d) (hd4 : d % 4 = 3)
    {sd : ℝ} (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (n : ℕ) :
    IsAlgebraic ℚ (iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0) :=
  canon_jets_isAlgebraic legendre hj hs hd hd4 hsd hΔ n

/-- **The canonical jets are `ℓ`-integral** at every prime `ℓ ≥ 5`, `ℓ ∤ d` (from CM-c and CM-d). -/
theorem canon_jets_int' (hj : CMjIntegral) (hs : CMs2) {d : ℕ} (hd : Squarefree d) (hd4 : d % 4 = 3) {sd : ℝ}
    (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
    (hℓd : ¬ ℓ ∣ d) (ι : ℂ ≃+* ℂ_[ℓ]) (n : ℕ) :
    ‖ι (iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0)‖ ≤ 1 :=
  canon_jets_int legendre hj hs hd hd4 hsd hΔ ℓ hℓ hℓd ι n

/-- **The canonical jets lie in `σ₀(K)`** when `g₂`, `℘(t)` and `s₂` of the canonical lattice do. -/
theorem canon_jets_mem_range' {sd : ℝ} (hsd : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) {K : Type*} [Field K]
    (σ₀ : K →+* ℂ) (h2 : (cmLat sd).g₂ ∈ Set.range σ₀) (hp : (cmLat sd).weierstrassP (tC sd) ∈ Set.range σ₀)
    (hs : s2 (cmLat sd) ∈ Set.range σ₀) (n : ℕ) :
    iteratedDeriv n (th0 (sC sd) (sgStar (cmLat sd)) (tC sd)) 0 ∈ Set.range σ₀ :=
  canon_jets_mem_range legendre hsd hΔ σ₀ h2 hp hs n

end

end CMThetaOne
