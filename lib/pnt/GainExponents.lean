import DesignOrbits
import SharpCons
import ForcedOrders
import GenIndex

/-!
# The gain's exponents

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G6 of the gain spec): the local
exponents of the gain at a design, as explicit functions of the design `Dg`, its top shifts (`DesignPar.bT`), the
translate `u`, the word's error data (`ErrData`) and the constant package `Kg` (`GainConsts`); the prime elements of
`ℚ(√−d)` that carry them; and the elements `α₀ = ∏_{s_ϖ ≥ 0} ϖ^{⌊s_ϖ⌋}`, `β₀ = ∏_{s_ϖ < 0} ϖ^{⌈−s_ϖ⌉}` whose images
generate `𝔞⁺`, `𝔞⁻` in the construction (the gain spec, C1). The bookkeeping that sums the exponents against the
frontier's `ASK` and `Fo` (M-G7), and the local theorems that realise them, read the definitions here.

**Orbit data** (`DesignOrbits`). At an inert or signal `p` with the twist `c = twA κ` the step is `σ_p = orbitStep c p`;
the orbits that carry tops are those of the base points `basePoint σ_p (TT)` (`basePts`), with tops `topsOn p t₀`; a
top is V-type at an even position (`IsVType`), its partner at step `e` is `pos_p(1, s; e)`, and a collision is
`Setting.Collides`. The weights are `w_j(z) = e_J(z)` of `hc u` (`wt`, lift `j = J + 1`), shifted
`w̃_j(z) = w_j(z) − (k + (2j − 1)(t + 1))/2` (`wsh`); `c₀ = 16kΔ` (`c0`), `S_c = 4kΔ` (`cloud`) and `η = 2mH` (`eta`).

**Per orbit** (the gain spec, §2.5): `ā_s = a_s − 2c₀` (`abar`), `cap_{s,e} = w̃_j(partner(s, e)) + c₀` (`cap`),
`γ_p = p/(p² − 1)` (`gamP`), the slack (`sl`), the trivial gain `g^{tr}` (`gTr`), the served gain `g^{sv}` (`gSv`), the
penalty (`pen`), the depth (`dep`, with `c_dep` (`cDep`) and the nearest V-top `vPrev` before a top, at the distance
`vDist`), the denominator exponent `D_p` (`Dexp`), the sandwich exponent `e_p` (`eSand`), and the served set `S_p`
(`served`: the good base points at a candidate).

**Per prime and lift**: the gain `G_j(p)` (`gainG`), the depth `τ_p` (`tau`), the forced orders `F_j` (`Fexp`, the
summands of `ForcedOrders.Fo`) and the error exponents `E_j` (`Eexp`; at inert and signal `p` it is `Einert`, which
reads the plus-sign forced order `Fplus`, the minus-sign places `Setting.minusPlaces` and the tops among them
`topsMinus`; at the cut it is `errT`).

**The prime elements** (`GainPrime`, the gain spec §2.2): the rational primes (`rat p`: the inert and signal `p ≤ X″`
and the primes of `D_Γ`), `g₀`, `g₁` (`gi i`), `π̄_i` (`gbar i`), the cut element `π_T` (`cut`) and `√−d` (`sqrtd`),
with their elements of `O_E` (`elt`) and their `log N_{F/ℚ}` (`logN`: `2 log p`, `2 log g_i`, `log g_i`, `log T`,
`log d`), indexed by `primeSet`. The real exponents are `s_ϖ = Σ_j (G_j(ϖ) + F_j(ϖ) − E_j(ϖ)) − τ(ϖ)` (`sExp`; `G` and
`τ` live at the rational primes, `Gexp`, `tauE`), the integer ones `n_ϖ = ⌊s_ϖ⌋` (`nExp`), and `α₀`, `β₀` are
`gainAlpha₀`, `gainBeta₀`.

**Theorems.**
* `α₀, β₀ ≠ 0` (`gainAlpha₀_ne_zero`, `gainBeta₀_ne_zero`), as every prime element is (`elt_ne_zero`).
* **The norm** (`log_norm_gain`): `λ(α₀/β₀) = Σ_ϖ n_ϖ·λ(ϖ)` for the normalised log-norm `λ(γ) = 2·log|N_{E/ℚ}γ|/[E:ℚ]`
  (`Setting.lnorm`), which is `log N_{F/ℚ}γ` on `F = ℚ(√−d)`, as `α₀/β₀ = ∏_ϖ ϖ^{n_ϖ}` (`gainAlpha₀_div_gainBeta₀`).
  With `λ(ϖ) = log N(ϖ)` (`lnorm_elt`: `N(p) = p^{[E:ℚ]}`, `N(conj z) = N(z)`, `π·π̄ = g`, `(√−d)² = −d`, under
  `d ≡ 3 (mod 4)`, A11's data at `g₀, g₁` and `ArithT` at the auxiliary prime) it is `Σ_ϖ n_ϖ·log N(ϖ)`
  (`log_norm_gain_logN`), and through any `τ : E → K` it is the certificate's norm term
  `(2/[K:ℚ])·log|N_{K/ℚ}(τα₀/τβ₀)|` (`log_norm_gain_map`; `SharpObj.GainCert.idx_ge`).
* **Rounding** (`abs_sum_round_le`, `sum_round_ge`): `|Σ_ϖ (n_ϖ − s_ϖ)·log N(ϖ)| ≤ Σ_ϖ log N(ϖ)`, as
  `s_ϖ − 1 < n_ϖ ≤ s_ϖ` and `log N(ϖ) ≥ 0`.
* **The gain's size** (`gainG_le`, `gain_le`): `0 ≤ G_j(p) ≤ γ_p·Σ_{t ∈ TT} a_t ≤ 4|TT|·a/p`, when the caps and the
  penalties of the served orbits are nonnegative and `0 ≤ a_t ≤ 2a` (as at an admissible design).
* **Signs** (the parts the spec calls `≥ 0`): `G_j(p)` (`gainG_nonneg`), the slack (`sl_nonneg`), the error exponents
  at the rational primes (`Eexp_rat_nonneg`), at `g_i` net of the forced order (`Eexp_gi_sub_nonneg`) and at the cut
  (`errT_nonneg`); the forced orders are `≥ 0` at the rational primes (`Fexp_rat_nonneg`) and `≤ 0` at `g_i` and `√−d`
  (`Fexp_gi_nonpos`, `Fexp_sqrtd_nonpos`).
* The exponents of the special elements in closed form (`sExp_gi`, `sExp_gbar`, `sExp_cut`, `sExp_sqrtd`), at the
  rational primes beyond `X″` (`sExp_rat_of_not_mem`), `G`, `τ` off `inertPrimes(X″)` (`gainG_eq_zero`,
  `tau_eq_zero`), and a sum over `primeSet` by kinds (`sum_primeSet`).

**Choices** (where §2.5 is ambiguous: the reading that makes M-G7's statements provable).
* The exponents of the sums are the odd `e = 2i + 1`, `i ≤ log_p⌈2a⌉` (`gainExps`): every odd `e` with `p^e ≤ 2a`.
  Beyond, `ā_s/p^e < 1` and the terms vanish once the caps are `≥ 1` (at an admissible design `w ≥ w″`), and so do the
  terms of `ASK` (`a_t ≤ 2a`, `w ≥ 1`).
* The served gain is `Σ_{V-tops} γ_p·ā_s + Σ_{other tops} Σ_e (ā_s/p^e − cap_{s,e})⁺ − sl`, the spec's
  `γ_p·Σ_s ā_s − Σ_{non-V s}Σ_e min(ā_s/p^e, cap_{s,e}) − sl` by `γ_p·ā − Σ_e min(ā/p^e, cap) = Σ_e (ā/p^e − cap)⁺`
  over all odd `e`; so no series is left but `γ_p`.
* Only the orbits that carry tops are summed and served (`basePts`): an orbit without tops has `g^{tr⁺} = 0` and
  `g^{sv} − pen < 0`, but would cost `m(⌈dep⌉ + D_p + 1)` in `τ_p` if it were served.
* The served set also asks `p ∈ inertPrimes(X″)` (true for a candidate at an admissible design, `p < X′ ≤ X″`), so
  that `G` and `τ` vanish off `inertPrimes(X″)`. `τ_p = 0` when `S_p = ∅`, `e_p` included.
* `r` in `pen`, `dep` and `D_p` is the tile rank `r = K + 1` (`tilePar`), the rank of the second local theorem; `N₁`,
  `G′`, `L₁(p)`, `La`, `p₀` are those of `DesignOrbits`. `log_p` is `Real.logb p`.
* The nearest V-top `y′` before a top `y` is the one at the cyclic distance `prevV` back along the orbit (`vDist`,
  `vPrev`); the term `min(b_y, a_{y′}/p^{d(y)})` is `0` when there is none.
* Forced orders on the prime elements: `FInert` on `p`, `FTypeG` on `g_i`, `2·FRamD` on `√−d` (`d = −(√−d)²`), and `0`
  on `π̄_i`, `π_T`; so `Σ_ϖ F_j(ϖ)·log N(ϖ)` is the lift's summand of `ForcedOrders.Fo`.
* Error exponents: on `p`, `Einert` at the inert and signal `p ≤ X″`, plus `v_p(D_Γ)`; on `g_i`,
  `FTypeG + c_E·f·(N_m² + m²η)` (net exponent `−m·c_E·f·(N_m² + m²η)`); on `π̄_i`, `ν(j)`; on `π_T`, `err_T` at every
  lift (net `−m·err_T`: `W_ρ` is a maximum over the lifts); on `√−d`, the remainder `½·max_ω Σ_t deg_j(t)` alone. The
  spec's `FRamD(J) + …` at `d` is read as the archive's per-place form, whose forced part is kept on the `F` side here:
  then the `d`-summand of `Fo` is carried exactly (§2.3) and the divisibility asked at `√−d` is the weakest that does.
* `F^+(p)` (`Fplus`) is the forced order's part over the plus-sign places (`z.1 = 1`, whose orbits stay there) at inert
  `p`, and `0` at signal `p`, where every place has the minus sign (`Φ_p⁻ = Φ`). A top is a place `(1, t)`, `t ∈ TT`,
  so `Φ_p⁻` holds no top at inert `p`.
* `π̄_i = π_{g_i}` (`normPi` at the modulus `N`): the conjugate of `conj π_{g_i}`, over which the level places `SG`
  lie (`sharpSG`). `π_T = conj(tz)` for the translate's auxiliary prime (`sharpTz`): its places are the cut places `ST`
  (`sharpST`). One word per translate, as in the construction.
* `F = ℚ(√−d)` is not a type upstream of the construction (`SharpChainU.chainK0` is downstream), so the elements are
  in `O_E` (all lie in `ℚ(√−d)`), and `log N_{F/ℚ}` is the normalised `λ`. `√−d` is `QuadSub`'s Gauss sum `gaussE`
  (`Setting.sqrtO`; `1` unless `d ≡ 3 (mod 4)`, which an admissible design has).
* `n_ϖ = ⌊s_ϖ⌋` in both cases of C1, as `−⌈−s⌉ = ⌊s⌋` (`nExp_eq_of_nonneg`, `nExp_eq_of_neg`).
* The pins' caps (`α₀ ∣ aBd`, `β₀ ∣ aBdN`) are not part of this module.

**Taken as data.** The quantities of §2.5 that read objects the library does not define yet are the fields of
`ErrData`: the stabiliser denominator `D_Γ`, the word's weighted degrees `ν(j)`, its weight deviations `W_ρ`, and the
error `½·max_ω Σ_t deg_j(t)` at `√−d`. The top shifts `b_t` are the design's parameters (`DesignPar.bT`), which
`SharpDesign` does not record.

**Against the spec.**
* `0 ≤ G_j(p) ≤ 4|TT|·a/p` does not follow from the definitions alone: the upper bound needs nonnegative caps and served
  penalties and `a_t ≤ 2a`, facts of an admissible design that `gain_le` takes as hypotheses.
* At `d` the spec lists the error `FRamD(J) + ½·max_ω Σ_t deg_j(t)` but also has the `d`-part of `Fo` carried exactly
  and the error at `d` polynomially small (§2.3, §2.7); read as above.
-/

open Finset NumberField

namespace ZetaBalance

noncomputable section

/-! ## The ingredients that do not read the design -/

/-- `i ↦ 2i + 1` is injective. -/
theorem two_mul_add_one_injective : Function.Injective fun i : ℕ => 2 * i + 1 := fun i j h => by
  simp only at h
  omega

/-- **The odd exponents** at `p`: `e = 2i + 1` for `i ≤ log_p⌈2a⌉`, every odd `e` with `p^e ≤ 2a`. -/
def gainExps (x ε : ℝ) (p : ℕ) : Finset ℕ :=
  (range (Nat.log p ⌈2 * scA x ε⌉₊ + 1)).map ⟨fun i => 2 * i + 1, two_mul_add_one_injective⟩

/-- **`γ_p = p/(p² − 1)`** `= Σ_{e odd} p^{−e}`. -/
def gamP (p : ℕ) : ℝ := p / ((p : ℝ) ^ 2 - 1)

/-- **The error data of a word**: the quantities of the error exponents that read objects the library does not
define yet. -/
structure ErrData (S : Setting) (R : S.Ranks) where
  /-- `D_Γ`, the lcm of the stabiliser orders over the classes of every level used (the masses' denominators). -/
  DΓ : ℕ
  /-- `ν(j)`, the signed weighted degree of the word's step-`j` source weights (the error on `π̄_i`). -/
  ν : Fin R.m → ℝ
  /-- `W_ρ = max_{i ≤ m, a} |λ_{i,ρ,a} − i(t + 1)/2|` over the word's weights, the top's first coordinate excluded. -/
  W : Φ S.A → ℝ
  /-- `½·max_ω Σ_t deg_j(t)`, the error at `√−d` (step-`j` weighted degrees at the places `(1, t)`). -/
  degD : Fin R.m → ℝ

/-- **The prime elements** of `ℚ(√−d)` that carry the gain's exponents: a rational prime `p`, the split primes `g_i`,
the conjugates `π̄_i` of their level elements, the cut element `π_T`, and `√−d`. -/
inductive GainPrime
  /-- A rational prime `p` (inert or signal `p ≤ X″`, or `p ∣ D_Γ`). -/
  | rat (p : ℕ)
  /-- The split prime `g_i`, a rational prime. -/
  | gi (i : Fin 2)
  /-- `π̄_i`, of norm `g_i`. -/
  | gbar (i : Fin 2)
  /-- The cut element `π_T`, of norm `T`. -/
  | cut
  /-- `√−d`. -/
  | sqrtd
  deriving DecidableEq

namespace GainPrime

/-- **The special prime elements**: `g₀, g₁, π̄₀, π̄₁, π_T, √−d`. -/
def specials : Finset GainPrime := {gi 0, gi 1, gbar 0, gbar 1, cut, sqrtd}

/-- `rat` is injective. -/
theorem rat_injective : Function.Injective rat := fun _ _ h => rat.inj h

end GainPrime

namespace Setting

variable (S : Setting)

/-- **`√−d` in `O_E`**: `QuadSub`'s Gauss sum `gaussE`, as `(0 + 2·gaussE)/2` (`halfO`), for `d ≡ 3 (mod 4)`; `1`
otherwise. -/
def sqrtO : 𝓞 S.E :=
  if hd : S.d % 4 = 3 then halfO (S.gaussE_sq hd) hd (a := 0) (b := 2) (Int.modEq_iff_dvd.2 ⟨1, by norm_num⟩) else 1

/-- **The normalised log-norm** `λ(γ) = 2·log|N_{E/ℚ}(γ)|/[E:ℚ]`, which is `log N_{F/ℚ}(γ)` for `γ ∈ F = ℚ(√−d)`. -/
def lnorm (γ : S.E) : ℝ := 2 * Real.log |(Algebra.norm ℚ γ : ℝ)| / Module.finrank ℚ S.E

/-- **The places of the minus sign** at `p`: those `z` with `z.1 = −1` at an inert `p`, and all places at a signal
`p`. -/
def minusPlaces (p : ℕ) : Finset (Φ S.A) :=
  if S.cls p = .signal then univ else univ.filter fun z => z.1 = -1

end Setting

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## The design's sizes -/

/-- `c₀ = 16kΔ`, four times the cloud. -/
def c0 : ℝ := 16 * Dg.R.k * designΔ x

/-- `S_c = 4kΔ`, the cloud of the Harish-Chandra families. -/
def cloud : ℝ := 4 * Dg.R.k * designΔ x

/-- `η = 2mH`, the spread of the families' weights. -/
def eta : ℝ := 2 * Dg.R.m * designH S x

/-- **The weight** `w_j(z) = e_J(z)` of `hc u` at the lift `j = J + 1`. -/
def wt (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : ℝ := Dg.R.wj (Dg.hc u) J z

/-- **The shifted weight** `w̃_j(z) = w_j(z) − (k + (2j − 1)(t + 1))/2`, `j = J + 1`. -/
def wsh (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : ℝ :=
  Dg.wt u J z - ((Dg.R.k : ℝ) + (2 * (J : ℝ) + 1) * ((Dg.R.t : ℝ) + 1)) / 2

/-- **The reduced scale** `ā_s = a_s − 2c₀` of a top. -/
def abar (s : S.A) : ℝ := Dg.a s - 2 * Dg.c0

/-- **The cap** `cap_{s,e} = w̃_j(partner(s, e)) + c₀`, with the partner `pos_p(1, s; e)` at the twist `twA κ`. -/
def cap (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (s : S.A) (e : ℕ) : ℝ :=
  Dg.wsh u J (S.pos (S.twA κ) p (1, s) e) + Dg.c0

/-! ## Orbits -/

/-- **The base points of the orbits that carry tops** at `p`: `basePoint σ_p (TT)`. -/
def basePts (p : ℕ) : Finset S.A := Dg.TT.image (basePoint (S.orbitStep (S.twA κ) p))

/-- **The tops on the orbit of `t₀`** at `p`. -/
def topsOn (p : ℕ) (t₀ : S.A) : Finset S.A := Dg.TT.filter fun s => basePoint (S.orbitStep (S.twA κ) p) s = t₀

/-- **The slack** `sl(p, t₀) = c_{dl,1}·n_p·N_m²·log_p(2a) + c_{dl,2}·#tops·log_p(2a)²`. -/
def sl (p : ℕ) (t₀ : S.A) : ℝ :=
  Kg.cdl₁ * S.nP (S.twA κ) p * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
    Kg.cdl₂ * (Dg.topsOn p t₀).card * Real.logb p (2 * scA x ε) ^ 2

open scoped Classical in
/-- **The trivial gain** of an orbit: `g^{tr}_j = Σ_{tops s} Σ_{e odd, no collision at (s, e)} (ā_s/p^e − cap_{s,e})⁺
− sl`. -/
def gTr (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (t₀ : S.A) : ℝ :=
  (∑ s ∈ Dg.topsOn p t₀, ∑ e ∈ (gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e),
      max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0) - Dg.sl p t₀

open scoped Classical in
/-- **The served gain** of an orbit: `g^{sv}_j = Σ_{V-tops s} γ_p·ā_s + Σ_{other tops s} Σ_{e odd}
(ā_s/p^e − cap_{s,e})⁺ − sl`, the spec's `γ_p·Σ_s ā_s − Σ_{non-V s} Σ_e min(ā_s/p^e, cap_{s,e}) − sl`. -/
def gSv (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (t₀ : S.A) : ℝ :=
  (∑ s ∈ Dg.topsOn p t₀, if IsVType (S.orbitStep (S.twA κ) p) s then gamP p * Dg.abar s
      else ∑ e ∈ gainExps x ε p, max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0) - Dg.sl p t₀

open scoped Classical in
/-- **The penalty** of an orbit: for `p ≥ p₀`, `Σ_{non-V tops s}(w̃_j(1, s) − b_s) + c_Pr·n_p·(w″ + η + c₀ + N_m)`;
for `p < p₀`, `r·(#tops·(2b′ + c₀) + n_p·(w″ + η + c₀ + N_m))`. -/
def pen (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (t₀ : S.A) : ℝ :=
  if scP0 x Dg.R.k ≤ p then
    (∑ s ∈ (Dg.topsOn p t₀).filter (fun s => ¬ IsVType (S.orbitStep (S.twA κ) p) s),
        (Dg.wsh u J (1, s) - pr.bT s)) +
      Kg.cPr * S.nP (S.twA κ) p * (scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m)
  else (tilePar x ε Dg.R.k).r * ((Dg.topsOn p t₀).card * (2 * scB' x ε + Dg.c0) +
      S.nP (S.twA κ) p * (scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m))

/-- **The denominator exponent** `D_p`: `⌈c_{D,1}·40n_pδ₁·x^{26}·(N₁⁵ + k³)·log_p a⌉` for `p ≥ p₀`, and
`⌈c_{D,2}·40n_pδ₁·(N₁³ + r⁵ + k²)·log_p a + 2r·n_p·c₀ + r·40n_pδ₁·(2b′ + 2c₀)⌉` below. -/
def Dexp (p : ℕ) : ℕ :=
  if scP0 x Dg.R.k ≤ p then
    ⌈(Kg.cD₁ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * x ^ 26 *
      (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * Real.logb p (scA x ε)⌉₊
  else
    ⌈(Kg.cD₂ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 3 +
        ((tilePar x ε Dg.R.k).r : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 2) * Real.logb p (scA x ε) +
      2 * (tilePar x ε Dg.R.k).r * S.nP (S.twA κ) p * Dg.c0 +
      (tilePar x ε Dg.R.k).r * 40 * S.nP (S.twA κ) p * scδ₁ x ε * (2 * scB' x ε + 2 * Dg.c0)⌉₊

/-- **The sandwich exponent** `e_p = ⌈c_S·f·k²·log_p a⌉`. -/
def eSand (p : ℕ) : ℕ := ⌈(Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * Real.logb p (scA x ε)⌉₊

/-- **The distance back to the nearest V-top** before the top `s` on its orbit at `p` (`prevV`; `0` if none). -/
def vDist (p : ℕ) (s : S.A) : ℕ :=
  prevV (orderOf (S.orbitStep (S.twA κ) p))
    (topPositions Dg.TT (S.orbitStep (S.twA κ) p) (basePoint (S.orbitStep (S.twA κ) p) s))
    (orbitPos (S.orbitStep (S.twA κ) p) s)

/-- **The nearest V-top before `s`**: the element at the position `vDist p s` back from `s` on its orbit. -/
def vPrev (p : ℕ) (s : S.A) : S.A :=
  basePoint (S.orbitStep (S.twA κ) p) s * S.orbitStep (S.twA κ) p ^
    ((orbitPos (S.orbitStep (S.twA κ) p) s + orderOf (S.orbitStep (S.twA κ) p) - Dg.vDist p s) %
      orderOf (S.orbitStep (S.twA κ) p))

/-- **The depth's constant** `c_dep = 8(D_p + 1) + c_{κ,2}·40n_pδ₁·k·log_p a + 160n_pδ₁c₀ + 2n_pc₀`. -/
def cDep (p : ℕ) : ℝ :=
  8 * ((Dg.Dexp p : ℝ) + 1) + Kg.cκ₂ * 40 * S.nP (S.twA κ) p * scδ₁ x ε * Dg.R.k * Real.logb p (scA x ε) +
    160 * S.nP (S.twA κ) p * scδ₁ x ε * Dg.c0 + 2 * S.nP (S.twA κ) p * Dg.c0

open scoped Classical in
/-- **The depth** of an orbit. For `p ≥ p₀`: `Σ_{non-V tops y} min(b_y, a_{y′}/p^{d(y)}) + c_{κ,1}·#tops·N₁·(a/p² +
La·a/(pk)) + c_{κ,2}·#tops·(Q_p·c_dep + k·Q_p + k·log_p a + c₀) + 2n_p·c₀`, with `y′` the nearest V-top before `y` at
the distance `d(y)` (the term is `0` if there is none) and `Q_p = p^{G′}`. For `p < p₀`:
`c_t·r·#tops·(La·a/(pk) + a·p^{−L₁(p)} + 2b′ + 2c₀ + k·Q_p) + 2r·n_p·c₀`. -/
def dep (pr : DesignPar S) (p : ℕ) (t₀ : S.A) : ℝ :=
  if scP0 x Dg.R.k ≤ p then
    (∑ y ∈ (Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y),
        if Dg.vDist p y = 0 then 0 else min (pr.bT y : ℝ) (Dg.a (Dg.vPrev p y) / (p : ℝ) ^ Dg.vDist p y)) +
      Kg.cκ₁ * (Dg.topsOn p t₀).card * (tilePar x ε Dg.R.k).N₁ *
        (scA x ε / (p : ℝ) ^ 2 + scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k)) +
      Kg.cκ₂ * (Dg.topsOn p t₀).card * ((p : ℝ) ^ (tilePar x ε Dg.R.k).G' * Dg.cDep p +
        Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G' + Dg.R.k * Real.logb p (scA x ε) + Dg.c0) +
      2 * S.nP (S.twA κ) p * Dg.c0
  else Kg.ct * (tilePar x ε Dg.R.k).r * (Dg.topsOn p t₀).card * (scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k) +
      scA x ε / (p : ℝ) ^ scL1 x Dg.R.k p + 2 * scB' x ε + 2 * Dg.c0 + Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G') +
    2 * (tilePar x ε Dg.R.k).r * S.nP (S.twA κ) p * Dg.c0

open scoped Classical in
/-- **The served set** `S_p`: the base points of good orbits (`IsGoodAt`) if `p` is a candidate (and in
`inertPrimes(X″)`), else `∅`. -/
def served (p : ℕ) : Finset S.A :=
  if p ∈ S.cand κ x ε Dg.R.k ∧ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) then
    (Dg.basePts p).filter (Dg.IsGoodAt p)
  else ∅

/-! ## The gain, the depth, the forced orders and the errors at a prime -/

open scoped Classical in
/-- **The gain** `G_j(p)` at an inert or signal `p ≤ X″` with `h_p` of even order:
`Σ_{t₀ ∈ S_p} max(g^{sv}_j − pen_j, g^{tr⁺}_j) + Σ_{t₀ ∉ S_p} g^{tr⁺}_j` over the orbits of the tops; `0` otherwise. -/
def gainG (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) (p : ℕ) : ℝ :=
  if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∧ Even (orderOf (S.hPtw (S.twA κ) p)) then
    ∑ t₀ ∈ Dg.basePts p, if t₀ ∈ Dg.served p then
      max (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) (max (Dg.gTr u J p t₀) 0) else max (Dg.gTr u J p t₀) 0
  else 0

/-- **The depth paid at `p`**: `τ_p = e_p + Σ_{t₀ ∈ S_p} m·(⌈dep⌉ + D_p + 1)`, and `0` if `S_p = ∅`. -/
def tau (pr : DesignPar S) (p : ℕ) : ℕ :=
  if (Dg.served p).Nonempty then
    Dg.eSand p + ∑ t₀ ∈ Dg.served p, Dg.R.m * (⌈Dg.dep pr p t₀⌉₊ + Dg.Dexp p + 1)
  else 0

/-- **The forced order on the plus-sign places** at `p`: `n_p⁻¹·Σ_{z ∉ Φ_p⁻} lpF(p, n_p, s ↦ (k − 1)·w_j(pos_p(z; s)))`,
the part of `FInert` over the places outside `Φ_p⁻` (none at a signal `p`). -/
def Fplus (u : S.A) (J : Fin Dg.R.m) (p : ℕ) : ℝ :=
  (S.nP (S.twA κ) p : ℝ)⁻¹ * ∑ z ∈ (S.minusPlaces p)ᶜ,
    Setting.lpF p (S.nP (S.twA κ) p) fun s => ((Dg.R.k : ℝ) - 1) * Dg.wt u J (S.pos (S.twA κ) p z s)

/-- **The tops among the minus-sign places** at `p`: `#{(1, t) ∈ Φ_p⁻ : t ∈ TT}`. -/
def topsMinus (p : ℕ) : ℕ := ((S.minusPlaces p).filter fun z => z.1 = 1 ∧ z.2 ∈ Dg.TT).card

/-- **The error exponent at an inert or signal `p`**. At inert `p` with `h_p = 1`:
`c_E′·f·N_m²·log_p a + Σ_ρ w_j(ρ)/(p² − 1)`. Otherwise: `max(0, F^+) + γ_p·#(tops in Φ_p⁻)·(b + η + 1 + 3S_c) +
c_E″·Σ_{Φ_p⁻} w_j/p + |Φ_p⁻|·N_{j−1}N_j·(log_p(4n_pN_m a) + 1) + c_{dl,1}·|Φ_p⁻|·N_m²·log_p(2a) +
c_{dl,2}·#(tops in Φ_p⁻)·log_p(2a)² + [ord h_p odd]·((k − 1)Σ_{Φ_p⁻} w_j/p³ + c_E″·f·N_m²·log_p a)`. -/
def Einert (u : S.A) (J : Fin Dg.R.m) (p : ℕ) : ℝ :=
  if S.cls p = .inert ∧ S.hPtw (S.twA κ) p = 1 then
    Kg.cE' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε) + ∑ ρ, Dg.wt u J ρ / ((p : ℝ) ^ 2 - 1)
  else max 0 (Dg.Fplus u J p) + gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) +
    Kg.cE'' * (∑ z ∈ S.minusPlaces p, Dg.wt u J z / p) +
    (S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
      (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1) +
    Kg.cdl₁ * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
    Kg.cdl₂ * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2 +
    (if Odd (orderOf (S.hPtw (S.twA κ) p)) then
      ((Dg.R.k : ℝ) - 1) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z) / (p : ℝ) ^ 3 +
        Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)
    else 0)

/-- **The error at the cut** `err_T = 2Σ_ρ W_ρ + f·N_m + #tops·(t + 1)(m + 1)/4`, at every lift. -/
def errT (ED : ErrData S Dg.R) : ℝ :=
  2 * (∑ ρ, ED.W ρ) + S.f * (Dg.R.N Dg.R.m : ℝ) + Dg.TT.card * ((Dg.R.t : ℝ) + 1) * ((Dg.R.m : ℝ) + 1) / 4

/-! ## The exponents at the prime elements -/

/-- **The gain at a prime element**: `G_j(p)` at `rat p`, `0` elsewhere. -/
def Gexp (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) : GainPrime → ℝ
  | .rat p => Dg.gainG pr u J p
  | _ => 0

/-- **The depth at a prime element**: `τ_p` at `rat p`, `0` elsewhere. -/
def tauE (pr : DesignPar S) : GainPrime → ℕ
  | .rat p => Dg.tau pr p
  | _ => 0

/-- **The forced orders** at a prime element: `FInert(J, p)` at an inert or signal `p ≤ X″`, `FTypeG(J)` at `g_i`,
`2·FRamD(J)` at `√−d` (as `d = −(√−d)²`), and `0` elsewhere; with the family `hc u` and the twist `twA κ`. -/
def Fexp (u : S.A) (J : Fin Dg.R.m) : GainPrime → ℝ
  | .rat p => if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) then
      Dg.R.FInert (Dg.hc u) (S.twA κ) J p else 0
  | .gi _ => Dg.R.FTypeG (Dg.hc u) J
  | .gbar _ => 0
  | .cut => 0
  | .sqrtd => 2 * Dg.R.FRamD (Dg.hc u) (S.twA κ) J

/-- **The error exponents** at a prime element: `Einert(J, p)` at an inert or signal `p ≤ X″` plus `v_p(D_Γ)` at
`rat p`; `FTypeG(J) + c_E·f·(N_m² + m²η)` at `g_i`; `ν(j)` at `π̄_i`; `err_T` at `π_T`; `½·max_ω Σ_t deg_j(t)` at
`√−d`. -/
def Eexp (u : S.A) (ED : ErrData S Dg.R) (J : Fin Dg.R.m) : GainPrime → ℝ
  | .rat p => (if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) then Dg.Einert u J p else 0) +
      padicValNat p ED.DΓ
  | .gi _ => Dg.R.FTypeG (Dg.hc u) J + Kg.cE * S.f * ((Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta)
  | .gbar _ => ED.ν J
  | .cut => Dg.errT ED
  | .sqrtd => ED.degD J

/-- **The real exponent** `s_ϖ = Σ_j (G_j(ϖ) + F_j(ϖ) − E_j(ϖ)) − τ(ϖ)`. -/
def sExp (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (ϖ : GainPrime) : ℝ :=
  (∑ J, (Dg.Gexp pr u J ϖ + Dg.Fexp u J ϖ - Dg.Eexp u ED J ϖ)) - Dg.tauE pr ϖ

/-- **The integer exponent** `n_ϖ = ⌊s_ϖ⌋` (`⌊s_ϖ⌋` for `s_ϖ ≥ 0`, `−⌈−s_ϖ⌉` below). -/
def nExp (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (ϖ : GainPrime) : ℤ := ⌊Dg.sExp pr u ED ϖ⌋

/-- **The index set of the prime elements**: the inert and signal `p ≤ X″`, the primes of `D_Γ`, and the specials. -/
def primeSet (ED : ErrData S Dg.R) : Finset GainPrime :=
  (Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors).map
    ⟨GainPrime.rat, GainPrime.rat_injective⟩ ∪ GainPrime.specials

/-- The split primes `g₀, g₁`. -/
def gs : Fin 2 → ℕ := ![Dg.g₀, Dg.g₁]

/-- **The prime elements in `O_E`**: `p`, `g_i`, `π̄_i = π_{g_i}` (`normPi` at `N`; `SG` lies over its conjugate),
`π_T = conj(tz)` of the translate's auxiliary prime (over which `ST` lies), and `√−d`. -/
def elt (u : S.A) : GainPrime → 𝓞 S.E
  | .rat p => p
  | .gi i => Dg.gs i
  | .gbar i => normPi S S.N (Dg.gs i)
  | .cut => IsCMField.ringOfIntegersComplexConj S.E (sharpTz Dg u)
  | .sqrtd => S.sqrtO

/-- **`log N_{F/ℚ}` of the prime elements**: `2 log p`, `2 log g_i`, `log g_i`, `log T`, `log d`. -/
def logN (u : S.A) : GainPrime → ℝ
  | .rat p => 2 * Real.log p
  | .gi i => 2 * Real.log (Dg.gs i)
  | .gbar i => Real.log (Dg.gs i)
  | .cut => Real.log (sharpT Dg u)
  | .sqrtd => Real.log S.d

/-- **`α₀ = ∏_{s_ϖ ≥ 0} ϖ^{⌊s_ϖ⌋}`**, the generator of `𝔞⁺` (through the CM type). -/
def gainAlpha₀ (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) : 𝓞 S.E :=
  ∏ ϖ ∈ (Dg.primeSet ED).filter (fun ϖ => 0 ≤ Dg.sExp pr u ED ϖ), Dg.elt u ϖ ^ ⌊Dg.sExp pr u ED ϖ⌋₊

/-- **`β₀ = ∏_{s_ϖ < 0} ϖ^{⌈−s_ϖ⌉}`**, the generator of `𝔞⁻` (through the CM type). -/
def gainBeta₀ (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) : 𝓞 S.E :=
  ∏ ϖ ∈ (Dg.primeSet ED).filter (fun ϖ => Dg.sExp pr u ED ϖ < 0), Dg.elt u ϖ ^ ⌈-Dg.sExp pr u ED ϖ⌉₊

end SharpDesign

/-! ## Elementary facts -/

/-- **`γ_p ≥ 0`** for every `p` (`γ_0 = 0`, and `γ_1 = 1/0 = 0`). -/
theorem gamP_nonneg (p : ℕ) : 0 ≤ gamP p := by
  unfold gamP
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp
  · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg (Nat.cast_nonneg _) (by nlinarith)

/-- **`γ_p ≤ 4/(3p)`** for `p ≥ 2`, as `p² ≥ 4`. -/
theorem gamP_le {p : ℕ} (hp : 2 ≤ p) : gamP p ≤ 4 / (3 * p) := by
  unfold gamP
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/-- **The odd powers sum to at most `γ_p`**: `Σ_{e ∈ gainExps} y/p^e ≤ γ_p·y` for `p ≥ 2` and `y ≥ 0`, a partial sum
of `y·Σ_{e odd} p^{−e}`. -/
theorem sum_gainExps_le {x ε : ℝ} {p : ℕ} (hp : 2 ≤ p) {y : ℝ} (hy : 0 ≤ y) :
    ∑ e ∈ gainExps x ε p, y / (p : ℝ) ^ e ≤ gamP p * y := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  set q : ℝ := 1 / (p : ℝ) ^ 2 with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq_def, div_lt_one (by positivity)]; nlinarith
  rw [gainExps, sum_map]
  have key : ∀ i : ℕ, y / (p : ℝ) ^ (2 * i + 1) = y / p * q ^ i := by
    intro i
    rw [hq_def, pow_succ, pow_mul, div_pow, one_pow]
    field_simp
  simp only [Function.Embedding.coeFn_mk, key, ← mul_sum]
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := Nat.log p ⌈2 * scA x ε⌉₊ + 1) hq0 hq1
  rw [← range_eq_Ico, pow_zero] at hg
  calc y / p * ∑ i ∈ range (Nat.log p ⌈2 * scA x ε⌉₊ + 1), q ^ i ≤ y / p * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = gamP p * y := by
        have h1q : 1 - q = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by rw [hq_def]; field_simp
        rw [h1q, gamP]
        field_simp

/-- **`log_p y ≥ 0`** for `y ≥ 1`, at every natural base (`log_0 = log_1 = 0`). -/
theorem logb_nat_nonneg (p : ℕ) {y : ℝ} (hy : 1 ≤ y) : 0 ≤ Real.logb p y :=
  div_nonneg (Real.log_nonneg hy) (Real.log_natCast_nonneg p)

/-- **`a ≥ 1`** for `x ≥ 1`. -/
theorem one_le_scA {x : ℝ} (ε : ℝ) (hx : 1 ≤ x) : 1 ≤ scA x ε := by
  unfold scA scB scL
  have := Real.one_le_exp (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) ε)
  nlinarith

/-- **`n_p ≥ 1`**: an order in the finite group `A`, or twice one. -/
theorem Setting.one_le_nP (S : Setting) (c : S.A) (p : ℕ) : 1 ≤ S.nP c p := by
  unfold Setting.nP
  split_ifs
  · have := orderOf_pos (S.hPtw c p ^ 2)
    omega
  · exact orderOf_pos _

/-- **The primes of `inertPrimes`** are primes. -/
theorem Setting.Ranks.prime_of_mem_inertPrimes {S : Setting} {X'' : ℝ} {p : ℕ}
    (h : p ∈ Setting.Ranks.inertPrimes (S := S) X'') : p.Prime := by
  simp only [Setting.Ranks.inertPrimes, mem_filter] at h
  exact h.2.1

/-! ## Elements of `O_E` -/

/-- **`π·conj π = p`** for `π = normPi S M p` a `halfO` (`Setting.halfO_mul_conj_eq`). -/
theorem normPi_mul_conj_eq {S : Setting} {M p : ℕ}
    (h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]) :
    normPi S M p * IsCMField.ringOfIntegersComplexConj S.E (normPi S M p) = p := by
  rw [normPi, dite_eq_left h]
  exact Setting.halfO_mul_conj_eq _ _ _ h.2.choose_spec.choose_spec.1

/-- **`normPi S M p ≠ 0`** for `p ≠ 0`: a `halfO` of norm `p`, or `1`. -/
theorem normPi_ne_zero {S : Setting} {M p : ℕ} (hp : p ≠ 0) : normPi S M p ≠ 0 := by
  by_cases h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]
  · intro h0
    have h1 := normPi_mul_conj_eq h
    rw [h0, zero_mul, eq_comm, Nat.cast_eq_zero] at h1
    exact hp h1
  · rw [normPi, dite_eq_right h]
    exact one_ne_zero

/-- **`sqrtO = gaussE`** for `d ≡ 3 (mod 4)`. -/
theorem Setting.coe_sqrtO (S : Setting) (hd : S.d % 4 = 3) : (S.sqrtO : S.E) = S.gaussE := by
  rw [Setting.sqrtO, dite_eq_left hd, Setting.coe_halfO]
  push_cast
  ring

/-- **`sqrtO ≠ 0`**: its square is `−d ≠ 0`, or it is `1`. -/
theorem Setting.sqrtO_ne_zero (S : Setting) : S.sqrtO ≠ 0 := by
  by_cases hd : S.d % 4 = 3
  · intro h0
    have h1 := S.gaussE_sq hd
    rw [← S.coe_sqrtO hd, h0] at h1
    have hd0 : (S.d : S.E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : S.d.Prime).ne_zero
    exact hd0 (by simpa using h1.symm)
  · rw [Setting.sqrtO, dite_eq_right hd]
    exact one_ne_zero

/-! ## The normalised log-norm -/

namespace Setting

variable (S : Setting)

/-- **`λ` of a natural number**: `λ(p) = 2 log p`, as `N_{E/ℚ}(p) = p^{[E:ℚ]}`. -/
theorem lnorm_natCast (p : ℕ) : S.lnorm (p : S.E) = 2 * Real.log p := by
  have hn : (Module.finrank ℚ S.E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold lnorm
  rw [show (p : S.E) = algebraMap ℚ S.E (p : ℚ) from (map_natCast _ p).symm, Algebra.norm_algebraMap]
  push_cast
  rw [abs_pow, Real.log_pow, abs_of_nonneg (Nat.cast_nonneg _)]
  field_simp

/-- **`λ` from a squared norm**: if `|N(z)|² = g^{[E:ℚ]}` then `λ(z) = log g`. -/
theorem lnorm_of_sq {z : S.E} {g : ℕ} (h : |(Algebra.norm ℚ z : ℝ)| ^ 2 = (g : ℝ) ^ Module.finrank ℚ S.E) :
    S.lnorm z = Real.log g := by
  have hn : (Module.finrank ℚ S.E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 := congrArg Real.log h
  rw [Real.log_pow, Real.log_pow] at h2
  unfold lnorm
  push_cast at h2
  rw [h2]
  field_simp

/-- **`λ` is invariant under complex conjugation**: `N(conj z) = N(z)`, `conj` being a `ℚ`-automorphism. -/
theorem lnorm_conj (z : S.E) : S.lnorm (IsCMField.complexConj S.E z) = S.lnorm z := by
  unfold lnorm
  rw [show IsCMField.complexConj S.E z = (IsCMField.complexConj S.E).toRingEquiv.toRatAlgEquiv z from rfl,
    Algebra.norm_eq_of_algEquiv]

/-- **`λ(π) = log g` for `π·conj π = g`**: `N(π)² = N(π)N(conj π) = N(g) = g^{[E:ℚ]}`. -/
theorem lnorm_of_mul_conj {z : S.E} {g : ℕ} (h : z * IsCMField.complexConj S.E z = g) :
    S.lnorm z = Real.log g := by
  refine S.lnorm_of_sq ?_
  have h1 := congrArg (Algebra.norm ℚ) h
  rw [map_mul, show IsCMField.complexConj S.E z = (IsCMField.complexConj S.E).toRingEquiv.toRatAlgEquiv z from rfl,
    Algebra.norm_eq_of_algEquiv, show (g : S.E) = algebraMap ℚ S.E (g : ℚ) from (map_natCast _ g).symm,
    Algebra.norm_algebraMap] at h1
  rw [sq_abs, sq, ← Rat.cast_mul, h1]
  push_cast
  rfl

/-- **`λ(√−d) = log d`** for `s² = −d`: `N(s)² = N(−d) = (−d)^{[E:ℚ]}`. -/
theorem lnorm_of_sq_eq {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) : S.lnorm s = Real.log S.d := by
  refine S.lnorm_of_sq ?_
  have h1 := congrArg (Algebra.norm ℚ) hs
  rw [map_pow, show -(S.d : S.E) = algebraMap ℚ S.E (-(S.d : ℚ)) by simp, Algebra.norm_algebraMap] at h1
  rw [← abs_pow, ← Rat.cast_pow, h1]
  push_cast
  rw [abs_pow, abs_neg, Nat.abs_cast]

/-- **`λ` of a product of integer powers**: `λ(∏ f_i^{n_i}) = Σ n_i·λ(f_i)` for nonzero `f_i`. -/
theorem lnorm_prod_zpow {ι : Type*} (s : Finset ι) (f : ι → S.E) (n : ι → ℤ) (hf : ∀ i ∈ s, f i ≠ 0) :
    S.lnorm (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, (n i : ℝ) * S.lnorm (f i) := by
  unfold lnorm
  rw [map_prod]
  simp only [Algebra.norm_zpow]
  push_cast
  rw [abs_prod, Real.log_prod]
  · simp only [abs_zpow, Real.log_zpow, mul_sum, sum_div]
    refine sum_congr rfl fun i _ => ?_
    ring
  · intro i hi
    rw [abs_ne_zero]
    apply zpow_ne_zero
    rw [Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 (hf i hi)

end Setting

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## Signs and supports -/

/-- `c₀ ≥ 0`. -/
theorem c0_nonneg : 0 ≤ Dg.c0 := by unfold c0; positivity

/-- `S_c ≥ 0`. -/
theorem cloud_nonneg : 0 ≤ Dg.cloud := by unfold cloud; positivity

/-- `η ≥ 0`. -/
theorem eta_nonneg : 0 ≤ Dg.eta := by unfold eta; positivity

/-- **The weights are positive** (`Weights.w_pos`, through `w_{u,j} = e_j`). -/
theorem wt_pos (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : 0 < Dg.wt u J z := by
  have h := Dg.w_pos u (Fin.cast Dg.hm.symm J) z
  rw [Dg.hw u (Fin.cast Dg.hm.symm J) z] at h
  simpa [wt] using h

/-- **The weights are nonnegative integers.** -/
theorem wj_nonneg (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : 0 ≤ Dg.R.wj (Dg.hc u) J z :=
  (Int.cast_pos.1 (Dg.wt_pos u J z)).le

/-- `N_m ≥ 1`. -/
theorem one_le_N : 1 ≤ Dg.R.N Dg.R.m :=
  (show 1 ≤ Dg.R.k by have := Dg.R.m_add_three_le; omega).trans (Nat.le_add_right _ _)

/-- `k ≥ 1`. -/
theorem one_le_k : (1 : ℝ) ≤ Dg.R.k := by
  have := Dg.R.m_add_three_le
  exact_mod_cast (by omega : 1 ≤ Dg.R.k)

/-- **The slack is nonnegative** for `x ≥ 1`. -/
theorem sl_nonneg (hx : 1 ≤ x) (p : ℕ) (t₀ : S.A) : 0 ≤ Dg.sl p t₀ := by
  have h := logb_nat_nonneg p (show (1 : ℝ) ≤ 2 * scA x ε by linarith [one_le_scA ε hx])
  unfold sl
  exact add_nonneg (mul_nonneg (by positivity) h) (by positivity)

/-- **The gain is nonnegative**: each orbit contributes a maximum with `g^{tr⁺} ≥ 0`. -/
theorem gainG_nonneg (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) (p : ℕ) : 0 ≤ Dg.gainG pr u J p := by
  unfold gainG
  split_ifs
  · refine sum_nonneg fun t₀ _ => ?_
    split_ifs
    · exact le_max_of_le_right (le_max_right _ _)
    · exact le_max_right _ _
  · exact le_rfl

/-- **The gain vanishes off the inert and signal `p ≤ X″` of even order.** -/
theorem gainG_eq_zero (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (h : ¬ (p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∧ Even (orderOf (S.hPtw (S.twA κ) p)))) :
    Dg.gainG pr u J p = 0 := by
  unfold gainG
  rw [ite_eq_right h]

/-- **The served set lies among the base points of the tops.** -/
theorem served_subset (p : ℕ) : Dg.served p ⊆ Dg.basePts p := by
  classical
  unfold served
  split_ifs
  · exact filter_subset _ _
  · exact empty_subset _

/-- **Membership in the served set**: a base point of a good orbit (`IsGoodAt`) at a candidate in
`inertPrimes(X″)`. -/
theorem mem_served_iff {p : ℕ} {t₀ : S.A} : t₀ ∈ Dg.served p ↔
    (p ∈ S.cand κ x ε Dg.R.k ∧ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) ∧ t₀ ∈ Dg.basePts p ∧
      Dg.IsGoodAt p t₀ := by
  classical
  unfold served
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **No served orbits off `inertPrimes(X″)`.** -/
theorem served_eq_empty {p : ℕ} (h : p ∉ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) : Dg.served p = ∅ := by
  unfold served
  rw [ite_eq_right fun h' => h h'.2]

/-- **The depth vanishes off `inertPrimes(X″)`.** -/
theorem tau_eq_zero (pr : DesignPar S) {p : ℕ} (h : p ∉ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    Dg.tau pr p = 0 := by
  unfold tau
  rw [Dg.served_eq_empty h]
  simp

/-- **The error exponent at an inert or signal `p ≥ 1` is nonnegative** for `x ≥ 1`. -/
theorem Einert_nonneg (hx : 1 ≤ x) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 1 ≤ p) : 0 ≤ Dg.Einert u J p := by
  have ha := one_le_scA ε hx
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hw : ∀ z, 0 ≤ Dg.wt u J z := fun z => (Dg.wt_pos u J z).le
  have hl1 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p ha
  have hl2 : 0 ≤ Real.logb p (2 * scA x ε) := logb_nat_nonneg p (by linarith)
  have hnP : (1 : ℝ) ≤ S.nP (S.twA κ) p := by exact_mod_cast S.one_le_nP _ p
  have hN : (1 : ℝ) ≤ Dg.R.N Dg.R.m := by exact_mod_cast Dg.one_le_N
  have hl3 : 0 ≤ Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) := by
    refine logb_nat_nonneg p ?_
    have h1 : (1 : ℝ) ≤ 4 * S.nP (S.twA κ) p := by linarith
    have h2 : (1 : ℝ) ≤ 4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m := one_le_mul_of_one_le_of_one_le h1 hN
    exact one_le_mul_of_one_le_of_one_le h2 ha
  have hk := Dg.one_le_k
  have hb : 0 ≤ scB x ε := (Real.exp_pos _).le
  unfold Einert
  split_ifs
  · have : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    exact add_nonneg (mul_nonneg (by positivity) hl1) (sum_nonneg fun ρ _ => div_nonneg (hw ρ) this)
  · have t1 : 0 ≤ max 0 (Dg.Fplus u J p) := le_max_left _ _
    have t2 : 0 ≤ gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) :=
      mul_nonneg (mul_nonneg (gamP_nonneg p) (Nat.cast_nonneg _)) (by linarith [Dg.eta_nonneg, Dg.cloud_nonneg])
    have t3 : 0 ≤ (Kg.cE'' : ℝ) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z / p) :=
      mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun z _ => div_nonneg (hw z) (Nat.cast_nonneg _))
    have t4 : 0 ≤ (S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
        (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1) :=
      mul_nonneg (by positivity) (by linarith)
    have t5 : 0 ≤ (Kg.cdl₁ : ℝ) * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) :=
      mul_nonneg (by positivity) hl2
    have t6 : 0 ≤ (Kg.cdl₂ : ℝ) * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2 := by positivity
    have t7 : 0 ≤ ((Dg.R.k : ℝ) - 1) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z) / (p : ℝ) ^ 3 +
        Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε) :=
      add_nonneg (div_nonneg (mul_nonneg (by linarith) (sum_nonneg fun z _ => hw z)) (by positivity))
        (mul_nonneg (by positivity) hl1)
    linarith
  · have t1 : 0 ≤ max 0 (Dg.Fplus u J p) := le_max_left _ _
    have t2 : 0 ≤ gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) :=
      mul_nonneg (mul_nonneg (gamP_nonneg p) (Nat.cast_nonneg _)) (by linarith [Dg.eta_nonneg, Dg.cloud_nonneg])
    have t3 : 0 ≤ (Kg.cE'' : ℝ) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z / p) :=
      mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun z _ => div_nonneg (hw z) (Nat.cast_nonneg _))
    have t4 : 0 ≤ (S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
        (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1) :=
      mul_nonneg (by positivity) (by linarith)
    have t5 : 0 ≤ (Kg.cdl₁ : ℝ) * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) :=
      mul_nonneg (by positivity) hl2
    have t6 : 0 ≤ (Kg.cdl₂ : ℝ) * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2 := by positivity
    linarith

/-- **The error exponent at a rational prime is nonnegative** for `x ≥ 1`. -/
theorem Eexp_rat_nonneg (hx : 1 ≤ x) (u : S.A) (ED : ErrData S Dg.R) (J : Fin Dg.R.m) (p : ℕ) :
    0 ≤ Dg.Eexp u ED J (.rat p) := by
  simp only [Eexp]
  split_ifs with h
  · exact add_nonneg (Dg.Einert_nonneg hx u J (Setting.Ranks.prime_of_mem_inertPrimes h).one_lt.le)
      (Nat.cast_nonneg _)
  · simp

/-- **The error exponent at `g_i` exceeds the forced order** by `c_E·f·(N_m² + m²η) ≥ 0`. -/
theorem Eexp_gi_sub_nonneg (u : S.A) (ED : ErrData S Dg.R) (J : Fin Dg.R.m) (i : Fin 2) :
    0 ≤ Dg.Eexp u ED J (.gi i) - Dg.Fexp u J (.gi i) := by
  simp only [Eexp, Fexp, add_sub_cancel_left]
  have := Dg.eta_nonneg
  positivity

/-- **The error at the cut is nonnegative** when the word's deviations are. -/
theorem errT_nonneg (ED : ErrData S Dg.R) (hW : ∀ ρ, 0 ≤ ED.W ρ) : 0 ≤ Dg.errT ED := by
  unfold errT
  have := sum_nonneg fun ρ (_ : ρ ∈ univ) => hW ρ
  positivity

/-- **The forced order at a rational prime is nonnegative** (`FInert_nonneg`). -/
theorem Fexp_rat_nonneg (u : S.A) (J : Fin Dg.R.m) (p : ℕ) : 0 ≤ Dg.Fexp u J (.rat p) := by
  simp only [Fexp]
  split_ifs with h
  · exact Dg.R.FInert_nonneg _ _ J (Setting.Ranks.prime_of_mem_inertPrimes h) (Dg.wj_nonneg u J)
  · exact le_rfl

/-- **The forced order at `g_i` is at most `0`** (`FTypeG_nonpos`). -/
theorem Fexp_gi_nonpos (u : S.A) (J : Fin Dg.R.m) (i : Fin 2) : Dg.Fexp u J (.gi i) ≤ 0 :=
  Dg.R.FTypeG_nonpos _ J

/-- **The forced order at `√−d` is at most `0`**: `FRamD = −((k − 1)/2)·Σ_t min(w, w) ≤ 0`. -/
theorem Fexp_sqrtd_nonpos (u : S.A) (J : Fin Dg.R.m) : Dg.Fexp u J .sqrtd ≤ 0 := by
  simp only [Fexp, Setting.Ranks.FRamD]
  have hk := Dg.one_le_k
  have hs : 0 ≤ ∑ t : S.A, (min (Dg.R.wj (Dg.hc u) J (1, t)) (Dg.R.wj (Dg.hc u) J (-1, S.twA κ * t)) : ℝ) :=
    sum_nonneg fun t _ => by exact_mod_cast le_min (Dg.wj_nonneg u J _) (Dg.wj_nonneg u J _)
  have : 0 ≤ ((Dg.R.k : ℝ) - 1) / 2 * ∑ t : S.A,
      (min (Dg.R.wj (Dg.hc u) J (1, t)) (Dg.R.wj (Dg.hc u) J (-1, S.twA κ * t)) : ℝ) :=
    mul_nonneg (by linarith) hs
  linarith

/-! ## The exponents of the special elements -/

/-- **At `g_i`** the forced order cancels: `s_{g_i} = −m·c_E·f·(N_m² + m²η)`. -/
theorem sExp_gi (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (i : Fin 2) :
    Dg.sExp pr u ED (.gi i) = -(Dg.R.m * (Kg.cE * S.f * ((Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta))) := by
  simp only [sExp, Gexp, Fexp, Eexp, tauE, Nat.cast_zero, sub_zero, zero_add, sub_add_cancel_left, sum_neg_distrib,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **At `π̄_i`**: `s_{π̄_i} = −Σ_j ν(j)`. -/
theorem sExp_gbar (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (i : Fin 2) :
    Dg.sExp pr u ED (.gbar i) = -∑ J, ED.ν J := by
  simp only [sExp, Gexp, Fexp, Eexp, tauE, Nat.cast_zero, sub_zero, zero_add, zero_sub, sum_neg_distrib]

/-- **At the cut**: `s_{π_T} = −m·err_T`. -/
theorem sExp_cut (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    Dg.sExp pr u ED .cut = -(Dg.R.m * Dg.errT ED) := by
  simp only [sExp, Gexp, Fexp, Eexp, tauE, Nat.cast_zero, sub_zero, zero_add, zero_sub, sum_neg_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **At `√−d`**: `s_{√−d} = Σ_j (2·FRamD(J) − ½·max_ω Σ_t deg_j(t))`. -/
theorem sExp_sqrtd (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    Dg.sExp pr u ED .sqrtd = ∑ J, (2 * Dg.R.FRamD (Dg.hc u) (S.twA κ) J - ED.degD J) := by
  simp only [sExp, Gexp, Fexp, Eexp, tauE, Nat.cast_zero, sub_zero, zero_add]

/-- **At a rational prime beyond `inertPrimes(X″)`** only the stabiliser denominators remain:
`s_p = −m·v_p(D_Γ)`. -/
theorem sExp_rat_of_not_mem (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) {p : ℕ}
    (h : p ∉ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    Dg.sExp pr u ED (.rat p) = -(Dg.R.m * (padicValNat p ED.DΓ : ℝ)) := by
  simp only [sExp, Gexp, Fexp, Eexp, tauE, ite_eq_right h, Dg.tau_eq_zero pr h,
    Dg.gainG_eq_zero pr u _ (fun h' => h h'.1), Nat.cast_zero, sub_zero, zero_add, zero_sub, sum_neg_distrib,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **A sum over the prime elements, by kinds**: the rational primes of `inertPrimes(X″) ∪ primes(D_Γ)`, then
`g₀, g₁, π̄₀, π̄₁, π_T, √−d`. -/
theorem sum_primeSet {M : Type*} [AddCommMonoid M] (ED : ErrData S Dg.R) (f : GainPrime → M) :
    ∑ ϖ ∈ Dg.primeSet ED, f ϖ = ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
      f (.rat p) + (f (.gi 0) + (f (.gi 1) + (f (.gbar 0) + (f (.gbar 1) + (f .cut + f .sqrtd))))) := by
  rw [primeSet, sum_union, sum_map]
  · simp [GainPrime.specials]
  · refine disjoint_left.2 fun ϖ h1 h2 => ?_
    obtain ⟨p, -, rfl⟩ := mem_map.1 h1
    simp [GainPrime.specials] at h2

/-! ## The prime elements -/

/-- **The split primes are primes.** -/
theorem gs_prime (i : Fin 2) : (Dg.gs i).Prime := by
  fin_cases i
  · simpa [gs] using Dg.g₀_prime
  · simpa [gs] using Dg.g₁_prime

/-- **The auxiliary prime is not `0`**: a prime, or the fallback `2`. -/
theorem sharpT_ne_zero (u : S.A) : sharpT Dg u ≠ 0 := by
  classical
  unfold sharpT
  split_ifs with h
  · exact (Nat.find_spec h).1.ne_zero
  · norm_num

/-- **The auxiliary prime has the shape `ArithT`** when some prime of the window does (the window of `sharpT`). -/
theorem arithT_sharpT (u : S.A) (h : ∃ T : ℕ, T.Prime ∧ Dg.ArithT T ∧
    S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - sharpCT x ε < Real.log T ∧
    Real.log T ≤ S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - sharpCT x ε + Real.log 2) :
    Dg.ArithT (sharpT Dg u) := by
  classical
  unfold sharpT
  rw [dite_eq_left h]
  exact (Nat.find_spec h).2.1

/-- **The prime elements are nonzero**: `p` and `g_i` are primes, `π̄_i` and `π_T` have nonzero norm (`normPi_ne_zero`),
and `√−d ≠ 0` (`Setting.sqrtO_ne_zero`). -/
theorem elt_ne_zero (u : S.A) (ED : ErrData S Dg.R) {ϖ : GainPrime} (h : ϖ ∈ Dg.primeSet ED) :
    Dg.elt u ϖ ≠ 0 := by
  cases ϖ with
  | rat p =>
    rw [primeSet, mem_union, mem_map] at h
    rcases h with ⟨q, hq, hqp⟩ | h
    · obtain rfl : q = p := GainPrime.rat.inj hqp
      have hp : q.Prime :=
        (mem_union.1 hq).elim Setting.Ranks.prime_of_mem_inertPrimes Nat.prime_of_mem_primeFactors
      exact Nat.cast_ne_zero.2 hp.ne_zero
    · simp [GainPrime.specials] at h
  | gi i => exact Nat.cast_ne_zero.2 (Dg.gs_prime i).ne_zero
  | gbar i => exact normPi_ne_zero (Dg.gs_prime i).ne_zero
  | cut =>
    show IsCMField.ringOfIntegersComplexConj S.E (sharpTz Dg u) ≠ 0
    exact (map_ne_zero_iff _ (IsCMField.ringOfIntegersComplexConj S.E).injective).2
      (normPi_ne_zero (Dg.sharpT_ne_zero u))
  | sqrtd => exact S.sqrtO_ne_zero

/-- **`α₀ ≠ 0`**, a product of powers of nonzero prime elements. -/
theorem gainAlpha₀_ne_zero (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) : Dg.gainAlpha₀ pr u ED ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hϖ => pow_ne_zero _ (Dg.elt_ne_zero u ED (mem_filter.1 hϖ).1)

/-- **`β₀ ≠ 0`**, a product of powers of nonzero prime elements. -/
theorem gainBeta₀_ne_zero (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) : Dg.gainBeta₀ pr u ED ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hϖ => pow_ne_zero _ (Dg.elt_ne_zero u ED (mem_filter.1 hϖ).1)

/-! ## Rounding -/

/-- **`n_ϖ ≤ s_ϖ`.** -/
theorem nExp_le (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (ϖ : GainPrime) :
    (Dg.nExp pr u ED ϖ : ℝ) ≤ Dg.sExp pr u ED ϖ :=
  Int.floor_le _

/-- **`s_ϖ < n_ϖ + 1`.** -/
theorem sExp_lt_nExp_add_one (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (ϖ : GainPrime) :
    Dg.sExp pr u ED ϖ < Dg.nExp pr u ED ϖ + 1 :=
  Int.lt_floor_add_one _

/-- **`n_ϖ = ⌊s_ϖ⌋` for `s_ϖ ≥ 0`**, the exponent of `ϖ` in `α₀`. -/
theorem nExp_eq_of_nonneg {pr : DesignPar S} {u : S.A} {ED : ErrData S Dg.R} {ϖ : GainPrime}
    (h : 0 ≤ Dg.sExp pr u ED ϖ) : Dg.nExp pr u ED ϖ = (⌊Dg.sExp pr u ED ϖ⌋₊ : ℤ) :=
  (Int.natCast_floor_eq_floor h).symm

/-- **`n_ϖ = −⌈−s_ϖ⌉` for `s_ϖ < 0`**, minus the exponent of `ϖ` in `β₀`. -/
theorem nExp_eq_of_neg {pr : DesignPar S} {u : S.A} {ED : ErrData S Dg.R} {ϖ : GainPrime}
    (h : Dg.sExp pr u ED ϖ < 0) : Dg.nExp pr u ED ϖ = -(⌈-Dg.sExp pr u ED ϖ⌉₊ : ℤ) := by
  rw [nExp, Int.natCast_ceil_eq_ceil (by linarith), Int.ceil_neg, neg_neg]

/-- **`log N(ϖ) ≥ 0`.** -/
theorem logN_nonneg (u : S.A) (ϖ : GainPrime) : 0 ≤ Dg.logN u ϖ := by
  cases ϖ with
  | rat p => exact mul_nonneg zero_le_two (Real.log_natCast_nonneg p)
  | gi i => exact mul_nonneg zero_le_two (Real.log_natCast_nonneg _)
  | gbar i => exact Real.log_natCast_nonneg _
  | cut => exact Real.log_natCast_nonneg _
  | sqrtd => exact Real.log_natCast_nonneg _

/-- **The rounding bound**: `|Σ_ϖ (n_ϖ − s_ϖ)·log N(ϖ)| ≤ Σ_ϖ log N(ϖ)`, as `|n_ϖ − s_ϖ| ≤ 1`. -/
theorem abs_sum_round_le (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    |∑ ϖ ∈ Dg.primeSet ED, ((Dg.nExp pr u ED ϖ : ℝ) - Dg.sExp pr u ED ϖ) * Dg.logN u ϖ| ≤
      ∑ ϖ ∈ Dg.primeSet ED, Dg.logN u ϖ := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ϖ _ => ?_)
  rw [abs_mul, abs_of_nonneg (Dg.logN_nonneg u ϖ)]
  have h1 := Dg.nExp_le pr u ED ϖ
  have h2 := Dg.sExp_lt_nExp_add_one pr u ED ϖ
  exact mul_le_of_le_one_left (Dg.logN_nonneg u ϖ) (abs_le.2 ⟨by linarith, by linarith⟩)

/-- **The rounding loss, one-sided** (what the index lemma reads): `Σ_ϖ n_ϖ·log N(ϖ) ≥ Σ_ϖ s_ϖ·log N(ϖ) −
Σ_ϖ log N(ϖ)`. -/
theorem sum_round_ge (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    ∑ ϖ ∈ Dg.primeSet ED, Dg.sExp pr u ED ϖ * Dg.logN u ϖ - ∑ ϖ ∈ Dg.primeSet ED, Dg.logN u ϖ ≤
      ∑ ϖ ∈ Dg.primeSet ED, (Dg.nExp pr u ED ϖ : ℝ) * Dg.logN u ϖ := by
  rw [← sum_sub_distrib]
  refine sum_le_sum fun ϖ _ => ?_
  have h2 := Dg.sExp_lt_nExp_add_one pr u ED ϖ
  have hl := Dg.logN_nonneg u ϖ
  nlinarith

/-! ## The norm of `α₀/β₀` -/

/-- **`α₀/β₀ = ∏_ϖ ϖ^{n_ϖ}`** in `E`. -/
theorem gainAlpha₀_div_gainBeta₀ (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    (Dg.gainAlpha₀ pr u ED : S.E) / Dg.gainBeta₀ pr u ED =
      ∏ ϖ ∈ Dg.primeSet ED, (Dg.elt u ϖ : S.E) ^ Dg.nExp pr u ED ϖ := by
  rw [← prod_filter_mul_prod_filter_not (Dg.primeSet ED) (fun ϖ => 0 ≤ Dg.sExp pr u ED ϖ), div_eq_mul_inv]
  have hf : (Dg.primeSet ED).filter (fun ϖ => Dg.sExp pr u ED ϖ < 0) =
      (Dg.primeSet ED).filter (fun ϖ => ¬ 0 ≤ Dg.sExp pr u ED ϖ) := filter_congr fun ϖ _ => not_le.symm
  simp only [gainAlpha₀, gainBeta₀, hf, RingOfIntegers.coe_eq_algebraMap, map_prod, map_pow]
  congr 1
  · refine prod_congr rfl fun ϖ hϖ => ?_
    rw [Dg.nExp_eq_of_nonneg (mem_filter.1 hϖ).2, zpow_natCast]
  · rw [← prod_inv_distrib]
    refine prod_congr rfl fun ϖ hϖ => ?_
    rw [Dg.nExp_eq_of_neg (not_le.1 (mem_filter.1 hϖ).2), zpow_neg, zpow_natCast]

/-- **The norm of the gain** (`log N_{F/ℚ}(α₀/β₀) = Σ_ϖ n_ϖ·log N_{F/ℚ}(ϖ)`, in the normalised form `λ`):
`λ(α₀/β₀) = Σ_ϖ n_ϖ·λ(ϖ)`. -/
theorem log_norm_gain (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    S.lnorm ((Dg.gainAlpha₀ pr u ED : S.E) / Dg.gainBeta₀ pr u ED) =
      ∑ ϖ ∈ Dg.primeSet ED, (Dg.nExp pr u ED ϖ : ℝ) * S.lnorm (Dg.elt u ϖ : S.E) := by
  rw [Dg.gainAlpha₀_div_gainBeta₀, S.lnorm_prod_zpow]
  intro ϖ hϖ h0
  exact Dg.elt_ne_zero u ED hϖ (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 S.E) S.E)).symm))

/-- `(z : E)·conj(z : E) = g` from `z·conj z = g` in `O_E`. -/
theorem coe_mul_conj {z : 𝓞 S.E} {g : ℕ} (h : z * IsCMField.ringOfIntegersComplexConj S.E z = g) :
    (z : S.E) * IsCMField.complexConj S.E (z : S.E) = g := by
  have h1 := congrArg (algebraMap (𝓞 S.E) S.E) h
  rwa [map_mul, map_natCast] at h1

/-- **The values `λ(ϖ) = log N(ϖ)`**: `λ(p) = 2 log p` (`N(p) = p^{[E:ℚ]}`), `λ(π̄_i) = log g_i` and
`λ(π_T) = log T` (`π·conj π = g`, `N(conj z) = N(z)`), `λ(√−d) = log d` (`(√−d)² = −d`); under `d ≡ 3 (mod 4)`, A11's
data at `g₀, g₁` and `ArithT` at the auxiliary prime. -/
theorem lnorm_elt (u : S.A) (hd : S.d % 4 = 3)
    (hg : ∀ i : Fin 2, ∃ a b : ℤ, 4 * (Dg.gs i : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (S.N : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * S.N])
    (hT : Dg.ArithT (sharpT Dg u)) (ϖ : GainPrime) : S.lnorm (Dg.elt u ϖ : S.E) = Dg.logN u ϖ := by
  cases ϖ with
  | rat p =>
    show S.lnorm (((p : 𝓞 S.E)) : S.E) = 2 * Real.log p
    rw [show ((p : 𝓞 S.E) : S.E) = (p : S.E) from map_natCast (algebraMap (𝓞 S.E) S.E) p]
    exact S.lnorm_natCast p
  | gi i =>
    show S.lnorm (((Dg.gs i : 𝓞 S.E)) : S.E) = 2 * Real.log (Dg.gs i)
    rw [show ((Dg.gs i : 𝓞 S.E) : S.E) = (Dg.gs i : S.E) from map_natCast (algebraMap (𝓞 S.E) S.E) _]
    exact S.lnorm_natCast _
  | gbar i => exact S.lnorm_of_mul_conj (coe_mul_conj (normPi_mul_conj_eq ⟨hd, hg i⟩))
  | cut =>
    show S.lnorm (IsCMField.complexConj S.E (sharpTz Dg u : S.E)) = Real.log (sharpT Dg u)
    rw [S.lnorm_conj]
    exact S.lnorm_of_mul_conj (coe_mul_conj (normPi_mul_conj_eq ⟨hd, hT⟩))
  | sqrtd =>
    show S.lnorm (S.sqrtO : S.E) = Real.log S.d
    rw [S.coe_sqrtO hd]
    exact S.lnorm_of_sq_eq (S.gaussE_sq hd)

/-- **The values `λ(ϖ) = log N(ϖ)` at an admissible design** (`d ≡ 7 (mod 16)` and A11), given `ArithT` at the
auxiliary prime (`arithT_sharpT`). -/
theorem lnorm_elt_of_adm (hA : Dg.Adm) (u : S.A) (hT : Dg.ArithT (sharpT Dg u)) (ϖ : GainPrime) :
    S.lnorm (Dg.elt u ϖ : S.E) = Dg.logN u ϖ := by
  refine Dg.lnorm_elt u (by have := hA.d_mod; omega) (fun i => ?_) hT ϖ
  fin_cases i
  · simpa [gs] using (hA.split Dg.g₀ (by simp)).2.2
  · simpa [gs] using (hA.split Dg.g₁ (by simp)).2.2

/-- **The norm of the gain in `log N`**: `λ(α₀/β₀) = Σ_ϖ n_ϖ·log N(ϖ)` (`log_norm_gain`, `lnorm_elt`). -/
theorem log_norm_gain_logN (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) (hd : S.d % 4 = 3)
    (hg : ∀ i : Fin 2, ∃ a b : ℤ, 4 * (Dg.gs i : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (S.N : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * S.N])
    (hT : Dg.ArithT (sharpT Dg u)) :
    S.lnorm ((Dg.gainAlpha₀ pr u ED : S.E) / Dg.gainBeta₀ pr u ED) =
      ∑ ϖ ∈ Dg.primeSet ED, (Dg.nExp pr u ED ϖ : ℝ) * Dg.logN u ϖ := by
  rw [Dg.log_norm_gain]
  simp only [Dg.lnorm_elt u hd hg hT]

/-- **The certificate's norm term**: through any `τ : E → K`, `(2/[K:ℚ])·log|N_{K/ℚ}(τα₀/τβ₀)| = Σ_ϖ n_ϖ·log N(ϖ)`
(`NumberField.log_abs_norm_map_div`, `log_norm_gain_logN`). -/
theorem log_norm_gain_map {K : Type*} [Field K] [NumberField K] (τ : S.E →+* K) (pr : DesignPar S) (u : S.A)
    (ED : ErrData S Dg.R) (hd : S.d % 4 = 3)
    (hg : ∀ i : Fin 2, ∃ a b : ℤ, 4 * (Dg.gs i : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (S.N : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * S.N])
    (hT : Dg.ArithT (sharpT Dg u)) :
    2 * Real.log |(Algebra.norm ℚ (τ (Dg.gainAlpha₀ pr u ED : S.E) / τ (Dg.gainBeta₀ pr u ED : S.E)) : ℝ)| /
        Module.finrank ℚ K = ∑ ϖ ∈ Dg.primeSet ED, (Dg.nExp pr u ED ϖ : ℝ) * Dg.logN u ϖ := by
  rw [← map_div₀, mul_div_assoc, NumberField.log_abs_norm_map_div, ← mul_div_assoc]
  exact Dg.log_norm_gain_logN pr u ED hd hg hT

/-! ## The size of the gain -/

/-- **The orbits partition the tops**: `Σ_{t₀ ∈ basePts} Σ_{s ∈ topsOn t₀} f(s) = Σ_{s ∈ TT} f(s)`. -/
theorem sum_topsOn {M : Type*} [AddCommMonoid M] (p : ℕ) (f : S.A → M) :
    ∑ t₀ ∈ Dg.basePts p, ∑ s ∈ Dg.topsOn p t₀, f s = ∑ s ∈ Dg.TT, f s :=
  sum_fiberwise_of_maps_to (fun _ hs => mem_image_of_mem _ hs) f

/-- **A top's terms are at most `γ_p·a_s`**: `Σ_{e ∈ E′} (ā_s/p^e − cap_{s,e})⁺ ≤ γ_p·a_s` for `E′ ⊆ gainExps`, when
the caps are nonnegative and `a_s ≥ 0`. -/
theorem sum_pos_le (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) (hcap : ∀ z, 0 ≤ Dg.wsh u J z + Dg.c0)
    {s : S.A} (ha : 0 ≤ Dg.a s) {E' : Finset ℕ} (hE : E' ⊆ gainExps x ε p) :
    ∑ e ∈ E', max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 ≤ gamP p * Dg.a s := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h1 : Dg.abar s ≤ Dg.a s := by unfold abar; linarith [Dg.c0_nonneg]
  calc ∑ e ∈ E', max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 ≤ ∑ e ∈ E', Dg.a s / (p : ℝ) ^ e :=
        sum_le_sum fun e _ => max_le (by
          have h2 : 0 ≤ Dg.cap u J p s e := hcap _
          have : Dg.abar s / (p : ℝ) ^ e ≤ Dg.a s / (p : ℝ) ^ e := div_le_div_of_nonneg_right h1 (by positivity)
          linarith) (div_nonneg ha (by positivity))
    _ ≤ ∑ e ∈ gainExps x ε p, Dg.a s / (p : ℝ) ^ e :=
        sum_le_sum_of_subset_of_nonneg hE fun _ _ _ => div_nonneg ha (by positivity)
    _ ≤ gamP p * Dg.a s := sum_gainExps_le hp ha

/-- **The trivial gain of an orbit is at most `γ_p·Σ_{tops} a_s`.** -/
theorem gTr_le (hx : 1 ≤ x) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) (hcap : ∀ z, 0 ≤ Dg.wsh u J z + Dg.c0)
    (ha : ∀ s ∈ Dg.TT, 0 ≤ Dg.a s) (t₀ : S.A) : Dg.gTr u J p t₀ ≤ gamP p * ∑ s ∈ Dg.topsOn p t₀, Dg.a s := by
  classical
  unfold gTr
  rw [mul_sum]
  have h0 := Dg.sl_nonneg hx p t₀
  have h1 : ∑ s ∈ Dg.topsOn p t₀, ∑ e ∈ (gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e),
      max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 ≤ ∑ s ∈ Dg.topsOn p t₀, gamP p * Dg.a s :=
    sum_le_sum fun s hs => Dg.sum_pos_le u J hp hcap (ha s (mem_filter.1 hs).1) (filter_subset _ _)
  linarith

/-- **The served gain of an orbit is at most `γ_p·Σ_{tops} a_s`.** -/
theorem gSv_le (hx : 1 ≤ x) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) (hcap : ∀ z, 0 ≤ Dg.wsh u J z + Dg.c0)
    (ha : ∀ s ∈ Dg.TT, 0 ≤ Dg.a s) (t₀ : S.A) : Dg.gSv u J p t₀ ≤ gamP p * ∑ s ∈ Dg.topsOn p t₀, Dg.a s := by
  classical
  unfold gSv
  rw [mul_sum]
  have h0 := Dg.sl_nonneg hx p t₀
  have h1 : ∑ s ∈ Dg.topsOn p t₀, (if IsVType (S.orbitStep (S.twA κ) p) s then gamP p * Dg.abar s
      else ∑ e ∈ gainExps x ε p, max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0) ≤
      ∑ s ∈ Dg.topsOn p t₀, gamP p * Dg.a s := by
    refine sum_le_sum fun s hs => ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_left (by unfold abar; linarith [Dg.c0_nonneg]) (gamP_nonneg p)
    · exact Dg.sum_pos_le u J hp hcap (ha s (mem_filter.1 hs).1) subset_rfl
  linarith

/-- **The gain is at most `γ_p·Σ_{t ∈ TT} a_t`**, when the caps and the penalties of the served orbits are
nonnegative and the scales are: each orbit's term is at most `γ_p` times its tops' scales (`gTr_le`, `gSv_le`), and
the orbits partition the tops (`sum_topsOn`). -/
theorem gainG_le (hx : 1 ≤ x) (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) (p : ℕ)
    (hcap : ∀ z, 0 ≤ Dg.wsh u J z + Dg.c0) (hpen : ∀ t₀ ∈ Dg.served p, 0 ≤ Dg.pen pr u J p t₀)
    (ha : ∀ s ∈ Dg.TT, 0 ≤ Dg.a s) : Dg.gainG pr u J p ≤ gamP p * ∑ s ∈ Dg.TT, Dg.a s := by
  unfold gainG
  split_ifs with h
  · have hp : 2 ≤ p := (Setting.Ranks.prime_of_mem_inertPrimes h.1).two_le
    rw [← Dg.sum_topsOn p, mul_sum]
    refine sum_le_sum fun t₀ _ => ?_
    have hT := Dg.gTr_le hx u J hp hcap ha t₀
    have h0 : 0 ≤ gamP p * ∑ s ∈ Dg.topsOn p t₀, Dg.a s :=
      mul_nonneg (gamP_nonneg p) (sum_nonneg fun s hs => ha s (mem_filter.1 hs).1)
    split_ifs with hs
    · refine max_le ?_ (max_le hT h0)
      have h1 := Dg.gSv_le hx u J hp hcap ha t₀
      have h2 := hpen t₀ hs
      linarith
    · exact max_le hT h0
  · exact mul_nonneg (gamP_nonneg p) (sum_nonneg ha)

/-- **The size of the gain**: `0 ≤ G_j(p) ≤ 4|TT|·a/p`, when the caps and the penalties of the served orbits are
nonnegative and `0 ≤ a_t ≤ 2a` (`gainG_le`, with `γ_p ≤ 4/(3p)`). -/
theorem gain_le (hx : 1 ≤ x) (pr : DesignPar S) (u : S.A) (J : Fin Dg.R.m) (p : ℕ)
    (hcap : ∀ z, 0 ≤ Dg.wsh u J z + Dg.c0) (hpen : ∀ t₀ ∈ Dg.served p, 0 ≤ Dg.pen pr u J p t₀)
    (ha : ∀ s ∈ Dg.TT, 0 ≤ Dg.a s ∧ Dg.a s ≤ 2 * scA x ε) :
    0 ≤ Dg.gainG pr u J p ∧ Dg.gainG pr u J p ≤ 4 * Dg.TT.card * scA x ε / p := by
  refine ⟨Dg.gainG_nonneg pr u J p, (Dg.gainG_le hx pr u J p hcap hpen fun s hs => (ha s hs).1).trans ?_⟩
  have hA : 0 ≤ scA x ε := by linarith [one_le_scA ε hx]
  have hsum : ∑ s ∈ Dg.TT, Dg.a s ≤ Dg.TT.card * (2 * scA x ε) := by
    have := sum_le_sum fun s hs => (ha s hs).2
    simpa [sum_const, nsmul_eq_mul] using this
  rcases Nat.lt_or_ge p 2 with hp | hp
  · have h0 : gamP p = 0 := by unfold gamP; interval_cases p <;> simp
    rw [h0, zero_mul]
    positivity
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hc : 0 ≤ (Dg.TT.card : ℝ) * scA x ε := by positivity
    calc gamP p * ∑ s ∈ Dg.TT, Dg.a s ≤ 4 / (3 * p) * (Dg.TT.card * (2 * scA x ε)) :=
          mul_le_mul (gamP_le hp) hsum (sum_nonneg fun s hs => (ha s hs).1) (by positivity)
      _ = 8 / 3 * (Dg.TT.card * scA x ε) / p := by field_simp; ring
      _ ≤ 4 * Dg.TT.card * scA x ε / p := by
          rw [show 4 * (Dg.TT.card : ℝ) * scA x ε = 4 * (Dg.TT.card * scA x ε) by ring]
          exact div_le_div_of_nonneg_right (by linarith) hp0.le

end SharpDesign

end

end ZetaBalance
