import CMFormalBiadd
import TorsionInt
import GqAdd

/-!
# Every prime-to-`ℓ` torsion translate is an integral unit

For a torsion point `q ∉ Λ` with `Nq ∈ Λ`, `ℓ ∤ N`, `ι`-integral `g₂`, `g₃` and the CM-b data `ε` (`‖ε‖ = 1`,
`t(ε·log_LT(T))` integral), the translate `U_q(T) = εT·G_q(z(T))`, `z(T) = ε·log_LT(T)`, is an integral power series
with `U_q(0) = 1` (`isInt_translate'`). This replaces the input `CMEquiv.TorsionTransl` (and `isInt_translate`'s
hypotheses on `G_qᴺ = P(℘) + ℘′Q(℘)`): the only arithmetic is the integrality of the torsion values of `℘` and `℘′`
(`TorsionInt`).

**Telescoping** (`Gq_pow_telescope`). Let `M` be the exact order of `q` (`M ∣ N`). Frobenius–Stickelberger
(`GqAdd.Gq_mul_Gq`, `GqAdd.Gq_sq`) with `a = q`, `b = kq` gives `G_q^{j+1} = G_{(j+1)q}·∏_{k ≤ j} R_k` with
`R_k = ζ(z) + ζ(q) + ζ(kq) − ζ(z + (k + 1)q)`, and at `j = M − 2` the lattice invariance `G_{(M−1)q} = G_{−q}`
(`GqAdd.Gq_add_lattice`) and `G_qG_{−q} = ℘ − ℘(q)` give `G_q^M = (℘ − ℘(q))·∏_{k=1}^{M−2} R_k`.

**The factors near `0`.** By the addition theorem of `ζ`, `z·R_k(z) = r_k(z) = λ_kz − ½(z³℘′(z) − ℘′(c)z³)/
(z²℘(z) − ℘(c)z²)` with `c = (k + 1)q` and `λ_k = ζ(q) + ζ(kq) − ζ(c)` (`mul_R_eq`), a function analytic at `0`
(`rfun`). So `(z·G_q)^M = (z²℘ − ℘(q)z²)·∏_k r_k` near `0` (`GqRes_pow_eventually'`), and in Taylor series
`tay(z·G_q)^M = (P − ℘(q)X²)·∏_k tay(r_k)` with `2·tay(r_k)·(P − ℘(c)X²) = 2λ_kX(P − ℘(c)X²) + 2R + ℘′(c)X³`
(`tay_rfun_mul`; `P = tay(z²℘)`, `−2R = tay(z³℘′)`).

**In Lubin–Tate coordinates.** With `ρ = ε²T²℘(z(T))` integral and `t(z(T)) = T·A₁(T)`, the substituted factors are
`ε·(log_LT(T)/T)·W_k` with `W_k = λ_kT + (2ρ + ℘′(c)T³A₁)·(2(ρ − ℘(c)T²)A₁)⁻¹` (`exists_factor_eq`), integral as
`λ_k² = ℘(q) + ℘(kq) + ℘(c)` (`GqAdd.chord_sq`, `GqAdd.tangent_sq`) and `℘(c)`, `℘′(c)` are integral. Hence
`U_q^M = ε^M(ρ − ℘(q)T²)·∏_k W_k` is integral, and so is its `M`-th root `U_q` (`isIntK_of_pow_eq`, `‖M‖ = 1`).

**Main declarations:** `Gq_pow_telescope`, `GqRes_pow_eventually'`, `tay_rfun_mul`, `exists_factor_eq`,
`isInt_translate'`; the definitions `lamK`, `rfun`.
-/

namespace TorsTransl

noncomputable section

open PowerSeries CMFormalInert CMFormalBiadd

/-! ## The telescoping product -/

section Telescope

open PeriodPair ThetaNorm CMThetaOne EllipticAdd EllipticDivisor GqAdd Filter Topology

variable (Λ : PeriodPair)

/-- **One Frobenius–Stickelberger step** `G_q·G_{kq} = G_{(k+1)q}·(ζ(z) + ζ(q) + ζ(kq) − ζ(z + (k + 1)q))` for
`1 ≤ k`, `k + 1 < M` (tangent case `k = 1`, chord case `k ≥ 2`). -/
theorem Gq_mul_Gq_step {q : ℂ} {M : ℕ} (hk : ∀ k : ℕ, 0 < k → k < M → (k : ℂ) * q ∉ Λ.lattice) {z : ℂ}
    (hz : z ∉ Λ.lattice) (hzk : ∀ k : ℕ, 0 < k → k < M → z + k * q ∉ Λ.lattice)
    (hzh : ∀ k : ℕ, 0 < k → k < M → z + k * q / 2 ∉ Λ.lattice) {k : ℕ} (hk1 : 1 ≤ k) (hkM : k + 1 < M) :
    Gq Λ q z * Gq Λ ((k : ℕ) * q) z = Gq Λ ((k + 1 : ℕ) * q) z *
      (zetaW Λ z + zetaW Λ q + zetaW Λ ((k : ℕ) * q) - zetaW Λ (z + (k + 1 : ℕ) * q)) := by
  have hq : q ∉ Λ.lattice := by simpa using hk 1 one_pos (by omega)
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
  · have h := Gq_sq Λ hq (by simpa using hk 2 two_pos (by omega)) hz (by simpa using hzk 1 one_pos (by omega))
      (by simpa using hzk 2 two_pos (by omega))
    norm_num
    rw [← sq, h]
    ring
  · have e : q + (k : ℂ) * q = ((k + 1 : ℕ) : ℂ) * q := by push_cast; ring
    have hamb : q - (k : ℂ) * q ∉ Λ.lattice := by
      intro h
      refine hk (k - 1) (by omega) (by omega) ?_
      rw [Nat.cast_sub (by omega)]
      simpa [sub_mul, neg_sub] using neg_mem h
    have h := Gq_mul_Gq Λ hq (hk k (by omega) (by omega)) (by rw [e]; exact hk _ (by omega) hkM) hamb hz
      (by rw [e]; exact hzk _ (by omega) hkM) (by rw [e]; exact hzh _ (by omega) hkM)
    rw [h, e]

/-- **The telescoping product** `G_q^M = (℘ − ℘(q))·∏_{k=0}^{M−3} (ζ(z) + ζ(q) + ζ((k+1)q) − ζ(z + (k+2)q))` for `q`
of exact order `M ≥ 2` (oriented: `G_{(M−1)q} = G_{−q}`). -/
theorem Gq_pow_telescope (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} {M : ℕ} (hM2 : 2 ≤ M)
    (hMq : (M : ℂ) * q ∈ Λ.lattice) (hk : ∀ k : ℕ, 0 < k → k < M → (k : ℂ) * q ∉ Λ.lattice) {z : ℂ}
    (hz : z ∉ Λ.lattice) (hzk : ∀ k : ℕ, 0 < k → k < M → z + k * q ∉ Λ.lattice)
    (hzh : ∀ k : ℕ, 0 < k → k < M → z + k * q / 2 ∉ Λ.lattice) :
    Gq Λ q z ^ M = (℘[Λ] z - ℘[Λ] q) * ∏ k ∈ Finset.range (M - 2),
      (zetaW Λ z + zetaW Λ q + zetaW Λ ((k + 1 : ℕ) * q) - zetaW Λ (z + (k + 2 : ℕ) * q)) := by
  have hq : q ∉ Λ.lattice := by simpa using hk 1 one_pos (by omega)
  have hT : ∀ j, j + 2 ≤ M → Gq Λ q z ^ (j + 1) = Gq Λ ((j + 1 : ℕ) * q) z * ∏ k ∈ Finset.range j,
      (zetaW Λ z + zetaW Λ q + zetaW Λ ((k + 1 : ℕ) * q) - zetaW Λ (z + (k + 2 : ℕ) * q)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [pow_succ', ih (by omega), ← mul_assoc, Gq_mul_Gq_step Λ hk hz hzk hzh (k := j + 1) (by omega) (by omega),
        Finset.prod_range_succ]
      push_cast
      ring_nf
  have hM1 : ((M - 1 : ℕ) : ℂ) * q = -q + M * q := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h := hT (M - 2) (by omega)
  rw [show M - 2 + 1 = M - 1 by omega, hM1, Gq_add_lattice Λ hor (by simpa using neg_mem_iff.not.mpr hq) hMq] at h
  rw [show M = M - 1 + 1 by omega, pow_succ', h, ← mul_assoc, Gq_mul_Gq_neg Λ hq hz, show M - 1 + 1 - 2 = M - 2 by
    omega]

/-- **The chord constant** `λ_k = ζ(q) + ζ(kq) − ζ((k + 1)q)`. -/
def lamK (q : ℂ) (k : ℕ) : ℂ := zetaW Λ q + zetaW Λ ((k : ℕ) * q) - zetaW Λ ((k + 1 : ℕ) * q)

/-- **The factor `z·R(z)` near `0`**: `r(z) = λz − ½(z³℘′(z) − ℘′(c)z³)/(z²℘(z) − ℘(c)z²)`, analytic at `0`. -/
def rfun (lam c z : ℂ) : ℂ := lam * z - (wpV Λ z - ℘'[Λ] c * z ^ 3) / (2 * (wpU Λ z - ℘[Λ] c * z ^ 2))

/-- **`z·(ζ(z) + μ − ζ(z + c)) = r(z)`** with `λ = μ − ζ(c)` (`zetaW_add` at `(z, c)`). -/
theorem mul_R_eq {z c : ℂ} (μ : ℂ) (hz0 : z ≠ 0) (hz : z ∉ Λ.lattice) (hc : c ∉ Λ.lattice)
    (hzc : z + c ∉ Λ.lattice) (hzmc : z - c ∉ Λ.lattice) :
    z * (zetaW Λ z + μ - zetaW Λ (z + c)) = rfun Λ (μ - zetaW Λ c) c z := by
  rw [rfun, ← sq_mul_weierstrassP Λ hz0, ← cube_mul_derivWeierstrassP Λ hz0, zetaW_add Λ hz hc hzc hzmc,
    show z ^ 3 * ℘'[Λ] z - ℘'[Λ] c * z ^ 3 = z ^ 2 * (z * (℘'[Λ] z - ℘'[Λ] c)) by ring,
    show 2 * (z ^ 2 * ℘[Λ] z - ℘[Λ] c * z ^ 2) = z ^ 2 * (2 * (℘[Λ] z - ℘[Λ] c)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hz0)]
  ring

/-- **`r` is analytic at `0`** (the denominator is `2` at `0`). -/
theorem analyticAt_rfun (lam c : ℂ) : AnalyticAt ℂ (rfun Λ lam c) 0 := by
  have hU := (analyticAt_wpU Λ).1
  have hV := (EllipticDivisor.analyticAt_wpV Λ).1
  refine (analyticAt_const.mul analyticAt_id).sub ((hV.sub (by fun_prop)).div (analyticAt_const.mul
    (hU.sub (by fun_prop))) ?_)
  simp [(analyticAt_wpU Λ).2]

/-- **Near `0`, `w`-translates stay off the lattice** for `w ∉ Λ`. -/
theorem eventually_add_not_mem {w : ℂ} (hw : w ∉ Λ.lattice) : ∀ᶠ z in 𝓝 0, z + w ∉ Λ.lattice :=
  ((continuous_id.add continuous_const : Continuous fun z : ℂ => z + w).tendsto' 0 w (zero_add w)).eventually
    (Λ.isClosed_lattice.isOpen_compl.mem_nhds hw)

/-- **The telescoped product near `0`**: `(z·G_q)^M = (z²℘ − ℘(q)z²)·∏_{k < M−2} r_k(z)` on a neighbourhood of `0`,
`r_k = rfun (λ_{k+1}) ((k + 2)q)` (both sides are analytic at `0`). -/
theorem GqRes_pow_eventually' (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q : ℂ} {m : ℕ}
    (hMq : ((m + 2 : ℕ) : ℂ) * q ∈ Λ.lattice) (hk : ∀ k : ℕ, 0 < k → k < m + 2 → (k : ℂ) * q ∉ Λ.lattice) :
    (fun z => GqRes Λ q z ^ (m + 2)) =ᶠ[𝓝 0] fun z => (wpU Λ z - ℘[Λ] q * z ^ 2) *
      ∏ k ∈ Finset.range m, rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q) z := by
  have hq : q ∉ Λ.lattice := by simpa using hk 1 one_pos (by omega)
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ k ∈ Finset.range (m + 2), 0 < k →
      z + k * q ∉ Λ.lattice ∧ z + k * q / 2 ∉ Λ.lattice ∧ z + -(k * q) ∉ Λ.lattice := by
    refine (eventually_all_finset _).2 fun k hk' => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Eventually.of_forall fun _ h => absurd h (lt_irrefl 0)
    have hkq := hk k hk0 (Finset.mem_range.1 hk')
    filter_upwards [eventually_add_not_mem Λ hkq,
      eventually_add_not_mem Λ (w := k * q / 2) (fun h => hkq (by simpa using add_mem h h)),
      eventually_add_not_mem Λ (w := -(k * q)) (fun h => hkq (by simpa using neg_mem h))] with z h1 h2 h3 _
    exact ⟨h1, h2, h3⟩
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), GqRes Λ q z ^ (m + 2) = (wpU Λ z - ℘[Λ] q * z ^ 2) *
      ∏ k ∈ Finset.range m, rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q) z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds hev] with z hz0 hzΛ hzk
    have hz0' : z ≠ 0 := hz0
    have hz : z ∉ Λ.lattice := fun h => hzΛ ⟨h, hz0⟩
    have hT := Gq_pow_telescope Λ hor (by omega) hMq hk hz
      (fun k h0 hkM => (hzk k (Finset.mem_range.2 hkM) h0).1) (fun k h0 hkM => (hzk k (Finset.mem_range.2 hkM) h0).2.1)
    rw [Nat.add_sub_cancel] at hT
    have hprod : ∏ k ∈ Finset.range m, rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q) z = ∏ k ∈ Finset.range m,
        z * (zetaW Λ z + zetaW Λ q + zetaW Λ ((k + 1 : ℕ) * q) - zetaW Λ (z + (k + 2 : ℕ) * q)) := by
      refine Finset.prod_congr rfl fun k hk' => ?_
      have hkm := Finset.mem_range.1 hk'
      have hc : ((k + 2 : ℕ) : ℂ) * q ∉ Λ.lattice := hk (k + 2) (by omega) (by omega)
      obtain ⟨h1, -, h3⟩ := hzk (k + 2) (Finset.mem_range.2 (by omega)) (by omega)
      have e := mul_R_eq Λ (zetaW Λ q + zetaW Λ ((k + 1 : ℕ) * q)) hz0' hz hc h1 (by rwa [sub_eq_add_neg])
      rw [show lamK Λ q (k + 1) = zetaW Λ q + zetaW Λ ((k + 1 : ℕ) * q) - zetaW Λ ((k + 2 : ℕ) * q) from rfl, ← e]
      ring
    rw [← mul_Gq Λ hz0', mul_pow, hT, ← sq_mul_weierstrassP Λ hz0', hprod, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
    ring
  have hcL : ContinuousAt (fun z => GqRes Λ q z ^ (m + 2)) 0 := ((analyticAt_GqRes Λ hq).1.pow _).continuousAt
  have hcR : ContinuousAt (fun z => (wpU Λ z - ℘[Λ] q * z ^ 2) *
      ∏ k ∈ Finset.range m, rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q) z) 0 :=
    (((analyticAt_wpU Λ).1.sub (by fun_prop)).mul
      (Finset.analyticAt_fun_prod _ fun k _ => analyticAt_rfun Λ _ _)).continuousAt
  exact (hcL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcR).1 hpunct

/-! ## Taylor series -/

/-- **`tay` of a finite product.** -/
theorem tay_prod {ι : Type} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    tay (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, tay (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tay_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [tay_mul (hf a (Finset.mem_insert_self a s)) (Finset.analyticAt_fun_prod _ fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)), ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **`tay(z²℘ − x·z²) = P − x·X²`.** -/
theorem tay_wpU_sub (x : ℂ) : tay (fun z => wpU Λ z - x * z ^ 2) = wpF Λ.g₂ Λ.g₃ - C x * X ^ 2 := by
  have hU := (analyticAt_wpU Λ).1
  rw [tay_sub hU (by fun_prop), tay_wpU, tay_mul analyticAt_const (by fun_prop), tay_const,
    tay_pow (f := fun z => z) analyticAt_id, tay_id]

/-- **The Taylor series of `r`**: `2·tay(r)·(P − ℘(c)X²) = 2λX(P − ℘(c)X²) + 2R + ℘′(c)X³` (`P = tay(z²℘)`,
`−2R = tay(z³℘′)`). -/
theorem tay_rfun_mul (lam c : ℂ) :
    2 * tay (rfun Λ lam c) * (wpF Λ.g₂ Λ.g₃ - C (℘[Λ] c) * X ^ 2) =
      2 * C lam * X * (wpF Λ.g₂ Λ.g₃ - C (℘[Λ] c) * X ^ 2) + 2 * wpR Λ.g₂ Λ.g₃ + C (℘'[Λ] c) * X ^ 3 := by
  have hU := (analyticAt_wpU Λ).1
  have hV := CMFormalBiadd.analyticAt_wpV Λ
  have hr := analyticAt_rfun Λ lam c
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), wpU Λ z - ℘[Λ] c * z ^ 2 ≠ 0 :=
    (hU.sub (by fun_prop)).continuousAt.eventually_ne (by simp [(analyticAt_wpU Λ).2])
  have hev : (fun z => (2 * rfun Λ lam c z) * (wpU Λ z - ℘[Λ] c * z ^ 2)) =ᶠ[𝓝 0]
      fun z => (2 * lam * z * (wpU Λ z - ℘[Λ] c * z ^ 2) - wpV Λ z) + ℘'[Λ] c * z ^ 3 := by
    filter_upwards [hne] with z hz
    have e : (wpV Λ z - ℘'[Λ] c * z ^ 3) / (2 * (wpU Λ z - ℘[Λ] c * z ^ 2)) * (2 * (wpU Λ z - ℘[Λ] c * z ^ 2)) =
        wpV Λ z - ℘'[Λ] c * z ^ 3 := div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hz)
    rw [rfun]
    linear_combination (-1 : ℂ) * e
  have hf : AnalyticAt ℂ (fun z => wpU Λ z - ℘[Λ] c * z ^ 2) 0 := hU.sub (by fun_prop)
  have hL : tay (fun z => (2 * rfun Λ lam c z) * (wpU Λ z - ℘[Λ] c * z ^ 2)) =
      C 2 * tay (rfun Λ lam c) * (wpF Λ.g₂ Λ.g₃ - C (℘[Λ] c) * X ^ 2) := by
    rw [tay_mul (f := fun z => 2 * rfun Λ lam c z) (by fun_prop) hf,
      tay_mul (f := fun _ => (2 : ℂ)) (g := rfun Λ lam c) (by fun_prop) hr, tay_const, tay_wpU_sub]
  have hR : tay (fun z => (2 * lam * z * (wpU Λ z - ℘[Λ] c * z ^ 2) - wpV Λ z) + ℘'[Λ] c * z ^ 3) =
      C (2 * lam) * X * (wpF Λ.g₂ Λ.g₃ - C (℘[Λ] c) * X ^ 2) - -2 * wpR Λ.g₂ Λ.g₃ + C (℘'[Λ] c) * X ^ 3 := by
    rw [tay_add (f := fun z => 2 * lam * z * (wpU Λ z - ℘[Λ] c * z ^ 2) - wpV Λ z) (by fun_prop) (by fun_prop),
      tay_sub (f := fun z => 2 * lam * z * (wpU Λ z - ℘[Λ] c * z ^ 2)) (g := wpV Λ) (by fun_prop) hV,
      tay_mul (f := fun z => 2 * lam * z) (by fun_prop) hf,
      tay_mul (f := fun _ => 2 * lam) (g := fun z => z) (by fun_prop) (by fun_prop), tay_const, tay_id,
      tay_wpU_sub, tay_wpV, tay_mul (f := fun _ => ℘'[Λ] c) (g := fun z => z ^ 3) (by fun_prop) (by fun_prop),
      tay_const, tay_pow (f := fun z => z) analyticAt_id, tay_id]
  have h := tay_congr hev
  rw [hL, hR, map_mul, map_ofNat] at h
  rw [h]
  ring

end Telescope

/-! ## Lubin–Tate coordinates -/

section LT

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`‖2‖ = 1`** in `ℂ_ℓ` for `ℓ ≠ 2`. -/
theorem norm_two_eq_one (hℓ2 : ℓ ≠ 2) : ‖(2 : ℂ_[ℓ])‖ = 1 := by
  have h := CMThetaOne.norm_natCast_padicComplex (ℓ := ℓ) (n := 2) ((Nat.coprime_primes hℓp.out Nat.prime_two).mpr hℓ2)
  rwa [Nat.cast_ofNat] at h

/-- **`z(T) = εT·(log_LT(T)/T)`.** -/
theorem zLT_eq (ε : ℂ_[ℓ]) : zLT ℓ ε = C ε * X * logLTDivX ℂ_[ℓ] ℓ := by
  rw [zLT, ← X_mul_logLTDivX hℓp.out.one_lt, mul_assoc]

/-- **`P(z(T)) = ε²(log_LT(T)/T)²·ρ`** (`X_sq_mul_wpF_subst`). -/
theorem wpF_subst_eq {a b ε : ℂ_[ℓ]} (hε : ε ≠ 0) :
    (wpF a b).subst (zLT ℓ ε) = C ε ^ 2 * logLTDivX ℂ_[ℓ] ℓ ^ 2 * rhoLT ℓ a b ε := by
  have h := X_sq_mul_wpF_subst hℓp.out.one_lt hε a b
  generalize (wpF a b).subst (zLT ℓ ε) = P at h ⊢
  rw [zLT_eq] at h
  refine mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) ?_
  linear_combination h

/-- **`t(z(T)) = T·A₁(T)`** with `A₁` integral, `A₁(0) = ε` and `A₁·R(z(T)) = ε³(log_LT(T)/T)³·ρ` (from
`t = zP/R`). -/
theorem exists_A₁ {a b ε : ℂ_[ℓ]} (hε : ε ≠ 0) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) :
    ∃ A₁ : ℂ_[ℓ]⟦X⟧, IsInt A₁ ∧ constantCoeff A₁ = ε ∧
      A₁ * (wpR a b).subst (zLT ℓ ε) = C ε ^ 3 * logLTDivX ℂ_[ℓ] ℓ ^ 3 * rhoLT ℓ a b ε := by
  have hℓ := hℓp.out.one_lt
  have hPz := wpF_subst_eq (a := a) (b := b) hε
  set z := zLT ℓ ε with hzdef
  have hz0 : constantCoeff z = 0 := constantCoeff_zLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  set A := (tSer a b).subst z
  have hA0 : constantCoeff A = 0 := constantCoeff_subst_eq_zero hz0 _ (constantCoeff_tSer a b)
  set A₁ : ℂ_[ℓ]⟦X⟧ := mk fun n => coeff (n + 1) A
  have hA : A = X * A₁ := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, hA0, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
        zero_mul]
    · rw [coeff_succ_X_mul, coeff_mk]
  refine ⟨A₁, fun n => by rw [coeff_mk]; exact ht (n + 1), ?_, ?_⟩
  · have h1 := congrArg (coeff 1) hA
    have h2 : coeff 1 ((tSer a b).subst z) = ε := by
      rw [coeff_one_subst hz0, coeff_one_tSer, hzdef, zLT, coeff_C_mul, coeff_one_logLT, one_mul, mul_one]
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h1
    rw [← h1]
    exact h2
  · set Rz := (wpR a b).subst z
    have hR0 : constantCoeff (wpR a b) ≠ 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, wpR, coeff_mk]; simp
    have htR : tSer a b * wpR a b = X * wpF a b := by
      rw [tSer_eq, mul_assoc, mul_assoc, PowerSeries.inv_mul_cancel _ hR0, mul_one]
    have h : A * Rz = z * (wpF a b).subst z := by
      have := congrArg (PowerSeries.subst z) htR
      rwa [subst_mul hzs, subst_mul hzs, subst_X hzs] at this
    rw [hA, hPz, hzdef, zLT_eq] at h
    refine mul_left_cancel₀ X_ne_zero ?_
    linear_combination h

/-- **A unit integral series has an integral inverse.** -/
theorem isInt_inv {f : ℂ_[ℓ]⟦X⟧} (hf : IsInt f) (h0 : ‖constantCoeff f‖ = 1) : IsInt f⁻¹ := by
  set c := constantCoeff f
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [h0]; exact one_ne_zero)
  have hci : IsInt (C c⁻¹ : ℂ_[ℓ]⟦X⟧) := isInt_C (by rw [norm_inv, h0, inv_one])
  have hv1 : MvPowerSeries.constantCoeff ((C c⁻¹ * f : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) = 1 := by
    change constantCoeff (C c⁻¹ * f) = 1
    rw [map_mul, constantCoeff_C, inv_mul_cancel₀ hc0]
  have hi := (hci.mul hf).isIntK.inv hv1 |>.isInt
  have e : f⁻¹ = C c⁻¹ * (C c⁻¹ * f)⁻¹ := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hc0]
    have h1 : (C c⁻¹ * f)⁻¹ * (C c⁻¹ * f) = 1 := PowerSeries.inv_mul_cancel _ (by
      change MvPowerSeries.constantCoeff ((C c⁻¹ * f : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) ≠ 0
      rw [hv1]
      exact one_ne_zero)
    linear_combination h1
  rw [e]
  exact hci.mul hi

/-- **`(P − xX²)(z(T)) = ε²(log_LT(T)/T)²·(ρ − xT²)`.** -/
theorem subst_wpF_sub {a b ε : ℂ_[ℓ]} (hε : ε ≠ 0) (x : ℂ_[ℓ]) :
    (wpF a b - C x * X ^ 2).subst (zLT ℓ ε) =
      C ε ^ 2 * logLTDivX ℂ_[ℓ] ℓ ^ 2 * (rhoLT ℓ a b ε - C x * X ^ 2) := by
  have hzs : HasSubst (zLT ℓ ε) := HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓp.out.one_lt ε)
  rw [← coe_substAlgHom hzs, map_sub, map_mul, map_pow, coe_substAlgHom hzs, subst_X hzs, subst_C, wpF_subst_eq hε,
    zLT_eq]
  change _ - C x * _ = _
  ring

/-- **A factor in Lubin–Tate coordinates**: if `2T·(P − xX²) = 2λX(P − xX²) + 2R + yX³` with `λ`, `x`, `y`
integral, then `T(z(T)) = ε·(log_LT(T)/T)·W` with `W = λT + (2ρ + yT³A₁)·(2(ρ − xT²)A₁)⁻¹` integral. -/
theorem exists_factor_eq (hℓ2 : ℓ ≠ 2) {a b ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) {lam x y : ℂ_[ℓ]} (hlam : ‖lam‖ ≤ 1)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {T : ℂ_[ℓ]⟦X⟧}
    (hT : 2 * T * (wpF a b - C x * X ^ 2) = 2 * C lam * X * (wpF a b - C x * X ^ 2) + 2 * wpR a b + C y * X ^ 3) :
    ∃ W, IsInt W ∧ T.subst (zLT ℓ ε) = C ε * logLTDivX ℂ_[ℓ] ℓ * W := by
  have hℓ := hℓp.out.one_lt
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hzs : HasSubst (zLT ℓ ε) := HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓ ε)
  obtain ⟨A₁, hA₁i, hA₁0, hRz⟩ := exists_A₁ hε0 ht
  have hρi := isInt_rhoLT hℓ2 ha hb hε hODE ht
  have h2i : IsInt (2 : ℂ_[ℓ]⟦X⟧) := by
    rw [← map_ofNat C 2]; exact isInt_C (norm_two_eq_one hℓ2).le
  have hId := congrArg (PowerSeries.subst (zLT ℓ ε)) hT
  rw [← coe_substAlgHom hzs] at hId
  have hC : ∀ r : ℂ_[ℓ], (MvPowerSeries.C r : MvPowerSeries Unit ℂ_[ℓ]) = C r := fun _ => rfl
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, coe_substAlgHom hzs, subst_X hzs, subst_C, hC] at hId
  set lam' := logLTDivX ℂ_[ℓ] ℓ
  set ρ := rhoLT ℓ a b ε
  set S := T.subst (zLT ℓ ε)
  set Rz := (wpR a b).subst (zLT ℓ ε)
  rw [wpF_subst_eq hε0, zLT_eq] at hId
  set V := 2 * (ρ - C x * X ^ 2) * A₁
  have hρ0 : constantCoeff ρ = ε⁻¹ ^ 2 := constantCoeff_rhoLT hℓ a b ε
  have hV0 : constantCoeff V = 2 * ε⁻¹ := by
    simp only [V, map_mul, map_sub, map_ofNat, hA₁0, hρ0, constantCoeff_C, map_pow, constantCoeff_X, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    field_simp
  have hVn : ‖constantCoeff V‖ = 1 := by rw [hV0, norm_mul, norm_two_eq_one hℓ2, norm_inv, hε, inv_one, one_mul]
  have hVne : constantCoeff V ≠ 0 := norm_ne_zero_iff.mp (by rw [hVn]; exact one_ne_zero)
  have hVi : IsInt V⁻¹ := isInt_inv ((h2i.mul (hρi.sub ((isInt_C hx).mul (isInt_X_pow 2)))).mul hA₁i) hVn
  refine ⟨C lam * X + (2 * ρ + C y * X ^ 3 * A₁) * V⁻¹, ?_, ?_⟩
  · refine ((isInt_C hlam).mul (by simpa using isInt_X_pow (K := ℂ_[ℓ]) 1)).add (IsInt.mul ?_ hVi)
    exact (h2i.mul hρi).add (((isInt_C hy).mul (isInt_X_pow 3)).mul hA₁i)
  · have hVV : V⁻¹ * V = 1 := PowerSeries.inv_mul_cancel _ hVne
    have hK : C ε ^ 2 * lam' ^ 2 * V ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      rw [map_mul, map_mul, map_pow, map_pow, constantCoeff_C, constantCoeff_logLTDivX, map_zero] at this
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hε0) (by simp)) hVne this
    refine mul_right_cancel₀ hK ?_
    linear_combination A₁ * hId + 2 * hRz - (C ε ^ 3 * lam' ^ 3 * (2 * ρ + C y * X ^ 3 * A₁)) * hVV

end LT

/-! ## The translates are integral units -/

section Translate

open PeriodPair EllipticDivisor

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The exact order** `m + 2` of a torsion point `q ∉ Λ` with `Nq ∈ Λ`, `N > 0`: `(m + 2)q ∈ Λ`, `kq ∉ Λ` for
`0 < k < m + 2`, and `m + 2 ∣ N`. -/
theorem exists_order {Λ : PeriodPair} {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hN0 : 0 < N)
    (hNq : (N : ℂ) * q ∈ Λ.lattice) : ∃ m : ℕ, ((m + 2 : ℕ) : ℂ) * q ∈ Λ.lattice ∧
      (∀ k : ℕ, 0 < k → k < m + 2 → (k : ℂ) * q ∉ Λ.lattice) ∧ m + 2 ∣ N := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ (k : ℂ) * q ∈ Λ.lattice := ⟨N, hN0, hNq⟩
  obtain ⟨hM0, hMq⟩ := Nat.find_spec hex
  have hk : ∀ k, 0 < k → k < Nat.find hex → (k : ℂ) * q ∉ Λ.lattice :=
    fun k h0 hkM h => Nat.find_min hex hkM ⟨h0, h⟩
  have hM2 : 2 ≤ Nat.find hex := by
    by_contra h
    have h1 : Nat.find hex = 1 := by omega
    rw [h1] at hMq
    exact hq (by simpa using hMq)
  refine ⟨Nat.find hex - 2, by rwa [Nat.sub_add_cancel hM2], fun k h0 hk' => hk k h0 (by omega), ?_⟩
  rw [Nat.sub_add_cancel hM2]
  by_contra hd
  have hr : 0 < N % Nat.find hex := Nat.pos_of_ne_zero fun h0 => hd (Nat.dvd_of_mod_eq_zero h0)
  refine hk (N % Nat.find hex) hr (Nat.mod_lt _ hM0) ?_
  have e : ((N % Nat.find hex : ℕ) : ℂ) * q =
      (N : ℂ) * q - ((N / Nat.find hex : ℕ) : ℤ) • ((Nat.find hex : ℂ) * q) := by
    have h' : ((N % Nat.find hex : ℕ) : ℂ) + (Nat.find hex : ℂ) * (N / Nat.find hex : ℕ) = N := by
      exact_mod_cast Nat.mod_add_div N (Nat.find hex)
    rw [zsmul_eq_mul, Int.cast_natCast]
    linear_combination q * h'
  rw [e]
  exact sub_mem hNq (zsmul_mem hMq _)

/-- **Every prime-to-`ℓ` torsion translate is an integral unit** (replaces `CMEquiv.TorsionTransl` and
`isInt_translate`'s hypotheses; oriented): for `q ∉ Λ`, `Nq ∈ Λ`, `ℓ ∤ N`, the series
`U_q = (log_LT(T)/T)⁻¹·(z·G_q)(z(T))` is integral with `U_q(0) = 1`. With `M = m + 2` the exact order of `q`,
`U_q^M = ε^M(ρ − ℘(q)T²)·∏_{k<m} W_k` (`Gq_pow_telescope`, `exists_factor_eq`), the constants `λ_k`, `℘(c_k)`,
`℘′(c_k)` being integral (`GqAdd.chord_sq`, `GqAdd.tangent_sq`, `TorsionInt`), and `‖M‖ = 1` (`M ∣ N`). -/
theorem isInt_translate' (hℓ2 : ℓ ≠ 2) (Λ : PeriodPair) (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) (ι : ℂ →+* ℂ_[ℓ])
    (h2 : ‖ι Λ.g₂‖ ≤ 1) (h3 : ‖ι Λ.g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε))) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ}
    (hNℓ : ¬ ℓ ∣ N) (hNq : (N : ℂ) * q ∈ Λ.lattice) :
    IsInt ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (GqRes Λ q))).subst (zLT ℓ ε)) ∧
      constantCoeff ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (GqRes Λ q))).subst (zLT ℓ ε)) = 1 := by
  have hℓ := hℓp.out.one_lt
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h0 => hNℓ (h0 ▸ dvd_zero ℓ)
  obtain ⟨m, hMq, hk, hMN⟩ := exists_order hq hN0 hNq
  have hMn : ‖((m + 2 : ℕ) : ℂ_[ℓ])‖ = 1 := CMThetaOne.norm_natCast_padicComplex
    ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 fun h => hNℓ (h.trans hMN))
  -- the torsion values are integral
  have hjN : ∀ j : ℕ, (N : ℂ) * ((j : ℂ) * q) ∈ Λ.lattice := fun j => by
    rw [show (N : ℂ) * ((j : ℂ) * q) = ((j : ℤ) : ℂ) * ((N : ℂ) * q) by push_cast; ring, ← zsmul_eq_mul]
    exact zsmul_mem hNq _
  have hwp : ∀ j : ℕ, 0 < j → j < m + 2 → ‖ι (℘[Λ] ((j : ℂ) * q))‖ ≤ 1 := fun j h0 hj =>
    TorsionInt.norm_iota_weierstrassP_le_one Λ hℓ2 ι h2 h3 (hk j h0 hj) hNℓ (hjN j)
  have hwp' : ∀ j : ℕ, 0 < j → j < m + 2 → ‖ι (℘'[Λ] ((j : ℂ) * q))‖ ≤ 1 := fun j h0 hj =>
    TorsionInt.norm_iota_derivWeierstrassP_le_one Λ hℓ2 ι h2 h3 (hk j h0 hj) hNℓ (hjN j)
  have hq1 : ‖ι (℘[Λ] q)‖ ≤ 1 := by simpa using hwp 1 one_pos (by omega)
  have hlam : ∀ k : ℕ, 0 < k → k + 1 < m + 2 → ‖ι (lamK Λ q k)‖ ≤ 1 := by
    intro k h0 hkM
    have hsq : lamK Λ q k ^ 2 = ℘[Λ] q + ℘[Λ] ((k : ℕ) * q) + ℘[Λ] ((k + 1 : ℕ) * q) := by
      rcases Nat.eq_or_lt_of_le h0 with rfl | hk2
      · have h := GqAdd.tangent_sq Λ hq (by simpa using hk 2 two_pos (by omega))
        have e1 : ((1 : ℕ) : ℂ) * q = q := by simp
        have e2 : ((0 + 1 + 1 : ℕ) : ℂ) * q = 2 * q := by push_cast; ring
        rw [lamK, e1, e2]
        linear_combination h
      · have e : q + (k : ℂ) * q = ((k + 1 : ℕ) : ℂ) * q := by push_cast; ring
        have hamb : q - (k : ℂ) * q ∉ Λ.lattice := by
          intro h
          refine hk (k - 1) (by omega) (by omega) ?_
          rw [Nat.cast_sub (by omega)]
          simpa [sub_mul, neg_sub] using neg_mem h
        have h := GqAdd.chord_sq Λ hq (hk k h0 (by omega)) (by rw [e]; exact hk _ (by omega) hkM) hamb
        rw [e] at h
        exact h
    have h' : ‖ι (lamK Λ q k)‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, ← map_pow, hsq, ← CMThetaOne.mem_intSub]
      exact add_mem (add_mem (CMThetaOne.mem_intSub.mpr hq1) (CMThetaOne.mem_intSub.mpr (hwp k h0 (by omega))))
        (CMThetaOne.mem_intSub.mpr (hwp (k + 1) (by omega) hkM))
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h'
  -- the telescoped product as Taylor series
  have htay : tay (GqRes Λ q) ^ (m + 2) = (wpF Λ.g₂ Λ.g₃ - C (℘[Λ] q) * X ^ 2) *
      ∏ k ∈ Finset.range m, tay (rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q)) := by
    rw [← tay_pow (analyticAt_GqRes Λ hq).1, tay_congr (GqRes_pow_eventually' Λ hor hMq hk),
      tay_mul (f := fun z => wpU Λ z - ℘[Λ] q * z ^ 2)
        (g := fun z => ∏ k ∈ Finset.range m, rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q) z)
        ((analyticAt_wpU Λ).1.sub (by fun_prop)) (Finset.analyticAt_fun_prod _ fun k _ => analyticAt_rfun Λ _ _),
      tay_wpU_sub, tay_prod _ fun k _ => analyticAt_rfun Λ _ _]
  -- in Lubin–Tate coordinates
  have hODE := (weierODE_lattice Λ).map ι
  set z := zLT ℓ ε with hzdef
  have hz0 : constantCoeff z = 0 := constantCoeff_zLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  set lam' := logLTDivX ℂ_[ℓ] ℓ
  have hfac : ∀ k ∈ Finset.range m, ∃ W, IsInt W ∧
      (map ι (tay (rfun Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q)))).subst z = C ε * lam' * W := by
    intro k hk'
    have hkm := Finset.mem_range.1 hk'
    have h := congrArg (map ι) (tay_rfun_mul Λ (lamK Λ q (k + 1)) ((k + 2 : ℕ) * q))
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_C, map_X, map_wpF, map_wpR] at h
    exact exists_factor_eq hℓ2 h2 h3 hε hODE ht (hlam (k + 1) (by omega) (by omega))
      (hwp (k + 2) (by omega) (by omega)) (hwp' (k + 2) (by omega) (by omega)) h
  choose! W hWi hW using hfac
  set g := (map ι (tay (GqRes Λ q))).subst z
  have hgM : g ^ (m + 2) = C ε ^ 2 * lam' ^ 2 * (rhoLT ℓ (ι Λ.g₂) (ι Λ.g₃) ε - C (ι (℘[Λ] q)) * X ^ 2) *
      ∏ k ∈ Finset.range m, (C ε * lam' * W k) := by
    have e := congrArg (fun f => (map ι f).subst z) htay
    simp only [map_pow, map_mul, map_prod, map_sub, map_C, map_X, map_wpF] at e
    rw [subst_pow hzs, subst_mul hzs, subst_wpF_sub hε0, ← coe_substAlgHom hzs, map_prod,
      coe_substAlgHom hzs] at e
    rw [e, Finset.prod_congr rfl fun k hk => hW k hk]
  set U := lam'⁻¹ * g
  have hlam0 : constantCoeff lam' = 1 := constantCoeff_logLTDivX ℓ
  have hlaml : lam' * lam'⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hlam0]; exact one_ne_zero)
  have hlamne : lam' ≠ 0 := fun h => by
    have := congrArg constantCoeff h
    rw [hlam0, map_zero] at this
    exact one_ne_zero this
  have hUM : U ^ (m + 2) = C ε ^ 2 * (rhoLT ℓ (ι Λ.g₂) (ι Λ.g₃) ε - C (ι (℘[Λ] q)) * X ^ 2) *
      ∏ k ∈ Finset.range m, (C ε * W k) := by
    refine mul_right_cancel₀ (pow_ne_zero (m + 2) hlamne) ?_
    calc U ^ (m + 2) * lam' ^ (m + 2) = g ^ (m + 2) * (lam' * lam'⁻¹) ^ (m + 2) := by simp only [U]; ring
      _ = _ := by
        rw [hlaml, one_pow, mul_one, hgM]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        ring
  have hg0 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hzs, finsum_eq_single _ 0]
    · simp [coeff_tay, (analyticAt_GqRes Λ hq).2]
    · intro d hd
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, hz0, zero_pow hd, smul_zero]
  have hU0 : constantCoeff U = 1 := by
    rw [map_mul, hg0, mul_one, PowerSeries.constantCoeff_inv, hlam0, inv_one]
  refine ⟨?_, hU0⟩
  have hρi := isInt_rhoLT hℓ2 h2 h3 hε hODE ht
  have hWi' : IsInt (C ε ^ 2 * (rhoLT ℓ (ι Λ.g₂) (ι Λ.g₃) ε - C (ι (℘[Λ] q)) * X ^ 2) *
      ∏ k ∈ Finset.range m, (C ε * W k)) :=
    (((isInt_C hε.le).pow 2).mul (hρi.sub ((isInt_C hq1).mul (isInt_X_pow 2)))).mul
      (Finset.prod_induction _ (fun f => IsInt f) (fun _ _ ha hb => ha.mul hb)
        (by rw [← map_one (C (R := ℂ_[ℓ]))]; exact isInt_C (by simp)) fun k hk => (isInt_C hε.le).mul (hWi k hk))
  exact (isIntK_of_pow_eq hMn hWi'.isIntK (by change ‖constantCoeff U‖ = 1; rw [hU0, norm_one])
    (by exact hUM)).isInt

end Translate

end

end TorsTransl
