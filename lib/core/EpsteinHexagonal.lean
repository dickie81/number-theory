/-
# The Epstein zeta function of the hexagonal lattice is the Dedekind zeta function of `ℚ(√−3)`

Plain statement. The hexagonal lattice is `ℤ²` with the norm form `Q(x, y) = x² + xy + y²` of `ℤ[ω]`:
`Q(x, y) = N(x − yω)` (`absNorm_ι`).
* **The points on each circle** (`rQ_eq`): `r_Q(n) = #{v ∈ ℤ² : Q(v) = n} = 6Σ_{d ∣ n} χ₋₃(d)` for `n ≥ 1`. `ℤ[ω]` is
  a principal ideal domain whose units are its elements of norm `1` (`mem_elts_one`), six of them (`rQ_one`), so each
  ideal of norm `n` has six generators (`card_elts`), and the ideals of norm `n` are counted by `Eis.rA_eq`.
* **The Dirichlet series** (`lseries_rQ`): `Σ_{n ≥ 1} r_Q(n)n^{−s} = 6ζ(s)L(s, χ₋₃)` on `Re s > 1`, with the library's
  `PsiOmega.chi3` (`1 ↦ 1`, `2 ↦ −1`), which is `Eis.chiInt` (`Eis.chiInt_eq`).
* **The theta function** `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−2πtQ(v)/√3}` (`thetaQ`, `hasSum_thetaQ`) is self-dual:
  `θ_Q(1/t) = tθ_Q(t)` (`thetaQ_inv`). With `u = 2x + y`, `4Q = u² + 3y²`; splitting `ℤ²` by the parities of `u` and
  `y` writes `θ_Q` through Jacobi's `θ = evenKernel 0` (`hasSum_Θ`), and `θ(1/x) = √x θ(x)` gives the functional
  equation.
* **The Epstein zeta function** `Λ_Q(s)`, the regularised Mellin transform of `θ_Q` (`LambdaQ`, Mathlib's
  `WeakFEPair.Λ`): `Λ_Q(1 − s) = Λ_Q(s)` (`LambdaQ_one_sub`), it is holomorphic off `s = 0, 1`
  (`differentiableAt_LambdaQ`), and `Λ_Q(s) = 6(2π/√3)^{−s}Γ(s)ζ(s)L(s, χ₋₃)` on `Re s > 1`
  (`LambdaQ_eq_of_one_lt_re`). By the identity theorem `Λ_Q(s) = 3·√3^s ζ̂(s)Λ(s, χ₋₃)` off `s = 0, 1` (`LambdaQ_eq`):
  three times the completed Dedekind zeta function `|d|^{s/2}Γ_ℂ(s)ζ(s)L(s, χ₋₃)` of `ℚ(√−3)`.
* **The Riemann hypothesis for the hexagonal lattice**, that the zeros of `Λ_Q` with `0 < Re s < 1` have `Re s = 1/2`,
  is RH for `ζ` and GRH for `χ₋₃` (`rh_hex_iff`), and so it is Weil's twin criterion for `ζ_{ℚ(√−3)}`
  (`rh_hex_iff_twins`, from `WeilTwinGeneral.rh_grh_iff_twins_Q3`).
This is the hexagonal companion of `TwoVariableZetaTwo`, where the square lattice `ℤ[i]` gives `ζ_{ℚ(i)}`.
-/
import Mathlib
import EisensteinIdealCount
import EisensteinCubicChar
import WeilTwinGeneral

open NumberField Ideal Finset

noncomputable section

namespace EpsteinHexagonal

open Eis

/-! ## The points of the hexagonal lattice on each circle -/

/-- The norm form of the hexagonal lattice, `Q(x, y) = x² + xy + y²`. -/
def qf (v : ℤ × ℤ) : ℤ := v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2

lemma qf_nonneg (v : ℤ × ℤ) : 0 ≤ qf v := by
  unfold qf
  nlinarith [sq_nonneg (2 * v.1 + v.2), sq_nonneg v.2]

lemma le_of_three_sq_le {x : ℤ} {n : ℕ} (h : 3 * x ^ 2 ≤ 4 * n) : -(n : ℤ) ≤ x ∧ x ≤ n := by
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  constructor
  · by_contra hx
    rw [not_le] at hx
    nlinarith [mul_le_mul_of_nonneg_left (show (n : ℤ) + 1 ≤ -x by linarith) (show (0 : ℤ) ≤ -x by linarith)]
  · by_contra hx
    rw [not_le] at hx
    nlinarith [mul_le_mul_of_nonneg_left (show (n : ℤ) + 1 ≤ x by linarith) (show (0 : ℤ) ≤ x by linarith)]

/-- The points of `ℤ²` on the circle `Q(v) = n`. -/
def shell (n : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun v => qf v = n

lemma mem_shell {n : ℕ} {v : ℤ × ℤ} : v ∈ shell n ↔ qf v = n := by
  unfold shell
  simp only [mem_filter, mem_product, mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · refine le_of_three_sq_le ?_
    unfold qf at h
    nlinarith [sq_nonneg (2 * v.2 + v.1)]
  · refine le_of_three_sq_le ?_
    unfold qf at h
    nlinarith [sq_nonneg (2 * v.1 + v.2)]

/-- **`r_Q(n)`**: the points of the hexagonal lattice `ℤ²` with `x² + xy + y² = n`. -/
def rQ (n : ℕ) : ℕ := (shell n).card

lemma rQ_one : rQ 1 = 6 := by decide

/-! ## Elements of `ℤ[ω]` of each norm -/

/-- `ι(x, y) = x − yω ∈ ℤ[ω]`, so that `N(ι v) = Q(v)`. -/
def ι (v : ℤ × ℤ) : 𝓞 K := (v.1 : 𝓞 K) + ((-v.2 : ℤ) : 𝓞 K) * ω

lemma ι_injective : Function.Injective ι := by
  intro v w h
  set a := v.1 - w.1
  set b := -v.2 - -w.2
  have hab : ((a : ℤ) : 𝓞 K) + (b : 𝓞 K) * ω = 0 := by
    rw [← sub_eq_zero.2 h]; simp only [ι, a, b]; push_cast; ring
  have hN := mul_cj_coords a b
  rw [hab, zero_mul] at hN
  have hz : a ^ 2 - a * b + b ^ 2 = 0 := by exact_mod_cast hN.symm
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  have hb : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 hb2
  have ha2 : a ^ 2 = 0 := by rw [hb] at hz; linarith
  have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.1 ha2
  have e1 : v.1 - w.1 = 0 := ha
  have e2 : -v.2 - -w.2 = 0 := hb
  exact Prod.ext (by omega) (by omega)

lemma ι_surjective : Function.Surjective ι := by
  intro x
  obtain ⟨m, n, rfl⟩ := exists_coords x
  exact ⟨(m, -n), by simp [ι]⟩

/-- `N(ι(x, y)) = x² + xy + y²`. -/
lemma absNorm_ι (v : ℤ × ℤ) : ((absNorm (span {ι v}) : ℕ) : ℤ) = qf v := by
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v.1 ^ 2 - v.1 * -v.2 + (-v.2) ^ 2 by
    nlinarith [sq_nonneg (2 * v.1 + v.2), sq_nonneg v.2])
  have h1 : absNorm (span {ι v}) ^ 2 = c ^ 2 := by
    rw [← absNorm_natCast_span_sq c, ← Int.cast_natCast, ← hc, ← mul_cj_coords,
      ← span_singleton_mul_span_singleton, map_mul, absNorm_span_cj, sq]
    rfl
  rw [Nat.pow_left_injective two_ne_zero h1, ← hc, qf]
  ring

/-- The elements of `ℤ[ω]` of norm `n`. -/
def elts (n : ℕ) : Finset (𝓞 K) := (shell n).map ⟨ι, ι_injective⟩

lemma mem_elts {n : ℕ} {β : 𝓞 K} : β ∈ elts n ↔ absNorm (span {β}) = n := by
  simp only [elts, mem_map, Function.Embedding.coeFn_mk, mem_shell]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := absNorm_ι v
    rw [hv] at this
    exact_mod_cast this
  · intro h
    obtain ⟨v, rfl⟩ := ι_surjective β
    exact ⟨v, by rw [← absNorm_ι, h], rfl⟩

lemma mem_elts_one {u : 𝓞 K} : u ∈ elts 1 ↔ IsUnit u := by
  rw [mem_elts, absNorm_eq_one_iff, span_singleton_eq_top]

/-- The generators of the principal ideal `(α₀)` are the `uα₀` with `u` a unit, i.e. of norm `1`. -/
lemma span_eq_iff {α₀ β : 𝓞 K} : span {β} = span {α₀} ↔ ∃ u ∈ elts 1, u * α₀ = β := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := span_singleton_eq_span_singleton.1 h
    exact ⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K), mem_elts_one.2 (Units.isUnit _), by
      rw [← hw, mul_comm β, ← mul_assoc, Units.inv_mul, one_mul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact span_singleton_mul_left_unit (mem_elts_one.1 hu) α₀

/-- **Six elements per ideal**: `#{β : N(β) = n} = 6·#{𝔞 : N𝔞 = n}` for `n ≥ 1`. -/
lemma card_elts {n : ℕ} (hn : n ≠ 0) : (elts n).card = 6 * (ofNorm n).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun β => span {β}) (t := ofNorm n) fun β hβ =>
    mem_ofNorm.2 (mem_elts.1 hβ), mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun I hI => ?_
  obtain ⟨α₀, rfl⟩ : ∃ α₀, I = span {α₀} := ⟨_, (span_singleton_generator I).symm⟩
  have hα₀ : α₀ ≠ 0 := by
    rintro rfl
    apply hn
    rw [← mem_ofNorm.1 hI]
    simp
  have hfib : (elts n).filter (fun β => span {β} = span {α₀}) =
      (elts 1).map ⟨(· * α₀), mul_left_injective₀ hα₀⟩ := by
    ext β
    rw [mem_filter, mem_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [← span_eq_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_elts.2 (h ▸ mem_ofNorm.1 hI), h⟩⟩
  rw [hfib, card_map, elts, card_map]
  exact rQ_one

/-- **The points of the hexagonal lattice on each circle**: `r_Q(n) = 6Σ_{d ∣ n} χ₋₃(d)` for `n ≥ 1`. -/
theorem rQ_eq {n : ℕ} (hn : n ≠ 0) : (rQ n : ℤ) = 6 * ∑ d ∈ n.divisors, chiInt d := by
  have h1 : rQ n = (elts n).card := (card_map _).symm
  have h2 : rA n = (ofNorm n).card := rA_apply hn
  have h3 : rA n = ∑ d ∈ n.divisors, chiInt d := by
    rw [rA_eq, ArithmeticFunction.coe_mul_zeta_apply]
    simp only [chiA_apply]
  rw [h1, card_elts hn, Nat.cast_mul, ← h2, h3]
  norm_num

lemma rQ_zero : rQ 0 = 1 := by decide

/-! ## The Dirichlet series `Σ r_Q(n)n^{−s} = 6ζ(s)L(s, χ₋₃)` -/

section Dirichlet

open scoped LSeries.notation

lemma rQ_eq_convolution {n : ℕ} (hn : n ≠ 0) :
    (rQ n : ℂ) = ((6 : ℂ) • (↗PsiOmega.chi3 ⍟ (1 : ℕ → ℂ))) n := by
  rw [Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => PsiOmega.chi3 a)]
  have h := congrArg (Int.cast : ℤ → ℂ) (rQ_eq hn)
  push_cast at h
  rw [h]
  simp [PsiOmega.chi3_nat, chiInt_eq]

lemma summable_rQ {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n ↦ (rQ n : ℂ)) s := by
  have hc := (DirichletCharacter.LSeriesSummable_of_one_lt_re PsiOmega.chi3 hs).convolution
    (LSeriesSummable_one_iff.mpr hs)
  exact (LSeriesSummable_congr s fun hn ↦ rQ_eq_convolution hn).2 (hc.smul 6)

/-- **The Dirichlet series of `r_Q`**: `Σ_{n ≥ 1} r_Q(n)n^{−s} = 6ζ(s)L(s, χ₋₃)` on `Re s > 1`. -/
theorem lseries_rQ {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (rQ n : ℂ)) s =
      6 * (riemannZeta s * DirichletCharacter.LFunction PsiOmega.chi3 s) := by
  have hχ := DirichletCharacter.LSeriesSummable_of_one_lt_re PsiOmega.chi3 hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  rw [LSeries_congr (fun hn ↦ rQ_eq_convolution hn) s, LSeries_smul, LSeries_convolution' hχ h1,
    DirichletCharacter.LFunction_eq_LSeries PsiOmega.chi3 hs, LSeries_one_eq_riemannZeta hs,
    mul_comm (riemannZeta s)]

end Dirichlet

/-! ## The theta function -/

section Theta

open Real Complex HurwitzZeta Filter Topology Asymptotics

/-- `θ(a)θ(b) = Σ_{(m, n) ∈ ℤ²} e^{−π(m²a + n²b)}`, for Jacobi's `θ = evenKernel 0`. -/
lemma hasSum_prod {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun p : ℤ × ℤ => rexp (-π * (p.1 : ℝ) ^ 2 * a) * rexp (-π * (p.2 : ℝ) ^ 2 * b))
      (evenKernel 0 a * evenKernel 0 b) := by
  have h1 : HasSum (fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * a)) (evenKernel 0 a) := by
    simpa using hasSum_int_evenKernel 0 ha
  have h2 : HasSum (fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * b)) (evenKernel 0 b) := by
    simpa using hasSum_int_evenKernel 0 hb
  exact h1.mul h2 (h1.summable.mul_of_nonneg h2.summable (fun _ => (Real.exp_pos _).le)
    fun _ => (Real.exp_pos _).le)

/-- A sum over the image of an injection `g`, written as a sum over the whole lattice. -/
lemma hasSum_ite {P : ℤ × ℤ → Prop} [DecidablePred P] {f : ℤ × ℤ → ℝ} {c : ℝ} (g : ℤ × ℤ → ℤ × ℤ)
    (hg : Function.Injective g) (hP : ∀ p, P p → ∃ q, g q = p) (hPg : ∀ q, P (g q))
    (h : HasSum (f ∘ g) c) : HasSum (fun p => if P p then f p else 0) c := by
  refine (hg.hasSum_iff fun p hp => ite_eq_right fun h' => hp (hP p h')).1 ?_
  convert h using 1
  funext q
  simp [hPg q]

/-- **The theta function of the hexagonal lattice**: `Θ(τ) = Σ_{v ∈ ℤ²} e^{−πτQ(v)}`. -/
def Θ (τ : ℝ) : ℝ := ∑' v : ℤ × ℤ, rexp (-π * (qf v : ℝ) * τ)

/-- **`Θ` through Jacobi's theta function**: `Θ(τ) = 2θ(τ)θ(3τ) + θ(τ/4)θ(3τ/4) − θ(τ)θ(3τ/4) − θ(τ/4)θ(3τ)`.
With `u = 2x + y`, `4Q(x, y) = u² + 3y²`, and `(x, y) ↦ (u, y)` is a bijection of `ℤ²` onto the `(u, y)` with
`u ≡ y mod 2`, whose indicator is `1 − [2 ∣ u] − [2 ∣ y] + 2[2 ∣ u][2 ∣ y]`. -/
lemma hasSum_Θ {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun v : ℤ × ℤ => rexp (-π * (qf v : ℝ) * τ))
      (2 * (evenKernel 0 τ * evenKernel 0 (3 * τ)) + evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ / 4) -
        evenKernel 0 τ * evenKernel 0 (3 * τ / 4) - evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ)) := by
  set F : ℤ × ℤ → ℝ := fun p => rexp (-π * (p.1 : ℝ) ^ 2 * (τ / 4)) * rexp (-π * (p.2 : ℝ) ^ 2 * (3 * τ / 4))
    with hF
  have h4 : 0 < τ / 4 := by positivity
  have h34 : 0 < 3 * τ / 4 := by positivity
  have h3 : 0 < 3 * τ := by positivity
  have hall : HasSum F _ := hasSum_prod h4 h34
  have hu : HasSum (fun p : ℤ × ℤ => if p.1 % 2 = 0 then F p else 0)
      (evenKernel 0 τ * evenKernel 0 (3 * τ / 4)) := by
    refine hasSum_ite (fun q => (2 * q.1, q.2)) (fun q q' h => ?_) (fun p hp => ⟨(p.1 / 2, p.2), ?_⟩)
      (fun q => show 2 * q.1 % 2 = 0 by omega) ((hasSum_prod hτ h34).congr_fun fun q => ?_)
    · simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) h.2
    · exact Prod.ext (show 2 * (p.1 / 2) = p.1 by omega) rfl
    · simp only [hF, Function.comp_apply]
      push_cast
      ring_nf
  have hy : HasSum (fun p : ℤ × ℤ => if p.2 % 2 = 0 then F p else 0)
      (evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ)) := by
    refine hasSum_ite (fun q => (q.1, 2 * q.2)) (fun q q' h => ?_) (fun p hp => ⟨(p.1, p.2 / 2), ?_⟩)
      (fun q => show 2 * q.2 % 2 = 0 by omega) ((hasSum_prod h4 h3).congr_fun fun q => ?_)
    · simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (by omega)
    · exact Prod.ext rfl (show 2 * (p.2 / 2) = p.2 by omega)
    · simp only [hF, Function.comp_apply]
      push_cast
      ring_nf
  have huy : HasSum (fun p : ℤ × ℤ => if p.1 % 2 = 0 ∧ p.2 % 2 = 0 then F p else 0)
      (evenKernel 0 τ * evenKernel 0 (3 * τ)) := by
    refine hasSum_ite (fun q => (2 * q.1, 2 * q.2)) (fun q q' h => ?_)
      (fun p hp => ⟨(p.1 / 2, p.2 / 2), ?_⟩) (fun q => ⟨show 2 * q.1 % 2 = 0 by omega, show 2 * q.2 % 2 = 0 by omega⟩)
      ((hasSum_prod hτ h3).congr_fun fun q => ?_)
    · simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · exact Prod.ext (show 2 * (p.1 / 2) = p.1 by omega) (show 2 * (p.2 / 2) = p.2 by omega)
    · simp only [hF, Function.comp_apply]
      push_cast
      ring_nf
  have hsame : HasSum (fun p : ℤ × ℤ => if p.1 % 2 = p.2 % 2 then F p else 0)
      (evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ / 4) - evenKernel 0 τ * evenKernel 0 (3 * τ / 4) -
        evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ) + 2 * (evenKernel 0 τ * evenKernel 0 (3 * τ))) := by
    refine (((hall.sub hu).sub hy).add (huy.mul_left 2)).congr_fun fun p => ?_
    rcases Int.emod_two_eq_zero_or_one p.1 with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one p.2 with h2 | h2 <;> simp [h1, h2]
    ring
  have hg : Function.Injective fun v : ℤ × ℤ => (2 * v.1 + v.2, v.2) := fun v w h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.2
  have h := (hg.hasSum_iff fun p hp => ite_eq_right fun h' => hp ⟨((p.1 - p.2) / 2, p.2),
    Prod.ext (show 2 * ((p.1 - p.2) / 2) + p.2 = p.1 by omega) rfl⟩).2 hsame
  convert h.congr_fun fun v => ?_ using 1
  · ring
  · simp only [Function.comp_apply, show (2 * v.1 + v.2) % 2 = v.2 % 2 by omega, ite_true, hF, qf,
      ← Real.exp_add]
    push_cast
    ring_nf

lemma Θ_eq {τ : ℝ} (hτ : 0 < τ) :
    Θ τ = 2 * (evenKernel 0 τ * evenKernel 0 (3 * τ)) + evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ / 4) -
      evenKernel 0 τ * evenKernel 0 (3 * τ / 4) - evenKernel 0 (τ / 4) * evenKernel 0 (3 * τ) :=
  (hasSum_Θ hτ).tsum_eq

/-- **`Θ(τ) = Σ_{n ≥ 0} r_Q(n)e^{−πnτ}`**: group the lattice sum by the circles `Q(v) = n`. -/
lemma hasSum_Θ_nat {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun n : ℕ => (rQ n : ℝ) * rexp (-π * n * τ)) (Θ τ) := by
  have hv : HasSum (fun v : ℤ × ℤ => rexp (-π * (qf v : ℝ) * τ)) (Θ τ) := (hasSum_Θ hτ).summable.hasSum
  let N : ℤ × ℤ → ℕ := fun v => (qf v).toNat
  have hN : ∀ v, ((N v : ℕ) : ℤ) = qf v := fun v => Int.toNat_of_nonneg (qf_nonneg v)
  have hv' : HasSum (fun v : ℤ × ℤ => rexp (-π * (N v : ℝ) * τ)) (Θ τ) :=
    hv.congr_fun fun v => by rw [← Int.cast_natCast, hN v]
  convert hv'.tsum_fiberwise N using 1
  funext n
  have hset : N ⁻¹' {n} = ↑(shell n) := by
    ext v
    rw [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_shell, ← hN v, Nat.cast_inj]
  rw [tsum_congr fun p : ↑(N ⁻¹' {n}) => show rexp (-π * (N p : ℝ) * τ) = rexp (-π * n * τ) by
    rw [show N p = n from p.2], hset, tsum_const, Nat.card_coe_set_eq, Set.ncard_coe_finset, nsmul_eq_mul]
  rfl

/-- Jacobi's transformation `θ(1/x) = √x θ(x)`. -/
lemma theta_inv {x : ℝ} (hx : 0 < x) : evenKernel 0 (1 / x) = Real.sqrt x * evenKernel 0 x := by
  have h := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h, ← mul_assoc, Real.sqrt_eq_rpow, mul_one_div_cancel (Real.rpow_pos_of_pos hx _).ne', one_mul]

/-- **The functional equation of `Θ`**: `Θ(1/τ) = (2τ/√3)Θ(4τ/3)`. -/
lemma Θ_inv {τ : ℝ} (hτ : 0 < τ) : Θ (1 / τ) = 2 * τ / Real.sqrt 3 * Θ (4 * τ / 3) := by
  rw [Θ_eq (by positivity), Θ_eq (by positivity)]
  have e1 : 3 * (1 / τ) / 4 = 1 / (4 * τ / 3) := by field_simp
  have e2 : 3 * (1 / τ) = 1 / (τ / 3) := by field_simp
  have e3 : 1 / τ / 4 = 1 / (4 * τ) := by field_simp
  have e4 : 3 * (4 * τ / 3) / 4 = τ := by field_simp
  have e5 : 3 * (4 * τ / 3) = 4 * τ := by field_simp
  have e6 : 4 * τ / 3 / 4 = τ / 3 := by field_simp
  have s1 : Real.sqrt (τ / 3) = Real.sqrt τ / Real.sqrt 3 := Real.sqrt_div' τ (by norm_num)
  have s2 : Real.sqrt (4 * τ) = 2 * Real.sqrt τ := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s3 : Real.sqrt (4 * τ / 3) = 2 * Real.sqrt τ / Real.sqrt 3 := by
    rw [Real.sqrt_div' _ (by norm_num), s2]
  rw [e1, e2, e3, e4, e5, e6, theta_inv hτ, theta_inv (by positivity : 0 < τ / 3),
    theta_inv (by positivity : 0 < 4 * τ), theta_inv (by positivity : 0 < 4 * τ / 3), s1, s2, s3]
  have hτ' : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  linear_combination ((2 * evenKernel 0 τ * evenKernel 0 (τ / 3) + 4 * evenKernel 0 (4 * τ) *
    evenKernel 0 (4 * τ / 3) - 2 * evenKernel 0 τ * evenKernel 0 (4 * τ / 3) - 2 * evenKernel 0 (4 * τ) *
    evenKernel 0 (τ / 3)) / Real.sqrt 3) * hτ'

/-- **The theta function of the hexagonal lattice**, `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−2πtQ(v)/√3} = Θ(2t/√3)`. -/
def thetaQ (t : ℝ) : ℝ := Θ (2 * t / Real.sqrt 3)

/-- `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−2πtQ(v)/√3}`. -/
theorem hasSum_thetaQ {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : ℤ × ℤ => rexp (-2 * π * t * (qf v : ℝ) / Real.sqrt 3)) (thetaQ t) :=
  (hasSum_Θ (by positivity : 0 < 2 * t / Real.sqrt 3)).summable.hasSum.congr_fun fun v => by
    congr 1
    ring

/-- **`θ_Q(1/t) = tθ_Q(t)`**: the hexagonal lattice is similar to its dual, and `θ_Q` is normalised so that it is
self-dual. -/
theorem thetaQ_inv {t : ℝ} (ht : 0 < t) : thetaQ (1 / t) = t * thetaQ t := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e1 : 2 * (1 / t) / Real.sqrt 3 = 1 / (Real.sqrt 3 * t / 2) := by field_simp
  have e2 : 2 * (Real.sqrt 3 * t / 2) / Real.sqrt 3 = t := by field_simp
  have e3 : 4 * (Real.sqrt 3 * t / 2) / 3 = 2 * t / Real.sqrt 3 := by
    field_simp
    linear_combination 4 * hs
  unfold thetaQ
  rw [e1, Θ_inv (by positivity), e2, e3]

/-- `0 ≤ Θ(τ) − 1 ≤ (Θ(1) − 1)e^{−π(τ − 1)}` for `τ ≥ 1`: every `v ≠ 0` has `Q(v) ≥ 1`. -/
lemma Θ_sub_one_le {τ : ℝ} (hτ : 1 ≤ τ) : 0 ≤ Θ τ - 1 ∧ Θ τ - 1 ≤ (Θ 1 - 1) * rexp (-π * (τ - 1)) := by
  have h1 := (hasSum_nat_add_iff' 1).2 (hasSum_Θ_nat (by linarith : (0 : ℝ) < τ))
  have h2 := (hasSum_nat_add_iff' 1).2 (hasSum_Θ_nat one_pos)
  simp only [Finset.sum_range_one, rQ_zero, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, Real.exp_zero,
    mul_one] at h1 h2
  refine ⟨h1.nonneg fun n => by positivity, ?_⟩
  rw [mul_comm]
  refine hasSum_le (fun n => ?_) h1 (h2.mul_left (rexp (-π * (τ - 1))))
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [← Real.exp_add, Real.exp_le_exp]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_nonneg.2 hτ)]

/-- `θ_Q(t) − 1` decays like `e^{−2πt/√3}`, so faster than any power of `t`. -/
lemma isBigO_thetaQ_sub (r : ℝ) : (fun t => (thetaQ t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have hκ : 0 < 2 * π / Real.sqrt 3 := by positivity
  have hO : (fun t => thetaQ t - 1) =O[atTop] fun t => rexp (-(2 * π / Real.sqrt 3) * t) := by
    refine IsBigO.of_bound ((Θ 1 - 1) * rexp π) ?_
    filter_upwards [eventually_ge_atTop (Real.sqrt 3 / 2)] with t ht
    have hτ : 1 ≤ 2 * t / Real.sqrt 3 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨h0, h1⟩ : 0 ≤ thetaQ t - 1 ∧ thetaQ t - 1 ≤ (Θ 1 - 1) * rexp (-π * (2 * t / Real.sqrt 3 - 1)) :=
      Θ_sub_one_le hτ
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc, ← Real.exp_add]
    convert h1 using 3
    ring
  refine (isBigO_ofReal_left.mpr (hO.trans (isLittleO_exp_neg_mul_rpow_atTop hκ r).isBigO)).congr_left
    fun t => ?_
  simp

lemma continuousOn_Θ : ContinuousOn Θ (Set.Ioi 0) := by
  have hE : ∀ g : ℝ → ℝ, Continuous g → (∀ τ, 0 < τ → 0 < g τ) →
      ContinuousOn (fun τ => evenKernel 0 (g τ)) (Set.Ioi 0) := fun g hg hpos =>
    (continuousOn_evenKernel 0).comp hg.continuousOn fun τ hτ => hpos τ hτ
  have h1 := hE id continuous_id fun τ h => h
  have h2 := hE (fun τ => 3 * τ) (by fun_prop) fun τ h => by positivity
  have h3 := hE (fun τ => τ / 4) (by fun_prop) fun τ h => by positivity
  have h4 := hE (fun τ => 3 * τ / 4) (by fun_prop) fun τ h => by positivity
  exact ContinuousOn.congr ((((continuousOn_const.mul (h1.mul h2)).add (h3.mul h4)).sub (h1.mul h4)).sub
    (h3.mul h2)) fun τ hτ => Θ_eq hτ

lemma locallyIntegrableOn_thetaQ : MeasureTheory.LocallyIntegrableOn (fun t => (thetaQ t : ℂ)) (Set.Ioi 0) := by
  have h : ContinuousOn thetaQ (Set.Ioi 0) :=
    continuousOn_Θ.comp (by fun_prop : Continuous fun t : ℝ => 2 * t / Real.sqrt 3).continuousOn
      fun t (ht : 0 < t) => show 0 < 2 * t / Real.sqrt 3 by positivity
  exact (continuous_ofReal.comp_continuousOn h).locallyIntegrableOn measurableSet_Ioi

/-- **`θ_Q` is a weak FE-pair** of weight `1` and root number `1`, its own dual, with constant term `1` at both
ends. -/
def thetaFEPair : WeakFEPair ℂ where
  f t := (thetaQ t : ℂ)
  g t := (thetaQ t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_thetaQ
  hg_int := locallyIntegrableOn_thetaQ
  hk := one_pos
  hε := one_ne_zero
  h_feq x hx := by
    show ((thetaQ (1 / x) : ℝ) : ℂ) = ((1 : ℂ) * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • ((thetaQ x : ℝ) : ℂ)
    rw [thetaQ_inv hx, Real.rpow_one, one_mul, smul_eq_mul, ofReal_mul]
  hf_top := isBigO_thetaQ_sub
  hg_top := isBigO_thetaQ_sub

lemma thetaFEPair_symm : thetaFEPair.symm = thetaFEPair := by
  unfold thetaFEPair WeakFEPair.symm
  congr 1
  exact inv_one

/-! ## The Epstein zeta function of the hexagonal lattice -/

/-- **The completed Epstein zeta function of the hexagonal lattice**, `Λ_Q(s) = ∫₀^∞ θ_Q(t)t^s dt/t` regularised:
Mathlib's `WeakFEPair.Λ` for `θ_Q`. -/
def LambdaQ (s : ℂ) : ℂ := thetaFEPair.Λ s

/-- **The functional equation** `Λ_Q(1 − s) = Λ_Q(s)`. -/
theorem LambdaQ_one_sub (s : ℂ) : LambdaQ (1 - s) = LambdaQ s := by
  have h := thetaFEPair.functional_equation s
  rw [thetaFEPair_symm] at h
  have hk : ((thetaFEPair.k : ℝ) : ℂ) = 1 := by simp [thetaFEPair]
  unfold LambdaQ
  rw [← hk, h]
  simp [thetaFEPair]

/-- `Λ_Q` is holomorphic away from its poles `s = 0` and `s = 1`. -/
theorem differentiableAt_LambdaQ {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : DifferentiableAt ℂ LambdaQ s :=
  thetaFEPair.differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [thetaFEPair] using h1))

/-- **On `Re s > 1`, `Λ_Q(s)` is the Mellin transform** `∫₀^∞ (θ_Q(t) − 1)t^s dt/t`. -/
theorem hasMellin_thetaQ {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (thetaQ t : ℂ) - 1) s (LambdaQ s) :=
  thetaFEPair.hasMellin (by simpa [thetaFEPair] using hs)

/-- **On `Re s > 1`, `Λ_Q(s) = 6(2π/√3)^{−s}Γ(s)ζ(s)L(s, χ₋₃)`**: term by term,
`Λ_Q(s) = (2π/√3)^{−s}Γ(s)Σ_{n ≥ 1} r_Q(n)n^{−s}`, and `lseries_rQ`. -/
theorem LambdaQ_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LambdaQ s = 6 * ((2 * π / Real.sqrt 3 : ℝ) : ℂ) ^ (-s) * Gamma s * riemannZeta s *
      DirichletCharacter.LFunction PsiOmega.chi3 s := by
  have hκ : 0 < 2 / Real.sqrt 3 := by positivity
  have hsum := summable_rQ hs
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun i : ℕ => if 2 / Real.sqrt 3 * (i : ℝ) = 0 then 0 else
      (rQ i : ℂ) * rexp (-π * (2 / Real.sqrt 3 * i) * t)) ((thetaQ t : ℂ) - 1) := by
    intro t (ht : 0 < t)
    have h := (hasSum_ofReal.2 (hasSum_Θ_nat (show 0 < 2 * t / Real.sqrt 3 by positivity))).update 0 0
    convert h using 1
    · funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      · rw [Function.update_of_ne hi, ite_eq_right (by positivity)]
        push_cast
        ring_nf
    · simp [thetaQ, rQ_zero]
      ring
  have h_sum : Summable fun i : ℕ => ‖(rQ i : ℂ)‖ / (2 / Real.sqrt 3 * i) ^ s.re := by
    refine (hsum.norm.mul_left ((2 / Real.sqrt 3) ^ s.re)⁻¹).congr fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hi, Real.mul_rpow hκ.le (Nat.cast_nonneg _)]
      ring
  have hD := hasSum_mellin_pi_mul₀ (a := fun i : ℕ => (rQ i : ℂ)) (p := fun i : ℕ => 2 / Real.sqrt 3 * (i : ℝ))
    (F := fun t => (thetaQ t : ℂ) - 1) (s := s) (fun i => by positivity) (by linarith) hF h_sum
  rw [(hasMellin_thetaQ hs).2] at hD
  have hT : (fun i : ℕ => (π : ℂ) ^ (-s) * Gamma s * (rQ i : ℂ) / ((2 / Real.sqrt 3 * i : ℝ) : ℂ) ^ s) =
      fun i => (π : ℂ) ^ (-s) * Gamma s * ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ (-s) *
        LSeries.term (fun n => (rQ n : ℂ)) s i := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; norm_num at hs
      simp [Complex.zero_cpow hs0]
    · rw [LSeries.term_of_ne_zero hi, ofReal_mul, mul_cpow_ofReal_nonneg hκ.le (Nat.cast_nonneg _),
        ofReal_natCast, cpow_neg ((2 / Real.sqrt 3 : ℝ) : ℂ) s]
      ring
  rw [hT] at hD
  have e := hD.unique (hsum.LSeriesHasSum.mul_left
    ((π : ℂ) ^ (-s) * Gamma s * ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ (-s)))
  rw [lseries_rQ hs] at e
  rw [e, show 2 * π / Real.sqrt 3 = π * (2 / Real.sqrt 3) by ring, ofReal_mul,
    mul_cpow_ofReal_nonneg Real.pi_pos.le hκ.le]
  ring

/-! ## The continuation -/

lemma odd_chi3 : PsiOmega.chi3.Odd := by
  have h : PsiOmega.χ₃ (-1 : ZMod 3) = -1 := by decide
  show PsiOmega.chi3 (-1) = -1
  simp [PsiOmega.chi3, MulChar.ringHomComp_apply, h]

lemma completedRiemannZeta_eq {z : ℂ} (hz : 0 < z.re) : completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  rw [riemannZeta_def_of_ne_zero hz0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)]

lemma completedLFunction_eq {z : ℂ} (hz : 0 < z.re) :
    DirichletCharacter.completedLFunction PsiOmega.chi3 z =
      Gammaℝ (z + 1) * DirichletCharacter.LFunction PsiOmega.chi3 z := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor PsiOmega.chi3 z (Or.inr (by norm_num))
  rw [odd_chi3.gammaFactor_def] at h
  rw [h, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))]

lemma LambdaQ_eq_completed_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LambdaQ s = 3 * ((Real.sqrt 3 : ℝ) : ℂ) ^ s * completedRiemannZeta s *
      DirichletCharacter.completedLFunction PsiOmega.chi3 s := by
  have h0 : 0 < s.re := by linarith
  have ha : 0 ≤ 2 * π / Real.sqrt 3 := by positivity
  have hb : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hB : ((Real.sqrt 3 : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.2 (by positivity))
  have hΓ : Gammaℝ s * Gammaℝ (s + 1) = 2 * ((2 * π : ℝ) : ℂ) ^ (-s) * Gamma s := by
    rw [Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def]
    push_cast
    ring
  have key : 2 * ((2 * π : ℝ) : ℂ) ^ (-s) * Gamma s * ((Real.sqrt 3 : ℝ) : ℂ) ^ s =
      2 * ((2 * π / Real.sqrt 3 : ℝ) : ℂ) ^ (-s) * Gamma s := by
    rw [show 2 * π = 2 * π / Real.sqrt 3 * Real.sqrt 3 by field_simp, ofReal_mul,
      mul_cpow_ofReal_nonneg ha hb, cpow_neg ((Real.sqrt 3 : ℝ) : ℂ) s]
    field_simp
  rw [LambdaQ_eq_of_one_lt_re hs, completedRiemannZeta_eq h0, completedLFunction_eq h0]
  linear_combination (-3 * ((Real.sqrt 3 : ℝ) : ℂ) ^ s * riemannZeta s *
    DirichletCharacter.LFunction PsiOmega.chi3 s) * hΓ +
    (-3 * riemannZeta s * DirichletCharacter.LFunction PsiOmega.chi3 s) * key

/-- **`Λ_Q(s) = 3·√3^s ζ̂(s)Λ(s, χ₋₃)` off `s = 0, 1`**, with Mathlib's completed functions `completedRiemannZeta`
and `DirichletCharacter.completedLFunction`: three times the completed Dedekind zeta function
`|d|^{s/2}Γ_ℂ(s)ζ(s)L(s, χ₋₃)` of `ℚ(√−3)`. Both sides are holomorphic off `s = 0, 1` and agree on `Re s > 1`. -/
theorem LambdaQ_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LambdaQ s = 3 * ((Real.sqrt 3 : ℝ) : ℂ) ^ s * completedRiemannZeta s *
      DirichletCharacter.completedLFunction PsiOmega.chi3 s := by
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
  have hfin : ({0, 1} : Set ℂ).Finite := by simp
  have hUo : IsOpen U := hfin.isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    (hfin.countable.isPathConnected_compl_of_one_lt_rank (by rw [rank_real_complex]; norm_num)).isConnected
      |>.isPreconnected
  have hf : DifferentiableOn ℂ LambdaQ U := by
    intro z hz
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact (differentiableAt_LambdaQ hz.1 hz.2).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => 3 * ((Real.sqrt 3 : ℝ) : ℂ) ^ z * completedRiemannZeta z *
      DirichletCharacter.completedLFunction PsiOmega.chi3 z) U := by
    intro z hz
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ((Real.sqrt 3 : ℝ) : ℂ) ^ z) z :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (by positivity)))
    have hζ : DifferentiableAt ℂ completedRiemannZeta z := differentiableAt_completedZeta hz.1 hz.2
    have hL : DifferentiableAt ℂ (DirichletCharacter.completedLFunction PsiOmega.chi3) z :=
      (DirichletCharacter.differentiable_completedLFunction PsiOmega.chi3_ne_one) z
    exact (((h3.const_mul 3).mul hζ).mul hL).differentiableWithinAt
  have heq : LambdaQ =ᶠ[𝓝 2] fun z => 3 * ((Real.sqrt 3 : ℝ) : ℂ) ^ z * completedRiemannZeta z *
      DirichletCharacter.completedLFunction PsiOmega.chi3 z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact LambdaQ_eq_completed_of_one_lt_re hz
  have h2 : (2 : ℂ) ∈ U := by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc h2 heq
    (by simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h0, h1⟩)

/-! ## The zeros and the Riemann hypothesis for the hexagonal lattice -/

/-- **In the strip `0 < Re s < 1`, `Λ_Q(s) = 0` exactly when `ζ(s) = 0` or `L(s, χ₋₃) = 0`.** -/
theorem LambdaQ_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    LambdaQ s = 0 ↔ riemannZeta s = 0 ∨ DirichletCharacter.LFunction PsiOmega.chi3 s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  rw [LambdaQ_eq hs0 hs1, completedRiemannZeta_eq h0, completedLFunction_eq h0]
  have hA : ((Real.sqrt 3 : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.2 (by positivity))
  have hB : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hC : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  simp [hA, hB, hC]

/-- **The Riemann hypothesis for the hexagonal lattice is RH for `ζ` and GRH for `χ₋₃`**: the zeros of `Λ_Q` in the
strip `0 < Re s < 1` are the zeros of `ζ` and of `L(s, χ₋₃)` there. -/
theorem rh_hex_iff :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → LambdaQ s = 0 → s.re = 1 / 2) ↔
      (RiemannHypothesis ∧ PsiOmega.GRH PsiOmega.chi3) := by
  constructor
  · intro h
    refine ⟨fun ρ hρ htriv _ => ?_, fun ρ hL h0 h1 => h ρ h0 h1 ((LambdaQ_eq_zero_iff h0 h1).2 (Or.inr hL))⟩
    have hnt : WeilTest.IsNontrivialZero ρ := ⟨hρ, htriv⟩
    exact h ρ hnt.re_pos hnt.re_lt_one ((LambdaQ_eq_zero_iff hnt.re_pos hnt.re_lt_one).2 (Or.inl hρ))
  · rintro ⟨hRH, hG⟩ s h0 h1 hz
    rcases (LambdaQ_eq_zero_iff h0 h1).1 hz with h | h
    · have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, rfl⟩
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        simp at h0
        linarith
      exact hRH s h htriv fun e => by rw [e, Complex.one_re] at h1; exact lt_irrefl 1 h1
    · exact hG s h h0 h1

/-- **…and so it is Weil's twin criterion for `ζ_{ℚ(√−3)}`** (`WeilTwinGeneral.rh_grh_iff_twins_Q3`): RH for the
hexagonal lattice holds exactly when the twin form of `ζ(s)L(s, χ₋₃)` is nonnegative on the twin boxes. -/
theorem rh_hex_iff_twins :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → LambdaQ s = 0 → s.re = 1 / 2) ↔
      ∀ l : ℝ, 0 ≤ l → 0 ≤ 2 * WeilForm.weilQ (l + 1) (WeilForm.twin (WeilForm.box 1) l) +
        PsiOmega.QC PsiOmega.chi3 (l + 1) (WeilForm.twin (WeilForm.box 1) l) :=
  rh_hex_iff.trans WeilTwinGeneral.rh_grh_iff_twins_Q3

end Theta

end EpsteinHexagonal

#print axioms EpsteinHexagonal.rQ_eq
#print axioms EpsteinHexagonal.lseries_rQ
#print axioms EpsteinHexagonal.hasSum_thetaQ
#print axioms EpsteinHexagonal.thetaQ_inv
#print axioms EpsteinHexagonal.LambdaQ_one_sub
#print axioms EpsteinHexagonal.differentiableAt_LambdaQ
#print axioms EpsteinHexagonal.LambdaQ_eq_of_one_lt_re
#print axioms EpsteinHexagonal.LambdaQ_eq
#print axioms EpsteinHexagonal.LambdaQ_eq_zero_iff
#print axioms EpsteinHexagonal.rh_hex_iff
#print axioms EpsteinHexagonal.rh_hex_iff_twins
