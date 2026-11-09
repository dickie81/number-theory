/-
# The Epstein zeta function of `x² + 2y²` is the Dedekind zeta function of `ℚ(√−2)`

Plain statement. `Q(x, y) = x² + 2y²` is the norm form of `ℤ[√−2]`, the ring of integers of `K = ℚ(√−2)`, here
Mathlib's quadratic algebra `ℚ[ω]` with `ω² = −2` (`K`): `N(x + y√−2) = Q(x, y)` (`algNorm_ι`).
* **The ring of integers is `ℤ[√−2]`** (`ι_surjective`): for an integral `z = r + s√−2`, the norms of `z` and `z + 1`
  are integers, so `2r` and `(4s)² = 8N(z) − 2(2r)²` are, and parity forces `r, s ∈ ℤ`. It is a principal ideal
  domain (`isPrincipalIdealRing`) by Euclid's algorithm: every `z ∈ K` is within norm `3/4` of `ℤ[√−2]`
  (`exists_norm_sub_lt`).
* **The splitting law**: `2𝓞 = (√−2)²` (`ramified_two`); an odd `p ≡ 1, 3 (mod 8)` splits, since `−2` is a square
  mod `p` and `p ∣ a² + 2 = (a + √−2)(a − √−2)` (`split`); and `p ≡ 5, 7 (mod 8)` is inert, since `p = x² + 2y²` would
  make `−2` a square mod `p` (`isSquare_of_qf`, `inert`). So `QuadIdeals.rA_eq` counts the ideals of norm `n` by
  `Σ_{d ∣ n} χ₋₈(d)` (`rA_eq`), with Mathlib's `ZMod.χ₈'` (`1` on `1, 3` and `−1` on `5, 7` mod `8`).
* **The points on each ellipse** (`rQ_eq`): `r_Q(n) = #{v ∈ ℤ² : Q(v) = n} = 2Σ_{d ∣ n} χ₋₈(d)` for `n ≥ 1`: the
  units of `ℤ[√−2]` are `±1` (`rQ_one`), so each ideal of norm `n` has two generators (`card_elts`).
* **The Dirichlet series** (`lseries_rQ`): `Σ_{n ≥ 1} r_Q(n)n^{−s} = 2ζ(s)L(s, χ₋₈)` on `Re s > 1`, with the
  library's `PsiOmega.chi8`.
* **The theta function** `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−πtQ(v)/√2} = θ(t/√2)θ(√2t)` (`thetaQ`, `hasSum_thetaQ`), for
  Jacobi's `θ = evenKernel 0`, is self-dual: `θ_Q(1/t) = tθ_Q(t)` (`thetaQ_inv`), from `θ(1/x) = √x θ(x)`.
* **The Epstein zeta function** `Λ_Q(s)`, the regularised Mellin transform of `θ_Q` (`LambdaQ`, Mathlib's
  `WeakFEPair.Λ`): `Λ_Q(1 − s) = Λ_Q(s)` (`LambdaQ_one_sub`), it is holomorphic off `s = 0, 1`
  (`differentiableAt_LambdaQ`), it is `∫₀^∞ (θ_Q(t) − 1)t^s dt/t = 2(π/√2)^{−s}Γ(s)ζ(s)L(s, χ₋₈)` on `Re s > 1`
  (`hasMellin_thetaQ`, `LambdaQ_eq_of_one_lt_re`), and by the identity theorem `Λ_Q(s) = √8^s ζ̂(s)Λ(s, χ₋₈)` off
  `s = 0, 1` (`LambdaQ_eq`): the completed Dedekind zeta function `|d|^{s/2}Γ_ℂ(s)ζ_K(s)` of `ℚ(√−2)`, `d = −8`.
* **The Riemann hypothesis for `x² + 2y²`**, that the zeros of `Λ_Q` with `0 < Re s < 1` have `Re s = 1/2`, is RH for
  `ζ` and GRH for `χ₋₈` (`LambdaQ_eq_zero_iff`, `rh_iff`), and so it is Weil's twin criterion for `ζ_{ℚ(√−2)}`
  (`rh_iff_twins`, from `WeilTwinGeneral.rh_grh_iff_twins_Q8`).
This is the companion of `TwoVariableZetaTwo` (`x² + y²`, `ℤ[i]`) and `EpsteinHexagonal` (`x² + xy + y²`, `ℤ[ω]`).
-/
import Mathlib
import QuadIdeals
import EpsteinHexagonal

open NumberField Ideal Finset

noncomputable section

namespace EpsteinTwo

/-! ## The field `ℚ(√−2)` and its ring of integers `ℤ[√−2]` -/

section Arithmetic

open QuadraticAlgebra

/-- `K = ℚ(√−2)`: Mathlib's quadratic algebra `ℚ[ω]` with `ω² = −2`. -/
abbrev K : Type := QuadraticAlgebra ℚ (-2) 0

instance fact_no_root : Fact (∀ r : ℚ, r ^ 2 ≠ -2 + 0 * r) := ⟨fun r h => by nlinarith [sq_nonneg r]⟩

instance numberField : NumberField K where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

lemma finrank_K : Module.finrank ℚ K = 2 := QuadraticAlgebra.finrank_eq_two _ _

lemma norm_mk (x y : ℚ) : QuadraticAlgebra.norm (⟨x, y⟩ : K) = x ^ 2 + 2 * y ^ 2 := by
  rw [norm_def]
  ring

lemma norm_nonneg' (z : K) : 0 ≤ QuadraticAlgebra.norm z := by
  rw [← z.mk_eta, norm_mk]
  positivity

/-- The norm of `K/ℚ` is the norm form of the quadratic algebra. -/
lemma norm_coe_int (x : 𝓞 K) : QuadraticAlgebra.norm (x : K) = (Algebra.norm ℤ x : ℚ) := by
  rw [Algebra.coe_norm_int, Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  rfl

lemma natAbs_norm (x : 𝓞 K) : ((Algebra.norm ℤ x).natAbs : ℚ) = QuadraticAlgebra.norm (x : K) := by
  rw [norm_coe_int, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg]
  rw [← norm_coe_int]
  exact norm_nonneg' _

lemma isIntegral_omega : IsIntegral ℤ (ω : K) :=
  ⟨Polynomial.X ^ 2 + 2, Polynomial.monic_X_pow_add_C _ two_ne_zero, by ext <;> simp [sq]⟩

/-- `√−2 ∈ 𝓞 K`. -/
def rt : 𝓞 K := ⟨ω, isIntegral_omega⟩

/-- The norm form `Q(x, y) = x² + 2y²`. -/
def qf (v : ℤ × ℤ) : ℤ := v.1 ^ 2 + 2 * v.2 ^ 2

lemma qf_nonneg (v : ℤ × ℤ) : 0 ≤ qf v := by
  unfold qf
  positivity

/-- `ι(x, y) = x + y√−2`. -/
def ι (v : ℤ × ℤ) : 𝓞 K := (v.1 : 𝓞 K) + (v.2 : 𝓞 K) * rt

lemma coe_ι (v : ℤ × ℤ) : ((ι v : 𝓞 K) : K) = ⟨(v.1 : ℚ), (v.2 : ℚ)⟩ := by
  have h : ((rt : 𝓞 K) : K) = ω := rfl
  simp only [ι, map_add, map_mul, map_intCast, h]
  ext <;> simp

/-- `N(x + y√−2) = x² + 2y²`. -/
lemma algNorm_ι (v : ℤ × ℤ) : Algebra.norm ℤ (ι v) = qf v := by
  have h := norm_coe_int (ι v)
  rw [coe_ι, norm_mk] at h
  have h' : ((Algebra.norm ℤ (ι v) : ℤ) : ℚ) = ((qf v : ℤ) : ℚ) := by rw [← h, qf]; push_cast; ring
  exact_mod_cast h'

lemma ι_injective : Function.Injective ι := fun v w h => by
  have h' := congrArg (fun z : 𝓞 K => (z : K)) h
  simp only [coe_ι, QuadraticAlgebra.mk.injEq, Int.cast_inj] at h'
  exact Prod.ext h'.1 h'.2

/-- A rational number whose square is an integer is an integer. -/
lemma exists_int_of_sq {w : ℚ} {k : ℤ} (h : w ^ 2 = k) : ∃ W : ℤ, (W : ℚ) = w := by
  obtain ⟨W, hW⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨Polynomial.X ^ 2 - Polynomial.C k,
    Polynomial.monic_X_pow_sub_C _ two_ne_zero, by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h]; simp⟩ : IsIntegral ℤ w)
  exact ⟨W, by simpa using hW⟩

lemma two_dvd_of_sq {a b : ℤ} (h : a ^ 2 = 2 * b) : 2 ∣ a :=
  even_iff_two_dvd.1 (Int.even_pow.1 ⟨b, by rw [h]; ring⟩).1

/-- **The ring of integers of `ℚ(√−2)` is `ℤ[√−2]`**: the norms of an integral `z = r + s√−2` and of `z + 1` are
integers, so `t = 2r` and `W = 4s` are, with `2t² + W² = 8N(z)`, which forces `t` even and `4 ∣ W`. -/
lemma ι_surjective : Function.Surjective ι := by
  intro x
  set r := (x : K).re
  set s := (x : K).im
  have h1 : r ^ 2 + 2 * s ^ 2 = (Algebra.norm ℤ x : ℚ) := by
    rw [← norm_coe_int, ← norm_mk]
  have h2 : (r + 1) ^ 2 + 2 * s ^ 2 = (Algebra.norm ℤ (x + 1) : ℚ) := by
    rw [← norm_coe_int, ← norm_mk]
    congr 1
    ext <;> simp [r, s]
  set n := Algebra.norm ℤ x
  obtain ⟨t, ht⟩ : ∃ t : ℤ, 2 * r = t := ⟨Algebra.norm ℤ (x + 1) - n - 1, by push_cast; linarith⟩
  obtain ⟨W, hW⟩ := exists_int_of_sq (w := 4 * s) (k := 8 * n - 2 * t ^ 2) (by push_cast; rw [← ht]; linarith)
  have key : W ^ 2 = 2 * (4 * n - t ^ 2) := by
    have : ((W : ℚ)) ^ 2 = 2 * (4 * n - (t : ℚ) ^ 2) := by rw [hW, ← ht]; linarith
    exact_mod_cast this
  obtain ⟨W1, rfl⟩ := two_dvd_of_sq key
  obtain ⟨t1, rfl⟩ := two_dvd_of_sq (a := t) (b := 2 * n - W1 ^ 2) (by linarith)
  obtain ⟨W2, rfl⟩ := two_dvd_of_sq (a := W1) (b := n - t1 ^ 2) (by linarith)
  refine ⟨(t1, W2), RingOfIntegers.ext ?_⟩
  rw [coe_ι]
  ext
  · simp only [Int.cast_mul, Int.cast_ofNat] at ht ⊢; linarith
  · simp only [Int.cast_mul, Int.cast_ofNat] at hW ⊢; linarith

/-- Every `z ∈ K` is within norm `3/4` of `ℤ[√−2]`: round both coordinates. -/
lemma exists_norm_sub_lt (z : K) : ∃ v : ℤ × ℤ, QuadraticAlgebra.norm (z - (ι v : K)) < 1 := by
  refine ⟨(round z.re, round z.im), ?_⟩
  obtain ⟨h1, h1'⟩ := abs_le.1 (abs_sub_round z.re)
  obtain ⟨h2, h2'⟩ := abs_le.1 (abs_sub_round z.im)
  have e : z - (ι (round z.re, round z.im) : K) = ⟨z.re - round z.re, z.im - round z.im⟩ := by
    rw [coe_ι]
    ext <;> simp
  rw [e, norm_mk]
  nlinarith

/-- **`ℤ[√−2]` is a principal ideal domain**, by Euclid's algorithm: an ideal is generated by an element `β` of
least norm, since `γ − δβ` with `δ ∈ ℤ[√−2]` nearest to `γ/β` has smaller norm. -/
instance isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) where
  principal I := by
    classical
    by_cases hI : I = ⊥
    · rw [hI]
      exact bot_isPrincipal
    have hex : ∃ k : ℕ, ∃ β ∈ I, β ≠ 0 ∧ (Algebra.norm ℤ β).natAbs = k := by
      obtain ⟨β, hβ, hβ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, β, hβ, hβ0, rfl⟩
    obtain ⟨β, hβI, hβ0, hβk⟩ := Nat.find_spec hex
    refine ⟨β, le_antisymm (fun γ hγ => ?_) ((Ideal.span_singleton_le_iff_mem I).2 hβI)⟩
    obtain ⟨v, hv⟩ := exists_norm_sub_lt ((γ : K) / (β : K))
    by_cases hρ : γ - ι v * β = 0
    · exact Ideal.mem_span_singleton'.2 ⟨ι v, (sub_eq_zero.1 hρ).symm⟩
    exfalso
    have hmin := Nat.find_min' hex ⟨_, I.sub_mem hγ (I.mul_mem_left _ hβI), hρ, rfl⟩
    rw [← hβk] at hmin
    have hβK : (β : K) ≠ 0 := by exact_mod_cast hβ0
    have e : ((γ - ι v * β : 𝓞 K) : K) = (β : K) * ((γ : K) / (β : K) - (ι v : K)) := by
      push_cast
      field_simp
    have hle : (((Algebra.norm ℤ β).natAbs : ℕ) : ℚ) ≤ (((Algebra.norm ℤ (γ - ι v * β)).natAbs : ℕ) : ℚ) := by
      exact_mod_cast hmin
    rw [natAbs_norm, natAbs_norm, e, map_mul] at hle
    have hpos : 0 < QuadraticAlgebra.norm (β : K) :=
      lt_of_le_of_ne (norm_nonneg' _) (Ne.symm (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.not.2 hβK))
    nlinarith

lemma ι_mul (v w : ℤ × ℤ) : ι v * ι w = ι (v.1 * w.1 - 2 * v.2 * w.2, v.1 * w.2 + v.2 * w.1) := by
  apply RingOfIntegers.ext
  rw [show ((ι v * ι w : 𝓞 K) : K) = (ι v : K) * (ι w : K) from rfl, coe_ι, coe_ι, coe_ι]
  ext
  · simp
    ring
  · simp

lemma natCast_eq_ι (n : ℕ) : (n : 𝓞 K) = ι (n, 0) := by
  apply RingOfIntegers.ext
  rw [coe_ι]
  ext <;> simp

lemma natCast_dvd_ι {p : ℕ} {v : ℤ × ℤ} : (p : 𝓞 K) ∣ ι v ↔ (p : ℤ) ∣ v.1 ∧ (p : ℤ) ∣ v.2 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := ι_surjective w
    rw [natCast_eq_ι, ι_mul] at hw
    have h := ι_injective hw
    rw [h]
    exact ⟨⟨u.1, by ring⟩, ⟨u.2, by ring⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨ι (a, b), ?_⟩
    rw [natCast_eq_ι, ι_mul]
    congr 1
    ext <;> simp [ha, hb]

/-- `N(ι v) = Q(v)`, as the norm of the principal ideal. -/
lemma absNorm_ι (v : ℤ × ℤ) : ((absNorm (span {ι v}) : ℕ) : ℤ) = qf v := by
  rw [absNorm_span_singleton, algNorm_ι, Int.natCast_natAbs, abs_of_nonneg (qf_nonneg v)]

/-- An ideal of norm `p` is `(x + y√−2)` with `x² + 2y² = p`. -/
lemma exists_of_absNorm {p : ℕ} {P : Ideal (𝓞 K)} (hP : absNorm P = p) : ∃ v, P = span {ι v} ∧ qf v = p := by
  obtain ⟨π, rfl⟩ : ∃ π, P = span {π} := ⟨_, (Ideal.span_singleton_generator P).symm⟩
  obtain ⟨v, rfl⟩ := ι_surjective π
  refine ⟨v, rfl, ?_⟩
  rw [← absNorm_ι, hP]

/-- If `p = x² + 2y²`, then `−2` is a square mod `p`. -/
lemma isSquare_of_qf {p : ℕ} [Fact p.Prime] {v : ℤ × ℤ} (h : qf v = p) : IsSquare (-2 : ZMod p) := by
  have h' : (v.1 : ZMod p) ^ 2 + 2 * (v.2 : ZMod p) ^ 2 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) h
    push_cast [qf] at this
    rw [this, ZMod.natCast_self]
  by_cases hy : (v.2 : ZMod p) = 0
  · exfalso
    rw [hy] at h'
    have hx : (v.1 : ZMod p) = 0 := by simpa using h'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
    refine hpZ.not_isUnit (IsUnit.of_mul_eq_one (a ^ 2 + 2 * b ^ 2) (mul_left_cancel₀ hpZ.ne_zero ?_))
    rw [qf, ha, hb] at h
    linear_combination h
  · exact ⟨v.1 / v.2, by field_simp; linear_combination -h'⟩

/-- **`2` ramifies**: `2𝓞 = (√−2)²`, and `N(√−2) = 2`. -/
lemma ramified_two : QuadIdeals.pFactors (K := K) 2 = {span {rt}, span {rt}} ∧ absNorm (span {rt}) = 2 := by
  have hrt : rt = ι (0, 1) := by simp [ι]
  have hN : absNorm (span {rt}) = 2 := by
    have h := absNorm_ι (0, 1)
    rw [← hrt, show qf (0, 1) = 2 by rfl] at h
    exact_mod_cast h
  have hprime : (span {rt}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact Nat.prime_two)
  have hrt0 : span {rt} ≠ ⊥ := fun h => by rw [h, absNorm_bot] at hN; norm_num at hN
  have e : rt ^ 2 = -((2 : ℕ) : 𝓞 K) := by
    rw [sq, hrt, ι_mul, natCast_eq_ι]
    apply RingOfIntegers.ext
    rw [show ((-ι (((2 : ℕ) : ℤ), 0) : 𝓞 K) : K) = -(ι (((2 : ℕ) : ℤ), 0) : K) from rfl, coe_ι, coe_ι]
    ext <;> simp
  have h2 : span {((2 : ℕ) : 𝓞 K)} = span {rt} ^ 2 := by
    rw [Ideal.span_singleton_pow, e, Ideal.span_singleton_neg]
  have hirr : Irreducible (span {rt}) := (Ideal.prime_of_isPrime hrt0 hprime).irreducible
  refine ⟨?_, hN⟩
  rw [QuadIdeals.pFactors, h2, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq]
  rfl

/-- **Inert**: `p ≡ 5, 7 (mod 8)` is prime in `ℤ[√−2]`, since `p = x² + 2y²` would make `−2` a square mod `p`. -/
lemma inert {p : ℕ} (hp : p.Prime) (h : p % 8 = 5 ∨ p % 8 = 7) : QuadIdeals.Inert K p := by
  rcases QuadIdeals.pFactors_cases finrank_K hp with h1 | ⟨hc, hall⟩
  · exact h1
  · exfalso
    obtain ⟨P, hP⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hc]; norm_num)
    obtain ⟨v, -, hv⟩ := exists_of_absNorm (hall P hP)
    have hp2 : p ≠ 2 := by omega
    have := Fact.mk hp
    have := (ZMod.exists_sq_eq_neg_two_iff hp2).1 (isSquare_of_qf hv)
    omega

/-- **Split**: an odd `p ≡ 1, 3 (mod 8)` is `PQ` with `P ≠ Q` of norm `p`. It is not prime, since `−2 ≡ a²` and
`p ∣ (a + √−2)(a − √−2)`; and it does not ramify, since `p ∣ (x + y√−2)²` with `x² + 2y² = p` forces `p ∣ x, y`. -/
lemma split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p % 8 = 1 ∨ p % 8 = 3) : QuadIdeals.Split K p := by
  have := Fact.mk hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rcases QuadIdeals.pFactors_cases finrank_K hp with ⟨P, hPf, -⟩ | ⟨hc, hall⟩
  · exfalso
    have hsp : span {(p : 𝓞 K)} = P := by
      rw [← QuadIdeals.prod_pFactors hp.ne_zero, hPf, Multiset.prod_singleton]
    have hprime : (span {(p : 𝓞 K)}).IsPrime :=
      hsp ▸ (QuadIdeals.pFactors_prime hp (hPf ▸ Multiset.mem_singleton_self P)).1
    obtain ⟨c, hc⟩ := (ZMod.exists_sq_eq_neg_two_iff hp2).2 h
    obtain ⟨k, hk⟩ : (p : ℤ) ∣ (c.val : ℤ) ^ 2 + 2 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hc]
      ring
    generalize ((c.val : ℕ) : ℤ) = a at hk
    have hmem : ι (a, 1) * ι (a, -1) ∈ span {(p : 𝓞 K)} := by
      rw [ι_mul, Ideal.mem_span_singleton]
      refine ⟨ι (k, 0), ?_⟩
      rw [natCast_eq_ι, ι_mul]
      congr 1
      ext
      · simp
        linear_combination hk
      · simp
    rcases hprime.mem_or_mem hmem with h1 | h1
    · rw [Ideal.mem_span_singleton, natCast_dvd_ι] at h1
      exact hpZ.not_isUnit (isUnit_of_dvd_one h1.2)
    · rw [Ideal.mem_span_singleton, natCast_dvd_ι] at h1
      exact hpZ.not_isUnit (isUnit_of_dvd_one (dvd_neg.1 h1.2))
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc
    have hP : P ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    have hQ : Q ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    refine ⟨P, Q, fun hPQ' => ?_, hPQ, hall P hP, hall Q hQ⟩
    subst hPQ'
    obtain ⟨v, rfl, hv⟩ := exists_of_absNorm (hall _ hP)
    have hsp : span {(p : 𝓞 K)} = span {ι v * ι v} := by
      rw [← QuadIdeals.prod_pFactors hp.ne_zero, hPQ, ← Ideal.span_singleton_mul_span_singleton]
      simp
    have hmem : ι v * ι v ∈ span {(p : 𝓞 K)} := hsp ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton, ι_mul, natCast_dvd_ι] at hmem
    have h2 : ¬ (p : ℤ) ∣ 2 := fun hd => by
      have := Int.le_of_dvd two_pos hd
      have := hp.two_le
      omega
    have hx : (p : ℤ) ∣ v.1 := by
      refine hpZ.dvd_of_dvd_pow (n := 2) ((hpZ.dvd_or_dvd ?_).resolve_left h2)
      have e : 2 * v.1 ^ 2 = (v.1 * v.1 - 2 * v.2 * v.2) + qf v := by unfold qf; ring
      rw [e, hv]
      exact dvd_add hmem.1 (dvd_refl _)
    have hy : (p : ℤ) ∣ v.2 := by
      refine hpZ.dvd_of_dvd_pow (n := 2) ((hpZ.dvd_or_dvd ?_).resolve_left h2)
      refine (hpZ.dvd_or_dvd ?_).resolve_left h2
      have e : 2 * (2 * v.2 ^ 2) = qf v - (v.1 * v.1 - 2 * v.2 * v.2) := by unfold qf; ring
      rw [e, hv]
      exact dvd_sub (dvd_refl _) hmem.1
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine hpZ.not_isUnit (IsUnit.of_mul_eq_one (a ^ 2 + 2 * b ^ 2) (mul_left_cancel₀ hpZ.ne_zero ?_))
    rw [qf, ha, hb] at hv
    linear_combination hv

end Arithmetic

/-! ## The points on each ellipse -/

lemma le_of_sq_le {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) : -(n : ℤ) ≤ x ∧ x ≤ n := by
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  constructor
  · by_contra hx
    rw [not_le] at hx
    nlinarith [mul_le_mul_of_nonneg_left (show (n : ℤ) + 1 ≤ -x by linarith) (show (0 : ℤ) ≤ -x by linarith)]
  · by_contra hx
    rw [not_le] at hx
    nlinarith [mul_le_mul_of_nonneg_left (show (n : ℤ) + 1 ≤ x by linarith) (show (0 : ℤ) ≤ x by linarith)]

/-- The points of `ℤ²` on the ellipse `Q(v) = n`. -/
def shell (n : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun v => qf v = n

lemma mem_shell {n : ℕ} {v : ℤ × ℤ} : v ∈ shell n ↔ qf v = n := by
  unfold shell
  simp only [mem_filter, mem_product, mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨le_of_sq_le ?_, le_of_sq_le ?_⟩, h⟩⟩ <;> unfold qf at h <;>
    nlinarith [sq_nonneg v.1, sq_nonneg v.2]

/-- **`r_Q(n)`**: the points of `ℤ²` with `x² + 2y² = n`. -/
def rQ (n : ℕ) : ℕ := (shell n).card

lemma rQ_one : rQ 1 = 2 := by decide

lemma rQ_zero : rQ 0 = 1 := by decide

/-- The elements of `ℤ[√−2]` of norm `n`. -/
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

/-- **Two elements per ideal**: `#{β : N(β) = n} = 2·#{𝔞 : N𝔞 = n}` for `n ≥ 1`. -/
lemma card_elts {n : ℕ} (hn : n ≠ 0) : (elts n).card = 2 * (QuadIdeals.ofNorm (K := K) n).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun β => span {β}) (t := QuadIdeals.ofNorm n) fun β hβ =>
    QuadIdeals.mem_ofNorm.2 (mem_elts.1 hβ), mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun I hI => ?_
  obtain ⟨α₀, rfl⟩ : ∃ α₀, I = span {α₀} := ⟨_, (span_singleton_generator I).symm⟩
  have hα₀ : α₀ ≠ 0 := by
    rintro rfl
    apply hn
    rw [← QuadIdeals.mem_ofNorm.1 hI]
    simp
  have hfib : (elts n).filter (fun β => span {β} = span {α₀}) =
      (elts 1).map ⟨(· * α₀), mul_left_injective₀ hα₀⟩ := by
    ext β
    rw [mem_filter, mem_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [← span_eq_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_elts.2 (h ▸ QuadIdeals.mem_ofNorm.1 hI), h⟩⟩
  rw [hfib, card_map, elts, card_map]
  exact rQ_one

/-- `χ₋₈` as an arithmetic function: Mathlib's `ZMod.χ₈'`. -/
def chiA : ArithmeticFunction ℤ := ⟨fun n => ZMod.χ₈' n, by simp⟩

lemma chiA_apply (n : ℕ) : chiA n = ZMod.χ₈' n := rfl

lemma chiA_mult : chiA.IsMultiplicative :=
  ⟨by rw [chiA_apply, Nat.cast_one, map_one], fun {m n} _ => by
    rw [chiA_apply, chiA_apply, chiA_apply, Nat.cast_mul, map_mul]⟩

/-- **The ideal count of `ℚ(√−2)`**: the number of ideals of `ℤ[√−2]` of norm `n` is `Σ_{d ∣ n} χ₋₈(d)`. -/
theorem rA_eq : QuadIdeals.rA K = chiA * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) := by
  refine QuadIdeals.rA_eq chiA_mult (fun p k _ => by rw [chiA_apply, chiA_apply, Nat.cast_pow, map_pow])
    fun p hp => ?_
  rw [chiA_apply, ZMod.χ₈'_nat_eq_if_mod_eight]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact Or.inr (Or.inr ⟨by decide, _, ramified_two⟩)
  · have h2 : p % 2 = 1 := Nat.odd_iff.1 hodd
    have hp2 : p ≠ 2 := by omega
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases h8 with h | h | h | h
    · exact Or.inl ⟨by simp [h2, h], split hp hp2 (Or.inl h)⟩
    · exact Or.inl ⟨by simp [h2, h], split hp hp2 (Or.inr h)⟩
    · exact Or.inr (Or.inl ⟨by simp [h2, h], inert hp (Or.inl h)⟩)
    · exact Or.inr (Or.inl ⟨by simp [h2, h], inert hp (Or.inr h)⟩)

/-- **The points of `x² + 2y²` on each ellipse**: `r_Q(n) = 2Σ_{d ∣ n} χ₋₈(d)` for `n ≥ 1`. -/
theorem rQ_eq {n : ℕ} (hn : n ≠ 0) : (rQ n : ℤ) = 2 * ∑ d ∈ n.divisors, ZMod.χ₈' d := by
  have h1 : rQ n = (elts n).card := (card_map _).symm
  have h2 : QuadIdeals.rA K n = (QuadIdeals.ofNorm (K := K) n).card := QuadIdeals.rA_apply hn
  have h3 : QuadIdeals.rA K n = ∑ d ∈ n.divisors, ZMod.χ₈' d := by
    rw [rA_eq, ArithmeticFunction.coe_mul_zeta_apply]
    rfl
  rw [h1, card_elts hn, Nat.cast_mul, ← h2, h3]
  norm_num

/-! ## The Dirichlet series `Σ r_Q(n)n^{−s} = 2ζ(s)L(s, χ₋₈)` -/

section Dirichlet

open scoped LSeries.notation

lemma rQ_eq_convolution {n : ℕ} (hn : n ≠ 0) :
    (rQ n : ℂ) = ((2 : ℂ) • (↗PsiOmega.chi8 ⍟ (1 : ℕ → ℂ))) n := by
  rw [Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => PsiOmega.chi8 a)]
  have h := congrArg (Int.cast : ℤ → ℂ) (rQ_eq hn)
  push_cast at h
  rw [h]
  simp [PsiOmega.chi8_nat]

lemma summable_rQ {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n ↦ (rQ n : ℂ)) s := by
  have hc := (DirichletCharacter.LSeriesSummable_of_one_lt_re PsiOmega.chi8 hs).convolution
    (LSeriesSummable_one_iff.mpr hs)
  exact (LSeriesSummable_congr s fun hn ↦ rQ_eq_convolution hn).2 (hc.smul 2)

/-- **The Dirichlet series of `r_Q`**: `Σ_{n ≥ 1} r_Q(n)n^{−s} = 2ζ(s)L(s, χ₋₈)` on `Re s > 1`. -/
theorem lseries_rQ {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (rQ n : ℂ)) s =
      2 * (riemannZeta s * DirichletCharacter.LFunction PsiOmega.chi8 s) := by
  have hχ := DirichletCharacter.LSeriesSummable_of_one_lt_re PsiOmega.chi8 hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  rw [LSeries_congr (fun hn ↦ rQ_eq_convolution hn) s, LSeries_smul, LSeries_convolution' hχ h1,
    DirichletCharacter.LFunction_eq_LSeries PsiOmega.chi8 hs, LSeries_one_eq_riemannZeta hs,
    mul_comm (riemannZeta s)]

end Dirichlet

/-! ## The theta function -/

section Theta

open Real Complex HurwitzZeta Filter Topology Asymptotics

/-- **The theta function of `x² + 2y²`**: `Θ(τ) = Σ_{v ∈ ℤ²} e^{−πτQ(v)}`. -/
def Θ (τ : ℝ) : ℝ := ∑' v : ℤ × ℤ, rexp (-π * (qf v : ℝ) * τ)

/-- `Θ(τ) = θ(τ)θ(2τ)`, for Jacobi's `θ = evenKernel 0`. -/
lemma hasSum_Θ {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun v : ℤ × ℤ => rexp (-π * (qf v : ℝ) * τ)) (evenKernel 0 τ * evenKernel 0 (2 * τ)) :=
  (EpsteinHexagonal.hasSum_prod hτ (by positivity)).congr_fun fun v => by
    rw [← Real.exp_add]
    congr 1
    push_cast [qf]
    ring

lemma Θ_eq {τ : ℝ} (hτ : 0 < τ) : Θ τ = evenKernel 0 τ * evenKernel 0 (2 * τ) := (hasSum_Θ hτ).tsum_eq

/-- **`Θ(τ) = Σ_{n ≥ 0} r_Q(n)e^{−πnτ}`**: group the lattice sum by the ellipses `Q(v) = n`. -/
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

/-- **The functional equation of `Θ`**: `Θ(1/τ) = (τ/√2)Θ(τ/2)`. -/
lemma Θ_inv {τ : ℝ} (hτ : 0 < τ) : Θ (1 / τ) = τ / Real.sqrt 2 * Θ (τ / 2) := by
  rw [Θ_eq (by positivity), Θ_eq (by positivity)]
  have e1 : 2 * (1 / τ) = 1 / (τ / 2) := by field_simp
  have e2 : 2 * (τ / 2) = τ := by ring
  have s1 : Real.sqrt (τ / 2) = Real.sqrt τ / Real.sqrt 2 := Real.sqrt_div' τ (by norm_num)
  rw [e1, e2, EpsteinHexagonal.theta_inv hτ, EpsteinHexagonal.theta_inv (by positivity : 0 < τ / 2), s1]
  have hτ' : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  linear_combination (evenKernel 0 τ * evenKernel 0 (τ / 2) / Real.sqrt 2) * hτ'

/-- **The theta function of `x² + 2y²`**, `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−πtQ(v)/√2} = Θ(t/√2)`. -/
def thetaQ (t : ℝ) : ℝ := Θ (t / Real.sqrt 2)

/-- `θ_Q(t) = Σ_{v ∈ ℤ²} e^{−πtQ(v)/√2}`. -/
theorem hasSum_thetaQ {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : ℤ × ℤ => rexp (-π * t * (qf v : ℝ) / Real.sqrt 2)) (thetaQ t) :=
  (hasSum_Θ (by positivity : 0 < t / Real.sqrt 2)).summable.hasSum.congr_fun fun v => by
    congr 1
    ring

/-- **`θ_Q(1/t) = tθ_Q(t)`**: `x² + 2y²` is similar to its dual form `2x² + y²`, and `θ_Q` is normalised so that it
is self-dual. -/
theorem thetaQ_inv {t : ℝ} (ht : 0 < t) : thetaQ (1 / t) = t * thetaQ t := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e1 : 1 / t / Real.sqrt 2 = 1 / (Real.sqrt 2 * t) := by field_simp
  have e2 : Real.sqrt 2 * t / Real.sqrt 2 = t := by field_simp
  have e3 : Real.sqrt 2 * t / 2 = t / Real.sqrt 2 := by
    rw [div_eq_div_iff (by norm_num) h2]
    linear_combination t * hs
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

/-- `θ_Q(t) − 1` decays like `e^{−πt/√2}`, so faster than any power of `t`. -/
lemma isBigO_thetaQ_sub (r : ℝ) : (fun t => (thetaQ t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have hκ : 0 < π / Real.sqrt 2 := by positivity
  have hO : (fun t => thetaQ t - 1) =O[atTop] fun t => rexp (-(π / Real.sqrt 2) * t) := by
    refine IsBigO.of_bound ((Θ 1 - 1) * rexp π) ?_
    filter_upwards [eventually_ge_atTop (Real.sqrt 2)] with t ht
    have hτ : 1 ≤ t / Real.sqrt 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨h0, h1⟩ : 0 ≤ thetaQ t - 1 ∧ thetaQ t - 1 ≤ (Θ 1 - 1) * rexp (-π * (t / Real.sqrt 2 - 1)) :=
      Θ_sub_one_le hτ
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc, ← Real.exp_add]
    convert h1 using 3
    ring
  refine (isBigO_ofReal_left.mpr (hO.trans (isLittleO_exp_neg_mul_rpow_atTop hκ r).isBigO)).congr_left
    fun t => ?_
  simp

lemma continuousOn_Θ : ContinuousOn Θ (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun τ => evenKernel 0 τ) (Set.Ioi 0) := continuousOn_evenKernel 0
  have h2 : ContinuousOn (fun τ => evenKernel 0 (2 * τ)) (Set.Ioi 0) :=
    (continuousOn_evenKernel 0).comp (by fun_prop : Continuous fun τ : ℝ => 2 * τ).continuousOn
      fun τ (hτ : 0 < τ) => show 0 < 2 * τ by positivity
  exact ContinuousOn.congr (h1.mul h2) fun τ hτ => Θ_eq hτ

lemma locallyIntegrableOn_thetaQ : MeasureTheory.LocallyIntegrableOn (fun t => (thetaQ t : ℂ)) (Set.Ioi 0) := by
  have h : ContinuousOn thetaQ (Set.Ioi 0) :=
    continuousOn_Θ.comp (by fun_prop : Continuous fun t : ℝ => t / Real.sqrt 2).continuousOn
      fun t (ht : 0 < t) => show 0 < t / Real.sqrt 2 by positivity
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

/-! ## The Epstein zeta function of `x² + 2y²` -/

/-- **The completed Epstein zeta function of `x² + 2y²`**, `Λ_Q(s) = ∫₀^∞ θ_Q(t)t^s dt/t` regularised: Mathlib's
`WeakFEPair.Λ` for `θ_Q`. -/
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

/-- **On `Re s > 1`, `Λ_Q(s) = 2(π/√2)^{−s}Γ(s)ζ(s)L(s, χ₋₈)`**: term by term,
`Λ_Q(s) = (π/√2)^{−s}Γ(s)Σ_{n ≥ 1} r_Q(n)n^{−s}`, and `lseries_rQ`. -/
theorem LambdaQ_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LambdaQ s = 2 * ((π / Real.sqrt 2 : ℝ) : ℂ) ^ (-s) * Gamma s * riemannZeta s *
      DirichletCharacter.LFunction PsiOmega.chi8 s := by
  have hκ : 0 < 1 / Real.sqrt 2 := by positivity
  have hsum := summable_rQ hs
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun i : ℕ => if 1 / Real.sqrt 2 * (i : ℝ) = 0 then 0 else
      (rQ i : ℂ) * rexp (-π * (1 / Real.sqrt 2 * i) * t)) ((thetaQ t : ℂ) - 1) := by
    intro t (ht : 0 < t)
    have h := (hasSum_ofReal.2 (hasSum_Θ_nat (show 0 < t / Real.sqrt 2 by positivity))).update 0 0
    convert h using 1
    · funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      · rw [Function.update_of_ne hi, ite_eq_right (by positivity)]
        push_cast
        ring_nf
    · simp [thetaQ, rQ_zero]
      ring
  have h_sum : Summable fun i : ℕ => ‖(rQ i : ℂ)‖ / (1 / Real.sqrt 2 * i) ^ s.re := by
    refine (hsum.norm.mul_left ((1 / Real.sqrt 2) ^ s.re)⁻¹).congr fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hi, Real.mul_rpow hκ.le (Nat.cast_nonneg _)]
      ring
  have hD := hasSum_mellin_pi_mul₀ (a := fun i : ℕ => (rQ i : ℂ)) (p := fun i : ℕ => 1 / Real.sqrt 2 * (i : ℝ))
    (F := fun t => (thetaQ t : ℂ) - 1) (s := s) (fun i => by positivity) (by linarith) hF h_sum
  rw [(hasMellin_thetaQ hs).2] at hD
  have hT : (fun i : ℕ => (π : ℂ) ^ (-s) * Gamma s * (rQ i : ℂ) / ((1 / Real.sqrt 2 * i : ℝ) : ℂ) ^ s) =
      fun i => (π : ℂ) ^ (-s) * Gamma s * ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ (-s) *
        LSeries.term (fun n => (rQ n : ℂ)) s i := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; norm_num at hs
      simp [Complex.zero_cpow hs0]
    · rw [LSeries.term_of_ne_zero hi, ofReal_mul, mul_cpow_ofReal_nonneg hκ.le (Nat.cast_nonneg _),
        ofReal_natCast, cpow_neg ((1 / Real.sqrt 2 : ℝ) : ℂ) s]
      ring
  rw [hT] at hD
  have e := hD.unique (hsum.LSeriesHasSum.mul_left
    ((π : ℂ) ^ (-s) * Gamma s * ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ (-s)))
  rw [lseries_rQ hs] at e
  rw [e, show π / Real.sqrt 2 = π * (1 / Real.sqrt 2) by ring, ofReal_mul,
    mul_cpow_ofReal_nonneg Real.pi_pos.le hκ.le]
  ring

/-! ## The continuation -/

lemma odd_chi8 : PsiOmega.chi8.Odd := by
  have h : ZMod.χ₈' (-1 : ZMod 8) = -1 := by decide
  show PsiOmega.chi8 (-1) = -1
  simp [PsiOmega.chi8, MulChar.ringHomComp_apply, h]

lemma completedLFunction_eq {z : ℂ} (hz : 0 < z.re) :
    DirichletCharacter.completedLFunction PsiOmega.chi8 z =
      Gammaℝ (z + 1) * DirichletCharacter.LFunction PsiOmega.chi8 z := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor PsiOmega.chi8 z (Or.inr (by norm_num))
  rw [odd_chi8.gammaFactor_def] at h
  rw [h, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))]

lemma sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma LambdaQ_eq_completed_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LambdaQ s = ((Real.sqrt 8 : ℝ) : ℂ) ^ s * completedRiemannZeta s *
      DirichletCharacter.completedLFunction PsiOmega.chi8 s := by
  have h0 : 0 < s.re := by linarith
  have ha : 0 ≤ π / Real.sqrt 2 := by positivity
  have hb : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  have hΓ : Gammaℝ s * Gammaℝ (s + 1) = 2 * ((2 * π : ℝ) : ℂ) ^ (-s) * Gamma s := by
    rw [Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def]
    push_cast
    ring
  have key : 2 * ((2 * π : ℝ) : ℂ) ^ (-s) * Gamma s * ((Real.sqrt 8 : ℝ) : ℂ) ^ s =
      2 * ((π / Real.sqrt 2 : ℝ) : ℂ) ^ (-s) * Gamma s := by
    rw [show 2 * π = π / Real.sqrt 2 * Real.sqrt 8 by rw [sqrt_eight]; field_simp, ofReal_mul,
      mul_cpow_ofReal_nonneg ha hb, cpow_neg ((Real.sqrt 8 : ℝ) : ℂ) s]
    have hB : ((Real.sqrt 8 : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (ofReal_ne_zero.2 (by positivity))
    field_simp
  rw [LambdaQ_eq_of_one_lt_re hs, EpsteinHexagonal.completedRiemannZeta_eq h0, completedLFunction_eq h0]
  linear_combination (-((Real.sqrt 8 : ℝ) : ℂ) ^ s * riemannZeta s *
    DirichletCharacter.LFunction PsiOmega.chi8 s) * hΓ +
    (-riemannZeta s * DirichletCharacter.LFunction PsiOmega.chi8 s) * key

/-- **`Λ_Q(s) = √8^s ζ̂(s)Λ(s, χ₋₈)` off `s = 0, 1`**, with Mathlib's completed functions `completedRiemannZeta` and
`DirichletCharacter.completedLFunction`: the completed Dedekind zeta function `|d|^{s/2}Γ_ℂ(s)ζ(s)L(s, χ₋₈)` of
`ℚ(√−2)`. Both sides are holomorphic off `s = 0, 1` and agree on `Re s > 1`. -/
theorem LambdaQ_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LambdaQ s = ((Real.sqrt 8 : ℝ) : ℂ) ^ s * completedRiemannZeta s *
      DirichletCharacter.completedLFunction PsiOmega.chi8 s := by
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
  have hg : DifferentiableOn ℂ (fun z => ((Real.sqrt 8 : ℝ) : ℂ) ^ z * completedRiemannZeta z *
      DirichletCharacter.completedLFunction PsiOmega.chi8 z) U := by
    intro z hz
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    have h8 : DifferentiableAt ℂ (fun z : ℂ => ((Real.sqrt 8 : ℝ) : ℂ) ^ z) z :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (by positivity)))
    have hζ : DifferentiableAt ℂ completedRiemannZeta z := differentiableAt_completedZeta hz.1 hz.2
    have hL : DifferentiableAt ℂ (DirichletCharacter.completedLFunction PsiOmega.chi8) z :=
      (DirichletCharacter.differentiable_completedLFunction PsiOmega.chi8_ne_one) z
    exact ((h8.mul hζ).mul hL).differentiableWithinAt
  have heq : LambdaQ =ᶠ[𝓝 2] fun z => ((Real.sqrt 8 : ℝ) : ℂ) ^ z * completedRiemannZeta z *
      DirichletCharacter.completedLFunction PsiOmega.chi8 z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact LambdaQ_eq_completed_of_one_lt_re hz
  have h2 : (2 : ℂ) ∈ U := by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc h2 heq
    (by simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h0, h1⟩)

/-! ## The zeros and the Riemann hypothesis for `x² + 2y²` -/

/-- **In the strip `0 < Re s < 1`, `Λ_Q(s) = 0` exactly when `ζ(s) = 0` or `L(s, χ₋₈) = 0`.** -/
theorem LambdaQ_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    LambdaQ s = 0 ↔ riemannZeta s = 0 ∨ DirichletCharacter.LFunction PsiOmega.chi8 s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  rw [LambdaQ_eq hs0 hs1, EpsteinHexagonal.completedRiemannZeta_eq h0, completedLFunction_eq h0]
  have hA : ((Real.sqrt 8 : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.2 (by positivity))
  have hB : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hC : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  simp [hA, hB, hC]

/-- **The Riemann hypothesis for `x² + 2y²` is RH for `ζ` and GRH for `χ₋₈`**: the zeros of `Λ_Q` in the strip
`0 < Re s < 1` are the zeros of `ζ` and of `L(s, χ₋₈)` there. -/
theorem rh_iff :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → LambdaQ s = 0 → s.re = 1 / 2) ↔
      (RiemannHypothesis ∧ PsiOmega.GRH PsiOmega.chi8) := by
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

/-- **…and so it is Weil's twin criterion for `ζ_{ℚ(√−2)}`** (`WeilTwinGeneral.rh_grh_iff_twins_Q8`): RH for
`x² + 2y²` holds exactly when the twin form of `ζ(s)L(s, χ₋₈)` is nonnegative on the twin boxes. -/
theorem rh_iff_twins :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → LambdaQ s = 0 → s.re = 1 / 2) ↔
      ∀ l : ℝ, 0 ≤ l → 0 ≤ 2 * WeilForm.weilQ (l + 1) (WeilForm.twin (WeilForm.box 1) l) +
        PsiOmega.QC PsiOmega.chi8 (l + 1) (WeilForm.twin (WeilForm.box 1) l) :=
  rh_iff.trans WeilTwinGeneral.rh_grh_iff_twins_Q8

end Theta

end EpsteinTwo

#print axioms EpsteinTwo.ι_surjective
#print axioms EpsteinTwo.rA_eq
#print axioms EpsteinTwo.rQ_eq
#print axioms EpsteinTwo.lseries_rQ
#print axioms EpsteinTwo.hasSum_thetaQ
#print axioms EpsteinTwo.thetaQ_inv
#print axioms EpsteinTwo.LambdaQ_one_sub
#print axioms EpsteinTwo.differentiableAt_LambdaQ
#print axioms EpsteinTwo.LambdaQ_eq_of_one_lt_re
#print axioms EpsteinTwo.LambdaQ_eq
#print axioms EpsteinTwo.LambdaQ_eq_zero_iff
#print axioms EpsteinTwo.rh_iff
#print axioms EpsteinTwo.rh_iff_twins
