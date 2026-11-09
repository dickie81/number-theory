/-
# Principal ideals of prime norm in an imaginary quadratic field

Imports Mathlib and the library's `QuadSplit` (with `QuadRing` and `QuadIdeals`).

Plain statement. Let `K` be a number field of degree `2` with no real place, and `D_K` its discriminant.

* `norm_eq_of_basis`: if `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then
  `N(u + vθ) = u² + euv − cv²`.
* `neg_of_nrRealPlaces`: if `K` has no real place and `s² = d` in `K`, `d` an integer, then `d < 0`.
* `abs_discr_le_of_norm`: an element of `𝓞 K` whose norm is a prime `p` up to sign forces `|D_K| ≤ 4p`. For
  `d ≡ 1 (mod 4)` the norm form is `((2u + v)² + |d|v²)/4` and `D_K = d`; for `d ≡ 2, 3 (mod 4)` it is `u² + |d|v²`
  and `D_K = 4d`. A value `p` with `v = 0` would make `p` a square.
* `abs_discr_le_of_isPrincipal`: so a principal ideal of prime norm `p` forces `|D_K| ≤ 4p`.
* `abs_discr_le_of_split`, `abs_discr_le_of_ramified`: if `K` has class number one, a prime `p` that splits or
  ramifies in `K` has `|D_K| ≤ 4p`. So in a field of class number one every prime `p < |D_K|/4` is inert.
* `classNumber_eq_one_of_inert`: conversely, if every class of ideals contains an ideal of norm at most `B` and every
  prime `p ≤ B` is inert, then `K` has class number one. An ideal `I ≠ 𝓞` of norm `m ≤ B` lies in a prime `P`, whose
  rational prime `p` divides `m`; `p` is inert, so `P = p𝓞`, and `I = p·J` with `J` of norm `m/p²` (induction).
-/
import Mathlib
import QuadSplit

open NumberField Ideal
open scoped nonZeroDivisors

namespace QuadPrincipal

variable {K : Type*} [Field K] [NumberField K]

/-! ### The norm form -/

omit [NumberField K] in
/-- **If `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then `N(u + vθ) = u² + euv − cv²`.** -/
theorem norm_eq_of_basis {θ : 𝓞 K} {c e : ℤ} (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb0 : b 0 = 1)
    (hb1 : b 1 = θ) (hθ : θ ^ 2 = c + e * θ) (u v : ℤ) :
    Algebra.norm ℤ ((u : 𝓞 K) + v * θ) = u ^ 2 + e * u * v - c * v ^ 2 := by
  classical
  have hθθ : θ * θ = c + e * θ := by rw [← sq, hθ]
  have h0 : ((u : 𝓞 K) + v * θ) * b 0 = u • b 0 + v • b 1 := by
    rw [hb0, hb1, mul_one, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  have h1 : ((u : 𝓞 K) + v * θ) * b 1 = (v * c) • b 0 + (u + v * e) • b 1 := by
    rw [hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one]
    push_cast
    linear_combination (v : 𝓞 K) * hθθ
  have r0 : b.repr (((u : 𝓞 K) + v * θ) * b 0) = u • Finsupp.single 0 1 + v • Finsupp.single 1 1 := by
    rw [h0, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  have r1 : b.repr (((u : 𝓞 K) + v * θ) * b 1) =
      (v * c) • Finsupp.single 0 1 + (u + v * e) • Finsupp.single 1 1 := by
    rw [h1, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    r0, r1]
  simp
  ring

/-! ### An imaginary quadratic field is `ℚ(√d)` with `d < 0` -/

/-- **If `K` has no real place and `s² = d` in `K`, then `d < 0`.** Otherwise an embedding of `K` in `ℂ` sends `s` to
a real number, and `K = ℚ + ℚs` to `ℝ`. -/
theorem neg_of_nrRealPlaces {d : ℤ} {s : K} (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
    (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) : d < 0 := by
  by_contra hneg
  rw [not_lt] at hneg
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hφs : (φ s) ^ 2 = (d : ℂ) := by
    rw [← map_pow, hs, map_intCast]
  -- `φ s` is real
  have him : (φ s).im = 0 := by
    have h2 : ((φ s) ^ 2).im = 0 := by rw [hφs]; simp
    have h3 : 0 ≤ ((φ s) ^ 2).re := by rw [hφs]; simpa using (by exact_mod_cast hneg : (0 : ℝ) ≤ d)
    rw [sq, Complex.mul_im] at h2
    rw [sq, Complex.mul_re] at h3
    by_contra hne
    have hre : (φ s).re = 0 := by
      have : 2 * ((φ s).re * (φ s).im) = 0 := by linarith
      rcases mul_eq_zero.1 (by linarith : (φ s).re * (φ s).im = 0) with h | h
      · exact h
      · exact absurd h hne
    rw [hre] at h3
    have : 0 < (φ s).im * (φ s).im := mul_self_pos.2 hne
    linarith
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    obtain ⟨a, b, rfl⟩ := QuadRing.exists_eq hd hd1 hs hK x
    rw [ComplexEmbedding.conjugate_coe_eq, map_add, map_mul, map_ratCast, map_ratCast, map_add, map_mul,
      map_ratCast, map_ratCast, Complex.conj_eq_iff_im.2 him]
  have htc : IsTotallyComplex K := nrRealPlaces_eq_zero_iff.1 hc
  exact IsTotallyComplex.complexEmbedding_not_isReal φ hreal

/-! ### No element of prime norm below `|D_K|/4` -/

/-- A prime is not a square. -/
theorem prime_ne_sq {p : ℕ} (hp : p.Prime) (u : ℤ) : (p : ℤ) ≠ u ^ 2 := by
  intro h
  have h2 : p = u.natAbs * u.natAbs := by
    have h3 := congrArg Int.natAbs h
    rw [Int.natAbs_natCast, Int.natAbs_pow, sq] at h3
    exact h3
  have hdvd : u.natAbs ∣ p := ⟨u.natAbs, h2⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpp
  · rw [h1] at h2
    exact hp.one_lt.ne' (by simpa using h2)
  · rw [hpp] at h2
    have := hp.one_lt
    nlinarith

/-- **An element of `𝓞 K` of prime norm `p` (up to sign) forces `|D_K| ≤ 4p`**, for `K` imaginary quadratic. -/
theorem abs_discr_le_of_norm (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    {p : ℕ} (hp : p.Prime) (y : 𝓞 K) (hy : (Algebra.norm ℤ y).natAbs = p) : |discr K| ≤ 4 * p := by
  obtain ⟨d, s, hd, hd1, hs⟩ := QuadRing.exists_sqrt hK
  have hd0 : d < 0 := neg_of_nrRealPlaces hd hd1 hs hK hc
  have hcases : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    have h0 : d % 4 ≠ 0 := by
      intro h
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
      have := hd 2 ⟨k, by rw [hk]; ring⟩
      exact absurd (Int.isUnit_iff.1 this) (by omega)
    omega
  have hyp : Algebra.norm ℤ y = p ∨ Algebra.norm ℤ y = -(p : ℤ) := by
    rcases Int.natAbs_eq (Algebra.norm ℤ y) with h | h
    · left; rw [h, hy]
    · right; rw [h, hy]
  rcases hcases with h1 | h23
  · -- `d ≡ 1 (mod 4)`: `4N(u + vθ) = (2u + v)² − dv²`, `D_K = d`
    obtain ⟨u, v, rfl⟩ := QuadRing.span_θ₁ hd hd1 hs h1 hK y
    have hN := norm_eq_of_basis (QuadRing.basis₁ hd hd1 hs h1 hK) (by simp [QuadRing.basis₁])
      (by simp [QuadRing.basis₁]) (QuadRing.θ₁_sq hs h1) u v
    rw [QuadRing.discr_θ₁ hd hd1 hs h1 hK, abs_of_neg hd0]
    have hc4 : d = 4 * ((d - 1) / 4) + 1 := by omega
    set c := (d - 1) / 4 with hcdef
    have h4 : 4 * Algebra.norm ℤ ((u : 𝓞 K) + v * QuadRing.θ₁ hs h1) = (2 * u + v) ^ 2 - d * v ^ 2 := by
      rw [hN, hc4]; ring
    have hnn : 0 ≤ (2 * u + v) ^ 2 - d * v ^ 2 := by nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]
    have hNp : Algebra.norm ℤ ((u : 𝓞 K) + v * QuadRing.θ₁ hs h1) = p := by
      rcases hyp with h | h
      · exact h
      · have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        rw [h] at h4
        linarith
    rw [hNp] at h4
    by_cases hv : v = 0
    · exfalso
      rw [hv] at h4
      have : (p : ℤ) = u ^ 2 := by nlinarith
      exact prime_ne_sq hp u this
    · have hv2 : 1 ≤ v ^ 2 := by
        have := sq_pos_of_ne_zero (a := v) hv  -- 0 < v²
        omega
      nlinarith [sq_nonneg (2 * u + v)]
  · -- `d ≡ 2, 3 (mod 4)`: `N(u + vs) = u² − dv²`, `D_K = 4d`
    obtain ⟨u, v, rfl⟩ := QuadRing.span_θ₂ hd hd1 hs h23 hK y
    have hN := norm_eq_of_basis (QuadRing.basis₂ hd hd1 hs h23 hK) (by simp [QuadRing.basis₂])
      (by simp [QuadRing.basis₂]) (QuadRing.θ₂_sq hs) u v
    rw [QuadRing.discr_θ₂ hd hd1 hs h23 hK, abs_of_neg (by linarith)]
    have h4 : Algebra.norm ℤ ((u : 𝓞 K) + v * QuadRing.θ₂ hs) = u ^ 2 - d * v ^ 2 := by
      rw [hN]; ring
    have hnn : 0 ≤ u ^ 2 - d * v ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hNp : Algebra.norm ℤ ((u : 𝓞 K) + v * QuadRing.θ₂ hs) = p := by
      rcases hyp with h | h
      · exact h
      · have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        rw [h] at h4
        linarith
    rw [hNp] at h4
    by_cases hv : v = 0
    · exfalso
      rw [hv] at h4
      have : (p : ℤ) = u ^ 2 := by nlinarith
      exact prime_ne_sq hp u this
    · have hv2 : 1 ≤ v ^ 2 := by
        have := sq_pos_of_ne_zero (a := v) hv
        omega
      nlinarith [sq_nonneg u]

/-- **A principal ideal of prime norm `p` forces `|D_K| ≤ 4p`.** -/
theorem abs_discr_le_of_isPrincipal (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P.IsPrincipal) (hn : absNorm P = p) :
    |discr K| ≤ 4 * p := by
  obtain ⟨⟨y, rfl⟩⟩ := hP
  refine abs_discr_le_of_norm hK hc hp y ?_
  rw [← hn]
  exact (Ideal.absNorm_span_singleton y).symm

/-- **In a field of class number one, a prime that splits has `|D_K| ≤ 4p`.** -/
theorem abs_discr_le_of_split (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    (h1 : classNumber K = 1) {p : ℕ} (hp : p.Prime) (hs : QuadIdeals.Split K p) : |discr K| ≤ 4 * p := by
  obtain ⟨P, -, -, -, hP, -⟩ := hs
  have hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.1 h1
  exact abs_discr_le_of_isPrincipal hK hc hp (IsPrincipalIdealRing.principal P) hP

/-- **In a field of class number one, a prime that ramifies has `|D_K| ≤ 4p`.** -/
theorem abs_discr_le_of_ramified (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    (h1 : classNumber K = 1) {p : ℕ} (hp : p.Prime) (hr : QuadIdeals.Ramified K p) : |discr K| ≤ 4 * p := by
  obtain ⟨P, -, hP⟩ := hr
  have hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.1 h1
  exact abs_discr_le_of_isPrincipal hK hc hp (IsPrincipalIdealRing.principal P) hP

/-! ### Class number one from inert primes -/

omit [NumberField K] in
/-- A prime ideal that contains a natural number `n ≥ 2` contains a prime divisor of `n`. -/
theorem exists_prime_mem {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    ∀ n : ℕ, 2 ≤ n → (n : 𝓞 K) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 K) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    obtain ⟨p, hp, k, rfl⟩ : ∃ p : ℕ, p.Prime ∧ ∃ k, n = p * k := by
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      exact ⟨p, hp, hpn⟩
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p k, h⟩
    · have hk0 : k ≠ 0 := by rintro rfl; omega
      have hk1 : k ≠ 1 := by
        rintro rfl
        exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using h))
      have hlt : k < p * k := by
        have := hp.two_le
        nlinarith [Nat.pos_of_ne_zero hk0]
      obtain ⟨q, hq, hqk, hqP⟩ := ih k hlt (by omega) h
      exact ⟨q, hq, hqk.trans (dvd_mul_left k p), hqP⟩

/-- **Over an inert prime `p` the only prime ideal is `p𝓞`.** -/
theorem eq_span_of_inert {p : ℕ} (hp : p.Prime) (hi : QuadIdeals.Inert K p) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hpP : (p : 𝓞 K) ∈ P) : P = span {(p : 𝓞 K)} := by
  obtain ⟨P₀, hf, -⟩ := hi
  have hmem : P ∈ QuadIdeals.pFactors p := (QuadIdeals.mem_pFactors hp.ne_zero).2 ⟨hP, hpP⟩
  rw [hf, Multiset.mem_singleton] at hmem
  have hprod := QuadIdeals.prod_pFactors (K := K) hp.ne_zero
  rw [hf, Multiset.prod_singleton] at hprod
  rw [hmem, hprod]

/-- **If every prime `p ≤ B` is inert, every nonzero ideal of norm at most `B` is principal.** -/
theorem isPrincipal_of_inert (hK : Module.finrank ℚ K = 2) {B : ℕ}
    (hB : ∀ p : ℕ, p.Prime → p ≤ B → QuadIdeals.Inert K p) :
    ∀ (m : ℕ) (I : Ideal (𝓞 K)), I ≠ ⊥ → absNorm I = m → m ≤ B → I.IsPrincipal := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI0 hm hmB
    by_cases htop : I = ⊤
    · rw [htop]
      refine ⟨⟨1, ?_⟩⟩
      change (⊤ : Ideal (𝓞 K)) = Ideal.span {1}
      rw [Ideal.span_singleton_one]
    obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I htop
    have hPprime : P.IsPrime := hPmax.isPrime
    have hm0 : m ≠ 0 := by
      rw [← hm]
      exact fun h => hI0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hdvd : absNorm P ∣ m := hm ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    have hP0 : absNorm P ≠ 0 := fun h => hm0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)
    have hP1 : absNorm P ≠ 1 := fun h => hPprime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    obtain ⟨p, hp, hpn, hpP⟩ := exists_prime_mem hPprime (absNorm P) (by omega) (Ideal.absNorm_mem P)
    have hpm : p ∣ m := hpn.trans hdvd
    have hple : p ≤ B := (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpm).trans hmB
    have hPeq : P = span {(p : 𝓞 K)} := eq_span_of_inert hp (hB p hp hple) hPprime hpP
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hIP
    have hJ0 : J ≠ ⊥ := by
      rintro rfl
      exact hI0 (by rw [hJ, mul_bot])
    have hnorm : m = p ^ 2 * absNorm J := by
      rw [← hm, hJ, map_mul, hPeq, QuadIdeals.absNorm_natCast_span_sq hK]
    have hJpos : 0 < absNorm J := Nat.pos_of_ne_zero fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hp2 := hp.two_le
    have h4 : 4 ≤ p ^ 2 := by nlinarith
    have hlt : absNorm J < m := by
      rw [hnorm]
      calc absNorm J < 4 * absNorm J := by omega
        _ ≤ p ^ 2 * absNorm J := Nat.mul_le_mul_right _ h4
    obtain ⟨⟨a, ha⟩⟩ := ih (absNorm J) hlt J hJ0 rfl (hlt.le.trans hmB)
    have ha' : J = Ideal.span {a} := ha
    refine ⟨⟨(p : 𝓞 K) * a, ?_⟩⟩
    change I = Ideal.span {(p : 𝓞 K) * a}
    rw [hJ, hPeq, ha', Ideal.span_singleton_mul_span_singleton]

/-- **Class number one from inert primes**: if every class of ideals contains an ideal of norm at most `B`, and every
prime `p ≤ B` is inert, then `K` has class number one. -/
theorem classNumber_eq_one_of_inert (hK : Module.finrank ℚ K = 2) {B : ℕ}
    (hmink : ∀ C : ClassGroup (𝓞 K), ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) ≤ B)
    (hB : ∀ p : ℕ, p.Prime → p ≤ B → QuadIdeals.Inert K p) : classNumber K = 1 := by
  rw [classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C => ?_⟩
  obtain ⟨I, rfl, hI⟩ := hmink C
  rw [ClassGroup.mk0_eq_one_iff]
  exact isPrincipal_of_inert hK hB _ I (nonZeroDivisors.coe_ne_zero I) rfl hI

/-- **Minkowski's bound for an imaginary quadratic field**: every class of ideals contains an ideal of norm at most
`(2/π)√|D_K|`. -/
theorem exists_ideal_norm_le (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0)
    (C : ClassGroup (𝓞 K)) : ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ 2 / Real.pi * Real.sqrt |(discr K : ℝ)| := by
  obtain ⟨I, hI, hle⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨I, hI, hle.trans (le_of_eq ?_)⟩
  have hc1 : InfinitePlace.nrComplexPlaces K = 1 := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hK] at this
    omega
  rw [hc1, hK]
  norm_num [Nat.factorial]
  ring

end QuadPrincipal
