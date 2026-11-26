import CMHost

/-!
# The quadratic subfield of the CM host

The arithmetic of the CM field `E = S.E` (`CMHost`) that the construction of the sharp frontier reads: a square root
`s` of `−d` in `E`, its complex conjugate, the half-integers `(a + bs)/2` of `ℚ(s)`, and the places of `E` over a
prime `g ≡ 1 (mod N)`, with the element `π_g = (α + βs)/2` of norm `g` that the design's split primes (`Adm`, A11)
give.

**`√−d ∈ E`** (`gaussE`, `gaussE_sq`, `exists_sq_eq_neg_d`). With `ζ_d = ζ_N^{N/d}` in `ℚ(ζ_N)`, the quadratic Gauss
sum `G = Σ_{a mod d} (a/d) ζ_d^a` has `G² = (−1/d)·d` (Mathlib's `gaussSum_sq`), which is `−d` for `d ≡ 3 (mod 4)`.
It lies in `E`: an automorphism `σ_u ∈ H` sends `ζ_d` to `ζ_d^u`, hence `G` to `(u/d)·G` (`gaussSum_mulShift`), and
`(u/d) = 1` is the first coordinate of `artin(u) = 1`. The setting does not assume `d ≡ 3 (mod 4)` (`CMHost`), so
the theorems that need it take `hd : S.d % 4 = 3`. `G ∈ E` needs no hypothesis, so `gaussE` is a definition: a
canonical `s`, with no choice.

**Complex conjugation** (`complexConj_sq_eq_neg`). `conj s` is again a square root of `−d`, so it is `±s`. If it
were `s`, then `φ(s)` would be real for an embedding `φ : E → ℂ` (`IsCMField.complexEmbedding_complexConj`), against
`φ(s)² = −d < 0`.

**Half-integers** (`isIntegral_half`, `halfO`, `halfO_mul_conj`). For `a ≡ b (mod 2)`, `x = (a + bs)/2` is a root of
`X² − aX + (a² + db²)/4`. This polynomial is integral when `d ≡ 3 (mod 4)`: with `a = b + 2k` and `d = 4e + 3` its
constant term is `(e + 1)b² + bk + k²`. And `x·conj x = (a² − b²s²)/4 = (a² + db²)/4`.

**Split primes** (`card_residue_of_dvd`). A prime `g ≡ 1 (mod N)` has residue degree `ord_N(g) = 1` in `ℚ(ζ_N)`
(Mathlib's `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`). Residue degrees multiply in the tower
`ℚ ⊆ E ⊆ ℚ(ζ_N)` (`Ideal.inertiaDeg_tower`), so every place `w ∣ g` of `E` has degree one, and `N(w) = g`
(`Ideal.pow_inertiaDeg`).

**`π_g`** (`modEq_one_of_norm`, `halfO_mul_conj_eq`, `isCoprime_halfO_conj`).
* The norm form `4g = α² + dβ²` of A11, with `N ∣ β` and `α ≡ β + 2 (mod 2N)`, gives `g ≡ 1 (mod N)`: with
  `β = Nb'`, `α = Nb' + 2 + 2Nc` and `d = 4e + 3`, `g − 1 = N(2c + Nc² + b' + Ncb' + (e + 1)Nb'²)`.
* `π_g = (α + βs)/2` has `π_g·conj π_g = g`, by the norm identity.
* `(π_g, conj π_g) = (1)`. The ideal contains `g` and `α = π_g + conj π_g`, and `g ∤ α`. Otherwise `g ∣ dβ²`, so
  `g ∣ β`, as `g ∤ d` (`d ∣ N < g`). Then `g² ∣ 4g`, against `g > N ≥ 9`.

**Choices.**
* `s` is any square root of `−d`: the theorems take `hs : s ^ 2 = -(S.d : S.E)`, and `gaussE` is one.
* The element `(a + bs)/2` of `O_E` is `halfO hs hd hab`; `π_g` is `halfO` at A11's `(α, β)`, with
  `α ≡ β (mod 2)` from `α ≡ β + 2 (mod 2N)`.
-/

open NumberField

namespace ZetaBalance.Setting

variable (S : Setting)

/-! ## `√−d` in `E` -/

/-- **The quadratic character** `(·/d)`, valued in `ℚ(ζ_N)`. -/
noncomputable def chiM : MulChar (ZMod S.d) S.M := (quadraticChar (ZMod S.d)).ringHomComp (Int.castRingHom S.M)

/-- **`ζ_d`**: `ζ_N^{N/d}` is a primitive `d`-th root of unity. -/
theorem isPrimitiveRoot_zetaD : IsPrimitiveRoot (IsCyclotomicExtension.zeta S.N ℚ S.M ^ (S.N / S.d)) S.d :=
  (IsCyclotomicExtension.zeta_spec S.N ℚ S.M).pow (NeZero.pos _) (Nat.div_mul_cancel S.d_dvd_N).symm

/-- **The additive character** `a ↦ ζ_d^a` of `ℤ/d`, a primitive one. -/
noncomputable def psiD : AddChar (ZMod S.d) S.M := AddChar.zmodChar S.d S.isPrimitiveRoot_zetaD.pow_eq_one

/-- **The quadratic Gauss sum** `G = Σ_{a mod d} (a/d) ζ_d^a ∈ ℚ(ζ_N)`. -/
noncomputable def gaussM : S.M := gaussSum S.chiM S.psiD

/-- **`G² = −d`** for `d ≡ 3 (mod 4)`: `G² = (−1/d)·d` (`gaussSum_sq`), and `−1` is not a square mod `d`. -/
theorem gaussM_sq (hd : S.d % 4 = 3) : S.gaussM ^ 2 = -(S.d : S.M) := by
  have h2 : ringChar (ZMod S.d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact S.d_ne_two
  rw [gaussM, chiM, psiD,
    gaussSum_sq ((MulChar.ringHomComp_ne_one_iff Int.cast_injective).2 (quadraticChar_ne_one h2))
      ((quadraticChar_isQuadratic _).comp _) (AddChar.zmodChar_primitive_of_primitive_root _ S.isPrimitiveRoot_zetaD),
    MulChar.ringHomComp_apply, ZMod.card,
    quadraticChar_neg_one_iff_not_isSquare.2 fun hsq => ZMod.exists_sq_eq_neg_one_iff.1 hsq hd]
  simp

/-- **`G ∈ E`**: `σ_u ∈ H` sends `ζ_d` to `ζ_d^u`, hence `G` to `(u/d)·G` (`gaussSum_mulShift`), and `(u/d) = 1` is
the first coordinate of `artin(u) = 1`. -/
theorem gaussM_mem : S.gaussM ∈ S.E := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  set e := S.autEquiv σ
  have hσζ : IsCyclotomicExtension.zeta S.N ℚ S.M ^ (e : ZMod S.N).val = σ (IsCyclotomicExtension.zeta S.N ℚ S.M) :=
    (IsCyclotomicExtension.zeta_spec S.N ℚ S.M).autToPow_spec ℚ σ
  set u := ZMod.unitsMap S.d_dvd_N e
  have hu : S.chiM u = 1 := by
    have h := congrArg (fun x => ((Prod.fst x : ℤˣ) : ℤ)) (show S.artin e = 1 from hσ)
    simp only [artin, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.fst_one, MulChar.coe_toUnitHom,
      Units.val_one] at h
    rw [chiM, MulChar.ringHomComp_apply, h, map_one]
  have hψ : ∀ a, σ (S.psiD a) = AddChar.mulShift S.psiD (u : ZMod S.d) a := by
    intro a
    have hua : (u : ZMod S.d) * a = (((e : ZMod S.N).val * a.val : ℕ) : ZMod S.d) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.unitsMap_val, ZMod.cast_eq_val]
    rw [AddChar.mulShift_apply, hua, psiD, AddChar.zmodChar_apply', AddChar.zmodChar_apply, map_pow, map_pow,
      ← hσζ, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  have hσG : σ S.gaussM = gaussSum S.chiM (AddChar.mulShift S.psiD (u : ZMod S.d)) := by
    simp only [gaussM, gaussSum, map_sum, map_mul, hψ]
    congr 1
    ext a
    congr 1
    simp [chiM]
  have h := gaussSum_mulShift S.chiM S.psiD u
  rw [hu, one_mul] at h
  rw [hσG, h, gaussM]

/-- **The Gauss sum in `E`**: `Σ_a (a/d) ζ_d^a`, which lies in `E` as `H` lies in the kernel of `(·/d)`. For
`d ≡ 3 (mod 4)` it is a square root of `−d` (`gaussE_sq`). -/
noncomputable def gaussE : S.E := ⟨S.gaussM, S.gaussM_mem⟩

/-- **`gaussE² = −d`** for `d ≡ 3 (mod 4)`. -/
theorem gaussE_sq (hd : S.d % 4 = 3) : S.gaussE ^ 2 = -(S.d : S.E) :=
  Subtype.ext (by simpa [gaussE] using S.gaussM_sq hd)

/-- **`√−d ∈ E`** for `d ≡ 3 (mod 4)`: `gaussE` is one. -/
theorem exists_sq_eq_neg_d (hd : S.d % 4 = 3) : ∃ s : S.E, s ^ 2 = -(S.d : S.E) := ⟨S.gaussE, S.gaussE_sq hd⟩

/-! ## Complex conjugation -/

variable {S}

/-- **`conj s = −s`** for `s² = −d`: `conj s = ±s`, and `conj s = s` would make `φ(s)` real for an embedding
`φ : E → ℂ`, against `φ(s)² = −d < 0`. -/
theorem complexConj_sq_eq_neg {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) : IsCMField.complexConj S.E s = -s := by
  set c := IsCMField.complexConj S.E s with hc_def
  have hc : c ^ 2 = -(S.d : S.E) := by rw [hc_def, ← map_pow, hs, map_neg, map_natCast]
  have h0 : (c - s) * (c + s) = 0 := by linear_combination hc - hs
  rcases mul_eq_zero.1 h0 with h | h
  · exfalso
    have hcs : c = s := sub_eq_zero.1 h
    let φ : S.E →+* ℂ := Classical.choice inferInstance
    have h1 : starRingEnd ℂ (φ s) = φ s := by
      rw [← IsCMField.complexEmbedding_complexConj, ← hc_def, hcs]
    have h2 : φ s ^ 2 = -(S.d : ℂ) := by rw [← map_pow, hs, map_neg, map_natCast]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = φ s := ⟨(φ s).re, Complex.conj_eq_iff_re.1 h1⟩
    rw [← hr] at h2
    have h3 : r ^ 2 = -(S.d : ℝ) := by exact_mod_cast h2
    have : (0 : ℝ) < S.d := by exact_mod_cast (Fact.out : S.d.Prime).pos
    nlinarith [sq_nonneg r]
  · exact eq_neg_of_add_eq_zero_left h

/-! ## Half-integers -/

/-- **`(a + bs)/2` is integral** for `a ≡ b (mod 2)`: with `a = b + 2k` and `d = 4e + 3`, it is a root of
`X² − aX + (e + 1)b² + bk + k²`. -/
theorem isIntegral_half {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) : IsIntegral ℤ (((a : S.E) + b * s) / 2) := by
  obtain ⟨k, hk⟩ := hab.symm.dvd
  obtain rfl : a = b + 2 * k := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℕ, S.d = 4 * e + 3 := ⟨S.d / 4, by omega⟩
  have hdE : (S.d : S.E) = 4 * e + 3 := by exact_mod_cast he
  refine ⟨(Polynomial.X ^ 2 - Polynomial.C (b + 2 * k) * Polynomial.X +
    Polynomial.C ((e + 1) * b ^ 2 + b * k + k ^ 2) : Polynomial ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  simp only [eq_intCast]
  push_cast
  linear_combination ((b : S.E) ^ 2 / 4) * hs - ((b : S.E) ^ 2 / 4) * hdE

/-- **`(a + bs)/2` as an element of `O_E`**, for `a ≡ b (mod 2)` (`isIntegral_half`). -/
noncomputable def halfO {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) : 𝓞 S.E :=
  ⟨((a : S.E) + b * s) / 2, isIntegral_half hs hd hab⟩

/-- **`halfO` in `E`** is `(a + bs)/2`. -/
@[simp] theorem coe_halfO {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) : (halfO hs hd hab : S.E) = ((a : S.E) + b * s) / 2 := rfl

/-- **The norm form**: `(a + bs)/2 · conj((a + bs)/2) = (a² + db²)/4`. -/
theorem halfO_mul_conj {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) :
    (halfO hs hd hab : S.E) * IsCMField.complexConj S.E (halfO hs hd hab) =
      ((a ^ 2 + S.d * b ^ 2 : ℤ) : S.E) / 4 := by
  rw [coe_halfO, map_div₀, map_add, map_mul, map_intCast, map_intCast, complexConj_sq_eq_neg hs, map_ofNat]
  push_cast
  linear_combination (-(b : S.E) ^ 2 / 4) * hs

/-! ## Split primes -/

/-- **`N < g`** for a prime `g ≡ 1 (mod N)`, as `N ∣ g − 1 ≠ 0`. -/
theorem lt_of_modEq_one {g : ℕ} (hg : g.Prime) (h1 : g ≡ 1 [MOD S.N]) : S.N < g := by
  have := hg.two_le
  have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' hg.one_lt.le).1 h1.symm)
  omega

/-- **Residue degree one**: a prime `g ≡ 1 (mod N)` splits completely in `ℚ(ζ_N)`
(`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`: the residue degree is the order of `g` mod `N`), so every
place `w ∣ g` of `E ⊆ ℚ(ζ_N)` has residue field `𝔽_g` (`Ideal.inertiaDeg_tower`). -/
theorem card_residue_of_dvd {g : ℕ} (hg : g.Prime) (h1 : g ≡ 1 [MOD S.N])
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 S.E)) (hw : (g : 𝓞 S.E) ∈ w.asIdeal) :
    Ideal.absNorm w.asIdeal = g := by
  have := Fact.mk hg
  have := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(g : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime g) Ideal.IsPrime.ne_top' ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
    simpa using hw
  obtain ⟨⟨P, hP, hPw⟩⟩ := w.asIdeal.nonempty_primesOver (S := 𝓞 S.M)
  have : P.LiesOver (Ideal.span {(g : ℤ)}) := Ideal.LiesOver.trans P w.asIdeal _
  have hN : ¬ g ∣ S.N := Nat.not_dvd_of_pos_of_lt (NeZero.pos _) (lt_of_modEq_one hg h1)
  have h := Ideal.inertiaDeg_tower w.asIdeal P (R := ℤ)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd g S.M P hN,
    orderOf_eq_one_iff.2 (by simpa using (ZMod.natCast_eq_natCast_iff g 1 S.N).2 h1)] at h
  rw [← Ideal.pow_inertiaDeg g w.asIdeal, Nat.eq_one_of_mul_eq_one_right h.symm, pow_one]

/-- **`g ≡ 1 (mod N)`** from the norm form of A11: `4g = α² + dβ²` with `N ∣ β` and `α ≡ β + 2 (mod 2N)`. With
`β = Nb'`, `α = Nb' + 2 + 2Nc` and `d = 4e + 3`, `g − 1 = N(2c + Nc² + b' + Ncb' + (e + 1)Nb'²)`. -/
theorem modEq_one_of_norm (hd : S.d % 4 = 3) {g : ℕ} {α β : ℤ} (h4 : 4 * (g : ℤ) = α ^ 2 + S.d * β ^ 2)
    (hβ : (S.N : ℤ) ∣ β) (hα : α ≡ β + 2 [ZMOD 2 * S.N]) : g ≡ 1 [MOD S.N] := by
  obtain ⟨b, rfl⟩ := hβ
  obtain ⟨c, hc⟩ := hα.symm.dvd
  obtain rfl : α = S.N * b + 2 + 2 * S.N * c := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℕ, S.d = 4 * e + 3 := ⟨S.d / 4, by omega⟩
  have hd' : (S.d : ℤ) = 4 * e + 3 := by exact_mod_cast he
  rw [hd'] at h4
  rw [Nat.modEq_iff_dvd]
  refine ⟨-(2 * c + S.N * c ^ 2 + b + S.N * c * b + (e + 1) * S.N * b ^ 2), ?_⟩
  refine mul_left_cancel₀ (four_ne_zero (α := ℤ)) ?_
  push_cast
  linear_combination -h4

/-- **`π_g·conj π_g = g`** in `O_E`, for `4g = a² + db²` (`halfO_mul_conj`). -/
theorem halfO_mul_conj_eq {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) {g : ℕ} (h4 : 4 * (g : ℤ) = a ^ 2 + S.d * b ^ 2) :
    halfO hs hd hab * IsCMField.ringOfIntegersComplexConj S.E (halfO hs hd hab) = g := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.val, map_mul, map_natCast]
  exact (halfO_mul_conj hs hd hab).trans (by rw [← h4]; push_cast; ring)

/-- **`(π_g, conj π_g) = (1)`**, for a prime `g ≡ 1 (mod N)` with `4g = a² + db²`: the ideal holds
`g = π_g·conj π_g` and `a = π_g + conj π_g`, and `g ∤ a`. Else `g ∣ db²`, so `g ∣ b` (`g ∤ d` as `d ∣ N < g`), and
`g² ∣ 4g`, against `g > N ≥ 9`. -/
theorem isCoprime_halfO_conj {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) {g : ℕ} (hg : g.Prime) (h1 : g ≡ 1 [MOD S.N])
    (h4 : 4 * (g : ℤ) = a ^ 2 + S.d * b ^ 2) :
    IsCoprime (halfO hs hd hab) (IsCMField.ringOfIntegersComplexConj S.E (halfO hs hd hab)) := by
  set x := halfO hs hd hab
  set y := IsCMField.ringOfIntegersComplexConj S.E x
  have hxy : x * y = g := halfO_mul_conj_eq hs hd hab h4
  have hsum : x + y = a := by
    apply RingOfIntegers.ext
    simp only [RingOfIntegers.val, map_add, map_intCast]
    change ((a : S.E) + b * s) / 2 + IsCMField.complexConj S.E (((a : S.E) + b * s) / 2) = a
    rw [map_div₀, map_add, map_mul, map_intCast, map_intCast, complexConj_sq_eq_neg hs, map_ofNat]
    ring
  have hlt := lt_of_modEq_one hg h1
  have hN : 9 ≤ S.N := by
    have := (Fact.out : S.q.Prime).two_le
    have := (Fact.out : S.d.Prime).two_le
    have := S.q_ne_two
    have := S.d_ne_two
    calc 9 = 3 * 3 := rfl
      _ ≤ S.q * S.d := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ S.N := Nat.le_of_dvd (NeZero.pos _) ⟨S.QS, by rw [N]; ring⟩
  have hpg : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  have hga : ¬ (g : ℤ) ∣ a := by
    intro hga
    have hgb : (g : ℤ) ∣ b := by
      have hdb : (g : ℤ) ∣ S.d * b ^ 2 := by
        rw [show (S.d : ℤ) * b ^ 2 = 4 * g - a ^ 2 by linarith]
        exact dvd_sub (dvd_mul_left _ _) (dvd_pow hga two_ne_zero)
      rcases hpg.dvd_or_dvd hdb with h | h
      · have := Nat.le_of_dvd (Fact.out : S.d.Prime).pos (Int.natCast_dvd_natCast.1 h)
        have := Nat.le_of_dvd (NeZero.pos _) S.d_dvd_N
        omega
      · exact hpg.dvd_of_dvd_pow h
    obtain ⟨a', rfl⟩ := hga
    obtain ⟨b', rfl⟩ := hgb
    have h4' : (g : ℤ) * (a' ^ 2 + S.d * b' ^ 2) = 4 :=
      mul_left_cancel₀ (Int.natCast_ne_zero.2 hg.ne_zero) (by linear_combination -h4)
    have h4d : (g : ℤ) ∣ 4 := Dvd.intro _ h4'
    have h4d : g ∣ 4 := by exact_mod_cast h4d
    have := Nat.le_of_dvd (by norm_num) h4d
    omega
  obtain ⟨u, v, huv⟩ := hpg.coprime_iff_not_dvd.2 hga
  refine ⟨u * y + v, v, ?_⟩
  have h : (u : 𝓞 S.E) * g + v * a = 1 := by exact_mod_cast huv
  rw [← h, ← hxy, ← hsum]
  ring

end ZetaBalance.Setting
