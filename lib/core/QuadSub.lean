import CMHost

/-!
# The quadratic subfield of the CM host

The arithmetic of the CM field `E = S.E` (`CMHost`) that the construction of the sharp frontier reads: a square root
`s` of `−d` in `E`, its complex conjugate, and the half-integers `(a + bs)/2` of `ℚ(s)`, among them the element
`π_g = (α + βs)/2` of norm `g` that the design's split primes (`Adm`, A11) give.

**`√−d ∈ E`** (`gaussE`, `gaussE_sq`). With `ζ_d = ζ_N^{N/d}` in `ℚ(ζ_N)`, the quadratic Gauss
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

**`π_g`** (`halfO_mul_conj_eq`): for `4g = α² + dβ²`, `π_g = (α + βs)/2` has `π_g·conj π_g = g` in `O_E`, by the
norm identity.

**Choices.**
* `s` is any square root of `−d`: the theorems take `hs : s ^ 2 = -(S.d : S.E)`, and `gaussE` is one.
* The element `(a + bs)/2` of `O_E` is `halfO hs hd hab`; `π_g` is `halfO` at A11's `(α, β)`.
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

/-- **`π_g·conj π_g = g`** in `O_E`, for `4g = a² + db²` (`halfO_mul_conj`). -/
theorem halfO_mul_conj_eq {s : S.E} (hs : s ^ 2 = -(S.d : S.E)) (hd : S.d % 4 = 3) {a b : ℤ}
    (hab : a ≡ b [ZMOD 2]) {g : ℕ} (h4 : 4 * (g : ℤ) = a ^ 2 + S.d * b ^ 2) :
    halfO hs hd hab * IsCMField.ringOfIntegersComplexConj S.E (halfO hs hd hab) = g := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.val, map_mul, map_natCast]
  exact (halfO_mul_conj hs hd hab).trans (by rw [← h4]; push_cast; ring)

end ZetaBalance.Setting
