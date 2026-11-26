import Mathlib
import ThetaVol

/-!
# The local data of the Stage-U theta chain at the level places `SG`

The level groups, the single-place ideles and the local parameters of the chain's factors at the places `P ∈ SG`,
for the untwisted chain (Stage U: one index per level, representatives `h = 1`, no twist places `Q`, twist `ξ = 1`).
All are definitions, and they satisfy the library's pins `ThetaVol.LevGOk` (`levG_spec`) and `ThetaVol.LocOk`
(`locOk`, from the arithmetic facts it names), so a construction can use them without carrying proofs.

**Reduction mod `P`.** Every `P`-integral `x ∈ E` is congruent mod `P·O_(P)` to some `y ∈ O_E` (`exists_lift`, from
Mathlib's approximation lemma), and `x ↦ y mod P` is a ring homomorphism `redP` from the valuation subring
`O_(P) = {v_P ≤ 1}` to `O_E/P` (`redP_eq`: any congruent `y` gives it). Entrywise it gives `redGL : GL_n(O_(P)) →
GL_n(O_E/P)` beside `toGL : GL_n(O_(P)) → GL_n(E)`, and `ThetaVol.IsRed` is exactly "a common preimage in
`GL_n(O_(P))`" (`isRed_units`, `exists_of_isRed`: an integral matrix whose reduction is invertible has a `P`-unit
determinant).

**The level groups.** `levG n c J` is the closure of the `ḡ` that are, at each `w ∈ SG`, the reduction of the block
`A(r)` of some `r ∈ R1 ∩ J_w`. That set is a group, as `toGL` and `redGL` are homomorphisms, so `levG` is
`∏_w red_w(prX(R1 ∩ J_w))` exactly (`levG_spec`, the archive's `grpG`). `levU` is the group of step `j`: `uniUT` at
`j = 0`, and `levG` with the sharp `JGsym` (`ThetaVol.jS`) at `j ≥ 1`. The level characters at `j ≥ 1` are not
defined: no factor reads them.

**Ideles from their components.** An idele is built from a nonzero family that is `1` almost everywhere
(`IsIdeleFam`) by `ideleOf` (`1` otherwise), whose components are the family's (`ideleOf_apply`). The single-place
idele `idAtE P a` is `ideleOf` of the family that is `a` at `P` and `1` elsewhere (`1` at `a = 0`); an idele with these
components is unique (`isLocAt_unique`), so it is the `x` of every `ThetaVol.IsLocAt P a x` (`eq_idAtE`).

**The residue character.** At a place of prime norm `q_P` where `xi0` is integral, `ThetaChain.psi0 xi0` is additive
(`psi0_add`): the least representatives of `c`, `c′`, `c + c′` differ by a multiple of `q_P`. It is the per-place
fact behind `ψ_P` here and the step-0 character `χ0 = σ₀⁻¹ ∘ lamGen xi0`.

**The local parameters** at `P ∈ SG` (`ThetaVol.LocOk`'s canonical values, with `σ₀⁻¹ = Function.invFun σ₀`):
`sqP = σ₀⁻¹(√q_P)`; `psiP(y) = σ₀⁻¹ψ₀(red(q_P·y))` on `q_P⁻¹O_(P)`, `1` off it; `chiP = ν_P⁻¹` on the `P`-units
(read at `idAtE`), `0` off them; `muP = locChar(ν_P(q_P)⁻¹, chiP)`. They satisfy `LocOk` at `R = SG`, `ξ = 1`
(`locOk`) when each `q_P` is prime (A11), `xi0` is `P`-integral, and `√q_P` and the `q_P`-th roots of unity lie in
`σ₀(L)`.

**The Stage-U factors.** `xiU` is `ThetaVol.xiStd` with these parameters (`R = SG`, `h = 1`, `jS`, `phS`, depth
`m + 1`), and `xiTopU` is `ThetaVol.xiTop` with no places off `SG`. Both read the chain data `D` but not `D.Xi`.
-/

namespace ChainLocal

open NumberField IsDedekindDomain ThetaChain ThetaVol HermClasses

noncomputable section

/-! ## Reduction modulo `P` -/

section Reduction

variable {E : Type*} [Field E] [NumberField E] (Pl : HeightOneSpectrum (𝓞 E))

/-- **Every `P`-integral element has a lift to `O_E`**: some `y ∈ O_E` with `x − y ∈ P·O_(P)`. -/
theorem exists_lift {x : E} (hx : intAt Pl x) : ∃ y : 𝓞 E, inP Pl (x - y) := by
  obtain ⟨a, ha⟩ := Pl.exists_valuation_sub_lt_of_integer (K := E) hx 1
  exact ⟨a, by rw [inP, Valuation.map_sub_swap]; simpa using ha⟩

/-- **Elements of `O_E` congruent mod `P·O_(P)` are congruent mod `P`.** -/
theorem mk_eq_of_inP {y y' : 𝓞 E} (h : inP Pl ((y : E) - y')) :
    Ideal.Quotient.mk Pl.asIdeal y = Ideal.Quotient.mk Pl.asIdeal y' := by
  rw [Ideal.Quotient.eq, ← Pl.valuation_lt_one_iff_mem (K := E)]
  push_cast
  exact h

variable {Pl} in
/-- **`P·O_(P)` is closed under differences.** -/
theorem inP_sub {x y : E} (hx : inP Pl x) (hy : inP Pl y) : inP Pl (x - y) := by
  rw [sub_eq_add_neg]
  exact (Pl.valuation E).map_add_lt hx (by rw [Valuation.map_neg]; exact hy)

variable {Pl} in
/-- **`P·O_(P)` is an `O_(P)`-ideal.** -/
theorem inP_mul {x y : E} (hx : inP Pl x) (hy : intAt Pl y) : inP Pl (x * y) := by
  rw [inP, map_mul]
  calc Pl.valuation E x * Pl.valuation E y ≤ Pl.valuation E x * 1 := by gcongr; exact hy
    _ < 1 := by rwa [mul_one]

/-- **Elements of `O_E` are `P`-integral.** -/
theorem intAt_coe (y : 𝓞 E) : intAt Pl (y : E) := Pl.valuation_le_one y

variable {Pl} in
/-- **An element congruent to an element of `O_E` is `P`-integral.** -/
theorem intAt_of_inP {x : E} {y : 𝓞 E} (h : inP Pl (x - y)) : intAt Pl x := by
  have := (Pl.valuation E).map_add_le h.le (intAt_coe Pl y)
  rwa [sub_add_cancel] at this

open Classical in
/-- **The chosen lift** of `x` to `O_E`: some `y` with `x − y ∈ P·O_(P)`, `0` if there is none (`x` not
`P`-integral). -/
def liftP (x : E) : 𝓞 E := if h : ∃ y : 𝓞 E, inP Pl (x - y) then h.choose else 0

variable {Pl} in
/-- **The lift is congruent to `x`.** -/
theorem inP_liftP {x : E} (hx : intAt Pl x) : inP Pl (x - liftP Pl x) := by
  have h := exists_lift Pl hx
  rw [liftP, dite_eq_left h]
  exact h.choose_spec

variable {Pl} in
/-- **The lift is the lift mod `P`**: any `y ∈ O_E` congruent to `x` has the lift's residue. -/
theorem mk_liftP {x : E} {y : 𝓞 E} (hy : inP Pl (x - y)) :
    Ideal.Quotient.mk Pl.asIdeal (liftP Pl x) = Ideal.Quotient.mk Pl.asIdeal y := by
  apply mk_eq_of_inP
  have := inP_sub hy (inP_liftP (intAt_of_inP hy))
  rwa [sub_sub_sub_cancel_left] at this

/-- **The reduction** `O_(P) → O_E/P`, `x ↦ y mod P` for any `y ∈ O_E` with `x − y ∈ P·O_(P)` (`redP_eq`), on the
valuation subring `O_(P) = {x : v_P(x) ≤ 1}`. The residue map read by `psiP`; with it the archive's `red_w` of
`ThetaVol.IsRed` is a ring homomorphism. -/
def redP : (Pl.valuation E).integer →+* 𝓞 E ⧸ Pl.asIdeal where
  toFun x := Ideal.Quotient.mk Pl.asIdeal (liftP Pl x)
  map_one' := by
    rw [mk_liftP (y := 1) (by simp [inP])]
    rfl
  map_mul' x y := by
    rw [mk_liftP (y := liftP Pl x * liftP Pl y), map_mul]
    have e : ((x * y : (Pl.valuation E).integer) : E) - ((liftP Pl x * liftP Pl y : 𝓞 E) : E) =
        ((x : E) - liftP Pl x) * y + (liftP Pl x : E) * ((y : E) - liftP Pl y) := by
      push_cast
      ring
    rw [e]
    exact (Pl.valuation E).map_add_lt (inP_mul (inP_liftP x.2) y.2)
      (by rw [mul_comm]; exact inP_mul (inP_liftP y.2) (intAt_coe Pl _))
  map_zero' := by
    rw [mk_liftP (y := 0) (by simp [inP])]
    rfl
  map_add' x y := by
    rw [mk_liftP (y := liftP Pl x + liftP Pl y), map_add]
    have e : ((x + y : (Pl.valuation E).integer) : E) - ((liftP Pl x + liftP Pl y : 𝓞 E) : E) =
        ((x : E) - liftP Pl x) - -((y : E) - liftP Pl y) := by
      push_cast
      ring
    rw [e]
    exact inP_sub (inP_liftP x.2) (by rw [inP, Valuation.map_neg]; exact inP_liftP y.2)

variable {Pl} in
/-- **The reduction is the residue of any congruent element of `O_E`.** -/
theorem redP_eq {x : (Pl.valuation E).integer} {y : 𝓞 E} (h : inP Pl ((x : E) - y)) :
    redP Pl x = Ideal.Quotient.mk Pl.asIdeal y :=
  mk_liftP h

end Reduction

/-! ## Reduction of matrices -/

section RedMat

variable {E : Type*} [Field E] [NumberField E] (Pl : HeightOneSpectrum (𝓞 E)) {n : ℕ}

/-- **`GL_n(O_(P))` inside `GL_n(E)`.** -/
def toGL : GL (Fin n) (Pl.valuation E).integer →* GL (Fin n) E :=
  Units.map (Pl.valuation E).integer.subtype.mapMatrix.toMonoidHom

/-- **The reduction `GL_n(O_(P)) → GL_n(O_E/P)`** (`redP` entrywise). -/
def redGL : GL (Fin n) (Pl.valuation E).integer →* GL (Fin n) (𝓞 E ⧸ Pl.asIdeal) :=
  Units.map (redP Pl).mapMatrix.toMonoidHom

/-- **An integral matrix reduces to its reduction.** -/
theorem isRed_units (G : GL (Fin n) (Pl.valuation E).integer) :
    IsRed Pl (toGL Pl G : Matrix (Fin n) (Fin n) E) (redGL Pl G : Matrix (Fin n) (Fin n) (𝓞 E ⧸ Pl.asIdeal)) := by
  intro a b
  refine ⟨liftP Pl (G.val a b : E), ?_, ?_⟩
  · simp only [redGL, Units.coe_map]
    rfl
  · simpa [toGL] using inP_liftP (G.val a b).2

variable {Pl} in
/-- **Every reduction comes from `GL_n(O_(P))`**: `g` is integral and its determinant a `P`-unit, as its reduction
is invertible. -/
theorem exists_of_isRed {g : GL (Fin n) E} {gb : GL (Fin n) (𝓞 E ⧸ Pl.asIdeal)}
    (h : IsRed Pl (g : Matrix (Fin n) (Fin n) E) (gb : Matrix (Fin n) (Fin n) (𝓞 E ⧸ Pl.asIdeal))) :
    ∃ G, toGL Pl G = g ∧ redGL Pl G = gb := by
  choose y hy hP using h
  let A : Matrix (Fin n) (Fin n) (Pl.valuation E).integer :=
    fun a b => ⟨_, (Valuation.mem_integer_iff _ _).2 (intAt_of_inP (hP a b))⟩
  have hA : (Pl.valuation E).integer.subtype.mapMatrix A = g := rfl
  have hAb : (redP Pl).mapMatrix A = gb := by
    ext a b
    exact (redP_eq (hP a b)).trans (hy a b)
  have : Nontrivial (𝓞 E ⧸ Pl.asIdeal) := Ideal.Quotient.nontrivial_iff.2 Pl.isPrime.ne_top
  have hdet : IsUnit A.det := by
    refine (Valuation.integer.integers _).isUnit_of_one' (le_antisymm A.det.2 (not_lt.1 fun hlt => ?_))
    have hlt' : inP Pl (A.det : E) := hlt
    have h0 : redP Pl A.det = 0 := by
      rw [redP_eq (y := 0) (by simpa using hlt'), map_zero]
    rw [RingHom.map_det, hAb] at h0
    exact (Matrix.isUnits_det_units gb).ne_zero h0
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hdet
  exact ⟨G, Units.ext (by simp [toGL, hG, ← hA]), Units.ext (by simp [redGL, hG, ← hAb])⟩

end RedMat

/-! ## Ideles from their components; the single-place idele -/

section Idele

variable {E : Type*} [Field E] [NumberField E]

/-- **A family of components of an idele**: nonzero everywhere and `1` at almost every place. -/
def IsIdeleFam (x : HeightOneSpectrum (𝓞 E) → E) : Prop :=
  (∀ w, x w ≠ 0) ∧ {w | x w ≠ 1}.Finite

/-- **The components are almost everywhere integral**, with their inverses. -/
theorem IsIdeleFam.eventually {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) (k : ℤ) :
    ∀ᶠ w in Filter.cofinite, algebraMap E (w.adicCompletion E) (x w ^ k) ∈ w.adicCompletionIntegers E :=
  (Filter.eventually_cofinite.2 (by simpa using h.2)).mono fun w (hw : x w = 1) => by simp [hw]

/-- **The adeles with components `x` and `x⁻¹` are inverse.** -/
theorem IsIdeleFam.mul_inv {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) :
    (show FiniteAdeleRing (𝓞 E) E from ⟨fun w => algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)), h.eventually 1⟩) *
      (show FiniteAdeleRing (𝓞 E) E from
        ⟨fun w => algebraMap E (w.adicCompletion E) (x w ^ (-1 : ℤ)), h.eventually (-1)⟩) = 1 :=
  FiniteAdeleRing.ext E fun w => by
    change algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)) * algebraMap E (w.adicCompletion E) (x w ^ (-1 : ℤ)) = 1
    rw [← map_mul, zpow_one, zpow_neg_one, mul_inv_cancel₀ (h.1 w), map_one]

open Classical in
/-- **The idele with components `x`** (`ideleOf_apply`), `1` if `x` is not a family of components. -/
def ideleOf (x : HeightOneSpectrum (𝓞 E) → E) : Ideles E :=
  if h : IsIdeleFam x then Units.mkOfMulEqOne _ _ (IsIdeleFam.mul_inv h) else 1

/-- **The components of `ideleOf x`** are those of `x`. -/
theorem ideleOf_apply {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) (w : HeightOneSpectrum (𝓞 E)) :
    ((ideleOf x : Ideles E) : FiniteAdeleRing (𝓞 E) E) w = algebraMap E (w.adicCompletion E) (x w) := by
  rw [ideleOf, dite_eq_left h]
  change algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)) = _
  rw [zpow_one]

variable (Pl : HeightOneSpectrum (𝓞 E))

variable {Pl} in
/-- **An idele is determined by being single-place at `P` with a given component** (`ThetaVol.IsLocAt`). -/
theorem isLocAt_unique {a : E} {x y : Ideles E} (hx : IsLocAt Pl a x) (hy : IsLocAt Pl a y) : x = y := by
  refine Units.ext (FiniteAdeleRing.ext E fun w => ?_)
  by_cases hw : w = Pl
  · subst hw
    rw [hx.2, hy.2]
  · rw [hx.1 w hw, hy.1 w hw]

open Classical in
/-- **The single-place idele of `a ∈ E`** at `P`: the idele with components `a` at `P` and `1` elsewhere (`ideleOf`),
`1` at `a = 0` (where no idele has component `a`): the `x` of `ThetaVol.IsLocAt Pl a x` (`isLocAt_idAtE`,
`eq_idAtE`), at which `chiP` and `muP` read a character. -/
def idAtE (a : E) : Ideles E := ideleOf (Pi.mulSingle Pl a)

/-- **It is single-place at `P` with component `a`.** -/
theorem isLocAt_idAtE {a : E} (ha : a ≠ 0) : IsLocAt Pl a (idAtE Pl a) := by
  classical
  have h : IsIdeleFam (Pi.mulSingle Pl a) :=
    ⟨fun w => by by_cases hw : w = Pl <;> simp [hw, ha],
      (Set.finite_singleton Pl).subset fun w hw =>
        Classical.byContradiction fun h => hw (Pi.mulSingle_eq_of_ne (M := fun _ => E) h a)⟩
  exact ⟨fun w hw => by rw [idAtE, ideleOf_apply h, Pi.mulSingle_eq_of_ne hw, map_one],
    by rw [idAtE, ideleOf_apply h, Pi.mulSingle_eq_same]⟩

variable {Pl} in
/-- **It is the only such idele.** -/
theorem eq_idAtE {a : E} {x : Ideles E} (ha : a ≠ 0) (hx : IsLocAt Pl a x) : x = idAtE Pl a :=
  isLocAt_unique hx (isLocAt_idAtE Pl ha)

end Idele

/-! ## The residue character at a place of prime norm -/

section Psi0

variable {E : Type*} [Field E] [NumberField E] (xi0 : E) {Pl : HeightOneSpectrum (𝓞 E)}

/-- **The integers in `P` are the multiples of `q_P`** when `q_P = N(P)` is prime. -/
theorem dvd_of_mem (hq : (Ideal.absNorm Pl.asIdeal).Prime) {z : ℤ} (hz : (z : 𝓞 E) ∈ Pl.asIdeal) :
    (Ideal.absNorm Pl.asIdeal : ℤ) ∣ z := by
  by_contra h
  have hc : IsCoprime (Ideal.absNorm Pl.asIdeal : ℤ) z :=
    Int.isCoprime_iff_gcd_eq_one.2 ((hq.coprime_iff_not_dvd).2 fun h' => h (Int.natCast_dvd.2 h'))
  obtain ⟨a, b, hab⟩ := hc
  apply Pl.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  rw [← this]
  exact Pl.asIdeal.add_mem (Pl.asIdeal.mul_mem_left _ (Ideal.absNorm_mem _)) (Pl.asIdeal.mul_mem_left _ hz)

/-- **Every residue mod `P` is that of a natural number** when `q_P` is prime (`O_E/P = 𝔽_q`). -/
theorem exists_natCast (hq : (Ideal.absNorm Pl.asIdeal).Prime) (c : 𝓞 E ⧸ Pl.asIdeal) :
    ∃ b : ℕ, (b : 𝓞 E ⧸ Pl.asIdeal) = c := by
  have : Fact (Ideal.absNorm Pl.asIdeal).Prime := ⟨hq⟩
  have : Nontrivial (𝓞 E ⧸ Pl.asIdeal) := Ideal.Quotient.nontrivial_iff.2 Pl.isPrime.ne_top
  have hcard : Nat.card (𝓞 E ⧸ Pl.asIdeal) = Ideal.absNorm Pl.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hc := (zmultiples_eq_top_of_prime_card hcard one_ne_zero).symm ▸ AddSubgroup.mem_top c
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
  have hq0 : ((Ideal.absNorm Pl.asIdeal : ℤ) : 𝓞 E ⧸ Pl.asIdeal) = 0 := by
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk Pl.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  refine ⟨(z % Ideal.absNorm Pl.asIdeal).toNat, ?_⟩
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq.ne_zero)), zsmul_one,
    Int.emod_def, Int.cast_sub, Int.cast_mul, hq0, zero_mul, sub_zero]

variable {xi0} in
/-- **The least representative is a representative**: `resRep(c) ≡ xi0·c′ (mod P)` for a lift `c′` of `c`, when
`q_P` is prime and `xi0` is `P`-integral. -/
theorem resRep_spec (hq : (Ideal.absNorm Pl.asIdeal).Prime) (hxi : intAt Pl xi0) (c : 𝓞 E ⧸ Pl.asIdeal) :
    ∃ c' : 𝓞 E, Ideal.Quotient.mk Pl.asIdeal c' = c ∧ inP Pl ((resRep xi0 Pl c : E) - xi0 * c') := by
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  have hint : intAt Pl (xi0 * c') := by
    rw [intAt, map_mul]
    exact mul_le_one' hxi (intAt_coe Pl c')
  obtain ⟨y, hy⟩ := exists_lift Pl hint
  obtain ⟨b, hb⟩ := exists_natCast hq (Ideal.Quotient.mk Pl.asIdeal y)
  have hby : inP Pl ((b : E) - y) := by
    rw [← map_natCast (Ideal.Quotient.mk Pl.asIdeal), Ideal.Quotient.eq,
      ← Pl.valuation_lt_one_iff_mem (K := E)] at hb
    push_cast at hb
    exact hb
  have hb' := inP_sub hby hy
  rw [sub_sub_sub_cancel_right] at hb'
  exact Nat.sInf_mem (s := {b : ℕ | ∃ c'' : 𝓞 E, Ideal.Quotient.mk Pl.asIdeal c'' = Ideal.Quotient.mk Pl.asIdeal c' ∧
    Pl.valuation E ((b : E) - xi0 * c'') < 1}) ⟨b, c', rfl, hb'⟩

variable {xi0} in
/-- **`ψ₀` is additive** at a place of prime norm `q_P` where `xi0` is integral: the representatives of `c`, `c′`
and `c + c′` differ by a multiple of `q_P`. -/
theorem psi0_add (hq : (Ideal.absNorm Pl.asIdeal).Prime) (hxi : intAt Pl xi0) (c c' : 𝓞 E ⧸ Pl.asIdeal) :
    psi0 xi0 Pl (c + c') = psi0 xi0 Pl c * psi0 xi0 Pl c' := by
  obtain ⟨d, rfl, h⟩ := resRep_spec hq hxi c
  obtain ⟨d', rfl, h'⟩ := resRep_spec hq hxi c'
  obtain ⟨d'', hd'', h''⟩ := resRep_spec hq hxi (Ideal.Quotient.mk Pl.asIdeal d + Ideal.Quotient.mk Pl.asIdeal d')
  set r := resRep xi0 Pl (Ideal.Quotient.mk Pl.asIdeal d)
  set r' := resRep xi0 Pl (Ideal.Quotient.mk Pl.asIdeal d')
  set r'' := resRep xi0 Pl (Ideal.Quotient.mk Pl.asIdeal d + Ideal.Quotient.mk Pl.asIdeal d')
  have hdd : inP Pl (((d + d' - d'' : 𝓞 E) : E) * xi0) := by
    refine inP_mul ?_ hxi
    rw [inP, Pl.valuation_lt_one_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hd'', sub_self]
  have hz : (((r + r' : ℕ) - r'' : ℤ) : 𝓞 E) ∈ Pl.asIdeal := by
    rw [← Pl.valuation_lt_one_iff_mem (K := E)]
    have e : (((((r + r' : ℕ) - r'' : ℤ) : 𝓞 E)) : E) =
        ((r : E) - xi0 * d) + ((r' : E) - xi0 * d') - ((r'' : E) - xi0 * d'') + ((d + d' - d'' : 𝓞 E) : E) * xi0 := by
      push_cast
      ring
    have hv := (Pl.valuation E).map_add_lt (inP_sub ((Pl.valuation E).map_add_lt h h') h'') hdd
    rw [← e] at hv
    exact hv
  obtain ⟨k, hk⟩ := dvd_of_mem hq hz
  have hkC : (r'' : ℂ) = r + r' - (Ideal.absNorm Pl.asIdeal : ℂ) * k := by
    have := congrArg (Int.cast : ℤ → ℂ) hk
    push_cast at this
    linear_combination -this
  have hq0 : (Ideal.absNorm Pl.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp only [psi0, ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [hkC]
  field_simp
  push_cast
  ring

end Psi0

/-! ## The local parameters at `P ∈ SG` -/

section Params

variable {E L : Type*} [Field E] [NumberField E] [Field L] (σ₀ : L →+* ℂ) (xi0 : E) (ν : Ideles E →* Lˣ)
  (Pl : HeightOneSpectrum (𝓞 E))

/-- **`sq_P = σ₀⁻¹(√q_P)`**, `q_P = N(P)` (the positive root; `sqP_sq` when `√q_P ∈ σ₀(L)`). -/
def sqP : L := Function.invFun σ₀ (Real.sqrt (Ideal.absNorm Pl.asIdeal) : ℂ)

open Classical in
/-- **The additive character `ψ_P`** at `P ∈ SG`: `ψ_P(y) = σ₀⁻¹(ψ₀(red(q_P·y)))` on `q_P⁻¹·O_(P)` (`redP`, and
`ψ₀ = ThetaChain.psi0 xi0`, the residue character of step 0), `1` off it: `ThetaVol.LocOk`'s values at `SG`. -/
def psiP (y : E) : L :=
  if h : intAt Pl (qP Pl * y) then
    Function.invFun σ₀ (psi0 xi0 Pl (redP Pl ⟨qP Pl * y, (Valuation.mem_integer_iff _ _).2 h⟩))
  else 1

open Classical in
/-- **The residue character `χ_P = ν_P⁻¹`** at `P ∈ SG` for a character `ν` of the ideles (the lift character
`μ_{0,j}`): `χ_P(a) = ν(a at P)⁻¹` on the `P`-units, `0` off them (`ThetaVol.ChiOk`). -/
def chiP (a : E) : L := if Pl.valuation E a = 1 then ((ν (idAtE Pl a) : Lˣ) : L)⁻¹ else 0

/-- **The local character `μ_P = locChar(ν_P(q_P)⁻¹, χ_P)`** at `P ∈ SG` (Stage U: no twist `ξ`), i.e.
`μ_P(a) = ν_P(q_P)^{−v(a)}·χ_P(a/q_P^{v(a)})`: `ThetaVol.LocOk`'s `μ` at `SG`. -/
def muP : E → L := locChar Pl ((ν (idAtE Pl (qP Pl)) : Lˣ) : L)⁻¹ (chiP ν Pl)

variable {σ₀} in
/-- **`σ₀⁻¹` is multiplicative on `σ₀(L)`.** -/
theorem invFun_mul {a b : ℂ} (ha : a ∈ Set.range σ₀) (hb : b ∈ Set.range σ₀) :
    Function.invFun σ₀ (a * b) = Function.invFun σ₀ a * Function.invFun σ₀ b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [← map_mul, Function.leftInverse_invFun σ₀.injective (a * b), Function.leftInverse_invFun σ₀.injective a,
    Function.leftInverse_invFun σ₀.injective b]

/-- **`q_P ≠ 0` in `E`.** -/
theorem qP_ne_zero : qP Pl ≠ 0 :=
  Nat.cast_ne_zero.2 fun h => Pl.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

/-- **`q_P ∈ P`.** -/
theorem inP_qP : inP Pl (qP Pl) := by
  have := (Pl.valuation_lt_one_iff_mem (K := E) _).2 (Ideal.absNorm_mem Pl.asIdeal)
  rw [inP, qP]
  simpa using this

/-- **`ψ₀(0) = 1`**: the least representative of `0` is `0`. -/
theorem psi0_zero : psi0 xi0 Pl 0 = 1 := by
  have h : resRep xi0 Pl 0 = 0 := Nat.sInf_eq_zero.2 (Or.inl ⟨0, by simp⟩)
  simp [psi0, h]

variable {σ₀ Pl} in
/-- **`sq_P² = q_P`** when `√q_P ∈ σ₀(L)`. -/
theorem sqP_sq (h : (Real.sqrt (Ideal.absNorm Pl.asIdeal) : ℂ) ∈ Set.range σ₀) :
    sqP σ₀ Pl ^ 2 = (Ideal.absNorm Pl.asIdeal : L) := by
  apply σ₀.injective
  rw [map_pow, sqP, Function.invFun_eq h, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

/-- **`ψ_P` is trivial on `O_(P)`**: `q_P·y ∈ P·O_(P)` reduces to `0`. -/
theorem psiP_of_intAt {y : E} (hy : intAt Pl y) : psiP σ₀ xi0 Pl y = 1 := by
  have h : inP Pl (qP Pl * y) := inP_mul (inP_qP Pl) hy
  rw [psiP, dite_eq_left (show intAt Pl (qP Pl * y) from h.le), redP_eq (y := 0) (by simpa using h), map_zero,
    psi0_zero]
  simpa using Function.leftInverse_invFun σ₀.injective 1

variable {σ₀ xi0 Pl} in
/-- **`ψ_P(y/q_P) = σ₀⁻¹ψ₀(y mod P)`** for `y ∈ O_E`, when `ψ₀`'s values lie in `σ₀(L)`. -/
theorem psiP_div (hψ : ∀ c, psi0 xi0 Pl c ∈ Set.range σ₀) (y : 𝓞 E) :
    σ₀ (psiP σ₀ xi0 Pl ((y : E) / qP Pl)) = psi0 xi0 Pl (Ideal.Quotient.mk Pl.asIdeal y) := by
  have e : qP Pl * ((y : E) / qP Pl) = y := mul_div_cancel₀ _ (qP_ne_zero Pl)
  have h : intAt Pl (qP Pl * ((y : E) / qP Pl)) := by rw [e]; exact intAt_coe Pl y
  rw [psiP, dite_eq_left h, redP_eq (y := y) (by simp [e, inP]), Function.invFun_eq (hψ _)]

variable {σ₀ xi0 Pl} in
/-- **`ψ_P` is additive on `q_P⁻¹·O_(P)`** when `ψ₀` is additive with values in `σ₀(L)`. -/
theorem psiP_add (hψ : ∀ c, psi0 xi0 Pl c ∈ Set.range σ₀)
    (hadd : ∀ c c', psi0 xi0 Pl (c + c') = psi0 xi0 Pl c * psi0 xi0 Pl c') {y z : E} (hy : intAt Pl (qP Pl * y))
    (hz : intAt Pl (qP Pl * z)) : psiP σ₀ xi0 Pl (y + z) = psiP σ₀ xi0 Pl y * psiP σ₀ xi0 Pl z := by
  have h : intAt Pl (qP Pl * (y + z)) := by
    rw [mul_add]
    exact (Pl.valuation E).map_add_le hy hz
  have e : (⟨qP Pl * (y + z), (Valuation.mem_integer_iff _ _).2 h⟩ : (Pl.valuation E).integer) =
      ⟨qP Pl * y, (Valuation.mem_integer_iff _ _).2 hy⟩ + ⟨qP Pl * z, (Valuation.mem_integer_iff _ _).2 hz⟩ :=
    Subtype.ext (mul_add _ _ _)
  rw [psiP, psiP, psiP, dite_eq_left h, dite_eq_left hy, dite_eq_left hz, e, map_add, hadd,
    invFun_mul (hψ _) (hψ _)]

variable {Pl} in
/-- **`χ_P = ν_P⁻¹` on the `P`-units, `0` off them** (`ThetaVol.ChiOk`). -/
theorem chiOk_chiP : ChiOk Pl ν (chiP ν Pl) := by
  intro a
  refine ⟨fun ha x hx => ?_, fun ha => by rw [chiP, ite_eq_right ha]⟩
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [chiP, ite_eq_left ha, ← eq_idAtE ha0 hx]

/-- **The local parameters at `SG` realise `ThetaVol.LocOk`** at Stage U (`R = SG`, `ξ = 1`), for every `dQ`, when at
each `P ∈ SG` the norm `q_P` is prime (A11), `xi0` is `P`-integral, and `√q_P` and the values of `ψ₀` (`q_P`-th roots
of unity) lie in `σ₀(L)` (facts of the coefficient field). -/
theorem locOk (dQ : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (hq : ∀ Pl ∈ SG, (Ideal.absNorm Pl.asIdeal).Prime) (hxi : ∀ Pl ∈ SG, intAt Pl xi0)
    (hsq : ∀ Pl ∈ SG, (Real.sqrt (Ideal.absNorm Pl.asIdeal) : ℂ) ∈ Set.range σ₀)
    (hψ : ∀ Pl ∈ SG, ∀ c, psi0 xi0 Pl c ∈ Set.range σ₀) :
    LocOk σ₀ xi0 dQ SG SG ν 1 (psiP σ₀ xi0) (muP ν) (sqP σ₀) (chiP ν) := by
  intro Pl hPl
  refine ⟨sqP_sq (hsq Pl hPl), fun y z => psiP_add (hψ Pl hPl) (psi0_add (hq Pl hPl) (hxi Pl hPl)),
    fun y => psiP_of_intAt σ₀ xi0 Pl, fun _ => ⟨psiP_div (hψ Pl hPl), fun y hy => by rw [psiP, dite_eq_right hy]⟩,
    fun h => absurd hPl h, ?_, ⟨_, rfl, fun x hx => ?_⟩⟩
  · rw [ite_eq_left hPl]
    exact chiOk_chiP ν
  · rw [← eq_idAtE (qP_ne_zero Pl) hx]
    simp

end Params

/-! ## The level groups at `SG` -/

section Levels

variable {E : Type*} [Field E] [NumberField E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

/-- **The level group at `SG`** of a step of size `n + c` with groups `J_w` (`h = 1`):
`∏_{w ∈ SG} red_w(prX(R1 ∩ J_w))`, the `ḡ` whose component at every `w ∈ SG` is the reduction (`ThetaVol.IsRed`) of
the block `A(r)` of some `r ∈ R1 ∩ J_w`. Written as the closure of that set, which is a group, so the closure adds
nothing (`levG_spec`). -/
def levG (n c : ℕ) (J : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n + c)) E)) :
    Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :=
  Subgroup.closure {gb | ∀ w : SG, ∃ g ∈ prX n c (R1 n c ⊓ J w.1),
    IsRed w.1 (g : Matrix (Fin n) (Fin n) E) (gb w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))}

/-- **The reductions are in the level group** (the easy half of `ThetaVol.LevGOk`). -/
theorem mem_levG {n c : ℕ} {J : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n + c)) E)}
    {gb : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)}
    (h : ∀ w : SG, ∃ g ∈ prX n c (R1 n c ⊓ J w.1),
      IsRed w.1 (g : Matrix (Fin n) (Fin n) E) (gb w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))) :
    gb ∈ levG n c J :=
  Subgroup.subset_closure h

/-- **The level group is `∏_w red_w(prX(R1 ∩ J_w))`** (`ThetaVol.LevGOk`): that set is a group, as products and
inverses of reductions are reductions (`toGL`, `redGL` are homomorphisms). -/
theorem levG_spec (n c : ℕ) (J : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n + c)) E)) :
    LevGOk n c J (levG (SG := SG) n c J) := by
  intro gb
  refine ⟨fun h => ?_, mem_levG⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro w
    refine ⟨1, one_mem _, ?_⟩
    simpa using isRed_units w.1 (n := n) 1
  | mul x y _ _ hx hy =>
    intro w
    obtain ⟨g, hg, hr⟩ := hx w
    obtain ⟨g', hg', hr'⟩ := hy w
    obtain ⟨G, rfl, hG⟩ := exists_of_isRed hr
    obtain ⟨G', rfl, hG'⟩ := exists_of_isRed hr'
    refine ⟨_, mul_mem hg hg', ?_⟩
    rw [Pi.mul_apply, ← hG, ← hG', ← map_mul, ← map_mul]
    exact isRed_units w.1 (G * G')
  | inv x _ hx =>
    intro w
    obtain ⟨g, hg, hr⟩ := hx w
    obtain ⟨G, rfl, hG⟩ := exists_of_isRed hr
    refine ⟨_, inv_mem hg, ?_⟩
    rw [Pi.inv_apply, ← hG, ← map_inv, ← map_inv]
    exact isRed_units w.1 G⁻¹

variable (SG) in
/-- **The level group of step `j` at `SG`** (Stage U: one index, `h = 1`) for ranks `n j`, length `m` and the sharp
parameters `k`, `t`: `uniUT` at `j = 0` (`ChIdx.zero_grp`), and `levG` with the sharp group
`JGsym(k, m/2 − 1, k + m − 1, t)` at size `n j + (m − 1 − j)` at `j ≥ 1`, i.e. `ThetaVol.jS` read on ranks `n`.
The chain's `Λ j` is its product with `⊤` at `Q = ∅`. -/
def levU (n : ℕ → ℕ) (m k t j : ℕ) : Subgroup (∀ w : SG, GL (Fin (n j)) (𝓞 E ⧸ w.1.asIdeal)) := by
  classical
  exact if j = 0 then uniUT SG (n j) else
    levG (n j) (m - 1 - j) fun Pl => JGsym (n j) (m - 1 - j) Pl k (m / 2 - 1) (k + m - 1) t

/-- **Step 0 has the upper unitriangular group.** -/
theorem levU_zero (n : ℕ → ℕ) (m k t : ℕ) : levU SG n m k t 0 = uniUT SG (n 0) := by
  simp [levU]

/-- **The later steps have the sharp group**, `ThetaVol.jS` read on ranks `n`. -/
theorem levU_of_ne_zero (n : ℕ → ℕ) (m k t : ℕ) {j : ℕ} (hj : j ≠ 0) :
    levU SG n m k t j = levG (n j) (m - 1 - j) fun Pl => JGsym (n j) (m - 1 - j) Pl k (m / 2 - 1) (k + m - 1) t := by
  simp [levU, hj]

end Levels

/-! ## The Stage-U local factors -/

section StageU

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {τ : Φ → (E →+* L)}

/-- **The local factor `Ξ_j(c, c′)` of a generic step at Stage U** (`Q = ∅`): `ThetaVol.xiStd` with the row set
`R = SG`, the representatives `h = 1`, the sharp groups `jS` and shapes `phS`, the depth `A = m + 1`, and at each
`P ∈ SG` the parameters `psiP`, `sqP`, `chiP`, `muP` of the step's lift character `μ_{0,j} = D.mu j` (with `σ₀ =
D.P.σ₀`). It reads `D` only through its ranks, places, classes and characters, not `D.Xi`, so the Stage-U data take
`Xi := xiU D₀ …` for `D₀` the data with any `Xi`. The coupled factor of step `m − 2` is the same: `xiCpl` with
`Q \ SG = ∅`. -/
def xiU (D : Data τ) (m k t : ℕ) (xi0 : E) (j : ℕ) (c : Cls D.n D.ST D.SG D.Q D.β D.Λ j)
    (c' : Cls D.n D.ST D.SG D.Q D.β D.Λ (j + 1)) : Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E → L :=
  xiStd D m (m + 1) k D.SG (fun _ _ _ => 1) (jS D m k t) (fun _ => psiP D.P.σ₀ xi0)
    (fun l => muP (D.mu l).toHom) (fun _ => sqP D.P.σ₀)
    (phS D m k t (fun _ => psiP D.P.σ₀ xi0) fun l => chiP (D.mu l).toHom) j c c'

/-- **The top factor at Stage U** (chain length `m2 + 2`): `ThetaVol.xiTop` at `j = m2 + 1` with no places off `SG`
(`R = ∅`, so no coset `ȳ`), the parameters of `xiU`, the target `d′` (the row point's lift `tilQ`), its frames `frd`
and `π = conj(tz)`. -/
def xiTopU (D : Data τ) (m2 k t : ℕ) (xi0 : E) {SF : Finset (HeightOneSpectrum (𝓞 E))}
    (c : Cls D.n D.ST D.SG D.Q D.β D.Λ (m2 + 1)) (d' : Deco E (D.n (m2 + 2)) D.ST SF)
    (frd : HeightOneSpectrum (𝓞 E) → Matrix (Fin (D.n (m2 + 2) - 1)) (Fin (D.n (m2 + 2) - 1)) E) (π : E) :
    Matrix (Fin (D.n (m2 + 2))) (Fin (D.n (m2 + 1))) E → L :=
  xiTop D (m2 + 2) k t ∅ (fun _ => psiP D.P.σ₀ xi0) (fun l => chiP (D.mu l).toHom) (m2 + 1) c d' frd π
    fun P => absurd P.2 (Finset.notMem_empty P.1)

end StageU

end

end ChainLocal
