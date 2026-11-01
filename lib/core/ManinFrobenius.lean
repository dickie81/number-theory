/-
# The Frobenius of Manin's twist: a similitude of the lattice

Plain statement. Let `𝔽_q` be a finite field of characteristic not `2`, `f = x³ + a₂x² + a₄x + a₆` with nonzero
discriminant, and `E'` Manin's twist `y² = x³ + a₂sx² + a₄s²x + a₆s³` of `y² = f(x)` over `𝔽_q(t)`, `s = f(t)`. For a
point `P` of `E'` let `deg P` be the degree of the rational function `x(P)/s`, a quadratic form on the points of `E'`
(`ManinTwist`), and `B` its polar form. There is an additive map `φ` from the points of `E'` to themselves with
(`frobenius_similitude`):
* `deg φ(P) = q·deg P` for every point `P`, so `B(φP, φR) = q·B(P, R)`: `φ` is a similitude of factor `q`;
* `φ^k(P₀) = P_k`: the Frobenius points `P_k` of `ManinLattice` are the orbit of `P₀ = (st, s²)`.

So `B(P_{j+d}, P_j) = q^j·B(P_d, P_0)` by the similitude alone (`gram_orbit`). For an elliptic curve `E` over `𝔽_q`
and `L_d` a field of `q^d` elements, `B(φ^{j+d}P₀, φ^jP₀) = q^j(q^d + 1 − #E(L_d))` for `d ≥ 1`
(`gram_orbit_card`). Separately, a similitude of factor `q` of a positive-definite Hermitian form has every eigenvalue
on `|α|² = q` (`normSq_eq_of_similitude`).

This is the function-field case of the sixth of the first steps in `docs/ball-conjecture.md`: the point counts of an
elliptic curve are the Gram kernel of an orbit of a similitude of an integral lattice, the points of the twist with
their degrees. The last theorem is how such a lattice gives the Riemann hypothesis.
* `φ` is the substitution `t ↦ t^q` (`frobRat`, `RatFunc.mapRingHom` of `expand`), which fixes `𝔽_q`, sends `s` to
  `s^q` and multiplies degrees by `q` (`rdeg_frobRat`, from `rdeg_expand`), applied to the coordinates (`mapPt`, to the
  twist by `s^q`), followed by the scaling `(x, y) ↦ (x/u², y/u³)` with `u = s^{(q−1)/2}`, from the twist by
  `s^q = s·u²` back to `E'` (`scalePt`).
* Both maps are additive: the slope and the coordinates of a sum commute with ring maps (Mathlib's `map_slope`,
  `map_addX`, `map_addY`) and scale by `1/u`, `1/u²` and `1/u³` (`slope_scale`, `addX_scale`, `addY_scale`).
* `φ(P_k) = P_{k+1}` (`frob_Pk`): `t^{q^k}` goes to `t^{q^{k+1}}`, and the exponent `(q^k + 3)/2` of `s` in `y`
  becomes `q(q^k + 3)/2 − 3(q − 1)/2 = (q^{k+1} + 3)/2`.
-/
import Mathlib
import ManinLattice

open Polynomial ManinDegree WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace ManinHasse

/-! ## Points along a ring map -/

section mapPt

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L] (W : WeierstrassCurve K) (f : K →+* L)

/-- The points of `W` carried along a ring map `f` to the points of `W.map f`. -/
def mapPt : W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).2 h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2]
      exact (Point.add_of_Y_eq (congr_arg f hxy.1) (by rw [hxy.2]; exact (W.toAffine.map_negY f x₂ y₂).symm)).symm
    · rw [Point.add_some hxy]
      have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := fun h =>
        hxy ⟨f.injective h.1, f.injective (by rw [h.2]; exact W.toAffine.map_negY f x₂ y₂)⟩
      rw [Point.add_some hxy']
      simp only [Point.some.injEq]
      rw [W.toAffine.map_slope f, W.toAffine.map_addX, W.toAffine.map_addY]
      exact ⟨rfl, rfl⟩

lemma mapPt_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    mapPt W f (.some x y h) = .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).2 h) := rfl

end mapPt

/-! ## The scaling `(x, y) ↦ (x/u², y/u³)` -/

section scale

variable {K : Type*} [Field K]

/-- `W₂` is `W₁` under `(x, y) ↦ (x/u², y/u³)`, both with `a₁ = a₃ = 0`. -/
structure IsScale (W₁ W₂ : WeierstrassCurve K) (u : K) : Prop where
  ne : u ≠ 0
  a₁ : W₁.a₁ = 0
  a₃ : W₁.a₃ = 0
  a₁' : W₂.a₁ = 0
  a₃' : W₂.a₃ = 0
  a₂ : W₂.a₂ * u ^ 2 = W₁.a₂
  a₄ : W₂.a₄ * u ^ 4 = W₁.a₄
  a₆ : W₂.a₆ * u ^ 6 = W₁.a₆

variable {W₁ W₂ : WeierstrassCurve K} {u : K} (hs : IsScale W₁ W₂ u)
include hs

lemma nonsingular_scale (x y : K) :
    W₂.toAffine.Nonsingular (x / u ^ 2) (y / u ^ 3) ↔ W₁.toAffine.Nonsingular x y := by
  have hu := hs.ne
  rw [nonsingular_iff', nonsingular_iff', equation_iff, equation_iff, hs.a₁, hs.a₃, hs.a₁', hs.a₃',
    ← hs.a₂, ← hs.a₄, ← hs.a₆]
  simp only [zero_mul, add_zero, zero_sub, neg_ne_zero]
  have e1 : (y / u ^ 3) ^ 2 = (x / u ^ 2) ^ 3 + W₂.a₂ * (x / u ^ 2) ^ 2 + W₂.a₄ * (x / u ^ 2) + W₂.a₆ ↔
      y ^ 2 = x ^ 3 + W₂.a₂ * u ^ 2 * x ^ 2 + W₂.a₄ * u ^ 4 * x + W₂.a₆ * u ^ 6 := by
    rw [← sub_eq_zero, ← sub_eq_zero (a := y ^ 2)]
    have e : (y / u ^ 3) ^ 2 - ((x / u ^ 2) ^ 3 + W₂.a₂ * (x / u ^ 2) ^ 2 + W₂.a₄ * (x / u ^ 2) + W₂.a₆) =
        (y ^ 2 - (x ^ 3 + W₂.a₂ * u ^ 2 * x ^ 2 + W₂.a₄ * u ^ 4 * x + W₂.a₆ * u ^ 6)) / u ^ 6 := by
      field_simp
    rw [e, div_eq_zero_iff, or_iff_left (pow_ne_zero 6 hu)]
  have e2 : 3 * (x / u ^ 2) ^ 2 + 2 * W₂.a₂ * (x / u ^ 2) + W₂.a₄ ≠ 0 ↔
      3 * x ^ 2 + 2 * (W₂.a₂ * u ^ 2) * x + W₂.a₄ * u ^ 4 ≠ 0 := by
    have e : 3 * (x / u ^ 2) ^ 2 + 2 * W₂.a₂ * (x / u ^ 2) + W₂.a₄ =
        (3 * x ^ 2 + 2 * (W₂.a₂ * u ^ 2) * x + W₂.a₄ * u ^ 4) / u ^ 4 := by
      field_simp
    rw [e, div_ne_zero_iff, and_iff_left (pow_ne_zero 4 hu)]
  have e3 : 2 * (y / u ^ 3) ≠ 0 ↔ 2 * y ≠ 0 := by
    rw [mul_div_assoc', div_ne_zero_iff, and_iff_left (pow_ne_zero 3 hu)]
  exact e1.and (e2.or e3)

lemma negY_scale (x y : K) : W₂.toAffine.negY (x / u ^ 2) (y / u ^ 3) = W₁.toAffine.negY x y / u ^ 3 := by
  simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃']
  ring

lemma addX_scale (x₁ x₂ ℓ : K) :
    W₂.toAffine.addX (x₁ / u ^ 2) (x₂ / u ^ 2) (ℓ / u) = W₁.toAffine.addX x₁ x₂ ℓ / u ^ 2 := by
  have hu := hs.ne
  simp only [addX, hs.a₁, hs.a₁', ← hs.a₂]
  field_simp
  ring

lemma addY_scale (x₁ x₂ y₁ ℓ : K) :
    W₂.toAffine.addY (x₁ / u ^ 2) (x₂ / u ^ 2) (y₁ / u ^ 3) (ℓ / u) = W₁.toAffine.addY x₁ x₂ y₁ ℓ / u ^ 3 := by
  have hu := hs.ne
  simp only [addY, negAddY, addX, negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃', ← hs.a₂]
  field_simp
  ring

variable [DecidableEq K]

lemma slope_scale (x₁ x₂ y₁ y₂ : K) :
    W₂.toAffine.slope (x₁ / u ^ 2) (x₂ / u ^ 2) (y₁ / u ^ 3) (y₂ / u ^ 3) = W₁.toAffine.slope x₁ x₂ y₁ y₂ / u := by
  have hu := hs.ne
  have hinj2 : ∀ a b : K, a / u ^ 2 = b / u ^ 2 ↔ a = b := fun a b => div_left_inj' (pow_ne_zero 2 hu)
  have hinj3 : ∀ a b : K, a / u ^ 3 = b / u ^ 3 ↔ a = b := fun a b => div_left_inj' (pow_ne_zero 3 hu)
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W₁.toAffine.negY x₂ y₂
    · rw [slope_of_Y_eq ((hinj2 _ _).2 hx) (by rw [negY_scale hs, hinj3]; exact hy), slope_of_Y_eq hx hy,
        zero_div]
    · have hy' : y₁ / u ^ 3 ≠ W₂.toAffine.negY (x₂ / u ^ 2) (y₂ / u ^ 3) := by
        rw [negY_scale hs, Ne, hinj3]
        exact hy
      rw [slope_of_Y_ne ((hinj2 _ _).2 hx) hy', slope_of_Y_ne hx hy]
      have key : ∀ A A' D D' : K, A' = A / u ^ 4 → D' = D / u ^ 3 → A' / D' = A / D / u := by
        rintro A A' D D' rfl rfl
        rcases eq_or_ne D 0 with rfl | hD
        · simp
        · field_simp
      refine key _ _ _ _ ?_ ?_
      · simp only [hs.a₁, hs.a₁', ← hs.a₂, ← hs.a₄]
        field_simp
        ring
      · simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃']
        field_simp
        ring
  · rw [slope_of_X_ne (fun h => hx ((hinj2 _ _).1 h)), slope_of_X_ne hx]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    field_simp

/-- **The scaling is additive**: `(x, y) ↦ (x/u², y/u³)` from the points of `W₁` to those of `W₂`. -/
def scalePt : W₁.toAffine.Point →+ W₂.toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (x / u ^ 2) (y / u ^ 3) ((nonsingular_scale hs x y).2 h)
  map_zero' := rfl
  map_add' := by
    have hu := hs.ne
    have hinj2 : ∀ a b : K, a / u ^ 2 = b / u ^ 2 ↔ a = b := fun a b => div_left_inj' (pow_ne_zero 2 hu)
    have hinj3 : ∀ a b : K, a / u ^ 3 = b / u ^ 3 ↔ a = b := fun a b => div_left_inj' (pow_ne_zero 3 hu)
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W₁.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2]
      exact (Point.add_of_Y_eq ((hinj2 _ _).2 hxy.1) (by rw [negY_scale hs, hinj3]; exact hxy.2)).symm
    · rw [Point.add_some hxy]
      have hxy' : ¬(x₁ / u ^ 2 = x₂ / u ^ 2 ∧ y₁ / u ^ 3 = W₂.toAffine.negY (x₂ / u ^ 2) (y₂ / u ^ 3)) := fun h =>
        hxy ⟨(hinj2 _ _).1 h.1, (hinj3 _ _).1 (by rw [h.2, negY_scale hs])⟩
      rw [Point.add_some hxy']
      simp only [Point.some.injEq]
      rw [slope_scale hs, addX_scale hs, addY_scale hs]
      exact ⟨rfl, rfl⟩

lemma scalePt_some {x y : K} (h : W₁.toAffine.Nonsingular x y) :
    scalePt hs (.some x y h) = .some (x / u ^ 2) (y / u ^ 3) ((nonsingular_scale hs x y).2 h) := rfl

end scale

/-! ## The substitution `t ↦ t^q` -/

section frob

variable {F : Type*} [Field F] [Fintype F]

local notation "ι" => algebraMap F[X] (RatFunc F)

lemma expand_le_nonZeroDivisors :
    nonZeroDivisors F[X] ≤ (nonZeroDivisors F[X]).comap (expand F (Fintype.card F)) := fun p hp => by
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, Ne, expand_eq_zero Fintype.card_pos]
  exact mem_nonZeroDivisors_iff_ne_zero.1 hp

/-- **The substitution `t ↦ t^q`** on `𝔽_q(t)`. -/
def frobRat : RatFunc F →+* RatFunc F := RatFunc.mapRingHom (expand F (Fintype.card F)) expand_le_nonZeroDivisors

lemma frobRat_div (p r : F[X]) :
    frobRat (ι p / ι r) = ι (expand F (Fintype.card F) p) / ι (expand F (Fintype.card F) r) := by
  unfold frobRat
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]

lemma frobRat_ι (p : F[X]) : frobRat (ι p) = ι (expand F (Fintype.card F) p) := by
  simpa only [map_one, div_one] using frobRat_div (F := F) p 1

/-- **The substitution multiplies degrees by `q`.** -/
lemma rdeg_frobRat (z : RatFunc F) : rdeg (frobRat z) = Fintype.card F * rdeg z := by
  have hz : z = ι z.num / ι z.denom := (RatFunc.num_div_denom z).symm
  conv_lhs => rw [hz]
  rw [frobRat_div, rdeg_expand Fintype.card_pos (RatFunc.denom_ne_zero z), ← hz]

variable {a₂ a₄ a₆ : F}

lemma frobRat_sf : frobRat (sf a₂ a₄ a₆) = sf a₂ a₄ a₆ ^ Fintype.card F := by
  rw [sf, frobRat_ι, ← map_pow, ← FiniteField.Polynomial.expand_card]

lemma frobRat_C (c : F) : frobRat (ι (C c)) = ι (C c) := by rw [frobRat_ι, expand_C]

lemma frobRat_X_pow (n : ℕ) : frobRat (ι X ^ n) = ι X ^ (Fintype.card F * n) := by
  rw [map_pow, frobRat_ι, expand_X, map_pow, ← pow_mul]

/-- The scaling data from the twist by `s^q` back to the twist by `s`, with `u = s^{(q−1)/2}`. -/
lemma isScale_frob (hF : ringChar F ≠ 2) :
    IsScale ((twist a₂ a₄ a₆).map frobRat) (twist a₂ a₄ a₆) (sf a₂ a₄ a₆ ^ (Fintype.card F / 2)) := by
  have hs := sf_ne_zero a₂ a₄ a₆
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = 2 * m + 1 :=
    ⟨Fintype.card F / 2, by have := card_pow_odd (F := F) hF 1; rw [pow_one] at this; omega⟩
  have hdiv : Fintype.card F / 2 = m := by omega
  rw [hdiv]
  refine ⟨pow_ne_zero _ hs, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [twist]
  · simp [twist]
  · simp only [twist, WeierstrassCurve.map_a₂, map_mul, frobRat_C, frobRat_sf, hm]
    ring
  · simp only [twist, WeierstrassCurve.map_a₄, map_mul, map_pow, frobRat_C, frobRat_sf, hm]
    ring
  · simp only [twist, WeierstrassCurve.map_a₆, map_mul, map_pow, frobRat_C, frobRat_sf, hm]
    ring

variable [DecidableEq (RatFunc F)]

/-- **The Frobenius of the twist**: `t ↦ t^q` on the coordinates, then `(x, y) ↦ (x/u², y/u³)`, `u = s^{(q−1)/2}`. -/
def frob (hF : ringChar F ≠ 2) : (twist a₂ a₄ a₆).toAffine.Point →+ (twist a₂ a₄ a₆).toAffine.Point :=
  (scalePt (isScale_frob hF)).comp (mapPt (twist a₂ a₄ a₆) frobRat)

/-- **The Frobenius multiplies degrees by `q`.** -/
lemma pdeg_frob (hF : ringChar F ≠ 2) (P : (twist a₂ a₄ a₆).toAffine.Point) :
    pdeg a₂ a₄ a₆ (frob hF P) = Fintype.card F * pdeg a₂ a₄ a₆ P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · have hs := sf_ne_zero a₂ a₄ a₆
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = 2 * m + 1 :=
      ⟨Fintype.card F / 2, by have := card_pow_odd (F := F) hF 1; rw [pow_one] at this; omega⟩
    have hdiv : Fintype.card F / 2 = m := by omega
    show rdeg (frobRat x / (sf a₂ a₄ a₆ ^ (Fintype.card F / 2)) ^ 2 / sf a₂ a₄ a₆) =
      Fintype.card F * rdeg (x / sf a₂ a₄ a₆)
    have e : frobRat x / (sf a₂ a₄ a₆ ^ (Fintype.card F / 2)) ^ 2 / sf a₂ a₄ a₆ = frobRat (x / sf a₂ a₄ a₆) := by
      rw [map_div₀, frobRat_sf, hdiv, hm]
      field_simp
      ring
    rw [e, rdeg_frobRat]

/-- **The Frobenius sends `P_k` to `P_{k+1}`.** -/
lemma frob_Pk (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (n : ℕ) : frob hF (Pk hF hD n) = Pk hF hD (n + 1) := by
  have hs := sf_ne_zero a₂ a₄ a₆
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = 2 * m + 1 :=
    ⟨Fintype.card F / 2, by have := card_pow_odd (F := F) hF 1; rw [pow_one] at this; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F ^ n = 2 * k + 1 := ⟨_, (Nat.div_add_mod _ 2).symm.trans (by
    rw [card_pow_odd hF n])⟩
  have hdiv : Fintype.card F / 2 = m := by omega
  have hkd : Fintype.card F ^ n / 2 = k := by omega
  have hsucc : Fintype.card F ^ (n + 1) = Fintype.card F * Fintype.card F ^ n := by rw [pow_succ, mul_comm]
  have hk1 : Fintype.card F ^ (n + 1) / 2 = (2 * m + 1) * k + m := by
    rw [hsucc, hk, hm]
    have : (2 * m + 1) * (2 * k + 1) = 2 * ((2 * m + 1) * k + m) + 1 := by ring
    omega
  simp only [frob, Pk, AddMonoidHom.coe_comp, Function.comp_apply, mapPt_some, scalePt_some, Point.some.injEq]
  constructor
  · rw [map_mul, frobRat_sf, frobRat_X_pow, hdiv, ← pow_succ' (Fintype.card F)]
    have e : sf a₂ a₄ a₆ ^ Fintype.card F / (sf a₂ a₄ a₆ ^ m) ^ 2 = sf a₂ a₄ a₆ := by
      rw [hm]
      field_simp
      ring
    rw [mul_div_right_comm, e]
  · rw [map_pow, frobRat_sf, hdiv, hkd, hk1, hm]
    field_simp
    ring

end frob

/-! ## The similitude -/

section similitude

variable {F : Type*} [Field F] [Fintype F] [DecidableEq (RatFunc F)] {a₂ a₄ a₆ : F}

omit [DecidableEq (RatFunc F)] in
/-- `P_0 = (st, s²)` is the point `P₀` of `ManinTwist`. -/
lemma Pk_zero (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) : Pk hF hD 0 = P0 (Ring.two_ne_zero hF) hD := by
  simp only [Pk, P0, pow_zero, pow_one, Nat.reduceDiv, zero_add]

lemma degZ_frob (hF : ringChar F ≠ 2) (P : (twist a₂ a₄ a₆).toAffine.Point) :
    degZ a₂ a₄ a₆ (frob hF P) = Fintype.card F * degZ a₂ a₄ a₆ P := by
  unfold degZ
  rw [pdeg_frob]
  push_cast
  ring

/-- **The Frobenius multiplies the polar form by `q`.** -/
lemma polar_frob (hF : ringChar F ≠ 2) (P R : (twist a₂ a₄ a₆).toAffine.Point) :
    polar (degZ a₂ a₄ a₆) (frob hF P) (frob hF R) = Fintype.card F * polar (degZ a₂ a₄ a₆) P R := by
  unfold polar
  rw [← map_add, degZ_frob, degZ_frob, degZ_frob]
  ring

lemma iterate_frob_P0 (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (n : ℕ) :
    (frob hF)^[n] (P0 (Ring.two_ne_zero hF) hD) = Pk hF hD n := by
  induction n with
  | zero => exact (Pk_zero hF hD).symm
  | succ n ih => rw [Function.iterate_succ_apply', ih, frob_Pk]

/-- **The Frobenius of Manin's twist is a similitude of factor `q` whose orbit of `P₀` is the Frobenius points.**
There is an additive map `φ` of the points of the twist with `deg φ(P) = q·deg P`, so `B(φP, φR) = q·B(P, R)` for the
polar form of the degree, and `φ^n(P₀) = P_n`. -/
theorem frobenius_similitude (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    ∃ φ : (twist a₂ a₄ a₆).toAffine.Point →+ (twist a₂ a₄ a₆).toAffine.Point,
      (∀ P, degZ a₂ a₄ a₆ (φ P) = Fintype.card F * degZ a₂ a₄ a₆ P) ∧
      (∀ P R, polar (degZ a₂ a₄ a₆) (φ P) (φ R) = Fintype.card F * polar (degZ a₂ a₄ a₆) P R) ∧
      ∀ n, φ^[n] (P0 (Ring.two_ne_zero hF) hD) = Pk hF hD n :=
  ⟨frob hF, degZ_frob hF, polar_frob hF, iterate_frob_P0 hF hD⟩

/-- **Along the orbit the form is Toeplitz up to `q^j`**: `B(P_{j+d}, P_j) = q^j·B(P_d, P_0)`, from the similitude
alone. So `B(P_i, P_j)/q^{(i+j)/2}` depends only on `|i − j|`. -/
theorem gram_orbit (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (j d : ℕ) :
    polar (degZ a₂ a₄ a₆) (Pk hF hD (j + d)) (Pk hF hD j) =
      (Fintype.card F : ℤ) ^ j * polar (degZ a₂ a₄ a₆) (Pk hF hD d) (Pk hF hD 0) := by
  induction j with
  | zero => rw [zero_add, pow_zero, one_mul]
  | succ j ih =>
    rw [show j + 1 + d = j + d + 1 by omega, ← frob_Pk, ← frob_Pk, polar_frob, ih, pow_succ]
    ring

/-- **The count kernel of `E` is the Gram kernel of an orbit of the similitude.** For an elliptic curve `E` over `𝔽_q`
and `d ≥ 1`, `B(φ^{j+d}P₀, φ^jP₀) = q^j(q^d + 1 − #E(L_d))`, with `L_d` a field of `q^d` elements and `φ` the
Frobenius of the twist of `y² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4`. With `B(φ^jP₀, φ^jP₀) = 2q^j` (`gram_self`). -/
theorem gram_orbit_card (W : WeierstrassCurve F) [W.IsElliptic] (hF : ringChar F ≠ 2) {L : Type*} [Field L]
    [Fintype L] [Algebra F L] {d : ℕ} (hd : 0 < d) (hL : Fintype.card L = Fintype.card F ^ d) (j : ℕ) :
    polar (degZ (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4))
        ((frob hF)^[j + d] (P0 (Ring.two_ne_zero hF) (dsc_ne_zero W hF W.isUnit_Δ.ne_zero)))
        ((frob hF)^[j] (P0 (Ring.two_ne_zero hF) (dsc_ne_zero W hF W.isUnit_Δ.ne_zero))) =
      (Fintype.card F : ℤ) ^ j * ((Fintype.card F : ℤ) ^ d + 1 - Nat.card (W.baseChange L).toAffine.Point) := by
  classical
  have hD := dsc_ne_zero W hF W.isUnit_Δ.ne_zero
  rw [iterate_frob_P0, iterate_frob_P0, gram_orbit, gram_lt hF hD hd, Nat.sub_zero, ← card_baseChange_eq W hF hL]
  ring

end similitude

/-! ## A similitude of a definite form -/

section spectrum

open Matrix ComplexConjugate
open scoped ComplexOrder

/-- **A similitude of factor `q` of a positive-definite Hermitian form has every eigenvalue on `|α|² = q`.** If
`AᴴGA = qG` with `G` positive-definite and `Av = αv` with `v ≠ 0`, then `|α|² = q`: both sides of
`(Av)ᴴG(Av) = vᴴ(AᴴGA)v` are multiples of `vᴴGv > 0`, by `|α|²` and by `q`. -/
theorem normSq_eq_of_similitude {n : Type*} [Fintype n] {G A : Matrix n n ℂ} (hG : G.PosDef) {q : ℝ}
    (hA : Aᴴ * G * A = (q : ℂ) • G) {α : ℂ} {v : n → ℂ} (hv : v ≠ 0) (hAv : A *ᵥ v = α • v) :
    Complex.normSq α = q := by
  have e1 : star (A *ᵥ v) ⬝ᵥ G *ᵥ (A *ᵥ v) = (q : ℂ) * (star v ⬝ᵥ G *ᵥ v) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have e2 : star (A *ᵥ v) ⬝ᵥ G *ᵥ (A *ᵥ v) = (Complex.normSq α : ℂ) * (star v ⬝ᵥ G *ᵥ v) := by
    rw [hAv, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  exact_mod_cast mul_right_cancel₀ (hG.dotProduct_mulVec_pos hv).ne' (e2.symm.trans e1)

end spectrum

end ManinHasse

#print axioms ManinHasse.frobenius_similitude
#print axioms ManinHasse.gram_orbit
#print axioms ManinHasse.gram_orbit_card
#print axioms ManinHasse.normSq_eq_of_similitude
