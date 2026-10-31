/-
# Manin's twist: the degree of the `x`-coordinate is a quadratic form along `P₀`

Plain statement. Let `k` be a field of characteristic not `2`. Let `f = X³ + a₂X² + a₄X + a₆ ∈ k[X]` with
`D = 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆ + 4a₄³ + 27a₆² ≠ 0`, so that `f` has no double root (`−D` is the discriminant of
`f`). Put `s = f(t) ∈ k(t)`. The twist `E'`: `y² = x³ + a₂sx² + a₄s²x + a₆s³` over `k(t)` carries the point
`P₀ = (st, s²)`. For a point `P` of `E'` write `deg P` for the degree of the rational function `x(P)/s`, and
`deg 0 = 0`. Then for every point `P`: `deg(P + P₀) + deg(P − P₀) = 2 deg P + 2` (`pdeg_add_add_pdeg_sub`). No
hypothesis beyond the two above.

This is the key step of Manin's proof of Hasse's bound (`ManinHasse`). In the coordinates `X = x/s`, `Y = y/s²` the
twist is `sY² = f(X)` and `P₀ = (t, 1)`. The `X`-coordinates of `P ± P₀` are the two roots of `W₀Z² − W₁Z + W₂`
(`vieta_X`). Here `X(P) = u/v` in lowest terms and
* `W₀ = (u − tv)²`,
* `W₁ = 2(u + tv)(tu + a₄v) + 4a₂tuv + 4a₆v²`,
* `W₂ = (tu − a₄v)² − 4a₆v(u + tv) − 4a₂a₆v²`.

Then:
* The `Wᵢ` have no common factor (`prim3_W`). A prime dividing them divides `f` and the doubling numerator
  `g = X⁴ − 2a₄X² − 8a₆X + a₄² − 4a₂a₆`, and `αf + βg = D` for explicit `α` and `β` (`bezout_fg`).
* Their largest degree is `2 max(deg u, deg v) + 2` (`max_natDegree_W`), read off the coefficient of `t^{2d+2}`.
* `ManinDegree.rdeg_add_rdeg_of_vieta` turns these into the identity.

The cases `P = 0` and `P = ±P₀` are checked directly, with `X(2P₀) = g(t)/4f(t)` of degree 4 (`pdeg_two_P0`).
-/
import ManinDegree

open Polynomial ManinDegree

namespace ManinHasse

/-- `D = 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆ + 4a₄³ + 27a₆²`, minus the discriminant of `X³ + a₂X² + a₄X + a₆`. -/
def dsc {R : Type*} [CommRing R] (a₂ a₄ a₆ : R) : R :=
  4 * a₂ ^ 3 * a₆ - a₂ ^ 2 * a₄ ^ 2 - 18 * a₂ * a₄ * a₆ + 4 * a₄ ^ 3 + 27 * a₆ ^ 2

/-- The discriminant of `y² = x³ + a₂x² + a₄x + a₆` is `−16D`. -/
lemma Δ_cubic {R : Type*} [CommRing R] (a₂ a₄ a₆ : R) :
    ({ a₁ := 0, a₂ := a₂, a₃ := 0, a₄ := a₄, a₆ := a₆ } : WeierstrassCurve R).Δ = -16 * dsc a₂ a₄ a₆ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, dsc]
  ring

variable {k : Type*} [Field k]

/-! ## The cubic and its Bézout identity -/

/-- `f = X³ + a₂X² + a₄X + a₆`. -/
noncomputable def fpol (a₂ a₄ a₆ : k) : k[X] := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆

/-- `g = X⁴ − 2a₄X² − 8a₆X + a₄² − 4a₂a₆`, the numerator of the doubling formula. -/
noncomputable def gpol (a₂ a₄ a₆ : k) : k[X] :=
  X ^ 4 - 2 * C a₄ * X ^ 2 - 8 * C a₆ * X + C a₄ ^ 2 - 4 * C a₂ * C a₆

lemma bezout_fg (a₂ a₄ a₆ : k) :
    (-3 * X ^ 3 + C a₂ * X ^ 2 + 5 * C a₄ * X - 2 * C a₂ * C a₄ + 27 * C a₆) * fpol a₂ a₄ a₆ +
      (3 * X ^ 2 + 2 * C a₂ * X - C a₂ ^ 2 + 4 * C a₄) * gpol a₂ a₄ a₆ = C (dsc a₂ a₄ a₆) := by
  simp only [fpol, gpol, dsc, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

variable {a₂ a₄ a₆ : k}

lemma not_prime_dvd_fg (hD : dsc a₂ a₄ a₆ ≠ 0) {π : k[X]} (hπ : Prime π) (hf : π ∣ fpol a₂ a₄ a₆)
    (hg : π ∣ gpol a₂ a₄ a₆) : False := by
  have h := dvd_add
    (dvd_mul_of_dvd_right hf (-3 * X ^ 3 + C a₂ * X ^ 2 + 5 * C a₄ * X - 2 * C a₂ * C a₄ + 27 * C a₆))
    (dvd_mul_of_dvd_right hg (3 * X ^ 2 + 2 * C a₂ * X - C a₂ ^ 2 + 4 * C a₄))
  rw [bezout_fg] at h
  exact hπ.not_isUnit (isUnit_of_dvd_unit h (isUnit_C.2 hD.isUnit))

lemma isCoprime_C {p : k[X]} {c : k} (hc : c ≠ 0) : IsCoprime p (C c) :=
  ⟨0, C c⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hc, C_1]⟩

lemma isCoprime_g_f (hD : dsc a₂ a₄ a₆ ≠ 0) : IsCoprime (gpol a₂ a₄ a₆) (fpol a₂ a₄ a₆) := by
  refine ⟨C (dsc a₂ a₄ a₆)⁻¹ * (3 * X ^ 2 + 2 * C a₂ * X - C a₂ ^ 2 + 4 * C a₄),
    C (dsc a₂ a₄ a₆)⁻¹ * (-3 * X ^ 3 + C a₂ * X ^ 2 + 5 * C a₄ * X - 2 * C a₂ * C a₄ + 27 * C a₆), ?_⟩
  have h := congrArg (C (dsc a₂ a₄ a₆)⁻¹ * ·) (bezout_fg a₂ a₄ a₆)
  simp only [← C_mul, inv_mul_cancel₀ hD, C_1] at h
  linear_combination h

variable (a₂ a₄ a₆) in
lemma fpol_ne_zero : fpol a₂ a₄ a₆ ≠ 0 := fun h => by
  have := congrArg (coeff · 3) h
  simp [fpol] at this

variable (a₂ a₄ a₆) in
lemma natDegree_fpol : (fpol a₂ a₄ a₆).natDegree = 3 := by
  unfold fpol; compute_degree!

variable (a₂ a₄ a₆) in
lemma natDegree_gpol : (gpol a₂ a₄ a₆).natDegree = 4 := by
  unfold gpol; compute_degree!

/-! ## The triple `W₀`, `W₁`, `W₂` -/

/-- `W₀ = (u − Xv)²`. -/
noncomputable def W0 (u v : k[X]) : k[X] := (u - X * v) ^ 2

/-- `W₁ = 2(u + Xv)(Xu + a₄v) + 4a₂Xuv + 4a₆v²`. -/
noncomputable def W1 (a₂ a₄ a₆ : k) (u v : k[X]) : k[X] :=
  C 2 * ((u + X * v) * (X * u + C a₄ * v)) + C (4 * a₂) * (X * (u * v)) + C (4 * a₆) * v ^ 2

/-- `W₂ = (Xu − a₄v)² − 4a₆v(u + Xv) − 4a₂a₆v²`. -/
noncomputable def W2 (a₂ a₄ a₆ : k) (u v : k[X]) : k[X] :=
  (X * u - C a₄ * v) ^ 2 - C (4 * a₆) * (v * (u + X * v)) - C (4 * a₂ * a₆) * v ^ 2

variable (a₂ a₄ a₆) in
lemma W1_eq (u v : k[X]) :
    W1 a₂ a₄ a₆ u v = C 4 * v ^ 2 * fpol a₂ a₄ a₆ +
      (u - X * v) * (C 2 * (2 * X ^ 2 * v + X * u + 2 * C a₂ * X * v + C a₄ * v)) := by
  simp only [W1, fpol, map_mul, map_ofNat]
  ring

variable (a₂ a₄ a₆) in
lemma W2_eq (u v : k[X]) :
    W2 a₂ a₄ a₆ u v = v ^ 2 * gpol a₂ a₄ a₆ +
      (u - X * v) * (X ^ 3 * v + X ^ 2 * u - 2 * C a₄ * X * v - 4 * C a₆ * v) := by
  simp only [W2, gpol, map_mul, map_ofNat]
  ring

/-- **The `Wᵢ` have no common factor.** -/
lemma prim3_W (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) {u v : k[X]} (huv : IsCoprime u v) :
    Prim3 (W0 u v) (W1 a₂ a₄ a₆ u v) (W2 a₂ a₄ a₆ u v) := by
  refine prim3_of_prime fun π hπ h0 h1 h2' => ?_
  have hL : π ∣ u - X * v := hπ.dvd_of_dvd_pow h0
  have hv : ¬π ∣ v := fun hv => hπ.not_isUnit (huv.isUnit_of_dvd' (by
    simpa using dvd_add hL (dvd_mul_of_dvd_right hv X)) hv)
  have hC : ∀ c : k, c ≠ 0 → ¬π ∣ C c := fun c hc h =>
    hπ.not_isUnit (isUnit_of_dvd_unit h (isUnit_C.2 hc.isUnit))
  have h4 : (4 : k) ≠ 0 := by
    have e : (4 : k) = 2 * 2 := by norm_num
    rw [e]; exact mul_ne_zero h2 h2
  have hf : π ∣ fpol a₂ a₄ a₆ := by
    rw [W1_eq] at h1
    have h' : π ∣ C 4 * v ^ 2 * fpol a₂ a₄ a₆ := (dvd_add_left (dvd_mul_of_dvd_left hL _)).1 h1
    rcases hπ.dvd_or_dvd h' with h'' | h''
    · rcases hπ.dvd_or_dvd h'' with h''' | h'''
      · exact absurd h''' (hC 4 h4)
      · exact absurd (hπ.dvd_of_dvd_pow h''') hv
    · exact h''
  have hg : π ∣ gpol a₂ a₄ a₆ := by
    rw [W2_eq] at h2'
    have h' : π ∣ v ^ 2 * gpol a₂ a₄ a₆ := (dvd_add_left (dvd_mul_of_dvd_left hL _)).1 h2'
    rcases hπ.dvd_or_dvd h' with h'' | h''
    · exact absurd (hπ.dvd_of_dvd_pow h'') hv
    · exact h''
  exact not_prime_dvd_fg hD hπ hf hg

variable (a₂ a₄ a₆) in
/-- **The largest degree among the `Wᵢ` is `2 max(deg u, deg v) + 2`.** -/
lemma max_natDegree_W {u v : k[X]} (hv : v ≠ 0) :
    max (W0 u v).natDegree (max (W1 a₂ a₄ a₆ u v).natDegree (W2 a₂ a₄ a₆ u v).natDegree) =
      2 * max u.natDegree v.natDegree + 2 := by
  set d := max u.natDegree v.natDegree
  have hu : u.natDegree ≤ d := le_max_left _ _
  have hvd : v.natDegree ≤ d := le_max_right _ _
  have hX : ∀ p : k[X], p.natDegree ≤ d → (X * p).natDegree ≤ d + 1 := fun p hp =>
    natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  have hC' : ∀ (c : k) (p : k[X]), p.natDegree ≤ d → (C c * p).natDegree ≤ d + 1 := fun c p hp =>
    (natDegree_C_mul_le c p).trans (by omega)
  have L1 : (u - X * v).natDegree ≤ d + 1 := (natDegree_sub_le _ _).trans (max_le (by omega) (hX v hvd))
  have L2 : (u + X * v).natDegree ≤ d + 1 := (natDegree_add_le _ _).trans (max_le (by omega) (hX v hvd))
  have L3 : (X * u + C a₄ * v).natDegree ≤ d + 1 :=
    (natDegree_add_le _ _).trans (max_le (hX u hu) (hC' a₄ v hvd))
  have L4 : (X * u - C a₄ * v).natDegree ≤ d + 1 :=
    (natDegree_sub_le _ _).trans (max_le (hX u hu) (hC' a₄ v hvd))
  have zu : u.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have zv : v.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have c1 : (u - X * v).coeff (d + 1) = -v.coeff d := by rw [coeff_sub, coeff_X_mul, zu]; ring
  have c4 : (X * u - C a₄ * v).coeff (d + 1) = u.coeff d := by
    rw [coeff_sub, coeff_X_mul, coeff_C_mul, zv]; ring
  have e2' : 2 * d + 2 = 2 * (d + 1) := by ring
  -- the bounds
  have B0 : (W0 u v).natDegree ≤ 2 * d + 2 := natDegree_pow_le.trans (by omega)
  have Bv2 : (C (4 * a₆) * v ^ 2).natDegree ≤ 2 * d :=
    (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega))
  have Bv2' : (C (4 * a₂ * a₆) * v ^ 2).natDegree ≤ 2 * d :=
    (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega))
  have Buv : (C (4 * a₂) * (X * (u * v))).natDegree ≤ 2 * d + 1 := by
    have := natDegree_mul_le (p := u) (q := v)
    exact (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans (by rw [natDegree_X]; omega))
  have Bvl : (C (4 * a₆) * (v * (u + X * v))).natDegree ≤ 2 * d + 1 := (natDegree_C_mul_le _ _).trans
    (natDegree_mul_le.trans (by omega))
  have Bm : ((u + X * v) * (X * u + C a₄ * v)).natDegree ≤ 2 * d + 2 := natDegree_mul_le.trans (by omega)
  have B1 : (W1 a₂ a₄ a₆ u v).natDegree ≤ 2 * d + 2 :=
    (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans Bm) (by omega))) (by omega))
  have B2 : (W2 a₂ a₄ a₆ u v).natDegree ≤ 2 * d + 2 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
      (max_le (natDegree_pow_le.trans (by omega)) (by omega))) (by omega))
  -- the coefficients of `t^{2d+2}`
  have k0 : (W0 u v).coeff (2 * d + 2) = v.coeff d ^ 2 := by
    rw [W0, e2', coeff_pow_of_natDegree_le L1, c1, neg_sq]
  have k2 : (W2 a₂ a₄ a₆ u v).coeff (2 * d + 2) = u.coeff d ^ 2 := by
    rw [W2, coeff_sub, coeff_sub, coeff_eq_zero_of_natDegree_lt (p := C (4 * a₆) * (v * (u + X * v))) (by omega),
      coeff_eq_zero_of_natDegree_lt (p := C (4 * a₂ * a₆) * v ^ 2) (by omega), sub_zero, sub_zero, e2',
      coeff_pow_of_natDegree_le L4, c4]
  apply le_antisymm
  · exact max_le B0 (max_le B1 B2)
  · rcases coeff_max_ne_zero (r := u) (Or.inr hv) with h | h
    · exact (le_natDegree_of_ne_zero (by rw [k2]; exact pow_ne_zero 2 h)).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_natDegree_of_ne_zero (by rw [k0]; exact pow_ne_zero 2 h)).trans (le_max_left _ _)

/-! ## The Vieta identities in a field -/

/-- **The `X`-coordinates of `P ± P₀` are the roots of `(X − t)²Z² − W₁Z + W₂`**, in the coordinates of `sY² = f(X)`
with `P = (X, Y)` and `P₀ = (t, 1)`. -/
lemma vieta_X {F : Type*} [Field F] {X Y s t A₂ A₄ A₆ : F} (hY : s * Y ^ 2 = X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆)
    (hs : s = t ^ 3 + A₂ * t ^ 2 + A₄ * t + A₆) (hX : X - t ≠ 0) :
    (s * (Y - 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂) + (s * (Y + 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂))) *
        (X - t) ^ 2 = 2 * (X + t) * (X * t + A₄) + 4 * A₂ * X * t + 4 * A₆ ∧
      (s * (Y - 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂)) * (s * (Y + 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂)) *
        (X - t) ^ 2 = (X * t - A₄) ^ 2 - 4 * A₆ * (X + t) - 4 * A₂ * A₆ := by
  have hQ : (X - t) ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have eP : (s * (Y - 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂)) * (X - t) ^ 2 =
      s * (Y - 1) ^ 2 - (X + t + A₂) * (X - t) ^ 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hQ]
  have eM : (s * (Y + 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂)) * (X - t) ^ 2 =
      s * (Y + 1) ^ 2 - (X + t + A₂) * (X - t) ^ 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hQ]
  refine ⟨by linear_combination eP + eM + 2 * hY + 2 * hs, ?_⟩
  refine mul_right_cancel₀ hQ ?_
  linear_combination (s * (Y + 1) ^ 2 / (X - t) ^ 2 - (X + t + A₂)) * (X - t) ^ 2 * eP +
    (s * (Y - 1) ^ 2 - (X + t + A₂) * (X - t) ^ 2) * eM +
    (-A₂ * X ^ 2 + 4 * A₂ * X * t - 2 * A₂ * t ^ 2 + A₄ * X + A₆ - X ^ 3 + 2 * X ^ 2 * t + 2 * X * t ^ 2 +
      Y ^ 2 * s - 2 * s - 2 * t ^ 3) * hY +
    (-4 * A₂ * X ^ 2 + 4 * A₂ * X * t - A₂ * t ^ 2 - 2 * A₄ * X + A₄ * t - A₆ - 4 * X ^ 3 + 2 * X ^ 2 * t +
      2 * X * t ^ 2 + s - t ^ 3) * hs

/-- The doubling formula at `P₀ = (st, s²)`: `x(2P₀)/s = g(t)/4s` with `s = f(t)`. -/
lemma double_div {F : Type*} [Field F] {s t A₂ A₄ A₆ : F} (h2 : (2 : F) ≠ 0) (hs0 : s ≠ 0)
    (hs : s = t ^ 3 + A₂ * t ^ 2 + A₄ * t + A₆) :
    (((3 * (s * t) ^ 2 + 2 * (A₂ * s) * (s * t) + A₄ * s ^ 2 - 0 * s ^ 2) / (s ^ 2 - -s ^ 2)) ^ 2 - A₂ * s -
        s * t - s * t) / s = (t ^ 4 - 2 * A₄ * t ^ 2 - 8 * A₆ * t + A₄ ^ 2 - 4 * A₂ * A₆) / (4 * s) := by
  have h4 : (4 : F) ≠ 0 := by
    have e : (4 : F) = 2 * 2 := by norm_num
    rw [e]; exact mul_ne_zero h2 h2
  have hss : s ^ 2 - -s ^ 2 = 2 * s ^ 2 := by ring
  rw [hss]
  field_simp
  linear_combination (-16 * (A₂ + 2 * t)) * hs

/-- The `X`-coordinate of `P + P₀` from the chord through `P` and `P₀`, in the coordinates `X = x/s`, `Y = y/s²`. -/
lemma chord_pos {F : Type*} [Field F] {x y s t A₂ : F} (hs : s ≠ 0) (hx : x - s * t ≠ 0) :
    (((y - s ^ 2) / (x - s * t)) ^ 2 - A₂ * s - x - s * t) / s =
      s * (y / s ^ 2 - 1) ^ 2 / (x / s - t) ^ 2 - (x / s + t + A₂) := by
  have hx'' : x - t * s ≠ 0 := by rwa [mul_comm] at hx
  have hx' : x / s - t ≠ 0 := by
    rw [div_sub' hs]; exact div_ne_zero hx hs
  field_simp
  ring

/-- The `X`-coordinate of `P − P₀` from the chord through `P` and `−P₀`. -/
lemma chord_neg {F : Type*} [Field F] {x y s t A₂ : F} (hs : s ≠ 0) (hx : x - s * t ≠ 0) :
    (((y - -s ^ 2) / (x - s * t)) ^ 2 - A₂ * s - x - s * t) / s =
      s * (y / s ^ 2 + 1) ^ 2 / (x / s - t) ^ 2 - (x / s + t + A₂) := by
  have hx'' : x - t * s ≠ 0 := by rwa [mul_comm] at hx
  have hx' : x / s - t ≠ 0 := by
    rw [div_sub' hs]; exact div_ne_zero hx hs
  field_simp
  ring

/-! ## The twist over `k(t)` -/

local notation "ι" => algebraMap k[X] (RatFunc k)

variable (a₂ a₄ a₆)

/-- `s = f(t)`. -/
noncomputable def sf : RatFunc k := ι (fpol a₂ a₄ a₆)

/-- The twist `y² = x³ + a₂sx² + a₄s²x + a₆s³` of `y² = f(x)` by `s = f(t)`, over `k(t)`. -/
noncomputable def twist : WeierstrassCurve (RatFunc k) :=
  { a₁ := 0, a₂ := ι (C a₂) * sf a₂ a₄ a₆, a₃ := 0, a₄ := ι (C a₄) * sf a₂ a₄ a₆ ^ 2,
    a₆ := ι (C a₆) * sf a₂ a₄ a₆ ^ 3 }

lemma sf_eq : sf a₂ a₄ a₆ = ι X ^ 3 + ι (C a₂) * ι X ^ 2 + ι (C a₄) * ι X + ι (C a₆) := by
  simp [sf, fpol]

lemma sf_ne_zero : sf a₂ a₄ a₆ ≠ 0 := fun h =>
  fpol_ne_zero a₂ a₄ a₆ (IsFractionRing.injective k[X] (RatFunc k) (h.trans (map_zero _).symm))

variable {a₂ a₄ a₆}

lemma twist_Δ_ne_zero (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) : (twist a₂ a₄ a₆).Δ ≠ 0 := by
  rw [twist, Δ_cubic]
  have hs := sf_ne_zero a₂ a₄ a₆
  have hD' : ι (C (dsc a₂ a₄ a₆)) ≠ 0 := fun h => hD (C_injective (IsFractionRing.injective k[X]
    (RatFunc k) (h.trans (map_zero _).symm) |>.trans C_0.symm))
  have h16 : (-16 : RatFunc k) ≠ 0 := by
    have h16k : (-16 : k) ≠ 0 := by
      have e : (-16 : k) = -2 ^ 4 := by norm_num
      rw [e]; exact neg_ne_zero.2 (pow_ne_zero 4 h2)
    have h := (map_ne_zero (algebraMap k (RatFunc k))).2 h16k
    rwa [map_neg, map_ofNat] at h
  have e : dsc (ι (C a₂) * sf a₂ a₄ a₆) (ι (C a₄) * sf a₂ a₄ a₆ ^ 2) (ι (C a₆) * sf a₂ a₄ a₆ ^ 3) =
      sf a₂ a₄ a₆ ^ 6 * ι (C (dsc a₂ a₄ a₆)) := by
    simp only [dsc, map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [e]
  exact mul_ne_zero h16 (mul_ne_zero (pow_ne_zero 6 hs) hD')

lemma twist_equation (x y : RatFunc k) :
    (twist a₂ a₄ a₆).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 + ι (C a₂) * sf a₂ a₄ a₆ * x ^ 2 + ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * x +
        ι (C a₆) * sf a₂ a₄ a₆ ^ 3 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [twist]

lemma twist_nonsingular (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) (x y : RatFunc k) :
    (twist a₂ a₄ a₆).toAffine.Nonsingular x y ↔
      y ^ 2 = x ^ 3 + ι (C a₂) * sf a₂ a₄ a₆ * x ^ 2 + ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * x +
        ι (C a₆) * sf a₂ a₄ a₆ ^ 3 :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := (twist a₂ a₄ a₆).toAffine)
    (twist_Δ_ne_zero h2 hD)).symm.trans (twist_equation x y)

lemma P0_equation : (sf a₂ a₄ a₆ ^ 2) ^ 2 = (sf a₂ a₄ a₆ * ι X) ^ 3 +
    ι (C a₂) * sf a₂ a₄ a₆ * (sf a₂ a₄ a₆ * ι X) ^ 2 + ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * (sf a₂ a₄ a₆ * ι X) +
      ι (C a₆) * sf a₂ a₄ a₆ ^ 3 := by
  have hs := sf_eq a₂ a₄ a₆
  linear_combination (sf a₂ a₄ a₆) ^ 3 * hs

/-- `P₀ = (st, s²)`, the point `(t, 1)` of `sY² = f(X)`. -/
noncomputable def P0 (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) : (twist a₂ a₄ a₆).toAffine.Point :=
  .some _ _ ((twist_nonsingular h2 hD _ _).2 P0_equation)

variable (a₂ a₄ a₆) in
/-- The degree of a point: the degree of the rational function `x/s`, and `0` at the point at infinity. -/
noncomputable def pdeg : (twist a₂ a₄ a₆).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => rdeg (x / sf a₂ a₄ a₆)

lemma pdeg_neg (P : (twist a₂ a₄ a₆).toAffine.Point) : pdeg a₂ a₄ a₆ (-P) = pdeg a₂ a₄ a₆ P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

lemma pdeg_P0 (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) : pdeg a₂ a₄ a₆ (P0 h2 hD) = 1 := by
  simp only [P0, pdeg]
  rw [mul_div_cancel_left₀ _ (sf_ne_zero a₂ a₄ a₆), rdeg_algebraMap, natDegree_X]

lemma twist_negY (x y : RatFunc k) : (twist a₂ a₄ a₆).toAffine.negY x y = -y := by
  show -y - 0 * x - 0 = -y
  ring

lemma twist_addX (x₁ x₂ ℓ : RatFunc k) :
    (twist a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - ι (C a₂) * sf a₂ a₄ a₆ - x₁ - x₂ := by
  show ℓ ^ 2 + 0 * ℓ - ι (C a₂) * sf a₂ a₄ a₆ - x₁ - x₂ = _
  ring

lemma pdeg_zero : pdeg a₂ a₄ a₆ 0 = 0 := rfl

lemma ratFunc_two_ne_zero (h2 : (2 : k) ≠ 0) : (2 : RatFunc k) ≠ 0 := by
  have h := (map_ne_zero (algebraMap k (RatFunc k))).2 h2
  rwa [map_ofNat] at h

/-- **The identity in the coordinates `X = x/s`, `Y = y/s²`.** For a point `(X, Y) ≠ (t, ±1)` of `sY² = f(X)`, the
degrees of the `X`-coordinates of `(X, Y) ± (t, 1)` add up to `2 deg X + 2`. -/
lemma rdeg_vieta (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) {z Y : RatFunc k}
    (hY : sf a₂ a₄ a₆ * Y ^ 2 = z ^ 3 + ι (C a₂) * z ^ 2 + ι (C a₄) * z + ι (C a₆)) (hz : z - ι X ≠ 0) :
    rdeg (sf a₂ a₄ a₆ * (Y - 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂))) +
      rdeg (sf a₂ a₄ a₆ * (Y + 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂))) = 2 * rdeg z + 2 := by
  obtain ⟨V1, V2⟩ := vieta_X hY (sf_eq a₂ a₄ a₆) hz
  have hv : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hv' : ι z.denom ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 hv
  have hu : ι z.num = z * ι z.denom := (div_eq_iff hv').1 (RatFunc.num_div_denom z)
  have e0 : ι (W0 z.num z.denom) = (z - ι X) ^ 2 * ι z.denom ^ 2 := by
    simp only [W0, map_pow, map_sub, map_mul]
    rw [hu]
    ring
  have e1 : ι (W1 a₂ a₄ a₆ z.num z.denom) =
      (2 * (z + ι X) * (z * ι X + ι (C a₄)) + 4 * ι (C a₂) * z * ι X + 4 * ι (C a₆)) * ι z.denom ^ 2 := by
    simp only [W1, map_add, map_mul, map_pow, map_ofNat]
    rw [hu]
    ring
  have e2 : ι (W2 a₂ a₄ a₆ z.num z.denom) =
      ((z * ι X - ι (C a₄)) ^ 2 - 4 * ι (C a₆) * (z + ι X) - 4 * ι (C a₂) * ι (C a₆)) * ι z.denom ^ 2 := by
    simp only [W2, map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hu]
    ring
  have hW0' : ι (W0 z.num z.denom) ≠ 0 := by
    rw [e0]; exact mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hv')
  have hW0 : W0 z.num z.denom ≠ 0 := fun h0 => hW0' (by rw [h0, map_zero])
  have hsum : sf a₂ a₄ a₆ * (Y - 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂)) +
      (sf a₂ a₄ a₆ * (Y + 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂))) =
        ι (W1 a₂ a₄ a₆ z.num z.denom) / ι (W0 z.num z.denom) := by
    rw [eq_div_iff hW0', e0, e1, ← V1]
    ring
  have hprod : (sf a₂ a₄ a₆ * (Y - 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂))) *
      (sf a₂ a₄ a₆ * (Y + 1) ^ 2 / (z - ι X) ^ 2 - (z + ι X + ι (C a₂))) =
        ι (W2 a₂ a₄ a₆ z.num z.denom) / ι (W0 z.num z.denom) := by
    rw [eq_div_iff hW0', e0, e2, ← V2]
    ring
  rw [rdeg_add_rdeg_of_vieta hW0 (prim3_W h2 hD (RatFunc.isCoprime_num_denom z)) hsum hprod,
    max_natDegree_W a₂ a₄ a₆ hv]
  rfl

section group

variable [DecidableEq (RatFunc k)]

/-- **`deg 2P₀ = 4`**: `X(2P₀) = g(t)/4f(t)`. -/
lemma pdeg_two_P0 (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    pdeg a₂ a₄ a₆ (P0 h2 hD + P0 h2 hD) = 4 := by
  have hs0 := sf_ne_zero a₂ a₄ a₆
  have h2' := ratFunc_two_ne_zero h2
  have hy : sf a₂ a₄ a₆ ^ 2 ≠ (twist a₂ a₄ a₆).toAffine.negY (sf a₂ a₄ a₆ * ι X) (sf a₂ a₄ a₆ ^ 2) := by
    rw [twist_negY]
    intro h
    have : 2 * sf a₂ a₄ a₆ ^ 2 = 0 := by linear_combination h
    exact mul_ne_zero h2' (pow_ne_zero 2 hs0) this
  have h4 : (4 : k) ≠ 0 := by
    have e : (4 : k) = 2 * 2 := by norm_num
    rw [e]; exact mul_ne_zero h2 h2
  have hx : (twist a₂ a₄ a₆).toAffine.addX (sf a₂ a₄ a₆ * ι X) (sf a₂ a₄ a₆ * ι X)
      ((twist a₂ a₄ a₆).toAffine.slope (sf a₂ a₄ a₆ * ι X) (sf a₂ a₄ a₆ * ι X) (sf a₂ a₄ a₆ ^ 2)
        (sf a₂ a₄ a₆ ^ 2)) / sf a₂ a₄ a₆ = ι (gpol a₂ a₄ a₆) / ι (C 4 * fpol a₂ a₄ a₆) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, twist_addX, twist_negY]
    show (((3 * (sf a₂ a₄ a₆ * ι X) ^ 2 + 2 * (ι (C a₂) * sf a₂ a₄ a₆) * (sf a₂ a₄ a₆ * ι X) +
      ι (C a₄) * sf a₂ a₄ a₆ ^ 2 - 0 * sf a₂ a₄ a₆ ^ 2) / (sf a₂ a₄ a₆ ^ 2 - -sf a₂ a₄ a₆ ^ 2)) ^ 2 -
        ι (C a₂) * sf a₂ a₄ a₆ - sf a₂ a₄ a₆ * ι X - sf a₂ a₄ a₆ * ι X) / sf a₂ a₄ a₆ =
      ι (gpol a₂ a₄ a₆) / ι (C 4 * fpol a₂ a₄ a₆)
    have h4f : ι (C 4 * fpol a₂ a₄ a₆) = 4 * sf a₂ a₄ a₆ := by simp only [map_mul, map_ofNat, sf]
    have hg : ι (gpol a₂ a₄ a₆) = ι X ^ 4 - 2 * ι (C a₄) * ι X ^ 2 - 8 * ι (C a₆) * ι X + ι (C a₄) ^ 2 -
        4 * ι (C a₂) * ι (C a₆) := by
      simp only [gpol, map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [h4f, hg]
    exact double_div h2' hs0 (sf_eq a₂ a₄ a₆)
  unfold P0
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  simp only [pdeg]
  rw [hx, rdeg_div ((isCoprime_C h4).mul_right (isCoprime_g_f hD))
    (mul_ne_zero (C_ne_zero.2 h4) (fpol_ne_zero a₂ a₄ a₆)), natDegree_gpol, natDegree_C_mul h4, natDegree_fpol]
  rfl

/-- `deg(P + P₀)` for `P = (x, y)` with `x ≠ st`, in the coordinates `X = x/s`, `Y = y/s²`. -/
lemma pdeg_some_add_P0 (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) {x y : RatFunc k}
    (h : (twist a₂ a₄ a₆).toAffine.Nonsingular x y) (hx : x ≠ sf a₂ a₄ a₆ * ι X) :
    pdeg a₂ a₄ a₆ (.some x y h + P0 h2 hD) = rdeg (sf a₂ a₄ a₆ * (y / sf a₂ a₄ a₆ ^ 2 - 1) ^ 2 /
      (x / sf a₂ a₄ a₆ - ι X) ^ 2 - (x / sf a₂ a₄ a₆ + ι X + ι (C a₂))) := by
  unfold P0
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [pdeg]
  rw [twist_addX, WeierstrassCurve.Affine.slope_of_X_ne hx, chord_pos (sf_ne_zero a₂ a₄ a₆) (sub_ne_zero.2 hx)]

/-- `deg(P − P₀)` for `P = (x, y)` with `x ≠ st`, in the coordinates `X = x/s`, `Y = y/s²`. -/
lemma pdeg_some_sub_P0 (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) {x y : RatFunc k}
    (h : (twist a₂ a₄ a₆).toAffine.Nonsingular x y) (hx : x ≠ sf a₂ a₄ a₆ * ι X) :
    pdeg a₂ a₄ a₆ (.some x y h - P0 h2 hD) = rdeg (sf a₂ a₄ a₆ * (y / sf a₂ a₄ a₆ ^ 2 + 1) ^ 2 /
      (x / sf a₂ a₄ a₆ - ι X) ^ 2 - (x / sf a₂ a₄ a₆ + ι X + ι (C a₂))) := by
  unfold P0
  rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [pdeg]
  rw [twist_addX, WeierstrassCurve.Affine.slope_of_X_ne hx, twist_negY,
    chord_neg (sf_ne_zero a₂ a₄ a₆) (sub_ne_zero.2 hx)]

/-- **`deg(P + P₀) + deg(P − P₀) = 2 deg P + 2`** on the twist `y² = x³ + a₂sx² + a₄s²x + a₆s³`. -/
theorem pdeg_add_add_pdeg_sub (h2 : (2 : k) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) (P : (twist a₂ a₄ a₆).toAffine.Point) :
    pdeg a₂ a₄ a₆ (P + P0 h2 hD) + pdeg a₂ a₄ a₆ (P - P0 h2 hD) = 2 * pdeg a₂ a₄ a₆ P + 2 := by
  have hs0 := sf_ne_zero a₂ a₄ a₆
  rcases P with _ | ⟨x, y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add, zero_sub, pdeg_neg, pdeg_P0, pdeg_zero]
  have heq := (twist_nonsingular h2 hD x y).1 h
  by_cases hx : x = sf a₂ a₄ a₆ * ι X
  · -- `P = ±P₀`
    have hyy : y ^ 2 = (sf a₂ a₄ a₆ ^ 2) ^ 2 := by rw [heq, hx]; exact P0_equation.symm
    subst hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hyy with hy | hy
    · subst hy
      have hP : (WeierstrassCurve.Affine.Point.some _ _ h : (twist a₂ a₄ a₆).toAffine.Point) = P0 h2 hD := rfl
      rw [hP, sub_self, pdeg_two_P0, pdeg_zero, pdeg_P0]
    · subst hy
      have hP : (WeierstrassCurve.Affine.Point.some _ _ h : (twist a₂ a₄ a₆).toAffine.Point) = -P0 h2 hD := by
        unfold P0
        rw [WeierstrassCurve.Affine.Point.neg_some]
        simp only [twist_negY]
      have hn : -P0 h2 hD - P0 h2 hD = -(P0 h2 hD + P0 h2 hD) := by abel
      rw [hP, neg_add_cancel, hn, pdeg_neg, pdeg_neg, pdeg_two_P0, pdeg_zero, pdeg_P0]
  · -- the generic case
    have hx' : x - sf a₂ a₄ a₆ * ι X ≠ 0 := sub_ne_zero.2 hx
    have hY : sf a₂ a₄ a₆ * (y / sf a₂ a₄ a₆ ^ 2) ^ 2 = (x / sf a₂ a₄ a₆) ^ 3 +
        ι (C a₂) * (x / sf a₂ a₄ a₆) ^ 2 + ι (C a₄) * (x / sf a₂ a₄ a₆) + ι (C a₆) := by
      have e : sf a₂ a₄ a₆ * (y / sf a₂ a₄ a₆ ^ 2) ^ 2 - ((x / sf a₂ a₄ a₆) ^ 3 +
          ι (C a₂) * (x / sf a₂ a₄ a₆) ^ 2 + ι (C a₄) * (x / sf a₂ a₄ a₆) + ι (C a₆)) =
          (y ^ 2 - (x ^ 3 + ι (C a₂) * sf a₂ a₄ a₆ * x ^ 2 + ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * x +
            ι (C a₆) * sf a₂ a₄ a₆ ^ 3)) / sf a₂ a₄ a₆ ^ 3 := by
        field_simp
      rw [heq, sub_self, zero_div] at e
      exact sub_eq_zero.1 e
    have hzt : x / sf a₂ a₄ a₆ - ι X ≠ 0 := by
      rw [div_sub' hs0]; exact div_ne_zero hx' hs0
    rw [pdeg_some_add_P0 h2 hD h hx, pdeg_some_sub_P0 h2 hD h hx]
    exact rdeg_vieta h2 hD hY hzt

end group

end ManinHasse
