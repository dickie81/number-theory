/-
# A bilinear Type I estimate by Parseval's identity

Plain statements. `e(x) = e^{2πix/q}` is Mathlib's `ZMod.stdAddChar`, `dw q a n = 1[n ≡ a] − 1[(n, q) = 1]/φ(q)`
(`SieveFamily.dw`), and for a weight `w` on a finite set `S` of naturals, `ŵ(h) = Σ_{k∈S} w(k)e(hk)` (`what`) and
`E_w = Σ_{k∈S} w(k)1[(k, q) = 1] − (φ(q)/q)Σ_{k∈S} w(k)` (`Ew`). For coefficients `α` on `D₁` and `β` on `D₂`, sets of
naturals prime to `q`, `B(h) = Σ_{d₁,d₂} α(d₁)β(d₂)e(−had̄₁d̄₂)` (`Bh`).

* `sum_eq_mul`, `ind_eq`: orthogonality, `Σ_h e(ht) = q·1[t = 0]`, and `1[k = c] = q⁻¹Σ_h e(h(k − c))`.
* `sum_w_dw`: for `d` prime to `q`, `Σ_{k∈S} w(k)dw(dk) = q⁻¹Σ_{h≠0} ŵ(h)e(−had̄) − E_w/φ(q)`.
* `sum_bilinear`: `Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k) = q⁻¹Σ_{h≠0} ŵ(h)B(h) − (Σα)(Σβ)E_w/φ(q)`.
* `sum_norm_sq_le` (Parseval): `Σ_r |Σ_{j∈J} c_je(rs_j)|² ≤ qΣ_{j,j′∈J, s_j = s_j′} |c_j||c_j′|`.
* `typeIB_bound`, **the bilinear Type I estimate**: let `a` be a unit mod `q`, `D₂ ⊆ [1, Dm]` with `Dm ≥ 1` and
  `2HDm < q`, every residue the inverse of at most `m` elements of `D₁`, every `|t|d` with `0 < |t| ≤ H` and `d ∈ D₂`
  with at most `F` divisors, and `|ŵ(h)| ≤ W` at the frequencies `h ≠ 0` off the image of `[−H, H]`. Then
  `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k)|` is at most
  `(Σ|α|²)^{1/2}(mF(Σ|β|²)·q⁻¹Σ_h|ŵ(h)|²)^{1/2} + W(Σ|α|)(Σ|β|) + |(Σα)(Σβ)E_w/φ(q)|`.

The proof:

* `sum_w_dw`, `sum_bilinear`: expand `1[d₁d₂k ≡ a]` by `ind_eq`; the frequency `h = 0` cancels the units' term up to
  `E_w`.
* `norm_sum_B_le`: for frequencies `f_j` with weights `c_j`, Cauchy–Schwarz over `d₁` extends `d̄₁` to every residue,
  counted at most `m` times, and Parseval (`sum_norm_sq_le`) leaves the pairs `(j, d₂)`, `(j′, d₂′)` with
  `f_jd̄₂ = f_j′d̄₂′`.
* `diag_le`: on the integer frequencies `0 < |t| ≤ H`, with `2HDm < q`, that congruence is the equation `td₂′ = t′d₂`
  (`int_eq_of_cong`); `|c_t||β_{d₂}||c_{t′}||β_{d₂′}| ≤ ½(|c_t|²|β_{d₂′}|² + |c_{t′}|²|β_{d₂}|²)`, and for each
  `(t, d₂′)` the pairs `(t′, d₂)` number at most `F` (`card_fiber_le`). So the diagonal is at most
  `F(Σ|c|²)(Σ|β|²)`.
* `typeIB_bound`: the frequencies `0 < |t| ≤ H` by `norm_sum_B_le` and `diag_le`, with `c_t = ŵ(t)` and
  `Σ_t |ŵ(t)|² ≤ Σ_h |ŵ(h)|²` (the casts are distinct, `cast_injOn`); the others by `|B(h)| ≤ (Σ|α|)(Σ|β|)`
  (`norm_Bh_le`).

The weights themselves, intervals and splines, are in `SieveSpline.lean`.

The file imports `SieveFamily.lean` (for `dw`).
-/
import SieveFamily

open Finset Complex

namespace SieveTypeIB

variable {q : ℕ} [NeZero q]

/-! ### The additive characters of `ℤ/qℤ` -/

/-- `e(x) = e^{2πix/q}`. -/
noncomputable abbrev eq (x : ZMod q) : ℂ := ZMod.stdAddChar x

theorem eq_add (x y : ZMod q) : eq (x + y) = eq x * eq y := AddChar.map_add_eq_mul _ x y

theorem eq_zero : eq (0 : ZMod q) = 1 := AddChar.map_zero_eq_one _

theorem norm_eq (x : ZMod q) : ‖eq x‖ = 1 := by
  simp [eq, ZMod.stdAddChar_apply]

theorem eq_neg (x : ZMod q) : eq (-x) = (starRingEnd ℂ) (eq x) := by
  have h1 : eq (-x) * eq x = 1 := by rw [← eq_add, neg_add_cancel, eq_zero]
  have h2 : (starRingEnd ℂ) (eq x) * eq x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_eq]; simp
  have hx : eq x ≠ 0 := fun h => by simpa [h] using norm_eq x
  exact mul_right_cancel₀ hx (h1.trans h2.symm)

/-- **Orthogonality**: `Σ_h e(ht) = q·1[t = 0]`. -/
theorem sum_eq_mul (t : ZMod q) : ∑ h : ZMod q, eq (h * t) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · have hψ : ZMod.stdAddChar.mulShift t ≠ 1 := ZMod.isPrimitive_stdAddChar q ht
    have := AddChar.sum_eq_zero_of_ne_one hψ
    simpa [AddChar.mulShift_apply, mul_comm] using this

/-- `1[k = c] = q⁻¹Σ_h e(h(k − c))`. -/
theorem ind_eq (k c : ZMod q) : (if k = c then (1 : ℂ) else 0) = (q : ℂ)⁻¹ * ∑ h : ZMod q, eq (h * (k - c)) := by
  rw [sum_eq_mul]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  by_cases h : k = c
  · simp [h, hq]
  · simp [h, sub_eq_zero]

/-! ### Inverses of units in `ℤ/qℤ` -/

omit [NeZero q] in
theorem inv_mul_inv {x y : ZMod q} (hx : IsUnit x) (hy : IsUnit y) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  calc x * y * (x⁻¹ * y⁻¹) = (x * x⁻¹) * (y * y⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit x hx, ZMod.mul_inv_of_unit y hy, one_mul]

omit [NeZero q] in
theorem isUnit_inv {x : ZMod q} (hx : IsUnit x) : IsUnit x⁻¹ :=
  IsUnit.of_mul_eq_one x (by rw [mul_comm]; exact ZMod.mul_inv_of_unit x hx)

/-! ### The Fourier form of a weighted difference -/

/-- The weight's transform, `ŵ(h) = Σ_{k∈S} w(k)e(hk)`. -/
noncomputable def what (S : Finset ℕ) (w : ℕ → ℂ) (h : ZMod q) : ℂ := ∑ k ∈ S, w k * eq (h * (k : ZMod q))

/-- The weight on the units less its mean, `E_w = Σ_{k∈S} w(k)1[(k, q) = 1] − (φ(q)/q)Σ_{k∈S} w(k)`. -/
noncomputable def Ew (S : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ k ∈ S, w k * (if IsUnit (k : ZMod q) then 1 else 0) - (q.totient : ℂ) / q * ∑ k ∈ S, w k

omit [NeZero q] in
theorem isUnit_mul_iff {d k : ℕ} (hd : IsUnit (d : ZMod q)) :
    IsUnit (((d * k : ℕ) : ZMod q)) ↔ IsUnit (k : ZMod q) := by
  push_cast
  exact IsUnit.mul_iff.trans (and_iff_right hd)

/-- `Σ_{k∈S} w(k)·q⁻¹Σ_h e(h(k − c)) = q⁻¹Σ_h ŵ(h)e(−hc)`. -/
theorem sum_w_ind (S : Finset ℕ) (w : ℕ → ℂ) (c : ZMod q) :
    ∑ k ∈ S, w k * ((q : ℂ)⁻¹ * ∑ h : ZMod q, eq (h * ((k : ZMod q) - c))) =
      (q : ℂ)⁻¹ * ∑ h : ZMod q, what S w h * eq (-(h * c)) := by
  have hterm : ∀ k ∈ S, w k * ((q : ℂ)⁻¹ * ∑ h : ZMod q, eq (h * ((k : ZMod q) - c))) =
      ∑ h : ZMod q, (q : ℂ)⁻¹ * (w k * eq (h * (k : ZMod q)) * eq (-(h * c))) := by
    intro k _
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show h * ((k : ZMod q) - c) = h * k + -(h * c) by ring, eq_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [what, Finset.sum_mul, Finset.mul_sum]

/-- For `d` prime to `q`: `Σ_{k∈S} w(k)dw(dk) = q⁻¹Σ_{h≠0} ŵ(h)e(−had̄) − E_w/φ(q)`. -/
theorem sum_w_dw (a : ZMod q) {d : ℕ} (hd : IsUnit (d : ZMod q)) (S : Finset ℕ) (w : ℕ → ℂ) :
    ∑ k ∈ S, w k * SieveFamily.dw q a (d * k) =
      (q : ℂ)⁻¹ * ∑ h ∈ univ.filter (· ≠ (0 : ZMod q)), what S w h * eq (-(h * (a * (d : ZMod q)⁻¹))) -
        Ew (q := q) S w / q.totient := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  set c : ZMod q := a * (d : ZMod q)⁻¹ with hc
  -- the congruence `dk = a` is `k = c`
  have hcong : ∀ k : ℕ, ((((d * k : ℕ) : ZMod q)) = a) ↔ ((k : ZMod q) = c) := by
    intro k
    push_cast
    constructor
    · intro h
      rw [hc, ← h, mul_comm (d : ZMod q), mul_assoc, ZMod.mul_inv_of_unit _ hd, mul_one]
    · intro h
      rw [h, hc, mul_comm, mul_assoc, ZMod.inv_mul_of_unit _ hd, mul_one]
  -- the first count by orthogonality
  have hA : ∑ k ∈ S, w k * (if (((d * k : ℕ) : ZMod q)) = a then 1 else 0) =
      (q : ℂ)⁻¹ * ∑ h : ZMod q, what S w h * eq (-(h * c)) := by
    simp_rw [hcong, ind_eq]
    exact sum_w_ind S w c
  -- the term `h = 0`
  have hsplit : ∑ h : ZMod q, what S w h * eq (-(h * c)) =
      ∑ k ∈ S, w k + ∑ h ∈ univ.filter (· ≠ (0 : ZMod q)), what S w h * eq (-(h * c)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (· = (0 : ZMod q))]
    congr 1
    rw [Finset.filter_eq' univ (0 : ZMod q)]
    simp [what]
  unfold SieveFamily.dw
  simp_rw [mul_sub, Finset.sum_sub_distrib, hA, hsplit, isUnit_mul_iff hd]
  unfold Ew
  have : ∑ k ∈ S, w k * ((if IsUnit (k : ZMod q) then 1 else 0) / (q.totient : ℂ)) =
      (∑ k ∈ S, w k * (if IsUnit (k : ZMod q) then 1 else 0)) / q.totient := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  field_simp
  ring

/-! ### The bilinear form -/

/-- `B(h) = Σ_{d₁∈D₁}Σ_{d₂∈D₂} α(d₁)β(d₂)e(−had̄₁d̄₂)`. -/
noncomputable def Bh (a : ZMod q) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ) (h : ZMod q) : ℂ :=
  ∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * eq (-(h * (a * ((d₁ : ZMod q)⁻¹ * (d₂ : ZMod q)⁻¹))))

/-- **The bilinear sum in Fourier form**: for `D₁`, `D₂` prime to `q`,
`Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k) = q⁻¹Σ_{h≠0} ŵ(h)B(h) − (Σα)(Σβ)E_w/φ(q)`. -/
theorem sum_bilinear (a : ZMod q) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ)
    (hD₁ : ∀ d ∈ D₁, IsUnit (d : ZMod q)) (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (S : Finset ℕ) (w : ℕ → ℂ) :
    ∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * ∑ k ∈ S, w k * SieveFamily.dw q a (d₁ * d₂ * k) =
      (q : ℂ)⁻¹ * ∑ h ∈ univ.filter (· ≠ (0 : ZMod q)), what S w h * Bh a D₁ D₂ α β h -
        (∑ d ∈ D₁, α d) * (∑ d ∈ D₂, β d) * (Ew (q := q) S w / q.totient) := by
  set F := univ.filter (· ≠ (0 : ZMod q)) with hF
  set X : ℕ → ℕ → ZMod q → ℂ := fun d₁ d₂ h =>
    eq (-(h * (a * ((d₁ : ZMod q)⁻¹ * (d₂ : ZMod q)⁻¹)))) with hX
  have hterm : ∀ d₁ ∈ D₁, ∀ d₂ ∈ D₂, α d₁ * β d₂ * ∑ k ∈ S, w k * SieveFamily.dw q a (d₁ * d₂ * k) =
      (q : ℂ)⁻¹ * ∑ h ∈ F, what S w h * (α d₁ * β d₂ * X d₁ d₂ h) -
        α d₁ * β d₂ * (Ew (q := q) S w / q.totient) := by
    intro d₁ h₁ d₂ h₂
    have hu : IsUnit (((d₁ * d₂ : ℕ) : ZMod q)) := by push_cast; exact (hD₁ d₁ h₁).mul (hD₂ d₂ h₂)
    rw [sum_w_dw a hu S w, mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    have : ((d₁ * d₂ : ℕ) : ZMod q)⁻¹ = (d₁ : ZMod q)⁻¹ * (d₂ : ZMod q)⁻¹ := by
      push_cast; exact inv_mul_inv (hD₁ d₁ h₁) (hD₂ d₂ h₂)
    rw [hX]
    simp only
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun d₁ h₁ => Finset.sum_congr rfl fun d₂ h₂ => hterm d₁ h₁ d₂ h₂]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · simp only [← Finset.mul_sum]
    congr 1
    -- `Σ_{d₁}Σ_{d₂}Σ_h = Σ_hΣ_{d₁}Σ_{d₂}`
    rw [← Finset.sum_product', Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Bh, ← Finset.sum_product', Finset.mul_sum]
  · rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]

/-! ### Parseval's identity and Cauchy–Schwarz over `d₁` -/

/-- `|z|² = z·z̄`. -/
theorem sq_norm_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']; push_cast; ring

/-- **Parseval**: `Σ_r |Σ_{j∈J} c_je(rs_j)|² ≤ qΣ_{j,j′∈J, s_j = s_j′} |c_j||c_j′|`. -/
theorem sum_norm_sq_le {ι : Type*} (J : Finset ι) (c : ι → ℂ) (s : ι → ZMod q) :
    ∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 ≤
      q * ∑ j ∈ J, ∑ j' ∈ J, if s j = s j' then ‖c j‖ * ‖c j'‖ else 0 := by
  have h1 : ∀ r : ZMod q, ((‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ J, ∑ j' ∈ J, c j * (starRingEnd ℂ) (c j') * eq (r * (s j - s j')) := by
    intro r
    rw [sq_norm_eq, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [map_mul, ← eq_neg, show r * (s j - s j') = r * s j + -(r * s j') by ring, eq_add]
    ring
  have hC : ((∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 : ℝ) : ℂ) =
      (q : ℂ) * ∑ j ∈ J, ∑ j' ∈ J, if s j = s j' then c j * (starRingEnd ℂ) (c j') else 0 := by
    calc ((∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 : ℝ) : ℂ)
        = ∑ r : ZMod q, ∑ j ∈ J, ∑ j' ∈ J, c j * (starRingEnd ℂ) (c j') * eq (r * (s j - s j')) := by
          rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun r _ => h1 r
      _ = ∑ j ∈ J, ∑ j' ∈ J, ∑ r : ZMod q, c j * (starRingEnd ℂ) (c j') * eq (r * (s j - s j')) := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j ∈ J, ∑ j' ∈ J, c j * (starRingEnd ℂ) (c j') * (if s j - s j' = 0 then (q : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [← Finset.mul_sum, sum_eq_mul]
      _ = (q : ℂ) * ∑ j ∈ J, ∑ j' ∈ J, if s j = s j' then c j * (starRingEnd ℂ) (c j') else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          simp only [sub_eq_zero]
          split_ifs <;> ring
  have hx0 : 0 ≤ ∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 := Finset.sum_nonneg fun r _ => by positivity
  calc ∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2
      = ‖((∑ r : ZMod q, ‖∑ j ∈ J, c j * eq (r * s j)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    _ = ‖(q : ℂ) * ∑ j ∈ J, ∑ j' ∈ J, if s j = s j' then c j * (starRingEnd ℂ) (c j') else 0‖ := by rw [hC]
    _ ≤ q * ∑ j ∈ J, ∑ j' ∈ J, if s j = s j' then ‖c j‖ * ‖c j'‖ else 0 := by
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j' _ => ?_))
        split_ifs <;> simp

/-- **Cauchy–Schwarz over `d₁`, then Parseval.** For frequencies `f j` with weights `c j`, if every residue is the
inverse of at most `m` elements of `D₁`, then `|Σ_j c_jB(f_j)| ≤ (Σ|α|²)^{1/2}(m·qΣ_{x,y})^{1/2}`, the sum over the
pairs `x, y ∈ J × D₂` with `f_{x₁}d̄_{x₂} = f_{y₁}d̄_{y₂}` of `|c_{x₁}β(x₂)||c_{y₁}β(y₂)|`. -/
theorem norm_sum_B_le (a : ZMod q) (ha : IsUnit a) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ) {ι : Type*} (J : Finset ι)
    (f : ι → ZMod q) (c : ι → ℂ) {m : ℕ}
    (hm : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m) :
    ‖∑ j ∈ J, c j * Bh a D₁ D₂ α β (f j)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * (q * ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        if f x.1 * (x.2 : ZMod q)⁻¹ = f y.1 * (y.2 : ZMod q)⁻¹ then ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0)) := by
  set s : ι × ℕ → ZMod q := fun x => -(f x.1 * (a * (x.2 : ZMod q)⁻¹)) with hs
  set G : ZMod q → ℂ := fun r => ∑ x ∈ J ×ˢ D₂, (c x.1 * β x.2) * eq (r * s x) with hG
  -- the sum as `Σ_{d₁} α(d₁)G(d̄₁)`
  have hsum : ∑ j ∈ J, c j * Bh a D₁ D₂ α β (f j) = ∑ d₁ ∈ D₁, α d₁ * G ((d₁ : ZMod q)⁻¹) := by
    simp only [Bh, hG, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d₂ _ => ?_
    simp only [hs]
    rw [show -(f j * (a * ((d₁ : ZMod q)⁻¹ * (d₂ : ZMod q)⁻¹))) =
      (d₁ : ZMod q)⁻¹ * -(f j * (a * (d₂ : ZMod q)⁻¹)) by ring]
    ring
  rw [hsum]
  -- Cauchy–Schwarz over `d₁`
  have hCS : ‖∑ d₁ ∈ D₁, α d₁ * G ((d₁ : ZMod q)⁻¹)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(∑ d ∈ D₁, ‖G ((d : ZMod q)⁻¹)‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  -- the fibres of `d ↦ d̄`
  have hfib : ∑ d ∈ D₁, ‖G ((d : ZMod q)⁻¹)‖ ^ 2 ≤ m * ∑ r : ZMod q, ‖G r‖ ^ 2 := by
    rw [← Finset.sum_fiberwise' D₁ (fun d => ((d : ZMod q)⁻¹)) (fun r => ‖G r‖ ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm r) (by positivity)
  -- Parseval, and the diagonal `s x = s y` as `f x₁ d̄ = f y₁ d̄′`
  have hP := sum_norm_sq_le (J ×ˢ D₂) (fun x => c x.1 * β x.2) s
  have hdiag : ∀ x y : ι × ℕ, (s x = s y) ↔ (f x.1 * (x.2 : ZMod q)⁻¹ = f y.1 * (y.2 : ZMod q)⁻¹) := by
    intro x y
    have hai : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
    simp only [hs, neg_inj]
    constructor
    · intro h
      have := congrArg (fun z => a⁻¹ * z) h
      calc f x.1 * (x.2 : ZMod q)⁻¹ = (a⁻¹ * a) * (f x.1 * (x.2 : ZMod q)⁻¹) := by rw [hai, one_mul]
        _ = a⁻¹ * (f x.1 * (a * (x.2 : ZMod q)⁻¹)) := by ring
        _ = a⁻¹ * (f y.1 * (a * (y.2 : ZMod q)⁻¹)) := this
        _ = (a⁻¹ * a) * (f y.1 * (y.2 : ZMod q)⁻¹) := by ring
        _ = f y.1 * (y.2 : ZMod q)⁻¹ := by rw [hai, one_mul]
    · intro h
      calc f x.1 * (a * (x.2 : ZMod q)⁻¹) = a * (f x.1 * (x.2 : ZMod q)⁻¹) := by ring
        _ = a * (f y.1 * (y.2 : ZMod q)⁻¹) := by rw [h]
        _ = f y.1 * (a * (y.2 : ZMod q)⁻¹) := by ring
  have hP' : ∑ r : ZMod q, ‖G r‖ ^ 2 ≤ q * ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
      if f x.1 * (x.2 : ZMod q)⁻¹ = f y.1 * (y.2 : ZMod q)⁻¹ then ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0 := by
    refine hP.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => if_congr (hdiag x y) rfl rfl
  calc ‖∑ d₁ ∈ D₁, α d₁ * G ((d₁ : ZMod q)⁻¹)‖
      ≤ √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(∑ d ∈ D₁, ‖G ((d : ZMod q)⁻¹)‖ ^ 2) := hCS
    _ ≤ √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * (q * ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        if f x.1 * (x.2 : ZMod q)⁻¹ = f y.1 * (y.2 : ZMod q)⁻¹ then ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖
          else 0)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        exact hfib.trans (mul_le_mul_of_nonneg_left hP' (Nat.cast_nonneg m))

/-! ### The diagonal -/

/-- For `t ≠ 0` and `d′ ≥ 1`, the pairs `(t′, d)` of `J × D₂` with `t′d = td′` number at most the divisors of
`|t|d′`. -/
theorem card_fiber_le (J : Finset ℤ) (D₂ : Finset ℕ) {t : ℤ} {d' : ℕ} (ht : t ≠ 0) (hd' : 0 < d')
    (hD₂ : ∀ d ∈ D₂, 0 < d) :
    #((J ×ˢ D₂).filter (fun y => y.1 * (y.2 : ℤ) = t * d')) ≤ (t.natAbs * d').divisors.card := by
  refine Finset.card_le_card_of_injOn (fun y => y.2) ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hy
    simp only [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, by positivity⟩
    have h : (y.2 : ℤ) ∣ t * d' := ⟨y.1, by rw [← hy.2]; ring⟩
    have := Int.natAbs_dvd_natAbs.2 h
    simpa [Int.natAbs_mul] using this
  · intro y hy z hz hyz
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hy hz
    simp only at hyz
    have hy2 : (0 : ℤ) < y.2 := by exact_mod_cast hD₂ y.2 hy.1.2
    have h1 : y.1 * (y.2 : ℤ) = z.1 * (y.2 : ℤ) := by rw [hy.2, hyz, hz.2]
    have h2 : y.1 = z.1 := mul_right_cancel₀ hy2.ne' h1
    exact Prod.ext h2 hyz

omit [NeZero q] in
/-- On the frequencies `0 < |t| ≤ H` and `D₂ ⊆ [1, Dm]` prime to `q`, with `2HDm < q`, the congruence
`t·d̄ = t′·d̄′` is the equation `td′ = t′d` in the integers. -/
theorem int_eq_of_cong {H Dm : ℕ} (hq : 2 * H * Dm < q) {t t' : ℤ} {d d' : ℕ} (ht : t.natAbs ≤ H)
    (ht' : t'.natAbs ≤ H) (hd : d ≤ Dm) (hd' : d' ≤ Dm) (hu : IsUnit (d : ZMod q)) (hu' : IsUnit (d' : ZMod q))
    (h : (t : ZMod q) * (d : ZMod q)⁻¹ = (t' : ZMod q) * (d' : ZMod q)⁻¹) : t * d' = t' * d := by
  have h1 : ((t * d' - t' * d : ℤ) : ZMod q) = 0 := by
    push_cast
    calc (t : ZMod q) * d' - t' * d
        = ((t : ZMod q) * (d : ZMod q)⁻¹ - (t' : ZMod q) * (d' : ZMod q)⁻¹) * (d * d') := by
          rw [sub_mul]
          congr 1
          · rw [show (t : ZMod q) * (d : ZMod q)⁻¹ * (d * d') = t * d' * ((d : ZMod q)⁻¹ * d) by ring,
              ZMod.inv_mul_of_unit _ hu, mul_one]
          · rw [show (t' : ZMod q) * (d' : ZMod q)⁻¹ * (d * d') = t' * d * ((d' : ZMod q)⁻¹ * d') by ring,
              ZMod.inv_mul_of_unit _ hu', mul_one]
      _ = 0 := by rw [h, sub_self, zero_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have hlt : |t * d' - t' * d| < q := by
    have e1 : |t * (d' : ℤ)| ≤ (H : ℤ) * Dm := by
      rw [abs_mul, Int.abs_natCast]
      have : |t| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht
      exact mul_le_mul this (by exact_mod_cast hd') (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have e2 : |t' * (d : ℤ)| ≤ (H : ℤ) * Dm := by
      rw [abs_mul, Int.abs_natCast]
      have : |t'| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht'
      exact mul_le_mul this (by exact_mod_cast hd) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hq' : (2 * H * Dm : ℤ) < q := by exact_mod_cast hq
    calc |t * d' - t' * d| ≤ |t * (d' : ℤ)| + |t' * (d : ℤ)| := abs_sub _ _
      _ < q := by linarith
  have := Int.eq_zero_of_abs_lt_dvd h1 hlt
  linarith

/-- Reindexing `(x, y) ↦ ((x₁, y₂), (y₁, x₂))` of a sum over `(J × D₂)²`. -/
theorem sum_swap4 (J : Finset ℤ) (D₂ : Finset ℕ) (φ : ℤ → ℕ → ℤ → ℕ → ℝ) :
    ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂, φ x.1 x.2 y.1 y.2 =
      ∑ t ∈ J, ∑ d' ∈ D₂, ∑ y ∈ J ×ˢ D₂, φ t y.2 y.1 d' := by
  simp only [Finset.sum_product]
  refine Finset.sum_congr rfl fun t _ => ?_
  -- `Σ_dΣ_{t′}Σ_{d′} = Σ_{d′}Σ_{t′}Σ_d`
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t' _ => Finset.sum_comm]
  rw [Finset.sum_comm]

omit [NeZero q] in
/-- **The diagonal.** For integer frequencies `t ∈ J` with `0 < |t| ≤ H`, and `D₂ ⊆ [1, Dm]` prime to `q` with
`2HDm < q`, if every `|t|d` (`t ∈ J`, `d ∈ D₂`) has at most `F` divisors, the diagonal sum of `norm_sum_B_le` at
`f = (·)` is at most `F(Σ_{t∈J}|c_t|²)(Σ_{d∈D₂}|β(d)|²)`. By `int_eq_of_cong` the congruence is `td′ = t′d`; then
`|c_t||β_d||c_{t′}||β_{d′}| ≤ ½(|c_t|²|β_{d′}|² + |c_{t′}|²|β_d|²)`, the two halves are equal by the symmetry of the
equation, and for each `(t, d′)` the pairs `(t′, d)` with `t′d = td′` number at most `F` (`card_fiber_le`). -/
theorem diag_le (J : Finset ℤ) (c : ℤ → ℂ) (D₂ : Finset ℕ) (β : ℕ → ℂ) {H Dm F : ℕ}
    (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d) (hDm : ∀ d ∈ D₂, d ≤ Dm)
    (hJ : ∀ t ∈ J, t ≠ 0 ∧ t.natAbs ≤ H) (hq : 2 * H * Dm < q)
    (hF : ∀ t ∈ J, ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F) :
    ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
          ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0) ≤
      F * ((∑ t ∈ J, ‖c t‖ ^ 2) * (∑ d ∈ D₂, ‖β d‖ ^ 2)) := by
  set g : ℤ → ℕ → ℝ := fun t d => ‖c t‖ ^ 2 * ‖β d‖ ^ 2 with hg
  have hg0 : ∀ t d, 0 ≤ g t d := fun t d => by rw [hg]; positivity
  -- each term is at most half the two squares, on the integer equation
  have hterm : ∀ x ∈ J ×ˢ D₂, ∀ y ∈ J ×ˢ D₂,
      (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
        ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0) ≤
      (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g x.1 y.2 / 2 else 0) +
        (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g y.1 x.2 / 2 else 0) := by
    intro x hx y hy
    rw [Finset.mem_product] at hx hy
    by_cases h1 : ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹
    · have h2 : x.1 * (y.2 : ℤ) = y.1 * x.2 := int_eq_of_cong hq (hJ _ hx.1).2 (hJ _ hy.1).2 (hDm _ hx.2)
        (hDm _ hy.2) (hD₂ _ hx.2) (hD₂ _ hy.2) h1
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h2]
      have e : ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ = (‖c x.1‖ * ‖β y.2‖) * (‖c y.1‖ * ‖β x.2‖) := by
        rw [norm_mul, norm_mul]; ring
      rw [e, hg]
      nlinarith [sq_nonneg (‖c x.1‖ * ‖β y.2‖ - ‖c y.1‖ * ‖β x.2‖)]
    · rw [ite_eq_right h1]
      have := hg0 x.1 y.2
      have := hg0 y.1 x.2
      split_ifs <;> linarith
  -- the second half equals the first, by symmetry
  have hsym : ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂, (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g y.1 x.2 / 2 else 0) =
      ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂, (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g x.1 y.2 / 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    exact if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl
  -- the fibres
  have hfib : ∀ t ∈ J, ∀ d' ∈ D₂, ∑ y ∈ J ×ˢ D₂, (if t * (d' : ℤ) = y.1 * y.2 then g t d' else 0) ≤ F * g t d' := by
    intro t ht d' hd'
    have hcard := card_fiber_le J D₂ (t := t) (d' := d') (hJ t ht).1 (hD₂0 d' hd') hD₂0
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hg0 t d')
    have hsame : (J ×ˢ D₂).filter (fun y => t * (d' : ℤ) = y.1 * y.2) =
        (J ×ˢ D₂).filter (fun y => y.1 * (y.2 : ℤ) = t * d') := by
      ext y; simp only [Finset.mem_filter]; exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
    rw [hsame]
    exact_mod_cast hcard.trans (hF t ht d' hd')
  calc ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂,
        (if ((x.1 : ZMod q)) * (x.2 : ZMod q)⁻¹ = ((y.1 : ZMod q)) * (y.2 : ZMod q)⁻¹ then
          ‖c x.1 * β x.2‖ * ‖c y.1 * β y.2‖ else 0)
      ≤ ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂, ((if x.1 * (y.2 : ℤ) = y.1 * x.2 then g x.1 y.2 / 2 else 0) +
          (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g y.1 x.2 / 2 else 0)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
    _ = ∑ x ∈ J ×ˢ D₂, ∑ y ∈ J ×ˢ D₂, (if x.1 * (y.2 : ℤ) = y.1 * x.2 then g x.1 y.2 else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [hsym, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
    _ = ∑ t ∈ J, ∑ d' ∈ D₂, ∑ y ∈ J ×ˢ D₂, (if t * (d' : ℤ) = y.1 * y.2 then g t d' else 0) :=
        sum_swap4 J D₂ (fun t d t' d' => if t * (d' : ℤ) = t' * d then g t d' else 0)
    _ ≤ ∑ t ∈ J, ∑ d' ∈ D₂, F * g t d' :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun d' hd' => hfib t ht d' hd'
    _ = F * ((∑ t ∈ J, ‖c t‖ ^ 2) * (∑ d ∈ D₂, ‖β d‖ ^ 2)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]

/-! ### The estimate -/

/-- The small frequencies, `0 < |t| ≤ H`. -/
def Jset (H : ℕ) : Finset ℤ := (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0)

theorem mem_Jset {H : ℕ} {t : ℤ} : t ∈ Jset H ↔ t ≠ 0 ∧ t.natAbs ≤ H := by
  simp only [Jset, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, h4⟩
    exact ⟨⟨by omega, by omega⟩, h3⟩

omit [NeZero q] in
/-- For `2H < q`, the casts of `[−H, H]` to `ℤ/qℤ` are distinct. -/
theorem cast_injOn {H : ℕ} (hq : 2 * H < q) : Set.InjOn (fun t : ℤ => (t : ZMod q)) (Jset H : Set ℤ) := by
  intro t ht t' ht' h
  rw [Finset.mem_coe, mem_Jset] at ht ht'
  simp only at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hlt : |t' - t| < q := by
    have hq' : (2 * H : ℤ) < q := by exact_mod_cast hq
    have h1 : |t'| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht'.2
    have h2 : |t| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht.2
    calc |t' - t| ≤ |t'| + |t| := abs_sub _ _
      _ < q := by linarith
  have := Int.eq_zero_of_abs_lt_dvd h hlt
  linarith

omit [NeZero q] in
/-- For `2H < q`, the casts of `0 < |t| ≤ H` are not `0`. -/
theorem cast_ne_zero {H : ℕ} (hq : 2 * H < q) {t : ℤ} (ht : t ∈ Jset H) : (t : ZMod q) ≠ 0 := by
  rw [mem_Jset] at ht
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hlt : |t| < q := by
    have : |t| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht.2
    have hq' : (2 * H : ℤ) < q := by exact_mod_cast hq
    have : (0 : ℤ) ≤ H := Nat.cast_nonneg H
    linarith
  exact ht.1 (Int.eq_zero_of_abs_lt_dvd h hlt)

theorem norm_Bh_le (a : ZMod q) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ) (h : ZMod q) :
    ‖Bh a D₁ D₂ α β h‖ ≤ (∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖) := by
  unfold Bh
  rw [Finset.sum_mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d₁ _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun d₂ _ => ?_))
  rw [norm_mul, norm_mul, norm_eq, mul_one]

/-- **The bilinear Type I estimate.** Let `a` be a unit mod `q`, `D₁` and `D₂` sets of naturals prime to `q`, `D₂ ⊆
[1, Dm]` with `Dm ≥ 1` and `2HDm < q`, every residue the inverse of at most `m` elements of `D₁`, every `|t|d` with
`0 < |t| ≤ H` and `d ∈ D₂` with at most `F` divisors, and `|ŵ(h)| ≤ W` at the other frequencies `h ≠ 0`. Then
`|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_{k∈S} w(k)dw(d₁d₂k)|` is at most
`(Σ|α|²)^{1/2}(mF(Σ|β|²)·q⁻¹Σ_h|ŵ(h)|²)^{1/2} + W(Σ|α|)(Σ|β|) + |(Σα)(Σβ)E_w/φ(q)|`.

The proof: `sum_bilinear`; the frequencies `0 < |t| ≤ H` by `norm_sum_B_le` and `diag_le`, the others by
`norm_Bh_le`. -/
theorem typeIB_bound (a : ZMod q) (ha : IsUnit a) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ)
    (hD₁ : ∀ d ∈ D₁, IsUnit (d : ZMod q)) (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d)
    (S : Finset ℕ) (w : ℕ → ℂ) {H Dm F m : ℕ} {W : ℝ} (hW0 : 0 ≤ W)
    (hDm : ∀ d ∈ D₂, d ≤ Dm) (hDm1 : 1 ≤ Dm) (hq : 2 * H * Dm < q)
    (hm : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F)
    (hW : ∀ h : ZMod q, h ≠ 0 → h ∉ (Jset H).image (fun t : ℤ => (t : ZMod q)) → ‖what S w h‖ ≤ W) :
    ‖∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * ∑ k ∈ S, w k * SieveFamily.dw q a (d₁ * d₂ * k)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * F * (∑ d ∈ D₂, ‖β d‖ ^ 2) * ((q : ℝ)⁻¹ * ∑ h : ZMod q, ‖what S w h‖ ^ 2)) +
        W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) +
        ‖(∑ d ∈ D₁, α d) * (∑ d ∈ D₂, β d) * (Ew (q := q) S w / q.totient)‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq2 : 2 * H < q := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hDm1) hq
  set Fz := univ.filter (· ≠ (0 : ZMod q)) with hFz
  set I := (Jset H).image (fun t : ℤ => (t : ZMod q)) with hI
  set Y := ∑ h : ZMod q, ‖what S w h‖ ^ 2 with hY
  set Z := ∑ d ∈ D₂, ‖β d‖ ^ 2 with hZ
  rw [sum_bilinear a D₁ D₂ α β hD₁ hD₂ S w]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  -- split the frequencies
  rw [← Finset.sum_filter_add_sum_filter_not Fz (· ∈ I), mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the small frequencies, as the integers of `Jset H`
    have hsub : Fz.filter (· ∈ I) = I := by
      ext h
      simp only [hFz, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hh => hh.2
      · intro hh
        refine ⟨?_, hh⟩
        rw [hI, Finset.mem_image] at hh
        obtain ⟨t, ht, rfl⟩ := hh
        exact cast_ne_zero hq2 ht
    rw [hsub, hI, Finset.sum_image (cast_injOn hq2)]
    have hB := norm_sum_B_le a ha D₁ D₂ α β (Jset H) (fun t : ℤ => (t : ZMod q))
      (fun t : ℤ => what S w (t : ZMod q)) hm
    have hD := diag_le (q := q) (Jset H) (fun t : ℤ => what S w (t : ZMod q)) D₂ β hD₂ hD₂0 hDm
      (fun t ht => mem_Jset.1 ht) hq (fun t ht d hd => hF t (mem_Jset.1 ht).1 (mem_Jset.1 ht).2 d hd)
    have hJY : ∑ t ∈ Jset H, ‖what S w (t : ZMod q)‖ ^ 2 ≤ Y := by
      rw [hY, ← Finset.sum_image (f := fun h : ZMod q => ‖what S w h‖ ^ 2) (cast_injOn hq2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun h _ _ => by positivity
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun h _ => by positivity
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun d _ => by positivity
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (q : ℝ)⁻¹ * ‖∑ t ∈ Jset H, what S w (t : ZMod q) * Bh a D₁ D₂ α β (t : ZMod q)‖
        ≤ (q : ℝ)⁻¹ * (√(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * (q * (F * (Y * Z))))) := by
          refine mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
            (Real.sqrt_nonneg _))) (by positivity)
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD.trans ?_) hq0.le) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJY hZ0) (Nat.cast_nonneg _)
      _ = √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * F * Z * ((q : ℝ)⁻¹ * Y)) := by
          rw [mul_left_comm]
          congr 1
          rw [show (m : ℝ) * (q * (F * (Y * Z))) = q ^ 2 * (m * F * Z * ((q : ℝ)⁻¹ * Y)) by
            field_simp]
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq0.le]
          field_simp
  · -- the other frequencies
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hcard : (#(Fz.filter (· ∉ I)) : ℝ) ≤ q := by
      have : #(Fz.filter (· ∉ I)) ≤ q := (Finset.card_le_univ _).trans (by rw [ZMod.card])
      exact_mod_cast this
    calc (q : ℝ)⁻¹ * ‖∑ h ∈ Fz.filter (· ∉ I), what S w h * Bh a D₁ D₂ α β h‖
        ≤ (q : ℝ)⁻¹ * ∑ h ∈ Fz.filter (· ∉ I), W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_))
            (by positivity)
          rw [Finset.mem_filter, hFz, Finset.mem_filter] at hh
          rw [norm_mul]
          exact mul_le_mul (hW h hh.1.2 hh.2) (norm_Bh_le a D₁ D₂ α β h) (norm_nonneg _) hW0
      _ ≤ W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
          have hX : 0 ≤ W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := by positivity
          calc (q : ℝ)⁻¹ * #(Fz.filter (· ∉ I)) * (W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)))
              ≤ 1 * (W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖))) := by
                refine mul_le_mul_of_nonneg_right ?_ hX
                rw [inv_mul_le_iff₀ hq0, mul_one]; exact hcard
            _ = W * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) := one_mul _

end SieveTypeIB
