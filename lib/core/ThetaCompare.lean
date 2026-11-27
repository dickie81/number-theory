import ThetaHeis
import ChainCanon
import EllipticDivisor

/-!
# The standard theta space is a line, and the comparison `θ = c·Θ_g`

D1b-2 of the D1b plan, with no `dim Th = 1` input: for the canonical CM lattice `Lc = δ(ℤ + ℤω)`
(`ChainCanon.cmLat`, `ω = (1 + √−d)/2`, `Δ(Lc) = 1`), the form `s = 1/area(Lc)` and the point `t = δ/2`, the theta
space of `Lc^ι` is the line `ℂ·F0`, `F0(z) = Π_i th0_t(z_i)` (`eq_smul_F0c`), and every `θ ∈ Th(C)`, `C` a self-dual
theta lattice, is a multiple of the adapted model theta `Θ_g = (Iop(Lc^ι, g⁻¹C) F0) ∘ g⁻¹` for every `H`-isometry `g`
with `g(Lc^ι)` commensurable with `C` (`theta_compare`).

**The standard lattice.** For `u = δ(a + bω)`, `v = δ(c + eω)` in `Lc`, `s·u·v̄ = (a + bω)(c + eω̄)/sd`, so
`Im(s·u·v̄) = bc − ae`, `2·sd·Re(s·u·v̄) = (bc − ae) + 2(ac + ae + beN)` and `sd·s·|u|² = a² + ab + b²N`, with
`N = (1 + d)/4` (`pair_cmLat`, `norm_cmLat`). So `Lc^ι` is a theta lattice (`isThetaLat_stdLc`, by
`ThetaHeis.isThetaLat_of_int`), with `α(x) = (−1)^{Σ N(a_i + b_iω)}`.

**`F0 ∈ Th(Lc^ι)` needs `d ≡ 7 (mod 8)`** (`F0c_mem_Th`). The stabiliser of `F0` in the theta lattice `Lc^ι` is a
subgroup (`ThetaHeis.mem_Th_of_le_closure`), so it suffices to check the generators `δ·e_i` and `δω·e_i`. At a basis
period `l` (`l/2 ∉ Lc`) the constant of `σ_W(z + l) = C·e^{η(l)z}σ_W(z)` (`EllipticAdd.sigmaW_add_lattice`, with
Masser's quasi-periods `η(l) = s₂l + (π/A)·l̄`, `CMThetaOne.zetaW_add_lattice`, unconditional by
`EllipticLegendre.legendre`) is `C = −e^{η(l)l/2}`, read at `z = −l/2` (`σ_W` is odd), so
`σ*(z + l) = −e^{(π/A)·l̄(z + l/2)}σ*(z)` (`sgStar_add_period`) and `th0_t(w + l)·e^{−(π/A)(w l̄ + |l|²/2)} =
−e^{(π/A)(l̄t − t̄l)}·th0_t(w)` (`th0L_add_period`). At `l = δ` the phase is `1` and `α(δ) = −1`; at `l = δω` the
phase is `e^{−πi} = −1` and `α(δω) = (−1)^N`. So both generators fix `F0` exactly when `N = (1 + d)/4` is even, that
is `d ≡ 7 (mod 8)` (2 splits in `K₀`). For `d ≡ 3 (mod 8)` the point would be `δω/2`.

**One variable** (`eq_mul_th0L`). If `f` is entire and has the multipliers of `th0_t` on `Lc`, then `f/th0_t(· − t)`
shifted by `t` is elliptic, holomorphic off the lattice, with at most a simple pole at `0` (the zeros of `σ*` are the
periods, simple: `σ*(v) = v·sigP(v)·e^{−s₂v²/2}`, `sigP(0) = 1`). So it is constant
(`EllipticDivisor.EllPole.lower_one`, `EllipticDivisor.EllPole.eq_const`), and `f = f(0)·th0_t` off a countable set,
hence everywhere. **Many variables** (`eq_smul_F0c`): restricted to one coordinate, `G ∈ Th(Lc^ι)` has the multipliers
of `th0_t`, and an induction over the coordinates gives `G = G(0)·F0`.

**The comparison** (`theta_compare`). Transport along `g` (`ThetaHeis.comp_mem_Th`) gives `θ ∘ g ∈ Th(g⁻¹C)`, and
`Iop(g⁻¹C, Lc^ι)(θ ∘ g) ∈ Th(Lc^ι)` (`ThetaHeis.Iop_mem_Th`) is `a·F0`; going back (`ThetaHeis.Iop_Iop_eq_smul`, `g⁻¹C`
self-dual) gives `√idx·(θ ∘ g) = a·Iop(Lc^ι, g⁻¹C) F0`, so `θ = (a/√idx)·Θ_g`. Only the self-duality of `C` is used, and
the hypothesis `Squarefree d` of the statements is not. The moved theta of the chain lies in `Th(La(N, N′))` when the
three lattices of `ThetaChain.thMoved` are commensurable theta lattices (`thMoved_mem_Th`).

**Main declarations:** `stdLc`, `F0c`, `thetaAdapt`, `isThetaLat_stdLc`, `F0c_mem_Th`, `eq_smul_F0c`,
`theta_compare`, `thMoved_mem_Th`.
-/

namespace ThetaCompare

open ThetaChain ThetaNorm ThetaHeis ChainCanon CMThetaOne EllipticAdd EllipticDivisor Complex

noncomputable section

/-! ## The canonical lattice in coordinates -/

section Setup

variable {d : ℕ} {sd : ℝ}

/-- **`sd > 0`** for `d ≡ 7 (mod 8)`. -/
theorem sd_pos8 (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) : 0 < sd := sd_pos (by omega) hsd

/-- **`4·sd² = d`.** -/
theorem sd_sq (hsd : sd = Real.sqrt d / 2) : 4 * sd ^ 2 = d := by
  rw [hsd, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

/-- **`area(Lc) = |δ|²·sd`.** -/
theorem area_cmLat (hsd0 : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) : area (cmLat sd) = normSq (deltaC sd) * sd := by
  obtain ⟨h1, h2⟩ := cmLat_ω hsd0.ne' hΔ
  have hc : starRingEnd ℂ (deltaC sd) * (deltaC sd * omegaD sd) = (normSq (deltaC sd) : ℂ) * omegaD sd := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have him : (omegaD sd).im = sd := by simp [omegaD]
  rw [area, h1, h2, hc, Complex.im_ofReal_mul, him]
  exact abs_of_pos (mul_pos (Complex.normSq_pos.mpr (deltaC_ne_zero hΔ)) hsd0)

/-- **`s·|δ|²·sd = 1`.** -/
theorem sC_mul_normSq (hsd0 : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) :
    sC sd * normSq (deltaC sd) * sd = 1 := by
  rw [sC, area_cmLat hsd0 hΔ, mul_assoc]
  exact inv_mul_cancel₀ (mul_pos (Complex.normSq_pos.mpr (deltaC_ne_zero hΔ)) hsd0).ne'

/-- **The points of `Lc`**: `δ(a + bω)`, `a, b ∈ ℤ`. -/
theorem mem_cmLat_iff (hsd0 : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) {l : ℂ} :
    l ∈ (cmLat sd).lattice ↔ ∃ a b : ℤ, l = deltaC sd * (a + b * omegaD sd) := by
  obtain ⟨h1, h2⟩ := cmLat_ω hsd0.ne' hΔ
  rw [PeriodPair.lattice, Submodule.mem_span_pair, h1, h2]
  refine ⟨fun ⟨a, b, h⟩ => ⟨a, b, by rw [← h, zsmul_eq_mul, zsmul_eq_mul]; ring⟩,
    fun ⟨a, b, h⟩ => ⟨a, b, by rw [h, zsmul_eq_mul, zsmul_eq_mul]; ring⟩⟩

/-- **The form on `Lc` in coordinates**: `s·u·v̄ = (a + bω)(c + eω̄)/sd` for `u = δ(a + bω)`, `v = δ(c + eω)`. -/
theorem pair_coord (hsd0 : 0 < sd) (hΔ : discr (baseLat sd) ≠ 0) (a b c e : ℤ) :
    (sC sd : ℂ) * (deltaC sd * (a + b * omegaD sd) * starRingEnd ℂ (deltaC sd * (c + e * omegaD sd))) =
      (((a + b / 2) * (c + e / 2) / sd + b * e * sd : ℝ) : ℂ) + ((b * c - a * e : ℤ) : ℂ) * I := by
  have h := sC_mul_normSq hsd0 hΔ
  have hn : (starRingEnd ℂ (deltaC sd) * deltaC sd : ℂ) = (normSq (deltaC sd) : ℂ) :=
    (Complex.normSq_eq_conj_mul_self).symm
  have hs : (sd : ℂ) ≠ 0 := by exact_mod_cast hsd0.ne'
  have hC : (sC sd : ℂ) * (normSq (deltaC sd) : ℂ) = 1 / sd := by
    rw [eq_div_iff hs]
    exact_mod_cast h
  simp only [map_mul, map_add, map_intCast, omegaD, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  calc (sC sd : ℂ) * (deltaC sd * (a + b * (1 / 2 + sd * I)) *
        (starRingEnd ℂ (deltaC sd) * (c + e * (1 / 2 + sd * -I))))
      = ((sC sd : ℂ) * (starRingEnd ℂ (deltaC sd) * deltaC sd)) *
          ((a + b * (1 / 2 + sd * I)) * (c + e * (1 / 2 + sd * -I))) := by ring
    _ = _ := by
      rw [hn, hC]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring

end Setup

/-! ## `Lc^ι` is a theta lattice -/

section Std

variable {d : ℕ} {sd : ℝ}

/-- **The form on `Lc` is integral, with the parity of a theta lattice**: `Im(s·u·v̄) = n ∈ ℤ` and
`2·sd·Re(s·u·v̄) = n + 2k`, `k ∈ ℤ` (`4 ∣ 1 + d` makes `be(1 + d)/2` even). -/
theorem pair_cmLat (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) {u v : ℂ}
    (hu : u ∈ (cmLat sd).lattice) (hv : v ∈ (cmLat sd).lattice) :
    ∃ n k : ℤ, ((sC sd : ℂ) * (u * starRingEnd ℂ v)).im = n ∧
      sd * (2 * ((sC sd : ℂ) * (u * starRingEnd ℂ v)).re) = n + 2 * k := by
  have hsd0 := sd_pos8 hd8 hsd
  obtain ⟨a, b, rfl⟩ := (mem_cmLat_iff hsd0 hΔ).mp hu
  obtain ⟨c, e, rfl⟩ := (mem_cmLat_iff hsd0 hΔ).mp hv
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d + 1 = 8 * j := ⟨(d + 1) / 8, by omega⟩
  have hj' : (d : ℝ) + 1 = 8 * j := by exact_mod_cast hj
  have h4 := sd_sq hsd
  refine ⟨b * c - a * e, a * c + a * e + 2 * b * e * j, ?_, ?_⟩ <;> rw [pair_coord hsd0 hΔ] <;>
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im]
  · push_cast
    ring
  · push_cast
    field_simp
    linear_combination ((b : ℝ) * e) * h4 + ((b : ℝ) * e) * hj'

/-- **The norm form on `Lc` is integral**: `sd·s·|u|² = a² + ab + b²(1 + d)/4 ∈ ℤ`. -/
theorem norm_cmLat (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) {u : ℂ}
    (hu : u ∈ (cmLat sd).lattice) : ∃ m : ℤ, sd * ((sC sd : ℂ) * (u * starRingEnd ℂ u)).re = m := by
  have hsd0 := sd_pos8 hd8 hsd
  obtain ⟨a, b, rfl⟩ := (mem_cmLat_iff hsd0 hΔ).mp hu
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d + 1 = 8 * j := ⟨(d + 1) / 8, by omega⟩
  have hj' : (d : ℝ) + 1 = 8 * j := by exact_mod_cast hj
  have h4 := sd_sq hsd
  refine ⟨a ^ 2 + a * b + 2 * b ^ 2 * j, ?_⟩
  rw [pair_coord hsd0 hΔ]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  field_simp
  linear_combination (b : ℝ) ^ 2 * h4 + (b : ℝ) ^ 2 * hj'

/-- **The standard lattice `Lc^ι`** of `F0`. -/
def stdLc (sd : ℝ) (ι : Type*) : AddSubgroup (ι → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => (cmLat sd).lattice.toAddSubgroup

/-- **Membership in `Lc^ι`** is coordinatewise. -/
theorem mem_stdLc {ι : Type*} {x : ι → ℂ} : x ∈ stdLc sd ι ↔ ∀ i, x i ∈ (cmLat sd).lattice := by
  simp [stdLc, AddSubgroup.mem_pi]

variable {ι : Type*} [Fintype ι]

/-- **`H` as a sum of one-variable forms.** -/
theorem Hf_eq_sum (s : ℝ) (x y : ι → ℂ) : Hf s x y = ∑ p, (s : ℂ) * (x p * starRingEnd ℂ (y p)) := by
  rw [Hf, Finset.mul_sum]

/-- **`Lc^ι` is a theta lattice** (`ThetaHeis.isThetaLat_of_int` with `pair_cmLat`, `norm_cmLat`). -/
theorem isThetaLat_stdLc (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) :
    IsThetaLat (sC sd) sd (stdLc sd ι) := by
  refine isThetaLat_of_int (fun x hx => ?_) (fun x hx y hy => ?_)
  · choose m hm using fun p => norm_cmLat hd8 hsd hΔ (mem_stdLc.mp hx p)
    refine ⟨∑ p, m p, ?_⟩
    rw [Hf_eq_sum, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun p _ => hm p
  · choose n k hn hk using fun p => pair_cmLat hd8 hsd hΔ (mem_stdLc.mp hx p) (mem_stdLc.mp hy p)
    refine ⟨∑ p, n p, ∑ p, k p, ?_, ?_⟩
    · rw [Hf_eq_sum, Complex.im_sum]
      push_cast
      exact Finset.sum_congr rfl fun p _ => hn p
    · rw [Hf_eq_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => hk p

end Std

/-! ## The one-variable theta at a basis period -/

section Period

variable (Λ : PeriodPair)

/-- **`σ*` at a basis period** `l` (`l/2 ∉ Λ`): `σ*(z + l) = −e^{(π/A)·l̄(z + l/2)}σ*(z)`. The constant of
`σ_W(z + l) = C·e^{η(l)z}σ_W(z)` is read at `z = −l/2`, where `σ_W` is odd and nonzero. -/
theorem sgStar_add_period (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l : ℂ} (hl : l ∈ Λ.lattice) (hl2 : l / 2 ∉ Λ.lattice)
    (z : ℂ) : sgStar Λ (z + l) =
      -cexp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l * (z + l / 2)) * sgStar Λ z := by
  set c : ℂ := ((Real.pi / area Λ : ℝ) : ℂ)
  set η := s2 Λ * l + c * starRingEnd ℂ l with hη_def
  have hη : ∀ z ∉ Λ.lattice, zetaW Λ (z + l) - zetaW Λ z = η := fun z hz =>
    zetaW_add_lattice Λ EllipticLegendre.legendre hor hl hz
  obtain ⟨C, -, hC⟩ := sigmaW_add_lattice Λ hl hη
  have hs : sigmaW Λ (l / 2) ≠ 0 := sigmaW_ne_zero Λ hl2
  have hCv : C = -cexp (η * (l / 2)) := by
    have h := hC (-(l / 2))
    rw [show -(l / 2) + l = l / 2 by ring, sigmaW_neg] at h
    have hE : cexp (η * -(l / 2)) * cexp (η * (l / 2)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      ring_nf
    have h1 : (C * cexp (η * -(l / 2)) + 1) * sigmaW Λ (l / 2) = 0 := by linear_combination h
    have h2 := (mul_eq_zero.mp h1).resolve_right hs
    linear_combination cexp (η * (l / 2)) * h2 - C * hE
  have hexp : cexp (η * (l / 2)) * cexp (η * z) * cexp (-(s2 Λ) * (z + l) ^ 2 / 2) =
      cexp (c * starRingEnd ℂ l * (z + l / 2)) * cexp (-(s2 Λ) * z ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hη_def]
    ring_nf
  simp only [sgStar]
  rw [hC z, hCv]
  linear_combination (-(sigmaW Λ z)) * hexp

/-- **`th0_t` at a basis period**: `th0_t(w + l)·e^{−(π/A)(w l̄ + l l̄/2)} = −e^{(π/A)(l̄t − t̄l)}·th0_t(w)`. -/
theorem th0L_add_period (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l : ℂ} (hl : l ∈ Λ.lattice) (hl2 : l / 2 ∉ Λ.lattice)
    (t w : ℂ) :
    th0L Λ t (w + l) * cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * (w * starRingEnd ℂ l)) -
        ((Real.pi / area Λ : ℝ) : ℂ) * (l * starRingEnd ℂ l) / 2) =
      -cexp (((Real.pi / area Λ : ℝ) : ℂ) * (starRingEnd ℂ l * t - starRingEnd ℂ t * l)) * th0L Λ t w := by
  set c : ℂ := ((Real.pi / area Λ : ℝ) : ℂ)
  rw [th0L_eq, th0L_eq, show w + l + t = (w + t) + l by ring, sgStar_add_period Λ hor hl hl2]
  have hexp : cexp (c * starRingEnd ℂ l * (w + t + l / 2)) * cexp (-(c * starRingEnd ℂ t) * (w + l)) *
      cexp (-(c * (w * starRingEnd ℂ l)) - c * (l * starRingEnd ℂ l) / 2) =
      cexp (c * (starRingEnd ℂ l * t - starRingEnd ℂ t * l)) * cexp (-(c * starRingEnd ℂ t) * w) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  linear_combination (-(sgStar Λ (w + t)) / sgStar Λ t) * hexp

end Period

/-! ## `F0 ∈ Th(Lc^ι)` -/

section F0

variable {d : ℕ} {sd : ℝ} {ι : Type*} [Fintype ι]

variable (sd) in
/-- **The canonical product theta** `F0 = Π_i th0_t(z_i)` on `ℂ^ι`, for `Lc`, `s = 1/area(Lc)` and `t = δ/2`. -/
def F0c : (ι → ℂ) → ℂ := F0 (sC sd) (sgStar (cmLat sd)) (tC sd)

/-- **`F0` is the product of the one-variable thetas `th0L`.** -/
theorem F0c_apply (z : ι → ℂ) : F0c sd z = ∏ i, th0L (cmLat sd) (tC sd) (z i) := rfl

omit [Fintype ι] in
/-- **`th0_t` is entire.** -/
theorem differentiable_th0L (Λ : PeriodPair) (t : ℂ) : Differentiable ℂ (th0L Λ t) := by
  have hs : Differentiable ℂ (sgStar Λ) := by
    change Differentiable ℂ fun z => sigmaW Λ z * cexp (-(s2 Λ) * z ^ 2 / 2)
    exact (differentiable_sigmaW Λ).mul (by fun_prop)
  rw [show th0L Λ t = fun z => sgStar Λ (z + t) * cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * z) /
    sgStar Λ t from funext (th0L_eq Λ t)]
  fun_prop

/-- **`F0` is entire.** -/
theorem differentiable_F0c : Differentiable ℂ (F0c (ι := ι) sd) := by
  have h := differentiable_th0L (cmLat sd) (tC sd)
  change Differentiable ℂ fun z : ι → ℂ => ∏ i, th0L (cmLat sd) (tC sd) (z i)
  fun_prop

variable [DecidableEq ι]

/-- **`H(z, l·e_i) = s·z_i·l̄`.** -/
theorem Hf_single_right (s : ℝ) (z : ι → ℂ) (i : ι) (l : ℂ) :
    Hf s z (Pi.single i l) = (s : ℂ) * (z i * starRingEnd ℂ l) := by
  rw [Hf_eq_sum, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **`F0` with one coordinate replaced**: `th0_t(v)·Π_{j ≠ i} th0_t(z_j)`. -/
theorem F0c_update (z : ι → ℂ) (i : ι) (v : ℂ) :
    F0c sd (Function.update z i v) =
      th0L (cmLat sd) (tC sd) v * ∏ j ∈ Finset.univ.erase i, th0L (cmLat sd) (tC sd) (z j) := by
  rw [F0c_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [Fintype ι] in
/-- **Translating by `l·e_i` replaces the coordinate `i`.** -/
theorem add_single_eq_update (z : ι → ℂ) (i : ι) (l : ℂ) : z + Pi.single i l = Function.update z i (z i + l) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- **The generators fix `F0`**: `α(l·e_i)·U_{l·e_i}F0 = F0` for `l = δ` and `l = δω`, when `d ≡ 7 (mod 8)`. At
`l = δ` the phase of `th0L_add_period` is `1` and `α = −1`; at `l = δω` it is `e^{−πi}` and `α = (−1)^{(1+d)/4}`. -/
theorem F0c_gen (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2) (hΔ : discr (baseLat sd) ≠ 0) (i : ι) {l : ℂ}
    (hl : l = deltaC sd ∨ l = deltaC sd * omegaD sd) :
    al (sC sd) sd (Pi.single i l) • opU (sC sd) (Pi.single i l) (F0c sd) = F0c sd := by
  have hsd0 := sd_pos8 hd8 hsd
  obtain ⟨hor, -, -, -⟩ := canon_data hsd0 hΔ
  obtain ⟨h1, h2⟩ := cmLat_ω hsd0.ne' hΔ
  have hlL : l ∈ (cmLat sd).lattice := by
    rcases hl with rfl | rfl
    · exact h1 ▸ (cmLat sd).ω₁_mem_lattice
    · exact h2 ▸ (cmLat sd).ω₂_mem_lattice
  have hl2 : l / 2 ∉ (cmLat sd).lattice := by
    rcases hl with rfl | rfl
    · exact h1 ▸ (cmLat sd).ω₁_div_two_notMem_lattice
    · exact h2 ▸ (cmLat sd).ω₂_div_two_notMem_lattice
  set c : ℂ := ((Real.pi / area (cmLat sd) : ℝ) : ℂ) with hc_def
  have hcs : (Real.pi : ℂ) * (sC sd : ℂ) = c := by
    rw [hc_def, sC]
    push_cast
    ring
  have hn : starRingEnd ℂ (deltaC sd) * deltaC sd = (normSq (deltaC sd) : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  have hcn : c * ((normSq (deltaC sd) : ℂ) * sd) = Real.pi := by
    have hn0 : (normSq (deltaC sd) : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.mpr (deltaC_ne_zero hΔ)).ne'
    have hs0 : (sd : ℂ) ≠ 0 := by exact_mod_cast hsd0.ne'
    rw [hc_def, area_cmLat hsd0 hΔ]
    push_cast
    field_simp
  have hj : ∃ j : ℕ, d + 1 = 8 * j := ⟨(d + 1) / 8, by omega⟩
  obtain ⟨j, hj⟩ := hj
  have hj' : (d : ℝ) + 1 = 8 * j := by exact_mod_cast hj
  have h4 := sd_sq hsd
  -- the sign and the phase cancel
  have hkey : al (sC sd) sd (Pi.single i l) *
      -cexp (c * (starRingEnd ℂ l * tC sd - starRingEnd ℂ (tC sd) * l)) = 1 := by
    have hHf := Hf_single_right (sC sd) (Pi.single i l) i l
    simp only [Pi.single_eq_same] at hHf
    rcases hl with rfl | rfl
    · have hal : al (sC sd) sd (Pi.single i (deltaC sd)) = (-1) ^ (1 : ℤ) := by
        refine al_eq_of_int ?_
        rw [hHf, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
        push_cast
        linear_combination sC_mul_normSq hsd0 hΔ
      have hph : starRingEnd ℂ (deltaC sd) * tC sd - starRingEnd ℂ (tC sd) * deltaC sd = 0 := by
        simp only [tC, map_div₀, map_ofNat]
        ring
      rw [hal, hph, mul_zero, Complex.exp_zero]
      norm_num
    · have hal : al (sC sd) sd (Pi.single i (deltaC sd * omegaD sd)) = (-1) ^ (2 * j : ℤ) := by
        refine al_eq_of_int ?_
        rw [hHf, show deltaC sd * omegaD sd = deltaC sd * ((0 : ℤ) + (1 : ℤ) * omegaD sd) by push_cast; ring,
          pair_coord hsd0 hΔ]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
          Complex.I_re, Complex.I_im]
        push_cast
        field_simp
        linear_combination h4 + hj'
      have hph : c * (starRingEnd ℂ (deltaC sd * omegaD sd) * tC sd -
          starRingEnd ℂ (tC sd) * (deltaC sd * omegaD sd)) = -(Real.pi * I) := by
        have hE : starRingEnd ℂ (deltaC sd * omegaD sd) * tC sd -
            starRingEnd ℂ (tC sd) * (deltaC sd * omegaD sd) = -((normSq (deltaC sd) : ℂ) * sd * I) := by
          simp only [tC, omegaD, map_mul, map_div₀, map_ofNat, map_add, map_one, Complex.conj_ofReal,
            Complex.conj_I]
          linear_combination (-(sd : ℂ) * I) * hn
        rw [hE]
        linear_combination (-I) * hcn
      rw [hal, hph, Complex.exp_neg_pi_mul_I, zpow_mul]
      norm_num
  funext z
  have hper := th0L_add_period (cmLat sd) hor hlL hl2 (tC sd) (z i)
  have hE : -(Real.pi : ℂ) * Hf (sC sd) z (Pi.single i l) -
      Real.pi * Hf (sC sd) (Pi.single i l) (Pi.single i l) / 2 =
      -(c * (z i * starRingEnd ℂ l)) - c * (l * starRingEnd ℂ l) / 2 := by
    rw [Hf_single_right, Hf_single_right, Pi.single_eq_same, ← hcs]
    ring
  simp only [Pi.smul_apply, smul_eq_mul, opU_apply, hE]
  rw [add_single_eq_update, F0c_update]
  conv_rhs => rw [← Function.update_eq_self i z, F0c_update]
  linear_combination (al (sC sd) sd (Pi.single i l) * ∏ j ∈ Finset.univ.erase i, th0L (cmLat sd) (tC sd) (z j)) *
    hper + (th0L (cmLat sd) (tC sd) (z i) * ∏ j ∈ Finset.univ.erase i, th0L (cmLat sd) (tC sd) (z j)) * hkey

/-- **`F0 ∈ Th(Lc^ι)`**, for `d ≡ 7 (mod 8)` (2 split in `K₀`, design A3): the generators `δ·e_i`, `δω·e_i` fix `F0`
(`F0c_gen`), and the stabiliser is a subgroup (`ThetaHeis.mem_Th_of_le_closure`). Squarefreeness is not used. -/
theorem F0c_mem_Th (_hd : Squarefree d) (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) : F0c sd ∈ Th (sC sd) sd (stdLc sd ι) := by
  have hsd0 := sd_pos8 hd8 hsd
  obtain ⟨h1, h2⟩ := cmLat_ω hsd0.ne' hΔ
  have hδ : deltaC sd ∈ (cmLat sd).lattice := h1 ▸ (cmLat sd).ω₁_mem_lattice
  have hδω : deltaC sd * omegaD sd ∈ (cmLat sd).lattice := h2 ▸ (cmLat sd).ω₂_mem_lattice
  have hsingle : ∀ (i : ι) {l : ℂ}, l ∈ (cmLat sd).lattice → Pi.single i l ∈ stdLc sd ι := fun i l hl =>
    mem_stdLc.mpr fun j => by
      by_cases h : j = i
      · subst h
        simpa using hl
      · simp [h, zero_mem]
  set T : Set (ι → ℂ) := {x | ∃ i, x = Pi.single i (deltaC sd) ∨ x = Pi.single i (deltaC sd * omegaD sd)}
  refine mem_Th_of_le_closure (isThetaLat_stdLc hd8 hsd hΔ) (T := T) ?_ ?_ differentiable_F0c ?_
  · rintro x ⟨i, rfl | rfl⟩
    exacts [hsingle i hδ, hsingle i hδω]
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨a, b, hab⟩ := (mem_cmLat_iff hsd0 hΔ).mp (mem_stdLc.mp hx i)
    have hxi : x i = a • deltaC sd + b • (deltaC sd * omegaD sd) := by
      rw [hab, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [hxi, Pi.single_add, Pi.single_zsmul, Pi.single_zsmul]
    exact add_mem (zsmul_mem (AddSubgroup.subset_closure (k := T) ⟨i, Or.inl rfl⟩) _)
      (zsmul_mem (AddSubgroup.subset_closure (k := T) ⟨i, Or.inr rfl⟩) _)
  · rintro x ⟨i, rfl | rfl⟩
    exacts [F0c_gen hd8 hsd hΔ i (Or.inl rfl), F0c_gen hd8 hsd hΔ i (Or.inr rfl)]

end F0

/-! ## `Th(Lc^ι) = ℂ·F0` -/

section Unique

/-- **One variable**: an entire `f` with the multipliers `M(l, u)` of `th0_t` on `Λ` (`t ∉ Λ`) is `f(0)·th0_t`. The
quotient `φ(v) = f(v − t)/th0_t(v − t)` is elliptic, holomorphic off the lattice, with at most a simple pole at `0`
(`th0_t(v − t) = v·sigP(v)·e^{−s₂v²/2}e^{−(π/A)t̄(v − t)}/σ*(t)`), so it is constant
(`EllipticDivisor.EllPole.lower_one`, `EllipticDivisor.EllPole.eq_const`); `f = C·th0_t` off the countable set
`Λ − t`, hence everywhere, and `C = f(0)` as `th0_t(0) = 1`. -/
theorem eq_mul_th0L (Λ : PeriodPair) {t : ℂ} (ht : t ∉ Λ.lattice) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (M : ℂ → ℂ → ℂ) (hfl : ∀ l ∈ Λ.lattice, ∀ u, M l u * f (u + l) = f u)
    (hhl : ∀ l ∈ Λ.lattice, ∀ u, M l u * th0L Λ t (u + l) = th0L Λ t u) (u : ℂ) :
    f u = f 0 * th0L Λ t u := by
  have hσt : sgStar Λ t ≠ 0 := mul_ne_zero (sigmaW_ne_zero Λ ht) (Complex.exp_ne_zero _)
  have hh0 : ∀ u, u + t ∉ Λ.lattice → th0L Λ t u ≠ 0 := fun u hu => by
    rw [th0L_eq]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (sigmaW_ne_zero Λ hu) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)) hσt
  set φ : ℂ → ℂ := fun v => f (v - t) / th0L Λ t (v - t) with hφ_def
  have hsub : Differentiable ℂ fun v : ℂ => v - t := differentiable_id.sub_const t
  have hφ : EllPole Λ φ 1 := by
    refine ⟨fun v hv l hl => ?_, fun v hv => ?_, ?_⟩
    · have hu : (v - t) + t ∉ Λ.lattice := by simpa using hv
      have h1 := hfl l hl (v - t)
      have h2 := hhl l hl (v - t)
      have hne := hh0 _ hu
      have hM : M l (v - t) ≠ 0 := fun h0 => hne (by rw [← h2, h0, zero_mul])
      simp only [hφ_def, show v + l - t = (v - t) + l by ring]
      rw [← h1, ← h2, mul_div_mul_left _ _ hM]
    · have hu : (v - t) + t ∉ Λ.lattice := by simpa using hv
      exact ((hf.comp hsub).differentiableAt.div ((differentiable_th0L Λ t).comp hsub).differentiableAt
        (hh0 _ hu)).differentiableWithinAt
    · set num : ℂ → ℂ := fun v => f (v - t) * sgStar Λ t
      set den : ℂ → ℂ := fun v => sigP Λ v * cexp (-(s2 Λ) * v ^ 2 / 2) *
        cexp (-(((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ t) * (v - t))
      have hnum : Differentiable ℂ num := (hf.comp hsub).mul_const _
      have hden : Differentiable ℂ den := ((differentiable_sigP Λ).mul (by fun_prop)).mul (by fun_prop)
      have hden0 : den 0 ≠ 0 := by
        simp only [den, sigP_zero, one_mul]
        exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
      refine ⟨num / den, (hnum.analyticAt 0).div (hden.analyticAt 0) hden0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv0 : v ≠ 0 := hv
      simp only [hφ_def, num, den, pow_one, Pi.div_apply]
      rw [th0L_eq, show v - t + t = v by ring, sgStar, sigmaW_eq]
      by_cases hp : sigP Λ v = 0
      · simp [hp]
      · field_simp
  have hconst : ∀ {z : ℂ}, z ∉ Λ.lattice → φ z = φ (Λ.ω₁ / 2) := fun hz =>
    EllPole.eq_const Λ (EllPole.lower_one Λ hφ) hz
  set C := φ (Λ.ω₁ / 2)
  have hfC : f = fun u => C * th0L Λ t u := by
    have hd : Dense {u : ℂ | u + t ∉ Λ.lattice} := by
      have e : {u : ℂ | u + t ∉ Λ.lattice} = ((fun u => u + t) ⁻¹' (Λ.lattice : Set ℂ))ᶜ := rfl
      rw [e]
      exact Set.Countable.dense_compl ℂ ((countable_lattice Λ).preimage (add_left_injective t))
    refine Continuous.ext_on hd hf.continuous (continuous_const.mul (differentiable_th0L Λ t).continuous)
      fun u hu => ?_
    have h1 : φ (u + t) = C := hconst hu
    simp only [hφ_def, add_sub_cancel_right] at h1
    rw [← h1, div_mul_cancel₀ _ (hh0 u hu)]
  rw [hfC]
  simp only
  rw [th0L_zero Λ ht, mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Replacing one coordinate is holomorphic.** -/
theorem differentiable_update (w : ι → ℂ) (i : ι) : Differentiable ℂ fun u : ℂ => Function.update w i u := by
  refine differentiable_pi.mpr fun j => ?_
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- **A theta function restricted to one coordinate**: for `l·e_i ∈ Λ`,
`α(l·e_i)·e^{−πs(u l̄) − πs(l l̄)/2}·G(w[i ↦ u + l]) = G(w[i ↦ u])`. -/
theorem restrict_Th {s sd : ℝ} {Λ : AddSubgroup (ι → ℂ)} {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ) (i : ι)
    (w : ι → ℂ) {l : ℂ} (hl : Pi.single i l ∈ Λ) (u : ℂ) :
    (al s sd (Pi.single i l) * cexp (-(Real.pi : ℂ) * ((s : ℂ) * (u * starRingEnd ℂ l)) -
        Real.pi * ((s : ℂ) * (l * starRingEnd ℂ l)) / 2)) * G (Function.update w i (u + l)) =
      G (Function.update w i u) := by
  have h := congrFun (hG.2 _ hl) (Function.update w i u)
  simp only [Pi.smul_apply, smul_eq_mul, opU_apply, Hf_single_right, Pi.single_eq_same, Function.update_self,
    add_single_eq_update, Function.update_idem] at h
  linear_combination h

variable {d : ℕ} {sd : ℝ}

/-- **The standard theta space is the line `ℂ·F0`** (with no `dim Th = 1` input): restricted to one coordinate,
`G ∈ Th(Lc^ι)` has the multipliers of `th0_t` (`restrict_Th`, and `F0c_mem_Th` for `th0_t`), so `eq_mul_th0L` applies;
an induction over the coordinates gives `G = G(0)·F0`. Squarefreeness is not used. -/
theorem eq_smul_F0c (_hd : Squarefree d) (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) {G : (ι → ℂ) → ℂ} (hG : G ∈ Th (sC sd) sd (stdLc sd ι)) : G = G 0 • F0c sd := by
  have hsd0 := sd_pos8 hd8 hsd
  obtain ⟨-, -, ht, -⟩ := canon_data hsd0 hΔ
  have hF := F0c_mem_Th (ι := ι) _hd hd8 hsd hΔ
  have hsingle : ∀ (i : ι) {l : ℂ}, l ∈ (cmLat sd).lattice → Pi.single i l ∈ stdLc sd ι := fun i l hl =>
    mem_stdLc.mpr fun j => by
      by_cases h : j = i
      · subst h
        simpa using hl
      · simp [h, zero_mem]
  have hone : ∀ (w : ι → ℂ) (i : ι) (u : ℂ),
      G (Function.update w i u) = G (Function.update w i 0) * th0L (cmLat sd) (tC sd) u := by
    intro w i u
    refine eq_mul_th0L (cmLat sd) ht (hG.1.comp (differentiable_update w i))
      (fun l u => al (sC sd) sd (Pi.single i l) * cexp (-(Real.pi : ℂ) * ((sC sd : ℂ) * (u * starRingEnd ℂ l)) -
        Real.pi * ((sC sd : ℂ) * (l * starRingEnd ℂ l)) / 2))
      (fun l hl u => restrict_Th hG i w (hsingle i hl) u) (fun l hl u => ?_) u
    have h := restrict_Th hF i 0 (hsingle i hl) u
    simp only [F0c_update, Pi.zero_apply, th0L_zero (cmLat sd) ht, Finset.prod_const_one, mul_one] at h
    exact h
  have hS : ∀ (S : Finset ι) (z : ι → ℂ),
      G z = (∏ i ∈ S, th0L (cmLat sd) (tC sd) (z i)) * G (fun j => if j ∈ S then 0 else z j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro z; simp
    | insert a S ha ih =>
      intro z
      rw [ih z, Finset.prod_insert ha]
      have e1 : (fun j => if j ∈ S then 0 else z j) =
          Function.update (fun j => if j ∈ insert a S then 0 else z j) a (z a) := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp [ha]
        · simp [hj, Finset.mem_insert]
      have e2 : Function.update (fun j => if j ∈ insert a S then (0 : ℂ) else z j) a 0 =
          fun j => if j ∈ insert a S then 0 else z j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [hj]
      rw [e1, hone, e2]
      ring
  funext z
  have h := hS Finset.univ z
  simp only [Finset.mem_univ, ↓reduceIte] at h
  rw [h, Pi.smul_apply, smul_eq_mul, F0c_apply, mul_comm]
  rfl

end Unique

/-! ## The comparison -/

section Compare

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {sd : ℝ}

/-- **The adapted model theta** `Θ_g = (Iop(Lc^ι, g⁻¹C) F0) ∘ g⁻¹` on the target of the isometry `g`. -/
def thetaAdapt (sd : ℝ) (g : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (C : AddSubgroup (ι → ℂ)) : (ι → ℂ) → ℂ :=
  Iop (sC sd) sd (stdLc sd ι) (C.comap g.toLinearMap.toAddMonoidHom) (F0c sd) ∘ g.symm

/-- **The per-prime comparison** (replaces `dim Th = 1`): every `θ ∈ Th(C)`, `C` a self-dual theta lattice, is a
multiple of `Θ_g` for every `H`-isometry `g` with `g(Lc^ι)` commensurable with `C`. The scalar is explicit:
`Iop(g⁻¹C, Lc^ι)(θ ∘ g) = a·F0` and `c = a/√idx` (`ThetaHeis.Iop_Iop_eq_smul`, `eq_smul_F0c`). -/
theorem theta_compare (hd : Squarefree d) (hd8 : d % 8 = 7) (hsd : sd = Real.sqrt d / 2)
    (hΔ : discr (baseLat sd) ≠ 0) (g : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (hg : ∀ z w, Hf (sC sd) (g z) (g w) = Hf (sC sd) z w) {C : AddSubgroup (ι → ℂ)}
    (hCt : IsThetaLat (sC sd) sd C) (hCd : IsEDual (sC sd) C)
    (hc : IsCommens C ((stdLc sd ι).map g.toLinearMap.toAddMonoidHom)) {θ : (ι → ℂ) → ℂ}
    (hθ : θ ∈ Th (sC sd) sd C) : ∃ c : ℂ, θ = c • thetaAdapt sd g C := by
  have hC't := isThetaLat_comap g hg hCt
  have hC'd := isEDual_comap g hg hCd
  have hc' := isCommens_comap g hc
  have hstd := isThetaLat_stdLc (ι := ι) hd8 hsd hΔ
  have hθ' := comp_mem_Th g hg hθ
  have ha := eq_smul_F0c hd hd8 hsd hΔ (Iop_mem_Th hC't hstd hc' hθ')
  have hII := Iop_Iop_eq_smul hC't hC'd hstd hc' hθ'
  rw [ha, Iop_smul] at hII
  set i₁ := (C.comap g.toLinearMap.toAddMonoidHom ⊓ stdLc sd ι).relIndex (C.comap g.toLinearMap.toAddMonoidHom)
  set i₂ := (C.comap g.toLinearMap.toAddMonoidHom ⊓ stdLc sd ι).relIndex (stdLc sd ι)
  set r : ℝ := Real.sqrt ((i₁ : ℝ) / (i₂ : ℝ)) with hr_def
  have hr : (r : ℂ) ≠ 0 := by
    have h1 : (0 : ℝ) < (i₁ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc'.1
    have h2 : (0 : ℝ) < (i₂ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc'.2
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos h1 h2)).ne'
  refine ⟨Iop (sC sd) sd (C.comap g.toLinearMap.toAddMonoidHom) (stdLc sd ι) (θ ∘ g) 0 / r, ?_⟩
  funext z
  have h := congrFun hII (g.symm z)
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp, LinearEquiv.apply_symm_apply] at h
  simp only [thetaAdapt, Pi.smul_apply, smul_eq_mul, Function.comp]
  field_simp
  linear_combination -h

end Compare

/-! ## The moved theta of the chain -/

section Membership

variable {E L : Type*} [Field E] [Field L] {Φ : Type*} [Fintype Φ] (τ : Φ → (E →+* L)) (P : TP E L Φ)

/-- **The moved theta lies in `Th(La(N, N′))`** when the three lattices of `ThetaChain.thMoved` are theta lattices and
commensurable (a C2-type fact; no `θ₀` is needed): two applications of `ThetaHeis.Iop_mem_Th`. -/
theorem thMoved_mem_Th {a b : ℕ} {θ : Amb Φ a b → ℂ} (N : Submodule (NumberField.RingOfIntegers E) (Fin a → E))
    (N' : Submodule (NumberField.RingOfIntegers E) (Fin b → E))
    (h₀ : IsThetaLat P.s P.sd (La τ P (WeylFock.stdLat a E) (WeylFock.stdLat b E)))
    (h₁ : IsThetaLat P.s P.sd (La τ P N (WeylFock.stdLat b E))) (h₂ : IsThetaLat P.s P.sd (La τ P N N'))
    (hc₁ : IsCommens (La τ P (WeylFock.stdLat a E) (WeylFock.stdLat b E)) (La τ P N (WeylFock.stdLat b E)))
    (hc₂ : IsCommens (La τ P N (WeylFock.stdLat b E)) (La τ P N N'))
    (hθ : θ ∈ Th P.s P.sd (La τ P (WeylFock.stdLat a E) (WeylFock.stdLat b E))) :
    thMoved τ P θ N N' ∈ Th P.s P.sd (La τ P N N') :=
  Iop_mem_Th h₁ h₂ hc₂ (Iop_mem_Th h₀ h₁ hc₁ hθ)

end Membership

end

end ThetaCompare
