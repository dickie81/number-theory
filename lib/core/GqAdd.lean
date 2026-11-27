import EllipticDivPoly
import EllipticDivisor

/-!
# Products of the translates `G_q`: Frobenius–Stickelberger

The translates `G_q(z) = e^{−η(q)z}σ(z + q)/(σ(z)σ(q))` (`EllipticDivisor.Gq`) multiply like the points: their
product is the translate of the sum times an elliptic function with a single pole, and `G_q` only depends on `q`
modulo the lattice. This is the analytic input of the telescoping product of `TorsTransl`.

**Pairs.** `η` is additive (`etaR_add`), so the exponentials cancel in `G_qG_{−q} = ℘(z) − ℘(q)` (`Gq_mul_Gq_neg`,
the `σ` addition formula) and in the **Frobenius–Stickelberger formula**
`G_aG_b = G_{a+b}·(ζ(z) + ζ(a) + ζ(b) − ζ(z + a + b))` (`Gq_mul_Gq`): with the half points `s = (a + b)/2`,
`d = (a − b)/2`, `u = z + s`, the `σ` addition formula at `(u, d)`, `(u, s)`, `(s, d)` and the duplication
`σ(2s) = −℘′(s)σ(s)⁴` give `G_aG_b/G_{a+b} = ℘′(s)(℘(d) − ℘(u))/((℘(s) − ℘(d))(℘(s) − ℘(u)))`, and
`EllipticAdd.zetaW_add_add_zetaW_sub` at `(s, d)` and `(s, u)` gives the same for the `ζ` side. In the tangent case
`a = b` (`Gq_sq`), `u = z + a` and `G_a²/G_{2a} = ℘′(a)/(℘(u) − ℘(a))`.

**The constants.** `ζ(a) + ζ(b) − ζ(a + b) = −½(℘′(a) − ℘′(b))/(℘(a) − ℘(b))` has square `℘(a) + ℘(b) + ℘(a + b)`
(`chord_sq`, by the addition theorem), and `2ζ(a) − ζ(2a)` has square `2℘(a) + ℘(2a)` (`tangent_sq`, by duplication):
the constants are integral where the values of `℘` are.

**Periods.** With the oriented quasi-periods (`CMThetaOne.zetaW_add_lattice`), `G_{q+l} = G_q` for every period `l`
(`Gq_add_lattice`).

**Main declarations:** `Gq_mul_Gq_neg`, `Gq_mul_Gq`, `Gq_sq`, `chord_sq`, `tangent_sq`, `Gq_add_lattice`.
-/

namespace GqAdd

noncomputable section

open PeriodPair ThetaNorm CMThetaOne EllipticAdd EllipticDivisor EllipticLegendre EllipticDivPoly Complex

variable (Λ : PeriodPair)

/-- **`η` is additive.** -/
theorem etaR_add (q r : ℂ) : etaR Λ (q + r) = etaR Λ q + etaR Λ r := by
  simp only [etaR, map_add]
  ring

/-- **`η` is odd.** -/
theorem etaR_neg (q : ℂ) : etaR Λ (-q) = -etaR Λ q := by
  simp only [etaR, map_neg]
  ring

/-- **`G_q(z)·G_{−q}(z) = ℘(z) − ℘(q)`** (`sigmaW_add_mul_sub`; the exponentials cancel). -/
theorem Gq_mul_Gq_neg {q z : ℂ} (hq : q ∉ Λ.lattice) (hz : z ∉ Λ.lattice) :
    Gq Λ q z * Gq Λ (-q) z = ℘[Λ] z - ℘[Λ] q := by
  have hsz := sigmaW_ne_zero Λ hz
  have hsq := sigmaW_ne_zero Λ hq
  have hE : cexp (-(etaR Λ q * z)) * cexp (-(etaR Λ (-q) * z)) = 1 := by
    rw [← Complex.exp_add, etaR_neg, neg_mul, neg_neg, neg_add_cancel, Complex.exp_zero]
  have h := sigmaW_add_mul_sub Λ hz hq
  simp only [Gq]
  rw [← sub_eq_add_neg, sigmaW_neg]
  generalize cexp (-(etaR Λ q * z)) = A at hE ⊢
  generalize cexp (-(etaR Λ (-q) * z)) = B at hE ⊢
  rw [div_mul_div_comm, div_eq_iff (by simp [hsz, hsq])]
  linear_combination (sigmaW Λ (z + q) * sigmaW Λ (z - q)) * hE + h

/-- **Frobenius–Stickelberger** `G_aG_b = G_{a+b}·(ζ(z) + ζ(a) + ζ(b) − ζ(z + a + b))` for `a ≢ ±b` (half points
`s = (a + b)/2`, `d = (a − b)/2`, `u = z + s`: `sigmaW_add_mul_sub` at `(u, d)`, `(u, s)`, `(s, d)`, `sigmaW_two_mul`
at `s`, `zetaW_add_add_zetaW_sub` at `(s, d)`, `(s, u)`). -/
theorem Gq_mul_Gq {a b z : ℂ} (ha : a ∉ Λ.lattice) (hb : b ∉ Λ.lattice) (hab : a + b ∉ Λ.lattice)
    (hamb : a - b ∉ Λ.lattice) (hz : z ∉ Λ.lattice) (hzab : z + (a + b) ∉ Λ.lattice)
    (hu : z + (a + b) / 2 ∉ Λ.lattice) :
    Gq Λ a z * Gq Λ b z = Gq Λ (a + b) z * (zetaW Λ z + zetaW Λ a + zetaW Λ b - zetaW Λ (z + (a + b))) := by
  have hs : (a + b) / 2 ∉ Λ.lattice := fun h => hab (by simpa using add_mem h h)
  have hd : (a - b) / 2 ∉ Λ.lattice := fun h => hamb (by simpa using add_mem h h)
  have E1 := sigmaW_add_mul_sub Λ hu hd
  have E2 := sigmaW_add_mul_sub Λ hu hs
  have E3 := sigmaW_add_mul_sub Λ hs hd
  have E4 := sigmaW_two_mul Λ hs
  have e1 : (a + b) / 2 + (a - b) / 2 = a := by ring
  have e2 : (a + b) / 2 - (a - b) / 2 = b := by ring
  have Z1 := zetaW_add_add_zetaW_sub Λ hs hd (by rwa [e1]) (by rwa [e2])
  have e3 : (a + b) / 2 + (z + (a + b) / 2) = z + (a + b) := by ring
  have e4 : (a + b) / 2 - (z + (a + b) / 2) = -z := by ring
  have Z2 := zetaW_add_add_zetaW_sub Λ hs hu (by rwa [e3]) (by rw [e4]; exact fun h => hz (by simpa using neg_mem h))
  rw [show z + (a + b) / 2 + (a - b) / 2 = z + a by ring, show z + (a + b) / 2 - (a - b) / 2 = z + b by ring] at E1
  rw [show z + (a + b) / 2 + (a + b) / 2 = z + (a + b) by ring, show z + (a + b) / 2 - (a + b) / 2 = z by ring] at E2
  rw [e1, e2] at E3 Z1
  rw [show 2 * ((a + b) / 2) = a + b by ring] at E4
  rw [e3, e4, zetaW_neg] at Z2
  set Ps := ℘[Λ] ((a + b) / 2)
  set Pd := ℘[Λ] ((a - b) / 2)
  set Pu := ℘[Λ] (z + (a + b) / 2)
  have hP : ℘'[Λ] ((a + b) / 2) ≠ 0 := fun h0 => sigmaW_ne_zero Λ hab (by rw [E4, h0]; ring)
  have hsd : Ps - Pd ≠ 0 := fun h0 => mul_ne_zero (sigmaW_ne_zero Λ ha) (sigmaW_ne_zero Λ hb)
    (by rw [E3]; linear_combination (-(sigmaW Λ ((a + b) / 2) ^ 2 * sigmaW Λ ((a - b) / 2) ^ 2)) * h0)
  have hsu : Ps - Pu ≠ 0 := fun h0 => mul_ne_zero (sigmaW_ne_zero Λ hzab) (sigmaW_ne_zero Λ hz)
    (by rw [E2]; linear_combination (sigmaW Λ (z + (a + b) / 2) ^ 2 * sigmaW Λ ((a + b) / 2) ^ 2) * h0)
  have hR : zetaW Λ z + zetaW Λ a + zetaW Λ b - zetaW Λ (z + (a + b)) =
      ℘'[Λ] ((a + b) / 2) / (Ps - Pd) - ℘'[Λ] ((a + b) / 2) / (Ps - Pu) := by
    linear_combination Z1 - Z2
  have hσz := sigmaW_ne_zero Λ hz
  have hE : cexp (-(etaR Λ (a + b) * z)) = cexp (-(etaR Λ a * z)) * cexp (-(etaR Λ b * z)) := by
    rw [← Complex.exp_add, etaR_add]; ring_nf
  have hzab' : sigmaW Λ (z + (a + b)) = sigmaW Λ (z + (a + b) / 2) ^ 2 * sigmaW Λ ((a + b) / 2) ^ 2 * (Ps - Pu) /
      sigmaW Λ z := by rw [eq_div_iff hσz, E2]
  have hL : Gq Λ a z * Gq Λ b z = cexp (-(etaR Λ a * z)) * cexp (-(etaR Λ b * z)) *
      (sigmaW Λ (z + a) * sigmaW Λ (z + b)) / (sigmaW Λ z ^ 2 * (sigmaW Λ a * sigmaW Λ b)) := by
    simp only [Gq]; ring
  rw [hL, E1, E3, hR, Gq, hE, hzab', E4]
  have hσs := sigmaW_ne_zero Λ hs
  have hσd := sigmaW_ne_zero Λ hd
  have hσu := sigmaW_ne_zero Λ hu
  have hds : Pd - Ps ≠ 0 := fun h0 => hsd (by linear_combination -h0)
  field_simp
  ring

/-- **Frobenius–Stickelberger, tangent case** `G_a² = G_{2a}·(ζ(z) + 2ζ(a) − ζ(z + 2a))` (`u = z + a`:
`sigmaW_add_mul_sub` at `(u, a)`, `sigmaW_two_mul` at `a`, `zetaW_add_add_zetaW_sub` at `(a, u)`). -/
theorem Gq_sq {a z : ℂ} (ha : a ∉ Λ.lattice) (h2a : 2 * a ∉ Λ.lattice) (hz : z ∉ Λ.lattice)
    (hza : z + a ∉ Λ.lattice) (hz2a : z + 2 * a ∉ Λ.lattice) :
    Gq Λ a z ^ 2 = Gq Λ (2 * a) z * (zetaW Λ z + 2 * zetaW Λ a - zetaW Λ (z + 2 * a)) := by
  have E2 := sigmaW_add_mul_sub Λ hza ha
  have E4 := sigmaW_two_mul Λ ha
  have e3 : a + (z + a) = z + 2 * a := by ring
  have e4 : a - (z + a) = -z := by ring
  have Z := zetaW_add_add_zetaW_sub Λ ha hza (by rwa [e3]) (by rw [e4]; exact fun h => hz (by simpa using neg_mem h))
  rw [show z + a + a = z + 2 * a by ring, show z + a - a = z by ring] at E2
  rw [e3, e4, zetaW_neg] at Z
  set Pa := ℘[Λ] a
  set Pu := ℘[Λ] (z + a)
  have hP : ℘'[Λ] a ≠ 0 := fun h0 => sigmaW_ne_zero Λ h2a (by rw [E4, h0]; ring)
  have hau : Pa - Pu ≠ 0 := fun h0 => mul_ne_zero (sigmaW_ne_zero Λ hz2a) (sigmaW_ne_zero Λ hz)
    (by rw [E2]; linear_combination (sigmaW Λ (z + a) ^ 2 * sigmaW Λ a ^ 2) * h0)
  have hR : zetaW Λ z + 2 * zetaW Λ a - zetaW Λ (z + 2 * a) = -(℘'[Λ] a / (Pa - Pu)) := by
    linear_combination -Z
  have hσz := sigmaW_ne_zero Λ hz
  have hσa := sigmaW_ne_zero Λ ha
  have hσu := sigmaW_ne_zero Λ hza
  have hE : cexp (-(etaR Λ (2 * a) * z)) = cexp (-(etaR Λ a * z)) ^ 2 := by
    rw [← Complex.exp_nat_mul, two_mul, etaR_add]; push_cast; ring_nf
  have hz2a' : sigmaW Λ (z + 2 * a) = sigmaW Λ (z + a) ^ 2 * sigmaW Λ a ^ 2 * (Pa - Pu) / sigmaW Λ z := by
    rw [eq_div_iff hσz, E2]
  rw [hR, Gq, Gq, hE, hz2a', E4]
  field_simp

/-- **The chord constant squared** `λ² = ℘(a) + ℘(b) + ℘(a + b)` for `λ = ζ(a) + ζ(b) − ζ(a + b)` (`zetaW_add`,
`weierstrassP_add`). -/
theorem chord_sq {a b : ℂ} (ha : a ∉ Λ.lattice) (hb : b ∉ Λ.lattice) (hab : a + b ∉ Λ.lattice)
    (hamb : a - b ∉ Λ.lattice) :
    (zetaW Λ a + zetaW Λ b - zetaW Λ (a + b)) ^ 2 = ℘[Λ] a + ℘[Λ] b + ℘[Λ] (a + b) := by
  rw [zetaW_add Λ ha hb hab hamb, weierstrassP_add Λ ha hb hab hamb, div_mul_eq_div_div_swap]
  ring

/-- **The tangent constant squared** `λ² = 2℘(a) + ℘(2a)` for `λ = 2ζ(a) − ζ(2a)` (`zetaW_two_mul`,
`weierstrassP_two_mul`). -/
theorem tangent_sq {a : ℂ} (ha : a ∉ Λ.lattice) (h2a : 2 * a ∉ Λ.lattice) :
    (2 * zetaW Λ a - zetaW Λ (2 * a)) ^ 2 = 2 * ℘[Λ] a + ℘[Λ] (2 * a) := by
  rw [zetaW_two_mul Λ ha h2a, weierstrassP_two_mul Λ ha h2a]
  ring

/-- **Lattice invariance** `G_{q+l} = G_q` for a period `l` (oriented: `sigmaW_add_lattice` with the quasi-period
`η(l)` of `zetaW_add_lattice`). -/
theorem Gq_add_lattice (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {q l : ℂ} (hq : q ∉ Λ.lattice) (hl : l ∈ Λ.lattice) :
    Gq Λ (q + l) = Gq Λ q := by
  obtain ⟨c, hc, hσ⟩ := sigmaW_add_lattice Λ hl (η := etaR Λ l) fun z hz => zetaW_add_lattice Λ legendre hor hl hz
  funext z
  have hsq := sigmaW_ne_zero Λ hq
  simp only [Gq]
  rw [← add_assoc, hσ, hσ, etaR_add]
  have hE : cexp (-((etaR Λ q + etaR Λ l) * z)) * cexp (etaR Λ l * (z + q)) =
      cexp (-(etaR Λ q * z)) * cexp (etaR Λ l * q) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have he := Complex.exp_ne_zero (etaR Λ l * q)
  by_cases hsz : sigmaW Λ z = 0
  · simp [hsz]
  rw [div_eq_div_iff (by simp [hc, he, hsz, hsq]) (by simp [hsz, hsq])]
  linear_combination (c * sigmaW Λ (z + q) * (sigmaW Λ z * sigmaW Λ q)) * hE

end

end GqAdd
