/-
# The library's zero-free band, as reflection inequalities for `|ξ|`

Plain statement. The library puts every zero `τ` of `Ξ` in `|Im τ| ≤ 5/12`
(`HalfPlaneJoins.abs_im_tau_le_five_twelfths`), that is every nontrivial zero `ρ` of `ζ` in `1/12 ≤ Re ρ ≤ 11/12`
(`HalfPlaneJoins.zeta_band_eleven_twelfths`). Through `XiReflection.reflect_lt` and `XiReflection.reflect_xi` this is
the reflection inequality across every line `Re s = c` with `c > 11/12`:
* **In `ξ`** (`reflect_xi_band`): `|ξ(2c − s̄)| < |ξ(s)|` for `c > 11/12` and `Re s > c`;
* **In `Ξ`** (`reflect_band`): `‖Ξ(t̄ − 2κi)‖ < ‖Ξ(t)‖` for `κ > 5/12` and `Im t < −κ`.
The same inequality across `Re s = 1` needs no hypothesis (`XiReflection.reflect_xi_one`), and it is all that the
Riemann hypothesis for Weng's rank-2 zeta function of `ℚ` uses (`WengRankTwo.rh_weng`). RH is the inequality across
every line `Re s = c` with `c > ½` (`XiReflection.rh_iff_reflect_xi`): between the band and RH lie the lines
`½ < c ≤ 11/12`.
-/
import Mathlib
import HalfPlaneJoinsFinal
import XiReflection

open Complex ComplexConjugate WeilForm

namespace XiReflectionBand

/-- **The band as reflection, in `Ξ`**: across every horizontal line `Im t = −κ` with `κ > 5/12`. -/
theorem reflect_band {κ : ℝ} (hκ : 5 / 12 < κ) {t : ℂ} (ht : t.im < -κ) :
    ‖Xi (conj t - 2 * κ * I)‖ < ‖Xi t‖ :=
  XiReflection.reflect_lt (fun i => lt_of_le_of_lt (HalfPlaneJoins.abs_im_tau_le_five_twelfths i) hκ) ht

/-- **The band as reflection, in `ξ`**: across every vertical line `Re s = c` with `c > 11/12`. -/
theorem reflect_xi_band {c : ℝ} (hc : 11 / 12 < c) {s : ℂ} (hs : c < s.re) :
    ‖xi (2 * c - conj s)‖ < ‖xi s‖ :=
  XiReflection.reflect_xi
    (fun i => lt_of_le_of_lt (HalfPlaneJoins.abs_im_tau_le_five_twelfths i) (by linarith)) hs

end XiReflectionBand

#print axioms XiReflectionBand.reflect_band
#print axioms XiReflectionBand.reflect_xi_band
