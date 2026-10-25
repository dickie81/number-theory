/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 627–630 of 1732

File 158 of 430: the parts `rows22310R_627` … `rows22310R_630` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25641 tests: row 112 columns 106–108, row 112 columns 109–111, row 112
columns 112–399, row 113 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_627 : rowsJ2 112 113 106 109 ≤ 3971839371315 := by decide +kernel

theorem rows22310R_628 : rowsJ2 112 113 109 112 ≤ 6181819501872 := by decide +kernel

theorem rows22310R_629 : rowsJ2 112 113 112 400 ≤ 2726714480752 := by decide +kernel

theorem rows22310R_630 : rowsJ2 113 114 0 35 ≤ 101779273836631 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_627
#print axioms SieveCert.rows22310R_630
