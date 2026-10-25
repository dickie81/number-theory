/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 757–760 of 1732

File 190 of 430: the parts `rows22310R_757` … `rows22310R_760` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28704 tests: row 119 columns 100–102, row 119 columns 103–105, row 119
columns 106–108, row 119 columns 109–111), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_757 : rowsJ2 119 120 100 103 ≤ 585754144487 := by decide +kernel

theorem rows22310R_758 : rowsJ2 119 120 103 106 ≤ 2084192508943 := by decide +kernel

theorem rows22310R_759 : rowsJ2 119 120 106 109 ≤ 4671714786077 := by decide +kernel

theorem rows22310R_760 : rowsJ2 119 120 109 112 ≤ 8344860517421 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_757
#print axioms SieveCert.rows22310R_760
