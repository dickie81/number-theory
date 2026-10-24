/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 357–360 of 549

File 93 of 140: the parts `rows22335R_357` … `rows22335R_360` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29117 tests: row 107 columns 64–70, row 107 columns 71–299, row 108 columns
0–50, row 108 columns 51–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_357 : rowsJ2 107 108 64 71 ≤ 0 := by decide +kernel

theorem rows22335R_358 : rowsJ2 107 108 71 300 ≤ 461372274973843 := by decide +kernel

theorem rows22335R_359 : rowsJ2 108 109 0 51 ≤ 335538114063374 := by decide +kernel

theorem rows22335R_360 : rowsJ2 108 109 51 57 ≤ 32599283579847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_357
#print axioms SieveCert.rows22335R_360
