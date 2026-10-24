/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 212–215 of 549

File 55 of 140: the parts `rows22335R_212` … `rows22335R_215` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29525 tests: row 85 columns 71–74, row 85 columns 75–79, row 85 columns
80–299, row 86 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_212 : rowsJ2 85 86 71 75 ≤ 4443796408313 := by decide +kernel

theorem rows22335R_213 : rowsJ2 85 86 75 80 ≤ 6395544218418 := by decide +kernel

theorem rows22335R_214 : rowsJ2 85 86 80 300 ≤ 27591208945229 := by decide +kernel

theorem rows22335R_215 : rowsJ2 86 87 0 40 ≤ 662051985240605 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_212
#print axioms SieveCert.rows22335R_215
