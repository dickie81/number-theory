/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 247–250 of 549

File 64 of 140: the parts `rows22335R_247` … `rows22335R_250` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29318 tests: row 90 columns 66–69, row 90 columns 70–74, row 90 columns
75–80, row 90 columns 81–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_247 : rowsJ2 90 91 66 70 ≤ 1680247146041 := by decide +kernel

theorem rows22335R_248 : rowsJ2 90 91 70 75 ≤ 524956355608 := by decide +kernel

theorem rows22335R_249 : rowsJ2 90 91 75 81 ≤ 10292586616210 := by decide +kernel

theorem rows22335R_250 : rowsJ2 90 91 81 300 ≤ 508026847739430 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_247
#print axioms SieveCert.rows22335R_250
