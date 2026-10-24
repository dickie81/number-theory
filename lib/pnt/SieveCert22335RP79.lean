/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 305–308 of 549

File 79 of 140: the parts `rows22335R_305` … `rows22335R_308` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23488 tests: row 98 columns 76–88, row 98 columns 89–299, row 99 columns
0–52, row 99 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_305 : rowsJ2 98 99 76 89 ≤ 654720409011636 := by decide +kernel

theorem rows22335R_306 : rowsJ2 98 99 89 300 ≤ 460149912026100 := by decide +kernel

theorem rows22335R_307 : rowsJ2 99 100 0 53 ≤ 500508182519079 := by decide +kernel

theorem rows22335R_308 : rowsJ2 99 100 53 60 ≤ 1199828966248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_305
#print axioms SieveCert.rows22335R_308
