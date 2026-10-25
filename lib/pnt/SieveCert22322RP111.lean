/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 426–429 of 561

File 111 of 143: the parts `rows22322R_426` … `rows22322R_429` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29564 tests: row 119 columns 63–299, row 120 columns 0–47, row 120 columns
48–54, row 120 columns 55–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_426 : rowsJ2 119 120 63 300 ≤ 306725436191648 := by decide +kernel

theorem rows22322R_427 : rowsJ2 120 121 0 48 ≤ 191875936951720 := by decide +kernel

theorem rows22322R_428 : rowsJ2 120 121 48 55 ≤ 85395138825213 := by decide +kernel

theorem rows22322R_429 : rowsJ2 120 121 55 63 ≤ 41347539027702 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_426
#print axioms SieveCert.rows22322R_429
