/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1018–1021 of 1732

File 255 of 430: the parts `rows22310R_1018` … `rows22310R_1021` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28697 tests: row 134 columns 108–399, row 135 columns 0–37, row 135 columns
38–67, row 135 columns 68–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1018 : rowsJ2 134 135 108 400 ≤ 674428397566738 := by decide +kernel

theorem rows22310R_1019 : rowsJ2 135 136 0 38 ≤ 220196923233875 := by decide +kernel

theorem rows22310R_1020 : rowsJ2 135 136 38 68 ≤ 126458190194273 := by decide +kernel

theorem rows22310R_1021 : rowsJ2 135 136 68 73 ≤ 4705872662559 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1018
#print axioms SieveCert.rows22310R_1021
