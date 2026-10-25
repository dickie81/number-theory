/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1460–1463 of 1732

File 367 of 430: the parts `rows22310R_1460` … `rows22310R_1463` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28977 tests: row 174 columns 62–65, row 174 columns 66–70, row 174 columns
71–75, row 174 columns 76–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1460 : rowsJ2 174 175 62 66 ≤ 34955278174750 := by decide +kernel

theorem rows22310R_1461 : rowsJ2 174 175 66 71 ≤ 27252556733125 := by decide +kernel

theorem rows22310R_1462 : rowsJ2 174 175 71 76 ≤ 13762888705834 := by decide +kernel

theorem rows22310R_1463 : rowsJ2 174 175 76 400 ≤ 1647934209573570 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1460
#print axioms SieveCert.rows22310R_1463
