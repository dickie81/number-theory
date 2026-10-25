/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1211–1214 of 1732

File 304 of 430: the parts `rows22310R_1211` … `rows22310R_1214` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27973 tests: row 149 columns 0–59, row 149 columns 60–65, row 149 columns
66–69, row 149 columns 70–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1211 : rowsJ2 149 150 0 60 ≤ 200270373236654 := by decide +kernel

theorem rows22310R_1212 : rowsJ2 149 150 60 66 ≤ 12116098444972 := by decide +kernel

theorem rows22310R_1213 : rowsJ2 149 150 66 70 ≤ 14333030880360 := by decide +kernel

theorem rows22310R_1214 : rowsJ2 149 150 70 73 ≤ 12975412334691 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1211
#print axioms SieveCert.rows22310R_1214
