/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1183–1186 of 1732

File 297 of 430: the parts `rows22310R_1183` … `rows22310R_1186` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25369 tests: row 146 columns 99–103, row 146 columns 104–399, row 147 columns
0–59, row 147 columns 60–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1183 : rowsJ2 146 147 99 104 ≤ 3975804111307 := by decide +kernel

theorem rows22310R_1184 : rowsJ2 146 147 104 400 ≤ 248725460460017 := by decide +kernel

theorem rows22310R_1185 : rowsJ2 147 148 0 60 ≤ 217561349028822 := by decide +kernel

theorem rows22310R_1186 : rowsJ2 147 148 60 67 ≤ 12738838768774 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1183
#print axioms SieveCert.rows22310R_1186
