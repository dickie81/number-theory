/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1323–1326 of 1732

File 332 of 430: the parts `rows22310R_1323` … `rows22310R_1326` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28425 tests: row 158 columns 82–86, row 158 columns 87–91, row 158 columns
92–399, row 159 columns 0–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1323 : rowsJ2 158 159 82 87 ≤ 6286389333223 := by decide +kernel

theorem rows22310R_1324 : rowsJ2 158 159 87 92 ≤ 1528196366546 := by decide +kernel

theorem rows22310R_1325 : rowsJ2 158 159 92 400 ≤ 57235613090957 := by decide +kernel

theorem rows22310R_1326 : rowsJ2 159 160 0 57 ≤ 124557763140822 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1323
#print axioms SieveCert.rows22310R_1326
