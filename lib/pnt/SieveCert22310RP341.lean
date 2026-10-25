/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1359–1362 of 1732

File 341 of 430: the parts `rows22310R_1359` … `rows22310R_1362` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26631 tests: row 162 columns 66–68, row 162 columns 69–71, row 162 columns
72–75, row 162 columns 76–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1359 : rowsJ2 162 163 66 69 ≤ 23088110187700 := by decide +kernel

theorem rows22310R_1360 : rowsJ2 162 163 69 72 ≤ 20532470025030 := by decide +kernel

theorem rows22310R_1361 : rowsJ2 162 163 72 76 ≤ 19243816388141 := by decide +kernel

theorem rows22310R_1362 : rowsJ2 162 163 76 80 ≤ 11688137146569 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1359
#print axioms SieveCert.rows22310R_1362
