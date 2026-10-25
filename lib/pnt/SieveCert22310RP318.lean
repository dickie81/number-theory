/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1268–1271 of 1732

File 318 of 430: the parts `rows22310R_1268` … `rows22310R_1271` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23958 tests: row 153 columns 85–88, row 153 columns 89–93, row 153 columns
94–99, row 153 columns 100–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1268 : rowsJ2 153 154 85 89 ≤ 3485519800271 := by decide +kernel

theorem rows22310R_1269 : rowsJ2 153 154 89 94 ≤ 1180401739882 := by decide +kernel

theorem rows22310R_1270 : rowsJ2 153 154 94 100 ≤ 26365274244 := by decide +kernel

theorem rows22310R_1271 : rowsJ2 153 154 100 400 ≤ 60629810188210 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1268
#print axioms SieveCert.rows22310R_1271
