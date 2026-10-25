/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1303–1306 of 1732

File 327 of 430: the parts `rows22310R_1303` … `rows22310R_1306` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27165 tests: row 156 columns 90–95, row 156 columns 96–399, row 157 columns
0–57, row 157 columns 58–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1303 : rowsJ2 156 157 90 96 ≤ 541188954397 := by decide +kernel

theorem rows22310R_1304 : rowsJ2 156 157 96 400 ≤ 0 := by decide +kernel

theorem rows22310R_1305 : rowsJ2 157 158 0 58 ≤ 138566456450742 := by decide +kernel

theorem rows22310R_1306 : rowsJ2 157 158 58 64 ≤ 17938292923043 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1303
#print axioms SieveCert.rows22310R_1306
