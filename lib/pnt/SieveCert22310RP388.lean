/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1541–1544 of 1732

File 388 of 430: the parts `rows22310R_1541` … `rows22310R_1544` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26894 tests: row 187 columns 59–64, row 187 columns 65–399, row 188 columns
0–46, row 188 columns 47–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1541 : rowsJ2 187 188 59 65 ≤ 39845321958944 := by decide +kernel

theorem rows22310R_1542 : rowsJ2 187 188 65 400 ≤ 2092963091453578 := by decide +kernel

theorem rows22310R_1543 : rowsJ2 188 189 0 47 ≤ 29847050414525 := by decide +kernel

theorem rows22310R_1544 : rowsJ2 188 189 47 53 ≤ 46848951075342 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1541
#print axioms SieveCert.rows22310R_1544
