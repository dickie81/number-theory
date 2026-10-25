/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1264–1267 of 1732

File 317 of 430: the parts `rows22310R_1264` … `rows22310R_1267` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27135 tests: row 153 columns 72–74, row 153 columns 75–77, row 153 columns
78–80, row 153 columns 81–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1264 : rowsJ2 153 154 72 75 ≤ 16730169673913 := by decide +kernel

theorem rows22310R_1265 : rowsJ2 153 154 75 78 ≤ 12623259112768 := by decide +kernel

theorem rows22310R_1266 : rowsJ2 153 154 78 81 ≤ 8906110076558 := by decide +kernel

theorem rows22310R_1267 : rowsJ2 153 154 81 85 ≤ 7297779199172 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1264
#print axioms SieveCert.rows22310R_1267
