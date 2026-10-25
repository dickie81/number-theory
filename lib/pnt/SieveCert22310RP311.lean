/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1240–1243 of 1732

File 311 of 430: the parts `rows22310R_1240` … `rows22310R_1243` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28105 tests: row 151 columns 72–74, row 151 columns 75–77, row 151 columns
78–80, row 151 columns 81–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1240 : rowsJ2 151 152 72 75 ≤ 15527872960502 := by decide +kernel

theorem rows22310R_1241 : rowsJ2 151 152 75 78 ≤ 12397120189220 := by decide +kernel

theorem rows22310R_1242 : rowsJ2 151 152 78 81 ≤ 8687188370442 := by decide +kernel

theorem rows22310R_1243 : rowsJ2 151 152 81 85 ≤ 7015447908493 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1240
#print axioms SieveCert.rows22310R_1243
