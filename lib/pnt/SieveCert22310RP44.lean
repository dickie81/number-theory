/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 177–180 of 1732

File 44 of 430: the parts `rows22310R_177` … `rows22310R_180` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29264 tests: row 71 columns 55–58, row 71 columns 59–62, row 71 columns
63–66, row 71 columns 67–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_177 : rowsJ2 71 72 55 59 ≤ 121050258215240 := by decide +kernel

theorem rows22310R_178 : rowsJ2 71 72 59 63 ≤ 166506600967662 := by decide +kernel

theorem rows22310R_179 : rowsJ2 71 72 63 67 ≤ 170867339801869 := by decide +kernel

theorem rows22310R_180 : rowsJ2 71 72 67 400 ≤ 195385122273716 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_177
#print axioms SieveCert.rows22310R_180
