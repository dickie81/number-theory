/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1386–1389 of 1732

File 348 of 430: the parts `rows22310R_1386` … `rows22310R_1389` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27567 tests: row 165 columns 61–64, row 165 columns 65–67, row 165 columns
68–71, row 165 columns 72–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1386 : rowsJ2 165 166 61 65 ≤ 25543215417471 := by decide +kernel

theorem rows22310R_1387 : rowsJ2 165 166 65 68 ≤ 24680341016133 := by decide +kernel

theorem rows22310R_1388 : rowsJ2 165 166 68 72 ≤ 26527204115139 := by decide +kernel

theorem rows22310R_1389 : rowsJ2 165 166 72 76 ≤ 17052462511864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1386
#print axioms SieveCert.rows22310R_1389
