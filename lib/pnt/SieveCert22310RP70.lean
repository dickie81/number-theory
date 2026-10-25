/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 281–284 of 1732

File 70 of 430: the parts `rows22310R_281` … `rows22310R_284` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29236 tests: row 83 columns 44–49, row 83 columns 50–54, row 83 columns
55–59, row 83 columns 60–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_281 : rowsJ2 83 84 44 50 ≤ 85824701632675 := by decide +kernel

theorem rows22310R_282 : rowsJ2 83 84 50 55 ≤ 143236987614662 := by decide +kernel

theorem rows22310R_283 : rowsJ2 83 84 55 60 ≤ 195204470283957 := by decide +kernel

theorem rows22310R_284 : rowsJ2 83 84 60 66 ≤ 208403107805687 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_281
#print axioms SieveCert.rows22310R_284
