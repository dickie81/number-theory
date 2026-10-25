/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 273–276 of 1732

File 68 of 430: the parts `rows22310R_273` … `rows22310R_276` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29761 tests: row 82 columns 44–49, row 82 columns 50–54, row 82 columns
55–59, row 82 columns 60–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_273 : rowsJ2 82 83 44 50 ≤ 83670106400977 := by decide +kernel

theorem rows22310R_274 : rowsJ2 82 83 50 55 ≤ 136997013211738 := by decide +kernel

theorem rows22310R_275 : rowsJ2 82 83 55 60 ≤ 197028260296054 := by decide +kernel

theorem rows22310R_276 : rowsJ2 82 83 60 66 ≤ 213357270524968 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_273
#print axioms SieveCert.rows22310R_276
