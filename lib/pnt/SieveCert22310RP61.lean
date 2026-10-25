/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 245–248 of 1732

File 61 of 430: the parts `rows22310R_245` … `rows22310R_248` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28161 tests: row 79 columns 35–43, row 79 columns 44–49, row 79 columns
50–54, row 79 columns 55–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_245 : rowsJ2 79 80 35 44 ≤ 112766597301637 := by decide +kernel

theorem rows22310R_246 : rowsJ2 79 80 44 50 ≤ 81076957496329 := by decide +kernel

theorem rows22310R_247 : rowsJ2 79 80 50 55 ≤ 121562438715679 := by decide +kernel

theorem rows22310R_248 : rowsJ2 79 80 55 59 ≤ 152677100533233 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_245
#print axioms SieveCert.rows22310R_248
