/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 225–228 of 1732

File 56 of 430: the parts `rows22310R_225` … `rows22310R_228` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25071 tests: row 76 columns 74–399, row 77 columns 0–34, row 77 columns
35–43, row 77 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_225 : rowsJ2 76 77 74 400 ≤ 89388727587165 := by decide +kernel

theorem rows22310R_226 : rowsJ2 77 78 0 35 ≤ 789805872856479 := by decide +kernel

theorem rows22310R_227 : rowsJ2 77 78 35 44 ≤ 133686816616534 := by decide +kernel

theorem rows22310R_228 : rowsJ2 77 78 44 50 ≤ 82467077847837 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_225
#print axioms SieveCert.rows22310R_228
