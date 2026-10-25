/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 265–268 of 1732

File 66 of 430: the parts `rows22310R_265` … `rows22310R_268` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28728 tests: row 81 columns 50–54, row 81 columns 55–58, row 81 columns
59–63, row 81 columns 64–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_265 : rowsJ2 81 82 50 55 ≤ 131310574144086 := by decide +kernel

theorem rows22310R_266 : rowsJ2 81 82 55 59 ≤ 157299583850704 := by decide +kernel

theorem rows22310R_267 : rowsJ2 81 82 59 64 ≤ 188284590058601 := by decide +kernel

theorem rows22310R_268 : rowsJ2 81 82 64 71 ≤ 227425455480627 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_265
#print axioms SieveCert.rows22310R_268
