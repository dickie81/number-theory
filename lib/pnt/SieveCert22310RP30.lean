/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 120–123 of 1732

File 30 of 430: the parts `rows22310R_120` … `rows22310R_123` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28220 tests: row 64 columns 35–43, row 64 columns 44–49, row 64 columns
50–54, row 64 columns 55–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_120 : rowsJ2 64 65 35 44 ≤ 338142829119023 := by decide +kernel

theorem rows22310R_121 : rowsJ2 64 65 44 50 ≤ 147494441462954 := by decide +kernel

theorem rows22310R_122 : rowsJ2 64 65 50 55 ≤ 117100351881672 := by decide +kernel

theorem rows22310R_123 : rowsJ2 64 65 55 59 ≤ 112752432285714 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_120
#print axioms SieveCert.rows22310R_123
