/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 241–244 of 1732

File 60 of 430: the parts `rows22310R_241` … `rows22310R_244` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24125 tests: row 78 columns 64–69, row 78 columns 70–77, row 78 columns
78–399, row 79 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_241 : rowsJ2 78 79 64 70 ≤ 212610127679940 := by decide +kernel

theorem rows22310R_242 : rowsJ2 78 79 70 78 ≤ 234876381978124 := by decide +kernel

theorem rows22310R_243 : rowsJ2 78 79 78 400 ≤ 25388566645946 := by decide +kernel

theorem rows22310R_244 : rowsJ2 79 80 0 35 ≤ 739099135924093 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_241
#print axioms SieveCert.rows22310R_244
