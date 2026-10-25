/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1117–1120 of 1732

File 280 of 430: the parts `rows22310R_1117` … `rows22310R_1120` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25254 tests: row 141 columns 97–100, row 141 columns 101–105, row 141 columns
106–399, row 142 columns 0–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1117 : rowsJ2 141 142 97 101 ≤ 0 := by decide +kernel

theorem rows22310R_1118 : rowsJ2 141 142 101 106 ≤ 8456770367713 := by decide +kernel

theorem rows22310R_1119 : rowsJ2 141 142 106 400 ≤ 446737373760987 := by decide +kernel

theorem rows22310R_1120 : rowsJ2 142 143 0 59 ≤ 265680291563911 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1117
#print axioms SieveCert.rows22310R_1120
