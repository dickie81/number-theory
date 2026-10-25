/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 950–953 of 1732

File 238 of 430: the parts `rows22310R_950` … `rows22310R_953` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27600 tests: row 130 columns 91–93, row 130 columns 94–96, row 130 columns
97–99, row 130 columns 100–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_950 : rowsJ2 130 131 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_951 : rowsJ2 130 131 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_952 : rowsJ2 130 131 97 100 ≤ 0 := by decide +kernel

theorem rows22310R_953 : rowsJ2 130 131 100 103 ≤ 867024554478 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_950
#print axioms SieveCert.rows22310R_953
