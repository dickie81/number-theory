/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1057–1060 of 1732

File 265 of 430: the parts `rows22310R_1057` … `rows22310R_1060` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27209 tests: row 137 columns 88–90, row 137 columns 91–93, row 137 columns
94–96, row 137 columns 97–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1057 : rowsJ2 137 138 88 91 ≤ 0 := by decide +kernel

theorem rows22310R_1058 : rowsJ2 137 138 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_1059 : rowsJ2 137 138 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_1060 : rowsJ2 137 138 97 101 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1057
#print axioms SieveCert.rows22310R_1060
