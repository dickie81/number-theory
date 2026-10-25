/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 998–1001 of 1732

File 250 of 430: the parts `rows22310R_998` … `rows22310R_1001` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27807 tests: row 133 columns 91–93, row 133 columns 94–96, row 133 columns
97–99, row 133 columns 100–103), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_998 : rowsJ2 133 134 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_999 : rowsJ2 133 134 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_1000 : rowsJ2 133 134 97 100 ≤ 0 := by decide +kernel

theorem rows22310R_1001 : rowsJ2 133 134 100 104 ≤ 2120817708692 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_998
#print axioms SieveCert.rows22310R_1001
