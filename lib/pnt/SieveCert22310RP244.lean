/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 974–977 of 1732

File 244 of 430: the parts `rows22310R_974` … `rows22310R_977` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29484 tests: row 132 columns 36–67, row 132 columns 68–73, row 132 columns
74–77, row 132 columns 78–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_974 : rowsJ2 132 133 36 68 ≤ 200830626473109 := by decide +kernel

theorem rows22310R_975 : rowsJ2 132 133 68 74 ≤ 2553329062413 := by decide +kernel

theorem rows22310R_976 : rowsJ2 132 133 74 78 ≤ 0 := by decide +kernel

theorem rows22310R_977 : rowsJ2 132 133 78 81 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_974
#print axioms SieveCert.rows22310R_977
