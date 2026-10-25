/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 859–862 of 1732

File 215 of 430: the parts `rows22310R_859` … `rows22310R_862` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26520 tests: row 125 columns 75–78, row 125 columns 79–81, row 125 columns
82–84, row 125 columns 85–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_859 : rowsJ2 125 126 75 79 ≤ 0 := by decide +kernel

theorem rows22310R_860 : rowsJ2 125 126 79 82 ≤ 0 := by decide +kernel

theorem rows22310R_861 : rowsJ2 125 126 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_862 : rowsJ2 125 126 85 87 ≤ 113703497063 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_859
#print axioms SieveCert.rows22310R_862
