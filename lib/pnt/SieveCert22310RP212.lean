/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 847–850 of 1732

File 212 of 430: the parts `rows22310R_847` … `rows22310R_850` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26220 tests: row 124 columns 91–92, row 124 columns 93–94, row 124 columns
95–97, row 124 columns 98–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_847 : rowsJ2 124 125 91 93 ≤ 110283425338 := by decide +kernel

theorem rows22310R_848 : rowsJ2 124 125 93 95 ≤ 44663427839 := by decide +kernel

theorem rows22310R_849 : rowsJ2 124 125 95 98 ≤ 7531266640 := by decide +kernel

theorem rows22310R_850 : rowsJ2 124 125 98 101 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_847
#print axioms SieveCert.rows22310R_850
