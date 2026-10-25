/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 898–901 of 1732

File 225 of 430: the parts `rows22310R_898` … `rows22310R_901` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26220 tests: row 127 columns 88–89, row 127 columns 90–91, row 127 columns
92–94, row 127 columns 95–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_898 : rowsJ2 127 128 88 90 ≤ 21596104730 := by decide +kernel

theorem rows22310R_899 : rowsJ2 127 128 90 92 ≤ 0 := by decide +kernel

theorem rows22310R_900 : rowsJ2 127 128 92 95 ≤ 0 := by decide +kernel

theorem rows22310R_901 : rowsJ2 127 128 95 98 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_898
#print axioms SieveCert.rows22310R_901
