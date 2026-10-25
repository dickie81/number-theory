/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 550–553 of 1732

File 139 of 430: the parts `rows22310R_550` … `rows22310R_553` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24705 tests: row 108 columns 90–91, row 108 columns 92–93, row 108 columns
94–95, row 108 columns 96–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_550 : rowsJ2 108 109 90 92 ≤ 1634306802875 := by decide +kernel

theorem rows22310R_551 : rowsJ2 108 109 92 94 ≤ 2707418881554 := by decide +kernel

theorem rows22310R_552 : rowsJ2 108 109 94 96 ≤ 4049377883817 := by decide +kernel

theorem rows22310R_553 : rowsJ2 108 109 96 98 ≤ 4079014906258 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_550
#print axioms SieveCert.rows22310R_553
