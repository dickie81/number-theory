/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 831–834 of 1732

File 208 of 430: the parts `rows22310R_831` … `rows22310R_834` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29256 tests: row 123 columns 95–97, row 123 columns 98–100, row 123 columns
101–103, row 123 columns 104–106), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_831 : rowsJ2 123 124 95 98 ≤ 52924987469 := by decide +kernel

theorem rows22310R_832 : rowsJ2 123 124 98 101 ≤ 0 := by decide +kernel

theorem rows22310R_833 : rowsJ2 123 124 101 104 ≤ 1139011292723 := by decide +kernel

theorem rows22310R_834 : rowsJ2 123 124 104 107 ≤ 3666331450604 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_831
#print axioms SieveCert.rows22310R_834
