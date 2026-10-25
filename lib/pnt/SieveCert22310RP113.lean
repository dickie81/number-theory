/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 449–452 of 1732

File 113 of 430: the parts `rows22310R_449` … `rows22310R_452` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25661 tests: row 101 columns 90–92, row 101 columns 93–94, row 101 columns
95–96, row 101 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_449 : rowsJ2 101 102 90 93 ≤ 4879779534838 := by decide +kernel

theorem rows22310R_450 : rowsJ2 101 102 93 95 ≤ 3604438676566 := by decide +kernel

theorem rows22310R_451 : rowsJ2 101 102 95 97 ≤ 5044242997317 := by decide +kernel

theorem rows22310R_452 : rowsJ2 101 102 97 99 ≤ 6873465206028 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_449
#print axioms SieveCert.rows22310R_452
