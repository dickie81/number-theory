/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 487–490 of 1732

File 123 of 430: the parts `rows22310R_487` … `rows22310R_490` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27647 tests: row 104 columns 82–86, row 104 columns 87–89, row 104 columns
90–92, row 104 columns 93–94), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_487 : rowsJ2 104 105 82 87 ≤ 11639091727084 := by decide +kernel

theorem rows22310R_488 : rowsJ2 104 105 87 90 ≤ 2963465413514 := by decide +kernel

theorem rows22310R_489 : rowsJ2 104 105 90 93 ≤ 3014816410424 := by decide +kernel

theorem rows22310R_490 : rowsJ2 104 105 93 95 ≤ 3432487536911 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_487
#print axioms SieveCert.rows22310R_490
