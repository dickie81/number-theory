/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 474–477 of 561

File 123 of 143: the parts `rows22322R_474` … `rows22322R_477` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26371 tests: row 133 columns 0–43, row 133 columns 44–52, row 133 columns
53–299, row 134 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_474 : rowsJ2 133 134 0 44 ≤ 135465127262882 := by decide +kernel

theorem rows22322R_475 : rowsJ2 133 134 44 53 ≤ 113843607514808 := by decide +kernel

theorem rows22322R_476 : rowsJ2 133 134 53 300 ≤ 2673113416633008 := by decide +kernel

theorem rows22322R_477 : rowsJ2 134 135 0 43 ≤ 123377182098256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_474
#print axioms SieveCert.rows22322R_477
